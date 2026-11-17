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
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.CyclotomicPhaseCheck
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SelectSwapQromUnload
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage4PrefixHoldDeferMux
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance : NeZero 2 := ⟨two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped Matrix BigOperators
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances
set_option autoImplicit false
set_option allowUnsafeReducibility true
open QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
  QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.Stage1Opt41TwoWrap
  QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu
open QuantumComputation.Specs.PhotochemistrySolution.PortBSharedPoly
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open QuantumComputation.Specs.PhotochemistrySolution.ProviderCoreFused
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.CoulombFast
  QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirstZero
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
open QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore
  QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
  QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
  QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.MidOW60
  QuantumComputation.Specs.PhotochemistrySolution.Stage1CoinDecode
  QuantumComputation.Specs.PhotochemistrySolution.MidOW42ExactOpt
open QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (ctrlNot_lt0 ctrlNot_ltZ
    cz2_counts cz2_dynWires cz2_step majCarryBit_val midOW_lt0 midOW_lt1 midOW_ltCln midOW_ltY
    pCtrlNotReg1 pCtrlNotReg1_counts pCtrlNotReg1_dynWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (pCtrlNotReg1_step
    pWrapCarryChain pWrapCarryChain_counts pWrapCarryChain_dynWires pWrapCarryChain_step rCarryOut
    stCarryOut x1_counts x1_dynWires x1_step)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
    (planeOfRouter_rIdx12Alias_roles rIdx12Alias)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (counts_wrapDynOnReg
    wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA (WOptInj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
    (subspaceStep_mul_right)
open PrimitiveGate (T TOFF)
set_option Elab.async false
set_option maxRecDepth 200000

noncomputable section
open scoped Circuit.Notation
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.MidOWTap29Xor240
set_option exponentiation.threshold 256
open DynamicCircuit PhotochemistrySolution.MidOWTap29
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
attribute [local irreducible] mkKetOpW SubregMBUCore.wrapDynOnReg SubregMBUCore.uStageOfCP
theorem tap29_lt82 : 82 < 71 + 29 := by omega

theorem tap29_ne_82_84 {n : ℕ} (r : QRegister (71 + 29) n) : r ⟨82, tap29_lt82⟩ ≠ r ⟨84, tap29_lt84⟩
    :=
  fun e ↦ by have hv : 82 = 84 := congrArg Fin.val (r.wires.injective e); omega

theorem tap29_ne_21_84 {n : ℕ} (r : QRegister (71 + 29) n) : r ⟨21, tap29_lt21⟩ ≠ r ⟨84, tap29_lt84⟩
    :=
  fun e ↦ by have hv : 21 = 84 := congrArg Fin.val (r.wires.injective e); omega

theorem tap29_ne_81_84 {n : ℕ} (r : QRegister (71 + 29) n) : r ⟨81, tap29_lt81⟩ ≠ r ⟨84, tap29_lt84⟩
    :=
  fun e ↦ by have hv : 81 = 84 := congrArg Fin.val (r.wires.injective e); omega

theorem zmod2_eq_of_val_eq {x y : ZMod 2} (h : x.val = y.val) : x = y := by
  rcases DynCircExt.bit_cases x with rfl | rfl <;>
  rcases DynCircExt.bit_cases y with rfl | rfl <;>
  first | rfl | (exfalso; revert h; decide)

theorem zmod2_maj_flip0 (a b c : ZMod 2) : ((a + 1) + c) * (b + c) + c = ((a + c) * (b + c) + c) +
    b + c := by
  rcases DynCircExt.bit_cases a with rfl | rfl <;>
  rcases DynCircExt.bit_cases b with rfl | rfl <;>
  rcases DynCircExt.bit_cases c with rfl | rfl <;> decide

/-- `0-T` carry-tap linear combination `cA[11] + y[16] + cA[10]` on `(r[82], r[21], r[81])`. -/
def tap29_cXorBit {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ZMod 2 :=
    st δ (r ⟨82, tap29_lt82⟩) + st δ (r ⟨21, tap29_lt21⟩) + st δ (r ⟨81, tap29_lt81⟩)
def tap29_stTapXor {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n) :
    BitAssignment n → BitAssignment n :=
  fun δ ↦ Function.update (st δ) (r ⟨84, tap29_lt84⟩)
    (st δ (r ⟨84, tap29_lt84⟩) + tap29_cXorBit r st δ)

/-- `0-T` 3-CNOT compute/uncompute of `cTap = cA[11] + y[16] + cA[10]` on `r[84]`. -/
def tap29_pTapXor {Var : Type} {n : ℕ} (v : Var) (r : QRegister (71 + 29) n) :
    DynamicCircuit Var n :=
  .seq (cnot1 v (r ⟨82, tap29_lt82⟩) (r ⟨84, tap29_lt84⟩) (tap29_ne_82_84 r))
  (.seq (cnot1 v (r ⟨21, tap29_lt21⟩) (r ⟨84, tap29_lt84⟩) (tap29_ne_21_84 r))
        (cnot1 v (r ⟨81, tap29_lt81⟩) (r ⟨84, tap29_lt84⟩) (tap29_ne_81_84 r)))

/-- `0-T` tap Pass-B (`124 T`, `0 .TOFF`). -/
def tap29_pPassB_xor240 {Var : Type} {n : ℕ} (v : Var) (r : QRegister (71 + 29) n) :
    DynamicCircuit Var n :=
  .seq (tap29_pTapXor v r)
  (.seq (tap29_pPassBInner v r)
        (tap29_pTapXor v r))

/-- Outer body of `MidOWTap29Xor240` without `x1(52)` pair or `cpMaj4` (`188 T`, `0 .TOFF`). -/
def tap29_pOuterBody_xor240 {Var : Type} {n : ℕ} (v : Var) (r : QRegister (71 + 29) n) :
    DynamicCircuit Var n :=
  .seq (tap29_pPassAHi v r)
  (.seq (tap29_pPassB_xor240 v r)
        (pCtrlNotReg1 15 v (tap29_rRefl r)))

/-- Complete carry-tap `Mid_OW` circuit on `71 + 29 = 100` wires (`240 T`, `0 .TOFF`). -/
def tap29_pMid_xor240 {Var : Type} {n : ℕ} (v : Var) (r : QRegister (71 + 29) n) :
    DynamicCircuit Var n := pWrapCarryChain 12 v (tap29_rCarryA r) (tap29_pOuterBody_xor240 v r)
theorem tap29_pTapXor_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (r : QRegister (71 + 29) n) (hr : ∀ u : Fin (71 + 29), S (r u)) : (tap29_pTapXor v r).count .T =
    0 ∧ (tap29_pTapXor v r).count .TOFF = 0 ∧ DynWires S (tap29_pTapXor v r) := by
  obtain ⟨t0, f0⟩ := cnot1_counts (Var := Var) v (r ⟨82, tap29_lt82⟩) (r ⟨84, tap29_lt84⟩)
    (tap29_ne_82_84 r)
  obtain ⟨t1, f1⟩ := cnot1_counts (Var := Var) v (r ⟨21, tap29_lt21⟩) (r ⟨84, tap29_lt84⟩)
    (tap29_ne_21_84 r)
  obtain ⟨t2, f2⟩ := cnot1_counts (Var := Var) v (r ⟨81, tap29_lt81⟩) (r ⟨84, tap29_lt84⟩)
    (tap29_ne_81_84 r)
  refine ⟨?_, ?_, ⟨cnot1_dynWires S v _ _ (tap29_ne_82_84 r) (hr _)
      (hr _), cnot1_dynWires S v _ _ (tap29_ne_21_84 r) (hr _)
      (hr _), cnot1_dynWires S v _ _ (tap29_ne_81_84 r) (hr _) (hr _)⟩⟩
  · dsimp only [tap29_pTapXor, DynamicCircuit.count]; rw [t0, t1, t2]
  · dsimp only [tap29_pTapXor, DynamicCircuit.count]; rw [f0, f1, f2]

theorem tap29_pPassB_xor240_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (r : QRegister (71 + 29) n) (hr : ∀ u : Fin (71 + 29), S (r u)) :
    (tap29_pPassB_xor240 v r).count .T = 124 ∧ (tap29_pPassB_xor240 v r).count .TOFF = 0 ∧
    DynWires S (tap29_pPassB_xor240 v r) := by
  obtain ⟨tXor, fXor, dwXor⟩ := tap29_pTapXor_counts_wires v r hr
  obtain ⟨tCz0, fCz0⟩ := cz2_counts (Var := Var) (r ⟨0, midOW_lt0 29⟩) (r ⟨1, midOW_lt1 29⟩)
    (tap29_ne_0_1 r)
  obtain ⟨tX1, fX1⟩ := x1_counts (Var := Var) (r ⟨1, midOW_lt1 29⟩)
  obtain ⟨tCz1, fCz1⟩ := cz2_counts (Var := Var) (r ⟨1, midOW_lt1 29⟩) (r ⟨38, tap29_lt38⟩)
    (tap29_ne_1_38 r)
  obtain ⟨tAdd, fAdd⟩ := pCtrlAddCarryKickFast0Anc_counts 15 v (tap29_rCtrlB r)
  refine ⟨?_, ?_, ⟨dwXor, ⟨cz2_dynWires S _ _ (tap29_ne_0_1 r) (hr _)
      (hr _), x1_dynWires S _ (hr _), cz2_dynWires S _ _ (tap29_ne_1_38 r) (hr _)
      (hr _), pCtrlAddCarryKickFast0Anc_dynWires 15 S v (tap29_rCtrlB r)
      (fun u ↦ hr (tap29_fCtrlB u)), x1_dynWires S _ (hr _)⟩, dwXor⟩⟩
  · dsimp only [tap29_pPassB_xor240, tap29_pPassBInner, DynamicCircuit.count];
    rw [tXor, tCz0, tX1, tCz1, tAdd]
  · dsimp only [tap29_pPassB_xor240, tap29_pPassBInner, DynamicCircuit.count];
    rw [fXor, fCz0, fX1, fCz1, fAdd]
theorem tap29_pMid_xor240_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (r : QRegister (71 + 29) n) (hr : ∀ u : Fin (71 + 29), S (r u)) :
    (tap29_pMid_xor240 v r).count .T = 240 ∧ (tap29_pMid_xor240 v r).count .TOFF = 0 ∧
    DynWires S (tap29_pMid_xor240 v r) := by
  obtain ⟨tPA, fPA, dwPA⟩ := tap29_pPassAHi_counts_wires v r hr; obtain ⟨tPB, fPB, dwPB⟩ :=
      tap29_pPassB_xor240_counts_wires v r hr; obtain ⟨tRef, fRef⟩ :=
      pCtrlNotReg1_counts 15 v (tap29_rRefl r); obtain ⟨tCarA, fCarA⟩ :=
      pWrapCarryChain_counts 12 v (tap29_rCarryA r) (tap29_pOuterBody_xor240 v r)
  have dwBody : DynWires S (tap29_pOuterBody_xor240 v r) :=
      ⟨dwPA, dwPB, pCtrlNotReg1_dynWires 15 S v (tap29_rRefl r) (fun u ↦ hr (tap29_fRefl u))⟩
  refine ⟨?_, ?_, pWrapCarryChain_dynWires 12 S v (tap29_rCarryA r) _ (fun u ↦
      hr (tap29_fCarryA u)) dwBody⟩
  · dsimp only [tap29_pMid_xor240]; rw [tCarA];
    dsimp only [tap29_pOuterBody_xor240, DynamicCircuit.count]; rw [tPA, tPB, tRef]
  · dsimp only [tap29_pMid_xor240]; rw [fCarA];
    dsimp only [tap29_pOuterBody_xor240, DynamicCircuit.count]; rw [fPA, fPB, fRef]
theorem tap29_pTapXor_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (mkKetOpW rWork st ph) (mkKetOpW rWork (tap29_stTapXor r st) ph)
    (tap29_pTapXor v r) := by
  let w84 := r ⟨84, tap29_lt84⟩
  let s1 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st δ) w84 (st δ w84 + st δ (r ⟨82, tap29_lt82⟩))
  let s2 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (s1 δ) w84 (s1 δ w84 + s1 δ (r ⟨21, tap29_lt21⟩))
  let s3 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (s2 δ) w84 (s2 δ w84 + s2 δ (r ⟨81, tap29_lt81⟩))
  have hs0 := cnot1_step v rWork (r ⟨82, tap29_lt82⟩) w84 (tap29_ne_82_84 r) st ph;
  have hs1 := cnot1_step v rWork (r ⟨21, tap29_lt21⟩) w84 (tap29_ne_21_84 r) s1 ph;
  have hs2 := cnot1_step v rWork (r ⟨81, tap29_lt81⟩) w84 (tap29_ne_81_84 r) s2 ph
  refine subspaceStep_of_eq_post
    (subspaceStep_seq_mbu hs0 (subspaceStep_seq_mbu hs1 hs2))
    (mkKetOpW_congr rWork (fun δ _ ↦ ?_) (fun _ _ ↦ rfl))
  funext w; dsimp only [s3, s2, s1, tap29_stTapXor, tap29_cXorBit, w84]
  by_cases hw : w = r ⟨84, tap29_lt84⟩
  · rw [hw];
    simp only [Function.update_self, Function.update_of_ne (tap29_ne_21_84 r),
        Function.update_of_ne (tap29_ne_81_84 r), add_assoc]
  · rw [Function.update_of_ne hw, Function.update_of_ne hw, Function.update_of_ne hw,
        Function.update_of_ne hw]

def tap29_phPassBOut {n : ℕ} (r : QRegister (71 + 29) n) (stA : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) (δ : BitAssignment n) : ZMod 2 :=
    ph δ + stA δ (r ⟨0, midOW_lt0 29⟩) * stA δ (r ⟨1, midOW_lt1 29⟩) +
    (stA δ (r ⟨1, midOW_lt1 29⟩) + 1) * stA δ (r ⟨38, tap29_lt38⟩) + (stA δ (r ⟨1, midOW_lt1 29⟩) +
    1) * (((finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) +
    finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨22 + j.val, tap29_lt22 j⟩)) +
    (tap29_cXorBit r stA δ).val) / 2 ^ 16 : ℕ) : ZMod 2)
theorem tap29_pPassBInner_step_xor {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (71 + 29) n)
    (stA : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hCln84 : ∀ (j : Fin 16) (δ : BitAssignment n),
      (∀ q : Fin W, δ (rWork q) = 0) → stA δ (r ⟨84 + j.val, tap29_lt84_pool j⟩) = 0) :
    let st1 := tap29_stTapXor r stA
    ∃ st4 : BitAssignment n → BitAssignment n,
      SubspaceStep (mkKetOpW rWork st1 ph)
        (mkKetOpW rWork st4 (tap29_phPassBOut r stA ph))
        (tap29_pPassBInner v r) ∧
      (∀ (δ : BitAssignment n) (w : Wire n),
        (∀ j : Fin 16, w ≠ r ⟨55 + j.val, tap29_lt55 j⟩) → st4 δ w = st1 δ w) ∧
      (∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
        stA δ (r ⟨1, midOW_lt1 29⟩) = 1 →
        ∀ j : Fin 16, st4 δ (r ⟨55 + j.val, tap29_lt55 j⟩) = stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) ∧
      (∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
        stA δ (r ⟨1, midOW_lt1 29⟩) = 0 →
        finBitsVal (fun j : Fin 16 ↦ st4 δ (r ⟨55 + j.val, tap29_lt55 j⟩)) =
          (finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) +
           finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨22 + j.val, tap29_lt22 j⟩)) +
           (tap29_cXorBit r stA δ).val) % 2 ^ 16) := by
  intro st1
  let rCtrl := tap29_rCtrlB r
  let w1 := r ⟨1, midOW_lt1 29⟩
  have rNe {a b : ℕ} {ha : a < 71 + 29} {hb : b < 71 + 29} (h : a ≠ b) : r ⟨a, ha⟩ ≠ r ⟨b, hb⟩ :=
    fun e ↦ h (congrArg Fin.val (r.wires.injective e))
  have hSt1Not (δ : BitAssignment n) {idx : ℕ} (hi : idx < 71 + 29) (hidx : idx ≠ 84) :
      st1 δ (r ⟨idx, hi⟩) = stA δ (r ⟨idx, hi⟩) := Function.update_of_ne (rNe hidx) _ _
  let ph1 (δ : BitAssignment n) : ZMod 2 := ph δ + st1 δ (r ⟨0, midOW_lt0 29⟩) * st1 δ w1
  let st2 (δ : BitAssignment n) : BitAssignment n := Function.update (st1 δ) w1 (st1 δ w1 + 1)
  let ph2 (δ : BitAssignment n) : ZMod 2 := ph1 δ + st2 δ w1 * st2 δ (r ⟨38, tap29_lt38⟩)
  have hSt2Not (δ : BitAssignment n) {idx : ℕ} (hi : idx < 71 + 29) (h1 : idx ≠ 1)
      (h84 : idx ≠ 84) :
      st2 δ (r ⟨idx, hi⟩) = stA δ (r ⟨idx, hi⟩) :=
          (Function.update_of_ne (rNe h1) _ _).trans (hSt1Not δ hi h84)
  have hCtrlCln (u : Fin 49) (δ : BitAssignment n) (hu : 4 + 2 * 15 ≤ u.val)
      (hz : ∀ q : Fin W, δ (rWork q) = 0) :
      st2 δ (rCtrl u) = 0 := by
    rw [show rCtrl u = r ⟨51 + u.val, by omega⟩ from congrArg r.wires (Fin.ext (by
      have := u.isLt
      dsimp [rCtrl, tap29_rCtrlB, tap29_fCtrlB, tap29_idxCtrlB]
      split_ifs <;> omega)), hSt2Not δ _ (by omega) (by omega)]
    exact (congrArg (stA δ)
        (congrArg r.wires (Fin.ext (by dsimp; omega)))).trans (hCln84 ⟨u.val - 33,
        by omega⟩ δ hz)
  obtain ⟨st3, hAddStep, h3Not, h3Idle, h3Act⟩ :=
      pCtrlAddCarryKickFast0Anc_step 15 v rWork rCtrl st2 ph2 hCtrlCln
  have hCtrlZ (i : Fin 16) : rCtrl ⟨2 + i.val, ctrl0_ltZ 15 i⟩ = r ⟨55 + i.val, tap29_lt55 i⟩ :=
    congrArg r.wires (Fin.ext (by
      have := i.isLt
      dsimp [rCtrl, tap29_rCtrlB, tap29_fCtrlB, tap29_idxCtrlB]
      split_ifs <;> omega))
  have hZVal2 (δ) : finBitsVal (fun i : Fin 16 ↦ st2 δ (rCtrl ⟨2 + i.val, ctrl0_ltZ 15 i⟩)) =
      finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) :=
    congrArg finBitsVal (funext fun i ↦ (congrArg (st2 δ) (hCtrlZ i)).trans (hSt2Not δ _ (by omega)
        (by omega)))
  have hBVal2 (δ) : finBitsVal (fun i : Fin 16 ↦ st2 δ (rCtrl ⟨3 + 15 + i.val, ctrl0_ltB 15 i⟩)) =
      finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨22 + j.val, tap29_lt22 j⟩)) :=
    congrArg finBitsVal (funext fun i ↦ (congrArg (st2 δ) (congrArg r.wires (Fin.ext (by
      have := i.isLt
      dsimp [rCtrl, tap29_rCtrlB, tap29_fCtrlB, tap29_idxCtrlB]
      split_ifs <;> omega)))).trans (hSt2Not δ _ (by omega) (by omega)))
  have hCin2 (δ) (hz : ∀ q : Fin W, δ (rWork q) = 0) :
      (st2 δ (rCtrl ⟨1, ctrl0_lt1 15⟩)).val = (tap29_cXorBit r stA δ).val := by
    change (st2 δ (r ⟨84, tap29_lt84⟩)).val = _
    dsimp only [st2, st1, tap29_stTapXor]
    rw [Function.update_of_ne (rNe (by decide : (84 : ℕ) ≠ 1)), Function.update_self,
      show r ⟨84, tap29_lt84⟩ = r ⟨84 + (⟨0, by omega⟩ : Fin 16).val, tap29_lt84_pool _⟩ from rfl,
      hCln84 ⟨0, by omega⟩ δ hz, zero_add]
  let st4 (δ : BitAssignment n) : BitAssignment n := Function.update (st3 δ) w1 (st3 δ w1 + 1)
  have hSt4Z (δ : BitAssignment n) (j : Fin 16) :
      st4 δ (r ⟨55 + j.val, tap29_lt55 j⟩) = st3 δ (rCtrl ⟨2 + j.val, ctrl0_ltZ 15 j⟩) :=
    (Function.update_of_ne (rNe (by omega)) _ _).trans (congrArg (st3 δ) (hCtrlZ j).symm)
  have hSt2_0 (δ) : st2 δ (rCtrl ⟨0, ctrl0_lt0 15⟩) = stA δ w1 + 1 :=
    (Function.update_self w1 (st1 δ w1 + 1) (st1 δ)).trans (congrArg (· + 1)
        (hSt1Not δ _ (by omega)))
  refine ⟨st4, subspaceStep_of_eq_post
      (subspaceStep_seq_mbu (cz2_step (Var := Var) rWork (r ⟨0,
          midOW_lt0 29⟩) w1 (tap29_ne_0_1 r) st1 ph)
        (subspaceStep_seq_mbu (x1_step (Var := Var) rWork w1 st1 ph1)
        (subspaceStep_seq_mbu (cz2_step (Var := Var) rWork w1 (r ⟨38, tap29_lt38⟩)
            (tap29_ne_1_38 r) st2 ph1)
        (subspaceStep_seq_mbu hAddStep (x1_step (Var := Var) rWork w1 st3 _)))))
      (mkKetOpW_congr rWork (fun _ _ ↦ rfl) fun δ hz ↦ by
        dsimp only [tap29_phPassBOut, ph2, ph1]
        rw [hZVal2 δ, hBVal2 δ, hCin2 δ hz, show rCtrl ⟨0, ctrl0_lt0 15⟩ = w1 from rfl]
        dsimp only [st2, w1]
        rw [Function.update_self, Function.update_of_ne (tap29_ne_1_38 r).symm,
          hSt1Not δ _ (by omega), hSt1Not δ _ (by omega), hSt1Not δ _ (by omega)]),
    fun δ w hw ↦ ?_, fun δ hz hs1 j ↦ ?_, fun δ hz hs0 ↦ ?_⟩
  · by_cases hw1 : w = w1
    · rw [hw1, show st4 δ w1 = st3 δ w1 + 1 from Function.update_self _ _ _,
        h3Not δ w1 fun i e ↦ rNe (a := 1) (by omega) (e.trans (hCtrlZ i)),
        show st2 δ w1 = st1 δ w1 + 1 from Function.update_self _ _ _, CharTwo.add_cancel_right]
    · exact (Function.update_of_ne hw1 _ _).trans ((h3Not δ w fun i e ↦
          hw i (e.trans (hCtrlZ i))).trans
        (Function.update_of_ne hw1 _ _))
  · rw [hSt4Z δ j, h3Idle δ hz ((hSt2_0 δ).trans (hs1.symm ▸ CharTwo.add_self_eq_zero 1)) j,
      hCtrlZ j, hSt2Not δ _ (by omega) (by omega)]
  · rw [congrArg finBitsVal (funext (hSt4Z δ)),
        h3Act δ hz ((hSt2_0 δ).trans (hs0.symm ▸ zero_add 1)),
      hZVal2 δ, hBVal2 δ, hCin2 δ hz]

theorem tap29_pPassB_xor240_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (71 + 29) n)
    (stA : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hCln84 : ∀ (j : Fin 16) (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
    stA δ (r ⟨84 + j.val, tap29_lt84_pool j⟩) = 0) : ∃ stB : BitAssignment n → BitAssignment n,
    SubspaceStep (mkKetOpW rWork stA ph) (mkKetOpW rWork stB (tap29_phPassBOut r stA ph))
    (tap29_pPassB_xor240 v r) ∧ (∀ (δ : BitAssignment n)
    (w : Wire n), (∀ j : Fin 16, w ≠ r ⟨55 + j.val, tap29_lt55 j⟩) → stB δ w = stA δ w) ∧
    (∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) → stA δ (r ⟨1, midOW_lt1 29⟩) = 1 →
    ∀ j : Fin 16, stB δ (r ⟨55 + j.val, tap29_lt55 j⟩) = stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) ∧
    (∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) → stA δ (r ⟨1, midOW_lt1 29⟩) = 0 →
    finBitsVal (fun j : Fin 16 ↦ stB δ (r ⟨55 + j.val, tap29_lt55 j⟩)) =
    (finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) +
    finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨22 + j.val, tap29_lt22 j⟩)) +
    (tap29_cXorBit r stA δ).val) % 2 ^ 16) := by
  obtain ⟨st4, hInner, h4Not, h4Idle, h4Act⟩ := tap29_pPassBInner_step_xor v rWork r stA ph hCln84
  let stB := tap29_stTapXor r st4
  have rNe {a b : ℕ} {ha : a < 71 + 29} {hb : b < 71 + 29} (h : a ≠ b) : r ⟨a, ha⟩ ≠ r ⟨b, hb⟩ :=
    fun e ↦ h (congrArg Fin.val (r.wires.injective e))
  have h4Out (δ) {idx : ℕ} (hi : idx < 71 + 29) (hidx : idx < 55 ∨ 71 ≤ idx) (h84 : idx ≠ 84) :
      st4 δ (r ⟨idx, hi⟩) = stA δ (r ⟨idx, hi⟩) :=
    (h4Not δ _ fun j ↦ rNe (by omega)).trans (Function.update_of_ne (rNe h84) _ _)
  have hBZ (δ) (j : Fin 16) : stB δ (r ⟨55 + j.val, tap29_lt55 j⟩) =
      st4 δ (r ⟨55 + j.val, tap29_lt55 j⟩) :=
    Function.update_of_ne (rNe (by omega)) _ _
  refine ⟨stB, subspaceStep_seq_mbu (tap29_pTapXor_step v rWork r stA ph)
    (subspaceStep_seq_mbu hInner (tap29_pTapXor_step v rWork r st4 (tap29_phPassBOut r stA ph))),
    fun δ w hw ↦ ?_, fun δ hz hs1 j ↦ (hBZ δ j).trans (h4Idle δ hz hs1 j),
    fun δ hz hs0 ↦ (congrArg finBitsVal (funext (hBZ δ))).trans (h4Act δ hz hs0)⟩
  dsimp only [stB, tap29_stTapXor]
  by_cases hw84 : w = r ⟨84, tap29_lt84⟩
  · rw [hw84, Function.update_self, show tap29_cXorBit r st4 δ = tap29_cXorBit r stA δ by
      dsimp only [tap29_cXorBit]
      rw [h4Out δ tap29_lt82 (.inr (by omega)) (by omega), h4Out δ tap29_lt21 (.inl (by omega))
          (by omega),
        h4Out δ tap29_lt81 (.inr (by omega)) (by omega)],
      h4Not δ _ fun j ↦
          rNe (by omega), tap29_stTapXor, Function.update_self, CharTwo.add_cancel_right]
  · rw [Function.update_of_ne hw84, h4Not δ w hw, tap29_stTapXor, Function.update_of_ne hw84]

theorem tap29_pOuterBody_xor240_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (71 + 29) n)
    (st0 : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hCln84 : ∀ (j : Fin 16) (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
    st0 δ (r ⟨84 + j.val, tap29_lt84_pool j⟩) = 0) : ∃ (stPre stBody : BitAssignment n →
    BitAssignment n) (phBody : BitAssignment n → ZMod 2), SubspaceStep (mkKetOpW rWork st0 ph)
    (mkKetOpW rWork stBody phBody) (tap29_pOuterBody_xor240 v r) ∧ (∀ (δ : BitAssignment n)
    (w : Wire n), (∀ j : Fin 16, w ≠ r ⟨55 + j.val, tap29_lt55 j⟩) → stBody δ w = st0 δ w) ∧
    (∀ (δ : BitAssignment n) (j : Fin 16), stBody δ (r ⟨55 + j.val, tap29_lt55 j⟩) =
    stPre δ (r ⟨55 + j.val, tap29_lt55 j⟩) + st0 δ (r ⟨0, midOW_lt0 29⟩)) ∧
    (∃ stA : BitAssignment n → BitAssignment n, (∀ (δ : BitAssignment n),
    (∀ q : Fin W, δ (rWork q) = 0) → finBitsVal (fun j : Fin 16 ↦
    stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) =
    (finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨55 + j.val, tap29_lt55 j⟩)) + tap29_w1HiVal r st0 δ +
    (tap29_cA13Bit r st0 δ).val) % 2 ^ 16) ∧ (∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) =
    0) → st0 δ (r ⟨1, midOW_lt1 29⟩) = 1 → ∀ j : Fin 16, stPre δ (r ⟨55 + j.val, tap29_lt55 j⟩) =
    stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) ∧ (∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) =
    0) → st0 δ (r ⟨1, midOW_lt1 29⟩) = 0 → finBitsVal (fun j : Fin 16 ↦
    stPre δ (r ⟨55 + j.val, tap29_lt55 j⟩)) =
    (finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) +
    finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨22 + j.val, tap29_lt22 j⟩)) +
    (tap29_cXorBit r st0 δ).val) % 2 ^ 16) ∧ (∀ δ : BitAssignment n, phBody δ = ph δ +
    st0 δ (r ⟨0, midOW_lt0 29⟩) * st0 δ (r ⟨40, tap29_lt40⟩) +
    (((finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨55 + j.val, tap29_lt55 j⟩)) + tap29_w1HiVal r st0 δ +
    (tap29_cA13Bit r st0 δ).val) / 2 ^ 16 : ℕ) : ZMod 2) + st0 δ (r ⟨0, midOW_lt0 29⟩) *
    st0 δ (r ⟨1, midOW_lt1 29⟩) + (st0 δ (r ⟨1, midOW_lt1 29⟩) + 1) * st0 δ (r ⟨38, tap29_lt38⟩) +
    (st0 δ (r ⟨1, midOW_lt1 29⟩) + 1) *
    (((finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) +
    finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨22 + j.val, tap29_lt22 j⟩)) +
    (tap29_cXorBit r st0 δ).val) / 2 ^ 16 : ℕ) : ZMod 2))) := by
  let rRef := tap29_rRefl r
  have rNe {a b : ℕ} {ha : a < 71 + 29} {hb : b < 71 + 29} (h : a ≠ b) : r ⟨a, ha⟩ ≠ r ⟨b, hb⟩ :=
    fun e ↦ h (congrArg Fin.val (r.wires.injective e))
  have hRefZ (j : Fin 16) : rRef ⟨1 + j.val, ctrlNot_ltZ 15 j⟩ = r ⟨55 + j.val, tap29_lt55 j⟩ :=
    congrArg r.wires (Fin.ext (by
      have := j.isLt; dsimp [rRef, tap29_rRefl, tap29_fRefl, tap29_idxRefl]; split_ifs <;> omega))
  obtain ⟨stA, hStepA, hANot, hAVal⟩ := tap29_pPassAHi_step v rWork r st0 ph hCln84
  let phA : BitAssignment n → ZMod 2 := fun δ ↦
      ph δ + st0 δ (r ⟨0, midOW_lt0 29⟩) * st0 δ (r ⟨40, tap29_lt40⟩) +
      (((finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨55 + j.val, tap29_lt55 j⟩)) +
      tap29_w1HiVal r st0 δ + (tap29_cA13Bit r st0 δ).val) / 2 ^ 16 : ℕ) : ZMod 2)
  have hAKeep (δ) {idx : ℕ} (hi : idx < 71 + 29) (hidx : idx < 55 ∨ 71 ≤ idx) :
      stA δ (r ⟨idx, hi⟩) = st0 δ (r ⟨idx, hi⟩) :=
    hANot δ _ fun _ ↦ rNe (by omega)
  have hCXorA (δ) : tap29_cXorBit r stA δ = tap29_cXorBit r st0 δ := by
    dsimp only [tap29_cXorBit]
    rw [hAKeep δ tap29_lt82 (.inr (by omega)), hAKeep δ tap29_lt21 (.inl (by omega)),
        hAKeep δ tap29_lt81 (.inr (by omega))]
  have hY22A (δ) : finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨22 + j.val, tap29_lt22 j⟩)) =
      finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨22 + j.val, tap29_lt22 j⟩)) :=
    congrArg finBitsVal (funext fun j ↦ hAKeep δ (tap29_lt22 j) (.inl (by omega)))
  obtain ⟨stB, hStepB, hBNot, hBIdle, hBAct⟩ :=
    tap29_pPassB_xor240_step v rWork r stA phA fun j δ hz ↦
        (hAKeep δ _ (.inr (by omega))).trans (hCln84 j δ hz)
  let phB := tap29_phPassBOut r stA phA
  obtain ⟨stR, hStepR, hRNot, hRFlip⟩ := pCtrlNotReg1_step 15 v rWork rRef stB phB
  refine ⟨stB, stR, phB, subspaceStep_seq_mbu hStepA (subspaceStep_seq_mbu hStepB hStepR),
    fun δ w hw ↦
        (hRNot δ w fun k e ↦ hw k (e.trans (hRefZ k))).trans ((hBNot δ w hw).trans (hANot δ w hw)),
    fun δ j ↦
        ?_, ⟨stA, hAVal, fun δ hz hs1 j ↦ hBIdle δ hz ((hAKeep δ _ (.inl (by omega))).trans hs1) j,
      fun δ hz hs0 ↦
          by rw [hBAct δ hz ((hAKeep δ _ (.inl (by omega))).trans hs0), hY22A δ, hCXorA δ],
      fun δ ↦ by
        dsimp only [phB, tap29_phPassBOut, phA]
        rw [hAKeep δ _ (.inl (by omega)), hAKeep δ _ (.inl (by omega)),
            hAKeep δ _ (.inl (by omega)), hY22A δ, hCXorA δ]⟩⟩
  rw [← hRefZ j, hRFlip δ j, hRefZ j, show rRef ⟨0, ctrlNot_lt0 15⟩ = r ⟨0, midOW_lt0 29⟩ from rfl,
    hBNot δ (r ⟨0, midOW_lt0 29⟩) fun _ ↦ rNe (by omega), hAKeep δ (midOW_lt0 29) (.inl (by omega))]

theorem tap29_cXor_eq_cTapBit {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) :
    tap29_cXorBit r (tap29_st0 r st) δ = tap29_cTapBit r (tap29_st0 r st) δ := by
  let i11 : Fin 14 := ⟨11, by omega⟩
  let fW (j : Fin 14) : ZMod 2 := st δ (r ⟨10 + j.val, tap29_lt10 j⟩)
  let fZ (j : Fin 14) : ZMod 2 := st δ (r ⟨41 + j.val, tap29_lt41 j⟩)
  let c10 : ZMod 2 := tap29_st0 r st δ (r ⟨81, tap29_lt81⟩)
  let c11 : ZMod 2 := tap29_st0 r st δ (r ⟨82, tap29_lt82⟩)
  have hc10Val : c10.val = (tap29_w1LoVal r st δ % 2048 + tap29_zLoVal r st δ % 2048) / 2048 := by
    rw [show c10 = _ from tap29_st0_carryA_bit r st δ ⟨10, by omega⟩,
        majCarryBit_val (Nat.zero_le 1) 10, add_zero]
    rfl
  have hc11Val : c11.val = (tap29_w1LoVal r st δ % 4096 + tap29_zLoVal r st δ % 4096) / 4096 := by
    rw [show c11 = _ from tap29_st0_carryA_bit r st δ ⟨11, by omega⟩,
        majCarryBit_val (Nat.zero_le 1) 11, add_zero]
    rfl
  let aLo := tap29_zLoVal r st δ % 2048
  let bLo := tap29_w1LoVal r st δ % 2048
  have hDiv11 : bLo + aLo = (bLo + aLo) % 2048 + 2048 * c10.val :=
      hc10Val ▸ (Nat.mod_add_div (bLo + aLo) 2048).symm
  have hRemLt : (bLo + aLo) % 2048 < 2048 := Nat.mod_lt _ (by omega)
  have hm := zmod2_maj_id (fZ i11) (fW i11) c10
  have hSumLt : (fZ i11 + fW i11 + c10).val < 2 := ZMod.val_lt _
  rw [show tap29_w1LoVal r st δ % 4096 = _ from tap29_fin14_mod4096_decomp fW,
    show tap29_zLoVal r st δ % 4096 = _ from tap29_fin14_mod4096_decomp fZ] at hc11Val
  change c11.val = ((bLo + 2048 * (fW i11).val) + (aLo + 2048 * (fZ i11).val)) / 4096 at hc11Val
  rw [show (bLo + 2048 * (fW i11).val) + (aLo + 2048 * (fZ i11).val) =
      ((bLo + aLo) % 2048 + 2048 * (fZ i11 + fW i11 + c10).val) +
        4096 * (((fZ i11 + c10) * (fW i11 + c10) + c10).val) by omega,
    Nat.add_mul_div_left _ _ (by omega : 0 < 4096), Nat.div_eq_of_lt (by omega),
        zero_add] at hc11Val
  dsimp only [tap29_cXorBit, tap29_cTapBit]
  rw [tap29_st0_keep r st δ tap29_lt52 (.inl (by omega)),
      tap29_st0_keep r st δ tap29_lt21 (.inl (by omega))]
  change c11 + fW i11 + c10 = ((fZ i11 + 1) + c10) * (fW i11 + c10) + c10
  rw [zmod2_eq_of_val_eq hc11Val]
  exact (zmod2_maj_flip0 (fZ i11) (fW i11) c10).symm
theorem tap29_pMid_xor240_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) (hCln : ∀ (j : Fin 29)
    (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
    st δ (r ⟨71 + j.val, midOW_ltCln 29 j⟩) = 0) (hYG : ∀ (k : Fin 36) (δ : BitAssignment n),
    (∀ q : Fin W, δ (rWork q) = 0) → st δ (r ⟨0, midOW_lt0 29⟩) = 0 →
    st δ (r ⟨5 + k.val, midOW_ltY 29 k⟩) = 0) : SubspaceStep (mkKetOpW rWork st ph)
    (mkKetOpW rWork (midOWPostStTap29 14 tap29_le14_30 r st) (midOWPhaseTap29 r st ph))
    (tap29_pMid_xor240 v r) := by
  let rCarA := tap29_rCarryA r
  let st0 := tap29_st0 r st
  have hk0 {idx : ℕ} (hi : idx < 71 + 29) (h71 : idx < 71) (δ) :
      tap29_st0 r st δ (r ⟨idx, hi⟩) = st δ (r ⟨idx, hi⟩) := tap29_st0_keep r st δ hi (.inl h71)
  obtain ⟨stPre, stBody, phBody, hBodyStep, hBodyNot, hBodyFlip, stA, hAVal, hPreIdle, hPreAct,
      hPhBody⟩ :=
    tap29_pOuterBody_xor240_step v rWork r st0 ph fun j δ hz ↦
      (tap29_st0_keep r st δ (tap29_lt84_pool j) (.inr (by omega))).trans
        ((congrArg (st δ) (congrArg r.wires (Fin.ext (by dsimp; omega)))).trans (hCln ⟨13 +
            j.val, by omega⟩ δ hz))
  let stFinal : BitAssignment n → BitAssignment n := stCarryOut 12 rCarA st stBody
  have hCarAStep : SubspaceStep (mkKetOpW rWork st ph) (mkKetOpW rWork stFinal phBody)
      (tap29_pMid_xor240 v r) :=
    pWrapCarryChain_step 12 v rWork rCarA _ st stBody ph phBody
      (fun i δ hz ↦ (congrArg (st δ) (tap29_rCarryA_out r i)).trans (hCln ⟨i.val, by omega⟩ δ hz))
      (fun u δ _ ↦ hBodyNot δ (rCarA u) fun j e ↦ by
        have hv := congrArg Fin.val (r.wires.injective e)
        have := u.isLt
        have := j.isLt
        dsimp [rCarA, tap29_rCarryA, tap29_fCarryA, tap29_idxCarryA] at hv
        split_ifs at hv <;> omega) hBodyStep
  have hZHi0 (δ) : finBitsVal (fun j : Fin 16 ↦ tap29_st0 r st δ (r ⟨55 + j.val, tap29_lt55 j⟩)) =
      tap29_zHiVal r st δ :=
    congrArg finBitsVal (funext fun j ↦ hk0 (tap29_lt55 j) (by omega) δ)
  have hW1Hi0 (δ) : tap29_w1HiVal r (tap29_st0 r st) δ = tap29_w1HiVal r st δ :=
    congrArg finBitsVal (funext fun j ↦ hk0 (tap29_lt24 j) (by omega) δ)
  have hY22_0 (δ) : finBitsVal (fun j : Fin 16 ↦ tap29_st0 r st δ (r ⟨22 + j.val, tap29_lt22 j⟩)) =
      finBitsVal (fun j : Fin 16 ↦ st δ (r ⟨22 + j.val, tap29_lt22 j⟩)) :=
    congrArg finBitsVal (funext fun j ↦ hk0 (tap29_lt22 j) (by omega) δ)
  dsimp only [st0] at hAVal hPhBody hBodyFlip hPreAct hPreIdle
  have hAV (δ) (hz : ∀ q : Fin W, δ (rWork q) = 0) :
      finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) =
        (tap29_zHiVal r st δ + tap29_w1HiVal r st δ + (tap29_zLoVal r st δ + tap29_w1LoVal r st δ) /
            2 ^ 14) % 2 ^ 16 := by
    rw [hAVal δ hz, hZHi0 δ, hW1Hi0 δ, tap29_cA13Bit_val_eq r st δ]
  refine subspaceStep_of_eq_post hCarAStep (mkKetOpW_congr rWork (fun δ hz ↦ ?_) fun δ hz ↦ ?_)
  · refine eq_midOWPostStTap29_of_finBitsVal 14 tap29_le14_30 rWork r st stPre stFinal δ hz
      (fun w hw ↦ if hm : ∃ i : Fin 13, rCarryOut 12 rCarA i = w then
          match hm with | ⟨i, hi⟩ => hi ▸ writeReg_apply_reg _ _ _ i
        else (writeReg_apply_of_not_mem _ _ _ w hm).trans
          ((hBodyNot δ w hw).trans (writeReg_apply_of_not_mem _ _ _ w hm)))
      (fun j ↦ ?_) (fun hg0 j ↦ ?_) fun _ ↦ ?_
    · refine (writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ ?_).trans
        ((hBodyFlip δ j).trans (congrArg _ (hk0 (midOW_lt0 29) (by omega) δ)))
      have hv := congrArg Fin.val (r.wires.injective ((tap29_rCarryA_out r i).symm.trans hi))
      have := j.isLt
      dsimp at hv
      omega
    · change stPre δ (r ⟨55 + j.val, tap29_lt55 j⟩) = st δ (r ⟨55 + j.val, tap29_lt55 j⟩)
      obtain ⟨hw1L, hw1H, hcTapZ, h22z, _, _⟩ := tap29_yZero_vals rWork r st hYG δ hz hg0
      have hAIdleVal : finBitsVal (fun k : Fin 16 ↦ stA δ (r ⟨55 + k.val, tap29_lt55 k⟩)) =
          finBitsVal (fun k : Fin 16 ↦ st δ (r ⟨55 + k.val, tap29_lt55 k⟩)) := by
        simp only [hAV δ hz, hw1L, hw1H, add_zero, tap29_zLoVal, tap29_zHiVal,
          Nat.div_eq_of_lt (finBitsVal_lt _), Nat.mod_eq_of_lt (finBitsVal_lt _)]
      rcases DynCircExt.bit_cases (st δ (r ⟨1, midOW_lt1 29⟩)) with hs0 | hs1
      · have hBIdleVal : finBitsVal (fun k : Fin 16 ↦ stPre δ (r ⟨55 + k.val, tap29_lt55 k⟩)) =
            finBitsVal (fun k : Fin 16 ↦ st δ (r ⟨55 + k.val, tap29_lt55 k⟩)) := by
          rw [hPreAct δ hz ((hk0 (midOW_lt1 29) (by omega) δ).trans hs0), hAIdleVal, hY22_0 δ, h22z,
              add_zero,
            tap29_cXor_eq_cTapBit r st δ, tap29_cTapBit_val_eq r st δ, hcTapZ, add_zero,
                Nat.mod_eq_of_lt (finBitsVal_lt _)]
        exact gh16_eq_of_finBitsVal_eq hBIdleVal j
      · exact (hPreIdle δ hz ((hk0 (midOW_lt1 29)
            (by omega) δ).trans hs1) j).trans (gh16_eq_of_finBitsVal_eq hAIdleVal j)
    · change finBitsVal (fun j : Fin 16 ↦ stPre δ (r ⟨55 + j.val, tap29_lt55 j⟩)) = _
      rw [tap29_totalSum_div14_mod16]
      obtain ⟨hMod16, _⟩ := gh16_two_pass_hi16 (tap29_zLoVal r st δ) (tap29_zHiVal r st δ)
        (tap29_w1LoVal r st δ) (tap29_w1HiVal r st δ) 0 (tap29_w2HiVal r st δ)
      rw [add_zero, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 14)), add_zero] at hMod16
      rcases DynCircExt.bit_cases (st δ (r ⟨1, midOW_lt1 29⟩)) with hs0 | hs1
      · rw [hPreAct δ hz ((hk0 (midOW_lt1 29) (by omega) δ).trans hs0), hAV δ hz, hY22_0 δ,
          tap29_cXor_eq_cTapBit r st δ, tap29_cTapBit_val_eq r st δ]
        simpa only [tap29_sum30, tap29_w2HiVal, hs0, ↓reduceIte, ← add_assoc] using hMod16
      · rw [congrArg finBitsVal (funext (hPreIdle δ hz ((hk0 (midOW_lt1 29)
            (by omega) δ).trans hs1))), hAV δ hz]
        simpa only [tap29_sum30, tap29_w2HiVal, hs1, one_ne_zero, ↓reduceIte, mul_zero, add_zero,
            Nat.mod_mod] using hMod16
  · rw [hPhBody δ, hk0 (midOW_lt0 29) (by omega) δ, hk0 tap29_lt40 (by omega) δ, hk0 (midOW_lt1 29)
        (by omega) δ,
      hk0 tap29_lt38 (by omega) δ, hZHi0 δ, hW1Hi0 δ, tap29_cA13Bit_val_eq r st δ, hAV δ hz,
          hY22_0 δ,
      tap29_cXor_eq_cTapBit r st δ, tap29_cTapBit_val_eq r st δ]
    exact tap29_phase_eq rWork r st ph hYG δ hz

/-- `MidOWTap29Xor240` (`240 T`, `0 .TOFF`, `kMid = 29`). -/
def midOWTap29XorPkg_240 : MidOWTap29Pkg 14 29 240 where
  hlZ := tap29_le14_30
  pMid := @tap29_pMid_xor240
  counts_wires := @tap29_pMid_xor240_counts_wires
  step_mid := @tap29_pMid_xor240_step
end QuantumComputation.Specs.PhotochemistrySolution.MidOWTap29Xor240

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1WRouter1260
set_option exponentiation.threshold 256
open PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.CoinWrap PhotochemistrySolution.Stage1SingleWrap
  PhotochemistrySolution.Stage1AsymRevEngine PhotochemistrySolution.Stage1WRouter1416
open PhotochemistrySolution.Stage1SplitRouter PhotochemistrySolution.Stage1WRouter1324
  PhotochemistrySolution.Stage1PrefixCerts PhotochemistrySolution.Stage1WRouterPkg
  PhotochemistrySolution.Stage12Instances
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket_X ket_CNOT
    eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1MaskEngine (CustomGateSem
    slot_table_match_get foldPrefixOps prefixOpsT checkPrefixPre checkPrefixCerts PrefixOpsSem
    prefix_ops_sem_of_certs wrapPrefixOps dw_wrap_prefix_ops step_wrap_prefix_ops)
theorem oddBits_eq_shared (x : ℕ) :
    ∀ n : ℕ, oddBits x n = PhotochemistrySolution.Stage1MaskEngine.oddBits x n
  | 0 => rfl
  | n + 1 => by
      dsimp only [oddBits, PhotochemistrySolution.Stage1MaskEngine.oddBits]
      rw [oddBits_eq_shared x n]

theorem checkListPairwiseNe_eq_shared :
    ∀ xs : List ℕ, checkListPairwiseNe xs = Stage1MaskEngine.checkListPairwiseNe xs
  | [] => rfl
  | _ :: xs => by
      dsimp only [checkListPairwiseNe, Stage1MaskEngine.checkListPairwiseNe]
      rw [checkListPairwiseNe_eq_shared xs]

def slotMasksLListRt : List ℕ :=
  [0x1800000000000, 0x5800020000000, 0x1800000000000, (1 <<< 102), 0x1800000000000,
   0x105800020000000, 0x1801e820000000001, 0x20001000000000000, 0x2000000000000000800000,
   (1 <<< 87), 0xf5000000000000040000, 0x28800000000000080000, (1 <<< 71), (1 <<< 87), (1 <<< 71),
   (5 <<< 86), (1 <<< 71), 0x10000000000000040000, 0x3000000000000030001, (11 <<< 72),
   0xb0000000000000000001, (1 <<< 77), 0xa000000000000000010000, 0x830000000000000000100000,
   (1 <<< 72), 0x110a231800000000000180000, 0x23f0000000000000c0001, 0x217000000000000040000,
   (9 <<< 104), (3 <<< 105), (1 <<< 118), 0x40000000000000000000000000040,
   0x1d23a00000000000800001, 0x1d35a00000000002800001, 0x570bd81c1d0000000, 0xe91ae024170000000,
   (1 <<< 155), (1 <<< 159), (3 <<< 155), (1 <<< 156), (1 <<< 160), (1 <<< 66), (1 <<< 161),
   0x7801f820000000001, 0xa801f820000000000]

def slotMasksUListRt : List ℕ :=
  [0x8000010000000, 0x8000010000000, 0x88000000, 0x88000000, 0x40000000, 0x40000000,
   0x211b1804170000001, 0x211b1804170000001, 0x200000, 0x200000, 0xc3a500000000000000100000,
   0xc3a500000000000000100000, 0x30000, 0x30000, 0x20000, 0x20000, 0x80000, 0x80000, (87 <<< 72),
   (87 <<< 72), 0x180000, 0x180000, (5 <<< 87), (5 <<< 87), (0x1549 <<< 77), (0x1549 <<< 77),
   0x800000000080001, 0x800000000080001, 0x200000000a81d2020120000001,
   0x200000000a81d2020120000001, (9 <<< 117), (9 <<< 117), 0x1800000000001, 0x1800000000001,
   (3 <<< 153), (3 <<< 153), 0x4800000000002400000, 0x4800000000002400000, 0x11000000000000200000,
   0x11000000000000200000, 0x11000000000000200000, 0x2221058080a0000001, 0x2221058080a0000001,
   (1 <<< 162), (1 <<< 162)]

def opsRt : List PhotochemistrySolution.Stage1MaskEngine.PrefixOp := [
  .gchunk [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
  .routerEpoch 2 0 ⟨[11, 60], 0x8000010000000,
    [0x1800000000000, 0x5800020000000],
    [0x15800000000000, 0], [1, 2]⟩,
  .gchunk [12],
  .routerEpoch 2 2 ⟨[14, 61], 0x88000000,
    [0x1800000000000, (1 <<< 102)],
    [0x180000a0000000, (1 <<< 102)], [1, 2]⟩,
  .routerEpoch 2 4 ⟨[13, 59], 0x40000000,
    [0x1800000000000, 0x105800020000000],
    [0x131800170000000, 0], [1, 2]⟩,
  .gchunk [15, 16, 17, 18, 19, 20, 21, 22, 23],
  .routerEpoch 2 6 ⟨[24, 25], 0x211b1804170000001,
    [0x1801e820000000001, 0x20001000000000000],
    [0, 0x2e1138380a0000001], [2, 3]⟩,
  .gchunk [27, 43, 45],
  .routerEpoch 2 8 ⟨[44, 46], 0x200000, [0x2000000000000000800000, (1 <<< 87)], [0, 0], [1, 2]⟩,
  .customGate 29 (1 <<< 69) 0x6000000000000000800000,
  .gchunk [31],
  .customGate 32 (1 <<< 71) 0x2200000000001940000,
  .routerEpoch 2 12 ⟨[30, 49], 0x30000, [(1 <<< 71), (1 <<< 87)], [(5 <<< 71), (1 <<< 74)], [1, 2]⟩,
  .routerEpoch 2 14 ⟨[34, 47], 0x20000, [(1 <<< 71), (5 <<< 86)], [(1 <<< 73), 0], [1, 2]⟩,
  .routerEpoch 2 16 ⟨[33, 35], 0x80000,
    [(1 <<< 71), 0x10000000000000040000],
    [(1 <<< 71), 0], [1, 2]⟩,
  .gchunk [36],
  .routerEpoch 2 18 ⟨[37, 40], (87 <<< 72),
    [0x3000000000000030001, (11 <<< 72)],
    [(1 <<< 76), 0], [1, 2]⟩,
  .routerEpoch 2 20 ⟨[38, 39], 0x180000,
    [0xb0000000000000000001, (1 <<< 77)],
    [0x180000, (39 <<< 72)], [1, 2]⟩,
  .gchunk [50, 53],
  .routerEpoch 2 22 ⟨[48, 52], (5 <<< 87),
    [0xa000000000000000010000, 0x830000000000000000100000],
    [(5 <<< 85), 0], [1, 2]⟩,
  .routerEpoch 2 10 ⟨[41, 54], 0xc3a500000000000000100000,
    [0xf5000000000000040000, 0x28800000000000080000],
    [(807 <<< 72), 0xc1a307000000000000180000], [1, 2]⟩,
  .routerEpoch 2 24 ⟨[42, 51], (0x1549 <<< 77),
    [(1 <<< 72), 0x110a231800000000000180000],
    [0xd23a00000000000800001, 0x1530307000000000000080000], [1, 2]⟩,
  .gchunk [55, 56],
  .routerEpoch 2 26 ⟨[57, 58], 0x800000000080001,
    [0x23f0000000000000c0001, 0x217000000000000040000],
    [0x40001a200c838003000020001, 0x20002270059f0001524000000], [1, 2]⟩,
  .gchunk [62, 63, 64, 65],
  .routerEpoch 2 28 ⟨[66, 67], 0x200000000a81d2020120000001,
    [(9 <<< 104), (3 <<< 105)],
    [0, 0], [1, 2]⟩,
  .gchunk [68, 69, 70, 71, 72, 73, 74, 75, 76, 78],
  .routerEpoch 2 30 ⟨[77, 79], (9 <<< 117),
    [(1 <<< 118), 0x40000000000000000000000000040],
    [0, 0], [1, 2]⟩,
  .gchunk [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101,
      102, 103, 104, 105, 106, 107],
  .routerEpoch 2 32 ⟨[108, 110], 0x1800000000001,
    [0x1d23a00000000000800001, 0x1d35a00000000002800001],
    [0x1800000000001, 0], [1, 2]⟩,
  .gchunk [111, 112],
  .routerEpoch 2 34 ⟨[113, 117], (3 <<< 153),
    [0x570bd81c1d0000000, 0xe91ae024170000000],
    [0, 0], [1, 2]⟩,
  .routerEpoch 2 36 ⟨[114, 118], 0x4800000000002400000, [(1 <<< 155), (1 <<< 159)], [0, 0], [1, 2]⟩,
  .routerEpoch 3 38 ⟨[115, 116, 119], 0x11000000000000200000,
    [(3 <<< 155), (1 <<< 156), (1 <<< 160)],
    [(3 <<< 155), (1 <<< 156), (1 <<< 160)], [1, 2, 4]⟩,
  .routerEpoch 2 41 ⟨[109, 120], 0x2221058080a0000001, [(1 <<< 66), (1 <<< 161)], [0, 0], [1, 2]⟩,
  .gchunk [121],
  .routerEpoch 2 43 ⟨[122, 123], (1 <<< 162),
    [0x7801f820000000001, 0xa801f820000000000],
    [0, 0], [1, 2]⟩,
  .gchunk [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]
]

def certsRt : List PhotochemistrySolution.Stage1MaskEngine.PrefixOpCert := [
  .none,
  .router [0x10000000, 0x1800000000000, 0x1800020000000, 0x2000210000000, 0x100000000]
    [8, 9, 10, 11]
    [((false, 2), (false, 4)), ((true, 16), (false, 18)), ((false, 2), (false, 57)),
     ((false, 2), (false, 8))]
    (false, 65) [(false, 2), (false, 36)] [(false, 162), (false, 0)]
    [((false, 2), (false, 8)), ((false, 36), (false, 483))],
  .none,
  .router [0x88000000, 0x1800000000000, 0xa0000000, 0x208000000, 0x1800020000000, 0x100000000,
     0x210000000]
    [7, 8, 9, 10, 11, 14, 60]
    [((false, 8), (false, 2)), ((false, 2), (false, 16)), ((true, 32), (false, 34)),
     ((false, 2), (false, 447)), ((false, 2), (false, 192)), ((true, 2), (false, 0x804)),
     ((false, 272), (false, 0xf5d))]
    (false, 1) [(false, 2), (false, 0x2000)] [(false, 0x604), (false, 0x2000)]
    [((true, 2), (false, 0x804)), ((true, 0x1605), (false, 0x2000))],
  .router [0x40000000, 0x1800000000000, 0x1800020000000, 0x1800170000000, 0x18001d0000000,
      0x100000000,
     0x2000300000000]
    [8, 9, 10, 11, 13, 14]
    [((false, 2), (false, 4)), ((true, 32), (false, 34)), ((false, 2), (false, 192)),
     ((false, 2), (false, 77)), ((true, 2), (false, 400)), ((true, 2), (false, 0x418))]
    (false, 1) [(false, 2), (false, 0x1084)] [(false, 0x1608), (false, 0)]
    [((true, 2), (false, 400)), ((false, 0x1084), (false, 0x1e09))],
  .none,
  .router [0x10004170000000, 0x10020000000000, 0x100380a0000000, 0x1400000000, 0x14000000000,
     0xa000000000, 0x20000000000, 0x400000000, 0x800000000, 0x8400000000, 0x10400000000,
     0x208000000, 0x20000000, 0x100000000, 0x210000000, 0x40000524000000]
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
    [((true, 8), (true, 16)), ((true, 32), (false, 64)), ((false, 128), (false, 0x20000)),
     ((false, 256), (false, 0x10000)), ((true, 512), (false, 0x40000)),
     ((false, 0x80000), (true, 0x110000)), ((false, 0x200000), (true, 0x250400)),
     ((false, 0x800), (false, 0x600000)), ((false, 0x600000), (false, 0x601000)),
     ((true, 0x2000), (false, 0x602000)), ((false, 0x600000), (false, 0x804000)),
     ((true, 0x600000), (false, 0x36002d5)), ((true, 0x600000), (false, 0x4000606)),
     ((false, 0x3e00002), (false, 0x1c600001)), ((false, 0x11600486), (true, 0x1e000481)),
     ((false, 0x20000000), (false, 0x40000000)), ((false, 0x1b608000), (true, 0x9b608000)),
     ((false, 0x1f000143), (false, 0x80000000)), ((false, 0x48000c8), (false, 0x80000000)),
     ((true, 0x16002a0), (false, 0x80000000)), ((false, 0x70f600007), (true, 0x803e00002)),
     ((false, 0x51de00483), (false, 0x170f600007)), ((false, 0x380000000), (true, 0x2063e00002))]
    (true, 0x211c600001) [(true, 0x1803a00002), (false, 0x2000400000)]
        [(false, 0), (true, 0x2e10e00004)]
    [((false, 0x380000000), (true, 0x2063e00002)), ((false, 0x1803e00002), (false, 0x7613000006))],
  .none,
  .router [0x200000, 0x800000, 0x400000, 0x10000]
    [43, 45]
    [((false, 2), (false, 4)), ((false, 16), (true, 8))]
    (false, 1) [(false, 18), (false, 32)] [(false, 0), (false, 0)]
    [((false, 18), (false, 1)), ((false, 32), (false, 1))],
  .custom [0x200000, 0x800000, 0x400000, 0x2800000, 0x1000000]
    [26, 27, 28, 43, 44]
    [((true, 4), (true, 8)), ((false, 16), (false, 10)), ((false, 64), (true, 1)),
     ((false, 2), (false, 4)), ((false, 258), (false, 1))]
    (false, 64) (false, 770) ((false, 32), (false, 128)),
  .none,
  .custom [(1 <<< 68), (1 <<< 70), 0x2200000000001940000]
    [29]
    [((false, 1), (false, 2))]
    (false, 8) (false, 4) ((false, 8), (true, 5)),
  .router [0x30000, 0xc50000, 0x400000, 0x2800000, 0x1000000, 0x2000000, 0x200000, 0x1940000,
      0x10000]
    [26, 27, 28, 29, 30, 31, 32, 43, 45]
    [((true, 4), (true, 8)), ((false, 16), (false, 32)), ((false, 0x400), (true, 64)),
     ((false, 512), (false, 0x800)), ((false, 0x1000), (false, 0x1402)),
     ((false, 103), (false, 0x1000)), ((false, 0x1000), (true, 0x4680)), ((false, 40), (false, 4)),
     ((false, 0x10000), (true, 256))]
    (false, 1) [(false, 0x1000), (false, 0x20000)] [(false, 0x5000), (false, 0x8000)]
    [((false, 0x1000), (false, 0x1402)), ((false, 0x28000), (false, 0x6001))],
  .router [0x20000, 0x100000, 0x400000, 0x2800000, 0x1000000, 0x2000000, 0x200000, 0xc50000,
      0x2a60000,
     0x80000]
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 43, 44, 45, 46]
    [((true, 4), (true, 8)), ((false, 16), (false, 32)), ((false, 0x800), (true, 64)),
     ((false, 0x400), (false, 0x1000)), ((false, 0x2000), (false, 0x2880)),
     ((false, 256), (false, 0x2000)), ((false, 0x2000), (true, 0x8d73)),
     ((true, 512), (false, 0x2000)), ((false, 0x2000), (true, 0x18002)),
     ((false, 0x2a200), (false, 0x4a149)), ((true, 0x6a348), (false, 0xd40ac)),
     ((false, 0xe2200), (false, 0x1c2149)), ((false, 0x29a002), (false, 0x2cc000)),
     ((true, 0x7c349), (false, 0x482000)), ((false, 0xb00000), (false, 0xcb0000)),
     ((false, 40), (false, 4)), ((false, 0x2000028), (false, 64)),
     ((false, 0x2000000), (true, 485)), ((false, 0x8000000), (false, 64))]
    (false, 1) [(false, 0x2000), (false, 0x14000000)] [(false, 0x8000), (false, 0)]
    [((false, 0x2000), (true, 0x18002)), ((false, 0x1004001), (false, 0x14000000))],
  .router [0x80000, 0x40000, 0x400000, 0x2800000, 0x1000000, 0x2000000, 0x200000, 0x2a60000,
      0x1940000]
    [26, 27, 28, 29, 31, 32, 33, 34]
    [((true, 4), (true, 8)), ((false, 16), (false, 32)), ((false, 0x400), (true, 64)),
     ((false, 512), (false, 0x800)), ((false, 128), (false, 0x1000)),
     ((false, 0x1000), (true, 0x2700)), ((true, 1), (false, 0x1000)),
     ((false, 0x1000), (true, 0x613a))]
    (false, 1) [(false, 0x1000), (false, 0x10002)] [(false, 0x1000), (false, 0)]
    [((true, 1), (false, 0x1000)), ((false, 0xb001), (false, 0x13002))],
  .none,
  .router [0x30000, 0x80000, 0x40000, 0x400000, 0x2800000, 0x1000000, 0x2000000, 0x200000, 0xc50000,
     0x1940000]
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]
    [((true, 8), (true, 16)), ((false, 32), (false, 64)), ((false, 0x800), (true, 128)),
     ((false, 0x400), (false, 0x1000)), ((false, 0x2000), (false, 0x2900)),
     ((false, 457), (false, 0x2000)), ((false, 0x2000), (true, 0x8e00)),
     ((true, 2), (false, 0x2000)), ((false, 0x2000), (true, 0x18274)),
     ((false, 0x2a002), (false, 0x4a004)), ((true, 0x6a15b), (false, 0xd4158)),
     ((false, 0xe2002), (false, 0x1c2004)), ((false, 0x29a274), (false, 0x2cc000)),
     ((true, 0x7c006), (false, 0x482000))]
    (false, 0x15c000) [(true, 0xc001), (false, 0x2c000)] [(false, 0x40000), (false, 0)]
    [((false, 0xe2002), (false, 0x1c2004)), ((false, 0xb00000), (false, 0xcb0000))],
  .router [0x180000, 0x100000, 0xc0000, 0x400000, 0x2800000, 0x1000000, 0x2000000, 0x200000,
      0xc50000,
     0x2a60000]
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
    [((true, 8), (true, 16)), ((false, 32), (false, 64)), ((false, 0x800), (true, 128)),
     ((false, 0x400), (false, 0x1000)), ((false, 0x2000), (false, 0x2900)),
     ((false, 512), (false, 0x2000)), ((false, 0x2000), (true, 0x8c75)),
     ((true, 3), (false, 0x2000)), ((false, 0x2000), (true, 0x18002)),
     ((false, 0x2a003), (false, 0x4a007)), ((true, 0x6a293), (false, 0xd4158)),
     ((false, 0xe2003), (false, 0x1c2007)), ((false, 0x29a002), (false, 0x2cc000))]
    (false, 1) [(true, 0x2c0000), (false, 0x80000)] [(false, 1), (false, 0x9c000)]
    [((false, 0x29a002), (false, 0x2cc000)), ((true, 0x7c004), (false, 0x482000))],
  .none,
  .router [0x10000, 0x100000, 0x200000, 0x400000, 0x2800000, 0x1000000, 0x2000000, 0xc50000,
      0x2a60000,
     0x80000]
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 43, 44, 45, 46, 47, 49, 50, 53]
    [((true, 8), (true, 16)), ((false, 32), (false, 64)), ((false, 0x800), (true, 4)),
     ((false, 0x400), (false, 0x1000)), ((false, 0x2000), (false, 0x2880)),
     ((false, 256), (false, 0x2000)), ((false, 0x2000), (true, 0x8cab)),
     ((true, 512), (false, 0x2000)), ((false, 0x2000), (true, 0x18002)),
     ((false, 0x2a200), (false, 0x4a0d9)), ((true, 0x6a314), (false, 0xd40d8)),
     ((false, 0xe2200), (false, 0x1c20d9)), ((false, 0x29a002), (false, 0x2cc000)),
     ((true, 0x7c2d9), (false, 0x482000)), ((false, 0xb00000), (false, 0xcb0000)),
     ((false, 80), (false, 8)), ((false, 0x2000050), (false, 4)), ((false, 0x2000000), (true, 1)),
     ((false, 0x8000000), (false, 4)), ((false, 0x10041cd), (false, 0x14000000)),
     ((false, 0x8010000), (false, 0xc1cc)), ((false, 0x400a0000), (false, 0x2a480000)),
     ((true, 0x80080000), (false, 0x2a000002))]
    (false, 0x28000000) [(false, 0xa000001), (false, 0x130000002)] [(false, 0xa000000), (false, 0)]
    [((false, 0x22000000), (false, 1)), ((false, 0x50000000), (false, 0x80480004))],
  .router [0x400000, 0x2800000, 0x1000000, 0x2000000, 0x200000, 0xc50000, 0x2a60000, 0x1940000,
      0x80000,
     0x100000]
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 49, 50,
     52, 53, 54]
    [((true, 1), (true, 2)), ((false, 4), (false, 8)), ((false, 0x800), (true, 16)),
     ((false, 0x400), (false, 0x1000)), ((false, 0x2000), (false, 0x2820)),
     ((false, 64), (false, 0x2000)), ((false, 0x2000), (true, 0x8c80)),
     ((true, 256), (false, 0x2000)), ((false, 0x2000), (true, 0x18200)),
     ((false, 0x2a100), (false, 0x4a28e)), ((true, 0x6a152), (false, 0xd402b)),
     ((false, 0xe2100), (false, 0x1c228e)), ((false, 0x29a200), (false, 0x2cc000)),
     ((true, 0x7c38e), (false, 0x482000)), ((false, 0xb00000), (false, 0xcb0000)),
     ((false, 0x948000), (false, 0x1400000)), ((false, 10), (false, 1)),
     ((false, 0x400000a), (false, 16)), ((false, 0x4000000), (true, 677)),
     ((false, 0x10000000), (false, 16)), ((false, 0x10042dc), (false, 0x28000000)),
     ((false, 0x10010000), (false, 0xc079)), ((false, 0x800a0000), (false, 0x54480000)),
     ((false, 0xa0000000), (false, 0x100480010)), ((true, 0x100080000), (false, 0x54000200)),
     ((false, 0x40080100), (false, 0x634080300))]
    (false, 0x675400200) [(false, 0x3d428e), (false, 0xa2100)]
        [(false, 0xc9c000), (false, 0x634c1c300)]
    [((false, 0x948000), (false, 0x1400000)), ((false, 0x40080100), (false, 0x634080300))],
  .router [0x400000, 0x2800000, 0x1000000, 0x2000000, 0x200000, 0xc50000, 0x2a60000, 0x1940000,
      0x80000,
     0x100000]
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49,
     50, 51, 52, 53, 54]
    [((true, 1), (true, 2)), ((false, 4), (false, 8)), ((false, 0x800), (true, 16)),
     ((false, 0x400), (false, 0x1000)), ((false, 0x2000), (false, 0x2820)),
     ((false, 64), (false, 0x2000)), ((false, 0x2000), (true, 0x8c80)),
     ((true, 256), (false, 0x2000)), ((false, 0x2000), (true, 0x18200)),
     ((false, 0x2a100), (false, 0x4a28e)), ((true, 0x6a152), (false, 0xd402b)),
     ((false, 0xe2100), (false, 0x1c228e)), ((false, 0x29a200), (false, 0x2cc000)),
     ((true, 0x7c38e), (false, 0x482000)), ((false, 0xb00000), (false, 0xcb0000)),
     ((false, 0x948000), (false, 0x1400000)), ((true, 0x100e000), (true, 0x248080a)),
     ((false, 10), (false, 1)), ((false, 0x800000a), (false, 16)),
     ((false, 0x8000000), (true, 677)), ((false, 0x20000000), (false, 16)),
     ((false, 0x10042dc), (false, 0x50000000)), ((false, 0x20010000), (false, 0xc079)),
     ((false, 0x1000a0000), (false, 0xa8480000)), ((true, 0x100000200), (false, 0xa8480000)),
     ((false, 0x140000000), (false, 0x200480010)), ((true, 0x200080000), (false, 0xa8000200)),
     ((false, 0x80080100), (false, 0x1868080300))]
    (false, 0xaa480000) [(false, 0x4000), (false, 0x22288c6300)]
        [(true, 0x348e80a), (false, 0x2ac0c1c100)]
    [((true, 0x100e000), (true, 0x248080a)), ((true, 0x100000200), (false, 0xa8480000))],
  .none,
  .router [0x80000, 0xc0000, 0x8038003000020000, 0x1f0001524000000, 0x1f820000000000,
      0x1b1804170000000,
     0x400000000000000, 0x1cd800524000000, 0x400000, 0x2800000, 0x1000000, 0x2000000, 0x200000,
     0xc50000, 0x2a60000, 0x1940000, 0xa018002800010000]
    [15, 17, 18, 20, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 55, 56, 57]
    [((false, 16), (false, 32)), ((false, 0x20000), (false, 64)), ((false, 128), (true, 0x40080)),
     ((false, 152), (false, 0x40000)), ((true, 256), (true, 512)),
     ((false, 0x400), (false, 0x800)), ((false, 0x400000), (true, 0x1000)),
     ((false, 0x200000), (false, 0x800000)), ((false, 0x1000000), (false, 0x1402000)),
     ((false, 0x4000), (false, 0x1000000)), ((false, 0x1000000), (true, 0x4608000)),
     ((true, 1), (false, 0x1000000)), ((false, 0x1000000), (true, 0xc008e03)),
     ((false, 0x15000001), (false, 0x25000003)), ((true, 0x35005201), (false, 0x6a002b00)),
     ((false, 0x71000001), (false, 0xe1000003)), ((false, 0x14d008e03), (false, 0x166000000)),
     ((true, 0x3e000002), (false, 0x241000000)), ((true, 0x40000), (false, 0x102010000)),
     ((true, 0x40000), (false, 0xa36110006)), ((false, 0x40000), (true, 0x1f4a08000c))]
    (true, 0x40001) [(true, 0x47e000002), (false, 0x42e000003)]
        [(true, 0x1344140004), (false, 0xc4e1c0008)]
    [((false, 0x40000), (true, 0x1f4a08000c)), ((true, 0x40000), (false, 0x2c2e18000b))],
  .none,
  .router [0x1d2020120000000, 0xc8000100000000, 0x1f820000000000, 0x1b1804170000000,
      0x1058080a0000000,
     0x1b8014170000000, 0x1cd800524000000, 0x1ac004970000000, 0x22021000000000, 0x5802000000000,
     0x1b1800130000000, 0x800000000001b1800130000000]
    [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 59, 62, 63, 64, 65, 66]
    [((false, 4), (false, 8)), ((false, 16), (true, 32)), ((false, 0x1000), (false, 0x2000)),
     ((false, 64), (true, 0x4040)), ((false, 128), (false, 0x4000)),
     ((false, 256), (false, 0x4000)), ((true, 512), (false, 0x4000)),
     ((false, 0x38030), (true, 0x40004)), ((false, 0x28024), (false, 0xb8030)),
     ((false, 0x1c000), (true, 0x103004)), ((false, 0xc0004), (false, 0x3b0038)),
     ((false, 7), (false, 0x400)), ((false, 0x800007), (false, 0x800800)),
     ((true, 0x680005), (false, 0x800005)), ((false, 0x2000000), (true, 0x3000000)),
     ((true, 0xe80000), (false, 0x7680000)), ((true, 0x6e80002), (false, 0x9000000))]
    (true, 0xd40001) [(false, 0x9000000), (false, 0x6000000)] [(false, 0), (false, 0)]
    [((true, 0x6e80002), (false, 0x9000000)), ((false, 0x540004), (false, 0x1b000000))],
  .none,
  .router [64, 0x116000000000000100840, 0x400, 0x800, 0x100000000000000000000000000400]
    [72, 75, 76, 77, 78]
    [((false, 4), (false, 8)), ((false, 40), (false, 48)), ((true, 10), (true, 33)),
     ((false, 128), (true, 192)), ((false, 43), (true, 203))]
    (false, 576) [(false, 128), (false, 33)] [(false, 0), (false, 0)]
    [((false, 128), (true, 192)), ((true, 418), (false, 576))],
  .none,
  .router [0x1800000000000, 0x800000, 0x2800000, 0x400000, 0x1000000, 0x200000, 0xc50000, 0x2a60000,
     0x1940000, 0x80000, 0x100000]
    [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 108]
    [((true, 8), (true, 4)), ((false, 16), (false, 6)), ((false, 0x1000), (true, 32)),
     ((false, 0x800), (false, 0x2000)), ((false, 0x4000), (false, 0x5040)),
     ((false, 128), (false, 0x4000)), ((false, 0x4000), (true, 0x11900)),
     ((true, 512), (false, 0x4000)), ((false, 0x4000), (true, 0x30400)),
     ((false, 0x54200), (false, 0x94512)), ((true, 0xd42a4), (false, 0x1a804a)),
     ((false, 0x1c4200), (false, 0x384512)), ((false, 0x534400), (false, 0x598000)),
     ((true, 0xf8712), (false, 0x904000)), ((false, 0x1600000), (false, 0x1960000)),
     ((false, 0x1290000), (false, 0x2800000)), ((true, 0x201c000), (true, 0x4901002)),
     ((true, 1), (false, 0xe91d002))]
    (true, 1) [(true, 0xe91d002), (true, 0xe9ad004)] [(true, 1), (false, 0)]
    [((true, 1), (false, 0xe91d002)), ((false, 0x10000000), (false, 0xb0006))],
  .none,
  .router [(3 <<< 153), 0x40bd81c1d0000000, 0x81ae024170000000, 0x1f820000000000, 0x1b1804170000000,
     0x400000000000000, 0x1cd800524000000, 0x1ac004970000000, 0x41a7834170000000]
    [15, 17, 18, 19, 22, 23, 24, 25]
    [((false, 8), (false, 16)), ((false, 512), (false, 32)), ((false, 64), (true, 0x440)),
     ((false, 128), (false, 0x400)), ((false, 0x1802), (true, 20)),
     ((false, 0x900), (false, 0x3802)), ((false, 0x1c00), (true, 0x4228)),
     ((false, 0x2014), (false, 0xf012))]
    (false, 1) [(false, 0xb802), (false, 0x1c804)] [(false, 0), (false, 0)]
    [((false, 1), (false, 0xb802)), ((false, 1), (false, 0x1c804))],
  .router [0x4800000000002400000, 0x12800000000000400000, 0x1f820000000000, 0x1b1804170000000,
     0x400000000000000, 0x1cd800524000000, 0x1ac004970000000, 0x40bd81c1d0000000,
     0x801f820000000000, 0x41a7834170000000, (1 <<< 150), 0x8000000000001000000,
     0x10800000000000800000]
    [15, 17, 18, 19, 22, 23, 24, 25, 110, 111, 112, 113, 117]
    [((false, 4), (false, 8)), ((false, 0x2000), (false, 16)), ((false, 32), (true, 0x4020)),
     ((false, 64), (false, 0x4000)), ((false, 0x18080), (true, 256)),
     ((false, 0x8200), (false, 0x38080)), ((false, 0x1c000), (true, 0x42014)),
     ((false, 0x20100), (false, 0xf0088)), ((false, 0x400), (false, 3)),
     ((false, 0x200000), (false, 0x800)), ((false, 0x400000), (false, 0x1000)),
     ((false, 0xc00000), (false, 0xb8080)), ((false, 0xc00000), (false, 0x1c8108))]
    (false, 1) [(false, 0x1000000), (false, 0x2000000)] [(false, 0), (false, 0)]
    [((false, 0x1000000), (true, 2)), ((false, 0x2000000), (true, 2))],
  .router [0x11000000000000200000, 0x1f820000000000, 0x1b1804170000000, 0x400000000000000,
     0x1cd800524000000, 0x1ac004970000000, 0x40bd81c1d0000000, 0x801f820000000000,
     0x41a7834170000000, (3 <<< 153), 0x12800000000000400000]
    [15, 17, 18, 19, 22, 23, 24, 25, 113, 114, 117, 118]
    [((false, 2), (false, 4)), ((false, 0x800), (false, 8)), ((false, 16), (true, 0x1010)),
     ((false, 32), (false, 0x1000)), ((false, 0x6040), (true, 128)),
     ((false, 0x2100), (false, 0xe040)), ((false, 0x7000), (true, 0x1080a)),
     ((false, 0x8080), (false, 0x3c044)), ((false, 512), (false, 0x2e040)),
     ((false, 0x80000), (true, 0x400)), ((false, 512), (false, 0x72084)),
     ((false, 0x200000), (true, 0x400))]
    (false, 1) [(false, 0x180000), (false, 0x100000), (false, 0x400000)]
        [(false, 0x180000), (false, 0x100000), (false, 0x400000)]
    [((false, 0x180000), (true, 1)), ((false, 0x100000), (true, 1)),
     ((false, 0x400000), (true, 1))],
  .router [0x1058080a0000000, 0x1f820000000000, 0x1b1804170000000, 0x400000000000000,
      0x1cd800524000000,
     0x1ac004970000000, 0x40bd81c1d0000000, 0x801f820000000000, 0x400000, 0x2800000, 0x1000000,
     0x2000000, 0x200000, 0x2a60000, 0x1940000, 0x80000, 0x100000, (1 <<< 150),
     0x1000000000000200000]
    [15, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 110, 111, 112, 117, 118, 119]
    [((false, 2), (false, 4)), ((false, 0x80000), (false, 8)), ((false, 16), (true, 0x100010)),
     ((false, 32), (false, 0x100000)), ((false, 0x600040), (true, 128)),
     ((false, 0x200043), (false, 0xe00040)), ((false, 0x700000), (true, 0x108000a)),
     ((false, 0x800080), (false, 0x3c00044)), ((true, 256), (true, 512)),
     ((false, 0x400), (false, 0x800)), ((false, 0x10000000), (true, 0x1000)),
     ((false, 0x8000000), (false, 0x20000000)), ((false, 0x2000), (false, 0x40000000)),
     ((false, 0x40000000), (true, 0x98004000)), ((true, 0x8000), (false, 0x40000000)),
     ((false, 0x40000000), (true, 0x180010000)), ((false, 0x20000), (false, 0x580000800)),
     ((false, 0x800000000), (false, 0x200000400)), ((false, 0x1000000000), (false, 0x440000a00)),
     ((false, 0x3000000000), (false, 0x7200084)), ((false, 0x4000000000), (true, 0x4c0000100)),
     ((false, 0x8000000000), (true, 0x400040000))]
    (true, 0x11400001) [(false, 0x2000000), (false, 0x10000000000)] [(false, 0), (false, 0)]
    [((false, 0x2000000), (true, 0x10000000)), ((false, 0x10000000000), (false, 0x1400001))],
  .none,
  .router [(1 <<< 162), 0x1f820000000000, 0x1b1804170000000, 0x1058080a0000000, 0x1b8014170000000,
     0x1cd800524000000, 0x1ac004970000000, 0x22021000000000, 0x5802000000000]
    [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
    [((false, 2), (false, 4)), ((false, 8), (true, 16)), ((false, 512), (false, 0x400)),
     ((false, 32), (true, 0x820)), ((false, 64), (false, 0x800)), ((false, 128), (false, 0x800)),
     ((true, 256), (false, 0x800)), ((false, 0x7018), (true, 0x8002)),
     ((false, 0x5012), (false, 0x17018)), ((false, 0x3800), (true, 0x20602)),
     ((false, 0x18002), (false, 0x7601c))]
    (false, 1) [(true, 0x78002), (false, 0xa8002)] [(false, 0), (false, 0)]
    [((false, 1), (true, 0x78002)), ((false, 1), (false, 0xa8002))],
  .none
]

abbrev sRtPrefix : ℕ := 0x1fffffffffff

abbrev slotMaskLRt (s : Fin 45) : ℕ := slotMasksLListRt.getD s.val 0
abbrev slotMaskURt (s : Fin 45) : ℕ := slotMasksUListRt.getD s.val 0

def slotBitLRt (c : Fin (2 ^ 41)) (s : Fin 45) : ZMod 2 :=
  let l := if oddBits (env139 c &&& slotMaskLRt s) 181 then (1 : ZMod 2) else 0
  let u := if oddBits (env139 c &&& slotMaskURt s) 181 then (1 : ZMod 2) else 0
  l * (1 + u)

def slotBitHRt (c : Fin (2 ^ 41)) (s : Fin 45) : ZMod 2 :=
  let l := if oddBits (env139 c &&& slotMaskLRt s) 181 then (1 : ZMod 2) else 0
  let u := if oddBits (env139 c &&& slotMaskURt s) 181 then (1 : ZMod 2) else 0
  l * u

def pre256BitsRt (c : Fin (2 ^ 41)) (m sMask : ℕ) (j : Fin 276) : ZMod 2 :=
  if j.val < 41 then
    if c.val.testBit j.val then 1 else 0
  else if j.val < 180 then
    if m.testBit (j.val - 41) && (env139 c).testBit (1 + j.val) then 1 else 0
  else if j.val < 186 then
    0
  else if hL : j.val < 231 then
    if sMask.testBit (j.val - 186) then slotBitLRt c ⟨j.val - 186, by omega⟩ else 0
  else
    if sMask.testBit (j.val - 231) then slotBitHRt c ⟨j.val - 231, by omega⟩ else 0

def tail215BitsRt (c : Fin (2 ^ 41)) (m sMask : ℕ) (i : Fin 235) : ZMod 2 :=
  pre256BitsRt c m sMask ⟨41 + i.val, by omega⟩

def stAtRt {n : ℕ} (rPre : QRegister 276 n) (coinFn : BitAssignment n → Fin (2 ^ 41))
    (base : BitAssignment n → BitAssignment n) (m sMask : ℕ) (δ : BitAssignment n) :
    BitAssignment n :=
  writeReg (base δ) (rPreTail215 rPre) (tail215BitsRt (coinFn δ) m sMask)

theorem stAtRt_apply_rPre {n : ℕ} (rPre : QRegister 276 n)
    (coinFn : BitAssignment n → Fin (2 ^ 41)) (base : BitAssignment n → BitAssignment n)
    (m sMask : ℕ) (δ : BitAssignment n)
    (hCoin : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
      if (coinFn δ).val.testBit k.val then 1 else 0)
    (j : Fin 276) :
    stAtRt rPre coinFn base m sMask δ (rPre j) = pre256BitsRt (coinFn δ) m sMask j := by
  dsimp only [stAtRt]
  by_cases hj : j.val < 41
  · rw [writeReg_apply_of_not_mem]
    · dsimp only [pre256BitsRt]
      rw [_root_.ite_eq_left hj]
      exact hCoin ⟨j.val, hj⟩
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val (rPre.wires.injective hi)
      simp only [QRegister.block_apply_val] at hv
      omega
  · let i : Fin 235 := ⟨j.val - 41, by omega⟩
    have hjEq : rPre j = rPreTail215 rPre i := congrArg rPre (Fin.ext (by
      simp only [QRegister.block_apply_val, i]
      omega))
    rw [hjEq, writeReg_apply_reg]
    dsimp only [tail215BitsRt, i]
    exact congrArg (pre256BitsRt (coinFn δ) m sMask) (Fin.ext (by
      dsimp
      omega))

theorem stAtRt_apply_outside {n : ℕ} (rPre : QRegister 276 n)
    (coinFn : BitAssignment n → Fin (2 ^ 41)) (base : BitAssignment n → BitAssignment n)
    (m sMask : ℕ) (δ : BitAssignment n) {x : Wire n}
    (hx : ∀ i : Fin 235, x ≠ rPreTail215 rPre i) :
    stAtRt rPre coinFn base m sMask δ x = base δ x :=
  writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ hx i hi.symm

theorem stAtRt_zero_eq_base {n : ℕ} (rPre : QRegister 276 n)
    (coinFn : BitAssignment n → Fin (2 ^ 41)) (base : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) (hz : ∀ i : Fin 235, base δ (rPreTail215 rPre i) = 0) :
    stAtRt rPre coinFn base 0 0 δ = base δ := by
  funext x
  by_cases hx : ∃ i : Fin 235, rPreTail215 rPre i = x
  · obtain ⟨i, rfl⟩ := hx
    simp only [stAtRt, writeReg_apply_reg, hz i, tail215BitsRt, pre256BitsRt,
        _root_.ite_eq_right (by omega : ¬ (41 + i.val < 41))]
    split_ifs <;> simp_all only [Nat.zero_testBit, Bool.false_and, Bool.false_eq_true]
  · exact stAtRt_apply_outside rPre coinFn base 0 0 δ fun i e ↦ hx ⟨i, e.symm⟩

theorem pre256BitsRt_gate_zero (c : Fin (2 ^ 41)) (m sMask g : ℕ) (hg : g < 139)
    (hmG : m.testBit g = false) :
    pre256BitsRt c m sMask ⟨41 + g, by omega⟩ = 0 := by
  dsimp only [pre256BitsRt]
  rw [_root_.ite_eq_right (by omega), _root_.ite_eq_left (by omega), show 41 + g - 41 = g by omega,
      hmG]
  rfl

theorem preBitsRt_allowed_eq_env (c : Fin (2 ^ 41)) (m sMask mask : ℕ)
    (hMaskAllowed : (mask &&& (((1 <<< 42) - 1) ||| (m <<< 42))) == mask)
    (u : Fin 180) (hBit : mask.testBit (1 + u.val) = true) :
    pre256BitsRt c m sMask ⟨u.val, by omega⟩ =
      if (env139 c).testBit (1 + u.val) then 1 else 0 := by
  dsimp only [pre256BitsRt]
  by_cases hu41 : u.val < 41
  · rw [_root_.ite_eq_left hu41, env139_coinBit c ⟨u.val, hu41⟩]
  · rw [_root_.ite_eq_right hu41, _root_.ite_eq_left u.isLt]
    have hAllowBit : (((1 <<< 42) - 1) ||| (m <<< 42)).testBit (1 + u.val) = true := by
      have htb : (mask &&& (((1 <<< 42) - 1) ||| (m <<< 42))).testBit (1 + u.val) = true := by
        rw [beq_iff_eq.mp hMaskAllowed, hBit]
      rw [Nat.testBit_and, hBit, Bool.true_and] at htb
      exact htb
    have hLoFalse : ((1 <<< 42) - 1).testBit (1 + u.val) = false := by
      rw [show (1 : ℕ) <<< 42 = 2 ^ 42 by decide, Nat.testBit_two_pow_sub_one,
          decide_eq_false (by omega)]
    rw [Nat.testBit_or, hLoFalse, Bool.false_or, Nat.testBit_shiftLeft,
        decide_eq_true (by omega : 1 + u.val ≥ 42), Bool.true_and,
        show 1 + u.val - 42 = u.val - 41 by omega] at hAllowBit
    rw [hAllowBit, Bool.true_and]

theorem eval_maskParity_on_preRt {n : ℕ} (rPre : QRegister 276 n)
    (c : Fin (2 ^ 41)) (m sMask mask : ℕ)
    (hAllow : (mask &&& (((1 <<< 42) - 1) ||| (m <<< 42))) == mask)
    (γ : BitAssignment n)
    (hγ : ∀ u : Fin 180, mask.testBit (1 + u.val) = true →
      γ (rPre ⟨u.val, by omega⟩) = pre256BitsRt c m sMask ⟨u.val, by omega⟩) :
    maskParity mask (fun u : Fin 180 ↦ γ (rPre ⟨u.val, by omega⟩)) 180 le_rfl =
      if oddBits (env139 c &&& mask) 181 then 1 else 0 := by
  let envFn : BitAssignment 180 := fun u ↦ if (env139 c).testBit (1 + u.val) then 1 else 0
  rw [maskParity_congr_support mask _ envFn 180 le_rfl (fun u _ hbt ↦
        (hγ u hbt).trans (preBitsRt_allowed_eq_env c m sMask mask hAllow u hbt)),
      maskParity_eq_oddBits mask (env139 c) envFn (env139_bit0 c) (fun _ ↦ rfl) 180 le_rfl]

theorem maskParity_rXagPre_eq (c : Fin (2 ^ 41)) (m sMask K : ℕ) (hK : K ≤ 139)
    (mask : ℕ) (hAllow : (mask &&& (((1 <<< 42) - 1) ||| (m <<< 42))) == mask)
    (α : BitAssignment 182)
    (hα : ∀ i : Fin 182, α i = pre256BitsRt c m sMask ⟨i.val, by omega⟩) :
    maskParity mask (fun i ↦ α (rXagPre 139 K hK i)) (41 + K) le_rfl =
      if oddBits (env139 c &&& mask) (42 + K) then 1 else 0 := by
  let envFn : BitAssignment (41 + K) := fun u ↦ if (env139 c).testBit (1 + u.val) then 1 else 0
  rw [maskParity_congr_support mask _ envFn (41 + K) le_rfl (fun u _ hbt ↦
        (hα _).trans ((congrArg (pre256BitsRt c m sMask) (Fin.ext (Nat.zero_add u.val))).trans
          (preBitsRt_allowed_eq_env c m sMask mask hAllow ⟨u.val, by omega⟩ hbt))),
      maskParity_eq_oddBits mask (env139 c) envFn (env139_bit0 c) (fun _ ↦ rfl) (41 + K) le_rfl,
      show 1 + (41 + K) = 42 + K by omega]

def toPkgRC (rc : PhotochemistrySolution.Stage1MaskEngine.RouterEpochCfg) : RouterEpochCfg :=
  ⟨rc.gates, rc.mU, rc.mLs, rc.mYs, rc.maskHs⟩

def stRouterLoadedRt {n R sb : ℕ} (rPre : QRegister 276 n) (hsb : sb + R ≤ 45)
    (coinFn : BitAssignment n → Fin (2 ^ 41)) (base : BitAssignment n → BitAssignment n)
    (m sMask mU : ℕ) (mLs : List ℕ) (δ : BitAssignment n) : BitAssignment n :=
  fun x ↦
    if x = rPre ⟨182, by decide⟩ then
      if oddBits (env139 (coinFn δ) &&& mU) 181 then 1 else 0
    else match findBranch (fun b : Fin R ↦ rPre ⟨186 + sb + b.val, by omega⟩) x with
    | some b =>
        if oddBits (env139 (coinFn δ) &&& (mLs.getD b.val 0)) 181 then 1 else 0
    | none => stAtRt rPre coinFn base m sMask δ x

section PrefixStep
variable {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
  (v : Var) (rWork : QRegister W n) (rPre : QRegister 276 n)
  (coinFn : BitAssignment n → Fin (2 ^ 41))
  (basePre basePost : BitAssignment n → BitAssignment n)
  (phPre phPost : BitAssignment n → ZMod 2)
  (hCoinPre : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ k : Fin 41,
    basePre δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0)
  (hCoinPost : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ k : Fin 41,
    basePost δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0)

abbrev StepAtRt (m sMask : ℕ) (c : DynamicCircuit Var n) : Prop :=
  SubspaceStep
    (mkKetOpW rWork (stAtRt rPre coinFn basePre m sMask) phPre)
    (mkKetOpW rWork (stAtRt rPre coinFn basePost m sMask) phPost) c

include hCoinPre hCoinPost

theorem step_wrapOneGate_of_cp (m sMask g : ℕ) (hg : g < 139) (hmG : m.testBit g = false)
    (cp : ComputeProg 182)
    (hSpec : cp.numAnd = 1 ∧ cp.ValidProg ∅ {wXagGate 139 ⟨g, by omega⟩})
    (hFwdEq : ∀ (c : Fin (2 ^ 41)) (α : BitAssignment 182),
      (∀ i : Fin 182, α i = pre256BitsRt c m sMask ⟨i.val, by omega⟩) →
      α (wXagGate 139 ⟨g, by omega⟩) = 0 →
      cp.fwdBits α =
        Function.update α (wXagGate 139 ⟨g, by omega⟩)
          (if (env139 c).testBit (42 + g) then 1 else 0))
    (mid : DynamicCircuit Var n)
    (hMid : StepAtRt rWork rPre coinFn basePre basePost phPre phPost (m ||| (1 <<< g)) sMask mid) :
    StepAtRt rWork rPre coinFn basePre basePost phPre phPost m sMask
      (wrapDynOnReg v (rPre182 rPre) cp mid) ∧
    (wrapDynOnReg v (rPre182 rPre) cp mid).count .T = 4 + mid.count .T ∧
    (wrapDynOnReg v (rPre182 rPre) cp mid).count .TOFF = mid.count .TOFF := by
  let wG := wXagGate 139 ⟨g, by omega⟩
  have h182Eq (i : Fin 182) : (rPre182 rPre) i = rPre ⟨i.val, by omega⟩ :=
    congrArg rPre (Fin.ext (Nat.zero_add i.val))
  have hClnBase (base : BitAssignment n → BitAssignment n)
      (hC : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0) :
      ∀ u ∈ ({wG} : Finset (Wire 182)), ∀ δ, (∀ q, δ (rWork q) = 0) →
          stAtRt rPre coinFn base m sMask δ ((rPre182 rPre) u) = 0 := by
    intro u hu δ hz
    rw [Finset.mem_singleton.mp hu, h182Eq wG,
        stAtRt_apply_rPre rPre coinFn base m sMask δ (hC δ hz)]
    exact pre256BitsRt_gate_zero (coinFn δ) m sMask g hg hmG
  have hStepEq (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (_ : ∀ q, δ (rWork q) = 0)
      (hC : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0) :
      stepCB (rPre182 rPre) cp.fwdBits (stAtRt rPre coinFn base m sMask δ) =
        stAtRt rPre coinFn base (m ||| (1 <<< g)) sMask δ := by
    let c := coinFn δ
    let α : BitAssignment 182 := fun i ↦ stAtRt rPre coinFn base m sMask δ ((rPre182 rPre) i)
    have hα (i : Fin 182) : α i = pre256BitsRt c m sMask ⟨i.val, by omega⟩ :=
      (congrArg (stAtRt rPre coinFn base m sMask δ)
          (h182Eq i)).trans (stAtRt_apply_rPre rPre coinFn base m sMask δ hC _)
    funext x
    by_cases hx182 : ∃ i : Fin 182, (rPre182 rPre) i = x
    · obtain ⟨i, rfl⟩ := hx182
      rw [stepCB, writeReg_apply_reg]
      change cp.fwdBits α i = _
      rw [hFwdEq c α hα ((hα wG).trans (pre256BitsRt_gate_zero c m sMask g hg hmG)),
        h182Eq i, stAtRt_apply_rPre rPre coinFn base (m ||| (1 <<< g)) sMask δ hC]
      by_cases hiG : i = wG
      · subst hiG
        dsimp only [c, wG, wXagGate, pre256BitsRt]
        rw [Function.update_self, _root_.ite_eq_right (by omega : ¬ 41 + g < 41),
            _root_.ite_eq_left (by omega : 41 + g < 180),
          show 41 + g - 41 = g by omega, show 1 + (41 + g) = 42 + g by omega,
          Nat.testBit_or, Stage1MaskEngine.testBit_one_shiftLeft, decide_eq_true rfl, Bool.or_true,
              Bool.true_and]
      · rw [Function.update_of_ne hiG, hα i]
        change pre256BitsRt c m sMask ⟨i.val, _⟩ = pre256BitsRt c (m ||| (1 <<< g)) sMask ⟨i.val, _⟩
        dsimp only [pre256BitsRt]
        by_cases h41 : i.val < 41
        · rw [_root_.ite_eq_left h41, _root_.ite_eq_left h41]
        · rw [_root_.ite_eq_right h41, _root_.ite_eq_right h41]
          by_cases h180 : i.val < 180
          · rw [_root_.ite_eq_left h180, _root_.ite_eq_left h180, Nat.testBit_or,
                Stage1MaskEngine.testBit_one_shiftLeft,
              decide_eq_false (fun e ↦ hiG (Fin.ext (by dsimp [wG, wXagGate]; omega))),
                  Bool.or_false]
          · rw [_root_.ite_eq_right h180, _root_.ite_eq_right h180]
    · rw [stepCB, writeReg_apply_of_not_mem _ _ _ _ hx182]
      by_cases hxPre : ∃ j : Fin 276, rPre j = x
      · obtain ⟨j, rfl⟩ := hxPre
        have hjGe : 182 ≤ j.val := Nat.le_of_not_lt fun hlt ↦
            hx182 ⟨⟨j.val, hlt⟩, h182Eq ⟨j.val, hlt⟩⟩
        simp only [stAtRt_apply_rPre rPre coinFn base _ sMask δ hC, pre256BitsRt,
          _root_.ite_eq_right (by omega : ¬ j.val < 41),
              _root_.ite_eq_right (by omega : ¬ j.val < 180)]
      · rw [stAtRt_apply_outside rPre coinFn base m sMask δ (fun _ e ↦ hxPre ⟨_, e.symm⟩),
          stAtRt_apply_outside rPre coinFn base (m ||| (1 <<< g)) sMask δ (fun _ e ↦
              hxPre ⟨_, e.symm⟩)]
  obtain ⟨hS, hT, hF, _⟩ :=
      subspaceStep_wrapOnReg_vprog2 v rWork (rPre182 rPre) {wG} cp 1 hSpec.2 hSpec.1
    (stAtRt rPre coinFn basePre m sMask) (stAtRt rPre coinFn basePost m sMask) phPre phPost mid
    (hClnBase basePre hCoinPre) (hClnBase basePost hCoinPost)
    (subspaceStep_congr_in (mkKetOpW_congr rWork (fun δ hz ↦
        hStepEq basePre δ hz (hCoinPre δ hz)) fun _ _ ↦ rfl)
      (subspaceStep_congr_out hMid (mkKetOpW_congr rWork (fun δ hz ↦
          (hStepEq basePost δ hz (hCoinPost δ hz)).symm) fun _ _ ↦ rfl)))
  exact ⟨hS, hT, hF⟩

theorem step_wrapGGateRt (m sMask g : ℕ)
    (hChk : PhotochemistrySolution.Stage1MaskEngine.checkGGatePre fgatesAtOpt m g = true)
    (mid : DynamicCircuit Var n)
    (hMid : StepAtRt rWork rPre coinFn basePre basePost phPre phPost (m ||| (1 <<< g)) sMask mid) :
    StepAtRt rWork rPre coinFn basePre basePost phPre phPost m sMask (wrapGGate v rPre g mid) ∧
    (wrapGGate v rPre g mid).count .T = 4 + mid.count .T ∧
    (wrapGGate v rPre g mid).count .TOFF = mid.count .TOFF := by
  dsimp only [PhotochemistrySolution.Stage1MaskEngine.checkGGatePre] at hChk
  split_ifs at hChk with hg
  simp only [Bool.and_eq_true] at hChk
  obtain ⟨⟨⟨⟨hmFalse, _⟩, _⟩, hgaAllow⟩, hgbAllow⟩ := hChk
  let p := fgatesPrefix139 ⟨g, hg⟩
  let hg1 : g + 1 ≤ 139 := by omega
  rw [wrapGGate, _root_.dite_eq_left hg]
  refine step_wrapOneGate_of_cp v rWork rPre coinFn basePre basePost phPre phPost hCoinPre hCoinPost
    m sMask g hg (eq_false_of_bnot_eq_true hmFalse) (xagStepProg 139 g hg1 p.1 p.2)
    (xagStepProg_singleton_spec 139 g hg1 p.1 p.2) (fun c α hα hG0 ↦ ?_) mid hMid
  have hFwd := fwdBits_xagStepProg 139 g hg1 p.1 p.2 α (hα (wXagA 139)) (hα (wXagB 139)) hG0
  have hgBit : (env139 c).testBit (42 + g) = (oddBits (env139 c &&& p.1)
      (42 + g) && oddBits (env139 c &&& p.2) (42 + g)) :=
    xagEnv_gate_bit c.val c.isLt fgatesPrefix139 (checkGatesWf_imp wf_fgatesPrefix139) 139 le_rfl g
        hg
  dsimp only at hFwd
  rwa [maskParity_rXagPre_eq c m sMask g (Nat.le_of_succ_le hg1) p.1 hgaAllow α hα,
    maskParity_rXagPre_eq c m sMask g (Nat.le_of_succ_le hg1) p.2 hgbAllow α hα, zmod2_ite_mul_b,
        ← hgBit] at hFwd

theorem step_wrapCustomGGateRt (m sMask g a b : ℕ)
    (hChk : PhotochemistrySolution.Stage1MaskEngine.checkCustomGGatePre m g a b = true)
    (hSem : CustomGateSem env139 g a b) (mid : DynamicCircuit Var n)
    (hMid : StepAtRt rWork rPre coinFn basePre basePost phPre phPost (m ||| (1 <<< g)) sMask mid) :
    StepAtRt rWork rPre coinFn basePre basePost phPre phPost m sMask
      (wrapCustomGGate v rPre g a b mid) ∧
    (wrapCustomGGate v rPre g a b mid).count .T = 4 + mid.count .T ∧
    (wrapCustomGGate v rPre g a b mid).count .TOFF = mid.count .TOFF := by
  simp only [Stage1MaskEngine.checkCustomGGatePre, Bool.and_eq_true] at hChk
  obtain ⟨⟨⟨⟨⟨hgDec, hmFalse⟩, _⟩, _⟩, hgaAllow⟩, hgbAllow⟩ := hChk
  have hg : g < 139 := of_decide_eq_true hgDec
  have hmG : m.testBit g = false := eq_false_of_bnot_eq_true hmFalse
  let hg1 : g + 1 ≤ 139 := by omega
  rw [wrapCustomGGate, _root_.dite_eq_left hg]
  refine step_wrapOneGate_of_cp v rWork rPre coinFn basePre basePost phPre phPost hCoinPre hCoinPost
    m sMask g hg hmG (customXagStep139 g hg1 a b) (customXagStep139_singleton_spec g hg1 a b)
    (fun c α hα hG0 ↦ ?_) mid hMid
  have hFwd := fwdBits_customXagStep139 g hg1 a b (maskAllow_not_gateBit hgaAllow hmG)
    (maskAllow_not_gateBit hgbAllow hmG) α (hα (wXagA 139)) (hα (wXagB 139)) hG0
  have hSemC := hSem c
  simp only [← oddBits_eq_shared] at hSemC
  dsimp only at hFwd
  rwa [maskParity_rXagPre_eq c m sMask 139 le_rfl a hgaAllow α hα,
    maskParity_rXagPre_eq c m sMask 139 le_rfl b hgbAllow α hα, zmod2_ite_mul_b, hSemC] at hFwd

theorem step_wrapGChunkRt (gs : List ℕ) (m sMask : ℕ)
    (hChk : PhotochemistrySolution.Stage1MaskEngine.checkGChunkPre fgatesAtOpt m gs = true)
    (mid : DynamicCircuit Var n)
    (hMid : StepAtRt rWork rPre coinFn basePre basePost phPre phPost
      (PhotochemistrySolution.Stage1MaskEngine.foldGatesMask m gs) sMask mid) :
    StepAtRt rWork rPre coinFn basePre basePost phPre phPost m sMask (wrapGChunk v rPre gs mid) ∧
    (wrapGChunk v rPre gs mid).count .T = 4 * gs.length + mid.count .T ∧
    (wrapGChunk v rPre gs mid).count .TOFF = mid.count .TOFF := by
  induction gs generalizing m mid with
  | nil => exact ⟨hMid, by dsimp [wrapGChunk]; omega, rfl⟩
  | cons g gs ih =>
      obtain ⟨hG, hRest⟩ := Bool.and_eq_true_iff.mp hChk
      obtain ⟨ihS, ihT, ihF⟩ := ih (m ||| (1 <<< g)) hRest mid hMid
      obtain ⟨gS, gT, gF⟩ := step_wrapGGateRt v rWork rPre coinFn basePre basePost phPre phPost
        hCoinPre hCoinPost m sMask g hG (wrapGChunk v rPre gs mid) ihS
      exact ⟨gS, by dsimp only [wrapGChunk, List.length]; omega, gF.trans ihF⟩

theorem step_wrapRouterEpochRt {R sb : ℕ} (hsb : sb + R ≤ 45)
    (m sMask : ℕ) (rc : PhotochemistrySolution.Stage1MaskEngine.RouterEpochCfg)
    (hEpoch : PhotochemistrySolution.Stage1MaskEngine.checkRouterEpochPre
      slotMasksLListRt slotMasksUListRt m sMask R sb rc = true)
    (hSem : PhotochemistrySolution.Stage1MaskEngine.RouterEpochSem env139 R rc)
    (mid : DynamicCircuit Var n)
    (hMid : StepAtRt rWork rPre coinFn basePre basePost phPre phPost
      (PhotochemistrySolution.Stage1MaskEngine.foldGatesMask m rc.gates)
      (PhotochemistrySolution.Stage1MaskEngine.foldSlotsMask sb sMask R) mid) :
    StepAtRt rWork rPre coinFn basePre basePost phPre phPost m sMask
      (wrapRouterEpoch v rPre hsb (toPkgRC rc) mid) ∧
    (wrapRouterEpoch v rPre hsb (toPkgRC rc) mid).count .T = (2 * R + 2) + mid.count .T ∧
    (wrapRouterEpoch v rPre hsb (toPkgRC rc) mid).count .TOFF = mid.count .TOFF := by
  simp only [Stage1MaskEngine.checkRouterEpochPre, Bool.and_eq_true] at hEpoch
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hR0, _⟩, hLenG0⟩, hLenL0⟩, hLenY0⟩, hPairNeSh⟩, hgAll⟩, hsFreeAll⟩, _⟩,
    hmUAllow⟩, hLsAll⟩, hYsAll⟩, hSlotTbl⟩ := hEpoch
  have hR : 0 < R := of_decide_eq_true hR0
  have hLenG : rc.gates.length = R := beq_iff_eq.mp hLenG0
  have hLenL : rc.mLs.length = R := beq_iff_eq.mp hLenL0
  have hLenY : rc.mYs.length = R := beq_iff_eq.mp hLenY0
  have hPairNe : checkListPairwiseNe rc.gates = true :=
      (checkListPairwiseNe_eq_shared rc.gates).trans hPairNeSh
  have hSemPkg : RouterEpochSem R (toPkgRC rc) := fun c ↦ by
    obtain ⟨h1, h2⟩ := hSem c
    simp only [← oddBits_eq_shared] at h1 h2
    exact ⟨h1, h2⟩
  have hGatesOk (j : ℕ) (hj : j < R) : rc.gates.getD j 0 < 139 ∧ m.testBit (rc.gates.getD j 0) =
      false := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hgAll _ (List.getElem_mem _))
    exact ⟨of_decide_eq_true h1, eq_false_of_bnot_eq_true h2⟩
  have hSlotsFree (b : ℕ) (hb : b < R) : sMask.testBit (sb + b) = false :=
    eq_false_of_bnot_eq_true (List.all_eq_true.mp hsFreeAll _ (List.mem_range.mpr hb))
  let allowMask := ((1 <<< 42) - 1) ||| (m <<< 42)
  have hLsAllow (j : ℕ) (hj : j < R) : (rc.mLs.getD j 0 &&& allowMask) == rc.mLs.getD j 0 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hLsAll _ (List.getElem_mem _))).2
  have hYsAllow (j : ℕ) (hj : j < R) : (rc.mYs.getD j 0 &&& allowMask) == rc.mYs.getD j 0 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hYsAll _ (List.getElem_mem _))).2
  have rNe {va vb : ℕ} {ha : va < 276} {hb : vb < 276} (h : va ≠ vb) : rPre ⟨va, ha⟩ ≠ rPre ⟨vb, hb⟩
      :=
    fun e ↦ h (congrArg Fin.val (rPre.wires.injective e))
  let uWire := rPre ⟨182, by decide⟩
  let lW (b : Fin R) : Wire n := rPre ⟨186 + sb + b.val, by omega⟩
  let hW (b : Fin R) : Wire n := rPre ⟨231 + sb + b.val, by omega⟩
  let gW (b : Fin R) : Wire n :=
    rPre ⟨41 + rc.gates.getD b.val 0,
        (Nat.add_lt_add_left (hGatesOk b.val b.isLt).1 41).trans (by decide)⟩
  let rDum := rPre ⟨183, by decide⟩
  let wDum := rPre ⟨184, by decide⟩
  let qEnc := rPre ⟨185, by decide⟩
  let hInj := routerInj_on_rPre rPre hsb
  obtain ⟨hlInj, hhInj, hlhNe⟩ := wPairR_inj_props hInj.w_inj
  have hlNeU (b : Fin R) : lW b ≠ uWire := rNe (by omega)
  have hhNeU (b : Fin R) : hW b ≠ uWire := rNe (by omega)
  have hPre182 (mc sc : ℕ) (cv : Fin (2 ^ 41)) : pre256BitsRt cv mc sc ⟨182, by decide⟩ = 0 := by
    simp only [pre256BitsRt, _root_.ite_eq_right (by decide : ¬ (182 : ℕ) < 41),
        _root_.ite_eq_right (by decide : ¬ (182 : ℕ) < 180),
      _root_.ite_eq_left (by decide : (182 : ℕ) < 186)]
  have hgInj : Function.Injective gW := fun b1 b2 e ↦ by
    by_contra hne
    have hv := congrArg Fin.val (rPre.wires.injective e)
    dsimp [gW] at hv
    rw [List.getD_eq_getElem _ _ (by omega : b1.val < rc.gates.length),
      List.getD_eq_getElem _ _ (by omega : b2.val < rc.gates.length)] at hv
    exact absurd (by omega) (Stage1MaskEngine.pairwise_ne_of_check rc.gates hPairNeSh
      b1.val b2.val (by omega) (by omega) (Fin.val_ne_of_ne hne))
  let m' := PhotochemistrySolution.Stage1MaskEngine.foldGatesMask m rc.gates
  let sMask' := PhotochemistrySolution.Stage1MaskEngine.foldSlotsMask sb sMask R
  let cOL := cOuterLoad rPre hsb rc.mU rc.mLs
  let cIE := cInnerEnter rPre hsb rc.mU rc.gates rc.mYs rc.maskHs
  let stRL (base : BitAssignment n → BitAssignment n) :=
      stRouterLoadedRt rPre hsb coinFn base m sMask rc.mU rc.mLs
  let CoinAt (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : Prop :=
    ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0
  let CoinOk (base : BitAssignment n → BitAssignment n) : Prop :=
      ∀ δ, (∀ q, δ (rWork q) = 0) → CoinAt base δ
  have hMulKet {U : Operator (2 ^ n)} {st₁ st₂ : BitAssignment n → BitAssignment n}
      {ph : BitAssignment n → ZMod 2}
      (h : ∀ δ, (∀ q, δ (rWork q) = 0) → U.mulVec (ket (st₁ δ)) = ket (st₂ δ)) :
      U * mkKetOpW rWork st₁ ph = mkKetOpW rWork st₂ ph := matrix_ext_ket fun δ ↦ by
    rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · rw [Matrix.mulVec_smul, h δ hz]
    · rw [Matrix.mulVec_zero]
  have sCirc {st₁ st₂ : BitAssignment n → BitAssignment n} {ph : BitAssignment n → ZMod 2}
      {c : Circuit n}
      (h : c.eval.1 * mkKetOpW rWork st₁ ph = mkKetOpW rWork st₂ ph) :
      SubspaceStep (mkKetOpW rWork st₁ ph) (mkKetOpW rWork st₂ ph)
          (.circuit c : DynamicCircuit Var n) :=
    subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) (mkKetOpW rWork st₁ ph) c) h
  obtain ⟨tOL, fOL⟩ := count_cOuterLoad rPre hsb rc.mU rc.mLs
  obtain ⟨tIE, fIE⟩ := count_cInnerEnter rPre hsb rc.mU rc.gates rc.mYs rc.maskHs
  let inner := (DynamicCircuit.circuit cIE).seq (mid.seq (DynamicCircuit.circuit cIE))
  obtain ⟨tSp, fSp⟩ := counts_pSplitRBracket v uWire lW hW rDum wDum qEnc hInj inner
  have hCntT : (wrapRouterEpoch v rPre hsb (toPkgRC rc) mid).count .T = (2 * R + 2) +
      mid.count .T := by
    dsimp only [wrapRouterEpoch, toPkgRC, inner, cIE, DynamicCircuit.count] at tSp ⊢
    rw [tOL, tSp, tIE]
    omega
  have hCntF : (wrapRouterEpoch v rPre hsb (toPkgRC rc) mid).count .TOFF = mid.count .TOFF := by
    dsimp only [wrapRouterEpoch, toPkgRC, inner, cIE, DynamicCircuit.count] at fSp ⊢
    rw [fOL, fSp, fIE]
    omega
  have hOuterEntry (base : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
      (hCoin : CoinOk base) :
      cOL.eval.1 * mkKetOpW rWork (stAtRt rPre coinFn base m sMask) ph =
          mkKetOpW rWork (stRL base) ph :=
    hMulKet fun δ hz ↦ by
      rw [ket_cOuterLoad]
      refine congrArg ket (funext fun x ↦ ?_)
      have hPar (mask : ℕ) (hA : (mask &&& allowMask) == mask) :=
        eval_maskParity_on_preRt rPre (coinFn δ) m sMask mask hA (stAtRt rPre coinFn base m sMask δ)
          (fun _ _ ↦ stAtRt_apply_rPre rPre coinFn base m sMask δ (hCoin δ hz) _)
      dsimp only [stRL, stRouterLoadedRt]
      by_cases hxU : x = rPre ⟨182, by decide⟩
      · rw [hxU, _root_.ite_eq_left rfl, _root_.ite_eq_left rfl, hPar rc.mU hmUAllow,
          stAtRt_apply_rPre rPre coinFn base m sMask δ (hCoin δ hz)
              ⟨182, by decide⟩, hPre182 m sMask (coinFn δ), zero_add]
      · rw [_root_.ite_eq_right hxU, _root_.ite_eq_right hxU]
        cases hfb : findBranch lW x with
        | none => rfl
        | some b =>
            dsimp only
            have h0 : pre256BitsRt (coinFn δ) m sMask ⟨186 + sb + b.val, by omega⟩ = 0 := by
              simp only [pre256BitsRt, _root_.ite_eq_right (by omega : ¬ 186 + sb + b.val < 41),
                _root_.ite_eq_right (by omega : ¬ 186 + sb + b.val < 180),
                    _root_.ite_eq_right (by omega : ¬ 186 + sb + b.val < 186),
                _root_.dite_eq_left (by omega : 186 + sb + b.val < 231), show 186 + sb + b.val -
                    186 = sb + b.val by omega,
                _root_.ite_eq_right (Bool.eq_false_iff.mp (hSlotsFree b.val b.isLt))]
            rw [hPar _ (hLsAllow b.val b.isLt), findBranch_spec hfb,
              stAtRt_apply_rPre rPre coinFn base m sMask δ (hCoin δ hz) ⟨186 + sb + b.val, _⟩, h0,
                  zero_add]
  have hOuterSq : cOL.eval.1 * cOL.eval.1 = 1 := matrix_ext_ket fun γ ↦ by
    let γ1 (y : Wire n) : ZMod 2 :=
      if y = uWire then γ y + maskParity rc.mU (fun u : Fin 180 ↦
          γ (rPre ⟨u.val, by omega⟩)) 180 le_rfl
      else match findBranch lW y with
      | some b =>
        γ y + maskParity (rc.mLs.getD b.val 0)
            (fun u : Fin 180 ↦ γ (rPre ⟨u.val, by omega⟩)) 180 le_rfl
      | none => γ y
    have hPreEq : (fun u : Fin 180 ↦ γ1 (rPre ⟨u.val, by omega⟩)) = fun u ↦
        γ (rPre ⟨u.val, by omega⟩) :=
      funext fun u ↦ by
        dsimp only [γ1, uWire]
        rw [_root_.ite_eq_right (rNe (by omega)), findBranch_none fun _ ↦ rNe (by omega)]
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, show cOL.eval.1.mulVec (ket γ) = ket γ1 from
      ket_cOuterLoad rPre hsb rc.mU rc.mLs γ, ket_cOuterLoad]
    refine congrArg ket (funext fun x ↦ ?_)
    rw [hPreEq]
    by_cases hxU : x = uWire
    · subst hxU
      dsimp only [γ1, uWire]
      rw [_root_.ite_eq_left rfl, _root_.ite_eq_left rfl, add_assoc, zmod2_add_self, add_zero]
    · dsimp only [γ1, uWire] at hxU ⊢
      rw [_root_.ite_eq_right hxU, _root_.ite_eq_right hxU]
      cases findBranch lW x <;> simp only [add_assoc, zmod2_add_self, add_zero]
  have hOuterExit (base : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
      (hCoin : CoinOk base) :
      cOL.eval.1 * mkKetOpW rWork (stRL base) ph =
          mkKetOpW rWork (stAtRt rPre coinFn base m sMask) ph := by
    rw [← hOuterEntry base ph hCoin, ← Matrix.mul_assoc, hOuterSq, Matrix.one_mul]
  have hInnerEntry (base : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
      (hCoin : CoinOk base) :
      cIE.eval.1 * mkKetOpW rWork (fun δ ↦ stSplitRFwd uWire lW hW (stRL base δ)) ph =
        mkKetOpW rWork (stAtRt rPre coinFn base m' sMask') ph :=
    hMulKet fun δ hz ↦ by
      rw [ket_cInnerEnter rPre hsb m rc.mU rc.gates rc.mYs rc.maskHs hLenG hPairNe hGatesOk hYsAllow
          hmUAllow]
      refine congrArg ket (funext fun x ↦ ?_)
      let c := coinFn δ
      obtain ⟨_, hSemBr⟩ := hSemPkg c
      dsimp only [toPkgRC] at hSemBr
      let γL := stRL base δ
      let γS := stSplitRFwd uWire lW hW γL
      have hγSOther (j : Fin 276) (hj182 : j ≠ ⟨182, by decide⟩)
          (hlx : ∀ b : Fin R, rPre j ≠ lW b) (hhx : ∀ b : Fin R, rPre j ≠ hW b) :
          γS (rPre j) = pre256BitsRt c m sMask j := by
        dsimp only [γS]
        rw [stSplitRFwd_other _ hlx hhx]
        dsimp only [γL, stRL, stRouterLoadedRt, c]
        rw [_root_.ite_eq_right (rPre.wires.injective.ne hj182), findBranch_none hlx,
          stAtRt_apply_rPre rPre coinFn base m sMask δ (hCoin δ hz) j]
      have hγS181 (u : Fin 180) : γS (rPre ⟨u.val, by omega⟩) = pre256BitsRt c m sMask ⟨u.val,
          by omega⟩ :=
        hγSOther _ (Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_trans u.isLt (by decide))))
          (fun _ ↦ rNe (by omega)) (fun _ ↦ rNe (by omega))
      have hPar (mask : ℕ) (hA : (mask &&& allowMask) == mask) :=
        eval_maskParity_on_preRt rPre c m sMask mask hA γS fun u _ ↦ hγS181 u
      have hγLU : γL uWire = if oddBits (env139 c &&& rc.mU) 181 then 1 else 0 := by
        dsimp only [γL, stRL, stRouterLoadedRt, uWire, c]
        rw [_root_.ite_eq_left rfl]
      have hγLL (b : Fin R) : γL (lW b) =
          if oddBits (env139 c &&& rc.mLs.getD b.val 0) 181 then 1 else 0 := by
        dsimp only [γL, stRL, stRouterLoadedRt, c]
        rw [_root_.ite_eq_right (hlNeU b), findBranch_self hlInj b]
      by_cases hxPre : ∃ j : Fin 276, rPre j = x
      · obtain ⟨j, rfl⟩ := hxPre
        rw [stAtRt_apply_rPre rPre coinFn base m' sMask' δ (hCoin δ hz) j]
        by_cases hj182 : j = ⟨182, by decide⟩
        · rw [hj182, _root_.ite_eq_left rfl, hPar rc.mU hmUAllow]
          change γS uWire + _ = _
          dsimp only [γS]
          rw [stSplitRFwd_other _ (fun b ↦ (hlNeU b).symm) (fun b ↦ (hhNeU b).symm),
            hγLU, zmod2_add_self, hPre182 m' sMask' (coinFn δ)]
        · rw [_root_.ite_eq_right (rPre.wires.injective.ne hj182)]
          cases hfbG : findBranch gW (rPre j) with
          | some b =>
              dsimp only
              have hvG0 := findBranch_spec hfbG
              dsimp only [gW] at hvG0
              have hvG : j.val = 41 + rc.gates.getD b.val 0 :=
                congrArg Fin.val (rPre.wires.injective hvG0)
              have hG := hGatesOk b.val b.isLt
              have hγSj : γS (rPre j) = 0 :=
                (congrArg (fun k ↦ γS (rPre k))
                    (Fin.ext hvG : j = ⟨41 + rc.gates.getD b.val 0, by omega⟩)).trans
                  ((hγS181 ⟨41 + rc.gates.getD b.val 0,
                      by omega⟩).trans (pre256BitsRt_gate_zero c m sMask _ hG.1 hG.2))
              have hγSH_mask : hMaskParity rPre hsb (rc.maskHs.getD b.val 0) γS R =
                  if (xorMaskBool (fun q ↦ oddBits (env139 c &&& rc.mLs.getD q 0) 181)
                        (rc.maskHs.getD b.val 0) R && oddBits (env139 c &&& rc.mU) 181)
                  then 1 else 0 := by
                dsimp only [hMaskParity]
                rw [xorMaskZMod2_congr_lt (g := fun q ↦
                    (if oddBits (env139 c &&& rc.mLs.getD q 0) 181 then (1 : ZMod 2) else 0) *
                        γL uWire)
                  _ R (fun q hq ↦ by
                    rw [_root_.dite_eq_left hq, show γS (rPre ⟨231 + sb + q, by omega⟩) =
                        γL (lW ⟨q, hq⟩) * γL uWire from
                      stSplitRFwd_hW hhInj hlhNe γL ⟨q, hq⟩, hγLL ⟨q, hq⟩]),
                  xorMaskZMod2_mul_right, xorMaskZMod2_ite, hγLU, zmod2_ite_mul_b]
              have hm'True : m'.testBit (rc.gates.getD b.val 0) = true := by
                dsimp only [m']
                rw [List.getD_eq_getElem _ _ (by omega : b.val < rc.gates.length),
                  PhotochemistrySolution.Stage1MaskEngine.foldGatesMask_testBit,
                  decide_eq_true (List.getElem_mem (by omega : b.val < rc.gates.length)),
                      Bool.or_true]
              change γS (rPre j) + hMaskParity rPre hsb (rc.maskHs.getD b.val 0) γS R + _ = _
              rw [hγSj, zero_add, hγSH_mask, hPar _ (hYsAllow b.val b.isLt), zmod2_ite_add_b,
                  hSemBr b.val b.isLt]
              dsimp only [c]
              simp only [pre256BitsRt, _root_.ite_eq_right (by omega : ¬ j.val < 41),
                  _root_.ite_eq_left (by omega : j.val < 180),
                show j.val - 41 = rc.gates.getD b.val 0 by omega,
                show 1 + j.val = 42 + rc.gates.getD b.val 0 by omega, hm'True, Bool.true_and]
          | none =>
              dsimp only
              by_cases hj186 : j.val < 186
              · change γS (rPre j) = pre256BitsRt c m' sMask' j
                rw [hγSOther j hj182 (fun _ ↦ rNe (by omega)) (fun _ ↦ rNe (by omega))]
                dsimp only [pre256BitsRt]
                by_cases hj41 : j.val < 41
                · rw [_root_.ite_eq_left hj41, _root_.ite_eq_left hj41]
                · rw [_root_.ite_eq_right hj41, _root_.ite_eq_right hj41]
                  by_cases hj180 : j.val < 180
                  · rw [_root_.ite_eq_left hj180, _root_.ite_eq_left hj180]
                    have hNotMem : j.val - 41 ∉ rc.gates := fun hmem ↦ by
                      obtain ⟨idx, hidxLt, hidxEq⟩ := List.mem_iff_getElem.mp hmem
                      have hjEqGW : rPre j = gW ⟨idx, by omega⟩ := congrArg rPre (Fin.ext (by
                        dsimp [gW]
                        rw [List.getD_eq_getElem _ _ hidxLt, hidxEq]
                        omega))
                      rw [hjEqGW, findBranch_self hgInj ⟨idx, by omega⟩] at hfbG
                      cases hfbG
                    dsimp only [m']
                    rw [Stage1MaskEngine.foldGatesMask_testBit, decide_eq_false hNotMem,
                        Bool.or_false]
                  · rw [_root_.ite_eq_right hj180, _root_.ite_eq_right hj180,
                        _root_.ite_eq_left hj186, _root_.ite_eq_left hj186]
              · have hn41 : ¬ j.val < 41 := by omega
                have hn180 : ¬ j.val < 180 := by omega
                let baseOff : ℕ := if j.val < 231 then 186 else 231
                by_cases hInSlot : sb ≤ j.val - baseOff ∧ j.val - baseOff < sb + R
                · let b : Fin R := ⟨j.val - baseOff - sb, by omega⟩
                  obtain ⟨hTblL, hTblU⟩ := slot_table_match_get
                    slotMasksLListRt slotMasksUListRt sb rc.mU 0 rc.mLs hSlotTbl b.val (by omega)
                  rw [show sb + (0 + b.val) = j.val - baseOff by dsimp [b]; omega] at hTblL hTblU
                  have hs'True : sMask'.testBit (j.val - baseOff) = true := by
                    dsimp only [sMask']
                    rw [Stage1MaskEngine.foldSlotsMask_testBit, decide_eq_true hInSlot,
                        Bool.or_true]
                  by_cases hj231 : j.val < 231
                  · dsimp only [baseOff] at hInSlot hTblL hTblU hs'True
                    rw [_root_.ite_eq_left hj231] at hInSlot hTblL hTblU hs'True
                    have hjEqLW : rPre j = lW b :=
                      congrArg rPre
                          (Fin.ext
                          (by dsimp [b, baseOff]; rw [_root_.ite_eq_left hj231]; omega))
                    rw [hjEqLW, stSplitRFwd_lW hlInj γL b, hγLL b, hγLU]
                    dsimp only [c]
                    simp only [pre256BitsRt, slotBitLRt, _root_.ite_eq_right hn41,
                        _root_.ite_eq_right hn180, _root_.ite_eq_right hj186,
                        _root_.dite_eq_left hj231,
                      _root_.ite_eq_left hs'True, show slotMaskLRt ⟨j.val - 186, by omega⟩ =
                          _ from hTblL,
                      show slotMaskURt ⟨j.val - 186, by omega⟩ = _ from hTblU,
                      List.getD_eq_getElem _ _ (by omega : b.val < rc.mLs.length)]
                  · dsimp only [baseOff] at hInSlot hTblL hTblU hs'True
                    rw [_root_.ite_eq_right hj231] at hInSlot hTblL hTblU hs'True
                    have hjEqHW : rPre j = hW b :=
                      congrArg rPre
                          (Fin.ext
                          (by dsimp [b, baseOff]; rw [_root_.ite_eq_right hj231]; omega))
                    rw [hjEqHW, stSplitRFwd_hW hhInj hlhNe γL b, hγLL b, hγLU]
                    dsimp only [c]
                    simp only [pre256BitsRt, slotBitHRt, _root_.ite_eq_right hn41,
                        _root_.ite_eq_right hn180, _root_.ite_eq_right hj186,
                        _root_.dite_eq_right hj231,
                      _root_.ite_eq_left hs'True, show slotMaskLRt ⟨j.val - 231, by omega⟩ =
                          _ from hTblL,
                      show slotMaskURt ⟨j.val - 231, by omega⟩ = _ from hTblU,
                      List.getD_eq_getElem _ _ (by omega : b.val < rc.mLs.length)]
                · have hNeLH (b : Fin R) : j.val ≠ 186 + sb + b.val ∧ j.val ≠ 231 + sb + b.val := by
                    dsimp only [baseOff] at hInSlot
                    split_ifs at hInSlot <;> exact ⟨by omega, by omega⟩
                  have hs'Eq : sMask'.testBit (j.val - baseOff) = sMask.testBit (j.val - baseOff)
                      := by
                    dsimp only [sMask']
                    rw [Stage1MaskEngine.foldSlotsMask_testBit, decide_eq_false hInSlot,
                        Bool.or_false]
                  change γS (rPre j) = pre256BitsRt c m' sMask' j
                  rw [hγSOther j hj182 (fun b ↦ rNe (hNeLH b).1) (fun b ↦ rNe (hNeLH b).2)]
                  dsimp only [pre256BitsRt, baseOff] at hs'Eq ⊢
                  rw [_root_.ite_eq_right hn41, _root_.ite_eq_right hn41, _root_.ite_eq_right hn180,
                      _root_.ite_eq_right hn180, _root_.ite_eq_right hj186,
                      _root_.ite_eq_right hj186]
                  by_cases hj231 : j.val < 231
                  · rw [_root_.ite_eq_left hj231] at hs'Eq
                    rw [_root_.dite_eq_left hj231, _root_.dite_eq_left hj231, hs'Eq]
                  · rw [_root_.ite_eq_right hj231] at hs'Eq
                    rw [_root_.dite_eq_right hj231, _root_.dite_eq_right hj231, hs'Eq]
      · have hxOut (i : Fin 235) : x ≠ rPreTail215 rPre i := fun e ↦ hxPre ⟨_, e.symm⟩
        have hxNe {j : Fin 276} : x ≠ rPre j := fun e ↦ hxPre ⟨j, e.symm⟩
        rw [_root_.ite_eq_right hxNe, findBranch_none fun _ ↦ hxNe]
        dsimp only
        rw [stSplitRFwd_other _ (fun _ ↦ hxNe) (fun _ ↦ hxNe)]
        dsimp only [stRL, stRouterLoadedRt]
        rw [_root_.ite_eq_right hxNe, findBranch_none fun _ ↦ hxNe]
        dsimp only
        rw [stAtRt_apply_outside rPre coinFn base m sMask δ hxOut,
          stAtRt_apply_outside rPre coinFn base m' sMask' δ hxOut]
  have hInnerSq : cIE.eval.1 * cIE.eval.1 = 1 := matrix_ext_ket fun γ ↦ by
    let γ1 (y : Wire n) : ZMod 2 :=
      if y = uWire then γ y + maskParity rc.mU (fun u : Fin 180 ↦
          γ (rPre ⟨u.val, by omega⟩)) 180 le_rfl
      else match findBranch gW y with
      | some b => γ y + hMaskParity rPre hsb (rc.maskHs.getD b.val 0) γ R +
          maskParity (rc.mYs.getD b.val 0) (fun u : Fin 180 ↦ γ (rPre ⟨u.val, by omega⟩)) 180 le_rfl
      | none => γ y
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, show cIE.eval.1.mulVec (ket γ) = ket γ1 from
      ket_cInnerEnter rPre hsb m rc.mU rc.gates rc.mYs rc.maskHs hLenG hPairNe hGatesOk hYsAllow
          hmUAllow γ,
      ket_cInnerEnter rPre hsb m rc.mU rc.gates rc.mYs rc.maskHs hLenG hPairNe hGatesOk hYsAllow
          hmUAllow γ1]
    refine congrArg ket (funext fun x ↦ ?_)
    have hSameAllow (mask : ℕ) (hAllow : (mask &&& allowMask) == mask) :
        maskParity mask (fun u : Fin 180 ↦ γ1 (rPre ⟨u.val, by omega⟩)) 180 le_rfl =
        maskParity mask (fun u : Fin 180 ↦ γ (rPre ⟨u.val, by omega⟩)) 180 le_rfl :=
      maskParity_congr_support mask _ _ 180 le_rfl fun u _ hbt ↦ by
        dsimp only [γ1, uWire]
        rw [_root_.ite_eq_right (rNe (by omega))]
        cases hfb : findBranch gW (rPre ⟨u.val, by omega⟩) with
        | none => rfl
        | some b =>
            have hv0 := findBranch_spec hfb
            dsimp only [gW] at hv0
            have hv : u.val = 41 + rc.gates.getD b.val 0 :=
              congrArg Fin.val (rPre.wires.injective hv0)
            nomatch (hv ▸ hbt).symm.trans (maskAllow_not_gateBit hAllow (hGatesOk b.val b.isLt).2)
    have hSameHW (b : Fin R) : γ1 (rPre ⟨231 + sb + b.val, by omega⟩) =
        γ (rPre ⟨231 + sb + b.val, by omega⟩) := by
      dsimp only [γ1, uWire]
      rw [_root_.ite_eq_right (rNe (by omega)),
        findBranch_none fun b' ↦ rNe (by
          have := b.isLt
          have := (hGatesOk b'.val b'.isLt).1
          dsimp [gW]
          omega)]
    by_cases hxU : x = uWire
    · subst hxU
      dsimp only [γ1, uWire]
      rw [_root_.ite_eq_left rfl, _root_.ite_eq_left rfl, hSameAllow rc.mU hmUAllow, add_assoc,
          zmod2_add_self, add_zero]
    · dsimp only [γ1, uWire] at hxU ⊢
      rw [_root_.ite_eq_right hxU, _root_.ite_eq_right hxU]
      cases hfb : findBranch gW x with
      | none => rfl
      | some b =>
          dsimp only
          rw [hSameAllow _ (hYsAllow b.val b.isLt),
              hMaskParity_congr rPre hsb (rc.maskHs.getD b.val 0) hSameHW]
          set p :=
              maskParity (rc.mYs.getD b.val 0) (fun u : Fin 180 ↦ γ (rPre ⟨u.val, _⟩)) 180 le_rfl
          set h := hMaskParity rPre hsb (rc.maskHs.getD b.val 0) γ R
          rw [show γ x + h + p + h + p = γ x + (h + h) + (p + p) by ring,
            zmod2_add_self, zmod2_add_self, add_zero, add_zero]
  have hInnerExit : cIE.eval.1 * mkKetOpW rWork (stAtRt rPre coinFn basePost m' sMask') phPost =
      mkKetOpW rWork (fun δ ↦ stSplitRFwd uWire lW hW (stRL basePost δ)) phPost := by
    rw [← hInnerEntry basePost phPost hCoinPost, ← Matrix.mul_assoc, hInnerSq, Matrix.one_mul]
  let eBranch (b : Fin R) (γ : BitAssignment n) : ZMod 2 :=
    maskParity (rc.mLs.getD b.val 0) (fun u : Fin 180 ↦ γ (rPre ⟨u.val, by omega⟩)) 180 le_rfl
  have heIndep (b : Fin R) (γ₁ γ₂ : BitAssignment n)
      (hEq : ∀ x, (∀ j, x ≠ lW j) → (∀ j, x ≠ hW j) → x ≠ rDum → γ₁ x = γ₂ x) : eBranch b γ₁ =
          eBranch b γ₂ :=
    congrArg (fun f ↦ maskParity (rc.mLs.getD b.val 0) f 180 le_rfl)
      (funext fun _ ↦ hEq _ (fun _ ↦ rNe (by omega)) (fun _ ↦ rNe (by omega)) (rNe (by omega)))
  have hMut (δ : BitAssignment n) (_ : ∀ q, δ (rWork q) = 0) (b₁ b₂ : Fin R) (hne : b₁ ≠ b₂)
      (hb1 : stRL basePre δ (lW b₁) = 1) : stRL basePre δ (lW b₂) = 0 := by
    obtain ⟨hMutCert, _⟩ := hSemPkg (coinFn δ)
    dsimp only [toPkgRC] at hMutCert
    dsimp only [stRL, stRouterLoadedRt] at hb1 ⊢
    rw [_root_.ite_eq_right (hlNeU b₁), findBranch_self hlInj b₁] at hb1
    rw [_root_.ite_eq_right (hlNeU b₂), findBranch_self hlInj b₂]
    dsimp only at hb1 ⊢
    cases h : oddBits (env139 (coinFn δ) &&& rc.mLs.getD b₁.val 0) 181
    · exact absurd (h ▸ hb1) (by decide)
    · rw [hMutCert b₁.val b₂.val b₁.isLt b₂.isLt (Fin.val_ne_of_ne hne) h]
      rfl
  have hLoadedPre (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : CoinAt base δ)
      (idx : Fin 276) (h186 : idx.val < 186) (h182 : idx.val ≠ 182) :
      stRL base δ (rPre idx) = pre256BitsRt (coinFn δ) m sMask idx := by
    dsimp only [stRL, stRouterLoadedRt]
    rw [_root_.ite_eq_right (rNe h182), findBranch_none fun _ ↦ rNe (by omega),
      stAtRt_apply_rPre rPre coinFn base m sMask δ hC idx]
  have hLoaded183_185 (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : CoinAt base δ)
      (idx : Fin 276) (hlo : 183 ≤ idx.val) (hhi : idx.val < 186) : stRL base δ (rPre idx) = 0 := by
    rw [hLoadedPre base δ hC idx hhi (by omega)]
    simp only [pre256BitsRt,
      _root_.ite_eq_right (by omega : ¬ idx.val < 41),
          _root_.ite_eq_right (by omega : ¬ idx.val < 180), _root_.ite_eq_left hhi]
  have hLoadedHW (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : CoinAt base δ)
      (b : Fin R) : stRL base δ (hW b) = 0 := by
    dsimp only [stRL, stRouterLoadedRt]
    rw [_root_.ite_eq_right (hhNeU b), findBranch_none (fun b1 e ↦ hlhNe b1 b e.symm),
      stAtRt_apply_rPre rPre coinFn base m sMask δ hC ⟨231 + sb + b.val, _⟩]
    simp only [pre256BitsRt,
      _root_.ite_eq_right (by omega : ¬ 231 + sb + b.val < 41),
          _root_.ite_eq_right (by omega : ¬ 231 + sb + b.val < 180),
      _root_.ite_eq_right (by omega : ¬ 231 + sb + b.val < 186),
          _root_.dite_eq_right (by omega : ¬ 231 + sb + b.val < 231),
      show 231 + sb + b.val - 231 = sb + b.val by omega,
      _root_.ite_eq_right (Bool.eq_false_iff.mp (hSlotsFree b.val b.isLt))]
  have heEq (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (b : Fin R) :
      eBranch b (stRL basePre δ) = stRL basePre δ (lW b) := by
    dsimp only [eBranch]
    rw [eval_maskParity_on_preRt rPre (coinFn δ) m sMask (rc.mLs.getD b.val 0)
        (hLsAllow b.val b.isLt)
      (stRL basePre δ) (fun u _ ↦ hLoadedPre basePre δ (hCoinPre δ hz) ⟨u.val, by omega⟩
        (by dsimp; omega) (by dsimp; omega))]
    dsimp only [stRL, stRouterLoadedRt]
    rw [_root_.ite_eq_right (hlNeU b), findBranch_self hlInj b]
  have sBracket := step_pSplitRBracket hR v rWork uWire lW hW rDum wDum qEnc eBranch hInj heIndep
    (stRL basePre) (stRL basePost) phPre phPost inner hMut
    (fun δ hz ↦ ⟨hLoadedHW basePre δ (hCoinPre δ hz),
      hLoaded183_185 basePre δ (hCoinPre δ hz) ⟨183, by decide⟩ (by decide) (by decide),
      hLoaded183_185 basePre δ (hCoinPre δ hz) ⟨184, by decide⟩ (by decide) (by decide),
      hLoaded183_185 basePre δ (hCoinPre δ hz) ⟨185, by decide⟩ (by decide) (by decide)⟩)
    heEq
    (fun δ hz ↦ by
      have hDum (idx : Fin 276) (h1 : 183 ≤ idx.val) (h2 : idx.val < 186) :
          stRL basePost δ (rPre idx) = stRL basePre δ (rPre idx) :=
        (hLoaded183_185 basePost δ (hCoinPost δ hz) idx h1 h2).trans
          (hLoaded183_185 basePre δ (hCoinPre δ hz) idx h1 h2).symm
      exact ⟨by
          dsimp only [stRL, stRouterLoadedRt, uWire]
          rw [_root_.ite_eq_left rfl, _root_.ite_eq_left rfl],
        fun b ↦ by
          dsimp only [stRL, stRouterLoadedRt]
          rw [_root_.ite_eq_right (hlNeU b), _root_.ite_eq_right (hlNeU b),
              findBranch_self hlInj b],
        fun b ↦
            by rw [hLoadedHW basePost δ (hCoinPost δ hz) b, hLoadedHW basePre δ (hCoinPre δ hz) b],
        hDum ⟨183, by decide⟩ (by decide) (by decide),
        hDum ⟨184, by decide⟩ (by decide) (by decide),
        hDum ⟨185, by decide⟩ (by decide) (by decide),
        fun b ↦ congrArg (fun f ↦ maskParity (rc.mLs.getD b.val 0) f 180 le_rfl)
          (funext fun u ↦ (hLoadedPre basePost δ (hCoinPost δ hz) ⟨u.val, by omega⟩
              (by dsimp; omega) (by dsimp; omega)).trans
            (hLoadedPre basePre δ (hCoinPre δ hz) ⟨u.val, by omega⟩
              (by dsimp; omega) (by dsimp; omega)).symm)⟩)
    ((sCirc (hInnerEntry basePre phPre hCoinPre)).seq (hMid.seq (sCirc hInnerExit)))
  exact ⟨(sCirc (hOuterEntry basePre phPre hCoinPre)).seq
    (sBracket.seq (sCirc (hOuterExit basePost phPost hCoinPost))), hCntT, hCntF⟩
end PrefixStep

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem prefixPre_opsRt :
    checkPrefixPre fgatesAtOpt slotMasksLListRt slotMasksUListRt 0 0 opsRt = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem prefixCerts_opsRt :
    checkPrefixCerts fgatesAtOpt opsRt certsRt = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem fold_opsRt :
    foldPrefixOps 0 0 opsRt = (m25Prefix, sRtPrefix) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem t_opsRt :
    prefixOpsT opsRt = 502 := by
  decide +kernel

theorem env139_hGate (c : Fin (2 ^ 41)) (g : ℕ) (hg : g < 139) :
    (env139 c).testBit (42 + g) =
      (Stage1MaskEngine.oddBits (env139 c &&& (fgatesAtOpt g).1) (42 + g) &&
       Stage1MaskEngine.oddBits (env139 c &&& (fgatesAtOpt g).2) (42 + g)) := by
  have h :=
    xagEnv_gate_bit c.val c.isLt fgatesPrefix139 (checkGatesWf_imp wf_fgatesPrefix139) 139 le_rfl g
        hg
  change (env139 c).testBit (42 + g) =
    (oddBits (env139 c &&& (fgatesAtOpt g).1) (42 + g) &&
     oddBits (env139 c &&& (fgatesAtOpt g).2) (42 + g)) at h
  simpa only [oddBits_eq_shared] using h

theorem sem_opsRt : PrefixOpsSem env139 opsRt :=
  prefix_ops_sem_of_certs env139_bit0 env139_hGate opsRt certsRt prefixCerts_opsRt

def wrapPrefixRt {Var : Type} {n : ℕ} (v : Var) (rPre : QRegister 276 n)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  wrapPrefixOps (wrapGChunk v rPre) (wrapCustomGGate v rPre)
    (fun R sb hsb rc m ↦ wrapRouterEpoch (R := R) (sb := sb) v rPre hsb (toPkgRC rc) m)
    opsRt mid

theorem dw_wrapPrefixRt {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rPre : QRegister 276 n) (hr : ∀ j : Fin 276, S (rPre j))
    (mid : DynamicCircuit Var n) (hd : DynWires S mid) :
    DynWires S (wrapPrefixRt v rPre mid) :=
  dw_wrap_prefix_ops (wrapGChunk v rPre) (wrapCustomGGate v rPre)
    (fun R sb hsb rc m ↦ wrapRouterEpoch (R := R) (sb := sb) v rPre hsb (toPkgRC rc) m)
    (fun gs m h ↦ dw_wrapGChunk v rPre hr gs m h)
    (fun g a b m h ↦ dw_wrapCustomGGate v rPre hr g a b m h)
    (fun R sb hsb rc m h ↦
      dw_wrapRouterEpoch (R := R) (sb := sb) v rPre hr hsb (toPkgRC rc) m h)
    opsRt mid hd

theorem step_wrapPrefixRt_clean {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (rPre : QRegister 276 n)
    (coinFn : BitAssignment n → Fin (2 ^ 41))
    (basePre basePost : BitAssignment n → BitAssignment n)
    (phPre phPost : BitAssignment n → ZMod 2)
    (hCoinPre : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ k : Fin 41,
      basePre δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0)
    (hCoinPost : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ k : Fin 41,
      basePost δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0)
    (hClnPre : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ i : Fin 235, basePre δ (rPreTail215 rPre i) = 0)
    (hClnPost : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ i : Fin 235, basePost δ (rPreTail215 rPre i) = 0)
    (mid : DynamicCircuit Var n)
    (hMid : SubspaceStep
      (mkKetOpW rWork (stAtRt rPre coinFn basePre m25Prefix sRtPrefix) phPre)
      (mkKetOpW rWork (stAtRt rPre coinFn basePost m25Prefix sRtPrefix) phPost) mid) :
    SubspaceStep (mkKetOpW rWork basePre phPre) (mkKetOpW rWork basePost phPost)
      (wrapPrefixRt v rPre mid) ∧
    (wrapPrefixRt v rPre mid).count .T = 502 + mid.count .T ∧
    (wrapPrefixRt v rPre mid).count .TOFF = mid.count .TOFF ∧
    (∀ S : Wire n → Prop, (∀ j : Fin 276, S (rPre j)) → DynWires S mid →
      DynWires S (wrapPrefixRt v rPre mid)) := by
  obtain ⟨hS, hT, hF⟩ := step_wrap_prefix_ops
    (Step := StepAtRt rWork rPre coinFn basePre basePost phPre phPost)
    (wrapGChunk v rPre) (wrapCustomGGate v rPre)
    (fun R sb hsb rc m ↦ wrapRouterEpoch (R := R) (sb := sb) v rPre hsb (toPkgRC rc) m)
    (fun m sMask gs c hCk hM ↦
      step_wrapGChunkRt v rWork rPre coinFn basePre basePost phPre phPost hCoinPre hCoinPost gs m
          sMask hCk c hM)
    (fun m sMask g a b c hCk hSm hM ↦
      step_wrapCustomGGateRt v rWork rPre coinFn basePre basePost phPre phPost hCoinPre hCoinPost m
          sMask g a b hCk hSm c hM)
    (fun m sMask R sb hsb rc c hCk hSm hM ↦
      step_wrapRouterEpochRt v rWork rPre coinFn basePre basePost phPre phPost hCoinPre hCoinPost
          hsb m sMask rc hCk hSm c hM)
    opsRt 0 0 mid prefixPre_opsRt sem_opsRt (by
      dsimp only [StepAtRt]
      rwa [fold_opsRt])
  exact ⟨subspaceStep_congr_in
      (mkKetOpW_congr rWork (fun δ hz ↦
          (stAtRt_zero_eq_base rPre coinFn basePre δ (hClnPre δ hz)).symm) fun _ _ ↦ rfl)
      (subspaceStep_congr_out hS
        (mkKetOpW_congr rWork (fun δ hz ↦
            stAtRt_zero_eq_base rPre coinFn basePost δ (hClnPost δ hz)) fun _ _ ↦ rfl)),
    t_opsRt ▸ hT, hF, fun _ hr hd ↦ dw_wrapPrefixRt v rPre hr mid hd⟩

attribute [irreducible] wrapPrefixRt

def hold70BitsRt (c : Fin (2 ^ 41)) (i : Fin 90) : ZMod 2 :=
  pre256BitsRt c m25Prefix sRtPrefix ⟨186 + i.val, by have := i.isLt; omega⟩


theorem mkKetOpW_mul_of_ket {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n)
    (U : Operator (2 ^ n)) (st₁ st₂ : BitAssignment n → BitAssignment n)
    (ph₁ ph₂ : BitAssignment n → ZMod 2)
    (h : ∀ δ, (∀ q, δ (rWork q) = 0) →
      QubitizationWalkSem.bitSign (ph₁ δ) • U.mulVec (ket (st₁ δ)) =
      QubitizationWalkSem.bitSign (ph₂ δ) • ket (st₂ δ)) :
    U * mkKetOpW rWork st₁ ph₁ = mkKetOpW rWork st₂ ph₂ := by
  refine matrix_ext_ket fun δ ↦ ?_
  rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul]
    exact h δ hz
  · rw [Matrix.mulVec_zero]

theorem mkKetOpW_mul_ket_eq {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n)
    (U : Operator (2 ^ n)) (st₁ st₂ : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2)
    (h : ∀ δ, (∀ q, δ (rWork q) = 0) → U.mulVec (ket (st₁ δ)) = ket (st₂ δ)) :
    U * mkKetOpW rWork st₁ ph = mkKetOpW rWork st₂ ph :=
  mkKetOpW_mul_of_ket rWork U st₁ st₂ ph ph fun δ hz ↦ congrArg _ (h δ hz)

theorem step_circ_mkKetOpW {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n)
    (st₁ st₂ : BitAssignment n → BitAssignment n) (ph₁ ph₂ : BitAssignment n → ZMod 2)
    (c : Circuit n) (h : c.eval.1 * mkKetOpW rWork st₁ ph₁ = mkKetOpW rWork st₂ ph₂) :
    SubspaceStep (mkKetOpW rWork st₁ ph₁) (mkKetOpW rWork st₂ ph₂)
      (.circuit c : DynamicCircuit Var n) :=
  subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) (mkKetOpW rWork st₁ ph₁) c) h

theorem left_inv_of_sq_one {d : ℕ} {U A B : Operator d} (hsq : U * U = 1) (h : U * A = B) :
    U * B = A := by
  rw [← h, ← Matrix.mul_assoc, hsq, Matrix.one_mul]

def pRevRt526 {Var : Type} {n : ℕ} (v : Var) (rTot : QRegister dLayout n) : DynamicCircuit Var n :=
    .seq (.circuit (cPreCnot40 (rTot.compose rOut40Layout))) (wrapPrefixRt v (rTot.compose rPreRev)
    (dRevInner v rTot))
theorem dw_pRevRt526 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (rTot : QRegister dLayout n)
    (hOuter : ∀ k : Fin 41, S (rTot (rOuter41Layout k)))
    (hOut40 : ∀ j : Fin 40, S (rTot (rOut40Layout j)))
    (hPreRev : ∀ j : Fin 276, S ((rTot.compose rPreRev) j)) (hScr148 : ∀ k : Fin 1493, k.val < 148 →
    S (rTot (rScrCompact1493 k))) : DynWires S (pRevRt526 v rTot) :=
    ⟨circWires_cPreCnot40 (rTot.compose rOut40Layout) hOut40,
    dw_wrapPrefixRt v (rTot.compose rPreRev) hPreRev _ (dw_dRevInner v rTot hOuter hOut40 hScr148)⟩
theorem step_and_counts_pRevRt526_rScrLayout {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rTot : QRegister dLayout n) :
    SubspaceStep ((rTot.embedUnitary oRef209.uLocal).1 *
    (rTot.compose rScrLayout).basisOutcomeProjector 0)
    ((rTot.compose rScrLayout).basisOutcomeProjector 0) (pRevRt526 v rTot) ∧
    (pRevRt526 v rTot).count .T = 526 ∧ (pRevRt526 v rTot).count .TOFF = 0 := by
  let decodeCoin := decodeTier1W11Opt1424Coin; let coreGates := rgates;
  let coreMask0 := coreMask0Sym96; let coreMask1 := coreMask1Sym96;
  let midPx := midPreXSym96
  let midPairs := fun j : Fin 32 ↦ compileBilinearPairs (midTermsSym96 j)
  let tailPx := tailPreXSym96
  let tailPairs := fun s : Fin 5 ↦ compileBilinearPairs (tailTermsSym96 s)
  have hMidBnd : ∀ j : Fin 32, checkPairsBound (49 + 143) (midPairs j) = true :=
      midBnd_of_bilinear checkBilinearTerms_midTermsSym96;
      have hMidEval :=
      midEval_of_bilinear checkBilinearTerms_midTermsSym96 evalBilinearBool_midTerms_coin;
      have hTailBnd : ∀ s : Fin 5, checkPairsBound (42 + 143 + s.val) (tailPairs s) = true :=
      tailBnd_of_bilinear checkBilinearTerms_tailTermsSym96;
      have hTailEval :=
      tailEval_of_bilinear checkBilinearTerms_tailTermsSym96 evalBilinearBool_tailTerms_coin;
      let rW :=
      rTot.compose rScrLayout; let rPre :=
                                 rTot.compose rPreRev; let rHold :=
                                                         rTot.compose rHold70Rev;
                                                         let coinFn : BitAssignment n → Fin (2 ^ 41)
                                                         :=
                                                         coinOfAmb rTot;
                                                         let gMid (η : BitAssignment n)
                                                         (j : Fin 32) : Bool :=
                                                         preCnotBit40 (zeroNEremOutMask (decodeCoin
                                                         (coinOfAmb rTot η)))
                                                         (mid32OutIdx j);
                                                         let gTail (η : BitAssignment n)
                                                         (s : Fin 5) : Bool :=
                                                         preCnotBit40 (zeroNEremOutMask (decodeCoin
                                                         (coinOfAmb rTot η))) (tail5OutIdx s)
  have liftDisj : ∀ {a b : ℕ} {rA : QRegister a dLayout} {rB : QRegister b dLayout},
      rA.DisjointWires rB → (rTot.compose rA).DisjointWires (rTot.compose rB) :=
    fun hd ↦ disj_of_ne fun i j e ↦ disj_ne hd i j (rTot.wires.injective e)
  have djCoreMid := liftDisj (disj_rRevCore_rOutMid32 143 hM5_143);
  have djCoreTail := liftDisj (disj_rRevCore_rOutTail5 143 hM5_143);
  have djTmpMid := liftDisj (disj_rRevTmp_rOutMid32 143 hM5_143);
  have djPredMid := liftDisj (disj_rMidPred_rOutMid32 143 hM5_143)
  have djTailMid : (rTot.compose rOutTail5).DisjointWires (rTot.compose rOutMid32) :=
      disj_of_ne fun s j e ↦
      mid32_ne_tail5 j s (congrArg Fin.val (rOut40Layout.wires.injective (rTot.wires.injective
      e))).symm
  have djHoldMid := liftDisj disj_rHold70Rev_rOutMid32;
  have djHoldTail := liftDisj disj_rHold70Rev_rOutTail5; let rDom := rTot.compose rDom2;
  have djHoldCore := liftDisj disj_rHold70Rev_rRevCore;
  have djHoldTmp := liftDisj disj_rHold70Rev_rRevTmp;
  have djHoldPred := liftDisj disj_rHold70Rev_rMidPred;
  have djDomMid := liftDisj disj_rDom2_rOutMid32; have djDomTail := liftDisj disj_rDom2_rOutTail5;
  have djDomHold := liftDisj disj_rDom2_rHold70Rev; have djDomTmp := liftDisj disj_rDom2_rRevTmp
  have sPre : SubspaceStep
      ((rTot.embedUnitary oRef209.uLocal).1 * rW.basisOutcomeProjector 0)
      (mkKetOpW rW (stPreCnotSplit decodeCoin rTot) (fun _ ↦ 0))
      (.circuit (cPreCnot40 (rTot.compose rOut40Layout))) :=
    subspaceStep_congr_in (uLocal_mul_rScrLayout_eq_mkKetOpW oRef209 rTot)
      (subspaceStep_congr_out
        (subspaceStep_of_circuit (Var := Var)
          (mkKetOpW rW (stStage1 decodeCoin rTot) (fun _ ↦ 0))
          (cPreCnot40 (rTot.compose rOut40Layout)))
        (cPreCnot40_mul_stStage1_eq_stPreCnotSplit decodeCoin rTot))
  let dTier1 := xUnloadChunkCzPairsXSeqDyn v (outWireOfReg pos32 (rTot.compose rOutMid32)) 0
    (fun s ↦ midPx ⟨s % 32, mod32_lt s⟩)
    (fun s ↦ wirePairsOfReg (rTot.compose (rMidPred 143 hM5_143)) (midPairs ⟨s % 32, mod32_lt s⟩))
        (.circuit .identity) 32
  let dTmpTier1 := wrapDynOnReg v (rTot.compose (rRevTmp 143 hM5_143)) cpRevTmp dTier1
  let dTier2 := xUnloadChunkCzPairsXSeqDyn v (outWireOfReg pos5 (rTot.compose rOutTail5)) 0
    (fun s ↦ tailPx ⟨s % 5, mod5_lt s⟩)
    (fun s ↦ wirePairsOfReg (rTot.compose (rTailPred 143 hM5_143)) (tailPairs ⟨s % 5, mod5_lt s⟩))
        (.circuit .identity) 5
  let stCoreHold (δ : BitAssignment n) : BitAssignment n :=
    writeReg (writeReg (stCoreClean 143 hM5_143 coreGates coreMask0 coreMask1 rTot δ) rHold
        (hold70BitsRt (coinFn δ)))
      rDom (fun _ ↦ 0)
  let stTier1Hold (δ : BitAssignment n) : BitAssignment n :=
    writeReg (writeReg (stTier1Done decodeCoin 143 hM5_143 coreGates coreMask0 coreMask1 rTot δ)
      rHold (hold70BitsRt (coinFn δ))) rDom (fun _ ↦ 0)
  let stTmpHold (δ : BitAssignment n) : BitAssignment n :=
    writeReg (writeReg (stTmpClean decodeCoin 143 hM5_143 coreGates coreMask0 coreMask1 rTot δ)
      rHold (hold70BitsRt (coinFn δ))) rDom (fun _ ↦ 0)
  have hPredNotDom (u : Fin (49 + 143)) (h68 : u.val ≠ 68) (h70 : u.val ≠ 70) :
      (rTot.compose (rMidPred 143 hM5_143)) u ∉ Set.range rDom.wires := fun ⟨b, hb⟩ ↦ by
    obtain ⟨k, hkEq, hk26⟩ : ∃ k : Fin 1493, dom2WireFn b = rScrCompact1493 k ∧
        (k.val = 26 ∨ k.val = 28) := by
      fin_cases b <;> exact ⟨_, rfl, by decide⟩
    have he : rScrCompact1493 k = midPredWireFn 143 hM5_143 u :=
        hkEq.symm.trans (rTot.wires.injective hb)
    have hScrNe {m : Fin 1493} (hne : k.val ≠ m.val) (h : rScrCompact1493 k = rScrCompact1493 m) :
        False :=
      hne (congrArg Fin.val (rScrCompact1493.wires.injective h))
    have := u.isLt
    dsimp only [midPredWireFn] at he
    split_ifs at he with _ _ h2 _
    · exact hScrNe (by dsimp; omega) he
    · exact rScr_ne_rOuter41 _ _ he
    · have := Nat.le_of_ble_eq_true h2
      exact hScrNe (by dsimp; omega) he
    · exact rScr_ne_rOut40 _ _ he
    · exact hScrNe (by dsimp; omega) he
  have hPredEqDom0 : (rTot.compose (rMidPred 143 hM5_143)) ⟨68, by decide⟩ = rDom ⟨0, by decide⟩ :=
      congrArg rTot.wires rfl
  have hPredEqDom1 : (rTot.compose (rMidPred 143 hM5_143)) ⟨70, by decide⟩ = rDom ⟨1, by decide⟩ :=
      congrArg rTot.wires rfl
  have hDropDomHold (stB : BitAssignment n) (δ : BitAssignment n) (u : Fin (49 + 143))
      (h68 : u.val ≠ 68) (h70 : u.val ≠ 70) :
      writeReg (writeReg stB rHold (hold70BitsRt (coinFn δ))) rDom (fun _ ↦ 0)
        ((rTot.compose (rMidPred 143 hM5_143)) u) = stB ((rTot.compose (rMidPred 143 hM5_143)) u) :=
    (writeReg_apply_of_not_mem _ rDom _ _ (hPredNotDom u h68 h70)).trans
      (writeReg_apply_of_not_mem _ rHold _ _ fun ⟨i, hi⟩ ↦ disj_ne djHoldPred i u hi)
  have sTier1 := subspaceStep_triangularTierX pos32 v rW (rTot.compose (rMidPred 143 hM5_143))
    (rTot.compose rOutMid32) (fun _ ↦ 49 + 143) midPx midPairs stTmpHold gMid
    (fun _ ↦ le_rfl) hMidBnd (fun s u _ ↦ disj_ne djPredMid u s)
    (fun j δ hz ↦ by
      simp only [stTmpHold, writeReg_apply_of_not_mem _ rDom _ _ (fun ⟨i, hi⟩ ↦
          disj_ne djDomMid i j hi),
        writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨i, hi⟩ ↦ disj_ne djHoldMid i j hi),
        stTmpClean, stepCB, writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦
            disj_ne djTmpMid i j hi),
        stTier1Done, writeReg_apply_of_not_mem _ _ _ _ (fun ⟨s, hs⟩ ↦ disj_ne djTailMid s j hs),
        stCoreClean, writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ disj_ne djCoreMid i j hi)]
      obtain ⟨m, hm⟩ := rOut40Layout_sub_scr ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
      exact (congrArg δ (congrArg rTot.wires hm)).trans (hz m))
    (fun j δ hz ↦ by
      let c := coinOfAmb rTot δ
      let m40 := zeroNEremOutMask (decodeCoin c)
      let predDom (u : ℕ) : Bool :=
          decide (u ≠ 68 ∧ u ≠ 70) && midPredBit 143 coreGates coreMask0 coreMask1 c m40 u
      refine ⟨predDom, fun u _ ↦ ?_, ?_⟩
      · have hUn (t : ℕ) : updPrefix pos32 (rTot.compose rOutMid32) (stTmpHold δ)
            (fun q ↦ if gMid δ ⟨q % 32, Nat.mod_lt q pos32⟩ then 1 else 0) t
            ((rTot.compose (rMidPred 143 hM5_143)) u) =
                stTmpHold δ ((rTot.compose (rMidPred 143 hM5_143)) u) := by
          induction t with
          | zero => rfl
          | succ _ ih => exact (Function.update_of_ne (disj_ne djPredMid u _) _ _).trans ih
        rw [hUn j.val]
        by_cases h68 : u.val = 68
        · dsimp only [stTmpHold, predDom]
          rw [show u = ⟨68, by decide⟩ from Fin.ext h68, hPredEqDom0, writeReg_apply_reg]
          rfl
        · by_cases h70 : u.val = 70
          · dsimp only [stTmpHold, predDom]
            rw [show u = ⟨70, by decide⟩ from Fin.ext h70, hPredEqDom1, writeReg_apply_reg]
            rfl
          · rw [show predDom u.val = midPredBit 143 coreGates coreMask0 coreMask1 c m40 u.val by
                simp only [predDom, decide_eq_true (And.intro h68 h70), Bool.true_and]]
            dsimp only [stTmpHold]
            rw [hDropDomHold _ δ u h68 h70]
            exact stTmpClean_midPred decodeCoin 143 hM5_143 coreGates coreMask0 coreMask1 rTot δ hz
                u
      · rw [pairsParityBool_congr_off_dom (f₂ := midPredBit 143 coreGates coreMask0 coreMask1 c m40)
          (fun u h68 h70 ↦ by
            dsimp only [predDom]
            rw [decide_eq_true (And.intro h68 h70), Bool.true_and])
          (midPairs j) (midPairs_noDom j)]
        exact hMidEval c j)
  have hTmpCln : ∀ u ∈ sRevTmp, ∀ δ : BitAssignment n, (∀ m, δ (rW m) = 0) →
      stTier1Hold δ ((rTot.compose (rRevTmp 143 hM5_143)) u) = 0 := fun u hu δ hz ↦ by
    simp only [stTier1Hold, writeReg_apply_of_not_mem _ rDom _ _ (fun ⟨i, hi⟩ ↦
        disj_ne djDomTmp i u hi),
      writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨i, hi⟩ ↦ disj_ne djHoldTmp i u hi)]
    obtain ⟨_, _, _, _, _, hHi⟩ :=
        stCoreClean_bits 143 hM5_143 coreGates coreMask0 coreMask1 rTot δ hz
    have hScr0 (k : ℕ) (hk : k = 146 ∨ k = 147) :
        writeReg (stCoreClean 143 hM5_143 coreGates coreMask0 coreMask1 rTot δ)
            (rTot.compose rOutTail5)
          (fun s ↦ if gTail δ s then 1 else 0) (rTot (rScrCompact1493 ⟨k, by omega⟩)) = 0 :=
      (writeReg_apply_of_not_mem _ _ _ _ fun ⟨_, hs⟩ ↦
          rScr_ne_rOut40 _ _ (rTot.wires.injective hs).symm).trans
        (hHi _ (by dsimp only; omega))
    rcases Finset.mem_insert.mp hu with rfl | h5
    · exact hScr0 146 (Or.inl rfl)
    · exact Finset.mem_singleton.mp h5 ▸ hScr0 147 (Or.inr rfl)
  have hTmpOutComm (δ : BitAssignment n) :
      stTmpHold δ = stepCB (rTot.compose (rRevTmp 143 hM5_143)) cpRevTmp.fwdBits (stTier1Hold δ)
          := by
    simp only [stTier1Hold, stTmpHold, stTmpClean,
      stepCB_writeReg_comm (rTot.compose (rRevTmp 143 hM5_143)) rDom
        (disj_of_ne fun i j e ↦ disj_ne djDomTmp j i e.symm) cpRevTmp.fwdBits,
      stepCB_writeReg_comm (rTot.compose (rRevTmp 143 hM5_143)) rHold
        (disj_of_ne fun i j e ↦ disj_ne djHoldTmp j i e.symm) cpRevTmp.fwdBits]
  have hTmpComm (δ : BitAssignment n) :
      stepCB (rTot.compose (rRevTmp 143 hM5_143)) cpRevTmp.fwdBits
        (writeReg (stTier1Hold δ) (rTot.compose rOutMid32) (fun j ↦ if gMid δ j then 1 else 0)) =
      writeReg (stTmpHold δ) (rTot.compose rOutMid32) (fun j ↦ if gMid δ j then 1 else 0) := by
    rw [stepCB_writeReg_comm (rTot.compose (rRevTmp 143 hM5_143)) (rTot.compose rOutMid32)
      djTmpMid cpRevTmp.fwdBits _ (stTier1Hold δ), ← hTmpOutComm δ]
  have sTmpTier1 :=
      (subspaceStep_wrapOnReg_vprog2 v rW (rTot.compose (rRevTmp 143 hM5_143)) sRevTmp cpRevTmp 2
    cpRevTmp_spec.2 cpRevTmp_spec.1
    (fun δ ↦ writeReg (stTier1Hold δ) (rTot.compose rOutMid32) (fun j ↦ if gMid δ j then 1 else 0))
    stTier1Hold (fun _ ↦ 0) (fun _ ↦ 0) dTier1
    (fun u hu δ hz ↦ (writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦
        disj_ne djTmpMid u j hj.symm).trans
      (hTmpCln u hu δ hz))
    hTmpCln
    (subspaceStep_congr_in
      (mkKetOpW_congr rW (ph₁ := fun _ ↦ 0) (ph₂ := fun _ ↦ 0) (fun δ _ ↦ hTmpComm δ)
          (fun _ _ ↦ rfl))
      (subspaceStep_congr_out sTier1
        (mkKetOpW_congr rW (ph₁ := fun _ ↦ 0) (ph₂ := fun _ ↦ 0) (fun δ _ ↦ hTmpOutComm δ)
            (fun _ _ ↦ rfl))))).1
  have hTier1HoldEq (δ : BitAssignment n) :
      stTier1Hold δ = writeReg (stCoreHold δ) (rTot.compose rOutTail5)
          (fun s ↦ if gTail δ s then 1 else 0) := by
    dsimp only [stTier1Hold, stTier1Done, stCoreHold, gTail]
    rw [← writeReg_comm_of_disj rHold (rTot.compose rOutTail5) djHoldTail]
    exact (writeReg_comm_of_disj rDom (rTot.compose rOutTail5) djDomTail _ _ _).symm
  have sTier2 := subspaceStep_congr_in
    (mkKetOpW_congr rW (ph₁ := fun _ ↦ 0) (ph₂ := fun _ ↦ 0) (fun δ _ ↦ hTier1HoldEq δ)
        (fun _ _ ↦ rfl))
    (subspaceStep_triangularTierX pos5 v rW (rTot.compose (rTailPred 143 hM5_143))
      (rTot.compose rOutTail5) (fun s ↦ 42 + 143 + s.val) tailPx tailPairs stCoreHold gTail
      (fun _ ↦ by omega) hTailBnd
      (fun s u hu ↦ rTot.wires.injective.ne (rTailPred_ne_rOutTail5_of_lt 143 hM5_143 s u hu))
      (fun s δ hz ↦ by
        simp only [stCoreHold, writeReg_apply_of_not_mem _ rDom _ _ (fun ⟨i, hi⟩ ↦
            disj_ne djDomTail i s hi),
          writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨i, hi⟩ ↦ disj_ne djHoldTail i s hi),
          stCoreClean, stepCB, writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦
              disj_ne djCoreTail i s hi)]
        obtain ⟨m, hm⟩ := rOut40Layout_sub_scr ⟨tail5OutIdx s, tail5OutIdx_lt40 s⟩
        exact (congrArg δ (congrArg rTot.wires hm)).trans (hz m))
      (fun s δ hz ↦ by
        let c := coinOfAmb rTot δ
        let m40 := zeroNEremOutMask (decodeCoin c)
        let predDom (u : ℕ) : Bool := decide (u ≠ 68 ∧ u ≠ 70) && tailPredBit 143 coreGates c m40 u
        refine ⟨predDom, fun u hu ↦ ?_, ?_⟩
        · have huMid : (rTot.compose (rTailPred 143 hM5_143)) u =
              (rTot.compose (rMidPred 143 hM5_143)) ⟨u.val, by omega⟩ :=
            congrArg rTot.wires (congrArg (midPredWireFn 143 hM5_143)
                (Fin.ext (Nat.zero_add u.val)))
          by_cases hlt42 : u.val < 42 + 143
          · have hUn (t : ℕ) (ht : t ≤ 5) : updPrefix pos5 (rTot.compose rOutTail5) (stCoreHold δ)
                (fun q ↦ if gTail δ ⟨q % 5, Nat.mod_lt q pos5⟩ then 1 else 0) t
                ((rTot.compose (rTailPred 143 hM5_143)) u) =
                stCoreHold δ ((rTot.compose (rTailPred 143 hM5_143)) u) := by
              induction t with
              | zero => rfl
              | succ q ih =>
                  exact (Function.update_of_ne (rTot.wires.injective.ne
                    (rTailPred_ne_rOutTail5_of_lt 143 hM5_143 _ u (by dsimp only; omega))) _
                        _).trans (ih (by omega))
            rw [hUn s.val (Nat.le_of_lt s.isLt)]
            by_cases h68 : u.val = 68
            · dsimp only [stCoreHold, predDom]
              rw [(huMid.trans (congrArg _ (Fin.ext h68))).trans hPredEqDom0, h68,
                  writeReg_apply_reg]
              rfl
            · by_cases h70 : u.val = 70
              · dsimp only [stCoreHold, predDom]
                rw [(huMid.trans (congrArg _ (Fin.ext h70))).trans hPredEqDom1, h70,
                    writeReg_apply_reg]
                rfl
              · rw [show predDom u.val = tailPredBit 143 coreGates c m40 u.val by
                    simp only [predDom, decide_eq_true (And.intro h68 h70), Bool.true_and], huMid]
                dsimp only [stCoreHold]
                rw [hDropDomHold _ δ ⟨u.val, by omega⟩ h68 h70, ← huMid]
                exact stCoreClean_tailPred_lt42M decodeCoin 143 hM5_143 coreGates coreMask0
                    coreMask1 rTot δ hz u hlt42
          · rw [show predDom u.val = tailPredBit 143 coreGates c m40 u.val by
                simp only [predDom, decide_eq_true (And.intro (by omega : u.val ≠ 68)
                    (by omega : u.val ≠ 70)),
                  Bool.true_and]]
            let q : Fin 5 := ⟨u.val - (42 + 143), by omega⟩
            have h2f : Nat.ble (u.val + 1) (42 + 143) = false := Bool.eq_false_iff.mpr fun l ↦
                hlt42 (Nat.le_of_ble_eq_true l)
            have hwEq : (rTot.compose (rTailPred 143 hM5_143)) u = (rTot.compose rOutTail5) q := by
              rw [huMid]
              change rTot (midPredWireFn 143 hM5_143 ⟨u.val, _⟩) = rTot (rOutTail5 q)
              have h1f : Nat.ble (u.val + 1) 42 = false :=
                Bool.eq_false_iff.mpr fun l ↦ absurd (Nat.le_of_ble_eq_true l) (by omega)
              simp only [midPredWireFn, beq_false_of_ne (by omega : u.val ≠ 0), h1f, h2f,
                  Bool.false_eq_true, ↓reduceIte,
                Nat.ble_eq_true_of_le u.isLt]
              exact congrArg rTot.wires (congrArg rOutTail5.wires (Fin.ext (Nat.mod_eq_of_lt
                  q.isLt)))
            rw [hwEq,
                updPrefix_tail5_readback rTot _ _ s.val (Nat.le_of_lt s.isLt) q
                (by dsimp only [q]; omega)]
            simp only [show (⟨q.val % 5, Nat.mod_lt q.val pos5⟩ : Fin 5) =
                q from Fin.ext (Nat.mod_eq_of_lt q.isLt), gTail]
            dsimp only [tailPredBit]
            simp only [h2f, Bool.false_eq_true, ↓reduceIte]
            rw [show u.val = 42 + 143 + q.val by dsimp [q]; omega]
            generalize (q : Fin 5) = q0
            fin_cases q0 <;> rfl
        · rw [pairsParityBool_congr_off_dom (f₂ := tailPredBit 143 coreGates c m40)
            (fun u h68 h70 ↦ by
              dsimp only [predDom]
              rw [decide_eq_true (And.intro h68 h70), Bool.true_and])
            (tailPairs s) (tailPairs_noDom s)]
          exact hTailEval c s))
  have stSplit_off (δ : BitAssignment n) (w : Wire dLayout) (hw : ∀ q, w ≠ rOut40Layout q) :
      stPreCnotSplit decodeCoin rTot δ (rTot w) = δ (rTot w) := by
    dsimp only [stPreCnotSplit, stTailOnly]
    rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨_, hj⟩ ↦ hw _ (rTot.wires.injective hj).symm),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨_, hs⟩ ↦ hw _ (rTot.wires.injective hs).symm)]
  have hCoinId (δ : BitAssignment n) (_ : ∀ m, δ (rW m) = 0) (k : Fin 41) :
      δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0 := by
    refine (congrArg δ ?_).trans (coinOfAmb_bit rTot δ k)
    change rTot (preRevWireFn _) = _
    simp only [preRevWireFn, _root_.dite_eq_left k.isLt]
  have hCoinSplit (δ : BitAssignment n) (hz : ∀ m, δ (rW m) = 0) (k : Fin 41) :
      stPreCnotSplit decodeCoin rTot δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0 :=
    (stSplit_off δ _ (rPreRev_ne_rOut40 _)).trans (hCoinId δ hz k)
  have hClnId215 (δ : BitAssignment n) (hz : ∀ m, δ (rW m) = 0) (i : Fin 235) :
      δ (rPreTail215 rPre i) = 0 := by
    obtain ⟨q, hq⟩ : ∃ q : Fin 1493, rPreTail215 rPre i = rTot (rScrCompact1493 q) := by
      change ∃ q : Fin 1493, rTot (preRevWireFn ⟨41 + i.val, _⟩) = rTot (rScrCompact1493 q)
      dsimp only [preRevWireFn]
      rw [_root_.dite_eq_right (by omega)]
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨m, hm⟩ := rScrCompact1493_sub_scr q
    exact (congrArg δ (hq.trans (congrArg rTot.wires hm))).trans (hz m)
  have hClnSplit215 (δ : BitAssignment n) (hz : ∀ m, δ (rW m) = 0) (i : Fin 235) :
      stPreCnotSplit decodeCoin rTot δ (rPreTail215 rPre i) = 0 := by
    have hEqW : rPreTail215 rPre i = rTot (rPreRev ⟨41 + i.val, by omega⟩) :=
      congrArg rPre (Fin.ext (by simp only [QRegister.block_apply_val]))
    exact (congrArg _ hEqW).trans ((stSplit_off δ _ (rPreRev_ne_rOut40 _)).trans
        ((congrArg δ hEqW.symm).trans (hClnId215 δ hz i)))
  have hCoreScrNotPre (k : ℕ) (hk139 : 139 ≤ k) (hk146 : k < 146) (idx : Fin 235) :
      rTot (rScrCompact1493 ⟨k, by omega⟩) ≠ rPreTail215 rPre idx := fun e ↦ by
    have he0 : rScrCompact1493 ⟨k, by omega⟩ = preRevWireFn ⟨41 + idx.val, _⟩ :=
        rTot.wires.injective e
    dsimp only [preRevWireFn] at he0
    rw [_root_.dite_eq_right (by omega)] at he0
    split_ifs at he0 <;> exact absurd (congrArg Fin.val (rScrCompact1493.wires.injective he0))
        (by (try dsimp); omega)
  have hTail4ClnGen (base : BitAssignment n → BitAssignment n)
      (hBaseScr : ∀ δ, (∀ m, δ (rW m) = 0) → ∀ k : Fin 154,
          base δ (rTot (rScrCompact1493 ⟨k.val, by omega⟩)) = 0)
      (u : Fin (41 + (143 + 3))) (hu : u ∈ sRevTail4) (δ : BitAssignment n)
          (hz : ∀ m, δ (rW m) = 0) :
      stAtRt rPre coinFn base m25Prefix sRtPrefix δ ((rTot.compose (rRevCore 143 hM5_143)) u) =
          0 := by
    have hb := sRevTail4_bounds hu
    let k0 : Fin (143 + 3) := ⟨u.val - 41, by omega⟩
    have hw : rRevCore 143 hM5_143 u = rScrCompact1493 ⟨u.val - 41, by omega⟩ :=
      (congrArg (rRevCore 143 hM5_143).wires (Fin.ext (by dsimp only [k0]; omega) : u =
          ⟨41 + k0.val, by omega⟩)).trans
        (rRevCore_scr 143 hM5_143 k0)
    change stAtRt rPre coinFn base m25Prefix sRtPrefix δ (rTot (rRevCore 143 hM5_143 u)) = 0
    rw [hw, stAtRt_apply_outside rPre coinFn base m25Prefix sRtPrefix δ (hCoreScrNotPre (u.val - 41)
        (by omega) (by omega))]
    exact hBaseScr δ hz ⟨u.val - 41, by omega⟩
  have hStepTail4 (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hz : ∀ m, δ (rW m) = 0)
      (hC : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0)
      (hBZ154 : ∀ k : Fin 154, base δ (rTot (rScrCompact1493 ⟨k.val, by omega⟩)) = 0) :
      stepCB (rTot.compose (rRevCore 143 hM5_143)) cpRevTail4.fwdBits (stAtRt rPre coinFn base
          m25Prefix sRtPrefix δ) =
      writeReg (writeReg (stepCB (rTot.compose (rRevCore 143 hM5_143))
        (cpRevCore 143 coreGates coreMask0 coreMask1).fwdBits (base δ)) rHold (hold70BitsRt
            (coinFn δ))) rDom (fun _ ↦ 0) := by
    let rRC := rTot.compose (rRevCore 143 hM5_143)
    let c := coinFn δ
    let α : BitAssignment (41 + (143 + 3)) := fun i ↦
        stAtRt rPre coinFn base m25Prefix sRtPrefix δ (rRC i)
    let α₀ : BitAssignment (41 + (143 + 3)) := fun i ↦ base δ (rRC i)
    have hrRC_lt41 (v : ℕ) (hv : v < 41) : rRC ⟨v, by omega⟩ = rPre ⟨v, by omega⟩ := by
      change rTot (revCoreWireFn 143 hM5_143 _) = rTot (preRevWireFn _)
      simp only [revCoreWireFn, preRevWireFn, _root_.ite_eq_left (Nat.ble_eq_true_of_le hv),
          _root_.dite_eq_left hv]
      exact congrArg rTot.wires (congrArg rOuter41Layout.wires (Fin.ext (Nat.mod_eq_of_lt hv)))
    have hrRC_ge41 (v : ℕ) (hlo : 41 ≤ v) (hhi : v < 41 + 146) :
        rRC ⟨v, by omega⟩ = rTot (rScrCompact1493 ⟨v - 41, by omega⟩) :=
      congrArg rTot.wires ((congrArg (rRevCore 143 hM5_143).wires
        (Fin.ext (by dsimp; omega) : (⟨v, by omega⟩ : Fin (41 + (143 + 3))) = ⟨41 + (v - 41),
            by omega⟩)).trans
        (rRevCore_scr 143 hM5_143 ⟨v - 41, by omega⟩))
    have hFwdEq : cpRevTail4.fwdBits α =
        domZeroBits (41 + (143 + 3)) ((cpRevCore 143 coreGates coreMask0 coreMask1).fwdBits α₀)
            := by
      refine fwdBits_cpRevTail4_eq_cpRevCore c α α₀ (fun u ↦ ?_) (fun u hu ↦ ?_)
        (fun k ↦ (congrArg (base δ) (hrRC_lt41 k.val k.isLt)).trans (hC k))
        (fun k ↦ (congrArg (base δ)
            (congrArg rTot.wires (rRevCore_scr 143 hM5_143 k))).trans (hBZ154 ⟨k.val, by omega⟩))
      · dsimp only [α, c]
        by_cases hu41 : u.val < 41
        · rw [hrRC_lt41 u.val hu41, stAtRt_apply_rPre rPre coinFn base m25Prefix sRtPrefix δ hC]
          dsimp only [pre256BitsRt]
          rw [_root_.ite_eq_left hu41, decide_eq_true (And.intro (by omega : u.val ≠ 67)
              (by omega : u.val ≠ 69)),
            Bool.true_and, ← env139_coinBit (coinFn δ) ⟨u.val, hu41⟩]
        · have hwPre : rPre ⟨u.val, by omega⟩ = rTot (rScrCompact1493 ⟨u.val - 41, by omega⟩) := by
            change rTot (preRevWireFn _) = _
            dsimp only [preRevWireFn]
            rw [_root_.dite_eq_right hu41, _root_.dite_eq_left (by omega : u.val < 180)]
          have hDecEq : decide (u.val - 41 ≠ 26 ∧ u.val - 41 ≠ 28) = decide (u.val ≠ 67 ∧ u.val ≠
              69) := by
            rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
            omega
          rw [hrRC_ge41 u.val (by omega) (by omega), ← hwPre,
            stAtRt_apply_rPre rPre coinFn base m25Prefix sRtPrefix δ hC]
          dsimp only [pre256BitsRt]
          rw [_root_.ite_eq_right hu41, _root_.ite_eq_left (by omega : u.val < 180),
              m25Prefix_testBit (u.val - 41) (by omega), hDecEq]
      · dsimp only [α]
        rw [show rRC u = rTot (rScrCompact1493 ⟨u.val - 41,
            by omega⟩) from hrRC_ge41 u.val (by omega) (by omega),
          stAtRt_apply_outside rPre coinFn base m25Prefix sRtPrefix δ (hCoreScrNotPre (u.val - 41)
              (by omega) (by omega)),
          hBZ154 ⟨u.val - 41, by omega⟩]
    funext x
    have hDom0RC : rDom ⟨0, by decide⟩ = rRC ⟨67, by decide⟩ :=
        (congrArg rTot.wires (rRevCore_scr 143 hM5_143 ⟨26, by decide⟩)).symm
    have hDom1RC : rDom ⟨1, by decide⟩ = rRC ⟨69, by decide⟩ :=
        (congrArg rTot.wires (rRevCore_scr 143 hM5_143 ⟨28, by decide⟩)).symm
    by_cases hxRC : x ∈ Set.range rRC.wires
    · obtain ⟨i, rfl⟩ := hxRC
      rw [stepCB, writeReg_apply_reg, congrFun hFwdEq i]
      by_cases hi67 : i.val = 67
      · rw [show i = ⟨67, by decide⟩ from Fin.ext hi67, ← hDom0RC, writeReg_apply_reg]
        rfl
      · by_cases hi69 : i.val = 69
        · rw [show i = ⟨69, by decide⟩ from Fin.ext hi69, ← hDom1RC, writeReg_apply_reg]
          rfl
        · have hnotDom : rRC i ∉ Set.range rDom.wires := fun ⟨b, hb⟩ ↦ by
            fin_cases b
            · exact hi67 (congrArg Fin.val (rRC.wires.injective (hb.symm.trans hDom0RC)))
            · exact hi69 (congrArg Fin.val (rRC.wires.injective (hb.symm.trans hDom1RC)))
          dsimp only [rRC, α₀, stepCB, domZeroBits]
          rw [_root_.ite_eq_right (by omega : ¬ (i.val = 67 ∨ i.val = 69)),
            writeReg_apply_of_not_mem _ rDom _ _ hnotDom,
            writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨j, hj⟩ ↦ disj_ne djHoldCore j i hj),
            writeReg_apply_reg]
    · have hnotDom : x ∉ Set.range rDom.wires := fun ⟨b, hb⟩ ↦ hxRC (by
        fin_cases b
        · exact ⟨⟨67, by decide⟩, hDom0RC.symm.trans hb⟩
        · exact ⟨⟨69, by decide⟩, hDom1RC.symm.trans hb⟩)
      have hjHold (j : Fin 90) : rHold j = rPre ⟨186 + j.val, by omega⟩ :=
        congrArg rPre (Fin.ext (by simp only [QRegister.block_apply_val]))
      by_cases hxH : x ∈ Set.range rHold.wires
      · obtain ⟨j, rfl⟩ := hxH
        rw [writeReg_apply_of_not_mem _ rDom _ _ hnotDom, writeReg_apply_reg, stepCB,
          writeReg_apply_of_not_mem _ rRC _ _ hxRC, hjHold j,
              stAtRt_apply_rPre rPre coinFn base m25Prefix sRtPrefix δ hC]
        rfl
      · rw [writeReg_apply_of_not_mem _ rDom _ _ hnotDom, writeReg_apply_of_not_mem _ rHold _ _ hxH,
          stepCB, writeReg_apply_of_not_mem _ rRC _ _ hxRC, stepCB,
              writeReg_apply_of_not_mem _ rRC _ _ hxRC]
        by_cases hxTail : ∃ idx : Fin 235, rPreTail215 rPre idx = x
        · obtain ⟨idx, rfl⟩ := hxTail
          have hEqPre : rPreTail215 rPre idx = rPre ⟨41 + idx.val, by omega⟩ :=
            congrArg rPre (Fin.ext (by simp only [QRegister.block_apply_val]))
          by_cases h139 : idx.val < 139
          · refine absurd ⟨⟨41 + idx.val, by omega⟩, (hrRC_ge41 (41 + idx.val) (by omega)
                (by omega)).trans ?_⟩ hxRC
            change _ = rTot (preRevWireFn ⟨41 + idx.val, _⟩)
            dsimp only [preRevWireFn]
            rw [_root_.dite_eq_right (by omega),
                _root_.dite_eq_left (by omega : 41 + idx.val < 180)]
          · by_cases h145 : idx.val < 145
            · have hScrEq : rPre ⟨41 + idx.val, by omega⟩ =
                  rTot (rScrCompact1493 ⟨148 + (idx.val - 139), by omega⟩) := by
                change rTot (preRevWireFn _) = _
                dsimp only [preRevWireFn]
                rw [_root_.dite_eq_right (by omega),
                    _root_.dite_eq_right (by omega : ¬ 41 + idx.val < 180)]
                exact congrArg rTot.wires (congrArg rScrCompact1493 (Fin.ext (by dsimp; omega)))
              rw [hEqPre, stAtRt_apply_rPre rPre coinFn base m25Prefix sRtPrefix δ hC, hScrEq,
                hBZ154 ⟨148 + (idx.val - 139), by omega⟩]
              dsimp only [pre256BitsRt]
              rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega),
                  _root_.ite_eq_left (by omega)]
            · exact absurd ⟨⟨idx.val - 145, by omega⟩,
                (hjHold ⟨idx.val - 145,
                    by omega⟩).trans ((congrArg rPre (Fin.ext (by dsimp; omega))).trans
                         hEqPre.symm)⟩ hxH
        · exact stAtRt_apply_outside rPre coinFn base m25Prefix sRtPrefix δ fun idx e ↦
              hxTail ⟨idx, e.symm⟩
  have hBZ154Id (δ : BitAssignment n) (hz : ∀ m, δ (rW m) = 0) (k : Fin 154) :
      δ (rTot (rScrCompact1493 ⟨k.val, by omega⟩)) = 0 := by
    obtain ⟨m, hm⟩ := rScrCompact1493_sub_scr ⟨k.val, by omega⟩
    exact (congrArg δ (congrArg rTot.wires hm)).trans (hz m)
  have hBZ154Split (δ : BitAssignment n) (hz : ∀ m, δ (rW m) = 0) (k : Fin 154) :
      stPreCnotSplit decodeCoin rTot δ (rTot (rScrCompact1493 ⟨k.val, by omega⟩)) = 0 :=
    (stSplit_off δ _ (rScr_ne_rOut40 _)).trans (hBZ154Id δ hz k)
  have hCoreSplitEq (δ : BitAssignment n) (hz : ∀ m, δ (rW m) = 0) :
      stepCB (rTot.compose (rRevCore 143 hM5_143)) cpRevTail4.fwdBits
        (stAtRt rPre coinFn (stPreCnotSplit decodeCoin rTot) m25Prefix sRtPrefix δ) =
      writeReg (stTier1Hold δ) (rTot.compose rOutMid32) (fun j ↦ if gMid δ j then 1 else 0) := by
    rw [hStepTail4 (stPreCnotSplit decodeCoin rTot) δ hz (hCoinSplit δ hz) (hBZ154Split δ hz)]
    have hCoreComm : stepCB (rTot.compose (rRevCore 143 hM5_143))
        (cpRevCore 143 coreGates coreMask0 coreMask1).fwdBits (stPreCnotSplit decodeCoin rTot δ) =
        writeReg (stTier1Done decodeCoin 143 hM5_143 coreGates coreMask0 coreMask1 rTot δ)
          (rTot.compose rOutMid32) (fun j ↦ if gMid δ j then 1 else 0) := by
      simp only [stPreCnotSplit, stTailOnly, stTier1Done, stCoreClean, gMid,
        stepCB_writeReg_comm _ _ djCoreMid, stepCB_writeReg_comm _ _ djCoreTail]
    rw [hCoreComm]
    dsimp only [stTier1Hold]
    rw [writeReg_comm_of_disj (rTot.compose rOutMid32) rHold (disj_of_ne fun j i e ↦
        disj_ne djHoldMid i j e.symm)]
    exact writeReg_comm_of_disj (rTot.compose rOutMid32) rDom
      (disj_of_ne fun j i e ↦ disj_ne djDomMid i j e.symm) _ _ _
  have hCoreIdEq (δ : BitAssignment n) (hz : ∀ m, δ (rW m) = 0) :
      stepCB (rTot.compose (rRevCore 143 hM5_143)) cpRevTail4.fwdBits
        (stAtRt rPre coinFn (fun η ↦ η) m25Prefix sRtPrefix δ) = stCoreHold δ :=
    hStepTail4 (fun η ↦ η) δ hz (hCoinId δ hz) (hBZ154Id δ hz)
  obtain ⟨sRevInner, tRevInner, fRevInner, _⟩ := subspaceStep_wrapOnReg_vprog2 v rW
    (rTot.compose (rRevCore 143 hM5_143)) sRevTail4 cpRevTail4 4 cpRevTail4_spec.2 cpRevTail4_spec.1
    (stAtRt rPre coinFn (stPreCnotSplit decodeCoin rTot) m25Prefix sRtPrefix)
    (stAtRt rPre coinFn (fun η ↦ η) m25Prefix sRtPrefix) (fun _ ↦ 0) (fun _ ↦ 0)
        (.seq dTmpTier1 dTier2)
    (hTail4ClnGen (stPreCnotSplit decodeCoin rTot) hBZ154Split) (hTail4ClnGen (fun η ↦ η) hBZ154Id)
    (subspaceStep_congr_in
      (mkKetOpW_congr rW (ph₁ := fun _ ↦ 0) (ph₂ := fun _ ↦ 0) (fun δ hz ↦ hCoreSplitEq δ hz)
          (fun _ _ ↦ rfl))
      (subspaceStep_congr_out (subspaceStep_seq_asym sTmpTier1 sTier2)
        (mkKetOpW_congr rW (ph₁ := fun _ ↦ 0) (ph₂ := fun _ ↦ 0) (fun δ hz ↦ (hCoreIdEq δ hz).symm)
            (fun _ _ ↦ rfl))))
  obtain ⟨sPref, tPref, fPref, _⟩ := step_wrapPrefixRt_clean v rW rPre coinFn
    (stPreCnotSplit decodeCoin rTot) (fun η ↦ η) (fun _ ↦ 0) (fun _ ↦ 0)
    hCoinSplit hCoinId hClnSplit215 hClnId215 (dRevInner v rTot) sRevInner
  obtain ⟨cP_t, cP_f⟩ := count_cPreCnot40 (rTot.compose rOut40Layout)
  obtain ⟨cW1_t, cW1_f⟩ :=
      count_xUnloadChunkCzPairsXSeqDyn v (outWireOfReg pos32 (rTot.compose rOutMid32)) 0
    (fun s ↦ midPx ⟨s % 32, mod32_lt s⟩)
    (fun s ↦ wirePairsOfReg (rTot.compose (rMidPred 143 hM5_143)) (midPairs ⟨s % 32, mod32_lt s⟩))
        (.circuit .identity) 32
  obtain ⟨cW2_t, cW2_f⟩ :=
      count_xUnloadChunkCzPairsXSeqDyn v (outWireOfReg pos5 (rTot.compose rOutTail5)) 0
    (fun s ↦ tailPx ⟨s % 5, mod5_lt s⟩)
    (fun s ↦ wirePairsOfReg (rTot.compose (rTailPred 143 hM5_143)) (tailPairs ⟨s % 5, mod5_lt s⟩))
        (.circuit .identity) 5
  obtain ⟨cTmp_t, cTmp_f⟩ :=
      counts_wrapDynOnReg v (rTot.compose (rRevTmp 143 hM5_143)) cpRevTmp dTier1
  have hCntT : (pRevRt526 v rTot).count .T = 526 := by
    dsimp only [pRevRt526, DynamicCircuit.count]
    rw [cP_t, tPref]
    change 0 +
        (502 +
        (wrapDynOnReg v (rTot.compose (rRevCore 143 hM5_143)) cpRevTail4 (.seq dTmpTier1
        dTier2)).count .T) = 526
    rw [tRevInner]
    dsimp only [DynamicCircuit.count, Circuit.count] at cW1_t cW2_t ⊢
    rw [cTmp_t, cpRevTmp_spec.1, cW1_t, cW2_t]
  have hCntF : (pRevRt526 v rTot).count .TOFF = 0 := by
    dsimp only [pRevRt526, DynamicCircuit.count]
    rw [cP_f, fPref]
    change 0 +
        (wrapDynOnReg v (rTot.compose (rRevCore 143 hM5_143)) cpRevTail4 (.seq dTmpTier1
        dTier2)).count .TOFF = 0
    rw [fRevInner]
    dsimp only [DynamicCircuit.count, Circuit.count] at cW1_f cW2_f ⊢
    rw [cTmp_f, cW1_f, cW2_f]
  exact ⟨subspaceStep_seq_asym sPre (subspaceStep_congr_out sPref (mkKetOpW_id_eq_proj rW)), hCntT,
      hCntF⟩

theorem subspaceStep_pRevRt526_ext_c70 {Var : Type} [Fintype Var] [DecidableEq Var] {kExt n : ℕ}
    [NeZero (2 ^ n)] (hk : kExt ≤ 72) (v : Var) (rTot : QRegister dLayout n) {X : Operator (2 ^ n)}
    (hDyn : DynWires (fun u ↦ ∀ j : Fin kExt, u ≠ (rTot.compose (rCoinExt kExt hk)) j)
    (pRevRt526 v rTot)) (hX : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 * X = X) :
    SubspaceStep ((rTot.embedUnitary (uStage1Clean_c70 decodeTier1W11Opt1424Coin)).1 *
    X) X (pRevRt526 v rTot) := by
  obtain ⟨sc, _, _⟩ := step_and_counts_pRevRt526_rScrLayout v rTot;
  have e0 : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 *
      (rTot.compose (rCoinExt kExt hk)).basisOutcomeProjector 0 =
      (rTot.compose rScrLayout).basisOutcomeProjector 0 := hP0_rScrExt_c70 hk rTot
  have eIn : ((rTot.embedUnitary (uStage1Clean_c70 decodeTier1W11Opt1424Coin)).1 *
      (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0) *
      (rTot.compose (rCoinExt kExt hk)).basisOutcomeProjector 0 =
      (rTot.embedUnitary oRef209.uLocal).1 * (rTot.compose rScrLayout).basisOutcomeProjector 0 := by
    rw [Matrix.mul_assoc, e0, wStage1Clean_mul_rScrLayout_c70 oRef209 rTot]
  have s0 := subspaceStep_congr_in eIn (subspaceStep_congr_out sc e0.symm)
  have hCommWP : ∀ V : Unitary (2 ^ kExt),
      ((rTot.embedUnitary (uStage1Clean_c70 decodeTier1W11Opt1424Coin)).1 *
        (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0) *
        ((rTot.compose (rCoinExt kExt hk)).embedUnitary V).1 =
      ((rTot.compose (rCoinExt kExt hk)).embedUnitary V).1 *
        ((rTot.embedUnitary (uStage1Clean_c70 decodeTier1W11Opt1424Coin)).1 *
          (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0) := fun V ↦ by
    rw [Matrix.mul_assoc, pScrExt_comm_rCoinExt_c70 hk rTot V, ← Matrix.mul_assoc,
        wStage1Clean_comm_rCoinExt_c70 decodeTier1W11Opt1424Coin hk rTot V, Matrix.mul_assoc]
  have sExt :=
      subspaceStep_drop_disj_c70 (rTot.compose (rCoinExt kExt hk)) hDyn hCommWP
      (pScrExt_comm_rCoinExt_c70 hk rTot) s0; simpa only [Matrix.mul_assoc,
      hX] using subspaceStep_mul_right X sExt
/-! ### Chunk-8 (`6`-Gather-Wire `1,260 T`, `+0 T`) Engine (`W = 300` & `DomZ W = 298`) -/

theorem domKeepMask_bit68_70 :
    domKeepMask.testBit 68 = false ∧ domKeepMask.testBit 70 = false := by decide

theorem mask_testBit_68_70_of_dom (mask : ℕ) (hDom : (domKeepMask &&& mask == mask) = true) :
    mask.testBit 68 = false ∧ mask.testBit 70 = false := by
  have heq : domKeepMask &&& mask = mask := beq_iff_eq.mp hDom; refine ⟨?_, ?_⟩
  · rw [← heq, Nat.testBit_and, domKeepMask_bit68_70.1, Bool.false_and]
  · rw [← heq, Nat.testBit_and, domKeepMask_bit68_70.2, Bool.false_and]

theorem env151_maskParity_domZ {n : ℕ} (rSrc : QRegister 192 n) (c : Fin (2 ^ 41))
    (γ : BitAssignment n) (hγ : ∀ u : Fin 192, u.val ≠ 67 → u.val ≠ 69 → γ (rSrc u) =
    if (e151Dom c).testBit (1 + u.val) then 1 else 0) (mask : ℕ)
    (hDom : (domKeepMask &&& mask == mask) = true) : maskParity mask (fun u : Fin 192 ↦
    γ (rSrc u)) 192 le_rfl = if bOf c mask then 1 else 0 := by
  let envFn : BitAssignment 192 := fun u ↦ if (e151Dom c).testBit (1 + u.val) then 1 else 0
  have hSup : ∀ u : Fin 192, u.val < 192 → mask.testBit (1 + u.val) = true → γ (rSrc u) =
      envFn u := by
    intro u _ htb; have h6870 := mask_testBit_68_70_of_dom mask hDom
    have hn67 : u.val ≠ 67 := fun e ↦ by rw [e, h6870.1] at htb; cases htb
    have hn69 : u.val ≠ 69 := fun e ↦ by rw [e, h6870.2] at htb; cases htb
    exact hγ u hn67 hn69
  rw [maskParity_congr_support mask _ envFn 192 le_rfl hSup,
      maskParity_eq_oddBits mask (e151Dom c) envFn
        (e151Dom_bit0 c) (fun _ ↦ rfl) 192 le_rfl]
  have hMaskEq : e151Dom c &&& mask = e151 c &&& mask := by
    dsimp only [e151Dom]; rw [Nat.and_assoc, beq_iff_eq.mp hDom]
  change (if oddBits (e151Dom c &&& mask) 193 then (1 : ZMod 2) else 0) = _
  rw [hMaskEq]; rfl

theorem wPairR_ne {n R : ℕ} {lW hW : Fin R → Wire n} {x : Wire n}
    (hl : ∀ b, lW b ≠ x) (hh : ∀ b, hW b ≠ x) (b : Fin R) (p : Fin 2) : wPairR lW hW b p ≠ x := by
  dsimp only [wPairR]
  split_ifs
  · exact hl b
  · exact hh b

theorem mkRouterInj1 {n R : ℕ} (u : Wire n) (lW hW : Fin R → Wire n) (rD wD qE : Wire n)
    (hlInj : Function.Injective lW) (hhInj : Function.Injective hW) (hlh : ∀ a b, lW a ≠ hW b)
    (huL : ∀ b, u ≠ lW b) (huH : ∀ b, u ≠ hW b)
    (hlD : ∀ b, lW b ≠ rD ∧ lW b ≠ wD ∧ lW b ≠ qE) (hhD : ∀ b, hW b ≠ rD ∧ hW b ≠ wD ∧ hW b ≠ qE)
    (huD : u ≠ rD ∧ u ≠ wD ∧ u ≠ qE) (hD : rD ≠ wD ∧ rD ≠ qE ∧ wD ≠ qE) :
    WOptInj R 1 (fun _ : Fin 1 ↦ u) (wPairR lW hW) rD wD qE where
  w_inj b1 p1 b2 p2 e := by
    dsimp only [wPairR] at e
    have hp1lt := p1.isLt
    have hp2lt := p2.isLt
    by_cases hp1 : p1.val = 0
    · by_cases hp2 : p2.val = 0
      · rw [_root_.ite_eq_left hp1, _root_.ite_eq_left hp2] at e
        exact ⟨hlInj e, Fin.ext (by omega)⟩
      · rw [_root_.ite_eq_left hp1, _root_.ite_eq_right hp2] at e
        exact absurd e (hlh b1 b2)
    · by_cases hp2 : p2.val = 0
      · rw [_root_.ite_eq_right hp1, _root_.ite_eq_left hp2] at e
        exact absurd e.symm (hlh b2 b1)
      · rw [_root_.ite_eq_right hp1, _root_.ite_eq_right hp2] at e
        exact ⟨hhInj e, Fin.ext (by omega)⟩
  uLo_ne_w _ b p := (wPairR_ne (fun k ↦ (huL k).symm) (fun k ↦ (huH k).symm) b p).symm
  uLo_ne_rDum _ := huD.1
  uLo_ne_wDum _ := huD.2.1
  uLo_ne_qEnc _ := huD.2.2
  w_ne_rDum := wPairR_ne (fun b ↦ (hlD b).1) (fun b ↦ (hhD b).1)
  w_ne_wDum := wPairR_ne (fun b ↦ (hlD b).2.1) (fun b ↦ (hhD b).2.1)
  w_ne_qEnc := wPairR_ne (fun b ↦ (hlD b).2.2) (fun b ↦ (hhD b).2.2)
  rDum_ne_wDum := hD.1
  rDum_ne_qEnc := hD.2.1
  wDum_ne_qEnc := hD.2.2

theorem gat7_idx_facts :
    Function.Injective (fun b : Fin 2 ↦ (⟨3 + b.val, by omega⟩ : Fin 7)) ∧
    Function.Injective (fun b : Fin 2 ↦ (⟨5 + b.val, by omega⟩ : Fin 7)) ∧
    (∀ a b : Fin 2, (⟨3 + a.val, by omega⟩ : Fin 7) ≠ ⟨5 + b.val, by omega⟩) ∧
    (∀ b : Fin 2, (⟨3 + b.val, by omega⟩ : Fin 7) ≠ ⟨0, by decide⟩ ∧
      (⟨3 + b.val, by omega⟩ : Fin 7) ≠ ⟨1, by decide⟩ ∧
      (⟨3 + b.val, by omega⟩ : Fin 7) ≠ ⟨2, by decide⟩) ∧
    (∀ b : Fin 2, (⟨5 + b.val, by omega⟩ : Fin 7) ≠ ⟨0, by decide⟩ ∧
      (⟨5 + b.val, by omega⟩ : Fin 7) ≠ ⟨1, by decide⟩ ∧
      (⟨5 + b.val, by omega⟩ : Fin 7) ≠ ⟨2, by decide⟩) ∧
    ((⟨0, by decide⟩ : Fin 7) ≠ ⟨1, by decide⟩ ∧
     (⟨0, by decide⟩ : Fin 7) ≠ ⟨2, by decide⟩ ∧
     (⟨1, by decide⟩ : Fin 7) ≠ ⟨2, by decide⟩) := by decide

theorem gat7RouterInj {n : ℕ} (rGat : QRegister 7 n) (u : Wire n)
    (hGatU : ∀ i : Fin 7, rGat i ≠ u) :
    WOptInj 2 1 (fun _ : Fin 1 ↦ u)
      (wPairR (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩)
          (fun b : Fin 2 ↦ rGat ⟨5 + b.val, by omega⟩))
      (rGat ⟨0, by decide⟩) (rGat ⟨1, by decide⟩) (rGat ⟨2, by decide⟩) :=
  have ⟨hl, hh, hlh, hlD, hhD, hD⟩ := gat7_idx_facts
  have neG : ∀ {a b : Fin 7}, a ≠ b → rGat a ≠ rGat b := rGat.wires.injective.ne
  mkRouterInj1 u _ _ _ _ _ (rGat.wires.injective.comp hl) (rGat.wires.injective.comp hh)
    (fun a b ↦ neG (hlh a b)) (fun _ ↦ (hGatU _).symm) (fun _ ↦ (hGatU _).symm)
    (fun b ↦ ⟨neG (hlD b).1, neG (hlD b).2.1, neG (hlD b).2.2⟩)
    (fun b ↦ ⟨neG (hhD b).1, neG (hhD b).2.1, neG (hhD b).2.2⟩)
    ⟨(hGatU _).symm, (hGatU _).symm, (hGatU _).symm⟩ ⟨neG hD.1, neG hD.2.1, neG hD.2.2⟩

def cLoadGatL2 {n : ℕ} (rSrc : QRegister 192 n) (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i) (mLs : List ℕ) : Circuit n :=
  cXorMaskSrc192 rSrc (rGat ⟨3, by decide⟩) (fun u ↦ hSrcGat u _) (mLs.getD 0 0) 192 le_rfl ;;ᶜ
    cXorMaskSrc192 rSrc (rGat ⟨4, by decide⟩) (fun u ↦ hSrcGat u _) (mLs.getD 1 0) 192 le_rfl

theorem count_cLoadGatL2 {n : ℕ} (rSrc : QRegister 192 n) (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i) (mLs : List ℕ) :
    (cLoadGatL2 rSrc rGat hSrcGat mLs).count .T = 0 ∧
        (cLoadGatL2 rSrc rGat hSrcGat mLs).count .TOFF = 0 := by
  obtain ⟨t0, f0⟩ :=
      count_cXorMaskSrc192 rSrc (rGat ⟨3, by decide⟩) (fun u ↦ hSrcGat u _)
      (mLs.getD 0 0) 192 le_rfl
  obtain ⟨t1, f1⟩ :=
      count_cXorMaskSrc192 rSrc (rGat ⟨4, by decide⟩) (fun u ↦ hSrcGat u _)
      (mLs.getD 1 0) 192 le_rfl
  dsimp only [cLoadGatL2]
  exact ⟨by rw [Circuit.count_seq, t0, t1], by rw [Circuit.count_seq, f0, f1]⟩

theorem cw_cLoadGatL2 {n : ℕ} {S : Wire n → Prop} (rSrc : QRegister 192 n) (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i)
    (hSrc : ∀ u : Fin 192, S (rSrc u)) (hGat : ∀ i : Fin 7, S (rGat i)) (mLs : List ℕ) :
    CircWires S (cLoadGatL2 rSrc rGat hSrcGat mLs) :=
  ⟨cw_cXorMaskSrc192 rSrc _ _ hSrc (hGat _) _ 192 le_rfl,
      cw_cXorMaskSrc192 rSrc _ _ hSrc (hGat _) _ 192 le_rfl⟩

theorem ket_cLoadGatL2 {n : ℕ} [NeZero (2 ^ n)] (rSrc : QRegister 192 n) (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i) (mLs : List ℕ) (γ : BitAssignment n) :
    (cLoadGatL2 rSrc rGat hSrcGat mLs).eval.1.mulVec (ket γ) =
      ket (fun x ↦ match findBranch (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩) x with
        | some b => γ x + maskParity (mLs.getD b.val 0) (fun u : Fin 192 ↦ γ (rSrc u)) 192 le_rfl
        | none => γ x) := by
  have hlInj : Function.Injective (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩) :=
    fun _ _ h ↦ gat7_idx_facts.1 (rGat.wires.injective h)
  have h43 : rGat ⟨4, by decide⟩ ≠ rGat ⟨3, by decide⟩ := rGat.wires.injective.ne (by decide)
  dsimp only [cLoadGatL2]
  rw [eval_seq_mulVec, ket_cXorMaskSrc192, ket_cXorMaskSrc192,
    show (fun u : Fin 192 ↦ Function.update γ (rGat ⟨3, by decide⟩) _ (rSrc u)) = fun u ↦
        γ (rSrc u) from
      funext fun u ↦ Function.update_of_ne (hSrcGat u _) _ _,
    Function.update_of_ne h43]
  refine congrArg ket (funext fun x ↦ ?_)
  cases hfb : findBranch (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩) x with
  | none =>
      have hne (b : Fin 2) : x ≠ rGat ⟨3 + b.val, by omega⟩ := fun e ↦ by
        rw [e, findBranch_self hlInj b] at hfb
        cases hfb
      exact (Function.update_of_ne (hne 1) _ _).trans (Function.update_of_ne (hne 0) _ _)
  | some b =>
      obtain rfl := findBranch_spec hfb
      fin_cases b
      · exact (Function.update_of_ne h43.symm _ _).trans (Function.update_self _ _ _)
      · exact Function.update_self _ _ _

theorem cLoadGatL2_sq {n : ℕ} [NeZero (2 ^ n)] (rSrc : QRegister 192 n) (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i) (mLs : List ℕ) :
    (cLoadGatL2 rSrc rGat hSrcGat mLs).eval.1 * (cLoadGatL2 rSrc rGat hSrcGat mLs).eval.1 = 1 := by
  refine matrix_ext_ket fun γ ↦ ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ket_cLoadGatL2, ket_cLoadGatL2]
  have hSrc : (fun u : Fin 192 ↦ match findBranch (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩)
      (rSrc u) with
      | some b => γ (rSrc u) + maskParity (mLs.getD b.val 0) (fun v ↦ γ (rSrc v)) 192 le_rfl
      | none => γ (rSrc u)) = fun u ↦ γ (rSrc u) :=
    funext fun u ↦ by rw [findBranch_none (fun _ ↦ hSrcGat u _)]
  apply congrArg ket
  funext x
  cases hfb : findBranch (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩) x with
  | none => simp only []
  | some b => simp only [hSrc, add_assoc, zmod2_add_self, add_zero]

def cPhaseGatH2 {n : ℕ} (rSrc : QRegister 192 n) (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i) (mYs : List ℕ) : Circuit n :=
  cPhaseMaskSrc192 rSrc (rGat ⟨5, by decide⟩) (fun u ↦ hSrcGat u _) (mYs.getD 0 0) ;;ᶜ
    cPhaseMaskSrc192 rSrc (rGat ⟨6, by decide⟩) (fun u ↦ hSrcGat u _) (mYs.getD 1 0)

theorem count_cPhaseGatH2 {n : ℕ} (rSrc : QRegister 192 n) (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i) (mYs : List ℕ) :
    (cPhaseGatH2 rSrc rGat hSrcGat mYs).count .T = 0 ∧
        (cPhaseGatH2 rSrc rGat hSrcGat mYs).count .TOFF = 0 := by
  obtain ⟨t0, f0⟩ :=
      count_cPhaseMaskSrc192 rSrc (rGat ⟨5, by decide⟩) (fun u ↦ hSrcGat u _) (mYs.getD 0 0)
  obtain ⟨t1, f1⟩ :=
      count_cPhaseMaskSrc192 rSrc (rGat ⟨6, by decide⟩) (fun u ↦ hSrcGat u _) (mYs.getD 1 0)
  dsimp only [cPhaseGatH2]
  exact ⟨by rw [Circuit.count_seq, t0, t1], by rw [Circuit.count_seq, f0, f1]⟩

theorem cw_cPhaseGatH2 {n : ℕ} {S : Wire n → Prop} (rSrc : QRegister 192 n) (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i)
    (hSrc : ∀ u : Fin 192, S (rSrc u)) (hGat : ∀ i : Fin 7, S (rGat i)) (mYs : List ℕ) :
    CircWires S (cPhaseGatH2 rSrc rGat hSrcGat mYs) :=
  ⟨cw_cPhaseMaskSrc192 rSrc _ _ hSrc (hGat _) _, cw_cPhaseMaskSrc192 rSrc _ _ hSrc (hGat _) _⟩

theorem ket_cPhaseGatH2_gather {n : ℕ} [NeZero (2 ^ n)] (rSrc : QRegister 192 n)
    (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i) (c : Fin (2 ^ 41)) (mLs mYs : List ℕ)
    (uVal : ZMod 2) (γ : BitAssignment n)
    (hSrc : ∀ u : Fin 192, u.val ≠ 67 → u.val ≠ 69 → γ (rSrc u) = if (e151Dom c).testBit (1 +
        u.val) then 1 else 0)
    (hH : ∀ b : Fin 2, γ (rGat ⟨5 + b.val, by omega⟩) =
        (if bOf c (mLs.getD b.val 0) then 1 else 0) * uVal)
    (hmYsDom : ∀ b : Fin 2, (domKeepMask &&& mYs.getD b.val 0 == mYs.getD b.val 0) = true) :
    (cPhaseGatH2 rSrc rGat hSrcGat mYs).eval.1.mulVec (ket γ) =
      QubitizationWalkSem.bitSign (uVal *
          if gatherParityAux c mLs mYs 2 then 1 else 0) • ket γ := by
  have hH0 : γ (rGat ⟨5, by decide⟩) = (if bOf c (mLs.getD 0 0) then 1 else 0) * uVal := hH 0
  have hH1 : γ (rGat ⟨6, by decide⟩) = (if bOf c (mLs.getD 1 0) then 1 else 0) * uVal := hH 1
  dsimp only [cPhaseGatH2]
  rw [eval_seq_mulVec, ket_cPhaseMaskSrc192, Matrix.mulVec_smul, ket_cPhaseMaskSrc192, smul_smul,
      ← bitSign_xmu_eq, ← bitSign_xmu_eq, ← XMeasUnld.bitSign_add, bitSign_xmu_eq,
      env151_maskParity_domZ rSrc c γ hSrc (mYs.getD 0 0) (hmYsDom 0),
      env151_maskParity_domZ rSrc c γ hSrc (mYs.getD 1 0) (hmYsDom 1),
      hH0, hH1]
  refine congrArg (fun z ↦ QubitizationWalkSem.bitSign z • ket γ) ?_
  have hp1 : gatherParityAux c mLs mYs 1 = xor false (bOf c (mLs.getD 0 0) && bOf c (mYs.getD 0 0))
      := rfl
  have hp2 : gatherParityAux c mLs mYs 2 = xor (gatherParityAux c mLs mYs 1)
      (bOf c (mLs.getD 1 0) && bOf c (mYs.getD 1 0)) := rfl
  have h0 := zmod2_gather_step_eq false (bOf c (mLs.getD 0 0)) (bOf c (mYs.getD 0 0)) uVal
  have h1 :=
      zmod2_gather_step_eq (gatherParityAux c mLs mYs 1) (bOf c (mLs.getD 1 0))
      (bOf c (mYs.getD 1 0)) uVal
  rw [_root_.ite_eq_right Bool.false_ne_true, mul_zero, zero_add, ← hp1] at h0
  rw [← hp2] at h1
  rw [h0, h1]

def pHkInnerChunk8 {Var : Type} {n : ℕ} (v : Var) (rSrc : QRegister 192 n) (rO : QRegister 40 n)
    (rGat : QRegister 7 n) (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i)
    (hGatO : ∀ (i : Fin 7) (q : Fin 40), rGat i ≠ rO q) (s : Fin 2) : DynamicCircuit Var n :=
  let j : Fin 32 := ⟨30 + s.val, by omega⟩
  let qIdx : Fin 40 := ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
  let cL := cLoadGatL2 rSrc rGat hSrcGat hkMLs
  .seq (.circuit cL)
    (.seq (pSplitRBracket v (rO qIdx) (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩)
             (fun b : Fin 2 ↦ rGat ⟨5 + b.val, by omega⟩) (rGat ⟨0, by decide⟩)
                 (rGat ⟨1, by decide⟩)
             (rGat ⟨2, by decide⟩) (gat7RouterInj rGat (rO qIdx) (fun i ↦ hGatO i qIdx))
             (.circuit (cPhaseGatH2 rSrc rGat hSrcGat (hkMYs s))))
      (.circuit cL))

def pHkStepChunk8 {Var : Type} {n : ℕ} (v : Var) (rSrc : QRegister 192 n) (rO : QRegister 40 n)
    (rGat : QRegister 7 n) (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i)
    (hGatO : ∀ (i : Fin 7) (q : Fin 40), rGat i ≠ rO q) (s : Fin 2) : DynamicCircuit Var n :=
  let j : Fin 32 := ⟨30 + s.val, by omega⟩
  let uWire := rO ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
  .seq (.circuit (.H uWire)) (.seq (pHkInnerChunk8 v rSrc rO rGat hSrcGat hGatO s)
      (.circuit (.H uWire)))

theorem counts_pHkStepChunk8 {Var : Type} {n : ℕ} (v : Var) (rSrc : QRegister 192 n)
    (rO : QRegister 40 n) (rGat : QRegister 7 n) (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠
    rGat i) (hGatO : ∀ (i : Fin 7) (q : Fin 40), rGat i ≠ rO q)
    (s : Fin 2) : (pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO s).count .T = 6 ∧
    (pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO s).count .TOFF = 0 := by
  let j : Fin 32 := ⟨30 + s.val, by omega⟩
  let qIdx : Fin 40 := ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
  obtain ⟨tL, fL⟩ := count_cLoadGatL2 rSrc rGat hSrcGat hkMLs
  obtain ⟨tP, fP⟩ := count_cPhaseGatH2 rSrc rGat hSrcGat (hkMYs s)
  obtain ⟨tB, fB⟩ := counts_pSplitRBracket v (rO qIdx)
    (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩) (fun b : Fin 2 ↦ rGat ⟨5 + b.val, by omega⟩)
    (rGat ⟨0, by decide⟩) (rGat ⟨1, by decide⟩) (rGat ⟨2, by decide⟩)
    (gat7RouterInj rGat (rO qIdx) (fun i ↦ hGatO i qIdx))
    (.circuit (cPhaseGatH2 rSrc rGat hSrcGat (hkMYs s)))
  have hHT : (Circuit.H (rO qIdx)).count .T = 0 := rfl
  have hHF : (Circuit.H (rO qIdx)).count .TOFF = 0 := rfl
  dsimp only [pHkStepChunk8, pHkInnerChunk8, DynamicCircuit.count] at tB fB ⊢
  rw [hHT, hHF, tL, fL, tB, fB, tP, fP]
  exact ⟨by omega, by omega⟩

theorem dw_pHkStepChunk8 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (rSrc : QRegister 192 n)
    (rO : QRegister 40 n) (rGat : QRegister 7 n) (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠
    rGat i) (hGatO : ∀ (i : Fin 7) (q : Fin 40), rGat i ≠ rO q) (hSrc : ∀ u : Fin 192, S (rSrc u))
    (hO : ∀ q : Fin 40, S (rO q)) (hGat : ∀ i : Fin 7, S (rGat i))
    (s : Fin 2) : DynWires S (pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO s) := by
  let j : Fin 32 := ⟨30 + s.val, by omega⟩
  let qIdx : Fin 40 := ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
  have dwL := cw_cLoadGatL2 rSrc rGat hSrcGat hSrc hGat hkMLs
  have dwP := cw_cPhaseGatH2 rSrc rGat hSrcGat hSrc hGat (hkMYs s)
  have dwB := dynWires_pSplitRBracket v (rO qIdx)
    (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩) (fun b : Fin 2 ↦ rGat ⟨5 + b.val, by omega⟩)
    (rGat ⟨0, by decide⟩) (rGat ⟨1, by decide⟩) (rGat ⟨2, by decide⟩)
    (gat7RouterInj rGat (rO qIdx) (fun i ↦ hGatO i qIdx))
    (.circuit (cPhaseGatH2 rSrc rGat hSrcGat (hkMYs s)))
    (hO qIdx) (fun _ ↦ hGat _) (fun _ ↦ hGat _) (hGat _) (hGat _) (hGat _) dwP
  exact ⟨cw_1 (hO qIdx), ⟨⟨dwL, ⟨dwB, dwL⟩⟩, cw_1 (hO qIdx)⟩⟩

theorem step_pHkStepChunk8 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n)
    (rSrc : QRegister 192 n) (rO : QRegister 40 n) (rGat : QRegister 7 n)
    (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i)
    (hGatO : ∀ (i : Fin 7) (q : Fin 40), rGat i ≠ rO q)
    (coinFn : BitAssignment n → Fin (2 ^ 41)) (st₀ : BitAssignment n → BitAssignment n) (s : Fin 2)
    (huWork : ∀ q : Fin W, rO ⟨mid32OutIdx ⟨30 + s.val, by omega⟩, mid32OutIdx_lt40 ⟨30 + s.val,
        by omega⟩⟩ ≠ rWork q)
    (huId : ∀ δ, (∀ q, δ (rWork q) = 0) →
      st₀ δ (rO ⟨mid32OutIdx ⟨30 + s.val, by omega⟩, mid32OutIdx_lt40 ⟨30 + s.val, by omega⟩⟩) =
        δ (rO ⟨mid32OutIdx ⟨30 + s.val, by omega⟩, mid32OutIdx_lt40 ⟨30 + s.val, by omega⟩⟩))
    (hstUpd : ∀ δ b, (∀ q, δ (rWork q) = 0) →
      st₀ (Function.update δ (rO ⟨mid32OutIdx ⟨30 + s.val, by omega⟩, mid32OutIdx_lt40 ⟨30 + s.val,
          by omega⟩⟩) b) =
        Function.update (st₀ δ)
            (rO ⟨mid32OutIdx ⟨30 + s.val, by omega⟩, mid32OutIdx_lt40 ⟨30 + s.val, by omega⟩⟩) b)
    (hcUpd : ∀ δ b, (∀ q, δ (rWork q) = 0) →
      coinFn (Function.update δ (rO ⟨mid32OutIdx ⟨30 + s.val, by omega⟩, mid32OutIdx_lt40 ⟨30 +
          s.val, by omega⟩⟩) b) = coinFn δ)
    (hSrcEnv : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin 192, u.val ≠ 67 → u.val ≠ 69 →
      st₀ δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0)
    (hGatZero : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ i : Fin 7, st₀ δ (rGat i) = 0) :
    let j : Fin 32 := ⟨30 + s.val, by omega⟩
    let qIdx : Fin 40 := ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
    let uWire := rO qIdx
    let gBit : BitAssignment n → ZMod 2 := fun δ ↦ if hkParityBool (coinFn δ) s then 1 else 0
    SubspaceStep (mkKetOpW rWork st₀ (fun _ ↦ 0))
      (mkKetOpW rWork (fun δ ↦ Function.update (st₀ δ) uWire (st₀ δ uWire + gBit δ)) (fun _ ↦ 0))
      (pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO s) := by
  intro j qIdx uWire gBit
  let lW (b : Fin 2) : Wire n := rGat ⟨3 + b.val, by omega⟩
  let hW (b : Fin 2) : Wire n := rGat ⟨5 + b.val, by omega⟩
  let hInj := gat7RouterInj rGat uWire fun i ↦ hGatO i qIdx
  obtain ⟨hlInj, hhInj, hlhNe⟩ := wPairR_inj_props hInj.w_inj
  let cL := cLoadGatL2 rSrc rGat hSrcGat hkMLs
  let cP := cPhaseGatH2 rSrc rGat hSrcGat (hkMYs s)
  let stLoaded (δ : BitAssignment n) (x : Wire n) : ZMod 2 :=
    match findBranch lW x with
    | some b => if bOf (coinFn δ) (hkMLs.getD b.val 0) then 1 else 0
    | none => st₀ δ x
  let phPost (δ : BitAssignment n) : ZMod 2 := (0 : ZMod 2) + st₀ δ uWire * gBit δ
  have hSrcL (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (u : Fin 192) (hn67 : u.val ≠ 67)
      (hn69 : u.val ≠ 69) :
      stLoaded δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0 := by
    dsimp only [stLoaded]
    rw [findBranch_none fun _ ↦ hSrcGat u _, hSrcEnv δ hz u hn67 hn69]
  have hLoadGen (ph : BitAssignment n → ZMod 2) : cL.eval.1 * mkKetOpW rWork st₀ ph =
      mkKetOpW rWork stLoaded ph :=
    mkKetOpW_mul_ket_eq rWork _ _ _ ph fun δ hz ↦ by
      rw [ket_cLoadGatL2]
      refine congrArg ket (funext fun x ↦ ?_)
      dsimp only [stLoaded, lW]
      cases hfb : findBranch (fun b : Fin 2 ↦ rGat ⟨3 + b.val, by omega⟩) x with
      | none => rfl
      | some b =>
          simp only [findBranch_spec hfb, hGatZero δ hz _, zero_add,
            env151_maskParity_domZ rSrc (coinFn δ) (st₀ δ) (hSrcEnv δ hz) _ (dom_hkMLs b)]
  have hPhaseEq : cP.eval.1 * mkKetOpW rWork (fun δ ↦ stSplitRFwd uWire lW hW (stLoaded δ))
      (fun _ ↦ 0) =
      mkKetOpW rWork (fun δ ↦ stSplitRFwd uWire lW hW (stLoaded δ)) phPost :=
    mkKetOpW_mul_of_ket rWork _ _ _ _ _ fun δ hz ↦ by
      rw [show QubitizationWalkSem.bitSign 0 = 1 from rfl, one_smul]
      let γ := stSplitRFwd uWire lW hW (stLoaded δ)
      have hSrcγ (u : Fin 192) (hn67 : u.val ≠ 67) (hn69 : u.val ≠ 69) :
          γ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0 :=
        (stSplitRFwd_other _ (fun _ ↦ hSrcGat u _)
            (fun _ ↦ hSrcGat u _)).trans (hSrcL δ hz u hn67 hn69)
      have hHγ (b : Fin 2) : γ (rGat ⟨5 + b.val, by omega⟩) =
          (if bOf (coinFn δ) (hkMLs.getD b.val 0) then 1 else 0) * st₀ δ uWire := by
        change stSplitRFwd uWire lW hW (stLoaded δ) (hW b) = _
        dsimp only [stLoaded]
        rw [stSplitRFwd_hW hhInj hlhNe _ b, findBranch_self hlInj b, findBranch_none fun _ ↦
            (hGatO _ qIdx).symm]
      rw [ket_cPhaseGatH2_gather rSrc rGat hSrcGat (coinFn δ) hkMLs (hkMYs s)
          (st₀ δ uWire) γ hSrcγ hHγ (dom_hkMYs s)]
      dsimp only [γ, phPost, gBit, hkParityBool]
      rw [zero_add]
      rfl
  let eBranch (b : Fin 2) (γ : BitAssignment n) : ZMod 2 :=
    maskParity (hkMLs.getD b.val 0) (fun u : Fin 192 ↦ γ (rSrc u)) 192 le_rfl
  have heIndep (b : Fin 2) (γ₁ γ₂ : BitAssignment n)
      (h : ∀ x, (∀ i, x ≠ lW i) → (∀ i, x ≠ hW i) → x ≠ rGat ⟨0, by decide⟩ → γ₁ x = γ₂ x) :
      eBranch b γ₁ = eBranch b γ₂ :=
    maskParity_congr_support _ _ _ 192 le_rfl fun u _ _ ↦
        h (rSrc u) (fun _ ↦ hSrcGat u _) (fun _ ↦ hSrcGat u _) (hSrcGat u _)
  have hMut (δ : BitAssignment n) (_ : ∀ q, δ (rWork q) = 0) (b₁ b₂ : Fin 2) (hne : b₁ ≠ b₂)
      (hb1 : stLoaded δ (lW b₁) = 1) : stLoaded δ (lW b₂) = 0 := by
    dsimp only [stLoaded] at hb1 ⊢
    rw [findBranch_self hlInj b₁] at hb1
    rw [findBranch_self hlInj b₂]
    dsimp only at hb1 ⊢
    have hMB : (bOf (coinFn δ) (hkMLs.getD b₁.val 0) && bOf (coinFn δ) (hkMLs.getD b₂.val 0)) =
        false := by
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact hk_mutex (coinFn δ) b₁.val b₂.val hlt b₂.isLt
      · exact Bool.and_comm _ _ ▸ hk_mutex (coinFn δ) b₂.val b₁.val hgt b₁.isLt
    cases h : bOf (coinFn δ) (hkMLs.getD b₁.val 0)
    · exact absurd (h ▸ hb1) zero_ne_one
    · rw [h, Bool.true_and] at hMB
      exact congrArg (fun b : Bool ↦ if b then (1 : ZMod 2) else 0) hMB
  have hGOut (idx : Fin 7) (hbd : idx.val < 3 ∨ 5 ≤ idx.val) (δ : BitAssignment n)
      (hz : ∀ q, δ (rWork q) = 0) :
      stLoaded δ (rGat idx) = 0 := by
    dsimp only [stLoaded]
    rw [findBranch_none fun b e ↦ absurd (congrArg Fin.val (rGat.wires.injective e))
        (by (try dsimp [lW]); omega)]
    exact hGatZero δ hz idx
  have heEq (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (b : Fin 2) :
      eBranch b (stLoaded δ) = stLoaded δ (lW b) := by
    dsimp only [eBranch, stLoaded]
    rw [env151_maskParity_domZ rSrc (coinFn δ) (stLoaded δ) (hSrcL δ hz) _ (dom_hkMLs b),
        findBranch_self hlInj b]
  have sSplit := step_pSplitRBracket (by decide : 0 < 2) v rWork uWire lW hW
    (rGat ⟨0, by decide⟩) (rGat ⟨1, by decide⟩) (rGat ⟨2, by decide⟩)
    eBranch hInj heIndep stLoaded stLoaded (fun _ ↦ 0) phPost (.circuit cP) hMut
    (fun δ hz ↦ ⟨fun b : Fin 2 ↦ hGOut ⟨5 + b.val, by omega⟩
        (Or.inr (Nat.le_add_right 5 b.val)) δ hz,
      hGOut _ (Or.inl (by decide)) δ hz, hGOut _ (Or.inl (by decide)) δ hz,
          hGOut _ (Or.inl (by decide)) δ hz⟩)
    heEq (fun _ _ ↦ ⟨rfl, fun _ ↦ rfl, fun _ ↦ rfl, rfl, rfl, rfl, fun _ ↦ rfl⟩)
    (step_circ_mkKetOpW rWork _ _ _ _ cP hPhaseEq)
  exact step_hadamard_phase_kickback rWork uWire huWork st₀ (fun _ ↦
      0) gBit huId hstUpd (fun _ _ _ ↦ rfl)
    (fun δ b hz ↦ congrArg (fun c ↦ if hkParityBool c s then (1 : ZMod 2) else 0) (hcUpd δ b hz))
    (pHkInnerChunk8 v rSrc rO rGat hSrcGat hGatO s)
    (PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans
      (step_circ_mkKetOpW rWork st₀ stLoaded _ _ cL (hLoadGen (fun _ ↦ 0)))
      (PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans sSplit
        (step_circ_mkKetOpW rWork stLoaded st₀ _ _ cL (left_inv_of_sq_one (cLoadGatL2_sq _ _ _ _)
            (hLoadGen phPost)))))

def pHk01Chunk8 {Var : Type} {n : ℕ} (v : Var) (rSrc : QRegister 192 n) (rO : QRegister 40 n)
    (rGat : QRegister 7 n) (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i)
    (hGatO : ∀ (i : Fin 7) (q : Fin 40), rGat i ≠ rO q) : DynamicCircuit Var n :=
    .seq (pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO 0)
    (pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO 1)
theorem counts_pHk01Chunk8 {Var : Type} {n : ℕ} (v : Var) (rSrc : QRegister 192 n)
    (rO : QRegister 40 n) (rGat : QRegister 7 n) (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠
    rGat i) (hGatO : ∀ (i : Fin 7) (q : Fin 40), rGat i ≠ rO q) :
    (pHk01Chunk8 v rSrc rO rGat hSrcGat hGatO).count .T = 12 ∧
    (pHk01Chunk8 v rSrc rO rGat hSrcGat hGatO).count .TOFF = 0 :=
    by
  obtain ⟨t0, f0⟩ := counts_pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO 0; obtain ⟨t1, f1⟩ :=
      counts_pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO 1; dsimp only [pHk01Chunk8,
      DynamicCircuit.count]; rw [t0, t1, f0, f1]
  exact ⟨by omega, by omega⟩

theorem dw_pHk01Chunk8 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (rSrc : QRegister 192 n)
    (rO : QRegister 40 n) (rGat : QRegister 7 n) (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠
    rGat i) (hGatO : ∀ (i : Fin 7) (q : Fin 40), rGat i ≠ rO q) (hSrc : ∀ u : Fin 192, S (rSrc u))
    (hO : ∀ q : Fin 40, S (rO q)) (hGat : ∀ i : Fin 7, S (rGat i)) :
    DynWires S (pHk01Chunk8 v rSrc rO rGat hSrcGat hGatO) :=
    ⟨dw_pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO hSrc hO hGat 0,
    dw_pHkStepChunk8 v rSrc rO rGat hSrcGat hGatO hSrc hO hGat 1⟩
theorem step_pHk01Chunk8 {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (rSrc : QRegister 192 n) (rO : QRegister 40 n)
    (rGat : QRegister 7 n) (hSrcGat : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat i)
    (hSrcO : ∀ (u : Fin 192) (q : Fin 40), rSrc u ≠ rO q) (hGatO : ∀ (i : Fin 7)
    (q : Fin 40), rGat i ≠ rO q) (hOWork : ∀ (q : Fin 40) (w : Fin W), rO q ≠ rWork w)
    (coinFn : BitAssignment n → Fin (2 ^ 41)) (hcUpdO : ∀ (q : Fin 40) (δ : BitAssignment n)
    (b : ZMod 2), coinFn (Function.update δ (rO q) b) = coinFn δ)
    (stBase : BitAssignment n → BitAssignment n) (hBaseMidId : ∀ (j : Fin 32) (δ : BitAssignment n),
    (∀ q, δ (rWork q) = 0) → stBase δ (rO ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩) =
    δ (rO ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩)) (hBaseUpdMid : ∀ (j : Fin 32) (δ : BitAssignment n)
    (b : ZMod 2), (∀ q, δ (rWork q) = 0) → stBase (Function.update δ (rO ⟨mid32OutIdx j,
    mid32OutIdx_lt40 j⟩) b) = Function.update (stBase δ) (rO ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩) b)
    (hSrcBase : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin 192, u.val ≠ 67 → u.val ≠ 69 →
    stBase δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0)
    (hGatBase : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ i : Fin 7, stBase δ (rGat i) = 0) :
    SubspaceStep (mkKetOpW rWork stBase (fun _ ↦ 0)) (mkKetOpW rWork (fun δ ↦ stHk01 rO (coinFn δ)
    (stBase δ)) (fun _ ↦ 0)) (pHk01Chunk8 v rSrc rO rGat hSrcGat hGatO) := by
  let q0 : Fin 40 := ⟨mid32OutIdx ⟨30, by decide⟩, mid32OutIdx_lt40 ⟨30, by decide⟩⟩
  let q1 : Fin 40 := ⟨mid32OutIdx ⟨31, by decide⟩, mid32OutIdx_lt40 ⟨31, by decide⟩⟩
  have hq01 : rO q0 ≠ rO q1 := rO.wires.injective.ne (Fin.ne_of_val_ne mid32_q30_ne_q31)
  have s0 := step_pHkStepChunk8 v rWork rSrc rO rGat hSrcGat hGatO coinFn stBase 0
    (fun w ↦ hOWork q0 w)
    (fun δ hz ↦ hBaseMidId ⟨30, by decide⟩ δ hz)
    (fun δ b hz ↦ hBaseUpdMid ⟨30, by decide⟩ δ b hz)
    (fun δ b _ ↦ hcUpdO q0 δ b)
    hSrcBase hGatBase
  let stMid : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (stBase δ) (rO q0)
      (stBase δ (rO q0) + if hkParityBool (coinFn δ) 0 then 1 else 0)
  have s1 := step_pHkStepChunk8 v rWork rSrc rO rGat hSrcGat hGatO coinFn stMid 1
    (fun w ↦ hOWork q1 w)
    (fun δ hz ↦ by
      dsimp only [stMid]
      exact (Function.update_of_ne hq01.symm _ _).trans (hBaseMidId ⟨31, by decide⟩ δ hz))
    (fun δ b hz ↦ by
      change Function.update (stBase (Function.update δ (rO q1) b)) (rO q0)
          (stBase (Function.update δ (rO q1) b)
          (rO q0) + if hkParityBool (coinFn (Function.update δ (rO q1) b)) 0 then 1 else 0) = _
      rw [hcUpdO q1 δ b, hBaseUpdMid ⟨31, by decide⟩ δ b hz,
          Function.update_of_ne hq01, Function.update_comm hq01.symm]; rfl)
    (fun δ b _ ↦ hcUpdO q1 δ b)
    (fun δ hz u hn67 hn69 ↦ by
      dsimp only [stMid]
      exact (Function.update_of_ne (hSrcO u q0) _ _).trans (hSrcBase δ hz u hn67 hn69))
    (fun δ hz i ↦ by
      dsimp only [stMid]
      exact (Function.update_of_ne (hGatO i q0) _ _).trans (hGatBase δ hz i))
  exact PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans s0 s1

abbrev rGat7Of8 {n : ℕ} (rGat8 : QRegister 8 n) : QRegister 7 n :=
  rGat8.compose (QRegister.block 0 7 (by decide))

theorem rGat7Of8_eq {n : ℕ} (rGat8 : QRegister 8 n) (i : Fin 7) :
    rGat7Of8 rGat8 i = rGat8 ⟨i.val, by have := i.isLt; omega⟩ :=
  congrArg rGat8.wires (Fin.ext (Nat.zero_add i.val))

theorem ne_rGat7Of8 {n : ℕ} {w : Wire n} {r8 : QRegister 8 n} (h : ∀ j, w ≠ r8 j) (i : Fin 7) :
    w ≠ rGat7Of8 r8 i := by
  rw [rGat7Of8_eq]
  exact h _

theorem rGat8_7_ne_7Of8 {n : ℕ} (r8 : QRegister 8 n) (i : Fin 7) :
    r8 ⟨7, by decide⟩ ≠ rGat7Of8 r8 i := by
  rw [rGat7Of8_eq]
  exact r8.wires.injective.ne (Fin.ne_of_val_ne (by
    dsimp
    omega))

theorem valRouterInjChunk8 {n : ℕ} (rGat8 : QRegister 8 n) :
    let rGat7 := rGat7Of8 rGat8
    WOptInj 2 1 (fun _ : Fin 1 ↦ rGat8 ⟨7, by decide⟩)
      (wPairR (fun b : Fin 2 ↦ rGat7 ⟨3 + b.val, by omega⟩)
          (fun b : Fin 2 ↦ rGat7 ⟨5 + b.val, by omega⟩))
      (rGat7 ⟨0, by decide⟩) (rGat7 ⟨1, by decide⟩) (rGat7 ⟨2, by decide⟩) :=
  gat7RouterInj (rGat7Of8 rGat8) (rGat8 ⟨7, by decide⟩) fun i ↦ (rGat8_7_ne_7Of8 rGat8 i).symm

def cLoadValOuterChunk8 {n : ℕ} (rSrc214 : QRegister 214 n) (rSrc : QRegister 192 n)
    (rGat8 : QRegister 8 n) (hSrc214Gat8 : ∀ (u : Fin 214) (i : Fin 8), rSrc214 u ≠ rGat8 i)
    (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i) (p : Fin 16) : Circuit n :=
  let gIdx : Fin 214 := ⟨41 + valPairGLo p, Nat.add_lt_add_left (valPairGLo_bounds p).2 41⟩
  (cLoadGatL2 rSrc (rGat7Of8 rGat8) (fun u ↦ ne_rGat7Of8 (hSrcGat8 u)) (valPairMLs p) ;;ᶜ
   cXorMaskSrc192 rSrc (rGat8 ⟨7, by decide⟩) (fun u ↦ hSrcGat8 u ⟨7, by decide⟩)
       (valPairBaseMask p) 192 le_rfl) ;;ᶜ
   Circuit.CNOT (rSrc214 gIdx) (rGat8 ⟨7, by decide⟩) (hSrc214Gat8 gIdx ⟨7, by decide⟩)

def cEmitValHChunk8 {n : ℕ} (rO : QRegister 40 n) (rGat8 : QRegister 8 n) (hGat8O : ∀ (i : Fin 8)
    (q : Fin 40), rGat8 i ≠ rO q) (p : Fin 16) : Circuit n :=
  let rGat7 := rGat7Of8 rGat8
  let hGat7O : ∀ (i : Fin 7) (q : Fin 40), rGat7 i ≠ rO q :=
    fun i q ↦ by rw [rGat7Of8_eq]; exact hGat8O _ q
  let qLo : Fin 40 :=
      ⟨mid32OutIdx ⟨valPairJLo p, valPairJLo_lt32 p⟩, mid32OutIdx_lt40 ⟨valPairJLo p,
      valPairJLo_lt32 p⟩⟩; let qHi : Fin 40 :=
                             ⟨mid32OutIdx ⟨valPairJHi p, valPairJHi_lt32 p⟩,
                             mid32OutIdx_lt40 ⟨valPairJHi p, valPairJHi_lt32 p⟩⟩
  let h0 : Fin 7 := ⟨5, by decide⟩
  let h1 : Fin 7 := ⟨6, by decide⟩
  if p.val < 14 then
    (Circuit.CNOT (rGat7 h0) (rO qLo) (hGat7O h0 qLo) ;;ᶜ
     Circuit.CNOT (rGat7 h0) (rO qHi) (hGat7O h0 qHi)) ;;ᶜ
     Circuit.CNOT (rGat7 h1) (rO qHi) (hGat7O h1 qHi)
  else
    Circuit.CNOT (rGat7 h0) (rO qLo) (hGat7O h0 qLo) ;;ᶜ
    Circuit.CNOT (rGat7 h1) (rO qHi) (hGat7O h1 qHi)

def pValPairStepChunk8 {Var : Type} {n : ℕ} (v : Var) (rSrc214 : QRegister 214 n)
    (rSrc : QRegister 192 n) (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214 u ≠ rO q) (hSrc214Gat8 : ∀ (u : Fin 214)
    (i : Fin 8), rSrc214 u ≠ rGat8 i) (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i)
    (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q) (p : Fin 16) : DynamicCircuit Var n :=
  let rGat7 := rGat7Of8 rGat8
  let uWire := rGat8 ⟨7, by decide⟩
  let lW : Fin 2 → Wire n := fun b ↦ rGat7 ⟨3 + b.val, by have := b.isLt; omega⟩
  let hW : Fin 2 → Wire n := fun b ↦ rGat7 ⟨5 + b.val, by have := b.isLt; omega⟩
  let cLO := cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 p;
  let cEH := cEmitValHChunk8 rO rGat8 hGat8O p; let cED := cEmitValDirect rSrc214 rO hSrc214O p
  .seq
    (.seq (.circuit cLO)
      (.seq (pSplitRBracket v uWire lW hW (rGat7 ⟨0, by decide⟩) (rGat7 ⟨1, by decide⟩)
               (rGat7 ⟨2, by decide⟩) (valRouterInjChunk8 rGat8) (.circuit cEH))
        (.circuit cLO)))
    (.circuit cED)

theorem count_cLoadValOuterChunk8 {n : ℕ} (rSrc214 : QRegister 214 n) (rSrc : QRegister 192 n)
    (rGat8 : QRegister 8 n) (hSrc214Gat8 : ∀ (u : Fin 214) (i : Fin 8), rSrc214 u ≠ rGat8 i)
    (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i)
    (p : Fin 16) : (cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 p).count .T = 0 ∧
    (cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 p).count .TOFF = 0 := by
  obtain ⟨tL, fL⟩ :=
      count_cLoadGatL2 rSrc (rGat7Of8 rGat8) (fun u ↦ ne_rGat7Of8 (hSrcGat8 u)) (valPairMLs p)
  obtain ⟨tX, fX⟩ :=
      count_cXorMaskSrc192 rSrc (rGat8 ⟨7, by decide⟩) (fun u ↦ hSrcGat8 u ⟨7, by decide⟩)
      (valPairBaseMask p) 192 le_rfl
  dsimp only [cLoadValOuterChunk8]
  refine ⟨?_, ?_⟩
  · rw [Circuit.count_seq, Circuit.count_seq, tL, tX]
    rfl
  · rw [Circuit.count_seq, Circuit.count_seq, fL, fX]
    rfl

theorem cw_cLoadValOuterChunk8 {n : ℕ} {S : Wire n → Prop} (rSrc214 : QRegister 214 n)
    (rSrc : QRegister 192 n) (rGat8 : QRegister 8 n) (hSrc214Gat8 : ∀ (u : Fin 214)
    (i : Fin 8), rSrc214 u ≠ rGat8 i) (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i)
    (hSrc214 : ∀ u : Fin 214, S (rSrc214 u)) (hSrc : ∀ u : Fin 192, S (rSrc u))
    (hGat8 : ∀ i : Fin 8, S (rGat8 i))
    (p : Fin 16) : CircWires S (cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 p) :=
  ⟨⟨cw_cLoadGatL2 rSrc (rGat7Of8 rGat8) _ hSrc (fun i ↦ rGat7Of8_eq rGat8 i ▸ hGat8 _)
      (valPairMLs p),
    cw_cXorMaskSrc192 rSrc _ _ hSrc (hGat8 _) (valPairBaseMask p) 192 le_rfl⟩, cw_cnot (hSrc214 _)
        (hGat8 _)⟩

theorem ket_cLoadValOuterChunk8 {n : ℕ} [NeZero (2 ^ n)] (rSrc214 : QRegister 214 n)
    (rSrc : QRegister 192 n) (rGat8 : QRegister 8 n)
    (hSrc214Gat8 : ∀ (u : Fin 214) (i : Fin 8), rSrc214 u ≠ rGat8 i) (hSrcGat8 : ∀ (u : Fin 192)
        (i : Fin 8), rSrc u ≠ rGat8 i)
    (p : Fin 16) (c : Fin (2 ^ 41)) (γ : BitAssignment n)
    (hSrc : ∀ u : Fin 192, u.val ≠ 67 → u.val ≠ 69 → γ (rSrc u) = if (e151Dom c).testBit (1 +
        u.val) then 1 else 0)
    (hSrc214 : ∀ u : Fin 214, u.val ≠ 67 → u.val ≠ 69 → γ (rSrc214 u) =
        if src214Bit c u then 1 else 0) :
    let rGat7 := rGat7Of8 rGat8
    let lW : Fin 2 → Wire n := fun b ↦ rGat7 ⟨3 + b.val, by omega⟩
    let uWire := rGat8 ⟨7, by decide⟩
    (cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 p).eval.1.mulVec (ket γ) =
      ket (Function.update (fun x ↦ match findBranch lW x with
          | some b => γ x + if bOf c ((valPairMLs p).getD b.val 0) then 1 else 0
          | none => γ x) uWire (γ uWire + if valUBool c p then 1 else 0)) := by
  intro rGat7 lW uWire
  dsimp only [rGat7, lW, uWire, cLoadValOuterChunk8]
  have hbLo := valPairGLo_bounds p
  let gIdx : Fin 214 := ⟨41 + valPairGLo p, Nat.add_lt_add_left hbLo.2 41⟩
  let γ₁ : BitAssignment n := fun x ↦
    match findBranch (fun b : Fin 2 ↦ rGat7Of8 rGat8 ⟨3 + b.val, by omega⟩) x with
    | some b => γ x + if bOf c ((valPairMLs p).getD b.val 0) then 1 else 0
    | none => γ x
  have hγ1Eq : (fun x ↦ match findBranch (fun b : Fin 2 ↦ rGat7Of8 rGat8 ⟨3 + b.val,
      by omega⟩) x with
      | some b => γ x + maskParity ((valPairMLs p).getD b.val 0) (fun u ↦ γ (rSrc u)) 192 le_rfl
      | none => γ x) = γ₁ := funext fun x ↦ by
    dsimp only [γ₁]
    cases findBranch (fun b : Fin 2 ↦ rGat7Of8 rGat8 ⟨3 + b.val, by omega⟩) x with
    | none => rfl
    | some b => simp only [env151_maskParity_domZ rSrc c γ hSrc _ (dom_valPairMLs p b)]
  have hSrc1 (u : Fin 192) (hn67 : u.val ≠ 67) (hn69 : u.val ≠ 69) :
      γ₁ (rSrc u) = if (e151Dom c).testBit (1 + u.val) then 1 else 0 := by
    dsimp only [γ₁]
    rw [findBranch_none (fun _ ↦ ne_rGat7Of8 (hSrcGat8 u) _), hSrc u hn67 hn69]
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_cLoadGatL2, hγ1Eq, ket_cXorMaskSrc192,
    env151_maskParity_domZ rSrc c γ₁ hSrc1 _ (dom_valPairBase p), ket_CNOT, Function.update_idem,
    Function.update_self, Function.update_of_ne (hSrc214Gat8 gIdx ⟨7, by decide⟩)]
  dsimp only [γ₁]
  rw [findBranch_none (fun _ ↦ rGat8_7_ne_7Of8 rGat8 _),
    findBranch_none (fun _ ↦ ne_rGat7Of8 (hSrc214Gat8 gIdx) _),
    hSrc214 gIdx (Nat.ne_of_gt (by omega : 67 < 41 + valPairGLo p))
        (Nat.ne_of_gt (by omega : 69 < 41 + valPairGLo p)),
    src214Bit_gate c (valPairGLo p) hbLo.1 hbLo.2, add_assoc, Stage1AsymRevEngine.z2_add_ite_xor]
  rfl

theorem count_cEmitValHChunk8 {n : ℕ} (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q)
    (p : Fin 16) : (cEmitValHChunk8 rO rGat8 hGat8O p).count .T = 0 ∧
    (cEmitValHChunk8 rO rGat8 hGat8O p).count .TOFF = 0 := by
  dsimp only [cEmitValHChunk8]
  split_ifs <;> simp [Circuit.CNOT]

theorem cw_cEmitValHChunk8 {n : ℕ} {S : Wire n → Prop} (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q) (hO : ∀ q : Fin 40, S (rO q))
    (hGat8 : ∀ i : Fin 8, S (rGat8 i))
    (p : Fin 16) : CircWires S (cEmitValHChunk8 rO rGat8 hGat8O p) := by
  have hGat7 : ∀ i : Fin 7, S (rGat7Of8 rGat8 i) := fun i ↦ by
    rw [rGat7Of8_eq]; exact hGat8 _
  dsimp only [cEmitValHChunk8]; split_ifs
  · exact ⟨⟨cw_cnot (hGat7 _) (hO _), cw_cnot (hGat7 _) (hO _)⟩, cw_cnot (hGat7 _) (hO _)⟩
  · exact ⟨cw_cnot (hGat7 _) (hO _), cw_cnot (hGat7 _) (hO _)⟩

theorem ket_cEmitValHChunk8 {n : ℕ} [NeZero (2 ^ n)]
    (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q)
    (p : Fin 16) (γ : BitAssignment n) :
    let rGat7 := rGat7Of8 rGat8;
    let qLo : Fin 40 :=
        ⟨mid32OutIdx ⟨valPairJLo p, valPairJLo_lt32 p⟩, mid32OutIdx_lt40 ⟨valPairJLo p,
        valPairJLo_lt32 p⟩⟩; let qHi : Fin 40 :=
                               ⟨mid32OutIdx ⟨valPairJHi p, valPairJHi_lt32 p⟩,
                               mid32OutIdx_lt40 ⟨valPairJHi p, valPairJHi_lt32 p⟩⟩
    let h0 := rGat7 ⟨5, by decide⟩
    let h1 := rGat7 ⟨6, by decide⟩
    (cEmitValHChunk8 rO rGat8 hGat8O p).eval.1.mulVec (ket γ) =
      ket (Function.update
            (Function.update γ (rO qLo) (γ (rO qLo) + γ h0))
            (rO qHi) (γ (rO qHi) + if p.val < 14 then γ h0 + γ h1 else γ h1)) := by
  intro rGat7 qLo qHi h0 h1
  have hGat7O : ∀ (i : Fin 7) (q : Fin 40), rGat7 i ≠ rO q :=
    fun i q ↦ by rw [rGat7Of8_eq]; exact hGat8O _ q
  have hNeLH : rO qLo ≠ rO qHi :=
      rO.wires.injective.ne (Fin.ne_of_val_ne (valPairOutLoNeHi p)); dsimp only [cEmitValHChunk8]
  split_ifs with hp14
  · rw [eval_seq_mulVec, eval_seq_mulVec, ket_CNOT, ket_CNOT,
        Function.update_of_ne hNeLH.symm, Function.update_of_ne (hGat7O ⟨5, by decide⟩ qLo),
        ket_CNOT, Function.update_self, Function.update_idem,
        Function.update_of_ne (hGat7O ⟨6, by decide⟩ qHi),
        Function.update_of_ne (hGat7O ⟨6, by decide⟩ qLo), add_assoc]
  · rw [eval_seq_mulVec, ket_CNOT, ket_CNOT,
        Function.update_of_ne hNeLH.symm, Function.update_of_ne (hGat7O ⟨6, by decide⟩ qLo)]

theorem ket_cEmitValDirect_domZ {n : ℕ} [NeZero (2 ^ n)]
    (rSrc214 : QRegister 214 n) (rO : QRegister 40 n)
    (hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214 u ≠ rO q)
    (p : Fin 16) (c : Fin (2 ^ 41)) (β : BitAssignment n)
    (hSrc214 : ∀ u : Fin 214, u.val ≠ 67 → u.val ≠ 69 → β (rSrc214 u) =
        if src214Bit c u then 1 else 0) :
    let qLo : Fin 40 :=
        ⟨mid32OutIdx ⟨valPairJLo p, valPairJLo_lt32 p⟩, mid32OutIdx_lt40 ⟨valPairJLo p,
        valPairJLo_lt32 p⟩⟩; let qHi : Fin 40 :=
                               ⟨mid32OutIdx ⟨valPairJHi p, valPairJHi_lt32 p⟩,
                               mid32OutIdx_lt40 ⟨valPairJHi p, valPairJHi_lt32 p⟩⟩
    let γH :=
        Function.update (Function.update β (rO qLo) (β (rO qLo) + if valH0Bool c p then 1 else 0))
        (rO qHi) (β (rO qHi) + if valHHiBool c p then 1 else 0)
    (cEmitValDirect rSrc214 rO hSrc214O p).eval.1.mulVec (ket γH) =
      ket (stValStep rO c p β) := by
  intro qLo qHi γH
  have hNeLH : rO qLo ≠ rO qHi := rO.wires.injective.ne (Fin.ne_of_val_ne (valPairOutLoNeHi p))
  have hgAt (g : ℕ) (hb : 151 ≤ g ∧ g < 173) :
      γH (rSrc214 ⟨41 + g, Nat.add_lt_add_left hb.2 41⟩) = if gate173Bit c g then 1 else 0 := by
    dsimp only [γH]
    rw [Function.update_of_ne (hSrc214O _ qHi), Function.update_of_ne (hSrc214O _ qLo),
      hSrc214 _ (Nat.ne_of_gt (by omega : 67 < 41 + g)) (Nat.ne_of_gt (by omega : 69 < 41 + g)),
      src214Bit_gate c g hb.1 hb.2]
  have hγHLo : γH (rO qLo) = β (rO qLo) + if valH0Bool c p then 1 else 0 := by
    dsimp only [γH]
    rw [Function.update_of_ne hNeLH, Function.update_self]
  have hγHHi : γH (rO qHi) = β (rO qHi) + if valHHiBool c p then 1 else 0 :=
      Function.update_self _ _ _
  have hLoIte : (if xor (valH0Bool c p) (gate173Bit c (valPairGLo p)) then (1 : ZMod 2) else 0) =
      if valLoBool c p then 1 else 0 := rfl
  change _ = ket (Function.update (Function.update β (rO qLo)
      (β (rO qLo) + if valLoBool c p then 1 else 0))
    (rO qHi) (β (rO qHi) + if valHiBool c p then 1 else 0))
  dsimp only [cEmitValDirect]
  by_cases h8 : p.val < 8
  · rw [_root_.ite_eq_left h8, ket_CNOT, hγHLo, hgAt _ (valPairGLo_bounds p), add_assoc,
      PhotochemistrySolution.Stage1AsymRevEngine.z2_add_ite_xor, hLoIte]
    dsimp only [γH]
    rw [Function.update_comm hNeLH.symm, Function.update_idem,
      show valHHiBool c p = valHiBool c p from (_root_.ite_eq_left h8).symm]
  · rw [_root_.ite_eq_right h8]
    have hTwo (g : ℕ) (hb : 151 ≤ g ∧ g < 173) (hHi : xor (valHHiBool c p)
        (gate173Bit c g) = valHiBool c p) :
        (Circuit.CNOT (rSrc214 ⟨41 + valPairGLo p, Nat.add_lt_add_left (valPairGLo_bounds p).2 41⟩)
            (rO qLo) (hSrc214O _ qLo) ;;ᶜ
         Circuit.CNOT (rSrc214 ⟨41 + g, Nat.add_lt_add_left hb.2 41⟩) (rO qHi)
             (hSrc214O _ qHi)).eval.1.mulVec (ket γH) =
          ket (Function.update (Function.update β (rO qLo)
              (β (rO qLo) + if valLoBool c p then 1 else 0))
            (rO qHi) (β (rO qHi) + if valHiBool c p then 1 else 0)) := by
      rw [eval_seq_mulVec, ket_CNOT, hγHLo, hgAt _ (valPairGLo_bounds p), add_assoc,
        Stage1AsymRevEngine.z2_add_ite_xor, ket_CNOT, Function.update_of_ne hNeLH.symm,
        hγHHi, Function.update_of_ne (hSrc214O _ qLo), hgAt g hb, add_assoc,
        PhotochemistrySolution.Stage1AsymRevEngine.z2_add_ite_xor, hLoIte, hHi]
      dsimp only [γH]
      rw [Function.update_comm hNeLH.symm, Function.update_idem, Function.update_idem]
    by_cases h14 : p.val < 14
    · rw [_root_.ite_eq_left h14]
      exact hTwo _ (valPairGT_bounds p)
          (by simp only [valHiBool, _root_.ite_eq_right h8, _root_.ite_eq_left h14])
    · rw [_root_.ite_eq_right h14]
      exact hTwo _ (valPairGLo_bounds p)
          (by simp only [valHiBool, _root_.ite_eq_right h8, _root_.ite_eq_right h14])

theorem counts_pValPairStepChunk8 {Var : Type} {n : ℕ} (v : Var) (rSrc214 : QRegister 214 n)
    (rSrc : QRegister 192 n) (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214 u ≠ rO q) (hSrc214Gat8 : ∀ (u : Fin 214)
    (i : Fin 8), rSrc214 u ≠ rGat8 i) (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i)
    (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q)
    (p : Fin 16) :
    (pValPairStepChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O p).count .T =
    6 ∧
    (pValPairStepChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O p).count .TOFF
    = 0 := by
  let rGat7 := rGat7Of8 rGat8; obtain ⟨tLO, fLO⟩ :=
      count_cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 p; obtain ⟨tEH, fEH⟩ :=
      count_cEmitValHChunk8 rO rGat8 hGat8O p; obtain ⟨tED, fED⟩ :=
      count_cEmitValDirect rSrc214 rO hSrc214O p
  obtain ⟨tB, fB⟩ := counts_pSplitRBracket v (rGat8 ⟨7, by decide⟩)
    (fun b : Fin 2 ↦ rGat7 ⟨3 + b.val, by have := b.isLt; omega⟩)
    (fun b : Fin 2 ↦ rGat7 ⟨5 + b.val, by have := b.isLt; omega⟩)
    (rGat7 ⟨0, by decide⟩) (rGat7 ⟨1, by decide⟩) (rGat7 ⟨2, by decide⟩)
    (valRouterInjChunk8 rGat8) (.circuit (cEmitValHChunk8 rO rGat8 hGat8O p))
  dsimp only [pValPairStepChunk8, DynamicCircuit.count] at tB fB ⊢;
  rw [tLO, fLO, tB, fB, tEH, fEH, tED, fED]
  exact ⟨by omega, by omega⟩

theorem dw_pValPairStepChunk8 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rSrc214 : QRegister 214 n) (rSrc : QRegister 192 n) (rO : QRegister 40 n)
    (rGat8 : QRegister 8 n) (hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214 u ≠ rO q)
    (hSrc214Gat8 : ∀ (u : Fin 214) (i : Fin 8), rSrc214 u ≠ rGat8 i) (hSrcGat8 : ∀ (u : Fin 192)
    (i : Fin 8), rSrc u ≠ rGat8 i) (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q)
    (hSrc214 : ∀ u : Fin 214, S (rSrc214 u)) (hSrc : ∀ u : Fin 192, S (rSrc u))
    (hO : ∀ q : Fin 40, S (rO q)) (hGat8 : ∀ i : Fin 8, S (rGat8 i))
    (p : Fin 16) :
    DynWires S (pValPairStepChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O p)
    := by
  have hGat7 : ∀ i : Fin 7, S (rGat7Of8 rGat8 i) := fun i ↦ by
    rw [rGat7Of8_eq]; exact hGat8 _
  have dwLO := cw_cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 hSrc214 hSrc hGat8 p;
  have dwEH := cw_cEmitValHChunk8 rO rGat8 hGat8O hO hGat8 p;
  have dwED := cw_cEmitValDirect rSrc214 rO hSrc214O hSrc214 hO p
  have dwB := dynWires_pSplitRBracket v (rGat8 ⟨7, by decide⟩)
    (fun b : Fin 2 ↦ rGat7Of8 rGat8 ⟨3 + b.val, by have := b.isLt; omega⟩)
    (fun b : Fin 2 ↦ rGat7Of8 rGat8 ⟨5 + b.val, by have := b.isLt; omega⟩)
    (rGat7Of8 rGat8 ⟨0, by decide⟩) (rGat7Of8 rGat8 ⟨1, by decide⟩) (rGat7Of8 rGat8 ⟨2, by decide⟩)
    (valRouterInjChunk8 rGat8) (.circuit (cEmitValHChunk8 rO rGat8 hGat8O p))
    (hGat8 _) (fun _ ↦ hGat7 _) (fun _ ↦ hGat7 _) (hGat7 _) (hGat7 _) (hGat7 _) dwEH
  exact ⟨⟨dwLO, ⟨dwB, dwLO⟩⟩, dwED⟩

theorem step_pValPairStepChunk8 {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (rSrc214 : QRegister 214 n)
    (rSrc : QRegister 192 n) (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214 u ≠ rO q) (hSrc214Gat8 : ∀ (u : Fin 214)
    (i : Fin 8), rSrc214 u ≠ rGat8 i) (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i)
    (hSrcO : ∀ (u : Fin 192) (q : Fin 40), rSrc u ≠ rO q) (hGat8O : ∀ (i : Fin 8)
    (q : Fin 40), rGat8 i ≠ rO q) (coinFn : BitAssignment n → Fin (2 ^ 41))
    (st₀ : BitAssignment n → BitAssignment n) (p : Fin 16) (hSrcEnv : ∀ δ, (∀ q, δ (rWork q) = 0) →
    ∀ u : Fin 192, u.val ≠ 67 → u.val ≠ 69 → st₀ δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 +
    u.val) then 1 else 0) (hSrc214Env : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin 214, u.val ≠ 67 →
    u.val ≠ 69 → st₀ δ (rSrc214 u) = if src214Bit (coinFn δ) u then 1 else 0)
    (hGatZero : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ i : Fin 8, st₀ δ (rGat8 i) = 0) :
    SubspaceStep (mkKetOpW rWork st₀ (fun _ ↦ 0))
    (mkKetOpW rWork (fun δ ↦ stValStep rO (coinFn δ) p (st₀ δ)) (fun _ ↦ 0))
    (pValPairStepChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O p) := by
  let rGat7 := rGat7Of8 rGat8
  let uWire := rGat8 ⟨7, by decide⟩
  let lW : Fin 2 → Wire n := fun b ↦ rGat7 ⟨3 + b.val, by have := b.isLt; omega⟩
  let hW : Fin 2 → Wire n := fun b ↦ rGat7 ⟨5 + b.val, by have := b.isLt; omega⟩
  let qLo : Fin 40 :=
      ⟨mid32OutIdx ⟨valPairJLo p, valPairJLo_lt32 p⟩, mid32OutIdx_lt40 ⟨valPairJLo p,
      valPairJLo_lt32 p⟩⟩; let qHi : Fin 40 :=
                             ⟨mid32OutIdx ⟨valPairJHi p, valPairJHi_lt32 p⟩,
                             mid32OutIdx_lt40 ⟨valPairJHi p,
                             valPairJHi_lt32 p⟩⟩; let hInj :=
                                                    valRouterInjChunk8 rGat8; obtain ⟨hlInj, hhInj,
                                                    hlhNe⟩ := wPairR_inj_props hInj.w_inj
  have hGat7Zero : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ i : Fin 7, st₀ δ (rGat7 i) = 0 :=
    fun δ hz i ↦ by rw [rGat7Of8_eq]; exact hGatZero δ hz _
  have hGat7O : ∀ (i : Fin 7) (q : Fin 40), rGat7 i ≠ rO q :=
    fun i q ↦ by rw [rGat7Of8_eq]; exact hGat8O _ q
  have hSrcGat7 : ∀ (u : Fin 192) (i : Fin 7), rSrc u ≠ rGat7 i :=
    fun u i ↦ by rw [rGat7Of8_eq]; exact hSrcGat8 u _
  have hUL : ∀ b : Fin 2, uWire ≠ lW b := fun b e ↦ hInj.uLo_ne_w 0 b 0 e
  have hUH : ∀ b : Fin 2, uWire ≠ hW b := fun b e ↦ hInj.uLo_ne_w 0 b 1 e
  let cLO := cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 p;
  let cEH := cEmitValHChunk8 rO rGat8 hGat8O p; let cED := cEmitValDirect rSrc214 rO hSrc214O p
  let stHOut : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (Function.update (st₀ δ) (rO qLo)
      (st₀ δ (rO qLo) + if valH0Bool (coinFn δ) p then 1 else 0)) (rO qHi)
      (st₀ δ (rO qHi) + if valHHiBool (coinFn δ) p then 1 else 0)
  let stLoadOf (stB : BitAssignment n → BitAssignment n) : BitAssignment n → BitAssignment n :=
    fun δ ↦
      Function.update
        (fun x ↦ match findBranch lW x with
          | some b => if bOf (coinFn δ) ((valPairMLs p).getD b.val 0) then 1 else 0
          | none => stB δ x)
        uWire (if valUBool (coinFn δ) p then 1 else 0)
  have hLoadEq : cLO.eval.1 * mkKetOpW rWork st₀ (fun _ ↦ 0) = mkKetOpW rWork (stLoadOf st₀)
      (fun _ ↦ 0) :=
    mkKetOpW_mul_ket_eq rWork _ _ _ _ fun δ hz ↦ by
      rw [ket_cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 p (coinFn δ) (st₀ δ)
        (hSrcEnv δ hz) (hSrc214Env δ hz)]
      refine congrArg ket (funext fun x ↦ ?_)
      dsimp only [stLoadOf]
      by_cases hxu : x = uWire
      · subst hxu
        rw [Function.update_self, Function.update_self, hGatZero δ hz _, zero_add]
      · rw [Function.update_of_ne hxu, Function.update_of_ne hxu]
        cases hfb : findBranch lW x with
        | none => rfl
        | some b =>
            dsimp only
            rw [findBranch_spec hfb, hGat7Zero δ hz _, zero_add]
  have hUnloadEq : cLO.eval.1 * mkKetOpW rWork (stLoadOf stHOut)
      (fun _ ↦ 0) = mkKetOpW rWork stHOut (fun _ ↦ 0) :=
    mkKetOpW_mul_ket_eq rWork _ _ _ _ fun δ hz ↦ by
      have hSrcL1 (u : Fin 192) (hn67 : u.val ≠ 67) (hn69 : u.val ≠ 69) :
          stLoadOf stHOut δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 +
              u.val) then 1 else 0 := by
        dsimp only [stLoadOf, stHOut]
        rw [Function.update_of_ne (hSrcGat8 u _), findBranch_none (fun _ ↦ hSrcGat7 u _),
          Function.update_of_ne (hSrcO u qHi), Function.update_of_ne (hSrcO u qLo),
              hSrcEnv δ hz u hn67 hn69]
      have hSrc214L1 (u : Fin 214) (hn67 : u.val ≠ 67) (hn69 : u.val ≠ 69) :
          stLoadOf stHOut δ (rSrc214 u) = if src214Bit (coinFn δ) u then 1 else 0 := by
        dsimp only [stLoadOf, stHOut]
        rw [Function.update_of_ne (hSrc214Gat8 u _),
          findBranch_none (fun _ ↦ ne_rGat7Of8 (hSrc214Gat8 u) _),
          Function.update_of_ne (hSrc214O u qHi), Function.update_of_ne (hSrc214O u qLo),
              hSrc214Env δ hz u hn67 hn69]
      rw [ket_cLoadValOuterChunk8 rSrc214 rSrc rGat8 hSrc214Gat8 hSrcGat8 p (coinFn δ)
        (stLoadOf stHOut δ) hSrcL1 hSrc214L1]
      refine congrArg ket (funext fun x ↦ ?_)
      by_cases hxu : x = uWire
      · subst hxu
        rw [Function.update_self]
        dsimp only [stLoadOf, stHOut]
        rw [Function.update_self, zmod2_add_self,
          Function.update_of_ne (hGat8O _ qHi), Function.update_of_ne (hGat8O _ qLo),
              hGatZero δ hz _]
      · rw [Function.update_of_ne hxu]
        cases hfb : findBranch lW x with
        | none =>
            dsimp only [stLoadOf]
            rw [Function.update_of_ne hxu, hfb]
        | some b =>
            dsimp only [stLoadOf, stHOut]
            rw [findBranch_spec hfb, Function.update_of_ne (hUL b).symm, findBranch_self hlInj b]
            dsimp only
            rw [zmod2_add_self, Function.update_of_ne (hGat7O _ qHi),
                Function.update_of_ne (hGat7O _ qLo), hGat7Zero δ hz _]
  have hEmitHEq : cEH.eval.1 * mkKetOpW rWork (fun δ ↦ stSplitRFwd uWire lW hW (stLoadOf st₀ δ))
      (fun _ ↦ 0) =
      mkKetOpW rWork (fun δ ↦ stSplitRFwd uWire lW hW (stLoadOf stHOut δ)) (fun _ ↦ 0) :=
    mkKetOpW_mul_ket_eq rWork _ _ _ _ fun δ _ ↦ by
      rw [ket_cEmitValHChunk8]
      refine congrArg ket ?_
      let γ := stSplitRFwd uWire lW hW (stLoadOf st₀ δ)
      have hh0 : γ (rGat7 ⟨5, by decide⟩) = if valH0Bool (coinFn δ) p then 1 else 0 := by
        change stSplitRFwd uWire lW hW (stLoadOf st₀ δ) (hW 0) = _
        rw [stSplitRFwd_hW hhInj hlhNe]
        dsimp only [stLoadOf, valH0Bool]
        rw [Function.update_self, Function.update_of_ne (hUL 0).symm, findBranch_self hlInj 0]
        dsimp only
        rw [z2_mul_ite_and]
        rfl
      have hh1 : γ (rGat7 ⟨6, by decide⟩) = if valH1Bool (coinFn δ) p then 1 else 0 := by
        change stSplitRFwd uWire lW hW (stLoadOf st₀ δ) (hW 1) = _
        rw [stSplitRFwd_hW hhInj hlhNe]
        dsimp only [stLoadOf, valH1Bool]
        rw [Function.update_self, Function.update_of_ne (hUL 1).symm, findBranch_self hlInj 1]
        dsimp only
        rw [z2_mul_ite_and]
        rfl
      have hOOther (q : Fin 40) : γ (rO q) = st₀ δ (rO q) := by
        dsimp only [γ, stLoadOf]
        rw [stSplitRFwd_other _ (fun _ ↦ (hGat7O _ q).symm) (fun _ ↦ (hGat7O _ q).symm),
          Function.update_of_ne (hGat8O _ q).symm, findBranch_none fun _ ↦ (hGat7O _ q).symm]
      have hHiVal : (if p.val < 14 then γ (rGat7 ⟨5, by decide⟩) + γ (rGat7 ⟨6, by decide⟩)
          else γ (rGat7 ⟨6, by decide⟩)) = if valHHiBool (coinFn δ) p then 1 else 0 := by
        rw [hh0, hh1, PhotochemistrySolution.Stage1AsymRevEngine.z2_add_ite_xor]
        dsimp only [valHHiBool]
        split_ifs <;> rfl
      change Function.update (Function.update γ (rO qLo) (γ (rO qLo) + γ (rGat7 ⟨5, by decide⟩)))
        (rO qHi) (γ (rO qHi) + if p.val < 14 then γ (rGat7 ⟨5, by decide⟩) +
            γ (rGat7 ⟨6, by decide⟩)
          else γ (rGat7 ⟨6, by decide⟩)) = _
      rw [hHiVal, hh0, hOOther qLo, hOOther qHi,
        stSplitRFwd_upd_other uWire lW hW _ _ (hGat8O _ qLo).symm (fun _ ↦ (hGat7O _ qLo).symm)
            (fun _ ↦ (hGat7O _ qLo).symm),
        stSplitRFwd_upd_other uWire lW hW _ _ (hGat8O _ qHi).symm (fun _ ↦ (hGat7O _ qHi).symm)
            (fun _ ↦ (hGat7O _ qHi).symm)]
      refine congrArg (stSplitRFwd uWire lW hW) (funext fun x ↦ ?_)
      by_cases hxu : x = uWire
      · subst hxu
        dsimp only [stLoadOf]
        rw [Function.update_of_ne (hGat8O _ qHi), Function.update_of_ne (hGat8O _ qLo),
          Function.update_self, Function.update_self]
      · by_cases hxH : x = rO qHi
        · subst hxH
          dsimp only [stLoadOf, stHOut]
          rw [Function.update_self, Function.update_of_ne (hGat8O _ qHi).symm,
            findBranch_none (fun _ ↦ (hGat7O _ qHi).symm), Function.update_self]
        · rw [Function.update_of_ne hxH]
          by_cases hxL : x = rO qLo
          · subst hxL
            dsimp only [stLoadOf, stHOut]
            rw [Function.update_self, Function.update_of_ne (hGat8O _ qLo).symm,
              findBranch_none (fun _ ↦ (hGat7O _ qLo).symm), Function.update_of_ne hxH,
                  Function.update_self]
          · dsimp only [stLoadOf, stHOut]
            rw [Function.update_of_ne hxL, Function.update_of_ne hxu, Function.update_of_ne hxu]
            cases findBranch lW x with
            | some _ => rfl
            | none => rw [Function.update_of_ne hxH, Function.update_of_ne hxL]
  let eBranch (b : Fin 2) (γ : BitAssignment n) : ZMod 2 :=
    maskParity ((valPairMLs p).getD b.val 0) (fun u : Fin 192 ↦ γ (rSrc u)) 192 le_rfl
  have heIndep (b : Fin 2) (γ₁ γ₂ : BitAssignment n)
      (h : ∀ x, (∀ i, x ≠ lW i) → (∀ i, x ≠ hW i) → x ≠ rGat7 ⟨0, by decide⟩ → γ₁ x = γ₂ x) :
      eBranch b γ₁ = eBranch b γ₂ :=
    maskParity_congr_support _ _ _ 192 le_rfl fun u _ _ ↦
        h (rSrc u) (fun _ ↦ hSrcGat7 u _) (fun _ ↦ hSrcGat7 u _) (hSrcGat7 u _)
  have hMut (δ : BitAssignment n) (_ : ∀ q, δ (rWork q) = 0) (b₁ b₂ : Fin 2) (hne : b₁ ≠ b₂)
      (hb1 : stLoadOf st₀ δ (lW b₁) = 1) : stLoadOf st₀ δ (lW b₂) = 0 := by
    dsimp only [stLoadOf] at hb1 ⊢
    rw [Function.update_of_ne (hUL b₁).symm, findBranch_self hlInj b₁] at hb1
    rw [Function.update_of_ne (hUL b₂).symm, findBranch_self hlInj b₂]
    dsimp only at hb1 ⊢
    have hMB : (bOf (coinFn δ) ((valPairMLs p).getD b₁.val 0) &&
        bOf (coinFn δ) ((valPairMLs p).getD b₂.val 0)) = false := by
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact valPair_mutex (coinFn δ) p b₁.val b₂.val hlt b₂.isLt
      · exact Bool.and_comm _ _ ▸ valPair_mutex (coinFn δ) p b₂.val b₁.val hgt b₁.isLt
    cases h : bOf (coinFn δ) ((valPairMLs p).getD b₁.val 0)
    · exact absurd (h ▸ hb1) zero_ne_one
    · rw [h, Bool.true_and] at hMB
      exact congrArg (fun b : Bool ↦ if b then (1 : ZMod 2) else 0) hMB
  have hG7Out (idx : Fin 7) (hbd : idx.val < 3 ∨ 5 ≤ idx.val) (δ : BitAssignment n)
      (hz : ∀ q, δ (rWork q) = 0) :
      stLoadOf st₀ δ (rGat7 idx) = 0 := by
    dsimp only [stLoadOf]
    rw [Function.update_of_ne (rGat8_7_ne_7Of8 rGat8 idx).symm,
      findBranch_none fun b e ↦
          absurd (congrArg Fin.val (rGat7.wires.injective e)) (by (try dsimp [lW]); omega)]
    exact hGat7Zero δ hz idx
  have heEq (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (b : Fin 2) :
      eBranch b (stLoadOf st₀ δ) = stLoadOf st₀ δ (lW b) := by
    have hSrcL (u : Fin 192) (hn67 : u.val ≠ 67) (hn69 : u.val ≠ 69) :
        stLoadOf st₀ δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0 := by
      dsimp only [stLoadOf]
      rw [Function.update_of_ne (hSrcGat8 u _), findBranch_none fun _ ↦ hSrcGat7 u _,
          hSrcEnv δ hz u hn67 hn69]
    dsimp only [eBranch, stLoadOf]
    rw [env151_maskParity_domZ rSrc (coinFn δ) (stLoadOf st₀ δ) hSrcL _ (dom_valPairMLs p b),
      Function.update_of_ne (hUL b).symm, findBranch_self hlInj b]
  have sSplit := step_pSplitRBracket (by decide : 0 < 2) v rWork uWire lW hW
    (rGat7 ⟨0, by decide⟩) (rGat7 ⟨1, by decide⟩) (rGat7 ⟨2, by decide⟩)
    eBranch hInj heIndep (stLoadOf st₀) (stLoadOf stHOut) (fun _ ↦ 0) (fun _ ↦ 0)
    (.circuit cEH) hMut
    (fun δ hz ↦ ⟨fun b : Fin 2 ↦ hG7Out ⟨5 + b.val, by omega⟩
        (Or.inr (Nat.le_add_right 5 b.val)) δ hz,
      hG7Out _ (Or.inl (by decide)) δ hz, hG7Out _ (Or.inl (by decide)) δ hz,
          hG7Out _ (Or.inl (by decide)) δ hz⟩)
    heEq
    (fun δ _ ↦ by
      have hG7Same (i : Fin 7) : stLoadOf stHOut δ (rGat7 i) = stLoadOf st₀ δ (rGat7 i) := by
        have hiU : rGat7 i ≠ uWire := (rGat8_7_ne_7Of8 rGat8 i).symm
        dsimp only [stLoadOf, stHOut]
        rw [Function.update_of_ne hiU, Function.update_of_ne hiU]
        cases findBranch lW (rGat7 i) with
        | some _ => rfl
        | none => rw [Function.update_of_ne (hGat7O i qHi), Function.update_of_ne (hGat7O i qLo)]
      exact ⟨by
          dsimp only [stLoadOf]
          rw [Function.update_self, Function.update_self],
        fun _ ↦ hG7Same _, fun _ ↦ hG7Same _, hG7Same _, hG7Same _, hG7Same _,
        fun _ ↦ maskParity_congr_support _ _ _ 192 le_rfl fun u _ _ ↦ by
          dsimp only [stLoadOf, stHOut]
          rw [Function.update_of_ne (hSrcGat8 u _), Function.update_of_ne (hSrcGat8 u _),
            findBranch_none (fun _ ↦ hSrcGat7 u _),
            Function.update_of_ne (hSrcO u qHi), Function.update_of_ne (hSrcO u qLo)]⟩)
    (step_circ_mkKetOpW rWork _ _ _ _ cEH hEmitHEq)
  exact PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans
    (PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans
      (step_circ_mkKetOpW rWork _ _ _ _ cLO hLoadEq)
      (Stage1AsymRevEngine.subspaceStep_seq_trans sSplit (step_circ_mkKetOpW rWork _ _ _ _ cLO
          hUnloadEq)))
    (step_circ_mkKetOpW (Var := Var) rWork _ _ _ _ cED
      (mkKetOpW_mul_ket_eq rWork _ _ _ _ fun δ hz ↦
        ket_cEmitValDirect_domZ rSrc214 rO hSrc214O p (coinFn δ) (st₀ δ) (hSrc214Env δ hz)))

def pValPairChainChunk8 {Var : Type} {n : ℕ} (v : Var)
    (rSrc214 : QRegister 214 n) (rSrc : QRegister 192 n)
    (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214 u ≠ rO q)
    (hSrc214Gat8 : ∀ (u : Fin 214) (i : Fin 8), rSrc214 u ≠ rGat8 i)
    (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i)
    (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q) :
    (k : ℕ) → k ≤ 16 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | k + 1, hk =>
      .seq (pValPairChainChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O
              k (Nat.le_of_succ_le hk))
        (pValPairStepChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O ⟨k, hk⟩)

theorem counts_pValPairChainChunk8 {Var : Type} {n : ℕ} (v : Var)
    (rSrc214 : QRegister 214 n) (rSrc : QRegister 192 n)
    (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214 u ≠ rO q)
    (hSrc214Gat8 : ∀ (u : Fin 214) (i : Fin 8), rSrc214 u ≠ rGat8 i)
    (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i)
    (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q) :
    ∀ (k : ℕ) (hk : k ≤ 16),
      (pValPairChainChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O k hk).count
          .T = 6 * k ∧
      (pValPairChainChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O k hk).count
          .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      obtain ⟨t1, f1⟩ :=
          counts_pValPairChainChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O k
          (Nat.le_of_succ_le hk); obtain ⟨t2, f2⟩ :=
          counts_pValPairStepChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O ⟨k,
          hk⟩; dsimp only [pValPairChainChunk8, DynamicCircuit.count]; rw [t1, t2, f1, f2]
      exact ⟨by omega, by omega⟩

theorem dw_pValPairChainChunk8 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rSrc214 : QRegister 214 n) (rSrc : QRegister 192 n)
    (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214 u ≠ rO q)
    (hSrc214Gat8 : ∀ (u : Fin 214) (i : Fin 8), rSrc214 u ≠ rGat8 i)
    (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i)
    (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q)
    (hSrc214 : ∀ u : Fin 214, S (rSrc214 u))
    (hSrc : ∀ u : Fin 192, S (rSrc u))
    (hO : ∀ q : Fin 40, S (rO q))
    (hGat8 : ∀ i : Fin 8, S (rGat8 i)) :
    ∀ (k : ℕ) (hk : k ≤ 16),
      DynWires S (pValPairChainChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O k
          hk)
  | 0, _ => trivial
  | k + 1, hk =>
      ⟨dw_pValPairChainChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O
         hSrc214 hSrc hO hGat8 k (Nat.le_of_succ_le hk),
       dw_pValPairStepChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O
         hSrc214 hSrc hO hGat8 ⟨k, hk⟩⟩

theorem step_pValPairChainChunk8 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n)
    (rSrc214 : QRegister 214 n) (rSrc : QRegister 192 n)
    (rO : QRegister 40 n) (rGat8 : QRegister 8 n)
    (hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214 u ≠ rO q)
    (hSrc214Gat8 : ∀ (u : Fin 214) (i : Fin 8), rSrc214 u ≠ rGat8 i)
    (hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrc u ≠ rGat8 i)
    (hSrcO : ∀ (u : Fin 192) (q : Fin 40), rSrc u ≠ rO q)
    (hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q)
    (coinFn : BitAssignment n → Fin (2 ^ 41))
    (stBase : BitAssignment n → BitAssignment n)
    (hSrcEnv : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin 192, u.val ≠ 67 → u.val ≠ 69 →
      stBase δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0)
    (hSrc214Env : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin 214, u.val ≠ 67 → u.val ≠ 69 →
      stBase δ (rSrc214 u) = if src214Bit (coinFn δ) u then 1 else 0)
    (hGatZero : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ i : Fin 8, stBase δ (rGat8 i) = 0) :
    ∀ (k : ℕ) (hk : k ≤ 16),
      SubspaceStep
        (mkKetOpW rWork stBase (fun _ ↦ 0))
        (mkKetOpW rWork (fun δ ↦ stValChain rO (coinFn δ) (stBase δ) k hk) (fun _ ↦ 0))
        (pValPairChainChunk8 v rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hGat8O k hk)
  | 0, _ => by
      dsimp only [pValPairChainChunk8, stValChain]
      have hId : (Circuit.identity : Circuit n).eval.1 * mkKetOpW rWork stBase (fun _ ↦ 0) =
          mkKetOpW rWork stBase (fun _ ↦ 0) := by
        rw [Circuit.eval_identity]; simp only [Submonoid.coe_one, Matrix.one_mul]
      exact subspaceStep_congr_out
        (subspaceStep_of_circuit (Var := Var) (mkKetOpW rWork stBase (fun _ ↦ 0)) .identity) hId
  | k + 1, hk => by
      have hk0 := Nat.le_of_succ_le hk;
      have sPrev :=
          step_pValPairChainChunk8 v rWork rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hSrcO
          hGat8O coinFn stBase hSrcEnv hSrc214Env hGatZero k hk0
      let stPrev : BitAssignment n → BitAssignment n := fun δ ↦
          stValChain rO (coinFn δ) (stBase δ) k hk0
      have sStep :=
          step_pValPairStepChunk8 v rWork rSrc214 rSrc rO rGat8 hSrc214O hSrc214Gat8 hSrcGat8 hSrcO
          hGat8O coinFn stPrev ⟨k, hk⟩ (fun δ hz u hn67 hn69 ↦ (stValChain_outside_rO rO (coinFn δ)
          (stBase δ) (fun q ↦ hSrcO u q) k hk0).trans (hSrcEnv δ hz u hn67 hn69))
          (fun δ hz u hn67 hn69 ↦ (stValChain_outside_rO rO (coinFn δ) (stBase δ)
          (fun q ↦ hSrc214O u q) k hk0).trans (hSrc214Env δ hz u hn67 hn69))
          (fun δ hz i ↦ (stValChain_outside_rO rO (coinFn δ) (stBase δ)
          (fun q ↦ hGat8O i q) k hk0).trans (hGatZero δ hz i))
      dsimp only [pValPairChainChunk8, stValChain];
      exact Stage1AsymRevEngine.subspaceStep_seq_trans sPrev sStep
def src214DomZWireFn (u : Fin 214) : Wire dLayout :=
  if h1 : u.val < 41 then rOuter41Layout ⟨u.val, h1⟩
  else if u.val = 67 then rScrCompact1493 ⟨179, by decide⟩
  else if u.val = 69 then rScrCompact1493 ⟨180, by decide⟩
  else if h2 : u.val < 204 then rScrCompact1493 ⟨u.val - 41, by omega⟩
  else rScrCompact1493 ⟨165 + (u.val - 204), by have := u.isLt; omega⟩

theorem src214DomZWireFn_ge41_bounds (u : Fin 214) (hu : ¬ u.val < 41) :
    let w := src214DomZWireFn u
    w.val ≤ 5712 ∨ (5755 ≤ w.val ∧ w.val ≤ 7214) := by
  dsimp only [src214DomZWireFn]; rw [_root_.dite_eq_right hu]
  split_ifs <;> (rw [val_rScrCompact1493]; split_ifs <;> omega)

theorem src214DomZWireFn_injective : Function.Injective src214DomZWireFn := fun a b e ↦ by
  have hCross {x y : Fin 214} (hx : x.val < 41) (hy : ¬ y.val < 41)
      (he : src214DomZWireFn x = src214DomZWireFn y) : False := by
    have hyB := src214DomZWireFn_ge41_bounds y hy
    have hv : 7215 + x.val = (src214DomZWireFn y).val := by
      rw [← he]; dsimp only [src214DomZWireFn]; rw [_root_.dite_eq_left hx, val_rOuter41Layout]
    dsimp only at hyB; have := x.isLt; omega
  by_cases ha : a.val < 41 <;> by_cases hb : b.val < 41
  · dsimp only [src214DomZWireFn] at e; rw [_root_.dite_eq_left ha, _root_.dite_eq_left hb] at e
    exact Fin.ext (Fin.mk.inj (rOuter41Layout.wires.injective e))
  · exact (hCross ha hb e).elim
  · exact (hCross hb ha e.symm).elim
  · dsimp only [src214DomZWireFn] at e; rw [_root_.dite_eq_right ha, _root_.dite_eq_right hb] at e
    have haLt := a.isLt; have hbLt := b.isLt
    split_ifs at e
    all_goals
      have hk := congrArg Fin.val (rScrCompact1493.wires.injective e)
      dsimp at hk; exact Fin.ext (by omega)

def rSrc214DomZ : QRegister 214 dLayout := ⟨⟨src214DomZWireFn, src214DomZWireFn_injective⟩⟩

abbrev rSrc192DomZ : QRegister 192 dLayout :=
    rSrc214DomZ.compose (QRegister.block 0 192 (by decide))

theorem rSrc214DomZ_eq_of_ne (u : Fin 214) (h67 : u.val ≠ 67) (h69 : u.val ≠ 69) : rSrc214DomZ u =
    rSrc214 u := by
  change src214DomZWireFn u = src214WireFn u; dsimp only [src214DomZWireFn, src214WireFn]
  by_cases h1 : u.val < 41
  · rw [_root_.dite_eq_left h1, _root_.dite_eq_left h1]
  · rw [_root_.dite_eq_right h1, _root_.dite_eq_right h1, _root_.ite_eq_right h67,
        _root_.ite_eq_right h69]

theorem rSrc192DomZ_eq_of_ne (u : Fin 192) (h67 : u.val ≠ 67) (h69 : u.val ≠ 69) : rSrc192DomZ u =
    rSrc192QromOpt u := by
  have h1 : (QRegister.block 0 192 (by decide) u : Fin 214).val ≠ 67 := by
    dsimp [QRegister.block_apply_val]; omega
  have h2 : (QRegister.block 0 192 (by decide) u : Fin 214).val ≠ 69 := by
    dsimp [QRegister.block_apply_val]; omega
  exact rSrc214DomZ_eq_of_ne _ h1 h2

theorem rSrc214DomZ_67 : rSrc214DomZ ⟨67, by decide⟩ = rAuxScr24 ⟨4, by decide⟩ := by
  change src214DomZWireFn ⟨67, by decide⟩ = rScrCompact1493 ⟨175 + 4, _⟩
  dsimp only [src214DomZWireFn]
  rw [_root_.dite_eq_right (by decide), _root_.ite_eq_left rfl]

theorem rSrc214DomZ_69 : rSrc214DomZ ⟨69, by decide⟩ = rAuxScr24 ⟨5, by decide⟩ := by
  change src214DomZWireFn ⟨69, by decide⟩ = rScrCompact1493 ⟨175 + 5, _⟩
  dsimp only [src214DomZWireFn]
  rw [_root_.dite_eq_right (by decide), _root_.ite_eq_right (by decide), _root_.ite_eq_left rfl]

theorem rSrc214DomZ_ne_rOut40 (u : Fin 214) (q : Fin 40) : rSrc214DomZ u ≠ rOut40Layout q := by
  change src214DomZWireFn u ≠ rOut40Layout q; dsimp only [src214DomZWireFn]; split_ifs
  · exact rOuter41_ne_rOut40 _ q
  all_goals exact rScr_ne_rOut40 _ q

theorem rSrc192DomZ_ne_rOut40 (u : Fin 192) (q : Fin 40) : rSrc192DomZ u ≠ rOut40Layout q :=
    rSrc214DomZ_ne_rOut40 _ q
def preFwdWireFnRtW300 (j : Fin 276) : Wire dLayout :=
  if h1 : j.val < 41 then rOuter41Layout ⟨j.val, h1⟩
  else if h2 : j.val < 180 then rScrCompact1493 ⟨j.val - 41, by omega⟩
  else rScrCompact1493 ⟨197 + (j.val - 180), by have := j.isLt; omega⟩

theorem preFwdWireFnRtW300_ge41_bounds (j : Fin 276) (hj : ¬ j.val < 41) :
    let w := preFwdWireFnRtW300 j
    w.val ≤ 5712 ∨ (5755 ≤ w.val ∧ w.val ≤ 7214) := by
  dsimp only [preFwdWireFnRtW300]; rw [_root_.dite_eq_right hj]
  split_ifs <;> (rw [val_rScrCompact1493]; split_ifs <;> omega)

theorem preFwdWireFnRtW300_injective : Function.Injective preFwdWireFnRtW300 := fun a b e ↦ by
  have hCross {x y : Fin 276} (hx : x.val < 41) (hy : ¬ y.val < 41)
      (he : preFwdWireFnRtW300 x = preFwdWireFnRtW300 y) : False := by
    have hyB := preFwdWireFnRtW300_ge41_bounds y hy
    have hv : 7215 + x.val = (preFwdWireFnRtW300 y).val := by
      rw [← he]; dsimp only [preFwdWireFnRtW300]; rw [_root_.dite_eq_left hx, val_rOuter41Layout]
    dsimp only at hyB; have := x.isLt; omega
  by_cases ha : a.val < 41 <;> by_cases hb : b.val < 41
  · dsimp only [preFwdWireFnRtW300] at e; rw [_root_.dite_eq_left ha, _root_.dite_eq_left hb] at e
    exact Fin.ext (Fin.mk.inj (rOuter41Layout.wires.injective e))
  · exact (hCross ha hb e).elim
  · exact (hCross hb ha e.symm).elim
  · dsimp only [preFwdWireFnRtW300] at e; rw [_root_.dite_eq_right ha, _root_.dite_eq_right hb] at e
    split_ifs at e
    all_goals
      have hk := congrArg Fin.val (rScrCompact1493.wires.injective e)
      dsimp at hk; exact Fin.ext (by omega)

def rPreFwdRtW300 : QRegister 276 dLayout := ⟨⟨preFwdWireFnRtW300, preFwdWireFnRtW300_injective⟩⟩

theorem rPreFwdRtW300_apply (j : Fin 276) : rPreFwdRtW300 j = preFwdWireFnRtW300 j := rfl

theorem rScrCompact1493_eq_rPreFwdRtW300_ge197 (k : ℕ) (hk197 : ¬ k < 197) (hk203 : k < 203)
    {hk1 : k < 1493} {hk2 : 180 + (k - 197) < 276} : rScrCompact1493 ⟨k, hk1⟩ = rPreFwdRtW300 ⟨180 +
    (k - 197), hk2⟩ := by
  have h1 : ¬ 180 + (k - 197) < 41 := by omega
  have h2 : ¬ 180 + (k - 197) < 180 := by omega
  rw [rPreFwdRtW300_apply]; dsimp only [preFwdWireFnRtW300];
  rw [_root_.dite_eq_right h1, _root_.dite_eq_right h2]
  exact congrArg rScrCompact1493 (Fin.ext (by dsimp; omega))

theorem rPreFwdRtW300_active_wIn0 (j : Fin 276) : ActiveLayoutFusedOf 0 (rPreFwdRtW300 j) := by
  change ActiveLayoutFusedOf 0 (preFwdWireFnRtW300 j); dsimp only [preFwdWireFnRtW300]
  split_ifs with h1 h2
  · have hv := val_rOuter41Layout ⟨j.val, h1⟩
    unfold ActiveLayoutFusedOf; omega
  · have hv := val_rScrCompact1493 ⟨j.val - 41, by omega⟩
    dsimp only at hv
    unfold ActiveLayoutFusedOf; rw [hv]; split_ifs <;> omega
  · have := j.isLt
    have hv := val_rScrCompact1493 ⟨197 + (j.val - 180), by omega⟩
    dsimp only at hv
    unfold ActiveLayoutFusedOf; rw [hv]; split_ifs <;> omega

theorem activeStack_rScr_lt293 (gLo : ℕ) {wWork : ℕ} (hw : 300 ≤ wWork) (mCoin_unused : ℕ)
    (m : Fin 1493) (hm : m.val < 293) :
    ActiveOuterCoinStackOf gLo wWork mCoin_unused (rScrCompact1493 m) := by
  have hv := val_rScrCompact1493 m; dsimp only [ActiveOuterCoinStackOf]
  rw [hv]; split_ifs <;> omega

theorem rPreFwdRtW300_activeStack (gLo : ℕ) {wWork mCoin : ℕ} (hw : 300 ≤ wWork) (hm : 39 ≤ mCoin)
    (j : Fin 276) : ActiveOuterCoinStackOf gLo wWork mCoin (rPreFwdRtW300 j) := by
  change ActiveOuterCoinStackOf gLo wWork mCoin (preFwdWireFnRtW300 j);
  dsimp only [preFwdWireFnRtW300]
  split_ifs with h1 h2
  · exact activeStack_rOuter41_sym gLo wWork hm ⟨j.val, h1⟩
  · exact activeStack_rScr_lt293 gLo hw mCoin _ (by dsimp; omega)
  · have := j.isLt
    exact activeStack_rScr_lt293 gLo hw mCoin _ (by dsimp; omega)

theorem rPreFwdRtW300_ne_rOut40 (j : Fin 276) (q : Fin 40) : rPreFwdRtW300 j ≠ rOut40Layout q := by
  change preFwdWireFnRtW300 j ≠ rOut40Layout q; dsimp only [preFwdWireFnRtW300]; split_ifs
  · exact rOuter41_ne_rOut40 _ _
  · exact rScr_ne_rOut40 _ _
  · exact rScr_ne_rOut40 _ _

theorem rW165_activeStack_w300 (gLo : ℕ) {wWork mCoin : ℕ} (hw : 300 ≤ wWork) (hm : 39 ≤ mCoin)
    (j : Fin (81 + (165 + 0))) : ActiveOuterCoinStackOf gLo wWork mCoin (rW165 j) := by
  have hj := j.isLt;
  have hv :=
      val_splitCoinGenWireFn hbLo_165 hbHi_165 j; dsimp only [ActiveOuterCoinStackOf, rW165,
      rSplitCoinGen, DFunLike.coe]
  rw [hv]; split_ifs <;> omega

theorem rAuxOut10_activeStack_w300 (gLo : ℕ) {wWork : ℕ} (hw : 300 ≤ wWork) (mCoin_unused : ℕ)
    (i : Fin 10) : ActiveOuterCoinStackOf gLo wWork mCoin_unused (rAuxOut10 i) := by
  have := i.isLt
  exact activeStack_rScr_lt293 gLo hw mCoin_unused ⟨165 + i.val, by omega⟩ (by dsimp; omega)

theorem rAuxScr24_activeStack_w300 (gLo : ℕ) {wWork : ℕ} (hw : 300 ≤ wWork) (mCoin_unused : ℕ)
    (i : Fin 24) : ActiveOuterCoinStackOf gLo wWork mCoin_unused (rAuxScr24 i) := by
  have := i.isLt
  exact activeStack_rScr_lt293 gLo hw mCoin_unused ⟨175 + i.val, by omega⟩ (by dsimp; omega)

def rRt139L4 : QRegister 4 dLayout :=
  rScrCompact1493.compose (QRegister.block 199 4 (by decide))

theorem rRt139L4_active_wIn0 (i : Fin 4) : ActiveLayoutFusedOf 0 (rRt139L4 i) := by
  have := i.isLt
  have hv := val_rScrCompact1493 ⟨199 + i.val, by omega⟩
  change ActiveLayoutFusedOf 0 (rScrCompact1493 ⟨199 + i.val, _⟩)
  dsimp only at hv; unfold ActiveLayoutFusedOf; rw [hv]; split_ifs <;> omega

theorem rRt139L4_activeStack_w300 (gLo : ℕ) {wWork : ℕ} (hw : 300 ≤ wWork) (mCoin_unused : ℕ)
    (i : Fin 4) : ActiveOuterCoinStackOf gLo wWork mCoin_unused (rRt139L4 i) := by
  have := i.isLt
  exact activeStack_rScr_lt293 gLo hw mCoin_unused ⟨199 + i.val, by omega⟩ (by dsimp; omega)

theorem rSrc192QromOpt_ne_rRt139L4 (u : Fin 192) (b : Fin 4) : rSrc192QromOpt u ≠ rRt139L4 b := by
  change src214WireFn ⟨0 + u.val, _⟩ ≠ rScrCompact1493 ⟨199 + b.val, _⟩; dsimp only [src214WireFn]
  have hu := u.isLt; have hb := b.isLt
  by_cases h1 : 0 + u.val < 41
  · rw [_root_.dite_eq_left h1]; exact rOuter41_ne_rScrIdx_qromOpt _ _
  · rw [_root_.dite_eq_right h1]
    split_ifs <;> exact rScrCompact1493.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))

theorem rSrc192QromOpt_lt180_ne_rCoinInner188 (u : Fin 192) (hu : u.val < 180) :
    rSrc192QromOpt u ≠ rCoinInner 165 rW165 ⟨188, by decide⟩ := fun e ↦ by
  have h1 : rSrc192QromOpt u = rCoinInner 165 rW165 ⟨u.val, by omega⟩ :=
    (rSrc214_lt204_eq_rI ⟨0 + u.val, by omega⟩ (by change 0 + u.val < 204; omega)).trans
      (congrArg (rCoinInner 165 rW165) (Fin.ext (Nat.zero_add u.val)))
  have hk := congrArg Fin.val ((rCoinInner 165 rW165).wires.injective (h1.symm.trans e))
  dsimp at hk; omega

theorem rCoinInner165_ne_rRt139L4 (i : Fin 206) (b : Fin 4) :
    rCoinInner 165 rW165 i ≠ rRt139L4 b := fun e ↦ by
  rw [rCoinInner_rW165_eq i] at e
  split_ifs at e with hi41
  · exact rOuter41_ne_rScrIdx_qromOpt _ _ e
  · have hk := congrArg Fin.val (rScrCompact1493.wires.injective e)
    dsimp [QRegister.block_apply_val] at hk; have := i.isLt; omega

theorem rCoinInner165_ne_rAuxScr24 (i : Fin 206) (a : Fin 24) :
    rCoinInner 165 rW165 i ≠ rAuxScr24 a := fun e ↦ by
  rw [rCoinInner_rW165_eq i] at e
  split_ifs at e with hi41
  · exact rOuter41_ne_rScrIdx_qromOpt _ _ e
  · have hk := congrArg Fin.val (rScrCompact1493.wires.injective e)
    dsimp [QRegister.block_apply_val] at hk; have := i.isLt; omega

theorem rRt139L4_ne_rAuxScr24 (b : Fin 4) (a : Fin 24) : rRt139L4 b ≠ rAuxScr24 a := by
  change rScrCompact1493 ⟨199 + b.val, _⟩ ≠ rScrCompact1493 ⟨175 + a.val, _⟩
  have := b.isLt; have := a.isLt
  exact rScrCompact1493.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))

theorem rRt139L4_ne_rOut40 (b : Fin 4) (q : Fin 40) : rRt139L4 b ≠ rOut40Layout q :=
    rScr_ne_rOut40 _ q
def gatScr8DomZW298WireFn (i : Fin 8) : Wire dLayout :=
  if i.val < 4 then rScrCompact1493 ⟨175 + i.val, by omega⟩
  else if i.val < 6 then rScrCompact1493 ⟨163 + (i.val - 4), by omega⟩
  else if i.val = 6 then rScrCompact1493 ⟨26, by decide⟩
  else rScrCompact1493 ⟨28, by decide⟩

theorem gatScr8DomZW298WireFn_injective : Function.Injective gatScr8DomZW298WireFn := fun a b e ↦ by
  dsimp only [gatScr8DomZW298WireFn] at e
  have ha := a.isLt; have hb := b.isLt
  split_ifs at e <;> (
    have hk := congrArg Fin.val (rScrCompact1493.wires.injective e)
    dsimp at hk; exact Fin.ext (by omega))

def rGatScr8DomZW298 : QRegister 8 dLayout :=
    ⟨⟨gatScr8DomZW298WireFn, gatScr8DomZW298WireFn_injective⟩⟩

theorem rGatScr8DomZW298_active_wIn0 (i : Fin 8) : ActiveLayoutFusedOf 0 (rGatScr8DomZW298 i) := by
  have hScr (m : Fin 1493) (hm : m.val < 293) : ActiveLayoutFusedOf 0 (rScrCompact1493 m) := by
    have hv := val_rScrCompact1493 m
    unfold ActiveLayoutFusedOf; rw [hv]; split_ifs <;> omega
  change ActiveLayoutFusedOf 0 (gatScr8DomZW298WireFn i);
  have := i.isLt; dsimp only [gatScr8DomZW298WireFn]
  split_ifs <;> exact hScr _ (by dsimp; omega)

theorem rGatScr8DomZW298_activeStack_w300 (gLo : ℕ) {wWork : ℕ} (hw : 300 ≤ wWork)
    (mCoin_unused : ℕ)
    (i : Fin 8) : ActiveOuterCoinStackOf gLo wWork mCoin_unused (rGatScr8DomZW298 i) := by
  change ActiveOuterCoinStackOf gLo wWork mCoin_unused (gatScr8DomZW298WireFn i);
  have := i.isLt; dsimp only [gatScr8DomZW298WireFn]
  split_ifs <;> exact activeStack_rScr_lt293 gLo hw mCoin_unused _ (by dsimp; omega)

theorem rSrc214DomZ_ne_rGatScr8DomZW298 (u : Fin 214) (i : Fin 8) : rSrc214DomZ u ≠
    rGatScr8DomZW298 i := by
  change src214DomZWireFn u ≠ gatScr8DomZW298WireFn i;
  dsimp only [src214DomZWireFn, gatScr8DomZW298WireFn]
  have hu := u.isLt; have hi := i.isLt
  by_cases h1 : u.val < 41
  · rw [_root_.dite_eq_left h1]
    split_ifs <;> exact rOuter41_ne_rScrIdx_qromOpt _ _
  · rw [_root_.dite_eq_right h1]
    split_ifs <;> exact rScrCompact1493.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))

theorem rSrc192DomZ_ne_rGatScr8DomZW298 (u : Fin 192) (i : Fin 8) : rSrc192DomZ u ≠
    rGatScr8DomZW298 i := rSrc214DomZ_ne_rGatScr8DomZW298 _ i
theorem rAuxOut10_ne_rGatScr8DomZW298 (b : Fin 10) (i : Fin 8) : rAuxOut10 b ≠
    rGatScr8DomZW298 i := by
  change rScrCompact1493 ⟨165 + b.val, _⟩ ≠ gatScr8DomZW298WireFn i;
  dsimp only [gatScr8DomZW298WireFn]
  have := b.isLt; have := i.isLt
  split_ifs <;> exact rScrCompact1493.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))

theorem rGatScr8DomZW298_ne_rOut40 (i : Fin 8) (q : Fin 40) : rGatScr8DomZW298 i ≠
    rOut40Layout q := by
  change gatScr8DomZW298WireFn i ≠ rOut40Layout q; dsimp only [gatScr8DomZW298WireFn]
  split_ifs <;> exact rScr_ne_rOut40 _ q

theorem rSrc192DomZ_rTot_ne_rGat7DomZW298 {n : ℕ} (rTot : QRegister dLayout n) (u : Fin 192)
    (i : Fin 7) : (rTot.compose rSrc192DomZ) u ≠ rGat7Of8 (rTot.compose rGatScr8DomZW298) i := by
  rw [rGat7Of8_eq]; exact rTot.wires.injective.ne (rSrc192DomZ_ne_rGatScr8DomZW298 u _)
theorem rGat7_rTot_ne_rOut40DomZW298 {n : ℕ} (rTot : QRegister dLayout n) (i : Fin 7)
    (q : Fin 40) : rGat7Of8 (rTot.compose rGatScr8DomZW298) i ≠ (rTot.compose rOut40Layout) q := by
  rw [rGat7Of8_eq]; exact rTot.wires.injective.ne (rGatScr8DomZW298_ne_rOut40 _ q)
def sRangeXag (N k₀ k₁ : ℕ) : Finset (Wire (41 + (N + 2))) :=
    (Finset.univ.filter fun j : Fin N ↦ k₀ ≤ j.val ∧ j.val < k₁).image (wXagGate N)
theorem wXagA_notMem_sRangeXag (N k₀ k₁ : ℕ) : wXagA N ∉ sRangeXag N k₀ k₁ := fun h ↦ by
  rcases Finset.mem_image.mp h with ⟨j, _, e⟩
  exact ne_xag_AG N j e.symm

theorem wXagB_notMem_sRangeXag (N k₀ k₁ : ℕ) : wXagB N ∉ sRangeXag N k₀ k₁ := fun h ↦ by
  rcases Finset.mem_image.mp h with ⟨j, _, e⟩
  exact ne_xag_BG N j e.symm

theorem mem_sRangeXag_self (N k k₁ : ℕ) (hk : k + 1 ≤ N)
    (hlt : k < k₁) : wXagGate N ⟨k, hk⟩ ∈ sRangeXag N k k₁ :=
  Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hlt⟩, rfl⟩

theorem erase_sRangeXag_eq (N k k₁ : ℕ) (hk : k + 1 ≤ N) : (sRangeXag N k k₁).erase (wXagGate N ⟨k,
    hk⟩) = sRangeXag N (k + 1) k₁ := by
  ext u;
  simp only [sRangeXag, Finset.mem_erase, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]; constructor
  · rintro ⟨hne, j, ⟨hkj, hj1⟩, rfl⟩; refine ⟨j, ⟨?_, hj1⟩, rfl⟩
    have hjne : j.val ≠ k := fun e ↦ hne (congrArg (wXagGate N) (Fin.ext e.symm)).symm
    omega
  · rintro ⟨j, ⟨hkj, hj1⟩, rfl⟩
    refine ⟨fun e ↦ ?_, j, ⟨by omega, hj1⟩, rfl⟩
    have hv := congrArg Fin.val e; dsimp [wXagGate] at hv; omega

theorem xagStepProg_range_spec (N k k₁ : ℕ) (hk : k + 1 ≤ N) (hlt : k < k₁)
    (a b : ℕ) : (xagStepProg N k hk a b).numAnd = 1 ∧ ComputeProg.finalClean (sRangeXag N k k₁)
    (xagStepProg N k hk a b) = sRangeXag N (k + 1) k₁ ∧ ComputeProg.ValidProg ∅ (sRangeXag N k k₁)
    (xagStepProg N k hk a b) := by
  let hk0 := Nat.le_of_succ_le hk;
  have nA :=
      numAnd_qXorMask1_zero (rXagPre N k hk0) (wXagA N)
      (disj_pre_A N k hk0) a (41 +
      k) le_rfl; have nB :=
                   numAnd_qXorMask1_zero (rXagPre N k hk0) (wXagB N)
                   (disj_pre_B N k hk0) b (41 + k) le_rfl; obtain ⟨fcA0, vpA0⟩ :=
                   valid_finalClean_qXorMask1 (rXagPre N k hk0) (wXagA N)
                   (disj_pre_A N k hk0) a (sRangeXag N k k₁) (wXagA_notMem_sRangeXag N k k₁)
                   (41 + k) le_rfl; obtain ⟨fcB0, vpB0⟩ :=
                   valid_finalClean_qXorMask1 (rXagPre N k hk0) (wXagB N)
                   (disj_pre_B N k hk0) b (sRangeXag N k k₁) (wXagB_notMem_sRangeXag N k k₁)
                   (41 + k) le_rfl; obtain ⟨fcB1, vpB1⟩ :=
                   valid_finalClean_qXorMask1 (rXagPre N k hk0) (wXagB N)
                   (disj_pre_B N k hk0) b (sRangeXag N (k + 1) k₁)
                   (wXagB_notMem_sRangeXag N (k + 1) k₁) (41 + k) le_rfl; obtain ⟨fcA1, vpA1⟩ :=
                   valid_finalClean_qXorMask1 (rXagPre N k hk0) (wXagA N)
                   (disj_pre_A N k hk0) a (sRangeXag N (k + 1) k₁)
                   (wXagA_notMem_sRangeXag N (k + 1) k₁) (41 + k) le_rfl; dsimp only [xagStepProg,
                   ComputeProg.numAnd, ComputeProg.finalClean, ComputeProg.ValidProg]; rw [nA, nB,
                   fcA0, fcB0, erase_sRangeXag_eq, fcB1, fcA1]; exact ⟨rfl, rfl,
                   ⟨⟨⟨vpA0, vpB0⟩, ⟨Finset.notMem_empty _, Finset.notMem_empty _,
                   Finset.notMem_empty _, mem_sRangeXag_self N k k₁ hk hlt⟩⟩, vpB1⟩, vpA1⟩
theorem compileXagRange_range_spec (N k₀ k₁ : ℕ) (gates : Fin N → ℕ × ℕ) :
    ∀ (d : ℕ) (hd : k₀ + d ≤ N), k₀ + d ≤ k₁ →
      (compileXagRange N k₀ gates d hd).numAnd = d ∧
      ComputeProg.finalClean (sRangeXag N k₀ k₁) (compileXagRange N k₀ gates d hd) =
          sRangeXag N (k₀ + d) k₁ ∧
      ComputeProg.ValidProg ∅ (sRangeXag N k₀ k₁) (compileXagRange N k₀ gates d hd)
  | 0, _, _ => by
      have hk0 : k₀ + 0 = k₀ := Nat.add_zero k₀; rw [hk0]; exact ⟨rfl, rfl, trivial⟩
  | d + 1, hd, hd1 => by
      let hd0 : k₀ + d ≤ N := by omega
      let hk : (k₀ + d) + 1 ≤ N := by omega
      obtain ⟨ihN, ihF, ihV⟩ := compileXagRange_range_spec N k₀ k₁ gates d hd0 (by omega)
      obtain ⟨stN, stF, stV⟩ := xagStepProg_range_spec N (k₀ + d) k₁ hk (by omega)
        (gates ⟨k₀ + d, hk⟩).1 (gates ⟨k₀ + d, hk⟩).2
      dsimp only [compileXagRange, ComputeProg.numAnd, ComputeProg.finalClean,
          ComputeProg.ValidProg]; rw [ihN, stN, ihF, stF]
      have hAdd : (k₀ + d) + 1 = k₀ + (d + 1) := by omega
      rw [hAdd]; exact ⟨rfl, rfl, ihV, stV⟩
theorem fwdBits_compileXagRange_congr (N k₀ : ℕ) (gates : Fin N → ℕ × ℕ)
    (β₁ β₂ : BitAssignment (41 + (N + 2)))
    (hEqLt : ∀ i : Wire (41 + (N + 2)), i.val < 41 + k₀ → β₁ i = β₂ i)
    (hA₁ : β₁ (wXagA N) = 0) (hB₁ : β₁ (wXagB N) = 0)
    (hA₂ : β₂ (wXagA N) = 0) (hB₂ : β₂ (wXagB N) = 0) :
    ∀ (d : ℕ) (hd : k₀ + d ≤ N),
      (∀ (j : ℕ) (hj : j < d), β₁ (wXagGate N ⟨k₀ + j, by omega⟩) = 0) →
      (∀ (j : ℕ) (hj : j < d), β₂ (wXagGate N ⟨k₀ + j, by omega⟩) = 0) →
      (∀ i : Wire (41 + (N + 2)), i.val < 41 + (k₀ + d) →
        (compileXagRange N k₀ gates d hd).fwdBits β₁ i =
          (compileXagRange N k₀ gates d hd).fwdBits β₂ i) ∧
      (∀ i : Wire (41 + (N + 2)), 41 + (k₀ + d) ≤ i.val →
        (compileXagRange N k₀ gates d hd).fwdBits β₁ i = β₁ i ∧
        (compileXagRange N k₀ gates d hd).fwdBits β₂ i = β₂ i)
  | 0, _, _, _ => by
      dsimp only [compileXagRange, ComputeProg.fwdBits]
      exact ⟨fun i hi ↦ hEqLt i (by omega), fun _ _ ↦ ⟨rfl, rfl⟩⟩
  | d + 1, hd, hG₁, hG₂ => by
      let hd0 : k₀ + d ≤ N := by omega
      let hk : (k₀ + d) + 1 ≤ N := by omega
      obtain ⟨ihLt, ihGe⟩ := fwdBits_compileXagRange_congr N k₀ gates β₁ β₂ hEqLt hA₁ hB₁ hA₂ hB₂
        d hd0 (fun j hj ↦ hG₁ j (by omega)) (fun j hj ↦ hG₂ j (by omega))
      let γ₁ := (compileXagRange N k₀ gates d hd0).fwdBits β₁;
      let γ₂ := (compileXagRange N k₀ gates d hd0).fwdBits β₂
      have hγA₁ : γ₁ (wXagA N) = 0 := (ihGe (wXagA N) (by dsimp [wXagA]; omega)).1.trans hA₁
      have hγB₁ : γ₁ (wXagB N) = 0 := (ihGe (wXagB N) (by dsimp [wXagB]; omega)).1.trans hB₁
      have hγA₂ : γ₂ (wXagA N) = 0 := (ihGe (wXagA N) (by dsimp [wXagA]; omega)).2.trans hA₂
      have hγB₂ : γ₂ (wXagB N) = 0 := (ihGe (wXagB N) (by dsimp [wXagB]; omega)).2.trans hB₂
      let wG := wXagGate N ⟨k₀ + d, hk⟩
      have hγG₁ : γ₁ wG = 0 :=
        (ihGe wG (by dsimp [wG, wXagGate]; omega)).1.trans (hG₁ d (Nat.lt_succ_self d))
      have hγG₂ : γ₂ wG = 0 :=
        (ihGe wG (by dsimp [wG, wXagGate]; omega)).2.trans (hG₂ d (Nat.lt_succ_self d))
      let a := (gates ⟨k₀ + d, hk⟩).1;
      let b :=
          (gates ⟨k₀ + d, hk⟩).2; dsimp only [compileXagRange, ComputeProg.fwdBits]; change (∀ i,
          i.val < 41 + (k₀ + (d + 1)) → (xagStepProg N (k₀ + d) hk a b).fwdBits γ₁ i =
          (xagStepProg N (k₀ + d) hk a b).fwdBits γ₂ i) ∧ (∀ i, 41 + (k₀ + (d + 1)) ≤ i.val →
          (xagStepProg N (k₀ + d) hk a b).fwdBits γ₁ i = β₁ i ∧
          (xagStepProg N (k₀ + d) hk a b).fwdBits γ₂ i = β₂ i); rw [fwdBits_xagStepProg N (k₀ +
          d) hk a b γ₁ hγA₁ hγB₁ hγG₁, fwdBits_xagStepProg N (k₀ + d) hk a b γ₂ hγA₂ hγB₂ hγG₂]
      have hPreEq : (fun u : Fin (41 + (k₀ + d)) ↦ γ₁ (rXagPre N (k₀ + d) hd0 u)) =
          (fun u : Fin (41 + (k₀ + d)) ↦ γ₂ (rXagPre N (k₀ + d) hd0 u)) :=
        funext fun u ↦ ihLt _ (by dsimp [rXagPre, QRegister.block]; omega)
      rw [hPreEq]
      refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
      · by_cases hiw : i = wG
        · subst hiw; rw [Function.update_self, Function.update_self]
        · have hvNe : i.val ≠ 41 + (k₀ + d) := fun e ↦ hiw (Fin.ext e)
          rw [Function.update_of_ne hiw, Function.update_of_ne hiw]
          exact ihLt i (by omega)
      · have hiw : i ≠ wG := Fin.ne_of_val_ne (by dsimp [wG, wXagGate]; omega)
        rw [Function.update_of_ne hiw, Function.update_of_ne hiw]
        exact ihGe i (by omega)

def cpFwdTail6 : ComputeProg (41 + (165 + 0)) :=
  compileXagRange 163 140 fgates163 6 (by decide)

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem fgates163_tail6_dom (j : Fin 6) :
    (domKeepMask &&& (fgates163 ⟨140 + j.val, by have := j.isLt; omega⟩).1 ==
      (fgates163 ⟨140 + j.val, by have := j.isLt; omega⟩).1) = true ∧
    (domKeepMask &&& (fgates163 ⟨140 + j.val, by have := j.isLt; omega⟩).2 ==
      (fgates163 ⟨140 + j.val, by have := j.isLt; omega⟩).2) = true := by
  revert j; decide +kernel

/-! ### Part 2: `cXorMaskSrcBdd`, `env151_maskParity180`, & `rt139Spec` -/

def cXorMaskSrcBdd {n : ℕ} (rSrc : QRegister 192 n) (dst : Wire n) (mask : ℕ) :
    (k : ℕ) → k ≤ 192 → (∀ u : Fin 192, u.val < k → rSrc u ≠ dst) → Circuit n
  | 0, _, _ => if mask.testBit 0 then Circuit.X dst else .identity
  | k + 1, hk, hne =>
      let prev :=
          cXorMaskSrcBdd rSrc dst mask k (Nat.le_of_succ_le hk)
          (fun u hu ↦ hne u (Nat.lt_succ_of_lt hu))
      if mask.testBit (1 + k) then
        prev ;;ᶜ Circuit.CNOT (rSrc ⟨k, hk⟩) dst (hne ⟨k, hk⟩ (Nat.lt_succ_self k))
      else prev

theorem count_cXorMaskSrcBdd {n : ℕ} (rSrc : QRegister 192 n) (dst : Wire n) (mask : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ 192) (hne : ∀ u : Fin 192, u.val < k → rSrc u ≠ dst),
      (cXorMaskSrcBdd rSrc dst mask k hk hne).count .T = 0 ∧
      (cXorMaskSrcBdd rSrc dst mask k hk hne).count .TOFF = 0
  | 0, _, _ => by dsimp only [cXorMaskSrcBdd]; split_ifs <;> simp [Circuit.X]
  | k + 1, hk, hne => by
      obtain ⟨ht, hf⟩ :=
          count_cXorMaskSrcBdd rSrc dst mask k (Nat.le_of_succ_le hk)
          (fun u hu ↦ hne u (Nat.lt_succ_of_lt hu))
      dsimp only [cXorMaskSrcBdd]
      split_ifs <;> simp [ht, hf, Circuit.CNOT]

theorem cw_cXorMaskSrcBdd {n : ℕ} {S : Wire n → Prop} (rSrc : QRegister 192 n) (dst : Wire n)
    (hSrc : ∀ u : Fin 192, S (rSrc u)) (hDst : S dst) (mask : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ 192) (hne : ∀ u : Fin 192, u.val < k → rSrc u ≠ dst),
      CircWires S (cXorMaskSrcBdd rSrc dst mask k hk hne)
  | 0, _, _ => by
      dsimp only [cXorMaskSrcBdd]; split_ifs
      · exact cw_1 hDst
      · trivial
  | k + 1, hk, hne => by
      have ih :=
          cw_cXorMaskSrcBdd rSrc dst hSrc hDst mask k (Nat.le_of_succ_le hk)
          (fun u hu ↦ hne u (Nat.lt_succ_of_lt hu))
      dsimp only [cXorMaskSrcBdd]; split_ifs
      · exact ⟨ih, cw_cnot (hSrc ⟨k, hk⟩) hDst⟩
      · exact ih

theorem ket_cXorMaskSrcBdd {n : ℕ} [NeZero (2 ^ n)] (rSrc : QRegister 192 n) (dst : Wire n)
    (mask : ℕ) (γ : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ 192) (hne : ∀ u : Fin 192, u.val < k → rSrc u ≠ dst),
      (cXorMaskSrcBdd rSrc dst mask k hk hne).eval.1.mulVec (ket γ) =
        ket (Function.update γ dst
          (γ dst + maskParity mask (fun u : Fin 192 ↦ γ (rSrc u)) k hk))
  | 0, _, _ => by
      dsimp only [cXorMaskSrcBdd, maskParity]
      cases mask.testBit 0
      · simp only [Bool.false_eq_true, ↓reduceIte, Circuit.eval_identity, Submonoid.coe_one,
            Matrix.one_mulVec, add_zero, Function.update_eq_self]
      · simp only [↓reduceIte, ket_X]
  | k + 1, hk, hne => by
      have ih :=
          ket_cXorMaskSrcBdd rSrc dst mask γ k (Nat.le_of_succ_le hk)
          (fun u hu ↦ hne u (Nat.lt_succ_of_lt hu))
      dsimp only [cXorMaskSrcBdd, maskParity]
      cases mask.testBit (1 + k)
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]; exact ih
      · simp only [↓reduceIte]; rw [eval_seq_mulVec, ih, ket_CNOT]
        apply congrArg ket; funext x
        by_cases hx : x = dst
        · subst hx;
          simp only [Function.update_self, Function.update_of_ne (hne ⟨k, hk⟩
              (Nat.lt_succ_self k))]; ring
        · simp only [Function.update_of_ne hx]

theorem env151_maskParity180 {n : ℕ} (rSrc : QRegister 192 n) (c : Fin (2 ^ 41))
    (γ : BitAssignment n)
    (hγ : ∀ u : Fin 192, u.val < 180 → γ (rSrc u) = if (e151Dom c).testBit (1 +
        u.val) then 1 else 0)
    (mask : ℕ) (hMask : mask < 2 ^ 181) (hDom : (domKeepMask &&& mask == mask) = true) :
    maskParity mask (fun u : Fin 192 ↦ γ (rSrc u)) 180 (by decide) =
      if bOf c mask then 1 else 0 := by
  let envFn : BitAssignment 192 := fun u ↦ if (e151Dom c).testBit (1 + u.val) then 1 else 0
  rw [maskParity_congr_support mask _ envFn 180 (by decide) (fun u hu _ ↦ hγ u hu),
      maskParity_eq_oddBits mask (e151Dom c) envFn
        (e151Dom_bit0 c) (fun _ ↦ rfl) 180 (by decide)]
  have hMaskEq : e151Dom c &&& mask = e151 c &&& mask := by
    dsimp only [e151Dom]; rw [Nat.and_assoc, beq_iff_eq.mp hDom]
  change (if oddBits (e151Dom c &&& mask) 181 then (1 : ZMod 2) else 0) = _
  rw [hMaskEq, ← oddBits_and_eq_of_lt_two_pow hMask (by decide : 181 ≤ 193)]
  rfl

def rt139MU : ℕ := rt147MA ^^^ rt147MB
def rt139MD0 : ℕ := (fgatesAtOpt 139).1
def rt139MD1 : ℕ := (1 ^^^ rt147MB) ^^^ rt147ML2
def rt139MD2 : ℕ := (rt147MB ^^^ (1 <<< 151)) ^^^ (fgatesAtOpt 139).1
def rt139MD3 : ℕ := rt147ML2
def rt139MY2 : ℕ := rt147MB ^^^ (1 <<< 151)

def rt139MPairsC : List (ℕ × ℕ) := [(1 <<< 155, 1 <<< 66)]
def rt139CPairsC : List ((Bool × ℕ) × (Bool × ℕ)) := [((false, 0x80000), (false, 0x20000))]

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem rt139ReconC_ok : checkDisjPairsRecon151 rt147BasisC rt147ExpC rt139MPairsC rt139CPairsC =
    true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- finite certificate kernel reduction
theorem rt139VecC_ok :
    checkDisjPairsVec151 rt147BasisC.length rt147ExpC.length rt147GcsC rt139CPairsC = true := by
  decide +kernel
theorem rt139DisjC (c : Fin (2 ^ 41)) (i : ℕ) (hi : i < rt139MPairsC.length) :
    (bOf c (rt139MPairsC.getD i (0, 0)).1 && bOf c (rt139MPairsC.getD i (0, 0)).2) = false :=
    disjPairs151_of_cert rt147CertC_ok rt139ReconC_ok rt139VecC_ok c i hi
def rt139MPairsE : List (ℕ × ℕ) :=
    [(1 ^^^ rt147MB0, (fgatesAtOpt 109).2), (1 ^^^ (fgatesAtOpt 112).2,
    rt147MS ^^^ (fgatesAtOpt 139).2)]
def rt139CPairsE : List ((Bool × ℕ) × (Bool × ℕ)) :=
    [((true, 0x748e808), (true, 0x800)), ((true, 0x42008), (false, 0x118000000))]
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem rt139ReconE_ok : checkDisjPairsRecon151 rt147BasisE rt147ExpE rt139MPairsE rt139CPairsE =
    true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- finite certificate kernel reduction
theorem rt139VecE_ok :
    checkDisjPairsVec151 rt147BasisE.length rt147ExpE.length rt147GcsE rt139CPairsE = true := by
  decide +kernel
theorem rt139DisjE (c : Fin (2 ^ 41)) (i : ℕ) (hi : i < rt139MPairsE.length) :
    (bOf c (rt139MPairsE.getD i (0, 0)).1 && bOf c (rt139MPairsE.getD i (0, 0)).2) = false :=
    disjPairs151_of_cert rt147CertE_ok rt139ReconE_ok rt139VecE_ok c i hi
def rt139Steps113 : List (ℕ × Bool × ℕ) :=
    [(114, false, 0x1), (115, false, 0x3), (116, false, 0x2), (121, true, 0x8)]
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem rt139Chain_ok : xorSublist (dominoFinalZs rt147InitZs1 rt147Steps1) 0xf0 =
    (fgatesAtOpt 139).1 ∧ xorSublist (dominoFinalZs rt147InitZs3 rt147Steps3) 0x870000 =
    (fgatesAtOpt 139).1 ∧ checkDominoSteps fgatesAtOpt [1 <<< 155] rt139Steps113 = true ∧
    xorSublist (dominoFinalZs [1 <<< 155] rt139Steps113) 0x1e = (fgatesAtOpt 139).1 ∧
    (fgatesAtOpt 112).1 = (1 <<< 153) ∧ (fgatesAtOpt 113).1 = ((1 <<< 153) ^^^ (1 <<< 154)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem rt139_bool_taut (w66 w151 w162 bL2 bB0 bS bX b139l b139r : Bool) :
    ((w66 = false → w151 = false) →
     (w162 = false → bL2 = false) →
     (w162 = true → bB0 = true ∧ w66 = false ∧ w151 = false ∧ bX = false ∧ b139l = false) →
     (bB0 = false → w151 = false ∧ w162 = false ∧ bL2 = false ∧ bS = false ∧ bX = false ∧ b139l =
         false) →
     (b139l = true → w66 = false ∧ bS = b139r) →
     let bB := xor bB0 w162; let bA := xor (xor true w66) bS; let w181 := b139l && b139r;
     let w188 := xor (xor bA bB) bX && xor bA bX; let bL1 := xor (xor bA w151) w188;
     let bU2 := xor (xor bB w151) w188; let w189 := bL1 && bU2;
     let l148 := xor (xor (xor (xor (xor true bS) w151) bL2) w188) w189;
     let r148 := xor (xor (xor bS w151) w162) w189; let w190 := l148 && r148; let u := xor bA bB;
     let d0 := b139l; let d1 := xor (xor true bB) bL2; let d2 := xor (xor bB w151) b139l;
     let d3 := bL2; let y2 := xor bB w151
     (d0 && d1) = false ∧ (d0 && d2) = false ∧ (d0 && d3) = false ∧
     (d1 && d2) = false ∧ (d1 && d3) = false ∧ (d2 && d3) = false ∧
     w181 = (d0 && u) ∧
     w188 = xor (d1 && u) (d3 && u) ∧
     w189 = xor (xor (d2 && u) (d0 && u)) y2 ∧
     w190 = (d3 && u)) := by
  intro hw151_of_w66 hbL2_of_w162 hC1 hC3 hC139; dsimp only
  cases bB0
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hC3 rfl
    cases w66 <;> cases b139r <;> decide
  · cases w162
    · obtain rfl := hbL2_of_w162 rfl
      cases b139l
      · cases w66 <;> cases w151 <;> cases bS <;> cases bX <;> cases b139r <;> decide
      · obtain ⟨rfl, rfl⟩ := hC139 rfl; obtain rfl := hw151_of_w66 rfl
        cases bS <;> cases bX <;> decide
    · obtain ⟨_, rfl, rfl, rfl, rfl⟩ := hC1 rfl
      cases bL2 <;> cases bS <;> cases b139r <;> decide

def rt139MDOf (b : Fin 4) : ℕ :=
    if b.val = 0 then rt139MD0 else if b.val = 1 then rt139MD1 else if b.val =
    2 then rt139MD2 else rt139MD3
set_option maxHeartbeats 1600000 in
-- finite certificate kernel reduction
theorem rt139Spec (c : Fin (2 ^ 41)) : (∀ b₁ b₂ : Fin 4, b₁ ≠ b₂ → (bOf c (rt139MDOf b₁) &&
    bOf c (rt139MDOf b₂)) = false) ∧ (e151 c).testBit 181 = (bOf c rt139MD0 && bOf c rt139MU) ∧
    (e151 c).testBit 188 = xor (bOf c rt139MD1 && bOf c rt139MU) (bOf c rt139MD3 && bOf c rt139MU) ∧
    (e151 c).testBit 189 = xor (xor (bOf c rt139MD2 && bOf c rt139MU)
    (bOf c rt139MD0 && bOf c rt139MU)) (bOf c rt139MY2) ∧ (e151 c).testBit 190 = (bOf c rt139MD3 &&
    bOf c rt139MU) := by
  obtain ⟨idMB, idMA, id109, id122, id123, idML2, id146, idML1, idMU, id147, id148⟩ :=
      rt147_mask_identities; obtain ⟨hc1_139, hc3_139, hDom113, hc113_139, id112, id113⟩ :=
      rt139Chain_ok; let w66 := bOf c (1 <<< 66); let w151 :=
                                                    bOf c (1 <<<
                                                    151); let w162 :=
                                                            bOf c (1 <<<
                                                            162);
                                                            let bL2 :=
                                                            bOf c rt147ML2;
                                                            let bB0 :=
                                                            bOf c rt147MB0;
                                                            let bS :=
                                                            bOf c rt147MS;
                                                            let bX :=
                                                            bOf c rt147MX;
                                                            let b139l :=
                                                            bOf c (fgatesAtOpt 139).1;
                                                            let b139r := bOf c (fgatesAtOpt 139).2
  have hw151_of_w66 (h0 : w66 = false) : w151 = false := by
    have hg : w151 = _ := bOf_gate_bit c 109 (by decide)
    rw [hg, id109]
    change (w66 && _) = false
    rw [h0, Bool.false_and]
  have hbL2_of_w162 (h0 : w162 = false) : bL2 = false := by
    dsimp only [bL2]
    have hg122 : bOf c (1 <<< 164) = _ := bOf_gate_bit c 122 (by decide)
    have hg123 : bOf c (1 <<< 165) = _ := bOf_gate_bit c 123 (by decide)
    rw [idML2, bOf_xor, hg122, hg123, id122, id123]
    change xor (w162 && _) (w162 && _) = false
    rw [h0]
    rfl
  have hC1 (hw : w162 = true) : bB0 = true ∧ w66 = false ∧ w151 = false ∧ bX = false ∧ b139l =
      false := by
    have dB0 := rt147DisjB c 0 (by decide)
    have dB1 := rt147DisjB c 1 (by decide)
    have dC0 := rt147DisjC c 0 (by decide)
    have dC1 := rt147DisjC c 1 (by decide)
    rw [show rt147MPairsB.getD 0 (0, 0) = (1 <<< 162, rt147MB) by decide +kernel] at dB0
    rw [show (rt147MPairsB.getD 1 (0, 0)).1 = (1 <<< 162) by decide +kernel] at dB1
    rw [show (rt147MPairsC.getD 0 (0, 0)).1 = (1 <<< 162) by decide +kernel] at dC0
    rw [show (rt147MPairsC.getD 1 (0, 0)).1 = (1 <<< 162) by decide +kernel] at dC1
    change (w162 && bOf c rt147MB) = false at dB0
    change (w162 && _) = false at dB1
    change (w162 && _) = false at dC0
    change (w162 && _) = false at dC1
    rw [hw, Bool.true_and] at dB0 dB1 dC0 dC1
    have hbB0_true : bB0 = true := by
      rw [idMB, bOf_xor] at dB0
      change xor bB0 w162 = false at dB0
      rw [hw] at dB0
      dsimp only [bB0] at dB0 ⊢
      cases h : bOf c rt147MB0 <;> first | rfl | exact absurd (h ▸ dB0) Bool.noConfusion
    have hzInit1 : ∀ z ∈ rt147InitZs1, bOf c z = false := by
      rintro z (_ | ⟨_, _ | ⟨_, hz2⟩⟩)
      · exact dB1
      · exact dC0
      · exact List.mem_singleton.mp hz2 ▸ dC1
    obtain ⟨hDom1, hc66, hc151, hcMX⟩ := rt147Chain1_ok
    have hzFin1 := dominoSteps_zero c rt147InitZs1 rt147Steps1 hDom1 hzInit1
    have subZ {m s} (heq : xorSublist (dominoFinalZs rt147InitZs1 rt147Steps1) s = m) : bOf c m =
        false :=
      heq ▸ bOf_xorSublist_false c _ _ hzFin1
    exact ⟨hbB0_true, subZ hc66, subZ hc151, subZ hcMX, subZ hc1_139⟩
  have hC3 (hb0 : bB0 = false) :
      w151 = false ∧ w162 = false ∧ bL2 = false ∧ bS = false ∧ bX = false ∧ b139l = false := by
    have hm1_true : bOf c (1 ^^^ rt147MB0) = true := by
      rw [bOf_xor, bOf_one]
      change xor true bB0 = true
      rw [hb0]
      rfl
    have dE0 := rt139DisjE c 0 (by decide)
    change (bOf c (1 ^^^ rt147MB0) && bOf c (fgatesAtOpt 109).2) = false at dE0
    rw [hm1_true, Bool.true_and] at dE0
    have hw151_z : w151 = false := by
      have hg : w151 = _ := bOf_gate_bit c 109 (by decide)
      rw [hg, dE0, Bool.and_false]
    have hPairE1 : ∀ i : Fin 10, (rt147MPairsE.getD i.val (0, 0)).1 = 1 ^^^ rt147MB0 := by
      decide +kernel
    have hMemInit : ∀ z ∈ rt147InitZs3, z = rt147MB0 ∨
        ∃ i : Fin 10, z = (rt147MPairsE.getD i.val (0, 0)).2 := by decide +kernel
    have hzInit3 : ∀ z ∈ rt147InitZs3, bOf c z = false := fun z hz ↦ by
      rcases hMemInit z hz with rfl | ⟨i, rfl⟩
      · exact hb0
      · have hd := rt147DisjE c i.val (Nat.lt_of_lt_of_eq i.isLt rfl)
        rw [hPairE1 i, hm1_true, Bool.true_and] at hd
        exact hd
    obtain ⟨hDom3, hc162, hcML2, hcS, hcMX⟩ := rt147Chain3_ok
    have hzFin3 := dominoSteps_zero c rt147InitZs3 rt147Steps3 hDom3 hzInit3
    have subZ3 {m s} (heq : xorSublist (dominoFinalZs rt147InitZs3 rt147Steps3) s = m) : bOf c m =
        false :=
      heq ▸ bOf_xorSublist_false c _ _ hzFin3
    exact ⟨hw151_z, subZ3 hc162, subZ3 hcML2, subZ3 hcS, subZ3 hcMX, subZ3 hc3_139⟩
  have hC139 (hb139 : b139l = true) : w66 = false ∧ bS = b139r := by
    have hw155 : bOf c (1 <<< 155) = true := by
      cases h55 : bOf c (1 <<< 155)
      · have hzFin :=
            dominoSteps_zero c [1 <<< 155] rt139Steps113 hDom113 (fun _ hz ↦
            List.mem_singleton.mp hz ▸ h55)
        exact absurd (hb139.symm.trans (hc113_139 ▸ bOf_xorSublist_false c _ _ hzFin))
            Bool.noConfusion
      · rfl
    have dC := rt139DisjC c 0 (by decide)
    change (bOf c (1 <<< 155) && w66) = false at dC
    rw [hw155, Bool.true_and] at dC
    have hg113 : bOf c (1 <<< 155) = _ := bOf_gate_bit c 113 (by decide)
    rw [hw155] at hg113
    have hl113 : bOf c (fgatesAtOpt 113).1 = true := (Bool.and_eq_true_iff.mp hg113.symm).1
    have hr112_false : bOf c (fgatesAtOpt 112).2 = false := by
      cases hr : bOf c (fgatesAtOpt 112).2
      · rfl
      · have hg112 : bOf c (1 <<< 154) = _ := bOf_gate_bit c 112 (by decide)
        rw [id112, hr, Bool.and_true] at hg112
        rw [id113, bOf_xor, hg112] at hl113
        generalize bOf c (1 <<< 153) = b53 at hl113
        cases b53 <;> cases hl113
    have hm112_true : bOf c (1 ^^^ (fgatesAtOpt 112).2) = true := by
      rw [bOf_xor, bOf_one, hr112_false]
      rfl
    have dE1 := rt139DisjE c 1 (by decide)
    change (bOf c (1 ^^^ (fgatesAtOpt 112).2) && bOf c (rt147MS ^^^ (fgatesAtOpt 139).2)) =
        false at dE1
    rw [hm112_true, Bool.true_and, bOf_xor] at dE1
    dsimp only [bS, b139r] at dE1 ⊢
    refine ⟨dC, ?_⟩
    cases hbS : bOf c rt147MS <;> cases hbR : bOf c (fgatesAtOpt 139).2 <;>
      first | rfl | exact absurd (hbR ▸ hbS ▸ dE1) Bool.noConfusion
  obtain ⟨m01, m02, m03, m12, m13, m23, eq181, eq188, eq189, eq190⟩ :=
    rt139_bool_taut w66 w151 w162 bL2 bB0 bS bX b139l b139r hw151_of_w66 hbL2_of_w162 hC1 hC3 hC139
  have hbB_eq : bOf c rt147MB = xor bB0 w162 := by rw [idMB, bOf_xor]
  have hbA_eq : bOf c rt147MA = xor (xor true w66) bS := by rw [idMA, bOf_xor, bOf_xor, bOf_one]
  have hu_eq : bOf c rt139MU = xor (bOf c rt147MA) (bOf c rt147MB) := bOf_xor c _ _
  have hd0_eq : bOf c rt139MD0 = b139l := rfl
  have hd1_eq : bOf c rt139MD1 = xor (xor true (bOf c rt147MB)) bL2 := by
    simp only [rt139MD1, bOf_xor, bOf_one]; rfl
  have hd2_eq : bOf c rt139MD2 = xor (xor (bOf c rt147MB) w151) b139l := by
    simp only [rt139MD2, bOf_xor]; rfl
  have hd3_eq : bOf c rt139MD3 = bL2 := rfl
  have hy2_eq : bOf c rt139MY2 = xor (bOf c rt147MB) w151 := bOf_xor c _ _
  have hw188_eq : bOf c (1 <<< 188) = (xor (xor (bOf c rt147MA) (bOf c rt147MB)) bX &&
      xor (bOf c rt147MA) bX) := by
    have hg : bOf c (1 <<< 188) = _ := bOf_gate_bit c 146 (by decide)
    rw [hg, id146, bOf_xor, bOf_xor, bOf_xor]
  have hbL1_eq : bOf c rt147ML1 = xor (xor (bOf c rt147MA) w151) (bOf c (1 <<< 188)) := by
    rw [idML1, bOf_xor, bOf_xor]
  have hbU2_eq : bOf c rt147MU = xor (xor (bOf c rt147MB) w151) (bOf c (1 <<< 188)) := by
    rw [idMU, bOf_xor, bOf_xor]
  have hw189_eq : bOf c (1 <<< 189) = (bOf c rt147ML1 && bOf c rt147MU) :=
    (bOf_gate_bit c 147 (by decide)).trans (by rw [id147])
  have hw190_eq : bOf c (1 <<< 190) =
      (xor (xor (xor (xor (xor true bS) w151) bL2) (bOf c (1 <<< 188))) (bOf c (1 <<< 189)) &&
       xor (xor (xor bS w151) w162) (bOf c (1 <<< 189))) := by
    have hg : bOf c (1 <<< 190) = _ := bOf_gate_bit c 148 (by decide)
    simp only [hg, id148, bOf_xor, bOf_one]; rfl
  have hwBit (k : ℕ) (hk : k < 193 := by decide) : (e151 c).testBit k = bOf c (1 <<< k) :=
    (oddBits_single_bit (e151 c) k 193 hk).symm
  refine ⟨fun b₁ b₂ hne ↦ ?_, ?_, ?_, ?_, ?_⟩
  · have hLt (a b : Fin 4) (hab : a.val < b.val) : (bOf c (rt139MDOf a) && bOf c (rt139MDOf b)) =
        false := by
      fin_cases a <;> fin_cases b <;> dsimp [rt139MDOf]
      all_goals try exact absurd hab (by decide)
      all_goals simp only [hd0_eq, hd1_eq, hd2_eq, hd3_eq, hbB_eq, m01, m02, m03, m12, m13, m23]
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact hLt b₁ b₂ h
    · exact Bool.and_comm _ _ ▸ hLt b₂ b₁ h
  · rw [hwBit 181, show bOf c (1 <<< 181) = (b139l && b139r) from bOf_gate_bit c 139 (by decide),
      hd0_eq, hu_eq, hbA_eq, hbB_eq]
    exact eq181
  · rw [hwBit 188, hw188_eq, hd1_eq, hd3_eq, hu_eq, hbA_eq, hbB_eq]
    exact eq188
  · rw [hwBit 189, hw189_eq, hbL1_eq, hbU2_eq, hw188_eq, hd2_eq, hd0_eq, hy2_eq, hu_eq, hbA_eq,
        hbB_eq]
    exact eq189
  · rw [hwBit 190, hw190_eq, hw189_eq, hbL1_eq, hbU2_eq, hw188_eq, hd3_eq, hu_eq, hbA_eq, hbB_eq]
    exact eq190
/-! ### Part 3: `wrapTail139Router4` (`R = 4`, `10 T`, `0 .TOFF`) -/

def rt139HIdx (b : Fin 4) : Fin 206 :=
  if b.val = 0 then ⟨180, by decide⟩
  else if b.val = 1 then ⟨187, by decide⟩
  else if b.val = 2 then ⟨188, by decide⟩
  else ⟨189, by decide⟩

theorem rt139HIdx_injective : Function.Injective rt139HIdx := by decide

theorem rt139RouterInj {n : ℕ} (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
    (rAuxScr : QRegister 24 n)
    (hIRtL4 : ∀ (i : Fin 206) (b : Fin 4), rI i ≠ rRtL4 b)
    (hIScr : ∀ (i : Fin 206) (a : Fin 24), rI i ≠ rAuxScr a)
    (hRtL4Scr : ∀ (b : Fin 4) (a : Fin 24), rRtL4 b ≠ rAuxScr a) :
    WOptInj 4 1 (fun _ : Fin 1 ↦ rAuxScr ⟨0, by decide⟩)
      (wPairR (fun b : Fin 4 ↦ rRtL4 b) (fun b : Fin 4 ↦ rI (rt139HIdx b)))
      (rAuxScr ⟨1, by decide⟩) (rAuxScr ⟨2, by decide⟩) (rAuxScr ⟨3, by decide⟩) :=
  have neS : ∀ {a b : Fin 24}, a ≠ b → rAuxScr a ≠ rAuxScr b := rAuxScr.wires.injective.ne
  mkRouterInj1 _ _ _ _ _ _ rRtL4.wires.injective (rI.wires.injective.comp rt139HIdx_injective)
    (fun a b ↦ (hIRtL4 _ a).symm) (fun b ↦ (hRtL4Scr b _).symm) (fun _ ↦ (hIScr _ _).symm)
    (fun b ↦ ⟨hRtL4Scr b _, hRtL4Scr b _, hRtL4Scr b _⟩) (fun _ ↦ ⟨hIScr _ _, hIScr _ _, hIScr _ _⟩)
    ⟨neS (by decide), neS (by decide), neS (by decide)⟩
        ⟨neS (by decide), neS (by decide), neS (by decide)⟩

def cRt139OuterLoad {n : ℕ} (rSrc : QRegister 192 n) (rRtL4 : QRegister 4 n)
    (rAuxScr : QRegister 24 n) (hSrcRtL4 : ∀ (u : Fin 192) (b : Fin 4), rSrc u ≠ rRtL4 b)
    (hSrcScr : ∀ (u : Fin 192) (i : Fin 24), rSrc u ≠ rAuxScr i) : Circuit n :=
  ((((cXorMaskSrc192 rSrc (rRtL4 0) (fun u ↦ hSrcRtL4 u 0) rt139MD0 180 (by decide) ;;ᶜ
      cXorMaskSrc192 rSrc (rRtL4 1) (fun u ↦ hSrcRtL4 u 1) rt139MD1 180 (by decide)) ;;ᶜ
     cXorMaskSrc192 rSrc (rRtL4 2) (fun u ↦ hSrcRtL4 u 2) rt139MD2 180 (by decide)) ;;ᶜ
    cXorMaskSrc192 rSrc (rRtL4 3) (fun u ↦ hSrcRtL4 u 3) rt139MD3 180 (by decide)) ;;ᶜ
   cXorMaskSrc192 rSrc (rAuxScr ⟨0, by decide⟩)
       (fun u ↦ hSrcScr u ⟨0, by decide⟩) rt139MU 180 (by decide))

def cRt139InnerEnter {n : ℕ} (rSrc : QRegister 192 n) (rI : QRegister 206 n)
    (rAuxScr : QRegister 24 n)
    (hSrcI188 : ∀ u : Fin 192, u.val < 180 → rSrc u ≠ rI ⟨188, by decide⟩)
    (hSrcScr : ∀ (u : Fin 192) (i : Fin 24), rSrc u ≠ rAuxScr i) : Circuit n :=
  let hNe89_87 : rI ⟨189, by decide⟩ ≠ rI ⟨187, by decide⟩ := rI.wires.injective.ne (by decide)
  let hNe80_88 : rI ⟨180, by decide⟩ ≠ rI ⟨188, by decide⟩ := rI.wires.injective.ne (by decide)
  (((Circuit.CNOT (rI ⟨189, by decide⟩) (rI ⟨187, by decide⟩) hNe89_87 ;;ᶜ
     Circuit.CNOT (rI ⟨180, by decide⟩) (rI ⟨188, by decide⟩) hNe80_88) ;;ᶜ
    cXorMaskSrcBdd rSrc (rI ⟨188, by decide⟩) rt139MY2 180 (by decide) hSrcI188) ;;ᶜ
   cXorMaskSrc192 rSrc (rAuxScr ⟨0, by decide⟩)
       (fun u ↦ hSrcScr u ⟨0, by decide⟩) rt139MU 180 (by decide))

def wrapTail139Router4 {Var : Type} {n : ℕ} (v : Var)
    (rSrc : QRegister 192 n) (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
        (rAuxScr : QRegister 24 n)
    (hSrcI188 : ∀ u : Fin 192, u.val < 180 → rSrc u ≠ rI ⟨188, by decide⟩)
    (hSrcRtL4 : ∀ (u : Fin 192) (b : Fin 4), rSrc u ≠ rRtL4 b)
    (hSrcScr : ∀ (u : Fin 192) (i : Fin 24), rSrc u ≠ rAuxScr i)
    (hIRtL4 : ∀ (i : Fin 206) (b : Fin 4), rI i ≠ rRtL4 b)
    (hIScr : ∀ (i : Fin 206) (a : Fin 24), rI i ≠ rAuxScr a)
    (hRtL4Scr : ∀ (b : Fin 4) (a : Fin 24), rRtL4 b ≠ rAuxScr a)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let uWire := rAuxScr ⟨0, by decide⟩
  let lW : Fin 4 → Wire n := fun b ↦ rRtL4 b
  let hW : Fin 4 → Wire n := fun b ↦ rI (rt139HIdx b)
  let hInj := rt139RouterInj rI rRtL4 rAuxScr hIRtL4 hIScr hRtL4Scr;
  let cOL := cRt139OuterLoad rSrc rRtL4 rAuxScr hSrcRtL4 hSrcScr;
  let cIE := cRt139InnerEnter rSrc rI rAuxScr hSrcI188 hSrcScr;
  let inner := DynamicCircuit.seq (.circuit cIE) (DynamicCircuit.seq mid (.circuit cIE))
  DynamicCircuit.seq (.circuit cOL)
    (DynamicCircuit.seq
      (pSplitRBracket v uWire lW hW (rAuxScr ⟨1, by decide⟩) (rAuxScr ⟨2, by decide⟩)
        (rAuxScr ⟨3, by decide⟩) hInj inner)
      (.circuit cOL))

theorem counts_wrapTail139Router4 {Var : Type} {n : ℕ} (v : Var)
    (rSrc : QRegister 192 n) (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
        (rAuxScr : QRegister 24 n)
    (hSrcI188 : ∀ u : Fin 192, u.val < 180 → rSrc u ≠ rI ⟨188, by decide⟩)
    (hSrcRtL4 : ∀ (u : Fin 192) (b : Fin 4), rSrc u ≠ rRtL4 b)
    (hSrcScr : ∀ (u : Fin 192) (i : Fin 24), rSrc u ≠ rAuxScr i)
    (hIRtL4 : ∀ (i : Fin 206) (b : Fin 4), rI i ≠ rRtL4 b)
    (hIScr : ∀ (i : Fin 206) (a : Fin 24), rI i ≠ rAuxScr a)
    (hRtL4Scr : ∀ (b : Fin 4) (a : Fin 24), rRtL4 b ≠ rAuxScr a)
    (mid : DynamicCircuit Var n) :
    (wrapTail139Router4 v rSrc rI rRtL4 rAuxScr hSrcI188 hSrcRtL4 hSrcScr hIRtL4 hIScr hRtL4Scr
        mid).count .T =
      10 + mid.count .T ∧
    (wrapTail139Router4 v rSrc rI rRtL4 rAuxScr hSrcI188 hSrcRtL4 hSrcScr hIRtL4 hIScr hRtL4Scr
        mid).count .TOFF =
      mid.count .TOFF := by
  have hcT (w1 w2 : Wire n) (h : w1 ≠ w2) : (Circuit.CNOT w1 w2 h).count .T = 0 := rfl;
  have hcF (w1 w2 : Wire n) (h : w1 ≠ w2) : (Circuit.CNOT w1 w2 h).count .TOFF = 0 := rfl
  obtain ⟨t0, f0⟩ := count_cXorMaskSrc192 rSrc _ (fun u ↦ hSrcRtL4 u 0) rt139MD0 180 (by decide)
  obtain ⟨t1, f1⟩ := count_cXorMaskSrc192 rSrc _ (fun u ↦ hSrcRtL4 u 1) rt139MD1 180 (by decide)
  obtain ⟨t2, f2⟩ := count_cXorMaskSrc192 rSrc _ (fun u ↦ hSrcRtL4 u 2) rt139MD2 180 (by decide)
  obtain ⟨t3, f3⟩ := count_cXorMaskSrc192 rSrc _ (fun u ↦ hSrcRtL4 u 3) rt139MD3 180 (by decide)
  obtain ⟨tu, fu⟩ :=
      count_cXorMaskSrc192 rSrc _ (fun u ↦ hSrcScr u ⟨0, by decide⟩) rt139MU 180 (by decide)
  obtain ⟨ty, fy⟩ :=
      count_cXorMaskSrcBdd rSrc (rI ⟨188, by decide⟩) rt139MY2 180 (by decide) hSrcI188
  let cIE := cRt139InnerEnter rSrc rI rAuxScr hSrcI188 hSrcScr;
  let inner := DynamicCircuit.seq (.circuit cIE) (DynamicCircuit.seq mid (.circuit cIE))
  obtain ⟨tB, fB⟩ := counts_pSplitRBracket v (rAuxScr ⟨0, by decide⟩)
    (fun b : Fin 4 ↦ rRtL4 b) (fun b : Fin 4 ↦ rI (rt139HIdx b))
    (rAuxScr ⟨1, by decide⟩) (rAuxScr ⟨2, by decide⟩) (rAuxScr ⟨3, by decide⟩)
    (rt139RouterInj rI rRtL4 rAuxScr hIRtL4 hIScr hRtL4Scr) inner
  dsimp only [wrapTail139Router4, cRt139OuterLoad, cRt139InnerEnter, inner, cIE,
      DynamicCircuit.count] at tB fB ⊢
  repeat rw [Circuit.count_seq] at tB
  repeat rw [Circuit.count_seq] at fB
  repeat rw [Circuit.count_seq]
  rw [t0, t1, t2, t3, tu, f0, f1, f2, f3, fu, tB, fB]; simp only [hcT, hcF, ty, fy]
  exact ⟨by omega, by omega⟩

theorem dw_wrapTail139Router4 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rSrc : QRegister 192 n) (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
        (rAuxScr : QRegister 24 n)
    (hSrcI188 : ∀ u : Fin 192, u.val < 180 → rSrc u ≠ rI ⟨188, by decide⟩)
    (hSrcRtL4 : ∀ (u : Fin 192) (b : Fin 4), rSrc u ≠ rRtL4 b)
    (hSrcScr : ∀ (u : Fin 192) (i : Fin 24), rSrc u ≠ rAuxScr i)
    (hIRtL4 : ∀ (i : Fin 206) (b : Fin 4), rI i ≠ rRtL4 b)
    (hIScr : ∀ (i : Fin 206) (a : Fin 24), rI i ≠ rAuxScr a)
    (hRtL4Scr : ∀ (b : Fin 4) (a : Fin 24), rRtL4 b ≠ rAuxScr a)
    (hSrc : ∀ u : Fin 192, S (rSrc u)) (hI : ∀ i : Fin 206, S (rI i))
    (hRt : ∀ b : Fin 4, S (rRtL4 b)) (hScr : ∀ a : Fin 24, S (rAuxScr a))
    (mid : DynamicCircuit Var n) (hMid : DynWires S mid) :
    DynWires S (wrapTail139Router4 v rSrc rI rRtL4 rAuxScr hSrcI188 hSrcRtL4 hSrcScr hIRtL4 hIScr
        hRtL4Scr mid) := by
  have dwOL : CircWires S (cRt139OuterLoad rSrc rRtL4 rAuxScr hSrcRtL4 hSrcScr) :=
    ⟨⟨⟨⟨cw_cXorMaskSrc192 rSrc _ _ hSrc (hRt 0) rt139MD0 180 (by decide),
        cw_cXorMaskSrc192 rSrc _ _ hSrc (hRt 1) rt139MD1 180 (by decide)⟩,
       cw_cXorMaskSrc192 rSrc _ _ hSrc (hRt 2) rt139MD2 180 (by decide)⟩,
      cw_cXorMaskSrc192 rSrc _ _ hSrc (hRt 3) rt139MD3 180 (by decide)⟩,
     cw_cXorMaskSrc192 rSrc _ _ hSrc (hScr _) rt139MU 180 (by decide)⟩
  have dwIE : CircWires S (cRt139InnerEnter rSrc rI rAuxScr hSrcI188 hSrcScr) :=
    ⟨⟨⟨cw_cnot (hI _) (hI _), cw_cnot (hI _) (hI _)⟩,
      cw_cXorMaskSrcBdd rSrc _ hSrc (hI _) rt139MY2 180 (by decide) hSrcI188⟩,
     cw_cXorMaskSrc192 rSrc _ _ hSrc (hScr _) rt139MU 180 (by decide)⟩
  have dwB := dynWires_pSplitRBracket v (rAuxScr ⟨0, by decide⟩)
    (fun b : Fin 4 ↦ rRtL4 b) (fun b : Fin 4 ↦ rI (rt139HIdx b))
    (rAuxScr ⟨1, by decide⟩) (rAuxScr ⟨2, by decide⟩) (rAuxScr ⟨3, by decide⟩)
    (rt139RouterInj rI rRtL4 rAuxScr hIRtL4 hIScr hRtL4Scr)
    (DynamicCircuit.seq (.circuit (cRt139InnerEnter rSrc rI rAuxScr hSrcI188 hSrcScr))
      (DynamicCircuit.seq mid (.circuit (cRt139InnerEnter rSrc rI rAuxScr hSrcI188 hSrcScr))))
    (hScr _) (fun _ ↦ hRt _) (fun _ ↦ hI _) (hScr _) (hScr _) (hScr _)
    ⟨dwIE, ⟨hMid, dwIE⟩⟩
  exact ⟨dwOL, ⟨dwB, dwOL⟩⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem rt139_masks_lt181 : rt139MD0 < 2 ^ 181 ∧ rt139MD1 < 2 ^ 181 ∧ rt139MD2 < 2 ^ 181 ∧
    rt139MD3 < 2 ^ 181 ∧ rt139MU < 2 ^ 181 ∧ rt139MY2 < 2 ^ 181 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem dom_rt139 : (domKeepMask &&& rt139MD0 == rt139MD0) = true ∧
    (domKeepMask &&& rt139MD1 == rt139MD1) = true ∧ (domKeepMask &&& rt139MD2 == rt139MD2) = true ∧
    (domKeepMask &&& rt139MD3 == rt139MD3) = true ∧ (domKeepMask &&& rt139MU == rt139MU) = true ∧
    (domKeepMask &&& rt139MY2 == rt139MY2) = true := by decide +kernel
theorem ket_cRt139OuterLoad {n : ℕ} [NeZero (2 ^ n)]
    (rSrc : QRegister 192 n) (rRtL4 : QRegister 4 n) (rAuxScr : QRegister 24 n)
    (hSrcRtL4 : ∀ (u : Fin 192) (b : Fin 4), rSrc u ≠ rRtL4 b)
    (hSrcScr : ∀ (u : Fin 192) (i : Fin 24), rSrc u ≠ rAuxScr i)
    (hRtL4Scr : ∀ (b : Fin 4) (a : Fin 24), rRtL4 b ≠ rAuxScr a)
    (c : Fin (2 ^ 41)) (γ : BitAssignment n)
    (hSrc : ∀ u : Fin 192, u.val < 180 → γ (rSrc u) = if (e151Dom c).testBit (1 +
        u.val) then 1 else 0) :
    (cRt139OuterLoad rSrc rRtL4 rAuxScr hSrcRtL4 hSrcScr).eval.1.mulVec (ket γ) =
      ket (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update γ (rRtL4 0) (γ (rRtL4 0) + if bOf c rt139MD0 then 1 else 0))
                  (rRtL4 1) (γ (rRtL4 1) + if bOf c rt139MD1 then 1 else 0))
                (rRtL4 2) (γ (rRtL4 2) + if bOf c rt139MD2 then 1 else 0))
              (rRtL4 3) (γ (rRtL4 3) + if bOf c rt139MD3 then 1 else 0))
            (rAuxScr ⟨0, by decide⟩) (γ (rAuxScr ⟨0, by decide⟩) + if bOf c rt139MU then 1 else 0))
                := by
  obtain ⟨hm0, hm1, hm2, hm3, hmU, _⟩ := rt139_masks_lt181; obtain ⟨dm0, dm1, dm2, dm3, dmU, _⟩ :=
      dom_rt139
  let iu : Fin 24 := ⟨0, by decide⟩
  have hNeRt : ∀ (a b : Fin 4), a ≠ b → rRtL4 a ≠ rRtL4 b := fun a b h ↦ rRtL4.wires.injective.ne h
  dsimp only [cRt139OuterLoad];
  rw [eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, ket_cXorMaskSrc192,
      env151_maskParity180 rSrc c γ hSrc rt139MD0 hm0 dm0]
  let γ1 := Function.update γ (rRtL4 0) (γ (rRtL4 0) + if bOf c rt139MD0 then 1 else 0)
  have hSrc1 : ∀ u : Fin 192, u.val < 180 → γ1 (rSrc u) = if (e151Dom c).testBit (1 +
      u.val) then 1 else 0 := fun u hu ↦
      (Function.update_of_ne (hSrcRtL4 u 0) _ _).trans (hSrc u hu)
  rw [ket_cXorMaskSrc192, env151_maskParity180 rSrc c γ1 hSrc1 rt139MD1 hm1 dm1,
      Function.update_of_ne (hNeRt 1 0 (by decide))]
  let γ2 := Function.update γ1 (rRtL4 1) (γ (rRtL4 1) + if bOf c rt139MD1 then 1 else 0)
  have hSrc2 : ∀ u : Fin 192, u.val < 180 → γ2 (rSrc u) = if (e151Dom c).testBit (1 +
      u.val) then 1 else 0 := fun u hu ↦
      (Function.update_of_ne (hSrcRtL4 u 1) _ _).trans (hSrc1 u hu)
  rw [ket_cXorMaskSrc192, env151_maskParity180 rSrc c γ2 hSrc2 rt139MD2 hm2 dm2,
      Function.update_of_ne (hNeRt 2 1 (by decide)), Function.update_of_ne (hNeRt 2 0 (by decide))]
  let γ3 := Function.update γ2 (rRtL4 2) (γ (rRtL4 2) + if bOf c rt139MD2 then 1 else 0)
  have hSrc3 : ∀ u : Fin 192, u.val < 180 → γ3 (rSrc u) = if (e151Dom c).testBit (1 +
      u.val) then 1 else 0 := fun u hu ↦
      (Function.update_of_ne (hSrcRtL4 u 2) _ _).trans (hSrc2 u hu)
  rw [ket_cXorMaskSrc192, env151_maskParity180 rSrc c γ3 hSrc3 rt139MD3 hm3 dm3,
      Function.update_of_ne (hNeRt 3 2 (by decide)), Function.update_of_ne (hNeRt 3 1 (by decide)),
      Function.update_of_ne (hNeRt 3 0 (by decide))]
  let γ4 := Function.update γ3 (rRtL4 3) (γ (rRtL4 3) + if bOf c rt139MD3 then 1 else 0)
  have hSrc4 : ∀ u : Fin 192, u.val < 180 → γ4 (rSrc u) = if (e151Dom c).testBit (1 +
      u.val) then 1 else 0 := fun u hu ↦
      (Function.update_of_ne (hSrcRtL4 u 3) _ _).trans (hSrc3 u hu)
  rw [ket_cXorMaskSrc192, env151_maskParity180 rSrc c γ4 hSrc4 rt139MU hmU dmU,
      Function.update_of_ne (hRtL4Scr 3 iu).symm, Function.update_of_ne (hRtL4Scr 2 iu).symm,
      Function.update_of_ne (hRtL4Scr 1 iu).symm, Function.update_of_ne (hRtL4Scr 0 iu).symm]

theorem ket_cRt139InnerEnter {n : ℕ} [NeZero (2 ^ n)]
    (rSrc : QRegister 192 n) (rI : QRegister 206 n) (rAuxScr : QRegister 24 n)
    (hSrcI187 : ∀ u : Fin 192, u.val < 180 → rSrc u ≠ rI ⟨187, by decide⟩)
    (hSrcI188 : ∀ u : Fin 192, u.val < 180 → rSrc u ≠ rI ⟨188, by decide⟩)
    (hSrcScr : ∀ (u : Fin 192) (i : Fin 24), rSrc u ≠ rAuxScr i)
    (hIScr : ∀ (i : Fin 206) (a : Fin 24), rI i ≠ rAuxScr a)
    (c : Fin (2 ^ 41)) (γ : BitAssignment n)
    (hSrc : ∀ u : Fin 192, u.val < 180 → γ (rSrc u) = if (e151Dom c).testBit (1 +
        u.val) then 1 else 0) :
    (cRt139InnerEnter rSrc rI rAuxScr hSrcI188 hSrcScr).eval.1.mulVec (ket γ) =
      ket (Function.update
            (Function.update
              (Function.update γ
                (rI ⟨187, by decide⟩) (γ (rI ⟨187, by decide⟩) + γ (rI ⟨189, by decide⟩)))
              (rI ⟨188, by decide⟩)
              (γ (rI ⟨188, by decide⟩) + γ (rI ⟨180, by decide⟩) + if bOf c rt139MY2 then 1 else 0))
            (rAuxScr ⟨0, by decide⟩)
            (γ (rAuxScr ⟨0, by decide⟩) + if bOf c rt139MU then 1 else 0)) := by
  obtain ⟨_, _, _, _, hmU, hmY⟩ := rt139_masks_lt181; obtain ⟨_, _, _, _, dmU, dmY⟩ := dom_rt139
  let iu : Fin 24 := ⟨0, by decide⟩
  let h80 : Fin 206 := ⟨180, by decide⟩
  let h87 : Fin 206 := ⟨187, by decide⟩
  let h88 : Fin 206 := ⟨188, by decide⟩
  let h89 : Fin 206 := ⟨189, by decide⟩
  have hNeI : ∀ (a b : Fin 206), a ≠ b → rI a ≠ rI b := fun a b h ↦ rI.wires.injective.ne h
  dsimp only [cRt139InnerEnter]; rw [eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, ket_CNOT];
  let γ1 := Function.update γ (rI h87) (γ (rI h87) + γ (rI h89))
  rw [ket_CNOT, Function.update_of_ne (hNeI h88 h87 (by decide)),
      Function.update_of_ne (hNeI h80 h87 (by decide))]
  let γ2 := Function.update γ1 (rI h88) (γ (rI h88) + γ (rI h80))
  have hSrc2 : ∀ u : Fin 192, u.val < 180 → γ2 (rSrc u) = if (e151Dom c).testBit (1 +
      u.val) then 1 else 0 :=
    fun u hu ↦ by
      dsimp only [γ2, γ1];
      rw [Function.update_of_ne (hSrcI188 u hu), Function.update_of_ne (hSrcI187 u hu)];
      exact hSrc u hu
  rw [ket_cXorMaskSrcBdd, env151_maskParity180 rSrc c γ2 hSrc2 rt139MY2 hmY dmY,
      Function.update_self, Function.update_idem]
  let γ3 := Function.update γ1 (rI h88) (γ (rI h88) + γ (rI h80) + if bOf c rt139MY2 then 1 else 0)
  have hSrc3 : ∀ u : Fin 192, u.val < 180 → γ3 (rSrc u) = if (e151Dom c).testBit (1 +
      u.val) then 1 else 0 :=
    fun u hu ↦ by
      dsimp only [γ3, γ1];
      rw [Function.update_of_ne (hSrcI188 u hu), Function.update_of_ne (hSrcI187 u hu)];
      exact hSrc u hu
  rw [ket_cXorMaskSrc192, env151_maskParity180 rSrc c γ3 hSrc3 rt139MU hmU dmU,
      Function.update_of_ne (hIScr h88 iu).symm, Function.update_of_ne (hIScr h87 iu).symm]

def stRt139Step {n : ℕ} (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
    (c : Fin (2 ^ 41)) (γ : BitAssignment n) (x : Wire n) : ZMod 2 :=
  let uV : ZMod 2 := if bOf c rt139MU then 1 else 0
  match findBranch (fun b : Fin 4 ↦ rI (rt139HIdx b)) x with
  | some b => if (e151 c).testBit (1 + (rt139HIdx b).val) then 1 else 0
  | none =>
      match findBranch rRtL4.wires x with
      | some b => (if bOf c (rt139MDOf b) then 1 else 0) * (1 + uV)
      | none => γ x

theorem stRt139Step_hW {n : ℕ} (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
    (c : Fin (2 ^ 41)) (γ : BitAssignment n) (b : Fin 4) :
    stRt139Step rI rRtL4 c γ (rI (rt139HIdx b)) =
      if (e151 c).testBit (1 + (rt139HIdx b).val) then 1 else 0 := by
  dsimp only [stRt139Step]
  rw [findBranch_self (show Function.Injective fun k ↦
      rI (rt139HIdx k) from rI.wires.injective.comp rt139HIdx_injective) b]

theorem stRt139Step_lW {n : ℕ} (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
    (hIRtL4 : ∀ (i : Fin 206) (b : Fin 4), rI i ≠ rRtL4 b)
    (c : Fin (2 ^ 41)) (γ : BitAssignment n) (b : Fin 4) :
    stRt139Step rI rRtL4 c γ (rRtL4 b) =
      (if bOf c (rt139MDOf b) then 1 else 0) * (1 + if bOf c rt139MU then 1 else 0) := by
  dsimp only [stRt139Step]
  rw [findBranch_none (fun k ↦ (hIRtL4 _ b).symm), findBranch_self rRtL4.wires.injective b]

theorem stRt139Step_outside {n : ℕ} (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
    (c : Fin (2 ^ 41)) (γ : BitAssignment n) {x : Wire n}
    (hxH : ∀ b : Fin 4, x ≠ rI (rt139HIdx b)) (hxRt : ∀ b : Fin 4, x ≠ rRtL4 b) :
    stRt139Step rI rRtL4 c γ x = γ x := by
  dsimp only [stRt139Step]
  rw [findBranch_none hxH, findBranch_none hxRt]

theorem stRt139Step_rI_other {n : ℕ} (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
    (hIRtL4 : ∀ (i : Fin 206) (b : Fin 4), rI i ≠ rRtL4 b) (c : Fin (2 ^ 41)) (γ : BitAssignment n)
    (i : Fin 206) (hi180 : i.val ≠ 180) (hi187 : i.val ≠ 187) (hi188 : i.val ≠ 188)
        (hi189 : i.val ≠ 189) :
    stRt139Step rI rRtL4 c γ (rI i) = γ (rI i) :=
  stRt139Step_outside rI rRtL4 c γ
    (fun b e ↦ by
      have hv := congrArg Fin.val (rI.wires.injective e)
      fin_cases b
      · exact hi180 hv
      · exact hi187 hv
      · exact hi188 hv
      · exact hi189 hv)
    (fun b ↦ hIRtL4 i b)

theorem stRt139Step_upd_outside {n : ℕ} (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
    (c : Fin (2 ^ 41)) (γ : BitAssignment n) {w : Wire n} (b : ZMod 2)
    (hwH : ∀ k : Fin 4, w ≠ rI (rt139HIdx k)) (hwRt : ∀ k : Fin 4, w ≠ rRtL4 k) :
    stRt139Step rI rRtL4 c (Function.update γ w b) =
        Function.update (stRt139Step rI rRtL4 c γ) w b := by
  funext x
  by_cases hxw : x = w
  · subst hxw
    rw [Function.update_self, stRt139Step_outside rI rRtL4 c _ hwH hwRt, Function.update_self]
  · rw [Function.update_of_ne hxw]
    dsimp only [stRt139Step]
    cases findBranch (fun k : Fin 4 ↦ rI (rt139HIdx k)) x with
    | some _ => rfl
    | none =>
      cases findBranch rRtL4.wires x with
      | some _ => rfl
      | none => rw [Function.update_of_ne hxw]
set_option maxHeartbeats 1600000 in
-- finite certificate kernel reduction
theorem step_wrapTail139Router4 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n)
    (rSrc : QRegister 192 n) (rI : QRegister 206 n) (rRtL4 : QRegister 4 n)
        (rAuxScr : QRegister 24 n)
    (hSrcEqI : ∀ u : Fin 180, rSrc ⟨u.val, by omega⟩ = rI ⟨u.val, by omega⟩)
    (hSrcI188 : ∀ u : Fin 192, u.val < 180 → rSrc u ≠ rI ⟨188, by decide⟩)
    (hSrcRtL4 : ∀ (u : Fin 192) (b : Fin 4), rSrc u ≠ rRtL4 b)
    (hSrcScr : ∀ (u : Fin 192) (i : Fin 24), rSrc u ≠ rAuxScr i)
    (hIRtL4 : ∀ (i : Fin 206) (b : Fin 4), rI i ≠ rRtL4 b)
    (hIScr : ∀ (i : Fin 206) (a : Fin 24), rI i ≠ rAuxScr a)
    (hRtL4Scr : ∀ (b : Fin 4) (a : Fin 24), rRtL4 b ≠ rAuxScr a)
    (coinFn : BitAssignment n → Fin (2 ^ 41))
    (st₀ st₁ : BitAssignment n → BitAssignment n)
    (mid : DynamicCircuit Var n)
    (hSrc₀ : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin 192, u.val < 180 →
      st₀ δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0)
    (hSrc₁ : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin 192, u.val < 180 →
      st₁ δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0)
    (hCln₀ : ∀ δ, (∀ q, δ (rWork q) = 0) →
      (∀ a : Fin 24, a.val < 4 → st₀ δ (rAuxScr a) = 0) ∧
      (∀ b : Fin 4, st₀ δ (rRtL4 b) = 0) ∧
      (∀ b : Fin 4, st₀ δ (rI (rt139HIdx b)) = 0))
    (hCln₁ : ∀ δ, (∀ q, δ (rWork q) = 0) →
      (∀ a : Fin 24, a.val < 4 → st₁ δ (rAuxScr a) = 0) ∧
      (∀ b : Fin 4, st₁ δ (rRtL4 b) = 0) ∧
      (∀ b : Fin 4, st₁ δ (rI (rt139HIdx b)) = 0))
    (hMid : SubspaceStep
      (mkKetOpW rWork (fun δ ↦ stRt139Step rI rRtL4 (coinFn δ) (st₀ δ)) (fun _ ↦ 0))
      (mkKetOpW rWork (fun δ ↦ stRt139Step rI rRtL4 (coinFn δ) (st₁ δ)) (fun _ ↦ 0))
      mid) :
    SubspaceStep (mkKetOpW rWork st₀ (fun _ ↦ 0)) (mkKetOpW rWork st₁ (fun _ ↦ 0))
      (wrapTail139Router4 v rSrc rI rRtL4 rAuxScr hSrcI188 hSrcRtL4 hSrcScr hIRtL4 hIScr hRtL4Scr
          mid) := by
  let iu : Fin 24 := ⟨0, by decide⟩
  let uWire := rAuxScr iu
  let lW : Fin 4 → Wire n := fun b ↦ rRtL4 b
  let hW : Fin 4 → Wire n := fun b ↦ rI (rt139HIdx b)
  let hInj := rt139RouterInj rI rRtL4 rAuxScr hIRtL4 hIScr hRtL4Scr; obtain ⟨hlInj, hhInj, hlhNe⟩ :=
      wPairR_inj_props hInj.w_inj; let cOL :=
                                     cRt139OuterLoad rSrc rRtL4 rAuxScr hSrcRtL4 hSrcScr;
                                     let cIE := cRt139InnerEnter rSrc rI rAuxScr hSrcI188 hSrcScr
  have hmLLt (b : Fin 4) : rt139MDOf b < 2 ^ 181 := by
    fin_cases b <;> dsimp [rt139MDOf] <;> decide +kernel
  have hmLDom (b : Fin 4) : (domKeepMask &&& rt139MDOf b == rt139MDOf b) = true := by
    fin_cases b <;> dsimp [rt139MDOf] <;> decide +kernel
  have hSrc180NotHW (u : Fin 192) (hu : u.val < 180) (b : Fin 4) : rSrc u ≠ hW b := by
    rw [show rSrc u = rI ⟨u.val, by omega⟩ from (congrArg rSrc (Fin.ext rfl)).trans (hSrcEqI ⟨u.val,
        hu⟩)]
    have hbGe : 180 ≤ (rt139HIdx b).val := by fin_cases b <;> decide
    exact rI.wires.injective.ne (Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hu hbGe)))
  have hSrcI187 (u : Fin 192) (hu : u.val < 180) : rSrc u ≠ rI ⟨187, by decide⟩ :=
      hSrc180NotHW u hu 1
  let stLoadOf (stB : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
    let c := coinFn δ
    Function.update (Function.update (Function.update (Function.update
      (Function.update (stB δ) (rRtL4 0) (if bOf c rt139MD0 then 1 else 0))
      (rRtL4 1) (if bOf c rt139MD1 then 1 else 0))
      (rRtL4 2) (if bOf c rt139MD2 then 1 else 0))
      (rRtL4 3) (if bOf c rt139MD3 then 1 else 0))
      (rAuxScr iu) (if bOf c rt139MU then 1 else 0)
  have hNeS (a b : Fin 24) (h : a.val ≠ b.val) : rAuxScr a ≠ rAuxScr b :=
    fun e ↦ h (congrArg Fin.val (rAuxScr.wires.injective e))
  have hLoadSrc (stB : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hS : ∀ u : Fin 192, u.val < 180 → stB δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 +
          u.val) then 1 else 0)
      (u : Fin 192) (hu : u.val < 180) :
      stLoadOf stB δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0 := by
    dsimp only [stLoadOf]
    rw [Function.update_of_ne (hSrcScr u iu), Function.update_of_ne (hSrcRtL4 u 3),
      Function.update_of_ne (hSrcRtL4 u 2), Function.update_of_ne (hSrcRtL4 u 1),
          Function.update_of_ne (hSrcRtL4 u 0)]
    exact hS u hu
  have hlVal (stB : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (b : Fin 4) :
      stLoadOf stB δ (lW b) = if bOf (coinFn δ) (rt139MDOf b) then 1 else 0 := by
    rcases (by decide : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) b with rfl | rfl | rfl | rfl
    all_goals
      dsimp only [stLoadOf, lW, rt139MDOf]
      rw [Function.update_of_ne (hRtL4Scr _ iu)]
      repeat rw [Function.update_of_ne (rRtL4.wires.injective.ne (by decide))]
      exact Function.update_self _ _ _
  have hLoadEq : cOL.eval.1 * mkKetOpW rWork st₀ (fun _ ↦ 0) = mkKetOpW rWork (stLoadOf st₀)
      (fun _ ↦ 0) :=
    mkKetOpW_mul_ket_eq rWork _ _ _ _ fun δ hz ↦ by
      rw [ket_cRt139OuterLoad rSrc rRtL4 rAuxScr hSrcRtL4 hSrcScr hRtL4Scr (coinFn δ) (st₀ δ)
          (hSrc₀ δ hz)]
      obtain ⟨cS, cL, _⟩ := hCln₀ δ hz
      dsimp only [stLoadOf]
      rw [cL 0, cL 1, cL 2, cL 3, cS iu (by decide), zero_add, zero_add, zero_add, zero_add,
          zero_add]
  have hMD0 : rt139MDOf 0 = rt139MD0 := rfl
  have hMD1 : rt139MDOf 1 = rt139MD1 := rfl
  have hMD2 : rt139MDOf 2 = rt139MD2 := rfl
  have hMD3 : rt139MDOf 3 = rt139MD3 := rfl
  have hUnloadEq : cOL.eval.1 * mkKetOpW rWork (stLoadOf st₁)
      (fun _ ↦ 0) = mkKetOpW rWork st₁ (fun _ ↦ 0) :=
    mkKetOpW_mul_ket_eq rWork _ _ _ _ fun δ hz ↦ by
      rw [ket_cRt139OuterLoad rSrc rRtL4 rAuxScr hSrcRtL4 hSrcScr hRtL4Scr (coinFn δ)
        (stLoadOf st₁ δ) (hLoadSrc st₁ δ (hSrc₁ δ hz))]
      obtain ⟨cS, cL, _⟩ := hCln₁ δ hz
      refine congrArg ket (funext fun x ↦ ?_)
      by_cases hxu : x = rAuxScr iu
      · subst hxu
        dsimp only [stLoadOf]
        rw [Function.update_self, Function.update_self, zmod2_add_self, cS iu (by decide)]
      · rw [Function.update_of_ne hxu]
        by_cases hxL : ∃ b : Fin 4, rRtL4 b = x
        · obtain ⟨b, rfl⟩ := hxL
          rcases (by decide : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) b with rfl | rfl | rfl
              | rfl
          · rw [Function.update_of_ne (rRtL4.wires.injective.ne (by decide)),
              Function.update_of_ne (rRtL4.wires.injective.ne (by decide)),
              Function.update_of_ne (rRtL4.wires.injective.ne (by decide)),
              Function.update_self, hlVal st₁ δ 0, hMD0, zmod2_add_self, cL 0]
          · rw [Function.update_of_ne (rRtL4.wires.injective.ne (by decide)),
              Function.update_of_ne (rRtL4.wires.injective.ne (by decide)),
              Function.update_self, hlVal st₁ δ 1, hMD1, zmod2_add_self, cL 1]
          · rw [Function.update_of_ne (rRtL4.wires.injective.ne (by decide)),
              Function.update_self, hlVal st₁ δ 2, hMD2, zmod2_add_self, cL 2]
          · rw [Function.update_self, hlVal st₁ δ 3, hMD3, zmod2_add_self, cL 3]
        · have hxNe (b : Fin 4) : x ≠ rRtL4 b := fun e ↦ hxL ⟨b, e.symm⟩
          dsimp only [stLoadOf]
          rw [Function.update_of_ne (hxNe 3), Function.update_of_ne (hxNe 2),
              Function.update_of_ne (hxNe 1),
            Function.update_of_ne (hxNe 0), Function.update_of_ne hxu,
                Function.update_of_ne (hxNe 3),
            Function.update_of_ne (hxNe 2), Function.update_of_ne (hxNe 1),
                Function.update_of_ne (hxNe 0)]
  have hEnterEq (stB : BitAssignment n → BitAssignment n)
      (hSrcB : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin 192, u.val < 180 →
        stB δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0)
      (hClnB : ∀ δ, (∀ q, δ (rWork q) = 0) → (∀ a : Fin 24, a.val < 4 → stB δ (rAuxScr a) = 0) ∧
        (∀ b : Fin 4, stB δ (rRtL4 b) = 0) ∧ (∀ b : Fin 4, stB δ (rI (rt139HIdx b)) = 0)) :
      cIE.eval.1 * mkKetOpW rWork (fun δ ↦ stSplitRFwd uWire lW hW (stLoadOf stB δ)) (fun _ ↦ 0) =
        mkKetOpW rWork (fun δ ↦ stRt139Step rI rRtL4 (coinFn δ) (stB δ)) (fun _ ↦ 0) :=
    mkKetOpW_mul_ket_eq rWork _ _ _ _ fun δ hz ↦ by
      let c := coinFn δ
      let γ := stSplitRFwd uWire lW hW (stLoadOf stB δ)
      have hSrcγ (u : Fin 192) (hu : u.val < 180) : γ (rSrc u) = if (e151Dom c).testBit (1 +
          u.val) then 1 else 0 :=
        (stSplitRFwd_other _ (fun b ↦ hSrcRtL4 u b)
            (fun b ↦ hSrc180NotHW u hu b)).trans (hLoadSrc stB δ (hSrcB δ hz) u hu)
      rw [ket_cRt139InnerEnter rSrc rI rAuxScr hSrcI187 hSrcI188 hSrcScr hIScr c γ hSrcγ]
      obtain ⟨cS, _, _⟩ := hClnB δ hz
      obtain ⟨_, hg181, hg188, hg189, hg190⟩ := rt139Spec c
      have huLoad : stLoadOf stB δ uWire = if bOf c rt139MU then 1 else 0 :=
          Function.update_self _ _ _
      have hγu : γ (rAuxScr iu) = if bOf c rt139MU then 1 else 0 :=
        (stSplitRFwd_other _ (fun b ↦ (hRtL4Scr b iu).symm)
            (fun _ ↦ (hIScr _ iu).symm)).trans huLoad
      have hγh (b : Fin 4) : γ (hW b) = if (bOf c (rt139MDOf b) &&
          bOf c rt139MU) then 1 else 0 := by
        dsimp only [γ]
        rw [stSplitRFwd_hW hhInj hlhNe _ b, hlVal stB δ b, huLoad]
        exact zmod2_and_eq _ _ _ rfl
      refine congrArg ket (funext fun x ↦ ?_)
      rw [hγu, zmod2_add_self, show γ (rI ⟨187, by decide⟩) = _ from hγh 1, hMD1,
        show γ (rI ⟨189, by decide⟩) = _ from hγh 3, hMD3, Stage1AsymRevEngine.z2_add_ite_xor,
            ← hg188,
        show γ (rI ⟨188, by decide⟩) = _ from hγh 2, hMD2, show γ (rI ⟨180, by decide⟩) =
            _ from hγh 0, hMD0,
        Stage1AsymRevEngine.z2_add_ite_xor, Stage1AsymRevEngine.z2_add_ite_xor, ← hg189]
      by_cases hxu : x = rAuxScr iu
      · subst hxu
        rw [Function.update_self, stRt139Step_outside rI rRtL4 c (stB δ)
          (fun _ ↦ (hIScr _ iu).symm) (fun b ↦ (hRtL4Scr b iu).symm), cS iu (by decide)]
      · rw [Function.update_of_ne hxu]
        by_cases hx88 : x = rI ⟨188, by decide⟩
        · rw [hx88, Function.update_self]
          exact (stRt139Step_hW rI rRtL4 c (stB δ) 2).symm
        · rw [Function.update_of_ne hx88]
          by_cases hx87 : x = rI ⟨187, by decide⟩
          · rw [hx87, Function.update_self]
            exact (stRt139Step_hW rI rRtL4 c (stB δ) 1).symm
          · rw [Function.update_of_ne hx87]
            by_cases hx89 : x = rI ⟨189, by decide⟩
            · subst hx89
              rw [show γ (rI ⟨189, by decide⟩) = _ from hγh 3, hMD3, ← hg190]
              exact (stRt139Step_hW rI rRtL4 c (stB δ) 3).symm
            · by_cases hx80 : x = rI ⟨180, by decide⟩
              · subst hx80
                rw [show γ (rI ⟨180, by decide⟩) = _ from hγh 0, hMD0, ← hg181]
                exact (stRt139Step_hW rI rRtL4 c (stB δ) 0).symm
              · by_cases hxL : ∃ b : Fin 4, rRtL4 b = x
                · obtain ⟨b, rfl⟩ := hxL
                  exact (stSplitRFwd_lW hlInj _ b).trans
                    (by rw [hlVal stB δ b, huLoad, stRt139Step_lW rI rRtL4 hIRtL4])
                · have hlx (b : Fin 4) : x ≠ lW b := fun e ↦ hxL ⟨b, e.symm⟩
                  have hhx (b : Fin 4) : x ≠ hW b := by
                    fin_cases b <;> first | exact hx80 | exact hx87 | exact hx88 | exact hx89
                  dsimp only [γ, stLoadOf]
                  rw [stSplitRFwd_other _ hlx hhx, stRt139Step_outside rI rRtL4 c (stB δ) hhx hlx,
                    Function.update_of_ne hxu, Function.update_of_ne (hlx 3),
                    Function.update_of_ne (hlx 2), Function.update_of_ne (hlx 1),
                        Function.update_of_ne (hlx 0)]
  have hExitEq : cIE.eval.1 * mkKetOpW rWork (fun δ ↦ stRt139Step rI rRtL4 (coinFn δ) (st₁ δ))
      (fun _ ↦ 0) =
      mkKetOpW rWork (fun δ ↦ stSplitRFwd uWire lW hW (stLoadOf st₁ δ)) (fun _ ↦ 0) := by
    rw [← hEnterEq st₁ hSrc₁ hCln₁]
    refine matrix_ext_ket fun δ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · let c := coinFn δ
      let γ := stSplitRFwd uWire lW hW (stLoadOf st₁ δ)
      have hSrcγ (u : Fin 192) (hu : u.val < 180) : γ (rSrc u) = if (e151Dom c).testBit (1 +
          u.val) then 1 else 0 :=
        (stSplitRFwd_other _ (fun b ↦ hSrcRtL4 u b)
            (fun b ↦ hSrc180NotHW u hu b)).trans (hLoadSrc st₁ δ (hSrc₁ δ hz) u hu)
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul,
          ket_cRt139InnerEnter rSrc rI rAuxScr hSrcI187 hSrcI188 hSrcScr hIScr c γ hSrcγ]
      let γ' := Function.update (Function.update
          (Function.update γ (rI ⟨187, by decide⟩)
              (γ (rI ⟨187, by decide⟩) + γ (rI ⟨189, by decide⟩)))
          (rI ⟨188, by decide⟩) (γ (rI ⟨188, by decide⟩) + γ (rI ⟨180, by decide⟩) +
              if bOf c rt139MY2 then 1 else 0))
        (rAuxScr iu) (γ (rAuxScr iu) + if bOf c rt139MU then 1 else 0)
      have hSrcγ' (u : Fin 192) (hu : u.val < 180) : γ' (rSrc u) = if (e151Dom c).testBit (1 +
          u.val) then 1 else 0 := by
        dsimp only [γ']
        rw [Function.update_of_ne (hSrcScr u iu), Function.update_of_ne (hSrcI188 u hu),
            Function.update_of_ne (hSrcI187 u hu)]
        exact hSrcγ u hu
      have hOut (i : Fin 206) (n7 : i.val ≠ 187) (n8 : i.val ≠ 188) : γ' (rI i) = γ (rI i) := by
        dsimp only [γ']
        rw [Function.update_of_ne (hIScr _ iu),
            Function.update_of_ne (rI.wires.injective.ne (Fin.ne_of_val_ne n8)),
          Function.update_of_ne (rI.wires.injective.ne (Fin.ne_of_val_ne n7))]
      rw [ket_cRt139InnerEnter rSrc rI rAuxScr hSrcI187 hSrcI188 hSrcScr hIScr c γ' hSrcγ',
        show γ' (rI ⟨187, by decide⟩) = γ (rI ⟨187, by decide⟩) + γ (rI ⟨189, by decide⟩) by
          dsimp only [γ']
          rw [Function.update_of_ne (hIScr _ iu),
              Function.update_of_ne (rI.wires.injective.ne (by decide)), Function.update_self],
        hOut ⟨189, by decide⟩ (by decide) (by decide),
        show γ' (rI ⟨188, by decide⟩) = γ (rI ⟨188, by decide⟩) + γ (rI ⟨180, by decide⟩) +
            if bOf c rt139MY2 then 1 else 0 by
          dsimp only [γ']
          rw [Function.update_of_ne (hIScr _ iu), Function.update_self],
        hOut ⟨180, by decide⟩ (by decide) (by decide),
        show γ' (rAuxScr iu) = γ (rAuxScr iu) +
            if bOf c rt139MU then 1 else 0 from Function.update_self _ _ _,
        show ∀ a b d : ZMod 2, a + b + d + b + d = a by decide,
        add_assoc (γ (rI ⟨187, by decide⟩)), zmod2_add_self, add_zero, add_assoc (γ (rAuxScr iu)),
            zmod2_add_self, add_zero]
      refine congrArg (_ • ·) (congrArg ket (funext fun x ↦ ?_))
      by_cases hxu : x = rAuxScr iu
      · rw [hxu, Function.update_self]
      · by_cases hx88 : x = rI ⟨188, by decide⟩
        · rw [Function.update_of_ne hxu, hx88, Function.update_self]
        · by_cases hx87 : x = rI ⟨187, by decide⟩
          · rw [Function.update_of_ne hxu, Function.update_of_ne hx88, hx87, Function.update_self]
          · dsimp only [γ']
            rw [Function.update_of_ne hxu, Function.update_of_ne hx88, Function.update_of_ne hx87,
              Function.update_of_ne hxu, Function.update_of_ne hx88, Function.update_of_ne hx87]
    · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
  let eBranch (b : Fin 4) (γ : BitAssignment n) : ZMod 2 :=
      maskParity (rt139MDOf b) (fun u : Fin 192 ↦ γ (rSrc u)) 180 (by decide)
  have heIndep (b : Fin 4) (γ₁ γ₂ : BitAssignment n)
      (h : ∀ x, (∀ j, x ≠ lW j) → (∀ j, x ≠ hW j) → x ≠ rAuxScr ⟨1, by decide⟩ → γ₁ x = γ₂ x) :
      eBranch b γ₁ = eBranch b γ₂ :=
    maskParity_congr_support _ _ _ 180 (by decide) fun u hu _ ↦
      h (rSrc u) (fun j ↦ hSrcRtL4 u j) (fun j ↦ hSrc180NotHW u hu j) (hSrcScr u _)
  have hMut (δ : BitAssignment n) (_ : ∀ q, δ (rWork q) = 0) (b₁ b₂ : Fin 4) (hne : b₁ ≠ b₂)
      (hb1 : stLoadOf st₀ δ (lW b₁) = 1) : stLoadOf st₀ δ (lW b₂) = 0 := by
    rw [hlVal st₀ δ b₁] at hb1
    rw [hlVal st₀ δ b₂]
    have hMB := (rt139Spec (coinFn δ)).1 b₁ b₂ hne
    cases h : bOf (coinFn δ) (rt139MDOf b₁)
    · exact absurd (h ▸ hb1) zero_ne_one
    · rw [h, Bool.true_and] at hMB
      rw [hMB]
      rfl
  have hLoadOthS (stB : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (a : Fin 24)
      (ha : a.val ≠ 0) :
      stLoadOf stB δ (rAuxScr a) = stB δ (rAuxScr a) := by
    dsimp only [stLoadOf]
    rw [Function.update_of_ne (hNeS a iu ha), Function.update_of_ne (hRtL4Scr 3 a).symm,
      Function.update_of_ne (hRtL4Scr 2 a).symm, Function.update_of_ne (hRtL4Scr 1 a).symm,
          Function.update_of_ne (hRtL4Scr 0 a).symm]
  have hLoadOthH (stB : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (b : Fin 4) :
      stLoadOf stB δ (hW b) = stB δ (hW b) := by
    dsimp only [stLoadOf, hW]
    rw [Function.update_of_ne (hIScr _ iu), Function.update_of_ne (hIRtL4 _ 3),
      Function.update_of_ne (hIRtL4 _ 2), Function.update_of_ne (hIRtL4 _ 1),
          Function.update_of_ne (hIRtL4 _ 0)]
  have heEq (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (b : Fin 4) :
      eBranch b (stLoadOf st₀ δ) = stLoadOf st₀ δ (lW b) :=
    (env151_maskParity180 rSrc (coinFn δ) (stLoadOf st₀ δ) (hLoadSrc st₀ δ (hSrc₀ δ hz))
      (rt139MDOf b) (hmLLt b) (hmLDom b)).trans (hlVal st₀ δ b).symm
  have sSplit := step_pSplitRBracket (by decide : 0 < 4) v rWork uWire lW hW
    (rAuxScr ⟨1, by decide⟩) (rAuxScr ⟨2, by decide⟩) (rAuxScr ⟨3, by decide⟩)
    eBranch hInj heIndep (stLoadOf st₀) (stLoadOf st₁) (fun _ ↦ 0) (fun _ ↦ 0)
    (DynamicCircuit.seq (.circuit cIE) (DynamicCircuit.seq mid (.circuit cIE)))
    hMut
    (fun δ hz ↦ by
      obtain ⟨cS, _, cH⟩ := hCln₀ δ hz
      exact ⟨fun b ↦ (hLoadOthH st₀ δ b).trans (cH b),
        (hLoadOthS st₀ δ _ (by decide)).trans (cS _ (by decide)),
        (hLoadOthS st₀ δ _ (by decide)).trans (cS _ (by decide)),
        (hLoadOthS st₀ δ _ (by decide)).trans (cS _ (by decide))⟩)
    heEq
    (fun δ hz ↦ by
      obtain ⟨aS, _, aH⟩ := hCln₀ δ hz
      obtain ⟨bS, _, bH⟩ := hCln₁ δ hz
      have hSD (a : Fin 24) (ha0 : a.val ≠ 0) (ha4 : a.val < 4) : stLoadOf st₁ δ (rAuxScr a) =
          stLoadOf st₀ δ (rAuxScr a) := by
        rw [hLoadOthS st₁ δ a ha0, hLoadOthS st₀ δ a ha0, bS a ha4, aS a ha4]
      exact ⟨by
          dsimp only [stLoadOf, uWire]
          rw [Function.update_self, Function.update_self],
        fun b ↦ (hlVal st₁ δ b).trans (hlVal st₀ δ b).symm,
        fun b ↦ by rw [hLoadOthH st₁ δ b, hLoadOthH st₀ δ b, bH b, aH b],
        hSD ⟨1, by decide⟩ (by decide) (by decide), hSD ⟨2, by decide⟩ (by decide) (by decide),
        hSD ⟨3, by decide⟩ (by decide) (by decide),
        fun _ ↦ maskParity_congr_support _ _ _ 180 (by decide) fun u hu _ ↦
          (hLoadSrc st₁ δ (hSrc₁ δ hz) u hu).trans (hLoadSrc st₀ δ (hSrc₀ δ hz) u hu).symm⟩)
    (PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans
      (step_circ_mkKetOpW rWork _ _ _ _ cIE (hEnterEq st₀ hSrc₀ hCln₀))
      (Stage1AsymRevEngine.subspaceStep_seq_trans hMid (step_circ_mkKetOpW rWork _ _ _ _ cIE
          hExitEq)))
  exact PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans
    (step_circ_mkKetOpW rWork _ _ _ _ cOL hLoadEq)
    (Stage1AsymRevEngine.subspaceStep_seq_trans sSplit (step_circ_mkKetOpW rWork _ _ _ _ cOL
        hUnloadEq))

def pFwdInnerRt730 {Var : Type} {n : ℕ} (v : Var) (rTot : QRegister dLayout n) :
    DynamicCircuit Var n :=
  let rI := rCoinInner 165 (rTot.compose rW165); let rSrc214DomZ_n := rTot.compose rSrc214DomZ;
  let rSrc193_n := rTot.compose rSrc193; let rSrc := rTot.compose rSrc192QromOpt;
  let rSrcDomZ := rTot.compose rSrc192DomZ; let rO := rTot.compose rOut40Layout;
  let rAuxOut := rTot.compose rAuxOut10; let rAuxScr := rTot.compose rAuxScr24;
  let rRtL4 := rTot.compose rRt139L4; let rGat8 := rTot.compose rGatScr8DomZW298
  wrapPrefixRt v (rTot.compose rPreFwdRtW300)
    (wrapTail139Router4 v rSrc rI rRtL4 rAuxScr
      (fun u hu ↦ rTot.wires.injective.ne (rSrc192QromOpt_lt180_ne_rCoinInner188 u hu))
      (fun u b ↦ rTot.wires.injective.ne (rSrc192QromOpt_ne_rRt139L4 u b))
      (fun u a ↦ rTot.wires.injective.ne (rSrc192QromOpt_ne_rAuxScr24 u a))
      (fun i b ↦ rTot.wires.injective.ne (rCoinInner165_ne_rRt139L4 i b))
      (fun i a ↦ rTot.wires.injective.ne (rCoinInner165_ne_rAuxScr24 i a))
      (fun b a ↦ rTot.wires.injective.ne (rRt139L4_ne_rAuxScr24 b a))
      (wrapDynOnReg v rI cpFwdTail6
        (wrapDynOnReg v rI cpFwdTail14
          (wrapAuxChain v rSrc193_n rAuxOut rAuxScr
            (fun u b ↦ rTot.wires.injective.ne (rSrc193_ne_rAuxOut10 u b))
            (fun u i ↦ rTot.wires.injective.ne (rSrc193_ne_rAuxScr24 u i))
            (fun b i ↦ rTot.wires.injective.ne (rAuxOut10_ne_rAuxScr24 b i))
            (wrapDecodeB1 rAuxOut
              (.seq (.circuit (cTail5XorAux rSrc rO (fun u q ↦
                  rTot.wires.injective.ne (rSrc192QromOpt_ne_rOut40 u q)) 5 le_rfl))
                (.seq (pHk01Chunk8 v rSrcDomZ rO (rGat7Of8 rGat8)
                    (rSrc192DomZ_rTot_ne_rGat7DomZW298 rTot) (rGat7_rTot_ne_rOut40DomZW298 rTot))
                  (pValPairChainChunk8 v rSrc214DomZ_n rSrcDomZ rO rGat8
                    (fun u q ↦ rTot.wires.injective.ne (rSrc214DomZ_ne_rOut40 u q))
                    (fun u i ↦ rTot.wires.injective.ne (rSrc214DomZ_ne_rGatScr8DomZW298 u i))
                    (fun u i ↦ rTot.wires.injective.ne (rSrc192DomZ_ne_rGatScr8DomZW298 u i))
                    (fun i q ↦
                        rTot.wires.injective.ne (rGatScr8DomZW298_ne_rOut40 i q)) 16 le_rfl))))
            5 le_rfl))))

theorem dw_pFwdInnerRt730 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rTot : QRegister dLayout n) (hrPre : ∀ j : Fin 276, S ((rTot.compose rPreFwdRtW300) j))
    (hrAmb : ∀ j : Fin (81 + (165 + 0)), S ((rTot.compose rW165) j))
    (hrAuxOut : ∀ b : Fin 10, S ((rTot.compose rAuxOut10) b))
    (hrAuxScr : ∀ i : Fin 24, S ((rTot.compose rAuxScr24) i))
    (hrRtL4 : ∀ b : Fin 4, S ((rTot.compose rRt139L4) b))
    (hrGat8 : ∀ i : Fin 8, S ((rTot.compose rGatScr8DomZW298) i)) :
    DynWires S (pFwdInnerRt730 v rTot) := by
  let rAmb := rTot.compose rW165; let rI := rCoinInner 165 rAmb;
  let rSrc214_n := rTot.compose rSrc214; let rSrc214DomZ_n := rTot.compose rSrc214DomZ;
  let rSrc193_n := rTot.compose rSrc193; let rSrc := rTot.compose rSrc192QromOpt;
  let rSrcDomZ := rTot.compose rSrc192DomZ; let rO := rTot.compose rOut40Layout;
  let rAuxOut := rTot.compose rAuxOut10; let rAuxScr := rTot.compose rAuxScr24;
  let rRtL4 := rTot.compose rRt139L4; let rGat8 := rTot.compose rGatScr8DomZW298;
  let rGat7 := rGat7Of8 rGat8
  have hIS (i : Fin 206) : S (rI i) := hrAmb (innerIdxCoin 165 i)
  have hSrc214S (u : Fin 214) : S (rSrc214_n u) := by
    by_cases hu : u.val < 204
    · exact congrArg rTot.wires (rSrc214_lt204_eq_rI u hu).symm ▸ hIS ⟨u.val, by omega⟩
    · let bIdx : Fin 10 := ⟨u.val - 204, by omega⟩
      have hEq : rSrc214_n u = rAuxOut bIdx :=
        (congrArg rSrc214_n (Fin.ext (Nat.add_sub_of_le (Nat.not_lt.mp hu)).symm)).trans
          (congrArg rTot.wires (rSrc214_ge204_eq_auxOut bIdx))
      exact hEq.symm ▸ hrAuxOut bIdx
  have hSrc214DomZS (u : Fin 214) : S (rSrc214DomZ_n u) := by
    by_cases h67 : u.val = 67
    · exact ((congrArg rSrc214DomZ_n (Fin.ext h67)).trans (congrArg rTot.wires rSrc214DomZ_67)).symm
          ▸
        hrAuxScr ⟨4, by decide⟩
    · by_cases h69 : u.val = 69
      · exact ((congrArg rSrc214DomZ_n (Fin.ext h69)).trans (congrArg rTot.wires
            rSrc214DomZ_69)).symm ▸
          hrAuxScr ⟨5, by decide⟩
      · exact congrArg rTot.wires (rSrc214DomZ_eq_of_ne u h67 h69).symm ▸ hSrc214S u
  have hOS (q : Fin 40) : S (rO q) :=
    congrArg rTot.wires (rCoinOut40_rW165_eq q) ▸ hrAmb (QRegister.block 41 40 (outBlk_le 165) q)
  exact dw_wrapPrefixRt v (rTot.compose rPreFwdRtW300) hrPre _
    (dw_wrapTail139Router4 v rSrc rI rRtL4 rAuxScr _ _ _ _ _ _ (fun _ ↦
        hSrc214S _) hIS hrRtL4 hrAuxScr _
      (dynWires_wrapDynOnReg_local v rI hIS cpFwdTail6 _
        (dynWires_wrapDynOnReg_local v rI hIS cpFwdTail14 _
          (dw_wrapAuxChain v rSrc193_n rAuxOut rAuxScr _ _ _ (fun _ ↦
              hSrc214S _) hrAuxOut hrAuxScr _
            (dw_wrapDecodeB1 rAuxOut hrAuxOut
              (.seq (.circuit (cTail5XorAux rSrc rO (fun u q ↦
                  rTot.wires.injective.ne (rSrc192QromOpt_ne_rOut40 u q)) 5 le_rfl))
                (.seq (pHk01Chunk8 v rSrcDomZ rO rGat7
                    (rSrc192DomZ_rTot_ne_rGat7DomZW298 rTot) (rGat7_rTot_ne_rOut40DomZW298 rTot))
                  (pValPairChainChunk8 v rSrc214DomZ_n rSrcDomZ rO rGat8
                    (fun u q ↦ rTot.wires.injective.ne (rSrc214DomZ_ne_rOut40 u q))
                    (fun u i ↦ rTot.wires.injective.ne (rSrc214DomZ_ne_rGatScr8DomZW298 u i))
                    (fun u i ↦ rTot.wires.injective.ne (rSrc192DomZ_ne_rGatScr8DomZW298 u i))
                    (fun i q ↦
                        rTot.wires.injective.ne (rGatScr8DomZW298_ne_rOut40 i q)) 16 le_rfl)))
              ⟨cw_cTail5XorAux rSrc rO _ (fun _ ↦ hSrc214S _) hOS 5 le_rfl,
                dw_pHk01Chunk8 v rSrcDomZ rO rGat7 _ _ (fun _ ↦ hSrc214DomZS _) hOS (fun i ↦
                    rGat7Of8_eq rGat8 i ▸ hrGat8 _),
                dw_pValPairChainChunk8 v rSrc214DomZ_n rSrcDomZ rO rGat8 _ _ _ _
                  hSrc214DomZS (fun _ ↦ hSrc214DomZS _) hOS hrGat8 16 le_rfl⟩)
            5 le_rfl))))

set_option maxHeartbeats 8000000 in
-- Large circuit/register elaboration requires raised heartbeat limit.
theorem step_and_counts_pFwdInnerRt730 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rTot : QRegister dLayout n) :
    let rWork := rTot.compose rScrCompact1493; let rO := rTot.compose rOut40Layout;
    let coinFn := coinOfAmb rTot
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ δ) (fun _ ↦ 0))
      (mkKetOpW rWork (fun δ ↦ xorDstK rO
        (fun q ↦ if preCnotBit40 (m40VOpt (coinFn δ)) q.val then 1 else 0)
        40 Nat.le.refl δ) (fun _ ↦ 0))
      (pFwdInnerRt730 v rTot) ∧
    (pFwdInnerRt730 v rTot).count .T = 730 ∧
    (pFwdInnerRt730 v rTot).count .TOFF = 0 := by
  let rWork := rTot.compose rScrCompact1493; let rPre := rTot.compose rPreFwdRtW300;
  let rAmb := rTot.compose rW165; let rI := rCoinInner 165 rAmb;
  let rSrc214_n := rTot.compose rSrc214; let rSrc214DomZ_n := rTot.compose rSrc214DomZ;
  let rSrc193_n := rTot.compose rSrc193; let rSrc := rTot.compose rSrc192QromOpt;
  let rSrcDomZ := rTot.compose rSrc192DomZ; let rO := rTot.compose rOut40Layout;
  let rAuxOut := rTot.compose rAuxOut10; let rAuxScr := rTot.compose rAuxScr24;
  let rRtL4 := rTot.compose rRt139L4; let rGat8 := rTot.compose rGatScr8DomZW298;
  let rGat7 := rGat7Of8 rGat8
  let hSrcO : ∀ (u : Fin 192) (q : Fin 40), rSrc u ≠ rO q := fun u q ↦
      rTot.wires.injective.ne (rSrc192QromOpt_ne_rOut40 u q)
  let hSrcDomZO : ∀ (u : Fin 192) (q : Fin 40), rSrcDomZ u ≠ rO q := fun u q ↦
      rTot.wires.injective.ne (rSrc192DomZ_ne_rOut40 u q)
  let hSrc214O : ∀ (u : Fin 214) (q : Fin 40), rSrc214_n u ≠ rO q := fun u q ↦
      rTot.wires.injective.ne (rSrc214_ne_rOut40 u q)
  let hSrc214DomZO : ∀ (u : Fin 214) (q : Fin 40), rSrc214DomZ_n u ≠ rO q := fun u q ↦
      rTot.wires.injective.ne (rSrc214DomZ_ne_rOut40 u q)
  let hSrc214Gat8 : ∀ (u : Fin 214) (i : Fin 8), rSrc214DomZ_n u ≠ rGat8 i := fun u i ↦
      rTot.wires.injective.ne (rSrc214DomZ_ne_rGatScr8DomZW298 u i)
  let hSrcGat8 : ∀ (u : Fin 192) (i : Fin 8), rSrcDomZ u ≠ rGat8 i := fun u i ↦
      rTot.wires.injective.ne (rSrc192DomZ_ne_rGatScr8DomZW298 u i)
  let hGat8O : ∀ (i : Fin 8) (q : Fin 40), rGat8 i ≠ rO q := fun i q ↦
      rTot.wires.injective.ne (rGatScr8DomZW298_ne_rOut40 i q)
  let hSrcGat7 := rSrc192DomZ_rTot_ne_rGat7DomZW298 rTot;
  let hGat7O := rGat7_rTot_ne_rOut40DomZW298 rTot
  let hSrc193AuxOut : ∀ (u : Fin 193) (b : Fin 10), rSrc193_n u ≠ rAuxOut b := fun u b ↦
      rTot.wires.injective.ne (rSrc193_ne_rAuxOut10 u b)
  let hSrc193AuxScr : ∀ (u : Fin 193) (i : Fin 24), rSrc193_n u ≠ rAuxScr i := fun u i ↦
      rTot.wires.injective.ne (rSrc193_ne_rAuxScr24 u i)
  let hSrcAuxOut : ∀ (u : Fin 192) (b : Fin 10), rSrc u ≠ rAuxOut b := fun u b ↦
      rTot.wires.injective.ne (rSrc192QromOpt_ne_rAuxOut10 u b)
  let hSrcAuxScr : ∀ (u : Fin 192) (i : Fin 24), rSrc u ≠ rAuxScr i := fun u i ↦
      rTot.wires.injective.ne (rSrc192QromOpt_ne_rAuxScr24 u i)
  let hAuxOutScr : ∀ (b : Fin 10) (i : Fin 24), rAuxOut b ≠ rAuxScr i := fun b i ↦
      rTot.wires.injective.ne (rAuxOut10_ne_rAuxScr24 b i)
  let hSrcI188 : ∀ u : Fin 192, u.val < 180 → rSrc u ≠ rI ⟨188, by decide⟩ :=
    fun u hu ↦ rTot.wires.injective.ne (rSrc192QromOpt_lt180_ne_rCoinInner188 u hu)
  let hSrcRtL4 : ∀ (u : Fin 192) (b : Fin 4), rSrc u ≠ rRtL4 b := fun u b ↦
      rTot.wires.injective.ne (rSrc192QromOpt_ne_rRt139L4 u b)
  let hIRtL4 : ∀ (i : Fin 206) (b : Fin 4), rI i ≠ rRtL4 b := fun i b ↦
      rTot.wires.injective.ne (rCoinInner165_ne_rRt139L4 i b)
  let hIScr : ∀ (i : Fin 206) (a : Fin 24), rI i ≠ rAuxScr a := fun i a ↦
      rTot.wires.injective.ne (rCoinInner165_ne_rAuxScr24 i a)
  let hRtL4Scr : ∀ (b : Fin 4) (a : Fin 24), rRtL4 b ≠ rAuxScr a := fun b a ↦
      rTot.wires.injective.ne (rRt139L4_ne_rAuxScr24 b a)
  have hAuxOutO : ∀ (b : Fin 10) (q : Fin 40), rAuxOut b ≠ rO q := fun b q ↦
      rTot.wires.injective.ne (rAuxOut10_ne_rOut40 b q)
  have hAuxScrO : ∀ (i : Fin 24) (q : Fin 40), rAuxScr i ≠ rO q := fun i q ↦
      rTot.wires.injective.ne (rAuxScr24_ne_rOut40 i q)
  have hRtL4O : ∀ (b : Fin 4) (q : Fin 40), rRtL4 b ≠ rO q := fun b q ↦
      rTot.wires.injective.ne (rRt139L4_ne_rOut40 b q)
  have hAuxOutGat8 : ∀ (b : Fin 10) (i : Fin 8), rAuxOut b ≠ rGat8 i := fun b i ↦
      rTot.wires.injective.ne (rAuxOut10_ne_rGatScr8DomZW298 b i)
  let coinFn : BitAssignment n → Fin (2 ^ 41) := coinOfAmb rTot
  let preOutBitsFn (c : Fin (2 ^ 41)) (q : Fin 40) : ZMod 2 :=
      if preCnotBit40 (m40VOpt c) q.val then 1 else 0
  let basePre : BitAssignment n → BitAssignment n := fun δ ↦ δ
  let basePost : BitAssignment n → BitAssignment n := fun δ ↦
      xorDstK rO (preOutBitsFn (coinFn δ)) 40 Nat.le.refl δ
  have hrAuxOutEq (b : Fin 10) : rAuxOut b = rWork ⟨165 + b.val, by omega⟩ :=
    congrArg rTot.wires (congrArg rScrCompact1493 (Fin.ext (by simp [QRegister.block_apply_val])))
  have hrAuxScrEq (a : Fin 24) : rAuxScr a = rWork ⟨175 + a.val, by omega⟩ :=
    congrArg rTot.wires (congrArg rScrCompact1493 (Fin.ext (by simp [QRegister.block_apply_val])))
  have hrRtL4Eq (b : Fin 4) : rRtL4 b = rWork ⟨199 + b.val, by omega⟩ :=
    congrArg rTot.wires (congrArg rScrCompact1493 (Fin.ext (by simp [QRegister.block_apply_val])))
  have hrIONe (i : Fin (41 + 165)) (q : Fin 40) : rI i ≠ rO q :=
    fun e ↦
        innerCoin_ne_out40 165 rAmb i q (e.trans (congrArg rTot.wires (rCoinOut40_rW165_eq q).symm))
  have hrIEq (i : Fin (41 + 165)) : rI i =
      if h : i.val < 41 then rTot (rOuter41Layout ⟨i.val, h⟩) else rTot (rScrCompact1493 ⟨i.val -
          41, by omega⟩) := by
    rw [show rI i = rTot (rCoinInner 165 rW165 i) from rfl, rCoinInner_rW165_eq i]
    split_ifs <;> rfl
  have hScrRangeNotI (m : Fin 1493) (hm : 165 ≤ m.val) : rWork m ∉ Set.range rI.wires :=
      fun ⟨i, hi⟩ ↦ by
    rw [hrIEq i] at hi
    split_ifs at hi
    · exact rOuter41_ne_rScrIdx_qromOpt _ m (rTot.wires.injective hi)
    · exact absurd (congrArg Fin.val (rScrCompact1493.wires.injective (rTot.wires.injective hi)))
          (by (try dsimp); omega)
  have hrINotAuxOut (i : Fin (41 + 165)) (b : Fin 10) : rI i ≠ rAuxOut b :=
    fun e ↦
        hScrRangeNotI ⟨165 + b.val, by omega⟩ (by (try dsimp); omega) ⟨i, e.trans (hrAuxOutEq b)⟩
  have hOWork (q : Fin 40) (w : Fin 1493) : rO q ≠ rWork w := fun e ↦
      rScr_ne_rOut40 w q (rTot.wires.injective e).symm
  have hPreONe (j : Fin 276) (q : Fin 40) : rPre j ≠ rO q :=
      rTot.wires.injective.ne (rPreFwdRtW300_ne_rOut40 j q)
  have hcUpdO (q : Fin 40) (δ : BitAssignment n)
      (b : ZMod 2) : coinFn (Function.update δ (rO q) b) = coinFn δ :=
    coinOfAmb_congr rTot _ _ fun k ↦
        Function.update_of_ne (rTot.wires.injective.ne (rOuter41_ne_rOut40 k q)) _ _
  have hCoinPre (δ : BitAssignment n) (_ : ∀ q, δ (rWork q) = 0) (k : Fin 41) :
      basePre δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0 := by
    have hw : rPre ⟨k.val, by omega⟩ = rTot (rOuter41Layout k) := by
      change rTot (preFwdWireFnRtW300 _) = _
      dsimp [preFwdWireFnRtW300]
      rw [_root_.dite_eq_left k.isLt]
    exact (congrArg δ hw).trans (coinOfAmb_bit rTot δ k)
  have hCoinPost (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (k : Fin 41) :
      basePost δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0 :=
    (xorDstK_outside _ _ _ _ _ fun q ↦ hPreONe _ q).trans (hCoinPre δ hz k)
  have hClnPre (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0)
      (i : Fin 235) : basePre δ (rPreTail215 rPre i) = 0 := by
    obtain ⟨q, hq⟩ : ∃ q : Fin 1493, rPreTail215 rPre i = rWork q := by
      change ∃ q : Fin 1493, rTot (preFwdWireFnRtW300 ⟨41 + i.val, _⟩) = rTot (rScrCompact1493 q)
      dsimp only [preFwdWireFnRtW300]
      rw [_root_.dite_eq_right (by omega)]
      split_ifs <;> exact ⟨_, rfl⟩
    exact (congrArg δ hq).trans (hz q)
  have hClnPost (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0)
      (i : Fin 235) : basePost δ (rPreTail215 rPre i) = 0 :=
    (xorDstK_outside _ _ _ _ _ fun q ↦ hPreONe _ q).trans (hClnPre δ hz i)
  obtain ⟨hAnd6, _, hVP6⟩ := compileXagRange_range_spec 163 140 146 fgates163 6 (by decide) le_rfl
  obtain ⟨hAnd14, _, hVP14⟩ := compileXagRange_spec 163 149 fgates163 14 (by decide)
  have hWorkOutPre (k : ℕ) (hk139 : 139 ≤ k) (hk197 : k < 197) (idx : Fin 235) :
      rWork ⟨k, by omega⟩ ≠ rPreTail215 rPre idx := fun e ↦ by
    have he0 : rScrCompact1493 ⟨k, by omega⟩ = preFwdWireFnRtW300 ⟨41 + idx.val, _⟩ :=
        rTot.wires.injective e
    dsimp only [preFwdWireFnRtW300] at he0
    rw [_root_.dite_eq_right (by omega)] at he0
    split_ifs at he0 <;> exact absurd (congrArg Fin.val (rScrCompact1493.wires.injective he0))
        (by (try dsimp); omega)
  have hClnTail139 (base : BitAssignment n → BitAssignment n)
      (hMidZero : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ q : Fin 1493, 139 ≤ q.val → q.val < 165 →
          base δ (rWork q) = 0)
      (u : Fin 206) (hu : u ∈ sXag 163 139) (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) :
      stAtRt rPre coinFn base m25Prefix sRtPrefix δ (rI u) = 0 := by
    rcases Finset.mem_image.mp hu with ⟨j, hjF, rfl⟩
    have hjGe : 139 ≤ j.val := (Finset.mem_filter.mp hjF).2
    have huEq : rI (wXagGate 163 j) = rWork ⟨j.val, by omega⟩ :=
      (hrIEq (wXagGate 163 j)).trans ((_root_.dite_eq_right
          (by (try dsimp [wXagGate]); omega)).trans
        (congrArg rTot.wires (congrArg rScrCompact1493
            (Fin.ext (by (try dsimp [wXagGate]); omega)))))
    rw [huEq,
        stAtRt_apply_outside rPre coinFn base m25Prefix sRtPrefix δ (hWorkOutPre j.val hjGe
        (by omega))]
    exact hMidZero δ hz ⟨j.val, by omega⟩ hjGe (by (try dsimp); omega)
  have hzPost (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0)
      (q : Fin 1493) : basePost δ (rWork q) = 0 :=
    (xorDstK_outside _ _ _ _ _ fun j e ↦ hOWork j q e.symm).trans (hz q)
  have hMidZeroPre (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (q : Fin 1493)
      (_ : 139 ≤ q.val) (_ : q.val < 165) :
      basePre δ (rWork q) = 0 := hz q
  have hMidZeroPost (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (q : Fin 1493)
      (_ : 139 ≤ q.val) (_ : q.val < 165) :
      basePost δ (rWork q) = 0 := hzPost δ hz q
  have hInput139 (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0)
      (hMZ : ∀ q : Fin 1493, 139 ≤ q.val → q.val < 165 → base δ (rWork q) = 0) :
      (fun i : Fin (41 + 165) ↦ stAtRt rPre coinFn base m25Prefix sRtPrefix δ (rI i)) =
        domZeroBits 206 ((compileXag 163 fgates163 139 (by decide)).fwdBits (coinInitBits 165
            (coinFn δ))) := by
    let c := coinFn δ
    have hInv139 := (xagEnv_invariant c 163 fgates163 139 (by decide)).2.2
    funext i
    dsimp only [domZeroBits]
    rw [hInv139 i, ← env139_eq_fwd163 c]
    by_cases hi41 : i.val < 41
    · have hw : rI i = rPre ⟨i.val, by omega⟩ := by
        rw [hrIEq i, _root_.dite_eq_left hi41]
        change _ = rTot (preFwdWireFnRtW300 _)
        dsimp [preFwdWireFnRtW300]
        rw [_root_.dite_eq_left hi41]
      rw [_root_.ite_eq_right (by omega), hw,
          stAtRt_apply_rPre rPre coinFn base m25Prefix sRtPrefix δ hC,
          _root_.ite_eq_left (by omega)]
      dsimp only [pre256BitsRt]
      rw [_root_.ite_eq_left hi41, ← env139_coinBit c ⟨i.val, hi41⟩]
    · by_cases hi180 : i.val < 41 + 139
      · have hw : rI i = rPre ⟨i.val, by omega⟩ := by
          rw [hrIEq i, _root_.dite_eq_right hi41]
          change _ = rTot (preFwdWireFnRtW300 _)
          dsimp [preFwdWireFnRtW300]
          rw [_root_.dite_eq_right hi41, _root_.dite_eq_left (by omega)]
        rw [hw, stAtRt_apply_rPre rPre coinFn base m25Prefix sRtPrefix δ hC,
            _root_.ite_eq_left hi180]
        dsimp only [pre256BitsRt]
        rw [_root_.ite_eq_right hi41, _root_.ite_eq_left (by omega), m25Prefix_testBit (i.val - 41)
            (by omega)]
        by_cases hdom : i.val = 67 ∨ i.val = 69
        · rw [_root_.ite_eq_left hdom, decide_eq_false (by omega), Bool.false_and]
          rfl
        · rw [_root_.ite_eq_right hdom, decide_eq_true (by omega), Bool.true_and]
      · rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right hi180, show rI i =
            rWork ⟨i.val - 41, by omega⟩ from (hrIEq i).trans (_root_.dite_eq_right hi41),
          stAtRt_apply_outside rPre coinFn base m25Prefix sRtPrefix δ (hWorkOutPre (i.val - 41)
              (by omega) (by omega))]
        exact hMZ ⟨i.val - 41, by omega⟩ (by (try dsimp); omega) (by (try dsimp); omega)
  let st140Of (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n) :=
    stRt139Step rI rRtL4 (coinFn δ) (stAtRt rPre coinFn base m25Prefix sRtPrefix δ)
  let st149Of (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n) :=
    stepCB rI cpFwdTail6.fwdBits (st140Of base δ)
  let st163Of (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n) :=
    stepCB rI cpFwdTail14.fwdBits (st149Of base δ)
  let st163Pre := st163Of basePre
  let st163Post := st163Of basePost
  have hRead149 (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0)
      (hMZ : ∀ q : Fin 1493, 139 ≤ q.val → q.val < 165 → base δ (rWork q) = 0) :
      (fun i : Fin 206 ↦ st149Of base δ (rI i)) =
        domZeroBits 206 ((compileXag 163 fgates163 149 (by decide)).fwdBits (coinInitBits 165
            (coinFn δ))) := by
    let c := coinFn δ
    have hInv139 := (xagEnv_invariant c 163 fgates163 139 (by decide)).2.2
    have hInv140 := (xagEnv_invariant c 163 fgates163 140 (by decide)).2.2
    have hInv146 := (xagEnv_invariant c 163 fgates163 146 (by decide)).2.2
    have hInv149 := (xagEnv_invariant c 163 fgates163 149 (by decide)).2.2
    have h140_eq_151 : (xagEnv c.val 163 fgates163 140 (by decide)).testBit 181 =
        (e151 c).testBit 181 :=
      (xagEnv_prefix_testBit c.val 163 fgates163 140 (by decide) 163 le_rfl (by decide) 181
          (by decide)).symm.trans
        (e163_testBit_lt193 c 181 (by decide))
    have h149_eq_151 (b : ℕ) (hb : b < 191) :
        (xagEnv c.val 163 fgates163 149 (by decide)).testBit b = (e151 c).testBit b :=
      (xagEnv_prefix_testBit c.val 163 fgates163 149 (by decide) 163 le_rfl (by decide) b
          hb).symm.trans
        (e163_testBit_lt193 c b (by omega))
    let β₁ : BitAssignment 206 := fun j ↦ st140Of base δ (rI j)
    let β₂ : BitAssignment 206 :=
        domZeroBits 206 ((compileXag 163 fgates163 140 (by decide)).fwdBits (coinInitBits 165 c))
    have hβ₁ZeroGe (j : Fin 206) (hj : 180 ≤ j.val)
        (h0 : j.val ≠ 180) (h7 : j.val ≠ 187) (h8 : j.val ≠ 188) (h9 : j.val ≠ 189) : β₁ j = 0 := by
      dsimp only [β₁, st140Of]
      rw [stRt139Step_rI_other rI rRtL4 hIRtL4 c _ j h0 h7 h8 h9,
          congrFun (hInput139 base δ hC hMZ) j]
      dsimp only [domZeroBits]
      rw [_root_.ite_eq_right (by omega), hInv139 j, _root_.ite_eq_right (by omega)]
    have hβ₂ZeroGe (j : Fin 206) (hj : 181 ≤ j.val) : β₂ j = 0 := by
      dsimp only [β₂, domZeroBits]
      rw [_root_.ite_eq_right (by omega), hInv140 j, _root_.ite_eq_right (by omega)]
    have hEqLt181 (j : Fin 206) (hj : j.val < 41 + 140) : β₁ j = β₂ j := by
      by_cases hjEq : j.val = 180
      · rw [show j = ⟨180, by decide⟩ from Fin.ext hjEq]
        dsimp only [β₁, β₂, st140Of, domZeroBits]
        rw [_root_.ite_eq_right (by decide : ¬ ((180 : ℕ) = 67 ∨ 180 = 69)),
            hInv140 ⟨180, by decide⟩, _root_.ite_eq_left (by decide : 180 < 41 + 140)]
        exact (stRt139Step_hW rI rRtL4 c _ 0).trans
          (congrArg (fun b : Bool ↦ if b then (1 : ZMod 2) else 0) h140_eq_151.symm)
      · dsimp only [β₁, β₂, st140Of]
        rw [stRt139Step_rI_other rI rRtL4 hIRtL4 c _ j hjEq (by omega) (by omega) (by omega),
          congrFun (hInput139 base δ hC hMZ) j]
        dsimp only [domZeroBits]
        by_cases hdom : j.val = 67 ∨ j.val = 69
        · rw [_root_.ite_eq_left hdom, _root_.ite_eq_left hdom]
        · rw [_root_.ite_eq_right hdom, _root_.ite_eq_right hdom, hInv139 j, hInv140 j,
              _root_.ite_eq_left (by omega), _root_.ite_eq_left hj,
            (xagEnv_prefix_testBit c.val 163 fgates163 139 (by decide) 140 (by decide) (by decide)
                (1 + j.val) (by omega)).symm]
    obtain ⟨hCongrLt, hCongrGe⟩ := fwdBits_compileXagRange_congr 163 140 fgates163 β₁ β₂ hEqLt181
      (hβ₁ZeroGe (wXagA 163) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hβ₁ZeroGe (wXagB 163) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hβ₂ZeroGe (wXagA 163) (by decide)) (hβ₂ZeroGe (wXagB 163) (by decide)) 6 (by decide)
      (fun k hk ↦ hβ₁ZeroGe (wXagGate 163 ⟨140 + k, by omega⟩)
        (by (try dsimp [wXagGate]); omega) (by (try dsimp [wXagGate]); omega)
        (by (try dsimp [wXagGate]); omega) (by (try dsimp [wXagGate]); omega)
        (by (try dsimp [wXagGate]); omega))
      (fun k hk ↦ hβ₂ZeroGe (wXagGate 163 ⟨140 + k, by omega⟩)
          (by (try dsimp [wXagGate]); omega))
    have hDom6 := fwdBits_compileXagRange_domZero 163 140 fgates163
      (by decide) (by decide) (by decide) c 6 (by decide) fun j hj ↦ fgates163_tail6_dom ⟨j, hj⟩
    funext i
    dsimp only [st149Of, stepCB]
    rw [writeReg_apply_reg]
    change cpFwdTail6.fwdBits β₁ i = _
    dsimp only [cpFwdTail6]
    by_cases hi187 : i.val < 41 + (140 + 6)
    · rw [hCongrLt i hi187, congrFun hDom6 i]
      dsimp only [domZeroBits]
      by_cases hdom : i.val = 67 ∨ i.val = 69
      · rw [_root_.ite_eq_left hdom, _root_.ite_eq_left hdom]
      · rw [_root_.ite_eq_right hdom, _root_.ite_eq_right hdom, hInv146 i, hInv149 i,
          _root_.ite_eq_left (by omega : i.val < 41 + 146),
              _root_.ite_eq_left (by omega : i.val < 41 + 149),
          (xagEnv_prefix_testBit c.val 163 fgates163 146 (by decide) 149 (by decide) (by decide)
              (1 + i.val) (by omega)).symm]
    · rw [(hCongrGe i (by omega)).1]
      dsimp only [domZeroBits]
      rw [_root_.ite_eq_right (by omega), hInv149 i]
      by_cases hiH : ∃ b : Fin 4, 0 < b.val ∧ i = rt139HIdx b
      · obtain ⟨b, hbPos, rfl⟩ := hiH
        have hbBounds : 187 ≤ (rt139HIdx b).val ∧ (rt139HIdx b).val < 41 + 149 := by
          fin_cases b <;> first | exact absurd rfl (Nat.ne_of_gt hbPos) | decide
        rw [_root_.ite_eq_left hbBounds.2]
        dsimp only [β₁, st140Of]
        rw [stRt139Step_hW rI rRtL4 c _ b]
        change (if (e151 c).testBit (1 + (rt139HIdx b).val) then (1 : ZMod 2) else 0) = _
        rw [h149_eq_151 (1 + (rt139HIdx b).val) (by omega)]
      · have hNe : i.val ≠ 187 ∧ i.val ≠ 188 ∧ i.val ≠ 189 :=
          ⟨fun h ↦ hiH ⟨1, by decide, Fin.ext h⟩,
           fun h ↦ hiH ⟨2, by decide, Fin.ext h⟩,
           fun h ↦ hiH ⟨3, by decide, Fin.ext h⟩⟩
        rw [_root_.ite_eq_right (by omega)]
        exact hβ₁ZeroGe i (by omega) (by omega) hNe.1 hNe.2.1 hNe.2.2
  have hReadOf (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0)
      (hMZ : ∀ q : Fin 1493, 139 ≤ q.val → q.val < 165 → base δ (rWork q) = 0) :
      (fun i : Fin 206 ↦ st163Of base δ (rI i)) =
        domZeroBits 206 (pRef163.fwdBits (coinInitBits 165 (coinFn δ))) := by
    funext i
    dsimp only [st163Of, stepCB]
    rw [writeReg_apply_reg, hRead149 base δ hC hMZ]
    exact congrFun (fwdBits_compileXagRange_domZero 163 149 fgates163
      (by decide) (by decide) (by decide) (coinFn δ) 14 (by decide) fun j hj ↦
          fgates163_tail14_dom ⟨j, hj⟩) i
  have hReadPre (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) :
      (fun i : Fin 206 ↦ st163Pre δ (rI i)) =
          domZeroBits 206 (pRef163.fwdBits (coinInitBits 165 (coinFn δ))) :=
    hReadOf basePre δ (hCoinPre δ hz) (hMidZeroPre δ hz)
  have hReadPost (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) :
      (fun i : Fin 206 ↦ st163Post δ (rI i)) =
          domZeroBits 206 (pRef163.fwdBits (coinInitBits 165 (coinFn δ))) :=
    hReadOf basePost δ (hCoinPost δ hz) (hMidZeroPost δ hz)
  have hrSrc193Eq (u : Fin 193) : rSrc193_n u = rI ⟨u.val, by omega⟩ :=
    (congrArg rTot.wires (rSrc214_lt204_eq_rI ⟨0 + u.val, by omega⟩
        (by omega : 0 + u.val < 204))).trans
      (congrArg rI (Fin.ext (Nat.zero_add u.val)))
  have hrSrcEq (u : Fin 192) : rSrc u = rI ⟨u.val, by omega⟩ := hrSrc193Eq ⟨u.val, by omega⟩
  have hSrc139 (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0)
      (hMZ : ∀ q : Fin 1493, 139 ≤ q.val → q.val < 165 → base δ (rWork q) = 0)
      (u : Fin 192) (hu : u.val < 180) :
      stAtRt rPre coinFn base m25Prefix sRtPrefix δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 +
          u.val) then 1 else 0 := by
    rw [hrSrcEq u, congrFun (hInput139 base δ hC hMZ) ⟨u.val, by omega⟩]
    dsimp only [domZeroBits, e151Dom]
    rw [Nat.testBit_and, domKeepMask_testBit (1 + u.val) (by omega)]
    by_cases hdom : u.val = 67 ∨ u.val = 69
    · rw [_root_.ite_eq_left hdom, decide_eq_false (by omega : ¬ (1 + u.val ≠ 68 ∧ 1 + u.val ≠ 70)),
          Bool.and_false]
      rfl
    · rw [_root_.ite_eq_right hdom, decide_eq_true (by omega : 1 + u.val ≠ 68 ∧ 1 + u.val ≠ 70),
          Bool.and_true]
      have h2 := (xagEnv_invariant (coinFn δ) 163 fgates163 139 (by decide)).2.2 ⟨u.val, by omega⟩
      rw [_root_.ite_eq_left (by (try dsimp); omega)] at h2
      have h3 := (xagEnv_prefix_testBit (coinFn δ).val 163 fgates163 139 (by decide) 163 le_rfl
        (by decide) (1 + u.val) (by omega)).symm.trans (e163_testBit_lt193 (coinFn δ) (1 + u.val)
            (by omega))
      exact h2.trans (by rw [h3])
  have hSrc193Of (st : BitAssignment n → BitAssignment n)
      (hRd : ∀ δ, (∀ q, δ (rWork q) = 0) →
        (fun i : Fin 206 ↦ st δ (rI i)) =
            domZeroBits 206 (pRef163.fwdBits (coinInitBits 165 (coinFn δ))))
      (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (u : Fin 193) :
      st δ (rSrc193_n u) = if (e163Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0 := by
    rw [hrSrc193Eq u, congrFun (hRd δ hz) ⟨u.val, by omega⟩]
    dsimp only [domZeroBits, e163Dom]
    rw [Nat.testBit_and, domKeepMask_testBit (1 + u.val) (by omega)]
    by_cases hdom : u.val = 67 ∨ u.val = 69
    · rw [_root_.ite_eq_left hdom, decide_eq_false (by omega), Bool.and_false]
      rfl
    · rw [_root_.ite_eq_right hdom, decide_eq_true (by omega), Bool.and_true]
      have h2 := (xagEnv_invariant (coinFn δ) 163 fgates163 163 le_rfl).2.2 ⟨u.val, by omega⟩
      rw [_root_.ite_eq_left (by (try dsimp); omega)] at h2
      exact h2
  have hSrc193_163Pre := hSrc193Of st163Pre hReadPre
  have hSrc193_163Post := hSrc193Of st163Post hReadPost
  have hSrc163Pre (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (u : Fin 192) :
      st163Pre δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0 :=
    (hSrc193_163Pre δ hz ⟨u.val,
        by omega⟩).trans (by rw [e163Dom_testBit_lt193 (coinFn δ) (1 + u.val) (by omega)])
  have hWorkStAtZero (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0)
      (k : ℕ) (hk165 : 165 ≤ k) (hk203 : k < 203) (hbz : base δ (rWork ⟨k, by omega⟩) = 0) :
      stAtRt rPre coinFn base m25Prefix sRtPrefix δ (rWork ⟨k, by omega⟩) = 0 := by
    by_cases hk197 : k < 197
    · exact (stAtRt_apply_outside rPre coinFn base m25Prefix sRtPrefix δ (hWorkOutPre k (by omega)
          hk197)).trans hbz
    · rw [show rWork ⟨k, by omega⟩ = rPre ⟨180 + (k - 197), by omega⟩ from
        congrArg rTot.wires (rScrCompact1493_eq_rPreFwdRtW300_ge197 k hk197 hk203),
        stAtRt_apply_rPre rPre coinFn base m25Prefix sRtPrefix δ hC]
      dsimp only [pre256BitsRt]
      rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega),
          _root_.ite_eq_left (by omega)]
  have hWork163Zero (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0)
      (k : ℕ) (hk165 : 165 ≤ k) (hk199 : k < 199) (hbz : base δ (rWork ⟨k, by omega⟩) = 0) :
      st163Of base δ (rWork ⟨k, by omega⟩) = 0 := by
    have hNotI (i : Fin 206) : rWork ⟨k, by omega⟩ ≠ rI i := fun e ↦
        hScrRangeNotI ⟨k, by omega⟩ hk165 ⟨i, e.symm⟩
    have hNotRt (b : Fin 4) : rWork ⟨k, by omega⟩ ≠ rRtL4 b := fun e ↦
      absurd (congrArg Fin.val (rScrCompact1493.wires.injective (rTot.wires.injective
          (e.trans (hrRtL4Eq b)))))
        (by (try dsimp); omega)
    dsimp only [st163Of, stepCB, st149Of, st140Of]
    rw [writeReg_apply_of_not_mem _ _ _ _ (hScrRangeNotI ⟨k, by omega⟩ hk165),
      writeReg_apply_of_not_mem _ _ _ _ (hScrRangeNotI ⟨k, by omega⟩ hk165),
      stRt139Step_outside rI rRtL4 (coinFn δ) _ (fun _ ↦ hNotI _) hNotRt]
    exact hWorkStAtZero base δ hC k hk165 (by omega) hbz
  have hClnRt139 (base : BitAssignment n → BitAssignment n)
      (hC : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ k : Fin 41,
        base δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0)
      (hMZ : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ q : Fin 1493, 139 ≤ q.val → q.val < 203 →
          base δ (rWork q) = 0)
      (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) :
      (∀ a : Fin 24, a.val < 4 → stAtRt rPre coinFn base m25Prefix sRtPrefix δ (rAuxScr a) = 0) ∧
      (∀ b : Fin 4, stAtRt rPre coinFn base m25Prefix sRtPrefix δ (rRtL4 b) = 0) ∧
      (∀ b : Fin 4, stAtRt rPre coinFn base m25Prefix sRtPrefix δ (rI (rt139HIdx b)) = 0) := by
    have hHGe180 : ∀ b : Fin 4, 180 ≤ (rt139HIdx b).val := by decide
    refine ⟨fun a ha ↦ (congrArg _ (hrAuxScrEq a)).trans (hWorkStAtZero base δ (hC δ hz)
        (175 + a.val) (by omega) (by omega)
        (hMZ δ hz _ (by (try dsimp); omega) (by (try dsimp); omega))),
      fun b ↦
          (congrArg _ (hrRtL4Eq b)).trans (hWorkStAtZero base δ (hC δ hz) (199 + b.val) (by omega)
          (by omega)
        (hMZ δ hz _ (by (try dsimp); omega) (by (try dsimp); omega))),
      fun b ↦ ?_⟩
    have := hHGe180 b
    rw [congrFun (hInput139 base δ (hC δ hz) fun q h1 h2 ↦ hMZ δ hz q h1 (by omega)) (rt139HIdx b)]
    dsimp only [domZeroBits]
    rw [_root_.ite_eq_right (by omega),
        (xagEnv_invariant (coinFn δ) 163 fgates163 139 (by decide)).2.2 (rt139HIdx b),
        _root_.ite_eq_right (by omega)]
  have hClnTail6 (base : BitAssignment n → BitAssignment n)
      (hMZ : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ q : Fin 1493, 139 ≤ q.val → q.val < 165 →
          base δ (rWork q) = 0)
      (u : Fin 206) (hu : u ∈ sRangeXag 163 140 146) (δ : BitAssignment n)
          (hz : ∀ q, δ (rWork q) = 0) :
      st140Of base δ (rI u) = 0 := by
    rcases Finset.mem_image.mp hu with ⟨j, hjF, rfl⟩
    obtain ⟨hj140, hj146⟩ := (Finset.mem_filter.mp hjF).2
    dsimp only [st140Of]
    rw [stRt139Step_rI_other rI rRtL4 hIRtL4 (coinFn δ) _ (wXagGate 163 j)
      (by (try dsimp [wXagGate]); omega) (by (try dsimp [wXagGate]); omega)
      (by (try dsimp [wXagGate]); omega) (by (try dsimp [wXagGate]); omega)]
    exact hClnTail139 base hMZ (wXagGate 163 j)
      (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, rfl⟩) δ hz
  have hClnTail149 (base : BitAssignment n → BitAssignment n)
      (hC : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ k : Fin 41,
        base δ (rPre ⟨k.val, by omega⟩) = if (coinFn δ).val.testBit k.val then 1 else 0)
      (hMZ : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ q : Fin 1493, 139 ≤ q.val → q.val < 165 →
          base δ (rWork q) = 0)
      (u : Fin 206) (hu : u ∈ sXag 163 149) (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) :
      st149Of base δ (rI u) = 0 := by
    rcases Finset.mem_image.mp hu with ⟨j, hjF, rfl⟩
    have hjGe : 149 ≤ j.val := (Finset.mem_filter.mp hjF).2
    rw [congrFun (hRead149 base δ (hC δ hz) (hMZ δ hz)) (wXagGate 163 j)]
    dsimp only [domZeroBits]
    rw [_root_.ite_eq_right (by (try dsimp [wXagGate]); omega),
      (xagEnv_invariant (coinFn δ) 163 fgates163 149 (by decide)).2.2 (wXagGate 163 j),
      _root_.ite_eq_right (by (try dsimp [wXagGate]); omega)]
  have hClnAuxOf (base : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (hC : ∀ k : Fin 41, base δ (rPre ⟨k.val, by omega⟩) =
          if (coinFn δ).val.testBit k.val then 1 else 0)
      (hzB : ∀ q : Fin 1493, base δ (rWork q) = 0) :
      (∀ i : Fin 24, st163Of base δ (rAuxScr i) = 0) ∧ (∀ b : Fin 10, st163Of base δ (rAuxOut b) =
          0) :=
    ⟨fun i ↦ (congrArg _ (hrAuxScrEq i)).trans (hWork163Zero base δ hC (175 + i.val) (by omega)
        (by omega) (hzB _)),
     fun b ↦
         (congrArg _ (hrAuxOutEq b)).trans (hWork163Zero base δ hC (165 + b.val) (by omega)
         (by omega) (hzB _))⟩
  have hClnAuxPre (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) :=
      hClnAuxOf basePre δ (hCoinPre δ hz) hz
  have hClnAuxPost (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) :=
      hClnAuxOf basePost δ (hCoinPost δ hz) (hzPost δ hz)
  let stRawPre (δ : BitAssignment n) := stAuxChain rAuxOut rAuxScr (coinFn δ) (st163Pre δ) 5 le_rfl
  let stRawPost (δ : BitAssignment n) :=
      stAuxChain rAuxOut rAuxScr (coinFn δ) (st163Post δ) 5 le_rfl
  let stInAux (δ : BitAssignment n) := stDecodeB1Fwd rAuxOut (stRawPre δ)
  let stOutAux (δ : BitAssignment n) := stDecodeB1Fwd rAuxOut (stRawPost δ)
  let stT5 (δ : BitAssignment n) := stTail5Aux rO (coinFn δ) (stInAux δ) 5 le_rfl
  let stHk (δ : BitAssignment n) := stHk01 rO (coinFn δ) (stT5 δ)
  have hSrcInAux (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (u : Fin 192) :
      stInAux δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0 :=
    (stDecodeB1Fwd_outside rAuxOut (stRawPre δ) fun g ↦ hSrcAuxOut u g).trans
      ((stAuxChain_outside rAuxOut rAuxScr (coinFn δ) (st163Pre δ)
        (fun g ↦ hSrcAuxOut u g) (fun a ↦ hSrcAuxScr u a) 5 le_rfl).trans (hSrc163Pre δ hz u))
  have hSrc214InAux (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (u : Fin 214) :
      stInAux δ (rSrc214_n u) = if src214Bit (coinFn δ) u then 1 else 0 := by
    let c := coinFn δ
    by_cases hu192 : u.val < 192
    · rw [show rSrc214_n u =
          rSrc ⟨u.val, hu192⟩ from congrArg rSrc214_n (Fin.ext (Nat.zero_add u.val).symm),
        hSrcInAux δ hz ⟨u.val, hu192⟩, show src214Bit (coinFn δ) u =
            _ from _root_.ite_eq_left hu192]
    · by_cases hu204 : u.val < 204
      · rw [show rSrc214_n u =
            rI ⟨u.val, by omega⟩ from congrArg rTot.wires (rSrc214_lt204_eq_rI u hu204)]
        dsimp only [stInAux, stRawPre]
        rw [stDecodeB1Fwd_outside rAuxOut _ (fun g ↦ hrINotAuxOut _ g),
          stAuxChain_outside rAuxOut rAuxScr c (st163Pre δ) (fun g ↦ hrINotAuxOut _ g)
              (fun a ↦ hIScr _ a) 5 le_rfl,
          congrFun (hReadPre δ hz) ⟨u.val, by omega⟩]
        dsimp only [domZeroBits]
        rw [_root_.ite_eq_right (by omega)]
        have h2 := (xagEnv_invariant c 163 fgates163 163 le_rfl).2.2 ⟨u.val, by omega⟩
        rw [_root_.ite_eq_left (by (try dsimp); omega)] at h2
        have hBit : src214Bit c u = (e163 c).testBit (1 + u.val) := by
          dsimp only [src214Bit]
          rw [_root_.ite_eq_right hu192, show 1 + u.val = 42 + (u.val - 41) by omega,
            e163_gate_eq_bOf c (u.val - 41) (by omega) (by omega)]
        exact h2.trans (congrArg (fun b : Bool ↦ if b then (1 : ZMod 2) else 0) hBit.symm)
      · let bIdx : Fin 10 := ⟨u.val - 204, by omega⟩
        have hEqW : rSrc214_n u = rAuxOut bIdx :=
          (congrArg rSrc214_n
            (Fin.ext (by (try dsimp [bIdx]); omega) : u = ⟨204 + bIdx.val,
                by (try dsimp [bIdx]); omega⟩)).trans
            (congrArg rTot.wires (rSrc214_ge204_eq_auxOut bIdx))
        rw [hEqW, show stInAux δ (rAuxOut bIdx) = auxDecBitVal c bIdx from
          stDecodeB1Fwd_rAuxOut_eq rAuxOut c (stRawPre δ)
            (fun g ↦
                stAuxChain_rAuxOut_lt rAuxOut rAuxScr hAuxOutScr c (st163Pre δ) g 5 le_rfl
                (by omega)) bIdx]
        dsimp only [auxDecBitVal, bIdx]
        rw [show src214Bit (coinFn δ) u =
            (bOf c (fgates173At (163 + (u.val - 204))).1 &&
                bOf c (fgates173At (163 + (u.val - 204))).2) by
          dsimp only [src214Bit, c]
          rw [_root_.ite_eq_right hu192, show u.val - 41 = 163 + (u.val - 204) by omega]]
  have sTail5 : SubspaceStep (mkKetOpW rWork stInAux (fun _ ↦ 0)) (mkKetOpW rWork stT5 (fun _ ↦ 0))
      (.circuit (cTail5XorAux rSrc rO hSrcO 5 le_rfl) : DynamicCircuit Var n) :=
    step_circ_mkKetOpW rWork stInAux stT5 _ _ _
      (mkKetOpW_mul_ket_eq rWork _ _ _ _ fun δ hz ↦
        ket_cTail5XorAux rSrc rO hSrcO (coinFn δ) (stInAux δ) (hSrcInAux δ hz) 5 le_rfl)
  have hPreOId (q : Fin 40) (δ : BitAssignment n) : st163Pre δ (rO q) = δ (rO q) := by
    dsimp only [st163Pre, st163Of, st149Of, st140Of, stepCB]
    rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ hrIONe i q hi),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ hrIONe i q hi),
      stRt139Step_outside rI rRtL4 (coinFn δ) _ (fun _ ↦ (hrIONe _ q).symm)
          (fun b ↦ (hRtL4O b q).symm),
      stAtRt_apply_outside rPre coinFn basePre m25Prefix sRtPrefix δ fun _ e ↦ hPreONe _ q e.symm]
  have stepCB_upd_outside_rI (cp : ComputeProg 206) (γ : BitAssignment n) (q : Fin 40)
      (b : ZMod 2) :
      stepCB rI cp.fwdBits (Function.update γ (rO q) b) = Function.update (stepCB rI cp.fwdBits γ)
          (rO q) b := by
    dsimp only [stepCB]
    have hInSame : (fun i : Fin 206 ↦ Function.update γ (rO q) b (rI i)) = fun i ↦ γ (rI i) :=
      funext fun i ↦ Function.update_of_ne (hrIONe i q) _ _
    funext x
    by_cases hxI : x ∈ Set.range rI.wires
    · obtain ⟨i, rfl⟩ := hxI
      rw [Function.update_of_ne (hrIONe i q), writeReg_apply_reg, writeReg_apply_reg, hInSame]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hxI]
      by_cases hxEq : x = rO q
      · subst hxEq
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hxEq, Function.update_of_ne hxEq,
            writeReg_apply_of_not_mem _ _ _ _ hxI]
  have hPreUpdO (q : Fin 40) (δ : BitAssignment n) (b : ZMod 2) (hz : ∀ w, δ (rWork w) = 0) :
      st163Pre (Function.update δ (rO q) b) = Function.update (st163Pre δ) (rO q) b := by
    have hzUpd (w : Fin 1493) : Function.update δ (rO q) b (rWork w) = 0 :=
      (Function.update_of_ne (hOWork q w).symm _ _).trans (hz w)
    have hStAtEq : stAtRt rPre coinFn basePre m25Prefix sRtPrefix (Function.update δ (rO q) b) =
        Function.update (stAtRt rPre coinFn basePre m25Prefix sRtPrefix δ) (rO q) b := by
      funext x
      by_cases hxEq : x = rO q
      · subst hxEq
        rw [Function.update_self,
            stAtRt_apply_outside rPre coinFn basePre m25Prefix sRtPrefix _ fun _ e ↦
            hPreONe _ q e.symm]
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hxEq]
        by_cases hxPre : ∃ idx : Fin 276, rPre idx = x
        · obtain ⟨idx, rfl⟩ := hxPre
          rw [stAtRt_apply_rPre rPre coinFn basePre m25Prefix sRtPrefix _ (hCoinPre _ hzUpd) idx,
            stAtRt_apply_rPre rPre coinFn basePre m25Prefix sRtPrefix δ (hCoinPre δ hz) idx,
                hcUpdO q δ b]
        · have hxOut (i : Fin 235) : x ≠ rPreTail215 rPre i := fun e ↦ hxPre ⟨_, e.symm⟩
          rw [stAtRt_apply_outside rPre coinFn basePre m25Prefix sRtPrefix _ hxOut,
            stAtRt_apply_outside rPre coinFn basePre m25Prefix sRtPrefix δ hxOut]
          exact Function.update_of_ne hxEq _ _
    dsimp only [st163Pre, st163Of, st149Of, st140Of]
    rw [hStAtEq, hcUpdO q δ b,
      stRt139Step_upd_outside rI rRtL4 (coinFn δ) _ b (fun _ ↦ (hrIONe _ q).symm)
          (fun k ↦ (hRtL4O k q).symm),
      stepCB_upd_outside_rI cpFwdTail6 _ q b, stepCB_upd_outside_rI cpFwdTail14 _ q b]
  have hInAuxOId (q : Fin 40) (δ : BitAssignment n) : stInAux δ (rO q) = δ (rO q) :=
    (stDecodeB1Fwd_outside rAuxOut (stRawPre δ) fun g ↦ (hAuxOutO g q).symm).trans
      ((stAuxChain_outside rAuxOut rAuxScr (coinFn δ) (st163Pre δ)
        (fun g ↦ (hAuxOutO g q).symm) (fun a ↦ (hAuxScrO a q).symm) 5 le_rfl).trans (hPreOId q δ))
  have hT5MidId (j : Fin 32) (δ : BitAssignment n) (_ : ∀ w, δ (rWork w) = 0) :
      stT5 δ (rO ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩) = δ (rO ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩)
          :=
    (stTail5Aux_other_rO rO (coinFn δ) (stInAux δ) ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩ 5 le_rfl
      fun s _ ↦ mid32_ne_tail5 j s).trans (hInAuxOId _ δ)
  have hT5UpdMid (j : Fin 32) (δ : BitAssignment n) (b : ZMod 2) (hz : ∀ w, δ (rWork w) = 0) :
      stT5 (Function.update δ (rO ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩) b) =
        Function.update (stT5 δ) (rO ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩) b := by
    let q : Fin 40 := ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
    dsimp only [stT5, stInAux, stRawPre]
    rw [hcUpdO q δ b, hPreUpdO q δ b hz,
      stAuxChain_upd_outside rAuxOut rAuxScr (coinFn δ) (st163Pre δ) b
        (fun g ↦ (hAuxOutO g q).symm) (fun a ↦ (hAuxScrO a q).symm) 5 le_rfl,
      stDecodeB1Fwd_upd_outside rAuxOut _ b (fun g ↦ (hAuxOutO g q).symm),
      stTail5Aux_upd_other rO (coinFn δ) (stInAux δ) q b 5 le_rfl fun s _ ↦ mid32_ne_tail5 j s]
  have hGat8T5 (δ : BitAssignment n) (hz : ∀ w, δ (rWork w) = 0) (i : Fin 8) : stT5 δ (rGat8 i) =
      0 := by
    have := i.isLt
    dsimp only [stT5, stInAux, stRawPre]
    rw [stTail5Aux_outside_rO rO (coinFn δ) _ (fun q ↦ hGat8O i q) 5 le_rfl,
      stDecodeB1Fwd_outside rAuxOut _ fun g ↦ (hAuxOutGat8 g i).symm]
    by_cases hi4 : i.val < 4
    · have hEq : rGat8 i = rAuxScr ⟨i.val, by omega⟩ := by
        change rTot (gatScr8DomZW298WireFn i) = rTot (rScrCompact1493 ⟨175 + i.val, _⟩)
        dsimp only [gatScr8DomZW298WireFn]
        rw [_root_.ite_eq_left hi4]
      rw [hEq, stAuxChain_rAuxScr_unused rAuxOut rAuxScr hAuxOutScr (coinFn δ) (st163Pre δ)
        ⟨i.val, by omega⟩ 5 le_rfl (Or.inl (by (try dsimp); omega))]
      exact (hClnAuxPre δ hz).1 ⟨i.val, by omega⟩
    · have hNeScr (a : Fin 24) : rGat8 i ≠ rAuxScr a := fun e ↦ by
        have he0 : gatScr8DomZW298WireFn i = rScrCompact1493 ⟨175 + a.val, by omega⟩ :=
            rTot.wires.injective e
        dsimp only [gatScr8DomZW298WireFn] at he0
        rw [_root_.ite_eq_right hi4] at he0
        split_ifs at he0 <;> exact absurd (congrArg Fin.val (rScrCompact1493.wires.injective he0))
            (by (try dsimp); omega)
      rw [stAuxChain_outside rAuxOut rAuxScr (coinFn δ) (st163Pre δ)
          (fun g ↦ (hAuxOutGat8 g i).symm) hNeScr 5 le_rfl]
      by_cases hi6 : i.val < 6
      · let uIdx : Fin 206 := ⟨204 + (i.val - 4), by omega⟩
        have hEqI : rGat8 i = rI uIdx := by
          rw [hrIEq uIdx, _root_.dite_eq_right (by (try dsimp [uIdx]); omega)]
          change rTot (gatScr8DomZW298WireFn i) = _
          dsimp only [gatScr8DomZW298WireFn]
          rw [_root_.ite_eq_right hi4, _root_.ite_eq_left hi6]
          exact congrArg rTot.wires (congrArg rScrCompact1493
              (Fin.ext (by (try dsimp [uIdx]); omega)))
        rw [hEqI, congrFun (hReadPre δ hz) uIdx]
        dsimp only [domZeroBits, pRef163]
        rw [_root_.ite_eq_right (by (try dsimp [uIdx]); omega),
          (xagEnv_invariant (coinFn δ) 163 fgates163 163 le_rfl).2.2 uIdx,
          _root_.ite_eq_right (by (try dsimp [uIdx]); omega)]
      · by_cases hiEq6 : i.val = 6
        · rw [show rGat8 i = rI ⟨67, by decide⟩ by
            rw [hrIEq ⟨67, by decide⟩, _root_.dite_eq_right (by decide)]
            change rTot (gatScr8DomZW298WireFn i) = _
            dsimp only [gatScr8DomZW298WireFn]
            rw [_root_.ite_eq_right hi4, _root_.ite_eq_right hi6, _root_.ite_eq_left hiEq6]]
          exact (congrFun (hReadPre δ hz) ⟨67, by decide⟩).trans (_root_.ite_eq_left (Or.inl rfl))
        · rw [show rGat8 i = rI ⟨69, by decide⟩ by
            rw [hrIEq ⟨69, by decide⟩, _root_.dite_eq_right (by decide)]
            change rTot (gatScr8DomZW298WireFn i) = _
            dsimp only [gatScr8DomZW298WireFn]
            rw [_root_.ite_eq_right hi4, _root_.ite_eq_right hi6, _root_.ite_eq_right hiEq6]]
          exact (congrFun (hReadPre δ hz) ⟨69, by decide⟩).trans (_root_.ite_eq_left (Or.inr rfl))
  have hSrcT5 (δ : BitAssignment n) (hz : ∀ w, δ (rWork w) = 0) (u : Fin 192) :
      stT5 δ (rSrc u) = if (e151Dom (coinFn δ)).testBit (1 + u.val) then 1 else 0 :=
    (stTail5Aux_outside_rO rO (coinFn δ) (stInAux δ)
        (fun q ↦ hSrcO u q) 5 le_rfl).trans (hSrcInAux δ hz u)
  have sHk :=
      step_pHk01Chunk8 v rWork rSrcDomZ rO rGat7 hSrcGat7 hSrcDomZO hGat7O hOWork coinFn hcUpdO
    stT5 hT5MidId hT5UpdMid
    (fun δ hz u hn67 hn69 ↦ (congrArg (stT5 δ)
        (congrArg rTot.wires (rSrc192DomZ_eq_of_ne u hn67 hn69))).trans (hSrcT5 δ hz u))
    (fun δ hz i ↦ (congrArg (stT5 δ) (rGat7Of8_eq rGat8 i)).trans (hGat8T5 δ hz _))
  have sVal := step_pValPairChainChunk8 v rWork rSrc214DomZ_n rSrcDomZ rO rGat8
    hSrc214DomZO hSrc214Gat8 hSrcGat8 hSrcDomZO hGat8O coinFn stHk
    (fun δ hz u hn67 hn69 ↦ (congrArg (stHk δ)
        (congrArg rTot.wires (rSrc192DomZ_eq_of_ne u hn67 hn69))).trans
      ((stHk01_outside_rO rO (coinFn δ) (stT5 δ) fun q ↦ hSrcO u q).trans (hSrcT5 δ hz u)))
    (fun δ hz u hn67 hn69 ↦ (congrArg (stHk δ)
        (congrArg rTot.wires (rSrc214DomZ_eq_of_ne u hn67 hn69))).trans
      ((stHk01_outside_rO rO (coinFn δ) (stT5 δ) fun q ↦ hSrc214O u q).trans
        ((stTail5Aux_outside_rO rO (coinFn δ) (stInAux δ)
            (fun q ↦ hSrc214O u q) 5 le_rfl).trans (hSrc214InAux δ hz u))))
    (fun δ hz i ↦ (stHk01_outside_rO rO (coinFn δ)
        (stT5 δ) fun q ↦ hGat8O i q).trans (hGat8T5 δ hz i))
    16 le_rfl
  have hPrePostOffO (δ : BitAssignment n) (hz : ∀ w, δ (rWork w) = 0) (x : Wire n)
      (hxNotO : ∀ q : Fin 40, x ≠ rO q) :
      st163Pre δ x = st163Post δ x := by
    by_cases hxI : ∃ i : Fin 206, rI i = x
    · obtain ⟨i, rfl⟩ := hxI
      exact (congrFun (hReadPre δ hz) i).trans (congrFun (hReadPost δ hz) i).symm
    · have hxNeI (i : Fin 206) : x ≠ rI i := fun e ↦ hxI ⟨i, e.symm⟩
      dsimp only [st163Pre, st163Post, st163Of, st149Of, stepCB]
      rw [writeReg_apply_of_not_mem _ _ _ _ hxI, writeReg_apply_of_not_mem _ _ _ _ hxI,
        writeReg_apply_of_not_mem _ _ _ _ hxI, writeReg_apply_of_not_mem _ _ _ _ hxI]
      by_cases hxRt : ∃ b : Fin 4, rRtL4 b = x
      · obtain ⟨b, rfl⟩ := hxRt
        dsimp only [st140Of]
        rw [stRt139Step_lW rI rRtL4 hIRtL4, stRt139Step_lW rI rRtL4 hIRtL4]
      · have hxNeRt (b : Fin 4) : x ≠ rRtL4 b := fun e ↦ hxRt ⟨b, e.symm⟩
        dsimp only [st140Of]
        rw [stRt139Step_outside rI rRtL4 (coinFn δ) _ (fun _ ↦ hxNeI _) hxNeRt,
          stRt139Step_outside rI rRtL4 (coinFn δ) _ (fun _ ↦ hxNeI _) hxNeRt]
        by_cases hxPre : ∃ idx : Fin 235, rPreTail215 rPre idx = x
        · obtain ⟨idx, rfl⟩ := hxPre
          rw [show rPreTail215 rPre idx = rPre ⟨41 + idx.val, by omega⟩ from
              congrArg rPre (Fin.ext (by simp only [QRegister.block_apply_val])),
            stAtRt_apply_rPre rPre coinFn basePre m25Prefix sRtPrefix δ (hCoinPre δ hz) _,
            stAtRt_apply_rPre rPre coinFn basePost m25Prefix sRtPrefix δ (hCoinPost δ hz) _]
        · have hxOutPre (idx : Fin 235) : x ≠ rPreTail215 rPre idx := fun e ↦ hxPre ⟨idx, e.symm⟩
          rw [stAtRt_apply_outside rPre coinFn basePre m25Prefix sRtPrefix δ hxOutPre,
            stAtRt_apply_outside rPre coinFn basePost m25Prefix sRtPrefix δ hxOutPre]
          exact (xorDstK_outside _ _ _ _ _ hxNotO).symm
  have hPostAuxEq (δ : BitAssignment n) (hz : ∀ w, δ (rWork w) = 0) :
      stValChain rO (coinFn δ) (stHk δ) 16 le_rfl = stOutAux δ := by
    let c := coinFn δ
    funext x
    by_cases hxO : ∃ q : Fin 40, rO q = x
    · obtain ⟨q, rfl⟩ := hxO
      have hNotI : rO q ∉ Set.range rI.wires := fun ⟨i, hi⟩ ↦ hrIONe i q hi
      have hRhs : stOutAux δ (rO q) = δ (rO q) +
          if preCnotBit40 (m40VOpt c) q.val then 1 else 0 := by
        dsimp only [stOutAux, stRawPost, st163Post, st163Of, st149Of, st140Of, stepCB]
        rw [stDecodeB1Fwd_outside rAuxOut _ (fun g ↦ (hAuxOutO g q).symm),
          stAuxChain_outside rAuxOut rAuxScr c _ (fun g ↦ (hAuxOutO g q).symm)
              (fun a ↦ (hAuxScrO a q).symm) 5 le_rfl,
          writeReg_apply_of_not_mem _ _ _ _ hNotI, writeReg_apply_of_not_mem _ _ _ _ hNotI,
          stRt139Step_outside rI rRtL4 c _ (fun _ ↦ (hrIONe _ q).symm) (fun b ↦ (hRtL4O b q).symm),
          stAtRt_apply_outside rPre coinFn basePost m25Prefix sRtPrefix δ fun _ e ↦
              hPreONe _ q e.symm]
        dsimp only [basePost, preOutBitsFn]
        rw [xorDstK_dst, ifp_tw q.isLt]
      rw [hRhs]
      obtain ⟨pz35, pz32, pz34⟩ := preCnotBit40_zeroNErem_pureZero (decodeTier1W11Opt1424Coin c)
      have hPureZ (k : ℕ) (hqk : q.val = k) (hpz : preCnotBit40 (m40VOpt c) k = false)
          (hnm : ∀ j : Fin 32, mid32OutIdx j ≠ k) (hnt : ∀ s : Fin 5, tail5OutIdx s ≠ k) :
          stValChain rO c (stHk δ) 16 le_rfl (rO q) = δ (rO q) +
              if preCnotBit40 (m40VOpt c) q.val then 1 else 0 := by
        rw [stValChain_after_hk_nonmid rO c (stT5 δ) q fun j ↦ hqk.trans_ne (hnm j).symm]
        dsimp only [stT5]
        rw [stTail5Aux_other_rO rO c (stInAux δ) q 5 le_rfl (fun s _ ↦ hqk.trans_ne (hnt s).symm),
            hInAuxOId q δ, hqk, hpz]
        simp
      rcases out40_partition q with hq35 | hq32 | hq34 | ⟨j, hj⟩ | ⟨s, hs⟩
      · exact hPureZ 35 hq35 pz35 (fun j ↦ (mid32OutIdx_ne_pureZero j).1)
            (fun s ↦ (tail5OutIdx_ne_pureZero s).1)
      · exact hPureZ 32 hq32 pz32 (fun j ↦ (mid32OutIdx_ne_pureZero j).2.1)
            (fun s ↦ (tail5OutIdx_ne_pureZero s).2.1)
      · exact hPureZ 34 hq34 pz34 (fun j ↦ (mid32OutIdx_ne_pureZero j).2.2)
            (fun s ↦ (tail5OutIdx_ne_pureZero s).2.2)
      · rw [show q = ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩ from Fin.ext hj.symm,
          stValChain_after_hk_mid32 rO c (stT5 δ) j, hT5MidId j δ hz]
      · rw [show q = ⟨tail5OutIdx s, tail5OutIdx_lt40 s⟩ from Fin.ext hs.symm,
          stValChain_after_hk_nonmid rO c (stT5 δ) _ fun j e ↦ mid32_ne_tail5 j s e.symm]
        dsimp only [stT5]
        rw [stTail5Aux_hit rO c (stInAux δ) s 5 le_rfl s.isLt, hInAuxOId _ δ]
    · have hxNotO (q : Fin 40) : x ≠ rO q := fun e ↦ hxO ⟨q, e.symm⟩
      rw [stValChain_outside_rO rO c (stHk δ) hxNotO 16 le_rfl]
      dsimp only [stHk, stT5, stInAux, stOutAux, stRawPre, stRawPost]
      rw [stHk01_outside_rO rO c _ hxNotO, stTail5Aux_outside_rO rO c _ hxNotO 5 le_rfl]
      exact stDecodeB1Fwd_congr_pred rAuxOut (P := fun y ↦ ∀ q : Fin 40, y ≠ rO q) hAuxOutO _ _
        (stAuxChain_congr_pred rAuxOut rAuxScr c (st163Pre δ) (st163Post δ)
            (hPrePostOffO δ hz) 5 le_rfl) x hxNotO
  have sMidDec := subspaceStep_congr_out
    (PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans sTail5
      (PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans sHk sVal))
    (mkKetOpW_congr rWork hPostAuxEq fun _ _ ↦ rfl)
  have sAux5 :=
      step_wrapAux5 v rWork rSrc193_n rAuxOut rAuxScr hSrc193AuxOut hSrc193AuxScr hAuxOutScr
    coinFn st163Pre st163Post _ hSrc193_163Pre hSrc193_163Post hClnAuxPre hClnAuxPost
    (step_wrapDecodeB1 rWork rAuxOut stRawPre stRawPost _ sMidDec)
  let pCore := DynamicCircuit.seq (.circuit (cTail5XorAux rSrc rO hSrcO 5 le_rfl))
    (.seq (pHk01Chunk8 v rSrcDomZ rO rGat7 hSrcGat7 hGat7O)
      (pValPairChainChunk8 v rSrc214DomZ_n rSrcDomZ rO rGat8 hSrc214DomZO hSrc214Gat8 hSrcGat8
          hGat8O 16 le_rfl))
  let pInTail14 := wrapAuxChain v rSrc193_n rAuxOut rAuxScr hSrc193AuxOut hSrc193AuxScr hAuxOutScr
    (wrapDecodeB1 rAuxOut pCore) 5 le_rfl
  obtain ⟨sTail14, tTail14, fTail14, _⟩ :=
      subspaceStep_wrapOnReg_vprog2 v rWork rI (sXag 163 149) cpFwdTail14 14
    hVP14 hAnd14 (st149Of basePre) (st149Of basePost) (fun _ ↦ 0) (fun _ ↦ 0) pInTail14
    (hClnTail149 basePre hCoinPre hMidZeroPre) (hClnTail149 basePost hCoinPost hMidZeroPost) sAux5
  let pInTail6 := wrapDynOnReg v rI cpFwdTail14 pInTail14
  obtain ⟨sTail6, tTail6, fTail6, _⟩ :=
      subspaceStep_wrapOnReg_vprog2 v rWork rI (sRangeXag 163 140 146) cpFwdTail6 6
    hVP6 hAnd6 (st140Of basePre) (st140Of basePost) (fun _ ↦ 0) (fun _ ↦ 0) pInTail6
    (hClnTail6 basePre hMidZeroPre) (hClnTail6 basePost hMidZeroPost) sTail14
  let pMidRt := wrapDynOnReg v rI cpFwdTail6 pInTail6
  have sRt139 := step_wrapTail139Router4 v rWork rSrc rI rRtL4 rAuxScr
    (fun u ↦ hrSrcEq ⟨u.val, by omega⟩) hSrcI188 hSrcRtL4 hSrcAuxScr hIRtL4 hIScr hRtL4Scr coinFn
    (stAtRt rPre coinFn basePre m25Prefix sRtPrefix)
        (stAtRt rPre coinFn basePost m25Prefix sRtPrefix) pMidRt
    (fun δ hz u hu ↦ hSrc139 basePre δ (hCoinPre δ hz) (hMidZeroPre δ hz) u hu)
    (fun δ hz u hu ↦ hSrc139 basePost δ (hCoinPost δ hz) (hMidZeroPost δ hz) u hu)
    (hClnRt139 basePre hCoinPre fun δ hz q _ _ ↦ hz q)
    (hClnRt139 basePost hCoinPost fun δ hz q _ _ ↦ hzPost δ hz q) sTail6
  let pAfterPre :=
      wrapTail139Router4 v rSrc rI rRtL4 rAuxScr hSrcI188 hSrcRtL4 hSrcAuxScr hIRtL4 hIScr hRtL4Scr
      pMidRt
  obtain ⟨cT5_t, cT5_f⟩ := count_cTail5XorAux rSrc rO hSrcO 5 le_rfl
  obtain ⟨cHk_t, cHk_f⟩ := counts_pHk01Chunk8 v rSrcDomZ rO rGat7 hSrcGat7 hGat7O
  obtain ⟨cVal_t, cVal_f⟩ := counts_pValPairChainChunk8 v rSrc214DomZ_n rSrcDomZ rO rGat8
    hSrc214DomZO hSrc214Gat8 hSrcGat8 hGat8O 16 le_rfl
  obtain ⟨cDec_t, cDec_f⟩ := counts_wrapDecodeB1 rAuxOut pCore
  obtain ⟨cAux_t, cAux_f⟩ :=
      counts_wrapAuxChain v rSrc193_n rAuxOut rAuxScr hSrc193AuxOut hSrc193AuxScr hAuxOutScr
    (wrapDecodeB1 rAuxOut pCore) 5 le_rfl
  obtain ⟨cRt_t, cRt_f⟩ := counts_wrapTail139Router4 v rSrc rI rRtL4 rAuxScr
    hSrcI188 hSrcRtL4 hSrcAuxScr hIRtL4 hIScr hRtL4Scr pMidRt
  have tAfterPreEq : pAfterPre.count .T = 228 := by
    dsimp only [pAfterPre, pMidRt, pInTail6, pInTail14, pCore,
        DynamicCircuit.count] at cRt_t tTail6 tTail14 cAux_t cDec_t ⊢
    rw [cRt_t, tTail6, tTail14, cAux_t, cDec_t, cT5_t, cHk_t, cVal_t]
  have fAfterPreEq : pAfterPre.count .TOFF = 0 := by
    dsimp only [pAfterPre, pMidRt, pInTail6, pInTail14, pCore,
        DynamicCircuit.count] at cRt_f fTail6 fTail14 cAux_f cDec_f ⊢
    rw [cRt_f, fTail6, fTail14, cAux_f, cDec_f, cT5_f, cHk_f, cVal_f]
  obtain ⟨sFull, tFull, fFull, _⟩ := step_wrapPrefixRt_clean v rWork rPre coinFn basePre basePost
    (fun _ ↦ 0) (fun _ ↦ 0) hCoinPre hCoinPost hClnPre hClnPost pAfterPre sRt139
  refine ⟨sFull, ?_, ?_⟩
  · dsimp only [pFwdInnerRt730]
    rw [tFull, tAfterPreEq]
  · dsimp only [pFwdInnerRt730]
    rw [fFull, fAfterPreEq]

def pFwdRt730 {Var : Type} {n : ℕ} (v : Var) (rTot : QRegister dLayout n) : DynamicCircuit Var n :=
  let rO := rTot.compose rOut40Layout
  .seq (.circuit (PhotochemistrySolution.Stage1AsymRevEngine.cPreCnot40 rO))
    (.seq (pFwdInnerRt730 v rTot)
      (.circuit (PhotochemistrySolution.Stage1AsymRevEngine.cPreCnot40 rO)))

theorem dw_pFwdRt730 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (rTot : QRegister dLayout n)
    (hrPre : ∀ j : Fin 276, S ((rTot.compose rPreFwdRtW300) j)) (hrAmb : ∀ j : Fin (81 + (165 + 0)),
    S ((rTot.compose rW165) j)) (hrAuxOut : ∀ b : Fin 10, S ((rTot.compose rAuxOut10) b))
    (hrAuxScr : ∀ i : Fin 24, S ((rTot.compose rAuxScr24) i))
    (hrRtL4 : ∀ b : Fin 4, S ((rTot.compose rRt139L4) b))
    (hrGat8 : ∀ i : Fin 8, S ((rTot.compose rGatScr8DomZW298) i)) : DynWires S (pFwdRt730 v rTot)
    := by
  let rAmb := rTot.compose rW165; let rO := rTot.compose rOut40Layout
  have hOS : ∀ q : Fin 40, S (rO q) := fun q ↦ by
    have hEq : rO q = rAmb (QRegister.block 41 40 (outBlk_le 165) q) :=
        congrArg rTot.wires (rCoinOut40_rW165_eq q).symm
    rw [hEq]; exact hrAmb _
  have cwPre :=
      Stage1AsymRevEngine.circWires_cPreCnot40 rO hOS; exact ⟨cwPre,
      ⟨dw_pFwdInnerRt730 v rTot hrPre hrAmb hrAuxOut hrAuxScr hrRtL4 hrGat8, cwPre⟩⟩
set_option maxHeartbeats 2000000 in
-- 730-T forward Stage-1 W-router step and gate counts
theorem step_and_counts_pFwdRt730 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rTot : QRegister dLayout n) :
    CleanWorkStep (rTot.compose rScrCompact1493) (rTot.embedUnitary oRef209.uLocal)
    (pFwdRt730 v rTot) ∧ CleanWorkStep (rTot.compose rScrCompact1493)
    ((rTot.embedUnitary oRef209.uLocal)⁻¹) (pFwdRt730 v rTot) ∧ (pFwdRt730 v rTot).count .T = 730 ∧
    (pFwdRt730 v rTot).count .TOFF = 0 := by
  let rWork := rTot.compose rScrCompact1493; let rO := rTot.compose rOut40Layout;
  let coinFn := coinOfAmb rTot
  let outBitsFn (c : Fin (2 ^ 41)) (q : Fin 40) : ZMod 2 :=
      if (m40VOpt c).testBit q.val then 1 else 0
  let preOutBitsFn (c : Fin (2 ^ 41)) (q : Fin 40) : ZMod 2 :=
      if preCnotBit40 (m40VOpt c) q.val then 1 else 0
  let R₀ := mkKetOpW rWork (fun δ ↦ δ) (fun _ ↦ 0)
  let R_mid :=
      mkKetOpW rWork (fun δ ↦ xorDstK rO (preOutBitsFn (coinFn δ)) 40 Nat.le.refl δ) (fun _ ↦ 0)
  let R_out :=
      mkKetOpW rWork (fun δ ↦ xorDstK rO (outBitsFn (coinFn δ)) 40 Nat.le.refl δ) (fun _ ↦ 0)
  let U_pre := (PhotochemistrySolution.Stage1AsymRevEngine.cPreCnot40 rO).eval.1
  have hWorkNotO : ∀ (w : Fin 1493) (u : Fin 40), rWork w ≠ rO u := fun w u ↦
      rTot.wires.injective.ne (rScr_ne_rOut40 w u)
  obtain ⟨sInner, tInner, fInner⟩ := step_and_counts_pFwdInnerRt730 v rTot
  have hSamePre (δ : BitAssignment n) (w : Fin 1493) : stPreCnot rO δ (rWork w) = δ (rWork w) :=
    (stPreCnot_spec rO δ).1 (rWork w) (hWorkNotO w)
  have hCommR0 : U_pre * R₀ = R₀ * U_pre :=
    matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket,
          ket_cPreCnot40_gen rO δ, mkKetOpW_mulVec_ket]
      by_cases hz : ∀ w : Fin 1493, δ (rWork w) = 0
      · rw [_root_.ite_eq_left hz, Matrix.mulVec_smul, ket_cPreCnot40_gen rO δ,
            _root_.ite_eq_left fun w ↦ (hSamePre δ w).trans (hz w)]
      · rw [_root_.ite_eq_right hz, Matrix.mulVec_zero, _root_.ite_eq_right fun h' ↦ hz fun w ↦
            (hSamePre δ w).symm.trans (h' w)]
  have hConjOut : U_pre * (R_mid * U_pre) = R_out :=
    matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_cPreCnot40_gen rO δ,
          mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
      by_cases hz : ∀ w : Fin 1493, δ (rWork w) = 0
      · rw [_root_.ite_eq_left fun w ↦ (hSamePre δ w).trans (hz w), _root_.ite_eq_left hz,
            Matrix.mulVec_smul, ket_cPreCnot40_gen rO]
        refine congrArg (QubitizationWalkSem.bitSign 0 • ·) (congrArg ket (funext fun x ↦ ?_))
        let δ' := stPreCnot rO δ
        have hcEq : coinFn δ' = coinFn δ :=
          coinOfAmb_congr rTot δ' δ fun k ↦
            (stPreCnot_spec rO δ).1 (rTot (rOuter41Layout k)) fun u ↦
                rTot.wires.injective.ne (rOuter41_ne_rOut40 k u)
        let c := coinFn δ
        let δ'' := xorDstK rO (preOutBitsFn (coinFn δ')) 40 Nat.le.refl δ'
        change stPreCnot rO δ'' x = xorDstK rO (outBitsFn c) 40 Nat.le.refl δ x
        by_cases hxO : ∃ u : Fin 40, rO u = x
        · obtain ⟨u, rfl⟩ := hxO
          have hBit'' (q : Fin 40) :
              bitFnOf40 rO δ'' q.val = preCnotBitFn (fun k ↦ xor (bitFnOf40 rO δ k)
                  ((m40VOpt c).testBit k)) q.val := by
            have hVal'' : δ'' (rO q) =
                if preCnotBitFn (fun k ↦ xor (bitFnOf40 rO δ k)
                    ((m40VOpt c).testBit k)) q.val then 1 else 0 := by
              change xorDstK rO (preOutBitsFn (coinFn δ')) 40 Nat.le.refl (stPreCnot rO δ)
                  (rO q) = _
              rw [hcEq, xorDstK_dst, ifp_tw q.isLt, (stPreCnot_spec rO δ).2 q]
              dsimp only [preOutBitsFn]
              rw [← Stage1AsymRevEngine.rawCnotXorSrcs_preCnot40 (m40VOpt c) q]
              change (if preCnotBitFn (bitFnOf40 rO δ) q.val then (1 : ZMod 2) else 0) +
                (if preCnotBitFn (m40VOpt c).testBit q.val then 1 else 0) = _
              rw [PhotochemistrySolution.Stage1AsymRevEngine.z2_add_ite_xor, ← preCnotBitFn_xor]
            rw [show bitFnOf40 rO δ'' q.val = decide (δ'' (rO q) =
                1) from _root_.dite_eq_left q.isLt, hVal'']
            exact decide_ite_zmod2_eq_one _
          rw [(stPreCnot_spec rO δ'').2 u, preCnotBitFn_congr_lt40 hBit'' u, preCnotBitFn_invol,
            ← Stage1AsymRevEngine.z2_add_ite_xor, ite_bitFnOf40_eq rO δ u, xorDstK_dst,
                ifp_tw u.isLt]
        · have hxNotO (u : Fin 40) : x ≠ rO u := fun e ↦ hxO ⟨u, e.symm⟩
          rw [(stPreCnot_spec rO δ'').1 x hxNotO]
          change xorDstK rO (preOutBitsFn (coinFn δ')) 40 Nat.le.refl (stPreCnot rO δ) x = _
          rw [xorDstK_outside _ _ _ _ _ hxNotO, (stPreCnot_spec rO δ).1 x hxNotO,
              xorDstK_outside _ _ _ _ _ hxNotO]
      · rw [_root_.ite_eq_right fun h' ↦ hz fun w ↦ (hSamePre δ w).symm.trans (h' w),
            _root_.ite_eq_right hz, Matrix.mulVec_zero]
  have sFull : SubspaceStep R₀ R_out (pFwdRt730 v rTot) :=
    PhotochemistrySolution.Stage1AsymRevEngine.subspaceStep_seq_trans
      (subspaceStep_congr_out (subspaceStep_of_circuit (Var :=
          Var) R₀ (Stage1AsymRevEngine.cPreCnot40 rO)) hCommR0)
      (Stage1AsymRevEngine.subspaceStep_seq_trans (subspaceStep_mul_right U_pre sInner)
        (subspaceStep_congr_out
          (subspaceStep_of_circuit (Var := Var) (R_mid * U_pre)
              (Stage1AsymRevEngine.cPreCnot40 rO)) hConjOut))
  let rW211 := rSplitCoinGen 0 211 0 hbLo_211 hbHi_211
  let rAmb211 := rTot.compose rW211
  let rI211 := rCoinInner 211 rAmb211
  have hrO211 : rCoinOut40 211 rAmb211 = rO :=
    QRegister.ext (DFunLike.ext _ _ fun j ↦
        congrArg rTot.wires (splitCoinGen_out40_eq hbLo_211 hbHi_211 j))
  have hrI211Eq (i : Fin (41 + 211)) : rI211 i =
      if h : i.val < 41 then rTot (rOuter41Layout ⟨i.val, h⟩) else rTot (rScrCompact1493 ⟨i.val -
          41, by omega⟩) := by
    have h1 : rCoinInner 211 rW211 i =
        if h : i.val < 41 then rOuter41Layout ⟨i.val, h⟩ else rScrCompact1493 ⟨i.val - 41, by omega⟩
            := by
      change splitCoinGenWireFn 0 211 0 hbLo_211 hbHi_211 (innerIdxCoin 211 i) = _
      have hiv := innerIdxCoin_val 211 i
      by_cases hi : i.val < 41
      · rw [_root_.dite_eq_left hi]
        have hidx : (innerIdxCoin 211 i).val = i.val := (hiv.trans (_root_.ite_eq_left hi))
        dsimp only [splitCoinGenWireFn]
        rw [_root_.dite_eq_left (by omega)]
        exact congrArg rOuter41Layout (Fin.ext hidx)
      · rw [_root_.dite_eq_right hi]
        have hidx : (innerIdxCoin 211 i).val = 40 + i.val := (hiv.trans (_root_.ite_eq_right hi))
        have := i.isLt
        dsimp only [splitCoinGenWireFn]
        rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right (by omega),
            _root_.dite_eq_left (by omega)]
        exact congrArg rScrCompact1493 (Fin.ext (by dsimp; omega))
    rw [show rI211 i = rTot (rCoinInner 211 rW211 i) from rfl, h1]
    split_ifs <;> rfl
  let o := stage1ZeroNEremOracleOfProg pRef209 (sXag 209 0) outs40Tier1Sym96 (sXag_ge41 209 0)
    (compileXag_spec 209 gatesTier1Sym96 209 le_rfl).2.2 (compileXag_spec 209 gatesTier1Sym96
        209 le_rfl).1
  have hemb : rTot.embedUnitary oRef209.uLocal =
      uCoinWrap 211 pRef209 outs40Tier1Sym96 rAmb211 := by
    change rTot.embedUnitary (rW211.embedUnitary (o.u rIdGenW)) = o.u rAmb211
    rw [← rTot.embedUnitary_compose,
      embedUnitary_zeroNErem_of_xorOut40 (le81_coin 211) o _
        (fun r β ↦ ket_uCoinWrap_all 211 pRef209 outs40Tier1Sym96 r β) rAmb211]
  have hInvEq : (rTot.embedUnitary oRef209.uLocal)⁻¹ = rTot.embedUnitary oRef209.uLocal := by
    rw [hemb, uCoinWrap_inv]
  have hOutOpEq : R_out = (rTot.embedUnitary oRef209.uLocal).1 * rWork.basisOutcomeProjector 0 := by
    rw [hemb]
    refine matrix_ext_ket fun δ ↦ ?_
    rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, SelectRefl.ket_basisOutcomeProjector_zero]
    split_ifs with hz
    · rw [ket_uCoinWrap_all 211 pRef209 outs40Tier1Sym96 rAmb211 δ,
        show QubitizationWalkSem.bitSign 0 = 1 from rfl, one_smul]
      change ket (xorDstK rO (outBitsFn (coinFn δ)) 40 Nat.le.refl δ) =
        ket (xorDstK (rCoinOut40 211 rAmb211)
          (coinWrapOutFn 211 pRef209 outs40Tier1Sym96 (fun k ↦ δ (rAmb211 k))) 40 Nat.le.refl δ)
      rw [hrO211]
      refine congrArg ket (congrArg (fun f ↦ xorDstK rO f 40 Nat.le.refl δ)
          (funext fun j ↦ ?_).symm)
      dsimp only [coinWrapOutFn]
      rw [show (fun i : Fin (41 + 211) ↦ δ (rAmb211 (innerIdxCoin 211 i))) =
          coinInitBits 211 (coinFn δ) by
        funext i
        change δ (rI211 i) = _
        rw [hrI211Eq i]
        dsimp only [coinInitBits]
        by_cases hi : i.val < 41
        · rw [_root_.dite_eq_left hi, _root_.ite_eq_left hi]
          exact coinOfAmb_bit rTot δ ⟨i.val, hi⟩
        · rw [_root_.dite_eq_right hi, _root_.ite_eq_right hi]
          exact hz ⟨i.val - 41, by omega⟩]
      exact xag_outParity_eq_of_eval gatesTier1Sym96 outs40Tier1Sym96
          xag_tier1W11Opt1424_eval (coinFn δ) j
    · rw [Matrix.mulVec_zero]
  have hCommAmb : (rTot.embedUnitary oRef209.uLocal).1 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * (rTot.embedUnitary oRef209.uLocal).1 := by
    rw [hemb]
    refine matrix_ext_ket fun β ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero,
      ket_uCoinWrap_all 211 pRef209 outs40Tier1Sym96 rAmb211 β,
      PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
    have hSame (k : Fin 1493) :
        xorDstK (rCoinOut40 211 rAmb211) (coinWrapOutFn 211 pRef209 outs40Tier1Sym96 (fun m ↦
            β (rAmb211 m)))
          40 Nat.le.refl β (rWork k) = β (rWork k) := by
      rw [hrO211]
      exact xorDstK_outside _ _ _ _ _ fun j e ↦ hWorkNotO k j e
    by_cases h0 : ∀ k : Fin 1493, β (rWork k) = 0
    · rw [ifp_tw h0, ket_uCoinWrap_all 211 pRef209 outs40Tier1Sym96 rAmb211 β,
        ifp_tw fun k ↦ (hSame k).trans (h0 k)]
    · rw [ifn_tw h0, Matrix.mulVec_zero, ifn_tw fun h' ↦ h0 fun k ↦ (hSame k).symm.trans (h' k)]
  have cwsFwd : CleanWorkStep rWork (rTot.embedUnitary oRef209.uLocal) (pFwdRt730 v rTot) :=
    cleanWorkStep_of_subspaceStep rWork (rTot.embedUnitary oRef209.uLocal) _ hCommAmb
      (subspaceStep_congr_in (mkKetOpW_id_eq_proj rWork).symm (subspaceStep_congr_out sFull
          hOutOpEq))
  obtain ⟨cPre_t, cPre_f⟩ := PhotochemistrySolution.Stage1AsymRevEngine.count_cPreCnot40 rO
  refine ⟨cwsFwd, hInvEq.symm ▸ cwsFwd, ?_, ?_⟩
  · dsimp only [pFwdRt730, DynamicCircuit.count]
    rw [cPre_t, tInner]
  · dsimp only [pFwdRt730, DynamicCircuit.count]
    rw [cPre_f, fInner]

def o1NucOptWRouter1256Chunk8W300 : Stage1ZeroNEremLayout 0 decodeTier1W11Opt1424Coin where
  tStage1 := 1460
  uLocal := oRef209.uLocal
  fwdAmb := pFwdRt730
  revAmb := pFwdRt730
  step_and_counts := fun v rTot ↦ by
    obtain ⟨cF, cR, tF, fF⟩ := step_and_counts_pFwdRt730 v rTot
    exact ⟨cF, cR, by rw [tF], fF, fF⟩
  comm_off := oRef209.comm_off
  dynWires_active_wIn := fun v rTot hAct ↦ by
    have hd : DynWires _ (pFwdRt730 v rTot) :=
        dw_pFwdRt730 v rTot (fun j ↦ hAct _ (rPreFwdRtW300_active_wIn0 j))
        (fun j ↦ hAct _ (rSplitCoinGen_active_wIn hbLo_165 hbHi_165 hw_165 j))
        (fun b ↦ hAct _ (rAuxOut10_active_wIn0 b)) (fun i ↦ hAct _ (rAuxScr24_active_wIn0 i))
        (fun b ↦ hAct _ (rRt139L4_active_wIn0 b)) (fun i ↦ hAct _ (rGatScr8DomZW298_active_wIn0 i))
    exact ⟨hd, hd⟩
  ket_of_clean := oRef209.ket_of_clean

/--
`1,280-T` (`746` forward + `534` reverse, `0` `.TOFF`, `+0` ancillas, `310 ≤ wWork`)
Multi-`hW` Shared-Prefix (`510 T`) + Two-Wave `cFanout` Mid32 Gather (`236 T`) + Multi-`hW` Reverse
(`534 T`)
`Stage1AsymRevPkg` on `decodeTier1W11Opt1424Coin`.
-/
noncomputable def stage1NucOptWRouter1256Chunk8W300AsymPkg :
    Stage1AsymRevPkg 0 1256 decodeTier1W11Opt1424Coin where
  o1 := o1NucOptWRouter1256Chunk8W300
  revAmb := pRevRt526
  counts := fun v rTot ↦ by
    obtain ⟨_, _, tF, _⟩ := step_and_counts_pFwdRt730 v rTot; obtain ⟨_, tR, fR⟩ :=
        step_and_counts_pRevRt526_rScrLayout v rTot; change (pFwdRt730 v rTot).count .T +
        (pRevRt526 v rTot).count .T = 1256 ∧ (pRevRt526 v rTot).count .TOFF =
        0; rw [tF, tR]; exact ⟨rfl, fR⟩
  stepRev := fun hk v rTot dw hAbs ↦
    subspaceStep_pRevRt526_ext_c70 hk v rTot dw hAbs

theorem dynWires_stage1NucOptWRouter1256Chunk8W300AsymPkg_stack {gLo wWork mCoin : ℕ}
    (hw : 300 ≤ wWork) (hm : 39 ≤ mCoin) {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rTot : QRegister dLayout n)
    (hAct : ∀ w : Wire dLayout, ActiveOuterCoinStackOf gLo wWork mCoin w → S (rTot w)) :
    DynWires S (stage1NucOptWRouter1256Chunk8W300AsymPkg.o1.fwdAmb v rTot) ∧
    DynWires S (stage1NucOptWRouter1256Chunk8W300AsymPkg.revAmb v rTot) :=
  ⟨dw_pFwdRt730 v rTot
     (fun j ↦ hAct _ (rPreFwdRtW300_activeStack gLo hw hm j))
     (fun j ↦ hAct _ (rW165_activeStack_w300 gLo hw hm j))
     (fun b ↦ hAct _ (rAuxOut10_activeStack_w300 gLo hw mCoin b))
     (fun i ↦ hAct _ (rAuxScr24_activeStack_w300 gLo hw mCoin i))
     (fun b ↦ hAct _ (rRt139L4_activeStack_w300 gLo hw mCoin b))
     (fun i ↦ hAct _ (rGatScr8DomZW298_activeStack_w300 gLo hw mCoin i)),
   dw_pRevRt526 v rTot
     (fun k ↦ hAct _ (activeStack_rOuter41_sym gLo wWork hm k))
     (fun j ↦ hAct _ (activeStack_rOut40_sym gLo (wWork := wWork) (by omega) mCoin j))
     (fun j ↦ hAct _ (rPreRev_activeStack gLo (by omega) hm j))
     (fun k hk ↦ hAct _ (activeStack_rScr_lt_sym gLo (M := 143) (wWork := wWork)
       (by omega) mCoin k hk))⟩

end QuantumComputation.Specs.PhotochemistrySolution.Stage1WRouter1260

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2WWork341
open scoped ComplexOrder MatrixOrder
open HermitianMat PrimitiveGate PhotochemistrySolution.KetSupport
   PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SplitRouterFredkinMux
open PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.Stage2QromMux
  PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.Sub5885MuxD1
open PhotochemistrySolution.PortBDualBellUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local reducible] SupportedOn
/-! ## Section 1: Single-Plane & Multi-Plane Semi-Bell `MuxD1SwapUnloadNoNF` Core (`0` Extra `T`) -/

/-- Wires modified by `cPlaneSemiEntangleCirc r` (`pHB r` is NOT modified!). -/
def SemiPlaneModSet {M D n : ℕ} (r : PlaneReg M D n) (w : Wire n) : Prop :=
  w = pBufLo r ∨ w = pBufHi r ∨ w = pHA r ∨ (∃ p : Fin M, w = pSys r p)

/-! ## Section 2: `cPlanesVecSemiEntangleCirc_eq_vec` & `prHB0` Aliasing -/

/-! ## Section 3: `rHB0Alias`, `prHB0`, and `subspaceStep_planes_zgModeMuxD1SwapUnloadNoNF_hb0` -/

def swapHB0 (D : ℕ) (b : Fin 24) (i : ℕ) : ℕ := swapPair (74 + 2 * D) (74 + 2 * D + b.val) 1 i
theorem swapHB0_lt {M D : ℕ} (b : Fin 24) : ∀ i < routerWidth M D, swapHB0 D b i <
    routerWidth M D := by
  intro i hi; have hb := b.isLt; unfold routerWidth at hi ⊢
  exact swapPair_lt (by omega) (by omega) hi

theorem swapHB0_invol {M D : ℕ} (b : Fin 24) : ∀ i < routerWidth M D, swapHB0 D b (swapHB0 D b i) =
    i := by
  intro i _
  by_cases hb0 : b.val = 0
  · unfold swapHB0 swapPair; split_ifs <;> omega
  · exact swapPair_invol (Or.inl (by omega)) i

theorem swapHB0_fixed_outside {D : ℕ} (b : Fin 24) {i : ℕ} (hi : i < 74 + 2 * D ∨ 98 + 2 * D ≤ i) :
    swapHB0 D b i = i := by
  have hb := b.isLt; unfold swapHB0
  exact swapPair_fixed (by omega) (by omega)

/-- Router register swapping `rHB r b` with `rHB r 0` (`74 + 2 * D`). -/
def rHB0Alias {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : RouterReg M D n :=
  routerOfInvol r (swapHB0 D b) (swapHB0_lt b) (swapHB0_invol b)

/--
Plane register for bit-plane `b` reading `rIdx1`, `rIdx2` on `(pNotMin, pNotMax)` and
aliasing `pHB` of every plane `b : Fin 24` to the single wire `rHB r 0` (`r ⟨74 + 2 * D⟩`).
-/
def prHB0 {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : PlaneReg M D n :=
    planeOfRouter (rIdx12Alias (rHB0Alias r b)) b
theorem prHB0_apply_of_ne6 {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) (i : Fin (planeWidth M D))
    (hi6 : i.val ≠ 6) : prHB0 r b i = planeOfRouter (rIdx12Alias r) b i := by
  have hb := b.isLt; have hi := i.isLt; unfold planeWidth at hi
  apply congrArg r.wires; apply Fin.ext
  let pv := planeIdxVal M D b i.val
  have hpv : pv < 74 + 2 * D ∨ 98 + 2 * D ≤ pv := by
    dsimp only [pv]; unfold planeIdxVal planeIdxFixed planeIdxD planeIdxM basePub
    split_ifs <;> omega
  let u := Stage2ChDiffNoNF.swapIdx12Alias M D pv; change swapHB0 D b u = u
  have hu : u < 74 + 2 * D ∨ 98 + 2 * D ≤ u := by
    dsimp only [u]; unfold Stage2ChDiffNoNF.swapIdx12Alias swapPair basePub
    split_ifs <;> omega
  exact swapHB0_fixed_outside b hu

theorem prHB0_hB {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pHB (prHB0 r b) = rHB r ⟨0, by omega⟩ := by
  have hb := b.isLt;
  have h1 : pHB (prHB0 r b) = rHB (rHB0Alias r b) b :=
      (planeOfRouter_rIdx12Alias_roles (rHB0Alias r b) b).2.2.2.2.2.2.1; rw [h1]
  exact congrArg r.wires (Fin.ext (by
    change swapHB0 D b (74 + 2 * D + b.val) = 74 + 2 * D + 0
    unfold swapHB0 swapPair; split_ifs <;> omega))

theorem prHB0_roles {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pHas1 (prHB0 r b) = rHas1 r ∧
    pHas2Eff (prHB0 r b) = rRawHas2 r ∧
    pBufLo (prHB0 r b) = pBufLo (planeOfRouter r b) ∧
    pBufHi (prHB0 r b) = pBufHi (planeOfRouter r b) ∧
    pHA (prHB0 r b) = pHA (planeOfRouter r b) ∧
    pHB (prHB0 r b) = rHB r ⟨0, by omega⟩ ∧
    pCtrlLo (prHB0 r b) = rCtrlLo r ∧
    pCtrlHi (prHB0 r b) = rCtrlHi r ∧
    pSys (prHB0 r b) = pSys (planeOfRouter r b) := by
  have hR := planeOfRouter_rIdx12Alias_roles r b
  have ne6 := prHB0_apply_of_ne6 r b
  exact ⟨(ne6 _ (by dsimp; omega)).trans hR.1, (ne6 _ (by dsimp; omega)).trans hR.2.1,
    (ne6 _ (by dsimp; omega)).trans hR.2.2.2.1, (ne6 _ (by dsimp; omega)).trans hR.2.2.2.2.1,
    (ne6 _ (by dsimp; omega)).trans hR.2.2.2.2.2.1, prHB0_hB r b,
    (funext fun p ↦ ne6 _ (by dsimp; omega)).trans hR.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (funext fun p ↦ ne6 _ (by dsimp; omega)).trans hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (funext fun p ↦ ne6 _ (by dsimp; omega)).trans hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem semiPlaneModSet_disj_prHB0 {M D n : ℕ} (r : RouterReg M D n) (j k : Fin 24) (hjk : j ≠ k)
    (w : Wire n) (hw : SemiPlaneModSet (prHB0 r j) w) (i : Fin (planeWidth M D)) : w ≠
    prHB0 r k i := by
  obtain ⟨_, _, eBL, eBH, eHA, _, _, _, eSys⟩ := prHB0_roles r j;
  have hR := planeOfRouter_rIdx12Alias_roles r j
  have hwIdx12 : PlaneModSet (planeOfRouter (rIdx12Alias r) j) w := by
    rcases hw with rfl | rfl | rfl | ⟨p, rfl⟩
    · rw [eBL, ← hR.2.2.2.1]; exact Or.inl rfl
    · rw [eBH, ← hR.2.2.2.2.1]; exact Or.inr (Or.inl rfl)
    · rw [eHA, ← hR.2.2.2.2.2.1]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [congrFun eSys p, ← congrFun hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p];
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, rfl⟩)))
  by_cases hi6 : i.val = 6
  · have hiEq : i = ⟨6, pw_lt6 M D⟩ := Fin.ext hi6
    rw [hiEq, show prHB0 r k ⟨6, pw_lt6 M D⟩ = pHB (prHB0 r k) from rfl, prHB0_hB r k]
    rcases hw with rfl | rfl | rfl | ⟨p, rfl⟩
    · rw [eBL, planeOfRouter_bufLo]; exact rr_ne r (by have := j.isLt; dsimp; omega)
    · rw [eBH, planeOfRouter_bufHi]; exact rr_ne r (by have := j.isLt; dsimp; omega)
    · rw [eHA, planeOfRouter_hA]; exact rr_ne r (by have := j.isLt; dsimp; omega)
    · rw [congrFun eSys p, planeOfRouter_sys]
      exact rr_ne r (by have := j.isLt; have := p.isLt; dsimp; omega)
  · rw [prHB0_apply_of_ne6 r k i hi6]; intro eqw;
    exact planeModSet_disj_planeOfRouter (rIdx12Alias r) j k hjk w hwIdx12 ⟨i, eqw.symm⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2WWork341
end

set_option maxRecDepth 16384
set_option exponentiation.threshold 8192

/-!
# `0-T` `.XMEAS + CZ` Stage-5 Uncomputation of `cLoN` , `cHiN` , `cHiE` , `cLoE` & `pUnloadCtrlLoZG`
Across Stage 4


1. **Generic `0-T` MBU Uncomputation Combinator `WRouterBracket.uncompAfter` (`Section 1`)**:
   - Factors the reverse `0-T` `.XMEAS + CZ` CH-tree uncomputation (`B.pUncomp`) from
   `WRouterBracket.wrap`
     into `B.uncompAfter v wHas wIdx wOut mid = .seq mid (B.pUncomp v wHas wIdx wOut)`, adding
     **`0 T` and `0 .TOFF`** (`count_uncompAfter`) and stepping
     `R_in -> (uOneHotToggle wHas wIdx wOut ...).1 * R_out -> R_out` (`subspaceStep_uncompAfter`).

2. **`0-T` Stage-5 `.XMEAS + CZ` Unloaders for Pre-Decoded `cLoN` , `cHiN + cHiE` , and `cLoE` (`0
T`, `Section 2` )**:
   - `pUnloadLoNPortOnlyZeroT` (`0 T`) + `count_pUnloadLoNPortOnlyZeroT` +
     `dynWires_pUnloadLoNPortOnlyZeroT_gen` + `subspaceStep_pUnloadLoNPortOnlyZeroT`.
   - `pUnloadSharedHiPortOnlyZeroT` & `pUnloadSharedHiPortOnlyHBEZeroT` (`0 T`) +
     `count_pUnloadSharedHiPortOnlyZeroT` + `dynWires_pUnloadSharedHiPortOnlyHBEZeroT_gen` +
     `subspaceStep_pUnloadSharedHiPortOnlyZeroT` + `subspaceStep_pUnloadSharedHiPortOnlyHBEZeroT`.
   - `pUnloadLoEZeroT` (`0 T`) + `count_pUnloadLoEZeroT` +
     `dynWires_pUnloadLoEZeroT` + `subspaceStep_pUnloadLoEZeroT`.
   - Combined `0-T` Stage-5 unloader `pSharedPortBStage5UnloadHiLoEPortOnlyHBEZeroT` (`0 T`) &
   `pSharedPortBStage5UnloadAllNPortOnlyHBEZeroT` (`0 T`).

3. **Stage-2 Electronic `pRouterWStateElecOptA_NoUnload_187_8` (`19,690 T`),
   `0-T` `pUnloadCtrlLoZG` Slice Uncomputation, & `uXorPubLo = F_LoE` / `uXorPubHi = F_DecE` Bridges
   (`Section 3`)**:
   - Proves `uXorPubLo_eq_fwdCirc_pDecLoE` and `uXorPubHi_eq_fwdCirc_pDecHiE`, showing that `pCLoE`
     (`330 T`) and `pCHiE` (`340 T`) produce the exact operators
     `F_LoE = (fwdCirc (pDecLoESorted rE)).eval`
     and `F_DecE = (fwdCirc (pDecHiESorted rE)).eval` on valid router inputs (`330 + 340 = 670
     T`
     total).
   - Defines `pRouterWStateElecOptA_NoUnload_187_8` (`19,690 T`, `0 .TOFF`),
     proving `count_pRouterWStateElecOptA_NoUnload_187_8` ,
     `dynWires_pRouterWStateElecOptA_NoUnload_187_8` ,
     and `subspaceStep_pRouterWStateElecOptA_NoUnload_187_8`.
   - Proves `subspaceStep_pUnloadCtrlLoZG_zeroT_of_slices` (`0 T` `.XMEAS + CZ` uncomputation of
     `uXorTargetLo rE` via `pUnloadCtrlLoZG` on `(wA24, wB24, wX8HB, wY8HB)`).

4. **Cross-Stage `CommutesWithDyn` Across Stage 3 & Stage 4 (`Section 4`)**:
   - Proves `commutesWithDyn_F_LoN_of_dynWires`, `commutesWithDyn_F_DecN_of_dynWires`,
     `commutesWithDyn_F_DecE_of_dynWires`, `commutesWithDyn_F_LoE_of_dynWires`, and
     `commutesWithDyn_uXorTargetLo_of_dynWires`.
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateCrossStage
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate
  PhotochemistrySolution.KetSupport PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SplitRouterFredkinMux
  PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.Stage2QromMux
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.Stage2ZeroGated
  PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ChDiffNoNF
  PhotochemistrySolution.PortBDualBellUnld PhotochemistrySolution.PortBStage5Merged
  PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.HalfBellCollapse
  PhotochemistrySolution.WStateStage2Load PhotochemistrySolution.Stage2ElecOptA
open PhotochemistrySolution.WStateStage5Unload
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen ancWOfScr
attribute [local semireducible]
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  ComputeProg.fwdBits
/-! ## Section 1: Generic `0-T` MBU Uncomputation Combinator `wRouterBracketUncompAfter` -/

/--
Uncompute-only half of `WRouterBracket.wrap`: runs `mid` followed by `B.pUncomp` (`0 T`, `0 .TOFF`
reverse `.XMEAS + CZ` CH-tree uncomputation), without re-running `B.pComp`.
-/
def wRouterBracketUncompAfter {D N tCost : ℕ} (B : WRouterBracket D N tCost) {Var : Type} {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n := .seq mid (B.pUncomp v wHas wIdx wOut)
theorem count_wRouterBracketUncompAfter {D N tCost : ℕ} (B : WRouterBracket D N tCost) {Var : Type}
    {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (mid : DynamicCircuit Var n) : (wRouterBracketUncompAfter B v wHas wIdx wOut mid).count .T =
    mid.count .T ∧ (wRouterBracketUncompAfter B v wHas wIdx wOut mid).count .TOFF =
    mid.count .TOFF := by
  obtain ⟨tu, fu⟩ :=
      B.count_uncomp v wHas wIdx wOut; dsimp only [wRouterBracketUncompAfter,
      DynamicCircuit.count]; omega
theorem dynWires_wRouterBracketUncompAfter {D N tCost : ℕ} (B : WRouterBracket D N tCost)
    {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (mid : DynamicCircuit Var n) (hHas : S wHas) (hIdx : ∀ d, S (wIdx d))
    (hOut : ∀ j, S (wOut j)) (hMid : DynWires S mid) :
    DynWires S (wRouterBracketUncompAfter B v wHas wIdx wOut mid) :=
    ⟨hMid, B.dynWires_uncomp v wHas wIdx wOut hHas hIdx hOut⟩
theorem subspaceStep_wRouterBracketUncompAfter {D N tCost : ℕ}
    (B : WRouterBracket D N tCost)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) {qEnc : Wire n}
    (hd : WRouterDisj wHas wIdx wOut qEnc) (mid : DynamicCircuit Var n)
    (R_in R_out : Operator (2 ^ n))
    (hOut : SupportedOn (ValidWRouterClean wHas wIdx wOut) R_out)
    (hMid : SubspaceStep (Var := Var)
      R_in
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_out)
      mid) :
    SubspaceStep (Var := Var) R_in R_out (wRouterBracketUncompAfter B v wHas wIdx wOut mid) :=
  hMid.seq (B.step_uncomp v wHas wIdx wOut hd R_out hOut)

/-!
## Section 1b: In-Place Truncated `187` -Wire W-State Bracket `wRouterWrap187` (`372 T`, `0` Extra
Hypotheses)
-/

/-!
## Section 2: `0-T` Stage-5 `.XMEAS + CZ` Unloaders for Pre-Decoded `cLoN` , `cHiN` , `cHiE` ,
`cLoE` (`0 T`)
-/

/-!
## Section 2b: Truncated `187` -Wire Stage-5 Unloaders (`pUnloadLoEWState372` `372 T` ,
`pUnloadSharedHiPortOnlyHBEWState462` `462 T` , `pSharedPortBStage5UnloadAllNPortOnlyHBEWState924`
`924 T` , `0` Extra Hypotheses, No Wires Held Across Stage 4!)
-/

/-!
## Section 3: Stage-2 Electronic `pRouterWStateElecOptA_NoUnload_187_8` (`19,690 T`), `0-T`
`pUnloadCtrlLoZG` Slice Uncomputation, & `uXorPubLo = F_LoE` / `uXorPubHi = F_DecE` Bridges
-/


/-!
## Section 3b: Stage-2 Nuclear `pRouterWStateNucKeepCtrl_47_6` &
`pRouterWStateNucKeepCtrlHBCollapse_47_6` (`5,476 T`, Leaving `ULo * UHi` / `UHi` Live for
Cross-Stage `0-T` Uncomputation)
-/

/-!
## Section 3c: `372-T` `pDecLoEWState372` , `332-T` Shared-Prefix `pCHiE332` , `19,658-T`
`pRouterWStateElecSwapUnloadOptA332_187_8` , `19,634-T` `NoUnload` , and `wWork = 313 / 317 / 318`
(`-28 / -24 / -23` Qubits = `-3.01T / -2.58T / -2.47T` at `0` Extra T-Gates!)
-/


attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean

theorem comm_uOneHotToggle_uVecToggle_pub {n D_idx N : ℕ} (r : RouterReg 187 8 n) {wHas : Wire n}
    {wIdx : Fin D_idx → Wire n} {wOut : Fin N → Wire n} (hHasOut : ∀ j, wHas ≠ wOut j)
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (f : BitAssignment n → Fin 187 → ZMod 2)
    (hf : ∀ α₁ α₂, (∀ w, (∀ p, w ≠ rCtrlLo r p) → α₁ w = α₂ w) → f α₁ = f α₂)
    (hfPub : ∀ α₁ α₂, (∀ w, PubCtrlSet r w → α₁ w = α₂ w) → f α₁ = f α₂)
    (hHasLo : ∀ p, wHas ≠ rCtrlLo r p) (hIdxLo : ∀ d p, wIdx d ≠ rCtrlLo r p)
    (hOutLo : ∀ j p, wOut j ≠ rCtrlLo r p) (hPubOut : ∀ w, PubCtrlSet r w → ∀ j, w ≠ wOut j) :
    (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1 * (uVecToggle (rCtrlLo r)
    (rCtrlLo_inj_ne r) f hf).1 = (uVecToggle (rCtrlLo r) (rCtrlLo_inj_ne r) f hf).1 *
    (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1 := by
  have ket_sr (δ : BitAssignment n) : ket δ = SplitRouterSeqBell26k.ket δ := rfl
  apply matrix_ext_ket; intro α
  let α_x := vecToggleBits (rCtrlLo r) f α;
  let α_t :=
      toggleOneHotBits wHas wIdx wOut α; simp only [← Matrix.mulVec_mulVec]; rw [ket_sr,
      uVecToggle_mulVec_ket, ← ket_sr, uOneHotToggle_mulVec_ket, uOneHotToggle_mulVec_ket, ket_sr,
      uVecToggle_mulVec_ket,
      ← ket_sr]; congr 1; have hHasX : α_x wHas = α wHas :=
                            (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f α).2 _ hHasLo
  have hIdxX : idxValD wIdx α_x = idxValD wIdx α := idxValD_congr wIdx fun d ↦
      (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f α).2 _ (hIdxLo d)
  have hPubT : ∀ w, PubCtrlSet r w → α_t w = α w := fun w hw ↦
      toggleOneHotBits_apply_other α (hPubOut w hw)
  have hfT : f α_t = f α := hfPub α_t α hPubT
  dsimp only [α_x, α_t] at *
  funext u
  by_cases hL : ∃ p : Fin 187, u = rCtrlLo r p
  · obtain ⟨p, rfl⟩ := hL
    rw [toggleOneHotBits_apply_other _ (fun j ↦ (hOutLo j p).symm), (vecToggleBits_spec (rCtrlLo r)
        (rCtrlLo_inj_ne r) f α).1 p, (vecToggleBits_spec (rCtrlLo r)
        (rCtrlLo_inj_ne r) f (toggleOneHotBits wHas wIdx wOut α)).1 p,
        toggleOneHotBits_apply_other α (fun j ↦ (hOutLo j p).symm), hfT]
  · have nL : ∀ p : Fin 187, u ≠ rCtrlLo r p := fun p e ↦ hL ⟨p, e⟩
    rw [(vecToggleBits_spec (rCtrlLo r)
        (rCtrlLo_inj_ne r) f (toggleOneHotBits wHas wIdx wOut α)).2 u nL]
    by_cases hLt : idxValD wIdx α < N
    · have hLtX : idxValD wIdx (vecToggleBits (rCtrlLo r) f α) < N :=
          hIdxX ▸ hLt; dsimp only [toggleOneHotBits]; rw [dite_eq_left hLtX, dite_eq_left hLt]
      have hFin : (⟨idxValD wIdx (vecToggleBits (rCtrlLo r) f α), hLtX⟩ : Fin N) =
          ⟨idxValD wIdx α, hLt⟩ := Fin.ext hIdxX
      rw [hFin]
      by_cases hwu : u = wOut ⟨idxValD wIdx α, hLt⟩
      · subst hwu;
        rw [Function.update_self, Function.update_self, hHasX, (vecToggleBits_spec (rCtrlLo r)
            (rCtrlLo_inj_ne r) f α).2 _ (hOutLo _)]
      · rw [Function.update_of_ne hwu, Function.update_of_ne hwu, (vecToggleBits_spec (rCtrlLo r)
            (rCtrlLo_inj_ne r) f α).2 u nL]
    · have hLtX : ¬ idxValD wIdx (vecToggleBits (rCtrlLo r) f α) < N :=
          hIdxX ▸ hLt; dsimp only [toggleOneHotBits]; rw [dite_eq_right hLtX, dite_eq_right hLt,
          (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f α).2 u nL]
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc

theorem count_fwdCirc_of_numAnd_zero {n : ℕ} :
    ∀ (p : ComputeProg n), p.numAnd = 0 →
      (fwdCirc p).count .T = 0 ∧ (fwdCirc p).count .TOFF = 0
  | .id, _ => ⟨rfl, rfl⟩
  | .x _, _ => by simp [fwdCirc, Circuit.X]
  | .cnot _ _ _, _ => by simp [fwdCirc, Circuit.CNOT]
  | .andGate _ _ _ _ _ _, h0 => by dsimp [ComputeProg.numAnd] at h0; omega
  | .seq p₁ p₂, h0 => by
      dsimp [ComputeProg.numAnd] at h0
      obtain ⟨t1, f1⟩ := count_fwdCirc_of_numAnd_zero p₁ (by omega)
      obtain ⟨t2, f2⟩ := count_fwdCirc_of_numAnd_zero p₂ (by omega)
      dsimp only [fwdCirc]; simp only [Circuit.count_seq, t1, t2, f1, f2, Nat.add_zero];
      exact ⟨trivial, trivial⟩
theorem cw_fwdCirc_of_supp {n : ℕ} {S : Wire n → Prop} :
    ∀ (p : ComputeProg n), p.numAnd = 0 → ProgSupportedIn S p → CircWires S (fwdCirc p)
  | .id, _, _ => trivial
  | .x _, _, h0 => cw_1 h0
  | .cnot _ _ _, _, ⟨hc, ht⟩ => cw_cnot hc ht
  | .andGate _ _ _ _ _ _, h0, _ => by dsimp [ComputeProg.numAnd] at h0; omega
  | .seq p₁ p₂, h0, ⟨h1, h2⟩ => by
      dsimp [ComputeProg.numAnd] at h0
      exact ⟨cw_fwdCirc_of_supp p₁ (by omega) h1, cw_fwdCirc_of_supp p₂ (by omega) h2⟩

open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2WWork341 (prHB0)
/-!
### `wWork = 313 / 317 / 318` Electronic Stage-2 Compression via `prHB0` (`rHB[1..23]` Idle Pool)
-/


attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  PhotochemistrySolution.DynQromUncompA.remeasureIf

abbrev wX8A {n : ℕ} (r : RouterReg 187 8 n) (j : Fin 8) : Wire n :=
  wA24 r ⟨j.val, by have := j.isLt; omega⟩

abbrev wY8A {n : ℕ} (r : RouterReg 187 8 n) (j : Fin 8) : Wire n :=
  wA24 r ⟨8 + j.val, by have := j.isLt; omega⟩

theorem wRouterDisj_x8A {n : ℕ} (r : RouterReg 187 8 n) :
    WRouterDisj (rHas1 r) (idxLo3_1 r) (wX8A r) (qEncE r) where
  has_ne_out := fun j ↦ (wRouterDisj_a24 r).has_ne_out _
  has_ne_q := (wRouterDisj_a24 r).has_ne_q
  idx_ne_out := fun d j ↦
      rr_ne r
      (by have := d.isLt; have := j.isLt; unfold idxA24Val; dsimp [idxLo3_1, rIdx1]; split_ifs <;>
                            omega)
  idx_ne_q := fun d ↦ rr_ne r (by have := d.isLt; dsimp [idxLo3_1, rIdx1]; omega)
  out_inj := fun i j hne e ↦ hne (Fin.ext (congrArg (Fin.val : Fin 24 → ℕ) (wA24_inj r e)))
  out_ne_q := fun j ↦ (wRouterDisj_a24 r).out_ne_q _

theorem wRouterDisj_y8A {n : ℕ} (r : RouterReg 187 8 n) :
    WRouterDisj (rRawHas2 r) (idxLo3_2 r) (wY8A r) (qEncE r) where
  has_ne_out := fun j ↦
      rRawHas2_ne_r r (by have := j.isLt; unfold idxA24Val; dsimp; split_ifs <;> omega)
  has_ne_q := rRawHas2_ne_r r (by dsimp; omega)
  idx_ne_out := fun d j ↦
      rr_ne r
      (by have := d.isLt; have := j.isLt; unfold idxA24Val; dsimp [idxLo3_2, rIdx2]; split_ifs <;>
                            omega)
  idx_ne_q := fun d ↦ rr_ne r (by have := d.isLt; dsimp [idxLo3_2, rIdx2]; omega)
  out_inj := fun i j hne e ↦ by
    have hv := congrArg (Fin.val : Fin 24 → ℕ) (wA24_inj r e)
    dsimp at hv; exact hne (Fin.ext (by omega))
  out_ne_q := fun j ↦ (wRouterDisj_a24 r).out_ne_q _

abbrev uToggleX8A {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
    uOneHotToggle (rHas1 r) (idxLo3_1 r) (wX8A r)
    (wRouterDisj_x8A r).has_ne_out (wRouterDisj_x8A r).idx_ne_out
abbrev uToggleY8A {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
    uOneHotToggle (rRawHas2 r) (idxLo3_2 r) (wY8A r)
    (wRouterDisj_y8A r).has_ne_out (wRouterDisj_y8A r).idx_ne_out
theorem comm_uToggleX8A_uXorTargetLo {n : ℕ} (r : RouterReg 187 8 n) : (uToggleX8A r).1 *
    (uXorTargetLo r).1 = (uXorTargetLo r).1 * (uToggleX8A r).1 :=
  comm_uOneHotToggle_uVecToggle_pub r _ _ (fun α p ↦ pubCtrlLo r α p + pubCtrlHi r α p) _
    (fun _ _ hEq ↦ funext fun p ↦ congrArg₂ (· + ·)
      (congrFun (pubCtrl_congr r hEq).1 p) (congrFun (pubCtrl_congr r hEq).2 p))
    (fun p ↦ rr_ne r (by dsimp [rHas1, rCtrlLo, basePub]; omega))
    (fun d p ↦ rr_ne r (by have := d.isLt; dsimp [idxLo3_1, rIdx1, rCtrlLo, basePub]; omega))
    (fun s p ↦ wA24_ne_rCtrlLo r _ p)
    (fun _ hw _ ↦ pubCtrlSet_ne_wA24 r hw _)

/-!
### `12-T` Staged Unloader `pElecUnloadLoStaged12NoHB23` & `19,654-T` Router
`pRouterWStateElecSwapUnloadOptA12_w318_187_8` (`318 ≤ wWork`)
-/

def pXorLoToY8A {n : ℕ} (r : RouterReg 187 8 n) : (m : ℕ) → m ≤ 187 → ComputeProg n
  | 0, _ => .id
  | m + 1, hm =>
      .seq (pXorLoToY8A r m (Nat.le_of_succ_le hm))
        (.cnot (rCtrlLo r ⟨m, hm⟩) (wY8A r ⟨m % 8, Nat.mod_lt m (by omega)⟩)
          (wA24_ne_rCtrlLo r _ ⟨m, hm⟩).symm)

def pXorX8AToY8A {n : ℕ} (r : RouterReg 187 8 n) : (m : ℕ) → m ≤ 8 → ComputeProg n
  | 0, _ => .id
  | m + 1, hm =>
      .seq (pXorX8AToY8A r m (Nat.le_of_succ_le hm))
        (.cnot (wX8A r ⟨m, hm⟩) (wY8A r ⟨m, hm⟩)
          (fun e ↦
              by have hv := congrArg (Fin.val : Fin 24 → ℕ) (wA24_inj r e); dsimp at hv; omega))

def pComputeY8AFromLoX8AProg {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
    .seq (pXorLoToY8A r 187 le_rfl) (pXorX8AToY8A r 8 le_rfl)
def cComputeY8AFromLoX8A {n : ℕ} (r : RouterReg 187 8 n) : Circuit n :=
    fwdCirc (pComputeY8AFromLoX8AProg r)
theorem numAnd_pXorLoToY8A {n : ℕ} (r : RouterReg 187 8 n) :
    ∀ m hm, (pXorLoToY8A r m hm).numAnd = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [pXorLoToY8A, ComputeProg.numAnd];
      exact numAnd_pXorLoToY8A r m (Nat.le_of_succ_le hm)
theorem numAnd_pXorX8AToY8A {n : ℕ} (r : RouterReg 187 8 n) :
    ∀ m hm, (pXorX8AToY8A r m hm).numAnd = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [pXorX8AToY8A, ComputeProg.numAnd];
      exact numAnd_pXorX8AToY8A r m (Nat.le_of_succ_le hm)
theorem count_cComputeY8AFromLoX8A {n : ℕ} (r : RouterReg 187 8 n) :
    (cComputeY8AFromLoX8A r).count .T = 0 ∧ (cComputeY8AFromLoX8A r).count .TOFF = 0 := by
  refine count_fwdCirc_of_numAnd_zero (pComputeY8AFromLoX8AProg r) ?_;
  dsimp only [pComputeY8AFromLoX8AProg, ComputeProg.numAnd];
  rw [numAnd_pXorLoToY8A, numAnd_pXorX8AToY8A]
theorem fwdBits_pXorLoToY8A_other {n : ℕ} (r : RouterReg 187 8 n) :
    ∀ (m : ℕ) (hm : m ≤ 187) (η : BitAssignment n) {w : Wire n},
      (∀ j : Fin 8, w ≠ wY8A r j) → (pXorLoToY8A r m hm).fwdBits η w = η w
  | 0, _, _, _, _ => rfl
  | m + 1, hm, η, w, hw => by
      dsimp only [pXorLoToY8A, ComputeProg.fwdBits]; rw [Function.update_of_ne (hw _)];
      exact fwdBits_pXorLoToY8A_other r m (Nat.le_of_succ_le hm) η hw
theorem fwdBits_pXorX8AToY8A_other {n : ℕ} (r : RouterReg 187 8 n) :
    ∀ (m : ℕ) (hm : m ≤ 8) (η : BitAssignment n) {w : Wire n},
      (∀ j : Fin 8, w ≠ wY8A r j) → (pXorX8AToY8A r m hm).fwdBits η w = η w
  | 0, _, _, _, _ => rfl
  | m + 1, hm, η, w, hw => by
      dsimp only [pXorX8AToY8A, ComputeProg.fwdBits]; rw [Function.update_of_ne (hw _)];
      exact fwdBits_pXorX8AToY8A_other r m (Nat.le_of_succ_le hm) η hw
theorem fwdBits_pComputeY8AFromLoX8AProg_other {n : ℕ} (r : RouterReg 187 8 n) (η : BitAssignment n)
    {w : Wire n} (hw : ∀ j : Fin 8, w ≠ wY8A r j) : (pComputeY8AFromLoX8AProg r).fwdBits η w =
    η w := by
  dsimp only [pComputeY8AFromLoX8AProg, ComputeProg.fwdBits];
  exact (fwdBits_pXorX8AToY8A_other r 8 le_rfl _ hw).trans (fwdBits_pXorLoToY8A_other r 187 le_rfl η
      hw)
theorem fwdBits_pXorLoToY8A_wY8A {n : ℕ} (r : RouterReg 187 8 n)
    {v₁ v₂ : ℕ} {h₁ h₂ : ZMod 2} {η : BitAssignment n}
    (hLo : ∀ p : Fin 187, η (rCtrlLo r p) =
      (if p.val = v₁ then h₁ else 0) + (if p.val = v₂ then h₂ else 0)) :
    ∀ (m : ℕ) (hm : m ≤ 187) (j : Fin 8),
      (pXorLoToY8A r m hm).fwdBits η (wY8A r j) =
        η (wY8A r j) +
          (if v₁ < m ∧ v₁ % 8 = j.val then h₁ else 0) +
          (if v₂ < m ∧ v₂ % 8 = j.val then h₂ else 0)
  | 0, _, j => by simp [pXorLoToY8A, ComputeProg.fwdBits]
  | m + 1, hm, j => by
      let η' := (pXorLoToY8A r m (Nat.le_of_succ_le hm)).fwdBits η;
      have hIH := fwdBits_pXorLoToY8A_wY8A r hLo m (Nat.le_of_succ_le hm) j
      have hCtrl : η' (rCtrlLo r ⟨m, hm⟩) = (if m = v₁ then h₁ else 0) + (if m = v₂ then h₂ else 0)
          :=
          (fwdBits_pXorLoToY8A_other r m (Nat.le_of_succ_le hm) η (fun j' ↦
          (wA24_ne_rCtrlLo r _ ⟨m, hm⟩).symm)).trans (hLo ⟨m, hm⟩)
      have hStepIte (v : ℕ) (hv : ZMod 2) :
          (if v < m ∧ v % 8 = j.val then hv else 0) + (if m % 8 = j.val then (if m =
              v then hv else 0) else 0) =
            (if v < m + 1 ∧ v % 8 = j.val then hv else 0) := by
        split_ifs <;> first | exact zero_add _ | exact add_zero _ | omega
      dsimp only [pXorLoToY8A, ComputeProg.fwdBits];
      change Function.update η' (wY8A r ⟨m % 8, _⟩)
          (η' (wY8A r ⟨m % 8, _⟩) + η' (rCtrlLo r ⟨m, hm⟩)) (wY8A r j) = _
      by_cases hj : m % 8 = j.val
      · have hjFin : (⟨m % 8, Nat.mod_lt m (by omega)⟩ : Fin 8) = j := Fin.ext hj
        rw [hjFin, Function.update_self, hCtrl]; dsimp only [η']; rw [hIH];
        have s1 := hStepIte v₁ h₁;
        have s2 := hStepIte v₂ h₂; rw [ite_eq_left hj] at s1 s2; rw [← s1, ← s2]; ring
      · have hne : wY8A r j ≠ wY8A r ⟨m % 8, Nat.mod_lt m (by omega)⟩ :=
          fun e ↦ ((wRouterDisj_y8A r).out_inj j ⟨m % 8, Nat.mod_lt m (by omega)⟩
            (fun h ↦ hj (congrArg Fin.val h).symm) e)
        rw [Function.update_of_ne hne]; dsimp only [η']; rw [hIH]; have s1 := hStepIte v₁ h₁;
        have s2 := hStepIte v₂ h₂; rw [ite_eq_right hj, add_zero] at s1 s2; rw [← s1, ← s2]
theorem fwdBits_pXorX8AToY8A_wY8A {n : ℕ} (r : RouterReg 187 8 n) (η : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ 8) (j : Fin 8),
      (pXorX8AToY8A r m hm).fwdBits η (wY8A r j) =
        η (wY8A r j) + (if j.val < m then η (wX8A r j) else 0)
  | 0, _, j => by simp [pXorX8AToY8A, ComputeProg.fwdBits]
  | m + 1, hm, j => by
      let η' := (pXorX8AToY8A r m (Nat.le_of_succ_le hm)).fwdBits η;
      have hIH := fwdBits_pXorX8AToY8A_wY8A r η m (Nat.le_of_succ_le hm) j
      have hX : η' (wX8A r ⟨m, hm⟩) = η (wX8A r ⟨m, hm⟩) :=
        fwdBits_pXorX8AToY8A_other r m (Nat.le_of_succ_le hm) η
          (fun j' e ↦
              by have hv := congrArg (Fin.val : Fin 24 → ℕ) (wA24_inj r e); dsimp at hv; omega)
      dsimp only [pXorX8AToY8A, ComputeProg.fwdBits];
      change Function.update η' (wY8A r ⟨m, hm⟩) (η' (wY8A r ⟨m, hm⟩) + η' (wX8A r ⟨m, hm⟩))
          (wY8A r j) = _
      by_cases hjm : j.val = m
      · have hjFin : (⟨m, hm⟩ : Fin 8) = j := Fin.ext hjm.symm;
        have hXj : η' (wX8A r j) = η (wX8A r j) :=
            hjFin ▸ hX; rw [hjFin, Function.update_self, hXj]; dsimp only [η']; rw [hIH, hjm,
            ite_eq_right (Nat.lt_irrefl m), add_zero, ite_eq_left (Nat.lt_succ_self m)]
      · have hne : wY8A r j ≠ wY8A r ⟨m, hm⟩ :=
          fun e ↦ ((wRouterDisj_y8A r).out_inj j ⟨m, hm⟩ (fun h ↦ hjm (congrArg Fin.val h)) e)
        rw [Function.update_of_ne hne]; dsimp only [η']; rw [hIH]
        by_cases hlt : j.val < m
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

theorem fwdBits_pComputeY8AFromLoX8AProg_wY8A {n : ℕ} (r : RouterReg 187 8 n) {v₁ v₂ : ℕ}
    {h₁ h₂ : ZMod 2} {η : BitAssignment n} (hv₁ : v₁ < 187) (hv₂ : v₂ < 187)
    (hLo : ∀ p : Fin 187, η (rCtrlLo r p) = (if p.val = v₁ then h₁ else 0) +
    (if p.val = v₂ then h₂ else 0)) (hX : ∀ j : Fin 8, η (wX8A r j) = if v₁ % 8 =
    j.val then h₁ else 0) (hY0 : ∀ j : Fin 8, η (wY8A r j) = 0)
    (j : Fin 8) : (pComputeY8AFromLoX8AProg r).fwdBits η (wY8A r j) = if v₂ % 8 =
    j.val then h₂ else 0 := by
  let η₁ := (pXorLoToY8A r 187 le_rfl).fwdBits η
  have hY₁ : η₁ (wY8A r j) = (if v₁ % 8 = j.val then h₁ else 0) + (if v₂ % 8 = j.val then h₂ else 0)
      := by
    dsimp only [η₁]
    rw [fwdBits_pXorLoToY8A_wY8A r hLo 187 le_rfl j, hY0 j, zero_add]
    split_ifs <;> first | rfl | omega
  have hX₁ : η₁ (wX8A r j) = if v₁ % 8 = j.val then h₁ else 0 :=
    (fwdBits_pXorLoToY8A_other r 187 le_rfl η
      (fun j' e ↦
          by have hv :=
               congrArg (Fin.val : Fin 24 → ℕ) (wA24_inj r e); dsimp at hv; omega)).trans (hX j)
  dsimp only [pComputeY8AFromLoX8AProg, ComputeProg.fwdBits];
  rw [fwdBits_pXorX8AToY8A_wY8A r η₁ 8 le_rfl j, ite_eq_left j.isLt, hY₁, hX₁, add_right_comm,
      CharTwo.add_self_eq_zero, zero_add]
theorem wRouterDisj_x8A_y0 {n : ℕ} (r : RouterReg 187 8 n) :
    WRouterDisj (rHas1 r) (idxLo3_1 r) (wX8A r) (wY8A r ⟨0, by omega⟩) where
  has_ne_out := (wRouterDisj_x8A r).has_ne_out
  has_ne_q := rr_ne r (by unfold idxA24Val; dsimp [rHas1, wY8A, wA24]; omega)
  idx_ne_out := (wRouterDisj_x8A r).idx_ne_out
  idx_ne_q := fun d ↦
      rr_ne r (by have := d.isLt; unfold idxA24Val; dsimp [idxLo3_1, rIdx1, wY8A, wA24]; omega)
  out_inj := (wRouterDisj_x8A r).out_inj
  out_ne_q := fun s ↦
      rr_ne r (by have := s.isLt; unfold idxA24Val; dsimp [wX8A, wY8A, wA24]; split_ifs <;> omega)

/-!
### Part 2: `334-T` `pCHiE334NoHB23_w315` Avoiding `91..113` and `5048, 5049, 5051` (`wWork = 315`)
-/

/-! ## Section 4: Cross-Stage `0-T` Spacetime Arithmetic Check -/
end QuantumComputation.Specs.PhotochemistrySolution.WStateCrossStage
end

set_option maxRecDepth 200000

/-!
# Zero-`pAnc` Stage-2 `AlwaysLo` Semi-Bell Planes (`18,816 T`, `0 .TOFF`, Avoiding `rAnc = r 5055`)

Eliminates `pAnc r` (`i = 7`, mapped to `rAnc rP = r 5055` ) from
`pDualBellPlaneMuxD1CHDiffNoNFAlwaysLoDyn`
and `pSemiBellPlanesAlwaysLoMD` without adding a single gate:
1. During `cHead` , `pScanPrefixXorMuxD1Dyn` , and `grayMuxD1Pairs` , `pBufLo r` (`i = 3`) is `|0⟩`
and untouched,
   so `rL := rSwapAncBufLo r` (`3 ↔ 7`) uses `pBufLo r` as the temporary `|0⟩ → |0⟩` ancilla.
2. `pUnloadAMsbHiDyn` runs right after `cDiffExtOneHotCirc` (before `pCloseMuxAlwaysLoDyn` ),
uncomputing
   `pAMsb r 1..D-1` to `|0⟩` so `rA := rSwapAncAMsb1 hD2 r` (`7 ↔ 8 + 3*D + 1`) uses `pAMsb r 1` as
   the
   temporary `|0⟩ → |0⟩` ancilla in `pCloseMuxAlwaysLoDyn`.
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.PlanesAlwaysLoNoAnc
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
  PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ChDiffNoNF
  PhotochemistrySolution.PortBDualBellUnld PhotochemistrySolution.WStateRouterPrim
  PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateStage2Load
  PhotochemistrySolution.Stage2ElecOptA PhotochemistrySolution.Stage2AlwaysLo
open PrimitiveGate hiding x y z h s t cnot swap toffoli
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding sqrtHalf
  star_sqrtHalf sqrtHalf_mul_sqrtHalf bitSign bitSign_add bitSign_mul_self
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2WWork341 (SemiPlaneModSet prHB0
    rHB0Alias prHB0_roles prHB0_hB prHB0_apply_of_ne6 semiPlaneModSet_disj_prHB0)
open scoped ComplexOrder MatrixOrder Circuit.Notation
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
    DynQromUncompA.fwdCirc SplitRouterSeqBell26k.tempAndFanoutDyn KinB.andComputeCircuit
    KinB.andUncomputeDyn XMeasLinearCleanStep.xUnloadCzPairsSeqDyn DynQromUncompA.remeasureIf
theorem writeReg_comm_of_actsIndepOf {n k : ℕ} {S : Wire n → Prop}
    {G : BitAssignment n → BitAssignment n} (hG : ∀ q, S q → ∀ β v, G (Function.update β q v) =
    Function.update (G β) q v) (reg : QRegister k n) (hreg : ∀ i : Fin k, S (reg.wires i))
    (β : BitAssignment n) (γ : BitAssignment k) : G (DynCircExt.writeReg β reg γ) =
    DynCircExt.writeReg (G β) reg γ := by
  have hStep : ∀ (m : ℕ) (hm : m ≤ k) (δ : BitAssignment n),
      (∀ w, (∀ i : Fin k, i.val < m → w ≠ reg.wires i) → δ w = β w) →
      (∀ w, (∀ i : Fin k, i.val < m → w ≠ reg.wires i) → G δ w = G β w) ∧
      (∀ i : Fin k, i.val < m → G δ (reg.wires i) = δ (reg.wires i)) := by
    intro m
    induction m with
    | zero =>
        intro _ δ hδ
        rw [show δ = β from funext fun w ↦ hδ w fun _ h ↦ by omega]
        exact ⟨fun _ _ ↦ rfl, fun _ h ↦ by omega⟩
    | succ m ih =>
        intro hm δ hδ
        let i₀ : Fin k := ⟨m, hm⟩
        let δ₀ := Function.update δ (reg.wires i₀) (β (reg.wires i₀))
        obtain ⟨hOth₀, hReg₀⟩ := ih (Nat.le_of_succ_le hm) δ₀ fun w hw ↦ by
          by_cases hw0 : w = reg.wires i₀
          · exact hw0 ▸ Function.update_self _ _ _
          · exact (Function.update_of_ne hw0 _ _).trans (hδ w fun i hi e ↦
              if him : i.val =
                  m then hw0 (e.trans (congrArg reg.wires (Fin.ext him))) else hw i (by omega) e)
        have hGδ : G δ = Function.update (G δ₀) (reg.wires i₀) (δ (reg.wires i₀)) := by
          conv_lhs => rw [show δ = Function.update δ₀ (reg.wires i₀) (δ (reg.wires i₀)) by
            simp only [δ₀, Function.update_idem, Function.update_eq_self]]
          exact hG (reg.wires i₀) (hreg i₀) δ₀ (δ (reg.wires i₀))
        rw [hGδ]
        refine ⟨fun w hw ↦ (Function.update_of_ne (hw i₀ (Nat.lt_succ_self m)) _ _).trans
          (hOth₀ w fun i hi ↦ hw i (Nat.lt_succ_of_lt hi)), fun i hi ↦ ?_⟩
        by_cases him : i = i₀
        · exact him ▸ Function.update_self _ _ _
        · have hne : reg.wires i ≠ reg.wires i₀ := reg.wires.injective.ne him
          have hneV : i.val ≠ m := Fin.val_ne_of_ne him
          exact (Function.update_of_ne hne _ _).trans
            ((hReg₀ i (by omega)).trans (Function.update_of_ne hne _ _))
  obtain ⟨hOth, hReg⟩ := hStep k le_rfl (DynCircExt.writeReg β reg γ)
    fun w hw ↦ DynCircExt.writeReg_apply_of_not_mem β reg γ w fun ⟨i, hi⟩ ↦ hw i i.isLt hi.symm
  funext w
  by_cases hw : w ∈ Set.range reg.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [hReg i i.isLt, DynCircExt.writeReg_apply_reg, DynCircExt.writeReg_apply_reg]
  · rw [hOth w fun i _ e ↦ hw ⟨i, e.symm⟩,
        DynCircExt.writeReg_apply_of_not_mem (G β) reg γ w hw]

theorem circSupportedIn_of_circWires_supp {n : ℕ} {S : Wire n → Prop} :
    ∀ {c : Circuit n}, CircWires S c → CircSupportedIn S c
  | .identity, _ => circSupportedIn_id
  | .seq _ _, ⟨h₁, h₂⟩ =>
    circSupportedIn_seq (circSupportedIn_of_circWires_supp h₁)
        (circSupportedIn_of_circWires_supp h₂)
  | .gate g reg, hreg => fun U ⟨G, hUk, hG⟩ ↦ by
      have ket_d (δ : BitAssignment n) : DynCircExt.ket δ = SplitRouterSeqBell26k.ket δ := rfl
      apply PhotochemistrySolution.SplitRouterSeqBell26k.matrix_ext_ket; intro β
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUk, Circuit.eval_gate,
          QRegister.embedUnitary_val, ← ket_d, DynCircExt.embedMatrix_mulVec_ket,
          DynCircExt.embedMatrix_mulVec_ket, Matrix.mulVec_sum]
      have hLoc : DynCircExt.localIdx reg (G β) = DynCircExt.localIdx reg β := by
        dsimp only [DynCircExt.localIdx]
        congr 1; funext i
        exact actsIndepOf_fix hG (hreg i) β
      rw [hLoc]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Matrix.mulVec_smul, ket_d, hUk,
          writeReg_comm_of_actsIndepOf hG reg hreg β (basisBits _ l)]

theorem dynSupportedIn_of_dynWires_supp {Var : Type} {n : ℕ} {S : Wire n → Prop} :
    ∀ {p : DynamicCircuit Var n}, DynWires S p → DynSupportedIn S p := by
  intro p hp
  induction p with
  | circuit _ => exact circSupportedIn_of_circWires_supp hp
  | measure _ reg =>
      exact ⟨reg.wires 0, hp 0, by
        cases reg with
        | mk wires =>
          dsimp [QRegister.singleton]
          congr 1; ext i; rw [Subsingleton.elim i 0]; rfl⟩
  | qIf _ _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩

/-!
### Part 1: Plane-Index Involutions `rSwapAncBufLo` (`3 ↔ 7`) & `rSwapAncAMsb1` (`7 ↔ 8 + 3*D + 1`)
-/

def swapAncBufLoVal (j : ℕ) : ℕ := if j = 3 then 7 else if j = 7 then 3 else j
theorem swapAncBufLoVal_lt {M D : ℕ} (j : ℕ) (hj : j < planeWidth M D) : swapAncBufLoVal j <
    planeWidth M D := by unfold planeWidth at hj ⊢; unfold swapAncBufLoVal; split_ifs <;> omega
theorem swapAncBufLoVal_invol (j : ℕ) : swapAncBufLoVal (swapAncBufLoVal j) = j := by
  unfold swapAncBufLoVal; split_ifs <;> omega
def rSwapAncBufLo {M D n : ℕ} (r : PlaneReg M D n) : PlaneReg M D n where
  wires :=
    { toFun := fun i ↦ r ⟨swapAncBufLoVal i.val, swapAncBufLoVal_lt i.val i.isLt⟩
      inj' := fun i₁ i₂ h ↦ by
        have hv := congrArg Fin.val (r.wires.injective h); dsimp at hv;
        have :=
            congrArg swapAncBufLoVal hv; rw [swapAncBufLoVal_invol, swapAncBufLoVal_invol] at this
        exact Fin.ext this }

theorem rSwapAncBufLo_apply_of_ne {M D n : ℕ} (r : PlaneReg M D n) (i : Fin (planeWidth M D))
    (h3 : i.val ≠ 3) (h7 : i.val ≠ 7) : rSwapAncBufLo r i = r i :=
  congrArg r.wires (Fin.ext (by dsimp [rSwapAncBufLo]; unfold swapAncBufLoVal; split_ifs <;> omega))

theorem rSwapAncBufLo_pAnc {M D n : ℕ} (r : PlaneReg M D n) : pAnc (rSwapAncBufLo r) = pBufLo r :=
  congrArg r.wires (Fin.ext rfl)

theorem rSwapAncBufLo_roles {M D n : ℕ} (r : PlaneReg M D n) : pHas1 (rSwapAncBufLo r) = pHas1 r ∧
    pHas2Eff (rSwapAncBufLo r) = pHas2Eff r ∧ pBufHi (rSwapAncBufLo r) = pBufHi r ∧
    pHA (rSwapAncBufLo r) = pHA r ∧ pHB (rSwapAncBufLo r) = pHB r ∧ pUMsb (rSwapAncBufLo r) =
    pUMsb r ∧ pNotMin (rSwapAncBufLo r) = pNotMin r ∧ pNotMax (rSwapAncBufLo r) = pNotMax r ∧
    pAMsb (rSwapAncBufLo r) = pAMsb r ∧ pCReg (rSwapAncBufLo r) = pCReg r ∧
    pCtrlLo (rSwapAncBufLo r) = pCtrlLo r ∧ pCtrlHi (rSwapAncBufLo r) = pCtrlHi r ∧
    pSys (rSwapAncBufLo r) = pSys r := by
  have out := rSwapAncBufLo_apply_of_ne r
  have s0 {i : Fin (planeWidth M D)} (h3 : i.val ≠ 3) (h7 : i.val ≠ 7) := out i h3 h7
  exact ⟨s0 (by dsimp; omega) (by dsimp; omega), s0 (by dsimp; omega) (by dsimp; omega),
    s0 (by dsimp; omega) (by dsimp; omega), s0 (by dsimp; omega) (by dsimp; omega),
    s0 (by dsimp; omega) (by dsimp; omega),
    funext fun d ↦ out _ (by dsimp [pUMsb]; omega) (by dsimp [pUMsb]; omega),
    funext fun d ↦ out _ (by dsimp [pNotMin]; omega) (by dsimp [pNotMin]; omega),
    funext fun d ↦ out _ (by dsimp [pNotMax]; omega) (by dsimp [pNotMax]; omega),
    funext fun d ↦ out _ (by dsimp [pAMsb]; omega) (by dsimp [pAMsb]; omega),
    funext fun d ↦ out _ (by dsimp [pCReg]; omega) (by dsimp [pCReg]; omega),
    funext fun p ↦ out _ (by dsimp [pCtrlLo]; omega) (by dsimp [pCtrlLo]; omega),
    funext fun p ↦ out _ (by dsimp [pCtrlHi]; omega) (by dsimp [pCtrlHi]; omega),
    funext fun p ↦ out _ (by dsimp [pSys]; omega) (by dsimp [pSys]; omega)⟩

/-! ### Part 2: `rL` / `rA` Invariance of Target Circuits -/

/-!
### Part 3: Commutation of `cCloseMuxAlwaysLoCirc` with `uPlaneXorCtrl` , `uScrubAMsbHi` , and
`projBit (pAMsb r d) 0`
-/

/-! ### Part 4: `pDualBellPlaneAlwaysLoNoAncDyn` (`0` `pAnc` Wires!) -/

/-!
### Part 5: `pSemiBellPlaneAlwaysLoNoAncDyn` , `pSemiBellPlanesAlwaysLoNoAncMD` , &
`subspaceStep_planes_zgModeMuxD1AlwaysLo_noAnc_hb0`
-/
end QuantumComputation.Specs.PhotochemistrySolution.PlanesAlwaysLoNoAnc
end

namespace QuantumComputation.Specs.PhotochemistrySolution.WCompElec187At368
export _root_.QuantumComputation.Specs.PhotochemistrySolution.AlwaysLo25860Opt (wComp187_368
    count_wComp187_368 dynWires_wComp187_368 subspaceStep_wComp187_368)
end QuantumComputation.Specs.PhotochemistrySolution.WCompElec187At368

end
