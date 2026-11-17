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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.HalfPlaneCauchyWalkCore
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option Elab.async false
set_option allowUnsafeReducibility true
set_option autoImplicit false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.DepthArithWalk
  QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
  QuantumComputation.Specs.PhotochemistrySolution.OuterW11Alt
open QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse
  QuantumComputation.Specs.PhotochemistrySolution.AlwaysLo25860Opt
  QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47
open QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
  QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu
  QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254
  QuantumComputation.Specs.PhotochemistrySolution.GenWeightsSelect
open QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA
  QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open QuantumComputation.Specs.PhotochemistrySolution.CoulombFast
  QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70
  QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (CommutesWithDyn
    subspaceStep_congr_out subspaceStep_mul_left_of_commutesWithDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_of_circuit subspaceStep_congr_in specFanoutCopyVecCirc bellXHalfVecDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (count_bellXHalfVecDyn_t count_bellXHalfVecDyn_toff fanoutXorBits fanoutXorBits_of_ne_tgt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (specFanoutCopyCirc specFanoutCopyCirc_mulVec_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (SharedPortBInput341
    supportedOn_and SharedPortBWiring.ofValidMuxD1_341)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (totDimCompactGen
    ancWOfScr BlockApproxSpecGen projOneQCompactGen SelectLocalSpecGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (LocalUnitary
    cat8SharedProjCompactGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (ValidPotBFlags
    potBGateActive reflPackPair_ne ReflPotSliceSpec owCompose_disj val_wPotFlags_rPot0Layout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1 (validMuxD1Stage2Regs_sub
    rNucSub rElecSub elecSubWireFn nucSubWireFn val_elecSubWireFn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1 (val_nucSubWireFn
    privRank454Sub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream (cHiNSub341
    val_cHiNSub341 cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (PotExpectFn
    speciesOfBits2 coordOfReg24 wPotBLocQ wPotBIsScreen wPotBIsPot wPotBIsNN wPotBSp1B0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (wPotBSp1B1 wPotBSp2B0
    wPotBSp2B1 rPotBNucA rPotBElecA rPotBPortB rPotBWork)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore (ActiveOuterCoinStackOf
    outerCoinAncillasStack OuterCoinSelectBundleStackAsym hpStack)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (Wtop wtop_ge192 r41_ne
    r41_blk_ne_blk r41_blk_ne_wire r41_wire_ne_blk rMuxZ16 rMuxD2_18 muxSt muxD2Val)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (ReflPotSliceSpec35
    coordOfReg24_congr wMuxScr0 rMuxM1 rMuxM2 writeSub24 writeSub24_apply_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (writeSub24_apply_reg
    writeSub24_zero eq_of_r41_parts muxSt_m1 muxSt_m2 openCoordDistSq_muxSt_m1_m2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam (take35Of41_wstate
    put35In41_wstate liftReflPotSlice35To41_wstate skip6Of122Wp_wstate)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam (val_skip6Of122Wp_wstate
    hk0_le72_wstate rPermPot103 rPermPot103_fix_of_bounds)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload (s7OfHBE padNOfS7
    padEOfS7 qEncOfS7 padWires_mem PortOnlyHiMod uSharedHiPortOnlyConj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload
    (uSharedHiPortOnlyConj_mulVec_ket unloadHiPred_congr stage5PortOnlyScratch_s7OfHBE)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles (DynWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge (CircWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA (dLayout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge (scrSubLGen lcuSubLGen
    reflULGen)
noncomputable section
set_option exponentiation.threshold 256
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin63
open QProg Qubit
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, p => p k && allBelow k p

theorem allBelow_true_iff : ∀ (n : ℕ) (p : ℕ → Bool),
    allBelow n p = true ↔ ∀ k < n, p k = true
  | 0, _ => ⟨fun _ _ hk ↦ absurd hk (by omega), fun _ ↦ rfl⟩
  | n + 1, p => by
      dsimp only [allBelow]
      rw [Bool.and_eq_true, allBelow_true_iff n p]
      exact ⟨fun ⟨hp, hall⟩ k hk ↦ if hkn : k = n then hkn.symm ▸ hp else hall k (by omega),
        fun h ↦ ⟨h n (by omega), fun k hk ↦ h k (by omega)⟩⟩
open Operator Matrix Circuit PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt
    natOfZModBits_testBit_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (clbGam6)
theorem clbGam6_bit_eq (w : Fin 2048) {b : ℕ} (hb : b < 6) :
    (clbGam6 w.val).testBit b =
      xor (w.val.testBit (10 - b)) (decide (b = 0 ∨ b = 2 ∨ b = 4)) := by
  have hc : allBelow 2048 (fun u ↦ allBelow 6 (fun j ↦ decide
      ((clbGam6 u).testBit j = xor (u.testBit (10 - j))
        (decide (j = 0 ∨ j = 2 ∨ j = 4))))) = true := by decide +kernel
  exact of_decide_eq_true ((allBelow_true_iff 6 _).mp
    ((allBelow_true_iff 2048 _).mp hc w.val w.isLt) b hb)
attribute [local irreducible] FineLegendre.natOfZModBits PopBernstein.popBernJ clbGam6

end QuantumComputation.Specs.PhotochemistrySolution.SubCoin63

namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4
open Operator QProg Matrix Circuit Qubit PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
theorem zmod2_eq_of_beq_one_eq_s1b (x : ZMod 2) (b : Bool) (h : (x == 1) = b) : x =
    if b then 1 else 0 := by
  rcases DynCircExt.bit_cases x with rfl | rfl <;> subst h <;> decide
/-! ### Step 1B.2: `24`-Inner-Coin `PortB` Interface (`Stage4ReflCoin24PotOraclePortBCtrlSafe`) -/
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 (RouterReg)
theorem potB24Idx0_lt {W : ℕ} : 0 < 105 + W := by omega
theorem potB24Idx1_lt {W : ℕ} : 1 < 105 + W := by omega
theorem potB24Idx2_lt {W : ℕ} : 2 < 105 + W := by omega
theorem potB24Idx4_lt {W : ℕ} : 4 < 105 + W := by omega
theorem potB24Idx5_lt {W : ℕ} : 5 < 105 + W := by omega
theorem potB24Idx6_lt {W : ℕ} : 6 < 105 + W := by omega
theorem potB24Idx7_lt {W : ℕ} : 7 < 105 + W := by omega
theorem potB24Idx8_lt {W : ℕ} : 8 < 105 + W := by omega
theorem potB24BlkNucA_le {W : ℕ} : 9 + 24 ≤ 105 + W := by omega
theorem potB24BlkElecA_le {W : ℕ} : 33 + 24 ≤ 105 + W := by omega
theorem potB24BlkPortB_le {W : ℕ} : 57 + 24 ≤ 105 + W := by omega
theorem potB24BlkCoin24_le {W : ℕ} : 81 + 24 ≤ 105 + W := by omega
theorem potB24BlkWork_le {W : ℕ} : 105 + W ≤ 105 + W := le_rfl

abbrev wPotB24LocQ {W n : ℕ} (r : QRegister (105 + W) n) : Wire n := r ⟨0, potB24Idx0_lt⟩
abbrev wPotB24IsScreen {W n : ℕ} (r : QRegister (105 + W) n) : Wire n := r ⟨1, potB24Idx1_lt⟩
abbrev wPotB24IsPot {W n : ℕ} (r : QRegister (105 + W) n) : Wire n := r ⟨2, potB24Idx2_lt⟩
abbrev wPotB24IsNN {W n : ℕ} (r : QRegister (105 + W) n) : Wire n := r ⟨4, potB24Idx4_lt⟩
abbrev wPotB24Sp1B0 {W n : ℕ} (r : QRegister (105 + W) n) : Wire n := r ⟨5, potB24Idx5_lt⟩
abbrev wPotB24Sp1B1 {W n : ℕ} (r : QRegister (105 + W) n) : Wire n := r ⟨6, potB24Idx6_lt⟩
abbrev wPotB24Sp2B0 {W n : ℕ} (r : QRegister (105 + W) n) : Wire n := r ⟨7, potB24Idx7_lt⟩
abbrev wPotB24Sp2B1 {W n : ℕ} (r : QRegister (105 + W) n) : Wire n := r ⟨8, potB24Idx8_lt⟩
abbrev rPotB24NucA {W n : ℕ} (r : QRegister (105 + W) n) : QRegister 24 n :=
    r.compose (QRegister.block 9 24 potB24BlkNucA_le)
abbrev rPotB24ElecA {W n : ℕ} (r : QRegister (105 + W) n) : QRegister 24 n :=
    r.compose (QRegister.block 33 24 potB24BlkElecA_le)
abbrev rPotB24PortB {W n : ℕ} (r : QRegister (105 + W) n) : QRegister 24 n :=
    r.compose (QRegister.block 57 24 potB24BlkPortB_le)
abbrev rPotBCoin24 {W n : ℕ} (r : QRegister (105 + W) n) : QRegister 24 n :=
    r.compose (QRegister.block 81 24 potB24BlkCoin24_le)
abbrev rPotBWork24 {W n : ℕ} (r : QRegister (105 + W) n) : QRegister W n :=
    r.compose (QRegister.block 105 W potB24BlkWork_le)
abbrev PotBPhaseBit24Fn : Type :=
    Bool → Bool → Fin 4 → Fin 4 → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    (Fin 3 → Fin 256) → BitAssignment 24 → ZMod 2
abbrev PotBCoinSwap24Fn : Type :=
    Bool → Bool → Fin 4 → Fin 4 → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    (Fin 3 → Fin 256) → BitAssignment 24 → BitAssignment 24
def ValidPotBFlags24 {W n : ℕ} (r : QRegister (105 + W) n) (β : BitAssignment n) : Prop :=
    (β (wPotB24IsPot r) = 0 → β (wPotB24IsScreen r) = 0 ∧ β (wPotB24IsNN r) = 0) ∧
    (β (wPotB24IsScreen r) = 0 → β (wPotB24IsNN r) = 0)
abbrev potOraclePortB24BitEval {W n : ℕ} (phaseBit : PotBPhaseBit24Fn) (r : QRegister (105 + W) n)
    (δ : BitAssignment n) : ZMod 2 :=
    phaseBit (δ (wPotB24IsScreen r) == 1) (δ (wPotB24IsNN r) == 1)
    (speciesOfBits2 (δ (wPotB24Sp1B0 r)) (δ (wPotB24Sp1B1 r))) (speciesOfBits2 (δ (wPotB24Sp2B0 r))
    (δ (wPotB24Sp2B1 r))) (coordOfReg24 (rPotB24NucA r) δ)
    (if δ (wPotB24IsNN r) == 1 then coordOfReg24 (rPotB24PortB r) δ else 0)
    (coordOfReg24 (rPotB24ElecA r) δ)
    (if δ (wPotB24IsNN r) == 1 then 0 else coordOfReg24 (rPotB24PortB r) δ)
    (fun k ↦ δ (rPotBCoin24 r k))
abbrev potOraclePortB24CoinEval {W n : ℕ} (coinSwap : PotBCoinSwap24Fn) (r : QRegister (105 + W) n)
    (δ : BitAssignment n) : BitAssignment 24 :=
    coinSwap (δ (wPotB24IsScreen r) == 1) (δ (wPotB24IsNN r) == 1)
    (speciesOfBits2 (δ (wPotB24Sp1B0 r)) (δ (wPotB24Sp1B1 r))) (speciesOfBits2 (δ (wPotB24Sp2B0 r))
    (δ (wPotB24Sp2B1 r))) (coordOfReg24 (rPotB24NucA r) δ)
    (if δ (wPotB24IsNN r) == 1 then coordOfReg24 (rPotB24PortB r) δ else 0)
    (coordOfReg24 (rPotB24ElecA r) δ)
    (if δ (wPotB24IsNN r) == 1 then 0 else coordOfReg24 (rPotB24PortB r) δ)
    (fun k ↦ δ (rPotBCoin24 r k))
def potB24GateActive {W n : ℕ} (isCsel : Bool) (r : QRegister (105 + W) n) (δ : BitAssignment n) :
    Bool :=
    if isCsel then (δ (wPotB24LocQ r) == 1) &&
    (δ (wPotB24IsPot r) == 1) else (δ (wPotB24IsPot r) == 1)
def potReflPortBSt24 {kCoin W n : ℕ} (coinSwapK : BitAssignment kCoin → PotBCoinSwap24Fn)
    (isCsel : Bool) (r : QRegister (105 + W) n) (rCoin : QRegister kCoin n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
    if potB24GateActive isCsel r (st δ) then writeReg (st δ) (rPotBCoin24 r)
    (potOraclePortB24CoinEval (coinSwapK (fun j ↦ st δ (rCoin j))) r (st δ)) else st δ
def potReflPortBPh0_24 {kCoin W n : ℕ} (phaseBitK : BitAssignment kCoin → PotBPhaseBit24Fn)
    (isCsel : Bool) (r : QRegister (105 + W) n) (rCoin : QRegister kCoin n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : ZMod 2 :=
    (if isCsel then st δ (wPotB24LocQ r) * st δ (wPotB24IsPot r) else st δ (wPotB24IsPot r)) *
    potOraclePortB24BitEval (phaseBitK (fun j ↦ st δ (rCoin j))) r (st δ)
structure ReflPotSliceSpec24 (potExpect : PotExpectFn) where
  phaseBit : PotBPhaseBit24Fn
  coinSwap : PotBCoinSwap24Fn
  coinSwap_invol : ∀ s nn sp1 sp2 nA nB eA eB z,
    coinSwap s nn sp1 sp2 nA nB eA eB (coinSwap s nn sp1 sp2 nA nB eA eB z) = z
  phaseBit_coinSwap : ∀ s nn sp1 sp2 nA nB eA eB z,
    phaseBit s nn sp1 sp2 nA nB eA eB (coinSwap s nn sp1 sp2 nA nB eA eB z) =
      phaseBit s nn sp1 sp2 nA nB eA eB z
  phaseBit_port : ∀ s nn sp1 sp2 nA nB eA eB z,
    phaseBit s nn sp1 sp2 nA (if nn then nB else 0) eA (if nn then 0 else eB) z =
      phaseBit s nn sp1 sp2 nA nB eA eB z
  coinSwap_port : ∀ s nn sp1 sp2 nA nB eA eB z,
    coinSwap s nn sp1 sp2 nA (if nn then nB else 0) eA (if nn then 0 else eB) z =
      coinSwap s nn sp1 sp2 nA nB eA eB z
  avg_coin24 : ∀ (isScreen isNN : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256),
    (2 ^ 24 : ℂ)⁻¹ *
      (∑ z : BitAssignment 24, bitSign (phaseBit isScreen isNN sp1 sp2 nA nB eA eB z)) =
      (potExpect isScreen isNN sp1 sp2 nA nB eA eB : ℂ)

theorem of3Port24_port_eq {α : Type*} (f3 : Bool → Bool → Fin 4 → Fin 4 → (Fin 3 → Fin 256) →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → BitAssignment 24 → α) (s nn : Bool) (sp1 sp2 : Fin 4)
    (nA nB eA eB : Fin 3 → Fin 256) (z : BitAssignment 24) :
    f3 s nn sp1 sp2 nA (if nn then (if nn then nB else 0) else (if nn then 0 else eB)) eA z =
    f3 s nn sp1 sp2 nA (if nn then nB else eB) eA z := by
  cases nn <;> rfl

def ReflPotSliceSpec24.of3Port {potExpect : PotExpectFn}
    (phaseBit3 : Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → BitAssignment 24 → ZMod 2)
    (coinSwap3 : Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      BitAssignment 24 → BitAssignment 24)
    (hInv : ∀ s nn sp1 sp2 nA pB eA z,
      coinSwap3 s nn sp1 sp2 nA pB eA (coinSwap3 s nn sp1 sp2 nA pB eA z) = z)
    (hPh : ∀ s nn sp1 sp2 nA pB eA z,
      phaseBit3 s nn sp1 sp2 nA pB eA (coinSwap3 s nn sp1 sp2 nA pB eA z) =
        phaseBit3 s nn sp1 sp2 nA pB eA z)
    (hAvg : ∀ (s nn : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256),
      (2 ^ 24 : ℂ)⁻¹ *
        (∑ z : BitAssignment 24,
          bitSign (phaseBit3 s nn sp1 sp2 nA (if nn then nB else eB) eA z)) =
        (potExpect s nn sp1 sp2 nA nB eA eB : ℂ)) :
    ReflPotSliceSpec24 potExpect where
  phaseBit s nn sp1 sp2 nA nB eA eB z :=
    phaseBit3 s nn sp1 sp2 nA (if nn then nB else eB) eA z
  coinSwap s nn sp1 sp2 nA nB eA eB z :=
    coinSwap3 s nn sp1 sp2 nA (if nn then nB else eB) eA z
  coinSwap_invol _ _ _ _ _ _ _ _ z := hInv _ _ _ _ _ _ _ z
  phaseBit_coinSwap _ _ _ _ _ _ _ _ z := hPh _ _ _ _ _ _ _ z
  phaseBit_port := of3Port24_port_eq phaseBit3
  coinSwap_port := of3Port24_port_eq coinSwap3
  avg_coin24 := hAvg
/-! ### Step 1B.3: `SubCoin63` `(γ : BitAssignment 17, z : BitAssignment 24)` Slice Spec -/
open Real
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PrimGateEval (natOfZModBits_lt)
attribute [local irreducible] PhotochemistrySolution.Stage4FineFast.natOfBoolBits
def w11Sub63 (γ : BitAssignment 17) : Fin 2048 :=
  ⟨natOfZModBits 11 (fun k ↦ γ ⟨k.val, by omega⟩), natOfZModBits_lt 11 _⟩

def zHi16Of24 (z : BitAssignment 24) : ℕ :=
  natOfZModBits 16 (fun j ↦ z ⟨8 + j.val, by omega⟩)

def equivBitZMod2 : ZMod 2 ≃ Fin 2 where
  toFun b := ⟨if b == 1 then 1 else 0, by split_ifs <;> omega⟩
  invFun u := if u.val = 1 then 1 else 0
  left_inv b := by rcases DynCircExt.bit_cases b with rfl | rfl <;> decide
  right_inv u := by fin_cases u <;> decide
end QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4

/-! ### Step 1B.4a: `Mux48` `r41Of24` / `rC12Of41` Adapter and `pMuxStageBScr_sub63` -/

namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4
open Operator QProg Matrix Circuit Qubit PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PrimGateEval (natOfZModBits_lt)
def f41Of24 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n) (i : Fin (122 + Wp)) :
    Wire n :=
  if h1 : i.val < 81 then r ⟨i.val, by omega⟩
  else if h2 : i.val < 91 then rCoin ⟨7 + (i.val - 81), by omega⟩
  else if h3 : i.val < 92 then r ⟨81, by omega⟩
  else if h4 : i.val < 99 then rCoin ⟨i.val - 92, by omega⟩
  else r ⟨i.val - 17, by have := i.isLt; omega⟩

def invR41Sub63 (k : ℕ) : ℕ := if k < 81 then k else if k = 81 then 91 else k + 17
def invC41Sub63 (j : ℕ) : ℕ := if j < 7 then 92 + j else 81 + (j - 7)
theorem f41Of24_tag {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (i : Fin (122 + Wp)) : (∃ k : Fin (105 + Wp), f41Of24 r rCoin i = r k ∧ invR41Sub63 k.val =
    i.val) ∨ (∃ j : Fin 17, f41Of24 r rCoin i = rCoin j ∧ invC41Sub63 j.val = i.val) := by
  have hi := i.isLt; unfold f41Of24
  split_ifs with h1 h2 h3 h4
  · exact Or.inl ⟨⟨i.val, by omega⟩, rfl, by unfold invR41Sub63; dsimp only; split_ifs; omega⟩
  · exact Or.inr ⟨⟨7 + (i.val - 81), by omega⟩, rfl,
      by unfold invC41Sub63; dsimp only; split_ifs <;> omega⟩
  · exact Or.inl ⟨⟨81, by omega⟩, rfl, by unfold invR41Sub63; dsimp only; split_ifs <;> omega⟩
  · exact Or.inr ⟨⟨i.val - 92, by omega⟩, rfl,
      by unfold invC41Sub63; dsimp only; split_ifs <;> omega⟩
  · exact Or.inl ⟨⟨i.val - 17, by omega⟩, rfl,
      by unfold invR41Sub63; dsimp only; split_ifs <;> omega⟩

theorem f41Of24_inj {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) : Function.Injective (f41Of24 r rCoin) := by
  intro a b hab
  rcases f41Of24_tag r rCoin a with ⟨ka, ha, hia⟩ | ⟨ja, ha, hia⟩ <;>
    rcases f41Of24_tag r rCoin b with ⟨kb, hb, hib⟩ | ⟨jb, hb, hib⟩
  · rw [ha, hb] at hab; have hk := congrArg Fin.val (r.wires.injective hab)
    exact Fin.ext (by rw [← hia, ← hib, hk])
  · rw [ha, hb] at hab; exact False.elim (disj_ne hd _ _ hab)
  · rw [ha, hb] at hab; exact False.elim (disj_ne hd _ _ hab.symm)
  · rw [ha, hb] at hab; have hj := congrArg Fin.val (rCoin.wires.injective hab)
    exact Fin.ext (by rw [← hia, ← hib, hj])

def r41Of24 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) : QRegister (122 + Wp) n :=
    ⟨⟨f41Of24 r rCoin, f41Of24_inj r rCoin hd⟩⟩
theorem r41Of24_lt81 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) {m : ℕ} (hm : m < 81) :
    r41Of24 r rCoin hd ⟨m, by omega⟩ = r ⟨m, by omega⟩ := by
  change f41Of24 r rCoin ⟨m, _⟩ = _; dsimp only [f41Of24]; simp only [hm, ↓reduceDIte]

theorem r41Of24_hi99 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) {m : ℕ} (hlo : 99 ≤ m) (hhi : m < 122 + Wp) :
    r41Of24 r rCoin hd ⟨m, hhi⟩ = r ⟨m - 17, by omega⟩ := by
  change f41Of24 r rCoin ⟨m, hhi⟩ = _
  dsimp only [f41Of24]
  split_ifs <;> first | rfl | omega

theorem r41Of24_z16 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) (j : Fin 16) :
    rMuxZ16 (r41Of24 r rCoin hd) j = rPotBCoin24 r ⟨8 + j.val, by omega⟩ := by
  have heq : rMuxZ16 (r41Of24 r rCoin hd) j = r41Of24 r rCoin hd ⟨106 + j.val, by omega⟩ :=
    congrArg (r41Of24 r rCoin hd).wires (Fin.ext (by simp only [QRegister.block_apply_val]))
  exact heq.trans ((r41Of24_hi99 r rCoin hd (by omega) (by omega)).trans
    (congrArg r.wires (Fin.ext (by dsimp [rPotBCoin24]; omega))))

theorem r41Of24_work {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) (u : Fin Wp) : rPotBWork (r41Of24 r rCoin hd) u =
    rPotBWork24 r u :=
  (r41Of24_hi99 r rCoin hd (m := 122 + u.val) (by omega) (by omega)).trans
    (congrArg r.wires (Fin.ext (by dsimp [rPotBWork24]; omega)))

theorem r41Of24_blocks {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) : rPotBNucA (r41Of24 r rCoin hd) = rPotB24NucA r ∧
    rPotBElecA (r41Of24 r rCoin hd) = rPotB24ElecA r ∧ rPotBPortB (r41Of24 r rCoin hd) =
    rPotB24PortB r := by
  have hb (o : ℕ) (h1 : o + 24 ≤ 122 + Wp) (h2 : o + 24 ≤ 105 + Wp) (ho : o + 24 ≤ 81) :
      (r41Of24 r rCoin hd).compose (QRegister.block o 24 h1) =
        r.compose (QRegister.block o 24 h2) :=
    QRegister.ext (Function.Embedding.ext fun ⟨v, hv⟩ ↦
      r41Of24_lt81 r rCoin hd (m := o + v) (by omega))
  exact ⟨hb 9 _ _ (by decide), hb 33 _ _ (by decide), hb 57 _ _ (by decide)⟩

theorem r41Of24_ctrl {Wp n : ℕ} {S_ctrl : Wire n → Prop} (r : QRegister (105 + Wp) n)
    (rCoin : QRegister 17 n) (hd : r.DisjointWires rCoin) (hSr : ∀ i, S_ctrl (r i))
    (hSc : ∀ j, S_ctrl (rCoin j)) (i : Fin (122 + Wp)) : S_ctrl (r41Of24 r rCoin hd i) := by
  change S_ctrl (f41Of24 r rCoin i); unfold f41Of24
  split_ifs <;> [exact hSr _; exact hSc _; exact hSr _; exact hSc _; exact hSr _]

theorem validPotBFlags_r41Of24 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) {δ : BitAssignment n} (h : ValidPotBFlags24 r δ) :
    ValidPotBFlags (r41Of24 r rCoin hd) δ := by
  dsimp only [ValidPotBFlags, ValidPotBFlags24, wPotBIsPot, wPotBIsScreen, wPotBIsNN,
    wPotB24IsPot, wPotB24IsScreen, wPotB24IsNN] at h ⊢
  rwa [r41Of24_lt81 r rCoin hd (m := 2) (by decide), r41Of24_lt81 r rCoin hd (m := 1) (by decide),
       r41Of24_lt81 r rCoin hd (m := 4) (by decide)]

theorem potBGateActive_r41Of24 {Wp n : ℕ} (isCsel : Bool) (r : QRegister (105 + Wp) n)
    (rCoin : QRegister 17 n) (hd : r.DisjointWires rCoin) (δ : BitAssignment n) :
    potBGateActive isCsel (r41Of24 r rCoin hd) δ = potB24GateActive isCsel r δ := by
  unfold potBGateActive potB24GateActive wPotBLocQ wPotBIsPot wPotB24LocQ wPotB24IsPot
  rw [r41Of24_lt81 r rCoin hd (m := 0) (by decide), r41Of24_lt81 r rCoin hd (m := 2) (by decide)]

theorem natOfZModBits_one_eq (f : Fin 1 → ZMod 2) :
    natOfZModBits 1 f = if f ⟨0, by omega⟩ == 1 then 1 else 0 := by
  rw [← finBitsVal_eq_natOfZModBits]
  rcases DynCircExt.bit_cases (f ⟨0, by decide⟩) with h | h
  · rw [show f = fun _ ↦ 0 from funext fun i ↦ (congrArg f (Subsingleton.elim i _)).trans h]
    decide
  · rw [show f = fun _ ↦ 1 from funext fun i ↦ (congrArg f (Subsingleton.elim i _)).trans h]
    decide
end QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4

/-! ### Part 1C.2: `24 -> 35 -> 41` PortB Oracle Lift & `ReflPotSlice24Only` -/

namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Walk
open Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution.KetSupport
  PhotochemistrySolution.PotOraclePortB PhotochemistrySolution.PotOraclePortBStream
  PhotochemistrySolution.PotOraclePortBStage4 PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.PortBSharedPoly
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (ReflPotSliceSpec24
    ValidPotBFlags24 rPotBCoin24 rPotBWork24 potReflPortBSt24 potReflPortBPh0_24
    potOraclePortB24BitEval potOraclePortB24CoinEval potB24GateActive wPotB24LocQ wPotB24IsScreen
    wPotB24IsPot wPotB24IsNN wPotB24Sp1B0 wPotB24Sp1B1 wPotB24Sp2B0 wPotB24Sp2B1 rPotB24NucA
    rPotB24ElecA rPotB24PortB)
def take24Of35_sub63 (z : BitAssignment 35) : BitAssignment 24 :=
  fun j ↦ z ⟨j.val, Nat.lt_trans j.isLt (by decide : 24 < 35)⟩

def put24In35_sub63 (z24 : BitAssignment 24) (z : BitAssignment 35) : BitAssignment 35 := fun i ↦
    if h : i.val < 24 then z24 ⟨i.val, h⟩ else z i
def equiv35_split24_11_sub63 : BitAssignment 35 ≃ BitAssignment 24 × BitAssignment 11 where
  toFun z := (take24Of35_sub63 z, fun j ↦ z ⟨24 + j.val, by have := j.isLt; omega⟩)
  invFun p := fun i ↦
    if h : i.val < 24 then p.1 ⟨i.val, h⟩
    else p.2 ⟨i.val - 24, by have := i.isLt; omega⟩
  left_inv z := funext fun i ↦ by
    by_cases h : i.val < 24
    · simp [take24Of35_sub63, h]
    · simp only [h, ↓reduceDIte]
      exact congrArg z (Fin.ext (by dsimp; omega))
  right_inv p := Prod.ext
    (funext fun j ↦ by simp [take24Of35_sub63, j.isLt])
    (funext fun j ↦ by
      have hn : ¬ (24 + j.val < 24) := by omega
      simp only [hn, ↓reduceDIte]
      exact congrArg p.2 (Fin.ext (by dsimp; omega)))

def liftReflPotSlice24To35_sub63 {potExpect : PotExpectFn} (s : ReflPotSliceSpec24 potExpect) :
    ReflPotSliceSpec35 potExpect where
  phaseBit s0 nn sp1 sp2 nA nB eA eB z :=
    s.phaseBit s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z)
  coinSwap s0 nn sp1 sp2 nA nB eA eB z :=
    put24In35_sub63 (s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z)) z
  coinSwap_invol s0 nn sp1 sp2 nA nB eA eB z := funext fun i ↦ by
    have hTake : take24Of35_sub63
        (put24In35_sub63 (s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z)) z) =
        s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z) :=
      funext fun j ↦ by simp [take24Of35_sub63, put24In35_sub63, j.isLt]
    rw [hTake, s.coinSwap_invol]
    by_cases hi : i.val < 24 <;> simp [put24In35_sub63, take24Of35_sub63, hi]
  phaseBit_coinSwap s0 nn sp1 sp2 nA nB eA eB z := by
    have hTake : take24Of35_sub63
        (put24In35_sub63 (s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z)) z) =
        s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z) :=
      funext fun j ↦ by simp [take24Of35_sub63, put24In35_sub63, j.isLt]
    rw [hTake]; exact s.phaseBit_coinSwap s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z)
  phaseBit_port s0 nn sp1 sp2 nA nB eA eB z :=
    s.phaseBit_port s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z)
  coinSwap_port s0 nn sp1 sp2 nA nB eA eB z :=
    congrArg (fun u ↦ put24In35_sub63 u z)
      (s.coinSwap_port s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z))
  avg_coin35 s0 nn sp1 sp2 nA nB eA eB := by
    let f : BitAssignment 35 → ℂ := fun z ↦
        bitSign (s.phaseBit s0 nn sp1 sp2 nA nB eA eB (take24Of35_sub63 z))
    change (2 ^ 35 : ℂ)⁻¹ * ∑ z : BitAssignment 35, f z =
        (potExpect s0 nn sp1 sp2 nA nB eA eB : ℂ); rw [← Equiv.sum_comp
        equiv35_split24_11_sub63.symm f, Fintype.sum_prod_type]
    have hPoint : ∀ (z24 : BitAssignment 24) (z11 : BitAssignment 11),
        f (equiv35_split24_11_sub63.symm (z24, z11)) =
          bitSign (s.phaseBit s0 nn sp1 sp2 nA nB eA eB z24) := fun z24 z11 ↦ by
      dsimp only [f]
      rw [show take24Of35_sub63 (equiv35_split24_11_sub63.symm (z24, z11)) = z24 from
        congrArg Prod.fst (equiv35_split24_11_sub63.apply_symm_apply (z24, z11))]
    simp_rw [hPoint]
    have hCard11 : Fintype.card (BitAssignment 11) = 2 ^ 11 := by
      dsimp only [BitAssignment]; rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    simp only [Finset.sum_const, Finset.card_univ, hCard11, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, ← Finset.mul_sum, ← mul_assoc]
    have h2 : (2 ^ 35 : ℂ)⁻¹ * (2 : ℂ) ^ 11 = (2 ^ 24 : ℂ)⁻¹ := by
      have h35 : (2 : ℂ) ^ 35 = (2 : ℂ) ^ 24 * (2 : ℂ) ^ 11 := by norm_num
      rw [h35, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 11 two_ne_zero), mul_one]
    rw [h2]; exact s.avg_coin24 s0 nn sp1 sp2 nA nB eA eB
def skip11Val_sub63 (k : ℕ) : ℕ := if k < 105 then k else k + 11
theorem skip11Val_lt_sub63 {Wp : ℕ} (i : Fin (105 + Wp)) : skip11Val_sub63 i.val < 116 + Wp := by
  have := i.isLt; unfold skip11Val_sub63; split_ifs <;> omega
/--
Subregister embedding `105 + Wp` into `116 + Wp` skipping retired inner coins `105 .. 115`
-/
def skip11Of116Wp_sub63 (Wp : ℕ) : QRegister (105 + Wp) (116 + Wp) where
  wires :=
    { toFun := fun i ↦ ⟨skip11Val_sub63 i.val, skip11Val_lt_sub63 i⟩
      inj' := fun a b h ↦ by
        have hv := congrArg Fin.val h
        dsimp [skip11Val_sub63] at hv; split_ifs at hv <;> exact Fin.ext (by omega) }

theorem val_skip11Of116Wp_sub63 {Wp : ℕ} (i : Fin (105 + Wp)) :
    (skip11Of116Wp_sub63 Wp i).val = if i.val < 105 then i.val else i.val + 11 := rfl

theorem circWires_cPackCnotAux_skip17_sub63 {W n : ℕ} {S : Wire n → Prop}
    (r : QRegister (122 + W) n) (h24 : 24 ≤ W)
    (hr : ∀ j : Fin (122 + W), (j.val < 105 ∨ 122 ≤ j.val) → S (r j)) :
    ∀ (k : ℕ) (hk : k ≤ 24), UnembedO3Bridge.CircWires S (cPackCnotAux r h24 k hk)
  | 0, _ => trivial
  | k + 1, hk =>
      ⟨circWires_cPackCnotAux_skip17_sub63 r h24 hr k (Nat.le_of_succ_le hk),
        fun | ⟨0, _⟩ => hr ⟨122 + k, by omega⟩ (Or.inr (Nat.le_add_right 122 k))
            | ⟨1, _⟩ => hr ⟨57 + k, by omega⟩ (Or.inl (show 57 + k < 105 by omega))⟩
/-!
### Part 1C.3: `Stack63` Wire-Footprint Helpers & `65` -Coin (`mCoin = 63`) Hadamard Cancellation
-/
end QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Walk

/-! ### Part 4B: Persistent `R6Tree` Prefix/Suffix `ST4` Direct `[0, 195076)` ULP Engine -/

namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs
open Real
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp
    (clbGam6 word512DualLegLo6T wOfU5Gam wOfU5GamF zKnotLo6 zKnotLo6_fastJ)
theorem nat_add_def (a b : Nat) : Nat.add a b = a + b := rfl
theorem nat_sub_def (a b : Nat) : Nat.sub a b = a - b := rfl
theorem nat_mul_def (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nat_div_def (a b : Nat) : Nat.div a b = a / b := rfl
theorem nat_mod_def (a b : Nat) : Nat.mod a b = a % b := rfl
theorem nat_pow_def (a b : Nat) : Nat.pow a b = a ^ b := rfl

@[inline] def fN63 {α : Type} (v : Nat) (k : Nat → α) : α := Nat.casesOn (Nat.add v 1) (k 0) k
theorem fN63_eq {α : Type} (v : Nat) (k : Nat → α) : fN63 v k = k v := rfl

@[inline] def sST63 {α : Type} (t : SumTree) (k : SumTree → α) : α :=
    SumTree.casesOn t (fun v => k (.leaf v)) (fun v l r => k (.node v l r))
theorem sST63_eq {α : Type} (t : SumTree) (k : SumTree → α) : sST63 t k = k t := by
  cases t <;> rfl

@[inline] def stVal63 (t : SumTree) : Nat := SumTree.casesOn t (fun v => v) (fun v _ _ => v)
theorem stVal63_eq (t : SumTree) : stVal63 t = stVal t := by
  cases t <;> rfl

@[inline] def sNT63 {α : Type} (t : NatTree) (k : NatTree → α) : α :=
    NatTree.casesOn t (fun v => k (.leaf v)) (fun l r => k (.node l r))
theorem sNT63_eq {α : Type} (t : NatTree) (k : NatTree → α) : sNT63 t k = k t := by
  cases t <;> rfl

@[inline] def andB63 (a b : Bool) : Bool := Bool.casesOn a false b

theorem andB63_eq_true (a b : Bool) : (andB63 a b = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

def buildNT63 (f : Nat → Nat) : Nat → Nat → Nat → NatTree
  | 0, i, _ => fN63 (f i) fun v => .leaf v
  | lvl + 1, base, half =>
      fN63 (Nat.div half 2) fun h2 =>
      sNT63 (buildNT63 f lvl base h2) fun l =>
      sNT63 (buildNT63 f lvl (Nat.add base half) h2) fun r =>
      .node l r

def getNT63 : Nat → NatTree → Nat → Nat
  | _, .leaf v, _ => v
  | h, .node l r, i =>
      Bool.casesOn (Nat.ble h i)
        (getNT63 (Nat.div h 2) l i)
        (getNT63 (Nat.div h 2) r (Nat.sub i h))

theorem getNT63_buildNT63 (f : Nat → Nat) :
    ∀ (lvl base idx : Nat), idx < 2 ^ lvl →
    getNT63 (2 ^ lvl / 2) (buildNT63 f lvl base (2 ^ lvl / 2)) idx = f (base + idx)
  | 0, base, idx, hidx => by
      obtain rfl : idx = 0 := by omega
      simp [buildNT63, fN63_eq, getNT63]
  | lvl + 1, base, idx, hidx => by
      rw [Nat.pow_succ] at hidx ⊢
      rw [Nat.mul_div_cancel _ (by decide)]
      unfold buildNT63
      simp only [fN63_eq, sNT63_eq, nat_div_def, nat_add_def]
      unfold getNT63
      cases hb : Nat.ble (2 ^ lvl) idx <;> simp only [nat_div_def, nat_sub_def]
      · exact getNT63_buildNT63 f lvl base idx
          (Nat.lt_of_not_le fun hge => Bool.noConfusion (hb.symm.trans (Nat.ble_eq.mpr hge)))
      · have hge := Nat.ble_eq.mp hb
        simpa [show base + 2 ^ lvl + (idx - 2 ^ lvl) = base + idx by omega] using
          getNT63_buildNT63 f lvl (base + 2 ^ lvl) (idx - 2 ^ lvl) (by omega)

@[inline] def getNT0F (t : NatTree) (i : Nat) : Nat :=
    NatTree.casesOn t (fun v => v) (fun l r => getNT63 0 (.node l r) i)
theorem getNT0F_eq (t : NatTree) (i : Nat) : getNT0F t i = getNT63 0 t i := by
  cases t <;> rfl

@[inline] def stepGetNT (nxt : NatTree → Nat → Nat) (h : Nat) (t : NatTree) (i : Nat) : Nat :=
    NatTree.casesOn t (fun v => v) fun l r =>
    Bool.casesOn (Nat.ble h i) (nxt l i) (nxt r (Nat.sub i h))
theorem stepGetNT_eq {nxt : NatTree → Nat → Nat} {h : Nat}
    (hnxt : ∀ t i, nxt t i = getNT63 (Nat.div h 2) t i) (t : NatTree)
    (i : Nat) : stepGetNT nxt h t i = getNT63 h t i := by
  cases t
  · rfl
  · unfold stepGetNT getNT63
    cases Nat.ble h i <;> dsimp only [Bool.casesOn] <;> exact hnxt _ _

def getNT1F : NatTree → Nat → Nat := stepGetNT getNT0F 1
def getNT2F : NatTree → Nat → Nat := stepGetNT getNT1F 2
def getNT4F : NatTree → Nat → Nat := stepGetNT getNT2F 4
def getNT8F : NatTree → Nat → Nat := stepGetNT getNT4F 8
def getNT16F : NatTree → Nat → Nat := stepGetNT getNT8F 16
def getNT32F : NatTree → Nat → Nat := stepGetNT getNT16F 32
def getNT64F : NatTree → Nat → Nat := stepGetNT getNT32F 64
def getNT128F : NatTree → Nat → Nat := stepGetNT getNT64F 128
def getNT256F : NatTree → Nat → Nat := stepGetNT getNT128F 256
def getNT512F : NatTree → Nat → Nat := stepGetNT getNT256F 512
def getNT1024F : NatTree → Nat → Nat := stepGetNT getNT512F 1024
theorem getNT256F_eq : ∀ t i, getNT256F t i = getNT63 256 t i :=
    stepGetNT_eq (stepGetNT_eq (stepGetNT_eq (stepGetNT_eq (stepGetNT_eq (stepGetNT_eq (stepGetNT_eq
    (stepGetNT_eq (stepGetNT_eq getNT0F_eq))))))))
theorem getNT1024F_eq : ∀ t i, getNT1024F t i = getNT63 1024 t i :=
    stepGetNT_eq (stepGetNT_eq getNT256F_eq)
@[inline] def xorBF (a b : Bool) : Bool := Bool.casesOn a b (Bool.casesOn b true false)

@[inline] def notBF (a : Bool) : Bool := Bool.casesOn a true false

@[inline] def sB63 {α : Type} (b : Bool) (k : Bool → α) : α := Bool.casesOn b (k false) (k true)
theorem sB63_eq {α : Type} (b : Bool) (k : Bool → α) : sB63 b k = k b := by
  cases b <;> rfl

@[inline] def checkNum63 (E m g hi lo s0Sq : Nat) : Bool := fN63 (Nat.mul g E) fun gE =>
    Bool.casesOn (Nat.ble lo gE) false (fN63 (Nat.add gE hi) fun u =>
    Bool.casesOn (Nat.ble s0Sq (Nat.mul (Nat.mul u u) m)) false (fN63 (Nat.sub gE lo) fun l =>
    Nat.ble (Nat.mul (Nat.mul l l) m) s0Sq))
def allCnt63 (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => Bool.casesOn (f i) false (fN63 (Nat.add i 1) fun i1 => allCnt63 f n i1)

theorem allCnt63_sound {f : Nat → Bool} :
    ∀ {n b : Nat}, allCnt63 f n b = true → ∀ off < n, f (b + off) = true
  | 0, _, _, _, hoff => by omega
  | n + 1, b, h, off, hoff => by
      unfold allCnt63 at h
      cases hf : f b <;> simp only [hf, fN63_eq, nat_add_def] at h
      · nomatch h
      · rcases off with _ | k
        · rwa [add_zero]
        · rw [show b + (k + 1) = b + 1 + k by omega]
          exact allCnt63_sound h k (by omega)

inductive ChSub63 : Type
  | ee : ChSub63
  | nn : ChSub63
  | en : ChSub63

def tail16List : List Nat :=
    [192534, 192536, 192538, 192542, 192550, 193041, 193043, 193045, 193051, 193548, 193550, 193554,
    194057, 194059, 194566, 195075]
def memNatList (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => Bool.casesOn (Nat.beq x y) (memNatList x ys) true

theorem memNatList_sound {x : Nat} : ∀ {xs : List Nat}, memNatList x xs = true → x ∈ xs
  | [], h => Bool.noConfusion h
  | y :: ys, h => by
      unfold memNatList at h
      cases hb : Nat.beq x y
      · rw [hb] at h; dsimp only [Bool.casesOn] at h
        exact List.mem_cons_of_mem y (memNatList_sound h)
      · exact List.mem_cons.mpr (.inl (Nat.beq_eq.mp hb))

def allList63 (f : Nat → Bool) : List Nat → Bool
  | [] => true
  | x :: xs => Bool.casesOn (f x) false (allList63 f xs)

theorem allList63_sound {f : Nat → Bool} :
    ∀ {xs : List Nat}, allList63 f xs = true → ∀ x ∈ xs, f x = true
  | [], _, _, hx => nomatch hx
  | y :: ys, h, x, hx => by
      unfold allList63 at h
      cases hfy : f y <;> simp only [hfy] at h
      · nomatch h
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact hfy
        · exact allList63_sound h x hmem

theorem openDistSq_ge_192512_mem_tail16 {d2 : ℕ} (h3d : Is3DBoxDistSq d2) (hge : 192512 ≤ d2)
    (hm7 : ¬(d2 % 8 = 7)) : d2 ∈ tail16List := by
  rcases h3d with ⟨a, b, c, ha, hb, hc, rfl⟩
  have h250 : 250 ≤ a ∧ 250 ≤ b ∧ 250 ≤ c := ⟨by nlinarith, by nlinarith, by nlinarith⟩
  have h0 : ∀ da db dc : Fin 6,
      let d2 := (250 + da.val) ^ 2 + (250 + db.val) ^ 2 + (250 + dc.val) ^ 2
      decide (192512 ≤ d2 → ¬(d2 % 8 = 7) → memNatList d2 tail16List = true) = true := by
    decide +kernel
  have hc1 := of_decide_eq_true (h0 ⟨a - 250, by omega⟩ ⟨b - 250, by omega⟩ ⟨c - 250, by omega⟩)
  dsimp only at hc1
  rw [show 250 + (a - 250) = a by omega, show 250 + (b - 250) = b by omega,
    show 250 + (c - 250) = c by omega] at hc1
  exact memNatList_sound (hc1 hge hm7)

def zeroST : Nat → SumTree
  | 0 => .leaf 0
  | d + 1 => sST63 (zeroST d) fun z => .node 0 z z

def insST : Nat → SumTree → Nat → Nat → SumTree
  | _, .leaf v, _, dw => fN63 (Nat.add v dw) fun v1 => .leaf v1
  | h, .node s l r, idx, dw =>
      fN63 (Nat.add s dw) fun s1 =>
      fN63 (Nat.div h 2) fun h2 =>
      Bool.casesOn (Nat.ble h idx)
        (sST63 (insST h2 l idx dw) fun l1 => .node s1 l1 r)
        (sST63 (insST h2 r (Nat.sub idx h) dw) fun r1 => .node s1 l r1)

def addST : SumTree → SumTree → SumTree
  | .leaf v1, .leaf v2 => fN63 (Nat.add v1 v2) fun v => .leaf v
  | .node s1 l1 r1, .node s2 l2 r2 =>
      fN63 (Nat.add s1 s2) fun s =>
      sST63 (addST l1 l2) fun l =>
      sST63 (addST r1 r2) fun r => .node s l r
  | t1, _ => t1

def sufST : Nat → SumTree → Nat → Nat → Nat
  | _, .leaf v, _, acc => Nat.add acc v
  | h, .node _ l r, M, acc =>
      Bool.casesOn (Nat.ble (Nat.add M 1) h)
        (sufST (Nat.div h 2) r (Nat.sub M h) acc)
        (sufST (Nat.div h 2) l M (Nat.add acc (stVal63 r)))

@[inline] def insST0F (t : SumTree) (idx dw : Nat) : SumTree :=
    SumTree.casesOn t (fun v => fN63 (Nat.add v dw) fun v1 => .leaf v1)
    (fun s l r => insST 0 (.node s l r) idx dw)
theorem insST0F_eq (t : SumTree) (idx dw : Nat) : insST0F t idx dw = insST 0 t idx dw := by
  cases t <;> rfl

@[inline] def stepInsST (nxt : SumTree → Nat → Nat → SumTree) (h : Nat) (t : SumTree)
    (idx dw : Nat) : SumTree :=
    SumTree.casesOn t (fun v => fN63 (Nat.add v dw) fun v1 => .leaf v1)
    (fun s l r => fN63 (Nat.add s dw) fun s1 => Bool.casesOn (Nat.ble h idx)
    (sST63 (nxt l idx dw) fun l1 => .node s1 l1 r) (sST63 (nxt r (Nat.sub idx h) dw) fun r1 =>
    .node s1 l r1))
theorem stepInsST_eq {nxt : SumTree → Nat → Nat → SumTree} {h : Nat}
    (hnxt : ∀ t idx dw, nxt t idx dw = insST (Nat.div h 2) t idx dw) (t : SumTree)
    (idx dw : Nat) : stepInsST nxt h t idx dw = insST h t idx dw := by
  cases t
  · rfl
  · unfold stepInsST insST; simp only [fN63_eq]
    cases Nat.ble h idx <;> dsimp only [Bool.casesOn] <;> rw [hnxt]

def insST1F : SumTree → Nat → Nat → SumTree := stepInsST insST0F 1
def insST2F : SumTree → Nat → Nat → SumTree := stepInsST insST1F 2
def insST4F : SumTree → Nat → Nat → SumTree := stepInsST insST2F 4
def insST8F : SumTree → Nat → Nat → SumTree := stepInsST insST4F 8
def insST16F : SumTree → Nat → Nat → SumTree := stepInsST insST8F 16
def insST32F : SumTree → Nat → Nat → SumTree := stepInsST insST16F 32
def insST64F : SumTree → Nat → Nat → SumTree := stepInsST insST32F 64

theorem insST64F_eq : ∀ t idx dw, insST64F t idx dw = insST 64 t idx dw :=
    stepInsST_eq (stepInsST_eq (stepInsST_eq (stepInsST_eq (stepInsST_eq (stepInsST_eq (stepInsST_eq
    insST0F_eq))))))
@[inline] def sufST0F (t : SumTree) (M acc : Nat) : Nat :=
    SumTree.casesOn t (fun v => Nat.add acc v) (fun s l r => sufST 0 (.node s l r) M acc)
theorem sufST0F_eq (t : SumTree) (M acc : Nat) : sufST0F t M acc = sufST 0 t M acc := by
  cases t <;> rfl

@[inline] def stepSufST (nxt : SumTree → Nat → Nat → Nat) (h : Nat) (t : SumTree)
    (M acc : Nat) : Nat :=
    SumTree.casesOn t (fun v => Nat.add acc v) (fun _ l r => Bool.casesOn (Nat.ble (Nat.add M 1) h)
    (nxt r (Nat.sub M h) acc) (nxt l M (Nat.add acc (stVal63 r))))
theorem stepSufST_eq {nxt : SumTree → Nat → Nat → Nat} {h : Nat}
    (hnxt : ∀ t M acc, nxt t M acc = sufST (Nat.div h 2) t M acc) (t : SumTree)
    (M acc : Nat) : stepSufST nxt h t M acc = sufST h t M acc := by
  cases t
  · rfl
  · unfold stepSufST sufST
    cases Nat.ble (Nat.add M 1) h <;> dsimp only [Bool.casesOn] <;> exact hnxt _ _ _

def sufST1F : SumTree → Nat → Nat → Nat := stepSufST sufST0F 1
def sufST2F : SumTree → Nat → Nat → Nat := stepSufST sufST1F 2
def sufST4F : SumTree → Nat → Nat → Nat := stepSufST sufST2F 4
def sufST8F : SumTree → Nat → Nat → Nat := stepSufST sufST4F 8
def sufST16F : SumTree → Nat → Nat → Nat := stepSufST sufST8F 16
def sufST32F : SumTree → Nat → Nat → Nat := stepSufST sufST16F 32
def sufST64F : SumTree → Nat → Nat → Nat := stepSufST sufST32F 64

theorem sufST64F_eq : ∀ t M acc, sufST64F t M acc = sufST 64 t M acc :=
    stepSufST_eq (stepSufST_eq (stepSufST_eq (stepSufST_eq (stepSufST_eq (stepSufST_eq (stepSufST_eq
    sufST0F_eq))))))
@[inline] def addST0F (t1 t2 : SumTree) : SumTree :=
    SumTree.casesOn t1 (fun v1 => SumTree.casesOn t2 (fun v2 => fN63 (Nat.add v1 v2) fun v =>
    .leaf v) (fun _ _ _ => .leaf v1)) (fun s1 l1 r1 => addST (.node s1 l1 r1) t2)
theorem addST0F_eq (t1 t2 : SumTree) : addST0F t1 t2 = addST t1 t2 := by
  cases t1 <;> cases t2 <;> rfl

@[inline] def stepAddST (nxt : SumTree → SumTree → SumTree) (t1 t2 : SumTree) : SumTree :=
    SumTree.casesOn t1 (fun v1 => SumTree.casesOn t2 (fun v2 => fN63 (Nat.add v1 v2) fun v =>
    .leaf v) (fun _ _ _ => .leaf v1)) (fun s1 l1 r1 => SumTree.casesOn t2 (fun _ => .node s1 l1 r1)
    (fun s2 l2 r2 => fN63 (Nat.add s1 s2) fun s => sST63 (nxt l1 l2) fun l =>
    sST63 (nxt r1 r2) fun r => .node s l r))
theorem stepAddST_eq {nxt : SumTree → SumTree → SumTree} (hnxt : ∀ t1 t2, nxt t1 t2 = addST t1 t2)
    (t1 t2 : SumTree) : stepAddST nxt t1 t2 = addST t1 t2 := by
  cases t1 <;> cases t2
  · rfl
  · rfl
  · rfl
  · unfold stepAddST addST; simp only [fN63_eq, sST63_eq, hnxt]

def addST1F : SumTree → SumTree → SumTree := stepAddST addST0F
def addST2F : SumTree → SumTree → SumTree := stepAddST addST1F
def addST3F : SumTree → SumTree → SumTree := stepAddST addST2F
def addST4F : SumTree → SumTree → SumTree := stepAddST addST3F
def addST5F : SumTree → SumTree → SumTree := stepAddST addST4F
def addST6F : SumTree → SumTree → SumTree := stepAddST addST5F
def addST7F : SumTree → SumTree → SumTree := stepAddST addST6F

theorem addST7F_eq : ∀ t1 t2, addST7F t1 t2 = addST t1 t2 :=
    stepAddST_eq (stepAddST_eq (stepAddST_eq (stepAddST_eq (stepAddST_eq (stepAddST_eq (stepAddST_eq
    addST0F_eq))))))
inductive ST4 : Type
  | mk : Nat → SumTree → SumTree → SumTree → SumTree → ST4

@[inline] def sST4 {α : Type} (p : ST4) (k : ST4 → α) : α := ST4.casesOn p fun s a b c d =>
    fN63 s fun s => sST63 a fun a => sST63 b fun b => sST63 c fun c => sST63 d fun d =>
    k (.mk s a b c d)
theorem sST4_eq {α : Type} (p : ST4) (k : ST4 → α) : sST4 p k = k p := by
  cases p; simp only [sST4, fN63_eq, sST63_eq]

def mkST4F (a b c d : SumTree) : ST4 := sST63 a fun a => sST63 b fun b => sST63 c fun c =>
    sST63 d fun d =>
    fN63 (Nat.add (Nat.add (stVal63 a) (stVal63 b)) (Nat.add (stVal63 c) (stVal63 d))) fun s =>
    .mk s a b c d
theorem wOfU5GamF_eq_spec : ∀ (u5 : Fin 32) (g6 : Fin 64), wOfU5GamF u5.val g6.val =
    wOfU5Gam u5.val g6.val := by decide +kernel
theorem b2n_testBit_eq_div_mod (n i : ℕ) : (if n.testBit i then 1 else 0) = (n / 2 ^ i) % 2 := by
  unfold Nat.testBit; rw [Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod]
  rcases (show (n / 2 ^ i) % 2 = 0 ∨ (n / 2 ^ i) % 2 = 1 by omega) with h | h <;>
    rw [h] <;> rfl

theorem b2n_ite_xor (m p b : Bool) : (if (if m then xor p b else p) then 1 else 0) =
    ((if p then 1 else 0) + (if (m && b) then 1 else 0)) % 2 := by
  cases m <;> cases p <;> cases b <;> rfl

@[inline] def r01OfR6 (r6 : Nat) : Bool := Nat.beq (Nat.mod (Nat.add (Nat.div r6 2) r6) 2) 1
@[inline] def j18Sum3 (aTop2 p0 p1 p2 : Nat) (c0 c1 c2 : Bool) : Nat :=
    fN63 (Nat.add aTop2 (Bool.casesOn c0 0 1)) fun thr0 =>
    fN63 (Nat.add aTop2 (Bool.casesOn c1 0 1)) fun thr1 =>
    fN63 (Nat.add aTop2 (Bool.casesOn c2 0 1)) fun thr2 =>
    Nat.add (Nat.add (Bool.casesOn (Nat.ble (Nat.add p0 1) thr0) 0 1)
    (Bool.casesOn (Nat.ble (Nat.add p1 1) thr1) 0 1))
    (Bool.casesOn (Nat.ble (Nat.add p2 1) thr2) 0 1)
theorem j18Sum3_lt_four (aTop2 p0 p1 p2 : Nat) (c0 c1 c2 : Bool) : j18Sum3 aTop2 p0 p1 p2 c0 c1 c2 <
    4 := by
  unfold j18Sum3; simp only [fN63_eq]
  cases Nat.ble _ _ <;> cases Nat.ble _ _ <;> cases Nat.ble _ _ <;> decide

theorem j18Sum3_eq (aTop2 p0 p1 p2 : Nat) (c0 c1 c2 : Bool) : j18Sum3 aTop2 p0 p1 p2 c0 c1 c2 =
    (if p0 < aTop2 + (if c0 then 1 else 0) then 1 else 0) + (if p1 < aTop2 +
    (if c1 then 1 else 0) then 1 else 0) + (if p2 < aTop2 + (if c2 then 1 else 0) then 1 else 0)
    := by
  have hbRec : ∀ x y : Nat, Bool.rec 0 1 (Nat.ble (x + 1) y) = if x < y then 1 else 0 := fun x y =>
      by
    by_cases hxy : x < y
    · rw [ite_eq_left hxy, show Nat.ble (x + 1) y = true from Nat.ble_eq.mpr hxy]
    · rw [ite_eq_right hxy, show Nat.ble (x + 1) y = false from
        Bool.eq_false_iff.mpr fun hb => hxy (Nat.ble_eq.mp hb)]
  have hBoolRec : ∀ b : Bool, Bool.rec 0 1 b = if b then 1 else 0 := fun b => by cases b <;> rfl
  unfold j18Sum3; simp only [fN63_eq, nat_add_def];
  rw [hbRec, hbRec, hbRec, hBoolRec, hBoolRec, hBoolRec]
@[inline] def j18CarryEval (aTop2 p0 p1 p2 : Nat) (r01 b6 g0 g1 z4 z2 z3 t6 t7 t8 : Bool) : Nat :=
    sB63 (andB63 (xorBF true (xorBF r01 g1)) g0) fun q01 => sB63 (xorBF t6 b6) fun tb6 =>
    sB63 (xorBF q01 tb6) fun qEff => sB63 (xorBF z2 qEff) fun za => sB63 (xorBF z3 za) fun wC1 =>
    sB63 (xorBF (andB63 (xorBF (notBF z4) b6) tb6) b6) fun e0 =>
    sB63 (xorBF (andB63 (xorBF (notBF za) t7) (xorBF t8 t7)) t7) fun c0 =>
    sB63 (xorBF (andB63 wC1 (xorBF t8 e0)) e0) fun c1 =>
    sB63 (xorBF (andB63 (xorBF (notBF z2) e0) (xorBF t7 e0)) e0) fun d2b =>
    sB63 (xorBF (andB63 (xorBF (notBF z3) d2b) (xorBF t8 d2b)) d2b) fun c2 =>
    j18Sum3 aTop2 p0 p1 p2 c0 c1 c2
def j18AtARB (a : Nat) (r01 b6 : Bool) (d11 : Nat) : Nat := fN63 (Nat.div d11 64) fun zp =>
    fN63 (Nat.mod zp 4) fun p0 => fN63 (Nat.mod (Nat.div zp 4) 4) fun p1 =>
    fN63 (Nat.add (Nat.mod (Nat.div d11 32) 2) (Nat.mul 2 (Nat.mod (Nat.div zp 16) 2))) fun p2 =>
    fN63 (Nat.mod (Nat.div a 8) 4) fun aTop2 => sB63 (Nat.beq (Nat.mod d11 2) 1) fun g0 =>
    sB63 (Nat.beq (Nat.mod (Nat.div d11 2) 2) 1) fun g1 =>
    sB63 (Nat.beq (Nat.mod (Nat.div d11 4) 2) 1) fun z4 =>
    sB63 (Nat.beq (Nat.mod (Nat.div d11 8) 2) 1) fun z2 =>
    sB63 (Nat.beq (Nat.mod (Nat.div d11 16) 2) 1) fun z3 => sB63 (Nat.beq (Nat.mod a 2) 1) fun t6 =>
    sB63 (Nat.beq (Nat.mod (Nat.div a 2) 2) 1) fun t7 =>
    sB63 (Nat.beq (Nat.mod (Nat.div a 4) 2) 1) fun t8 =>
    j18CarryEval aTop2 p0 p1 p2 r01 b6 g0 g1 z4 z2 z3 t6 t7 t8
theorem j18AtARB_lt_four (a : Nat) (r01 b6 : Bool) (d11 : Nat) : j18AtARB a r01 b6 d11 < 4 := by
  unfold j18AtARB j18CarryEval; simp only [fN63_eq, sB63_eq]; exact j18Sum3_lt_four _ _ _ _ _ _ _
def jPack4Leaf (a d11 : Nat) : Nat := fN63 (j18AtARB a false false d11) fun j00 =>
    fN63 (j18AtARB a true false d11) fun j10 => fN63 (j18AtARB a false true d11) fun j01 =>
    fN63 (j18AtARB a true true d11) fun j11 =>
    Nat.add j00 (Nat.mul 4 (Nat.add j10 (Nat.mul 4 (Nat.add j01 (Nat.mul 4 j11)))))
theorem jPack4Leaf_unpack (a d11 : Nat) :
    let jp := jPack4Leaf a d11
    jp % 4 = j18AtARB a false false d11 ∧
    (jp / 4) % 4 = j18AtARB a true false d11 ∧
    (jp / 16) % 4 = j18AtARB a false true d11 ∧
    jp / 64 = j18AtARB a true true d11 := by
  have h00 := j18AtARB_lt_four a false false d11; have h10 := j18AtARB_lt_four a true false d11;
  have h01 := j18AtARB_lt_four a false true d11;
  have h11 :=
      j18AtARB_lt_four a true true d11; unfold jPack4Leaf; simp only [fN63_eq, nat_add_def,
      nat_mul_def]; omega
@[inline] def sParts {α : Type} (p : Nat × Nat × Nat) (k : Nat → Nat → Nat → α) : α :=
    Prod.casesOn p fun p1 rest => Prod.casesOn rest fun t10 kk => fN63 p1 fun p1 =>
    fN63 t10 fun t10 => fN63 kk fun kk => k p1 t10 kk
theorem sParts_eq {α : Type} (p : Nat × Nat × Nat) (k : Nat → Nat → Nat → α) : sParts p k =
    k p.1 p.2.1 p.2.2 := by
  rcases p with ⟨p1, t10, kk⟩; simp [sParts, fN63_eq]

inductive IsValidST : Nat → SumTree → Prop
  | leaf (v : Nat) : IsValidST 0 (.leaf v)
  | node {d s : Nat} {l r : SumTree} :
      s = stVal l + stVal r → IsValidST d l → IsValidST d r → IsValidST (d + 1) (.node s l r)

def sumAllST : SumTree → Nat
  | .leaf v => v
  | .node _ l r => sumAllST l + sumAllST r

def sumSufST : Nat → Nat → SumTree → Nat → Nat
  | _, base, .leaf v, M => if M ≤ base then v else 0
  | h, base, .node _ l r, M =>
      sumSufST (h / 2) base l M + sumSufST (h / 2) (base + h) r M

theorem stVal_eq_sumAllST {d : Nat} {st : SumTree} (h : IsValidST d st) : stVal st =
    sumAllST st := by
  induction h with
  | leaf _ => rfl
  | node hs _ _ ihl ihr => dsimp only [stVal, sumAllST]; omega

theorem sumSufST_all {d : Nat} {st : SumTree} (hv : IsValidST d st) : ∀ {base K : Nat}, K ≤ base →
    sumSufST (2 ^ d / 2) base st K = sumAllST st := by
  induction hv with
  | leaf v => intro base K hK; simp [sumSufST, sumAllST, hK]
  | @node d _ _ _ _ _ _ ihl ihr =>
      intro base K hK
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
      dsimp only [sumSufST, sumAllST]
      rw [ihl hK, ihr (Nat.le_trans hK (Nat.le_add_right _ _))]

theorem sumSufST_none {d : Nat} {st : SumTree} (hv : IsValidST d st) : ∀ {base K : Nat}, base +
    2 ^ d ≤ K → sumSufST (2 ^ d / 2) base st K = 0 := by
  induction hv with
  | leaf v => exact fun {base K} _ => by simp [sumSufST, show ¬(K ≤ base) by omega]
  | @node d _ _ _ _ _ _ ihl ihr =>
      intro base K hK
      rw [Nat.pow_succ] at hK ⊢
      rw [Nat.mul_div_cancel _ (by decide)]
      dsimp only [sumSufST]
      rw [ihl (base := base) (K := K) (by omega), ihr (base := base + 2 ^ d) (K := K) (by omega)]

theorem sufST_eq_sumSufST {d : Nat} {st : SumTree} (hv : IsValidST d st) : ∀ (base M acc : Nat), M <
    2 ^ d → sufST (2 ^ d / 2) st M acc = acc + sumSufST (2 ^ d / 2) base st (base + M) := by
  induction hv with
  | leaf v =>
      intro base M acc hM
      obtain rfl : M = 0 := by omega
      simp [sufST, sumSufST]
  | @node d s l r hs hl hr ihl ihr =>
      intro base M acc hM
      rw [Nat.pow_succ] at hM ⊢
      rw [Nat.mul_div_cancel _ (by decide)]
      unfold sufST
      cases hb : Nat.ble (M + 1) (2 ^ d) <;>
        simp only [nat_add_def, nat_div_def, nat_sub_def, stVal63_eq]
      · have hge := Nat.le_of_not_lt fun hlt =>
          Bool.noConfusion (hb.symm.trans (Nat.ble_eq.mpr hlt))
        rw [ihr (base + 2 ^ d) (M - 2 ^ d) acc (by omega),
          show base + 2 ^ d + (M - 2 ^ d) = base + M by omega]
        dsimp only [sumSufST]
        have hn := sumSufST_none hl (base := base) (K := base + M) (by omega)
        omega
      · have hlt : M < 2 ^ d := Nat.ble_eq.mp hb
        rw [ihl base M (acc + stVal r) hlt, stVal_eq_sumAllST hr]
        dsimp only [sumSufST]
        have ha := sumSufST_all hr (base := base + 2 ^ d) (K := base + M) (by omega)
        omega

def IsValidST4 : ST4 → Prop
  | .mk _ a b c d => IsValidST 7 a ∧ IsValidST 7 b ∧ IsValidST 7 c ∧ IsValidST 7 d

theorem checkNum63_sound {E m g hi lo s0Sq : Nat} (h : checkNum63 E m g hi lo s0Sq = true) : lo ≤
    g * E ∧ s0Sq ≤ (g * E + hi) * (g * E + hi) * m ∧ (g * E - lo) * (g * E - lo) * m ≤ s0Sq := by
  unfold checkNum63 at h
  simp only [fN63_eq, nat_mul_def, nat_add_def, nat_sub_def] at h
  cases h1 : Nat.ble lo (g * E) <;>
    cases h2 : Nat.ble s0Sq ((g * E + hi) * (g * E + hi) * m) <;>
    simp_all [Nat.ble_eq]
/-! ### Part 4C: 62-Bit Packed `ST4` Fused 3-Channel Kernel ULP Certificates (`decide +kernel`) -/
def beqNT : NatTree → NatTree → Bool
  | .leaf v1, .leaf v2 => Nat.beq v1 v2
  | .node l1 r1, .node l2 r2 => Bool.casesOn (beqNT l1 l2) false (beqNT r1 r2)
  | _, _ => false

theorem beqNT_eq : ∀ {t1 t2 : NatTree}, beqNT t1 t2 = true → t1 = t2
  | .leaf v1, .leaf v2, h => congrArg NatTree.leaf (Nat.eq_of_beq_eq_true h)
  | .leaf _, .node _ _, h => Bool.noConfusion h
  | .node _ _, .leaf _, h => Bool.noConfusion h
  | .node l1 r1, .node l2 r2, h => by
      dsimp only [beqNT] at h
      cases h1 : beqNT l1 l2
      · rw [h1] at h; exact Bool.noConfusion h
      · rw [h1] at h; dsimp only [Bool.casesOn] at h
        rw [beqNT_eq h1, beqNT_eq h]

@[inline] def bNT0 (f : Nat → Nat) (i _ : Nat) : NatTree := fN63 (f i) fun v => .leaf v
@[inline] def stepBNT (nxt : (Nat → Nat) → Nat → Nat → NatTree) (f : Nat → Nat)
    (base half : Nat) : NatTree := fN63 (Nat.div half 2) fun h2 => sNT63 (nxt f base h2) fun l =>
    sNT63 (nxt f (Nat.add base half) h2) fun r => .node l r
def bNT1 := stepBNT bNT0
def bNT2 := stepBNT bNT1
def bNT3 := stepBNT bNT2
def bNT4 := stepBNT bNT3
def bNT5 := stepBNT bNT4
def bNT6 := stepBNT bNT5
def bNT7 := stepBNT bNT6
def bNT8 := stepBNT bNT7
def bNT9 := stepBNT bNT8
def bNT10 := stepBNT bNT9
def bNT11 := stepBNT bNT10
def bNT12 := stepBNT bNT11
def bNT13 := stepBNT bNT12

@[inline] def bitAtF (x p2 : Nat) : Nat := Nat.mod (Nat.div x p2) 2

def zeroST0F : SumTree := .leaf 0
def stepZeroST (z : SumTree) : SumTree := sST63 z fun z => .node 0 z z
def zeroST7F : SumTree :=
    stepZeroST (stepZeroST (stepZeroST (stepZeroST (stepZeroST (stepZeroST (stepZeroST
    zeroST0F))))))
@[inline] def subST0F (t : SumTree) (_ dw : Nat) : SumTree :=
    SumTree.casesOn t (fun v => fN63 (Nat.sub v dw) fun v1 => .leaf v1) (fun s l r => .node s l r)
@[inline] def stepSubST (nxt : SumTree → Nat → Nat → SumTree) (h : Nat) (t : SumTree)
    (idx dw : Nat) : SumTree :=
    SumTree.casesOn t (fun v => fN63 (Nat.sub v dw) fun v1 => .leaf v1)
    (fun s l r => fN63 (Nat.sub s dw) fun s1 => Bool.casesOn (Nat.ble h idx)
    (sST63 (nxt l idx dw) fun l1 => .node s1 l1 r) (sST63 (nxt r (Nat.sub idx h) dw) fun r1 =>
    .node s1 l r1))
def subST1F := stepSubST subST0F 1
def subST2F := stepSubST subST1F 2
def subST4F := stepSubST subST2F 4
def subST8F := stepSubST subST4F 8
def subST16F := stepSubST subST8F 16
def subST32F := stepSubST subST16F 32
def subST64F := stepSubST subST32F 64

inductive ST4P2 : Type
  | mk : ST4 → ST4 → ST4P2

@[inline] def sST4P2 {α : Type} (p : ST4P2) (k : ST4P2 → α) : α := ST4P2.casesOn p fun s0 s1 =>
    sST4 s0 fun s0 => sST4 s1 fun s1 => k (.mk s0 s1)
@[inline] def selST4P2 (r01 : Bool) (p : ST4P2) : ST4 := ST4P2.casesOn p fun s0 s1 =>
    Bool.casesOn r01 s0 s1
inductive ST4T3 : Type
  | mk : ST4 → ST4 → ST4 → ST4T3

@[inline] def sST4T3 {α : Type} (t : ST4T3) (k : ST4T3 → α) : α := ST4T3.casesOn t fun sc s0 s1 =>
    sST4 sc fun sc => sST4 s0 fun s0 => sST4 s1 fun s1 => k (.mk sc s0 s1)
@[inline] def packThr3 (aTop2 : Nat) (c0 c1 c2 : Bool) : Nat :=
    fN63 (Nat.add aTop2 (Bool.casesOn c0 0 1)) fun thr0 =>
    fN63 (Nat.add aTop2 (Bool.casesOn c1 0 1)) fun thr1 =>
    fN63 (Nat.add aTop2 (Bool.casesOn c2 0 1)) fun thr2 =>
    Nat.add thr0 (Nat.mul 8 (Nat.add thr1 (Nat.mul 8 thr2)))
def thr9OfARB (a : Nat) (r01 b6 : Bool) (lo5 : Nat) : Nat :=
    fN63 (Nat.mod (Nat.div a 8) 4) fun aTop2 => sB63 (Nat.beq (Nat.mod lo5 2) 1) fun g0 =>
    sB63 (Nat.beq (Nat.mod (Nat.div lo5 2) 2) 1) fun g1 =>
    sB63 (Nat.beq (Nat.mod (Nat.div lo5 4) 2) 1) fun z4 =>
    sB63 (Nat.beq (Nat.mod (Nat.div lo5 8) 2) 1) fun z2 =>
    sB63 (Nat.beq (Nat.mod (Nat.div lo5 16) 2) 1) fun z3 => sB63 (Nat.beq (Nat.mod a 2) 1) fun t6 =>
    sB63 (Nat.beq (Nat.mod (Nat.div a 2) 2) 1) fun t7 =>
    sB63 (Nat.beq (Nat.mod (Nat.div a 4) 2) 1) fun t8 =>
    sB63 (andB63 (xorBF true (xorBF r01 g1)) g0) fun q01 => sB63 (xorBF t6 b6) fun tb6 =>
    sB63 (xorBF q01 tb6) fun qEff => sB63 (xorBF z2 qEff) fun za => sB63 (xorBF z3 za) fun wC1 =>
    sB63 (xorBF (andB63 (xorBF (notBF z4) b6) tb6) b6) fun e0 =>
    sB63 (xorBF (andB63 (xorBF (notBF za) t7) (xorBF t8 t7)) t7) fun c0 =>
    sB63 (xorBF (andB63 wC1 (xorBF t8 e0)) e0) fun c1 =>
    sB63 (xorBF (andB63 (xorBF (notBF z2) e0) (xorBF t7 e0)) e0) fun d2b =>
    sB63 (xorBF (andB63 (xorBF (notBF z3) d2b) (xorBF t8 d2b)) d2b) fun c2 =>
    packThr3 aTop2 c0 c1 c2
def thr36PackLeaf (a00 : Nat) (r00 b00 : Bool) (a10 : Nat) (r10 b10 : Bool) (a01 : Nat)
    (r01 b01 : Bool) (a11 : Nat) (r11 b11 : Bool) (lo5 : Nat) : Nat :=
    fN63 (thr9OfARB a00 r00 b00 lo5) fun t00 => fN63 (thr9OfARB a10 r10 b10 lo5) fun t10 =>
    fN63 (thr9OfARB a01 r01 b01 lo5) fun t01 => fN63 (thr9OfARB a11 r11 b11 lo5) fun t11 =>
    Nat.add t00 (Nat.mul 512 (Nat.add t10 (Nat.mul 512 (Nat.add t01 (Nat.mul 512 t11)))))
@[inline] def evalThr9 (p01 p11 p21 t9 : Nat) : Nat :=
    Nat.add (Nat.add (Bool.casesOn (Nat.ble p01 (Nat.mod t9 8)) 0 1)
    (Bool.casesOn (Nat.ble p11 (Nat.mod (Nat.div t9 8) 8)) 0 1))
    (Bool.casesOn (Nat.ble p21 (Nat.div t9 64)) 0 1)
def j4FromThrNT5 (thrNT5 : NatTree) (d11 : Nat) : Nat :=
    fN63 (getNT16F thrNT5 (Nat.mod d11 32)) fun t36 => fN63 (Nat.div d11 64) fun zp =>
    fN63 (Nat.add (Nat.mod zp 4) 1) fun p01 =>
    fN63 (Nat.add (Nat.mod (Nat.div zp 4) 4) 1) fun p11 =>
    fN63 (Nat.add (Nat.add (Nat.mod (Nat.div d11 32) 2)
    (Nat.mul 2 (Nat.mod (Nat.div zp 16) 2))) 1) fun p21 =>
    fN63 (evalThr9 p01 p11 p21 (Nat.mod t36 512)) fun j00 => fN63 (Nat.div t36 512) fun q1 =>
    fN63 (evalThr9 p01 p11 p21 (Nat.mod q1 512)) fun j10 => fN63 (Nat.div q1 512) fun q2 =>
    fN63 (evalThr9 p01 p11 p21 (Nat.mod q2 512)) fun j01 =>
    fN63 (evalThr9 p01 p11 p21 (Nat.div q2 512)) fun j11 =>
    Nat.add j00 (Nat.mul 4 (Nat.add j10 (Nat.mul 4 (Nat.add j01 (Nat.mul 4 j11)))))
def buildJPackNT (a : Nat) : NatTree :=
    sNT63 (bNT5 (thr36PackLeaf a false false a true false a false true a true true) 0 16) fun thrNT5
    => bNT11 (j4FromThrNT5 thrNT5) 0 1024
inductive ZLeafL : Type
  | nil : ZLeafL
  | cons : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → ZLeafL → ZLeafL

@[inline] def sZLL {α : Type} (l : ZLeafL) (k : ZLeafL → α) : α :=
    ZLeafL.casesOn l (k .nil) fun m0 q0 M0 q1 M1 q2 M2 q3 M3 tl => fN63 m0 fun m0 =>
    fN63 q0 fun q0 => fN63 M0 fun M0 => fN63 q1 fun q1 => fN63 M1 fun M1 => fN63 q2 fun q2 =>
    fN63 M2 fun M2 => fN63 q3 fun q3 => fN63 M3 fun M3 => k (.cons m0 q0 M0 q1 M1 q2 M2 q3 M3 tl)
inductive ZOct10L : Type
  | mk : ZLeafL → ZLeafL → ZLeafL → ZLeafL → ZLeafL →
         ZLeafL → ZLeafL → ZLeafL → ZLeafL → ZLeafL → ZOct10L

def checkSmCoordsB (isNN : Bool) : Bool :=
    andB63 (allCnt63 (fun d2 => sParts (evenOctPartsW11 isNN d2) fun p1 t10 _ =>
    Nat.beq (Nat.mod (Nat.add (Nat.mul (Nat.mod p1 2) 1024) t10) 1024) 0) 256 0)
    (allList63 (fun d2 => sParts (evenOctPartsW11 isNN d2) fun p1 t10 _ =>
    fN63 (Nat.add (Nat.mul (Nat.mod p1 2) 1024) t10) fun t11 =>
    andB63 (Nat.beq (Nat.mod (Nat.div t11 64) 8) 0) (Nat.beq (Nat.mod t11 64)
    (Nat.mod d2 64))) tail16List)
inductive ChCtx3 : Type
  | mk : ChW11 → ZOct10L → Nat → Nat → Nat → Nat → ChCtx3

inductive ST4P2B : Type
  | mk : Bool → ST4P2 → ST4P2B

@[inline] def sST4P2B {α : Type} (x : ST4P2B) (k : Bool → ST4P2 → α) : α :=
    ST4P2B.casesOn x fun ok st => Bool.casesOn ok (k false st) (sST4P2 st fun st => k true st)
set_option Elab.async true
theorem tSmCoords : andB63 (checkSmCoordsB false) (checkSmCoordsB true) = true := by decide +kernel
/-! ### Part 4D: Soundness of 62-Bit Packed `ST4` Sweep and Closed `BlockApproxSpecGen` -/
theorem bNT0_eq (f : Nat → Nat) (base half : Nat) :
    bNT0 f base half = buildNT63 f 0 base half := rfl

theorem stepBNT_eq {d : Nat} {nxt : (Nat → Nat) → Nat → Nat → NatTree}
    (hnxt : ∀ f base half, nxt f base half = buildNT63 f d base half) (f : Nat → Nat)
    (base half : Nat) : stepBNT nxt f base half = buildNT63 f (d + 1) base half := by
  unfold stepBNT buildNT63; simp only [fN63_eq, sNT63_eq, hnxt]
theorem bNT9_eq : ∀ f base half, bNT9 f base half = buildNT63 f 9 base half :=
    stepBNT_eq (stepBNT_eq (stepBNT_eq (stepBNT_eq (stepBNT_eq (stepBNT_eq (stepBNT_eq (stepBNT_eq
    (stepBNT_eq bNT0_eq))))))))
theorem bNT11_eq : ∀ f base half, bNT11 f base half = buildNT63 f 11 base half :=
    stepBNT_eq (stepBNT_eq bNT9_eq)
theorem bNT12_eq : ∀ f base half, bNT12 f base half = buildNT63 f 12 base half :=
    stepBNT_eq bNT11_eq
theorem bNT13_eq : ∀ f base half, bNT13 f base half = buildNT63 f 13 base half :=
    stepBNT_eq bNT12_eq
theorem buildNT63_zero (f : Nat → Nat) (base half : Nat) : buildNT63 f 0 base half = .leaf (f base)
    := by unfold buildNT63; rw [fN63_eq]
theorem buildNT63_succ (f : Nat → Nat) (d base half : Nat) : buildNT63 f (d + 1) base half =
    .node (buildNT63 f d base (half / 2)) (buildNT63 f d (base + half) (half / 2)) := by
  conv_lhs => unfold buildNT63
  simp only [fN63_eq, sNT63_eq, nat_div_def, nat_add_def]

theorem sST4P2_eq {α : Type} (p : ST4P2) (k : ST4P2 → α) : sST4P2 p k = k p := by
  cases p; simp only [sST4P2, sST4_eq]

theorem sST4P2B_eq {α : Type} (x : ST4P2B) (k : Bool → ST4P2 → α) :
    sST4P2B x k = match x with | .mk ok st => k ok st := by
  rcases x with ⟨ok, st⟩; cases ok <;> simp [sST4P2B, sST4P2_eq]

theorem sST4T3_eq {α : Type} (t : ST4T3) (k : ST4T3 → α) : sST4T3 t k = k t := by
  cases t; simp only [sST4T3, sST4_eq]

theorem bNT5_eq : ∀ f base half, bNT5 f base half = buildNT63 f 5 base half :=
    stepBNT_eq (stepBNT_eq (stepBNT_eq (stepBNT_eq (stepBNT_eq bNT0_eq))))
theorem getNT16F_eq : ∀ t i, getNT16F t i = getNT63 16 t i :=
    stepGetNT_eq (stepGetNT_eq (stepGetNT_eq (stepGetNT_eq (stepGetNT_eq getNT0F_eq))))
theorem packThr3_unpack {aTop2 : Nat} (ha : aTop2 < 4) (c0 c1 c2 : Bool) :
    let t9 := packThr3 aTop2 c0 c1 c2
    t9 < 512 ∧
    t9 % 8 = aTop2 + Bool.casesOn c0 0 1 ∧
    (t9 / 8) % 8 = aTop2 + Bool.casesOn c1 0 1 ∧
    t9 / 64 = aTop2 + Bool.casesOn c2 0 1 := by
  rcases (by omega : aTop2 = 0 ∨ aTop2 = 1 ∨ aTop2 = 2 ∨ aTop2 = 3) with rfl | rfl | rfl | rfl <;>
    cases c0 <;> cases c1 <;> cases c2 <;> decide

theorem evalThr9_packThr3 {aTop2 : Nat} (ha : aTop2 < 4) (p0 p1 p2 : Nat)
    (c0 c1 c2 : Bool) : evalThr9 (p0 + 1) (p1 + 1) (p2 + 1) (packThr3 aTop2 c0 c1 c2) =
    j18Sum3 aTop2 p0 p1 p2 c0 c1 c2 := by
  obtain ⟨_, u0, u1, u2⟩ :=
      packThr3_unpack ha c0 c1 c2; unfold evalThr9 j18Sum3; simp only [fN63_eq, nat_mod_def,
      nat_div_def, nat_add_def]; rw [u0, u1, u2]
theorem thr9OfARB_lt_512 (a : Nat) (r01 b6 : Bool) (lo5 : Nat) : thr9OfARB a r01 b6 lo5 < 512 := by
  unfold thr9OfARB; simp only [fN63_eq, sB63_eq, nat_mod_def, nat_div_def]
  exact (packThr3_unpack (Nat.mod_lt _ (by omega)) _ _ _).1

theorem evalThr9_thr9OfARB (a d11 : Nat) (r01 b6 : Bool) :
    let zp := d11 / 64
    let p0 := zp % 4
    let p1 := (zp / 4) % 4
    let p2 := (d11 / 32) % 2 + 2 * ((zp / 16) % 2)
    evalThr9 (p0 + 1) (p1 + 1) (p2 + 1) (thr9OfARB a r01 b6 (d11 % 32)) =
      j18AtARB a r01 b6 d11 := by
  dsimp only; unfold thr9OfARB j18AtARB j18CarryEval;
  simp only [fN63_eq, sB63_eq, nat_mod_def, nat_div_def, nat_add_def, nat_mul_def]
  have h0 : (d11 % 32) % 2 = d11 % 2 := by omega
  have h1 : ((d11 % 32) / 2) % 2 = (d11 / 2) % 2 := by omega
  have h2 : ((d11 % 32) / 4) % 2 = (d11 / 4) % 2 := by omega
  have h3 : ((d11 % 32) / 8) % 2 = (d11 / 8) % 2 := by omega
  have h4 : ((d11 % 32) / 16) % 2 = (d11 / 16) % 2 := by omega
  rw [h0, h1, h2, h3, h4]
  exact evalThr9_packThr3 (Nat.mod_lt _ (by omega)) _ _ _ _ _ _

theorem thr36PackLeaf_unpack
    (a00 : Nat) (r00 b00 : Bool) (a10 : Nat) (r10 b10 : Bool)
    (a01 : Nat) (r01 b01 : Bool) (a11 : Nat) (r11 b11 : Bool) (lo5 : Nat) :
    let t36 := thr36PackLeaf a00 r00 b00 a10 r10 b10 a01 r01 b01 a11 r11 b11 lo5
    t36 % 512 = thr9OfARB a00 r00 b00 lo5 ∧
    (t36 / 512) % 512 = thr9OfARB a10 r10 b10 lo5 ∧
    ((t36 / 512) / 512) % 512 = thr9OfARB a01 r01 b01 lo5 ∧
    ((t36 / 512) / 512) / 512 = thr9OfARB a11 r11 b11 lo5 := by
  dsimp only; have h00 := thr9OfARB_lt_512 a00 r00 b00 lo5;
  have h10 := thr9OfARB_lt_512 a10 r10 b10 lo5; have h01 := thr9OfARB_lt_512 a01 r01 b01 lo5;
  have h11 :=
      thr9OfARB_lt_512 a11 r11 b11 lo5; unfold thr36PackLeaf; simp only [fN63_eq, nat_add_def,
      nat_mul_def]; omega
theorem j4FromThrNT5_eq (a00 : Nat) (r00 b00 : Bool) (a10 : Nat) (r10 b10 : Bool) (a01 : Nat)
    (r01 b01 : Bool) (a11 : Nat) (r11 b11 : Bool)
    (d11 : Nat) :
    j4FromThrNT5 (bNT5 (thr36PackLeaf a00 r00 b00 a10 r10 b10 a01 r01 b01 a11 r11 b11) 0 16) d11 =
    j18AtARB a00 r00 b00 d11 + 4 * (j18AtARB a10 r10 b10 d11 + 4 * (j18AtARB a01 r01 b01 d11 + 4 *
    j18AtARB a11 r11 b11 d11)) := by
  unfold j4FromThrNT5; simp only [fN63_eq, nat_mod_def, nat_div_def, nat_mul_def, nat_add_def]
  rw [bNT5_eq, getNT16F_eq]
  have hg := getNT63_buildNT63 (thr36PackLeaf a00 r00 b00 a10 r10 b10 a01 r01 b01 a11 r11 b11)
    5 0 (d11 % 32) (by simpa using Nat.mod_lt d11 (by omega))
  rw [show 2 ^ 5 / 2 = 16 by decide, zero_add] at hg
  rw [hg]
  obtain ⟨u00, u10, u01, u11⟩ :=
      thr36PackLeaf_unpack a00 r00 b00 a10 r10 b10 a01 r01 b01 a11 r11 b11 (d11 % 32); rw [u00, u10,
      u01, u11, evalThr9_thr9OfARB a00 d11 r00 b00, evalThr9_thr9OfARB a10 d11 r10 b10,
      evalThr9_thr9OfARB a01 d11 r01 b01, evalThr9_thr9OfARB a11 d11 r11 b11]
theorem buildJPackNT_eq (a : Nat) : buildJPackNT a = bNT11 (jPack4Leaf a) 0 1024 := by
  unfold buildJPackNT; rw [sNT63_eq]; congr 1; funext d11; rw [j4FromThrNT5_eq]; unfold jPack4Leaf;
  simp only [fN63_eq, nat_add_def, nat_mul_def]
theorem j18AtARB_even_true_eq_odd_false {a : Nat} (ha : a % 2 = 0) (r01 : Bool)
    (d11 : Nat) : j18AtARB a r01 true d11 = j18AtARB (a + 1) r01 false d11 := by
  unfold j18AtARB
  simp only [fN63_eq, sB63_eq, nat_div_def, nat_mod_def]
  rw [show (a + 1) / 8 = a / 8 by omega, show (a + 1) / 2 = a / 2 by omega,
    show (a + 1) / 4 = a / 4 by omega, ha, show (a + 1) % 2 = 1 by omega]
  dsimp only [cond, Nat.beq]
  unfold j18CarryEval
  simp only [sB63_eq]
  have he0 (z : Bool) : xorBF (andB63 (xorBF (notBF z) true) (xorBF false true)) true =
      xorBF (andB63 (xorBF (notBF z) false) (xorBF true false)) false := by cases z <;> rfl
  rw [he0, show xorBF false true = xorBF true false from rfl]
theorem checkSmCoordsB_true (isNN : Bool) : checkSmCoordsB isNN = true := by
  have h := (andB63_eq_true _ _).mp tSmCoords
  cases isNN
  · exact h.1
  · exact h.2

theorem smCoords_lt256 (isNN : Bool) {d2 : Nat}
    (hd2 : d2 < 256) : t11OfParts (evenOctIdxT10K isNN d2) % 64 = 0 ∧
    (t11OfParts (evenOctIdxT10K isNN d2) / 64) % 16 = 0 := by
  have hc := ((andB63_eq_true _ _).mp (checkSmCoordsB_true isNN)).1;
  have hpt :=
      allCnt63_sound hc d2 hd2; simp only [zero_add, sParts_eq, evenOctPartsW11_eq_w11B,
      nat_mod_def, nat_add_def, nat_mul_def,
      Nat.beq_eq] at hpt; have h1024 : t11OfParts (evenOctIdxT10K isNN d2) % 1024 = 0 := hpt; omega
theorem smCoords_tail16 (isNN : Bool) {d2 : Nat} (hmem : d2 ∈ tail16List) :
    (t11OfParts (evenOctIdxT10K isNN d2) / 64) % 8 = 0 ∧ t11OfParts (evenOctIdxT10K isNN d2) % 64 =
    d2 % 64 := by
  have hc := ((andB63_eq_true _ _).mp (checkSmCoordsB_true isNN)).2;
  have hpt :=
      allList63_sound hc d2 hmem; simp only [sParts_eq, evenOctPartsW11_eq_w11B, fN63_eq,
      andB63_eq_true, nat_mod_def, nat_div_def, nat_add_def, nat_mul_def,
      Nat.beq_eq] at hpt; exact hpt
attribute [local irreducible] buildNT63 bNT5 bNT9 bNT11 bNT12 bNT13 word512DualLegLo6T wOfU5GamF
    allCnt63 allList63 buildJPackNT checkSmCoordsB
theorem stepZeroST_eq {d : Nat} {z : SumTree} (hz : z = zeroST d) :
    stepZeroST z = zeroST (d + 1) := by subst hz; rfl

theorem zeroST7F_eq : zeroST7F = zeroST 7 :=
  stepZeroST_eq (stepZeroST_eq (stepZeroST_eq (stepZeroST_eq
    (stepZeroST_eq (stepZeroST_eq (stepZeroST_eq rfl))))))

def subSTD : Nat → SumTree → Nat → Nat → SumTree
  | 0, t, idx, dw => subST0F t idx dw
  | d + 1, t, idx, dw => stepSubST (subSTD d) (2 ^ d) t idx dw

theorem subST64F_eq_subSTD : subST64F = subSTD 7 := rfl

inductive IsTreeOf (f : Nat → Nat) : Nat → Nat → SumTree → Prop
  | leaf (base : Nat) : IsTreeOf f 0 base (.leaf (f base))
  | node {d base s : Nat} {l r : SumTree} :
      s = stVal l + stVal r →
      IsTreeOf f d base l →
      IsTreeOf f d (base + 2 ^ d) r →
      IsTreeOf f (d + 1) base (.node s l r)

theorem IsTreeOf.isValid {f : Nat → Nat} {d base : Nat} {st : SumTree} (h : IsTreeOf f d base st) :
    IsValidST d st := by
  induction h with
  | leaf _ => exact .leaf _
  | node hs _ _ ihl ihr => exact .node hs ihl ihr

theorem IsTreeOf.congr {f g : Nat → Nat} {d base : Nat} {st : SumTree} (h : IsTreeOf f d base st)
    (hfg : ∀ i < 2 ^ d, f (base + i) = g (base + i)) : IsTreeOf g d base st := by
  induction h with
  | leaf base =>
      have h0 := hfg 0 (by omega)
      rw [add_zero] at h0; rw [h0]; exact .leaf base
  | @node d base s l r hs _ _ ihl ihr =>
      refine .node hs (ihl fun i hi => hfg i (by rw [Nat.pow_succ]; omega))
        (ihr fun i hi => ?_)
      rw [Nat.add_assoc]
      exact hfg (2 ^ d + i) (by rw [Nat.pow_succ]; omega)

theorem IsTreeOf.le_stVal {f : Nat → Nat} {d base : Nat} {st : SumTree} (h : IsTreeOf f d base st) :
    ∀ i < 2 ^ d, f (base + i) ≤ stVal st := by
  induction h with
  | leaf base =>
      intro i hi
      have hz : i = 0 := by omega
      subst hz; simp [stVal]
  | @node d base s l r hs _ _ ihl ihr =>
      intro i hi; dsimp only [stVal]
      by_cases hlt : i < 2 ^ d
      · have h1 := ihl i hlt; omega
      · have h2 := ihr (i - 2 ^ d) (by rw [Nat.pow_succ] at hi; omega)
        rw [show base + 2 ^ d + (i - 2 ^ d) = base + i by omega] at h2
        omega

theorem zeroST_isTreeOf :
    ∀ (d base : Nat), IsTreeOf (fun _ => 0) d base (zeroST d) ∧ stVal (zeroST d) = 0
  | 0, base => ⟨.leaf base, rfl⟩
  | d + 1, base => by
      obtain ⟨hl, sl⟩ := zeroST_isTreeOf d base; obtain ⟨hr, _⟩ := zeroST_isTreeOf d (base + 2 ^ d)
      unfold zeroST; rw [sST63_eq]
      exact ⟨.node (by omega) hl hr, rfl⟩

def updAdd (f : Nat → Nat) (k dw x : Nat) : Nat := f x + if x = k then dw else 0
def updSub (f : Nat → Nat) (k dw x : Nat) : Nat := f x - if x = k then dw else 0

theorem insST_isTreeOf {f : Nat → Nat} {d base : Nat} {st : SumTree} (h : IsTreeOf f d base st) :
    ∀ (idx dw : Nat), idx < 2 ^ d → IsTreeOf (updAdd f (base + idx) dw) d base (insST (2 ^ d /
    2) st idx dw) ∧ stVal (insST (2 ^ d / 2) st idx dw) = stVal st + dw := by
  induction h with
  | leaf base =>
      intro idx dw hidx
      obtain rfl : idx = 0 := by omega
      simp only [add_zero, insST, fN63_eq, nat_add_def]
      exact ⟨(show updAdd f base dw base = f base + dw by simp [updAdd]) ▸ .leaf base, rfl⟩
  | @node d base s l r hs hl hr ihl ihr =>
      intro idx dw hidx
      rw [Nat.pow_succ] at hidx ⊢
      rw [Nat.mul_div_cancel _ (by decide)]
      unfold insST
      cases hb : Nat.ble (2 ^ d) idx <;>
        simp only [fN63_eq, sST63_eq, nat_add_def, nat_div_def, nat_sub_def]
      · have hlt := Nat.lt_of_not_le fun hge =>
          Bool.noConfusion (hb.symm.trans (Nat.ble_eq.mpr hge))
        obtain ⟨vl, sl⟩ := ihl idx dw hlt
        exact ⟨.node (by omega) vl
          (hr.congr fun i _ => by rw [updAdd, ite_eq_right (by omega), add_zero]), rfl⟩
      · have hge : 2 ^ d ≤ idx := Nat.ble_eq.mp hb
        obtain ⟨vr, sr⟩ := ihr (idx - 2 ^ d) dw (by omega)
        rw [show base + 2 ^ d + (idx - 2 ^ d) = base + idx by omega] at vr
        exact ⟨.node (by omega)
          (hl.congr fun i hi => by rw [updAdd, ite_eq_right (by omega), add_zero]) vr, rfl⟩

theorem subSTD_isTreeOf {f : Nat → Nat} {d base : Nat} {st : SumTree} (h : IsTreeOf f d base st) :
    ∀ (idx dw : Nat), idx < 2 ^ d → dw ≤ f (base + idx) →
    IsTreeOf (updSub f (base + idx) dw) d base (subSTD d st idx dw) ∧ stVal (subSTD d st idx dw) =
    stVal st - dw := by
  induction h with
  | leaf base =>
      intro idx dw hidx _
      obtain rfl : idx = 0 := by omega
      simp only [add_zero, subSTD, subST0F, fN63_eq, nat_sub_def]
      exact ⟨(show updSub f base dw base = f base - dw by simp [updSub]) ▸ .leaf base, rfl⟩
  | @node d base s l r hs hl hr ihl ihr =>
      intro idx dw hidx hdw
      rw [Nat.pow_succ] at hidx
      unfold subSTD stepSubST
      cases hb : Nat.ble (2 ^ d) idx <;> simp only [fN63_eq, sST63_eq, nat_sub_def]
      · have hlt := Nat.lt_of_not_le fun hge =>
          Bool.noConfusion (hb.symm.trans (Nat.ble_eq.mpr hge))
        have _ := hl.le_stVal idx hlt
        obtain ⟨vl, sl⟩ := ihl idx dw hlt hdw
        exact ⟨.node (by omega) vl
          (hr.congr fun i _ => by rw [updSub, ite_eq_right (by omega), Nat.sub_zero]), rfl⟩
      · have hge : 2 ^ d ≤ idx := Nat.ble_eq.mp hb
        have hba : base + 2 ^ d + (idx - 2 ^ d) = base + idx := by omega
        have hdwR : dw ≤ f (base + 2 ^ d + (idx - 2 ^ d)) := hba.symm ▸ hdw
        have _ := hr.le_stVal (idx - 2 ^ d) (by omega)
        obtain ⟨vr, sr⟩ := ihr (idx - 2 ^ d) dw (by omega) hdwR
        exact ⟨.node (by omega) (hl.congr fun i hi => by
          rw [updSub, ite_eq_right (by omega), Nat.sub_zero]) (hba ▸ vr), rfl⟩

theorem addST_isTreeOf {f g : Nat → Nat} {d base : Nat} {t1 t2 : SumTree}
    (h1 : IsTreeOf f d base t1) (h2 : IsTreeOf g d base t2) : IsTreeOf (fun x => f x +
    g x) d base (addST t1 t2) ∧ stVal (addST t1 t2) = stVal t1 + stVal t2 := by
  induction h1 generalizing t2 with
  | leaf base =>
      cases h2 with
      | leaf _ =>
          unfold addST; rw [fN63_eq, nat_add_def]
          exact ⟨.leaf base, rfl⟩
  | @node d base s1 l1 r1 hs1 hl1 hr1 ihl ihr =>
      cases h2 with
      | node hs2 hl2 hr2 =>
          unfold addST; simp only [fN63_eq, sST63_eq, nat_add_def]
          obtain ⟨vl, sl⟩ := ihl hl2; obtain ⟨vr, sr⟩ := ihr hr2
          exact ⟨.node (by rw [sl, sr, hs1, hs2]; ring) vl vr, rfl⟩

def IsST4Of (F : Nat → Nat → Nat) : ST4 → Prop
  | .mk _ a b c d =>
      IsTreeOf (F 0) 7 0 a ∧ IsTreeOf (F 1) 7 0 b ∧
      IsTreeOf (F 2) 7 0 c ∧ IsTreeOf (F 3) 7 0 d

theorem IsST4Of.isValid {F : Nat → Nat → Nat} {p : ST4} (h : IsST4Of F p) : IsValidST4 p := by
  rcases p with ⟨_, a, b, c, d⟩
  exact ⟨h.1.isValid, h.2.1.isValid, h.2.2.1.isValid, h.2.2.2.isValid⟩

theorem IsST4Of.congr {F G : Nat → Nat → Nat} {p : ST4} (h : IsST4Of F p)
    (hFG : ∀ j < 4, ∀ idx < 128, F j idx = G j idx) : IsST4Of G p := by
  rcases p with ⟨_, a, b, c, d⟩
  refine ⟨h.1.congr (fun i hi => by simpa using hFG 0 (by omega) i hi),
    h.2.1.congr (fun i hi => by simpa using hFG 1 (by omega) i hi),
    h.2.2.1.congr (fun i hi => by simpa using hFG 2 (by omega) i hi),
    h.2.2.2.congr (fun i hi => by simpa using hFG 3 (by omega) i hi)⟩

attribute [local irreducible] zeroST7F zeroST insST64F subST64F addST7F
theorem get_bNT11 (f : Nat → Nat) {d11 : Nat} (hd11 : d11 < 2048) :
    getNT1024F (bNT11 f 0 1024) d11 = f d11 := by
  rw [bNT11_eq, getNT1024F_eq]
  have hg := getNT63_buildNT63 f 11 0 d11 (by simpa using hd11)
  have hp1024 : (2 ^ 11 / 2 : Nat) = 1024 := by norm_num
  simpa only [hp1024, zero_add] using hg

attribute [local irreducible] jPack4Leaf
def IsST4P2Of (F0 F1 : Nat → Nat → Nat) : ST4P2 → Prop
  | .mk s0 s1 => IsST4Of F0 s0 ∧ IsST4Of F1 s1

theorem IsST4P2Of.congr {F0 F1 F0' F1' : Nat → Nat → Nat} {p : ST4P2} (h : IsST4P2Of F0 F1 p)
    (h0 : ∀ j < 4, ∀ idx < 128, F0 j idx = F0' j idx) (h1 : ∀ j < 4, ∀ idx < 128, F1 j idx =
    F1' j idx) : IsST4P2Of F0' F1' p := by
  rcases p with ⟨s0, s1⟩
  exact ⟨h.1.congr h0, h.2.congr h1⟩

theorem updAdd_updSub_bkt {j0 j1 z0 dw S j idx : Nat}
    (_hjNe : j0 ≠ j1) : ((if j0 = j ∧ z0 = idx then dw else 0) + S - (if j = j0 ∧ idx =
    z0 then dw else 0)) + (if j = j1 ∧ idx = z0 then dw else 0) = (if j1 = j ∧ z0 =
    idx then dw else 0) + S := by
  split_ifs <;> omega
def IsST4T3Sum (F0 F1 : Nat → Nat → Nat) : ST4T3 → Prop
  | .mk sc s0 s1 =>
      ∃ Fc G0 G1 : Nat → Nat → Nat,
        IsST4Of Fc sc ∧ IsST4Of G0 s0 ∧ IsST4Of G1 s1 ∧
        (∀ j < 4, ∀ idx < 128, Fc j idx + G0 j idx = F0 j idx) ∧
        (∀ j < 4, ∀ idx < 128, Fc j idx + G1 j idx = F1 j idx)

theorem IsST4T3Sum.congr {F0 F1 F0' F1' : Nat → Nat → Nat} {t : ST4T3} (h : IsST4T3Sum F0 F1 t)
    (h0 : ∀ j < 4, ∀ idx < 128, F0 j idx = F0' j idx) (h1 : ∀ j < 4, ∀ idx < 128, F1 j idx =
    F1' j idx) : IsST4T3Sum F0' F1' t := by
  rcases t with ⟨sc, s0, s1⟩
  rcases h with ⟨Fc, G0, G1, hsc, hs0, hs1, e0, e1⟩
  exact ⟨Fc, G0, G1, hsc, hs0, hs1, fun j hj idx hi => (e0 j hj idx hi).trans (h0 j hj idx hi),
      fun j hj idx hi => (e1 j hj idx hi).trans (h1 j hj idx hi)⟩

theorem sufST_le_add_stVal {d : Nat} {t : SumTree} (hv : IsValidST d t) : ∀ (h M acc : Nat),
    sufST h t M acc ≤ acc + stVal t := by
  induction hv with
  | leaf v =>
      intro h M acc; unfold sufST
      rw [nat_add_def]; dsimp only [stVal]; omega
  | @node d s l r hs hl hr ihl ihr =>
      intro h M acc; unfold sufST; simp only [nat_add_def, nat_div_def, nat_sub_def, stVal63_eq];
      have hst_node : stVal (.node s l r) = s := rfl; rw [hst_node]
      cases Nat.ble (M + 1) h
      · dsimp only [Bool.casesOn]; have hR := ihr (h / 2) (M - h) acc; omega
      · dsimp only [Bool.casesOn]; have hL := ihl (h / 2) M (acc + stVal r); omega
theorem sZLL_eq {α : Type} (l : ZLeafL) (k : ZLeafL → α) : sZLL l k = k l := by
  cases l <;> simp only [sZLL, fN63_eq]

theorem zKnotFast_at_lo6NT (cb : ChW11) (k i7 j : Nat) (hi7 : i7 < 128)
    (hj : j < 4) : chFnFast cb (Nat.div (getNT256F (bNT9 word512DualLegLo6T 0 256) (4 * i7 + j))
    (2 ^ k)) = zKnotLo6 cb k i7 j := by
  rw [bNT9_eq, getNT256F_eq, nat_div_def]
  have hg := getNT63_buildNT63 word512DualLegLo6T 9 0 (4 * i7 + j) (by omega)
  have hp256 : (2 ^ 9 / 2 : Nat) = 256 := by norm_num
  rw [hp256, zero_add] at hg; rw [hg]; exact zKnotLo6_fastJ cb k i7 j
theorem t11_step_arith {M I7 T11 wBase step2 : Nat} (hstep : step2 = 512 ∨ step2 = 256 ∨ step2 =
    128 ∨ step2 = 64 ∨ step2 = 32 ∨ step2 = 16 ∨ step2 = 8 ∨ step2 = 4 ∨ step2 = 2 ∨ step2 = 1)
    (hw : wBase = 0 ∨ wBase = 131072) (hmsh : M * step2 = wBase + 2048 * I7 + T11) : T11 % step2 =
    0 ∧ (wBase + 2048 * I7) / step2 + T11 / step2 = M := by
  rcases hstep with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl <;> omega

theorem sq_mod4_cases (x : ℕ) : (x % 2 = 0 ∧ x ^ 2 = 4 * (x / 2) ^ 2) ∨ (x % 2 = 1 ∧ x ^ 2 % 4 = 1)
    := by
  have h2 : (2 * (x / 2) + x % 2) ^ 2 = 4 * (x / 2) ^ 2 + 4 * (x / 2) * (x % 2) + (x % 2) ^ 2 := by
    ring
  rw [Nat.div_add_mod] at h2
  rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with h | h <;> rw [h] at h2 <;> omega

theorem sq_mod8_bound (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h4 : (4 * (x / 4) + x % 4) ^ 2 =
      8 * (2 * (x / 4) ^ 2 + (x / 4) * (x % 4)) + (x % 4) ^ 2 := by ring
  rw [Nat.div_add_mod] at h4
  rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with h | h | h | h <;>
    rw [h] at h4 <;> omega

theorem is3DBoxDistSq_mod32_ne_28 {d2 : ℕ} (h3d : Is3DBoxDistSq d2) : ¬(d2 % 32 = 28) := by
  rcases h3d with ⟨a, b, c, _, _, _, rfl⟩
  intro h28
  rcases sq_mod4_cases a with ⟨_, ha⟩ | ⟨_, ha⟩ <;>
    rcases sq_mod4_cases b with ⟨_, hb⟩ | ⟨_, hb⟩ <;>
    rcases sq_mod4_cases c with ⟨_, hc⟩ | ⟨_, hc⟩
  · rw [ha, hb, hc] at h28
    have h8 : ((a / 2) ^ 2 + (b / 2) ^ 2 + (c / 2) ^ 2) % 8 = 7 := by omega
    have sa := sq_mod8_bound (a / 2); have sb := sq_mod8_bound (b / 2);
    have sc := sq_mod8_bound (c / 2); omega
  all_goals omega

theorem elim_st4p2b (x : ST4P2B) : ∃ ok : Bool, ∃ st : ST4P2, x = .mk ok st := by
  cases x with | mk ok st => exact ⟨ok, st, rfl⟩
end QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.CoulombK115
open Operator QProg Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PrimitiveGate (T TOFF)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt
    natOfZModBits_testBit_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4
    (zmod2_eq_of_beq_one_eq_s1b)
theorem cnot_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (c t : Wire n) (hct : c ≠ t) (hc : S c) (ht : S t) :
    (DynamicCircuit.circuit (Var := Var) (.CNOT c t hct)).count .T = 0 ∧
    (DynamicCircuit.circuit (Var := Var) (.CNOT c t hct)).count .TOFF = 0 ∧
    DynWires S (DynamicCircuit.circuit (Var := Var) (.CNOT c t hct)) :=
  ⟨rfl, rfl, fun i ↦ by fin_cases i <;> [exact hc; exact ht]⟩

theorem natOfZModBits18_bit (f : Fin 18 → ZMod 2)
    (b : Fin 18) : (if (natOfZModBits 18 f).testBit b.val then (1 : ZMod 2) else 0) = f b := by
  rw [natOfZModBits_testBit_lt f b.isLt]
  rcases DynCircExt.bit_cases (f b) with h | h <;> rw [h] <;> decide

theorem dom22Bit21_eq_d2_xor (isNN : Bool) {d2 : ℕ} (hd2 : d2 ≤ 195075) :
    dom22Bit (evenOctIdxT10K isNN d2) ⟨21, by decide⟩ =
      xor (d2.testBit 16) (d2.testBit 17) := by
  change (evenOctKRef (max d2 (if isNN then 8 else 1))).testBit 3 = xor (d2.testBit 16)
      (d2.testBit 17)
  conv_rhs => rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hMain : (evenOctKRef d2).testBit 3 =
      xor (decide (d2 / 65536 % 2 = 1)) (decide (d2 / 131072 % 2 = 1)) := by
    unfold evenOctKRef
    by_cases h64 : d2 < 65536
    · rw [show d2 / 65536 % 2 = 0 by omega, show d2 / 131072 % 2 = 0 by omega]
      split_ifs <;> decide
    · by_cases h128 : d2 < 131072
      · rw [show d2 / 65536 % 2 = 1 by omega, show d2 / 131072 % 2 = 0 by omega]
        split_ifs <;> first | decide | omega
      · rw [show d2 / 65536 % 2 = 0 by omega, show d2 / 131072 % 2 = 1 by omega]
        split_ifs <;> first | decide | omega
  cases isNN <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · by_cases h0 : d2 = 0
    · exact h0 ▸ by decide
    · rwa [Nat.max_eq_left (by omega)]
  · by_cases h8 : d2 ≤ 8
    · rw [Nat.max_eq_right h8, show d2 / 65536 % 2 = 0 by omega, show d2 / 131072 % 2 = 0 by omega]
      decide
    · rwa [Nat.max_eq_left (by omega)]

theorem zmod2_dom21_xor_eq (b16 b17 : Bool) : (if b17 then (1 : ZMod 2) else 0) +
    (if b16 then 1 else 0) = if xor b16 b17 then 1 else 0 := by
  cases b16 <;> cases b17 <;> decide
end QuantumComputation.Specs.PhotochemistrySolution.CoulombK115
end

set_option maxRecDepth 200000
section
open scoped Circuit.Notation
section
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Sub63Stage25W309
open PhotochemistrySolution.PortBAncillaScrub Operator QProg Matrix HermitianMat Circuit Qubit
  PrimitiveGate PhotochemistrySolution.KetSupport PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCore
open PhotochemistrySolution.ProviderCoreFused PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ProviderZeroFloor
open PhotochemistrySolution.FastQft8 PhotochemistrySolution.Kinetic664
open PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.Qft8PostCancelT5
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.WStateStage2Load PhotochemistrySolution.WStateWalkSeam
  PhotochemistrySolution.RouterAlwaysLoW338
open PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.NucPairFlags
  PhotochemistrySolution.AlwaysLoNuc8886W338 PhotochemistrySolution.Stage2W325AlwaysLo
  PhotochemistrySolution.AlwaysLoW325 PhotochemistrySolution.AlwaysLoW322
  PhotochemistrySolution.ParityCheckW309
open PhotochemistrySolution.SelectRefl
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (uSwapHi24
    SharedPortBWiring val_rBufHi_rElecLayout val_rBufHi_rNucLayout routerCtrlSet_pubIdx_elec
    HCNOTSupportedIn hcnotSupportedIn_fixedSwapVec)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr CleanWorkStep phaseFlipUnitary
    reflULGen bOuterZeroNErem uRouterSwapConj uRouterSwapAlwaysLoConj uZeroSwapNE uSwapHi24
    uBellLoCopyHiAlwaysLoConj uBellLoEAlwaysLoMux_wstate uCopyAll3AlwaysLoMux_wstate

section
open PhotochemistrySolution.PotOraclePortB PhotochemistrySolution.PotOraclePortBStream
  PhotochemistrySolution.PotOraclePortBStage4
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (appendFin
    appendFin_castAdd appendFin_natAdd appendFin_cases dynWires_bellXHalfVecDyn_gen)
theorem circWires_cOut40Scrub3_w310_mCoin {wWork mCoin n : ℕ} {S : Wire n → Prop} (hw : 309 ≤ wWork)
    (rTot : QRegister dLayout n)
    (hAct : ∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w → S (rTot w)) :
    CircWires S (cOut40Scrub3 rTot) := by
  dsimp only [cOut40Scrub3, CircWires, Circuit.CNOT]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> intro i <;> fin_cases i <;>
    exact hAct _ (by
      unfold ActiveOuterCoinStackOf
      first | rw [val_wOut0] | rw [val_wOut1] | rw [val_wOut14] | rw [val_wOut15]
            | rw [val_wOut32] | rw [val_wOut34] | rw [val_wOut35]
      omega)
end
end QuantumComputation.Specs.PhotochemistrySolution.Sub63Stage25W309
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp198Opt

open scoped ComplexOrder MatrixOrder
open Operator QProg Matrix Circuit Qubit PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.ProviderCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket ComputeProg
    andComputeCircuit count_andComputeCircuit_t count_andComputeCircuit_toff)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB
    (andComputeCircuit_mulVec_ket_of_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket_X ket_CNOT
    eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (PotBPhaseBit24Fn
    PotBCoinSwap24Fn ReflPotSliceSpec24 ValidPotBFlags24 rPotBWork24 rPotBCoin24)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (wPotB24LocQ
    wPotB24IsScreen wPotB24IsPot wPotB24IsNN wPotB24Sp1B0 wPotB24Sp1B1 wPotB24Sp2B0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (wPotB24Sp2B1
    rPotB24NucA rPotB24ElecA rPotB24PortB r41Of24 r41Of24_ctrl r41Of24_work r41Of24_lt81)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (r41Of24_blocks
    validPotBFlags_r41Of24 potReflPortBSt24 potReflPortBPh0_24)
def xorPortB24NotScr {W n : ℕ} (r : QRegister (105 + W) n) (β : BitAssignment n) :
    BitAssignment n :=
    writeReg β (rPotB24PortB r) (fun i ↦ β (rPotB24PortB r i) + (1 + β (wPotB24IsScreen r)) *
    β (rPotB24NucA r i))
def xorPortB41NotScr {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n) :
    BitAssignment n :=
    writeReg β (rPotBPortB r41) (fun i ↦ β (rPotBPortB r41 i) + (1 + β (wPotBIsScreen r41)) *
    β (rPotBNucA r41 i))
theorem xorPortB41NotScr_eq_24 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) (β : BitAssignment n) : xorPortB41NotScr (r41Of24 r rCoin hd) β =
    xorPortB24NotScr r β := by
  have ⟨hNA, _, hPB⟩ := r41Of24_blocks r rCoin hd
  have hScr : wPotBIsScreen (r41Of24 r rCoin hd) = wPotB24IsScreen r :=
    r41Of24_lt81 r rCoin hd (m := 1) (by omega)
  unfold xorPortB41NotScr xorPortB24NotScr; rw [hPB, hScr, hNA]
theorem xorPortB41NotScr_outside {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n)
    {m : ℕ} (hm : m < 122 + Wp) (hout : m < 57 ∨ 81 ≤ m) : xorPortB41NotScr r41 β (r41 ⟨m, hm⟩) =
    β (r41 ⟨m, hm⟩) :=
  writeReg_apply_of_not_mem _ _ _ _
    (fun ⟨i, hi⟩ ↦ r41_blk_ne_wire r41 i _ (by have := i.isLt; omega) hi)

theorem xorPortB41NotScr_portB {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n)
    (i : Fin 24) : xorPortB41NotScr r41 β (rPotBPortB r41 i) = β (rPotBPortB r41 i) +
    (1 + β (wPotBIsScreen r41)) * β (rPotBNucA r41 i) := writeReg_apply_reg _ _ _ i
theorem xorPortB41NotScr_work {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n)
    (u : Fin Wp) : xorPortB41NotScr r41 β (rPotBWork r41 u) = β (rPotBWork r41 u) :=
  writeReg_apply_of_not_mem _ _ _ _
    (fun ⟨i, hi⟩ ↦ r41_blk_ne_blk r41 i u (by have := i.isLt; omega) hi)

theorem xorPortB41NotScr_writeReg_z16_comm {Wp n : ℕ} (r41 : QRegister (122 + Wp) n)
    (β : BitAssignment n) (z16 : Fin 16 → ZMod 2) : writeReg (xorPortB41NotScr r41 β)
    (rMuxZ16 r41) z16 = xorPortB41NotScr r41 (writeReg β (rMuxZ16 r41) z16) := by
  funext w; unfold xorPortB41NotScr
  by_cases hwZ : ∃ j : Fin 16, rMuxZ16 r41 j = w
  · obtain ⟨⟨jv, hj⟩, rfl⟩ := hwZ
    rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ (rPotBPortB r41) _ _
      (fun ⟨⟨iv, hi⟩, he⟩ ↦ r41_blk_ne_blk r41 ⟨iv, hi⟩ ⟨jv, hj⟩ (by omega) he),
      writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ w hwZ]
    by_cases hwPB : ∃ i : Fin 24, rPotBPortB r41 i = w
    · obtain ⟨⟨iv, hi⟩, rfl⟩ := hwPB
      rw [writeReg_apply_reg, writeReg_apply_reg,
        writeReg_apply_of_not_mem _ _ _ _ (fun ⟨⟨jv, hj⟩, he⟩ ↦
          r41_blk_ne_blk r41 ⟨jv, hj⟩ ⟨iv, hi⟩ (by omega) he),
        writeReg_apply_of_not_mem _ _ _ _ (fun ⟨⟨jv, hj⟩, he⟩ ↦
          r41_blk_ne_wire r41 ⟨jv, hj⟩ _ (by omega) he),
        writeReg_apply_of_not_mem _ _ _ _ (fun ⟨⟨jv, hj⟩, he⟩ ↦
          r41_blk_ne_blk r41 ⟨jv, hj⟩ ⟨iv, hi⟩ (by omega) he)]
    · simp only [writeReg_apply_of_not_mem _ _ _ w hwPB, writeReg_apply_of_not_mem _ _ _ w hwZ]

theorem xorPortB41NotScr_muxD2Val {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n) :
    muxD2Val r41 (xorPortB41NotScr r41 β) = muxD2Val r41 β := by
  have hBlk : ∀ (off : ℕ) (ho : off + 24 ≤ 57) (h41 : off + 24 ≤ 122 + Wp),
      coordOfReg24 (r41.compose (QRegister.block off 24 h41)) (xorPortB41NotScr r41 β) =
        coordOfReg24 (r41.compose (QRegister.block off 24 h41)) β :=
    fun off ho _ ↦ coordOfReg24_congr _ _ _ _ fun i ↦ by
      rw [show (r41.compose (QRegister.block off 24 _)) i = r41 ⟨off + i.val, by omega⟩ from
        congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val]))]
      exact xorPortB41NotScr_outside r41 β (by omega)
        (Or.inl ((Nat.add_lt_add_left i.isLt off).trans_le ho))
  unfold muxD2Val
  rw [xorPortB41NotScr_outside r41 β (m := 4) (by omega) (Or.inl (by omega)),
      xorPortB41NotScr_outside r41 β (m := 1) (by omega) (Or.inl (by omega)),
      hBlk 9 (by decide) _, hBlk 33 (by decide) _]
  rcases DynCircExt.bit_cases (β (wPotBIsScreen r41)) with hs | hs
  · simp [hs]
  · have hPB := coordOfReg24_congr (rPotBPortB r41) (rPotBPortB r41)
      (xorPortB41NotScr r41 β) β fun i ↦ by
      have h11 : (1 + 1 : ZMod 2) = 0 := rfl
      rw [xorPortB41NotScr_portB, hs, h11, zero_mul, add_zero]
    rw [hs, hPB]

theorem xorPortB41NotScr_validFlags {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) {β : BitAssignment n}
    (hV : ValidPotBFlags r41 β) : ValidPotBFlags r41 (xorPortB41NotScr r41 β) := by
  unfold ValidPotBFlags at hV ⊢
  rwa [xorPortB41NotScr_outside r41 β (m := 1) (by omega) (Or.inl (by omega)),
       xorPortB41NotScr_outside r41 β (m := 2) (by omega) (Or.inl (by omega)),
       xorPortB41NotScr_outside r41 β (m := 4) (by omega) (Or.inl (by omega))]

def pInPlaceMux2Bit {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (r41 : QRegister (122 + Wp) n) (i : Fin 24) : DynamicCircuit Var n :=
  let scr := wPotBIsScreen r41
  let na := rPotBNucA r41 i
  let pb := rPotBPortB r41 i
  let s0 := wMuxScr0 h193 r41
  (DynamicCircuit.circuit (andComputeCircuit scr na s0
    (r41_wire_ne_blk r41 _ i (by omega))
    (r41_ne r41 _ _ (by omega))
    (r41_blk_ne_wire r41 i _ (by omega)))).seq
    ((DynamicCircuit.circuit (Circuit.CNOT na pb
        (r41_blk_ne_blk r41 i i (by omega)))).seq
      ((DynamicCircuit.circuit (Circuit.CNOT s0 pb
          (r41_wire_ne_blk r41 _ i (by omega)))).seq
        (xUnloadCzPairsSeqDyn v s0
          [⟨scr, ⟨na, r41_wire_ne_blk r41 _ i (by omega)⟩⟩]
          (.circuit .identity))))

theorem count_pInPlaceMux2Bit {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (r41 : QRegister (122 + Wp) n) (i : Fin 24) : (pInPlaceMux2Bit h193 v r41 i).count .T = 4 ∧
    (pInPlaceMux2Bit h193 v r41 i).count .TOFF = 0 := by
  unfold pInPlaceMux2Bit; dsimp only
  obtain ⟨ut, uf⟩ := count_xUnloadCzPairsSeqDyn v (wMuxScr0 h193 r41)
    [⟨wPotBIsScreen r41, ⟨rPotBNucA r41 i, r41_wire_ne_blk r41 _ i (by omega)⟩⟩]
    (.circuit .identity)
  have hidT : (DynamicCircuit.circuit (Var := Var) (n := n) .identity).count .T = 0 := rfl
  have hidF : (DynamicCircuit.circuit (Var := Var) (n := n) .identity).count .TOFF = 0 := rfl
  rw [dc_count_seq, dc_count_seq, dc_count_seq, dc_count_seq, dc_count_seq, dc_count_seq,
      dc_count_circ, dc_count_circ, dc_count_circ, dc_count_circ, dc_count_circ, dc_count_circ,
      count_andComputeCircuit_t, count_andComputeCircuit_toff, (count_cnot_zero _ _ _).1,
      (count_cnot_zero _ _ _).2, (count_cnot_zero _ _ _).1, (count_cnot_zero _ _ _).2, ut, uf, hidT,
      hidF]
  exact ⟨by omega, rfl⟩

theorem step_pInPlaceMux2Bit {Var : Type} [Fintype Var] [DecidableEq Var] {W Wp n : ℕ}
    [NeZero (2 ^ n)] (h193 : 193 ≤ Wp) (v : Var) (rWork : QRegister W n)
    (r41 : QRegister (122 + Wp) n) (i : Fin 24) (st0 : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) (hs0 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (wMuxScr0 h193 r41) =
    0) : SubspaceStep (mkKetOpW rWork st0 ph) (mkKetOpW rWork (fun δ ↦ Function.update (st0 δ)
    (rPotBPortB r41 i) (st0 δ (rPotBPortB r41 i) + (1 + st0 δ (wPotBIsScreen r41)) *
    st0 δ (rPotBNucA r41 i))) ph) (pInPlaceMux2Bit h193 v r41 i) := by
  let scr := wPotBIsScreen r41
  let na := rPotBNucA r41 i
  let pb := rPotBPortB r41 i
  let s0 := wMuxScr0 h193 r41
  have hne_sn : scr ≠ na := r41_wire_ne_blk r41 _ i (by omega)
  have hne_ss0 : scr ≠ s0 := r41_ne r41 _ _ (by omega)
  have hne_ns0 : na ≠ s0 := r41_blk_ne_wire r41 i _ (by omega)
  have hne_np : na ≠ pb := r41_blk_ne_blk r41 i i (by omega)
  have hne_s0p : s0 ≠ pb := r41_wire_ne_blk r41 _ i (by omega)
  have hne_sp : scr ≠ pb := r41_wire_ne_blk r41 _ i (by omega)
  let stPost : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st0 δ) pb (st0 δ pb + (1 + st0 δ scr) * st0 δ na)
  let stAnd : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st0 δ) s0 (st0 δ scr * st0 δ na)
  let stC1 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (stAnd δ) pb (st0 δ pb + st0 δ na)
  let stC2 : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (stPost δ) s0 (stPost δ scr * stPost δ na)
  have mkCirc {stA stB : BitAssignment n → BitAssignment n} (c : Circuit n)
      (hc : ∀ δ, (∀ q, δ (rWork q) = 0) → c.eval.1 *ᵥ ket (stA δ) = ket (stB δ)) :
      SubspaceStep (Var := Var) (mkKetOpW rWork stA ph) (mkKetOpW rWork stB ph) (.circuit c) :=
    subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ c) (matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
      split_ifs with hz
      · rw [Matrix.mulVec_smul, hc δ hz]
      · exact Matrix.mulVec_zero _)
  have hsAnd := mkCirc (andComputeCircuit scr na s0 hne_sn hne_ss0 hne_ns0) fun δ hz ↦
    andComputeCircuit_mulVec_ket_of_zero scr na s0 hne_sn hne_ss0 hne_ns0 (st0 δ) (hs0 δ hz)
  have hsC1 := mkCirc (stA := stAnd) (stB := stC1) (Circuit.CNOT na pb hne_np) fun δ _ ↦ by
    rw [ket_CNOT]
    congr 1
    simp only [stAnd, stC1, Function.update_of_ne hne_s0p.symm, Function.update_of_ne hne_ns0]
  have hsC2 := mkCirc (stA := stC1) (stB := stC2) (Circuit.CNOT s0 pb hne_s0p) fun δ _ ↦ by
    rw [ket_CNOT]
    refine congrArg ket (funext fun w ↦ ?_)
    dsimp only [stC1, stC2, stAnd, stPost]
    by_cases hws0 : w = s0
    · subst hws0
      simp only [Function.update_of_ne hne_s0p, Function.update_self,
        Function.update_of_ne hne_sp, Function.update_of_ne hne_np]
    · by_cases hwpb : w = pb
      · subst hwpb
        simp only [Function.update_of_ne hws0, Function.update_self,
          Function.update_of_ne hne_s0p]
        ring
      · simp only [Function.update_of_ne hws0, Function.update_of_ne hwpb]
  exact subspaceStep_seq_u hsAnd (subspaceStep_seq_u hsC1 (subspaceStep_seq_u hsC2
    (subspaceStep_xUnloadSetProd_mkKetOpW v rWork s0 scr na hne_sn hne_ss0 hne_ns0
      (.circuit .identity) stPost ph (mkKetOpW rWork stPost ph)
      (fun δ hz ↦ (Function.update_of_ne hne_s0p _ _).trans (hs0 δ hz))
      (subspaceStep_id_mkKetOpW rWork stPost ph))))

def pInPlaceMux2Range {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp)
    (v : Var) (r41 : QRegister (122 + Wp) n) : ∀ (k : ℕ), k ≤ 24 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | k + 1, hk =>
      (pInPlaceMux2Range h193 v r41 k (Nat.le_of_succ_le hk)).seq
        (pInPlaceMux2Bit h193 v r41 ⟨k, hk⟩)

theorem count_pInPlaceMux2Range {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp)
    (v : Var) (r41 : QRegister (122 + Wp) n) :
    ∀ (k : ℕ) (hk : k ≤ 24),
      (pInPlaceMux2Range h193 v r41 k hk).count .T = 4 * k ∧
      (pInPlaceMux2Range h193 v r41 k hk).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      dsimp only [pInPlaceMux2Range];
      obtain ⟨tR, fR⟩ :=
          count_pInPlaceMux2Range h193 v r41 k (Nat.le_of_succ_le hk); obtain ⟨tB, fB⟩ :=
          count_pInPlaceMux2Bit h193 v r41 ⟨k, hk⟩; rw [dc_count_seq, dc_count_seq, tR, tB, fR, fB]
      exact ⟨by omega, rfl⟩

theorem dynWires_pInPlaceMux2Range {Var : Type} {Wp n : ℕ} {S : Wire n → Prop}
    (h193 : 193 ≤ Wp) (v : Var) (r41 : QRegister (122 + Wp) n) (hS : ∀ j, S (r41 j)) :
    ∀ (k : ℕ) (hk : k ≤ 24), DynWires S (pInPlaceMux2Range h193 v r41 k hk)
  | 0, _ => trivial
  | k + 1, hk =>
      ⟨dynWires_pInPlaceMux2Range h193 v r41 hS k (Nat.le_of_succ_le hk),
       cw_andComputeCircuit _ _ _ _ _ _ (hS _) (hS _) (hS _), cw_cnot (hS _) (hS _),
       cw_cnot (hS _) (hS _),
       dw_xUnload (hS _) (fun _ hp ↦ (List.mem_singleton.mp hp) ▸ ⟨hS _, hS _⟩) trivial⟩

theorem step_pInPlaceMux2Range {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp n : ℕ} [NeZero (2 ^ n)] (h193 : 193 ≤ Wp)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st0 : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hs0 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (wMuxScr0 h193 r41) = 0) :
    ∀ (k : ℕ) (hk : k ≤ 24),
      SubspaceStep (mkKetOpW rWork st0 ph)
        (mkKetOpW rWork (fun δ ↦ writeSub24 (st0 δ) (rPotBPortB r41) 0 k
          (fun i ↦ st0 δ (rPotBPortB r41 i) +
            (1 + st0 δ (wPotBIsScreen r41)) * st0 δ (rPotBNucA r41 i))) ph)
        (pInPlaceMux2Range h193 v r41 k hk)
  | 0, _ =>
      subspaceStep_of_eq_post (subspaceStep_id_mkKetOpW rWork st0 ph)
        (mkKetOpW_congr rWork (fun δ _ ↦ (writeSub24_zero (st0 δ) _ 0 _).symm) (fun _ _ ↦ rfl))
  | k + 1, hk => by
      let ik : Fin 24 := ⟨k, hk⟩
      let rP := rPotBPortB r41
      let bitFn : BitAssignment n → Fin 24 → ZMod 2 := fun β i ↦
          β (rP i) + (1 + β (wPotBIsScreen r41)) * β (rPotBNucA r41 i)
      let stMid : BitAssignment n → BitAssignment n := fun δ ↦
          writeSub24 (st0 δ) rP 0 k (bitFn (st0 δ))
      have hsR := step_pInPlaceMux2Range h193 v rWork r41 st0 ph hs0 k (Nat.le_of_succ_le hk)
      have hsB := step_pInPlaceMux2Bit h193 v rWork r41 ik stMid ph fun δ hz ↦
        (writeSub24_apply_out _ _ _ _ _ fun i ↦ r41_wire_ne_blk r41 _ i (by omega)).trans
          (hs0 δ hz)
      refine subspaceStep_of_eq_post (subspaceStep_seq_u hsR hsB)
        (mkKetOpW_congr rWork (fun δ _ ↦ funext fun w ↦ ?_) (fun _ _ ↦ rfl))
      by_cases hmP : ∃ i : Fin 24, rP i = w
      · obtain ⟨i, rfl⟩ := hmP
        dsimp only [stMid]
        by_cases hiEq : i = ik
        · subst hiEq
          rw [Function.update_self, writeSub24_apply_reg, writeSub24_apply_reg,
            ite_eq_right (fun ⟨_, hlt⟩ ↦ Nat.lt_irrefl k (by simpa only [zero_add] using hlt)),
            ite_eq_left ⟨Nat.zero_le _, by simpa only [zero_add] using Nat.lt_succ_self k⟩,
            writeSub24_apply_out _ _ _ _ _ fun j ↦ r41_wire_ne_blk r41 _ j (by omega),
            writeSub24_apply_out _ _ _ _ _ fun j ↦ r41_blk_ne_blk r41 ik j (by omega)]
        · rw [Function.update_of_ne (rP.wires.injective.ne hiEq),
            writeSub24_apply_reg, writeSub24_apply_reg]
          have hiNe : i.val ≠ k := Fin.val_ne_of_ne hiEq
          split_ifs <;> first | rfl | omega
      · dsimp only [stMid]
        rw [Function.update_of_ne fun h ↦ hmP ⟨ik, h.symm⟩,
          writeSub24_apply_out _ _ _ _ _ fun i h ↦ hmP ⟨i, h.symm⟩,
          writeSub24_apply_out _ _ _ _ _ fun i h ↦ hmP ⟨i, h.symm⟩]

def pInPlaceMux2_24 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (r41 : QRegister (122 + Wp) n) : DynamicCircuit Var n :=
    pInPlaceMux2Range h193 v r41 24 (Nat.le_refl 24)
theorem step_pInPlaceMux2_24_muxStNoM2 {Var : Type} [Fintype Var] [DecidableEq Var] {W Wp n : ℕ}
    [NeZero (2 ^ n)] (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var) (rWork : QRegister W n)
    (r41 : QRegister (122 + Wp) n) (st : BitAssignment n → BitAssignment n)
    (z16 : BitAssignment n → Fin 16 → ZMod 2) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (mkKetOpW rWork (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16 δ) (st δ)) ph)
    (mkKetOpW rWork (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16 δ) (xorPortB41NotScr r41 (st δ))) ph)
    (pInPlaceMux2_24 h193 v r41) ∧ (pInPlaceMux2_24 h193 v r41).count .T = 96 ∧
    (pInPlaceMux2_24 h193 v r41).count .TOFF = 0 := by
  have hw := wtop_ge192 h193 isCsel
  let stNo := fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16 δ) (st δ)
  have hs0 : ∀ δ, (∀ q, δ (rWork q) = 0) → stNo δ (wMuxScr0 h193 r41) = 0 := fun δ _ ↦
    muxStNoM2_pool_zero h193 isCsel r41 0 (z16 δ) (st δ) (u := 0) (by omega)
      (by cases isCsel <;> [exact Or.inl rfl; exact Or.inr (by omega)]) (Or.inl (by omega))
  have hs :=
      step_pInPlaceMux2Range h193 v rWork r41 stNo ph hs0 24 (Nat.le_refl 24); obtain ⟨ct, cf⟩ :=
      count_pInPlaceMux2Range h193 v r41 24 (Nat.le_refl 24)
  refine ⟨subspaceStep_of_eq_post hs (mkKetOpW_congr rWork (fun δ _ ↦ ?_) (fun _ _ ↦ rfl)), ct, cf⟩
  have hWorkEq : muxWorkValNoM2 h193 isCsel r41 0 (xorPortB41NotScr r41 (st δ)) =
      muxWorkValNoM2 h193 isCsel r41 0 (st δ) := by
    funext u; unfold muxWorkValNoM2; dsimp only
    rw [show wPotBLocQ r41 = r41 ⟨0, by omega⟩ from rfl,
        show wPotBIsPot r41 = r41 ⟨2, by omega⟩ from rfl,
        show wPotBIsNN r41 = r41 ⟨4, by omega⟩ from rfl,
        xorPortB41NotScr_outside r41 (st δ) (m := 0) (by omega) (Or.inl (by omega)),
        xorPortB41NotScr_outside r41 (st δ) (m := 2) (by omega) (Or.inl (by omega)),
        xorPortB41NotScr_outside r41 (st δ) (m := 4) (by omega) (Or.inl (by omega))]
    split_ifs with h1 h2 h3
    · rfl
    · rw [show rPotBNucA r41 ⟨(u.val - (Wtop Wp isCsel - 48)) % 24, Nat.mod_lt _ (by decide)⟩ =
            r41 ⟨9 + ((u.val - (Wtop Wp isCsel - 48)) % 24), by omega⟩ from
          congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val]))]
      exact xorPortB41NotScr_outside r41 (st δ) (by omega)
        (Or.inl (by have := Nat.mod_lt (u.val - (Wtop Wp isCsel - 48)) (by decide : 0 < 24); omega))
    · rw [show rPotBElecA r41 ⟨(u.val - (Wtop Wp isCsel - 48)) % 24, Nat.mod_lt _ (by decide)⟩ =
            r41 ⟨33 + ((u.val - (Wtop Wp isCsel - 48)) % 24), by omega⟩ from
          congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val]))]
      exact xorPortB41NotScr_outside r41 (st δ) (by omega)
        (Or.inl (by have := Nat.mod_lt (u.val - (Wtop Wp isCsel - 48)) (by decide : 0 < 24); omega))
    · rfl
  refine eq_of_r41_parts r41 (fun w hwOut ↦ ?_) (fun m hm ↦ ?_) (fun j ↦ ?_) (fun u ↦ ?_)
  · dsimp only [stNo]
    rw [writeSub24_apply_out _ _ _ _ _ (fun i h ↦ hwOut _ h), muxStNoM2_out _ _ _ _ _ _ hwOut,
        muxStNoM2_out _ _ _ _ _ _ hwOut]
    exact (writeReg_apply_of_not_mem _ (rPotBPortB r41) _ w (fun ⟨i, hi⟩ ↦ hwOut _ hi.symm)).symm
  · by_cases hmPB : 57 ≤ m ∧ m < 81
    · let i0 : Fin 24 := ⟨m - 57, by omega⟩
      have heq : r41 ⟨m, by omega⟩ = rPotBPortB r41 i0 :=
        congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val, i0]; omega))
      rw [heq, writeSub24_apply_reg, ite_eq_left ⟨Nat.zero_le _, by have := i0.isLt; omega⟩]
      have h1 : stNo δ (rPotBPortB r41 i0) = st δ (rPotBPortB r41 i0) := by
        dsimp only [stNo]; rw [← heq]; exact muxStNoM2_lt106 h193 isCsel r41 0 (z16 δ) (st δ) hm
      have h2 : stNo δ (wPotBIsScreen r41) = st δ (wPotBIsScreen r41) :=
        muxStNoM2_lt106 h193 isCsel r41 0 (z16 δ) (st δ) (m := 1) (by omega)
      have h3 : stNo δ (rPotBNucA r41 i0) = st δ (rPotBNucA r41 i0) := by
        dsimp only [stNo]
        rw [show rPotBNucA r41 i0 = r41 ⟨9 + i0.val, by omega⟩ from
          congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val]))]
        exact muxStNoM2_lt106 h193 isCsel r41 0 (z16 δ) (st δ) (by have := i0.isLt; omega)
      have h4 : muxStNoM2 h193 isCsel r41 0 (z16 δ) (xorPortB41NotScr r41 (st δ))
          (rPotBPortB r41 i0) = xorPortB41NotScr r41 (st δ) (rPotBPortB r41 i0) := by
        rw [← heq]; exact muxStNoM2_lt106 h193 isCsel r41 0 (z16 δ) _ hm
      rw [h1, h2, h3, h4, xorPortB41NotScr_portB]
    · dsimp only [stNo]
      rw [writeSub24_apply_out _ _ _ _ _
            (fun i ↦ r41_wire_ne_blk r41 _ i (by have := i.isLt; omega)),
          muxStNoM2_lt106 _ _ _ _ _ _ hm, muxStNoM2_lt106 _ _ _ _ _ _ hm,
          xorPortB41NotScr_outside r41 (st δ) (by omega) (by omega)]
  · dsimp only [stNo]
    rw [writeSub24_apply_out _ _ _ _ _ (fun i ↦ r41_blk_ne_blk r41 j i (by omega)),
        muxStNoM2_z16, muxStNoM2_z16]
  · dsimp only [stNo]
    rw [writeSub24_apply_out _ _ _ _ _ (fun i ↦ r41_blk_ne_blk r41 u i (by omega)),
        muxStNoM2_work, muxStNoM2_work, hWorkEq]

def muxStNoM2D2 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) : BitAssignment n :=
    writeReg (muxStNoM2 h193 isCsel r41 0 z16 β) (rMuxD2_18 h193 r41)
    (fun j ↦ if (muxD2Val r41 β).testBit j.val then 1 else 0)
theorem muxStNoM2_writeReg_d2_xor {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) :
    writeReg (muxStNoM2 h193 isCsel r41 0 z16 β) (rMuxD2_18 h193 r41)
    (fun j ↦ muxStNoM2 h193 isCsel r41 0 z16 β (rMuxD2_18 h193 r41 j) +
    (if (muxD2Val r41 β).testBit j.val then 1 else 0)) = muxStNoM2D2 h193 isCsel r41 z16 β := by
  have hw := wtop_ge192 h193 isCsel; unfold muxStNoM2D2
  congr 1; funext j
  have heq : rMuxD2_18 h193 r41 j = r41 ⟨122 + j.val, by omega⟩ :=
    congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val]))
  rw [heq, muxStNoM2_pool_zero h193 isCsel r41 0 z16 β
      (by have := j.isLt; omega)
      (by cases isCsel <;> [exact Or.inl rfl; exact Or.inr (by have := j.isLt; omega)])
      (Or.inl (by have := j.isLt; omega)), zero_add]

theorem muxStNoM2D2_d2 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n)
    (j : Fin 18) : muxStNoM2D2 h193 isCsel r41 z16 β (rMuxD2_18 h193 r41 j) =
    if (muxD2Val r41 β).testBit j.val then 1 else 0 := writeReg_apply_reg _ _ _ j
theorem muxDisj_m1_portB {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) : (rMuxM1 h193 isCsel r41).DisjointWires (rPotBPortB r41) := by
  have hw := wtop_ge192 h193 isCsel
  exact owCompose_disj r41 fun _ _ ↦ by simp only [QRegister.block_apply_val]; omega

theorem muxDisj_portB_d2 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    (rPotBPortB r41).DisjointWires (rMuxD2_18 h193 r41) :=
  owCompose_disj r41 fun _ _ ↦ by simp only [QRegister.block_apply_val]; omega

theorem openCoordDistSq_muxStNoM2_m1_portB {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) {β : BitAssignment n}
    (hPB0 : β (wPotBIsScreen r41) = 0 → ∀ i : Fin 24, β (rPotBPortB r41 i) = 0) :
    openCoordDistSq (coordOfReg24 (rMuxM1 h193 isCsel r41)
    (muxStNoM2 h193 isCsel r41 0 z16 (xorPortB41NotScr r41 β))) (coordOfReg24 (rPotBPortB r41)
    (muxStNoM2 h193 isCsel r41 0 z16 (xorPortB41NotScr r41 β))) =
    muxD2Val r41 (xorPortB41NotScr r41 β) := by
  rw [coordOfReg24_congr (rMuxM1 h193 isCsel r41) (rMuxM1 h193 isCsel r41) _
        (muxSt h193 isCsel r41 0 false z16 β) fun i ↦ by
      rw [muxStNoM2_m1, muxSt_m1, ite_eq_left (Nat.zero_le _), ite_eq_left (Nat.zero_le _),
          xorPortB41NotScr_outside r41 β (m := 4) (by omega) (Or.inl (by omega)),
          show rPotBNucA r41 i = r41 ⟨9 + i.val, by omega⟩ from
            congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val])),
          xorPortB41NotScr_outside r41 β (by omega)
            (Or.inl ((Nat.add_lt_add_left i.isLt 9).trans (by decide))),
          show rPotBElecA r41 i = r41 ⟨33 + i.val, by omega⟩ from
            congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val])),
          xorPortB41NotScr_outside r41 β (by omega)
            (Or.inl ((Nat.add_lt_add_left i.isLt 33).trans_le (by decide)))],
      coordOfReg24_congr (rPotBPortB r41) (rMuxM2 h193 isCsel r41) _
        (muxSt h193 isCsel r41 0 false z16 β) fun i ↦ by
      have hpEq : rPotBPortB r41 i = r41 ⟨57 + i.val, by omega⟩ :=
        congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val]))
      rw [hpEq, muxStNoM2_lt106 h193 isCsel r41 0 z16 _
            ((Nat.add_lt_add_left i.isLt 57).trans (by decide)),
          ← hpEq, xorPortB41NotScr_portB, muxSt_m2]
      rcases DynCircExt.bit_cases (β (wPotBIsScreen r41)) with hs | hs
      · rw [hs, hPB0 hs i]
        have h01 : ((0 : ZMod 2) == 1) = false := by decide
        simp only [h01, Bool.false_eq_true, ↓reduceIte, add_zero, one_mul, zero_add]
      · have h11 : ((1 : ZMod 2) == 1) = true := by decide
        have h20 : (1 + 1 : ZMod 2) = 0 := rfl
        simp only [hs, h11, ↓reduceIte, h20, zero_mul, add_zero],
      openCoordDistSq_muxSt_m1_m2, xorPortB41NotScr_muxD2Val]

structure Stage4ReflCoin24PotOraclePortBInPlace (kCoin Wp tPotU tPotC : ℕ)
    (potExpectK : BitAssignment kCoin → PotExpectFn) where
  sliceSpec : ∀ γ : BitAssignment kCoin, ReflPotSliceSpec24 (potExpectK γ)
  pCsel : ∀ {Var : Type} {n : ℕ},
    Var → QRegister (105 + Wp) n → QRegister kCoin n → DynamicCircuit Var n
  pUsel : ∀ {Var : Type} {n : ℕ},
    Var → QRegister (105 + Wp) n → QRegister kCoin n → DynamicCircuit Var n
  step_and_counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)] (v : Var) (rW : QRegister m n)
    (r : QRegister (105 + Wp) n) (rCoin : QRegister kCoin n)
    (_ : r.DisjointWires rCoin) (isCsel : Bool)
    (st : BitAssignment n → BitAssignment n),
    (∀ δ, (∀ q : Fin m, δ (rW q) = 0) → ValidPotBFlags24 r (st δ)) →
    (∀ δ (u : Fin Wp), (∀ q : Fin m, δ (rW q) = 0) → st δ (rPotBWork24 r u) = 0) →
    (∀ δ (i : Fin 24), (∀ q : Fin m, δ (rW q) = 0) →
      st δ (wPotB24IsScreen r) = 0 → st δ (rPotB24PortB r i) = 0) →
    let p := if isCsel then pCsel v r rCoin else pUsel v r rCoin
    SubspaceStep (mkKetOpW rW st (fun _ ↦ 0))
      (mkKetOpW rW
        (fun δ ↦ xorPortB24NotScr r
          (potReflPortBSt24 (fun γ ↦ (sliceSpec γ).coinSwap) isCsel r rCoin st δ))
        (potReflPortBPh0_24 (fun γ ↦ (sliceSpec γ).phaseBit) isCsel r rCoin st)) p ∧
    p.count .T = (if isCsel then tPotC else tPotU) ∧
    p.count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} (S : Wire n → Prop) (v : Var)
    (r : QRegister (105 + Wp) n) (rCoin : QRegister kCoin n),
    (∀ i : Fin (105 + Wp), S (r i)) → (∀ j : Fin kCoin, S (rCoin j)) →
    DynWires S (pCsel v r rCoin) ∧ DynWires S (pUsel v r rCoin)
end QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp198Opt
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.InPlacePortBOracle

open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate
  PhotochemistrySolution.KetSupport PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.ProviderCoreFused
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ProviderZeroFloor
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.PotOraclePortB
  PhotochemistrySolution.PotOraclePortBStream PhotochemistrySolution.PotOraclePortBStage4
  PhotochemistrySolution.Stage2ChDiffMux960
open PhotochemistrySolution.Stage2ChDiffNoNF PhotochemistrySolution.Sub5885
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.PortBSharedPoly
  PhotochemistrySolution.ReflStage4 PhotochemistrySolution.Stage2ElecOptA
open PhotochemistrySolution.WStateStage2Load PhotochemistrySolution.WStateWalkSeam
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.RouterAlwaysLoW338
  PhotochemistrySolution.NucPairFlags PhotochemistrySolution.PortBAncillaScrub
open PhotochemistrySolution.XMeasChunkQromUnld PhotochemistrySolution.Stage4Cluster22Xnor
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket ket_X ket_CNOT
    eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
    (bitSign bitSign_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated hiding zg47_hM0
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (ReflPotSliceSpec24
    ValidPotBFlags24 rPotBWork24 rPotBCoin24 wPotB24LocQ wPotB24IsScreen wPotB24IsPot wPotB24IsNN
    wPotB24Sp1B0 wPotB24Sp1B1 wPotB24Sp2B0 wPotB24Sp2B1 rPotB24NucA rPotB24ElecA rPotB24PortB
    potReflPortBSt24 potReflPortBPh0_24 potOraclePortB24BitEval potOraclePortB24CoinEval
    potB24GateActive)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Walk (take24Of35_sub63
    put24In35_sub63 liftReflPotSlice24To35_sub63 skip11Of116Wp_sub63 val_skip11Of116Wp_sub63
    circWires_cPackCnotAux_skip17_sub63)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp198Opt (xorPortB24NotScr
    xorPortB41NotScr Stage4ReflCoin24PotOraclePortBInPlace)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr

def skip17Of122Wp_ipb (Wp : ℕ) : QRegister (105 + Wp) (122 + Wp) :=
    (skip6Of122Wp_wstate Wp).compose (skip11Of116Wp_sub63 Wp)
theorem val_skip17Of122Wp_ipb {Wp : ℕ} (i : Fin (105 + Wp)) : (skip17Of122Wp_ipb Wp i).val =
    if i.val < 105 then i.val else i.val + 17 := by
  change (skip6Of122Wp_wstate Wp (skip11Of116Wp_sub63 Wp i)).val = _;
  rw [val_skip6Of122Wp_wstate, val_skip11Of116Wp_sub63]
  split_ifs <;> omega

def castZeroAddReg_ipb {kOut n : ℕ} (rCoin : QRegister (0 + kOut) n) : QRegister kOut n :=
  rCoin.compose ⟨⟨fun j ↦ ⟨j.val, by have := j.isLt; omega⟩,
    fun _ _ h ↦ Fin.ext (by simpa using congrArg Fin.val h)⟩⟩

def spec41Of24_ipb {kOut : ℕ} {peOut : BitAssignment kOut → PotExpectFn}
    (s24 : ∀ γ : BitAssignment kOut, ReflPotSliceSpec24 (peOut γ))
    (γω : BitAssignment (0 + kOut)) :
    ReflPotSliceSpec (peOut (fun j ↦ γω ⟨j.val, by have := j.isLt; omega⟩)) :=
  liftReflPotSlice35To41_wstate (liftReflPotSlice24To35_sub63
    (s24 (fun j ↦ γω ⟨j.val, by have := j.isLt; omega⟩)))

def pPotWrapReflCoinKPortBInPlace {Var : Type} {kOut n Wp W tPotU tPotC : ℕ}
    {peOut : BitAssignment kOut → PotExpectFn}
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut) (hW : Wp ≤ W)
    (h24 : 24 ≤ W) (v : Var) (r : QRegister (122 + W) n) (rC : QRegister (0 + kOut) n)
    (isCsel : Bool) : DynamicCircuit Var n :=
  let rSub : QRegister (122 + Wp) n := r.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le hW))
  let r24 := rSub.compose (skip17Of122Wp_ipb Wp)
  let rC0 := castZeroAddReg_ipb rC
  let dPot := if isCsel then o24.pCsel v r24 rC0 else o24.pUsel v r24 rC0
  let cP := cPackCnotAux r h24 24 le_rfl
  .seq (.circuit cP)
    (xUnloadChunkCzPairsSeqDyn v
      (fun i ↦ if hi : i < 24 then r ⟨122 + i, (packUnpack_b h24 hi).2.2.1⟩
        else r ⟨0, (packUnpack_b h24 (Nat.zero_lt_succ 23)).2.2.2.1⟩) 0
      (fun i ↦ if hi : i < 24 then
        ⟨r ⟨4, (packUnpack_b h24 hi).1⟩,
          ⟨r ⟨57 + i, (packUnpack_b h24 hi).2.1⟩, reflPackPair_ne r h24 hi⟩⟩ :: []
        else [])
      dPot 24)

attribute [local semireducible] projBit chunkXorOp in
theorem subspaceStep_pPotWrapReflCoinKPortBInPlace {Var : Type} [Fintype Var] [DecidableEq Var]
    {kOut m n Wp W tPotU tPotC : ℕ} [NeZero (2 ^ n)]
    {peOut : BitAssignment kOut → PotExpectFn}
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut)
    (hW : Wp ≤ W) (h24 : 24 ≤ W)
    (v : Var) (rW : QRegister m n) (r : QRegister (122 + W) n) (rC : QRegister (0 + kOut) n)
    (hd : r.DisjointWires rC) (isCsel : Bool)
    (st0 : BitAssignment n → BitAssignment n)
    (hValid : ∀ δ, (∀ q : Fin m, δ (rW q) = 0) →
      ValidPotBFlags (r.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le hW)))
        (packPortBSt r h24 st0 δ))
    (hOneHot : ∀ δ (b : Fin 24),
      (st0 δ (r ⟨4, by omega⟩) = 0 → st0 δ (r ⟨122 + b.val, by omega⟩) = 0) ∧
      (st0 δ (r ⟨4, by omega⟩) = 1 → st0 δ (r ⟨57 + b.val, by omega⟩) = 0))
    (hCleanHi : ∀ δ (u : Fin W), 24 ≤ u.val → (∀ q : Fin m, δ (rW q) = 0) →
      st0 δ (r ⟨122 + u.val, by omega⟩) = 0)
    (hPB0 : ∀ δ (i : Fin 24), (∀ q : Fin m, δ (rW q) = 0) →
      packPortBSt r h24 st0 δ
        (wPotBIsScreen (r.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le hW)))) = 0 →
      packPortBSt r h24 st0 δ
        (rPotBPortB (r.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le hW))) i) = 0) :
    let rSub : QRegister (122 + Wp) n := r.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le hW))
    let stP := packPortBSt r h24 st0
    let s41 := spec41Of24_ipb o24.sliceSpec
    SubspaceStep (mkKetOpW rW st0 (fun _ ↦ 0))
      (mkKetOpW rW
        (fun δ ↦ xorPortB41NotScr rSub
          (potReflPortBSt (fun γω ↦ (s41 γω).coinSwap) isCsel rSub rC stP δ))
        (potReflPortBPh0 (fun γω ↦ (s41 γω).phaseBit) isCsel rSub rC stP))
      (pPotWrapReflCoinKPortBInPlace o24 hW h24 v r rC isCsel) ∧
    (pPotWrapReflCoinKPortBInPlace o24 hW h24 v r rC isCsel).count .T =
      (if isCsel then tPotC else tPotU) ∧
    (pPotWrapReflCoinKPortBInPlace o24 hW h24 v r rC isCsel).count .TOFF = 0 := by
  intro rSub stP s41
  let rE := r.compose (QRegister.block 57 24 (by omega))
  let rN := r.compose (QRegister.block 122 24 (by omega))
  obtain ⟨hPZero, hP4, hP57⟩ := packPortBSt_props r h24 st0; obtain ⟨cKet, cT, cF, _⟩ :=
      cPackCnotAux_spec r h24 24 le_rfl
  have hdSub : rSub.DisjointWires rC := QRegister.disjoint_iff.mpr fun i j e ↦
      QRegister.disjoint_iff.mp hd _ j e
  have rNe : ∀ {a b : Fin (122 + W)}, a.val ≠ b.val → r a ≠ r b :=
    fun hne ↦ r.wires.injective.ne fun e ↦ hne (congrArg Fin.val e)
  let rOutP : ℕ → Wire n := fun i ↦ if hi : i < 24 then r ⟨122 + i, by omega⟩ else r ⟨0, by omega⟩
  let pairsP : ℕ → List (WirePair n) := fun i ↦
      if hi : i < 24 then ⟨r ⟨4, (packUnpack_b h24 hi).1⟩, ⟨r ⟨57 + i, (packUnpack_b h24 hi).2.1⟩,
      reflPackPair_ne r h24 hi⟩⟩ :: [] else []
  have hfP : ∀ i β a, czPairsParity (pairsP i) (Function.update β (rOutP (0 + i)) a) =
      czPairsParity (pairsP i) β := fun i β a ↦ by
    dsimp only [rOutP, pairsP]; rw [Nat.zero_add]; split_ifs with hi
    · exact czPairsParity_indep _ _ (fun p hp ↦ by
        rw [List.mem_singleton.mp hp]; exact ⟨rNe (by dsimp; omega), rNe (by dsimp; omega)⟩) β a
    · rfl
  have sPack1 : SubspaceStep (mkKetOpW rW st0 (fun _ ↦ 0))
      (chunkXorOp rOutP 0 (fun i β ↦ czPairsParity (pairsP i) β) hfP 24 *
        mkKetOpW rW stP (fun _ ↦ 0))
      (.circuit (Var := Var) (cPackCnotAux r h24 24 le_rfl)) := by
    refine subspaceStep_congr_out (subspaceStep_of_circuit _ _) ?_;
    rw [chunkXorOp_mkKetOpW_eq rW r h24 stP hPZero 24 le_rfl]
    apply matrix_ext_ket; intro δ
    rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · rw [bitSign_zero, one_smul, one_smul, cKet (st0 δ)]
      refine congrArg ket (funext fun w ↦ ?_)
      by_cases hwN : ∃ b : Fin 24, rN b = w
      · obtain ⟨b, rfl⟩ := hwN
        have hr : rN b = r ⟨122 + b.val, by omega⟩ := congrArg r.wires (Fin.ext rfl)
        rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ (blk24_disj r 122 57 _ _ (by omega) b),
            DynCircExt.writeReg_apply_reg, ite_eq_left b.isLt, hr]
        dsimp only [stP]; rw [hP4, hP57]
        exact (oneHot_pack_unpack_bits _ _ _ (hOneHot δ b)).1
      · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hwN]
        by_cases hwE : ∃ b : Fin 24, rE b = w
        · obtain ⟨b, rfl⟩ := hwE
          have hr : rE b = r ⟨57 + b.val, by omega⟩ := congrArg r.wires (Fin.ext rfl)
          rw [DynCircExt.writeReg_apply_reg, ite_eq_left b.isLt, hr]; exact (hP57 δ b).symm
        · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hwE]; dsimp only [stP, packPortBSt]
          rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hwN,
              DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hwE]
    · rw [Matrix.mulVec_zero]
  let r24 := rSub.compose (skip17Of122Wp_ipb Wp)
  let rC0 := castZeroAddReg_ipb rC
  let dPot := if isCsel then o24.pCsel v r24 rC0 else o24.pUsel v r24 rC0
  have hLow (c : ℕ) (hc24 : c < 105 + Wp) (hc : c < 105) : r24 ⟨c, hc24⟩ = rSub ⟨c, by omega⟩ :=
    congrArg rSub.wires (Fin.ext (by rw [val_skip17Of122Wp_ipb, ite_eq_left hc]))
  have hBlk24 (o : ℕ) (h1 : o + 24 ≤ 105 + Wp) (h2 : o + 24 ≤ 122 + Wp) (ho : o + 24 ≤ 105) :
      r24.compose (QRegister.block o 24 h1) = rSub.compose (QRegister.block o 24 h2) :=
    QRegister.ext (Function.Embedding.ext fun ⟨kv, hk⟩ ↦ hLow (o + kv) (by omega) (by omega))
  have hNucA : rPotB24NucA r24 = rPotBNucA rSub := hBlk24 9 _ _ (by decide)
  have hElecA : rPotB24ElecA r24 = rPotBElecA rSub := hBlk24 33 _ _ (by decide)
  have hPortB : rPotB24PortB r24 = rPotBPortB rSub := hBlk24 57 _ _ (by decide)
  have hScrW : wPotB24IsScreen r24 = wPotBIsScreen rSub := hLow 1 _ (by decide)
  obtain ⟨s24, tPot, fPot⟩ := o24.step_and_counts v rW r24 rC0
    (disj_of_ne fun i _ e ↦ QRegister.disjoint_iff.mp hdSub (skip17Of122Wp_ipb Wp i) _ e)
    isCsel stP
    (fun δ hz ↦ by
      have hv := hValid δ hz
      dsimp only [ValidPotBFlags24, wPotB24IsPot, wPotB24IsScreen, wPotB24IsNN]
      rwa [hLow 2 _ (by decide), hLow 1 _ (by decide), hLow 4 _ (by decide)])
    (fun δ u hz ↦ by
      have _ := u.isLt
      rw [show rPotBWork24 r24 u = r ⟨122 + u.val, by omega⟩ from
        Eq.trans (b := rPotBWork rSub u)
          (congrArg rSub.wires (Fin.ext (by
            change (skip17Of122Wp_ipb Wp ⟨105 + u.val, _⟩).val = 122 + u.val
            rw [val_skip17Of122Wp_ipb]
            dsimp only
            split_ifs <;> omega)))
          (congrArg r.wires (Fin.ext (by
            dsimp [rSub, rPotBWork, QRegister.compose, QRegister.block, Fin.natAddEmb,
              Fin.natAdd, DFunLike.coe, -Function.Embedding.toFun_eq_coe]
            omega)))]
      by_cases hu24 : u.val < 24
      · exact hPZero δ ⟨u.val, hu24⟩
      · dsimp only [stP, packPortBSt]
        rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _
              (blk24_not_mem r 122 _ _ (by omega) (by omega)),
            DynCircExt.writeReg_apply_of_not_mem _ _ _ _
              (blk24_not_mem r 57 _ _ (by omega) (by omega))]
        exact hCleanHi δ ⟨u.val, by omega⟩ (Nat.le_of_not_lt hu24) hz)
    (fun δ i hz hs0 ↦ by
      rw [hScrW] at hs0
      simpa only [congrArg (fun reg ↦ reg i) hPortB] using hPB0 δ i hz hs0)
  have hTakeC (δ : BitAssignment n) :
      take24Of35_sub63 (take35Of41_wstate (fun k ↦ stP δ (rPotBCoin41 rSub k))) =
        fun j ↦ stP δ (rPotBCoin24 r24 j) :=
    funext fun ⟨jv, hj⟩ ↦ (congrArg (stP δ) (hLow (81 + jv) (by omega) (by omega))).symm
  have sPot : SubspaceStep (mkKetOpW rW stP (fun _ ↦ 0))
      (mkKetOpW rW (fun δ ↦ xorPortB41NotScr rSub
        (potReflPortBSt (fun γω ↦ (s41 γω).coinSwap) isCsel rSub rC stP δ))
        (potReflPortBPh0 (fun γω ↦ (s41 γω).phaseBit) isCsel rSub rC stP)) dPot := by
    refine subspaceStep_congr_out s24
      (congrArg₂ (mkKetOpW rW) (funext fun δ ↦ ?_) (funext fun δ ↦ ?_))
    · have hXor : xorPortB24NotScr r24 = xorPortB41NotScr rSub := by
        funext β
        unfold xorPortB24NotScr xorPortB41NotScr
        rw [hPortB, hScrW, hNucA]
      rw [congrFun hXor]
      apply congrArg (xorPortB41NotScr rSub)
      have hGate : potB24GateActive isCsel r24 (stP δ) = potBGateActive isCsel rSub (stP δ) := by
        dsimp only [potB24GateActive, potBGateActive, wPotB24LocQ, wPotB24IsPot, wPotBLocQ,
          wPotBIsPot]
        rw [hLow 0 _ (by decide), hLow 2 _ (by decide)]
      have hCoinEq : potOraclePortB24CoinEval ((o24.sliceSpec (fun j ↦ stP δ (rC0 j))).coinSwap)
          r24 (stP δ) = take24Of35_sub63 (take35Of41_wstate
            (potOraclePortBCoinEval ((s41 (fun j ↦ stP δ (rC j))).coinSwap) rSub (stP δ))) := by
        funext j
        dsimp only [take24Of35_sub63, take35Of41_wstate, potOraclePortBCoinEval,
          potOraclePortB24CoinEval, s41, spec41Of24_ipb, liftReflPotSlice35To41_wstate,
          liftReflPotSlice24To35_sub63, put35In41_wstate, put24In35_sub63, wPotB24IsScreen,
          wPotB24IsNN, wPotB24Sp1B0, wPotB24Sp1B1, wPotB24Sp2B0, wPotB24Sp2B1, wPotBIsScreen,
          wPotBIsNN, wPotBSp1B0, wPotBSp1B1, wPotBSp2B0, wPotBSp2B1]
        simp only [Nat.lt_trans j.isLt (by decide : 24 < 35), j.isLt, ↓reduceDIte,
          hLow 1 _ (by decide), hLow 4 _ (by decide), hLow 5 _ (by decide), hLow 6 _ (by decide),
          hLow 7 _ (by decide), hLow 8 _ (by decide), hNucA, hElecA, hPortB, hTakeC δ, Fin.eta]
        rfl
      dsimp only [potReflPortBSt24, potReflPortBSt]
      rw [hGate]
      split_ifs
      · funext w
        rw [hCoinEq]
        by_cases hm41 : ∃ i : Fin 41, rPotBCoin41 rSub i = w
        · obtain ⟨i, rfl⟩ := hm41
          rw [DynCircExt.writeReg_apply_reg]
          by_cases hi : i.val < 24
          · rw [← show rPotBCoin24 r24 ⟨i.val, hi⟩ = rPotBCoin41 rSub i from
                hLow (81 + i.val) (by omega) (by omega), DynCircExt.writeReg_apply_reg]
            rfl
          · rw [DynCircExt.writeReg_apply_of_not_mem (stP δ) (rPotBCoin24 r24) _ _
              (fun ⟨⟨jv, hj⟩, he⟩ ↦ hi (by
                have hjEq : rPotBCoin24 r24 ⟨jv, hj⟩ = rPotBCoin41 rSub ⟨jv, by omega⟩ :=
                  hLow (81 + jv) (by omega) (by omega)
                simpa only [← congrArg Fin.val ((rPotBCoin41 rSub).wires.injective
                  (hjEq.symm.trans he))] using hj))]
            dsimp only [potOraclePortBCoinEval, s41, spec41Of24_ipb, liftReflPotSlice35To41_wstate,
              liftReflPotSlice24To35_sub63, put35In41_wstate, put24In35_sub63, take35Of41_wstate]
            split_ifs <;> rfl
        · rw [DynCircExt.writeReg_apply_of_not_mem _ (rPotBCoin41 rSub) _ w hm41,
            DynCircExt.writeReg_apply_of_not_mem _ (rPotBCoin24 r24) _ w
              (fun ⟨⟨jv, hj⟩, he⟩ ↦ hm41 ⟨⟨jv, by omega⟩,
                (hLow (81 + jv) (by omega) (by omega)).symm.trans he⟩)]
      · rfl
    · dsimp only [potReflPortBPh0_24, potReflPortBPh0, potOraclePortB24BitEval,
        potOraclePortBBitEval, s41, spec41Of24_ipb, liftReflPotSlice35To41_wstate,
        liftReflPotSlice24To35_sub63, wPotB24LocQ, wPotB24IsPot, wPotB24IsScreen, wPotB24IsNN,
        wPotB24Sp1B0, wPotB24Sp1B1, wPotB24Sp2B0, wPotB24Sp2B1, wPotBLocQ, wPotBIsPot,
        wPotBIsScreen, wPotBIsNN, wPotBSp1B0, wPotBSp1B1, wPotBSp2B0, wPotBSp2B1]
      simp only [hLow 0 _ (by decide), hLow 2 _ (by decide), hLow 1 _ (by decide),
        hLow 4 _ (by decide), hLow 5 _ (by decide), hLow 6 _ (by decide), hLow 7 _ (by decide),
        hLow 8 _ (by decide), hNucA, hElecA, hPortB, hTakeC δ]
      rfl
  have sX := subspaceStep_xUnloadChunkCzPairsSeqDyn v rOutP 0 pairsP
    (fun i β ↦ czPairsParity (pairsP i) β) hfP (fun _ _ ↦ rfl) dPot
    (mkKetOpW rW stP (fun _ ↦ 0))
    (mkKetOpW rW
      (fun δ ↦ xorPortB41NotScr rSub
        (potReflPortBSt (fun γω ↦ (s41 γω).coinSwap) isCsel rSub rC stP δ))
      (potReflPortBPh0 (fun γω ↦ (s41 γω).phaseBit) isCsel rSub rC stP))
    sPot 24
    (fun a ha b hb hab ↦ by
      dsimp only [rOutP]; simp only [Nat.zero_add, ha, hb, ↓reduceDIte]
      exact rNe (by dsimp; omega))
    (fun i hi ↦ by
      dsimp only [rOutP]; simp only [Nat.zero_add, hi, ↓reduceDIte]
      apply matrix_ext_ket; intro δ
      rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]; split_ifs
      · rw [Matrix.mulVec_smul]; dsimp only [projBit]
        rw [PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left]
        intro q; fin_cases q; exact hPZero δ ⟨i, hi⟩
      · exact Matrix.mulVec_zero _)
  let tcX :=
      count_xUnloadChunkCzPairsSeqDyn v rOutP 0 pairsP dPot 24; refine ⟨subspaceStep_seq_portB
      sPack1 sX, ?_, ?_⟩
  · dsimp only [pPotWrapReflCoinKPortBInPlace, DynamicCircuit.count]
    rw [cT, zero_add, tcX.1]; exact tPot
  · dsimp only [pPotWrapReflCoinKPortBInPlace, DynamicCircuit.count]
    rw [cF, zero_add, tcX.2]; exact fPot

abbrev pPotWrapReflPortB151InPlace {Var : Type} {kOut n Wp tPotU tPotC : ℕ}
    {peOut : BitAssignment kOut → PotExpectFn}
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut) (hWp : Wp ≤ 738)
    (v : Var) (rTot : QRegister dLayout n) (rCoin : QRegister (0 + kOut) dLayout)
    (isCsel : Bool) : DynamicCircuit Var n :=
    pPotWrapReflCoinKPortBInPlace o24 (Nat.le_max_left Wp 24)
    (Nat.le_max_right Wp 24) v (rTot.compose (rPotZeroNEremPortB151 (max Wp 24)
    (maxWp24_le_738 hWp))) (rTot.compose rCoin) isCsel
theorem dynWires_pPotWrapReflPortB151InPlace_skip17 {Var : Type} {kOut n Wp tPotU tPotC : ℕ}
    {S : Wire n → Prop} {peOut : BitAssignment kOut → PotExpectFn}
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut) (hWp : Wp ≤ 738)
    (v : Var) (rTot : QRegister dLayout n) (rCoin : QRegister (0 + kOut) dLayout) (isCsel : Bool)
    (hrB : ∀ j : Fin (122 + max Wp 24), (j.val < 105 ∨ 122 ≤ j.val) →
    S (rTot (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp) j)))
    (hrC : ∀ j : Fin (0 + kOut), S (rTot (rCoin j))) :
    DynWires S (pPotWrapReflPortB151InPlace o24 hWp v rTot rCoin isCsel) := by
  let rB := rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
  let rC := rTot.compose rCoin
  let rSub := rB.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le (Nat.le_max_left Wp 24)))
  obtain ⟨wBC, wBU⟩ := o24.dynWires S v (rSub.compose (skip17Of122Wp_ipb Wp))
    (castZeroAddReg_ipb rC)
    (fun i ↦ hrB ⟨0 + (skip17Of122Wp_ipb Wp i).val, by
      have _ := (skip17Of122Wp_ipb Wp i).isLt
      omega⟩ (by
      dsimp
      rw [val_skip17Of122Wp_ipb]
      split_ifs <;> omega))
    (fun _ ↦ hrC _)
  let dPot :=
      if isCsel then o24.pCsel v (rSub.compose (skip17Of122Wp_ipb Wp)) (castZeroAddReg_ipb rC)
  else
    o24.pUsel v (rSub.compose (skip17Of122Wp_ipb Wp)) (castZeroAddReg_ipb rC)
  have wP : DynWires S dPot := by dsimp only [dPot]; cases isCsel <;> [exact wBU; exact wBC]
  exact ⟨circWires_cPackCnotAux_skip17_sub63 rB (Nat.le_max_right Wp 24) hrB 24 le_rfl,
    PhotochemistrySolution.PotOraclePortB.dynWires_xUnloadChunkCzPairsSeqDyn v
      (fun i ↦ if hi : i < 24 then
        rB ⟨122 + i, (packUnpack_b (Nat.le_max_right Wp 24) hi).2.2.1⟩
        else rB ⟨0, (packUnpack_b (Nat.le_max_right Wp 24) (Nat.zero_lt_succ 23)).2.2.2.1⟩) 0
      (fun i ↦ if hi : i < 24 then
        ⟨rB ⟨4, (packUnpack_b (Nat.le_max_right Wp 24) hi).1⟩,
          ⟨rB ⟨57 + i, (packUnpack_b (Nat.le_max_right Wp 24) hi).2.1⟩,
            reflPackPair_ne rB (Nat.le_max_right Wp 24) hi⟩⟩ :: []
        else [])
      dPot wP 24
      (fun _ _ ↦ by split_ifs <;> exact hrB _ (by dsimp; omega))
      (fun _ _ p hp ↦ by
        split_ifs at hp; rw [List.mem_singleton.mp hp]
        exact ⟨hrB _ (Or.inl (by dsimp; omega)), hrB _ (Or.inl (by dsimp; omega))⟩)⟩

def clampScreenPortB {n : ℕ} (rTot : QRegister dLayout n) (δ : BitAssignment n) :
    BitAssignment n :=
    DynCircExt.writeReg δ (rTot.compose ⟨rBufHi rElecLayout, rBufHi_inj rElecLayout⟩)
    (fun b ↦
    if δ (rTot (wPotIsScreen rPot0Layout)) == 0 then 0 else δ (rTot (rBufHi rElecLayout b)))
theorem clampScreenPortB_apply {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    (∀ b : Fin 24, clampScreenPortB rTot β (rTot (rBufHi rElecLayout b)) =
    if β (rTot (wPotIsScreen rPot0Layout)) == 0 then 0 else β (rTot (rBufHi rElecLayout b))) ∧
    (∀ w : Wire n, (∀ b : Fin 24, w ≠ rTot (rBufHi rElecLayout b)) → clampScreenPortB rTot β w =
    β w) := by
  let rEB : QRegister 24 n := rTot.compose ⟨rBufHi rElecLayout, rBufHi_inj rElecLayout⟩
  exact ⟨fun b ↦ DynCircExt.writeReg_apply_reg β rEB _ b, fun w hE ↦
      DynCircExt.writeReg_apply_of_not_mem β rEB _ w (fun ⟨b, hb⟩ ↦ hE b hb.symm)⟩

def clampPotBInPlace {n : ℕ} (rTot : QRegister dLayout n) (δ : BitAssignment n) :
    BitAssignment n := clampScreenPortB rTot (clampPotBRefl rTot δ)
theorem routedKet_screenZero_elecHiZero {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {α : BitAssignment dLayout} (hScr : CleanScr α) (c : Fin (2 ^ 41)) (z : BitAssignment 41)
    (b : Fin 24) : routedKet decodeCoin α c z (wPotIsScreen rPot0Layout) = 0 →
    routedKet decodeCoin α c z (rBufHi rElecLayout b) = 0 := by
  let δ₁ := routedStage1 decodeCoin α c z
  let δ₂ := routedStage2 decodeCoin α c z
  obtain ⟨_, hKeepE, hVE, hOut, _, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin)
    hScr c z
  have hScrKeep : routedKet decodeCoin α c z (wPotIsScreen rPot0Layout) =
      δ₁ (wPotIsScreen rPot0Layout) :=
    hOut (wPotIsScreen rPot0Layout) (.inl (by rw [val_wPotFlags_rPot0Layout.1]; omega))
  rw [hScrKeep]
  have hOut1 : ∀ j : Fin 40, δ₁ (rOut40Layout j) = outMaskBits40 (decodeCoin c) j := fun j ↦
      DynCircExt.writeReg_apply_reg _ rOut40Layout _ j
  have checkSec : ∀ (hN1 hN2 : Bool) (n1 n2 : ℕ) (hE1 hE2 : Bool) (e1 e2 : ℕ)
      (isScreen isPot isKin isNN : Bool) (sp1 aux2 : ℕ), n1 < 64 → n2 < 64 → e1 < 256 → e2 < 256 →
      (isScreen = false → hE2 = false) → zeroNEremOutMask (decodeCoin c) =
      packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2 →
      δ₁ (wPotIsScreen rPot0Layout) = 0 → routedKet decodeCoin α c z (rBufHi rElecLayout b) =
      0 := by
    intro hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2
      ln1 ln2 le1 le2 impE heq h0
    have F := packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2
      isScreen isPot isKin isNN sp1 aux2 ln1 ln2 le1 le2 δ₁
      (fun j ↦ (hOut1 j).trans (by
        dsimp only [outMaskBits40]
        rw [heq]))
    have hsF : isScreen = false := by
      cases isScreen
      · rfl
      · exact absurd (F.2.2.2.2.2.2.2.2.1.symm.trans h0) one_ne_zero
    have he20 : δ₂ (rRawHas2 rElecLayout) = 0 :=
      (hKeepE _).trans (F.2.2.2.2.2.1.trans (by simp [impE hsF]))
    have heCond : ¬ (routerHas2Eff rElecLayout δ₂ = 1 ∧ routerIdxMaxVal rElecLayout δ₂ < 187) := by
      simp [routerHas2Eff, he20]
    dsimp only [routedKet];
    rw [(routerSwapBits_spec rElecLayout hVE).2.1 b, dite_eq_right heCond]
  cases hc : decodeCoin c with
  | idle =>
      exact checkSec false false 0 0 false false 0 0 false false false false 0 0
        (by omega) (by omega) (by omega) (by omega) (fun _ ↦ rfl) (hc ▸ rfl)
  | ee n1 e1 e2 =>
      exact checkSec true false n1.val 0 true true e1.val e2.val true true false false
        (nucSpecies n1).val 0 (by omega) (by omega) (by omega) (by omega) (by simp) (hc ▸ rfl)
  | nn n1 n2 e1 =>
      exact checkSec true true n1.val n2.val true false e1.val 0 true true false true
        (nucSpecies n1).val (nucSpecies n2).val (by omega) (by omega) (by omega) (by omega)
        (by simp) (hc ▸ rfl)
  | en n1 e1 =>
      exact checkSec true false n1.val 0 true false e1.val 0 false true false false
        (nucSpecies n1).val 0 (by omega) (by omega) (by omega) (by omega) (fun _ ↦ rfl) (hc ▸ rfl)
  | kin i ax =>
      have _ := i.isLt
      by_cases hi : i.val < 47
      · exact checkSec true false i.val 0 false false 0 0 false false true false 0 ax.val
          (by omega) (by omega) (by omega) (by omega) (fun _ ↦ rfl)
          (hc ▸ by simp [zeroNEremOutMask, hi])
      · exact checkSec false false 0 0 true false (i.val - 47) 0 false false true false 0 ax.val
          (by omega) (by omega) (by omega) (by omega) (fun _ ↦ rfl)
          (hc ▸ by simp [zeroNEremOutMask, hi])

theorem routed_clampPotBInPlace_fix_wstate {decode : Fin (2 ^ 41) → ZeroNEremSector} {n : ℕ}
    (rTot : QRegister dLayout n) (η : BitAssignment n)
    (hrk : IsRoutedKet decode (fun i ↦ η (rTot i))) : clampPotBInPlace rTot η = η := by
  have hFixR := routed_clampPotBRefl_fix_wstate rTot η hrk; unfold clampPotBInPlace; rw [hFixR]
  rcases hrk with ⟨α, c0, z0, hScr, heq⟩
  obtain ⟨cE, cO⟩ := clampScreenPortB_apply rTot η; funext w
  by_cases hwE : ∃ b : Fin 24, w = rTot (rBufHi rElecLayout b)
  · obtain ⟨b, rfl⟩ := hwE; rw [cE b]
    by_cases hs0 : (η (rTot (wPotIsScreen rPot0Layout)) == 0) = true
    · rw [ite_eq_left hs0];
      have h0 : routedKet decode α c0 z0 (wPotIsScreen rPot0Layout) = 0 :=
          (congrFun heq (wPotIsScreen rPot0Layout)).symm.trans (beq_iff_eq.mp hs0); exact
          ((congrFun heq (rBufHi rElecLayout b)).trans (routedKet_screenZero_elecHiZero hScr c0 z0
          b h0)).symm
    · exact ite_eq_right hs0
  · exact cO w (fun b e ↦ hwE ⟨b, e⟩)

attribute [local irreducible] clampOneHot packPortBSt in
theorem clampPotBInPlace_props_portB151 {n Wp : ℕ} (hWp : Wp ≤ 738) (rTot : QRegister dLayout n) :
    let hMax := maxWp24_le_738 hWp
    let rW := rTot.compose rClean714Layout
    let rB := rTot.compose (rPotZeroNEremPortB151 (max Wp 24) hMax)
    let rSub := rB.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le (Nat.le_max_left Wp 24)))
    let st0 := clampPotBInPlace rTot
    (∀ δ, ValidPotBFlags rSub (packPortBSt rB (Nat.le_max_right Wp 24) st0 δ)) ∧
    (∀ δ (b : Fin 24),
      (st0 δ (rB ⟨4, by omega⟩) = 0 → st0 δ (rB ⟨122 + b.val, by omega⟩) = 0) ∧
      (st0 δ (rB ⟨4, by omega⟩) = 1 → st0 δ (rB ⟨57 + b.val, by omega⟩) = 0)) ∧
    (∀ δ (u : Fin (max Wp 24)), 24 ≤ u.val → (∀ q : Fin 714, δ (rW q) = 0) →
      st0 δ (rB ⟨122 + u.val, by omega⟩) = 0) ∧
    (∀ δ (i : Fin 24),
      packPortBSt rB (Nat.le_max_right Wp 24) st0 δ (wPotBIsScreen rSub) = 0 →
      packPortBSt rB (Nat.le_max_right Wp 24) st0 δ (rPotBPortB rSub i) = 0) := by
  intro hMax rW rB rSub st0;
  let stR := clampPotBRefl rTot; obtain ⟨hValidR, hOneHotR, hCleanHiR⟩ :=
      clampPotBRefl_props_portB151 hWp rTot; obtain ⟨_, hB57, _, _⟩ := portB151_reg_links hWp rTot
  have hBNot57 : ∀ (idx : Fin (122 + max Wp 24)), (idx.val < 57 ∨ 81 ≤ idx.val) →
      ∀ b : Fin 24, rB idx ≠ rTot (rBufHi rElecLayout b) := fun idx hidx b e ↦ by
    rw [← hB57 b] at e; have hv := congrArg Fin.val (rB.wires.injective e)
    have := b.isLt; dsimp only at hv; omega
  have hSt0Out : ∀ (δ : BitAssignment n) (idx : Fin (122 + max Wp 24)), (idx.val < 57 ∨ 81 ≤
      idx.val) → st0 δ (rB idx) = stR δ (rB idx) := fun δ idx hidx ↦
      (clampScreenPortB_apply rTot (stR δ)).2 (rB idx) (hBNot57 idx hidx)
  have hPackKeep : ∀ (f : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      (c : ℕ) (hc : c < 33),
      packPortBSt rB (Nat.le_max_right Wp 24) f δ (rSub ⟨c, by omega⟩) =
        f δ (rB ⟨c, by omega⟩) := fun f δ c hc ↦ by
    have hr : rSub ⟨c, by omega⟩ = rB ⟨c, by omega⟩ :=
      congrArg rB.wires (Fin.ext (Nat.zero_add c))
    rw [hr]; unfold packPortBSt
    rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem rB 122 _ c (by omega)
        (by omega)),
        DynCircExt.writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem rB 57 _ c (by omega)
            (by omega))]
  have hValid0 : ∀ δ, ValidPotBFlags rSub (packPortBSt rB (Nat.le_max_right Wp 24) st0 δ) := fun δ ↦
      by
    have hv := hValidR δ; dsimp only [ValidPotBFlags, wPotBIsPot, wPotBIsScreen, wPotBIsNN] at hv ⊢
    rw [hPackKeep st0 δ 2 (by omega), hPackKeep st0 δ 1 (by omega), hPackKeep st0 δ 4 (by omega),
        hSt0Out δ ⟨2, by omega⟩ (Or.inl (by dsimp; omega)),
        hSt0Out δ ⟨1, by omega⟩ (Or.inl (by dsimp; omega)),
        hSt0Out δ ⟨4, by omega⟩ (Or.inl (by dsimp; omega)),
        ← hPackKeep stR δ 2 (by omega), ← hPackKeep stR δ 1 (by omega),
            ← hPackKeep stR δ 4 (by omega)]
    exact hv
  have hOneHot0 : ∀ δ (b : Fin 24),
      (st0 δ (rB ⟨4, by omega⟩) = 0 → st0 δ (rB ⟨122 + b.val, by omega⟩) = 0) ∧
      (st0 δ (rB ⟨4, by omega⟩) = 1 → st0 δ (rB ⟨57 + b.val, by omega⟩) = 0) := fun δ b ↦ by
    refine ⟨fun h40 ↦ ?_, fun h41 ↦ ?_⟩
    · rw [hSt0Out δ ⟨4, by omega⟩ (Or.inl (by dsimp; omega))] at h40
      rw [hSt0Out δ ⟨122 + b.val, by omega⟩ (Or.inr (by dsimp; omega))]
      exact (hOneHotR δ b).1 h40
    · rw [hSt0Out δ ⟨4, by omega⟩ (Or.inl (by dsimp; omega))] at h41
      have hE0 : stR δ (rTot (rBufHi rElecLayout b)) = 0 := by
        rw [← hB57 b]; exact (hOneHotR δ b).2 h41
      rw [hB57 b]; change clampScreenPortB rTot (stR δ) (rTot (rBufHi rElecLayout b)) = 0;
      rw [(clampScreenPortB_apply rTot (stR δ)).1 b, hE0]
      split_ifs <;> rfl
  refine ⟨hValid0, hOneHot0, fun δ u hu24 hz ↦ ?_, fun δ i hs0 ↦ ?_⟩
  · rw [hSt0Out δ ⟨122 + u.val, by omega⟩ (Or.inr (by dsimp; omega))]
    exact hCleanHiR δ u hu24 hz
  · have hNN0_pack : packPortBSt rB (Nat.le_max_right Wp 24) st0 δ (wPotBIsNN rSub) = 0 :=
      (hValid0 δ).2 hs0
    have h40 : st0 δ (rB ⟨4, by omega⟩) = 0 :=
      (hPackKeep st0 δ 4 (by omega)).symm.trans hNN0_pack
    have h122_0 : st0 δ (rB ⟨122 + i.val, by omega⟩) = 0 := (hOneHot0 δ i).1 h40
    have hB1 : rB ⟨1, by omega⟩ = rTot (wPotIsScreen rPot0Layout) := by
      refine congrArg rTot.wires (Fin.ext ?_)
      change (potZeroNEremPortB151WireFn (max Wp 24) hMax ⟨1, by omega⟩).val =
        (wPotIsScreen rPot0Layout).val
      rw [val_potZeroNEremPortB151WireFn hMax, val_wPotFlags_rPot0Layout.1]; dsimp
    have hScrR0 : stR δ (rTot (wPotIsScreen rPot0Layout)) = 0 := by
      rw [← hB1, ← hSt0Out δ ⟨1, by omega⟩ (Or.inl (by dsimp; omega)),
          ← hPackKeep st0 δ 1 (by omega)]
      exact hs0
    have h57_0 : st0 δ (rB ⟨57 + i.val, by omega⟩) = 0 := by
      rw [hB57 i]; change clampScreenPortB rTot (stR δ) (rTot (rBufHi rElecLayout i)) = 0;
      rw [(clampScreenPortB_apply rTot (stR δ)).1 i, hScrR0]; rfl
    have hPB_eq : rPotBPortB rSub i = rB ⟨57 + i.val, by omega⟩ :=
      congrArg rB.wires (Fin.ext (Nat.zero_add (57 + i.val)))
    obtain ⟨_, _, hP57⟩ :=
        packPortBSt_props rB (Nat.le_max_right Wp 24) st0; rw [hPB_eq, hP57 δ i, h57_0, h122_0,
        zero_add]
attribute [local irreducible] uCopyAll3AlwaysLoMux_wstate copyAll3AlwaysLoBits_wstate clampOneHot
    in
theorem routed_scrubNuc3_copyAll3Lo_zeroSwap_wstate
    {w1 wWork n : ℕ} [NeZero (2 ^ n)]
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (hwLo : 232 ≤ wWork) (hwHi : wWork ≤ 886)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (rTot : QRegister dLayout n) (isCsel : Bool)
    (X₁ : Operator (2 ^ n))
    (hAbsX₁ : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁) :
    let rTot'' := rTot.compose (rPermPotNuc3 wWork hwLo hwHi)
    let Wnh := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))
    let uKin :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    let M0 := mkKetOpW (rTot''.compose rClean714Layout) (clampPotBInPlace rTot) (fun _ ↦ 0)
    M0 * ((cScrubNucFlags3 rTot).eval.1 *
      ((uCopyAll3AlwaysLoMux_wstate rTot).1 * ((uZeroSwapNE rTot).1 * (uKin.1 * (Wnh.1 * X₁))))) =
      (cScrubNucFlags3 rTot).eval.1 *
        ((uCopyAll3AlwaysLoMux_wstate rTot).1 * ((uZeroSwapNE rTot).1 * (uKin.1 * (Wnh.1 * X₁))))
            := by
  intro rTot'' Wnh uKin M0
  have hPot0Ge : ∀ i : Fin 146, 5616 ≤ (rPot0Layout i).val := fun i ↦ by
    have _ := i.isLt;
    have hv : (rPot0Layout i).val = (potZeroNEremWireFn 0 pot0_le_690 i).val := rfl
    rw [hv, val_potZeroNEremWireFn pot0_le_690]; split_ifs <;> omega
  refine mkKetOpW_mul_eq_of_inKetPred_wstate (rTot''.compose rClean714Layout)
      (clampPotBInPlace rTot) _ fun ξ ↦ ?_
  rw [← Matrix.mulVec_mulVec (ket ξ), ← Matrix.mulVec_mulVec (ket ξ)
      (uCopyAll3AlwaysLoMux_wstate rTot).1, ← Matrix.mulVec_mulVec (ket ξ) (uZeroSwapNE rTot).1]
  have hZS : inKetPred
      (fun η₁ ↦ ∃ η : BitAssignment n,
        IsRoutedKet decode (fun i ↦ η (rTot i)) ∧
        η₁ = DynCircExt.writeReg η rTot (zeroSwapBitsLayout (fun u ↦ η (rTot u))))
      ((uZeroSwapNE rTot).1.mulVec ((uKin.1 * (Wnh.1 * X₁)).mulVec (ket ξ))) :=
    inKetPred_mulVec (uZeroSwapNE rTot).1 (fun η hrk ↦ by
      rw [uZeroSwapNE_mulVec_ket rTot η]
      exact inKetPred_ket ⟨η, hrk, rfl⟩)
        (routed_uKin_inKetPred_wstate o1 rTot isCsel X₁ hAbsX₁ ξ)
  refine inKetPred_mulVec
    (P := fun β ↦ NucFlags3Rel rTot β ∧ clampPotBInPlace rTot β = β ∧
      ∀ q : Fin 714, β (((rTot.compose rPermPot103).compose rClean714Layout) q) = 0)
    (cScrubNucFlags3 rTot).eval.1 (fun β ⟨hRelβ, hClpβ, hZ714β⟩ ↦ ?_)
    (inKetPred_mulVec (uCopyAll3AlwaysLoMux_wstate rTot).1 (fun η₁ ⟨η, hrk, hη₁⟩ ↦ ?_) hZS)
  · rw [cScrubNucFlags3_mulVec_ket rTot β]
    set δ := nucFlags3XorBits rTot β
    obtain ⟨hz0, hz1, hz15⟩ := nucFlags3XorBits_zero_targets rTot hRelβ
    have nePair {a b : Wire dLayout} (hne : a.val ≠ b.val) : rTot a ≠ rTot b :=
      fun e ↦ hne (congrArg Fin.val (rTot.wires.injective e))
    refine inKetPred_ket ⟨fun q ↦ ?_, ?_⟩
    · set y := rPermPot103 (rClean714Layout q)
      have hRng := val_rPermPot103_rClean714Layout_rng q
      have hSwEq (t : Wire dLayout) {tv yv : ℕ} (hy : y.val = yv) (ht : t.val = tv)
          (hc : yv = 5715 + wWork ∧ tv = 5715 ∨ yv = 5716 + wWork ∧ tv = 5716 ∨
            yv = 5717 + wWork ∧ tv = 5730) :
          rSwapNucFlags3Top wWork hwLo hwHi y = t := Fin.ext (by
        rw [val_rSwapNucFlags3Top, hy, ht]
        unfold swapNucFlags3TopVal
        rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> split_ifs <;> omega)
      change δ (rTot (rSwapNucFlags3Top wWork hwLo hwHi y)) = 0
      by_cases hy0 : y.val = 5715 + wWork
      · rw [hSwEq wOut0 hy0 val_wOut0 (Or.inl ⟨rfl, rfl⟩)]
        exact hz0
      · by_cases hy1 : y.val = 5716 + wWork
        · rw [hSwEq wOut1 hy1 val_wOut1 (Or.inr (Or.inl ⟨rfl, rfl⟩))]
          exact hz1
        · by_cases hy15 : y.val = 5717 + wWork
          · rw [hSwEq wOut15 hy15 val_wOut15 (Or.inr (Or.inr ⟨rfl, rfl⟩))]
            exact hz15
          · have hyNe : y.val ≠ 5715 ∧ y.val ≠ 5716 ∧ y.val ≠ 5730 := by
              rcases hRng with h | h | h <;> omega
            rw [rSwapNucFlags3Top_fix hwLo hwHi y ⟨hyNe.1, hyNe.2.1, hyNe.2.2, hy0, hy1, hy15⟩]
            exact (nucFlags3XorBits_of_ne rTot β (nePair (val_wOut0 ▸ hyNe.1))
              (nePair (val_wOut1 ▸ hyNe.2.1)) (nePair (val_wOut15 ▸ hyNe.2.2))).trans (hZ714β q)
    · have hReflOut : ∀ {u : Wire dLayout}, u.val ≠ 5715 → u.val ≠ 5716 → u.val ≠ 5730 →
          clampPotBRefl rTot δ (rTot u) = clampPotBRefl rTot β (rTot u) :=
        fun {u} h0 h1 h15 ↦ by
        rw [congrFun (clampPotBRefl_nucFlags3XorBits rTot β) (rTot u),
            ite_eq_right (nePair (val_wOut0 ▸ h0)), ite_eq_right (nePair (val_wOut1 ▸ h1)),
            ite_eq_right (nePair (val_wOut15 ▸ h15))]
      obtain ⟨hvS, _, _⟩ := val_wPotFlags_rPot0Layout
      obtain ⟨sE1, sO1⟩ := clampScreenPortB_apply rTot (clampPotBRefl rTot δ)
      obtain ⟨sE2, sO2⟩ := clampScreenPortB_apply rTot (clampPotBRefl rTot β)
      funext w
      by_cases hwE : ∃ b : Fin 24, w = rTot (rBufHi rElecLayout b)
      · obtain ⟨b, rfl⟩ := hwE
        have hb := val_bufHi_elec b
        have _ := b.isLt
        change clampScreenPortB rTot (clampPotBRefl rTot δ) _ = _
        rw [sE1 b, hReflOut (by omega) (by omega) (by omega),
            hReflOut (by omega) (by omega) (by omega), ← sE2 b]
        exact (congrFun hClpβ _).trans (nucFlags3XorBits_of_ne rTot β
          (nePair (val_wOut0 ▸ by omega)) (nePair (val_wOut1 ▸ by omega))
          (nePair (val_wOut15 ▸ by omega))).symm
      · change clampScreenPortB rTot (clampPotBRefl rTot δ) w = δ w
        rw [sO1 w (fun b e ↦ hwE ⟨b, e⟩), congrFun (clampPotBRefl_nucFlags3XorBits rTot β) w]
        split_ifs with c0 c1 c15
        · exact congrArg δ c0.symm
        · exact congrArg δ c1.symm
        · exact congrArg δ c15.symm
        · exact (sO2 w (fun b e ↦ hwE ⟨b, e⟩)).symm.trans
            ((congrFun hClpβ w).trans (nucFlags3XorBits_of_ne rTot β c0 c1 c15).symm)
  · subst hη₁
    let η₁ := DynCircExt.writeReg η rTot (zeroSwapBitsLayout (fun u ↦ η (rTot u)))
    rw [uCopyAll3AlwaysLoMux_mulVec_ket_wstate rTot η₁]
    set β := copyAll3AlwaysLoBits_wstate rTot η₁
    have hKeep : ∀ u : Wire dLayout, 5616 ≤ u.val → ¬ IsZeroSwapWireLayout u → β (rTot u) =
        η (rTot u) := fun u hu hnz ↦
        (copyAll3AlwaysLoBits_of_val_ge_5616_wstate rTot η₁ u hu).trans
        ((DynCircExt.writeReg_apply_reg η rTot _ u).trans (zeroSwapBitsLayout_other (fun v ↦
        η (rTot v)) hnz))
    have nZS_scr : ¬ IsZeroSwapWireLayout (wPotIsScreen rPot0Layout) := by
      unfold IsZeroSwapWireLayout; rw [val_wPotFlags_rPot0Layout.1]; omega
    have nZS_pot : ¬ IsZeroSwapWireLayout (wPotIsPot rPot0Layout) := by
      unfold IsZeroSwapWireLayout; rw [val_wPotFlags_rPot0Layout.2.1]; omega
    have nZS_nn : ¬ IsZeroSwapWireLayout (wPotIsNN rPot0Layout) := by
      unfold IsZeroSwapWireLayout; rw [val_wPotFlags_rPot0Layout.2.2]; omega
    obtain ⟨r0, r1, r15⟩ := routed_nucFlags3Rel_wstate rTot η hrk
    have hKO {u : Wire dLayout} {v : ℕ} (hv : u.val = v) (hu : 5715 ≤ v ∧ v < 5755) :
        β (rTot u) = η (rTot u) :=
      hKeep u (by omega) (by
        unfold IsZeroSwapWireLayout
        omega)
    have hBNZ (b : Fin 24) :
        (5616 ≤ (rBufHi rNucLayout b).val ∧ ¬IsZeroSwapWireLayout (rBufHi rNucLayout b)) ∧
          (5616 ≤ (rBufHi rElecLayout b).val ∧ ¬IsZeroSwapWireLayout (rBufHi rElecLayout b)) := by
      have _ := val_bufHi_nuc b
      have _ := val_bufHi_elec b
      have _ := b.isLt
      unfold IsZeroSwapWireLayout
      omega
    refine inKetPred_ket ⟨⟨?_, ?_, ?_⟩, ?_, fun q ↦ ?_⟩
    · rw [hKO val_wOut0 (by decide), hKO val_wOut14 (by decide), hKO val_wOut34 (by decide)]
      exact r0
    · rw [hKO val_wOut1 (by decide), hKO val_wOut35 (by decide)]
      exact r1
    · rw [hKO val_wOut15 (by decide), hKO val_wOut32 (by decide), hKO val_wOut35 (by decide)]
      exact r15
    · have hFixRη := routed_clampPotBRefl_fix_wstate rTot η hrk;
      have hFixIη := routed_clampPotBInPlace_fix_wstate rTot η hrk
      have hFlEq (u : Wire dLayout) (hu : 5616 ≤ u.val) (hnz : ¬ IsZeroSwapWireLayout u) :
          clampFlags rTot β (rTot u) = clampFlags rTot η (rTot u) := by
        obtain ⟨_, fS1, fN1, fO1⟩ := clampFlags_apply rTot β
        obtain ⟨_, fS2, fN2, fO2⟩ := clampFlags_apply rTot η
        by_cases hwS : rTot u = rTot (wPotIsScreen rPot0Layout)
        · rw [hwS, fS1, fS2, hKeep _ (hPot0Ge ⟨2, by decide⟩) nZS_pot,
            hKeep _ (hPot0Ge ⟨1, by decide⟩) nZS_scr]
        · by_cases hwN : rTot u = rTot (wPotIsNN rPot0Layout)
          · rw [hwN, fN1, fN2, hKeep _ (hPot0Ge ⟨2, by decide⟩) nZS_pot,
              hKeep _ (hPot0Ge ⟨1, by decide⟩) nZS_scr, hKeep _ (hPot0Ge ⟨4, by decide⟩) nZS_nn]
          · rw [fO1 _ hwS hwN, fO2 _ hwS hwN, hKeep u hu hnz]
      have hReflβ : clampPotBRefl rTot β = β := by
        funext w;
        obtain ⟨_, _, _, fO1⟩ := clampFlags_apply rTot β; obtain ⟨cN1, cE1, cO1⟩ :=
            clampOneHot_apply rTot (clampFlags rTot β); obtain ⟨cN2, cE2, cO2⟩ :=
            clampOneHot_apply rTot (clampFlags rTot η)
        by_cases hwN : ∃ b, w = rTot (rBufHi rNucLayout b)
        · obtain ⟨b, rfl⟩ := hwN
          change clampOneHot rTot (clampFlags rTot β) _ = _
          rw [cN1 b, hFlEq _ (hPot0Ge ⟨4, by decide⟩) nZS_nn, hFlEq _ (hBNZ b).1.1 (hBNZ b).1.2,
            ← cN2 b]
          exact (congrFun hFixRη _).trans (hKeep _ (hBNZ b).1.1 (hBNZ b).1.2).symm
        · by_cases hwE : ∃ b, w = rTot (rBufHi rElecLayout b)
          · obtain ⟨b, rfl⟩ := hwE
            change clampOneHot rTot (clampFlags rTot β) _ = _
            rw [cE1 b, hFlEq _ (hPot0Ge ⟨4, by decide⟩) nZS_nn, hFlEq _ (hBNZ b).2.1 (hBNZ b).2.2,
              ← cE2 b]
            exact (congrFun hFixRη _).trans (hKeep _ (hBNZ b).2.1 (hBNZ b).2.2).symm
          · change clampOneHot rTot (clampFlags rTot β) w = β w
            rw [cO1 w (fun b e ↦ hwN ⟨b, e⟩) (fun b e ↦ hwE ⟨b, e⟩)]
            by_cases hwS : w = rTot (wPotIsScreen rPot0Layout)
            · subst hwS
              rw [hFlEq _ (hPot0Ge ⟨1, by decide⟩) nZS_scr,
                ← cO2 _ (fun b e ↦ hwN ⟨b, e⟩) (fun b e ↦ hwE ⟨b, e⟩)]
              exact (congrFun hFixRη _).trans (hKeep _ (hPot0Ge ⟨1, by decide⟩) nZS_scr).symm
            · by_cases hwNN : w = rTot (wPotIsNN rPot0Layout)
              · subst hwNN
                rw [hFlEq _ (hPot0Ge ⟨4, by decide⟩) nZS_nn,
                  ← cO2 _ (fun b e ↦ hwN ⟨b, e⟩) (fun b e ↦ hwE ⟨b, e⟩)]
                exact (congrFun hFixRη _).trans (hKeep _ (hPot0Ge ⟨4, by decide⟩) nZS_nn).symm
              · exact fO1 w hwS hwNN
      unfold clampPotBInPlace; rw [hReflβ]; funext w;
      obtain ⟨sE1, sO1⟩ := clampScreenPortB_apply rTot β; obtain ⟨sE2, _⟩ :=
          clampScreenPortB_apply rTot η
      by_cases hwE : ∃ b, w = rTot (rBufHi rElecLayout b)
      · obtain ⟨b, rfl⟩ := hwE
        have hbGe : 5616 ≤ (rBufHi rElecLayout b).val := by have := val_bufHi_elec b; omega
        have hbNZ : ¬ IsZeroSwapWireLayout (rBufHi rElecLayout b) := by
          unfold IsZeroSwapWireLayout; have := val_bufHi_elec b; have := b.isLt; omega
        rw [sE1 b, hKeep (wPotIsScreen rPot0Layout) (hPot0Ge ⟨1, by omega⟩) nZS_scr,
            hKeep _ hbGe hbNZ, ← sE2 b]
        have hScη : clampScreenPortB rTot η = η := by
          have := hFixIη; unfold clampPotBInPlace at this; rwa [hFixRη] at this
        exact congrFun hScη (rTot (rBufHi rElecLayout b))
      · exact sO1 w (fun b e ↦ hwE ⟨b, e⟩)
    · have hRng := val_rPermPot103_rClean714Layout_rng q
      exact (hKeep (rPermPot103 (rClean714Layout q))
        (by rcases hRng with h | h | h <;> omega)
        (by unfold IsZeroSwapWireLayout; rcases hRng with h | h | h <;> omega)).trans
        (routed_clean714_zero_wstate rTot η hrk q)

def xorNucLoToElecHiNotScrBits {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    BitAssignment n :=
    DynCircExt.writeReg β (rTot.compose ⟨rBufHi rElecLayout, rBufHi_inj rElecLayout⟩)
    (fun b ↦ β (rTot (rBufHi rElecLayout b)) + (1 + β (rTot (wPotIsScreen rPot0Layout))) *
    β (rTot (rBufLo rNucLayout b)))
theorem xorNucLoToElecHiNotScrBits_apply {n : ℕ} (rTot : QRegister dLayout n)
    (β : BitAssignment n) :
    (∀ b : Fin 24, xorNucLoToElecHiNotScrBits rTot β (rTot (rBufHi rElecLayout b)) =
    β (rTot (rBufHi rElecLayout b)) + (1 + β (rTot (wPotIsScreen rPot0Layout))) *
    β (rTot (rBufLo rNucLayout b))) ∧ (∀ w : Wire n, (∀ b : Fin 24, w ≠
    rTot (rBufHi rElecLayout b)) → xorNucLoToElecHiNotScrBits rTot β w = β w) := by
  let rEB : QRegister 24 n := rTot.compose ⟨rBufHi rElecLayout, rBufHi_inj rElecLayout⟩
  exact ⟨fun b ↦ DynCircExt.writeReg_apply_reg β rEB _ b, fun w hE ↦
      DynCircExt.writeReg_apply_of_not_mem β rEB _ w (fun ⟨b, hb⟩ ↦ hE b hb.symm)⟩

theorem xorNucLoToElecHi_wires_ne {n : ℕ} (rTot : QRegister dLayout n) :
    (∀ b : Fin 24, rTot (wPotIsScreen rPot0Layout) ≠ rTot (rBufLo rNucLayout b)) ∧
    (∀ b : Fin 24, rTot (wPotIsScreen rPot0Layout) ≠ rTot (rBufHi rElecLayout b)) ∧
    (∀ b₁ b₂ : Fin 24, rTot (rBufLo rNucLayout b₁) ≠ rTot (rBufHi rElecLayout b₂)) ∧
    (∀ b₁ b₂ : Fin 24, rTot (rBufHi rElecLayout b₁) = rTot (rBufHi rElecLayout b₂) → b₁ = b₂) := by
  have nePair : ∀ {a b : Wire dLayout}, a.val ≠ b.val → rTot a ≠ rTot b :=
    fun hne e ↦ hne (congrArg Fin.val (rTot.wires.injective e))
  refine ⟨fun b ↦
      nePair (by rw [val_wPotFlags_rPot0Layout.1, val_rBufLo_nuc b]; have := b.isLt; omega),
    fun b ↦
        nePair (by rw [val_wPotFlags_rPot0Layout.1, val_bufHi_elec b]; have := b.isLt; omega),
    fun b₁ b₂ ↦
        nePair
        (by rw [val_rBufLo_nuc b₁,
              val_bufHi_elec b₂]; have := b₁.isLt; have := b₂.isLt; omega),
    fun b₁ b₂ e ↦ rBufHi_inj rElecLayout (rTot.wires.injective e)⟩

def toffScr24Prefix {n : ℕ} (rTot : QRegister dLayout n) : ℕ → BitAssignment n → BitAssignment n
  | 0, β => β
  | j + 1, β =>
      if hj : j < 24 then
        let γ := toffScr24Prefix rTot j β
        let t := rTot (rBufHi rElecLayout ⟨j, hj⟩)
        Function.update γ t
          (γ t + γ (rTot (wPotIsScreen rPot0Layout)) * γ (rTot (rBufLo rNucLayout ⟨j, hj⟩)))
      else toffScr24Prefix rTot j β

def cToffScr24Aux {n : ℕ} (rTot : QRegister dLayout n) : ∀ k : ℕ, k ≤ 24 → Circuit n
  | 0, _ => .identity
  | j + 1, hj =>
      let hne := xorNucLoToElecHi_wires_ne rTot
      cToffScr24Aux rTot j (Nat.le_of_succ_le hj) ;;ᶜ
        Circuit.TOFF
          (rTot (wPotIsScreen rPot0Layout))
          (rTot (rBufLo rNucLayout ⟨j, hj⟩))
          (rTot (rBufHi rElecLayout ⟨j, hj⟩))
          (hne.1 ⟨j, hj⟩) (hne.2.1 ⟨j, hj⟩) (hne.2.2.1 ⟨j, hj⟩ ⟨j, hj⟩)

theorem cToffScr24Aux_mulVec_ket {n : ℕ} (rTot : QRegister dLayout n) :
    ∀ (k : ℕ) (hk : k ≤ 24) (β : BitAssignment n),
      (cToffScr24Aux rTot k hk).eval.1.mulVec (ket β) = ket (toffScr24Prefix rTot k β)
  | 0, _, β => by
      dsimp only [cToffScr24Aux, toffScr24Prefix];
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | j + 1, hj, β => by
      have hlt : j < 24 :=
          hj; dsimp only [cToffScr24Aux, toffScr24Prefix]; rw [DynCircExt.eval_seq_mulVec,
          cToffScr24Aux_mulVec_ket rTot j (Nat.le_of_succ_le hj) β,
          dite_eq_left hlt]; exact DynCircExt.ket_TOFF _ _ _ _ _ _ _
theorem toffScr24Prefix_props {n : ℕ} (rTot : QRegister dLayout n) :
    ∀ (k : ℕ) (_hk : k ≤ 24) (β : BitAssignment n),
      (∀ b : Fin 24, b.val < k →
        toffScr24Prefix rTot k β (rTot (rBufHi rElecLayout b)) =
          β (rTot (rBufHi rElecLayout b)) +
            β (rTot (wPotIsScreen rPot0Layout)) * β (rTot (rBufLo rNucLayout b))) ∧
      (∀ w : Wire n, (∀ b : Fin 24, b.val < k → w ≠ rTot (rBufHi rElecLayout b)) →
        toffScr24Prefix rTot k β w = β w)
  | 0, _, _ => ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ ↦ rfl⟩
  | j + 1, hj, β => by
      obtain ⟨hE, hO⟩ :=
          toffScr24Prefix_props rTot j (Nat.le_of_succ_le hj) β; obtain ⟨_, hneSE, hneNE, hinjE⟩ :=
          xorNucLoToElecHi_wires_ne rTot; have hlt : j < 24 := hj
      dsimp only [toffScr24Prefix]; rw [dite_eq_left hlt]
      set γ := toffScr24Prefix rTot j β
      let bj : Fin 24 := ⟨j, hlt⟩
      have hγS : γ (rTot (wPotIsScreen rPot0Layout)) = β (rTot (wPotIsScreen rPot0Layout)) :=
          hO _ fun b _ ↦ hneSE b
      have hγNj : γ (rTot (rBufLo rNucLayout bj)) = β (rTot (rBufLo rNucLayout bj)) :=
          hO _ fun b _ ↦ hneNE bj b
      have hγEj : γ (rTot (rBufHi rElecLayout bj)) = β (rTot (rBufHi rElecLayout bj)) :=
          hO _ fun b hb ↦ fun e ↦ Nat.ne_of_gt hb (congrArg Fin.val (hinjE bj b e))
      refine ⟨fun b hb ↦ ?_, fun w hw ↦ ?_⟩
      · by_cases hbj : b = bj
        · subst hbj; rw [Function.update_self, hγEj, hγS, hγNj]
        · have hb' : b.val < j :=
            Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hb) (fun e ↦ hbj (Fin.ext e))
          rw [Function.update_of_ne (fun e ↦ hbj (hinjE b bj e)), hE b hb']
      · rw [Function.update_of_ne (hw bj (Nat.lt_succ_self j))]
        exact hO w fun b hb ↦ hw b (Nat.lt_succ_of_lt hb)

def cXorNucLoToElecHiNotScr {n : ℕ} (rTot : QRegister dLayout n) : Circuit n :=
  Circuit.X (rTot (wPotIsScreen rPot0Layout)) ;;ᶜ
    cToffScr24Aux rTot 24 le_rfl ;;ᶜ
    Circuit.X (rTot (wPotIsScreen rPot0Layout))

def uXorNucLoToElecHiNotScr {n : ℕ} (rTot : QRegister dLayout n) : Unitary (2 ^ n) :=
    (cXorNucLoToElecHiNotScr rTot).eval
def xorNucLoToElecHiNotScrOp {n : ℕ} (rTot : QRegister dLayout n) : Operator (2 ^ n) :=
    (uXorNucLoToElecHiNotScr rTot).1
theorem circWires_cToffScr24Aux {n : ℕ} {S : Wire n → Prop} (rTot : QRegister dLayout n)
    (hScr : S (rTot (wPotIsScreen rPot0Layout)))
    (hNuc : ∀ b : Fin 24, S (rTot (rBufLo rNucLayout b)))
    (hElec : ∀ b : Fin 24, S (rTot (rBufHi rElecLayout b))) :
    ∀ (k : ℕ) (hk : k ≤ 24), CircWires S (cToffScr24Aux rTot k hk)
  | 0, _ => trivial
  | j + 1, hj =>
      ⟨circWires_cToffScr24Aux rTot hScr hNuc hElec j (Nat.le_of_succ_le hj),
       fun i ↦ by fin_cases i <;> first | exact hScr | exact hNuc ⟨j, hj⟩ | exact hElec ⟨j, hj⟩⟩

theorem circWires_cXorNucLoToElecHiNotScr {n : ℕ} {S : Wire n → Prop} (rTot : QRegister dLayout n)
    (hScr : S (rTot (wPotIsScreen rPot0Layout)))
    (hNuc : ∀ b : Fin 24, S (rTot (rBufLo rNucLayout b)))
    (hElec : ∀ b : Fin 24, S (rTot (rBufHi rElecLayout b))) :
    CircWires S (cXorNucLoToElecHiNotScr rTot) :=
  ⟨fun i ↦ by fin_cases i; exact hScr,
   circWires_cToffScr24Aux rTot hScr hNuc hElec 24 le_rfl,
   fun i ↦ by fin_cases i; exact hScr⟩

theorem xorNucLoToElecHiNotScrOp_mulVec_ket {n : ℕ} (rTot : QRegister dLayout n)
    (β : BitAssignment n) : (xorNucLoToElecHiNotScrOp rTot).mulVec (ket β) =
    ket (xorNucLoToElecHiNotScrBits rTot β) := by
  dsimp only [xorNucLoToElecHiNotScrOp, uXorNucLoToElecHiNotScr, cXorNucLoToElecHiNotScr];
  rw [DynCircExt.eval_seq_mulVec, DynCircExt.eval_seq_mulVec, ket_X,
      cToffScr24Aux_mulVec_ket rTot 24 le_rfl, ket_X]; obtain ⟨hneSN, hneSE, _, _⟩ :=
      xorNucLoToElecHi_wires_ne rTot; let β₁ :=
                                        Function.update β (rTot (wPotIsScreen rPot0Layout))
                                        (β (rTot (wPotIsScreen rPot0Layout)) + 1); obtain ⟨hE, hO⟩
                                        :=
                                        toffScr24Prefix_props rTot 24 le_rfl β₁; obtain ⟨xE, xO⟩ :=
                                        xorNucLoToElecHiNotScrBits_apply rTot β
  refine congrArg ket (funext fun w ↦ ?_)
  have hS₂ : toffScr24Prefix rTot 24 β₁ (rTot (wPotIsScreen rPot0Layout)) =
      β (rTot (wPotIsScreen rPot0Layout)) + 1 :=
      (hO _ fun b _ ↦ hneSE b).trans (Function.update_self _ _ _)
  by_cases hwS : w = rTot (wPotIsScreen rPot0Layout)
  · subst hwS
    rw [Function.update_self, hS₂, xO _ (fun b e ↦ hneSE b e)]
    rcases DynCircExt.bit_cases (β (rTot (wPotIsScreen rPot0Layout))) with hs | hs <;>
      (rw [hs]; decide)
  · rw [Function.update_of_ne hwS]
    by_cases hwE : ∃ b : Fin 24, w = rTot (rBufHi rElecLayout b)
    · obtain ⟨b, rfl⟩ := hwE
      rw [hE b b.isLt, xE b,
          show β₁ (rTot (rBufHi rElecLayout b)) = β (rTot (rBufHi rElecLayout b)) from
            Function.update_of_ne (hneSE b).symm _ _,
          show β₁ (rTot (wPotIsScreen rPot0Layout)) = β (rTot (wPotIsScreen rPot0Layout)) + 1 from
            Function.update_self _ _ _,
          show β₁ (rTot (rBufLo rNucLayout b)) = β (rTot (rBufLo rNucLayout b)) from
            Function.update_of_ne (hneSN b).symm _ _,
          add_comm (β (rTot (wPotIsScreen rPot0Layout))) 1]
    · rw [hO w (fun b _ e ↦ hwE ⟨b, e⟩), xO w (fun b e ↦ hwE ⟨b, e⟩)]
      exact Function.update_of_ne hwS _ _

theorem xorNucLoToElecHiNotScrOp_congr_of_pot0Eq {n : ℕ} (rTot₁ rTot₂ : QRegister dLayout n)
    (hReg0 : rTot₁.compose rPot0Layout = rTot₂.compose rPot0Layout) :
    xorNucLoToElecHiNotScrOp rTot₁ = xorNucLoToElecHiNotScrOp rTot₂ := by
  have hAt (j : Fin 146) : rTot₁ (rPot0Layout j) = rTot₂ (rPot0Layout j) :=
    congrArg (fun r : QRegister 146 n ↦ r j) hReg0
  have hW {w : Wire dLayout} (o : ℕ) (ho : o < 146)
      (hv : w.val = (potZeroNEremWireFn 0 pot0_le_690 ⟨o, ho⟩).val) :
      rTot₁ w = rTot₂ w := Fin.ext hv ▸ hAt ⟨o, ho⟩
  have hNuc : ∀ b : Fin 24, rTot₁ (rBufLo rNucLayout b) = rTot₂ (rBufLo rNucLayout b)
    | ⟨bv, hb⟩ => hW (9 + bv) (by omega) (by
        rw [val_rBufLo_nuc ⟨bv, hb⟩, val_potZeroNEremWireFn pot0_le_690]
        dsimp only
        split_ifs <;> omega)
  have hElec : ∀ b : Fin 24, rTot₁ (rBufHi rElecLayout b) = rTot₂ (rBufHi rElecLayout b)
    | ⟨bv, hb⟩ => hW (81 + bv) (by omega) (by
        rw [val_bufHi_elec ⟨bv, hb⟩, val_potZeroNEremWireFn pot0_le_690]
        dsimp only
        split_ifs <;> omega)
  have hwSc : rTot₁ (wPotIsScreen rPot0Layout) = rTot₂ (wPotIsScreen rPot0Layout) :=
    hAt ⟨1, by decide⟩
  refine matrix_ext_ket fun β ↦ ?_
  rw [xorNucLoToElecHiNotScrOp_mulVec_ket, xorNucLoToElecHiNotScrOp_mulVec_ket]
  obtain ⟨xE1, xO1⟩ := xorNucLoToElecHiNotScrBits_apply rTot₁ β
  obtain ⟨xE2, xO2⟩ := xorNucLoToElecHiNotScrBits_apply rTot₂ β
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hwE : ∃ b : Fin 24, w = rTot₁ (rBufHi rElecLayout b)
  · obtain ⟨b, rfl⟩ := hwE
    rw [xE1 b, hElec b, xE2 b, hwSc, hNuc b]
  · rw [xO1 w (fun b e ↦ hwE ⟨b, e⟩), xO2 w (fun b e ↦ hwE ⟨b, e.trans (hElec b).symm⟩)]

set_option maxHeartbeats 2000000 in
-- In-place 151-wire potential reflection ket action proof needs raised heartbeats.
attribute [local irreducible] clampOneHot clampPotBRefl packPortBSt swapHi24Bits in
theorem uPotReflMuxZeroNErem_specK_portB151_inPlace_ket_eq
    {K n Wp : ℕ} [NeZero (2 ^ n)]
    {peK : BitAssignment K → PotExpectFn}
    (specK : ∀ γ : BitAssignment K, ReflPotSliceSpec (peK γ)) (hWp : Wp ≤ 738)
    (rCoin : QRegister K dLayout)
    (hBand : ∀ j : Fin K, 7143 ≤ (rCoin j).val ∧ (rCoin j).val < 7256)
    (rTot : QRegister dLayout n) (isCsel : Bool)
    (st0 : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
    (hOneHot : ∀ b : Fin 24,
      (st0 δ (rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
          ⟨4, by omega⟩) = 0 →
        st0 δ (rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
          ⟨122 + b.val, by omega⟩) = 0) ∧
      (st0 δ (rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
          ⟨4, by omega⟩) = 1 →
        st0 δ (rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp))
          ⟨57 + b.val, by omega⟩) = 0)) :
    let hMaxWp := maxWp24_le_738 hWp
    let rB := rTot.compose (rPotZeroNEremPortB151 (max Wp 24) hMaxWp)
    let rSub := rB.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le (Nat.le_max_left Wp 24)))
    let rC := rTot.compose rCoin
    let stP := packPortBSt rB (Nat.le_max_right Wp 24) st0
    (xorNucLoToElecHiNotScrOp rTot).mulVec ((uSwapHi24 rTot).1 *ᵥ
        ((rTot.embedUnitary (uPotReflMuxZeroNErem rCoin hBand specK isCsel)).1 *ᵥ ket (st0 δ))) =
      bitSign (potReflPortBPh0 (fun γ ↦ (specK γ).phaseBit) isCsel rSub rC stP δ) •
        ket (xorPortB41NotScr rSub
          (potReflPortBSt (fun γ ↦ (specK γ).coinSwap) isCsel rSub rC stP δ)) := by
  intro hMaxWp rB rSub rC stP; let r0 := rTot.compose rPot0Layout;
  have hSwEq : swapHi24Bits rTot (st0 δ) = stP δ :=
      swapHi24Bits_eq_packPortB151St hWp rTot st0 δ hOneHot; obtain ⟨sPE, _, sPO⟩ :=
      swapHi24Bits_apply rTot (st0 δ)
  have hStPK : ∀ (u : Wire dLayout),
      (u.val < 5779 ∨ (5803 ≤ u.val ∧ u.val < 5875) ∨ 5899 ≤ u.val) →
      stP δ (rTot u) = st0 δ (rTot u) := fun u hu ↦ by
    rw [← hSwEq]
    exact sPO (rTot u)
      (fun b e ↦ by
        have hv := congrArg Fin.val (rTot.wires.injective e)
        rw [val_rBufHi_rElecLayout] at hv; have _ := b.isLt; omega)
      (fun b e ↦ by
        have hv := congrArg Fin.val (rTot.wires.injective e)
        rw [val_rBufHi_rNucLayout] at hv; have _ := b.isLt; omega)
  have hv0 : ∀ (c : ℕ) (hc : c < 146), (c < 33 ∨ (57 ≤ c ∧ c < 81) ∨ 105 ≤ c) →
      (rPot0Layout ⟨c, hc⟩).val < 5779 ∨
        (5803 ≤ (rPot0Layout ⟨c, hc⟩).val ∧ (rPot0Layout ⟨c, hc⟩).val < 5875) ∨
        5899 ≤ (rPot0Layout ⟨c, hc⟩).val := fun c hc hcond ↦ by
    have hv : (rPot0Layout ⟨c, hc⟩).val =
        (potZeroNEremWireFn 0 pot0_le_690 ⟨c, hc⟩).val := rfl
    rw [hv, val_potZeroNEremWireFn pot0_le_690]; dsimp; split_ifs <;> omega
  have hSubAt (c d : ℕ) (hc : c < 122) (hd : d < 146)
      (heq : (if c < 33 then c else c + 24) = d) : rSub ⟨c, by omega⟩ = r0 ⟨d, hd⟩ := by
    have hcB : c < 122 + max Wp 24 := by omega
    refine Eq.trans (b := rB ⟨c, hcB⟩) (congrArg rB.wires (Fin.ext (Nat.zero_add c)))
      (congrArg rTot.wires (Fin.ext ?_))
    change (potZeroNEremPortB151WireFn (max Wp 24) hMaxWp ⟨c, hcB⟩).val =
      (potZeroNEremWireFn 0 pot0_le_690 ⟨d, hd⟩).val
    rw [val_potZeroNEremPortB151WireFn hMaxWp, val_potZeroNEremWireFn pot0_le_690]
    dsimp
    split_ifs at heq ⊢ <;> omega
  have hSubHi (c : ℕ) (hlo : 33 ≤ c) (hc : c < 122) :
      rSub ⟨c, by omega⟩ = r0 ⟨c + 24, by omega⟩ :=
    hSubAt c (c + 24) hc (by omega) (ite_eq_right (by omega))
  have hKeep0 (c : ℕ) (hc : c < 33) :
      stP δ (rSub ⟨c, by omega⟩) = st0 δ (r0 ⟨c, by omega⟩) :=
    (congrArg (stP δ) (hSubAt c c (by omega) (by omega) (ite_eq_left hc))).trans
      (hStPK (rPot0Layout ⟨c, by omega⟩) (hv0 c (by omega) (Or.inl hc)))
  have hCoinEq : (fun j : Fin K ↦ stP δ (rC j)) = fun j : Fin K ↦ st0 δ (rC j) :=
    funext fun j ↦ hStPK (rCoin j) (Or.inr (Or.inr (by have := hBand j; omega)))
  have hNAM : coordOfReg24 (rPotBNucA rSub) (stP δ) = coordOfReg24 (rPotNucA r0) (st0 δ) :=
    funext fun ax ↦ congrArg byteOfBits (funext fun b ↦
      hKeep0 (9 + (8 * ax.val + b.val))
        (by have := PhotochemistrySolution.PotSelectWiring.coordOfReg24_lt ax b; omega))
  have hEAM : coordOfReg24 (rPotBElecA rSub) (stP δ) = coordOfReg24 (rPotElecA r0) (st0 δ) :=
    funext fun ax ↦ congrArg byteOfBits (funext fun b ↦ by
      have hlt := PhotochemistrySolution.PotSelectWiring.coordOfReg24_lt ax b
      have hr : rPotBElecA rSub ⟨8 * ax.val + b.val, hlt⟩ =
          r0 ⟨57 + (8 * ax.val + b.val), by omega⟩ :=
        (hSubHi (33 + (8 * ax.val + b.val)) (by omega) (by omega)).trans
          (congrArg r0.wires (Fin.ext (Nat.add_right_comm 33 _ 24)))
      exact (congrArg (stP δ) hr).trans (hStPK _
        (hv0 (57 + (8 * ax.val + b.val)) (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
  have hRegCoin41 : rPotBCoin41 rSub = rPotCoin41 r0 :=
    QRegister.ext (Function.Embedding.ext fun ⟨kv, hk⟩ ↦
      (hSubHi (81 + kv) (by omega) (by omega)).trans
        (congrArg r0.wires (Fin.ext (Nat.add_right_comm 81 kv 24))))
  have hZM : (fun k : Fin 41 ↦ stP δ (rPotBCoin41 rSub k)) =
      fun k : Fin 41 ↦ st0 δ (rPotCoin41 r0 k) :=
    funext fun ⟨kv, hk⟩ ↦ (congrArg (stP δ) (congrArg (fun r ↦ r ⟨kv, hk⟩) hRegCoin41)).trans
      (hStPK (rPot0Layout ⟨105 + kv, by omega⟩)
        (hv0 (105 + kv) (by omega) (Or.inr (Or.inr (by omega)))))
  have hPB_wire : ∀ b : Fin 24, rPotBPortB rSub b = rTot (rBufHi rElecLayout b) := fun b ↦ by
    obtain ⟨_, hB57, _, _⟩ :=
        portB151_reg_links hWp rTot; exact (congrArg rB.wires (Fin.ext (Nat.zero_add (57 +
        b.val)))).trans (hB57 b)
  have hPB_nn : (st0 δ (wPotIsNN r0) == 1) = true →
      coordOfReg24 (rPotBPortB rSub) (stP δ) = coordOfReg24 (rPotNucB r0) (st0 δ) :=
    fun hnn ↦ funext fun ax ↦ congrArg byteOfBits (funext fun b ↦ by
      have hlt := PotSelectWiring.coordOfReg24_lt ax b;
      have h1 : st0 δ (rTot (wPotIsNN rPot0Layout)) = 1 :=
          beq_iff_eq.mp hnn; rw [hPB_wire ⟨8 * ax.val + b.val, hlt⟩, ← hSwEq, sPE ⟨8 * ax.val +
          b.val, hlt⟩, ite_eq_left h1]; refine congrArg (st0 δ)
          (congrArg rTot.wires (Fin.ext ?_)); rw [val_rBufHi_rNucLayout]
      change 5779 + (8 * ax.val + b.val) =
        (potZeroNEremWireFn 0 pot0_le_690 ⟨33 + (8 * ax.val + b.val), by omega⟩).val
      rw [val_potZeroNEremWireFn pot0_le_690]; dsimp; split_ifs <;> omega)
  have hPB_ee : (st0 δ (wPotIsNN r0) == 1) = false →
      coordOfReg24 (rPotBPortB rSub) (stP δ) = coordOfReg24 (rPotElecB r0) (st0 δ) :=
    fun hnn ↦ funext fun ax ↦ congrArg byteOfBits (funext fun b ↦ by
      have hlt := PotSelectWiring.coordOfReg24_lt ax b;
      have h0 : st0 δ (rTot (wPotIsNN rPot0Layout)) ≠ 1 :=
          beq_eq_false_iff_ne.mp hnn; rw [hPB_wire ⟨8 * ax.val + b.val, hlt⟩, ← hSwEq,
          sPE ⟨8 * ax.val + b.val, hlt⟩, ite_eq_right h0]; refine congrArg (st0 δ)
          (congrArg rTot.wires (Fin.ext ?_)); rw [val_rBufHi_rElecLayout]
      change 5875 + (8 * ax.val + b.val) =
        (potZeroNEremWireFn 0 pot0_le_690 ⟨81 + (8 * ax.val + b.val), by omega⟩).val
      rw [val_potZeroNEremWireFn pot0_le_690]; dsimp; split_ifs <;> omega)
  obtain ⟨hNB_match, hEB_match⟩ :
      (if stP δ (wPotBIsNN rSub) == 1 then coordOfReg24 (rPotBPortB rSub) (stP δ) else 0) =
        (if st0 δ (wPotIsNN r0) == 1 then coordOfReg24 (rPotNucB r0) (st0 δ) else 0) ∧
      (if stP δ (wPotBIsNN rSub) == 1 then 0 else coordOfReg24 (rPotBPortB rSub) (stP δ)) =
        (if st0 δ (wPotIsNN r0) == 1 then 0 else coordOfReg24 (rPotElecB r0) (st0 δ)) := by
    rw [show stP δ (wPotBIsNN rSub) = st0 δ (wPotIsNN r0) from hKeep0 4 (by omega)]
    cases hnn : (st0 δ (wPotIsNN r0) == 1)
    · exact ⟨rfl, hPB_ee hnn⟩
    · exact ⟨hPB_nn hnn, rfl⟩
  have hGateEq : potGateActive4 isCsel r0 (st0 δ) = potBGateActive isCsel rSub (stP δ) := by
    dsimp only [potGateActive4, potBGateActive, wPotLocQ, wPotIsPot, wPotBLocQ, wPotBIsPot]
    rw [hKeep0 0 (by omega), hKeep0 2 (by omega)]
  have hBitEq : potOracleBitEval ((specK (fun j ↦ st0 δ (rC j))).phaseBit) r0 (st0 δ) =
      potOraclePortBBitEval ((specK (fun j ↦ stP δ (rC j))).phaseBit) rSub (stP δ) := by
    rw [hCoinEq]; dsimp only [potOracleBitEval, potOraclePortBBitEval]
    rw [← (specK (fun j ↦ st0 δ (rC j))).phaseBit_port, hNAM, hEAM, hNB_match, hEB_match, hZM]
    dsimp only [wPotIsScreen, wPotIsNN, wPotSp1B0, wPotSp1B1, wPotSp2B0, wPotSp2B1, wPotBIsScreen,
        wPotBIsNN, wPotBSp1B0, wPotBSp1B1, wPotBSp2B0, wPotBSp2B1]
    rw [hKeep0 1 (by omega), hKeep0 4 (by omega), hKeep0 5 (by omega),
        hKeep0 6 (by omega), hKeep0 7 (by omega), hKeep0 8 (by omega)]
  have hSwapEvalEq : potOracleCoinEval ((specK (fun j ↦ st0 δ (rC j))).coinSwap) r0 (st0 δ) =
      potOraclePortBCoinEval ((specK (fun j ↦ stP δ (rC j))).coinSwap) rSub (stP δ) := by
    rw [hCoinEq]; dsimp only [potOracleCoinEval, potOraclePortBCoinEval]
    rw [← (specK (fun j ↦ st0 δ (rC j))).coinSwap_port, hNAM, hEAM, hNB_match, hEB_match, hZM]
    dsimp only [wPotIsScreen, wPotIsNN, wPotSp1B0, wPotSp1B1, wPotSp2B0, wPotSp2B1, wPotBIsScreen,
        wPotBIsNN, wPotBSp1B0, wPotBSp1B1, wPotBSp2B0, wPotBSp2B1]
    rw [hKeep0 1 (by omega), hKeep0 4 (by omega), hKeep0 5 (by omega),
        hKeep0 6 (by omega), hKeep0 7 (by omega), hKeep0 8 (by omega)]
  have hSwapKet :
      (uSwapHi24 rTot).1 *ᵥ ((rTot.embedUnitary (uPotReflMuxZeroNErem rCoin hBand specK isCsel)).1
      *ᵥ ket (st0 δ)) = bitSign (potReflPortBPh0 (fun γ ↦
      (specK γ).phaseBit) isCsel rSub rC stP δ) • ket (potReflPortBSt (fun γ ↦
      (specK γ).coinSwap) isCsel rSub rC stP δ) := by
    rw [embedUnitary_uPotReflMuxZeroNErem_mulVec_ket rTot rCoin hBand specK isCsel (st0 δ),
        Matrix.mulVec_smul, uSwapHi24_mulVec_ket]
    have hPhEq : potReflPh4 (specK (fun j ↦ st0 δ (rC j))) isCsel r0 (st0 δ) =
        potReflPortBPh0 (fun γ ↦ (specK γ).phaseBit) isCsel rSub rC stP δ := by
      dsimp only [potReflPh4, potReflPortBPh0, wPotLocQ, wPotIsPot, wPotBLocQ, wPotBIsPot]
      rw [hBitEq, hKeep0 0 (by omega), hKeep0 2 (by omega)]
    have hKetEq : swapHi24Bits rTot (potReflSwap4 (specK (fun j ↦
        st0 δ (rC j))) isCsel r0 (st0 δ)) = potReflPortBSt (fun γ ↦
        (specK γ).coinSwap) isCsel rSub rC stP δ := by
      dsimp only [potReflSwap4, potReflPortBSt]; rw [hGateEq, hSwapEvalEq]; split_ifs
      · rw [swapHi24Bits_writeReg_rPotCoin41 rTot (st0 δ) _, hSwEq, hRegCoin41]
      · exact hSwEq
    rw [hPhEq, hKetEq]
  have hXor41 (η : BitAssignment n) :
      xorPortB41NotScr rSub η = xorNucLoToElecHiNotScrBits rTot η := by
    have hPB : rPotBPortB rSub = rTot.compose ⟨rBufHi rElecLayout, rBufHi_inj rElecLayout⟩ :=
      QRegister.ext (Function.Embedding.ext hPB_wire)
    have hNuc : ∀ b : Fin 24, rPotBNucA rSub b = rTot (rBufLo rNucLayout b)
      | ⟨bv, hb⟩ =>
        (hSubAt (9 + bv) (9 + bv) (by omega) (by omega) (ite_eq_left (by omega))).trans
          (congrArg rTot.wires (Fin.ext (by
            change (potZeroNEremWireFn 0 pot0_le_690 ⟨9 + bv, _⟩).val = _
            rw [val_potZeroNEremWireFn pot0_le_690, val_rBufLo_nuc ⟨bv, hb⟩]
            dsimp only
            split_ifs <;> omega)))
    unfold xorPortB41NotScr xorNucLoToElecHiNotScrBits
    rw [hPB, show wPotBIsScreen rSub = rTot (wPotIsScreen rPot0Layout) from
      hSubAt 1 1 (by decide) (by decide) rfl]
    refine congrArg (DynCircExt.writeReg η _) (funext fun b ↦ ?_)
    rw [show (rTot.compose ⟨rBufHi rElecLayout, rBufHi_inj rElecLayout⟩) b =
      rTot (rBufHi rElecLayout b) from rfl, hNuc b]
  rw [hSwapKet, Matrix.mulVec_smul, xorNucLoToElecHiNotScrOp_mulVec_ket, ← hXor41]

theorem cScrubNucFlags3_comm_xorNucLoToElecHiNotScrOp {n : ℕ} (rTot : QRegister dLayout n) :
    (cScrubNucFlags3 rTot).eval.1 * xorNucLoToElecHiNotScrOp rTot = xorNucLoToElecHiNotScrOp rTot *
    (cScrubNucFlags3 rTot).eval.1 := by
  have nePair {a b : Wire dLayout} (hne : a.val ≠ b.val) : rTot a ≠ rTot b :=
    fun e ↦ hne (congrArg Fin.val (rTot.wires.injective e))
  have neE {u : Wire dLayout} (hu : u.val < 5875) (b : Fin 24) :
      rTot u ≠ rTot (rBufHi rElecLayout b) := nePair (val_bufHi_elec b ▸ by omega)
  have hNFix {u : Wire dLayout} (hu : 5747 ≤ u.val) (δ : BitAssignment n) :
      nucFlags3XorBits rTot δ (rTot u) = δ (rTot u) :=
    nucFlags3XorBits_of_ne rTot δ (nePair (val_wOut0 ▸ by omega))
      (nePair (val_wOut1 ▸ by omega)) (nePair (val_wOut15 ▸ by omega))
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, xorNucLoToElecHiNotScrOp_mulVec_ket,
    cScrubNucFlags3_mulVec_ket, cScrubNucFlags3_mulVec_ket, xorNucLoToElecHiNotScrOp_mulVec_ket]
  refine congrArg ket (funext fun w ↦ ?_)
  obtain ⟨xE1, xO1⟩ := xorNucLoToElecHiNotScrBits_apply rTot β
  obtain ⟨xE2, xO2⟩ := xorNucLoToElecHiNotScrBits_apply rTot (nucFlags3XorBits rTot β)
  by_cases hwE : ∃ b : Fin 24, w = rTot (rBufHi rElecLayout b)
  · obtain ⟨b, rfl⟩ := hwE
    have _ := val_bufHi_elec b
    have _ := val_rBufLo_nuc b
    have _ := val_wPotFlags_rPot0Layout.1
    rw [hNFix (by omega), xE1 b, xE2 b, hNFix (by omega), hNFix (by omega), hNFix (by omega)]
  · rw [xO2 w (fun b e ↦ hwE ⟨b, e⟩)]
    unfold nucFlags3XorBits
    have hO : ∀ {u : Wire dLayout}, u.val < 5875 → xorNucLoToElecHiNotScrBits rTot β (rTot u) =
        β (rTot u) := fun hu ↦ xO1 _ (neE hu)
    split_ifs with c0 c1 c15
    · rw [hO (val_wOut0 ▸ by decide), hO (val_wOut14 ▸ by decide), hO (val_wOut34 ▸ by decide)]
    · rw [hO (val_wOut1 ▸ by decide), hO (val_wOut35 ▸ by decide)]
    · rw [hO (val_wOut15 ▸ by decide), hO (val_wOut32 ▸ by decide), hO (val_wOut35 ▸ by decide)]
    · exact xO1 w (fun b e ↦ hwE ⟨b, e⟩)

theorem xorNucLoToElecHiNotScrOp_comm_uBellLoELoMux_wstate {n : ℕ} [NeZero (2 ^ n)]
    (rTot : QRegister dLayout n) : xorNucLoToElecHiNotScrOp rTot *
    (uBellLoEAlwaysLoMux_wstate rTot).1 = (uBellLoEAlwaysLoMux_wstate rTot).1 *
    xorNucLoToElecHiNotScrOp rTot :=
  commutesWithDyn_uBellLoEAlwaysLoMux_elec8_wstate (Var := Unit) rTot
    (p := .circuit (cXorNucLoToElecHiNotScr rTot))
    (circWires_cXorNucLoToElecHiNotScr rTot
      (fun u hu e ↦ by
        have hv := (congrArg Fin.val (rTot.wires.injective e)).symm.trans
          val_wPotFlags_rPot0Layout.1
        omega)
      (fun ⟨bv, hb⟩ u hu e ↦ by
        have hv := (congrArg Fin.val (rTot.wires.injective e)).symm.trans
          (val_rBufLo_nuc ⟨bv, hb⟩)
        omega)
      (fun ⟨bv, hb⟩ u hu e ↦ by
        have hv := (congrArg Fin.val (rTot.wires.injective e)).symm.trans
          (val_bufHi_elec ⟨bv, hb⟩)
        omega))

def pPotWrapReflPortB100InPlaceCore {Var : Type} {kOut n Wp tPotU tPotC : ℕ}
    {peOut : BitAssignment kOut → PotExpectFn} (wWork : ℕ) (hwLo : 232 ≤ wWork) (hwHi : wWork ≤ 886)
    (rSub : QRegister kOut 41)
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut) (hWp : Wp ≤ 609)
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool) : DynamicCircuit Var n :=
  pPotWrapReflPortB151InPlace o24 (by omega : Wp ≤ 738) v
    (rTot.compose (rPermPotNuc3 wWork hwLo hwHi))
    (rCoinExtOut hk0_le72_wstate rSub) isCsel

def pPotWrapReflPortB100InPlaceScrub {Var : Type} {kOut n Wp tPotU tPotC : ℕ}
    {peOut : BitAssignment kOut → PotExpectFn} (wWork : ℕ) (hwLo : 232 ≤ wWork) (hwHi : wWork ≤ 886)
    (rSub : QRegister kOut 41)
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut) (hWp : Wp ≤ 609)
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool) : DynamicCircuit Var n :=
    .seq (.circuit (cScrubNucFlags3 rTot))
    (.seq (pPotWrapReflPortB100InPlaceCore wWork hwLo hwHi rSub o24 hWp v rTot isCsel)
    (.circuit (cScrubNucFlags3 rTot)))
theorem counts_pPotWrapReflPortB100InPlaceScrub {Var : Type} [Finite Var]
    {kOut n Wp tPotU tPotC : ℕ} [NeZero (2 ^ n)] {peOut : BitAssignment kOut → PotExpectFn}
    (wWork : ℕ) (hwLo : 232 ≤ wWork) (hwHi : wWork ≤ 886) (rSub : QRegister kOut 41)
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut) (hWp : Wp ≤ 609)
    (v : Var) (rTot : QRegister dLayout n)
    (isCsel : Bool) :
    (pPotWrapReflPortB100InPlaceScrub wWork hwLo hwHi rSub o24 hWp v rTot isCsel).count .T =
    (if isCsel then tPotC else tPotU) ∧
    (pPotWrapReflPortB100InPlaceScrub wWork hwLo hwHi rSub o24 hWp v rTot isCsel).count .TOFF =
    0 := by
  cases nonempty_fintype Var
  classical
  let rT := rTot.compose (rPermPotNuc3 wWork hwLo hwHi)
  let rC := rCoinExtOut hk0_le72_wstate rSub
  have hM := maxWp24_le_738 (by omega : Wp ≤ 738)
  have hdBC : (rT.compose (rPotZeroNEremPortB151 (max Wp 24) hM)).DisjointWires (rT.compose rC) :=
    disj_of_ne fun i j e ↦ QRegister.disjoint_iff.mp
      (rPotPortB151_disj_coinBand7256 hM rC
        (val_rCoinExtOut_coinBand7256_wstate hk0_le72_wstate rSub)) i j (rT.wires.injective e)
  obtain ⟨hV, hOH, hCl, hPB0⟩ := clampPotBInPlace_props_portB151 (by omega : Wp ≤ 738) rT
  obtain ⟨_, tCore, fCore⟩ := subspaceStep_pPotWrapReflCoinKPortBInPlace o24
    (Nat.le_max_left Wp 24) (Nat.le_max_right Wp 24) v (rT.compose rClean714Layout)
    (rT.compose (rPotZeroNEremPortB151 (max Wp 24) hM)) (rT.compose rC) hdBC isCsel
    (clampPotBInPlace rT) (fun δ _ ↦ hV δ) hOH hCl (fun δ i _ ↦ hPB0 δ i)
  obtain ⟨tSc, fSc⟩ :=
      counts_cScrubNucFlags3 rTot; dsimp only [pPotWrapReflPortB100InPlaceScrub,
      pPotWrapReflPortB100InPlaceCore, DynamicCircuit.count]; rw [tSc, fSc, tCore, fCore]
  exact ⟨by omega, by omega⟩

attribute [local irreducible] cScrubNucFlags3 uCopyAll3AlwaysLoMux_wstate in
theorem subspaceStep_pPotWrapReflPortB100Scrub_lo_wstate
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {w1 wWork kOut n Wp tPotU tPotC : ℕ} [NeZero (2 ^ n)]
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peOut : BitAssignment kOut → PotExpectFn}
    (hwLo : 232 ≤ wWork) (hwHi : wWork ≤ 886)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode)
    (rSub : QRegister kOut 41)
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut)
    (hWp : Wp ≤ 609)
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool)
    (X₁ : Operator (2 ^ n))
    (hAbsX₁ : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁) :
    let rN := rTot.compose rNucSub
    let rE := rTot.compose rElecSub
    let Wnh := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))
    let uKin :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    let s41 := spec41Of24_ipb o24.sliceSpec
    let s4 := stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk0_le72_wstate rSub o1 s41 hCoin
    let uStage4 :=
        if isCsel then uCselMuxWState hk0_le72_wstate rSub o1 s4 else uUselMuxWState hk0_le72_wstate
        rSub o1 s4
    SubspaceStep (Var := Var) ((uBellLoCopyHiAlwaysLoConj rE).1 *
        (uCopyLoHiAlwaysLoMat rN * ((uZeroSwapNE rTot).1 * (uKin.1 * (Wnh.1 * X₁)))))
      ((uBellLoEAlwaysLoMux_wstate rTot).1 * (xorNucLoToElecHiNotScrOp rTot * ((uSwapHi24 rTot).1 *
            ((uCopyAll3AlwaysLoMux_wstate rTot).1 *
              ((uZeroSwapNE rTot).1 * ((rTot.embedUnitary uStage4).1 * (Wnh.1 * X₁)))))))
      (pPotWrapReflPortB100InPlaceScrub wWork hwLo hwHi rSub o24 hWp v rTot isCsel) := by
  intro rN rE Wnh uKin s41 s4 uStage4;
  let rTot1  := rTot.compose (rSwapNucFlags3Top wWork hwLo hwHi);
  let rTot'' := rTot.compose (rPermPotNuc3 wWork hwLo hwHi);
  let rCoin := rCoinExtOut hk0_le72_wstate rSub;
  let hBand := val_rCoinExtOut_coinBand7256_wstate hk0_le72_wstate rSub
  have hWp738 : Wp ≤ 738 := by omega
  have hMaxWp : max Wp 24 ≤ 738 := maxWp24_le_738 hWp738;
  let rW'' := rTot''.compose rClean714Layout;
  let rB'' := rTot''.compose (rPotZeroNEremPortB151 (max Wp 24) hMaxWp);
  let rC'' := rTot''.compose rCoin; let st0'' := clampPotBInPlace rTot''
  have hdBC : rB''.DisjointWires rC'' := disj_of_ne fun i j e ↦
      QRegister.disjoint_iff.mp (rPotPortB151_disj_coinBand7256 hMaxWp rCoin hBand) i j
      (rTot''.wires.injective e)
  obtain ⟨hValidStP, hOneHotSt0, hCleanHiSt0, hPB0StP⟩ :=
      clampPotBInPlace_props_portB151 hWp738 rTot''
  obtain ⟨sPW, _, _⟩ :=
      subspaceStep_pPotWrapReflCoinKPortBInPlace o24 (Nat.le_max_left Wp 24)
      (Nat.le_max_right Wp 24) v rW'' rB'' rC'' hdBC isCsel st0'' (fun δ _ ↦
      hValidStP δ) hOneHotSt0 hCleanHiSt0 (fun δ i _ ↦ hPB0StP δ i)
  obtain ⟨hReg103, hSwap103, hCl103⟩ := permPot103_rPot0_and_clamp rTot1
  obtain ⟨hRegNF, hSwapNF, hClNF⟩ := rSwapNucFlags3Top_rPot0_and_clamp hwLo hwHi rTot
  have hReg0 : rTot''.compose rPot0Layout = rTot.compose rPot0Layout := hReg103.trans hRegNF
  have hSwapEq : (uSwapHi24 rTot'').1 = (uSwapHi24 rTot).1 := hSwap103.trans hSwapNF
  have hXorEq : xorNucLoToElecHiNotScrOp rTot'' = xorNucLoToElecHiNotScrOp rTot :=
    xorNucLoToElecHiNotScrOp_congr_of_pot0Eq rTot'' rTot hReg0
  have hEHi : ∀ b : Fin 24, rTot'' (rBufHi rElecLayout b) = rTot (rBufHi rElecLayout b)
    | ⟨bv, hb⟩ => by
        have hr : rPot0Layout ⟨81 + bv, by omega⟩ = rBufHi rElecLayout ⟨bv, hb⟩ := Fin.ext (by
          change (potZeroNEremWireFn 0 pot0_le_690 _).val = _
          rw [val_potZeroNEremWireFn pot0_le_690, val_bufHi_elec ⟨bv, hb⟩]
          dsimp only
          split_ifs <;> omega)
        exact hr ▸ congrArg (fun r : QRegister 146 n ↦ r ⟨81 + bv, by omega⟩) hReg0
  have hClEq : clampPotBRefl rTot'' = clampPotBRefl rTot := hCl103.trans hClNF
  have hwSc : rTot'' (wPotIsScreen rPot0Layout) = rTot (wPotIsScreen rPot0Layout) :=
    congrArg (fun r : QRegister 146 n ↦ r ⟨1, by decide⟩) hReg0
  have hClampEq : clampPotBInPlace rTot'' = clampPotBInPlace rTot := funext fun β ↦ by
    unfold clampPotBInPlace
    rw [hClEq]
    funext w
    obtain ⟨cE1, cO1⟩ := clampScreenPortB_apply rTot'' (clampPotBRefl rTot β)
    obtain ⟨cE2, cO2⟩ := clampScreenPortB_apply rTot (clampPotBRefl rTot β)
    by_cases hwE : ∃ b : Fin 24, w = rTot (rBufHi rElecLayout b)
    · obtain ⟨b, rfl⟩ := hwE
      rw [← hEHi b, cE1 b, hEHi b, hwSc, cE2 b]
    · rw [cO1 w (fun b e ↦ hwE ⟨b, e.trans (hEHi b)⟩), cO2 w (fun b e ↦ hwE ⟨b, e⟩)]
  have hCoinEq : rTot''.compose rCoin = rTot.compose rCoin :=
    congrArg QRegister.mk (Function.Embedding.ext fun j ↦ congrArg rTot.wires (by
      have hb :=
          val_rCoinExtOut_bounds hk0_le72_wstate rSub j; change rSwapNucFlags3Top wWork hwLo hwHi
          (rPermPot103 (rCoin j)) = rCoin j
      rw [rPermPot103_fix_of_bounds (rCoin j) (Or.inr (Or.inr (by dsimp only [rCoin]; omega)))]
      exact rSwapNucFlags3Top_fix hwLo hwHi (rCoin j) (by dsimp only [rCoin]; omega)))
  let UPot'' := rTot''.embedUnitary (uPotReflMuxZeroNErem rCoin hBand s41 isCsel)
  let UPot := rTot.embedUnitary (uPotReflMuxZeroNErem rCoin hBand s41 isCsel)
  have hUPotEq : UPot''.1 = UPot.1 := by
    apply matrix_ext_ket; intro β
    rw [embedUnitary_uPotReflMuxZeroNErem_mulVec_ket rTot'' rCoin hBand s41 isCsel β,
        embedUnitary_uPotReflMuxZeroNErem_mulVec_ket rTot rCoin hBand s41 isCsel β, hReg0, hCoinEq]
  let M0 := mkKetOpW rW'' (clampPotBInPlace rTot) (fun _ ↦ 0)
  have hM0Eq : mkKetOpW rW'' st0'' (fun _ ↦ 0) = M0 := by dsimp only [st0'', M0]; rw [hClampEq]
  have sPW0 : SubspaceStep (Var := Var) M0
      (xorNucLoToElecHiNotScrOp rTot * ((uSwapHi24 rTot).1 * (UPot.1 * M0)))
      (pPotWrapReflPortB100InPlaceCore wWork hwLo hwHi rSub o24 hWp v rTot isCsel) := by
    rw [← hM0Eq, ← hXorEq, ← hSwapEq, ← hUPotEq]; refine subspaceStep_congr_out sPW ?_
    symm
    apply matrix_ext_ket; intro δ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket,
        mkKetOpW_mulVec_ket]
    by_cases hz : ∀ q : Fin 714, δ (rW'' q) = 0
    · rw [ite_eq_left hz, ite_eq_left hz, bitSign_zero, one_smul];
      exact uPotReflMuxZeroNErem_specK_portB151_inPlace_ket_eq s41 hWp738 rCoin hBand rTot'' isCsel
          st0'' δ (hOneHotSt0 δ)
    · rw [ite_eq_right hz, ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
  let Rk := uKin.1 * (Wnh.1 * X₁)
  let Y₀ := (uCopyAll3AlwaysLoMux_wstate rTot).1 * ((uZeroSwapNE rTot).1 * Rk)
  let S := (cScrubNucFlags3 rTot).eval;
  have hInEq :=
      routed_scrubNuc3_copyAll3Lo_zeroSwap_wstate hwLo hwHi o1 rTot isCsel X₁ hAbsX₁; change M0 *
      (S.1 * Y₀) = S.1 *
      Y₀ at hInEq; have cCPot :=
                     copyAll3AlwaysLoMux_comm_uPot_wstate rSub s41 rTot isCsel; change
                     (uCopyAll3AlwaysLoMux_wstate rTot).1 * UPot.1 = UPot.1 *
                     (uCopyAll3AlwaysLoMux_wstate rTot).1 at cCPot;
                     have cZPot :=
                     uPot_mul_uZeroSwapNE_rk_wstate o1 rSub s41 rTot isCsel X₁ hAbsX₁; change UPot.1
                     * ((uZeroSwapNE rTot).1 * Rk) = (uZeroSwapNE rTot).1 *
                     (UPot.1 *
                     Rk) at cZPot; have hPotKin :=
                                     (routed_m0Abs_and_potKin_rev_wstate o1 hCoin rSub s41 rTot
                                     isCsel X₁ hAbsX₁).2; change UPot.1 * Rk =
                                     (rTot.embedUnitary uStage4).1 * (Wnh.1 * X₁) at hPotKin
  have sSc1 : SubspaceStep (Var := Var) Y₀ (S.1 * Y₀) (.circuit (cScrubNucFlags3 rTot)) :=
    subspaceStep_of_circuit Y₀ (cScrubNucFlags3 rTot)
  have sMid0 := subspaceStep_mul_right (S.1 * Y₀) sPW0; rw [hInEq] at sMid0
  have sSc2 : SubspaceStep (Var := Var)
      ((xorNucLoToElecHiNotScrOp rTot * ((uSwapHi24 rTot).1 * (UPot.1 * M0))) * (S.1 * Y₀))
      (S.1 * ((xorNucLoToElecHiNotScrOp rTot * ((uSwapHi24 rTot).1 * (UPot.1 * M0))) * (S.1 * Y₀)))
      (.circuit (cScrubNucFlags3 rTot)) :=
    subspaceStep_of_circuit _ (cScrubNucFlags3 rTot)
  have sChain := sSc1.seq (sMid0.seq sSc2)
  have hOutEq : S.1 * ((xorNucLoToElecHiNotScrOp rTot * ((uSwapHi24 rTot).1 * (UPot.1 * M0))) *
      (S.1 * Y₀)) = xorNucLoToElecHiNotScrOp rTot * ((uSwapHi24 rTot).1 *
      ((uCopyAll3AlwaysLoMux_wstate rTot).1 * ((uZeroSwapNE rTot).1 *
      ((rTot.embedUnitary uStage4).1 * (Wnh.1 * X₁))))) := by
    let Xop := xorNucLoToElecHiNotScrOp rTot;
    have cXr : S.1 * Xop = Xop * S.1 := cScrubNucFlags3_comm_xorNucLoToElecHiNotScrOp rTot;
    have cSw : S.1 * (uSwapHi24 rTot).1 = (uSwapHi24 rTot).1 * S.1 :=
        cScrubNucFlags3_comm_uSwapHi24 rTot; have cPt : S.1 * UPot.1 = UPot.1 * S.1 :=
                                               cScrubNucFlags3_comm_uPot_wstate rSub s41 rTot
                                               isCsel; have hSS : S.1 * S.1 = 1 :=
                                                         cScrubNucFlags3_mul_self rTot
    have hS1 : S.1 * ((uSwapHi24 rTot).1 * (UPot.1 * (S.1 * Y₀))) =
        (uSwapHi24 rTot).1 * (UPot.1 * Y₀) := by
      rw [← Matrix.mul_assoc S.1, cSw, Matrix.mul_assoc (uSwapHi24 rTot).1, ← Matrix.mul_assoc S.1,
          cPt, Matrix.mul_assoc UPot.1, ← Matrix.mul_assoc S.1 S.1, hSS, Matrix.one_mul]
    simp only [Matrix.mul_assoc] at hInEq cCPot cZPot hPotKin hS1 ⊢
    rw [hInEq, ← Matrix.mul_assoc S.1 Xop, cXr, Matrix.mul_assoc Xop, hS1]
    dsimp only [Y₀]
    rw [← Matrix.mul_assoc UPot.1 (uCopyAll3AlwaysLoMux_wstate rTot).1, ← cCPot,
        Matrix.mul_assoc (uCopyAll3AlwaysLoMux_wstate rTot).1, cZPot, hPotKin]
  have sInner := subspaceStep_congr_out sChain hOutEq
  change SubspaceStep (Var := Var) Y₀ _
      (pPotWrapReflPortB100InPlaceScrub wWork hwLo hwHi rSub o24 hWp v rTot isCsel) at sInner
  have hDynDisj : DynWires (fun w ↦ ∀ u : Wire dLayout,
      (u.val < 5616 ∨ (5731 ≤ u.val ∧ u.val < 5739) ∨ (5899 ≤ u.val ∧ u.val < 5923)) →
      w ≠ rTot u) (pPotWrapReflPortB100InPlaceCore wWork hwLo hwHi rSub o24 hWp v rTot isCsel) :=
    dynWires_pPotWrapReflPortB151InPlace_skip17 o24 hWp738 v rTot'' rCoin isCsel
      (fun j _ u hu e ↦
        swapNucFlags3Top_permPot103_potPortB151_disj hwLo hwHi hWp738 j hu
          (congrArg Fin.val (rTot.wires.injective e)))
      (fun j u hu e ↦ by
        have hb := val_rCoinExtOut_bounds hk0_le72_wstate rSub j
        have hFix1 := rPermPot103_fix_of_bounds (rCoin j)
          (Or.inr (Or.inr (by dsimp only [rCoin]; omega)))
        have hFix2 := rSwapNucFlags3Top_fix hwLo hwHi (rCoin j) (by dsimp only [rCoin]; omega)
        have hv :=
            congrArg Fin.val (rTot.wires.injective e); change (rSwapNucFlags3Top wWork hwLo hwHi
            (rPermPot103 (rCoin j))).val = u.val at hv; rw [hFix1, hFix2] at hv
        dsimp only [rCoin] at hv; omega)
  have hCommFull : CommutesWithDyn (uBellLoEAlwaysLoMux_wstate rTot)
      (pPotWrapReflPortB100InPlaceScrub wWork hwLo hwHi rSub o24 hWp v rTot isCsel) := by
    unfold pPotWrapReflPortB100InPlaceScrub CommutesWithDyn;
    exact ⟨cScrubNucFlags3_comm_uBellLoEAlwaysLoMux_wstate rTot,
        ⟨commutesWithDyn_uBellLoEAlwaysLoMux_elec8_wstate rTot hDynDisj,
        cScrubNucFlags3_comm_uBellLoEAlwaysLoMux_wstate rTot⟩⟩
  have sBoth :=
      subspaceStep_mul_left_of_commutesWithDyn (uBellLoEAlwaysLoMux_wstate rTot) hCommFull sInner;
      dsimp only [Y₀] at sBoth; rw [← Matrix.mul_assoc (uBellLoEAlwaysLoMux_wstate rTot).1
      (uCopyAll3AlwaysLoMux_wstate rTot).1, ← uBellLoCopyHiLoE_mul_uCopyLoHiLoN_eq_wstate rTot,
      Matrix.mul_assoc] at sBoth; exact sBoth
end QuantumComputation.Specs.PhotochemistrySolution.InPlacePortBOracle
end

namespace QuantumComputation.Specs.PhotochemistrySolution.SharedHi235Port
noncomputable section
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate
  PhotochemistrySolution.KetSupport PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.PortBStage5Merged
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.WStateStage2Load
  PhotochemistrySolution.WStateStage5Unload
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder
/--
Clean `|0⟩` scratch wire `rHA rE 12` (`dLayout[5911]`, fixed by `rPermSharedHi310` and
`rPermScrub338` )
used to hold `1 + rRawHas2 rN + rRawHas2 rE` (`= 1 + isScreen`) as the 235th `bellXHalfVecDyn`
control.
-/
abbrev qScrNotE {n : ℕ} (rE : RouterReg 187 8 n) : Wire n := rHA rE ⟨12, by decide⟩

def cToggleNotRaw2 {n : ℕ} (qNH qEH qOut : Wire n) (hNO : qNH ≠ qOut) (hEO : qEH ≠ qOut) :
    Circuit n :=
  (Circuit.X qOut ;;ᶜ Circuit.CNOT qNH qOut hNO) ;;ᶜ Circuit.CNOT qEH qOut hEO

def toggleNotRaw2Bits {n : ℕ} (qNH qEH qOut : Wire n) (α : BitAssignment n) : BitAssignment n :=
    Function.update α qOut (α qOut + 1 + α qNH + α qEH)
theorem counts_cToggleNotRaw2 {n : ℕ} (qNH qEH qOut : Wire n) (hNO : qNH ≠ qOut)
    (hEO : qEH ≠ qOut) :
    (cToggleNotRaw2 qNH qEH qOut hNO hEO).count .T = 0 ∧
    (cToggleNotRaw2 qNH qEH qOut hNO hEO).count .TOFF = 0 := ⟨rfl, rfl⟩

theorem cToggleNotRaw2_mulVec_ket {n : ℕ} (qNH qEH qOut : Wire n) (hNO : qNH ≠ qOut)
    (hEO : qEH ≠ qOut) (α : BitAssignment n) :
    (cToggleNotRaw2 qNH qEH qOut hNO hEO).eval.1.mulVec (ket α) =
    ket (toggleNotRaw2Bits qNH qEH qOut α) := by
  dsimp only [cToggleNotRaw2, toggleNotRaw2Bits];
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_X, ket_CNOT, ket_CNOT]
  refine congrArg ket (funext fun u ↦ ?_)
  by_cases hu : u = qOut
  · subst hu;
    simp only [Function.update_self, Function.update_of_ne hNO, Function.update_of_ne hEO,
        add_assoc]
  · simp only [Function.update_of_ne hu]

theorem cToggleNotRaw2_mul_self {n : ℕ} (qNH qEH qOut : Wire n) (hNO : qNH ≠ qOut)
    (hEO : qEH ≠ qOut) : (cToggleNotRaw2 qNH qEH qOut hNO hEO).eval.1 *
    (cToggleNotRaw2 qNH qEH qOut hNO hEO).eval.1 = 1 := by
  have h2z : ∀ x : ZMod 2, x + x = 0 := by decide
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, cToggleNotRaw2_mulVec_ket,
      cToggleNotRaw2_mulVec_ket]
  refine congrArg ket (funext fun u ↦ ?_)
  dsimp only [toggleNotRaw2Bits]
  by_cases hu : u = qOut
  · subst hu; simp only [Function.update_self, Function.update_of_ne hNO, Function.update_of_ne hEO]
    calc (α u + 1 + α qNH + α qEH) + 1 + α qNH + α qEH
        = α u + (1 + 1) + (α qNH + α qNH) + (α qEH + α qEH) := by ring
      _ = α u := by rw [h2z, h2z, h2z, add_zero, add_zero, add_zero]
  · simp only [Function.update_of_ne hu]

theorem rawN_ne_qScrNotE {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} (w : SharedPortBWiring rN rE cHiN) : rRawHas2 rN ≠ qScrNotE rE :=
  w.pubN_ne_pubE (i := ⟨1, rw_lt1 47 6⟩) (j := ⟨66 + 12, rw_ltHA 187 8 ⟨12, by decide⟩⟩)
    (by dsimp [routerWidth]; omega) (by dsimp; omega)

theorem rawE_ne_qScrNotE {n : ℕ} (rE : RouterReg 187 8 n) : rRawHas2 rE ≠ qScrNotE rE :=
  rr_ne rE (by dsimp [routerWidth]; omega)

theorem qScrNotE_ne_bufLoN {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} (w : SharedPortBWiring rN rE cHiN) (k : Fin 24) : qScrNotE rE ≠
    rBufLo rN k :=
  (w.pubN_ne_pubE (i := ⟨14 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩)
    (j := ⟨66 + 12, rw_ltHA 187 8 ⟨12, by decide⟩⟩)
    (by have := k.isLt; dsimp; omega) (by dsimp; omega)).symm

theorem qScrNotE_ne_bufHiE {n : ℕ} (rE : RouterReg 187 8 n) (k : Fin 24) : qScrNotE rE ≠
    rBufHi rE k :=
  rr_ne rE (by have := k.isLt; dsimp [routerWidth]; omega)

theorem bufLoN_ne_bufHiE {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} (w : SharedPortBWiring rN rE cHiN) (k₁ k₂ : Fin 24) : rBufLo rN k₁ ≠
    rBufHi rE k₂ :=
  w.pubN_ne_pubE (i := ⟨14 + k₁.val, by have := k₁.isLt; dsimp [routerWidth]; omega⟩)
    (j := ⟨42 + k₂.val, by have := k₂.isLt; dsimp [routerWidth]; omega⟩)
    (by have := k₁.isLt; dsimp; omega) (by have := k₂.isLt; dsimp; omega)

def wC235 {n : ℕ} (cHiN : Fin 47 → Wire n) (rE : RouterReg 187 8 n) : Fin ((47 + 187) + 1) →
    Wire n := appendFin (appendFin cHiN (rCtrlLo rE)) (fun _ : Fin 1 ↦ qScrNotE rE)
def sysNE235 {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (k : Fin 24) : Fin ((47 + 187) + 1) → Wire n :=
    appendFin (appendFin (fun p ↦ pSys (planeOfRouter rN k) p)
    (fun q ↦ pSys (planeOfRouter rE k) q)) (fun _ : Fin 1 ↦ rBufLo rN k)
theorem hBC_235 {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n} {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) : ∀ (k : Fin 24) (i : Fin ((47 + 187) + 1)), rBufHi rE k ≠
    wC235 cHiN rE i :=
  fun k ↦ appendFin_cases
    (fun i₀ ↦ by dsimp only [wC235]; rw [appendFin_castAdd]; exact w.hBC_NE k i₀)
    (fun _ ↦ by dsimp only [wC235]; rw [appendFin_natAdd]; exact (qScrNotE_ne_bufHiE rE k).symm)

theorem hBT_235_all {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} (w : SharedPortBWiring rN rE cHiN) : ∀ (k₁ k₂ : Fin 24)
    (i : Fin ((47 + 187) + 1)), rBufHi rE k₁ ≠ sysNE235 rN rE k₂ i :=
  fun k₁ k₂ ↦ appendFin_cases
    (fun i₀ ↦ by dsimp only [sysNE235]; rw [appendFin_castAdd]; exact w.hBT_NE_all k₁ k₂ i₀)
    (fun _ ↦ by dsimp only [sysNE235]; rw [appendFin_natAdd]; exact (bufLoN_ne_bufHiE w k₂ k₁).symm)

theorem hCT_235_all {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} (w : SharedPortBWiring rN rE cHiN) (hCtrlEBufN : ∀ (q : Fin 187)
    (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) : ∀ (k : Fin 24) (i j : Fin ((47 + 187) + 1)),
    wC235 cHiN rE i ≠ sysNE235 rN rE k j :=
  fun k ↦ appendFin_cases
    (fun i₀ ↦ appendFin_cases
      (fun j₀ ↦ by
        dsimp only [wC235, sysNE235]; rw [appendFin_castAdd, appendFin_castAdd]
        exact w.hCT_NE_all k i₀ j₀)
      (fun _ ↦ by
        dsimp only [wC235, sysNE235]; rw [appendFin_castAdd, appendFin_natAdd]
        rcases appendFin_eq i₀ with ⟨p, rfl⟩ | ⟨q, rfl⟩
        · rw [appendFin_castAdd]; exact fun e ↦ w.cHiN_notModN p (e ▸ ⟨k, Or.inl rfl⟩)
        · rw [appendFin_natAdd]; exact hCtrlEBufN q k))
    (fun _ ↦ appendFin_cases
      (fun j₀ ↦ by
        dsimp only [wC235, sysNE235]; rw [appendFin_natAdd, appendFin_castAdd]
        rcases appendFin_eq j₀ with ⟨p, rfl⟩ | ⟨q, rfl⟩
        · rw [appendFin_castAdd, planeOfRouter_sys]
          exact (w.pubN_ne_pubE
            (i := ⟨110 + 24 * p.val + k.val,
                by have := p.isLt; have := k.isLt; dsimp [routerWidth]; omega⟩)
            (j := ⟨66 + 12, rw_ltHA 187 8 ⟨12, by decide⟩⟩)
            (by have := p.isLt; have := k.isLt; dsimp; omega) (by dsimp; omega)).symm
        · rw [appendFin_natAdd, planeOfRouter_sys]
          exact rr_ne rE (by have := q.isLt; have := k.isLt; dsimp [routerWidth]; omega))
      (fun _ ↦ by
        dsimp only [wC235, sysNE235]; rw [appendFin_natAdd, appendFin_natAdd]
        exact qScrNotE_ne_bufLoN w k))

theorem ket_sr_eq_xm {n : ℕ} (α : BitAssignment n) :
    PhotochemistrySolution.SplitRouterSeqBell26k.ket α = ket α := rfl

theorem rBufHi_inj {M D n : ℕ} (r : RouterReg M D n) : Function.Injective (rBufHi r) :=
  fun k₁ k₂ e ↦ Fin.ext (by
    have hv := congrArg Fin.val (r.wires.injective e)
    have := k₁.isLt; have := k₂.isLt; dsimp [rBufHi] at hv; omega)

theorem rBufLo_inj {M D n : ℕ} (r : RouterReg M D n) : Function.Injective (rBufLo r) :=
  fun k₁ k₂ e ↦ Fin.ext (by
    have hv := congrArg Fin.val (r.wires.injective e)
    have := k₁.isLt; have := k₂.isLt; dsimp [rBufLo] at hv; omega)

attribute [local irreducible] systemQubits_frozen

attribute [local semireducible]
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  ComputeProg.fwdBits
  PhotochemistrySolution.SplitBellVecCleanStep.cnotFanoutCirc
  PhotochemistrySolution.SplitBellVecCleanStep.specFanoutCopyCirc
  PhotochemistrySolution.SplitBellVecCleanStep.specFanoutCopyVecCirc
  PhotochemistrySolution.SplitBellVecCleanStep.bellXHalf1Dyn
  PhotochemistrySolution.SplitBellVecCleanStep.bellXHalfVecDyn

def xorNotRaw2Bits {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n) (α : BitAssignment n) :
    BitAssignment n :=
    DynCircExt.writeReg α ⟨rBufHi rE, rBufHi_inj rE⟩
    (fun k ↦ α (rBufHi rE k) + (1 + α (rRawHas2 rN) + α (rRawHas2 rE)) * α (rBufLo rN k))
theorem xorNotRaw2Bits_apply {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (α : BitAssignment n) : (∀ k : Fin 24, xorNotRaw2Bits rN rE α (rBufHi rE k) = α (rBufHi rE k) +
    (1 + α (rRawHas2 rN) + α (rRawHas2 rE)) * α (rBufLo rN k)) ∧ (∀ u : Wire n, (∀ k : Fin 24, u ≠
    rBufHi rE k) → xorNotRaw2Bits rN rE α u = α u) := by
  let rEB : QRegister 24 n := ⟨rBufHi rE, rBufHi_inj rE⟩
  exact ⟨fun k ↦ DynCircExt.writeReg_apply_reg α rEB _ k, fun u hE ↦
      DynCircExt.writeReg_apply_of_not_mem α rEB _ u (fun ⟨k, hk⟩ ↦ hE k hk.symm)⟩

def SharedHi235Pred {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (α : BitAssignment n) : Prop :=
    (∀ p : Fin 47, α (cHiN p) = 0) ∧ (∀ q : Fin 187, α (rCtrlLo rE q) = 0) ∧ UnloadHiPred rN α ∧
    UnloadHiPred rE α ∧ (α (rRawHas2 rN) = 1 → α (rRawHas2 rE) = 0) ∧
    (∀ k : Fin 24, α (rBufHi rE k) = 0) ∧ α (qScrNotE rE) = 0
def Stage5SharedHi235ElecFootprint {n : ℕ} (rE : RouterReg 187 8 n) (u : Wire n) : Prop :=
    ∃ j : Fin (routerWidth 187 8), u = rE j ∧ (j.val < 18 ∨ (42 ≤ j.val ∧ j.val < 66) ∨ j.val = 78 ∨
    (90 ≤ j.val ∧ j.val < 97) ∨ (114 ≤ j.val ∧ j.val < 4602) ∨ (4624 ≤ j.val ∧ j.val < 4811))
def pUnloadSharedHiPortOnly235Inner {Var : Type} {n : ℕ} (v : Var) (rN : RouterReg 47 6 n)
    (rE : RouterReg 187 8 n) (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN)
    (hCtrlEBufN : ∀ (q : Fin 187) (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) (s7 : Fin 7 → Wire n) :
    DynamicCircuit Var n :=
    wrapWRouterHi47 v (rRawHas2 rN) (rIdx2 rN) (padWires cHiN (padNOfS7 s7)) (qEncOfS7 s7)
    (wWrapHi187_366 v (rRawHas2 rE) (rIdx2 rE) (padWires (rCtrlLo rE) (padEOfS7 s7)) (qEncOfS7 s7)
    (bellXHalfVecDyn v ((47 + 187) + 1) 24 (rBufHi rE) (wC235 cHiN rE) (sysNE235 rN rE)
    (fun k i ↦ hCT_235_all w hCtrlEBufN k i i)))
def pUnloadSharedHiPortOnly235WState_452 {Var : Type} {n : ℕ} (v : Var) (rN : RouterReg 47 6 n)
    (rE : RouterReg 187 8 n) (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN)
    (hCtrlEBufN : ∀ (q : Fin 187) (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) (s7 : Fin 7 → Wire n) :
    DynamicCircuit Var n :=
  let cTog :=
      cToggleNotRaw2 (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE) (rawN_ne_qScrNotE w)
      (rawE_ne_qScrNotE rE)
  .seq (.circuit cTog)
    (.seq (pUnloadSharedHiPortOnly235Inner v rN rE cHiN w hCtrlEBufN s7)
      (.circuit cTog))

def pUnloadSharedHiPortOnly235HBEWState_452 {Var : Type} {n : ℕ} (v : Var) (rN : RouterReg 47 6 n)
    (rE : RouterReg 187 8 n) (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN)
    (hCtrlEBufN : ∀ (q : Fin 187) (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) :
    DynamicCircuit Var n :=
    pUnloadSharedHiPortOnly235WState_452 v rN rE cHiN w hCtrlEBufN (s7OfHBE rE)
theorem count_pUnloadSharedHiPortOnly235WState_452 {Var : Type} {n : ℕ} (v : Var)
    (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n) (cHiN : Fin 47 → Wire n)
    (w : SharedPortBWiring rN rE cHiN) (hCtrlEBufN : ∀ (q : Fin 187) (k : Fin 24), rCtrlLo rE q ≠
    rBufLo rN k) (s7 : Fin 7 → Wire n) :
    (pUnloadSharedHiPortOnly235WState_452 v rN rE cHiN w hCtrlEBufN s7).count .T = 452 ∧
    (pUnloadSharedHiPortOnly235WState_452 v rN rE cHiN w hCtrlEBufN s7).count .TOFF = 0 := by
  unfold pUnloadSharedHiPortOnly235WState_452 pUnloadSharedHiPortOnly235Inner;
  obtain ⟨tTog, fTog⟩ :=
      counts_cToggleNotRaw2 (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE) (rawN_ne_qScrNotE w)
      (rawE_ne_qScrNotE rE); obtain ⟨tOut, fOut⟩ :=
      count_wrapWRouterHi47 v (rRawHas2 rN) (rIdx2 rN) (padWires cHiN (padNOfS7 s7))
      (qEncOfS7 s7) _; obtain ⟨tIn, fIn⟩ :=
      count_wWrapHi187_366 v (rRawHas2 rE) (rIdx2 rE) (padWires (rCtrlLo rE) (padEOfS7 s7))
      (qEncOfS7 s7) _; dsimp only [DynamicCircuit.count]; rw [tTog, fTog, tOut, fOut, tIn,
      fIn]; simp [count_bellXHalfVecDyn_t, count_bellXHalfVecDyn_toff]
theorem dynWires_pUnloadSharedHiPortOnly235WState_452_exact {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n) (cHiN : Fin 47 → Wire n)
    (w : SharedPortBWiring rN rE cHiN) (hCtrlEBufN : ∀ (q : Fin 187) (k : Fin 24), rCtrlLo rE q ≠
    rBufLo rN k) (s7 : Fin 7 → Wire n) (hRawN : S (rRawHas2 rN))
    (hIdx2N : ∀ d : Fin 6, S (rIdx2 rN d)) (hBufLoN : ∀ k : Fin 24, S (rBufLo rN k))
    (hSysN : ∀ (p : Fin 47) (k : Fin 24), S (rSys rN p k))
    (hrE : ∀ u, Stage5SharedHi235ElecFootprint rE u → S u) (hcHiN : ∀ p : Fin 47, S (cHiN p))
    (hs7 : ∀ j : Fin 7, S (s7 j)) :
    DynWires S (pUnloadSharedHiPortOnly235WState_452 v rN rE cHiN w hCtrlEBufN s7) := by
  have hRawE : S (rRawHas2 rE) :=
    hrE _ ⟨Fin.mk 1 (rw_lt1 187 8), rfl, Or.inl (by dsimp [routerWidth]; omega)⟩
  have hScrE : S (qScrNotE rE) :=
    hrE _ ⟨⟨66 + 12, rw_ltHA 187 8 ⟨12, by decide⟩⟩, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  have hCtrlE : ∀ q : Fin 187, S (rCtrlLo rE q) := fun q ↦
    hrE _ ⟨⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩, rfl,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by dsimp [basePub]; omega,
          by have := q.isLt; dsimp [basePub]; omega⟩))))⟩
  have hBufHiE : ∀ k : Fin 24, S (rBufHi rE k) := fun k ↦
    hrE _ ⟨⟨42 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩, rfl,
      Or.inr (Or.inl ⟨by dsimp; omega, by have := k.isLt; dsimp; omega⟩)⟩
  have hSysE : ∀ (q : Fin 187) (k : Fin 24), S (rSys rE q k) := fun q k ↦
    hrE _ ⟨⟨114 + 24 * q.val + k.val,
        by have := q.isLt; have := k.isLt; dsimp [routerWidth]; omega⟩, rfl,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega,
          by have := q.isLt; have := k.isLt; dsimp; omega⟩))))⟩
  have hC235 : ∀ i : Fin ((47 + 187) + 1), S (wC235 cHiN rE i) :=
    appendFin_cases
      (appendFin_cases
        (fun p ↦ by dsimp only [wC235]; rw [appendFin_castAdd, appendFin_castAdd]; exact hcHiN p)
        (fun q ↦ by dsimp only [wC235]; rw [appendFin_castAdd, appendFin_natAdd]; exact hCtrlE q))
      (fun _ ↦ by dsimp only [wC235]; rw [appendFin_natAdd]; exact hScrE)
  have hT235 : ∀ (k : Fin 24) (i : Fin ((47 + 187) + 1)), S (sysNE235 rN rE k i) :=
    fun k ↦ appendFin_cases
      (appendFin_cases
        (fun p ↦
            by dsimp only [sysNE235]; rw [appendFin_castAdd, appendFin_castAdd,
                 planeOfRouter_sys]; exact hSysN p k)
        (fun q ↦
            by dsimp only [sysNE235]; rw [appendFin_castAdd, appendFin_natAdd,
                 planeOfRouter_sys]; exact hSysE q k))
      (fun _ ↦ by dsimp only [sysNE235]; rw [appendFin_natAdd]; exact hBufLoN k)
  have cwT : CircWires S (cToggleNotRaw2 (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE)
      (rawN_ne_qScrNotE w) (rawE_ne_qScrNotE rE)) :=
    ⟨⟨fun _ ↦ hScrE, fun | ⟨0, _⟩ => hRawN | ⟨1, _⟩ => hScrE⟩,
     fun | ⟨0, _⟩ => hRawE | ⟨1, _⟩ => hScrE⟩
  exact ⟨cwT,
    dynWires_wrapWRouterHi47 v _ _ _ _ _
      hRawN hIdx2N (padWires_mem hcHiN fun _ ↦ hs7 _) (hs7 _)
      (dynWires_wWrapHi187_366 v _ _ _ _ _
        hRawE
        (fun d ↦ hrE _ ⟨⟨2 + 8 + d.val, rw_ltIdx2 d⟩, rfl,
            Or.inl (by have := d.isLt; dsimp; omega)⟩)
        (padWires_mem hCtrlE fun i ↦ hs7 ⟨1 + i.val, by omega⟩)
        (hs7 _)
        (dynWires_bellXHalfVecDyn_gen v 24 _ _ _ _ hBufHiE hC235 hT235)),
    cwT⟩

def uSharedHi235Inner {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN) (hCtrlEBufN : ∀ (q : Fin 187)
    (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) : Operator (2 ^ n) :=
  let F_N := (fwdCirc (pDecHiNOn rN rE cHiN w)).eval
  let F_E := (fwdCirc (pDecHiESorted rE)).eval
  let C_235 :=
      (specFanoutCopyVecCirc ((47 + 187) + 1) 24 (rBufHi rE) (wC235 cHiN rE) (sysNE235 rN rE)
      (hBC_235 w) (fun k ↦ hBT_235_all w k k) (fun k i ↦ hCT_235_all w hCtrlEBufN k i i)).eval.1
  let S_235 :=
      (portSwapVecCirc ((47 + 187) + 1) 24 (rBufHi rE) (wC235 cHiN rE) (sysNE235 rN rE) (hBC_235 w)
      (fun k ↦ hBT_235_all w k k) (fun k i ↦ hCT_235_all w hCtrlEBufN k i i)).eval.1
  (F_N⁻¹).1 * ((F_E⁻¹).1 * (C_235 * (S_235 * (F_E.1 * F_N.1))))

def uSharedHi235Conj {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN) (hCtrlEBufN : ∀ (q : Fin 187)
    (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) : Operator (2 ^ n) :=
  let T_tog :=
      (cToggleNotRaw2 (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE) (rawN_ne_qScrNotE w)
      (rawE_ne_qScrNotE rE)).eval.1
  T_tog * (uSharedHi235Inner rN rE cHiN w hCtrlEBufN * T_tog)

theorem portSwap1Bits_zero_ctrl {n : ℕ} :
    ∀ (M : ℕ) (qB : Wire n) (wC wT : Fin M → Wire n) (δ : BitAssignment n),
      (∀ p : Fin M, qB ≠ wC p) → (∀ p q : Fin M, wC p ≠ wT q) →
      (∀ p : Fin M, δ (wC p) = 0) →
      portSwap1Bits M qB wC wT δ = δ
  | 0, _, _, _, _, _, _, _ => rfl
  | M + 1, qB, wC, wT, δ, hbc, hct, hz => by
      dsimp only [portSwap1Bits]
      rw [portSwap1Bits_zero_ctrl M qB (fun p ↦ wC p.castSucc)
          (fun p ↦ wT p.castSucc) δ (fun p ↦ hbc p.castSucc) (fun p q ↦ hct p.castSucc q.castSucc)
          (fun p ↦ hz p.castSucc), hz (Fin.last M), zero_mul, add_zero, add_zero,
          Function.update_eq_self, Function.update_eq_self]

theorem fanoutXorBits_zero_ctrl {n : ℕ} :
    ∀ (M : ℕ) (wC wT : Fin M → Wire n) (δ : BitAssignment n),
      (∀ p q : Fin M, wC p ≠ wT q) → (∀ p : Fin M, δ (wC p) = 0) →
      fanoutXorBits M wC wT δ = δ
  | 0, _, _, _, _, _ => rfl
  | M + 1, wC, wT, δ, hct, hz => by
      dsimp only [fanoutXorBits]
      rw [fanoutXorBits_zero_ctrl M (fun p ↦ wC p.castSucc) (fun p ↦ wT p.castSucc) δ (fun p q ↦
          hct p.castSucc q.castSucc) (fun p ↦ hz p.castSucc), hz (Fin.last M), add_zero,
          Function.update_eq_self]

theorem appendFin_one_castSucc {M : ℕ} {α : Type*} (f : Fin M → α)
    (x : α) : (fun p : Fin M ↦ appendFin f (fun _ : Fin 1 ↦ x) p.castSucc) = f :=
  funext fun p ↦ appendFin_castAdd f (fun _ : Fin 1 ↦ x) p

theorem appendFin_one_last {M : ℕ} {α : Type*} (f : Fin M → α)
    (x : α) : appendFin f (fun _ : Fin 1 ↦ x) (Fin.last M) = x :=
  appendFin_natAdd f (fun _ : Fin 1 ↦ x) ⟨0, by decide⟩

theorem portSwap1Bits_succ {n M : ℕ} (qB : Wire n) (wCtrl wTgt : Fin (M + 1) → Wire n)
    (β : BitAssignment n) :
    portSwap1Bits (M + 1) qB wCtrl wTgt β =
      let β' := portSwap1Bits M qB (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc) β
      let d := β' (wCtrl (Fin.last M)) * (β' (wTgt (Fin.last M)) + β' qB)
      Function.update (Function.update β' qB (β' qB + d))
        (wTgt (Fin.last M)) (β' (wTgt (Fin.last M)) + d) := rfl

theorem fanoutXorBits_succ {n M : ℕ} (wCtrl wTgt : Fin (M + 1) → Wire n)
    (β : BitAssignment n) :
    fanoutXorBits (M + 1) wCtrl wTgt β =
      let β' := fanoutXorBits M (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc) β
      Function.update β' (wTgt (Fin.last M)) (β' (wTgt (Fin.last M)) + β' (wCtrl (Fin.last M))) :=
          rfl

theorem portSwapVecCirc_235_eq_234_of_q0 {n : ℕ}
    {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n} {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN)
    (hCtrlEBufN : ∀ (q : Fin 187) (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) :
    ∀ (m : ℕ) (hm : m ≤ 24) (δ : BitAssignment n), δ (qScrNotE rE) = 0 →
      let qBm : Fin m → Wire n := fun k ↦ rBufHi rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩
      let sys234m : Fin m → Fin (47 + 187) → Wire n := fun k ↦
          appendFin (fun p ↦ pSys (planeOfRouter rN ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩) p)
          (fun q ↦ pSys (planeOfRouter rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩) q)
      let sys235m : Fin m → Fin ((47 + 187) + 1) → Wire n := fun k ↦
          sysNE235 rN rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩
      (portSwapVecCirc ((47 + 187) + 1) m qBm (wC235 cHiN rE) sys235m
        (fun _k ↦ hBC_235 w _) (fun _k ↦ hBT_235_all w _ _)
        (fun _k i ↦ hCT_235_all w hCtrlEBufN _ i i)).eval.1.mulVec (ket δ) =
      (portSwapVecCirc (47 + 187) m qBm (appendFin cHiN (rCtrlLo rE)) sys234m
        (fun _k ↦ w.hBC_NE _) (fun _k ↦ w.hBT_NE_all _ _)
        (fun _k i ↦ w.hCT_NE_all _ i i)).eval.1.mulVec (ket δ)
  | 0, _, δ, _ => by
      intros; unfold portSwapVecCirc; rfl
  | m + 1, hm, δ, hq0 => by
      dsimp only;
      have ih :=
          portSwapVecCirc_235_eq_234_of_q0 w hCtrlEBufN m (Nat.le_of_succ_le hm) δ hq0; dsimp only
          at ih
      obtain ⟨ζ₀, hζ₀, hEq₀⟩ :=
          portSwapVecCirc_ket_preserve (47 + 187) m (fun k ↦ rBufHi rE ⟨k.val,
          Nat.lt_of_lt_of_le k.isLt (Nat.le_of_succ_le hm)⟩) (appendFin cHiN (rCtrlLo rE))
          (fun k ↦ appendFin (fun p ↦ pSys (planeOfRouter rN ⟨k.val,
          Nat.lt_of_lt_of_le k.isLt (Nat.le_of_succ_le hm)⟩) p)
          (fun q ↦ pSys (planeOfRouter rE ⟨k.val,
          Nat.lt_of_lt_of_le k.isLt (Nat.le_of_succ_le hm)⟩) q)) (fun _ ↦ w.hBC_NE _)
          (fun _ ↦ w.hBT_NE_all _ _) (fun _ i ↦ w.hCT_NE_all _ i i) δ
      have hneS (b : Fin 24) (i : Fin (47 + 187)) :
          qScrNotE rE ≠ appendFin (fun p ↦ pSys (planeOfRouter rN b) p)
            (fun q ↦ pSys (planeOfRouter rE b) q) i := by
        simpa only [wC235, sysNE235, appendFin_natAdd, appendFin_castAdd] using
          hCT_235_all w hCtrlEBufN b (Fin.natAdd (47 + 187) ⟨0, by decide⟩) (Fin.castAdd 1 i)
      have hζq0 : ζ₀ (qScrNotE rE) = 0 := (hEq₀ _ (fun _ ↦ qScrNotE_ne_bufHiE rE _)
        fun k ↦ hneS ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.le_of_succ_le hm)⟩).trans hq0
      unfold portSwapVecCirc; rw [eval_seq_mulVec, eval_seq_mulVec];
      dsimp only [Fin.val_castSucc, Fin.val_last];
      rw [ih, hζ₀, ← ket_sr_eq_xm, portSwap1Circ_mulVec_ket, portSwap1Circ_mulVec_ket];
      refine congrArg SplitRouterSeqBell26k.ket ?_; rw [portSwap1Bits_succ];
      dsimp only [wC235, sysNE235]
      rw [appendFin_one_castSucc, appendFin_one_castSucc, appendFin_one_last, appendFin_one_last,
          (portSwap1Bits_of_ne (47 + 187) (rBufHi rE ⟨m, hm⟩) (appendFin cHiN (rCtrlLo rE))
            _ ζ₀ (qScrNotE rE) (qScrNotE_ne_bufHiE rE _) (hneS ⟨m, hm⟩)).trans hζq0,
          zero_mul, add_zero, add_zero, Function.update_eq_self, Function.update_eq_self]

theorem specFanoutCopyVecCirc_235_eq_234_of_q0 {n : ℕ}
    {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n} {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN)
    (hCtrlEBufN : ∀ (q : Fin 187) (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) :
    ∀ (m : ℕ) (hm : m ≤ 24) (δ : BitAssignment n), δ (qScrNotE rE) = 0 →
      let qBm : Fin m → Wire n := fun k ↦ rBufHi rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩
      let sys234m : Fin m → Fin (47 + 187) → Wire n := fun k ↦
          appendFin (fun p ↦ pSys (planeOfRouter rN ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩) p)
          (fun q ↦ pSys (planeOfRouter rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩) q)
      let sys235m : Fin m → Fin ((47 + 187) + 1) → Wire n := fun k ↦
          sysNE235 rN rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩
      (specFanoutCopyVecCirc ((47 + 187) + 1) m qBm (wC235 cHiN rE) sys235m
        (fun _k ↦ hBC_235 w _) (fun _k ↦ hBT_235_all w _ _)
        (fun _k i ↦ hCT_235_all w hCtrlEBufN _ i i)).eval.1.mulVec (ket δ) =
      (specFanoutCopyVecCirc (47 + 187) m qBm (appendFin cHiN (rCtrlLo rE)) sys234m
        (fun _k ↦ w.hBC_NE _) (fun _k ↦ w.hBT_NE_all _ _)
        (fun _k i ↦ w.hCT_NE_all _ i i)).eval.1.mulVec (ket δ)
  | 0, _, δ, _ => by
      intros; unfold specFanoutCopyVecCirc; rfl
  | m + 1, hm, δ, hq0 => by
      dsimp only;
      have ih :=
          specFanoutCopyVecCirc_235_eq_234_of_q0 w hCtrlEBufN m (Nat.le_of_succ_le hm) δ hq0; dsimp
          only at ih
      obtain ⟨ζ₀, hζ₀, hEq₀⟩ :=
          specFanoutCopyVecCirc_ket_preserve (47 + 187) m (fun k ↦ rBufHi rE ⟨k.val,
          Nat.lt_of_lt_of_le k.isLt (Nat.le_of_succ_le hm)⟩) (appendFin cHiN (rCtrlLo rE))
          (fun k ↦ appendFin (fun p ↦ pSys (planeOfRouter rN ⟨k.val,
          Nat.lt_of_lt_of_le k.isLt (Nat.le_of_succ_le hm)⟩) p)
          (fun q ↦ pSys (planeOfRouter rE ⟨k.val,
          Nat.lt_of_lt_of_le k.isLt (Nat.le_of_succ_le hm)⟩) q)) (fun _ ↦ w.hBC_NE _)
          (fun _ ↦ w.hBT_NE_all _ _) (fun _ i ↦ w.hCT_NE_all _ i i) δ
      have hneS (b : Fin 24) (i : Fin (47 + 187)) :
          qScrNotE rE ≠ appendFin (fun p ↦ pSys (planeOfRouter rN b) p)
            (fun q ↦ pSys (planeOfRouter rE b) q) i := by
        simpa only [wC235, sysNE235, appendFin_natAdd, appendFin_castAdd] using
          hCT_235_all w hCtrlEBufN b (Fin.natAdd (47 + 187) ⟨0, by decide⟩) (Fin.castAdd 1 i)
      have hζq0 : ζ₀ (qScrNotE rE) = 0 :=
        (hEq₀ _ fun k ↦ hneS ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.le_of_succ_le hm)⟩).trans hq0
      unfold specFanoutCopyVecCirc; rw [eval_seq_mulVec, eval_seq_mulVec];
      dsimp only [Fin.val_castSucc, Fin.val_last];
      rw [ih, hζ₀, specFanoutCopyCirc_mulVec_ket, specFanoutCopyCirc_mulVec_ket];
      refine congrArg ket ?_
      split_ifs with hb0
      · rfl
      · rw [fanoutXorBits_succ]; dsimp only [wC235, sysNE235]
        rw [appendFin_one_castSucc, appendFin_one_castSucc, appendFin_one_last, appendFin_one_last,
            (fanoutXorBits_of_ne_tgt (47 + 187) (appendFin cHiN (rCtrlLo rE))
              _ ζ₀ (qScrNotE rE) (hneS ⟨m, hm⟩)).trans hζq0,
            add_zero, Function.update_eq_self]

theorem portSwapAndCopy_235_of_q1 {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} (w : SharedPortBWiring rN rE cHiN) (hCtrlEBufN : ∀ (q : Fin 187)
    (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) {δ : BitAssignment n}
    (hc0 : ∀ i : Fin (47 + 187), δ (appendFin cHiN (rCtrlLo rE) i) = 0) (hq1 : δ (qScrNotE rE) = 1)
    (hB0 : ∀ k : Fin 24, δ (rBufHi rE k) = 0) : (specFanoutCopyVecCirc ((47 + 187) +
    1) 24 (rBufHi rE) (wC235 cHiN rE) (sysNE235 rN rE) (hBC_235 w) (fun k ↦ hBT_235_all w k k)
    (fun k i ↦ hCT_235_all w hCtrlEBufN k i i)).eval.1.mulVec ((portSwapVecCirc ((47 + 187) +
    1) 24 (rBufHi rE) (wC235 cHiN rE) (sysNE235 rN rE) (hBC_235 w) (fun k ↦ hBT_235_all w k k)
    (fun k i ↦ hCT_235_all w hCtrlEBufN k i i)).eval.1.mulVec (ket δ)) =
    ket (DynCircExt.writeReg δ ⟨rBufHi rE, rBufHi_inj rE⟩ (fun k ↦ δ (rBufLo rN k))) := by
  have h2z : ∀ x : ZMod 2, x + x = 0 := by decide
  have hc_ne_bufN : ∀ (i : Fin (47 + 187)) (k : Fin 24), appendFin cHiN (rCtrlLo rE) i ≠
      rBufLo rN k :=
    fun i k ↦ by
      have := hCT_235_all w hCtrlEBufN k (Fin.castAdd 1 i) (Fin.natAdd (47 + 187) ⟨0, by decide⟩)
      dsimp only [wC235, sysNE235] at this; rwa [appendFin_castAdd, appendFin_natAdd] at this
  have hSw : ∀ (m : ℕ) (hm : m ≤ 24), ∃ ζ : BitAssignment n, (portSwapVecCirc ((47 + 187) +
      1) m (fun k ↦ rBufHi rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩) (wC235 cHiN rE)
      (fun k ↦ sysNE235 rN rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩) (fun _ ↦ hBC_235 w _)
      (fun _ ↦ hBT_235_all w _ _)
      (fun _ i ↦ hCT_235_all w hCtrlEBufN _ i i)).eval.1.mulVec (ket δ) = ket ζ ∧
      (∀ k : Fin 24, ζ (rBufHi rE k) = if k.val < m then δ (rBufLo rN k) else 0) ∧
      (∀ k : Fin 24, ζ (rBufLo rN k) = if k.val < m then 0 else δ (rBufLo rN k)) ∧
      (∀ u : Wire n, (∀ k, u ≠ rBufHi rE k) → (∀ k, u ≠ rBufLo rN k) → ζ u = δ u) := by
    intro m; induction m with
    | zero =>
        intro _
        refine ⟨δ, ?_, fun k ↦ by simp [hB0 k], fun k ↦ by simp, fun _ _ _ ↦ rfl⟩
        unfold portSwapVecCirc; rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    | succ m ihm =>
        intro hm; obtain ⟨ζ₀, hζ₀, hBζ₀, hNζ₀, hOζ₀⟩ := ihm (Nat.le_of_succ_le hm);
        let km : Fin 24 := ⟨m, hm⟩
        have hcζ₀ : ∀ i : Fin (47 + 187), ζ₀ (appendFin cHiN (rCtrlLo rE) i) = 0 := fun i ↦
            (hOζ₀ _ (fun k ↦ (w.hBC_NE k i).symm) (hc_ne_bufN i)).trans (hc0 i)
        have hqζ₀ : ζ₀ (qScrNotE rE) = 1 :=
            (hOζ₀ _ (qScrNotE_ne_bufHiE rE)
            (qScrNotE_ne_bufLoN w)).trans hq1; have hBkm : ζ₀ (rBufHi rE km) = 0 :=
                                                 (hBζ₀ km).trans (ite_eq_right (Nat.lt_irrefl m));
                                                 have hNkm : ζ₀ (rBufLo rN km) = δ (rBufLo rN km) :=
                                                 (hNζ₀ km).trans (ite_eq_right (Nat.lt_irrefl m));
                                                 let ζ₁ :=
                                                 Function.update (Function.update ζ₀ (rBufHi rE km)
                                                 (δ (rBufLo rN km))) (rBufLo rN km) 0
        refine ⟨ζ₁, ?_, fun k ↦ ?_, fun k ↦ ?_, fun u huB huN ↦ ?_⟩
        · unfold portSwapVecCirc
          rw [eval_seq_mulVec]; dsimp only [Fin.val_castSucc]
          rw [hζ₀, ← ket_sr_eq_xm, portSwap1Circ_mulVec_ket, ket_sr_eq_xm]; refine congrArg ket ?_;
          dsimp only [Fin.val_last]; rw [portSwap1Bits_succ]; dsimp only [wC235, sysNE235];
          rw [appendFin_one_castSucc, appendFin_one_castSucc, appendFin_one_last,
              appendFin_one_last, portSwap1Bits_zero_ctrl (47 + 187) (rBufHi rE km)
              (appendFin cHiN (rCtrlLo rE)) _ ζ₀ (w.hBC_NE km) (w.hCT_NE_all km) hcζ₀, hqζ₀, hBkm,
              hNkm, add_zero, one_mul, zero_add, h2z]
        · dsimp only [ζ₁]; rw [Function.update_of_ne (bufLoN_ne_bufHiE w km k).symm]
          by_cases hk : k = km
          · subst hk; rw [Function.update_self, ite_eq_left (Nat.lt_succ_self m)]
          · rw [Function.update_of_ne (fun e ↦ hk (rBufHi_inj rE e)), hBζ₀ k]
            have hne : k.val ≠ m := Fin.val_ne_of_ne hk
            split_ifs <;> first | rfl | omega
        · dsimp only [ζ₁]
          by_cases hk : k = km
          · subst hk
            rw [Function.update_self, ite_eq_left (Nat.lt_succ_self m)]
          · rw [Function.update_of_ne (fun e ↦ hk (rBufLo_inj rN e)),
                Function.update_of_ne (bufLoN_ne_bufHiE w k km), hNζ₀ k]
            have hne : k.val ≠ m := Fin.val_ne_of_ne hk
            split_ifs <;> first | rfl | omega
        · dsimp only [ζ₁]; rw [Function.update_of_ne (huN km), Function.update_of_ne (huB km)];
          exact hOζ₀ u huB huN
  obtain ⟨ζ₁, hζ₁, hBζ₁, hNζ₁, hOζ₁⟩ := hSw 24 le_rfl; rw [hζ₁]
  have hCp : ∀ (m : ℕ) (hm : m ≤ 24), ∃ η : BitAssignment n, (specFanoutCopyVecCirc ((47 + 187) +
      1) m (fun k ↦ rBufHi rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩) (wC235 cHiN rE)
      (fun k ↦ sysNE235 rN rE ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩) (fun _ ↦ hBC_235 w _)
      (fun _ ↦ hBT_235_all w _ _)
      (fun _ i ↦ hCT_235_all w hCtrlEBufN _ i i)).eval.1.mulVec (ket ζ₁) = ket η ∧
      (∀ k : Fin 24, η (rBufLo rN k) = if k.val < m then δ (rBufLo rN k) else 0) ∧
      (∀ u : Wire n, (∀ k, u ≠ rBufLo rN k) → η u = ζ₁ u) := by
    intro m; induction m with
    | zero =>
        intro _
        refine ⟨ζ₁, ?_, fun k ↦ (hNζ₁ k).trans (ite_eq_left k.isLt), fun _ _ ↦ rfl⟩
        unfold specFanoutCopyVecCirc;
        rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    | succ m ihm =>
        intro hm; obtain ⟨η₀, hη₀, hNη₀, hOη₀⟩ := ihm (Nat.le_of_succ_le hm);
        let km : Fin 24 := ⟨m, hm⟩
        have hcη₀ : ∀ i : Fin (47 + 187), η₀ (appendFin cHiN (rCtrlLo rE) i) = 0 := fun i ↦
            (hOη₀ _ (hc_ne_bufN i)).trans ((hOζ₁ _ (fun k ↦ (w.hBC_NE k i).symm)
            (hc_ne_bufN i)).trans (hc0 i))
        have hqη₀ : η₀ (qScrNotE rE) = 1 :=
            (hOη₀ _ (qScrNotE_ne_bufLoN w)).trans ((hOζ₁ _ (qScrNotE_ne_bufHiE rE)
            (qScrNotE_ne_bufLoN w)).trans hq1)
        have hBkm : η₀ (rBufHi rE km) = δ (rBufLo rN km) :=
            (hOη₀ _ (fun k ↦
            (bufLoN_ne_bufHiE w k km).symm)).trans ((hBζ₁ km).trans (ite_eq_left km.isLt))
        have hNkm : η₀ (rBufLo rN km) = 0 := (hNη₀ km).trans (ite_eq_right (Nat.lt_irrefl m));
        let η₁ := Function.update η₀ (rBufLo rN km) (δ (rBufLo rN km))
        refine ⟨η₁, ?_, fun k ↦ ?_, fun u huN ↦ ?_⟩
        · unfold specFanoutCopyVecCirc
          rw [eval_seq_mulVec]; dsimp only [Fin.val_castSucc]
          rw [hη₀, specFanoutCopyCirc_mulVec_ket]; refine congrArg ket ?_; dsimp only [Fin.val_last]
          rcases DynCircExt.bit_cases (δ (rBufLo rN km)) with hb0 | hb1
          · rw [ite_eq_left (hBkm.trans hb0)]; dsimp only [η₁]
            rw [hb0, ← hNkm, Function.update_eq_self]
          · rw [ite_eq_right (by rw [hBkm, hb1]; decide), fanoutXorBits_succ]
            dsimp only [wC235, sysNE235, η₁];
            rw [appendFin_one_castSucc, appendFin_one_castSucc, appendFin_one_last,
                appendFin_one_last, fanoutXorBits_zero_ctrl (47 + 187)
                (appendFin cHiN (rCtrlLo rE)) _ η₀ (w.hCT_NE_all km) hcη₀, hqη₀, hNkm, zero_add,
                hb1]
        · dsimp only [η₁]
          by_cases hk : k = km
          · subst hk; rw [Function.update_self, ite_eq_left (Nat.lt_succ_self m)]
          · rw [Function.update_of_ne (fun e ↦ hk (rBufLo_inj rN e)), hNη₀ k]
            have hne : k.val ≠ m := Fin.val_ne_of_ne hk
            split_ifs <;> first | rfl | omega
        · dsimp only [η₁]; rw [Function.update_of_ne (huN km)]; exact hOη₀ u huN
  obtain ⟨η₂, hη₂, hNη₂, hOη₂⟩ := hCp 24 le_rfl; rw [hη₂]
  refine congrArg ket (funext fun u ↦ ?_)
  let rEB : QRegister 24 n := ⟨rBufHi rE, rBufHi_inj rE⟩
  by_cases huB : ∃ k : Fin 24, u = rBufHi rE k
  · obtain ⟨k, rfl⟩ := huB
    change η₂ (rBufHi rE k) = DynCircExt.writeReg δ rEB (fun b ↦ δ (rBufLo rN b)) (rEB k)
    rw [DynCircExt.writeReg_apply_reg, hOη₂ _ (fun b ↦ (bufLoN_ne_bufHiE w b k).symm), hBζ₁ k,
        ite_eq_left k.isLt]
  · rw [DynCircExt.writeReg_apply_of_not_mem δ rEB _ u (fun ⟨k, hk⟩ ↦ huB ⟨k, hk.symm⟩)]
    by_cases huN : ∃ k : Fin 24, u = rBufLo rN k
    · obtain ⟨k, rfl⟩ := huN; exact (hNη₂ k).trans (ite_eq_left k.isLt)
    · exact (hOη₂ u (fun k e ↦ huN ⟨k, e⟩)).trans
        (hOζ₁ u (fun k e ↦ huB ⟨k, e⟩) (fun k e ↦ huN ⟨k, e⟩))

theorem portSwapVecCirc_zero_ctrl {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p)
      (hct : ∀ k p, wCtrl p ≠ wTgt k p) (_hct_all : ∀ k p q, wCtrl p ≠ wTgt k q)
      (δ : BitAssignment n), (∀ p : Fin M, δ (wCtrl p) = 0) →
      (portSwapVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1.mulVec (ket δ) = ket δ
  | 0, _, _, _, _, _, _, _, δ, _ => by
      unfold portSwapVecCirc; rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | m + 1, qB, wCtrl, wTgt, hbc, hbt, hct, hct_all, δ, hz => by
      unfold portSwapVecCirc
      rw [eval_seq_mulVec, portSwapVecCirc_zero_ctrl M m (fun k ↦ qB k.castSucc) wCtrl (fun k ↦
          wTgt k.castSucc) (fun k ↦ hbc k.castSucc) (fun k ↦ hbt k.castSucc)
          (fun k ↦ hct k.castSucc) (fun k ↦ hct_all k.castSucc) δ hz, ← ket_sr_eq_xm,
          portSwap1Circ_mulVec_ket, portSwap1Bits_zero_ctrl M _ wCtrl _ δ (hbc (Fin.last m))
          (hct_all (Fin.last m)) hz, ket_sr_eq_xm]

theorem specFanoutCopyVecCirc_zero_ctrl {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p)
      (hct : ∀ k p, wCtrl p ≠ wTgt k p) (_hct_all : ∀ k p q, wCtrl p ≠ wTgt k q)
      (δ : BitAssignment n), (∀ p : Fin M, δ (wCtrl p) = 0) →
      (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1.mulVec (ket δ) = ket δ
  | 0, _, _, _, _, _, _, _, δ, _ => by
      unfold specFanoutCopyVecCirc; rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | m + 1, qB, wCtrl, wTgt, hbc, hbt, hct, hct_all, δ, hz => by
      unfold specFanoutCopyVecCirc
      rw [eval_seq_mulVec, specFanoutCopyVecCirc_zero_ctrl M m (fun k ↦
          qB k.castSucc) wCtrl (fun k ↦ wTgt k.castSucc) (fun k ↦ hbc k.castSucc)
          (fun k ↦ hbt k.castSucc) (fun k ↦ hct k.castSucc) (fun k ↦ hct_all k.castSucc) δ hz,
          specFanoutCopyCirc_mulVec_ket]
      refine congrArg ket ?_; split_ifs
      · rfl
      · exact fanoutXorBits_zero_ctrl M wCtrl _ δ (hct_all (Fin.last m)) hz

theorem qScrNotE_not_portOnlyHiMod {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} (w : SharedPortBWiring rN rE cHiN) :
    ¬ PortOnlyHiMod rN rE (qScrNotE rE) := by
  rintro (⟨b, h⟩ | ⟨p, b, h⟩ | ⟨q, b, h⟩)
  · exact qScrNotE_ne_bufHiE rE b h
  · exact (w.pubN_ne_pubE
      (i := ⟨110 + 24 * p.val + b.val,
          by have := p.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩)
      (j := ⟨66 + 12, rw_ltHA 187 8 ⟨12, by decide⟩⟩)
      (by have := p.isLt; have := b.isLt; dsimp; omega) (by dsimp; omega)) h.symm
  · exact rr_ne rE (by have := q.isLt; have := b.isLt; dsimp [qScrNotE, routerWidth]; omega) h

theorem qScrNotE_ne_cHiN {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} (w : SharedPortBWiring rN rE cHiN) (p : Fin 47) : qScrNotE rE ≠
    cHiN p :=
  fun e ↦ w.cHiN_notModE p ⟨⟨12, by decide⟩, Or.inr (Or.inr (Or.inl e.symm))⟩

theorem qScrNotE_ne_ctrlE {n : ℕ} (rE : RouterReg 187 8 n) (q : Fin 187) : qScrNotE rE ≠
    rCtrlLo rE q :=
  rr_ne rE (by have := q.isLt; unfold basePub; dsimp [qScrNotE]; omega)

theorem uSharedHi235Conj_ket_eq_xorNotRaw2 {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN) (hCtrlEBufN : ∀ (q : Fin 187)
    (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k) {α : BitAssignment n}
    (hP : SharedHi235Pred rN rE cHiN α) : ∃ η₀ : BitAssignment n,
    (uSharedHiPortOnlyConj rN rE cHiN w).mulVec (ket α) = ket η₀ ∧
    (∀ u : Wire n, ¬ PortOnlyHiMod rN rE u → η₀ u = α u) ∧
    (uSharedHi235Inner rN rE cHiN w hCtrlEBufN).mulVec (ket (toggleNotRaw2Bits (rRawHas2 rN)
    (rRawHas2 rE) (qScrNotE rE) α)) = ket (toggleNotRaw2Bits (rRawHas2 rN) (rRawHas2 rE)
    (qScrNotE rE) (xorNotRaw2Bits rN rE η₀)) ∧
    (uSharedHi235Conj rN rE cHiN w hCtrlEBufN).mulVec (ket α) = ket (xorNotRaw2Bits rN rE η₀) := by
  obtain ⟨hcN, hcE, hPHiN, hPHiE, hExcl, hBufE0, hqScr0⟩ := hP; let pDecN := pDecHiNOn rN rE cHiN w;
  let pDecE := pDecHiESorted rE
  have hHdrN_nm : ∀ {u : Wire n}, RouterCtrlSet rN u → ¬ PortOnlyHiMod rN rE u := by
    intro u hh hm; obtain ⟨i, _, rfl⟩ := routerCtrlSet_pubIdx_nuc hh
    rcases hm with ⟨b, h⟩ | ⟨p, b, h⟩ | ⟨q, b, h⟩
    · exact w.rN_disj_rE_mod i _ ⟨b, Or.inr (Or.inl rfl)⟩ h
    · exact rr_ne rN (by have := p.isLt; have := b.isLt; dsimp; omega) h
    · exact w.rN_disj_rE_mod i _ ⟨b,
          Or.inr (Or.inr (Or.inr (Or.inr ⟨q, (planeOfRouter_sys rE b q).symm⟩)))⟩ h
  have hHdrE_nm : ∀ {u : Wire n}, RouterCtrlSet rE u → ¬ PortOnlyHiMod rN rE u := by
    intro u hh hm; obtain ⟨j, _, rfl⟩ := routerCtrlSet_pubIdx_elec hh
    rcases hm with ⟨b, h⟩ | ⟨p, b, h⟩ | ⟨q, b, h⟩
    · exact rr_ne rE (by have := b.isLt; dsimp; omega) h
    · exact (w.pubN_ne_pubE (i := ⟨110 + 24 * p.val + b.val,
        by have := p.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩)
        (by have := p.isLt; have := b.isLt; dsimp; omega) (by omega)) h.symm
    · exact rr_ne rE (by have := q.isLt; have := b.isLt; dsimp; omega) h
  rcases DynCircExt.bit_cases (1 + α (rRawHas2 rN) + α (rRawHas2 rE)) with hs0 | hs1
  · obtain ⟨η₀, hUHi, hOut⟩ := uSharedHiPortOnlyConj_ket_preserve rN rE cHiN w hcN hcE hPHiN hPHiE
    have hTogα : toggleNotRaw2Bits (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE) α = α := by
      unfold toggleNotRaw2Bits; rw [hqScr0, zero_add, hs0, ← hqScr0, Function.update_eq_self]
    have hηRawN : η₀ (rRawHas2 rN) = α (rRawHas2 rN) := hOut _ (hHdrN_nm (Or.inr (Or.inl rfl)));
    have hηRawE : η₀ (rRawHas2 rE) = α (rRawHas2 rE) := hOut _ (hHdrE_nm (Or.inr (Or.inl rfl)));
    have hηq0 : η₀ (qScrNotE rE) = 0 := (hOut _ (qScrNotE_not_portOnlyHiMod w)).trans hqScr0
    have hXorη : xorNotRaw2Bits rN rE η₀ = η₀ := by
      funext u
      by_cases huB : ∃ k : Fin 24, u = rBufHi rE k
      · obtain ⟨k, rfl⟩ :=
            huB; rw [(xorNotRaw2Bits_apply rN rE η₀).1 k, hηRawN, hηRawE, hs0, zero_mul, add_zero]
      · exact (xorNotRaw2Bits_apply rN rE η₀).2 u fun k e ↦ huB ⟨k, e⟩
    have hTogη : toggleNotRaw2Bits (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE) η₀ = η₀ := by
      unfold toggleNotRaw2Bits;
      rw [hηq0, zero_add, hηRawN, hηRawE, hs0, ← hηq0, Function.update_eq_self]
    have hInEq : (uSharedHi235Inner rN rE cHiN w hCtrlEBufN).mulVec (ket α) = ket η₀ := by
      obtain ⟨_, hγ₁Oth, _⟩ := spec_pDecHiNOn rN rE cHiN w α hcN hPHiN; let γ₁ := pDecN.fwdBits α
      have hγ₁CtrlE0 : ∀ q : Fin 187, γ₁ (rCtrlLo rE q) = 0 := fun q ↦
          (hγ₁Oth _ fun p ↦ (w.cHiN_ne_ctrlE p q).symm).trans (hcE q)
      have hγ₁RawE : γ₁ (rRawHas2 rE) = α (rRawHas2 rE) :=
        hγ₁Oth _ fun p e ↦ w.cHiN_notHdrE p (e ▸ Or.inr (Or.inl rfl))
      have hγ₁IdxE : ∀ d : Fin 8, γ₁ (rIdx2 rE d) = α (rIdx2 rE d) :=
        fun d ↦ hγ₁Oth _ fun p e ↦ w.cHiN_notHdrE p (e ▸ Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))
      have hPHiE_γ₁ : UnloadHiPred rE γ₁ := unloadHiPred_congr hγ₁RawE hγ₁IdxE hPHiE
      obtain ⟨_, hγ₂Oth, _⟩ := spec_pDecHi_sorted sorted187_hD1 sorted187_hMlo (by omega)
        (fun d hdlt ↦ sorted187_hPow d (sortedUnload_lt_of_sub hdlt)) rE γ₁ hγ₁CtrlE0 hPHiE_γ₁
      let γ₂ := pDecE.fwdBits γ₁;
      have hγ₂q0 : γ₂ (qScrNotE rE) = 0 :=
          (hγ₂Oth _ (qScrNotE_ne_ctrlE rE)).trans ((hγ₁Oth _ (qScrNotE_ne_cHiN w)).trans hqScr0)
      let sys234 : Fin 24 → Fin (47 + 187) → Wire n := fun k ↦
          appendFin (fun p ↦ pSys (planeOfRouter rN k) p) (fun q ↦ pSys (planeOfRouter rE k) q)
      obtain ⟨ζ₁, hζ₁, hEqζ₁⟩ :=
          portSwapVecCirc_ket_preserve (47 + 187) 24 (rBufHi rE)
          (appendFin cHiN (rCtrlLo rE)) sys234 w.hBC_NE (fun k ↦ w.hBT_NE_all k k)
          (fun k i ↦ w.hCT_NE_all k i i) γ₂
      have hζ₁q0 : ζ₁ (qScrNotE rE) = 0 :=
        (hEqζ₁ _ (qScrNotE_ne_bufHiE rE) fun k i e ↦ by
          rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
          · dsimp [sys234] at e; rw [appendFin_castAdd, planeOfRouter_sys] at e
            exact qScrNotE_not_portOnlyHiMod w (Or.inr (Or.inl ⟨p, k, e⟩))
          · dsimp [sys234] at e; rw [appendFin_natAdd, planeOfRouter_sys] at e
            exact qScrNotE_not_portOnlyHiMod w (Or.inr (Or.inr ⟨q, k, e⟩))).trans hγ₂q0
      have hSwEq := portSwapVecCirc_235_eq_234_of_q0 w hCtrlEBufN 24 le_rfl γ₂ hγ₂q0;
      have hCpEq :=
          specFanoutCopyVecCirc_235_eq_234_of_q0 w hCtrlEBufN 24 le_rfl ζ₁ hζ₁q0; rw [← hUHi]; dsimp
          only [uSharedHi235Inner, uSharedHiPortOnlyConj, pDecN,
          pDecE] at hSwEq hCpEq hζ₁ ⊢; simp only [← Matrix.mulVec_mulVec]; rw [fwdCirc_ket pDecN α,
          fwdCirc_ket pDecE γ₁, hSwEq, hζ₁, hCpEq]
    refine ⟨η₀, hUHi, hOut, ?_, ?_⟩
    · rw [hTogα, hXorη, hTogη]; exact hInEq
    · dsimp only [uSharedHi235Conj];
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cToggleNotRaw2_mulVec_ket, hTogα, hInEq,
          cToggleNotRaw2_mulVec_ket, hTogη, hXorη]
  · have hrN0 : α (rRawHas2 rN) = 0 :=
      (DynCircExt.bit_cases (α (rRawHas2 rN))).elim id fun ho ↦ by simp [ho, hExcl ho] at hs1
    have hrE0 : α (rRawHas2 rE) = 0 :=
      (DynCircExt.bit_cases (α (rRawHas2 rE))).elim id fun ho ↦ by simp [hrN0, ho] at hs1
    have hDec0 : ∀ {δ : BitAssignment n},
        (∀ p : Fin 47, δ (cHiN p) = 0) → (∀ q : Fin 187, δ (rCtrlLo rE q) = 0) →
        UnloadHiPred rN δ → UnloadHiPred rE δ →
        δ (rRawHas2 rN) = 0 → δ (rRawHas2 rE) = 0 →
        pDecN.fwdBits δ = δ ∧ pDecE.fwdBits δ = δ :=
      fun {δ} hcNd hcEd hPNd hPEd hrNd hrEd ↦ by
        obtain ⟨hFN, hON, _⟩ := spec_pDecHiNOn rN rE cHiN w δ hcNd hPNd
        obtain ⟨hFE, hOE, _⟩ := spec_pDecHi_sorted sorted187_hD1 sorted187_hMlo (by omega)
          (fun d hdlt ↦ sorted187_hPow d (sortedUnload_lt_of_sub hdlt)) rE δ hcEd hPEd
        refine ⟨funext fun u ↦ ?_, funext fun u ↦ ?_⟩
        · by_cases hp : ∃ p, u = cHiN p
          · obtain ⟨p, rfl⟩ :=
                hp; rw [hFN p, hcNd p]; dsimp [cOfSortedHi]; rw [hrNd]; split_ifs <;> rfl
          · exact hON u fun p e ↦ hp ⟨p, e⟩
        · by_cases hq : ∃ q, u = rCtrlLo rE q
          · obtain ⟨q, rfl⟩ :=
                hq; dsimp only [pDecE, pDecHiESorted]; rw [hFE q,
                hcEd q]; dsimp [cOfSortedHi]; rw [hrEd]; split_ifs <;> rfl
          · exact hOE u fun q e ↦ hq ⟨q, e⟩
    have hUHi0 : (uSharedHiPortOnlyConj rN rE cHiN w).mulVec (ket α) = ket α := by
      obtain ⟨hDNα, hDEα⟩ := hDec0 hcN hcE hPHiN hPHiE hrN0 hrE0
      have hc0α : ∀ i : Fin (47 + 187), α (appendFin cHiN (rCtrlLo rE) i) = 0 :=
        appendFin_cases (fun p ↦ by rw [appendFin_castAdd]; exact hcN p)
          (fun q ↦ by rw [appendFin_natAdd]; exact hcE q)
      dsimp only [uSharedHiPortOnlyConj, pDecN, pDecE] at hDNα hDEα ⊢;
      simp only [← Matrix.mulVec_mulVec];
      rw [fwdCirc_ket (pDecHiNOn rN rE cHiN w) α, hDNα, fwdCirc_ket (pDecHiESorted rE) α, hDEα,
          portSwapVecCirc_zero_ctrl (47 + 187) 24 _ _ _ _ _ _ w.hCT_NE_all α hc0α,
          specFanoutCopyVecCirc_zero_ctrl (47 + 187) 24 _ _ _ _ _ _ w.hCT_NE_all α hc0α,
          fwdCirc_inv_mulVec_ket_of_fwdBits_eq (pDecHiESorted rE) hDEα,
          fwdCirc_inv_mulVec_ket_of_fwdBits_eq (pDecHiNOn rN rE cHiN w) hDNα]
    let α_tog := toggleNotRaw2Bits (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE) α
    have hαTog_ne : ∀ {u : Wire n}, u ≠ qScrNotE rE → α_tog u = α u :=
      fun hne ↦ Function.update_of_ne hne _ _
    have hαTog_q1 : α_tog (qScrNotE rE) = 1 := by
      dsimp only [α_tog, toggleNotRaw2Bits]; rw [Function.update_self, hqScr0, zero_add, hs1]
    have hcN_t : ∀ p, α_tog (cHiN p) = 0 := fun p ↦
        (hαTog_ne (qScrNotE_ne_cHiN w p).symm).trans (hcN p)
    have hcE_t : ∀ q, α_tog (rCtrlLo rE q) = 0 := fun q ↦
        (hαTog_ne (qScrNotE_ne_ctrlE rE q).symm).trans (hcE q)
    have hrN_t : α_tog (rRawHas2 rN) = 0 := (hαTog_ne (rawN_ne_qScrNotE w)).trans hrN0;
    have hrE_t : α_tog (rRawHas2 rE) = 0 := (hαTog_ne (rawE_ne_qScrNotE rE)).trans hrE0
    have hPN_t : UnloadHiPred rN α_tog := unloadHiPred_congr
      (hαTog_ne (rawN_ne_qScrNotE w))
      (fun d ↦ hαTog_ne fun e ↦ (qScrNotE_not_portOnlyHiMod w)
        (False.elim (w.rN_disj_rE_mod ⟨2 + 6 + d.val, rw_ltIdx2 d⟩ _ ⟨⟨12, by decide⟩,
            Or.inr (Or.inr (Or.inl rfl))⟩ e)))
      hPHiN
    have hPE_t : UnloadHiPred rE α_tog := unloadHiPred_congr
      (hαTog_ne (rawE_ne_qScrNotE rE))
      (fun d ↦ hαTog_ne (rr_ne rE (by have := d.isLt; dsimp [qScrNotE]; omega)))
      hPHiE
    obtain ⟨hDNt, hDEt⟩ := hDec0 hcN_t hcE_t hPN_t hPE_t hrN_t hrE_t
    have hc0_t : ∀ i : Fin (47 + 187), α_tog (appendFin cHiN (rCtrlLo rE) i) = 0 :=
      appendFin_cases (fun p ↦ by rw [appendFin_castAdd]; exact hcN_t p)
        (fun q ↦ by rw [appendFin_natAdd]; exact hcE_t q)
    have hB0_t : ∀ k : Fin 24, α_tog (rBufHi rE k) = 0 := fun k ↦
        (hαTog_ne (qScrNotE_ne_bufHiE rE k).symm).trans (hBufE0 k)
    let rEB : QRegister 24 n := ⟨rBufHi rE, rBufHi_inj rE⟩
    let β_tog := DynCircExt.writeReg α_tog rEB (fun k ↦ α_tog (rBufLo rN k))
    have hβ_ne : ∀ {u : Wire n}, (∀ k : Fin 24, u ≠ rBufHi rE k) → β_tog u = α_tog u :=
      fun hne ↦ DynCircExt.writeReg_apply_of_not_mem α_tog rEB _ _ fun ⟨k, hk⟩ ↦ hne k hk.symm
    obtain ⟨hDNβ, hDEβ⟩ := hDec0
      (fun p ↦ (hβ_ne fun k ↦ (w.hBC_N k p).symm).trans (hcN_t p))
      (fun q ↦
          (hβ_ne fun k ↦
          rr_ne rE (by have := q.isLt; have := k.isLt; unfold basePub; dsimp; omega)).trans
          (hcE_t q))
      (unloadHiPred_congr
        (hβ_ne fun k e ↦ hHdrN_nm (Or.inr (Or.inl rfl)) (Or.inl ⟨k, e⟩))
        (fun d ↦ hβ_ne fun k e ↦ hHdrN_nm (Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))
            (Or.inl ⟨k, e⟩)) hPN_t)
      (unloadHiPred_congr
        (hβ_ne fun k e ↦ hHdrE_nm (Or.inr (Or.inl rfl)) (Or.inl ⟨k, e⟩))
        (fun d ↦ hβ_ne fun k e ↦ hHdrE_nm (Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))
            (Or.inl ⟨k, e⟩)) hPE_t)
      ((hβ_ne fun k e ↦ hHdrN_nm (Or.inr (Or.inl rfl)) (Or.inl ⟨k, e⟩)).trans hrN_t)
      ((hβ_ne fun k e ↦ hHdrE_nm (Or.inr (Or.inl rfl)) (Or.inl ⟨k, e⟩)).trans hrE_t)
    have hInTog : (uSharedHi235Inner rN rE cHiN w hCtrlEBufN).mulVec (ket α_tog) =
        ket (toggleNotRaw2Bits (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE) (xorNotRaw2Bits rN rE α))
        := by
      dsimp only [uSharedHi235Inner, pDecN, pDecE] at hDNt hDEt hDNβ hDEβ ⊢;
      simp only [← Matrix.mulVec_mulVec];
      rw [fwdCirc_ket (pDecHiNOn rN rE cHiN w) α_tog, hDNt, fwdCirc_ket (pDecHiESorted rE) α_tog,
          hDEt, portSwapAndCopy_235_of_q1 w hCtrlEBufN hc0_t hαTog_q1 hB0_t,
          fwdCirc_inv_mulVec_ket_of_fwdBits_eq (pDecHiESorted rE) hDEβ,
          fwdCirc_inv_mulVec_ket_of_fwdBits_eq (pDecHiNOn rN rE cHiN w) hDNβ]
      refine congrArg ket (funext fun u ↦ ?_)
      by_cases huQ : u = qScrNotE rE
      · subst huQ; unfold toggleNotRaw2Bits
        rw [Function.update_self, hβ_ne (qScrNotE_ne_bufHiE rE), hαTog_q1,
            (xorNotRaw2Bits_apply rN rE α).2 _ (qScrNotE_ne_bufHiE rE),
            (xorNotRaw2Bits_apply rN rE α).2 _ (fun k e ↦ hHdrN_nm (Or.inr (Or.inl rfl))
                (Or.inl ⟨k, e⟩)),
            (xorNotRaw2Bits_apply rN rE α).2 _ (fun k e ↦ hHdrE_nm (Or.inr (Or.inl rfl))
                (Or.inl ⟨k, e⟩)),
            hqScr0, zero_add, hs1]
      · unfold toggleNotRaw2Bits; rw [Function.update_of_ne huQ]
        by_cases huB : ∃ k : Fin 24, u = rBufHi rE k
        · obtain ⟨k, rfl⟩ :=
              huB; change β_tog (rEB k) =
              xorNotRaw2Bits rN rE α (rBufHi rE k); dsimp only [β_tog];
              rw [DynCircExt.writeReg_apply_reg, (xorNotRaw2Bits_apply rN rE α).1 k, hBufE0 k,
                hs1,
              zero_add, one_mul, hαTog_ne (qScrNotE_ne_bufLoN w k).symm]
        · rw [hβ_ne (fun k e ↦ huB ⟨k, e⟩), hαTog_ne huQ,
              (xorNotRaw2Bits_apply rN rE α).2 u (fun k e ↦ huB ⟨k, e⟩)]
    refine ⟨α, hUHi0, fun _ _ ↦ rfl, hInTog, ?_⟩
    dsimp only [uSharedHi235Conj]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cToggleNotRaw2_mulVec_ket, hInTog,
        ← cToggleNotRaw2_mulVec_ket _ _ _ (rawN_ne_qScrNotE w) (rawE_ne_qScrNotE rE),
        Matrix.mulVec_mulVec, cToggleNotRaw2_mul_self, Matrix.one_mulVec]
theorem subspaceStep_pUnloadSharedHiPortOnly235WState_452
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN)
    (hCtrlEBufN : ∀ (q : Fin 187) (k : Fin 24), rCtrlLo rE q ≠ rBufLo rN k)
    (s7 : Fin 7 → Wire n) (hs : Stage5PortOnlyScratch rN rE cHiN s7)
    (hs_qScr : ∀ j : Fin 7, s7 j ≠ qScrNotE rE)
    (X₁ : Operator (2 ^ n))
    (hSuppX1 : SupportedOn
      (fun α ↦ SharedHi235Pred rN rE cHiN α ∧ ∀ j : Fin 7, α (s7 j) = 0) X₁) :
    SubspaceStep (Var := Var)
      (uSharedHi235Conj rN rE cHiN w hCtrlEBufN * X₁)
      X₁
      (pUnloadSharedHiPortOnly235WState_452 v rN rE cHiN w hCtrlEBufN s7) := by
  let hdN := hs.disjHiN w
  let hdE := hs.disjHiE
  let pDecN := pDecHiNOn rN rE cHiN w
  let pDecE := pDecHiESorted rE
  let F_N := (fwdCirc pDecN).eval
  let F_E := (fwdCirc pDecE).eval
  let cTog :=
      cToggleNotRaw2 (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE) (rawN_ne_qScrNotE w)
      (rawE_ne_qScrNotE rE)
  let T_tog := cTog.eval.1
  let X₁_tog := T_tog * X₁
  let U_in := uSharedHi235Inner rN rE cHiN w hCtrlEBufN
  let U_conj := uSharedHi235Conj rN rE cHiN w hCtrlEBufN
  let C_235 :=
      (specFanoutCopyVecCirc ((47 + 187) + 1) 24 (rBufHi rE) (wC235 cHiN rE) (sysNE235 rN rE)
      (hBC_235 w) (fun k ↦ hBT_235_all w k k) (fun k i ↦ hCT_235_all w hCtrlEBufN k i i)).eval.1
  let S_235 :=
      (portSwapVecCirc ((47 + 187) + 1) 24 (rBufHi rE) (wC235 cHiN rE) (sysNE235 rN rE) (hBC_235 w)
      (fun k ↦ hBT_235_all w k k) (fun k i ↦ hCT_235_all w hCtrlEBufN k i i)).eval.1
  let Y₁ := F_N.1 * X₁_tog
  let Y₂ := F_E.1 * Y₁
  let Z_in := S_235 * Y₂
  let W_in := (F_E⁻¹).1 * (C_235 * Z_in)
  have hBC_E : ∀ (k : Fin 24) (q : Fin 187), rBufHi rE k ≠ rCtrlLo rE q :=
    fun k q ↦ rr_ne rE (by have := k.isLt; have := q.isLt; unfold basePub; dsimp; omega)
  have hs7_notMod : ∀ j : Fin 7, ¬ PortOnlyHiMod rN rE (s7 j) := by
    rintro j (⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩)
    · exact hs.s7_ne_bufHiE j b h
    · exact hs.s7_notModN j ⟨b,
          Or.inr (Or.inr (Or.inr (Or.inr ⟨p', h.trans (planeOfRouter_sys rN b p').symm⟩)))⟩
    · exact hs.s7_ne_sysE j q' b h
  have hCHiN_nm : ∀ p : Fin 47, ¬ PortOnlyHiMod rN rE (cHiN p) := by
    rintro p (⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩)
    · exact (w.hBC_N b p) h.symm
    · exact w.cHiN_notModN p ⟨b,
          Or.inr (Or.inr (Or.inr (Or.inr ⟨p', h.trans (planeOfRouter_sys rN b p').symm⟩)))⟩
    · exact w.cHiN_notModE p ⟨b,
          Or.inr (Or.inr (Or.inr (Or.inr ⟨q', h.trans (planeOfRouter_sys rE b q').symm⟩)))⟩
  have hCtrlE_nm : ∀ q : Fin 187, ¬ PortOnlyHiMod rN rE (rCtrlLo rE q) := by
    rintro q (⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩)
    · exact (hBC_E b q).symm h
    · exact w.ctrlE_ne_sysN q p' b h
    · exact rr_ne rE
          (by have := q.isLt; have := q'.isLt; have := b.isLt; unfold basePub; dsimp; omega) h
  have hHdrN_nm : ∀ {u : Wire n}, RouterCtrlSet rN u → ¬ PortOnlyHiMod rN rE u := by
    intro u hh hm; obtain ⟨i, _, rfl⟩ := routerCtrlSet_pubIdx_nuc hh
    rcases hm with ⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩
    · exact w.rN_disj_rE_mod i _ ⟨b, Or.inr (Or.inl rfl)⟩ h
    · exact rr_ne rN (by have := p'.isLt; have := b.isLt; dsimp; omega) h
    · exact w.rN_disj_rE_mod i _ ⟨b,
          Or.inr (Or.inr (Or.inr (Or.inr ⟨q', (planeOfRouter_sys rE b q').symm⟩)))⟩ h
  have hHdrE_nm : ∀ {u : Wire n}, RouterCtrlSet rE u → ¬ PortOnlyHiMod rN rE u := by
    intro u hh hm; obtain ⟨j, _, rfl⟩ := routerCtrlSet_pubIdx_elec hh
    rcases hm with ⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩
    · exact rr_ne rE (by have := b.isLt; dsimp; omega) h
    · exact (w.pubN_ne_pubE (i := ⟨110 + 24 * p'.val + b.val,
        by have := p'.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩)
        (by have := p'.isLt; have := b.isLt; dsimp; omega) (by omega)) h.symm
    · exact rr_ne rE (by have := q'.isLt; have := b.isLt; dsimp; omega) h
  have hIdx2N_ne_q : ∀ d : Fin 6, rIdx2 rN d ≠ qScrNotE rE := fun d e ↦
    w.rN_disj_rE_mod ⟨2 + 6 + d.val, rw_ltIdx2 d⟩ _ ⟨⟨12, by decide⟩,
        Or.inr (Or.inr (Or.inl rfl))⟩ e
  have hIdx2E_ne_q : ∀ d : Fin 8, rIdx2 rE d ≠ qScrNotE rE := fun d ↦
    rr_ne rE (by have := d.isLt; dsimp [qScrNotE]; omega)
  have hSuppX1_tog : SupportedOn
      (fun δ ↦ (∀ p : Fin 47, δ (cHiN p) = 0) ∧ (∀ q : Fin 187, δ (rCtrlLo rE q) = 0) ∧
        UnloadHiPred rN δ ∧ UnloadHiPred rE δ ∧
        (δ (rRawHas2 rN) = 1 → δ (rRawHas2 rE) = 0) ∧
        (∀ k : Fin 24, δ (rBufHi rE k) = 0) ∧ (∀ j : Fin 7, δ (s7 j) = 0) ∧
        δ (qScrNotE rE) = 1 + δ (rRawHas2 rN) + δ (rRawHas2 rE)) X₁_tog := fun A B hAB ↦ by
    dsimp only [X₁_tog]; rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
    refine hSuppX1 _ _ fun α ⟨⟨hcN, hcE, hPHiN, hPHiE, hExcl, hBufE0, hq0⟩, hs0⟩ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_sr_eq_xm, cToggleNotRaw2_mulVec_ket,
        ← ket_sr_eq_xm]; let δ := toggleNotRaw2Bits (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE) α
    have hne : ∀ {u : Wire n}, u ≠ qScrNotE rE → δ u = α u := fun h ↦ Function.update_of_ne h _ _
    have hrN : δ (rRawHas2 rN) = α (rRawHas2 rN) := hne (rawN_ne_qScrNotE w);
    have hrE : δ (rRawHas2 rE) = α (rRawHas2 rE) := hne (rawE_ne_qScrNotE rE)
    refine hAB δ ⟨fun p ↦ (hne (qScrNotE_ne_cHiN w p).symm).trans (hcN p),
      fun q ↦ (hne (qScrNotE_ne_ctrlE rE q).symm).trans (hcE q),
      unloadHiPred_congr hrN (fun d ↦ hne (hIdx2N_ne_q d)) hPHiN,
      unloadHiPred_congr hrE (fun d ↦ hne (hIdx2E_ne_q d)) hPHiE,
      fun h1 ↦ hrE.trans (hExcl (hrN.symm.trans h1)),
      fun k ↦ (hne (qScrNotE_ne_bufHiE rE k).symm).trans (hBufE0 k),
      fun j ↦ (hne (hs_qScr j)).trans (hs0 j),
      by rw [show δ (qScrNotE rE) = α (qScrNotE rE) + 1 + α (rRawHas2 rN) + α (rRawHas2 rE) from
               Function.update_self .., hq0, zero_add, hrN, hrE]⟩
  have hSuppInN : SupportedOn (fun δ ↦
      (∀ p : Fin 47, δ (cHiN p) = 0) ∧ (∀ j : Fin 7, δ (s7 j) = 0) ∧
      UnloadHiPred rN δ ∧ (∀ q : Fin 187, δ (rCtrlLo rE q) = 0) ∧ UnloadHiPred rE δ)
      (U_in * X₁_tog) := fun A B hAB ↦ by
    dsimp only [X₁_tog]; simp only [← Matrix.mul_assoc]
    refine hSuppX1 _ _ fun α ⟨hP, hs0⟩ ↦ ?_
    obtain ⟨η₀, _, hOut, hInTog, _⟩ :=
        uSharedHi235Conj_ket_eq_xorNotRaw2 rN rE cHiN w hCtrlEBufN hP;
        simp only [← Matrix.mulVec_mulVec]; rw [ket_sr_eq_xm, cToggleNotRaw2_mulVec_ket, hInTog,
        ← ket_sr_eq_xm]; let δ :=
                           toggleNotRaw2Bits (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE)
                           (xorNotRaw2Bits rN rE η₀)
    have hEqOut : ∀ {u : Wire n}, u ≠ qScrNotE rE → ¬ PortOnlyHiMod rN rE u → δ u = α u :=
      fun huQ huM ↦ (Function.update_of_ne huQ _ _).trans
        (((xorNotRaw2Bits_apply rN rE η₀).2 _ fun k e ↦ huM (Or.inl ⟨k, e⟩)).trans (hOut _ huM))
    exact hAB δ
      ⟨fun p ↦ (hEqOut (qScrNotE_ne_cHiN w p).symm (hCHiN_nm p)).trans (hP.1 p),
       fun j ↦ (hEqOut (hs_qScr j) (hs7_notMod j)).trans (hs0 j),
       unloadHiPred_congr (hEqOut (rawN_ne_qScrNotE w) (hHdrN_nm (Or.inr (Or.inl rfl))))
         (fun d ↦ hEqOut (hIdx2N_ne_q d) (hHdrN_nm (Or.inr (Or.inr (Or.inr ⟨d, rfl⟩))))) hP.2.2.1,
       fun q ↦ (hEqOut (qScrNotE_ne_ctrlE rE q).symm (hCtrlE_nm q)).trans (hP.2.1 q),
       unloadHiPred_congr (hEqOut (rawE_ne_qScrNotE rE) (hHdrE_nm (Or.inr (Or.inl rfl))))
         (fun d ↦ hEqOut (hIdx2E_ne_q d) (hHdrE_nm (Or.inr (Or.inr (Or.inr ⟨d, rfl⟩))))) hP.2.2.2.1⟩
  have hWInN : SupportedOn (ValidWRouterInHi47 (rRawHas2 rN) (rIdx2 rN)
      (padWires cHiN (padNOfS7 s7)) (qEncOfS7 s7)) (U_in * X₁_tog) := fun A B hAB ↦
      hSuppInN A B fun δ ⟨hc0, hs0, hPHiN, _, _⟩ ↦
      hAB δ (validWRouterInHi47_padWires hc0 (fun _ ↦ hs0 _) (hs0 _) hPHiN.1 hPHiN.2.1 hPHiN.2.2)
  have hWOutN : SupportedOn (ValidWRouterCleanHi47 (rRawHas2 rN) (rIdx2 rN)
      (padWires cHiN (padNOfS7 s7))) X₁_tog := fun A B hAB ↦
      hSuppX1_tog A B fun δ ⟨hc0, _, hPHiN, _, _, _, hs0, _⟩ ↦
      hAB δ (validWRouterCleanHi47_padWires hc0 (fun _ ↦ hs0 _) hPHiN.1 hPHiN.2.1 hPHiN.2.2)
  have hEqOutN : (uOneHotToggle (rRawHas2 rN) (rIdx2 rN)
      (padWires cHiN (padNOfS7 s7)) hdN.has_ne_out hdN.idx_ne_out).1 * X₁_tog = Y₁ :=
      uOneHotToggle_eq_fwdCirc_pDecHiN rN rE cHiN w (padNOfS7 s7)
      (qEncOfS7 s7) hdN X₁_tog (fun A B hAB ↦ hSuppX1_tog A B fun δ ⟨hc0, _, hPHiN, _, _, _, hs0,
      _⟩ ↦ hAB δ ⟨hc0, fun _ ↦ hs0 _, hPHiN⟩)
  have hFN_cancel : F_N.1 * (F_N⁻¹).1 = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
  have hFN_Win : F_N.1 * (U_in * X₁_tog) = W_in := by
    dsimp only [U_in, uSharedHi235Inner, F_N, F_E, pDecN, pDecE, C_235, S_235, W_in, Z_in, Y₂,
        Y₁] at hFN_cancel ⊢; simp only [← Matrix.mul_assoc, hFN_cancel, Matrix.one_mul]
  have hEqInN : (uOneHotToggle (rRawHas2 rN) (rIdx2 rN)
      (padWires cHiN (padNOfS7 s7)) hdN.has_ne_out hdN.idx_ne_out).1 * (U_in * X₁_tog) = W_in := by
    rw [uOneHotToggle_eq_fwdCirc_pDecHiN rN rE cHiN w (padNOfS7 s7)
        (qEncOfS7 s7) hdN (U_in * X₁_tog) (fun A B hAB ↦ hSuppInN A B fun δ ⟨hc0, hs0, hPHiN, _,
        _⟩ ↦ hAB δ ⟨hc0, fun _ ↦ hs0 _, hPHiN⟩)]
    exact hFN_Win
  have hSuppWin : SupportedOn (fun η ↦
      (∀ q : Fin 187, η (rCtrlLo rE q) = 0) ∧ (∀ j : Fin 7, η (s7 j) = 0) ∧
          UnloadHiPred rE η) W_in :=
    fun A B hAB ↦ by
      rw [← hFN_Win, ← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
      refine hSuppInN _ _ fun δ ⟨hc0, hs0, hPHiN, hcE0, hPHiE⟩ ↦ ?_
      obtain ⟨_, hOthN, _⟩ :=
          spec_pDecHiNOn rN rE cHiN w δ hc0 hPHiN; rw [← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, ket_sr_eq_xm, fwdCirc_ket pDecN δ, ← ket_sr_eq_xm]
      exact hAB _
        ⟨fun q ↦ (hOthN _ fun p ↦ (w.cHiN_ne_ctrlE p q).symm).trans (hcE0 q),
         fun j ↦ (hOthN _ (hs.s7_ne_cHiN j)).trans (hs0 j),
         unloadHiPred_congr (hOthN _ fun p e ↦ w.cHiN_notHdrE p (e ▸ Or.inr (Or.inl rfl)))
           (fun d ↦ hOthN _ fun p e ↦
               w.cHiN_notHdrE p (e ▸ Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))) hPHiE⟩
  have hDecFacts : ∀ {δ : BitAssignment n},
      (∀ p : Fin 47, δ (cHiN p) = 0) → (∀ q : Fin 187, δ (rCtrlLo rE q) = 0) →
      UnloadHiPred rN δ → UnloadHiPred rE δ →
      (δ (rRawHas2 rN) = 1 → δ (rRawHas2 rE) = 0) →
      (∀ k : Fin 24, δ (rBufHi rE k) = 0) → (∀ j : Fin 7, δ (s7 j) = 0) →
      δ (qScrNotE rE) = 1 + δ (rRawHas2 rN) + δ (rRawHas2 rE) →
      let γ₁ := pDecN.fwdBits δ
      let γ₂ := pDecE.fwdBits γ₁
      ((∀ q : Fin 187, γ₁ (rCtrlLo rE q) = 0) ∧ (∀ j : Fin 7, γ₁ (s7 j) = 0) ∧ UnloadHiPred rE γ₁) ∧
      (AtMostOneCtrl (wC235 cHiN rE) γ₂ ∧ ∀ k : Fin 24, γ₂ (rBufHi rE k) = 0) :=
    fun {δ} hcN hcE hPHiN hPHiE hExcl hBufE0 hs0 hqEq ↦ by
      obtain ⟨hγ₁N, hγ₁Oth, hAtMostN⟩ := spec_pDecHiNOn rN rE cHiN w δ hcN hPHiN;
      let γ₁ := pDecN.fwdBits δ
      have hγ₁CtrlE0 : ∀ q, γ₁ (rCtrlLo rE q) = 0 := fun q ↦
          (hγ₁Oth _ fun p ↦ (w.cHiN_ne_ctrlE p q).symm).trans (hcE q)
      have hγ₁S7 : ∀ j, γ₁ (s7 j) = 0 := fun j ↦ (hγ₁Oth _ (hs.s7_ne_cHiN j)).trans (hs0 j)
      have hγ₁BufE0 : ∀ k, γ₁ (rBufHi rE k) = 0 := fun k ↦ (hγ₁Oth _ (w.hBC_N k)).trans (hBufE0 k)
      have hγ₁RawE : γ₁ (rRawHas2 rE) = δ (rRawHas2 rE) :=
        hγ₁Oth _ fun p e ↦ w.cHiN_notHdrE p (e ▸ Or.inr (Or.inl rfl))
      have hγ₁IdxE : ∀ d, γ₁ (rIdx2 rE d) = δ (rIdx2 rE d) :=
        fun d ↦ hγ₁Oth _ fun p e ↦ w.cHiN_notHdrE p (e ▸ Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))
      have hPHiE_γ₁ : UnloadHiPred rE γ₁ := unloadHiPred_congr hγ₁RawE hγ₁IdxE hPHiE
      have hcHiEEq : cOfSortedHi rE γ₁ = cOfSortedHi rE δ := by
        funext q; dsimp [cOfSortedHi]; rw [SplitRouter47_187.idxValD_congr hγ₁IdxE, hγ₁RawE]
      obtain ⟨hγ₂E0, hγ₂Oth, hAtMostE⟩ := spec_pDecHi_sorted sorted187_hD1 sorted187_hMlo
        (by omega) (fun d hdlt ↦ sorted187_hPow d (sortedUnload_lt_of_sub hdlt))
        rE γ₁ hγ₁CtrlE0 hPHiE_γ₁
      let γ₂ := pDecE.fwdBits γ₁
      have hγ₂E : ∀ q, γ₂ (rCtrlLo rE q) = cOfSortedHi rE δ q := fun q ↦
          (hγ₂E0 q).trans (congrFun hcHiEEq q)
      have hγ₂N : ∀ p, γ₂ (cHiN p) = cOfSortedHi rN δ p := fun p ↦
          (hγ₂Oth _ (w.cHiN_ne_ctrlE p)).trans (hγ₁N p)
      have hγ₂q : γ₂ (qScrNotE rE) = 1 + δ (rRawHas2 rN) + δ (rRawHas2 rE) :=
          (hγ₂Oth _ (qScrNotE_ne_ctrlE rE)).trans ((hγ₁Oth _ (qScrNotE_ne_cHiN w)).trans hqEq)
      have hAtMostN_γ₂ : AtMostOneCtrl cHiN γ₂ := by
        rcases hAtMostN with hz | ⟨p₀, hp1, hp0⟩
        · exact Or.inl fun p ↦ (hγ₂Oth _ (w.cHiN_ne_ctrlE p)).trans (hz p)
        · exact Or.inr ⟨p₀, (hγ₂Oth _ (w.cHiN_ne_ctrlE p₀)).trans hp1,
            fun p hp ↦ (hγ₂Oth _ (w.cHiN_ne_ctrlE p)).trans (hp0 p hp)⟩
      have hRaw1 {M D : ℕ} (r : RouterReg M D n) {i : Fin M}
          (hc1 : cOfSortedHi r δ i = 1) : δ (rRawHas2 r) = 1 := by
        rcases DynCircExt.bit_cases (δ (rRawHas2 r)) with hz | ho
        · dsimp [cOfSortedHi] at hc1
          rw [hz] at hc1
          split_ifs at hc1 <;> nomatch hc1
        · exact ho
      have hAtMostNE : AtMostOneCtrl (appendFin cHiN (rCtrlLo rE)) γ₂ :=
        atMostOneCtrl_appendFin cHiN (rCtrlLo rE) γ₂ hAtMostN_γ₂ hAtMostE fun ⟨p₀, hp1⟩ q ↦ by
          rw [hγ₂E q]
          dsimp [cOfSortedHi]
          rw [hExcl (hRaw1 rN ((hγ₂N p₀).symm.trans hp1))]
          split_ifs <;> rfl
      have hAtMostQ : AtMostOneCtrl (fun _ : Fin 1 ↦ qScrNotE rE) γ₂ :=
        (DynCircExt.bit_cases (γ₂ (qScrNotE rE))).elim (fun hz ↦ Or.inl fun _ ↦ hz)
          fun ho ↦ Or.inr ⟨⟨0, by decide⟩, ho, fun i hi ↦ False.elim (hi (Subsingleton.elim _ _))⟩
      have hAtMost235 : AtMostOneCtrl (wC235 cHiN rE) γ₂ :=
        atMostOneCtrl_appendFin (appendFin cHiN (rCtrlLo rE)) (fun _ : Fin 1 ↦ qScrNotE rE) γ₂
          hAtMostNE hAtMostQ fun ⟨i₀, hi1⟩ _ ↦ by
            rw [hγ₂q]
            rcases appendFin_eq i₀ with ⟨p₀, rfl⟩ | ⟨q₀, rfl⟩
            · rw [appendFin_castAdd, hγ₂N p₀] at hi1
              rw [hRaw1 rN hi1, hExcl (hRaw1 rN hi1)]
              decide
            · rw [appendFin_natAdd, hγ₂E q₀] at hi1
              rcases DynCircExt.bit_cases (δ (rRawHas2 rN)) with hz | ho
              · rw [hz, hRaw1 rE hi1]
                decide
              · exact False.elim (zero_ne_one ((hExcl ho).symm.trans (hRaw1 rE hi1)))
      exact ⟨⟨hγ₁CtrlE0, hγ₁S7, hPHiE_γ₁⟩, hAtMost235, fun k ↦
          (hγ₂Oth _ (hBC_E k)).trans (hγ₁BufE0 k)⟩
  have hSuppY1 : SupportedOn (fun γ₁ ↦
      (∀ q : Fin 187, γ₁ (rCtrlLo rE q) = 0) ∧ (∀ j : Fin 7, γ₁ (s7 j) = 0) ∧
          UnloadHiPred rE γ₁) Y₁ :=
    fun A B hAB ↦ by
      dsimp only [Y₁]; rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
      refine hSuppX1_tog _ _ fun δ ⟨hcN, hcE, hPN, hPE, hEx, hB0, hs0, hq⟩ ↦ ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_sr_eq_xm, fwdCirc_ket pDecN δ,
          ← ket_sr_eq_xm]; exact hAB _ (hDecFacts hcN hcE hPN hPE hEx hB0 hs0 hq).1
  have hWInE : SupportedOn (ValidWRouterInHi187 (rRawHas2 rE) (rIdx2 rE) (padWires (rCtrlLo rE)
      (padEOfS7 s7)) (qEncOfS7 s7)) W_in := fun A B hAB ↦ hSuppWin A B fun η ⟨hc0, hs0, hPHE⟩ ↦
      hAB η ⟨padWires_zero_of_zero hc0 (fun _ ↦ hs0 _), hs0 _, hPHE.1, hPHE.2.1, hPHE.2.2⟩
  have hWOutE : SupportedOn (ValidWRouterCleanHi187 (rRawHas2 rE) (rIdx2 rE) (padWires (rCtrlLo rE)
      (padEOfS7 s7))) Y₁ := fun A B hAB ↦ hSuppY1 A B fun γ₁ ⟨hc0, hs0, hPHE⟩ ↦
      hAB γ₁ ⟨padWires_zero_of_zero hc0 (fun _ ↦ hs0 _), hPHE.1, hPHE.2.1, hPHE.2.2⟩
  have hEqOutE : (uOneHotToggle (rRawHas2 rE) (rIdx2 rE) (padWires (rCtrlLo rE)
      (padEOfS7 s7)) hdE.has_ne_out hdE.idx_ne_out).1 * Y₁ = Y₂ :=
      uOneHotToggle_eq_fwdCirc_pDecHiE rE (padEOfS7 s7) (qEncOfS7 s7) hdE Y₁ (fun A B hAB ↦
      hSuppY1 A B fun γ₁ ⟨hc0, hs0, hPHE⟩ ↦ hAB γ₁ ⟨hc0, fun _ ↦ hs0 _, hPHE⟩)
  have hFE_cancel : F_E.1 * (F_E⁻¹).1 = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
  have hEqInE : (uOneHotToggle (rRawHas2 rE) (rIdx2 rE) (padWires (rCtrlLo rE)
      (padEOfS7 s7)) hdE.has_ne_out hdE.idx_ne_out).1 * W_in = C_235 * Z_in := by
    rw [uOneHotToggle_eq_fwdCirc_pDecHiE rE (padEOfS7 s7) (qEncOfS7 s7) hdE W_in (fun A B hAB ↦
        hSuppWin A B fun η ⟨hc0, hs0, hPHE⟩ ↦ hAB η ⟨hc0, fun _ ↦ hs0 _, hPHE⟩)]
    dsimp only [W_in, F_E, pDecE] at hFE_cancel ⊢;
    simp only [← Matrix.mul_assoc, hFE_cancel, Matrix.one_mul]
  have hSuppY2 : SupportedOn
      (fun γ₂ ↦ AtMostOneCtrl (wC235 cHiN rE) γ₂ ∧ ∀ k : Fin 24, γ₂ (rBufHi rE k) = 0) Y₂ :=
    fun A B hAB ↦ by
      dsimp only [Y₂, Y₁];
      rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B, ← Matrix.mul_assoc (A * _),
          ← Matrix.mul_assoc (B * _)]
      refine hSuppX1_tog _ _ fun δ ⟨hcN, hcE, hPN, hPE, hEx, hB0, hs0, hq⟩ ↦ ?_
      simp only [← Matrix.mulVec_mulVec];
      rw [ket_sr_eq_xm, fwdCirc_ket pDecN δ, fwdCirc_ket pDecE, ← ket_sr_eq_xm];
      exact hAB _ (hDecFacts hcN hcE hPN hPE hEx hB0 hs0 hq).2
  have hSysNeBuf (ks : Fin 24) : ∀ kb : Fin 24, ∀ i₀ : Fin (47 + 187),
      appendFin (fun p ↦ pSys (planeOfRouter rN ks) p)
        (fun q ↦ pSys (planeOfRouter rE ks) q) i₀ ≠ rBufLo rN kb
    | ⟨kbv, hkb⟩ => appendFin_cases
        (fun p ↦ by
          rw [appendFin_castAdd, planeOfRouter_sys]
          refine rr_ne rN ?_
          change 110 + 24 * p.val + ks.val ≠ 14 + kbv
          omega)
        (fun q ↦ by
          rw [appendFin_natAdd]
          exact (w.modN_ne_modE ⟨⟨kbv, hkb⟩, Or.inl rfl⟩
            ⟨ks, Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩)))⟩).symm)
  have sX_235 := subspaceStep_bellXHalfVec_general v (rBufHi rE)
    (wC235 cHiN rE) (sysNE235 rN rE)
    (fun k ↦ appendFin_inj (sysNE_inj w k) (fun a b _ ↦ Subsingleton.elim a b)
      (fun i₀ _ ↦ hSysNeBuf k k i₀))
    (fun _ _ hne ↦ (rBufHi_inj rE).ne hne)
    (hBC_235 w) (hBT_235_all w) (hCT_235_all w hCtrlEBufN)
    (fun k₁ k₂ hne ↦ appendFin_cases
      (fun i₀ ↦ appendFin_cases
        (fun j₀ ↦ by
          simpa only [sysNE235, appendFin_castAdd] using sysNE_plane_disj w k₁ k₂ hne i₀ j₀)
        (fun _ ↦ by
          simpa only [sysNE235, appendFin_castAdd, appendFin_natAdd] using hSysNeBuf k₁ k₂ i₀))
      (fun _ ↦ appendFin_cases
        (fun j₀ ↦ by
          simpa only [sysNE235, appendFin_natAdd, appendFin_castAdd] using
            (hSysNeBuf k₂ k₁ j₀).symm)
        (fun _ ↦ by
          simpa only [sysNE235, appendFin_natAdd] using (rBufLo_inj rN).ne hne)))
    Y₂ hSuppY2
  have sInE :=
      subspaceStep_wWrapHi187_366 v _ _ _ _ hdE _ W_in Y₁ hWInE hWOutE (subspaceStep_congr_in hEqInE
      (subspaceStep_congr_out sX_235 hEqOutE.symm))
  have sInner := subspaceStep_wrapWRouterHi47 v _ _ _ _ hdN _ (U_in * X₁_tog) X₁_tog
    hWInN hWOutN (subspaceStep_congr_in hEqInN (subspaceStep_congr_out sInE hEqOutN.symm))
  have hTogSq : T_tog * T_tog = 1 :=
    cToggleNotRaw2_mul_self (rRawHas2 rN) (rRawHas2 rE) (qScrNotE rE)
      (rawN_ne_qScrNotE w) (rawE_ne_qScrNotE rE)
  exact (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) (U_conj * X₁) cTog) (by
      dsimp only [U_conj, uSharedHi235Conj, U_in, X₁_tog, T_tog, cTog] at hTogSq ⊢
      simp only [← Matrix.mul_assoc, hTogSq, Matrix.one_mul])).seq
    (sInner.seq (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) X₁_tog cTog) (by
      dsimp only [X₁_tog]
      rw [← Matrix.mul_assoc, hTogSq, Matrix.one_mul])))

end
noncomputable section
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate
  PhotochemistrySolution.KetSupport PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.ZeroNEremSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.SortedRouterSpec
  PhotochemistrySolution.PotOraclePortBStream PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.PortBDualBellUnld PhotochemistrySolution.PortBStage5Merged
  PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.WStateWalkSeam
  PhotochemistrySolution.RouterAlwaysLoW338 PhotochemistrySolution.WState25PortOpt
open PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.AlwaysLoW338At19580
  PhotochemistrySolution.AlwaysLoNuc8886W338 PhotochemistrySolution.AlwaysLoW322
  PhotochemistrySolution.ParityCheckW309 PhotochemistrySolution.PortBAncillaScrub
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.InPlacePortBOracle
    (cXorNucLoToElecHiNotScr circWires_cXorNucLoToElecHiNotScr xorNucLoToElecHiNotScrBits
    xorNucLoToElecHiNotScrBits_apply xorNucLoToElecHiNotScrOp xorNucLoToElecHiNotScrOp_mulVec_ket
    xorNucLoToElecHiNotScrOp_congr_of_pot0Eq xorNucLoToElecHiNotScrOp_comm_uBellLoELoMux_wstate)
theorem hcnotSupportedIn_toCircWires {n : ℕ} {S : Wire n → Prop} {c : Circuit n}
    (hc : HCNOTSupportedIn S c) : CircWires S c := by
  induction hc with
  | id => exact trivial
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | h hq => exact fun _ ↦ hq
  | cnot _ hc0 ht0 => intro i; fin_cases i <;> [exact hc0; exact ht0]
theorem privRank454Sub_of_6_209 {x : ℕ} (h1 : 6 ≤ x) (h2 : x < 209) : privRank454Sub x = x - 6 := by
  unfold privRank454Sub
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]

def permIdx5056Val (j : ℕ) : ℕ :=
    if 18 ≤ j ∧ j < 42 then 4811 + (j - 18) else if 4641 ≤ j ∧ j < 4665 then 18 +
    (j - 4641) else if 4811 ≤ j ∧ j < 4835 then 4641 + (j - 4811) else j
theorem permIdx5056Val_cube (j : ℕ) : permIdx5056Val (permIdx5056Val (permIdx5056Val j)) = j := by
  generalize ha : permIdx5056Val j = a
  generalize hb : permIdx5056Val a = b
  unfold permIdx5056Val at ha hb ⊢
  split_ifs at ha hb ⊢ <;> omega

theorem permIdx5056Val_lt (j : Fin (routerWidth 187 8)) : permIdx5056Val j.val <
    routerWidth 187 8 := by
  have hrw : routerWidth 187 8 = 5056 := rfl; have hj : j.val < 5056 := hrw ▸ j.isLt
  suffices permIdx5056Val j.val < 5056 by omega
  unfold permIdx5056Val; split_ifs <;> omega

def elecHi235WireFn (j : Fin (routerWidth 187 8)) : Wire dLayout :=
    elecSubWireFn ⟨permIdx5056Val j.val, permIdx5056Val_lt j⟩
theorem elecHi235WireFn_inj : Function.Injective elecHi235WireFn := fun a b h ↦ by
  have heq := congrArg Fin.val (elecSubWireFn_inj h); dsimp only at heq
  have h3 := congrArg (fun x ↦ permIdx5056Val (permIdx5056Val x)) heq
  rw [permIdx5056Val_cube, permIdx5056Val_cube] at h3; exact Fin.ext h3
def rElecHi235 : RouterReg 187 8 dLayout := ⟨⟨elecHi235WireFn, elecHi235WireFn_inj⟩⟩
theorem rElecHi235_eq_of_not_swap {j : Fin (routerWidth 187 8)}
    (h : ¬ (18 ≤ j.val ∧ j.val < 42) ∧ ¬ (4641 ≤ j.val ∧ j.val < 4665) ∧ ¬ (4811 ≤ j.val ∧ j.val <
    4835)) : rElecHi235 j = rElecSub j := by
  change elecSubWireFn ⟨permIdx5056Val j.val, _⟩ = elecSubWireFn j;
  refine congrArg elecSubWireFn (Fin.ext ?_)
  dsimp only; unfold permIdx5056Val; split_ifs <;> omega

theorem val_rBufLo_rElecHi235 (b : Fin 24) : (rBufLo rElecHi235 b).val = 6082 + b.val := by
  have hb := b.isLt
  let j : Fin (routerWidth 187 8) := ⟨18 + b.val, (Nat.add_lt_add_left hb 18).trans (by decide)⟩
  have hp : permIdx5056Val j.val = 4811 + b.val := by
    unfold permIdx5056Val
    dsimp only [j]
    split_ifs <;> omega
  let jp : Fin (routerWidth 187 8) := ⟨permIdx5056Val j.val, permIdx5056Val_lt j⟩;
  have hjp : jp.val = 4811 + b.val := hp;
  have hv : (rBufLo rElecHi235 b).val = (elecSubWireFn jp).val := rfl
  have hrk : privRank454Sub (jp.val - 4602) = 264 + b.val := by
    rw [hjp]
    unfold privRank454Sub
    split_ifs <;> omega
  rw [hv, val_elecSubWireFn, hrk]
  split_ifs <;> omega

theorem rCtrlLo_rElecHi235_eq_bufLo_of_17_41 {q : Fin 187} (h1 : 17 ≤ q.val) (h2 : q.val < 41) :
    rCtrlLo rElecHi235 q = rBufLo rElecSub ⟨q.val - 17, by omega⟩ := by
  let j : Fin (routerWidth 187 8) :=
      ⟨basePub 187 8 + 6 + 2 * 8 + q.val,
      rw_ltCtrlLo q⟩; change elecSubWireFn ⟨permIdx5056Val j.val, permIdx5056Val_lt j⟩ =
      elecSubWireFn ⟨18 + (q.val - 17), _⟩; refine congrArg elecSubWireFn (Fin.ext ?_)
  dsimp [j, basePub]; unfold permIdx5056Val
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]; omega

theorem rCtrlLo_rElecHi235_eq_of_out {q : Fin 187} (h : ¬ (17 ≤ q.val ∧ q.val < 41)) :
    rCtrlLo rElecHi235 q = rCtrlLo rElecSub q := by
  have hq := q.isLt
  exact rElecHi235_eq_of_not_swap (j := ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩)
    (by dsimp [basePub]; omega)

theorem val_rCtrlLo_rElecHi235_bounds (q : Fin 187) :
    let v := (rCtrlLo rElecHi235 q).val
    (5696 ≤ v ∧ v < 5713) ∨ (5779 ≤ v ∧ v < 5875) ∨ (5947 ≤ v ∧ v < 6021) := by
  have hq := q.isLt
  by_cases h17 : 17 ≤ q.val ∧ q.val < 41
  · dsimp only; rw [rCtrlLo_rElecHi235_eq_bufLo_of_17_41 h17.1 h17.2]
    let b : Fin 24 := ⟨q.val - 17, by omega⟩
    have hv : (rBufLo rElecSub b).val =
        (elecSubWireFn ⟨18 + b.val, by dsimp [routerWidth]; omega⟩).val := rfl
    rw [hv, val_elecSubWireFn]; dsimp [b]; split_ifs <;> omega
  · dsimp only; rw [rCtrlLo_rElecHi235_eq_of_out h17];
    let j : Fin (routerWidth 187 8) := ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩;
    have hjVal : j.val = 4624 + q.val := rfl
    have hrk : privRank454Sub (j.val - 4602) = 16 + q.val := by
      rw [hjVal, privRank454Sub_of_6_209 (by omega) (by omega)]; omega
    have hv0 : (rCtrlLo rElecSub q).val = (elecSubWireFn j).val := rfl
    rw [hv0, val_elecSubWireFn, hrk, hjVal]; split_ifs <;> omega

theorem val_rNucSub_lt_6070 (i : Fin (routerWidth 47 6)) : (rNucSub i).val < 6070 := by
  have hrw : routerWidth 47 6 = 1394 := rfl; have hi : i.val < 1394 := hrw ▸ i.isLt
  have _ : privRank156Sub (i.val - 1238) < 156 := privRank156Sub_lt (by omega)
  have hv : (rNucSub i).val = (nucSubWireFn i).val := rfl
  rw [hv, val_nucSubWireFn]; split_ifs <;> omega

theorem routerCtrlSet_hi235_iff {n : ℕ} (rBase : QRegister dLayout n)
    (u : Wire n) : RouterCtrlSet (rBase.compose rElecHi235) u ↔
    RouterCtrlSet (rBase.compose rElecSub) u := by
  have hfx {j : Fin (routerWidth 187 8)} (hj : j.val < 18) :
      (rBase.compose rElecHi235) j = (rBase.compose rElecSub) j :=
    congrArg rBase (rElecHi235_eq_of_not_swap (by omega))
  have e0 : rHas1 (rBase.compose rElecHi235) = rHas1 (rBase.compose rElecSub) := hfx (by decide)
  have e1 : rRawHas2 (rBase.compose rElecHi235) = rRawHas2 (rBase.compose rElecSub) :=
    hfx (by decide)
  have ei1 : rIdx1 (rBase.compose rElecHi235) = rIdx1 (rBase.compose rElecSub) :=
    funext fun d ↦ hfx ((Nat.add_lt_add_left d.isLt 2).trans (by decide))
  have ei2 : rIdx2 (rBase.compose rElecHi235) = rIdx2 (rBase.compose rElecSub) :=
    funext fun d ↦ hfx (Nat.add_lt_add_left d.isLt 10)
  dsimp only [RouterCtrlSet]; rw [e0, e1, ei1, ei2]
theorem portOnlyHiMod_hi235_iff {n : ℕ} (rBase : QRegister dLayout n)
    (u : Wire n) : PortOnlyHiMod (rBase.compose rNucSub) (rBase.compose rElecHi235) u ↔
    PortOnlyHiMod (rBase.compose rNucSub) (rBase.compose rElecSub) u := by
  have hPub {j : Fin (routerWidth 187 8)} (h1 : 42 ≤ j.val) (h2 : j.val < 4602) :
      (rBase.compose rElecHi235) j = (rBase.compose rElecSub) j :=
    congrArg rBase (rElecHi235_eq_of_not_swap (by omega))
  have hBH : rBufHi (rBase.compose rElecHi235) = rBufHi (rBase.compose rElecSub) :=
    funext fun b ↦ hPub (Nat.le_add_right _ _) ((Nat.add_lt_add_left b.isLt 42).trans (by decide))
  have hSys : rSys (rBase.compose rElecHi235) = rSys (rBase.compose rElecSub) :=
    funext fun ⟨qv, hq⟩ ↦ funext fun ⟨bv, hb⟩ ↦
      hPub (j := ⟨114 + 24 * qv + bv, by
        dsimp [routerWidth]
        omega⟩)
        (show 42 ≤ 114 + 24 * qv + bv by omega) (show 114 + 24 * qv + bv < 4602 by omega)
  dsimp only [PortOnlyHiMod]; rw [hBH, hSys]
theorem allPlaneMod_hi235_cases {n : ℕ} (rBase : QRegister dLayout n) {u : Wire n}
    (hm : AllPlaneMod (rBase.compose rElecHi235) u) : (∃ b : Fin 24, u =
    rBase (rBufLo rElecHi235 b)) ∨ AllPlaneMod (rBase.compose rElecSub) u := by
  let rE1 := rBase.compose rElecHi235
  let rE0 := rBase.compose rElecSub
  have hPub {j : Fin (routerWidth 187 8)} (h1 : 42 ≤ j.val) (h2 : j.val < 4602) :
      rE1 j = rE0 j := congrArg rBase (rElecHi235_eq_of_not_swap (by omega))
  rcases hm with ⟨⟨bv, hb⟩, heq | heq | heq | heq | ⟨⟨qv, hq⟩, heq⟩⟩
  · exact Or.inl ⟨⟨bv, hb⟩, heq.trans (planeOfRouter_bufLo rE1 _)⟩
  · rw [planeOfRouter_bufHi] at heq
    have eqW : rBufHi rE1 ⟨bv, hb⟩ = rBufHi rE0 ⟨bv, hb⟩ :=
      hPub (j := ⟨42 + bv, (Nat.add_lt_add_left hb 42).trans (by decide)⟩) (Nat.le_add_right _ _)
        (show 42 + bv < 4602 by omega)
    exact Or.inr ⟨⟨bv, hb⟩, Or.inr (Or.inl
      (heq.trans (eqW.trans (planeOfRouter_bufHi rE0 _).symm)))⟩
  · rw [planeOfRouter_hA] at heq
    have eqW : rHA rE1 ⟨bv, hb⟩ = rHA rE0 ⟨bv, hb⟩ :=
      hPub (j := ⟨66 + bv, rw_ltHA 187 8 ⟨bv, hb⟩⟩)
        (show 42 ≤ 66 + bv by omega) (show 66 + bv < 4602 by omega)
    exact Or.inr ⟨⟨bv, hb⟩, Or.inr (Or.inr (Or.inl
      (heq.trans (eqW.trans (planeOfRouter_hA rE0 _).symm))))⟩
  · rw [planeOfRouter_hB] at heq
    have eqW : rHB rE1 ⟨bv, hb⟩ = rHB rE0 ⟨bv, hb⟩ :=
      hPub (j := ⟨90 + bv, rw_ltHB 187 8 ⟨bv, hb⟩⟩)
        (show 42 ≤ 90 + bv by omega) (show 90 + bv < 4602 by omega)
    exact Or.inr ⟨⟨bv, hb⟩, Or.inr (Or.inr (Or.inr (Or.inl
      (heq.trans (eqW.trans (planeOfRouter_hB rE0 _).symm)))))⟩
  · rw [planeOfRouter_sys] at heq
    have eqW : rSys rE1 ⟨qv, hq⟩ ⟨bv, hb⟩ = rSys rE0 ⟨qv, hq⟩ ⟨bv, hb⟩ :=
      hPub (j := ⟨114 + 24 * qv + bv, by
        dsimp [routerWidth]
        omega⟩)
        (show 42 ≤ 114 + 24 * qv + bv by omega) (show 114 + 24 * qv + bv < 4602 by omega)
    exact Or.inr ⟨⟨bv, hb⟩, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨qv, hq⟩, heq.trans (eqW.trans (planeOfRouter_sys rE0 _ _).symm)⟩)))⟩

theorem ctrlE_ne_bufLoN_hi235 {n : ℕ} (rBase : QRegister dLayout n) (q : Fin 187)
    (k : Fin 24) : rCtrlLo (rBase.compose rElecHi235) q ≠ rBufLo (rBase.compose rNucSub) k := by
  intro e; have e' : rBase (rCtrlLo rElecHi235 q) = rBase (rBufLo rNucSub k) := e;
  have hv := congrArg Fin.val (rBase.wires.injective e');
  have hbE := val_rCtrlLo_rElecHi235_bounds q
  have hvN : (rBufLo rNucSub k).val = 5755 + k.val := by
    have hv0 : (rBufLo rNucSub k).val = (nucSubWireFn
          ⟨14 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩).val := rfl
    rw [hv0, val_nucSubWireFn]; have := k.isLt; dsimp; split_ifs <;> omega
  have := k.isLt; omega

theorem sharedPortBWiring_hi235 {n : ℕ} (rBase : QRegister dLayout n) :
    SharedPortBWiring (rBase.compose rNucSub) (rBase.compose rElecHi235)
    (fun p ↦ rBase (cHiNSub341 p)) := by
  let w0 :=
      SharedPortBWiring.ofValidMuxD1_341 validMuxD1Stage2Regs_sub cHiNSub341_ne_rCtrlLo_rNucSub
      cHiNSub341_ne_rCtrlLo_rElecSub rBase
  refine
    { cHiN_inj := w0.cHiN_inj
      rawN_ne_cHiN := w0.rawN_ne_cHiN
      idx2N_ne_cHiN := w0.idx2N_ne_cHiN
      cHiN_ne_ctrlE := fun p q e ↦ by
        have e' : rBase (cHiNSub341 p) = rBase (rCtrlLo rElecHi235 q) := e;
        have hv := congrArg Fin.val (rBase.wires.injective e');
        have hbE := val_rCtrlLo_rElecHi235_bounds q; have hp := p.isLt
        rw [val_cHiNSub341] at hv; split_ifs at hv <;> omega
      cHiN_ne_ctrlN := w0.cHiN_ne_ctrlN
      cHiN_notModN := w0.cHiN_notModN
      cHiN_notModE := fun p hm ↦ by
        rcases allPlaneMod_hi235_cases rBase hm with ⟨b, e⟩ | hm0
        · have hv := congrArg Fin.val (rBase.wires.injective e)
          have hp := p.isLt; have hb := b.isLt
          rw [val_cHiNSub341, val_rBufLo_rElecHi235] at hv; split_ifs at hv <;> omega
        · exact w0.cHiN_notModE p hm0
      cHiN_notHdrE := fun p hc ↦ w0.cHiN_notHdrE p ((routerCtrlSet_hi235_iff rBase _).mp hc)
      pubN_ne_pubE := fun {i} hi {j} hj e ↦ by
        by_cases h18 : 18 ≤ j.val ∧ j.val < 42
        · let b : Fin 24 := ⟨j.val - 18, by omega⟩
          have hjEq : j = ⟨18 + b.val, by have := b.isLt; dsimp [routerWidth]; omega⟩ :=
            Fin.ext (by dsimp [b]; omega)
          have ej : (rBase.compose rElecHi235) j = rBase (rBufLo rElecHi235 b) :=
              congrArg (fun idx ↦ rBase (rElecHi235 idx)) hjEq
          have e' : rBase (rNucSub i) = rBase (rBufLo rElecHi235 b) := e.trans ej;
          have hv := congrArg Fin.val (rBase.wires.injective e'); have hlt := val_rNucSub_lt_6070 i
          rw [val_rBufLo_rElecHi235] at hv; omega
        · have eqE : (rBase.compose rElecHi235) j = (rBase.compose rElecSub) j :=
            congrArg rBase (rElecHi235_eq_of_not_swap (by omega))
          exact w0.pubN_ne_pubE hi hj (e.trans eqE)
      rN_disj_rE_mod := fun i u hm e ↦ by
        rcases allPlaneMod_hi235_cases rBase hm with ⟨b, rfl⟩ | hm0
        · have hv := congrArg Fin.val (rBase.wires.injective e); have hlt := val_rNucSub_lt_6070 i
          rw [val_rBufLo_rElecHi235] at hv; omega
        · exact w0.rN_disj_rE_mod i u hm0 e
      ctrlN_disj_rE_hdr := fun p u hc ↦
        w0.ctrlN_disj_rE_hdr p u ((routerCtrlSet_hi235_iff rBase _).mp hc)
      ctrlE_ne_sysN := fun q p b e ↦ by
        have e' : rBase (rCtrlLo rElecHi235 q) = rBase (rSys rNucSub p b) := e;
        have hv := congrArg Fin.val (rBase.wires.injective e');
        have hbE := val_rCtrlLo_rElecHi235_bounds q
        have hvN : (rSys rNucSub p b).val = (nucSubWireFn
          ⟨110 + 24 * p.val + b.val,
            by have := p.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩).val := rfl
        rw [hvN, val_nucSubWireFn] at hv
        have := p.isLt; have := b.isLt; dsimp at hv; split_ifs at hv <;> omega
      ctrlE_disj_rN_hdr := fun q u hc e ↦ by
        have hHdrVal : ∀ {i : Fin (routerWidth 47 6)}, i.val < 14 →
            rCtrlLo (rBase.compose rElecHi235) q ≠ (rBase.compose rNucSub) i := fun {i} hi eq0 ↦ by
          have eq0' : rBase (rCtrlLo rElecHi235 q) = rBase (rNucSub i) := eq0;
          have hv := congrArg Fin.val (rBase.wires.injective eq0');
          have hbE := val_rCtrlLo_rElecHi235_bounds q;
          have hvN : (rNucSub i).val = (nucSubWireFn i).val := rfl
          rw [hvN, val_nucSubWireFn] at hv; split_ifs at hv; omega
        rcases hc with rfl | rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩
        · exact hHdrVal (i := ⟨0, rw_lt0 47 6⟩) (by dsimp; omega) e
        · exact hHdrVal (i := ⟨1, rw_lt1 47 6⟩) (by dsimp [routerWidth]; omega) e
        · exact hHdrVal (i := ⟨2 + d.val, rw_ltIdx1 d⟩) (by have := d.isLt; dsimp; omega) e
        · exact hHdrVal (i := ⟨2 + 6 + d.val, rw_ltIdx2 d⟩) (by have := d.isLt; dsimp; omega) e }

theorem s7OfHBE_hi235_eq {n : ℕ} (rBase : QRegister dLayout n) :
    s7OfHBE (rBase.compose rElecHi235) = s7OfHBE (rBase.compose rElecSub) :=
  funext fun j ↦ congrArg rBase (rElecHi235_eq_of_not_swap
    (j := ⟨90 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩)
    (by have := j.isLt; dsimp; omega))

theorem stage5PortOnlyScratch_hi235 {n : ℕ} (rBase : QRegister dLayout n) :
    WStateStage5Unload.Stage5PortOnlyScratch (rBase.compose rNucSub) (rBase.compose rElecHi235)
    (fun p ↦ rBase (cHiNSub341 p)) (s7OfHBE (rBase.compose rElecHi235)) := by
  let rE := rBase.compose rElecHi235
  let hs0 :=
      stage5PortOnlyScratch_s7OfHBE validMuxD1Stage2Regs_sub rBase;
      have hs7Eq : ∀ j : Fin 7, s7OfHBE rE j = s7OfHBE (rBase.compose rElecSub) j :=
      congrFun (s7OfHBE_hi235_eq rBase)
  refine
    { s7_inj := fun i j hne ↦ by rw [hs7Eq i, hs7Eq j]; exact hs0.s7_inj i j hne
      s7_notHdrN := fun j ↦ by rw [hs7Eq j]; exact hs0.s7_notHdrN j
      s7_notHdrE := fun j hc ↦
        hs0.s7_notHdrE j (hs7Eq j ▸ (routerCtrlSet_hi235_iff rBase _).mp hc)
      s7_ne_ctrlN := fun j p ↦ hs7Eq j ▸ hs0.s7_ne_ctrlN j p
      s7_ne_ctrlE := fun ⟨jv, hj⟩ ⟨qv, hq⟩ ↦ rr_ne rE (by
        dsimp [s7OfHBE, basePub, routerWidth]
        omega)
      s7_ne_cHiN := fun j p ↦ hs7Eq j ▸ hs0.s7_ne_cHiN j p
      s7_notModN := fun j ↦ hs7Eq j ▸ hs0.s7_notModN j
      s7_ne_bufLoE := fun ⟨jv, hj⟩ ⟨kv, hk⟩ ↦ rr_ne rE (by
        dsimp [s7OfHBE, routerWidth]
        omega)
      s7_ne_bufHiE := fun ⟨jv, hj⟩ ⟨kv, hk⟩ ↦ rr_ne rE (by
        dsimp [s7OfHBE, routerWidth]
        omega)
      s7_ne_hAE := fun ⟨jv, hj⟩ ⟨kv, hk⟩ ↦ rr_ne rE (by
        dsimp [s7OfHBE, routerWidth]
        omega)
      s7_ne_sysE := fun ⟨jv, hj⟩ ⟨qv, hq⟩ ⟨bv, hb⟩ ↦ rr_ne rE (by
        dsimp [s7OfHBE, routerWidth]
        omega) }

def pUnloadSharedHi235W338_452 {Var : Type} {n : ℕ} (v : Var) (rTot : QRegister dLayout n) :
    DynamicCircuit Var n :=
  let rTot' := rTot.compose rPermScrub338
  let w' := sharedPortBWiring_hi235 rTot'
  .seq (.circuit (cOut40Scrub3 rTot))
    (.seq (pUnloadSharedHiPortOnly235HBEWState_452 v
            (rTot'.compose rNucSub) (rTot'.compose rElecHi235)
            (fun p ↦ rTot' (cHiNSub341 p)) w' (ctrlE_ne_bufLoN_hi235 rTot'))
          (.circuit (cOut40Scrub3 rTot)))

theorem pot0_routerSub_dLayout_eqs : wPotIsScreen rPot0Layout = wOut32 ∧ rRawHas2 rNucSub = wOut1 ∧
    rRawHas2 rElecSub = wOut15 ∧ (∀ b : Fin 24, rBufLo rNucSub b = rBufLo rNucLayout b) ∧
    (∀ b : Fin 24, rBufHi rElecSub b = rBufHi rElecLayout b) := by
  refine ⟨Fin.ext (by rw [val_wPotFlags_rPot0Layout.1, val_wOut32]),
    Fin.ext (by
      change (nucSubWireFn ⟨1, rw_lt1 47 6⟩).val = wOut1.val
      rw [val_nucSubWireFn, val_wOut1]; dsimp [routerWidth]),
    Fin.ext (by
      change (elecSubWireFn ⟨1, rw_lt1 187 8⟩).val = wOut15.val
      rw [val_elecSubWireFn, val_wOut15]; dsimp [routerWidth]),
    fun b ↦ Fin.ext (by
      have := b.isLt; change (nucSubWireFn ⟨14 + b.val, _⟩).val = (rBufLo rNucLayout b).val
      rw [val_nucSubWireFn, val_rBufLo_nuc b]; dsimp; split_ifs <;> omega),
    fun b ↦ Fin.ext (by
      have := b.isLt; change (elecSubWireFn ⟨42 + b.val, _⟩).val = (rBufHi rElecLayout b).val
      rw [val_elecSubWireFn, val_bufHi_elec b]; dsimp; split_ifs <;> omega)⟩

theorem rPermScrub338_elecFoot_hi235_facts {j : Fin (routerWidth 187 8)}
    (hj : j.val < basePub 187 8 ∨ (4624 ≤ j.val ∧ j.val < 4811)) : rPermScrub338 (rElecHi235 j) =
    rElecHi235 j ∧ (rElecHi235 j).val ≠ 5747 ∧ (rElecHi235 j).val ≠ 5749 ∧ (rElecHi235 j).val ≠
    5750 := by
  have hbp : basePub 187 8 = 4602 := rfl
  by_cases h18 : 18 ≤ j.val ∧ j.val < 42
  · let b : Fin 24 := ⟨j.val - 18, by omega⟩
    have hjEq : j = ⟨18 + b.val, by have := b.isLt; dsimp [routerWidth]; omega⟩ :=
      Fin.ext (by dsimp [b]; omega)
    have hwEq : rElecHi235 j = rBufLo rElecHi235 b := congrArg rElecHi235.wires hjEq; rw [hwEq];
    have hv := val_rBufLo_rElecHi235 b; have hb := b.isLt
    exact ⟨rPermScrub338_fix (by omega), by omega, by omega, by omega⟩
  by_cases h4641 : 4641 ≤ j.val ∧ j.val < 4665
  · let q : Fin 187 := ⟨j.val - 4624, by omega⟩
    have hq : q.val = j.val - 4624 := rfl
    have hjEq : j = ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩ :=
      Fin.ext (by dsimp [basePub]; omega)
    have hwEq : rElecHi235 j = rBufLo rElecSub ⟨q.val - 17, by omega⟩ :=
      (congrArg rElecHi235.wires hjEq).trans
        (rCtrlLo_rElecHi235_eq_bufLo_of_17_41 (by omega) (by omega))
    rw [hwEq]
    set b : Fin 24 := ⟨q.val - 17, by omega⟩
    have hb := b.isLt
    have hv : (rBufLo rElecSub b).val = 5851 + b.val := by
      have hv0 : (rBufLo rElecSub b).val =
          (elecSubWireFn ⟨18 + b.val, by dsimp [routerWidth]; omega⟩).val := rfl
      rw [hv0, val_elecSubWireFn]; dsimp only; split_ifs <;> omega
    exact ⟨rPermScrub338_fix (by omega), by omega, by omega, by omega⟩
  · have hEq : rElecHi235 j = rElecSub j :=
      rElecHi235_eq_of_not_swap (by rw [hbp] at hj; omega)
    rw [hEq]; obtain ⟨f, n1, n2, n3, _⟩ := rPermScrub338_elecFoot_facts hj; exact ⟨f, n1, n2, n3⟩
attribute [local irreducible] systemQubits_frozen ancWOfScr uLoNPortOnlyAlways1Conj uLoEAlways1Conj
  uSharedHiPortOnlyConj uSharedHi235Conj uSwapHi24 uRouterSwapAlwaysLoConj
  pUnloadLoNPortOnlyAlways1WState88 pUnloadLoEAlways1WState_368 in
theorem subspaceStep_pUnloadSharedHi235W338_452
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister dLayout n) (X₁ : Operator (2 ^ n))
    (hSuppX1 : SupportedOn (fun α ↦
      SharedHi235Pred (rTot.compose rNucSub) (rTot.compose rElecHi235)
        (fun p ↦ rTot (cHiNSub341 p)) α ∧
      ∀ j : Fin 7, α (s7OfHBE (rTot.compose rElecHi235) j) = 0) X₁)
    (hRelX1 : SupportedOn (Out40Scrub3Rel rTot) X₁) :
    let rN := rTot.compose rNucSub
    let rE := rTot.compose rElecHi235
    let cHiN := fun p ↦ rTot (cHiNSub341 p)
    let w := sharedPortBWiring_hi235 rTot
    SubspaceStep (Var := Var)
      (xorNucLoToElecHiNotScrOp rTot * (uSharedHiPortOnlyConj rN rE cHiN w * X₁))
      X₁
      (pUnloadSharedHi235W338_452 v rTot) := by
  intro rN rE cHiN w; let rTot' := rTot.compose rPermScrub338; let rN' := rTot'.compose rNucSub;
  let rE' := rTot'.compose rElecHi235
  let cHiN' := fun p ↦ rTot' (cHiNSub341 p)
  let w' := sharedPortBWiring_hi235 rTot'
  let S3 := (cOut40Scrub3 rTot).eval; obtain ⟨eScr32, eRawN1, eRawE15_0, eBufLoN, eBufHiE_0⟩ :=
      pot0_routerSub_dLayout_eqs
  have eRawE15 : rRawHas2 rElecHi235 = wOut15 :=
    (rElecHi235_eq_of_not_swap (j := ⟨1, rw_lt1 187 8⟩)
        (by dsimp [routerWidth]; omega)).trans eRawE15_0
  have eBufHiE : ∀ b : Fin 24, rBufHi rElecHi235 b = rBufHi rElecLayout b := fun b ↦
    (rElecHi235_eq_of_not_swap (j := ⟨42 + b.val, by have := b.isLt; dsimp [routerWidth]; omega⟩)
      (by have := b.isLt; dsimp; omega)).trans (eBufHiE_0 b)
  have scrub3_id (u : Wire dLayout) (h32 : u.val ≠ 5747) (h34 : u.val ≠ 5749)
      (h35 : u.val ≠ 5750) (α) : scrub3XorBits rTot α (rTot u) = α (rTot u) := by
    have neW {wt : Wire dLayout} (hw : u.val ≠ wt.val) : rTot u ≠ rTot wt :=
      fun e ↦ hw (congrArg Fin.val (rTot.wires.injective e))
    unfold scrub3XorBits
    rw [ite_eq_right (neW (val_wOut32.symm ▸ h32)), ite_eq_right (neW (val_wOut34.symm ▸ h34)),
        ite_eq_right (neW (val_wOut35.symm ▸ h35))]
  have pubNEq (i : Fin (routerWidth 47 6))
      (hi : i.val < basePub 47 6 ∨ (1256 ≤ i.val ∧ i.val < 1303)) (α : BitAssignment n) :
      rN' i = rN i ∧ scrub3XorBits rTot α (rN' i) = α (rN i) :=
    let ⟨hf, n32, n34, n35, _⟩ := rPermScrub338_nucFoot_facts hi
    ⟨congrArg rTot hf,
      congrArg (scrub3XorBits rTot α ∘ rTot) hf |>.trans (scrub3_id _ n32 n34 n35 α)⟩
  have pubEEq (j : Fin (routerWidth 187 8))
      (hj : j.val < basePub 187 8 ∨ (4624 ≤ j.val ∧ j.val < 4811)) (α : BitAssignment n) :
      rE' j = rE j ∧ scrub3XorBits rTot α (rE' j) = α (rE j) :=
    let ⟨hf, n32, n34, n35⟩ := rPermScrub338_elecFoot_hi235_facts hj
    ⟨congrArg rTot hf,
      congrArg (scrub3XorBits rTot α ∘ rTot) hf |>.trans (scrub3_id _ n32 n34 n35 α)⟩
  have pubNLt (k : ℕ) (hk : k < basePub 47 6) := pubNEq ⟨k, hk.trans (by decide)⟩ (Or.inl hk)
  have pubELt (k : ℕ) (hk : k < basePub 187 8) := pubEEq ⟨k, hk.trans (by decide)⟩ (Or.inl hk)
  have bufNLt (b : Fin 24) : 14 + b.val < basePub 47 6 :=
    (Nat.add_lt_add_left b.isLt 14).trans (by decide)
  have bufELt (b : Fin 24) : 42 + b.val < basePub 187 8 :=
    (Nat.add_lt_add_left b.isLt 42).trans (by decide)
  have sysNLt : ∀ (p : Fin 47) (b : Fin 24), 110 + 24 * p.val + b.val < basePub 47 6
    | ⟨pv, hp⟩, ⟨bv, hb⟩ => by
        dsimp [basePub]
        omega
  have sysELt : ∀ (q : Fin 187) (b : Fin 24), 114 + 24 * q.val + b.val < basePub 187 8
    | ⟨qv, hq⟩, ⟨bv, hb⟩ => by
        dsimp [basePub]
        omega
  have hStepPred : ∀ {α : BitAssignment n}, SharedHi235Pred rN rE cHiN α →
      (∀ j : Fin 7, α (s7OfHBE rE j) = 0) → Out40Scrub3Rel rTot α →
      let α' := scrub3XorBits rTot α
      (SharedHi235Pred rN' rE' cHiN' α' ∧ ∀ j : Fin 7, α' (s7OfHBE rE' j) = 0) ∧
      cOfSortedHi rN' α' = cOfSortedHi rN α ∧ cOfSortedHi rE' α' = cOfSortedHi rE α := by
    intro α ⟨hcN, hcE, hPHiN, hPHiE, hExcl, hBufE0, hq0⟩ hs7 hr;
    let α' := scrub3XorBits rTot α; obtain ⟨z32, z34, z35⟩ := scrub3XorBits_zero_targets rTot hr
    have rawNEq : α' (rRawHas2 rN') = α (rRawHas2 rN) := (pubNLt 1 (by decide) α).2
    have rawEEq : α' (rRawHas2 rE') = α (rRawHas2 rE) := (pubELt 1 (by decide) α).2
    have idx2NEq : idxValD (rIdx2 rN') α' = idxValD (rIdx2 rN) α :=
      SplitRouter47_187.idxValD_congr fun d ↦
        (pubNLt (2 + 6 + d.val) ((Nat.add_lt_add_left d.isLt 8).trans (by decide)) α).2
    have idx2EEq : idxValD (rIdx2 rE') α' = idxValD (rIdx2 rE) α :=
      SplitRouter47_187.idxValD_congr fun d ↦
        (pubELt (2 + 8 + d.val) ((Nat.add_lt_add_left d.isLt 10).trans (by decide)) α).2
    have hcN' : ∀ p : Fin 47, α' (cHiN' p) = 0 := fun ⟨pv, hpLt⟩ ↦ by
      by_cases hp44 : pv < 44
      · have hVal : (cHiNSub341 ⟨pv, hpLt⟩).val ≠ 5747 ∧ (cHiNSub341 ⟨pv, hpLt⟩).val ≠ 5749 ∧
            (cHiNSub341 ⟨pv, hpLt⟩).val ≠ 5750 ∧ (cHiNSub341 ⟨pv, hpLt⟩).val ≠ 6053 ∧
            (cHiNSub341 ⟨pv, hpLt⟩).val ≠ 6054 ∧ (cHiNSub341 ⟨pv, hpLt⟩).val ≠ 6055 := by
          rw [val_cHiNSub341]
          dsimp only
          split_ifs <;> omega
        change scrub3XorBits rTot α (rTot (rPermScrub338 (cHiNSub341 ⟨pv, hpLt⟩))) = 0
        rw [rPermScrub338_fix hVal, scrub3_id _ hVal.1 hVal.2.1 hVal.2.2.1 α]
        exact hcN ⟨pv, hpLt⟩
      · have hPerm0 (wt : Wire dLayout) (hz : α' (rTot wt) = 0)
            (hwt : permScrub338Val (cHiNSub341 ⟨pv, hpLt⟩).val = wt.val) :
            α' (cHiN' ⟨pv, hpLt⟩) = 0 := by
          change α' (rTot (rPermScrub338 (cHiNSub341 ⟨pv, hpLt⟩))) = 0
          rwa [show rPermScrub338 (cHiNSub341 ⟨pv, hpLt⟩) = wt from Fin.ext hwt]
        have hVal3 : permScrub338Val (cHiNSub341 ⟨pv, hpLt⟩).val =
            if pv = 44 then 5747 else if pv = 45 then 5749 else 5750 := by
          rw [val_cHiNSub341]
          unfold permScrub338Val
          dsimp only
          split_ifs <;> omega
        rcases (by omega : pv = 44 ∨ pv = 45 ∨ pv = 46) with h4 | h5 | h6
        · exact hPerm0 wOut32 z32 (by rw [hVal3, val_wOut32, ite_eq_left h4])
        · exact hPerm0 wOut34 z34
            (by rw [hVal3, val_wOut34, ite_eq_right (by omega), ite_eq_left h5])
        · exact hPerm0 wOut35 z35
            (by rw [hVal3, val_wOut35, ite_eq_right (by omega), ite_eq_right (by omega)])
    have hcE' : ∀ q : Fin 187, α' (rCtrlLo rE' q) = 0 := fun ⟨qv, hq⟩ ↦
      (pubEEq ⟨4624 + qv, by
        dsimp [routerWidth]
        omega⟩
        (Or.inr ⟨Nat.le_add_right 4624 qv, Nat.add_lt_add_left hq 4624⟩) α).2.trans (hcE ⟨qv, hq⟩)
    have hPHiN' : UnloadHiPred rN' α' :=
        ⟨idx2NEq.trans_lt hPHiN.1, fun hz ↦ idx2NEq.trans (hPHiN.2.1 (rawNEq.symm.trans hz)),
        fun ho h0 ↦ hPHiN.2.2 (rawNEq.symm.trans ho) (idx2NEq.symm.trans h0)⟩
    have hPHiE' : UnloadHiPred rE' α' :=
        ⟨idx2EEq.trans_lt hPHiE.1, fun hz ↦ idx2EEq.trans (hPHiE.2.1 (rawEEq.symm.trans hz)),
        fun ho h0 ↦ hPHiE.2.2 (rawEEq.symm.trans ho) (idx2EEq.symm.trans h0)⟩
    have hBufE0' (k : Fin 24) : α' (rBufHi rE' k) = 0 :=
      (pubELt _ (bufELt k) α).2.trans (hBufE0 k)
    have hq0' : α' (qScrNotE rE') = 0 := (pubELt (66 + 12) (by decide) α).2.trans hq0
    have hs7' (j : Fin 7) : α' (s7OfHBE rE' j) = 0 :=
      (pubELt _ ((Nat.add_lt_add_left j.isLt 90).trans (by decide)) α).2.trans (hs7 j)
    refine ⟨⟨⟨hcN', hcE', hPHiN', hPHiE', fun h1 ↦ rawEEq.trans (hExcl (rawNEq.symm.trans h1)),
        hBufE0', hq0'⟩, hs7'⟩, ?_, ?_⟩
    · funext p; dsimp only [cOfSortedHi, α'] at idx2NEq rawNEq ⊢; rw [idx2NEq, rawNEq]
    · funext q; dsimp only [cOfSortedHi, α'] at idx2EEq rawEEq ⊢; rw [idx2EEq, rawEEq]
  have hSuppSX1 : SupportedOn (fun α' ↦
      SharedHi235Pred rN' rE' cHiN' α' ∧ ∀ j : Fin 7, α' (s7OfHBE rE' j) = 0)
      (S3.1 * X₁) := fun A B hAB ↦ by
    rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
    refine (supportedOn_and hSuppX1 hRelX1) (A * S3.1) (B * S3.1) fun α ⟨⟨hP, hs7⟩, hr⟩ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cOut40Scrub3_mulVec_ket];
    exact hAB _ (hStepPred hP hs7 hr).1
  have hStep1Eq : S3.1 * (xorNucLoToElecHiNotScrOp rTot * (uSharedHiPortOnlyConj rN rE cHiN w *
      X₁)) = uSharedHi235Conj rN' rE' cHiN' w' (ctrlE_ne_bufLoN_hi235 rTot') * (S3.1 * X₁) := by
    simp only [← Matrix.mul_assoc]
    refine (supportedOn_and hSuppX1 hRelX1) _ _ fun α ⟨⟨hP, hs7⟩, hr⟩ ↦ ?_
    obtain ⟨⟨hP', _⟩, hcS_N, hcS_E⟩ := hStepPred hP hs7 hr;
    let α' := scrub3XorBits rTot α; obtain ⟨η₀', hUHi', hOut', _, hU235'⟩ :=
        uSharedHi235Conj_ket_eq_xorNotRaw2 rN' rE' cHiN' w' (ctrlE_ne_bufLoN_hi235 rTot') hP'
    have hCommUHiKet : S3.1.mulVec ((uSharedHiPortOnlyConj rN rE cHiN w).mulVec (ket α)) =
        ket η₀' := by
      rw [← hUHi']; dsimp only [S3, α'];
      rw [uSharedHiPortOnlyConj_mulVec_ket rN' rE' cHiN' w' hP'.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1,
          uSharedHiPortOnlyConj_mulVec_ket rN rE cHiN w hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1]
      have hBufEq : rBufHi rE' = rBufHi rE := funext fun b ↦ (pubELt _ (bufELt b) α).1
      have hSysEq : (fun b : Fin 24 ↦ appendFin (fun p ↦ rSys rN' p b) (fun q ↦ rSys rE' q b)) =
          (fun b : Fin 24 ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b)) := by
        exact funext fun b ↦ funext (appendFin_cases
          (fun p ↦ by simpa only [appendFin_castAdd] using (pubNLt _ (sysNLt p b) α).1)
          (fun q ↦ by simpa only [appendFin_natAdd] using (pubELt _ (sysELt q b) α).1))
      rw [hcS_N, hcS_E, fixedSwapVecCirc_congr_w310 hBufEq _ hSysEq _ _,
          fixedFanoutVecCirc_congr_w310 _ hBufEq hSysEq _ _]
      · have hSuppSys (b : Fin 24) : ∀ (i : Fin (47 + 187)),
            appendFin (cOfSortedHi rN α) (cOfSortedHi rE α) i = 1 →
            PortOnlyHiMod rN rE
              (appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b) i) :=
          appendFin_cases
            (fun p _ ↦ by
              rw [appendFin_castAdd]
              exact Or.inr (Or.inl ⟨p, b, rfl⟩))
            (fun q _ ↦ by
              rw [appendFin_natAdd]
              exact Or.inr (Or.inr ⟨q, b, rfl⟩))
        have hcIn := HCNOTSupportedIn.seq
          (hcnotSupportedIn_fixedSwapVec _ 24 _ _ w.hBTs_NE
            (fun b ↦ Or.inl ⟨b, rfl⟩) hSuppSys)
          (hcnotSupportedIn_fixedFanoutVec 24 _ _ _ w.hBTs_NE
            (fun b ↦ Or.inl ⟨b, rfl⟩) hSuppSys)
        have hCommMat :=
          (hcnotSupportedIn_cOut40Scrub3 rTot).comm hcIn (fun _ hs hp ↦
            scrub3_disj_portOnlyHiMod rTot hs ((portOnlyHiMod_hi235_iff rTot _).mp hp))
        rw [← cOut40Scrub3_mulVec_ket rTot α]
        simpa only [← Matrix.mulVec_mulVec] using congrArg (fun M : Operator (2 ^ n) ↦
            M.mulVec (ket α)) hCommMat
    have hUHiKet : (uSharedHiPortOnlyConj rN rE cHiN w).mulVec (ket α) =
        ket (scrub3XorBits rTot η₀') := by
      have h1 :=
          congrArg S3.1.mulVec hCommUHiKet; dsimp only [S3] at h1; rwa [Matrix.mulVec_mulVec,
          cOut40Scrub3_mul_self rTot, Matrix.one_mulVec, cOut40Scrub3_mulVec_ket] at h1
    simp only [← Matrix.mulVec_mulVec]; dsimp only [S3];
    rw [hUHiKet, xorNucLoToElecHiNotScrOp_mulVec_ket, cOut40Scrub3_mulVec_ket,
        cOut40Scrub3_mulVec_ket rTot α, hU235']
    refine congrArg ket (funext fun u ↦ ?_)
    let ζ := scrub3XorBits rTot η₀'
    have hEB' (b : Fin 24) : rBufHi rE' b = rTot (rBufHi rElecLayout b) :=
      ((pubELt _ (bufELt b) α).1).trans (congrArg rTot (eBufHiE b))
    have hNL' (b : Fin 24) : rBufLo rN' b = rTot (rBufLo rNucLayout b) :=
      ((pubNLt _ (bufNLt b) α).1).trans (congrArg rTot (eBufLoN b))
    have hOut_notMod' {wt : Wire dLayout} (hge : 5715 ≤ wt.val) (hle : wt.val ≤ 5778)
        (hm : PortOnlyHiMod rN' rE' (rTot wt)) : False := by
      rcases hm with ⟨⟨bv, hb⟩, e⟩ | ⟨⟨pv, hp⟩, ⟨bv, hb⟩, e⟩ | ⟨⟨qv, hq⟩, ⟨bv, hb⟩, e⟩
      · have hv := (congrArg Fin.val (rTot.wires.injective (e.trans (hEB' ⟨bv, hb⟩)))).trans
          (val_bufHi_elec ⟨bv, hb⟩)
        omega
      · have hv := congrArg Fin.val (rTot.wires.injective
          (e.trans (pubNLt _ (sysNLt ⟨pv, hp⟩ ⟨bv, hb⟩) α).1))
        change wt.val = (nucSubWireFn ⟨110 + 24 * pv + bv, _⟩).val at hv
        rw [val_nucSubWireFn] at hv
        dsimp only at hv
        split_ifs at hv <;> omega
      · have hqw : 114 + 24 * qv + bv < routerWidth 187 8 := by
          dsimp [routerWidth]
          omega
        have e2 : rE ⟨114 + 24 * qv + bv, hqw⟩ = rTot (elecSubWireFn ⟨114 + 24 * qv + bv, hqw⟩) :=
          congrArg rTot (rElecHi235_eq_of_not_swap (by
            dsimp only
            omega))
        have hv := congrArg Fin.val (rTot.wires.injective
          (e.trans ((pubELt _ (sysELt ⟨qv, hq⟩ ⟨bv, hb⟩) α).1.trans e2)))
        rw [val_elecSubWireFn] at hv
        dsimp only at hv
        split_ifs at hv <;> omega
    have hηα {wt : Wire dLayout} {v : ℕ} (hv : wt.val = v) (h : 5715 ≤ v ∧ v ≤ 5778) :
        η₀' (rTot wt) = α' (rTot wt) := hOut' _ (hOut_notMod' (by omega) (by omega))
    have nePair {a b : Wire dLayout} (hne : a.val ≠ b.val) : rTot a ≠ rTot b :=
      fun e ↦ hne (congrArg Fin.val (rTot.wires.injective e))
    have neE {wt : Wire dLayout} (hlt : wt.val < 5875) (b : Fin 24) :
        rTot wt ≠ rTot (rBufHi rElecLayout b) := nePair (val_bufHi_elec b ▸ by omega)
    have hRawN_η : η₀' (rRawHas2 rN') = α (rTot wOut1) := by
      have e1 : rRawHas2 rN' = rTot wOut1 :=
        (pubNLt 1 (by decide) α).1.trans (congrArg rTot eRawN1)
      rw [e1, hηα val_wOut1 (by decide)]
      exact (congrArg α' e1).symm.trans
        ((pubNLt 1 (by decide) α).2.trans (congrArg (α ∘ rTot) eRawN1))
    have hRawE_η : η₀' (rRawHas2 rE') = α (rTot wOut15) := by
      have e1 : rRawHas2 rE' = rTot wOut15 :=
        (pubELt 1 (by decide) α).1.trans (congrArg rTot eRawE15)
      rw [e1, hηα val_wOut15 (by decide)]
      exact (congrArg α' e1).symm.trans
        ((pubELt 1 (by decide) α).2.trans (congrArg (α ∘ rTot) eRawE15))
    have hζScr : ζ (rTot (wPotIsScreen rPot0Layout)) = η₀' (rRawHas2 rN') + η₀' (rRawHas2 rE') := by
      rw [eScr32]
      have h1 : ζ (rTot wOut32) = scrub3XorBits rTot α' (rTot wOut32) := by
        dsimp only [ζ]
        unfold scrub3XorBits
        rw [ite_eq_left rfl, ite_eq_left rfl, hηα val_wOut32 (by decide),
          hηα val_wOut1 (by decide), hηα val_wOut15 (by decide)]
      rw [h1, congrFun (scrub3XorBits_invol rTot α) (rTot wOut32), hr.1, hRawN_η, hRawE_η]
    obtain ⟨xApp, xOth⟩ := xorNucLoToElecHiNotScrBits_apply rTot ζ
    by_cases huE : ∃ b : Fin 24, u = rTot (rBufHi rElecLayout b)
    · obtain ⟨b, rfl⟩ := huE
      have hScId (β) := scrub3_id (rBufHi rElecLayout b) (val_bufHi_elec b ▸ by omega)
        (val_bufHi_elec b ▸ by omega) (val_bufHi_elec b ▸ by omega) β
      have hζNL : ζ (rTot (rBufLo rNucLayout b)) = η₀' (rBufLo rN' b) :=
        (scrub3_id (rBufLo rNucLayout b) (val_rBufLo_nuc b ▸ by omega)
          (val_rBufLo_nuc b ▸ by omega) (val_rBufLo_nuc b ▸ by omega) _).trans
          (congrArg η₀' (hNL' b).symm)
      have hζEB : ζ (rTot (rBufHi rElecLayout b)) = η₀' (rTot (rBufHi rElecLayout b)) :=
          hScId η₀'; rw [hScId, xApp b, hζEB, ← hEB' b, hζScr, hζNL,
          (xorNotRaw2Bits_apply rN' rE' η₀').1 b, ← add_assoc]
    · have xo {wt : Wire dLayout} {v : ℕ} (hv : wt.val = v) (h : v < 5875) :=
        xOth (rTot wt) (neE (by omega))
      have hScEq :
          scrub3XorBits rTot (xorNucLoToElecHiNotScrBits rTot ζ) u = scrub3XorBits rTot ζ u := by
        unfold scrub3XorBits
        split_ifs
        · rw [xo val_wOut32 (by decide), xo val_wOut1 (by decide), xo val_wOut15 (by decide)]
        · rw [xo val_wOut34 (by decide), xo val_wOut0 (by decide), xo val_wOut14 (by decide)]
        · rw [xo val_wOut35 (by decide), xo val_wOut1 (by decide)]
        · exact xOth u fun b e ↦ huE ⟨b, e⟩
      rw [hScEq, congrFun (scrub3XorBits_invol rTot η₀') u,
          (xorNotRaw2Bits_apply rN' rE' η₀').2 u (fun b e ↦ huE ⟨b, e.trans (hEB' b)⟩)]
  exact (subspaceStep_congr_out (subspaceStep_of_circuit _ _) hStep1Eq).seq
    ((subspaceStep_pUnloadSharedHiPortOnly235WState_452 v rN' rE' cHiN' w'
      (ctrlE_ne_bufLoN_hi235 rTot') (s7OfHBE rE') (stage5PortOnlyScratch_hi235 rTot')
      (fun ⟨jv, hj⟩ ↦ rr_ne rE' (by
        dsimp [qScrNotE, s7OfHBE]
        omega))
      (S3.1 * X₁) hSuppSX1).seq (subspaceStep_congr_out
        (subspaceStep_of_circuit (Var := Var) (S3.1 * X₁) (cOut40Scrub3 rTot))
        (by rw [← Matrix.mul_assoc, cOut40Scrub3_mul_self rTot, Matrix.one_mul])))

theorem rElecSub_pub_ne_loNSub {n : ℕ} (rTot : QRegister dLayout n) {j : Fin (routerWidth 187 8)}
    (hj : j.val < 4602) {u : Wire n} (hu : (∃ b : Fin 24, u = rBufLo (rTot.compose rNucSub) b) ∨
    ∃ (p : Fin 47) (b : Fin 24), u = rSys (rTot.compose rNucSub) p b) : (rTot.compose rElecSub) j ≠
    u := by
  rcases hu with ⟨b, rfl⟩ | ⟨p, b, rfl⟩ <;> intro e
  · have e' : rTot (rElecSub j) = rTot (rBufLo rNucSub b) := e;
    have hv :=
        congrArg Fin.val (rTot.wires.injective e'); rw [pot0_routerSub_dLayout_eqs.2.2.2.1 b,
        val_rBufLo_nuc b] at hv; have hvE : (rElecSub j).val = (elecSubWireFn j).val := rfl
    rw [hvE, val_elecSubWireFn] at hv; have := b.isLt; split_ifs at hv <;> omega
  · have e' : rTot (rElecSub j) = rTot (rSys rNucSub p b) := e;
    have hv := congrArg Fin.val (rTot.wires.injective e');
    have hvE : (rElecSub j).val = (elecSubWireFn j).val := rfl
    have hvN : (rSys rNucSub p b).val = (nucSubWireFn
          ⟨110 + 24 * p.val + b.val,
      by have := p.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩).val := rfl
    rw [hvE, hvN, val_elecSubWireFn, val_nucSubWireFn] at hv
    have := p.isLt; have := b.isLt; dsimp only at hv; split_ifs at hv <;> omega

theorem rElecHi235_ne_loNSub {n : ℕ} (rTot : QRegister dLayout n) {j : Fin (routerWidth 187 8)}
    (hj : j.val < 4602 ∨ (4624 ≤ j.val ∧ j.val < 4811)) {u : Wire n}
    (hu : (∃ b : Fin 24, u = rBufLo (rTot.compose rNucSub) b) ∨ ∃ (p : Fin 47)
    (b : Fin 24), u = rSys (rTot.compose rNucSub) p b) : (rTot.compose rElecHi235) j ≠ u := by
  by_cases h18 : 18 ≤ j.val ∧ j.val < 42
  · let k : Fin 24 := ⟨j.val - 18, by omega⟩
    have hjEq : j = ⟨18 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩ :=
      Fin.ext (by dsimp [k]; omega)
    have hwEq : (rTot.compose rElecHi235) j = rTot (rBufLo rElecHi235 k) :=
        congrArg (fun idx ↦ rTot (rElecHi235 idx)) hjEq
    rw [hwEq]; have hvE := val_rBufLo_rElecHi235 k; have hk := k.isLt
    rcases hu with ⟨b, rfl⟩ | ⟨p, b, rfl⟩ <;> intro e
    · have e' : rTot (rBufLo rElecHi235 k) = rTot (rBufLo rNucSub b) := e;
      have hv :=
          congrArg Fin.val (rTot.wires.injective e'); rw [pot0_routerSub_dLayout_eqs.2.2.2.1 b,
          val_rBufLo_nuc b] at hv
      have := b.isLt; omega
    · have e' : rTot (rBufLo rElecHi235 k) = rTot (rSys rNucSub p b) := e;
      have hv := congrArg Fin.val (rTot.wires.injective e');
      have hlt := val_rNucSub_lt_6070 ⟨98 + 2 * 6 + 24 * p.val + b.val, rw_ltSys p b⟩;
      have hvN : (rSys rNucSub p b).val = (rNucSub ⟨98 + 2 * 6 + 24 * p.val + b.val,
          rw_ltSys p b⟩).val := rfl
      rw [hvN] at hv; omega
  by_cases hCtrl : 4624 ≤ j.val ∧ j.val < 4811
  · let q : Fin 187 := ⟨j.val - 4624, by omega⟩
    have hjEq : j = ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩ :=
      Fin.ext (by dsimp [q, basePub]; omega)
    have hwEq : (rTot.compose rElecHi235) j = rTot (rCtrlLo rElecHi235 q) :=
      congrArg (fun idx ↦ rTot (rElecHi235 idx)) hjEq
    rw [hwEq]
    rcases hu with ⟨b, rfl⟩ | ⟨p, b, rfl⟩
    · exact ctrlE_ne_bufLoN_hi235 rTot q b
    · exact (sharedPortBWiring_hi235 rTot).ctrlE_ne_sysN q p b
  · have hj0 : j.val < 4602 := by rcases hj with h | h <;> omega
    change rTot (rElecHi235 j) ≠ u
    rw [rElecHi235_eq_of_not_swap (by omega)]
    exact rElecSub_pub_ne_loNSub rTot hj0 hu

theorem rCtrlLo_rElecHi235_zero_of_sharedPortB341 {n : ℕ} (rTot : QRegister dLayout n)
    {β : BitAssignment n} (hβ : SharedPortBInput341 rTot (rTot.compose rNucSub)
    (rTot.compose rElecSub) β) (q : Fin 187) : β (rCtrlLo (rTot.compose rElecHi235) q) = 0 := by
  obtain ⟨hC0E, _, _, _, _⟩ := facts_of_zeroGatedSorted (by omega) (rTot.compose rElecSub) hβ.1
  by_cases h17 : 17 ≤ q.val ∧ q.val < 41
  · change β (rTot (rCtrlLo rElecHi235 q)) = 0;
    rw [rCtrlLo_rElecHi235_eq_bufLo_of_17_41 h17.1 h17.2]
    exact (hβ.1.1.2.2.2.1 ⟨q.val - 17, by omega⟩).1
  · change β (rTot (rCtrlLo rElecHi235 q)) = 0; rw [rCtrlLo_rElecHi235_eq_of_out h17]; exact hC0E q
theorem unloadHiPred_router_congr {M D n : ℕ} {r₁ r₂ : RouterReg M D n} {β : BitAssignment n}
    (hRaw : rRawHas2 r₁ = rRawHas2 r₂) (hIdx : ∀ d : Fin D, rIdx2 r₁ d = rIdx2 r₂ d)
    (h : UnloadHiPred r₂ β) : UnloadHiPred r₁ β :=
    ⟨(SplitRouter47_187.idxValD_congr fun d ↦ congrArg β (hIdx d)).trans_lt h.1, fun hz ↦
    (SplitRouter47_187.idxValD_congr fun d ↦
    congrArg β (hIdx d)).trans (h.2.1 ((congrArg β hRaw).symm.trans hz)), fun ho h0 ↦
    h.2.2 ((congrArg β hRaw).symm.trans ho)
    ((SplitRouter47_187.idxValD_congr fun d ↦ congrArg β (hIdx d)).symm.trans h0)⟩
end
end QuantumComputation.Specs.PhotochemistrySolution.SharedHi235Port
end

noncomputable section

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage25InPlace

open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate
  PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.WStateWalkSeam PhotochemistrySolution.SubCoin63Walk
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp198Opt
    (Stage4ReflCoin24PotOraclePortBInPlace)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.InPlacePortBOracle (spec41Of24_ipb)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr CleanWorkStep phaseFlipUnitary
  reflULGen bOuterZeroNErem

structure Stage25InPlaceSub63Pkg (wWork w1 kOut Wp tStage25U tStage25C tPotU tPotC : ℕ)
    (decode : Fin (2 ^ 41) → ZeroNEremSector)
    (peOut : BitAssignment kOut → PotExpectFn)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (rSub : QRegister kOut 41)
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut) where
  prog : ∀ {Var : Type} {n : ℕ}, Var → QRegister dLayout n → Bool → DynamicCircuit Var n
  counts : ∀ {Var : Type} [Finite Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool),
    (prog v rTot isCsel).count .T = (if isCsel then tStage25C else tStage25U) ∧
    (prog v rTot isCsel).count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool),
    (∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork 63 w → S (rTot w)) →
    DynWires S (prog v rTot isCsel)
  step25 : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode)
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool)
    (X₁ : Operator (2 ^ n)),
    (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁ →
    let specKOut := spec41Of24_ipb o24.sliceSpec
    let s4 := stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk0_le72_wstate rSub o1 specKOut hCoin
    let uStage4 :=
        if isCsel then uCselMuxWState hk0_le72_wstate rSub o1 s4 else uUselMuxWState hk0_le72_wstate
        rSub o1 s4
    let W₁ := rTot.embedUnitary (uStage1Clean_c70 decode)
    let Wnh_loc := wNoHad (uStage1Clean_c70 decode)
    let X₂ := (rTot.embedUnitary (Wnh_loc⁻¹ * uStage4 * Wnh_loc)).1 * X₁
    (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₂ = X₂ →
    SubspaceStep (W₁.1 * X₁) (W₁.1 * X₂) (prog v rTot isCsel)

attribute [local irreducible] sReflSliceOuterSub2m1_wstate cselReflRevSliceOuterSub2m1_98_wstate
    uselReflRevSliceOuterSub2m1_98_wstate
end QuantumComputation.Specs.PhotochemistrySolution.Stage25InPlace
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.NoEndRefl
set_option exponentiation.threshold 8192
open scoped Matrix.Norms.L2Operator
open PhotochemistrySolution.Lo5J8HalfTurnkey PhotochemistrySolution.LaplaceMgfBounds
open PhotochemistrySolution.LaplaceHalfTurnkey PhotochemistrySolution.TopHadBridge
  PhotochemistrySolution.Lo5J8CatWalk
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate Real ComplexConjugate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.GQSP
  PhotochemistrySolution.OvBidir PhotochemistrySolution.BucketRouterCircuit
open PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationTop
open PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectCompactAnc
open PhotochemistrySolution.SelectCompactRot34 PhotochemistrySolution.UnembedIdleAncillas
  PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.TopSelectBridge
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.FusedUnembedLGen
open PhotochemistrySolution.Stage5StackCore PhotochemistrySolution.SelectCsa64ThreeSpec
  PhotochemistrySolution.ProviderZeroFloor
open PhotochemistrySolution.RieszQspCovering
theorem commute_unitary_inv_left {d : ℕ} (G : Unitary d) (A : Operator d) (h : Commute G.1 A) :
    Commute (G⁻¹).1 A := by
  have h1 : (G * G⁻¹).1 = 1 := by rw [mul_inv_cancel, Submonoid.coe_one]
  have h2 : (G⁻¹ * G).1 = 1 := by rw [inv_mul_cancel, Submonoid.coe_one]
  rw [commute_iff_eq, ← Matrix.mul_one ((G⁻¹).1 * A), ← h1, Submonoid.coe_mul,
      ← Matrix.mul_assoc ((G⁻¹).1 * A), Matrix.mul_assoc (G⁻¹).1 A, ← h.eq,
      ← Matrix.mul_assoc (G⁻¹).1 G.1, ← Submonoid.coe_mul, h2, Matrix.one_mul]

theorem reflU_mul_lcuProjGen
    {Var : Type} [Fintype Var] [DecidableEq Var] {ancW n tSel : ℕ} {hAnc : 100 ≤ ancW}
    {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
    {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    D.reflU.1 * lcuProjGen D.lcuSub = lcuProjGen D.lcuSub := by
  have hidem : lcuProjGen D.lcuSub * lcuProjGen D.lcuSub = lcuProjGen D.lcuSub :=
      ((locAncGen ancW).compose D.lcuSub).basisOutcomeProjector_mul_self 0
  have hzero : (1 - lcuProjGen D.lcuSub) * lcuProjGen D.lcuSub = 0 := by
    rw [sub_mul, Matrix.one_mul, hidem, sub_self]
  rw [D.reflU_eq, sub_mul, Matrix.one_mul, smul_mul_assoc, Matrix.mul_assoc, hzero, Matrix.mul_zero,
      smul_zero, sub_zero]

def bidirBodyNoEndReflLocalUnitary
    {Var : Type} [Fintype Var] [DecidableEq Var] {ancW n d tSel : ℕ} {hAnc : 100 ≤ ancW}
    {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
    {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    (U : UselDataShared34 D)
    (rot0 rotTop : Circuit 1) (steps : Fin d → Circuit 1) :
    Unitary (2 ^ (systemQubits_frozen + ancW)) :=
  pureRotLocalUnitary hAnc rotTop *
    ((Circuit.X (locQGen hAnc)).eval * D.cselU * (Circuit.X (locQGen hAnc)).eval) *
    (foldFinUnitary (m := d) fun s ↦
      pureRotLocalUnitary hAnc (steps s) * bidirStepLocalUnitaryShared34 D U) *
    pureRotLocalUnitary hAnc rot0 *
    D.cselU *
    (Circuit.H (locQGen hAnc)).eval

def bidirCoreNoEndReflLocalUnitary_lo5j8
    {Var : Type} [Fintype Var] [DecidableEq Var] {ancW n d tSel : ℕ} {hAnc : 100 ≤ ancW}
    {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
    {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    (U : UselDataShared34 D)
    (rot0 rotTop : Circuit 1) (steps : Fin d → Circuit 1) :
    Unitary (2 ^ (systemQubits_frozen + ancW)) :=
  (unpreparePhaseGradientLo5j8 (locCat8SharedGen hAnc)).eval *
    bidirBodyNoEndReflLocalUnitary D U rot0 rotTop steps *
    (preparePhaseGradientLo5j8 (locCat8SharedGen hAnc)).eval

attribute [local irreducible] systemQubits_frozen ancWOfScr pureRotLocalUnitary in
theorem approximatesTimeEvolution_noEndRefl_of_orig
    {Var : Type} [Fintype Var] [DecidableEq Var] {ancW n d tSel : ℕ} {hAnc : 100 ≤ ancW}
    {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
    {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    (U : UselDataShared34 D)
    (rot0 rotTop : Circuit 1) (steps : Fin d → Circuit 1)
    {H_eff : Operator (2 ^ systemQubits_frozen)} {t_eff εWalk : ℝ}
    (hwalk : ApproximatesTimeEvolution (k := systemQubits_frozen) (m := ancW) H_eff t_eff εWalk 1
      (bidirCorePureTopHadLocalUnitary_lo5j8 D U rot0 rotTop steps)) :
    ApproximatesTimeEvolution (k := systemQubits_frozen) (m := ancW) H_eff t_eff εWalk 1
      (bidirCoreNoEndReflLocalUnitary_lo5j8 D U rot0 rotTop steps) := by
  have : NeZero (2 ^ (systemQubits_frozen + ancW)) := ⟨pow_ne_zero _ two_ne_zero⟩
  set P₀ := (locAncGen ancW).basisOutcomeProjector 0
  set P8 := (preparePhaseGradientLo5j8 (locCat8SharedGen hAnc)).eval
  set U8 := (unpreparePhaseGradientLo5j8 (locCat8SharedGen hAnc)).eval
  set Xq := (Circuit.X (locQGen hAnc)).eval
  set Hq := (Circuit.H (locQGen hAnc)).eval
  set Rt := pureRotLocalUnitary hAnc rotTop
  set V : Unitary (2 ^ (systemQubits_frozen + ancW)) := U8 * Rt * Xq
  set R_end : Unitary (2 ^ (systemQubits_frozen + ancW)) := V * D.reflU⁻¹ * V⁻¹
  set F := foldFinUnitary (m := d) fun s ↦
      pureRotLocalUnitary hAnc (steps s) * bidirStepLocalUnitaryShared34 D U
  set Mid : Unitary (2 ^ (systemQubits_frozen + ancW)) :=
      D.cselU * Xq * F * pureRotLocalUnitary hAnc rot0 * D.cselU
  have hDisjSysQ : (locSysGen ancW).DisjointWires (QRegister.singleton (locQGen hAnc)) :=
    QRegister.disjoint_iff.mpr fun i j h ↦ by
      fin_cases j;
      have hv :=
          congrArg Fin.val h; dsimp [locSysGen, locQGen, locAncGen, QRegister.block_apply_val] at hv
      have := i.isLt; omega
  have hDisjSysCat8 : (locSysGen ancW).DisjointWires (locCat8SharedGen hAnc) :=
    QRegister.disjoint_iff.mpr fun i _ h ↦ by
      have hv :=
          congrArg Fin.val h; dsimp [locSysGen, locCat8SharedGen, locGrad34Gen, locAncGen,
          QRegister.slice, QRegister.block_apply_val] at hv
      have := i.isLt; omega
  have hP8_emb : P8 =
      (locCat8SharedGen hAnc).embedUnitary (preparePhaseGradientLo5j8 (QRegister.whole 8)).eval
      := by
    dsimp only [P8];
    rw [preparePhaseGradientLo5j8_onRegister (locCat8SharedGen hAnc), Circuit.eval_onRegister]
  have hU8_eq : U8 = P8⁻¹ := by
    dsimp only [U8, P8]; unfold unpreparePhaseGradientLo5j8; rw [Circuit.eval_inverse]
  have hP8_lcu : Commute P8.1 (lcuProjGen D.lcuSub) := by
    rw [hP8_emb, QRegister.embedUnitary_val];
    exact (locCat8SharedGen hAnc).embedMatrix_comm_of_disjoint ((locAncGen ancW).compose D.lcuSub)
        (disj_lcu_locCat8SharedGen D).symm _ (compProj 0)
  have hU8_lcu : Commute U8.1 (lcuProjGen D.lcuSub) := by
    rw [hU8_eq]; exact commute_unitary_inv_left P8 _ hP8_lcu
  have hHq_lcu : Commute Hq.1 (lcuProjGen D.lcuSub) := by
    dsimp only [Hq]; rw [Circuit.eval_single, QRegister.embedUnitary_val];
    exact (QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint
        ((locAncGen ancW).compose D.lcuSub) (disj_locQGen_lcu D) _ (compProj 0)
  have hXq_lcu : Commute Xq.1 (lcuProjGen D.lcuSub) := by
    dsimp only [Xq]; rw [Circuit.eval_single, QRegister.embedUnitary_val];
    exact (QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint
        ((locAncGen ancW).compose D.lcuSub) (disj_locQGen_lcu D) _ (compProj 0)
  have hRt_lcu : Commute Rt.1 (lcuProjGen D.lcuSub) := by
    dsimp only [Rt]; rw [pureRotLocalUnitary_val];
    exact (QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint
        ((locAncGen ancW).compose D.lcuSub) (disj_locQGen_lcu D) rotTop.eval.1 (compProj 0)
  have hV_lcu : Commute V.1 (lcuProjGen D.lcuSub) := by
    have hv_coe : V.1 = U8.1 * Rt.1 * Xq.1 := by
      dsimp only [V]; rw [Submonoid.coe_mul, Submonoid.coe_mul]
    rw [hv_coe]; exact (hU8_lcu.mul_left hRt_lcu).mul_left hXq_lcu
  have hVinv_lcu : Commute (V⁻¹).1 (lcuProjGen D.lcuSub) := commute_unitary_inv_left V _ hV_lcu
  have hPlcu_P0 : lcuProjGen D.lcuSub * P₀ = P₀ :=
      QRegExt.basisOutcomeProjector_compose_mul_zero (locAncGen ancW) D.lcuSub
  have hRend_Plcu : R_end.1 * lcuProjGen D.lcuSub = lcuProjGen D.lcuSub := by
    have hrinv : (D.reflU⁻¹).1 * lcuProjGen D.lcuSub = lcuProjGen D.lcuSub := by
      nth_rw 1 [← reflU_mul_lcuProjGen D]
      rw [← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one,
          Matrix.one_mul]
    dsimp only [R_end]
    rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc, hVinv_lcu.eq,
        ← Matrix.mul_assoc (V.1 * (D.reflU⁻¹).1), Matrix.mul_assoc V.1, hrinv, hV_lcu.eq,
        Matrix.mul_assoc, ← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one, Matrix.mul_one]
  have hRend_P0 : R_end.1 * P₀ = P₀ := by
    nth_rw 1 [← hPlcu_P0]; rw [← Matrix.mul_assoc, hRend_Plcu, hPlcu_P0]
  have hInit_P0 : D.reflU.1 * (Hq.1 * (P8.1 * P₀)) = Hq.1 * (P8.1 * P₀) := by
    nth_rw 1 [← hPlcu_P0]
    rw [← Matrix.mul_assoc P8.1, hP8_lcu.eq, Matrix.mul_assoc (lcuProjGen D.lcuSub),
        ← Matrix.mul_assoc Hq.1, hHq_lcu.eq, Matrix.mul_assoc (lcuProjGen D.lcuSub),
        ← Matrix.mul_assoc D.reflU.1, reflU_mul_lcuProjGen D,
        ← Matrix.mul_assoc (lcuProjGen D.lcuSub), ← hHq_lcu.eq, Matrix.mul_assoc Hq.1,
        ← Matrix.mul_assoc (lcuProjGen D.lcuSub), ← hP8_lcu.eq, Matrix.mul_assoc P8.1, hPlcu_P0]
  have hOrig_split : bidirCorePureTopHadLocalUnitary_lo5j8 D U rot0 rotTop steps = V *
      (D.reflU * (Mid * (D.reflU * (Hq * P8)))) := by
    unfold bidirCorePureTopHadLocalUnitary_lo5j8 bidirBodyPureTopHadLocalUnitary;
    have hWT : walkLocalUnitaryShared34 D true = D.cselU * D.reflU := rfl;
    have hWF : walkLocalUnitaryShared34 D false = Xq * D.reflU * D.cselU * Xq :=
        rfl; rw [hWT, hWF]; dsimp only [V, Mid, F, U8, P8, Xq, Hq, Rt]; simp only [mul_assoc]
  have hNoEnd_split : bidirCoreNoEndReflLocalUnitary_lo5j8 D U rot0 rotTop steps = V *
      (Mid * (Hq * P8)) := by
    unfold bidirCoreNoEndReflLocalUnitary_lo5j8 bidirBodyNoEndReflLocalUnitary;
    dsimp only [V, Mid, F, U8, P8, Xq, Hq, Rt]; simp only [mul_assoc]
  have hRend_orig_grp : R_end * bidirCorePureTopHadLocalUnitary_lo5j8 D U rot0 rotTop steps = V *
      (Mid * (D.reflU * (Hq * P8))) := by
    rw [hOrig_split]; dsimp only [R_end]
    calc (V * D.reflU⁻¹ * V⁻¹) * (V * (D.reflU * (Mid * (D.reflU * (Hq * P8)))))
        = (V * D.reflU⁻¹) * ((V⁻¹ * V) * (D.reflU * (Mid * (D.reflU * (Hq * P8))))) := by
          simp only [mul_assoc]
      _ = V * ((D.reflU⁻¹ * D.reflU) * (Mid * (D.reflU * (Hq * P8)))) := by
        rw [inv_mul_cancel, one_mul, mul_assoc V D.reflU⁻¹, ← mul_assoc D.reflU⁻¹ D.reflU]
      _ = V * (Mid * (D.reflU * (Hq * P8))) := by rw [inv_mul_cancel, one_mul]
  have hW_P0 : (bidirCoreNoEndReflLocalUnitary_lo5j8 D U rot0 rotTop steps).1 * P₀ = R_end.1 *
      ((bidirCorePureTopHadLocalUnitary_lo5j8 D U rot0 rotTop steps).1 * P₀) := by
    rw [← Matrix.mul_assoc, ← Submonoid.coe_mul, hRend_orig_grp, hNoEnd_split];
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]; rw [hInit_P0]
  have hRend_sys (X : Operator (2 ^ systemQubits_frozen)) :
      Commute R_end.1 ((locSysGen ancW).embedMatrix X) := by
    have hP8_sys : Commute P8.1 ((locSysGen ancW).embedMatrix X) := by
      rw [hP8_emb, QRegister.embedUnitary_val];
      exact (locCat8SharedGen hAnc).embedMatrix_comm_of_disjoint (locSysGen ancW) hDisjSysCat8.symm
          _ X
    have hU8_sys : Commute U8.1 ((locSysGen ancW).embedMatrix X) := by
      rw [hU8_eq]; exact commute_unitary_inv_left P8 _ hP8_sys
    have hXq_sys : Commute Xq.1 ((locSysGen ancW).embedMatrix X) := by
      dsimp only [Xq]; rw [Circuit.eval_single, QRegister.embedUnitary_val];
      exact (QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint (locSysGen ancW)
          hDisjSysQ.symm _ X
    have hRt_sys : Commute Rt.1 ((locSysGen ancW).embedMatrix X) := by
      dsimp only [Rt]; rw [pureRotLocalUnitary_val];
      exact (QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint (locSysGen ancW)
          hDisjSysQ.symm rotTop.eval.1 X
    have hRefl_sys : Commute D.reflU.1 ((locSysGen ancW).embedMatrix X) := by
      rw [D.reflU_eq];
      have hP1 : Commute (projOneQGen hAnc) ((locSysGen ancW).embedMatrix X) :=
          (QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint (locSysGen ancW)
          hDisjSysQ.symm (compProj 1) X; have hPL : Commute (lcuProjGen D.lcuSub)
                                           ((locSysGen ancW).embedMatrix X) :=
                                           ((locAncGen ancW).compose
                                           D.lcuSub).embedMatrix_comm_of_disjoint (locSysGen ancW)
                                           (disj_locSysGen_lcu D).symm (compProj 0) X
      exact Commute.one_left _ |>.sub_left ((hP1.mul_left (Commute.one_left _ |>.sub_left
          hPL)).smul_left _)
    have hV_sys : Commute V.1 ((locSysGen ancW).embedMatrix X) :=
        (hU8_sys.mul_left hRt_sys).mul_left hXq_sys
    exact (hV_sys.mul_left (commute_unitary_inv_left D.reflU _ hRefl_sys)).mul_left
        (commute_unitary_inv_left V _ hV_sys)
  obtain ⟨θ, hθ⟩ := hwalk; refine ⟨θ, ?_⟩; rw [(locSysGen ancW).embedMatrix_one, one_mul] at hθ ⊢;
  let +nondep : NormedAlgebra ℚ (Operator (2 ^ systemQubits_frozen)) :=
      .restrictScalars ℚ ℂ (Operator (2 ^ systemQubits_frozen))
  set U_eff_op := NormedSpace.exp ((-Complex.I * (t_eff : ℂ)) • H_eff)
  have hDiff : ((bidirCoreNoEndReflLocalUnitary_lo5j8 D U rot0 rotTop steps).1 -
      Complex.exp ((θ : ℂ) * Complex.I) • (locSysGen ancW).embedMatrix U_eff_op) * P₀ = R_end.1 *
      (((bidirCorePureTopHadLocalUnitary_lo5j8 D U rot0 rotTop steps).1 - Complex.exp ((θ : ℂ) *
      Complex.I) • (locSysGen ancW).embedMatrix U_eff_op) * P₀) := by
    rw [sub_mul, smul_mul_assoc, hW_P0]; nth_rw 2 [← hRend_P0]
    rw [← Matrix.mul_assoc ((locSysGen ancW).embedMatrix U_eff_op), ← (hRend_sys U_eff_op).eq]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc]
  have hRend_norm : ‖R_end.1‖ ≤ 1 := norm_unitary_le_one R_end
  change ‖((bidirCoreNoEndReflLocalUnitary_lo5j8 D U rot0 rotTop steps).1 - Complex.exp ((θ : ℂ) *
      Complex.I) • (locSysGen ancW).embedMatrix U_eff_op) * P₀‖ ≤ εWalk
  rw [hDiff];
  exact ((norm_mul_le _ _).trans (mul_le_mul hRend_norm hθ (norm_nonneg _) zero_le_one)).trans_eq
      (one_mul _)

attribute [local reducible] totDimCompactGen in
attribute [local irreducible] systemQubits_frozen ancWOfScr pureRotLocalUnitary pureRotDyn in
def bidirBodyFusedNoEndReflLGenOff {scrW scrL m offRefl tSel d' : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (hm : offRefl + (m + 1) ≤ scrL)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister (ancWOfScr scrW) n}
    {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) (hAncCompact scrW) rSys rAnc hdisj tSel)
    (U : UselDataShared34 D) (rot0 rotTop : DynamicCircuit Var n)
    (steps : Fin (d' + 1) → Circuit 1) : DynamicCircuit Var n :=
  let hAnc := hAncCompact scrW
  let q := qspQubitGen hAnc rAnc
  let loopCore :=
    .seq D.reflCirc
      (.seq U.uselCirc
        (.seq (foldFinDyn (m := d') fun i : Fin d' ↦
                .seq (fusedReflPureRotDyn hp hm v rSys rAnc hdisj (steps i.castSucc))
                  U.uselCirc)
          (.seq (.circuit (Circuit.X q))
            (.seq D.reflCirc
              (.seq (.circuit (Circuit.X q))
                (pureRotDyn hAnc rAnc (steps (Fin.last d'))))))))
  .seq (.circuit (Circuit.H q))
    (.seq D.cselCirc
      (.seq rot0
        (.seq loopCore
          (.seq (.seq (.circuit (Circuit.X q)) (.seq D.cselCirc (.circuit (Circuit.X q))))
            rotTop))))

def bidirProgramFusedNoEndReflLo5_lo5j8 {scrW scrL m offRefl tSel d' : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (hm : offRefl + (m + 1) ≤ scrL)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister (ancWOfScr scrW) n}
    {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) (hAncCompact scrW) rSys rAnc hdisj tSel)
    (U : UselDataShared34 D) (rot0 rotTop : DynamicCircuit Var n)
    (steps : Fin (d' + 1) → Circuit 1) : DynamicCircuit Var n :=
  .seq (.circuit (preparePhaseGradientLo8_3_lo5j8 (gradReg5LoGen (hAncCompact scrW) rAnc)))
    (.seq (bidirBodyFusedNoEndReflLGenOff hp hm v D U rot0 rotTop steps)
      (.circuit (unpreparePhaseGradientLo8_3_lo5j8 (gradReg5LoGen (hAncCompact scrW) rAnc))))

attribute [local reducible] totDimCompactGen in
attribute [local irreducible] systemQubits_frozen ancWOfScr pureRotLocalUnitary pureRotDyn in
theorem realizes_bidirProgramFusedNoEndReflLo5_lo5j8 {scrW scrL m offRefl tSel d' : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (hOff65 : 65 ≤ offRefl) (hm : offRefl + (m + 1) ≤ scrL)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister (ancWOfScr scrW) n}
    {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) (hAncCompact scrW) rSys rAnc hdisj tSel)
    (U : UselDataShared34 D) (hD_scrL : D.scrL = scrL)
    (hD_scr : hD_scrL ▸ D.scrSub = scrSubLGen hp) (hD_refl : D.reflU = reflULGen hp)
    (hCommC : ∀ M : Operator (2 ^ 3), Commute D.cselU.1 ((locGrad3HiCompactGen scrW).embedMatrix M))
    (hCommU : ∀ M : Operator (2 ^ 3), Commute U.uselU.1 ((locGrad3HiCompactGen scrW).embedMatrix M))
    (rot0 rotTop : Circuit 1) (steps : Fin (d' + 1) → Circuit 1) :
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj
      (bidirCoreNoEndReflLocalUnitary_lo5j8 D U rot0 rotTop steps)
      (bidirProgramFusedNoEndReflLo5_lo5j8 hp hm v D U
        (pureRotDyn (hAncCompact scrW) rAnc rot0)
        (pureRotDyn (hAncCompact scrW) rAnc rotTop) steps).compile := by
  let hAnc := hAncCompact scrW
  let rTot := rSys.concat rAnc hdisj; have hrot (c : Circuit 1) := cleanWorkStep_pureRotDyn D c;
  have hX := cleanWorkStep_X_qspGen D; have hH := cleanWorkStep_H_qspGen D
  have hFused (c : Circuit 1) : CleanWorkStep (rAnc.compose D.scrSub)
      (rTot.embedUnitary (D.reflU * pureRotLocalUnitary hAnc c * (Circuit.X (locQGen hAnc)).eval *
      D.reflU * (Circuit.X (locQGen hAnc)).eval)) (fusedReflPureRotDyn hp hm v rSys rAnc hdisj c)
      := by
    cases hD_scrL; dsimp only at hD_scr; rw [hD_scr, hD_refl]
    exact fusedReflPureRotDyn_clean hp hOff65 hm v rSys rAnc hdisj c
  have hFoldMid : CleanWorkStep (rAnc.compose D.scrSub)
      (rTot.embedUnitary (foldFinUnitary (m := d') fun i : Fin d' ↦
        U.uselU * (D.reflU * pureRotLocalUnitary hAnc (steps i.castSucc) *
          (Circuit.X (locQGen hAnc)).eval * D.reflU * (Circuit.X (locQGen hAnc)).eval)))
      (foldFinDyn (m := d') fun i : Fin d' ↦
        .seq (fusedReflPureRotDyn hp hm v rSys rAnc hdisj (steps i.castSucc)) U.uselCirc) := by
    rw [embedUnitary_foldFinUnitary]
    refine CleanWorkStep.of_foldFinDyn _ _ _ fun i ↦ ?_
    rw [rTot.embedUnitary_mul]
    exact CleanWorkStep.seq (hFused (steps i.castSucc)) U.usel_clean
  have hLoop : CleanWorkStep (rAnc.compose D.scrSub)
      (rTot.embedUnitary (foldFinUnitary (m := d' + 1) fun s ↦
        pureRotLocalUnitary hAnc (steps s) * bidirStepLocalUnitaryShared34 D U))
      (.seq D.reflCirc (.seq U.uselCirc
        (.seq (foldFinDyn (m := d') fun i : Fin d' ↦
                .seq (fusedReflPureRotDyn hp hm v rSys rAnc hdisj (steps i.castSucc)) U.uselCirc)
          (.seq (.circuit (Circuit.X (qspQubitGen hAnc rAnc)))
            (.seq D.reflCirc (.seq (.circuit (Circuit.X (qspQubitGen hAnc rAnc)))
              (pureRotDyn hAnc rAnc (steps (Fin.last d'))))))))) := by
    have hseq :=
        CleanWorkStep.seq D.refl_clean (CleanWorkStep.seq U.usel_clean (CleanWorkStep.seq hFoldMid
        (CleanWorkStep.seq hX (CleanWorkStep.seq D.refl_clean (CleanWorkStep.seq hX
        (hrot (steps (Fin.last d')))))))); unfold bidirStepLocalUnitaryShared34
    rw [foldFinUnitary_fused_eq_gen D.reflU U.uselU (Circuit.X (locQGen hAnc)).eval (fun c ↦
        pureRotLocalUnitary hAnc c) d' steps, rTot.embedUnitary_mul, rTot.embedUnitary_mul,
        rTot.embedUnitary_mul, rTot.embedUnitary_mul, rTot.embedUnitary_mul, rTot.embedUnitary_mul]
    exact hseq
  have hWalkF_no : CleanWorkStep (rAnc.compose D.scrSub)
      (rTot.embedUnitary ((Circuit.X (locQGen hAnc)).eval * D.cselU *
      (Circuit.X (locQGen hAnc)).eval)) (.seq (.circuit (Circuit.X (qspQubitGen hAnc rAnc)))
      (.seq D.cselCirc (.circuit (Circuit.X (qspQubitGen hAnc rAnc)))))
      := by
    rw [rTot.embedUnitary_mul, rTot.embedUnitary_mul];
    exact CleanWorkStep.seq hX (CleanWorkStep.seq D.csel_clean hX)
  have hBody : CleanWorkStep (rAnc.compose D.scrSub)
      (rTot.embedUnitary (bidirBodyNoEndReflLocalUnitary D U rot0 rotTop steps))
      (bidirBodyFusedNoEndReflLGenOff hp hm v D U (pureRotDyn hAnc rAnc rot0)
      (pureRotDyn hAnc rAnc rotTop) steps)
      := by
    have h :=
        CleanWorkStep.seq hH (CleanWorkStep.seq D.csel_clean (CleanWorkStep.seq (hrot rot0)
        (CleanWorkStep.seq hLoop (CleanWorkStep.seq hWalkF_no (hrot rotTop))))); unfold
        bidirBodyNoEndReflLocalUnitary bidirBodyFusedNoEndReflLGenOff; rw [rTot.embedUnitary_mul,
        rTot.embedUnitary_mul, rTot.embedUnitary_mul, rTot.embedUnitary_mul,
        rTot.embedUnitary_mul]; exact h
  have hdisj5 : (rAnc.compose D.scrSub).DisjointWires (gradReg5LoGen hAnc rAnc) :=
    QRegister.disjoint_iff.mpr fun i ⟨jv, hj⟩ hij ↦ by
      have hv := congrArg Fin.val (rAnc.wires.injective hij)
      have _ := (D.scr_idx i).1
      simp only [QRegister.block_apply_val] at hv
      omega
  have hcomp5 : rTot.compose (locGrad5LoGen hAnc) = gradReg5LoGen hAnc rAnc :=
    QRegister.ext <| Function.Embedding.ext fun ⟨iv, hi⟩ ↦ by
      have hi26 : 26 + iv < ancWOfScr scrW := by
        have _ := hAncCompact scrW
        omega
      exact (congrArg rTot (Fin.ext rfl)).trans
        ((concat_locAncGen_apply_fs rSys rAnc hdisj ⟨26 + iv, hi26⟩).trans
          (congrArg rAnc (Fin.ext rfl)).symm)
  have hprep5_emb : rTot.embedUnitary (preparePhaseGradientLo8_3_lo5j8 (locGrad5LoGen hAnc)).eval =
      (preparePhaseGradientLo8_3_lo5j8 (gradReg5LoGen hAnc rAnc)).eval := by
    rw [preparePhaseGradientLo8_3_lo5j8_onRegister (locGrad5LoGen hAnc), Circuit.eval_onRegister,
        ← QRegister.embedUnitary_compose, hcomp5, ← Circuit.eval_onRegister,
        ← preparePhaseGradientLo8_3_lo5j8_onRegister]
  have hP5 : CleanWorkStep (Var := Var) (rAnc.compose D.scrSub)
      (rTot.embedUnitary (preparePhaseGradientLo8_3_lo5j8 (locGrad5LoGen hAnc)).eval)
      (.circuit (preparePhaseGradientLo8_3_lo5j8 (gradReg5LoGen hAnc rAnc))) := by
    rw [hprep5_emb]; apply CleanWorkStep.of_pureCircuit_comm
    rw [preparePhaseGradientLo8_3_lo5j8_onRegister (gradReg5LoGen hAnc rAnc),
        Circuit.eval_onRegister,
        QRegister.embedUnitary_val]; exact (gradReg5LoGen hAnc rAnc).embedMatrix_comm_of_disjoint _
        hdisj5.symm _ _
  have hU5 : CleanWorkStep (Var := Var) (rAnc.compose D.scrSub)
      (rTot.embedUnitary (unpreparePhaseGradientLo8_3_lo5j8 (locGrad5LoGen hAnc)).eval)
      (.circuit (unpreparePhaseGradientLo8_3_lo5j8 (gradReg5LoGen hAnc rAnc))) := by
    have hemb : rTot.embedUnitary (unpreparePhaseGradientLo8_3_lo5j8 (locGrad5LoGen hAnc)).eval =
        (unpreparePhaseGradientLo8_3_lo5j8 (gradReg5LoGen hAnc rAnc)).eval := by
      unfold unpreparePhaseGradientLo8_3_lo5j8;
      rw [Circuit.eval_inverse, Circuit.eval_inverse, rTot.embedUnitary_inv, hprep5_emb]
    rw [hemb]; apply CleanWorkStep.of_pureCircuit_comm
    unfold unpreparePhaseGradientLo8_3_lo5j8;
    rw [Circuit.eval_inverse, preparePhaseGradientLo8_3_lo5j8_onRegister (gradReg5LoGen hAnc rAnc),
        Circuit.eval_onRegister, ← (gradReg5LoGen hAnc rAnc).embedUnitary_inv,
        QRegister.embedUnitary_val]; exact (gradReg5LoGen hAnc rAnc).embedMatrix_comm_of_disjoint _
        hdisj5.symm _ _
  set U_lo := (unpreparePhaseGradientLo8_3_lo5j8 (locGrad5LoGen hAnc)).eval
  set P_lo := (preparePhaseGradientLo8_3_lo5j8 (locGrad5LoGen hAnc)).eval
  set P_hi := (preparePhaseGradient (locGrad3HiCompactGen scrW)).eval
  set B := bidirBodyNoEndReflLocalUnitary D U rot0 rotTop steps
  have hP8 : (preparePhaseGradientLo5j8 (locCat8SharedGen hAnc)).eval = P_hi * P_lo := by
    rw [preparePhaseGradientLo5j8_8_eval_split (locCat8SharedGen hAnc),
        locCat8SharedGen_slice_0_5 hAnc, locCat8SharedGen_slice_5_3 hAnc]; rfl
  have hU8 : (unpreparePhaseGradientLo5j8 (locCat8SharedGen hAnc)).eval = U_lo * P_hi⁻¹ := by
    unfold unpreparePhaseGradientLo5j8; rw [Circuit.eval_inverse, hP8, _root_.mul_inv_rev];
    dsimp only [U_lo]; unfold unpreparePhaseGradientLo8_3_lo5j8; rw [Circuit.eval_inverse]
  have hPhi_comm : Commute B.1 P_hi.1 := by
    set M := (preparePhaseGradient (QRegister.whole 3)).eval.1
    set E3 := (locGrad3HiCompactGen scrW).embedMatrix M
    have hOn : P_hi.1 = E3 := by
      dsimp only [P_hi, E3, M]
      rw [preparePhaseGradient_onRegister (locGrad3HiCompactGen scrW),
        Circuit.eval_onRegister, QRegister.embedUnitary_val]
    rw [hOn]
    have hDisjQ : (QRegister.singleton (locQGen hAnc)).DisjointWires
        (locGrad3HiCompactGen scrW) :=
      QRegister.disjoint_iff.mpr fun i _ h ↦ by
        fin_cases i
        have hv := congrArg Fin.val h
        have _ := hAncCompact scrW
        dsimp [locQGen, locGrad3HiCompactGen, locGrad3HiGen, locAncGen, QRegister.slice] at hv
        omega
    have hDisjQComp : (QRegister.singleton (locQCompactGen scrW)).DisjointWires
        (locGrad3HiCompactGen scrW) :=
      QRegister.disjoint_iff.mpr fun i _ h ↦ by
        fin_cases i
        have hv := congrArg Fin.val h
        dsimp [locQCompactGen, locAncCompactGen, locGrad3HiCompactGen, locGrad3HiGen,
          locAncGen, QRegister.slice, QRegister.block_apply_val] at hv
        omega
    have hDisjLcu : (rLcuLGen hp).DisjointWires (locGrad3HiCompactGen scrW) :=
      QRegister.disjoint_iff.mpr fun _ ⟨jv, hj⟩ h ↦ by
        have hv := congrArg Fin.val h
        dsimp [rLcuLGen, lcuSubLGen, locAncCompactGen, locGrad3HiCompactGen, locGrad3HiGen,
          locAncGen, QRegister.slice, QRegister.compose_apply, QRegister.block_apply_val] at hv
        omega
    have hQ (W : Operator (2 ^ 1)) :
        Commute ((QRegister.singleton (locQGen hAnc)).embedMatrix W) E3 :=
      (QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint _ hDisjQ W M
    have hH : Commute (Circuit.H (locQGen hAnc)).eval.1 E3 := by
      rw [Circuit.eval_single, QRegister.embedUnitary_val]
      exact hQ _
    have hX : Commute (Circuit.X (locQGen hAnc)).eval.1 E3 := by
      rw [Circuit.eval_single, QRegister.embedUnitary_val]
      exact hQ _
    have hRefl : Commute D.reflU.1 E3 := by
      rw [hD_refl, reflULGen_eq]
      have hP1 : Commute (projOneQCompactGen scrW) E3 :=
        (QRegister.singleton (locQCompactGen scrW)).embedMatrix_comm_of_disjoint _ hDisjQComp _ _
      have hPL : Commute (lcuProjCompactGen scrW (lcuSubLGen hp)) E3 :=
        (rLcuLGen hp).embedMatrix_comm_of_disjoint _ hDisjLcu _ _
      exact Commute.one_left E3 |>.sub_left
        ((hP1.mul_left (Commute.one_left E3 |>.sub_left hPL)).smul_left _)
    have hRot (c : Circuit 1) : Commute (pureRotLocalUnitary hAnc c).1 E3 :=
      pureRotLocalUnitary_val hAnc c ▸ hQ c.eval.1
    have hWalkF_no : Commute
        ((Circuit.X (locQGen hAnc)).eval * D.cselU * (Circuit.X (locQGen hAnc)).eval).1 E3 :=
      (hX.mul_left (hCommC M)).mul_left hX
    have hStep : Commute (bidirStepLocalUnitaryShared34 D U).1 E3 :=
      (((hX.mul_left hRefl).mul_left hX).mul_left (hCommU M)).mul_left hRefl
    have hFold : ∀ (k : ℕ) (cs : Fin k → Circuit 1), Commute
        (foldFinUnitary (m := k) fun s ↦
          pureRotLocalUnitary hAnc (cs s) * bidirStepLocalUnitaryShared34 D U).1 E3 := by
      intro k
      induction k with
      | zero => exact fun _ ↦ Commute.one_left E3
      | succ k ih =>
        exact fun cs ↦ ((hRot (cs (Fin.last k))).mul_left hStep).mul_left
          (ih fun i ↦ cs i.castSucc)
    dsimp only [B]
    unfold bidirBodyNoEndReflLocalUnitary
    exact (((((hRot rotTop).mul_left hWalkF_no).mul_left (hFold _ steps)).mul_left
      (hRot rot0)).mul_left (hCommC M)).mul_left hH
  have hCoreEq :
      U_lo * B * P_lo = bidirCoreNoEndReflLocalUnitary_lo5j8 D U rot0 rotTop steps := by
    unfold bidirCoreNoEndReflLocalUnitary_lo5j8
    rw [hP8, hU8]
    apply Subtype.ext
    change U_lo.1 * B.1 * P_lo.1 = U_lo.1 * P_hi⁻¹.1 * B.1 * (P_hi.1 * P_lo.1)
    have hInv : P_hi⁻¹.1 * P_hi.1 = 1 := congrArg Subtype.val (inv_mul_cancel P_hi)
    conv_lhs =>
      rw [← Matrix.one_mul B.1, ← hInv, Matrix.mul_assoc P_hi⁻¹.1 P_hi.1 B.1,
        hPhi_comm.symm.eq]
    simp only [Matrix.mul_assoc]
  have hCore : CleanWorkStep (rAnc.compose D.scrSub)
      (rTot.embedUnitary (bidirCoreNoEndReflLocalUnitary_lo5j8 D U rot0 rotTop steps))
      (bidirProgramFusedNoEndReflLo5_lo5j8 hp hm v D U
        (pureRotDyn hAnc rAnc rot0) (pureRotDyn hAnc rAnc rotTop) steps) := by
    unfold bidirProgramFusedNoEndReflLo5_lo5j8
    rw [← hCoreEq, rTot.embedUnitary_mul, rTot.embedUnitary_mul]
    exact CleanWorkStep.seq hP5 (CleanWorkStep.seq hBody hU5)
  exact realizes_from_cleanWorkStep v rSys rAnc hdisj D.scrSub _ _ hCore

section AmbientOuter
attribute [local irreducible] systemQubits_frozen hamiltonian_frozen
  pureRotLocalUnitary pureRotDyn jung87TopHadWordsPackHalf_walkCert
  bidirCorePureTopHadLocalUnitary_lo5j8 bidirCoreNoEndReflLocalUnitary_lo5j8
structure WalkWordsCertPack (scrW d' tCsel tStep tRot0 tTop : ℕ) (α εWalk0 : ℝ) : Type 1 where
  pkOf : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {rS : QRegister systemQubits_frozen n} {rA : QRegister (ancWOfScr scrW) n}
    {hd : rS.DisjointWires rA}
    (D : SelectConjugationDataShared34 (Var := Var) (hAncCompact scrW) rS rA hd tCsel),
    UselDataShared34 D → scaleTimeShared D = α * evolutionTime_frozen →
    Circuit 1 × Circuit 1 × (Fin (d' + 1) → Circuit 1)
  counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {rS : QRegister systemQubits_frozen n} {rA : QRegister (ancWOfScr scrW) n}
    {hd : rS.DisjointWires rA}
    (D : SelectConjugationDataShared34 (Var := Var) (hAncCompact scrW) rS rA hd tCsel)
    (U : UselDataShared34 D) (hs_eq : scaleTimeShared D = α * evolutionTime_frozen),
    let pk := pkOf D U hs_eq
    pk.1.count .TOFF = 0 ∧ pk.1.count .T ≤ tRot0 ∧
    pk.2.1.count .TOFF = 0 ∧ pk.2.1.count .T ≤ tTop ∧
    ∀ s : Fin (d' + 1), (pk.2.2 s).count .TOFF = 0 ∧ (pk.2.2 s).count .T ≤ tStep
  hwalk : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {rS : QRegister systemQubits_frozen n} {rA : QRegister (ancWOfScr scrW) n}
    {hd : rS.DisjointWires rA}
    (D : SelectConjugationDataShared34 (Var := Var) (hAncCompact scrW) rS rA hd tCsel)
    (U : UselDataShared34 D) (hs_eq : scaleTimeShared D = α * evolutionTime_frozen),
    let pk := pkOf D U hs_eq
    ApproximatesTimeEvolution (k := systemQubits_frozen) (m := ancWOfScr scrW)
      D.aImpl (D.α * evolutionTime_frozen) εWalk0 1
      (bidirCorePureTopHadLocalUnitary_lo5j8 D U pk.1 pk.2.1 pk.2.2)

def walkWordsCertPack_jung87Half {capStep capTop : ℕ}
    (hStep : ∀ U ∈ unitaryGroup (Fin 2) ℂ, Nonempty (SimpStepSpecCapEp capStep 460 35304 U))
    (hTop : ∀ g_final : ℝ, Nonempty (SimpStepSpecCapEp capTop 460 35304 (hadamard2 *
        phaseTurn g_final)))
    {scrW d' tCsel : ℕ} (hd_hi : d' + 1 ≤ 3326913) {sMax δ ε_clean α : ℝ}
    (cw : PhotochemistrySolution.HalfWalk.CleanWalkCertHalf (d' + 1) sMax δ ε_clean)
    (hs_le : α * evolutionTime_frozen ≤ sMax) :
    WalkWordsCertPack scrW d' tCsel capStep capStep capTop α
      (2 * (1512885 / 10 ^ 12 : ℝ) + epsDyad + ε_clean) where
  pkOf D U hs_eq :=
      jung87TopHadWordsPackHalf_walkCert hStep hTop hd_hi cw D U (hs_eq.trans_le hs_le)
  counts D U hs_eq :=
      jung87TopHadWordsPackHalf_walkCert_counts hStep hTop hd_hi cw D U (hs_eq.trans_le hs_le)
  hwalk D U hs_eq :=
      hwalk_of_cleanWalkCertHalf_jung87_tophad_walkCert hStep hTop hd_hi cw D U (hs_eq.trans_le
      hs_le)

attribute [local semireducible] mkShared34DataLGenOff
attribute [local reducible] totDimCompactGen
def ambientFusedSpecsProgramNoEndReflLo5AsymOfPack
    {scrW scrL m offRefl d' tUsel tCsel tStep tRot0 tTop : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (hOff65 : 65 ≤ offRefl) (hm : offRefl + (m + 1) ≤ scrL)
    {εWalk0 α c εBlock : ℝ} (A : Operator (2 ^ systemQubits_frozen))
    (hB : BlockApproxSpecGen hamiltonian_frozen α c εBlock A)
    (wpk : WalkWordsCertPack scrW d' tCsel tStep tRot0 tTop α εWalk0)
    (S cselU uselU : LocalUnitary (totDimCompactGen scrW))
    (hlocal : SelectLocalSpecGen (scrSubLGen hp) (lcuSubLGen hp) A S.u cselU.u (reflULGen hp))
    (hUselCat : uselU.u.1 * cat8SharedProjCompactGen scrW = S.u.1 * cat8SharedProjCompactGen scrW)
    (cOf uOf : ∀ {Var : Type} {n : ℕ}, Var → QRegister systemQubits_frozen n →
        QRegister (ancWOfScr scrW) n → DynamicCircuit Var n)
    (hC : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
      (v : Var) (rS : QRegister systemQubits_frozen n) (rA : QRegister (ancWOfScr scrW) n)
          (hd : rS.DisjointWires rA),
      CleanWorkStep (rA.compose (scrSubLGen hp)) ((rS.concat rA hd).embedUnitary cselU.u)
          (cOf v rS rA) ∧
      CleanWorkStep (rA.compose (scrSubLGen hp)) ((rS.concat rA hd).embedUnitary uselU.u)
          (uOf v rS rA) ∧
      (cOf v rS rA).count .TOFF = 0 ∧ (uOf v rS rA).count .TOFF = 0 ∧
      (uOf v rS rA).count .T + 4 * (m + 1) ≤ tUsel ∧ (cOf v rS rA).count .T + 4 * (m + 1) ≤ tCsel)
    {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister systemQubits_frozen n)
        (rAnc : QRegister (ancWOfScr scrW) n) : DynamicCircuit Var n :=
  @dite _ (rSys.DisjointWires rAnc ∧ Nonempty (Fintype Var) ∧ Nonempty (DecidableEq Var))
    (Classical.dec _) (fun hcond ↦
      let _ : Fintype Var := hcond.2.1.some
      let _ : DecidableEq Var := hcond.2.2.some
      let hc := hC v rSys rAnc hcond.1
      let D :=
          mkShared34DataLGenOff hp (hOff65_le_scrL_31 hOff65 hm) hm v rSys rAnc hcond.1 α c εBlock A
          hB S cselU (cOf v rSys rAnc) hlocal hc.1 hc.2.2.1 hc.2.2.2.2.2
      let U : UselDataShared34 D :=
        { uselCirc := uOf v rSys rAnc, uselU := uselU.u, uselU_cat := hUselCat,
          usel_clean := hc.2.1, usel_toff := hc.2.2.2.1 }
      let pk := wpk.pkOf D U rfl
      bidirProgramFusedNoEndReflLo5_lo5j8 hp hm v D U
        (pureRotDyn (hAncCompact scrW) rAnc pk.1)
        (pureRotDyn (hAncCompact scrW) rAnc pk.2.1)
        pk.2.2)
    (fun _ ↦ .circuit .identity)

def unembedFusedSpecsProgramNoEndReflLo5AsymOfPack
    {scrW scrL m offRefl ancW' kIdle d' tUsel tCsel tStep tRot0 tTop : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (hOff65 : 65 ≤ offRefl) (hm : offRefl + (m + 1) ≤ scrL)
    (part : AncillaPartition (ancWOfScr scrW) ancW' kIdle)
    {εWalk0 α c εBlock : ℝ} (A : Operator (2 ^ systemQubits_frozen))
    (hB : BlockApproxSpecGen hamiltonian_frozen α c εBlock A)
    (wpk : WalkWordsCertPack scrW d' tCsel tStep tRot0 tTop α εWalk0)
    (S cselU uselU : LocalUnitary (totDimCompactGen scrW))
    (hlocal : SelectLocalSpecGen (scrSubLGen hp) (lcuSubLGen hp) A S.u cselU.u (reflULGen hp))
    (hUselCat : uselU.u.1 * cat8SharedProjCompactGen scrW = S.u.1 * cat8SharedProjCompactGen scrW)
    (cOf uOf : ∀ {Var : Type} {n : ℕ}, Var → QRegister systemQubits_frozen n →
        QRegister (ancWOfScr scrW) n → DynamicCircuit Var n)
    (hC : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
      (v : Var) (rS : QRegister systemQubits_frozen n) (rA : QRegister (ancWOfScr scrW) n)
          (hd : rS.DisjointWires rA),
      CleanWorkStep (rA.compose (scrSubLGen hp)) ((rS.concat rA hd).embedUnitary cselU.u)
          (cOf v rS rA) ∧
      CleanWorkStep (rA.compose (scrSubLGen hp)) ((rS.concat rA hd).embedUnitary uselU.u)
          (uOf v rS rA) ∧
      (cOf v rS rA).count .TOFF = 0 ∧ (uOf v rS rA).count .TOFF = 0 ∧
      (uOf v rS rA).count .T + 4 * (m + 1) ≤ tUsel ∧ (cOf v rS rA).count .T + 4 * (m + 1) ≤ tCsel)
    {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister systemQubits_frozen n)
        (rAncSmall : QRegister ancW' n) : DynamicCircuit Var n :=
  unembedProgram part (fun v' rS rA ↦
      ambientFusedSpecsProgramNoEndReflLo5AsymOfPack hp hOff65 hm A hB wpk S cselU uselU hlocal
      hUselCat cOf uOf hC v' rS rA) v rSys rAncSmall
end AmbientOuter

attribute [local irreducible] ambientFusedSpecsProgramNoEndReflLo5AsymOfPack
  unembedFusedSpecsProgramNoEndReflLo5AsymOfPack

def outerCoinProgNoEndReflHalfOfPack
    {wWork mCoin d' tUsel tCsel tStep tRot0 tTop : ℕ} {hg23 : 23 ≤ 23} {hmCoin : mCoin ≤ 80}
    {εWalk0 α c εBlock : ℝ} {A : Operator (2 ^ systemQubits_frozen)}
    (hB : BlockApproxSpecGen hamiltonian_frozen α c εBlock A)
    (wpk : WalkWordsCertPack scrWLayout d' tCsel tStep tRot0 tTop α εWalk0)
    (B : OuterCoinSelectBundleStackAsym 23 wWork mCoin tUsel tCsel hg23 hmCoin A)
    {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister systemQubits_frozen n)
    (rAnc : QRegister (outerCoinAncillasStack 23 wWork mCoin) n) : DynamicCircuit Var n :=
  unembedFusedSpecsProgramNoEndReflLo5AsymOfPack
    (hpStack mCoin hmCoin) hOff65Zero (hmStackOff65 mCoin hmCoin)
    (partOuterCoinStackOf 23 wWork mCoin hg23 hmCoin B.hwHi)
    A hB wpk B.S B.cselU B.uselU B.hlocal B.hUselCat B.cOf B.uOf B.hC v rSys rAnc

def outerCoinProgNoEndReflHalf
    {wWork mCoin d' tUsel tCsel : ℕ} (hd_hi : d' + 1 ≤ 3326913) {hg23 : 23 ≤ 23}
        {hmCoin : mCoin ≤ 80}
    {sMax δ ε_clean α c εBlock : ℝ}
    (cw : PhotochemistrySolution.HalfWalk.CleanWalkCertHalf (d' + 1) sMax δ ε_clean)
    {A : Operator (2 ^ systemQubits_frozen)}
    (hB : BlockApproxSpecGen hamiltonian_frozen α c εBlock A)
    (hs_le : α * evolutionTime_frozen ≤ sMax)
    (B : OuterCoinSelectBundleStackAsym 23 wWork mCoin tUsel tCsel hg23 hmCoin A)
    {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister systemQubits_frozen n)
    (rAnc : QRegister (outerCoinAncillasStack 23 wWork mCoin) n) : DynamicCircuit Var n :=
  outerCoinProgNoEndReflHalfOfPack hB
    (walkWordsCertPack_jung87Half exists_simp76_step_ep460 exists_top73_step_ep460 hd_hi cw hs_le)
    B v rSys rAnc

section TurnkeyProofs
attribute [local irreducible] systemQubits_frozen ancWOfScr bidirCoreNoEndReflLocalUnitary_lo5j8
    hamiltonian_frozen
attribute [local irreducible] bidirCorePureTopHadLocalUnitary_lo5j8 pureRotLocalUnitary
    jung87TopHadWordsPackHalf_walkCert
attribute [local semireducible] mkShared34DataLGenOff
attribute [local reducible] totDimCompactGen

attribute [local irreducible] pureRotDyn in
theorem outerCoinProgNoEndReflHalf_correctness
    {wWork mCoin d' tUsel tCsel : ℕ} (hd_hi : d' + 1 ≤ 3326913) {hg23 : 23 ≤ 23}
        {hmCoin : mCoin ≤ 80}
    {sMax δ ε_clean εWalk εHamBudget α c εBlock : ℝ}
    (cw : PhotochemistrySolution.HalfWalk.CleanWalkCertHalf (d' + 1) sMax δ ε_clean)
    {A : Operator (2 ^ systemQubits_frozen)}
    (hB : BlockApproxSpecGen hamiltonian_frozen α c εBlock A)
    (hs_le : α * evolutionTime_frozen ≤ sMax)
    (hwalk_sum : 2 * (1512885 / 10 ^ 12 : ℝ) + epsDyad + ε_clean ≤ εWalk)
    (hham_le : (α * evolutionTime_frozen) * εBlock ≤ εHamBudget)
    (htot_sum : εWalk + εHamBudget ≤ 0.01)
    (B : OuterCoinSelectBundleStackAsym 23 wWork mCoin tUsel tCsel hg23 hmCoin A)
    {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rSys : QRegister systemQubits_frozen n)
    (rAnc : QRegister (outerCoinAncillasStack 23 wWork mCoin) n) (hdisj : rSys.DisjointWires rAnc) :
    ∃ W' : Unitary (2 ^ (systemQubits_frozen + outerCoinAncillasStack 23 wWork mCoin)),
      ApproximatesTimeEvolution hamiltonian_frozen evolutionTime_frozen 0.01 1 W' ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W'
        (outerCoinProgNoEndReflHalf hd_hi cw hB hs_le B v rSys
          rAnc).compile := by
  let _ := Fintype.ofFinite Var
  let hp := hpStack mCoin hmCoin
  let hm := hmStackOff65 mCoin hmCoin
  let part := partOuterCoinStackOf 23 wWork mCoin hg23 hmCoin B.hwHi
  let wpk : WalkWordsCertPack scrWLayout d' tCsel _ _ _ α _ :=
    walkWordsCertPack_jung87Half exists_simp76_step_ep460 exists_top73_step_ep460 hd_hi cw hs_le
  have hIdleSafe :=
      hIdleSafe_partOuterCoinStackOf hg23 hmCoin (Nat.add_le_add_left B.hwLo 65) B.hwHi
  unfold outerCoinProgNoEndReflHalf
    outerCoinProgNoEndReflHalfOfPack
    unembedFusedSpecsProgramNoEndReflLo5AsymOfPack
  refine unembedProgram_correctness part _ ?_ ?_ v rSys rAnc hdisj
  · intro Var' instF instD k _ v' rS (rA : QRegister (ancWOfScr scrWLayout) k) hd
    by_cases hcond : rS.DisjointWires rA ∧ Nonempty (Fintype Var') ∧ Nonempty (DecidableEq Var')
    · cases Subsingleton.elim instF hcond.2.1.some
      cases Subsingleton.elim instD hcond.2.2.some
      let _ : Fintype Var' := hcond.2.1.some
      let _ : DecidableEq Var' := hcond.2.2.some
      let hc := B.hC v' rS rA hcond.1
      let D := mkShared34DataLGenOff hp (hOff65_le_scrL_31 hOff65Zero hm) hm v' rS rA hcond.1
        α c εBlock A hB B.S B.cselU (B.cOf v' rS rA) B.hlocal hc.1 hc.2.2.1 hc.2.2.2.2.2
      let U : UselDataShared34 D :=
        { uselCirc := B.uOf v' rS rA, uselU := B.uselU.u, uselU_cat := B.hUselCat,
          usel_clean := hc.2.1, usel_toff := hc.2.2.2.1 }
      let pk := wpk.pkOf D U rfl
      have hwalk := approximatesTimeEvolution_noEndRefl_of_orig D U pk.1 pk.2.1 pk.2.2
        (wpk.hwalk D U rfl)
      refine ⟨_, approximatesTimeEvolution_of_O1_O2_O3_walk D _ hwalk
        ((add_le_add hwalk_sum hham_le).trans htot_sum), ?_⟩
      unfold ambientFusedSpecsProgramNoEndReflLo5AsymOfPack
      rw [dite_eq_left hcond]
      exact realizes_bidirProgramFusedNoEndReflLo5_lo5j8 hp hOff65Zero hm v' D U
        rfl rfl rfl B.hCommC B.hCommU pk.1 pk.2.1 pk.2.2
    · exact False.elim (hcond ⟨hd, ⟨instF⟩, ⟨instD⟩⟩)
  · intro Var' k v' rSys' rAnc' hd' rAmb rPhantom
    have hanc := ancWOfScr_eq_fs scrWLayout
    have hancF : ancWOfScr ProviderCoreFused.scrWLayoutFused = ancWOfScr scrWLayout := rfl
    let rA := assembleAnc part (rAmb.compose rAnc') rPhantom (amb_disj_phantom rAnc')
    have hAncLt (j : Fin (ancWOfScr scrWLayout))
        (hj : (26 ≤ j.val ∧ j.val ≤ 30) ∨ j.val = ancWOfScr scrWLayout - 1) : (rA j).val < k := by
      refine UnembedO3Bridge.assembleAnc_val_lt_of_not_idle part rAnc' j fun l hl ↦ ?_
      have hu := hIdleSafe l
      dsimp only at hu
      rw [congrArg Fin.val hl] at hu
      have hj_lt := j.isLt
      omega
    unfold ambientFusedSpecsProgramNoEndReflLo5AsymOfPack
    split_ifs with hcond
    · let _ : Fintype Var' := hcond.2.1.some
      let _ : DecidableEq Var' := hcond.2.2.some
      obtain ⟨hcD, huD⟩ := B.hDyn v' (rAmb.compose rSys') rA
      have hCw := allWiresLtDyn_of_safeConcatActiveStack hg23 hmCoin B.hwHi rSys' rAnc'
        (dynWires_mono (fun _ ⟨hd, w, hw, eu⟩ ↦ ⟨hd, w, hw, eu⟩) hcD)
      have hUw := allWiresLtDyn_of_safeConcatActiveStack hg23 hmCoin B.hwHi rSys' rAnc'
        (dynWires_mono (fun _ ⟨hd, w, hw, eu⟩ ↦ ⟨hd, w, hw, eu⟩) huD)
      have hRefl := allWiresLtDyn_fastReflCircLGenOff hp hm part (fun l ↦ by
        have hu := hIdleSafe l
        dsimp only [part] at hu ⊢
        omega) v' rSys' rAnc' hd' hcond.1
      have hqsp : (qspQubitGen (hAncCompact scrWLayout) rA).val < k :=
        hAncLt ⟨ancWOfScr scrWLayout - 1, by omega⟩ (Or.inr rfl)
      have hgrad5 (i : Fin 5) : (gradReg5LoGen (hAncCompact scrWLayout) rA i).val < k :=
        hAncLt ⟨26 + i.val, by omega⟩
          (Or.inl ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.le_of_lt_succ i.isLt) 26⟩)
      have hprep5 := preparePhaseGradientLo8_3_lo5j8_onRegister _ ▸
        allWiresLtCirc_onRegister _ (gradReg5LoGen (hAncCompact scrWLayout) rA) hgrad5
      have hqs {g : PrimitiveGate 1} := allWiresLtCirc_single (g := g) hqsp
      have hrot (c : Circuit 1) :=
        allWiresLtDyn_pureRotDyn (Var := Var') (hAncCompact scrWLayout) rA c hqsp
      exact ⟨hprep5, ⟨hqs, hCw, hrot _, ⟨hRefl, hUw, allWiresLtDyn_foldFinDyn (fun _ ↦
        ⟨allWiresLtDyn_fusedReflPureRotDyn hp hOff65Zero hm part hIdleSafe v' rSys' rAnc' hd' _
          hcond.1, hUw⟩), hqs, hRefl, hqs, hrot _⟩, ⟨hqs, hCw, hqs⟩, hrot _⟩,
        allWiresLtCirc_inverse hprep5⟩
    · trivial

theorem outerCoinProgNoEndReflHalf_const_cost
    {wWork mCoin d' tUsel tCsel cost : ℕ} (hd_hi : d' + 1 ≤ 3326913) {hg23 : 23 ≤ 23}
        {hmCoin : mCoin ≤ 80}
    (_hm_init : 4 * (mCoin + 1) ≤ 497) {sMax δ ε_clean α c εBlock : ℝ}
    (cw : PhotochemistrySolution.HalfWalk.CleanWalkCertHalf (d' + 1) sMax δ ε_clean)
    {A : Operator (2 ^ systemQubits_frozen)}
    (hB : BlockApproxSpecGen hamiltonian_frozen α c εBlock A)
    (hs_le : α * evolutionTime_frozen ≤ sMax)
    (B : OuterCoinSelectBundleStackAsym 23 wWork mCoin tUsel tCsel hg23 hmCoin A)
    (hCost : (systemQubits_frozen + outerCoinAncillasStack 23 wWork mCoin) *
      bidirTotalTAsym (d' + 1) tUsel tCsel 76 (497 - 4 * (mCoin + 1)) ≤ cost)
    {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister systemQubits_frozen n)
    (rAnc : QRegister (outerCoinAncillasStack 23 wWork mCoin) n) :
    (outerCoinProgNoEndReflHalf hd_hi cw hB hs_le B v rSys rAnc).count .TOFF = 0 ∧
    (systemQubits_frozen + outerCoinAncillasStack 23 wWork mCoin) *
      (outerCoinProgNoEndReflHalf hd_hi cw hB hs_le B v rSys
        rAnc).count .T ≤ cost := by
  let hp := hpStack mCoin hmCoin
  let hm := hmStackOff65 mCoin hmCoin
  let part := partOuterCoinStackOf 23 wWork mCoin hg23 hmCoin B.hwHi
  let wpk : WalkWordsCertPack scrWLayout d' tCsel _ _ _ α _ :=
    walkWordsCertPack_jung87Half exists_simp76_step_ep460 exists_top73_step_ep460 hd_hi cw hs_le
  unfold outerCoinProgNoEndReflHalf
    outerCoinProgNoEndReflHalfOfPack
    unembedFusedSpecsProgramNoEndReflLo5AsymOfPack
  refine unembedProgram_const_cost part _ (T_max :=
    bidirTotalTAsym (d' + 1) tUsel tCsel 76 (497 - 4 * (mCoin + 1))) ?_ hCost v rSys rAnc
  intro Var' k v' rS (rA : QRegister (ancWOfScr scrWLayout) k)
  unfold ambientFusedSpecsProgramNoEndReflLo5AsymOfPack
  split_ifs with hcond
  · let _ : Fintype Var' := hcond.2.1.some
    let _ : DecidableEq Var' := hcond.2.2.some
    let hc := B.hC v' rS rA hcond.1
    let D := mkShared34DataLGenOff hp (hOff65_le_scrL_31 hOff65Zero hm) hm v' rS rA hcond.1
      α c εBlock A hB B.S B.cselU (B.cOf v' rS rA) B.hlocal hc.1 hc.2.2.1 hc.2.2.2.2.2
    let U : UselDataShared34 D :=
      { uselCirc := B.uOf v' rS rA, uselU := B.uselU.u, uselU_cat := B.hUselCat,
        usel_clean := hc.2.1, usel_toff := hc.2.2.2.1 }
    obtain ⟨hr0F, hr0T, hrtF, hrtT, hst⟩ := wpk.counts D U rfl
    let pk := wpk.pkOf D U rfl
    let hAnc := hAncCompact scrWLayout
    have hP5 := preparePhaseGradientLo8_3_lo5j8_count_t (gradReg5LoGen hAnc rA)
    have hU5 := unpreparePhaseGradientLo8_3_lo5j8_count_t (gradReg5LoGen hAnc rA)
    have husel : U.uselCirc.count .T + 4 * (mCoin + 1) ≤ tUsel := hc.2.2.2.2.1
    have hrefl : D.reflCirc.count .T = 4 * (mCoin + 1) :=
      (fastReflCircLGenOff_clean_and_count hp hm v' rS rA hcond.1).2.1
    have hsel := D.t_le
    have hStepF (i : Fin d') :
        (DynamicCircuit.seq (fusedReflPureRotDyn hp hm v' rS rA hcond.1 (pk.2.2 i.castSucc))
          U.uselCirc).count .T ≤ tUsel + 76 ∧
        (DynamicCircuit.seq (fusedReflPureRotDyn hp hm v' rS rA hcond.1 (pk.2.2 i.castSucc))
          U.uselCirc).count .TOFF = 0 := by
      obtain ⟨hfT, hfF⟩ := count_fusedReflPureRotDyn hp hm v' rS rA hcond.1 (pk.2.2 i.castSucc)
      obtain ⟨hsF, hsT⟩ : (pk.2.2 i.castSucc).count .TOFF = 0 ∧
          (pk.2.2 i.castSucc).count .T ≤ 76 := hst i.castSucc
      refine ⟨?_, by simp [DynamicCircuit.count, hfF, hsF, U.usel_toff]⟩
      simp only [DynamicCircuit.count, hfT]
      omega
    have hFoldT := count_foldFinDyn_le (tUsel + 76) _ (fun i ↦ (hStepF i).1)
    have hFoldF := Nat.eq_zero_of_le_zero (count_foldFinDyn_le 0 _ (fun i ↦ ((hStepF i).2).le))
    have hHT : (Circuit.H (qspQubitGen hAnc rA)).count .T = 0 := rfl
    have hXT : (Circuit.X (qspQubitGen hAnc rA)).count .T = 0 := rfl
    let prog := bidirProgramFusedNoEndReflLo5_lo5j8 hp hm v' D U
      (pureRotDyn hAnc rA pk.1) (pureRotDyn hAnc rA pk.2.1) pk.2.2
    change prog.count .TOFF = 0 ∧ prog.count .T ≤ _
    dsimp only [prog, pk] at hFoldT hFoldF ⊢
    refine ⟨?_, ?_⟩
    · simp only [bidirProgramFusedNoEndReflLo5_lo5j8, bidirBodyFusedNoEndReflLGenOff,
        Circuit.H, Circuit.X, DynamicCircuit.count, preparePhaseGradientLo8_3_lo5j8_count_toff,
        Circuit.count_gate, Sigma.mk.injEq, OfNat.one_ne_ofNat, false_and, ↓reduceIte, D.csel_toff,
        D.refl_toff, U.usel_toff, hFoldF, zero_add, add_zero,
        unpreparePhaseGradientLo8_3_lo5j8_count_toff, Nat.add_eq_zero_iff]
      exact ⟨(count_pureRotDyn _ _ _ _).trans hr0F, (count_pureRotDyn _ _ _ _).trans
        (hst (Fin.last d')).1, (count_pureRotDyn _ _ _ _).trans hrtF⟩
    · simp only [bidirProgramFusedNoEndReflLo5_lo5j8, bidirBodyFusedNoEndReflLGenOff,
        DynamicCircuit.count, hP5, hU5, hHT, hXT, bidirTotalTAsym]
      have hc0T := (count_pureRotDyn (Var := Var') hAnc rA _ .T).trans_le hr0T
      have hctT := (count_pureRotDyn (Var := Var') hAnc rA _ .T).trans_le hrtT
      have hrLastT := (count_pureRotDyn (Var := Var') hAnc rA _ .T).trans_le
        (hst (Fin.last d')).2
      have hsucc := Nat.add_one_mul d' (tUsel + 76)
      omega
  · exact ⟨rfl, Nat.zero_le _⟩
end TurnkeyProofs
end QuantumComputation.Specs.PhotochemistrySolution.NoEndRefl
end

end
