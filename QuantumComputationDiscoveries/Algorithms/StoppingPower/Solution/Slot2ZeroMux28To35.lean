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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SelectPass13Pruned

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Slot2ZeroMuxTrunc28To35Aux
local instance (priority := 1000000) instNeZeroTwoPow_Slot2ZeroMuxTrunc28To35 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section
section Slot2ZeroMuxTrunc28To35

section ModSlot2ZeroMuxTrunc28To35
public section
namespace Slot2ZeroMuxTrunc28To35
section PartA_ZeroMuxSkip
set_option maxRecDepth 4096
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64WalkCircuit
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes
open WindowedSlot2MulKick288
open Slot2ZeroMuxSignedMul46
open HeldMsbInc7ApexWrap288 (mEffBits)
local instance (priority :=
  1000000) instLoc_Slot2ZeroMuxTrunc28To35_1InstNeZeroTwoPowSlo (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
attribute [local irreducible]
  cnotFanoutCircuit apexGidneyRippleAuxDyn apexGidneyRippleAuxCircuit apexGidneyNoCinDyn
  apexGidneyNoCinCircuit ctrlSignApexShiftDyn
attribute [local irreducible] apexCatModAddZ
theorem bitsVal_of_prefix_zero {k r m : ℕ} (hkr : k + r = m) (B : Fin m → ZMod 2) (h0 : ∀ j : Fin k,
    B ⟨j.val, by omega⟩ = 0) :
    bitsVal B = 2 ^ k * bitsVal (fun j : Fin r ↦ B ⟨k + j.val, by omega⟩) := by
  have hSp := regVal_split_at_shift hkr (QRegExt.idReg m) B
  change bitsVal B = bitsVal (fun j : Fin k ↦ B ⟨j.val, by omega⟩) +
    2 ^ k * bitsVal (fun j : Fin r ↦ B ⟨k + j.val, by omega⟩) at hSp
  have hLo : (fun j : Fin k ↦ B ⟨j.val, by omega⟩) = fun _ ↦ 0 := funext h0
  rw [hSp, hLo]
  unfold bitsVal
  simp [show (0 : ZMod 2).val = 0 from rfl]
theorem bitsVal_mEffBits_prefix {skip m : ℕ} (hsk : skip ≤ m) (hm48 : m ≤ 48) (M : Fin 48 →
    ZMod 2) :
    bitsVal (fun j : Fin m ↦
      mEffBits skip M ⟨j.val, by omega⟩) = 2 ^ skip * bitsVal (fun j : Fin (m - skip) ↦
      M ⟨j.val + skip, by omega⟩) := by
  rw [bitsVal_of_prefix_zero (Nat.add_sub_of_le hsk) _ (fun j ↦ ite_eq_left j.isLt)]
  refine congrArg (fun x : Fin (m - skip) → ZMod 2 ↦ 2 ^ skip * bitsVal x) (funext fun j ↦ ?_)
  dsimp only [mEffBits]
  rw [ite_eq_right (show ¬ (skip + j.val < skip) by omega)]
  exact congrArg M (Fin.ext (show skip + j.val = j.val + skip by omega))
theorem bitsVal_mEffBits_eq {skip : ℕ} (hsk48 : skip ≤ 48) (M : Fin 48 →
    ZMod 2) : bitsVal (mEffBits skip M) =
    2 ^ skip * bitsVal (fun j : Fin (48 - skip) ↦ M ⟨j.val + skip, by omega⟩) :=
  bitsVal_mEffBits_prefix hsk48 le_rfl M
theorem bitsVal_47_mEffBits_eq {skip : ℕ} (hsk1 : 1 ≤ skip) (hsk48 : skip ≤ 48) (M : Fin 48 →
    ZMod 2) :
    bitsVal (fun j : Fin 47 ↦
      mEffBits skip M j.succ) = 2 ^ (skip - 1) * bitsVal (fun j : Fin (48 - skip) ↦
      M ⟨j.val + skip, by omega⟩) := by
  rw [bitsVal_of_prefix_zero (by omega : (skip - 1) + (48 - skip) = 47) _
    (fun j ↦ ite_eq_left (show j.val + 1 < skip by omega))]
  refine congrArg (fun x : Fin (48 - skip) → ZMod 2 ↦ 2 ^ (skip - 1) * bitsVal x) (funext fun j ↦
    ?_)
  simpa only [mEffBits, Fin.val_succ,
    ite_eq_right (show ¬ ((skip - 1) + j.val + 1 < skip) by omega)]
    using congrArg M (Fin.ext (show (skip - 1) + j.val + 1 = j.val + skip by omega))
set_option maxRecDepth 2000
end PartA_ZeroMuxSkip
end Slot2ZeroMuxTrunc28To35
end
end ModSlot2ZeroMuxTrunc28To35
end Slot2ZeroMuxTrunc28To35
end
end Slot2ZeroMuxTrunc28To35Aux

section MomSlot1DyadicTopAdapterAux
local instance (priority := 1000000) instNeZeroTwoPow_MomSlot1DyadicTopAdapter (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section
section MomSlot1DyadicTopAdapter

section ModMomSlot1DyadicTopAdapter
public section
namespace MomSlot1DyadicTopAdapter
section ConfigMomSlot1DyadicTopAdapter
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority :=
  1000000) instLoc_MomSlot1DyadicTopAdapter_1InstNeZeroTwoPowMo (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem sum_rearrange_gen {V : Type*} [AddCommGroup V] [Module ℂ V] (αinv w0 w1 w2 w3 w4 w5 c2 c3 ds
    : ℂ) (hds : c2 - c3 = αinv * ds)
    (b0 b1 b2 b3 b4 b5 u1 : V) : (αinv * w2) • b2 + (αinv * w4) • b4 + c2 • u1 + c3 • (-u1) +
    (αinv * w0) • b0 + (αinv * w1) • b1 + (αinv * w3) • b3 + (αinv * w5) • b5 = αinv • ((w0 •
    b0 + w1 • b1 + w2 • b2 + w3 • b3 + w4 • b4 + w5 • b5) + ds • u1) := by
  rw [add_assoc ((αinv * w2) • b2 + (αinv * w4) • b4) (c2 • u1) (c3 • (-u1)), smul_neg,
    ← sub_eq_add_neg, ← sub_smul, hds]
  simp only [← smul_smul, smul_add]
  abel

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem heff_shift_diff_eq {n : Type*} [Fintype n] [DecidableEq n]
    (G S_act S_id H_id Δ : Matrix n n ℂ) (hGG : G * G = G) (e0 ds : ℝ) (hSubId : H_id -
      (e0 : ℂ) • (1 : Matrix n n ℂ) = G * S_id * G)
    (hSumDiff : S_act - S_id = Δ) : G * ((G * (S_act + (ds : ℂ) • (1 : Matrix n n ℂ)) * G +
    ((e0 - ds : ℝ) : ℂ) • (1 : Matrix n n ℂ)) - H_id) * G = G * Δ * G := by
  have hGGG (X : Matrix n n ℂ) : G * (G * X * G) * G = G * X * G :=
    (by simp only [Matrix.mul_assoc] : _ = (G * G) * X * (G * G)).trans (by rw [hGG])
  have hGs1G (c : ℂ) : G * (c • (1 : Matrix n n ℂ)) * G = c • G := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hGG]
  have hSc : (ds : ℂ) + ((e0 - ds : ℝ) : ℂ) = (e0 : ℂ) :=
    (Complex.ofReal_add ds (e0 - ds)).symm.trans (congrArg Complex.ofReal (add_sub_cancel ds e0))
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, hGGG, Matrix.mul_add,
    Matrix.add_mul, hGs1G, hGs1G, add_assoc, ← add_smul, hSc, eq_add_of_sub_eq hSubId,
    Matrix.mul_add, Matrix.add_mul, hGGG, hGs1G, add_sub_add_right_eq_sub, ← Matrix.sub_mul,
    ← Matrix.mul_sub, hSumDiff]
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open PosMomSelectSandwich (slotBitProj)
open PosMomSelectDynamic (unitaryConj)
open FullSysCatSegmentBridge
  (fullSysCoreWires iSlot2)
open FullSysMomSlots0135Concrete
  (iSlot2Mom momCoinProj MomSingleSlotOracle)
open HoistedSwapSelectBridge (FullSysHoistedSelectBundle)
open FullSysHoistedSelectStitch (HoistedBarrelBundle HoistedBarrelSpec)
open MomSlot0CircuitHalf (slot0ElectronKineticOracleSym)
open MomSlot0LocalAndMomCombine288 (MomLocalSlotData slot0LocalWorkWires)
open MomSlot1Dyadic459Sub36w
  (slot1DyadicWorkWires
     slot1DyadicSelectUnitary_conj_highWire
   slot1Dyadic459OracleSym)
open OraAndPrepBundle
  (castNatCat_intertwines
   momCoreWires_eq_fullSysCoreWires momCatWires_eq_fullSysCatWires
   coreUnitaryToFullSys coreUnitaryFromFullSys catUnitaryToFullSys
    fin6Tuple)
open GeneralBetaAndAlphaTopEndpoint
  (HoistedTwistRestOutBundle iSlot2_ge_3924 iSlot2_ge_3948
   iSlot2_lt_3951)
open TierClosure
  (castNatUnitary_comm_slotBitProj castNatUnitary_sa castNatUnitary_mul_slotBitProj_id
   castNatUnitary_conj_val_eq mkSlot0LocalDataOfBarrelFast liftSlot3OfBarrelFast)
open PosSlots24TopWrapper (PosSlots24DataGen)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
structure HoistedMomLocalBundleS1 {mPayload mPGTwist : ℕ} (hm80 : 80 ≤ mPayload) (mWork : ℕ)
    (barrel : HoistedBarrelBundle mPayload mWork) (s1 : MomSingleSlotOracle mPayload mPGTwist 1)
    (s3 : MomSingleSlotOracle mPayload mPGTwist 3) (s5 : MomSingleSlotOracle mPayload mPGTwist 5)
      where
  uMomLocalCat : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload +
    mPGTwist))
  uMomLocal : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))
  hIntertwinesMomLocal : ∀ cfg (U_catTwist : Unitary (2 ^ mPGTwist)),
    (∀ m : Fin (2 ^ mPGTwist),
      U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState mPGTwist m) →
    FullSysCatSegmentBridge.IntertwinesLocalCat U_catTwist (uMomLocalCat cfg) (uMomLocal cfg)
  hMomLocal_sa : ∀ cfg, (uMomLocal cfg).1ᴴ = (uMomLocal cfg).1
  hMomLocal_on_P0 : ∀ cfg,
    (uMomLocal cfg).1 * slotBitProj (iSlot2 mPayload) 0 = slotBitProj (iSlot2 mPayload) 0
  hCoin4 : ∀ cfg, (coreUnitaryFromFullSys
      (HoistedSwapSelectBridge.unitaryConj (barrel.uBarrel cfg) (uMomLocal cfg))).1 *
    momCoinProj mPayload 4 = ((slot0ElectronKineticOracleSym hm80).uSlotEff cfg).1 *
      momCoinProj mPayload 4
  hCoin5 : ∀ cfg, (coreUnitaryFromFullSys
      (HoistedSwapSelectBridge.unitaryConj (barrel.uBarrel cfg) (uMomLocal cfg))).1 *
    momCoinProj mPayload 5 = (s1.uSlotEff cfg).1 * momCoinProj mPayload 5
  hCoin6 : ∀ cfg, (coreUnitaryFromFullSys
      (HoistedSwapSelectBridge.unitaryConj (barrel.uBarrel cfg) (uMomLocal cfg))).1 *
    momCoinProj mPayload 6 = (s3.uSlotEff cfg).1 * momCoinProj mPayload 6
  hCoin7 : ∀ cfg, (coreUnitaryFromFullSys
      (HoistedSwapSelectBridge.unitaryConj (barrel.uBarrel cfg) (uMomLocal cfg))).1 *
    momCoinProj mPayload 7 = (s5.uSlotEff cfg).1 * momCoinProj mPayload 7
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
abbrev HoistedMomLocalSpecS1 := @HoistedMomLocalBundleS1
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def mkHoistedMomLocalSpecS1 {mPayload mWork : ℕ} (hm80 : 80 ≤ mPayload)
    (barrel : HoistedBarrelSpec mPayload mWork) (s1 : MomSingleSlotOracle mPayload 48 1)
    (l0 : MomLocalSlotData mPayload 48 0 (fun cfg ↦ coreUnitaryFromFullSys (barrel.uBarrel cfg)))
    (l1 : MomLocalSlotData mPayload 48 1 (fun cfg ↦ coreUnitaryFromFullSys (barrel.uBarrel cfg)))
    (l3 : MomLocalSlotData mPayload 48 3 (fun cfg ↦ coreUnitaryFromFullSys (barrel.uBarrel cfg)))
    (l5 : MomLocalSlotData mPayload 48 5 (fun cfg ↦ coreUnitaryFromFullSys (barrel.uBarrel cfg)))
    (hl0 : l0.oracle = slot0ElectronKineticOracleSym hm80) (hl1 : l1.oracle = s1) (hw0 : l0.mWork ≤
      mWork) (hw1 : l1.mWork ≤ mWork) (hw3 : l3.mWork ≤ mWork)
    (hw5 : l5.mWork ≤ mWork) : HoistedMomLocalSpecS1 hm80 mWork barrel s1 l3.oracle l5.oracle :=
  let hCoreEq := momCoreWires_eq_fullSysCoreWires mPayload
  let hCatEq := momCatWires_eq_fullSysCatWires mPayload 48
  let comb := MomSlot0LocalAndMomCombine288.combineFourLocalMomSlots l0 l1 l3 l5 hw0 hw1 hw3 hw5
    (fun cfg ↦ castNatUnitary_comm_slotBitProj hCoreEq (barrel.uBarrel cfg)
      (barrel.hHighWireComm cfg))
  have hConj (cfg) := castNatUnitary_conj_val_eq hCoreEq (barrel.uBarrel cfg) (comb.uMomLocal cfg)
  { uMomLocalCat := fun cfg ↦ catUnitaryToFullSys (comb.uMomLocalCat cfg)
    uMomLocal := fun cfg ↦ coreUnitaryToFullSys (comb.uMomLocal cfg)
    hIntertwinesMomLocal := fun cfg U_cat hcol ↦ castNatCat_intertwines hCoreEq hCatEq U_cat
      (comb.uMomLocalCat cfg) (comb.uMomLocal cfg) (comb.hIntertwinesMomLocal cfg U_cat hcol)
    hMomLocal_sa := fun cfg ↦ castNatUnitary_sa hCoreEq (comb.uMomLocal cfg) (comb.hMomLocal_sa cfg)
    hMomLocal_on_P0 := fun cfg ↦ castNatUnitary_mul_slotBitProj_id hCoreEq (comb.uMomLocal cfg)
      _ _ rfl 0 (comb.hMomLocal_on_P0 cfg)
    hCoin4 := fun cfg ↦ (congrArg (· * _) (hConj cfg)).trans (hl0 ▸ comb.hCoin4 cfg)
    hCoin5 := fun cfg ↦ (congrArg (· * _) (hConj cfg)).trans (hl1 ▸ comb.hCoin5 cfg)
    hCoin6 := fun cfg ↦ (congrArg (· * _) (hConj cfg)).trans (comb.hCoin6 cfg)
    hCoin7 := fun cfg ↦ (congrArg (· * _) (hConj cfg)).trans (comb.hCoin7 cfg) }
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def mkHoistedMomLocalFromS1S3L5Fast {mPayload mWork : ℕ} (hm80 : 80 ≤ mPayload)
    (hm288 : 288 ≤ mWork) (barrel : HoistedBarrelSpec mPayload mWork) (hBarrelEq : ∀ cfg,
      barrel.uBarrel cfg = CoinDispatchedBarrel288.uBarrelFast hm80)
    (s3 : MomSingleSlotOracle mPayload 48 3) (l5 : MomLocalSlotData mPayload 48 5 (fun cfg ↦
    coreUnitaryFromFullSys (barrel.uBarrel cfg))) (hw3 : s3.mWork ≤ mWork) (hw5 : l5.mWork ≤
      mWork) : HoistedMomLocalSpecS1 hm80 mWork barrel
    (slot1Dyadic459OracleSym hm80) s3 l5.oracle :=
  let ref1 := slot1Dyadic459OracleSym hm80
  let l1 : MomLocalSlotData mPayload 48 1 (fun cfg ↦ coreUnitaryFromFullSys (barrel.uBarrel cfg)) :=
    MomLocalSlotData.ofCoreOnly slot1DyadicWorkWires ref1 ref1.uSlotEff
      ref1.hSA ref1.hOffCoin (fun cfg ↦ congrArg (· * momCoinProj mPayload 5) (congrArg Subtype.val
        (slot1DyadicSelectUnitary_conj_highWire hm80 cfg _ (fun q hq bit ↦
          castNatUnitary_comm_slotBitProj (momCoreWires_eq_fullSysCoreWires mPayload)
            (barrel.uBarrel cfg) (barrel.hHighWireComm cfg) q hq bit))))
  mkHoistedMomLocalSpecS1 hm80 barrel ref1
    (mkSlot0LocalDataOfBarrelFast hm80 barrel.uBarrel hBarrelEq) l1
    (liftSlot3OfBarrelFast hm80 s3 barrel.uBarrel hBarrelEq) l5 rfl rfl
    (le_trans (by decide : slot0LocalWorkWires ≤ 288) hm288)
    (le_trans (by decide : slot1DyadicWorkWires ≤ 288) hm288) hw3 hw5
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def mkFullSysHoistedSelectBundleOutS1 {mPayload mWork mWorkPos : ℕ}
    {hm22 : 22 ≤ mPayload} {hm80 : 80 ≤ mPayload} (barrel : HoistedBarrelSpec mPayload mWork)
    (twistRest : HoistedTwistRestOutBundle (mPayload := mPayload) (mPGTwist := 48) mWork)
    (posData : PosSlots24DataGen (fullSysCoreWires mPayload) (iSlot2 mPayload) mWorkPos)
    (s1 : MomSingleSlotOracle mPayload 48 1) (s3 : MomSingleSlotOracle mPayload 48 3)
    (s5 : MomSingleSlotOracle mPayload 48 5)
    (momLoc : HoistedMomLocalSpecS1 hm80 mWork barrel s1 s3 s5) (_hmPos : mWorkPos ≤ mWork) :
    FullSysHoistedSelectBundle mPayload 48 :=
  { hmPay := le_trans (by decide : 6 ≤ 22) hm22
    uBarrel := barrel.uBarrel
    uMomLocalCat := momLoc.uMomLocalCat
    uMomLocal := momLoc.uMomLocal
    uTwistRestCat := twistRest.uTwistRestCat
    uTwistRest := twistRest.uTwistRest
    uPosPhase := posData.uPosPhase
    hIntertwinesMomLocal := momLoc.hIntertwinesMomLocal
    hIntertwinesTwistRest := twistRest.hIntertwinesTwistRest
    hBarrel_comm_P0 := fun cfg ↦
      barrel.hHighWireComm cfg (iSlot2 mPayload) (iSlot2_ge_3924 mPayload) 0
    hMomLocal_sa := momLoc.hMomLocal_sa
    hMomLocal_on_P0 := momLoc.hMomLocal_on_P0
    hTwistRest_comm_P1 := fun cfg ↦
      twistRest.hCoinWireComm cfg (iSlot2 mPayload) (iSlot2_ge_3948 mPayload) (iSlot2_lt_3951
        mPayload) 1
    hPos_sa := posData.hPos_sa
    hPos_on_P1 := posData.hPos_on_P1 }
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
noncomputable def zeroSubwireEpsSlotOfEps2S1 (s1 : MomSingleSlotOracle 80 48 1) (s3 :
    MomSingleSlotOracle 80 48 3) (eps2 eps4 : ℝ) : Fin 6 → ℝ := fin6Tuple
    (slot0ElectronKineticOracleSym (le_refl 80)).epsIntr s1.epsIntr ((109 / 108 : ℝ) * eps2)
    s3.epsIntr eps4 0
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem zeroSubwireEpsSlotS1_sum_le_of_bounds (s1 : MomSingleSlotOracle 80 48 1) {e1 : ℝ}
    (hs1Eps : s1.epsIntr ≤ e1) (s3 : MomSingleSlotOracle 80 48 3) {e3 : ℝ} (hs3Eps : s3.epsIntr ≤
      e3) {eps2 eps4 b2 b4 cap : ℝ} (heps2 : eps2 ≤ b2)
    (heps4 : eps4 ≤ b4) (hSum : (slot0ElectronKineticOracleSym (le_refl 80)).epsIntr + e1 + (109 /
      108 : ℝ) * b2 + e3 + b4 ≤ cap) :
    (∑ k : Fin 6, zeroSubwireEpsSlotOfEps2S1 s1 s3 eps2 eps4 k) ≤ cap := by
  rw [Fin.sum_univ_six]
  change (slot0ElectronKineticOracleSym (le_refl 80)).epsIntr + s1.epsIntr +
    (109 / 108 : ℝ) * eps2 + s3.epsIntr + eps4 + 0 ≤ cap
  linarith
set_option maxRecDepth 512
end ConfigMomSlot1DyadicTopAdapter
end MomSlot1DyadicTopAdapter
end
end ModMomSlot1DyadicTopAdapter
end MomSlot1DyadicTopAdapter
end
end MomSlot1DyadicTopAdapterAux

section Leaf4Twist162
local instance (priority := 1000000) instNeZeroTwoPow_Leaf4Twist162 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace Leaf4Twist162

section ConfigLeaf4Twist162

set_option maxRecDepth 4096

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation

open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open FullSysCatSegmentBridge (coreCosetB1Block fullSysCoreWires)
open NuclearTwistAndXor654Concrete (nuclearM48 rNucIdx wSlot0 wSlot1 wSlot2)
open NuclearTwistRealizes (RealizesCleanPair basisBits_symm_apply coin0Active
  dite_neg_eq dite_pos_eq embedUnitary_idReg_eq
  slot2AxisSum slot2M48Val uXor32Core)

open FusedPreDiagFromTwist288 (hm6_of_hm22)
open ProjZ512QftAndTwist288
  (rCoreBlock48 vepHighNuc vepLockVal vepLockVal_eq vepOnlyM48Val vepProj9CoreIdx)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open SharedUnary108ZeroTUncompTwist
open HeldMsbInc7ApexWrap288 (mEffBits apexKoffDelta)
open SubvoxelNuclearTrunc34And33Physics (truncWCfg)
open FusedVepCore288 (DiagOn mat_ext_basisKet regVal_shiftCatKet shiftCatKet shiftCatKet_outside)
open UltraAsymVepTwist288 (realizesClean_of_workspace_subset)
open Slot2ZeroMuxSignedMul46 (apexCatModAddZ)
open MeasureBranchHadamardSem (bit_cases)
open MomSlot0CircuitHalf (phaseDiagUnitary)

local instance (priority :=
  1000000) instLoc_Leaf4Twist162_1InstNeZeroTwoPowTwist162 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- Register-commutation predicate matching `Leaf4Ext48TopStitch.CommutesWithReg` (`rfl`). -/
abbrev CommutesWithReg {k n : ℕ} (r : QRegister k n) (M : Operator (2 ^ n)) : Prop :=
  ∀ B : Operator (2 ^ k), M * r.embedMatrix B = r.embedMatrix B * M

/-- Exact T-count of `dSlot2ZeroMuxTruncSkip_koff` at `skip = 48 - K` (`12 <= skip <= 20`). -/
def tZeroMuxSkip (skip : ℕ) : ℕ :=
  (4 * (46 - skip) + 2) + ∑ i : Fin 13, (4 * (45 - skip - i.val) + 2)

def rSum14Of42 {n : ℕ} (w : Fin 3) (rSum42 : QRegister 42 n) : QRegister 14 n :=
  rSum42.slice (14 * w.val) 14 (by have := w.isLt; omega)

theorem core_ge_3954 (mPayload : ℕ) : 3954 ≤ fullSysCoreWires mPayload := by
  dsimp [FullSysCatSegmentBridge.fullSysCoreWires,
    NuclearTwistAndXor654Concrete.fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega

def rMPad48 {mPayload K n : ℕ} (hK48 : K ≤
    48) (rCore : QRegister (fullSysCoreWires mPayload) n) (rMK : QRegister K n)
    (hCMK : rCore.DisjointWires rMK) : QRegister 48 n :=
  ⟨⟨fun i ↦
      if hi : i.val < 48 - K then
        rCore ⟨14 + i.val, Nat.lt_of_lt_of_le (by omega) (core_ge_3954 mPayload)⟩
      else rMK ⟨i.val - (48 - K), by omega⟩,
    fun x y hxy ↦ by
      dsimp only at hxy
      split_ifs at hxy with hx hy
      · exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (rCore.wires.injective hxy)))
      · exact (hCMK.ne _ _ hxy).elim
      · exact (hCMK.ne _ _ hxy.symm).elim
      · have hv : x.val - (48 - K) = y.val - (48 - K) := congrArg Fin.val (rMK.wires.injective hxy)
        exact Fin.ext (by omega)⟩⟩

theorem rMPad48_apply {mPayload K n : ℕ} (hK48 : K ≤
    48) (rCore : QRegister (fullSysCoreWires mPayload) n) (rMK : QRegister K n)
    (hCMK : rCore.DisjointWires rMK) (i : Fin 48) : rMPad48 hK48 rCore rMK hCMK i = if hi : i.val <
      48 - K then
    rCore ⟨14 + i.val, Nat.lt_of_lt_of_le (by
      omega) (core_ge_3954 mPayload)⟩ else rMK ⟨i.val - (48 - K), by omega⟩ := rfl

abbrev rHi54Of61 {n : ℕ} (rHdr61 : QRegister 61 n) : QRegister 54 n :=
  rHdr61.slice 7 54 (by decide)

theorem seven_add_lt61 (q : Fin 54) : 7 + q.val < 61 := by omega

def xorMKBitsFn {kCH K : ℕ} (valFn : BitAssignment kCH → Fin K → ZMod 2) (γ : BitAssignment (kCH +
    K)) : BitAssignment (kCH + K) := fun idx ↦
  if h : idx.val < kCH then γ idx
  else γ idx + valFn (fun q ↦ γ (Fin.castAdd K q)) ⟨idx.val - kCH, by omega⟩

theorem xorMKBitsFn_lt {kCH K : ℕ} (valFn : BitAssignment kCH → Fin K → ZMod 2)
    (γ : BitAssignment (kCH + K)) (idx : Fin (kCH + K)) (h : idx.val <
      kCH) : xorMKBitsFn valFn γ idx = γ idx := dite_pos_eq h

theorem xorMKBitsFn_ge {kCH K : ℕ} (valFn : BitAssignment kCH → Fin K → ZMod 2)
    (γ : BitAssignment (kCH + K)) (idx : Fin (kCH + K)) (h : ¬(idx.val <
      kCH)) : xorMKBitsFn valFn γ idx =
    γ idx + valFn (fun q ↦ γ (Fin.castAdd K q)) ⟨idx.val - kCH, by omega⟩ := dite_neg_eq h

theorem xorMKBitsFn_involutive {kCH K : ℕ} (valFn : BitAssignment kCH → Fin K → ZMod 2) :
    Function.Involutive (xorMKBitsFn valFn) := fun γ ↦
  funext fun idx ↦ if h : idx.val < kCH then by
    rw [xorMKBitsFn_lt _ _ _ h, xorMKBitsFn_lt _ _ _ h]
  else by
    rw [xorMKBitsFn_ge _ _ _ h, xorMKBitsFn_ge _ _ _ h,
      funext fun q : Fin kCH ↦ xorMKBitsFn_lt valFn γ (Fin.castAdd K q) q.isLt]
    exact CleanZeroSlot2AxisSum288.zmod2_add_self_cancel _ _

/-- Self-inverse unitary on `2 ^ (kCH + K)` induced by `xorMKBitsFn valFn`. -/
noncomputable def uXorMK {kCH K : ℕ} (valFn : BitAssignment kCH → Fin K → ZMod 2) : Unitary
    (2 ^ (kCH + K)) := Operator.permutationUnitary ((basisBitsEquiv (kCH + K)).trans
    ((Equiv.ofBijective (xorMKBitsFn valFn) (xorMKBitsFn_involutive valFn).bijective).trans
    (basisBitsEquiv (kCH + K)).symm))

theorem embedUnitary_uXorMK_mulVec_ket {kCH K n : ℕ} [NeZero (2 ^ n)]
    (valFn : BitAssignment kCH → Fin K → ZMod 2) (rCH : QRegister kCH n) (rMK : QRegister K n)
    (hCHM : rCH.DisjointWires rMK) (β : BitAssignment n) :
    ((rCH.concat rMK hCHM).embedUnitary (uXorMK valFn)).1.mulVec (basisKet β) =
      basisKet (fun u ↦
        if hu : u ∈ rMK.image then
          let j := Classical.choose ((QRegister.mem_image rMK u).mp hu)
          β (rMK j) + valFn (fun q ↦ β (rCH q)) j
        else β u) := by
  let rAct := rCH.concat rMK hCHM
  refine NuclearTwistRealizes.embedUnitary_perm_mulVec_basisKet rAct _ β _ (fun idx ↦
    ?_) (fun z hz ↦ ?_)
  · rw [NuclearTwistRealizes.basisBits_perm_ofBijective (xorMKBitsFn valFn)
      (xorMKBitsFn_involutive valFn).bijective]
    by_cases hlt : idx.val < kCH
    · rw [xorMKBitsFn_lt _ _ _ hlt, dite_neg_eq (by
        rw [show idx = Fin.castAdd K ⟨idx.val, hlt⟩ from Fin.ext rfl, QRegister.concat_apply_left]
        exact hCHM.apply_not_mem_right _)]
    · let j : Fin K := ⟨idx.val - kCH, by omega⟩
      have hact : rAct idx = rMK j := (congrArg rAct
        (Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hlt)).symm)).trans
        (QRegister.concat_apply_right rCH rMK hCHM j)
      have hmM : rAct idx ∈ rMK.image := hact ▸ (QRegister.mem_image rMK _).mpr ⟨j, rfl⟩
      rw [xorMKBitsFn_ge _ _ _ hlt, dite_pos_eq hmM,
        rMK.wires.injective
          ((Classical.choose_spec ((QRegister.mem_image rMK _).mp hmM)).trans hact),
        hact, funext fun q : Fin kCH ↦ congrArg β (QRegister.concat_apply_left rCH rMK hCHM q)]
  · refine dite_neg_eq fun hm_in ↦ ?_
    obtain ⟨j, rfl⟩ := (QRegister.mem_image rMK z).mp hm_in
    exact hz ((QRegister.mem_image rAct _).mpr
      ⟨Fin.natAdd kCH j, QRegister.concat_apply_right rCH rMK hCHM j⟩)

theorem block0_concat_block_eq_idReg (a b : ℕ) : (QRegister.block 0 a (by
    omega)).concat (QRegister.block a b le_rfl)
    (QRegister.block_disjoint_of_le 0 a a b (by
      omega) le_rfl (by omega)) = QRegExt.idReg (a + b) := by
  apply qreg_ext
  intro idx
  by_cases h : idx.val < a
  · rw [show idx = Fin.castAdd b ⟨idx.val, h⟩ from Fin.ext rfl, QRegister.concat_apply_left]
    exact Fin.ext (by simp [QRegExt.idReg])
  · rw [show idx = Fin.natAdd a ⟨idx.val - a, by omega⟩ from
        Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt h)).symm,
      QRegister.concat_apply_right]
    exact Fin.ext (by simp [QRegExt.idReg])

theorem uXorMK_mul {kCH K : ℕ} (fn₁ fn₂ : BitAssignment kCH → Fin K → ZMod 2) : uXorMK fn₁ *
    uXorMK fn₂ = uXorMK (fun x j ↦ fn₁ x j + fn₂ x j) := by
  refine Subtype.ext (mat_ext_basisKet fun γ ↦ ?_)
  let rCH0 : QRegister kCH (kCH + K) := .block 0 kCH (by omega)
  let rM0 : QRegister K (kCH + K) := .block kCH K le_rfl
  have hdisj := QRegister.block_disjoint_of_le 0 kCH kCH K (by omega) le_rfl (by omega)
  have hev (fn : BitAssignment kCH → Fin K → ZMod 2) (η : BitAssignment (kCH + K)) := by
    have h0 := embedUnitary_uXorMK_mulVec_ket fn rCH0 rM0 hdisj η
    rwa [block0_concat_block_eq_idReg kCH K, embedUnitary_idReg_eq] at h0
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hev fn₂ γ, hev fn₁ _, hev _ γ]
  refine congrArg basisKet (funext fun u ↦ ?_)
  by_cases hu : u ∈ rM0.image
  · obtain ⟨j, rfl⟩ := (QRegister.mem_image rM0 u).mp hu
    have hch : Classical.choose ((QRegister.mem_image rM0 (rM0 j)).mp hu) = j :=
      rM0.wires.injective (Classical.choose_spec ((QRegister.mem_image rM0 (rM0 j)).mp hu))
    have hNotM (q : Fin kCH) : rCH0 q ∉ rM0.image := hdisj.apply_not_mem_right q
    simp only [hu, hNotM, ↓reduceDIte, hch]
    ring
  · simp only [hu, ↓reduceDIte]

theorem uXorMK_inv {kCH K : ℕ} (valFn : BitAssignment kCH → Fin K → ZMod 2) : (uXorMK valFn)⁻¹ =
    uXorMK valFn :=
  NuclearTwistDisentangleSum288.permUnitaryBits_inv_eq_self
    (xorMKBitsFn valFn) (xorMKBitsFn_involutive valFn)

/-- Local involutive `(K + kCtrl)`-wire bit-assignment map XORing `localBit (α[K..K+kCtrl))` into
  `α[0..K)`. -/
def localXorFn {K kCtrl : ℕ} (localBit : BitAssignment kCtrl → Fin K →
    ZMod 2) (α : BitAssignment (K + kCtrl)) : BitAssignment (K + kCtrl) := fun idx ↦
  if hk : idx.val < K then α idx + localBit (fun q ↦ α ⟨K + q.val, by omega⟩) ⟨idx.val, hk⟩
  else α idx

theorem localXorFn_involutive {K kCtrl : ℕ} (localBit : BitAssignment kCtrl → Fin K →
    ZMod 2) : Function.Involutive (localXorFn localBit) := fun α ↦ by
  have hhi (γ : BitAssignment (K + kCtrl)) (q : Fin (K + kCtrl)) (hq : K ≤ q.val) :
      localXorFn localBit γ q = γ q := dite_neg_eq (not_lt.mpr hq)
  have hlo (γ : BitAssignment (K + kCtrl)) (i : Fin (K + kCtrl)) (hi : i.val < K) :
      localXorFn localBit γ i = γ i + localBit (fun q ↦ γ ⟨K + q.val, by omega⟩) ⟨i.val, hi⟩ :=
    dite_pos_eq hi
  refine funext fun k ↦ if hk : k.val < K then ?_ else by
    rw [hhi _ k (not_lt.mp hk), hhi _ k (not_lt.mp hk)]
  rw [hlo _ k hk, hlo _ k hk,
    funext fun q : Fin kCtrl ↦ hhi α ⟨K + q.val, by omega⟩ (Nat.le_add_right K q.val)]
  exact CleanZeroSlot2AxisSum288.zmod2_add_self_cancel _ _

/-- Self-inverse unitary on `2 ^ (K + kCtrl)` induced by `localXorFn localBit`. -/
noncomputable def uLocalXor {K kCtrl : ℕ} (localBit : BitAssignment kCtrl → Fin K → ZMod 2) :
    Unitary (2 ^ (K + kCtrl)) := Operator.permutationUnitary ((basisBitsEquiv (K +
    kCtrl)).trans ((Equiv.ofBijective (localXorFn localBit) (localXorFn_involutive
    localBit).bijective).trans (basisBitsEquiv (K + kCtrl)).symm))

theorem uLocalXor_inv_eq_self {K kCtrl : ℕ} (localBit : BitAssignment kCtrl → Fin K →
    ZMod 2) : (uLocalXor localBit)⁻¹ = uLocalXor localBit :=
  NuclearTwistDisentangleSum288.permUnitaryBits_inv_eq_self
    (localXorFn localBit) (localXorFn_involutive localBit)

theorem zmod2_split_b0_xor (b0 u : ZMod 2) (p0 p1 : Bool) : (if p0 = true then u + u * b0 else 0) +
    (if p1 = true then u * b0 else 0) =
    (if p0 = true then u else 0) + b0 * (if xor p0 p1 = true then u else 0) := by
  rcases bit_cases b0 with rfl | rfl
  · cases p0
    all_goals simp
  · rcases bit_cases u with rfl | rfl
    all_goals cases p0
    all_goals cases p1
    all_goals decide

def vepMKBitFn {mPayload : ℕ} (K H : ℕ) (_hK9 : 9 ≤ K) (hm : 22 ≤ mPayload) (w : Fin 3)
    (xCH : BitAssignment ((fullSysCoreWires mPayload + 61) + H)) (k : Fin K) : ZMod 2 :=
  if hk : K - 9 ≤ k.val then
    xCH (Fin.castAdd H (Fin.natAdd (fullSysCoreWires mPayload) ⟨6, by decide⟩)) *
      xCH (Fin.castAdd H (Fin.castAdd 61 (vepProj9CoreIdx hm w ⟨k.val - (K - 9), by omega⟩)))
  else 0

theorem sub9_add9_le {K : ℕ} (hK9 : 9 ≤ K) : (K - 9) + 9 ≤ K := by omega

theorem mkEntry54_lt216 (i : Fin 54) (s b0 : Bool) : 4 * i.val + (if s then 2 else 0) + (if b0 then
    1 else 0) < 216 := by
  cases s
  all_goals cases b0
  all_goals dsimp
  all_goals omega

open Classical in
/-- Unified `54 × 2 × 2` shifted `nuclearM48` entry covering both `lo208Table` (`i < 52`) and
  `top8Table` (`i ∈ {52, 53}`). -/
noncomputable def mkEntry54 (K : ℕ) (c : Configuration) (w : Fin 3) (i : Fin 54) (s b0 : Bool)
    : ℕ := Nat.shiftRight (nuclearM48 c ⟨4 * i.val + (if s then 2 else 0) + (if b0 then 1 else
    0), mkEntry54_lt216 i s b0⟩ w) (48 - K)

/-- Unified `54 × 2` leaf assignment matching `uLo104` on `i < 52` and `uTop4` on `i ∈ {52, 53}`. -/
def uLeaf54 {H : ℕ} (b1 : ZMod 2) (xHi : Fin 54 → ZMod 2) (xPre : Fin H → ZMod 2) (i : Fin 54)
    (s : Bool) : ZMod 2 := if hi : i.val < H then if s then xPre ⟨i.val, hi⟩ else xHi i else
    if s then xHi i * b1 else xHi i + xHi i * b1

/-- `𝔽₂` parity of `pred` masked by `X`-measurement outcome `f : Fin K → Bool`. -/
def parityMaskK {K : ℕ} (f : Fin K → Bool) (pred : Fin K → Bool) : Bool :=
  decide ((∑ k : Fin K, if (f k && pred k) = true then (1 : ZMod 2) else 0) = 1)

theorem sum_ite_parityMaskK {K : ℕ} (f : Fin K → Bool) (pred : Fin K → Bool) (u : ZMod 2) :
    (∑ k : Fin K,
      if f k = true then (if pred k = true then u else 0) else 0) = if parityMaskK f pred =
      true then u else 0 := by
  have hmul : (∑ k : Fin K, if f k = true then (if pred k = true then u else 0) else 0) =
      (∑ k : Fin K, if (f k && pred k) = true then (1 : ZMod 2) else 0) * u := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    cases f k
    all_goals cases pred k
    all_goals simp
  rw [hmul]
  set s : ZMod 2 := ∑ k : Fin K, if (f k && pred k) = true then (1 : ZMod 2) else 0
  change s * u = if decide (s = 1) = true then u else 0
  rcases bit_cases s with hs | hs
  all_goals simp [hs]

/-- `b_0 = 0` column parity mask on `(i, s) ∈ Fin 54 × Bool`. -/
noncomputable def parB0MK (K : ℕ) (c : Configuration) (w : Fin 3) (f : Fin K →
    Bool) (i : Fin 54) (s : Bool) : Bool :=
  vepLockVal <| parityMaskK f (fun k ↦ (mkEntry54 K c w i s false).testBit k.val)

/-- `b_0 = 0 ⊕ b_0 = 1` difference column parity mask on `(i, s) ∈ Fin 54 × Bool`. -/
noncomputable def parDMK (K : ℕ) (c : Configuration) (w : Fin 3) (f : Fin K →
    Bool) (i : Fin 54) (s : Bool) : Bool :=
  vepLockVal <| parityMaskK f (fun k ↦
    xor ((mkEntry54 K c w i s false).testBit k.val) ((mkEntry54 K c w i s true).testBit k.val))

theorem sum_vepMKBitFn_eq {mPayload : ℕ} (K H : ℕ) (hK9 : 9 ≤ K) (hm : 22 ≤
    mPayload) (w : Fin 3) (f : Fin K → Bool)
    (xCH : BitAssignment ((fullSysCoreWires mPayload + 61) + H)) : (∑ k : Fin K,
      if f k = true then vepMKBitFn K H hK9 hm w xCH k else 0) =
    xCH (Fin.castAdd H (Fin.natAdd (fullSysCoreWires mPayload) ⟨6, by decide⟩)) * (∑ m : Fin 9,
      if f ⟨(K - 9) + m.val, by omega⟩ = true then
    xCH (Fin.castAdd H (Fin.castAdd 61 (vepProj9CoreIdx hm w m))) else 0) := by
  let e : Fin ((K - 9) + 9) ≃ Fin K := finCongr (by omega)
  rw [← Equiv.sum_comp e, Fin.sum_univ_add, Finset.sum_eq_zero fun x _ ↦ by
    dsimp only [vepMKBitFn]
    rw [dite_neg_eq (not_le.mpr x.isLt : ¬(K - 9 ≤ (e (Fin.castAdd 9 x)).val)), ite_self],
    zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [show e (Fin.natAdd (K - 9) m) = ⟨(K - 9) + m.val, by omega⟩ from Fin.ext rfl]
  dsimp only [vepMKBitFn]
  rw [dite_pos_eq (Nat.le_add_right _ _),
    show (⟨((K - 9) + m.val) - (K - 9), by omega⟩ : Fin 9) = m from
      Fin.ext (Nat.add_sub_cancel_left _ _)]
  cases f ⟨(K - 9) + m.val, by omega⟩
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, mul_zero]

section PhaseFixupMK

open _root_.QuantumComputation.Specs.StoppingPowerSolution (CliffProg)

/-- Generic pure-Clifford CNOT fanout from `src : Fin M → Wire n` onto `wAnc`. -/
def fanoutCliffGen {n : ℕ} (M : ℕ) (src : Fin M → Wire n) (wAnc : Wire n)
    (hDisj : ∀ i : Fin M, src i ≠ wAnc) (mask : Fin M → Bool) :
    (rem : ℕ) → (hrem : rem ≤ M) → CliffProg n
  | 0, _ => .nil
  | j + 1, hrem =>
      .seq (fanoutCliffGen M src wAnc hDisj mask j (by omega))
        (if mask ⟨j, hrem⟩ then .cnot (src ⟨j, hrem⟩) wAnc (hDisj ⟨j, hrem⟩) else .nil)

theorem fanoutCliffGen_eval {n : ℕ} (M : ℕ) (src : Fin M → Wire n) (wAnc : Wire n)
    (hDisj : ∀ i : Fin M, src i ≠ wAnc) (mask : Fin M → Bool) :
    ∀ (rem : ℕ) (hrem : rem ≤ M) (β : BitAssignment n),
      (fanoutCliffGen M src wAnc hDisj mask rem hrem).eval β =
        Function.update β wAnc
          (β wAnc + ∑ i : Fin rem, if mask ⟨i.val, by omega⟩ = true then β (src ⟨i.val,
            by omega⟩) else 0)
  | 0, _, β => by simp [fanoutCliffGen, CliffProg.eval]
  | j + 1, hrem, β => by
      have ihβ := fanoutCliffGen_eval M src wAnc hDisj mask j (by omega) β
      simp only [fanoutCliffGen, CliffProg.eval]
      split_ifs with hp
      · simp only [CliffProg.eval, ihβ, Function.update_of_ne (hDisj ⟨j, hrem⟩),
          Function.update_idem,
          Function.update_self, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, hp,
            ↓reduceIte, add_assoc]
      · simp only [CliffProg.eval, ihβ, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
          Bool.eq_false_iff.mpr hp, Bool.false_eq_true, ↓reduceIte, add_zero]

noncomputable def fanoutCliffFull {n : ℕ} (M : ℕ) (src : Fin M → Wire n) (wAnc : Wire n)
    (hDisj : ∀ i : Fin M, src i ≠ wAnc) (mask : Fin M → Bool) : CliffProg n :=
  vepLockVal (fanoutCliffGen M src wAnc hDisj mask M le_rfl)

theorem fanoutCliffFull_eval {n : ℕ} (M : ℕ) (src : Fin M → Wire n) (wAnc : Wire n)
    (hDisj : ∀ i : Fin M, src i ≠ wAnc) (mask : Fin M → Bool) (β : BitAssignment n) :
    (fanoutCliffFull M src wAnc hDisj mask).eval β = Function.update β wAnc (β wAnc + ∑ i : Fin M,
      if mask i = true then β (src i) else 0) := by
  rw [fanoutCliffFull, vepLockVal_eq, fanoutCliffGen_eval]

theorem sub9_add_fin9_lt {K : ℕ} (hK9 : 9 ≤ K) (m : Fin 9) : (K - 9) + m.val < K := by omega

theorem neg_one_pow_zmod2_add (x y : ZMod 2) : ((-1 : ℂ) ^ x.val) * ((-1 : ℂ) ^ y.val) =
    (-1 : ℂ) ^ (x + y).val := by
  rcases bit_cases x with rfl | rfl
  · simp [ZMod.val_zero]
  · rcases bit_cases y with rfl | rfl
    · simp [ZMod.val_zero]
    · exact (by norm_num : (-1 : ℂ) ^ 1 * (-1 : ℂ) ^ 1 = (-1 : ℂ) ^ 0)

theorem neg_one_pow_sum_zmod2 {ι : Type*} (s : Finset ι) (g : ι → ZMod 2) : ((-1 : ℂ) ^ (∑ j ∈ s,
    g j).val) = ∏ j ∈ s, ((-1 : ℂ) ^ (g j).val) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hat ih => rw [Finset.sum_cons, Finset.prod_cons, ← ih, neg_one_pow_zmod2_add]

theorem phaseDiagUnitary_mulVec_basisKet {n : ℕ} (ψ : BitAssignment n →
    ZMod 2) (β : BitAssignment n) :
    (phaseDiagUnitary ψ).1.mulVec (basisKet β) = ((-1 : ℂ) ^ (ψ β).val) • basisKet β := by
  have hev := embedUnitary_phaseDiagUnitary_mulVec_ket (QRegExt.idReg n) ψ β
  rwa [embedUnitary_idReg_eq] at hev

theorem phaseDiagUnitary_eq_diagSignUnitary_f2Parity_gen {k b : ℕ} (f : Fin b →
    Bool) (bitFn : BitAssignment k → Fin b → ZMod 2) :
    phaseDiagUnitary (fun α : BitAssignment k ↦ ∑ j : Fin b, if f j = true then bitFn α j else 0) =
    diagSignUnitary (fun x : Fin (2 ^ k) ↦
      f2Parity b f ((basisBitsEquiv b).symm (bitFn (basisBits k x)))) := by
  refine Subtype.ext (mat_ext_basisKet fun β ↦ ?_)
  have hR := embedUnitary_diagSignUnitary_mulVec_single (QRegExt.idReg k)
    (fun x : Fin (2 ^ k) ↦ f2Parity b f ((basisBitsEquiv b).symm (bitFn (basisBits k x))))
    ((basisBitsEquiv k).symm β)
  have hexId := (basisBitsEquiv k).injective
    (funext (QRegister.basisBits_extractIndex (QRegExt.idReg k) ((basisBitsEquiv k).symm β)))
  rw [embedUnitary_idReg_eq,
    show Pi.single ((basisBitsEquiv k).symm β) (1 : ℂ) = basisKet β from rfl,
    hexId,
      show basisBits k ((basisBitsEquiv k).symm β) = β from funext (basisBits_symm_apply k β)] at hR
  rw [phaseDiagUnitary_mulVec_basisKet, hR]
  refine congrArg (· • basisKet β) ?_
  rw [sign_f2Parity_eq_prod, neg_one_pow_sum_zmod2]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [basisBits_symm_apply b (bitFn β) j]
  rcases bit_cases (bitFn β j) with h | h
  all_goals cases f j
  all_goals simp [h]

abbrev rCHHold {mPayload H n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) : QRegister
    ((fullSysCoreWires mPayload + 61) + H) n := (rCore.concat rHdr61 hCH61).concat rPreHold hCHPH

end PhaseFixupMK

section AxisInnerKH

open HeldMsbInc7ApexWrap288
  (ApexKoffMulKickSpec fApexKoff48Fn apexCore14M48Fn
  shiftMsbInc7Sys shiftMsbInc7Sys_castAdd shiftMsbInc7Sys_natAdd
  apexCatModAddZ_comm_projector_of_not_mem_cat conj_selCM_apexCatModAddZ_eq
  six_le_six_add six_add_le_six_add slice6_disj_sliceTail slice6_concat_sliceTail_sub)
open FusedPreDiagFromTwist288 (w48_ge_7)
open HeldMsbInc7Sandwich288
  (dWithInvMsbInc7 dWithInvMsbInc7_realizesPair_general
  selCM_core14M48PG compose_selCM_core14M48PG)
open KoffPrunedSlot2ZeroMuxTrunc37 (kOffFromEff)

/-- Shifted Mode-1 `k_off` `ℤ`-delta after conjugating `fApexKoff48Fn` by `dWithInvMsbInc7`. -/
noncomputable def fApexKoffShiftedZ (skip kC : ℕ) (iCtrl : Fin kC) (γ : BitAssignment ((kC + 14) +
    48)) : ℤ :=
  let rRaw := bitsVal (fun j : Fin 48 ↦ γ (Fin.natAdd (kC + 14) j))
  let bBar := 1 - (γ (Fin.castAdd 48 (Fin.castAdd 14 iCtrl))).val
  apexKoffDelta skip
    (fun s : Fin 14 ↦ γ (Fin.castAdd 48 (Fin.natAdd kC s)))
    (basisBits 48 ⟨(rRaw + bBar * 2 ^ 41) % 2 ^ 48, Nat.mod_lt _ (Nat.two_pow_pos 48)⟩)

theorem fApexKoff48Fn_shiftMsbInc7Sys (skip kC : ℕ) (iCtrl : Fin kC)
    (γ : BitAssignment ((kC + 14) + 48)) : fApexKoff48Fn skip kC (shiftMsbInc7Sys kC iCtrl γ) =
      fApexKoffShiftedZ skip kC iCtrl γ := by
  dsimp only [fApexKoff48Fn, apexCore14M48Fn, fApexKoffShiftedZ]
  rw [funext fun s : Fin 14 ↦ shiftMsbInc7Sys_castAdd kC iCtrl γ (Fin.natAdd kC s),
    funext fun j : Fin 48 ↦ shiftMsbInc7Sys_natAdd kC iCtrl γ j]

/-- Single-scratch `(6 + mScr)`-wire wrapper for `dApexKoffWithInvMsbInc7`, slicing `rScrAll` into
`rHold6 := rScrAll.slice 0 6` and `rScr := rScrAll.slice 6 mScr`. -/
noncomputable def dApexKoffWithInvMsbInc7Scr {skip mScr tKick : ℕ} (kick : ApexKoffMulKickSpec skip
    mScr tKick) (isInv : Bool) {Var : Type} {n : ℕ} (v : Var)
    (wCtrl : Wire n) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScrAll : QRegister (6 + mScr) n) (hcM : ∀ j, wCtrl ≠ rM48 j)
    (hcScr : ∀ i,
      wCtrl ≠ rScrAll i) (hSM : rSum14.DisjointWires rM48) (hSP : rSum14.DisjointWires rPGTwist)
      (hMP : rM48.DisjointWires rPGTwist)
    (hSScr : rSum14.DisjointWires rScrAll) (hMScr : rM48.DisjointWires rScrAll) (hPScr :
      rPGTwist.DisjointWires rScrAll) : DynamicCircuit Var n :=
  let rHold6 := rScrAll.slice 0 6 (six_le_six_add mScr)
  let rScr := rScrAll.slice 6 mScr (six_add_le_six_add mScr)
  have hcH : ∀ i : Fin 6, wCtrl ≠ rHold6 i := fun i h ↦ by
    obtain ⟨q, hq⟩ := (QRegister.mem_image rScrAll _).mp
      ((QRegister.image_compose_subset rScrAll _) ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩))
    exact hcScr q (h.trans hq.symm)
  dWithInvMsbInc7 v 48 w48_ge_7 wCtrl rM48 rHold6 hcM hcH (hMScr.compose_right _)
    (kick.dKick isInv v rSum14 rM48 rPGTwist rScr hSM hSP hMP
      (hSScr.compose_right _) (hMScr.compose_right _) (hPScr.compose_right _))

theorem count_dApexKoffWithInvMsbInc7Scr_toff {skip mScr tKick : ℕ} (kick : ApexKoffMulKickSpec skip
    mScr tKick) (isInv : Bool) {Var : Type} {n : ℕ} (v : Var)
    (wCtrl : Wire n) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScrAll : QRegister (6 + mScr) n) (hcM : ∀ j, wCtrl ≠ rM48 j)
    (hcScr : ∀ i,
      wCtrl ≠ rScrAll i) (hSM : rSum14.DisjointWires rM48) (hSP : rSum14.DisjointWires rPGTwist)
      (hMP : rM48.DisjointWires rPGTwist)
    (hSScr : rSum14.DisjointWires rScrAll) (hMScr : rM48.DisjointWires rScrAll)
    (hPScr : rPGTwist.DisjointWires rScrAll) : (dApexKoffWithInvMsbInc7Scr kick isInv v wCtrl
    rSum14 rM48 rPGTwist rScrAll hcM hcScr hSM hSP hMP hSScr hMScr hPScr).count .TOFF = 0 := by
  rw [dApexKoffWithInvMsbInc7Scr, HeldMsbInc7Sandwich288.count_dWithInvMsbInc7_toff]
  exact kick.hToff isInv v rSum14 rM48 rPGTwist _ hSM hSP hMP _ _ _

theorem count_dApexKoffWithInvMsbInc7Scr_t_le {skip mScr tKick : ℕ} (kick : ApexKoffMulKickSpec skip
    mScr tKick) (isInv : Bool) {Var : Type} {n : ℕ} (v : Var)
    (wCtrl : Wire n) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScrAll : QRegister (6 + mScr) n) (hcM : ∀ j, wCtrl ≠ rM48 j)
    (hcScr : ∀ i,
      wCtrl ≠ rScrAll i) (hSM : rSum14.DisjointWires rM48) (hSP : rSum14.DisjointWires rPGTwist)
      (hMP : rM48.DisjointWires rPGTwist)
    (hSScr : rSum14.DisjointWires rScrAll) (hMScr : rM48.DisjointWires rScrAll)
    (hPScr : rPGTwist.DisjointWires rScrAll) : (dApexKoffWithInvMsbInc7Scr kick isInv v wCtrl
    rSum14 rM48 rPGTwist rScrAll hcM hcScr hSM hSP hMP hSScr hMScr hPScr).count .T ≤ 24 + tKick :=
      by
  rw [dApexKoffWithInvMsbInc7Scr, HeldMsbInc7Sandwich288.count_dWithInvMsbInc7_t]
  exact Nat.add_le_add_left (kick.hT isInv v rSum14 rM48 rPGTwist _ hSM hSP hMP _ _ _) 24

theorem dApexKoffWithInvMsbInc7Scr_realizesPair_core14M48PG {skip mScr tKick kC : ℕ}
    (kick : ApexKoffMulKickSpec skip mScr tKick) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rCore : QRegister kC n) (iCtrl : Fin kC) (rSum14 : QRegister
      14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScrAll : QRegister (6 +
      mScr) n) (hCSum : rCore.DisjointWires rSum14) (hCP : rCore.DisjointWires rPGTwist) (hSP :
      rSum14.DisjointWires rPGTwist)
    (hCM48 : rCore.DisjointWires rM48) (hSM : rSum14.DisjointWires rM48) (hMP : rM48.DisjointWires
      rPGTwist) (hCScr : rCore.DisjointWires rScrAll)
    (hSScr : rSum14.DisjointWires rScrAll) (hMScr : rM48.DisjointWires rScrAll)
    (hPScr : rPGTwist.DisjointWires rScrAll) : RealizesCleanPair (((rCore.concat rSum14
    hCSum).concat rM48 (QRegExt.disjointWires_concat_left hCM48 hSM)).concat rPGTwist
    (QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCP hSP) hMP))
    rScrAll (apexCatModAddZ ((kC + 14) + 48) (fApexKoffShiftedZ skip kC iCtrl))
    (dApexKoffWithInvMsbInc7Scr kick false v (rCore iCtrl) rSum14 rM48 rPGTwist rScrAll (fun j
    ↦ hCM48.ne iCtrl j) (fun i ↦ hCScr.ne iCtrl i) hSM hSP hMP hSScr hMScr hPScr)
    (dApexKoffWithInvMsbInc7Scr kick true v (rCore iCtrl) rSum14 rM48 rPGTwist rScrAll (fun j
    ↦ hCM48.ne iCtrl j) (fun i ↦ hCScr.ne iCtrl i) hSM hSP hMP hSScr hMScr hPScr) := by
  let rHold6 := rScrAll.slice 0 6 (six_le_six_add mScr)
  let rScr := rScrAll.slice 6 mScr (six_add_le_six_add mScr)
  let hCSM48 : (rCore.concat rSum14 hCSum).DisjointWires rM48 :=
    QRegExt.disjointWires_concat_left hCM48 hSM
  let rSys := (rCore.concat rSum14 hCSum).concat rM48 hCSM48
  let hExtP48 : rSys.DisjointWires rPGTwist := QRegExt.disjointWires_concat_left
    (QRegExt.disjointWires_concat_left hCP hSP :
      (rCore.concat rSum14 hCSum).DisjointWires rPGTwist) hMP
  let rAct := rSys.concat rPGTwist hExtP48
  have hActScr : rAct.DisjointWires rScrAll := QRegExt.disjointWires_concat_left
    (QRegExt.disjointWires_concat_left
      (QRegExt.disjointWires_concat_left hCScr hSScr :
        (rCore.concat rSum14 hCSum).DisjointWires rScrAll) hMScr :
      rSys.DisjointWires rScrAll) hPScr
  have hcH : ∀ i : Fin 6, rCore iCtrl ≠ rHold6 i := fun i h ↦ by
    obtain ⟨q, hq⟩ := (QRegister.mem_image rScrAll _).mp
      ((QRegister.image_compose_subset rScrAll _) ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩))
    exact hCScr.ne iCtrl q (h.trans hq.symm)
  have hcNotPG : rCore iCtrl ∉ rPGTwist.image := by
    rw [show rCore iCtrl = rSys (Fin.castAdd 48 (Fin.castAdd 14 iCtrl)) by
      simp [rSys, QRegister.concat_apply_left]]
    exact hExtP48.apply_not_mem_right _
  have hp := (dWithInvMsbInc7_realizesPair_general v w48_ge_7 rCore iCtrl rM48 rHold6 rAct rScr
    (selCM_core14M48PG kC) hCM48
    (compose_selCM_core14M48PG rCore rSum14 rM48 rPGTwist hCSum hCSM48 hExtP48 hCM48)
    hcH (hMScr.compose_right _) (hActScr.compose_right _) (hActScr.compose_right _)
    (slice6_disj_sliceTail rScrAll)
    (apexCatModAddZ_comm_projector_of_not_mem_cat rSys rPGTwist hExtP48
      (fApexKoff48Fn skip kC) (rCore iCtrl) hcNotPG)
    (fun j ↦ apexCatModAddZ_comm_projector_of_not_mem_cat rSys rPGTwist hExtP48
      (fApexKoff48Fn skip kC) (rM48 j) (hMP.apply_not_mem_right j))
    (kick.realizesPair_core14M48PG v rCore rSum14 rM48 rPGTwist rScr
      hCSum hCSM48 hExtP48 hSM hSP hMP
      (hSScr.compose_right _) (hMScr.compose_right _) (hPScr.compose_right _))).congr_unitary
    ((conj_selCM_apexCatModAddZ_eq kC iCtrl (fApexKoff48Fn skip kC)).trans
      (congrArg (apexCatModAddZ ((kC + 14) + 48))
        (funext (fApexKoff48Fn_shiftMsbInc7Sys skip kC iCtrl))))
  exact { fwd := realizesClean_of_workspace_subset (slice6_concat_sliceTail_sub rScrAll) hp.fwd
          inv := realizesClean_of_workspace_subset (slice6_concat_sliceTail_sub rScrAll) hp.inv }

theorem apexKoffDelta_eq_kOffFromEff (skip : ℕ) (hsk1 : 1 ≤ skip) (hsk48 : skip ≤ 48)
    (B : Fin 14 → ZMod 2) (M : Fin 48 → ZMod 2) : apexKoffDelta skip B M = (bitsVal B : ℤ) *
    (bitsVal (mEffBits skip M) : ℤ) - kOffFromEff (bitsVal (mEffBits skip M)) := by
  have h0 : (mEffBits skip M 0).val = 0 := congrArg ZMod.val (ite_eq_left hsk1)
  have hDiv : bitsVal (mEffBits skip M) / 2 = 2 ^ (skip - 1) * bitsVal (fun j : Fin (48 - skip) ↦
    M ⟨j.val + skip, by omega⟩) := by
    rw [Slot2ZeroMuxTrunc28To35.bitsVal_mEffBits_eq hsk48 M,
      show 2 ^ skip = 2 * 2 ^ (skip - 1) by rw [← pow_succ', show skip - 1 + 1 = skip by omega],
      mul_assoc, Nat.mul_div_right _ (by decide)]
  dsimp only [apexKoffDelta, kOffFromEff]
  change (bitsVal B : ℤ) * (bitsVal (mEffBits skip M) : ℤ) - ((2 ^ 13 : ℤ) * (bitsVal
    (mEffBits skip M) : ℤ) - ((bitsVal (fun j : Fin 47 ↦ mEffBits skip M j.succ) : ℤ) +
    ((mEffBits skip M 0).val : ℤ))) = (bitsVal B : ℤ) * (bitsVal (mEffBits skip M) : ℤ) - ((2
    ^ 13 : ℤ) * (bitsVal (mEffBits skip M) : ℤ) - ((bitsVal (mEffBits skip M) / 2 : ℕ) : ℤ))
  rw [h0, Slot2ZeroMuxTrunc28To35.bitsVal_47_mEffBits_eq hsk1 hsk48 M, hDiv, Nat.cast_zero,
    add_zero]

private theorem bitsVal_mEffBits_basisBits_eq {skip : ℕ} (hsk48 : skip ≤ 48) (N : ℕ) (hN : N <
    2 ^ 48) :
    bitsVal (mEffBits skip (basisBits 48 ⟨N, hN⟩)) = 2 ^ skip * (N / 2 ^ skip) := by
  let M : BitAssignment 48 := basisBits 48 ⟨N, hN⟩
  have hM : regVal (QRegExt.idReg 48) M = N := (bitsVal_eq_symm_val M).trans
    (congrArg Fin.val ((basisBitsEquiv 48).symm_apply_apply ⟨N, hN⟩))
  let L := regVal ((QRegExt.idReg 48).slice 0 skip (by omega)) M
  let R := regVal ((QRegExt.idReg 48).slice skip (48 - skip) (by omega)) M
  have hNR : N = L + R * 2 ^ skip := by
    rw [← hM, ParametricMulKickAndSlopePG.regVal_split_at_slice skip (48 - skip) (by
      omega) (QRegExt.idReg 48) M, mul_comm]
  have hDiv : N / 2 ^ skip = R := by
    rw [hNR, Nat.add_mul_div_right _ _ (Nat.two_pow_pos skip),
      Nat.div_eq_of_lt (_root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_lt_two_pow _
      M), zero_add]
  have hHi : R = bitsVal (fun j : Fin (48 - skip) ↦ M ⟨j.val + skip, by omega⟩) := by
    dsimp only [R, regVal, bitsVal]
    refine Finset.sum_congr rfl fun j _ ↦ congrArg (fun w ↦ (M w).val * 2 ^ j.val) (Fin.ext ?_)
    simp only [QRegister.slice_apply, QRegExt.idReg, Function.Embedding.refl_apply]
    omega
  rw [Slot2ZeroMuxTrunc28To35.bitsVal_mEffBits_eq hsk48 M, hDiv, hHi]

theorem mEffBits_shifted_pad_eq (skip : ℕ) (hsk41 : skip ≤ 41) (lo hi bBar : ℕ)
    (hlo : lo < 2 ^ skip) : bitsVal (mEffBits skip (basisBits 48 ⟨(lo + 2 ^ skip * hi + bBar *
    2 ^ 41) % 2 ^ 48,
      Nat.mod_lt _ (Nat.two_pow_pos 48)⟩)) = (2 ^ skip * hi + bBar * 2 ^ 41) % 2 ^ 48 := by
  let S := hi + bBar * 2 ^ (41 - skip)
  have h41 : 2 ^ 41 = 2 ^ skip * 2 ^ (41 - skip) := by rw [← pow_add, Nat.add_sub_cancel' hsk41]
  have h48 : 2 ^ skip * 2 ^ (48 - skip) = 2 ^ 48 := by rw [← pow_add, Nat.add_sub_cancel' (by
    omega)]
  let Q := S % 2 ^ (48 - skip)
  let D := S / 2 ^ (48 - skip)
  have hQ_lt : Q < 2 ^ (48 - skip) := Nat.mod_lt S (Nat.two_pow_pos _)
  have hMulS : 2 ^ skip * hi + bBar * 2 ^ 41 = 2 ^ 48 * D + 2 ^ skip * Q := by
    rw [h41, show 2 ^ skip * hi + bBar * (2 ^ skip * 2 ^ (41 - skip)) = 2 ^ skip * S by ring,
      (Nat.div_add_mod S (2 ^ (48 - skip))).symm, mul_add, ← mul_assoc, h48]
  have h2Q_lt : 2 ^ skip * Q < 2 ^ 48 := h48 ▸ Nat.mul_lt_mul_of_pos_left hQ_lt (Nat.two_pow_pos _)
  have hLo2Q_lt : lo + 2 ^ skip * Q < 2 ^ 48 := by
    have hm : 2 ^ skip * Q + 2 ^ skip ≤ 2 ^ 48 := by
      have hle : Q + 1 ≤ 2 ^ (48 - skip) := hQ_lt
      simpa only [mul_add, mul_one, h48] using Nat.mul_le_mul_left (2 ^ skip) hle
    omega
  rw [bitsVal_mEffBits_basisBits_eq (by omega : skip ≤ 48),
    show (lo + 2 ^ skip * hi + bBar * 2 ^ 41) % 2 ^ 48 = lo + 2 ^ skip * Q by
      rw [add_assoc, hMulS,
        show lo + (2 ^ 48 * D + 2 ^ skip * Q) = (lo + 2 ^ skip * Q) + 2 ^ 48 * D by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hLo2Q_lt],
    show (2 ^ skip * hi + bBar * 2 ^ 41) % 2 ^ 48 = 2 ^ skip * Q by
      rw [hMulS, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2Q_lt],
    mul_comm (2 ^ skip) Q, Nat.add_mul_div_right _ _ (Nat.two_pow_pos skip), Nat.div_eq_of_lt hlo,
      zero_add]
  ring

theorem hSub14_le_core (mPayload : ℕ) : 14 + (fullSysCoreWires mPayload - 14) ≤
    fullSysCoreWires mPayload := by
  have := core_ge_3954 mPayload
  omega

theorem hTail_le_core (mPayload K : ℕ) : (62 - K) + (fullSysCoreWires mPayload - (62 - K)) ≤
    fullSysCoreWires mPayload := by
  have := core_ge_3954 mPayload
  omega

theorem hK9_of_K28 (K : ℕ) (hK28 : 28 ≤ K) : 9 ≤ K := by omega
theorem hK48_of_K36 (K : ℕ) (hK36 : K ≤ 36) : K ≤ 48 := by omega

private theorem disj_rMPad48 {mPayload K a n : ℕ} (hK48 : K ≤
    48) {rCore : QRegister (fullSysCoreWires mPayload) n} {rA : QRegister a n} {rMK : QRegister K n}
    (hCMK : rCore.DisjointWires rMK) (hCA : rCore.DisjointWires rA) (hAMK : rA.DisjointWires rMK) :
      rA.DisjointWires (rMPad48 hK48 rCore rMK hCMK) := by
  rw [QRegister.disjoint_iff]
  intro s j hsj
  rw [rMPad48_apply] at hsj
  split_ifs at hsj
  · exact hCA.ne _ _ hsj.symm
  · exact hAMK.ne _ _ hsj

theorem rSum14_disj_rMPad48 {mPayload K n : ℕ} (hK48 : K ≤
    48) (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (rMK : QRegister K n) (hCMK : rCore.DisjointWires rMK) (hCSum : rCore.DisjointWires rSum14)
      (hSMK : rSum14.DisjointWires rMK) :
    rSum14.DisjointWires (rMPad48 hK48 rCore rMK hCMK) :=
  disj_rMPad48 hK48 hCMK hCSum hSMK

theorem coreCosetB1Block_val_ge_3954 {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) : 3954 ≤
    (coreCosetB1Block (hm6_of_hm22 hm) w).val := by
  change 3954 ≤ 3954 + w.val
  omega

theorem wCtrl_ne_rMPad48 {mPayload K n : ℕ} (hm : 22 ≤ mPayload) (hK48 : K ≤
    48) (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rMK : QRegister K n) (hCMK : rCore.DisjointWires rMK) (j : Fin 48) : rCore (coreCosetB1Block
      (hm6_of_hm22 hm) w) ≠ rMPad48 hK48 rCore rMK hCMK j := by
  intro h
  rw [rMPad48_apply] at h
  split_ifs at h
  · have hv := congrArg Fin.val (rCore.wires.injective h)
    have hge := coreCosetB1Block_val_ge_3954 hm w
    have hj48 := j.isLt
    dsimp at hv
    omega
  · exact hCMK.ne _ _ h

/-- Pad `γNo14 : BitAssignment ((((kC - 14) + 61) + H) + 14)` with `0` on `rCore[0..14)`. -/
def padZero14CH {mPayload H : ℕ} (γNo14 : BitAssignment ((((fullSysCoreWires mPayload - 14) +
    61) + H) + 14)) : BitAssignment ((fullSysCoreWires mPayload + 61) + H) :=
  fun q ↦
    if h14 : q.val < 14 then 0
    else γNo14 ⟨q.val - 14, by
      have := q.isLt
      have := core_ge_3954 mPayload
      omega⟩

theorem rNucIdx_val_ge_3960 {mPayload : ℕ} (hm : 22 ≤ mPayload) (d : Fin 8) : 3960 ≤
    (rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) d).val := by
  change 3960 ≤ 3960 + d.val
  omega

theorem vepProj9CoreIdx_val_ge_3924 {mPayload : ℕ} (hm : 22 ≤
    mPayload) (w : Fin 3) (j : Fin 9) : 3924 ≤ (vepProj9CoreIdx hm w j).val := by
  unfold vepProj9CoreIdx
  split_ifs
  · change 3924 ≤ 3957 + w.val
    omega
  · change 3924 ≤ (3924 + 8 * w.val) + (j.val - 1)
    omega

theorem slice_concat_disj_preHold {k s l b H n : ℕ} {rCore : QRegister k n}
    {rHdr : QRegister b n} {rPH : QRegister H n} (hle : s + l ≤ k)
    (hCH : rCore.DisjointWires rHdr) (hCHPH : (rCore.concat rHdr hCH).DisjointWires rPH) :
    ((rCore.slice s l hle).concat rHdr (hCH.compose_left _)).DisjointWires rPH :=
  QRegExt.disjointWires_concat_left
    ((QRegExt.disjointWires_mono_left hCHPH) ((QRegister.image_compose_subset rCore _).trans (by
      rw [QRegExt.image_concat]
      exact Finset.subset_union_left)))
    ((QRegExt.disjointWires_mono_left hCHPH) (by
      rw [QRegExt.image_concat]
      exact Finset.subset_union_right))

abbrev rSysNo14 {mPayload H n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rSum14 : QRegister 14 n) (hCH61 :
      rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) (hCHSum : (rCHHold rCore rHdr61
      rPreHold hCH61 hCHPH).DisjointWires rSum14) : QRegister
    ((((fullSysCoreWires mPayload - 14) + 61) + H) + 14) n :=
  let rPre := (rCore.slice 14 (fullSysCoreWires mPayload - 14) (hSub14_le_core mPayload)).concat
    rHdr61 (hCH61.compose_left _) |>.concat rPreHold
    (slice_concat_disj_preHold (hSub14_le_core mPayload) hCH61 hCHPH)
  rPre.concat rSum14 ((QRegExt.disjointWires_mono_left hCHSum) (by
    simp only [rPre, rCHHold, QRegExt.image_concat]
    exact Finset.union_subset_union_left
      (Finset.union_subset_union_left (QRegister.image_compose_subset rCore _))))

abbrev rSysTail {mPayload K H n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) : QRegister (((fullSysCoreWires
      mPayload - (62 - K)) + 61) + H) n :=
  ((rCore.slice (62 - K) (fullSysCoreWires mPayload - (62 - K)) (hTail_le_core mPayload K)).concat
    rHdr61 (hCH61.compose_left _)).concat rPreHold
    (slice_concat_disj_preHold (hTail_le_core mPayload K) hCH61 hCHPH)

theorem rSysTail_image_sub_rCHHold {mPayload K H n : ℕ} (rCore : QRegister (fullSysCoreWires
    mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) : (rSysTail (K :=
      K) rCore rHdr61 rPreHold hCH61 hCHPH).image ⊆
      (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).image := by
  dsimp only [rSysTail, rCHHold]
  rw [QRegExt.image_concat, QRegExt.image_concat, QRegExt.image_concat, QRegExt.image_concat]
  exact Finset.union_subset_union_left
    (Finset.union_subset_union_left (QRegister.image_compose_subset rCore _))

/-- Index of `coreCosetB1Block w` inside `rSysTail`. -/
def iCtrlTail {mPayload : ℕ} (K H : ℕ) (hm : 22 ≤
    mPayload) (w : Fin 3) : Fin (((fullSysCoreWires mPayload - (62 - K)) + 61) + H) :=
  Fin.castAdd H (Fin.castAdd 61
    ⟨(coreCosetB1Block (hm6_of_hm22 hm) w).val - (62 - K), by
      have hlt := (coreCosetB1Block (hm6_of_hm22 hm) w).isLt
      have hge := coreCosetB1Block_val_ge_3954 hm w
      omega⟩)

theorem rSysTail_iCtrlTail {mPayload K H n : ℕ} (hm : 22 ≤
    mPayload) (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) : rSysTail (K :=
      K) rCore rHdr61 rPreHold hCH61 hCHPH (iCtrlTail K H hm w) =
      rCore (coreCosetB1Block (hm6_of_hm22 hm) w) := by
  dsimp only [rSysTail, iCtrlTail]
  rw [QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.slice_apply]
  have hge := coreCosetB1Block_val_ge_3954 hm w
  exact congrArg rCore (Fin.ext (by
    dsimp
    omega))

theorem rSysTail_disj_rMPad48 {mPayload K H n : ℕ} (hK48 : K ≤
    48) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rMK : QRegister K n) (hCH61 :
      rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) (hCMK : rCore.DisjointWires rMK)
    (hH61MK : rHdr61.DisjointWires rMK) (hPHMK : rPreHold.DisjointWires rMK) : (rSysTail (K :=
      K) rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires
      (rMPad48 hK48 rCore rMK hCMK) := by
  refine QRegExt.disjointWires_concat_left
    (QRegExt.disjointWires_concat_left ?_ (disj_rMPad48 hK48 hCMK hCH61 hH61MK))
    (disj_rMPad48 hK48 hCMK
      ((QRegExt.disjointWires_mono_left hCHPH) (by
        rw [QRegExt.image_concat]
        exact Finset.subset_union_left))
      hPHMK)
  rw [QRegister.disjoint_iff]
  intro i j hij
  rw [QRegister.slice_apply, rMPad48_apply] at hij
  split_ifs at hij
  · have hv := congrArg Fin.val (rCore.wires.injective hij)
    have hj48 := j.isLt
    dsimp at hv
    omega
  · exact hCMK.ne _ _ hij

theorem dApexKoffWithInvMsbInc7Scr_congr_wCtrl {skip mScr tKick : ℕ} (kick : ApexKoffMulKickSpec
    skip mScr tKick) (isInv : Bool) {Var : Type} {n : ℕ} (v : Var)
    {w₁ w₂ : Wire n} (hw : w₁ = w₂) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScrAll : QRegister (6 + mScr) n) (hcM₁ : ∀ j, w₁ ≠ rM48 j)
    (hcScr₁ : ∀ i,
      w₁ ≠ rScrAll i) (hSM₁ : rSum14.DisjointWires rM48) (hSP₁ : rSum14.DisjointWires rPGTwist)
      (hMP₁ : rM48.DisjointWires rPGTwist)
    (hSScr₁ : rSum14.DisjointWires rScrAll) (hMScr₁ : rM48.DisjointWires rScrAll) (hPScr₁ :
      rPGTwist.DisjointWires rScrAll) (hcM₂ : ∀ j, w₂ ≠ rM48 j)
    (hcScr₂ : ∀ i,
      w₂ ≠ rScrAll i) (hSM₂ : rSum14.DisjointWires rM48) (hSP₂ : rSum14.DisjointWires rPGTwist)
      (hMP₂ : rM48.DisjointWires rPGTwist)
    (hSScr₂ : rSum14.DisjointWires rScrAll) (hMScr₂ : rM48.DisjointWires rScrAll)
    (hPScr₂ : rPGTwist.DisjointWires rScrAll) : dApexKoffWithInvMsbInc7Scr kick isInv v w₁
    rSum14 rM48 rPGTwist rScrAll hcM₁ hcScr₁ hSM₁ hSP₁ hMP₁ hSScr₁ hMScr₁ hPScr₁ =
    dApexKoffWithInvMsbInc7Scr kick isInv v w₂ rSum14 rM48 rPGTwist rScrAll hcM₂ hcScr₂ hSM₂ hSP₂
      hMP₂ hSScr₂ hMScr₂ hPScr₂ := by
  subst hw
  rfl

theorem bitsVal_lt_two_pow_gen {m : ℕ} (B : Fin m → ZMod 2) : bitsVal B < 2 ^ m :=
  _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_lt_two_pow (QRegExt.idReg m) B

theorem bitsVal_split_gen {A B K : ℕ} (hAB : A + B = K) (M : Fin K → ZMod 2) : bitsVal M =
    bitsVal (fun i : Fin A ↦ M ⟨i.val, by omega⟩) +
    2 ^ A * bitsVal (fun k : Fin B ↦ M ⟨A + k.val, by omega⟩) := by
  have h : bitsVal M = regVal ((QRegExt.idReg K).slice 0 A (by
    omega)) M + 2 ^ A * regVal ((QRegExt.idReg K).slice A B (by omega)) M :=
    ParametricMulKickAndSlopePG.regVal_split_at_slice A B (by omega) (QRegExt.idReg K) M
  rw [h]
  refine congrArg₂ HAdd.hAdd
    (congrArg bitsVal (funext fun i ↦ congrArg M (Fin.ext (by
      simp only [QRegister.slice_apply, QRegExt.idReg, Function.Embedding.refl_apply, zero_add]))))
    (congrArg (2 ^ A * ·)
      (congrArg bitsVal (funext fun k ↦ congrArg M (Fin.ext (by
        simp only [QRegister.slice_apply, QRegExt.idReg, Function.Embedding.refl_apply])))))

theorem bitsVal_split_48 {K : ℕ} (hK48 : K ≤ 48) (M : Fin 48 → ZMod 2) : bitsVal M =
    bitsVal (fun i : Fin (48 - K) ↦ M ⟨i.val, by omega⟩) +
    2 ^ (48 - K) * bitsVal (fun k : Fin K ↦ M ⟨(48 - K) + k.val, by omega⟩) :=
  bitsVal_split_gen (Nat.sub_add_cancel hK48) M

end AxisInnerKH

section KickKoffKH

open KoffPrunedSlot2ZeroMuxTrunc37 (vepEffSlope48)

theorem apexCatModAdd34Z_idReg_eq {kSys : ℕ} :
    let rSys0 : QRegister kSys (kSys + 34) := QRegister.block 0 kSys (by omega)
    let rPG0 : QRegister 34 (kSys + 34) := QRegister.block kSys 34 le_rfl
    let hdisj : rSys0.DisjointWires rPG0 :=
      QRegister.block_disjoint_of_le 0 kSys kSys 34 (by omega) le_rfl (by omega)
    rSys0.concat rPG0 hdisj = QRegExt.idReg (kSys + 34) := by
  intro rSys0 rPG0 hdisj
  exact block0_concat_block_eq_idReg kSys 34

theorem commutesWithReg_of_smul_ket {k n : ℕ} (r : QRegister k n) (M : Operator (2 ^ n))
    (φ : BitAssignment n → ℂ) (σ σ_inv : BitAssignment n →
      BitAssignment n) (hEv : ∀ ξ : BitAssignment n, M.mulVec (basisKet ξ) = φ ξ • basisKet (σ ξ))
    (hLeftInv : ∀ ξ, σ_inv (σ ξ) = ξ) (hRightInv : ∀ ξ, σ (σ_inv ξ) = ξ) (hFixR : ∀ ξ (i : Fin k),
      σ ξ (r i) = ξ (r i)) (hPhiOut : ∀ ξ₁ ξ₂, (∀ w, w ∉ Set.range
    r.wires → ξ₁ w = ξ₂ w) → φ ξ₁ = φ ξ₂) (hSigmaOut : ∀ ξ₁ ξ₂, (∀ w, w ∉ Set.range r.wires →
    ξ₁ w = ξ₂ w) → ∀ w, w ∉ Set.range r.wires → σ ξ₁ w = σ ξ₂ w) (hSigmaInvOut : ∀ ξ₁ ξ₂, (∀
    w, w ∉ Set.range r.wires → ξ₁ w = ξ₂ w) → ∀ w,
      w ∉ Set.range r.wires → σ_inv ξ₁ w = σ_inv ξ₂ w) : CommutesWithReg r M := by
  intro B
  ext x y
  let eσ : Equiv.Perm (BitAssignment n) :=
    { toFun := σ, invFun := σ_inv, left_inv := hLeftInv, right_inv := hRightInv }
  let τ : Equiv.Perm (Fin (2 ^ n)) := (basisBitsEquiv n).trans (eσ.trans (basisBitsEquiv n).symm)
  have hτ_bits (z) : basisBits n (τ z) = σ (basisBits n z) :=
    funext (basisBits_symm_apply n (σ (basisBits n z)))
  have hτs_bits (z) : basisBits n (τ.symm z) = σ_inv (basisBits n z) :=
    funext (basisBits_symm_apply n (σ_inv (basisBits n z)))
  have hM_entry (a b : Fin (2 ^ n)) : M a b = if a = τ b then φ (basisBits n b) else 0 := by
    have h1 := congrFun (hEv (basisBits n b)) a
    rw [show basisKet (basisBits n b) = (Pi.single b (1 : ℂ) : Fin (2 ^ n) → ℂ) from
          congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ))
            ((basisBitsEquiv n).symm_apply_apply b),
        show basisKet (σ (basisBits n b)) = (Pi.single (τ b) (1 : ℂ) : Fin (2 ^ n) → ℂ) from rfl,
        show (M.mulVec (Pi.single b (1 : ℂ) : Fin (2 ^ n) → ℂ)) a = M a b by
          simp [Matrix.mulVec, dotProduct, Pi.single_apply]] at h1
    simpa [Pi.single_apply, eq_comm] using h1
  have hLHS : (M * r.embedMatrix B) x y = φ (basisBits n (τ.symm x)) *
    (r.embedMatrix B) (τ.symm x) y := by
    rw [Matrix.mul_apply]
    simp_rw [hM_entry x, show ∀ z, (x = τ z) ↔ (z = τ.symm x) from fun z ↦
      ⟨fun h ↦ by rw [h, τ.symm_apply_apply], fun h ↦ by rw [h, τ.apply_symm_apply]⟩]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hRHS : (r.embedMatrix B * M) x y = (r.embedMatrix B) x (τ y) * φ (basisBits n y) := by
    rw [Matrix.mul_apply]
    simp_rw [hM_entry _ y]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hExt_τ (z) : r.extractIndex (τ z) = r.extractIndex z :=
    (basisBitsEquiv k).injective (funext fun i ↦ by
      change basisBits k (r.extractIndex (τ z)) i = basisBits k (r.extractIndex z) i
      rw [r.basisBits_extractIndex, r.basisBits_extractIndex, hτ_bits, hFixR])
  have hExt_τs (z) : r.extractIndex (τ.symm z) = r.extractIndex z := by
    simpa only [τ.apply_symm_apply] using (hExt_τ (τ.symm z)).symm
  have hEnvIff : ((r.basisSplitEquiv (τ.symm x)).2 = (r.basisSplitEquiv y).2) ↔
    ((r.basisSplitEquiv x).2 = (r.basisSplitEquiv (τ y)).2) := by
    rw [r.basisSplit_environment_eq_iff, r.basisSplit_environment_eq_iff]
    refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩
    · have h1 := hSigmaOut _ _ h w hw
      rwa [hτs_bits, hRightInv, ← hτ_bits] at h1
    · have h1 := hSigmaInvOut _ _ h w hw
      rwa [← hτs_bits, hτ_bits, hLeftInv] at h1
  rw [hLHS, hRHS, QRegister.embedMatrix_apply, QRegister.embedMatrix_apply, hExt_τs x, hExt_τ y]
  by_cases hE : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv (τ y)).2
  · have hE1 := hEnvIff.mpr hE
    simp only [hE1, hE, ↓reduceIte, hPhiOut _ _ ((r.basisSplit_environment_eq_iff _ _).mp hE1),
      mul_comm]
  · simp only [show ¬((r.basisSplitEquiv (τ.symm x)).2 = (r.basisSplitEquiv y).2) from
      fun h ↦ hE (hEnvIff.mp h), hE, ↓reduceIte, mul_zero, zero_mul]

theorem CommutesWithReg.mul {k n : ℕ} {r : QRegister k n} {M₁ M₂ : Operator (2 ^ n)} (h₁ :
    CommutesWithReg r M₁) (h₂ : CommutesWithReg r M₂) :
    CommutesWithReg r (M₁ * M₂) := fun B ↦ by
  rw [Matrix.mul_assoc, h₂ B, ← Matrix.mul_assoc, h₁ B, Matrix.mul_assoc]

theorem CommutesWithReg.embedUnitary_of_compose {k m n : ℕ} {sub : QRegister m n}
    {rLoc : QRegister k m} {r : QRegister k n} (hComp : sub.compose rLoc = r)
    {U : Unitary (2 ^ m)} (hLoc : CommutesWithReg rLoc U.1) : CommutesWithReg r (sub.embedUnitary
      U).1 := fun B ↦ by
  rw [← hComp, show (sub.embedUnitary U).1 = sub.embedMatrix U.1 from rfl,
    QRegister.embedMatrix_compose, ← QRegister.embedMatrix_mul, hLoc B, QRegister.embedMatrix_mul]

theorem shiftCatKet_congr_of_outside {B k n : ℕ} (r : QRegister k n) (rCat : QRegister B n)
    (hDisj : r.DisjointWires rCat) (ξ₁ ξ₂ : BitAssignment n) (s : ℕ) (hOut : ∀ w,
      w ∉ Set.range r.wires → ξ₁ w = ξ₂ w) : ∀ w, w ∉ Set.range r.wires →
    shiftCatKet rCat ξ₁ s w = shiftCatKet rCat ξ₂ s w := by
  have hValEq : regVal rCat ξ₁ = regVal rCat ξ₂ :=
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rCat fun p ↦
      hOut (rCat p) (fun ⟨i, hi⟩ ↦ hDisj.ne i p hi)
  let η : BitAssignment n := fun u ↦ if u ∈ rCat.image then shiftCatKet rCat ξ₂ s u else ξ₁ u
  have hηEq : η = shiftCatKet rCat ξ₁ s :=
    FusedVepCore288.eq_shiftCatKet_of_outside_and_regVal rCat η ξ₁ s (fun _ hu ↦
      ite_eq_right hu) (by
      rw [_root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rCat (fun p ↦
        ite_eq_left ((QRegister.mem_image rCat _).mpr ⟨p, rfl⟩)),
        regVal_shiftCatKet, hValEq])
  intro w hw
  rw [← hηEq]
  dsimp only [η]
  split_ifs with hm
  · rfl
  · exact (hOut w hw).trans (shiftCatKet_outside rCat ξ₂ s hm).symm

theorem add_sub_mod_cancel_pow {B v s : ℕ} (hv : v < 2 ^ B) : (v + (s + (2 ^ B -
    s % 2 ^ B))) % 2 ^ B = v := by
  have hdm := Nat.div_add_mod s (2 ^ B)
  have hlt := Nat.mod_lt s (Nat.two_pow_pos B)
  have hexp : 2 ^ B * (s / 2 ^ B + 1) = 2 ^ B * (s / 2 ^ B) + 2 ^ B := by ring
  rw [show v + (s + (2 ^ B - s % 2 ^ B)) = v + 2 ^ B * (s / 2 ^ B + 1) by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

def rCtrl3InCore (mPayload : ℕ) : QRegister 3 (fullSysCoreWires mPayload) :=
  QRegister.block 3951 3 (core_ge_3954 mPayload)

/-- Local `3`-wire `[3951 .. 3954)` register inside `fullSysCoreWires 80 + mCat`,
`rfl`-identical to `Leaf4Ext48TopStitch.rCtrl3InCoreCat`. -/
def rCtrl3InCoreCat (mCat : ℕ) : QRegister 3 (fullSysCoreWires 80 + mCat) :=
  QRegister.block 3951 3 (Nat.le_add_right_of_le (core_ge_3954 80))

theorem rCoreBlock48_disj_topCat (mCat : ℕ) (hmCat : mCat ≤ 48) : (rCoreBlock48 80).DisjointWires
    ((QRegister.block (fullSysCoreWires 80) 48 le_rfl).compose (SingleCatSpine.rTopCatSlice mCat 48
      hmCat)) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  have hi := i.isLt
  have hj := (SingleCatSpine.rTopCatSlice mCat 48 hmCat j).isLt
  dsimp [rCoreBlock48, QRegister.compose_apply, QRegister.block, Fin.natAddEmb, Fin.castLEEmb] at hv
  omega

/-- Local `(fullSysCoreWires 80 + mCat)` embedding inside `fullSysCoreWires 80 + 48` via
  `rTopCatSlice`,
`rfl`-identical to `SelectStitch.rCoreTopCatInCT`. -/
def rCoreTopCatInCT (mCat : ℕ) (hmCat : mCat ≤ 48) : QRegister (fullSysCoreWires 80 + mCat)
    (fullSysCoreWires 80 + 48) := (rCoreBlock48 80).concat ((QRegister.block
    (fullSysCoreWires 80) 48 le_rfl).compose
    (SingleCatSpine.rTopCatSlice mCat 48 hmCat))
    (rCoreBlock48_disj_topCat mCat hmCat)

theorem rTopCatSlice34_val_all : ∀ j : Fin 34, (SingleCatSpine.rTopCatSlice 34 48 (by
    decide) j).val = 14 + j.val := by
  decide

theorem not_mem_range_rCtrl3InCore {mPayload : ℕ} {q : Fin (fullSysCoreWires mPayload)}
    (hq : q.val < 3951 ∨ 3954 ≤ q.val) : q ∉ Set.range (rCtrl3InCore mPayload).wires := by
  rintro ⟨i, rfl⟩
  have hi := i.isLt
  simp only [rCtrl3InCore, qreg_block_apply, Fin.val_mk] at hq
  omega

theorem vepCoreFns_congr_outside_rCtrl3 {mPayload : ℕ} (c : Configuration) (hm : 22 ≤
    mPayload) (w : Fin 3) {x₁ x₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hOut : ∀ q, q ∉ Set.range (rCtrl3InCore mPayload).wires → x₁ q = x₂ q) : slot2AxisSum w
    x₁ = slot2AxisSum w x₂ ∧ slot2M48Val c hm w x₁ = slot2M48Val c hm w x₂ ∧ vepOnlyM48Val hm
    w x₁ = vepOnlyM48Val hm w x₂ ∧ x₁ (coreCosetB1Block (hm6_of_hm22 hm) w) = x₂
    (coreCosetB1Block (hm6_of_hm22 hm) w) ∧ vepEffSlope48 c hm w x₁ = vepEffSlope48 c hm w x₂ := by
  have hCoin0 : coin0Active x₁ = coin0Active x₂ := by
    unfold coin0Active
    rw [hOut _ (not_mem_range_rCtrl3InCore (Or.inl (by simp [wSlot2, QRegExt.idReg]))),
        hOut _ (not_mem_range_rCtrl3InCore (Or.inl (by simp [wSlot1, QRegExt.idReg]))),
        hOut _ (not_mem_range_rCtrl3InCore (Or.inl (by simp [wSlot0, QRegExt.idReg])))]
  have hNuc : regVal (rNucIdx hm (QRegExt.idReg _)) x₁ = regVal (rNucIdx hm (QRegExt.idReg _)) x₂ :=
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr (rNucIdx hm (QRegExt.idReg
      _)) fun d ↦
      hOut _ (not_mem_range_rCtrl3InCore (Or.inr (le_trans (by
        decide : 3954 ≤ 3960) (rNucIdx_val_ge_3960 hm d))))
  have hHigh : vepHighNuc hm x₁ = vepHighNuc hm x₂ := by
    rw [Bool.eq_iff_iff, ProjZ512QftAndTwist288.vepHighNuc_iff hm x₁,
      ProjZ512QftAndTwist288.vepHighNuc_iff hm x₂, hCoin0, hNuc]
  have hSlot2 : slot2M48Val c hm w x₁ = slot2M48Val c hm w x₂ := by
    unfold slot2M48Val
    by_cases hc1 : coin0Active x₁ = true ∧ regVal (rNucIdx hm (QRegExt.idReg _)) x₁ < 216
    · rw [dite_eq_left hc1, dite_eq_left (by rwa [← hCoin0, ← hNuc])]
      exact congrArg (fun idx ↦ nuclearM48 c idx w) (Fin.ext hNuc)
    · rw [dite_eq_right hc1, dite_eq_right (by rwa [← hCoin0, ← hNuc])]
  have hVep : vepOnlyM48Val hm w x₁ = vepOnlyM48Val hm w x₂ := by
    unfold vepOnlyM48Val
    rw [hHigh]
    split_ifs
    · refine congrArg (2 ^ 39 * ·) (congrArg bitsVal (funext fun j ↦ hOut _ ?_))
      unfold vepProj9CoreIdx
      split_ifs
      · exact not_mem_range_rCtrl3InCore (Or.inr (show 3954 ≤ 3957 + w.val by omega))
      · have := w.isLt
        have := j.isLt
        exact not_mem_range_rCtrl3InCore
          (Or.inl (show (3924 + 8 * w.val) + (j.val - 1) < 3951 by omega))
    · rfl
  have hB1 : x₁ (coreCosetB1Block (hm6_of_hm22 hm) w) = x₂ (coreCosetB1Block (hm6_of_hm22 hm) w) :=
    hOut _ (not_mem_range_rCtrl3InCore (Or.inr (coreCosetB1Block_val_ge_3954 hm w)))
  have hSum : slot2AxisSum w x₁ = slot2AxisSum w x₂ := by
    rw [SinglePassNuclearTwist288.slot2AxisSum_eq_bitPlane_sum w x₁,
      SinglePassNuclearTwist288.slot2AxisSum_eq_bitPlane_sum w x₂]
    refine Finset.sum_congr rfl fun r _ ↦ congrArg (2 ^ r.val * ·) (Finset.sum_congr rfl fun e _ ↦
      ?_)
    refine congrArg ZMod.val (hOut _ (not_mem_range_rCtrl3InCore (Or.inl ?_)))
    rw [HybridStream288Aux.elecAxisBitWire_val]
    have he : e.val < 218 := e.isLt
    have hw := w.isLt
    have hr := r.isLt
    omega
  have hEff : vepEffSlope48 c hm w x₁ = vepEffSlope48 c hm w x₂ := by
    unfold vepEffSlope48
    rw [hSlot2, hVep, hB1]
  exact ⟨hSum, hSlot2, hVep, hB1, hEff⟩

set_option exponentiation.threshold 8192 in
theorem commutesWithReg_rCtrl3_uXor32Core : CommutesWithReg (rCtrl3InCore 80) (uXor32Core 80).1 :=
  have hOutFn : ∀ ξ₁ ξ₂ : BitAssignment (fullSysCoreWires 80),
      (∀ w, w ∉ Set.range (rCtrl3InCore 80).wires → ξ₁ w = ξ₂ w) →
      ∀ w, w ∉ Set.range (rCtrl3InCore 80).wires →
      NuclearTwistRealizes.xor32BitFn 80 ξ₁ w = NuclearTwistRealizes.xor32BitFn 80 ξ₂ w :=
    fun _ _ hOut w hw ↦ by
      dsimp only [NuclearTwistRealizes.xor32BitFn]
      rw [hOut w hw]
  commutesWithReg_of_smul_ket (rCtrl3InCore 80) (uXor32Core 80).1 (fun _ ↦ 1)
    (NuclearTwistRealizes.xor32BitFn 80) (NuclearTwistRealizes.xor32BitFn 80)
    (fun ξ ↦ (Barrel3PassCommuteHelpers.uXor32Core_mulVec_ket 80 ξ).trans (one_smul _ _).symm)
    (NuclearTwistRealizes.xor32BitFn_involutive 80) (NuclearTwistRealizes.xor32BitFn_involutive 80)
    (fun _ i ↦ ite_eq_right fun h ↦ absurd h.1 (by
      have := i.isLt
      simp only [rCtrl3InCore, qreg_block_apply, Fin.val_mk]
      omega))
    (fun _ _ _ ↦ rfl) hOutFn hOutFn

theorem mkEntry54_truncWCfg_eq {K : ℕ} (hK48 : K ≤
    48) (c : Configuration) (w : Fin 3) (i : Fin 54) (s d : Bool) : mkEntry54 K (truncWCfg K c) w i
    s d =
    SubvoxelNuclearTrunc34And33Physics.nuclearMW K c ⟨4 * i.val +
    (if s then 2 else 0) + (if d then 1 else 0), mkEntry54_lt216 i s d⟩ w := by
  unfold mkEntry54
  rw [SubvoxelNuclearTrunc28To35Chiral.nuclearM48_truncWCfg hK48]
  change (_ >>> (48 - K)) = _
  rw [Nat.shiftRight_eq_div_pow, mul_comm (2 ^ (48 - K)),
    Nat.mul_div_left _ (Nat.two_pow_pos (48 - K))]

theorem zmod2_testBit_b0_comb (t0 t1 : Bool) (b0 : ZMod 2) : (if t0 then (1 : ZMod 2) else 0)
    + b0 * (if xor t0 t1 then 1 else 0) = if (if b0 = 1 then t1 else t0) then 1 else 0 := by
  rcases bit_cases b0 with rfl | rfl
  all_goals cases t0
  all_goals cases t1
  all_goals decide

theorem zmod2_collapse_s_comb (b1 : ZMod 2) (pf pt : Bool) : (if pf then (if false = true then
    b1 else 1 + b1) else 0) +
    (if pt then (if true = true then b1 else 1 + b1) else 0) = if (if decide (b1 = 1) then pt else
      pf) then (1 : ZMod 2) else 0 := by
  rcases bit_cases b1 with rfl | rfl
  all_goals cases pf
  all_goals cases pt
  all_goals decide

theorem zmod2_four_i_add_bits (iVal : ℕ) (b1 b0 : ZMod 2) : 4 * iVal + (if decide (b1 = 1) then
    2 else 0) + (if decide (b0 = 1) then 1 else 0) =
    4 * iVal + 2 * b1.val + b0.val := by
  have h01 : decide ((0 : ZMod 2) = 1) = false := rfl
  have h11 : decide ((1 : ZMod 2) = 1) = true := rfl
  rcases bit_cases b1 with rfl | rfl
  all_goals rcases bit_cases b0 with rfl | rfl
  all_goals simp only [h01, decide_true, ZMod.val_zero, ZMod.val_one, Bool.false_eq_true,
    ↓reduceIte]

theorem padZero14CH_on_rSysNo14_ge14 {mPayload H n : ℕ} (rCore : QRegister (fullSysCoreWires
    mPayload) n) (rHdr61 : QRegister 61 n)
    (rPreHold : QRegister H n) (rSum14 : QRegister 14 n) (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) (hCHSum : (rCHHold rCore
    rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14) (ξ : BitAssignment n)
    (q : Fin ((fullSysCoreWires mPayload + 61) + H)) (hq14 : 14 ≤ q.val) : padZero14CH (fun p
    ↦
      ξ ((rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum) p)) q =
      ξ ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH) q) := by
  let kC := fullSysCoreWires mPayload
  have hkC := core_ge_3954 mPayload
  have hqLt := q.isLt
  dsimp only [padZero14CH]
  rw [dite_eq_right (show ¬(q.val < 14) by omega)]
  refine congrArg ξ ?_
  let rS := rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum
  let rH := rCHHold rCore rHdr61 rPreHold hCH61 hCHPH
  let qS : Fin ((((kC - 14) + 61) + H) + 14) := ⟨q.val - 14, by omega⟩
  by_cases h1 : q.val < kC
  · rw [congrArg rS (Fin.ext rfl :
        qS = Fin.castAdd 14 (Fin.castAdd H (Fin.castAdd 61 ⟨q.val - 14, by omega⟩))),
      congrArg rH (Fin.ext rfl : q = Fin.castAdd H (Fin.castAdd 61 ⟨q.val, h1⟩))]
    simp only [rS, rH, rSysNo14, rCHHold, QRegister.concat_apply_left, QRegister.slice_apply]
    exact congrArg rCore (Fin.ext (Nat.add_sub_cancel' hq14))
  · by_cases h2 : q.val < kC + 61
    · rw [congrArg rS (Fin.ext (show q.val - 14 = (kC - 14) + (q.val - kC) by omega) :
          qS = Fin.castAdd 14 (Fin.castAdd H (Fin.natAdd (kC - 14) ⟨q.val - kC, by omega⟩))),
        congrArg rH (Fin.ext (show q.val = kC + (q.val - kC) by omega) :
          q = Fin.castAdd H (Fin.natAdd kC ⟨q.val - kC, by omega⟩))]
      dsimp only [rS, rH, rSysNo14, rCHHold]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_right,
        QRegister.concat_apply_left, QRegister.concat_apply_right]
    · rw [congrArg rS (Fin.ext (show q.val - 14 = ((kC - 14) + 61) + (q.val - (kC + 61)) by omega) :
          qS = Fin.castAdd 14 (Fin.natAdd ((kC - 14) + 61) ⟨q.val - (kC + 61), by omega⟩)),
        congrArg rH (Fin.ext (show q.val = (kC + 61) + (q.val - (kC + 61)) by omega) :
          q = Fin.natAdd (kC + 61) ⟨q.val - (kC + 61), by omega⟩)]
      dsimp only [rS, rH, rSysNo14, rCHHold]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_right, QRegister.concat_apply_right]

theorem uLeaf54_on_hdr_eq {H : ℕ} (hH54 : H ≤ 54) (b1 : ZMod 2) (u54Val : Fin 54 →
    ZMod 2) (xHi : Fin 54 → ZMod 2) (xPre : Fin H → ZMod 2)
    (hHiLt : ∀ k : Fin 54, k.val < H → xHi k = u54Val k * (1 + b1)) (hHiGe : ∀ k : Fin 54,
      H ≤ k.val → xHi k = u54Val k)
    (hPre : ∀ m : Fin H, xPre m = u54Val ⟨m.val, by have := m.isLt; omega⟩ * b1)
    (i : Fin 54) (s : Bool) :
    uLeaf54 b1 xHi xPre i s = u54Val i * (if s then b1 else 1 + b1) := by
  dsimp only [uLeaf54]
  by_cases hi : i.val < H
  · rw [dite_pos_eq hi]
    cases s
    · exact hHiLt i hi
    · exact (hPre ⟨i.val, hi⟩).trans (congrArg (· * b1) (congrArg u54Val (Fin.ext rfl)))
  · rw [dite_neg_eq hi, hHiGe i (by omega)]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ring
    · rfl

theorem disj_compose_both {a b m n : ℕ} (r : QRegister m n) {r₁ : QRegister a m} {r₂ : QRegister b
    m} (h : r₁.DisjointWires r₂) :
    (r.compose r₁).DisjointWires (r.compose r₂) := by
  rw [QRegister.disjoint_iff]
  exact fun i j hij ↦ h.ne i j (r.wires.injective hij)

theorem diagOn_compl_of_mulVec_shiftCatKet {B n : ℕ} (rCat : QRegister B n)
    {M : Operator (2 ^ n)} (h : ∀ ξ : BitAssignment n, ∃ (z : ℂ) (d : ℕ), M.mulVec (basisKet
    ξ) = z • basisKet (shiftCatKet rCat ξ d)) : DiagOn (Finset.univ \ rCat.image) M := by
  apply DiagOn.of_mulVec_basisKet
  intro β i hnz u hu
  obtain ⟨z, d, hM⟩ := h β
  rw [hM, Pi.smul_apply] at hnz
  have hket : (Pi.single ((basisBitsEquiv n).symm (shiftCatKet rCat β d)) (1 : ℂ) : Fin (2 ^ n) →
    ℂ) i ≠ 0 :=
    right_ne_zero_of_mul hnz
  rw [Pi.single_apply] at hket
  split_ifs at hket with hEq
  · subst hEq
    rw [basisBits_symm_apply]
    exact shiftCatKet_outside rCat β d (Finset.mem_sdiff.mp hu).2
  · exact absurd rfl hket

theorem image_subset_compl_of_disj {a b n : ℕ} {r₁ : QRegister a n} {r₂ : QRegister b n} (h :
    r₁.DisjointWires r₂) : r₁.image ⊆ Finset.univ \ r₂.image := by
  intro u hu
  obtain ⟨i, rfl⟩ := (QRegister.mem_image r₁ _).mp hu
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h.apply_not_mem_right i⟩

end KickKoffKH

export SubvoxelNuclearTrunc34And33Physics (truncWCfg)

def rCoreInCat34 : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 34) :=
  QRegister.block 0 (fullSysCoreWires 80) (by omega)

theorem rCoreInCat34_compose_rCtrl3 : rCoreInCat34.compose (rCtrl3InCore 80) = rCtrl3InCoreCat 34 :=
  by
  apply qreg_ext
  exact fun _ ↦ Fin.ext (by simp [rCoreInCat34, rCtrl3InCore, rCtrl3InCoreCat])

theorem rCoreTopCatInCT34_compose_rCoreInCat34 : (rCoreTopCatInCT 34 (by
    decide)).compose rCoreInCat34 = rCoreBlock48 80 := by
  apply qreg_ext
  intro iC
  rw [QRegister.compose_apply, show rCoreInCat34 iC = Fin.castAdd 34 iC from
    Fin.ext (by simp [rCoreInCat34])]
  exact QRegister.concat_apply_left _ _ _ _

set_option maxRecDepth 512

end ConfigLeaf4Twist162

set_option maxRecDepth 512

end Leaf4Twist162

end
end Leaf4Twist162

section MomAdapterGen
local instance (priority := 1000000) instNeZeroTwoPow_MomAdapterGen (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace MomAdapterGen

section ConfigMomAdapterGen

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority := 1000000) instLoc_MomAdapterGen_1InstNeZeroTwoPowMomAdapterGen (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open FullSysCatSegmentBridge (fullSysCoreWires iSlot2)
open OraAndPrepBundle (PosPostPrepCert)
open TierBClean80Closure (tierBQftFull)
open PosSlots24TopWrapper (PosSlots24DataGen)
open MergedVepTopCoinCollapse (topCoinPropGen)

set_option exponentiation.threshold 4160 in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem topCoinPropGen_comp_truncCfg_of_posPhase_param {mWorkPos : ℕ} (post : PosPostPrepCert 80)
    (posData : PosSlots24DataGen (fullSysCoreWires 80) (iSlot2
    80) mWorkPos) {uPosPhase0 : Unitary (2 ^ (fullSysCoreWires 80))} (hPosEq : ∀ cfg,
      posData.uPosPhase cfg = uPosPhase0)
    (uTwistRef0 : Configuration → Unitary (2 ^ (fullSysCoreWires 80))) (truncCfg : Configuration →
      Configuration) (c : Fin 8)
    (B : Configuration → Operator (2 ^ systemQubits)) (hTop : ∀ cfg, topCoinPropGen (le_rfl :
    80 ≤
      80) tierBQftFull cfg post uTwistRef0 posData c (B cfg)) (cfg : Configuration) : topCoinPropGen
      (le_rfl : 80 ≤ 80) tierBQftFull cfg post
    (fun c0 ↦ uTwistRef0 (truncCfg c0)) posData c (B (truncCfg cfg)) := by
  have h := hTop (truncCfg cfg)
  dsimp only [topCoinPropGen] at h ⊢
  rwa [hPosEq cfg, ← hPosEq (truncCfg cfg)]

set_option maxRecDepth 512

end ConfigMomAdapterGen

end MomAdapterGen

end
end MomAdapterGen

section Leaf3MidKickAndPrepCore
local instance (priority := 1000000) instNeZeroTwoPow_Leaf3MidKickAndPrepCore (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace Leaf3MidKickAndPrepCore

section ConfigLeaf3MidKickAndPrepCore

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority :=
  1000000) instLoc_Leaf3MidKickAndPrepCore_1InstNeZeroTwoPowW7L (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore (hadamardAll)
-- Root solution namespace already active.
open FullSysCatSegmentBridge
  (FullSysPrepareBundle fullSys_zero_add_le_of_le)
open FullSysPrepare6Slot (fullSysCoinIdx)
open FullSysFullPrepareAndTopConcrete (coreWiresSym corePayloadSym
   coreHadamardUnitary coreHadamardUnitary_inv coreHadamardUnitary_eq_embed)
open SegmentAndTopClosure (rCleanSubW compressCleanUnitary
   embedUnitary_compressCleanUnitary_mul_proj embedUnitary_compressCleanUnitary_inv_mul_proj)
open OraAndPrepBundle (PosPostPrepCert)
open ZeroSubwireCoinPrep80 (coinHwa wIdealRat rCoin3Core two_le_max100)
open ZeroSubwireHarmonicGridPert (zeroSubwireConstPrepUnitary)
open Coin3PerHorizon5799
  (CleanPrepProg dCleanSubDynProg dCleanSubDynProg_count_TOFF dCleanSubDynProg_count_T_le
    realizesCleanWorkspace_dCleanSubDynProg)
open InterWalkRSum42Hoist
  (PreservesFeature FixesLow3924 h3924_core h3924_be fixesLow3924_embedMatrix_high
   fixesLow3924_coreAncSym80_embed fixesLow3924_castNatUnitary)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem w7lp_embedUnitary_inv_eq {k n : ℕ} (r : QRegister k n) (U : Unitary (2 ^ k)) :
    (r.embedUnitary U)⁻¹ = r.embedUnitary U⁻¹ :=
  inv_eq_of_mul_eq_one_right (by
    rw [← QRegister.embedUnitary_mul, mul_inv_cancel, QRegister.embedUnitary_one])

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Specification bundle for a 4-wire `CleanPrepProg 4` 3-coin state preparation at scale `α_real`,
lowered `.T` budget `tCoin`, and 6-slot L1 weight error `err_w` (`0 .TOFF`, `0` persistent subwires,
borrowing `2` clean workspace wires during `dCleanSubDynProg`). -/
structure Coin3CleanProgSpec (α_real : ℝ) (tCoin : ℕ) (err_w : ℝ) where
  pPrep : CleanPrepProg 4
  hT : pPrep.tBound ≤ tCoin
  hValid : CleanPrepProg.ValidDyn ({⟨3, by decide⟩} : Finset (Wire 4)) pPrep
  hClean :
    (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 * pPrep.toCircuit.eval.1 *
      (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 =
    pPrep.toCircuit.eval.1 * (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0
  uCoin : Unitary (2 ^ 3)
  hUCoin : uCoin = compressCleanUnitary coinHwa pPrep.toCircuit.eval hClean
  hWeightErr :
    ∑ k : Fin 6, |α_real * ‖uCoin.1 (fullSysCoinIdx k) 0‖ ^ 2 - wIdealRat k| ≤ err_w

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Forward dynamic wrapper for `Coin3CleanProgSpec.pPrep` borrowing `2` clean workspace wires. -/
def dCoin3CleanProgDyn {mPayload tCoin : ℕ} {α_real err_w : ℝ} (mWorkPost : ℕ) (spec :
    Coin3CleanProgSpec α_real tCoin err_w) {Var : Type} {n : ℕ} (v : Var)
    (rBE : QRegister (coreWiresSym mPayload) n) (rWork : QRegister (Nat.max 100 mWorkPost) n)
    (hD : rBE.DisjointWires rWork) : DynamicCircuit Var n := dCleanSubDynProg coinHwa
    (two_le_max100 mWorkPost) v (rBE.compose (rCoin3Core mPayload)) rWork
    (hD.compose_left (rCoin3Core mPayload)) spec.pPrep

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Inverse dynamic wrapper for `Coin3CleanProgSpec.pPrep` borrowing `2` clean workspace wires. -/
def dCoin3CleanProgInvDyn {mPayload tCoin : ℕ} {α_real err_w : ℝ} (mWorkPost : ℕ) (spec :
    Coin3CleanProgSpec α_real tCoin err_w) {Var : Type} {n : ℕ} (v : Var)
    (rBE : QRegister (coreWiresSym mPayload) n) (rWork : QRegister (Nat.max 100 mWorkPost) n)
    (hD : rBE.DisjointWires rWork) : DynamicCircuit Var n := dCleanSubDynProg coinHwa
    (two_le_max100 mWorkPost) v (rBE.compose (rCoin3Core mPayload)) rWork
    (hD.compose_left (rCoin3Core mPayload)) spec.pPrep.inv

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem dCleanSubCoin3_realizes {mPayload : ℕ} (mWorkPost : ℕ) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rBE : QRegister (coreWiresSym mPayload) n) (rWork : QRegister (Nat.max 100 mWorkPost) n) (hD :
      rBE.DisjointWires rWork) (p : CleanPrepProg 4)
    (hV : CleanPrepProg.ValidDyn ({⟨3, by decide⟩} : Finset (Wire 4)) p) (U : Unitary (2 ^ 3))
    (hProj : p.toCircuit.eval.1 * (QRegister.block 3 1 (by
      omega) : QRegister 1 4).basisOutcomeProjector 0 =
    ((QRegister.block 0 3 (by
      omega) : QRegister 3 4).embedUnitary U).1 * (QRegister.block 3 1 (by
      omega) : QRegister 1 4).basisOutcomeProjector 0) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rBE rWork ((rCoin3Core
      mPayload).embedUnitary U)
    (dCleanSubDynProg coinHwa (two_le_max100 mWorkPost) v (rBE.compose (rCoin3Core mPayload)) rWork
      (hD.compose_left (rCoin3Core mPayload)) p) :=
  DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace.widenActive
    (realizesCleanWorkspace_dCleanSubDynProg coinHwa (two_le_max100 mWorkPost) v
      (rBE.compose (rCoin3Core mPayload)) rWork (hD.compose_left (rCoin3Core mPayload))
      _ (fun _ hw ↦ by rw [Finset.mem_singleton.mp hw]) p hV U hProj)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem coreHadamard_realizes {mPayload mW : ℕ} {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (rBE : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mW n) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rBE rWork (coreHadamardUnitary mPayload)
    (.circuit ((hadamardAll (corePayloadSym mPayload)).onRegister rBE) : DynamicCircuit Var n) :=
  DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit rBE rWork
    (coreHadamardUnitary mPayload) _ (Circuit.eval_onRegister rBE (hadamardAll (corePayloadSym
      mPayload)))

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Zero-subwire `FullSysPrepareBundle mPayload` built from any `PosPostPrepCert mPayload` and
`Coin3CleanProgSpec α_real tCoin err_w` (`tPrep = tCoin + post.tPosPost`,
`mWorkPrep = Nat.max 100 post.mWorkPost`, `0 .TOFF`). -/
def zeroSubwireCleanProgPrepBundle {mPayload tCoin : ℕ} {α_real err_w : ℝ} (post : PosPostPrepCert
    mPayload)
    (spec : Coin3CleanProgSpec α_real tCoin err_w) : FullSysPrepareBundle mPayload :=
  let selPost : QRegister post.mWorkPost (Nat.max 100 post.mWorkPost) := QRegister.block 0
    post.mWorkPost (fullSys_zero_add_le_of_le (Nat.le_max_right 100 post.mWorkPost))
  { mWorkPrep := Nat.max 100 post.mWorkPost
    tPrep := tCoin + post.tPosPost
    uPrep := fun _ ↦ zeroSubwireConstPrepUnitary post spec.uCoin
    dPrep := fun _ {_} {_} v rBE rWork hD ↦ .seq
      (.seq (dCoin3CleanProgDyn post.mWorkPost spec v rBE rWork hD)
        (.circuit ((hadamardAll (corePayloadSym mPayload)).onRegister rBE)))
      (post.dPosPost v rBE (rWork.compose selPost))
    dPrepInv := fun _ {_} {_} v rBE rWork hD ↦ .seq
      (.seq (post.dPosPostInv v rBE (rWork.compose selPost))
        (.circuit ((hadamardAll (corePayloadSym mPayload)).onRegister rBE)))
      (dCoin3CleanProgInvDyn post.mWorkPost spec v rBE rWork hD)
    hToffPrep := fun _ {_} {_} _ _ _ _ ↦ by
      simp [DynamicCircuit.count, dCoin3CleanProgDyn, dCleanSubDynProg_count_TOFF,
        Circuit.count_onRegister, post.hToffPosPost]
    hToffPrepInv := fun _ {_} {_} _ _ _ _ ↦ by
      simp [DynamicCircuit.count, dCoin3CleanProgInvDyn, dCleanSubDynProg_count_TOFF,
        Circuit.count_onRegister, post.hToffPosPostInv]
    hTPrep := fun _ {_} {_} v rBE rWork hD ↦ by
      have hC := (dCleanSubDynProg_count_T_le coinHwa (two_le_max100 post.mWorkPost) v
        (rBE.compose (rCoin3Core mPayload)) rWork (hD.compose_left _) spec.pPrep).trans spec.hT
      have hH : ((hadamardAll (corePayloadSym mPayload)).onRegister rBE).count .T = 0 := by
        simp [Circuit.count_onRegister]
      have hP := post.hTPosPost v rBE (rWork.compose selPost)
      dsimp only [DynamicCircuit.count, dCoin3CleanProgDyn]
      omega
    hTPrepInv := fun _ {_} {_} v rBE rWork hD ↦ by
      have hC := (dCleanSubDynProg_count_T_le coinHwa (two_le_max100 post.mWorkPost) v
        (rBE.compose (rCoin3Core mPayload)) rWork (hD.compose_left _) spec.pPrep.inv).trans
        (CleanPrepProg.tBound_inv spec.pPrep ▸ spec.hT)
      have hH : ((hadamardAll (corePayloadSym mPayload)).onRegister rBE).count .T = 0 := by
        simp [Circuit.count_onRegister]
      have hP := post.hTPosPostInv v rBE (rWork.compose selPost)
      dsimp only [DynamicCircuit.count, dCoin3CleanProgInvDyn]
      omega
    hRealPrep := fun _ {_} [_] [_] {_} [_] v rBE rWork hD ↦
      ((dCleanSubCoin3_realizes post.mWorkPost v rBE rWork hD spec.pPrep spec.hValid spec.uCoin
          (by
            rw [spec.hUCoin]
            exact (embedUnitary_compressCleanUnitary_mul_proj coinHwa
              spec.pPrep.toCircuit.eval spec.hClean).symm)).seq
        hD (coreHadamard_realizes rBE rWork)).seq hD
        ((post.hRealPosPost v rBE (rWork.compose selPost)
          (hD.compose_right selPost)).widenWorkspace)
    hRealPrepInv := fun _ {_} [_] [_] {_} [_] v rBE rWork hD ↦ by
      rw [show (zeroSubwireConstPrepUnitary post spec.uCoin)⁻¹ =
          ((rCoin3Core mPayload).embedUnitary spec.uCoin)⁻¹ *
            (coreHadamardUnitary mPayload * (post.uPosPost)⁻¹) by
        dsimp only [zeroSubwireConstPrepUnitary]
        rw [_root_.mul_inv_rev, _root_.mul_inv_rev, coreHadamardUnitary_inv, mul_assoc],
        w7lp_embedUnitary_inv_eq]
      exact (((post.hRealPosPostInv v rBE (rWork.compose selPost)
        (hD.compose_right selPost)).widenWorkspace).seq hD (coreHadamard_realizes rBE rWork)).seq hD
        (dCleanSubCoin3_realizes post.mWorkPost v rBE rWork hD spec.pPrep.inv spec.hValid.inv
          spec.uCoin⁻¹ (by
            rw [CleanPrepProg.eval_inv_toCircuit, spec.hUCoin]
            exact (embedUnitary_compressCleanUnitary_inv_mul_proj coinHwa
              spec.pPrep.toCircuit.eval spec.hClean).symm)) }

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem zeroSubwireCleanProgPrep_hmPrep_gen {mPayload mWork tCoin : ℕ} {α_real err_w : ℝ}
    (post : PosPostPrepCert mPayload) (spec : Coin3CleanProgSpec α_real tCoin err_w) (h100 : 100 ≤
      mWork) (hmPost : post.mWorkPost ≤ mWork) :
    (zeroSubwireCleanProgPrepBundle post spec).mWorkPrep ≤ mWork :=
  Nat.max_le.mpr ⟨h100, hmPost⟩

section Part1BS3Invariants

open PosPostPrep80MergedVepS3
open ZeroAncillaUSP hiding ket

set_option exponentiation.threshold 4160 in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem fixesLow3924_zeroSubwireCleanProgPrepBundle {tCoin : ℕ} {α_real err_w : ℝ}
    (post : PosPostPrepCert 80) (hFixPost : FixesLow3924 h3924_core post.uPosPost.1)
    (spec : Coin3CleanProgSpec α_real tCoin err_w) (cfg : Configuration) : FixesLow3924 h3924_be
      ((zeroSubwireCleanProgPrepBundle post spec).uPrep cfg).1 := by
  have hFixHad : FixesLow3924 h3924_core (coreHadamardUnitary 80).1 := by
    rw [coreHadamardUnitary_eq_embed 80, QRegister.embedUnitary_val]
    refine fixesLow3924_embedMatrix_high h3924_core (fun i ↦ ?_) _
    have := i.isLt
    dsimp [corePayloadSym, QRegister.block, Function.Embedding.trans, Fin.castLEEmb,
      Fin.natAddEmb, Fin.castLE, Fin.natAdd, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
        SpecsAux.SpecMirror.projectileBits]
    omega
  have hFixCoin : FixesLow3924 h3924_core ((rCoin3Core 80).embedUnitary spec.uCoin).1 := by
    dsimp only [rCoin3Core]
    rw [QRegister.embedUnitary_compose]
    exact fixesLow3924_coreAncSym80_embed _
  refine fixesLow3924_castNatUnitary rfl h3924_core h3924_be ?_
  change FixesLow3924 h3924_core
    ((post.uPosPost * (coreHadamardUnitary 80 * (rCoin3Core 80).embedUnitary spec.uCoin)).1)
  simp only [Submonoid.coe_mul]
  exact PreservesFeature.mul hFixPost (PreservesFeature.mul hFixHad hFixCoin)

end Part1BS3Invariants

end

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512

end ConfigLeaf3MidKickAndPrepCore
end Leaf3MidKickAndPrepCore

end
end Leaf3MidKickAndPrepCore

end QuantumComputation.Specs.StoppingPowerSolution
