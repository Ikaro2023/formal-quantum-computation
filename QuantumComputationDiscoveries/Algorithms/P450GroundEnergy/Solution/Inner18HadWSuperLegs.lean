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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsA
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsB
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsC
/-!
# Narrow `wInner2 = 18` + `46-T` Hadamard W-State Three-Gear Superstep Walk Legs

Top-level facade re-exporting `Inner18HadWSuperLegsA`, `B`, `C` and providing:
1. `inner18TurnDyn`: Coarse/Mid `Hot128` turnaround leg.
2. `inner18Step4ColdDyn`: `294 + tMag` `T` (`68`-scratch) cold Step-4 unload leg.
3. `directDNeg732Dyn`: `732-T` (`63`-scratch) direct `-D_l` phase pass for Fine gear.
4. `selectSwapW642Keep9LoadDyn` (`2,644 T`) and `120`-scratch Fine-gear walk legs.
-/

@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegs
open QuantumComputation.Specs QuantumComputation.Specs.P450
export Solution.Inner18HadWSuperLegsA (
  Mag30Circ2 Mag30Bundle2 preservesWires_comm_predProj_oneHot OneHot14LoadCirc2 OneHot14LoadBundle_3
  mid159Xo7Reg_disjoint_qro mid159Hot128Reg_eq_qrom oneHotPred_perm_eq
  xo7OneHotClearCirc_mul_qrom14_mul_self preservesWiresMid159Qroxo_hot
  qromXoBorrowLoad14GenDyn countQromXoBorrowLoad14GenDyn_toff
  countQromXoBorrowLoad14GenDyn_t predProj_oneHot_comm_xo7Clear
  cleanPredRealizesQromXoBorrowLoad14GenDyn midSub18_disjoint_xo_hot Mux23Circ Mux23Bundle
  prepMid18BorrowGenDyn countPrepMid18BorrowGenDyn_toff countPrepMid18BorrowGenDyn_t
  cleanPredRealizesPrepMid18BorrowGenDyn genPrepMid18InvDyn countGenPrepMid18InvDyn_toff
  countGenPrepMid18InvDyn_t cleanUnloadsWpGenPrepMid18InvDyn
  pktMuxSwap23UnitaryMux9AltBit_eq hadWMux23Circ hadWMux23Bundle keep9Pi128Hot14Bool
  hotLinearKeep9Pi128_oneHot prepMid18DagW3Pi128Dyn countPrepMid18DagW3Pi128Dyn_toff
  countPrepMid18DagW3Pi128Dyn_t wpQAssign_conj cleanUnloadConj
  wpPrepMid18DagW3Pi128Dyn_xoOneHot
)
export Solution.Inner18HadWSuperLegsB (
  muxCongr muxConst muxConstOne concat_singleton_right preservesWires_muxUnitary
  circuitH0_mul_self circuitH_mul_self cnot_mulVec_H_ket cHXor2 cHXoMain countCHXor2_toff
  countCHXor2_t countCHXoMain_toff countCHXoMain_t ketCHXor2 ketCHXoMain is1BBool2
  is1BBool_eq_hotZMod mainSpinCancelUBMux midInMX xo8InMX xo7InMX mXOfUB
  xo8InMX_disjoint_sig midInMX_disjoint_xo7 xo7InMX_disjoint_mid spinCancelMXMux
  spinCancelMXMux_mul_self embedSpinCancelMXMux_ofUB embed_xo7MuxMX_ofUB actInMX
  actInMX_disjoint_xo7 spinAct_disj spinAct mainHotSpinCircuit countMainHotSpinCircuit_toff
  countMainHotSpinCircuit_t mainHotSpinCircuit_mul_self xo8InMX_disjoint_mid
  embed_reflMidUnitary_congr embed_reflMidUnitary_inMidWalkCat_eq
  mainHotSpinCircuit_eval_eqHotMux135 cleanPredRealizesMainHotSpinCircuit
  ctxMux7SpinAct_eq spin9InMX spinRawOps spinSteps spinSteps_numAnds spinCtrlHMidFn
  mainSpinCancel22Dyn countMainSpinCancel22Dyn_toff countMainSpinCancel22Dyn_t
  spinCtrlH_eval_eq cleanRealizesSpinCtrlHMidFn cleanRealizesMainSpinCancel22Dyn inner18Mfwd
  hot128NegUB inner18MX32Mux embedInner18MX32Mux_ofUB xoBInMX32 embedXoBInMX32_ofUB
  preserves_vec_zero bitPerm_vec_zero keep9Slice_alt_lt30
  b_lt_30_ofPrepMid18FromSliceKeep9_ne_zero locMX locScr locMX_disjoint_scr
  workPlace workPlace_compose_locMX workPlace_compose_locScr
  disjoint_support_onRegisterWorkPlace
)
export Solution.Inner18HadWSuperLegsC (cleanRealizesSet_onRegisterWorkPlace
  cleanTurnaroundWp_onRegister cleanUnloadsWp_onRegister keep9Pi128Rows128
  keep9Pi128FlatBool keep9Pi128FlatBool_combineAddr sum_parityPhaseTable
  qromW642Keep9Mid31UnloadDyn count_qromW642Keep9Mid31UnloadDyn_toff
  count_qromW642Keep9Mid31UnloadDyn_t cleanUnloadsSet_qromW642Keep9Mid31UnloadDyn
  hotMux135_mul ctxMux7_mul hotMux135_lift7_eq ctxMux7_lift7_eq hotMux135_embedMid_eq
  ctxMux7_embedMid_eq loc159Perm loc159Id loc159Perm_disjoint_tail loc159Perm_xo7_eq
  loc159Perm_hot128_eq inner18Step1LocDyn countInner18Step1LocDyn_toff
  countInner18Step1LocDyn_t cleanRealizesInner18Step1LocDyn inner18Step1Dyn
  countInner18Step1Dyn_toff countInner18Step1Dyn_t cleanRealizesSetInner18Step1Dyn
  disjoint_supportInner18Step1Dyn hot128DNeg68CompDyn countHot128DNeg68CompDyn_toff
  countHot128DNeg68CompDyn_t hot128DNeg68CompDyn_eq HotDNegCirc HotDNegBundle
  hotDNegActBranch muxHotDNegActBranch_eq locTurnCleanReg imageLocTurnCleanReg
  workPlace_turnClean_subset inner18TurnGenLocDyn countInner18TurnGenLocDyn_toff
  countInner18TurnGenLocDyn_t cleanTurnaroundWpInner18TurnGenLocDyn inner18TurnGenDyn
  countInner18TurnGenDyn_toff countInner18TurnGenDyn_t cleanTurnaroundWpInner18TurnGenDyn
  disjoint_supportInner18TurnGenDyn)
open Inner18HadWSuperLegsA Inner18HadWSuperLegsB Inner18HadWSuperLegsC
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 CoherentAlias Solution.CleanDyn
open AliasPrep
open Solution.CircuitModular Solution.GivensOps MidReflCtxRetain
open Phase2MidSandwich OptFactoredMag30AndCoin9 QuantizedFactoredMag30
open Cat11CompactPhase2Bridge ReordOuter13Bridge ZeroRcHotPrepMid21Fast OptXMeasUnload21
open Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 TopIntegrationBridge
open MobiusOptSubcube163Walk CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam
open CompactStepZeroCmp20OuterParam StepAnfAndCoin14Core CompactStepCompact2504ZeroCmp20
open Pi145SOSPermBridge StepOuter8Pi145Outer StepOuter8Pi145L1 StepKeep9Symp14Data
open StepBound148Borrow Tuned155Hot128SympQrom20 CompactOuter9Bound50Core LowBitPi145Select
open BellSingletCSwap58 FastUniform Inner18Symp14Walk HGadgetSympQrom
open QRegister InnerTable GroupUnary Pi145CompactRouter HadWStateMux25CompactA
open HadWStateMux25CompactB
open Solution.CircuitModular.UnsignedGivens (maskSumBit basisBits_symm_eq cnotMaskReg
  evolve_cnotMaskReg_ket eval_identity_mulVec)
open Function (update update_of_ne update_self update_apply)
open Observable (conj_coe)
open Unitary (coe_star)
open Submonoid (coe_mul)
open DynamicCircuit (qc_wp_circuit_compile compile_circuit)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowLegs (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
/-- `588 + tLoad14 + tMag1 + tMag2` `T` (`1,106 T` at `406, 56, 56`) `Hot128` turnaround. -/
def inner18TurnDyn {Var : Type} {sQrom tLoad14 tMag1 tMag2 N wOuter sUb : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : max 146 (121 + sQrom) ≤ kInner)
    (hUb : kInner ≤ sUb) (hDisj : rUB.DisjointWires rScrUb) (v : Var) : DynamicCircuit Var N :=
  inner18TurnGenDyn (Inner18HadWSuperLegsC.HotDNegCirc.hot68 Var) qrom mag1 mag2 π128 rUB rScrUb
    kInner hk hUb hDisj v
@[simp] theorem countInner18TurnDyn_toff {Var : Type} {sQrom tLoad14 tMag1 tMag2 N wOuter sUb : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : max 146 (121 + sQrom) ≤ kInner)
    (hUb : kInner ≤ sUb) (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    (inner18TurnDyn qrom mag1 mag2 π128 rUB rScrUb kInner hk hUb hDisj v).count .TOFF = 0 := by
  dsimp only [inner18TurnDyn]
  rw [countInner18TurnGenDyn_toff]
@[simp] theorem countInner18TurnDyn_t {Var : Type} {sQrom tLoad14 tMag1 tMag2 N wOuter sUb : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : max 146 (121 + sQrom) ≤ kInner)
    (hUb : kInner ≤ sUb) (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    (inner18TurnDyn qrom mag1 mag2 π128 rUB rScrUb kInner hk hUb hDisj v).count .T =
      588 + tLoad14 + tMag1 + tMag2 := by
  dsimp only [inner18TurnDyn]
  rw [countInner18TurnGenDyn_t]
theorem cleanTurnaroundWpInner18TurnDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {sQrom tLoad14 tMag1 tMag2 N wOuter sUb : ℕ} {uIdx1 uIdx2 : Unitary (2 ^ 5)}
    (qromBundle : OneHot14LoadBundle_3 Var sQrom tLoad14 keep9Hot24BoolTable)
    (mag1 : Mag30Bundle2 Var tMag1 uIdx1) (mag2 : Mag30Bundle2 Var tMag2 uIdx2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : max 146 (121 + sQrom) ≤ kInner)
    (hUb : kInner ≤ sUb) (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    CleanTurnaroundWp v
      (rScrUb.image ∪
        ((rUB.compose (rMidUB wOuter 18)).compose (midZeroPrefixReg 18 14 (by decide))).image)
      (rUB.embedUnitary (hot128NegUB wOuter * inner18Mfwd wOuter π128 uIdx1))
      ((rUB.embedUnitary (hot128NegUB wOuter * inner18Mfwd wOuter π128 uIdx2)) *
        rUB.embedUnitary (QubitisedWalk.reflMidUnitary (rMidUB wOuter 18)))
      (inner18TurnDyn qromBundle.toOneHot14LoadCirc2 mag1.toMag30Circ2 mag2.toMag30Circ2 π128 rUB
        rScrUb kInner hk hUb hDisj v) := by
  have h := cleanTurnaroundWpInner18TurnGenDyn (Inner18HadWSuperLegsC.HotDNegBundle.hot68 Var)
    qromBundle mag1 mag2 π128 rUB rScrUb kInner hk hUb hDisj v
  dsimp only [Inner18HadWSuperLegsC.HotDNegBundle.hot68] at h
  dsimp only [inner18TurnDyn, hot128NegUB, hot128NegRegUnitary]
  exact h
theorem disjoint_supportInner18TurnDyn {Var : Type}
    {sQrom tLoad14 tMag1 tMag2 N wOuter sUb kInner : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rMain : QRegister (nUB wOuter 18 + 11) N)
    (rScrUb : QRegister sUb N) (hk : max 146 (121 + sQrom) ≤ kInner) (hk1 : 1 + kInner ≤ sUb)
    (hMainScr : rMain.DisjointWires rScrUb) (v : Var) :
    Disjoint (inner18TurnDyn qrom mag1 mag2 π128 (rMain.compose (rUBInCat wOuter 18 11)) rScrUb
        kInner hk (by omega) (hMainScr.compose_left _) v).support
      ((((rMain.compose (rSysCatUB wOuter 18 11)).compose
        (QRegister.block 0 (2 * 58) (by decide))).image ∪ {rScrUb ⟨kInner, by omega⟩})) := by
  unfold inner18TurnDyn
  exact disjoint_supportInner18TurnGenDyn (Inner18HadWSuperLegsC.HotDNegCirc.hot68 Var) qrom
    mag1 mag2 π128 rMain rScrUb hk hk1 hMainScr v
attribute [irreducible] inner18TurnDyn
theorem cleanUnloadsWp_prepend_cleanRealizesSet_inv {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} {v : Var} {S₀ S : Finset (Wire N)} (hSub : S₀ ⊆ S) {U₁ U₂ : Unitary (2 ^ N)}
    {P₁ P₂ : DynamicCircuit Var N} (h₁ : SelectSwapQROM.CleanRealizesSet v S₀ U₁⁻¹ P₁)
    (h₂ : CleanUnloadsWp v S U₂ P₂) (hPres : AliasPrep.PreservesWires (U₁ * U₂).1 S₀) :
    CleanUnloadsWp v S (U₁ * U₂) (.seq P₁ P₂) := by
  refine ⟨by simp only [DynamicCircuit.count, h₁.1, h₂.1],
    fun Θ hΘ σ val ↦ h₁.2.1 (wp P₂.compile Θ) (h₂.2.1 Θ hΘ) σ val, fun Θ hΘ ↦ ?_⟩
  let Ψ := wp P₂.compile Θ
  have hΨ := h₂.2.1 Θ hΘ
  let Z₀ := SelectSwapQROM.zeroProjOn S₀
  let Z := SelectSwapQROM.zeroProjOn S
  have hZ0H : Z₀ᴴ = Z₀ := SelectSwapQROM.zeroProjOn_conjTranspose S₀
  have hZZ' : Z * Z₀ = Z := by
    dsimp only [Z, Z₀]
    rw [SelectSwapQROM.zeroProjOn_comm S S₀, SelectSwapQROM.zeroProjOn_mul_union,
      Finset.union_eq_right.mpr hSub]
  have hComm : Z₀ * (U₁ * U₂).1 = (U₁ * U₂).1 * Z₀ :=
    (AliasPrep.preservesWires_comm_zeroProjOn hPres Finset.Subset.rfl).symm
  have hCommH : (U₁ * U₂).1ᴴ * Z₀ = Z₀ * (U₁ * U₂).1ᴴ := by
    have h := congrArg (·ᴴ) hComm
    rwa [conjTranspose_mul, conjTranspose_mul, hZ0H] at h
  have hAbs : (Z * (U₁ * U₂).1ᴴ) * Z₀ = Z * (U₁ * U₂).1ᴴ := by
    rw [Matrix.mul_assoc, hCommH, ← Matrix.mul_assoc, hZZ']
  have hUinvH : (U₁⁻¹ : Unitary (2 ^ N)).1ᴴ = U₁.1 := by
    change (star U₁ : Unitary (2 ^ N)).1ᴴ = U₁.1
    rw [coe_star, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hCancel : (Z * (U₁ * U₂).1ᴴ) * (Z₀ * U₁.1) = Z * U₂.1ᴴ :=
    calc (Z * (U₁ * U₂).1ᴴ) * (Z₀ * U₁.1)
        = ((Z * (U₁ * U₂).1ᴴ) * Z₀) * U₁.1 := (Matrix.mul_assoc _ _ _).symm
      _ = Z * (U₂.1ᴴ * (U₁.1ᴴ * U₁.1)) := by
            rw [hAbs, Submonoid.coe_mul, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Z * U₂.1ᴴ := by
            rw [← Matrix.star_eq_conjTranspose U₁.1, U₁.prop.1, mul_one]
  have hStep : SelectSwapQROM.restrictZeroSet (qcWpQAssign (U₁ * U₂) (wp P₁.compile Ψ)) S =
      SelectSwapQROM.restrictZeroSet (qcWpQAssign U₂ Ψ) S := by
    funext σ
    apply Subtype.ext
    have hv := congrArg Subtype.val (congrFun (h₁.2.2.1 Ψ hΨ) σ)
    rw [SelectSwapQROM.restrictZeroSet_coe, SelectSwapQROM.restrictZeroSet_coe,
      wpQAssign_conj, hUinvH] at hv
    calc (SelectSwapQROM.restrictZeroSet (qcWpQAssign (U₁ * U₂) (wp P₁.compile Ψ)) S σ).1
        = ((wp P₁.compile Ψ σ).1).conj ((Z * (U₁ * U₂).1ᴴ) * Z₀) := by
            rw [SelectSwapQROM.restrictZeroSet_coe, wpQAssign_conj, hAbs]
      _ = (((wp P₁.compile Ψ σ).1).conj Z₀).conj (Z * (U₁ * U₂).1ᴴ) := by rw [← conj_conj]
      _ = ((Ψ σ).1).conj ((Z * (U₁ * U₂).1ᴴ) * (Z₀ * U₁.1)) := by rw [hv, conj_conj]
      _ = (SelectSwapQROM.restrictZeroSet (qcWpQAssign U₂ Ψ) S σ).1 := by
            rw [hCancel, ← wpQAssign_conj, ← SelectSwapQROM.restrictZeroSet_coe]
  change SelectSwapQROM.restrictZeroSet (qcWpQAssign (U₁ * U₂) (wp P₁.compile Ψ)) S = _
  rw [hStep, h₂.2.2 Θ hΘ]
/-- `31`-wire `(mMidUB 18 + 7)` subregister `midInMX 18 ++ xo7InMX 18` inside `32 + kInner`. -/
def loc31Reg (kInner : ℕ) : QRegister (mMidUB 18 + 7) (32 + kInner) :=
  ((locMX kInner).compose (midInMX 18)).concat ((locMX kInner).compose (xo7InMX 18))
    (compose_disjoint_zc20 (locMX kInner) (midInMX_disjoint_xo7 18))
theorem loc31Reg_disjoint_scr (kInner : ℕ) :
    (loc31Reg kInner).DisjointWires (locScr kInner) :=
  disjointWires_concat_left _ ((locMX_disjoint_scr kInner).compose_left _)
    ((locMX_disjoint_scr kInner).compose_left _)
theorem loc31Reg_aliasOut_eq (kInner : ℕ) :
    (loc31Reg kInner).compose (midGen18AliasOutReg 7) =
      ((locMX kInner).compose (midInMX 18)).compose (midZeroPrefixReg 18 14 (by decide)) :=
  CoherentAlias.qreg_ext fun i ↦ by
    have hi : (midGen18AliasOutReg 7) i = Fin.castAdd 7 ((midZeroPrefixReg 18 14 (by decide)) i) :=
      Fin.ext (by simp [midGen18AliasOutReg, midGen18MidReg, mid18AliasOutReg, midZeroPrefixReg,
        blockZeroReg])
    rw [QRegister.compose_apply, hi]
    dsimp only [loc31Reg]
    rw [concat_apply_left]
    exact congrArg Fin.val (QRegister.compose_apply _ _ i).symm
theorem loc31Reg_embed_muxOnAct_eq (kInner : ℕ) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (uIdx : Unitary (2 ^ 5)) :
    (loc31Reg kInner).embedUnitary (muxOnAct (mMidUB 18) 7 (fun y ↦
      prepMid18FromSlice mux9AltBit (genPi128SliceFn14 keep9SliceTargetFn14 π128) uIdx
        (finOfBits 7 y))) =
    (locMX kInner).embedUnitary (muxUnitary (xo7InMX 18) (midInMX 18)
      (xo7InMX_disjoint_mid 18) (genPi128PrepMid18Of mux9AltBit keep9SliceTargetFn14
        π128 uIdx)) := by
  rw [muxOnAct_finOfBits_eq_muxUnitary (k_t := mMidUB 18) (k_c := 7)
    (genPi128PrepMid18Of mux9AltBit keep9SliceTargetFn14 π128 uIdx),
    embedUnitary_muxUnitary, embedUnitary_muxUnitary]
  dsimp only [loc31Reg]
  exact muxCongr (concat_compose_block_right _ _ _ _) (concat_compose_block_left _ _ _ _)
    _ _ fun _ ↦ rfl
/-- Local `(32 + kInner)`-wire Step-4 cold unloader (`294 + tMag` `T`, `68 ≤ kInner`, `0 D_neg`). -/
def inner18Step4ColdLocDyn {Var : Type} {tMag : ℕ} (mag : Mag30Circ2 Var tMag)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (kInner : ℕ) (hk : 68 ≤ kInner) (v : Var) :
    DynamicCircuit Var (32 + kInner) :=
  let rMX := locMX kInner
  let rScr := locScr kInner
  let r31 := loc31Reg kInner
  have h31Scr := loc31Reg_disjoint_scr kInner
  .seq (mainSpinCancel22Dyn v rMX rScr (by omega))
    (genPrepMid18InvDyn (hadWMux23Circ Var) v r31 rScr (by omega) h31Scr
      (qromW642Keep9Mid31UnloadDyn v π128 r31 rScr hk h31Scr)
      (mag.invDyn (r31.compose (midGen18Idx5Reg 7))))
@[simp] theorem countInner18Step4ColdLocDyn_toff {Var : Type} {tMag : ℕ}
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7))) (kInner : ℕ) (hk : 68 ≤ kInner)
    (v : Var) : (inner18Step4ColdLocDyn mag π128 kInner hk v).count .TOFF = 0 := by
  dsimp only [inner18Step4ColdLocDyn]
  simp only [DynamicCircuit.count, countMainSpinCancel22Dyn_toff,
    countGenPrepMid18InvDyn_toff _ _ _ _ _ _ (count_qromW642Keep9Mid31UnloadDyn_toff ..)
      (mag.count_inv_toff _)]
@[simp] theorem countInner18Step4ColdLocDyn_t {Var : Type} {tMag : ℕ}
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7))) (kInner : ℕ) (hk : 68 ≤ kInner)
    (v : Var) : (inner18Step4ColdLocDyn mag π128 kInner hk v).count .T = 294 + tMag := by
  dsimp only [inner18Step4ColdLocDyn, DynamicCircuit.count]
  rw [countMainSpinCancel22Dyn_t _ _ _ _ (locMX_disjoint_scr kInner),
    countGenPrepMid18InvDyn_t, count_qromW642Keep9Mid31UnloadDyn_t, mag.count_inv_t]
  omega
theorem cleanUnloadsWpInner18Step4ColdLocDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {tMag : ℕ} {uIdx : Unitary (2 ^ 5)} (mag : Mag30Bundle2 Var tMag uIdx)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (kInner : ℕ) (hk : 68 ≤ kInner) (v : Var) :
    CleanUnloadsWp v (locTurnCleanReg kInner).image
      ((locMX kInner).embedUnitary (inner18MX32Mux π128 uIdx))
      (inner18Step4ColdLocDyn mag.toMag30Circ2 π128 kInner hk v) := by
  let rMX := locMX kInner
  let rScr := locScr kInner
  let r31 := loc31Reg kInner
  have hMXScr := locMX_disjoint_scr kInner
  have h31Scr := loc31Reg_disjoint_scr kInner
  have hSpinInv : (rMX.embedUnitary (spinCancelMXMux 18))⁻¹ =
      rMX.embedUnitary (spinCancelMXMux 18) :=
    inv_eq_iff_mul_eq_one.mpr (by rw [← QRegister.embedUnitary_mul, spinCancelMXMux_mul_self,
      QRegister.embedUnitary_one])
  have hCr1 : SelectSwapQROM.CleanRealizesSet v rScr.image
      (rMX.embedUnitary (spinCancelMXMux 18))⁻¹
      (mainSpinCancel22Dyn v rMX rScr (by omega)) := by
    rw [hSpinInv]
    exact crSet_of (cleanRealizesMainSpinCancel22Dyn v rMX rScr (by omega) hMXScr)
  let F_cold : Fin (2 ^ (5 + 7)) → BitAssignment 14 :=
    fun addr k ↦ if keep9Pi128FlatBool π128 addr.val k then 1 else 0
  have hF_cold (rc : Fin (2 ^ 7)) (x : Fin (2 ^ 5)) :
      F_cold (CoherentAlias.combineAddr x rc) =
        genPi128SliceFn14 keep9SliceTargetFn14 π128 rc x := by
    funext k
    dsimp only [F_cold, genPi128SliceFn14, keep9SliceTargetFn14]
    rw [keep9Pi128FlatBool_combineAddr]
    rfl
  have hQr := cleanUnloadsSet_qromW642Keep9Mid31UnloadDyn v π128 r31 rScr hk h31Scr
  dsimp only [mid31Qrom26Reg, mid31AliasOutReg] at hQr
  have hUn2 := cleanUnloadsWpGenPrepMid18InvDyn (hadWMux23Bundle Var) v (QRegister.whole 7)
    F_cold r31 rScr (by omega) h31Scr uIdx _ hQr
    (mag.clean_inv v (r31.compose (midGen18Idx5Reg 7)) rScr (h31Scr.compose_left _))
    (mux31_eq mux9AltBit uIdx _ F_cold hF_cold)
  have hImgEq : rScr.image ∪ (r31.compose (midGen18AliasOutReg 7)).image =
      (locTurnCleanReg kInner).image := by
    rw [loc31Reg_aliasOut_eq, imageLocTurnCleanReg]
  rw [hImgEq, loc31Reg_embed_muxOnAct_eq] at hUn2
  have hSub : rScr.image ⊆ (locTurnCleanReg kInner).image := by
    rw [← hImgEq]
    exact Finset.subset_union_left
  have hAll := cleanUnloadsWp_prepend_cleanRealizesSet_inv hSub hCr1 hUn2
    (by rw [← QRegister.embedUnitary_mul]
        exact AliasPrep.preservesWires_embedMatrix_of_disjoint rMX _ _
          (SelectSwapQROM.disjoint_image_of_disjointWires hMXScr))
  rwa [← QRegister.embedUnitary_mul] at hAll
attribute [irreducible] inner18Step4ColdLocDyn
/-- Ambient `N`-wire Step-4 cold walk unloader (`294 + tMag` `T`, `68 ≤ kInner`, `0 D_neg`). -/
def inner18Step4ColdDyn {Var : Type} {tMag N wOuter sUb : ℕ} (mag : Mag30Circ2 Var tMag)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : 68 ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) : DynamicCircuit Var N :=
  (inner18Step4ColdLocDyn mag π128 kInner hk v).onRegister (workPlace rUB rScrUb kInner hUb hDisj)
@[simp] theorem countInner18Step4ColdDyn_toff {Var : Type} {tMag N wOuter sUb : ℕ}
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (rUB : QRegister (nUB wOuter 18) N) (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : 68 ≤ kInner)
    (hUb : kInner ≤ sUb) (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    (inner18Step4ColdDyn mag π128 rUB rScrUb kInner hk hUb hDisj v).count .TOFF = 0 := by
  dsimp only [inner18Step4ColdDyn]
  rw [DynamicCircuit.count_onRegister, countInner18Step4ColdLocDyn_toff]
@[simp] theorem countInner18Step4ColdDyn_t {Var : Type} {tMag N wOuter sUb : ℕ}
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (rUB : QRegister (nUB wOuter 18) N) (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : 68 ≤ kInner)
    (hUb : kInner ≤ sUb) (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    (inner18Step4ColdDyn mag π128 rUB rScrUb kInner hk hUb hDisj v).count .T = 294 + tMag := by
  dsimp only [inner18Step4ColdDyn]
  rw [DynamicCircuit.count_onRegister, countInner18Step4ColdLocDyn_t]
theorem cleanUnloadsWpInner18Step4ColdDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {tMag N wOuter sUb : ℕ} {uIdx : Unitary (2 ^ 5)} (mag : Mag30Bundle2 Var tMag uIdx)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : 68 ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    CleanUnloadsWp v
      (rScrUb.image ∪
        ((rUB.compose (rMidUB wOuter 18)).compose (midZeroPrefixReg 18 14 (by decide))).image)
      (rUB.embedUnitary (inner18Mfwd wOuter π128 uIdx))
      (inner18Step4ColdDyn mag.toMag30Circ2 π128 rUB rScrUb kInner hk hUb hDisj v) := by
  have hOn := cleanUnloadsWp_onRegister v (workPlace rUB rScrUb kInner hUb hDisj)
    (locTurnCleanReg kInner) (workPlace_turnClean_subset rUB rScrUb hUb hDisj) _ _
    (cleanUnloadsWpInner18Step4ColdLocDyn mag π128 kInner hk v)
  rwa [← QRegister.embedUnitary_compose, workPlace_compose_locMX, embedInner18MX32Mux_ofUB]
    at hOn
theorem disjoint_supportInner18Step4ColdDyn {Var : Type} {tMag N wOuter sUb kInner : ℕ}
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (rMain : QRegister (nUB wOuter 18 + 11) N) (rScrUb : QRegister sUb N) (hk : 68 ≤ kInner)
    (hk1 : 1 + kInner ≤ sUb) (hMainScr : rMain.DisjointWires rScrUb) (v : Var) :
    Disjoint (inner18Step4ColdDyn mag π128 (rMain.compose (rUBInCat wOuter 18 11)) rScrUb kInner hk
        (by omega) (hMainScr.compose_left _) v).support
      ((((rMain.compose (rSysCatUB wOuter 18 11)).compose
        (QRegister.block 0 (2 * 58) (by decide))).image ∪ {rScrUb ⟨kInner, by omega⟩})) := by
  unfold inner18Step4ColdDyn
  exact disjoint_support_onRegisterWorkPlace rMain rScrUb hk1 hMainScr _
attribute [irreducible] inner18Step4ColdDyn
/-! ## Section 6: Fine-Gear Low-Scratch (`120` Scratch, `0 rHot128`) Walk Legs -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegs
end
