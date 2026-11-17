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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellSelectD11CoreB
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145Select24
/-! # Computable `d ≤ 11` (`148`-Inner / `149`-Bell Scratch) Core & `57`-AND Walk Wrappers
Refs: Berry (`10.22331/q-2019-12-02-208`), Lee (`10.1103/PRXQuantum.2.030305`),
Low (`10.1103/PhysRevX.15.041016`). -/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix HermitianMat Real CoherentAlias CleanDyn AliasPrep
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 TwoGearBox CircuitModular GivensOps BlockEncodingCore
  BlockEncodingCircuit SelectSwapQROM GivensCascade
  SelectRouter10 TopIntegrationBridge Lac2Fused184Select
  Lac2Fused184SelectWrap Router10Lac2Select Phase2MidSandwich MidReflCtxRetain OneHotSimulates
  PolymorphicFused184Select Lac2ZeroPar183Select CompactFoldedSelect ReordOuter13Bridge
  StepEncK StepDecK CompactStepFast175Core CompactOuter9Bound50Core
  CompactOuter9Bound50Select Balanced160Select Pi145SOSPermBridge LowBitPi145Select
  BellPhaseASelect BellSingletCSwap58 Cat11CompactPhase2Bridge PhaseB154Pi145Select
  TwoGearQPEPhase5 CompactTuned162StepWalk CompactTuned162StepZeroCmp20
  CompactZeroCmp20OuterParam DihedralWalkQPE DihedralWalkQPE.MultiGearQPE BellRouter57
  BellRouter57Pure NoNegSelect57Pure CompactCore145Bundle BellPersistNoNeg BellSelectNoNegPair
  Select57Slices BellPersistCore BellPersistSuperWalk BellSuperNoNegWalk BellAsymCore
  ThreeGearBellSuper BellSuperLegSplice
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast176Select
  hiding blockRemWidth
  outRemWidth midRemWidth combARem
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk (
  ubCustomMuxCatUnitary)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensCascade (
  compose_disjointWires_right)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace PhaseBD11CompactCore
open LowBitPi145Select NoNegSelect57Pure
/-- Canonical `227`-wire (`mCanCore 11`, `148`-inner-scratch) reflection core (`16,786 T`). -/
def compactCanCore11UnitDyn (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool → Fin 319)
  (negMask : Fin 145 → Bool) : DynamicCircuit Unit (mCanCore 11) := .seq (trimDyn (mCanCore 11) 11
  (dEnc145Dyn () extCanLayout11)) (.seq (.circuit (trimCircuit (mCanCore 11) 11
  (compactExtPre11Circuit actFlipMask negMask))) (.seq (compactCascadeCan11Dyn orbitalOf) (.seq
  (.circuit (trimCircuit (mCanCore 11) 11 (compactExtPost11Circuit actFlipMask))) (trimDyn (mCanCore
  11) 11 (dDec145Dyn () extCanLayout11)))))
/-- Extended `(mCanCore 11 + 11)`-wire core matching `compactCanCore11UnitDyn.onRegister`. -/
def compactExtCore11Dyn (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool → Fin 319)
    (negMask : Fin 145 → Bool) : DynamicCircuit Unit (mCanCore 11 + 11) :=
  let L := extCanLayout11
  .seq (dEnc145Dyn () L) (.seq (.circuit (compactExtPre11Circuit actFlipMask negMask)) (.seq
    ((compactCascadeCan11Dyn orbitalOf).onRegister (trimLeftReg (mCanCore 11) 11)) (.seq (.circuit
    (compactExtPost11Circuit actFlipMask)) (dDec145Dyn () L))))
theorem onRegister_trimLeftReg_compactCanCore11UnitDyn (actFlipMask : Fin 145 → Bool) (orbitalOf :
    Fin 145 → Bool → Fin 319) (negMask : Fin 145 → Bool) : (compactCanCore11UnitDyn actFlipMask
    orbitalOf negMask).onRegister (trimLeftReg (mCanCore 11) 11) = compactExtCore11Dyn actFlipMask
    orbitalOf negMask := by
  obtain ⟨h1, h2, h3, h4⟩ := inLeft_compactExtGlue11 actFlipMask negMask
  simp only [compactCanCore11UnitDyn, compactExtCore11Dyn, DynamicCircuit.onRegister_seq,
    DynamicCircuit.onRegister_circuit, onRegister_trimLeftReg_trimDyn _ _ _ h1,
    onRegister_trimLeftReg_trimCircuit _ _ _ h2, onRegister_trimLeftReg_trimCircuit _ _ _ h3,
    onRegister_trimLeftReg_trimDyn _ _ _ h4]
attribute [irreducible] compactCanCore11UnitDyn
theorem count_compactCanCore11UnitDyn_toff (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 →
    Bool
    → Fin 319) (negMask : Fin 145 → Bool) : (compactCanCore11UnitDyn actFlipMask orbitalOf
    negMask).count .TOFF = 0 := by
  rw [← DynamicCircuit.count_onRegister .TOFF (trimLeftReg (mCanCore 11) 11),
    onRegister_trimLeftReg_compactCanCore11UnitDyn, compactExtCore11Dyn, compactExtPre11Circuit,
    compactExtPost11Circuit, compactCascadeCan11Dyn]
  have hX : (Circuit.X extCanLayout11.wOne).count .TOFF = 0 := rfl
  simp only [DynamicCircuit.count, DynamicCircuit.count_onRegister, Circuit.count_seq,
    count_dEnc145Dyn_toff, count_dDec145Dyn_toff, count_flipAct145Circuit_toff,
    count_zMaskAct145Circuit_toff, Lac2Fused184Select.count_fanoutActIdxCircuit_toff,
    count_topZeroLac2CascadeCtrl11Dyn_toff, hX]
theorem count_compactCanCore11UnitDyn_t (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool →
    Fin 319) (negMask : Fin 145 → Bool) : (compactCanCore11UnitDyn actFlipMask orbitalOf
    negMask).count .T = compactCoreTCount 11 := by
  rw [← DynamicCircuit.count_onRegister .T (trimLeftReg (mCanCore 11) 11),
    onRegister_trimLeftReg_compactCanCore11UnitDyn, compactExtCore11Dyn, compactExtPre11Circuit,
    compactExtPost11Circuit, compactCascadeCan11Dyn, compactCoreTCount]
  have hX : (Circuit.X extCanLayout11.wOne).count .T = 0 := rfl
  simp only [DynamicCircuit.count, DynamicCircuit.count_onRegister, Circuit.count_seq,
    count_dEnc145Dyn_t, count_dDec145Dyn_t, count_flipAct145Circuit_t, count_zMaskAct145Circuit_t,
    Lac2Fused184Select.count_fanoutActIdxCircuit_t, count_topZeroLac2CascadeCtrl11Dyn_t, hX]
theorem diagProjSimulates_compactExtCore11Dyn (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 →
    Bool → Fin 319) (negMask : Fin 145 → Bool) :
    let L := extCanLayout11
    let rSC := L.rSpin.concat L.rCat11 (OneHotMux.disj_sys_cat_of L.hsc L.hac)
    ∃ wPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)), DiagProjSimulates (ketPredProj (sValid145
      L)) ((rSC.concat L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)).embedUnitary
      (UnsignedGivens.muxCtrlUnitary wPhased)) (compactExtCore11Dyn actFlipMask orbitalOf negMask) ∧
        ∀ (c10 :
      Fin (2 ^ 10)) (ψ : Fin (2 ^ 58) → ℂ), (wPhased c10).1 *ᵥ prodState ψ (phaseGradientLowFactor
      11 3) = prodState ((phase2Bal145PhasedBranch actFlipMask orbitalOf negMask c10).1 *ᵥ ψ)
      (phaseGradientLowFactor 11 3) := by
  intro L rSC
  have : NeZero (2 ^ (mCanCore 11)) := ⟨(Nat.two_pow_pos _).ne'⟩
  have : NeZero (2 ^ (mCanCore 11 + 11)) := ⟨(Nat.two_pow_pos _).ne'⟩
  let hlt := extCanLayout11_lt
  let rSpinC := projReg L.rSpin hlt.1
  let rTailC := projReg L.rCtrlTail146 hlt.2.1
  let rCatC := projReg L.rCat11 hlt.2.2.1
  let wHot0C : Wire (mCanCore 11) := ⟨(L.wHot0).val, hlt.2.2.2.1⟩
  let rWorkC := projReg (L.rGivens22.slice 0 11 (by decide)) hlt.2.2.2.2
  let hscC := extCan11_hsc
  let hacC := extCan11_hac
  let hWork0C := extCan11_hWork0
  let hdisjPlusC := extCan11_hdisjPlus
  obtain ⟨wAff, hSimCan, hcatAff⟩ := diagProjSimulates_topZeroLac2CascadeCtrl11Dyn
    () OneHotMux.h58_gt_1
    (p450Bal145OrbitalTable orbitalOf) rSpinC rTailC hscC actIdx146 selHot144 subIdx146 wHot0C rCatC
    rWorkC le_rfl hacC hWork0C hdisjPlusC
  rw [← compactCascadeCan11Dyn] at hSimCan
  let rCan := rSpinC.concat rCatC (OneHotMux.disj_sys_cat_of hscC hacC)
  let rActCan := rCan.concat rTailC (OneHotMux.disj_sysCat_ctrl_of hscC hacC)
  let sCan (γ : BitAssignment (mCanCore 11)) : Prop := (∃ g₀ : Fin (144 + 1),
    UnsignedGivens.IsOneHotBits g₀
    (Fin.cases (γ wHot0C) (fun g ↦ γ ((rTailC.compose selHot144) g)))) ∧ ∀ j : Fin 11, γ (rWorkC j)
    = 0
  have hSimPush := diagProjSimulates_onRegister (trimLeftReg (mCanCore 11) 11) sCan
    (rActCan.embedUnitary (UnsignedGivens.muxCtrlUnitary wAff)) (compactCascadeCan11Dyn orbitalOf)
      hSimCan
  let uAff : Unitary (2 ^ (mCanCore 11 + 11)) := (rSC.concat L.rCtrlTail146
    (OneHotMux.disj_sysCat_ctrl_of L.hSpinTail146 L.hSpinTail146Cat)).embedUnitary
      (UnsignedGivens.muxCtrlUnitary
    wAff)
  have huAffEq : (trimLeftReg (mCanCore 11) 11).embedUnitary (rActCan.embedUnitary
      (UnsignedGivens.muxCtrlUnitary wAff)) = uAff := by
    dsimp only [uAff]
    rw [← QRegister.embedUnitary_compose]
    refine congrArg (fun r ↦ r.embedUnitary (UnsignedGivens.muxCtrlUnitary wAff))
      (CoherentAlias.qreg_ext ?_)
    dsimp only [rActCan, rCan, rSC, rSpinC, rTailC, rCatC, L]
    decide +kernel
  rw [huAffEq] at hSimPush
  let wPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)) := fun c10 ↦
    let cF := flipActCtrl10_145 actFlipMask c10
    (if ctrl10RawPhase145 negMask cF then negOneUnitary (58 + 11) else 1) * wAff
      (ctrl10ToTail146Idx cF)
  let uPhased : Unitary (2 ^ (mCanCore 11 + 11)) := (rSC.concat L.rCtrl10
    (OneHotMux.disj_sysCat_ctrl_of
    L.hsc L.hac)).embedUnitary (UnsignedGivens.muxCtrlUnitary wPhased)
  have hcFanEq : Lac2Fused184Select.fanoutActIdxCircuit 8 145 L.wOne L.rSelPair8 L.rOneHot145 (fun
      g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i) = cFan145 L := by unfold cFan145
                                                                                 rfl
  obtain ⟨cFanU, hcFanU⟩ : ∃ cFanU, (cFan145 L).eval = cFanU := ⟨_, rfl⟩
  obtain ⟨hnotC, hnotI, _, _⟩ := rSC145_not_mem L
  have hsWr (β : BitAssignment (mCanCore 11 + 11)) (l : Fin (2 ^ (58 + 11))) : sValid145 L
      (UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l)) ↔ sValid145 L β := by
    have hpLoc : UnsignedGivens.localIdx L.rSelPair8 (UnsignedGivens.writeReg β rSC (basisBits (58 +
      11) l)) =
      UnsignedGivens.localIdx L.rSelPair8 β := localIdx_congr L.rSelPair8 fun i ↦
      UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hnotC (Lac2Fused184Select.selPair10 i))
    have hi (idx : Fin 159) : UnsignedGivens.writeReg β rSC (basisBits (58 +
      11) l) (L.rInner159 idx) = β
        (L.rInner159 idx) := UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hnotI idx)
    dsimp only [sValid145]
    simp only [hpLoc, hi]
  have hCommTgt : uPhased.1 * ketPredProj (sValid145 L) = ketPredProj (sValid145 L) * uPhased.1 :=
    embed_muxCtrl_comm_ketPredProj rSC L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac) wPhased
    (sValid145 L) hsWr
  refine ⟨wPhased, SubspaceStepU.toDiagProjSimulates ⟨sValid145 L, rfl⟩ hCommTgt ?_, fun c10 ψ ↦ ?_⟩
  · let R_enc := ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (encAssign145 L β))
    let βFOf (β : BitAssignment (mCanCore 11 + 11)) := flipAct145Assign actFlipMask L β
    let β₂Of (β : BitAssignment (mCanCore 11 + 11)) := Lac2Fused184Select.fanoutActIdxAssign 8 145
      L.wOne L.rSelPair8 L.rOneHot145 (Function.update (encAssign145 L (βFOf β)) L.wOne 1)
    let phOf (β : BitAssignment (mCanCore 11 + 11)) : ℂ := if ctrl10RawPhase145 negMask
      (UnsignedGivens.localIdx L.rCtrl10 (βFOf β)) then -1 else 1
    let R_mid1 := ketMapOp (sValid145 L) (fun β ↦ phOf β • XMeasCircuit.ket (β₂Of β))
    have hMid1 : (compactExtPre11Circuit actFlipMask negMask).eval.1 * R_enc = R_mid1 := by
      dsimp only [compactExtPre11Circuit]
      rw [hcFanEq, mul_ketMapOp]
      refine ketMapOp_congr fun β hS ↦ ?_
      have hSF : sValid145 L (βFOf β) := (sValid145_flipAct145Assign actFlipMask L β).mpr hS
      have ho0 : encAssign145 L (βFOf β) L.wOne = 0 := by
        dsimp only [encAssign145]
        rw [Function.update_of_ne (oh145_ne_rest L _ 0).symm]
        exact rest14_zero_of_sValid hSF 0
      have hx1 : (Circuit.X L.wOne).eval.1.mulVec (XMeasCircuit.ket (encAssign145 L (βFOf β))) =
          OneHotSimulates.ket (Function.update (encAssign145 L (βFOf β)) L.wOne 1) := by
        simpa only [ho0, zero_add] using UnsignedGivens.evolve_X_ket L.wOne (encAssign145 L
          (βFOf β))
      have hf1 : cFanU.1.mulVec (OneHotSimulates.ket (Function.update (encAssign145 L
        (βFOf β)) L.wOne
          1)) = XMeasCircuit.ket (β₂Of β) := by
        rw [← hcFanU]
        exact ket_cFan145 L _
      rw [StepEncK.eval_seq_mulVec, StepEncK.eval_seq_mulVec,
        StepEncK.eval_seq_mulVec, hcFanU, flipAct145Circuit_enc_ket actFlipMask L hS, hx1,
        zMask145_enc_ket negMask L hSF, Matrix.mulVec_smul, hf1]
    let sPush (β : BitAssignment (mCanCore 11 + 11)) : Prop := sCan fun u ↦ β (trimLeftReg _ _ u)
    have hCascClean : ketPredProj sPush * R_mid1 = R_mid1 := by
      classical
      rw [mul_ketMapOp]
      refine ketMapOp_congr fun β hS ↦ ?_
      have hSF : sValid145 L (βFOf β) := (sValid145_flipAct145Assign actFlipMask L β).mpr hS
      obtain ⟨⟨g₀, hoh⟩, hgiv0⟩ := fanout_enc_sCascValid145 L hSF
      have hs2 : sPush (β₂Of β) := by
        dsimp only [sPush, sCan]
        refine ⟨⟨g₀, Eq.mp (congrArg (UnsignedGivens.IsOneHotBits g₀) ?_) hoh⟩, fun j ↦ ?_⟩
        · funext k
          cases k using Fin.cases with
          | zero => exact congrArg (β₂Of β) (Fin.ext rfl)
          | succ g => exact congrArg (β₂Of β) (Fin.ext rfl)
        · have := j.isLt
          have hjw : trimLeftReg (mCanCore 11) 11 (rWorkC j) =
              L.rGivens22 ⟨0 + j.val, by omega⟩ := Fin.ext rfl
          rw [hjw]
          exact hgiv0 ⟨0 + j.val, by omega⟩
      have hket2 : XMeasCircuit.ket (β₂Of β) = OneHotSimulates.ket (β₂Of β) := rfl
      rw [Matrix.mulVec_smul, hket2, ketPredProj_mulVec_ket, ite_posE hs2, ← hket2]
    have hFanSq : cFanU.1 * cFanU.1 = 1 := by rw [← hcFanU]
                                              exact cFan145_eval_mul_self L
    have hMid3 : (compactExtPost11Circuit actFlipMask).eval.1 * (uAff.1 * R_mid1) = R_enc *
      uPhased.1
        := by
      dsimp only [compactExtPost11Circuit]
      rw [hcFanEq]
      classical
      refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ketMapOp_mulVec_ket]
      by_cases hS : sValid145 L β
      · rw [ite_posE hS]
        have hSF : sValid145 L (βFOf β) := (sValid145_flipAct145Assign actFlipMask L β).mpr hS
        have hLocSC := (writeReg_fanout145_comm actFlipMask L β 0).1
        have hket2 : XMeasCircuit.ket (β₂Of β) = UnsignedGivens.ket (β₂Of β) := rfl
        have hket0 : XMeasCircuit.ket β = UnsignedGivens.ket β := rfl
        have hCtrlEq := localIdx_ctrl10_flipAct145Assign actFlipMask L β
        rw [Matrix.mulVec_smul, hket2, UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket,
          localIdx_tail146_fanout L hSF, hCtrlEq, QRegister.embedUnitary_val,
          UnsignedGivens.embedMatrix_mulVec_ket, hLocSC, Finset.smul_sum, Matrix.mulVec_sum]
        have hrhs : uPhased.1.mulVec (XMeasCircuit.ket β) = ∑ l : Fin (2 ^ (58 + 11)),
          phOf β • ((wAff
            (ctrl10ToTail146Idx (flipActCtrl10_145 actFlipMask (UnsignedGivens.localIdx L.rCtrl10
              β)))).1 l
            (UnsignedGivens.localIdx rSC β) • UnsignedGivens.ket (UnsignedGivens.writeReg β rSC
              (basisBits (58 + 11) l))) := by
          rw [hket0, UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket]
          dsimp only [wPhased, phOf]
          rw [hCtrlEq]
          by_cases hph : ctrl10RawPhase145 negMask (flipActCtrl10_145 actFlipMask
            (UnsignedGivens.localIdx
              L.rCtrl10 β)) = true
          · simp only [hph, ↓reduceIte, QRegister.embedUnitary_val, Submonoid.coe_mul,
              negOneUnitary_val, Matrix.smul_mul, Matrix.one_mul, rSC.embedMatrix_smul,
              Matrix.smul_mulVec, UnsignedGivens.embedMatrix_mulVec_ket, Finset.smul_sum]
          · simp only [hph, Bool.false_eq_true, ↓reduceIte, one_mul, one_smul,
              QRegister.embedUnitary_val, UnsignedGivens.embedMatrix_mulVec_ket]
        rw [hrhs, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
        refine congrArg (phOf β • ·) (congrArg (_ • ·) ?_)
        let γL := UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l)
        have hSγ : sValid145 L γL := (hsWr β l).mpr hS
        have hSFγ : sValid145 L (βFOf γL) := (sValid145_flipAct145Assign actFlipMask L γL).mpr hSγ
        have hfanBack : cFanU.1.mulVec (OneHotSimulates.ket (β₂Of γL)) = OneHotSimulates.ket
            (Function.update (encAssign145 L (βFOf γL)) L.wOne 1) := by
          have hf1 : cFanU.1.mulVec (OneHotSimulates.ket (Function.update (encAssign145 L (βFOf γL))
              L.wOne 1)) = OneHotSimulates.ket (β₂Of γL) := by
            rw [← hcFanU]
            exact ket_cFan145 L _
          rw [← hf1, Matrix.mulVec_mulVec, hFanSq, Matrix.one_mulVec]
        have ho0γ : encAssign145 L (βFOf γL) L.wOne = 0 := by
          dsimp only [encAssign145]
          rw [Function.update_of_ne (oh145_ne_rest L _ 0).symm]
          exact rest14_zero_of_sValid hSFγ 0
        have hclr1 : Function.update (Function.update (encAssign145 L (βFOf γL)) L.wOne 1) L.wOne
            (Function.update (encAssign145 L (βFOf γL)) L.wOne 1 L.wOne + 1) = encAssign145 L (βFOf
            γL) := by rw [Function.update_self, Function.update_idem]
                      exact Function.update_eq_self_iff.mpr ho0γ.symm
        have hxBack : (Circuit.X L.wOne).eval.1.mulVec (OneHotSimulates.ket (Function.update
            (encAssign145 L (βFOf γL)) L.wOne 1)) = XMeasCircuit.ket (encAssign145 L
              (βFOf γL)) := by
          simpa only [hclr1] using UnsignedGivens.evolve_X_ket L.wOne (Function.update (encAssign145
            L (βFOf
            γL)) L.wOne 1)
        have hflBack : (flipAct145Circuit actFlipMask L).eval.1.mulVec (XMeasCircuit.ket
          (encAssign145
            L (βFOf γL))) = XMeasCircuit.ket (encAssign145 L γL) := by
          rw [flipAct145Circuit_enc_ket actFlipMask L hSFγ]
          dsimp only [βFOf]
          rw [flipAct145Assign_involutive]
        have hketEq : UnsignedGivens.ket (β₂Of γL) = OneHotSimulates.ket (β₂Of γL) := rfl
        have hketγ : UnsignedGivens.ket γL = XMeasCircuit.ket γL := rfl
        rw [(writeReg_fanout145_comm actFlipMask L β l).2, hketEq, hketγ, ketMapOp_mulVec_ket,
          ite_posE hSγ, StepEncK.eval_seq_mulVec, StepEncK.eval_seq_mulVec, hcFanU,
          hfanBack, hxBack, hflBack]
      · have hket0 : XMeasCircuit.ket β = UnsignedGivens.ket β := rfl
        rw [ite_negE hS, Matrix.mulVec_zero, Matrix.mulVec_zero, hket0,
          UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket, QRegister.embedUnitary_val,
          UnsignedGivens.embedMatrix_mulVec_ket, Matrix.mulVec_sum]
        symm
        refine Finset.sum_eq_zero fun l _ ↦ ?_
        have hketL : UnsignedGivens.ket (UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l)) =
          XMeasCircuit.ket
            (UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l)) := rfl
        rw [Matrix.mulVec_smul, hketL, ketMapOp_mulVec_ket, ite_negE (mt (hsWr β l).mp hS),
          smul_zero]
    have hDecR := SubspaceStepU.congr rfl hCommTgt.symm (SubspaceStepU.mul_right uPhased.1
      (dDec145Dyn_step () L))
    dsimp only [compactExtCore11Dyn]
    exact SubspaceStepU.seq (dEnc145Dyn_step () L) (SubspaceStepU.seq (SubspaceStepU.of_circuit
      (Var := Unit) _ hMid1) (SubspaceStepU.seq (SubspaceStepU.of_diagProjSimulates hSimPush
      hCascClean) (SubspaceStepU.seq (SubspaceStepU.of_circuit (Var := Unit) _ hMid3) hDecR)))
  · dsimp only [wPhased, phase2Bal145PhasedBranch, phase2Bal145RawPhasedBranch]
    let cF := flipActCtrl10_145 actFlipMask c10
    have hpg : phaseGradientLowFactor 11 3 = phaseGradientFineLow 11 3 := rfl
    by_cases hph : ctrl10RawPhase145 negMask cF = true
    · simp only [cF, hph, ↓reduceIte, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hpg, hcatAff, affCascadeBranch_bal145_ctrl10ToTail146Idx, negOneUnitary_val,
        Matrix.smul_mulVec, Matrix.one_mulVec, negOneUnitary_val, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      funext G
      simp [prodState, CircuitModular.prodStateOf]
    · simp only [cF, hph, Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [hpg, hcatAff, affCascadeBranch_bal145_ctrl10ToTail146Idx]
attribute [local irreducible] compactCascadeCan11Dyn compactExtPre11Circuit compactExtPost11Circuit
attribute [irreducible] compactExtCore11Dyn
/-- Relocated `148`-inner-scratch (`d = 11`) reflection core for arbitrary `Core145Layout`. -/
def compactStepCore11UnitDyn (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool → Fin 319)
  (negMask : Fin 145 → Bool) {n : ℕ} (L : Core145Layout (159 - 11) n) : DynamicCircuit Unit n :=
  (compactCanCore11UnitDyn actFlipMask orbitalOf negMask).onRegister L.rFull
/-- Table-parametric `148`-inner-scratch (`d = 11`) `Core145Bundle` (`16,786 T`, `0 TOFF`). -/
def compactParamCore11Bundle (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin 145 → Bool → Fin 319)
    (negMask : Fin 145 → Bool) : Core145Bundle (159 - 11) (compactCoreTCount 11) actFlipMask
      orbitalOf
    negMask where
  hk6 := by decide
  coreUnitDyn := compactStepCore11UnitDyn actFlipMask orbitalOf negMask
  count_toff _ := by rw [compactStepCore11UnitDyn, DynamicCircuit.count_onRegister,
                       count_compactCanCore11UnitDyn_toff]
  count_t _ := by
    rw [compactStepCore11UnitDyn, DynamicCircuit.count_onRegister, count_compactCanCore11UnitDyn_t]
  simCore {n} L := by
    have : NeZero (2 ^ n) := ⟨(Nat.two_pow_pos n).ne'⟩
    have : NeZero (2 ^ (mCanCore 11)) := ⟨(Nat.two_pow_pos _).ne'⟩
    have : NeZero (2 ^ (mCanCore 11 + 11)) := ⟨(Nat.two_pow_pos _).ne'⟩
    let C := canCoreLayout 11
    let L_ext := extCanLayout11
    have hm : mCanCore 11 = 227 := rfl
    obtain ⟨wPhased, hSimExt, hBr⟩ := diagProjSimulates_compactExtCore11Dyn actFlipMask orbitalOf
      negMask
    rw [← onRegister_trimLeftReg_compactCanCore11UnitDyn] at hSimExt
    let rC_3 := C.rSpin.concat C.rCat11 (OneHotMux.disj_sys_cat_of C.hsc C.hac)
    let rActC := rC_3.concat C.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of C.hsc C.hac)
    let uCan := rActC.embedUnitary (UnsignedGivens.muxCtrlUnitary wPhased)
    have huExtEq : (trimLeftReg (mCanCore 11) 11).embedUnitary uCan = ((L_ext.rSpin.concat
        L_ext.rCat11 (OneHotMux.disj_sys_cat_of L_ext.hsc L_ext.hac)).concat L_ext.rCtrl10
        (OneHotMux.disj_sysCat_ctrl_of L_ext.hsc L_ext.hac)).embedUnitary
          (UnsignedGivens.muxCtrlUnitary wPhased)
        := by
      dsimp only [uCan]
      rw [← QRegister.embedUnitary_compose]
      refine congrArg (fun r ↦ r.embedUnitary (UnsignedGivens.muxCtrlUnitary wPhased))
        (CoherentAlias.qreg_ext ?_)
      dsimp only [rActC, rC_3, C, L_ext]
      decide +kernel
    rw [← huExtEq] at hSimExt
    have hCommCan : uCan.1 * ketPredProj (sValidCore C) = ketPredProj (sValidCore C) * uCan.1 := by
      refine embed_muxCtrl_comm_ketPredProj rC_3 C.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of C.hsc
        C.hac)
        wPhased (sValidCore C) fun β l ↦ ?_
      have hnSC_C (u : Fin 10) : C.rCtrl10 u ∉ Set.range rC_3.wires := fun ⟨sc, hsc⟩ ↦
        QRegister.disjoint_iff.mp (OneHotMux.disj_sysCat_ctrl_of C.hsc C.hac) sc u hsc
      have hnSC_I (idx : Fin (159 - 11)) : C.rInner idx ∉ Set.range rC_3.wires :=
        fun ⟨sc, hsc⟩ ↦ (show ∀ s i, rC_3 s ≠ C.rInner i by decide +kernel) sc idx hsc
      have hpLoc : UnsignedGivens.localIdx C.rSelPair8 (UnsignedGivens.writeReg β rC_3 (basisBits
        (58 + 11) l)) =
        UnsignedGivens.localIdx C.rSelPair8 β := localIdx_congr C.rSelPair8 fun i ↦
        UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hnSC_C (Lac2Fused184Select.selPair10 i))
      have hi (idx : Fin (159 - 11)) : UnsignedGivens.writeReg β rC_3 (basisBits (58 +
        11) l) (C.rInner idx)
        = β (C.rInner idx) := UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hnSC_I idx)
      dsimp only [sValidCore]
      simp only [hpLoc, hi]
    have hPairW : ∀ i : Fin 8, L_ext.rSelPair8 i = trimLeftReg (mCanCore 11) 11 (C.rSelPair8 i) :=
      by decide +kernel
    have hInLo : ∀ j : Fin 3, L_ext.rInner159 ⟨j.val, by omega⟩ =
        trimLeftReg (mCanCore 11) 11 (C.rInner ⟨j.val, by omega⟩) := by decide +kernel
    have hInHi : ∀ k : Fin 145, L_ext.rInner159 ⟨k.val + 14, by omega⟩ =
        trimLeftReg (mCanCore 11) 11 (C.rInner ⟨k.val + 3, by omega⟩) := by decide +kernel
    have hInMid : ∀ m : Fin 11, mCanCore 11 ≤ (L_ext.rInner159 ⟨m.val + 3, by omega⟩).val :=
      by decide +kernel
    have hSimCan : DiagProjSimulates (ketPredProj (sValidCore C)) uCan (compactCanCore11UnitDyn
        actFlipMask orbitalOf negMask) := by
      refine diagProjSimulates_of_onRegister (trimLeftReg (mCanCore 11) 11) (sValidCore C)
        (sValid145 L_ext) uCan _ hSimExt hCommCan fun x ↦ ?_
      let g₀ := (trimLeftReg (mCanCore 11) 11).basisSplitEquiv.symm (x, 0)
      have hleft (w : Fin (mCanCore 11)) : basisBits (mCanCore 11 + 11) g₀ (trimLeftReg (mCanCore
          11) 11 w) = basisBits (mCanCore 11) x w := by
        rw [← QRegister.basisBits_extractIndex, ← QRegister.basisSplitEquiv_apply_fst,
          Equiv.apply_symm_apply]
      have hright (w : Fin (mCanCore 11 + 11)) (hw : mCanCore 11 ≤ w.val) : basisBits (mCanCore 11 +
          11) g₀ w = 0 := by
        have hnot : w ∉ Set.range (trimLeftReg (mCanCore 11) 11).wires := by
          rintro ⟨u, rfl⟩
          exact Nat.not_le.mpr u.isLt hw
        have hsnd : ((trimLeftReg (mCanCore 11) 11).basisSplitEquiv g₀).2 = 0 := by simp [g₀]
        simpa only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply] using congrFun hsnd ⟨w,
          hnot⟩
      have hpEq : UnsignedGivens.localIdx L_ext.rSelPair8 (basisBits (mCanCore 11 + 11) g₀) =
        UnsignedGivens.localIdx
          C.rSelPair8 (basisBits (mCanCore 11) x) :=
        localIdx_eq_of_forall L_ext.rSelPair8 C.rSelPair8 _ _ fun i ↦ by rw [hPairW i, hleft]
      dsimp only [sValid145, sValidCore]
      rw [hpEq]
      refine and_congr_right fun _ ↦ ⟨fun hI j ↦ ?_, fun hC idx ↦ ?_⟩
      · have := j.isLt
        by_cases hj : j.val < 3
        · have h0 := hI ⟨j.val, by omega⟩
          have hw := hInLo ⟨j.val, hj⟩
          rwa [hw, hleft] at h0
        · have h0 := hI ⟨j.val + 11, by omega⟩
          have hjEq : (⟨(j.val - 3) + 3, by omega⟩ : Fin 148) = j := Fin.ext (by
            dsimp
            omega)
          have hkEq : (⟨(j.val - 3) + 14, by omega⟩ : Fin 159) = ⟨j.val + 11, by omega⟩ :=
            Fin.ext (by
              dsimp
              omega)
          have hw := hInHi ⟨j.val - 3, by omega⟩
          rw [hjEq, hkEq] at hw
          rwa [hw, hleft] at h0
      · have := idx.isLt
        by_cases h1 : idx.val < 3
        · have hiEq : (⟨idx.val, by omega⟩ : Fin 159) = idx := Fin.ext rfl
          have hw := hInLo ⟨idx.val, h1⟩
          rw [hiEq] at hw
          rw [hw, hleft]
          exact hC _
        · by_cases h2 : idx.val < 14
          · have hmEq : (⟨(idx.val - 3) + 3, by omega⟩ : Fin 159) = idx :=
              Fin.ext (by
                dsimp
                omega)
            have hm := hInMid ⟨idx.val - 3, by omega⟩
            rw [hmEq] at hm
            exact hright _ hm
          · have hkEq : (⟨(idx.val - 14) + 14, by omega⟩ : Fin 159) = idx :=
              Fin.ext (by
                dsimp
                omega)
            have hw := hInHi ⟨idx.val - 14, by omega⟩
            rw [hkEq] at hw
            rw [hw, hleft]
            exact hC _
    have hPushL := diagProjSimulates_onRegister L.rFull (sValidCore C) uCan
      (compactCanCore11UnitDyn actFlipMask orbitalOf negMask) hSimCan
    have hSEq : ketPredProj (fun β ↦ sValidCore C (fun i ↦ β (L.rFull i))) =
        ketPredProj (sValidCore L) := ketPredProj_congr fun β ↦ by
      have hp : UnsignedGivens.localIdx C.rSelPair8 (fun i ↦ β (L.rFull i)) =
        UnsignedGivens.localIdx L.rSelPair8 β :=
          by
        dsimp [UnsignedGivens.localIdx, C, canCoreLayout, Core145Layout.rSelPair8,
          Core145Layout.rCtrl10]
      dsimp only [sValidCore]
      rw [hp]
      rfl
    have hUEq : L.rFull.embedUnitary uCan = (((L.rSpin.concat L.rCat11 (OneHotMux.disj_sys_cat_of
      L.hsc
        L.hac)).concat L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)).embedUnitary
        (UnsignedGivens.muxCtrlUnitary wPhased)) := by
      dsimp only [uCan, rActC, rC_3]
      rw [← QRegister.embedUnitary_compose]
      congr 1
      refine CoherentAlias.qreg_ext fun idx ↦ Fin.addCases (fun sc ↦ ?_) (fun j ↦ ?_) idx
      · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left]
        refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) sc
        · rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
          simp [C, canCoreLayout, Core145Layout.rSpin]
        · rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
          simp [C, canCoreLayout, Core145Layout.rCat11]
      · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right]
        simp [C, canCoreLayout, Core145Layout.rCtrl10]
    rw [hSEq, hUEq] at hPushL
    exact ⟨wPhased, hPushL, hBr⟩
attribute [irreducible] compactStepCore11UnitDyn
/-- Computable reindexing of `Core145Layout` along an inner-scratch width equality `k₁ = k₂`. -/
def castCore145Layout {k₁ k₂ n : ℕ} (hk : k₁ = k₂) (L : Core145Layout k₁ n) : Core145Layout k₂ n :=
  { rFull := ⟨⟨fun i ↦ L.rFull ⟨i.val, by
        have := i.isLt
        omega⟩,
      fun _ _ h ↦ by have hv := congrArg Fin.val (L.rFull.wires.injective h)
                     exact Fin.ext hv⟩⟩ }
@[simp] theorem castCore145Layout_self {k n : ℕ} (hk : k = k) (L : Core145Layout k n) :
    castCore145Layout hk L = L := by cases L
                                     rfl
/-- Unified computable `(159 - d)`-inner-scratch reflection core (`0 ≤ d ≤ 11`). -/
def compactStepCoreD11UnitDyn (d : ℕ) (hd : d ≤ 11) (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin
  145 → Bool → Fin 319) (negMask : Fin 145 → Bool) {n : ℕ} (L : Core145Layout (159 - d) n) :
  DynamicCircuit Unit n := if h10 : d ≤ 10 then compactStepCoreUnitDyn d h10 actFlipMask orbitalOf
  negMask L else compactStepCore11UnitDyn actFlipMask orbitalOf negMask (castCore145Layout
  (by omega) L)
/-- Unified table-parametric `(159 - d)`-inner-scratch `Core145Bundle` (`0 ≤ d ≤ 11`). -/
def compactParamCoreD11Bundle (d : ℕ) (hd : d ≤ 11) (actFlipMask : Fin 145 → Bool) (orbitalOf : Fin
    145
    → Bool → Fin 319) (negMask : Fin 145 → Bool) : Core145Bundle (159 - d) (compactCoreTCount d)
    actFlipMask orbitalOf negMask where
  hk6 := by omega
  coreUnitDyn := compactStepCoreD11UnitDyn d hd actFlipMask orbitalOf negMask
  count_toff L := by
    unfold compactStepCoreD11UnitDyn
    by_cases h10 : d ≤ 10
    · rw [dite_eq_left h10]
      exact (compactParamCore145Bundle d h10 actFlipMask orbitalOf negMask).count_toff L
    · rw [dite_eq_right h10]
      exact (compactParamCore11Bundle actFlipMask orbitalOf negMask).count_toff _
  count_t L := by
    unfold compactStepCoreD11UnitDyn
    by_cases h10 : d ≤ 10
    · rw [dite_eq_left h10]
      exact (compactParamCore145Bundle d h10 actFlipMask orbitalOf negMask).count_t L
    · rw [dite_eq_right h10]
      have hd11 : d = 11 := by omega
      subst hd11
      exact (compactParamCore11Bundle actFlipMask orbitalOf negMask).count_t _
  simCore {n} L := by
    unfold compactStepCoreD11UnitDyn
    by_cases h10 : d ≤ 10
    · rw [dite_eq_left h10]
      exact (compactParamCore145Bundle d h10 actFlipMask orbitalOf negMask).simCore L
    · rw [dite_eq_right h10]
      have hd11 : d = 11 := by omega
      subst hd11
      rw [castCore145Layout_self]
      exact (compactParamCore11Bundle actFlipMask orbitalOf negMask).simCore L
attribute [irreducible] compactStepCoreD11UnitDyn
/-- Compact `(159 - d)`-inner-scratch `Core145Bundle` for `57`-AND `π145` `SiZero`
(`0 ≤ d ≤ 11`). -/
abbrev compactCoreD11Bundle (d : ℕ) (hd : d ≤ 11) (oddPass : Bool) : Core145Bundle (159 - d)
  (compactCoreTCount d) actFlip145 (orbitalOfPi14557 oddPass) (negMaskPi14557 oddPass) :=
  compactParamCoreD11Bundle d hd actFlip145 (orbitalOfPi14557 oddPass) (negMaskPi14557 oddPass)
end PhaseBD11CompactCore
namespace PhaseBD11CompactCore
open LowBitPi145Select NoNegSelect57Pure BellPersistNoNeg Select57Slices
export _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPersistNoNeg
  (cleanRealizesSet_selectLowBitNoNegCoreSliceDyn)
/-- Computable single-pass `(1 + kInner)`-scratch `wNegIn`-free `SELECT` slice (`0 < wInner2`). -/
def selectLowBitNoNegCoreCompDyn {Var : Type} {N kInner sUb : ℕ} (hk6 : 6 ≤ kInner) (core : ∀ {n :
    ℕ}, Core145Layout kInner n → DynamicCircuit Unit n) (stepsA stepsB : List (RouterStep 23)) (hs :
    1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister
      (nUB wOuter wInner2 +
    11) N) (rScrUb : QRegister sUb N) : DynamicCircuit Var N :=
  let rScr := rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
  let innerB : DynamicCircuit Unit N := if hdisj : rMain.DisjointWires rScr then
      let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
      let rRouter23 := lowBitRouter23 hk6 wOuter wInner2 wDummy rMain rScr hdisj
      let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
      let dSwap := cswapBlockDyn () 58 (rSwap117LowBit wOuter wInner2 wDummy rMain) (L.rInner
        ⟨0, by omega⟩)
      routerStepsProg () (LowBitPi145Select.liftRouterStepsN rRouter23 stepsB)
        (.seq dSwap (.seq (core L) dSwap))
    else .identity
  liftUnitVar v (if hdisj : rMain.DisjointWires rScr then
      let rRouter23 := lowBitRouter23 hk6 wOuter wInner2 ⟨0, hGiPos⟩ rMain rScr hdisj
      routerStepsProg () (LowBitPi145Select.liftRouterStepsN rRouter23 stepsA) innerB
    else .identity)
/-- Computable single-pass `(160 - d)`-scratch `wNegIn`-free `57`-AND `SELECT` slice (`d ≤ 11`). -/
def compactSelect57NoNegD11SliceDyn {Var : Type} {N sUb : ℕ} (d : ℕ) (hd : d ≤ 11) (oddPass : Bool)
  (hs : 160 - d ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister
    (nUB wOuter wInner2 +
  11) N) (rScrUb : QRegister sUb N) : DynamicCircuit Var N := selectLowBitNoNegCoreCompDyn
  (by omega) (compactStepCoreD11UnitDyn d hd actFlip145 (orbitalOfPi14557 oddPass)
  (negMaskPi14557 oddPass)) stepsA57 (stepsB57 oddPass) (by omega) v wOuter wInner2 hGiPos rMain
  rScrUb
theorem compactSelect57NoNegD11SliceDyn_eq {Var : Type} {N sUb : ℕ} (d : ℕ) (hd : d ≤ 11) (oddPass
    : Bool) (hs : 160 - d ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
      (rMain : QRegister (nUB
    wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N) : compactSelect57NoNegD11SliceDyn d hd
      oddPass hs v
    wOuter wInner2 hGiPos rMain rScrUb = selectLowBitNoNegCoreSliceDyn (compactCoreD11Bundle d hd
    oddPass).toGen stepsA57 (stepsB57 oddPass) (by omega) v wOuter wInner2 hGiPos rMain rScrUb :=
      rfl
theorem cleanRealizesSetCompactSelect57NoNegD11SliceDyn {Var : Type} [Fintype Var] [DecidableEq
  Var] {N sUb : ℕ} (d : ℕ) (hd : d ≤ 11) (oddPass : Bool) (hs : 160 - d ≤ sUb) (v : Var)
    (wOuter wInner2 :
  ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb
    N) (hdisj :
  rMain.DisjointWires rScrUb) : ∃ selectCat : Unitary (2 ^ (nUB wOuter wInner2 + 11)),
    CleanRealizesSet v
  rScrUb.image (rMain.embedUnitary selectCat) (compactSelect57NoNegD11SliceDyn d hd oddPass hs v
  wOuter wInner2 hGiPos rMain rScrUb) ∧ AliasPrep.PreservesWires (rMain.embedUnitary selectCat).1
  ((((rMain.compose (rUBInCat wOuter wInner2 11)).compose (rAllUB wOuter wInner2)).image) ∪
    rScrUb.image) ∧
  SelCatEqOuterInner wOuter wInner2 selectCat (select57NoNegPureUnitary oddPass wOuter wInner2) ∧
    SelCatEqOuterInner wOuter
  wInner2 selectCat⁻¹ (select57NoNegPureUnitary oddPass wOuter wInner2)⁻¹ ∧
    SelectCatPi145OneBodyMidCoreComm
  selectCat ∧ (∀ M : Operator (2 ^ wInner2), selectCat.1 * (rMidInnerInCat wOuter wInner2
    11).embedMatrix M =
  (rMidInnerInCat wOuter wInner2 11).embedMatrix M * selectCat.1) :=
  cleanRealizesSet_selectLowBitNoNegCoreSliceDyn (compactCoreD11Bundle d hd oddPass).toGen stepsA57
  (stepsB57 oddPass) specA57 (specB57 oddPass) runSteps24StepsA57 (fun x16 ↦
  (specA57_borrows x16).2.2 ⟨4, by decide⟩) (runSteps24StepsB57 oddPass)
  (specB57_borrows_false oddPass) (ctrl10_pair8_lt145_2 oddPass)
  (Select57Slices.y12NoNegOfState2457_indep15 oddPass)
  (Select57Slices.y12NoNegOf1557_of_ge126 oddPass) (by omega) v wOuter wInner2 hGiPos rMain rScrUb
  hdisj
/-- Computable (`{Var : Type}`) `wNegIn`-free `K`-step `57`-AND `(160 - d)`-scratch Bell-persistent
super-reflection on `combQubitsAt` (`0 < wInner2`, `0 ≤ d ≤ 11`, standard `π145` `SiZero` tables).
-/
def bellSuperNoNeg57D11CompDyn {Var : Type} (d : ℕ) (hd : d ≤ 11) (bQPE wOuter wInner2 ko km mLow
    sUb K
  : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2) (hs : 160 -
    d ≤ sUb) (hsIn :
  combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v : Var) (pOutFwd pOutBwd P_1 pTurn P_4 :
    DynamicCircuit
  Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) : DynamicCircuit Var (combQubitsAt bQPE
    wOuter
  wInner2 ko km mLow sUb) := bellSuperNoNegGen57CompDyn (by omega) bQPE wOuter wInner2 ko km mLow
    sUb K
  hkOut hkMid hGiPos (by omega) hsIn (compactStepCoreD11UnitDyn d hd actFlip145
  (orbitalOfPi14557 false) (negMaskPi14557 false)) (compactStepCoreD11UnitDyn d hd actFlip145
  (orbitalOfPi14557 true) (negMaskPi14557 true)) v pOutFwd pOutBwd P_1 pTurn P_4
theorem bellSuperNoNeg57D11CompDyn_eq {Var : Type} (d : ℕ) (hd : d ≤ 11) (bQPE wOuter wInner2 ko km
    mLow
    sUb K : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2) (hs : 160 -
      d ≤ sUb) (hsIn :
    combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v : Var) (pOutFwd pOutBwd P_1 pTurn P_4 :
    DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :
      bellSuperNoNeg57D11CompDyn
    d hd bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn
      P_4 =
    bellSuperNoNegGen57Dyn (compactCoreD11Bundle d hd false).toGen (compactCoreD11Bundle d hd
    true).toGen bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos (by omega) hsIn v pOutFwd
      pOutBwd
    P_1 pTurn P_4 := rfl
/-- Computable single-step (`K = 1`) `(160 - d)`-scratch `wNegIn`-free `57`-AND Bell reflection. -/
abbrev bellRefl2NoNeg57D11CompDyn {Var : Type} (d : ℕ) (hd : d ≤ 11) (bQPE wOuter wInner2 ko km mLow
    sUb
  : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2) (hs : 160 -
    d ≤ sUb) (hsIn :
  combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v : Var) (pOutFwd pOutBwd P_1 pTurn P_4 :
    DynamicCircuit
  Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) : DynamicCircuit Var (combQubitsAt bQPE
    wOuter
  wInner2 ko km mLow sUb) := bellSuperNoNeg57D11CompDyn d hd bQPE wOuter wInner2 ko km mLow sUb 1
    hkOut
  hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4
theorem count_bellSuperNoNeg57D11CompDyn_toff {Var : Type} (d : ℕ) (hd : d ≤ 11) (bQPE wOuter
    wInner2 ko
    km mLow sUb K : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2)
      (hs : 160 - d ≤ sUb)
    (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v : Var) {pOutFwd pOutBwd P_1 pTurn P_4 :
    DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)} (hFwd0 : pOutFwd.count
      .TOFF =
    0) (hBwd0 : pOutBwd.count .TOFF = 0) (h10 : P_1.count .TOFF = 0) (hTurn0 : pTurn.count .TOFF =
    0) (h40 : P_4.count .TOFF = 0) : (bellSuperNoNeg57D11CompDyn d hd bQPE wOuter wInner2 ko km mLow
      sUb
    K hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4).count .TOFF = 0 := by
  rw [bellSuperNoNeg57D11CompDyn_eq, bellSuperNoNegGen57Dyn]
  exact count_bellSuperNoNegGenBundleDyn_toff _ _ _ _ _ bQPE wOuter wInner2 ko km mLow sUb K hkOut
    hkMid
    hGiPos (by omega) hsIn v hFwd0 hBwd0 h10 hTurn0 h40
theorem count_bellSuperNoNeg57D11CompDyn_t {Var : Type} (d : ℕ) (hd : d ≤ 11) (bQPE wOuter wInner2
    ko km
    mLow sUb K : ℕ) (hK : 1 ≤ K) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2)
      (hs : 160
    - d ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v : Var) (pOutFwd pOutBwd P_1
      pTurn
    P_4 : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :
    (bellSuperNoNeg57D11CompDyn d hd bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs hsIn
      v
    pOutFwd pOutBwd P_1 pTurn P_4).count .T = K * (pOutFwd.count .T + P_1.count .T +
    compactBellSuperStep57TCount d + pTurn.count .T + P_4.count .T + pOutBwd.count .T) + 232 + (K -
    1) * (4 * (combARem wOuter wInner2 ko km - 2)) := by
  rw [bellSuperNoNeg57D11CompDyn_eq, bellSuperNoNegGen57Dyn, count_bellSuperNoNegGenBundleDyn_t _
    _ _ _ _ bQPE wOuter wInner2 ko km mLow sUb K hK hkOut hkMid hGiPos _ hsIn v,
      numRouterAndsStepsA57,
    numRouterAndsStepsB57, numRouterAndsStepsB57]
  have hc := compactBellSuperStep57TCount_eq_core d
  dsimp only [compactBellSuperStep57TCount, compactCoreTCount] at hc ⊢
  congr 2
  congr 1
  omega
theorem count_bellRefl2NoNeg57D11CompDyn_toff {Var : Type} (d : ℕ) (hd : d ≤ 11) (bQPE wOuter
    wInner2 ko
  km mLow sUb : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2) (hs : 160 -
    d ≤ sUb)
  (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v : Var) {pOutFwd pOutBwd P_1 pTurn P_4 :
  DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)} (hFwd0 : pOutFwd.count .TOFF
    = 0)
  (hBwd0 : pOutBwd.count .TOFF = 0) (h10 : P_1.count .TOFF = 0) (hTurn0 : pTurn.count .TOFF = 0)
  (h40 : P_4.count .TOFF = 0) : (bellRefl2NoNeg57D11CompDyn d hd bQPE wOuter wInner2 ko km mLow sUb
  hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4).count .TOFF = 0 :=
  count_bellSuperNoNeg57D11CompDyn_toff d hd bQPE wOuter wInner2 ko km mLow sUb 1 hkOut hkMid hGiPos
    hs
  hsIn v hFwd0 hBwd0 h10 hTurn0 h40
theorem count_bellRefl2NoNeg57D11CompDyn_t {Var : Type} (d : ℕ) (hd : d ≤ 11) (bQPE wOuter wInner2
    ko km
    mLow sUb : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2) (hs : 160 -
      d ≤ sUb)
    (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v : Var) (pOutFwd pOutBwd P_1 pTurn P_4 :
    DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :
    (bellRefl2NoNeg57D11CompDyn d hd bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid hGiPos hs hsIn v
    pOutFwd pOutBwd P_1 pTurn P_4).count .T = pOutFwd.count .T + P_1.count .T +
    compactBellSelect57TCount d + pTurn.count .T + P_4.count .T + pOutBwd.count .T := by
  rw [bellRefl2NoNeg57D11CompDyn, count_bellSuperNoNeg57D11CompDyn_t d hd bQPE wOuter wInner2 ko km
    mLow sUb 1 (by decide) hkOut hkMid hGiPos hs hsIn v]
  dsimp only [compactBellSuperStep57TCount, compactBellSelect57TCount]
  omega
theorem cleanWalkRefl2At_bellSuperNoNeg57D11CompDyn_asym {Var : Type} [Fintype Var]
    [DecidableEq Var] (d : ℕ) (hd : d ≤ 11) {bQPE wOuter wInner2 ko km mLow sUb : ℕ} (K : ℕ)
      (hK : 1 ≤ K)
    (hGiPos : 0 < wInner2) {hkOut : ko ≤ wOuter} {hkMid : km ≤ wInner2} (hs : 160 - d ≤ sUb)
    (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) {v : Var}
    {prepOutImpl : Unitary (2 ^ mOutUB wOuter)} {M_fwd M_bwd : Unitary (2 ^ nUB wOuter wInner2)}
    {raw_4 raw_3 sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    {pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (legs : BellAsymLegs Var bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v prepOutImpl M_fwd
      M_bwd
      raw_4 raw_3 sF sB pOutFwd pOutBwd P_1 pTurn P_4)
    (hs1 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_4)
      (compactSelect57NoNegD11SliceDyn d hd false hs v wOuter wInner2 hGiPos
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hs2 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_3)
      (compactSelect57NoNegD11SliceDyn d hd true hs v wOuter wInner2 hGiPos
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hTurnSupp : Disjoint pTurn.support
      (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb (159 - d) (by omega)))
    (hInterSupp : 2 ≤ K → Disjoint (P_1.support ∪ P_4.support ∪ pOutFwd.support ∪ pOutBwd.support)
      (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb (159 - d) (by omega))) :
    let uRefl2 := QubitisedWalk.reflPulledPair (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
      (ubCustomMuxCatUnitary M_fwd prepOutImpl sF) (ubCustomMuxCatUnitary M_bwd prepOutImpl sB⁻¹)⁻¹
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
    CleanWalkRefl2At bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v
      (uRefl2 * (R₀ * uRefl2) ^ (K - 1))
      (bellSuperNoNeg57D11CompDyn d hd bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs
        hsIn
        v pOutFwd pOutBwd P_1 pTurn P_4) := by
  rw [bellSuperNoNeg57D11CompDyn_eq]
  rw [compactSelect57NoNegD11SliceDyn_eq] at hs1 hs2
  exact cleanWalkRefl2At_bellSuperNoNegGen57Dyn_asym (by omega) (compactCoreD11Bundle d hd
    false).toGen (compactCoreD11Bundle d hd true).toGen K hK hGiPos (by omega) hsIn legs hs1 hs2
    hTurnSupp hInterSupp
theorem cleanWalkRefl2At_bellRefl2NoNeg57D11CompDyn_asym {Var : Type} [Fintype Var] [DecidableEq
  Var] (d : ℕ) (hd : d ≤ 11) {bQPE wOuter wInner2 ko km mLow sUb : ℕ} (hGiPos : 0 < wInner2)
    {hkOut : ko ≤ wOuter}
  {hkMid : km ≤ wInner2} (hs : 160 - d ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 -
    d) {v : Var}
  {prepOutImpl : Unitary (2 ^ mOutUB wOuter)} {M_fwd M_bwd : Unitary (2 ^ nUB wOuter wInner2)}
    {raw_4 raw_3
  sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))} {pOutFwd pOutBwd P_1 pTurn P_4 : DynamicCircuit
    Var
  (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)} (legs : BellAsymLegs Var bQPE wOuter wInner2 ko
    km mLow sUb
  hkOut hkMid v prepOutImpl M_fwd M_bwd raw_4 raw_3 sF sB pOutFwd pOutBwd P_1 pTurn P_4) (hs1 :
  CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image ((combWalkCatRegAt
    bQPE
  wOuter wInner2 ko km mLow sUb).embedUnitary raw_4) (compactSelect57NoNegD11SliceDyn d hd false hs
    v wOuter
  wInner2 hGiPos (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb) (combScrUbRegAt bQPE wOuter
    wInner2 ko km
  mLow sUb))) (hs2 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
  ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_3)
  (compactSelect57NoNegD11SliceDyn d hd true hs v wOuter wInner2 hGiPos (combWalkCatRegAt bQPE
    wOuter wInner2
  ko km mLow sUb) (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb))) (hTurnSupp : Disjoint
  pTurn.support (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb (159 - d) (by omega))) :
  CleanWalkRefl2At bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v (QubitisedWalk.reflPulledPair
    (inMidWalkCat
  11 (mOutUB wOuter) (mMidUB wInner2)) (ubCustomMuxCatUnitary M_fwd prepOutImpl sF)
    (ubCustomMuxCatUnitary
  M_bwd prepOutImpl sB⁻¹)⁻¹) (bellRefl2NoNeg57D11CompDyn d hd bQPE wOuter wInner2 ko km mLow sUb
    hkOut
  hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4) := cleanWalkRefl2At_congr_u
  (by rw [Nat.sub_self, _root_.pow_zero, mul_one])
  (cleanWalkRefl2At_bellSuperNoNeg57D11CompDyn_asym d hd 1 (by decide) hGiPos hs hsIn legs hs1
  hs2 hTurnSupp (fun h2 ↦ absurd h2 (by decide)))
end PhaseBD11CompactCore
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
end
