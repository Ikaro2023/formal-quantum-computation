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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.AlwaysLoStage1DualGlfa
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.TopHadStage1Tab0Core


open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option autoImplicit false
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 8192
set_option Elab.async false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
  QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (zg187_hM0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_of_circuit subspaceStep_congr_in subspaceStep_congr_out specFanoutCopyVecCirc
    count_bellXHalfVecDyn_t count_bellXHalfVecDyn_toff)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn)
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance : NeZero 2 := ⟨two_ne_zero⟩
scoped instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances


open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.CoulombFast
  QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70
open QuantumComputation.Specs.PhotochemistrySolution.Bf33K9UniCrtOpt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18 (evalPrimTree
    decodePrimTree decodePrimTree_spec PrimTree evalPrimGate checkPrimTree testBit_xor_shift1)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (bellXHalfVecDyn
    specBellEntangleVecCirc bellZHalfVecDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 (idxValPrefix idxValD
    idxValPrefix_lt_two_pow)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse (fixedFanoutVecCirc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA (wSuperVec_bot_pub
    wSuperVec_top_pub oneHotOptPreVec oneHotOptPreOp count_wUncompTreeDyn_opt dw_wUncompTreeDyn_opt
    subspaceStep_wUncompTreeDyn_opt update_eq_self_of_zero ket_CNOT_ctrl_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA (wZeroGate_ket WOptInj
    OptBasePred wLastSplitShiftDyn count_wLastSplitShiftDyn dw_wLastSplitShiftDyn
    subspaceStep_wLastSplitShiftDyn)


noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.KpBasis9WRouterOpt
open scoped Circuit.Notation
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.XMeasLinearCleanStep
  PhotochemistrySolution.PotOracleGen PhotochemistrySolution.Unshift32Bf84
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PrimitiveGate (T TOFF)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (xorWireUnitary
    xorWireUnitary_mulVec_ket ket_X ket_CNOT eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt
    natOfZModBits_testBit_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (WRouterDisj
    toggleOneHotBits toggleOneHotBits_apply_out toggleOneHotBits_apply_other uOneHotToggle
    uOneHotToggle_mulVec_ket wRouterBracket3x2k)
/-! ### 1. Distinctness Witnesses & `27`-Point `ZMod 2` Polynomial Certificate for `kpBasis9Code` -/

theorem rBasis9_ne_of_ne {n : ℕ} (rBasis9 : QRegister 9 n) {u v : Fin 9} (h : u ≠ v) : rBasis9 u ≠
    rBasis9 v := fun e ↦ h (rBasis9.wires.injective e)
theorem rScr40_ne_of_ne {n : ℕ} (rScr40 : QRegister 40 n) {u v : Fin 40} (h : u ≠ v) : rScr40 u ≠
    rScr40 v := fun e ↦ h (rScr40.wires.injective e)
def kpOfBits (scr nn : ZMod 2) (kF : Fin 4 → ZMod 2) : ℕ :=
    natOfZModBits 4 kF + (if scr = 1 ∧ nn = 0 then 1 else 0)
def kpBasis9Vec (scr nn k0 k1 k2 k3 : ZMod 2) (u : Fin 9) : ZMod 2 :=
  let d := scr + nn
  let c0 := k0 * d
  let c1 := k1 * c0
  let c2 := k2 * c1
  let s0 := d + k0
  let s1 := k1 + c0
  let s2 := k2 + c1
  let s3 := k3 + c2
  match u.val with
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s0 * s1
  | 5 => s0 * s2
  | 6 => s1 * s2
  | 7 => (s0 * s1) * s2
  | _ => s0 * s3

private def z2OfBool (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem z2OfBool_beq_id (b : ZMod 2) : z2OfBool (b == 1) = b := by decide +revert
private def checkKpBasis9Poly : Bool :=
  allLt 2 fun scr ↦
    allLt 2 fun nn ↦
      allLt 9 fun k ↦
        if scr == 0 && nn == 1 then true
        else
          let kp := k + (if scr == 1 && nn == 0 then 1 else 0)
          let c0 := kpBasis9Code kp
          let bF :=
              kpBasis9Vec (z2OfBool (scr == 1)) (z2OfBool (nn == 1)) (z2OfBool (k.testBit 0))
              (z2OfBool (k.testBit 1)) (z2OfBool (k.testBit 2)) (z2OfBool (k.testBit 3))
          allLt 9 fun u ↦ if hu : u < 9 then (bF ⟨u, hu⟩ == 1) == c0.testBit u else true

private theorem checkKpBasis9Poly_cert : checkKpBasis9Poly = true := by decide +kernel

private def checkKLe8NotBoth : Bool := allLt 9 fun k ↦ !(k.testBit 0 && k.testBit 3)
private theorem checkKLe8NotBoth_cert : checkKLe8NotBoth = true := by decide

theorem not_k0_and_k3_of_le8 (kF : Fin 4 → ZMod 2) (hk : natOfZModBits 4 kF ≤ 8) :
    ¬(kF ⟨0, by decide⟩ = 1 ∧ kF ⟨3, by decide⟩ = 1) := by
  rintro ⟨h0, h3⟩
  have hRow := allLt_spec checkKLe8NotBoth_cert (natOfZModBits 4 kF) (by omega)
  rw [natOfZModBits_testBit_lt _ (by decide), natOfZModBits_testBit_lt _ (by decide),
    h0, h3] at hRow
  exact absurd hRow (by decide)
private theorem z2OfBool_val_beq_one (x : ZMod 2) : z2OfBool (x.val == 1) = x := by decide +revert
private theorem scr_nn_false_of_valid (scr nn : ZMod 2) (hValid : ¬(scr = 0 ∧ nn = 1)) :
    (scr.val == 0 && nn.val == 1) = false := by decide +revert
private theorem kp_offset_val_eq (scr nn : ZMod 2) : (if (scr.val == 1 && nn.val == 0) =
    true then 1 else 0) = (if scr = 1 ∧ nn = 0 then 1 else 0) := by decide +revert
private theorem z2_eq_ite_beq_one (b : ZMod 2) (c : Bool) (h : (b == 1) = c) : b =
    if c then 1 else 0 := by subst h; decide +revert
theorem kpBasis9Vec_eq_code (scr nn : ZMod 2) (kF : Fin 4 → ZMod 2)
    (hk : natOfZModBits 4 kF ≤ 8) (hValid : ¬(scr = 0 ∧ nn = 1)) (u : Fin 9) :
    (kpBasis9Vec scr nn (kF ⟨0, by decide⟩) (kF ⟨1, by decide⟩)
      (kF ⟨2, by decide⟩) (kF ⟨3, by decide⟩) u == 1) =
    (kpBasis9Code (kpOfBits scr nn kF)).testBit u.val := by
  have hRow := allLt_spec (allLt_spec (allLt_spec checkKpBasis9Poly_cert
    scr.val (ZMod.val_lt scr)) nn.val (ZMod.val_lt nn)) (natOfZModBits 4 kF) (by omega)
  rw [scr_nn_false_of_valid scr nn hValid] at hRow
  simp only [Bool.false_eq_true, ↓reduceIte] at hRow
  have hu0 := allLt_spec hRow u.val u.isLt
  simp only [u.isLt, ↓reduceDIte] at hu0
  have hkBit (i : ℕ) (hi : i < 4) :
      z2OfBool ((natOfZModBits 4 kF).testBit i) = kF ⟨i, hi⟩ := by
    rw [natOfZModBits_testBit_lt _ hi, z2OfBool_beq_id]
  have hu := eq_of_beq hu0
  rwa [z2OfBool_val_beq_one scr, z2OfBool_val_beq_one nn, hkBit 0 (by decide),
    hkBit 1 (by decide), hkBit 2 (by decide), hkBit 3 (by decide), kp_offset_val_eq scr nn] at hu
theorem kpBasis9Vec_eq_ite_code (scr nn : ZMod 2) (kF : Fin 4 → ZMod 2)
    (hk : natOfZModBits 4 kF ≤ 8) (hValid : ¬(scr = 0 ∧ nn = 1)) (u : Fin 9) :
    kpBasis9Vec scr nn (kF ⟨0, by decide⟩) (kF ⟨1, by decide⟩)
      (kF ⟨2, by decide⟩) (kF ⟨3, by decide⟩) u =
    if (kpBasis9Code (kpOfBits scr nn kF)).testBit u.val then 1 else 0 :=
  z2_eq_ite_beq_one _ _ (kpBasis9Vec_eq_code scr nn kF hk hValid u)

/-! ### 2. 14-Step Causal Evolution `kpStep1..kpStep14` & `0-T` MBU Uncomputer `pKpBasis9Rev0` -/

private def vKp0 : Fin 9 → ZMod 2 := fun _ ↦ 0
private def vKp1 (nn : ZMod 2) : Fin 9 → ZMod 2 :=
  Function.update vKp0 ⟨0, by decide⟩ (vKp0 ⟨0, by decide⟩ + nn)
private def vKp2 (scr nn : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp1 nn
  Function.update v ⟨0, by decide⟩ (v ⟨0, by decide⟩ + scr)
private def vKp3 (scr nn k0 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp2 scr nn
  Function.update v ⟨1, by decide⟩ (v ⟨1, by decide⟩ + k0 * v ⟨0, by decide⟩)
private def vKp4 (scr nn k0 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp3 scr nn k0
  Function.update v ⟨0, by decide⟩ (v ⟨0, by decide⟩ + k0)
private def vKp5 (scr nn k0 k1 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp4 scr nn k0
  Function.update v ⟨2, by decide⟩ (v ⟨2, by decide⟩ + k1 * v ⟨1, by decide⟩)
private def vKp6 (scr nn k0 k1 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp5 scr nn k0 k1
  Function.update v ⟨1, by decide⟩ (v ⟨1, by decide⟩ + k1)
private def vKp7 (scr nn k0 k1 k2 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp6 scr nn k0 k1
  Function.update v ⟨3, by decide⟩ (v ⟨3, by decide⟩ + k2 * v ⟨2, by decide⟩)
private def vKp8 (scr nn k0 k1 k2 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp7 scr nn k0 k1 k2
  Function.update v ⟨2, by decide⟩ (v ⟨2, by decide⟩ + k2)
private def vKp9 (scr nn k0 k1 k2 k3 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp8 scr nn k0 k1 k2
  Function.update v ⟨3, by decide⟩ (v ⟨3, by decide⟩ + k3)
private def vKp10 (scr nn k0 k1 k2 k3 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp9 scr nn k0 k1 k2 k3
  Function.update v ⟨4, by decide⟩ (v ⟨4, by decide⟩ + v ⟨0, by decide⟩ * v ⟨1, by decide⟩)
private def vKp11 (scr nn k0 k1 k2 k3 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp10 scr nn k0 k1 k2 k3
  Function.update v ⟨5, by decide⟩ (v ⟨5, by decide⟩ + v ⟨0, by decide⟩ * v ⟨2, by decide⟩)
private def vKp12 (scr nn k0 k1 k2 k3 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp11 scr nn k0 k1 k2 k3
  Function.update v ⟨6, by decide⟩ (v ⟨6, by decide⟩ + v ⟨1, by decide⟩ * v ⟨2, by decide⟩)
private def vKp13 (scr nn k0 k1 k2 k3 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp12 scr nn k0 k1 k2 k3
  Function.update v ⟨8, by decide⟩ (v ⟨8, by decide⟩ + v ⟨0, by decide⟩ * v ⟨3, by decide⟩)
private def vKp14 (scr nn k0 k1 k2 k3 : ZMod 2) : Fin 9 → ZMod 2 :=
  let v := vKp13 scr nn k0 k1 k2 k3
  Function.update v ⟨7, by decide⟩ (v ⟨7, by decide⟩ + v ⟨4, by decide⟩ * v ⟨2, by decide⟩)

private theorem vKp_targets_zero (scr nn k0 k1 k2 k3 : ZMod 2) :
    vKp2 scr nn ⟨1, by decide⟩ = 0 ∧
    vKp4 scr nn k0 ⟨2, by decide⟩ = 0 ∧
    vKp6 scr nn k0 k1 ⟨3, by decide⟩ = 0 ∧
    vKp9 scr nn k0 k1 k2 k3 ⟨4, by decide⟩ = 0 ∧
    vKp10 scr nn k0 k1 k2 k3 ⟨5, by decide⟩ = 0 ∧
    vKp11 scr nn k0 k1 k2 k3 ⟨6, by decide⟩ = 0 ∧
    vKp12 scr nn k0 k1 k2 k3 ⟨8, by decide⟩ = 0 ∧
    vKp13 scr nn k0 k1 k2 k3 ⟨7, by decide⟩ = 0 := by
  decide +revert

private theorem vKp14_eq_vec (scr nn k0 k1 k2 k3 : ZMod 2)
    (u : Fin 9) : vKp14 scr nn k0 k1 k2 k3 u = kpBasis9Vec scr nn k0 k1 k2 k3 u := by decide +revert
def kpStep1 {n : ℕ} (wNN : Wire n) (rBasis9 : QRegister 9 n) (β : BitAssignment n) :
    BitAssignment n :=
  let b0 := rBasis9 ⟨0, by decide⟩
  Function.update β b0 (β b0 + β wNN)

def kpStep2 {n : ℕ} (wScr wNN : Wire n) (rBasis9 : QRegister 9 n) (β : BitAssignment n) :
    BitAssignment n :=
  let s := kpStep1 wNN rBasis9 β
  let b0 := rBasis9 ⟨0, by decide⟩
  Function.update s b0 (s b0 + s wScr)

def kpStep3 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep2 wScr wNN rBasis9 β
  let b1 := rBasis9 ⟨1, by decide⟩
  Function.update s b1 (s b1 + s (rK4 ⟨0, by decide⟩) * s (rBasis9 ⟨0, by decide⟩))

def kpStep4 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep3 wScr wNN rK4 rBasis9 β
  let b0 := rBasis9 ⟨0, by decide⟩
  Function.update s b0 (s b0 + s (rK4 ⟨0, by decide⟩))

def kpStep5 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep4 wScr wNN rK4 rBasis9 β
  let b2 := rBasis9 ⟨2, by decide⟩
  Function.update s b2 (s b2 + s (rK4 ⟨1, by decide⟩) * s (rBasis9 ⟨1, by decide⟩))

def kpStep6 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep5 wScr wNN rK4 rBasis9 β
  let b1 := rBasis9 ⟨1, by decide⟩
  Function.update s b1 (s b1 + s (rK4 ⟨1, by decide⟩))

def kpStep7 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep6 wScr wNN rK4 rBasis9 β
  let b3 := rBasis9 ⟨3, by decide⟩
  Function.update s b3 (s b3 + s (rK4 ⟨2, by decide⟩) * s (rBasis9 ⟨2, by decide⟩))

def kpStep8 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep7 wScr wNN rK4 rBasis9 β
  let b2 := rBasis9 ⟨2, by decide⟩
  Function.update s b2 (s b2 + s (rK4 ⟨2, by decide⟩))

def kpStep9 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep8 wScr wNN rK4 rBasis9 β
  let b3 := rBasis9 ⟨3, by decide⟩
  Function.update s b3 (s b3 + s (rK4 ⟨3, by decide⟩))

def kpStep10 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep9 wScr wNN rK4 rBasis9 β
  let b4 := rBasis9 ⟨4, by decide⟩
  Function.update s b4 (s b4 + s (rBasis9 ⟨0, by decide⟩) * s (rBasis9 ⟨1, by decide⟩))

def kpStep11 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep10 wScr wNN rK4 rBasis9 β
  let b5 := rBasis9 ⟨5, by decide⟩
  Function.update s b5 (s b5 + s (rBasis9 ⟨0, by decide⟩) * s (rBasis9 ⟨2, by decide⟩))

def kpStep12 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep11 wScr wNN rK4 rBasis9 β
  let b6 := rBasis9 ⟨6, by decide⟩
  Function.update s b6 (s b6 + s (rBasis9 ⟨1, by decide⟩) * s (rBasis9 ⟨2, by decide⟩))

def kpStep13 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep12 wScr wNN rK4 rBasis9 β
  let b8 := rBasis9 ⟨8, by decide⟩
  Function.update s b8 (s b8 + s (rBasis9 ⟨0, by decide⟩) * s (rBasis9 ⟨3, by decide⟩))

def kpStep14 {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (β : BitAssignment n) : BitAssignment n :=
  let s := kpStep13 wScr wNN rK4 rBasis9 β
  let b7 := rBasis9 ⟨7, by decide⟩
  Function.update s b7 (s b7 + s (rBasis9 ⟨4, by decide⟩) * s (rBasis9 ⟨2, by decide⟩))

private def AgreesBasis9 {n : ℕ} (rBasis9 : QRegister 9 n) (β st : BitAssignment n)
    (v : Fin 9 → ZMod 2) : Prop :=
    (∀ u : Fin 9, st (rBasis9 u) = v u) ∧ (∀ w : Wire n, (∀ u : Fin 9, w ≠ rBasis9 u) → st w = β w)
private theorem agreesBasis9_upd {n : ℕ} {rBasis9 : QRegister 9 n} {β st : BitAssignment n}
    {v : Fin 9 → ZMod 2} (h : AgreesBasis9 rBasis9 β st v) (idx : Fin 9) (val1 val2 : ZMod 2)
    (hv : val1 = val2) : AgreesBasis9 rBasis9 β (Function.update st (rBasis9 idx) val1)
    (Function.update v idx val2) := by
  subst hv
  refine ⟨fun u ↦ ?_, fun w hw ↦ (Function.update_of_ne (hw idx) val1 st).trans (h.2 w hw)⟩
  by_cases hu : u = idx
  · subst hu; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (rBasis9_ne_of_ne rBasis9 hu), Function.update_of_ne hu, h.1 u]

private theorem kpSteps_agrees {n : ℕ} {wScr wNN : Wire n} {rK4 : QRegister 4 n}
    {rBasis9 : QRegister 9 n}
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9) (β : BitAssignment n)
    (hb0 : ∀ u : Fin 9, β (rBasis9 u) = 0) :
    let scr := β wScr
    let nn := β wNN
    let k0 := β (rK4 ⟨0, by decide⟩)
    let k1 := β (rK4 ⟨1, by decide⟩)
    let k2 := β (rK4 ⟨2, by decide⟩)
    let k3 := β (rK4 ⟨3, by decide⟩)
    AgreesBasis9 rBasis9 β (kpStep2 wScr wNN rBasis9 β) (vKp2 scr nn) ∧
    AgreesBasis9 rBasis9 β (kpStep4 wScr wNN rK4 rBasis9 β) (vKp4 scr nn k0) ∧
    AgreesBasis9 rBasis9 β (kpStep6 wScr wNN rK4 rBasis9 β) (vKp6 scr nn k0 k1) ∧
    AgreesBasis9 rBasis9 β (kpStep9 wScr wNN rK4 rBasis9 β) (vKp9 scr nn k0 k1 k2 k3) ∧
    AgreesBasis9 rBasis9 β (kpStep10 wScr wNN rK4 rBasis9 β) (vKp10 scr nn k0 k1 k2 k3) ∧
    AgreesBasis9 rBasis9 β (kpStep11 wScr wNN rK4 rBasis9 β) (vKp11 scr nn k0 k1 k2 k3) ∧
    AgreesBasis9 rBasis9 β (kpStep12 wScr wNN rK4 rBasis9 β) (vKp12 scr nn k0 k1 k2 k3) ∧
    AgreesBasis9 rBasis9 β (kpStep13 wScr wNN rK4 rBasis9 β) (vKp13 scr nn k0 k1 k2 k3) ∧
    AgreesBasis9 rBasis9 β (kpStep14 wScr wNN rK4 rBasis9 β) (vKp14 scr nn k0 k1 k2 k3) := by
  intro scr nn k0 k1 k2 k3
  let A := AgreesBasis9 rBasis9 β
  let AK (s : _ → _ → _ → _ → _ → _) (v : _ → _ → _ → _ → _ → _ → _) :=
    A (s wScr wNN rK4 rBasis9 β) (v scr nn k0 k1 k2 k3)
  have uC {st v} (a : A st v) (q : Fin 9) {w} (hw : ∀ u, w ≠ rBasis9 u) : A _ _ :=
    agreesBasis9_upd a q (st (rBasis9 q) + st w) (v q + β w) (by rw [a.1, a.2 w hw])
  have uK {st v} (a : A st v) (q : Fin 9) (i : Fin 4) (u : Fin 9) : A _ _ :=
    agreesBasis9_upd a q (st (rBasis9 q) + st (rK4 i) * st (rBasis9 u)) (v q + β (rK4 i) * v u)
      (by rw [a.1, a.1, a.2 _ (disj_ne hKB i)])
  have uB {st v} (a : A st v) (q u1 u2 : Fin 9) : A _ _ :=
    agreesBasis9_upd a q (st (rBasis9 q) + st (rBasis9 u1) * st (rBasis9 u2))
      (v q + v u1 * v u2) (by rw [a.1, a.1, a.1])
  have a2 : A (kpStep2 wScr wNN rBasis9 β) (vKp2 scr nn) :=
    uC (uC (⟨hb0, fun _ _ ↦ rfl⟩ : A β vKp0) 0 hNNB) 0 hScrB
  have a4 : A (kpStep4 wScr wNN rK4 rBasis9 β) (vKp4 scr nn k0) :=
    uC (uK a2 1 0 0) 0 (disj_ne hKB 0)
  have a6 : A (kpStep6 wScr wNN rK4 rBasis9 β) (vKp6 scr nn k0 k1) :=
    uC (uK a4 2 1 1) 1 (disj_ne hKB 1)
  have a9 : AK kpStep9 vKp9 := uC (uC (uK a6 3 2 2) 2 (disj_ne hKB 2)) 3 (disj_ne hKB 3)
  have a10 : AK kpStep10 vKp10 := uB a9 4 0 1
  have a11 : AK kpStep11 vKp11 := uB a10 5 0 2
  have a12 : AK kpStep12 vKp12 := uB a11 6 1 2
  have a13 : AK kpStep13 vKp13 := uB a12 8 0 3
  exact ⟨a2, a4, a6, a9, a10, a11, a12, a13, uB a13 7 4 2⟩

theorem kpStep14_eq_writeReg {n : ℕ} {wScr wNN : Wire n} {rK4 : QRegister 4 n}
    {rBasis9 : QRegister 9 n}
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9) (β : BitAssignment n)
    (hb0 : ∀ u : Fin 9, β (rBasis9 u) = 0) :
    kpStep14 wScr wNN rK4 rBasis9 β =
      writeReg β rBasis9 (kpBasis9Vec (β wScr) (β wNN)
        (β (rK4 ⟨0, by decide⟩)) (β (rK4 ⟨1, by decide⟩))
        (β (rK4 ⟨2, by decide⟩)) (β (rK4 ⟨3, by decide⟩))) := by
  have a14 := (kpSteps_agrees hScrB hNNB hKB β hb0).2.2.2.2.2.2.2.2; funext w
  by_cases hm : ∃ u : Fin 9, rBasis9 u = w
  · obtain ⟨u, rfl⟩ := hm; rw [writeReg_apply_reg, a14.1 u, vKp14_eq_vec]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hm]
    exact a14.2 w fun u e ↦ hm ⟨u, e.symm⟩

theorem kpStep14_eq_writeReg_code {n : ℕ} {wScr wNN : Wire n} {rK4 : QRegister 4 n}
    {rBasis9 : QRegister 9 n} (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9) (β : BitAssignment n) (hb0 : ∀ u : Fin 9, β (rBasis9 u) = 0)
    (hk : natOfZModBits 4 (fun i ↦ β (rK4 i)) ≤ 8) (hValid : ¬(β wScr = 0 ∧ β wNN = 1)) :
    kpStep14 wScr wNN rK4 rBasis9 β = writeReg β rBasis9 (fun u ↦
    if (kpBasis9Code (kpOfBits (β wScr) (β wNN) (fun i ↦ β (rK4 i)))).testBit u.val then 1 else 0)
    := by
  rw [kpStep14_eq_writeReg hScrB hNNB hKB β hb0]
  congr 1; funext u
  exact kpBasis9Vec_eq_ite_code (β wScr) (β wNN) (fun i ↦ β (rK4 i)) hk hValid u

private theorem subspaceStep_xUnloadSinglePair_mkKetOpW {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (q c₁ c₂ : Wire n) (hc12 : c₁ ≠ c₂)
    (hqc1 : c₁ ≠ q) (hqc2 : c₂ ≠ q) (rest : DynamicCircuit Var n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (R_out : Operator (2 ^ n)) (hq0 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → st δ q = 0)
    (hRest : SubspaceStep (mkKetOpW rWork st ph) R_out rest) : SubspaceStep (mkKetOpW rWork (fun δ ↦
    Function.update (st δ) q (st δ q + st δ c₁ * st δ c₂)) ph) R_out (xUnloadCzPairsSeqDyn v q [⟨c₁,
    ⟨c₂, hc12⟩⟩] rest) := by
  let f : BitAssignment n → ZMod 2 := fun β ↦ β c₁ * β c₂
  have hf (β a) : f (Function.update β q a) = f β :=
    congrArg₂ (· * ·) (Function.update_of_ne hqc1 a β) (Function.update_of_ne hqc2 a β)
  refine subspaceStep_congr_in (matrix_ext_ket fun δ ↦ ?_).symm
    (subspaceStep_xUnloadCzPairsSeqDyn v q [⟨c₁, ⟨c₂, hc12⟩⟩] rest f hf
      (fun β ↦ by dsimp only [f, czPairsParity]; exact (add_zero _).symm)
      (mkKetOpW rWork st ph) R_out (projBit_zero_mkKetOpW rWork q st ph hq0) hRest)
  rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, xorWireUnitary_mulVec_ket]
  · rw [Matrix.mulVec_zero]

private theorem subspaceStep_cnot_undo_mkKetOpW {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n)
    (c q : Wire n) (hcq : c ≠ q)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (Var := Var)
      (mkKetOpW rWork (fun δ ↦ Function.update (st δ) q (st δ q + st δ c)) ph)
      (mkKetOpW rWork st ph)
      (.circuit (Circuit.CNOT c q hcq)) := by
  refine subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ (Circuit.CNOT c q hcq)) ?_
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, ket_CNOT, Function.update_self, Function.update_of_ne hcq, add_assoc,
        CharTwo.add_self_eq_zero, add_zero, Function.update_idem, Function.update_eq_self]
  · rw [Matrix.mulVec_zero]

private theorem subspaceStep_cnot_seq_mkKetOpW {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n) (c q : Wire n) (hcq : c ≠ q)
    (rest : DynamicCircuit Var n) (st : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) (R_out : Operator (2 ^ n))
    (hRest : SubspaceStep (mkKetOpW rWork st ph) R_out rest) : SubspaceStep (mkKetOpW rWork (fun δ ↦
    Function.update (st δ) q (st δ q +
    st δ c)) ph) R_out (.seq (.circuit (Circuit.CNOT c q hcq)) rest) :=
  subspaceStep_seq_u (subspaceStep_cnot_undo_mkKetOpW rWork c q hcq st ph) hRest

/--
`0-T` , `0-.TOFF` , zero-scratch reverse MBU uncomputer for `rBasis9` (`8` `.XMEAS+CZ` + `6` CNOTs).
-/
def pKpBasis9Rev0 {Var : Type} {n : ℕ} (v : Var) (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (rBasis9 : QRegister 9 n) (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9) : DynamicCircuit Var n :=
  xUnloadCzPairsSeqDyn v (rBasis9 ⟨7, by decide⟩)
    [⟨rBasis9 ⟨4, by decide⟩, ⟨rBasis9 ⟨2, by decide⟩, rBasis9_ne_of_ne rBasis9 (by decide)⟩⟩]
  (xUnloadCzPairsSeqDyn v (rBasis9 ⟨8, by decide⟩)
    [⟨rBasis9 ⟨0, by decide⟩, ⟨rBasis9 ⟨3, by decide⟩, rBasis9_ne_of_ne rBasis9 (by decide)⟩⟩]
  (xUnloadCzPairsSeqDyn v (rBasis9 ⟨6, by decide⟩)
    [⟨rBasis9 ⟨1, by decide⟩, ⟨rBasis9 ⟨2, by decide⟩, rBasis9_ne_of_ne rBasis9 (by decide)⟩⟩]
  (xUnloadCzPairsSeqDyn v (rBasis9 ⟨5, by decide⟩)
    [⟨rBasis9 ⟨0, by decide⟩, ⟨rBasis9 ⟨2, by decide⟩, rBasis9_ne_of_ne rBasis9 (by decide)⟩⟩]
  (xUnloadCzPairsSeqDyn v (rBasis9 ⟨4, by decide⟩)
    [⟨rBasis9 ⟨0, by decide⟩, ⟨rBasis9 ⟨1, by decide⟩, rBasis9_ne_of_ne rBasis9 (by decide)⟩⟩]
  (.seq (.circuit (Circuit.CNOT (rK4 ⟨3, by decide⟩) (rBasis9 ⟨3, by decide⟩) (disj_ne hKB _ _)))
  (.seq (.circuit (Circuit.CNOT (rK4 ⟨2, by decide⟩) (rBasis9 ⟨2, by decide⟩) (disj_ne hKB _ _)))
  (xUnloadCzPairsSeqDyn v (rBasis9 ⟨3, by decide⟩)
    [⟨rK4 ⟨2, by decide⟩, ⟨rBasis9 ⟨2, by decide⟩, disj_ne hKB _ _⟩⟩]
  (.seq (.circuit (Circuit.CNOT (rK4 ⟨1, by decide⟩) (rBasis9 ⟨1, by decide⟩) (disj_ne hKB _ _)))
  (xUnloadCzPairsSeqDyn v (rBasis9 ⟨2, by decide⟩)
    [⟨rK4 ⟨1, by decide⟩, ⟨rBasis9 ⟨1, by decide⟩, disj_ne hKB _ _⟩⟩]
  (.seq (.circuit (Circuit.CNOT (rK4 ⟨0, by decide⟩) (rBasis9 ⟨0, by decide⟩) (disj_ne hKB _ _)))
  (xUnloadCzPairsSeqDyn v (rBasis9 ⟨1, by decide⟩)
    [⟨rK4 ⟨0, by decide⟩, ⟨rBasis9 ⟨0, by decide⟩, disj_ne hKB _ _⟩⟩]
  (.seq (.circuit (Circuit.CNOT wScr (rBasis9 ⟨0, by decide⟩) (hScrB _)))
        (.circuit (Circuit.CNOT wNN (rBasis9 ⟨0, by decide⟩) (hNNB _)))))))))))))))

theorem pKpBasis9Rev0_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u) (hKB : rK4.DisjointWires rBasis9)
    (hScr : S wScr) (hNN : S wNN) (hrK : ∀ i, S (rK4 i)) (hrB : ∀ u, S (rBasis9 u)) :
    (pKpBasis9Rev0 v wScr wNN rK4 rBasis9 hScrB hNNB hKB).count .T = 0 ∧
    (pKpBasis9Rev0 v wScr wNN rK4 rBasis9 hScrB hNNB hKB).count .TOFF = 0 ∧
    DynWires S (pKpBasis9Rev0 v wScr wNN rK4 rBasis9 hScrB hNNB hKB) := by
  unfold pKpBasis9Rev0
  have dwB : ∀ q u₁ u₂ (h : rBasis9 u₁ ≠ rBasis9 u₂) {r}, DynWires S r →
      DynWires S (xUnloadCzPairsSeqDyn v (rBasis9 q) [⟨rBasis9 u₁, ⟨rBasis9 u₂, h⟩⟩] r) :=
    fun _ _ _ _ _ hr ↦ dw_xUnload (hrB _) (fun _ hp ↦ by
      rcases List.mem_singleton.mp hp with rfl
      exact ⟨hrB _, hrB _⟩) hr
  have dwK : ∀ q i u (h : rK4 i ≠ rBasis9 u) {r}, DynWires S r →
      DynWires S (xUnloadCzPairsSeqDyn v (rBasis9 q) [⟨rK4 i, ⟨rBasis9 u, h⟩⟩] r) :=
    fun _ _ _ _ _ hr ↦ dw_xUnload (hrB _) (fun _ hp ↦ by
      rcases List.mem_singleton.mp hp with rfl
      exact ⟨hrK _, hrB _⟩) hr
  refine ⟨by simp [(count_xUnloadCzPairsSeqDyn _ _ _ _).1, DynamicCircuit.count, Circuit.CNOT],
    by simp [(count_xUnloadCzPairsSeqDyn _ _ _ _).2, DynamicCircuit.count, Circuit.CNOT],
    dwB _ _ _ _ (dwB _ _ _ _ (dwB _ _ _ _ (dwB _ _ _ _ (dwB _ _ _ _
      ⟨cw_cnot (hrK _) (hrB _), cw_cnot (hrK _) (hrB _), dwK _ _ _ _ ⟨cw_cnot (hrK _) (hrB _),
        dwK _ _ _ _ ⟨cw_cnot (hrK _) (hrB _), dwK _ _ _ _ ⟨cw_cnot hScr (hrB _),
          cw_cnot hNN (hrB _)⟩⟩⟩⟩))))⟩

section Rev0Irred
attribute [local irreducible] mkKetOpW
theorem subspaceStep_pKpBasis9Rev0 {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (rBasis9 : QRegister 9 n) (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9) (st : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) (hb0 : ∀ (δ : BitAssignment n)
    (u : Fin 9), (∀ k : Fin W, δ (rWork k) = 0) → st δ (rBasis9 u) = 0) :
    SubspaceStep (mkKetOpW rWork (fun δ ↦ kpStep14 wScr wNN rK4 rBasis9 (st δ)) ph)
    (mkKetOpW rWork st ph) (pKpBasis9Rev0 v wScr wNN rK4 rBasis9 hScrB hNNB hKB) := by
  unfold pKpBasis9Rev0
  have hAg (δ : BitAssignment n) (hz : ∀ k : Fin W, δ (rWork k) = 0) :=
    kpSteps_agrees hScrB hNNB hKB (st δ) fun u ↦ hb0 δ u hz
  have hTz (δ : BitAssignment n) := vKp_targets_zero (st δ wScr) (st δ wNN) (st δ (rK4 0))
    (st δ (rK4 1)) (st δ (rK4 2)) (st δ (rK4 3))
  let R := mkKetOpW rWork st ph
  let cnotS (c q : Wire n) (hcq : c ≠ q) {rest : DynamicCircuit Var n} {st'}
      (hs : SubspaceStep (mkKetOpW rWork st' ph) R rest) :=
    subspaceStep_cnot_seq_mkKetOpW rWork c q hcq rest st' ph R hs
  let unlK (q : Fin 9) (i : Fin 4) (u : Fin 9) (huq : u ≠ q) {st' rest}
      (hs : SubspaceStep (mkKetOpW rWork st' ph) R rest)
      (hq0 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → st' δ (rBasis9 q) = 0) :=
    subspaceStep_xUnloadSinglePair_mkKetOpW v rWork (rBasis9 q) (rK4 i) (rBasis9 u)
      (disj_ne hKB _ _) (disj_ne hKB _ _) (rBasis9_ne_of_ne rBasis9 huq) rest st' ph R hq0 hs
  let unlB (q u₁ u₂ : Fin 9) (h12 : u₁ ≠ u₂) (h1q : u₁ ≠ q) (h2q : u₂ ≠ q) {st' rest}
      (hs : SubspaceStep (mkKetOpW rWork st' ph) R rest)
      (hq0 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → st' δ (rBasis9 q) = 0) :=
    subspaceStep_xUnloadSinglePair_mkKetOpW v rWork (rBasis9 q) (rBasis9 u₁) (rBasis9 u₂)
      (rBasis9_ne_of_ne rBasis9 h12) (rBasis9_ne_of_ne rBasis9 h1q)
      (rBasis9_ne_of_ne rBasis9 h2q) rest st' ph R hq0 hs
  let s9 := cnotS (rK4 3) (rBasis9 3) (disj_ne hKB _ _)
    (cnotS (rK4 2) (rBasis9 2) (disj_ne hKB _ _)
      (unlK 3 2 2 (by decide) (cnotS (rK4 1) (rBasis9 1) (disj_ne hKB _ _)
        (unlK 2 1 1 (by decide) (cnotS (rK4 0) (rBasis9 0) (disj_ne hKB _ _)
          (unlK 1 0 0 (by decide) (cnotS wScr (rBasis9 0) (hScrB _)
            (subspaceStep_cnot_undo_mkKetOpW rWork wNN (rBasis9 0) (hNNB _) st ph))
            fun δ hz ↦ ((hAg δ hz).1.1 _).trans (hTz δ).1))
          fun δ hz ↦ ((hAg δ hz).2.1.1 _).trans (hTz δ).2.1))
        fun δ hz ↦ ((hAg δ hz).2.2.1.1 _).trans (hTz δ).2.2.1))
  exact unlB 7 4 2 (by decide) (by decide) (by decide)
    (unlB 8 0 3 (by decide) (by decide) (by decide)
      (unlB 6 1 2 (by decide) (by decide) (by decide)
        (unlB 5 0 2 (by decide) (by decide) (by decide)
          (unlB 4 0 1 (by decide) (by decide) (by decide) s9
            fun δ hz ↦ ((hAg δ hz).2.2.2.1.1 _).trans (hTz δ).2.2.2.1)
          fun δ hz ↦ ((hAg δ hz).2.2.2.2.1.1 _).trans (hTz δ).2.2.2.2.1)
        fun δ hz ↦ ((hAg δ hz).2.2.2.2.2.1.1 _).trans (hTz δ).2.2.2.2.2.1)
      fun δ hz ↦ ((hAg δ hz).2.2.2.2.2.2.1.1 _).trans (hTz δ).2.2.2.2.2.2.1)
    fun δ hz ↦ ((hAg δ hz).2.2.2.2.2.2.2.1.1 _).trans (hTz δ).2.2.2.2.2.2.2

end Rev0Irred

/-! ### 3. Forward `24-T` Two-Stage `3x2k` W-Router Loader `pKpBasis9Fwd24` (`6 + 18 = 24 T`) -/

private theorem supportedOn_mkKetOpW {W n : ℕ} (rWork : QRegister W n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    {P : BitAssignment n → Prop}
    (hP : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → P (st δ)) :
    SupportedOn P (mkKetOpW rWork st ph) := fun A B hAB ↦ by
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hAB (st δ) (hP δ hz)]
  · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]

abbrev kpIdxA {n : ℕ} (rBasis9 : QRegister 9 n) (rK4 : QRegister 4 n) : Fin 3 → Wire n
  | ⟨0, _⟩ => rBasis9 ⟨0, by decide⟩
  | ⟨1, _⟩ => rK4 ⟨0, by decide⟩
  | ⟨2, _⟩ => rK4 ⟨3, by decide⟩

abbrev kpOut6 {n : ℕ} (rScr40 : QRegister 40 n) (j : Fin 6) : Wire n :=
  rScr40 ⟨2 + j.val, by have := j.isLt; omega⟩

private theorem wRouterDisj_kpA {n : ℕ} {rBasis9 : QRegister 9 n} {rK4 : QRegister 4 n}
    {rScr40 : QRegister 40 n} (hBS : rBasis9.DisjointWires rScr40)
    (hKS : rK4.DisjointWires rScr40) :
    WRouterDisj (rScr40 ⟨0, by decide⟩) (kpIdxA rBasis9 rK4) (kpOut6 rScr40)
      (rScr40 ⟨1, by decide⟩) where
  has_ne_out j := rScr40_ne_of_ne rScr40 fun e ↦
    (by decide : ∀ k : Fin 6, 0 ≠ 2 + k.val) j (congrArg Fin.val e)
  has_ne_q := rScr40_ne_of_ne rScr40 (by decide)
  idx_ne_out d _ := by fin_cases d <;> first | exact disj_ne hBS _ _ | exact disj_ne hKS _ _
  idx_ne_q d := by fin_cases d <;> first | exact disj_ne hBS _ _ | exact disj_ne hKS _ _
  out_inj i j hij := rScr40_ne_of_ne rScr40 fun e ↦
    (by decide : ∀ a b : Fin 6, a ≠ b → 2 + a.val ≠ 2 + b.val) i j hij (congrArg Fin.val e)
  out_ne_q j := rScr40_ne_of_ne rScr40 fun e ↦
    (by decide : ∀ k : Fin 6, 2 + k.val ≠ 1) j (congrArg Fin.val e)

def cStageAPre {n : ℕ} (wScr wNN : Wire n) (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u) : Circuit n :=
  Circuit.CNOT wScr (rBasis9 ⟨0, by decide⟩) (hScrB _) ;;ᶜ
  Circuit.CNOT wNN (rBasis9 ⟨0, by decide⟩) (hNNB _) ;;ᶜ
  Circuit.X (rScr40 ⟨0, by decide⟩)

def cStageAGather {n : ℕ} (rScr40 : QRegister 40 n) (rBasis9 : QRegister 9 n)
    (hBS : rBasis9.DisjointWires rScr40) : Circuit n :=
  Circuit.CNOT (kpOut6 rScr40 ⟨3, by decide⟩) (rBasis9 ⟨1, by decide⟩) (disj_ne hBS _ _).symm ;;ᶜ
  Circuit.CNOT (kpOut6 rScr40 ⟨5, by decide⟩) (rBasis9 ⟨8, by decide⟩) (disj_ne hBS _ _).symm

private theorem count_cStageAPre {n : ℕ} (wScr wNN : Wire n) (rBasis9 : QRegister 9 n)
    (rScr40 : QRegister 40 n) (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u) :
    (cStageAPre wScr wNN rBasis9 rScr40 hScrB hNNB).count .T = 0 ∧
    (cStageAPre wScr wNN rBasis9 rScr40 hScrB hNNB).count .TOFF = 0 := by
  simp [cStageAPre, Circuit.count_seq, Circuit.CNOT, Circuit.X]
private theorem count_cStageAGather {n : ℕ} (rScr40 : QRegister 40 n) (rBasis9 : QRegister 9 n)
    (hBS : rBasis9.DisjointWires rScr40) : (cStageAGather rScr40 rBasis9 hBS).count .T = 0 ∧
    (cStageAGather rScr40 rBasis9 hBS).count .TOFF = 0 := by
  simp [cStageAGather, Circuit.count_seq, Circuit.CNOT]
private def vStageAPreCnot (scr nn k0 k3 : ZMod 2) (u : Fin 9) : ZMod 2 :=
  let d := scr + nn
  match u.val with
  | 0 => d
  | 1 => k0 * d
  | 8 => k3 * d
  | _ => 0

private def vStageA (scr nn k0 k3 : ZMod 2) (u : Fin 9) : ZMod 2 :=
  let d := scr + nn
  match u.val with
  | 0 => d + k0
  | 1 => k0 * d
  | 8 => k3 * d
  | _ => 0

private theorem z2_stageA_oneHot (d k0 k3 : ZMod 2) (hnb : ¬(k0 = 1 ∧ k3 = 1)) :
    let v :=
        ((0 + if d = 1 then 2 ^ 0 else 0) + if k0 = 1 then 2 ^ 1 else 0) + if k3 =
        1 then 2 ^ 2 else 0
    v < 6 ∧
    (0 : ZMod 2) + (if v = 3 then 1 else 0) = k0 * d ∧
    (0 : ZMod 2) + (if v = 5 then 1 else 0) = k3 * d := by
  revert d k0 k3 hnb; decide

private theorem cStageAGather_mulVec_ket {n : ℕ} (rScr40 : QRegister 40 n)
    (rBasis9 : QRegister 9 n) (hBS : rBasis9.DisjointWires rScr40) (η : BitAssignment n) :
    (cStageAGather rScr40 rBasis9 hBS).eval.1.mulVec (ket η) =
      let wOut6 := kpOut6 rScr40
      ket (Function.update
        (Function.update η (rBasis9 ⟨1, by decide⟩)
          (η (rBasis9 ⟨1, by decide⟩) + η (wOut6 ⟨3, by decide⟩)))
        (rBasis9 ⟨8, by decide⟩)
        (η (rBasis9 ⟨8, by decide⟩) + η (wOut6 ⟨5, by decide⟩))) := by
  dsimp only [cStageAGather]; rw [eval_seq_mulVec, ket_CNOT, ket_CNOT]
  have n5_1 : kpOut6 rScr40 ⟨5, by decide⟩ ≠ rBasis9 ⟨1, by decide⟩ := (disj_ne hBS _ _).symm
  have n8_1 : rBasis9 ⟨8, by decide⟩ ≠ rBasis9 ⟨1, by decide⟩ :=
      rBasis9_ne_of_ne rBasis9 (by decide)
  simp only [Function.update_of_ne n5_1, Function.update_of_ne n8_1]

theorem pb_pos33 : 0 < 33 := by decide

def fOh19 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n) (u : Fin 19) : Wire n :=
  if hu9 : u.val < 9 then rBasis9 ⟨u.val, hu9⟩
  else rScr40 ⟨u.val - 9, by omega⟩

def rOh19Of {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hBS : rBasis9.DisjointWires rScr40) : QRegister 19 n :=
  ⟨⟨fOh19 rBasis9 rScr40, fun a b e ↦ Fin.ext (by
    dsimp only [fOh19] at e
    by_cases ha9 : a.val < 9 <;> by_cases hb9 : b.val < 9 <;>
      simp only [ha9, hb9, ↓reduceDIte] at e
    · have hv := congrArg Fin.val (rBasis9.wires.injective e); dsimp at hv; omega
    · exact absurd e (disj_ne hBS _ _)
    · exact absurd e.symm (disj_ne hBS _ _)
    · have hv := congrArg Fin.val (rScr40.wires.injective e); dsimp at hv; omega)⟩⟩

theorem copy30_disj_oh19 {n : ℕ} {rBasis9 : QRegister 9 n} {rCopy30 : QRegister 30 n}
    {rScr40 : QRegister 40 n} (hBC : rBasis9.DisjointWires rCopy30)
    (hBS : rBasis9.DisjointWires rScr40) (hCS : rCopy30.DisjointWires rScr40) :
    rCopy30.DisjointWires (rOh19Of rBasis9 rScr40 hBS) :=
  disj_of_ne fun j u e ↦ by
    change rCopy30 j = fOh19 rBasis9 rScr40 u at e; dsimp only [fOh19] at e; split_ifs at e
    · exact disj_ne hBC _ _ e.symm
    · exact disj_ne hCS _ _ e

theorem oh19_disj_yHi33 {n : ℕ} {rBasis9 : QRegister 9 n} {rScr40 : QRegister 40 n}
    {rYHi33 : QRegister 33 n} (hBS : rBasis9.DisjointWires rScr40)
    (hBY : rBasis9.DisjointWires rYHi33) (hSY : rScr40.DisjointWires rYHi33) :
    (rOh19Of rBasis9 rScr40 hBS).DisjointWires rYHi33 :=
  disj_of_ne fun u b2 e ↦ by
    change fOh19 rBasis9 rScr40 u = rYHi33 b2 at e; dsimp only [fOh19] at e; split_ifs at e
    · exact disj_ne hBY _ _ e
    · exact disj_ne hSY _ _ e

def unshiftRowPairs30K9 {n : ℕ} (rCopy30 : QRegister 30 n) (rOh19 : QRegister 19 n)
    (hDisj : rCopy30.DisjointWires rOh19) (b2 : ℕ) : ℕ → List (WirePair n)
  | 0 => []
  | r + 1 =>
      let rest := unshiftRowPairs30K9 rCopy30 rOh19 hDisj b2 r
      if h : r < 10 ∧ 3 ≤ b2 + r ∧ b2 + r - 3 < 30 then
        ⟨rCopy30 ⟨b2 + r - 3, h.2.2⟩, ⟨rOh19 ⟨9 + r, by omega⟩, disj_ne hDisj _ _⟩⟩ :: rest
      else rest

theorem unshiftRowPairs30K9_mem {n : ℕ} (rCopy30 : QRegister 30 n)
    (rOh19 : QRegister 19 n) (hDisj : rCopy30.DisjointWires rOh19) (b2 : ℕ) :
    ∀ (m : ℕ) (p : WirePair n), p ∈ unshiftRowPairs30K9 rCopy30 rOh19 hDisj b2 m →
      (∃ c, rCopy30 c = p.1) ∧ (∃ u, rOh19 u = p.2.1)
  | 0, _, hp => nomatch hp
  | r + 1, p, hp => by
      dsimp only [unshiftRowPairs30K9] at hp; split_ifs at hp
      · rcases List.mem_cons.mp hp with rfl | htl
        · exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
        · exact unshiftRowPairs30K9_mem rCopy30 rOh19 hDisj b2 r p htl
      · exact unshiftRowPairs30K9_mem rCopy30 rOh19 hDisj b2 r p hp

theorem unshiftRowPairs30K9_parity {n : ℕ} (rCopy30 : QRegister 30 n)
    (rOh19 : QRegister 19 n) (hDisj : rCopy30.DisjointWires rOh19)
    (b2 x32 kp : ℕ) (hx : x32 < 2 ^ 32) (β : BitAssignment n)
    (hCopy : ∀ c : Fin 30, β (rCopy30 c) = if x32.testBit (2 + c.val) then 1 else 0)
    (hOh : ∀ r : Fin 10, β (rOh19 ⟨9 + r.val, by omega⟩) = if r.val = kp then 1 else 0) :
    ∀ m ≤ 10,
      czPairsParity (unshiftRowPairs30K9 rCopy30 rOh19 hDisj b2 m) β =
        if kp < m ∧ (((mask30 x32) <<< 4) >>> kp).testBit (3 + b2) then 1 else 0
  | 0, _ => by simp [unshiftRowPairs30K9, czPairsParity]
  | r + 1, hm => by
      have hr10 : r < 10 := by omega
      have ih := unshiftRowPairs30K9_parity rCopy30 rOh19 hDisj b2 x32 kp hx β hCopy hOh r hr10.le
      have hOhR := hOh ⟨r, hr10⟩
      dsimp only [unshiftRowPairs30K9]
      by_cases hrk : r = kp
      · subst hrk
        have hih0 : czPairsParity (unshiftRowPairs30K9 rCopy30 rOh19 hDisj b2 r) β = 0 := by
          simpa only [lt_irrefl, false_and, ↓reduceIte] using ih
        rw [itePos rfl] at hOhR
        by_cases hbnd : 3 ≤ b2 + r ∧ b2 + r - 3 < 30
        · rw [ditePos ⟨hr10, hbnd⟩, czPairsParity, hOhR, mul_one, hih0, add_zero,
            hCopy ⟨b2 + r - 3, hbnd.2⟩, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
            mask30_testBit]
          simp only [Nat.lt_succ_self, true_and, show 4 ≤ r + (3 + b2) by omega,
            show r + (3 + b2) - 4 = 2 + (b2 + r - 3) by omega,
            show 2 ≤ 2 + (b2 + r - 3) by omega, decide_true, Bool.true_and]
        · have hf : (((mask30 x32) <<< 4) >>> r).testBit (3 + b2) = false := by
            rw [Nat.testBit_shiftRight, Nat.testBit_shiftLeft, mask30_testBit]
            by_cases h3 : 3 ≤ b2 + r
            · simp only [show 4 ≤ r + (3 + b2) by omega, show 2 ≤ r + (3 + b2) - 4 by omega,
                decide_true, Bool.true_and]
              exact Nat.testBit_eq_false_of_lt
                (hx.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
            · by_cases h4 : 4 ≤ r + (3 + b2) <;>
                simp only [h4, show ¬(2 ≤ r + (3 + b2) - 4) by omega,
                  decide_true, decide_false, Bool.true_and, Bool.false_and]
          rw [diteNeg (fun h ↦ hbnd h.2), hih0]
          simp only [hf, Bool.false_eq_true, and_false, ↓reduceIte]
      · rw [iteNeg hrk] at hOhR
        have hkp : (kp < r + 1) = (kp < r) := propext ⟨by omega, Nat.lt_succ_of_lt⟩
        by_cases h : r < 10 ∧ 3 ≤ b2 + r ∧ b2 + r - 3 < 30
        · simp only [ditePos h, czPairsParity, hOhR, mul_zero, zero_add, ih, hkp]
        · simp only [diteNeg h, ih, hkp]

def pUnshift30ZeroUnload_33_k9 {Var : Type} {n : ℕ} (v : Var) (rBasis9 : QRegister 9 n)
    (rCopy30 : QRegister 30 n) (rScr40 : QRegister 40 n) (rYHi33 : QRegister 33 n)
    (hBC : rBasis9.DisjointWires rCopy30) (hBS : rBasis9.DisjointWires rScr40)
    (hCS : rCopy30.DisjointWires rScr40) : DynamicCircuit Var n :=
  let rOh19 := rOh19Of rBasis9 rScr40 hBS
  let hCO := copy30_disj_oh19 hBC hBS hCS
  wrapDynOnReg v rOh19 (decodePrimTree 18 oh10ZeroTree)
    (xUnloadChunkCzPairsSeqDyn v (outWireOfReg pb_pos33 rYHi33) 0
      (fun b2 ↦ unshiftRowPairs30K9 rCopy30 rOh19 hCO b2 10) (.circuit .identity) 33)

theorem subspaceStep_pUnshift30ZeroUnload_33_k9 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (rBasis9 : QRegister 9 n)
    (rCopy30 : QRegister 30 n) (rScr40 : QRegister 40 n) (rYHi33 : QRegister 33 n)
    (hBC : rBasis9.DisjointWires rCopy30) (hBS : rBasis9.DisjointWires rScr40)
    (hCS : rCopy30.DisjointWires rScr40) (hBY : rBasis9.DisjointWires rYHi33)
    (hCY : rCopy30.DisjointWires rYHi33) (hSY : rScr40.DisjointWires rYHi33)
    (st stWB : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (x32Fn kpFn : BitAssignment n → ℕ) (hx32 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → x32Fn δ <
    2 ^ 32) (hkpLe : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → kpFn δ ≤ 9)
    (hCopy : ∀ (δ : BitAssignment n) (c : Fin 30), (∀ k : Fin W, δ (rWork k) = 0) →
    st δ (rCopy30 c) = if (x32Fn δ).testBit (2 + c.val) then 1 else 0)
    (hBasis : ∀ (δ : BitAssignment n) (u : Fin 9), (∀ k : Fin W, δ (rWork k) = 0) →
    (st δ (rBasis9 u) == 1) = (kpBasis9Code (kpFn δ)).testBit u.val)
    (hScr10 : ∀ (δ : BitAssignment n) (u : Fin 40), u.val < 10 → (∀ k : Fin W, δ (rWork k) = 0) →
    st δ (rScr40 u) = 0) (hY0 : ∀ (δ : BitAssignment n) (b2 : Fin 33), (∀ k : Fin W, δ (rWork k) =
    0) → st δ (rYHi33 b2) = 0) (hWB : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stWB δ =
    writeReg (st δ) rYHi33 (fun b2 ↦ if (((mask30 (x32Fn δ)) <<< 4) >>> kpFn δ).testBit (3 +
    b2.val) then 1 else 0)) : SubspaceStep (mkKetOpW rWork stWB ph) (mkKetOpW rWork st ph)
    (pUnshift30ZeroUnload_33_k9 v rBasis9 rCopy30 rScr40 rYHi33 hBC hBS hCS) ∧
    (pUnshift30ZeroUnload_33_k9 v rBasis9 rCopy30 rScr40 rYHi33 hBC hBS hCS).count .T = 0 ∧
    (pUnshift30ZeroUnload_33_k9 v rBasis9 rCopy30 rScr40 rYHi33 hBC hBS hCS).count .TOFF = 0 ∧
    (∀ S : Wire n → Prop, (∀ u, S (rBasis9 u)) → (∀ c, S (rCopy30 c)) → (∀ u, S (rScr40 u)) →
    (∀ b2, S (rYHi33 b2)) →
    DynWires S (pUnshift30ZeroUnload_33_k9 v rBasis9 rCopy30 rScr40 rYHi33 hBC hBS hCS)) := by
  let rOh19 := rOh19Of rBasis9 rScr40 hBS
  let hCO := copy30_disj_oh19 hBC hBS hCS
  let hOY := oh19_disj_yHi33 hBS hBY hSY
  let cp : ComputeProg 19 := decodePrimTree 18 oh10ZeroTree
  let outW := outWireOfReg pb_pos33 rYHi33
  let pairsFn (b2 : ℕ) := unshiftRowPairs30K9 rCopy30 rOh19 hCO b2 10
  let bitFn (b2 : ℕ) := czPairsParity (pairsFn b2)
  rcases decodePrimTree_spec 18 oh10ZeroTree 0 0 with ⟨hv, _, ha⟩
  have hPairsMem (b2 : ℕ) (p : WirePair n) := unshiftRowPairs30K9_mem rCopy30 rOh19 hCO b2 10 p
  have hOutDisj (s : ℕ) : (∀ c, rCopy30 c ≠ outW s) ∧ ∀ u, rOh19 u ≠ outW s :=
    ⟨fun c ↦ disj_ne hCY c _, fun u ↦ disj_ne hOY u _⟩
  have hf (i : ℕ) := czPairsParity_indep _ (pairsFn i) fun p hp ↦
    ⟨(hPairsMem i p hp).1.choose_spec ▸ (hOutDisj (0 + i)).1 _,
     (hPairsMem i p hp).2.choose_spec ▸ (hOutDisj (0 + i)).2 _⟩
  set stPost := fun δ ↦ stepCB rOh19 cp.fwdBits (st δ)
  have hPostOut0 (s : ℕ) (_ : s < 33) (δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) :
      stPost δ (outW s) = 0 :=
    (writeReg_apply_of_not_mem _ _ _ _ fun ⟨u, hu⟩ ↦ disj_ne hOY u _ hu).trans (hY0 δ _ hz)
  have outInj {a b} (ha : a < 33) (hb : b < 33) (e : outW a = outW b) : a = b := by
    simpa only [outW, outWireOfReg, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using
      congrArg Fin.val (rYHi33.wires.injective e)
  let cXor := PhotochemistrySolution.XMeasChunkQromUnld.chunkXorOp outW 0 bitFn hf
  let updP (δ) := updPrefix pb_pos33 rYHi33 (stPost δ) (fun i ↦ bitFn i (stPost δ))
  have hChunkEq (m : ℕ) (hm : m ≤ 33) :
      cXor m * mkKetOpW rWork stPost ph = mkKetOpW rWork (fun δ ↦ updP δ m) ph := by
    induction m with
    | zero => exact Matrix.one_mul _
    | succ s ih =>
        change ((xorWireUnitary (outW (0 + s)) (bitFn s) (hf s)).1 * cXor s) * _ = _
        rw [Matrix.mul_assoc, ih (Nat.le_of_succ_le hm)]
        refine matrix_ext_ket fun δ ↦ ?_
        rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
        split_ifs with hz
        · rw [Matrix.mulVec_smul, xorWireUnitary_mulVec_ket, Nat.zero_add]
          congr 2
          have hPf (w : Wire n) (t : ℕ) (hw : ∀ q < t, w ≠ outW q) : updP δ t w = stPost δ w := by
            induction t with
            | zero => rfl
            | succ q ihs =>
                exact (Function.update_of_ne (hw q (Nat.lt_succ_self q)) _ _).trans
                  (ihs fun r hr ↦ hw r (Nat.lt_succ_of_lt hr))
          have hEqP (ps : List (WirePair n))
              (hps : ∀ p ∈ ps, (∃ c, rCopy30 c = p.1) ∧ ∃ u, rOh19 u = p.2.1) :
              czPairsParity ps (updP δ s) = czPairsParity ps (stPost δ) := by
            induction ps with
            | nil => rfl
            | cons p rest ihp =>
                obtain ⟨⟨c, hc⟩, ⟨u, hu⟩⟩ := hps p List.mem_cons_self
                simp only [czPairsParity, ← hc, ← hu,
                  hPf (rCopy30 c) s fun q _ ↦ (hOutDisj q).1 c,
                  hPf (rOh19 u) s fun q _ ↦ (hOutDisj q).2 u,
                  ihp fun p' hp' ↦ hps p' (List.mem_cons_of_mem p hp')]
          rw [hPf (outW s) s fun q hq e ↦ Nat.ne_of_lt hq (outInj (hq.trans hm) hm e.symm),
            hPostOut0 s hm δ hz, zero_add, show bitFn s _ = _ from hEqP _ (hPairsMem s)]; rfl
        · rw [Matrix.mulVec_zero]
  have hPreEq : mkKetOpW rWork (fun δ ↦ stepCB rOh19 cp.fwdBits (stWB δ)) ph =
      cXor 33 * mkKetOpW rWork stPost ph := by
    rw [hChunkEq 33 le_rfl]
    refine mkKetOpW_congr rWork (fun δ hz ↦ ?_) (fun _ _ ↦ rfl)
    dsimp only [updP]
    rw [updPrefix_eq_writeReg, hWB δ hz, stepCB_writeReg_comm rOh19 rYHi33 hOY]
    refine congrArg _ (funext fun j ↦ ?_)
    have hPostC (c : Fin 30) :
        stPost δ (rCopy30 c) = if (x32Fn δ).testBit (2 + c.val) then 1 else 0 :=
      (writeReg_apply_of_not_mem _ _ _ _ fun ⟨u, hu⟩ ↦ disj_ne hCO c u hu.symm).trans
        (hCopy δ c hz)
    have hPostOh (r : Fin 10) :
        stPost δ (rOh19 ⟨9 + r.val, by omega⟩) = if r.val = kpFn δ then 1 else 0 := by
      dsimp only [stPost, cp]
      rw [stepCB_decodePrimTree_apply]
      have hNat : natOfZModBits 19 (fun u ↦ st δ (rOh19 u)) = kpBasis9Code (kpFn δ) := by
        simpa only [Nat.add_zero, Nat.zero_shiftLeft, Nat.xor_zero] using
          natOfZModBits_split9 (N := 19) (B := 0) (by decide) (fun u ↦ st δ (rOh19 u))
            (kpBasis9Code (kpFn δ)) 0 (kpBasis9Code_lt512 (hkpLe δ hz)) (by decide)
            (fun u ↦ by
              rw [show rOh19 ⟨u.val, by omega⟩ = rBasis9 u from ditePos u.isLt]
              exact hBasis δ u hz)
            (fun q ↦ Fin.elim0 q) fun u hu ↦
              (congrArg (st δ) (show rOh19 u = rScr40 ⟨u.val - 9, by omega⟩ from
                diteNeg (by omega))).trans (hScr10 δ ⟨u.val - 9, by omega⟩
                  (show u.val - 9 < 10 by omega) hz)
      rw [hNat, (oh10ZeroTree_eval (hkpLe δ hz)).2 r.val r.isLt]
      by_cases hrk : r.val = kpFn δ <;> simp [hrk]
    simpa only [Nat.lt_succ_of_le (hkpLe δ hz), true_and] using (unshiftRowPairs30K9_parity rCopy30
      rOh19 hCO j.val (x32Fn δ) (kpFn δ) (hx32 δ hz) (stPost δ) hPostC hPostOh 10 le_rfl).symm
  let pMid := xUnloadChunkCzPairsSeqDyn v outW 0 pairsFn (.circuit .identity) 33
  have hMidStep : SubspaceStep
      (mkKetOpW rWork (fun δ ↦ stepCB rOh19 cp.fwdBits (stWB δ)) ph)
      (mkKetOpW rWork stPost ph) pMid := by
    rw [hPreEq]
    exact subspaceStep_xUnloadChunkCzPairsSeqDyn v outW 0 pairsFn bitFn hf (fun _ _ ↦ rfl)
      (.circuit .identity) (mkKetOpW rWork stPost ph) (mkKetOpW rWork stPost ph)
      (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ .identity)
        (by simp [Circuit.eval_identity])) 33
      (fun a ha b hb hab e ↦
        hab (outInj (by omega) (by omega) (by simpa only [Nat.zero_add] using e)))
      fun i hi ↦ projBit_zero_mkKetOpW rWork _ stPost ph fun δ hz ↦ by
        simpa only [Nat.zero_add] using hPostOut0 i hi δ hz
  have hCln0 {stX : BitAssignment n → BitAssignment n} (u : Wire 19) (hu : u ∈ maskFinset 19 0)
      (δ : BitAssignment n) (_ : ∀ k : Fin W, δ (rWork k) = 0) : stX δ (rOh19 u) = 0 :=
    absurd (mem_maskFinset.mp hu) (by simp [Nat.zero_testBit])
  obtain ⟨hWrap, htW, hfW, hDynW⟩ := subspaceStep_wrapOnReg_vprog2 v rWork rOh19
    (maskFinset 19 0) cp 0 (maskFinset_zero 19 ▸ StructuredCB.validProg_of_validProgMask
      (hv.trans oh10ZeroTree_check.1)) (ha.trans oh10ZeroTree_check.2) stWB st ph ph pMid
    hCln0 hCln0 hMidStep
  obtain ⟨htMid, hfMid⟩ := count_xUnloadChunkCzPairsSeqDyn v outW 0 pairsFn (.circuit .identity) 33
  refine ⟨hWrap, htW.trans (by rw [show pMid.count .T = _ from htMid]; rfl),
    hfW.trans (by rw [show pMid.count .TOFF = _ from hfMid]; rfl),
    fun S hrB hrC hrS hrY ↦ ?_⟩
  have hrOhS (u) : S (rOh19 u) := by
    change S (fOh19 rBasis9 rScr40 u)
    dsimp only [fOh19]
    split_ifs <;> first | exact hrB _ | exact hrS _
  exact hDynW S hrOhS (dynWires_xUnloadChunk v outW 0 pairsFn (fun i ↦ hrY _)
    (fun j p hp ↦ ⟨(hPairsMem j p hp).1.choose_spec ▸ hrC _,
      (hPairsMem j p hp).2.choose_spec ▸ hrOhS _⟩) 33)

/-! ### 5. Parametric `KpBasis9Pkg 24` & Turnkey `312-T` / `0-T` Coupled `Stage4NoMuxK9` Wrappers -/

structure KpBasis9Pkg (tBasis : ℕ) where
  pFwd : {Var : Type} → {n : ℕ} → Var →
    (wScr wNN : Wire n) → (rK4 : QRegister 4 n) →
    (rBasis9 : QRegister 9 n) → (rScr40 : QRegister 40 n) →
    (∀ u, wScr ≠ rBasis9 u) → (∀ u, wNN ≠ rBasis9 u) →
    rK4.DisjointWires rBasis9 → rBasis9.DisjointWires rScr40 →
    DynamicCircuit Var n
  pRev : {Var : Type} → {n : ℕ} → Var →
    (wScr wNN : Wire n) → (rK4 : QRegister 4 n) → (rBasis9 : QRegister 9 n) →
    (∀ u, wScr ≠ rBasis9 u) → (∀ u, wNN ≠ rBasis9 u) →
    rK4.DisjointWires rBasis9 →
    DynamicCircuit Var n
  fwd_counts_wires : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9) (hBS : rBasis9.DisjointWires rScr40),
    S wScr → S wNN → (∀ i, S (rK4 i)) → (∀ u, S (rBasis9 u)) → (∀ u, S (rScr40 u)) →
    (pFwd v wScr wNN rK4 rBasis9 rScr40 hScrB hNNB hKB hBS).count .T = tBasis ∧
    (pFwd v wScr wNN rK4 rBasis9 rScr40 hScrB hNNB hKB hBS).count .TOFF = 0 ∧
    DynWires S (pFwd v wScr wNN rK4 rBasis9 rScr40 hScrB hNNB hKB hBS)
  rev_counts_wires : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9),
    S wScr → S wNN → (∀ i, S (rK4 i)) → (∀ u, S (rBasis9 u)) →
    (pRev v wScr wNN rK4 rBasis9 hScrB hNNB hKB).count .T = 0 ∧
    (pRev v wScr wNN rK4 rBasis9 hScrB hNNB hKB).count .TOFF = 0 ∧
    DynWires S (pRev v wScr wNN rK4 rBasis9 hScrB hNNB hKB)
  fwd_step : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (_hScrS : ∀ u, wScr ≠ rScr40 u) (_hNNS : ∀ u, wNN ≠ rScr40 u)
    (hKB : rK4.DisjointWires rBasis9) (_hKS : rK4.DisjointWires rScr40)
    (hBS : rBasis9.DisjointWires rScr40)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 4 (fun i ↦ st δ (rK4 i)) ≤ 8) →
    (∀ (δ : BitAssignment n) (u : Fin 9),
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rBasis9 u) = 0) →
    (∀ (δ : BitAssignment n) (u : Fin 40), u.val < 14 →
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rScr40 u) = 0) →
    SubspaceStep
      (mkKetOpW rWork st ph)
      (mkKetOpW rWork (fun δ ↦ kpStep14 wScr wNN rK4 rBasis9 (st δ)) ph)
      (pFwd v wScr wNN rK4 rBasis9 rScr40 hScrB hNNB hKB hBS)
  rev_step : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ (δ : BitAssignment n) (u : Fin 9),
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rBasis9 u) = 0) →
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ kpStep14 wScr wNN rK4 rBasis9 (st δ)) ph)
      (mkKetOpW rWork st ph)
      (pRev v wScr wNN rK4 rBasis9 hScrB hNNB hKB)

section
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (WInj mkVecOp
    mkVecOp_mulVec_ket wTreePrefix count_wTreePrefix cw_wTreePrefix wShiftLevels count_wShiftLevels
    dw_wShiftLevels wSuperOp subspaceStep_wShiftLevels subspaceStep_mul_right wUncompTreeDyn)
abbrev kpIdxB1 {n : ℕ} (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n) : Fin 3 → Wire n
  | ⟨0, _⟩ => rK4 ⟨1, by decide⟩
  | ⟨1, _⟩ => rBasis9 ⟨0, by decide⟩
  | ⟨2, _⟩ => rBasis9 ⟨1, by decide⟩

abbrev kpOh4 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n) : Fin 4 → Wire n
  | ⟨0, _⟩ => rBasis9 ⟨2, by decide⟩
  | ⟨1, _⟩ => rBasis9 ⟨4, by decide⟩
  | ⟨2, _⟩ => rScr40 ⟨12, by decide⟩
  | ⟨3, _⟩ => rScr40 ⟨13, by decide⟩

abbrev kpSh1 {n : ℕ} (rK4 : QRegister 4 n) : Fin 1 → Wire n :=
  fun _ ↦ rK4 ⟨2, by decide⟩

abbrev kpW5x2 {n : ℕ} (rScr40 : QRegister 40 n) (b : Fin 5) (p : Fin (2 ^ 1)) : Wire n :=
  rScr40 ⟨2 + 2 * b.val + p.val, by have := b.isLt; have := p.isLt; omega⟩

theorem wInj_kpW5x2 {n : ℕ} (rScr40 : QRegister 40 n) : WInj (kpW5x2 rScr40) :=
  fun b₁ p₁ b₂ p₂ heq ↦ by
    have hv := congrArg Fin.val (rScr40.wires.injective heq)
    have := p₁.isLt; have := p₂.isLt; dsimp at hv
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

theorem kpW5x2_ne_qEnc {n : ℕ} (rScr40 : QRegister 40 n) (b : Fin 5) (p : Fin (2 ^ 1)) :
    kpW5x2 rScr40 b p ≠ rScr40 ⟨1, by decide⟩ :=
  rScr40_ne_of_ne rScr40 fun e ↦ by
    have hv := congrArg Fin.val e; dsimp at hv; omega

theorem kpOh4_ne_w5 {n : ℕ} {rBasis9 : QRegister 9 n} {rScr40 : QRegister 40 n}
    (hBS : rBasis9.DisjointWires rScr40) (t : Fin 4) (b : Fin 5)
    (p : Fin (2 ^ 1)) : kpOh4 rBasis9 rScr40 t ≠ kpW5x2 rScr40 b p := by
  fin_cases t <;> first
    | exact disj_ne hBS _ _
    | exact rScr40_ne_of_ne rScr40 fun e ↦
        (by decide : ∀ (a : Fin 5) (q : Fin (2 ^ 1)), 12 ≠ 2 + 2 * a.val + q.val) b p
          (congrArg Fin.val e)
    | exact rScr40_ne_of_ne rScr40 fun e ↦
        (by decide : ∀ (a : Fin 5) (q : Fin (2 ^ 1)), 13 ≠ 2 + 2 * a.val + q.val) b p
          (congrArg Fin.val e)

theorem wRouterDisj_kpB1 {n : ℕ} {rK4 : QRegister 4 n} {rBasis9 : QRegister 9 n}
    {rScr40 : QRegister 40 n} (hKS : rK4.DisjointWires rScr40)
    (hBS : rBasis9.DisjointWires rScr40) :
    WRouterDisj (rScr40 ⟨0, by decide⟩) (kpIdxB1 rK4 rBasis9) (kpOut6 rScr40)
      (rScr40 ⟨1, by decide⟩) where
  has_ne_out j := rScr40_ne_of_ne rScr40 fun e ↦
    (by decide : ∀ k : Fin 6, 0 ≠ 2 + k.val) j (congrArg Fin.val e)
  has_ne_q := rScr40_ne_of_ne rScr40 (by decide)
  idx_ne_out d _ := by fin_cases d <;> first | exact disj_ne hKS _ _ | exact disj_ne hBS _ _
  idx_ne_q d := by fin_cases d <;> first | exact disj_ne hKS _ _ | exact disj_ne hBS _ _
  out_inj i j hij := rScr40_ne_of_ne rScr40 fun e ↦
    (by decide : ∀ a b : Fin 6, a ≠ b → 2 + a.val ≠ 2 + b.val) i j hij (congrArg Fin.val e)
  out_ne_q j := rScr40_ne_of_ne rScr40 fun e ↦
    (by decide : ∀ k : Fin 6, 2 + k.val ≠ 1) j (congrArg Fin.val e)

def KpK2DisjScr12 {n : ℕ} (rK4 : QRegister 4 n) (rScr40 : QRegister 40 n) : Prop :=
  (∀ d : Fin 1, kpSh1 rK4 d ≠ rScr40 ⟨1, by decide⟩) ∧
  (∀ (d : Fin 1) (b : Fin 5) (p : Fin (2 ^ 1)), kpSh1 rK4 d ≠ kpW5x2 rScr40 b p)

instance instDecKpK2DisjScr12 {n : ℕ} (rK4 : QRegister 4 n) (rScr40 : QRegister 40 n) :
    Decidable (KpK2DisjScr12 rK4 rScr40) := by unfold KpK2DisjScr12; infer_instance
def cStageB1Gather {n : ℕ} (rScr40 : QRegister 40 n) (rBasis9 : QRegister 9 n)
    (hBS : rBasis9.DisjointWires rScr40) : Circuit n :=
  Circuit.CNOT (kpOut6 rScr40 ⟨3, by decide⟩) (rBasis9 ⟨4, by decide⟩) (disj_ne hBS _ _).symm ;;ᶜ
  Circuit.CNOT (kpOut6 rScr40 ⟨5, by decide⟩) (rBasis9 ⟨2, by decide⟩) (disj_ne hBS _ _).symm

def cStageB2Mid {n : ℕ} (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (rScr40 : QRegister 40 n) (hKB : rK4.DisjointWires rBasis9)
    (hBS : rBasis9.DisjointWires rScr40) : Circuit n :=
  Circuit.CNOT (rK4 ⟨1, by decide⟩) (rBasis9 ⟨1, by decide⟩) (disj_ne hKB _ _) ;;ᶜ
  Circuit.CNOT (rBasis9 ⟨0, by decide⟩) (rScr40 ⟨12, by decide⟩) (disj_ne hBS _ _) ;;ᶜ
  Circuit.CNOT (rBasis9 ⟨4, by decide⟩) (rScr40 ⟨12, by decide⟩) (disj_ne hBS _ _) ;;ᶜ
  Circuit.CNOT (rBasis9 ⟨1, by decide⟩) (rScr40 ⟨13, by decide⟩) (disj_ne hBS _ _) ;;ᶜ
  Circuit.CNOT (rBasis9 ⟨4, by decide⟩) (rScr40 ⟨13, by decide⟩) (disj_ne hBS _ _)

def cRootInit5 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hBS : rBasis9.DisjointWires rScr40) : Circuit n :=
  let uOh := kpOh4 rBasis9 rScr40
  let w5 := kpW5x2 rScr40
  let p0 : Fin (2 ^ 1) := ⟨0, by decide⟩
  Circuit.X (w5 ⟨0, by decide⟩ p0) ;;ᶜ
  Circuit.CNOT (uOh ⟨0, by decide⟩) (w5 ⟨0, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨0, by decide⟩) (w5 ⟨1, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨1, by decide⟩) (w5 ⟨0, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨1, by decide⟩) (w5 ⟨2, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨2, by decide⟩) (w5 ⟨0, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨2, by decide⟩) (w5 ⟨3, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨3, by decide⟩) (w5 ⟨0, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨3, by decide⟩) (w5 ⟨4, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _)

def cRootUninit5 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hBS : rBasis9.DisjointWires rScr40) : Circuit n :=
  let uOh := kpOh4 rBasis9 rScr40
  let w5 := kpW5x2 rScr40
  let p0 : Fin (2 ^ 1) := ⟨0, by decide⟩
  Circuit.CNOT (uOh ⟨3, by decide⟩) (w5 ⟨4, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨3, by decide⟩) (w5 ⟨0, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨2, by decide⟩) (w5 ⟨3, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨2, by decide⟩) (w5 ⟨0, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨1, by decide⟩) (w5 ⟨2, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨1, by decide⟩) (w5 ⟨0, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨0, by decide⟩) (w5 ⟨1, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.CNOT (uOh ⟨0, by decide⟩) (w5 ⟨0, by decide⟩ p0) (kpOh4_ne_w5 hBS _ _ _) ;;ᶜ
  Circuit.X (w5 ⟨0, by decide⟩ p0)

def cStageB2Gather {n : ℕ} (rScr40 : QRegister 40 n) (rBasis9 : QRegister 9 n)
    (hBS : rBasis9.DisjointWires rScr40) : Circuit n :=
  let w5 := kpW5x2 rScr40
  let p1 : Fin (2 ^ 1) := ⟨1, by decide⟩
  Circuit.CNOT (w5 ⟨1, by decide⟩ p1) (rBasis9 ⟨3, by decide⟩) (disj_ne hBS _ _).symm ;;ᶜ
  Circuit.CNOT (w5 ⟨2, by decide⟩ p1) (rBasis9 ⟨5, by decide⟩) (disj_ne hBS _ _).symm ;;ᶜ
  Circuit.CNOT (w5 ⟨2, by decide⟩ p1) (rBasis9 ⟨6, by decide⟩) (disj_ne hBS _ _).symm ;;ᶜ
  Circuit.CNOT (w5 ⟨2, by decide⟩ p1) (rBasis9 ⟨7, by decide⟩) (disj_ne hBS _ _).symm ;;ᶜ
  Circuit.CNOT (w5 ⟨3, by decide⟩ p1) (rBasis9 ⟨5, by decide⟩) (disj_ne hBS _ _).symm ;;ᶜ
  Circuit.CNOT (w5 ⟨4, by decide⟩ p1) (rBasis9 ⟨6, by decide⟩) (disj_ne hBS _ _).symm

def cStageB2Post {n : ℕ} (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (rScr40 : QRegister 40 n) (hKB : rK4.DisjointWires rBasis9)
    (hBS : rBasis9.DisjointWires rScr40) : Circuit n :=
  Circuit.CNOT (rBasis9 ⟨4, by decide⟩) (rScr40 ⟨12, by decide⟩) (disj_ne hBS _ _) ;;ᶜ
  Circuit.CNOT (rBasis9 ⟨0, by decide⟩) (rScr40 ⟨12, by decide⟩) (disj_ne hBS _ _) ;;ᶜ
  Circuit.CNOT (rBasis9 ⟨4, by decide⟩) (rScr40 ⟨13, by decide⟩) (disj_ne hBS _ _) ;;ᶜ
  Circuit.CNOT (rBasis9 ⟨1, by decide⟩) (rScr40 ⟨13, by decide⟩) (disj_ne hBS _ _) ;;ᶜ
  Circuit.X (rScr40 ⟨0, by decide⟩) ;;ᶜ
  Circuit.CNOT (rK4 ⟨2, by decide⟩) (rBasis9 ⟨2, by decide⟩) (disj_ne hKB _ _) ;;ᶜ
  Circuit.CNOT (rK4 ⟨3, by decide⟩) (rBasis9 ⟨3, by decide⟩) (disj_ne hKB _ _)

def pStageB2_5x2 {Var : Type} {n : ℕ} (v : Var) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (rScr40 : QRegister 40 n) (hBS : rBasis9.DisjointWires rScr40) : DynamicCircuit Var n :=
  let qEnc := rScr40 ⟨1, by decide⟩
  let w5 := kpW5x2 rScr40
  let hw5 := wInj_kpW5x2 rScr40
  if hd : KpK2DisjScr12 rK4 rScr40 then
    .seq (.circuit (cRootInit5 rBasis9 rScr40 hBS ;;ᶜ wTreePrefix 5 1 w5 hw5 1 le_rfl))
      (.seq (wShiftLevels v 5 1 (kpSh1 rK4) w5 qEnc hw5 (kpW5x2_ne_qEnc rScr40) hd.1 1
          le_rfl)
        (.seq (.circuit (cStageB2Gather rScr40 rBasis9 hBS))
          (wUncompTreeDyn v 5 1 (kpSh1 rK4) w5 hw5 hd.2
            (.circuit (cRootUninit5 rBasis9 rScr40 hBS)) 1 le_rfl)))
  else
    .circuit (wTreePrefix 5 1 w5 hw5 1 le_rfl)

/--
Forward `22-T` , `0-.TOFF` three-stage W-state `kpBasis9` loader (`rScr40[0..13]` used cleanly &
returned `|0⟩` ).
-/
def pKpBasis9Fwd22 {Var : Type} {n : ℕ} (v : Var) (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n) (hScrB : ∀ u, wScr ≠ rBasis9 u)
    (hNNB : ∀ u, wNN ≠ rBasis9 u) (hKB : rK4.DisjointWires rBasis9)
    (hBS : rBasis9.DisjointWires rScr40) : DynamicCircuit Var n :=
  let wHas := rScr40 ⟨0, by decide⟩
  let qEnc := rScr40 ⟨1, by decide⟩
  .seq (.circuit (cStageAPre wScr wNN rBasis9 rScr40 hScrB hNNB))
    (.seq ((wRouterBracket3x2k 1).wrap v wHas (kpIdxA rBasis9 rK4) (kpOut6 rScr40) qEnc
            (.circuit (cStageAGather rScr40 rBasis9 hBS)))
      (.seq (.circuit (Circuit.CNOT (rK4 ⟨0, by decide⟩) (rBasis9 ⟨0, by decide⟩)
          (disj_ne hKB _ _)))
        (.seq ((wRouterBracket3x2k 1).wrap v wHas (kpIdxB1 rK4 rBasis9) (kpOut6 rScr40) qEnc
                (.circuit (cStageB1Gather rScr40 rBasis9 hBS)))
          (.seq (.circuit (cStageB2Mid rK4 rBasis9 rScr40 hKB hBS))
            (.seq (pStageB2_5x2 v rK4 rBasis9 rScr40 hBS)
              (.circuit (cStageB2Post rK4 rBasis9 rScr40 hKB hBS)))))))

theorem count_cStageB1Gather {n : ℕ} (rScr40 : QRegister 40 n) (rBasis9 : QRegister 9 n)
    (hBS : rBasis9.DisjointWires rScr40) : (cStageB1Gather rScr40 rBasis9 hBS).count .T = 0 ∧
    (cStageB1Gather rScr40 rBasis9 hBS).count .TOFF = 0 := by
  simp [cStageB1Gather, Circuit.count_seq, Circuit.CNOT]
theorem count_cStageB2Mid {n : ℕ} (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (rScr40 : QRegister 40 n) (hKB : rK4.DisjointWires rBasis9)
    (hBS : rBasis9.DisjointWires rScr40) : (cStageB2Mid rK4 rBasis9 rScr40 hKB hBS).count .T =
    0 ∧ (cStageB2Mid rK4 rBasis9 rScr40 hKB hBS).count .TOFF = 0 := by
  simp [cStageB2Mid, Circuit.count_seq, Circuit.CNOT]
theorem count_cRootInit5 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hBS : rBasis9.DisjointWires rScr40) : (cRootInit5 rBasis9 rScr40 hBS).count .T = 0 ∧
    (cRootInit5 rBasis9 rScr40 hBS).count .TOFF = 0 := by
  simp [cRootInit5, Circuit.count_seq, Circuit.CNOT, Circuit.X]
theorem count_cRootUninit5 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hBS : rBasis9.DisjointWires rScr40) : (cRootUninit5 rBasis9 rScr40 hBS).count .T = 0 ∧
    (cRootUninit5 rBasis9 rScr40 hBS).count .TOFF = 0 := by
  simp [cRootUninit5, Circuit.count_seq, Circuit.CNOT, Circuit.X]
theorem count_cStageB2Gather {n : ℕ} (rScr40 : QRegister 40 n) (rBasis9 : QRegister 9 n)
    (hBS : rBasis9.DisjointWires rScr40) : (cStageB2Gather rScr40 rBasis9 hBS).count .T = 0 ∧
    (cStageB2Gather rScr40 rBasis9 hBS).count .TOFF = 0 := by
  simp [cStageB2Gather, Circuit.count_seq, Circuit.CNOT]
theorem count_cStageB2Post {n : ℕ} (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n)
    (rScr40 : QRegister 40 n) (hKB : rK4.DisjointWires rBasis9)
    (hBS : rBasis9.DisjointWires rScr40) : (cStageB2Post rK4 rBasis9 rScr40 hKB hBS).count .T =
    0 ∧ (cStageB2Post rK4 rBasis9 rScr40 hKB hBS).count .TOFF = 0 := by
  simp [cStageB2Post, Circuit.count_seq, Circuit.CNOT, Circuit.X]
theorem pStageB2_5x2_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hBS : rBasis9.DisjointWires rScr40) (hrK : ∀ i, S (rK4 i)) (hrB : ∀ u, S (rBasis9 u))
    (hrS : ∀ u, S (rScr40 u)) : (pStageB2_5x2 v rK4 rBasis9 rScr40 hBS).count .T = 10 ∧
    (pStageB2_5x2 v rK4 rBasis9 rScr40 hBS).count .TOFF = 0 ∧
    DynWires S (pStageB2_5x2 v rK4 rBasis9 rScr40 hBS) := by
  obtain ⟨tRI, fRI⟩ := count_cRootInit5 rBasis9 rScr40 hBS; obtain ⟨tRU, fRU⟩ :=
      count_cRootUninit5 rBasis9 rScr40 hBS; obtain ⟨tTr, fTr⟩ :=
      count_wTreePrefix 5 1 (kpW5x2 rScr40) (wInj_kpW5x2 rScr40) 1 le_rfl; obtain ⟨tGB2,
      fGB2⟩ := count_cStageB2Gather rScr40 rBasis9 hBS
  have hOhS : ∀ t, S (kpOh4 rBasis9 rScr40 t) := fun t ↦ by
    fin_cases t <;> [exact hrB _; exact hrB _; exact hrS _; exact hrS _]
  have cwRI : CircWires S (cRootInit5 rBasis9 rScr40 hBS) :=
      ⟨cw_1 (hrS _), cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _)
      (hrS _), cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _)
      (hrS _), cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _)
      (hrS _)⟩; have cwRU : CircWires S (cRootUninit5 rBasis9 rScr40 hBS) :=
                  ⟨cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _)
                  (hrS _), cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _)
                  (hrS _), cw_cnot (hOhS _) (hrS _), cw_cnot (hOhS _) (hrS _), cw_1 (hrS _)⟩
  have cwTr : CircWires S (wTreePrefix 5 1 (kpW5x2 rScr40) (wInj_kpW5x2 rScr40) 1 le_rfl) :=
      cw_wTreePrefix 5 1 _ _ (fun _ _ ↦ hrS _) 1 le_rfl
  have cwGB2 : CircWires S (cStageB2Gather rScr40 rBasis9 hBS) :=
      ⟨cw_cnot (hrS _) (hrB _), cw_cnot (hrS _) (hrB _), cw_cnot (hrS _) (hrB _), cw_cnot (hrS _)
      (hrB _), cw_cnot (hrS _) (hrB _), cw_cnot (hrS _) (hrB _)⟩
  dsimp only [pStageB2_5x2]
  split_ifs with hd
  · obtain ⟨tSh, fSh⟩ := count_wShiftLevels v 5 1 (kpSh1 rK4) (kpW5x2 rScr40)
      (rScr40 ⟨1, by decide⟩) (wInj_kpW5x2 rScr40) (kpW5x2_ne_qEnc rScr40) hd.1 1 le_rfl
    obtain ⟨tUn, fUn⟩ := count_wUncompTreeDyn_opt v 5 1 (kpSh1 rK4) (kpW5x2 rScr40)
      (wInj_kpW5x2 rScr40) hd.2 (.circuit (cRootUninit5 rBasis9 rScr40 hBS)) 1 le_rfl
    dsimp only [DynamicCircuit.count] at tUn fUn ⊢
    refine ⟨by simp only [Circuit.count_seq, tRI, tTr, tSh, tGB2, tUn, tRU]; rfl,
      by simp only [Circuit.count_seq, fRI, fTr, fSh, fGB2, fUn, fRU], ⟨cwRI, cwTr⟩,
      dw_wShiftLevels v 5 1 _ _ _ _ _ hd.1 (fun _ ↦ hrK _) (fun _ _ ↦ hrS _) (hrS _) 1 le_rfl,
      cwGB2, dw_wUncompTreeDyn_opt v 5 1 _ _ _ hd.2 (fun _ ↦ hrK _) (fun _ _ ↦ hrS _)
        (rest := .circuit (cRootUninit5 rBasis9 rScr40 hBS)) cwRU 1 le_rfl⟩
  · exact ⟨tTr, fTr, cwTr⟩

theorem pKpBasis9Fwd22_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u) (hKB : rK4.DisjointWires rBasis9)
    (hBS : rBasis9.DisjointWires rScr40) (hScr : S wScr) (hNN : S wNN) (hrK : ∀ i, S (rK4 i))
    (hrB : ∀ u, S (rBasis9 u)) (hrS : ∀ u, S (rScr40 u)) :
    (pKpBasis9Fwd22 v wScr wNN rK4 rBasis9 rScr40 hScrB hNNB hKB hBS).count .T = 22 ∧
    (pKpBasis9Fwd22 v wScr wNN rK4 rBasis9 rScr40 hScrB hNNB hKB hBS).count .TOFF = 0 ∧
    DynWires S (pKpBasis9Fwd22 v wScr wNN rK4 rBasis9 rScr40 hScrB hNNB hKB hBS) := by
  let wHas := rScr40 ⟨0, by decide⟩
  let qEnc := rScr40 ⟨1, by decide⟩
  let pGA : DynamicCircuit Var n := .circuit (cStageAGather rScr40 rBasis9 hBS)
  let pGB1 : DynamicCircuit Var n :=
      .circuit (cStageB1Gather rScr40 rBasis9 hBS); obtain ⟨tPre, fPre⟩ :=
      count_cStageAPre wScr wNN rBasis9 rScr40 hScrB hNNB; obtain ⟨tWA, fWA⟩ :=
      (wRouterBracket3x2k 1).count_wrap v wHas (kpIdxA rBasis9 rK4)
      (kpOut6 rScr40) qEnc pGA; obtain ⟨tGA, fGA⟩ :=
      count_cStageAGather rScr40 rBasis9 hBS; obtain ⟨tWB1, fWB1⟩ :=
      (wRouterBracket3x2k 1).count_wrap v wHas (kpIdxB1 rK4 rBasis9)
      (kpOut6 rScr40) qEnc pGB1; obtain ⟨tGB1, fGB1⟩ :=
      count_cStageB1Gather rScr40 rBasis9 hBS; obtain ⟨tMid2, fMid2⟩ :=
      count_cStageB2Mid rK4 rBasis9 rScr40 hKB hBS; obtain ⟨tB2, fB2, dwB2⟩ :=
      pStageB2_5x2_counts_wires v rK4 rBasis9 rScr40 hBS hrK hrB hrS; obtain ⟨tPost, fPost⟩ :=
      count_cStageB2Post rK4 rBasis9 rScr40 hKB hBS
  have hIdxAS : ∀ d, S (kpIdxA rBasis9 rK4 d) := fun d ↦ by
    fin_cases d <;> [exact hrB _; exact hrK _; exact hrK _]
  have hIdxB1S : ∀ d, S (kpIdxB1 rK4 rBasis9 d) := fun d ↦ by
    fin_cases d <;> [exact hrK _; exact hrB _; exact hrB _]
  have cwPre : CircWires S (cStageAPre wScr wNN rBasis9 rScr40 hScrB hNNB) :=
      ⟨cw_cnot hScr (hrB _), cw_cnot hNN (hrB _),
      cw_1 (hrS _)⟩; have cwGA : CircWires S (cStageAGather rScr40 rBasis9 hBS) :=
                       ⟨cw_cnot (hrS _) (hrB _), cw_cnot (hrS _)
                       (hrB _)⟩; have cwGB1 : CircWires S (cStageB1Gather rScr40 rBasis9 hBS) :=
                                   ⟨cw_cnot (hrS _) (hrB _), cw_cnot (hrS _)
                                   (hrB _)⟩;
                                   have cwMid2 :
                                   CircWires S (cStageB2Mid rK4 rBasis9 rScr40 hKB hBS) :=
                                   ⟨cw_cnot (hrK _) (hrB _), cw_cnot (hrB _)
                                   (hrS _), cw_cnot (hrB _) (hrS _), cw_cnot (hrB _)
                                   (hrS _), cw_cnot (hrB _)
                                   (hrS _)⟩;
                                   have cwPost :
                                   CircWires S (cStageB2Post rK4 rBasis9 rScr40 hKB hBS) :=
                                   ⟨cw_cnot (hrB _) (hrS _), cw_cnot (hrB _)
                                   (hrS _), cw_cnot (hrB _) (hrS _), cw_cnot (hrB _)
                                   (hrS _), cw_1 (hrS _), cw_cnot (hrK _) (hrB _), cw_cnot (hrK _)
                                   (hrB _)⟩
  have dwA :=
      (wRouterBracket3x2k 1).dynWires_wrap v wHas (kpIdxA rBasis9 rK4)
      (kpOut6 rScr40) qEnc pGA (hrS _) hIdxAS (fun _ ↦ hrS _) (hrS _) cwGA
  have dwB1 :=
      (wRouterBracket3x2k 1).dynWires_wrap v wHas (kpIdxB1 rK4 rBasis9)
      (kpOut6 rScr40) qEnc pGB1 (hrS _) hIdxB1S (fun _ ↦ hrS _) (hrS _) cwGB1
  unfold pKpBasis9Fwd22;
  refine ⟨?_, ?_, ⟨cwPre, dwA, cw_cnot (hrK _) (hrB _), dwB1, cwMid2, dwB2, cwPost⟩⟩
  · dsimp only [DynamicCircuit.count, pGA, pGB1] at tWA tWB1 ⊢
    rw [tPre, tWA, tGA, tWB1, tGB1, tMid2, tB2, tPost]; simp [Circuit.CNOT]
  · dsimp only [DynamicCircuit.count, pGA, pGB1] at fWA fWB1 ⊢
    rw [fPre, fWA, fGA, fWB1, fGB1, fMid2, fB2, fPost]; simp [Circuit.CNOT]

def AtMostOneOh4 (u0 u1 u2 u3 : ZMod 2) : Prop :=
    (u0 = 0 ∨ (u1 = 0 ∧ u2 = 0 ∧ u3 = 0)) ∧ (u1 = 0 ∨ (u2 = 0 ∧ u3 = 0)) ∧ (u2 = 0 ∨ u3 = 0)
instance instDecAtMostOneOh4 (u0 u1 u2 u3 : ZMod 2) : Decidable (AtMostOneOh4 u0 u1 u2 u3)
    := by unfold AtMostOneOh4; infer_instance
def bStar5Val (u0 u1 u2 u3 : ZMod 2) : Fin 5 :=
  if u0 = 1 then ⟨1, by decide⟩
  else if u1 = 1 then ⟨2, by decide⟩
  else if u2 = 1 then ⟨3, by decide⟩
  else if u3 = 1 then ⟨4, by decide⟩
  else ⟨0, by decide⟩

abbrev bStar5 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (η : BitAssignment n) : Fin 5 :=
  bStar5Val (η (kpOh4 rBasis9 rScr40 ⟨0, by decide⟩))
    (η (kpOh4 rBasis9 rScr40 ⟨1, by decide⟩))
    (η (kpOh4 rBasis9 rScr40 ⟨2, by decide⟩))
    (η (kpOh4 rBasis9 rScr40 ⟨3, by decide⟩))

def ValidOh5 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n) (η : BitAssignment n) :
    Prop :=
  AtMostOneOh4 (η (kpOh4 rBasis9 rScr40 ⟨0, by decide⟩))
    (η (kpOh4 rBasis9 rScr40 ⟨1, by decide⟩))
    (η (kpOh4 rBasis9 rScr40 ⟨2, by decide⟩))
    (η (kpOh4 rBasis9 rScr40 ⟨3, by decide⟩))

instance instDecValidOh5 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n) :
    DecidablePred (ValidOh5 rBasis9 rScr40) := fun _ ↦ by
  unfold ValidOh5; infer_instance

def vStageB1Out (scr nn k0 k1 k3 : ZMod 2) (u : Fin 9) : ZMod 2 :=
  let d := scr + nn
  let c0 := k0 * d
  let s0 := d + k0
  match u.val with
  | 0 => s0
  | 1 => c0
  | 2 => k1 * c0
  | 4 => k1 * s0
  | 8 => k3 * d
  | _ => 0

def vStageB2In (scr nn k0 k1 k3 : ZMod 2) (u : Fin 9) : ZMod 2 :=
  let d := scr + nn
  let c0 := k0 * d
  let s0 := d + k0
  match u.val with
  | 0 => s0
  | 1 => k1 + c0
  | 2 => k1 * c0
  | 4 => k1 * s0
  | 8 => k3 * d
  | _ => 0

def vStageB2Out (scr nn k0 k1 k2 k3 : ZMod 2) (u : Fin 9) : ZMod 2 :=
  let d := scr + nn
  let c0 := k0 * d
  let c1 := k1 * c0
  if u.val = 2 then c1
  else if u.val = 3 then k2 * c1
  else kpBasis9Vec scr nn k0 k1 k2 k3 u

theorem z2_stageB1_oneHot (d k0 k1 : ZMod 2) :
    let s0 := d + k0
    let c0 := k0 * d
    let v :=
        ((0 + if k1 = 1 then 2 ^ 0 else 0) + if s0 = 1 then 2 ^ 1 else 0) + if c0 =
        1 then 2 ^ 2 else 0
    v < 6 ∧
    (0 : ZMod 2) + (if v = 3 then 1 else 0) = k1 * s0 ∧
    (0 : ZMod 2) + (if v = 5 then 1 else 0) = k1 * c0 := by
  revert d k0 k1; decide

theorem z2_root5_oneHot (u0 u1 u2 u3 : ZMod 2) (h : AtMostOneOh4 u0 u1 u2 u3)
    (b : Fin 5) :
    (match b.val with
      | 0 => (1 : ZMod 2) + u0 + u1 + u2 + u3
      | 1 => u0
      | 2 => u1
      | 3 => u2
      | _ => u3) = (if b = bStar5Val u0 u1 u2 u3 then 1 else 0) := by
  revert u0 u1 u2 u3 h b; decide

theorem z2_stageB2_oneHot (scr nn k0 k1 k2 k3 : ZMod 2) (hnb : ¬(k0 = 1 ∧ k3 = 1)) :
    let d := scr + nn
    let c0 := k0 * d
    let s0 := d + k0
    let s1 := k1 + c0
    let y1 := k1 * c0
    let y3 := k1 * s0
    let c12 := s0 + y3
    let c13 := s1 + y3
    let bS := bStar5Val y1 y3 c12 c13
    let pS : Fin (2 ^ 1) := ⟨0 + if k2 = 1 then 2 ^ 0 else 0, by split_ifs <;> decide⟩
    let wBit (b : Fin 5) : ZMod 2 := if b = bS ∧ (⟨1, by decide⟩ : Fin (2 ^ 1)) = pS then 1 else 0
    AtMostOneOh4 y1 y3 c12 c13 ∧
    (0 : ZMod 2) + wBit ⟨1, by decide⟩ = k2 * y1 ∧
    (0 : ZMod 2) + wBit ⟨2, by decide⟩ + wBit ⟨3, by decide⟩ =
      kpBasis9Vec scr nn k0 k1 k2 k3 ⟨5, by decide⟩ ∧
    (0 : ZMod 2) + wBit ⟨2, by decide⟩ + wBit ⟨4, by decide⟩ =
      kpBasis9Vec scr nn k0 k1 k2 k3 ⟨6, by decide⟩ ∧
    (0 : ZMod 2) + wBit ⟨2, by decide⟩ =
      kpBasis9Vec scr nn k0 k1 k2 k3 ⟨7, by decide⟩ ∧
    y3 = kpBasis9Vec scr nn k0 k1 k2 k3 ⟨4, by decide⟩ ∧
    k3 * d = kpBasis9Vec scr nn k0 k1 k2 k3 ⟨8, by decide⟩ ∧
    y1 + k2 = kpBasis9Vec scr nn k0 k1 k2 k3 ⟨2, by decide⟩ ∧
    (k2 * y1) + k3 = kpBasis9Vec scr nn k0 k1 k2 k3 ⟨3, by decide⟩ := by
  revert scr nn k0 k1 k2 k3 hnb; decide

theorem cnot_invol_mulVec {n : ℕ} {c t : Wire n} (h₁ h₂ : c ≠ t) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.CNOT c t h₁).eval.1.mulVec ((Circuit.CNOT c t h₂).eval.1.mulVec ψ) = ψ := by
  have hM : (Circuit.CNOT c t h₁).eval.1 * (Circuit.CNOT c t h₂).eval.1 = 1 := by
    apply matrix_ext_ket; intro η
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ket_CNOT, ket_CNOT, Function.update_self,
        Function.update_of_ne h₁, add_assoc, CharTwo.add_self_eq_zero, add_zero,
        Function.update_idem, Function.update_eq_self]
  rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]

theorem x_invol_mulVec {n : ℕ} (q : Wire n) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.X q).eval.1.mulVec ((Circuit.X q).eval.1.mulVec ψ) = ψ := by
  have hM : (Circuit.X q).eval.1 * (Circuit.X q).eval.1 = 1 := by
    apply matrix_ext_ket; intro η
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ket_X, ket_X, Function.update_self, add_assoc,
        CharTwo.add_self_eq_zero, add_zero, Function.update_idem, Function.update_eq_self]
  rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]

theorem cRootUninit5_init5_ket {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hBS : rBasis9.DisjointWires rScr40) (η : BitAssignment n) :
    (cRootUninit5 rBasis9 rScr40 hBS).eval.1.mulVec ((cRootInit5 rBasis9 rScr40
    hBS).eval.1.mulVec (ket η)) =
    ket η := by
  dsimp only [cRootInit5, cRootUninit5];
  simp only [eval_seq_mulVec, cnot_invol_mulVec, x_invol_mulVec]
theorem update_inj_apply_w5 {α ι : Type*} [DecidableEq α] [DecidableEq ι] {β : Type*}
    (g : ι → α) (hg : ∀ a b, g a = g b → a = b) (f : α → β) (a b : ι) (v : β) :
    Function.update f (g a) v (g b) = if b = a then v else f (g b) := by
  by_cases h : b = a
  · subst h
    rw [itePos rfl, Function.update_self]
  · rw [iteNeg h, Function.update_of_ne (fun e ↦ h (hg b a e))]

theorem cRootInit5_ket_oneHot {n : ℕ} (rBasis9 : QRegister 9 n)
    (rScr40 : QRegister 40 n) (hBS : rBasis9.DisjointWires rScr40) (η : BitAssignment n)
    (hOh : ValidOh5 rBasis9 rScr40 η)
    (hw0 : ∀ b p, η (kpW5x2 rScr40 b p) = 0) :
    (cRootInit5 rBasis9 rScr40 hBS).eval.1.mulVec (ket η) =
      ket (Function.update η (kpW5x2 rScr40 (bStar5 rBasis9 rScr40 η) ⟨0, by decide⟩) 1)
          := by
  have hUpdOh (f : BitAssignment n) (b v t) :=
    Function.update_of_ne (kpOh4_ne_w5 hBS t b ⟨0, by decide⟩) v f
  have hUpdW := update_inj_apply_w5 (β := ZMod 2) (kpW5x2 rScr40 · ⟨0, by decide⟩)
    fun _ _ e ↦ (wInj_kpW5x2 rScr40 _ _ _ _ e).1
  have hw0_p0 (b : Fin 5) : η (kpW5x2 rScr40 b ⟨0, by decide⟩) = 0 := hw0 b ⟨0, by decide⟩
  simp only [cRootInit5, eval_seq_mulVec, ket_X, ket_CNOT]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hm : ∃ b : Fin 5, w = kpW5x2 rScr40 b ⟨0, by decide⟩
  · obtain ⟨b, rfl⟩ := hm
    refine Eq.trans
      (by fin_cases b <;> simp only [hUpdOh, hUpdW, hw0_p0] <;> dsimp <;> simp only [zero_add])
      ((z2_root5_oneHot _ _ _ _ hOh b).trans ?_)
    rw [hUpdW]
    by_cases hb : b = bStar5 rBasis9 rScr40 η <;> simp only [hb, ↓reduceIte, hw0_p0]
  · simp only [fun (f : BitAssignment n) (b : Fin 5) (v : ZMod 2) ↦
      Function.update_of_ne (fun e ↦ hm ⟨b, e⟩) v f]

theorem cStageB1Gather_mulVec_ket {n : ℕ} (rScr40 : QRegister 40 n)
    (rBasis9 : QRegister 9 n) (hBS : rBasis9.DisjointWires rScr40) (η : BitAssignment n) :
    (cStageB1Gather rScr40 rBasis9 hBS).eval.1.mulVec (ket η) =
      let wOut6 := kpOut6 rScr40
      ket (Function.update
        (Function.update η (rBasis9 ⟨4, by decide⟩)
          (η (rBasis9 ⟨4, by decide⟩) + η (wOut6 ⟨3, by decide⟩)))
        (rBasis9 ⟨2, by decide⟩)
        (η (rBasis9 ⟨2, by decide⟩) + η (wOut6 ⟨5, by decide⟩))) := by
  dsimp only [cStageB1Gather]; rw [eval_seq_mulVec, ket_CNOT, ket_CNOT]
  have n5_4 : kpOut6 rScr40 ⟨5, by decide⟩ ≠ rBasis9 ⟨4, by decide⟩ := (disj_ne hBS _ _).symm
  have n2_4 : rBasis9 ⟨2, by decide⟩ ≠ rBasis9 ⟨4, by decide⟩ :=
      rBasis9_ne_of_ne rBasis9 (by decide)
  simp only [Function.update_of_ne n5_4, Function.update_of_ne n2_4]

theorem cStageB2Gather_mulVec_ket {n : ℕ} (rScr40 : QRegister 40 n)
    (rBasis9 : QRegister 9 n) (hBS : rBasis9.DisjointWires rScr40) (η : BitAssignment n) :
    (cStageB2Gather rScr40 rBasis9 hBS).eval.1.mulVec (ket η) =
      let w5 := kpW5x2 rScr40
      let p1 : Fin (2 ^ 1) := ⟨1, by decide⟩
      ket (Function.update
        (Function.update
          (Function.update
            (Function.update η (rBasis9 ⟨3, by decide⟩)
              (η (rBasis9 ⟨3, by decide⟩) + η (w5 ⟨1, by decide⟩ p1)))
            (rBasis9 ⟨5, by decide⟩)
            (η (rBasis9 ⟨5, by decide⟩) + η (w5 ⟨2, by decide⟩ p1) + η (w5 ⟨3, by decide⟩ p1)))
          (rBasis9 ⟨6, by decide⟩)
          (η (rBasis9 ⟨6, by decide⟩) + η (w5 ⟨2, by decide⟩ p1) + η (w5 ⟨4, by decide⟩ p1)))
        (rBasis9 ⟨7, by decide⟩)
        (η (rBasis9 ⟨7, by decide⟩) + η (w5 ⟨2, by decide⟩ p1))) := by
  dsimp only [cStageB2Gather]
  simp only [eval_seq_mulVec, ket_CNOT]
  have hUpdWB (f : BitAssignment n) (u : Fin 9) (v : ZMod 2) (b : Fin 5) :
      Function.update f (rBasis9 u) v (kpW5x2 rScr40 b ⟨1, by decide⟩) =
        f (kpW5x2 rScr40 b ⟨1, by decide⟩) :=
    Function.update_of_ne (disj_ne hBS u _).symm v f
  have hUpdBB := update_inj_apply_w5 (β := ZMod 2) (fun u ↦ rBasis9 u)
    (fun _ _ e ↦ rBasis9.wires.injective e)
  apply congrArg ket
  funext w
  by_cases hm : ∃ u : Fin 9, w = rBasis9 u
  · obtain ⟨u, rfl⟩ := hm
    fin_cases u <;> simp only [hUpdWB, hUpdBB] <;> dsimp
  · simp only [fun (f : BitAssignment n) (u : Fin 9) (v : ZMod 2) ↦
      Function.update_of_ne (fun e ↦ hm ⟨u, e⟩) v f]

theorem subspaceStep_pStageB2_5x2 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hKS : rK4.DisjointWires rScr40) (hBS : rBasis9.DisjointWires rScr40)
    (G_in G_out : Operator (2 ^ n))
    (hSuppIn : SupportedOn (fun η ↦ ValidOh5 rBasis9 rScr40 η ∧
        (∀ b p, η (kpW5x2 rScr40 b p) = 0) ∧ η (rScr40 ⟨1, by decide⟩) = 0) G_in)
    (hSuppOut : SupportedOn (fun η ↦ ValidOh5 rBasis9 rScr40 η ∧
        ∀ b p, η (kpW5x2 rScr40 b p) = 0) G_out)
    (hGatEq : (cStageB2Gather rScr40 rBasis9 hBS).eval.1 *
        (wSuperOp (bStar5 rBasis9 rScr40) (kpSh1 rK4) (kpW5x2 rScr40)
          (rScr40 ⟨1, by decide⟩) 1 le_rfl * G_in) =
      oneHotOptPreOp (ValidOh5 rBasis9 rScr40) (fun _ ↦ True)
        (bStar5 rBasis9 rScr40) (kpSh1 rK4) (kpW5x2 rScr40) 1 le_rfl * G_out) :
    SubspaceStep (Var := Var) G_in G_out (pStageB2_5x2 v rK4 rBasis9 rScr40 hBS) := by
  have hd : KpK2DisjScr12 rK4 rScr40 := ⟨fun _ ↦ disj_ne hKS _ _, fun _ _ _ ↦ disj_ne hKS _ _⟩
  unfold pStageB2_5x2
  rw [ditePos hd]
  let bS := bStar5 rBasis9 rScr40
  let uSh := kpSh1 rK4
  let w5 := kpW5x2 rScr40
  let hw5 := wInj_kpW5x2 rScr40
  let P5 := ValidOh5 rBasis9 rScr40
  let idOnP5 : Operator (2 ^ n) :=
    mkVecOp fun η ↦ if P5 η ∧ ∀ b p, η (w5 b p) = 0 then ket η else 0
  exact subspaceStep_seq_u
    (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) G_in _)
      (hSuppIn _ _ fun η ⟨hOh, hw0, hq0⟩ ↦ by
        rw [show SplitRouterSeqBell26k.ket η = ket η from rfl, eval_seq_mulVec,
          cRootInit5_ket_oneHot rBasis9 rScr40 hBS η hOh hw0,
          wSuperVec_bot_pub bS uSh w5 hw5 _ η hw0 hq0, wSuperOp, mkVecOp_mulVec_ket]))
    (subspaceStep_seq_u
      (subspaceStep_mul_right G_in (subspaceStep_wShiftLevels v bS uSh w5 _ hw5
        (kpW5x2_ne_qEnc rScr40) hd.1 hd.2 1 le_rfl))
      (subspaceStep_seq_u (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) hGatEq)
        (subspaceStep_congr_out (subspaceStep_mul_right G_out
          (subspaceStep_wUncompTreeDyn_opt v P5 (fun _ ↦ True) bS uSh w5 hw5 hd.2
            (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _)
              (matrix_ext_ket fun η ↦ by
                simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, idOnP5, mkVecOp_mulVec_ket,
                  oneHotOptPreVec]
                by_cases hV : P5 η ∧ ∀ b p, η (w5 b p) = 0
                · rw [itePos hV, itePos trivial, itePos hV,
                    show @PhotochemistrySolution.XMeasUnld.ket n = ket from rfl,
                    show (⟨idxValPrefix uSh η 0 _, _⟩ : Fin (2 ^ 1)) = ⟨0, by decide⟩ from
                      Fin.ext rfl, ← cRootInit5_ket_oneHot rBasis9 rScr40 hBS η hV.1 hV.2,
                    cRootUninit5_init5_ket]
                · rw [iteNeg hV, iteNeg hV, Matrix.mulVec_zero])) 1 le_rfl))
          ((hSuppOut idOnP5 1 fun η hV ↦ by
            simp only [show SplitRouterSeqBell26k.ket η = ket η from rfl, idOnP5,
              mkVecOp_mulVec_ket, Matrix.one_mulVec]
            exact itePos hV).trans (Matrix.one_mul G_out)))))

theorem z2_vStageB2In_agree (scr nn k0 k1 k2 k3 : ZMod 2)
    (hnb : ¬(k0 = 1 ∧ k3 = 1)) (u : Fin 9)
    (h3 : u ≠ ⟨3, by decide⟩) (h5 : u ≠ ⟨5, by decide⟩)
    (h6 : u ≠ ⟨6, by decide⟩) (h7 : u ≠ ⟨7, by decide⟩) :
    vStageB2In scr nn k0 k1 k3 u = vStageB2Out scr nn k0 k1 k2 k3 u := by
  revert scr nn k0 k1 k2 k3 hnb u h3 h5 h6 h7; decide

theorem z2_stageB2Mid_identities (scr nn k0 k1 k3 : ZMod 2) :
    vStageB1Out scr nn k0 k1 k3 ⟨1, by decide⟩ + k1 +
      vStageB1Out scr nn k0 k1 k3 ⟨4, by decide⟩ =
      vStageB2In scr nn k0 k1 k3 ⟨1, by decide⟩ +
      vStageB2In scr nn k0 k1 k3 ⟨4, by decide⟩ ∧
    vStageB1Out scr nn k0 k1 k3 ⟨0, by decide⟩ +
      vStageB1Out scr nn k0 k1 k3 ⟨4, by decide⟩ =
      vStageB2In scr nn k0 k1 k3 ⟨0, by decide⟩ +
      vStageB2In scr nn k0 k1 k3 ⟨4, by decide⟩ ∧
    vStageB1Out scr nn k0 k1 k3 ⟨1, by decide⟩ + k1 =
      vStageB2In scr nn k0 k1 k3 ⟨1, by decide⟩ := by
  revert scr nn k0 k1 k3; decide

abbrev vfB2InFn {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : Fin 9 → ZMod 2 :=
  vStageB2In (st δ wScr) (st δ wNN)
    (st δ (rK4 ⟨0, by decide⟩)) (st δ (rK4 ⟨1, by decide⟩)) (st δ (rK4 ⟨3, by decide⟩))

abbrev vfB2OutFn {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : Fin 9 → ZMod 2 :=
  vStageB2Out (st δ wScr) (st δ wNN)
    (st δ (rK4 ⟨0, by decide⟩)) (st δ (rK4 ⟨1, by decide⟩))
    (st δ (rK4 ⟨2, by decide⟩)) (st δ (rK4 ⟨3, by decide⟩))

abbrev c12Fn {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : ZMod 2 :=
  vfB2InFn wScr wNN rK4 st δ ⟨0, by decide⟩ + vfB2InFn wScr wNN rK4 st δ ⟨4, by decide⟩

abbrev c13Fn {n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : ZMod 2 :=
  vfB2InFn wScr wNN rK4 st δ ⟨1, by decide⟩ + vfB2InFn wScr wNN rK4 st δ ⟨4, by decide⟩

def mkSt22 {n : ℕ} (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (st : BitAssignment n → BitAssignment n) (vf : BitAssignment n → Fin 9 → ZMod 2)
    (c12 c13 : BitAssignment n → ZMod 2) (δ : BitAssignment n) : BitAssignment n :=
  Function.update
    (Function.update
      (Function.update (writeReg (st δ) rBasis9 (vf δ)) (rScr40 ⟨0, by decide⟩) 1)
      (rScr40 ⟨12, by decide⟩) (c12 δ))
    (rScr40 ⟨13, by decide⟩) (c13 δ)

theorem update_congr_at {α : Type*} [DecidableEq α] {β : α → Sort*} {f g : (a : α) → β a}
    (a : α) (v : β a) {w : α} (h : f w = g w) :
    Function.update f a v w = Function.update g a v w := by
  by_cases hw : w = a
  · subst hw
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hw, Function.update_of_ne hw, h]

theorem subspaceStep_circuit_mkKetOpW {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (rWork : QRegister W n) (st₁ st₂ : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) (c : Circuit n)
    (hKet : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → c.eval.1.mulVec (ket (st₁ δ)) = ket (st₂ δ)) :
    SubspaceStep (Var := Var) (mkKetOpW rWork st₁ ph) (mkKetOpW rWork st₂ ph) (.circuit c) := by
  refine subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ c)
    (matrix_ext_ket fun δ ↦ ?_)
  rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, hKet δ hz]
  · rw [Matrix.mulVec_zero]

theorem mkSt22_basis {n : ℕ} {rBasis9 : QRegister 9 n} {rScr40 : QRegister 40 n}
    (hBS : rBasis9.DisjointWires rScr40) {st vf c12 c13 δ} (u : Fin 9) :
    mkSt22 rBasis9 rScr40 st vf c12 c13 δ (rBasis9 u) = vf δ u := by
  dsimp only [mkSt22]
  rw [Function.update_of_ne (disj_ne hBS u _), Function.update_of_ne (disj_ne hBS u _),
    Function.update_of_ne (disj_ne hBS u _), writeReg_apply_reg]

theorem mkSt22_k4 {n : ℕ} {rK4 : QRegister 4 n} {rBasis9 : QRegister 9 n}
    {rScr40 : QRegister 40 n} (hKB : rK4.DisjointWires rBasis9) (hKS : rK4.DisjointWires rScr40)
    {st vf c12 c13 δ} (i : Fin 4) :
    mkSt22 rBasis9 rScr40 st vf c12 c13 δ (rK4 i) = st δ (rK4 i) := by
  dsimp only [mkSt22]
  rw [Function.update_of_ne (disj_ne hKS i _), Function.update_of_ne (disj_ne hKS i _),
    Function.update_of_ne (disj_ne hKS i _),
    writeReg_apply_of_not_mem _ _ _ _ (fun ⟨v, hv⟩ ↦ disj_ne hKB i v hv.symm)]

theorem mkSt22_s0 {n : ℕ} {rBasis9 : QRegister 9 n} {rScr40 : QRegister 40 n}
    {st vf c12 c13 δ} :
    mkSt22 rBasis9 rScr40 st vf c12 c13 δ (rScr40 ⟨0, by decide⟩) = 1 := by
  dsimp only [mkSt22]
  rw [Function.update_of_ne (rScr40_ne_of_ne rScr40 (by decide)),
    Function.update_of_ne (rScr40_ne_of_ne rScr40 (by decide)), Function.update_self]

theorem mkSt22_scr12 {n : ℕ} {rBasis9 : QRegister 9 n} {rScr40 : QRegister 40 n}
    {st vf c12 c13 δ} :
    mkSt22 rBasis9 rScr40 st vf c12 c13 δ (rScr40 ⟨12, by decide⟩) = c12 δ := by
  dsimp only [mkSt22]
  rw [Function.update_of_ne (rScr40_ne_of_ne rScr40 (by decide)), Function.update_self]

theorem mkSt22_s13 {n : ℕ} {rBasis9 : QRegister 9 n} {rScr40 : QRegister 40 n}
    {st vf c12 c13 δ} :
    mkSt22 rBasis9 rScr40 st vf c12 c13 δ (rScr40 ⟨13, by decide⟩) = c13 δ :=
  Function.update_self _ _ _

theorem mkSt22_scr {n : ℕ} {rBasis9 : QRegister 9 n} {rScr40 : QRegister 40 n}
    (hBS : rBasis9.DisjointWires rScr40) {st vf c12 c13 δ} (u : Fin 40)
    (h0 : u.val ≠ 0) (h12 : u.val ≠ 12) (h13 : u.val ≠ 13) :
    mkSt22 rBasis9 rScr40 st vf c12 c13 δ (rScr40 u) = st δ (rScr40 u) := by
  dsimp only [mkSt22]
  rw [Function.update_of_ne (rScr40_ne_of_ne rScr40 (fun e ↦ h13 (congrArg Fin.val e))),
    Function.update_of_ne (rScr40_ne_of_ne rScr40 (fun e ↦ h12 (congrArg Fin.val e))),
    Function.update_of_ne (rScr40_ne_of_ne rScr40 (fun e ↦ h0 (congrArg Fin.val e))),
    writeReg_apply_of_not_mem _ _ _ _ (fun ⟨v, hv⟩ ↦ disj_ne hBS v u hv)]

theorem subspaceStep_stageB2_mkKetOpW {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hKB : rK4.DisjointWires rBasis9) (hKS : rK4.DisjointWires rScr40)
    (hBS : rBasis9.DisjointWires rScr40)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hkLe : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 4 (fun i ↦ st δ (rK4 i)) ≤ 8)
    (hLo0 : ∀ (δ : BitAssignment n) (u : Fin 40), u.val < 14 →
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rScr40 u) = 0) :
    SubspaceStep (Var := Var)
      (mkKetOpW rWork (mkSt22 rBasis9 rScr40 st (vfB2InFn wScr wNN rK4 st)
        (c12Fn wScr wNN rK4 st) (c13Fn wScr wNN rK4 st)) ph)
      (mkKetOpW rWork (mkSt22 rBasis9 rScr40 st (vfB2OutFn wScr wNN rK4 st)
        (c12Fn wScr wNN rK4 st) (c13Fn wScr wNN rK4 st)) ph)
      (pStageB2_5x2 v rK4 rBasis9 rScr40 hBS) := by
  let st22 (vf : BitAssignment n → Fin 9 → ZMod 2) :=
    mkSt22 rBasis9 rScr40 st vf (c12Fn wScr wNN rK4 st) (c13Fn wScr wNN rK4 st)
  have hBnd : ∀ (b : Fin 5) (p : Fin (2 ^ 1)),
      (2 + 2 * b.val + p.val) ≠ 0 ∧ (2 + 2 * b.val + p.val) ≠ 12 ∧
        (2 + 2 * b.val + p.val) ≠ 13 ∧ (2 + 2 * b.val + p.val) < 14 := by decide
  have hW5_0 (vf) (δ : BitAssignment n) (hz : ∀ k : Fin W, δ (rWork k) = 0)
      (b : Fin 5) (p : Fin (2 ^ 1)) : st22 vf δ (kpW5x2 rScr40 b p) = 0 :=
    let ⟨h0, h12, h13, h14⟩ := hBnd b p
    (mkSt22_scr hBS _ h0 h12 h13).trans (hLo0 δ _ h14 hz)
  have hQ0 (vf) (δ : BitAssignment n) (hz : ∀ k : Fin W, δ (rWork k) = 0) :
      st22 vf δ (rScr40 ⟨1, by decide⟩) = 0 :=
    (mkSt22_scr hBS ⟨1, by decide⟩ (by decide) (by decide) (by decide)).trans
      (hLo0 δ ⟨1, by decide⟩ (by decide) hz)
  let vfIn := vfB2InFn wScr wNN rK4 st
  let vfOut := vfB2OutFn wScr wNN rK4 st
  have hz2Ag (δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) :=
    let k (i : ℕ) (h : i < 4 := by decide) := st δ (rK4 ⟨i, h⟩)
    let hnb := not_k0_and_k3_of_le8 _ (hkLe δ hz)
    And.intro (z2_stageB2_oneHot (st δ wScr) (st δ wNN) (k 0) (k 1) (k 2) (k 3) hnb)
      (z2_vStageB2In_agree (st δ wScr) (st δ wNN) (k 0) (k 1) (k 2) (k 3) hnb)
  have hOhIn (δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) :
      ValidOh5 rBasis9 rScr40 (st22 vfIn δ) := by
    simp only [ValidOh5, kpOh4, st22, mkSt22_basis hBS, mkSt22_scr12,
      mkSt22_s13]
    exact (hz2Ag δ hz).1.1
  have hOhEq (δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) (t : Fin 4) :
      st22 vfOut δ (kpOh4 rBasis9 rScr40 t) = st22 vfIn δ (kpOh4 rBasis9 rScr40 t) := by
    fin_cases t <;> simp only [kpOh4, st22, mkSt22_basis hBS, mkSt22_scr12,
      mkSt22_s13] <;> exact ((hz2Ag δ hz).2 _ (by decide) (by decide) (by decide)
        (by decide)).symm
  have hOhOut (δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) :
      ValidOh5 rBasis9 rScr40 (st22 vfOut δ) := by
    simpa only [ValidOh5, hOhEq δ hz] using hOhIn δ hz
  refine subspaceStep_pStageB2_5x2 v rK4 rBasis9 rScr40 hKS hBS _ _
    (supportedOn_mkKetOpW rWork _ ph fun δ hz ↦ ⟨hOhIn δ hz, hW5_0 _ δ hz, hQ0 _ δ hz⟩)
    (supportedOn_mkKetOpW rWork _ ph fun δ hz ↦ ⟨hOhOut δ hz, hW5_0 _ δ hz⟩)
    (matrix_ext_ket fun δ ↦ ?_)
  simp only [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, wSuperOp, mkVecOp_mulVec_ket,
      wSuperVec_top_pub _ _ _ _ _ (hW5_0 _ δ hz) (hQ0 _ δ hz), oneHotOptPreOp, mkVecOp_mulVec_ket,
      oneHotOptPreVec, itePos ⟨hOhOut δ hz, hW5_0 _ δ hz⟩, itePos trivial]
    let pS : Fin (2 ^ 1) :=
      ⟨0 + if st δ (rK4 ⟨2, by decide⟩) = 1 then 2 ^ 0 else 0, by split_ifs <;> decide⟩
    let bS : Fin 5 := bStar5Val (vfIn δ ⟨2, by decide⟩) (vfIn δ ⟨4, by decide⟩)
      (c12Fn wScr wNN rK4 st δ) (c13Fn wScr wNN rK4 st δ)
    have hpVal (vf) {hlt} :
        (⟨idxValPrefix (kpSh1 rK4) (st22 vf δ) 1 le_rfl, hlt⟩ : Fin (2 ^ 1)) = pS :=
      Fin.ext (by simp only [idxValPrefix, kpSh1, pS, st22, mkSt22_k4 hKB hKS])
    have hbSIn : bStar5 rBasis9 rScr40 (st22 vfIn δ) = bS := by
      simp only [bStar5, kpOh4, bS, st22, mkSt22_basis hBS, mkSt22_scr12,
        mkSt22_s13]
    rw [hpVal vfIn, hbSIn, hpVal vfOut, show bStar5 rBasis9 rScr40 (st22 vfOut δ) = bS by
      simpa only [bStar5, hOhEq δ hz] using hbSIn, cStageB2Gather_mulVec_ket]
    refine congrArg (_ • ket ·) ?_
    set η := Function.update (st22 vfIn δ) (kpW5x2 rScr40 bS pS) 1
    obtain ⟨⟨_, g3, g5, g6, g7, _⟩, hAg⟩ := hz2Ag δ hz
    have hηB (u : Fin 9) : η (rBasis9 u) = vfIn δ u :=
      (Function.update_of_ne (disj_ne hBS u _) 1 _).trans (mkSt22_basis hBS u)
    have hηW (b : Fin 5) : η (kpW5x2 rScr40 b ⟨1, by decide⟩) =
        if b = bS ∧ (⟨1, by decide⟩ : Fin (2 ^ 1)) = pS then 1 else 0 := by
      split_ifs with hbp
      · exact (congrArg η (congrArg₂ _ hbp.1 hbp.2)).trans (Function.update_self _ _ _)
      · exact (Function.update_of_ne (fun e ↦ hbp (wInj_kpW5x2 rScr40 _ _ _ _ e)) 1 _).trans
          (hW5_0 _ δ hz _ _)
    have hUpdB := update_inj_apply_w5 (β := ZMod 2) rBasis9 fun _ _ e ↦ rBasis9.wires.injective e
    funext w
    by_cases hm : ∃ u : Fin 9, rBasis9 u = w
    · obtain ⟨u, rfl⟩ := hm
      rw [Function.update_of_ne (disj_ne hBS u _), mkSt22_basis hBS]
      have h := hAg u
      fin_cases u <;> simp only [hUpdB, hηB, hηW] <;>
        first | exact g3 | exact g5 | exact g6 | exact g7 |
          exact h (by decide) (by decide) (by decide) (by decide)
    · simp only [fun (f : BitAssignment n) (u : Fin 9) (v : ZMod 2) ↦
        Function.update_of_ne (fun e ↦ hm ⟨u, e.symm⟩) v f]
      refine update_congr_at _ _ (update_congr_at _ _
        (update_congr_at _ _ (update_congr_at _ _ ?_)))
      rw [writeReg_apply_of_not_mem _ _ _ _ hm, writeReg_apply_of_not_mem _ _ _ _ hm]
  · simp only [Matrix.mulVec_zero]

theorem subspaceStep_post22_mkKetOpW {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)]
    (rWork : QRegister W n)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n)
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9) (hKS : rK4.DisjointWires rScr40)
    (hBS : rBasis9.DisjointWires rScr40)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hkLe : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 4 (fun i ↦ st δ (rK4 i)) ≤ 8)
    (hb0 : ∀ (δ : BitAssignment n) (u : Fin 9),
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rBasis9 u) = 0)
    (hLo0 : ∀ (δ : BitAssignment n) (u : Fin 40), u.val < 14 →
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rScr40 u) = 0) :
    SubspaceStep (Var := Var)
      (mkKetOpW rWork (mkSt22 rBasis9 rScr40 st (vfB2OutFn wScr wNN rK4 st)
        (c12Fn wScr wNN rK4 st) (c13Fn wScr wNN rK4 st)) ph)
      (mkKetOpW rWork (fun δ ↦ kpStep14 wScr wNN rK4 rBasis9 (st δ)) ph)
      (.circuit (cStageB2Post rK4 rBasis9 rScr40 hKB hBS)) := by
  refine subspaceStep_circuit_mkKetOpW rWork _ _ ph _ fun δ hz ↦ ?_
  simp only [cStageB2Post, eval_seq_mulVec, ket_CNOT, ket_X]
  rw [kpStep14_eq_writeReg hScrB hNNB hKB (st δ) fun u ↦ hb0 δ u hz]
  have hnb := not_k0_and_k3_of_le8 _ (hkLe δ hz)
  have hAg := z2_vStageB2In_agree (st δ wScr) (st δ wNN) (st δ (rK4 ⟨0, by decide⟩))
    (st δ (rK4 ⟨1, by decide⟩)) (st δ (rK4 ⟨2, by decide⟩)) (st δ (rK4 ⟨3, by decide⟩)) hnb
  have hz2 := (z2_stageB2_oneHot (st δ wScr) (st δ wNN) (st δ (rK4 ⟨0, by decide⟩))
    (st δ (rK4 ⟨1, by decide⟩)) (st δ (rK4 ⟨2, by decide⟩)) (st δ (rK4 ⟨3, by decide⟩))
    hnb).2.2.2.2.2.2.2
  let sNe (a b : Fin 40) (h : a ≠ b) :=
    Function.update_of_ne (β := fun _ ↦ ZMod 2) (rScr40_ne_of_ne rScr40 h)
  have hSc (u : Fin 9) (h3 : u ≠ ⟨3, by decide⟩) (h5 : u ≠ ⟨5, by decide⟩)
      (h6 : u ≠ ⟨6, by decide⟩) (h7 : u ≠ ⟨7, by decide⟩) :
      vfB2InFn wScr wNN rK4 st δ u + vfB2InFn wScr wNN rK4 st δ ⟨4, by decide⟩ +
        vfB2OutFn wScr wNN rK4 st δ ⟨4, by decide⟩ + vfB2OutFn wScr wNN rK4 st δ u = 0 := by
    dsimp only [vfB2InFn, vfB2OutFn]
    rw [hAg u h3 h5 h6 h7, hAg ⟨4, by decide⟩ (by decide) (by decide) (by decide) (by decide),
      show ∀ x y : ZMod 2, x + y + y + x = 0 by decide]
  simp only [Function.update_self, Function.update_idem,
    fun (f : BitAssignment n) s (v : ZMod 2) u ↦ Function.update_of_ne (disj_ne hBS u s) v f,
    fun (f : BitAssignment n) s (v : ZMod 2) i ↦ Function.update_of_ne (disj_ne hKS i s) v f,
    fun (f : BitAssignment n) u (v : ZMod 2) i ↦ Function.update_of_ne (disj_ne hKB i u) v f,
    sNe ⟨13, by decide⟩ ⟨12, by decide⟩ (by decide),
    sNe ⟨0, by decide⟩ ⟨12, by decide⟩ (by decide),
    sNe ⟨0, by decide⟩ ⟨13, by decide⟩ (by decide),
    Function.update_of_ne
      (rBasis9_ne_of_ne rBasis9 (by decide) : rBasis9 ⟨3, by decide⟩ ≠ rBasis9 ⟨2, by decide⟩),
    mkSt22_basis hBS, mkSt22_k4 hKB hKS, mkSt22_scr12, mkSt22_s13, mkSt22_s0,
    CharTwo.add_self_eq_zero]
  have hRS {vf} (u : Fin 40) (hu : u.val < 14) : writeReg (st δ) rBasis9 vf (rScr40 u) = 0 :=
    (writeReg_apply_of_not_mem _ _ _ _ fun ⟨v, hv⟩ ↦ disj_ne hBS v u hv).trans (hLo0 δ u hu hz)
  refine congrArg ket (funext fun w ↦ ?_)
  rcases eq_or_ne w (rBasis9 ⟨3, by decide⟩) with rfl | hb3
  · rw [Function.update_self, writeReg_apply_reg]
    exact hz2.2
  rw [Function.update_of_ne hb3]
  rcases eq_or_ne w (rBasis9 ⟨2, by decide⟩) with rfl | hb2
  · rw [Function.update_self, writeReg_apply_reg]
    exact hz2.1
  rw [Function.update_of_ne hb2]
  rcases eq_or_ne w (rScr40 ⟨0, by decide⟩) with rfl | hs0
  · rw [Function.update_self, hRS ⟨0, by decide⟩ (by decide)]
  rw [Function.update_of_ne hs0]
  rcases eq_or_ne w (rScr40 ⟨13, by decide⟩) with rfl | hs3
  · simpa only [Function.update_self, hRS ⟨13, by decide⟩ (by decide)] using
      hSc ⟨1, by decide⟩ (by decide) (by decide) (by decide) (by decide)
  rw [Function.update_of_ne hs3]
  rcases eq_or_ne w (rScr40 ⟨12, by decide⟩) with rfl | hs2
  · simpa only [Function.update_self, hRS ⟨12, by decide⟩ (by decide)] using
      hSc ⟨0, by decide⟩ (by decide) (by decide) (by decide) (by decide)
  simp only [mkSt22, Function.update_of_ne hs2, Function.update_of_ne hs3,
    Function.update_of_ne hs0]
  by_cases hm : ∃ u : Fin 9, rBasis9 u = w
  · obtain ⟨u, rfl⟩ := hm
    simp only [writeReg_apply_reg, vfB2OutFn, vStageB2Out,
      iteNeg fun e ↦ hb2 (congrArg rBasis9.wires (Fin.ext e)),
      iteNeg fun e ↦ hb3 (congrArg rBasis9.wires (Fin.ext e))]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hm, writeReg_apply_of_not_mem _ _ _ _ hm]

theorem subspaceStep_wRouter6_gather2 {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (rBasis9 : QRegister 9 n)
    (rScr40 : QRegister 40 n) (hBS : rBasis9.DisjointWires rScr40) (idx : Fin 3 → Wire n)
    (hd : WRouterDisj (rScr40 ⟨0, by decide⟩) idx (kpOut6 rScr40) (rScr40 ⟨1, by decide⟩))
    (u3 u5 : Fin 9) (cGat : Circuit n)
    (hGatKet : ∀ η : BitAssignment n, cGat.eval.1.mulVec (ket η) =
      ket (Function.update (Function.update η (rBasis9 u3)
        (η (rBasis9 u3) + η (kpOut6 rScr40 ⟨3, by decide⟩)))
        (rBasis9 u5) (η (rBasis9 u5) + η (kpOut6 rScr40 ⟨5, by decide⟩))))
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (vfIn vfOut : BitAssignment n → Fin 9 → ZMod 2)
    (hLo0 : ∀ (δ : BitAssignment n) (u : Fin 40), u.val < 14 →
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rScr40 u) = 0)
    (hIdxEq : ∀ δ, idxValD idx
      (Function.update (writeReg (st δ) rBasis9 (vfOut δ)) (rScr40 ⟨0, by decide⟩) 1) =
      idxValD idx (Function.update (writeReg (st δ) rBasis9 (vfIn δ)) (rScr40 ⟨0, by decide⟩) 1))
    (hStep : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      let vIdx := idxValD idx
        (Function.update (writeReg (st δ) rBasis9 (vfIn δ)) (rScr40 ⟨0, by decide⟩) 1)
      vIdx < 6 ∧ vfIn δ u3 + (if vIdx = 3 then 1 else 0) = vfOut δ u3 ∧
        vfIn δ u5 + (if vIdx = 5 then 1 else 0) = vfOut δ u5 ∧
        ∀ u : Fin 9, u ≠ u3 → u ≠ u5 → vfIn δ u = vfOut δ u) :
    SubspaceStep (Var := Var)
      (mkKetOpW rWork
        (fun δ ↦ Function.update (writeReg (st δ) rBasis9 (vfIn δ)) (rScr40 ⟨0, by decide⟩) 1) ph)
      (mkKetOpW rWork
        (fun δ ↦ Function.update (writeReg (st δ) rBasis9 (vfOut δ)) (rScr40 ⟨0, by decide⟩) 1) ph)
      ((wRouterBracket3x2k 1).wrap v (rScr40 ⟨0, by decide⟩) idx (kpOut6 rScr40)
        (rScr40 ⟨1, by decide⟩) (.circuit cGat)) := by
  let wHas := rScr40 ⟨0, by decide⟩
  let mkSt (vf : BitAssignment n → Fin 9 → ZMod 2) (δ : BitAssignment n) :=
    Function.update (writeReg (st δ) rBasis9 (vf δ)) wHas 1
  have hMkBasis (vf δ) (u : Fin 9) : mkSt vf δ (rBasis9 u) = vf δ u :=
    (Function.update_of_ne (disj_ne hBS u _) 1 _).trans (writeReg_apply_reg _ _ _ _)
  have hMkScr (vf δ) (u : Fin 40) (hu0 : u.val ≠ 0) : mkSt vf δ (rScr40 u) = st δ (rScr40 u) :=
    (Function.update_of_ne (rScr40_ne_of_ne rScr40 fun e ↦ hu0 (congrArg Fin.val e)) 1 _).trans
      (writeReg_apply_of_not_mem _ _ _ _ fun ⟨v, hv⟩ ↦ disj_ne hBS v u hv)
  have hwHasMk (vf δ) : mkSt vf δ wHas = 1 := Function.update_self wHas 1 _
  have hOut6_0 (vf δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) (j : Fin 6) :
      mkSt vf δ (kpOut6 rScr40 j) = 0 :=
    (hMkScr vf δ _ ((by decide : ∀ k : Fin 6, 2 + k.val ≠ 0) j)).trans
      (hLo0 δ _ ((by decide : ∀ k : Fin 6, 2 + k.val < 14) j) hz)
  have hLtOut (δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) : idxValD idx (mkSt vfOut δ) < 6 :=
    (hIdxEq δ).symm ▸ (hStep δ hz).1
  refine (wRouterBracket3x2k 1).subspaceStep_wrap v wHas idx (kpOut6 rScr40) _ hd (.circuit cGat)
    _ _ (supportedOn_mkKetOpW rWork _ ph fun δ hz ↦
      ⟨hOut6_0 vfIn δ hz, (hMkScr vfIn δ ⟨1, by decide⟩ (by decide)).trans
        (hLo0 δ ⟨1, by decide⟩ (by decide) hz), (hStep δ hz).1,
        fun h0 ↦ absurd ((hwHasMk vfIn δ).symm.trans h0) one_ne_zero⟩)
    (supportedOn_mkKetOpW rWork _ ph fun δ hz ↦
      ⟨hOut6_0 vfOut δ hz, hLtOut δ hz,
        fun h0 ↦ absurd ((hwHasMk vfOut δ).symm.trans h0) one_ne_zero⟩)
    (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ cGat)
      (matrix_ext_ket fun δ ↦ ?_))
  simp only [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, uOneHotToggle_mulVec_ket,
      uOneHotToggle_mulVec_ket, hGatKet]
    obtain ⟨hLtIn, hG3, hG5, hRest⟩ := hStep δ hz
    have hηOut6 (vf) (hLt : idxValD idx (mkSt vf δ) < 6) (j : Fin 6) :=
      (toggleOneHotBits_apply_out hd.out_inj (hOut6_0 vf δ hz) hLt j).trans (by rw [hwHasMk])
    have hηB (vf) (u : Fin 9) :
        toggleOneHotBits wHas idx (kpOut6 rScr40) (mkSt vf δ) (rBasis9 u) = vf δ u :=
      (toggleOneHotBits_apply_other (mkSt vf δ) fun _ ↦ disj_ne hBS _ _).trans (hMkBasis vf δ u)
    refine congrArg (_ • ket ·) (funext fun w ↦ ?_)
    rcases eq_or_ne w (rBasis9 u5) with rfl | hw5
    · rw [Function.update_self, hηB vfIn u5, hηOut6 vfIn hLtIn ⟨5, by decide⟩, hηB vfOut u5, hG5]
    rw [Function.update_of_ne hw5]
    rcases eq_or_ne w (rBasis9 u3) with rfl | hw3
    · rw [Function.update_self, hηB vfIn u3, hηOut6 vfIn hLtIn ⟨3, by decide⟩, hηB vfOut u3, hG3]
    rw [Function.update_of_ne hw3]
    by_cases hwO : ∃ j : Fin 6, w = kpOut6 rScr40 j
    · obtain ⟨j, rfl⟩ := hwO
      rw [hηOut6 vfIn hLtIn j, hηOut6 vfOut (hLtOut δ hz) j, hIdxEq δ]
    · rw [toggleOneHotBits_apply_other (mkSt vfIn δ) fun j e ↦ hwO ⟨j, e⟩,
        toggleOneHotBits_apply_other (mkSt vfOut δ) fun j e ↦ hwO ⟨j, e⟩]
      refine update_congr_at wHas 1 ?_
      by_cases hm : ∃ u : Fin 9, rBasis9 u = w
      · obtain ⟨u, rfl⟩ := hm
        simpa only [writeReg_apply_reg] using hRest u (fun e ↦ hw3 (congrArg rBasis9.wires e))
          fun e ↦ hw5 (congrArg rBasis9.wires e)
      · rw [writeReg_apply_of_not_mem _ _ _ _ hm, writeReg_apply_of_not_mem _ _ _ _ hm]
  · simp only [Matrix.mulVec_zero]

theorem subspaceStep_pKpBasis9Fwd22 {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (rBasis9 : QRegister 9 n) (rScr40 : QRegister 40 n) (hScrB : ∀ u, wScr ≠ rBasis9 u)
    (hNNB : ∀ u, wNN ≠ rBasis9 u) (_hScrS : ∀ u, wScr ≠ rScr40 u) (_hNNS : ∀ u, wNN ≠ rScr40 u)
    (hKB : rK4.DisjointWires rBasis9) (hKS : rK4.DisjointWires rScr40)
    (hBS : rBasis9.DisjointWires rScr40) (st : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) (hkLe : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
    natOfZModBits 4 (fun i ↦ st δ (rK4 i)) ≤ 8) (hb0 : ∀ (δ : BitAssignment n)
    (u : Fin 9), (∀ k : Fin W, δ (rWork k) = 0) → st δ (rBasis9 u) = 0)
    (hLo0 : ∀ (δ : BitAssignment n) (u : Fin 40), u.val < 14 → (∀ k : Fin W, δ (rWork k) = 0) →
    st δ (rScr40 u) = 0) : SubspaceStep (mkKetOpW rWork st ph)
    (mkKetOpW rWork (fun δ ↦ kpStep14 wScr wNN rK4 rBasis9 (st δ)) ph)
    (pKpBasis9Fwd22 v wScr wNN rK4 rBasis9 rScr40 hScrB hNNB hKB hBS) := by
  let wHas := rScr40 ⟨0, by decide⟩
  let mkSt (vf : BitAssignment n → Fin 9 → ZMod 2) (δ : BitAssignment n) :=
    Function.update (writeReg (st δ) rBasis9 (vf δ)) wHas 1
  let vfAIn (δ : BitAssignment n) (u : Fin 9) : ZMod 2 :=
    if u.val = 0 then st δ wScr + st δ wNN else 0
  let vfAOut (δ : BitAssignment n) := vStageAPreCnot (st δ wScr) (st δ wNN)
    (st δ (rK4 ⟨0, by decide⟩)) (st δ (rK4 ⟨3, by decide⟩))
  let vfMid1 (δ : BitAssignment n) := vStageA (st δ wScr) (st δ wNN)
    (st δ (rK4 ⟨0, by decide⟩)) (st δ (rK4 ⟨3, by decide⟩))
  let vfB1Out (δ : BitAssignment n) := vStageB1Out (st δ wScr) (st δ wNN)
    (st δ (rK4 ⟨0, by decide⟩)) (st δ (rK4 ⟨1, by decide⟩)) (st δ (rK4 ⟨3, by decide⟩))
  have hMkBasis (vf δ) (u : Fin 9) : mkSt vf δ (rBasis9 u) = vf δ u :=
    (Function.update_of_ne (disj_ne hBS u _) 1 _).trans (writeReg_apply_reg _ _ _ _)
  have hMkK (vf δ) (i : Fin 4) : mkSt vf δ (rK4 i) = st δ (rK4 i) :=
    (Function.update_of_ne (disj_ne hKS i _) 1 _).trans
      (writeReg_apply_of_not_mem _ _ _ _ fun ⟨v, hv⟩ ↦ disj_ne hKB i v hv.symm)
  have hMkScr (vf δ) (u : Fin 40) (hu0 : u.val ≠ 0) : mkSt vf δ (rScr40 u) = st δ (rScr40 u) :=
    (Function.update_of_ne (rScr40_ne_of_ne rScr40 fun e ↦ hu0 (congrArg Fin.val e)) 1 _).trans
      (writeReg_apply_of_not_mem _ _ _ _ fun ⟨v, hv⟩ ↦ disj_ne hBS v u hv)
  have hMkEq (vf₁ vf₂ δ) (w : Wire n) (h : ∀ u, rBasis9 u = w → vf₁ δ u = vf₂ δ u) :
      mkSt vf₁ δ w = mkSt vf₂ δ w := update_congr_at wHas 1 (by
    by_cases hm : ∃ u : Fin 9, rBasis9 u = w
    · obtain ⟨u, rfl⟩ := hm
      simpa only [writeReg_apply_reg] using h u rfl
    · rw [writeReg_apply_of_not_mem _ _ _ _ hm, writeReg_apply_of_not_mem _ _ _ _ hm])
  -- Step 1: cStageAPre (`st -> mkSt vfAIn`)
  have hsPre := subspaceStep_circuit_mkKetOpW (Var := Var) rWork st (mkSt vfAIn) ph
    (cStageAPre wScr wNN rBasis9 rScr40 hScrB hNNB) fun δ hz ↦ by
      dsimp only [cStageAPre]
      rw [eval_seq_mulVec, eval_seq_mulVec, ket_CNOT, ket_CNOT, ket_X, Function.update_idem,
        Function.update_self, Function.update_of_ne (hNNB _), hb0 δ ⟨0, by decide⟩ hz, zero_add,
        Function.update_of_ne (disj_ne hBS ⟨0, by decide⟩ _).symm,
        hLo0 δ ⟨0, by decide⟩ (by decide) hz, zero_add]
      refine congrArg ket (congrArg (Function.update · wHas 1) (funext fun w ↦ ?_))
      by_cases hm : ∃ u : Fin 9, rBasis9 u = w
      · obtain ⟨u, rfl⟩ := hm
        rw [writeReg_apply_reg]
        rcases eq_or_ne u ⟨0, by decide⟩ with rfl | hu0
        · simp [vfAIn]
        · rw [show vfAIn δ u = 0 from iteNeg fun e ↦ hu0 (Fin.ext e),
            Function.update_of_ne (rBasis9_ne_of_ne rBasis9 hu0), hb0 δ u hz]
      · rw [writeReg_apply_of_not_mem _ _ _ _ hm,
          Function.update_of_ne fun e ↦ hm ⟨⟨0, by decide⟩, e.symm⟩]
  -- Step 2: Stage A 6-way W-router (`mkSt vfAIn -> mkSt vfAOut`)
  have hMkB' (vf : _ → _ → _) (δ u) : Function.update (writeReg (st δ) rBasis9 (vf δ))
      (rScr40 ⟨0, by decide⟩) 1 (rBasis9 u) = vf δ u := hMkBasis vf δ u
  have hMkK' (vf : _ → _ → _) (δ i) : Function.update (writeReg (st δ) rBasis9 (vf δ))
      (rScr40 ⟨0, by decide⟩) 1 (rK4 i) = st δ (rK4 i) := hMkK vf δ i
  have hsWrapA := subspaceStep_wRouter6_gather2 v rWork rBasis9 rScr40 hBS (kpIdxA rBasis9 rK4)
    (wRouterDisj_kpA hBS hKS) ⟨1, by decide⟩ ⟨8, by decide⟩ (cStageAGather rScr40 rBasis9 hBS)
    (cStageAGather_mulVec_ket rScr40 rBasis9 hBS) st ph vfAIn vfAOut hLo0
    (fun δ ↦ by simp only [idxValD, idxValPrefix, kpIdxA, hMkB', hMkK']; rfl) fun δ hz ↦ by
      dsimp only []
      simp only [idxValD, idxValPrefix, kpIdxA, hMkB', hMkK']
      obtain ⟨hLt, h3, h5⟩ := z2_stageA_oneHot (st δ wScr + st δ wNN)
        (st δ (rK4 ⟨0, by decide⟩)) (st δ (rK4 ⟨3, by decide⟩))
        (not_k0_and_k3_of_le8 _ (hkLe δ hz))
      exact ⟨hLt, h3, h5, fun u hu1 hu8 ↦ by
        fin_cases u <;> first | rfl | exact absurd rfl hu1 | exact absurd rfl hu8⟩
  -- Step 3: CNOT `rK4[0] -> rBasis9[0]` (`mkSt vfAOut -> mkSt vfMid1`)
  have hsCnotA := subspaceStep_circuit_mkKetOpW (Var := Var) rWork (mkSt vfAOut) (mkSt vfMid1)
    ph (Circuit.CNOT (rK4 ⟨0, by decide⟩) (rBasis9 ⟨0, by decide⟩) (disj_ne hKB _ _)) fun δ _ ↦ by
      rw [ket_CNOT, hMkBasis vfAOut δ ⟨0, by decide⟩, hMkK vfAOut δ ⟨0, by decide⟩]
      refine congrArg ket (funext fun w ↦ ?_)
      rcases eq_or_ne w (rBasis9 ⟨0, by decide⟩) with rfl | hw0
      · rw [Function.update_self, hMkBasis vfMid1 δ ⟨0, by decide⟩]
        rfl
      · exact (Function.update_of_ne hw0 _ _).trans (hMkEq vfAOut vfMid1 δ w fun u hu ↦ by
          fin_cases u <;> first | rfl | exact absurd hu.symm hw0)
  -- Step 4: Stage B1 6-way W-router (`mkSt vfMid1 -> mkSt vfB1Out`)
  have hsWrapB1 := subspaceStep_wRouter6_gather2 v rWork rBasis9 rScr40 hBS
    (kpIdxB1 rK4 rBasis9) (wRouterDisj_kpB1 hKS hBS) ⟨4, by decide⟩ ⟨2, by decide⟩
    (cStageB1Gather rScr40 rBasis9 hBS) (cStageB1Gather_mulVec_ket rScr40 rBasis9 hBS)
    st ph vfMid1 vfB1Out hLo0
    (fun δ ↦ by simp only [idxValD, idxValPrefix, kpIdxB1, hMkB', hMkK']; rfl) fun δ _ ↦ by
      dsimp only []
      simp only [idxValD, idxValPrefix, kpIdxB1, hMkB', hMkK']
      obtain ⟨hLt, h3, h5⟩ := z2_stageB1_oneHot (st δ wScr + st δ wNN)
        (st δ (rK4 ⟨0, by decide⟩)) (st δ (rK4 ⟨1, by decide⟩))
      exact ⟨hLt, h3, h5, fun u hu4 hu2 ↦ by
        fin_cases u <;> first | rfl | exact absurd rfl hu4 | exact absurd rfl hu2⟩
  -- Step 5: cStageB2Mid (`mkSt vfB1Out -> mkSt22 vfB2InFn`)
  have hsMid2 := subspaceStep_circuit_mkKetOpW (Var := Var) rWork (mkSt vfB1Out)
    (mkSt22 rBasis9 rScr40 st (vfB2InFn wScr wNN rK4 st)
      (c12Fn wScr wNN rK4 st) (c13Fn wScr wNN rK4 st)) ph
    (cStageB2Mid rK4 rBasis9 rScr40 hKB hBS) fun δ hz ↦ by
      dsimp only [cStageB2Mid]
      simp only [eval_seq_mulVec, ket_CNOT]
      have hs0 (u : Fin 40) (hu0 : u.val ≠ 0) (hu14 : u.val < 14) :=
        (hMkScr vfB1Out δ u hu0).trans (hLo0 δ u hu14 hz)
      let bNe (x y : Fin 9) (h : x ≠ y) :=
        Function.update_of_ne (β := fun _ ↦ ZMod 2) (rBasis9_ne_of_ne rBasis9 h)
      simp only [Function.update_self, Function.update_idem,
        bNe ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide),
        bNe ⟨4, by decide⟩ ⟨1, by decide⟩ (by decide),
        fun (f : BitAssignment n) u (v : ZMod 2) s ↦
          Function.update_of_ne (disj_ne hBS u s).symm v f,
        fun (f : BitAssignment n) s (v : ZMod 2) u ↦ Function.update_of_ne (disj_ne hBS u s) v f,
        Function.update_of_ne
          (rScr40_ne_of_ne rScr40 (by decide) : rScr40 ⟨13, by decide⟩ ≠ rScr40 ⟨12, by decide⟩),
        hMkBasis vfB1Out δ, hMkK vfB1Out δ,
        hs0 ⟨12, by decide⟩ (by decide) (by decide),
        hs0 ⟨13, by decide⟩ (by decide) (by decide), zero_add]
      have hzid := z2_stageB2Mid_identities (st δ wScr) (st δ wNN)
        (st δ (rK4 ⟨0, by decide⟩)) (st δ (rK4 ⟨1, by decide⟩)) (st δ (rK4 ⟨3, by decide⟩))
      refine congrArg ket (funext fun w ↦ ?_)
      rcases eq_or_ne w (rScr40 ⟨13, by decide⟩) with rfl | hw13
      · rw [Function.update_self, mkSt22_s13]
        exact hzid.1
      rw [Function.update_of_ne hw13]
      rcases eq_or_ne w (rScr40 ⟨12, by decide⟩) with rfl | hw12
      · rw [Function.update_self, mkSt22_scr12]
        exact hzid.2.1
      rw [Function.update_of_ne hw12]
      rcases eq_or_ne w (rBasis9 ⟨1, by decide⟩) with rfl | hw1
      · rw [Function.update_self, mkSt22_basis hBS]
        exact hzid.2.2
      rw [Function.update_of_ne hw1]
      dsimp only [mkSt22]
      rw [Function.update_of_ne hw13, Function.update_of_ne hw12]
      exact hMkEq vfB1Out (vfB2InFn wScr wNN rK4 st) δ w fun u hu ↦ by
        fin_cases u <;> first | rfl | exact absurd hu.symm hw1
  unfold pKpBasis9Fwd22
  exact subspaceStep_seq_u hsPre (subspaceStep_seq_u hsWrapA (subspaceStep_seq_u hsCnotA
    (subspaceStep_seq_u hsWrapB1 (subspaceStep_seq_u hsMid2
      (subspaceStep_seq_u
        (subspaceStep_stageB2_mkKetOpW v rWork wScr wNN rK4 rBasis9 rScr40 hKB hKS hBS st ph
          hkLe hLo0)
        (subspaceStep_post22_mkKetOpW rWork wScr wNN rK4 rBasis9 rScr40 hScrB hNNB hKB hKS
          hBS st ph hkLe hb0 hLo0))))))
/--
Globally optimal `22-T` forward + `0-T` reverse W-state `KpBasis9Pkg` (`-2 T/step` vs
`kpBasis9WRouterPkg24` ).
-/
def kpBasis9WRouterPkg22 : KpBasis9Pkg 22 where
  pFwd := @pKpBasis9Fwd22
  pRev := @pKpBasis9Rev0
  fwd_counts_wires := @pKpBasis9Fwd22_counts_wires
  rev_counts_wires := @pKpBasis9Rev0_counts_wires
  fwd_step := @subspaceStep_pKpBasis9Fwd22
  rev_step := @subspaceStep_pKpBasis9Rev0
end


def pKpBasis9Unshift30Rev0 {Var : Type} {tBasis n : ℕ} (pkgBasis : KpBasis9Pkg tBasis) (v : Var)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rBasis9 : QRegister 9 n) (rCopy30 : QRegister 30 n)
    (rScr40 : QRegister 40 n) (rYHi33 : QRegister 33 n) (hScrB : ∀ u, wScr ≠ rBasis9 u)
    (hNNB : ∀ u, wNN ≠ rBasis9 u) (hKB : rK4.DisjointWires rBasis9)
    (hBC : rBasis9.DisjointWires rCopy30) (hBS : rBasis9.DisjointWires rScr40)
    (hCS : rCopy30.DisjointWires rScr40) : DynamicCircuit Var n :=
    .seq (pUnshift30ZeroUnload_33_k9 v rBasis9 rCopy30 rScr40 rYHi33 hBC hBS hCS)
    (pkgBasis.pRev v wScr wNN rK4 rBasis9 hScrB hNNB hKB)
theorem subspaceStep_pKpBasis9Unshift30Rev0 {Var : Type} [Fintype Var] [DecidableEq Var]
    {tBasis W n : ℕ} [NeZero (2 ^ n)]
    (pkgBasis : KpBasis9Pkg tBasis) (v : Var) (rWork : QRegister W n)
    (wScr wNN : Wire n) (rK4 : QRegister 4 n)
    (rBasis9 : QRegister 9 n) (rCopy30 : QRegister 30 n)
    (rScr40 : QRegister 40 n) (rYHi33 : QRegister 33 n)
    (hScrB : ∀ u, wScr ≠ rBasis9 u) (hNNB : ∀ u, wNN ≠ rBasis9 u)
    (hKB : rK4.DisjointWires rBasis9)
    (hBC : rBasis9.DisjointWires rCopy30) (hBS : rBasis9.DisjointWires rScr40)
    (hCS : rCopy30.DisjointWires rScr40)
    (hBY : rBasis9.DisjointWires rYHi33) (hCY : rCopy30.DisjointWires rYHi33)
    (hSY : rScr40.DisjointWires rYHi33)
    (st stWB : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (x32Fn : BitAssignment n → ℕ)
    (hx32 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → x32Fn δ < 2 ^ 32)
    (hkLe : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 4 (fun i ↦ st δ (rK4 i)) ≤ 8)
    (hValid : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → ¬(st δ wScr = 0 ∧ st δ wNN = 1))
    (hCopy : ∀ (δ : BitAssignment n) (c : Fin 30), (∀ k : Fin W, δ (rWork k) = 0) →
      st δ (rCopy30 c) = if (x32Fn δ).testBit (2 + c.val) then 1 else 0)
    (hb0 : ∀ (δ : BitAssignment n) (u : Fin 9),
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rBasis9 u) = 0)
    (hScr10 : ∀ (δ : BitAssignment n) (u : Fin 40), u.val < 10 →
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rScr40 u) = 0)
    (hY0 : ∀ (δ : BitAssignment n) (b2 : Fin 33),
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rYHi33 b2) = 0)
    (hWB : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      stWB δ = writeReg (kpStep14 wScr wNN rK4 rBasis9 (st δ)) rYHi33
        (fun b2 ↦
          let kp := kpOfBits (st δ wScr) (st δ wNN) (fun i ↦ st δ (rK4 i))
          if (((mask30 (x32Fn δ)) <<< 4) >>> kp).testBit (3 + b2.val) then 1 else 0)) :
    SubspaceStep (mkKetOpW rWork stWB ph) (mkKetOpW rWork st ph)
      (pKpBasis9Unshift30Rev0 pkgBasis v wScr wNN rK4 rBasis9 rCopy30 rScr40 rYHi33
        hScrB hNNB hKB hBC hBS hCS) ∧
    (pKpBasis9Unshift30Rev0 pkgBasis v wScr wNN rK4 rBasis9 rCopy30 rScr40 rYHi33
      hScrB hNNB hKB hBC hBS hCS).count .T = 0 ∧
    (pKpBasis9Unshift30Rev0 pkgBasis v wScr wNN rK4 rBasis9 rCopy30 rScr40 rYHi33
      hScrB hNNB hKB hBC hBS hCS).count .TOFF = 0 ∧
    (∀ S : Wire n → Prop,
      S wScr → S wNN → (∀ i, S (rK4 i)) → (∀ u, S (rBasis9 u)) →
      (∀ c, S (rCopy30 c)) → (∀ u, S (rScr40 u)) → (∀ b2, S (rYHi33 b2)) →
      DynWires S (pKpBasis9Unshift30Rev0 pkgBasis v wScr wNN rK4 rBasis9 rCopy30 rScr40 rYHi33
        hScrB hNNB hKB hBC hBS hCS)) := by
  let stKM (δ : BitAssignment n) := kpStep14 wScr wNN rK4 rBasis9 (st δ)
  let kpFn (δ : BitAssignment n) := kpOfBits (st δ wScr) (st δ wNN) fun i ↦ st δ (rK4 i)
  have hNonB (δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) (w : Wire n) (hw : ∀ u, w ≠ rBasis9 u) :
      stKM δ w = st δ w :=
    (congrFun (kpStep14_eq_writeReg hScrB hNNB hKB (st δ) fun u ↦ hb0 δ u hz) w).trans
      (writeReg_apply_of_not_mem _ _ _ _ fun ⟨u, hu⟩ ↦ hw u hu.symm)
  obtain ⟨hUn, htUn, hfUn, hdUn⟩ := subspaceStep_pUnshift30ZeroUnload_33_k9 v rWork
    rBasis9 rCopy30 rScr40 rYHi33 hBC hBS hCS hBY hCY hSY stKM stWB ph x32Fn kpFn hx32
    (fun δ hz ↦ by
      have := hkLe δ hz
      dsimp only [kpFn, kpOfBits]
      split_ifs <;> omega)
    (fun δ c hz ↦ (hNonB δ hz _ fun u ↦ (disj_ne hBC u c).symm).trans (hCopy δ c hz))
    (fun δ u hz ↦ by
      dsimp only [stKM, kpFn]
      rw [kpStep14_eq_writeReg hScrB hNNB hKB (st δ) fun u ↦ hb0 δ u hz, writeReg_apply_reg]
      exact kpBasis9Vec_eq_code _ _ _ (hkLe δ hz) (hValid δ hz) u)
    (fun δ u hu10 hz ↦ (hNonB δ hz _ fun v ↦ (disj_ne hBS v u).symm).trans (hScr10 δ u hu10 hz))
    (fun δ b2 hz ↦ (hNonB δ hz _ fun v ↦ (disj_ne hBY v b2).symm).trans (hY0 δ b2 hz)) hWB
  obtain ⟨tR, fR, _⟩ := pkgBasis.rev_counts_wires (S := fun _ ↦ True) v wScr wNN rK4 rBasis9
    hScrB hNNB hKB trivial trivial (fun _ ↦ trivial) (fun _ ↦ trivial)
  exact ⟨subspaceStep_seq_u hUn (pkgBasis.rev_step v rWork wScr wNN rK4 rBasis9 hScrB hNNB
    hKB st ph hb0), congrArg₂ (· + ·) htUn tR, congrArg₂ (· + ·) hfUn fR,
    fun S hScr hNN hrK hrB hrC hrS hrY ↦ ⟨hdUn S hrB hrC hrS hrY,
      (pkgBasis.rev_counts_wires v wScr wNN rK4 rBasis9 hScrB hNNB hKB hScr hNN hrK hrB).2.2⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.KpBasis9WRouterOpt
end


noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.NucPairFlags
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate
  PhotochemistrySolution.KetSupport PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.Stage12Compact
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.PotOraclePortB
  PhotochemistrySolution.PotOraclePortBStream PhotochemistrySolution.PotOraclePortBStage4
  PhotochemistrySolution.Coin70Lift PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.ReflStage4
open PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket ket_CNOT)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1 (rElecSub)
open scoped Circuit.Notation
/-! ## Part A: `18`-Wire Electronic Control Multiplexing for Low-Index Bell Pairs -/

theorem z2_add_self_nf2 (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl
end QuantumComputation.Specs.PhotochemistrySolution.NucPairFlags
end


noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW338Wp237
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate
  PhotochemistrySolution.KetSupport PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.ProviderCoreFused
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.SortedRouterSpec
  PhotochemistrySolution.PotOraclePortB PhotochemistrySolution.PotOraclePortBStream
  PhotochemistrySolution.PotOraclePortBStage4 PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF
open PhotochemistrySolution.Coin70Lift PhotochemistrySolution.Sub5885
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.ReflStage4
  PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.WStateStage2Load PhotochemistrySolution.WStateWalkSeam
open PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.RouterAlwaysLoW338
  PhotochemistrySolution.NucPairFlags
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket ket_CNOT eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated hiding zg47_hM0
open scoped Circuit.Notation
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr
theorem routerAlwaysLoUnitaries_congr_of_muxD1RolesEq_elec {n : ℕ} {r₁ r₂ : RouterReg 187 8 n}
    (hR : MuxD1RolesEq r₁ r₂) : (∀ β : BitAssignment n, cLoAlways r₁ β = cLoAlways r₂ β ∧
    routerCtrlHi r₁ β = routerCtrlHi r₂ β) ∧ (∀ cLo cHi, cFixedSwapCirc r₁ cLo cHi =
    cFixedSwapCirc r₂ cLo cHi) ∧ (uBellLoCopyHiAlwaysLoConj r₁).1 =
    (uBellLoCopyHiAlwaysLoConj r₂).1 := by
  obtain ⟨r1, r2, ri1, ri2, rbl, rbh, rha, rhb, rsy⟩ := hR
  have hCtrlEq : ∀ β : BitAssignment n,
      cLoAlways r₁ β = cLoAlways r₂ β ∧ routerCtrlHi r₁ β = routerCtrlHi r₂ β := fun β ↦ by
    constructor
    · funext p; unfold cLoAlways; simp only [ri1]
    · funext p; unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; simp only [r2, ri1, ri2]
  have hSysFlip : (fun (b : Fin 24) (p : Fin 187) ↦ rSys r₁ p b) = (fun b p ↦ rSys r₂ p b) :=
    funext fun b ↦ funext fun p ↦ congrFun (congrFun rsy p) b
  have hSVEq : ∀ (q₁ q₂ : Fin 24 → Wire n) (cV : Fin 187 → ZMod 2)
      (t₁ t₂ : Fin 24 → Fin 187 → Wire n) (h₁ : ∀ b p, q₁ b ≠ t₁ b p) (h₂ : ∀ b p, q₂ b ≠ t₂ b p),
      q₁ = q₂ → t₁ = t₂ → fixedSwapVecCirc 187 24 q₁ cV t₁ h₁ =
      fixedSwapVecCirc 187 24 q₂ cV t₂ h₂ := by rintro _ _ _ _ _ _ _ rfl rfl; rfl
  have hBVEq : ∀ (q₁ q₂ : Fin 24 → Wire n) (cV : Fin 187 → ZMod 2)
      (t₁ t₂ : Fin 24 → Fin 187 → Wire n) (h₁ : ∀ b p, q₁ b ≠ t₁ b p) (h₂ : ∀ b p, q₂ b ≠ t₂ b p),
      q₁ = q₂ → t₁ = t₂ → fixedBellVecCirc 187 24 q₁ cV t₁ h₁ =
      fixedBellVecCirc 187 24 q₂ cV t₂ h₂ := by rintro _ _ _ _ _ _ _ rfl rfl; rfl
  have hFVEq : ∀ (q₁ q₂ : Fin 24 → Wire n) (cV : Fin 187 → ZMod 2)
      (t₁ t₂ : Fin 24 → Fin 187 → Wire n) (h₁ : ∀ b p, q₁ b ≠ t₁ b p) (h₂ : ∀ b p, q₂ b ≠ t₂ b p),
      q₁ = q₂ → t₁ = t₂ → fixedFanoutVecCirc 187 24 q₁ cV t₁ h₁ =
      fixedFanoutVecCirc 187 24 q₂ cV t₂ h₂ := by rintro _ _ _ _ _ _ _ rfl rfl; rfl
  refine ⟨hCtrlEq, fun cLo cHi ↦ ?_, ?_⟩
  · dsimp only [cFixedSwapCirc];
    rw [hSVEq _ _ _ _ _ _ _ rbl hSysFlip, hSVEq _ _ _ _ _ _ _ rbh hSysFlip]
  · refine matrix_ext_ket fun β ↦ ?_
    rw [uBellLoCopyHiAlwaysLoConj_mulVec_ket_any r₁ β,
        uBellLoCopyHiAlwaysLoConj_mulVec_ket_any r₂ β, (hCtrlEq β).1,
        (hCtrlEq β).2]; dsimp only [cFixedBellLoCopyHiCirc]; rw [hBVEq _ _ _ _ _ _ _ rha hSysFlip,
        hFVEq _ _ _ _ _ _ _ rbh hSysFlip]
def pLoadEAlwaysLoW338 {Var : Type} {n : ℕ} (o2E : Stage2ElecAlwaysLoPkg UsedNoNFW346) (v : Var)
    (rTot : QRegister dLayout n) : DynamicCircuit Var n :=
    .seq (.circuit (cOut40Scrub3 rTot))
    (.seq (o2E.pLoadE v ((rTot.compose rPermScrub338).compose rElecSub))
    (.circuit (cOut40Scrub3 rTot)))
theorem counts_pLoadEAlwaysLoW338 {Var : Type} [Finite Var] {n : ℕ}
    (o2E : Stage2ElecAlwaysLoPkg UsedNoNFW346) (v : Var) (rTot : QRegister dLayout n) :
    (pLoadEAlwaysLoW338 o2E v rTot).count .T = o2E.tLoadE ∧
    (pLoadEAlwaysLoW338 o2E v rTot).count .TOFF = 0 := by
  obtain ⟨tS, fS⟩ := counts_cOut40Scrub3 rTot; obtain ⟨tE, fE⟩ :=
      o2E.countE v ((rTot.compose rPermScrub338).compose rElecSub); dsimp only [pLoadEAlwaysLoW338,
      DynamicCircuit.count]; rw [tS, fS, tE, fE]
  exact ⟨by omega, rfl⟩

theorem cLoAlways_routerCtrlHi_eq_of_routerCtrlSet {M D n : ℕ} (r : RouterReg M D n)
    {α β : BitAssignment n} (hEq : ∀ u, RouterCtrlSet r u → α u = β u) : cLoAlways r α =
    cLoAlways r β ∧ routerCtrlHi r α = routerCtrlHi r β :=
  ⟨funext fun p ↦ by
     dsimp only [cLoAlways]
     rw [idxValD_eq_of_bitEq (rIdx1 r) α (rIdx1 r) β fun d ↦
         hEq _ (Or.inr (Or.inr (Or.inl ⟨d, rfl⟩)))],
   (routerCtrlPair_eq_of_eq r hEq).2⟩

theorem subspaceStep_pLoadEAlwaysLoW338 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)]
    (o2E : Stage2ElecAlwaysLoPkg UsedNoNFW346)
    (v : Var) (rTot : QRegister dLayout n) (R : Operator (2 ^ n))
    (hVE : SupportedOn (ValidZeroGatedSortedRouterInput (rTot.compose rElecSub)) R)
    (hRel : SupportedOn (Out40Scrub3Rel rTot) R) :
    let rE := rTot.compose rElecSub
    SubspaceStep (Var := Var) R
      ((uBellLoCopyHiAlwaysLoConj rE).1 * ((uRouterSwapAlwaysLoConj rE).1 * R))
      (pLoadEAlwaysLoW338 o2E v rTot) := by
  intro rE
  let rE' := (rTot.compose rPermScrub338).compose rElecSub
  obtain ⟨hCtrlEq, hSwapEq, hBellEq⟩ :=
    routerAlwaysLoUnitaries_congr_of_muxD1RolesEq_elec (muxD1RolesEq_rPermScrub338_elec rTot)
  have hSuppIn : SupportedOn (ValidZeroGatedSortedRouterInput rE')
      ((cOut40Scrub3 rTot).eval.1 * R) := fun A B hAB ↦ by
    rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
    refine (supportedOn_and hVE hRel) _ _ fun β ⟨hv, hr⟩ ↦ ?_
    simpa only [← Matrix.mulVec_mulVec, cOut40Scrub3_mulVec_ket] using
      hAB _ (validZeroGatedSorted_scrub3_rE' rTot hv hr)
  refine subspaceStep_congr_out ((subspaceStep_of_circuit R _).seq
    ((o2E.stepE v rE' _ hSuppIn).seq (subspaceStep_of_circuit _ _))) ?_
  rw [hBellEq]
  simp only [← Matrix.mul_assoc]
  refine (supportedOn_and hVE hRel) _ _ fun β _ ↦ ?_
  simp only [← Matrix.mulVec_mulVec, cOut40Scrub3_mulVec_ket]
  let β' := scrub3XorBits rTot β
  have pubEq (j : Fin (routerWidth 187 8)) (hj : j.val < 4602) : β' (rE' j) = β (rE j) := by
    rw [rPermScrub338_elecPub_eq rTot hj]
    have neT {wt : Wire dLayout} (hwt : wt.val = 5747 ∨ wt.val = 5749 ∨ wt.val = 5750) :
        rTot (elecSubWireFn j) ≠ rTot wt := fun e ↦ by
      have hv0 := congrArg Fin.val (rTot.wires.injective e)
      rw [val_elecSubWireFn j] at hv0
      split_ifs at hv0 <;> omega
    change scrub3XorBits rTot β (rTot (elecSubWireFn j)) = β (rTot (elecSubWireFn j))
    unfold scrub3XorBits
    rw [ite_eq_right (neT (Or.inl val_wOut32)), ite_eq_right (neT (Or.inr (Or.inl val_wOut34))),
      ite_eq_right (neT (Or.inr (Or.inr val_wOut35)))]
  have hPair' := cLoAlways_routerCtrlHi_eq_of_routerCtrlSet rE fun u hu ↦ by
    obtain ⟨j, hj, rfl⟩ := routerCtrlSet_pubIdx_elec hu
    exact (congrArg β' (rPermScrub338_elecPub_eq rTot (j := j) (by omega)).symm).trans
      (pubEq j (by omega))
  rw [uRouterSwapAlwaysLoConj_mulVec_ket_any rE' β', (hCtrlEq β').1, (hCtrlEq β').2,
    hPair'.1, hPair'.2, hSwapEq]
  let cSw := cFixedSwapCirc rE (cLoAlways rE β) (routerCtrlHi rE β)
  let cBl := cFixedBellLoCopyHiCirc rE (cLoAlways rE β) (routerCtrlHi rE β)
  have hSys (b : Fin 24) (q : Fin 187) : AllPlaneMod rE (rSys rE q b) :=
    ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨q, (planeOfRouter_sys rE b q).symm⟩)))⟩
  have hcSw : HCNOTSupportedIn (AllPlaneMod rE) cSw := .seq
    (hcnotSupportedIn_fixedSwapVec _ 24 _ _ _ (fun b ↦ ⟨b, Or.inl rfl⟩) fun b q _ ↦ hSys b q)
    (hcnotSupportedIn_fixedSwapVec _ 24 _ _ _ (fun b ↦ ⟨b, Or.inr (Or.inl rfl)⟩)
      fun b q _ ↦ hSys b q)
  have hBellOn (γ : BitAssignment n) (h1 : cLoAlways rE γ = cLoAlways rE β)
      (h2 : routerCtrlHi rE γ = routerCtrlHi rE β) :
      (uBellLoCopyHiAlwaysLoConj rE).1.mulVec (cSw.eval.1.mulVec (ket γ)) =
        cBl.eval.1.mulVec (cSw.eval.1.mulVec (ket γ)) :=
    hcSw.preservesKetPred (P := fun α ↦ ∀ u, RouterCtrlSet rE u → α u = γ u)
      (fun {u} hu α val hα w hw ↦ (Function.update_of_ne (fun e ↦
        let ⟨j, hj, hw'⟩ := routerCtrlSet_pubIdx_elec hw
        not_allPlaneMod_of_pubIdx rE j (by omega)
          ((congrArg (AllPlaneMod rE) (hw'.symm.trans e)).mpr hu)) _ _).trans (hα w hw))
      (preservesKetPred_ket fun _ _ ↦ rfl) _ _ fun α hα ↦ by
        have pα := cLoAlways_routerCtrlHi_eq_of_routerCtrlSet rE hα
        rw [uBellLoCopyHiAlwaysLoConj_mulVec_ket_any rE α, pα.1, pα.2, h1, h2]
  rw [hBellOn β' hPair'.1 hPair'.2, uRouterSwapAlwaysLoConj_mulVec_ket_any rE β, hBellOn β rfl rfl]
  have hComm {c : Circuit n} (hc : HCNOTSupportedIn (AllPlaneMod rE) c) :=
    (hcnotSupportedIn_cOut40Scrub3 rTot).comm hc fun _ ↦ scrub3_disj_allPlaneMod_elec rTot
  have hMat : (cOut40Scrub3 rTot).eval.1 *
      (cBl.eval.1 * (cSw.eval.1 * (cOut40Scrub3 rTot).eval.1)) = cBl.eval.1 * cSw.eval.1 := by
    rw [← Matrix.mul_assoc, hComm (hcnotSupportedIn_cFixedBellLoCopyHiCirc_allPlaneMod rE _ _),
      Matrix.mul_assoc cBl.eval.1, ← Matrix.mul_assoc (cOut40Scrub3 rTot).eval.1, hComm hcSw,
      Matrix.mul_assoc, cOut40Scrub3_mul_self, Matrix.mul_one]
  simpa only [← Matrix.mulVec_mulVec, cOut40Scrub3_mulVec_ket] using
    congrArg (fun M : Operator (2 ^ n) ↦ M.mulVec (ket β)) hMat

/-! ## Part 3: `pNucKinAlwaysLoW338` (`5,380 + 446/450 T` Stage-2N+3 at `wWork = 338`) -/
end QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW338Wp237
end


noncomputable section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat PrimitiveGate PhotochemistrySolution.KetSupport
   PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.WStateRouterPrim
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
private theorem ket_sr_47 {n : ℕ} (δ : BitAssignment n) :
    PhotochemistrySolution.SplitRouterSeqBell26k.ket δ = ket δ := rfl

private theorem eval_X_mul_self_47 {n : ℕ} (q : Wire n) : (Circuit.X q).eval.1 *
    (Circuit.X q).eval.1 = 1 := by
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, ket_X, ket_X, Function.update_idem, Function.update_self, add_assoc,
      CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self, Matrix.one_mulVec]

private theorem mulVec_X_invol_47 {n : ℕ} (q : Wire n) (v : Fin (2 ^ n) → ℂ) :
    (Circuit.X q).eval.1.mulVec ((Circuit.X q).eval.1.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, eval_X_mul_self_47, Matrix.one_mulVec]
private theorem eval_CNOT_mul_self_47 {n : ℕ} (c t : Wire n)
    (h : c ≠ t) : (Circuit.CNOT c t h).eval.1 * (Circuit.CNOT c t h).eval.1 = 1 := by
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, ket_CNOT, ket_CNOT, Function.update_idem, Function.update_self,
      Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero, add_zero,
      Function.update_eq_self, Matrix.one_mulVec]

private theorem mulVec_CNOT_invol_47 {n : ℕ} (c t : Wire n) (h : c ≠ t) (v : Fin (2 ^ n) → ℂ) :
    (Circuit.CNOT c t h).eval.1.mulVec ((Circuit.CNOT c t h).eval.1.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, eval_CNOT_mul_self_47, Matrix.one_mulVec]
private theorem ket_wZeroGate_of_one {n : ℕ} {wHas t0 : Wire n} (h : wHas ≠ t0)
    {δ : BitAssignment n} (h1 : δ wHas = 1) : (wZeroGate wHas t0 h).eval.1.mulVec (ket δ) =
    ket δ := by
  dsimp only [wZeroGate];
  rw [eval_seq_mulVec, ket_X, ket_CNOT, Function.update_of_ne h, h1, Function.update_self,
      add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_idem, Function.update_eq_self]
private theorem ket_wZeroGate_of_zero {n : ℕ} {wHas t0 : Wire n} (h : wHas ≠ t0)
    {δ : BitAssignment n} (h0 : δ wHas = 0) : (wZeroGate wHas t0 h).eval.1.mulVec (ket δ) =
    ket (Function.update δ t0 (δ t0 + 1)) := by
  dsimp only [wZeroGate];
  have hc0 : Function.update δ t0 (δ t0 + 1) wHas = 0 :=
      (Function.update_of_ne h _ δ).trans h0; rw [eval_seq_mulVec, ket_X, ket_CNOT_ctrl_zero h hc0]
private theorem ite_pow2_47 (P : Prop) [Decidable P] (k : ℕ) : (if P then 2 ^ k else 0) = 2 ^ k *
    (if P then 1 else 0) := by split_ifs <;> omega
abbrev uIdx5 {n : ℕ} (wIdx : Fin 6 → Wire n) (d : Fin 5) : Wire n :=
  wIdx ⟨if d.val < 3 then d.val else d.val + 1, by have := d.isLt; split_ifs <;> omega⟩

abbrev uBit3 {n : ℕ} (wIdx : Fin 6 → Wire n) (_ : Fin 1) : Wire n :=
  wIdx ⟨3, by omega⟩

theorem idxValD_6_split_bit3 {n : ℕ} (wIdx : Fin 6 → Wire n) (δ : BitAssignment n) :
    idxValD wIdx δ = 16 * (idxValD (uIdx5 wIdx) δ / 8) + 8 * idxValPrefix (uBit3 wIdx) δ 1 le_rfl +
    (idxValD (uIdx5 wIdx) δ % 8) := by
  let b (i : ℕ) (h : i < 6 := by decide) : ℕ := if δ (wIdx ⟨i, h⟩) = 1 then 1 else 0
  have hb (i : ℕ) (h : i < 6) : b i h ≤ 1 := by dsimp only [b]; split_ifs <;> omega
  have _ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ :=
    ⟨hb 0 (by decide), hb 1 (by decide), hb 2 (by decide),
     hb 3 (by decide), hb 4 (by decide), hb 5 (by decide)⟩
  dsimp only [idxValD, idxValPrefix, uIdx5, uBit3]
  simp only [ite_pow2_47]
  change 0 + 1 * b 0 + 2 * b 1 + 4 * b 2 + 8 * b 3 + 16 * b 4 + 32 * b 5 =
    16 * ((0 + 1 * b 0 + 2 * b 1 + 4 * b 2 + 8 * b 4 + 16 * b 5) / 8) + 8 * (0 + 1 * b 3) +
      (0 + 1 * b 0 + 2 * b 1 + 4 * b 2 + 8 * b 4 + 16 * b 5) % 8
  omega
theorem uIdx5_lt24_of_lt47 {n : ℕ} {wIdx : Fin 6 → Wire n} {δ : BitAssignment n}
    (hLt : idxValD wIdx δ < 47) : idxValD (uIdx5 wIdx) δ < 24 := by
  have hsp := idxValD_6_split_bit3 wIdx δ;
  have h32 :=
      idxValPrefix_lt_two_pow (uIdx5 wIdx) δ 5 le_rfl; change idxValD (uIdx5 wIdx) δ <
      2 ^ 5 at h32; omega
theorem uBit3_zero_of_q23 {n : ℕ} {wIdx : Fin 6 → Wire n} {δ : BitAssignment n}
    (hLt : idxValD wIdx δ < 47) (hq23 : idxValD (uIdx5 wIdx) δ = 23) :
    idxValPrefix (uBit3 wIdx) δ 1 le_rfl = 0 ∧ idxValD wIdx δ = 39 := by
  have hsp := idxValD_6_split_bit3 wIdx δ; rw [hq23] at hsp; omega
theorem uBit3_one_of_q0_pos {n : ℕ} {wIdx : Fin 6 → Wire n} {δ : BitAssignment n}
    (hLt : idxValD wIdx δ < 47) (hPos : idxValD wIdx δ ≠ 0) (hq0 : idxValD (uIdx5 wIdx) δ = 0) :
    idxValPrefix (uBit3 wIdx) δ 1 le_rfl = 1 ∧ idxValD wIdx δ = 8 := by
  have hsp := idxValD_6_split_bit3 wIdx δ;
  have hp2 := idxValPrefix_lt_two_pow (uBit3 wIdx) δ 1 le_rfl; rw [hq0] at hsp; omega
theorem wOut48_ne_of_val_ne {n : ℕ} {wOut : Fin 48 → Wire n}
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j) {i j : Fin 48} (h : i.val ≠ j.val) : wOut i ≠
    wOut j :=
  hInj i j (fun e ↦ h (congrArg Fin.val e))

theorem wOut48_val_eq_w5 {n : ℕ} {wOut : Fin 48 → Wire n}
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j) {i j : Fin 48} (h : wOut i = wOut j) :
    i.val = j.val :=
  Decidable.byContradiction fun hne ↦ wOut48_ne_of_val_ne hInj hne h

/-! ## Part 1A: `wrapWRouterLo47` (`88 T` compute, `0 T` MBU uncompute) -/

abbrev w24Lo {n : ℕ} (wOut : Fin 48 → Wire n) (q : Fin 24) : Wire n :=
  wOut ⟨16 * (q.val / 8) + (q.val % 8), by have := q.isLt; omega⟩

abbrev w3x8Lo {n : ℕ} (wOut : Fin 48 → Wire n) : Fin 3 → Fin (2 ^ 3) → Wire n :=
    blockWires (rfl : 3 * 2 ^ 3 = 24) (w24Lo wOut)
abbrev wPairLo {n : ℕ} (wOut : Fin 48 → Wire n) (b : Fin 23) (p : Fin (2 ^ 1)) : Wire n :=
  wOut ⟨16 * (b.val / 8) + 8 * p.val + (b.val % 8), by have := b.isLt; have := p.isLt; omega⟩

theorem wInj_w24Lo {n : ℕ} {wOut : Fin 48 → Wire n} (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠
    wOut j) : ∀ i j : Fin 24, i ≠ j → w24Lo wOut i ≠ w24Lo wOut j :=
  fun i j hne ↦ wOut48_ne_of_val_ne hInj
    (by have := i.isLt; have := j.isLt; have := Fin.val_ne_of_ne hne; dsimp; omega)

theorem wInj_w3x8Lo {n : ℕ} {wOut : Fin 48 → Wire n} (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠
    wOut j) : WInj (w3x8Lo wOut) :=
  wInj_blockWires (rfl : 3 * 2 ^ 3 = 24) (wInj_w24Lo hInj)

theorem wInj_wPairLo {n : ℕ} {wOut : Fin 48 → Wire n} (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠
    wOut j) : WInj (wPairLo wOut) :=
  fun b₁ p₁ b₂ p₂ heq ↦ by
    have hv : 16 * (b₁.val / 8) + 8 * p₁.val + b₁.val % 8 =
        16 * (b₂.val / 8) + 8 * p₂.val + b₂.val % 8 := wOut48_val_eq_w5 hInj heq
    have _ : _ ∧ _ ∧ _ ∧ _ := ⟨b₁.isLt, b₂.isLt, p₁.isLt, p₂.isLt⟩
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

def bStarLo {n : ℕ} (wIdx : Fin 6 → Wire n) (δ : BitAssignment n) : Fin 23 :=
  ⟨if idxValD (uIdx5 wIdx) δ < 23 then idxValD (uIdx5 wIdx) δ else 0, by split_ifs <;> omega⟩

def ValidWRouterInLo47 {n : ℕ} (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (qEnc : Wire n) (δ : BitAssignment n) : Prop :=
    (∀ j : Fin 48, δ (wOut j) = 0) ∧ δ qEnc = 0 ∧ idxValD wIdx δ < 47 ∧
    (δ wHas = 0 → idxValD wIdx δ = 0)
def ValidWRouterCleanLo47 {n : ℕ} (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (δ : BitAssignment n) : Prop :=
    (∀ j : Fin 48, δ (wOut j) = 0) ∧ idxValD wIdx δ < 47 ∧ (δ wHas = 0 → idxValD wIdx δ = 0)
noncomputable instance instDecidableValidWRouterCleanLo47 {n : ℕ} (wHas : Wire n)
    (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) :
    DecidablePred (ValidWRouterCleanLo47 wHas wIdx wOut) :=
  Classical.decPred _

/-- Forward `88-T` (`42 + 46 = 88`, `0 .TOFF`) W-state one-hot loader for `idx < 47`. -/
def wStateComputeLo47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n)
    (wOut : Fin 48 → Wire n) (qEnc : Wire n) : DynamicCircuit Var n :=
  if h : WRouterDisjProp wHas wIdx wOut qEnc then
    let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ h.2.2.1 _ _)
    .seq (.circuit (root3.cRootInit ;;ᶜ wTreePrefix 3 3 (w3x8Lo wOut)
        (wInj_w3x8Lo h.2.2.2.2.1) 3 le_rfl))
      (.seq (wShiftLevels v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut) qEnc
          (wInj_w3x8Lo h.2.2.2.2.1) (fun _ _ ↦ h.2.2.2.2.2 _) (fun _ ↦ h.2.2.2.1 _) 3 le_rfl)
        (.seq (.circuit (Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨0, by omega⟩)
              (wOut48_ne_of_val_ne h.2.2.2.2.1 (by dsimp; omega)) ;;ᶜ
            wTreePrefix 23 1 (wPairLo wOut) (wInj_wPairLo h.2.2.2.2.1) 1 le_rfl))
          (.seq (wShiftLevels v 23 1 (uBit3 wIdx) (wPairLo wOut) qEnc
              (wInj_wPairLo h.2.2.2.2.1) (fun _ _ ↦ h.2.2.2.2.2 _) (fun _ ↦ h.2.2.2.1 _) 1 le_rfl)
            (.circuit (Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨0, by omega⟩)
                (wOut48_ne_of_val_ne h.2.2.2.2.1 (by dsimp; omega)) ;;ᶜ
              wZeroGate wHas (wOut ⟨0, by omega⟩) (h.1 _))))))
  else
    .circuit (seqNat 88 fun _ _ ↦ Circuit.T wHas)

/-- Reverse `0-T` (`0 .TOFF`) MBU uncomputer for `idx < 47`. -/
def wStateUncomputeLo47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n)
    (wOut : Fin 48 → Wire n) : DynamicCircuit Var n :=
  if ho : WRouterOutDisj wHas wIdx wOut then
    let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ ho.2.1 _ _)
    .seq (.circuit (wUnzeroGate wHas (wOut ⟨0, by omega⟩) (ho.1 _) ;;ᶜ
        Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨0, by omega⟩)
          (wOut48_ne_of_val_ne ho.2.2 (by dsimp; omega))))
      (.seq (wUncompTreeDyn v 23 1 (uBit3 wIdx) (wPairLo wOut) (wInj_wPairLo ho.2.2)
          (fun _ _ _ ↦ ho.2.1 _ _) (.circuit .identity) 1 le_rfl)
        (.seq (.circuit (Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨0, by omega⟩)
            (wOut48_ne_of_val_ne ho.2.2 (by dsimp; omega))))
          (wUncompTreeDyn v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut)
            (wInj_w3x8Lo ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _)
            (.circuit root3.cRootUninit) 3 le_rfl)))
  else
    .circuit .identity

theorem count_wStateComputeLo47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (qEnc : Wire n) : (wStateComputeLo47 v wHas wIdx wOut qEnc).count .T = 88 ∧
    (wStateComputeLo47 v wHas wIdx wOut qEnc).count .TOFF = 0 := by
  dsimp only [wStateComputeLo47]
  split_ifs with h
  · let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ h.2.2.1 _ _)
    obtain ⟨ri_t, ri_f⟩ := root3.count_init; obtain ⟨t3, f3⟩ :=
        count_wTreePrefix 3 3 (w3x8Lo wOut) (wInj_w3x8Lo h.2.2.2.2.1) 3 le_rfl
    obtain ⟨s3_t, s3_f⟩ :=
        count_wShiftLevels v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx))
        (w3x8Lo wOut) qEnc (wInj_w3x8Lo h.2.2.2.2.1) (fun _ _ ↦ h.2.2.2.2.2 _)
        (fun _ ↦ h.2.2.2.1 _) 3 le_rfl
    obtain ⟨t23, f23⟩ := count_wTreePrefix 23 1 (wPairLo wOut) (wInj_wPairLo h.2.2.2.2.1) 1 le_rfl
    obtain ⟨s23_t, s23_f⟩ :=
        count_wShiftLevels v 23 1 (uBit3 wIdx) (wPairLo wOut) qEnc (wInj_wPairLo h.2.2.2.2.1)
        (fun _ _ ↦ h.2.2.2.2.2 _) (fun _ ↦ h.2.2.2.1 _) 1 le_rfl
    dsimp only [DynamicCircuit.count]; simp only [Circuit.count_seq]
    rw [ri_t, ri_f, t3, f3, s3_t, s3_f, t23, f23, s23_t, s23_f]
    refine ⟨?_, ?_⟩ <;> simp [wZeroGate, Circuit.count_seq, Circuit.X, Circuit.CNOT]
  · refine ⟨?_, ?_⟩
    · simpa [DynamicCircuit.count] using count_seqNat_T 1 88 _ (fun _ _ ↦ by simp [Circuit.T])
    · exact count_seqNat_TOFF_zero 88 _ (fun _ _ ↦ by simp [Circuit.T])

theorem count_wStateUncomputeLo47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) :
    (wStateUncomputeLo47 v wHas wIdx wOut).count .T = 0 ∧
    (wStateUncomputeLo47 v wHas wIdx wOut).count .TOFF = 0 := by
  dsimp only [wStateUncomputeLo47]
  split_ifs with ho
  · let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ ho.2.1 _ _)
    obtain ⟨ru_t, ru_f⟩ := root3.count_uninit
    obtain ⟨tr23_t, tr23_f⟩ :=
        count_wUncompTreeDyn_opt v 23 1 (uBit3 wIdx) (wPairLo wOut) (wInj_wPairLo ho.2.2)
        (fun _ _ _ ↦ ho.2.1 _ _) (.circuit .identity) 1 le_rfl
    obtain ⟨tr3_t, tr3_f⟩ :=
        count_wUncompTreeDyn_opt v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut)
        (wInj_w3x8Lo ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _) (.circuit root3.cRootUninit) 3 le_rfl
    dsimp only [DynamicCircuit.count]; rw [tr23_t, tr23_f, tr3_t, tr3_f];
    dsimp only [DynamicCircuit.count]; rw [ru_t, ru_f];
    have id_t : (Circuit.identity : Circuit n).count .T = 0 := rfl;
    have id_f : (Circuit.identity : Circuit n).count .TOFF = 0 := rfl
    refine ⟨?_, ?_⟩ <;>
      simp [wUnzeroGate, Circuit.count_seq, Circuit.X, Circuit.CNOT, id_t, id_f]
  · exact ⟨rfl, rfl⟩

section DynWiresLo47Irred
attribute [local irreducible] instDecidableWRouterDisjProp instDecidableWRouterOutDisj
theorem dynWires_wStateComputeLo47 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n) (hHas : S wHas)
    (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j))
    (hQ : S qEnc) : DynWires S (wStateComputeLo47 v wHas wIdx wOut qEnc) := by
  dsimp only [wStateComputeLo47]
  split_ifs with h
  · exact ⟨⟨(wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ h.2.2.1 _ _)).cw_init
        (fun _ ↦ hIdx _) (fun _ ↦ hOut _), cw_wTreePrefix 3 3 _ _ (fun _ _ ↦ hOut _) 3 le_rfl⟩,
      dw_wShiftLevels v 3 3 _ _ qEnc _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _) hQ 3 le_rfl,
      ⟨cw_cnot (hOut _) (hOut _), cw_wTreePrefix 23 1 _ _ (fun _ _ ↦ hOut _) 1 le_rfl⟩,
      dw_wShiftLevels v 23 1 _ _ qEnc _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _) hQ 1 le_rfl,
      ⟨cw_cnot (hOut _) (hOut _), ⟨cw_1 (hOut _), cw_cnot hHas (hOut _)⟩⟩⟩
  · exact cw_seqNat 88 _ fun _ _ ↦ cw_1 hHas

theorem dynWires_wStateUncomputeLo47 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (hHas : S wHas)
    (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j)) :
    DynWires S (wStateUncomputeLo47 v wHas wIdx wOut) := by
  dsimp only [wStateUncomputeLo47]
  split_ifs with ho
  · exact ⟨⟨⟨cw_cnot hHas (hOut _), cw_1 (hOut _)⟩, cw_cnot (hOut _) (hOut _)⟩,
      dw_wUncompTreeDyn_opt v 23 1 _ _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _)
        (rest := .circuit .identity) trivial 1 le_rfl, cw_cnot (hOut _) (hOut _),
      dw_wUncompTreeDyn_opt v 3 3 _ _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _)
        (rest := .circuit _)
        ((wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ ho.2.1 _ _)).cw_uninit
          (fun _ ↦ hIdx _) (fun _ ↦ hOut _)) 3 le_rfl⟩
  · trivial

end DynWiresLo47Irred


def δ_rLo {n : ℕ} (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (δ : BitAssignment n) : BitAssignment n :=
  if idxValD (uIdx5 wIdx) δ < 23 then δ else Function.update δ (wOut ⟨39, by omega⟩) 1

theorem bStarLo_δ_rLo_w5 {n : ℕ} {wIdx : Fin 6 → Wire n} {wOut : Fin 48 → Wire n}
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (δ : BitAssignment n) :
    bStarLo wIdx (δ_rLo wIdx wOut δ) = bStarLo wIdx δ := by
  dsimp only [δ_rLo]
  split_ifs
  · rfl
  · have hEq5 : idxValD (uIdx5 wIdx) _ = idxValD (uIdx5 wIdx) δ := idxValPrefix_congr _
      (Function.update δ (wOut ⟨39, by omega⟩) 1) δ
      (fun _ ↦ Function.update_of_ne (hIdxOut _ _) 1 δ) 5 le_rfl
    exact Fin.ext (by simp only [bStarLo, hEq5])

theorem δ_rLo_wPairLo_w5 {n : ℕ} {wIdx : Fin 6 → Wire n} {wOut : Fin 48 → Wire n}
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j) {δ : BitAssignment n}
    (hOut0 : ∀ j : Fin 48, δ (wOut j) = 0) (b : Fin 23) (p : Fin (2 ^ 1)) :
    δ_rLo wIdx wOut δ (wPairLo wOut b p) = 0 := by
  dsimp only [δ_rLo]
  split_ifs
  · exact hOut0 _
  · have _ : _ ∧ _ := ⟨b.isLt, p.isLt⟩
    exact (Function.update_of_ne (wOut48_ne_of_val_ne hInj
      (show 16 * (b.val / 8) + 8 * p.val + (b.val % 8) ≠ 39 by omega)) 1 δ).trans (hOut0 _)

theorem δ_rLo_qEnc_w5 {n : ℕ} {wIdx : Fin 6 → Wire n} {wOut : Fin 48 → Wire n} {qEnc : Wire n}
    (hOutQ : ∀ j, wOut j ≠ qEnc) {δ : BitAssignment n} (hq0 : δ qEnc = 0) :
    δ_rLo wIdx wOut δ qEnc = 0 := by
  dsimp only [δ_rLo]
  split_ifs
  · exact hq0
  · exact (Function.update_of_ne (hOutQ _).symm 1 δ).trans hq0

theorem subspaceStep_id_47_w5 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (X : Operator (2 ^ n)) : SubspaceStep (Var := Var) X X (.circuit .identity) := by
  simpa only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
    subspaceStep_of_circuit (Var := Var) X (.identity : Circuit n)

theorem wSuperOp_root3_top_ket_w5 {n : ℕ} (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (qEnc : Wire n) (hIdxOut : ∀ d j, wIdx d ≠ wOut j) {δ : BitAssignment n}
    (hOut0 : ∀ j, δ (wOut j) = 0) (hq0 : δ qEnc = 0) (hLt : idxValD wIdx δ < 47) :
    (wSuperOp (wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut)
        (fun _ _ ↦ hIdxOut _ _)).bStarFn
      (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut) qEnc 3 le_rfl).mulVec (ket δ) =
      ket (Function.update δ (w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, uIdx5_lt24_of_lt47 hLt⟩) 1) := by
  let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ hIdxOut _ _)
  let uLo3Hi := uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)
  rw [wSuperOp, mkVecOp_mulVec_ket,
    wSuperVec_top_pub root3.bStarFn uLo3Hi (w3x8Lo wOut) qEnc δ (fun _ _ ↦ hOut0 _) hq0,
    show w3x8Lo wOut (root3.bStarFn δ)
        ⟨idxValPrefix uLo3Hi δ 3 le_rfl, idxValPrefix_lt_two_pow uLo3Hi δ 3 le_rfl⟩ =
      w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, uIdx5_lt24_of_lt47 hLt⟩ from
      congrArg (w24Lo wOut) (Fin.ext (root3.idx_decomp δ (uIdx5_lt24_of_lt47 hLt)))]

theorem subspaceStep_wCompRoot3_47_w5 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (R R_out : Operator (2 ^ n))
    (hSupp : SupportedOn (fun δ ↦ (∀ j, δ (wOut j) = 0) ∧ δ qEnc = 0 ∧ idxValD wIdx δ < 47) R)
    (rest : DynamicCircuit Var n)
    (hRest : SubspaceStep (Var := Var)
      (wSuperOp (wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut)
          (fun _ _ ↦ hd.idx_ne_out _ _)).bStarFn
        (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut) qEnc 3 le_rfl * R)
      R_out rest) :
    SubspaceStep (Var := Var) R R_out
      (.seq (.circuit ((wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut)
            (fun _ _ ↦ hd.idx_ne_out _ _)).cRootInit ;;ᶜ
          wTreePrefix 3 3 (w3x8Lo wOut) (wInj_w3x8Lo hd.out_inj) 3 le_rfl))
        (.seq (wShiftLevels v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut) qEnc
            (wInj_w3x8Lo hd.out_inj) (fun _ _ ↦ hd.out_ne_q _) (fun _ ↦ hd.idx_ne_q _) 3 le_rfl)
          rest)) := by
  let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ hd.idx_ne_out _ _)
  let hw3 := wInj_w3x8Lo hd.out_inj
  let uLo3Hi := uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)
  have h1 : (root3.cRootInit ;;ᶜ wTreePrefix 3 3 (w3x8Lo wOut) hw3 3 le_rfl).eval.1 * R =
      wSuperOp root3.bStarFn uLo3Hi (w3x8Lo wOut) qEnc 0 (Nat.zero_le 3) * R :=
    hSupp _ _ fun δ ⟨hOut0, hq0, hLt⟩ ↦ by
      rw [ket_sr_47, eval_seq_mulVec, root3.init_ket δ (fun _ ↦ hOut0 _) (uIdx5_lt24_of_lt47 hLt),
        wSuperVec_bot_pub root3.bStarFn uLo3Hi (w3x8Lo wOut) hw3 qEnc δ (fun _ _ ↦ hOut0 _) hq0,
        wSuperOp, mkVecOp_mulVec_ket]
  exact (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) R _) h1).seq
    ((subspaceStep_mul_right R (subspaceStep_wShiftLevels v root3.bStarFn uLo3Hi (w3x8Lo wOut)
      qEnc hw3 (fun _ _ ↦ hd.out_ne_q _) (fun _ ↦ hd.idx_ne_q _)
      (fun _ _ _ ↦ hd.idx_ne_out _ _) 3 le_rfl)).seq hRest)

theorem subspaceStep_wUncompRoot3_47_w5 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (ho : WRouterOutDisj wHas wIdx wOut) (Pclean Ptrue : BitAssignment n → Prop)
    [DecidablePred Pclean] [DecidablePred Ptrue] (hTrue : ∀ δ, Ptrue δ)
    (hClean : ∀ δ, Pclean δ → (∀ j, δ (wOut j) = 0) ∧ idxValD wIdx δ < 47)
    (R : Operator (2 ^ n)) (hSupp : SupportedOn Pclean R) :
    SubspaceStep (Var := Var)
      (oneHotOptPreOp Pclean Ptrue
        (wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ ho.2.1 _ _)).bStarFn
        (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut) 3 le_rfl * R) R
      (wUncompTreeDyn v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut)
        (wInj_w3x8Lo ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _)
        (.circuit (wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut)
          (fun _ _ ↦ ho.2.1 _ _)).cRootUninit) 3 le_rfl) := by
  let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) fun _ _ ↦ ho.2.1 _ _
  let uLo3Hi := uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)
  let idOnClean : Operator (2 ^ n) :=
    mkVecOp fun δ ↦ if Pclean δ ∧ ∀ b p, δ (w3x8Lo wOut b p) = 0 then ket δ else 0
  refine subspaceStep_congr_out (subspaceStep_mul_right R
    (subspaceStep_wUncompTreeDyn_opt v Pclean Ptrue root3.bStarFn uLo3Hi (w3x8Lo wOut)
      (wInj_w3x8Lo ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _)
      (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ root3.cRootUninit)
        (matrix_ext_ket fun δ ↦ by
          simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, idOnClean, mkVecOp_mulVec_ket,
            oneHotOptPreVec]
          by_cases hV : Pclean δ ∧ ∀ b p, δ (w3x8Lo wOut b p) = 0
          · rw [ite_eq_left hV, ite_eq_left hV, ite_eq_left (hTrue δ),
              show (⟨idxValPrefix uLo3Hi δ 0 _, _⟩ : Fin (2 ^ 3)) = ⟨0, Nat.two_pow_pos 3⟩ from
                Fin.ext rfl, ← root3.init_ket δ (fun _ ↦ (hClean δ hV.1).1 _)
                (uIdx5_lt24_of_lt47 (hClean δ hV.1).2), root3.uninit_init]
          · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero])) 3 le_rfl))
      ((hSupp idOnClean 1 fun δ hP ↦ by
        rw [ket_sr_47]
        simp only [idOnClean, mkVecOp_mulVec_ket, Matrix.one_mulVec]
        exact ite_eq_left ⟨hP, fun _ _ ↦ (hClean δ hP).1 _⟩).trans (Matrix.one_mul R))

private theorem cMidLo_ket {n : ℕ} {wIdx : Fin 6 → Wire n} {wOut : Fin 48 → Wire n}
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j)
    {δ : BitAssignment n} (hOut0 : ∀ j : Fin 48, δ (wOut j) = 0)
    (hLt : idxValD wIdx δ < 47) :
    (Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨0, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega))).eval.1.mulVec
      (ket (Function.update δ (w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, uIdx5_lt24_of_lt47 hLt⟩) 1)) =
    ket (Function.update (δ_rLo wIdx wOut δ) (wPairLo wOut (bStarLo wIdx δ) ⟨0, by omega⟩) 1) := by
  have hq24 := uIdx5_lt24_of_lt47 hLt
  have hne39_0 := wOut48_ne_of_val_ne hInj (i := ⟨39, by omega⟩) (j := ⟨0, by omega⟩) (by simp)
  by_cases hq23 : idxValD (uIdx5 wIdx) δ < 23
  · rw [ket_CNOT_ctrl_zero hne39_0 ((Function.update_of_ne (wOut48_ne_of_val_ne hInj
        (show 39 ≠ 16 * (idxValD (uIdx5 wIdx) δ / 8) + idxValD (uIdx5 wIdx) δ % 8 by omega))
        1 δ).trans (hOut0 _)), show δ_rLo wIdx wOut δ = δ from ite_eq_left hq23,
      show bStarLo wIdx δ = ⟨idxValD (uIdx5 wIdx) δ, hq23⟩ from Fin.ext (ite_eq_left hq23)]
    rfl
  · have heq23 : idxValD (uIdx5 wIdx) δ = 23 := by omega
    rw [show w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, hq24⟩ = wOut ⟨39, by omega⟩ from
        congrArg wOut (Fin.ext (show 16 * (idxValD (uIdx5 wIdx) δ / 8) +
          idxValD (uIdx5 wIdx) δ % 8 = 39 by omega)),
      show bStarLo wIdx δ = ⟨0, by omega⟩ from Fin.ext (ite_eq_right hq23),
      show wPairLo wOut ⟨0, by omega⟩ ⟨0, by omega⟩ = wOut ⟨0, by omega⟩ from
        congrArg wOut (Fin.ext (by simp)),
      show δ_rLo wIdx wOut δ = _ from ite_eq_right hq23, ket_CNOT, Function.update_self,
      Function.update_of_ne hne39_0.symm, hOut0 _, zero_add]

private theorem cPostLo_ket {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n} {wOut : Fin 48 → Wire n}
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j)
    {δ : BitAssignment n} (hOut0 : ∀ j : Fin 48, δ (wOut j) = 0)
    (hLt : idxValD wIdx δ < 47) (hZero : δ wHas = 0 → idxValD wIdx δ = 0) :
    let δr := δ_rLo wIdx wOut δ
    (Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨0, by omega⟩)
        (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
      wZeroGate wHas (wOut ⟨0, by omega⟩) (hHasOut _)).eval.1.mulVec
      (ket (Function.update δr (wPairLo wOut (bStarLo wIdx δr)
        ⟨idxValPrefix (uBit3 wIdx) δr 1 le_rfl, idxValPrefix_lt_two_pow _ δr 1 le_rfl⟩) 1)) =
    (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1.mulVec (ket δ) := by
  intro δr
  have hLt48 : idxValD wIdx δ < 48 := Nat.lt_trans hLt (by decide)
  let jStar : Fin 48 := ⟨idxValD wIdx δ, hLt48⟩
  have hne39_0 := wOut48_ne_of_val_ne hInj (i := ⟨39, by omega⟩) (j := ⟨0, by omega⟩) (by simp)
  have hPreZero : (Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨0, by omega⟩) hne39_0).eval.1.mulVec
      (ket (Function.update δr (wPairLo wOut (bStarLo wIdx δr)
        ⟨idxValPrefix (uBit3 wIdx) δr 1 le_rfl, idxValPrefix_lt_two_pow _ δr 1 le_rfl⟩) 1)) =
      ket (Function.update δ (wOut jStar) 1) := by
    by_cases hq23 : idxValD (uIdx5 wIdx) δ < 23
    · have hb : bStarLo wIdx δ = ⟨idxValD (uIdx5 wIdx) δ, hq23⟩ := Fin.ext (ite_eq_left hq23)
      rw [show δr = δ from ite_eq_left hq23,
        show wPairLo wOut (bStarLo wIdx δ) ⟨idxValPrefix (uBit3 wIdx) δ 1 le_rfl, _⟩ = wOut jStar
          from (congrArg (wPairLo wOut · _) hb).trans
            (congrArg wOut (Fin.ext (idxValD_6_split_bit3 wIdx δ).symm)),
        ket_CNOT_ctrl_zero hne39_0 ((Function.update_of_ne (wOut48_ne_of_val_ne hInj
          (show 39 ≠ idxValD wIdx δ by
            have := idxValPrefix_lt_two_pow (uBit3 wIdx) δ 1 le_rfl
            have := idxValD_6_split_bit3 wIdx δ
            omega)) 1 δ).trans (hOut0 _))]
    · have := uIdx5_lt24_of_lt47 hLt
      obtain ⟨hb3_0, hIdx39⟩ := uBit3_zero_of_q23 hLt (by omega)
      have hδr : δr = Function.update δ (wOut ⟨39, by omega⟩) 1 := ite_eq_right hq23
      have hb3_r : idxValPrefix (uBit3 wIdx) δr 1 le_rfl = 0 := hδr ▸
        (idxValPrefix_congr _ _ _ (fun _ ↦ Function.update_of_ne (hIdxOut _ _) 1 δ) 1 le_rfl).trans
          hb3_0
      rw [show wPairLo wOut (bStarLo wIdx δr) ⟨idxValPrefix (uBit3 wIdx) δr 1 le_rfl, _⟩ =
          wOut ⟨0, by omega⟩ from
          (congrArg (wPairLo wOut · _) ((bStarLo_δ_rLo_w5 hIdxOut δ).trans
            (Fin.ext (ite_eq_right hq23) : _ = ⟨0, by omega⟩))).trans
          (congrArg wOut (Fin.ext (show 16 * (0 / 8) + 8 *
            idxValPrefix (uBit3 wIdx) δr 1 le_rfl + 0 % 8 = 0 by omega))),
        hδr, ket_CNOT, Function.update_self, Function.update_of_ne hne39_0, Function.update_self,
        CharTwo.add_self_eq_zero, Function.update_idem,
        update_eq_self_of_zero ((Function.update_of_ne hne39_0.symm 1 δ).trans (hOut0 _)),
        show wOut jStar = wOut ⟨39, by omega⟩ from congrArg wOut (Fin.ext hIdx39)]
  rw [eval_seq_mulVec, hPreZero, uOneHotToggle_mulVec_ket, wZeroGate_ket (hHasOut _) (hHasOut _)
    fun h0 ↦ congrArg wOut (Fin.ext (hZero h0 : jStar.val = 0))]
  dsimp only [toggleOneHotBits, jStar]
  rw [dite_eq_left hLt48, hOut0 _, zero_add]

theorem subspaceStep_wCompTail_47_w5 {Var : Type} [Fintype Var] [DecidableEq Var] {R_sz n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (R : Operator (2 ^ n))
    {P : BitAssignment n → Prop} (hSupp : SupportedOn P R)
    (hP : ∀ δ, P δ → (∀ j, δ (wOut j) = 0) ∧ δ qEnc = 0 ∧ idxValD wIdx δ < 47)
    (δr : BitAssignment n → BitAssignment n) (bStar : BitAssignment n → Fin R_sz)
    (uSh : Fin 1 → Wire n) (wPair : Fin R_sz → Fin (2 ^ 1) → Wire n) (hwPair : WInj wPair)
    (hWQ : ∀ b p, wPair b p ≠ qEnc) (huQ : ∀ d, uSh d ≠ qEnc) (huW : ∀ d b p, uSh d ≠ wPair b p)
    (cMid cPost : Circuit n) (hbEq : ∀ δ, bStar (δr δ) = bStar δ)
    (hPair0 : ∀ δ, (∀ j, δ (wOut j) = 0) → ∀ b p, δr δ (wPair b p) = 0)
    (hq0r : ∀ δ, δ qEnc = 0 → δr δ qEnc = 0)
    (hcMid : ∀ δ (_hOut0 : ∀ j, δ (wOut j) = 0) (hLt : idxValD wIdx δ < 47),
      cMid.eval.1.mulVec
        (ket (Function.update δ (w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, uIdx5_lt24_of_lt47 hLt⟩) 1)) =
      ket (Function.update (δr δ) (wPair (bStar δ) ⟨0, by omega⟩) 1))
    (hcPost : ∀ δ, P δ → cPost.eval.1.mulVec
      (ket (Function.update (δr δ) (wPair (bStar (δr δ))
        ⟨idxValPrefix uSh (δr δ) 1 le_rfl, idxValPrefix_lt_two_pow _ (δr δ) 1 le_rfl⟩) 1)) =
      (uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1.mulVec (ket δ)) :
    SubspaceStep (Var := Var) R ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R)
      (.seq (.circuit ((wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut)
            (fun _ _ ↦ hd.idx_ne_out _ _)).cRootInit ;;ᶜ
          wTreePrefix 3 3 (w3x8Lo wOut) (wInj_w3x8Lo hd.out_inj) 3 le_rfl))
        (.seq (wShiftLevels v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut) qEnc
            (wInj_w3x8Lo hd.out_inj) (fun _ _ ↦ hd.out_ne_q _) (fun _ ↦ hd.idx_ne_q _) 3 le_rfl)
          (.seq (.circuit (cMid ;;ᶜ wTreePrefix R_sz 1 wPair hwPair 1 le_rfl))
            (.seq (wShiftLevels v R_sz 1 uSh wPair qEnc hwPair hWQ huQ 1 le_rfl)
              (.circuit cPost))))) := by
  refine subspaceStep_wCompRoot3_47_w5 v wHas wIdx wOut qEnc hd R _
    (fun A B hAB ↦ hSupp A B fun δ hp ↦ hAB δ (hP δ hp)) _ ?_
  let R₁ : Operator (2 ^ n) := mkVecOp (fun δ ↦ ket (δr δ)) * R
  exact (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) (by
    dsimp only [R₁]
    simp only [← Matrix.mul_assoc]
    refine hSupp _ _ fun δ hp ↦ ?_
    obtain ⟨hOut0, hq0, hLt⟩ := hP δ hp
    rw [ket_sr_47, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      wSuperOp_root3_top_ket_w5 wIdx wOut qEnc hd.idx_ne_out hOut0 hq0 hLt, eval_seq_mulVec,
      mkVecOp_mulVec_ket, wSuperOp, mkVecOp_mulVec_ket, hcMid δ hOut0 hLt, ← hbEq δ,
      wSuperVec_bot_pub bStar uSh wPair hwPair qEnc _ (hPair0 δ hOut0) (hq0r δ hq0)])).seq
    ((subspaceStep_mul_right R₁ (subspaceStep_wShiftLevels v bStar uSh wPair qEnc hwPair hWQ huQ
      huW 1 le_rfl)).seq
      (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) (by
        dsimp only [R₁]
        simp only [← Matrix.mul_assoc]
        refine hSupp _ _ fun δ hp ↦ ?_
        obtain ⟨hOut0, hq0, _⟩ := hP δ hp
        rw [ket_sr_47, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket, wSuperOp,
          mkVecOp_mulVec_ket,
          wSuperVec_top_pub bStar uSh wPair qEnc _ (hPair0 δ hOut0) (hq0r δ hq0)]
        exact hcPost δ hp)))

theorem subspaceStep_wUncompTail_47_w5 {Var : Type} [Fintype Var] [DecidableEq Var] {R_sz n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (ho : WRouterOutDisj wHas wIdx wOut) (R : Operator (2 ^ n))
    (Pclean : BitAssignment n → Prop) (hSupp : SupportedOn Pclean R)
    (hClean : ∀ δ, Pclean δ → (∀ j, δ (wOut j) = 0) ∧ idxValD wIdx δ < 47)
    (δr : BitAssignment n → BitAssignment n) (bStar : BitAssignment n → Fin R_sz)
    (uSh : Fin 1 → Wire n) (wPair : Fin R_sz → Fin (2 ^ 1) → Wire n) (hwPair : WInj wPair)
    (huW : ∀ d b p, uSh d ≠ wPair b p) (cMid cPost cUn1 cUn3 : Circuit n)
    (hbEq : ∀ δ, bStar (δr δ) = bStar δ)
    (hPair0 : ∀ δ, (∀ j, δ (wOut j) = 0) → ∀ b p, δr δ (wPair b p) = 0)
    (hcMid : ∀ δ (_hOut0 : ∀ j, δ (wOut j) = 0) (hLt : idxValD wIdx δ < 47),
      cMid.eval.1.mulVec
        (ket (Function.update δ (w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, uIdx5_lt24_of_lt47 hLt⟩) 1)) =
      ket (Function.update (δr δ) (wPair (bStar δ) ⟨0, by omega⟩) 1))
    (hcPost : ∀ δ, Pclean δ → cPost.eval.1.mulVec
      (ket (Function.update (δr δ) (wPair (bStar (δr δ))
        ⟨idxValPrefix uSh (δr δ) 1 le_rfl, idxValPrefix_lt_two_pow _ (δr δ) 1 le_rfl⟩) 1)) =
      (uOneHotToggle wHas wIdx wOut ho.1 ho.2.1).1.mulVec (ket δ))
    (hInv1 : ∀ ψ, cUn1.eval.1.mulVec (cPost.eval.1.mulVec ψ) = ψ)
    (hInv3 : ∀ ψ, cUn3.eval.1.mulVec (cMid.eval.1.mulVec ψ) = ψ) :
    SubspaceStep (Var := Var) ((uOneHotToggle wHas wIdx wOut ho.1 ho.2.1).1 * R) R
      (.seq (.circuit cUn1)
        (.seq (wUncompTreeDyn v R_sz 1 uSh wPair hwPair huW (.circuit .identity) 1 le_rfl)
          (.seq (.circuit cUn3)
            (wUncompTreeDyn v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut)
              (wInj_w3x8Lo ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _)
              (.circuit (wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut)
                (fun _ _ ↦ ho.2.1 _ _)).cRootUninit) 3 le_rfl)))) := by
  classical
  let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) fun _ _ ↦ ho.2.1 _ _
  let uLo3Hi := uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)
  let Ptrue : BitAssignment n → Prop := fun _ ↦ True
  let : DecidablePred Ptrue := fun _ ↦ isTrue trivial
  let M_tail : Operator (2 ^ n) := mkVecOp (fun δ ↦ ket (δr δ)) * R
  exact (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) (by
    dsimp only [M_tail]
    simp only [← Matrix.mul_assoc]
    refine hSupp _ _ fun δ hP ↦ ?_
    rw [ket_sr_47, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket,
      oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec,
      ite_eq_left ⟨trivial, hPair0 δ (hClean δ hP).1⟩, ite_eq_left trivial, ← hcPost δ hP,
      hInv1])).seq
    ((subspaceStep_mul_right M_tail (subspaceStep_wUncompTreeDyn_opt v Ptrue Ptrue bStar uSh
      wPair hwPair huW (subspaceStep_id_47_w5 _) 1 le_rfl)).seq
      ((subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) (by
        dsimp only [M_tail]
        simp only [← Matrix.mul_assoc]
        refine hSupp _ _ fun δ hP ↦ ?_
        obtain ⟨hOut0, hLt⟩ := hClean δ hP
        have hq24 := uIdx5_lt24_of_lt47 hLt
        rw [ket_sr_47, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket,
          oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec,
          ite_eq_left ⟨trivial, hPair0 δ hOut0⟩, ite_eq_left trivial, oneHotOptPreOp,
          mkVecOp_mulVec_ket, oneHotOptPreVec, ite_eq_left ⟨hP, fun _ _ ↦ hOut0 _⟩,
          ite_eq_left trivial, show (⟨idxValPrefix uSh (δr δ) 0 _, _⟩ : Fin (2 ^ 1)) =
            ⟨0, by omega⟩ from Fin.ext rfl, hbEq δ, ← hcMid δ hOut0 hLt, hInv3,
          show w3x8Lo wOut (root3.bStarFn δ) ⟨idxValPrefix uLo3Hi δ 3 le_rfl, _⟩ =
            w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, hq24⟩ from
            congrArg (w24Lo wOut) (Fin.ext (root3.idx_decomp δ hq24))])).seq
        (subspaceStep_wUncompRoot3_47_w5 v wHas wIdx wOut ho Pclean Ptrue (fun _ ↦ trivial)
          hClean R hSupp)))

theorem subspaceStep_wStateComputeLo47 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (R : Operator (2 ^ n))
    (hSupp : SupportedOn (ValidWRouterInLo47 wHas wIdx wOut qEnc) R) :
    SubspaceStep (Var := Var) R ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R)
      (wStateComputeLo47 v wHas wIdx wOut qEnc) := by
  dsimp only [wStateComputeLo47]
  rw [dite_eq_left hd.disjProp]
  refine subspaceStep_wCompTail_47_w5 v wHas wIdx wOut qEnc hd R hSupp
    (fun _ ⟨h1, h2, h3, _⟩ ↦ ⟨h1, h2, h3⟩) (δ_rLo wIdx wOut) (bStarLo wIdx) (uBit3 wIdx)
    (wPairLo wOut) (wInj_wPairLo hd.out_inj) (fun _ _ ↦ hd.out_ne_q _) (fun _ ↦ hd.idx_ne_q _)
    (fun _ _ _ ↦ hd.idx_ne_out _ _) _ _ (bStarLo_δ_rLo_w5 hd.idx_ne_out)
    (fun _ h ↦ δ_rLo_wPairLo_w5 hd.out_inj h) (fun _ h ↦ δ_rLo_qEnc_w5 hd.out_ne_q h)
    (fun _ hOut0 hLt ↦ cMidLo_ket hd.out_inj hOut0 hLt)
    (fun _ ⟨hOut0, _, hLt, hZ⟩ ↦ cPostLo_ket hd.has_ne_out hd.idx_ne_out hd.out_inj hOut0 hLt hZ)

theorem subspaceStep_wStateUncomputeLo47 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (ho : WRouterOutDisj wHas wIdx wOut) (R : Operator (2 ^ n))
    (hSupp : SupportedOn (ValidWRouterCleanLo47 wHas wIdx wOut) R) :
    SubspaceStep (Var := Var) ((uOneHotToggle wHas wIdx wOut ho.1 ho.2.1).1 * R) R
      (wStateUncomputeLo47 v wHas wIdx wOut) := by
  dsimp only [wStateUncomputeLo47]
  rw [dite_eq_left ho]
  let c39 := Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨0, by omega⟩)
    (wOut48_ne_of_val_ne ho.2.2 (by decide))
  exact subspaceStep_wUncompTail_47_w5 v wHas wIdx wOut ho R
    (ValidWRouterCleanLo47 wHas wIdx wOut) hSupp (fun _ h ↦ ⟨h.1, h.2.1⟩) (δ_rLo wIdx wOut)
    (bStarLo wIdx) (uBit3 wIdx) (wPairLo wOut) (wInj_wPairLo ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _)
    c39 (Circuit.seq c39 (wZeroGate wHas (wOut ⟨0, by omega⟩) (ho.1 _)))
    (Circuit.seq (wUnzeroGate wHas (wOut ⟨0, by omega⟩) (ho.1 _)) c39) c39
    (bStarLo_δ_rLo_w5 ho.2.1) (fun _ h ↦ δ_rLo_wPairLo_w5 ho.2.2 h)
    (fun _ hOut0 hLt ↦ cMidLo_ket ho.2.2 hOut0 hLt)
    (fun _ ⟨hOut0, hLt, hZ⟩ ↦ cPostLo_ket ho.1 ho.2.1 ho.2.2 hOut0 hLt hZ)
    (fun _ ↦ by simp only [c39, wUnzeroGate, wZeroGate, eval_seq_mulVec, mulVec_CNOT_invol_47,
      mulVec_X_invol_47])
    fun _ ↦ mulVec_CNOT_invol_47 _ _ _ _

section WrapLo47Irred
attribute [local irreducible] wStateComputeLo47 wStateUncomputeLo47
/-- Bracketed `88-T` W-state one-hot subroutine for `< 47` index domains (`Lo_N`). -/
def wrapWRouterLo47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n)
    (wOut : Fin 48 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
    .seq (wStateComputeLo47 v wHas wIdx wOut qEnc) (.seq mid (wStateUncomputeLo47 v wHas wIdx wOut))
theorem count_wrapWRouterLo47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n)
    (wOut : Fin 48 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n) :
    (wrapWRouterLo47 v wHas wIdx wOut qEnc mid).count .T = 88 + mid.count .T ∧
    (wrapWRouterLo47 v wHas wIdx wOut qEnc mid).count .TOFF = mid.count .TOFF := by
  obtain ⟨tc, fc⟩ := count_wStateComputeLo47 v wHas wIdx wOut qEnc; obtain ⟨tu, fu⟩ :=
      count_wStateUncomputeLo47 v wHas wIdx wOut; dsimp only [wrapWRouterLo47,
      DynamicCircuit.count]; omega
theorem dynWires_wrapWRouterLo47 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n)
    (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n)
    (hHas : S wHas) (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j)) (hQ : S qEnc)
    (hMid : DynWires S mid) : DynWires S (wrapWRouterLo47 v wHas wIdx wOut qEnc mid) :=
    ⟨dynWires_wStateComputeLo47 v wHas wIdx wOut qEnc hHas hIdx hOut hQ, hMid,
    dynWires_wStateUncomputeLo47 v wHas wIdx wOut hHas hIdx hOut⟩
theorem subspaceStep_wrapWRouterLo47 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (mid : DynamicCircuit Var n)
    (R_in R_out : Operator (2 ^ n))
    (hIn : SupportedOn (ValidWRouterInLo47 wHas wIdx wOut qEnc) R_in)
    (hOut : SupportedOn (ValidWRouterCleanLo47 wHas wIdx wOut) R_out)
    (hMid : SubspaceStep (Var := Var)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_in)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_out)
      mid) :
    SubspaceStep (Var := Var) R_in R_out (wrapWRouterLo47 v wHas wIdx wOut qEnc mid) :=
  (subspaceStep_wStateComputeLo47 v wHas wIdx wOut qEnc hd R_in hIn).seq
    (hMid.seq (subspaceStep_wStateUncomputeLo47 v wHas wIdx wOut hd.outDisj R_out hOut))
end WrapLo47Irred

/-! ## Part 1B: `wrapWRouterHi47` (`86 T` compute, `0 T` MBU uncompute) -/

private theorem ket_CNOT_scrub {n : ℕ} {c t : Wire n} (h : c ≠ t) {η : BitAssignment n}
    (hc1 : η c = 1)
    (ht0 : η t = 0) : (Circuit.CNOT c t h).eval.1.mulVec (ket (Function.update η t 1)) = ket η := by
  rw [ket_CNOT, Function.update_self, Function.update_of_ne h, hc1, CharTwo.add_self_eq_zero,
      Function.update_idem, update_eq_self_of_zero ht0]
private theorem ket_CNOT_set {n : ℕ} {c t : Wire n} (h : c ≠ t) {η : BitAssignment n}
    (hc1 : η c = 1) (ht0 : η t = 0) : (Circuit.CNOT c t h).eval.1.mulVec (ket η) =
    ket (Function.update η t 1) := by rw [ket_CNOT, ht0, hc1, zero_add]
private theorem update_comm_47 {n : ℕ} (δ : BitAssignment n) {u v : Wire n} (h : u ≠ v)
    (a b : ZMod 2) : Function.update (Function.update δ u a) v b =
    Function.update (Function.update δ v b) u a := by
  exact Function.update_comm h a b δ

private theorem ket_loadBit47 {n : ℕ} {wHas c t0 : Wire n} (h1 : wHas ≠ t0) (h2 : c ≠ t0)
    {η : BitAssignment n} (ht0 : η t0 = 0) :
    (wZeroGate wHas t0 h1 ;;ᶜ Circuit.CNOT c t0 h2).eval.1.mulVec (ket η) =
      ket (Function.update η t0 (1 + η wHas + η c)) := by
  dsimp only [wZeroGate];
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_X, ket_CNOT, Function.update_self,
      Function.update_of_ne h1, Function.update_idem, ket_CNOT, Function.update_self,
      Function.update_of_ne h2, Function.update_idem, ht0, zero_add]
private theorem ket_unloadBit47 {n : ℕ} {wHas c t0 : Wire n} (h1 : wHas ≠ t0) (h2 : c ≠ t0)
    {η : BitAssignment n} (ht0 : η t0 = 0) :
    (Circuit.CNOT c t0 h2 ;;ᶜ wUnzeroGate wHas t0 h1).eval.1.mulVec
      (ket (Function.update η t0 (1 + η wHas + η c))) = ket η := by
  rw [← ket_loadBit47 h1 h2 ht0];
  simp only [wUnzeroGate, wZeroGate, eval_seq_mulVec, mulVec_CNOT_invol_47, mulVec_X_invol_47]
private theorem uBit3_zmod_eq_zero {n : ℕ} {wIdx : Fin 6 → Wire n} {δ : BitAssignment n}
    (h : idxValPrefix (uBit3 wIdx) δ 1 le_rfl = 0) : δ (wIdx ⟨3, by omega⟩) = 0 := by
  rcases DynCircExt.bit_cases (δ (wIdx ⟨3, by omega⟩)) with h0 | h1 <;>
    simp_all [idxValPrefix, uBit3]

private theorem uBit3_zmod_eq_one {n : ℕ} {wIdx : Fin 6 → Wire n} {δ : BitAssignment n}
    (h : idxValPrefix (uBit3 wIdx) δ 1 le_rfl = 1) : δ (wIdx ⟨3, by omega⟩) = 1 := by
  rcases DynCircExt.bit_cases (δ (wIdx ⟨3, by omega⟩)) with h0 | h1 <;>
    simp_all [idxValPrefix, uBit3]

abbrev wPairHi {n : ℕ} (wOut : Fin 48 → Wire n) (b : Fin 22) (p : Fin (2 ^ 1)) : Wire n :=
  wOut ⟨16 * ((b.val + 1) / 8) + 8 * p.val + ((b.val + 1) % 8),
    by have := b.isLt; have := p.isLt; omega⟩

abbrev uBit47 {n : ℕ} (wOut : Fin 48 → Wire n) (_ : Fin 1) : Wire n :=
  wOut ⟨47, by omega⟩

theorem wInj_wPairHi {n : ℕ} {wOut : Fin 48 → Wire n} (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠
    wOut j) : WInj (wPairHi wOut) :=
  fun b₁ p₁ b₂ p₂ heq ↦ by
    have hv : 16 * ((b₁.val + 1) / 8) + 8 * p₁.val + (b₁.val + 1) % 8 =
        16 * ((b₂.val + 1) / 8) + 8 * p₂.val + (b₂.val + 1) % 8 := wOut48_val_eq_w5 hInj heq
    have _ : _ ∧ _ ∧ _ ∧ _ := ⟨b₁.isLt, b₂.isLt, p₁.isLt, p₂.isLt⟩
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

def bStarHi {n : ℕ} (wIdx : Fin 6 → Wire n) (δ : BitAssignment n) : Fin 22 :=
  ⟨if 1 ≤ idxValD (uIdx5 wIdx) δ ∧ idxValD (uIdx5 wIdx) δ ≤ 22
    then idxValD (uIdx5 wIdx) δ - 1 else 0, by split_ifs <;> omega⟩

def ValidWRouterInHi47 {n : ℕ} (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (qEnc : Wire n) (δ : BitAssignment n) : Prop :=
    (∀ j : Fin 48, δ (wOut j) = 0) ∧ δ qEnc = 0 ∧ idxValD wIdx δ < 47 ∧
    (δ wHas = 0 → idxValD wIdx δ = 0) ∧ (δ wHas = 1 → idxValD wIdx δ ≠ 0)
def ValidWRouterCleanHi47 {n : ℕ} (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (δ : BitAssignment n) : Prop :=
    (∀ j : Fin 48, δ (wOut j) = 0) ∧ idxValD wIdx δ < 47 ∧ (δ wHas = 0 → idxValD wIdx δ = 0) ∧
    (δ wHas = 1 → idxValD wIdx δ ≠ 0)
noncomputable instance instDecidableValidWRouterCleanHi47 {n : ℕ} (wHas : Wire n)
    (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) :
    DecidablePred (ValidWRouterCleanHi47 wHas wIdx wOut) :=
  Classical.decPred _

def cMidHi {n : ℕ} (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j) : Circuit n :=
  (Circuit.CNOT (wOut ⟨0, by omega⟩) (wOut ⟨1, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨1, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega))) ;;ᶜ
  (wZeroGate wHas (wOut ⟨47, by omega⟩) (hHasOut _) ;;ᶜ
    Circuit.CNOT (wIdx ⟨3, by omega⟩) (wOut ⟨47, by omega⟩) (hIdxOut _ _))

def cMidHiInv {n : ℕ} (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j) : Circuit n :=
  (Circuit.CNOT (wIdx ⟨3, by omega⟩) (wOut ⟨47, by omega⟩) (hIdxOut _ _) ;;ᶜ
    wUnzeroGate wHas (wOut ⟨47, by omega⟩) (hHasOut _)) ;;ᶜ
  (Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨1, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    Circuit.CNOT (wOut ⟨0, by omega⟩) (wOut ⟨1, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)))

def cPostHi {n : ℕ} (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j) : Circuit n :=
  (Circuit.CNOT (wIdx ⟨3, by omega⟩) (wOut ⟨47, by omega⟩) (hIdxOut _ _) ;;ᶜ
    wUnzeroGate wHas (wOut ⟨47, by omega⟩) (hHasOut _)) ;;ᶜ
  (Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨1, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    Circuit.CNOT (wOut ⟨0, by omega⟩) (wOut ⟨9, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    Circuit.CNOT (wOut ⟨0, by omega⟩) (wOut ⟨8, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    Circuit.CNOT (wOut ⟨8, by omega⟩) (wOut ⟨0, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    wZeroGate wHas (wOut ⟨8, by omega⟩) (hHasOut _))

def cPostHiInv {n : ℕ} (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j) : Circuit n :=
  (wUnzeroGate wHas (wOut ⟨8, by omega⟩) (hHasOut _) ;;ᶜ
    Circuit.CNOT (wOut ⟨8, by omega⟩) (wOut ⟨0, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    Circuit.CNOT (wOut ⟨0, by omega⟩) (wOut ⟨8, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    Circuit.CNOT (wOut ⟨0, by omega⟩) (wOut ⟨9, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨1, by omega⟩)
      (wOut48_ne_of_val_ne hInj (by dsimp; omega))) ;;ᶜ
  (wZeroGate wHas (wOut ⟨47, by omega⟩) (hHasOut _) ;;ᶜ
    Circuit.CNOT (wIdx ⟨3, by omega⟩) (wOut ⟨47, by omega⟩) (hIdxOut _ _))

/--
Forward `86-T` (`42 + 44 = 86`, `0 .TOFF` ) W-state one-hot loader for `Hi_N` (`0 < idx < 47` when
`wHas = 1` ).
-/
def wStateComputeHi47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n)
    (wOut : Fin 48 → Wire n) (qEnc : Wire n) : DynamicCircuit Var n :=
  if h : WRouterDisjProp wHas wIdx wOut qEnc then
    let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ h.2.2.1 _ _)
    .seq (.circuit (root3.cRootInit ;;ᶜ wTreePrefix 3 3 (w3x8Lo wOut)
        (wInj_w3x8Lo h.2.2.2.2.1) 3 le_rfl))
      (.seq (wShiftLevels v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut) qEnc
          (wInj_w3x8Lo h.2.2.2.2.1) (fun _ _ ↦ h.2.2.2.2.2 _) (fun _ ↦ h.2.2.2.1 _) 3 le_rfl)
        (.seq (.circuit (cMidHi wHas wIdx wOut h.1 h.2.2.1 h.2.2.2.2.1 ;;ᶜ
            wTreePrefix 22 1 (wPairHi wOut) (wInj_wPairHi h.2.2.2.2.1) 1 le_rfl))
          (.seq (wShiftLevels v 22 1 (uBit47 wOut) (wPairHi wOut) qEnc
              (wInj_wPairHi h.2.2.2.2.1) (fun _ _ ↦ h.2.2.2.2.2 _) (fun _ ↦ h.2.2.2.2.2 _) 1 le_rfl)
            (.circuit (cPostHi wHas wIdx wOut h.1 h.2.2.1 h.2.2.2.2.1)))))
  else
    .circuit (seqNat 86 fun _ _ ↦ Circuit.T wHas)

/-- Reverse `0-T` (`0 .TOFF`) MBU uncomputer for `Hi_N`. -/
def wStateUncomputeHi47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n)
    (wOut : Fin 48 → Wire n) : DynamicCircuit Var n :=
  if ho : WRouterOutDisj wHas wIdx wOut then
    let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ ho.2.1 _ _)
    .seq (.circuit (cPostHiInv wHas wIdx wOut ho.1 ho.2.1 ho.2.2))
      (.seq (wUncompTreeDyn v 22 1 (uBit47 wOut) (wPairHi wOut) (wInj_wPairHi ho.2.2)
          (fun _ b p ↦ wOut48_ne_of_val_ne ho.2.2
            (by have := b.isLt; have := p.isLt; dsimp; omega))
          (.circuit .identity) 1 le_rfl)
        (.seq (.circuit (cMidHiInv wHas wIdx wOut ho.1 ho.2.1 ho.2.2))
          (wUncompTreeDyn v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut)
            (wInj_w3x8Lo ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _)
            (.circuit root3.cRootUninit) 3 le_rfl)))
  else
    .circuit .identity

theorem count_wStateComputeHi47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (qEnc : Wire n) : (wStateComputeHi47 v wHas wIdx wOut qEnc).count .T = 86 ∧
    (wStateComputeHi47 v wHas wIdx wOut qEnc).count .TOFF = 0 := by
  dsimp only [wStateComputeHi47]
  split_ifs with h
  · let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ h.2.2.1 _ _)
    obtain ⟨ri_t, ri_f⟩ := root3.count_init; obtain ⟨t3, f3⟩ :=
        count_wTreePrefix 3 3 (w3x8Lo wOut) (wInj_w3x8Lo h.2.2.2.2.1) 3 le_rfl
    obtain ⟨s3_t, s3_f⟩ :=
        count_wShiftLevels v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx))
        (w3x8Lo wOut) qEnc (wInj_w3x8Lo h.2.2.2.2.1) (fun _ _ ↦ h.2.2.2.2.2 _)
        (fun _ ↦ h.2.2.2.1 _) 3 le_rfl
    obtain ⟨t22, f22⟩ := count_wTreePrefix 22 1 (wPairHi wOut) (wInj_wPairHi h.2.2.2.2.1) 1 le_rfl
    obtain ⟨s22_t, s22_f⟩ :=
        count_wShiftLevels v 22 1 (uBit47 wOut) (wPairHi wOut) qEnc (wInj_wPairHi h.2.2.2.2.1)
        (fun _ _ ↦ h.2.2.2.2.2 _) (fun _ ↦ h.2.2.2.2.2 _) 1 le_rfl
    dsimp only [DynamicCircuit.count]; simp only [Circuit.count_seq]
    rw [ri_t, ri_f, t3, f3, s3_t, s3_f, t22, f22, s22_t, s22_f]
    refine ⟨?_, ?_⟩ <;>
      simp [cMidHi, cPostHi, wZeroGate, wUnzeroGate, Circuit.count_seq, Circuit.X, Circuit.CNOT]
  · refine ⟨?_, ?_⟩
    · simpa [DynamicCircuit.count] using count_seqNat_T 1 86 _ (fun _ _ ↦ by simp [Circuit.T])
    · exact count_seqNat_TOFF_zero 86 _ (fun _ _ ↦ by simp [Circuit.T])

theorem count_wStateUncomputeHi47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) :
    (wStateUncomputeHi47 v wHas wIdx wOut).count .T = 0 ∧
    (wStateUncomputeHi47 v wHas wIdx wOut).count .TOFF = 0 := by
  dsimp only [wStateUncomputeHi47]
  split_ifs with ho
  · let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ ho.2.1 _ _)
    obtain ⟨ru_t, ru_f⟩ := root3.count_uninit
    obtain ⟨tr22_t, tr22_f⟩ := count_wUncompTreeDyn_opt v 22 1 (uBit47 wOut) (wPairHi wOut)
      (wInj_wPairHi ho.2.2)
      (fun _ b p ↦ wOut48_ne_of_val_ne ho.2.2 (by have := b.isLt; have := p.isLt; dsimp; omega))
      (.circuit .identity) 1 le_rfl
    obtain ⟨tr3_t, tr3_f⟩ :=
        count_wUncompTreeDyn_opt v 3 3 (uLoOf (Nat.le_add_right 3 2) (uIdx5 wIdx)) (w3x8Lo wOut)
        (wInj_w3x8Lo ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _) (.circuit root3.cRootUninit) 3 le_rfl
    dsimp only [DynamicCircuit.count]; rw [tr22_t, tr22_f, tr3_t, tr3_f];
    dsimp only [DynamicCircuit.count]; rw [ru_t, ru_f];
    have id_t : (Circuit.identity : Circuit n).count .T = 0 := rfl;
    have id_f : (Circuit.identity : Circuit n).count .TOFF = 0 := rfl
    refine ⟨?_, ?_⟩ <;>
      simp [cPostHiInv, cMidHiInv, wZeroGate, wUnzeroGate, Circuit.count_seq, Circuit.X,
          Circuit.CNOT, id_t, id_f]
  · exact ⟨rfl, rfl⟩

section DynWiresHi47Irred
attribute [local irreducible] instDecidableWRouterDisjProp instDecidableWRouterOutDisj
theorem dynWires_wStateComputeHi47 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n) (hHas : S wHas)
    (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j))
    (hQ : S qEnc) : DynWires S (wStateComputeHi47 v wHas wIdx wOut qEnc) := by
  dsimp only [wStateComputeHi47]
  split_ifs with h
  · let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ h.2.2.1 _ _)
    exact ⟨⟨root3.cw_init (fun _ ↦ hIdx _) (fun _ ↦ hOut _),
        cw_wTreePrefix 3 3 _ _ (fun _ _ ↦ hOut _) 3 le_rfl⟩,
      dw_wShiftLevels v 3 3 _ _ qEnc _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _) hQ 3 le_rfl,
      ⟨⟨⟨cw_cnot (hOut _) (hOut _), cw_cnot (hOut _) (hOut _)⟩,
        ⟨⟨cw_1 (hOut _), cw_cnot hHas (hOut _)⟩, cw_cnot (hIdx _) (hOut _)⟩⟩,
        cw_wTreePrefix 22 1 _ _ (fun _ _ ↦ hOut _) 1 le_rfl⟩,
      dw_wShiftLevels v 22 1 _ _ qEnc _ _ _ (fun _ ↦ hOut _) (fun _ _ ↦ hOut _) hQ 1 le_rfl,
      ⟨⟨cw_cnot (hIdx _) (hOut _), ⟨cw_cnot hHas (hOut _), cw_1 (hOut _)⟩⟩,
        ⟨cw_cnot (hOut _) (hOut _), cw_cnot (hOut _) (hOut _), cw_cnot (hOut _) (hOut _),
          cw_cnot (hOut _) (hOut _), ⟨cw_1 (hOut _), cw_cnot hHas (hOut _)⟩⟩⟩⟩
  · exact cw_seqNat 86 _ fun _ _ ↦ cw_1 hHas

theorem dynWires_wStateUncomputeHi47 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (hHas : S wHas)
    (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j)) :
    DynWires S (wStateUncomputeHi47 v wHas wIdx wOut) := by
  dsimp only [wStateUncomputeHi47]
  split_ifs with ho
  · let root3 := wRootSpec3x2k (k := 3) (uIdx5 wIdx) (w24Lo wOut) (fun _ _ ↦ ho.2.1 _ _)
    exact ⟨⟨⟨⟨cw_cnot hHas (hOut _), cw_1 (hOut _)⟩, cw_cnot (hOut _) (hOut _),
          cw_cnot (hOut _) (hOut _), cw_cnot (hOut _) (hOut _), cw_cnot (hOut _) (hOut _)⟩,
        ⟨⟨cw_1 (hOut _), cw_cnot hHas (hOut _)⟩, cw_cnot (hIdx _) (hOut _)⟩⟩,
      dw_wUncompTreeDyn_opt v 22 1 _ _ _ _ (fun _ ↦ hOut _) (fun _ _ ↦ hOut _)
        (rest := .circuit .identity) trivial 1 le_rfl,
      ⟨⟨cw_cnot (hIdx _) (hOut _), ⟨cw_cnot hHas (hOut _), cw_1 (hOut _)⟩⟩,
        ⟨cw_cnot (hOut _) (hOut _), cw_cnot (hOut _) (hOut _)⟩⟩,
      dw_wUncompTreeDyn_opt v 3 3 _ _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _)
        (rest := .circuit root3.cRootUninit)
        (root3.cw_uninit (fun _ ↦ hIdx _) (fun _ ↦ hOut _)) 3 le_rfl⟩
  · trivial

end DynWiresHi47Irred

def δ_rHiBase {n : ℕ} (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (δ : BitAssignment n) : BitAssignment n :=
  if idxValD (uIdx5 wIdx) δ = 0 then Function.update δ (wOut ⟨0, by omega⟩) 1
  else if idxValD (uIdx5 wIdx) δ < 23 then δ
  else Function.update δ (wOut ⟨39, by omega⟩) 1

def δ_rHi {n : ℕ} (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (δ : BitAssignment n) : BitAssignment n :=
  Function.update (δ_rHiBase wIdx wOut δ) (wOut ⟨47, by omega⟩)
    (1 + δ wHas + δ (wIdx ⟨3, by omega⟩))

private theorem bStarHi_update_wOut {n : ℕ} {wIdx : Fin 6 → Wire n} {wOut : Fin 48 → Wire n}
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (δ : BitAssignment n) (j : Fin 48)
    (x : ZMod 2) : bStarHi wIdx (Function.update δ (wOut j) x) = bStarHi wIdx δ := by
  have hEq5 : idxValD (uIdx5 wIdx) (Function.update δ (wOut j) x) = idxValD (uIdx5 wIdx) δ :=
      idxValPrefix_congr _ _ _ (fun _ ↦ Function.update_of_ne (hIdxOut _ j) x δ) 5 le_rfl
  apply Fin.ext; dsimp only [bStarHi]; simp only [hEq5]
private theorem bStarHi_δ_rHi {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {wOut : Fin 48 → Wire n} (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (δ : BitAssignment n) :
    bStarHi wIdx (δ_rHi wHas wIdx wOut δ) = bStarHi wIdx δ := by
  dsimp only [δ_rHi, δ_rHiBase]
  split_ifs <;> simp [bStarHi_update_wOut hIdxOut]

theorem δ_rHiBase_of_ne_w5 {n : ℕ} {wIdx : Fin 6 → Wire n} {wOut : Fin 48 → Wire n}
    (δ : BitAssignment n) {u : Wire n} (h0 : u ≠ wOut ⟨0, by omega⟩)
    (h39 : u ≠ wOut ⟨39, by omega⟩) : δ_rHiBase wIdx wOut δ u = δ u := by
  dsimp only [δ_rHiBase]
  split_ifs <;> first | rfl | exact Function.update_of_ne h0 1 δ |
    exact Function.update_of_ne h39 1 δ

private theorem δ_rHiBase_wHas {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {wOut : Fin 48 → Wire n} (hHasOut : ∀ j, wHas ≠ wOut j) (δ : BitAssignment n) :
    δ_rHiBase wIdx wOut δ wHas = δ wHas := by
  exact δ_rHiBase_of_ne_w5 δ (hHasOut _) (hHasOut _)

private theorem δ_rHiBase_wIdx {n : ℕ} {wIdx : Fin 6 → Wire n}
    {wOut : Fin 48 → Wire n} (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (δ : BitAssignment n) (d : Fin 6) :
    δ_rHiBase wIdx wOut δ (wIdx d) = δ (wIdx d) := by
  exact δ_rHiBase_of_ne_w5 δ (hIdxOut d _) (hIdxOut d _)

private theorem δ_rHiBase_wOut47 {n : ℕ} {wIdx : Fin 6 → Wire n} {wOut : Fin 48 → Wire n}
    (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j)
    {δ : BitAssignment n} (hOut0 : ∀ j : Fin 48, δ (wOut j) = 0) :
    δ_rHiBase wIdx wOut δ (wOut ⟨47, by omega⟩) = 0 := by
  exact (δ_rHiBase_of_ne_w5 δ (wOut48_ne_of_val_ne hInj (by decide))
    (wOut48_ne_of_val_ne hInj (by decide))).trans (hOut0 _)

private theorem δ_rHi_wPairHi {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {wOut : Fin 48 → Wire n} (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j)
    {δ : BitAssignment n} (hOut0 : ∀ j : Fin 48, δ (wOut j) = 0)
    (b : Fin 22) (p : Fin (2 ^ 1)) :
    δ_rHi wHas wIdx wOut δ (wPairHi wOut b p) = 0 := by
  have hne (k : Fin 48) (hk : k.val = 0 ∨ k.val = 39 ∨ k.val = 47) :
      wPairHi wOut b p ≠ wOut k := by
    have _ : _ ∧ _ := ⟨b.isLt, p.isLt⟩
    exact wOut48_ne_of_val_ne hInj
      (show 16 * ((b.val + 1) / 8) + 8 * p.val + ((b.val + 1) % 8) ≠ k.val by omega)
  exact (Function.update_of_ne (hne _ (Or.inr (Or.inr rfl))) _ _).trans
    ((δ_rHiBase_of_ne_w5 δ (hne _ (Or.inl rfl)) (hne _ (Or.inr (Or.inl rfl)))).trans (hOut0 _))

private theorem δ_rHi_qEnc {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {wOut : Fin 48 → Wire n} {qEnc : Wire n} (hOutQ : ∀ j, wOut j ≠ qEnc)
    {δ : BitAssignment n} (hq0 : δ qEnc = 0) :
    δ_rHi wHas wIdx wOut δ qEnc = 0 := by
  exact (Function.update_of_ne (hOutQ _).symm _ _).trans
    ((δ_rHiBase_of_ne_w5 δ (hOutQ _).symm (hOutQ _).symm).trans hq0)

private theorem cMidHi_ket {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {wOut : Fin 48 → Wire n} (hHasOut : ∀ j, wHas ≠ wOut j)
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j)
    {δ : BitAssignment n} (hOut0 : ∀ j : Fin 48, δ (wOut j) = 0)
    (hLt : idxValD wIdx δ < 47) :
    (cMidHi wHas wIdx wOut hHasOut hIdxOut hInj).eval.1.mulVec
      (ket (Function.update δ (w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, uIdx5_lt24_of_lt47 hLt⟩) 1)) =
    ket (Function.update (δ_rHi wHas wIdx wOut δ)
      (wPairHi wOut (bStarHi wIdx δ) ⟨0, by omega⟩) 1) := by
  have hq24 := uIdx5_lt24_of_lt47 hLt
  have hne0_1 := wOut48_ne_of_val_ne hInj (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp)
  have hne39_1 := wOut48_ne_of_val_ne hInj (i := ⟨39, by omega⟩) (j := ⟨1, by omega⟩) (by simp)
  have hUpd0 {i j : Fin 48} (h : j.val ≠ i.val) : Function.update δ (wOut i) 1 (wOut j) = 0 :=
    (Function.update_of_ne (wOut48_ne_of_val_ne hInj h) 1 δ).trans (hOut0 j)
  let wP0 := wPairHi wOut (bStarHi wIdx δ) ⟨0, by omega⟩
  have hwP0_of_nr (hnr : ¬(1 ≤ idxValD (uIdx5 wIdx) δ ∧ idxValD (uIdx5 wIdx) δ ≤ 22)) :
      wP0 = wOut ⟨1, by omega⟩ := congrArg wOut (Fin.ext (by
    dsimp only [wP0, wPairHi, bStarHi]
    rw [ite_eq_right hnr]))
  have hStepA : (Circuit.seq (Circuit.CNOT (wOut ⟨0, by omega⟩) (wOut ⟨1, by omega⟩) hne0_1)
      (Circuit.CNOT (wOut ⟨39, by omega⟩) (wOut ⟨1, by omega⟩) hne39_1)).eval.1.mulVec
      (ket (Function.update δ (w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, hq24⟩) 1)) =
      ket (Function.update (δ_rHiBase wIdx wOut δ) wP0 1) := by
    by_cases hq0 : idxValD (uIdx5 wIdx) δ = 0
    · rw [eval_seq_mulVec, show w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, hq24⟩ = wOut ⟨0, by omega⟩ from
          congrArg wOut (Fin.ext (show 16 * (idxValD (uIdx5 wIdx) δ / 8) +
            idxValD (uIdx5 wIdx) δ % 8 = 0 by omega)),
        ket_CNOT_set hne0_1 (Function.update_self _ _ _) (hUpd0 (by simp)),
        ket_CNOT_ctrl_zero hne39_1 ((Function.update_of_ne hne39_1 1 _).trans (hUpd0 (by simp))),
        show δ_rHiBase wIdx wOut δ = _ from ite_eq_left hq0, hwP0_of_nr (by omega)]
    · by_cases hq23 : idxValD (uIdx5 wIdx) δ < 23
      · have hwEq : w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, hq24⟩ = wP0 := by
          rw [show wP0 = wPairHi wOut ⟨idxValD (uIdx5 wIdx) δ - 1, by omega⟩ ⟨0, by omega⟩ from
            congrArg (wPairHi wOut · ⟨0, by omega⟩) (Fin.ext (ite_eq_left ⟨by omega, by omega⟩))]
          exact congrArg wOut (Fin.ext (show 16 * (idxValD (uIdx5 wIdx) δ / 8) +
            idxValD (uIdx5 wIdx) δ % 8 = 16 * ((idxValD (uIdx5 wIdx) δ - 1 + 1) / 8) + 8 * 0 +
            (idxValD (uIdx5 wIdx) δ - 1 + 1) % 8 by omega))
        rw [eval_seq_mulVec, ket_CNOT_ctrl_zero hne0_1 (hUpd0 (show 0 ≠
              16 * (idxValD (uIdx5 wIdx) δ / 8) + idxValD (uIdx5 wIdx) δ % 8 by omega)),
          ket_CNOT_ctrl_zero hne39_1 (hUpd0 (show 39 ≠
              16 * (idxValD (uIdx5 wIdx) δ / 8) + idxValD (uIdx5 wIdx) δ % 8 by omega)),
          show δ_rHiBase wIdx wOut δ = δ from (ite_eq_right hq0).trans (ite_eq_left hq23)]
        exact congrArg (fun w ↦ ket (Function.update δ w 1)) hwEq
      · have heq23 : idxValD (uIdx5 wIdx) δ = 23 := by omega
        rw [eval_seq_mulVec, show w24Lo wOut ⟨idxValD (uIdx5 wIdx) δ, hq24⟩ =
            wOut ⟨39, by omega⟩ from congrArg wOut (Fin.ext (show
              16 * (idxValD (uIdx5 wIdx) δ / 8) + idxValD (uIdx5 wIdx) δ % 8 = 39 by omega)),
          ket_CNOT_ctrl_zero hne0_1 (hUpd0 (by simp)),
          ket_CNOT_set hne39_1 (Function.update_self _ _ _) (hUpd0 (by simp)),
          show δ_rHiBase wIdx wOut δ = _ from (ite_eq_right hq0).trans (ite_eq_right hq23),
          hwP0_of_nr (by omega)]
  have hneP0_47 : wP0 ≠ wOut ⟨47, by omega⟩ := by
    have := (bStarHi wIdx δ).isLt
    exact wOut48_ne_of_val_ne hInj (show 16 * (((bStarHi wIdx δ).val + 1) / 8) + 8 * 0 +
      ((bStarHi wIdx δ).val + 1) % 8 ≠ 47 by omega)
  dsimp only [cMidHi]
  rw [eval_seq_mulVec, hStepA, ket_loadBit47 (hHasOut _) (hIdxOut _ _)
      ((Function.update_of_ne hneP0_47.symm 1 _).trans (δ_rHiBase_wOut47 hInj hOut0)),
    (Function.update_of_ne (hHasOut _) 1 _).trans (δ_rHiBase_wHas hHasOut δ),
    (Function.update_of_ne (hIdxOut _ _) 1 _).trans (δ_rHiBase_wIdx hIdxOut δ _),
    update_comm_47 _ hneP0_47]
  rfl

private theorem cPostHi_ket {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {wOut : Fin 48 → Wire n} (hHasOut : ∀ j, wHas ≠ wOut j)
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (hInj : ∀ i j : Fin 48, i ≠ j → wOut i ≠ wOut j)
    {δ : BitAssignment n} (hOut0 : ∀ j : Fin 48, δ (wOut j) = 0)
    (hLt : idxValD wIdx δ < 47) (hZero : δ wHas = 0 → idxValD wIdx δ = 0)
    (hOne : δ wHas = 1 → idxValD wIdx δ ≠ 0) :
    let δr := δ_rHi wHas wIdx wOut δ
    (cPostHi wHas wIdx wOut hHasOut hIdxOut hInj).eval.1.mulVec
      (ket (Function.update δr (wPairHi wOut (bStarHi wIdx δr)
        ⟨idxValPrefix (uBit47 wOut) δr 1 le_rfl, idxValPrefix_lt_two_pow _ δr 1 le_rfl⟩) 1)) =
    (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1.mulVec (ket δ) := by
  intro δr
  have hLt48 : idxValD wIdx δ < 48 := Nat.lt_trans hLt (by decide)
  let jStar : Fin 48 := ⟨idxValD wIdx δ, hLt48⟩
  let pStar : Fin (2 ^ 1) :=
    ⟨idxValPrefix (uBit47 wOut) δr 1 le_rfl, idxValPrefix_lt_two_pow _ δr 1 le_rfl⟩
  let wSh := wPairHi wOut (bStarHi wIdx δr) pStar
  have hneSh47 : wSh ≠ wOut ⟨47, by omega⟩ := by
    have := (bStarHi wIdx δr).isLt
    have := pStar.isLt
    exact wOut48_ne_of_val_ne hInj (show 16 * (((bStarHi wIdx δr).val + 1) / 8) + 8 * pStar.val +
      ((bStarHi wIdx δr).val + 1) % 8 ≠ 47 by omega)
  let η := Function.update (δ_rHiBase wIdx wOut δ) wSh 1
  have hUn47 : (Circuit.CNOT (wIdx ⟨3, by omega⟩) (wOut ⟨47, by omega⟩) (hIdxOut _ _) ;;ᶜ
      wUnzeroGate wHas (wOut ⟨47, by omega⟩) (hHasOut _)).eval.1.mulVec
      (ket (Function.update δr wSh 1)) = ket η := by
    rw [show Function.update δr wSh 1 =
        Function.update η (wOut ⟨47, by omega⟩) (1 + η wHas + η (wIdx ⟨3, by omega⟩)) by
          dsimp only [η]
          rw [(Function.update_of_ne (hHasOut _) 1 _).trans (δ_rHiBase_wHas hHasOut δ),
            (Function.update_of_ne (hIdxOut _ _) 1 _).trans (δ_rHiBase_wIdx hIdxOut δ _)]
          exact update_comm_47 _ hneSh47.symm _ _,
      ket_unloadBit47 (hHasOut _) (hIdxOut _ _)
        ((Function.update_of_ne hneSh47.symm 1 _).trans (δ_rHiBase_wOut47 hInj hOut0))]
  dsimp only [cPostHi]
  rw [eval_seq_mulVec, hUn47]
  have hb_r : bStarHi wIdx δr = bStarHi wIdx δ := bStarHi_δ_rHi hIdxOut δ
  have hne39_1 := wOut48_ne_of_val_ne hInj (i := ⟨39, by omega⟩) (j := ⟨1, by omega⟩) (by simp)
  have hne0_9 := wOut48_ne_of_val_ne hInj (i := ⟨0, by omega⟩) (j := ⟨9, by omega⟩) (by simp)
  have hne0_8 := wOut48_ne_of_val_ne hInj (i := ⟨0, by omega⟩) (j := ⟨8, by omega⟩) (by simp)
  have hne8_0 := wOut48_ne_of_val_ne hInj (i := ⟨8, by omega⟩) (j := ⟨0, by omega⟩) (by simp)
  have hUpd0 {i j : Fin 48} (h : j.val ≠ i.val) : Function.update δ (wOut i) 1 (wOut j) = 0 :=
    (Function.update_of_ne (wOut48_ne_of_val_ne hInj h) 1 δ).trans (hOut0 j)
  have hToggle1 (hh1 : δ wHas = 1) :
      (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1.mulVec (ket δ) =
        ket (Function.update δ (wOut jStar) 1) := by
    rw [uOneHotToggle_mulVec_ket]
    dsimp only [toggleOneHotBits, jStar]
    rw [dite_eq_left hLt48, hOut0 _, hh1, zero_add]
  have hTail4 (hh1 : δ wHas = 1) (j : Fin 48) (hj0 : 0 ≠ j.val) (hj8 : 8 ≠ j.val) :
      (Circuit.CNOT (wOut ⟨0, by omega⟩) (wOut ⟨9, by omega⟩) hne0_9 ;;ᶜ
        Circuit.CNOT (wOut ⟨0, by omega⟩) (wOut ⟨8, by omega⟩) hne0_8 ;;ᶜ
        Circuit.CNOT (wOut ⟨8, by omega⟩) (wOut ⟨0, by omega⟩) hne8_0 ;;ᶜ
        wZeroGate wHas (wOut ⟨8, by omega⟩) (hHasOut _)).eval.1.mulVec
        (ket (Function.update δ (wOut j) 1)) = ket (Function.update δ (wOut j) 1) := by
    rw [eval_seq_mulVec, ket_CNOT_ctrl_zero hne0_9 (hUpd0 hj0), eval_seq_mulVec,
      ket_CNOT_ctrl_zero hne0_8 (hUpd0 hj0), eval_seq_mulVec,
      ket_CNOT_ctrl_zero hne8_0 (hUpd0 hj8),
      ket_wZeroGate_of_one (hHasOut _) ((Function.update_of_ne (hHasOut _) 1 δ).trans hh1)]
  have hb0_of_nr (hnr : ¬(1 ≤ idxValD (uIdx5 wIdx) δ ∧ idxValD (uIdx5 wIdx) δ ≤ 22)) :
      bStarHi wIdx δ = ⟨0, by omega⟩ := Fin.ext (ite_eq_right hnr)
  by_cases hq0 : idxValD (uIdx5 wIdx) δ = 0
  · have hb47_1 : 1 + δ wHas + δ (wIdx ⟨3, by omega⟩) = 1 := by
      rcases DynCircExt.bit_cases (δ wHas) with hh0 | hh1
      · have hsp := idxValD_6_split_bit3 wIdx δ
        rw [hZero hh0, hq0] at hsp
        rw [hh0, uBit3_zmod_eq_zero (wIdx := wIdx) (δ := δ) (by omega)]
        rfl
      · rw [hh1, uBit3_zmod_eq_one (uBit3_one_of_q0_pos hLt (hOne hh1) hq0).1]
        rfl
    have hp1 : pStar = ⟨1, by omega⟩ := Fin.ext (by
      dsimp only [pStar, idxValPrefix, uBit47, δr, δ_rHi]
      rw [Function.update_self, hb47_1]
      decide)
    rw [show η = Function.update (Function.update δ (wOut ⟨0, by omega⟩) 1) (wOut ⟨9, by omega⟩) 1
        by dsimp only [η, wSh]
           rw [show δ_rHiBase wIdx wOut δ = _ from ite_eq_left hq0, hb_r, hb0_of_nr (by omega), hp1]
           exact congrArg (Function.update _ · 1) (congrArg wOut (Fin.ext (by simp))),
      eval_seq_mulVec, ket_CNOT_ctrl_zero hne39_1 ((Function.update_of_ne
        (wOut48_ne_of_val_ne hInj (by simp)) 1 _).trans (hUpd0 (by simp))), eval_seq_mulVec,
      ket_CNOT_scrub hne0_9 (Function.update_self _ _ _) (hUpd0 (by simp)), eval_seq_mulVec,
      ket_CNOT_set hne0_8 (Function.update_self _ _ _) (hUpd0 (by simp)),
      update_comm_47 δ hne0_8, eval_seq_mulVec,
      ket_CNOT_scrub hne8_0 (Function.update_self _ _ _) (hUpd0 (by simp))]
    rcases DynCircExt.bit_cases (δ wHas) with hh0 | hh1
    · rw [ket_wZeroGate_of_zero (hHasOut _) ((Function.update_of_ne (hHasOut _) 1 δ).trans hh0),
        Function.update_self, CharTwo.add_self_eq_zero, Function.update_idem,
        update_eq_self_of_zero (hOut0 _), uOneHotToggle_mulVec_ket]
      simp [toggleOneHotBits, dite_eq_left hLt48, hh0, hOut0 _, update_eq_self_of_zero (hOut0 _)]
    · rw [ket_wZeroGate_of_one (hHasOut _) ((Function.update_of_ne (hHasOut _) 1 δ).trans hh1),
        hToggle1 hh1]
      exact congrArg (fun j ↦ ket (Function.update δ (wOut j) 1))
        (Fin.ext (uBit3_one_of_q0_pos hLt (hOne hh1) hq0).2.symm)
  · have hh1 : δ wHas = 1 := (DynCircExt.bit_cases (δ wHas)).elim (fun hh0 ↦ False.elim (by
      have hsp := idxValD_6_split_bit3 wIdx δ
      rw [hZero hh0] at hsp
      omega)) id
    have hpEq : pStar.val = idxValPrefix (uBit3 wIdx) δ 1 le_rfl := by
      simp only [pStar, idxValPrefix, uBit47, uBit3, δr, δ_rHi, Function.update_self, hh1,
        CharTwo.add_self_eq_zero, zero_add]
    have hsp := idxValD_6_split_bit3 wIdx δ
    have hp2 := idxValPrefix_lt_two_pow (uBit3 wIdx) δ 1 le_rfl
    by_cases hq23 : idxValD (uIdx5 wIdx) δ < 23
    · have hwSh : wSh = wOut jStar := by
        dsimp only [wSh]
        rw [hb_r, show bStarHi wIdx δ = ⟨idxValD (uIdx5 wIdx) δ - 1, by omega⟩ from
          Fin.ext (ite_eq_left ⟨by omega, by omega⟩)]
        exact congrArg wOut (Fin.ext (show 16 * ((idxValD (uIdx5 wIdx) δ - 1 + 1) / 8) +
          8 * pStar.val + (idxValD (uIdx5 wIdx) δ - 1 + 1) % 8 = idxValD wIdx δ by omega))
      dsimp only [η, δ_rHiBase]
      rw [congrArg₂ (Function.update · · 1) ((ite_eq_right hq0).trans (ite_eq_left hq23)) hwSh,
        eval_seq_mulVec, ket_CNOT_ctrl_zero hne39_1 (hUpd0 (show 39 ≠ idxValD wIdx δ by omega)),
        hTail4 hh1 jStar (show 0 ≠ idxValD wIdx δ by omega) (show 8 ≠ idxValD wIdx δ by omega),
        hToggle1 hh1]
    · have heq23 : idxValD (uIdx5 wIdx) δ = 23 := by omega
      obtain ⟨hb3_0, hIdx39⟩ := uBit3_zero_of_q23 hLt heq23
      have hwSh : wSh = wOut ⟨1, by omega⟩ := by
        dsimp only [wSh]
        rw [hb_r, hb0_of_nr (by omega)]
        exact congrArg wOut (Fin.ext (show 16 * ((0 + 1) / 8) + 8 * pStar.val +
          (0 + 1) % 8 = 1 by omega))
      dsimp only [η, δ_rHiBase]
      rw [congrArg₂ (Function.update · · 1) ((ite_eq_right hq0).trans (ite_eq_right hq23)) hwSh,
        eval_seq_mulVec,
        ket_CNOT_scrub hne39_1 (Function.update_self _ _ _) (hUpd0 (by simp)),
        hTail4 hh1 ⟨39, by omega⟩ (by simp) (by simp), hToggle1 hh1]
      exact congrArg (fun j ↦ ket (Function.update δ (wOut j) 1))
        (Fin.ext (hIdx39.symm : 39 = jStar.val))

theorem subspaceStep_wStateComputeHi47 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (R : Operator (2 ^ n))
    (hSupp : SupportedOn (ValidWRouterInHi47 wHas wIdx wOut qEnc) R) :
    SubspaceStep (Var := Var) R ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R)
      (wStateComputeHi47 v wHas wIdx wOut qEnc) := by
  dsimp only [wStateComputeHi47]
  rw [dite_eq_left hd.disjProp]
  refine subspaceStep_wCompTail_47_w5 v wHas wIdx wOut qEnc hd R hSupp
    (fun _ ⟨h1, h2, h3, _, _⟩ ↦ ⟨h1, h2, h3⟩) (δ_rHi wHas wIdx wOut) (bStarHi wIdx)
    (uBit47 wOut) (wPairHi wOut) (wInj_wPairHi hd.out_inj) (fun _ _ ↦ hd.out_ne_q _)
    (fun _ ↦ hd.out_ne_q _) (fun _ b p ↦ by
      have _ : _ ∧ _ := ⟨b.isLt, p.isLt⟩
      exact wOut48_ne_of_val_ne hd.out_inj
        (show 47 ≠ 16 * ((b.val + 1) / 8) + 8 * p.val + ((b.val + 1) % 8) by omega))
    (cMidHi wHas wIdx wOut hd.has_ne_out hd.idx_ne_out hd.out_inj)
    (cPostHi wHas wIdx wOut hd.has_ne_out hd.idx_ne_out hd.out_inj)
    (bStarHi_δ_rHi hd.idx_ne_out) (fun _ h ↦ δ_rHi_wPairHi hd.out_inj h)
    (fun _ h ↦ δ_rHi_qEnc hd.out_ne_q h)
    (fun _ hOut0 hLt ↦ cMidHi_ket hd.has_ne_out hd.idx_ne_out hd.out_inj hOut0 hLt)
    (fun _ ⟨hOut0, _, hLt, hZ, hO⟩ ↦
      cPostHi_ket hd.has_ne_out hd.idx_ne_out hd.out_inj hOut0 hLt hZ hO)

theorem subspaceStep_wStateUncomputeHi47 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n)
    (ho : WRouterOutDisj wHas wIdx wOut) (R : Operator (2 ^ n))
    (hSupp : SupportedOn (ValidWRouterCleanHi47 wHas wIdx wOut) R) :
    SubspaceStep (Var := Var) ((uOneHotToggle wHas wIdx wOut ho.1 ho.2.1).1 * R) R
      (wStateUncomputeHi47 v wHas wIdx wOut) := by
  dsimp only [wStateUncomputeHi47]
  rw [dite_eq_left ho]
  refine subspaceStep_wUncompTail_47_w5 v wHas wIdx wOut ho R
    (ValidWRouterCleanHi47 wHas wIdx wOut) hSupp (fun _ h ↦ ⟨h.1, h.2.1⟩) (δ_rHi wHas wIdx wOut)
    (bStarHi wIdx) (uBit47 wOut) (wPairHi wOut) (wInj_wPairHi ho.2.2) (fun _ b p ↦ by
      have _ : _ ∧ _ := ⟨b.isLt, p.isLt⟩
      exact wOut48_ne_of_val_ne ho.2.2
        (show 47 ≠ 16 * ((b.val + 1) / 8) + 8 * p.val + ((b.val + 1) % 8) by omega))
    (cMidHi wHas wIdx wOut ho.1 ho.2.1 ho.2.2) (cPostHi wHas wIdx wOut ho.1 ho.2.1 ho.2.2)
    (cPostHiInv wHas wIdx wOut ho.1 ho.2.1 ho.2.2) (cMidHiInv wHas wIdx wOut ho.1 ho.2.1 ho.2.2)
    (bStarHi_δ_rHi ho.2.1) (fun _ h ↦ δ_rHi_wPairHi ho.2.2 h)
    (fun _ hOut0 hLt ↦ cMidHi_ket ho.1 ho.2.1 ho.2.2 hOut0 hLt)
    (fun _ ⟨hOut0, hLt, hZ, hO⟩ ↦ cPostHi_ket ho.1 ho.2.1 ho.2.2 hOut0 hLt hZ hO)
    (fun _ ↦ by simp only [cPostHiInv, cPostHi, wUnzeroGate, wZeroGate, eval_seq_mulVec,
      mulVec_CNOT_invol_47, mulVec_X_invol_47])
    (fun _ ↦ by simp only [cMidHiInv, cMidHi, wUnzeroGate, wZeroGate, eval_seq_mulVec,
      mulVec_CNOT_invol_47, mulVec_X_invol_47])

section WrapHi47Irred
attribute [local irreducible] wStateComputeHi47 wStateUncomputeHi47
/-- Bracketed `86-T` W-state one-hot subroutine for `Hi_N` (`0 < idx < 47` when `wHas = 1`). -/
def wrapWRouterHi47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n)
    (wOut : Fin 48 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
    .seq (wStateComputeHi47 v wHas wIdx wOut qEnc) (.seq mid (wStateUncomputeHi47 v wHas wIdx wOut))
theorem count_wrapWRouterHi47 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n)
    (wOut : Fin 48 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n) :
    (wrapWRouterHi47 v wHas wIdx wOut qEnc mid).count .T = 86 + mid.count .T ∧
    (wrapWRouterHi47 v wHas wIdx wOut qEnc mid).count .TOFF = mid.count .TOFF := by
  obtain ⟨tc, fc⟩ := count_wStateComputeHi47 v wHas wIdx wOut qEnc; obtain ⟨tu, fu⟩ :=
      count_wStateUncomputeHi47 v wHas wIdx wOut; dsimp only [wrapWRouterHi47,
      DynamicCircuit.count]; omega
theorem dynWires_wrapWRouterHi47 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n)
    (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n)
    (hHas : S wHas) (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j)) (hQ : S qEnc)
    (hMid : DynWires S mid) : DynWires S (wrapWRouterHi47 v wHas wIdx wOut qEnc mid) :=
    ⟨dynWires_wStateComputeHi47 v wHas wIdx wOut qEnc hHas hIdx hOut hQ, hMid,
    dynWires_wStateUncomputeHi47 v wHas wIdx wOut hHas hIdx hOut⟩
theorem subspaceStep_wrapWRouterHi47 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 6 → Wire n) (wOut : Fin 48 → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (mid : DynamicCircuit Var n)
    (R_in R_out : Operator (2 ^ n))
    (hIn : SupportedOn (ValidWRouterInHi47 wHas wIdx wOut qEnc) R_in)
    (hOut : SupportedOn (ValidWRouterCleanHi47 wHas wIdx wOut) R_out)
    (hMid : SubspaceStep (Var := Var)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_in)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_out)
      mid) :
    SubspaceStep (Var := Var) R_in R_out (wrapWRouterHi47 v wHas wIdx wOut qEnc mid) :=
  (subspaceStep_wStateComputeHi47 v wHas wIdx wOut qEnc hd R_in hIn).seq
    (hMid.seq (subspaceStep_wStateUncomputeHi47 v wHas wIdx wOut hd.outDisj R_out hOut))
end WrapHi47Irred
end QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47

section
open scoped Circuit.Notation
open HermitianMat QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
  QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam
open PrimitiveGate PhotochemistrySolution.SplitRouterFredkinMux
  PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.Stage2QromMux
  PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.Stage2ElecFirstZero PhotochemistrySolution.Stage2ZeroGated
  PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ChDiffNoNF
  PhotochemistrySolution.Sub5885 PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.HalfBellCollapse
open PhotochemistrySolution.WStateStage2Load
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 hiding idxValD_congr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
    (ValidZeroGatedSortedRouterInput facts_of_zeroGatedSorted)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47 (ValidWRouterInLo47
    ValidWRouterCleanLo47 ValidWRouterInHi47 ValidWRouterCleanHi47 wStateComputeLo47
    wStateUncomputeLo47 count_wStateComputeLo47 count_wStateUncomputeLo47
    dynWires_wStateComputeLo47)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47
    (dynWires_wStateUncomputeLo47 wrapWRouterLo47 count_wrapWRouterLo47 dynWires_wrapWRouterLo47
    subspaceStep_wrapWRouterLo47 wrapWRouterHi47 count_wrapWRouterHi47 dynWires_wrapWRouterHi47)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47
    (subspaceStep_wrapWRouterHi47)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
    (toggleOneHotBits_apply_other toggleOneHotBits_apply_out uOneHotToggle uOneHotToggle_mulVec_ket
    toggleOneHotBits idxValD_congr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload
    (padWires_zero_of_zero)
attribute [local irreducible] systemQubits_frozen uRouterSwapConj
theorem validWRouterCleanLo47_loN48_inv {n : ℕ} (rn : RouterReg 47 6 n) {u : Wire n}
    (hu : AllPlaneMod rn u) (α : BitAssignment n) (val : ZMod 2)
    (hα : ValidWRouterCleanLo47 (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) α) :
    ValidWRouterCleanLo47 (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) (Function.update α u val) := by
  have hbp : basePub 47 6 = 1238 := rfl
  have neHas : rHas1 rn ≠ u :=
    fun e ↦ not_allPlaneMod_of_idx rn (Or.inl (by dsimp [rHas1]; omega)) (e ▸ hu)
  have neIdx : ∀ d, rIdx1 rn d ≠ u :=
    fun d e ↦ not_allPlaneMod_of_idx rn (Or.inl (by have := d.isLt; dsimp [rIdx1]; omega)) (e ▸ hu)
  have neOut : ∀ j, wOutLoN48 rn j ≠ u := wOutLoN48_mem (S := fun v ↦ v ≠ u) rn
    (fun p e ↦ not_allPlaneMod_of_idx rn (Or.inr (by dsimp [rCtrlLo]; rw [hbp]; omega)) (e ▸ hu))
    (fun e ↦ not_allPlaneMod_of_idx rn (Or.inr (by dsimp; rw [hbp]; omega)) (e ▸ hu))
  have hIdxEq : idxValD (rIdx1 rn) (Function.update α u val) = idxValD (rIdx1 rn) α :=
      idxValD_congr (rIdx1 rn) fun d ↦ Function.update_of_ne (neIdx d) val α
  exact ⟨fun j ↦ (Function.update_of_ne (neOut j) val α).trans (hα.1 j), hIdxEq ▸ hα.2.1, fun h0 ↦
      hIdxEq ▸ hα.2.2 ((Function.update_of_ne neHas val α).symm.trans h0)⟩

theorem validWRouterCleanHi47_hiN48_inv {n : ℕ} (rn : RouterReg 47 6 n) {u : Wire n}
    (hu : AllPlaneMod rn u) (α : BitAssignment n) (val : ZMod 2)
    (hα : ValidWRouterCleanHi47 (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) α) :
    ValidWRouterCleanHi47 (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) (Function.update α u val) := by
  have hbp : basePub 47 6 = 1238 := rfl; have hrw : routerWidth 47 6 = 1394 := rfl
  have neHas : rRawHas2 rn ≠ u :=
    fun e ↦ not_allPlaneMod_of_idx rn (Or.inl (by dsimp [rRawHas2]; rw [hrw]; omega)) (e ▸ hu)
  have neIdx : ∀ d, rIdx2 rn d ≠ u :=
    fun d e ↦ not_allPlaneMod_of_idx rn (Or.inl (by have := d.isLt; dsimp [rIdx2]; omega)) (e ▸ hu)
  have neOut : ∀ j, wOutHiN48 rn j ≠ u := wOutHiN48_mem (S := fun v ↦ v ≠ u) rn
    (fun p e ↦ not_allPlaneMod_of_idx rn (Or.inr (by dsimp [rCtrlHi]; rw [hbp]; omega)) (e ▸ hu))
    (fun e ↦ not_allPlaneMod_of_idx rn (Or.inr (by dsimp; rw [hbp]; omega)) (e ▸ hu))
  have hIdxEq : idxValD (rIdx2 rn) (Function.update α u val) = idxValD (rIdx2 rn) α :=
      idxValD_congr (rIdx2 rn) fun d ↦ Function.update_of_ne (neIdx d) val α
  exact ⟨fun j ↦ (Function.update_of_ne (neOut j) val α).trans (hα.1 j), hIdxEq ▸ hα.2.1, fun h0 ↦
      hIdxEq ▸ hα.2.2.1 ((Function.update_of_ne neHas val α).symm.trans h0), fun h1 ↦
      hIdxEq ▸ hα.2.2.2 ((Function.update_of_ne neHas val α).symm.trans h1)⟩

theorem validWRouterBase_nuc8886 {n : ℕ} (rn : RouterReg 47 6 n) {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput rn β) : ValidWRouterInHi47 (rRawHas2 rn) (rIdx2 rn)
    (wOutHiN48 rn) (qEncNuc rn) β ∧ ValidWRouterCleanHi47 (rRawHas2 rn) (rIdx2 rn)
    (wOutHiN48 rn) β ∧ ValidWRouterInLo47 (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn)
    (qEncNuc rn) β ∧ ValidWRouterCleanLo47 (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) β := by
  have hbp : basePub 47 6 = 1238 := rfl
  have hHi0 : ∀ j, β (wOutHiN48 rn j) = 0 := padWires_zero_of_zero
    (fun p ↦ hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff rn _).mpr (by dsimp [rCtrlHi]; omega)))
    (fun _ ↦
        hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff rn _).mpr (by dsimp [padHiN48]; rw [hbp]; omega)))
  have hLo0 : ∀ j, β (wOutLoN48 rn j) = 0 := padWires_zero_of_zero
    (fun p ↦ hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff rn _).mpr (by dsimp [rCtrlLo]; omega)))
    (fun _ ↦
        hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff rn _).mpr (by dsimp [padLoN48]; rw [hbp]; omega)))
  have hQ0 : β (qEncNuc rn) = 0 :=
    hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff rn _).mpr (by dsimp [qEncNuc]; rw [hbp]; omega))
  obtain ⟨_, ⟨hLt1, hZG1⟩, ⟨hLt2, hZG2, hPos2⟩, _, _⟩ :=
    facts_of_zeroGatedSorted (by omega) rn hβ
  exact ⟨⟨hHi0, hQ0, hLt2, hZG2, hPos2⟩, ⟨hHi0, hLt2, hZG2, hPos2⟩, ⟨hLo0, hQ0, hLt1, hZG1⟩,
      ⟨hLo0, hLt1, hZG1⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam

section
open scoped ComplexOrder MatrixOrder
open QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
  QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47 (ValidWRouterInLo47
    ValidWRouterCleanLo47 wrapWRouterLo47 count_wrapWRouterLo47 dynWires_wrapWRouterLo47
    subspaceStep_wrapWRouterLo47)
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload
open PrimitiveGate PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47 (ValidWRouterInHi47
    ValidWRouterCleanHi47 wrapWRouterHi47 count_wrapWRouterHi47 dynWires_wrapWRouterHi47
    subspaceStep_wrapWRouterHi47)
theorem validWRouterInLo47_padWires {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {c : Fin 47 → Wire n} {pad : Fin (48 - 47) → Wire n} {qEnc : Wire n} {δ : BitAssignment n}
    (hc0 : ∀ p : Fin 47, δ (c p) = 0) (hp0 : ∀ i, δ (pad i) = 0) (hq0 : δ qEnc = 0)
    (hLt : idxValD wIdx δ < 47) (hZG : δ wHas = 0 → idxValD wIdx δ = 0) :
    ValidWRouterInLo47 wHas wIdx (padWires c pad) qEnc δ :=
    ⟨padWires_zero_of_zero hc0 hp0, hq0, hLt, hZG⟩
theorem validWRouterCleanLo47_padWires {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {c : Fin 47 → Wire n} {pad : Fin (48 - 47) → Wire n} {δ : BitAssignment n}
    (hc0 : ∀ p : Fin 47, δ (c p) = 0) (hp0 : ∀ i, δ (pad i) = 0) (hLt : idxValD wIdx δ < 47)
    (hZG : δ wHas = 0 → idxValD wIdx δ = 0) : ValidWRouterCleanLo47 wHas wIdx (padWires c pad) δ :=
    ⟨padWires_zero_of_zero hc0 hp0, hLt, hZG⟩
theorem validWRouterInHi47_padWires {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {c : Fin 47 → Wire n} {pad : Fin (48 - 47) → Wire n} {qEnc : Wire n} {δ : BitAssignment n}
    (hc0 : ∀ p : Fin 47, δ (c p) = 0) (hp0 : ∀ i, δ (pad i) = 0) (hq0 : δ qEnc = 0)
    (hLt : idxValD wIdx δ < 47) (hZG : δ wHas = 0 → idxValD wIdx δ = 0)
    (hPos : δ wHas = 1 → idxValD wIdx δ ≠ 0) :
    ValidWRouterInHi47 wHas wIdx (padWires c pad) qEnc δ :=
    ⟨padWires_zero_of_zero hc0 hp0, hq0, hLt, hZG, hPos⟩
theorem validWRouterCleanHi47_padWires {n : ℕ} {wHas : Wire n} {wIdx : Fin 6 → Wire n}
    {c : Fin 47 → Wire n} {pad : Fin (48 - 47) → Wire n} {δ : BitAssignment n}
    (hc0 : ∀ p : Fin 47, δ (c p) = 0) (hp0 : ∀ i, δ (pad i) = 0) (hLt : idxValD wIdx δ < 47)
    (hZG : δ wHas = 0 → idxValD wIdx δ = 0) (hPos : δ wHas = 1 → idxValD wIdx δ ≠ 0) :
    ValidWRouterCleanHi47 wHas wIdx (padWires c pad) δ :=
    ⟨padWires_zero_of_zero hc0 hp0, hLt, hZG, hPos⟩
end QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload

namespace QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoNuc8886W338
open PhotochemistrySolution.WStateStage5Unload PhotochemistrySolution.WState25PortOpt
  PhotochemistrySolution.Stage2AlwaysLo
open PrimitiveGate hiding cnot h s swap t toffoli x y z
def pUnloadLoNPortOnlyAlways1WState88 {Var : Type} {n : ℕ} (v : Var) (rN : RouterReg 47 6 n)
    (pad : Fin (48 - 47) → Wire n) (qEnc : Wire n) : DynamicCircuit Var n :=
  let hc := hne_unload_core rN
  wrapWRouterLo47 v (rHas1 rN) (rIdx1 rN) (padWires (rCtrlLo rN) pad) qEnc
    (.seq (.circuit (cFlipLo0 zg47_hM0 rN))
      (.seq (bellXHalfVecDyn v 47 24 (rBufLo rN) (rCtrlLo rN)
              (fun k p ↦ pSys (planeOfRouter rN k) p) hc.2.2.2)
            (.circuit (cFlipLo0 zg47_hM0 rN))))

theorem count_pUnloadLoNPortOnlyAlways1WState88 {Var : Type} {n : ℕ} (v : Var)
    (rN : RouterReg 47 6 n) (pad : Fin (48 - 47) → Wire n)
    (qEnc : Wire n) : (pUnloadLoNPortOnlyAlways1WState88 v rN pad qEnc).count .T = 88 ∧
    (pUnloadLoNPortOnlyAlways1WState88 v rN pad qEnc).count .TOFF = 0 := by
  unfold pUnloadLoNPortOnlyAlways1WState88;
  obtain ⟨hT, hF⟩ :=
      count_wrapWRouterLo47 v (rHas1 rN) (rIdx1 rN) (padWires (rCtrlLo rN) pad) qEnc _; rw [hT,
      hF]; simp [DynamicCircuit.count, count_cFlipLo0_T, count_cFlipLo0_TOFF,
      count_bellXHalfVecDyn_t, count_bellXHalfVecDyn_toff]
theorem dynWires_pUnloadLoNPortOnlyAlways1WState88_gen {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rN : RouterReg 47 6 n) (pad : Fin (48 - 47) → Wire n) (qEnc : Wire n)
    (hHas : S (rHas1 rN)) (hIdx : ∀ d : Fin 6, S (rIdx1 rN d))
    (hCtrl : ∀ p : Fin 47, S (rCtrlLo rN p)) (hBuf : ∀ k : Fin 24, S (rBufLo rN k))
    (hSys : ∀ (p : Fin 47) (k : Fin 24), S (rSys rN p k)) (hPad : ∀ i, S (pad i))
    (hQ : S qEnc) : DynWires S (pUnloadLoNPortOnlyAlways1WState88 v rN pad qEnc) :=
  let hFl := cw_cFlipLo0 zg47_hM0 rN hHas (hCtrl ⟨0, zg47_hM0⟩)
  dynWires_wrapWRouterLo47 v _ _ _ _ _
    hHas hIdx (padWires_mem hCtrl hPad) hQ
    ⟨hFl, dynWires_bellXHalfVecDyn_gen v 24 _ _ _ _
      hBuf hCtrl (fun k p ↦ by rw [planeOfRouter_sys]; exact hSys p k), hFl⟩

theorem dynWires_pUnloadLoNPortOnlyAlways1WState88 {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rN : RouterReg 47 6 n) (pad : Fin (48 - 47) → Wire n) (qEnc : Wire n)
    (hrN : ∀ u, UnloadFootprintN rN u → S u) (hPad : ∀ i, S (pad i))
    (hQ : S qEnc) : DynWires S (pUnloadLoNPortOnlyAlways1WState88 v rN pad qEnc) := by
  have pubN : ∀ i : Fin (routerWidth 47 6), i.val < 1238 → S (rN i) :=
    fun i hi ↦ hrN (rN i) ⟨i, rfl, Or.inl hi⟩
  exact dynWires_pUnloadLoNPortOnlyAlways1WState88_gen v rN pad qEnc
    (pubN ⟨0, rw_lt0 47 6⟩ (by dsimp; omega))
    (fun d ↦ pubN ⟨2 + d.val, rw_ltIdx1 d⟩ (by have := d.isLt; dsimp; omega))
    (fun p ↦ hrN _ ⟨⟨basePub 47 6 + 6 + 2 * 6 + p.val, rw_ltCtrlLo p⟩, rfl,
      Or.inr ⟨by dsimp [basePub]; omega, by have := p.isLt; dsimp [basePub]; omega⟩⟩)
    (fun k ↦ pubN ⟨14 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩
      (by have := k.isLt; dsimp; omega))
    (fun p k ↦ pubN ⟨110 + 24 * p.val + k.val,
        by have := p.isLt; have := k.isLt; dsimp [routerWidth]; omega⟩
      (by have := p.isLt; have := k.isLt; dsimp; omega))
    hPad hQ

attribute [local irreducible] systemQubits_frozen
  portSwapVecCirc specFanoutCopyVecCirc specBellEntangleVecCirc
  bellZHalfVecDyn bellXHalfVecDyn

attribute [local semireducible]
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  ComputeProg.fwdBits

theorem subspaceStep_pUnloadLoNPortOnlyAlways1WState88
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rN : RouterReg 47 6 n) (pad : Fin (48 - 47) → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj (rHas1 rN) (rIdx1 rN) (padWires (rCtrlLo rN) pad) qEnc)
    (hPadDisj : ∀ i, (∀ b, pad i ≠ rBufLo rN b) ∧ ∀ p b, pad i ≠ rSys rN p b)
    (hQDisj : (∀ b, qEnc ≠ rBufLo rN b) ∧ ∀ p b, qEnc ≠ rSys rN p b)
    (X : Operator (2 ^ n))
    (hSuppX : SupportedOn (fun δ ↦
      (∀ p : Fin 47, δ (rCtrlLo rN p) = 0) ∧
      (∀ i, δ (pad i) = 0) ∧
      δ qEnc = 0 ∧
      UnloadLoPred rN δ ∧
      (∀ k : Fin 24, δ (rBufLo rN k) = 0)) X) :
    SubspaceStep (Var := Var) (uLoNPortOnlyAlways1Conj rN * X) X
      (pUnloadLoNPortOnlyAlways1WState88 v rN pad qEnc) := by
  let rs := planeOfRouter rN
  let pDec := pDecLoNSorted rN
  let F := (fwdCirc pDec).eval
  let F_fl := (cFlipLo0 zg47_hM0 rN).eval
  let hBC := hne_rBufLo_ctrlLo rN
  have hSuppIn : SupportedOn (fun δ ↦ (∀ p : Fin 47, δ (rCtrlLo rN p) = 0) ∧
      (∀ i, δ (pad i) = 0) ∧ δ qEnc = 0 ∧ UnloadLoPred rN δ) (uLoNPortOnlyAlways1Conj rN * X) :=
    supportedOn_preserves_uLoNPortOnlyAlways1Conj rN
      (fun {u} hu α val ⟨hc0, hp0, hq0, hPLo⟩ ↦ by
        have hrN {k : Fin (routerWidth 47 6)} (hk : k.val < 14 ∨ 1238 ≤ k.val) : rN k ≠ u := by
          rcases hu with ⟨b, rfl⟩ | ⟨p', b, rfl⟩
          · have := b.isLt
            exact rr_ne rN (by dsimp [rBufLo]; omega)
          · have _ : _ ∧ _ := ⟨p'.isLt, b.isLt⟩
            exact rr_ne rN (by dsimp [rSys]; omega)
        have hi1 (d : Fin 6) : Function.update α u val (rIdx1 rN d) = α (rIdx1 rN d) :=
          Function.update_of_ne (hrN (Or.inl (by
            have := d.isLt
            dsimp [rIdx1]; omega))) _ _
        exact ⟨fun p ↦ (Function.update_of_ne (hrN (Or.inr (by
            have := p.isLt
            dsimp [rCtrlLo, basePub]; omega))) _ _).trans (hc0 p),
          fun i ↦ (Function.update_of_ne (hu.elim (fun ⟨b, e⟩ ↦ e ▸ (hPadDisj i).1 b)
            fun ⟨p', b, e⟩ ↦ e ▸ (hPadDisj i).2 p' b) _ _).trans (hp0 i),
          (Function.update_of_ne (hu.elim (fun ⟨b, e⟩ ↦ e ▸ hQDisj.1 b)
            fun ⟨p', b, e⟩ ↦ e ▸ hQDisj.2 p' b) _ _).trans hq0,
          (SplitRouter47_187.idxValD_congr hi1).trans_lt hPLo.1,
          fun hz ↦ (SplitRouter47_187.idxValD_congr hi1).trans
            (hPLo.2 ((Function.update_of_ne (hrN (Or.inl (by decide))) _ _).symm.trans hz))⟩)
      fun A B hAB ↦ hSuppX A B fun δ ⟨hc0, hp0, hq0, hPLo, _⟩ ↦
        hAB δ ⟨hc0, hPLo, hc0, hp0, hq0, hPLo⟩
  have sX := subspaceStep_bellXHalfVec_portSwap v rN (rBufLo rN) (rCtrlLo rN)
    (fun k₁ k₂ hne ↦ rr_ne rN (by
      have _ : _ ∧ _ ∧ _ := ⟨k₁.isLt, k₂.isLt, Fin.val_ne_of_ne hne⟩
      dsimp; omega))
    (fun k ↦ Or.inl (planeOfRouter_bufLo rN k).symm)
    (fun k p hM ↦ by
      rw [← planeOfRouter_ctrlLo rN k] at hM
      rcases hM with e | e | e | e | ⟨_, e⟩ <;> exact pr_ne (rs k) (by dsimp; omega) e)
    hBC (fun k₁ k₂ p ↦ (hne_fixed_router_sys rN k₁ k₂ p).1) (hne_rCtrlLo_pSys rN)
    (F_fl.1 * (F.1 * X)) fun A B hAB ↦ by
      simp only [← Matrix.mul_assoc]
      refine hSuppX (A * F_fl.1 * F.1) (B * F_fl.1 * F.1) fun δ ⟨hc0, _, _, hPLo, hB0⟩ ↦ ?_
      simp only [← Matrix.mulVec_mulVec]
      rw [ket_sr_eq_xm, fwdCirc_ket pDec δ, cFlipLo0_mulVec_ket zg47_hM0 rN, ← ket_sr_eq_xm]
      obtain ⟨_, hOth, hAtMost⟩ := flipLo0Bits_pDecLo_sorted zg47_hM0 (by decide) sorted47_hPow rN
        (fun d p ↦ rr_ne rN (by
          have _ : _ ∧ _ := ⟨d.isLt, p.isLt⟩
          dsimp [basePub]; omega)) δ hc0 hPLo
      exact hAB _ ⟨hAtMost, fun k ↦ (hOth _ (hBC k)).trans (hB0 k)⟩
  have sFl (R : Operator (2 ^ n)) :
      SubspaceStep (Var := Var) (F_fl.1 * R) R (.circuit (cFlipLo0 zg47_hM0 rN)) :=
    subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) (by
      dsimp only [F_fl]
      rw [← Matrix.mul_assoc, cFlipLo0_eval_sq_eq_one zg47_hM0 rN, Matrix.one_mul])
  exact subspaceStep_wrapWRouterLo47 v _ _ _ _ hd _ (uLoNPortOnlyAlways1Conj rN * X) X
    (fun A B hAB ↦ hSuppIn A B fun δ ⟨hc0, hp0, hq0, hLt, hZG⟩ ↦
      hAB δ (validWRouterInLo47_padWires hc0 hp0 hq0 hLt hZG))
    (fun A B hAB ↦ hSuppX A B fun δ ⟨hc0, hp0, _, ⟨hLt, hZG⟩, _⟩ ↦
      hAB δ (validWRouterCleanLo47_padWires hc0 hp0 hLt hZG))
    (subspaceStep_congr_in (by
      rw [uOneHotToggle_eq_fwdCirc_pDecLoN rN pad qEnc hd (uLoNPortOnlyAlways1Conj rN * X)
        fun A B hAB ↦ hSuppIn A B fun δ ⟨hc0, hp0, _, hPLo⟩ ↦ hAB δ ⟨hc0, hp0, hPLo⟩]
      dsimp only [uLoNPortOnlyAlways1Conj, uDecPortOnlyAlways1Conj, F, F_fl, pDec, rs, hBC]
      rw [← Matrix.mul_assoc F.1, ← Matrix.mul_assoc F.1, ← Submonoid.coe_mul, mul_inv_cancel F,
        Submonoid.coe_one, Matrix.one_mul]
      simp only [Matrix.mul_assoc])
      (subspaceStep_congr_out ((sFl _).seq (sX.seq (sFl _)))
        (uOneHotToggle_eq_fwdCirc_pDecLoN rN pad qEnc hd X fun A B hAB ↦
          hSuppX A B fun δ ⟨hc0, hp0, _, hPLo, _⟩ ↦ hAB δ ⟨hc0, hp0, hPLo⟩).symm))

end QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoNuc8886W338
end

namespace QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW325
open PrimitiveGate PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.SortedRouterSpec
  PhotochemistrySolution.PotOraclePortBStream
open PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.WStateRouterPrim
  PhotochemistrySolution.WStateStage5Unload PhotochemistrySolution.WStateWalkSeam
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.AlwaysLoNuc8886W338
open PhotochemistrySolution.Stage2W325AlwaysLo
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.AlwaysLo25860Opt
    (dynWires_wWrapLo187_368)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47
    (dynWires_wrapWRouterHi47)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket)
theorem dynWires_pUnloadLoEAlways1WState_368_noHB7 {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rE : RouterReg 187 8 n) (pad : Fin (192 - 187) → Wire n) (qEnc : Wire n)
    (hrE : ∀ u, Stage5ElecFootprintNoHB7 rE u → S u) (hPad : ∀ i, S (pad i))
    (hQ : S qEnc) : DynWires S (pUnloadLoEAlways1WState_368 v rE pad qEnc) := by
  have pubE97 : ∀ j : Fin (routerWidth 187 8), j.val < 97 → S (rE j) :=
    fun j hj ↦ hrE (rE j) ⟨j, rfl, Or.inl hj⟩
  have sysE : ∀ (q : Fin 187) (k : Fin 24), S (pSys (planeOfRouter rE k) q) := fun q k ↦ by
    rw [planeOfRouter_sys]
    exact hrE _ ⟨⟨114 + 24 * q.val + k.val,
        by have := q.isLt; have := k.isLt; dsimp [routerWidth]; omega⟩,
      rfl, Or.inr (Or.inl ⟨by dsimp; omega, by have := q.isLt; have := k.isLt; dsimp; omega⟩)⟩
  have hCtrlE : ∀ q : Fin 187, S (rCtrlLo rE q) := fun q ↦
    hrE _ ⟨⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩, rfl,
      Or.inr (Or.inr ⟨by dsimp [basePub]; omega, by have := q.isLt; dsimp [basePub]; omega⟩)⟩
  have hBufLoE : ∀ k : Fin 24, S (pBufLo (planeOfRouter rE k)) := fun k ↦
    pubE97 ⟨18 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩
        (by have := k.isLt; dsimp; omega)
  have hHAE : ∀ k : Fin 24, S (pHA (planeOfRouter rE k)) := fun k ↦
    pubE97 ⟨50 + 2 * 8 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩
        (by have := k.isLt; dsimp; omega)
  have hFl := cw_cFlipLo0 zg187_hM0 rE
    (pubE97 ⟨0, rw_lt0 187 8⟩ (by dsimp; omega)) (hCtrlE ⟨0, zg187_hM0⟩)
  exact dynWires_wWrapLo187_368 v _ _ _ _ _
    (pubE97 ⟨0, rw_lt0 187 8⟩ (by dsimp; omega))
    (fun d ↦ pubE97 ⟨2 + d.val, rw_ltIdx1 d⟩ (by have := d.isLt; dsimp; omega))
    (padWires_mem hCtrlE hPad)
    hQ
    ⟨hFl,
     ⟨dynWires_bellZHalfVecDyn_gen v 24 _ _ _ _ _ _ hBufLoE hHAE hCtrlE (fun k q ↦ sysE q k),
      dynWires_bellXHalfVecDyn_gen v 24 _ _ _ _ hBufLoE hCtrlE (fun k q ↦ sysE q k)⟩,
     hFl⟩

attribute [local irreducible] systemQubits_frozen ancWOfScr uLoNPortOnlyAlways1Conj uLoEAlways1Conj
    uSharedHiPortOnlyConj uSwapHi24 uRouterSwapAlwaysLoConj pUnloadLoNPortOnlyAlways1WState88
    pUnloadLoEAlways1WState_368
end QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW325
end

namespace QuantumComputation.Specs.PhotochemistrySolution.CoulombM76Core
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt
    natOfZModBits_testBit_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (itePos iteNeg ditePos
    diteNeg disj_ne disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KpBasis9WRouterOpt (KpBasis9Pkg
    pKpBasis9Unshift30Rev0 subspaceStep_pKpBasis9Unshift30Rev0 kpOfBits kpStep14
    kpStep14_eq_writeReg_code)
open PrimitiveGate (T TOFF)
theorem not_scr0_nn1_of_valid (scr nn : ZMod 2) (hValid : (scr == 1) = false → (nn == 1) = false) :
    ¬(scr = 0 ∧ nn = 1) := by rintro ⟨rfl, rfl⟩; have hf := hValid rfl; contradiction
theorem kpOfBits_eq_kpFn (scr nn : ZMod 2) (kF : Fin 4 → ZMod 2) : kpOfBits scr nn kF =
    natOfZModBits 4 kF + (if (scr == 1) && !(nn == 1) then 1 else 0) := by
  unfold kpOfBits; congr 1
  rcases DynCircExt.bit_cases scr with rfl | rfl <;>
    rcases DynCircExt.bit_cases nn with rfl | rfl <;> decide

attribute [local irreducible] PhotochemistrySolution.FineLegendre.mkKetOpW
end QuantumComputation.Specs.PhotochemistrySolution.CoulombM76Core


namespace QuantumComputation.Specs.PhotochemistrySolution.CoulDomWRouter216
open scoped Circuit.Notation
open PrimitiveGate PhotochemistrySolution.ZeroNEremCsa36Kick
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (ltMask testBit_ltMask
    coordState evalStrict checkColsMask checkColsMask_sound zmod2_eq_ite_of_beq_one natOfZModBits_lt
    natOfZModBits_testBit_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (ditePos diteNeg disj_ne
    disj_of_ne subspaceStep_wrapOnReg_vprog2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18 (pN p2 p3 p4 p5 p6)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (WInj seqNat
    count_seqNat_T count_seqNat_TOFF_zero cw_seqNat seqNat_mulVec_fixed seqNat_mulVec_single
    wUncompTreeDyn mkVecOp mkVecOp_mulVec_ket subspaceStep_mul_right)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket_X ket_CNOT
    eval_seq_mulVec)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
/-! ### 1. `118`-Wire Register `rDom118Lo` (`dom216M = 117`, `kFloor = 90`) -/

abbrev dom216M : ℕ := 117
abbrev dom216OutBase : ℕ := 96

theorem dom216_ge18 : 18 ≤ dom216M := by decide
theorem dom216_lt128 : dom216M < 128 := by decide
theorem dom216_1add_lt (b : Fin 18) : 1 + b.val < dom216M + 1 := by dsimp [dom216M]; omega
theorem dom216Out_lt (j : Fin 22) : dom216OutBase + j.val < dom216M + 1 := by
  dsimp [dom216OutBase, dom216M]; omega
def dom216OutW (j : Fin 22) : Wire (dom216M + 1) := ⟨dom216OutBase + j.val, dom216Out_lt j⟩
theorem bitZMod2_congr {a b : Bool} (h : a = b) : (if a then (1 : ZMod 2) else 0) =
    (if b then 1 else 0) := by
  cases h; rfl

theorem nat_beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.beq_eq.mp hb) h

theorem evalPrimGate_testBit_ge (x c j : ℕ) (hj : 118 ≤ j) : (evalPrimGate 117 x c).testBit j =
    x.testBit j := by
  unfold evalPrimGate
  have hw (s : ℕ) : ((c >>> s) % 512) % 118 ≠ j :=
    ne_of_lt ((Nat.mod_lt _ (by decide)).trans_le hj)
  dsimp only
  split_ifs <;> first | rfl | simp only [testBit_xor_shift1, hw, ↓reduceIte]

theorem evalPrimTree_testBit_ge :
    ∀ (t : PrimTree) (st0 j : ℕ), 118 ≤ j → (evalPrimTree 117 st0 t).testBit j = st0.testBit j
  | .empty, _, _, _ => rfl
  | .leaf c, st0, j, hj => evalPrimGate_testBit_ge st0 c j hj
  | .node tl tr, st0, j, hj =>
      (evalPrimTree_testBit_ge tr (evalPrimTree 117 st0 tl) j hj).trans
        (evalPrimTree_testBit_ge tl st0 j hj)

theorem evalPrimTree_node (st0 : ℕ) (tl tr : PrimTree) :
    evalPrimTree 117 st0 (.node tl tr) = evalPrimTree 117 (evalPrimTree 117 st0 tl) tr := rfl

def stTree118 {n : ℕ} (r : QRegister 118 n) (t : PrimTree) (stX : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : BitAssignment n :=
    writeReg (stX δ) r (fun u ↦ if (evalPrimTree 117 (natOfZModBits 118 (fun i ↦
    stX δ (r i))) t).testBit u.val then 1 else 0)
theorem stTree118_apply_reg {n : ℕ} (r : QRegister 118 n) (t : PrimTree)
    (stX : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
    (u : Wire 118) : stTree118 r t stX δ (r u) = if (evalPrimTree 117 (natOfZModBits 118 (fun i ↦
    stX δ (r i))) t).testBit u.val then 1 else 0
    := by dsimp only [stTree118]; rw [writeReg_apply_reg]
theorem stTree118_eq_zero_of_false {n : ℕ} (r : QRegister 118 n) (t : PrimTree)
    (stX : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (u : Wire 118)
    (hf : (evalPrimTree 117 (natOfZModBits 118 (fun i ↦ stX δ (r i))) t).testBit u.val = false) :
    stTree118 r t stX δ (r u) = 0 := by rw [stTree118_apply_reg, bitZMod2_congr hf]; rfl
theorem stTree118_empty {n : ℕ} (r : QRegister 118 n) (stX : BitAssignment n → BitAssignment n) :
    stTree118 r .empty stX = stX := by
  funext δ; ext x
  by_cases hx : ∃ u, r u = x
  · obtain ⟨u, rfl⟩ := hx; rw [stTree118_apply_reg]
    exact (zmod2_eq_ite_of_beq_one (stX δ (r u)) _ (natOfZModBits_testBit_lt (fun i ↦
        stX δ (r i)) u.isLt).symm).symm
  · dsimp only [stTree118]; exact writeReg_apply_of_not_mem _ _ _ _ hx
theorem itePos {α : Sort*} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by split_ifs; rfl

theorem iteNeg {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by split_ifs; rfl

theorem natOfZModBits_stTree118 {n : ℕ} (r : QRegister 118 n) (t : PrimTree)
    (stX : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : natOfZModBits 118 (fun i ↦
    stTree118 r t stX δ (r i)) = evalPrimTree 117 (natOfZModBits 118 (fun i ↦ stX δ (r i))) t := by
  refine Nat.eq_of_testBit_eq fun k ↦ ?_
  by_cases hk : k < 118
  · rw [natOfZModBits_testBit_lt _ hk, stTree118_apply_reg]
    cases (evalPrimTree 117 _ t).testBit k <;> rfl
  · have hk2 : 2 ^ 118 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hk)
    rw [Nat.testBit_lt_two_pow ((natOfZModBits_lt 118 _).trans_le hk2),
      evalPrimTree_testBit_ge t _ k (by omega),
      Nat.testBit_lt_two_pow ((natOfZModBits_lt 118 _).trans_le hk2)]

theorem stepCB_stTree118 {n : ℕ} (r : QRegister 118 n) (tCur tStep : PrimTree)
    (stX : BitAssignment n → BitAssignment n) :
    (fun δ ↦ stepCB r (decodePrimTree 117 tStep).fwdBits (stTree118 r tCur stX δ)) =
    stTree118 r (.node tCur tStep) stX := by
  funext δ; ext x
  by_cases hx : ∃ u, r u = x
  · obtain ⟨u, rfl⟩ :=
        hx; rw [stepCB_decodePrimTree_apply, natOfZModBits_stTree118, stTree118_apply_reg]; rfl
  · dsimp only [stepCB, stTree118];
    rw [writeReg_apply_of_not_mem _ _ _ _ hx, writeReg_apply_of_not_mem _ _ _ _ hx,
        writeReg_apply_of_not_mem _ _ _ _ hx]
theorem writeReg_comm_disj {a b n : ℕ} (rA : QRegister a n) (rB : QRegister b n)
    (hd : rA.DisjointWires rB) (f : Fin a → ZMod 2) (g : Fin b → ZMod 2) (β : BitAssignment n) :
    writeReg (writeReg β rB g) rA f = writeReg (writeReg β rA f) rB g := by
  ext x
  rcases Classical.em (∃ u, rA u = x) with ⟨u, rfl⟩ | hxA
  · simp [writeReg_apply_reg,
      writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ disj_ne hd u j hj.symm]
  · rcases Classical.em (∃ j, rB j = x) with ⟨j, rfl⟩ | hxB
    · simp [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ hxA]
    · simp [writeReg_apply_of_not_mem _ _ _ _ hxA, writeReg_apply_of_not_mem _ _ _ _ hxB]

theorem stTree118_writeReg_disj {k n : ℕ} (r : QRegister 118 n) (rTgt : QRegister k n)
    (hd : r.DisjointWires rTgt) (t : PrimTree) (st : BitAssignment n → BitAssignment n)
    (g : BitAssignment n → Fin k → ZMod 2) : stTree118 r t (fun δ ↦ writeReg (st δ) rTgt (g δ)) =
    fun δ ↦ writeReg (stTree118 r t st δ) rTgt (g δ) := by
  funext δ
  have hfn : (fun i : Wire 118 ↦ writeReg (st δ) rTgt (g δ) (r i)) = (fun i ↦ st δ (r i)) :=
    funext fun i ↦ writeReg_apply_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ disj_ne hd i j hj.symm)
  dsimp only [stTree118]; rw [hfn]; exact writeReg_comm_disj r rTgt hd _ (g δ) (st δ)
theorem stTree118_eq_on_r_of_disj {k n : ℕ} (r : QRegister 118 n) (rTgt : QRegister k n)
    (hd : r.DisjointWires rTgt) (t : PrimTree) (st : BitAssignment n → BitAssignment n)
    (g : BitAssignment n → Fin k → ZMod 2) (δ : BitAssignment n)
    (u : Wire 118) : stTree118 r t (fun δ' ↦ writeReg (st δ') rTgt (g δ')) δ (r u) =
    stTree118 r t st δ (r u) := by
  rw [stTree118_writeReg_disj r rTgt hd t st g]
  exact writeReg_apply_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ disj_ne hd u j hj.symm)

theorem subspaceStep_treeWrap118 {Var : Type} [Fintype Var] [DecidableEq Var] {W k n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister 118 n) (rTgt : QRegister k n)
    (hDisj : r.DisjointWires rTgt) (sMask nAnd : ℕ) (tCur tStep : PrimTree)
    (hCheck : (checkPrimTree 117 0 sMask tStep).1 = true ∧ (checkPrimTree 117 0 sMask tStep).2.2 =
    nAnd) (st : BitAssignment n → BitAssignment n) (g : BitAssignment n → Fin k → ZMod 2)
    (phPre phPost : BitAssignment n → ZMod 2) (pMid : DynamicCircuit Var n)
    (hCln : ∀ u : Wire 118, sMask.testBit u.val = true → ∀ δ, (∀ q : Fin W, δ (rWork q) = 0) →
    stTree118 r tCur st δ (r u) = 0)
    (hMid : SubspaceStep (mkKetOpW rWork (stTree118 r (.node tCur tStep) st) phPre)
    (mkKetOpW rWork (stTree118 r (.node tCur tStep)
    (fun δ ↦ writeReg (st δ) rTgt (g δ))) phPost) pMid) :
    SubspaceStep (mkKetOpW rWork (stTree118 r tCur st) phPre)
    (mkKetOpW rWork (stTree118 r tCur (fun δ ↦ writeReg (st δ) rTgt (g δ))) phPost)
    (wrapDynOnReg v r (decodePrimTree 117 tStep) pMid) ∧
    (wrapDynOnReg v r (decodePrimTree 117 tStep) pMid).count .T = 4 * nAnd + pMid.count .T ∧
    (wrapDynOnReg v r (decodePrimTree 117 tStep) pMid).count .TOFF = pMid.count .TOFF ∧
    (∀ S : Wire n → Prop, (∀ u, S (r u)) → DynWires S pMid →
    DynWires S (wrapDynOnReg v r (decodePrimTree 117 tStep) pMid)) := by
  let stPost := fun δ ↦ writeReg (st δ) rTgt (g δ)
  rcases decodePrimTree_spec 117 tStep 0 sMask with ⟨hv, _, ha⟩
  have hVpLoc : (decodePrimTree 117 tStep).ValidProg ∅ (maskFinset 118 sMask) :=
      maskFinset_zero 118 ▸ StructuredCB.validProg_of_validProgMask (hv.trans hCheck.1);
      have hAnd : (decodePrimTree 117 tStep).numAnd = nAnd := ha.trans hCheck.2
  have hMid' : SubspaceStep (mkKetOpW rWork (fun δ ↦
      stepCB r (decodePrimTree 117 tStep).fwdBits (stTree118 r tCur st δ)) phPre)
      (mkKetOpW rWork (fun δ ↦
      stepCB r (decodePrimTree 117 tStep).fwdBits (stTree118 r tCur stPost δ)) phPost) pMid
      := by rw [stepCB_stTree118 r tCur tStep st, stepCB_stTree118 r tCur tStep stPost]; exact hMid
  exact subspaceStep_wrapOnReg_vprog2 v rWork r (maskFinset 118 sMask)
      (decodePrimTree 117 tStep) nAnd hVpLoc hAnd (stTree118 r tCur st)
      (stTree118 r tCur stPost) phPre phPost pMid (fun u hu δ hz ↦
      hCln u (mem_maskFinset.mp hu) δ hz)
      (fun u hu δ hz ↦
      (stTree118_eq_on_r_of_disj r rTgt hDisj tCur st g δ u).trans (hCln u (mem_maskFinset.mp hu) δ
      hz)) hMid'

/-! ### 3. Generic `k = 1` Intact-Flag W-Router Bracket (`2 * R + 2` `T`s, `0 .TOFF`) -/

abbrev fp1_0 : Fin (2 ^ 1) := ⟨0, by decide⟩
abbrev qEncIdx118 : Wire 118 := ⟨38, by decide⟩

abbrev rDumIdxR (outBase R : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118) : Wire 118 :=
  ⟨outBase, by omega⟩

abbrev wDumIdxR (outBase R : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118) : Wire 118 :=
  ⟨outBase + 1, by omega⟩

abbrev wIdxR (outBase R : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118) (b : Fin R)
    (p : Fin (2 ^ 1)) : Wire 118 :=
  ⟨outBase + 2 + 2 * b.val + p.val, by
    have := b.isLt; have hp := p.isLt; change p.val < 2 at hp; omega⟩

theorem wOptInj_onReg118 {R n : ℕ} (r : QRegister 118 n) (uIdx : Wire 118) (outBase : ℕ)
    (hOut : outBase + 2 + 2 * R ≤ 118) (hBnd : 38 < outBase ∧ uIdx.val < outBase ∧ uIdx.val ≠ 38) :
    WOptInj R 1 (fun _ : Fin 1 ↦ r uIdx) (fun b p ↦ r (wIdxR outBase R hOut b p))
      (r (rDumIdxR outBase R hOut)) (r (wDumIdxR outBase R hOut)) (r qEncIdx118) := by
  have rn : ∀ {a b : Wire 118}, a.val ≠ b.val → r a ≠ r b :=
    fun h e ↦ h (congrArg Fin.val (r.wires.injective e))
  refine ⟨fun b1 p1 b2 p2 h ↦ ?_, fun _ _ _ ↦ rn ?_, fun _ ↦ rn ?_, fun _ ↦ rn ?_,
    fun _ ↦ rn ?_, fun _ _ ↦ rn ?_, fun _ _ ↦ rn ?_, fun _ _ ↦ rn ?_, rn ?_, rn ?_, rn ?_⟩
  · have hv := congrArg Fin.val (r.wires.injective h)
    have ⟨hp1, hp2⟩ : p1.val < 2 ∧ p2.val < 2 := ⟨p1.isLt, p2.isLt⟩
    dsimp only [wIdxR] at hv
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  all_goals (dsimp [wIdxR, rDumIdxR, wDumIdxR, qEncIdx118]; omega)

theorem flag_ne_rDum {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    (outBase : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118)
    (hf : ∀ b : Fin R, (fIdx b).val < outBase) (b : Fin R) :
    r (fIdx b) ≠ r (rDumIdxR outBase R hOut) := fun h ↦ by
  have hv := congrArg Fin.val (r.wires.injective h)
  have := hf b
  dsimp [rDumIdxR] at hv; omega

theorem flag_ne_wIdx {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    (outBase : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118)
    (hf : ∀ b : Fin R, (fIdx b).val < outBase) (b1 b2 : Fin R) (p : Fin (2 ^ 1)) :
    r (fIdx b1) ≠ r (wIdxR outBase R hOut b2 p) := fun h ↦ by
  have hv := congrArg Fin.val (r.wires.injective h)
  have := hf b1
  dsimp [wIdxR] at hv; omega

def cXorFlagsToDum {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118) (outBase : ℕ)
    (hOut : outBase + 2 + 2 * R ≤ 118) (hf : ∀ b : Fin R, (fIdx b).val < outBase) : Circuit n :=
    seqNat R fun i hi ↦
    Circuit.CNOT (r (fIdx ⟨i, hi⟩)) (r (rDumIdxR outBase R hOut))
    (flag_ne_rDum r fIdx outBase hOut hf ⟨i, hi⟩)
def cXorFlagsToLo {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118) (outBase : ℕ)
    (hOut : outBase + 2 + 2 * R ≤ 118) (hf : ∀ b : Fin R, (fIdx b).val < outBase) : Circuit n :=
    seqNat R fun i hi ↦
    Circuit.CNOT (r (fIdx ⟨i, hi⟩)) (r (wIdxR outBase R hOut ⟨i, hi⟩ fp1_0))
    (flag_ne_wIdx r fIdx outBase hOut hf ⟨i, hi⟩ ⟨i, hi⟩ fp1_0)
def pWIntactBracket {Var : Type} {R n : ℕ} (v : Var) (r : QRegister 118 n) (uIdx : Wire 118)
    (fIdx : Fin R → Wire 118) (outBase : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118)
    (hBnd : 38 < outBase ∧ uIdx.val < outBase ∧ uIdx.val ≠ 38)
    (hf : ∀ b : Fin R, (fIdx b).val < outBase) (mid : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  let hInj := wOptInj_onReg118 r uIdx outBase hOut hBnd
  let uLo1 : Fin 1 → Wire n := fun _ ↦ r uIdx
  let wP := fun b p ↦ r (wIdxR outBase R hOut b p)
  let rDum := r (rDumIdxR outBase R hOut)
  let wDum := r (wDumIdxR outBase R hOut)
  let qEnc := r qEncIdx118
  let cInit := Circuit.X rDum ;;ᶜ cXorFlagsToDum r fIdx outBase hOut hf ;;ᶜ
    cXorFlagsToLo r fIdx outBase hOut hf
  let cClearDum := cXorFlagsToDum r fIdx outBase hOut hf ;;ᶜ Circuit.X rDum
  .seq (.circuit cInit)
    (.seq (wLastSplitShiftDyn v R 0 uLo1 wP rDum wDum qEnc hInj)
      (.seq (.circuit cClearDum)
        (.seq mid
          (.seq (wUncompTreeDyn v R 1 uLo1 wP hInj.w_inj hInj.uLo_ne_w (.circuit .identity) 1
              le_rfl)
            (.circuit (cXorFlagsToLo r fIdx outBase hOut hf))))))

theorem counts_dw_pWIntactBracket {Var : Type} {R n : ℕ} (v : Var) (r : QRegister 118 n)
    (uIdx : Wire 118) (fIdx : Fin R → Wire 118) (outBase : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118)
    (hBnd : 38 < outBase ∧ uIdx.val < outBase ∧ uIdx.val ≠ 38)
    (hf : ∀ b : Fin R, (fIdx b).val < outBase) (mid : DynamicCircuit Var n) :
    (pWIntactBracket v r uIdx fIdx outBase hOut hBnd hf mid).count .T = (2 * R + 2) + mid.count .T ∧
    (pWIntactBracket v r uIdx fIdx outBase hOut hBnd hf mid).count .TOFF = mid.count .TOFF ∧
    (∀ S : Wire n → Prop, (∀ u, S (r u)) → DynWires S mid →
    DynWires S (pWIntactBracket v r uIdx fIdx outBase hOut hBnd hf mid)) := by
  let hInj := wOptInj_onReg118 r uIdx outBase hOut hBnd
  obtain ⟨tS, fS⟩ := count_wLastSplitShiftDyn v R 0 (fun _ ↦ r uIdx)
    (fun b p ↦ r (wIdxR outBase R hOut b p)) (r (rDumIdxR outBase R hOut))
    (r (wDumIdxR outBase R hOut)) (r qEncIdx118) hInj
  obtain ⟨tU, fU⟩ := count_wUncompTreeDyn_opt v R 1 (fun _ ↦ r uIdx)
    (fun b p ↦ r (wIdxR outBase R hOut b p)) hInj.w_inj hInj.uLo_ne_w (.circuit .identity) 1 le_rfl
  obtain ⟨hDT, hDF⟩ : (cXorFlagsToDum r fIdx outBase hOut hf).count .T = 0 ∧
      (cXorFlagsToDum r fIdx outBase hOut hf).count .TOFF = 0 :=
    ⟨(count_seqNat_T 0 R _ fun _ _ ↦ by simp [Circuit.CNOT]).trans (Nat.mul_zero _),
     count_seqNat_TOFF_zero R _ fun _ _ ↦ by simp [Circuit.CNOT]⟩
  obtain ⟨hLT, hLF⟩ : (cXorFlagsToLo r fIdx outBase hOut hf).count .T = 0 ∧
      (cXorFlagsToLo r fIdx outBase hOut hf).count .TOFF = 0 :=
    ⟨(count_seqNat_T 0 R _ fun _ _ ↦ by simp [Circuit.CNOT]).trans (Nat.mul_zero _),
     count_seqNat_TOFF_zero R _ fun _ _ ↦ by simp [Circuit.CNOT]⟩
  dsimp only [pWIntactBracket, DynamicCircuit.count] at tU fU ⊢
  refine ⟨?_, ?_, fun S hrS hMidS ↦
    ⟨⟨cw_1 (hrS _), cw_seqNat R _ fun _ _ ↦ cw_cnot (hrS _) (hrS _),
        cw_seqNat R _ fun _ _ ↦ cw_cnot (hrS _) (hrS _)⟩,
      dw_wLastSplitShiftDyn v R 0 _ _ _ _ _ hInj (fun _ ↦ hrS _) (fun _ _ ↦ hrS _)
        (hrS _) (hrS _) (hrS _), ⟨cw_seqNat R _ fun _ _ ↦ cw_cnot (hrS _) (hrS _), cw_1 (hrS _)⟩,
      hMidS, dw_wUncompTreeDyn_opt v R 1 _ _ hInj.w_inj hInj.uLo_ne_w (fun _ ↦ hrS _)
        (fun _ _ ↦ hrS _) (rest := .circuit .identity) trivial 1 le_rfl,
      cw_seqNat R _ fun _ _ ↦ cw_cnot (hrS _) (hrS _)⟩⟩
  · rw [tS, tU]
    simp [Circuit.count, hDT, hLT]
  · rw [fS, fU]
    simp [Circuit.count, hDF, hLF]

def pTrue118 {n : ℕ} (_ : BitAssignment n) : Prop := True
instance instDecPTrue118 {n : ℕ} : DecidablePred (@pTrue118 n) := fun _ ↦ isTrue trivial

def activeFlags {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118) (γ : BitAssignment n) :
    Prop := ∃ b : Fin R, γ (r (fIdx b)) = 1
instance instDecActiveFlags {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118) :
    DecidablePred (activeFlags r fIdx) := fun γ ↦ by
  unfold activeFlags; infer_instance

def pDumMatch {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118) (rDum : Wire n)
    (γ : BitAssignment n) : Prop := γ rDum = if activeFlags r fIdx γ then 0 else 1
instance instDecPDumMatch {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    (rDum : Wire n) : DecidablePred (pDumMatch r fIdx rDum) := fun γ ↦ by
  unfold pDumMatch; infer_instance

noncomputable def bStarFlags {R n : ℕ} (hR : 0 < R) (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    (γ : BitAssignment n) : Fin R :=
    if h : activeFlags r fIdx γ then Classical.choose h else ⟨0, hR⟩
theorem bStarFlags_spec {R n : ℕ} (hR : 0 < R) (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    {γ : BitAssignment n} (h : activeFlags r fIdx γ) : γ (r (fIdx (bStarFlags hR r fIdx γ))) =
    1 := by
  have hb : bStarFlags hR r fIdx γ = Classical.choose h := by unfold bStarFlags; exact ditePos h
  rw [hb]; exact Classical.choose_spec h

theorem bStarFlags_eq_of_one {R n : ℕ} (hR : 0 < R) (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    {γ : BitAssignment n} (hMut : ∀ b1 b2 : Fin R, b1 ≠ b2 → γ (r (fIdx b1)) = 1 → γ (r (fIdx b2)) =
    0) {b : Fin R} (hb : γ (r (fIdx b)) = 1) : bStarFlags hR r fIdx γ = b := by
  have hAct : activeFlags r fIdx γ := ⟨b, hb⟩; have hs := bStarFlags_spec hR r fIdx hAct
  by_contra hne
  have h0 := hMut b (bStarFlags hR r fIdx γ) (Ne.symm hne) hb
  rw [h0] at hs; exact zero_ne_one hs

theorem bStarFlags_congr {R n : ℕ} (hR : 0 < R) (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    {γ1 γ2 : BitAssignment n} (hEq : ∀ b : Fin R, γ1 (r (fIdx b)) = γ2 (r (fIdx b))) :
    bStarFlags hR r fIdx γ1 = bStarFlags hR r fIdx γ2 ∧ (activeFlags r fIdx γ1 ↔
    activeFlags r fIdx γ2) := by
  have hiff : activeFlags r fIdx γ1 ↔ activeFlags r fIdx γ2 :=
      ⟨fun ⟨b, hb⟩ ↦ ⟨b, (hEq b).symm.trans hb⟩, fun ⟨b, hb⟩ ↦ ⟨b, (hEq b).trans hb⟩⟩
  refine ⟨?_, hiff⟩
  have hpred : (fun b : Fin R ↦ γ1 (r (fIdx b)) = 1) = (fun b : Fin R ↦ γ2 (r (fIdx b)) = 1) :=
    funext fun b ↦ propext ⟨fun h ↦ (hEq b).symm.trans h, fun h ↦ (hEq b).trans h⟩
  dsimp only [bStarFlags, activeFlags]; simp only [hpred]
theorem cXorFlagsToDum_inactive {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    (outBase : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118) (hf : ∀ b : Fin R, (fIdx b).val < outBase)
    {γ : BitAssignment n} (h0 : ∀ b : Fin R, γ (r (fIdx b)) = 0) :
    (cXorFlagsToDum r fIdx outBase hOut hf).eval.1.mulVec (ket γ) = ket γ :=
  seqNat_mulVec_fixed (ket γ) R _ fun i hi ↦ by
    rw [ket_CNOT, h0 ⟨i, hi⟩, add_zero, Function.update_eq_self]

theorem seqNat_cnot_active_w5 {R n : ℕ} (c t : Fin R → Wire n) (hct : ∀ b1 b2, c b1 ≠ t b2)
    {γ : BitAssignment n} {b0 : Fin R} (hb0 : γ (c b0) = 1) (hOther : ∀ b, b ≠ b0 → γ (c b) = 0) :
    (seqNat R fun i hi ↦ Circuit.CNOT (c ⟨i, hi⟩) (t ⟨i, hi⟩) (hct ⟨i, hi⟩ ⟨i, hi⟩)).eval.1.mulVec
      (ket γ) = ket (Function.update γ (t b0) (γ (t b0) + 1)) := by
  have hneOf {i : ℕ} (hi : i < R) (h : i ≠ b0.val) : (⟨i, hi⟩ : Fin R) ≠ b0 :=
    fun e ↦ h (congrArg Fin.val e)
  simpa only [b0.isLt, ↓reduceIte] using
    seqNat_mulVec_single (ket γ) (ket (Function.update γ (t b0) (γ (t b0) + 1))) b0.val R _
      (fun i hi hlt ↦ by
        rw [ket_CNOT, hOther ⟨i, hi⟩ (hneOf hi (Nat.ne_of_lt hlt)), add_zero,
          Function.update_eq_self])
      (fun hi0 ↦ by
        rw [ket_CNOT, show (⟨b0.val, hi0⟩ : Fin R) = b0 from Fin.ext rfl, hb0])
      (fun i hi hgt ↦ by
        rw [ket_CNOT, Function.update_of_ne (hct ⟨i, hi⟩ b0),
          hOther ⟨i, hi⟩ (hneOf hi (Nat.ne_of_gt hgt)), add_zero, Function.update_eq_self])

theorem cXorFlagsToDum_active {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    (outBase : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118) (hf : ∀ b : Fin R, (fIdx b).val < outBase)
    {γ : BitAssignment n} {b0 : Fin R} (hb0 : γ (r (fIdx b0)) = 1)
    (hOther : ∀ b : Fin R, b ≠ b0 → γ (r (fIdx b)) = 0) :
    (cXorFlagsToDum r fIdx outBase hOut hf).eval.1.mulVec (ket γ) =
    ket (Function.update γ (r (rDumIdxR outBase R hOut)) (γ (r (rDumIdxR outBase R hOut)) + 1))
    := by
  exact seqNat_cnot_active_w5 (fun b ↦ r (fIdx b)) (fun _ ↦ r (rDumIdxR outBase R hOut))
    (fun b _ ↦ flag_ne_rDum r fIdx outBase hOut hf b) hb0 hOther

theorem cXorFlagsToLo_inactive {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118)
    (outBase : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118) (hf : ∀ b : Fin R, (fIdx b).val < outBase)
    {γ : BitAssignment n} (h0 : ∀ b : Fin R, γ (r (fIdx b)) = 0) :
    (cXorFlagsToLo r fIdx outBase hOut hf).eval.1.mulVec (ket γ) = ket γ :=
  seqNat_mulVec_fixed (ket γ) R _ fun i hi ↦ by
    rw [ket_CNOT, h0 ⟨i, hi⟩, add_zero, Function.update_eq_self]

theorem cXorFlagsToLo_active {R n : ℕ} (r : QRegister 118 n) (fIdx : Fin R → Wire 118) (outBase : ℕ)
    (hOut : outBase + 2 + 2 * R ≤ 118) (hf : ∀ b : Fin R, (fIdx b).val < outBase)
    {γ : BitAssignment n} {b0 : Fin R} (hb0 : γ (r (fIdx b0)) = 1)
    (hOther : ∀ b : Fin R, b ≠ b0 → γ (r (fIdx b)) = 0) :
    (cXorFlagsToLo r fIdx outBase hOut hf).eval.1.mulVec (ket γ) =
    ket (Function.update γ (r (wIdxR outBase R hOut b0 fp1_0))
    (γ (r (wIdxR outBase R hOut b0 fp1_0)) + 1)) := by
  exact seqNat_cnot_active_w5 (fun b ↦ r (fIdx b)) (fun b ↦ r (wIdxR outBase R hOut b fp1_0))
    (fun b1 b2 ↦ flag_ne_wIdx r fIdx outBase hOut hf b1 b2 fp1_0) hb0 hOther

abbrev cAnd118 (a b t : ℕ) : ℕ := 2 + 4 * a + 2048 * b + 1048576 * t
abbrev cCnot118 (c t : ℕ) : ℕ := 1 + 4 * c + 2048 * t

def tPairSpec (u fb lo hi : ℕ) : PrimTree := p3 (cAnd118 fb u hi) (cCnot118 fb lo) (cCnot118 hi lo)
theorem evalPrimTree_tPairSpec_testBit (st u fb lo hi k : ℕ) (hu : u < 118) (hfb : fb < 118)
    (hlo : lo < 118) (hhi : hi < 118) (hfbu : fb ≠ u) (hfblo : fb ≠ lo) (hfbhi : fb ≠ hi)
    (hulo : u ≠ lo) (huhi : u ≠ hi) (hlohi : lo ≠ hi) (hlo0 : st.testBit lo = false)
    (hhi0 : st.testBit hi = false) : (evalPrimTree 117 st (tPairSpec u fb lo hi)).testBit k = if k =
    lo then st.testBit fb && !st.testBit u else if k = hi then st.testBit fb &&
    st.testBit u else st.testBit k := by
  dsimp only [tPairSpec, p3, p2, evalPrimTree]
  have g1 (x : ℕ) : evalPrimGate 117 x (cAnd118 fb u hi) =
      if x.testBit fb && x.testBit u then x ^^^ (1 <<< hi) else x := by
    unfold evalPrimGate cAnd118
    dsimp only
    set c := 2 + 4 * fb + 2048 * u + 1048576 * hi
    rw [Nat.shiftRight_eq_div_pow c 2, Nat.shiftRight_eq_div_pow c 11,
      Nat.shiftRight_eq_div_pow c 20, show c % 4 = 2 by omega,
      show ((c / 4) % 512) % 118 = fb by omega, show ((c / 2048) % 512) % 118 = u by omega,
      show ((c / 1048576) % 512) % 118 = hi by omega,
      nat_beq_false_of_ne hfbu, nat_beq_false_of_ne hfbhi, nat_beq_false_of_ne huhi]
    simp only [Nat.beq, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
  have gCnot {a b : ℕ} (ha : a < 118) (hb : b < 118) (hab : a ≠ b) (x : ℕ) :
      evalPrimGate 117 x (cCnot118 a b) = if x.testBit a then x ^^^ (1 <<< b) else x := by
    unfold evalPrimGate cCnot118
    dsimp only
    set c := 1 + 4 * a + 2048 * b
    rw [Nat.shiftRight_eq_div_pow c 2, Nat.shiftRight_eq_div_pow c 11,
      show c % 4 = 1 by omega, show ((c / 4) % 512) % 118 = a by omega,
      show ((c / 2048) % 512) % 118 = b by omega, nat_beq_false_of_ne hab]
    simp only [Nat.beq, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
  have hXor (b : Bool) (x a j : ℕ) :
      (if b then x ^^^ (1 <<< a) else x).testBit j =
        if a = j then b != x.testBit j else x.testBit j := by
    by_cases haj : a = j <;> cases b <;>
      simp only [haj, Bool.false_eq_true, ↓reduceIte, testBit_xor_shift1] <;>
      cases x.testBit j <;> rfl
  rw [g1, gCnot hfb hlo hfblo, gCnot hhi hlo hlohi.symm]
  rcases eq_or_ne k lo with rfl | hklo
  · simp only [hXor, hlohi, hlohi.symm, hfbhi.symm, ↓reduceIte, hlo0, hhi0]
    cases st.testBit fb <;> cases st.testBit u <;> decide
  rcases eq_or_ne k hi with rfl | hkhi
  · simp only [hXor, hklo, hlohi, hfbhi.symm, ↓reduceIte, hhi0]
    cases st.testBit fb <;> cases st.testBit u <;> decide
  simp only [hXor, hklo, hkhi, Ne.symm hklo, Ne.symm hkhi, hlohi, hfbhi.symm, ↓reduceIte]

def tRouterSpec {R : ℕ} (uIdx : Wire 118) (fIdx : Fin R → Wire 118)
    (outBase : ℕ) : (m : ℕ) → m ≤ R → PrimTree
  | 0, _ => .empty
  | m + 1, hm =>
      .node (tRouterSpec uIdx fIdx outBase m (Nat.le_of_succ_le hm))
        (tPairSpec uIdx.val (fIdx ⟨m, hm⟩).val (outBase + 2 + 2 * m) (outBase + 3 + 2 * m))

theorem evalPrimTree_tRouterSpec_testBit {R : ℕ}
    (uIdx : Wire 118) (fIdx : Fin R → Wire 118) (outBase : ℕ)
    (hOut : outBase + 2 + 2 * R ≤ 118) (huB : uIdx.val < outBase)
    (hfB : ∀ b : Fin R, (fIdx b).val < outBase ∧ (fIdx b).val ≠ uIdx.val)
    (st : ℕ) (hZeroOut : ∀ j, outBase + 2 ≤ j → j < outBase + 2 + 2 * R → st.testBit j = false) :
    ∀ (m : ℕ) (hm : m ≤ R) (k : ℕ),
      (evalPrimTree 117 st (tRouterSpec uIdx fIdx outBase m hm)).testBit k =
        if h : outBase + 2 ≤ k ∧ k < outBase + 2 + 2 * m then
          st.testBit (fIdx ⟨(k - (outBase + 2)) / 2, by omega⟩).val &&
            if (k - (outBase + 2)) % 2 = 0 then !st.testBit uIdx.val else st.testBit uIdx.val
        else st.testBit k
  | 0, _, _ => by
      dsimp only [tRouterSpec, evalPrimTree]
      rw [diteNeg (by omega)]
  | m + 1, hm, k => by
      dsimp only [tRouterSpec, evalPrimTree]
      have ih := evalPrimTree_tRouterSpec_testBit uIdx fIdx outBase hOut huB hfB st hZeroOut m
        (Nat.le_of_succ_le hm)
      have hfbB := (hfB ⟨m, hm⟩).1
      have h0 {j} (hj1 : outBase + 2 + 2 * m ≤ j) (hj2 : j < outBase + 2 + 2 * (m + 1)) :=
        (ih j).trans ((diteNeg (by omega)).trans (hZeroOut j (by omega) (by omega)))
      rw [evalPrimTree_tPairSpec_testBit _ uIdx.val (fIdx ⟨m, hm⟩).val (outBase + 2 + 2 * m)
          (outBase + 3 + 2 * m) k uIdx.isLt (fIdx ⟨m, hm⟩).isLt (by omega) (by omega)
          (hfB ⟨m, hm⟩).2 (by omega) (by omega) (by omega) (by omega) (by omega)
          (h0 le_rfl (by omega)) (h0 (by omega) (by omega)),
        (ih (fIdx ⟨m, hm⟩).val).trans (diteNeg (by omega)),
        (ih uIdx.val).trans (diteNeg (by omega))]
      rcases eq_or_ne k (outBase + 2 + 2 * m) with rfl | hklo
      · rw [itePos rfl, ditePos (by omega),
          show (outBase + 2 + 2 * m - (outBase + 2)) % 2 = 0 by omega, itePos rfl]
        exact congrArg (fun b : Fin R ↦ st.testBit (fIdx b).val && !st.testBit uIdx.val)
          (Fin.ext (show m = (outBase + 2 + 2 * m - (outBase + 2)) / 2 by omega))
      rcases eq_or_ne k (outBase + 3 + 2 * m) with rfl | hkhi
      · rw [iteNeg hklo, itePos rfl, ditePos (by omega),
          show (outBase + 3 + 2 * m - (outBase + 2)) % 2 = 1 by omega, iteNeg one_ne_zero]
        exact congrArg (fun b : Fin R ↦ st.testBit (fIdx b).val && st.testBit uIdx.val)
          (Fin.ext (show m = (outBase + 3 + 2 * m - (outBase + 2)) / 2 by omega))
      rw [iteNeg hklo, iteNeg hkhi, ih k]
      by_cases hkM : outBase + 2 ≤ k ∧ k < outBase + 2 + 2 * m
      · rw [ditePos hkM, ditePos (by omega)]
      · rw [diteNeg hkM, diteNeg (by omega)]

theorem subspaceStep_pWIntactTreeBracket {Var : Type} [Fintype Var] [DecidableEq Var] {W R k n : ℕ}
    [NeZero (2 ^ n)] (hR : 0 < R) (v : Var) (rWork : QRegister W n) (r : QRegister 118 n)
    (rTgt : QRegister k n) (hDisj : r.DisjointWires rTgt) (uIdx : Wire 118)
    (fIdx : Fin R → Wire 118) (outBase : ℕ) (hOut : outBase + 2 + 2 * R ≤ 118)
    (hBnd : 38 < outBase ∧ uIdx.val < outBase ∧ uIdx.val ≠ 38)
    (hfB : ∀ b : Fin R, (fIdx b).val < outBase ∧ (fIdx b).val ≠ uIdx.val) (tCur : PrimTree)
    (st : BitAssignment n → BitAssignment n) (g : BitAssignment n → Fin k → ZMod 2)
    (phPre phPost : BitAssignment n → ZMod 2) (mid : DynamicCircuit Var n)
    (hMut : ∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) → ∀ b1 b2 : Fin R, b1 ≠ b2 →
    stTree118 r tCur st δ (r (fIdx b1)) = 1 → stTree118 r tCur st δ (r (fIdx b2)) = 0)
    (hCln : ∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
    (evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) tCur).testBit 38 = false ∧ ∀ j,
    outBase ≤ j → j < outBase + 2 + 2 * R → (evalPrimTree 117 (natOfZModBits 118 (fun i ↦
    st δ (r i))) tCur).testBit j = false)
    (hMid : SubspaceStep (mkKetOpW rWork (stTree118 r (.node tCur (tRouterSpec uIdx fIdx outBase R
    le_rfl)) st) phPre)
    (mkKetOpW rWork (stTree118 r (.node tCur (tRouterSpec uIdx fIdx outBase R le_rfl))
    (fun δ ↦ writeReg (st δ) rTgt (g δ))) phPost) mid) :
    SubspaceStep (mkKetOpW rWork (stTree118 r tCur st) phPre)
    (mkKetOpW rWork (stTree118 r tCur (fun δ ↦ writeReg (st δ) rTgt (g δ))) phPost)
    (pWIntactBracket v r uIdx fIdx outBase hOut hBnd (fun b ↦ (hfB b).1) mid) ∧
    (pWIntactBracket v r uIdx fIdx outBase hOut hBnd (fun b ↦ (hfB b).1) mid).count .T =
    (2 * R + 2) + mid.count .T ∧ (pWIntactBracket v r uIdx fIdx outBase hOut hBnd (fun b ↦
    (hfB b).1) mid).count .TOFF = mid.count .TOFF ∧ (∀ S : Wire n → Prop, (∀ u, S (r u)) →
    DynWires S mid → DynWires S (pWIntactBracket v r uIdx fIdx outBase hOut hBnd (fun b ↦
    (hfB b).1) mid)) := by
  let hf := fun b : Fin R ↦ (hfB b).1
  obtain ⟨hCntT, hCntF, hDW⟩ := counts_dw_pWIntactBracket v r uIdx fIdx outBase hOut hBnd hf mid
  refine ⟨?_, hCntT, hCntF, hDW⟩
  let stPost := fun δ ↦ writeReg (st δ) rTgt (g δ)
  let tR := tRouterSpec uIdx fIdx outBase R le_rfl
  let hInj := wOptInj_onReg118 r uIdx outBase hOut hBnd
  let uLo1 : Fin 1 → Wire n := fun _ ↦ r uIdx
  let wP := fun b p ↦ r (wIdxR outBase R hOut b p)
  let rDum := r (rDumIdxR outBase R hOut)
  let wDum := r (wDumIdxR outBase R hOut)
  let qEnc := r qEncIdx118
  let actP := activeFlags r fIdx
  let bStar := bStarFlags hR r fIdx
  let PDum := pDumMatch r fIdx rDum
  let stInPre := stTree118 r tCur st
  let stInPost := stTree118 r tCur stPost
  let stDumPre (δ : BitAssignment n) : BitAssignment n :=
    Function.update (stInPre δ) rDum (if actP (stInPre δ) then 0 else 1)
  let pUOf (η : BitAssignment n) : Fin (2 ^ 1) :=
    ⟨idxValPrefix uLo1 η 1 le_rfl, idxValPrefix_lt_two_pow uLo1 η 1 le_rfl⟩
  have hpUVal (η) : (pUOf η).val = if η (r uIdx) = 1 then 1 else 0 := zero_add _
  have upd0 {f : BitAssignment n} {w : Wire n} (hw : f w = 0) : Function.update f w 0 = f :=
    hw ▸ Function.update_eq_self w f
  have hOtherOf {γ : BitAssignment n}
      (hM : ∀ b1 b2 : Fin R, b1 ≠ b2 → γ (r (fIdx b1)) = 1 → γ (r (fIdx b2)) = 0)
      {b0 : Fin R} (hb0 : γ (r (fIdx b0)) = 1) (b : Fin R) (hne : b ≠ b0) : γ (r (fIdx b)) = 0 :=
    (DynCircExt.bit_cases (γ (r (fIdx b)))).elim id
      fun h1 ↦ absurd ((hM b b0 hne h1).symm.trans hb0) zero_ne_one
  have hAll0Of {γ : BitAssignment n} (hnA : ¬ actP γ) (b : Fin R) : γ (r (fIdx b)) = 0 :=
    (DynCircExt.bit_cases (γ (r (fIdx b)))).elim id fun h1 ↦ (hnA ⟨b, h1⟩).elim
  -- Helper properties for any stX agreeing with st on r
  have hKetFacts (stX : BitAssignment n → BitAssignment n) (hAg : ∀ δ u, stX δ (r u) = st δ (r u))
      (δ : BitAssignment n) (hz : ∀ q : Fin W, δ (rWork q) = 0) :
      let γ := stTree118 r tCur stX δ
      (∀ b1 b2 : Fin R, b1 ≠ b2 → γ (r (fIdx b1)) = 1 → γ (r (fIdx b2)) = 0) ∧
      γ qEnc = 0 ∧ γ rDum = 0 ∧ γ wDum = 0 ∧ (∀ b p, γ (wP b p) = 0) ∧
      (∀ b0, γ (r (fIdx b0)) = 1 → ∀ pU : Fin (2 ^ 1),
        pU.val = (if γ (r uIdx) = 1 then 1 else 0) →
        stTree118 r (.node tCur tR) stX δ = Function.update γ (wP b0 pU) 1) ∧
      (¬ actP γ → stTree118 r (.node tCur tR) stX δ = γ) := by
    intro γ
    have hNatEq := congrArg (natOfZModBits 118) (funext fun i ↦ hAg δ i)
    have hγEq (u : Wire 118) : γ (r u) = stInPre δ (r u) := by
      simp only [γ, stInPre, stTree118_apply_reg]
      exact bitZMod2_congr (congrArg (fun x ↦ (evalPrimTree 117 x tCur).testBit u.val) hNatEq)
    obtain ⟨hqB, hOutB⟩ := hCln δ hz
    have hMutγ (b1 b2 : Fin R) (hne : b1 ≠ b2) (h1 : γ (r (fIdx b1)) = 1) : γ (r (fIdx b2)) = 0 :=
      (hγEq _).trans (hMut δ hz b1 b2 hne ((hγEq _).symm.trans h1))
    have h0Of (u : Wire 118) (hf0) : γ (r u) = 0 := stTree118_eq_zero_of_false r tCur stX δ u
      ((congrArg (fun x ↦ (evalPrimTree 117 x tCur).testBit u.val) hNatEq).trans hf0)
    have hwP0 (b : Fin R) (p : Fin (2 ^ 1)) : γ (wP b p) = 0 :=
      h0Of (wIdxR outBase R hOut b p) (by
        have hp : p.val < 2 := p.isLt
        dsimp only [wIdxR]
        exact hOutB _ (by omega) (by omega))
    have hSp (x : Wire n) : stTree118 r (.node tCur tR) stX δ x =
        if h : ∃ (b : Fin R) (p : Fin (2 ^ 1)), x = wP b p then
          γ (r (fIdx h.choose)) *
            if h.choose_spec.choose.val = 0 then 1 + γ (r uIdx) else γ (r uIdx)
        else γ x := by
      by_cases hxR : ∃ u : Wire 118, r u = x
      · obtain ⟨u, rfl⟩ := hxR
        rw [stTree118_apply_reg]
        set t0 := evalPrimTree 117 (natOfZModBits 118 (fun i ↦ stX δ (r i))) tCur with ht0
        have hEvSp : (evalPrimTree 117 (natOfZModBits 118 (fun i ↦ stX δ (r i)))
            (.node tCur tR)).testBit u.val = _ :=
          evalPrimTree_tRouterSpec_testBit uIdx fIdx outBase hOut hBnd.2.1 hfB t0
            (fun j _ hj2 ↦ (congrArg (fun x ↦ (evalPrimTree 117 x tCur).testBit j) hNatEq).trans
              (hOutB j (by omega) hj2)) R le_rfl u.val
        by_cases huW : outBase + 2 ≤ u.val ∧ u.val < outBase + 2 + 2 * R
        · let b : Fin R := ⟨(u.val - (outBase + 2)) / 2, by omega⟩
          let p : Fin (2 ^ 1) := ⟨(u.val - (outBase + 2)) % 2, Nat.mod_lt _ (by decide)⟩
          have huEq : r u = wP b p := congrArg r.wires (Fin.ext (by dsimp [wIdxR, b, p]; omega))
          have hex : ∃ b' p', r u = wP b' p' := ⟨b, p, huEq⟩
          obtain ⟨hbEq, hpEq⟩ := hInj.w_inj _ _ b p (hex.choose_spec.choose_spec.symm.trans huEq)
          rw [ditePos hex, congrArg Fin.val hpEq, hbEq, bitZMod2_congr (hEvSp.trans (ditePos huW))]
          dsimp only [γ, p]
          rw [stTree118_apply_reg, stTree118_apply_reg]
          by_cases hp0 : (u.val - (outBase + 2)) % 2 = 0 <;> simp only [← ht0, hp0, ↓reduceIte] <;>
            cases t0.testBit (fIdx b).val <;> cases t0.testBit uIdx.val <;> decide
        · rw [diteNeg fun ⟨b, p, heq⟩ ↦ by
              have hv := congrArg Fin.val (r.wires.injective heq)
              have hp : p.val < 2 := p.isLt
              dsimp only [wIdxR] at hv; omega,
            bitZMod2_congr (hEvSp.trans (diteNeg huW))]
          exact (stTree118_apply_reg r tCur stX δ u).symm
      · rw [diteNeg fun ⟨b, p, heq⟩ ↦ hxR ⟨wIdxR outBase R hOut b p, heq.symm⟩,
          stTree118, writeReg_apply_of_not_mem _ _ _ _ hxR]
        exact (writeReg_apply_of_not_mem _ _ _ _ hxR).symm
    refine ⟨hMutγ, h0Of qEncIdx118 hqB, h0Of _ (hOutB outBase le_rfl (by omega)),
      h0Of _ (hOutB (outBase + 1) (by omega) (by omega)), hwP0,
      fun b0 hb0 pU hpU ↦ funext fun x ↦ ?_, fun hA ↦ funext fun x ↦ ?_⟩
    · rw [hSp x]
      by_cases hxw : ∃ b p, x = wP b p
      · rw [ditePos hxw]
        conv_rhs => rw [hxw.choose_spec.choose_spec]
        have hM (b' : Fin R) (p' : Fin (2 ^ 1)) :
            γ (r (fIdx b')) * (if p'.val = 0 then 1 + γ (r uIdx) else γ (r uIdx)) =
              Function.update γ (wP b0 pU) 1 (wP b' p') := by
          rcases eq_or_ne b' b0 with rfl | hbb
          · rw [hb0, one_mul]
            have h2 : ∀ (q q' : Fin (2 ^ 1)) (u : ZMod 2), q.val = (if u = 1 then 1 else 0) →
                (if q' = q then (1 : ZMod 2) else 0) = if q'.val = 0 then 1 + u else u := by decide
            rcases eq_or_ne p' pU with rfl | hp
            · rw [Function.update_self, ← h2 p' p' _ hpU, itePos rfl]
            · rw [Function.update_of_ne fun e ↦ hp (hInj.w_inj _ _ _ _ e).2, hwP0,
                ← h2 pU _ _ hpU, iteNeg hp]
          · rw [hOtherOf hMutγ hb0 _ hbb, zero_mul,
              Function.update_of_ne fun e ↦ hbb (hInj.w_inj _ _ _ _ e).1, hwP0]
        exact hM _ _
      · rw [diteNeg hxw, Function.update_of_ne fun e ↦ hxw ⟨b0, pU, e⟩]
    · rw [hSp x]
      by_cases hxw : ∃ b p, x = wP b p
      · rw [ditePos hxw, hAll0Of hA hxw.choose, zero_mul]
        conv_rhs => rw [hxw.choose_spec.choose_spec]
        exact (hwP0 _ _).symm
      · rw [diteNeg hxw]
  have hBaseDum (δ : BitAssignment n) (hz : ∀ q : Fin W, δ (rWork q) = 0) :
      (∀ b : Fin R, stDumPre δ (r (fIdx b)) = stInPre δ (r (fIdx b))) ∧
      bStar (stDumPre δ) = bStar (stInPre δ) ∧ (actP (stInPre δ) ↔ actP (stDumPre δ)) ∧
      (OptBasePred PDum wDum qEnc (stDumPre δ) ∧ ∀ b p, stDumPre δ (wP b p) = 0) := by
    obtain ⟨_, hq0, _, hwd0, hwP0, _, _⟩ := hKetFacts st (fun _ _ ↦ rfl) δ hz
    have hFlagD (b : Fin R) : stDumPre δ (r (fIdx b)) = stInPre δ (r (fIdx b)) :=
      Function.update_of_ne (flag_ne_rDum r fIdx outBase hOut hf b) _ _
    obtain ⟨hbStarD, hActD⟩ := bStarFlags_congr hR r fIdx hFlagD
    refine ⟨hFlagD, hbStarD, hActD.symm, ⟨⟨?_,
      (Function.update_of_ne hInj.rDum_ne_wDum.symm _ _).trans hwd0,
      (Function.update_of_ne hInj.rDum_ne_qEnc.symm _ _).trans hq0⟩,
      fun b p ↦ (Function.update_of_ne (hInj.w_ne_rDum b p) _ _).trans (hwP0 b p)⟩⟩
    change stDumPre δ rDum = if activeFlags r fIdx (stDumPre δ) then 0 else 1
    rw [show stDumPre δ rDum = if actP (stInPre δ) then 0 else 1 from
      Function.update_self rDum _ (stInPre δ)]
    by_cases hA : actP (stInPre δ)
    · rw [itePos hA, itePos (hActD.mpr hA)]
    · rw [iteNeg hA, iteNeg fun h ↦ hA (hActD.mp h)]
  have hAgPost (δ' u) : stPost δ' (r u) = st δ' (r u) :=
    writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ disj_ne hDisj u j hj.symm
  have eqMulMul {A B s1 s2 ph} (h : ∀ δ, (∀ q, δ (rWork q) = 0) →
      (A : Operator (2 ^ n)).mulVec (ket (s1 δ)) = B.mulVec (ket (s2 δ))) :
      A * mkKetOpW rWork s1 ph = B * mkKetOpW rWork s2 ph := matrix_ext_ket fun δ ↦ by
    simp only [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, h δ hz]
    · simp only [Matrix.mulVec_zero]
  have eqMulKet {A s1 s2 ph} (h : ∀ δ, (∀ q, δ (rWork q) = 0) →
      (A : Operator (2 ^ n)).mulVec (ket (s1 δ)) = ket (s2 δ)) :
      A * mkKetOpW rWork s1 ph = mkKetOpW rWork s2 ph := by
    simpa only [Matrix.one_mul] using
      eqMulMul (B := 1) fun δ hz ↦ (h δ hz).trans (Matrix.one_mulVec _).symm
  have eqMul2Ket {A B s1 s2 ph} (h : ∀ δ, (∀ q, δ (rWork q) = 0) →
      (A : Operator (2 ^ n)).mulVec (B.mulVec (ket (s1 δ))) = ket (s2 δ)) :
      A * (B * mkKetOpW rWork s1 ph) = mkKetOpW rWork s2 ph :=
    (Matrix.mul_assoc A B _).symm.trans <| eqMulKet fun δ hz ↦ by
      simpa only [← Matrix.mulVec_mulVec] using h δ hz
  let preOp (P) [DecidablePred P] := oneHotOptPreOp (OptBasePred P wDum qEnc) actP bStar uLo1 wP
  let cXLo := cXorFlagsToLo r fIdx outBase hOut hf
  let cXDum := cXorFlagsToDum r fIdx outBase hOut hf
  have hFw {γ : BitAssignment n} {p} (b b0) :
      Function.update γ (wP b0 p) 1 (r (fIdx b)) = γ (r (fIdx b)) :=
    Function.update_of_ne (flag_ne_wIdx r fIdx outBase hOut hf b b0 p) 1 γ
  have hPre {P} [DecidablePred P] {γ γD lvl} (hl : lvl ≤ 1) (p : Fin (2 ^ 1))
      (hp : ∀ {hlt}, (⟨idxValPrefix uLo1 γD lvl hl, hlt⟩ : Fin (2 ^ 1)) = p)
      (hM : ∀ b1 b2, b1 ≠ b2 → γ (r (fIdx b1)) = 1 → γ (r (fIdx b2)) = 0)
      (hB : OptBasePred P wDum qEnc γD ∧ ∀ b q, γD (wP b q) = 0)
      (hbS : bStar γD = bStar γ) (hAct : actP γ ↔ actP γD) :
      (∀ b0, γ (r (fIdx b0)) = 1 →
        (preOp P lvl hl).mulVec (ket γD) = ket (Function.update γD (wP b0 p) 1)) ∧
      (¬ actP γ → (preOp P lvl hl).mulVec (ket γD) = ket γD) :=
    ⟨fun b0 hb0 ↦ by
      dsimp only [preOp, actP, bStar]
      rw [oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec, itePos hB,
          itePos (hAct.mp ⟨b0, hb0⟩),
        show bStarFlags hR r fIdx γD = bStarFlags hR r fIdx γ from hbS,
        bStarFlags_eq_of_one hR r fIdx hM hb0, hp], fun hI ↦ by
      dsimp only [preOp, actP]
      rw [oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec, itePos hB,
        iteNeg fun h ↦ hI (hAct.mpr h)]⟩
  -- 1. Forward cInit identity
  have hStepInit : (Circuit.X rDum ;;ᶜ cXDum ;;ᶜ cXLo).eval.1 * mkKetOpW rWork stInPre phPre =
      preOp PDum 0 (Nat.zero_le 1) * mkKetOpW rWork stDumPre phPre :=
    eqMulMul fun δ hz ↦ by
      set γ := stInPre δ
      set γD := stDumPre δ
      obtain ⟨hMutγ, _, hrd0, _, hwP0, _, _⟩ := hKetFacts st (fun _ _ ↦ rfl) δ hz
      obtain ⟨_, hbSD, hActD, hBaseD⟩ := hBaseDum δ hz
      obtain ⟨hDA, hDI⟩ := hPre (P := PDum) (γD := γD) (Nat.zero_le 1) fp1_0
        (fun {_} ↦ Fin.ext rfl) hMutγ hBaseD hbSD hActD
      rw [eval_seq_mulVec, eval_seq_mulVec, ket_X, show γ rDum = 0 from hrd0, zero_add]
      have hF1 (b : Fin R) : Function.update γ rDum 1 (r (fIdx b)) = γ (r (fIdx b)) :=
        Function.update_of_ne (flag_ne_rDum r fIdx outBase hOut hf b) 1 γ
      by_cases hA : actP γ
      · obtain ⟨b0, hb0⟩ := hA
        have hbO := hOtherOf hMutγ hb0
        rw [hDA b0 hb0,
          show γD = γ from (congrArg (Function.update γ rDum) (itePos ⟨b0, hb0⟩)).trans (upd0 hrd0),
          cXorFlagsToDum_active r fIdx outBase hOut hf ((hF1 b0).trans hb0)
            (fun b hne ↦ (hF1 b).trans (hbO b hne)),
          Function.update_idem, Function.update_self, CharTwo.add_self_eq_zero, upd0 hrd0,
          cXorFlagsToLo_active r fIdx outBase hOut hf hb0 hbO,
          show γ (wP b0 fp1_0) = 0 from hwP0 b0 fp1_0, zero_add]
      · have hF0 b := (hF1 b).trans (hAll0Of hA b)
        rw [hDI hA, cXorFlagsToDum_inactive r fIdx outBase hOut hf hF0,
          cXorFlagsToLo_inactive r fIdx outBase hOut hf hF0]
        dsimp only [actP, γD, stDumPre]
        rw [iteNeg hA]
  -- 2. Forward cClearDum identity
  have hStepClear : (cXDum ;;ᶜ Circuit.X rDum).eval.1 *
      (preOp PDum 1 le_rfl * mkKetOpW rWork stDumPre phPre) =
      mkKetOpW rWork (stTree118 r (.node tCur tR) st) phPre :=
    eqMul2Ket fun δ hz ↦ by
      set γ := stInPre δ
      set γD := stDumPre δ
      obtain ⟨hMutγ, _, hrd0, _, _, hNodeAct, hNodeInact⟩ := hKetFacts st (fun _ _ ↦ rfl) δ hz
      obtain ⟨hFlagD, hbSD, hActD, hBaseD⟩ := hBaseDum δ hz
      obtain ⟨hDA, hDI⟩ := hPre (P := PDum) (γD := γD) le_rfl (pUOf γD) (fun {_} ↦ Fin.ext rfl)
        hMutγ hBaseD hbSD hActD
      by_cases hA : actP γ
      · obtain ⟨b0, hb0⟩ := hA
        have hbO := hOtherOf hMutγ hb0
        have hrd1 : Function.update γ (wP b0 (pUOf γ)) 1 rDum = 0 :=
          (Function.update_of_ne (hInj.w_ne_rDum b0 (pUOf γ)).symm 1 γ).trans hrd0
        rw [hDA b0 hb0,
          show γD = γ from (congrArg (Function.update γ rDum) (itePos ⟨b0, hb0⟩)).trans (upd0 hrd0),
          eval_seq_mulVec, cXorFlagsToDum_active r fIdx outBase hOut hf ((hFw b0 b0).trans hb0)
            (fun b hne ↦ (hFw b b0).trans (hbO b hne)),
          ket_X, Function.update_idem, Function.update_self, hrd1, zero_add,
          CharTwo.add_self_eq_zero, upd0 hrd1]
        exact congrArg ket (hNodeAct b0 hb0 (pUOf γ) (hpUVal γ)).symm
      · rw [hDI hA, eval_seq_mulVec,
          cXorFlagsToDum_inactive r fIdx outBase hOut hf (fun b ↦ (hFlagD b).trans (hAll0Of hA b)),
          ket_X]
        dsimp only [γD, stDumPre, actP]
        rw [iteNeg (show ¬ activeFlags r fIdx γ from hA), Function.update_idem,
          Function.update_self, CharTwo.add_self_eq_zero, upd0 hrd0, ← hNodeInact hA]
  -- 3. Uncompute entry identity (on stPost)
  have hUncIn : mkKetOpW rWork (stTree118 r (.node tCur tR) stPost) phPost =
      preOp (@pTrue118 n) 1 le_rfl * mkKetOpW rWork stInPost phPost :=
    (eqMulKet fun δ hz ↦ by
      set γ := stInPost δ
      obtain ⟨hMutγ, hq0, _, hwd0, hwP0, hNodeAct, hNodeInact⟩ := hKetFacts stPost hAgPost δ hz
      obtain ⟨hTA, hTI⟩ := hPre (P := @pTrue118 n) (γD := γ) le_rfl (pUOf γ) (fun {_} ↦ Fin.ext rfl)
        hMutγ ⟨⟨trivial, hwd0, hq0⟩, hwP0⟩ rfl .rfl
      by_cases hA : actP γ
      · obtain ⟨b0, hb0⟩ := hA
        exact (hTA b0 hb0).trans (congrArg ket (hNodeAct b0 hb0 (pUOf γ) (hpUVal γ)).symm)
      · exact (hTI hA).trans (congrArg ket (hNodeInact hA).symm)).symm
  -- 4. Uncompute exit identity (cXorFlagsToLo on level 0)
  let oT0 := preOp (@pTrue118 n) 0 (Nat.zero_le 1)
  have hUncOut : cXLo.eval.1 * (oT0 * mkKetOpW rWork stInPost phPost) =
      mkKetOpW rWork stInPost phPost :=
    eqMul2Ket fun δ hz ↦ by
      set γ := stInPost δ
      obtain ⟨hMutγ, hq0, _, hwd0, hwP0, _, _⟩ := hKetFacts stPost hAgPost δ hz
      obtain ⟨hTA, hTI⟩ := hPre (P := @pTrue118 n) (γD := γ) (Nat.zero_le 1) fp1_0
        (fun {_} ↦ Fin.ext rfl) hMutγ ⟨⟨trivial, hwd0, hq0⟩, hwP0⟩ rfl .rfl
      by_cases hA : actP γ
      · obtain ⟨b0, hb0⟩ := hA
        have hbO := hOtherOf hMutγ hb0
        rw [hTA b0 hb0, cXorFlagsToLo_active r fIdx outBase hOut hf ((hFw b0 b0).trans hb0)
            (fun b hne ↦ (hFw b b0).trans (hbO b hne)),
          Function.update_idem, Function.update_self, CharTwo.add_self_eq_zero,
              upd0 (hwP0 b0 fp1_0)]
      · exact (congrArg cXLo.eval.1.mulVec (hTI hA)).trans
          (cXorFlagsToLo_inactive r fIdx outBase hOut hf (hAll0Of hA))
  -- Assemble the 5 steps
  exact subspaceStep_seq_u
    (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) hStepInit)
    (subspaceStep_seq_u
      (subspaceStep_mul_right (mkKetOpW rWork stDumPre phPre)
        (subspaceStep_wLastSplitShiftDyn v PDum actP bStar uLo1 wP rDum wDum qEnc hInj fun _ ↦ id))
      (subspaceStep_seq_u
        (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) hStepClear)
        (subspaceStep_seq_u hMid (subspaceStep_congr_in hUncIn (subspaceStep_seq_u
          (subspaceStep_mul_right (mkKetOpW rWork stInPost phPost)
            (subspaceStep_wUncompTreeDyn_opt v (OptBasePred (@pTrue118 n) wDum qEnc) actP bStar
              uLo1 wP hInj.w_inj hInj.uLo_ne_w
              (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) oT0 .identity)
                (by simp [Circuit.eval_identity])) 1 le_rfl))
          (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) hUncOut))))))
/-! ### 4. Concrete `Dom216` Stage `PrimTree`s & Single-Pass `decide +kernel` Verification -/

def dom216Post21SMask : ℕ := 0x3ffffe000000000000000000

def dom216PreTree : PrimTree :=
    (pN (pN (pN (pN (p4 76 38981 38985 80) (p5 41025 23109710 76 38981 38985))
    (pN (p5 39001 41021 41025 24158286 39001) (p5 39005 41017 41021 25206862 39005)))
    (pN (pN (p5 39009 41013 41017 26255438 39009) (p5 39013 41009 41013 27304014 39013))
    (pN (p5 39017 41005 41009 28352590 39017) (p5 39021 41001 41005 29401166 39021))))
    (pN (pN (pN (p4 39025 40997 41001 30449742) (p5 39025 39029 40993 40997 31498318))
    (pN (p5 39029 39033 40989 40993 32546894) (p5 39033 39037 40985 40989 33595470)))
    (pN (pN (p5 39037 39041 40981 40985 34644046) (p5 39041 39045 40977 40981 35692622))
    (pN (p5 39045 39049 40961 40977 36741198) (p5 73865 73869 75921 73801 75845)))))
def dom216Setup2Tree : PrimTree := (p2 92301 92329)
def dom216Setup3Tree : PrimTree :=
    (pN (p4 110773 110789 220 112729) (p5 112777 112781 112857 112709 112713))
def dom216Setup4Tree : PrimTree :=
    (pN (pN (p4 131085 131093 131105 131113) (p4 131125 131133 131285 131325))
    (pN (p4 133257 133261 133337 135257) (p5 135265 135277 135285 135297 135305)))
def dom216Post21TreeL : PrimTree :=
    (pN (pN (pN (pN (pN (pN (p6 192517 192521 192525 192529 192533 192537)
    (pN (p3 192541 192545 192549) (p4 192553 192557 192561 192565)))
    (pN (pN (p3 192569 192573 192577) (p4 192689 192717 192725 192749))
    (pN (p3 192757 192765 194629) (p4 194649 194653 194657 194661))))
    (pN (pN (pN (p3 194665 194669 194673) (p4 194677 194681 194685 194689))
    (pN (p3 194693 194701 194741) (p4 76740986 192525 192529 192541)))
    (pN (pN (p3 192545 192557 192561) (p4 192573 192577 192689 77789562)) (pN (p3 380 192521 192525)
    (p4 192537 192541 192553 192557))))) (pN (pN (pN (p6 192569 192573 192689 192717 192725 192805)
    (pN (p3 194629 194633 194653) (p4 194661 194669 194677 194685)))
    (pN (pN (p3 194693 194697 194701) (p4 194741 78838138 192517 192521))
    (pN (p3 192525 192529 192533) (p4 192537 192541 192545 192549))))
    (pN (pN (pN (p3 192553 192557 192561) (p4 192565 192569 192573 192577))
    (pN (p3 192689 192717 192725) (p4 192749 192757 192765 194629)))
    (pN (pN (p3 194649 194653 194657) (p4 194661 194665 194669 194673))
    (pN (p3 194677 194681 194685) (p4 194689 194693 194701 194741))))))
    (pN (pN (pN (pN (p6 79886714 380 192517 192525 192537 192545) (pN (p3 192549 192557 192569)
    (p4 192577 192689 192749 192757))) (pN (pN (p3 192765 192805 194633)
    (p4 194649 194657 194665 194673)) (pN (p3 194681 194689 194697)
    (p4 80935290 192525 192529 192557))))
    (pN (pN (pN (p3 192561 192689 81983866) (p4 380 192521 192525 192553))
    (pN (p3 192557 192689 192717) (p4 192725 192821 194629 194633)))
    (pN (pN (p3 194653 194661 194669) (p4 194677 194685 194693 194697))
    (pN (p3 194701 194741 83032442) (p4 192517 192521 192525 192529)))))
    (pN (pN (pN (p6 192549 192553 192557 192561 192689 192717) (pN (p3 192725 192749 192757)
    (p4 192765 194629 194649 194653))) (pN (pN (p3 194657 194661 194665)
    (p4 194669 194673 194677 194681)) (pN (p3 194685 194689 194693)
    (p4 194701 194741 84081018 192517))))
    (pN (pN (pN (p3 192521 192529 192533) (p4 192549 192553 192561 192565))
    (pN (p3 192717 192725 192749) (p4 192757 192765 192809 192813)))
    (pN (pN (p3 192821 194629 194653) (p4 194657 194661 194669 194673))
    (pN (p3 194677 194685 194689) (p4 194693 194697 194701 194741)))))))
    (pN (pN (pN (pN (pN (p6 85129594 192517 192521 192533 192537 192549)
    (pN (p3 192553 192565 192569) (p4 192717 192725 192749 192757)))
    (pN (pN (p3 192765 192813 192817) (p4 194629 194657 194661 194673)) (pN (p3 194677
  194689 194693) (p4 86178170 380 192521 192525))))
      (pN (pN (pN (p3 192537 192541 192553) (p4 192557 192569 192573 192689))
      (pN (p3 192717 192725 192805) (p4 192813 192817 194629 194633)))
      (pN (pN (p3 194649 194661 194665) (p4 194677 194681 194693 194697))
      (pN (p3 87226746 192525 192529) (p4 192541 192545 192557 192561)))))
      (pN (pN (pN (p6 192573 192577 192689 192813 192817 194649) (pN (p3 194653 194665 194669)
      (p4 194681 194685 194701 194741))) (pN (pN (p3 88275322 380 192517)
      (p4 192525 192537 192541 192545)) (pN (p3 192549 192553 192565)
      (p4 192573 192689 192749 192757))))
      (pN (pN (pN (p3 192765 192805 192809) (p4 192817 194629 194633 194649))
      (pN (p3 194653 194657 194661) (p4 194673 194681 194693 194701)))
      (pN (pN (p3 194741 89323898 380) (p4 192517 192521 192529 192533))
      (pN (p3 192541 192545 192553) (p4 192557 192565 192569 192577))))))
      (pN (pN (pN (pN (p6 192717 192725 192749 192757 192765 194633) (pN (p3 194649 194653 194661)
      (p4 194665 194673 194677 194685))) (pN (pN (p3 194689 194697 194741)
      (p4 194777 90372474 380 192517)) (pN (p3 192525 192529 192537)
      (p4 192541 192549 192553 192561))))
      (pN (pN (pN (p3 192565 192573 192577) (p4 192689 192749 192757 192765))
      (pN (p3 194629 194633 194649) (p4 194657 194661 194669 194673)))
      (pN (pN (p3 194681 194685 194693) (p4 194697 91421050 380 192521))
      (pN (p3 192529 192537 192541) (p4 192545 192565 192569 192573)))))
      (pN (pN (pN (pN (p3 192717 192725 194649) (p4 194653 194657 194665 194673))
      (pN (p3 194681 194685 194689) (p4 194697 194701 194777 92469626)))
      (pN (pN (p3 192521 192533 192541) (p4 192553 192561 192573 192717))
      (pN (p3 192725 194629 194633) (p4 194649 194653 194657 194665))))
      (pN (pN (pN (p3 194669 194673 194677) (p4 194685 194689 194693 194701))
      (pN (p3 194777 93518202 380) (p4 192517 192529 192537 192549)))
      (pN (pN (p3 192557 192569 192577) (p4 192749 192757 192765 192869))
      (pN (p3 194633 194649 194661) (p4 194669 194681 194689 194741))))))))
def dom216Post21TreeR : PrimTree :=
    (pN (pN (pN (pN (pN (pN (p6 194777 94566778 192529 192533 192549 192553)
    (pN (p3 192569 192573 192801) (p4 192869 192873 194649 194657)))
    (pN (pN (p3 194669 194677 194689) (p4 194697 95615354 380 192521)) (pN (p3 192525 192529 192533)
    (p4 192541 192545 192549 192553))))
    (pN (pN (pN (p3 192561 192565 192569) (p4 192573 192689 192717 192725))
    (pN (p3 192873 194633 194649) (p4 194661 194669 194681 194689)))
    (pN (pN (p3 194741 194777 96663930) (p4 380 192517 192529 192537)) (pN (p3 192549 192557 192569)
    (p4 192577 192749 192757 192765))))) (pN (pN (pN (p6 192801 192869 192881 194629 194633 194649)
    (pN (p3 194653 194657 194665) (p4 194669 194673 194677 194685)))
    (pN (pN (p3 194689 194693 194697) (p4 97712506 388 396 400)) (pN (p3 404 412 428)
    (p4 436 440 444 452)))) (pN (pN (pN (p3 456 460 464) (p4 196621 196653 196785 196917))
    (pN (p3 196921 196925 196941) (p4 198661 198665 198705 198725)))
    (pN (pN (p3 198729 198793 198797) (p4 198861 198869 198873 198893))
    (pN (p3 198901 198909 198945) (p4 198953 198957 198973 198977))))))
    (pN (pN (pN (pN (p6 198989 198993 198997 199005 199017 199029) (pN (p3 200709 200713 200717)
    (p4 200725 200729 200745 200749))) (pN (pN (p3 200757 200765 200769)
    (p4 200881 200909 200917 200941)) (pN (p3 200949 200957 201005)
    (p4 201009 201013 201021 201025))))
    (pN (pN (pN (p3 201029 201041 201045) (p4 201049 201057 201061 201065))
    (pN (p3 201073 201077 202757) (p4 202761 202765 202809 202821)))
    (pN (pN (p3 202825 202889 202893) (p4 202929 202957 202965 202969))
    (pN (p3 202989 202997 203005) (p4 203045 203053 203057 203061)))))
    (pN (pN (pN (pN (p3 203065 203073 203077) (p4 203081 203085 203093 203097))
    (pN (p3 203109 203113 203117) (p4 204813 204861 204869 204873)))
    (pN (pN (p3 204937 204941 204977) (p4 205017 205097 205105 205109))
    (pN (p3 205129 205137 205141) (p4 205145 205161 205169 206853))))
    (pN (pN (pN (p3 206857 206869 206873) (p4 206889 206893 206909 206917))
    (pN (p3 206921 206985 206989) (p4 207053 207061 207065 207085)))
    (pN (pN (p3 207093 207101 207137) (p4 207141 207145 207149 207161))
    (pN (p3 207165 207173 207189) (p4 207193 207201 207205 207209)))))))
    (pN (pN (pN (pN (pN (p6 208901 208909 209073 209133 209141 209149) (pN (p3 209185 209189 209193)
    (p4 209201 209209 209217 209225))) (pN (pN (p3 209241 209245 209253)
    (p4 209257 209261 209265 209269)) (pN (p3 211013 211033 211037) (p4 211041
  211045 211049 211053)))) (pN (pN (pN (p3 211057 211061 211065) (p4 211069 211073 211077 211085))
      (pN (p3 211125 211161 213237) (p4 215245 215277 217265 217301)))
      (pN (pN (p3 217341 217369 219141) (p4 219145 219153 219205 219209))
      (pN (p3 219273 219277 219341) (p4 219349 219353 219373 219381)))))
      (pN (pN (pN (p6 219389 219425 219433 219437 219445 219449) (pN (p3 219453 219469 219477)
      (p4 219485 219497 219509 221189))) (pN (pN (p3 221193 221197 221209)
      (p4 221225 221229 221245 221249)) (pN (p3 221361 221389 221397)
      (p4 221421 221429 221437 221481))))
      (pN (pN (pN (p3 221489 221493 221497) (p4 221505 221521 221525 221529))
      (pN (p3 221537 221541 221545) (p4 221553 221557 223237 223241)))
      (pN (pN (p3 223245 223257 223301) (p4 223305 223369 223373 223409))
      (pN (p3 223437 223445 223449) (p4 223469 223477 223485 223525))))))
      (pN (pN (pN (pN (p6 223529 223533 223541 223557 223565 223573) (pN (p3 223577 223589 223593)
      (p4 223597 225293 225309 225349))) (pN (pN (p3 225353 225417 225421)
      (p4 225457 225497 225573 225581)) (pN (p3 225585 225593 225597)
      (p4 225609 225613 225617 225621))))
      (pN (pN (pN (p3 225625 225641 225649) (p4 227333 227337 227349 227353))
      (pN (p3 227361 227369 227373) (p4 227389 227393 227397 227401)))
      (pN (pN (p3 227465 227469 227533) (p4 227541 227545 227565 227573))
      (pN (p3 227581 227617 227629) (p4 227633 227637 227645 227649)))))
      (pN (pN (pN (pN (p3 227653 227665 227669) (p4 227673 227681 227685 227689))
      (pN (p3 229389 229413 229553) (p4 229665 229669 229673 229681)))
      (pN (pN (p3 229693 229697 229701) (p4 229705 229721 229725 229733))
      (pN (p3 229737 229741 229745) (p4 229749 231433 231465 231493))))
      (pN (pN (pN (p3 231497 231561 231565) (p4 231629 231637 231641 231737))
      (pN (p3 231745 231753 233541) (p4 233545 233565 233573 233581)))
      (pN (pN (p3 233589 233597 233605) (p4 233653 235589 235593 235621))
      (pN (p3 235637 235653 237637) (p4 237641 237685 239685 239689))))))))
def dom216Post21Tree : PrimTree := .node dom216Post21TreeL dom216Post21TreeR
theorem dom216Setup2Tree_check : (checkPrimTree 117 0 0 dom216Setup2Tree).1 = true ∧
    (checkPrimTree 117 0 0 dom216Setup2Tree).2.2 = 0 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem dom216Setup3Tree_check : (checkPrimTree 117 0 0 dom216Setup3Tree).1 = true ∧
    (checkPrimTree 117 0 0 dom216Setup3Tree).2.2 = 0 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem dom216Setup4Tree_check : (checkPrimTree 117 0 0 dom216Setup4Tree).1 = true ∧
    (checkPrimTree 117 0 0 dom216Setup4Tree).2.2 = 0 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem dom216Post21Tree_check : (checkPrimTree 117 0 dom216Post21SMask dom216Post21Tree).1 = true ∧
    (checkPrimTree 117 0 dom216Post21SMask dom216Post21Tree).2.2 = 21 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem dom216Post21SMask_outside (u : ℕ) (hu : u < 118) (hm : dom216Post21SMask.testBit u = true) :
    73 ≤ u ∧ u < 73 + 45 := by
  revert hm hu u; decide +kernel

abbrev uR1 : Wire 118 := ⟨3, by decide⟩
abbrev uR2 : Wire 118 := ⟨2, by decide⟩
abbrev uR3 : Wire 118 := ⟨1, by decide⟩
abbrev uR4 : Wire 118 := ⟨64, by decide⟩

def fR1 (b : Fin 2) : Wire 118 :=
  if b.val = 0 then ⟨35, by decide⟩ else ⟨36, by decide⟩

def fR2 (b : Fin 3) : Wire 118 :=
  if b.val = 0 then ⟨45, by decide⟩
  else if b.val = 1 then ⟨18, by decide⟩
  else ⟨37, by decide⟩

def fR3 (b : Fin 3) : Wire 118 :=
  if b.val = 0 then ⟨17, by decide⟩
  else if b.val = 1 then ⟨18, by decide⟩
  else ⟨55, by decide⟩

def fR4 (b : Fin 2) : Wire 118 :=
  if b.val = 0 then ⟨65, by decide⟩ else ⟨66, by decide⟩

theorem hfB_R1 : ∀ b : Fin 2, (fR1 b).val < 39 ∧ (fR1 b).val ≠ uR1.val := by decide
theorem hfB_R2 : ∀ b : Fin 3, (fR2 b).val < 46 ∧ (fR2 b).val ≠ uR2.val := by decide
theorem hfB_R3 : ∀ b : Fin 3, (fR3 b).val < 56 ∧ (fR3 b).val ≠ uR3.val := by decide
theorem hfB_R4 : ∀ b : Fin 2, (fR4 b).val < 67 ∧ (fR4 b).val ≠ uR4.val := by decide

def tR1 : PrimTree := tRouterSpec uR1 fR1 39 2 le_rfl
def tR2 : PrimTree := tRouterSpec uR2 fR2 46 3 le_rfl
def tR3 : PrimTree := tRouterSpec uR3 fR3 56 3 le_rfl
def tR4 : PrimTree := tRouterSpec uR4 fR4 67 2 le_rfl

def tDom1 : PrimTree := .node .empty dom216PreTree
def tDom2 : PrimTree := .node tDom1 tR1
def tDom3 : PrimTree := .node tDom2 dom216Setup2Tree
def tDom4 : PrimTree := .node tDom3 tR2
def tDom5 : PrimTree := .node tDom4 dom216Setup3Tree
def tDom6 : PrimTree := .node tDom5 tR3
def tDom7 : PrimTree := .node tDom6 dom216Setup4Tree
def tDom8 : PrimTree := .node tDom7 tR4
def tDom9 : PrimTree := .node tDom8 dom216Post21Tree

theorem evalStrict_empty (M mx : ℕ) (cols : CT) : evalStrict M mx cols .empty = cols := by
  cases cols <;> rfl

theorem evalStrict_node (M mx : ℕ) (cols : CT) (l r : PrimTree) : evalStrict M mx cols (.node l r) =
    evalStrict M mx (evalStrict M mx cols l) r := by
  dsimp only [evalStrict]
  cases evalStrict M mx cols l <;> rfl

def checkZeroRange (cols : CT) (vmask base : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => Nat.beq (getCT 7 cols (base + k) &&& vmask) 0 && checkZeroRange cols vmask base k

theorem checkZeroRange_sound (cols : CT) (vmask base d2 : ℕ) (hvm : vmask.testBit d2 = true) :
    ∀ (k : ℕ), checkZeroRange cols vmask base k = true →
      ∀ j, base ≤ j → j < base + k → (getCT 7 cols j).testBit d2 = false
  | 0, _, j, hj1, hj2 => absurd hj2 (by omega)
  | k + 1, hchk, j, hj1, hj2 => by
      rcases Bool.and_eq_true_iff.mp hchk with ⟨heq, hrest⟩
      by_cases hjk : j = base + k
      · subst hjk
        have h := congrArg (fun x ↦ x.testBit d2) (Nat.beq_eq.mp heq)
        simpa [Nat.testBit_and, hvm] using h
      · exact checkZeroRange_sound cols vmask base d2 hvm k hrest j hj1 (by omega)

def checkDisjPair (cols : CT) (vmask a b : ℕ) : Bool :=
    Nat.beq (getCT 7 cols a &&& getCT 7 cols b &&& vmask) 0
theorem checkDisjPair_sound (cols : CT) (vmask a b d2 : ℕ) (hchk : checkDisjPair cols vmask a b =
    true) (hvm : vmask.testBit d2 = true) : ¬ ((getCT 7 cols a).testBit d2 = true ∧
    (getCT 7 cols b).testBit d2 = true) := by
  rintro ⟨ha, hb⟩
  have h := congrArg (fun x ↦ x.testBit d2) (Nat.beq_eq.mp hchk)
  simp [Nat.testBit_and, ha, hb, hvm] at h

def checkDom216All (nn : ℕ) : Bool :=
  let mx := (coordState 18).2.1
  let vm := ltMask 196608
  let c1 := evalStrict 117 mx (initDomCT nn) dom216PreTree
  let c3 := evalStrict 117 mx (evalStrict 117 mx c1 tR1) dom216Setup2Tree
  let c5 := evalStrict 117 mx (evalStrict 117 mx c3 tR2) dom216Setup3Tree
  let c7 := evalStrict 117 mx (evalStrict 117 mx c5 tR3) dom216Setup4Tree
  let c8 := evalStrict 117 mx c7 tR4
  let c9 := evalStrict 117 mx c8 dom216Post21Tree
  (checkDisjPair c1 vm 35 36 && checkZeroRange c1 vm 38 7) &&
  (checkDisjPair c3 vm 45 18 && checkDisjPair c3 vm 45 37 &&
    checkDisjPair c3 vm 18 37 && checkZeroRange c3 vm 38 1 && checkZeroRange c3 vm 46 8) &&
  (checkDisjPair c5 vm 17 18 && checkDisjPair c5 vm 17 55 &&
    checkDisjPair c5 vm 18 55 && checkZeroRange c5 vm 38 1 && checkZeroRange c5 vm 56 8) &&
  (checkDisjPair c7 vm 65 66 && checkZeroRange c7 vm 38 1 && checkZeroRange c7 vm 67 6) &&
  checkZeroRange c8 vm 73 45 &&
  checkColsMask 22 96 c9 (expEvenOctCols nn mx (coordState 18).2.2) vm

theorem checkDom216All_0 : checkDom216All 0 = true := by decide +kernel
theorem checkDom216All_1 : checkDom216All 1 = true := by decide +kernel

theorem checkDom216All_nn (b : Bool) : checkDom216All (if b then 1 else 0) = true := by
  cases b
  · exact checkDom216All_0
  · exact checkDom216All_1

theorem band_left {a b : Bool} (h : (a && b) = true) : a = true := (Bool.and_eq_true a b).mp h |>.1
theorem band_right {a b : Bool} (h : (a && b) = true) : b = true := (Bool.and_eq_true a b).mp h |>.2
theorem tDom9_eq : tDom9 = .node tDom8 dom216Post21Tree := rfl

theorem dom216_stage_facts (β : Fin 118 → ZMod 2)
    (hd2 : natOfZModBits 18 (fun b ↦ β ⟨1 + b.val, dom216_1add_lt b⟩) < 196608)
    (hZero : ∀ u : Fin 118, 19 ≤ u.val → β u = 0) :
    let x0 := natOfZModBits 118 β
    let s1 := evalPrimTree 117 x0 tDom1
    let s3 := evalPrimTree 117 x0 tDom3
    let s5 := evalPrimTree 117 x0 tDom5
    let s7 := evalPrimTree 117 x0 tDom7
    let s8 := evalPrimTree 117 x0 tDom8
    let s9 := evalPrimTree 117 x0 tDom9
    let p := evenOctIdxT10K (β ⟨0, by decide⟩ == 1)
      (natOfZModBits 18 (fun b ↦ β ⟨1 + b.val, dom216_1add_lt b⟩))
    (¬(s1.testBit 35 = true ∧ s1.testBit 36 = true) ∧
      (∀ j, 38 ≤ j → j < 45 → s1.testBit j = false)) ∧
    (¬(s3.testBit 45 = true ∧ s3.testBit 18 = true) ∧
      ¬(s3.testBit 45 = true ∧ s3.testBit 37 = true) ∧
      ¬(s3.testBit 18 = true ∧ s3.testBit 37 = true) ∧ s3.testBit 38 = false ∧
      (∀ j, 46 ≤ j → j < 54 → s3.testBit j = false)) ∧
    (¬(s5.testBit 17 = true ∧ s5.testBit 18 = true) ∧
      ¬(s5.testBit 17 = true ∧ s5.testBit 55 = true) ∧
      ¬(s5.testBit 18 = true ∧ s5.testBit 55 = true) ∧ s5.testBit 38 = false ∧
      (∀ j, 56 ≤ j → j < 64 → s5.testBit j = false)) ∧
    (¬(s7.testBit 65 = true ∧ s7.testBit 66 = true) ∧ s7.testBit 38 = false ∧
      (∀ j, 67 ≤ j → j < 73 → s7.testBit j = false)) ∧
    (∀ j, 73 ≤ j → j < 118 → s8.testBit j = false) ∧
    (∀ j : Fin 22, s9.testBit (dom216OutW j).val = dom22Bit p j) := by
  let f18 (b : Fin 18) := β ⟨1 + b.val, dom216_1add_lt b⟩
  set d2 := natOfZModBits 18 f18
  have hd2_262 : d2 < 2 ^ 18 := natOfZModBits_lt 18 _
  have hvm := (testBit_ltMask 196608 d2).trans (decide_eq_true hd2)
  set nn := if β ⟨0, by decide⟩ == 1 then 1 else 0
  have hEv (t : PrimTree) (u : ℕ) (hu : u < 118) := (evalStrict_initDomCT dom216_ge18 dom216_lt128
    t β d2 hd2_262 (fun b ↦ (natOfZModBits_testBit_lt f18 b.isLt).symm) hZero u hu).symm
  have hAll : checkDom216All nn = true := checkDom216All_nn (β ⟨0, by decide⟩ == 1)
  dsimp only [checkDom216All] at hAll
  rw [← evalStrict_empty 117 (coordState 18).2.1 (initDomCT nn)] at hAll
  simp only [← evalStrict_node, Bool.and_eq_true] at hAll
  rcases hAll with ⟨⟨⟨⟨⟨⟨h1d, h1z⟩, ⟨⟨⟨⟨h3d1, h3d2⟩, h3d3⟩, h3z1⟩, h3z2⟩⟩,
    ⟨⟨⟨⟨h5d1, h5d2⟩, h5d3⟩, h5z1⟩, h5z2⟩⟩, ⟨⟨h7d, h7z1⟩, h7z2⟩⟩, h8z⟩, h9c⟩
  have hDP {t a b} (hd : checkDisjPair (evalStrict 117 (coordState 18).2.1 (initDomCT nn) t)
      (ltMask 196608) a b = true) (ha : a < 118 := by decide) (hb : b < 118 := by decide) :=
    (hEv t a ha).symm ▸ (hEv t b hb).symm ▸ checkDisjPair_sound _ _ a b d2 hd hvm
  have hZR {t base k} (hz : checkZeroRange (evalStrict 117 (coordState 18).2.1 (initDomCT nn) t)
      (ltMask 196608) base k = true) (hk : base + k ≤ 118 := by decide) :
      ∀ j, base ≤ j → j < base + k →
        (evalPrimTree 117 (natOfZModBits 118 β) t).testBit j = false := fun j hj1 hj2 ↦
    (hEv t j (by omega)).trans (checkZeroRange_sound _ _ base d2 hvm k hz j hj1 hj2)
  refine ⟨⟨hDP h1d, hZR h1z⟩,
    ⟨hDP h3d1, hDP h3d2, hDP h3d3, (hZR h3z1) 38 le_rfl (by decide), hZR h3z2⟩,
    ⟨hDP h5d1, hDP h5d2, hDP h5d3, (hZR h5z1) 38 le_rfl (by decide), hZR h5z2⟩,
    ⟨hDP h7d, (hZR h7z1) 38 le_rfl (by decide), hZR h7z2⟩, hZR h8z, fun j ↦ ?_⟩
  dsimp only [dom216OutW, dom216OutBase, dom22Bit]
  rw [hEv tDom9 (96 + j.val) (dom216Out_lt j)]
  exact (checkColsMask_sound 22 96 _ _ (ltMask 196608) d2 h9c hvm j.val j.isLt).trans
    ((show nn.beq 1 = (β ⟨0, by decide⟩ == 1) by dsimp only [nn]; cases (β _ == 1) <;> rfl) ▸
      expEvenOctCols_testBit nn (by dsimp only [nn]; split_ifs <;> omega) hd2_262 j.val j.isLt)
/-! ### 5. Assembled `168 T` Forward Normalizer & `216 T` `PopBernDomSplitPkg2` -/

theorem stTree118_zero_of_not_and {n : ℕ} (r : QRegister 118 n) (t : PrimTree)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) {u1 u2 : Wire 118} {a1 a2 : ℕ}
    (hu1 : u1.val = a1) (hu2 : u2.val = a2)
    (hd : ¬((evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a1 = true ∧
            (evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a2 = true))
    (h1 : stTree118 r t st δ (r u1) = 1) : stTree118 r t st δ (r u2) = 0 := by
  rw [stTree118_apply_reg, hu1] at h1
  refine stTree118_eq_zero_of_false r t st δ u2 (hu2.symm ▸ ?_)
  cases ha : (evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a1
  · exact absurd ((bitZMod2_congr ha).symm.trans h1) zero_ne_one
  · exact Bool.eq_false_of_ne_true fun hb ↦ hd ⟨ha, hb⟩

theorem mut2_of_disj {n : ℕ} (r : QRegister 118 n) (t : PrimTree)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (f : Fin 2 → Wire 118)
    (a0 a1 : ℕ) (hf0 : (f ⟨0, by decide⟩).val = a0) (hf1 : (f ⟨1, by decide⟩).val = a1)
    (hd : ¬((evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a0 = true ∧
            (evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a1 = true)) :
    ∀ b1 b2 : Fin 2, b1 ≠ b2 → stTree118 r t st δ (r (f b1)) = 1 →
      stTree118 r t st δ (r (f b2)) = 0 := fun b1 b2 hne h1 ↦ by
  fin_cases b1 <;> fin_cases b2 <;> first
    | exact absurd rfl hne
    | exact stTree118_zero_of_not_and r t st δ hf0 hf1 hd h1
    | exact stTree118_zero_of_not_and r t st δ hf1 hf0 (fun ⟨a, b⟩ ↦ hd ⟨b, a⟩) h1

theorem mut3_of_disj {n : ℕ} (r : QRegister 118 n) (t : PrimTree)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (f : Fin 3 → Wire 118)
    (a0 a1 a2 : ℕ) (hf0 : (f ⟨0, by decide⟩).val = a0) (hf1 : (f ⟨1, by decide⟩).val = a1)
    (hf2 : (f ⟨2, by decide⟩).val = a2)
    (hd01 : ¬((evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a0 = true ∧
              (evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a1 = true))
    (hd02 : ¬((evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a0 = true ∧
              (evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a2 = true))
    (hd12 : ¬((evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a1 = true ∧
              (evalPrimTree 117 (natOfZModBits 118 (fun i ↦ st δ (r i))) t).testBit a2 = true)) :
    ∀ b1 b2 : Fin 3, b1 ≠ b2 → stTree118 r t st δ (r (f b1)) = 1 →
      stTree118 r t st δ (r (f b2)) = 0 := fun b1 b2 hne h1 ↦ by
  let z {u1 u2 x y} := @stTree118_zero_of_not_and n r t st δ u1 u2 x y
  fin_cases b1 <;> fin_cases b2 <;> first
    | exact absurd rfl hne
    | exact z hf0 hf1 hd01 h1
    | exact z hf0 hf2 hd02 h1
    | exact z hf1 hf2 hd12 h1
    | exact z hf1 hf0 (fun h ↦ hd01 h.symm) h1
    | exact z hf2 hf0 (fun h ↦ hd02 h.symm) h1
    | exact z hf2 hf1 (fun h ↦ hd12 h.symm) h1

end QuantumComputation.Specs.PhotochemistrySolution.CoulDomWRouter216
end
end
