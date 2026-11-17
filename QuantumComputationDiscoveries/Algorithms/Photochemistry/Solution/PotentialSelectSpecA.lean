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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage4SplitAlignXor84

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators
noncomputable section
open Operator QProg Matrix QuantumComputation.Specs.PhotochemistrySolution
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat PhotochemistrySolution.XMeasUnld PhotochemistrySolution.XMeasLinearCleanStep
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
abbrev uXorCtrlVec {M n : ℕ} (wLo wHi : Fin M → Wire n) (hNe : ∀ p : Fin M, wHi p ≠ wLo p) :
    Unitary (2 ^ n) := (cnotPairsCircuit (xorCtrlPairsVec wLo wHi hNe M le_rfl)).eval
abbrev uPlaneXorCtrl {M D n : ℕ} (r : PlaneReg M D n) : Unitary (2 ^ n) :=
    uXorCtrlVec (pCtrlLo r) (pCtrlHi r) (hne_Ctrl_HiLo r)
theorem uPlaneXorCtrl_mulVec_ket {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n) :
    (uPlaneXorCtrl r).1.mulVec (ket δ) = ket (planeXorBits r δ) :=
  cnotPairs_xorCtrlVec_mulVec_ket (pCtrlLo r) (pCtrlHi r) (hne_Ctrl_HiLo r)
    (fun _ _ h ↦ pr_ne r fun e ↦ h (Fin.ext (by
      dsimp at e
      omega)))
        (fun _ _ ↦ pr_ne r (by
          dsimp
          omega)) M le_rfl δ
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187

section
set_option exponentiation.threshold 8192
open scoped Matrix.Norms.L2Operator
open DynamicCircuit Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.OvBidir
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactRot34
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectEulerRot32
  QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge
  QuantumComputation.Specs.PhotochemistrySolution.FusedUnembedLGen
  QuantumComputation.Specs.PhotochemistrySolution.UnembedDualBell531
namespace QuantumComputation.Specs.PhotochemistrySolution.DepthArithWalk
set_option maxRecDepth 4096
section FusedRot31Kick3Defs
open ComplexConjugate PhotochemistrySolution.SelectCsa64ProvSpec
  PhotochemistrySolution.SelectGidneyFast PhotochemistrySolution.TargetBScr
  PhotochemistrySolution.DynQromUncompA PhotochemistrySolution.UnembedIdleAncillas
  PhotochemistrySolution.UnembedO3Bridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem hqTop_kick3_gen_31 {scrW scrL m offRefl n : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL) (rSys : QRegister systemQubits_frozen n)
    (rAnc : QRegister (ancWOfScr scrW) n) (hdisj : rSys.DisjointWires rAnc) :
    qspQubitGen (hAncCompact scrW) rAnc ≠ (rSys.concat rAnc hdisj)
    (reflRCleanLGenOff hp hm (Fin.last m)) := by
  exact fun h ↦ locQ_ne_reflRCleanLGenOff hp hm _ ((rSys.concat rAnc hdisj).wires.injective
    ((concat_locAnc_apply_fs rSys rAnc hdisj ⟨34 + scrW + 70,
        by
          unfold ancWOfScr
          omega⟩).trans h))
attribute [local semireducible] fwdCirc wrapDyn
theorem reflAmb_hIC_31 {scrW scrL m offRefl n : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL) (rTot : QRegister (totDimCompactGen scrW) n) : ∀ i j,
    rTot (rLcuLGen hp i) ≠ rTot (reflRCleanLGenOff hp hm j) := fun i j h ↦
    reflHICLGenOff hp hm i j (rTot.wires.injective h)
theorem reflAmb_hCC_31 {scrW scrL m offRefl n : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL) (rTot : QRegister (totDimCompactGen scrW) n) : ∀ j₁ j₂, j₁ ≠
    j₂ → rTot (reflRCleanLGenOff hp hm j₁) ≠ rTot (reflRCleanLGenOff hp hm j₂) := fun j₁ j₂ h hj ↦
    reflHCCLGenOff hp hm j₁ j₂ h (rTot.wires.injective hj)
theorem reflAmb_hIn_31 {scrW scrL m n : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (rTot : QRegister (totDimCompactGen scrW) n) : ∀ i₁ i₂, i₁ ≠ i₂ → rTot (rLcuLGen hp i₁) ≠
    rTot (rLcuLGen hp i₂) := fun i₁ i₂ h hi ↦ reflHInLGen hp i₁ i₂ h (rTot.wires.injective hi)
end FusedRot31Kick3Defs
open ComplexConjugate PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.QubitizationTop
  PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.SelectLcu70Rot32
theorem circuit_sequence_append_eval_kick3_31 {n : ℕ} [NeZero (2 ^ n)]
    (cs₁ cs₂ : List (Circuit n)) : (Circuit.sequence (cs₁ ++ cs₂)).eval =
    (Circuit.sequence cs₂).eval * (Circuit.sequence cs₁).eval := by
  induction cs₁ <;> simp [Circuit.sequence, Circuit.eval_seq, *, mul_assoc]
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
theorem foldFinUnitary_fused_eq_gen {α : Type*} {d : ℕ}
    (R Us X : Unitary d) (V : α → Unitary d) :
    ∀ (k : ℕ) (ang : Fin (k + 1) → α),
      foldFinUnitary (m := k + 1) (fun s ↦ V (ang s) * (X * R * X * Us * R)) =
        V (ang (Fin.last k)) * X * R * X *
          foldFinUnitary (m := k) (fun i ↦ Us * (R * V (ang i.castSucc) * X * R * X)) * Us * R
  | 0, _ => by simp only [foldFinUnitary, mul_one, mul_assoc]
  | k + 1, ang => by
      rw [foldFinUnitary, foldFinUnitary_fused_eq_gen R Us X V k (fun i ↦ ang i.castSucc),
          foldFinUnitary]
      simp only [mul_assoc]
end QuantumComputation.Specs.PhotochemistrySolution.DepthArithWalk
end
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCoreFused
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open scoped Circuit.Notation
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.ZeroNEremSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage4Cluster22Xnor
  PhotochemistrySolution.SplitRouter47_187
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
-- target operators
-- Section 1: Decoded Coordinates, Species Codes, and Inner-Coin Helpers
theorem nucParticle_lt (n : Fin 47) : n.val < 234 := by omega
/-- Canonical nuclear particle index `0..46` inside `Particle = Fin 234`. -/
def nucParticle (n : Fin 47) : Particle_frozen := ⟨n.val, nucParticle_lt n⟩
theorem elecParticle_lt (e : Fin 187) : 47 + e.val < 234 := by omega
/-- Canonical electronic particle index `47..233` inside `Particle = Fin 234`. -/
def elecParticle (e : Fin 187) : Particle_frozen := ⟨47 + e.val, elecParticle_lt e⟩
theorem coordOfReg24_lt (ax : Fin 3) (k : Fin 8) : 8 * ax.val + k.val < 24 := by omega
/-- Decode 3D grid coordinates `(ax : Fin 3) -> Fin 256` from a `24`-bit router port. -/
def coordOfReg24 {n : ℕ} (r24 : QRegister 24 n) (δ : BitAssignment n) : Fin 3 → Fin 256 :=
  fun ax ↦ byteOfBits (fun k : Fin 8 ↦ δ (r24 ⟨8 * ax.val + k.val, coordOfReg24_lt ax k⟩))
/-- Extract 3D grid coordinates of particle `i` from a computational basis index `x`. -/
def sysCoord (x : Fin (2 ^ systemQubits_frozen)) (i : Particle_frozen) : Fin 3 → Fin 256 := fun ax ↦
    (coordinateRegister_frozen i ax).extractIndex x
theorem speciesOfBits2_lt (b0 b1 : ZMod 2) : (if b0 = 1 then 1 else 0) + (if b1 = 1 then 2 else 0) <
    4 := by split_ifs <;> omega
/-- Decode `Fin 4` species code (`0=H, 1=C, 2=N, 3=O`) from two little-endian `ZMod 2` bits. -/
def speciesOfBits2 (b0 b1 : ZMod 2) : Fin 4 :=
  ⟨(if b0 = 1 then 1 else 0) + (if b1 = 1 then 2 else 0), speciesOfBits2_lt b0 b1⟩
/-- Real inner-coin expectation `(isScreen, isNN, sp1, sp2, nucA, nucB, elecA, elecB) -> ℝ`. -/
abbrev PotExpectFn : Type :=
    Bool → Bool → Fin 4 → Fin 4 → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    (Fin 3 → Fin 256) → ℝ
theorem potWire_out_lt {N : ℕ} (j : Fin N) (_h0 : ¬ j.val = 0) (h1 : j.val < 9) :
    32 + (j.val - 1) < 40 := by omega
theorem potWire_nucLo_lt {N : ℕ} (j : Fin N) (h1 : ¬ j.val < 9) (h2 : j.val < 33) : j.val - 9 <
    24 := by omega
theorem potWire_nucHi_lt {N : ℕ} (j : Fin N) (h2 : ¬ j.val < 33) (h3 : j.val < 57) : j.val - 33 <
    24 := by omega
theorem potWire_elecLo_lt {N : ℕ} (j : Fin N) (h3 : ¬ j.val < 57) (h4 : j.val < 81) : j.val - 57 <
    24 := by omega
theorem potWire_elecHi_lt {N : ℕ} (j : Fin N) (h4 : ¬ j.val < 81) (h5 : j.val < 105) : j.val - 81 <
    24 := by omega
theorem potWire_inner_lt {N : ℕ} (j : Fin N) (h5 : ¬ j.val < 105) (h6 : j.val < 146) : j.val - 105 <
    41 := by omega
theorem potWire_clean_lt {Wp : ℕ} (hWp : Wp ≤ 690) (j : Fin (146 + Wp)) (h6 : ¬ j.val < 146) :
    j.val - 146 < 690 := by omega
/--
Wire map for `rPotZeroNErem Wp hWp`:
- `0`: `wLocQLayout` (`7297`),
- `1..8`: `rOut40Layout 32..39` (`5747..5754`: `isScreen, isPot, isKin, isNN, sp1[2], sp2[2]`),
- `9..32`: `rBufLo rNucLayout` (`5755..5778`, `NucPortA`),
- `33..56`: `rBufHi rNucLayout` (`5779..5802`, `NucPortB`),
- `57..80`: `rBufLo rElecLayout` (`5851..5874`, `ElecPortA`),
- `81..104`: `rBufHi rElecLayout` (`5875..5898`, `ElecPortB`),
- `105..145`: `rInner41Layout` (`7256..7296`, all `41` uniform inner coin bits),
- `146..145+Wp`: `rClean690Layout 0..Wp-1` (`[5680..5712]` and `[5947..6082+wIn]`).
-/
def potZeroNEremWireFn (Wp : ℕ) (hWp : Wp ≤ 690) (j : Fin (146 + Wp)) : Wire dLayout :=
    if h0 : j.val = 0 then wLocQLayout else if h1 : j.val < 9 then rOut40Layout ⟨32 + (j.val - 1),
    potWire_out_lt j h0 h1⟩ else if h2 : j.val < 33 then rBufLo rNucLayout ⟨j.val - 9,
    potWire_nucLo_lt j h1 h2⟩ else if h3 : j.val < 57 then rBufHi rNucLayout ⟨j.val - 33,
    potWire_nucHi_lt j h2 h3⟩ else if h4 : j.val < 81 then rBufLo rElecLayout ⟨j.val - 57,
    potWire_elecLo_lt j h3 h4⟩ else if h5 : j.val < 105 then rBufHi rElecLayout ⟨j.val - 81,
    potWire_elecHi_lt j h4 h5⟩ else if h6 : j.val < 146 then rInner41Layout ⟨j.val - 105,
    potWire_inner_lt j h5 h6⟩ else rClean690Layout ⟨j.val - 146, potWire_clean_lt hWp j h6⟩
theorem val_potZeroNEremWireFn {Wp : ℕ} (hWp : Wp ≤ 690) (j : Fin (146 + Wp)) :
    (potZeroNEremWireFn Wp hWp j).val = if j.val = 0 then 7297 else if j.val < 57 then 5746 +
    j.val else if j.val < 105 then 5851 + (j.val - 57) else if j.val < 146 then 7256 +
    (j.val - 105) else if j.val < 179 then 5680 + (j.val - 146) else 5947 + (j.val - 179) := by
  have hN (k) : (rNucLayout k).val = (nucRouterWireFn k).val := rfl
  have hE (k) : (rElecLayout k).val = (elecRouterWireFn k).val := rfl
  dsimp only [potZeroNEremWireFn, rBufLo, rBufHi]
  split_ifs <;> simp only [val_wLocQLayout, val_rOut40Layout, hN, hE, val_nucRouterWireFn,
    val_elecRouterWireFn, val_rInner41Layout, val_rClean690Layout] <;> (try dsimp) <;>
        (try split_ifs) <;> omega
/-- Linear left inverse of `(potZeroNEremWireFn Wp hWp ·).val`. -/
def invPotZeroNErem (w : ℕ) : ℕ :=
    if w = 7297 then 0 else if w < 5715 then 146 + (w - 5680) else if w < 5810 then w -
    5746 else if w < 5910 then 57 + (w - 5851) else if w < 7000 then 179 + (w - 5947) else 105 +
    (w - 7256)
theorem invPotZeroNErem_val {Wp : ℕ} (hWp : Wp ≤ 690) (j : Fin (146 + Wp)) :
    invPotZeroNErem (potZeroNEremWireFn Wp hWp j).val = j.val := by
  rw [val_potZeroNEremWireFn]
  split_ifs <;> dsimp only [invPotZeroNErem] <;> split_ifs <;> omega
/-- Complete `(146 + Wp)`-wire `Zero-NErem` Stage-4 potential register on `dLayout`. -/
def rPotZeroNErem (Wp : ℕ) (hWp : Wp ≤ 690) : QRegister (146 + Wp) dLayout :=
  ⟨⟨potZeroNEremWireFn Wp hWp, fun a b h ↦ Fin.ext (by
    rw [← invPotZeroNErem_val hWp a, ← invPotZeroNErem_val hWp b, h])⟩⟩
theorem potIdx0_lt {W : ℕ} : 0 < 146 + W := by omega
theorem potIdx1_lt {W : ℕ} : 1 < 146 + W := by omega
theorem potIdx2_lt {W : ℕ} : 2 < 146 + W := by omega
theorem potIdx3_lt {W : ℕ} : 3 < 146 + W := by omega
theorem potIdx4_lt {W : ℕ} : 4 < 146 + W := by omega
theorem potIdx5_lt {W : ℕ} : 5 < 146 + W := by omega
theorem potIdx6_lt {W : ℕ} : 6 < 146 + W := by omega
theorem potIdx7_lt {W : ℕ} : 7 < 146 + W := by omega
theorem potIdx8_lt {W : ℕ} : 8 < 146 + W := by omega
theorem potBlkNucA_le {W : ℕ} : 9 + 24 ≤ 146 + W := by omega
theorem potBlkNucB_le {W : ℕ} : 33 + 24 ≤ 146 + W := by omega
theorem potBlkElecA_le {W : ℕ} : 57 + 24 ≤ 146 + W := by omega
theorem potBlkElecB_le {W : ℕ} : 81 + 24 ≤ 146 + W := by omega
theorem potBlkCoin41_le {W : ℕ} : 105 + 41 ≤ 146 + W := by omega
theorem potBlkWork_le {W : ℕ} : 146 + W ≤ 146 + W := le_rfl
abbrev wPotLocQ {W n : ℕ} (r : QRegister (146 + W) n) : Wire n := r ⟨0, potIdx0_lt⟩
abbrev wPotIsScreen {W n : ℕ} (r : QRegister (146 + W) n) : Wire n := r ⟨1, potIdx1_lt⟩
abbrev wPotIsPot {W n : ℕ} (r : QRegister (146 + W) n) : Wire n := r ⟨2, potIdx2_lt⟩
abbrev wPotIsKin {W n : ℕ} (r : QRegister (146 + W) n) : Wire n := r ⟨3, potIdx3_lt⟩
abbrev wPotIsNN {W n : ℕ} (r : QRegister (146 + W) n) : Wire n := r ⟨4, potIdx4_lt⟩
abbrev wPotSp1B0 {W n : ℕ} (r : QRegister (146 + W) n) : Wire n := r ⟨5, potIdx5_lt⟩
abbrev wPotSp1B1 {W n : ℕ} (r : QRegister (146 + W) n) : Wire n := r ⟨6, potIdx6_lt⟩
abbrev wPotSp2B0 {W n : ℕ} (r : QRegister (146 + W) n) : Wire n := r ⟨7, potIdx7_lt⟩
abbrev wPotSp2B1 {W n : ℕ} (r : QRegister (146 + W) n) : Wire n := r ⟨8, potIdx8_lt⟩
abbrev rPotNucA {W : ℕ} {n : ℕ} (r : QRegister (146 + W) n) : QRegister 24 n :=
    r.compose (QRegister.block 9 24 potBlkNucA_le)
abbrev rPotNucB {W : ℕ} {n : ℕ} (r : QRegister (146 + W) n) : QRegister 24 n :=
    r.compose (QRegister.block 33 24 potBlkNucB_le)
abbrev rPotElecA {W : ℕ} {n : ℕ} (r : QRegister (146 + W) n) : QRegister 24 n :=
    r.compose (QRegister.block 57 24 potBlkElecA_le)
abbrev rPotElecB {W : ℕ} {n : ℕ} (r : QRegister (146 + W) n) : QRegister 24 n :=
    r.compose (QRegister.block 81 24 potBlkElecB_le)
abbrev rPotCoin41 {W : ℕ} {n : ℕ} (r : QRegister (146 + W) n) : QRegister 41 n :=
    r.compose (QRegister.block 105 41 potBlkCoin41_le)
abbrev rPotWork {W : ℕ} {n : ℕ} (r : QRegister (146 + W) n) : QRegister W n :=
  r.compose (QRegister.block 146 W potBlkWork_le)
/-- Phase bit of a `Stage4ZeroNEremPotOracle` read from `r : QRegister (146 + W) n`. -/
abbrev potOracleBitEval {W : ℕ} {n : ℕ} (phaseBit : Bool → Bool → Fin 4 → Fin 4 →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    BitAssignment 41 → ZMod 2) (r : QRegister (146 + W) n) (δ : BitAssignment n) : ZMod 2 :=
    phaseBit (δ (wPotIsScreen r) == 1) (δ (wPotIsNN r) == 1) (speciesOfBits2 (δ (wPotSp1B0 r))
    (δ (wPotSp1B1 r))) (speciesOfBits2 (δ (wPotSp2B0 r)) (δ (wPotSp2B1 r)))
    (coordOfReg24 (rPotNucA r) δ) (coordOfReg24 (rPotNucB r) δ) (coordOfReg24 (rPotElecA r) δ)
    (coordOfReg24 (rPotElecB r) δ) (fun k ↦ δ (rPotCoin41 r k))
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

namespace QuantumComputation.Specs.PhotochemistrySolution.Word73PotPool
theorem finBitsVal_testBit : ∀ {B : ℕ} (f : Fin B → ZMod 2) (j : Fin B),
    f j = if (finBitsVal f).testBit j.val then 1 else 0
  | 0, _, j => Fin.elim0 j
  | B + 1, f, j => Fin.cases (by
      change f 0 = if ((f 0).val + 2 * finBitsVal _).testBit 0 = true then 1 else 0
      rcases DynCircExt.bit_cases (f 0) with h | h <;>
        simp [h, Nat.testBit_zero, Nat.add_mul_mod_self_left]
      rfl)
      (fun k ↦ by
        have := ZMod.val_lt (f 0)
        change f k.succ = if ((f 0).val + 2 * finBitsVal _).testBit (k.val + 1) = true then 1 else 0
        rw [Nat.testBit_succ, show ((f 0).val + 2 * finBitsVal (fun i : Fin B ↦ f i.succ)) / 2 =
          finBitsVal (fun i : Fin B ↦ f i.succ) by omega]
        exact finBitsVal_testBit (fun i ↦ f i.succ) k) j
end QuantumComputation.Specs.PhotochemistrySolution.Word73PotPool

namespace QuantumComputation.Specs.PhotochemistrySolution.CoinWrap
open scoped Circuit.Notation
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.DynQromUncompA PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.SubspaceMbu
open PhotochemistrySolution.Stage1Opt41Single
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1Opt41TwoWrap (coe_mul_u_tw
    coe_one_u_tw ifp_tw ifn_tw xorDstK xorDstK_outside xorDstK_dst)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg ket matrix_ext_ket
    cleanProj cleanProj_mulVec_ket)
/-- `wrapDyn` circuit (`4 * p.numAnd` `T`-gates, `0` `.TOFF`) with linear fanout `outs40`. -/
def pCoinWrap (K : ℕ) (p : ComputeProg (41 + K)) (outs40 : Fin 40 → ℕ) {Var : Type} {n : ℕ}
    (v : Var) (r : QRegister (81 + K) n) : DynamicCircuit Var n :=
  wrapDyn v (mapCPSW (rCoinInner K r) p) (.circuit (cXorMaskCoin K outs40 r))
/-- Self-inverse `40`-wire XOR unitary induced by `(p, outs40)` on `QRegister (81 + K) n`. -/
def uCoinWrap (K : ℕ) (p : ComputeProg (41 + K)) (outs40 : Fin 40 → ℕ) {n : ℕ} [NeZero (2 ^ n)]
    (r : QRegister (81 + K) n) : Unitary (2 ^ n) :=
    (fwdCirc (mapCPSW (rCoinInner K r) p)).eval⁻¹ * (cXorMaskCoin K outs40 r).eval *
    (fwdCirc (mapCPSW (rCoinInner K r) p)).eval
theorem uCoinWrap_inv (K : ℕ) (p : ComputeProg (41 + K)) (outs40 : Fin 40 → ℕ) {n : ℕ}
    [NeZero (2 ^ n)] (r : QRegister (81 + K) n) : (uCoinWrap K p outs40 r)⁻¹ =
    uCoinWrap K p outs40 r := by
  refine mul_left_cancel ((mul_inv_cancel (uCoinWrap K p outs40 r)).trans ?_.symm)
  simp only [uCoinWrap, mul_assoc, mul_inv_cancel_left]
  rw [← mul_assoc (cXorMaskCoin K outs40 r).eval, cXorMaskCoin_sq, one_mul, inv_mul_cancel]
/-- Output `40`-bit function evaluated from `p.fwdBits` and parity masks `outs40`. -/
def coinWrapOutFn (K : ℕ) (p : ComputeProg (41 + K)) (outs40 : Fin 40 → ℕ)
    (α : BitAssignment (81 + K)) (j : Fin 40) : ZMod 2 :=
    maskParity (outs40 j) (p.fwdBits (fun i : Fin (41 + K) ↦ α (innerIdxCoin K i))) (41 + K) le_rfl
theorem ket_uCoinWrap_all (K : ℕ) (p : ComputeProg (41 + K)) (outs40 : Fin 40 → ℕ) {n : ℕ}
    [NeZero (2 ^ n)] (r : QRegister (81 + K) n) (β : BitAssignment n) :
    (uCoinWrap K p outs40 r).1.mulVec (ket β) = ket (xorDstK (rCoinOut40 K r)
    (coinWrapOutFn K p outs40 (fun u ↦ β (r u))) 40 Nat.le.refl β) := by
  let q := mapCPSW (rCoinInner K r) p
  let g := coinWrapOutFn K p outs40 (fun u ↦ β (r u))
  have hNo (α k) := xorDstK_outside (rCoinOut40 K r) g 40 Nat.le.refl α (innerCoin_ne_out40 K r k)
  dsimp only [uCoinWrap]
  rw [coe_mul_u_tw, coe_mul_u_tw, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    fwdCirc_mulVec_ket, ket_cXorMaskCoin,
    show (fun j : Fin 40 ↦ maskParity (outs40 j) (fun i ↦ q.fwdBits β (rCoinInner K r i))
      (41 + K) le_rfl) = g from congrArg (fun f j ↦ maskParity (outs40 j) f (41 + K) le_rfl)
      (funext (fwdBits_mapCPSW_inside _ p β)),
    show xorDstK (rCoinOut40 K r) g 40 Nat.le.refl (q.fwdBits β) =
      q.fwdBits (xorDstK (rCoinOut40 K r) g 40 Nat.le.refl β) from funext fun w ↦ by
      by_cases hw : ∃ i, w = rCoinInner K r i
      · rcases hw with ⟨i, rfl⟩
        rw [hNo, fwdBits_mapCPSW_inside, fwdBits_mapCPSW_inside,
          show (fun k ↦ xorDstK (rCoinOut40 K r) g 40 Nat.le.refl β (rCoinInner K r k)) =
              _ from funext (hNo β)]
      · rw [fwdBits_mapCPSW_outside _ _ _ fun i e ↦ hw ⟨i, e⟩]
        rcases Classical.em (∃ j, w = rCoinOut40 K r j) with ⟨j, rfl⟩ | ho
        · rw [xorDstK_dst, xorDstK_dst, fwdBits_mapCPSW_outside _ _ β fun i e ↦ hw ⟨i, e⟩]
        · rw [xorDstK_outside _ _ _ _ _ fun j e ↦ ho ⟨j, e⟩,
            xorDstK_outside _ _ _ _ _ fun j e ↦ ho ⟨j, e⟩,
            fwdBits_mapCPSW_outside _ _ β fun i e ↦ hw ⟨i, e⟩],
    show ket (q.fwdBits _) =
        (fwdCirc q).eval.1.mulVec (ket _) from (fwdCirc_mulVec_ket q _).symm,
    Matrix.mulVec_mulVec, ← coe_mul_u_tw, inv_mul_cancel, coe_one_u_tw, Matrix.one_mulVec]
theorem comm_uCoinWrap_clean (K : ℕ) (p : ComputeProg (41 + K)) (outs40 : Fin 40 → ℕ) {n : ℕ}
    [NeZero (2 ^ n)] (r : QRegister (81 + K) n) : (uCoinWrap K p outs40 r).1 *
    (rCoinClean K r).basisOutcomeProjector 0 = (rCoinClean K r).basisOutcomeProjector 0 *
    (uCoinWrap K p outs40 r).1 := by
  refine matrix_ext_ket fun β ↦ ?_
  have hSame (k) : xorDstK (rCoinOut40 K r) (coinWrapOutFn K p outs40 (fun u ↦ β (r u)))
      40 Nat.le.refl β (rCoinClean K r k) = β (rCoinClean K r k) :=
    xorDstK_outside _ _ _ _ _ fun j e ↦ absurd (congrArg Fin.val (r.wires.injective e))
      (by
        simp only [QRegister.block_apply_val]
        omega)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero, ket_uCoinWrap_all,
    PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases h0 : ∀ k, β (rCoinClean K r k) = 0
  · rw [ifp_tw h0, ket_uCoinWrap_all, ifp_tw fun k ↦ (hSame k).trans (h0 k)]
  · rw [ifn_tw h0, Matrix.mulVec_zero, ifn_tw fun h' ↦ h0 fun k ↦ (hSame k).symm.trans (h' k)]
theorem subspaceStep_circuit_cw {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (c : Circuit n) (A : Operator (2 ^ n)) : SubspaceStep A (c.eval.1 * A)
    (.circuit c : DynamicCircuit Var n) := Stage1Opt41TwoWrap.subspaceStep_circuit_tw c A
theorem cleanWorkStep_pCoinWrap (K : ℕ) (p : ComputeProg (41 + K)) (s : Finset (Wire (41 + K)))
    (outs40 : Fin 40 → ℕ) (hs : ∀ u ∈ s, 41 ≤ u.val) (hValid : p.ValidProg ∅ s) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (r : QRegister (81 + K) n) :
    CleanWorkStep (rCoinClean K r) (uCoinWrap K p outs40 r) (pCoinWrap K p outs40 v r) := by
  let rI := rCoinInner K r; let q := mapCPSW rI p;
  let P := (rCoinClean K r).basisOutcomeProjector 0; let sImg := s.image rI.wires
  have hAbs : cleanProj sImg * P = P := matrix_ext_ket fun β ↦ by
    rw [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
    split_ifs with h0
    · rw [cleanProj_mulVec_ket, ite_eq_left_iff.mpr fun hNot ↦ (hNot fun w hw ↦ by
        rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
        exact (congrArg β (innerCoin_ge41_eq_clean K r u (hs u hu))).trans (h0 _)).elim]
    · exact Matrix.mulVec_zero _
  have hComm := comm_uCoinWrap_clean K p outs40 r
  have hRout : cleanProj sImg * ((uCoinWrap K p outs40 r).1 * P) = (uCoinWrap K p outs40 r).1 *
      P := by rw [hComm, ← Matrix.mul_assoc, hAbs]
  have hGrp : (fwdCirc q).eval * uCoinWrap K p outs40 r = (cXorMaskCoin K outs40 r).eval *
      (fwdCirc q).eval
      := by dsimp only [uCoinWrap]; rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hMidEq : (fwdCirc q).eval.1 * ((uCoinWrap K p outs40 r).1 * P) =
      (cXorMaskCoin K outs40 r).eval.1 * ((fwdCirc q).eval.1 * P)
      := by rw [← Matrix.mul_assoc, ← coe_mul_u_tw, hGrp, coe_mul_u_tw, Matrix.mul_assoc]
  exact cleanWorkStep_of_subspaceStep (rCoinClean K r)
      (uCoinWrap K p outs40 r) _ hComm (subspaceStep_wrapDyn v q sImg (.circuit (cXorMaskCoin K
      outs40 r)) P ((uCoinWrap K p outs40 r).1 * P)
      (validProg_mapCPSW rI p s hValid) hAbs hRout (hMidEq ▸ subspaceStep_circuit_cw (cXorMaskCoin K
      outs40 r) ((fwdCirc q).eval.1 * P)))
theorem count_pCoinWrap {K nAnd : ℕ} (p : ComputeProg (41 + K)) (outs40 : Fin 40 → ℕ)
    (hAnd : p.numAnd = nAnd) {Var : Type} {n : ℕ} (v : Var) (r : QRegister (81 + K) n) :
    (pCoinWrap K p outs40 v r).count PrimitiveGate.T = 4 * nAnd ∧
    (pCoinWrap K p outs40 v r).count PrimitiveGate.TOFF =
    0 := by obtain ⟨hT, hF⟩ :=
              count_wrapDyn v (mapCPSW (rCoinInner K r) p)
              (.circuit (cXorMaskCoin K outs40 r)); obtain ⟨cT, cF⟩ :=
              count_qXorMask40 (rCoinInner K r) (rCoinOut40 K r)
              (innerCoin_ne_out40 K r) outs40 40 Nat.le.refl; dsimp only [pCoinWrap,
              DynamicCircuit.count, cXorMaskCoin] at hT hF ⊢; rw [numAnd_mapCPSW, hAnd,
              cT] at hT; rw [cF] at hF; exact ⟨hT, hF⟩
theorem dynWires_pCoinWrap (K : ℕ) (p : ComputeProg (41 + K)) (outs40 : Fin 40 → ℕ) {Var : Type}
    {n : ℕ} (S : Wire n → Prop) (v : Var) (r : QRegister (81 + K) n)
    (hr : ∀ j : Fin (81 + K), S (r j)) : DynWires S (pCoinWrap K p outs40 v r) :=
  dynWires_wrapDyn v (mapCPSW (rCoinInner K r) p) (.circuit (cXorMaskCoin K outs40 r))
    (computeProgWires_mapCPSW _ (fun i ↦ hr (innerIdxCoin K i)) p)
    (circWires_qXorMask40 _ _ _ outs40 (fun i ↦ hr (innerIdxCoin K i))
      (fun j ↦ hr (QRegister.block 41 40 (outBlk_le K) j)) 40 Nat.le.refl)
/-- Canonical `41 + K`-wire input assignment for `c : Fin (2 ^ 41)` with `0` on `41..40+K`. -/
def coinInitBits (K : ℕ) (c : Fin (2 ^ 41)) : BitAssignment (41 + K) :=
  fun i ↦ if i.val < 41 then (if c.val.testBit i.val then 1 else 0) else 0
/-- Turnkey `Stage1ZeroNEremOracleGen (4 * nAnd) (81 + K)` from `(p, outs40)`. -/
def stage1ZeroNEremOracleOfProg {K nAnd : ℕ}
    (p : ComputeProg (41 + K)) (s : Finset (Wire (41 + K))) (outs40 : Fin 40 → ℕ)
    (hs : ∀ u ∈ s, 41 ≤ u.val) (hValid : p.ValidProg ∅ s) (hAnd : p.numAnd = nAnd) :
    Stage1ZeroNEremOracleGen (4 * nAnd) (81 + K) (le81_coin K) where
  u := uCoinWrap K p outs40
  fwdDyn := pCoinWrap K p outs40
  revDyn := pCoinWrap K p outs40
  cleanWorkStep := fun v r ↦
    let hc := cleanWorkStep_pCoinWrap K p s outs40 hs hValid v r
    ⟨hc, (uCoinWrap_inv K p outs40 r).symm ▸ hc⟩
  counts := fun v r ↦
    let ⟨hT, hF⟩ := count_pCoinWrap p outs40 hAnd v r
    ⟨hT, hF, hT, hF⟩
  dynWires := fun S v r hr ↦
    let hd := dynWires_pCoinWrap K p outs40 S v r hr
    ⟨hd, hd⟩
theorem coinWrapOutFn_eq_of_eval {K : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (p : ComputeProg (41 + K)) (outs40 : Fin 40 → ℕ) (hEval : ∀ (c : Fin (2 ^ 41))
    (j : Fin 40), maskParity (outs40 j) (p.fwdBits (coinInitBits K c))
    (41 + K) le_rfl = if (zeroNEremOutMask (decodeCoin c)).testBit j.val then 1 else 0)
    (c : Fin (2 ^ 41)) (j : Fin 40) : coinWrapOutFn K p outs40 (fun u : Fin (81 + K) ↦
    if _ : u.val < 41 then (if c.val.testBit u.val then 1 else 0) else 0) j =
    if (zeroNEremOutMask (decodeCoin c)).testBit j.val then 1 else 0 := by
  refine (congrArg (fun f ↦ maskParity (outs40 j) (p.fwdBits f) (41 + K) le_rfl)
      (funext fun i ↦ ?_)).trans (hEval c j)
  dsimp only [coinInitBits]
  rw [innerIdxCoin_val]
  split_ifs <;> first | rfl | omega
theorem xag_pre_le (N k : ℕ) (hk : k ≤ N) : 0 + (41 + k) ≤ 41 + (N + 2) := by omega
theorem xag_gate_lt (N : ℕ) (j : Fin N) : 41 + j.val < 41 + (N + 2) := by omega
theorem xag_wA_lt (N : ℕ) : 41 + N < 41 + (N + 2) := by omega
theorem xag_wB_lt (N : ℕ) : 42 + N < 41 + (N + 2) := by omega
abbrev rXagPre (N k : ℕ) (hk : k ≤ N) : QRegister (41 + k) (41 + (N + 2)) :=
    QRegister.block 0 (41 + k) (xag_pre_le N k hk)
def wXagGate (N : ℕ) (j : Fin N) : Wire (41 + (N + 2)) := ⟨41 + j.val, xag_gate_lt N j⟩
def wXagA (N : ℕ) : Wire (41 + (N + 2)) := ⟨41 + N, xag_wA_lt N⟩
def wXagB (N : ℕ) : Wire (41 + (N + 2)) := ⟨42 + N, xag_wB_lt N⟩
theorem disj_pre_A (N k : ℕ) (hk : k ≤ N) (i : Fin (41 + k)) : rXagPre N k hk i ≠ wXagA N :=
  fun e ↦ (by omega : 0 + i.val ≠ 41 + N) (congrArg Fin.val e)
theorem disj_pre_B (N k : ℕ) (hk : k ≤ N) (i : Fin (41 + k)) : rXagPre N k hk i ≠ wXagB N :=
  fun e ↦ (by omega : 0 + i.val ≠ 42 + N) (congrArg Fin.val e)
theorem disj_pre_gate (N k : ℕ) (hk : k + 1 ≤ N) (i : Fin (41 + k)) :
    rXagPre N k (Nat.le_of_succ_le hk) i ≠ wXagGate N ⟨k, hk⟩ :=
  fun e ↦ (by omega : 0 + i.val ≠ 41 + k) (congrArg Fin.val e)
theorem ne_xag_AB (N : ℕ) : wXagA N ≠ wXagB N := fun e ↦
    (by omega : 41 + N ≠ 42 + N) (congrArg Fin.val e)
theorem ne_xag_AG (N : ℕ) (j : Fin N) : wXagA N ≠ wXagGate N j :=
  fun e ↦ (by omega : 41 + N ≠ 41 + j.val) (congrArg Fin.val e)
theorem ne_xag_BG (N : ℕ) (j : Fin N) : wXagB N ≠ wXagGate N j :=
  fun e ↦ (by omega : 42 + N ≠ 41 + j.val) (congrArg Fin.val e)
/-- Clean `TempAND` wire set remaining before gate index `k`. -/
def sXag (N k : ℕ) : Finset (Wire (41 + (N + 2))) :=
    (Finset.univ.filter fun j : Fin N ↦ k ≤ j.val).image (wXagGate N)
theorem sXag_ge41 (N k : ℕ) (u : Wire (41 + (N + 2))) (hu : u ∈ sXag N k) : 41 ≤ u.val := by
  exact (Finset.mem_image.mp hu).elim fun j hj ↦ hj.2 ▸ Nat.le_add_right 41 j.val
theorem wXagA_notMem_sXag (N k : ℕ) : wXagA N ∉ sXag N k := fun h ↦
  (Finset.mem_image.mp h).elim fun j hj ↦ ne_xag_AG N j hj.2.symm
theorem wXagB_notMem_sXag (N k : ℕ) : wXagB N ∉ sXag N k := fun h ↦
  (Finset.mem_image.mp h).elim fun j hj ↦ ne_xag_BG N j hj.2.symm
theorem mem_sXag_self (N k : ℕ) (hk : k + 1 ≤ N) : wXagGate N ⟨k, hk⟩ ∈ sXag N k :=
  Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, rfl⟩
theorem erase_sXag_eq (N k : ℕ) (hk : k + 1 ≤ N) : (sXag N k).erase (wXagGate N ⟨k, hk⟩) =
    sXag N (k + 1) := by
  ext u
  simp only [sXag, Finset.mem_erase, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨hne, j, hkj, hu⟩ ↦ ⟨j, Nat.lt_of_le_of_ne hkj fun e ↦
      hne (hu.symm.trans (congrArg (wXagGate N) (Fin.ext e.symm))), hu⟩,
    fun ⟨j, hkj, hu⟩ ↦
        ⟨fun e ↦ (by omega : 41 + j.val ≠ 41 + k) (congrArg Fin.val (hu.trans e)), j, by omega, hu⟩⟩
theorem numAnd_qXorMask1_zero {M n : ℕ} (src : QRegister M n) (dst : Wire n)
    (hDisj : ∀ i : Fin M, src i ≠ dst) (mask : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ M), (qXorMask1 src dst hDisj mask m hm).numAnd = 0
  | 0, _ => by cases h : mask.testBit 0 <;> simp [qXorMask1, h, ComputeProg.numAnd]
  | m + 1, _ => by
      cases h : mask.testBit (1 + m) <;>
        simp [qXorMask1, h, ComputeProg.numAnd, numAnd_qXorMask1_zero src dst hDisj mask m]
theorem valid_finalClean_qXorMask1 {M n : ℕ} (src : QRegister M n) (dst : Wire n)
    (hDisj : ∀ i : Fin M, src i ≠ dst) (mask : ℕ) (s : Finset (Wire n)) (hdst : dst ∉ s) :
    ∀ (m : ℕ) (hm : m ≤ M),
      ComputeProg.finalClean s (qXorMask1 src dst hDisj mask m hm) = s ∧
      ComputeProg.ValidProg ∅ s (qXorMask1 src dst hDisj mask m hm)
  | 0, _ =>
        by cases h : mask.testBit 0 <;> simp [qXorMask1, h, ComputeProg.finalClean,
             ComputeProg.ValidProg, hdst]
  | m + 1, hm => by
      obtain ⟨hfc, hvp⟩ :=
          valid_finalClean_qXorMask1 src dst hDisj mask s hdst m (Nat.le_of_succ_le hm)
      cases h : mask.testBit (1 + m) <;>
        simp [qXorMask1, h, ComputeProg.finalClean, ComputeProg.ValidProg, hfc, hvp, hdst]
/-- Single XAG `AND` step computing `(maskParity a) * (maskParity b)` into clean `wXagGate N k`. -/
def xagStepProg (N k : ℕ) (hk : k + 1 ≤ N) (a b : ℕ) : ComputeProg (41 + (N + 2)) :=
  let hk0 := Nat.le_of_succ_le hk;
  let pA := qXorMask1 (rXagPre N k hk0) (wXagA N) (disj_pre_A N k hk0) a (41 + k) le_rfl;
  let pB := qXorMask1 (rXagPre N k hk0) (wXagB N) (disj_pre_B N k hk0) b (41 + k) le_rfl;
  let gAnd : ComputeProg (41 + (N + 2)) :=
      .andGate (wXagA N) (wXagB N) (wXagGate N ⟨k, hk⟩) (ne_xag_AB N) (ne_xag_AG N ⟨k, hk⟩)
      (ne_xag_BG N ⟨k, hk⟩)
  .seq (.seq (.seq (.seq pA pB) gAnd) pB) pA
theorem xagStepProg_spec (N k : ℕ) (hk : k + 1 ≤ N) (a b : ℕ) : (xagStepProg N k hk a b).numAnd =
    1 ∧
    ComputeProg.finalClean (sXag N k) (xagStepProg N k hk a b) = sXag N (k + 1) ∧
    ComputeProg.ValidProg ∅ (sXag N k) (xagStepProg N k hk a b) := by
  let hk0 := Nat.le_of_succ_le hk
  have vfA (j) :=
      valid_finalClean_qXorMask1 _ _ (disj_pre_A N k hk0) a (sXag N j) (wXagA_notMem_sXag N j)
      (41 + k) le_rfl
  have vfB (j) :=
      valid_finalClean_qXorMask1 _ _ (disj_pre_B N k hk0) b (sXag N j) (wXagB_notMem_sXag N j)
      (41 + k) le_rfl
  dsimp only [xagStepProg, ComputeProg.numAnd, ComputeProg.finalClean, ComputeProg.ValidProg]
  rw [numAnd_qXorMask1_zero, numAnd_qXorMask1_zero, (vfA k).1, (vfB k).1, erase_sXag_eq, (vfB _).1,
      (vfA _).1]
  exact ⟨rfl, rfl, ⟨⟨⟨(vfA k).2, (vfB k).2⟩, Finset.notMem_empty _, Finset.notMem_empty _,
    Finset.notMem_empty _, mem_sXag_self N k hk⟩, (vfB _).2⟩, (vfA _).2⟩
theorem fwdBits_xagStepProg (N k : ℕ) (hk : k + 1 ≤ N) (a b : ℕ) (β : BitAssignment (41 + (N + 2)))
    (hA : β (wXagA N) = 0) (hB : β (wXagB N) = 0) (hG : β (wXagGate N ⟨k, hk⟩) = 0) :
    let hk0 := Nat.le_of_succ_le hk
    let vA := maskParity a (fun i ↦ β (rXagPre N k hk0 i)) (41 + k) le_rfl
    let vB := maskParity b (fun i ↦ β (rXagPre N k hk0 i)) (41 + k) le_rfl
    (xagStepProg N k hk a b).fwdBits β = Function.update β (wXagGate N ⟨k, hk⟩) (vA * vB) := by
  let hk0 := Nat.le_of_succ_le hk
  let fPre := fun i : Fin (41 + k) ↦ β (rXagPre N k hk0 i)
  have hp {d} (hd : ∀ i, rXagPre N k hk0 i ≠ d) (m) {γ : BitAssignment (41 + (N + 2))}
      (hγ : (fun i ↦ γ (rXagPre N k hk0 i)) = fPre) :
      (qXorMask1 (rXagPre N k hk0) d hd m (41 + k) le_rfl).fwdBits γ =
        Function.update γ d (γ d + maskParity m fPre (41 + k) le_rfl) := by
          rw [fwdBits_qXorMask1, hγ]
  have hU {d} {γ : BitAssignment (41 + (N + 2))} {x} (hd : ∀ i, rXagPre N k hk0 i ≠ d)
      (hγ : (fun i ↦ γ (rXagPre N k hk0 i)) = fPre) :
      (fun i ↦ Function.update γ d x (rXagPre N k hk0 i)) = fPre :=
    funext fun i ↦ (Function.update_of_ne (hd i) _ _).trans (congrFun hγ i)
  dsimp only [xagStepProg, ComputeProg.fwdBits]
  rw [hp (disj_pre_A N k hk0) a rfl, hp (disj_pre_B N k hk0) b (hU (disj_pre_A N k hk0) rfl),
    hp (disj_pre_B N k hk0) b (hU (disj_pre_gate N k hk) (hU (disj_pre_B N k hk0)
        (hU (disj_pre_A N k hk0) rfl))),
    hp (disj_pre_A N k hk0) a (hU (disj_pre_B N k hk0)
      (hU (disj_pre_gate N k hk) (hU (disj_pre_B N k hk0) (hU (disj_pre_A N k hk0) rfl))))]
  funext w
  rcases eq_or_ne w (wXagA N) with rfl | hwA
  · simp only [Function.update_self, Function.update_of_ne (ne_xag_AB N),
      Function.update_of_ne (ne_xag_AG N ⟨k, hk⟩), hA, zero_add, CharTwo.add_self_eq_zero]
  · rcases eq_or_ne w (wXagB N) with rfl | hwB
    · simp only [Function.update_self, Function.update_of_ne hwA,
        Function.update_of_ne (ne_xag_BG N ⟨k, hk⟩), hB, zero_add, CharTwo.add_self_eq_zero]
    · rcases eq_or_ne w (wXagGate N ⟨k, hk⟩) with rfl | hwG
      · simp only [Function.update_self, Function.update_of_ne hwA, Function.update_of_ne hwB,
          Function.update_of_ne (ne_xag_AB N), Function.update_of_ne (ne_xag_AB N).symm, hA, hB, hG,
          zero_add, fPre]
      · simp only [Function.update_of_ne hwA, Function.update_of_ne hwB, Function.update_of_ne hwG]
/-- Compile `N` XAG `AND` gates `gates : Fin N → ℕ × ℕ` into `ComputeProg (41 + (N + 2))`. -/
def compileXag (N : ℕ) (gates : Fin N → ℕ × ℕ) : (k : ℕ) → k ≤ N → ComputeProg (41 + (N + 2))
  | 0, _ => .id
  | k + 1, hk =>
      .seq (compileXag N gates k (Nat.le_of_succ_le hk))
        (xagStepProg N k hk (gates ⟨k, hk⟩).1 (gates ⟨k, hk⟩).2)
theorem compileXag_spec (N : ℕ) (gates : Fin N → ℕ × ℕ) :
    ∀ (k : ℕ) (hk : k ≤ N),
      (compileXag N gates k hk).numAnd = k ∧
      ComputeProg.finalClean (sXag N 0) (compileXag N gates k hk) = sXag N k ∧
      ComputeProg.ValidProg ∅ (sXag N 0) (compileXag N gates k hk)
  | 0, _ => ⟨rfl, rfl, trivial⟩
  | k + 1, hk => by
      obtain ⟨ihN, ihF, ihV⟩ :=
          compileXag_spec N gates k (Nat.le_of_succ_le hk); obtain ⟨stN, stF, stV⟩ :=
          xagStepProg_spec N k hk (gates ⟨k, hk⟩).1 (gates ⟨k, hk⟩).2; dsimp only [compileXag,
          ComputeProg.numAnd, ComputeProg.finalClean, ComputeProg.ValidProg]; rw [ihN, stN, ihF,
          stF]; exact ⟨rfl, rfl, ihV, stV⟩
theorem testBit_one_succ (n : ℕ) : (1 : ℕ).testBit (n + 1) = false :=
    Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (Nat.succ_ne_zero n))
theorem zmod2_ite_xor_and (u v w : Bool) : (if u then (1 : ZMod 2) else 0) +
    (if w then (if v then 1 else 0) else 0) = if xor u (v && w) then 1 else 0 := by
  cases u <;> cases v <;> cases w <;> decide
theorem zmod2_ite_mul (b1 b2 : Bool) : (if b1 then (1 : ZMod 2) else 0) * (if b2 then 1 else 0) =
    if (b1 && b2) then 1 else 0 := by
  cases b1 <;> cases b2 <;> decide
/-- Pure `Bool` bit-count parity over bits `0 .. m - 1` of `x : ℕ`. -/
def oddBits (x : ℕ) : ℕ → Bool
  | 0 => false
  | m + 1 => xor (oddBits x m) (x.testBit m)
theorem maskParity_eq_oddBits {M : ℕ} (mask env : ℕ) (α : BitAssignment M)
    (hBit0 : env.testBit 0 = true)
    (hBits : ∀ i : Fin M, α i = if env.testBit (1 + i.val) then 1 else 0) :
    ∀ (k : ℕ) (hk : k ≤ M),
      maskParity mask α k hk = if oddBits (env &&& mask) (1 + k) then 1 else 0
  | 0, _ =>
        by simp only [maskParity, oddBits, Nat.testBit_and, hBit0, Bool.true_and, Bool.false_xor]
  | k + 1, hk => by
      dsimp only [maskParity]
      rw [maskParity_eq_oddBits mask env α hBit0 hBits k (Nat.le_of_succ_le hk), hBits ⟨k, hk⟩,
        show 1 + (k + 1) = (1 + k) + 1 by omega]
      simp only [oddBits, Nat.testBit_and]
      exact zmod2_ite_xor_and _ _ _
/-- Pure `ℕ` bitmask XAG evaluator (`env` bit `0` = `1`, `1..41` = `c`, `42 + k` = gate `k`). -/
def xagEnv (c : ℕ) (N : ℕ) (gates : Fin N → ℕ × ℕ) : (k : ℕ) → k ≤ N → ℕ
  | 0, _ => 1 ||| (c <<< 1)
  | k + 1, hk =>
      let prev := xagEnv c N gates k (Nat.le_of_succ_le hk); let ga := (gates ⟨k, hk⟩).1;
      let gb := (gates ⟨k, hk⟩).2
      if oddBits (prev &&& ga) (42 + k) && oddBits (prev &&& gb) (42 + k) then
        prev ||| (1 <<< (42 + k))
      else prev
theorem xagEnv_zero_testBit (c : ℕ) (hc : c < 2 ^ 41) :
    (1 ||| (c <<< 1)).testBit 0 = true ∧ (∀ u < 41, (1 ||| (c <<< 1)).testBit (1 + u) =
        c.testBit u) ∧
    (∀ b : ℕ, 42 ≤ b → (1 ||| (c <<< 1)).testBit b = false) := by
  refine ⟨by simp,
    fun u _ ↦ by simp [Nat.testBit_or, Nat.add_comm 1 u, testBit_one_succ, Nat.testBit_shiftLeft],
    fun b hb ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  simpa [Nat.testBit_or, testBit_one_succ, Nat.testBit_shiftLeft] using
    Nat.testBit_lt_two_pow (hc.trans_le (Nat.pow_le_pow_right (by omega) (by omega : 41 ≤ m)))
theorem xagEnv_invariant (c : Fin (2 ^ 41)) (N : ℕ) (gates : Fin N → ℕ × ℕ) :
    ∀ (k : ℕ) (hk : k ≤ N),
      let β := (compileXag N gates k hk).fwdBits (coinInitBits (N + 2) c)
      let env := xagEnv c.val N gates k hk
      env.testBit 0 = true ∧ (∀ b : ℕ, 42 + k ≤ b → env.testBit b = false) ∧
      (∀ i : Fin (41 + (N + 2)), β i = if i.val < 41 +
          k then (if env.testBit (1 + i.val) then 1 else 0) else 0)
  | 0, _ => by
      obtain ⟨h0, hc0, hhi⟩ := xagEnv_zero_testBit c.val c.isLt
      exact ⟨h0, hhi, fun i ↦ by by_cases hi : i.val < 41 <;>
        simp [compileXag, ComputeProg.fwdBits, xagEnv, coinInitBits, hi, hc0]⟩
  | k + 1, hk => by
      let hk0 := Nat.le_of_succ_le hk
      obtain ⟨ih0, ihHi, ihB⟩ := xagEnv_invariant c N gates k hk0
      let β := (compileXag N gates k hk0).fwdBits (coinInitBits (N + 2) c)
      let env := xagEnv c.val N gates k hk0
      have hZero {w} (hw : ¬ w.val < 41 + k) : β w = 0 := (ihB w).trans (ifn_tw hw)
      have hPre (u : Fin (41 + k)) : β (rXagPre N k hk0 u) = if env.testBit (1 +
          u.val) then 1 else 0 := by
        simpa [Nat.zero_add, u.isLt] using ihB (rXagPre N k hk0 u)
      have hp (g) : maskParity g (fun i ↦ β (rXagPre N k hk0 i)) (41 + k) le_rfl =
          if oddBits (env &&& g) (42 + k) then 1 else 0 := by
        simpa only [show 1 + (41 + k) = 42 +
            k by omega] using maskParity_eq_oddBits g env _ ih0 hPre (41 + k) le_rfl
      dsimp only [compileXag, ComputeProg.fwdBits, xagEnv]
      rw [fwdBits_xagStepProg N k hk _ _ β (hZero (by
        dsimp [wXagA]
        omega))
        (hZero (by
          dsimp [wXagB]
          omega)) (hZero (by
          dsimp [wXagGate]
          omega)), hp, hp,
            zmod2_ite_mul]
      set bitOut : Bool :=
          oddBits (env &&& (gates ⟨k, hk⟩).1) (42 + k) && oddBits (env &&& (gates ⟨k, hk⟩).2)
          (42 + k)
      refine
          ⟨by cases bitOut <;> simp only [↓reduceIte, Bool.false_eq_true, Nat.testBit_or, ih0,
                Bool.true_or],
        fun b hb ↦ ?_, fun i ↦ ?_⟩
      · cases bitOut
        · exact ihHi b (by omega)
        · obtain ⟨m, hm⟩ : ∃ m, b - (42 + k) = m + 1 := ⟨b - (42 + k) - 1, by omega⟩
          simp [Nat.testBit_or, ihHi b (by omega), Nat.testBit_shiftLeft, show b ≥ 42 + k by omega,
              hm, testBit_one_succ]
      · by_cases hiG : i = wXagGate N ⟨k, hk⟩
        · subst hiG
          cases bitOut <;> simp [wXagGate, show 1 + (41 + k) = 42 + k by omega,
              ihHi (42 + k) le_rfl,
            Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_zero]
        · rw [Function.update_of_ne hiG]
          refine (ihB i).trans ?_
          have : i.val ≠ 41 + k := fun e ↦ hiG (Fin.ext e)
          by_cases hlt : i.val < 41 + k
          · cases bitOut <;> simp [hlt, show i.val < 41 + (k + 1) by omega, Nat.testBit_or,
              Nat.testBit_shiftLeft, show ¬(1 + i.val ≥ 42 + k) by omega]
          · simp [hlt, show ¬i.val < 41 + (k + 1) by omega]
theorem xag_outParity_eq_of_eval {N : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (gates : Fin N → ℕ × ℕ) (outs40 : Fin 40 → ℕ) (hEval : ∀ (c : Fin (2 ^ 41))
    (j : Fin 40), oddBits (xagEnv c.val N gates N le_rfl &&& outs40 j)
    (42 + N) = (zeroNEremOutMask (decodeCoin c)).testBit j.val) (c : Fin (2 ^ 41))
    (j : Fin 40) : maskParity (outs40 j)
    ((compileXag N gates N le_rfl).fwdBits (coinInitBits (N + 2) c)) (41 + (N + 2)) le_rfl =
    if (zeroNEremOutMask (decodeCoin c)).testBit j.val then 1 else 0 := by
  obtain ⟨he0, heHi, heB⟩ := xagEnv_invariant c N gates N le_rfl
  let env := xagEnv c.val N gates N le_rfl
  have hAll (i : Fin (41 + (N + 2))) :
      (compileXag N gates N le_rfl).fwdBits (coinInitBits (N + 2) c) i =
        if env.testBit (1 + i.val) then 1 else 0 := by
    by_cases hlt : i.val < 41 + N
    · simp [env, heB i, hlt]
    · simp [env, heB i, hlt, heHi (1 + i.val) (by omega)]
  rw [maskParity_eq_oddBits (outs40 j) env _ he0 hAll (41 + (N + 2)) le_rfl,
    show 1 + (41 + (N + 2)) = ((42 + N) + 1) + 1 by omega]
  simp [env, oddBits, Nat.testBit_and, heHi (42 + N) le_rfl, heHi ((42 + N) + 1)
      (by omega), hEval c j]
end QuantumComputation.Specs.PhotochemistrySolution.CoinWrap

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1SingleWrap
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs PhotochemistrySolution.KetSupport
  PhotochemistrySolution PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.CoinWrap
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
/--
Generalized split Stage-1 wire map placing `K₁` live wires at `rScrCompact1493[bLive..)` and
`K₂` inner-recomputed wires at `rScrCompact1493[0..K₂)` (`K₂ <= bLive`, `bLive + K₁ <= 1493`).
-/
def splitCoinGenWireFn (bLive K₁ K₂ : ℕ) (hbLo : K₂ ≤ bLive) (hbHi : bLive + K₁ ≤ 1493)
    (j : Fin (81 + (K₁ + K₂))) : Wire dLayout :=
  if h1 : j.val < 41 then rOuter41Layout ⟨j.val, h1⟩
  else if h2 : j.val < 81 then rOut40Layout ⟨j.val - 41, by omega⟩
  else if h3 : j.val < 81 + K₁ then rScrCompact1493 ⟨bLive + (j.val - 81), by omega⟩
  else rScrCompact1493 ⟨j.val - (81 + K₁), by omega⟩
theorem val_splitCoinGenWireFn {bLive K₁ K₂ : ℕ} (hbLo : K₂ ≤ bLive) (hbHi : bLive + K₁ ≤ 1493)
    (j : Fin (81 + (K₁ + K₂))) : (splitCoinGenWireFn bLive K₁ K₂ hbLo hbHi j).val = if j.val <
    41 then 7215 + j.val else if j.val < 81 then 5715 + (j.val - 41) else if j.val < 81 +
    K₁ then if bLive + (j.val - 81) < 33 then 5680 + (bLive + (j.val - 81)) else 5755 +
    (bLive + (j.val - 81) - 33) else if j.val - (81 + K₁) < 33 then 5680 +
    (j.val - (81 + K₁)) else 5755 + (j.val - (81 + K₁) - 33) := by
  dsimp only [splitCoinGenWireFn]
  split_ifs <;> simp_all only [val_rOuter41Layout, val_rOut40Layout, val_rScrCompact1493,
      ↓reduceIte]
theorem splitCoinGenWireFn_injective {bLive K₁ K₂ : ℕ} (hbLo : K₂ ≤ bLive)
    (hbHi : bLive + K₁ ≤ 1493) :
    Function.Injective (splitCoinGenWireFn bLive K₁ K₂ hbLo hbHi) := fun a b e ↦ by
  have hv := (val_splitCoinGenWireFn hbLo hbHi a).symm.trans
    ((congrArg Fin.val e).trans (val_splitCoinGenWireFn hbLo hbHi b))
  exact Fin.ext (by repeat' first | omega | split at hv)
/--
Generalized split `81 + (K₁ + K₂)` Stage-1 `QRegister` on `dLayout` (`bLive = 311` starts live
wires at `6033` for 3-port `PortB`; `bLive = 361 + wMid` starts at `6083 + wMid` for 4-port).
-/
def rSplitCoinGen (bLive K₁ K₂ : ℕ) (hbLo : K₂ ≤ bLive) (hbHi : bLive + K₁ ≤ 1493) : QRegister (81 +
    (K₁ + K₂)) dLayout :=
    ⟨⟨splitCoinGenWireFn bLive K₁ K₂ hbLo hbHi, splitCoinGenWireFn_injective hbLo hbHi⟩⟩
theorem rSplitCoinGen_active_wIn {bLive wIn K₁ K₂ : ℕ} (hbLo : K₂ ≤ bLive)
    (hbHi : bLive + K₁ ≤ 1493) (hw : bLive + K₁ ≤ 361 + wIn) (j : Fin (81 + (K₁ + K₂))) :
    ActiveLayoutFusedOf wIn (rSplitCoinGen bLive K₁ K₂ hbLo hbHi j) := by
  have hv : (rSplitCoinGen bLive K₁ K₂ hbLo hbHi j).val = _ := val_splitCoinGenWireFn hbLo hbHi j
  unfold ActiveLayoutFusedOf
  rw [hv]
  repeat' first | omega | split
theorem rSplitCoinGen_clean_sub_1493 {bLive K₁ K₂ : ℕ} (hbLo : K₂ ≤ bLive)
    (hbHi : bLive + K₁ ≤ 1493) (u : Fin ((81 + (K₁ + K₂)) - 81)) : ∃ k : Fin 1493,
    (rCoinClean (K₁ + K₂) (rSplitCoinGen bLive K₁ K₂ hbLo hbHi)) u = rScrCompact1493 k := by
  refine ⟨⟨if u.val < K₁ then bLive + u.val else u.val - K₁, by split_ifs <;> omega⟩, ?_⟩
  change splitCoinGenWireFn bLive K₁ K₂ hbLo hbHi ⟨81 + u.val, _⟩ = _
  dsimp only [splitCoinGenWireFn]
  split_ifs <;> first | omega | exact congrArg rScrCompact1493 (Fin.ext (by
    dsimp only
    omega))
end QuantumComputation.Specs.PhotochemistrySolution.Stage1SingleWrap

namespace QuantumComputation.Specs.PhotochemistrySolution.MidOWCore
open Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution
  PhotochemistrySolution.FineLegendre PhotochemistrySolution.Stage4FineFast
  PhotochemistrySolution.Stage4FineMbu PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.Poly28Sub254
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (speciesOfBits2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg
    counts_wrapDynOnReg)
attribute [local irreducible] mkKetOpW SubregMBUCore.wrapDynOnReg SubregMBUCore.uStageOfCP
/- ### 1. Register Bounds and `Z[lZ..29]` Subregister on `QRegister (71 + K) n` -/

theorem midOW_lt0 (K : ℕ) : 0 < 71 + K := by omega
theorem midOW_lt1 (K : ℕ) : 1 < 71 + K := by omega
theorem midOW_ltY (K : ℕ) (k : Fin 36) : 5 + k.val < 71 + K := by have := k.isLt; omega
theorem midOW_ltZ (K : ℕ) (i : Fin 30) : 41 + i.val < 71 + K := by have := i.isLt; omega
theorem midOW_ltZHi (lZ K : ℕ) (hlZ : lZ ≤ 30) (j : Fin (30 - lZ)) :
    41 + lZ + j.val < 71 + K := by have := j.isLt; omega
theorem midOW_ltCln (K : ℕ) (j : Fin K) : 71 + j.val < 71 + K := by have := j.isLt; omega
/-- Wire map into `Z[lZ..29]` (`r[41+lZ .. 70]`) inside `QRegister (71 + K) n`. -/
def fMidZHi (lZ K : ℕ) (hlZ : lZ ≤ 30) : Fin (30 - lZ) → Fin (71 + K) := fun j ↦
    ⟨41 + lZ + j.val, midOW_ltZHi lZ K hlZ j⟩
theorem fMidZHi_inj (lZ K : ℕ) (hlZ : lZ ≤ 30) : Function.Injective (fMidZHi lZ K hlZ) :=
  fun _ _ e ↦ Fin.ext (Nat.add_left_cancel (congrArg Fin.val e))
/-- Subregister `Z[lZ..29]` of `r : QRegister (71 + K) n`. -/
def rMidZHi (lZ K : ℕ) (hlZ : lZ ≤ 30) {n : ℕ} (r : QRegister (71 + K) n) : QRegister (30 - lZ) n :=
  r.compose ⟨fMidZHi lZ K hlZ, fMidZHi_inj lZ K hlZ⟩
/- ### 3. Bit-Slicing & Carry-Kick Arithmetic Lemmas -/

theorem finBitsVal_cast {m m' : ℕ} (h : m = m') (f : Fin m → ZMod 2) : finBitsVal f =
    finBitsVal (fun i : Fin m' ↦ f ⟨i.val, h ▸ i.isLt⟩) := by
  cases h; rfl
theorem finBitsVal_split : ∀ (a b : ℕ) (f : Fin (a + b) → ZMod 2),
    finBitsVal f = finBitsVal (fun i : Fin a ↦
        f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩) +
      2 ^ a * finBitsVal (fun j : Fin b ↦ f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩)
  | 0, b, f => by
      simp [Nat.lt_one_iff.mp (finBitsVal_lt (fun i : Fin 0 ↦ f ⟨i.val, by omega⟩)),
        finBitsVal_cast (Nat.zero_add b) f]
  | a + 1, b, f => by
      rw [finBitsVal_cast (by omega : a + 1 + b = (a + b) + 1) f, finBitsVal_succ, finBitsVal_succ,
        show (fun i : Fin (a + b) ↦ f ⟨i.succ.val, _⟩) = fun i ↦ f ⟨i.val + 1, by omega⟩ from rfl,
        finBitsVal_split a b, show (fun i : Fin a ↦ f ⟨i.val + 1, _⟩) = fun i ↦
            f ⟨i.succ.val, by omega⟩ from rfl,
        show (fun j : Fin b ↦ f ⟨a + j.val + 1, _⟩) = fun j ↦ f ⟨a + 1 + j.val, by omega⟩ from
          funext fun j ↦ congrArg f (Fin.ext (Nat.add_right_comm a j.val 1)),
        show f ⟨(0 : Fin (a + b + 1)).val, _⟩ = f ⟨(0 : Fin (a + 1)).val, by omega⟩ from rfl,
            pow_succ']
      ring
theorem finBitsVal_shr (a b : ℕ) (f : Fin (a + b) → ZMod 2) : (finBitsVal f) >>> a =
    finBitsVal (fun j : Fin b ↦ f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩)
    := by rw [Nat.shiftRight_eq_div_pow, finBitsVal_split a b f,
            Nat.add_mul_div_left _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt (finBitsVal_lt _),
            zero_add]
theorem natOfZModBits_shr (a b : ℕ) (f : Fin (a + b) → ZMod 2) : (natOfZModBits (a + b) f) >>> a =
    finBitsVal (fun j : Fin b ↦ f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩)
    := by rw [← finBitsVal_eq_natOfZModBits (a + b) f, finBitsVal_shr a b f]
theorem finBitsVal_of_testBit : ∀ (m M : ℕ),
    finBitsVal (fun j : Fin m ↦ if M.testBit j.val then (1 : ZMod 2) else 0) = M % 2 ^ m
  | 0, M => (Nat.lt_one_iff.mp (finBitsVal_lt _)).trans (Nat.mod_one M).symm
  | m + 1, M => by
      rw [finBitsVal_succ, show (fun j : Fin m ↦ if M.testBit j.succ.val then (1 : ZMod 2) else 0) =
            fun j ↦ if (M / 2).testBit j.val then 1 else 0 from
            funext fun j ↦ by rw [Fin.val_succ, Nat.testBit_add, pow_one],
          finBitsVal_of_testBit m (M / 2),
          show (if M.testBit (0 : Fin (m + 1)).val then (1 : ZMod 2) else 0).val = M % 2 by
            rcases Nat.mod_two_eq_zero_or_one M with hm | hm <;> simp [Nat.testBit_zero, hm]
            try rfl,
          two_mul_mod_add (Nat.mod_lt M Nat.zero_lt_two), Nat.mod_add_div M 2, pow_succ']
theorem zmod2_testBit_eq_div_pow (M b : ℕ) : (if M.testBit b then (1 : ZMod 2) else 0) =
    ((M / 2 ^ b : ℕ) : ZMod 2) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  conv_rhs => rw [← Nat.mod_add_div (M / 2 ^ b) 2]
  rcases Nat.mod_two_eq_zero_or_one (M / 2 ^ b) with hm | hm <;>
    simp [hm, CharTwo.two_eq_zero]
theorem zmod2_not_ite_bool (b : Bool) : (if b then (1 : ZMod 2) else 0) + 1 =
    if b then 0 else 1 := by
  cases b <;> decide
/- ### 4. Master Reflection Reduction to `finBitsVal` -/

/- ### 1. Controlled Reflection Loop `pCtrlNotReg1` (`0 T`, `0` `.TOFF`) -/

theorem ctrlNot_lt0 (k : ℕ) : 0 < 2 + k := by omega
theorem ctrlNot_lt1 (k : ℕ) : 1 < 2 + k := by omega
theorem ctrlNot_ltZ (k : ℕ) (j : Fin (k + 1)) : 1 + j.val < 2 + k := by have := j.isLt; omega
theorem ctrlNot_ne01 {n : ℕ} (k : ℕ) (r : QRegister (2 + k) n) : r ⟨0, ctrlNot_lt0 k⟩ ≠
    r ⟨1, ctrlNot_lt1 k⟩ :=
  fun e ↦ nomatch r.wires.injective e
/-- Subregister map skipping wire `1` (`r[0], r[2..k+2]`) for `pCtrlNotReg1`. -/
def idxCtrlNotSub (k : ℕ) (u : Fin (2 + k)) : ℕ := if u.val = 0 then 0 else 1 + u.val
theorem idxCtrlNotSub_lt (k : ℕ) (u : Fin (2 + k)) : idxCtrlNotSub k u < 2 + (k + 1) := by
  have _ := u.isLt; dsimp only [idxCtrlNotSub]; split_ifs <;> omega
/-- `Fin`-typed wire map for `pCtrlNotReg1` recursion. -/
def fCtrlNotSub (k : ℕ) : Fin (2 + k) → Fin (2 + (k + 1)) := fun u ↦
    ⟨idxCtrlNotSub k u, idxCtrlNotSub_lt k u⟩
theorem fCtrlNotSub_inj (k : ℕ) : Function.Injective (fCtrlNotSub k) := fun a b e ↦ by
  have hv : idxCtrlNotSub k a = idxCtrlNotSub k b := congrArg Fin.val e
  have _ := a.isLt; have _ := b.isLt
  dsimp only [idxCtrlNotSub] at hv; split_ifs at hv <;> exact Fin.ext (by omega)
/-- Controlled `CNOT` fanout from `r[0]` (`g`) onto `r[1 .. k+1]` (`0 T`, `0` `.TOFF`). -/
def pCtrlNotReg1 : (k : ℕ) → {Var : Type} → {n : ℕ} → Var → QRegister (2 + k) n →
    DynamicCircuit Var n
  | 0, _, _, v, r => cnot1 v (r ⟨0, ctrlNot_lt0 0⟩) (r ⟨1, ctrlNot_lt1 0⟩) (ctrlNot_ne01 0 r)
  | k + 1, _, _, v, r =>
      .seq (cnot1 v (r ⟨0, ctrlNot_lt0 (k + 1)⟩) (r ⟨1, ctrlNot_lt1 (k + 1)⟩)
          (ctrlNot_ne01 (k + 1) r))
        (pCtrlNotReg1 k v (r.compose ⟨fCtrlNotSub k, fCtrlNotSub_inj k⟩))
theorem pCtrlNotReg1_counts : ∀ (k : ℕ) {Var : Type} {n : ℕ} (v : Var) (r : QRegister (2 + k) n),
    (pCtrlNotReg1 k v r).count .T = 0 ∧ (pCtrlNotReg1 k v r).count .TOFF = 0
  | 0, Var, _, v, r => cnot1_counts (Var := Var) v _ _ (ctrlNot_ne01 0 r)
  | k + 1, Var, _, v, r => by
      have c0 := cnot1_counts (Var := Var) v _ _ (ctrlNot_ne01 (k + 1) r)
      have ih := pCtrlNotReg1_counts k v (r.compose ⟨fCtrlNotSub k, fCtrlNotSub_inj k⟩)
      simp only [pCtrlNotReg1, DynamicCircuit.count, c0.1, c0.2, ih.1, ih.2, Nat.add_zero, and_self]
theorem pCtrlNotReg1_dynWires : ∀ (k : ℕ) {Var : Type} {n : ℕ} (P : Wire n → Prop) (v : Var)
    (r : QRegister (2 + k) n),
    (∀ u : Fin (2 + k), P (r u)) → DynWires P (pCtrlNotReg1 k v r)
  | 0, _, _, P, v, r, hP => cnot1_dynWires P v _ _ (ctrlNot_ne01 0 r) (hP _) (hP _)
  | k + 1, _, _, P, v, r, hP =>
      ⟨cnot1_dynWires P v _ _ (ctrlNot_ne01 (k + 1) r) (hP _) (hP _),
       pCtrlNotReg1_dynWires k P v _ (fun u ↦ hP (fCtrlNotSub k u))⟩
theorem pCtrlNotReg1_step : ∀ (k : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (r : QRegister (2 + k) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    ∃ st' : BitAssignment n → BitAssignment n,
      SubspaceStep (mkKetOpW rWork st ph) (mkKetOpW rWork st' ph) (pCtrlNotReg1 k v r) ∧
      (∀ (δ : BitAssignment n) (w : Wire n), (∀ j : Fin (k + 1), w ≠
          r ⟨1 + j.val, ctrlNot_ltZ k j⟩) → st' δ w = st δ w) ∧
      (∀ (δ : BitAssignment n) (j : Fin (k + 1)),
        st' δ (r ⟨1 + j.val, ctrlNot_ltZ k j⟩) = st δ (r ⟨1 + j.val, ctrlNot_ltZ k j⟩) +
            st δ (r ⟨0, ctrlNot_lt0 k⟩))
  | 0, _, _, _, _, _, _, v, rWork, r, st, ph =>
      ⟨fun δ ↦ Function.update (st δ) (r ⟨1, ctrlNot_lt1 0⟩)
          (st δ (r ⟨1, ctrlNot_lt1 0⟩) + st δ (r ⟨0, ctrlNot_lt0 0⟩)),
       cnot1_step v rWork _ _ (ctrlNot_ne01 0 r) st ph,
       fun _ _ hw ↦ Function.update_of_ne (hw 0) _ _,
       fun _ j ↦ (Fin.ext (Nat.lt_one_iff.mp j.isLt) : j = 0) ▸ Function.update_self _ _ _⟩
  | k + 1, _, _, _, _, _, _, v, rWork, r, st, ph => by
      let st1 := fun δ ↦ Function.update (st δ) (r ⟨1, ctrlNot_lt1 (k + 1)⟩)
        (st δ (r ⟨1, ctrlNot_lt1 (k + 1)⟩) + st δ (r ⟨0, ctrlNot_lt0 (k + 1)⟩))
      let rSub := r.compose ⟨fCtrlNotSub k, fCtrlNotSub_inj k⟩
      obtain ⟨st2, hStep2, hNot2, hAct2⟩ := pCtrlNotReg1_step k v rWork rSub st1 ph
      have hrSucc (i : Fin (k + 1)) : rSub ⟨1 + i.val, ctrlNot_ltZ k i⟩ = r ⟨1 + i.succ.val,
          ctrlNot_ltZ (k + 1) i.succ⟩ :=
        congrArg r.wires (Fin.ext (by
          simp [fCtrlNotSub, idxCtrlNotSub, Fin.val_succ]
          omega))
      refine ⟨st2, subspaceStep_seq_mbu (cnot1_step v rWork _ _ (ctrlNot_ne01 (k +
          1) r) st ph) hStep2,
        fun δ w hw ↦ (hNot2 δ w fun i e ↦ hw i.succ (e.trans (hrSucc i))).trans
          (Function.update_of_ne (hw 0) _ _),
        fun δ j ↦ Fin.cases
          ((hNot2 δ _ fun i e ↦
              absurd (congrArg Fin.val (r.wires.injective (e.trans (hrSucc i)))) (by simp)).trans
            (Function.update_self _ _ _))
          (fun i ↦ by
            rw [← hrSucc i, hAct2 δ i, hrSucc i]
            dsimp only [st1]
            rw [Function.update_of_ne fun e ↦
                absurd (congrArg Fin.val (r.wires.injective e)) (by simp),
              show rSub ⟨0, ctrlNot_lt0 k⟩ = r ⟨0, ctrlNot_lt0 (k + 1)⟩ from rfl,
              Function.update_of_ne (ctrlNot_ne01 (k + 1) r)]) j⟩
/- ### 2. `1`-`AND` Wrapper `wrapAnd3` on `QRegister 3 n` (`4 T`, `0` `.TOFF`) -/

theorem pAnd3_valid4 : StructuredCB.validProgMask 0 4 pAnd3 = true := by decide +kernel
theorem mask4_eq_w3_2 {u : Wire 3} (hu : (4 : ℕ).testBit u.val = true) : u = w3_2 := by
  fin_cases u <;> first | rfl | cases hu
/-- Generic `wrapDynOnReg` step for `pAnd3` whenever `mid` preserves all `3` wires of `rAnd`. -/
theorem wrapAnd3 {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rWork : QRegister W n) (rAnd : QRegister 3 n) (mid : DynamicCircuit Var n)
    (st stMid : BitAssignment n → BitAssignment n) (ph₁ phMid ph₂ : BitAssignment n → ZMod 2)
    (hCln2 : ∀ δ, (∀ m : Fin W, δ (rWork m) = 0) → st δ (rAnd w3_2) = 0) (hFix : ∀ (u : Wire 3)
    (δ : BitAssignment n), stMid δ (rAnd u) = stepCB rAnd pAnd3.fwdBits (st δ) (rAnd u))
    (hPhEq : ∀ δ, (∀ m : Fin W, δ (rWork m) = 0) → phMid δ = ph₂ δ)
    (hInner : SubspaceStep (mkKetOpW rWork (fun δ ↦ stepCB rAnd pAnd3.fwdBits (st δ)) ph₁)
    (mkKetOpW rWork stMid phMid) mid) : SubspaceStep (mkKetOpW rWork st ph₁)
    (mkKetOpW rWork (fun δ w ↦ if w = rAnd w3_2 then st δ w else stMid δ w) ph₂)
    (wrapDynOnReg v rAnd pAnd3 mid) := by
  refine wrapStepMask v rWork rAnd 4 pAnd3 pAnd3_valid4 mid st _ ph₁ ph₂
    (fun _ δ hu hz ↦ mask4_eq_w3_2 hu ▸ hCln2 δ hz)
        (fun _ δ hu hz ↦ by simp [mask4_eq_w3_2 hu, hCln2 δ hz])
    (subspaceStep_of_eq_post hInner (mkKetOpW_congr rWork (fun δ _ ↦ funext fun w ↦ ?_) hPhEq))
  have hKeep (u : Wire 3) : (if rAnd u = rAnd w3_2 then st δ (rAnd u) else stMid δ (rAnd u)) =
      st δ (rAnd u) :=
    if he : rAnd u =
        rAnd w3_2 then ite_eq_left he else (ite_eq_right he).trans ((hFix u δ).trans
            (stepCB_pAnd3_not rAnd
        (st δ) he))
  by_cases hw2 : w = rAnd w3_2
  · rw [hw2, stepCB_pAnd3_anc, hKeep, hKeep, hKeep, hFix w3_2 δ, ← stepCB_pAnd3_anc]
  · rw [stepCB_pAnd3_not rAnd _ hw2, ite_eq_right hw2]
theorem finBitsVal_zero_fun : ∀ (m : ℕ), finBitsVal (fun _ : Fin m ↦ (0 : ZMod 2)) = 0
  | 0 => Nat.lt_one_iff.mp (finBitsVal_lt _)
  | m + 1 => (finBitsVal_succ _).trans (congrArg _ (congrArg (2 * ·) (finBitsVal_zero_fun m)))
/- ### 1. Full `(m + 1)`-Bit Carry Chain `pWrapCarryChain` (`4 * (m + 1)` `T`, `0` `.TOFF`) -/

theorem carryCh_ltA (m : ℕ) (j : Fin (m + 1)) : j.val < 3 * (m + 1) := by have := j.isLt; omega
theorem carryCh_ltB (m : ℕ) (j : Fin (m + 1)) : m + 1 + j.val < 3 * (m + 1) := by
  have := j.isLt; omega
theorem carryCh_ltOut (m : ℕ) (j : Fin (m + 1)) : 2 * m + 2 + j.val < 3 * (m + 1) := by
  have := j.isLt; omega
/-- Wire map for the `m + 1` clean carry outputs `r[2*m+2 .. 3*m+2]` of `pWrapCarryChain`. -/
def fCarryOut (m : ℕ) : Fin (m + 1) → Fin (3 * (m + 1)) := fun j ↦
    ⟨2 * m + 2 + j.val, carryCh_ltOut m j⟩
theorem fCarryOut_inj (m : ℕ) : Function.Injective (fCarryOut m) := fun a b e ↦ by
  have hv : 2 * m + 2 + a.val = 2 * m + 2 + b.val := congrArg Fin.val e
  exact Fin.ext (by omega)
/-- Output subregister `r[2*m+2 .. 3*m+2]` of `pWrapCarryChain`. -/
def rCarryOut (m : ℕ) {n : ℕ} (r : QRegister (3 * (m + 1)) n) : QRegister (m + 1) n :=
  r.compose ⟨fCarryOut m, fCarryOut_inj m⟩
/-- Head `3`-wire index map `(A[0], B[0], C[0])` for `pWrapCarryChain m`. -/
def idxCarryHead (m : ℕ) (u : Fin 3) : ℕ :=
    if u.val = 0 then 0 else if u.val = 1 then m + 1 else 2 * m + 2
theorem idxCarryHead_lt (m : ℕ) (u : Fin 3) : idxCarryHead m u < 3 * (m + 1) := by
  dsimp only [idxCarryHead]; (try split_ifs); all_goals omega
/-- `Fin`-typed head `3`-wire map for `pWrapCarryChain m`. -/
def fCarryHead (m : ℕ) : Fin 3 → Fin (3 * (m + 1)) := fun u ↦
    ⟨idxCarryHead m u, idxCarryHead_lt m u⟩
theorem fCarryHead_inj (m : ℕ) : Function.Injective (fCarryHead m) := fun a b e ↦ by
  fin_cases a <;> fin_cases b <;> simp_all [fCarryHead, idxCarryHead] <;> omega
/--
Tail `(1 + 3 * m)` -wire index map `(C[0], A[1..m], B[1..m], C[1..m])` for `pWrapCarryChain m` .
-/
def idxCarryTail (m : ℕ) (u : Fin (1 + 3 * m)) : ℕ :=
    if u.val = 0 then 2 * m + 2 else if u.val < 1 + m then u.val else if u.val < 1 + 2 * m then 1 +
    u.val else 2 + u.val
theorem idxCarryTail_lt (m : ℕ) (u : Fin (1 + 3 * m)) : idxCarryTail m u < 3 * (m + 1) := by
  have _ := u.isLt; dsimp only [idxCarryTail]; (try split_ifs); all_goals omega
/-- `Fin`-typed tail wire map for `pWrapCarryChain m`. -/
def fCarryTail (m : ℕ) : Fin (1 + 3 * m) → Fin (3 * (m + 1)) := fun u ↦
    ⟨idxCarryTail m u, idxCarryTail_lt m u⟩
theorem fCarryTail_inj (m : ℕ) : Function.Injective (fCarryTail m) := fun a b e ↦ by
  have hv : idxCarryTail m a = idxCarryTail m b ∧ a.val < _ ∧ b.val < _ :=
      ⟨congrArg Fin.val e, a.isLt, b.isLt⟩
  dsimp only [idxCarryTail] at hv
  (try split_ifs at hv) <;> exact Fin.ext (by omega)
/-- Full `(m + 1)`-bit carry-ripple MBU wrapper (`4 * (m + 1)` `T`, `0` `.TOFF`). -/
def pWrapCarryChain (m : ℕ) {Var : Type} {n : ℕ} (v : Var) (r : QRegister (3 * (m + 1)) n)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
    wrapDynOnReg v (r.compose ⟨fCarryHead m,
    fCarryHead_inj m⟩) pAnd3 (pWrapMajChain m v (r.compose ⟨fCarryTail m, fCarryTail_inj m⟩) mid)
theorem pWrapCarryChain_counts (m : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (r : QRegister (3 * (m + 1)) n) (mid : DynamicCircuit Var n) :
    (pWrapCarryChain m v r mid).count .T = 4 * (m + 1) + mid.count .T ∧
    (pWrapCarryChain m v r mid).count .TOFF = mid.count .TOFF := by
  obtain ⟨mT, mF⟩ :=
      pWrapMajChain_counts m v (r.compose ⟨fCarryTail m, fCarryTail_inj m⟩) mid; obtain ⟨wT, wF⟩ :=
      counts_wrapDynOnReg v (r.compose ⟨fCarryHead m,
      fCarryHead_inj m⟩) pAnd3 (pWrapMajChain m v (r.compose ⟨fCarryTail m,
      fCarryTail_inj m⟩) mid); rw [pAnd3_numAnd] at wT
  exact ⟨by dsimp only [pWrapCarryChain]; rw [wT, mT]; omega,
         by dsimp only [pWrapCarryChain]; rw [wF, mF]⟩
theorem pWrapCarryChain_dynWires (m : ℕ) {Var : Type} {n : ℕ} (P : Wire n → Prop) (v : Var)
    (r : QRegister (3 * (m + 1)) n) (mid : DynamicCircuit Var n)
    (hP : ∀ u : Fin (3 * (m + 1)), P (r u)) (hM : DynWires P mid) :
    DynWires P (pWrapCarryChain m v r mid) :=
  dynWires_wrapDynOnReg v (r.compose ⟨fCarryHead m, fCarryHead_inj m⟩)
    (fun u ↦ hP (fCarryHead m u)) pAnd3
    (pWrapMajChain_dynWires m P v (r.compose ⟨fCarryTail m, fCarryTail_inj m⟩) mid
      (fun u ↦ hP (fCarryTail m u)) hM)
/-- Loaded inner state of `pWrapCarryChain m`. -/
def stCarryIn (m : ℕ) {n : ℕ} (r : QRegister (3 * (m + 1)) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
  writeReg (st δ) (rCarryOut m r) (fun j ↦
    majCarryBit
      (finBitsVal (fun i : Fin (m + 1) ↦ st δ (r ⟨i.val, carryCh_ltA m i⟩)))
      (finBitsVal (fun i : Fin (m + 1) ↦ st δ (r ⟨m + 1 + i.val, carryCh_ltB m i⟩)))
      0 j.val)
/-- Uncomputed post-state of `pWrapCarryChain m`. -/
def stCarryOut (m : ℕ) {n : ℕ} (r : QRegister (3 * (m + 1)) n)
    (st stMid : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
    writeReg (stMid δ) (rCarryOut m r) (fun j ↦ st δ (rCarryOut m r j))
theorem carryChain_top_val (m : ℕ) {n : ℕ} (r : QRegister (3 * (m + 1)) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) :
    (stCarryIn m r st δ (rCarryOut m r ⟨m, Nat.lt_succ_self m⟩)).val =
    (finBitsVal (fun i : Fin (m + 1) ↦ st δ (r ⟨i.val, carryCh_ltA m i⟩)) +
    finBitsVal (fun i : Fin (m + 1) ↦ st δ (r ⟨m + 1 + i.val, carryCh_ltB m i⟩))) / 2 ^ (m + 1)
    := by dsimp only [stCarryIn]; rw [writeReg_apply_reg, majCarryBit_val (Nat.zero_le 1) m,
            Nat.mod_eq_of_lt (finBitsVal_lt _), Nat.mod_eq_of_lt (finBitsVal_lt _), Nat.add_zero]
theorem pWrapCarryChain_step (m : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (3 * (m + 1)) n)
    (mid : DynamicCircuit Var n) (st stMid : BitAssignment n → BitAssignment n)
    (ph₁ ph₂ : BitAssignment n → ZMod 2) (hCln : ∀ (j : Fin (m + 1)) (δ : BitAssignment n),
    (∀ q : Fin W, δ (rWork q) = 0) → st δ (rCarryOut m r j) = 0) (hFix : ∀ (u : Fin (3 * (m + 1)))
    (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) → stMid δ (r u) =
    stCarryIn m r st δ (r u)) (hInner : SubspaceStep (mkKetOpW rWork (stCarryIn m r st) ph₁)
    (mkKetOpW rWork stMid ph₂) mid) : SubspaceStep (mkKetOpW rWork st ph₁)
    (mkKetOpW rWork (stCarryOut m r st stMid) ph₂) (pWrapCarryChain m v r mid) := by
  let rHead := r.compose ⟨fCarryHead m, fCarryHead_inj m⟩
  let rTail := r.compose ⟨fCarryTail m, fCarryTail_inj m⟩
  let st1 : BitAssignment n → BitAssignment n := fun δ ↦ stepCB rHead pAnd3.fwdBits (st δ)
  have hHead2Eq : rHead w3_2 = rCarryOut m r 0 :=
    congrArg r.wires (Fin.ext (by dsimp [fCarryHead, idxCarryHead, fCarryOut, w3_2]))
  have hSt1Not (δ : BitAssignment n) (u : Fin (3 * (m + 1))) (hu : u.val ≠ 2 * m + 2) :
      st1 δ (r u) = st δ (r u) :=
    stepCB_pAnd3_not rHead (st δ) fun e ↦ hu (congrArg Fin.val (r.wires.injective e))
  have hHeadNotTailOut (u : Wire 3) : rHead u ∉ Set.range (rMajOut m rTail).wires := fun ⟨j, e⟩ ↦ by
    have hv : _ ∧ u.val < 3 ∧ j.val < m :=
        ⟨congrArg Fin.val (r.wires.injective e.symm), u.isLt, j.isLt⟩
    dsimp [fCarryHead, idxCarryHead, fCarryTail, idxCarryTail, fMajOut] at hv
    (try split_ifs at hv) <;> omega
  have hTailOutEq (j : Fin m) : rMajOut m rTail j = rCarryOut m r j.succ :=
    congrArg r.wires (Fin.ext (by
      have := j.isLt
      dsimp [fCarryTail, idxCarryTail, fMajOut, fCarryOut, Fin.val_succ]
      (try split_ifs) <;> omega))
  have hNotOut {w} (hw2 : w ≠ rHead w3_2) (hmTail : ¬ ∃ j, rMajOut m rTail j = w) : ¬ ∃ k,
      rCarryOut m r k = w :=
    fun ⟨k, hk⟩ ↦ Fin.cases (motive := (rCarryOut m r · = w → False))
      (fun e ↦ hw2 (e.symm.trans hHead2Eq.symm)) (fun j e ↦ hmTail ⟨j, (hTailOutEq j).trans e⟩) k hk
  have hSt1Head2 (δ) (hz : ∀ q : Fin W, δ (rWork q) = 0) : st1 δ (rHead w3_2) =
      st δ (r ⟨(0 : Fin (m + 1)).val, carryCh_ltA m 0⟩) * st δ (r ⟨m + 1 + (0 : Fin (m + 1)).val,
          carryCh_ltB m 0⟩) := by
    dsimp only [st1]
    rw [stepCB_pAnd3_anc, hHead2Eq, hCln 0 δ hz, zero_add,
      show rHead w3_0 = r ⟨(0 : Fin (m + 1)).val, carryCh_ltA m 0⟩ from rfl,
      show rHead w3_1 = r ⟨m + 1 + (0 : Fin (m + 1)).val, carryCh_ltB m 0⟩ from rfl]
  have hInEq (δ) (hz : ∀ q : Fin W, δ (rWork q) = 0) : stMajIn m rTail st1 δ = stCarryIn m r st δ :=
      funext fun w ↦ by
    have hVA := finBitsVal_succ (fun i : Fin (m + 1) ↦ st δ (r ⟨i.val, carryCh_ltA m i⟩))
    have hVB := finBitsVal_succ (fun i : Fin (m + 1) ↦ st δ (r ⟨m + 1 + i.val, carryCh_ltB m i⟩))
    by_cases hmTail : ∃ j : Fin m, rMajOut m rTail j = w
    · obtain ⟨j, rfl⟩ := hmTail
      have hTB {fT : Fin m → Fin (1 + 3 * m)} {fR : Fin m → Fin (3 * (m + 1))}
          (h : ∀ i, (fT i).val = 1 + i.val ∧ (fR i).val = i.succ.val ∨
            (fT i).val = 1 + m + i.val ∧ (fR i).val = m + 1 + i.succ.val) :
          finBitsVal (fun i ↦ st1 δ (rTail (fT i))) = finBitsVal (fun i ↦ st δ (r (fR i))) :=
        congrArg finBitsVal (funext fun i ↦ (congrArg (st1 δ ∘ r.wires) (Fin.ext (by
          have hv : i.val < m ∧ _ := ⟨i.isLt, h i⟩
          dsimp [fCarryTail, idxCarryTail, Fin.val_succ] at hv ⊢
          (try split_ifs) <;> omega))).trans (hSt1Not δ _ (by
          have hv : i.val < m ∧ _ := ⟨i.isLt, h i⟩
          simp only [Fin.val_succ] at hv
          omega)))
      dsimp only [stMajIn, stCarryIn]
      rw [writeReg_apply_reg, hTailOutEq j, writeReg_apply_reg,
        hTB (fR := fun i ↦ ⟨i.succ.val, carryCh_ltA m i.succ⟩) (fun _ ↦ .inl ⟨rfl, rfl⟩),
        hTB (fR := fun i ↦ ⟨m + 1 + i.succ.val, carryCh_ltB m i.succ⟩) (fun _ ↦ .inr ⟨rfl, rfl⟩),
        show rTail ⟨0, majCh_lt0 m⟩ = rHead w3_2 from
          congrArg r.wires
              (Fin.ext (by dsimp [fCarryTail, idxCarryTail, fCarryHead, idxCarryHead, w3_2])),
        hSt1Head2 δ hz, hVA, hVB, Fin.val_succ]
      exact (majCarryBit_and_succ _ _ _ _ j.val).symm
    · dsimp only [stMajIn, stCarryIn]
      rw [writeReg_apply_of_not_mem _ _ _ w hmTail]
      by_cases hw2 : w = rHead w3_2
      · rw [hw2, hSt1Head2 δ hz, hHead2Eq, writeReg_apply_reg, hVA, hVB]
        exact (majCarryBit_and_zero _ _ _ _).symm
      · dsimp only [st1]
        rw [stepCB_pAnd3_not rHead (st δ) hw2,
            writeReg_apply_of_not_mem _ _ _ w (hNotOut hw2 hmTail)]
  have hTailStep := pWrapMajChain_step m v rWork rTail mid st1 stMid ph₁ ph₂
    (fun j δ hz ↦ (congrArg (st1 δ) (hTailOutEq j)).trans
      ((hSt1Not δ _ (by
        dsimp [fCarryOut, Fin.val_succ]
        omega)).trans (hCln j.succ δ hz)))
    (fun u δ hz ↦ (hFix (fCarryTail m u) δ hz).trans (congrFun (hInEq δ hz).symm _))
    ((mkKetOpW_congr rWork hInEq (fun _ _ ↦ rfl)).symm ▸ hInner)
  let stMidFix := fun δ ↦ writeReg (stMajOut m rTail st1 stMid δ) rHead (fun u ↦ st1 δ (rHead u))
  have hMidFixEq (δ) (hz : ∀ q : Fin W, δ (rWork q) = 0) : stMajOut m rTail st1 stMid δ =
      stMidFix δ :=
    funext fun w ↦ by
      by_cases hmH : ∃ u : Wire 3, rHead u = w
      · obtain ⟨u, rfl⟩ := hmH
        dsimp only [stMidFix, stMajOut]
        rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ (hHeadNotTailOut u),
          show rHead u = r (fCarryHead m u) from rfl, hFix _ δ hz, ← hInEq δ hz]
        exact writeReg_apply_of_not_mem _ _ _ _ (hHeadNotTailOut u)
      · exact (writeReg_apply_of_not_mem _ _ _ w hmH).symm
  refine subspaceStep_of_eq_post (wrapAnd3 v rWork rHead _ st stMidFix ph₁ ph₂ ph₂
    (fun δ hz ↦ hHead2Eq ▸ hCln 0 δ hz) (fun _ _ ↦ writeReg_apply_reg _ _ _ _) (fun _ _ ↦ rfl)
    (subspaceStep_of_eq_post hTailStep (mkKetOpW_congr rWork hMidFixEq (fun _ _ ↦ rfl))))
    (mkKetOpW_congr rWork (fun δ hz ↦ funext fun w ↦ ?_) (fun _ _ ↦ rfl))
  by_cases hw2 : w = rHead w3_2
  · subst hw2
    dsimp only [stCarryOut]
    rw [leg_if_pos rfl, hHead2Eq, writeReg_apply_reg]
  · rw [leg_if_neg hw2, ← hMidFixEq δ hz]
    by_cases hmTail : ∃ j : Fin m, rMajOut m rTail j = w
    · obtain ⟨j, rfl⟩ := hmTail
      dsimp only [stMajOut, stCarryOut]
      rw [writeReg_apply_reg, hTailOutEq j, writeReg_apply_reg, ← hTailOutEq j]
      exact stepCB_pAnd3_not rHead (st δ) hw2
    · simp only [stMajOut, stCarryOut, writeReg_apply_of_not_mem _ _ _ w hmTail,
        writeReg_apply_of_not_mem _ _ _ w (hNotOut hw2 hmTail)]
end QuantumComputation.Specs.PhotochemistrySolution.MidOWCore

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec
open QuantumComputation.Specs
  PhotochemistrySolution.ZeroNEremSpec
theorem foldSum_zero_of_forall {M : ℕ} {f : ℕ → ℕ} (h : ∀ i < M, f i = 0) : foldSum M f = 0 := by
  exact (sum_fin_eq_foldSum M f).symm.trans (Finset.sum_eq_zero fun x _ ↦ h x.val x.isLt)
theorem foldSum_congr {M : ℕ} {f g : ℕ → ℕ} (h : ∀ i < M, f i = g i) : foldSum M f =
    foldSum M g := by
  exact (sum_fin_eq_foldSum M f).symm.trans ((Finset.sum_congr rfl fun x _ ↦
      h x.val x.isLt).trans (sum_fin_eq_foldSum M g))
end QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec

namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
open QuantumComputation.Specs
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.Stage1ZeroNEremSpec
  PhotochemistrySolution.ScreenFermatCore
theorem card_decodeFermatCanon_master (s : ZeroNEremSector) :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeFermatCanon c = s)).card =
    (∑ u1 : Fin 187, fermatPerU1 u1.val s) + cond (eqSec .idle s) 2097120 0 + (foldSum 1024 fun b ↦
    cond (eqSec (kinNucBlkFermat b).1 s) (kinNucBlkFermat b).2 0 + cond (eqSec .idle s)
    (32768 - (kinNucBlkFermat b).2) 0) := by
  have hSlab (u1 M : ℕ) (cell : ℕ → ℕ → ZeroNEremSector × ℕ)
      (fDec : Fin 3 → Fin 3 → Fin (M * 4096) → _)
      (hLe : ∀ z1 z2, (cell z1 z2).2 ≤ M) (hEv : ∀ h1 h2 (u : Fin (M * 4096)), fDec h1 h2 u =
        cond (Nat.blt (u.val / 4096) (cell (h1.val * 64 + (u.val % 4096) % 64)
            (h2.val * 64 + (u.val % 4096) / 64)).2)
          (cell (h1.val * 64 + (u.val % 4096) % 64) (h2.val * 64 + (u.val % 4096) / 64)).1
          (.kin (mkFin234 (47 + u1)) (mkFin3 h1.val))) :
      (∑ h1 : Fin 3, ∑ h2 : Fin 3, (Finset.univ.filter fun u : Fin (M * 4096) ↦ fDec h1 h2 u =
          s).card) =
        foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦
          cond (eqSec (cell z1 z2).1 s) (cell z1 z2).2 0 +
          cond (eqSec (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64))) s) (M - (cell z1 z2).2) 0 := by
    refine (Finset.sum_congr rfl fun h1 _ ↦ Finset.sum_congr rfl fun h2 _ ↦ ?_).trans
      (sum_h1_h2_fin4096 fun z1 z2 ↦
        cond (eqSec (cell z1 z2).1 s) (cell z1 z2).2 0 +
        cond (eqSec (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64))) s) (M - (cell z1 z2).2) 0)
    refine (congrArg Finset.card (Finset.filter_congr fun u _ ↦ by rw [hEv h1 h2 u])).trans ?_
    rw [card_fin_div_lt_of_mod (M := M) (B := 4096) (Nat.succ_pos _)
      (fun r ↦ (cell (h1.val * 64 + r % 64) (h2.val * 64 + r / 64)).1)
      (.kin (mkFin234 (47 + u1)) (mkFin3 h1.val)) s
      (fun r ↦ (cell (h1.val * 64 + r % 64) (h2.val * 64 + r / 64)).2) (fun _ _ ↦ hLe _ _)]
    exact Finset.sum_congr rfl fun r _ ↦
        by rw [show (h1.val * 64 + r.val % 64) / 64 = h1.val by omega]
  rw [card_decodeFermatCanon_split s, card_decodeFermatKinNuc25_eq s]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl fun u1 _ ↦ ?_) rfl) rfl
  simp only [card_decodeFermatCell_split, Finset.sum_add_distrib]
  unfold fermatPerU1
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) (sum_enSlab_eq u1.val s))
      (sum_topSpill_eq u1.val s)
  · refine hSlab u1.val 172032 (eeCellFermat u1.val)
        (fun h1 h2 u ↦ decodeFermatCell u1.val h1.val h2.val u.val)
      (fun _ _ ↦ cond_snd_le (show qEEFermatCoin ≤ 172032 by decide) (Nat.zero_le _)) fun _ _ ⟨uv,
          huv⟩ ↦ ?_
    simp only [decodeFermatCell, Nat.blt_eq.mpr (by omega : uv < 704643072), Bool.cond_true,
      show uv % 64 = (uv % 4096) % 64 by omega, show (uv / 64) % 64 = (uv % 4096) / 64 by omega]
  · refine hSlab u1.val 90112 (nnCellFermat u1.val)
      (fun h1 h2 u ↦ decodeFermatCell u1.val h1.val h2.val (704643072 + u.val))
      (fun _ _ ↦ cond_snd_le (cond_le (by omega) (by omega)) (by omega)) fun _ _ ⟨uv, huv⟩ ↦ ?_
    simp only [decodeFermatCell,
        Bool.eq_false_iff.mpr (mt Nat.blt_eq.mp (by omega : ¬ 704643072 + uv < 704643072)),
      Nat.blt_eq.mpr (by omega : 704643072 + uv < 1073741824), Bool.cond_false, Bool.cond_true,
      show (704643072 + uv) % 64 = (uv % 4096) % 64 by omega,
      show ((704643072 + uv) / 64) % 64 = (uv % 4096) / 64 by omega,
      show 704643072 + uv - 704643072 = uv by omega]
theorem foldSum_cond_const (M : ℕ) (f : ℕ → Bool) (W : ℕ) : (foldSum M fun i ↦ cond (f i) W 0) =
    (foldSum M fun i ↦ cond (f i) 1 0) * W := by
  induction M with
  | zero => simp [foldSum]
  | succ m ih =>
      rw [foldSum_succ, foldSum_succ, ih]
      cases f m <;> simp [Nat.add_one_mul]
theorem foldSum2_cond_and (M1 M2 : ℕ) (f1 : ℕ → Bool) (f2 : ℕ → Bool)
    (W : ℕ) : (foldSum M1 fun i ↦ foldSum M2 fun j ↦ cond (f1 i && f2 j) W 0) = (foldSum M1 fun i ↦
    cond (f1 i) 1 0) * (foldSum M2 fun j ↦ cond (f2 j) 1 0) * W := by
  rw [foldSum_congr (g := fun i ↦ cond (f1 i) ((foldSum M2 fun j ↦ cond (f2 j) 1 0) *
      W) 0) fun i _ ↦ by
    cases f1 i
    · exact foldSum_zero_of_forall fun _ _ ↦ rfl
    · exact foldSum_cond_const M2 f2 W, foldSum_cond_const M1 f1, mul_assoc]
def ultraNucCnt (n : Fin 47) : ℕ := bSum 8 192 0 fun z ↦
    cond ((decodeUltraNuc192 z).1 && ((decodeUltraNuc192 z).2 == n)) 1 0
def pinnedNucCnt (n : Fin 47) : ℕ := bSum 8 192 0 fun z ↦
    cond ((decodePinnedNuc192 z).1 && ((decodePinnedNuc192 z).2 == n)) 1 0
theorem check_ultraNucCnt_a : ((List.range 24).all fun k ↦
    ultraNucCnt (mkFin47 k) == speciesZ (nucSpecies (mkFin47 k))) = true := by rfl
theorem check_ultraNucCnt_b : ((List.range 23).all fun k ↦
    ultraNucCnt (mkFin47 (24 + k)) == speciesZ (nucSpecies (mkFin47 (24 + k)))) = true := by rfl
theorem check_pinnedNucCnt_a : ((List.range 24).all fun k ↦
    pinnedNucCnt (mkFin47 k) == speciesZ (nucSpecies (mkFin47 k))) = true := by rfl
theorem check_pinnedNucCnt_b : ((List.range 23).all fun k ↦
    pinnedNucCnt (mkFin47 (24 + k)) == speciesZ (nucSpecies (mkFin47 (24 + k)))) = true := by rfl
theorem nucCnt_eq_of_checks (cnt : Fin 47 → ℕ)
    (ha : ((List.range 24).all fun k ↦ cnt (mkFin47 k) == speciesZ (nucSpecies (mkFin47 k))) = true)
    (hb : ((List.range 23).all fun k ↦ cnt (mkFin47 (24 + k)) == speciesZ (nucSpecies (mkFin47 (24 +
        k)))) = true)
    (n : Fin 47) : cnt n = speciesZ (nucSpecies n) := by
  have hmk : mkFin47 n.val = n := Fin.ext (Nat.mod_eq_of_lt n.isLt)
  rcases lt_or_ge n.val 24 with h24 | h24
  · exact hmk ▸ beq_iff_eq.mp (List.all_eq_true.mp ha n.val (List.mem_range.mpr h24))
  · have h := beq_iff_eq.mp (List.all_eq_true.mp hb (n.val - 24) (List.mem_range.mpr (by omega)))
    rwa [show 24 + (n.val - 24) = n.val by omega, hmk] at h
theorem ultraNucCnt_eq (n : Fin 47) :
    (foldSum 192 fun z ↦
      let d := decodeUltraNuc192 z
      cond (d.1 && (d.2 == n)) 1 0) = speciesZ (nucSpecies n) :=
  (foldSum_eq_bSum 8 192 _).trans (nucCnt_eq_of_checks ultraNucCnt check_ultraNucCnt_a
      check_ultraNucCnt_b n)
theorem pinnedNucCnt_eq (n : Fin 47) :
    (foldSum 192 fun z ↦
      let d := decodePinnedNuc192 z
      cond (d.1 && (d.2 == n)) 1 0) = speciesZ (nucSpecies n) :=
  (foldSum_eq_bSum 8 192 _).trans (nucCnt_eq_of_checks pinnedNucCnt check_pinnedNucCnt_a
      check_pinnedNucCnt_b n)
theorem nnCellFermat_eq_zero_of_not_nn (u1 z1 z2 : ℕ) (s : ZeroNEremSector)
    (hs : ∀ a b c, s ≠ .nn a b c) : cond (eqSec (nnCellFermat u1 z1 z2).1 s)
    (nnCellFermat u1 z1 z2).2 0 = 0 := by
  unfold nnCellFermat
  dsimp only
  cases (decodeUltraNuc192 z1).1 && (decodePinnedNuc192 z2).1 &&
      (((decodeUltraNuc192 z1).2 == (decodePinnedNuc192 z2).2) == false) <;>
    cases he : eqSec _ s <;> first | rfl | exact absurd ((eqSec_iff _ _).mp he).symm (hs _ _ _)
theorem enCellFermat_eq_zero_of_not_en (u1 h2 z1 : ℕ) (s : ZeroNEremSector)
    (hs : ∀ a b, s ≠ .en a b) : cond (eqSec (enCellFermat u1 h2 z1).1 s)
    (enCellFermat u1 h2 z1).2 0 = 0 := by
  unfold enCellFermat
  dsimp only
  cases (decodeUltraNuc192 z1).1 <;> cases he : eqSec _ s <;>
    first | rfl | exact absurd ((eqSec_iff _ _).mp he).symm (hs _ _)
theorem kinNucBlkFermat_eq_zero_of_not_kin (b : ℕ) (s : ZeroNEremSector)
    (hs : ∀ i w, s ≠ .kin i w) : cond (eqSec (kinNucBlkFermat b).1 s) (kinNucBlkFermat b).2 0 =
    0 := by
  have htag : (kinNucBlkFermat b).2 = 0 ∨ ∃ i w, (kinNucBlkFermat b).1 = .kin i w := by
    unfold kinNucBlkFermat
    dsimp only [cond]
    repeat' first | exact Or.inl rfl | exact Or.inr ⟨_, _, rfl⟩ | split
  rcases htag with hz | ⟨i, w, hkw⟩
  · exact hz ▸ Bool.rec rfl rfl (eqSec _ s)
  · rw [hkw]
    cases he : eqSec (.kin i w) s <;>
        first | rfl | exact absurd ((eqSec_iff _ _).mp he).symm (hs i w)
theorem mkFin187_of_lt {x : ℕ} (hx : x < 187) : mkFin187 x = ⟨x, hx⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hx)
theorem eeCellFermat_pair_sum (n1 : Fin 47) {a b : Fin 187} (hab : a < b) : (foldSum 192 fun z1 ↦
    foldSum 192 fun z2 ↦
    cond (eqSec (eeCellFermat a.val z1 z2).1 (.ee n1 a b)) (eeCellFermat a.val z1 z2).2 0) =
    speciesZ (nucSpecies n1) * qEEFermatCoin ∧ (foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦
    cond (eqSec (eeCellFermat b.val z1 z2).1 (.ee n1 a b)) (eeCellFermat b.val z1 z2).2 0) =
    speciesZ (nucSpecies n1) * qEEFermatCoin := by
  have hHalf (u v : Fin 187) (huv : v.val ≠ u.val) (hmin : min u.val v.val = a.val)
      (hmax : max u.val v.val = b.val) (hNot : ∀ z2 < 187, z2 ≠ v.val →
        ((mkFin187 (min u.val z2) == a) && (mkFin187 (max u.val z2) == b)) = false) :
      (foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦
        cond (eqSec (eeCellFermat u.val z1 z2).1 (.ee n1 a b)) (eeCellFermat u.val z1 z2).2 0) =
        speciesZ (nucSpecies n1) * qEEFermatCoin := by
    have hv1 : (foldSum 192 fun j ↦ cond (j == v.val) 1 0) = 1 := by
      rw [foldSum_eq_single (k := v.val) (Nat.lt_trans v.isLt (by omega))]
      · simp
      · exact fun _ _ hj ↦ by simp [beq_eq_false_iff_ne.mpr hj]
    have hTerm (z1 z2 : ℕ) : cond (eqSec (eeCellFermat u.val z1 z2).1 (.ee n1 a b))
        (eeCellFermat u.val z1 z2).2 0 =
        cond (((decodeUltraNuc192 z1).1 && ((decodeUltraNuc192 z1).2 == n1)) &&
            (z2 == v.val)) qEEFermatCoin 0 := by
      unfold eeCellFermat
      dsimp only
      cases (decodeUltraNuc192 z1).1
      · rfl
      · simp only [Bool.true_and]
        cases hz2 : (z2 == v.val)
        · simp only [Bool.and_false, Bool.cond_false]
          cases hltz : Nat.blt z2 187 && ((z2 == u.val) == false)
          · rfl
          · simp [eqSec, Bool.and_assoc, hNot z2 (Nat.blt_eq.mp (Bool.and_eq_true_iff.mp hltz).1)
                (beq_eq_false_iff_ne.mp hz2)]
        · rw [beq_iff_eq.mp hz2]
          simp [Nat.blt_eq.mpr v.isLt, beq_eq_false_iff_ne.mpr huv, hmin, hmax,
              mkFin187_of_lt a.isLt, mkFin187_of_lt b.isLt, eqSec]
    rw [foldSum_congr fun z1 _ ↦ foldSum_congr fun z2 _ ↦ hTerm z1 z2, foldSum2_cond_and, hv1,
        mul_one, ultraNucCnt_eq]
  refine ⟨hHalf a b (ne_of_gt hab) (Nat.min_eq_left (le_of_lt hab))
      (Nat.max_eq_right (le_of_lt hab)) fun z2 hzlt hzne ↦ ?_,
    hHalf b a (ne_of_lt hab) (Nat.min_eq_right (le_of_lt hab))
      (Nat.max_eq_left (le_of_lt hab)) fun z2 _ hzne ↦ ?_⟩
  · rw [mkFin187_of_lt (max_lt a.isLt hzlt), beq_eq_false_iff_ne.mpr
      (Fin.ne_of_val_ne (i := ⟨_, _⟩) (show max a.val z2 ≠ b.val by omega)), Bool.and_false]
  · rw [mkFin187_of_lt (min_lt_iff.mpr (.inl b.isLt)), beq_eq_false_iff_ne.mpr
      (Fin.ne_of_val_ne (i := ⟨_, _⟩) (show min b.val z2 ≠ a.val by omega)), Bool.false_and]
attribute [local irreducible] foldSum mkFin187 mkFin47 mkFin234 decodeUltraNuc192
theorem sum_fin187_eq_pair {f : Fin 187 → ℕ} {a b : Fin 187} (hab : a ≠ b)
    (h0 : ∀ x : Fin 187, x ≠ a → x ≠ b → f x = 0) : (∑ x : Fin 187, f x) = f a + f b := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
    Finset.sum_eq_zero fun x hx ↦
      h0 x (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1 (Finset.mem_erase.mp hx).1,
    Nat.add_zero]
theorem eeMinMax_beq_false_of_other (e1 e2 u1 : Fin 187) (h1 : u1 ≠ e1) (h2 : u1 ≠ e2)
    (z2 : ℕ) : ((mkFin187 (min u1.val z2) == e1) && (mkFin187 (max u1.val z2) == e2)) = false := by
  rcases Nat.le_total u1.val z2 with hle | hle
  · rw [Nat.min_eq_left hle, mkFin187_of_lt u1.isLt, beq_eq_false_iff_ne.mpr h1, Bool.false_and]
  · rw [Nat.max_eq_left hle, mkFin187_of_lt u1.isLt, beq_eq_false_iff_ne.mpr h2, Bool.and_false]
theorem bool_and_eq_false_of_imp (x y : Bool) (h : x = true → y = true → False) : (x && y) =
    false := by
  cases x <;> cases y <;> first | rfl | exact (h rfl rfl).elim
theorem cond_and3_eq_zero {a b c : Bool} (q : ℕ) (h : (b && c) = false) : cond (a && b && c) q 0 =
    0 := by
  simp [Bool.and_assoc, h]
theorem fin187_beq_and_false_of_lt {a b e1 e2 : Fin 187} (hab : a.val < b.val)
    (hgele : e2.val ≤ e1.val) : ((a == e1) && (b == e2)) = false :=
  bool_and_eq_false_of_imp _ _ fun h1 h2 ↦ by
    linarith [congrArg Fin.val (beq_iff_eq.mp h1), congrArg Fin.val (beq_iff_eq.mp h2)]
theorem eeMinMax_beq_false_of_ge {e1 e2 : Fin 187} (hgele : e2.val ≤ e1.val) (u1 z2F : Fin 187)
    (hzne : z2F.val ≠ u1.val) : ((mkFin187 (min u1.val z2F.val) == e1) &&
    (mkFin187 (max u1.val z2F.val) == e2)) = false := by
  refine fin187_beq_and_false_of_lt ?_ hgele
  rcases Nat.le_total u1.val z2F.val with hle | hle <;>
    simp [hle, mkFin187_of_lt u1.isLt, mkFin187_of_lt z2F.isLt] <;> omega
theorem fermatPerU1_ee (n1 : Fin 47) (e1 e2 u1 : Fin 187) : fermatPerU1 u1.val (.ee n1 e1 e2) =
    foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦
    cond (eqSec (eeCellFermat u1.val z1 z2).1 (.ee n1 e1 e2)) (eeCellFermat u1.val z1 z2).2 0 := by
  unfold fermatPerU1
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (foldSum_congr fun _ _ ↦ foldSum_congr fun _ _ ↦ Nat.add_zero _)
    (foldSum_zero_of_forall fun _ _ ↦ foldSum_zero_of_forall fun _ _ ↦ congrArg (· + 0)
      (nnCellFermat_eq_zero_of_not_nn _ _ _ (.ee n1 e1 e2) fun _ _ _ h ↦ nomatch h)))
    (foldSum_zero_of_forall fun _ _ ↦ foldSum_zero_of_forall fun _ _ ↦ congrArg (· + 0)
      (enCellFermat_eq_zero_of_not_en _ _ _ (.ee n1 e1 e2) fun _ _ h ↦ nomatch h))) rfl
theorem eeCellFermat_zero_of_false (n1 : Fin 47) (e1 e2 u1 : Fin 187)
    (hf : ∀ z2 < 187, z2 ≠ u1.val →
      ((mkFin187 (min u1.val z2) == e1) && (mkFin187 (max u1.val z2) == e2)) = false) :
    (foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦
      cond (eqSec (eeCellFermat u1.val z1 z2).1 (.ee n1 e1 e2))
        (eeCellFermat u1.val z1 z2).2 0) = 0 :=
  foldSum_zero_of_forall fun z1 _ ↦ foldSum_zero_of_forall fun z2 _ ↦ by
    unfold eeCellFermat
    dsimp only
    cases (decodeUltraNuc192 z1).1
    · rfl
    · simp only [Bool.true_and]
      cases hltz : Nat.blt z2 187 && ((z2 == u1.val) == false)
      · rfl
      · exact cond_and3_eq_zero qEEFermatCoin (hf z2 (Nat.blt_eq.mp (Bool.and_eq_true_iff.mp
            hltz).1)
          (beq_eq_false_iff_ne.mp (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hltz).2)))
theorem eeCellFermat_other_zero (n1 : Fin 47) (e1 e2 u1 : Fin 187) (h1 : u1 ≠ e1)
    (h2 : u1 ≠ e2) : (foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦
    cond (eqSec (eeCellFermat u1.val z1 z2).1 (.ee n1 e1 e2)) (eeCellFermat u1.val z1 z2).2 0) =
    0 :=
  eeCellFermat_zero_of_false n1 e1 e2 u1 fun z _ _ ↦ eeMinMax_beq_false_of_other e1 e2 u1 h1 h2 z
theorem eeCellFermat_ge_zero (n1 : Fin 47) {e1 e2 : Fin 187} (hgele : e2.val ≤ e1.val)
    (u1 : Fin 187) : (foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦
    cond (eqSec (eeCellFermat u1.val z1 z2).1 (.ee n1 e1 e2)) (eeCellFermat u1.val z1 z2).2 0) =
    0 :=
  eeCellFermat_zero_of_false n1 e1 e2 u1 fun z hz h ↦ eeMinMax_beq_false_of_ge hgele u1 ⟨z, hz⟩ h
theorem add_zero_zero {a b c r : ℕ} (ha : a = r) (hb : b = 0) (hc : c = 0) : a + b + c = r := by
  rw [ha, hb, hc, Nat.add_zero]
theorem count_fermat_ee (n1 : Fin 47)
    (e1 e2 : Fin 187) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeFermatCanon c =
    .ee n1 e1 e2)).card = (if e1 < e2 then wEESpeciesFermatCoin (nucSpecies n1) else 0) := by
  rw [card_decodeFermatCanon_master (.ee n1 e1 e2)]
  refine add_zero_zero ((Finset.sum_congr rfl fun u1 _ ↦ fermatPerU1_ee n1 e1 e2 u1).trans ?_) rfl
    (foldSum_zero_of_forall fun b _ ↦ congrArg (· + 0)
      (kinNucBlkFermat_eq_zero_of_not_kin b (.ee n1 e1 e2) fun _ _ h ↦ nomatch h))
  split
  · next hlt =>
    refine (sum_fin187_eq_pair (fun h ↦ Nat.ne_of_lt hlt (congrArg Fin.val h))
      (eeCellFermat_other_zero n1 e1 e2)).trans
      ((congrArg₂ (· + ·)
          (eeCellFermat_pair_sum n1 hlt).1 (eeCellFermat_pair_sum n1 hlt).2).trans ?_)
    generalize nucSpecies n1 = sp
    fin_cases sp <;> simp [speciesZ, qEEFermatCoin, wEESpeciesFermatCoin]
  · next hlt => exact Finset.sum_eq_zero fun u1 _ ↦ eeCellFermat_ge_zero n1 (Nat.not_lt.mp hlt) u1
attribute [local irreducible] decodePinnedNuc192
theorem cond_eq_zero_of_and_left {x : Bool} (hx : x = false) (y : Bool)
    (q : ℕ) : cond (x && y) q 0 = 0 := by
  exact hx ▸ rfl
theorem nnPair_beq_false_of_ge (a b n1 n2 : Fin 47) (e1 u1 : Fin 187) (hgele : n2.val ≤ n1.val) :
    cond ((a == b) == false)
      (cond (eqSec (let cLt := Nat.blt b.val a.val
                    ZeroNEremSector.nn (cond cLt b a) (cond cLt a b) (mkFin187 u1.val))
                        (.nn n1 n2 e1))
        (cond (Nat.blt b.val a.val) 83543 83542) 0) 0 = 0 := by
  have hOrd {x y : Fin 47} (hxy : x.val < y.val) : ((x == n1) && (y == n2)) = false :=
    bool_and_eq_false_of_imp _ _ fun h1 h2 ↦ by
      linarith [congrArg Fin.val (beq_iff_eq.mp h1), congrArg Fin.val (beq_iff_eq.mp h2)]
  by_cases hab : a = b
  · simp [hab]
  · rw [beq_eq_false_iff_ne.mpr hab]
    cases hc : Nat.blt b.val a.val <;> dsimp only [cond, eqSec]
    · exact cond_eq_zero_of_and_left (hOrd (Nat.lt_of_le_of_ne
        (Nat.not_lt.mp fun h ↦ Bool.noConfusion (hc.symm.trans (Nat.blt_eq.mpr h)))
            (Fin.val_ne_of_ne hab))) _ _
    · exact cond_eq_zero_of_and_left (hOrd (Nat.blt_eq.mp hc)) _ _
open PrimitiveGate PhotochemistrySolution.CoinWrap
theorem xagEnv_congr_step {c N : ℕ} {gates : Fin N → ℕ × ℕ} :
    ∀ {k₁ k₂ : ℕ} (_ : k₁ = k₂) (hk₁ : k₁ ≤ N) (hk₂ : k₂ ≤ N), xagEnv c N gates k₁ hk₁ =
        xagEnv c N gates k₂ hk₂
  | _, _, rfl, _, _ => rfl
theorem xagEnv_testBit_above {c N : ℕ} {gates : Fin N → ℕ × ℕ} (hc : c < 2 ^ 41) :
    ∀ (k : ℕ) (hk : k ≤ N) {b : ℕ}, 42 + k ≤ b → (xagEnv c N gates k hk).testBit b = false :=
  fun k hk {_} hb ↦ (xagEnv_invariant ⟨c, hc⟩ N gates k hk).2.1 _ hb
theorem xagEnv_mono_below {c N : ℕ} {gates : Fin N → ℕ × ℕ} {k b : ℕ} (hb : b < 42 + k) :
    ∀ (d : ℕ) (hd : k + d ≤ N), (xagEnv c N gates (k + d) hd).testBit b =
        (xagEnv c N gates k (Nat.le_of_add_right_le hd)).testBit b
  | 0, _ => rfl
  | d + 1, hd => by
      rw [xagEnv_congr_step (show k + (d + 1) = (k + d) + 1 by omega) hd (by omega)]
      dsimp only [xagEnv]
      split_ifs <;> simp [Nat.testBit_or, Nat.testBit_shiftLeft, show ¬(b ≥ 42 + (k + d)) by omega,
          xagEnv_mono_below hb d _]
theorem ite_or_unit_testBit (e m : ℕ) (b : Bool) (h0 : e.testBit m = false) :
    (if b = true then e ||| 1 <<< m else e).testBit m = b := by
  cases b <;> simp [h0, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_zero]
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
end

end ScopedLocalHelpers
end
