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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.HadCut570Tail3D

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section SelectHoistLemmas
local instance (priority := 1000000) instNeZeroTwoPow_SelectHoistLemmas (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `SELECT` Hoist & Twist-Slot Commutation Lemmas (`SelectHoistLemmas`)

Standalone foundational lemmas for `SelectStitch` and `SelectExtStitch`
(`mWork = 137`, `k_idle = 11`, `Q = 4,265`):
1. Exact twist-slot commutations of `(uVepFusedTwistRestCut80 (trunc36Cfg c) * uBarrelFast (le_refl
80)).1`
   with `slotBitProj (iSlot2 80) 0`, `slotBitProj (iSlot1 80) 1`, and `slotBitProj (iSlot0 80) 0`.
2. Parametric hoisted `SELECT` subspace intertwiners and commutations (`hSelCtrlE` on `E_ctrl3Ext`,
   `hSelCatE` on `E_segExt`, `hSelSlack010` on `pCoinSlack010Orig`, and `hSelIdle` on `rPGIdleOrig`)
   together with concrete factor-level dischargers for `rCoreSeg`, `rCTSeg`, `rQSeg`,
   `uTrailCliffordXor80`, and `unitaryConj (uBarrelFast (le_refl 80)) uPosPhase0`.
-/

public section

namespace SelectHoistLemmas

section ConfigSelectHoistLemmas

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 65536

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority :=
  1000000) instLoc_SelectHoistLemmas_1InstNeZeroTwoPowSelectHoi (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix SpecsAux.SpecMirror
open PosMomSelectSandwich
open FullSysCatSegmentBridge
open SingleCatSpine
open SingleCatClosure
open InterWalkRSum42Hoist
open Barrel3PassSelectStitch
open Leaf4Ext48TopStitch

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Reducible local `(fullSysCoreWires 80 + mCat)` embedding inside `fullSysCoreWires 80 + 48`
via `rTopCatSlice`, definitionally matching `SelectStitch.rCoreTopCatInCT`. -/
abbrev rCoreTopCatInCT (mCat : ℕ) (hmCat : mCat ≤ 48) :
    QRegister (fullSysCoreWires 80 + mCat) (fullSysCoreWires 80 + 48) :=
  rCoreInCT80.concat
    ((QRegister.block (fullSysCoreWires 80) 48 le_rfl).compose (rTopCatSlice mCat 48 hmCat))
    (by
      rw [QRegister.disjoint_iff]
      intro i j hij
      have hv := congrArg Fin.val hij
      have hi := i.isLt
      have hj := (rTopCatSlice mCat 48 hmCat j).isLt
      dsimp [rCoreInCT80, QRegister.compose_apply, QRegister.block,
        Fin.natAddEmb, Fin.castLEEmb] at hv
      omega)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Local `3`-wire `[3951 .. 3954)` control register inside `fullSysBEWires 80 + 48`. -/
abbrev rCtrl3InSeg : QRegister 3 (fullSysBEWires 80 + 48) := rCoreSeg.compose rCtrl3InCore

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem rSegFull_eq_rAct0_compose_rSegOrig : rSegFull = rAct0.compose rSegOrig := rfl

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem rSegFull_compose_rCTSeg_rCoreTopCatInCT (mCat : ℕ) (hmCat : mCat ≤ 48) :
    rSegFull.compose (rCTSeg.compose (rCoreTopCatInCT mCat hmCat)) =
      rCoreTopCatFull mCat hmCat := by
  rw [← QRegister.compose_assoc, rSegFull_compose_rCTSeg]
  refine qreg_ext fun idx ↦ Fin.addCases (fun i ↦ ?_) (fun t ↦ ?_) idx
  · change rCTFull (rCoreTopCatInCT mCat hmCat (Fin.castAdd mCat i)) =
      rCoreTopCatFull mCat hmCat (Fin.castAdd mCat i)
    rw [rCoreTopCatInCT, QRegister.concat_apply_left, rCoreTopCatFull, QRegister.concat_apply_left,
      show rCoreInCT80 i = Fin.castAdd 48 i from Fin.ext (by simp [rCoreInCT80]),
      rCTFull, QRegister.concat_apply_left]
  · change rCTFull (rCoreTopCatInCT mCat hmCat (Fin.natAdd (fullSysCoreWires 80) t)) =
      rCoreTopCatFull mCat hmCat (Fin.natAdd (fullSysCoreWires 80) t)
    rw [rCoreTopCatInCT, QRegister.concat_apply_right, rCoreTopCatFull,
      QRegister.concat_apply_right, show ((QRegister.block (fullSysCoreWires 80) 48
        le_rfl).compose (rTopCatSlice mCat 48 hmCat)) t = Fin.natAdd (fullSysCoreWires 80)
        (rTopCatSlice mCat 48 hmCat t) from Fin.ext (by simp [QRegister.block]),
      rCTFull, QRegister.concat_apply_right]
    rfl

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem rSegFull_compose_rCtrl3InSeg : rSegFull.compose rCtrl3InSeg = rUnusedCtrl3Full := by
  apply qreg_ext; intro t
  change rAct0 (rSegOrig (rCoreSeg (rCtrl3InCore t))) = rUnusedCtrl3Full t
  have hbe : rCoreSeg (rCtrl3InCore t) = Fin.castAdd 48 (beCoreBlock 80 (rCtrl3InCore t)) := by
    ext; simp [rCoreSeg, rBE80, rBESelLoc, QRegister.block]
  rw [hbe, rSegOrig, rBECatSingleCatInAct, QRegister.concat_apply_left]
  ext; rw [rAct0_val_eq, rBEOrig_val_eq, rUnusedCtrl3Full_val_eq]
  simp [beCoreBlock, rCtrl3InCore]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem rCoreTopCatFull_disj_rPGIdle (k_idle mCat : ℕ) (hkc : k_idle + mCat ≤ 48) :
    (rCoreTopCatFull mCat (by omega)).DisjointWires (rPGIdle k_idle (by omega)) := by
  have hCIdle : rCoreFull.DisjointWires (rPGIdle k_idle (by omega)) :=
    disj_of_val_ne fun i q ↦ by
      rw [rCoreFull_val_eq, rPGIdle_val_eq]
      have hi := i.isLt; have hq := q.isLt
      dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
        SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
      omega
  exact disjointWires_concat_left _ hCIdle (topCat_disj_rPGIdle k_idle mCat hkc)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem rSegOrig_disj_rSlack3Orig : rSegOrig.DisjointWires rSlack3Orig := by
  have hBE_slk : rBEOrig.DisjointWires rSlack3Orig :=
    disj_of_val_ne fun i t ↦ by
      rw [rSlack3Orig_val_eq]
      have := rBEOrig_val_lt_4034 i; have := t.isLt; omega
  have hCat_slk : (rCatTotInSingleCat 80 48 40).DisjointWires rSlack3Orig := by
    rw [rCatTotInSingleCat80_eq_rPG48Orig]; exact hPG48Orig_disj_Slack3Orig
  exact disjointWires_concat_left _ hBE_slk hCat_slk

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem rSegFull_comm_pSlack3Zero (U : Unitary (2 ^ (fullSysBEWires 80 + 48))) :
    (rSegFull.embedUnitary U).1 * pSlack3Zero = pSlack3Zero * (rSegFull.embedUnitary U).1 := by
  have hDisj : rSegFull.DisjointWires rSlack3Full :=
    disjointWires_compose_of_disjoint rAct0 rSegOrig_disj_rSlack3Orig
  rw [QRegister.embedUnitary_val]
  exact (CommutesWithReg.of_disjoint hDisj U.1).comm_basisOutcomeProjector 0

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem commutesWithReg_unitary_inv {k n : ℕ} {r : QRegister k n} {U : Unitary (2 ^ n)}
    (hU : CommutesWithReg r U.1) : CommutesWithReg r (U⁻¹).1 := by
  have hEq : (U⁻¹).1 = U.1ᴴ := Matrix.star_eq_conjTranspose U.1
  rw [hEq]
  exact hU.conjTranspose

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem unitary_inv_comm_selfAdj {D : ℕ} {U : Unitary D} {P : Operator D} (hP : Pᴴ = P)
    (hU : U.1 * P = P * U.1) : (U⁻¹).1 * P = P * (U⁻¹).1 := by
  have hInv : (U⁻¹).1 = U.1ᴴ := Matrix.star_eq_conjTranspose U.1
  rw [hInv]
  simpa only [Matrix.conjTranspose_mul, hP] using (congrArg Matrix.conjTranspose hU).symm

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem commutesWithReg_rCtrl3InSeg_rCoreSeg {U : Unitary (2 ^ (fullSysCoreWires 80))}
    (hU : CommutesWithReg rCtrl3InCore U.1) : CommutesWithReg rCtrl3InSeg
    (rCoreSeg.embedUnitary U).1 := CommutesWithReg.embedMatrix rCoreSeg hU

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Coin-`010` slack projector on `fullSysCoreWires 80`. -/
noncomputable abbrev pCoinSlack010Core : Operator (2 ^ (fullSysCoreWires 80)) :=
  slotBitProj (iSlot2 80) 0 * slotBitProj (iSlot1 80) 1 * slotBitProj (iSlot0 80) 0

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Coin-`010` slack projector embedded into `fullSysBEWires 80 + 48`. -/
noncomputable abbrev pCoinSlack010Seg : Operator (2 ^ (fullSysBEWires 80 + 48)) :=
  rCoreSeg.embedMatrix pCoinSlack010Core

set_option exponentiation.threshold 4200 in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem rSegOrig_embedMatrix_pCoinSlack010Seg :
    rSegOrig.embedMatrix pCoinSlack010Seg = pCoinSlack010Orig := by
  unfold pCoinSlack010Seg pCoinSlack010Core pCoinSlack010Orig
  rw [← QRegister.embedMatrix_compose, rSegOrig_compose_rCoreLoc]
  unfold rCoreOrig rBEOrig
  rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul,
    embed_slotBitProj_eq_singleton_singleCat (iSlot2 80) (qCoin2InSingleCat 80 48 40) (by decide) 0,
    embed_slotBitProj_eq_singleton_singleCat (iSlot1 80) (qCoin1InSingleCat 80 48 40) (by decide) 1,
    embed_slotBitProj_eq_singleton_singleCat (iSlot0 80) (qCoin0InSingleCat 80 48 40) (by decide) 0]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Generic `hSelSlack010` identity for hoisted `SELECT` on `pCoinSlack010Orig`. -/
theorem hoistedSelect_mul_pCoinSlack010Orig
    (uTwSeg uMidSeg : Unitary (2 ^ (fullSysBEWires 80 + 48)))
    (hTwSlack : uTwSeg.1 * pCoinSlack010Seg = pCoinSlack010Seg * uTwSeg.1)
    (hMidSlack : uMidSeg.1 * pCoinSlack010Seg = pCoinSlack010Seg) :
    (rSegOrig.embedUnitary (uTwSeg⁻¹ * (uMidSeg * uTwSeg))).1 * pCoinSlack010Orig =
      pCoinSlack010Orig := by
  rw [← rSegOrig_embedMatrix_pCoinSlack010Seg, QRegister.embedUnitary_val,
    ← rSegOrig.embedMatrix_mul]
  apply congrArg rSegOrig.embedMatrix
  have hInv : (uTwSeg⁻¹).1 * uTwSeg.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  calc (uTwSeg⁻¹ * (uMidSeg * uTwSeg)).1 * pCoinSlack010Seg
    _ = (uTwSeg⁻¹).1 * (uMidSeg.1 * (uTwSeg.1 * pCoinSlack010Seg)) := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (uTwSeg⁻¹).1 * ((uMidSeg.1 * pCoinSlack010Seg) * uTwSeg.1) := by
          rw [hTwSlack]; simp only [Matrix.mul_assoc]
    _ = ((uTwSeg⁻¹).1 * uTwSeg.1) * pCoinSlack010Seg := by
          rw [hMidSlack, ← hTwSlack]; simp only [Matrix.mul_assoc]
    _ = pCoinSlack010Seg := by rw [hInv, Matrix.one_mul]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem embedMatrix_slotBitProj {k n : ℕ} (r : QRegister k n) (w : Wire k) (b : Fin 2) :
    r.embedMatrix (slotBitProj w b) = slotBitProj (r w) b := by
  simp only [slotBitProj, QRegister.embedMatrix_diagonal, QRegister.basisBits_extractIndex]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem disjointWires_singleton_of_not_mem {m n : ℕ} {s : QRegister m n} {w : Wire n}
    (hwOut : w ∉ Set.range s.wires) : s.DisjointWires (QRegister.singleton w) := by
  rw [QRegister.disjoint_iff]
  intro i _ hij
  exact hwOut ⟨i, hij⟩

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem embedMatrix_comm_slotBitProj_of_disjoint {m n : ℕ} {s : QRegister m n} {w : Wire n}
    (hsr : s.DisjointWires (QRegister.singleton w)) (A : Operator (2 ^ m)) (b : Fin 2) :
    s.embedMatrix A * slotBitProj w b = slotBitProj w b * s.embedMatrix A := by
  have hEmb : (QRegister.singleton w).embedMatrix (slotBitProj 0 b) = slotBitProj w b :=
    embedMatrix_slotBitProj (QRegister.singleton w) 0 b
  rw [← hEmb]
  exact s.embedMatrix_comm_of_disjoint (QRegister.singleton w) hsr A (slotBitProj 0 b)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem embedMatrix_comm_slotBitProj_of_not_mem {m n : ℕ} {s : QRegister m n} {w : Wire n}
    (hwOut : w ∉ Set.range s.wires) (A : Operator (2 ^ m)) (b : Fin 2) :
    s.embedMatrix A * slotBitProj w b = slotBitProj w b * s.embedMatrix A :=
  embedMatrix_comm_slotBitProj_of_disjoint (disjointWires_singleton_of_not_mem hwOut) A b

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pCoinSlack010Core_conjTranspose : pCoinSlack010Coreᴴ = pCoinSlack010Core := by
  rw [pCoinSlack010Core, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    slotBitProj_conjTranspose, slotBitProj_conjTranspose, slotBitProj_conjTranspose]
  unfold slotBitProj
  simp only [Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ by ring)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem rSegOrig_compose_rCTSeg : rSegOrig.compose rCTSeg = rCTOrig := by
  apply qreg_ext; intro idx
  apply rAct0.wires.injective
  have h :=
    congrArg (fun r : QRegister (fullSysCoreWires 80 + 48) kFull80 ↦ r idx) rSegFull_compose_rCTSeg
  rwa [rCTFull_eq_compose] at h

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem commutesWithReg_rPGIdleOrig_rCTSeg_catSlice_ge (k_idle mCat : ℕ) (hk : k_idle ≤ 48)
    (s : QRegister mCat 48) (hs : ∀ t : Fin mCat, k_idle ≤ (s t).val) (hDisj :
    rCoreInCT80.DisjointWires ((QRegister.block (fullSysCoreWires 80) 48 le_rfl).compose s))
    (U : Unitary (2 ^ (fullSysCoreWires 80 + mCat))) : CommutesWithReg
    (rPGIdleOrig k_idle hk) (rSegOrig.embedUnitary (rCTSeg.embedUnitary ((rCoreInCT80.concat
    ((QRegister.block (fullSysCoreWires 80) 48 le_rfl).compose s) hDisj).embedUnitary U))).1
    := by
  rw [← QRegister.embedUnitary_compose, rSegOrig_compose_rCTSeg,
    ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
  refine CommutesWithReg.of_disjoint (disj_of_val_ne fun idx q ↦ ?_) U.1
  rw [rPGIdleOrig_val_eq]; have hq := q.isLt
  refine Fin.addCases (fun i ↦ ?_) (fun t ↦ ?_) idx
  · change (rCTOrig ((rCoreInCT80.concat _ hDisj) (Fin.castAdd mCat i))).val ≠ 4035 + q.val
    rw [QRegister.concat_apply_left]
    have hci : rCoreInCT80 i = Fin.castAdd 48 i := by ext; simp [rCoreInCT80]
    rw [hci, rCTOrig, QRegister.concat_apply_left, rCoreOrig_val_eq]
    have hi := i.isLt
    dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
      SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
    omega
  · change (rCTOrig ((rCoreInCT80.concat _ hDisj) (Fin.natAdd (fullSysCoreWires 80) t))).val ≠ 4035
      + q.val
    rw [QRegister.concat_apply_right]
    have hct : ((QRegister.block (fullSysCoreWires 80) 48 le_rfl).compose s) t =
        Fin.natAdd (fullSysCoreWires 80) (s t) := by ext; simp [QRegister.block]
    rw [hct, rCTOrig, QRegister.concat_apply_right, rPG48Orig_val_eq]
    have := hs t; omega

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem commutesWithReg_rPGIdleOrig_rCoreSeg (k_idle : ℕ) (hk : k_idle ≤ 48)
    (U : Unitary (2 ^ (fullSysCoreWires 80))) : CommutesWithReg (rPGIdleOrig k_idle hk)
    (rSegOrig.embedUnitary (rCoreSeg.embedUnitary U)).1 := by
  rw [← QRegister.embedUnitary_compose, rSegOrig_compose_rCoreLoc, QRegister.embedUnitary_val]
  refine CommutesWithReg.of_disjoint (disj_of_val_ne fun i q ↦ ?_) U.1
  rw [rCoreOrig_val_eq, rPGIdleOrig_val_eq]
  have hi := i.isLt; have hq := q.isLt
  dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
    SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
  omega

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Generic `hSelIdle` commutation for hoisted `SELECT` on `rPGIdleOrig k_idle hk`. -/
theorem commutesWithReg_rPGIdleOrig_hoistedSelect (k_idle mCatTw : ℕ) (hk : k_idle ≤ 48)
    (hkcTw : k_idle + mCatTw ≤ 48) (uTwCatSub : Unitary (2 ^ (fullSysCoreWires 80 + mCatTw)))
    (uMidSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))) (hMidIdle : CommutesWithReg
    (rPGIdleOrig k_idle hk) (rSegOrig.embedUnitary uMidSeg).1) : CommutesWithReg
    (rPGIdleOrig k_idle hk) (rSegOrig.embedUnitary ((rCTSeg.embedUnitary ((rCoreTopCatInCT
    mCatTw (by omega)).embedUnitary uTwCatSub))⁻¹ * (uMidSeg * rCTSeg.embedUnitary
    ((rCoreTopCatInCT mCatTw (by omega)).embedUnitary uTwCatSub)))).1 := by
  have hTw : CommutesWithReg (rPGIdleOrig k_idle hk)
      (rSegOrig.embedUnitary
        (rCTSeg.embedUnitary ((rCoreTopCatInCT mCatTw (by omega)).embedUnitary uTwCatSub))).1 := by
    refine commutesWithReg_rPGIdleOrig_rCTSeg_catSlice_ge k_idle mCatTw hk
      (rTopCatSlice mCatTw 48 (by omega)) (fun t ↦ ?_) _ uTwCatSub
    have htop : (rTopCatSlice mCatTw 48 (by omega) t).val = (48 - mCatTw) + t.val := by
      simp [rTopCatSlice]
    rw [htop]; omega
  have hTwInv : CommutesWithReg (rPGIdleOrig k_idle hk)
      (rSegOrig.embedUnitary
        (rCTSeg.embedUnitary ((rCoreTopCatInCT mCatTw (by omega)).embedUnitary uTwCatSub))⁻¹).1 :=
          by
    rw [← embedUnitary_inv_symm]
    exact commutesWithReg_unitary_inv hTw
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, Submonoid.coe_mul, Submonoid.coe_mul]
  exact hTwInv.mul (hMidIdle.mul hTw)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512

end ConfigSelectHoistLemmas
end SelectHoistLemmas
end
set_option exponentiation.threshold 256
end SelectHoistLemmas

section SelectStitch
local instance (priority := 1000000) instNeZeroTwoPow_SelectStitch (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `SELECT` Base Specifications & `SingleCatSelectImpl` (`SelectStitch`)

Base `SELECT` specification and `SingleCatSelectImpl` stitcher (`mWork = 137`, `k_idle = 11`):
1. Parametric leaf specifications (`Leaf2Spec`, `Leaf3SpecGen`, `TwistSpecGen`)
   parametric over per-leaf `Ctrl`/`Cat` T-caps and catalyst subslice widths (`mCat = 0, mCat3,
   mCatTw`).
2. `SelectOraHypothesis` (`FullSysSelectOracleBundle 80 48`) with `step_hTwist_s2`,
   `step_hTwist_s1`, `step_hTwist_s0`, and `step_hPos_slack`.
3. `uMidHoistSeg`, `uSelCatHoist`, `uSelectHoist`, and `mkSingleCatSelectImpl`
   (`SingleCatSelectImpl 80 48 qft selOra`) via HadCut-to-PosCut branch reduction and
   `Koff3PassSelectBridge`.
-/

public section

namespace SelectStitch

section ConfigSelectStitch

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

local instance (priority :=
  1000000) instLoc_SelectStitch_1InstNeZeroTwoPowSelectStitch (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open SpecsAux.SpecMirror
open PosMomSelectSandwich (slotBitProj)
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge (fullSysCoreWires)
open FullSysCatSegmentBridge (coreElecCosetB1Block)
open FullSysCatSegmentBridge (disjointWires_concat_left)
open FullSysCatSegmentBridge (FullSysSelectOracleBundle iSlot0)
open FullSysCatSegmentBridge (iSlot1 iSlot2 IntertwinesLocalCat)
open SingleCatSpine (rTopCatSlice)
open OraAndPrepBundle
  (coreUnitaryToFullSys catUnitaryToFullSys
   castNatCat_intertwines momCoreWires_eq_fullSysCoreWires momCatWires_eq_fullSysCatWires)
open NuclearTwistAndXor654Concrete hiding
  fullSysCoreWires IntertwinesLocalCat wSlot0 wSlot1 wSlot2
open NuclearTwistRealizes (uSlot4KickCore)
open NuclearTwistRealizes (intertwinesLocalCat_to_fullSys)
open NuclearTwistRealizes (coin0Active)
open CoinDispatchedBarrel288 (uBarrelFast)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open InterWalkRSum42Hoist (qreg_ext)
open InterWalkRSum42Hoist (rCTFull)
open KoffPrunedSlot2ZeroMuxTrunc37 (uKoffDiagCore)
open SchedBranchStitchGen
  (uVepFusedTwistRestCut80 uFusedTwistRestCut80_factor uTwistEffCut80_comm_slotBitProj
   uSlot4KickCore_comm_slotBitProj op_comm_mul
   intertwinesLocal_unitaryConj_rCoreBlock48
   dyadicDiagUnitary_eq_diagonal uProj3DCutCore_comm_uBarrelFast_gen)
open CoinDispatchedBarrel288 (uBarrelFast_comm_high_wire)
open Barrel3PassSelectStitch
open Koff3PassSelectBridge
open Leaf4HadCut570
open Leaf4Ext48TopStitch

/- ## Section 1: Parametric Leaf Specifications & `FullSysSelectOracleBundle 80 48` -/

/-- Local `(fullSysCoreWires 80 + mCat)` embedding inside `fullSysCoreWires 80 + 48` via
  `rTopCatSlice`. -/
def rCoreTopCatInCT (mCat : ℕ) (hmCat : mCat ≤ 48) :
    QRegister (fullSysCoreWires 80 + mCat) (fullSysCoreWires 80 + 48) :=
  rCoreInCT80.concat
    ((QRegister.block (fullSysCoreWires 80) 48 le_rfl).compose (rTopCatSlice mCat 48 hmCat))
    (by
      rw [QRegister.disjoint_iff]
      intro i j hij
      have hv := congrArg Fin.val hij
      have hi := i.isLt
      have hj := (rTopCatSlice mCat 48 hmCat j).isLt
      dsimp [rCoreInCT80, QRegister.compose_apply, QRegister.block,
        Fin.natAddEmb, Fin.castLEEmb] at hv
      omega)

/-- Ratio `Proj3DCut.uProj3DCutCore * (JunctionProj3DCut.uProj3DCutCore)⁻¹` on `80`
payload wires: equal to `1` on `coin0Active = true` and on `s₂ = 1`, and supported on `rProjAxis`
(`[3924..3948)`) controlled on `(s₂, s₁, s₀, cosetB0)` on coins `1, 2, 3`. -/
noncomputable def uProjPosToCut80 : Unitary (2 ^ (fullSysCoreWires 80)) :=
  Proj3DCut.uProj3DCutCore (by decide : 22 ≤ 80) *
    (JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80))⁻¹

/-- Symbolic-dimension core for `Leaf2Spec` so `mkProjections` runs without concrete
exponent reduction. -/
structure Leaf2SpecCore (kCore wCtrl wCat : ℕ)
    (uBarrel uProjDiff : Unitary (2 ^ kCore))
    (p1 pSlk2 pSlk3 : Operator (2 ^ kCore))
    (uKoff : Configuration → Unitary (2 ^ kCore))
    (rCtrl3 : QRegister 3 kCore)
    (tCtrl tCat : ℕ) where
  uPosPhase0 : Unitary (2 ^ kCore)
  hPosSA : uPosPhase0.1ᴴ = uPosPhase0.1
  hPosOnP1 : uPosPhase0.1 * p1 = p1
  hPosSlack2 : uPosPhase0.1 * pSlk2 = pSlk2
  hPosSlack3 : uPosPhase0.1 * pSlk3 = -pSlk3
  hPosCommK : ∀ c, uKoff c * uPosPhase0 = uPosPhase0 * uKoff c
  hPosCommProjCut : uProjDiff * uPosPhase0 = uPosPhase0 * uProjDiff
  hPass2CommCtrl3 : CommutesWithReg rCtrl3 (unitaryConj uBarrel uPosPhase0).1

/-- Parametric Pass-2 (`mCat = 0`) specification over arbitrary truncation map `truncFn`,
supporting asymmetric `190w` `Ctrl` and `196w` `Cat` workspaces and per-horizon
`(tCtrl, tCat)` T-caps. -/
abbrev Leaf2SpecOfTrunc (truncFn : Configuration → Configuration) (tCtrl tCat : ℕ) :=
    Leaf2SpecCore (fullSysCoreWires 80) 190 196 (uBarrelFast (le_refl 80))
    uProjPosToCut80 (slotBitProj (iSlot2 80) 1) (slotBitProj (iSlot2 80) 0 * slotBitProj
    (iSlot1 80) 1 * slotBitProj (iSlot0 80) 0) (slotBitProj (iSlot2 80) 0 * slotBitProj
    (iSlot1 80) 1 * slotBitProj (iSlot0 80) 1)
    (fun c ↦ uKoffDiagCore (truncFn c) (by decide : 22 ≤ 80)) rCtrl3InCore tCtrl tCat

structure Leaf3SpecCore (kSub kCT wCtrl wCat mPayload kCat : ℕ)
    (rSubInCT : QRegister kSub kCT)
    (uTailConj : Unitary (2 ^ kCT))
    (toFullSys :
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload + kCat)) →
        Unitary (2 ^ kCT))
    (commEC :
      Operator (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)) → Prop)
    (rCtrl3 : QRegister 3 kSub)
    (tCtrl tCat : ℕ) where
  ora3 : MomSingleSlotOracle mPayload kCat 3
  hSlot3CommEC : ∀ c, commEC (ora3.uSlotEff c).1
  uCatSub : Configuration → Unitary (2 ^ kSub)
  hEmbedTop : ∀ c,
    rSubInCT.embedUnitary (uCatSub c) =
      unitaryConj uTailConj (toFullSys (ora3.uSlotCat c))
  hCommCtrl3 : ∀ c, CommutesWithReg rCtrl3 (uCatSub c).1
  dSlot3Ctrl : Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rSub : QRegister kSub n) → (rWB : QRegister wCtrl n) →
    rSub.DisjointWires rWB → DynamicCircuit Var n
  dSlot3Cat : Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rSub : QRegister kSub n) → (rWB : QRegister wCat n) →
    rSub.DisjointWires rWB → DynamicCircuit Var n
  hToffCtrl : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kSub n) (rWB : QRegister wCtrl n)
    (hSW : rSub.DisjointWires rWB),
    (dSlot3Ctrl c v rSub rWB hSW).count .TOFF = 0
  hToffCat : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kSub n) (rWB : QRegister wCat n)
    (hSW : rSub.DisjointWires rWB),
    (dSlot3Cat c v rSub rWB hSW).count .TOFF = 0
  hTCtrl : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kSub n) (rWB : QRegister wCtrl n)
    (hSW : rSub.DisjointWires rWB),
    (dSlot3Ctrl c v rSub rWB hSW).count .T ≤ tCtrl
  hTCat : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kSub n) (rWB : QRegister wCat n)
    (hSW : rSub.DisjointWires rWB),
    (dSlot3Cat c v rSub rWB hSW).count .T ≤ tCat
  hRealCtrl : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rSub : QRegister kSub n) (rWB : QRegister wCtrl n)
    (hSW : rSub.DisjointWires rWB),
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rSub rWB (uCatSub c) (dSlot3Ctrl c v rSub rWB hSW)
  hRealCat : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rSub : QRegister kSub n) (rWB : QRegister wCat n)
    (hSW : rSub.DisjointWires rWB),
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rSub rWB (uCatSub c) (dSlot3Cat c v rSub rWB hSW)

structure SelectOraHypothesisOfTrunc {t2Ctrl t2Cat : ℕ}
    (truncFn : Configuration → Configuration)
    (selOra : FullSysSelectOracleBundle 80 48)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (ora3 : MomSingleSlotOracle 80 48 3) : Prop where
  hTw : ∀ c, selOra.uTwist c =
    uVepFusedTwistRestCut80 (truncFn c) * uBarrelFast (le_refl 80)
  hMom : ∀ c, selOra.uMomPhase c =
    unitaryConj (uBarrelFast (le_refl 80))
      (coreUnitaryToFullSys
        (((GeneralBetaAndAlphaTopEndpoint.zeroMomSlotOracle5
            80 48).uSlotEff c *
          ora3.uSlotEff c) *
          (MomSlot1Dyadic459Sub36w.slot1Dyadic459Oracle.uSlotEff c *
            MomSlot0LocalAndMomCombine288.uSlot0Local (le_refl 80)
              LiteralKineticAndMidpoint128.lambdaSlot0TeHi)))
  hPosEq : ∀ c, selOra.uPosPhase c = leaf2.uPosPhase0

theorem step_uTwist_comm_slotBitProj {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration} {selOra : FullSysSelectOracleBundle 80 48}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat} {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfTrunc truncFn selOra leaf2 ora3) (c : Configuration)
    {w : Wire (fullSysCoreWires 80)} (hwLo : 3948 ≤ w.val) (hwHi : w.val < 3954) (b : Fin 2)
    : (selOra.uTwist c).1 * slotBitProj w b = slotBitProj w b * (selOra.uTwist c).1 := by
  rw [hOra.hTw c, ← uFusedTwistRestCut80_factor (truncFn c)]
  simp only [Submonoid.coe_mul]
  exact op_comm_mul (op_comm_mul (uTrailCliffordXor80_comm_slotBitProj (by omega) hwHi b)
    (op_comm_mul (uSlot4KickCore_comm_slotBitProj w b) (uTwistEffCut80_comm_slotBitProj
    (truncFn c) hwLo b))) (uBarrelFast_comm_high_wire (le_refl 80) w (by omega) b)

theorem step_hTwist_s2 {t2Ctrl t2Cat : ℕ} {truncFn : Configuration → Configuration}
    {selOra : FullSysSelectOracleBundle 80 48}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat} {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfTrunc truncFn selOra leaf2 ora3) (c : Configuration) :
    (selOra.uTwist c).1 * slotBitProj (iSlot2 80) 0 = slotBitProj (iSlot2 80) 0 *
    (selOra.uTwist c).1 := step_uTwist_comm_slotBitProj hOra c (by decide) (by decide) 0

theorem step_hTwist_s1 {t2Ctrl t2Cat : ℕ} {truncFn : Configuration → Configuration}
    {selOra : FullSysSelectOracleBundle 80 48}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat} {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfTrunc truncFn selOra leaf2 ora3) (c : Configuration) :
    (selOra.uTwist c).1 * slotBitProj (iSlot1 80) 1 = slotBitProj (iSlot1 80) 1 *
    (selOra.uTwist c).1 := step_uTwist_comm_slotBitProj hOra c (by decide) (by decide) 1

theorem rCTFull_compose_rCoreTopCatInCT (mCat : ℕ) (hmCat : mCat ≤ 48) :
    rCTFull.compose (rCoreTopCatInCT mCat hmCat) = rCoreTopCatFull mCat hmCat := by
  rw [show rCoreTopCatInCT mCat hmCat =
      SelectHoistLemmas.rCoreTopCatInCT mCat hmCat from rfl,
    ← rSegFull_compose_rCTSeg, QRegister.compose_assoc,
    SelectHoistLemmas.rSegFull_compose_rCTSeg_rCoreTopCatInCT]

theorem rCoreTopCatSum42Full_disj_rGap4Full (mCat : ℕ) (hmCat : mCat ≤ 48) :
    (rCoreTopCatSum42Full mCat hmCat).DisjointWires
    ApexTwistOut334.rGap4Full := disjointWires_concat_left _
    (disjointWires_concat_left _ ApexTwistOut334.hCoreFull_disj_Gap4
    (ApexTwistOut334.hPG48Full_disj_Gap4.compose_left _))
    (QRegExt.disjointWires_symm ApexTwistOut334.hGap4_disj_Sum0)

theorem intertwinesLocalCat_slot3HadCut_of_embedTop {mCat3 : ℕ} {hmCat3 : mCat3 ≤ 48}
    {ora3 : MomSingleSlotOracle 80 48 3} {uCatSub : Unitary (2 ^ (fullSysCoreWires 80 + mCat3))}
    {c : Configuration}
    (hEmb : (rCoreTopCatInCT mCat3 hmCat3).embedUnitary uCatSub =
      unitaryConj (rCoreInCT80.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹)
        (catUnitaryToFullSys (ora3.uSlotCat c)))
    (U_cat48 : Unitary (2 ^ 48))
    (hcol : ∀ m : Fin (2 ^ 48), U_cat48.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) :
    IntertwinesLocalCat U_cat48 ((rCoreTopCatInCT mCat3 hmCat3).embedUnitary uCatSub)
      (unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
        (coreUnitaryToFullSys (ora3.uSlotEff c))) := by
  rw [hEmb]
  have h0 := castNatCat_intertwines (momCoreWires_eq_fullSysCoreWires 80)
      (momCatWires_eq_fullSysCatWires 80 48) U_cat48 (ora3.uSlotCat c)
      (ora3.uSlotEff c) (ora3.hIntertwines c U_cat48 hcol)
  have hN : NuclearTwistAndXor654Concrete.IntertwinesLocalCat
      U_cat48 (catUnitaryToFullSys (ora3.uSlotCat c))
      (coreUnitaryToFullSys (ora3.uSlotEff c)) := ⟨h0.1, h0.2.1, h0.2.2⟩
  exact intertwinesLocalCat_to_fullSys (intertwinesLocal_unitaryConj_rCoreBlock48 U_cat48
    (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹ _ _ hN)

theorem comm_twoBranchProjRow_of_preserves_and_comm (w : Fin 3)
    (P : BitAssignment (fullSysCoreWires 80) → Bool)
    (F : Fin 2 → Operator 256) (G : Operator 256)
    (A : Operator (2 ^ (fullSysCoreWires 80)))
    (hPres : ∀ i k : Fin (2 ^ (fullSysCoreWires 80)), A i k ≠ 0 →
      P (basisBits _ k) = P (basisBits _ i) ∧
        ProjZ512QftAndTwist288.extractCosetP3
          (by decide : 22 ≤ 80) (basisBits _ k) w =
        ProjZ512QftAndTwist288.extractCosetP3
          (by decide : 22 ≤ 80) (basisBits _ i) w)
    (hComm : ∀ B : Operator 256,
      A * (ProjZ512QftAndTwist288.rProjAxis
            (QRegExt.idReg (fullSysCoreWires 80)) w).embedMatrix B =
      (ProjZ512QftAndTwist288.rProjAxis
            (QRegExt.idReg (fullSysCoreWires 80)) w).embedMatrix B * A) :
    A * Matrix.of (fun i j ↦
          if P (basisBits _ i) then
            ((ProjZ512QftAndTwist288.rProjAxis
              (QRegExt.idReg _) w).embedMatrix
              (F (ProjZ512QftAndTwist288.extractCosetP3
                (by decide : 22 ≤ 80) (basisBits _ i) w))) i j
          else
            ((ProjZ512QftAndTwist288.rProjAxis
              (QRegExt.idReg _) w).embedMatrix G) i j) =
    Matrix.of (fun i j ↦
          if P (basisBits _ i) then
            ((ProjZ512QftAndTwist288.rProjAxis
              (QRegExt.idReg _) w).embedMatrix
              (F (ProjZ512QftAndTwist288.extractCosetP3
                (by decide : 22 ≤ 80) (basisBits _ i) w))) i j
          else
            ((ProjZ512QftAndTwist288.rProjAxis
              (QRegExt.idReg _) w).embedMatrix G) i j) * A := by
  let rAx := ProjZ512QftAndTwist288.rProjAxis
    (QRegExt.idReg (fullSysCoreWires 80)) w
  ext i j
  let B_i : Operator 256 := if P (basisBits _ i) then
    F (ProjZ512QftAndTwist288.extractCosetP3
      (by decide : 22 ≤ 80) (basisBits _ i) w) else G
  simp only [Matrix.mul_apply, Matrix.of_apply]
  have hL : ∀ k : Fin (2 ^ (fullSysCoreWires 80)),
      A i k * (if P (basisBits _ k) then
        (rAx.embedMatrix (F (ProjZ512QftAndTwist288.extractCosetP3
          (by decide : 22 ≤ 80) (basisBits _ k) w))) k j
        else (rAx.embedMatrix G) k j) = A i k * (rAx.embedMatrix B_i) k j := fun k ↦ by
    by_cases h0 : A i k = 0
    · rw [h0, zero_mul, zero_mul]
    · obtain ⟨hpk, hek⟩ := hPres i k h0
      by_cases hp : P (basisBits _ i)
      · simp only [B_i, hpk, hp, ↓reduceIte, hek]
      · simp only [B_i, hpk, hp, Bool.false_eq_true, ↓reduceIte]
  have hR : ∀ k : Fin (2 ^ (fullSysCoreWires 80)),
      (if P (basisBits _ i) then
        (rAx.embedMatrix (F (ProjZ512QftAndTwist288.extractCosetP3
          (by decide : 22 ≤ 80) (basisBits _ i) w))) i k
        else (rAx.embedMatrix G) i k) * A k j = (rAx.embedMatrix B_i) i k * A k j := fun k ↦ by
    by_cases hp : P (basisBits _ i)
    · simp only [B_i, hp, ↓reduceIte]
    · simp only [B_i, hp, Bool.false_eq_true, ↓reduceIte]
  rw [Finset.sum_congr rfl fun k _ ↦ hL k, Finset.sum_congr rfl fun k _ ↦ hR k,
    ← Matrix.mul_apply, ← Matrix.mul_apply, hComm B_i]

theorem unitary_inv_commAux {d : ℕ} (C : Unitary d) {A : Operator d}
    (h : A * C.1 = C.1 * A) : A * (C⁻¹).1 = (C⁻¹).1 * A := by
  have hR : C.1 * (C⁻¹).1 = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  have hL : (C⁻¹).1 * C.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  calc A * (C⁻¹).1 = ((C⁻¹).1 * C.1) * (A * (C⁻¹).1) := by rw [hL, Matrix.one_mul]
    _ = (C⁻¹).1 * ((C.1 * A) * (C⁻¹).1) := by simp only [Matrix.mul_assoc]
    _ = (C⁻¹).1 * (A * (C.1 * (C⁻¹).1)) := by rw [← h, Matrix.mul_assoc]
    _ = (C⁻¹).1 * A := by rw [hR, Matrix.mul_one]

theorem op_comm_mul3Aux {d : ℕ} {A X Y Z : Operator d}
    (hx : A * X = X * A) (hy : A * Y = Y * A) (hz : A * Z = Z * A) :
    A * (X * (Y * Z)) = (X * (Y * Z)) * A :=
  (op_comm_mul hx.symm (op_comm_mul hy.symm hz.symm)).symm

private theorem comm_uProjPosToCut80_mat (A : Operator (2 ^ (fullSysCoreWires 80)))
    (hPosPres : ∀ i k : Fin (2 ^ (fullSysCoreWires 80)), A i k ≠ 0 →
      Proj3DCut.posBranchActive (basisBits _ k) =
      Proj3DCut.posBranchActive (basisBits _ i))
    (hCutPres : ∀ i k : Fin (2 ^ (fullSysCoreWires 80)), A i k ≠ 0 →
      coin0Active (basisBits _ k) = coin0Active (basisBits _ i))
    (hCoset : ∀ (w : Fin 3) (i k : Fin (2 ^ (fullSysCoreWires 80))), A i k ≠ 0 →
      ProjZ512QftAndTwist288.extractCosetP3
        (by decide : 22 ≤ 80) (basisBits _ k) w =
      ProjZ512QftAndTwist288.extractCosetP3
        (by decide : 22 ≤ 80) (basisBits _ i) w)
    (hComm : ∀ (w : Fin 3) (B : Operator 256), A *
      (ProjZ512QftAndTwist288.rProjAxis
        (QRegExt.idReg (fullSysCoreWires 80)) w).embedMatrix B =
      (ProjZ512QftAndTwist288.rProjAxis
        (QRegExt.idReg (fullSysCoreWires 80)) w).embedMatrix B * A) :
    (∀ w : Fin 3, A * (JunctionProj3DCut.uProj3DCut1DCore
        (by decide : 22 ≤ 80) w).1 =
      (JunctionProj3DCut.uProj3DCut1DCore
        (by decide : 22 ≤ 80) w).1 * A) ∧
      uProjPosToCut80.1 * A = A * uProjPosToCut80.1 := by
  have hPos1D : ∀ w : Fin 3, A *
      (Proj3DCut.uProj3DCut1DCore
        (by decide : 22 ≤ 80) w).1 =
      (Proj3DCut.uProj3DCut1DCore
        (by decide : 22 ≤ 80) w).1 * A := fun w ↦
    comm_twoBranchProjRow_of_preserves_and_comm w
      Proj3DCut.posBranchActive
      (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1)
      Proj3DCut.uTailLocal8.1 A
      (fun i k h0 ↦ ⟨hPosPres i k h0, hCoset w i k h0⟩) (hComm w)
  have hCut1D : ∀ w : Fin 3, A *
      (JunctionProj3DCut.uProj3DCut1DCore
        (by decide : 22 ≤ 80) w).1 =
      (JunctionProj3DCut.uProj3DCut1DCore
        (by decide : 22 ≤ 80) w).1 * A := fun w ↦
    comm_twoBranchProjRow_of_preserves_and_comm w coin0Active
      (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1)
      JunctionProj3DCut.uTailLocal8.1 A
      (fun i k h0 ↦ ⟨hCutPres i k h0, hCoset w i k h0⟩) (hComm w)
  have hPos3D : A * (Proj3DCut.uProj3DCutCore
      (by decide : 22 ≤ 80)).1 =
      (Proj3DCut.uProj3DCutCore
        (by decide : 22 ≤ 80)).1 * A := by
    unfold Proj3DCut.uProj3DCutCore
    simp only [Submonoid.coe_mul]
    exact op_comm_mul3Aux (hPos1D 0) (hPos1D 1) (hPos1D 2)
  have hCut3D : A * (JunctionProj3DCut.uProj3DCutCore
      (by decide : 22 ≤ 80)).1 =
      (JunctionProj3DCut.uProj3DCutCore
        (by decide : 22 ≤ 80)).1 * A := by
    unfold JunctionProj3DCut.uProj3DCutCore
    simp only [Submonoid.coe_mul]
    exact op_comm_mul3Aux (hCut1D 0) (hCut1D 1) (hCut1D 2)
  refine ⟨hCut1D, ?_⟩
  unfold uProjPosToCut80
  simp only [Submonoid.coe_mul]
  rw [Matrix.mul_assoc, ← unitary_inv_commAux _ hCut3D, ← Matrix.mul_assoc,
    ← hPos3D, Matrix.mul_assoc]

theorem comm_uProjPosToCut80_of_preserves_and_comm (U : Unitary (2 ^ (fullSysCoreWires 80)))
    (hPres : ∀ i k : Fin (2 ^ (fullSysCoreWires 80)), U.1 i k ≠ 0 → ∀ q : Wire
    (fullSysCoreWires 80), (3948 ≤ q.val ∧ q.val < 3951) ∨ (3957 ≤ q.val ∧ q.val < 3960) →
    basisBits _ k q = basisBits _ i q) (hComm : ∀ (w : Fin 3) (B : Operator 256), U.1 *
    (ProjZ512QftAndTwist288.rProjAxis (QRegExt.idReg
    (fullSysCoreWires 80)) w).embedMatrix B =
    (ProjZ512QftAndTwist288.rProjAxis (QRegExt.idReg
    (fullSysCoreWires 80)) w).embedMatrix B * U.1) : uProjPosToCut80 * U = U *
    uProjPosToCut80 := by
  refine Subtype.ext ((comm_uProjPosToCut80_mat U.1 (fun i k h0 ↦ ?_) (fun i k h0 ↦ ?_)
    (fun w i k h0 ↦ ?_) hComm).2)
  · unfold Proj3DCut.posBranchActive
    rw [hPres i k h0 _ (Or.inl (by
      simp [NuclearTwistAndXor654Concrete.wSlot2, QRegExt.idReg]))]
  · unfold coin0Active
    rw [hPres i k h0 _ (Or.inl (by
          simp [NuclearTwistAndXor654Concrete.wSlot2, QRegExt.idReg])),
        hPres i k h0 _ (Or.inl (by
          simp [NuclearTwistAndXor654Concrete.wSlot1, QRegExt.idReg])),
        hPres i k h0 _ (Or.inl (by
          simp [NuclearTwistAndXor654Concrete.wSlot0, QRegExt.idReg]))]
  · unfold ProjZ512QftAndTwist288.extractCosetP3
      ProjZ512QftAndTwist288.rProjCosetP3
    refine Fin.ext (congrArg ZMod.val (hPres i k h0 _ (Or.inr ?_)))
    have := w.isLt
    simp [NuclearTwistAndXor654Concrete.rCosetB0,
      QRegister.slice, QRegister.compose, QRegExt.idReg]
    omega

theorem embed_coreElecCosetB1_comm_uProjPosToCut80 (hm6 : 6 ≤ 80) (W : Unitary (2 ^ (3924 + 3))) :
    uProjPosToCut80 * (coreElecCosetB1Block hm6).embedUnitary W =
      (coreElecCosetB1Block hm6).embedUnitary W * uProjPosToCut80 := by
  have hOutRange : ∀ (q : Wire (fullSysCoreWires 80)), (3948 ≤ q.val ∧ q.val < 3951) ∨
      (3957 ≤ q.val ∧ q.val < 3960) → q ∉ Set.range (coreElecCosetB1Block hm6).wires := by
    rintro q hq ⟨i, hij⟩
    have hv := congrArg Fin.val hij
    have hi := i.isLt
    by_cases hlt : i.val < 3924
    · rw [show i = Fin.castAdd 3 ⟨i.val, hlt⟩ from Fin.ext rfl,
        QRegister.concat_apply_left] at hv
      change 0 + i.val = q.val at hv
      omega
    · rw [show i = Fin.natAdd 3924 ⟨i.val - 3924, by omega⟩ from Fin.ext (by
          simp
          omega),
        QRegister.concat_apply_right] at hv
      change 3954 + (i.val - 3924) = q.val at hv
      omega
  refine comm_uProjPosToCut80_of_preserves_and_comm _ (fun i k hne q hq ↦ ?_) (fun w B ↦ ?_)
  · by_contra hdiff
    rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply_of_agreeOutside] at hne
    exact hne (by rw [ite_eq_right (fun ha ↦ hdiff (ha q (hOutRange q hq)).symm), mul_zero])
  · rw [QRegister.embedUnitary_val]
    refine QRegister.embedMatrix_comm_of_disjoint _ _
      (QRegister.disjoint_iff.mpr fun i j hij ↦ ?_) _ _
    have hb := SchedBranchStitchGen.rProjAxis_bounds80 w
    exact FullSysCatSegmentBridge.wire_not_mem_coreElecCosetB1
      hm6 (hb.1 j) (by
        have := hb.2 j
        omega) ⟨i, hij⟩

theorem uSlot4KickCore_comm_uProjPosToCut80 : uProjPosToCut80 * uSlot4KickCore
    (by decide : 22 ≤ 80) = uSlot4KickCore (by decide : 22 ≤ 80) * uProjPosToCut80 := by
  refine comm_uProjPosToCut80_of_preserves_and_comm _ (fun i k hne q _ ↦ ?_) (fun w B ↦ ?_)
  · by_contra hdiff
    exact hne (by rw [uSlot4KickCore, dyadicDiagUnitary_eq_diagonal,
      Matrix.diagonal_apply_ne _ (fun hik ↦ hdiff (by rw [hik]))])
  · rw [uSlot4KickCore, dyadicDiagUnitary_eq_diagonal]
    refine (PosMomSelectDynamic.embedMatrix_comm_diagonal_of_outside
      (ProjZ512QftAndTwist288.rProjAxis
        (QRegExt.idReg (fullSysCoreWires 80)) w) B _ (fun x y hOut ↦ ?_)).symm
    have hNotIn : ∀ (q : Wire (fullSysCoreWires 80)),
        q.val < 3924 ∨ 3948 ≤ q.val → basisBits _ x q = basisBits _ y q := fun q hq ↦
      hOut q (fun ⟨m, hm⟩ ↦ by
        have hb := SchedBranchStitchGen.rProjAxis_bounds80 w
        have := hb.1 m
        have := hb.2 m
        have hv := congrArg Fin.val hm
        omega)
    congr 1
    unfold NuclearTwistRealizes.slot4TotalPhaseExp
    rw [hNotIn _ (Or.inr (by
          simp [NuclearTwistAndXor654Concrete.wSlot2, QRegExt.idReg])),
        hNotIn _ (Or.inr (by
          simp [NuclearTwistAndXor654Concrete.wSlot1, QRegExt.idReg])),
        hNotIn _ (Or.inr (by
          simp [NuclearTwistAndXor654Concrete.wSlot0, QRegExt.idReg]))]
    split_ifs with hc
    · refine Finset.sum_congr rfl fun a _ ↦ ?_
      have hb1 := hNotIn (rCosetB1 (by decide : 22 ≤ 80) (QRegExt.idReg _) a)
        (Or.inr (by
          have := a.isLt
          simp [rCosetB1, QRegister.slice, QRegExt.idReg]
          omega))
      have hb0 := hNotIn (rCosetB0 (by decide : 22 ≤ 80) (QRegExt.idReg _) a)
        (Or.inr (by
          have := a.isLt
          simp [rCosetB0, QRegister.slice, QRegExt.idReg]
          omega))
      have he0 : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
        (rElecSlotAxis (QRegExt.idReg _) 0 a) (basisBits _ x) =
          _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
            (rElecSlotAxis (QRegExt.idReg _) 0 a) (basisBits _ y) :=
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr _ fun j ↦
          hNotIn _ (Or.inl (by
          have := a.isLt
          have := j.isLt
          have hne218 : SpecsAux.SpecMirror.numElectrons = 218 := rfl
          simp [rElecSlotAxis, QRegister.slice, QRegExt.idReg, hne218]
          omega))
      rw [hb1, hb0, he0]
    · rfl

theorem comm_of_complementary_proj_id {d : ℕ} (U V P : Operator d) (hUP : U * P = P)
    (hPU : P * U = P) (hVP : V * P = P * V) (hV1 : V * (1 - P) = 1 - P)
    (_h1V : (1 - P) * V = 1 - P) : U * V = V * U := by
  have hVR : P * V + (1 - P) = V := by
    rw [← hVP, ← hV1, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  calc U * V = U * (P * V + (1 - P)) := congrArg (U * ·) hVR.symm
    _ = (U * P) * V + (U * 1 - U * P) := by rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_sub]
    _ = P * V + (U - P) := by rw [hUP, Matrix.mul_one]
    _ = V * (P * U) + (1 * U - P * U) := by rw [hPU, Matrix.one_mul, hVP]
    _ = (V * P + (1 - P)) * U := by rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul]
    _ = V * U := congrArg (· * U) (by
      rw [hVP]
      exact hVR)

theorem uVepSlot2KickCore_comm_uProjPosToCut80 (c' : Configuration) :
    uProjPosToCut80 *
      ProjZ512QftAndTwist288.uVepSlot2KickCore c' (by decide : 22 ≤ 80) =
      ProjZ512QftAndTwist288.uVepSlot2KickCore c' (by decide : 22 ≤ 80) *
        uProjPosToCut80 := by
  let pCoin0 : Operator (2 ^ (fullSysCoreWires 80)) :=
    Matrix.diagonal (fun u ↦ if coin0Active (basisBits _ u) then (1 : ℂ) else 0)
  have hPC0Ax : ∀ (w : Fin 3) (B : Operator 256),
      pCoin0 * (ProjZ512QftAndTwist288.rProjAxis
            (QRegExt.idReg (fullSysCoreWires 80)) w).embedMatrix B =
      (ProjZ512QftAndTwist288.rProjAxis
            (QRegExt.idReg (fullSysCoreWires 80)) w).embedMatrix B * pCoin0 := fun w B ↦ by
    refine (PosMomSelectDynamic.embedMatrix_comm_diagonal_of_outside
      (ProjZ512QftAndTwist288.rProjAxis
        (QRegExt.idReg (fullSysCoreWires 80)) w) B _ (fun x y hOut ↦ ?_)).symm
    have hNotIn : ∀ (q : Wire (fullSysCoreWires 80)), 3948 ≤ q.val →
        basisBits _ x q = basisBits _ y q := fun q hq ↦
      hOut q (fun ⟨m, hm⟩ ↦ by
        have hHi := (SchedBranchStitchGen.rProjAxis_bounds80 w).2 m
        have hv := congrArg Fin.val hm
        omega)
    unfold coin0Active
    rw [hNotIn _ (by
          simp [NuclearTwistAndXor654Concrete.wSlot2, QRegExt.idReg]),
        hNotIn _ (by
          simp [NuclearTwistAndXor654Concrete.wSlot1, QRegExt.idReg]),
        hNotIn _ (by
          simp [NuclearTwistAndXor654Concrete.wSlot0, QRegExt.idReg])]
  have hPC0Eq : ∀ i k : Fin (2 ^ (fullSysCoreWires 80)), pCoin0 i k ≠ 0 → i = k :=
    fun i k h0 ↦ by
      by_contra hne
      exact h0 (Matrix.diagonal_apply_ne _ hne)
  obtain ⟨hCutComm1D, hCommUP⟩ := comm_uProjPosToCut80_mat pCoin0
    (fun i k h0 ↦ by rw [hPC0Eq i k h0]) (fun i k h0 ↦ by rw [hPC0Eq i k h0])
    (fun _ i k h0 ↦ by rw [hPC0Eq i k h0]) hPC0Ax
  have hEq1D : ∀ w : Fin 3,
      pCoin0 * (Proj3DCut.uProj3DCut1DCore
        (by decide : 22 ≤ 80) w).1 =
      pCoin0 * (JunctionProj3DCut.uProj3DCut1DCore
        (by decide : 22 ≤ 80) w).1 := fun w ↦ by
    dsimp only [pCoin0]
    unfold Proj3DCut.uProj3DCut1DCore
      Proj3DCut.uCoin0Stage1DCore
      Proj3DCut.uCoin0Stage1DMat
      JunctionProj3DCut.uProj3DCut1DCore
      JunctionProj3DCut.uCoin0Stage1DCore
      JunctionProj3DCut.uCoin0Stage1DMat
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.of_apply]
    by_cases hc : coin0Active (basisBits _ i)
    · have hp : Proj3DCut.posBranchActive
          (basisBits _ i) = true := by
        unfold coin0Active at hc
        unfold Proj3DCut.posBranchActive
        simp only [decide_eq_true_eq] at hc ⊢
        exact hc.1
      simp only [hc, hp, ↓reduceIte]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, zero_mul]
  have hPU : pCoin0 * uProjPosToCut80.1 = pCoin0 := by
    have hEq3D : pCoin0 * (Proj3DCut.uProj3DCutCore
        (by decide : 22 ≤ 80)).1 =
        pCoin0 * (JunctionProj3DCut.uProj3DCutCore
          (by decide : 22 ≤ 80)).1 := by
      unfold Proj3DCut.uProj3DCutCore
        JunctionProj3DCut.uProj3DCutCore
      simp only [Submonoid.coe_mul]
      rw [← mul_assoc pCoin0, hEq1D 0, hCutComm1D 0, mul_assoc _ pCoin0, ← mul_assoc pCoin0,
        hEq1D 1, hCutComm1D 1, mul_assoc _ pCoin0, hEq1D 2, ← mul_assoc _ pCoin0,
        ← hCutComm1D 1, mul_assoc pCoin0, ← mul_assoc _ pCoin0, ← hCutComm1D 0, mul_assoc pCoin0]
    unfold uProjPosToCut80
    rw [Submonoid.coe_mul, ← Matrix.mul_assoc, hEq3D, Matrix.mul_assoc,
      ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one, Matrix.mul_one]
  let V := ProjZ512QftAndTwist288.uVepSlot2KickCore c'
    (by decide : 22 ≤ 80)
  have hVP : V.1 * pCoin0 = pCoin0 * V.1 := by
    dsimp only [V, pCoin0]
    rw [ProjZ512QftAndTwist288.uVepSlot2KickCore,
      dyadicDiagUnitary_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  have hV1 : V.1 * (1 - pCoin0) = 1 - pCoin0 := by
    have h1m : 1 - pCoin0 =
        Matrix.diagonal (fun u ↦ (1 : ℂ) - if coin0Active (basisBits _ u) then 1 else 0) := by
      ext i j
      simp only [pCoin0, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
      split_ifs <;> ring
    dsimp only [V]
    rw [h1m, ProjZ512QftAndTwist288.uVepSlot2KickCore,
      dyadicDiagUnitary_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext u
    by_cases hc : coin0Active (basisBits _ u)
    · simp only [hc, ↓reduceIte, sub_self, mul_zero]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte, sub_zero, mul_one]
      have hm48 (w : Fin 3) : NuclearTwistRealizes.slot2M48Val
          c' (by decide : 22 ≤ 80) w (basisBits _ u) = 0 := by
        unfold NuclearTwistRealizes.slot2M48Val
        simp only [hc, Bool.false_eq_true, false_and, ↓reduceDIte]
      have hvep (w : Fin 3) : ProjZ512QftAndTwist288.vepOnlyM48Val
          (by decide : 22 ≤ 80) w (basisBits _ u) = 0 := by
        unfold ProjZ512QftAndTwist288.vepOnlyM48Val
          ProjZ512QftAndTwist288.vepHighNuc
        simp [hc]
      have hexp : ProjZ512QftAndTwist288.vepSlot2TotalPhaseExp
          c' (by decide : 22 ≤ 80) (basisBits _ u) = 0 := by
        unfold ProjZ512QftAndTwist288.vepSlot2TotalPhaseExp
        simp only [hm48, hvep, add_zero, Nat.cast_zero, mul_zero, Finset.sum_const_zero]
      rw [hexp, DyadicQft64.dyadicTurn_zero]
  have h1V : (1 - pCoin0) * V.1 = 1 - pCoin0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, ← hVP, ← hV1, Matrix.mul_sub, Matrix.mul_one]
  exact Subtype.ext (comm_of_complementary_proj_id uProjPosToCut80.1 V.1 pCoin0
    (hCommUP.trans hPU) hPU hVP hV1 h1V)

theorem uProjPosToCut80_comm_uBarrelFast :
    uProjPosToCut80 * uBarrelFast (le_refl 80) = uBarrelFast (le_refl 80) * uProjPosToCut80 := by
  apply Subtype.ext
  have hPos := uProj3DPosCutCore_comm_uBarrelFast_gen (by decide) (le_refl 80)
  have hCut := uProj3DCutCore_comm_uBarrelFast_gen (by decide) (le_refl 80)
  have hCutInv := (unitary_inv_commAux _ hCut.symm).symm
  unfold uProjPosToCut80
  simp only [Submonoid.coe_mul]
  rw [Matrix.mul_assoc, hCutInv, ← Matrix.mul_assoc, hPos, Matrix.mul_assoc]

theorem uTailHad3DCore_comm_uKoffMomCore80 :
    uKoffMomCore80 * JunctionUncondHadTailCut.uTailHad3DCore =
      JunctionUncondHadTailCut.uTailHad3DCore * uKoffMomCore80 := by
  have h1D : ∀ a : Fin 3,
      uKoffMomCore80.1 *
        ((ProjZ512QftAndTwist288.rProjAxis
          (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
          JunctionUncondHadTailCut.uTailHadLocal8).1 =
      ((ProjZ512QftAndTwist288.rProjAxis
        (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
        JunctionUncondHadTailCut.uTailHadLocal8).1 * uKoffMomCore80.1 := by
    intro a
    unfold uKoffMomCore80
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    refine QRegister.embedMatrix_comm_of_disjoint _ _ ?_ _ _
    rw [QRegister.disjoint_iff]
    intro i j hij
    have hb := SchedBranchStitchGen.rProjAxis_bounds80 a
    exact FullSysCatSegmentBridge.wire_not_mem_coreElecCosetB1
      (by decide : 6 ≤ 80) (hb.1 j) (by have := hb.2 j; omega) ⟨i, hij⟩
  apply Subtype.ext
  unfold JunctionUncondHadTailCut.uTailHad3DCore
  simp only [Submonoid.coe_mul]
  exact (op_comm_mul (h1D 0).symm (op_comm_mul (h1D 1).symm (h1D 2).symm)).symm

set_option maxRecDepth 512
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency false

end ConfigSelectStitch

end SelectStitch

end
set_option exponentiation.threshold 256
end SelectStitch

section Leaf3HadCutBridge
local instance (priority := 1000000) instNeZeroTwoPow_Leaf3HadCutBridge (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
  Slot-3 `0-T` `dConjInvTailHad3D` (`JunctionUncondHadTailCut`) Bridge

  Wraps any clean-workspace `Slot3LeafSpec 36 mWB tCap` realizing `uSlot3Swap3Cat36Norm1s t`
  inside `JunctionUncondHadTailCut.dConjInvTailHad3D` (`0` extra `T` gates, `0 .TOFF` gates),
  and packages `(190w Ctrl, 193w Cat)` pairs directly into `SelectStitch.Leaf3Spec`
  via the `0`-step `rfl` register-splitting adapter `dSub36OfLeaf`.
-/

public section

namespace Leaf3HadCutBridge

section ConfigLeaf3HadCutBridge

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

local instance (priority :=
  10) instLoc_Leaf3HadCutBridge_1InstNeZeroTwoPowLeaf3HadC (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open SpecsAux.SpecMirror
open TwosCompAndWire0Cancel (fwdPermUnitary fwdPermMatrix)
open TwosCompAndWire0Cancel (fwdPermMatrix_apply)
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_concat_left disjointWires_compose_of_disjoint)
open OraAndPrepBundle (castNatUnitary castNatReg
   momCoreWires_eq_fullSysCoreWires)
open QRegExt
open ProjZ512QftAndTwist288 (rProjAxis)
open InterWalkRSum42Hoist (qreg_ext)
open FullSysMomSlots0135Concrete (momCoreWires)
open MomSlots35Slot3ProjNuclear (s3MomCore_ge_4034 s3Coarse33Core)
open MomSlots35Slot3ProjNuclear (uPrep3)
open StepBBlock0 (s3DisjConcatLeft sel107_80 sel107_80_val)
open Slot3Exact216Oracle80 (s3QutritPairCore uQutrit3 uPrep3_216)
open Slot3Prep273AndSwap3 (piSwap3Wire piSwap3WireFun_involutive)
open Slot3Prep273AndSwap3 (piSwap3Wire_fix_lt3954 piSwap3CorePerm)
open Slot3Prep273AndSwap3 (basisBits_piSwap3CorePerm uPiSwap3Core)
open Slot3Prep273AndSwap3 (uPiSwap3Core_apply)
open Slot3Norm1s36_161w (Norm1sTier)
open Leaf3Slot3Norm1sWidth204
  (coreWires80 rCore0_36 rCat0_36 hCoreCatDisj36 sel143_80_36 uCore143Norm1s uSlot3Cat36Norm1s
    uSlot3Swap3Cat36Norm1s)
open Leaf4Ext48TopStitch (CommutesWithReg rCtrl3InCoreCat)
open Leaf4Ext48TopStitch (commutesWithReg_fwdPermUnitary)

/- ## Section 1: `rEC80` Commutation & Core+36 Symbolic Width Casts -/

theorem hCore80_eq : coreWires80 = fullSysCoreWires 80 :=
  momCoreWires_eq_fullSysCoreWires 80

theorem hCoreCat36_eq : coreWires80 + 36 = fullSysCoreWires 80 + 36 :=
  congrArg (· + 36) hCore80_eq

/-- Core `4,034`-wire prefix `[0 .. fullSysCoreWires 80)` inside `fullSysCoreWires 80 + 36`. -/
def rCoreInCoreCat36 : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 36) :=
  QRegister.block 0 (fullSysCoreWires 80) (by omega)

/-- `0-T` `uTailHad3DCore⁻¹`-conjugated `36`-catalyst-wire Slot-3 unitary on
`fullSysCoreWires 80 + 36`. -/
noncomputable def uSlot3HadCutCat36FullSys (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) : Unitary (2 ^ (fullSysCoreWires 80 + 36)) :=
    unitaryConj (rCoreInCoreCat36.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹)
    (castNatUnitary hCoreCat36_eq (uSlot3Swap3Cat36Norm1s t cfg))

/-- `0-T` `uTailHad3DCore⁻¹`-conjugated `36`-catalyst-wire Slot-3 unitary on `coreWires80 + 36`
for `Slot3LeafSpec 36 mWB tCap` and `CleanLeafSpec 36 mWB tCap`. -/
noncomputable def uSlot3HadCutCat36Mom (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) : Unitary (2 ^ (coreWires80 + 36)) :=
  castNatUnitary hCoreCat36_eq.symm (uSlot3HadCutCat36FullSys t cfg)

def rCtrl3MomCore : QRegister 3 (momCoreWires 80) :=
  QRegister.block 3951 3 (by have := s3MomCore_ge_4034 (le_refl 80); omega)

/-- `3`-qubit Slot-3 control slice `[3951 .. 3954)` inside `coreWires80 + 36`. -/
def rCtrl3MomCat36 : QRegister 3 (coreWires80 + 36) :=
  QRegister.block 3951 3 (by
    have : coreWires80 = momCoreWires 80 := rfl
    have := s3MomCore_ge_4034 (le_refl 80); omega)

theorem commutesWithReg_rCtrl3MomCore_uPiSwap3Core :
    CommutesWithReg rCtrl3MomCore uPiSwap3Core.1 := by
  have hMat : uPiSwap3Core.1 = (fwdPermUnitary piSwap3CorePerm).1 := by
    ext i j; rw [uPiSwap3Core_apply]; change _ = fwdPermMatrix piSwap3CorePerm i j
    rw [fwdPermMatrix_apply]; simp only [eq_comm]
  rw [hMat]
  have hFix : ∀ b : Fin 3, piSwap3Wire (rCtrl3MomCore b) = rCtrl3MomCore b :=
    fun b ↦ piSwap3Wire_fix_lt3954 _ (by have := b.isLt; change 3951 + b.val < 3954; omega)
  have hOut : ∀ x y : Fin (2 ^ (momCoreWires 80)), rCtrl3MomCore.AgreeOutside x y →
      rCtrl3MomCore.AgreeOutside (piSwap3CorePerm x) (piSwap3CorePerm y) :=
    fun x y hxy q hq ↦ by
      rw [basisBits_piSwap3CorePerm, basisBits_piSwap3CorePerm]
      refine hxy (piSwap3Wire q) fun ⟨b, hb⟩ ↦ hq ⟨b, ?_⟩
      have hbFix := hFix b
      have hinv : piSwap3Wire (piSwap3Wire q) = q := piSwap3WireFun_involutive q
      rw [hb, hinv] at hbFix
      exact hb.trans hbFix.symm
  refine commutesWithReg_fwdPermUnitary rCtrl3MomCore piSwap3CorePerm (fun x ↦ ?_) hOut hOut
  apply (basisBitsEquiv 3).injective; funext b
  change basisBits 3 _ b = basisBits 3 _ b
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    basisBits_piSwap3CorePerm, hFix b]

theorem commutesWithReg_rCtrl3MomCore_uPrep3_216 :
    CommutesWithReg rCtrl3MomCore (uPrep3_216 (le_refl 80)).1 := by
  have hQ : ∀ j : Fin 3, (s3QutritPairCore (le_refl 80) j).DisjointWires rCtrl3MomCore :=
    fun j ↦ QRegister.disjoint_iff.mpr fun a b heq ↦ by
      have hv := congrArg Fin.val heq; have := a.isLt; have := b.isLt; have := j.isLt
      change (4020 + 2 * j.val) + a.val = 3951 + b.val at hv; omega
  have hC : (s3Coarse33Core (le_refl 80)).DisjointWires rCtrl3MomCore :=
    QRegister.disjoint_iff.mpr fun a b heq ↦ by
      have hv := congrArg Fin.val heq; have := a.isLt; have := b.isLt
      change 3954 + a.val = 3951 + b.val at hv; omega
  unfold uPrep3_216 uQutrit3 uPrep3
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
  exact ((CommutesWithReg.of_disjoint (hQ 2) _).mul ((CommutesWithReg.of_disjoint (hQ 1)
    _).mul (CommutesWithReg.of_disjoint (hQ 0) _))).mul (CommutesWithReg.of_disjoint hC _)

theorem commutesWithReg_rCtrl3MomCat36_uSlot3Swap3Cat36Norm1s
    (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    CommutesWithReg rCtrl3MomCat36 (uSlot3Swap3Cat36Norm1s t cfg).1 := by
  have hComp : rCtrl3MomCat36 = rCore0_36.compose rCtrl3MomCore :=
    qreg_ext fun _ ↦ Fin.ext (Nat.zero_add _).symm
  have hSelDisj : sel143_80_36.DisjointWires rCtrl3MomCat36 :=
    s3DisjConcatLeft
      (QRegister.disjoint_iff.mpr fun i b heq ↦ by
        have hv : 0 + (sel107_80 i).val = 3951 + b.val := congrArg Fin.val heq
        have hsel := sel107_80_val i; have := i.isLt; have := b.isLt
        split_ifs at hsel <;> omega)
      (QRegister.disjoint_iff.mpr fun j b heq ↦ by
        have hv : coreWires80 + j.val = 3951 + b.val := congrArg Fin.val heq
        have := j.isLt; have := b.isLt
        have : 4034 ≤ coreWires80 := s3MomCore_ge_4034 (le_refl 80)
        omega)
  have hPi : CommutesWithReg rCtrl3MomCat36 (rCore0_36.embedMatrix uPiSwap3Core.1) := by
    rw [hComp]; exact CommutesWithReg.embedMatrix rCore0_36
      commutesWithReg_rCtrl3MomCore_uPiSwap3Core
  have hPrep : CommutesWithReg rCtrl3MomCat36
      (rCore0_36.embedUnitary (uPrep3_216 (le_refl 80))).1 := by
    rw [hComp, QRegister.embedUnitary_val]
    exact CommutesWithReg.embedMatrix rCore0_36 commutesWithReg_rCtrl3MomCore_uPrep3_216
  have hCore : CommutesWithReg rCtrl3MomCat36
      (sel143_80_36.embedUnitary (uCore143Norm1s t cfg)).1 := by
    rw [QRegister.embedUnitary_val]; exact CommutesWithReg.of_disjoint hSelDisj _
  unfold uSlot3Swap3Cat36Norm1s uSlot3Cat36Norm1s
  rw [PosMomSelectDynamic.unitaryConj_val, PosMomSelectDynamic.unitaryConj_val,
    QRegister.embedUnitary_val]
  exact (hPi.conjTranspose.mul ((hPrep.conjTranspose.mul hCore).mul hPrep)).mul hPi

theorem commutesWithReg_rCtrl3InCoreCat36_uSlot3HadCut
    (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    CommutesWithReg (rCtrl3InCoreCat 36) (uSlot3HadCutCat36FullSys t cfg).1 := by
  have hGen : ∀ {a b : ℕ} (hab : a = b) (rA : QRegister 3 a) (rB : QRegister 3 b)
      (hr : ∀ i : Fin 3, (rA i).val = (rB i).val) (U : Unitary (2 ^ a)),
      CommutesWithReg rA U.1 → CommutesWithReg rB (castNatUnitary hab U).1 := by
    intro a b hab rA rB hr U hComm; subst hab
    rwa [← qreg_ext fun i ↦ Fin.ext (hr i)]
  have hU := hGen hCoreCat36_eq rCtrl3MomCat36 (rCtrl3InCoreCat 36) (fun _ ↦ rfl)
    (uSlot3Swap3Cat36Norm1s t cfg) (commutesWithReg_rCtrl3MomCat36_uSlot3Swap3Cat36Norm1s t cfg)
  have hAx : ∀ w : Fin 3, CommutesWithReg (rCtrl3InCoreCat 36) ((rCoreInCoreCat36.compose
      (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) w)).embedUnitary
      JunctionUncondHadTailCut.uTailHadLocal8).1 := fun w ↦ by
    rw [QRegister.embedUnitary_val]
    refine CommutesWithReg.of_disjoint (QRegister.disjoint_iff.mpr fun i b heq ↦ ?_) _
    have hv : 0 + (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) w i).val = 3951 + b.val :=
      congrArg Fin.val heq
    have hlt : (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) w i).val < 3948 := by
      fin_cases w <;> fin_cases i <;> decide
    have := b.isLt; omega
  have hTH : CommutesWithReg (rCtrl3InCoreCat 36) (rCoreInCoreCat36.embedUnitary
      (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80))).1 := by
    unfold JunctionUncondHadTailCut.uTailHad3DCore
    simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, Submonoid.coe_mul]
    exact (hAx 0).mul ((hAx 1).mul (hAx 2))
  let B := rCoreInCoreCat36.embedUnitary
    (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80))⁻¹
  have hB : CommutesWithReg (rCtrl3InCoreCat 36) B.1 := by
    dsimp only [B]; rw [QRegister.embedUnitary_inv]
    rw [show ((rCoreInCoreCat36.embedUnitary
      (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)))⁻¹).1 =
      (rCoreInCoreCat36.embedUnitary
        (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80))).1ᴴ by
      simp [Matrix.star_eq_conjTranspose]]
    exact hTH.conjTranspose
  unfold uSlot3HadCutCat36FullSys unitaryConj
  change CommutesWithReg (rCtrl3InCoreCat 36)
    (B⁻¹ * castNatUnitary hCoreCat36_eq (uSlot3Swap3Cat36Norm1s t cfg) * B).1
  rw [Submonoid.coe_mul, Submonoid.coe_mul,
    show (B⁻¹).1 = B.1ᴴ by simp [Matrix.star_eq_conjTranspose]]
  exact (hB.conjTranspose.mul hU).mul hB

/- ## Section 3: `slot3HadCutLeafSpec36`, `0`-Step `rfl` `dSub36OfLeaf`, & `Leaf3Spec` -/

theorem dConjInvTailHad3D_realizes_fullSys36 {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWB n : ℕ} [NeZero (2 ^ n)] (rCF : QRegister (fullSysCoreWires 80) n)
    (rP : QRegister 36 n) (rWB : QRegister mWB n) (hCPF : rCF.DisjointWires rP)
    (hCWF : rCF.DisjointWires rWB) (hPW : rP.DisjointWires rWB)
    (UF : Unitary (2 ^ (fullSysCoreWires 80 + 36))) (d : DynamicCircuit Var n) (hdF :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCF.concat rP hCPF) rWB UF d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCF.concat rP hCPF) rWB
    (unitaryConj (rCoreInCoreCat36.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹) UF)
    (JunctionUncondHadTailCut.dConjInvTailHad3D rCF d) := by
  let rCT := rCF.concat rP hCPF
  have hDisj : rCT.DisjointWires rWB := disjointWires_concat_left hCPF hCWF hPW
  have hConcatCore : rCT.compose rCoreInCoreCat36 = rCF := qreg_ext fun i ↦ by
    change rCT (rCoreInCoreCat36 i) = rCF i
    rw [show rCoreInCoreCat36 i = Fin.castAdd 36 i from Fin.ext (Nat.zero_add i.val),
      QRegister.concat_apply_left]
  let B_ct : Unitary (2 ^ (fullSysCoreWires 80 + 36)) :=
    rCoreInCoreCat36.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
  have hPre : (JunctionUncondHadTailCut.cTailHad_3D rCF).inverse.eval = rCT.embedUnitary B_ct := by
    dsimp only [B_ct]
    rw [Circuit.eval_inverse, JunctionUncondHadTailCut.cTailHad_3D_eval,
      ← QRegister.embedUnitary_inv, ← QRegister.embedUnitary_compose, hConcatCore]
  have hPost : ((JunctionUncondHadTailCut.cTailHad_3D rCF).inverse).inverse.eval =
      rCT.embedUnitary B_ct⁻¹ := by rw [Circuit.eval_inverse, hPre, QRegister.embedUnitary_inv]
  have h1 := DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit (Var := Var)
    rCT rWB B_ct (JunctionUncondHadTailCut.cTailHad_3D rCF).inverse hPre
  have h3 := DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit (Var := Var)
    rCT rWB B_ct⁻¹ ((JunctionUncondHadTailCut.cTailHad_3D rCF).inverse).inverse hPost
  simpa only [JunctionUncondHadTailCut.dConjInvTailHad3D,
    FusedVepCore288.dPureConj,
    unitaryConj, mul_assoc] using h1.seq hDisj (hdF.seq hDisj h3)

theorem dConjInvTailHad3D_realizes_mom36 {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWB n : ℕ} [NeZero (2 ^ n)] (rC : QRegister coreWires80 n) (rP : QRegister 36 n)
    (rWB : QRegister mWB n) (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB)
    (hPW : rP.DisjointWires rWB) (U : Unitary (2 ^ (coreWires80 + 36)))
    (d : DynamicCircuit Var n) (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rC.concat rP hCP) rWB U d) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rC.concat rP hCP) rWB (castNatUnitary hCoreCat36_eq.symm (unitaryConj
    (rCoreInCoreCat36.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹) (castNatUnitary
    hCoreCat36_eq U))) (JunctionUncondHadTailCut.dConjInvTailHad3D (castNatReg hCore80_eq rC) d)
    := by
  have hGen : ∀ {a : ℕ} (ha : a = fullSysCoreWires 80)
      (hab : a + 36 = fullSysCoreWires 80 + 36) (rA : QRegister a n)
      (hAP : rA.DisjointWires rP) (hAW : rA.DisjointWires rWB) (UA : Unitary (2 ^ (a + 36))),
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rA.concat rP hAP) rWB UA d →
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rA.concat rP hAP) rWB
      (castNatUnitary hab.symm (unitaryConj (rCoreInCoreCat36.embedUnitary
      (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹) (castNatUnitary hab UA)))
      (JunctionUncondHadTailCut.dConjInvTailHad3D (castNatReg ha rA) d) := by
    intro a ha hab rA hAP hAW UA hRealA; subst ha
    obtain rfl : hab = rfl := Subsingleton.elim _ _
    exact dConjInvTailHad3D_realizes_fullSys36 rA rP rWB hAP hAW hPW UA d hRealA
  exact hGen hCore80_eq hCoreCat36_eq rC hCP hCW U hd

abbrev Slot3Leaf36Prog (mWB : ℕ) := SpecsAux.SpecMirror.Configuration → ∀ {Var : Type} {n : ℕ}, Var
    → (rC : QRegister coreWires80 n) → (rP : QRegister 36 n) → (rWB : QRegister mWB n) →
    rC.DisjointWires rP → rC.DisjointWires rWB → rP.DisjointWires rWB → DynamicCircuit Var n

theorem castNatReg_disj_left {a b m n : ℕ} (h : a = b) (r : QRegister a n)
    (rW : QRegister m n) (hd : r.DisjointWires rW) : (castNatReg h r).DisjointWires rW := by
  subst h; exact hd

/-- Canonical `0`-step `rfl` circuit adapter splitting `rSub : QRegister (fullSysCoreWires 80 + 36)
  n`
into `(rCore0_36, rCat0_36)` so `CleanLeafSpec 36 mWB` and `Leaf3Spec` share one `dSlot3*`
definition by `rfl`. -/
def dSub36OfLeaf {mWB : ℕ} (dLeaf : Slot3Leaf36Prog mWB) (c : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rSub : QRegister (fullSysCoreWires 80 + 36) n)
    (rWB : QRegister mWB n) (hSW : rSub.DisjointWires rWB) : DynamicCircuit Var n :=
  let rSubM : QRegister (coreWires80 + 36) n := castNatReg hCoreCat36_eq.symm rSub
  let hSWM : rSubM.DisjointWires rWB := castNatReg_disj_left hCoreCat36_eq.symm rSub rWB hSW
  dLeaf c v (rSubM.compose rCore0_36) (rSubM.compose rCat0_36) rWB
    (disjointWires_compose_of_disjoint rSubM hCoreCatDisj36)
    (hSWM.compose_left rCore0_36)
    (hSWM.compose_left rCat0_36)

theorem count_dSub36OfLeaf_toff {mWB : ℕ} (dLeaf : Slot3Leaf36Prog mWB)
    (c : SpecsAux.SpecMirror.Configuration) {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister (fullSysCoreWires 80 + 36) n) (rWB : QRegister mWB n)
    (hSW : rSub.DisjointWires rWB) (hToff : ∀ (rC : QRegister coreWires80 n) (rP : QRegister
    36 n) (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires
    rWB), (dLeaf c v rC rP rWB hCP hCW hPW).count .TOFF = 0) :
    (dSub36OfLeaf dLeaf c v rSub rWB hSW).count .TOFF = 0 := hToff _ _ _ _ _

theorem count_dSub36OfLeaf_t_le {mWB tCap : ℕ} (dLeaf : Slot3Leaf36Prog mWB)
    (c : SpecsAux.SpecMirror.Configuration) {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister (fullSysCoreWires 80 + 36) n) (rWB : QRegister mWB n)
    (hSW : rSub.DisjointWires rWB) (hT : ∀ (rC : QRegister coreWires80 n) (rP : QRegister 36
    n) (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB),
    (dLeaf c v rC rP rWB hCP hCW hPW).count .T ≤ tCap) :
    (dSub36OfLeaf dLeaf c v rSub rWB hSW).count .T ≤ tCap := hT _ _ _ _ _

theorem dSub36OfLeaf_realizes {mWB : ℕ} (dLeaf : Slot3Leaf36Prog mWB)
    (c : SpecsAux.SpecMirror.Configuration) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rSub : QRegister (fullSysCoreWires 80 + 36) n)
    (rWB : QRegister mWB n) (hSW : rSub.DisjointWires rWB)
    (UM : Unitary (2 ^ (coreWires80 + 36))) (hReal : ∀ (rC : QRegister coreWires80 n) (rP :
    QRegister 36 n) (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW :
    rP.DisjointWires rWB), DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rC.concat
    rP hCP) rWB UM (dLeaf c v rC rP rWB hCP hCW hPW)) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rSub rWB
    (castNatUnitary hCoreCat36_eq UM) (dSub36OfLeaf dLeaf c v rSub rWB hSW) := by
  let rSubM : QRegister (coreWires80 + 36) n := castNatReg hCoreCat36_eq.symm rSub
  let hSWM : rSubM.DisjointWires rWB := castNatReg_disj_left hCoreCat36_eq.symm rSub rWB hSW
  let hCP := disjointWires_compose_of_disjoint rSubM hCoreCatDisj36
  have hConcat : (rSubM.compose rCore0_36).concat (rSubM.compose rCat0_36) hCP = rSubM := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact congrArg rSubM (Fin.ext (Nat.zero_add i.val))
    · rw [QRegister.concat_apply_right]
      rfl
  have hM := Leaf3Slot3Norm1sWidth204.Internal.realizesEmbedded_eq_left hConcat rWB
    (hReal (rSubM.compose rCore0_36) (rSubM.compose rCat0_36) hCP
      (hSWM.compose_left rCore0_36) (hSWM.compose_left rCat0_36))
  have hGen : ∀ {a b : ℕ} (hab : a = b) (rB : QRegister b n) (UA : Unitary (2 ^ a))
      (d : DynamicCircuit Var n),
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (castNatReg hab.symm rB) rWB UA d →
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rB rWB (castNatUnitary hab UA) d := by
    intro a b hab rB UA d hIn
    subst hab; exact hIn
  exact hGen hCoreCat36_eq rSub UM (dSub36OfLeaf dLeaf c v rSub rWB hSW) hM

set_option maxRecDepth 512
set_option exponentiation.threshold 256

end ConfigLeaf3HadCutBridge

end Leaf3HadCutBridge

end
set_option exponentiation.threshold 256
end Leaf3HadCutBridge

section Slot3ZRetCore
local instance (priority := 1000000) instNeZeroTwoPow_Slot3ZRetCore (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
Retained-Scratch `K_wrapLin`, `ZRet`, and Fused `ZQuadRet` Outer Building Blocks (`M = 437`)
for Compact Slot-3 Oracles.

Provides:
1. Linear `0`-`TempAnd` wrap-head context `K_wrapLin` (`-24 T` across forward
   `sTrue18FwdPBuf_fast158_275` and asymmetric uncompute `dSTrue18RevPBuf142_275 = 568 T`).
2. Retained zero-magnitude flags `retZeroMW` on wires `254..256` (`zMag3Ret18_275`,
   `dZMag3Rev15_275 = 60 T`, `s3FlipFromZ3_275`, `validStaticFromZ28_275`,
   `dValidStaticFromZRev27_275 = 108 T`, `pStep1ZRet30 = 1,276 T`, `pStep5ZRet30 = 108 T`,
   `dRevTailZRet216_275 = 276 T`, saving `-84 T` on top of `K_wrapLin` for `-108 T` total).
3. Retained `mu`-quadratic flags `retMuQuadW` on wires `251..253` (`muQuad3Ret3_275`,
   `0 T` `dClearRetMuQuad0_275`, fused `5`-`TempAnd` `muAndQuadXor5_275`, `60`-`TempAnd`
   `magUnpackFromRetQuad60_275`, `0 T` `dMagUnpackFromRetQuad0_275`,
   `pStep1Fast316_ZQuadRet30 = 1,264 T`, and `dRevTailZQuadRet216_275 = 264 T`,
   reaching `-120 T` with post-Stage-1 clear or `-132 T` when `251..253` stay live).
-/

namespace Slot3ZRetCore

section ConfigSlot3ZRetCore

set_option maxRecDepth 8192

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open MeasureBranchHadamardSem (bit_cases RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open MomSlots35Slot3ProjNuclear
  (shellMu3 shellMu3_lt_seven shellMagCoord3 s3ShellMagCoord3_lt_128)
open StepBBlock0 Prod57BoothHoist
open StepBOuter Slot3Exact216Oracle80
open Slot3Outer2344AndRelayWide
open Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31
  (axisStep3_fast_275 axisStep3_fast_275_spec)
open Slot3Outer2344AndRelayWide.Slot3Exact216AsymUncomp
  (p57ToDynWith_realizes_prog_of_graft TempCtx.append_assoc
   mutMag21 magPairK magPairLhs magPairRhs magInnerLoopStatic magInnerLoopStatic_spec
   magInnerLoopStatic_valid_le dMagInnerLoop dMagInnerLoop_count_t dMagInnerLoop_count_toff
   dMagInnerLoop_preservesStore InvMagHole dMagInnerLoop_realizes
   InvMagRev InvValidStatic216Rev)
open Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore
  (top7MaxMag11Ops top7MaxMag11_meta top7MaxMag11Check top7MaxMag11_eval_ok
   vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj vsAnd5In216W vsAnd5In216W_inj
   validStatic216_fast46_275Ctx validStatic216_fast46_275 validStatic216_fast46_275_spec
   validStatic216_fast46_275_eq_orig magUnpack63_275Ctx magUnpack63_275 magUnpack63_275_spec)
open Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned
  (dXorBlock1Peel_realizes xorAndPairsStatic xorAndPairsStatic_countTempAnd
   xorAndPairsStatic_clear_spec dXorAndPairsUncomp dXorAndPairsUncomp_count_t
   dXorAndPairsUncomp_count_toff dXorAndPairsUncomp_preservesStore
   dXorAndPairsUncomp_realizes_static
   InvAxis1 dAxisStep3Rev_275
   InvRevTailPruned216)
open Slot3Outer2344AndRelayWide.Slot3Br31SharedDecodeAndBoothPruned
  (vsK6FastPre3Ctx)
open Slot3Outer2344AndRelayWide.Slot3Retained15522_Core
  (dCoinMuRev3_275)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide
  (cliffDisjointBad progDisjointBad progDisjointBad_eval isBadMW st0 st1)
open Slot3Outer2344AndRelayWide.Slot3UltraWidthWide
  (pStep1Ultra_evalBits_st0)

/- Section 1: Linear 0-TempAnd Wrap-Head Context K_wrapLin (-24 T) -/

theorem val_zero_eq_bitsVal_mod_two {W : ℕ} (f : Fin (W + 1) → ZMod 2) :
    (f 0).val = bitsVal f % 2 := by
  have h := Prod57BoothHoist.bitsVal_succ_split f
  have h0 : (f 0).val < 2 := ZMod.val_lt (f 0)
  omega

theorem ite_testBit_zero_val_eq_mod_two (x : ℕ) :
    (if x.testBit 0 then (1 : ZMod 2) else 0).val = x % 2 := by
  rw [Nat.testBit_zero]
  by_cases h : x % 2 = 1
  · simp [h]
  · have h0 : x % 2 = 0 := by omega
    simp [h]; omega

theorem wWrapFromPBufZMod_eq_linXor
    (fP : Fin 8 → ZMod 2) (fM : Fin 7 → ZMod 2) (pb0 pb7 sw : ZMod 2)
    (hpb0 : pb0 = if (p57AxisFastVal (bitsVal fP) (bitsVal fM) sw.val).testBit 0 then 1 else 0)
    (hpb7 : pb7 = if (p57AxisFastVal (bitsVal fP) (bitsVal fM) sw.val).testBit 7 then 1 else 0) :
    wWrapFromPBufZMod (fP ⟨7, by decide⟩) pb7 sw = fP 0 + pb0 + fM 0 := by
  have hp_lt : bitsVal fP < 256 := bitsVal_lt_two_pow fP
  have hm_lt : bitsVal fM < 128 := bitsVal_lt_two_pow fM
  have hp7 : fP ⟨7, by decide⟩ = if 128 ≤ bitsVal fP then 1 else 0 :=
    Prod57BoothHoist.bitsVal_last_seven_eq_ite fP
  have hp0 : (fP 0).val = bitsVal fP % 2 := val_zero_eq_bitsVal_mod_two fP
  have hm0 : (fM 0).val = bitsVal fM % 2 := val_zero_eq_bitsVal_mod_two fM
  have hfast_lt : p57AxisFastVal (bitsVal fP) (bitsVal fM) sw.val < 256 :=
    Nat.mod_lt _ (by decide)
  simp only [Prod57BoothHoist.nat_testBit_seven_of_lt_256 hfast_lt, decide_eq_true_eq] at hpb7
  have hpb0_val : pb0.val = p57AxisFastVal (bitsVal fP) (bitsVal fM) sw.val % 2 := by
    rw [hpb0, ite_testBit_zero_val_eq_mod_two]
  let rhs := if 255 - (if bitsVal fP < 128 then bitsVal fP + 128 else bitsVal fP - 128) <
      (if sw.val = 1 then 255 - bitsVal fM else bitsVal fM) then 1 - sw.val else sw.val
  have hW : (wWrapFromPBufZMod (fP ⟨7, by decide⟩) pb7 sw).val = rhs := by
    dsimp only [rhs]; rw [hp7, hpb7]
    generalize bitsVal fP = p at hp_lt ⊢; generalize bitsVal fM = m at hm_lt ⊢
    dsimp only [p57AxisFastVal]
    have h01 : ¬ ((0 : ℕ) = 1) := by decide
    rcases bit_cases sw with rfl | rfl
    · simp only [show (0 : ZMod 2).val = 0 from rfl, h01, ↓reduceIte]
      by_cases hp128 : p < 128
      · have hnp : ¬ 128 ≤ p := by omega
        by_cases hlt : 255 - (p + 128) < m
        · have hge : 128 ≤ (p + m + 1) % 256 := by omega
          simp only [hp128, hnp, hlt, ↓reduceIte, hge]; decide
        · have hng : ¬ 128 ≤ (p + m + 0) % 256 := by omega
          simp only [hp128, hnp, hlt, ↓reduceIte, hng]; decide
      · have hgep : 128 ≤ p := by omega
        have hnlt : ¬ 255 - (p - 128) < m := by omega
        by_cases hge : 128 ≤ (p + m + 0) % 256 <;>
          (simp only [hp128, hgep, hnlt, ↓reduceIte, hge]; decide)
    · simp only [show (1 : ZMod 2).val = 1 from rfl, ↓reduceIte]
      by_cases hp128 : p < 128
      · have hnp : ¬ 128 ≤ p := by omega
        have hlt : 255 - (p + 128) < 255 - m := by omega
        by_cases hge : 128 ≤ (p + (255 - m) + 1) % 256 <;>
          (simp only [hp128, hnp, hlt, ↓reduceIte, hge]; decide)
      · have hgep : 128 ≤ p := by omega
        by_cases hlt : 255 - (p - 128) < 255 - m
        · have hge : 128 ≤ (p + (255 - m) + 1) % 256 := by omega
          simp only [hp128, hgep, hlt, ↓reduceIte, hge]; decide
        · have hng : ¬ 128 ≤ (p + (255 - m) + 0) % 256 := by omega
          simp only [hp128, hgep, hlt, ↓reduceIte, hng]; decide
  have hL : (fP 0 + pb0 + fM 0).val = rhs := by
    dsimp only [rhs]
    rw [Prod57BoothHoist.zmod2_add3_val_mod2 (fP 0) pb0 (fM 0), hp0, hm0, hpb0_val]
    generalize bitsVal fP = p at hp_lt ⊢; generalize bitsVal fM = m at hm_lt ⊢
    dsimp only [p57AxisFastVal]
    have h01 : ¬ ((0 : ℕ) = 1) := by decide
    rcases bit_cases sw with rfl | rfl
    · simp only [show (0 : ZMod 2).val = 0 from rfl, h01, ↓reduceIte]
      split_ifs <;> omega
    · simp only [show (1 : ZMod 2).val = 1 from rfl, ↓reduceIte]
      split_ifs <;> omega
  exact Fin.ext (hW.trans hL.symm)

/-- Three-CNOT linear wrap-head writing `p[0] ⊕ pBuf[0] ⊕ m[0]` into `ww`. -/
def wrap7HeadLinW (p0 pb0 m0 ww : Wire 437) : List P57Step :=
  [.cnot p0.val ww.val, .cnot pb0.val ww.val, .cnot m0.val ww.val]

/-- Full `0`-`TempAnd` wrap-and-conditionally-complement step list for axis `w`. -/
def axisWrapLinSteps (w : Fin 3) : List P57Step :=
  wrap7HeadLinW (p57ProjW w 0) (p57PBufW w 0) (p57MW w 0) ⟨275 + w.val, by omega⟩ ++
    wrap7TailW ⟨275 + w.val, by omega⟩ (p57MW w)

theorem wrap7HeadLinW_eval (w : Fin 3) (γ : BitAssignment 437)
    (hww0 : γ ⟨275 + w.val, by omega⟩ = 0) :
    let p0 := p57ProjW w 0
    let pb0 := p57PBufW w 0
    let m0 := p57MW w 0
    let ww : Wire 437 := ⟨275 + w.val, by omega⟩
    evalP57Steps (wrap7HeadLinW p0 pb0 m0 ww) γ =
      Function.update γ ww (γ p0 + γ pb0 + γ m0) := by
  intro p0 pb0 m0 ww
  have h_pw : p0 ≠ ww := wire_ne_val (by dsimp [p0, ww, p57ProjW]; omega)
  have h_pbw : pb0 ≠ ww := wire_ne_val (by dsimp [pb0, ww, p57PBufW]; omega)
  have h_mw : m0 ≠ ww := wire_ne_val (by dsimp [m0, ww, p57MW]; omega)
  dsimp only [wrap7HeadLinW, evalP57Steps]
  rw [evalP57Step_cnot h_pw, evalP57Step_cnot h_pbw, evalP57Step_cnot h_mw]
  funext u
  by_cases hu : u = ww
  · subst hu
    have hww0' : γ ww = 0 := hww0
    simp [Function.update_self, Function.update_of_ne h_pbw,
      Function.update_of_ne h_mw, hww0', add_assoc]
  · simp [Function.update_of_ne hu]

theorem axisWrapLin_fwdBits (w : Fin 3) (γ : BitAssignment 437)
    (hww0 : γ ⟨275 + w.val, by omega⟩ = 0) (u : Wire 437) :
    let z := γ (p57ProjW w 0) + γ (p57PBufW w 0) + γ (p57MW w 0)
    (buildP57Ctx (axisWrapLinSteps w)).fwdBits γ u =
      if u = ⟨275 + w.val, by omega⟩ then z
      else if ∃ b : Fin 7, u = p57MW w b then γ u + z
      else γ u := by
  intro z
  rw [buildP57Ctx_fwdBits, axisWrapLinSteps, evalP57Steps_append,
    wrap7HeadLinW_eval w γ hww0, wrap7TailW_eval w]
  by_cases huw : u = ⟨275 + w.val, by omega⟩
  · subst huw
    have hnm : ¬ ∃ b : Fin 7, (⟨275 + w.val, by omega⟩ : Wire 437) = p57MW w b := by
      rintro ⟨b, hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega
    rw [ite_eq_left rfl, ite_eq_right hnm, Function.update_self]
  · rw [ite_eq_right huw]
    by_cases hex : ∃ b : Fin 7, u = p57MW w b
    · rw [ite_eq_left hex, ite_eq_left hex, Function.update_of_ne huw, Function.update_self]
    · rw [ite_eq_right hex, ite_eq_right hex, Function.update_of_ne huw]

/-- Linear `0`-`TempAnd` wrap-head `TempCtx` for axis `0`. -/
def K_wrapLin0 : TempCtx 437 := buildP57Ctx (axisWrapLinSteps 0)

/-- Linear `0`-`TempAnd` wrap-head `TempCtx` for axis `1`. -/
def K_wrapLin1 : TempCtx 437 := buildP57Ctx (axisWrapLinSteps 1)

/-- Linear `0`-`TempAnd` wrap-head `TempCtx` for axis `2`. -/
def K_wrapLin2 : TempCtx 437 := buildP57Ctx (axisWrapLinSteps 2)

/-- Combined `0`-`TempAnd` wrap-head `TempCtx` across all three axes (`-3` `TempAnd`s per call). -/
def K_wrapLin : TempCtx 437 := K_wrapLin0.append (K_wrapLin1.append K_wrapLin2)

theorem K_wrapLin_pkg278 : P57CtxPkg 278 278 0 K_wrapLin :=
  (buildP57Ctx_pkg (by decide : wfP57Steps 278 (axisWrapLinSteps 0) = some (278, 0))).append
    ((buildP57Ctx_pkg (by decide : wfP57Steps 278 (axisWrapLinSteps 1) = some (278, 0))).append
      (buildP57Ctx_pkg (by decide : wfP57Steps 278 (axisWrapLinSteps 2) = some (278, 0))))

theorem K_wrapLin_pkg : P57CtxPkg 275 278 0 K_wrapLin where
  le_end := by decide
  end_le := by decide
  cnt_eq := K_wrapLin_pkg278.cnt_eq
  disj := K_wrapLin_pkg278.disj
  supp := K_wrapLin_pkg278.supp
  lift := StepBBlock0.TempCtxLiftEx.mono (by decide) le_rfl (by decide) K_wrapLin_pkg278.lift
  clean β hβ := K_wrapLin_pkg278.clean β (cleanRem_anti (by decide) hβ)

/-- Retained-axis parity invariant guaranteeing `p[0] ⊕ pBuf[0] ⊕ m[0] = wWrap` on every axis. -/
def InvWrapLin (β : BitAssignment 437) : Prop :=
  ∀ w : Fin 3,
    β (p57ProjW w 0) + β (p57PBufW w 0) + β (p57MW w 0) =
      wWrapFromPBufZMod (β (p57ProjW w ⟨7, by decide⟩)) (β (p57PBufW w ⟨7,
        by decide⟩)) (β (p57S3W w))

theorem InvWrapLin_of_invAxis (β : BitAssignment 437) (hAx : ∀ w : Fin 3, InvAxis1 w β) :
    InvWrapLin β := fun w ↦
  (wWrapFromPBufZMod_eq_linXor
    (fun j ↦ β (p57ProjW w j))
    (fun j ↦ β (p57MW w j))
    (β (p57PBufW w 0))
    (β (p57PBufW w ⟨7, by decide⟩))
    (β (p57S3W w))
    (hAx w 0)
    (hAx w ⟨7, by decide⟩)).symm

theorem K_wrapLin_fwdBits_eq (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β)
    (hW : InvWrapLin β) : K_wrapLin.fwdBits β = K_wrap.fwdBits β := by
  have ha0 : β ⟨275, by decide⟩ = 0 := hβ ⟨275, by decide⟩ (by decide)
  have h0 : K_wrapLin0.fwdBits β = K_wrap0.fwdBits β := funext fun u ↦ by
    dsimp only [K_wrapLin0, K_wrap0]
    rw [axisWrapLin_fwdBits 0 β ha0 u, axisWrap_fwdBits 0 β ha0 u, hW 0]
  set βa := K_wrap0.fwdBits β
  have hpres0 (u : Wire 437) (hm : ¬(177 ≤ u.val ∧ u.val < 184)) (hu : u.val ≠ 275) :
      βa u = β u := by
    dsimp only [βa, K_wrap0]
    rw [axisWrap_fwdBits 0 β ha0, ite_eq_right (fun h ↦ hu (by
      have hv := congrArg Fin.val h
      dsimp at hv
      omega)), ite_eq_right (by
      rintro ⟨b, rfl⟩
      exact hm ((by decide : ∀ b' : Fin 7, 177 ≤ (p57MW 0 b').val ∧ (p57MW 0 b').val < 184) b))]
  have hb0 : βa ⟨276, by decide⟩ = 0 :=
    (hpres0 _ (by decide) (by decide)).trans (hβ _ (by decide))
  have hW_pres (w : Fin 3) (hw12 : w = 1 ∨ w = 2) (γ : BitAssignment 437)
      (hp : ∀ u : Wire 437, ¬(177 ≤ u.val ∧ u.val < 177 + 7 * w.val) → u.val < 275 → γ u = β u) :
      γ (p57ProjW w 0) + γ (p57PBufW w 0) + γ (p57MW w 0) =
        wWrapFromPBufZMod (γ (p57ProjW w ⟨7, by decide⟩)) (γ (p57PBufW w ⟨7, by decide⟩))
          (γ (p57S3W w)) := by
    rcases hw12 with rfl | rfl
    · rw [hp _ (by decide) (by decide), hp _ (by decide) (by decide),
        hp _ (by decide) (by decide), hp _ (by decide) (by decide),
        hp _ (by decide) (by decide), hp _ (by decide) (by decide)]
      exact hW 1
    · rw [hp _ (by decide) (by decide), hp _ (by decide) (by decide),
        hp _ (by decide) (by decide), hp _ (by decide) (by decide),
        hp _ (by decide) (by decide), hp _ (by decide) (by decide)]
      exact hW 2
  have hW1 := hW_pres 1 (Or.inl rfl) βa fun u hm hu ↦ hpres0 u hm (by omega)
  have h1 : K_wrapLin1.fwdBits βa = K_wrap1.fwdBits βa := funext fun u ↦ by
    dsimp only [K_wrapLin1, K_wrap1]
    rw [axisWrapLin_fwdBits 1 βa hb0 u, axisWrap_fwdBits 1 βa hb0 u, hW1]
  set βb := K_wrap1.fwdBits βa
  have hpres1 (u : Wire 437) (hm : ¬(177 ≤ u.val ∧ u.val < 191))
      (hu0 : u.val ≠ 275) (hu1 : u.val ≠ 276) : βb u = β u := by
    dsimp only [βb, K_wrap1]
    rw [axisWrap_fwdBits 1 βa hb0, ite_eq_right (fun h ↦ hu1 (by
      have hv := congrArg Fin.val h
      dsimp at hv
      omega)), ite_eq_right (by
      rintro ⟨b, rfl⟩
      exact hm ((by decide : ∀ b' : Fin 7, 177 ≤ (p57MW 1 b').val ∧ (p57MW 1 b').val < 191) b))]
    exact hpres0 u (by omega) hu0
  have hc0 : βb ⟨277, by decide⟩ = 0 :=
    (hpres1 _ (by decide) (by decide) (by decide)).trans (hβ _ (by decide))
  have hW2 := hW_pres 2 (Or.inr rfl) βb fun u hm hu ↦ hpres1 u hm (by omega) (by omega)
  have h2 : K_wrapLin2.fwdBits βb = K_wrap2.fwdBits βb := funext fun u ↦ by
    dsimp only [K_wrapLin2, K_wrap2]
    rw [axisWrapLin_fwdBits 2 βb hc0 u, axisWrap_fwdBits 2 βb hc0 u, hW2]
  dsimp only [K_wrapLin, K_wrap]
  repeat rw [Prod57BoothHoist.TempCtx.append_fwdBits]
  rw [h0, h1, h2]

/-- `79`-`TempAnd` pre-reduction `TempCtx` pairing `K_wrapLin` (`0`) with `K_ax0..2` (`79`). -/
def K_preRed79_lin : TempCtx 437 := K_wrapLin.append (K_ax0.append (K_ax1.append K_ax2))

/-- `156`-`TempAnd` forward `sTrue18` joint `TempCtx` (`K_preRed79_lin` + `K_red77`). -/
def ctxJointPBuf156 : TempCtx 437 := K_preRed79_lin.append K_red77

theorem K_preRed79_lin_pkg : P57CtxPkg 275 357 79 K_preRed79_lin :=
  K_wrapLin_pkg.append (K_ax0_pkg.append (K_ax1_pkg.append K_ax2_pkg))

theorem ctxJointPBuf156_pkg : P57CtxPkg 275 434 156 ctxJointPBuf156 :=
  K_preRed79_lin_pkg.append K_red77_sound.1

theorem ctxJointPBuf156_fwdBits_eq (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β)
    (hW : InvWrapLin β) : ctxJointPBuf156.fwdBits β = ctxJointPBuf159.fwdBits β := by
  dsimp only [ctxJointPBuf156, K_preRed79_lin, ctxJointPBuf159, K_preRed82]
  repeat rw [Prod57BoothHoist.TempCtx.append_fwdBits]
  rw [K_wrapLin_fwdBits_eq β hβ hW]

/-- `158`-`TempAnd` (`632 T`) forward `sTrue18` adder using `K_wrapLin` (`-12 T` vs `161`
  `TempAnd`s). -/
def sTrue18FwdPBuf_fast158_275 : TempPhaseProg 437 := ctxJointPBuf156.plug innerApex2

open Classical in
theorem sTrue18FwdPBuf_fast158_275_graft : ValidCleanRem 437 (437 - 275)
    sTrue18FwdPBuf_fast158_275 ∧ sTrue18FwdPBuf_fast158_275.countTempAnd = 158 ∧ (∀ β :
    BitAssignment 437, cleanRem 437 (437 - 275) β → sTrue18FwdPBuf_fast158_275.evalSign β = 0)
    ∧ (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β → (∀ q : Wire 437, ¬ mutSTrue q →
    sTrue18FwdPBuf_fast158_275.evalBits β q = β q) ∧ (∀ j : Fin 18,
    sTrue18FwdPBuf_fast158_275.evalBits β (sTrue18WDefault j) = β (sTrue18WDefault j) +
    targetBit (ctxJointPBuf156.fwdBits β) j)) := by
  obtain ⟨hvIn, hcIn, _, hsIn, hbIn⟩ := innerApex2_spec
  have hpkg := ctxJointPBuf156_pkg
  obtain ⟨hv, hcnt, hsgn, hbits⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean (M := 437) (rem := 437 - 275) (curHole := 434)
      mutSTrue ctxJointPBuf156 hpkg.disj hpkg.supp (by decide)
      ctxJointPBuf156.fwdBits (StepBBlock0.TempCtxLiftEx.probe hpkg.lift) innerApex2 hvIn
      (fun γ hγ w hnw ↦ (hbIn γ hγ).1 w hnw)
  refine ⟨hv, by dsimp [sTrue18FwdPBuf_fast158_275]; rw [hcnt, hpkg.cnt_eq, hcIn], fun β hβ ↦ ?_,
    fun β hβ ↦ ⟨fun q hnq ↦ ?_, fun j ↦ ?_⟩⟩
  · dsimp [sTrue18FwdPBuf_fast158_275]
    rw [hsgn β hβ, hsIn _ (hpkg.clean β hβ)]
  · dsimp [sTrue18FwdPBuf_fast158_275]
    rw [hbits β hβ q, ite_eq_right hnq]
  · dsimp [sTrue18FwdPBuf_fast158_275]
    have hm : mutSTrue (sTrue18WDefault j) := ⟨j, rfl⟩
    rw[hbits β hβ (sTrue18WDefault j), ite_eq_left hm, (hbIn _ (hpkg.clean β hβ)).2 j,
        Prod57BoothHoist.TempCtx.fwdBits_mut hpkg.disj β hm]

theorem sTrue18FwdPBuf_fast158_275_eq_orig (β : BitAssignment 437)
    (hβ : cleanRem 437 (437 - 275) β) (hW : InvWrapLin β) :
    sTrue18FwdPBuf_fast158_275.evalBits β = sTrue18FwdPBuf275.evalBits β := by
  obtain ⟨_, _, _, h1⟩ := sTrue18FwdPBuf_fast158_275_graft
  obtain ⟨_, _, _, h2⟩ := sTrue18FwdPBuf275_graft
  funext q
  by_cases hq : mutSTrue q
  · obtain ⟨j, rfl⟩ := hq
    rw [(h1 β hβ).2 j, (h2 β hβ).2 j, ctxJointPBuf156_fwdBits_eq β hβ hW]
  · exact ((h1 β hβ).1 q hq).trans ((h2 β hβ).1 q hq).symm

def ctxDisjointBad {M : ℕ} (bad : Wire M → Bool) : TempCtx M → Bool
  | .hole => true
  | .seqPre c K => cliffDisjointBad bad c && ctxDisjointBad bad K
  | .seqPost K c => ctxDisjointBad bad K && cliffDisjointBad bad c
  | .tempAnd c₁ c₂ anc _ _ _ K => !bad c₁ && (!bad c₂ && (!bad anc && ctxDisjointBad bad K))

theorem progDisjointBad_plug {M : ℕ} (bad : Wire M → Bool) :
    ∀ (K : TempCtx M) (body : TempPhaseProg M),
      progDisjointBad bad (K.plug body) = (ctxDisjointBad bad K && progDisjointBad bad body)
  | .hole, _ => by simp [TempCtx.plug, ctxDisjointBad]
  | .seqPre c K, body => by
      simp only [TempCtx.plug, progDisjointBad, ctxDisjointBad, progDisjointBad_plug bad K body,
        Bool.and_assoc]
  | .seqPost K c, body => by
      simp only [TempCtx.plug, progDisjointBad, ctxDisjointBad, progDisjointBad_plug bad K body]
      cases ctxDisjointBad bad K <;> cases progDisjointBad bad body <;>
        cases cliffDisjointBad bad c <;> rfl
  | .tempAnd c₁ c₂ anc _ _ _ K, body => by
      simp only [TempCtx.plug, progDisjointBad, ctxDisjointBad, progDisjointBad_plug bad K body,
        Bool.and_assoc]

theorem ctxDisjointBad_append {M : ℕ} (bad : Wire M → Bool) :
    ∀ (K₁ K₂ : TempCtx M),
      ctxDisjointBad bad (K₁.append K₂) = (ctxDisjointBad bad K₁ && ctxDisjointBad bad K₂)
  | .hole, _ => by simp [TempCtx.append, ctxDisjointBad]
  | .seqPre c K₁, K₂ => by
      simp only [TempCtx.append, ctxDisjointBad, ctxDisjointBad_append bad K₁ K₂, Bool.and_assoc]
  | .seqPost K₁ c, K₂ => by
      simp only [TempCtx.append, ctxDisjointBad, ctxDisjointBad_append bad K₁ K₂]
      cases ctxDisjointBad bad K₁ <;> cases ctxDisjointBad bad K₂ <;>
        cases cliffDisjointBad bad c <;> rfl
  | .tempAnd c₁ c₂ anc _ _ _ K₁, K₂ => by
      simp only [TempCtx.append, ctxDisjointBad, ctxDisjointBad_append bad K₁ K₂, Bool.and_assoc]

/-- Stage-1 preparation pipeline using `sTrue18FwdPBuf_fast158_275` (`K_wrapLin`). -/
def pStep1Lin : TempPhaseProg 437 := .seq coinMuXor275 (.seq magUnpack63_275 (.seq
    validStatic216_fast46_275 (.seq axisStep3_fast_275 sTrue18FwdPBuf_fast158_275)))

theorem st0_coinMu_props (α : BitAssignment 149) :
    cleanRem 437 (437 - 275) (st0 α) ∧
    (∀ q : Wire 437, 149 ≤ q.val → st0 α q = 0) ∧
    cleanRem 437 (437 - 275) (coinMuXor275.evalBits (st0 α)) ∧
    (∀ q : Wire 437, q.val ≠ 198 → ¬(174 ≤ q.val ∧ q.val < 177) →
      coinMuXor275.evalBits (st0 α) q = st0 α q) ∧
    getU22 (coinMuXor275.evalBits (st0 α)) = getU22 (st0 α) ∧
    (∀ j : Fin 3, coinMuXor275.evalBits (st0 α) (muW j) =
      if (shellMu3 (getU22 (st0 α))).testBit j.val then 1 else 0) := by
  obtain ⟨hB1, hE1⟩ := coinMuXor275_spec
  have hcl₀ : cleanRem 437 (437 - 275) (st0 α) :=
    cleanRem_anti (by decide) (padZeroBits149_clean α)
  have hz₀ : ∀ q : Wire 437, 149 ≤ q.val → st0 α q = 0 :=
    fun q hq ↦ padZeroBits149_clean α q (by omega)
  have hp1 : ∀ q : Wire 437, q.val ≠ 198 → ¬(174 ≤ q.val ∧ q.val < 177) →
      coinMuXor275.evalBits (st0 α) q = st0 α q :=
    fun q hc hm ↦ hB1.2.2.2 (st0 α) hcl₀ q (fun h ↦ by
      rcases h with rfl | ⟨j, rfl⟩
      · exact hc rfl
      · exact hm ⟨by dsimp [muW]; omega, by dsimp [muW]; omega⟩)
  refine ⟨hcl₀, hz₀, hB1.2.2.1 (st0 α) hcl₀, hp1,
    getU22_congr (fun i ↦ hp1 _ (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega)),
    fun j ↦ ?_⟩
  rw [(hE1 (st0 α) hcl₀).2 j, hz₀ _ (by dsimp [muW]; omega), zero_add,
    top7_eq_shellMu3_216 (st0 α)]

theorem pStep1Lin_evalBits_st0 (α : BitAssignment 149) :
    pStep1Lin.evalBits (st0 α) = st1 α := by
  rw [← pStep1Ultra_evalBits_st0 α]
  obtain ⟨_, hz₀, hcl₁, hp1, _, _⟩ := st0_coinMu_props α
  obtain ⟨hB2, _, _⟩ := magUnpack63_275_spec
  obtain ⟨hB3, _, _⟩ := validStatic216_fast46_275_spec
  obtain ⟨hB4, _, hE4⟩ := axisStep3_fast_275_spec
  let β₁ := coinMuXor275.evalBits (st0 α)
  let β₂ := magUnpack63_275.evalBits β₁
  let β₃ := validStatic216_fast46_275.evalBits β₂
  let β₄ := axisStep3_fast_275.evalBits β₃
  have hcl₂ := hB2.2.2.1 β₁ hcl₁
  have hcl₃ := hB3.2.2.1 β₂ hcl₂
  have hp2 : ∀ q : Wire 437, ¬(177 ≤ q.val ∧ q.val < 198) → β₂ q = β₁ q :=
    fun q hm ↦ hB2.2.2.2 β₁ hcl₁ q (fun ⟨w, b, hq⟩ ↦ by
      subst hq; exact hm ⟨by dsimp [p57MW]; omega, by dsimp [p57MW]; omega⟩)
  have hp3 : ∀ q : Wire 437, q.val ≠ 258 → β₃ q = β₂ q :=
    fun q hv ↦ hB3.2.2.2 β₂ hcl₂ q (fun h ↦ hv (by subst h; rfl))
  have hp4 : ∀ q : Wire 437, ¬(150 ≤ q.val ∧ q.val < 174) → β₄ q = β₃ q :=
    fun q hp ↦ hB4.2.2.2 β₃ hcl₃ q (fun ⟨w, b, h⟩ ↦ by
      subst h; exact hp ⟨by dsimp [pBufW]; omega, by dsimp [pBufW]; omega⟩)
  have hAx4 : ∀ w : Fin 3, InvAxis1 w β₄ := fun w b ↦ by
    have hz : β₃ (pBufW w b) = 0 :=
      (hp3 _ (by dsimp [pBufW]; omega)).trans ((hp2 _ (by dsimp [pBufW]; omega)).trans
        ((hp1 _ (by dsimp [pBufW]; omega) (by dsimp [pBufW]; omega)).trans
          (hz₀ _ (by dsimp [pBufW]; omega))))
    have hev := hE4 β₃ hcl₃ w b
    change β₄ (pBufW w b) = _ at hev; rw [hz, zero_add] at hev
    simpa only [show (fun j ↦ β₄ (p57ProjW w j)) = fun j ↦ β₃ (p57ProjW w j) from
        funext fun j ↦ hp4 _ (by dsimp [p57ProjW]; omega),
      show (fun j ↦ β₄ (p57MW w j)) = fun j ↦ β₃ (p57MW w j) from
        funext fun j ↦ hp4 _ (by dsimp [p57MW]; omega),
      hp4 (p57S3W w) (by dsimp [p57S3W]; omega)] using hev
  exact sTrue18FwdPBuf_fast158_275_eq_orig β₄ (hB4.2.2.1 β₃ hcl₃) (InvWrapLin_of_invAxis β₄ hAx4)

/- Section 2: Retained Zero-Magnitude Flags `retZeroMW` (`254..256`, `-84 T`) -/

theorem fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ w : Fin 3, P w
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- Retained `mu`-quadratic wires `251..253` (`mu_0*mu_1`, `mu_0*mu_2`, `mu_1*mu_2`). -/
def retMuQuadW : Fin 3 → Wire 437 :=
  ![⟨251, by decide⟩, ⟨252, by decide⟩, ⟨253, by decide⟩]

theorem retMuQuadW_inj : Function.Injective retMuQuadW := fun i j h ↦ by
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)

/-- Retained zero-magnitude flag wires `254..256` (`decide (|n_w| = 0)`). -/
def retZeroMW (w : Fin 3) : Wire 437 := ⟨254 + w.val, by omega⟩

/-- Left factor wires `(mu_0, mu_0, mu_1)` for the three quadratic `mu` monomials. -/
def lhsQuad3 : Fin 3 → Wire 437 := ![muW 0, muW 0, muW 1]

/-- Right factor wires `(mu_1, mu_2, mu_2)` for the three quadratic `mu` monomials. -/
def rhsQuad3 : Fin 3 → Wire 437 := ![muW 1, muW 2, muW 2]

theorem lhsQuad3_ne_rhs (j : Fin 3) : lhsQuad3 j ≠ rhsQuad3 j := by
  fin_cases j <;> decide

theorem lhsQuad3_lt275 (j : Fin 3) : (lhsQuad3 j).val < 275 := by
  fin_cases j <;> decide

theorem rhsQuad3_lt275 (j : Fin 3) : (rhsQuad3 j).val < 275 := by
  fin_cases j <;> decide

theorem retMuQuadW_lt275 (j : Fin 3) : (retMuQuadW j).val < 275 := by
  fin_cases j <;> decide

theorem xorAndPairsStatic_add_spec {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + 1 ≤ M) (lhs rhs acc : Fin W → Wire M)
      (hlr : ∀ j, lhs j ≠ rhs j)
      (_hl_a : ∀ i j : Fin W, lhs i ≠ acc j)
      (_hr_a : ∀ i j : Fin W, rhs i ≠ acc j)
      (_ha_inj : Function.Injective acc)
      (hl_lt : ∀ j, (lhs j).val < cur) (hr_lt : ∀ j, (rhs j).val < cur) (ha_lt : ∀ j,
        (acc j).val < cur),
      let p := xorAndPairsStatic W cur hcur lhs rhs acc hlr hl_lt hr_lt ha_lt
      ValidCleanRem M (M - cur) p ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β → p.evalSign β = 0) ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - cur) (p.evalBits β) ∧
          (∀ w : Wire M, (∀ j, w ≠ acc j) → p.evalBits β w = β w) ∧
          (∀ j : Fin W, p.evalBits β (acc j) = β (acc j) + β (lhs j) * β (rhs j)))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨trivial, fun _ _ ↦ rfl, fun β hβ ↦ ⟨hβ, fun _ _ ↦ rfl, fun j ↦ Fin.elim0 j⟩⟩
  | W + 1, cur, hcur, lhs, rhs, acc, hlr, hl_a, hr_a, ha_inj, hl_lt, hr_lt, ha_lt => by
      dsimp only [xorAndPairsStatic]
      obtain ⟨hv0, _, hs0, hb0⟩ := msbClearStatic_spec cur hcur (lhs 0) (rhs 0) (acc 0)
        (hlr 0) (hl_a 0 0) (hr_a 0 0) (hl_lt 0) (hr_lt 0) (ha_lt 0)
      obtain ⟨hvR, hsR, hR⟩ := xorAndPairsStatic_add_spec W cur hcur
        (fun j ↦ lhs j.succ) (fun j ↦ rhs j.succ) (fun j ↦ acc j.succ)
        (fun j ↦ hlr j.succ) (fun i j ↦ hl_a i.succ j.succ) (fun i j ↦ hr_a i.succ j.succ)
        (ha_inj.comp (Fin.succ_injective W))
        (fun j ↦ hl_lt j.succ) (fun j ↦ hr_lt j.succ) (fun j ↦ ha_lt j.succ)
      have hcl0 : ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - cur)
            ((msbClearStatic cur hcur (lhs 0) (rhs 0) (acc 0) (hlr 0) (hl_lt 0) (hr_lt 0)
              (ha_lt 0)).evalBits β) := by
        intro β hβ w hw
        rw [hb0 β hβ, Function.update_of_ne (wire_ne_of_gt (by have := ha_lt 0; omega))]
        exact hβ w hw
      refine ⟨⟨M - cur, by omega, hv0, hvR, hcl0⟩, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
      · dsimp only [TempPhaseProg.evalSign]
        rw [hs0 β hβ, hsR _ (hcl0 β hβ), zero_add]
      · dsimp only [TempPhaseProg.evalBits]
        let β₁ :=
          (msbClearStatic cur hcur (lhs 0) (rhs 0) (acc 0) (hlr 0) (hl_lt 0) (hr_lt 0)
          (ha_lt 0)).evalBits β
        have hβ₁_eq : β₁ = Function.update β (acc 0) (β (acc 0) + β (lhs 0) * β (rhs 0)) := hb0 β hβ
        obtain ⟨hclOut, hnonR, haccR⟩ := hR β₁ (hcl0 β hβ)
        refine ⟨hclOut, fun w hw ↦ ?_, fun j ↦ ?_⟩
        · rw [hnonR w (fun j ↦ hw j.succ), hβ₁_eq, Function.update_of_ne (hw 0)]
        · cases j using Fin.cases with
          | zero =>
              rw [hnonR (acc 0) (fun i h ↦ Fin.succ_ne_zero i (ha_inj h.symm)),
                hβ₁_eq, Function.update_self]
          | succ i =>
              rw [haccR i, hβ₁_eq,
                Function.update_of_ne (fun h ↦ Fin.succ_ne_zero i (ha_inj h)),
                Function.update_of_ne (hl_a i.succ 0),
                Function.update_of_ne (hr_a i.succ 0)]

/-- `3`-`TempAnd` (`12 T`) XOR of `mu_0*mu_1`, `mu_0*mu_2`, `mu_1*mu_2` into `retMuQuadW`. -/
def muQuad3Ret3_275 : TempPhaseProg 437 := xorAndPairsStatic 3 275 (by decide) lhsQuad3
    rhsQuad3 retMuQuadW lhsQuad3_ne_rhs lhsQuad3_lt275 rhsQuad3_lt275 retMuQuadW_lt275

theorem muQuad3Ret3_275_spec : ValidCleanRem 437 (437 - 275) muQuad3Ret3_275 ∧ (∀ β :
    BitAssignment 437, cleanRem 437 (437 - 275) β → muQuad3Ret3_275.evalSign β = 0) ∧ (∀ β :
    BitAssignment 437, cleanRem 437 (437 - 275) β → cleanRem 437 (437 - 275)
    (muQuad3Ret3_275.evalBits β) ∧ (∀ w : Wire 437, (∀ j : Fin 3, w ≠ retMuQuadW j) →
    muQuad3Ret3_275.evalBits β w = β w) ∧ (∀ j : Fin 3, muQuad3Ret3_275.evalBits β (retMuQuadW
    j) = β (retMuQuadW j) + β (lhsQuad3 j) * β (rhsQuad3 j))) := xorAndPairsStatic_add_spec 3
    275 (by decide) lhsQuad3 rhsQuad3 retMuQuadW lhsQuad3_ne_rhs (by decide) (by decide)
    retMuQuadW_inj lhsQuad3_lt275 rhsQuad3_lt275 retMuQuadW_lt275

/-- `5`-`TempAnd` 6-input NOR micro-program on `m[0..5]`. -/
def nor6Ops : List Slot3MicroEngineAux.MicroOp := [
  .notW 0, .notW 1, .notW 2, .notW 3, .notW 4, .notW 5,
  .andAlloc 0 1, .andAlloc 6 2, .andAlloc 7 3, .andAlloc 8 4, .andAlloc 9 5,
  .notW 0, .notW 1, .notW 2, .notW 3, .notW 4, .notW 5
]

theorem nor6_meta :
    Slot3MicroEngineAux.microValid 6 nor6Ops = true ∧
      Slot3MicroEngineAux.microAllocs nor6Ops = 5 ∧
      Slot3MicroEngineAux.microAnds nor6Ops = 5 := by decide

/-- Exhaustive 64-input truth-table check for `nor6Ops`. -/
def nor6Check (x : ℕ) : Bool :=
  let st := Slot3MicroEngineAux.evalMicroList 6 nor6Ops (Slot3MicroEngineAux.initBoolList 6 11 x)
  Slot3MicroEngineAux.allBelow 6 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 10 ==
      (!x.testBit 0 && !x.testBit 1 && !x.testBit 2 && !x.testBit 3 && !x.testBit 4 && !x.testBit
        5))

theorem nor6_eval_ok : Slot3MicroEngineAux.allBelow 64 nor6Check = true := by decide

/-- Low-6 magnitude wires `p57MW w 0..5` for axis `w`. -/
def zMagLow6W (w : Fin 3) (i : Fin 6) : Wire 437 := p57MW w i.castSucc

theorem zMagLow6W_inj (w : Fin 3) : Function.Injective (zMagLow6W w) := fun i j h ↦ by
  have hv := congrArg Fin.val h; dsimp [zMagLow6W, p57MW] at hv; exact Fin.ext (by omega)

/-- `5`-`TempAnd` prefix `TempCtx` for `dZMag1Rev5_275`. -/
def zMag1Rev5Ctx (w : Fin 3) : TempCtx 437 :=
  let kX := ctxCliffAlloc (.x (p57MW w ⟨6, by decide⟩))
  let kNor6 := Slot3MicroEngineAux.ctxMicro (zMagLow6W w) (zMagLow6W_inj w) 275 5 5
    (fun i ↦ by dsimp [zMagLow6W, p57MW]; omega) nor6Ops nor6_meta (by decide)
  kX.append kNor6

/-- `6`-`TempAnd` forward `TempCtx` computing `decide (|n_w| = 0)` on wire `280`. -/
def zMag1Ctx (w : Fin 3) : TempCtx 437 :=
  (zMag1Rev5Ctx w).append
    (ctxTempBit ⟨279, by decide⟩ (p57MW w ⟨6, by decide⟩) ⟨280, by decide⟩
      (wire_ne_of_gt (by dsimp [p57MW]; omega)) (by decide)
      (wire_ne_of_lt (by dsimp [p57MW]; omega)))

/-- `6`-`TempAnd` (`24 T`) single-axis zero-magnitude XOR into `retZeroMW w`. -/
def zMag1_275 (w : Fin 3) : TempPhaseProg 437 :=
  xorBlock1Prog (retZeroMW w) ⟨280, by decide⟩
    (by dsimp [retZeroMW]; omega) (by decide) (zMag1Ctx w)

/-- `20 T` (`5`-`TempAnd` + `0 T` `andUncompute`) single-axis asymmetric uncomputer for
  `zMag1_275`. -/
def dZMag1Rev5_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) (w : Fin 3) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb
    (DynamicCircuit.andUncompute v (rComb ⟨279, by decide⟩) (rComb (p57MW w ⟨6, by decide⟩))
      (rComb (retZeroMW w))
      (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [p57MW]; omega))))
    (zMag1Rev5Ctx w)

theorem zMag1Rev5Ctx_countTempAnd (w : Fin 3) : (zMag1Rev5Ctx w).countTempAnd = 5 := by
  have h1 := (Slot3MicroEngineAux.ctxMicro_scoped (zMagLow6W w) (zMagLow6W_inj w) 275 5 5
    (fun i ↦ by dsimp [zMagLow6W, p57MW]; omega) nor6Ops nor6_meta (by decide)).1
  dsimp only [zMag1Rev5Ctx]
  rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd, h1]
  rfl

theorem dZMag1Rev5_275_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) (w : Fin 3)
    :
    (dZMag1Rev5_275 v rComb w).count PrimitiveGate.T = 20 := by
  dsimp only [dZMag1Rev5_275]
  rw [p57ToDynWith_count_t, zMag1Rev5Ctx_countTempAnd w, DynamicCircuit.count_andUncompute_t]

theorem dZMag1Rev5_275_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n)
    (w : Fin 3) :
    (dZMag1Rev5_275 v rComb w).count PrimitiveGate.TOFF = 0 :=
  p57ToDynWith_count_toff v rComb _ (DynamicCircuit.count_andUncompute_toff v _ _ _ _) _

theorem dZMag1Rev5_275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) (w : Fin 3) :
    PreservesStoreConst (dZMag1Rev5_275 v rComb w) :=
  p57ToDynWith_preservesStore v rComb _ (PreservesStoreConst.andUncompute v _ _ _ _) _

theorem nor7_eq_decide_bitsVal_zero (f : Fin 7 → ZMod 2) :
    ((!decide (f 0 = 1) && !decide (f 1 = 1) && !decide (f 2 = 1) &&
      !decide (f 3 = 1) && !decide (f 4 = 1) && !decide (f 5 = 1)) &&
      decide ((f ⟨6, by decide⟩ + 1 : ZMod 2) = 1)) =
      decide (bitsVal f = 0) := by
  revert f; decide

theorem zMag1Rev5Ctx_disj_supp (w : Fin 3) {mutW : Wire 437 → Prop}
    (hmut : ∀ q, mutW q → q = retZeroMW w) :
    (zMag1Rev5Ctx w).DisjointFrom mutW ∧ (zMag1Rev5Ctx w).SupportsBelowCtx 280 := by
  obtain ⟨_, hPropsN, _, _⟩ := Slot3MicroEngineAux.ctxMicro_scoped (zMagLow6W w)
    (zMagLow6W_inj w) 275 5 5 (fun i ↦ by dsimp [zMagLow6W, p57MW]; omega)
    nor6Ops nor6_meta (by decide)
  obtain ⟨hdN, hsN⟩ := hPropsN (mutW := mutW)
    (fun i h ↦ by
      have hv := congrArg Fin.val (hmut _ h); dsimp [zMagLow6W, p57MW, retZeroMW] at hv; omega)
    (fun q hq h ↦ by have hv := congrArg Fin.val (hmut _ h); dsimp [retZeroMW] at hv; omega)
  have hdX : (ctxCliffAlloc (.x (p57MW w ⟨6, by decide⟩))).DisjointFrom mutW := by
    dsimp [ctxCliffAlloc, TempCtx.DisjointFrom, CliffDisjoint, CliffProg.inv]
    refine ⟨?_, trivial, ?_⟩ <;>
      (intro h; have hv := congrArg Fin.val (hmut _ h); dsimp [p57MW, retZeroMW] at hv; omega)
  have hsX : (ctxCliffAlloc (.x (p57MW w ⟨6, by decide⟩))).SupportsBelowCtx 275 := by
    dsimp [ctxCliffAlloc, TempCtx.SupportsBelowCtx, CliffProg.SupportsBelow, CliffProg.inv]
    exact ⟨by dsimp [p57MW]; omega, trivial, by dsimp [p57MW]; omega⟩
  exact ⟨TempCtx.disjointFrom_append hdX hdN, TempCtx.supportsBelowCtx_append (by decide) hsX hsN⟩

theorem zMag1_275_spec (w : Fin 3) : IsMutBlock 437 (437 - 275) (fun q ↦ q = retZeroMW w)
    (zMag1_275 w) ∧ (zMag1_275 w).countTempAnd = 6 ∧ (∀ β : BitAssignment 437, cleanRem 437
    (437 - 275) β → (zMag1_275 w).evalBits β (retZeroMW w) = β (retZeroMW w) + if bitsVal (fun
    b ↦ β (p57MW w b)) = 0 then 1 else 0) := by
  let mut1 : Wire 437 → Prop := fun q ↦ ∃ _ : Fin 1, q = retZeroMW w
  have hin : ∀ i, (zMagLow6W w i).val < 275 := fun i ↦ by dsimp [zMagLow6W, p57MW]; omega
  obtain ⟨_, _, hLiftN, hEvalN⟩ := Slot3MicroEngineAux.ctxMicro_scoped (zMagLow6W w)
    (zMagLow6W_inj w) 275 5 5 hin nor6Ops nor6_meta (by decide)
  obtain ⟨hdPre, hsPre⟩ := zMag1Rev5Ctx_disj_supp w (mutW := mut1) (fun _ ⟨_, h⟩ ↦ h)
  have hLiftX : Slot3MicroEngineAux.TempCtxLiftEx 275 275
      (ctxCliffAlloc (.x (p57MW w ⟨6, by decide⟩))) :=
    Slot3MicroEngineAux.TempCtxLiftEx.cliff 275 (by decide) (.x (p57MW w ⟨6, by decide⟩))
      (by dsimp [CliffProg.SupportsBelow, p57MW]; omega)
  have hdLast : (ctxTempBit ⟨279, by decide⟩ (p57MW w ⟨6, by decide⟩) ⟨280, by decide⟩
      (wire_ne_of_gt (by dsimp [p57MW]; omega)) (by decide)
      (wire_ne_of_lt (by dsimp [p57MW]; omega))).DisjointFrom mut1 := by
    dsimp [ctxTempBit, TempCtx.DisjointFrom]
    refine ⟨?_, ?_, ?_, trivial⟩ <;>
      (rintro ⟨_, h⟩; have hv := congrArg Fin.val h; dsimp [p57MW, retZeroMW] at hv; omega)
  have hsLast : (ctxTempBit ⟨279, by decide⟩ (p57MW w ⟨6, by decide⟩) ⟨280, by decide⟩
      (wire_ne_of_gt (by dsimp [p57MW]; omega)) (by decide)
      (wire_ne_of_lt (by dsimp [p57MW]; omega))).SupportsBelowCtx 281 := ⟨by decide, trivial⟩
  have hLiftLast : Slot3MicroEngineAux.TempCtxLiftEx 280 281
      (ctxTempBit ⟨279, by decide⟩ (p57MW w ⟨6, by decide⟩) ⟨280, by decide⟩
        (wire_ne_of_gt (by dsimp [p57MW]; omega)) (by decide)
        (wire_ne_of_lt (by dsimp [p57MW]; omega))) :=
    Slot3MicroEngineAux.TempCtxLiftEx.tempBit 280 (by decide)
      ⟨279, by decide⟩ (p57MW w ⟨6, by decide⟩)
      (wire_ne_of_gt (by dsimp [p57MW]; omega)) (by decide) (by dsimp [p57MW]; omega)
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock1_275_spec (curEnd := 281) (by decide) (by decide)
    (retZeroMW w) ⟨280, by decide⟩ (by dsimp [retZeroMW]; omega) (by decide) (zMag1Ctx w)
    (TempCtx.disjointFrom_append hdPre hdLast)
    (TempCtx.supportsBelowCtx_append (by decide) hsPre hsLast)
    (Slot3MicroEngineAux.TempCtxLiftEx.append
      (Slot3MicroEngineAux.TempCtxLiftEx.append hLiftX hLiftN) hLiftLast)
  have hCnt6 : (zMag1Ctx w).countTempAnd = 6 := by
    dsimp only [zMag1Ctx]
    rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd, zMag1Rev5Ctx_countTempAnd w]; rfl
  refine ⟨⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2⟩, hCnt.trans hCnt6, fun β hβ ↦ ?_⟩
  dsimp only [zMag1_275]; rw [hEv β hβ]
  refine congrArg (β (retZeroMW w) + ·) ?_
  dsimp only [zMag1Ctx, zMag1Rev5Ctx]
  rw [Slot3MicroEngineAux.TempCtx.append_fwdBits, Slot3MicroEngineAux.TempCtx.append_fwdBits]
  set β₁ := (ctxCliffAlloc (.x (p57MW w ⟨6, by decide⟩))).fwdBits β
  have hβ₁_eq : β₁ = Function.update β (p57MW w ⟨6, by decide⟩)
      (β (p57MW w ⟨6, by decide⟩) + 1) := rfl
  have hcl₁ : cleanRem 437 (437 - 275) β₁ := fun q hq ↦ by
    rw [hβ₁_eq, Function.update_of_ne (wire_ne_of_gt (by dsimp [p57MW]; omega))]; exact hβ q hq
  obtain ⟨hcl₂, hpres₂, hsOut₂⟩ := hEvalN β₁ hcl₁
  set β₂ := (Slot3MicroEngineAux.ctxMicro (zMagLow6W w) (zMagLow6W_inj w) 275 5 5 hin
    nor6Ops nor6_meta (by decide)).fwdBits β₁
  have hm_lt : bitsVal (fun i ↦ β₁ (zMagLow6W w i)) < 64 := bitsVal_lt_two_pow _
  have hchk := (Slot3MicroEngineAux.allBelow_iff 64 nor6Check).mp nor6_eval_ok _ hm_lt
  dsimp only [nor6Check] at hchk; simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  have ht : ∀ i : Fin 6, (bitsVal (fun j ↦ β₁ (zMagLow6W w j))).testBit i.val =
      decide (β (p57MW w i.castSucc) = 1) := fun i ↦ by
    have heq : β₁ (zMagLow6W w i) = β (p57MW w i.castSucc) := by
      rw [hβ₁_eq]; dsimp only [zMagLow6W]
      exact Function.update_of_ne (wire_ne_of_lt (by have := i.isLt; dsimp [p57MW]; omega)) _ _
    rw [Slot3MicroEngineAux.bitsVal_testBit_eq, heq]
  have hw279 : β₂ ⟨279, by decide⟩ = Slot3MicroEngineAux.boolToZMod2
      (!decide (β (p57MW w 0) = 1) && !decide (β (p57MW w 1) = 1) &&
        !decide (β (p57MW w 2) = 1) && !decide (β (p57MW w 3) = 1) &&
        !decide (β (p57MW w 4) = 1) && !decide (β (p57MW w 5) = 1)) := by
    rw [show (⟨279, by decide⟩ : Wire 437) = ⟨275 + (10 - 6), by decide⟩ from rfl,
      hsOut₂ 10 (by decide) (by decide), hchk.2,
      show (bitsVal (fun j ↦ β₁ (zMagLow6W w j))).testBit 0 = _ from ht 0,
      show (bitsVal (fun j ↦ β₁ (zMagLow6W w j))).testBit 1 = _ from ht 1,
      show (bitsVal (fun j ↦ β₁ (zMagLow6W w j))).testBit 2 = _ from ht 2,
      show (bitsVal (fun j ↦ β₁ (zMagLow6W w j))).testBit 3 = _ from ht 3,
      show (bitsVal (fun j ↦ β₁ (zMagLow6W w j))).testBit 4 = _ from ht 4,
      show (bitsVal (fun j ↦ β₁ (zMagLow6W w j))).testBit 5 = _ from ht 5]
    rfl
  have hm6_β₂ : β₂ (p57MW w ⟨6, by decide⟩) = β (p57MW w ⟨6, by decide⟩) + 1 := by
    rw [hpres₂ hchk.1 _ (by have := w.isLt; dsimp [p57MW]; omega), hβ₁_eq, Function.update_self]
  dsimp only [ctxTempBit, TempCtx.fwdBits]
  rw [Function.update_self, hcl₂ ⟨280, by decide⟩ (by decide), zero_add, hw279, hm6_β₂]
  have hmul : ∀ (b : Bool) (z : ZMod 2), Slot3MicroEngineAux.boolToZMod2 b * z =
      Slot3MicroEngineAux.boolToZMod2 (b && decide (z = 1)) := by
    intro b z; cases b <;> rcases bit_cases z with rfl | rfl <;> decide
  rw [hmul, nor7_eq_decide_bitsVal_zero (fun b ↦ β (p57MW w b))]
  by_cases h0 : bitsVal (fun b ↦ β (p57MW w b)) = 0
  · rw [ite_eq_left h0, decide_eq_true h0]; rfl
  · rw [ite_eq_right h0, decide_eq_false h0]; rfl

theorem dZMag1Rev5_275_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n) (w : Fin 3)
    (Inv : BitAssignment 437 → Prop) (hInv : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275)
    γ → Inv γ → γ (retZeroMW w) = if bitsVal (fun b ↦ γ (p57MW w b)) = 0 then 1 else 0) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (437 - 275) (by decide) Inv)
    (dZMag1Rev5_275 v rComb w) (((zMag1_275 w).onRegister rComb).toToffCircuit.eval) := by
  obtain ⟨hDisj, hSupp⟩ := zMag1Rev5Ctx_disj_supp w (fun _ h ↦ h)
  obtain ⟨hBZ, _, hEZ⟩ := zMag1_275_spec w
  refine dXorBlock1Peel_realizes v rComb 280 (by decide) (by decide)
    ⟨279, by decide⟩ (p57MW w ⟨6, by decide⟩) (retZeroMW w)
    (wire_ne_of_gt (by dsimp [p57MW]; omega))
    (wire_ne_of_gt (by dsimp [retZeroMW]; omega))
    (wire_ne_of_lt (by dsimp [p57MW, retZeroMW]; omega))
    (by decide) (by dsimp [p57MW]; omega) (by dsimp [retZeroMW]; omega)
    (zMag1Rev5Ctx w) hDisj hSupp
    (.cliff (Slot3MicroEngineAux.cnotVec 1 (fun _ ↦ ⟨280, by decide⟩) (fun _ ↦ retZeroMW w)
      (fun _ ↦ wire_ne_of_gt (by dsimp [retZeroMW]; omega))))
    (fun _ ↦ trivial) (fun _ ↦ rfl) (fun _ ↦ rfl) Inv (zMag1_275 w) rfl hBZ.1
    (fun γ hcl hi ↦ by rw [hEZ γ hcl, hInv γ hcl hi, CharTwo.add_self_eq_zero])

/-- `18`-`TempAnd` (`72 T`) 3-axis zero-magnitude XOR writing `retZeroMW 0..2` (`254..256`). -/
def zMag3Ret18_275 : TempPhaseProg 437 :=
  .seq (zMag1_275 0) (.seq (zMag1_275 1) (zMag1_275 2))

theorem zMag3Ret18_275_countTempAnd : zMag3Ret18_275.countTempAnd = 18 := by
  dsimp only [zMag3Ret18_275, TempPhaseProg.countTempAnd]
  rw [(zMag1_275_spec 0).2.1, (zMag1_275_spec 1).2.1, (zMag1_275_spec 2).2.1]

theorem zMag3Ret18_275_spec : IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w, q = retZeroMW w)
    zMag3Ret18_275 ∧ zMag3Ret18_275.countTempAnd = 18 ∧ (∀ β : BitAssignment 437, cleanRem 437
    (437 - 275) β → ∀ w : Fin 3, zMag3Ret18_275.evalBits β (retZeroMW w) = β (retZeroMW w) +
    if bitsVal (fun b ↦ β (p57MW w b)) = 0 then 1 else 0) := by
  have hLift : ∀ w : Fin 3, IsMutBlock 437 (437 - 275) (fun q ↦ ∃ u, q = retZeroMW u)
      (zMag1_275 w) := fun w ↦ by
    obtain ⟨hB, _, _⟩ := zMag1_275_spec w
    exact ⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦ hB.2.2.2 β hβ q (fun h ↦ hq ⟨w, h⟩)⟩
  obtain ⟨hB0, _, hE0⟩ := zMag1_275_spec 0
  obtain ⟨hB1, _, hE1⟩ := zMag1_275_spec 1
  obtain ⟨hB2, _, hE2⟩ := zMag1_275_spec 2
  refine ⟨IsMutBlock.seq (by decide) (hLift 0) (IsMutBlock.seq (by decide) (hLift 1) (hLift 2)),
    zMag3Ret18_275_countTempAnd, fun β hβ ↦ ?_⟩
  have hcl₁ := hB0.2.2.1 β hβ
  have hcl₂ := hB1.2.2.1 ((zMag1_275 0).evalBits β) hcl₁
  refine fin3_cases ?_ ?_ ?_
  · dsimp only [zMag3Ret18_275, TempPhaseProg.evalBits]
    rw [hB2.2.2.2 _ hcl₂ (retZeroMW 0) (by decide),
      hB1.2.2.2 _ hcl₁ (retZeroMW 0) (by decide), hE0 β hβ]
  · dsimp only [zMag3Ret18_275, TempPhaseProg.evalBits]
    rw [hB2.2.2.2 _ hcl₂ (retZeroMW 1) (by decide), hE1 _ hcl₁,
      hB0.2.2.2 β hβ (retZeroMW 1) (by decide)]
    simp only [fun b ↦
      hB0.2.2.2 β hβ (p57MW 1 b) (wire_ne_of_lt (by dsimp [p57MW, retZeroMW]; omega))]
  · dsimp only [zMag3Ret18_275, TempPhaseProg.evalBits]
    rw [hE2 _ hcl₂, hB1.2.2.2 _ hcl₁ (retZeroMW 2) (by decide),
      hB0.2.2.2 β hβ (retZeroMW 2) (by decide)]
    simp only [fun b ↦ (hB1.2.2.2 _ hcl₁ (p57MW 2 b)
      (wire_ne_of_lt (by dsimp [p57MW, retZeroMW]; omega))).trans
      (hB0.2.2.2 β hβ (p57MW 2 b) (wire_ne_of_lt (by dsimp [p57MW, retZeroMW]; omega)))]

/-- `60 T` (`15`-`TempAnd`) 3-axis asymmetric dynamic uncomputer for `zMag3Ret18_275`. -/
def dZMag3Rev15_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) : DynamicCircuit
    Var n := .seq (dZMag1Rev5_275 v rComb 0)
    (.seq (dZMag1Rev5_275 v rComb 1) (dZMag1Rev5_275 v rComb 2))

theorem dZMag3Rev15_275_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dZMag3Rev15_275 v rComb).count PrimitiveGate.T = 60 := by
  dsimp only [dZMag3Rev15_275]
  simp only [DynamicCircuit.count, dZMag1Rev5_275_count_t]

theorem dZMag3Rev15_275_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dZMag3Rev15_275 v rComb).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dZMag3Rev15_275]
  simp only [DynamicCircuit.count, dZMag1Rev5_275_count_toff, add_zero]

theorem dZMag3Rev15_275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) : PreservesStoreConst (dZMag3Rev15_275 v rComb) :=
    PreservesStoreConst.seq (dZMag1Rev5_275_preservesStore v rComb 0) (PreservesStoreConst.seq
    (dZMag1Rev5_275_preservesStore v rComb 1) (dZMag1Rev5_275_preservesStore v rComb 2))

/-- Single-axis zero-magnitude invariant `retZeroMW w = decide (|n_w| = 0)`. -/
def InvZMag1 (w : Fin 3) (γ : BitAssignment 437) : Prop :=
  γ (retZeroMW w) = if bitsVal (fun b ↦ γ (p57MW w b)) = 0 then 1 else 0

/-- Three-axis zero-magnitude invariant on `retZeroMW 0..2`. -/
def InvZMag3 (γ : BitAssignment 437) : Prop := ∀ w : Fin 3, InvZMag1 w γ

theorem InvZMag3_congr {γ₁ γ₂ : BitAssignment 437}
    (hz : ∀ w : Fin 3, γ₁ (retZeroMW w) = γ₂ (retZeroMW w))
    (hm : ∀ w b, γ₁ (p57MW w b) = γ₂ (p57MW w b)) : InvZMag3 γ₁ ↔ InvZMag3 γ₂ := by
  refine forall_congr' fun w ↦ ?_
  dsimp only [InvZMag1]
  have hm_fn : (fun b ↦ γ₁ (p57MW w b)) = fun b ↦ γ₂ (p57MW w b) := funext (hm w)
  rw [hz w, hm_fn]

theorem dZMag3Rev15_275_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n) (Inv : BitAssignment 437 → Prop)
    (hInv : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ → Inv γ → InvZMag3 γ) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (437 - 275) (by decide) Inv)
    (dZMag3Rev15_275 v rComb) (((zMag3Ret18_275.onRegister rComb).toToffCircuit).eval) := by
  obtain ⟨hB0, _, _⟩ := zMag1_275_spec 0
  obtain ⟨hB1, _, _⟩ := zMag1_275_spec 1
  have hPresInv : ∀ (u w : Fin 3) (γ : BitAssignment 437), u ≠ w →
      cleanRem 437 (437 - 275) γ → InvZMag1 w γ → InvZMag1 w ((zMag1_275 u).evalBits γ) :=
    fun u w γ huw hcl hi ↦ by
      have hnon := (zMag1_275_spec u).1.2.2.2 γ hcl
      unfold InvZMag1
      rw [hnon (retZeroMW w) (fun h ↦ huw (Fin.ext (by
          have hv := congrArg Fin.val h; dsimp [retZeroMW] at hv; omega)).symm),
        show (fun b ↦ (zMag1_275 u).evalBits γ (p57MW w b)) = fun b ↦ γ (p57MW w b) from
          funext fun b ↦ hnon _ (wire_ne_of_lt (by dsimp [p57MW, retZeroMW]; omega))]
      exact hi
  let Inv1 : BitAssignment 437 → Prop := fun γ₁ ↦ InvZMag1 1 γ₁ ∧ InvZMag1 2 γ₁
  let Inv2 : BitAssignment 437 → Prop := InvZMag1 2
  have h12 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv1)
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv2)
    (dZMag1Rev5_275_realizes v rComb 1 Inv1 (fun _ _ hi ↦ hi.1))
    (dZMag1Rev5_275_realizes v rComb 2 Inv2 (fun _ _ hi ↦ hi))
    (p57SeqClean_prog_inv rComb (zMag1_275 1) (by decide) (by decide) fun γ₁ hcl₁ ⟨_, hi2⟩ ↦
      ⟨hB1.2.2.1 γ₁ hcl₁, hPresInv 1 2 γ₁ (by decide) hcl₁ hi2⟩)
  rw [← seq_onReg_eval rComb (zMag1_275 1) (zMag1_275 2)] at h12
  have h012 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv)
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv1)
    (dZMag1Rev5_275_realizes v rComb 0 Inv (fun γ hcr hi ↦ hInv γ hcr hi 0)) h12
    (p57SeqClean_prog_inv rComb (zMag1_275 0) (by decide) (by decide) fun γ₀ hcl₀ hi₀ ↦
      ⟨hB0.2.2.1 γ₀ hcl₀, hPresInv 0 1 γ₀ (by decide) hcl₀ (hInv γ₀ hcl₀ hi₀ 1),
        hPresInv 0 2 γ₀ (by decide) hcl₀ (hInv γ₀ hcl₀ hi₀ 2)⟩)
  rwa [← seq_onReg_eval rComb (zMag1_275 0) (.seq (zMag1_275 1) (zMag1_275 2))] at h012

/-- Clifford X-flip on `retZeroMW 0..2` to form `1 + retZeroMW w = decide (|n_w| ≠ 0)`. -/
def xRetZero3Cliff : CliffProg 437 :=
  .seq (.x (retZeroMW 0)) (.seq (.x (retZeroMW 1)) (.x (retZeroMW 2)))

/-- `3`-`TempAnd` (`12 T`) conditional sign-flip on `p57S3W 0..2` reading `retZeroMW` (`-60 T` vs
  `18` `TempAnd`s). -/
def s3FlipFromZ3_275 : TempPhaseProg 437 :=
  withCliffAlloc xRetZero3Cliff
    (xorAndPairsStatic 3 275 (by decide)
      (fun _ ↦ accWAux) retZeroMW p57S3W
      (fun w ↦ wire_ne_of_lt (by dsimp [accWAux, retZeroMW]; omega))
      (fun _ ↦ by decide)
      (fun w ↦ by dsimp [retZeroMW]; omega)
      (fun w ↦ by dsimp [p57S3W]; omega))

theorem s3FlipFromZ3_275_countTempAnd : s3FlipFromZ3_275.countTempAnd = 3 := by
  dsimp only [s3FlipFromZ3_275]
  rw [withCliffAlloc_countTempAnd, xorAndPairsStatic_countTempAnd]

theorem s3FlipFromZ3_275_spec : IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w, q = p57S3W w)
    s3FlipFromZ3_275 ∧ s3FlipFromZ3_275.countTempAnd = 3 ∧ (∀ β : BitAssignment 437, cleanRem
    437 (437 - 275) β → ∀ w : Fin 3, s3FlipFromZ3_275.evalBits β (p57S3W w) = β (p57S3W w) + β
    accWAux * (1 + β (retZeroMW w))) := by
  let pIn := xorAndPairsStatic 3 275 (by decide)
    (fun _ ↦ accWAux) retZeroMW p57S3W
    (fun w ↦ wire_ne_of_lt (by dsimp [accWAux, retZeroMW]; omega))
    (fun _ ↦ by decide)
    (fun w ↦ by dsimp [retZeroMW]; omega)
    (fun w ↦ by dsimp [p57S3W]; omega)
  have hcX_supp : xRetZero3Cliff.SupportsBelow 275 := by
    dsimp [xRetZero3Cliff, CliffProg.SupportsBelow]; decide
  obtain ⟨hvIn, hsIn, hEvIn⟩ := xorAndPairsStatic_add_spec 3 275 (by decide)
    (fun _ ↦ accWAux) retZeroMW p57S3W
    (fun w ↦ wire_ne_of_lt (by dsimp [accWAux, retZeroMW]; omega))
    (fun _ w ↦ wire_ne_of_gt (by dsimp [accWAux, p57S3W]; omega))
    (fun i w ↦ wire_ne_of_gt (by dsimp [retZeroMW, p57S3W]; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp [p57S3W] at hv; exact Fin.ext (by omega))
    (fun _ ↦ by decide)
    (fun w ↦ by dsimp [retZeroMW]; omega)
    (fun w ↦ by dsimp [p57S3W]; omega)
  obtain ⟨hvWrap, hevWrap⟩ := Prod57BoothHoist.withCliffAlloc_valid_and_eval
    (M := 437) (rem := 437 - 275) (remIn := 437 - 275)
    (by decide) le_rfl xRetZero3Cliff hcX_supp pIn hvIn
  have hDisjS3 : CliffDisjoint (fun q ↦ ∃ w, q = p57S3W w) xRetZero3Cliff := by
    dsimp [xRetZero3Cliff, CliffDisjoint]
    refine ⟨?_, ?_, ?_⟩ <;> (rintro ⟨u, hu⟩; revert u hu; decide)
  have hDisjInv := CliffDisjoint.inv hDisjS3
  have hNonMut : ∀ β, cleanRem 437 (437 - 275) β → ∀ q : Wire 437, ¬(∃ w, q = p57S3W w) →
      s3FlipFromZ3_275.evalBits β q = β q := by
    intro β hβ q hnq
    obtain ⟨hcγ, _, hev1⟩ := hevWrap β hβ
    have hδ_non : ∀ u : Wire 437,
      ¬(∃ w, u = p57S3W w) → pIn.evalBits (xRetZero3Cliff.eval β) u = (xRetZero3Cliff.eval β) u :=
      fun u hnu ↦ (hEvIn (xRetZero3Cliff.eval β) hcγ).2.1 u (fun w h ↦ hnu ⟨w, h⟩)
    dsimp only [s3FlipFromZ3_275]
    rw [hev1, hDisjInv.eval_congr_nonMut hδ_non q hnq, Prod57BoothHoist.cliffInv_comp_eval]
  have hClOut : ∀ β,
    cleanRem 437 (437 - 275) β → cleanRem 437 (437 - 275) (s3FlipFromZ3_275.evalBits β) := by
    intro β hβ q hq
    rw [hNonMut β hβ q (fun ⟨w, hw⟩ ↦ by subst hw; dsimp [p57S3W] at hq; omega)]
    exact hβ q hq
  refine ⟨⟨hvWrap, fun β hβ ↦ by
    obtain ⟨hcγ, hs1, _⟩ := hevWrap β hβ
    dsimp only [s3FlipFromZ3_275]
    rw [hs1, hsIn (xRetZero3Cliff.eval β) hcγ],
    hClOut, hNonMut⟩, s3FlipFromZ3_275_countTempAnd, fun β hβ w ↦ ?_⟩
  obtain ⟨hcγ, _, hev1⟩ := hevWrap β hβ
  dsimp only [s3FlipFromZ3_275]
  rw [hev1, hDisjInv.eval_mut (pIn.evalBits (xRetZero3Cliff.eval β)) ⟨w, rfl⟩,
    (hEvIn (xRetZero3Cliff.eval β) hcγ).2.2 w, hDisjS3.eval_mut β ⟨w, rfl⟩]
  have hcX_ev : ∀ u : Fin 3, xRetZero3Cliff.eval β (retZeroMW u) = 1 + β (retZeroMW u) := by
    have hev : xRetZero3Cliff.eval β =
        Function.update (Function.update (Function.update β (retZeroMW 0) (β (retZeroMW 0) + 1))
          (retZeroMW 1) (β (retZeroMW 1) + 1)) (retZeroMW 2) (β (retZeroMW 2) + 1) := by
      dsimp only [xRetZero3Cliff, CliffProg.eval]
      simp only [Function.update_of_ne (by decide : retZeroMW 1 ≠ retZeroMW 0),
        Function.update_of_ne (by decide : retZeroMW 2 ≠ retZeroMW 1),
        Function.update_of_ne (by decide : retZeroMW 2 ≠ retZeroMW 0)]
    rw [hev]
    refine fin3_cases ?_ ?_ ?_
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self, add_comm]
    · rw [Function.update_of_ne (by decide), Function.update_self, add_comm]
    · rw [Function.update_self, add_comm]
  have hcX_acc : xRetZero3Cliff.eval β accWAux = β accWAux := by
    dsimp only [xRetZero3Cliff, CliffProg.eval]
    simp only [Function.update_of_ne (by decide : accWAux ≠ retZeroMW 2),
      Function.update_of_ne (by decide : accWAux ≠ retZeroMW 1),
      Function.update_of_ne (by decide : accWAux ≠ retZeroMW 0)]
  rw [hcX_acc, hcX_ev w]

theorem s3FlipFromZ3_275_eq_orig (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β)
    (hZ : InvZMag3 β) : s3FlipFromZ3_275.evalBits β = s3Flip275.evalBits β := by
  obtain ⟨hB1, _, hE1⟩ := s3FlipFromZ3_275_spec
  obtain ⟨hB2, _, hE2⟩ := s3Flip275_spec
  funext q
  by_cases hq : ∃ w, q = p57S3W w
  · obtain ⟨w, rfl⟩ := hq
    rw [hE1 β hβ w, hE2 β hβ w, hZ w]
    by_cases hm0 : bitsVal (fun j ↦ β (p57MW w j)) = 0
    · simp only [hm0, ↓reduceIte]
      have h11 : (1 + 1 : ZMod 2) = 0 := rfl
      rw [h11]
    · simp only [hm0, ↓reduceIte, add_zero]
  · exact (hB1.2.2.2 β hβ q hq).trans (hB2.2.2.2 β hβ q hq).symm

/-- `3`-`TempAnd` micro-program computing `!(s3[w] && retZeroMW[w])` across all three axes. -/
def vsSignFromZ6Ops : List Slot3MicroEngineAux.MicroOp := [
  .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .andAlloc 0 3, .notW 12,
  .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .andAlloc 1 4, .notW 19,
  .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .andAlloc 2 5, .notW 26
]

theorem vsSignFromZ6_meta :
    Slot3MicroEngineAux.microValid 6 vsSignFromZ6Ops = true ∧
      Slot3MicroEngineAux.microAllocs vsSignFromZ6Ops = 21 ∧
      Slot3MicroEngineAux.microAnds vsSignFromZ6Ops = 3 := by decide

/-- Exhaustive 64-input truth-table check for `vsSignFromZ6Ops`. -/
def vsSignFromZ6Check (x : ℕ) : Bool :=
  let st :=
    Slot3MicroEngineAux.evalMicroList 6 vsSignFromZ6Ops (Slot3MicroEngineAux.initBoolList 6 27 x)
  Slot3MicroEngineAux.allBelow 6 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 12 == !(x.testBit 0 && x.testBit 3)) &&
    (Slot3MicroEngineAux.getBoolAt st 19 == !(x.testBit 1 && x.testBit 4)) &&
    (Slot3MicroEngineAux.getBoolAt st 26 == !(x.testBit 2 && x.testBit 5))

theorem vsSignFromZ6_eval_ok : Slot3MicroEngineAux.allBelow 64 vsSignFromZ6Check = true := by decide

/-- Six-wire input vector `(s3[0..2], retZeroMW[0..2])` for `vsSignFromZ6Ops`. -/
def vsSignIn6W : Fin 6 → Wire 437 :=
  ![p57S3W 0, p57S3W 1, p57S3W 2, retZeroMW 0, retZeroMW 1, retZeroMW 2]

theorem vsSignIn6W_inj : Function.Injective vsSignIn6W := fun i j h ↦ by
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)

/-- `28`-`TempAnd` forward `TempCtx` computing `validStatic` from `retZeroMW` (`-18` `TempAnd`s
  vs `46`). -/
def validStaticFromZ28_275Ctx : TempCtx 437 :=
  let k3 := ctxVsOr3Loop216 7 le_rfl
  let k5 := Slot3MicroEngineAux.ctxMicro vsSignIn6W vsSignIn6W_inj 303 21 3
    (fun i ↦ by fin_cases i <;> decide)
    vsSignFromZ6Ops vsSignFromZ6_meta (by decide)
  let k4 := Micro216.ctxMicro vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7
    (fun k ↦ by
      dsimp only [vsTop7MaxMagIn11W]
      split_ifs <;> (dsimp [muW, top7W, vsOr3_216W]; omega))
    top7MaxMag11Ops top7MaxMag11_meta (by decide)
  let k6 := Slot3MicroEngineAux.ctxMicro vsAnd5In216W vsAnd5In216W_inj 331 4 4
    (fun i ↦ by fin_cases i <;> decide)
    Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta (by decide)
  k3.append (k5.append (k4.append k6))

/-- `28`-`TempAnd` (`112 T`) forward `validStatic` XOR reading `retZeroMW` (`-72 T` vs
  `validStatic216_fast46_275`). -/
def validStaticFromZ28_275 : TempPhaseProg 437 :=
  xorBlock1Prog216 validStaticW ⟨334, by decide⟩ (by decide) (by decide) validStaticFromZ28_275Ctx

/-- `27`-`TempAnd` prefix `TempCtx` for `dValidStaticFromZRev27_275`. -/
def validStaticFromZRev27Ctx : TempCtx 437 :=
  let k3 := ctxVsOr3Loop216 7 le_rfl
  let k5 := Slot3MicroEngineAux.ctxMicro vsSignIn6W vsSignIn6W_inj 303 21 3
    (fun i ↦ by fin_cases i <;> decide)
    vsSignFromZ6Ops vsSignFromZ6_meta (by decide)
  let k4 := Micro216.ctxMicro vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7
    (fun k ↦ by
      dsimp only [vsTop7MaxMagIn11W]
      split_ifs <;> (dsimp [muW, top7W, vsOr3_216W]; omega))
    top7MaxMag11Ops top7MaxMag11_meta (by decide)
  k3.append (k5.append (k4.append vsK6FastPre3Ctx))

/-- `108 T` (`27`-`TempAnd` + `0 T` `andUncompute`) asymmetric uncomputer for
  `validStaticFromZ28_275`. -/
def dValidStaticFromZRev27_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb
    (DynamicCircuit.andUncompute v (rComb ⟨333,
      by decide⟩) (rComb (vsAnd5In216W 4)) (rComb validStaticW)
      (rComb.wires.injective.ne (by decide)))
    validStaticFromZRev27Ctx

theorem validStaticFromZRev27Ctx_countTempAnd : validStaticFromZRev27Ctx.countTempAnd = 27 := by
  have h3 := (ctxVsOr3Loop216_scoped 7 le_rfl).1
  have h5 := (Slot3MicroEngineAux.ctxMicro_scoped vsSignIn6W vsSignIn6W_inj 303 21 3
    (fun i ↦ by fin_cases i <;> decide)
    vsSignFromZ6Ops vsSignFromZ6_meta (by decide)).1
  have h4 := (Micro216.ctxMicro_scoped vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7
    (fun k ↦ by
      dsimp only [vsTop7MaxMagIn11W]
      split_ifs <;> (dsimp [muW, top7W, vsOr3_216W]; omega))
    top7MaxMag11Ops top7MaxMag11_meta (by decide)).1
  dsimp only [validStaticFromZRev27Ctx]
  repeat rw [Micro216.TempCtx.append_countTempAnd]
  rw [h3, h5, h4]
  rfl

theorem dValidStaticFromZRev27_275_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n)
    :
    (dValidStaticFromZRev27_275 v rComb).count PrimitiveGate.T = 108 := by
  dsimp only [dValidStaticFromZRev27_275]
  rw [p57ToDynWith_count_t, validStaticFromZRev27Ctx_countTempAnd,
    DynamicCircuit.count_andUncompute_t]

theorem dValidStaticFromZRev27_275_count_toff {Var : Type} {n : ℕ} (v : Var)
    (rComb : QRegister 437 n) :
    (dValidStaticFromZRev27_275 v rComb).count PrimitiveGate.TOFF = 0 :=
  p57ToDynWith_count_toff v rComb _ (DynamicCircuit.count_andUncompute_toff v _ _ _ _) _

theorem dValidStaticFromZRev27_275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) :
    PreservesStoreConst (dValidStaticFromZRev27_275 v rComb) :=
  p57ToDynWith_preservesStore v rComb _ (PreservesStoreConst.andUncompute v _ _ _ _) _

theorem vsFromZ_prefix3_disj_supp {mutW : Wire 437 → Prop}
    (hmut : ∀ q, mutW q → q = validStaticW) :
    (ctxVsOr3Loop216 7 le_rfl).DisjointFrom mutW ∧
    (ctxVsOr3Loop216 7 le_rfl).SupportsBelowCtx 303 ∧
    (Slot3MicroEngineAux.ctxMicro vsSignIn6W vsSignIn6W_inj 303 21 3
      (fun i ↦ by fin_cases i <;> decide)
      vsSignFromZ6Ops vsSignFromZ6_meta (by decide)).DisjointFrom mutW ∧
    (Slot3MicroEngineAux.ctxMicro vsSignIn6W vsSignIn6W_inj 303 21 3
      (fun i ↦ by fin_cases i <;> decide)
      vsSignFromZ6Ops vsSignFromZ6_meta (by decide)).SupportsBelowCtx 324 ∧
    (Micro216.ctxMicro vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7
      (fun k ↦ by dsimp only [vsTop7MaxMagIn11W]; split_ifs <;>
        (dsimp [muW, top7W, vsOr3_216W]; omega))
      top7MaxMag11Ops top7MaxMag11_meta (by decide)).DisjointFrom mutW ∧
    (Micro216.ctxMicro vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7
      (fun k ↦ by dsimp only [vsTop7MaxMagIn11W]; split_ifs <;>
        (dsimp [muW, top7W, vsOr3_216W]; omega))
      top7MaxMag11Ops top7MaxMag11_meta (by decide)).SupportsBelowCtx 331 := by
  have hnot_ge259 : ∀ q : Wire 437, 259 ≤ q.val → ¬ mutW q := fun q hq hm ↦ by
    have hv := congrArg Fin.val (hmut q hm); dsimp [validStaticW] at hv; omega
  obtain ⟨_, hP3, _, _⟩ := ctxVsOr3Loop216_scoped 7 le_rfl
  obtain ⟨_, hP5, _, _⟩ := Slot3MicroEngineAux.ctxMicro_scoped vsSignIn6W vsSignIn6W_inj 303 21 3
    (fun i ↦ by fin_cases i <;> decide) vsSignFromZ6Ops vsSignFromZ6_meta (by decide)
  obtain ⟨_, hP4, _, _⟩ := Micro216.ctxMicro_scoped vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj
    324 7 7 (fun k ↦ by dsimp only [vsTop7MaxMagIn11W]; split_ifs <;>
      (dsimp [muW, top7W, vsOr3_216W]; omega))
    top7MaxMag11Ops top7MaxMag11_meta (by decide)
  obtain ⟨hd3, hs3⟩ := hP3 (mutW := mutW)
    (fun w b hm ↦ by
      have hv := congrArg Fin.val (hmut _ hm); dsimp [p57MW, validStaticW] at hv; omega)
    (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hd5, hs5⟩ := hP5 (mutW := mutW)
    (fun i hm ↦ by have h := hmut _ hm; fin_cases i <;> (exfalso; revert h; decide))
    (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hd4, hs4⟩ := hP4 (mutW := mutW)
    (fun k hm ↦ by
      have hv := congrArg Fin.val (hmut _ hm); dsimp only [vsTop7MaxMagIn11W] at hv
      split_ifs at hv <;> (dsimp [muW, top7W, vsOr3_216W, validStaticW] at hv; omega))
    (fun q hq ↦ hnot_ge259 q (by omega))
  exact ⟨hd3, Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs3, hd5, hs5, hd4, hs4⟩

theorem validStaticFromZ28_275_spec : IsMutBlock 437 (437 - 275) vsMutW validStaticFromZ28_275
    ∧ validStaticFromZ28_275.countTempAnd = 28 ∧ (∀ β, cleanRem 437 (437 - 275) β → InvZMag3 β
    → validStaticFromZ28_275.evalBits β = validStatic216_fast46_275.evalBits β) := by
  let mut1 : Wire 437 → Prop := fun q ↦ ∃ _ : Fin 1, q = validStaticW
  have hnot_ge259 : ∀ q : Wire 437, 259 ≤ q.val → ¬ mut1 q := by
    rintro q hq ⟨_, rfl⟩; dsimp [validStaticW] at hq; omega
  have hin5 : ∀ i, (vsSignIn6W i).val < 303 := fun i ↦ by fin_cases i <;> decide
  have hin4 : ∀ k, (vsTop7MaxMagIn11W k).val < 324 := fun k ↦ by
    dsimp only [vsTop7MaxMagIn11W]; split_ifs <;> (dsimp [muW, top7W, vsOr3_216W]; omega)
  have hin6 : ∀ i, (vsAnd5In216W i).val < 331 := fun i ↦ by fin_cases i <;> decide
  obtain ⟨hCnt3, _, hL30, hEval3⟩ := ctxVsOr3Loop216_scoped 7 le_rfl
  obtain ⟨hCnt5, _, hL5, hEval5⟩ := Slot3MicroEngineAux.ctxMicro_scoped vsSignIn6W
    vsSignIn6W_inj 303 21 3 hin5 vsSignFromZ6Ops vsSignFromZ6_meta (by decide)
  obtain ⟨_, hP5Orig, hL5Orig, hEval5Orig⟩ := ctxVsSignLoop216_scoped 3 le_rfl
  obtain ⟨hCnt4, _, hL4, hEval4⟩ := Micro216.ctxMicro_scoped vsTop7MaxMagIn11W
    vsTop7MaxMagIn11W_inj 324 7 7 hin4 top7MaxMag11Ops top7MaxMag11_meta (by decide)
  obtain ⟨hCnt6, hP6, hL6, hEval6⟩ := Slot3MicroEngineAux.ctxMicro_scoped vsAnd5In216W
    vsAnd5In216W_inj 331 4 4 hin6 Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta
      (by decide)
  have hL3 : Micro216.TempCtxLiftEx 275 303 (ctxVsOr3Loop216 7 le_rfl) :=
    Micro216.TempCtxLiftEx.mono hL30 (by decide) (by decide) (by decide)
  obtain ⟨hd3, hs3, hd5, hs5, hd4, hs4⟩ :=
    vsFromZ_prefix3_disj_supp (mutW := mut1) (fun _ ⟨_, h⟩ ↦ h)
  obtain ⟨hd6, hs6⟩ := hP6
    (fun i ⟨_, h⟩ ↦ by fin_cases i <;> (exfalso; revert h; decide))
    (fun q hq ↦ hnot_ge259 q (by omega))
  have hXor1 (ctx k5 : TempCtx 437)
      (hctx : ctx = (ctxVsOr3Loop216 7 le_rfl).append (k5.append ((Micro216.ctxMicro
        vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7 hin4 top7MaxMag11Ops top7MaxMag11_meta
        (by decide)).append (Slot3MicroEngineAux.ctxMicro vsAnd5In216W vsAnd5In216W_inj 331 4 4 hin6
          Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta (by decide)))))
      (hd : k5.DisjointFrom mut1) (hs : k5.SupportsBelowCtx 324)
      (hL : Micro216.TempCtxLiftEx 303 324 k5) :=
    xorBlock1_275_216_spec (by decide) (by decide) validStaticW ⟨334, by decide⟩
      (by decide) (by decide) ctx
      (hctx ▸ TempCtx.disjointFrom_append hd3
        (TempCtx.disjointFrom_append hd (TempCtx.disjointFrom_append hd4 hd6)))
      (hctx ▸ TempCtx.supportsBelowCtx_append le_rfl
        (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs3)
        (TempCtx.supportsBelowCtx_append le_rfl
          (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs)
          (TempCtx.supportsBelowCtx_append le_rfl
            (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs4) hs6)))
      (hctx ▸ Micro216.TempCtxLiftEx.append hL3
        (Micro216.TempCtxLiftEx.append hL (Micro216.TempCtxLiftEx.append hL4 hL6)))
  obtain ⟨hBlk, hCnt, hEv⟩ := hXor1 validStaticFromZ28_275Ctx _ rfl hd5 hs5 hL5
  have hCnt28 : validStaticFromZ28_275Ctx.countTempAnd = 28 := by
    dsimp only [validStaticFromZ28_275Ctx]
    repeat rw [Micro216.TempCtx.append_countTempAnd]
    rw [hCnt3, hCnt5, hCnt4, hCnt6]
  obtain ⟨hd5Orig, hs5Orig⟩ := hP5Orig
    (fun w ⟨_, h⟩ ↦ by
      have hv := congrArg Fin.val h
      dsimp [p57S3W, validStaticW] at hv
      omega)
    (fun w b ⟨_, h⟩ ↦ by
      have hv := congrArg Fin.val h
      dsimp [p57MW, validStaticW] at hv
      omega)
    (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hBlkOrig, _, hEvOrig⟩ := hXor1 validStatic216_fast46_275Ctx _ rfl hd5Orig hs5Orig hL5Orig
  refine ⟨hBlk, hCnt.trans hCnt28, fun β hβ hZ ↦ funext fun q ↦ ?_⟩
  by_cases hq : vsMutW q
  · have hq' : q = validStaticW := hq; subst hq'
    dsimp only [validStaticFromZ28_275]
    rw [hEv β hβ, show validStatic216_fast46_275.evalBits β validStaticW =
      β validStaticW + validStatic216_fast46_275Ctx.fwdBits β ⟨334, by decide⟩ from
      hEvOrig β hβ]
    refine congrArg (β validStaticW + ·) ?_
    obtain ⟨hcl30, hpres3, _⟩ := hEval3 β (cleanRem_anti (by decide) hβ)
    let β₃ := (ctxVsOr3Loop216 7 le_rfl).fwdBits β
    have hcl3 : cleanRem 437 (437 - 303) β₃ := cleanRem_anti (by decide) hcl30
    obtain ⟨hcl5, hpres5, hsOut5⟩ := hEval5 β₃ hcl3
    obtain ⟨hcl5Orig, hpres5Orig, hout5Orig⟩ := hEval5Orig β₃ hcl3
    let β₅ := (Slot3MicroEngineAux.ctxMicro vsSignIn6W vsSignIn6W_inj 303 21 3 hin5
      vsSignFromZ6Ops vsSignFromZ6_meta (by decide)).fwdBits β₃
    let β₅Orig := (ctxVsSignLoop216 3 le_rfl).fwdBits β₃
    have hm5_lt : bitsVal (fun i ↦ β₃ (vsSignIn6W i)) < 64 := bitsVal_lt_two_pow _
    have hchk5 := (Slot3MicroEngineAux.allBelow_iff 64 vsSignFromZ6Check).mp
      vsSignFromZ6_eval_ok _ hm5_lt
    dsimp only [vsSignFromZ6Check] at hchk5; simp only [Bool.and_eq_true, beq_iff_eq] at hchk5
    have hSignEq : ∀ w : Fin 3, β₅ (vsSignOut216W w) = β₅Orig (vsSignOut216W w) := fun w ↦ by
      dsimp only [β₅Orig]; rw [hout5Orig w w.isLt]
      have ht : ∀ (i : ℕ) (hi : i < 6),
          (bitsVal (fun j ↦ β₃ (vsSignIn6W j))).testBit i =
            decide (β (vsSignIn6W ⟨i, hi⟩) = 1) := fun i hi ↦ by
        have heq : β₃ (vsSignIn6W ⟨i, hi⟩) = β (vsSignIn6W ⟨i, hi⟩) :=
          hpres3 _ (by generalize (⟨i, hi⟩ : Fin 6) = idx; revert idx; decide)
        rw [Slot3MicroEngineAux.bitsVal_testBit_eq (fun j ↦ β₃ (vsSignIn6W j)) ⟨i, hi⟩, heq]
      have hz_eq : ∀ u : Fin 3, decide (β (retZeroMW u) = 1) =
          decide (bitsVal (fun b ↦ β (p57MW u b)) = 0) := fun u ↦ by
        rw [hZ u]; by_cases h0 : bitsVal (fun b ↦ β (p57MW u b)) = 0 <;> simp
      have hs_pres : β₃ (p57S3W w) = β (p57S3W w) := hpres3 _ (by dsimp [p57S3W]; omega)
      have hm_pres : (fun b ↦ β₃ (p57MW w b)) = fun b ↦ β (p57MW w b) :=
        funext fun b ↦ hpres3 _ (by dsimp [p57MW]; omega)
      rw [hs_pres, hm_pres]
      clear hs_pres hm_pres
      have hFin : ∀ (u : Fin 3) (slot : ℕ) (hs1 : 6 ≤ slot) (hs2 : slot < 27)
          (hwEq : vsSignOut216W u = ⟨303 + (slot - 6), by omega⟩)
          (hck : Slot3MicroEngineAux.getBoolAt (Slot3MicroEngineAux.evalMicroList 6 vsSignFromZ6Ops
            (Slot3MicroEngineAux.initBoolList 6 27 (bitsVal (fun j ↦ β₃ (vsSignIn6W j))))) slot =
            !((bitsVal (fun j ↦ β₃ (vsSignIn6W j))).testBit u.val &&
              (bitsVal (fun j ↦ β₃ (vsSignIn6W j))).testBit (u.val + 3))),
          β₅ (vsSignOut216W u) = Micro216.boolToZMod2
            !(decide ((β (p57S3W u)).val = 1) && decide (bitsVal (fun b ↦ β (p57MW u b)) = 0)) :=
        fun u slot hs1 hs2 hwEq hck ↦ by
          dsimp only [β₅]
          rw [hwEq, hsOut5 slot hs1 hs2, hck, ht u.val (by omega), ht (u.val + 3) (by omega)]
          have hIn0 : vsSignIn6W ⟨u.val, by omega⟩ = p57S3W u := by fin_cases u <;> rfl
          have hIn3 : vsSignIn6W ⟨u.val + 3, by omega⟩ = retZeroMW u := by fin_cases u <;> rfl
          rw [hIn0, hIn3, hz_eq u]
          rcases bit_cases (β (p57S3W u)) with hs | hs <;> rw [hs] <;> rfl
      revert w; refine fin3_cases ?_ ?_ ?_
      · exact hFin 0 12 (by decide) (by decide) rfl hchk5.1.1.2
      · exact hFin 1 19 (by decide) (by decide) rfl hchk5.1.2
      · exact hFin 2 26 (by decide) (by decide) rfl hchk5.2
    obtain ⟨hcl4, hpres4, hsOut4⟩ := hEval4 β₅ hcl5
    obtain ⟨hcl4Orig, hpres4Orig, hsOut4Orig⟩ := hEval4 β₅Orig hcl5Orig
    let β₄ := (Micro216.ctxMicro vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7 hin4
      top7MaxMag11Ops top7MaxMag11_meta (by decide)).fwdBits β₅
    let β₄Orig := (Micro216.ctxMicro vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7 hin4
      top7MaxMag11Ops top7MaxMag11_meta (by decide)).fwdBits β₅Orig
    have hin4_eq : (fun k ↦ β₅ (vsTop7MaxMagIn11W k)) = fun k ↦ β₅Orig (vsTop7MaxMagIn11W k) :=
      funext fun k ↦ by
        have hk_lt : (vsTop7MaxMagIn11W k).val < 303 := by
          dsimp only [vsTop7MaxMagIn11W]
          split_ifs <;> (dsimp [muW, top7W, vsOr3_216W]; omega)
        exact (hpres5 hchk5.1.1.1 _ hk_lt).trans (hpres5Orig _ hk_lt).symm
    have hm4_lt : bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k)) < 2048 := bitsVal_lt_two_pow _
    have hchk4 := (Micro216.allBelow_iff 2048 top7MaxMag11Check).mp top7MaxMag11_eval_ok _ hm4_lt
    dsimp only [top7MaxMag11Check] at hchk4; simp only [Bool.and_eq_true, beq_iff_eq] at hchk4
    have hchk4Orig : Micro216.allBelow 11 (fun i ↦ Micro216.getBoolAt
        (Micro216.evalMicroList 11 top7MaxMag11Ops
          (Micro216.initBoolList 11 18 (bitsVal (fun k ↦ β₅Orig (vsTop7MaxMagIn11W k))))) i ==
        (bitsVal (fun k ↦ β₅Orig (vsTop7MaxMagIn11W k))).testBit i) = true := by
      rw [← hin4_eq]; exact hchk4.1
    have hin6_eq : (fun i ↦ β₄ (vsAnd5In216W i)) = fun i ↦ β₄Orig (vsAnd5In216W i) := by
      funext i; fin_cases i
      · exact (hpres4 hchk4.1 _ (by decide)).trans ((hpres5 hchk5.1.1.1 _ (by decide)).trans
          ((hpres5Orig _ (by decide)).symm.trans (hpres4Orig hchk4Orig _ (by decide)).symm))
      · change β₄ ⟨324 + (17 - 11), by decide⟩ = β₄Orig ⟨324 + (17 - 11), by decide⟩
        dsimp only [β₄, β₄Orig]
        rw [hsOut4 17 (by decide) (by decide), hsOut4Orig 17 (by decide) (by decide), hin4_eq]
      · exact (hpres4 hchk4.1 _ (by decide)).trans
          ((hSignEq 0).trans (hpres4Orig hchk4Orig _ (by decide)).symm)
      · exact (hpres4 hchk4.1 _ (by decide)).trans
          ((hSignEq 1).trans (hpres4Orig hchk4Orig _ (by decide)).symm)
      · exact (hpres4 hchk4.1 _ (by decide)).trans
          ((hSignEq 2).trans (hpres4Orig hchk4Orig _ (by decide)).symm)
    obtain ⟨_, _, hsOut6⟩ := hEval6 β₄ hcl4
    obtain ⟨_, _, hsOut6Orig⟩ := hEval6 β₄Orig hcl4Orig
    dsimp only [validStaticFromZ28_275Ctx, validStatic216_fast46_275Ctx]
    repeat rw [Micro216.TempCtx.append_fwdBits]
    rw [show (⟨334, by decide⟩ : Wire 437) = ⟨331 + (8 - 5), by decide⟩ from rfl,
      hsOut6 8 (by decide) (by decide), hsOut6Orig 8 (by decide) (by decide), hin6_eq]
  · exact (hBlk.2.2.2 β hβ q hq).trans (hBlkOrig.2.2.2 β hβ q hq).symm

theorem validStaticFromZ28_275_eq_orig (β : BitAssignment 437)
    (hβ : cleanRem 437 (437 - 275) β) (hZ : InvZMag3 β)
    (hmu : bitsVal (fun j ↦ β (muW j)) = shellMu3 (getU22 β)) (hm : ∀ w : Fin 3,
    bitsVal (fun b ↦ β (p57MW w b)) = shellMagCoord3 (getU22 β) w) :
    validStaticFromZ28_275.evalBits β = validStatic216_275.evalBits β :=
    (validStaticFromZ28_275_spec.2.2 β hβ hZ).trans
    (validStatic216_fast46_275_eq_orig β hβ hmu hm)

theorem dValidStaticFromZRev27_275_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n)
    (Inv : BitAssignment 437 → Prop) (hInv : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275)
    γ → Inv γ → InvValidStatic216Rev γ ∧ InvZMag3 γ) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - 275) (by decide) Inv) (dValidStaticFromZRev27_275 v rComb)
    (((validStaticFromZ28_275.onRegister rComb).toToffCircuit).eval) := by
  let mut1 : Wire 437 → Prop := fun w ↦ w = validStaticW
  obtain ⟨hd3, hs3, hd5, hs5, hd4, hs4⟩ := vsFromZ_prefix3_disj_supp (mutW := mut1) (fun _ h ↦ h)
  have hd6 : vsK6FastPre3Ctx.DisjointFrom mut1 := by
    dsimp [vsK6FastPre3Ctx, mut1, TempCtx.DisjointFrom, TempCtx.append, ctxTempBit]; decide
  have hs6 : vsK6FastPre3Ctx.SupportsBelowCtx 334 := by
    dsimp [vsK6FastPre3Ctx, TempCtx.SupportsBelowCtx, TempCtx.append, ctxTempBit]; decide
  obtain ⟨hB3, _, hEqFast⟩ := validStaticFromZ28_275_spec
  obtain ⟨_, _, hE3⟩ := validStatic216_fast46_275_spec
  have hVsEq : validStaticFromZ28_275 = (validStaticFromZRev27Ctx.append
      (ctxTempBit ⟨333, by decide⟩ (vsAnd5In216W 4) ⟨334, by decide⟩
        (by decide) (by decide) (by decide))).plug
      (.cliff (Micro216.cnotVec 1 (fun _ ↦ ⟨334, by decide⟩) (fun _ ↦ validStaticW)
        (fun _ ↦ by decide))) := by
    dsimp only [validStaticFromZ28_275, xorBlock1Prog216, xorBlockProg216,
      validStaticFromZ28_275Ctx, validStaticFromZRev27Ctx]
    repeat rw [TempCtx.append_assoc]; rfl
  refine dXorBlock1Peel_realizes v rComb 334 (by decide) (by decide)
    ⟨333, by decide⟩ (vsAnd5In216W 4) validStaticW (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) validStaticFromZRev27Ctx
    (TempCtx.disjointFrom_append hd3
      (TempCtx.disjointFrom_append hd5 (TempCtx.disjointFrom_append hd4 hd6)))
    (TempCtx.supportsBelowCtx_append le_rfl (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs3)
      (TempCtx.supportsBelowCtx_append le_rfl
        (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs5)
        (TempCtx.supportsBelowCtx_append le_rfl
          (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs4) hs6)))
    (.cliff (Micro216.cnotVec 1 (fun _ ↦ ⟨334, by decide⟩) (fun _ ↦ validStaticW)
      (fun _ ↦ by decide)))
    (fun _ ↦ trivial) (fun _ ↦ rfl) (fun _ ↦ rfl) Inv validStaticFromZ28_275 hVsEq hB3.1
    (fun γ hcl hi ↦ ?_)
  obtain ⟨⟨hmu, hm, hcoin, hvs⟩, hZ⟩ := hInv γ hcl hi
  rw [congrFun (hEqFast γ hcl hZ) validStaticW]
  have he := hE3 γ hcl hmu hm; dsimp only at he
  rw [he, hvs, hcoin]; exact CharTwo.add_self_eq_zero _

/-- Predicate identifying the 3 retained zero-magnitude wires `[254..257)`. -/
def isBadZ3 (w : Wire 437) : Bool := decide (254 ≤ w.val ∧ w.val < 257)

/-- Target zero-magnitude indicator bit `[shellMagCoord3(u22, w) = 0]` in `ZMod 2`. -/
def zMagBit (ξ : BitAssignment 437) (w : Fin 3) : ZMod 2 :=
  if shellMagCoord3 (getU22 ξ) w = 0 then 1 else 0

theorem zMagBit_congr_u22 {ξ₁ ξ₂ : BitAssignment 437}
    (hu22 : ∀ i : Fin 22, ξ₁ (u22WAux i) = ξ₂ (u22WAux i)) (w : Fin 3) :
    zMagBit ξ₁ w = zMagBit ξ₂ w := by
  dsimp only [zMagBit]
  rw [getU22_congr hu22]

/-- Overwrites wires `[254..257)` (`retZeroMW`) of `ξ` with `zMagBit ξ`. -/
def putZ3 (ξ : BitAssignment 437) : BitAssignment 437 :=
  fun w ↦
    if h : 254 ≤ w.val ∧ w.val < 257 then
      zMagBit ξ ⟨w.val - 254, by omega⟩
    else ξ w

theorem putZ3_of_not_bad {ξ : BitAssignment 437} {w : Wire 437} (hw : isBadZ3 w = false) :
    putZ3 ξ w = ξ w := by
  have hnot : ¬(254 ≤ w.val ∧ w.val < 257) := of_decide_eq_false hw
  exact dite_eq_right hnot

theorem putZ3_retZeroMW (ξ : BitAssignment 437) (w : Fin 3) :
    putZ3 ξ (retZeroMW w) = zMagBit ξ w := by
  have hmem : 254 ≤ (retZeroMW w).val ∧ (retZeroMW w).val < 257 := by
    dsimp [retZeroMW]; omega
  dsimp only [putZ3]
  rw [dite_eq_left hmem]
  congr 1
  ext
  dsimp [retZeroMW]
  omega

theorem cleanRem_putZ3 {ξ : BitAssignment 437} (hcl : cleanRem 437 (437 - 275) ξ) :
    cleanRem 437 (437 - 275) (putZ3 ξ) := fun w hw ↦ by
  rw [putZ3_of_not_bad (decide_eq_false (by omega))]
  exact hcl w hw

theorem eval_putZ3_of_disjoint {p : TempPhaseProg 437} (hp : progDisjointBad isBadZ3 p = true)
    (ξ : BitAssignment 437) (hu22 : ∀ i : Fin 22, p.evalBits ξ (u22WAux i) = ξ (u22WAux i))
    : p.evalSign (putZ3 ξ) = p.evalSign ξ ∧ p.evalBits (putZ3 ξ) = putZ3 (p.evalBits ξ) := by
  obtain ⟨hs, hEq, hBad⟩ := progDisjointBad_eval isBadZ3 p hp (putZ3 ξ) ξ
    (fun w hw ↦ putZ3_of_not_bad hw)
  refine ⟨hs, funext fun w ↦ ?_⟩
  by_cases h : 254 ≤ w.val ∧ w.val < 257
  · have hb : isBadZ3 w = true := decide_eq_true h
    rw [hBad w hb]
    dsimp only [putZ3]
    rw [dite_eq_left h, dite_eq_left h, zMagBit_congr_u22 hu22]
  · have hb : isBadZ3 w = false := decide_eq_false h
    rw [putZ3_of_not_bad hb, hEq w hb]

theorem invZMag3_putZ3 {ξ : BitAssignment 437}
    (hm : ∀ w : Fin 3, bitsVal (fun b ↦ ξ (p57MW w b)) = shellMagCoord3 (getU22 ξ) w) :
    InvZMag3 (putZ3 ξ) := fun w ↦ by
  dsimp only [InvZMag1]
  rw [putZ3_retZeroMW]
  have hfn : (fun b ↦ putZ3 ξ (p57MW w b)) = fun b ↦ ξ (p57MW w b) :=
    funext fun b ↦ putZ3_of_not_bad (by dsimp [isBadZ3, p57MW]; exact decide_eq_false (by omega))
  rw [hfn, hm w]
  rfl

/-- `319`-`TempAnd` (`1,276 T`) Stage-1 forward preparation with retained `retZeroMW`
  (`254..256`). -/
def pStep1ZRet30 : TempPhaseProg 437 := .seq coinMuXor275 (.seq magUnpack63_275 (.seq
    zMag3Ret18_275 (.seq validStaticFromZ28_275 (.seq axisStep3_fast_275
    sTrue18FwdPBuf_fast158_275))))

/-- `27`-`TempAnd` (`108 T`) Stage-5 swap-and-sign-flip reading retained `retZeroMW` (`-24 T`). -/
def pStep5ZRet30 : TempPhaseProg 437 := .seq cSwap24_275 s3FlipFromZ3_275

theorem pStep5ZRet30_count : pStep5ZRet30.countTempAnd = 27 := by
  have h1 := cSwap24_275_spec.2.1
  have h2 := s3FlipFromZ3_275_countTempAnd
  dsimp only [pStep5ZRet30, TempPhaseProg.countTempAnd]
  omega

theorem pStep5ZRet30_clean_spec : ValidCleanRem 437 (437 - 275) pStep5ZRet30 ∧
    (∀ β, cleanRem 437 (437 - 275) β → pStep5ZRet30.evalSign β = 0) ∧ (∀ β, cleanRem 437 (437
    - 275) β → cleanRem 437 (437 - 275) (pStep5ZRet30.evalBits β)) := by
  obtain ⟨hvSw, _, hsSw, hclSw, _⟩ := cSwap24_275_spec
  obtain ⟨hBFl, _, _⟩ := s3FlipFromZ3_275_spec
  obtain ⟨hv, _, hs, hcl, _⟩ := seqClean_spec (by decide)
    hvSw hBFl.1 hsSw hBFl.2.1 hclSw hBFl.2.2.1
  exact ⟨hv, hs, hcl⟩

theorem pStep5ZRet30_pres_mu (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β)
    (j : Fin 3) : pStep5ZRet30.evalBits β (muW j) = β (muW j) := by
  obtain ⟨_, _, _, hclSw, hSw⟩ := cSwap24_275_spec
  obtain ⟨hBFl, _, _⟩ := s3FlipFromZ3_275_spec
  dsimp only [pStep5ZRet30, TempPhaseProg.evalBits]
  have h1 : cSwap24_275.evalBits β (muW j) = β (muW j) :=
    (hSw β hβ).2.2 (muW j)
      (by dsimp [muW]; omega)
      (by dsimp [muW]; omega)
  have h2 : s3FlipFromZ3_275.evalBits (cSwap24_275.evalBits β) (muW j) =
      cSwap24_275.evalBits β (muW j) :=
    hBFl.2.2.2 _ (hclSw β hβ) (muW j) (fun ⟨w, h⟩ ↦ by
      have hv := congrArg Fin.val h; dsimp [muW, p57S3W] at hv; omega)
  exact h2.trans h1

set_option maxRecDepth 20000 in
theorem pStepsZRet30_disjoint :
    progDisjointBad isBadZ3 validStatic216_fast46_275 = true ∧
      progDisjointBad isBadZ3 axisStep3_fast_275 = true ∧
      progDisjointBad isBadZ3 magUnpack275 = true ∧
      progDisjointBad isBadZ3 magUnpack63_275 = true ∧
      progDisjointBad isBadZ3 cSwap24_275 = true ∧
      progDisjointBad isBadZ3 sTrue18RevPBuf275 = true ∧
      progDisjointBad isBadMW s3FlipFromZ3_275 = true := by decide

theorem pStep1ZRet30_disjointZ3_tail :
    progDisjointBad isBadZ3 sTrue18FwdPBuf_fast158_275 = true := by
  have hU : progDisjointBad isBadZ3 sTrue18FwdPBuf275 = true := by decide
  change progDisjointBad isBadZ3
    ((K_wrap.append (K_ax0.append (K_ax1.append K_ax2)) |>.append K_red77).plug innerApex2) =
      true at hU
  rw [progDisjointBad_plug, ctxDisjointBad_append, ctxDisjointBad_append] at hU
  obtain ⟨hPre, hIn⟩ := (Bool.and_eq_true _ _).mp hU
  obtain ⟨hWAx, hRed⟩ := (Bool.and_eq_true _ _).mp hPre
  obtain ⟨_, hAx⟩ := (Bool.and_eq_true _ _).mp hWAx
  have hWLin : ctxDisjointBad isBadZ3 K_wrapLin = true := by decide
  dsimp only [sTrue18FwdPBuf_fast158_275, ctxJointPBuf156, K_preRed79_lin]
  rw [progDisjointBad_plug, ctxDisjointBad_append, ctxDisjointBad_append, hWLin, hAx, hRed, hIn]
  rfl

/-- Stage-1 clean bit assignment after `pStep1ZRet30` (`putZ3 (st1 α)`). -/
def st1Z (α : BitAssignment 149) : BitAssignment 437 := putZ3 (st1 α)

theorem pStep1ZRet30_evalBits_st0 (α : BitAssignment 149) :
    pStep1ZRet30.evalBits (st0 α) = st1Z α := by
  dsimp only [st1Z]
  rw [← pStep1Lin_evalBits_st0 α]
  obtain ⟨_, hz₀, hcl₁, hp1, hu22_1, hmu₁⟩ := st0_coinMu_props α
  obtain ⟨hB2, _, hE2⟩ := magUnpack63_275_spec
  obtain ⟨hBZ, _, hEZ⟩ := zMag3Ret18_275_spec
  obtain ⟨hB3, _, _⟩ := validStatic216_fast46_275_spec
  obtain ⟨hB4, _, _⟩ := axisStep3_fast_275_spec
  obtain ⟨_, _, _, h5⟩ := sTrue18FwdPBuf_fast158_275_graft
  let β₁ := coinMuXor275.evalBits (st0 α)
  let β₂ := magUnpack63_275.evalBits β₁
  have hcl₂ := hB2.2.2.1 β₁ hcl₁
  have hp2 : ∀ q : Wire 437, ¬(177 ≤ q.val ∧ q.val < 198) → β₂ q = β₁ q :=
    fun q hm ↦ hB2.2.2.2 β₁ hcl₁ q (fun ⟨w, b, hq⟩ ↦ by
      subst hq; exact hm ⟨by dsimp [p57MW]; omega, by dsimp [p57MW]; omega⟩)
  have hu22_2 : getU22 β₂ = getU22 (st0 α) :=
    (getU22_congr (fun i ↦ hp2 _ (by dsimp [u22WAux]; omega))).trans hu22_1
  have hmu_val₁ : bitsVal (fun j ↦ β₁ (muW j)) = shellMu3 (getU22 β₁) := by
    rw [hu22_1]
    exact StepBBlock0.bitsVal_eq_of_testBit _ _ (lt_trans (shellMu3_lt_seven _) (by decide)) hmu₁
  have hm_val₂ : ∀ w : Fin 3,
      bitsVal (fun b ↦ β₂ (p57MW w b)) = shellMagCoord3 (getU22 β₂) w := fun w ↦ by
    rw [hu22_2]
    refine StepBBlock0.bitsVal_eq_of_testBit _ _ (s3ShellMagCoord3_lt_128 _ w) fun b ↦ ?_
    have hz : β₁ (p57MW w b) = 0 :=
      (hp1 _ (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega)).trans
        (hz₀ _ (by dsimp [p57MW]; omega))
    dsimp only [β₂]
    rw [hE2 β₁ hcl₁ hmu_val₁ w b, hz, zero_add]
    change (if (shellMagCoord3 (getU22 β₁) w).testBit b.val then (1 : ZMod 2) else 0) = _
    rw [hu22_1]
  have hzZ : zMag3Ret18_275.evalBits β₂ = putZ3 β₂ := by
    funext q
    by_cases h : 254 ≤ q.val ∧ q.val < 257
    · let w : Fin 3 := ⟨q.val - 254, by omega⟩
      have hq : q = retZeroMW w := Fin.ext (by dsimp [retZeroMW, w]; omega)
      have hz0 : β₂ (retZeroMW w) = 0 :=
        (hp2 _ (by dsimp [retZeroMW]; omega)).trans
          ((hp1 _ (by dsimp [retZeroMW]; omega) (by dsimp [retZeroMW]; omega)).trans
            (hz₀ _ (by dsimp [retZeroMW]; omega)))
      rw [hq, putZ3_retZeroMW, hEZ β₂ hcl₂ w, hz0, zero_add, hm_val₂ w]; rfl
    · rw [putZ3_of_not_bad (decide_eq_false h)]
      exact hBZ.2.2.2 β₂ hcl₂ q (fun ⟨w, hw⟩ ↦ h (by subst hw; dsimp [retZeroMW]; omega))
  let β₃ := validStatic216_fast46_275.evalBits β₂
  let β₄ := axisStep3_fast_275.evalBits β₃
  have hcl₃ := hB3.2.2.1 β₂ hcl₂
  have hcl₄ := hB4.2.2.1 β₃ hcl₃
  have hVsEq : validStaticFromZ28_275.evalBits (putZ3 β₂) = putZ3 β₃ := by
    rw [validStaticFromZ28_275_spec.2.2 (putZ3 β₂) (cleanRem_putZ3 hcl₂) (invZMag3_putZ3 hm_val₂),
      (eval_putZ3_of_disjoint pStepsZRet30_disjoint.1 β₂
        (fun i ↦ hB3.2.2.2 β₂ hcl₂ _ (fun h ↦ by
          have hv := congrArg Fin.val h; dsimp [u22WAux, validStaticW] at hv; omega))).2]
  have hAxEq : axisStep3_fast_275.evalBits (putZ3 β₃) = putZ3 β₄ :=
    (eval_putZ3_of_disjoint pStepsZRet30_disjoint.2.1 β₃
      (fun i ↦ hB4.2.2.2 β₃ hcl₃ _ (fun ⟨w, b, h⟩ ↦ by
        have hv := congrArg Fin.val h; dsimp [u22WAux, pBufW] at hv; omega))).2
  have hSTrueEq : sTrue18FwdPBuf_fast158_275.evalBits (putZ3 β₄) =
      putZ3 (sTrue18FwdPBuf_fast158_275.evalBits β₄) :=
    (eval_putZ3_of_disjoint pStep1ZRet30_disjointZ3_tail β₄
      (fun i ↦ (h5 β₄ hcl₄).1 _ (fun ⟨j, h⟩ ↦ by
        have hv := congrArg Fin.val h
        have := sTrue18WDefault216_bounds j; dsimp [u22WAux] at hv; omega))).2
  dsimp only [pStep1ZRet30, pStep1Lin]
  repeat rw [tempPhaseProg216_seq_evalBits]
  change sTrue18FwdPBuf_fast158_275.evalBits (axisStep3_fast_275.evalBits
    (validStaticFromZ28_275.evalBits (zMag3Ret18_275.evalBits β₂))) =
    putZ3 (sTrue18FwdPBuf_fast158_275.evalBits β₄)
  rw [hzZ, hVsEq, hAxEq, hSTrueEq]

/- Section 3: Retained mu-Quadratic Flags (251..253) and Fused ZQuadRet (-120 T / -132 T) -/

/-- `0`-`TempAnd` micro-program computing `7` one-hot `mu` selectors from `(mu, retMuQuadW)`. -/
def mu3OneHot7FromQuadOps : List Slot3MicroEngineAux.MicroOp := [
  .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc,
  .cnotW 3 11, .cnotW 4 12, .cnotW 5 13,
  .cnotW 0 10, .cnotW 11 10, .cnotW 12 10,
  .cnotW 1 8, .cnotW 11 8, .cnotW 13 8,
  .cnotW 2 7, .cnotW 12 7, .cnotW 13 7,
  .notW 6, .cnotW 10 6, .cnotW 8 6, .cnotW 11 6, .cnotW 7 6, .cnotW 12 6, .cnotW 13 6
]

/-- Slot indices `[6, 10, 8, 11, 7, 12, 13]` holding the `7` one-hot `mu` selector bits. -/
def mu3Sel7FromQuadSlots : List ℕ := [6, 10, 8, 11, 7, 12, 13]

theorem mu3Sel7FromQuadSlots_bounds14 (a : Fin 7) : 6 ≤ Slot3MicroEngineAux.getNatAt
    mu3Sel7FromQuadSlots a.val ∧ Slot3MicroEngineAux.getNatAt mu3Sel7FromQuadSlots a.val < 14 ∧
    275 + (Slot3MicroEngineAux.getNatAt mu3Sel7FromQuadSlots a.val - 6) = (accSel7W a).val := by
  fin_cases a <;> decide

/-- `14`-alloc `0`-`TempAnd` extension of `mu3OneHot7FromQuadOps` matching `magUnpack` slot
  layout. -/
def mu3OneHot7FromQuad14Ops : List Slot3MicroEngineAux.MicroOp := mu3OneHot7FromQuadOps ++
    [.zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc]

theorem mu3OneHot7FromQuad14_meta :
    Slot3MicroEngineAux.microValid 6 mu3OneHot7FromQuad14Ops = true ∧
      Slot3MicroEngineAux.microAllocs mu3OneHot7FromQuad14Ops = 14 ∧
      Slot3MicroEngineAux.microAnds mu3OneHot7FromQuad14Ops = 0 := by decide

/-- Exhaustive truth-table check over `6` input bits for `mu3OneHot7FromQuad14Ops`. -/
def mu3OneHot7FromQuad14Check (x : ℕ) : Bool :=
  let st :=
    Slot3MicroEngineAux.evalMicroList 6 mu3OneHot7FromQuad14Ops
    (Slot3MicroEngineAux.initBoolList 6 20 x)
  let m :=
    (if x.testBit 0 then 1 else 0) + 2 * (if x.testBit 1 then 1 else 0) + 4 *
    (if x.testBit 2 then 1 else 0)
  Slot3MicroEngineAux.allBelow 6 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (!(decide (m < 7) &&
       (x.testBit 3 == (x.testBit 0 && x.testBit 1)) &&
       (x.testBit 4 == (x.testBit 0 && x.testBit 2)) &&
       (x.testBit 5 == (x.testBit 1 && x.testBit 2))) ||
     Slot3MicroEngineAux.allBelow 7 (fun a ↦
       Slot3MicroEngineAux.getBoolAt st (Slot3MicroEngineAux.getNatAt mu3Sel7FromQuadSlots a) ==
         decide (m = a)))

theorem mu3OneHot7FromQuad14_eval_ok :
    Slot3MicroEngineAux.allBelow 64 mu3OneHot7FromQuad14Check = true := by decide

/-- `6`-wire input map `[muW 0..2, retMuQuadW 0..2]` for quadratic-retained `mu` decoders. -/
def muQuadIn6W : Fin 6 → Wire 437 :=
  ![muW 0, muW 1, muW 2, retMuQuadW 0, retMuQuadW 1, retMuQuadW 2]

theorem muQuadIn6W_inj : Function.Injective muQuadIn6W := fun i j h ↦ by
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)

/-- Retained-scratch invariant stating `retMuQuadW j = lhsQuad3 j * rhsQuad3 j` for `j < 3`. -/
def InvMuQuad3 (γ : BitAssignment 437) : Prop :=
  ∀ j : Fin 3, γ (retMuQuadW j) = γ (lhsQuad3 j) * γ (rhsQuad3 j)

theorem InvMuQuad3_congr {γ₁ γ₂ : BitAssignment 437}
    (hmu : ∀ j : Fin 3, γ₁ (muW j) = γ₂ (muW j))
    (hq : ∀ j : Fin 3, γ₁ (retMuQuadW j) = γ₂ (retMuQuadW j)) :
    InvMuQuad3 γ₁ ↔ InvMuQuad3 γ₂ := by
  refine forall_congr' fun j ↦ ?_
  have hl : γ₁ (lhsQuad3 j) = γ₂ (lhsQuad3 j) := by fin_cases j <;> exact hmu _
  have hr : γ₁ (rhsQuad3 j) = γ₂ (rhsQuad3 j) := by fin_cases j <;> exact hmu _
  rw [hq j, hl, hr]

/-- `0 T` (`0 TOFF`) measurement-based dynamic uncomputer clearing `retMuQuadW` (`251..253`). -/
def dClearRetMuQuad0_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    DynamicCircuit Var n :=
  dXorAndPairsUncomp v rComb 3 lhsQuad3 rhsQuad3 retMuQuadW lhsQuad3_ne_rhs

theorem dClearRetMuQuad0_275_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dClearRetMuQuad0_275 v rComb).count PrimitiveGate.T = 0 :=
  dXorAndPairsUncomp_count_t v rComb 3 lhsQuad3 rhsQuad3 retMuQuadW lhsQuad3_ne_rhs

theorem dClearRetMuQuad0_275_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dClearRetMuQuad0_275 v rComb).count PrimitiveGate.TOFF = 0 :=
  dXorAndPairsUncomp_count_toff v rComb 3 lhsQuad3 rhsQuad3 retMuQuadW lhsQuad3_ne_rhs

theorem dClearRetMuQuad0_275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) :
    PreservesStoreConst (dClearRetMuQuad0_275 v rComb) :=
  dXorAndPairsUncomp_preservesStore v rComb 3 lhsQuad3 rhsQuad3 retMuQuadW lhsQuad3_ne_rhs

theorem clearRetMuQuad_spec_and_dyn : ValidCleanRem 437 (437 - 275) muQuad3Ret3_275 ∧ (∀ δ :
    BitAssignment 437, cleanRem 437 (437 - 275) δ → muQuad3Ret3_275.evalSign δ = 0) ∧ (∀ δ :
    BitAssignment 437, cleanRem 437 (437 - 275) δ → cleanRem 437 (437 - 275)
    (muQuad3Ret3_275.evalBits δ) ∧ (∀ w : Wire 437, (∀ j, w ≠ retMuQuadW j) →
    muQuad3Ret3_275.evalBits δ w = δ w) ∧ (InvMuQuad3 δ → ∀ j : Fin 3,
    muQuad3Ret3_275.evalBits δ (retMuQuadW j) = 0)) ∧ (∀ {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n) (Inv :
    BitAssignment 437 → Prop), (∀ δ : BitAssignment 437, cleanRem 437 (437 - 275) δ → Inv δ →
    InvMuQuad3 δ) → RealizesCleanUnitary v (p57CleanDiagProj rComb (437 - 275) (by decide)
    Inv) (dClearRetMuQuad0_275 v rComb) (((muQuad3Ret3_275.onRegister
    rComb).toToffCircuit).eval)) := by
  have hl_a : ∀ i j : Fin 3, j.val ≤ i.val → lhsQuad3 i ≠ retMuQuadW j := by
    intro i j _; fin_cases i <;> fin_cases j <;> decide
  have hr_a : ∀ i j : Fin 3, j.val ≤ i.val → rhsQuad3 i ≠ retMuQuadW j := by
    intro i j _; fin_cases i <;> fin_cases j <;> decide
  obtain ⟨hv, hs, hEv⟩ :=
    xorAndPairsStatic_clear_spec 3 275 (by decide) lhsQuad3 rhsQuad3 retMuQuadW
    lhsQuad3_ne_rhs hl_a hr_a retMuQuadW_inj lhsQuad3_lt275 rhsQuad3_lt275 retMuQuadW_lt275
  exact ⟨hv, hs, hEv, fun v rComb Inv hInv ↦
    dXorAndPairsUncomp_realizes_static v rComb 3 275 (by decide) lhsQuad3 rhsQuad3 retMuQuadW
      lhsQuad3_ne_rhs hl_a hr_a retMuQuadW_inj lhsQuad3_lt275 rhsQuad3_lt275 retMuQuadW_lt275 Inv
        hInv⟩

theorem bool_not_or_elim {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  subst ha; exact h

theorem decide_zmod2_mul_eq_one (a b : ZMod 2) :
    decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  revert a b; decide

theorem bitsVal_fin3_eq (g : Fin 3 → ZMod 2) : (if decide (g 0 = 1) then 1 else 0) + 2 *
    (if decide (g 1 = 1) then 1 else 0) + 4 * (if decide (g 2 = 1) then 1 else 0) = bitsVal g
    := by
  revert g; decide

theorem retMuQuadW_val_eq (j : Fin 3) : (retMuQuadW j).val = 251 + j.val := by
  fin_cases j <;> rfl

theorem quad3_congr_of_mu {ξ₁ ξ₂ : BitAssignment 437}
    (hmu : ∀ i : Fin 3, ξ₁ (muW i) = ξ₂ (muW i)) (j : Fin 3) :
    ξ₁ (lhsQuad3 j) = ξ₂ (lhsQuad3 j) ∧ ξ₁ (rhsQuad3 j) = ξ₂ (rhsQuad3 j) := by
  fin_cases j <;> exact ⟨hmu _, hmu _⟩

/-- `0`-`TempAnd` `14`-alloc prefix `TempCtx` computing `magSel7W` from `(mu, retMuQuadW)`. -/
def magUnpackFromRetQuadK1Ctx : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro muQuadIn6W muQuadIn6W_inj 275 14 0
    (fun i ↦ by fin_cases i <;> decide)
    mu3OneHot7FromQuad14Ops mu3OneHot7FromQuad14_meta (by decide)

/-- `0 T` (`0 TOFF`) dynamic uncomputer for `magUnpack63_275` reading retained `retMuQuadW` (`-12
  T`). -/
def dMagUnpackFromRetQuad0_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb (dMagInnerLoop v rComb 21 le_rfl) magUnpackFromRetQuadK1Ctx

theorem dMagUnpackFromRetQuad0_275_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n)
    :
    (dMagUnpackFromRetQuad0_275 v rComb).count PrimitiveGate.T = 0 := by
  obtain ⟨hCnt1, _, _, _⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muQuadIn6W muQuadIn6W_inj 275 14 0
      (fun i ↦ by fin_cases i <;> decide)
      mu3OneHot7FromQuad14Ops mu3OneHot7FromQuad14_meta (by decide)
  dsimp only [dMagUnpackFromRetQuad0_275, magUnpackFromRetQuadK1Ctx]
  rw [p57ToDynWith_count_t, dMagInnerLoop_count_t, Nat.add_zero, hCnt1]

theorem dMagUnpackFromRetQuad0_275_count_toff {Var : Type} {n : ℕ} (v : Var)
    (rComb : QRegister 437 n) :
    (dMagUnpackFromRetQuad0_275 v rComb).count PrimitiveGate.TOFF = 0 :=
  p57ToDynWith_count_toff v rComb _ (dMagInnerLoop_count_toff v rComb 21 le_rfl)
    magUnpackFromRetQuadK1Ctx

theorem dMagUnpackFromRetQuad0_275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (rComb : QRegister 437 n) : PreservesStoreConst
    (dMagUnpackFromRetQuad0_275 v rComb) := p57ToDynWith_preservesStore v rComb _
    (dMagInnerLoop_preservesStore v rComb 21 le_rfl) magUnpackFromRetQuadK1Ctx

/-- Predicate identifying the 3 retained `mu`-quadratic wires `[251..254)`. -/
def isBadQ3 (w : Wire 437) : Bool := decide (251 ≤ w.val ∧ w.val < 254)

/-- Overwrites wires `[251..254)` (`retMuQuadW`) of `ξ` with `ξ (lhsQuad3 j) * ξ (rhsQuad3 j)`. -/
def putQ3 (ξ : BitAssignment 437) : BitAssignment 437 :=
  fun w ↦
    if h : 251 ≤ w.val ∧ w.val < 254 then
      let j : Fin 3 := ⟨w.val - 251, by omega⟩
      ξ (lhsQuad3 j) * ξ (rhsQuad3 j)
    else ξ w

theorem putQ3_of_not_bad {ξ : BitAssignment 437} {w : Wire 437} (hw : isBadQ3 w = false) :
    putQ3 ξ w = ξ w := by
  have hnot : ¬(251 ≤ w.val ∧ w.val < 254) := of_decide_eq_false hw
  exact dite_eq_right hnot

theorem putQ3_retMuQuadW (ξ : BitAssignment 437) (j : Fin 3) :
    putQ3 ξ (retMuQuadW j) = ξ (lhsQuad3 j) * ξ (rhsQuad3 j) := by
  fin_cases j <;> rfl

theorem invMuQuad3_putQ3 (ξ : BitAssignment 437) : InvMuQuad3 (putQ3 ξ) := fun j ↦ by
  fin_cases j <;> rfl

theorem cleanRem_putQ3 {ξ : BitAssignment 437} (hcl : cleanRem 437 (437 - 275) ξ) :
    cleanRem 437 (437 - 275) (putQ3 ξ) := fun w hw ↦ by
  rw [putQ3_of_not_bad (decide_eq_false (by omega))]
  exact hcl w hw

theorem muQuad3Ret3_evalBits_of_zero {ξ : BitAssignment 437}
    (hcl : cleanRem 437 (437 - 275) ξ) (hz : ∀ j : Fin 3, ξ (retMuQuadW j) = 0) :
    muQuad3Ret3_275.evalBits ξ = putQ3 ξ := by
  obtain ⟨_, hnon, hadd⟩ := muQuad3Ret3_275_spec.2.2 ξ hcl
  funext w
  by_cases h : 251 ≤ w.val ∧ w.val < 254
  · let j : Fin 3 := ⟨w.val - 251, by omega⟩
    have hw : w = retMuQuadW j := Fin.ext (by rw [retMuQuadW_val_eq]; dsimp [j]; omega)
    rw [hw, hadd j, hz j, zero_add, putQ3_retMuQuadW]
  · rw [putQ3_of_not_bad (decide_eq_false h)]
    exact hnon w (fun j hj ↦ h (by subst hj; fin_cases j <;> decide))

theorem muQuad3Ret3_evalBits_putQ3_of_zero {ξ : BitAssignment 437}
    (hcl : cleanRem 437 (437 - 275) ξ) (hz : ∀ j : Fin 3, ξ (retMuQuadW j) = 0) :
    muQuad3Ret3_275.evalBits (putQ3 ξ) = ξ := by
  have hclQ : cleanRem 437 (437 - 275) (putQ3 ξ) := cleanRem_putQ3 hcl
  obtain ⟨_, hnon, hclr⟩ := clearRetMuQuad_spec_and_dyn.2.2.1 (putQ3 ξ) hclQ
  funext w
  by_cases h : 251 ≤ w.val ∧ w.val < 254
  · let j : Fin 3 := ⟨w.val - 251, by omega⟩
    have hw : w = retMuQuadW j := Fin.ext (by rw [retMuQuadW_val_eq]; dsimp [j]; omega)
    rw [hw, hclr (invMuQuad3_putQ3 ξ) j, hz j]
  · rw [hnon w (fun j hj ↦ h (by subst hj; fin_cases j <;> decide)),
      putQ3_of_not_bad (decide_eq_false h)]

theorem eval_putQ3_of_disjoint {p : TempPhaseProg 437} (hp : progDisjointBad isBadQ3 p = true)
    (ξ : BitAssignment 437) (hmu : ∀ j : Fin 3, p.evalBits ξ (muW j) = ξ (muW j)) :
    p.evalSign (putQ3 ξ) = p.evalSign ξ ∧ p.evalBits (putQ3 ξ) = putQ3 (p.evalBits ξ) := by
  obtain ⟨hs, hEq, hBad⟩ := progDisjointBad_eval isBadQ3 p hp (putQ3 ξ) ξ
    (fun w hw ↦ putQ3_of_not_bad hw)
  refine ⟨hs, funext fun w ↦ ?_⟩
  by_cases h : 251 ≤ w.val ∧ w.val < 254
  · have hb : isBadQ3 w = true := decide_eq_true h
    rw [hBad w hb]
    dsimp only [putQ3]
    rw [dite_eq_left h, dite_eq_left h]
    let j : Fin 3 := ⟨w.val - 251, by omega⟩
    obtain ⟨hl, hr⟩ := quad3_congr_of_mu hmu j
    change ξ (lhsQuad3 j) * ξ (rhsQuad3 j) = p.evalBits ξ (lhsQuad3 j) * p.evalBits ξ (rhsQuad3 j)
    rw [hl, hr]
  · have hb : isBadQ3 w = false := decide_eq_false h
    rw [putQ3_of_not_bad hb, hEq w hb]

theorem muQuadIn6_cond_true (γ : BitAssignment 437) (hQ : InvMuQuad3 γ)
    (hμ7 : bitsVal (fun i ↦ γ (muW i)) < 7) :
    (if (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 0 then 1 else 0) +
      2 * (if (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 1 then 1 else 0) +
      4 * (if (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 2 then 1 else 0) =
        bitsVal (fun i ↦ γ (muW i)) ∧
    (decide (((if (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 0 then 1 else 0) +
      2 * (if (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 1 then 1 else 0) +
      4 * (if (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 2 then 1 else 0)) < 7) &&
      ((bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 3 ==
        ((bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 0 &&
         (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 1)) &&
      ((bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 4 ==
        ((bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 0 &&
         (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 2)) &&
      ((bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 5 ==
        ((bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 1 &&
         (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 2))) = true := by
  have ht : ∀ (i : ℕ) (hi : i < 6),
      (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit i = decide (γ (muQuadIn6W ⟨i, hi⟩) = 1) :=
    fun i hi ↦ Slot3MicroEngineAux.bitsVal_testBit_eq _ ⟨i, hi⟩
  have hm_eq : (if (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 0 then 1 else 0) +
      2 * (if (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 1 then 1 else 0) +
      4 * (if (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit 2 then 1 else 0) =
      bitsVal (fun i ↦ γ (muW i)) := by
    rw [ht 0 (by decide), ht 1 (by decide), ht 2 (by decide)]
    exact bitsVal_fin3_eq (fun i ↦ γ (muW i))
  have hqk : ∀ (k i0 i1 : ℕ) (hk : k < 6) (h0 : i0 < 6) (h1 : i1 < 6) (q : Fin 3),
      muQuadIn6W ⟨k, hk⟩ = retMuQuadW q → muQuadIn6W ⟨i0, h0⟩ = lhsQuad3 q →
      muQuadIn6W ⟨i1, h1⟩ = rhsQuad3 q →
      ((bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit k ==
        ((bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit i0 &&
         (bitsVal (fun j ↦ γ (muQuadIn6W j))).testBit i1)) = true :=
    fun k i0 i1 hk h0 h1 q hkq h0q h1q ↦ by
      rw [beq_iff_eq, ht k hk, ht i0 h0, ht i1 h1, hkq, h0q, h1q, hQ q]
      exact decide_zmod2_mul_eq_one _ _
  refine ⟨hm_eq, ?_⟩
  rw [hm_eq, decide_eq_true hμ7,
    hqk 3 0 1 (by decide) (by decide) (by decide) 0 rfl rfl rfl,
    hqk 4 0 2 (by decide) (by decide) (by decide) 1 rfl rfl rfl,
    hqk 5 1 2 (by decide) (by decide) (by decide) 2 rfl rfl rfl]
  rfl

theorem magUnpackFromRetQuadK1_dotSum_eq (γ : BitAssignment 437)
    (hcl : cleanRem 437 (437 - 275) γ)
    (hmu : bitsVal (fun j ↦ γ (muW j)) = shellMu3 (getU22 γ))
    (hQ : InvMuQuad3 γ) (idx : Fin 21) :
    (∑ k : Fin (magPairK idx),
      (magUnpackFromRetQuadK1Ctx.fwdBits γ) (magPairLhs idx k) *
        (magUnpackFromRetQuadK1Ctx.fwdBits γ) (magPairRhs idx k)) =
    if (shellMagCoord3 (getU22 γ) ⟨idx.val / 7, by omega⟩).testBit (idx.val % 7)
    then 1 else 0 := by
  obtain ⟨_, _, _, hEval1⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muQuadIn6W muQuadIn6W_inj 275 14 0
      (fun i ↦ by fin_cases i <;> decide)
      mu3OneHot7FromQuad14Ops mu3OneHot7FromQuad14_meta (by decide)
  obtain ⟨_, hpres1, hsOut1⟩ := hEval1 γ hcl
  let u22 := getU22 γ
  have hμ7 : bitsVal (fun i ↦ γ (muW i)) < 7 := hmu ▸ shellMu3_lt_seven u22
  have hchk := (Slot3MicroEngineAux.allBelow_iff 64 mu3OneHot7FromQuad14Check).mp
    mu3OneHot7FromQuad14_eval_ok _ (bitsVal_lt_two_pow (fun i ↦ γ (muQuadIn6W i)) : _ < 64)
  dsimp only [mu3OneHot7FromQuad14Check] at hchk
  have hchk12 := (Bool.and_eq_true _ _).mp hchk
  obtain ⟨hm_eq, hCond⟩ := muQuadIn6_cond_true γ hQ hμ7
  have hSelAll := bool_not_or_elim hchk12.2 hCond
  have huBitAll := StepBBlock0.u22_testBit_eq_wire u22WAux γ u22 rfl
  have hsel : ∀ a : Fin 7, (magUnpackFromRetQuadK1Ctx.fwdBits γ) (magSel7W a) =
      if shellMu3 u22 = a.val then 1 else 0 := fun a ↦ by
    obtain ⟨hb1, _, hwa⟩ := mu3Sel7FromQuadSlots_bounds14 a
    have ha := (Slot3MicroEngineAux.allBelow_iff 7 _).mp hSelAll a.val a.isLt
    simp only [beq_iff_eq] at ha
    have hwEq : magSel7W a =
        ⟨275 + (Slot3MicroEngineAux.getNatAt mu3Sel7FromQuadSlots a.val - 6), by omega⟩ :=
      Fin.ext hwa.symm
    dsimp only [magUnpackFromRetQuadK1Ctx]
    rw [hwEq, hsOut1 _ hb1 (by omega), ha, hm_eq, hmu]
    by_cases he : shellMu3 (getU22 γ) = a.val <;>
      simp [u22, Slot3MicroEngineAux.boolToZMod2, he]
  have hu22_fwd : ∀ i : Fin 22, (magUnpackFromRetQuadK1Ctx.fwdBits γ) (u22WAux i) =
      if u22.val.testBit i.val then 1 else 0 := fun i ↦ by
    dsimp only [magUnpackFromRetQuadK1Ctx]
    rw [hpres1 hchk12.1 (u22WAux i) (by dsimp [u22WAux]; omega), huBitAll i]
  exact magDotSum_eq u22 ⟨idx.val / 7, by omega⟩ ⟨idx.val % 7, by omega⟩
    (fun a ↦ (magUnpackFromRetQuadK1Ctx.fwdBits γ) (magSel7W a))
    (fun i ↦ (magUnpackFromRetQuadK1Ctx.fwdBits γ) (u22WAux i)) hsel hu22_fwd

open Classical in
theorem dMagUnpackFromRetQuad0_275_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n)
    (Inv : BitAssignment 437 → Prop) (hInv : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275)
    γ → Inv γ → InvMagRev γ ∧ InvMuQuad3 γ) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - 275) (by decide) Inv) (dMagUnpackFromRetQuad0_275 v rComb)
    ((((magUnpack63_275.onRegister rComb).toToffCircuit).eval)) := by
  obtain ⟨_, hProps1, hLift1, hEval1⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muQuadIn6W muQuadIn6W_inj 275 14 0
      (fun i ↦ by fin_cases i <;> decide)
      mu3OneHot7FromQuad14Ops mu3OneHot7FromQuad14_meta (by decide)
  obtain ⟨hd1, hs1⟩ := hProps1 (mutW := mutMag21)
    (fun i ⟨idx, h⟩ ↦ by
      have hv := congrArg Fin.val h
      fin_cases i <;> (dsimp [muQuadIn6W, muW, retMuQuadW, magDest21, p57MW] at hv; omega))
    (fun q hq ⟨idx, h⟩ ↦ by subst h; dsimp [magDest21, p57MW] at hq; omega)
  obtain ⟨hvIn, hsIn, hSpecIn⟩ := magInnerLoopStatic_spec 21 le_rfl
  obtain ⟨hBMag, _, hEMag⟩ := magUnpack63_275_spec
  have hd1' : magUnpackFromRetQuadK1Ctx.DisjointFrom mutMag21 := hd1
  have hcl1 : ∀ δ, cleanRem 437 (437 - 275) δ →
      cleanRem 437 (437 - 289) (magUnpackFromRetQuadK1Ctx.fwdBits δ) :=
    fun δ hδ ↦ (hEval1 δ hδ).1
  dsimp only [dMagUnpackFromRetQuad0_275]
  refine p57ToDynWith_realizes_prog_of_graft v rComb 289 (by decide) (by decide)
    mutMag21 magUnpackFromRetQuadK1Ctx hd1 hs1 (Slot3MicroEngineAux.TempCtxLiftEx.probe hLift1)
    (magInnerLoopStatic 21 le_rfl) magUnpack63_275 (dMagInnerLoop v rComb 21 le_rfl)
    (InvMagHole 21) Inv hvIn (magInnerLoopStatic_valid_le 20 le_rfl) hsIn
    (fun δ hδ w hw ↦ (hSpecIn δ hδ).2.1 w (fun idx _ h ↦ hw ⟨idx, h⟩))
    (dMagInnerLoop_realizes v rComb 21 le_rfl)
    (fun γ hcr hi ↦ ⟨hcl1 γ hcr, fun idx _ ↦ by
      obtain ⟨⟨hmu, hm⟩, hQ⟩ := hInv γ hcr hi
      rw [StepBBlock0.TempCtx.fwdBits_mut hd1' γ ⟨idx, rfl⟩,
        magUnpackFromRetQuadK1_dotSum_eq γ hcr hmu hQ idx]
      exact hm ⟨idx.val / 7, by omega⟩ ⟨idx.val % 7, by omega⟩⟩)
    (fun γ hcr _ ↦ hBMag.2.1 γ hcr)
    (fun γ hcr _ w hw ↦ hBMag.2.2.2 γ hcr w
      (fun ⟨w₀, b₀, h⟩ ↦ hw ⟨⟨7 * w₀.val + b₀.val, by omega⟩,
        h.trans (Fin.ext (by have := b₀.isLt; dsimp [magDest21, p57MW]; omega)).symm⟩))
    (fun γ hcr hi w ⟨idx, hw⟩ ↦ ?_)
  subst hw
  obtain ⟨⟨hmu, _⟩, hQ⟩ := hInv γ hcr hi
  rw [(hSpecIn _ (hcl1 γ hcr)).2.2 idx idx.isLt,
    StepBBlock0.TempCtx.fwdBits_mut hd1' γ ⟨idx, rfl⟩,
    magUnpackFromRetQuadK1_dotSum_eq γ hcr hmu hQ idx]
  dsimp only [magDest21]
  exact (hEMag γ hcr hmu ⟨idx.val / 7, by omega⟩ ⟨idx.val % 7, by omega⟩).symm

/-- `0`-`TempAnd` `14`-alloc micro-program computing `7` one-hot `mu` selectors and `7` `>=` bits
  from `(mu, retMuQuadW)`. -/
def mu3OneHot7GeFromQuadOps : List Slot3MicroEngineAux.MicroOp := mu3OneHot7FromQuad14Ops ++ [
    .cnotW 13 14, .cnotW 12 14, .cnotW 14 15, .cnotW 7 15, .cnotW 15 16, .cnotW 11 16, .cnotW
    16 17, .cnotW 8 17, .cnotW 17 18, .cnotW 10 18, .cnotW 18 19, .cnotW 6 19 ]

theorem mu3OneHot7GeFromQuad_meta :
    Slot3MicroEngineAux.microValid 6 mu3OneHot7GeFromQuadOps = true ∧
      Slot3MicroEngineAux.microAllocs mu3OneHot7GeFromQuadOps = 14 ∧
      Slot3MicroEngineAux.microAnds mu3OneHot7GeFromQuadOps = 0 := by decide

/-- Exhaustive equivalence check between `mu3OneHot7GeFromQuadOps` and `mu3OneHot7GeFastOps`. -/
def mu3OneHot7GeFromQuadEqCheck (x : ℕ) : Bool :=
  let m :=
    (if x.testBit 0 then 1 else 0) + 2 * (if x.testBit 1 then 1 else 0) + 4 *
    (if x.testBit 2 then 1 else 0)
  let stQ :=
    Slot3MicroEngineAux.evalMicroList 6 mu3OneHot7GeFromQuadOps
    (Slot3MicroEngineAux.initBoolList 6 20 x)
  let stF :=
    Slot3MicroEngineAux.evalMicroList 3
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFastOps
    (Slot3MicroEngineAux.initBoolList 3 17 m)
  Slot3MicroEngineAux.allBelow 6 (fun i ↦ Slot3MicroEngineAux.getBoolAt stQ i == x.testBit i) &&
    (!(decide (m < 7) &&
       (x.testBit 3 == (x.testBit 0 && x.testBit 1)) &&
       (x.testBit 4 == (x.testBit 0 && x.testBit 2)) &&
       (x.testBit 5 == (x.testBit 1 && x.testBit 2))) ||
     Slot3MicroEngineAux.allBelow 14 (fun k ↦
       Slot3MicroEngineAux.getBoolAt stQ (6 + k) == Slot3MicroEngineAux.getBoolAt stF (3 + k)))

theorem mu3OneHot7GeFromQuadEq_eval_ok :
    Slot3MicroEngineAux.allBelow 64 mu3OneHot7GeFromQuadEqCheck = true := by decide

/-- `60`-`TempAnd` forward `TempCtx` unpacking `p57MW` from `(u22, mu, retMuQuadW)` (`-3`
  `TempAnd`s vs `63`). -/
def magUnpackFromRetQuad60_275Ctx : TempCtx 437 :=
  let k1 := Slot3MicroEngineAux.ctxMicro muQuadIn6W muQuadIn6W_inj 275 14 0
    (fun i ↦ by fin_cases i <;> decide)
    mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta (by decide)
  let k2 := ctxCliffAlloc (.cnot (u22WAux 0) ⟨289, by decide⟩ (by decide))
  let k3 := Slot3MicroEngineAux.ctxAndPairs 6 290 (by decide)
    (fun i : Fin 6 ↦ magGeW ⟨i.val + 1, by omega⟩)
    (fun i : Fin 6 ↦ u22WAux ⟨i.val + 1, by omega⟩)
    (fun i ↦ wire_ne_of_gt (by
      have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
      dsimp at hb; dsimp [magGeW, u22WAux]; omega))
    (fun i ↦ by
      have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
      dsimp at hb; dsimp [magGeW]; omega)
    (fun i ↦ by dsimp [u22WAux]; omega)
  let k4 :=
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.ctxMagAxisLoopFast 1 (by decide) 296
    (by decide) (by decide) 7 le_rfl
  let k5 :=
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.ctxMagAxisLoopFast 2 (by decide) 324
    (by decide) (by decide) 7 le_rfl
  k1.append (k2.append (k3.append (k4.append k5)))

/-- `60`-`TempAnd` (`240 T`) forward `magUnpack` reading retained `retMuQuadW` (`-12 T` vs
  `magUnpack63_275`). -/
def magUnpackFromRetQuad60_275 : TempPhaseProg 437 :=
  xorBlockProg 21 magDest21 magSrc21
    (fun idx ↦ by dsimp [magDest21, p57MW]; omega)
    (fun idx ↦ by dsimp only [magSrc21]; split_ifs <;> (dsimp; omega))
    magUnpackFromRetQuad60_275Ctx

theorem magUnpackFromRetQuad60_275Ctx_fwdBits_eq (β : BitAssignment 437)
    (hβ : cleanRem 437 (437 - 275) β) (hQ : InvMuQuad3 β)
    (hμ7 : bitsVal (fun i ↦ β (muW i)) < 7) : magUnpackFromRetQuad60_275Ctx.fwdBits β =
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.magUnpack63_275Ctx.fwdBits β := by
  have hinQ : ∀ i, (muQuadIn6W i).val < 275 := fun i ↦ by fin_cases i <;> decide
  have hinF : ∀ i, (muW i).val < 275 := fun i ↦ by dsimp [muW]; omega
  obtain ⟨_, _, _, hEvalQ⟩ := Slot3MicroEngineAux.ctxMicro_scoped muQuadIn6W muQuadIn6W_inj 275
    14 0 hinQ mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta (by decide)
  obtain ⟨_, _, _, hEvalF⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muW muW_inj 275 14 3 hinF
      Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFastOps
      Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFast_meta3 (by decide)
  obtain ⟨hclQ, hpresQ, hsOutQ⟩ := hEvalQ β hβ
  obtain ⟨hclF, hpresF, hsOutF⟩ := hEvalF β hβ
  have hchkQ := (Slot3MicroEngineAux.allBelow_iff 64 mu3OneHot7GeFromQuadEqCheck).mp
    mu3OneHot7GeFromQuadEq_eval_ok _ (bitsVal_lt_two_pow (fun i ↦ β (muQuadIn6W i)) : _ < 64)
  dsimp only [mu3OneHot7GeFromQuadEqCheck] at hchkQ
  have hchkQ12 := (Bool.and_eq_true _ _).mp hchkQ
  have hchkF := (Slot3MicroEngineAux.allBelow_iff 7
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFastCheck).mp
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFast_eval_ok _ hμ7
  dsimp only [Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFastCheck]
    at hchkF
  have hchkF1 := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hchkF).1).1
  obtain ⟨hm_eq, hCond⟩ := muQuadIn6_cond_true β hQ hμ7
  have hSlotsEq := bool_not_or_elim hchkQ12.2 hCond
  have hk1_eq :
      (Slot3MicroEngineAux.ctxMicro muQuadIn6W muQuadIn6W_inj 275 14 0 hinQ
        mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta (by decide)).fwdBits β =
      (Slot3MicroEngineAux.ctxMicro muW muW_inj 275 14 3 hinF
        Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFastOps
        Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFast_meta3
        (by decide)).fwdBits β := by
    funext w
    by_cases hw275 : w.val < 275
    · exact (hpresQ hchkQ12.1 w hw275).trans (hpresF hchkF1 w hw275).symm
    · by_cases hw289 : w.val < 289
      · let k := w.val - 275
        have hw_q : w = ⟨275 + (6 + k - 6), by omega⟩ := Fin.ext (by dsimp [k]; omega)
        have hw_f : w = ⟨275 + (3 + k - 3), by omega⟩ := Fin.ext (by dsimp [k]; omega)
        have hbe := (Slot3MicroEngineAux.allBelow_iff 14 _).mp hSlotsEq k (by omega)
        simp only [beq_iff_eq, hm_eq] at hbe
        exact (congrArg _ hw_q).trans ((hsOutQ (6 + k) (by omega) (by omega)).trans
          ((congrArg Slot3MicroEngineAux.boolToZMod2 hbe).trans
            ((hsOutF (3 + k) (by omega) (by omega)).symm.trans (congrArg _ hw_f.symm))))
      · exact (hclQ w (by omega)).trans (hclF w (by omega)).symm
  dsimp only [magUnpackFromRetQuad60_275Ctx,
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.magUnpack63_275Ctx]
  repeat rw [Slot3MicroEngineAux.TempCtx.append_fwdBits]
  rw [hk1_eq]

theorem magUnpackFromRetQuad60_pkg :
    IsMutBlock 437 (437 - 275) (fun q ↦ ∃ idx, q = magDest21 idx) magUnpackFromRetQuad60_275 ∧
    magUnpackFromRetQuad60_275.countTempAnd = 60 ∧
    (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β → ∀ idx : Fin 21,
      magUnpackFromRetQuad60_275.evalBits β (magDest21 idx) =
        β (magDest21 idx) + magUnpackFromRetQuad60_275Ctx.fwdBits β (magSrc21 idx)) ∧
    IsMutBlock 437 (437 - 275) (fun q ↦ ∃ idx, q = magDest21 idx) magUnpack63_275 ∧
    (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β → ∀ idx : Fin 21,
      magUnpack63_275.evalBits β (magDest21 idx) =
        β (magDest21 idx) +
          Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.magUnpack63_275Ctx.fwdBits β
            (magSrc21 idx)) := by
  let mut21 : Wire 437 → Prop := fun q ↦ ∃ idx, q = magDest21 idx
  have hnot_ge275 : ∀ q : Wire 437, 275 ≤ q.val → ¬ mut21 q := by
    rintro q hq ⟨idx, rfl⟩; dsimp [magDest21, p57MW] at hq; omega
  have hnot_u22 : ∀ i : Fin 22, ¬ mut21 (u22WAux i) := by
    rintro i ⟨idx, h⟩; have hv := congrArg Fin.val h; dsimp [u22WAux, magDest21, p57MW] at hv; omega
  have hnot_mu : ∀ j : Fin 3, ¬ mut21 (muW j) := by
    rintro j ⟨idx, h⟩; have hv := congrArg Fin.val h; dsimp [muW, magDest21, p57MW] at hv; omega
  obtain ⟨hCnt1, hProps1, hLift1, _⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muQuadIn6W muQuadIn6W_inj 275 14 0
      (fun i ↦ by fin_cases i <;> decide)
      mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta (by decide)
  obtain ⟨hd1, hs1⟩ := hProps1 (mutW := mut21)
    (fun i ⟨idx, h⟩ ↦ by
      have hv := congrArg Fin.val h
      fin_cases i <;> (dsimp [muQuadIn6W, muW, retMuQuadW, magDest21, p57MW] at hv; omega))
    hnot_ge275
  let c2 : CliffProg 437 := .cnot (u22WAux 0) ⟨289, by decide⟩ (by decide)
  have hc2_supp : c2.SupportsBelow 290 := ⟨by dsimp [u22WAux]; omega, by dsimp; omega⟩
  have hd2 : (ctxCliffAlloc c2).DisjointFrom mut21 :=
    ctxCliffAlloc_disjoint ⟨hnot_u22 0, hnot_ge275 _ (by dsimp; omega)⟩
  have hs2 : (ctxCliffAlloc c2).SupportsBelowCtx 290 := ctxCliffAlloc_supports hc2_supp
  have hLift2 : Slot3MicroEngineAux.TempCtxLiftEx 289 290 (ctxCliffAlloc c2) :=
    Slot3MicroEngineAux.TempCtxLiftEx.mono
      (Slot3MicroEngineAux.TempCtxLiftEx.cliff 290 (by decide) c2 hc2_supp)
      (by decide) le_rfl (by decide)
  let l3 : Fin 6 → Wire 437 := fun i ↦ magGeW ⟨i.val + 1, by omega⟩
  let r3 : Fin 6 → Wire 437 := fun i ↦ u22WAux ⟨i.val + 1, by omega⟩
  have hne3 : ∀ i, l3 i ≠ r3 i := fun i ↦ wire_ne_of_gt (by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
    dsimp at hb; dsimp [l3, r3, magGeW, u22WAux]; omega)
  have hl3 : ∀ i, (l3 i).val < 290 := fun i ↦ by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
    dsimp at hb; dsimp [l3, magGeW]; omega
  have hr3 : ∀ i, (r3 i).val < 290 := fun i ↦ by dsimp [r3, u22WAux]; omega
  have hCnt3 := Slot3MicroEngineAux.ctxAndPairs_countTempAnd (M := 437) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3
  obtain ⟨hd3, hs3⟩ := Slot3MicroEngineAux.ctxAndPairs_props (mutW := mut21) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3 (fun i ↦ hnot_ge275 _ (by dsimp [l3, magGeW]; omega))
    (fun i ↦ hnot_u22 _) (fun q hq ↦ hnot_ge275 q (by omega))
  obtain ⟨hLift3, _⟩ := Slot3MicroEngineAux.ctxAndPairs_scoped (M := 437) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3
  obtain ⟨hCnt4, hProps4, hLift4, _⟩ :=
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.ctxMagAxisLoopFast_scoped 1
      (by decide) 296 (by decide) (by decide) 7 le_rfl
  obtain ⟨hCnt5, hProps5, hLift5, _⟩ :=
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.ctxMagAxisLoopFast_scoped 2
      (by decide) 324 (by decide) (by decide) 7 le_rfl
  obtain ⟨hd4, hs4⟩ := hProps4 hnot_mu (fun a ↦ hnot_ge275 _ (by dsimp [magSel7W]; omega))
    hnot_u22 (fun q hq ↦ hnot_ge275 q (by omega))
  obtain ⟨hd5, hs5⟩ := hProps5 hnot_mu (fun a ↦ hnot_ge275 _ (by dsimp [magSel7W]; omega))
    hnot_u22 (fun q hq ↦ hnot_ge275 q (by omega))
  have hXor21 (kAll : TempCtx 437) (hd : kAll.DisjointFrom mut21)
      (hs : kAll.SupportsBelowCtx 352) (hL : Slot3MicroEngineAux.TempCtxLiftEx 275 352 kAll) :=
    xorBlock275_spec (curEnd := 352) (by decide) (by decide) magDest21 magSrc21
      (fun idx ↦ by
        dsimp [magDest21, p57MW]
        omega)
      magDest21_inj
      (fun idx ↦ by
        dsimp only [magSrc21]
        split_ifs <;> dsimp
        all_goals omega)
      kAll hd hs hL
  have hdT := TempCtx.disjointFrom_append hd2
    (TempCtx.disjointFrom_append hd3 (TempCtx.disjointFrom_append hd4 hd5))
  have hsT := TempCtx.supportsBelowCtx_append (by decide) hs2
    (TempCtx.supportsBelowCtx_append (by decide) hs3
      (TempCtx.supportsBelowCtx_append (by decide) hs4 hs5))
  have hLT : Slot3MicroEngineAux.TempCtxLiftEx 289 352 _ :=
    Slot3MicroEngineAux.TempCtxLiftEx.append hLift2
      (Slot3MicroEngineAux.TempCtxLiftEx.append hLift3
        (Slot3MicroEngineAux.TempCtxLiftEx.append hLift4 hLift5))
  obtain ⟨hB, hCnt, hEv⟩ := hXor21 magUnpackFromRetQuad60_275Ctx
    (TempCtx.disjointFrom_append hd1 hdT) (TempCtx.supportsBelowCtx_append (by decide) hs1 hsT)
    (Slot3MicroEngineAux.TempCtxLiftEx.append hLift1 hLT)
  have hCntTot : magUnpackFromRetQuad60_275Ctx.countTempAnd = 60 := by
    dsimp only [magUnpackFromRetQuad60_275Ctx]
    repeat rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd]
    rw [hCnt1, hCnt3, hCnt4, hCnt5]
    rfl
  obtain ⟨_, hProps1F, hLift1F, _⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muW muW_inj 275 14 3
      (fun i ↦ by
        dsimp [muW]
        omega)
      Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFastOps
      Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.mu3OneHot7GeFast_meta3 (by decide)
  obtain ⟨hd1F, hs1F⟩ := hProps1F (mutW := mut21) hnot_mu hnot_ge275
  obtain ⟨hB63, _, hEv63⟩ := hXor21
    Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore.magUnpack63_275Ctx
    (TempCtx.disjointFrom_append hd1F hdT) (TempCtx.supportsBelowCtx_append (by decide) hs1F hsT)
    (Slot3MicroEngineAux.TempCtxLiftEx.append hLift1F hLT)
  exact ⟨hB, hCnt.trans hCntTot, hEv, hB63, hEv63⟩

theorem magUnpackFromRetQuad60_275_spec : IsMutBlock 437 (437 - 275)
    (fun q ↦ ∃ w b, q = p57MW w b) magUnpackFromRetQuad60_275 ∧
    magUnpackFromRetQuad60_275.countTempAnd = 60 ∧ (∀ β : BitAssignment 437, cleanRem 437 (437
    - 275) β → InvMuQuad3 β → bitsVal (fun i ↦ β (muW i)) < 7 →
    magUnpackFromRetQuad60_275.evalBits β = magUnpack63_275.evalBits β) := by
  obtain ⟨hB, hCnt, hEv, hB63, hEv63⟩ := magUnpackFromRetQuad60_pkg
  refine ⟨⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦ hB.2.2.2 β hβ q
      (fun ⟨idx, h⟩ ↦ hq ⟨⟨idx.val / 7, by omega⟩, ⟨idx.val % 7, by omega⟩, h⟩)⟩,
    hCnt, fun β hβ hQ hμ7 ↦ funext fun q ↦ ?_⟩
  by_cases hq : ∃ idx, q = magDest21 idx
  · obtain ⟨idx, rfl⟩ := hq
    rw [hEv β hβ idx, hEv63 β hβ idx, magUnpackFromRetQuad60_275Ctx_fwdBits_eq β hβ hQ hμ7]
  · exact (hB.2.2.2 β hβ q hq).trans (hB63.2.2.2 β hβ q hq).symm

/-- Static reverse-tail specification program for `ZQuadRet` (`264 T` target). -/
def revTailZQuadRet216_275 : TempPhaseProg 437 := .seq axisStep3_fast_275 (.seq
    validStaticFromZ28_275 (.seq zMag3Ret18_275 (.seq magUnpack63_275 (.seq muQuad3Ret3_275
    coinMuXor275))))

/-- `264 T` (`84 + 108 + 60 + 0 + 0 + 12`) dynamic reverse-tail uncomputer when `retMuQuadW`
  stays live. -/
def dRevTailZQuadRet216_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    DynamicCircuit Var n := .seq (dAxisStep3Rev_275 v rComb) (.seq (dValidStaticFromZRev27_275
    v rComb) (.seq (dZMag3Rev15_275 v rComb) (.seq (dMagUnpackFromRetQuad0_275 v rComb) (.seq
    (dClearRetMuQuad0_275 v rComb) (dCoinMuRev3_275 v rComb)))))

def InvRevTailZQuadRet216 (γ : BitAssignment 437) : Prop :=
  InvRevTailPruned216 γ ∧ InvZMag3 γ ∧ InvMuQuad3 γ

def top7MuAndQuad5Ops : List Slot3MicroEngineAux.MicroOp := [
  .notW 1, .notW 2, .notW 3, .notW 4, .notW 5, .notW 6,
  .andAlloc 6 5, .andAlloc 7 4, .andAlloc 8 3, .andAlloc 9 2, .andAlloc 10 1,
  .zeroAlloc, .cnotW 6 12, .cnotW 7 12, .cnotW 8 12, .cnotW 9 12, .cnotW 10 12, .cnotW 11 12,
  .zeroAlloc, .notW 13, .cnotW 6 13, .cnotW 8 13, .cnotW 10 13,
  .zeroAlloc, .notW 14, .cnotW 8 14,
  .notW 1, .notW 2, .notW 3, .notW 4, .notW 5, .notW 6,
  .zeroAlloc, .cnotW 8 15, .cnotW 9 15,
  .zeroAlloc, .notW 16, .cnotW 6 16, .cnotW 7 16,
  .zeroAlloc, .cnotW 6 17
]

theorem top7MuAndQuad5_meta3 :
    Slot3MicroEngineAux.microValid 7 top7MuAndQuad5Ops = true ∧
      Slot3MicroEngineAux.microAllocs top7MuAndQuad5Ops = 11 ∧
      Slot3MicroEngineAux.microAnds top7MuAndQuad5Ops = 5 := by decide

/-- Exhaustive truth-table check over `7` input bits (`0..127`) for `top7MuAndQuad5Ops`. -/
def top7MuAndQuad5Check (m : ℕ) : Bool :=
  let st :=
    Slot3MicroEngineAux.evalMicroList 7 top7MuAndQuad5Ops (Slot3MicroEngineAux.initBoolList 7 18 m)
  let mu := Slot3MicroEngineAux.s3mTop7Mu m
  Slot3MicroEngineAux.allBelow 7 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == m.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 12 == mu.testBit 0) &&
    (Slot3MicroEngineAux.getBoolAt st 13 == mu.testBit 1) &&
    (Slot3MicroEngineAux.getBoolAt st 14 == mu.testBit 2) &&
    (Slot3MicroEngineAux.getBoolAt st 15 == (mu.testBit 0 && mu.testBit 1)) &&
    (Slot3MicroEngineAux.getBoolAt st 16 == (mu.testBit 0 && mu.testBit 2)) &&
    (Slot3MicroEngineAux.getBoolAt st 17 == (mu.testBit 1 && mu.testBit 2))

theorem top7MuAndQuad5_eval_ok :
    Slot3MicroEngineAux.allBelow 128 top7MuAndQuad5Check = true := by decide

/-- Output temporary wire map `[280..286)` for `muAndQuadXor5Ctx`. -/
def muAndQuadXor5OutW (j : Fin 6) : Wire 437 := ⟨280 + j.val, by omega⟩

/-- `5`-`TempAnd` `TempCtx` computing `(mu, muQuad)` on `[280..286)` from `top7W`. -/
def muAndQuadXor5Ctx : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro top7W top7W_inj 275 11 5
    (fun i ↦ by dsimp [top7W]; omega)
    top7MuAndQuad5Ops top7MuAndQuad5_meta3 (by decide)

/-- `5`-`TempAnd` (`20 T`) fused forward XOR writing `muW` and `retMuQuadW` (`-12 T` vs `muXor +
  muQuad3`). -/
def muAndQuadXor5_275 : TempPhaseProg 437 :=
  xorBlockProg 6 muQuadIn6W muAndQuadXor5OutW
    (fun j ↦ by fin_cases j <;> decide)
    (fun j ↦ by dsimp [muAndQuadXor5OutW]; omega)
    muAndQuadXor5Ctx

theorem muAndQuadXor5_275_spec : IsMutBlock 437 (437 - 275) (fun q ↦ ∃ j, q = muQuadIn6W j)
    muAndQuadXor5_275 ∧ muAndQuadXor5_275.countTempAnd = 5 ∧ (∀ β : BitAssignment 437,
    cleanRem 437 (437 - 275) β → (∀ j : Fin 3, β (muW j) = 0) → muAndQuadXor5_275.evalBits
    β = (TempPhaseProg.seq muXor275 muQuad3Ret3_275).evalBits β) := by
  obtain ⟨hCntM, hPropsM, hLiftM, hEvalM⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped top7W top7W_inj 275 11 5
      (fun i ↦ by dsimp [top7W]; omega) top7MuAndQuad5Ops top7MuAndQuad5_meta3 (by decide)
  obtain ⟨hDisj, hSupp⟩ := hPropsM (mutW := fun q ↦ ∃ j, q = muQuadIn6W j)
    (fun i ⟨j, h⟩ ↦ by
      have hv := congrArg Fin.val h
      fin_cases j <;> (dsimp [top7W, muQuadIn6W, muW, retMuQuadW] at hv; omega))
    (fun w hw ⟨j, h⟩ ↦ by
      subst h; fin_cases j <;> (dsimp [muQuadIn6W, muW, retMuQuadW] at hw; omega))
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock275_spec (curEnd := 286) (by decide) (by decide)
    muQuadIn6W muAndQuadXor5OutW (fun j ↦ by fin_cases j <;> decide) muQuadIn6W_inj
    (fun j ↦ by dsimp [muAndQuadXor5OutW]; omega) muAndQuadXor5Ctx hDisj hSupp hLiftM
  refine ⟨hB, hCnt.trans hCntM, fun β hβ hmu0 ↦ ?_⟩
  obtain ⟨hBMu, _, hEMu⟩ := muXor275_spec_full
  obtain ⟨_, _, hQSpec⟩ := muQuad3Ret3_275_spec
  let β₁ := muXor275.evalBits β
  obtain ⟨_, hQNon, hQEv⟩ := hQSpec β₁ (hBMu.2.2.1 β hβ)
  obtain ⟨_, _, hsOut⟩ := hEvalM β hβ
  let m := bitsVal (fun i ↦ β (top7W i))
  have hchk := (Slot3MicroEngineAux.allBelow_iff 128 top7MuAndQuad5Check).mp
    top7MuAndQuad5_eval_ok m (bitsVal_lt_two_pow _)
  dsimp only [top7MuAndQuad5Check] at hchk
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨_, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩
  have hβ₁_mu : ∀ j : Fin 3, β₁ (muW j) =
      Slot3MicroEngineAux.boolToZMod2 ((Slot3MicroEngineAux.s3mTop7Mu m).testBit j.val) := fun j ↦
        by
    dsimp only [β₁]; rw [hEMu β hβ j, hmu0 j, zero_add]; rfl
  have hβ₁_quad : ∀ k : Fin 3, β₁ (retMuQuadW k) = β (retMuQuadW k) := fun k ↦
    hBMu.2.2.2 β hβ (retMuQuadW k) (fun ⟨j, hj⟩ ↦ by
      have hv := congrArg Fin.val hj; fin_cases k <;> (dsimp [retMuQuadW, muW] at hv; omega))
  have hbool_mul : ∀ a b : Bool, Slot3MicroEngineAux.boolToZMod2 (a && b) =
      Slot3MicroEngineAux.boolToZMod2 a * Slot3MicroEngineAux.boolToZMod2 b := by
    intro a b; cases a <;> cases b <;> rfl
  have hMCase : ∀ (i : Fin 6) (j : Fin 3) (s : ℕ) (hs1 : 7 ≤ s) (hs2 : s < 18),
      muQuadIn6W i = muW j → muAndQuadXor5OutW i = ⟨275 + (s - 7), by omega⟩ →
      (∀ k : Fin 3, muW j ≠ retMuQuadW k) →
      Slot3MicroEngineAux.getBoolAt (Slot3MicroEngineAux.evalMicroList 7 top7MuAndQuad5Ops
        (Slot3MicroEngineAux.initBoolList 7 18 m)) s =
          (Slot3MicroEngineAux.s3mTop7Mu m).testBit j.val →
      β (muQuadIn6W i) + muAndQuadXor5Ctx.fwdBits β (muAndQuadXor5OutW i) =
        muQuad3Ret3_275.evalBits β₁ (muQuadIn6W i) :=
    fun i j s hs1 hs2 hi ho hne hsEq ↦ by
      dsimp only [muAndQuadXor5Ctx]
      rw [hi, ho, hsOut s hs1 hs2, hsEq, hQNon (muW j) hne, hβ₁_mu j, hmu0 j, zero_add]
  have hQCase : ∀ (i : Fin 6) (k j0 j1 : Fin 3) (s : ℕ) (hs1 : 7 ≤ s) (hs2 : s < 18),
      muQuadIn6W i = retMuQuadW k → muAndQuadXor5OutW i = ⟨275 + (s - 7), by omega⟩ →
      lhsQuad3 k = muW j0 → rhsQuad3 k = muW j1 →
      Slot3MicroEngineAux.getBoolAt (Slot3MicroEngineAux.evalMicroList 7 top7MuAndQuad5Ops
        (Slot3MicroEngineAux.initBoolList 7 18 m)) s =
        ((Slot3MicroEngineAux.s3mTop7Mu m).testBit j0.val &&
         (Slot3MicroEngineAux.s3mTop7Mu m).testBit j1.val) →
      β (muQuadIn6W i) + muAndQuadXor5Ctx.fwdBits β (muAndQuadXor5OutW i) =
        muQuad3Ret3_275.evalBits β₁ (muQuadIn6W i) :=
    fun i k j0 j1 s hs1 hs2 hi ho hl hr hsEq ↦ by
      dsimp only [muAndQuadXor5Ctx]
      rw [hi, ho, hsOut s hs1 hs2, hsEq, hbool_mul, hQEv k, hβ₁_quad k, hl, hr,
        hβ₁_mu j0, hβ₁_mu j1]
  funext q
  by_cases hq : ∃ i : Fin 6, q = muQuadIn6W i
  · obtain ⟨i, rfl⟩ := hq
    dsimp only [muAndQuadXor5_275, TempPhaseProg.evalBits]
    rw [hEv β hβ i]
    fin_cases i
    · exact hMCase 0 0 12 (by decide) (by decide) rfl rfl (by decide) h12
    · exact hMCase 1 1 13 (by decide) (by decide) rfl rfl (by decide) h13
    · exact hMCase 2 2 14 (by decide) (by decide) rfl rfl (by decide) h14
    · exact hQCase 3 0 0 1 15 (by decide) (by decide) rfl rfl rfl rfl h15
    · exact hQCase 4 1 0 2 16 (by decide) (by decide) rfl rfl rfl rfl h16
    · exact hQCase 5 2 1 2 17 (by decide) (by decide) rfl rfl rfl rfl h17
  · dsimp only [muAndQuadXor5_275, TempPhaseProg.evalBits]
    rw [hB.2.2.2 β hβ q hq,
      hQNon q (fun k hk ↦ hq ⟨⟨3 + k.val, by omega⟩, by fin_cases k <;> exact hk⟩)]
    exact (hBMu.2.2.2 β hβ q
      (fun ⟨j, hj⟩ ↦ hq ⟨⟨j.val, by omega⟩, by fin_cases j <;> exact hj⟩)).symm

/-- `319`-`TempAnd` Stage-1 intermediate program using `muQuad3Ret3_275` +
  `magUnpackFromRetQuad60_275`. -/
def pStep1ZQuadRet30 : TempPhaseProg 437 := .seq coinMuXor275 (.seq muQuad3Ret3_275 (.seq
    magUnpackFromRetQuad60_275 (.seq zMag3Ret18_275 (.seq validStaticFromZ28_275 (.seq
    axisStep3_fast_275 sTrue18FwdPBuf_fast158_275)))))

set_option maxRecDepth 32768 in
theorem pStepsQZRet30_disjoint :
    progDisjointBad isBadQ3 magUnpack63_275 = true ∧
      progDisjointBad isBadQ3 zMag3Ret18_275 = true ∧
      progDisjointBad isBadQ3 validStaticFromZ28_275 = true ∧
      progDisjointBad isBadQ3 axisStep3_fast_275 = true ∧
      progDisjointBad isBadQ3 magUnpack275 = true ∧
      progDisjointBad isBadQ3 pStep5ZRet30 = true ∧
      progDisjointBad isBadQ3 sTrue18RevPBuf275 = true ∧
      progDisjointBad isBadZ3 magUnpackFromRetQuad60_275 = true := by decide

theorem pStep1ZQuadRet30_disjointQ3_tail :
    progDisjointBad isBadQ3 sTrue18FwdPBuf_fast158_275 = true := by
  have hU : progDisjointBad isBadQ3 sTrue18FwdPBuf275 = true := by decide
  change progDisjointBad isBadQ3
    ((K_wrap.append (K_ax0.append (K_ax1.append K_ax2)) |>.append K_red77).plug innerApex2) =
      true at hU
  rw [progDisjointBad_plug, ctxDisjointBad_append, ctxDisjointBad_append] at hU
  obtain ⟨hPre, hIn⟩ := (Bool.and_eq_true _ _).mp hU
  obtain ⟨hWAx, hRed⟩ := (Bool.and_eq_true _ _).mp hPre
  obtain ⟨_, hAx⟩ := (Bool.and_eq_true _ _).mp hWAx
  have hWLin : ctxDisjointBad isBadQ3 K_wrapLin = true := by decide
  dsimp only [sTrue18FwdPBuf_fast158_275, ctxJointPBuf156, K_preRed79_lin]
  rw [progDisjointBad_plug, ctxDisjointBad_append, ctxDisjointBad_append, hWLin, hAx, hRed, hIn]
  rfl

/-- Stage-1 clean bit assignment after `pStep1Fast316_ZQuadRet30` (`putQ3 (st1Z α)`). -/
def st1QZ (α : BitAssignment 149) : BitAssignment 437 := putQ3 (st1Z α)

theorem pStep1ZQuadRet30_evalBits_st0 (α : BitAssignment 149) :
    pStep1ZQuadRet30.evalBits (st0 α) = st1QZ α := by
  dsimp only [st1QZ]
  rw [← pStep1ZRet30_evalBits_st0 α]
  obtain ⟨_, hz₀, hcl₁, hp1, _, hmu₁⟩ := st0_coinMu_props α
  obtain ⟨hB2, _, _⟩ := magUnpack63_275_spec
  obtain ⟨hBZ, _, _⟩ := zMag3Ret18_275_spec
  obtain ⟨hB3, _, _⟩ := validStaticFromZ28_275_spec
  obtain ⟨hB4, _, _⟩ := axisStep3_fast_275_spec
  obtain ⟨_, _, _, h5⟩ := sTrue18FwdPBuf_fast158_275_graft
  let β₁ := coinMuXor275.evalBits (st0 α)
  have hmu_lt7 : bitsVal (fun j ↦ β₁ (muW j)) < 7 := by
    rw [StepBBlock0.bitsVal_eq_of_testBit _ _ (lt_trans (shellMu3_lt_seven _) (by decide)) hmu₁]
    exact shellMu3_lt_seven _
  have hzQ₁ : ∀ j : Fin 3, β₁ (retMuQuadW j) = 0 := fun j ↦
    (hp1 _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)).trans
      (hz₀ _ (by fin_cases j <;> decide))
  have hQ₁ : muQuad3Ret3_275.evalBits β₁ = putQ3 β₁ := muQuad3Ret3_evalBits_of_zero hcl₁ hzQ₁
  have hmu_putQ3 : bitsVal (fun j ↦ putQ3 β₁ (muW j)) < 7 := by
    rwa [show (fun j ↦ putQ3 β₁ (muW j)) = fun j ↦ β₁ (muW j) from
      funext fun j ↦ putQ3_of_not_bad (by dsimp [isBadQ3, muW]; exact decide_eq_false (by omega))]
  let β₂ := magUnpack63_275.evalBits β₁
  let β₃ := zMag3Ret18_275.evalBits β₂
  let β₄ := validStaticFromZ28_275.evalBits β₃
  let β₅ := axisStep3_fast_275.evalBits β₄
  have hcl₂ := hB2.2.2.1 β₁ hcl₁
  have hcl₃ := hBZ.2.2.1 β₂ hcl₂
  have hcl₄ := hB3.2.2.1 β₃ hcl₃
  have hcl₅ := hB4.2.2.1 β₄ hcl₄
  have hMagEq : magUnpackFromRetQuad60_275.evalBits (putQ3 β₁) = putQ3 β₂ := by
    rw [magUnpackFromRetQuad60_275_spec.2.2 (putQ3 β₁) (cleanRem_putQ3 hcl₁)
      (invMuQuad3_putQ3 β₁) hmu_putQ3]
    exact (eval_putQ3_of_disjoint pStepsQZRet30_disjoint.1 β₁ fun j ↦
      hB2.2.2.2 β₁ hcl₁ _ fun ⟨w, b, h⟩ ↦
        (by decide : ∀ j' w' b', muW j' ≠ p57MW w' b') j w b h).2
  have hZEq : zMag3Ret18_275.evalBits (putQ3 β₂) = putQ3 β₃ :=
    (eval_putQ3_of_disjoint pStepsQZRet30_disjoint.2.1 β₂ fun j ↦
      hBZ.2.2.2 β₂ hcl₂ _ fun ⟨w, h⟩ ↦
        (by decide : ∀ j' w', muW j' ≠ retZeroMW w') j w h).2
  have hVsEq : validStaticFromZ28_275.evalBits (putQ3 β₃) = putQ3 β₄ :=
    (eval_putQ3_of_disjoint pStepsQZRet30_disjoint.2.2.1 β₃ fun j ↦
      hB3.2.2.2 β₃ hcl₃ _ ((by decide : ∀ j', muW j' ≠ validStaticW) j)).2
  have hAxEq : axisStep3_fast_275.evalBits (putQ3 β₄) = putQ3 β₅ :=
    (eval_putQ3_of_disjoint pStepsQZRet30_disjoint.2.2.2.1 β₄ fun j ↦
      hB4.2.2.2 β₄ hcl₄ _ fun ⟨w, b, h⟩ ↦
        (by decide : ∀ j' w' b', muW j' ≠ pBufW w' b') j w b h).2
  have hSTEq : sTrue18FwdPBuf_fast158_275.evalBits (putQ3 β₅) =
      putQ3 (sTrue18FwdPBuf_fast158_275.evalBits β₅) :=
    (eval_putQ3_of_disjoint pStep1ZQuadRet30_disjointQ3_tail β₅ fun j ↦
      (h5 β₅ hcl₅).1 _ fun ⟨k, h⟩ ↦ by
        have hv := congrArg Fin.val h
        have := sTrue18WDefault216_bounds k
        dsimp [muW] at hv
        omega).2
  dsimp only [pStep1ZQuadRet30, pStep1ZRet30]
  repeat rw [tempPhaseProg216_seq_evalBits]
  change sTrue18FwdPBuf_fast158_275.evalBits (axisStep3_fast_275.evalBits
    (validStaticFromZ28_275.evalBits (zMag3Ret18_275.evalBits
      (magUnpackFromRetQuad60_275.evalBits (muQuad3Ret3_275.evalBits β₁))))) =
    putQ3 (sTrue18FwdPBuf_fast158_275.evalBits β₅)
  rw [hQ₁, hMagEq, hZEq, hVsEq, hAxEq, hSTEq]

/-- `294`-`TempAnd` Stage-1 tail following `muAndQuadXor5_275`
  (`magUnpackFromRetQuad60`..`sTrue18Fwd`). -/
def pStep1Tail294_ZQuadRet30 : TempPhaseProg 437 := .seq magUnpackFromRetQuad60_275 (.seq
    zMag3Ret18_275 (.seq validStaticFromZ28_275 (.seq axisStep3_fast_275
    sTrue18FwdPBuf_fast158_275)))

/-- `316`-`TempAnd` (`1,264 T`) Stage-1 forward preparation fusing `muAndQuadXor5_275` +
  `ZQuadRet` (`-24 T`). -/
def pStep1Fast316_ZQuadRet30 : TempPhaseProg 437 :=
  .seq coinOkXor275 (.seq muAndQuadXor5_275 pStep1Tail294_ZQuadRet30)

theorem pStep1Fast316_ZQuadRet30_evalBits_st0 (α : BitAssignment 149) :
    pStep1Fast316_ZQuadRet30.evalBits (st0 α) = st1QZ α := by
  rw [← pStep1ZQuadRet30_evalBits_st0 α]
  obtain ⟨hBC, _⟩ := coinOkXor275_spec
  obtain ⟨_, _, hEvM⟩ := muAndQuadXor5_275_spec
  let β₀ := st0 α
  have hcl₀ : cleanRem 437 (437 - 275) β₀ :=
    cleanRem_anti (by decide) (padZeroBits149_clean α)
  let β_c := coinOkXor275.evalBits β₀
  have hcl_c : cleanRem 437 (437 - 275) β_c := hBC.2.2.1 β₀ hcl₀
  have hmu0_c : ∀ j : Fin 3, β_c (muW j) = 0 := fun j ↦ by
    dsimp only [β_c]
    rw [hBC.2.2.2 β₀ hcl₀ (muW j) (wire_ne_of_lt (by dsimp [muW, coinOkW]; omega))]
    exact padZeroBits149_clean α (muW j) (by dsimp [muW]; omega)
  have hEq : muAndQuadXor5_275.evalBits β_c = muQuad3Ret3_275.evalBits (muXor275.evalBits β_c) :=
    hEvM β_c hcl_c hmu0_c
  dsimp only [pStep1Fast316_ZQuadRet30, pStep1Tail294_ZQuadRet30, pStep1ZQuadRet30,
    coinMuXor275, TempPhaseProg.evalBits]
  rw [hEq]

end
end ConfigSlot3ZRetCore
end Slot3ZRetCore
end
set_option exponentiation.threshold 256
end Slot3ZRetCore

section True18Compact99
local instance (priority := 1000000) instNeZeroTwoPow_True18Compact99 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
Compact `< 374`-Wire (`<= 99` Scratch Wires) Two-Phase `sTrue18` Forward & Asymmetric Dynamic
Uncomputer (`True18Compact99`) for Compact Slot-3 Leaves (`179w` / `190w` / `193w`).

Provides:
1. Two-phase `< 374`-wire column-reduction contexts `K_ph1` (`278 -> 371`, `93` `TempAnd`s for
   axes `0, 1`) and `K_ph2` (`278 -> 327`, `49` `TempAnd`s for axis `2`), wrapped inside linear
   `0`-`TempAnd` `K_wrapLin` (`275 -> 278`).
2. `374`-wire native circuits `sTrue18Fwd99_374 : TempPhaseProg 374` (`172` `TempAnd`s = `688 T`,
   peak wire `372 < 374`), `sTrue18Rev99_374 : TempPhaseProg 374`, and `0`-`TOFF` dynamic
   uncomputer `dSTrue18Rev99_374` (`624 T`, `PreservesStoreConst`, `RealizesCleanUnitary` on
   `p57CleanDiagProj rComb374 (374 - 275)` requiring only `99` clean scratch wires `275..373`).
3. `437`-wire wrappers `sTrue18Fwd99_275 : TempPhaseProg 437` (`progSupportsBelowB 374 = true`)
   and `dSTrue18Rev99_275` (`624 T`, `0 TOFF`, realizing both `sTrue18RevPBuf275` on
   `p57CleanDiagProj rComb (437 - 275)` and `sTrue18Rev99_275` on `< 374`-clean relay projectors
   with arbitrary dirty spectator wires `374..436`).
-/

namespace True18Compact99

section ConfigTrue18Compact99

set_option maxRecDepth 8192
set_option exponentiation.threshold 256

local instance (priority :=
  10) instLoc_True18Compact99_1InstNeZeroTwoPowSTrue99 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

-- Root solution namespace already active.
open MeasureBranchHadamardSem (bit_cases matrix_ext_ket)
open MeasureBranchHadamardSem (RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open Prod57BoothHoist
open Slot3Outer2344AndRelayWide.PosPhase246
  (cliffSupportsBelowB progSupportsBelowB
    truncateCtxB)
open Slot3ZRetCore (K_wrapLin)

/- Section 1: Polymorphic `cXor3M`, `apexMajAt`, and `dApexMajAt` Primitives -/

theorem evalBits_seq {M : ℕ} (p₁ p₂ : TempPhaseProg M) (β : BitAssignment M) :
    (TempPhaseProg.seq p₁ p₂).evalBits β = p₂.evalBits (p₁.evalBits β) := rfl

theorem evalSign_seq {M : ℕ} (p₁ p₂ : TempPhaseProg M) (β : BitAssignment M) :
    (TempPhaseProg.seq p₁ p₂).evalSign β = p₁.evalSign β + p₂.evalSign (p₁.evalBits β) := rfl

theorem countTempAnd_seq {M : ℕ} (p₁ p₂ : TempPhaseProg M) :
    (TempPhaseProg.seq p₁ p₂).countTempAnd = p₁.countTempAnd + p₂.countTempAnd := rfl

/-- Three-input XOR Clifford gadget `dst ⊕= a + b + c` on `Wire M`. -/
def cXor3M {M : ℕ} (a b c dst : Wire M) (ha : a ≠ dst) (hb : b ≠ dst) (hc : c ≠ dst) :
    CliffProg M := .seq (.cnot a dst ha) (.seq (.cnot b dst hb) (.cnot c dst hc))

theorem cXor3M_eval {M : ℕ} (a b c dst : Wire M) (ha : a ≠ dst) (hb : b ≠ dst) (hc : c ≠ dst)
    (δ : BitAssignment M) : (cXor3M a b c dst ha hb hc).eval δ = Function.update δ dst
    (δ dst + (δ a + δ b + δ c)) := by
  funext u
  dsimp [cXor3M, CliffProg.eval]
  by_cases hud : u = dst
  · subst hud
    simp [Function.update_self, Function.update_of_ne hb, Function.update_of_ne hc, add_assoc]
  · simp [Function.update_of_ne hud]

/-- Pre-Clifford CNOT sequence for majority-into-`sHi` on `Wire M`. -/
def cApexPreM {M : ℕ} (x y z sHi : Wire M) (hxs : x ≠ sHi) (hxy : x ≠ y) (hxz : x ≠ z) :
    CliffProg M := .seq (.cnot x sHi hxs) (.seq (.cnot x y hxy) (.cnot x z hxz))

/-- Post-Clifford CNOT sequence restoring `y, z` after majority-into-`sHi` on `Wire M`. -/
def cApexPostM {M : ℕ} (x y z : Wire M) (hxy : x ≠ y) (hxz : x ≠ z) : CliffProg M :=
  .seq (.cnot x z hxz) (.cnot x y hxy)

/-- `1`-`TempAnd` static majority XOR `sHi ⊕= maj(x, y, z)` using clean wire `⟨cur, hcur⟩`. -/
def apexMajAt {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (x y z sHi : Wire M) (hxs : x ≠ sHi)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (_hx : x.val < cur) (hy : y.val < cur)
    (hz : z.val < cur) (hs : sHi.val < cur) : TempPhaseProg M := .seq
    (.cliff (cApexPreM x y z sHi hxs hxy hxz)) (.seq (msbClearStatic cur hcur y z sHi hyz hy
    hz hs) (.cliff (cApexPostM x y z hxy hxz)))

/-- `0-T` dynamic uncomputer for `apexMajAt` when `sHi = maj(x, y, z)` (`0 T`, `0 TOFF`). -/
def dApexMajAt {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) (x y z sHi : Wire M)
    (hxs : x ≠ sHi) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : DynamicCircuit Var n := .seq
    (.circuit (((cApexPreM x y z sHi hxs hxy hxz).onRegister rComb).toCircuit)) (.seq
    (DynamicCircuit.andUncompute v (rComb y) (rComb z) (rComb sHi) (rComb.wires.injective.ne
    hyz)) (.circuit (((cApexPostM x y z hxy hxz).onRegister rComb).toCircuit)))

theorem dApexMajAt_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (x y z sHi : Wire M) (hxs : x ≠ sHi) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (dApexMajAt v rComb x y z sHi hxs hxy hxz hyz).count PrimitiveGate.T = 0 := by
  simp [dApexMajAt, DynamicCircuit.count_andUncompute_t]

theorem dApexMajAt_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (x y z sHi : Wire M) (hxs : x ≠ sHi) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (dApexMajAt v rComb x y z sHi hxs hxy hxz hyz).count PrimitiveGate.TOFF = 0 := by
  simp [dApexMajAt, DynamicCircuit.count_andUncompute_toff]

theorem dApexMajAt_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (x y z sHi : Wire M) (hxs : x ≠ sHi) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) : PreservesStoreConst
    (dApexMajAt v rComb x y z sHi hxs hxy hxz hyz) := PreservesStoreConst.seq
    (PreservesStoreConst.circuit _) (PreservesStoreConst.seq (PreservesStoreConst.andUncompute
    v _ _ _ _) (PreservesStoreConst.circuit _))
theorem apexMajAt_spec {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (x y z sHi : Wire M)
    (hxs : x ≠ sHi) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hys : y ≠ sHi) (hzs : z ≠ sHi)
    (hx : x.val < cur) (hy : y.val < cur) (hz : z.val < cur) (hs : sHi.val < cur) :
    ValidCleanRem M (M - cur) (apexMajAt cur hcur x y z sHi hxs hxy hxz hyz hx hy hz hs) ∧
    (apexMajAt cur hcur x y z sHi hxs hxy hxz hyz hx hy hz hs).countTempAnd = 1 ∧ (∀ r,
    ValidCleanRem M r (apexMajAt cur hcur x y z sHi hxs hxy hxz hyz hx hy hz hs) → M - cur ≤
    r) ∧ (∀ δ : BitAssignment M, cleanRem M (M - cur) δ → (apexMajAt cur hcur x y z sHi hxs
    hxy hxz hyz hx hy hz hs).evalSign δ = 0) ∧ (∀ δ : BitAssignment M, cleanRem M (M - cur) δ
    → cleanRem M (M - cur) ((apexMajAt cur hcur x y z sHi hxs hxy hxz hyz hx hy hz
    hs).evalBits δ) ∧ (apexMajAt cur hcur x y z sHi hxs hxy hxz hyz hx hy hz hs).evalBits δ =
    Function.update δ sHi (δ sHi + (δ x + (δ y + δ x) * (δ z + δ x)))) := by
  let p := apexMajAt cur hcur x y z sHi hxs hxy hxz hyz hx hy hz hs
  obtain ⟨hvM, hcM, hsM, hbM⟩ := msbClearStatic_spec cur hcur y z sHi hyz hys hzs hy hz hs
  have hcPre_supp : (cApexPreM x y z sHi hxs hxy hxz).SupportsBelow cur :=
    ⟨⟨hx, hs⟩, ⟨hx, hy⟩, ⟨hx, hz⟩⟩
  have hclPre : ∀ δ : BitAssignment M, cleanRem M (M - cur) δ →
      cleanRem M (M - cur) ((cApexPreM x y z sHi hxs hxy hxz).eval δ) := fun δ hδ w hw ↦ by
    rw [(cApexPreM x y z sHi hxs hxy hxz).eval_outside hcPre_supp δ w (by omega)]; exact hδ w hw
  have hclM : ∀ δ₁ : BitAssignment M, cleanRem M (M - cur) δ₁ →
      cleanRem M (M - cur) ((msbClearStatic cur hcur y z sHi hyz hy hz hs).evalBits δ₁) :=
    fun δ₁ hδ₁ w hw ↦ by
      rw [hbM δ₁ hδ₁, Function.update_of_ne (wire_ne_of_gt (by omega))]; exact hδ₁ w hw
  have hvAll : ValidCleanRem M (M - cur) p :=
    ⟨M - cur, Nat.sub_le M cur, trivial, ⟨M - cur, Nat.sub_le M cur, hvM, trivial, hclM⟩, hclPre⟩
  have hle_all : ∀ r, ValidCleanRem M r p → M - cur ≤ r := fun r hr ↦ by
    dsimp only [p, apexMajAt] at hr
    refine validCleanRem_cliff_seq_le (by omega) _ hcPre_supp (fun r' hr' ↦ ?_) hr
    obtain ⟨_, _, hv1, _, _⟩ := hr'
    exact msbClearStatic_valid_le cur hcur y z sHi hyz hy hz hs r' hv1
  refine ⟨hvAll, hcM, hle_all, fun δ hδ ↦ ?_, fun δ hδ ↦ ?_⟩
  · dsimp only [p, apexMajAt, TempPhaseProg.evalSign, TempPhaseProg.evalBits]
    rw [hsM _ (hclPre δ hδ)]; simp
  · have hEqBits : p.evalBits δ =
        Function.update δ sHi (δ sHi + (δ x + (δ y + δ x) * (δ z + δ x))) := by
      funext u
      dsimp only [p, apexMajAt, TempPhaseProg.evalBits]
      rw [hbM _ (hclPre δ hδ)]
      dsimp only [cApexPostM, cApexPreM, CliffProg.eval]
      simp only [Function.update_self, Function.update_of_ne hxs, Function.update_of_ne hxy,
        Function.update_of_ne hxz, Function.update_of_ne hyz, Function.update_of_ne hyz.symm,
        Function.update_of_ne hys, Function.update_of_ne hys.symm, Function.update_of_ne hzs,
        Function.update_of_ne hzs.symm, zmod2_add_self_cancel]
      by_cases huy : u = y
      · subst huy
        simp [Function.update_self, Function.update_of_ne hys]
      · by_cases huz : u = z
        · subst huz
          simp [Function.update_self, Function.update_of_ne hyz.symm, Function.update_of_ne hzs]
        · by_cases hus : u = sHi
          · subst hus
            simp [Function.update_self, Function.update_of_ne hys.symm,
              Function.update_of_ne hzs.symm, add_assoc]
          · simp [Function.update_of_ne huy, Function.update_of_ne huz,
              Function.update_of_ne hus]
    refine ⟨fun w hw ↦ ?_, hEqBits⟩
    rw [hEqBits, Function.update_of_ne (wire_ne_of_gt (by omega))]; exact hδ w hw

theorem dApexMajAt_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (cur : ℕ) (hcur : cur + 1 ≤ M)
    (x y z sHi : Wire M) (hxs : x ≠ sHi) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hys : y ≠ sHi) (hzs : z ≠ sHi) (hx : x.val < cur) (hy : y.val < cur) (hz : z.val < cur)
    (hs : sHi.val < cur) (Inv : BitAssignment M → Prop) (hInv : ∀ δ : BitAssignment M,
    cleanRem M (M - cur) δ → Inv δ → δ sHi = δ x + (δ y + δ x) * (δ z + δ x)) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (M - cur) (by omega) Inv)
    (dApexMajAt v rComb x y z sHi hxs hxy hxz hyz) ((((apexMajAt cur hcur x y z sHi hxs hxy
    hxz hyz hx hy hz hs).onRegister rComb).toToffCircuit).eval) := by
  let cPre := cApexPreM x y z sHi hxs hxy hxz
  let cPost := cApexPostM x y z hxy hxz
  let pMid := msbClearStatic cur hcur y z sHi hyz hy hz hs
  let InvMid : BitAssignment M → Prop := fun δ₁ ↦ δ₁ sHi = δ₁ y * δ₁ z
  have hcPre_supp : cPre.SupportsBelow cur := ⟨⟨hx, hs⟩, ⟨hx, hy⟩, ⟨hx, hz⟩⟩
  have hStep1 : ∀ δ : BitAssignment M, cleanRem M (M - cur) δ → Inv δ →
      cleanRem M (M - cur) ((TempPhaseProg.cliff cPre).evalBits δ) ∧
        InvMid ((TempPhaseProg.cliff cPre).evalBits δ) := fun δ hcl hi ↦ by
    refine ⟨fun w hw ↦ ?_, ?_⟩
    · rw [TempPhaseProg.evalBits, cPre.eval_outside hcPre_supp δ w (by omega)]; exact hcl w hw
    · dsimp [InvMid, TempPhaseProg.evalBits, cPre, cApexPreM, CliffProg.eval]
      simp only [Function.update_self, Function.update_of_ne hxs, Function.update_of_ne hxy,
        Function.update_of_ne hzs, Function.update_of_ne hzs.symm, Function.update_of_ne hys,
        Function.update_of_ne hys.symm, Function.update_of_ne hyz, Function.update_of_ne hyz.symm]
      rw [hInv δ hcl hi]
      generalize δ x = a; generalize δ y = b; generalize δ z = c
      revert a b c; decide
  obtain ⟨_, _, _, hbMid⟩ := msbClearStatic_spec cur hcur y z sHi hyz hys hzs hy hz hs
  have hStep2 : ∀ δ₁ : BitAssignment M, cleanRem M (M - cur) δ₁ → InvMid δ₁ →
      cleanRem M (M - cur) (pMid.evalBits δ₁) ∧ True := fun δ₁ hcl₁ _ ↦
    ⟨fun w hw ↦ by
      rw [hbMid δ₁ hcl₁, Function.update_of_ne (wire_ne_of_gt (by omega))]; exact hcl₁ w hw,
      trivial⟩
  have h123 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (M - cur) (by omega) Inv)
    (p57CleanDiagProj_conjTranspose rComb (M - cur) (by omega) InvMid)
    (RealizesCleanUnitary.circuit v _ ((cPre.onRegister rComb).toCircuit))
    (RealizesCleanUnitary_seq_asym
      (p57CleanDiagProj_conjTranspose rComb (M - cur) (by omega) InvMid)
      (p57CleanDiagProj_conjTranspose rComb (M - cur) (by omega) fun _ ↦ True)
      (dMsbClear_realizes_static v rComb cur hcur y z sHi hyz hys hzs hy hz hs
        (M - cur) (by omega) le_rfl InvMid (fun _ _ hi ↦ hi))
      (RealizesCleanUnitary.circuit v _ ((cPost.onRegister rComb).toCircuit))
      (p57SeqClean_prog_inv rComb pMid (by omega) (by omega) hStep2))
    (p57SeqClean_prog_inv rComb (.cliff cPre) (by omega) (by omega) hStep1)
  have hMul : ((((cPost.onRegister rComb).toCircuit).eval) * (((pMid.onRegister
      rComb).toToffCircuit).eval)) * (((cPre.onRegister rComb).toCircuit).eval) =
      ((((apexMajAt cur hcur x y z sHi hxs hxy hxz hyz hx hy hz hs).onRegister
      rComb).toToffCircuit).eval) := by
    simp [apexMajAt, cPre, cPost, pMid, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
      Circuit.eval_seq, mul_assoc]
  rwa [hMul] at h123

/- Section 2: `374 ↔ 437` Truncation & Lifting Infrastructure -/

/-- `374`-wire `sTrue18` output slice matching `sTrue18WDefault`. -/
def sTrue18W374 (j : Fin 18) : Wire 374 :=
  ⟨(sTrue18WDefault j).val, by revert j; decide⟩

def padCliff437 : CliffProg 374 → CliffProg 437
  | .nil => .nil
  | .x q => .x ⟨q.val, by omega⟩
  | .cnot c t hct =>
      .cnot ⟨c.val, by omega⟩ ⟨t.val, by omega⟩
        (fun h ↦ hct (Fin.ext (congrArg (Fin.val (n := 437)) h)))
  | .seq c₁ c₂ => .seq (padCliff437 c₁) (padCliff437 c₂)

/-- Embed a `374`-wire `TempPhaseProg` into `437` wires. -/
def padProg437 : TempPhaseProg 374 → TempPhaseProg 437
  | .nil => .nil
  | .cliff c => .cliff (padCliff437 c)
  | .z q => .z ⟨q.val, by omega⟩
  | .seq p₁ p₂ => .seq (padProg437 p₁) (padProg437 p₂)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd ⟨c₁.val, by omega⟩ ⟨c₂.val, by omega⟩ ⟨anc.val, by omega⟩
        (fun h ↦ h₁₂ (Fin.ext (congrArg (Fin.val (n := 437)) h)))
        (fun h ↦ h₁a (Fin.ext (congrArg (Fin.val (n := 437)) h)))
        (fun h ↦ h₂a (Fin.ext (congrArg (Fin.val (n := 437)) h)))
        (padProg437 body)

theorem cliffSupportsBelowB_padCliff437 :
    ∀ c : CliffProg 374, cliffSupportsBelowB 374 (padCliff437 c) = true
  | .nil => rfl
  | .x q => decide_eq_true q.isLt
  | .cnot c t _ => Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true c.isLt, decide_eq_true t.isLt⟩
  | .seq c₁ c₂ =>
      Bool.and_eq_true _ _ |>.mpr
        ⟨cliffSupportsBelowB_padCliff437 c₁, cliffSupportsBelowB_padCliff437 c₂⟩

theorem progSupportsBelowB_padProg437 :
    ∀ p : TempPhaseProg 374, progSupportsBelowB 374 (padProg437 p) = true
  | .nil => rfl
  | .cliff c => cliffSupportsBelowB_padCliff437 c
  | .z q => decide_eq_true q.isLt
  | .seq p₁ p₂ =>
      Bool.and_eq_true _ _ |>.mpr
        ⟨progSupportsBelowB_padProg437 p₁, progSupportsBelowB_padProg437 p₂⟩
  | .tempAnd c₁ c₂ anc _ _ _ body =>
      Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true c₁.isLt,
        Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true c₂.isLt,
          Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true anc.isLt,
            progSupportsBelowB_padProg437 body⟩⟩⟩

def K_wrapLin_374 : TempCtx 374 := truncateCtxB 374 K_wrapLin (by decide)

def ph0X0 : Wire 374 := ⟨177, by decide⟩

/-- Axis `1` LSB wire `184` on `Wire 374`. -/
def ph0X1 : Wire 374 := ⟨184, by decide⟩

/-- Axis `2` LSB wire `191` on `Wire 374`. -/
def ph0X2 : Wire 374 := ⟨191, by decide⟩

/-- Phase 0 LSB XOR Clifford `sTrue18[0] ⊕= d_0[0] + d_1[0] + d_2[0]`. -/
def ph0XorCliff : CliffProg 374 :=
  cXor3M ph0X0 ph0X1 ph0X2 (sTrue18W374 0) (by decide) (by decide) (by decide)

/-- Phase 0 majority `TempPhaseProg` `sTrue18[1] ⊕= maj(d_0[0], d_1[0], d_2[0])` at `cur = 278`. -/
def ph0MajProg : TempPhaseProg 374 := apexMajAt 278 (by decide) ph0X0 ph0X1 ph0X2
    (sTrue18W374 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- Phase 0 forward `1`-`TempAnd` program setting `sTrue18[0..1] = d_0 % 2 + d_1 % 2 + d_2 % 2`. -/
def ph0Fwd374 : TempPhaseProg 374 := .seq ph0MajProg (.cliff ph0XorCliff)

theorem ph0_fwd_val (x0 x1 x2 : ZMod 2) : (x0 + x1 + x2).val + 2 *
    (x0 + (x1 + x0) * (x2 + x0)).val = x0.val + x1.val + x2.val := by
  rcases bit_cases x0 with rfl | rfl <;>
    rcases bit_cases x1 with rfl | rfl <;>
    rcases bit_cases x2 with rfl | rfl <;> decide

theorem ph0_sum_bits_eq (x0 x1 x2 s0 s1 : ZMod 2)
    (h : s0.val + 2 * s1.val = x0.val + x1.val + x2.val) :
    s0 = x0 + x1 + x2 ∧ s1 = x0 + (x1 + x0) * (x2 + x0) := by
  rcases bit_cases x0 with rfl | rfl <;>
    rcases bit_cases x1 with rfl | rfl <;>
    rcases bit_cases x2 with rfl | rfl <;>
    rcases bit_cases s0 with rfl | rfl <;>
    rcases bit_cases s1 with rfl | rfl <;> revert h <;> decide

attribute [local irreducible] ph0Fwd374

/- Section 4B: Ripple-Carry Algebra and Phase 1 (`ph1Fwd374` / `dPh1Rev374`) -/

/-- `W`-bit ripple-carry sequence from LSB (`0`) to MSB (`Fin.last W`). -/
def rippleCarry : {W : ℕ} → (Fin W → ZMod 2) → (Fin W → ZMod 2) → ZMod 2 → Fin (W + 1) → ZMod 2
  | 0, _, _, cin, _ => cin
  | _ + 1, a, b, cin, j =>
      Fin.cases cin
        (fun i ↦ rippleCarry (fun k ↦ a k.succ) (fun k ↦ b k.succ)
          (cin + (a 0 + cin) * (b 0 + cin)) i) j

theorem rippleCarry_zero :
    ∀ {W : ℕ} (a b : Fin W → ZMod 2) (cin : ZMod 2),
      rippleCarry a b cin 0 = cin
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl

theorem rippleCarry_step :
    ∀ {W : ℕ} (a b : Fin W → ZMod 2) (cin : ZMod 2) (i : Fin W),
      rippleCarry a b cin i.succ =
        rippleCarry a b cin i.castSucc +
          (a i + rippleCarry a b cin i.castSucc) * (b i + rippleCarry a b cin i.castSucc)
  | 0, _, _, _, i => Fin.elim0 i
  | _ + 1, a, b, cin, i => by
      cases i using Fin.cases with
      | zero =>
          dsimp only [rippleCarry]
          simp only [Fin.cases_succ, Fin.castSucc_zero, Fin.cases_zero, rippleCarry_zero]
      | succ k =>
          have hcs : (k.succ).castSucc = (k.castSucc).succ := Fin.ext rfl
          dsimp only [rippleCarry]
          rw [hcs]
          simp only [Fin.cases_succ]
          exact rippleCarry_step (fun m ↦ a m.succ) (fun m ↦ b m.succ)
            (cin + (a 0 + cin) * (b 0 + cin)) k

theorem rippleCarry_bitsVal :
    ∀ {W : ℕ} (a b : Fin W → ZMod 2) (cin : ZMod 2),
      bitsVal (fun i : Fin W ↦ a i + b i + rippleCarry a b cin i.castSucc) +
        2 ^ W * (rippleCarry a b cin (Fin.last W)).val =
        bitsVal a + bitsVal b + cin.val
  | 0, _, _, cin => by simp [rippleCarry]
  | W + 1, a, b, cin => by
      have hl : (Fin.last (W + 1) : Fin (W + 2)) = (Fin.last W).succ :=
        Fin.ext (by simp [Fin.last])
      have hcs : ∀ k : Fin W, (k.succ : Fin (W + 1)).castSucc = (k.castSucc).succ :=
        fun _ ↦ Fin.ext rfl
      rw [bitsVal_succ_split, bitsVal_succ_split a, bitsVal_succ_split b, hl]
      dsimp only [rippleCarry]
      simp only [Fin.cases_zero, Fin.castSucc_zero, hcs, Fin.cases_succ]
      have ih := rippleCarry_bitsVal (fun k ↦ a k.succ) (fun k ↦ b k.succ)
        (cin + (a 0 + cin) * (b 0 + cin))
      have hfa := fullAdd_val_eq (a 0) (b 0) cin
      have hpw : 2 ^ (W + 1) * (rippleCarry (fun k ↦ a k.succ) (fun k ↦ b k.succ)
          (cin + (a 0 + cin) * (b 0 + cin)) (Fin.last W)).val =
        2 * (2 ^ W * (rippleCarry (fun k ↦ a k.succ) (fun k ↦ b k.succ)
          (cin + (a 0 + cin) * (b 0 + cin)) (Fin.last W)).val) := by ring
      omega
def ph1Dst15 (k : Fin 15) : Wire 374 :=
  sTrue18W374 ⟨2 + k.val, by omega⟩

/-- Phase 1 carry-in wire `⟨371, _⟩` at `k = 0` and `ph1Dst15 k` at `k > 0`. -/
def ph1CarryW (k : Fin 15) : Wire 374 :=
  if k.val = 0 then ⟨371, by decide⟩ else ph1Dst15 k

/- Section 4C: Phase 2 (`ph2Fwd374` / `dPh2Rev374`) via Clean-MSB Add/Subtract -/

/- Section 5A: Combined `374`-Wire `sTrue18Fwd99_374` (`172` `TempAnd`s) & `dSTrue18Rev99_374` -/

theorem p57CleanDiagProj_absorb {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    {rem₁ rem₂ : ℕ} (h₁ : rem₁ ≤ M) (h₂ : rem₂ ≤ M) {Inv₁ Inv₂ : BitAssignment M → Prop} (hImp
    : ∀ γ : BitAssignment M, cleanRem M rem₂ γ → Inv₂ γ → cleanRem M rem₁ γ ∧ Inv₁ γ) :
    p57CleanDiagProj rComb rem₁ h₁ Inv₁ * p57CleanDiagProj rComb rem₂ h₂ Inv₂ =
    p57CleanDiagProj rComb rem₂ h₂ Inv₂ := by
  apply matrix_ext_ket; intro β
  rw [mul_mulVec_prog, ket_p57CleanDiagProj]
  by_cases h : cleanRem M rem₂ (fun idx ↦ β (rComb idx)) ∧ Inv₂ (fun idx ↦ β (rComb idx))
  · obtain ⟨hc1, hi1⟩ := hImp _ h.1 h.2
    simp [h, hc1, hi1, ket_p57CleanDiagProj]
  · simp [h]

theorem p57ToDynWith_realizes_zero_and
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n)
    (innerProg : TempPhaseProg M) (dInner : DynamicCircuit Var n)
    (InvHole : BitAssignment M → Prop) (remHole : ℕ) (hremHole : remHole ≤ M)
    (hInner : RealizesCleanUnitary v (p57CleanDiagProj rComb remHole hremHole InvHole)
      dInner (((innerProg.onRegister rComb).toToffCircuit).eval)) :
    ∀ (K : TempCtx M), K.countTempAnd = 0 →
      ∀ (rem : ℕ) (hrem : rem ≤ M) (Inv : BitAssignment M → Prop),
        ValidCleanRem M rem (K.plug innerProg) →
        (∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ →
          cleanRem M remHole (K.fwdBits γ) ∧ InvHole (K.fwdBits γ)) →
        RealizesCleanUnitary v (p57CleanDiagProj rComb rem hrem Inv)
          (p57ToDynWith v rComb dInner K)
          ((((K.plug innerProg).onRegister rComb).toToffCircuit).eval)
  | .hole, _, rem, hrem, Inv, _, hFwd =>
      RealizesCleanUnitary.mono_proj
        (p57CleanDiagProj_conjTranspose rComb remHole hremHole InvHole)
        (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
        (p57CleanDiagProj_absorb rComb hremHole hrem hFwd)
        hInner
  | .seqPre c K, hc, rem, hrem, Inv, ⟨remMid, hmid, _, hv₂, hpres⟩, hFwd => by
      dsimp only [TempCtx.countTempAnd] at hc
      let InvMid : BitAssignment M → Prop :=
        fun δ ↦ ∃ γ, cleanRem M rem γ ∧ Inv γ ∧ δ = c.eval γ
      have ih₂ := p57ToDynWith_realizes_zero_and v rComb innerProg dInner InvHole remHole hremHole
        hInner K hc remMid hmid InvMid hv₂ (fun δ _ ⟨γ, hcr, hi, hδ⟩ ↦ by
          subst hδ; exact hFwd γ hcr hi)
      have hseq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
        (p57CleanDiagProj_conjTranspose rComb remMid hmid InvMid)
        (RealizesCleanUnitary.circuit v _ ((c.onRegister rComb).toCircuit)) ih₂
        (p57SeqClean_prog_inv rComb (.cliff c) hrem hmid
          (fun γ hcr hi ↦ ⟨hpres γ hcr, ⟨γ, hcr, hi, rfl⟩⟩))
      have heq : ((K.plug innerProg).onRegister rComb).toToffCircuit.eval *
          ((c.onRegister rComb).toCircuit).eval =
          ((((TempCtx.seqPre c K).plug innerProg).onRegister rComb).toToffCircuit).eval := by
        simp [TempCtx.plug, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
      dsimp only [p57ToDynWith]
      rwa [heq] at hseq
  | .seqPost K c, hc, rem, hrem, Inv, ⟨remMid, hmid, hv₁, _, hpres⟩, hFwd => by
      dsimp only [TempCtx.countTempAnd] at hc
      have ih₁ := p57ToDynWith_realizes_zero_and v rComb innerProg dInner InvHole remHole hremHole
        hInner K hc rem hrem Inv hv₁ hFwd
      have hseq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
        (p57CleanDiagProj_conjTranspose rComb remMid hmid (fun _ ↦ True))
        ih₁ (RealizesCleanUnitary.circuit v _ ((c.onRegister rComb).toCircuit))
        (p57SeqClean_prog_inv rComb (K.plug innerProg) hrem hmid
          (fun γ hcr _ ↦ ⟨hpres γ hcr, trivial⟩))
      have heq : ((c.onRegister rComb).toCircuit).eval *
          ((K.plug innerProg).onRegister rComb).toToffCircuit.eval =
          ((((TempCtx.seqPost K c).plug innerProg).onRegister rComb).toToffCircuit).eval := by
        simp [TempCtx.plug, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
      dsimp only [p57ToDynWith]
      rwa [heq] at hseq
  | .tempAnd _ _ _ _ _ _ _, hc, _, _, _, _, _ =>
      absurd hc (by simp [TempCtx.countTempAnd])

attribute [local irreducible] K_wrapLin_374

end

set_option maxRecDepth 512

end ConfigTrue18Compact99

end True18Compact99

end
set_option exponentiation.threshold 256
end True18Compact99

section Leaf3Slot3ZRet193
local instance (priority := 1000000) instNeZeroTwoPow_Leaf3Slot3ZRet193 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Compact `179w` / `193w` `Slot3Norm1s36` `ZRet` Slot-3 Oracles (`Leaf3Slot3ZRet193`)

Provides:
1. Concrete `165`-wire / `179`-wire `Slot3PrepCompactSpec` (`3,242 T`, `0 TOFF`) wired from
   `Leaf3Prep179Spec`.
2. Parameterized spectator-wire core-to-leaf assemblers (`mkSlot3CtrlLeafOfCoreWithDummy`,
   `mkSlot3Cat36LeafOfCoreWithDummy`) borrowing `437 - (149 + mWB)` spectator wires from
   `(rC.compose piSwap3Core).slice 18 _` so `437`-wire `StepBundle` stages compose verbatim
   on `mWB = 179`, `190`, and `193`.
3. Compact `179w` (`dSelCtrl`) and `193w` (`dSelCat`) `uCore149Norm1s` / `uSlot3Swap3Cat36Norm1s`
   realizers combining `Slot3ZRetCore`, `Leaf3Slot3Norm1sWidth204` (`clz17Ops` +
   `barrel55Ops`), `2`-phase `99`-scratch `sTrue18`, `17`-bit hoisted Booth (`mS = 2^17 + m17`),
   and `Slot3MidKick36CompactSpec 94 5116`, plus `CommutesWithReg (rCtrl3InCoreCat 36)` for
   `SelectExtStitch` and `Slot3LeafSpec` bundles.
-/

public section

namespace Leaf3Slot3ZRet193

section ConfigLeaf3Slot3ZRet193

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

local instance (priority :=
  10) instLoc_Leaf3Slot3ZRet193_1InstNeZeroTwoPowLeaf3ZRet (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open FullSysMomSlots0135Concrete (momCoreWires)
open MomSlots35Slot3ProjNuclear (s3MomCore_ge_4034)
open Leaf3Slot3Norm1sWidth204
  (coreWires80)

/- ## Section 1: Concrete `Slot3PrepCompactSpec` Instances & Spectator-Wire Disjointness -/

theorem rAct149_disj_rDummy_36 {mDummy n : ℕ} (hm : 18 + mDummy ≤ 3924)
    (rCore : QRegister coreWires80 n) (rPG36 : QRegister 36 n)
    (hCP : rCore.DisjointWires rPG36) :
    let hSlice : 18 + mDummy ≤ coreWires80 := by
      have : coreWires80 = momCoreWires 80 := rfl
      have := s3MomCore_ge_4034 (le_refl 80); omega
    ((rCore.concat rPG36 hCP).compose
      Leaf3Slot3Norm1sWidth204.Internal.sel149In36).DisjointWires
      (rCore.slice 18 mDummy hSlice) := by
  intro hSlice
  rw [QRegister.disjoint_iff]
  intro i j heq
  rw [QRegister.compose_apply, QRegister.slice_apply,
    ← QRegister.concat_apply_left rCore rPG36 hCP ⟨18 + j.val, by omega⟩] at heq
  have hv := congrArg Fin.val ((rCore.concat rPG36 hCP).wires.injective heq)
  have hj := j.isLt
  have hR : (Fin.castAdd 36 (⟨18 + j.val, by omega⟩ : Fin coreWires80)).val = 18 + j.val := rfl
  change Fin ((107 + 6) + 36) at i
  revert hv
  refine Fin.addCases (fun i113 ↦ ?_) (fun j36 hv ↦ ?_) i
  · refine Fin.addCases (fun i107 hv ↦ ?_) (fun j6 hv ↦ ?_) i113
    · unfold Leaf3Slot3Norm1sWidth204.Internal.sel149In36 at hv
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left] at hv
      have := Leaf3Slot3Norm1sWidth204.Internal.sel107_80_ge_3924
        i107
      change 0 + (StepBBlock0.sel107_80 i107).val = _ at hv; omega
    · unfold Leaf3Slot3Norm1sWidth204.Internal.sel149In36 at hv
      rw [QRegister.concat_apply_left, QRegister.concat_apply_right] at hv
      have := j6.isLt; change 0 + (0 + j6.val) = _ at hv; omega
  · unfold Leaf3Slot3Norm1sWidth204.Internal.sel149In36 at hv
    rw [QRegister.concat_apply_right] at hv
    change coreWires80 + j36.val = _ at hv; omega

/- ## Section 2: `MidKick94` Spec, `rCtrl3InCoreCat` Commutation & Spectator-Dummy Leaf Assemblers
-/

/- ## Section 3: Parameterized `topW` `StepBundleW` & Swap-Relay Engine -/

section RelayEngineW

open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (TempPhaseProg cleanRem ValidCleanRem tailScr writeRegProg writeRegProg_apply_reg
   writeRegProg_apply_of_not_mem eval_onRegister_prog_ket mul_mulVec_prog
   realizes_of_validCleanRem RealizesCleanUnitary_seq_asym PreservesStoreConst_toDyn
   embedMatrix_mulVec_ket_prog localIdxProg)
open MeasureBranchHadamardSem
  (ket ket_X ket_projector_zero matrix_ext_ket projZeroAll projZeroAll_conjTranspose
   ket_projZeroAll projZeroAll_eq_basisOutcomeProjector_zero RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open MomSlot0CircuitHalf (padZeroBits)
open Prod57BoothHoist
  (p57DiagProj ket_p57DiagProj p57DiagProj_conjTranspose p57BasisProj_comm_diag
   p57CleanDiagProj ket_p57CleanDiagProj)
open ShiftedMagS1 (disjConcatLeft padZeroBits_ltAux)
open StepBBlock0 (padZeroBits149_clean)
open OraAndPrepBundle (castNatReg)
open Slot3Outer2344AndRelayWide.PosPhase246
  (progSupportsBelowB truncateProgB truncateProgB_validCleanRem)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide
  (progDisjointBad progDisjointBad_eval truncateProgB_onRegister_eq
   permOfInvol permReg writeRegProg_compose_perm writeRegProg_idem_437)

def zeroTopW (topW : ℕ) (γ : BitAssignment 437) : BitAssignment 437 :=
  fun w ↦ if w.val < topW then γ w else 0

/-- Merges `δ` on `[0, topW)` with spectator assignment `γ` on `[topW, 437)`. -/
def liftTopW (topW : ℕ) (δ γ : BitAssignment 437) : BitAssignment 437 :=
  fun w ↦ if w.val < topW then δ w else γ w

theorem zeroTopW_lt {topW : ℕ} {γ : BitAssignment 437} {w : Wire 437} (hw : w.val < topW) :
    zeroTopW topW γ w = γ w := ite_eq_left hw

theorem zeroTopW_ge {topW : ℕ} {γ : BitAssignment 437} {w : Wire 437} (hw : topW ≤ w.val) :
    zeroTopW topW γ w = 0 := ite_eq_right (by omega)

theorem liftTopW_lt {topW : ℕ} {δ γ : BitAssignment 437} {w : Wire 437} (hw : w.val < topW) :
    liftTopW topW δ γ w = δ w := ite_eq_left hw

theorem liftTopW_ge {topW : ℕ} {δ γ : BitAssignment 437} {w : Wire 437} (hw : topW ≤ w.val) :
    liftTopW topW δ γ w = γ w := ite_eq_right (by omega)

theorem liftTopW_idem (topW : ℕ) (δ₂ δ₁ γ : BitAssignment 437) :
    liftTopW topW δ₂ (liftTopW topW δ₁ γ) = liftTopW topW δ₂ γ := by
  funext w; dsimp [liftTopW]; split_ifs <;> rfl

theorem zeroTopW_liftTopW {topW : ℕ} {δ : BitAssignment 437} (h275 : 275 ≤ topW)
    (γ : BitAssignment 437) (hcl : cleanRem 437 (437 - 275) δ) :
    zeroTopW topW (liftTopW topW δ γ) = δ := by
  funext w; dsimp [zeroTopW, liftTopW]; split_ifs with hw
  · rfl
  · exact (hcl w (by omega)).symm

/-- Stage-scoped swap-relay specification on `[0, M_stage)` (`275 ≤ topW ≤ M_stage ≤ 437`). -/
structure ValidSwapRelayWM (topW M_stage : ℕ) (swapX : Wire 437 → Wire 437)
    (isBadX : Wire 437 → Bool) : Prop where
  h275 : 275 ≤ topW
  htopM : topW ≤ M_stage
  hM437 : M_stage ≤ 437
  invol : ∀ w, swapX (swapX w) = w
  fix_ge_M : ∀ w : Wire 437, M_stage ≤ w.val → swapX w = w
  fix_not_bad_lt : ∀ w : Wire 437, w.val < topW → isBadX w = false → swapX w = w
  bad_lt275 : ∀ w : Wire 437, isBadX w = true → w.val < 275
  bad_swap_range : ∀ w : Wire 437, isBadX w = true ↔ topW ≤ (swapX w).val ∧ (swapX w).val < M_stage
  range_swap_bad : ∀ w : Wire 437, topW ≤ w.val ∧ w.val < M_stage ↔ isBadX (swapX w) = true

/-- Combined stage-disjointness mask marking `isBadX w` or `M_stage ≤ w.val`. -/
def isBadXM (M_stage : ℕ) (isBadX : Wire 437 → Bool) (w : Wire 437) : Bool :=
  isBadX w || decide (M_stage ≤ w.val)

/-- Diagonal invariant projector on `[0, topW)` requiring `[275, topW)` clean and `Inv` on
  `zeroTopW`. -/
noncomputable def baseDiagProjW (topW : ℕ) {n : ℕ} (rCombBase : QRegister 437 n)
    (Inv : BitAssignment 437 → Prop) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  p57DiagProj rCombBase (fun γ ↦
    (∀ w : Wire 437, 275 ≤ w.val → w.val < topW → γ w = 0) ∧ Inv (zeroTopW topW γ))

theorem baseDiagProjW_conjTranspose (topW : ℕ) {n : ℕ} (rCombBase : QRegister 437 n)
    (Inv : BitAssignment 437 → Prop) : (baseDiagProjW topW rCombBase Inv)ᴴ = baseDiagProjW
    topW rCombBase Inv := p57DiagProj_conjTranspose rCombBase _

open Classical in
theorem ket_baseDiagProjW (topW : ℕ) {n : ℕ} (rCombBase : QRegister 437 n)
    (Inv : BitAssignment 437 → Prop) (β : BitAssignment n) :
    (baseDiagProjW topW rCombBase Inv).mulVec (ket β) = if
    (∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β (rCombBase w) = 0) ∧ Inv
    (zeroTopW topW (fun idx ↦ β (rCombBase idx))) then ket β else 0 := by
  rcases Classical.em ((∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β (rCombBase w) = 0) ∧
      Inv (zeroTopW topW (fun idx ↦ β (rCombBase idx)))) with h | h
  · exact (ket_p57DiagProj rCombBase _ β).trans ((ite_eq_left h).trans (ite_eq_left h).symm)
  · exact (ket_p57DiagProj rCombBase _ β).trans ((ite_eq_right h).trans (ite_eq_right h).symm)

theorem relayWM_assign_props {topW M_stage : ℕ} {swapX : Wire 437 → Wire 437}
    {isBadX : Wire 437 → Bool} (hsr : ValidSwapRelayWM topW M_stage swapX isBadX)
    {γ δ : BitAssignment 437} (hγ_top : zeroTopW topW γ = δ)
    (hcl : cleanRem 437 (437 - 275) δ) (hbad0 : ∀ w, isBadX w = true → δ w = 0) : (∀ w : Wire
    437, isBadXM M_stage isBadX w = false → γ (swapX w) = δ w) ∧
    (∀ w : Wire 437, 275 ≤ w.val → w.val < M_stage → γ (swapX w) = 0) := by
  have h275 := hsr.h275
  have h1 : ∀ w : Wire 437, isBadXM M_stage isBadX w = false → γ (swapX w) = δ w := fun w hw ↦ by
    dsimp [isBadXM] at hw
    obtain ⟨hb, hm⟩ := Bool.or_eq_false_iff.mp hw
    have hwM : w.val < M_stage := Nat.lt_of_not_le (of_decide_eq_false hm)
    by_cases hlt : w.val < topW
    · rw [hsr.fix_not_bad_lt w hlt hb, ← hγ_top, zeroTopW_lt hlt]
    · have hge : topW ≤ w.val := by omega
      have hsw_bad : isBadX (swapX w) = true := (hsr.range_swap_bad w).mp ⟨hge, hwM⟩
      have hsw_lt : (swapX w).val < topW := lt_of_lt_of_le (hsr.bad_lt275 _ hsw_bad) h275
      have hz := (zeroTopW_lt (topW := topW) (γ := γ) hsw_lt).symm
      rw [hz, hγ_top, hbad0 (swapX w) hsw_bad, hcl w (by omega)]
  refine ⟨h1, fun w hw1 hw2 ↦ ?_⟩
  have hnot_bad : isBadXM M_stage isBadX w = false := by
    dsimp [isBadXM]
    rw [decide_eq_false (by omega), Bool.or_false]
    cases h : isBadX w
    · rfl
    · exfalso; have := hsr.bad_lt275 w h; omega
  rw [h1 w hnot_bad]; exact hcl w (by omega)

theorem relayWM_unswap_eq_liftTopW {topW M_stage : ℕ} {swapX : Wire 437 → Wire 437}
    {isBadX : Wire 437 → Bool} (hsr : ValidSwapRelayWM topW M_stage swapX isBadX)
    {γ δ_step δ_out : BitAssignment 437} (hcl_out : cleanRem 437 (437 - 275) δ_out)
    (hbad_out : ∀ w, isBadX w = true → δ_out w = 0)
    (hEq : ∀ w, isBadXM M_stage isBadX w = false → δ_step w = δ_out w) (hBad : ∀ w, isBadXM
    M_stage isBadX w = true → δ_step w = γ (swapX w)) : (fun idx ↦ δ_step (swapX idx)) =
    liftTopW topW δ_out γ := by
  have h275 := hsr.h275
  have htopM := hsr.htopM
  funext w
  by_cases hlt : w.val < topW
  · rw [liftTopW_lt hlt]
    cases hb : isBadX w
    · have hbm : isBadXM M_stage isBadX w = false := by
        dsimp [isBadXM]; rw [hb, decide_eq_false (by omega)]; rfl
      rw [hsr.fix_not_bad_lt w hlt hb, hEq w hbm]
    · obtain ⟨hsw_ge, hsw_ltM⟩ := (hsr.bad_swap_range w).mp hb
      have hsw_not_bad : isBadXM M_stage isBadX (swapX w) = false := by
        dsimp [isBadXM]
        rw [decide_eq_false (by omega), Bool.or_false]
        cases h : isBadX (swapX w)
        · rfl
        · exfalso; have := hsr.bad_lt275 _ h; omega
      rw [hEq (swapX w) hsw_not_bad, hcl_out (swapX w) (by omega), hbad_out w hb]
  · have hge : topW ≤ w.val := by omega
    rw [liftTopW_ge hge]
    by_cases hwM : w.val < M_stage
    · have hsw_bad : isBadX (swapX w) = true := (hsr.range_swap_bad w).mp ⟨hge, hwM⟩
      have hbm : isBadXM M_stage isBadX (swapX w) = true := by
        dsimp [isBadXM]; rw [hsw_bad]; rfl
      rw [hBad (swapX w) hbm, hsr.invol w]
    · have hgeM : M_stage ≤ w.val := by omega
      have hbm : isBadXM M_stage isBadX w = true := by
        dsimp [isBadXM]; rw [decide_eq_true hgeM, Bool.or_true]
      rw [hsr.fix_ge_M w hgeM, hBad w hbm, hsr.fix_ge_M w hgeM]

/- ### Section 3B.1: Unused-Ancilla Projector Dropping for `RealizesCleanUnitary` -/

/-- Exact rational `(3/5, 4/5)` `2 × 2` rotation matrix avoiding square roots. -/
noncomputable def rot35Mat : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ := Matrix.of fun i j ↦ if i
    = 0 then (if j = 0 then (3 : ℂ) / 5 else (4 : ℂ) / 5) else
    (if j = 0 then (-4 : ℂ) / 5 else (3 : ℂ) / 5)

/-- Bundled `1`-qubit unitary for `rot35Mat`. -/
noncomputable def rot35Unitary : Unitary (2 ^ 1) :=
  ⟨rot35Mat, by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rot35Mat, Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two,
        map_ofNat] <;>
      norm_num⟩

/-- Bundled `1`-qubit bit-flip unitary avoiding `vecHead`/`vecTail` reduction. -/
noncomputable def flip2Unitary : Unitary (2 ^ 1) :=
  ⟨Matrix.of fun i j ↦ if i = j then 0 else (1 : ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- Local `1`-qubit matrix unit `|a⟩⟨b|` on `Fin (2 ^ 1)`. -/
def matUnit2 (a b : Fin (2 ^ 1)) : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ :=
  Matrix.of fun i j ↦ if i = a ∧ j = b then 1 else 0

theorem singleton_basisOutcomeProjector_zero_eq_matUnit2 {n : ℕ} (w : Wire n) :
    (QRegister.singleton w).basisOutcomeProjector 0 =
      (QRegister.singleton w).embedMatrix (matUnit2 0 0) := by
  have hcomp : compProj (0 : Fin (2 ^ 1)) = matUnit2 0 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [compProj_eq_diagonal, matUnit2]
  rw [QRegister.basisOutcomeProjector, hcomp]

theorem embed_eq_zero_of_four_proj {n : ℕ} (w : Wire n)
    (D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hV : ∀ V : Unitary (2 ^ 1),
    (QRegister.singleton w).embedMatrix (V.1 * matUnit2 0 0 * V.1ᴴ) * D * (QRegister.singleton
    w).embedMatrix (V.1 * matUnit2 0 0 * V.1ᴴ) = 0) : D = 0 := by
  let r := QRegister.singleton w
  let e00 := matUnit2 0 0
  let e11 := matUnit2 1 1
  let e01 := matUnit2 0 1
  let e10 := matUnit2 1 0
  have he_sum : e00 + e11 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [e00, e11, matUnit2]
  have hD00 : r.embedMatrix e00 * D * r.embedMatrix e00 = 0 := by
    simpa [e00] using hV 1
  have hq1 : flip2Unitary.1 * e00 * flip2Unitary.1ᴴ = e11 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [e00, e11, matUnit2, flip2Unitary, Matrix.mul_apply, Fin.sum_univ_two]
  have hD11 : r.embedMatrix e11 * D * r.embedMatrix e11 = 0 := by
    have h1 := hV flip2Unitary; rwa [hq1] at h1
  let D01 := r.embedMatrix e00 * D * r.embedMatrix e11
  let D10 := r.embedMatrix e11 * D * r.embedMatrix e00
  have hR_sum : r.embedMatrix e00 + r.embedMatrix e11 = 1 := by
    rw [← r.embedMatrix_add, he_sum, r.embedMatrix_one]
  have hD_decomp : D = D01 + D10 := by
    calc D = (r.embedMatrix e00 + r.embedMatrix e11) * D *
              (r.embedMatrix e00 + r.embedMatrix e11) := by rw [hR_sum, one_mul, mul_one]
      _ = (r.embedMatrix e00 * D * r.embedMatrix e00 + D10) +
            (D01 + r.embedMatrix e11 * D * r.embedMatrix e11) := by
          dsimp only [D01, D10]; simp only [add_mul, mul_add]
      _ = D01 + D10 := by rw [hD00, hD11, zero_add, add_zero, add_comm D10 D01]
  let q2 := rot35Unitary.1 * e00 * rot35Unitary.1ᴴ
  let q3 := (PrimitiveGate.S.eval * rot35Unitary).1 * e00 *
    (PrimitiveGate.S.eval * rot35Unitary).1ᴴ
  have heq23 : (e00 * q2 = ((9 : ℂ) / 25) • e00 + ((-12 : ℂ) / 25) • e01) ∧
      (q2 * e00 = ((9 : ℂ) / 25) • e00 + ((-12 : ℂ) / 25) • e10) ∧
      (e00 * q3 = ((9 : ℂ) / 25) • e00 + ((12 * Complex.I) / 25) • e01) ∧
      (q3 * e00 = ((9 : ℂ) / 25) • e00 + ((-12 * Complex.I) / 25) • e10) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      ext i j
      fin_cases i <;> fin_cases j
      all_goals
        simp [q2, q3, rot35Unitary, rot35Mat, e00, e01, e10, matUnit2, Matrix.mul_apply,
          Fin.sum_univ_two, map_ofNat]
        try ring
  obtain ⟨he00_q2, hq2_e00, he00_q3, hq3_e00⟩ := heq23
  have hm00 : e00 * e00 = e00 ∧ e11 * e11 = e11 ∧ e00 * e11 = 0 ∧ e11 * e00 = 0 ∧
      e01 * e00 = 0 ∧ e00 * e10 = 0 ∧ e10 * e01 = e11 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      ext i j
      fin_cases i <;> fin_cases j
      all_goals simp [e00, e11, e01, e10, matUnit2, Matrix.mul_apply]
  obtain ⟨h00, h11, h00_11, h11_00, h01_00, h00_10, h10_01⟩ := hm00
  have hSandwich (q : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) (cL cR : ℂ)
      (hL : e00 * q = ((9 : ℂ) / 25) • e00 + cL • e01)
      (hR : q * e00 = ((9 : ℂ) / 25) • e00 + cR • e10)
      (hZ : r.embedMatrix q * D * r.embedMatrix q = 0) :
      (((9 : ℂ) / 25) * cR) • (D01 * r.embedMatrix e10) +
        (cL * ((9 : ℂ) / 25)) • (r.embedMatrix e01 * D10) = 0 := by
    have hZ0 : r.embedMatrix (e00 * q) * (D01 + D10) * r.embedMatrix (q * e00) = 0 := by
      rw [r.embedMatrix_mul, r.embedMatrix_mul, ← hD_decomp]
      calc (r.embedMatrix e00 * r.embedMatrix q) * D * (r.embedMatrix q * r.embedMatrix e00)
          = r.embedMatrix e00 * (r.embedMatrix q * D * r.embedMatrix q) * r.embedMatrix e00 := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hZ, mul_zero, zero_mul]
    simp only [hL, hR, r.embedMatrix_add, r.embedMatrix_smul] at hZ0
    have z1 : r.embedMatrix e00 * D01 = D01 := by
      dsimp [D01]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← r.embedMatrix_mul, h00]
    have z2 : D01 * r.embedMatrix e00 = 0 := by
      dsimp [D01]; rw [Matrix.mul_assoc, ← r.embedMatrix_mul, h11_00, r.embedMatrix_zero, mul_zero]
    have z3 : r.embedMatrix e01 * D01 = 0 := by
      dsimp [D01]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← r.embedMatrix_mul, h01_00,
        r.embedMatrix_zero, zero_mul, zero_mul]
    have z4 : r.embedMatrix e00 * D10 = 0 := by
      dsimp [D10]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← r.embedMatrix_mul, h00_11,
        r.embedMatrix_zero, zero_mul, zero_mul]
    have z5 : r.embedMatrix e01 * D10 * r.embedMatrix e00 = r.embedMatrix e01 * D10 := by
      dsimp [D10]; rw [Matrix.mul_assoc, Matrix.mul_assoc, ← r.embedMatrix_mul, h00]
    have z6 : r.embedMatrix e01 * D10 * r.embedMatrix e10 = 0 := by
      dsimp [D10]; rw [Matrix.mul_assoc, Matrix.mul_assoc, ← r.embedMatrix_mul, h00_10,
        r.embedMatrix_zero, mul_zero, mul_zero]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      z1, z2, z3, z4, z5, z6, smul_zero, add_zero, zero_add] at hZ0
    rwa [mul_comm ((9 : ℂ) / 25) cL, mul_comm cR ((9 : ℂ) / 25), add_comm] at hZ0
  have eqRe := hSandwich q2 ((-12 : ℂ) / 25) ((-12 : ℂ) / 25) he00_q2 hq2_e00 (hV rot35Unitary)
  have eqIm := hSandwich q3 ((12 * Complex.I) / 25) ((-12 * Complex.I) / 25) he00_q3 hq3_e00
    (hV (PrimitiveGate.S.eval * rot35Unitary))
  let X01 := D01 * r.embedMatrix e10
  let X10 := r.embedMatrix e01 * D10
  change (((9 : ℂ) / 25) * ((-12 : ℂ) / 25)) • X01 +
    (((-12 : ℂ) / 25) * ((9 : ℂ) / 25)) • X10 = 0 at eqRe
  change (((9 : ℂ) / 25) * ((-12 * Complex.I) / 25)) • X01 +
    (((12 * Complex.I) / 25) * ((9 : ℂ) / 25)) • X10 = 0 at eqIm
  have hAdd : X01 + X10 = 0 := by
    rw [show ((9 : ℂ) / 25) * ((-12 : ℂ) / 25) = (-108 : ℂ) / 625 by ring,
      show ((-12 : ℂ) / 25) * ((9 : ℂ) / 25) = (-108 : ℂ) / 625 by ring, ← smul_add] at eqRe
    exact (smul_eq_zero.mp eqRe).resolve_left (by norm_num)
  have hSub : -X01 + X10 = 0 := by
    rw [show ((9 : ℂ) / 25) * ((-12 * Complex.I) / 25) =
          ((108 * Complex.I) / 625) * (-1) by ring,
      show ((12 * Complex.I) / 25) * ((9 : ℂ) / 25) = (108 * Complex.I) / 625 by ring,
      mul_smul, neg_one_smul, ← smul_add] at eqIm
    exact (smul_eq_zero.mp eqIm).resolve_left (by norm_num [Complex.I_ne_zero])
  have hX10 : X10 = 0 := by
    have h2 : (2 : ℂ) • X10 = 0 := by
      rw [two_smul, show X10 + X10 = (X01 + X10) + (-X01 + X10) by abel, hAdd, hSub, add_zero]
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hX01 : X01 = 0 := by simpa [hX10] using hAdd
  have hD01_z : D01 = 0 := by
    calc D01 = r.embedMatrix e00 * D * (r.embedMatrix e11 * r.embedMatrix e11) := by
          dsimp only [D01]
          rw [← r.embedMatrix_mul, h11]
      _ = X01 * r.embedMatrix e01 := by
          dsimp only [X01, D01]
          rw [Matrix.mul_assoc (r.embedMatrix e00 * D * r.embedMatrix e11)
            (r.embedMatrix e10) (r.embedMatrix e01), ← r.embedMatrix_mul e10 e01, h10_01]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hX01, zero_mul]
  have hD10_z : D10 = 0 := by
    calc D10 = (r.embedMatrix e11 * r.embedMatrix e11) * D * r.embedMatrix e00 := by
          dsimp only [D10]
          rw [← r.embedMatrix_mul, h11]
      _ = r.embedMatrix e10 * X10 := by
          dsimp only [X10, D10]
          rw [← Matrix.mul_assoc (r.embedMatrix e10) (r.embedMatrix e01),
            ← r.embedMatrix_mul e10 e01, h10_01]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hX10, mul_zero]
  rw [hD_decomp, hD01_z, hD10_z, add_zero]

theorem circuit_eval_comm_singleton_of_not_mem_support {n : ℕ} {w : Wire n}
    (d : Circuit n) (hd : w ∉ d.support) (A : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) :
    d.eval.1 * (QRegister.singleton w).embedMatrix A =
      (QRegister.singleton w).embedMatrix A * d.eval.1 := by
  induction d with
  | identity => simp
  | gate g r =>
      have hdisj : (QRegister.singleton w).DisjointWires r :=
        QRegister.disjoint_iff.mpr fun _ j ↦ r.ne_apply_of_not_mem_image w hd j
      exact ((QRegister.singleton w).embedMatrix_comm_of_disjoint r hdisj A g.eval.1).symm
  | seq d₁ d₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.mem_union, not_or] at hd
      calc (d₂.eval * d₁.eval).1 * (QRegister.singleton w).embedMatrix A
          = d₂.eval.1 * (d₁.eval.1 * (QRegister.singleton w).embedMatrix A) := by
              simp [Matrix.mul_assoc]
        _ = (d₂.eval.1 * (QRegister.singleton w).embedMatrix A) * d₁.eval.1 := by
              rw [ih₁ hd.1, Matrix.mul_assoc]
        _ = (QRegister.singleton w).embedMatrix A * (d₂.eval * d₁.eval).1 := by
              rw [ih₂ hd.2]; simp [Matrix.mul_assoc]

theorem sandwich_comm {m : ℕ} {A B M C D : Matrix (Fin m) (Fin m) ℂ}
    (hAB : A * B = B * A) (hCD : C * D = D * C) :
    A * (B * M * C) * D = B * (A * M * D) * C := by
  calc A * (B * M * C) * D = (A * B) * M * (C * D) := by simp only [Matrix.mul_assoc]
    _ = B * (A * M * D) * C := by rw [hAB, hCD]; simp only [Matrix.mul_assoc]

theorem wp_conj_singleton_of_not_mem_support {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {w : Wire n} (c : DynamicCircuit Var n) (hc : w ∉ c.support)
    (V : Unitary (2 ^ 1)) (Θ : CQAssertionCompat Var (2 ^ n)) (σ : Store Var) : (wp c.compile
    (wpQAssignCompat ((QRegister.singleton w).embedUnitary V) Θ) σ).1 =
    ((wp c.compile Θ σ).1).conj ((QRegister.singleton w).embedUnitary V).1ᴴ := by
  induction c generalizing Θ σ with
  | circuit d =>
      have hcomm := circuit_eval_comm_singleton_of_not_mem_support d hc V.1
      ext1
      simp only [DynamicCircuit.compile_circuit, wp_circuit_compile_compat, wpQAssignCompat,
        qAssignObsMap, Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
        HermitianMat.conj_apply_mat, conjTranspose_conjTranspose, QRegister.embedUnitary_val]
      have hcomm_adj : ((QRegister.singleton w).embedMatrix V.1)ᴴ * d.eval.1ᴴ =
          d.eval.1ᴴ * ((QRegister.singleton w).embedMatrix V.1)ᴴ := by
        simpa [conjTranspose_mul] using congrArg conjTranspose hcomm
      exact sandwich_comm hcomm_adj.symm hcomm.symm
  | measure x r =>
      have hdisj : (QRegister.singleton w).DisjointWires r :=
        QRegister.disjoint_iff.mpr fun _ j ↦ r.ne_apply_of_not_mem_image w hc j
      simp only [DynamicCircuit.compile_measure, QProg.measureRegister, wp_qMeasure_apply,
        qMeasure_obs_map_coe, CQAssertionCompat.subst_apply, map_sum]
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      ext1
      have hc1 :=
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (QRegister.singleton w))
        r hdisj V.1 o
      have hc2 :=
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (QRegister.singleton w))
        r hdisj (V.1ᴴ) o
      rw [QRegister.embedMatrix_conjTranspose] at hc2
      simp only [qMeasure_outcome_herm_eq_conj]
      try simp only [CompleteMeasurement.toMeasurement_coe]
      simp only [QRegister.computationalBasisMeasurement_apply,
        QRegister.basisOutcomeProjector_conjTranspose, wpQAssignCompat, qAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
        HermitianMat.conj_apply_mat, conjTranspose_conjTranspose, QRegister.embedUnitary_val]
      exact sandwich_comm hc2.symm hc1
  | qIf cond t f iht ihf =>
      simp only [DynamicCircuit.support_qIf, Finset.mem_union, not_or] at hc
      simp only [DynamicCircuit.compile_qIf, wp_qIf]
      split_ifs
      · exact iht hc.1 Θ σ
      · exact ihf hc.2 Θ σ
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or] at hc
      simp only [DynamicCircuit.compile_seq, wp_qSeq]
      have h₂ : wp p₂.compile (wpQAssignCompat ((QRegister.singleton w).embedUnitary V) Θ) =
          wpQAssignCompat ((QRegister.singleton w).embedUnitary V) (wp p₂.compile Θ) := by
        funext τ; ext1
        simpa [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
          Matrix.star_eq_conjTranspose] using ih₂ hc.2 Θ τ
      rw [h₂]; exact ih₁ hc.1 (wp p₂.compile Θ) σ

theorem realizesCleanUnitary_drop_anc {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (w : Wire n) (P_base : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hP : P_baseᴴ = P_base) (hCommP : ∀ A : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ,
    (QRegister.singleton w).embedMatrix A * P_base = P_base * (QRegister.singleton
    w).embedMatrix A) (c : DynamicCircuit Var n) (hc : w ∉ c.support) (U : Unitary (2 ^ n))
    (hCommU : ∀ A : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ, U.1 * (QRegister.singleton
    w).embedMatrix A = (QRegister.singleton w).embedMatrix A * U.1) (hReal :
    RealizesCleanUnitary v (P_base * (QRegister.singleton w).basisOutcomeProjector 0) c U) :
    RealizesCleanUnitary v P_base c U := by
  let r := QRegister.singleton w
  have hb0 : r.basisOutcomeProjector 0 = r.embedMatrix (matUnit2 0 0) :=
    singleton_basisOutcomeProjector_zero_eq_matUnit2 w
  have hcP_0 : r.basisOutcomeProjector 0 * P_base = P_base * r.basisOutcomeProjector 0 := by
    rw [hb0]; exact hCommP (matUnit2 0 0)
  refine ⟨hReal.1, fun Θ hΘ σ ↦ ?_⟩
  ext1; rw [← sub_eq_zero]
  let D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    (((wp c.compile Θ σ).1).conj P_base).mat - (((wpQAssignCompat U Θ σ).1).conj P_base).mat
  refine embed_eq_zero_of_four_proj w D (fun V ↦ ?_)
  let W := r.embedUnitary V
  have hΘW : ∀ τ val, wpQAssignCompat W Θ (Function.update τ v val) = wpQAssignCompat W Θ τ := by
    intro τ val; simp [wpQAssignCompat, hΘ τ val]
  have hEqW := congrArg HermitianMat.mat (hReal.2 (wpQAssignCompat W Θ) hΘW σ)
  have hUq : (wpQAssignCompat U (wpQAssignCompat W Θ) σ).1 =
      ((wpQAssignCompat U Θ σ).1).conj W.1ᴴ := by
    ext1
    have hcU : U.1 * W.1 = W.1 * U.1 := hCommU V.1
    have hcU_adj : W.1ᴴ * U.1ᴴ = U.1ᴴ * W.1ᴴ := by
      simpa [conjTranspose_mul] using congrArg conjTranspose hcU
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, conjTranspose_conjTranspose]
    exact sandwich_comm hcU_adj.symm hcU.symm
  rw [wp_conj_singleton_of_not_mem_support c hc V Θ σ, hUq] at hEqW
  change (((((wp c.compile Θ σ).1).conj W.1ᴴ).conj (P_base * r.basisOutcomeProjector 0)).mat =
    ((((wpQAssignCompat U Θ σ).1).conj W.1ᴴ).conj (P_base * r.basisOutcomeProjector 0)).mat) at hEqW
  simp only [HermitianMat.conj_apply_mat, conjTranspose_mul, hP,
    QRegister.basisOutcomeProjector_conjTranspose, conjTranspose_conjTranspose] at hEqW
  have hSwap : ∀ M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      (P_base * r.basisOutcomeProjector 0) * M * (r.basisOutcomeProjector 0 * P_base) =
        (r.basisOutcomeProjector 0 * P_base) * M * (P_base * r.basisOutcomeProjector 0) :=
    fun M ↦ congrArg₂ (· * ·) (congrArg (· * M) hcP_0.symm) hcP_0
  rw [hSwap, hSwap] at hEqW
  have hSub0 : (r.basisOutcomeProjector 0 * P_base) * (W.1ᴴ * ((wp c.compile Θ σ).1.mat -
      (wpQAssignCompat U Θ σ).1.mat) * W.1) * (P_base * r.basisOutcomeProjector 0) = 0 := by
    simpa only [mul_sub, sub_mul] using sub_eq_zero.mpr hEqW
  have hcP_V : W.1 * P_base = P_base * W.1 := hCommP V.1
  have hcP_Vadj : P_base * W.1ᴴ = W.1ᴴ * P_base := by
    have h := hCommP (V.1ᴴ); rw [r.embedMatrix_conjTranspose] at h; exact h.symm
  have hD_def :
      D = P_base * ((wp c.compile Θ σ).1.mat - (wpQAssignCompat U Θ σ).1.mat) * P_base := by
    simp only [D, HermitianMat.conj_apply_mat, hP, mul_sub, sub_mul]
  have hL : W.1 * (r.basisOutcomeProjector 0 * W.1ᴴ) =
      r.embedMatrix (V.1 * matUnit2 0 0 * V.1ᴴ) := by
    dsimp [W]
    rw [hb0, ← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul,
      ← r.embedMatrix_mul, Matrix.mul_assoc]
  calc r.embedMatrix (V.1 * matUnit2 0 0 * V.1ᴴ) * D *
          r.embedMatrix (V.1 * matUnit2 0 0 * V.1ᴴ)
      = W.1 * (r.basisOutcomeProjector 0 *
          (W.1ᴴ * (P_base * ((wp c.compile Θ σ).1.mat -
            (wpQAssignCompat U Θ σ).1.mat) * P_base) * W.1) *
          r.basisOutcomeProjector 0) * W.1ᴴ := by
        rw [← hL, hD_def]
        simp only [Matrix.mul_assoc]
    _ = W.1 * ((r.basisOutcomeProjector 0 * P_base) *
          (W.1ᴴ * ((wp c.compile Θ σ).1.mat - (wpQAssignCompat U Θ σ).1.mat) * W.1) *
          (P_base * r.basisOutcomeProjector 0)) * W.1ᴴ := by
        rw [← sandwich_comm hcP_Vadj hcP_V]
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hSub0, mul_zero, zero_mul]

/-- Joint computational-basis projector onto `[base .. m)` clean ancillas and `Inv` on `rComb`. -/
noncomputable def p57RangeDiagProj {M n : ℕ} (rComb : QRegister M n) (base m : ℕ)
    (Inv : BitAssignment M → Prop) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  p57DiagProj rComb fun γ ↦ (∀ w : Wire M, base ≤ w.val → w.val < m → γ w = 0) ∧ Inv γ

theorem p57RangeDiagProj_eq_clean {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    (base : ℕ) (hbase : base ≤ M) (hrem : M - base ≤ M) (Inv : BitAssignment M → Prop) :
    p57RangeDiagProj rComb base M Inv = p57CleanDiagProj rComb (M - base) hrem Inv := by
  apply matrix_ext_ket; intro β
  rw [p57RangeDiagProj, ket_p57DiagProj, ket_p57CleanDiagProj]
  have hiff : (∀ w : Wire M, base ≤ w.val → w.val < M → β (rComb w) = 0) ↔
      cleanRem M (M - base) (fun idx ↦ β (rComb idx)) :=
    ⟨fun H w hw ↦ H w (by omega) w.isLt, fun H w hw _ ↦ H w (by omega)⟩
  by_cases hI : cleanRem M (M - base) (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx))
  · rw [ite_eq_left hI, ite_eq_left ⟨hiff.mpr hI.1, hI.2⟩]
  · rw [ite_eq_right hI, ite_eq_right (fun h' ↦ hI ⟨hiff.mp h'.1, h'.2⟩)]

theorem p57RangeDiagProj_succ {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n) (base m : ℕ)
    (hbm : base ≤ m) (hm : m < M) (Inv : BitAssignment M → Prop) : p57RangeDiagProj rComb base
    (m + 1) Inv = p57RangeDiagProj rComb base m Inv *
    (QRegister.singleton (rComb ⟨m, hm⟩)).basisOutcomeProjector 0 := by
  apply matrix_ext_ket; intro β
  rw [p57RangeDiagProj, p57RangeDiagProj, mul_mulVec_prog, ket_projector_zero]
  by_cases h0 : β (rComb ⟨m, hm⟩) = 0
  · rw [ite_eq_left h0, ket_p57DiagProj, ket_p57DiagProj]
    have hiff : (∀ w : Wire M, base ≤ w.val → w.val < m + 1 → β (rComb w) = 0) ↔
        (∀ w : Wire M, base ≤ w.val → w.val < m → β (rComb w) = 0) :=
      ⟨fun H w hw1 hw2 ↦ H w hw1 (by omega), fun H w hw1 hw2 ↦ by
        by_cases heq : w.val = m
        · exact (congrArg (fun u ↦ β (rComb u)) (Fin.ext heq)).trans h0
        · exact H w hw1 (by omega)⟩
    by_cases hI : (∀ w : Wire M, base ≤ w.val → w.val < m → β (rComb w) = 0) ∧
        Inv (fun idx ↦ β (rComb idx))
    · rw [ite_eq_left hI, ite_eq_left ⟨hiff.mpr hI.1, hI.2⟩]
    · rw [ite_eq_right hI, ite_eq_right (fun h' ↦ hI ⟨hiff.mp h'.1, h'.2⟩)]
  · rw [ite_eq_right h0, Matrix.mulVec_zero, ket_p57DiagProj, ite_eq_right]
    rintro ⟨H, _⟩
    exact h0 (H ⟨m, hm⟩ hbm (by dsimp; omega))

theorem mat2_decomp (A : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) : ∃ c00 c01 c10 c11 : ℂ, A =
    c00 • matUnit2 0 0 + c01 • (matUnit2 0 0 * flip2Unitary.1) + c10 •
    (flip2Unitary.1 * matUnit2 0 0) + c11 • (flip2Unitary.1 * matUnit2 0 0 * flip2Unitary.1)
    := by
  refine ⟨A 0 0, A 0 1, A 1 0, A 1 1, ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matUnit2, flip2Unitary, Matrix.mul_apply, Fin.sum_univ_two]

theorem comm_mul_of_comm {K : Type} [Semiring K] {X Y P : K} (hX : X * P = P * X)
    (hY : Y * P = P * Y) : (X * Y) * P = P * (X * Y) := by
  rw [mul_assoc, hY, ← mul_assoc, hX, mul_assoc]

theorem embedMatrix_comm_p57DiagProj {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    (u : Wire M) (Pred : BitAssignment M → Prop) (hPred : ∀ γ₁ γ₂ : BitAssignment M, (∀ w :
    Wire M, w ≠ u → γ₁ w = γ₂ w) → (Pred γ₁ ↔ Pred γ₂))
    (A : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) : (QRegister.singleton (rComb u)).embedMatrix A
    * p57DiagProj rComb Pred = p57DiagProj rComb Pred *
    (QRegister.singleton (rComb u)).embedMatrix A := by
  let r := QRegister.singleton (rComb u)
  let P := p57DiagProj rComb Pred
  change r.embedMatrix A * P = P * r.embedMatrix A
  have hc0 : r.embedMatrix (matUnit2 0 0) * P = P * r.embedMatrix (matUnit2 0 0) := by
    rw [← singleton_basisOutcomeProjector_zero_eq_matUnit2 (rComb u)]
    exact p57BasisProj_comm_diag rComb Pred (rComb u)
  have hcX : r.embedMatrix flip2Unitary.1 * P = P * r.embedMatrix flip2Unitary.1 := by
    have hX : r.embedMatrix flip2Unitary.1 = (Circuit.X (rComb u)).eval.1 := by
      rw [Circuit.eval_single, QRegister.embedUnitary_val]
      congr 1; ext i j; fin_cases i <;> fin_cases j <;>
        simp [flip2Unitary, PrimitiveGate.eval, Qubit.X]
    apply matrix_ext_ket; intro β
    rw [hX, mul_mulVec_prog, mul_mulVec_prog, ket_p57DiagProj, ket_X, ket_p57DiagProj]
    have hIff : Pred (fun idx ↦ Function.update β (rComb u) (β (rComb u) + 1) (rComb idx)) ↔
        Pred (fun idx ↦ β (rComb idx)) :=
      hPred _ _ fun w hwu ↦ Function.update_of_ne (fun heq ↦ hwu (rComb.wires.injective heq)) _ _
    by_cases hP : Pred (fun idx ↦ β (rComb idx))
    · rw [ite_eq_left hP, ket_X, ite_eq_left (hIff.mpr hP)]
    · rw [ite_eq_right hP, Matrix.mulVec_zero, ite_eq_right (fun h' ↦ hP (hIff.mp h'))]
  obtain ⟨c00, c01, c10, c11, rfl⟩ := mat2_decomp A
  simp only [QRegister.embedMatrix_add, QRegister.embedMatrix_smul, QRegister.embedMatrix_mul,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [hc0, comm_mul_of_comm hc0 hcX, comm_mul_of_comm hcX hc0,
    comm_mul_of_comm (comm_mul_of_comm hcX hc0) hcX]

theorem realizesCleanUnitary_drop_range {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (base m k : ℕ) (hbm : base ≤ m)
    (hmk : m + k ≤ M) (Inv : BitAssignment M → Prop) (hInv : ∀ u : Wire M, m ≤ u.val → ∀ γ₁ γ₂
    : BitAssignment M, (∀ w : Wire M, w ≠ u → γ₁ w = γ₂ w) → (Inv γ₁ ↔ Inv γ₂))
    (c : DynamicCircuit Var n) (hc : ∀ u : Wire M, m ≤ u.val → rComb u ∉ c.support)
    (d_spec : Circuit n) (hd : ∀ u : Wire M, m ≤ u.val → rComb u ∉ d_spec.support) (hReal :
    RealizesCleanUnitary v (p57RangeDiagProj rComb base (m + k) Inv) c d_spec.eval) :
    RealizesCleanUnitary v (p57RangeDiagProj rComb base m Inv) c d_spec.eval := by
  induction k with
  | zero => simpa using hReal
  | succ k ih =>
      let u : Wire M := ⟨m + k, by omega⟩
      have hPred : ∀ γ₁ γ₂ : BitAssignment M, (∀ w : Wire M, w ≠ u → γ₁ w = γ₂ w) →
          (((∀ w : Wire M, base ≤ w.val → w.val < m + k → γ₁ w = 0) ∧ Inv γ₁) ↔
            ((∀ w : Wire M, base ≤ w.val → w.val < m + k → γ₂ w = 0) ∧ Inv γ₂)) :=
        fun γ₁ γ₂ hne ↦ and_congr
          ⟨fun H w hw1 hw2 ↦ (hne w (fun heq ↦ by subst heq; dsimp [u] at hw2; omega)).symm.trans
            (H w hw1 hw2),
           fun H w hw1 hw2 ↦ (hne w (fun heq ↦ by subst heq; dsimp [u] at hw2; omega)).trans
            (H w hw1 hw2)⟩
          (hInv u (by dsimp [u]; omega) γ₁ γ₂ hne)
      have hStep : RealizesCleanUnitary v (p57RangeDiagProj rComb base (m + k) Inv) c d_spec.eval :=
        realizesCleanUnitary_drop_anc v (rComb u) (p57RangeDiagProj rComb base (m + k) Inv)
          (p57DiagProj_conjTranspose _ _)
          (embedMatrix_comm_p57DiagProj rComb u _ hPred)
          c (hc u (by dsimp [u]; omega))
          d_spec.eval
          (circuit_eval_comm_singleton_of_not_mem_support d_spec (hd u (by dsimp [u]; omega)))
          (by rwa [← p57RangeDiagProj_succ rComb base (m + k) (by omega) (by omega) Inv])
      exact ih (by omega) hStep

theorem realizesCleanUnitary_drop_tail {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (base M_stage : ℕ)
    (hbm : base ≤ M_stage) (hmM : M_stage ≤ M) (Inv : BitAssignment M → Prop) (hInv : ∀ u :
    Wire M, M_stage ≤ u.val → ∀ γ₁ γ₂ : BitAssignment M, (∀ w : Wire M, w ≠ u → γ₁ w = γ₂ w) →
    (Inv γ₁ ↔ Inv γ₂)) (c : DynamicCircuit Var n)
    (hc : ∀ u : Wire M, M_stage ≤ u.val → rComb u ∉ c.support) (d_spec : Circuit n)
    (hd : ∀ u : Wire M, M_stage ≤ u.val → rComb u ∉ d_spec.support) (hReal :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (M - base) (by omega) Inv) c d_spec.eval) :
    RealizesCleanUnitary v (p57RangeDiagProj rComb base M_stage Inv) c d_spec.eval := by
  have hEq : M_stage + (M - M_stage) = M := by omega
  refine realizesCleanUnitary_drop_range v rComb base M_stage (M - M_stage) hbm (by omega)
    Inv hInv c hc d_spec hd ?_
  rw [hEq, p57RangeDiagProj_eq_clean rComb base (by omega) (by omega) Inv]
  exact hReal

/- ### Section 3B.2: Stage-Scoped `StepBundleW` Combinators & Clean-Workspace Extraction -/

/-- Parameterized `topW` deterministic stage bundle on `rCombBase : QRegister 437 n`. -/
structure StepBundleW (topW : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCombBase : QRegister 437 n)
    (δ_in δ_out : BitAssignment 149 → BitAssignment 437)
    (sgn : BitAssignment 149 → ZMod 2)
    (d : DynamicCircuit Var n) : Prop where
  h275 : 275 ≤ topW
  hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α)
  store : PreservesStoreConst d
  exists_u : ∃ U : Unitary (2 ^ n),
    RealizesCleanUnitary v (baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_in α)) d U ∧
    (∀ (β : BitAssignment n) (α : BitAssignment 149),
      zeroTopW topW (fun idx ↦ β (rCombBase idx)) = δ_in α →
      U.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (sgn α).val) •
          ket (writeRegProg β rCombBase (liftTopW topW (δ_out α) (fun idx ↦ β (rCombBase idx))))) ∧
    baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_out α) *
      (U.1 * baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_in α)) =
      U.1 * baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_in α)

theorem StepBundleW.seq {topW : ℕ} {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rCombBase : QRegister 437 n}
    {δ_A δ_B δ_C : BitAssignment 149 → BitAssignment 437}
    {sgn1 sgn2 sgn12 : BitAssignment 149 → ZMod 2} {d1 d2 : DynamicCircuit Var n}
    (h1 : StepBundleW topW v rCombBase δ_A δ_B sgn1 d1)
    (h2 : StepBundleW topW v rCombBase δ_B δ_C sgn2 d2) (hsgn : ∀ α, ((-1 : ℂ) ^ (sgn1 α).val)
    * ((-1 : ℂ) ^ (sgn2 α).val) = ((-1 : ℂ) ^ (sgn12 α).val)) : StepBundleW topW v rCombBase
    δ_A δ_C sgn12 (.seq d1 d2) := by
  obtain ⟨U1, hR1, hM1, hC1⟩ := h1.exists_u
  obtain ⟨U2, hR2, hM2, hC2⟩ := h2.exists_u
  refine ⟨h1.h275, h2.hcl_out, PreservesStoreConst.seq h1.store h2.store, ⟨U2 * U1, ?_, ?_, ?_⟩⟩
  · exact RealizesCleanUnitary_seq_asym (baseDiagProjW_conjTranspose topW rCombBase _)
      (baseDiagProjW_conjTranspose topW rCombBase _) hR1 hR2 hC1
  · intro β α htop
    rw [Submonoid.coe_mul, mul_mulVec_prog, hM1 β α htop, Matrix.mulVec_smul]
    let β' := writeRegProg β rCombBase (liftTopW topW (δ_B α) (fun idx ↦ β (rCombBase idx)))
    have hβ'_reg : (fun idx ↦ β' (rCombBase idx)) = liftTopW topW (δ_B α)
        (fun idx ↦ β (rCombBase idx)) := funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
    have htop' : zeroTopW topW (fun idx ↦ β' (rCombBase idx)) = δ_B α := by
      rw [hβ'_reg, zeroTopW_liftTopW h1.h275 _ (h1.hcl_out α)]
    rw [hM2 β' α htop', smul_smul, hsgn α]
    dsimp only [β']
    rw [hβ'_reg, liftTopW_idem, writeRegProg_idem_437]
  · calc baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_C α) *
          ((U2 * U1).1 * baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_A α))
        = baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_C α) *
          (U2.1 * (baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_B α) *
            (U1.1 * baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_A α)))) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]; rw [hC1]
      _ = (baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_C α) *
            (U2.1 * baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_B α))) *
          (U1.1 * baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_A α)) := by
            simp only [Matrix.mul_assoc]
      _ = (U2 * U1).1 * baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_A α) := by
            rw [hC2]; simp only [Matrix.mul_assoc]; rw [hC1]
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]

theorem StepBundleW.seq_zero_left {topW : ℕ} {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {v : Var} {rCombBase : QRegister 437 n}
    {δ_A δ_B δ_C : BitAssignment 149 → BitAssignment 437} {sgn2 : BitAssignment 149 → ZMod 2}
    {d1 d2 : DynamicCircuit Var n} (h1 : StepBundleW topW v rCombBase δ_A δ_B (fun _ ↦ 0) d1)
    (h2 : StepBundleW topW v rCombBase δ_B δ_C sgn2 d2) : StepBundleW topW v rCombBase δ_A δ_C
    sgn2 (.seq d1 d2) :=
  h1.seq h2 (fun _ ↦ by simp)

theorem StepBundleW.seq_zero_right {topW : ℕ} {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {v : Var} {rCombBase : QRegister 437 n}
    {δ_A δ_B δ_C : BitAssignment 149 → BitAssignment 437} {sgn1 : BitAssignment 149 → ZMod 2}
    {d1 d2 : DynamicCircuit Var n} (h1 : StepBundleW topW v rCombBase δ_A δ_B sgn1 d1)
    (h2 : StepBundleW topW v rCombBase δ_B δ_C (fun _ ↦ 0) d2) : StepBundleW topW v rCombBase
    δ_A δ_C sgn1 (.seq d1 d2) :=
  h1.seq h2 (fun _ ↦ by simp)

theorem stepBundleW_of_relayWM_dyn {topW M_stage : ℕ} {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rCombBase : QRegister 437 n)
    {swapX : Wire 437 → Wire 437} {isBadX : Wire 437 → Bool}
    (hsr : ValidSwapRelayWM topW M_stage swapX isBadX)
    (δ_in δ_out : BitAssignment 149 → BitAssignment 437) (sgn : BitAssignment 149 → ZMod 2)
    (p : TempPhaseProg 437) (d : DynamicCircuit Var n) (hPres : PreservesStoreConst d)
    (InvX : BitAssignment 437 → Prop) (hRealRange : RealizesCleanUnitary v (p57RangeDiagProj
    (rCombBase.compose (permReg (permOfInvol swapX hsr.invol))) 275 M_stage InvX) d
    (((p.onRegister (rCombBase.compose (permReg (permOfInvol swapX
    hsr.invol)))).toToffCircuit).eval))
    (hpBad : progDisjointBad (isBadXM M_stage isBadX) p = true) (hIn : ∀ α, cleanRem 437 (437
    - 275) (δ_in α) ∧ (∀ w, isBadX w = true → δ_in α w = 0))
    (hOut_eq : ∀ α, δ_out α = p.evalBits (δ_in α))
    (hSgn_eq : ∀ α, p.evalSign (δ_in α) = sgn α) (hOut : ∀ α, cleanRem 437 (437 - 275) (δ_out
    α) ∧ (∀ w, isBadX w = true → δ_out α w = 0)) (hInvX : ∀ (γ : BitAssignment 437) (α :
    BitAssignment 149), (∀ w : Wire 437, 275 ≤ w.val → w.val < M_stage → γ (swapX w) = 0) → (∀
    w, isBadXM M_stage isBadX w = false → γ (swapX w) = δ_in α w) → InvX (fun w ↦ γ (swapX
    w))) : StepBundleW topW v rCombBase δ_in δ_out sgn d := by
  let rCombX := rCombBase.compose (permReg (permOfInvol swapX hsr.invol))
  let P_in := baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_in α)
  let P_out := baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_out α)
  let U := (((p.onRegister rCombX).toToffCircuit).eval)
  have hSub : p57RangeDiagProj rCombX 275 M_stage InvX * P_in = P_in := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, ket_baseDiagProjW]
    by_cases hP : (∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β (rCombBase w) = 0) ∧
        ∃ α, zeroTopW topW (fun idx ↦ β (rCombBase idx)) = δ_in α
    · rw [ite_eq_left hP, p57RangeDiagProj, ket_p57DiagProj]
      obtain ⟨_, α, htop⟩ := hP
      obtain ⟨hEq, hcl⟩ := relayWM_assign_props hsr htop (hIn α).1 (hIn α).2
      have hreg : (fun idx ↦ β (rCombX idx)) = fun w ↦ β (rCombBase (swapX w)) := rfl
      rw [hreg]
      exact ite_eq_left ⟨hcl, hInvX (fun idx ↦ β (rCombBase idx)) α hcl hEq⟩
    · rw [ite_eq_right hP, Matrix.mulVec_zero]
  have hReal : RealizesCleanUnitary v P_in d U := RealizesCleanUnitary.mono_proj
      (p57DiagProj_conjTranspose rCombX _) (baseDiagProjW_conjTranspose topW rCombBase _) hSub
      hRealRange
  have hMulVec : ∀ (β : BitAssignment n) (α : BitAssignment 149), zeroTopW topW
      (fun idx ↦ β (rCombBase idx)) = δ_in α → U.1.mulVec (ket β) = ((-1 : ℂ) ^ (sgn α).val) •
      ket (writeRegProg β rCombBase (liftTopW topW (δ_out α) (fun idx ↦ β (rCombBase idx))))
      := by
    intro β α htop
    let γ : BitAssignment 437 := fun idx ↦ β (rCombBase idx)
    obtain ⟨hEq, _⟩ := relayWM_assign_props hsr htop (hIn α).1 (hIn α).2
    obtain ⟨hsgn, hBitsEq, hBitsBad⟩ :=
      progDisjointBad_eval (isBadXM M_stage isBadX) p hpBad (fun w ↦ γ (swapX w)) (δ_in α) hEq
    have hBitsEq' : ∀ w, isBadXM M_stage isBadX w = false → p.evalBits (fun w ↦ γ (swapX w)) w
        = δ_out α w := fun w hw ↦ (hBitsEq w hw).trans (congrFun (hOut_eq α).symm w)
    have hreg : (fun idx ↦ β (rCombX idx)) = fun w ↦ γ (swapX w) := rfl
    dsimp only [U]
    rw [eval_onRegister_prog_ket, hreg, hsgn, hSgn_eq α,
      writeRegProg_compose_perm β rCombBase (permOfInvol swapX hsr.invol)]
    have hsymm : (fun idx ↦ p.evalBits (fun w ↦ γ (swapX w)) ((permOfInvol swapX
        hsr.invol).symm idx)) = fun idx ↦ p.evalBits (fun w ↦ γ (swapX w)) (swapX idx) := rfl
    rw [hsymm, relayWM_unswap_eq_liftTopW hsr (hOut α).1 (hOut α).2 hBitsEq' hBitsBad]
  refine ⟨hsr.h275, fun α ↦ (hOut α).1, hPres, ⟨U, hReal, hMulVec, ?_⟩⟩
  apply matrix_ext_ket; intro β
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_baseDiagProjW]
  by_cases hP : (∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β (rCombBase w) = 0) ∧
      ∃ α, zeroTopW topW (fun idx ↦ β (rCombBase idx)) = δ_in α
  · rw [ite_eq_left hP]
    obtain ⟨_, α, htop⟩ := hP
    rw [hMulVec β α htop, Matrix.mulVec_smul, ket_baseDiagProjW]
    let β' := writeRegProg β rCombBase (liftTopW topW (δ_out α) (fun idx ↦ β (rCombBase idx)))
    have hβ'_reg : (fun idx ↦ β' (rCombBase idx)) = liftTopW topW (δ_out α)
        (fun idx ↦ β (rCombBase idx)) := funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
    have hscr' : ∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β' (rCombBase w) = 0 :=
      fun w hw1 hw2 ↦ by
        change (fun idx ↦ β' (rCombBase idx)) w = 0
        rw [hβ'_reg, liftTopW_lt hw2]
        exact (hOut α).1 w hw1
    have htop' : ∃ α', zeroTopW topW (fun idx ↦ β' (rCombBase idx)) = δ_out α' :=
      ⟨α, by rw [hβ'_reg, zeroTopW_liftTopW hsr.h275 _ (hOut α).1]⟩
    rw [ite_eq_left ⟨hscr', htop'⟩]
  · rw [ite_eq_right hP, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem stepBundleW_of_relayWM_static {topW M_stage : ℕ}
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCombBase : QRegister 437 n)
    {swapX : Wire 437 → Wire 437} {isBadX : Wire 437 → Bool}
    (hsr : ValidSwapRelayWM topW M_stage swapX isBadX)
    (δ_in δ_out : BitAssignment 149 → BitAssignment 437)
    (sgn : BitAssignment 149 → ZMod 2)
    (p : TempPhaseProg 437)
    (hpM : progSupportsBelowB M_stage p = true)
    (hpBad : progDisjointBad (isBadXM M_stage isBadX) p = true)
    (hv : ValidCleanRem 437 (437 - 275) p)
    (hIn : ∀ α, cleanRem 437 (437 - 275) (δ_in α) ∧ (∀ w, isBadX w = true → δ_in α w = 0))
    (hOut_eq : ∀ α, δ_out α = p.evalBits (δ_in α))
    (hSgn_eq : ∀ α, p.evalSign (δ_in α) = sgn α)
    (hOut : ∀ α, cleanRem 437 (437 - 275) (δ_out α) ∧ (∀ w, isBadX w = true → δ_out α w = 0)) :
    let rCombX := rCombBase.compose (permReg (permOfInvol swapX hsr.invol))
    StepBundleW topW v rCombBase δ_in δ_out sgn ((p.onRegister rCombX).toDyn v) := by
  intro rCombX
  have h275M : 275 ≤ M_stage := le_trans hsr.h275 hsr.htopM
  let rCombXM : QRegister M_stage n :=
    rCombX.compose (QRegister.block 0 M_stage (by have := hsr.hM437; omega))
  let pM : TempPhaseProg M_stage := truncateProgB M_stage p hpM
  have hEqRem : 437 - 275 - (437 - M_stage) = M_stage - 275 := by
    have := hsr.hM437; omega
  have hvM : ValidCleanRem M_stage (M_stage - 275) pM :=
    hEqRem ▸ truncateProgB_validCleanRem hsr.hM437 p hpM (437 - 275) hv
  have hOnReg : pM.onRegister rCombXM = p.onRegister rCombX :=
    truncateProgB_onRegister_eq (by have := hsr.hM437; omega) rCombX p hpM
  have hRealM := realizes_of_validCleanRem v rCombXM pM (M_stage - 275) (by omega) hvM
  rw [hOnReg] at hRealM
  have hAbs : projZeroAll (M_stage - 275) (tailScr rCombXM (M_stage - 275) (by omega)) *
      p57RangeDiagProj rCombX 275 M_stage (fun _ ↦ True) =
      p57RangeDiagProj rCombX 275 M_stage (fun _ ↦ True) := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, p57RangeDiagProj, ket_p57DiagProj]
    by_cases hR : (∀ w : Wire 437, 275 ≤ w.val → w.val < M_stage → β (rCombX w) = 0) ∧ True
    · rw [ite_eq_left hR, ket_projZeroAll]
      refine ite_eq_left fun j ↦ ?_
      have hwire : tailScr rCombXM (M_stage - 275) (by omega) j =
          rCombX ⟨275 + j.val, by have := hsr.hM437; omega⟩ := by
        dsimp [tailScr, rCombXM, QRegister.compose_apply]
        congr 1; ext; dsimp; omega
      rw [hwire]
      exact hR.1 ⟨275 + j.val, by have := hsr.hM437; omega⟩ (by dsimp; omega) (by dsimp; omega)
    · rw [ite_eq_right hR, Matrix.mulVec_zero]
  have hRealRange := RealizesCleanUnitary.mono_proj
      (projZeroAll_conjTranspose (M_stage - 275) _) (p57DiagProj_conjTranspose rCombX _) hAbs
      hRealM
  exact stepBundleW_of_relayWM_dyn v rCombBase hsr δ_in δ_out sgn p
    ((p.onRegister rCombX).toDyn v) (PreservesStoreConst_toDyn v _) (fun _ ↦ True)
    hRealRange hpBad hIn hOut_eq hSgn_eq hOut (fun _ _ _ _ ↦ trivial)

theorem castNatReg_apply {a b n : ℕ} (h : a = b) (r : QRegister a n) (idx : Fin b) :
    castNatReg h r idx = r (Fin.cast h.symm idx) := by
  subst h; rfl

theorem StepBundleW.to_cleanWorkspace {mWB mDummy : ℕ}
    (hm : (149 + mWB) + mDummy = 437) (h275 : 275 ≤ 149 + mWB)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct149 : QRegister 149 n) (rWork : QRegister mWB n) (rDummy : QRegister mDummy n)
    (hAW : rAct149.DisjointWires rWork) (hAD : rAct149.DisjointWires rDummy)
    (hWD : rWork.DisjointWires rDummy) (uTarget : Unitary (2 ^ 149))
    (permTarget : BitAssignment 149 → BitAssignment 149)
    (phaseTarget : BitAssignment 149 → ZMod 2)
    (huTarget : ∀ α : BitAssignment 149,
      uTarget.1 *ᵥ ket α = ((-1 : ℂ) ^ (phaseTarget α).val) • ket (permTarget α))
    (d : DynamicCircuit Var n)
    (hBundle : StepBundleW (149 + mWB) v
      (castNatReg hm ((rAct149.concat rWork hAW).concat rDummy (disjConcatLeft hAD hWD)))
      (fun α ↦ padZeroBits (mClean := 288) α)
      (fun α ↦ padZeroBits (mClean := 288) (permTarget α)) phaseTarget d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct149 rWork uTarget d := by
  let topW := 149 + mWB
  let rCombBase : QRegister 437 n :=
    castNatReg hm ((rAct149.concat rWork hAW).concat rDummy (disjConcatLeft hAD hWD))
  obtain ⟨U, hR, hM, _⟩ := hBundle.exists_u
  let P_0 := baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = padZeroBits (mClean := 288) α)
  let P_work := projZeroAll mWB rWork.wires
  have hPw : P_workᴴ = P_work := projZeroAll_conjTranspose mWB _
  have hBaseAct (i : Fin 149) : rCombBase ⟨i.val, by omega⟩ = rAct149 i := by
    simp only [rCombBase, castNatReg_apply, show Fin.cast hm.symm ⟨i.val, by omega⟩ =
      Fin.castAdd mDummy (Fin.castAdd mWB i) from Fin.ext rfl, QRegister.concat_apply_left]
  have hBaseWork (j : Fin mWB) : rCombBase ⟨149 + j.val, by omega⟩ = rWork j := by
    simp only [rCombBase, castNatReg_apply, show Fin.cast hm.symm ⟨149 + j.val, by omega⟩ =
      Fin.castAdd mDummy (Fin.natAdd 149 j) from Fin.ext rfl,
      QRegister.concat_apply_left, QRegister.concat_apply_right]
  have hBaseDummy (k : Fin mDummy) : rCombBase ⟨(149 + mWB) + k.val, by omega⟩ = rDummy k := by
    simp only [rCombBase, castNatReg_apply,
      show Fin.cast hm.symm ⟨(149 + mWB) + k.val, by omega⟩ = Fin.natAdd (149 + mWB) k from
        Fin.ext rfl, QRegister.concat_apply_right]
  have hTopOfWork : ∀ (β : BitAssignment n), (∀ j : Fin mWB, β (rWork j) = 0) →
      (∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β (rCombBase w) = 0) ∧
        zeroTopW topW (fun idx ↦ β (rCombBase idx)) =
          padZeroBits (mClean := 288) (fun i ↦ β (rAct149 i)) := fun β hw ↦ by
    have hwork0 : ∀ w : Wire 437, 149 ≤ w.val → w.val < topW → β (rCombBase w) = 0 :=
      fun w hw1 hw2 ↦ by
        rw [show w = ⟨149 + (⟨w.val - 149, by omega⟩ : Fin mWB).val, by omega⟩ from
          Fin.ext (by dsimp; omega), hBaseWork ⟨w.val - 149, by omega⟩, hw _]
    refine ⟨fun w hw1 hw2 ↦ hwork0 w (by omega) hw2, funext fun w ↦ ?_⟩
    by_cases hw149 : w.val < 149
    · let i : Fin 149 := ⟨w.val, hw149⟩
      rw [zeroTopW_lt (by omega), padZeroBits_ltAux (mClean := 288) _ w hw149]
      change β (rCombBase w) = β (rAct149 i)
      rw [show w = ⟨i.val, by omega⟩ from Fin.ext rfl, hBaseAct i]
    · by_cases hwTop : w.val < topW
      · rw [zeroTopW_lt hwTop, hwork0 w (by omega) hwTop, padZeroBits149_clean _ w (by omega)]
      · rw [zeroTopW_ge (by omega), padZeroBits149_clean _ w (by omega)]
  have hSub : P_0 * P_work = P_work := by
    apply matrix_ext_ket; intro β
    simp only [P_0, P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ j : Fin mWB, β (rWork j) = 0
    · simp only [hw, imp_true_iff, ↓reduceIte, ket_baseDiagProjW]
      obtain ⟨hscr, htop⟩ := hTopOfWork β hw; exact ite_eq_left ⟨hscr, ⟨_, htop⟩⟩
    · simp only [hw, ↓reduceIte, Matrix.mulVec_zero]
  have hUeq : U.1 * P_work = (rAct149.embedUnitary uTarget).1 * P_work := by
    apply matrix_ext_ket; intro β
    simp only [P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ j : Fin mWB, β (rWork j) = 0
    · simp only [hw, imp_true_iff, ↓reduceIte]
      let α : BitAssignment 149 := fun i ↦ β (rAct149 i)
      rw [hM β α (hTopOfWork β hw).2]
      have hwComb : writeRegProg β rCombBase
          (liftTopW topW (padZeroBits (mClean := 288) (permTarget α))
            (fun idx ↦ β (rCombBase idx))) = writeRegProg β rAct149 (permTarget α) := by
        funext w
        by_cases hmem : w ∈ Set.range rCombBase.wires
        · obtain ⟨idx, rfl⟩ := hmem
          rw [writeRegProg_apply_reg]
          by_cases h149 : idx.val < 149
          · let i : Fin 149 := ⟨idx.val, h149⟩
            rw [liftTopW_lt (by omega), padZeroBits_ltAux (mClean := 288) (permTarget α) idx h149]
            change permTarget α i = writeRegProg β rAct149 (permTarget α) (rCombBase idx)
            rw [show idx = ⟨i.val, by omega⟩ from Fin.ext rfl,
              hBaseAct i, writeRegProg_apply_reg]
          · by_cases hTop : idx.val < topW
            · let j : Fin mWB := ⟨idx.val - 149, by omega⟩
              have hnotAct : rWork j ∉ Set.range rAct149.wires := fun ⟨i, hi⟩ ↦ hAW.ne i j hi
              rw [liftTopW_lt hTop, padZeroBits149_clean _ idx (by omega),
                show idx = ⟨149 + j.val, by omega⟩ from Fin.ext (by dsimp [j]; omega),
                hBaseWork j, writeRegProg_apply_of_not_mem _ _ _ _ hnotAct, hw j]
            · let k : Fin mDummy := ⟨idx.val - topW, by omega⟩
              have hnotAct : rDummy k ∉ Set.range rAct149.wires := fun ⟨i, hi⟩ ↦ hAD.ne i k hi
              rw [liftTopW_ge (by omega),
                show idx = ⟨(149 + mWB) + k.val, by omega⟩ from Fin.ext (by dsimp [k, topW]; omega),
                hBaseDummy k, writeRegProg_apply_of_not_mem _ _ _ _ hnotAct]
        · have hnotAct : w ∉ Set.range rAct149.wires :=
            fun ⟨i, hi⟩ ↦ hmem ⟨⟨i.val, by omega⟩, (hBaseAct i).trans hi⟩
          rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem,
            writeRegProg_apply_of_not_mem _ _ _ _ hnotAct]
      rw [hwComb, QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog,
        show localIdxProg rAct149 β = (basisBitsEquiv 149).symm α from rfl]
      have hEvalAct : ∀ l : Fin (2 ^ 149),
          uTarget.1 l ((basisBitsEquiv 149).symm α) =
            if l = (basisBitsEquiv 149).symm (permTarget α) then
              ((-1 : ℂ) ^ (phaseTarget α).val) else 0 := fun l ↦ by
        simpa [ket, basisState, Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using
          congrFun (huTarget α) l
      simp_rw [hEvalAct, ite_smul, zero_smul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [show basisBits 149 ((basisBitsEquiv 149).symm (permTarget α)) = permTarget α from
        (basisBitsEquiv 149).apply_symm_apply _]
    · simp [hw]
  have hTarget := RealizesCleanUnitary.congr_unitary hPw
    (RealizesCleanUnitary.mono_proj (baseDiagProjW_conjTranspose topW rCombBase _) hPw hSub hR)
    hUeq
  intro M_obs
  obtain ⟨M_out, hM_out⟩ := hBundle.store M_obs
  refine ⟨M_out, hM_out, ?_⟩
  have hconj := hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
  rw [← congrFun hM_out default, ← projZeroAll_eq_basisOutcomeProjector_zero rWork]
  simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
    congrArg HermitianMat.mat hconj

end RelayEngineW

/- ## Section 4A: Hoisted Pre-MidKick `0-T` Clear & Post-Stage-6 Recompute `StepBundleW`s -/

/-- Combined Z3 and Q3 retained-bit overlay on the 437-wire Slot-3 frame. -/
abbrev putQZ (ξ : BitAssignment 437) : BitAssignment 437 :=
  Slot3ZRetCore.putQ3
    (Slot3ZRetCore.putZ3 ξ)

/-- Pre-MidKick retained-wire clear on the 179w / 190w control-tier branches:
zeros `p57MW 0..2` (`177..197`) and `retMuQuadW 0..2` (`251..253`). -/
def clearPreMKCtrl (ξ : BitAssignment 437) : BitAssignment 437 := fun w ↦ if
    (177 ≤ w.val ∧ w.val < 198) ∨ (251 ≤ w.val ∧ w.val < 254) then 0 else ξ w

/-- Pre-MidKick retained-wire clear on the 193w catalytic branch:
zeros `p57MW 0` (`177..183`) and `retMuQuadW 0..2` (`251..253`). -/
def clearPreMKCat (ξ : BitAssignment 437) : BitAssignment 437 := fun w ↦ if
    (177 ≤ w.val ∧ w.val < 184) ∨ (251 ≤ w.val ∧ w.val < 254) then 0 else ξ w

/-- Width-indexed hoisted pre-MidKick clear (`clearPreMKCat` on `342`, `clearPreMKCtrl`
  otherwise). -/
abbrev clearPreMKOfTopW (topW : ℕ) : BitAssignment 437 → BitAssignment 437 :=
  if topW = 342 then clearPreMKCat else clearPreMKCtrl

section Part4A_PrePostMK

open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (wire_ne_of_lt wire_ne_of_gt CliffProg TempPhaseProg cleanRem)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (ValidCleanRem TempCtx ctxCliffAlloc)
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (ctxCliffAlloc_disjoint ctxCliffAlloc_supports)
open MeasureBranchHadamardSem
  (RealizesCleanUnitary measureAndBranchSeq_support_subset
   hadamardAll xReset)
open StreamingBchComparator (PreservesStoreConst)
open MomSlots35Slot3ProjNuclear (shellMu3 shellMu3_lt_seven)
open MomSlots35Slot3ProjNuclear (shellMagCoord3)
open StepBBlock0 (IsMutBlock)
open Prod57BoothHoist (p57MW p57CleanDiagProj p57ToDynWith)
open Prod57BoothHoist (p57ToDynWith_count_t p57ToDynWith_count_toff)
open Prod57BoothHoist (p57ToDynWith_preservesStore)
open StepBOuter
  (muW u22WAux getU22 getU22_congr magDest21
   magSrc21 magSel7W magGeW xorBlockProg xorBlock275_spec)
open Slot3Outer2344AndRelayWide.PosPhase246
  (cliffSupportsBelowB ctxSupportsBelowB progSupportsBelowB)
open Slot3Outer2344AndRelayWide.Slot3Exact216AsymUncomp
  (czVecCircuit dZeroTUncomp1
   magPairK magPairLhs magPairRhs
   magPairLhs_ne_rhs magPairLhs_lt289 magPairRhs_lt289 magDest21_lt289
   magInnerLoopStatic magInnerLoopStatic_spec
   dMagInnerLoop dMagInnerLoop_count_t dMagInnerLoop_count_toff
   dMagInnerLoop_preservesStore InvMagHole dMagInnerLoop_realizes InvMagRev)
open Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore
  (magUnpack63_275_spec ctxMagAxisLoopFast ctxMagAxisLoopFast_scoped)
open Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned
  (dXorAndPairsUncomp)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide
  (cliffDisjointBad progDisjointBad permOfInvol permReg)
open Slot3ZRetCore
  (putZ3_of_not_bad cleanRem_putZ3 putQ3_of_not_bad invMuQuad3_putQ3 cleanRem_putQ3 st1Z st1QZ
    lhsQuad3 rhsQuad3 lhsQuad3_ne_rhs lhsQuad3_lt275 rhsQuad3_lt275 retMuQuadW retMuQuadW_lt275
    retMuQuadW_val_eq InvMuQuad3 InvMuQuad3_congr muQuad3Ret3_275 dClearRetMuQuad0_275
    dClearRetMuQuad0_275_count_t dClearRetMuQuad0_275_count_toff dClearRetMuQuad0_275_preservesStore
    clearRetMuQuad_spec_and_dyn muQuadIn6W muQuadIn6W_inj mu3OneHot7FromQuad14Ops
    mu3OneHot7FromQuad14_meta mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta
    magUnpackFromRetQuadK1Ctx magUnpackFromRetQuad60_275 magUnpackFromRetQuad60_275Ctx
    magUnpackFromRetQuad60_275_spec)
open Slot3Norm1s36CoreWide (n1s_st1_props N1sRetainedInv)

/-- Intermediate retained-wire clear zeroing `m` magnitude wires `[177 .. 177 + m)`. -/
def clearMWPrefix (m : ℕ) (ξ : BitAssignment 437) : BitAssignment 437 :=
  fun w ↦ if 177 ≤ w.val ∧ w.val < 177 + m then 0 else ξ w

theorem validSwapRelayWM_id_zret {topW : ℕ} (h275 : 275 ≤ topW) (h437 : topW ≤ 437) :
    ValidSwapRelayWM topW topW id (fun _ ↦ false) where
  h275 := h275
  htopM := le_rfl
  hM437 := h437
  invol _ := rfl
  fix_ge_M _ _ := rfl
  fix_not_bad_lt _ _ _ := rfl
  bad_lt275 _ h := Bool.noConfusion h
  bad_swap_range _ := ⟨fun h ↦ Bool.noConfusion h, fun ⟨h1, h2⟩ ↦ by omega⟩
  range_swap_bad _ := ⟨fun ⟨h1, h2⟩ ↦ by omega, fun h ↦ Bool.noConfusion h⟩

theorem cliff_not_mem_support_of_lt {M n : ℕ} (rComb : QRegister M n) (bound : ℕ) :
    ∀ (c : CliffProg M), cliffSupportsBelowB bound c = true →
      ∀ u : Wire M, bound ≤ u.val → rComb u ∉ ((c.onRegister rComb).toCircuit).support
  | .nil, _, _, _ => by simp [CliffProg.onRegister, CliffProg.toCircuit]
  | .x q, hc, u, hu => by
      have hq : q.val < bound := of_decide_eq_true hc
      have hne : rComb u ≠ rComb q := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      simp [CliffProg.onRegister, CliffProg.toCircuit, hne]
  | .cnot c t _, hc, u, hu => by
      obtain ⟨hc1, ht1⟩ := (Bool.and_eq_true _ _).mp hc
      have hcv : c.val < bound := of_decide_eq_true hc1
      have htv : t.val < bound := of_decide_eq_true ht1
      have hnec : rComb u ≠ rComb c := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      have hnet : rComb u ≠ rComb t := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      simp [CliffProg.onRegister, CliffProg.toCircuit, hnec, hnet]
  | .seq c₁ c₂, hc, u, hu => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hc
      simp only [CliffProg.onRegister, CliffProg.toCircuit, Circuit.support_seq,
        Finset.mem_union, not_or]
      exact ⟨cliff_not_mem_support_of_lt rComb bound c₁ h1 u hu,
        cliff_not_mem_support_of_lt rComb bound c₂ h2 u hu⟩

theorem prog_not_mem_support_of_lt {M n : ℕ} (rComb : QRegister M n) (bound : ℕ) :
    ∀ (p : TempPhaseProg M), progSupportsBelowB bound p = true →
      ∀ u : Wire M, bound ≤ u.val → rComb u ∉ ((p.onRegister rComb).toToffCircuit).support
  | .nil, _, _, _ => by simp [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit]
  | .cliff c, hp, u, hu => cliff_not_mem_support_of_lt rComb bound c hp u hu
  | .z q, hp, u, hu => by
      have hq : q.val < bound := of_decide_eq_true hp
      have hne : rComb u ≠ rComb q := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      simp [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, hne]
  | .seq p₁ p₂, hp, u, hu => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hp
      simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.support_seq,
        Finset.mem_union, not_or]
      exact ⟨prog_not_mem_support_of_lt rComb bound p₁ h1 u hu,
        prog_not_mem_support_of_lt rComb bound p₂ h2 u hu⟩
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, hp, u, hu => by
      obtain ⟨hc1, hrest⟩ := (Bool.and_eq_true _ _).mp hp
      obtain ⟨hc2, ha_b⟩ := (Bool.and_eq_true _ _).mp hrest
      obtain ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp ha_b
      have hv1 : c₁.val < bound := of_decide_eq_true hc1
      have hv2 : c₂.val < bound := of_decide_eq_true hc2
      have hva : anc.val < bound := of_decide_eq_true ha
      have hne1 : rComb u ≠ rComb c₁ := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      have hne2 : rComb u ≠ rComb c₂ := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      have hnea : rComb u ≠ rComb anc := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      have hbody := prog_not_mem_support_of_lt rComb bound body hb u hu
      have htoff : rComb u ∉ (Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a)
          (rComb.wires.injective.ne h₂a)).support := by
        simp only [Circuit.support, QRegister.image, Finset.mem_map, Finset.mem_univ, true_and,
          not_exists]
        intro i hi
        fin_cases i
        · exact hne1 hi.symm
        · exact hne2 hi.symm
        · exact hnea hi.symm
      simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.support_seq,
        Finset.mem_union, not_or]
      exact ⟨htoff, hbody, htoff⟩

theorem p57ToDynWith_not_mem_support_of_lt {Var : Type} {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (bound : ℕ)
    (dInner : DynamicCircuit Var n)
    (hInner : ∀ u : Wire M, bound ≤ u.val → rComb u ∉ dInner.support) :
    ∀ (K : TempCtx M), ctxSupportsBelowB bound K = true →
      ∀ u : Wire M, bound ≤ u.val → rComb u ∉ (p57ToDynWith v rComb dInner K).support
  | .hole, _, u, hu => hInner u hu
  | .seqPre c K, hK, u, hu => by
      obtain ⟨hc, hk⟩ := (Bool.and_eq_true _ _).mp hK
      simp only [p57ToDynWith, DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
        Finset.mem_union, not_or]
      exact ⟨cliff_not_mem_support_of_lt rComb bound c hc u hu,
        p57ToDynWith_not_mem_support_of_lt v rComb bound dInner hInner K hk u hu⟩
  | .seqPost K c, hK, u, hu => by
      obtain ⟨hk, hc⟩ := (Bool.and_eq_true _ _).mp hK
      simp only [p57ToDynWith, DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
        Finset.mem_union, not_or]
      exact ⟨p57ToDynWith_not_mem_support_of_lt v rComb bound dInner hInner K hk u hu,
        cliff_not_mem_support_of_lt rComb bound c hc u hu⟩
  | .tempAnd c₁ c₂ anc _ _ _ K, hK, u, hu => by
      obtain ⟨hc1, hrest⟩ := (Bool.and_eq_true _ _).mp hK
      obtain ⟨hc2, ha_k⟩ := (Bool.and_eq_true _ _).mp hrest
      obtain ⟨ha, hk⟩ := (Bool.and_eq_true _ _).mp ha_k
      have hv1 : c₁.val < bound := of_decide_eq_true hc1
      have hv2 : c₂.val < bound := of_decide_eq_true hc2
      have hva : anc.val < bound := of_decide_eq_true ha
      have hne1 : rComb u ≠ rComb c₁ := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      have hne2 : rComb u ≠ rComb c₂ := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      have hnea : rComb u ≠ rComb anc := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      simp only [p57ToDynWith, DynamicCircuit.support_seq, DynamicCircuit.support_andCompute,
        DynamicCircuit.support_andUncompute, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨⟨hne1, hne2, hnea⟩, p57ToDynWith_not_mem_support_of_lt v rComb bound dInner
        hInner K hk u hu, ⟨hne1, hne2, hnea⟩⟩

theorem dXorAndPairsUncomp_not_mem_support_of_lt {Var : Type} {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (bound : ℕ) :
    ∀ (W : ℕ) (lhs rhs acc : Fin W → Wire M) (hlr : ∀ j, lhs j ≠ rhs j),
      (∀ j, (lhs j).val < bound) → (∀ j, (rhs j).val < bound) → (∀ j, (acc j).val < bound) →
      ∀ u : Wire M, bound ≤ u.val →
        rComb u ∉ (dXorAndPairsUncomp v rComb W lhs rhs acc hlr).support
  | 0, _, _, _, _, _, _, _, _, _ => by simp [dXorAndPairsUncomp]
  | W + 1, lhs, rhs, acc, hlr, hl, hr, ha, u, hu => by
      have hne1 : rComb u ≠ rComb (lhs 0) := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; have := hl 0; omega)
      have hne2 : rComb u ≠ rComb (rhs 0) := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; have := hr 0; omega)
      have hnea : rComb u ≠ rComb (acc 0) := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; have := ha 0; omega)
      simp only [dXorAndPairsUncomp, DynamicCircuit.support_seq,
        DynamicCircuit.support_andUncompute,
        Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨hne1, hne2, hnea⟩, dXorAndPairsUncomp_not_mem_support_of_lt v rComb bound W (fun
        j ↦ lhs j.succ) (fun j ↦ rhs j.succ) (fun j ↦ acc j.succ) (fun j ↦ hlr j.succ) (fun j
        ↦ hl j.succ) (fun j ↦ hr j.succ) (fun j ↦ ha j.succ) u hu⟩

theorem czVecCircuit_not_mem_support {n : ℕ} (w : Wire n) :
    ∀ (K : ℕ) (lhs rhs : Fin K → Wire n) (hne : ∀ k, lhs k ≠ rhs k),
      (∀ k, w ≠ lhs k) → (∀ k, w ≠ rhs k) →
      w ∉ (czVecCircuit K lhs rhs hne).support
  | 0, _, _, _, _, _ => by simp [czVecCircuit]
  | K + 1, lhs, rhs, hne, hl, hr => by
      have hcz : w ∉ (DynCircuitExt.czCircuit (lhs 0) (rhs 0) (hne 0)).support := by
        simp [DynCircuitExt.czCircuit, hl 0, hr 0]
      simp only [czVecCircuit, Circuit.support_seq, Finset.mem_union, not_or]
      exact ⟨hcz, czVecCircuit_not_mem_support w K _ _ _ (fun k ↦ hl k.succ) (fun k ↦ hr k.succ)⟩

theorem dZeroTUncomp1_not_mem_support {Var : Type} {n : ℕ} (v : Var) (qanc w : Wire n)
    (cFix : Circuit n) (hwq : w ≠ qanc) (hc : w ∉ cFix.support) : w ∉
    (dZeroTUncomp1 v qanc cFix).support := by
  let S : Finset (Wire n) := insert qanc cFix.support
  have hwS : w ∉ S := by simp [S, hwq, hc]
  have hsub : (dZeroTUncomp1 v qanc cFix).support ⊆ S := by
    dsimp only [dZeroTUncomp1]
    rw [DynamicCircuit.support_seq, Finset.union_subset_iff]
    refine ⟨?_, measureAndBranchSeq_support_subset v S 1 _ _ (fun _ ↦ ?_) (fun g ↦ ?_)⟩
    · simp [hadamardAll, S]
    · simp [QRegister.image_singleton, S]
    · by_cases hg : g 0 = true <;> simp [hg, xReset, S]
  exact fun hw ↦ hwS (hsub hw)

theorem dMagInnerLoop_not_mem_support_of_lt {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) (bound : ℕ) (hb : 289 ≤ bound) :
    ∀ (m : ℕ) (hm : m ≤ 21) (u : Wire 437), bound ≤ u.val →
      rComb u ∉ (dMagInnerLoop v rComb m hm).support
  | 0, _, _, _ => by simp [dMagInnerLoop]
  | m + 1, hm, u, hu => by
      let idx : Fin 21 := ⟨m, by omega⟩
      have hne_d : rComb u ≠ rComb (magDest21 idx) := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; have := magDest21_lt289 idx; omega)
      have hlr : ∀ k, rComb (magPairLhs idx k) ≠ rComb (magPairRhs idx k) :=
        fun k ↦ rComb.wires.injective.ne (magPairLhs_ne_rhs idx k)
      have hcz : rComb u ∉ (czVecCircuit (magPairK idx) (fun k ↦ rComb (magPairLhs idx k))
          (fun k ↦ rComb (magPairRhs idx k)) hlr).support :=
        czVecCircuit_not_mem_support (rComb u) (magPairK idx) _ _ hlr
          (fun k ↦ rComb.wires.injective.ne (fun h ↦ by
            have hv := congrArg Fin.val h; have := magPairLhs_lt289 idx k; omega))
          (fun k ↦ rComb.wires.injective.ne (fun h ↦ by
            have hv := congrArg Fin.val h; have := magPairRhs_lt289 idx k; omega))
      simp only [dMagInnerLoop, DynamicCircuit.support_seq, Finset.mem_union, not_or]
      exact ⟨dZeroTUncomp1_not_mem_support v (rComb (magDest21 idx)) (rComb u) _ hne_d hcz,
        dMagInnerLoop_not_mem_support_of_lt v rComb bound hb m (by omega) u hu⟩

/-- `< 290`-wire static reference uncomputer for the first `m` (`m ≤ 21`) `p57MW` wires. -/
def pMagUnpackPrefixCut (m : ℕ) (hm : m ≤ 21) : TempPhaseProg 437 :=
  magUnpackFromRetQuadK1Ctx.plug (magInnerLoopStatic m hm)

/-- `0 T` (`0 .TOFF`) `< 289`-wire dynamic uncomputer for the first `m` (`m ≤ 21`) `p57MW` wires. -/
def dMagUnpackPrefixFromRetQuad0_275 {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) (m : ℕ) (hm : m ≤ 21) : DynamicCircuit Var n :=
  p57ToDynWith v rComb (dMagInnerLoop v rComb m hm) magUnpackFromRetQuadK1Ctx

theorem dMagUnpackPrefixFromRetQuad0_275_count_t {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) (m : ℕ) (hm : m ≤ 21) :
    (dMagUnpackPrefixFromRetQuad0_275 v rComb m hm).count PrimitiveGate.T = 0 := by
  obtain ⟨hCnt1, _, _, _⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muQuadIn6W muQuadIn6W_inj 275 14 0
      (fun i ↦ by fin_cases i <;> decide)
      mu3OneHot7FromQuad14Ops mu3OneHot7FromQuad14_meta (by decide)
  dsimp only [dMagUnpackPrefixFromRetQuad0_275, magUnpackFromRetQuadK1Ctx]
  rw [p57ToDynWith_count_t, dMagInnerLoop_count_t, Nat.add_zero, hCnt1]

theorem dMagUnpackPrefixFromRetQuad0_275_count_toff {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) (m : ℕ) (hm : m ≤ 21) :
    (dMagUnpackPrefixFromRetQuad0_275 v rComb m hm).count PrimitiveGate.TOFF = 0 :=
  p57ToDynWith_count_toff v rComb _ (dMagInnerLoop_count_toff v rComb m hm)
    magUnpackFromRetQuadK1Ctx

theorem dMagUnpackPrefixFromRetQuad0_275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (rComb : QRegister 437 n) (m : ℕ) (hm : m ≤ 21) :
    PreservesStoreConst (dMagUnpackPrefixFromRetQuad0_275 v rComb m hm) :=
  p57ToDynWith_preservesStore v rComb _
    (dMagInnerLoop_preservesStore v rComb m hm) magUnpackFromRetQuadK1Ctx

theorem pMagUnpackPrefixCut_spec_and_dyn (m : ℕ) (hm : m ≤ 21) :
    let mutM : Wire 437 → Prop := fun q ↦ ∃ idx : Fin 21, idx.val < m ∧ q = magDest21 idx
    ValidCleanRem 437 (437 - 275) (pMagUnpackPrefixCut m hm) ∧
      (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β →
        (pMagUnpackPrefixCut m hm).evalSign β = 0 ∧
        cleanRem 437 (437 - 275) ((pMagUnpackPrefixCut m hm).evalBits β) ∧
        (∀ w : Wire 437, ¬ mutM w → (pMagUnpackPrefixCut m hm).evalBits β w = β w) ∧
        (InvMagRev β → InvMuQuad3 β →
          ∀ idx : Fin 21,
            idx.val < m → (pMagUnpackPrefixCut m hm).evalBits β (magDest21 idx) = 0)) ∧
      (∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
        (v : Var) (rComb : QRegister 437 n) (Inv : BitAssignment 437 → Prop),
        (∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ → Inv γ →
          InvMagRev γ ∧ InvMuQuad3 γ) →
        RealizesCleanUnitary v (p57CleanDiagProj rComb (437 - 275) (by decide) Inv)
          (dMagUnpackPrefixFromRetQuad0_275 v rComb m hm)
          ((((pMagUnpackPrefixCut m hm).onRegister rComb).toToffCircuit).eval)) := by
  intro mutM
  obtain ⟨_, hProps1, hLift1, hEval1⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muQuadIn6W muQuadIn6W_inj 275 14 0
      (fun i ↦ by fin_cases i <;> decide)
      mu3OneHot7FromQuad14Ops mu3OneHot7FromQuad14_meta (by decide)
  obtain ⟨hd1, hs1⟩ := hProps1 (mutW := mutM)
    (fun i ⟨idx, _, h⟩ ↦ by
      have hv := congrArg Fin.val h
      fin_cases i <;> (dsimp [muQuadIn6W, muW, retMuQuadW, magDest21, p57MW] at hv; omega))
    (fun q hq ⟨idx, _, h⟩ ↦ by subst h; dsimp [magDest21, p57MW] at hq; omega)
  obtain ⟨hvIn, hsIn, hSpecIn⟩ := magInnerLoopStatic_spec m hm
  obtain ⟨hvAll, _, hsAll, hbitsAll⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean
      (M := 437) (rem := 437 - 275) (curHole := 289)
      mutM magUnpackFromRetQuadK1Ctx hd1 hs1 (by decide)
      magUnpackFromRetQuadK1Ctx.fwdBits
      (Slot3MicroEngineAux.TempCtxLiftEx.probe hLift1)
      (magInnerLoopStatic m hm) hvIn
      (fun δ hδ w hw ↦ (hSpecIn δ hδ).2.1 w (fun idx hlt h ↦ hw ⟨idx, hlt, h⟩))
  have hDotEq := Slot3ZRetCore.magUnpackFromRetQuadK1_dotSum_eq
  have hnonAll : ∀ β, cleanRem 437 (437 - 275) β → ∀ w, ¬ mutM w →
      (pMagUnpackPrefixCut m hm).evalBits β w = β w := fun β hβ w hw ↦ by
    dsimp only [pMagUnpackPrefixCut]; rw [hbitsAll β hβ w, ite_eq_right hw]
  have hclAll : ∀ β, cleanRem 437 (437 - 275) β →
      cleanRem 437 (437 - 275) ((pMagUnpackPrefixCut m hm).evalBits β) := fun β hβ u hu ↦ by
    rw [hnonAll β hβ u (fun ⟨idx, _, h⟩ ↦ by subst h; dsimp [magDest21, p57MW] at hu; omega)]
    exact hβ u hu
  have hcl1 : ∀ δ, cleanRem 437 (437 - 275) δ → cleanRem 437 (437 - 289)
      (magUnpackFromRetQuadK1Ctx.fwdBits δ) := fun δ hδ ↦ (hEval1 δ hδ).1
  have hd1' : magUnpackFromRetQuadK1Ctx.DisjointFrom mutM := hd1
  have hsgnAll : ∀ β, cleanRem 437 (437 - 275) β →
      (pMagUnpackPrefixCut m hm).evalSign β = 0 := fun β hβ ↦ by
    dsimp only [pMagUnpackPrefixCut]; rw [hsAll β hβ, hsIn _ (hcl1 β hβ)]
  refine ⟨hvAll, fun β hβ ↦ ⟨hsgnAll β hβ, hclAll β hβ, hnonAll β hβ, fun hMag hQ idx hlt ↦ ?_⟩,
    fun v rComb Inv hInv ↦ ?_⟩
  · have hm_in : mutM (magDest21 idx) := ⟨idx, hlt, rfl⟩
    dsimp only [pMagUnpackPrefixCut]
    rw [hbitsAll β hβ (magDest21 idx), ite_eq_left hm_in, (hSpecIn _ (hcl1 β hβ)).2.2 idx hlt,
      StepBBlock0.TempCtx.fwdBits_mut hd1' β hm_in,
      hDotEq β hβ hMag.1 hQ idx]
    dsimp only [magDest21]
    rw [hMag.2 ⟨idx.val / 7, by omega⟩ ⟨idx.val % 7, by omega⟩]
    by_cases ht : (shellMagCoord3 (getU22 β) ⟨idx.val / 7, by omega⟩).testBit (idx.val % 7) <;>
      simp [ht]
  · dsimp only [dMagUnpackPrefixFromRetQuad0_275, pMagUnpackPrefixCut]
    exact Slot3Norm1s36CoreWideBooth.n1s_toDynWith_realizes_supp
      v rComb (magInnerLoopStatic m hm) (dMagInnerLoop v rComb m hm)
      (InvMagHole m) 289 (by decide) (dMagInnerLoop_realizes v rComb m hm)
      magUnpackFromRetQuadK1Ctx hs1 (437 - 275) (by decide) (by decide) Inv hvAll
      (fun γ hcr hi idx hlt ↦ by
        obtain ⟨⟨hmu, hm_b⟩, hQ⟩ := hInv γ hcr hi
        rw [StepBBlock0.TempCtx.fwdBits_mut hd1' γ ⟨idx, hlt, rfl⟩,
          hDotEq γ hcr hmu hQ idx]
        exact hm_b ⟨idx.val / 7, by omega⟩ ⟨idx.val % 7, by omega⟩)

/-- `6`-`TempAnd` (`24 T`, `< 296`-wire) forward `TempCtx` unpacking axis-0 `p57MW 0`
from `(u22, mu, retMuQuadW)` on the `193w` catalytic branch. -/
def magUnpackAx0FromRetQuad6_275Ctx : TempCtx 437 :=
  let k1 := Slot3MicroEngineAux.ctxMicro muQuadIn6W muQuadIn6W_inj 275 14 0
    (fun i ↦ by fin_cases i <;> decide)
    mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta (by decide)
  let k2 := ctxCliffAlloc (.cnot (u22WAux 0) ⟨289, by decide⟩ (by decide))
  let k3 := Slot3MicroEngineAux.ctxAndPairs 6 290 (by decide)
    (fun i : Fin 6 ↦ magGeW ⟨i.val + 1, by omega⟩)
    (fun i : Fin 6 ↦ u22WAux ⟨i.val + 1, by omega⟩)
    (fun i ↦ wire_ne_of_gt (by
      have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
      dsimp at hb; dsimp [magGeW, u22WAux]; omega))
    (fun i ↦ by
      have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
      dsimp at hb; dsimp [magGeW]; omega)
    (fun i ↦ by dsimp [u22WAux]; omega)
  k1.append (k2.append k3)

/-- `6`-`TempAnd` (`24 T`, `< 296`-wire) static axis-0 `p57MW 0` recompute program. -/
def magUnpackAx0FromRetQuad6_275 : TempPhaseProg 437 :=
  xorBlockProg 7
    (fun j : Fin 7 ↦ magDest21 ⟨j.val, by omega⟩)
    (fun j : Fin 7 ↦ magSrc21 ⟨j.val, by omega⟩)
    (fun j ↦ by dsimp [magDest21, p57MW]; omega)
    (fun j ↦ by dsimp only [magSrc21]; rw [dite_eq_left j.isLt]; dsimp; omega)
    magUnpackAx0FromRetQuad6_275Ctx

theorem magUnpackAx0FromRetQuad6_275_spec : IsMutBlock 437 (437 - 275)
    (fun q ↦ ∃ b : Fin 7, q = p57MW 0 b) magUnpackAx0FromRetQuad6_275 ∧
    magUnpackAx0FromRetQuad6_275.countTempAnd = 6 ∧ (∀ β : BitAssignment 437, cleanRem 437
    (437 - 275) β → InvMuQuad3 β → bitsVal (fun i ↦ β (muW i)) = shellMu3 (getU22 β) →
    ∀ b : Fin 7, magUnpackAx0FromRetQuad6_275.evalBits β (p57MW 0 b) = β (p57MW 0 b) + if
    (shellMagCoord3 (getU22 β) 0).testBit b.val then 1 else 0) := by
  let out7 : Fin 7 → Wire 437 := fun j ↦ magDest21 ⟨j.val, by omega⟩
  let src7 : Fin 7 → Wire 437 := fun j ↦ magSrc21 ⟨j.val, by omega⟩
  let mut7 : Wire 437 → Prop := fun q ↦ ∃ j : Fin 7, q = out7 j
  have hout7_inj : Function.Injective out7 := fun i j h ↦ by
    have hv := congrArg Fin.val h; dsimp [out7, magDest21, p57MW] at hv; exact Fin.ext (by omega)
  have hnot_ge275 : ∀ q : Wire 437, 275 ≤ q.val → ¬ mut7 q := by
    rintro q hq ⟨j, rfl⟩; dsimp [out7, magDest21, p57MW] at hq; omega
  have hnot_u22 : ∀ i : Fin 22, ¬ mut7 (u22WAux i) := by
    rintro i ⟨j, h⟩; have hv :=
      congrArg Fin.val h; dsimp [u22WAux, out7, magDest21, p57MW] at hv; omega
  let hin1 : ∀ i, (muQuadIn6W i).val < 275 := fun i ↦ by fin_cases i <;> decide
  obtain ⟨hCnt1, hProps1, hLift1, _⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muQuadIn6W muQuadIn6W_inj 275 14 0 hin1
      mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta (by decide)
  obtain ⟨hd1, hs1⟩ := hProps1 (mutW := mut7)
    (fun i ⟨j, h⟩ ↦ by
      have hv := congrArg Fin.val h
      fin_cases i <;> (dsimp [muQuadIn6W, muW, retMuQuadW, out7, magDest21, p57MW] at hv; omega))
    hnot_ge275
  let c2 : CliffProg 437 := .cnot (u22WAux 0) ⟨289, by decide⟩ (by decide)
  have hc2_supp : c2.SupportsBelow 290 := ⟨by dsimp [u22WAux]; omega, by dsimp; omega⟩
  have hd2 : (ctxCliffAlloc c2).DisjointFrom mut7 :=
    ctxCliffAlloc_disjoint ⟨hnot_u22 0, hnot_ge275 _ (by dsimp; omega)⟩
  have hs2 : (ctxCliffAlloc c2).SupportsBelowCtx 290 := ctxCliffAlloc_supports hc2_supp
  have hLift2 : Slot3MicroEngineAux.TempCtxLiftEx 289 290 (ctxCliffAlloc c2) :=
    Slot3MicroEngineAux.TempCtxLiftEx.mono
      (Slot3MicroEngineAux.TempCtxLiftEx.cliff 290 (by decide) c2 hc2_supp)
      (by decide) le_rfl (by decide)
  let l3 : Fin 6 → Wire 437 := fun i ↦ magGeW ⟨i.val + 1, by omega⟩
  let r3 : Fin 6 → Wire 437 := fun i ↦ u22WAux ⟨i.val + 1, by omega⟩
  have hne3 : ∀ i, l3 i ≠ r3 i := fun i ↦ wire_ne_of_gt (by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
    dsimp at hb; dsimp [l3, r3, magGeW, u22WAux]; omega)
  have hl3 : ∀ i, (l3 i).val < 290 := fun i ↦ by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
    dsimp at hb; dsimp [l3, magGeW]; omega
  have hr3 : ∀ i, (r3 i).val < 290 := fun i ↦ by dsimp [r3, u22WAux]; omega
  have hCnt3 := Slot3MicroEngineAux.ctxAndPairs_countTempAnd (M := 437) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3
  obtain ⟨hd3, hs3⟩ := Slot3MicroEngineAux.ctxAndPairs_props (mutW := mut7) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3
    (fun i ↦ hnot_ge275 _ (by dsimp [l3, magGeW]; omega))
    (fun i ↦ hnot_u22 _)
    (fun q hq ↦ hnot_ge275 q (by omega))
  obtain ⟨hLift3, _⟩ := Slot3MicroEngineAux.ctxAndPairs_scoped (M := 437) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3
  have hdAll : magUnpackAx0FromRetQuad6_275Ctx.DisjointFrom mut7 :=
    TempCtx.disjointFrom_append hd1 (TempCtx.disjointFrom_append hd2 hd3)
  have hsAll : magUnpackAx0FromRetQuad6_275Ctx.SupportsBelowCtx 296 :=
    TempCtx.supportsBelowCtx_append (by decide) hs1
      (TempCtx.supportsBelowCtx_append (by decide) hs2 hs3)
  have hLiftAll : Slot3MicroEngineAux.TempCtxLiftEx 275 296 magUnpackAx0FromRetQuad6_275Ctx :=
    Slot3MicroEngineAux.TempCtxLiftEx.append hLift1
      (Slot3MicroEngineAux.TempCtxLiftEx.append hLift2 hLift3)
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock275_spec (curEnd := 296) (by decide) (by decide)
    out7 src7
    (fun j ↦ by dsimp [out7, magDest21, p57MW]; omega)
    hout7_inj
    (fun j ↦ by dsimp only [src7, magSrc21]; rw [dite_eq_left j.isLt]; dsimp; omega)
    magUnpackAx0FromRetQuad6_275Ctx hdAll hsAll hLiftAll
  have hCnt6 : magUnpackAx0FromRetQuad6_275Ctx.countTempAnd = 6 := by
    dsimp only [magUnpackAx0FromRetQuad6_275Ctx]
    rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd,
      Slot3MicroEngineAux.TempCtx.append_countTempAnd, hCnt1, hCnt3]
    rfl
  have hMutIff : ∀ q : Wire 437, mut7 q ↔ ∃ b : Fin 7, q = p57MW 0 b := fun q ↦
    ⟨fun ⟨j, hj⟩ ↦ ⟨j, hj.trans (Fin.ext (by dsimp [out7, magDest21, p57MW]; omega))⟩,
     fun ⟨b, hb⟩ ↦ ⟨b, hb.trans (Fin.ext (by dsimp [out7, magDest21, p57MW]; omega))⟩⟩
  refine ⟨⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦
    hB.2.2.2 β hβ q (fun hm ↦ hq ((hMutIff q).mp hm))⟩,
    hCnt.trans hCnt6, fun β hβ hQ hmu b ↦ ?_⟩
  have hb_out : out7 b = p57MW 0 b := Fin.ext (by dsimp [out7, magDest21, p57MW]; omega)
  rw [← hb_out]
  dsimp only [magUnpackAx0FromRetQuad6_275]
  rw [hEv β hβ b, hb_out]
  let mutSrc : Wire 437 → Prop := fun q ↦ q = src7 b
  have hsrc_val : (src7 b).val = 289 + b.val := by
    dsimp only [src7, magSrc21]; rw [dite_eq_left b.isLt]
  obtain ⟨_, hProps4, _, _⟩ :=
    ctxMagAxisLoopFast_scoped 1 (by decide) 296 (by decide) (by decide) 7 le_rfl
  obtain ⟨_, hProps5, _, _⟩ :=
    ctxMagAxisLoopFast_scoped 2 (by decide) 324 (by decide) (by decide) 7 le_rfl
  have hnotS_sel (a : Fin 7) : ¬ mutSrc (magSel7W a) := fun h ↦ by
    have hv := congrArg Fin.val h
    have hb7 := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
    dsimp [magSel7W] at hv hb7
    omega
  have hd45S := TempCtx.disjointFrom_append
    (hProps4 (mutW := mutSrc)
      (fun j h ↦ by
        have hv := congrArg Fin.val h
        dsimp [muW] at hv
        omega)
      hnotS_sel
      (fun i h ↦ by
        have hv := congrArg Fin.val h
        dsimp [u22WAux] at hv
        omega)
      (fun q hq h ↦ by
        have hv := congrArg Fin.val h
        omega)).1
    (hProps5 (mutW := mutSrc)
      (fun j h ↦ by
        have hv := congrArg Fin.val h
        dsimp [muW] at hv
        omega)
      hnotS_sel
      (fun i h ↦ by
        have hv := congrArg Fin.val h
        dsimp [u22WAux] at hv
        omega)
      (fun q hq h ↦ by
        have hv := congrArg Fin.val h
        omega)).1
  have hfEq : magUnpackAx0FromRetQuad6_275Ctx.fwdBits β (src7 b) =
      magUnpackFromRetQuad60_275Ctx.fwdBits β (src7 b) := by
    have hf60 : magUnpackFromRetQuad60_275Ctx.fwdBits β =
        ((ctxMagAxisLoopFast 1 (by decide) 296 (by decide) (by decide) 7 le_rfl).append
          (ctxMagAxisLoopFast 2 (by decide) 324 (by decide) (by decide) 7 le_rfl)).fwdBits
          (magUnpackAx0FromRetQuad6_275Ctx.fwdBits β) := by
      dsimp only [magUnpackFromRetQuad60_275Ctx, magUnpackAx0FromRetQuad6_275Ctx]
      repeat rw [Slot3MicroEngineAux.TempCtx.append_fwdBits]
    rw [hf60]
    exact (StepBBlock0.TempCtx.fwdBits_mut hd45S _ rfl).symm
  have h60_b :=
    Slot3ZRetCore.magUnpackFromRetQuad60_pkg.2.2.1 β hβ
      ⟨b.val, by omega⟩
  change magUnpackFromRetQuad60_275.evalBits β (out7 b) = β (out7 b) +
      magUnpackFromRetQuad60_275Ctx.fwdBits β (src7 b) at h60_b
  rw [hb_out] at h60_b
  have hμ7 : bitsVal (fun i ↦ β (muW i)) < 7 := hmu ▸ shellMu3_lt_seven (getU22 β)
  rw [hfEq, ← h60_b, magUnpackFromRetQuad60_275_spec.2.2 β hβ hQ hμ7]
  exact magUnpack63_275_spec.2.2 β hβ hmu 0 b

theorem isBadXM_false_of_lt {M_stage : ℕ} {w : Wire 437} (hw : w.val < M_stage) :
    isBadXM M_stage (fun _ ↦ false) w = false := by
  simp [isBadXM, Nat.not_le.mpr hw]

theorem cliffDisjointBad_isBadXM_false {bound M_stage : ℕ} (h : bound ≤ M_stage) :
    ∀ (c : CliffProg 437), cliffSupportsBelowB bound c = true →
      cliffDisjointBad (isBadXM M_stage (fun _ ↦ false)) c = true
  | .nil, _ => rfl
  | .x q, hc => by
      have hq : q.val < bound := of_decide_eq_true hc
      dsimp [cliffDisjointBad]
      rw [isBadXM_false_of_lt (lt_of_lt_of_le hq h)]; rfl
  | .cnot x y _, hc => by
      obtain ⟨hx1, hy1⟩ := (Bool.and_eq_true _ _).mp hc
      have hx : x.val < bound := of_decide_eq_true hx1
      have hy : y.val < bound := of_decide_eq_true hy1
      dsimp [cliffDisjointBad]
      rw [isBadXM_false_of_lt (lt_of_lt_of_le hx h),
        isBadXM_false_of_lt (lt_of_lt_of_le hy h)]; rfl
  | .seq c₁ c₂, hc => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hc
      dsimp [cliffDisjointBad]
      rw [cliffDisjointBad_isBadXM_false h c₁ h1,
        cliffDisjointBad_isBadXM_false h c₂ h2]; rfl

theorem progDisjointBad_isBadXM_false {bound M_stage : ℕ} (h : bound ≤ M_stage) :
    ∀ (p : TempPhaseProg 437), progSupportsBelowB bound p = true →
      progDisjointBad (isBadXM M_stage (fun _ ↦ false)) p = true
  | .nil, _ => rfl
  | .cliff c, hp => cliffDisjointBad_isBadXM_false h c hp
  | .z q, hp => by
      have hq : q.val < bound := of_decide_eq_true hp
      dsimp [progDisjointBad]
      rw [isBadXM_false_of_lt (lt_of_lt_of_le hq h)]; rfl
  | .seq p₁ p₂, hp => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hp
      dsimp [progDisjointBad]
      rw [progDisjointBad_isBadXM_false h p₁ h1,
        progDisjointBad_isBadXM_false h p₂ h2]; rfl
  | .tempAnd c₁ c₂ anc _ _ _ body, hp => by
      obtain ⟨hc1, hrest⟩ := (Bool.and_eq_true _ _).mp hp
      obtain ⟨hc2, ha_b⟩ := (Bool.and_eq_true _ _).mp hrest
      obtain ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp ha_b
      have hv1 : c₁.val < bound := of_decide_eq_true hc1
      have hv2 : c₂.val < bound := of_decide_eq_true hc2
      have hva : anc.val < bound := of_decide_eq_true ha
      dsimp [progDisjointBad]
      rw [isBadXM_false_of_lt (lt_of_lt_of_le hv1 h),
        isBadXM_false_of_lt (lt_of_lt_of_le hv2 h),
        isBadXM_false_of_lt (lt_of_lt_of_le hva h),
        progDisjointBad_isBadXM_false h body hb]; rfl

theorem compose_permReg_id {n : ℕ} (r : QRegister 437 n) (h : ∀ w : Wire 437, id w = w) :
    r.compose (permReg (permOfInvol id h)) = r := by
  cases r; rfl

theorem putQZ_of_lt251 {ξ : BitAssignment 437} {w : Wire 437} (hw : w.val < 251) :
    putQZ ξ w = ξ w := by
  dsimp only [putQZ]
  rw [putQ3_of_not_bad (decide_eq_false (by omega)),
    putZ3_of_not_bad (decide_eq_false (by omega))]

theorem putQZ_of_ge257 {ξ : BitAssignment 437} {w : Wire 437} (hw : 257 ≤ w.val) :
    putQZ ξ w = ξ w := by
  dsimp only [putQZ]
  rw [putQ3_of_not_bad (decide_eq_false (by omega)),
    putZ3_of_not_bad (decide_eq_false (by omega))]

theorem cleanRem_putQZ {ξ : BitAssignment 437} (hcl : cleanRem 437 (437 - 275) ξ) : cleanRem
    437 (437 - 275) (putQZ ξ) := cleanRem_putQ3 (cleanRem_putZ3 hcl)

theorem invMagRev_putQZ_of_n1s {ξ : BitAssignment 437} (h : N1sRetainedInv ξ) :
    InvMagRev (putQZ ξ) := by
  have hu22 : getU22 (putQZ ξ) = getU22 ξ :=
    getU22_congr (fun i ↦ putQZ_of_lt251 (by dsimp [u22WAux]; omega))
  have hmu_fn : (fun j ↦ putQZ ξ (muW j)) = fun j ↦ ξ (muW j) :=
    funext fun j ↦ putQZ_of_lt251 (by dsimp [muW]; omega)
  refine ⟨by rw [hmu_fn, hu22]; exact h.mu_val, fun w b ↦ ?_⟩
  rw [putQZ_of_lt251 (by dsimp [p57MW]; omega), hu22]
  exact h.hm w b

theorem invMagRev_congr_lt275 {γ₁ γ₂ : BitAssignment 437}
    (hag : ∀ w : Wire 437, w.val < 275 → γ₁ w = γ₂ w) : InvMagRev γ₁ ↔ InvMagRev γ₂ := by
  have hu22 : getU22 γ₁ = getU22 γ₂ :=
    getU22_congr (fun i ↦ hag _ (by dsimp [u22WAux]; omega))
  have hmu : (fun j ↦ γ₁ (muW j)) = fun j ↦ γ₂ (muW j) :=
    funext fun j ↦ hag _ (by dsimp [muW]; omega)
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨by rw [← hmu, ← hu22]; exact h1, fun w b ↦ ?_⟩,
    fun ⟨h1, h2⟩ ↦ ⟨by rw [hmu, hu22]; exact h1, fun w b ↦ ?_⟩⟩
  · rw [← hag _ (by dsimp [p57MW]; omega), ← hu22]; exact h2 w b
  · rw [hag _ (by dsimp [p57MW]; omega), hu22]; exact h2 w b

/-- Parametric `0 T` (`0 .TOFF`) pre-MidKick uncomputer clearing `m` (`m ≤ 21`) `p57MW` wires
followed by `retMuQuadW 0..2` (`251..253`). -/
def dPreMKPrefix {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n)
    (m : ℕ) (hm : m ≤ 21) : DynamicCircuit Var n :=
  .seq (dMagUnpackPrefixFromRetQuad0_275 v rCombBase m hm) (dClearRetMuQuad0_275 v rCombBase)

/-- `0 T` (`0 .TOFF`) pre-MidKick retained-wire clear on `179w` / `190w` control-tier branches. -/
def dPreMKCtrl {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) : DynamicCircuit
    Var n := dPreMKPrefix v rCombBase 21 le_rfl

theorem dPreMKCtrl_count_t {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    (dPreMKCtrl v rCombBase).count PrimitiveGate.T = 0 := by
  dsimp only [dPreMKCtrl, dPreMKPrefix]
  simp only [DynamicCircuit.count, dMagUnpackPrefixFromRetQuad0_275_count_t,
    dClearRetMuQuad0_275_count_t]

theorem dPreMKCtrl_count_toff {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    (dPreMKCtrl v rCombBase).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dPreMKCtrl, dPreMKPrefix]
  simp only [DynamicCircuit.count, dMagUnpackPrefixFromRetQuad0_275_count_toff,
    dClearRetMuQuad0_275_count_toff]

theorem stepBundleW_dPreMKPrefix (m : ℕ) (hm : m ≤ 21) (topW : ℕ) (htop_lo : 290 ≤ topW)
    (htop_hi : topW ≤ 437) (hpSupp : progSupportsBelowB 290 (pMagUnpackPrefixCut m hm) = true)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rCombBase : QRegister 437 n) : StepBundleW topW v rCombBase st1QZ (fun α w ↦ if (177 ≤
    w.val ∧ w.val < 177 + m) ∨ (251 ≤ w.val ∧ w.val < 254) then 0 else st1QZ α w) (fun _ ↦ 0)
    (dPreMKPrefix v rCombBase m hm) := by
  have h275 : 275 ≤ topW := by omega
  let hsr := validSwapRelayWM_id_zret h275 htop_hi
  have hRegId : rCombBase.compose (permReg (permOfInvol id hsr.invol)) = rCombBase :=
    compose_permReg_id rCombBase hsr.invol
  obtain ⟨_, hEvP, hDynP⟩ := pMagUnpackPrefixCut_spec_and_dyn m hm
  let Inv1 : BitAssignment 437 → Prop := fun γ ↦ InvMagRev γ ∧ InvMuQuad3 γ
  have hInv1_ag : ∀ {γ₁ γ₂ : BitAssignment 437},
      (∀ w : Wire 437, w.val < 275 → γ₁ w = γ₂ w) → (Inv1 γ₁ ↔ Inv1 γ₂) := fun hag ↦
    and_congr (invMagRev_congr_lt275 hag)
      (InvMuQuad3_congr (fun j ↦ hag _ (by dsimp [muW]; omega))
        (fun j ↦ hag _ (by fin_cases j <;> decide)))
  have hRealRange1 : RealizesCleanUnitary v (p57RangeDiagProj rCombBase 275 topW Inv1)
      (dMagUnpackPrefixFromRetQuad0_275 v rCombBase m hm)
      ((((pMagUnpackPrefixCut m hm).onRegister rCombBase).toToffCircuit).eval) :=
    realizesCleanUnitary_drop_tail v rCombBase 275 topW h275 htop_hi Inv1
      (fun u hu _ _ hne ↦ hInv1_ag fun w hw ↦ hne w (wire_ne_of_lt (by omega)))
      _ (fun u hu ↦ p57ToDynWith_not_mem_support_of_lt v rCombBase 289
          (dMagInnerLoop v rCombBase m hm)
          (dMagInnerLoop_not_mem_support_of_lt v rCombBase 289 le_rfl m hm)
          magUnpackFromRetQuadK1Ctx (by decide) u (by omega))
      _ (fun u hu ↦ prog_not_mem_support_of_lt rCombBase 290 _ hpSupp u (by omega))
      (hDynP v rCombBase Inv1 (fun _ _ h ↦ h))
  let δ_mid : BitAssignment 149 → BitAssignment 437 := fun α ↦ clearMWPrefix m (st1QZ α)
  have hcl_in : ∀ α, cleanRem 437 (437 - 275) (st1QZ α) :=
    fun α ↦ cleanRem_putQZ (n1s_st1_props α).1.hcl
  have hcl_mid : ∀ α, cleanRem 437 (437 - 275) (δ_mid α) := fun α w hw ↦ by
    dsimp [δ_mid, clearMWPrefix]
    split_ifs
    · rfl
    · exact hcl_in α w hw
  have hInv1_st1 : ∀ α, Inv1 (st1QZ α) := fun α ↦
    ⟨invMagRev_putQZ_of_n1s (n1s_st1_props α).1, invMuQuad3_putQ3 (st1Z α)⟩
  have hMid_eq : ∀ α, δ_mid α = (pMagUnpackPrefixCut m hm).evalBits (st1QZ α) := fun α ↦ by
    obtain ⟨_, _, hnon, hclr⟩ := hEvP (st1QZ α) (hcl_in α)
    obtain ⟨hMag, hQ⟩ := hInv1_st1 α
    funext w; dsimp only [δ_mid, clearMWPrefix]
    by_cases hw : 177 ≤ w.val ∧ w.val < 177 + m
    · rw [ite_eq_left hw, show w = magDest21 ⟨w.val - 177, by omega⟩ from Fin.ext (by
        have := Nat.mod_lt (w.val - 177) (by decide : 0 < 7); dsimp [magDest21, p57MW]; omega)]
      exact (hclr hMag hQ ⟨w.val - 177, by omega⟩ (by dsimp; omega)).symm
    · rw [ite_eq_right hw]
      exact (hnon w (fun ⟨idx, hlt, hweq⟩ ↦
        hw (by subst hweq; dsimp [magDest21, p57MW]; omega))).symm
  have hB1 : StepBundleW topW v rCombBase st1QZ δ_mid (fun _ ↦ 0)
      (dMagUnpackPrefixFromRetQuad0_275 v rCombBase m hm) :=
    stepBundleW_of_relayWM_dyn v rCombBase hsr st1QZ δ_mid (fun _ ↦ 0)
      (pMagUnpackPrefixCut m hm) (dMagUnpackPrefixFromRetQuad0_275 v rCombBase m hm)
      (dMagUnpackPrefixFromRetQuad0_275_preservesStore v rCombBase m hm) Inv1
      (by rw [hRegId]; exact hRealRange1) (progDisjointBad_isBadXM_false htop_lo _ hpSupp)
      (fun α ↦ ⟨hcl_in α, fun _ h ↦ Bool.noConfusion h⟩) hMid_eq
      (fun α ↦ (hEvP (st1QZ α) (hcl_in α)).1)
      (fun α ↦ ⟨hcl_mid α, fun _ h ↦ Bool.noConfusion h⟩)
      (fun _ α _ hEq ↦ (hInv1_ag fun w hw ↦
        hEq w (isBadXM_false_of_lt (lt_of_lt_of_le hw h275))).mpr (hInv1_st1 α))
  obtain ⟨_, hs2, hEv2, hDyn2⟩ := clearRetMuQuad_spec_and_dyn
  have hRealRange2 : RealizesCleanUnitary v (p57RangeDiagProj rCombBase 275 topW InvMuQuad3)
      (dClearRetMuQuad0_275 v rCombBase)
      (((muQuad3Ret3_275.onRegister rCombBase).toToffCircuit).eval) :=
    realizesCleanUnitary_drop_tail v rCombBase 275 topW h275 htop_hi InvMuQuad3
      (fun _ hu _ _ hne ↦ InvMuQuad3_congr
        (fun j ↦ hne _ (wire_ne_of_lt (by dsimp [muW]; omega)))
        (fun j ↦ hne _ (wire_ne_of_lt (lt_of_lt_of_le (retMuQuadW_lt275 j) (le_trans h275 hu)))))
      _ (fun u hu ↦ dXorAndPairsUncomp_not_mem_support_of_lt v rCombBase 275 3
          lhsQuad3 rhsQuad3 retMuQuadW lhsQuad3_ne_rhs lhsQuad3_lt275 rhsQuad3_lt275
          retMuQuadW_lt275 u (by omega))
      _ (fun u hu ↦
        prog_not_mem_support_of_lt rCombBase 276 muQuad3Ret3_275 (by decide) u (by omega))
      (hDyn2 v rCombBase InvMuQuad3 (fun _ _ h ↦ h))
  let δ_out : BitAssignment 149 → BitAssignment 437 := fun α w ↦
    if (177 ≤ w.val ∧ w.val < 177 + m) ∨ (251 ≤ w.val ∧ w.val < 254) then 0 else st1QZ α w
  have hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α) := fun α w hw ↦ by
    dsimp [δ_out]
    split_ifs
    · rfl
    · exact hcl_in α w hw
  have hInv2_mid : ∀ α, InvMuQuad3 (δ_mid α) := fun α ↦
    (InvMuQuad3_congr
      (fun j ↦ by dsimp [δ_mid, clearMWPrefix, st1QZ, muW]; rw [ite_eq_right (by omega)])
      (fun j ↦ by
        have := retMuQuadW_val_eq j
        dsimp [δ_mid, clearMWPrefix, st1QZ]; rw [ite_eq_right (by omega)])).mpr
      (invMuQuad3_putQ3 (st1Z α))
  have hOut_eq : ∀ α, δ_out α = muQuad3Ret3_275.evalBits (δ_mid α) := fun α ↦ by
    obtain ⟨_, hnon, hclr⟩ := hEv2 (δ_mid α) (hcl_mid α)
    funext w
    by_cases hq : 251 ≤ w.val ∧ w.val < 254
    · dsimp only [δ_out]; rw [ite_eq_left (Or.inr hq),
        show w = retMuQuadW ⟨w.val - 251, by omega⟩ from
          Fin.ext (by rw [retMuQuadW_val_eq]; dsimp; omega),
        hclr (hInv2_mid α) ⟨w.val - 251, by omega⟩]
    · rw [hnon w (fun j hj ↦ hq (by subst hj; rw [retMuQuadW_val_eq]; omega))]
      dsimp only [δ_out, δ_mid, clearMWPrefix]
      by_cases hm_w : 177 ≤ w.val ∧ w.val < 177 + m
      · rw [ite_eq_left (Or.inl hm_w), ite_eq_left hm_w]
      · rw [ite_eq_right (fun h ↦ h.elim hm_w hq), ite_eq_right hm_w]
  exact hB1.seq_zero_left (stepBundleW_of_relayWM_dyn v rCombBase hsr δ_mid δ_out (fun _ ↦ 0)
    muQuad3Ret3_275 (dClearRetMuQuad0_275 v rCombBase)
    (dClearRetMuQuad0_275_preservesStore v rCombBase) InvMuQuad3
    (by rw [hRegId]; exact hRealRange2)
    (progDisjointBad_isBadXM_false (by omega : 276 ≤ topW) _ (by decide))
    (fun α ↦ ⟨hcl_mid α, fun _ h ↦ Bool.noConfusion h⟩) hOut_eq
    (fun α ↦ hs2 (δ_mid α) (hcl_mid α))
    (fun α ↦ ⟨hcl_out α, fun _ h ↦ Bool.noConfusion h⟩)
    (fun _ α _ hEq ↦ (InvMuQuad3_congr
      (fun j ↦ hEq _ (isBadXM_false_of_lt (by dsimp [muW]; omega)))
      (fun j ↦ hEq _ (isBadXM_false_of_lt (lt_of_lt_of_le (retMuQuadW_lt275 j) h275)))).mpr
        (hInv2_mid α)))

theorem stepBundleW_dPreMKCtrl (topW : ℕ) (htop : topW = 328 ∨ topW = 339) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rCombBase : QRegister 437 n) : StepBundleW topW v rCombBase st1QZ
    (clearPreMKCtrl ∘ st1QZ) (fun _ ↦ 0) (dPreMKCtrl v rCombBase) :=
  stepBundleW_dPreMKPrefix 21 le_rfl topW
    (by rcases htop with rfl | rfl <;> decide)
    (by rcases htop with rfl | rfl <;> decide)
    (by decide) v rCombBase

end Part4A_PrePostMK

set_option maxRecDepth 512
set_option exponentiation.threshold 256

end ConfigLeaf3Slot3ZRet193

end Leaf3Slot3ZRet193

end
set_option exponentiation.threshold 256
end Leaf3Slot3ZRet193

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
