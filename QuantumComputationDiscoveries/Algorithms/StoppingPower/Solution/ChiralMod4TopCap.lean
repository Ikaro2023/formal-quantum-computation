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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPhaseMod4Bnds

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section TopClosureAux
local instance (priority := 1000000) instNeZeroTwoPow_TopClosureAux (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace TopClosureAux

section ConfigTopClosureAux

local instance (priority := 1000000) instLoc_TopClosure_1InstNeZeroTwoPowTop (k : ℕ) : NeZero (2 ^
  k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option exponentiation.threshold 256

open Real Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped Matrix Matrix.Norms.L2Operator BigOperators

open SpecsAux.SpecMirror
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
open SpecsAux.FullScaleBESector (AgreesOnFermionicSector)

/- ## Section 1: Chiral `W ∈ {28 .. 33}` Mod-4 Fermionic Bridges & Tight Non-`S3` / `ε_BE` Caps -/

section Part1ChiralMod4AndCaps

open MomSlot0CircuitHalf (slot0ElectronKineticOracleSym)
theorem slot0ElectronKineticOracleSym_80_epsIntr :
    (slot0ElectronKineticOracleSym (le_refl 80)).epsIntr = (6 : ℝ) / 10 ^ 7 := rfl

end Part1ChiralMod4AndCaps

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512

end ConfigTopClosureAux
end TopClosureAux
end
set_option exponentiation.threshold 256
end TopClosureAux

section Leaf2Packed18Mux2DCore
local instance (priority := 1000000) instNeZeroTwoPow_Leaf2Packed18Mux2DCore (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
# Chiral `K = 28..33` Mod-4 Perturbation, `uPosPhase80Mod4Eff` Commutations, and Parametric
`190w`/`196w` Pass-2 Wrappers

Provides Pass-2 building blocks:
1. **Universal `uCoin` Block-Encoding Perturbation & `Coin3ConstAlphaSpecV2` (`c230` / `c86`)
Bridge**:
   - Proves `zeroSubwire_uCoin_gridPerturbation_of_trunc_param_s1_b2b4_of_posPhase` directly from
     any `prep : FullSysPrepareBundle 80` and `uCoin : Unitary (2 ^ 3)` satisfying
     `∀ c, prep.uPrep c = zeroSubwireConstPrepUnitary post uCoin` and 6-slot L1 weight error
     `≤ err_w` (requiring neither static `Circuit 4` nor `hSlack23` / `hCoin7`, so `c230`, `c234`,
     and `CleanPrepProg` `c86`/`c92` witnesses all plug in identically).
   - Exports `FixesCtrl3`, `FixesLow3924`, and `hmPrep ≤ 137` for `zeroSubwireConstPrepBundleV2`
     with `PosPostPrep80CertS3.pos80MergedPostPrepCert` (`1,744 T`).
2. **`uPosPhase80Mod4Eff` Commutation with `dyadicDiagUnitary` (`uKoffDiagCore`) &
`uProjPosToCut80`**:
   - Proves `dyadicDiagUnitary_comm_uPosPhase80Mod4Eff`, `slot2M48Val_posPhase80Mod4BitFn`,
     `vepOnlyM48Val_posPhase80Mod4BitFn`, and `uProjPosToCut80_comm_uPosPhase80Mod4Eff`.
3. **Chiral `K ∈ {28..33}` (`chiralKOfJ`) Mod-4 Fermionic Bounds & Turnkey `hPert`**:
   - Combines `SubvoxelNuclearTrunc28To35Chiral` (`280,677` nano-Ha at `K = 33`) with
     `PosMod4FermionicBounds` and `PosS3Bounds.deltaPosBhmtExactNatOfB` for per-horizon
     block-encoding perturbation bounds.
4. **Zero-Overlap Parametric `190w` / `196w` Pass-2 Wrappers (`Unheld138` & `Packed18`)**:
   - Parameterizes over `(dCore133, tCore)`, `(dPartnerTail2D, tPartner)`, and `(dMid, tMid)` for
     both `dOrbitSandUnheld138` (`190 ≤ mWB`, `(mWB - 18) - 34` clean wires: `138` on `190w`
     `Ctrl` and `144 ≥ 135` on `196w` `Cat`, enabling `dMidK6SplitRouter135Dyn` at `-592 T/walk`)
     and `dOrbitSandPacked18` (`196 ≤ mWB`, `((mWB - 18) - 34) - 18 = 126+` clean wires),
     plus concrete circuits (`41,289 + 260*B` / `40,529 + 260*B`).
-/

namespace Leaf2Packed18Mux2DCore

section ConfigLeaf2Packed18Mux2DCore

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

set_option maxRecDepth 4096
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true

local instance (priority := 1000000) instLoc_Leaf2Packed18Mux2DCore_1InstNeZeroTwoPowLeaf (k : ℕ) :
  NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
-- Root solution namespace already active.
open PosMomSelectSandwich (slotBitProj)
open TwosCompAndWire0Cancel (smToTwosSysUnitary)
open FullSysCatSegmentBridge (fullSysCoreWires)
open PosSlots24SemanticOracleConcrete80 (pos80Slot2Scale)
open Pos24MergedVepPrepAndStitch (mergedPosSlot2WeightGen)
open Pos24Slot2FermionicBridge (pos24Slot2E2Const)

section Part2PosPhase80Mod4Comm

open Dyadic128CoulombMath (orbitCount47905)
open FullSysCatSegmentBridge (coreCosetB1Block)
open InterWalkRSum42Hoist (PreservesFeature)
open NuclearTwistAndXor654Concrete (nuclearM48)
open NuclearTwistRealizes (coin0Active slot2M48Val)
open ProjZ512QftAndTwist288
  (vepHighNuc vepHighNuc_iff vepOnlyM48Val vepProj9CoreIdx rProjAxis)
open FusedPreDiagFromTwist288 (hm6_of_hm22)
open KoffPrunedSlot2ZeroMuxTrunc37 (uKoffDiagCore kOffTotalPhaseExp kOffFromEff vepEffSlope48)
open SchedBranchStitchGen (dyadicDiagUnitary_eq_diagonal)
open SelectStitch (uProjPosToCut80 comm_uProjPosToCut80_of_preserves_and_comm)
open Leaf4Ext48TopStitch (CommutesWithReg commutesWithReg_of_forall_singleton)
open PosSlots24BranchConcrete (posCoreWires wHeadThresh rElecSlot rAnchorIdx
  tailAndSlackPhaseBitSpec)
open PosHeadMod4_15476 (flipTh flipThClean headEnBoolSpec headPhaseMod4Z8Spec posPhaseMod4Z8Spec)
open PosSlots24SemanticBridge (pos24_coreWires80_eq)
open PosSlots24UnbarreledWide (castBits swapCore3967Fn_high)
open PosPostPrep80MergedVep (swapCore3967Fn)
open Leaf2PosMod4WidthCore
  (uPosPhase80Mod4Eff uPosPhase80Mod4Eff_mulVec_ket
   posPhase80Mod4Scalar posPhase80Mod4BitFn posPhase80Mod4BitFn_apply_of_ne_3985
   preservesFeature_of_mulVec_ket_smul commutesWithReg_singleton_of_ket_indep
   lt_posCore_of_fullSys80 lt_fullSys80_of_posCore)

theorem matrix_diagonal_comm_of_preservesFeature {n : ℕ} {α : Type} (F : Fin (2 ^ n) → α)
    (d : α → ℂ) (A : Operator (2 ^ n)) (hPres : PreservesFeature F A) : Matrix.diagonal
    (fun u ↦ d (F u)) * A = A * Matrix.diagonal (fun u ↦ d (F u)) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h0 : A i j = 0
  · simp [h0]
  · rw [hPres i j h0, mul_comm]

theorem vepEffSlope48_posPhase80Mod4BitFn (c : Configuration) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires 80)) : vepEffSlope48 c (by decide : 22 ≤ 80) w
    (posPhase80Mod4BitFn γ) = vepEffSlope48 c (by decide : 22 ≤ 80) w γ := by
  let hm : 22 ≤ 80 := by decide
  have hCoin : coin0Active (posPhase80Mod4BitFn γ) = coin0Active γ := by
    unfold coin0Active
    rw [posPhase80Mod4BitFn_apply_of_ne_3985 γ _ (by decide), posPhase80Mod4BitFn_apply_of_ne_3985 γ
      _ (by decide), posPhase80Mod4BitFn_apply_of_ne_3985 γ _ (by decide)]
  have hNuc : regVal (NuclearTwistAndXor654Concrete.rNucIdx hm (QRegExt.idReg _))
      (posPhase80Mod4BitFn γ) = regVal
      (NuclearTwistAndXor654Concrete.rNucIdx hm (QRegExt.idReg _)) γ :=
    congrArg bitsVal (funext fun k : Fin 8 ↦
      posPhase80Mod4BitFn_apply_of_ne_3985 γ
        (NuclearTwistAndXor654Concrete.rNucIdx hm (QRegExt.idReg _) k)
        ((by decide : ∀ s : Fin 8,
          (NuclearTwistAndXor654Concrete.rNucIdx hm (QRegExt.idReg _) s).val ≠ 3985) k))
  have hSlot2 : slot2M48Val c hm w (posPhase80Mod4BitFn γ) = slot2M48Val c hm w γ := by
    unfold slot2M48Val
    by_cases h1 : coin0Active γ = true ∧
        regVal (NuclearTwistAndXor654Concrete.rNucIdx hm (QRegExt.idReg _)) γ < 216
    · have h2 : coin0Active (posPhase80Mod4BitFn γ) = true ∧
          regVal (NuclearTwistAndXor654Concrete.rNucIdx hm (QRegExt.idReg _))
            (posPhase80Mod4BitFn γ) < 216 := by
        rwa [hCoin, hNuc]
      rw [dite_eq_left h2, dite_eq_left h1]
      exact congrArg (fun idx ↦ nuclearM48 c idx w) (Fin.ext hNuc)
    · have h2 : ¬ (coin0Active (posPhase80Mod4BitFn γ) = true ∧
          regVal (NuclearTwistAndXor654Concrete.rNucIdx hm (QRegExt.idReg _))
            (posPhase80Mod4BitFn γ) < 216) := by
        rwa [hCoin, hNuc]
      rw [dite_eq_right h2, dite_eq_right h1]
  have hHigh : vepHighNuc hm (posPhase80Mod4BitFn γ) = vepHighNuc hm γ :=
    Bool.eq_iff_iff.mpr ((vepHighNuc_iff hm _).trans (by
      rw [hCoin, hNuc]
      exact (vepHighNuc_iff hm _).symm))
  have hVep : vepOnlyM48Val hm w (posPhase80Mod4BitFn γ) = vepOnlyM48Val hm w γ := by
    unfold vepOnlyM48Val
    rw [hHigh]
    split_ifs with hv
    · refine congrArg (2 ^ 39 * ·) (congrArg bitsVal (funext fun j : Fin 9 ↦ ?_))
      exact posPhase80Mod4BitFn_apply_of_ne_3985 γ (vepProj9CoreIdx hm w j)
        ((by decide : ∀ (a : Fin 3) (b : Fin 9),
          (vepProj9CoreIdx hm a b).val ≠ 3985) w j)
    · rfl
  have hCoset : posPhase80Mod4BitFn γ (coreCosetB1Block (hm6_of_hm22 hm) w) =
      γ (coreCosetB1Block (hm6_of_hm22 hm) w) :=
    posPhase80Mod4BitFn_apply_of_ne_3985 γ (coreCosetB1Block (hm6_of_hm22 hm) w)
      ((by decide : ∀ a : Fin 3,
        (coreCosetB1Block (hm6_of_hm22 hm) a).val ≠ 3985) w)
  unfold vepEffSlope48
  rw [hSlot2, hVep, hCoset]

theorem kOffTotalPhaseExp_posPhase80Mod4BitFn (c : Configuration)
    (γ : BitAssignment (fullSysCoreWires 80)) : kOffTotalPhaseExp c (by decide : 22 ≤ 80)
    (posPhase80Mod4BitFn γ) = kOffTotalPhaseExp c (by decide : 22 ≤ 80) γ := by
  unfold kOffTotalPhaseExp
  exact congrArg (- ·) (Finset.sum_congr rfl fun w _ ↦
    congrArg kOffFromEff (vepEffSlope48_posPhase80Mod4BitFn c w γ))

theorem uKoffDiagCore_comm_uPosPhase80Mod4Eff (c : Configuration)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    uKoffDiagCore c (by decide : 22 ≤ 80) * uPosPhase80Mod4Eff tailSign tailMag30 =
    uPosPhase80Mod4Eff tailSign tailMag30 * uKoffDiagCore c (by decide : 22 ≤ 80) := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  rw [uKoffDiagCore, dyadicDiagUnitary_eq_diagonal]
  refine matrix_diagonal_comm_of_preservesFeature
    (fun u ↦ kOffTotalPhaseExp c (by decide : 22 ≤ 80) (basisBits _ u))
    (DyadicQft64.dyadicTurn 48) (uPosPhase80Mod4Eff tailSign tailMag30).1 ?_
  refine preservesFeature_of_mulVec_ket_smul _ _ (posPhase80Mod4Scalar tailSign tailMag30)
    posPhase80Mod4BitFn (uPosPhase80Mod4Eff_mulVec_ket tailSign tailMag30) fun j ↦ ?_
  change kOffTotalPhaseExp c (by decide : 22 ≤ 80)
      (basisBitsEquiv _ ((basisBitsEquiv _).symm (posPhase80Mod4BitFn (basisBits _ j)))) = _
  rw [(basisBitsEquiv _).apply_symm_apply]
  exact kOffTotalPhaseExp_posPhase80Mod4BitFn c (basisBits _ j)

/-- Projectile coordinate wire `3924 + p.val` (`p : Fin 24`) on `posCoreWires = 4,034`. -/
def wProj24Pos (p : Fin 24) : Wire posCoreWires :=
  ⟨3924 + p.val, by have := p.isLt; dsimp [posCoreWires]; omega⟩

/-- Projectile coordinate wire `3924 + p.val` (`p : Fin 24`) on `fullSysCoreWires 80 = 4,034`. -/
def wProj24Core (p : Fin 24) : Wire (fullSysCoreWires 80) :=
  ⟨3924 + p.val, lt_fullSys80_of_posCore (wProj24Pos p).isLt⟩

private theorem upd_proj24_w (f : QRegister posCoreWires posCoreWires → Wire posCoreWires)
    (h : ∀ s : Fin 24, f (QRegExt.ofFin posCoreWires) ≠ wProj24Pos s)
    (p : Fin 24) (β : BitAssignment posCoreWires) (v : ZMod 2) :
    Function.update β (wProj24Pos p) v (f (QRegExt.ofFin posCoreWires)) =
      β (f (QRegExt.ofFin posCoreWires)) := Function.update_of_ne (h p) _ _

private theorem upd_proj24_reg {k : ℕ}
    (f : QRegister posCoreWires posCoreWires → QRegister k posCoreWires)
    (h : ∀ (s : Fin 24) (j : Fin k), f (QRegExt.ofFin posCoreWires) j ≠ wProj24Pos s)
    (p : Fin 24) (β : BitAssignment posCoreWires) (v : ZMod 2) :
    regVal (f (QRegExt.ofFin posCoreWires)) (Function.update β (wProj24Pos p) v) =
      regVal (f (QRegExt.ofFin posCoreWires)) β :=
  PosSlots24BranchConcrete.regVal_congr' fun i ↦ Function.update_of_ne (h p i) _ _

private theorem upd_proj24_parity3
    (f : QRegister posCoreWires posCoreWires → QRegister 3 posCoreWires)
    (h : ∀ (s : Fin 24) (a : Fin 3), f (QRegExt.ofFin posCoreWires) a ≠ wProj24Pos s)
    (p : Fin 24) (β : BitAssignment posCoreWires) (v : ZMod 2) :
    PosSlots24BranchConcrete.parity3OfReg (f (QRegExt.ofFin posCoreWires))
      (Function.update β (wProj24Pos p) v) =
    PosSlots24BranchConcrete.parity3OfReg (f (QRegExt.ofFin posCoreWires)) β := by
  funext w
  dsimp [PosSlots24BranchConcrete.parity3OfReg]
  rw [Function.update_of_ne (h p w)]

private theorem upd_proj24_elec (p : Fin 24) (β : BitAssignment posCoreWires) (v : ZMod 2)
    (e : Fin 218) :
    PosSlots24BranchConcrete.slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e)
      (Function.update β (wProj24Pos p) v) =
    PosSlots24BranchConcrete.slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β := by
  funext w
  ext
  refine PosSlots24BranchConcrete.regVal_congr' fun j ↦ Function.update_of_ne (fun h ↦ ?_) _ _
  have hv : 18 * e.val + (6 * w.val + (5 - j.val)) = 3924 + p.val := congrArg Fin.val h
  have he := e.isLt
  have hw := w.isLt
  have hj := j.isLt
  have hp := p.isLt
  omega

theorem headEnBoolSpec_update_proj24 (p : Fin 24) (β : BitAssignment posCoreWires) (v : ZMod 2) :
    headEnBoolSpec (Function.update β (wProj24Pos p) v) = headEnBoolSpec β := by
  dsimp only [headEnBoolSpec]
  rw [upd_proj24_w PosSlots24BranchConcrete.wSlot2Core (by decide), upd_proj24_w
    PosSlots24BranchConcrete.wSlot1Core (by decide), upd_proj24_w
    PosSlots24BranchConcrete.wSlot0Core (by decide), upd_proj24_w
    PosSlots24BranchConcrete.wSubReject (by decide), upd_proj24_w PosSlots24BranchConcrete.wIsHead
    (by decide), upd_proj24_reg PosSlots24BranchConcrete.rNucIdx (by decide), upd_proj24_reg
    rAnchorIdx (by decide)]

theorem headHitSetSpec_update_proj24 (p : Fin 24) (β : BitAssignment posCoreWires) (v : ZMod 2) :
    PosHeadMod4_15476.headHitSetSpec (Function.update β (wProj24Pos p) v) =
      PosHeadMod4_15476.headHitSetSpec β := by
  have hFine : CanonRank7Circuit.fineCoordOfReg21
      (PosSlots24BranchConcrete.rHeadFine21 (QRegExt.ofFin posCoreWires))
      (Function.update β (wProj24Pos p) v) =
      CanonRank7Circuit.fineCoordOfReg21
      (PosSlots24BranchConcrete.rHeadFine21 (QRegExt.ofFin posCoreWires)) β := by
    funext w
    ext
    refine PosSlots24BranchConcrete.regVal_congr' fun i ↦ Function.update_of_ne (fun h ↦ ?_) _ _
    have hv : 3954 + (32 + (7 * w.val + i.val)) = 3924 + p.val := congrArg Fin.val h
    have hp := p.isLt
    omega
  dsimp only [PosHeadMod4_15476.headHitSetSpec]
  simp only [upd_proj24_w PosSlots24BranchConcrete.wSlot0Core (by decide) p β v, hFine,
    upd_proj24_parity3 PosSlots24BranchConcrete.rCosetB0 (by decide) p β v, upd_proj24_elec p β v]

theorem tailAndSlackPhaseBitSpec_update_proj24 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (p : Fin 24) (β : BitAssignment posCoreWires) (v : ZMod 2) : tailAndSlackPhaseBitSpec
    slot2SwappedTo0 tailSign tailMag30 (Function.update β (wProj24Pos p) v) =
    tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β := by
  dsimp only [tailAndSlackPhaseBitSpec]
  simp only [upd_proj24_w PosSlots24BranchConcrete.wSlot2Core (by decide) p β v, upd_proj24_w
    PosSlots24BranchConcrete.wSlot1Core (by decide) p β v, upd_proj24_w
    PosSlots24BranchConcrete.wSlot0Core (by decide) p β v, upd_proj24_w
    PosSlots24BranchConcrete.wSubReject (by decide) p β v, upd_proj24_w
    PosSlots24BranchConcrete.wIsHead (by decide) p β v, upd_proj24_w
    PosSlots24BranchConcrete.wRejectZero (by decide) p β v, upd_proj24_reg
    PosSlots24BranchConcrete.rNucIdx (by decide) p β v, upd_proj24_reg rAnchorIdx (by decide) p β v,
    upd_proj24_reg PosSlots24BranchConcrete.rPartnerIdx (by decide) p β v, upd_proj24_reg
    PosSlots24BranchConcrete.rTailKeep30 (by decide) p β v, upd_proj24_parity3
    PosSlots24BranchConcrete.rCosetB0 (by decide) p β v, upd_proj24_parity3
    PosSlots24BranchConcrete.rCosetB1 (by decide) p β v, upd_proj24_elec p β v]

theorem posPhaseMod4Z8Spec_update_proj24 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (p : Fin 24) (β : BitAssignment posCoreWires) (v : ZMod 2) : posPhaseMod4Z8Spec
    slot2SwappedTo0 tailSign tailMag30 (Function.update β (wProj24Pos p) v) =
    posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30 β := by
  dsimp only [posPhaseMod4Z8Spec, headPhaseMod4Z8Spec]
  rw [headEnBoolSpec_update_proj24, headHitSetSpec_update_proj24,
    tailAndSlackPhaseBitSpec_update_proj24, upd_proj24_w PosSlots24BranchConcrete.wSlot0Core (by
    decide), upd_proj24_w wHeadThresh (by decide)]

theorem castBits_swapCore3967_update_proj24 (p : Fin 24)
    (γ : BitAssignment (fullSysCoreWires 80)) (v : ZMod 2) : castBits pos24_coreWires80_eq
    (swapCore3967Fn (Function.update γ (wProj24Core p) v)) = Function.update
    (castBits pos24_coreWires80_eq (swapCore3967Fn γ)) (wProj24Pos p) v := by
  have hw67 : wProj24Core p ≠ PosPostPrep80MergedVep.wCore3967 :=
    (by decide : ∀ s : Fin 24, wProj24Core s ≠ PosPostPrep80MergedVep.wCore3967) p
  have hw29 : wProj24Core p ≠ PosPostPrep80MergedVep.wCore4029 :=
    (by decide : ∀ s : Fin 24, wProj24Core s ≠ PosPostPrep80MergedVep.wCore4029) p
  let w := wProj24Core p
  funext q
  by_cases hq : q = wProj24Pos p
  · subst hq
    rw [Function.update_self]
    dsimp only [PosSlots24UnbarreledWide.castBits, swapCore3967Fn]
    have hq_eq : (⟨(wProj24Pos p).val, lt_fullSys80_of_posCore (wProj24Pos p).isLt⟩ :
        Wire (fullSysCoreWires 80)) = w := Fin.ext rfl
    rw [hq_eq, Equiv.swap_apply_of_ne_of_ne hw67 hw29, Function.update_self]
  · rw [Function.update_of_ne hq]
    dsimp only [PosSlots24UnbarreledWide.castBits, swapCore3967Fn]
    let q' : Wire (fullSysCoreWires 80) := ⟨q.val, lt_fullSys80_of_posCore q.isLt⟩
    have hq'w : q' ≠ w := fun h ↦ hq (Fin.ext (congrArg Fin.val h))
    have hsw_ne :
        Equiv.swap PosPostPrep80MergedVep.wCore3967 PosPostPrep80MergedVep.wCore4029 q' ≠ w := by
      intro h
      have h2 := congrArg
        (Equiv.swap PosPostPrep80MergedVep.wCore3967 PosPostPrep80MergedVep.wCore4029) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne hw67 hw29] at h2
      exact hq'w h2
    exact Function.update_of_ne hsw_ne v γ

theorem posPhase80Mod4Scalar_update_proj24 (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (p : Fin 24)
    (γ : BitAssignment (fullSysCoreWires 80)) (v : ZMod 2) : posPhase80Mod4Scalar tailSign
    tailMag30 (Function.update γ (wProj24Core p) v) = posPhase80Mod4Scalar tailSign tailMag30
    γ := by
  dsimp only [posPhase80Mod4Scalar]
  rw [castBits_swapCore3967_update_proj24, posPhaseMod4Z8Spec_update_proj24]

theorem posPhase80Mod4BitFn_update_proj24
    (p : Fin 24) (γ : BitAssignment (fullSysCoreWires 80)) (v : ZMod 2) :
    posPhase80Mod4BitFn (Function.update γ (wProj24Core p) v) =
      Function.update (posPhase80Mod4BitFn γ) (wProj24Core p) v := by
  have hw_ne3985 : (wProj24Core p).val ≠ 3985 :=
    (by decide : ∀ s : Fin 24, (wProj24Core s).val ≠ 3985) p
  let w := wProj24Core p
  funext q
  by_cases hqw : q = w
  · subst hqw
    rw [Function.update_self, posPhase80Mod4BitFn_apply_of_ne_3985 _ w hw_ne3985,
      Function.update_self]
  · rw [Function.update_of_ne hqw]
    by_cases hq85 : q.val = 3985
    · have hwTh_ne : wProj24Pos p ≠ wHeadThresh (QRegExt.ofFin posCoreWires) :=
        (by decide : ∀ s : Fin 24, wProj24Pos s ≠ wHeadThresh (QRegExt.ofFin posCoreWires)) p
      let wTh := wHeadThresh (QRegExt.ofFin posCoreWires)
      have hqp_eq : (⟨q.val, lt_posCore_of_fullSys80 q.isLt⟩ : Wire posCoreWires) = wTh :=
        Fin.ext hq85
      dsimp only [posPhase80Mod4BitFn]
      rw [swapCore3967Fn_high _ q ⟨by omega, by omega⟩,
          swapCore3967Fn_high _ q ⟨by omega, by omega⟩]
      change flipThClean wTh headEnBoolSpec (castBits pos24_coreWires80_eq (swapCore3967Fn
        (Function.update γ w v))) ⟨q.val, lt_posCore_of_fullSys80 q.isLt⟩ = flipThClean wTh
        headEnBoolSpec (castBits pos24_coreWires80_eq (swapCore3967Fn γ))
        ⟨q.val, lt_posCore_of_fullSys80 q.isLt⟩
      rw [hqp_eq, castBits_swapCore3967_update_proj24]
      unfold flipThClean flipTh
      rw [Function.update_comm hwTh_ne, headEnBoolSpec_update_proj24]
      by_cases hen : headEnBoolSpec
          (Function.update (castBits pos24_coreWires80_eq (swapCore3967Fn γ)) wTh 0) = true
      · rw [ite_eq_left hen, ite_eq_left hen, Function.update_self, Function.update_self,
          Function.update_of_ne hwTh_ne.symm]
      · rw [ite_eq_right hen, ite_eq_right hen, Function.update_of_ne hwTh_ne.symm]
    · rw[posPhase80Mod4BitFn_apply_of_ne_3985 _ q hq85,
        posPhase80Mod4BitFn_apply_of_ne_3985 _ q hq85, Function.update_of_ne hqw]

theorem commutesWithReg_rProjAxis_uPosPhase80Mod4Eff (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (w : Fin 3) : CommutesWithReg
    (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) w)
    (uPosPhase80Mod4Eff tailSign tailMag30).1 := by
  refine commutesWithReg_of_forall_singleton _ fun j ↦ ?_
  have hb := SchedBranchStitchGen.rProjAxis_bounds80 w
  have hlo := hb.1 j
  have hhi := hb.2 j
  let p : Fin 24 := ⟨(rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) w j).val - 3924, by omega⟩
  have hEq : rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) w j = wProj24Core p :=
    Fin.ext (by dsimp [p, wProj24Core]; omega)
  rw [hEq]
  exact commutesWithReg_singleton_of_ket_indep (wProj24Core p) _
    (posPhase80Mod4Scalar tailSign tailMag30) posPhase80Mod4BitFn
    (uPosPhase80Mod4Eff_mulVec_ket tailSign tailMag30)
    (fun γ ↦ posPhase80Mod4BitFn_apply_of_ne_3985 γ _
      ((by decide : ∀ s : Fin 24, (wProj24Core s).val ≠ 3985) p))
    (posPhase80Mod4Scalar_update_proj24 tailSign tailMag30 p)
    (posPhase80Mod4BitFn_update_proj24 p)

theorem uProjPosToCut80_comm_uPosPhase80Mod4Eff (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : uProjPosToCut80 * uPosPhase80Mod4Eff
    tailSign tailMag30 = uPosPhase80Mod4Eff tailSign tailMag30 * uProjPosToCut80 := by
  refine comm_uProjPosToCut80_of_preserves_and_comm (uPosPhase80Mod4Eff tailSign tailMag30)
    (fun i k hne q hq ↦ ?_) (fun w B ↦ commutesWithReg_rProjAxis_uPosPhase80Mod4Eff tailSign
    tailMag30 w B)
  have hne85 : q.val ≠ 3985 := by omega
  have hPresQ : PreservesFeature (fun u : Fin (2 ^ (fullSysCoreWires 80)) ↦ basisBits _ u q)
      (uPosPhase80Mod4Eff tailSign tailMag30).1 := by
    refine preservesFeature_of_mulVec_ket_smul _ _ (posPhase80Mod4Scalar tailSign tailMag30)
      posPhase80Mod4BitFn (uPosPhase80Mod4Eff_mulVec_ket tailSign tailMag30) fun j ↦ ?_
    change (basisBitsEquiv _ ((basisBitsEquiv _).symm (posPhase80Mod4BitFn (basisBits _ j)))) q = _
    rw [(basisBitsEquiv _).apply_symm_apply]
    exact posPhase80Mod4BitFn_apply_of_ne_3985 _ q hne85
  have hEq := hPresQ i k hne
  exact hEq.symm

end Part2PosPhase80Mod4Comm

/- ## Section 3: Chiral `K = 28..33` Mod-4 Perturbation Bounds -/

section Part3ChiralMod4Pert

open PosSlots24SemanticBridge (pos24TailSign)
open SubvoxelNuclearTrunc28To35Chiral (trunc28Cfg trunc29Cfg trunc30Cfg trunc31Cfg trunc32Cfg
  trunc33Cfg)
open Leaf2PosMod4WidthCore
  (uPosPhase80Mod4OfB pos24TailMag30Aux
     uPosPhase80Mod4Eff_comm_slotBitProj)

/-- Chiral subvoxel nuclear configuration truncation map `trunc{28..33}Cfg` indexed by `W`. -/
def truncChiralOfW (W : ℕ) : Configuration → Configuration :=
  if W = 29 then trunc29Cfg else if W = 30 then trunc30Cfg else if W = 31 then trunc31Cfg
  else if W = 32 then trunc32Cfg else if W = 33 then trunc33Cfg else trunc28Cfg

theorem uPosPhase80Mod4OfB_comm_slotBitProj (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (wFlag : Wire (fullSysCoreWires 80)) (_hw1 : 3948 ≤ wFlag.val) (hw2 : wFlag.val < 3954)
    (b : Fin 2) : (uPosPhase80Mod4OfB B hB6 hB27).1 * slotBitProj wFlag b = slotBitProj
    wFlag b * (uPosPhase80Mod4OfB B hB6 hB27).1 := by
  rw [uPosPhase80Mod4OfB]
  exact uPosPhase80Mod4Eff_comm_slotBitProj pos24TailSign
    (pos24TailMag30Aux B hB6 hB27) wFlag (by omega) b

end Part3ChiralMod4Pert

/- ## Section 4: Zero-Overlap Parametric `Leaf2SpecOfTrunc` Builders & `107w` Swap-0 SR Wrappers -/

section Part4Leaf2SpecsAndSwap0SR

open Dyadic128CoulombMath (orbitCount47905)
open PosSlots24SemanticBridge (pos24TailSign)
open SelectStitch (Leaf2SpecOfTrunc)
open Leaf2PosMod4WidthCore (uPosPhase80Mod4Eff uPosPhase80Mod4Eff_conjTranspose
  uPosPhase80Mod4Eff_on_P1 uPosPhase80Mod4Eff_slack2 uPosPhase80Mod4Eff_slack3
  commutesWithReg_rCtrl3InCore_uPass2Mod4Eff)

/-- Universal `Leaf2SpecOfTrunc` builder for any `tailMag30` and any `(190w, 196w)` circuits
realizing `uPass2Mod4Eff pos24TailSign tailMag30`, discharging all 7 commutation/eigenvalue fields.
-/
def mkLeaf2SpecOfTailMag (truncFn : Configuration → Configuration) (tCtrl tCat : ℕ)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    Leaf2SpecOfTrunc truncFn tCtrl tCat where
  uPosPhase0 := uPosPhase80Mod4Eff pos24TailSign tailMag30
  hPosSA := uPosPhase80Mod4Eff_conjTranspose pos24TailSign tailMag30
  hPosOnP1 := uPosPhase80Mod4Eff_on_P1 pos24TailSign tailMag30
  hPosSlack2 := uPosPhase80Mod4Eff_slack2 pos24TailSign tailMag30
  hPosSlack3 := uPosPhase80Mod4Eff_slack3 pos24TailSign tailMag30
  hPosCommK := fun c ↦ uKoffDiagCore_comm_uPosPhase80Mod4Eff (truncFn c) pos24TailSign tailMag30
  hPosCommProjCut := uProjPosToCut80_comm_uPosPhase80Mod4Eff pos24TailSign tailMag30
  hPass2CommCtrl3 := commutesWithReg_rCtrl3InCore_uPass2Mod4Eff pos24TailSign tailMag30

end Part4Leaf2SpecsAndSwap0SR

end

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512

end ConfigLeaf2Packed18Mux2DCore
end Leaf2Packed18Mux2DCore
end
set_option exponentiation.threshold 256
end Leaf2Packed18Mux2DCore

section PerHorizonPert
local instance (priority := 1000000) instNeZeroTwoPow_PerHorizonPert (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `fastCut` Mod-4 Perturbation & Per-Horizon Closure (`PerHorizonPert`)

Complete block-encoding perturbation (`hPert`) and `PREPARE` table closures (`TopClosure` and
`ExtHkCircuitCost`) on `uVepFusedTwistRestCut80` (`JunctionProj3DCut` `fastCutUVepTwistRef`)
and
Mod-4 midpoint position reflections (`uPosPhase80Mod4OfB`):
1. `fastCut` top-coin Mod-4 collapses (`fastCutMergedVepTopCoin0_80_mod4_midpoint` and
   `fastCutMergedVepTopCoin1_80_mod4_midpoint`) at `0.00 uHa` error change.
2. Direct `SelectOraHypothesisOfTrunc` core-blocks and grid-perturbation closure
   (`select_core_blocks_of_oraHyp`, `selOra_uCoin_gridPerturbation_of_oraHyp`,
   `selOra_cleanProg_gridPerturbation_of_oraHyp`) with zero `HoistedTwistRestOutBundle` or
   `s3.mWork ≤ 288` dependencies.
3. Concrete uniform `c99` (`tPrep = 1,843 T`) and per-horizon `{c99, c101, c109}` `PREPARE`
   tables and turnkey `PerHorizonSelAndPertSpec` constructors.
-/

public section

namespace PerHorizonPert

section ConfigPerHorizonPert

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

local instance (priority := 1000000) instLoc_PerHorizonPert_1InstNeZeroTwoPowPerHorizonPe (k : ℕ) :
  NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
-- Root solution namespace already active.
open MeasureBranchHadamardSem (ket)
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysPrepare6Slot (coinSelOutcome)
open FullSysCatSegmentBridge (FullSysQft654Bundle fullSysCoreWires iSlot2 fullSysQftCoreUnitary)
open FullSysFullPrepareAndTopConcrete (selWiresSym coreSysSym coreAncSym selCoin3Sym
  coreHadamardUnitary)
open OraAndPrepBundle (PosPostPrepCert)
open Dyadic128CoulombMath (orbitCount47905)
open PosSlots24TopWrapper (PosSlots24DataGen)
open PosSlots24BranchConcrete (posCoreWires)
open PosSlots24SemanticBridge
  (castUnitaryPow2 pos24TailSign pos24_6_le_80 pos24_22_le_80 pos24_coreWires80_eq)
open PosSlots24SemanticOracleConcrete80
  (QftPreservesCoset3 hkSym80 coreIdxOf ancIdx86 ancIdx86_injective rAncFlag80
   pos80_coreIdxOf_extract_sys pos80_coreIdxOf_extract_anc
   pos80_coreIdxOf_uniq pos80_coreAnc_agreeOutside_iff pos80_coreSys_agreeOutside)
open MergedVepTopCoinCollapse
  (coreUnitarySym topCoinPropGen topCoinPropGen_of_collapse swapCoreScrGenFn mergedSliceGen
   mWCore3967Gen mWCoreScrGen conj_comm_of_parts_comm)
open MergedVepCoreSliceClosureGen
  (mscCoreBeta mscUVepTwistRef msc_mul2_comm msc_transport_hDiag_of_comm
   msc_transport_entry_of_comm msc_conj3_entry_eq_dotProduct msc_qft_comm_rAncFlag80
   matrix_ext_of_ket_core mscRNucCore msc_rNucCore_in_range)
open MergedVepCoreSliceClosure (msc_diagonal_mulVec_ket msc_uVepTwistRef_comm_rAncFlag80)
open PosPostPrep80MergedVep (conjSwapCore3967 uSwapCore3967)
open JunctionProj3DCutPos24BridgeGen
  (uVepTwistCutRef fastCutUVepTwistRef uVepTwistCutRef_pf_congr fastCutUVepTwistRef_eq_gen
   fastCutUVepTwistRef_comm_rAncFlag80
   uProjAxes3D wCutAxes wCutAxes_eq_of_high_eq ketDiag_comm_uProjAxes3D_of_outside_proj24
   mscUVepTwistRest mscUBarrelCore mscBarrelBitFn mscUVepTwistRef_eq_mul
   mscUBarrelCore_mulVec_ket mscBarrelBitFn_high_eq
   genCutUVepTwistRef_mul_assoc_ket origTwist_mul_assoc_ket
   msc_dotProduct_unitary_cancel qft_uVepTwistRestCut_mulVec_ket mscCoreBeta_high_eq)
open PosHeadMod4_15476 (permThClean embedUnitary_permThClean uPosPhaseMod4)
open PosMod4FermionicBounds (posPhaseBitMod4_eq_of_eq_active)
open PosS3Bounds
  (posPhaseBitMod4 uPosPhaseRealMod4 uXThCore wThCore one_add_uXThCore_mul_uPosPhaseMod4_eq
    posPhaseBitMod4_eq_of_coin0 idxTh80 mergedCoherentOp80Mod4Of coherentSysOp80Mod4Of
    sysBlock80Mod4Of mbh_ket_uXThCore uXThCore_sa uSwapCore3967_comm_uXThCore
    fullSysQftCoreUnitary_comm_uXThCore mscUVepTwistRef_comm_uXThCore uXThCore_mul_embedAnc_proj_eq
    conj_eq_of_one_add_inv_mul_eq msc_posPhaseBitMod4_eq_of_coin1 msc_phaseBit_swap_coin0_gen
    msc_phaseBit_swap_coin1_gen conjSwapCore3967_raw_hUPosKet mergedVepCore_hBlk0_gen
    mergedVepCore_hBlk1_gen)

/- ## Section 1: `fastCutUVepTwistRef` + `uXThCore` Commutation & Mod-4 Top-Coin Collapses -/

theorem uProjAxes3D_comm_uXThCore (W : Fin 3 → Unitary 256) :
    (uProjAxes3D 80 W).1 * uXThCore.1 = uXThCore.1 * (uProjAxes3D 80 W).1 := by
  have hEmb : ((QRegister.singleton wThCore).embedUnitary (permutationUnitary (permThClean 0
      (fun _ ↦ true)))).1 = uXThCore.1 := congrArg Subtype.val (embedUnitary_permThClean
      (QRegister.singleton wThCore) 0 (fun _ ↦ true))
  have hAx : ∀ a : Fin 3,
      ((ProjZ512QftAndTwist288.rProjAxis
          (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary (W a)).1 * uXThCore.1 =
      uXThCore.1 *
        ((ProjZ512QftAndTwist288.rProjAxis
          (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary (W a)).1 := fun a ↦ by
    have hDisj : (ProjZ512QftAndTwist288.rProjAxis (QRegExt.idReg
        (fullSysCoreWires 80)) a).DisjointWires (QRegister.singleton wThCore) := by
      rw [QRegister.disjoint_iff]
      intro i j hij
      have hb := JunctionProj3DCutPos24BridgeGen.rProjAxis_wire_bounds (mPayload := 80) a i
      have hv : ((QRegister.singleton wThCore) j).val = 3985 := rfl
      have hijv : ((ProjZ512QftAndTwist288.rProjAxis (QRegExt.idReg
          (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)) a).wires i).val =
          ((QRegister.singleton wThCore) j).val := congrArg Fin.val hij
      omega
    rw [← hEmb, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisj _ _
  unfold uProjAxes3D
  simp only [Submonoid.coe_mul]
  exact msc_mul2_comm _ _ uXThCore.1 (hAx 0) (msc_mul2_comm _ _ uXThCore.1 (hAx 1) (hAx 2))

theorem mscBarrelBitFn_update_wThCore (γ : BitAssignment (fullSysCoreWires 80)) :
    mscBarrelBitFn true pos24_22_le_80 (Function.update γ wThCore (γ wThCore + 1)) =
      Function.update (mscBarrelBitFn true pos24_22_le_80 γ) wThCore
        (mscBarrelBitFn true pos24_22_le_80 γ wThCore + 1) := by
  let γ' : BitAssignment (fullSysCoreWires 80) := Function.update γ wThCore (γ wThCore + 1)
  funext k
  by_cases hkTh : k = wThCore
  · subst hkTh
    rw [Function.update_self, mscBarrelBitFn_high_eq true pos24_22_le_80 γ' wThCore (by decide),
      mscBarrelBitFn_high_eq true pos24_22_le_80 γ wThCore (by decide)]
    exact Function.update_self wThCore (γ wThCore + 1) γ
  · rw [Function.update_of_ne hkTh]
    have hOut : ∀ q : Wire (fullSysCoreWires 80), q.val < 3976 → γ' q = γ q := fun q hq ↦
      Function.update_of_ne (fun h ↦ by have hv : q.val = 3985 := congrArg Fin.val h; omega) _ _
    have hAct : NuclearTwistRealizes.barrelActive true γ' =
        NuclearTwistRealizes.barrelActive true γ := by
      unfold NuclearTwistRealizes.barrelActive
      simp only [↓reduceIte]
      rw [hOut _ (by decide), hOut _ (by decide)]
    have hIdx : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
      (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
        (QRegExt.idReg (fullSysCoreWires 80))) γ' =
          _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
        (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
        (QRegExt.idReg (fullSysCoreWires 80))) γ :=
      PosSlots24SemanticOracleConcrete80.regVal_eq_of_wire_eq _ γ' γ
        (fun i ↦ Function.update_of_ne (by revert i; decide) _ _)
    change mscBarrelBitFn true pos24_22_le_80 γ' k = mscBarrelBitFn true pos24_22_le_80 γ k
    unfold mscBarrelBitFn NuclearTwistRealizes.barrelBitFn
    by_cases hcond : NuclearTwistRealizes.barrelActive true γ = true ∧
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
          (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
          (QRegExt.idReg (fullSysCoreWires 80))) γ < 218
    · have hcond' : NuclearTwistRealizes.barrelActive true γ' = true ∧
          _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
            (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
            (QRegExt.idReg (fullSysCoreWires 80))) γ' < 218 := by
        rwa [hAct, hIdx]
      rw [NuclearTwistRealizes.dite_pos_eq hcond', NuclearTwistRealizes.dite_pos_eq hcond]
      by_cases hk0 : k.val < 18
      · rw [NuclearTwistRealizes.dite_pos_eq hk0, NuclearTwistRealizes.dite_pos_eq hk0]
        refine (hOut _ ?_).trans (congrArg γ (Fin.ext ?_))
        · dsimp only; rw [hIdx]; have := hcond.2; omega
        · dsimp only; rw [hIdx]
      · rw [NuclearTwistRealizes.dite_neg_eq hk0, NuclearTwistRealizes.dite_neg_eq hk0]
        by_cases hk1 :
            18 * _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
              (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
              (QRegExt.idReg (fullSysCoreWires 80))) γ ≤ k.val ∧
            k.val < 18 * _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
              (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
              (QRegExt.idReg (fullSysCoreWires 80))) γ + 18
        · have hk1' :
              18 * _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
                (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
                (QRegExt.idReg (fullSysCoreWires 80))) γ' ≤ k.val ∧
              k.val < 18 * _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
                (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
                (QRegExt.idReg (fullSysCoreWires 80))) γ' + 18 := by
            rwa [hIdx]
          rw [NuclearTwistRealizes.dite_pos_eq hk1', NuclearTwistRealizes.dite_pos_eq hk1]
          refine (hOut _ ?_).trans (congrArg γ (Fin.ext ?_))
          · dsimp only; rw [hIdx]; have := hk1.2; omega
          · dsimp only; rw [hIdx]
        · have hk1' :
              ¬(18 * _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
                (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
                  (QRegExt.idReg (fullSysCoreWires 80))) γ' ≤ k.val ∧
                k.val < 18 * _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
                  (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
                  (QRegExt.idReg (fullSysCoreWires 80))) γ' + 18) := by
            rwa [hIdx]
          rw [NuclearTwistRealizes.dite_neg_eq hk1', NuclearTwistRealizes.dite_neg_eq hk1]
          exact Function.update_of_ne hkTh _ _
    · have hcond' : ¬(NuclearTwistRealizes.barrelActive true γ' = true ∧
          _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
            (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
            (QRegExt.idReg (fullSysCoreWires 80))) γ' < 218) := by
        rwa [hAct, hIdx]
      rw [NuclearTwistRealizes.dite_neg_eq hcond', NuclearTwistRealizes.dite_neg_eq hcond]
      exact Function.update_of_ne hkTh _ _

theorem qft_fastCutUVepTwistRef_comm_uXThCore (qft : FullSysQft654Bundle)
    (cfg : Configuration) : (fullSysQftCoreUnitary pos24_6_le_80 qft * fastCutUVepTwistRef
    pos24_22_le_80 cfg).1 * uXThCore.1 = uXThCore.1 * (fullSysQftCoreUnitary pos24_6_le_80
    qft * fastCutUVepTwistRef pos24_22_le_80 cfg).1 := by
  apply matrix_ext_of_ket_core; intro γ
  let γ' := Function.update γ wThCore (γ wThCore + 1)
  let β := mscBarrelBitFn true pos24_22_le_80 γ
  let β' := Function.update β wThCore (β wThCore + 1)
  have hβ' : mscBarrelBitFn true pos24_22_le_80 γ' = β' := mscBarrelBitFn_update_wThCore γ
  have hOutβ : ∀ q : Wire (fullSysCoreWires 80), q.val < 3976 → β' q = β q := fun q hq ↦
    Function.update_of_ne (fun h ↦ by have hv : q.val = 3985 := congrArg Fin.val h; omega) _ _
  have hvEq : ProjZ512QftAndTwist288.vepHighNuc pos24_22_le_80 β' =
      ProjZ512QftAndTwist288.vepHighNuc pos24_22_le_80 β := by
    apply Bool.eq_iff_iff.mpr
    rw [ProjZ512QftAndTwist288.vepHighNuc_iff, ProjZ512QftAndTwist288.vepHighNuc_iff]
    have hc0 : NuclearTwistRealizes.coin0Active β' = NuclearTwistRealizes.coin0Active β := by
      unfold NuclearTwistRealizes.coin0Active
      rw [hOutβ _ (by decide), hOutβ _ (by decide), hOutβ _ (by decide)]
    have hrn : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore
      pos24_22_le_80) β' =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80)
          β :=
      PosSlots24SemanticOracleConcrete80.regVal_eq_of_wire_eq _ β' β
        fun i ↦ hOutβ _ (by have := (msc_rNucCore_in_range i).2; omega)
    rw [hc0]; exact and_congr_right fun _ ↦ by rw [hrn]
  have hwEq : wCutAxes pos24_22_le_80 β' = wCutAxes pos24_22_le_80 β := by
    funext w; unfold wCutAxes
    have hc0 : NuclearTwistRealizes.coin0Active β' = NuclearTwistRealizes.coin0Active β := by
      unfold NuclearTwistRealizes.coin0Active
      rw [hOutβ _ (by decide), hOutβ _ (by decide), hOutβ _ (by decide)]
    have hcs : ProjZ512QftAndTwist288.extractCosetP3 pos24_22_le_80 β' w =
        ProjZ512QftAndTwist288.extractCosetP3 pos24_22_le_80 β w := by
      apply Fin.ext; dsimp [ProjZ512QftAndTwist288.extractCosetP3]
      exact congrArg ZMod.val (hOutβ _ (by revert w; decide))
    rw [hc0, hcs]
  have hMscComm : (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUVepTwistRest pos24_22_le_80
      cfg).1.mulVec (ket β') = uXThCore.1.mulVec ((fullSysQftCoreUnitary pos24_6_le_80 qft *
      mscUVepTwistRest pos24_22_le_80 cfg).1.mulVec (ket β)) := by
    rw [← hβ', ← origTwist_mul_assoc_ket pos24_6_le_80 pos24_22_le_80 (mscUBarrelCore true
      pos24_22_le_80) (mscBarrelBitFn true pos24_22_le_80) (mscUBarrelCore_mulVec_ket true
      pos24_22_le_80) qft cfg γ', ← origTwist_mul_assoc_ket pos24_6_le_80 pos24_22_le_80
      (mscUBarrelCore true pos24_22_le_80) (mscBarrelBitFn true pos24_22_le_80)
      (mscUBarrelCore_mulVec_ket true pos24_22_le_80) qft cfg γ, ← mscUVepTwistRef_eq_mul
      pos24_22_le_80 cfg]
    have hCommU : (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUVepTwistRef pos24_22_le_80
        cfg).1 * uXThCore.1 = uXThCore.1 * (fullSysQftCoreUnitary pos24_6_le_80 qft *
        mscUVepTwistRef pos24_22_le_80 cfg).1 := msc_mul2_comm _ _ uXThCore.1
        (fullSysQftCoreUnitary_comm_uXThCore qft) (mscUVepTwistRef_comm_uXThCore cfg)
    change (fullSysQftCoreUnitary pos24_6_le_80 qft *
        mscUVepTwistRef pos24_22_le_80 cfg).1.mulVec (ket γ') = _
    rw [show ket γ' = uXThCore.1.mulVec (ket γ) from (mbh_ket_uXThCore γ).symm,
      Matrix.mulVec_mulVec, hCommU, ← Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_uXThCore]
  change (fullSysQftCoreUnitary pos24_6_le_80 qft *
      fastCutUVepTwistRef pos24_22_le_80 cfg).1.mulVec (ket γ') = _
  rw [fastCutUVepTwistRef_eq_gen pos24_22_le_80 cfg, genCutUVepTwistRef_mul_assoc_ket pos24_6_le_80
    pos24_22_le_80 (mscUBarrelCore true pos24_22_le_80) (mscBarrelBitFn true pos24_22_le_80)
    (mscUBarrelCore_mulVec_ket true pos24_22_le_80) qft cfg γ', genCutUVepTwistRef_mul_assoc_ket
    pos24_6_le_80 pos24_22_le_80 (mscUBarrelCore true pos24_22_le_80) (mscBarrelBitFn true
    pos24_22_le_80) (mscUBarrelCore_mulVec_ket true pos24_22_le_80) qft cfg γ, hβ',
    qft_uVepTwistRestCut_mulVec_ket pos24_6_le_80 pos24_22_le_80 qft cfg β',
    qft_uVepTwistRestCut_mulVec_ket pos24_6_le_80 pos24_22_le_80 qft cfg β, hvEq, hwEq]
  by_cases hv : ProjZ512QftAndTwist288.vepHighNuc pos24_22_le_80 β
  · rw [MergedVepCoreSliceClosureGen.msc_ite_pos hv,
        MergedVepCoreSliceClosureGen.msc_ite_pos hv, hMscComm]
  · rw [MergedVepCoreSliceClosureGen.msc_ite_neg hv,
        MergedVepCoreSliceClosureGen.msc_ite_neg hv, hMscComm,
        Matrix.mulVec_mulVec, uProjAxes3D_comm_uXThCore, ← Matrix.mulVec_mulVec]

theorem topCoin_fastCut_lhs_mod4_eq_realMod4
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (V_eff : Unitary (2 ^ (selWiresSym 80))) (s0 : Bool)
    (hSupp : ∀ b : Fin (2 ^ (selWiresSym 80)),
      b ∉ Set.range (ancIdx86 s0) →
        V_eff.1 b (coinSelOutcome (selCoin3Sym 80) (if s0 then 1 else 0)) = 0)
    (hTh : ∀ p : BitAssignment 80,
      V_eff.1 (ancIdx86 s0 (Function.update p idxTh80 (p idxTh80 + 1)))
          (coinSelOutcome (selCoin3Sym 80) (if s0 then 1 else 0)) =
        V_eff.1 (ancIdx86 s0 p)
          (coinSelOutcome (selCoin3Sym 80) (if s0 then 1 else 0))) :
    let a_c := coinSelOutcome (selCoin3Sym 80) (if s0 then 1 else 0)
    let P_anc := (coreAncSym 80).basisOutcomeProjector a_c
    let U_out := fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft *
      fastCutUVepTwistRef pos24_22_le_80 cfg
    let U_mod4 := conjSwapCore3967
      (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhaseMod4 true pos24TailSign tM))
    let U_real := conjSwapCore3967
      (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhaseRealMod4 true pos24TailSign tM))
    P_anc * (((coreAncSym 80).embedMatrix V_eff.1)ᴴ *
        (coreUnitarySym (unitaryConj U_out U_mod4)).1 *
        (coreAncSym 80).embedMatrix V_eff.1) * P_anc =
      P_anc * (((coreAncSym 80).embedMatrix V_eff.1)ᴴ *
        (coreUnitarySym (unitaryConj U_out U_real)).1 *
        (coreAncSym 80).embedMatrix V_eff.1) * P_anc := by
  intro a_c P_anc U_out U_mod4 U_real
  have hP_sa : P_ancᴴ = P_anc := QRegister.basisOutcomeProjector_conjTranspose _ _
  let W₀ : Operator (2 ^ posCoreWires) := (coreAncSym 80).embedMatrix V_eff.1 * P_anc
  let T : Operator (2 ^ posCoreWires) := uSwapCore3967.1 * U_out.1
  let W : Operator (2 ^ posCoreWires) := T * W₀
  have hXW₀ : uXThCore.1 * W₀ = W₀ := uXThCore_mul_embedAnc_proj_eq V_eff s0 a_c hSupp hTh
  have hXUout : uXThCore.1 * U_out.1 = U_out.1 * uXThCore.1 :=
    (qft_fastCutUVepTwistRef_comm_uXThCore qft cfg).symm
  have hXT : uXThCore.1 * T = T * uXThCore.1 := by
    dsimp only [T]
    rw [← Matrix.mul_assoc, uSwapCore3967_comm_uXThCore.symm, Matrix.mul_assoc, hXUout,
      ← Matrix.mul_assoc]
  have hXW : uXThCore.1 * W = W := by
    dsimp only [W]; rw [← Matrix.mul_assoc, hXT, Matrix.mul_assoc, hXW₀]
  have hSw_sa : uSwapCore3967.1ᴴ = uSwapCore3967.1 :=
    PosPostPrep80MergedVep.uSwapCore3967_conjTranspose
  have hSandwich : ∀ (Ph : Unitary (2 ^ posCoreWires)),
      P_anc * (((coreAncSym 80).embedMatrix V_eff.1)ᴴ *
        (coreUnitarySym (unitaryConj U_out
          (conjSwapCore3967 (castUnitaryPow2 pos24_coreWires80_eq.symm Ph)))).1 *
        (coreAncSym 80).embedMatrix V_eff.1) * P_anc =
      Wᴴ * Ph.1 * W := fun Ph ↦ by
    have hCoreVal : (coreUnitarySym (unitaryConj U_out
        (conjSwapCore3967 (castUnitaryPow2 pos24_coreWires80_eq.symm Ph)))).1 =
        U_out.1ᴴ * (uSwapCore3967.1 * Ph.1 * uSwapCore3967.1) * U_out.1 := rfl
    have hWH : Wᴴ = P_anc * ((coreAncSym 80).embedMatrix V_eff.1)ᴴ * U_out.1ᴴ * uSwapCore3967.1 :=
      by
      dsimp only [W, T, W₀]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP_sa,
        hSw_sa]
      simp only [Matrix.mul_assoc]
    rw [hCoreVal, hWH]; dsimp only [W, T, W₀]; simp only [Matrix.mul_assoc]
  rw [hSandwich (uPosPhaseMod4 true pos24TailSign tM), hSandwich (uPosPhaseRealMod4 true
    pos24TailSign tM)]
  exact conj_eq_of_one_add_inv_mul_eq uXThCore.1
    (uPosPhaseMod4 true pos24TailSign tM).1 (uPosPhaseRealMod4 true pos24TailSign tM).1
    W uXThCore_sa hXW (one_add_uXThCore_mul_uPosPhaseMod4_eq true pos24TailSign tM)

theorem uPosPhaseRealMod4_swap12_comm_uProjAxes3D (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (W : Fin 3 → Unitary 256) : (conjSwapCore3967 (castUnitaryPow2 pos24_coreWires80_eq.symm
    (uPosPhaseRealMod4 true pos24TailSign tM))).1 * (uProjAxes3D 80 W).1 =
    (uProjAxes3D 80 W).1 * (conjSwapCore3967 (castUnitaryPow2 pos24_coreWires80_eq.symm
    (uPosPhaseRealMod4 true pos24TailSign tM))).1 := by
  let U_raw := uPosPhaseRealMod4 true pos24TailSign tM
  let φ := posPhaseBitMod4 true pos24TailSign tM
  have hRawKet : ∀ η : BitAssignment (fullSysCoreWires 80),
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) =
        (if φ η then (-1 : ℂ) else 1) • ket η :=
    fun η ↦ PosSlots24BranchConcrete.ket_diagonalSignUnitaryN φ η
  have hRealKet := conjSwapCore3967_raw_hUPosKet U_raw φ hRawKet
  refine ketDiag_comm_uProjAxes3D_of_outside_proj24 _
    (fun γ ↦ if φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) ⟨12, by decide⟩ γ) then (-1 : ℂ) else 1)
    hRealKet (fun γ₁ γ₂ h ↦ ?_) W
  have hbit : φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) ⟨12, by decide⟩ γ₁) =
      φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) ⟨12, by decide⟩ γ₂) := by
    refine posPhaseBitMod4_eq_of_eq_active true pos24TailSign tM _ _ fun q hq ↦ ?_
    let q80 : Wire (fullSysCoreWires 80) := ⟨q.val, q.isLt⟩
    let qSw := Equiv.swap (mWCore3967Gen (le_rfl : 80 ≤ 80))
      (mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩) q80
    change γ₁ qSw = γ₂ qSw
    refine h qSw ?_
    by_cases h1 : q80 = mWCore3967Gen (le_rfl : 80 ≤ 80)
    · dsimp only [qSw]; rw [h1, Equiv.swap_apply_left]; exact Or.inr (by decide)
    · by_cases h2 : q80 = mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩
      · dsimp only [qSw]; rw [h2, Equiv.swap_apply_right]; exact Or.inr (by decide)
      · dsimp only [qSw]; rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        have : q80.val = q.val := rfl
        omega
  rw [hbit]

theorem mod4Real_conj_comm_rAncFlag80
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (uTw : Unitary (2 ^ (fullSysCoreWires 80)))
    (hTwComm : ∀ a : Fin (2 ^ 86),
      uTw.1 * rAncFlag80.basisOutcomeProjector a =
        rAncFlag80.basisOutcomeProjector a * uTw.1)
    (qft : FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft) (a : Fin (2 ^ 86)) :
    let U_real := conjSwapCore3967
      (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhaseRealMod4 true pos24TailSign tM))
    (unitaryConj
      (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft * uTw)
      U_real).1 * rAncFlag80.basisOutcomeProjector a =
    rAncFlag80.basisOutcomeProjector a *
      (unitaryConj
        (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft * uTw)
        U_real).1 := by
  intro U_real
  let U_raw := uPosPhaseRealMod4 true pos24TailSign tM
  let φ := posPhaseBitMod4 true pos24TailSign tM
  have hRawKet : ∀ η : BitAssignment (fullSysCoreWires 80),
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) =
        (if φ η then (-1 : ℂ) else 1) • ket η :=
    fun η ↦ PosSlots24BranchConcrete.ket_diagonalSignUnitaryN φ η
  have hRealKet := conjSwapCore3967_raw_hUPosKet U_raw φ hRawKet
  have hRealDiag : U_real.1 =
      Matrix.diagonal (fun u : Fin (2 ^ (fullSysCoreWires 80)) ↦
        if φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) ⟨12, by decide⟩
          (basisBits (fullSysCoreWires 80) u))
        then (-1 : ℂ) else 1) := by
    apply matrix_ext_of_ket_core; intro β
    rw [hRealKet β,
        msc_diagonal_mulVec_ket
          (fun γ ↦ if φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) ⟨12, by decide⟩ γ)
            then (-1 : ℂ) else 1) β]
  have hPhP : U_real.1 * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * U_real.1 := by
    rw [hRealDiag, QRegister.basisOutcomeProjector_eq_diagonal]
    exact PosSlots24SemanticOracleConcrete80.diagonal_comm_diagonal _ _
  rw [unitaryConj_val, Submonoid.coe_mul]
  exact conj_comm_of_parts_comm (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl
    : 80 ≤ 80)) qft).1 uTw.1 U_real.1 (rAncFlag80.basisOutcomeProjector a)
    (QRegister.basisOutcomeProjector_conjTranspose _ _) (msc_qft_comm_rAncFlag80 qft hQft a)
    (hTwComm a) hPhP

theorem fastCut_mod4_coreIdx_entry_eq_msc
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft)
    (cfg : Configuration) (s0 : Bool) (p : BitAssignment 80)
    (x' x : Fin (2 ^ systemQubits)) :
    let U_real := conjSwapCore3967
      (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhaseRealMod4 true pos24TailSign tM))
    (coreUnitarySym
      (unitaryConj
        (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft *
          fastCutUVepTwistRef pos24_22_le_80 cfg)
        U_real)).1
        (coreIdxOf hkSym80 s0 p x') (coreIdxOf hkSym80 s0 p x) =
    (coreUnitarySym
      (unitaryConj
        (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft *
          mscUVepTwistRef pos24_22_le_80 cfg)
        U_real)).1
        (coreIdxOf hkSym80 s0 p x') (coreIdxOf hkSym80 s0 p x) := by
  intro U_real
  have hCutEntry := msc_transport_entry_of_comm _
    (mod4Real_conj_comm_rAncFlag80 tM (fastCutUVepTwistRef pos24_22_le_80 cfg)
      (fastCutUVepTwistRef_comm_rAncFlag80 cfg) qft hQft) s0 p x' x
  have hOrigEntry := msc_transport_entry_of_comm _
    (mod4Real_conj_comm_rAncFlag80 tM (mscUVepTwistRef pos24_22_le_80 cfg)
      (msc_uVepTwistRef_comm_rAncFlag80 cfg) qft hQft) s0 p x' x
  rw[hCutEntry, hOrigEntry, fastCutUVepTwistRef_eq_gen pos24_22_le_80 cfg, mscUVepTwistRef_eq_mul
    pos24_22_le_80 cfg, unitaryConj_val, unitaryConj_val, msc_conj3_entry_eq_dotProduct,
    msc_conj3_entry_eq_dotProduct]
  let bFn := mscBarrelBitFn true pos24_22_le_80
  let γ' := bFn (mscCoreBeta s0 p x')
  let γ := bFn (mscCoreBeta s0 p x)
  have hhi : ∀ q : Wire (fullSysCoreWires 80), 3948 ≤ q.val → γ' q = γ q := fun q hq ↦
      (mscBarrelBitFn_high_eq true pos24_22_le_80 _ q hq).trans ((mscCoreBeta_high_eq s0 p x'
      x q hq).trans (mscBarrelBitFn_high_eq true pos24_22_le_80 _ q hq).symm)
  have hvEq : ProjZ512QftAndTwist288.vepHighNuc pos24_22_le_80 γ' =
      ProjZ512QftAndTwist288.vepHighNuc pos24_22_le_80 γ := by
    apply Bool.eq_iff_iff.mpr
    rw [ProjZ512QftAndTwist288.vepHighNuc_iff, ProjZ512QftAndTwist288.vepHighNuc_iff]
    have hc0 : NuclearTwistRealizes.coin0Active γ' = NuclearTwistRealizes.coin0Active γ := by
      unfold NuclearTwistRealizes.coin0Active
      rw [hhi _ (by decide), hhi _ (by decide), hhi _ (by decide)]
    have hrn : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore
      pos24_22_le_80) γ' =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80)
          γ :=
      PosSlots24SemanticOracleConcrete80.regVal_eq_of_wire_eq _ γ' γ
        fun i ↦ hhi _ (by have := (msc_rNucCore_in_range i).1; omega)
    rw [hc0]; exact and_congr_right fun _ ↦ by rw [hrn]
  have hwEq : wCutAxes pos24_22_le_80 γ' = wCutAxes pos24_22_le_80 γ :=
    wCutAxes_eq_of_high_eq pos24_22_le_80 hhi
  rw [genCutUVepTwistRef_mul_assoc_ket pos24_6_le_80 pos24_22_le_80 (mscUBarrelCore true
    pos24_22_le_80) bFn (mscUBarrelCore_mulVec_ket true pos24_22_le_80) qft cfg (mscCoreBeta s0 p
    x'), genCutUVepTwistRef_mul_assoc_ket pos24_6_le_80 pos24_22_le_80 (mscUBarrelCore true
    pos24_22_le_80) bFn (mscUBarrelCore_mulVec_ket true pos24_22_le_80) qft cfg (mscCoreBeta s0 p
    x), origTwist_mul_assoc_ket pos24_6_le_80 pos24_22_le_80 (mscUBarrelCore true pos24_22_le_80)
    bFn (mscUBarrelCore_mulVec_ket true pos24_22_le_80) qft cfg (mscCoreBeta s0 p x'),
    origTwist_mul_assoc_ket pos24_6_le_80 pos24_22_le_80 (mscUBarrelCore true pos24_22_le_80) bFn
    (mscUBarrelCore_mulVec_ket true pos24_22_le_80) qft cfg (mscCoreBeta s0 p x),
    qft_uVepTwistRestCut_mulVec_ket pos24_6_le_80 pos24_22_le_80 qft cfg γ',
    qft_uVepTwistRestCut_mulVec_ket pos24_6_le_80 pos24_22_le_80 qft cfg γ, hvEq, hwEq]
  by_cases hv : ProjZ512QftAndTwist288.vepHighNuc pos24_22_le_80 γ
  · rw [MergedVepCoreSliceClosureGen.msc_ite_pos hv, MergedVepCoreSliceClosureGen.msc_ite_pos hv]
  · rw [MergedVepCoreSliceClosureGen.msc_ite_neg hv, MergedVepCoreSliceClosureGen.msc_ite_neg hv]
    exact msc_dotProduct_unitary_cancel (uProjAxes3D 80 (wCutAxes pos24_22_le_80 γ)) U_real.1 _ _
      (uPosPhaseRealMod4_swap12_comm_uProjAxes3D tM (wCutAxes pos24_22_le_80 γ))

theorem fastCutMergedVepTopCoin0_80_of_mod4
    (tM : Fin orbitCount47905 → Fin (2 ^ 30)) {mWorkPos : ℕ} (hm : 22 ≤ 80)
    (qft : FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft) (cfg : Configuration)
    (post : PosPostPrepCert 80) (V_eff : Unitary (2 ^ (selWiresSym 80)))
    (hVeff : post.uPosPost * coreHadamardUnitary 80 = (coreAncSym 80).embedUnitary V_eff)
    (hSupp0 : ∀ b : Fin (2 ^ (selWiresSym 80)),
      b ∉ Set.range (ancIdx86 false) → V_eff.1 b (coinSelOutcome (selCoin3Sym 80) 0) = 0)
    (hScrClean : ∀ p : BitAssignment 80,
      ‖V_eff.1 (ancIdx86 false p) (coinSelOutcome (selCoin3Sym 80) 0)‖ ^ 2 ≠ 0 →
        p ⟨75, by decide⟩ = 0)
    (hTh0 : ∀ p : BitAssignment 80,
      V_eff.1 (ancIdx86 false (Function.update p idxTh80 (p idxTh80 + 1)))
          (coinSelOutcome (selCoin3Sym 80) 0) =
        V_eff.1 (ancIdx86 false p) (coinSelOutcome (selCoin3Sym 80) 0))
    (μ0 : BitAssignment 80 → ℝ)
    (hμ0 : ∀ p : BitAssignment 80,
      ‖V_eff.1 (ancIdx86 false p) (coinSelOutcome (selCoin3Sym 80) 0)‖ ^ 2 = μ0 p)
    (posData : PosSlots24DataGen (fullSysCoreWires 80) (iSlot2 80) mWorkPos)
    (hUPos : posData.uPosPhase cfg =
      conjSwapCore3967
        (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhaseMod4 true pos24TailSign tM))) :
    topCoinPropGen (le_rfl : 80 ≤ 80) qft cfg post (uVepTwistCutRef hm) posData 0
      (mergedCoherentOp80Mod4Of tM qft cfg μ0) := by
  rw [uVepTwistCutRef_pf_congr hm pos24_22_le_80]
  refine topCoinPropGen_of_collapse (le_rfl : 80 ≤ 80) qft cfg post V_eff
    (fastCutUVepTwistRef pos24_22_le_80) posData 0
    (mergedCoherentOp80Mod4Of tM qft cfg μ0) hVeff ?_
  dsimp only
  have hLhs0 := topCoin_fastCut_lhs_mod4_eq_realMod4 tM qft cfg V_eff false hSupp0 hTh0
  dsimp only at hLhs0
  have hite0 : (if false = true then (1 : Fin 8) else 0) = 0 := rfl
  rw [hite0] at hLhs0
  rw [hUPos, hLhs0]
  let U_raw := uPosPhaseRealMod4 true pos24TailSign tM
  let φ := posPhaseBitMod4 true pos24TailSign tM
  have hRawKet : ∀ η : BitAssignment (fullSysCoreWires 80),
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) =
        (if φ η then (-1 : ℂ) else 1) • ket η :=
    fun η ↦ PosSlots24BranchConcrete.ket_diagonalSignUnitaryN φ η
  let U_out := fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft *
    fastCutUVepTwistRef pos24_22_le_80 cfg
  let U_real := conjSwapCore3967 (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw)
  have hSwap0 := msc_phaseBit_swap_coin0_gen φ
    (posPhaseBitMod4_eq_of_coin0 pos24TailSign tM) ⟨12, by decide⟩
  have hCollapse := MergedVepTopCoinCollapse.ancBlockCollapse_symbolic_onRange
    (coreSysSym 80) (coreAncSym 80) (coinSelOutcome (selCoin3Sym 80) 0)
    (ancIdx86 false) (ancIdx86_injective false)
    (fun p z ↦ coreIdxOf hkSym80 false p z)
    (pos80_coreIdxOf_extract_sys false) (pos80_coreIdxOf_extract_anc false)
    (pos80_coreIdxOf_uniq false) pos80_coreAnc_agreeOutside_iff
    (pos80_coreSys_agreeOutside (coinSelOutcome (selCoin3Sym 80) 0))
    V_eff hSupp0 (coreUnitarySym (unitaryConj U_out U_real)).1
    (fun j p x hne _ ↦ msc_transport_hDiag_of_comm _
      (mod4Real_conj_comm_rAncFlag80 tM (fastCutUVepTwistRef pos24_22_le_80 cfg)
        (fastCutUVepTwistRef_comm_rAncFlag80 cfg) qft hQft) false j p x hne)
    (fun p ↦ mergedSliceGen (fun c' p' ↦ sysBlock80Mod4Of tM qft c' false p') cfg p)
    (fun p x' x hnz ↦ (fastCut_mod4_coreIdx_entry_eq_msc tM qft hQft cfg false p x' x).trans
      (mergedVepCore_hBlk0_gen U_raw φ hRawKet qft hQft cfg ⟨12, by decide⟩ hSwap0 U_real
        (conjSwapCore3967_raw_hUPosKet U_raw φ hRawKet) p
        (hScrClean p (pow_ne_zero 2 (norm_ne_zero_iff.mpr hnz))) x' x))
  have hSumEq : (∑ p : BitAssignment 80, ((‖V_eff.1 (ancIdx86 false p) (coinSelOutcome
      (selCoin3Sym 80) 0)‖ ^ 2 : ℝ) : ℂ) • mergedSliceGen (fun c' p' ↦ sysBlock80Mod4Of tM qft
      c' false p') cfg p) = mergedCoherentOp80Mod4Of tM qft cfg μ0 :=
    Finset.sum_congr rfl fun p _ ↦ by rw [hμ0 p]
  rw [hSumEq] at hCollapse; exact hCollapse

theorem fastCutMergedVepTopCoin1_80_of_mod4 (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    {mWorkPos : ℕ} (hm : 22 ≤ 80) (qft : FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft)
    (cfg : Configuration) (post : PosPostPrepCert 80) (V_eff : Unitary (2 ^ (selWiresSym 80)))
    (hVeff : post.uPosPost * coreHadamardUnitary 80 = (coreAncSym 80).embedUnitary V_eff)
    (hSupp1 : ∀ b : Fin (2 ^ (selWiresSym 80)), b ∉ Set.range (ancIdx86 true) → V_eff.1 b
    (coinSelOutcome (selCoin3Sym 80) 1) = 0) (hTh1 : ∀ p : BitAssignment 80, V_eff.1 (ancIdx86
    true (Function.update p idxTh80 (p idxTh80 + 1))) (coinSelOutcome (selCoin3Sym 80) 1) =
    V_eff.1 (ancIdx86 true p) (coinSelOutcome (selCoin3Sym 80) 1)) (μ1 : BitAssignment 80 → ℝ)
    (hμ1 : ∀ p : BitAssignment 80, ‖V_eff.1 (ancIdx86 true p) (coinSelOutcome (selCoin3Sym 80)
    1)‖ ^ 2 = μ1 p) (posData : PosSlots24DataGen (fullSysCoreWires 80) (iSlot2 80) mWorkPos)
    (hUPos : posData.uPosPhase cfg = conjSwapCore3967 (castUnitaryPow2
    pos24_coreWires80_eq.symm (uPosPhaseMod4 true pos24TailSign tM))) : topCoinPropGen
    (le_rfl : 80 ≤ 80) qft cfg post (uVepTwistCutRef hm) posData 1
    (coherentSysOp80Mod4Of tM qft cfg true μ1) := by
  rw [uVepTwistCutRef_pf_congr hm pos24_22_le_80]
  refine topCoinPropGen_of_collapse (le_rfl : 80 ≤ 80) qft cfg post V_eff
    (fastCutUVepTwistRef pos24_22_le_80) posData 1
    (coherentSysOp80Mod4Of tM qft cfg true μ1) hVeff ?_
  dsimp only
  have hLhs1 := topCoin_fastCut_lhs_mod4_eq_realMod4 tM qft cfg V_eff true hSupp1 hTh1
  dsimp only at hLhs1
  have hite1 : (if true = true then (1 : Fin 8) else 0) = 1 := rfl
  rw [hite1] at hLhs1
  rw [hUPos, hLhs1]
  let U_raw := uPosPhaseRealMod4 true pos24TailSign tM
  let φ := posPhaseBitMod4 true pos24TailSign tM
  have hRawKet : ∀ η : BitAssignment (fullSysCoreWires 80),
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) =
        (if φ η then (-1 : ℂ) else 1) • ket η :=
    fun η ↦ PosSlots24BranchConcrete.ket_diagonalSignUnitaryN φ η
  let U_out := fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft *
    fastCutUVepTwistRef pos24_22_le_80 cfg
  let U_real := conjSwapCore3967 (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw)
  have hSwap1 := msc_phaseBit_swap_coin1_gen φ
    (msc_posPhaseBitMod4_eq_of_coin1 pos24TailSign tM) ⟨12, by decide⟩
  have hCollapse := MergedVepTopCoinCollapse.ancBlockCollapse_symbolic_onRange
    (coreSysSym 80) (coreAncSym 80) (coinSelOutcome (selCoin3Sym 80) 1)
    (ancIdx86 true) (ancIdx86_injective true)
    (fun p z ↦ coreIdxOf hkSym80 true p z)
    (pos80_coreIdxOf_extract_sys true) (pos80_coreIdxOf_extract_anc true)
    (pos80_coreIdxOf_uniq true) pos80_coreAnc_agreeOutside_iff
    (pos80_coreSys_agreeOutside (coinSelOutcome (selCoin3Sym 80) 1))
    V_eff hSupp1 (coreUnitarySym (unitaryConj U_out U_real)).1
    (fun j p x hne _ ↦ msc_transport_hDiag_of_comm _
      (mod4Real_conj_comm_rAncFlag80 tM (fastCutUVepTwistRef pos24_22_le_80 cfg)
        (fastCutUVepTwistRef_comm_rAncFlag80 cfg) qft hQft) true j p x hne)
    (fun p ↦ sysBlock80Mod4Of tM qft cfg true p)
    (fun p x' x _ ↦ (fastCut_mod4_coreIdx_entry_eq_msc tM qft hQft cfg true p x' x).trans
      (mergedVepCore_hBlk1_gen U_raw φ hRawKet qft hQft cfg ⟨12, by decide⟩ hSwap1 U_real
        (conjSwapCore3967_raw_hUPosKet U_raw φ hRawKet) p x' x))
  have hSumEq : (∑ p : BitAssignment 80, ((‖V_eff.1 (ancIdx86 true p) (coinSelOutcome
      (selCoin3Sym 80) 1)‖ ^ 2 : ℝ) : ℂ) • sysBlock80Mod4Of tM qft cfg true p) =
      coherentSysOp80Mod4Of tM qft cfg true μ1 :=
    Finset.sum_congr rfl fun p _ ↦ by rw [hμ1 p]
  rw [hSumEq] at hCollapse; exact hCollapse

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512
set_option exponentiation.threshold 256

end ConfigPerHorizonPert
end PerHorizonPert
end
set_option exponentiation.threshold 256
end PerHorizonPert

section Leaf3Slot3ZRetOuter
local instance (priority := 1000000) instNeZeroTwoPow_Leaf3Slot3ZRetOuter (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace Leaf3Slot3ZRetOuter

section ConfigLeaf3Slot3ZRetOuter

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option exponentiation.threshold 256

local instance (priority := 10) instLoc_Leaf3Slot3ZRetOuter_1InstNeZeroTwoPowRetOute (k : ℕ) :
  NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux.SpecMirror
open StepBBlock0 Prod57BoothHoist
open StepBOuter Slot3Exact216Oracle80
open Slot3Outer2344AndRelayWide
open Slot3Outer2344AndRelayWide.PosPhase246
open Slot3Outer2344AndRelayWide.Slot3Exact216AsymUncomp
open Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore
  (vsAnd5In216W magUnpack63_275 magUnpack63_275_spec)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide
open Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned
  (InvRevTailPruned216_congr
   dCliffXorAndPairsUncomp
   cAxisRevPre7 axRevLhs7 axRevRhs7 axRevAcc7 axRevLhs7_ne_rhs7
   axCtxRev7_275 dInnerAxisRev dAxisStep1Rev_275 dAxisStep3Rev_275)
open Slot3Outer2344AndRelayWide.Slot3Retained15522_Core
  (muXorPre2Ctx muHole2Cliff mu0Lhs2 mu0Rhs2 mu12Lhs2 mu12Rhs2 mu12Acc2 mu12_hlr
   dMuInner2_0 dMuXorRev2_275 dCoinMuRev3_275)
open MomSlots35Slot3ProjNuclear (shellMagCoord3)
open Slot3ZRetCore
open True18Compact99
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36CoreWide
open InterWalkRSum42Hoist (qreg_ext)
open Leaf3Slot3ZRet193 (ValidSwapRelayWM isBadXM StepBundleW stepBundleW_of_relayWM_static putQZ
  clearPreMKCtrl clearPreMKCat clearPreMKOfTopW cleanRem_putQZ cliff_not_mem_support_of_lt
  p57ToDynWith_not_mem_support_of_lt dXorAndPairsUncomp_not_mem_support_of_lt
  czVecCircuit_not_mem_support dZeroTUncomp1_not_mem_support dMagInnerLoop_not_mem_support_of_lt)

/-- Unified involutive wire relay mapping clean retained wires `[201 .. 201 + (374 - topW))`
onto `[topW .. 374)` for `324 ≤ topW ∧ topW ≤ 374` (`topW ∈ {328, 339, 342}`). -/
def swap374 (topW x : ℕ) : ℕ := if 201 ≤ x ∧ x < 201 + (374 - topW) then topW + (x - 201) else
    if topW ≤ x ∧ x < 374 then 201 + (x - topW) else x

/-- Bad-wire predicate for `swap374 topW`, marking `[201 .. 201 + (374 - topW))`. -/
def isBad374 (topW x : ℕ) : Bool := decide (201 ≤ x ∧ x < 201 + (374 - topW))

theorem swap374_involutive {topW : ℕ} (hlo : 324 ≤ topW) (hhi : topW ≤ 374) (x : ℕ) :
    swap374 topW (swap374 topW x) = x := by
  unfold swap374
  split_ifs with h1 h2 h3 h4 h5 <;> omega

theorem swap374_bad_ge_topW {topW x : ℕ} (hlo : 324 ≤ topW) (hhi : topW ≤ 374)
    (hbad : isBad374 topW x = true) : topW ≤ swap374 topW x ∧ swap374 topW x < 374 := by
  simp only [isBad374, decide_eq_true_eq] at hbad
  unfold swap374
  (split_ifs; omega)

theorem swap374_out_lt_topW {topW x : ℕ} (hlo : 324 ≤ topW) (hhi : topW ≤ 374)
    (hge : topW ≤ x) (hlt : x < 374) :
    isBad374 topW (swap374 topW x) = true ∧ swap374 topW x < topW := by
  simp only [isBad374, decide_eq_true_eq]
  unfold swap374
  split_ifs <;> omega

theorem swap374_fix_good {topW x : ℕ} (_hlo : 324 ≤ topW) (_hhi : topW ≤ 374)
    (hgood : isBad374 topW x = false) (hlt : x < topW) : swap374 topW x = x := by
  simp only [isBad374, decide_eq_false_iff_not] at hgood
  unfold swap374
  split_ifs <;> omega

theorem swap374_lt_437 {topW x : ℕ} (hlo : 324 ≤ topW) (hhi : topW ≤ 374) (hx : x < 437) :
    swap374 topW x < 437 := by
  unfold swap374
  split_ifs <;> omega

/-- Bundled `Wire 437` relay permutation for `swap374 topW` (`324 ≤ topW ≤ 374`). -/
def swap374W (topW : ℕ) (hlo : 324 ≤ topW) (hhi : topW ≤ 374) (w : Wire 437) : Wire 437 :=
  ⟨swap374 topW w.val, swap374_lt_437 hlo hhi w.isLt⟩

/-- Bundled `Wire 437` bad-wire mask for `isBad374 topW`. -/
def isBad374W (topW : ℕ) (w : Wire 437) : Bool := isBad374 topW w.val

theorem validSwapRelayWM_374 {topW : ℕ} (hlo : 324 ≤ topW) (hhi : topW ≤ 374) :
    ValidSwapRelayWM topW 374 (swap374W topW hlo hhi) (isBad374W topW) where
  h275 := by omega
  htopM := hhi
  hM437 := by decide
  invol w := Fin.ext (swap374_involutive hlo hhi w.val)
  fix_ge_M w hw := Fin.ext (by dsimp only [swap374W]; unfold swap374; split_ifs <;> omega)
  fix_not_bad_lt w hlt hnb := Fin.ext (swap374_fix_good hlo hhi hnb hlt)
  bad_lt275 w hb := by
    simp only [isBad374W, isBad374, decide_eq_true_eq] at hb; omega
  bad_swap_range w := by
    constructor
    · exact swap374_bad_ge_topW hlo hhi
    · rintro ⟨h1, h2⟩
      have h := (swap374_out_lt_topW hlo hhi h1 h2).1
      have hinv : swap374 topW (swap374 topW w.val) = w.val := swap374_involutive hlo hhi w.val
      dsimp only [isBad374W]; dsimp only [swap374W] at h; rwa [hinv] at h
  range_swap_bad w := by
    constructor
    · exact fun ⟨h1, h2⟩ ↦ (swap374_out_lt_topW hlo hhi h1 h2).1
    · intro hb
      have h := swap374_bad_ge_topW hlo hhi hb
      have hinv : swap374 topW (swap374 topW w.val) = w.val := swap374_involutive hlo hhi w.val
      dsimp only [swap374W] at h; rwa [hinv] at h

theorem validSwapRelayWM_id {topW : ℕ} (h275 : 275 ≤ topW) (h437 : topW ≤ 437) :
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

theorem false_of_antitone_bad {b₁ b₂ : Wire 437 → Bool} (h : ∀ w, b₁ w = true → b₂ w = true)
    (q : Wire 437) (hq : b₂ q = false) : b₁ q = false := by
  cases hx : b₁ q
  · rfl
  · rw [h q hx] at hq; exact Bool.noConfusion hq

theorem cliffDisjointBad_antitone {b₁ b₂ : Wire 437 → Bool}
    (h : ∀ w, b₁ w = true → b₂ w = true) (c : CliffProg 437)
    (hc : cliffDisjointBad b₂ c = true) : cliffDisjointBad b₁ c = true := by
  induction c with
  | nil => rfl
  | x q =>
      simp only [cliffDisjointBad, Bool.not_eq_true'] at hc ⊢
      exact false_of_antitone_bad h q hc
  | cnot x y _ =>
      simp only [cliffDisjointBad, Bool.and_eq_true, Bool.not_eq_true'] at hc ⊢
      exact ⟨false_of_antitone_bad h x hc.1, false_of_antitone_bad h y hc.2⟩
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [cliffDisjointBad, Bool.and_eq_true] at hc ⊢
      exact ⟨ih₁ hc.1, ih₂ hc.2⟩

theorem progDisjointBad_antitone {b₁ b₂ : Wire 437 → Bool}
    (h : ∀ w, b₁ w = true → b₂ w = true) (p : TempPhaseProg 437)
    (hp : progDisjointBad b₂ p = true) : progDisjointBad b₁ p = true := by
  induction p with
  | nil => rfl
  | cliff c => exact cliffDisjointBad_antitone h c hp
  | z q =>
      simp only [progDisjointBad, Bool.not_eq_true'] at hp ⊢
      exact false_of_antitone_bad h q hp
  | tempAnd c1 c2 out _ _ _ body ih =>
      simp only [progDisjointBad, Bool.and_eq_true, Bool.not_eq_true'] at hp ⊢
      exact ⟨false_of_antitone_bad h c1 hp.1, false_of_antitone_bad h c2 hp.2.1,
        false_of_antitone_bad h out hp.2.2.1, ih hp.2.2.2⟩
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [progDisjointBad, Bool.and_eq_true] at hp ⊢
      exact ⟨ih₁ hp.1, ih₂ hp.2⟩

/-- `< 321`-wire static hole stage for `axCtx14_275 w` using clean wire `320` instead of `434`. -/
def axInner1At320 (w : Fin 3) : TempPhaseProg 437 :=
  .seq (.cliff (axMidCliff w))
    (apexMajAt 320 (by decide) ⟨319, by decide⟩ (p57ProjW w ⟨6, by decide⟩)
      (axBAddW ⟨6, by decide⟩) (pBufW w ⟨7, by decide⟩)
      (ax319_ne_pbuf7 w) (ax319_ne_proj6 w) ax319_ne_badd6 (axProj6_ne_badd6 w)
      (by decide) (by dsimp [p57ProjW]; omega) (by decide) (by dsimp [pBufW]; omega))

theorem axInner1At320_spec (w : Fin 3) : ValidCleanRem 437 (437 - 320) (axInner1At320 w) ∧
    (axInner1At320 w).countTempAnd = 1 ∧ (∀ δ : BitAssignment 437, cleanRem 437 (437 - 320) δ
    → (axInner1At320 w).evalSign δ = 0) ∧ (∀ δ : BitAssignment 437, cleanRem 437 (437 - 320) δ
    → (∀ u : Wire 437, ¬ mutAxis1 w u → (axInner1At320 w).evalBits δ u = δ u) ∧ (∀ b : Fin 8,
    (axInner1At320 w).evalBits δ (pBufW w b) = δ (pBufW w b) + axHoleTargetBit w δ b))
    := by
  obtain ⟨hv7, _, _, hs7, hb7⟩ := apexMajAt_spec 320 (by decide)
    ⟨319, by decide⟩ (p57ProjW w ⟨6, by decide⟩) (axBAddW ⟨6, by decide⟩) (pBufW w ⟨7, by decide⟩)
    (ax319_ne_pbuf7 w) (ax319_ne_proj6 w) ax319_ne_badd6 (axProj6_ne_badd6 w)
    (axProj6_ne_pbuf7 w) (axBAdd6_ne_pbuf7 w)
    (by decide) (by dsimp [p57ProjW]; omega) (by decide) (by dsimp [pBufW]; omega)
  have hSuppMid : (axMidCliff w).SupportsBelow 320 := by
    refine ⟨Prod57BoothHoist.cnotVec_supportsBelow 6 axSrc6 (axDst6 w) _
      (fun i ↦ by fin_cases i <;> decide) (fun i ↦ by dsimp [axDst6, pBufW]; omega), ?_⟩
    dsimp [cXor3, p57ProjW, axBAddW, pBufW, CliffProg.SupportsBelow]
    omega
  have hclMid : ∀ δ : BitAssignment 437, cleanRem 437 (437 - 320) δ →
      cleanRem 437 (437 - 320) ((axMidCliff w).eval δ) := fun δ hδ u hu ↦ by
    rw [(axMidCliff w).eval_outside hSuppMid δ u (by omega)]
    exact hδ u hu
  have hvAll : ValidCleanRem 437 (437 - 320) (axInner1At320 w) :=
    ⟨437 - 320, by decide, trivial, hv7, hclMid⟩
  refine ⟨hvAll, rfl, fun δ hδ ↦ ?_, fun δ hδ ↦ ?_⟩
  · dsimp only [axInner1At320, TempPhaseProg.evalSign, TempPhaseProg.evalBits]
    rw [hs7 _ (hclMid δ hδ), zero_add]
  · obtain ⟨hM_non, hM_7, hM_6, hM_lo⟩ := axMidCliff_eval w δ
    obtain ⟨_, heq7⟩ := hb7 ((axMidCliff w).eval δ) (hclMid δ hδ)
    have h319 : (axMidCliff w).eval δ ⟨319, by decide⟩ = δ ⟨319, by decide⟩ :=
      hM_non _ (fun ⟨b, hb⟩ ↦ by have hv := congrArg Fin.val hb; dsimp [pBufW] at hv; omega)
    have hp6 : (axMidCliff w).eval δ (p57ProjW w ⟨6, by decide⟩) = δ (p57ProjW w ⟨6, by decide⟩) :=
      hM_non _ (fun ⟨b, hb⟩ ↦ by
        have hv := congrArg Fin.val hb; dsimp [p57ProjW, pBufW] at hv; omega)
    have hb6 : (axMidCliff w).eval δ (axBAddW ⟨6, by decide⟩) = δ (axBAddW ⟨6, by decide⟩) :=
      hM_non _ (fun ⟨b, hb⟩ ↦ by
        have hv := congrArg Fin.val hb; dsimp [axBAddW, pBufW] at hv; omega)
    have h_ev : (axInner1At320 w).evalBits δ =
        Function.update ((axMidCliff w).eval δ) (pBufW w ⟨7, by decide⟩)
          (δ (pBufW w ⟨7, by decide⟩) + axHoleTargetBit w δ ⟨7, by decide⟩) := by
      dsimp only [axInner1At320, TempPhaseProg.evalBits]
      rw [heq7, hM_7, h319, hp6, hb6]
      congr 1
      dsimp only [axHoleTargetBit]
      simp only [show ¬((7 : ℕ) < 6) by decide, ↓reduceDIte, show (7 : ℕ) ≠ 6 by decide, ↓reduceIte,
        add_assoc]
    rw [h_ev]
    refine ⟨fun u hnu ↦ ?_, fun b ↦ ?_⟩
    · rw [Function.update_of_ne (fun h ↦ hnu ⟨⟨7, by decide⟩, h⟩)]
      exact hM_non u hnu
    · by_cases hb_lt6 : b.val < 6
      · rw [Function.update_of_ne
          (wire_ne_of_lt (by change 150 + 8 * w.val + b.val < 150 + 8 * w.val + 7; omega))]
        exact hM_lo ⟨b.val, hb_lt6⟩
      · by_cases hb_eq6 : b.val = 6
        · have hb_fin : b = ⟨6, by decide⟩ := Fin.ext hb_eq6
          subst hb_fin
          rw [Function.update_of_ne
            (wire_ne_of_lt (by change 150 + 8 * w.val + 6 < 150 + 8 * w.val + 7; omega))]
          exact hM_6
        · have hb_fin : b = ⟨7, by decide⟩ := Fin.ext (by have := b.isLt; change b.val = 7; omega)
          subst hb_fin
          exact Function.update_self _ _ _

/-- Single-axis `< 321`-wire stepped-projectile XOR (`15` `TempAnd`s, max wire `320`). -/
def axisStep1_fast321_275 (w : Fin 3) : TempPhaseProg 437 :=
  (axCtx14_275 w).plug (axInner1At320 w)

/-- 3-axis `< 321`-wire stepped-projectile XOR (`45` `TempAnd`s, `progSupportsBelowB 321 =
true`). -/
def axisStep3_fast321_275 : TempPhaseProg 437 := .seq (axisStep1_fast321_275 0)
    (.seq (axisStep1_fast321_275 1) (axisStep1_fast321_275 2))

open Classical in
theorem axisStep1_fast321_275_spec (w : Fin 3) : IsMutBlock 437 (437 - 275) (mutAxis1 w)
    (axisStep1_fast321_275 w) ∧ (axisStep1_fast321_275 w).countTempAnd = 15 ∧ (∀ β,
    cleanRem 437 (437 - 275) β → (axisStep1_fast321_275 w).evalBits β =
    (Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep1_fast_275 w).evalBits β)
    := by
  obtain ⟨hCntC, hDisjC, _, _, hEvalC⟩ := axCtx14_275_pkg w
  obtain ⟨hsP, _, _, _⟩ := axPrepCliff_props w
  obtain ⟨_, hsLt⟩ := StepBBlock0.ctxLtCompLoop_props (mutW := mutAxis1 w)
    8 299 (by decide) axAW axBW
    (fun b ↦ wire_ne_of_lt (by dsimp [axAW, axBW]; omega))
    (fun b ↦ by dsimp [axAW]; omega) (fun b ↦ by dsimp [axBW]; omega)
    (fun j ⟨b, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [axAW, pBufW] at hv; omega)
    (fun j ⟨b, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [axBW, pBufW] at hv; omega)
    (fun q hq ⟨b, h⟩ ↦ by subst h; dsimp [pBufW] at hq; omega)
  obtain ⟨_, hsAdd6⟩ := StepBBlock0.ctxRippleAddCarry_props (mutW := mutAxis1 w)
    6 308 (by decide)
    (fun b : Fin 6 ↦ p57ProjW w ⟨b.val, by omega⟩)
    (fun b : Fin 6 ↦ axBAddW ⟨b.val, by omega⟩) axLtW
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axLtW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [axBAddW, axLtW]; omega))
    (fun b ↦ by dsimp [p57ProjW]; omega)
    (fun b ↦ by dsimp [axBAddW]; omega)
    (by dsimp [axLtW]; omega)
    (fun j ⟨b, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [p57ProjW, pBufW] at hv; omega)
    (fun j ⟨b, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [axBAddW, pBufW] at hv; omega)
    (fun ⟨b, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [axLtW, pBufW] at hv; omega)
    (fun q hq ⟨b, h⟩ ↦ by subst h; dsimp [pBufW] at hq; omega)
  have hSupp320 : (axCtx14_275 w).SupportsBelowCtx 320 := TempCtx.supportsBelowCtx_append
      le_rfl (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide) (ctxCliffAlloc_supports
      hsP)) (TempCtx.supportsBelowCtx_append le_rfl (StepBBlock0.TempCtx.supportsBelowCtx_mono
      (by decide) hsLt) hsAdd6)
  have hLift320 : StepBBlock0.TempCtxLiftEx 275 320 (axCtx14_275 w) :=
    StepBBlock0.TempCtxLiftEx.append
      (StepBBlock0.TempCtxLiftEx.mono (cur₀ := 275) (next₁ := 299) (by decide) le_rfl (by decide)
        (StepBBlock0.TempCtxLiftEx.cliff (cur := 299) (by decide) (axPrepCliff w) hsP))
      (StepBBlock0.TempCtxLiftEx.append
        (StepBBlock0.TempCtxLiftEx.ltCompLoop 8 299 (by decide) axAW axBW _ _ _)
        (StepBBlock0.TempCtxLiftEx.rippleAddCarry 6 308 (by decide) _ _ axLtW _ _ _ _ _ _))
  have hcl320 : ∀ β, cleanRem 437 (437 - 275) β →
      cleanRem 437 (437 - 320) ((axCtx14_275 w).fwdBits β) := fun β hβ ↦ by
    dsimp only [axCtx14_275]
    rw [StepBBlock0.TempCtx.append_fwdBits, StepBBlock0.TempCtx.append_fwdBits]
    have hcl1 := cliff_cleanRem (by decide) hsP (cleanRem_anti (by decide) hβ)
    have hcl2 := ctx_fwdBits_clean (by decide) hsLt (cleanRem_anti (by decide) hcl1)
    exact ctx_fwdBits_clean (by decide) hsAdd6 (cleanRem_anti (by decide) hcl2)
  obtain ⟨hvIn, hcIn, hsIn, hbIn⟩ := axInner1At320_spec w
  obtain ⟨hv, hcnt, hsgn, hbits⟩ :=
    StepBBlock0.ScopedBlock.graft_mutating_clean (M := 437) (rem := 437 - 275) (curHole := 320)
      (mutAxis1 w) (axCtx14_275 w) hDisjC hSupp320 (by decide)
      (axCtx14_275 w).fwdBits (StepBBlock0.TempCtxLiftEx.probe hLift320) (axInner1At320 w) hvIn
      (fun δ hδ u hnu ↦ (hbIn δ hδ).1 u hnu)
  obtain ⟨hBFast, _, hEFast⟩ :=
    Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep1_fast_275_spec w
  have hnon : ∀ β, cleanRem 437 (437 - 275) β → ∀ q, ¬ mutAxis1 w q →
      (axisStep1_fast321_275 w).evalBits β q = β q := fun β hβ q hnq ↦ by
    dsimp only [axisStep1_fast321_275]; rw [hbits β hβ q]; simp [hnq]
  have hcl : ∀ β, cleanRem 437 (437 - 275) β →
      cleanRem 437 (437 - 275) ((axisStep1_fast321_275 w).evalBits β) :=
    fun β hβ u hu ↦ by
      rw [hnon β hβ u (fun ⟨b, hb⟩ ↦ by subst hb; dsimp [pBufW] at hu; omega)]
      exact hβ u hu
  refine ⟨⟨hv, fun β hβ ↦ ?_, hcl, hnon⟩,
    by dsimp [axisStep1_fast321_275]; rw [hcnt, hCntC, hcIn],
    fun β hβ ↦ ?_⟩
  · dsimp only [axisStep1_fast321_275]
    rw [hsgn β hβ, hsIn _ (hcl320 β hβ)]
  · funext q
    by_cases hq : mutAxis1 w q
    · obtain ⟨b, rfl⟩ := hq
      have hm : mutAxis1 w (pBufW w b) := ⟨b, rfl⟩
      dsimp only [axisStep1_fast321_275]
      rw [hbits β hβ (pBufW w b)]
      simp only [hm, ↓reduceIte]
      rw [(hbIn _ (hcl320 β hβ)).2 b, StepBBlock0.TempCtx.fwdBits_mut hDisjC β hm, (hEvalC β hβ).2
        b, (hEFast β hβ b).symm]
    · exact (hnon β hβ q hq).trans (hBFast.2.2.2 β hβ q hq).symm

theorem axisStep3_fast321_275_spec : IsMutBlock 437 (437 - 275)
    (fun q ↦ ∃ w b, q = pBufW w b) axisStep3_fast321_275 ∧
    axisStep3_fast321_275.countTempAnd = 45 ∧ (∀ β, cleanRem 437 (437 - 275) β →
    axisStep3_fast321_275.evalBits β =
    Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275.evalBits β) := by
  obtain ⟨hB0, hc0, hE0⟩ := axisStep1_fast321_275_spec 0
  obtain ⟨hB1, hc1, hE1⟩ := axisStep1_fast321_275_spec 1
  obtain ⟨hB2, hc2, hE2⟩ := axisStep1_fast321_275_spec 2
  let mutAll : Wire 437 → Prop := fun q ↦ ∃ w b, q = pBufW w b
  have liftMut : ∀ w : Fin 3, IsMutBlock 437 (437 - 275) (mutAxis1 w) (axisStep1_fast321_275 w) →
      IsMutBlock 437 (437 - 275) mutAll (axisStep1_fast321_275 w) :=
    fun w hB ↦ ⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦ hB.2.2.2 β hβ q (fun ⟨b, hb⟩ ↦ hq ⟨w, b,
      hb⟩)⟩
  refine ⟨IsMutBlock.seq (by decide) (liftMut 0 hB0)
      (IsMutBlock.seq (by decide) (liftMut 1 hB1) (liftMut 2 hB2)),
    by dsimp [axisStep3_fast321_275, TempPhaseProg.countTempAnd]; rw [hc0, hc1, hc2],
    fun β hβ ↦ ?_⟩
  have hcl0 := hB0.2.2.1 β hβ
  have hcl1 := hB1.2.2.1 ((axisStep1_fast321_275 0).evalBits β) hcl0
  rw [axisStep3_fast321_275, Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275]
  dsimp only [TempPhaseProg.evalBits]
  rw [hE2 _ hcl1, hE1 _ hcl0, hE0 β hβ]

theorem compose_permReg_id {n : ℕ} (r : QRegister 437 n) (h : ∀ w : Wire 437, id (id w) = w) :
    r.compose (permReg (permOfInvol id h)) = r := qreg_ext fun _ ↦ rfl

theorem putQZ_eq_of_lt251 {ξ : BitAssignment 437} {w : Wire 437} (hw : w.val < 251) :
    putQZ ξ w = ξ w := by
  dsimp only [putQZ]
  rw [putQ3_of_not_bad (by simp only [isBadQ3, decide_eq_false_iff_not]; omega),
    putZ3_of_not_bad (by simp only [isBadZ3, decide_eq_false_iff_not]; omega)]

/-- Bad-wire predicate for `clearPreMKCtrl` (`[177..198)` or `[251..254)`). -/
def isBadPreMKCtrl (w : Wire 437) : Bool :=
  decide ((177 ≤ w.val ∧ w.val < 198) ∨ (251 ≤ w.val ∧ w.val < 254))

/-- Bad-wire predicate for `clearPreMKCat` (`[177..184)` or `[251..254)`). -/
def isBadPreMKCat (w : Wire 437) : Bool :=
  decide ((177 ≤ w.val ∧ w.val < 184) ∨ (251 ≤ w.val ∧ w.val < 254))

/-- Width-indexed bad-wire predicate matching `clearPreMKOfTopW topW`. -/
abbrev isBadPreMKOfTopW (topW : ℕ) : Wire 437 → Bool :=
  if topW = 342 then isBadPreMKCat else isBadPreMKCtrl

theorem clearPreMKOfTopW_eq_ite (topW : ℕ) (ξ : BitAssignment 437) (w : Wire 437) :
    clearPreMKOfTopW topW ξ w = if isBadPreMKOfTopW topW w = true then 0 else ξ w := by
  by_cases h : topW = 342
  · simp [clearPreMKOfTopW, isBadPreMKOfTopW, h, clearPreMKCat, isBadPreMKCat]
  · simp [clearPreMKOfTopW, isBadPreMKOfTopW, h, clearPreMKCtrl, isBadPreMKCtrl]

theorem cleanRem_clearPreMKOfTopW (topW : ℕ) {ξ : BitAssignment 437}
    (hcl : cleanRem 437 (437 - 275) ξ) :
    cleanRem 437 (437 - 275) (clearPreMKOfTopW topW ξ) := fun w hw ↦ by
  rw [clearPreMKOfTopW_eq_ite]
  split_ifs
  · rfl
  · exact hcl w hw

theorem eval_clearPreMKOfTopW_of_disjoint (topW : ℕ) {p : TempPhaseProg 437}
    (hp : progDisjointBad isBadPreMKCtrl p = true) (ξ : BitAssignment 437) :
    p.evalSign (clearPreMKOfTopW topW ξ) = p.evalSign ξ ∧
      p.evalBits (clearPreMKOfTopW topW ξ) = clearPreMKOfTopW topW (p.evalBits ξ) := by
  have hpW : progDisjointBad (isBadPreMKOfTopW topW) p = true :=
    progDisjointBad_antitone
      (fun w hw ↦ by
        by_cases h : topW = 342
        · simp only [isBadPreMKOfTopW, ite_eq_left h, isBadPreMKCat, decide_eq_true_eq] at hw
          simp only [isBadPreMKCtrl, decide_eq_true_eq]; omega
        · simpa [isBadPreMKOfTopW, h] using hw)
      p hp
  obtain ⟨hs, hEq, hBad⟩ := progDisjointBad_eval (isBadPreMKOfTopW topW) p hpW
    (clearPreMKOfTopW topW ξ) ξ
    (fun w hw ↦ by rw [clearPreMKOfTopW_eq_ite, ite_eq_right (by rw [hw]; exact Bool.noConfusion)])
  refine ⟨hs, funext fun w ↦ ?_⟩
  rw [clearPreMKOfTopW_eq_ite]
  cases hb : isBadPreMKOfTopW topW w
  · rw [ite_eq_right Bool.noConfusion, hEq w hb]
  · rw [ite_eq_left rfl, hBad w hb, clearPreMKOfTopW_eq_ite, ite_eq_left hb]

theorem zretStepWitness {T : Type} (x : T) : ∃ y : T, y = x := ⟨x, rfl⟩

theorem tempPhaseProg437_seq_evalBits (p q : TempPhaseProg 437) (x : BitAssignment 437) :
    (TempPhaseProg.seq p q).evalBits x = q.evalBits (p.evalBits x) := rfl

theorem rejKick275_disjoint_checks :
    progDisjointBad isBadPreMKCtrl rejKick275 = true ∧
      progDisjointBad isBadQ3 rejKick275 = true ∧
      progDisjointBad isBadZ3 rejKick275 = true ∧
      progDisjointBad (isBadXM 328 (fun _ ↦ false)) rejKick275 = true := by decide

theorem n1s_st3_retainedInv (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) : N1sRetainedInv (n1sSt3 t cfg α) := by
  obtain ⟨hInv2, hAct2, _, _, _, hacc2_s3⟩ := n1s_st2_props t α
  obtain ⟨hmk_non, _⟩ := n1s_midKick36_cat42_eq t cfg α hInv2 hAct2 hacc2_s3
  have hnon3 : ∀ q : Wire 437, ¬(107 ≤ q.val ∧ q.val < 149) → n1sSt3 t cfg α q = n1sSt2 t α q :=
    fun q h107 ↦ by
      dsimp only [n1sSt3, n1sLiftEval411]
      by_cases h411 : q.val < 411
      · rw [dite_eq_left h411]; exact hmk_non ⟨q.val, h411⟩ h107
      · rw [dite_eq_right h411]; exact (hInv2.hcl q (by omega)).symm
  exact N1sRetainedInv.of_agree_core hInv2
    (fun w hw ↦ (hnon3 w (by omega)).trans (hInv2.hcl w hw))
    (fun w h1 h2 ↦ (hnon3 w (by omega)).trans (hInv2.hz233 w h1 h2))
    (fun q _ _ _ ↦ hnon3 q (by omega))

theorem pStep5ZRet30_disjoint_checks :
    progDisjointBad isBadPreMKCtrl pStep5ZRet30 = true ∧
      progDisjointBad isBadZ3 cSwap24_275 = true ∧
      progDisjointBad isBadZ3 s3Flip275 = true ∧
      progDisjointBad (isBadXM 328 (fun _ ↦ false)) pStep5ZRet30 = true := by decide

theorem stepBundleW_pStep5ZRet30 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (topW : ℕ) (hlo : 328 ≤ topW) (hhi : topW ≤ 437)
    (hpM : progSupportsBelowB topW pStep5ZRet30 = true := by decide)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCombBase : QRegister 437 n) :
    StepBundleW topW v rCombBase
      (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt3 t cfg)
      (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt4 t cfg)
      (fun _ ↦ 0)
      ((pStep5ZRet30.onRegister rCombBase).toDyn v) := by
  let hsr := validSwapRelayWM_id (topW := topW) (by omega) hhi
  let δ_in : BitAssignment 149 → BitAssignment 437 := clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt3 t cfg
  let δ_out : BitAssignment 149 → BitAssignment 437 := clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt4 t cfg
  have hcl_in : ∀ α, cleanRem 437 (437 - 275) (δ_in α) :=
    fun α ↦ cleanRem_clearPreMKOfTopW topW (cleanRem_putQZ (n1s_st3_retainedInv t cfg α).hcl)
  have hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α) :=
    fun α ↦ cleanRem_clearPreMKOfTopW topW (cleanRem_putQZ (n1s_st4_props t cfg α).1.hcl)
  have hpBad : progDisjointBad (isBadXM topW (fun _ ↦ false)) pStep5ZRet30 = true :=
    progDisjointBad_antitone
      (fun w hw ↦ by
        simp only [isBadXM, Bool.false_or, decide_eq_true_eq] at hw ⊢; omega)
      pStep5ZRet30 pStep5ZRet30_disjoint_checks.2.2.2
  have hOut_eq : ∀ α, δ_out α = pStep5ZRet30.evalBits (δ_in α) := fun α ↦ by
    have hInv3 := n1s_st3_retainedInv t cfg α
    dsimp only [δ_in, δ_out, Function.comp_apply, putQZ]
    rw [(eval_clearPreMKOfTopW_of_disjoint topW pStep5ZRet30_disjoint_checks.1 _).2,
      (eval_putQ3_of_disjoint pStepsQZRet30_disjoint.2.2.2.2.2.1 (putZ3 (n1sSt3 t cfg α))
      (pStep5ZRet30_pres_mu _ (cleanRem_putZ3 hInv3.hcl))).2]
    congr 2
    dsimp only [pStep5ZRet30, n1sSt4, TempPhaseProg.evalBits]
    rw [(eval_putZ3_of_disjoint pStep5ZRet30_disjoint_checks.2.1 (n1sSt3 t cfg α)
      (fun i ↦ (cSwap24_275_spec.2.2.2.2 (n1sSt3 t cfg α) hInv3.hcl).2.2 (u22WAux i)
        (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega))).2]
    let γ₃ := cSwap24_275.evalBits (n1sSt3 t cfg α)
    have hcl₃ : cleanRem 437 (437 - 275) γ₃ :=
      cSwap24_275_spec.2.2.2.1 (n1sSt3 t cfg α) hInv3.hcl
    have hm₃ : ∀ w : Fin 3, bitsVal (fun b ↦ γ₃ (p57MW w b)) = shellMagCoord3 (getU22 γ₃) w :=
      fun w ↦ by
        have hm_fn : (fun b ↦ γ₃ (p57MW w b)) = fun b ↦ n1sSt3 t cfg α (p57MW w b) :=
          funext fun b ↦ (cSwap24_275_spec.2.2.2.2 (n1sSt3 t cfg α) hInv3.hcl).2.2 (p57MW w b)
            (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega)
        have hu_eq : getU22 γ₃ = getU22 (n1sSt3 t cfg α) :=
          getU22_congr fun i ↦
            (cSwap24_275_spec.2.2.2.2 (n1sSt3 t cfg α) hInv3.hcl).2.2 (u22WAux i)
              (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega)
        rw [hm_fn, hu_eq]
        exact hInv3.m_val w
    rw [s3FlipFromZ3_275_eq_orig (putZ3 γ₃) (cleanRem_putZ3 hcl₃) (invZMag3_putZ3 hm₃),
      (eval_putZ3_of_disjoint pStep5ZRet30_disjoint_checks.2.2.1 γ₃
        (fun i ↦ s3Flip275_spec.1.2.2.2 γ₃ hcl₃ (u22WAux i)
          (fun ⟨w, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [u22WAux, p57S3W] at hv; omega))).2]
  have hB := stepBundleW_of_relayWM_static v rCombBase hsr δ_in δ_out (fun _ ↦ 0) pStep5ZRet30
      hpM hpBad pStep5ZRet30_clean_spec.1 (fun α ↦ ⟨hcl_in α, fun _ h ↦ Bool.noConfusion h⟩)
      hOut_eq (fun α ↦ pStep5ZRet30_clean_spec.2.1 (δ_in α) (hcl_in α))
      (fun α ↦ ⟨hcl_out α, fun _ h ↦ Bool.noConfusion h⟩)
  dsimp only at hB
  rwa [compose_permReg_id rCombBase hsr.invol] at hB

theorem sTrueRawValPBuf_congr_lt201 {γ₁ γ₂ : BitAssignment 437}
    (hag : ∀ w : Wire 437, w.val < 201 → γ₁ w = γ₂ w) :
    sTrueRawValPBuf γ₁ = sTrueRawValPBuf γ₂ := by
  unfold sTrueRawValPBuf
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hmw : (fun b : Fin 7 ↦ γ₁ (p57MW w b)) = fun b ↦ γ₂ (p57MW w b) :=
    funext fun b ↦ hag _ (by dsimp [p57MW]; omega)
  rw [hag (p57ProjW w ⟨7, by decide⟩) (by dsimp [p57ProjW]; omega),
    hag (p57PBufW w ⟨7, by decide⟩) (by dsimp [p57PBufW]; omega),
    hag (p57S3W w) (by dsimp [p57S3W]; omega), hmw]

def revTailZQuadRet216_338 : TempPhaseProg 437 := .seq axisStep3_fast321_275 (.seq
    validStaticFromZ28_275 (.seq zMag3Ret18_275 (.seq magUnpack63_275 (.seq muQuad3Ret3_275
    coinMuXor275))))

set_option maxRecDepth 32768 in
theorem revTailZQuadRet216_338_checks :
    progSupportsBelowB 374 revTailZQuadRet216_338 = true ∧
      progDisjointBad (isBadXM 374 (isBad374W 324)) revTailZQuadRet216_338 = true ∧
      progDisjointBad isBadZ3 Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275 =
        true ∧
      progDisjointBad isBadZ3 validStatic216_275 = true ∧
      progDisjointBad isBadQ3 validStatic216_275 = true := by decide

theorem andUncompute_not_mem_support_of_lt {Var : Type} {M n : ℕ} (v : Var)
    (rComb : QRegister M n) (bound : ℕ) (c₁ c₂ anc : Wire M) (h₁₂ : rComb c₁ ≠ rComb c₂)
    (hv1 : c₁.val < bound) (hv2 : c₂.val < bound) (hva : anc.val < bound) (u : Wire M)
    (hu : bound ≤ u.val) : rComb u ∉ (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂)
    (rComb anc) h₁₂).support := by
  have hne1 : rComb u ≠ rComb c₁ := rComb.wires.injective.ne (fun h ↦ by
    have := congrArg Fin.val h; omega)
  have hne2 : rComb u ≠ rComb c₂ := rComb.wires.injective.ne (fun h ↦ by
    have := congrArg Fin.val h; omega)
  have hnea : rComb u ≠ rComb anc := rComb.wires.injective.ne (fun h ↦ by
    have := congrArg Fin.val h; omega)
  simp [DynamicCircuit.support_andUncompute, hne1, hne2, hnea]

theorem dCliffXorAndPairsUncomp_not_mem_support_of_lt {Var : Type} {M n : ℕ} (v : Var)
    (rComb : QRegister M n) (bound W : ℕ) (cPre : CliffProg M) (lhs rhs acc : Fin W → Wire M)
    (hlr : ∀ j, lhs j ≠ rhs j) (hc : cliffSupportsBelowB bound cPre = true)
    (hl : ∀ j, (lhs j).val < bound) (hr : ∀ j, (rhs j).val < bound)
    (ha : ∀ j, (acc j).val < bound) (u : Wire M) (hu : bound ≤ u.val) : rComb u ∉
    (dCliffXorAndPairsUncomp v rComb W cPre lhs rhs acc hlr).support := by
  simp only [dCliffXorAndPairsUncomp, DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
    Finset.mem_union, not_or]
  exact ⟨cliff_not_mem_support_of_lt rComb bound cPre hc u hu,
    dXorAndPairsUncomp_not_mem_support_of_lt v rComb bound W lhs rhs acc hlr hl hr ha u hu⟩

set_option maxRecDepth 32768 in
theorem validStaticFromZRev27Ctx_supports374 :
    ctxSupportsBelowB 374 validStaticFromZRev27Ctx = true := by decide

theorem dRevTailZQuadRet216_275_not_mem_support_ge374 {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) (u : Wire 437) (hu : 374 ≤ u.val) :
    rComb u ∉ (dRevTailZQuadRet216_275 v rComb).support := by
  have hAx1 : ∀ w : Fin 3, rComb u ∉ (dAxisStep1Rev_275 v rComb w).support := fun w ↦ by
    have hK : ctxSupportsBelowB 374 (axCtxRev7_275 w) = true := by fin_cases w <;> decide
    have hc7 : cliffSupportsBelowB 374 (cAxisRevPre7 w) = true := by fin_cases w <;> decide
    refine p57ToDynWith_not_mem_support_of_lt v rComb 374 (dInnerAxisRev v rComb w)
      (fun u' hu' ↦ ?_) (axCtxRev7_275 w) hK u hu
    simp only [dInnerAxisRev, DynamicCircuit.support_seq, Finset.mem_union, not_or]
    refine ⟨dCliffXorAndPairsUncomp_not_mem_support_of_lt v rComb 374 7 (cAxisRevPre7 w)
        axRevLhs7 (axRevRhs7 w) (axRevAcc7 w) (axRevLhs7_ne_rhs7 w) hc7
        (fun k ↦ by revert k; decide) (fun k ↦ by revert w k; decide)
        (fun k ↦ by revert w k; decide) u' hu',
      dCliffXorAndPairsUncomp_not_mem_support_of_lt v rComb 374 1 _ _ _ _ _
        ?_ ?_ ?_ ?_ u' hu'⟩
    · revert w; decide
    · intro _; decide
    · intro _; decide
    · intro _; revert w; decide
  have hVS : rComb u ∉ (dValidStaticFromZRev27_275 v rComb).support := by
    refine p57ToDynWith_not_mem_support_of_lt v rComb 374 _
      (fun u' hu' ↦ ?_) validStaticFromZRev27Ctx validStaticFromZRev27Ctx_supports374 u hu
    exact andUncompute_not_mem_support_of_lt v rComb 374 ⟨333, by decide⟩ (vsAnd5In216W 4)
      validStaticW _ (by decide) (by decide) (by decide) u' hu'
  have hZM1 : ∀ w : Fin 3, rComb u ∉ (dZMag1Rev5_275 v rComb w).support := fun w ↦ by
    have hK : ctxSupportsBelowB 374 (zMag1Rev5Ctx w) = true := by fin_cases w <;> decide
    refine p57ToDynWith_not_mem_support_of_lt v rComb 374 _
      (fun u' hu' ↦ ?_) (zMag1Rev5Ctx w) hK u hu
    exact andUncompute_not_mem_support_of_lt v rComb 374 ⟨279, by decide⟩ (p57MW w ⟨6, by decide⟩)
      (retZeroMW w) _ (by decide) (by dsimp [p57MW]; omega) (by dsimp [retZeroMW]; omega) u' hu'
  have hMag : rComb u ∉ (dMagUnpackFromRetQuad0_275 v rComb).support :=
      p57ToDynWith_not_mem_support_of_lt v rComb 374 _ (dMagInnerLoop_not_mem_support_of_lt v
      rComb 374 (by decide) 21 le_rfl) magUnpackFromRetQuadK1Ctx (by decide) u hu
  have hClrQ : rComb u ∉ (dClearRetMuQuad0_275 v rComb).support :=
    dXorAndPairsUncomp_not_mem_support_of_lt v rComb 374 3
      lhsQuad3 rhsQuad3 retMuQuadW lhsQuad3_ne_rhs
      (fun j ↦ by revert j; decide) (fun j ↦ by revert j; decide)
      (fun j ↦ by revert j; decide) u hu
  have hCoinOk : rComb u ∉ (dCoinOkRev275 v rComb).support := by
    refine p57ToDynWith_not_mem_support_of_lt v rComb 374 _
      (fun u' hu' ↦ ?_) coinOkRevCtx (by decide) u hu
    exact andUncompute_not_mem_support_of_lt v rComb 374 ⟨275, by decide⟩ (coinW 2)
      coinOkW _ (by decide) (by decide) (by decide) u' hu'
  have hMuRev : rComb u ∉ (dMuXorRev2_275 v rComb).support := by
    refine p57ToDynWith_not_mem_support_of_lt v rComb 374 (dMuInner2_0 v rComb)
      (fun u' hu' ↦ ?_) muXorPre2Ctx (by decide) u hu
    have hne_mu0 : rComb u' ≠ rComb (muW 0) := rComb.wires.injective.ne (fun h ↦ by
      have := congrArg Fin.val h; dsimp [muW] at this; omega)
    simp only [dMuInner2_0, dZeroTPairsUncomp, DynamicCircuit.support_seq,
      DynamicCircuit.support_circuit, Finset.mem_union, not_or]
    refine ⟨cliff_not_mem_support_of_lt rComb 374 muHole2Cliff (by decide) u' hu',
      dZeroTUncomp1_not_mem_support v (rComb (muW 0)) (rComb u') _ hne_mu0 ?_,
      dXorAndPairsUncomp_not_mem_support_of_lt v rComb 374 2
        mu12Lhs2 mu12Rhs2 mu12Acc2 mu12_hlr
        (fun j ↦ by revert j; decide) (fun j ↦ by revert j; decide)
        (fun j ↦ by revert j; decide) u' hu'⟩
    exact czVecCircuit_not_mem_support (rComb u') 2 _ _ _
      (fun k ↦ rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h
        have hk : (mu0Lhs2 k).val < 374 := by fin_cases k <;> decide
        omega))
      (fun k ↦ rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h
        have hk : (mu0Rhs2 k).val < 374 := by fin_cases k <;> decide
        omega))
  simp only [dRevTailZQuadRet216_275, dAxisStep3Rev_275, dZMag3Rev15_275, dCoinMuRev3_275,
    DynamicCircuit.support_seq, Finset.mem_union, not_or]
  exact ⟨⟨hAx1 0, hAx1 1, hAx1 2⟩, hVS, ⟨hZM1 0, hZM1 1, hZM1 2⟩, hMag, hClrQ, hCoinOk, hMuRev⟩

theorem invRevTailZQuadRet216_congr_good {γ₁ γ₂ : BitAssignment 437}
    (hag : ∀ w : Wire 437, w.val < 275 → ¬(201 ≤ w.val ∧ w.val < 251) → γ₁ w = γ₂ w) :
    InvRevTailZQuadRet216 γ₁ ↔ InvRevTailZQuadRet216 γ₂ := by
  refine and_congr
    (InvRevTailPruned216_congr
      (fun w b ↦ hag _ (by dsimp [p57ProjW]; omega) (by dsimp [p57ProjW]; omega))
      (fun w b ↦ hag _ (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega))
      (fun w ↦ hag _ (by dsimp [p57S3W]; omega) (by dsimp [p57S3W]; omega))
      (fun w b ↦ hag _ (by dsimp [pBufW]; omega) (by dsimp [pBufW]; omega))
      (fun j ↦ hag _ (by dsimp [muW]; omega) (by dsimp [muW]; omega))
      (fun i ↦ hag _ (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega))
      (fun b ↦ hag _ (by dsimp [coinW]; omega) (by dsimp [coinW]; omega))
      (fun i ↦ hag _ (by dsimp [top7W]; omega) (by dsimp [top7W]; omega))
      (hag _ (by decide) (by decide)) (hag _ (by decide) (by decide)))
    (and_congr
      (InvZMag3_congr
        (fun w ↦ hag _ (by dsimp [retZeroMW]; omega) (by dsimp [retZeroMW]; omega))
        (fun w b ↦ hag _ (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega)))
      (InvMuQuad3_congr
        (fun j ↦ hag _ (by dsimp [muW]; omega) (by dsimp [muW]; omega))
        (fun j ↦ hag _ (by have := retMuQuadW_lt275 j; omega)
          (by rw [retMuQuadW_val_eq]; omega))))

theorem revTailZQuadRet216_338_eval_eq (γ : BitAssignment 437)
    (hcl : cleanRem 437 (437 - 275) γ) : revTailZQuadRet216_338.evalSign γ = 0 ∧
    revTailZQuadRet216_275.evalSign γ = 0 ∧ revTailZQuadRet216_338.evalBits γ =
    revTailZQuadRet216_275.evalBits γ := by
  obtain ⟨hB6_321, _, hEq6⟩ := axisStep3_fast321_275_spec
  obtain ⟨hB6, _, _⟩ := Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275_spec
  obtain ⟨hB5, _, _⟩ := validStaticFromZ28_275_spec
  obtain ⟨hB4, _, _⟩ := zMag3Ret18_275_spec
  obtain ⟨hB3, _, _⟩ := magUnpack63_275_spec
  obtain ⟨_, hs2, hEv2⟩ := muQuad3Ret3_275_spec
  obtain ⟨hB1, _⟩ := coinMuXor275_spec
  obtain ⟨γ₁, hγ₁⟩ := zretStepWitness
    (Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275.evalBits γ)
  obtain ⟨γ₂, hγ₂⟩ := zretStepWitness (validStaticFromZ28_275.evalBits γ₁)
  obtain ⟨γ₃, hγ₃⟩ := zretStepWitness (zMag3Ret18_275.evalBits γ₂)
  obtain ⟨γ₄, hγ₄⟩ := zretStepWitness (magUnpack63_275.evalBits γ₃)
  obtain ⟨γ₅, hγ₅⟩ := zretStepWitness (muQuad3Ret3_275.evalBits γ₄)
  have hcl₁ : cleanRem 437 (437 - 275) γ₁ := by rw [hγ₁]; exact hB6.2.2.1 γ hcl
  have hcl₂ : cleanRem 437 (437 - 275) γ₂ := by rw [hγ₂]; exact hB5.2.2.1 γ₁ hcl₁
  have hcl₃ : cleanRem 437 (437 - 275) γ₃ := by rw [hγ₃]; exact hB4.2.2.1 γ₂ hcl₂
  have hcl₄ : cleanRem 437 (437 - 275) γ₄ := by rw [hγ₄]; exact hB3.2.2.1 γ₃ hcl₃
  have hcl₅ : cleanRem 437 (437 - 275) γ₅ := by rw [hγ₅]; exact (hEv2 γ₄ hcl₄).1
  have hBits : revTailZQuadRet216_338.evalBits γ = revTailZQuadRet216_275.evalBits γ := by
    rw [revTailZQuadRet216_338, revTailZQuadRet216_275]
    repeat rw [tempPhaseProg437_seq_evalBits]
    rw [hEq6 γ hcl]
  have hSgn275 : revTailZQuadRet216_275.evalSign γ = 0 := by
    rw [revTailZQuadRet216_275]
    dsimp only [TempPhaseProg.evalSign]
    rw [← hγ₁, ← hγ₂, ← hγ₃, ← hγ₄, ← hγ₅]
    rw [hB6.2.1 γ hcl, hB5.2.1 γ₁ hcl₁, hB4.2.1 γ₂ hcl₂, hB3.2.1 γ₃ hcl₃, hs2 γ₄ hcl₄,
      hB1.2.1 γ₅ hcl₅]
    decide
  have hSgn338 : revTailZQuadRet216_338.evalSign γ = 0 := by
    rw [revTailZQuadRet216_338]
    dsimp only [TempPhaseProg.evalSign]
    rw [hEq6 γ hcl, ← hγ₁, ← hγ₂, ← hγ₃, ← hγ₄, ← hγ₅]
    rw [hB6_321.2.1 γ hcl, hB5.2.1 γ₁ hcl₁, hB4.2.1 γ₂ hcl₂, hB3.2.1 γ₃ hcl₃, hs2 γ₄ hcl₄,
      hB1.2.1 γ₅ hcl₅]
    decide
  exact ⟨hSgn338, hSgn275, hBits⟩

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512

end ConfigLeaf3Slot3ZRetOuter

end Leaf3Slot3ZRetOuter

end
set_option exponentiation.threshold 256
end Leaf3Slot3ZRetOuter

section Leaf3Slot3ZRet193Sec4B
local instance (priority := 1000000) instNeZeroTwoPow_Leaf3Slot3ZRet193Sec4B (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Section 4B Compact `< 371` (`96w`) `Norm1s` `StepBundleW`s (`Leaf3Slot3ZRet193Sec4B`)

Provides `dN1sFwdW`, `dN1sRevW`, their `TOFF`/`T` counts and `StepBundleW` theorems across all
`t : Norm1sTier` and `topW ∈ {328, 339, 342}`, plus `zRetStage26Input`, `core149ZRetBundle`,
`slot3Cat190ZRet`, `slot3Cat193ZRet`, `leaf3ZRetPerHorizon190`, and `leaf3ZRetPerHorizon193`.
-/

public section

namespace Leaf3Slot3ZRet193

section ConfigLeaf3Slot3ZRet193Sec4B

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance (priority := 10) instLoc_Leaf3Slot3ZRet193Sec4B_1InstNeZeroTwoPowZRet (k : ℕ) :
  NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

/- ## Section 4B: Compact `< 371` (`96w`) `Norm1s` Forward & Reverse `StepBundleW`s -/

section Part4B_Norm1sCompact

open SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution (wire_ne_of_lt wire_ne_of_gt CliffProg
  CliffDisjoint TempPhaseProg cleanRem ValidCleanRem validCleanRem_mono ScopedBlock TempCtx
  ctxCliffAlloc ctxCliffAlloc_disjoint ctxCliffAlloc_supports)
open MeasureBranchHadamardSem (matrix_ext_ket RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open Prod57BoothHoist (bitsVal_injective sTrueRawVal ket_p57DiagProj p57CleanDiagProj ctxCleanMsbSub
  dCleanMsbSub p57ToDynWith p57ToDynWith_count_t p57ToDynWith_count_toff
  p57ToDynWith_preservesStore)
open MomSlots35Slot3ProjNuclear (shellMu3 shellMu3_lt_seven)
open StepBOuter (accWAux muW u22WAux getU22)
open Slot3Exact216Oracle80 (validStaticVal216)
open Slot3MicroEngineAux
  (MicroOp microValid microAllocs microAnds boolToZMod2 boolToZMod2_decide_eq_one
   getBoolAt setBoolAt length_setBoolAt getBoolAt_setBoolAt
   initBoolList length_mkBoolList getBoolAt_mkBoolList
   bitsVal_eq_of_testBit bitsVal_testBit_eq
   evalMicroList evalMicroListStrict evalMicroListStrict_eq
   allBelow allBelow_iff allBelowFrom allBelowFrom_add allBelowFrom_chunks4
   TempCtxLiftEx ctxMicro ctxMicro_scoped ctxCliffAlloc_fwdBits)
open Slot3Norm1s36_161w (Norm1sTier clz18Log2 clz18Log2_le_17 norm1sMant18 norm1sHwProd)
open Slot3Norm1s36CoreWideBooth
  (Aff18 eqAff getAffAt evalAff evalMicroAff evalMicroAffStrict evalMicroAffStrict_eq
   evalMicroAff_sound evalAff_of_eqAff getBoolAt_map_evalAff
   expectedInAff18 initAff18 expectedMantAff18 clz18Log2_testBit_top initAff18_map_eq
   evalMicroList_append evalMicroList_ext_below n1sNoMutBelow n1s_evalMicroList_pres_below
   n1s_allBelow_of_noMutBelow n1s_norm1sMant18_lt
   two_mul_mu_le_clz18Log2
   n1sSTrue18W411 n1s_sTrue18W411_inj n1s_sTrue18W411_lt_275 n1s_sTrue18W411_range
   n1sU38W411 n1s_u38W411_range n1sUKW411 n1s_uKW411_range n1s_uKW411_bitsVal
   n1sMuW411 n1sProjW411 n1sValidStaticW411 n1sAccFlagW411 n1sOut32W411 n1sMantW411
   n1sInvW411 n1sCinW411
   n1sFlipMantSlice n1sCRowSetup n1sCRow0Lt18 n1sCRow0Full n1sAccSlice n1sBLowR
   n1sDBaseRevD18 n1sDLowRowRev n1sDHighRowRev n1sDBoothPrefixRev n1s_tier_bounds
   n1sBoothDoneInv n1sBoothFwd411 n1sBoothRevStatic411
   n1sBoothFwdAnds n1s_boothFwd411_spec n1s_boothFwd411_countTempAnd
   n1s_toDynWith_realizes_supp)
open Slot3Norm1s36CoreWide (n1sLiftEval411 n1sSt1_411 n1sSt2 n1sSt4 n1sSt5 n1s_revStatic411_spec
  n1s_st1_props n1s_st2_props n1s_st4_props n1s_st5_props n1s_if_pos n1s_if_neg
  n1s_boothRevStatic411_spec n1sAccTarget411 n1sRevInv411)
open Leaf3Slot3Norm1sWidth204 (clz17Ops clz17Ops_meta)
open Slot3Outer2344AndRelayWide.PosPhase246
  (cliffSupportsBelowB ctxSupportsBelowB progSupportsBelowB)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide
  (cliffDisjointBad progDisjointBad permOfInvol permReg st1)
open Slot3ZRetCore
  (st1QZ putZ3 zMagBit_congr_u22 putQ3 quad3_congr_of_mu ctxDisjointBad progDisjointBad_plug)
open Leaf3Slot3ZRet193Guard
  (zrEW411 zrEW411_bounds zrClzE5Cliff zr_clzE5Cliff_supportsBelow
   zr_clzE5Cliff_eval_outside zr_clzE5Cliff_cleanRem
   zrCliffWithinB zrE5PredB zr_clzE5Cliff_withinB zr_cliff_eval_congr
   zrGuardBit zrPGuard411 zrDGuardFwd411 zrDGuardRev411
   zr_pGuard411_supportsBelowB zr_dGuardFwd411_not_mem_support zr_dGuardRev411_not_mem_support
   zr_pGuard411_spec zr_dGuardFwd411_props zr_dGuardRev411_props
   zr_guardBit_eq_target_of_clzE5)

/- ### Section 4B.1: `56`-Alloc (`55`-`TempAnd`) Barrel Micro-Program & `GF(2)` Atom Tracker -/

/-- `56`-alloc (`55` `.andAlloc` + `1` `.zeroAlloc`) left-normalizing barrel shifter on `35` inputs
(`s[0..17] ++ clz17[18..34]`), restoring all `35` inputs and placing `norm1sMant18 s` at `73..90`.
-/
def zrBarrel55Ops : List MicroOp := [ .cnotW 34 18, .andAlloc 18 0, .cnotW 34 18, .cnotW 33 27,
    .cnotW 32 27, .cnotW 31 27, .cnotW 30 27, .cnotW 29 27, .cnotW 28 27, .cnotW 26 27, .cnotW 35 0,
    .andAlloc 27 0, .cnotW 35 0, .cnotW 34 1, .andAlloc 27 1, .cnotW 34 1, .andAlloc 27 2,
    .andAlloc 27 3, .andAlloc 27 4, .andAlloc 27 5, .andAlloc 27 6, .andAlloc 27 7, .andAlloc 27 8,
    .cnotW 33 27, .cnotW 32 27, .cnotW 31 27, .cnotW 30 27, .cnotW 29 27, .cnotW 28 27,
    .cnotW 26 27, .cnotW 33 23, .cnotW 32 23, .cnotW 31 23, .cnotW 30 23, .cnotW 25 23,
    .cnotW 24 23, .cnotW 22 23, .cnotW 35 0, .cnotW 36 0, .andAlloc 23 0, .cnotW 35 0, .cnotW 36 0,
    .cnotW 34 1, .cnotW 37 1, .andAlloc 23 1, .cnotW 34 1, .cnotW 37 1, .cnotW 38 2, .andAlloc 23 2,
    .cnotW 38 2, .cnotW 39 3, .andAlloc 23 3, .cnotW 39 3, .cnotW 40 4, .andAlloc 23 4, .cnotW 40 4,
    .cnotW 41 5, .andAlloc 23 5, .cnotW 41 5, .cnotW 42 6, .andAlloc 23 6, .cnotW 42 6, .cnotW 43 7,
    .andAlloc 23 7, .cnotW 43 7, .cnotW 36 8, .cnotW 44 8, .andAlloc 23 8, .cnotW 36 8, .cnotW 44 8,
    .cnotW 26 9, .cnotW 37 9, .andAlloc 23 9, .cnotW 26 9, .cnotW 37 9, .cnotW 38 10, .andAlloc 23
    10, .cnotW 38 10, .cnotW 39 11, .andAlloc 23 11, .cnotW 39 11, .cnotW 40 12, .andAlloc 23 12,
    .cnotW 40 12, .cnotW 33 23, .cnotW 32 23, .cnotW 31 23, .cnotW 30 23, .cnotW 25 23,
    .cnotW 24 23, .cnotW 22 23, .cnotW 33 21, .cnotW 32 21, .cnotW 29 21, .cnotW 28 21,
    .cnotW 25 21, .cnotW 24 21, .cnotW 20 21, .cnotW 35 0, .cnotW 36 0, .cnotW 45 0, .andAlloc 21 0,
    .cnotW 35 0, .cnotW 36 0, .cnotW 45 0, .cnotW 34 1, .cnotW 37 1, .cnotW 46 1, .andAlloc 21 1,
    .cnotW 34 1, .cnotW 37 1, .cnotW 46 1, .cnotW 38 2, .cnotW 47 2, .andAlloc 21 2, .cnotW 38 2,
    .cnotW 47 2, .cnotW 39 3, .cnotW 48 3, .andAlloc 21 3, .cnotW 39 3, .cnotW 48 3, .cnotW 40 4,
    .cnotW 45 4, .cnotW 49 4, .andAlloc 21 4, .cnotW 40 4, .cnotW 45 4, .cnotW 49 4, .cnotW 41 5,
    .cnotW 46 5, .cnotW 50 5, .andAlloc 21 5, .cnotW 41 5, .cnotW 46 5, .cnotW 50 5, .cnotW 42 6,
    .cnotW 47 6, .cnotW 51 6, .andAlloc 21 6, .cnotW 42 6, .cnotW 47 6, .cnotW 51 6, .cnotW 43 7,
    .cnotW 48 7, .cnotW 52 7, .andAlloc 21 7, .cnotW 43 7, .cnotW 48 7, .cnotW 52 7, .cnotW 36 8,
    .cnotW 44 8, .cnotW 49 8, .cnotW 53 8, .andAlloc 21 8, .cnotW 36 8, .cnotW 44 8, .cnotW 49 8,
    .cnotW 53 8, .cnotW 26 9, .cnotW 37 9, .cnotW 50 9, .cnotW 54 9, .andAlloc 21 9, .cnotW 26 9,
    .cnotW 37 9, .cnotW 50 9, .cnotW 54 9, .cnotW 38 10, .cnotW 51 10, .cnotW 55 10, .andAlloc 21
    10, .cnotW 38 10, .cnotW 51 10, .cnotW 55 10, .cnotW 39 11, .cnotW 52 11, .cnotW 56 11,
    .andAlloc 21 11, .cnotW 39 11, .cnotW 52 11, .cnotW 56 11, .cnotW 40 12, .cnotW 53 12,
    .cnotW 57 12, .andAlloc 21 12, .cnotW 40 12, .cnotW 53 12, .cnotW 57 12, .cnotW 22 13,
    .cnotW 30 13, .cnotW 41 13, .cnotW 54 13, .andAlloc 21 13, .cnotW 22 13, .cnotW 30 13,
    .cnotW 41 13, .cnotW 54 13, .cnotW 42 14, .cnotW 55 14, .andAlloc 21 14, .cnotW 42 14,
    .cnotW 55 14, .cnotW 33 21, .cnotW 32 21, .cnotW 29 21, .cnotW 28 21, .cnotW 25 21,
    .cnotW 24 21, .cnotW 20 21, .cnotW 18 19, .cnotW 33 19, .cnotW 31 19, .cnotW 29 19,
    .cnotW 27 19, .cnotW 25 19, .cnotW 23 19, .cnotW 21 19, .cnotW 35 0, .cnotW 36 0, .cnotW 45 0,
    .cnotW 58 0, .andAlloc 19 0, .cnotW 35 0, .cnotW 36 0, .cnotW 45 0, .cnotW 58 0, .cnotW 34 1,
    .cnotW 37 1, .cnotW 46 1, .cnotW 59 1, .andAlloc 19 1, .cnotW 34 1, .cnotW 37 1, .cnotW 46 1,
    .cnotW 59 1, .cnotW 38 2, .cnotW 47 2, .cnotW 58 2, .cnotW 60 2, .andAlloc 19 2, .cnotW 38 2,
    .cnotW 47 2, .cnotW 58 2, .cnotW 60 2, .cnotW 39 3, .cnotW 48 3, .cnotW 59 3, .cnotW 61 3,
    .andAlloc 19 3, .cnotW 39 3, .cnotW 48 3, .cnotW 59 3, .cnotW 61 3, .cnotW 40 4, .cnotW 45 4,
    .cnotW 49 4, .cnotW 60 4, .cnotW 62 4, .andAlloc 19 4, .cnotW 40 4, .cnotW 45 4, .cnotW 49 4,
    .cnotW 60 4, .cnotW 62 4, .cnotW 41 5, .cnotW 46 5, .cnotW 50 5, .cnotW 61 5, .cnotW 63 5,
    .andAlloc 19 5, .cnotW 41 5, .cnotW 46 5, .cnotW 50 5, .cnotW 61 5, .cnotW 63 5, .cnotW 42 6,
    .cnotW 47 6, .cnotW 51 6, .cnotW 62 6, .cnotW 64 6, .andAlloc 19 6, .cnotW 42 6, .cnotW 47 6,
    .cnotW 51 6, .cnotW 62 6, .cnotW 64 6, .cnotW 43 7, .cnotW 48 7, .cnotW 52 7, .cnotW 63 7,
    .cnotW 65 7, .andAlloc 19 7, .cnotW 43 7, .cnotW 48 7, .cnotW 52 7, .cnotW 63 7, .cnotW 65 7,
    .cnotW 36 8, .cnotW 44 8, .cnotW 49 8, .cnotW 53 8, .cnotW 64 8, .cnotW 66 8, .andAlloc 19 8,
    .cnotW 36 8, .cnotW 44 8, .cnotW 49 8, .cnotW 53 8, .cnotW 64 8, .cnotW 66 8, .cnotW 26 9,
    .cnotW 37 9, .cnotW 50 9, .cnotW 54 9, .cnotW 65 9, .cnotW 67 9, .andAlloc 19 9, .cnotW 26 9,
    .cnotW 37 9, .cnotW 50 9, .cnotW 54 9, .cnotW 65 9, .cnotW 67 9, .cnotW 38 10, .cnotW 51 10,
    .cnotW 55 10, .cnotW 66 10, .cnotW 68 10, .andAlloc 19 10, .cnotW 38 10, .cnotW 51 10,
    .cnotW 55 10, .cnotW 66 10, .cnotW 68 10, .cnotW 39 11, .cnotW 52 11, .cnotW 56 11,
    .cnotW 67 11, .cnotW 69 11, .andAlloc 19 11, .cnotW 39 11, .cnotW 52 11, .cnotW 56 11,
    .cnotW 67 11, .cnotW 69 11, .cnotW 40 12, .cnotW 53 12, .cnotW 57 12, .cnotW 68 12,
    .cnotW 70 12, .andAlloc 19 12, .cnotW 40 12, .cnotW 53 12, .cnotW 57 12, .cnotW 68 12,
    .cnotW 70 12, .cnotW 22 13, .cnotW 30 13, .cnotW 41 13, .cnotW 54 13, .cnotW 69 13,
    .cnotW 71 13, .andAlloc 19 13, .cnotW 22 13, .cnotW 30 13, .cnotW 41 13, .cnotW 54 13,
    .cnotW 69 13, .cnotW 71 13, .cnotW 42 14, .cnotW 55 14, .cnotW 70 14, .cnotW 72 14, .andAlloc 19
    14, .cnotW 42 14, .cnotW 55 14, .cnotW 70 14, .cnotW 72 14, .cnotW 20 15, .cnotW 24 15,
    .cnotW 28 15, .cnotW 32 15, .cnotW 43 15, .cnotW 56 15, .cnotW 71 15, .andAlloc 19 15,
    .cnotW 20 15, .cnotW 24 15, .cnotW 28 15, .cnotW 32 15, .cnotW 43 15, .cnotW 56 15,
    .cnotW 71 15, .cnotW 35 16, .cnotW 44 16, .cnotW 57 16, .cnotW 72 16, .andAlloc 19 16,
    .cnotW 35 16, .cnotW 44 16, .cnotW 57 16, .cnotW 72 16, .cnotW 18 19, .cnotW 33 19,
    .cnotW 31 19, .cnotW 29 19, .cnotW 27 19, .cnotW 25 19, .cnotW 23 19, .cnotW 21 19, .zeroAlloc,
    .cnotW 17 90, .cnotW 20 90, .cnotW 22 90, .cnotW 24 90, .cnotW 26 90, .cnotW 28 90,
    .cnotW 30 90, .cnotW 32 90, .cnotW 34 90, .cnotW 89 90, .cnotW 16 89, .cnotW 35 89,
    .cnotW 44 89, .cnotW 57 89, .cnotW 72 89, .cnotW 88 89, .cnotW 15 88, .cnotW 20 88,
    .cnotW 24 88, .cnotW 28 88, .cnotW 32 88, .cnotW 43 88, .cnotW 56 88, .cnotW 71 88,
    .cnotW 87 88, .cnotW 14 87, .cnotW 42 87, .cnotW 55 87, .cnotW 70 87, .cnotW 72 87,
    .cnotW 86 87, .cnotW 13 86, .cnotW 22 86, .cnotW 30 86, .cnotW 41 86, .cnotW 54 86,
    .cnotW 69 86, .cnotW 71 86, .cnotW 85 86, .cnotW 12 85, .cnotW 40 85, .cnotW 53 85,
    .cnotW 57 85, .cnotW 68 85, .cnotW 70 85, .cnotW 84 85, .cnotW 11 84, .cnotW 39 84,
    .cnotW 52 84, .cnotW 56 84, .cnotW 67 84, .cnotW 69 84, .cnotW 83 84, .cnotW 10 83,
    .cnotW 38 83, .cnotW 51 83, .cnotW 55 83, .cnotW 66 83, .cnotW 68 83, .cnotW 82 83, .cnotW 9 82,
    .cnotW 26 82, .cnotW 37 82, .cnotW 50 82, .cnotW 54 82, .cnotW 65 82, .cnotW 67 82,
    .cnotW 81 82, .cnotW 8 81, .cnotW 36 81, .cnotW 44 81, .cnotW 49 81, .cnotW 53 81, .cnotW 64 81,
    .cnotW 66 81, .cnotW 80 81, .cnotW 7 80, .cnotW 43 80, .cnotW 48 80, .cnotW 52 80, .cnotW 63 80,
    .cnotW 65 80, .cnotW 79 80, .cnotW 6 79, .cnotW 42 79, .cnotW 47 79, .cnotW 51 79, .cnotW 62 79,
    .cnotW 64 79, .cnotW 78 79, .cnotW 5 78, .cnotW 41 78, .cnotW 46 78, .cnotW 50 78, .cnotW 61 78,
    .cnotW 63 78, .cnotW 77 78, .cnotW 4 77, .cnotW 40 77, .cnotW 45 77, .cnotW 49 77, .cnotW 60 77,
    .cnotW 62 77, .cnotW 76 77, .cnotW 3 76, .cnotW 39 76, .cnotW 48 76, .cnotW 59 76, .cnotW 61 76,
    .cnotW 75 76, .cnotW 2 75, .cnotW 38 75, .cnotW 47 75, .cnotW 58 75, .cnotW 60 75, .cnotW 74 75,
    .cnotW 1 74, .cnotW 34 74, .cnotW 37 74, .cnotW 46 74, .cnotW 59 74, .cnotW 73 74, .cnotW 0 73,
    .cnotW 35 73, .cnotW 36 73, .cnotW 45 73, .cnotW 58 73 ]

theorem zr_barrel55Ops_meta : microValid 35 zrBarrel55Ops = true ∧ microAllocs
    zrBarrel55Ops = 56 ∧ microAnds zrBarrel55Ops = 55 := by
  decide

/-- Concatenated `clz17Ops ++ zrBarrel55Ops` micro-program (`73` allocs, `71` `TempAnd`s). -/
def zrClz17Barrel55Ops : List MicroOp := clz17Ops ++ zrBarrel55Ops

theorem zr_clz17Barrel55Ops_meta : microValid 18 zrClz17Barrel55Ops = true ∧ microAllocs
    zrClz17Barrel55Ops = 73 ∧ microAnds zrClz17Barrel55Ops = 71 := by
  decide

theorem zr_clz17Ops_noMut : n1sNoMutBelow 18 clz17Ops = true := by decide

/-- Read an entry of a `Nat` bitmask list with `0` default. -/
def zrGetMask : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => zrGetMask xs i

/-- Update an entry of a `Nat` bitmask list in place. -/
def zrSetMask : List ℕ → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, i + 1, v => x :: zrSetMask xs i v

theorem zr_length_setMask (ms : List ℕ) (i v : ℕ) :
    (zrSetMask ms i v).length = ms.length := by
  induction ms generalizing i with
  | nil => rfl
  | cons _ rest ih => cases i <;> simp [zrSetMask, ih]

theorem zr_getMask_setMask (ms : List ℕ) (i j v : ℕ) (hi : i < ms.length) :
    zrGetMask (zrSetMask ms i v) j = if j = i then v else zrGetMask ms j := by
  induction ms generalizing i j with
  | nil => cases hi
  | cons x rest ih =>
      cases i with
      | zero =>
          cases j <;> simp [zrSetMask, zrGetMask]
      | succ i' =>
          cases j with
          | zero => simp [zrSetMask, zrGetMask]
          | succ j' =>
              simp only [zrSetMask, zrGetMask]
              rw [ih i' j' (Nat.lt_of_succ_lt_succ hi)]
              by_cases h : j' = i' <;> simp [h]

/-- Symbolic `GF(2)` atom-mask simulator for `MicroOp` lists without `.notW`. -/
def zrStepMasks (top : ℕ) : List MicroOp → List ℕ → Option (List ℕ)
  | [], ms => some ms
  | .notW _ :: _, _ => none
  | .cnotW a b :: rest, ms =>
      zrStepMasks top rest (zrSetMask ms b (zrGetMask ms b ^^^ zrGetMask ms a))
  | .andAlloc _ _ :: rest, ms =>
      zrStepMasks (top + 1) rest (zrSetMask ms top (2 ^ top))
  | .zeroAlloc :: rest, ms =>
      zrStepMasks (top + 1) rest (zrSetMask ms top 0)

/-- Initial atom-mask table of length `total` with `2 ^ i` on `[0 .. nIn)` and `0` above. -/
def zrInitMasksAux (nIn idx : ℕ) : ℕ → List ℕ
  | 0 => []
  | rem + 1 => (if idx < nIn then 2 ^ idx else 0) :: zrInitMasksAux nIn (idx + 1) rem

/-- Initial atom-mask table for `nIn` inputs inside `total` slots. -/
def zrInitMasks (nIn total : ℕ) : List ℕ := zrInitMasksAux nIn 0 total

theorem zr_length_initMasksAux (nIn idx rem : ℕ) :
    (zrInitMasksAux nIn idx rem).length = rem := by
  induction rem generalizing idx with
  | zero => rfl
  | succ r ih => simp [zrInitMasksAux, ih]

theorem zr_getMask_initMasksAux (nIn idx rem k : ℕ) (hk : k < rem) :
    zrGetMask (zrInitMasksAux nIn idx rem) k = if idx + k < nIn then 2 ^ (idx + k) else 0 := by
  induction rem generalizing idx k with
  | zero => omega
  | succ r ih =>
      cases k with
      | zero => simp [zrInitMasksAux, zrGetMask]
      | succ k' =>
          simp only [zrInitMasksAux, zrGetMask]
          rw [ih (idx + 1) k' (by omega)]
          have hadd : idx + 1 + k' = idx + (k' + 1) := by omega
          rw [hadd]

/-- Evaluate a `GF(2)` bitmask `mask < 2 ^ bound` against an atom list `atoms`. -/
def zrEvalMask (atoms : List Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, mask => xor (mask.testBit k && getBoolAt atoms k) (zrEvalMask atoms k mask)

theorem zr_evalMask_xor (atoms : List Bool) :
    ∀ (k m₁ m₂ : ℕ),
      zrEvalMask atoms k (m₁ ^^^ m₂) =
        xor (zrEvalMask atoms k m₁) (zrEvalMask atoms k m₂)
  | 0, _, _ => rfl
  | k + 1, m₁, m₂ => by
      simp only [zrEvalMask, Nat.testBit_xor]
      rw [zr_evalMask_xor atoms k m₁ m₂]
      generalize m₁.testBit k = a
      generalize m₂.testBit k = b
      generalize getBoolAt atoms k = c
      generalize zrEvalMask atoms k m₁ = x
      generalize zrEvalMask atoms k m₂ = y
      cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> rfl

theorem zr_evalMask_ext (atoms₁ atoms₂ : List Bool) :
    ∀ (k mask : ℕ), (∀ j, j < k → getBoolAt atoms₁ j = getBoolAt atoms₂ j) →
      zrEvalMask atoms₁ k mask = zrEvalMask atoms₂ k mask
  | 0, _, _ => rfl
  | k + 1, mask, hEq => by
      simp only [zrEvalMask]
      rw [hEq k (by omega), zr_evalMask_ext atoms₁ atoms₂ k mask (fun j hj ↦ hEq j (by omega))]

theorem zr_evalMask_zero (atoms : List Bool) : ∀ k : ℕ, zrEvalMask atoms k 0 = false
  | 0 => rfl
  | k + 1 => by simp [zrEvalMask, zr_evalMask_zero atoms k]

theorem zr_evalMask_two_pow (atoms : List Bool) :
    ∀ (k idx : ℕ), idx < k → zrEvalMask atoms k (2 ^ idx) = getBoolAt atoms idx
  | 0, _, h => by omega
  | k + 1, idx, h => by
      simp only [zrEvalMask]
      by_cases heq : idx = k
      · subst heq
        have hzero : ∀ j, j ≤ idx → zrEvalMask atoms j (2 ^ idx) = false := by
          intro j hj
          induction j with
          | zero => rfl
          | succ j' ih =>
              simp only [zrEvalMask, ih (by omega), Bool.xor_false]
              have hne : idx ≠ j' := by omega
              simp [hne]
        rw [hzero idx le_rfl]
        simp
      · have hlt : idx < k := by omega
        have hd : decide (idx = k) = false := decide_eq_false heq
        rw [zr_evalMask_two_pow atoms k idx hlt]
        simp [Nat.testBit_two_pow, hd]

theorem zr_getBoolAt_append_left :
    ∀ (xs ys : List Bool) (i : ℕ), i < xs.length → getBoolAt (xs ++ ys) i = getBoolAt xs i
  | [], _, _, h => by simp at h
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, h =>
      zr_getBoolAt_append_left xs ys i (Nat.lt_of_succ_lt_succ h)

theorem zr_getBoolAt_append_singleton :
    ∀ (xs : List Bool) (b : Bool), getBoolAt (xs ++ [b]) xs.length = b
  | [], _b => rfl
  | _ :: xs, b => zr_getBoolAt_append_singleton xs b

theorem zr_stepMasks_sound :
    ∀ (ops : List MicroOp) (top : ℕ) (st atoms : List Bool) (ms msOut : List ℕ),
      microValid top ops = true →
      top + microAllocs ops ≤ st.length →
      st.length = ms.length →
      atoms.length = top →
      (∀ j, j < top → zrGetMask ms j < 2 ^ top ∧
        getBoolAt st j = zrEvalMask atoms top (zrGetMask ms j)) →
      zrStepMasks top ops ms = some msOut →
      ∃ atomsOut : List Bool,
        (∀ i, i < top → getBoolAt atomsOut i = getBoolAt atoms i) ∧
        atomsOut.length = top + microAllocs ops ∧
        (∀ j, j < top + microAllocs ops →
          getBoolAt (evalMicroList top ops st) j =
            zrEvalMask atomsOut (top + microAllocs ops) (zrGetMask msOut j))
  | [], top, st, atoms, ms, msOut, _, _, _, _, hInv, hStep => by
      injection hStep with hEq; subst hEq
      exact ⟨atoms, fun _ _ ↦ rfl, by simp only [microAllocs, Nat.add_zero]; assumption,
        fun j hj ↦ (hInv j (by simpa [microAllocs] using hj)).2⟩
  | .notW _ :: _, _, _, _, _, _, _, _, _, _, _, hStep => by simp [zrStepMasks] at hStep
  | .cnotW a b :: rest, top, st, atoms, ms, msOut, hv, hlen, hms, hat, hInv, hStep => by
      dsimp [microValid] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨⟨ha, hb⟩, _⟩, hvRest⟩ := hv
      let st' := setBoolAt st b (xor (getBoolAt st b) (getBoolAt st a))
      let ms' := zrSetMask ms b (zrGetMask ms b ^^^ zrGetMask ms a)
      have hInv' : ∀ j, j < top → zrGetMask ms' j < 2 ^ top ∧
          getBoolAt st' j = zrEvalMask atoms top (zrGetMask ms' j) := by
        intro j hj
        by_cases hjb : j = b
        · subst hjb
          rw [getBoolAt_setBoolAt st j j (by omega), ite_eq_left rfl, zr_getMask_setMask ms j j _
            (by omega), ite_eq_left rfl]
          refine ⟨Nat.xor_lt_two_pow (hInv j hj).1 (hInv a ha).1, ?_⟩
          rw [(hInv j hj).2, (hInv a ha).2, zr_evalMask_xor]
        · rw [getBoolAt_setBoolAt st b j (by omega), ite_eq_right hjb,
            zr_getMask_setMask ms b j _ (by omega), ite_eq_right hjb]
          exact hInv j hj
      exact zr_stepMasks_sound rest top st' atoms ms' msOut hvRest
        (by dsimp [st']; rw [length_setBoolAt]; exact hlen)
        (by dsimp [st', ms']; rw [length_setBoolAt, zr_length_setMask]; exact hms)
        hat hInv' hStep
  | .andAlloc a b :: rest, top, st, atoms, ms, msOut, hv, hlen, hms, hat, hInv, hStep => by
      dsimp [microValid] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨ha, hb⟩, hvRest⟩ := hv
      let bit := getBoolAt st a && getBoolAt st b
      let st' := setBoolAt st top bit
      let atoms' := atoms ++ [bit]
      let ms' := zrSetMask ms top (2 ^ top)
      have hAllocs : top + 1 + microAllocs rest = top + microAllocs (.andAlloc a b :: rest) := by
        dsimp [microAllocs]; omega
      have hInv' : ∀ j, j < top + 1 → zrGetMask ms' j < 2 ^ (top + 1) ∧
          getBoolAt st' j = zrEvalMask atoms' (top + 1) (zrGetMask ms' j) := by
        intro j hj
        by_cases hjt : j = top
        · subst hjt
          rw [getBoolAt_setBoolAt st j j (by omega), ite_eq_left rfl, zr_getMask_setMask ms j j _
            (by omega), ite_eq_left rfl]
          refine ⟨Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega), ?_⟩
          rw [zr_evalMask_two_pow atoms' (j + 1) j (by omega)]
          dsimp [atoms']
          rw [← hat, zr_getBoolAt_append_singleton]
        · have hjlt : j < top := by omega
          rw [getBoolAt_setBoolAt st top j (by omega), ite_eq_right hjt, zr_getMask_setMask ms top j
            _ (by omega), ite_eq_right hjt]
          have hm_lt := (hInv j hjlt).1
          refine ⟨lt_trans hm_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)), ?_⟩
          dsimp [zrEvalMask]
          have htb : (zrGetMask ms j).testBit top = false := Nat.testBit_lt_two_pow hm_lt
          rw [htb, Bool.false_and, Bool.false_xor,
            zr_evalMask_ext atoms' atoms top _ (fun k hk ↦ by
              dsimp [atoms']; rw [zr_getBoolAt_append_left _ _ k (by omega)])]
          exact (hInv j hjlt).2
      obtain ⟨atomsOut, hpre, hlOut, hEvOut⟩ := zr_stepMasks_sound rest (top + 1) st' atoms'
        ms' msOut hvRest
        (by dsimp [st']; rw [length_setBoolAt]; omega)
        (by dsimp [st', ms']; rw [length_setBoolAt, zr_length_setMask]; exact hms)
        (by simp [atoms', hat]) hInv' hStep
      refine ⟨atomsOut, fun i hi ↦ (hpre i (by omega)).trans ?_, by rw [← hAllocs]; exact hlOut,
        fun j hj ↦ by rw [← hAllocs] at hj ⊢; exact hEvOut j hj⟩
      dsimp [atoms']
      exact zr_getBoolAt_append_left atoms [bit] i (by omega)
  | .zeroAlloc :: rest, top, st, atoms, ms, msOut, hv, hlen, hms, hat, hInv, hStep => by
      dsimp [microValid] at hv
      let st' := setBoolAt st top false
      let atoms' := atoms ++ [false]
      let ms' := zrSetMask ms top 0
      have hAllocs : top + 1 + microAllocs rest = top + microAllocs (.zeroAlloc :: rest) := by
        dsimp [microAllocs]; omega
      have hInv' : ∀ j, j < top + 1 → zrGetMask ms' j < 2 ^ (top + 1) ∧
          getBoolAt st' j = zrEvalMask atoms' (top + 1) (zrGetMask ms' j) := by
        intro j hj
        by_cases hjt : j = top
        · subst hjt
          rw [getBoolAt_setBoolAt st j j (by omega), ite_eq_left rfl, zr_getMask_setMask ms j j _
            (by omega), ite_eq_left rfl]
          exact ⟨Nat.two_pow_pos _, (zr_evalMask_zero atoms' (j + 1)).symm⟩
        · have hjlt : j < top := by omega
          rw [getBoolAt_setBoolAt st top j (by omega), ite_eq_right hjt, zr_getMask_setMask ms top j
            _ (by omega), ite_eq_right hjt]
          have hm_lt := (hInv j hjlt).1
          refine ⟨lt_trans hm_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)), ?_⟩
          dsimp [zrEvalMask]
          have htb : (zrGetMask ms j).testBit top = false := Nat.testBit_lt_two_pow hm_lt
          rw [htb, Bool.false_and, Bool.false_xor,
            zr_evalMask_ext atoms' atoms top _ (fun k hk ↦ by
              dsimp [atoms']; rw [zr_getBoolAt_append_left _ _ k (by omega)])]
          exact (hInv j hjlt).2
      obtain ⟨atomsOut, hpre, hlOut, hEvOut⟩ := zr_stepMasks_sound rest (top + 1) st' atoms'
        ms' msOut hv
        (by dsimp [st']; rw [length_setBoolAt]; omega)
        (by dsimp [st', ms']; rw [length_setBoolAt, zr_length_setMask]; exact hms)
        (by simp [atoms', hat]) hInv' hStep
      refine ⟨atomsOut, fun i hi ↦ (hpre i (by omega)).trans ?_, by rw [← hAllocs]; exact hlOut,
        fun j hj ↦ by rw [← hAllocs] at hj ⊢; exact hEvOut j hj⟩
      dsimp [atoms']
      exact zr_getBoolAt_append_left atoms [false] i (by omega)

/-- Decidable check that `zrBarrel55Ops` restores all `35` input atom masks `2 ^ i`. -/
def zrBarrel55MaskCheck : Bool :=
  match zrStepMasks 35 zrBarrel55Ops (zrInitMasks 35 91) with
  | none => false
  | some msOut => allBelow 35 (fun i ↦ decide (zrGetMask msOut i = 2 ^ i))

theorem zr_barrel55Mask_ok : zrBarrel55MaskCheck = true := by decide +kernel

theorem zr_barrel55Ops_allBelow35 (m : ℕ) :
    let stOut := evalMicroList 35 zrBarrel55Ops (initBoolList 35 (35 + 56) m)
    allBelow 35 (fun i ↦ getBoolAt stOut i == m.testBit i) = true := by
  have hchk := zr_barrel55Mask_ok
  dsimp only [zrBarrel55MaskCheck] at hchk
  cases hStep : zrStepMasks 35 zrBarrel55Ops (zrInitMasks 35 91) with
  | none => rw [hStep] at hchk; exact Bool.noConfusion hchk
  | some msOut =>
      rw [hStep] at hchk
      let st₀ := initBoolList 35 91 m
      let atoms₀ := initBoolList 35 35 m
      have hlen₀ : st₀.length = 91 := by
        dsimp [st₀, initBoolList]; exact length_mkBoolList 35 m 0 91
      have hms₀ : (zrInitMasks 35 91).length = 91 := zr_length_initMasksAux 35 0 91
      have hat₀ : atoms₀.length = 35 := by
        dsimp [atoms₀, initBoolList]; exact length_mkBoolList 35 m 0 35
      have hInv₀ : ∀ j, j < 35 → zrGetMask (zrInitMasks 35 91) j < 2 ^ 35 ∧
          getBoolAt st₀ j = zrEvalMask atoms₀ 35 (zrGetMask (zrInitMasks 35 91) j) := by
        intro j hj
        have hgm : zrGetMask (zrInitMasks 35 91) j = 2 ^ j := by
          dsimp [zrInitMasks]
          rw [zr_getMask_initMasksAux 35 0 91 j (by omega), Nat.zero_add, ite_eq_left hj]
        rw [hgm]
        refine ⟨Nat.pow_lt_pow_right (by decide : 1 < 2) hj, ?_⟩
        rw [zr_evalMask_two_pow atoms₀ 35 j hj]
        dsimp [st₀, atoms₀, initBoolList]
        rw [getBoolAt_mkBoolList 35 m 0 91 j (by omega), getBoolAt_mkBoolList 35 m 0 35 j (by
          omega)]
      obtain ⟨atomsOut, hpre, _, hEvOut⟩ := zr_stepMasks_sound zrBarrel55Ops 35 st₀ atoms₀
        (zrInitMasks 35 91) msOut zr_barrel55Ops_meta.1
        (by rw [hlen₀, zr_barrel55Ops_meta.2.1])
        (hlen₀.trans hms₀.symm) hat₀ hInv₀ hStep
      rw [allBelow_iff]
      intro i hi
      have hmi : zrGetMask msOut i = 2 ^ i :=
        of_decide_eq_true ((allBelow_iff 35 _).mp hchk i hi)
      have hbit := hEvOut i (by rw [zr_barrel55Ops_meta.2.1]; omega)
      rw [hmi, zr_evalMask_two_pow atomsOut (35 + microAllocs zrBarrel55Ops) i
        (by rw [zr_barrel55Ops_meta.2.1]; omega), hpre i hi] at hbit
      have hat_i : getBoolAt atoms₀ i = m.testBit i := by
        dsimp [atoms₀, initBoolList]
        rw [getBoolAt_mkBoolList 35 m 0 35 i (by omega)]
        simp [hi]
      rw [beq_iff_eq]
      exact hbit.trans hat_i

/-- Symbolic `Aff18` postcondition on `zrClz17Barrel55Ops` (`mant[0..17]` at slots `73..90`). -/
def zrClz17Barrel55AffPost (k : ℕ) (st : List Aff18) : Bool :=
  allBelow 18 (fun i ↦ eqAff (getAffAt st i) (expectedInAff18 k i)) &&
  allBelow 18 (fun j ↦ eqAff (getAffAt st (73 + j)) (expectedMantAff18 k j))

/-- Symbolic `Aff18` branch check (`0 <= k < 18`) for `zrClz17Barrel55Ops`. -/
def zrClz17Barrel55AffCheck (k : ℕ) : Bool :=
  match evalMicroAffStrict 18 zrClz17Barrel55Ops (initAff18 k) with
  | none => false
  | some st => zrClz17Barrel55AffPost k st

/-- Concrete `s = 0` check for `zrClz17Barrel55Ops`. -/
def zrClz17Barrel55ZeroCheck : Bool :=
  let st := evalMicroListStrict 18 zrClz17Barrel55Ops (initBoolList 18 91 0)
  allBelow 18 (fun i ↦ getBoolAt st i == false) &&
  allBelow 18 (fun j ↦ getBoolAt st (73 + j) == false)

theorem zr_clz17Barrel55Zero_ok : zrClz17Barrel55ZeroCheck = true := by decide

set_option maxHeartbeats 800000 in
-- Symbolic Aff18 18-branch chunk verification
theorem zr_clz17Barrel55Aff_ok : allBelow 18 zrClz17Barrel55AffCheck = true := by
  change allBelowFrom zrClz17Barrel55AffCheck 0 (16 + 2) = true
  rw [allBelowFrom_add]
  have h0 : allBelowFrom zrClz17Barrel55AffCheck 0 16 = true :=
    allBelowFrom_chunks4 0 4 zrClz17Barrel55AffCheck
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h1 : allBelowFrom zrClz17Barrel55AffCheck 16 2 = true := by decide +kernel
  rw [h0, h1]
  rfl

/-- Full `2 ^ 18`-input specification of `zrClz17Barrel55Ops` at slots `73..90`. -/
theorem zr_clz17Barrel55Ops_spec (s : ℕ) (hs : s < 2 ^ 18) :
    let st := evalMicroList 18 zrClz17Barrel55Ops (initBoolList 18 91 s)
    allBelow 18 (fun i ↦ getBoolAt st i == s.testBit i) = true ∧
    (∀ j : Fin 18, getBoolAt st (73 + j.val) = (norm1sMant18 s).testBit j.val) := by
  by_cases hs0 : s = 0
  · subst hs0
    have h := zr_clz17Barrel55Zero_ok
    dsimp only [zrClz17Barrel55ZeroCheck] at h
    rw [evalMicroListStrict_eq] at h
    simp only [Bool.and_eq_true] at h
    have hm0 : norm1sMant18 0 = 0 := by decide
    refine ⟨?_, fun j ↦ ?_⟩
    · rw [allBelow_iff]
      intro i hi
      simpa [Nat.zero_testBit] using (allBelow_iff 18 _).mp h.1 i hi
    · have hj0 := of_decide_eq_true ((allBelow_iff 18 _).mp h.2 j.val j.isLt)
      rw [hj0, hm0, Nat.zero_testBit]
  · have hs_pos : 0 < s := Nat.pos_of_ne_zero hs0
    obtain ⟨htop, hhi0⟩ := clz18Log2_testBit_top hs_pos hs
    set k := clz18Log2 s
    have hk18 : k < 18 := Nat.lt_succ_of_le (clz18Log2_le_17 s)
    have hchk := (allBelow_iff 18 zrClz17Barrel55AffCheck).mp zr_clz17Barrel55Aff_ok k hk18
    dsimp only [zrClz17Barrel55AffCheck] at hchk
    rw [evalMicroAffStrict_eq] at hchk
    cases hAff : evalMicroAff 18 zrClz17Barrel55Ops (initAff18 k) with
    | none => rw [hAff] at hchk; exact Bool.noConfusion hchk
    | some stA =>
        rw [hAff] at hchk
        dsimp only [zrClz17Barrel55AffPost] at hchk
        simp only [Bool.and_eq_true] at hchk
        have hMap : stA.map (evalAff s.testBit) =
            evalMicroList 18 zrClz17Barrel55Ops (initBoolList 18 122 s) := by
          rw [evalMicroAff_sound s.testBit zrClz17Barrel55Ops 18 (initAff18 k) stA hAff,
            initAff18_map_eq hs_pos hs]
        have hBit : ∀ idx : ℕ, idx < 91 →
            getBoolAt (evalMicroList 18 zrClz17Barrel55Ops (initBoolList 18 91 s)) idx =
              evalAff s.testBit (getAffAt stA idx) := by
          intro idx hidx
          have hExt := evalMicroList_ext_below zrClz17Barrel55Ops 18
            (initBoolList 18 91 s) (initBoolList 18 122 s) zr_clz17Barrel55Ops_meta.1
            (by dsimp [initBoolList]; rw [length_mkBoolList, zr_clz17Barrel55Ops_meta.2.1])
            (by dsimp [initBoolList]; rw [length_mkBoolList, zr_clz17Barrel55Ops_meta.2.1]; omega)
            (fun i hi ↦ by
              dsimp [initBoolList]
              rw [getBoolAt_mkBoolList 18 s 0 91 i (by omega),
                getBoolAt_mkBoolList 18 s 0 122 i (by omega)])
            idx (by rw [zr_clz17Barrel55Ops_meta.2.1]; exact hidx)
          rw [hExt, ← hMap, getBoolAt_map_evalAff]
        refine ⟨?_, fun j ↦ ?_⟩
        · rw [allBelow_iff]
          intro i hi18
          rw [beq_iff_eq, hBit i (by omega), evalAff_of_eqAff s.testBit ((allBelow_iff 18 _).mp
            hchk.1 i hi18)]
          dsimp only [expectedInAff18]
          by_cases hik : i < k
          · simp only [hik, ↓reduceIte, Slot3Norm1s36CoreWideBooth.evalAff_var]
          · by_cases heq : i = k
            · subst heq
              simp only [hik, ↓reduceIte, Slot3Norm1s36CoreWideBooth.evalAff_const, htop]
            · simp only [hik, heq, ↓reduceIte,
                Slot3Norm1s36CoreWideBooth.evalAff_zero,
                hhi0 i (by omega)]
        · rw [hBit (73 + j.val) (by have := j.isLt; omega),
            evalAff_of_eqAff s.testBit ((allBelow_iff 18 _).mp hchk.2 j.val j.isLt)]
          unfold norm1sMant18 expectedMantAff18
          change _ = (s * 2 ^ (17 - k)).testBit j.val
          set sh := 17 - k
          rw [Nat.testBit_mul_two_pow]
          by_cases hjsh : j.val < sh
          · have hnot : ¬(sh ≤ j.val) := by omega
            simp only [hjsh, ↓reduceIte, Slot3Norm1s36CoreWideBooth.evalAff_zero, hnot,
              decide_false, Bool.false_and]
          · have hle : sh ≤ j.val := by omega
            simp only [hjsh, ↓reduceIte, hle, decide_true, Bool.true_and]
            by_cases hjk : j.val - sh < k
            · simp only [hjk, ↓reduceIte,
                Slot3Norm1s36CoreWideBooth.evalAff_var]
            · have heq : j.val - sh = k := by have := j.isLt; omega
              rw [heq]
              simp only [Nat.lt_irrefl, ↓reduceIte, Slot3Norm1s36CoreWideBooth.evalAff_const, htop]

/- ### Section 4B.2: Outer `clz17` (`[275..292)`), Compact Barrel (`[292..348)`) & Permuted Booth -/

/-- `17`-wire outer `clz17Ops` context on `[275..292)` (`16` `TempAnd`s). -/
def zrCtxClz411 : TempCtx 411 := ctxMicro n1sSTrue18W411 n1s_sTrue18W411_inj 275 17 16
    n1s_sTrue18W411_lt_275 clz17Ops clz17Ops_meta (by decide)

theorem zr_ctxClz411_scoped :
    zrCtxClz411.countTempAnd = 16 ∧
    (∀ {mutW : Wire 411 → Prop},
      (∀ i, ¬ mutW (n1sSTrue18W411 i)) → (∀ w : Wire 411, 275 ≤ w.val → ¬ mutW w) →
      zrCtxClz411.DisjointFrom mutW ∧ zrCtxClz411.SupportsBelowCtx (275 + 17)) ∧
    TempCtxLiftEx 275 (275 + 17) zrCtxClz411 ∧
    (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β →
      let m := bitsVal (fun i ↦ β (n1sSTrue18W411 i))
      let stOut := evalMicroList 18 clz17Ops (initBoolList 18 (18 + 17) m)
      cleanRem 411 (411 - (275 + 17)) (zrCtxClz411.fwdBits β) ∧
      (allBelow 18 (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire 411, w.val < 275 → zrCtxClz411.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : 18 ≤ s) (hhi : s < 18 + 17),
        zrCtxClz411.fwdBits β ⟨275 + (s - 18), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) :=
  ctxMicro_scoped n1sSTrue18W411 n1s_sTrue18W411_inj 275 17 16
    n1s_sTrue18W411_lt_275 clz17Ops clz17Ops_meta (by decide)

theorem zr_ctxClz411_pkg :
    let mut32Acc : Wire 411 → Prop := fun q ↦ q = n1sAccFlagW411 ∨ ∃ k : Fin 32, q = n1sOut32W411 k
    zrCtxClz411.countTempAnd = 16 ∧
    zrCtxClz411.DisjointFrom mut32Acc ∧
    zrCtxClz411.SupportsBelowCtx 292 ∧
    TempCtxLiftEx 275 292 zrCtxClz411 := by
  intro mut32Acc
  obtain ⟨hc, hp, hl, _⟩ := zr_ctxClz411_scoped
  obtain ⟨hd, hs⟩ := hp
    (fun i (h : mut32Acc (n1sSTrue18W411 i)) ↦ by
      have hr := n1s_sTrue18W411_range i
      rcases h with h1 | ⟨k, hk⟩
      · have hv := congrArg Fin.val h1; dsimp [n1sAccFlagW411] at hv
        rcases hr with r | r | r <;> omega
      · have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv
        rcases hr with r | r | r <;> omega)
    (fun w hw (h : mut32Acc w) ↦ by
      rcases h with h1 | ⟨k, hk⟩
      · subst h1; dsimp [n1sAccFlagW411] at hw; omega
      · subst hk; dsimp [n1sOut32W411] at hw; omega)
  exact ⟨hc, hd, hs, hl⟩

/-- `35`-wire barrel input map (`sTrue18` on `0..17`, `clz17` cascade `[275..292)` on `18..34`). -/
def zrInBarrel35W411 (i : Fin 35) : Wire 411 :=
  if h : i.val < 18 then n1sSTrue18W411 ⟨i.val, h⟩ else ⟨275 + (i.val - 18), by omega⟩

theorem zr_inBarrel35W411_lt_292 (i : Fin 35) : (zrInBarrel35W411 i).val < 292 := by
  dsimp [zrInBarrel35W411]
  by_cases h : i.val < 18
  · rw [dite_eq_left h]; exact lt_trans (n1s_sTrue18W411_lt_275 ⟨i.val, h⟩) (by decide)
  · rw [dite_eq_right h]; dsimp; omega

theorem zr_inBarrel35W411_inj : Function.Injective zrInBarrel35W411 := by
  intro a b hab
  dsimp [zrInBarrel35W411] at hab
  by_cases ha : a.val < 18 <;> by_cases hb : b.val < 18
  · rw [dite_eq_left ha, dite_eq_left hb] at hab
    exact Fin.ext (congrArg (Fin.val (n := 18)) (n1s_sTrue18W411_inj hab))
  · rw [dite_eq_left ha, dite_eq_right hb] at hab
    have := n1s_sTrue18W411_lt_275 ⟨a.val, ha⟩
    have hv := congrArg Fin.val hab; dsimp at hv; omega
  · rw [dite_eq_right ha, dite_eq_left hb] at hab
    have := n1s_sTrue18W411_lt_275 ⟨b.val, hb⟩
    have hv := congrArg Fin.val hab; dsimp at hv; omega
  · rw [dite_eq_right ha, dite_eq_right hb] at hab
    have hv := congrArg Fin.val hab; dsimp at hv; exact Fin.ext (by omega)

/-- `56`-wire compact barrel context on `[292..348)` (`55` `TempAnd`s; `mant` on `[330..348)`). -/
def zrCtxBarrel411 : TempCtx 411 := ctxMicro zrInBarrel35W411 zr_inBarrel35W411_inj 292
    56 55 zr_inBarrel35W411_lt_292 zrBarrel55Ops zr_barrel55Ops_meta (by decide)

theorem zr_ctxBarrel411_scoped :
    zrCtxBarrel411.countTempAnd = 55 ∧
    (∀ {mutW : Wire 411 → Prop},
      (∀ i, ¬ mutW (zrInBarrel35W411 i)) → (∀ w : Wire 411, 292 ≤ w.val → ¬ mutW w) →
      zrCtxBarrel411.DisjointFrom mutW ∧ zrCtxBarrel411.SupportsBelowCtx (292 + 56)) ∧
    TempCtxLiftEx 292 (292 + 56) zrCtxBarrel411 ∧
    (∀ β : BitAssignment 411, cleanRem 411 (411 - 292) β →
      let m := bitsVal (fun i ↦ β (zrInBarrel35W411 i))
      let stOut := evalMicroList 35 zrBarrel55Ops (initBoolList 35 (35 + 56) m)
      cleanRem 411 (411 - (292 + 56)) (zrCtxBarrel411.fwdBits β) ∧
      (allBelow 35 (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire 411, w.val < 292 → zrCtxBarrel411.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : 35 ≤ s) (hhi : s < 35 + 56),
        zrCtxBarrel411.fwdBits β ⟨292 + (s - 35), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) :=
  ctxMicro_scoped zrInBarrel35W411 zr_inBarrel35W411_inj 292 56 55
    zr_inBarrel35W411_lt_292 zrBarrel55Ops zr_barrel55Ops_meta (by decide)

theorem zr_ctxBarrel411_pkg :
    let mutOut : Wire 411 → Prop := fun q ↦ ∃ k : Fin 32, q = n1sOut32W411 k
    zrCtxBarrel411.countTempAnd = 55 ∧
    zrCtxBarrel411.DisjointFrom mutOut ∧
    zrCtxBarrel411.SupportsBelowCtx 348 ∧
    TempCtxLiftEx 292 348 zrCtxBarrel411 := by
  intro mutOut
  obtain ⟨hc, hp, hl, _⟩ := zr_ctxBarrel411_scoped
  obtain ⟨hd, hs⟩ := hp
    (fun i (h : mutOut (zrInBarrel35W411 i)) ↦ by
      rcases h with ⟨k, hk⟩
      dsimp [zrInBarrel35W411] at hk
      by_cases hi : i.val < 18
      · rw [dite_eq_left hi] at hk
        have hr := n1s_sTrue18W411_range ⟨i.val, hi⟩
        have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv
        rcases hr with h | h | h <;> omega
      · rw [dite_eq_right hi] at hk
        have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv; omega)
    (fun w hw (h : mutOut w) ↦ by
      rcases h with ⟨k, hk⟩; subst hk; dsimp [n1sOut32W411] at hw; omega)
  exact ⟨hc, hd, hs, hl⟩

/-- Mantissa output wire `330 + j` (`j : Fin 18`) of `zrCtxBarrel411`. -/
def zrMantW411 (j : Fin 18) : Wire 411 := ⟨330 + j.val, by omega⟩

theorem zr_ctxClz_and_barrel_fwd (β : BitAssignment 411) (hβ : cleanRem 411 (411 - 275) β) :
    let s := bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))
    let β₁ := zrCtxClz411.fwdBits β
    let β₂ := zrCtxBarrel411.fwdBits β₁
    cleanRem 411 (411 - 292) β₁ ∧
    (∀ w : Wire 411, w.val < 275 → β₁ w = β w) ∧
    cleanRem 411 (411 - 348) β₂ ∧
    (∀ w : Wire 411, w.val < 292 → β₂ w = β₁ w) ∧
    bitsVal (fun j : Fin 18 ↦ β₂ (zrMantW411 j)) = norm1sMant18 s := by
  intro s β₁ β₂
  have hs : s < 2 ^ 18 := bitsVal_lt_two_pow _
  obtain ⟨_, _, _, hClzEv⟩ := zr_ctxClz411_scoped
  obtain ⟨hcl₁, hpres₁_raw, hout₁⟩ := hClzEv β hβ
  have hpres₁ : ∀ w : Wire 411, w.val < 275 → β₁ w = β w :=
    hpres₁_raw (n1s_allBelow_of_noMutBelow 18 17 s clz17Ops clz17Ops_meta.2.1 zr_clz17Ops_noMut)
  obtain ⟨_, _, _, hBarEv⟩ := zr_ctxBarrel411_scoped
  obtain ⟨hcl₂, hpres₂_raw, hout₂⟩ := hBarEv β₁ hcl₁
  let m35 := bitsVal (fun i ↦ β₁ (zrInBarrel35W411 i))
  have hpres₂ : ∀ w : Wire 411, w.val < 292 → β₂ w = β₁ w :=
    hpres₂_raw (zr_barrel55Ops_allBelow35 m35)
  let stClz35 := evalMicroList 18 clz17Ops (initBoolList 18 35 s)
  let stClz91 := evalMicroList 18 clz17Ops (initBoolList 18 91 s)
  let stFull := evalMicroList 18 zrClz17Barrel55Ops (initBoolList 18 91 s)
  have hClz35_eq_91 : ∀ i, i < 35 → getBoolAt stClz35 i = getBoolAt stClz91 i := by
    apply evalMicroList_ext_below clz17Ops 18 (initBoolList 18 35 s) (initBoolList 18 91 s)
      clz17Ops_meta.1
    · dsimp [initBoolList]; rw [length_mkBoolList, clz17Ops_meta.2.1]
    · dsimp [initBoolList]; rw [length_mkBoolList, clz17Ops_meta.2.1]; omega
    · intro k hk
      dsimp [initBoolList]
      rw [getBoolAt_mkBoolList 18 s 0 35 k (by omega), getBoolAt_mkBoolList 18 s 0 91 k (by omega)]
  have hInit35_eq : ∀ i, i < 35 → getBoolAt (initBoolList 35 91 m35) i = getBoolAt stClz91 i := by
    intro i hi
    dsimp [initBoolList]
    rw [getBoolAt_mkBoolList 35 m35 0 91 i (by omega)]
    simp only [Nat.zero_add, hi, decide_true, Bool.true_and]
    rw [show m35.testBit i = decide (β₁ (zrInBarrel35W411 ⟨i, hi⟩) = 1) from
      bitsVal_testBit_eq (fun k ↦ β₁ (zrInBarrel35W411 k)) ⟨i, hi⟩,
      ← hClz35_eq_91 i hi]
    by_cases hi18 : i < 18
    · have hw_eq : zrInBarrel35W411 ⟨i, hi⟩ = n1sSTrue18W411 ⟨i, hi18⟩ := dite_eq_left hi18
      rw [hw_eq, hpres₁ _ (n1s_sTrue18W411_lt_275 _),
        ← bitsVal_testBit_eq (fun k ↦ β (n1sSTrue18W411 k)) ⟨i, hi18⟩,
        n1s_evalMicroList_pres_below clz17Ops 18 18 _ le_rfl zr_clz17Ops_noMut i hi18]
      dsimp only [initBoolList]
      rw [getBoolAt_mkBoolList 18 s 0 35 i (by omega)]
      simp only [Nat.zero_add, hi18, decide_true, Bool.true_and]
      rfl
    · have hw_eq : zrInBarrel35W411 ⟨i, hi⟩ = ⟨275 + (i - 18), by omega⟩ := dite_eq_right hi18
      rw [hw_eq]
      dsimp only [β₁]
      simp only [hout₁ i (by omega) hi, boolToZMod2_decide_eq_one]
      rfl
  have hBar_eq_Full : ∀ idx, idx < 91 →
      getBoolAt (evalMicroList 35 zrBarrel55Ops (initBoolList 35 91 m35)) idx =
        getBoolAt stFull idx := by
    intro idx hidx
    have happ : stFull = evalMicroList 35 zrBarrel55Ops stClz91 := by
      dsimp [stFull, zrClz17Barrel55Ops, stClz91]
      rw [evalMicroList_append, clz17Ops_meta.2.1]
    rw [happ]
    exact evalMicroList_ext_below zrBarrel55Ops 35 (initBoolList 35 91 m35) stClz91
      zr_barrel55Ops_meta.1
      (by dsimp [initBoolList]; rw [length_mkBoolList, zr_barrel55Ops_meta.2.1])
      (by dsimp [stClz91]
          have hlen_pres : ∀ (ops : List MicroOp) (top : ℕ) (st : List Bool),
              (evalMicroList top ops st).length = st.length := by
            intro ops; induction ops with
            | nil => intro _ _; rfl
            | cons op rest ih =>
                intro top st; cases op <;> simp [evalMicroList, ih, length_setBoolAt]
          rw [hlen_pres, show (initBoolList 18 91 s).length = 91 from by
            dsimp [initBoolList]; exact length_mkBoolList 18 s 0 91,
            zr_barrel55Ops_meta.2.1])
      hInit35_eq idx (by rw [zr_barrel55Ops_meta.2.1]; exact hidx)
  obtain ⟨_, hmSpec⟩ := zr_clz17Barrel55Ops_spec s hs
  have hmVal : bitsVal (fun j : Fin 18 ↦ β₂ (zrMantW411 j)) = norm1sMant18 s := by
    apply bitsVal_eq_of_testBit _ _ (n1s_norm1sMant18_lt s hs)
    intro j
    have hwire : zrMantW411 j = ⟨292 + ((73 + j.val) - 35), by omega⟩ :=
      Fin.ext (by dsimp [zrMantW411]; omega)
    rw [hwire]
    dsimp only [β₂]
    rw [hout₂ (73 + j.val) (by omega) (by omega), hBar_eq_Full (73 + j.val) (by omega), hmSpec j]
    cases (norm1sMant18 s).testBit j.val <;> rfl
  exact ⟨hcl₁, hpres₁, hcl₂, hpres₂, hmVal⟩

/- ### Section 4B.3: Permuted `< 371` Booth + `55`-`TempAnd` Barrel Plug on `Wire 411` -/

theorem zr_cliff_onRegister_comp {m₁ m₂ m₃ : ℕ}
    (r₁ : QRegister m₁ m₂) (r₂ : QRegister m₂ m₃) :
    ∀ c : CliffProg m₁, (c.onRegister r₁).onRegister r₂ = c.onRegister (r₂.compose r₁)
  | .nil => rfl
  | .x _ => rfl
  | .cnot _ _ _ => rfl
  | .seq c₁ c₂ =>
      congrArg₂ CliffProg.seq
        (zr_cliff_onRegister_comp r₁ r₂ c₁)
        (zr_cliff_onRegister_comp r₁ r₂ c₂)

theorem zr_prog_onRegister_comp {m₁ m₂ m₃ : ℕ}
    (r₁ : QRegister m₁ m₂) (r₂ : QRegister m₂ m₃) :
    ∀ p : TempPhaseProg m₁, (p.onRegister r₁).onRegister r₂ = p.onRegister (r₂.compose r₁)
  | .nil => rfl
  | .cliff c => congrArg TempPhaseProg.cliff (zr_cliff_onRegister_comp r₁ r₂ c)
  | .z _ => rfl
  | .seq p₁ p₂ =>
      congrArg₂ TempPhaseProg.seq
        (zr_prog_onRegister_comp r₁ r₂ p₁)
        (zr_prog_onRegister_comp r₁ r₂ p₂)
  | .tempAnd _ _ _ _ _ _ body =>
      congrArg _ (zr_prog_onRegister_comp r₁ r₂ body)

theorem zr_cliff_onRegister_eval {m n : ℕ} (r : QRegister m n) :
    ∀ (c : CliffProg m) (γ : BitAssignment n),
      (∀ j : Wire m, (c.onRegister r).eval γ (r j) = c.eval (fun i ↦ γ (r i)) j) ∧
      (∀ w : Wire n, (∀ j : Wire m, w ≠ r j) → (c.onRegister r).eval γ w = γ w)
  | .nil, _ => ⟨fun _ ↦ rfl, fun _ _ ↦ rfl⟩
  | .x q, γ =>
      ⟨fun j ↦ by
          by_cases hj : j = q
          · subst hj; simp [CliffProg.onRegister, CliffProg.eval]
          · simp [CliffProg.onRegister, CliffProg.eval, Function.update_of_ne hj,
              Function.update_of_ne (r.wires.injective.ne hj)],
       fun w hw ↦ by
          simp [CliffProg.onRegister, CliffProg.eval, Function.update_of_ne (hw q)]⟩
  | .cnot c t h, γ =>
      ⟨fun j ↦ by
          by_cases hj : j = t
          · subst hj; simp [CliffProg.onRegister, CliffProg.eval]
          · simp [CliffProg.onRegister, CliffProg.eval, Function.update_of_ne hj,
              Function.update_of_ne (r.wires.injective.ne hj)],
       fun w hw ↦ by
          simp [CliffProg.onRegister, CliffProg.eval, Function.update_of_ne (hw t)]⟩
  | .seq c₁ c₂, γ => by
      obtain ⟨h1_in, h1_out⟩ := zr_cliff_onRegister_eval r c₁ γ
      let γ₁ := (c₁.onRegister r).eval γ
      obtain ⟨h2_in, h2_out⟩ := zr_cliff_onRegister_eval r c₂ γ₁
      have hpull : (fun i ↦ γ₁ (r i)) = c₁.eval (fun i ↦ γ (r i)) := funext h1_in
      exact ⟨fun j ↦ (h2_in j).trans (by rw [hpull]; rfl),
        fun w hw ↦ (h2_out w hw).trans (h1_out w hw)⟩

theorem zr_prog_onRegister_eval {m n : ℕ} (r : QRegister m n) :
    ∀ (p : TempPhaseProg m) (γ : BitAssignment n),
      (p.onRegister r).evalSign γ = p.evalSign (fun i ↦ γ (r i)) ∧
      (∀ j : Wire m, (p.onRegister r).evalBits γ (r j) = p.evalBits (fun i ↦ γ (r i)) j) ∧
      (∀ w : Wire n, (∀ j : Wire m, w ≠ r j) → (p.onRegister r).evalBits γ w = γ w)
  | .nil, _ => ⟨rfl, fun _ ↦ rfl, fun _ _ ↦ rfl⟩
  | .cliff c, γ => ⟨rfl, (zr_cliff_onRegister_eval r c γ).1, (zr_cliff_onRegister_eval r c γ).2⟩
  | .z _, _ => ⟨rfl, fun _ ↦ rfl, fun _ _ ↦ rfl⟩
  | .seq p₁ p₂, γ => by
      obtain ⟨hs1, h1_in, h1_out⟩ := zr_prog_onRegister_eval r p₁ γ
      let γ₁ := (p₁.onRegister r).evalBits γ
      obtain ⟨hs2, h2_in, h2_out⟩ := zr_prog_onRegister_eval r p₂ γ₁
      have hpull : (fun i ↦ γ₁ (r i)) = p₁.evalBits (fun i ↦ γ (r i)) := funext h1_in
      refine ⟨by dsimp [TempPhaseProg.onRegister, TempPhaseProg.evalSign]; rw [hs1, hs2, hpull],
        fun j ↦ (h2_in j).trans (by rw [hpull]; rfl),
        fun w hw ↦ (h2_out w hw).trans (h1_out w hw)⟩
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, γ => by
      let γ₁ := Function.update γ (r anc) (γ (r anc) + γ (r c₁) * γ (r c₂))
      have hpull₁ : (fun i ↦ γ₁ (r i)) = Function.update (fun i ↦ γ (r i)) anc
          (γ (r anc) + γ (r c₁) * γ (r c₂)) := by
        funext i
        by_cases hi : i = anc
        · subst hi; simp [γ₁]
        · simp [γ₁, Function.update_of_ne hi, Function.update_of_ne (r.wires.injective.ne hi)]
      obtain ⟨hsB, hB_in, hB_out⟩ := zr_prog_onRegister_eval r body γ₁
      refine ⟨by dsimp [TempPhaseProg.onRegister, TempPhaseProg.evalSign]; rw [hsB, hpull₁],
        fun j ↦ ?_, fun w hw ↦ ?_⟩
      · dsimp only [TempPhaseProg.onRegister, TempPhaseProg.evalBits]
        by_cases hj : j = anc
        · subst hj
          simp only [Function.update_self]
          rw [hB_in j, hB_in c₁, hB_in c₂, hpull₁]
        · simp only [Function.update_of_ne hj, Function.update_of_ne (r.wires.injective.ne hj)]
          rw [hB_in j, hpull₁]
      · dsimp only [TempPhaseProg.onRegister, TempPhaseProg.evalBits]
        rw [Function.update_of_ne (hw anc), hB_out w hw]
        exact Function.update_of_ne (hw anc) _ _

/-- Involutive wire swap on `ℕ` sending `[302..320) ↔ [330..348)` (`18` mantissa wires) and
`[348..371) ↔ [379..402)` (`23` Booth scratch wires), fixing all other indices. -/
def zrSwapBoothNat (x : ℕ) : ℕ := if 302 ≤ x ∧ x < 320 then x + 28 else if 330 ≤ x ∧ x < 348
    then x - 28 else if 348 ≤ x ∧ x < 371 then x + 31 else if 379 ≤ x ∧ x < 402 then x - 31
    else x

theorem zr_swapBoothNat_involutive (x : ℕ) : zrSwapBoothNat (zrSwapBoothNat x) = x := by
  unfold zrSwapBoothNat
  split_ifs <;> omega

theorem zr_swapBoothNat_lt_411 {x : ℕ} (hx : x < 411) : zrSwapBoothNat x < 411 := by
  unfold zrSwapBoothNat
  split_ifs <;> omega

/-- Bundled `Wire 411` involutive permutation for `zrSwapBoothNat`. -/
def zrPermBooth411 (w : Wire 411) : Wire 411 :=
  ⟨zrSwapBoothNat w.val, zr_swapBoothNat_lt_411 w.isLt⟩

theorem zr_permBooth411_involutive (w : Wire 411) : zrPermBooth411 (zrPermBooth411 w) =
    w := Fin.ext (zr_swapBoothNat_involutive w.val)

/-- `QRegister 411 411` wrapper around `zrPermBooth411` (`r w = zrPermBooth411 w`). -/
def zrBoothPermReg : QRegister 411 411 :=
  ⟨⟨zrPermBooth411, Function.Involutive.injective zr_permBooth411_involutive⟩⟩

theorem zr_permBooth411_lt302 {w : Wire 411} (hw : w.val < 302) :
    zrPermBooth411 w = w := by
  apply Fin.ext
  unfold zrPermBooth411 zrSwapBoothNat
  dsimp only
  split_ifs <;> omega

theorem zr_permBooth411_mant (j : Fin 18) :
    zrPermBooth411 (n1sMantW411 j) = zrMantW411 j := by
  apply Fin.ext
  dsimp only [zrPermBooth411, n1sMantW411, zrMantW411]
  unfold zrSwapBoothNat
  split_ifs <;> omega

theorem zr_prog_permBooth_eval (p : TempPhaseProg 411) (γ : BitAssignment 411) :
    (p.onRegister zrBoothPermReg).evalSign γ = p.evalSign (fun i ↦ γ (zrPermBooth411 i)) ∧
    (∀ w : Wire 411, (p.onRegister zrBoothPermReg).evalBits γ w =
      p.evalBits (fun i ↦ γ (zrPermBooth411 i)) (zrPermBooth411 w)) := by
  obtain ⟨hs, hin, _⟩ := zr_prog_onRegister_eval zrBoothPermReg p γ
  refine ⟨hs, fun w ↦ ?_⟩
  have hw := hin (zrPermBooth411 w)
  change (p.onRegister zrBoothPermReg).evalBits γ (zrPermBooth411 (zrPermBooth411 w)) = _ at hw
  rwa [zr_permBooth411_involutive] at hw

/-- Wire-domain mask for `n1sBoothFwd411` and `n1sBoothRevStatic411`: `< 320` or `[379, 402)`. -/
def zrInBoothDomB (w : Wire 411) : Bool :=
  decide (w.val < 320 ∨ (379 ≤ w.val ∧ w.val < 402))

theorem zr_permBooth411_lt371_of_dom {w : Wire 411} (hw : zrInBoothDomB w = true) :
    (zrPermBooth411 w).val < 371 := by
  have hd : w.val < 320 ∨ (379 ≤ w.val ∧ w.val < 402) := of_decide_eq_true hw
  dsimp only [zrPermBooth411]
  unfold zrSwapBoothNat
  split_ifs <;> omega

/-- Checks that every wire of `c : CliffProg 411` lies in `zrInBoothDomB`. -/
def zrCliffInBoothDom : CliffProg 411 → Bool
  | .nil => true
  | .x q => zrInBoothDomB q
  | .cnot c t _ => zrInBoothDomB c && zrInBoothDomB t
  | .seq c₁ c₂ => zrCliffInBoothDom c₁ && zrCliffInBoothDom c₂

/-- Checks that every wire of `p : TempPhaseProg 411` lies in `zrInBoothDomB`. -/
def zrProgInBoothDom : TempPhaseProg 411 → Bool
  | .nil => true
  | .cliff c => zrCliffInBoothDom c
  | .z q => zrInBoothDomB q
  | .seq p₁ p₂ => zrProgInBoothDom p₁ && zrProgInBoothDom p₂
  | .tempAnd c₁ c₂ anc _ _ _ body =>
      zrInBoothDomB c₁ && zrInBoothDomB c₂ && zrInBoothDomB anc && zrProgInBoothDom body

theorem zr_cliff_permBooth_supportsBelowB371 :
    ∀ (c : CliffProg 411), zrCliffInBoothDom c = true →
      cliffSupportsBelowB 371 (c.onRegister zrBoothPermReg) = true
  | .nil, _ => rfl
  | .x q, hq => decide_eq_true (zr_permBooth411_lt371_of_dom hq)
  | .cnot c t _, hct => by
      obtain ⟨hc, ht⟩ := (Bool.and_eq_true _ _).mp hct
      exact (Bool.and_eq_true _ _).mpr ⟨decide_eq_true (zr_permBooth411_lt371_of_dom hc),
        decide_eq_true (zr_permBooth411_lt371_of_dom ht)⟩
  | .seq c₁ c₂, h12 => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      exact (Bool.and_eq_true _ _).mpr ⟨zr_cliff_permBooth_supportsBelowB371 c₁ h1,
        zr_cliff_permBooth_supportsBelowB371 c₂ h2⟩

theorem zr_prog_permBooth_supportsBelowB371 :
    ∀ (p : TempPhaseProg 411), zrProgInBoothDom p = true →
      progSupportsBelowB 371 (p.onRegister zrBoothPermReg) = true
  | .nil, _ => rfl
  | .cliff c, hc => zr_cliff_permBooth_supportsBelowB371 c hc
  | .z q, hq => decide_eq_true (zr_permBooth411_lt371_of_dom hq)
  | .seq p₁ p₂, h12 => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      exact (Bool.and_eq_true _ _).mpr ⟨zr_prog_permBooth_supportsBelowB371 p₁ h1,
        zr_prog_permBooth_supportsBelowB371 p₂ h2⟩
  | .tempAnd c₁ c₂ anc _ _ _ body, hall => by
      obtain ⟨h12a, hb⟩ := (Bool.and_eq_true _ _).mp hall
      obtain ⟨h12, ha⟩ := (Bool.and_eq_true _ _).mp h12a
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      exact (Bool.and_eq_true _ _).mpr ⟨decide_eq_true (zr_permBooth411_lt371_of_dom h1),
        (Bool.and_eq_true _ _).mpr ⟨decide_eq_true (zr_permBooth411_lt371_of_dom h2),
        (Bool.and_eq_true _ _).mpr ⟨decide_eq_true (zr_permBooth411_lt371_of_dom ha),
        zr_prog_permBooth_supportsBelowB371 body hb⟩⟩⟩

theorem zr_cliff_eval_unchanged_of_dom :
    ∀ (c : CliffProg 411), zrCliffInBoothDom c = true →
      ∀ (β : BitAssignment 411) (w : Wire 411),
        zrInBoothDomB w = false → c.eval β w = β w
  | .nil, _, _, _, _ => rfl
  | .x q, hq, β, w, hw =>
      Function.update_of_ne (fun h ↦ by
        subst h; dsimp [zrCliffInBoothDom] at hq; rw [hq] at hw; exact Bool.noConfusion hw) _ _
  | .cnot _ t _, hct, β, w, hw => by
      obtain ⟨_, ht⟩ := (Bool.and_eq_true _ _).mp hct
      exact Function.update_of_ne (fun h ↦ by subst h; rw [ht] at hw; exact Bool.noConfusion hw) _ _
  | .seq c₁ c₂, h12, β, w, hw => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      exact (zr_cliff_eval_unchanged_of_dom c₂ h2 _ w hw).trans
        (zr_cliff_eval_unchanged_of_dom c₁ h1 _ w hw)

theorem zr_prog_eval_unchanged_of_dom :
    ∀ (p : TempPhaseProg 411), zrProgInBoothDom p = true →
      ∀ (β : BitAssignment 411) (w : Wire 411),
        zrInBoothDomB w = false → p.evalBits β w = β w
  | .nil, _, _, _, _ => rfl
  | .cliff c, hc, β, w, hw => zr_cliff_eval_unchanged_of_dom c hc β w hw
  | .z _, _, _, _, _ => rfl
  | .seq p₁ p₂, h12, β, w, hw => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      exact (zr_prog_eval_unchanged_of_dom p₂ h2 _ w hw).trans
        (zr_prog_eval_unchanged_of_dom p₁ h1 _ w hw)
  | .tempAnd c₁ c₂ anc _ _ _ body, hall, β, w, hw => by
      dsimp [zrProgInBoothDom] at hall
      simp only [Bool.and_eq_true] at hall
      obtain ⟨⟨⟨_, _⟩, ha⟩, hb⟩ := hall
      have hne : w ≠ anc := fun h ↦ by subst h; rw [ha] at hw; exact Bool.noConfusion hw
      dsimp only [TempPhaseProg.evalBits]
      rw [Function.update_of_ne hne, zr_prog_eval_unchanged_of_dom body hb _ w hw]
      exact Function.update_of_ne hne _ _

theorem zr_cleanRem_pull_permBooth {rem : ℕ} (hrem : rem ≤ 32) {γ : BitAssignment 411}
    (hγ : cleanRem 411 (rem + 31) γ) : cleanRem 411 rem (fun i ↦ γ (zrPermBooth411 i)) := by
  intro w hw
  apply hγ (zrPermBooth411 w)
  dsimp only [zrPermBooth411]
  unfold zrSwapBoothNat
  split_ifs <;> omega

theorem zr_validCleanRem_permBooth :
    ∀ (p : TempPhaseProg 411), zrProgInBoothDom p = true →
      ∀ (rem : ℕ), 9 ≤ rem → rem ≤ 32 → ValidCleanRem 411 rem p →
        ValidCleanRem 411 (rem + 31) (p.onRegister zrBoothPermReg)
  | .nil, _, _, _, _, _ => trivial
  | .cliff _, _, _, _, _, _ => trivial
  | .z _, _, _, _, _, _ => trivial
  | .seq p₁ p₂, h12, rem, hrem9, hrem, ⟨remMid, _, hv₁, hv₂, hcl⟩ => by
      obtain ⟨hp1, hp2⟩ := (Bool.and_eq_true _ _).mp h12
      have hmid32 : remMid ≤ 32 := by
        by_contra hgt
        let β₀ : BitAssignment 411 := fun w ↦ if w.val < 379 then 1 else 0
        have hcl₀ : cleanRem 411 rem β₀ := fun w hw ↦ by
          dsimp [β₀]; exact ite_eq_right (by omega)
        have hcl₁ := hcl β₀ hcl₀ ⟨378, by decide⟩ (by dsimp; omega)
        have hunch := zr_prog_eval_unchanged_of_dom p₁ hp1 β₀ ⟨378, by decide⟩ (by decide)
        rw [hunch] at hcl₁
        have h1 : β₀ ⟨378, by decide⟩ = 1 := rfl
        rw [h1] at hcl₁
        exact one_ne_zero hcl₁
      let remMid' := max remMid 9
      have hv₂' : ValidCleanRem 411 remMid' p₂ :=
        validCleanRem_mono (Nat.le_max_left remMid 9) hv₂
      refine ⟨remMid' + 31, by omega,
        zr_validCleanRem_permBooth p₁ hp1 rem hrem9 hrem hv₁,
        zr_validCleanRem_permBooth p₂ hp2 remMid' (Nat.le_max_right remMid 9) (by omega) hv₂',
        fun γ hγ u hu ↦ ?_⟩
      rw [(zr_prog_permBooth_eval p₁ γ).2 u]
      have hcl_in := zr_cleanRem_pull_permBooth hrem hγ
      by_cases hu371 : u.val < 371
      · apply hcl _ hcl_in (zrPermBooth411 u)
        dsimp only [zrPermBooth411, remMid'] at hu ⊢
        unfold zrSwapBoothNat
        split_ifs <;> omega
      · have hfalse : zrInBoothDomB (zrPermBooth411 u) = false := by
          rw [zrInBoothDomB, decide_eq_false_iff_not]
          dsimp only [zrPermBooth411]
          unfold zrSwapBoothNat
          split_ifs <;> omega
        rw[zr_prog_eval_unchanged_of_dom p₁ hp1 _ _ hfalse, zr_permBooth411_involutive]
        exact hγ u (by omega)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, hall, rem, _, hrem, ⟨hanc_lo, hvBody, hpres⟩ => by
      dsimp [zrProgInBoothDom] at hall
      simp only [Bool.and_eq_true] at hall
      obtain ⟨⟨⟨_, _⟩, ha⟩, hb⟩ := hall
      have hanc_dom : anc.val < 320 ∨ (379 ≤ anc.val ∧ anc.val < 402) := of_decide_eq_true ha
      have hanc_val : (zrPermBooth411 anc).val = anc.val - 31 := by
        dsimp only [zrPermBooth411]
        unfold zrSwapBoothNat
        split_ifs <;> omega
      have hrem_eq : (411 - (anc.val + 1)) + 31 = 411 - ((zrPermBooth411 anc).val + 1) := by
        rw [hanc_val]; omega
      have hvB' : ValidCleanRem 411 (411 - ((zrPermBooth411 anc).val + 1))
          (body.onRegister zrBoothPermReg) := hrem_eq ▸ zr_validCleanRem_permBooth body hb
          (411 - (anc.val + 1)) (by omega) (by omega) hvBody
      refine ⟨by change 411 - (rem + 31) ≤ (zrPermBooth411 anc).val; omega, hvB', fun γ₁ hγ₁ ↦ ?_⟩
      have hγ₁' : cleanRem 411 (411 - ((zrPermBooth411 anc).val + 1)) γ₁ := hγ₁
      have hcl₁ : cleanRem 411 (411 - (anc.val + 1)) (fun i ↦ γ₁ (zrPermBooth411 i)) :=
        zr_cleanRem_pull_permBooth (by omega) (hrem_eq.symm ▸ hγ₁')
      obtain ⟨hp1, hp2, hpa⟩ := hpres _ hcl₁
      have hev := (zr_prog_permBooth_eval body γ₁).2
      change (body.onRegister zrBoothPermReg).evalBits γ₁ (zrPermBooth411 c₁) = γ₁
        (zrPermBooth411 c₁) ∧ (body.onRegister zrBoothPermReg).evalBits γ₁
        (zrPermBooth411 c₂) = γ₁ (zrPermBooth411 c₂) ∧
        (body.onRegister zrBoothPermReg).evalBits γ₁ (zrPermBooth411 anc) = γ₁
        (zrPermBooth411 anc)
      rw [hev (zrPermBooth411 c₁), hev (zrPermBooth411 c₂), hev (zrPermBooth411 anc),
        zr_permBooth411_involutive, zr_permBooth411_involutive, zr_permBooth411_involutive]
      exact ⟨hp1, hp2, hpa⟩

set_option maxRecDepth 16384 in
theorem zr_boothProgs_inBoothDom (t : Norm1sTier) : zrProgInBoothDom (n1sBoothFwd411 t) =
    true ∧ zrProgInBoothDom (n1sBoothRevStatic411 t) = true := by
  cases t <;> decide

/-- Permuted `< 371` forward Booth program on `Wire 411` (`mant` at `[330..348)`, scratch
`[348..371)`). -/
def zrBoothFwd411 (t : Norm1sTier) : TempPhaseProg 411 :=
  (n1sBoothFwd411 t).onRegister zrBoothPermReg

/-- Permuted `< 371` reverse static Booth program on `Wire 411`. -/
def zrBoothRevStatic411 (t : Norm1sTier) : TempPhaseProg 411 :=
  (n1sBoothRevStatic411 t).onRegister zrBoothPermReg

def zrBoothDoneInv (t : Norm1sTier) (γ : BitAssignment 411) : Prop := bitsVal
    (fun j : Fin 32 ↦ γ (n1sOut32W411 j)) = norm1sHwProd t.kBits t.dCut
    (bitsVal (fun i : Fin 18 ↦ γ (zrMantW411 i)))
    (bitsVal (fun k : Fin t.kBits ↦ γ (n1sUKW411 t k)))

theorem zr_boothDoneInv_iff_pull (t : Norm1sTier) (γ : BitAssignment 411) :
    zrBoothDoneInv t γ ↔ n1sBoothDoneInv t (fun w ↦ γ (zrPermBooth411 w)) := by
  unfold zrBoothDoneInv n1sBoothDoneInv
  have hout : (fun j : Fin 32 ↦ γ (zrPermBooth411 (n1sOut32W411 j))) =
      fun j ↦ γ (n1sOut32W411 j) :=
    funext fun j ↦ congrArg γ (zr_permBooth411_lt302 (by dsimp [n1sOut32W411]; omega))
  have hmant : (fun i : Fin 18 ↦ γ (zrPermBooth411 (n1sMantW411 i))) = fun i ↦ γ
      (zrMantW411 i) := funext fun i ↦ congrArg γ (zr_permBooth411_mant i)
  have huk : (fun k : Fin t.kBits ↦ γ (zrPermBooth411 (n1sUKW411 t k))) = fun k ↦ γ
      (n1sUKW411 t k) := funext fun k ↦ congrArg γ (zr_permBooth411_lt302 (lt_trans
      (n1s_uKW411_range t k).2 (by decide)))
  rw [hout, hmant, huk]

theorem zr_boothFwd411_spec (t : Norm1sTier) : progSupportsBelowB 371 (zrBoothFwd411 t) =
    true ∧ (zrBoothFwd411 t).countTempAnd = n1sBoothFwdAnds t ∧ ValidCleanRem 411
    (411 - 348) (zrBoothFwd411 t) ∧ (∀ γ : BitAssignment 411, cleanRem 411 (411 - 348) γ →
    (zrBoothFwd411 t).evalSign γ = 0 ∧ cleanRem 411 (411 - 348) ((zrBoothFwd411
    t).evalBits γ) ∧ (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → (zrBoothFwd411
    t).evalBits γ q = γ q) ∧ ((∀ k : Fin 32, γ (n1sOut32W411 k) = 0) → bitsVal (fun k : Fin 32
    ↦ (zrBoothFwd411 t).evalBits γ (n1sOut32W411 k)) = norm1sHwProd t.kBits t.dCut (bitsVal
    (fun i : Fin 18 ↦ γ (zrMantW411 i))) (bitsVal (fun k : Fin t.kBits ↦ γ (n1sUKW411 t
    k))))) := by
  have hdom := (zr_boothProgs_inBoothDom t).1
  obtain ⟨hv0, hEv0⟩ := n1s_boothFwd411_spec t
  refine ⟨zr_prog_permBooth_supportsBelowB371 _ hdom, ((n1sBoothFwd411
    t).onRegister_countTempAnd zrBoothPermReg).trans (n1s_boothFwd411_countTempAnd t),
    zr_validCleanRem_permBooth _ hdom (411 - 379) (by decide) (by decide) hv0, fun γ hγ ↦
    ?_⟩
  let β : BitAssignment 411 := fun i ↦ γ (zrPermBooth411 i)
  have hcl_β : cleanRem 411 (411 - 379) β := zr_cleanRem_pull_permBooth (by decide) hγ
  obtain ⟨hs0, _, hnon0, hval0⟩ := hEv0 β hcl_β
  obtain ⟨hsP, hbitsP⟩ := zr_prog_permBooth_eval (n1sBoothFwd411 t) γ
  have hnon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (zrBoothFwd411 t).evalBits γ q = γ q := fun q hq ↦ by
    dsimp only [zrBoothFwd411]
    rw [hbitsP q, hnon0 (zrPermBooth411 q) (fun k hk ↦ hq k (by
      have h1 := congrArg zrPermBooth411 hk
      rw [zr_permBooth411_involutive, zr_permBooth411_lt302 (by dsimp [n1sOut32W411]; omega)] at h1
      exact h1))]
    exact congrArg γ (zr_permBooth411_involutive q)
  refine ⟨hsP.trans hs0,
    fun w hw ↦ (hnon w (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))).trans (hγ w hw),
    hnon, fun hout0 ↦ ?_⟩
  have hout0_β : ∀ k : Fin 32, β (n1sOut32W411 k) = 0 := fun k ↦ by
    dsimp [β]
    rw [zr_permBooth411_lt302 (by dsimp [n1sOut32W411]; omega)]
    exact hout0 k
  have hd := hval0 hout0_β
  unfold n1sBoothDoneInv at hd
  have hout_eq : bitsVal (fun k : Fin 32 ↦ (zrBoothFwd411 t).evalBits γ (n1sOut32W411 k)) =
      bitsVal (fun k : Fin 32 ↦ (n1sBoothFwd411 t).evalBits β (n1sOut32W411 k)) :=
    congrArg bitsVal (funext fun k ↦ by
      dsimp only [zrBoothFwd411]
      rw [hbitsP (n1sOut32W411 k), zr_permBooth411_lt302 (by dsimp [n1sOut32W411]; omega)])
  have hmant : (fun i : Fin 18 ↦ (n1sBoothFwd411 t).evalBits β (n1sMantW411 i)) =
      fun i ↦ γ (zrMantW411 i) :=
    funext fun i ↦
      (hnon0 (n1sMantW411 i)
        (fun k ↦ wire_ne_of_gt (by dsimp [n1sMantW411, n1sOut32W411]; omega))).trans
        (congrArg γ (zr_permBooth411_mant i))
  have huk : (fun k : Fin t.kBits ↦ (n1sBoothFwd411 t).evalBits β (n1sUKW411 t k)) =
      fun k ↦ γ (n1sUKW411 t k) :=
    funext fun k ↦
      (hnon0 (n1sUKW411 t k)
        (fun j ↦ wire_ne_of_lt (by
          have := (n1s_uKW411_range t k).2; dsimp [n1sOut32W411]; omega))).trans
        (congrArg γ (zr_permBooth411_lt302
          (lt_trans (n1s_uKW411_range t k).2 (by decide))))
  rw [hout_eq, hd, hmant, huk]

set_option maxHeartbeats 800000 in
-- Reverse static 411-wire Booth permutation support and clean-remainder proof
theorem zr_boothRevStatic411_spec (t : Norm1sTier) : progSupportsBelowB 371
    (zrBoothRevStatic411 t) = true ∧ ValidCleanRem 411 (411 - 348) (zrBoothRevStatic411 t)
    ∧ (∀ γ : BitAssignment 411, cleanRem 411 (411 - 348) γ → (zrBoothRevStatic411
    t).evalSign γ = 0 ∧ cleanRem 411 (411 - 348) ((zrBoothRevStatic411 t).evalBits γ) ∧ (∀ q
    : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → (zrBoothRevStatic411 t).evalBits γ q =
    γ q) ∧ (zrBoothDoneInv t γ → ∀ k : Fin 32, (zrBoothRevStatic411 t).evalBits γ
    (n1sOut32W411 k) = 0)) := by
  have hdom := (zr_boothProgs_inBoothDom t).2
  obtain ⟨hv0, hEv0⟩ := n1s_boothRevStatic411_spec t
  refine ⟨zr_prog_permBooth_supportsBelowB371 _ hdom, zr_validCleanRem_permBooth _ hdom
    (411 - 379) (by decide) (by decide) hv0, fun γ hγ ↦ ?_⟩
  let β : BitAssignment 411 := fun i ↦ γ (zrPermBooth411 i)
  have hcl_β : cleanRem 411 (411 - 379) β := zr_cleanRem_pull_permBooth (by decide) hγ
  obtain ⟨hs0, _, hnon0, hzero0⟩ := hEv0 β hcl_β
  obtain ⟨hsP, hbitsP⟩ := zr_prog_permBooth_eval (n1sBoothRevStatic411 t) γ
  have hnon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (zrBoothRevStatic411 t).evalBits γ q = γ q := fun q hq ↦ by
    dsimp only [zrBoothRevStatic411]
    rw [hbitsP q, hnon0 (zrPermBooth411 q) (fun k hk ↦ hq k (by
      have h1 := congrArg zrPermBooth411 hk
      rw [zr_permBooth411_involutive, zr_permBooth411_lt302 (by dsimp [n1sOut32W411]; omega)] at h1
      exact h1))]
    exact congrArg γ (zr_permBooth411_involutive q)
  refine ⟨hsP.trans hs0,
    fun w hw ↦ (hnon w (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))).trans (hγ w hw),
    hnon, fun hDone k ↦ ?_⟩
  dsimp only [zrBoothRevStatic411]
  rw [hbitsP (n1sOut32W411 k), zr_permBooth411_lt302 (by dsimp [n1sOut32W411]; omega)]
  exact hzero0 ((zr_boothDoneInv_iff_pull t γ).mp hDone) k

/-- Checks that every wire of `K : TempCtx 411` lies in `zrInBoothDomB`. -/
def zrCtxInBoothDom : TempCtx 411 → Bool
  | .hole => true
  | .seqPre c K => zrCliffInBoothDom c && zrCtxInBoothDom K
  | .seqPost K c => zrCtxInBoothDom K && zrCliffInBoothDom c
  | .tempAnd c₁ c₂ anc _ _ _ K =>
      zrInBoothDomB c₁ && zrInBoothDomB c₂ && zrInBoothDomB anc && zrCtxInBoothDom K

theorem zr_cliff_not_mem_support_of_dom {n : ℕ} (rBooth : QRegister 411 n) (x : Wire n)
    (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) :
    ∀ (c : CliffProg 411), zrCliffInBoothDom c = true →
      x ∉ ((c.onRegister rBooth).toCircuit).support
  | .nil, _ => by simp [CliffProg.onRegister, CliffProg.toCircuit]
  | .x q, hq => by simp [CliffProg.onRegister, CliffProg.toCircuit, hx q hq]
  | .cnot c t _, hct => by
      obtain ⟨hc, ht⟩ := (Bool.and_eq_true _ _).mp hct
      simp [CliffProg.onRegister, CliffProg.toCircuit, hx c hc, hx t ht]
  | .seq c₁ c₂, h12 => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      simp only [CliffProg.onRegister, CliffProg.toCircuit, Circuit.support_seq, Finset.mem_union,
        not_or]
      exact ⟨zr_cliff_not_mem_support_of_dom rBooth x hx c₁ h1,
        zr_cliff_not_mem_support_of_dom rBooth x hx c₂ h2⟩

theorem zr_p57ToDynWith_not_mem_support_of_dom {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) (x : Wire n)
    (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q)
    (dInner : DynamicCircuit Var n) (hIn : x ∉ dInner.support) :
    ∀ (K : TempCtx 411), zrCtxInBoothDom K = true →
      x ∉ (p57ToDynWith v rBooth dInner K).support
  | .hole, _ => hIn
  | .seqPre c K, hcK => by
      obtain ⟨hc, hK⟩ := (Bool.and_eq_true _ _).mp hcK
      simp only [p57ToDynWith, DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
        Finset.mem_union, not_or]
      exact ⟨zr_cliff_not_mem_support_of_dom rBooth x hx c hc,
        zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx dInner hIn K hK⟩
  | .seqPost K c, hKc => by
      obtain ⟨hK, hc⟩ := (Bool.and_eq_true _ _).mp hKc
      simp only [p57ToDynWith, DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
        Finset.mem_union, not_or]
      exact ⟨zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx dInner hIn K hK,
        zr_cliff_not_mem_support_of_dom rBooth x hx c hc⟩
  | .tempAnd c₁ c₂ anc _ _ _ K, hall => by
      obtain ⟨h12a, hK⟩ := (Bool.and_eq_true _ _).mp hall
      obtain ⟨h12, ha⟩ := (Bool.and_eq_true _ _).mp h12a
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      simp only [p57ToDynWith, DynamicCircuit.support_seq, DynamicCircuit.support_andCompute,
        DynamicCircuit.support_andUncompute, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨⟨hx c₁ h1, hx c₂ h2, hx anc ha⟩, zr_p57ToDynWith_not_mem_support_of_dom v
        rBooth x hx dInner hIn K hK, ⟨hx c₁ h1, hx c₂ h2, hx anc ha⟩⟩

theorem zr_ctxCleanMsbSub_inBoothDom :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ 411)
      (_hlo : 379 ≤ cur) (_hhi : cur + W ≤ 402)
      (b acc : Fin (W + 1) → Wire 411) (msb cin : Wire 411)
      (hab : ∀ j, acc j ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (hmc : msb ≠ cin)
      (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur)
      (hmsb : msb.val < cur) (hc : cin.val < cur)
      (_hbD : ∀ j, zrInBoothDomB (b j) = true)
      (_haD : ∀ j, zrInBoothDomB (acc j) = true)
      (_hmD : zrInBoothDomB msb = true)
      (_hcD : zrInBoothDomB cin = true),
      zrCtxInBoothDom
        (ctxCleanMsbSub W cur hcur b acc msb cin hab hac hbc hmc hb ha hmsb hc) = true
  | 0, _, _, _, _, b, acc, msb, cin, _, _, _, _, _, _, _, _, hbD, haD, hmD, hcD => by
      simp [ctxCleanMsbSub, zrCtxInBoothDom, zrCliffInBoothDom, hbD 0, haD 0, hmD, hcD]
  | W + 1, cur, hcur, hlo, hhi, b, acc, msb, cin, hab, hac, hbc, hmc, hb, ha, hmsb, hc,
      hbD, haD, hmD, hcD => by
      have hcoutD : zrInBoothDomB ⟨cur, by omega⟩ = true :=
        decide_eq_true (Or.inr ⟨by dsimp; omega, by dsimp; omega⟩)
      have hrec := zr_ctxCleanMsbSub_inBoothDom W (cur + 1) (by omega) (by omega) (by omega)
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) msb ⟨cur, by omega⟩
        (fun j ↦ hab j.succ)
        (fun j ↦ wire_ne_of_lt (by have := ha j.succ; dsimp; omega))
        (fun j ↦ wire_ne_of_lt (by have := hb j.succ; dsimp; omega))
        (wire_ne_of_lt (by dsimp; omega))
        (fun j ↦ lt_trans (hb j.succ) (by omega))
        (fun j ↦ lt_trans (ha j.succ) (by omega))
        (lt_trans hmsb (by omega))
        (by dsimp; omega)
        (fun j ↦ hbD j.succ) (fun j ↦ haD j.succ) hmD hcoutD
      simp [ctxCleanMsbSub, zrCtxInBoothDom, zrCliffInBoothDom,
        hbD 0, haD 0, hcD, hcoutD, hrec]

theorem zr_dCleanMsbSub_not_mem_support {Var : Type} {n : ℕ} (v : Var)
    (rBooth : QRegister 411 n) (x : Wire n)
    (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) (W cur : ℕ)
    (hcur : cur + W ≤ 411) (hlo : 379 ≤ cur) (hhi : cur + W ≤ 402)
    (b acc : Fin (W + 1) → Wire 411) (msb cin : Wire 411) (hab : ∀ j, acc j ≠ b j)
    (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin) (hmc : msb ≠ cin)
    (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hmsb : msb.val < cur)
    (hc : cin.val < cur) (hbD : ∀ j, zrInBoothDomB (b j) = true)
    (haD : ∀ j, zrInBoothDomB (acc j) = true) (hmD : zrInBoothDomB msb = true)
    (hcD : zrInBoothDomB cin = true) : x ∉ (dCleanMsbSub v rBooth W cur hcur b acc msb cin
    hab hac hbc hmc hb ha hmsb hc).support := by
  dsimp only [dCleanMsbSub]
  refine zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx _ ?_ _
    (zr_ctxCleanMsbSub_inBoothDom W cur hcur hlo hhi b acc msb cin
      hab hac hbc hmc hb ha hmsb hc hbD haD hmD hcD)
  simp only [DynamicCircuit.support_andUncompute, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hx _ (haD (Fin.last W)), hx _ (hbD (Fin.last W)), hx _ hmD⟩

theorem zr_bLowR_inBoothDom (w : ℕ) (hw : w ≤ 18) (j : Fin (w + 1)) :
    zrInBoothDomB (n1sBLowR w hw j) = true := by
  cases j using Fin.lastCases with
  | last => simp [n1sBLowR, n1sInvW411, zrInBoothDomB]
  | cast j =>
      simp only [n1sBLowR, Fin.snoc_castSucc]
      exact decide_eq_true (Or.inl (by dsimp [n1sMantW411]; omega))

theorem zr_accSlice_inBoothDom (off len : ℕ) (h : off + len ≤ 32) (j : Fin len) :
    zrInBoothDomB (n1sAccSlice off len h j) = true :=
  decide_eq_true (Or.inl (by dsimp [n1sAccSlice, n1sOut32W411]; omega))

theorem zr_flipMantSlice_inBoothDom (off : ℕ) :
    ∀ (w : ℕ) (hoff : off + w ≤ 18), zrCliffInBoothDom (n1sFlipMantSlice off w hoff) = true
  | 0, _ => rfl
  | w + 1, hoff => by
      have hm : zrInBoothDomB (n1sMantW411 ⟨off + w, by omega⟩) = true :=
        decide_eq_true (Or.inl (by dsimp [n1sMantW411]; omega))
      have hc : zrInBoothDomB n1sCinW411 = true := by decide
      simp [n1sFlipMantSlice, zrCliffInBoothDom, hc, hm,
        zr_flipMantSlice_inBoothDom off w (by omega)]

theorem zr_cRowSetup_inBoothDom (uW : Wire 411) (hu320 : uW.val < 320)
    (hu : uW.val < 379) (off w : ℕ) (hoff : off + w ≤ 18) :
    zrCliffInBoothDom (n1sCRowSetup uW hu off w hoff) = true := by
  have huD : zrInBoothDomB uW = true := decide_eq_true (Or.inl hu320)
  have hcD : zrInBoothDomB n1sCinW411 = true := by decide
  have hiD : zrInBoothDomB n1sInvW411 = true := by decide
  simp [n1sCRowSetup, zrCliffInBoothDom, huD, hcD, hiD,
    zr_flipMantSlice_inBoothDom off w hoff]

theorem zr_cliff_inv_inBoothDom :
    ∀ (c : CliffProg 411), zrCliffInBoothDom c = true → zrCliffInBoothDom c.inv = true
  | .nil, _ => rfl
  | .x _, h => h
  | .cnot _ _ _, h => h
  | .seq c₁ c₂, h12 => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      exact (Bool.and_eq_true _ _).mpr
        ⟨zr_cliff_inv_inBoothDom c₂ h2, zr_cliff_inv_inBoothDom c₁ h1⟩

theorem zr_cRow0Lt18_inBoothDom (u0 : Wire 411) (hu : u0.val < 201) (dCut : ℕ) :
    ∀ (w : ℕ) (hw : dCut + w ≤ 18), zrCliffInBoothDom (n1sCRow0Lt18 u0 hu dCut w hw) = true
  | 0, _ => rfl
  | w + 1, hw => by
      have huD : zrInBoothDomB u0 = true := decide_eq_true (Or.inl (by omega))
      have hmD : zrInBoothDomB (n1sMantW411 ⟨dCut + w, by omega⟩) = true :=
        decide_eq_true (Or.inl (by dsimp [n1sMantW411]; omega))
      have hoD : zrInBoothDomB (n1sOut32W411 ⟨w, by omega⟩) = true :=
        decide_eq_true (Or.inl (by dsimp [n1sOut32W411]; omega))
      simp [n1sCRow0Lt18, zrCliffInBoothDom, huD, hmD, hoD,
        zr_cRow0Lt18_inBoothDom u0 hu dCut w (by omega)]

private theorem zr_dLowRowRev_not_mem_support (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) (x : Wire n)
    (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q)
    (m : ℕ) (hm1 : 1 ≤ m) (hmd : m < t.dCut) (hw2 : 2 ≤ 18 - (t.dCut - m)) (hmk : m < t.kBits) :
    x ∉ (n1sDLowRowRev t m hm1 hmd hw2 v rBooth).support := by
  dsimp only [n1sDLowRowRev]
  have hu320 : (n1sUKW411 t ⟨m, hmk⟩).val < 320 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  have hsetup := zr_cRowSetup_inBoothDom (n1sUKW411 t ⟨m, hmk⟩) hu320
    (lt_trans hu320 (by decide)) (t.dCut - m) (18 - (t.dCut - m))
    (by have := n1s_tier_bounds t; omega)
  refine zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx _
    (zr_dCleanMsbSub_not_mem_support v rBooth x hx (18 - (t.dCut - m)) 383 _
      (by decide) (by omega) _ _ _ _ _ _ _ _ _ _ _ _
      (zr_bLowR_inBoothDom _ _) (zr_accSlice_inBoothDom _ _ _)
      (decide_eq_true (Or.inl (by dsimp [n1sOut32W411]; omega))) (by decide)) _ ?_
  simp [ctxCliffAlloc, zrCtxInBoothDom, hsetup, zr_cliff_inv_inBoothDom _ hsetup]

theorem zr_dBoothPrefixRev_not_mem_support (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) (x : Wire n)
    (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits), x ∉ (n1sDBoothPrefixRev t v rBooth m hm).support
  | 0, _ => by simp [n1sDBoothPrefixRev, CliffProg.onRegister, CliffProg.toCircuit]
  | 1, _ => by
      dsimp only [n1sDBoothPrefixRev]
      split_ifs with hd18
      · simp [CliffProg.onRegister, CliffProg.toCircuit]
      · simp only [DynamicCircuit.support_circuit]
        refine zr_cliff_not_mem_support_of_dom rBooth x hx _ (zr_cliff_inv_inBoothDom _ ?_)
        have hu201 : (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩).val < 201 :=
          lt_trans (n1s_uKW411_range t _).2 (by decide)
        have hoD : zrInBoothDomB (n1sOut32W411 ⟨18 - t.dCut, by have := n1s_tier_bounds t; omega⟩) =
          true :=
          decide_eq_true (Or.inl (by dsimp [n1sOut32W411]; omega))
        have huD : zrInBoothDomB (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) = true :=
          decide_eq_true (Or.inl (by omega))
        simp[n1sCRow0Full, zrCliffInBoothDom, huD, hoD, zr_cRow0Lt18_inBoothDom _ hu201]
  | 2, _ => by
      rw [n1sDBoothPrefixRev]
      split_ifs with hd18
      · dsimp only [n1sDBaseRevD18]
        have hu0 : zrInBoothDomB (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) = true :=
          decide_eq_true (Or.inl (lt_trans (n1s_uKW411_range t _).2 (by decide)))
        have hu1_320 : (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩).val < 320 :=
          lt_trans (n1s_uKW411_range t _).2 (by decide)
        refine zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx _
          (zr_dCleanMsbSub_not_mem_support v rBooth x hx 1 383 _ (by decide) (by decide) _ _
          _ _ _ _ _ _ _ _ _ _ (zr_bLowR_inBoothDom 1 _) (zr_accSlice_inBoothDom 0 2 _)
          (by decide) hu0) _ ?_
        have hsetup1 := zr_cRowSetup_inBoothDom
          (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) hu1_320
          (lt_trans hu1_320 (by decide)) 17 1 (by decide)
        simp [ctxCliffAlloc, zrCtxInBoothDom, hsetup1, zr_cliff_inv_inBoothDom _ hsetup1]
      · simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
        refine ⟨?_, zr_dBoothPrefixRev_not_mem_support t v rBooth x hx 1 (by
          have := n1s_tier_bounds t; omega)⟩
        exact zr_dLowRowRev_not_mem_support t v rBooth x hx 1 _ _ _
          (by have := n1s_tier_bounds t; omega)
  | m + 3, hm => by
      rw [n1sDBoothPrefixRev]
      have hrest := zr_dBoothPrefixRev_not_mem_support t v rBooth x hx (m + 2) (by omega)
      split_ifs with hlow
      · simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
        refine ⟨?_, hrest⟩
        exact zr_dLowRowRev_not_mem_support t v rBooth x hx (m + 2) _ _ _ (by omega)
      · simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
        refine ⟨?_, hrest⟩
        dsimp only [n1sDHighRowRev]
        have hu320 : (n1sUKW411 t ⟨t.dCut + ((m + 2) - t.dCut), by omega⟩).val < 320 :=
          lt_trans (n1s_uKW411_range t _).2 (by decide)
        have hsetup := zr_cRowSetup_inBoothDom
          (n1sUKW411 t ⟨t.dCut + ((m + 2) - t.dCut), by omega⟩) hu320
          (lt_trans hu320 (by decide)) 0 18 (by decide)
        refine zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx _
          (zr_dCleanMsbSub_not_mem_support v rBooth x hx 18 383 _
            (by decide) (by decide) _ _ _ _ _ _ _ _ _ _ _ _
            (zr_bLowR_inBoothDom 18 le_rfl) (zr_accSlice_inBoothDom _ 19 _)
            (decide_eq_true (Or.inl (by have := n1s_tier_bounds t; dsimp [n1sOut32W411]; omega)))
              (by decide))
          _ ?_
        simp [ctxCliffAlloc, zrCtxInBoothDom, hsetup, zr_cliff_inv_inBoothDom _ hsetup]

def zrPBarFwd411 (t : Norm1sTier) : TempPhaseProg 411 :=
  zrCtxBarrel411.plug (zrBoothFwd411 t)

def zrPBarRev411 (t : Norm1sTier) : TempPhaseProg 411 :=
  zrCtxBarrel411.plug (zrBoothRevStatic411 t)

set_option maxRecDepth 16384 in
theorem zr_ctxBarrel411_supportsBelowB371 :
    ctxSupportsBelowB 371 zrCtxBarrel411 = true := by
  decide

theorem zr_plug_supportsBelowB {M bound : ℕ} {inner : TempPhaseProg M}
    (hIn : progSupportsBelowB bound inner = true) :
    ∀ (K : TempCtx M), ctxSupportsBelowB bound K = true →
      progSupportsBelowB bound (K.plug inner) = true
  | .hole, _ => hIn
  | .seqPre c K, hcK => by
      obtain ⟨hc, hK⟩ := (Bool.and_eq_true _ _).mp hcK
      exact (Bool.and_eq_true _ _).mpr ⟨hc, zr_plug_supportsBelowB hIn K hK⟩
  | .seqPost K c, hKc => by
      obtain ⟨hK, hc⟩ := (Bool.and_eq_true _ _).mp hKc
      exact (Bool.and_eq_true _ _).mpr ⟨zr_plug_supportsBelowB hIn K hK, hc⟩
  | .tempAnd _ _ _ _ _ _ K, hall => by
      dsimp [ctxSupportsBelowB] at hall
      dsimp [TempCtx.plug, progSupportsBelowB]
      simp only [Bool.and_eq_true] at hall ⊢
      exact ⟨hall.1, hall.2.1, hall.2.2.1, zr_plug_supportsBelowB hIn K hall.2.2.2⟩

theorem zr_toDyn_not_mem_support_of_lt {Var : Type} {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (bound : ℕ) :
    ∀ (p : TempPhaseProg M), progSupportsBelowB bound p = true →
      ∀ u : Wire M, bound ≤ u.val → rComb u ∉ ((p.onRegister rComb).toDyn v).support
  | .nil, _, _, _ => by simp [TempPhaseProg.onRegister, TempPhaseProg.toDyn]
  | .cliff c, hc, u, hu => cliff_not_mem_support_of_lt rComb bound c hc u hu
  | .z q, hq, u, hu => by
      have hv : q.val < bound := of_decide_eq_true hq
      have hne : rComb u ≠ rComb q := rComb.wires.injective.ne (fun h ↦ by
        have hv' := congrArg Fin.val h; omega)
      simp [TempPhaseProg.onRegister, TempPhaseProg.toDyn, hne]
  | .seq p₁ p₂, h12, u, hu => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      simp only [TempPhaseProg.onRegister, TempPhaseProg.toDyn, DynamicCircuit.support_seq,
        Finset.mem_union, not_or]
      exact ⟨zr_toDyn_not_mem_support_of_lt v rComb bound p₁ h1 u hu,
        zr_toDyn_not_mem_support_of_lt v rComb bound p₂ h2 u hu⟩
  | .tempAnd c₁ c₂ anc _ _ _ body, hall, u, hu => by
      dsimp [progSupportsBelowB] at hall
      simp only [Bool.and_eq_true] at hall
      obtain ⟨h1, h2, ha, hb⟩ := hall
      have hv1 : c₁.val < bound := of_decide_eq_true h1
      have hv2 : c₂.val < bound := of_decide_eq_true h2
      have hva : anc.val < bound := of_decide_eq_true ha
      have hne1 : rComb u ≠ rComb c₁ := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      have hne2 : rComb u ≠ rComb c₂ := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      have hnea : rComb u ≠ rComb anc := rComb.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; omega)
      simp only [TempPhaseProg.onRegister, TempPhaseProg.toDyn, DynamicCircuit.support_seq,
        DynamicCircuit.support_andCompute, DynamicCircuit.support_andUncompute, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨hne1, hne2, hnea⟩, zr_toDyn_not_mem_support_of_lt v rComb bound body hb u hu,
        ⟨hne1, hne2, hnea⟩⟩

theorem zr_pBarFwd411_spec (t : Norm1sTier) : progSupportsBelowB 371 (zrPBarFwd411 t) =
    true ∧ ValidCleanRem 411 (411 - 292) (zrPBarFwd411 t) ∧ (zrPBarFwd411 t).countTempAnd
    = 55 + n1sBoothFwdAnds t ∧ (∀ γ : BitAssignment 411, cleanRem 411 (411 - 292) γ →
    (zrPBarFwd411 t).evalSign γ = 0 ∧ cleanRem 411 (411 - 292) ((zrPBarFwd411 t).evalBits
    γ) ∧ (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → (zrPBarFwd411 t).evalBits γ q
    = γ q) ∧ ((∀ k : Fin 32, γ (n1sOut32W411 k) = 0) → bitsVal (fun k : Fin 32 ↦
    (zrPBarFwd411 t).evalBits γ (n1sOut32W411 k)) = norm1sHwProd t.kBits t.dCut (bitsVal
    (fun i : Fin 18 ↦ (zrCtxBarrel411.fwdBits γ) (zrMantW411 i))) (bitsVal (fun k : Fin
    t.kBits ↦ (zrCtxBarrel411.fwdBits γ) (n1sUKW411 t k))))) := by
  dsimp only [zrPBarFwd411]
  obtain ⟨hcB, hdB, hsB, hlB⟩ := zr_ctxBarrel411_pkg
  obtain ⟨hsuppIn, hcIn, hvIn, hEvIn⟩ := zr_boothFwd411_spec t
  obtain ⟨hv, _hcnt, hsgn, hbits⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean
      (M := 411) (rem := 411 - 292) (curHole := 348)
      (fun q : Wire 411 ↦ ∃ k : Fin 32, q = n1sOut32W411 k)
      zrCtxBarrel411 hdB hsB (by decide)
      zrCtxBarrel411.fwdBits (TempCtxLiftEx.probe hlB)
      (zrBoothFwd411 t) hvIn
      (fun δ hδ w hnw ↦ (hEvIn δ hδ).2.2.1 w (fun k hk ↦ hnw ⟨k, hk⟩))
  refine ⟨zr_plug_supportsBelowB hsuppIn zrCtxBarrel411 zr_ctxBarrel411_supportsBelowB371,
    hv,
    by rw [TempCtx.plug_countTempAnd, hcB, hcIn],
    fun γ hγ ↦ ?_⟩
  obtain ⟨_, _, _, hBarEv⟩ := zr_ctxBarrel411_scoped
  obtain ⟨hcl₂, hpres₂_raw, _⟩ := hBarEv γ hγ
  have hpres₂ : ∀ w : Wire 411, w.val < 292 → zrCtxBarrel411.fwdBits γ w = γ w :=
    hpres₂_raw (zr_barrel55Ops_allBelow35 (bitsVal (fun i ↦ γ (zrInBarrel35W411 i))))
  obtain ⟨hsI, _, _, hvalI⟩ := hEvIn (zrCtxBarrel411.fwdBits γ) hcl₂
  have hnon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (zrCtxBarrel411.plug (zrBoothFwd411 t)).evalBits γ q = γ q :=
    fun q hq ↦ (hbits γ hγ q).trans (n1s_if_neg (fun ⟨k, hk⟩ ↦ hq k hk))
  refine ⟨(hsgn γ hγ).trans hsI,
    fun w hw ↦ (hnon w (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))).trans (hγ w hw),
    hnon,
    fun hout0 ↦ ?_⟩
  have hout0' : ∀ k : Fin 32, (zrCtxBarrel411.fwdBits γ) (n1sOut32W411 k) = 0 :=
    fun k ↦ (hpres₂ _ (by dsimp [n1sOut32W411]; omega)).trans (hout0 k)
  have heq : bitsVal (fun k : Fin 32 ↦ (zrCtxBarrel411.plug (zrBoothFwd411 t)).evalBits γ
      (n1sOut32W411 k)) = bitsVal (fun k : Fin 32 ↦ (zrBoothFwd411 t).evalBits
      (zrCtxBarrel411.fwdBits γ) (n1sOut32W411 k)) := congrArg bitsVal (funext fun k ↦
      (hbits γ hγ (n1sOut32W411 k)).trans (n1s_if_pos ⟨k, rfl⟩))
  exact heq.trans (hvalI hout0')

theorem zr_pBarRev411_spec (t : Norm1sTier) : progSupportsBelowB 371 (zrPBarRev411 t) =
    true ∧ ValidCleanRem 411 (411 - 292) (zrPBarRev411 t) ∧ (∀ γ : BitAssignment 411,
    cleanRem 411 (411 - 292) γ → (zrPBarRev411 t).evalSign γ = 0 ∧ cleanRem 411 (411 - 292)
    ((zrPBarRev411 t).evalBits γ) ∧ (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
    (zrPBarRev411 t).evalBits γ q = γ q) ∧ (zrBoothDoneInv t (zrCtxBarrel411.fwdBits γ)
    → ∀ k : Fin 32, (zrPBarRev411 t).evalBits γ (n1sOut32W411 k) = 0)) := by
  dsimp only [zrPBarRev411]
  obtain ⟨_, hdB, hsB, hlB⟩ := zr_ctxBarrel411_pkg
  obtain ⟨hsuppIn, hvIn, hEvIn⟩ := zr_boothRevStatic411_spec t
  obtain ⟨hv, _hcnt, hsgn, hbits⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean
      (M := 411) (rem := 411 - 292) (curHole := 348)
      (fun q : Wire 411 ↦ ∃ k : Fin 32, q = n1sOut32W411 k)
      zrCtxBarrel411 hdB hsB (by decide)
      zrCtxBarrel411.fwdBits (TempCtxLiftEx.probe hlB)
      (zrBoothRevStatic411 t) hvIn
      (fun δ hδ w hnw ↦ (hEvIn δ hδ).2.2.1 w (fun k hk ↦ hnw ⟨k, hk⟩))
  refine ⟨zr_plug_supportsBelowB hsuppIn zrCtxBarrel411 zr_ctxBarrel411_supportsBelowB371,
    hv, fun γ hγ ↦ ?_⟩
  obtain ⟨_, _, _, hBarEv⟩ := zr_ctxBarrel411_scoped
  obtain ⟨hcl₂, _, _⟩ := hBarEv γ hγ
  obtain ⟨hsI, _, _, hzeroI⟩ := hEvIn (zrCtxBarrel411.fwdBits γ) hcl₂
  have hnon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (zrCtxBarrel411.plug (zrBoothRevStatic411 t)).evalBits γ q = γ q :=
    fun q hq ↦ (hbits γ hγ q).trans (n1s_if_neg (fun ⟨k, hk⟩ ↦ hq k hk))
  exact ⟨(hsgn γ hγ).trans hsI,
    fun w hw ↦ (hnon w (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))).trans (hγ w hw),
    hnon,
    fun hDone k ↦
      (hbits γ hγ (n1sOut32W411 k)).trans ((n1s_if_pos ⟨k, rfl⟩).trans (hzeroI hDone k))⟩

def zrSwap371 (topW x : ℕ) : ℕ := if 233 ≤ x ∧ x < 254 then topW + (x - 233) else if topW ≤
    x ∧ x < topW + 21 then 233 + (x - topW) else if x = 257 then topW + 21 else if x = topW +
    21 then 257 else if 177 ≤ x ∧ x < 177 + (371 - topW - 22) then (topW + 22) + (x - 177)
    else if topW + 22 ≤ x ∧ x < 371 then 177 + (x - (topW + 22)) else x

/-- Bad-wire predicate for `zrSwap371 topW`. -/
def zrIsBad371 (topW x : ℕ) : Bool :=
  decide ((233 ≤ x ∧ x < 254) ∨ x = 257 ∨ (177 ≤ x ∧ x < 177 + (371 - topW - 22)))

theorem zr_topW_bounds {topW : ℕ} (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) :
    328 ≤ topW ∧ topW ≤ 342 := by
  rcases htop with rfl | rfl | rfl <;> decide

theorem zr_swap371_involutive {topW : ℕ} (htop : topW = 328 ∨ topW = 339 ∨ topW = 342)
    (x : ℕ) : zrSwap371 topW (zrSwap371 topW x) = x := by
  have hb := zr_topW_bounds htop
  set y := zrSwap371 topW x
  have hy : y = zrSwap371 topW x := rfl
  unfold zrSwap371 at hy
  split_ifs at hy <;> (unfold zrSwap371; split_ifs <;> omega)

theorem zr_swap371_lt_437 {topW x : ℕ} (htop : topW = 328 ∨ topW = 339 ∨ topW = 342)
    (hx : x < 437) : zrSwap371 topW x < 437 := by
  have hb := zr_topW_bounds htop
  unfold zrSwap371
  split_ifs <;> omega

/-- Bundled `Wire 437` relay permutation for `zrSwap371 topW`. -/
def zrSwap371W (topW : ℕ) (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) (w : Wire 437) :
    Wire 437 := ⟨zrSwap371 topW w.val, zr_swap371_lt_437 htop w.isLt⟩

/-- Bundled `Wire 437` bad-wire mask for `zrIsBad371 topW`. -/
def zrIsBad371W (topW : ℕ) (w : Wire 437) : Bool := zrIsBad371 topW w.val

theorem zr_validSwapRelayWM_371 {topW : ℕ}
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) :
    ValidSwapRelayWM topW 371 (zrSwap371W topW htop) (zrIsBad371W topW) where
  h275 := by have := zr_topW_bounds htop; omega
  htopM := by have := zr_topW_bounds htop; omega
  hM437 := by decide
  invol w := Fin.ext (zr_swap371_involutive htop w.val)
  fix_ge_M w hw := Fin.ext (by
    have := zr_topW_bounds htop
    dsimp only [zrSwap371W, zrSwap371]
    split_ifs <;> omega)
  fix_not_bad_lt w hlt hnb := Fin.ext (by
    have := zr_topW_bounds htop
    simp only [zrIsBad371W, zrIsBad371, decide_eq_false_iff_not] at hnb
    dsimp only [zrSwap371W, zrSwap371]
    split_ifs <;> omega)
  bad_lt275 w hb := by
    have := zr_topW_bounds htop
    simp only [zrIsBad371W, zrIsBad371, decide_eq_true_eq] at hb
    omega
  bad_swap_range w := by
    have := zr_topW_bounds htop
    simp only [zrIsBad371W, zrIsBad371, decide_eq_true_eq]
    dsimp only [zrSwap371W, zrSwap371]
    constructor <;> (intro h; split_ifs at h ⊢ <;> omega)
  range_swap_bad w := by
    have := zr_topW_bounds htop
    simp only [zrIsBad371W, zrIsBad371, decide_eq_true_eq]
    dsimp only [zrSwap371W, zrSwap371]
    constructor <;> (intro h; split_ifs at h ⊢ <;> omega)

/-- Maximal `Wire 411` bad-wire mask covering `[177..198) ∪ [233..254) ∪ {257}` across all
`topW`. -/
def zrBad411Max (w : Wire 411) : Bool :=
  decide ((177 ≤ w.val ∧ w.val < 198) ∨ (233 ≤ w.val ∧ w.val < 254) ∨ w.val = 257)

/-- Canonical `411`-prefix register inside `Wire 437`. -/
def zrBlk411 : QRegister 411 437 := QRegister.block 0 411 (by decide)

theorem zr_blk411_val (j : Wire 411) : (zrBlk411 j).val = j.val := Nat.zero_add j.val

theorem zr_not_bad411Max_of_not_true {w : Wire 411} (h : Bool.not (zrBad411Max w) = true)
    : ¬((177 ≤ w.val ∧ w.val < 198) ∨ (233 ≤ w.val ∧ w.val < 254) ∨ w.val = 257) :=
    of_decide_eq_false ((Bool.not_eq_true' (zrBad411Max w)).mp h)

private theorem zr_blk411_not_badXM {topW : ℕ}
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) {q : Wire 411}
    (hs : decide (q.val < 371) = true) (hd : Bool.not (zrBad411Max q) = true) :
    isBadXM 371 (zrIsBad371W topW) (zrBlk411 q) = false := by
  have hb := zr_topW_bounds htop
  have hq371 : q.val < 371 := of_decide_eq_true hs
  have hqd := zr_not_bad411Max_of_not_true hd
  simp only [isBadXM, zrIsBad371W, zrIsBad371, zr_blk411_val, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  omega

theorem zr_cliff_blk411_disjointBad {topW : ℕ}
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) :
    ∀ (c : CliffProg 411), cliffSupportsBelowB 371 c = true →
      cliffDisjointBad zrBad411Max c = true →
      cliffDisjointBad (isBadXM 371 (zrIsBad371W topW)) (c.onRegister zrBlk411) = true
  | .nil, _, _ => rfl
  | .x q, hs, hd => by
      simp [CliffProg.onRegister, cliffDisjointBad, zr_blk411_not_badXM htop hs hd]
  | .cnot c t _, hs, hd => by
      obtain ⟨hsc, hst⟩ := (Bool.and_eq_true _ _).mp hs
      obtain ⟨hdc, hdt⟩ := (Bool.and_eq_true _ _).mp hd
      simp [CliffProg.onRegister, cliffDisjointBad, zr_blk411_not_badXM htop hsc hdc,
        zr_blk411_not_badXM htop hst hdt]
  | .seq c₁ c₂, hs, hd => by
      obtain ⟨hs1, hs2⟩ := (Bool.and_eq_true _ _).mp hs
      obtain ⟨hd1, hd2⟩ := (Bool.and_eq_true _ _).mp hd
      exact (Bool.and_eq_true _ _).mpr ⟨zr_cliff_blk411_disjointBad htop c₁ hs1 hd1,
        zr_cliff_blk411_disjointBad htop c₂ hs2 hd2⟩

theorem zr_prog_blk411_disjointBad {topW : ℕ}
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) :
    ∀ (p : TempPhaseProg 411), progSupportsBelowB 371 p = true →
      progDisjointBad zrBad411Max p = true →
      progDisjointBad (isBadXM 371 (zrIsBad371W topW)) (p.onRegister zrBlk411) = true
  | .nil, _, _ => rfl
  | .cliff c, hs, hd => zr_cliff_blk411_disjointBad htop c hs hd
  | .z q, hs, hd => by
      simp [TempPhaseProg.onRegister, progDisjointBad, zr_blk411_not_badXM htop hs hd]
  | .seq p₁ p₂, hs, hd => by
      obtain ⟨hs1, hs2⟩ := (Bool.and_eq_true _ _).mp hs
      obtain ⟨hd1, hd2⟩ := (Bool.and_eq_true _ _).mp hd
      exact (Bool.and_eq_true _ _).mpr ⟨zr_prog_blk411_disjointBad htop p₁ hs1 hd1,
        zr_prog_blk411_disjointBad htop p₂ hs2 hd2⟩
  | .tempAnd c₁ c₂ anc _ _ _ body, hs, hd => by
      dsimp [progSupportsBelowB] at hs
      simp only [Bool.and_eq_true] at hs
      obtain ⟨hs1, hs2, hsa, hsb⟩ := hs
      dsimp [progDisjointBad] at hd
      simp only [Bool.and_eq_true] at hd
      obtain ⟨hd1, hd2, hda, hdb⟩ := hd
      simp [TempPhaseProg.onRegister, progDisjointBad, zr_blk411_not_badXM htop hs1 hd1,
        zr_blk411_not_badXM htop hs2 hd2, zr_blk411_not_badXM htop hsa hda,
        zr_prog_blk411_disjointBad htop body hsb hdb]

theorem zr_onRegister_blk411_eval (p : TempPhaseProg 411) (δ : BitAssignment 437)
    (hcl : cleanRem 437 (437 - 275) δ) :
    (p.onRegister zrBlk411).evalSign δ = p.evalSign (fun j : Wire 411 ↦ δ ⟨j.val, by omega⟩) ∧
    (p.onRegister zrBlk411).evalBits δ = n1sLiftEval411 p δ := by
  obtain ⟨hs, hin, hout⟩ := zr_prog_onRegister_eval zrBlk411 p δ
  have hfn : (fun i : Wire 411 ↦ δ (zrBlk411 i)) = fun j : Wire 411 ↦ δ ⟨j.val, by omega⟩ :=
    funext fun j ↦ congrArg δ (Fin.ext (zr_blk411_val j))
  refine ⟨hs.trans (congrArg p.evalSign hfn), funext fun w ↦ ?_⟩
  dsimp only [n1sLiftEval411]
  by_cases hw : w.val < 411
  · rw [dite_eq_left hw]
    have hw_eq : w = zrBlk411 ⟨w.val, hw⟩ := Fin.ext (zr_blk411_val ⟨w.val, hw⟩).symm
    conv_lhs => rw [hw_eq]
    exact (hin ⟨w.val, hw⟩).trans (by rw [hfn])
  · rw [dite_eq_right hw, hout w (fun j hj ↦ hw (by rw [hj, zr_blk411_val]; exact j.isLt))]
    exact hcl w (by omega)

theorem zr_stepBundleW_of_dyn411_lt371 {topW : ℕ}
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCombBase : QRegister 437 n)
    (p411 : TempPhaseProg 411)
    (d411 : QRegister 411 n → DynamicCircuit Var n)
    (hpSupp : progSupportsBelowB 371 p411 = true)
    (hpBad : progDisjointBad zrBad411Max p411 = true)
    (Inv411 : BitAssignment 411 → Prop)
    (hInv275 : ∀ β₁ β₂ : BitAssignment 411,
      (∀ w : Wire 411, w.val < 275 → β₁ w = β₂ w) → (Inv411 β₁ ↔ Inv411 β₂))
    (hPres : ∀ r : QRegister 411 n, PreservesStoreConst (d411 r))
    (hdSupp : ∀ (r : QRegister 411 n) (u : Wire 411), 371 ≤ u.val → r u ∉ (d411 r).support)
    (hReal411 : ∀ r : QRegister 411 n,
      RealizesCleanUnitary v (p57CleanDiagProj r (411 - 275) (by decide) Inv411)
        (d411 r) (((p411.onRegister r).toToffCircuit).eval))
    (δ_in δ_out : BitAssignment 149 → BitAssignment 437)
    (hIn : ∀ α, cleanRem 437 (437 - 275) (δ_in α) ∧
      (∀ w, zrIsBad371W topW w = true → δ_in α w = 0))
    (hOut : ∀ α, cleanRem 437 (437 - 275) (δ_out α) ∧
      (∀ w, zrIsBad371W topW w = true → δ_out α w = 0))
    (hOut_eq : ∀ α, δ_out α = n1sLiftEval411 p411 (δ_in α))
    (hSgn0 : ∀ α, p411.evalSign (fun j : Wire 411 ↦ δ_in α ⟨j.val, by omega⟩) = 0)
    (hInv_in : ∀ (β : BitAssignment 411) (α : BitAssignment 149),
      (∀ w : Wire 411, w.val < 275 → zrBad411Max w = false →
        β w = δ_in α ⟨w.val, by omega⟩) →
      Inv411 β) :
    let hsr := zr_validSwapRelayWM_371 htop
    let rCombX := rCombBase.compose (permReg (permOfInvol (zrSwap371W topW htop) hsr.invol))
    StepBundleW topW v rCombBase δ_in δ_out (fun _ ↦ 0)
      (d411 (rCombX.compose zrBlk411)) := by
  intro hsr rCombX
  let rComb411 : QRegister 411 n := rCombX.compose zrBlk411
  let p437 : TempPhaseProg 437 := p411.onRegister zrBlk411
  let Inv437 : BitAssignment 437 → Prop := fun γ ↦ Inv411 (fun j ↦ γ (zrBlk411 j))
  have hInv371 : ∀ u : Wire 411, 371 ≤ u.val → ∀ γ₁ γ₂ : BitAssignment 411,
      (∀ w : Wire 411, w ≠ u → γ₁ w = γ₂ w) → (Inv411 γ₁ ↔ Inv411 γ₂) :=
    fun u hu γ₁ γ₂ hne ↦ hInv275 γ₁ γ₂ (fun w hw ↦ hne w (wire_ne_of_lt (by omega)))
  have hp411_not : ∀ u : Wire 411, 371 ≤ u.val →
      rComb411 u ∉ ((p411.onRegister rComb411).toToffCircuit).support :=
    prog_not_mem_support_of_lt rComb411 371 p411 hpSupp
  have hRange411 : RealizesCleanUnitary v (p57RangeDiagProj rComb411 275 371 Inv411)
      (d411 rComb411) (((p411.onRegister rComb411).toToffCircuit).eval) :=
    realizesCleanUnitary_drop_tail v rComb411 275 371 (by decide) (by decide)
      Inv411 hInv371 (d411 rComb411) (hdSupp rComb411)
      ((p411.onRegister rComb411).toToffCircuit) hp411_not (hReal411 rComb411)
  have hProjEq : p57RangeDiagProj rComb411 275 371 Inv411 =
      p57RangeDiagProj rCombX 275 371 Inv437 := by
    apply matrix_ext_ket; intro β
    rw [p57RangeDiagProj, p57RangeDiagProj, ket_p57DiagProj, ket_p57DiagProj]
    have hiff : (∀ w : Wire 411, 275 ≤ w.val → w.val < 371 → β (rComb411 w) = 0) ↔
        (∀ w : Wire 437, 275 ≤ w.val → w.val < 371 → β (rCombX w) = 0) :=
      ⟨fun H w hw1 hw2 ↦ by
          have hw_eq : w = zrBlk411 ⟨w.val, by omega⟩ :=
            Fin.ext (zr_blk411_val ⟨w.val, by omega⟩).symm
          rw [hw_eq]; exact H ⟨w.val, by omega⟩ hw1 hw2,
       fun H w hw1 hw2 ↦ H (zrBlk411 w)
          (by rw [zr_blk411_val]; exact hw1) (by rw [zr_blk411_val]; exact hw2)⟩
    have hinv_eq : Inv411 (fun idx ↦ β (rComb411 idx)) ↔ Inv437 (fun idx ↦ β (rCombX idx)) :=
      Iff.rfl
    by_cases hR : (∀ w : Wire 437, 275 ≤ w.val → w.val < 371 → β (rCombX w) = 0) ∧
        Inv437 (fun idx ↦ β (rCombX idx))
    · rw [ite_eq_left hR, ite_eq_left ⟨hiff.mpr hR.1, hinv_eq.mpr hR.2⟩]
    · rw [ite_eq_right hR, ite_eq_right (fun hL ↦ hR ⟨hiff.mp hL.1, hinv_eq.mp hL.2⟩)]
  have hProgEq : p437.onRegister rCombX = p411.onRegister rComb411 :=
    zr_prog_onRegister_comp zrBlk411 rCombX p411
  rw [hProjEq, ← hProgEq] at hRange411
  refine stepBundleW_of_relayWM_dyn v rCombBase hsr δ_in δ_out (fun _ ↦ 0) p437
    (d411 rComb411) (hPres rComb411) Inv437 hRange411
    (zr_prog_blk411_disjointBad htop p411 hpSupp hpBad) hIn (fun α ↦ (hOut_eq α).trans
    ((zr_onRegister_blk411_eval p411 (δ_in α) (hIn α).1).2).symm) (fun α ↦
    ((zr_onRegister_blk411_eval p411 (δ_in α) (hIn α).1).1).trans (hSgn0 α)) hOut (fun γ α _
    hEq ↦ hInv_in (fun j ↦ γ (zrSwap371W topW htop (zrBlk411 j))) α (fun j hj275 hjBad ↦
    ?_))
  have hb := zr_topW_bounds htop
  have hnb : ¬((177 ≤ j.val ∧ j.val < 198) ∨ (233 ≤ j.val ∧ j.val < 254) ∨ j.val = 257) :=
    of_decide_eq_false hjBad
  have hxm : isBadXM 371 (zrIsBad371W topW) (zrBlk411 j) = false := by
    simp only [isBadXM, zrIsBad371W, zrIsBad371, zr_blk411_val, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    omega
  exact (hEq (zrBlk411 j) hxm).trans (congrArg (δ_in α) (Fin.ext (zr_blk411_val j)))

theorem zr_clearPreMK_clean_and_bad {topW : ℕ} (htop : topW = 328 ∨ topW = 339 ∨ topW = 342)
    {ξ : BitAssignment 437} (hcl : cleanRem 437 (437 - 275) ξ)
    (hz233 : ∀ w : Wire 437, 233 ≤ w.val → w.val < 258 → ξ w = 0) : cleanRem 437 (437 - 275)
    (clearPreMKOfTopW topW (putQZ ξ)) ∧ (∀ w : Wire 437, zrIsBad371W topW w = true →
    clearPreMKOfTopW topW (putQZ ξ) w = 0) := by
  have hcl_qz : cleanRem 437 (437 - 275) (putQZ ξ) := cleanRem_putQZ hcl
  refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · by_cases ht342 : topW = 342
    · subst ht342
      simp only [clearPreMKOfTopW, ↓reduceIte, clearPreMKCat]
      split_ifs <;> [rfl; exact hcl_qz w hw]
    · simp only [clearPreMKOfTopW, ht342, ↓reduceIte, clearPreMKCtrl]
      split_ifs <;> [rfl; exact hcl_qz w hw]
  · simp only [zrIsBad371W, zrIsBad371, decide_eq_true_eq] at hw
    rcases htop with rfl | rfl | rfl
    · simp only [clearPreMKOfTopW, show (328 = 342) = False by decide, ↓reduceIte, clearPreMKCtrl]
      rcases hw with h233 | h257 | h177
      · by_cases h251 : 251 ≤ w.val
        · exact ite_eq_left (Or.inr ⟨h251, h233.2⟩)
        · rw [ite_eq_right (by omega), putQZ_of_lt251 (by omega)]
          exact hz233 w h233.1 (by omega)
      · rw [ite_eq_right (by omega), putQZ_of_ge257 (by omega)]
        exact hz233 w (by omega) (by omega)
      · exact ite_eq_left (Or.inl ⟨h177.1, by omega⟩)
    · simp only [clearPreMKOfTopW, show (339 = 342) = False by decide, ↓reduceIte, clearPreMKCtrl]
      rcases hw with h233 | h257 | h177
      · by_cases h251 : 251 ≤ w.val
        · exact ite_eq_left (Or.inr ⟨h251, h233.2⟩)
        · rw [ite_eq_right (by omega), putQZ_of_lt251 (by omega)]
          exact hz233 w h233.1 (by omega)
      · rw [ite_eq_right (by omega), putQZ_of_ge257 (by omega)]
        exact hz233 w (by omega) (by omega)
      · exact ite_eq_left (Or.inl ⟨h177.1, by omega⟩)
    · simp only [clearPreMKOfTopW, ↓reduceIte, clearPreMKCat]
      rcases hw with h233 | h257 | h177
      · by_cases h251 : 251 ≤ w.val
        · exact ite_eq_left (Or.inr ⟨h251, h233.2⟩)
        · rw [ite_eq_right (by omega), putQZ_of_lt251 (by omega)]
          exact hz233 w h233.1 (by omega)
      · rw [ite_eq_right (by omega), putQZ_of_ge257 (by omega)]
        exact hz233 w (by omega) (by omega)
      · exact ite_eq_left (Or.inl ⟨h177.1, by omega⟩)

theorem zr_clearPreMK_putQZ_eq_of_not_bad (topW : ℕ) (ξ : BitAssignment 437) (w : Wire 437)
    (hnb : ¬((177 ≤ w.val ∧ w.val < 198) ∨ (233 ≤ w.val ∧ w.val < 258))) : clearPreMKOfTopW
    topW (putQZ ξ) w = ξ w := by
  have hc : clearPreMKOfTopW topW (putQZ ξ) w = putQZ ξ w := by
    by_cases ht342 : topW = 342
    · subst ht342
      simp only [clearPreMKOfTopW, ↓reduceIte, clearPreMKCat]
      exact ite_eq_right (by omega)
    · simp only [clearPreMKOfTopW, ht342, ↓reduceIte, clearPreMKCtrl]
      exact ite_eq_right (by omega)
  rw [hc]
  by_cases hlt : w.val < 251
  · exact putQZ_of_lt251 hlt
  · exact putQZ_of_ge257 (by omega)

theorem zr_revInv411_congr_258 (t : Norm1sTier) {β₁ β₂ : BitAssignment 411} (hg : ∀ w : Wire
    411, w.val < 275 → ¬((177 ≤ w.val ∧ w.val < 198) ∨ (233 ≤ w.val ∧ w.val < 258)) → β₁ w =
    β₂ w) : n1sRevInv411 t β₁ ↔ n1sRevInv411 t β₂ := by
  have hs : bitsVal (fun i : Fin 18 ↦ β₁ (n1sSTrue18W411 i)) =
      bitsVal (fun i : Fin 18 ↦ β₂ (n1sSTrue18W411 i)) :=
    congrArg bitsVal (funext fun i ↦ by
      have hr := n1s_sTrue18W411_range i
      exact hg _ (n1s_sTrue18W411_lt_275 i) (by rcases hr with r | r | r <;> omega))
  have hu : bitsVal (fun k : Fin 38 ↦ β₁ (n1sU38W411 k)) =
      bitsVal (fun k : Fin 38 ↦ β₂ (n1sU38W411 k)) :=
    congrArg bitsVal (funext fun k ↦ by
      have hr := n1s_u38W411_range k
      exact hg _ (by omega) (by omega))
  have hmu : bitsVal (fun i : Fin 3 ↦ β₁ (n1sMuW411 i)) =
      bitsVal (fun i : Fin 3 ↦ β₂ (n1sMuW411 i)) :=
    congrArg bitsVal (funext fun i ↦ hg _ (by dsimp [n1sMuW411]; omega) (by
      dsimp [n1sMuW411]; omega))
  have hout : bitsVal (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k)) =
      bitsVal (fun k : Fin 32 ↦ β₂ (n1sOut32W411 k)) :=
    congrArg bitsVal (funext fun k ↦ hg _ (by dsimp [n1sOut32W411]; omega) (by
      dsimp [n1sOut32W411]; omega))
  have hvs : β₁ n1sValidStaticW411 = β₂ n1sValidStaticW411 := hg _ (by decide) (by decide)
  have hacc : β₁ n1sAccFlagW411 = β₂ n1sAccFlagW411 := hg _ (by decide) (by decide)
  have hpr : ∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β₁ (n1sProjW411 w b)) =
      bitsVal (fun b : Fin 8 ↦ β₂ (n1sProjW411 w b)) :=
    fun w ↦ congrArg bitsVal (funext fun b ↦
      hg _ (by dsimp [n1sProjW411]; omega) (by dsimp [n1sProjW411]; omega))
  have htgt : n1sAccTarget411 t β₁ = n1sAccTarget411 t β₂ := by
    unfold n1sAccTarget411
    simp only [hs, hu, hmu, hvs, hpr]
  unfold n1sRevInv411
  simp only [hs, hu, hmu, hout, hvs, hacc, htgt]

theorem zr_plug_seq_411_gen (mutW : Wire 411 → Prop) [DecidablePred mutW] (K : TempCtx 411)
    (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx 292)
    (hLift : TempCtxLiftEx 275 292 K) (p₁ p₂ : TempPhaseProg 411)
    (hv₁ : ValidCleanRem 411 (411 - 292) p₁) (hv₂ : ValidCleanRem 411 (411 - 292) p₂) (hcl₁ :
    ∀ γ, cleanRem 411 (411 - 292) γ → cleanRem 411 (411 - 292) (p₁.evalBits γ)) (hnon₁ : ∀ γ,
    cleanRem 411 (411 - 292) γ → ∀ w, ¬ mutW w → p₁.evalBits γ w = γ w) (hnon₂ : ∀ γ, cleanRem
    411 (411 - 292) γ → ∀ w, ¬ mutW w → p₂.evalBits γ w = γ w) : ValidCleanRem 411 (411 - 275)
    (K.plug (.seq p₁ p₂)) ∧ (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β → (K.plug
    (.seq p₁ p₂)).evalSign β = p₁.evalSign (K.fwdBits β) + p₂.evalSign (p₁.evalBits (K.fwdBits
    β))) ∧ (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β → ∀ w : Wire 411, (K.plug
    (.seq p₁ p₂)).evalBits β w = if mutW w then p₂.evalBits (p₁.evalBits (K.fwdBits β)) w else
    β w) := by
  have hvIn : ValidCleanRem 411 (411 - 292) (.seq p₁ p₂) :=
    ⟨411 - 292, by decide, hv₁, hv₂, hcl₁⟩
  obtain ⟨hv, _, hsgn, hbits⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean
      (M := 411) (rem := 411 - 275) (curHole := 292)
      mutW K hDisj hSupp (by decide) K.fwdBits
      (TempCtxLiftEx.probe hLift) (.seq p₁ p₂) hvIn
      (fun γ hγ w hnw ↦ (hnon₂ (p₁.evalBits γ) (hcl₁ γ hγ) w hnw).trans (hnon₁ γ hγ w hnw))
  exact ⟨hv, fun β hβ ↦ hsgn β hβ, fun β hβ w ↦ hbits β hβ w⟩

theorem zr_clearPreMK_putQZ_congr_outside_n1s (topW : ℕ) {ξ₁ ξ₂ : BitAssignment 437} (hag :
    ∀ q : Wire 437, q.val ≠ 149 → ¬(201 ≤ q.val ∧ q.val < 233) → ξ₁ q = ξ₂ q) (w : Wire 437)
    (h149 : w.val ≠ 149) (h201 : ¬(201 ≤ w.val ∧ w.val < 233)) : clearPreMKOfTopW topW
    (putQZ ξ₁) w = clearPreMKOfTopW topW (putQZ ξ₂) w := by
  suffices hqz : ∀ q : Wire 437, q.val ≠ 149 → ¬(201 ≤ q.val ∧ q.val < 233) →
      putQZ ξ₁ q = putQZ ξ₂ q by
    by_cases ht342 : topW = 342
    · subst ht342
      simp only [clearPreMKOfTopW, ↓reduceIte, clearPreMKCat]
      split_ifs <;> [rfl; exact hqz w h149 h201]
    · simp only [clearPreMKOfTopW, ht342, ↓reduceIte, clearPreMKCtrl]
      split_ifs <;> [rfl; exact hqz w h149 h201]
  intro q hq149 hq201
  have hz_congr : ∀ u : Wire 437, u.val ≠ 149 → ¬(201 ≤ u.val ∧ u.val < 233) →
      putZ3 ξ₁ u = putZ3 ξ₂ u := fun u hu149 hu201 ↦ by
    dsimp only [putZ3]
    split_ifs with h254
    · exact zMagBit_congr_u22
        (fun i ↦ hag (u22WAux i) (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega)) _
    · exact hag u hu149 hu201
  have hmu_eq : ∀ i : Fin 3, putZ3 ξ₁ (muW i) = putZ3 ξ₂ (muW i) :=
    fun i ↦ hz_congr (muW i) (by dsimp [muW]; omega) (by dsimp [muW]; omega)
  dsimp only [putQZ, putQ3]
  split_ifs with h251
  · obtain ⟨hl, hr⟩ := quad3_congr_of_mu hmu_eq ⟨q.val - 251, by omega⟩
    exact congrArg₂ (· * ·) hl hr
  · exact hz_congr q hq149 hq201

/- ### Section 4B.5: E5-Wrapped Guard, `< 371` `411`-Wire Fwd/Rev Assemblies & `StepBundleW`s -/

/-- `0`-`TempAnd` in-place `e[0..4]` Clifford wrapper context on `[275..292)`. -/
def zrCtxE5_411 : TempCtx 411 := ctxCliffAlloc zrClzE5Cliff

/-- E5-wrapped `< 371` static guard program on `Wire 411`. -/
def zrPGuardE5_411 (t : Norm1sTier) : TempPhaseProg 411 :=
  zrCtxE5_411.plug (zrPGuard411 t)

/-- E5-wrapped `< 371` dynamic forward guard circuit (`4 * (15 + 21 + 3 + t.wAcc) + 4` `T`). -/
def zrDGuardE5Fwd411 (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb (zrDGuardFwd411 t v rComb) zrCtxE5_411

/-- E5-wrapped `< 371` dynamic reverse guard circuit (`4 * (15 + 21 + 3 + t.wAcc)` `T`). -/
def zrDGuardE5Rev411 (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb (zrDGuardRev411 t v rComb) zrCtxE5_411

theorem zr_cliffDisjoint_of_withinB {mutW : Wire 411 → Prop} {p : Wire 411 → Bool}
    (hp : ∀ w, p w = true → ¬ mutW w) :
    ∀ {c : CliffProg 411}, zrCliffWithinB p c = true → CliffDisjoint mutW c
  | .nil, _ => trivial
  | .x q, h => hp q h
  | .cnot c t _, h =>
      ⟨hp c (Bool.and_eq_true _ _ |>.mp h).1, hp t (Bool.and_eq_true _ _ |>.mp h).2⟩
  | .seq _ _, h =>
      ⟨zr_cliffDisjoint_of_withinB hp (Bool.and_eq_true _ _ |>.mp h).1,
       zr_cliffDisjoint_of_withinB hp (Bool.and_eq_true _ _ |>.mp h).2⟩

theorem zr_ctxE5_411_pkg : zrCtxE5_411.countTempAnd = 0 ∧ zrCtxE5_411.DisjointFrom
    (fun q : Wire 411 ↦ q = n1sAccFlagW411) ∧ zrCtxE5_411.SupportsBelowCtx 292 ∧
    TempCtxLiftEx 292 292 zrCtxE5_411 ∧ ctxSupportsBelowB 371 zrCtxE5_411 = true :=
  ⟨by decide,
    ctxCliffAlloc_disjoint (zr_cliffDisjoint_of_withinB
      (fun _ hw h ↦ by
        subst h
        rw [(by decide : zrE5PredB n1sAccFlagW411 = false)] at hw
        exact Bool.noConfusion hw)
      zr_clzE5Cliff_withinB),
    ctxCliffAlloc_supports zr_clzE5Cliff_supportsBelow,
    TempCtxLiftEx.cliff 292 (by decide) zrClzE5Cliff zr_clzE5Cliff_supportsBelow,
    by decide⟩

theorem zr_pGuardE5_411_spec (t : Norm1sTier) : progSupportsBelowB 371 (zrPGuardE5_411 t)
    = true ∧ ValidCleanRem 411 (411 - 292) (zrPGuardE5_411 t) ∧
    (zrPGuardE5_411 t).countTempAnd = (15 + 21 + 3 + t.wAcc) + 1 ∧ (∀ γ : BitAssignment 411,
    cleanRem 411 (411 - 292) γ → (zrPGuardE5_411 t).evalSign γ = 0 ∧ cleanRem 411 (411 -
    292) ((zrPGuardE5_411 t).evalBits γ) ∧ (∀ q : Wire 411, q ≠ n1sAccFlagW411 →
    (zrPGuardE5_411 t).evalBits γ q = γ q) ∧ (zrPGuardE5_411 t).evalBits γ n1sAccFlagW411
    = γ n1sAccFlagW411 + zrGuardBit t (zrClzE5Cliff.eval γ)) := by
  dsimp only [zrPGuardE5_411]
  obtain ⟨hcE, hdE, hsE, hlE, hsbE⟩ := zr_ctxE5_411_pkg
  obtain ⟨hvG, hcG, hEvG⟩ := zr_pGuard411_spec t
  obtain ⟨hv, hcnt, hsgn, hbits⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean
      (M := 411) (rem := 411 - 292) (curHole := 292)
      (fun q : Wire 411 ↦ q = n1sAccFlagW411)
      zrCtxE5_411 hdE hsE (by decide)
      zrCtxE5_411.fwdBits (TempCtxLiftEx.probe hlE)
      (zrPGuard411 t) hvG
      (fun δ hδ w hnw ↦ (hEvG δ hδ).2.2.1 w hnw)
  refine ⟨zr_plug_supportsBelowB (zr_pGuard411_supportsBelowB t) zrCtxE5_411 hsbE,
    hv, by rw [hcnt, hcE, zero_add, hcG], fun γ hγ ↦ ?_⟩
  have hfwd : zrCtxE5_411.fwdBits γ = zrClzE5Cliff.eval γ :=
    ctxCliffAlloc_fwdBits 292 (by decide) zrClzE5Cliff zr_clzE5Cliff_supportsBelow γ hγ
  have hclE : cleanRem 411 (411 - 292) (zrCtxE5_411.fwdBits γ) := by
    rw [hfwd]; exact zr_clzE5Cliff_cleanRem γ hγ
  obtain ⟨hsG, _, _, hvalG⟩ := hEvG (zrCtxE5_411.fwdBits γ) hclE
  have hnon : ∀ q : Wire 411, q ≠ n1sAccFlagW411 →
      (zrCtxE5_411.plug (zrPGuard411 t)).evalBits γ q = γ q :=
    fun q hq ↦ (hbits γ hγ q).trans (ite_eq_right hq)
  have haccE : (zrCtxE5_411.fwdBits γ) n1sAccFlagW411 = γ n1sAccFlagW411 := by
    rw [hfwd]
    exact zr_clzE5Cliff_eval_outside γ n1sAccFlagW411
      (fun b ↦ wire_ne_of_lt (by have := (zrEW411_bounds b).1; dsimp [n1sAccFlagW411]; omega))
  refine ⟨(hsgn γ hγ).trans hsG,
    fun w hw ↦ (hnon w (wire_ne_of_gt (by dsimp [n1sAccFlagW411]; omega))).trans (hγ w hw),
    hnon, ?_⟩
  rw [hbits γ hγ n1sAccFlagW411, ite_eq_left rfl, hvalG, haccE, hfwd]

theorem zr_dGuardE5Fwd411_props (t : Norm1sTier) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (zrDGuardE5Fwd411 t v rComb).count PrimitiveGate.T = 4 * (15 + 21 + 3 + t.wAcc) + 4 ∧
    (zrDGuardE5Fwd411 t v rComb).count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (zrDGuardE5Fwd411 t v rComb) ∧ (∀ u : Wire 411, 371 ≤ u.val → rComb u ∉
    (zrDGuardE5Fwd411 t v rComb).support) ∧ RealizesCleanUnitary v
    (p57CleanDiagProj rComb (411 - 292) (by decide) (fun _ ↦ True))
    (zrDGuardE5Fwd411 t v rComb)
    ((((zrPGuardE5_411 t).onRegister rComb).toToffCircuit).eval) := by
  dsimp only [zrDGuardE5Fwd411, zrPGuardE5_411]
  obtain ⟨hcE, _, hsE, _, hsbE⟩ := zr_ctxE5_411_pkg
  obtain ⟨hcT, hcToff, hPres, hReal⟩ := zr_dGuardFwd411_props t v rComb
  exact ⟨by rw [p57ToDynWith_count_t, hcE, mul_zero, zero_add, hcT],
    p57ToDynWith_count_toff v rComb _ hcToff _,
    p57ToDynWith_preservesStore v rComb _ hPres _,
    fun u hu ↦ p57ToDynWith_not_mem_support_of_lt v rComb 371 _
      (zr_dGuardFwd411_not_mem_support t v rComb) zrCtxE5_411 hsbE u hu,
    n1s_toDynWith_realizes_supp v rComb _ _ (fun _ ↦ True) 292 (by decide) hReal
      zrCtxE5_411 hsE (411 - 292) (by decide) (by decide) (fun _ ↦ True)
      (zr_pGuardE5_411_spec t).2.1 (fun _ _ _ ↦ trivial)⟩

theorem zr_dGuardE5Rev411_props (t : Norm1sTier) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (zrDGuardE5Rev411 t v rComb).count PrimitiveGate.T = 4 * (15 + 21 + 3 + t.wAcc) ∧
    (zrDGuardE5Rev411 t v rComb).count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (zrDGuardE5Rev411 t v rComb) ∧ (∀ u : Wire 411, 371 ≤ u.val → rComb u ∉
    (zrDGuardE5Rev411 t v rComb).support) ∧ RealizesCleanUnitary v (p57CleanDiagProj rComb
    (411 - 292) (by decide) (fun β₁ ↦ β₁ n1sAccFlagW411 = zrGuardBit t (zrClzE5Cliff.eval
    β₁))) (zrDGuardE5Rev411 t v rComb)
    ((((zrPGuardE5_411 t).onRegister rComb).toToffCircuit).eval) := by
  dsimp only [zrDGuardE5Rev411, zrPGuardE5_411]
  obtain ⟨hcE, _, hsE, _, hsbE⟩ := zr_ctxE5_411_pkg
  obtain ⟨hcT, hcToff, hPres, hReal⟩ := zr_dGuardRev411_props t v rComb
  refine ⟨by rw [p57ToDynWith_count_t, hcE, mul_zero, zero_add, hcT],
    p57ToDynWith_count_toff v rComb _ hcToff _,
    p57ToDynWith_preservesStore v rComb _ hPres _,
    fun u hu ↦ p57ToDynWith_not_mem_support_of_lt v rComb 371 _
      (zr_dGuardRev411_not_mem_support t v rComb) zrCtxE5_411 hsbE u hu,
    n1s_toDynWith_realizes_supp v rComb _ _ _ 292 (by decide) hReal
      zrCtxE5_411 hsE (411 - 292) (by decide) (by decide) _
      (zr_pGuardE5_411_spec t).2.1 (fun β₁ hβ₁ hi ↦ ?_)⟩
  have hfwd : zrCtxE5_411.fwdBits β₁ = zrClzE5Cliff.eval β₁ :=
    ctxCliffAlloc_fwdBits 292 (by decide) zrClzE5Cliff zr_clzE5Cliff_supportsBelow β₁ hβ₁
  rw [hfwd]
  exact (zr_clzE5Cliff_eval_outside β₁ n1sAccFlagW411
    (fun b ↦ wire_ne_of_lt (by have := (zrEW411_bounds b).1; dsimp [n1sAccFlagW411]; omega))).trans
      hi

/-- Full `< 371` Stage-2 static forward `Norm1s` program on `Wire 411`. -/
def zrFwdStatic411 (t : Norm1sTier) : TempPhaseProg 411 :=
  zrCtxClz411.plug (.seq (zrPBarFwd411 t) (zrPGuardE5_411 t))

def zrRevStatic411 (t : Norm1sTier) : TempPhaseProg 411 :=
  zrCtxClz411.plug (.seq (zrPGuardE5_411 t) (zrPBarRev411 t))

set_option maxRecDepth 16384 in
theorem zr_ctxClz411_supportsBelowB371 : ctxSupportsBelowB 371 zrCtxClz411 = true := by
  decide

theorem zr_fwdStatic411_spec (t : Norm1sTier) : ValidCleanRem 411 (411 - 275)
    (zrFwdStatic411 t) ∧ (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β →
    (zrFwdStatic411 t).evalSign β = 0 ∧ cleanRem 411 (411 - 275) ((zrFwdStatic411
    t).evalBits β) ∧ (∀ q : Wire 411, q ≠ n1sAccFlagW411 → (∀ k : Fin 32, q ≠ n1sOut32W411 k)
    → (zrFwdStatic411 t).evalBits β q = β q) ∧ ((∀ k : Fin 32, β (n1sOut32W411 k) = 0) → β
    n1sAccFlagW411 = 0 → (β n1sValidStaticW411 = 1 → bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i))
    < 7 ∧ 2 * bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) ≤ clz18Log2 (bitsVal (fun i : Fin 18 ↦
    β (n1sSTrue18W411 i)))) → bitsVal (fun k : Fin 32 ↦ (zrFwdStatic411 t).evalBits β
    (n1sOut32W411 k)) = norm1sHwProd t.kBits t.dCut (norm1sMant18 (bitsVal (fun i : Fin 18 ↦ β
    (n1sSTrue18W411 i)))) (bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits)) ∧
    (zrFwdStatic411 t).evalBits β n1sAccFlagW411 = n1sAccTarget411 t β)) := by
  dsimp only [zrFwdStatic411]
  obtain ⟨_, hdC, hsC, hlC⟩ := zr_ctxClz411_pkg
  obtain ⟨_, hvB, _, hEvB⟩ := zr_pBarFwd411_spec t
  obtain ⟨_, hvG, _, hEvG⟩ := zr_pGuardE5_411_spec t
  obtain ⟨hv, hsgn, hbits⟩ := zr_plug_seq_411_gen
      (fun q ↦ q = n1sAccFlagW411 ∨ ∃ k : Fin 32, q = n1sOut32W411 k) zrCtxClz411 hdC hsC
      hlC (zrPBarFwd411 t) (zrPGuardE5_411 t) hvB hvG (fun γ hγ ↦ (hEvB γ hγ).2.1) (fun γ
      hγ w hnw ↦ (hEvB γ hγ).2.2.1 w (fun k hk ↦ hnw (Or.inr ⟨k, hk⟩)))
      (fun γ hγ w hnw ↦ (hEvG γ hγ).2.2.1 w (fun h ↦ hnw (Or.inl h)))
  refine ⟨hv, fun β hβ ↦ ?_⟩
  obtain ⟨hcl₁, hpres₁, _, hpres₂, hmVal⟩ := zr_ctxClz_and_barrel_fwd β hβ
  let β₁ := zrCtxClz411.fwdBits β
  obtain ⟨hsB, hcl_mid, hnonB, hvalB⟩ := hEvB β₁ hcl₁
  let β_mid := (zrPBarFwd411 t).evalBits β₁
  obtain ⟨hsG, _, hnonG, hvalG⟩ := hEvG β_mid hcl_mid
  have hnon : ∀ q : Wire 411, q ≠ n1sAccFlagW411 → (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (zrCtxClz411.plug (.seq (zrPBarFwd411 t) (zrPGuardE5_411 t))).evalBits β q = β q :=
    fun q h1 h2 ↦ (hbits β hβ q).trans (n1s_if_neg (fun h ↦ h.elim h1 (fun ⟨k, hk⟩ ↦ h2 k hk)))
  refine ⟨(hsgn β hβ).trans ((congrArg₂ (· + ·) hsB hsG).trans (add_zero (0 : ZMod 2))),
    fun w hw ↦ (hnon w (wire_ne_of_gt (by dsimp [n1sAccFlagW411]; omega))
      (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))).trans (hβ w hw),
    hnon, fun hout0 hacc0 hvalid ↦ ?_⟩
  have hout0_1 : ∀ k : Fin 32, β₁ (n1sOut32W411 k) = 0 :=
    fun k ↦ (hpres₁ _ (by dsimp [n1sOut32W411]; omega)).trans (hout0 k)
  have huK_eq : bitsVal (fun m : Fin t.kBits ↦ (zrCtxBarrel411.fwdBits β₁) (n1sUKW411 t m)) =
      bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits) := by
    have hfn : (fun m : Fin t.kBits ↦ (zrCtxBarrel411.fwdBits β₁) (n1sUKW411 t m)) =
        fun m ↦ β (n1sUKW411 t m) := funext fun m ↦ by
      have hr := (n1s_uKW411_range t m).2
      exact (hpres₂ _ (by omega)).trans (hpres₁ _ (by omega))
    exact (congrArg bitsVal hfn).trans (by rw [n1s_uKW411_bitsVal])
  have hout_mid : bitsVal (fun k : Fin 32 ↦ β_mid (n1sOut32W411 k)) = norm1sHwProd t.kBits
      t.dCut (norm1sMant18 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))))
      (bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits)) :=
      (hvalB hout0_1).trans (congrArg₂ (norm1sHwProd t.kBits t.dCut) hmVal huK_eq)
  have hout_final : bitsVal (fun k : Fin 32 ↦ (zrCtxClz411.plug (.seq (zrPBarFwd411 t)
      (zrPGuardE5_411 t))).evalBits β (n1sOut32W411 k)) = bitsVal
      (fun k : Fin 32 ↦ β_mid (n1sOut32W411 k)) :=
    congrArg bitsVal (funext fun k ↦
      (hbits β hβ (n1sOut32W411 k)).trans
        ((n1s_if_pos (Or.inr ⟨k, rfl⟩)).trans
          (hnonG (n1sOut32W411 k) (wire_ne_of_gt (by
            dsimp [n1sOut32W411, n1sAccFlagW411]; omega)))))
  have hacc_mid : β_mid n1sAccFlagW411 = 0 :=
    (hnonB n1sAccFlagW411
      (fun k ↦ wire_ne_of_lt (by dsimp [n1sAccFlagW411, n1sOut32W411]; omega))).trans
      ((hpres₁ n1sAccFlagW411 (by decide)).trans hacc0)
  have he5 : ∀ b : Fin 5,
      (zrClzE5Cliff.eval β_mid) (zrEW411 b) =
        (zrClzE5Cliff.eval β₁) (zrEW411 b) := fun b ↦
    zr_cliff_eval_congr zr_clzE5Cliff_withinB
      (fun w hw ↦ hnonB w fun k hk ↦ by
        subst hk
        have hf : zrE5PredB (n1sOut32W411 k) = false := by fin_cases k <;> decide
        rw [hf] at hw
        exact Bool.noConfusion hw)
      (zrEW411 b) (by fin_cases b <;> decide)
  have hout_e5 : bitsVal (fun k : Fin 32 ↦ (zrClzE5Cliff.eval β_mid) (n1sOut32W411 k)) =
      bitsVal (fun k : Fin 32 ↦ β_mid (n1sOut32W411 k)) :=
    congrArg bitsVal (funext fun k ↦ zr_clzE5Cliff_eval_outside β_mid (n1sOut32W411 k)
      (fun b ↦ wire_ne_of_lt (by have := (zrEW411_bounds b).1; dsimp [n1sOut32W411]; omega)))
  have hgb_eq : zrGuardBit t (zrClzE5Cliff.eval β_mid) = n1sAccTarget411 t β :=
    zr_guardBit_eq_target_of_clzE5 t β (zrClzE5Cliff.eval β_mid) hβ
      (zr_clzE5Cliff_cleanRem β_mid hcl_mid)
      (fun w hw _ h2 ↦ (zr_clzE5Cliff_eval_outside β_mid w
        (fun b ↦ wire_ne_of_lt (by have := (zrEW411_bounds b).1; omega))).trans
        ((hnonB w h2).trans (hpres₁ w hw)))
      he5 (hout_e5.trans hout_mid) hvalid
  have hacc_final : (zrCtxClz411.plug (.seq (zrPBarFwd411 t) (zrPGuardE5_411
      t))).evalBits β n1sAccFlagW411 = n1sAccTarget411 t β := by
    rw [hbits β hβ n1sAccFlagW411, n1s_if_pos (Or.inl rfl), hvalG, hacc_mid, zero_add]
    exact hgb_eq
  exact ⟨hout_final.trans hout_mid, hacc_final⟩

theorem zr_revHole_invs (t : Norm1sTier) (β : BitAssignment 411)
    (hβ : cleanRem 411 (411 - 275) β)
    (hInv : n1sRevInv411 t β) :
    let β₁ := zrCtxClz411.fwdBits β
    let β₁' := (zrPGuardE5_411 t).evalBits β₁
    β₁ n1sAccFlagW411 = zrGuardBit t (zrClzE5Cliff.eval β₁) ∧
    β₁' n1sAccFlagW411 = 0 ∧
    cleanRem 411 (411 - 292) β₁' ∧
    zrBoothDoneInv t (zrCtxBarrel411.fwdBits β₁') := by
  intro β₁ β₁'
  obtain ⟨hOut, hValid, hAcc⟩ := hInv
  obtain ⟨hcl₁, hpres₁, _, _, _⟩ := zr_ctxClz_and_barrel_fwd β hβ
  obtain ⟨_, _, _, hEvG⟩ := zr_pGuardE5_411_spec t
  obtain ⟨_, hcl₁', hnonG, hvalG⟩ := hEvG β₁ hcl₁
  let γE := zrClzE5Cliff.eval β₁
  have hclE : cleanRem 411 (411 - 292) γE := zr_clzE5Cliff_cleanRem β₁ hcl₁
  have hout_e5 : bitsVal (fun k : Fin 32 ↦ γE (n1sOut32W411 k)) =
      bitsVal (fun k : Fin 32 ↦ β (n1sOut32W411 k)) :=
    congrArg bitsVal (funext fun k ↦
      (zr_clzE5Cliff_eval_outside β₁ (n1sOut32W411 k)
        (fun b ↦ wire_ne_of_lt (by
          have := (zrEW411_bounds b).1; dsimp [n1sOut32W411]; omega))).trans
        (hpres₁ (n1sOut32W411 k) (by dsimp [n1sOut32W411]; omega)))
  have hgb : zrGuardBit t γE = n1sAccTarget411 t β :=
    zr_guardBit_eq_target_of_clzE5 t β γE hβ hclE
      (fun w hw _ _ ↦ (zr_clzE5Cliff_eval_outside β₁ w
        (fun b ↦ wire_ne_of_lt (by have := (zrEW411_bounds b).1; omega))).trans (hpres₁ w hw))
      (fun _ ↦ rfl) (hout_e5.trans hOut) hValid
  have hHole1 : β₁ n1sAccFlagW411 = zrGuardBit t γE :=
    (hpres₁ n1sAccFlagW411 (by decide)).trans (hAcc.trans hgb.symm)
  have hAcc0 : β₁' n1sAccFlagW411 = 0 :=
    hvalG.trans ((congrArg (· + zrGuardBit t γE) hHole1).trans (CharTwo.add_self_eq_zero _))
  let β0 : BitAssignment 411 := Function.update β n1sAccFlagW411 0
  have hcl_β0 : cleanRem 411 (411 - 275) β0 := fun w hw ↦ by
    dsimp [β0]
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [n1sAccFlagW411]; omega))]
    exact hβ w hw
  have hs_eq : bitsVal (fun i : Fin 18 ↦ β0 (n1sSTrue18W411 i)) =
      bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)) :=
    congrArg bitsVal (funext fun i ↦ by
      dsimp [β0]
      refine Function.update_of_ne (fun h ↦ ?_) _ _
      have hr := n1s_sTrue18W411_range i
      have hv := congrArg Fin.val h; dsimp [n1sAccFlagW411] at hv
      rcases hr with r | r | r <;> omega)
  have hβ₁'_eq : β₁' = zrCtxClz411.fwdBits β0 := by
    obtain ⟨_, _, _, hClzEv⟩ := zr_ctxClz411_scoped
    obtain ⟨hcl_a, _, hout_a⟩ := hClzEv β hβ
    obtain ⟨hcl_b, hp_b, hout_b⟩ := hClzEv β0 hcl_β0
    have hp0 := hp_b (n1s_allBelow_of_noMutBelow 18 17
      (bitsVal (fun i ↦ β0 (n1sSTrue18W411 i))) clz17Ops clz17Ops_meta.2.1 zr_clz17Ops_noMut)
    have hβ0_acc : β0 n1sAccFlagW411 = 0 := by simp [β0]
    funext w
    by_cases hw1 : w = n1sAccFlagW411
    · subst hw1
      exact hAcc0.trans (hβ0_acc.symm.trans (hp0 n1sAccFlagW411 (by decide)).symm)
    · refine (hnonG w hw1).trans ?_
      by_cases hw275 : w.val < 275
      · exact (hpres₁ w hw275).trans
          (((Function.update_of_ne hw1 _ _).symm).trans (hp0 w hw275).symm)
      · by_cases hw292 : w.val < 292
        · have hw_idx : w = ⟨275 + ((18 + (w.val - 275)) - 18), by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hw_idx]
          exact (hout_a (18 + (w.val - 275)) (by omega) (by omega)).trans ((congrArg (fun m ↦
            boolToZMod2 (getBoolAt (evalMicroList 18 clz17Ops (initBoolList 18 (18 + 17) m))
            (18 + (w.val - 275)))) hs_eq.symm).trans (hout_b (18 + (w.val - 275)) (by omega)
            (by omega)).symm)
        · exact (hcl_a w (by omega)).trans (hcl_b w (by omega)).symm
  obtain ⟨_, hpres₁_0, _, hpres₂_0, hmVal_0⟩ := zr_ctxClz_and_barrel_fwd β0 hcl_β0
  refine ⟨hHole1, hAcc0, hcl₁', ?_⟩
  suffices hDone0 : zrBoothDoneInv t (zrCtxBarrel411.fwdBits (zrCtxClz411.fwdBits β0)) from
    hβ₁'_eq.symm ▸ hDone0
  unfold zrBoothDoneInv
  have hout_b2 : bitsVal (fun j : Fin 32 ↦ (zrCtxBarrel411.fwdBits (zrCtxClz411.fwdBits
      β0)) (n1sOut32W411 j)) = bitsVal (fun j : Fin 32 ↦ β (n1sOut32W411 j)) :=
    congrArg bitsVal (funext fun j ↦
      (hpres₂_0 _ (by dsimp [n1sOut32W411]; omega)).trans
        ((hpres₁_0 _ (by dsimp [n1sOut32W411]; omega)).trans
          (Function.update_of_ne
            (wire_ne_of_gt (by dsimp [n1sOut32W411, n1sAccFlagW411]; omega)) _ _)))
  have huK_b2 : bitsVal (fun k : Fin t.kBits ↦ (zrCtxBarrel411.fwdBits
      (zrCtxClz411.fwdBits β0)) (n1sUKW411 t k)) = bitsVal
      (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits) := by
    have hfn :
        (fun k : Fin t.kBits ↦
          (zrCtxBarrel411.fwdBits (zrCtxClz411.fwdBits β0)) (n1sUKW411 t k)) =
        fun k ↦ β (n1sUKW411 t k) := funext fun k ↦ by
      have hr := (n1s_uKW411_range t k).2
      exact (hpres₂_0 _ (by omega)).trans ((hpres₁_0 _ (by omega)).trans
        (Function.update_of_ne (wire_ne_of_lt (by dsimp [n1sAccFlagW411]; omega)) _ _))
    exact (congrArg bitsVal hfn).trans (by rw [n1s_uKW411_bitsVal])
  exact hout_b2.trans (hOut.trans (congrArg₂ (norm1sHwProd t.kBits t.dCut) (hmVal_0.trans
    (congrArg norm1sMant18 hs_eq)) huK_b2).symm)

theorem zr_revStatic411_spec (t : Norm1sTier) : ValidCleanRem 411 (411 - 275)
    (zrRevStatic411 t) ∧ (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β →
    (zrRevStatic411 t).evalSign β = 0 ∧ cleanRem 411 (411 - 275) ((zrRevStatic411
    t).evalBits β) ∧ (∀ q : Wire 411, q ≠ n1sAccFlagW411 → (∀ k : Fin 32, q ≠ n1sOut32W411 k)
    → (zrRevStatic411 t).evalBits β q = β q) ∧ (n1sRevInv411 t β → (zrRevStatic411
    t).evalBits β n1sAccFlagW411 = 0 ∧ ∀ k : Fin 32, (zrRevStatic411 t).evalBits β
    (n1sOut32W411 k) = 0)) := by
  dsimp only [zrRevStatic411]
  obtain ⟨_, hdC, hsC, hlC⟩ := zr_ctxClz411_pkg
  obtain ⟨_, hvG, _, hEvG⟩ := zr_pGuardE5_411_spec t
  obtain ⟨_, hvB, hEvB⟩ := zr_pBarRev411_spec t
  obtain ⟨hv, hsgn, hbits⟩ := zr_plug_seq_411_gen
      (fun q ↦ q = n1sAccFlagW411 ∨ ∃ k : Fin 32, q = n1sOut32W411 k) zrCtxClz411 hdC hsC
      hlC (zrPGuardE5_411 t) (zrPBarRev411 t) hvG hvB (fun γ hγ ↦ (hEvG γ hγ).2.1)
      (fun γ hγ w hnw ↦ (hEvG γ hγ).2.2.1 w (fun h ↦ hnw (Or.inl h))) (fun γ hγ w hnw ↦ (hEvB
      γ hγ).2.2.1 w (fun k hk ↦ hnw (Or.inr ⟨k, hk⟩)))
  refine ⟨hv, fun β hβ ↦ ?_⟩
  obtain ⟨hcl₁, _, _, _, _⟩ := zr_ctxClz_and_barrel_fwd β hβ
  let β₁ := zrCtxClz411.fwdBits β
  obtain ⟨hsG, hcl₁', _, _⟩ := hEvG β₁ hcl₁
  obtain ⟨hsB, _, hnonB, hzeroB⟩ := hEvB ((zrPGuardE5_411 t).evalBits β₁) hcl₁'
  have hnon : ∀ q : Wire 411, q ≠ n1sAccFlagW411 → (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (zrCtxClz411.plug (.seq (zrPGuardE5_411 t) (zrPBarRev411 t))).evalBits β q = β q :=
    fun q h1 h2 ↦ (hbits β hβ q).trans (n1s_if_neg (fun h ↦ h.elim h1 (fun ⟨k, hk⟩ ↦ h2 k hk)))
  refine ⟨(hsgn β hβ).trans ((congrArg₂ (· + ·) hsG hsB).trans (add_zero (0 : ZMod 2))),
    fun w hw ↦ (hnon w (wire_ne_of_gt (by dsimp [n1sAccFlagW411]; omega))
      (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))).trans (hβ w hw),
    hnon, fun hInv ↦ ?_⟩
  obtain ⟨_, hAcc0, _, hDone⟩ := zr_revHole_invs t β hβ hInv
  exact ⟨(hbits β hβ n1sAccFlagW411).trans ((n1s_if_pos (Or.inl rfl)).trans
      ((hnonB n1sAccFlagW411
        (fun k ↦ wire_ne_of_lt (by dsimp [n1sAccFlagW411, n1sOut32W411]; omega))).trans hAcc0)),
    fun k ↦ (hbits β hβ (n1sOut32W411 k)).trans ((n1s_if_pos (Or.inr ⟨k, rfl⟩)).trans (hzeroB hDone
      k))⟩

set_option maxRecDepth 16384 in
theorem zr_ctx_disjointBad : ctxDisjointBad zrBad411Max zrCtxClz411 = true ∧
    ctxDisjointBad zrBad411Max zrCtxBarrel411 = true ∧ ctxDisjointBad zrBad411Max
    zrCtxE5_411 = true :=
  ⟨by decide, by decide, by decide⟩

set_option maxHeartbeats 800000 in
-- Disjointness decision across Norm1sTier cases
set_option maxRecDepth 16384 in
theorem zr_inner_disjointBad (t : Norm1sTier) : progDisjointBad zrBad411Max
    (zrPGuard411 t) = true ∧ progDisjointBad zrBad411Max (zrBoothFwd411 t) = true ∧
    progDisjointBad zrBad411Max (zrBoothRevStatic411 t) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> (cases t <;> decide)

theorem zr_fwdRev_checks (t : Norm1sTier) : progSupportsBelowB 371 (zrFwdStatic411 t) =
    true ∧ progDisjointBad zrBad411Max (zrFwdStatic411 t) = true ∧ progSupportsBelowB 371
    (zrRevStatic411 t) = true ∧ progDisjointBad zrBad411Max (zrRevStatic411 t) = true
    := by
  obtain ⟨hcC, hcB, hcE⟩ := zr_ctx_disjointBad
  obtain ⟨hiG, hiBF, hiBR⟩ := zr_inner_disjointBad t
  have hdGE : progDisjointBad zrBad411Max (zrPGuardE5_411 t) = true := by
    dsimp only [zrPGuardE5_411]; rw [progDisjointBad_plug, hcE, hiG]; rfl
  have hdBF : progDisjointBad zrBad411Max (zrPBarFwd411 t) = true := by
    dsimp only [zrPBarFwd411]; rw [progDisjointBad_plug, hcB, hiBF]; rfl
  have hdBR : progDisjointBad zrBad411Max (zrPBarRev411 t) = true := by
    dsimp only [zrPBarRev411]; rw [progDisjointBad_plug, hcB, hiBR]; rfl
  have hsFwdIn : progSupportsBelowB 371 (.seq (zrPBarFwd411 t) (zrPGuardE5_411 t)) = true
      := (Bool.and_eq_true (progSupportsBelowB 371 (zrPBarFwd411 t)) (progSupportsBelowB 371
      (zrPGuardE5_411 t))).mpr ⟨(zr_pBarFwd411_spec t).1, (zr_pGuardE5_411_spec t).1⟩
  have hsRevIn : progSupportsBelowB 371 (.seq (zrPGuardE5_411 t) (zrPBarRev411 t)) = true
      := (Bool.and_eq_true (progSupportsBelowB 371 (zrPGuardE5_411 t)) (progSupportsBelowB
      371 (zrPBarRev411 t))).mpr ⟨(zr_pGuardE5_411_spec t).1, (zr_pBarRev411_spec t).1⟩
  dsimp only [zrFwdStatic411, zrRevStatic411]
  refine ⟨zr_plug_supportsBelowB hsFwdIn zrCtxClz411 zr_ctxClz411_supportsBelowB371, ?_,
    zr_plug_supportsBelowB hsRevIn zrCtxClz411 zr_ctxClz411_supportsBelowB371, ?_⟩
  · rw [progDisjointBad_plug, hcC]
    exact (Bool.and_eq_true _ _).mpr ⟨rfl, (Bool.and_eq_true _ _).mpr ⟨hdBF, hdGE⟩⟩
  · rw [progDisjointBad_plug, hcC]
    exact (Bool.and_eq_true _ _).mpr ⟨rfl, (Bool.and_eq_true _ _).mpr ⟨hdGE, hdBR⟩⟩

theorem zr_liftEval_fwd_eq_st2 (t : Norm1sTier) {topW : ℕ}
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) (α : BitAssignment 149) :
    clearPreMKOfTopW topW (putQZ (n1sSt2 t α)) =
      n1sLiftEval411 (zrFwdStatic411 t) (clearPreMKOfTopW topW (st1QZ α)) := by
  let δ_in := clearPreMKOfTopW topW (st1QZ α)
  let β_in : BitAssignment 411 := fun j ↦ δ_in ⟨j.val, by omega⟩
  let β₁ : BitAssignment 411 := n1sSt1_411 α
  obtain ⟨hInv1, _, hAcc1, hOut1⟩ := n1s_st1_props α
  obtain ⟨_, _, hnon2, hout2, hacc2, _⟩ := n1s_st2_props t α
  have hcl_in : cleanRem 437 (437 - 275) δ_in :=
    (zr_clearPreMK_clean_and_bad htop hInv1.hcl hInv1.hz233).1
  have hcl_β_in : cleanRem 411 (411 - 275) β_in :=
    fun j hj ↦ hcl_in ⟨j.val, by omega⟩ hj
  have hag : ∀ u : Wire 411, ¬((177 ≤ u.val ∧ u.val < 198) ∨ (233 ≤ u.val ∧ u.val < 258)) →
      β_in u = β₁ u :=
    fun u hnb ↦ zr_clearPreMK_putQZ_eq_of_not_bad topW (st1 α) ⟨u.val, by omega⟩ hnb
  have hs_eq : bitsVal (fun i : Fin 18 ↦ β_in (n1sSTrue18W411 i)) =
      bitsVal (fun i : Fin 18 ↦ β₁ (n1sSTrue18W411 i)) :=
    congrArg bitsVal (funext fun i ↦ by
      have hr := n1s_sTrue18W411_range i
      exact hag _ (by rcases hr with r | r | r <;> omega))
  have hu_eq : bitsVal (fun k : Fin 38 ↦ β_in (n1sU38W411 k)) =
      bitsVal (fun k : Fin 38 ↦ β₁ (n1sU38W411 k)) :=
    congrArg bitsVal (funext fun k ↦ by
      have hr := n1s_u38W411_range k; exact hag _ (by omega))
  have hmu_eq : bitsVal (fun i : Fin 3 ↦ β_in (n1sMuW411 i)) =
      bitsVal (fun i : Fin 3 ↦ β₁ (n1sMuW411 i)) :=
    congrArg bitsVal (funext fun i ↦ hag _ (by dsimp [n1sMuW411]; omega))
  have hvs_eq : β_in n1sValidStaticW411 = β₁ n1sValidStaticW411 := hag _ (by decide)
  have hpr_eq : ∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β_in (n1sProjW411 w b)) =
      bitsVal (fun b : Fin 8 ↦ β₁ (n1sProjW411 w b)) :=
    fun w ↦ congrArg bitsVal (funext fun b ↦ hag _ (by dsimp [n1sProjW411]; omega))
  have hout0 : ∀ k : Fin 32, β_in (n1sOut32W411 k) = 0 := fun k ↦
    (hag _ (by dsimp [n1sOut32W411]; omega)).trans (hOut1 k)
  have hacc0 : β_in n1sAccFlagW411 = 0 := (hag _ (by decide)).trans hAcc1
  have hvalid : β_in n1sValidStaticW411 = 1 →
      bitsVal (fun i : Fin 3 ↦ β_in (n1sMuW411 i)) < 7 ∧
        2 * bitsVal (fun i : Fin 3 ↦ β_in (n1sMuW411 i)) ≤
          clz18Log2 (bitsVal (fun i : Fin 18 ↦ β_in (n1sSTrue18W411 i))) := fun hvs ↦ by
    rw [hmu_eq, hs_eq]
    have hmu1 : bitsVal (fun i : Fin 3 ↦ β₁ (n1sMuW411 i)) = shellMu3 (getU22 (st1 α)) :=
      (congrArg bitsVal (funext fun i ↦
        congrArg (st1 α) (Fin.ext (by fin_cases i <;> rfl)))).trans hInv1.mu_val
    have hs1 : bitsVal (fun i : Fin 18 ↦ β₁ (n1sSTrue18W411 i)) = sTrueRawVal (st1 α) :=
      (congrArg bitsVal (funext fun i ↦
        congrArg (st1 α) (Fin.ext (by fin_cases i <;> rfl)))).trans hInv1.hstrue
    rw [hmu1, hs1]
    have hvs' : validStaticVal216 (st1 α) = 1 :=
      (hInv1.hvs.symm.trans (congrArg (st1 α) (Fin.ext rfl)).symm).trans (hvs_eq.symm.trans hvs)
    exact ⟨shellMu3_lt_seven _, two_mul_mu_le_clz18Log2 hvs' hInv1.m_val⟩
  obtain ⟨_, _, hnon_ev, hval_ev⟩ := (zr_fwdStatic411_spec t).2 β_in hcl_β_in
  obtain ⟨hout_ev, hacc_ev⟩ := hval_ev hout0 hacc0 hvalid
  have hout_bits : bitsVal (fun k : Fin 32 ↦ (zrFwdStatic411 t).evalBits β_in (n1sOut32W411 k)) =
      bitsVal (fun k : Fin 32 ↦ n1sSt2 t α ⟨201 + k.val, by omega⟩) := by
    rw [hout_ev, hs_eq, hu_eq]; exact hout2.symm
  have hout_pt := bitsVal_injective hout_bits
  have htgt_eq : n1sAccTarget411 t β_in = n1sAccTarget411 t β₁ := by
    unfold n1sAccTarget411; simp only [hs_eq, hu_eq, hmu_eq, hvs_eq, hpr_eq]
  funext w
  by_cases hw149 : w.val = 149
  · have hw_acc : w = accWAux := Fin.ext hw149
    rw [hw_acc, zr_clearPreMK_putQZ_eq_of_not_bad topW _ accWAux (by decide)]
    dsimp only [n1sLiftEval411, accWAux]; rw [dite_eq_left (by decide)]
    exact (hacc2.trans htgt_eq.symm).trans hacc_ev.symm
  · by_cases hw201 : 201 ≤ w.val ∧ w.val < 233
    · rw [zr_clearPreMK_putQZ_eq_of_not_bad topW _ w (by omega)]
      dsimp only [n1sLiftEval411]; rw [dite_eq_left (by omega)]
      let k : Fin 32 := ⟨w.val - 201, by omega⟩
      have hlhs : n1sSt2 t α w = n1sSt2 t α ⟨201 + k.val, by omega⟩ :=
        congrArg (n1sSt2 t α) (Fin.ext (by dsimp [k]; omega))
      have hrhs : (zrFwdStatic411 t).evalBits β_in ⟨w.val, by omega⟩ =
          (zrFwdStatic411 t).evalBits β_in (n1sOut32W411 k) :=
        congrArg ((zrFwdStatic411 t).evalBits β_in)
          (Fin.ext (by dsimp [n1sOut32W411, k]; omega))
      exact (hlhs.trans (congrFun hout_pt k).symm).trans hrhs.symm
    · rw [zr_clearPreMK_putQZ_congr_outside_n1s topW hnon2 w hw149 hw201]
      dsimp only [n1sLiftEval411]
      by_cases hw411 : w.val < 411
      · rw [dite_eq_left hw411]
        exact (hnon_ev ⟨w.val, hw411⟩
          (fun h ↦ hw149 (congrArg Fin.val h))
          (fun k hk ↦ hw201 (by
            have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv; omega))).symm
      · rw [dite_eq_right hw411]; exact hcl_in w (by omega)

theorem zr_liftEval_rev_eq_st5 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {topW : ℕ} (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) (α : BitAssignment 149) :
    clearPreMKOfTopW topW (putQZ (n1sSt5 t cfg α)) =
      n1sLiftEval411 (zrRevStatic411 t) (clearPreMKOfTopW topW (putQZ (n1sSt4 t cfg α))) := by
  let δ_in := clearPreMKOfTopW topW (putQZ (n1sSt4 t cfg α))
  let β_in : BitAssignment 411 := fun j ↦ δ_in ⟨j.val, by omega⟩
  let β₄ : BitAssignment 411 := fun j ↦ n1sSt4 t cfg α ⟨j.val, by omega⟩
  obtain ⟨hInv4, _, hRevInv4⟩ := n1s_st4_props t cfg α
  obtain ⟨_, _, hAcc5, hOut5⟩ := n1s_st5_props t cfg α
  have hcl_in : cleanRem 437 (437 - 275) δ_in :=
    (zr_clearPreMK_clean_and_bad htop hInv4.hcl hInv4.hz233).1
  have hcl_β_in : cleanRem 411 (411 - 275) β_in :=
    fun j hj ↦ hcl_in ⟨j.val, by omega⟩ hj
  have hRev_in : n1sRevInv411 t β_in :=
    (zr_revInv411_congr_258 t fun u _ hnb ↦
      zr_clearPreMK_putQZ_eq_of_not_bad topW (n1sSt4 t cfg α) ⟨u.val, by omega⟩ hnb).mpr hRevInv4
  obtain ⟨_, _, hnon_ev, hzero_ev⟩ := (zr_revStatic411_spec t).2 β_in hcl_β_in
  obtain ⟨hacc0_ev, hout0_ev⟩ := hzero_ev hRev_in
  have hcl_β₄ : cleanRem 411 (411 - 275) β₄ := fun j hj ↦ hInv4.hcl ⟨j.val, by omega⟩ hj
  obtain ⟨_, _, hnon_n1s, _⟩ := (n1s_revStatic411_spec t).2 β₄ hcl_β₄
  have hnon5 : ∀ q : Wire 437, q.val ≠ 149 → ¬(201 ≤ q.val ∧ q.val < 233) →
      n1sSt5 t cfg α q = n1sSt4 t cfg α q := fun q h149 h201 ↦ by
    dsimp only [n1sSt5, n1sLiftEval411]
    by_cases h411 : q.val < 411
    · rw [dite_eq_left h411]
      exact hnon_n1s ⟨q.val, h411⟩
        (fun h ↦ h149 (congrArg Fin.val h))
        (fun k hk ↦ h201 (by have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv; omega))
    · rw [dite_eq_right h411]; exact (hInv4.hcl q (by omega)).symm
  funext w
  by_cases hw149 : w.val = 149
  · have hw_acc : w = accWAux := Fin.ext hw149
    rw [hw_acc, zr_clearPreMK_putQZ_eq_of_not_bad topW _ accWAux (by decide), hAcc5]
    dsimp only [n1sLiftEval411, accWAux]; rw [dite_eq_left (by decide)]
    exact hacc0_ev.symm
  · by_cases hw201 : 201 ≤ w.val ∧ w.val < 233
    · rw [zr_clearPreMK_putQZ_eq_of_not_bad topW _ w (by omega), hOut5 w hw201.1 (by omega)]
      dsimp only [n1sLiftEval411]; rw [dite_eq_left (by omega)]
      have hw411 : (⟨w.val, by omega⟩ : Wire 411) = n1sOut32W411 ⟨w.val - 201, by omega⟩ :=
        Fin.ext (by dsimp [n1sOut32W411]; omega)
      rw [hw411]; exact (hout0_ev _).symm
    · rw [zr_clearPreMK_putQZ_congr_outside_n1s topW hnon5 w hw149 hw201]
      dsimp only [n1sLiftEval411]
      by_cases hw411 : w.val < 411
      · rw [dite_eq_left hw411]
        exact (hnon_ev ⟨w.val, hw411⟩
          (fun h ↦ hw149 (congrArg Fin.val h))
          (fun k hk ↦ hw201 (by
            have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv; omega))).symm
      · rw [dite_eq_right hw411]; exact hcl_in w (by omega)

end Part4B_Norm1sCompact

end

set_option maxRecDepth 512

end ConfigLeaf3Slot3ZRet193Sec4B

end Leaf3Slot3ZRet193

end
set_option exponentiation.threshold 256
end Leaf3Slot3ZRet193Sec4B

section SelAndPertStitch
local instance (priority := 1000000) instNeZeroTwoPow_SelAndPertStitch (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
Hoisted SELECT Oracle Assembly and Grid-Perturbation Stitch (`SelAndPertStitch`):

1. `leaf2Spec44409OfTrunc` / `leaf2Spec44409` (`Section 1`):
   Specializes `Leaf2Packed18Mux2DCore.leaf2SpecMidOfB` to `B = 12`
   (`tCtrl = 44,409`, `tCat = 43,649`).
2. `cutVepTwistOutBundleOfTrunc` (`Section 2`):
   Constructs `HoistedTwistRestOutBundle (mPayload := 80) (mPGTwist := 48) mWork`
   (`mWorkTwist <= mWork`) realizing `uVepFusedTwistRestCutCat` (`51,839 T/side`, `0 .TOFF`) and
   intertwining to `uVepFusedTwistRestCut80 (truncFn cfg)`.
3. `mkHoistedSelectBundleOfTrunc`, `stepSelectOraHypothesisOfTrunc`, and
   `uCoin_gridPerturbation_of_trunc` (`Section 3`):
   Width-unrestricted hoisted `SELECT` oracle bundle (`mWork = max 288 s3.mWork`), discharging
   `SelectOraHypothesisOfTrunc` for any `MomSingleSlotOracle 80 48 3` and wrapping
   `zeroSubwire_uCoin_gridPerturbation_of_trunc_param_s1_b2b4_of_posPhase`.
-/

public section

namespace SelAndPertStitch

section ConfigSelAndPertStitch

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency true

open Operator QProg Matrix Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
-- Root solution namespace already active.
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysCatSegmentBridge (fullSysCoreWires iSlot2 FullSysSelectOracleBundle IntertwinesLocalCat)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open HoistedSwapSelectBridge (FullSysHoistedSelectBundle)
open FullSysHoistedSelectStitch (HoistedBarrelSpec)
open OraAndPrepBundle (coreUnitaryFromFullSys)
open GeneralBetaAndAlphaTopEndpoint
  (zeroMomSlotOracle5 HoistedTwistRestOutBundle)
open TierClosure (zeroMomLocalSlotData)
open TierBClean80Closure (tierBBarrel80)
open PosSlots24TopWrapper (PosSlots24DataGen)
open CoinDispatchedBarrel288 (uBarrelFast)
open NuclearTwistRealizes
  (uXor32Core uSlot4KickCore
     intertwinesLocalCat_to_fullSys)
open NuclearTwistAndXor654Concrete
  (mWorkTwist)
open FusedPreDiagFromTwist288
  (hm6_of_hm22 uTildeFullCore uPreDiagCliffordCore
    embed_uPre654_eq_xor32_clifford_uTildeCore)
open ProjZ512QftAndTwist288
  (uVepSlot2KickCore rCoreBlock48
   uVepFusedSlot2KickCat
    uVepFusedSlot2KickCat_intertwinesLocal)
open JunctionApexCSA288 (uSlot4ApexCat_intertwinesLocal)
open DyadicQft64Engine (phaseGradKet)
open MomSlot1Dyadic459Sub36w (slot1Dyadic459Oracle)
open MomSlot1DyadicTopAdapter (HoistedMomLocalSpecS1 mkHoistedMomLocalFromS1S3L5Fast
  mkFullSysHoistedSelectBundleOutS1)
open SchedBranchStitchGen (uVepFusedTwistRestCut80)
open SelectStitch (Leaf2SpecOfTrunc SelectOraHypothesisOfTrunc)

local instance (priority := 1000000) instLoc_SelAndPertStitch_1InstNeZeroTwoPowSelAndPert (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

theorem uProj3DCut1DCore_bridge_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    JunctionProj3DCut.uProj3DCut1DCore hm w = JunctionProj3DCutPos24BridgeGen.uProj3DCut1DCore hm
    w := Subtype.ext (Matrix.ext fun _ _ ↦ rfl)

theorem uProj3DCutCore_bridge_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    JunctionProj3DCut.uProj3DCutCore hm = JunctionProj3DCutPos24BridgeGen.uProj3DCutCore hm := by
  unfold JunctionProj3DCut.uProj3DCutCore JunctionProj3DCutPos24BridgeGen.uProj3DCutCore
  rw [uProj3DCut1DCore_bridge_eq, uProj3DCut1DCore_bridge_eq, uProj3DCut1DCore_bridge_eq]

theorem uVepFusedTwistRestCut80_eq_bridge (c : Configuration) : uVepFusedTwistRestCut80 c =
    JunctionProj3DCutPos24BridgeGen.uVepFusedTwistRestCut (by decide : 22 ≤ 80) c := by
  unfold uVepFusedTwistRestCut80 SchedBranchStitchGen.uVepTwistRestCut80
    JunctionProj3DCutPos24BridgeGen.uVepFusedTwistRestCut
    JunctionProj3DCutPos24BridgeGen.uVepTwistRestCut
  rw [uProj3DCutCore_bridge_eq]

/-- Catalyst-lifted fused cut twist remainder unitary on `fullSysCoreWires mPayload + 48`. -/
noncomputable def uVepFusedTwistRestCutCat {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (c : Configuration) : Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  (rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload) *
    ((rCoreBlock48 mPayload).embedUnitary (uPreDiagCliffordCore (hm6_of_hm22 hm)) *
      (uVepFusedSlot2KickCat c hm * JunctionProj3DCut.uJunctionPrefixCutCat hm))

theorem uVepFusedTwistRestCutCat_intertwinesLocal_of_col0 {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (c : Configuration) (U_catTwist : Unitary (2 ^ 48)) (hcol : ∀ m : Fin (2 ^ 48),
    U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) : IntertwinesLocalCat
    U_catTwist (uVepFusedTwistRestCutCat hm c)
    (JunctionProj3DCutPos24BridgeGen.uVepFusedTwistRestCut hm c) := by
  have hcol0 : U_catTwist.1.mulVec (Pi.single 0 1) = phaseGradKet 48 := by
    funext m
    rw [Matrix.mulVec_single_one]
    change U_catTwist.1 m 0 = phaseGradKet 48 m
    exact (hcol m).trans (by
      unfold PhaseGradCatalystCore.phaseGradientState DyadicQft64Engine.phaseGradKet
      congr 1)
  have hP3 := JunctionProj3DCut.uProj3DCutApexCat_intertwinesLocal hm U_catTwist hcol0
  have hXor := NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_catTwist
    (uXor32Core mPayload)
  have hS4 := uSlot4ApexCat_intertwinesLocal hm U_catTwist hcol0
  have hPref : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_catTwist
      (JunctionProj3DCut.uJunctionPrefixCutCat hm) (uSlot4KickCore hm * (uXor32Core mPayload *
      JunctionProj3DCut.uProj3DCutCore hm)) := (hP3.mul hXor).mul hS4
  have hS2 := uVepFusedSlot2KickCat_intertwinesLocal c hm U_catTwist hcol0
  have hCl := NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_catTwist
    (uPreDiagCliffordCore (hm6_of_hm22 hm))
  have hAll := ((hPref.mul hS2).mul hCl).mul hXor
  have hEffEq : uXor32Core mPayload * (uPreDiagCliffordCore (hm6_of_hm22 hm) *
      ((uTildeFullCore (hm6_of_hm22 hm) * uVepSlot2KickCore c hm) * (uSlot4KickCore hm *
      (uXor32Core mPayload * JunctionProj3DCut.uProj3DCutCore hm)))) =
      JunctionProj3DCutPos24BridgeGen.uVepFusedTwistRestCut hm c := by
    unfold JunctionProj3DCutPos24BridgeGen.uVepFusedTwistRestCut
      JunctionProj3DCutPos24BridgeGen.uVepTwistRestCut
    rw [embed_uPre654_eq_xor32_clifford_uTildeCore (hm6_of_hm22 hm), ← uProj3DCutCore_bridge_eq hm]
    simp only [mul_assoc]
  rw [hEffEq] at hAll
  exact intertwinesLocalCat_to_fullSys hAll

/-- Turnkey `HoistedTwistRestOutBundle` (`mPayload = 80`, `mPGTwist = 48`, `51,839 T/side`,
`0 .TOFF`) realizing `uVepFusedTwistRestCut80 (truncFn cfg)` for any `mWorkTwist <= mWork`. -/
noncomputable def cutVepTwistOutBundleOfTrunc {mWork : ℕ}
    (_hmWork : mWorkTwist ≤ mWork)
    (truncFn : Configuration → Configuration) :
    HoistedTwistRestOutBundle (mPayload := 80) (mPGTwist := 48) mWork where
  uTwistRestCat c := uVepFusedTwistRestCutCat (by decide : 22 ≤ 80) (truncFn c)
  uTwistRest c := uVepFusedTwistRestCut80 (truncFn c)
  hIntertwinesTwistRest c U_catTwist hcol := by
    rw [uVepFusedTwistRestCut80_eq_bridge (truncFn c)]
    exact uVepFusedTwistRestCutCat_intertwinesLocal_of_col0 (by decide : 22 ≤ 80)
      (truncFn c) U_catTwist hcol
  hCoinWireComm c q hqLo hqHi b := by
    rw [uVepFusedTwistRestCut80_eq_bridge (truncFn c)]
    exact JunctionProj3DCutPos24BridgeGen.uVepFusedTwistRestCut_comm_coin_wire
      (by decide : 22 ≤ 80) (truncFn c) q hqLo hqHi b

/- ## Section 3: Width-Unrestricted Hoisted `SELECT` Assembly and Grid-Perturbation Wrapper -/

/-- Widen a `HoistedBarrelSpec mPayload mW0` to any workspace width `mWork >= mW0`. -/
noncomputable def widenHoistedBarrel {mPayload mW0 mWork : ℕ} (_hmW : mW0 ≤ mWork)
    (b : HoistedBarrelSpec mPayload mW0) : HoistedBarrelSpec mPayload mWork :=
  { uBarrel := b.uBarrel
    hHighWireComm := b.hHighWireComm }

theorem tierBBarrel80_eq_uBarrelFast (cfg : Configuration) :
    tierBBarrel80.uBarrel cfg = uBarrelFast (le_refl 80) :=
  FastCoinBarrel288.fastHoistedBarrelSpec145_uBarrel (le_refl 80) cfg

theorem unitaryConj_hoisted_eq_posMom {D : ℕ} (B M : Unitary D) :
    HoistedSwapSelectBridge.unitaryConj B M = unitaryConj B M := Subtype.ext
    ((HoistedSwapSelectBridge.unitaryConj_val B M).trans (unitaryConj_val B M).symm)

/-- `PosSlots24DataGen` (`288w`) built from any `Leaf2SpecOfTrunc`
(`uPosPhase _ = leaf2.uPosPhase0`). -/
noncomputable def posDataOfLeaf2 {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat) :
    PosSlots24DataGen (fullSysCoreWires 80) (iSlot2 80) 288 where
  uPosPhase _ := leaf2.uPosPhase0
  hPos_sa _ := leaf2.hPosSA
  hPos_on_P1 _ := leaf2.hPosOnP1

/-- `tierBBarrel80` widened to `max 288 s3.mWork` so any `MomSingleSlotOracle 80 48 3` plugs in
with zero workspace-width hypothesis. -/
noncomputable def stepBarrelWiden (s3 : MomSingleSlotOracle 80 48 3) : HoistedBarrelSpec 80
    (max 288 s3.mWork) := widenHoistedBarrel (Nat.le_max_left 288 s3.mWork) tierBBarrel80

/-- Zero-cost Slot-5 local data (`0 T`, `mWork = 0`) paired with `stepBarrelWiden s3`. -/
noncomputable def stepZeroSlot5Data (s3 : MomSingleSlotOracle 80 48 3) :
    MomSlot0LocalAndMomCombine288.MomLocalSlotData 80 48 5 (fun cfg ↦ coreUnitaryFromFullSys
    ((stepBarrelWiden s3).uBarrel cfg)) := zeroMomLocalSlotData (fun cfg ↦
    coreUnitaryFromFullSys ((stepBarrelWiden s3).uBarrel cfg)) (zeroMomSlotOracle5 80 48)
    (fun _ ↦ rfl)

/-- Combined 4-slot local momentum bundle (`Slots 0, 1, 3, 5`) for any `s3` at width
`max 288 s3.mWork`. -/
noncomputable def mkMomLocalOfS3 (s3 : MomSingleSlotOracle 80 48 3) :
    HoistedMomLocalSpecS1 (le_refl 80) (max 288 s3.mWork) (stepBarrelWiden s3)
      slot1Dyadic459Oracle s3 (zeroMomSlotOracle5 80 48) :=
  mkHoistedMomLocalFromS1S3L5Fast (le_refl 80) (Nat.le_max_left 288 s3.mWork)
    (stepBarrelWiden s3) tierBBarrel80_eq_uBarrelFast s3 (stepZeroSlot5Data s3)
    (Nat.le_max_right 288 s3.mWork) (Nat.zero_le _)

/-- Width-unrestricted `FullSysHoistedSelectBundle 80 48` (`mWorkSelect = max 288 s3.mWork`)
combining `stepBarrelWiden s3`, `cutVepTwistOutBundleOfTrunc`, `posDataOfLeaf2 leaf2`,
`slot1Dyadic459Oracle`, `s3`, and `zeroMomSlotOracle5 80 48`. -/
noncomputable def mkHoistedSelectBundleOfTrunc {t2Ctrl t2Cat : ℕ}
    (truncFn : Configuration → Configuration)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat) (s3 : MomSingleSlotOracle 80 48 3) :
    FullSysHoistedSelectBundle 80 48 :=
  mkFullSysHoistedSelectBundleOutS1 (hm22 := (by decide : 22 ≤ 80)) (hm80 := le_refl 80)
    (stepBarrelWiden s3)
    (cutVepTwistOutBundleOfTrunc
      (le_trans (by decide : mWorkTwist ≤ 288) (Nat.le_max_left 288 s3.mWork)) truncFn)
    (posDataOfLeaf2 leaf2)
    slot1Dyadic459Oracle s3 (zeroMomSlotOracle5 80 48)
    (mkMomLocalOfS3 s3)
    (Nat.le_max_left 288 s3.mWork)

/-- Turnkey `FullSysSelectOracleBundle 80 48` at arbitrary `truncFn`. -/
noncomputable def mkSelectOraBundleOfTrunc {t2Ctrl t2Cat : ℕ}
    (truncFn : Configuration → Configuration)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat) (s3 : MomSingleSlotOracle 80 48 3) :
    FullSysSelectOracleBundle 80 48 := (mkHoistedSelectBundleOfTrunc truncFn leaf2
    s3).toSelectOracleBundle

/-- Discharges `SelectOraHypothesisOfTrunc` for `mkSelectOraBundleOfTrunc` with zero
workspace-width side conditions on `s3`. -/
theorem stepSelectOraHypothesisOfTrunc {t2Ctrl t2Cat : ℕ}
    (truncFn : Configuration → Configuration)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (s3 : MomSingleSlotOracle 80 48 3) :
    SelectOraHypothesisOfTrunc truncFn
      (mkSelectOraBundleOfTrunc truncFn leaf2 s3) leaf2 s3 where
  hTw c := congrArg (uVepFusedTwistRestCut80 (truncFn c) * ·) (tierBBarrel80_eq_uBarrelFast c)
  hMom c := (unitaryConj_hoisted_eq_posMom (tierBBarrel80.uBarrel c) _).trans
    (congrArg (fun B ↦ unitaryConj B _) (tierBBarrel80_eq_uBarrelFast c))
  hPosEq _ := rfl

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512
set_option exponentiation.threshold 256

end ConfigSelAndPertStitch

end SelAndPertStitch

end
set_option exponentiation.threshold 256
end SelAndPertStitch

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
