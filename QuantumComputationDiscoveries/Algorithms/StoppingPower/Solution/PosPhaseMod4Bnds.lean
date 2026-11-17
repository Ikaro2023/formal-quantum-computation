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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SelectHoistComm
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot2ZeroMux28To35

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosS3Bounds
local instance (priority := 1000000) instNeZeroTwoPow_PosS3Bounds (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace PosS3Bounds

section ConfigPosS3Bounds
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift (nyq512ProjEquiv3D)
open Dyadic128CoulombMath (orbitCount47905)
open CanonRank7Circuit (fineCoordOfReg21)
open MeasureBranchHadamardSem (ket bit_cases)
open ZeroAncillaUSP (omega8 omega8_sq)
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysCatSegmentBridge
  (FullSysQft654Bundle fullSysCoreWires fullSysQftCoreUnitary coreElecCosetB1Block)
open FullSysFullPrepareAndTopConcrete (selWiresSym coreAncSym)
open TierBClean80Closure (tierBQftFull)
open ProjZ512QftAndTwist288
  (cfgProjZ512 projGridEquiv24 uProjPlus512_3D rProjCore extractProj24 extractCosetP3
   vepHighNuc_iff vepWriteReg vepSwapNuc)
open PosSlots24BranchConcrete
  (posCoreWires wSlot0Core wSlot1Core wSlot2Core wIsHead wSubReject wHeadThresh wRejectZero
   rNucIdx rAnchorIdx rPartnerIdx rTailKeep30 rHeadFine21 rCosetB0 rCosetB1 rElecSlot
   slotSubGridCoord64 axisBitRev6 parity3OfReg tailAndSlackPhaseBitSpec uPosPhase)
open PosSlots24SemanticBridge
  (pos24_6_le_80 pos24_22_le_80 pos24_coreWires80_eq pos24_core80_eq_twist80
   pos24TailSign pos24TailMag30 castUnitaryPow2 mulUnitaryPow2 sysBlockAtPayloadGen)
open PosSlots24SemanticOracleConcrete80 (QftPreservesCoset3 hkSym80 coreBetaOf coreIdxOf ancIdx86
  rAncFlag80 embedMatrix_entry_of_agreeOutside embedMatrix_entry_of_not_agreeOutside
  entry_zero_of_comm_basisOutcomeProjector regVal_eq_of_wire_eq)
open PosSlots24Semantic80Physics (pos80IdealDist)
open PosPostPrep80MergedVep
  (conjSwapCore3967 uSwapCore3967 uSwapCore3967_mulVec_ket swapCore3967Fn swapCore3967Fn_involutive)
open PosPostPrep80InnerAmpS3 (ancBits86)
open MergedVepTopCoinCollapse
  (mProj24_sp mProjGridEquiv24 mProjBasisGen mWCore3967Gen mWCoreScrGen swapCoreScrGenFn
   p80NucVal p80NucVal_lt_256 p80CosetP3 p80SetNucZero mergedSliceGen mergedCoherentOpGen
   coreUnitarySym)
open MergedVepCoreSliceClosure
  (msc_congr2 msc_ite_pos msc_ite_neg mscUVepTwistRef mscUTwistParam mscVepSwapNuc mscRNucCore
    mscRProjCore mscExtractProj24 mscExtractCosetP3 mscVepHighNuc mscCoreBeta mscWSlot0 mscPredA
    mscPredB mscDiagPred mscDiagPredB mscCfgY mscGammaAct mscTailAlpha mscTailVH
    matrix_ext_of_ket_core msc_basisBits_symm msc_diagonal_mulVec_ket msc_conj3_entry_eq_dotProduct
    msc_conj_entry_eq_of_proj msc_conj_entry_eq_finset_sum_of_orth_proj msc_unitary_adj_mul_self
    msc_mul2_comm msc_fullSysQft_pf_congr msc_mulUnitaryPow2_qft_twist msc_cast_basisBits_symm
    msc_qft_comm_rAncFlag80 msc_uVepTwistRef_comm_rAncFlag80 msc_transport_entry_of_comm
    msc_uVepTwistRef_host_ket msc_uVepTwistRef_vep_ket msc_coreBetaOf_coin0_bits
    msc_coreBetaOf_coin1_wSlot0 msc_uTwistParam_preserves_diag_ge3924
    msc_qft_preserves_diag_not_in_elecCosetB1 msc_wire_not_in_elecCosetB1 msc_coreBetaOf_scr_zero
    msc_regVal_rNuc_coreBetaOf msc_regVal_posBranch_eq_twist msc_scr_ge_3924 msc_scr_ge_3957
    msc_rNucBranch_ge_3924 msc_rNucBranch_ge_3957 msc_rNucCore_in_range msc_vepSwapNuc_mulVec_ket
    mscGammaAct_scr_zero mscGammaAct_out msc_hFwdVep msc_tail_hs msc_tail_hvIn msc_tail_hOrth
    msc_mergedSliceGen_lt msc_mergedSliceGen_ge_sum msc_proj_sandwich_entry_gen)
open Pos24MergedVepPrepAndStitch (mergedPosSlot2BUnitTwosGen)
open MergedVepLeaf4GridPerturbation
  (swapCore3967Fn_eq_swapCoreScrGenFn12)
open PosHeadMod4_15476
  (omega8_pow_four flipTh flipThClean permThClean ket_permThClean embedUnitary_permThClean
   ket_monomialZ8UnitaryN headEnBoolSpec headHitSetSpec headPhaseMod4Z8Spec posPhaseMod4Z8Spec
   uPosPhaseMod4 headEnBoolSpec_update_wHeadThresh headHitSetSpec_update_wHeadThresh
   tailAndSlackPhaseBitSpec_update_wHeadThresh)

-- ============================================================================
-- Section 1: Fermionic + Midpoint Perturbation Caps (delta2, delta4, deltaPos)
-- ============================================================================

/-- Real Boolean counterpart of the Mod-4 head phase on `posCoreWires`. -/
def headPhaseBitMod4Spec (β : BitAssignment posCoreWires) : Bool :=
  let rCore := QRegExt.ofFin posCoreWires
  if Bool.not (headEnBoolSpec β) then false
  else
    let s0 := β (wSlot0Core rCore) == 1
    let c := (headHitSetSpec β).card
    let rawBit := if c % 2 == 1 then (β (wHeadThresh rCore) == 1) else Bool.not (decide (c % 4 = 0))
    if s0 then Bool.not rawBit else rawBit

/-- Combined Mod-4 head and tail/slack Boolean phase bit on `posCoreWires`. -/
def posPhaseBitMod4 (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (β : BitAssignment posCoreWires) : Bool
    := Bool.xor (headPhaseBitMod4Spec β)
    (tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β)

/-- Diagonal sign unitary on `posCoreWires` induced by `posPhaseBitMod4`. -/
noncomputable def uPosPhaseRealMod4 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : Unitary (2 ^ posCoreWires) :=
  BchCubeDecoder.diagonalSignUnitaryN (posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30)

/-- Canonicalized `posCoreWires` bit assignment zeroing projectile, slack, and scratch wires. -/
def canonPosCoreBits (β : BitAssignment posCoreWires) : BitAssignment posCoreWires := fun w ↦
    if (3924 ≤ w.val ∧ w.val < 3948) ∨ (3951 ≤ w.val ∧ w.val < 3954) ∨
    (4017 ≤ w.val ∧ w.val < 4033) then 0 else β w

private theorem zmod8_mul_even_eq_mod4 (c : ℕ) (k : ZMod 8) (hk : (4 : ZMod 8) * k = 0) :
    (c : ZMod 8) * k = ((c % 4 : ℕ) : ZMod 8) * k := by
  conv_lhs => rw [← Nat.div_add_mod c 4]
  push_cast
  calc ((4 : ZMod 8) * ((c / 4 : ℕ) : ZMod 8) + ((c % 4 : ℕ) : ZMod 8)) * k
      = ((4 : ZMod 8) * k) * ((c / 4 : ℕ) : ZMod 8) + ((c % 4 : ℕ) : ZMod 8) * k := by ring
    _ = ((c % 4 : ℕ) : ZMod 8) * k := by rw [hk, zero_mul, zero_add]

theorem zmod8_mul_two_eq_mod4 (c : ℕ) : (c : ZMod 8) * 2 = ((c % 4 : ℕ) : ZMod 8) * 2 :=
  zmod8_mul_even_eq_mod4 c 2 rfl

theorem zmod8_mul_six_eq_mod4 (c : ℕ) : (c : ZMod 8) * 6 = ((c % 4 : ℕ) : ZMod 8) * 6 :=
  zmod8_mul_even_eq_mod4 c 6 rfl

theorem omega8_pow_even_zmod8 (x : ZMod 8) : omega8 ^ x.val = if decide (x = 0) then 1 else if
    decide (x = 2) then Complex.I else if decide (x = 4) then -1 else if decide (x = 6) then
    -Complex.I else omega8 ^ x.val := by
  have h2 : omega8 ^ 2 = Complex.I := omega8_sq
  have h4 : omega8 ^ 4 = -1 := omega8_pow_four
  have h6 : omega8 ^ 6 = -Complex.I := by
    calc omega8 ^ 6 = omega8 ^ 4 * omega8 ^ 2 := by ring
      _ = -Complex.I := by rw [h4, h2]; ring
  fin_cases x
  · change omega8 ^ 0 = 1; simp
  · rfl
  · change omega8 ^ 2 = Complex.I; exact h2
  · rfl
  · change omega8 ^ 4 = -1; exact h4
  · rfl
  · change omega8 ^ 6 = -Complex.I; exact h6
  · rfl

theorem mod4_phase_pair_sum_finite (en s0 tb : Bool) (rv : ℕ)
    (hr : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3) :
    let e0 : ZMod 8 := (if Bool.not en then 0 else (if s0 then 4 else 0) + (rv : ZMod 8) * 2)
        + (if tb then 4 else 0)
    let e1 : ZMod 8 := (if Bool.not en then 0 else (if s0 then 4 else 0) + (rv : ZMod 8) * 6)
        + (if tb then 4 else 0)
    let b0 : Bool :=
      Bool.xor
        (if Bool.not en then false else
          let raw := if rv % 2 == 1 then false else Bool.not (decide (rv = 0))
          if s0 then Bool.not raw else raw)
        tb
    let b1 : Bool :=
      Bool.xor
        (if Bool.not en then false else
          let raw := if rv % 2 == 1 then true else Bool.not (decide (rv = 0))
          if s0 then Bool.not raw else raw)
        tb
    omega8 ^ e0.val + omega8 ^ e1.val =
      (if b0 then (-1 : ℂ) else 1) + (if b1 then (-1 : ℂ) else 1) := by
  intro e0 e1 b0 b1
  rw [omega8_pow_even_zmod8 e0, omega8_pow_even_zmod8 e1]
  dsimp only [e0, e1, b0, b1]
  rcases hr with rfl | rfl | rfl | rfl <;>
    cases en <;> cases s0 <;> cases tb <;>
    simp +decide only [Bool.false_eq_true, decide_true, decide_false, ↓reduceIte] <;>
    ring

private theorem posPhaseMod4Z8Spec_update_wHeadThresh_bit (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment posCoreWires) (b : ZMod 2) (k : ZMod 8)
    (hk : ((2 : ZMod 8) + if (b == 1) then 4 else 0) = k)
    (hmod : ∀ c : ℕ, (c : ZMod 8) * k = ((c % 4 : ℕ) : ZMod 8) * k) :
    posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30
        (Function.update γ (wHeadThresh (QRegExt.ofFin posCoreWires)) b) =
      (if Bool.not (headEnBoolSpec γ) then 0
       else (if γ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1 then 4 else 0) +
         (((headHitSetSpec γ).card % 4 : ℕ) : ZMod 8) * k) +
      (if tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 γ then 4 else 0) := by
  let rCore := QRegExt.ofFin posCoreWires
  let wTh := wHeadThresh rCore
  have hEn := headEnBoolSpec_update_wHeadThresh γ b
  have hHit := headHitSetSpec_update_wHeadThresh γ b
  have hTail := tailAndSlackPhaseBitSpec_update_wHeadThresh slot2SwappedTo0 tailSign tailMag30 γ b
  have hS0 : Function.update γ wTh b (wSlot0Core rCore) = γ (wSlot0Core rCore) :=
    Function.update_of_ne (PosHeadMod4_15476.wHeadThresh_ne_wSlot0Core rCore).symm _ _
  unfold posPhaseMod4Z8Spec headPhaseMod4Z8Spec
  dsimp only [rCore, wTh] at hEn hHit hTail hS0 ⊢
  rw [hEn, hHit, hTail, hS0, Function.update_self, hk, hmod]

theorem posPhaseMod4Z8Spec_update_wHeadThresh_zero (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment posCoreWires) : posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30
    (Function.update γ (wHeadThresh (QRegExt.ofFin posCoreWires)) 0) = (if Bool.not
    (headEnBoolSpec γ) then 0 else (if γ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1 then
    4 else 0) + (((headHitSetSpec γ).card % 4 : ℕ) : ZMod 8) * 2) + (if
    tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 γ then 4 else 0) :=
  posPhaseMod4Z8Spec_update_wHeadThresh_bit slot2SwappedTo0 tailSign tailMag30 γ 0 2 rfl
    zmod8_mul_two_eq_mod4

theorem posPhaseMod4Z8Spec_update_wHeadThresh_one (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment posCoreWires) : posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30
    (Function.update γ (wHeadThresh (QRegExt.ofFin posCoreWires)) 1) = (if Bool.not
    (headEnBoolSpec γ) then 0 else (if γ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1 then
    4 else 0) + (((headHitSetSpec γ).card % 4 : ℕ) : ZMod 8) * 6) + (if
    tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 γ then 4 else 0) :=
  posPhaseMod4Z8Spec_update_wHeadThresh_bit slot2SwappedTo0 tailSign tailMag30 γ 1 6 rfl
    zmod8_mul_six_eq_mod4

private theorem posPhaseBitMod4_update_wHeadThresh_bit (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment posCoreWires) (b : ZMod 2) :
    posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30
        (Function.update γ (wHeadThresh (QRegExt.ofFin posCoreWires)) b) =
      Bool.xor
        (if Bool.not (headEnBoolSpec γ) then false else
          let raw := if ((headHitSetSpec γ).card % 4) % 2 == 1 then (b == 1)
            else Bool.not (decide ((headHitSetSpec γ).card % 4 = 0))
          if γ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1 then Bool.not raw else raw)
        (tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 γ) := by
  let rCore := QRegExt.ofFin posCoreWires
  let wTh := wHeadThresh rCore
  have hEn := headEnBoolSpec_update_wHeadThresh γ b
  have hHit := headHitSetSpec_update_wHeadThresh γ b
  have hTail := tailAndSlackPhaseBitSpec_update_wHeadThresh slot2SwappedTo0 tailSign tailMag30 γ b
  have hS0 : Function.update γ wTh b (wSlot0Core rCore) = γ (wSlot0Core rCore) :=
    Function.update_of_ne (PosHeadMod4_15476.wHeadThresh_ne_wSlot0Core rCore).symm _ _
  have hmod2 : (headHitSetSpec γ).card % 2 = ((headHitSetSpec γ).card % 4) % 2 := by omega
  unfold posPhaseBitMod4 headPhaseBitMod4Spec
  dsimp only [rCore, wTh] at hEn hHit hTail hS0 ⊢
  rw [hEn, hHit, hTail, hS0, Function.update_self, hmod2]

theorem posPhaseBitMod4_update_wHeadThresh_zero (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment posCoreWires) :
    posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30
        (Function.update γ (wHeadThresh (QRegExt.ofFin posCoreWires)) 0) =
      Bool.xor
        (if Bool.not (headEnBoolSpec γ) then false else
          let raw := if ((headHitSetSpec γ).card % 4) % 2 == 1 then false
            else Bool.not (decide ((headHitSetSpec γ).card % 4 = 0))
          if γ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1 then Bool.not raw else raw)
        (tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 γ) :=
  posPhaseBitMod4_update_wHeadThresh_bit slot2SwappedTo0 tailSign tailMag30 γ 0

theorem posPhaseBitMod4_update_wHeadThresh_one (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment posCoreWires) :
    posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30
        (Function.update γ (wHeadThresh (QRegExt.ofFin posCoreWires)) 1) =
      Bool.xor
        (if Bool.not (headEnBoolSpec γ) then false else
          let raw := if ((headHitSetSpec γ).card % 4) % 2 == 1 then true
            else Bool.not (decide ((headHitSetSpec γ).card % 4 = 0))
          if γ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1 then Bool.not raw else raw)
        (tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 γ) :=
  posPhaseBitMod4_update_wHeadThresh_bit slot2SwappedTo0 tailSign tailMag30 γ 1

theorem posPhaseMod4Z8_pair_sum_eq_posPhaseBitMod4
    (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment posCoreWires) :
    let wTh := wHeadThresh (QRegExt.ofFin posCoreWires)
    let γ₀ := Function.update γ wTh 0
    let γ₁ := Function.update γ wTh 1
    omega8 ^ (posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30 γ₀).val +
      omega8 ^ (posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30 γ₁).val =
    (if posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30 γ₀ then (-1 : ℂ) else 1) +
      (if posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30 γ₁ then (-1 : ℂ) else 1) := by
  intro wTh γ₀ γ₁
  dsimp only [γ₀, γ₁, wTh]
  rw[posPhaseMod4Z8Spec_update_wHeadThresh_zero, posPhaseMod4Z8Spec_update_wHeadThresh_one,
      posPhaseBitMod4_update_wHeadThresh_zero, posPhaseBitMod4_update_wHeadThresh_one]
  exact mod4_phase_pair_sum_finite (headEnBoolSpec γ)
    (γ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1)
    (tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 γ)
    ((headHitSetSpec γ).card % 4)
    (by have := Nat.mod_lt (headHitSetSpec γ).card (by decide : 0 < 4); omega)

abbrev wThCore : Wire posCoreWires := wHeadThresh (QRegExt.ofFin posCoreWires)

/-- Single-bit permutation unitary flipping `wHeadThresh` on `posCoreWires`. -/
noncomputable def uXThCore : Unitary (2 ^ posCoreWires) :=
  permutationUnitary (permThClean wThCore (fun _ ↦ true))

theorem ket_uXThCore (γ : BitAssignment posCoreWires) :
    uXThCore.1.mulVec (OctahedralOrbit.ket γ) =
      OctahedralOrbit.ket (Function.update γ wThCore (γ wThCore + 1)) := by
  dsimp only [uXThCore]
  rw [ket_permThClean]
  congr 1

theorem one_add_uXThCore_mulVec_ket (γ : BitAssignment posCoreWires) :
    ((1 : Operator (2 ^ posCoreWires)) + uXThCore.1).mulVec (OctahedralOrbit.ket γ) =
      OctahedralOrbit.ket (Function.update γ wThCore 0) +
        OctahedralOrbit.ket (Function.update γ wThCore 1) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ket_uXThCore]
  rcases bit_cases (γ wThCore) with h0 | h1
  · have h01 : γ wThCore + 1 = 1 := by
      rw [h0]
      rfl
    rw [h01, ← h0, Function.update_eq_self]
  · have h10 : γ wThCore + 1 = 0 := by
      rw [h1]
      rfl
    rw [h10, ← h1, Function.update_eq_self, add_comm]

theorem one_add_uXThCore_mulVec_ket_update (γ : BitAssignment posCoreWires) (b : ZMod 2) :
    ((1 : Operator (2 ^ posCoreWires)) + uXThCore.1).mulVec
    (OctahedralOrbit.ket (Function.update γ wThCore b)) = OctahedralOrbit.ket
    (Function.update γ wThCore 0) + OctahedralOrbit.ket (Function.update γ wThCore 1) := by
  rw [one_add_uXThCore_mulVec_ket, Function.update_idem, Function.update_idem]

theorem one_add_uXThCore_mulVec_ket_flipThClean (γ : BitAssignment posCoreWires)
    (d : BitAssignment posCoreWires → Bool) (b : ZMod 2) :
    ((1 : Operator (2 ^ posCoreWires)) + uXThCore.1).mulVec (OctahedralOrbit.ket (flipThClean
    wThCore d (Function.update γ wThCore b))) = OctahedralOrbit.ket
    (Function.update γ wThCore 0) + OctahedralOrbit.ket (Function.update γ wThCore 1) := by
  unfold flipThClean flipTh
  by_cases hd : d (Function.update (Function.update γ wThCore b) wThCore 0) = true
  · rw [MergedVepCoreSliceClosure.msc_ite_pos hd, Function.update_self, Function.update_idem]
    exact one_add_uXThCore_mulVec_ket_update γ (b + 1)
  · rw [MergedVepCoreSliceClosure.msc_ite_neg hd]
    exact one_add_uXThCore_mulVec_ket_update γ b

theorem one_add_uXThCore_mul_uPosPhaseMod4_eq (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    ((1 : Operator (2 ^ posCoreWires)) + uXThCore.1) *
    (uPosPhaseMod4 slot2SwappedTo0 tailSign tailMag30).1 *
    ((1 : Operator (2 ^ posCoreWires)) + uXThCore.1) =
    ((1 : Operator (2 ^ posCoreWires)) + uXThCore.1) *
    (uPosPhaseRealMod4 slot2SwappedTo0 tailSign tailMag30).1 *
    ((1 : Operator (2 ^ posCoreWires)) + uXThCore.1) := by
  apply matrix_ext_of_ket_core
  intro γ
  have hket : MeasureBranchHadamardSem.ket γ = OctahedralOrbit.ket γ := rfl
  rw [hket]
  let γ₀ := Function.update γ wThCore 0
  let γ₁ := Function.update γ wThCore 1
  have hketBch : ∀ β : BitAssignment posCoreWires,
      (uPosPhaseRealMod4 slot2SwappedTo0 tailSign tailMag30).1.mulVec (OctahedralOrbit.ket β)
      = (if posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30 β then (-1 : ℂ) else 1) •
      OctahedralOrbit.ket β := fun β ↦ PosSlots24BranchConcrete.ket_diagonalSignUnitaryN _ β
  rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, one_add_uXThCore_mulVec_ket γ, Matrix.mulVec_add,
      Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add]
  rw [hketBch γ₀, hketBch γ₁]
  dsimp only [uPosPhaseMod4]
  rw[ket_monomialZ8UnitaryN, ket_monomialZ8UnitaryN, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul,
      one_add_uXThCore_mulVec_ket_flipThClean γ headEnBoolSpec 0,
      one_add_uXThCore_mulVec_ket_flipThClean γ headEnBoolSpec 1,
      one_add_uXThCore_mulVec_ket_update γ 0, one_add_uXThCore_mulVec_ket_update γ 1,
      ← add_smul, ← add_smul]
  refine congrArg (· • (OctahedralOrbit.ket γ₀ + OctahedralOrbit.ket γ₁)) ?_
  exact posPhaseMod4Z8_pair_sum_eq_posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30 γ

-- Non-Mod-4 coherent system operators parameterized by `tM`
/-- Core-conjugated position phase unitary parameterized by `tM`. -/
noncomputable def pos24ConjCore80Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration) : Unitary (2 ^ (fullSysCoreWires 80))
    := unitaryConj (mulUnitaryPow2 (fullSysQftCoreUnitary pos24_6_le_80 qft)
    (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg) pos24_core80_eq_twist80)
    (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhase true pos24TailSign tM))

noncomputable abbrev sysBlock80Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (s0 : Bool) (p80 : BitAssignment 80) : Operator (2 ^ systemQubits) :=
  sysBlockAtPayloadGen pos24_coreWires80_eq.symm (pos24ConjCore80Of tM qft cfg).1 s0 p80

/-- Coherent system operator on payload distribution `mu` parameterized by `tM`. -/
noncomputable def coherentSysOp80Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (s0 : Bool) (mu : BitAssignment 80 → ℝ) : Operator (2 ^ systemQubits) :=
  ∑ p80 : BitAssignment 80, (mu p80 : ℂ) • sysBlock80Of tM qft cfg s0 p80

/-- Ideal raw Slot-2 operator parameterized by `tM`. -/
noncomputable def tierBB2RawIdOf (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : Operator (2 ^ systemQubits) :=
  coherentSysOp80Of tM tierBQftFull cfg false (pos80IdealDist false)

/-- Ideal merged Slot-2 + V_ep operator parameterized by `tM`. -/
noncomputable def tierBB2IdOf (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : Operator (2 ^ systemQubits) :=
  mergedPosSlot2BUnitTwosGen ((108 : ℝ) / 109) (tierBB2RawIdOf tM) cfg

/-- Ideal Slot-4 operator parameterized by `tM`. -/
noncomputable def tierBB4IdOf (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : Operator (2 ^ systemQubits) :=
  coherentSysOp80Of tM tierBQftFull cfg true (pos80IdealDist true)

/-- Core-conjugated Mod-4 real position phase unitary parameterized by `tM`. -/
noncomputable def pos24ConjCore80Mod4Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration) : Unitary (2 ^ (fullSysCoreWires 80))
    := unitaryConj (mulUnitaryPow2 (fullSysQftCoreUnitary pos24_6_le_80 qft)
    (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg) pos24_core80_eq_twist80)
    (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhaseRealMod4 true pos24TailSign tM))

noncomputable abbrev sysBlock80Mod4Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (s0 : Bool) (p80 : BitAssignment 80) : Operator (2 ^ systemQubits) :=
  sysBlockAtPayloadGen pos24_coreWires80_eq.symm (pos24ConjCore80Mod4Of tM qft cfg).1 s0 p80

/-- Coherent Mod-4 system operator on payload distribution `mu` parameterized by `tM`. -/
noncomputable def coherentSysOp80Mod4Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (s0 : Bool) (mu : BitAssignment 80 → ℝ) : Operator (2 ^ systemQubits) :=
  ∑ p80 : BitAssignment 80, (mu p80 : ℂ) • sysBlock80Mod4Of tM qft cfg s0 p80

noncomputable abbrev mergedCoherentOp80Mod4Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (mu : BitAssignment 80 → ℝ) : Operator (2 ^ systemQubits) :=
  mergedCoherentOpGen (fun c' p' ↦ sysBlock80Mod4Of tM qft c' false p') cfg mu

/-- Ideal Mod-4 raw Slot-2 operator parameterized by `tM`. -/
noncomputable def tierBB2RawIdMod4Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : Operator (2 ^ systemQubits) :=
  coherentSysOp80Mod4Of tM tierBQftFull cfg false (pos80IdealDist false)

/-- Ideal Mod-4 merged Slot-2 + V_ep operator parameterized by `tM`. -/
noncomputable def tierBB2IdMod4Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : Operator (2 ^ systemQubits) :=
  mergedPosSlot2BUnitTwosGen ((108 : ℝ) / 109) (tierBB2RawIdMod4Of tM) cfg

/-- Ideal Mod-4 Slot-4 operator parameterized by `tM`. -/
noncomputable def tierBB4IdMod4Of (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : Operator (2 ^ systemQubits) :=
  coherentSysOp80Mod4Of tM tierBQftFull cfg true (pos80IdealDist true)

noncomputable abbrev tierBB2RawIdMod4 : Configuration → Operator (2 ^ systemQubits) :=
  tierBB2RawIdMod4Of pos24TailMag30

noncomputable abbrev tierBB2IdMod4 : Configuration → Operator (2 ^ systemQubits) :=
  tierBB2IdMod4Of pos24TailMag30

noncomputable abbrev tierBB4IdMod4 : Configuration → Operator (2 ^ systemQubits) :=
  tierBB4IdMod4Of pos24TailMag30

-- ============================================================================
-- Section 4: Top-Coin Collapse (Mod-4 & Non-Mod-4, Generic & Fermionic)
-- ============================================================================

abbrev idxTh80 : Fin 80 := ⟨31, by decide⟩
abbrev wTh86 : Wire 86 := ⟨37, by decide⟩

theorem posPhaseBitMod4_eq_of_coin0
    (tS : Fin orbitCount47905 → Bool) (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ1 γ2 : BitAssignment posCoreWires)
    (hw2_1 : γ1 (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0)
    (hw1_1 : γ1 (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0)
    (hw0_1 : γ1 (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0)
    (hw2_2 : γ2 (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0)
    (hw1_2 : γ2 (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0)
    (hw0_2 : γ2 (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0)
    (hnuc1 : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx (QRegExt.ofFin
      posCoreWires)) γ1 < 216)
    (hnuc2 : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx (QRegExt.ofFin
      posCoreWires)) γ2 < 216)
    (hwRej : γ1 (wSubReject (QRegExt.ofFin posCoreWires)) =
      γ2 (wSubReject (QRegExt.ofFin posCoreWires)))
    (hwIsH : γ1 (wIsHead (QRegExt.ofFin posCoreWires)) =
      γ2 (wIsHead (QRegExt.ofFin posCoreWires)))
    (hwThr : γ1 (wHeadThresh (QRegExt.ofFin posCoreWires)) =
      γ2 (wHeadThresh (QRegExt.ofFin posCoreWires)))
    (hwRejZ : γ1 (wRejectZero (QRegExt.ofFin posCoreWires)) =
      γ2 (wRejectZero (QRegExt.ofFin posCoreWires)))
    (hanc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx (QRegExt.ofFin
      posCoreWires)) γ1 =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx (QRegExt.ofFin
        posCoreWires)) γ2)
    (hhead21 : fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) γ1 =
      fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) γ2)
    (hkeep30 : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30
      (QRegExt.ofFin posCoreWires)) γ1 =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 (QRegExt.ofFin
        posCoreWires)) γ2)
    (hpar1 : parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) γ1 =
      parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) γ2)
    (hslot : ∀ e : Fin 218,
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) γ1 =
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) γ2) :
    posPhaseBitMod4 true tS tM γ1 = posPhaseBitMod4 true tS tM γ2 := by
  have hEn : headEnBoolSpec γ1 = headEnBoolSpec γ2 := by
    unfold headEnBoolSpec; dsimp only
    simp only [hw2_1, hw1_1, hw0_1, hw2_2, hw1_2, hw0_2,
      beq_self_eq_true, show ((0 : ZMod 2) == 1) = false by decide,
      Bool.not_false, Bool.true_and, imp_true_iff, hnuc1, hnuc2, decide_true,
      hwRej, hwIsH, hanc]
  have hHit : headHitSetSpec γ1 = headHitSetSpec γ2 := by
    unfold headHitSetSpec; dsimp only
    simp only [hw0_1, hw0_2, show ((0 : ZMod 2) == 1) = false by decide,
      Bool.not_false, ↓reduceIte, Bool.true_or, hhead21, hslot]
  have hHead : headPhaseBitMod4Spec γ1 = headPhaseBitMod4Spec γ2 := by
    unfold headPhaseBitMod4Spec; dsimp only; rw [hEn, hHit, hw0_1, hw0_2, hwThr]
  have hTail : tailAndSlackPhaseBitSpec true tS tM γ1 =
      tailAndSlackPhaseBitSpec true tS tM γ2 := by
    rw [MergedVepTopCoinCollapse.tailAndSlackPhaseBitSpec_eq_orbitBody true tS tM γ1,
      MergedVepTopCoinCollapse.tailAndSlackPhaseBitSpec_eq_orbitBody true tS tM γ2]
    dsimp only
    simp only [hw2_1, hw1_1, hw0_1, hw2_2, hw1_2, hw0_2,
      show ((0 : ZMod 2) == 1) = false by decide, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.false_and, false_implies, imp_true_iff, hnuc1, hnuc2, decide_true, Bool.and_true,
      hwRej, hwIsH, hwRejZ, hanc, hslot 0, hpar1, hkeep30]
  unfold posPhaseBitMod4; rw [hHead, hTail]

theorem msc_posPhaseBitMod4_eq_of_coin1
    (tS : Fin orbitCount47905 → Bool) (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (β₁ β₂ : BitAssignment posCoreWires)
    (hs0_1 : β₁ (wSlot0Core (QRegExt.ofFin posCoreWires)) = 1)
    (hs0_2 : β₂ (wSlot0Core (QRegExt.ofFin posCoreWires)) = 1)
    (hw1 : β₁ (wSlot1Core (QRegExt.ofFin posCoreWires)) =
      β₂ (wSlot1Core (QRegExt.ofFin posCoreWires)))
    (hw2 : β₁ (wSlot2Core (QRegExt.ofFin posCoreWires)) =
      β₂ (wSlot2Core (QRegExt.ofFin posCoreWires)))
    (hwsub : β₁ (wSubReject (QRegExt.ofFin posCoreWires)) =
      β₂ (wSubReject (QRegExt.ofFin posCoreWires)))
    (hwhd : β₁ (wIsHead (QRegExt.ofFin posCoreWires)) =
      β₂ (wIsHead (QRegExt.ofFin posCoreWires)))
    (hwth : β₁ (wHeadThresh (QRegExt.ofFin posCoreWires)) =
      β₂ (wHeadThresh (QRegExt.ofFin posCoreWires)))
    (hwrz : β₁ (wRejectZero (QRegExt.ofFin posCoreWires)) =
      β₂ (wRejectZero (QRegExt.ofFin posCoreWires)))
    (hanc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx (QRegExt.ofFin
      posCoreWires)) β₁ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx (QRegExt.ofFin
        posCoreWires)) β₂)
    (hpart : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx
      (QRegExt.ofFin posCoreWires)) β₁ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx (QRegExt.ofFin
        posCoreWires)) β₂)
    (hkeep : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30
      (QRegExt.ofFin posCoreWires)) β₁ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 (QRegExt.ofFin
        posCoreWires)) β₂)
    (hf21 : fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₁ =
      fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₂)
    (hpar0 : parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β₁ =
      parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β₂)
    (hpar1 : parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) β₁ =
      parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) β₂)
    (hslot : ∀ e : Fin 218,
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β₁ =
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β₂) :
    posPhaseBitMod4 true tS tM β₁ = posPhaseBitMod4 true tS tM β₂ := by
  have hEn : headEnBoolSpec β₁ = headEnBoolSpec β₂ := by
    unfold headEnBoolSpec; dsimp only
    simp only [hs0_1, hs0_2, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
      false_implies, decide_true, Bool.true_and, hw1, hw2, hwsub, hwhd, hanc]
  have hHit : headHitSetSpec β₁ = headHitSetSpec β₂ := by
    unfold headHitSetSpec; dsimp only
    simp only [hs0_1, hs0_2, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Bool.false_or, hf21, hpar0, hslot]
  have hhead : headPhaseBitMod4Spec β₁ = headPhaseBitMod4Spec β₂ := by
    unfold headPhaseBitMod4Spec; dsimp only; rw [hEn, hHit, hs0_1, hs0_2, hwth]
  have htail : tailAndSlackPhaseBitSpec true tS tM β₁ =
      tailAndSlackPhaseBitSpec true tS tM β₂ := by
    rw [MergedVepTopCoinCollapse.tailAndSlackPhaseBitSpec_eq_orbitBody true tS tM β₁,
      MergedVepTopCoinCollapse.tailAndSlackPhaseBitSpec_eq_orbitBody true tS tM β₂]
    simp only [hs0_1, hs0_2, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      false_implies, decide_true, Bool.true_and,
      hw1, hw2, hwsub, hwhd, hwrz, hanc, hpart, hkeep, hpar0, hpar1, hslot]
  unfold posPhaseBitMod4; rw [hhead, htail]

noncomputable abbrev pos24ConjCore80Raw (U_raw : Unitary (2 ^ posCoreWires))
    (qft : FullSysQft654Bundle) (cfg : Configuration) : Unitary (2 ^ (fullSysCoreWires 80))
    := unitaryConj (mulUnitaryPow2 (fullSysQftCoreUnitary pos24_6_le_80 qft)
    (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg) pos24_core80_eq_twist80)
    (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw)

noncomputable abbrev sysBlock80Raw (U_raw : Unitary (2 ^ posCoreWires))
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (s0 : Bool) (p80 : BitAssignment 80) : Operator (2 ^ systemQubits) :=
  sysBlockAtPayloadGen pos24_coreWires80_eq.symm (pos24ConjCore80Raw U_raw qft cfg).1 s0 p80

section HpowStep_1
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_1 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem castRaw_eq_diagonal (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool) (hRawKet : ∀ η : BitAssignment (fullSysCoreWires
    80), (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) = (if φ η then (-1
    : ℂ) else 1) • ket η) : (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 =
    Matrix.diagonal (fun u : Fin (2 ^ posCoreWires) ↦ if φ (basisBits posCoreWires u) then (-1
    : ℂ) else 1) := by
  apply matrix_ext_of_ket_core
  intro β
  rw [hRawKet β, msc_diagonal_mulVec_ket (fun γ ↦ if φ γ then (-1 : ℂ) else 1) β]

end HpowStep_1
section HpowStep_2
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_2 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem castRaw_comm_diagonal (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool) (hRawKet : ∀ η : BitAssignment (fullSysCoreWires
    80), (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) = (if φ η then (-1
    : ℂ) else 1) • ket η) (d : Fin (2 ^ (fullSysCoreWires 80)) → ℂ) :
    (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 * Matrix.diagonal d = Matrix.diagonal
    d * (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 := by
  rw [castRaw_eq_diagonal U_raw φ hRawKet]
  exact PosSlots24SemanticOracleConcrete80.diagonal_comm_diagonal _ _

end HpowStep_2
theorem conjSwapCore3967_raw_hUPosKet (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool)
    (hRawKet : ∀ η : BitAssignment (fullSysCoreWires 80),
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) =
        (if φ η then (-1 : ℂ) else 1) • ket η)
    (β : BitAssignment (fullSysCoreWires 80)) :
    (conjSwapCore3967 (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw)).1.mulVec (ket β) =
      (if φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) ⟨12, by decide⟩ β)
        then (-1 : ℂ) else 1) • ket β := by
  unfold conjSwapCore3967
  rw[Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, uSwapCore3967_mulVec_ket, hRawKet (swapCore3967Fn β),
      Matrix.mulVec_smul, uSwapCore3967_mulVec_ket, swapCore3967Fn_involutive,
      swapCore3967Fn_eq_swapCoreScrGenFn12]

section HpowStep_3
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_3 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem sysBlock80Raw_projDiag (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool) (hRawKet : ∀ η : BitAssignment (fullSysCoreWires
    80), (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) = (if φ η then (-1
    : ℂ) else 1) • ket η) (qft : FullSysQft654Bundle) (cfg : Configuration) (s0 : Bool)
    (p : BitAssignment 80) (x' x : Fin (2 ^ systemQubits))
    (hne : mProj24_sp.extractIndex x' ≠ mProj24_sp.extractIndex x) : sysBlock80Raw U_raw qft
    cfg s0 p x' x = 0 := by
  let M_gen := (pos24ConjCore80Raw U_raw qft cfg).1
  let rProjC : QRegister 24 (fullSysCoreWires 80) := QRegister.block 3924 24 (by
    dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]; omega)
  have hCommAll : ∀ a : Fin (2 ^ 24),
      M_gen * rProjC.basisOutcomeProjector a =
        rProjC.basisOutcomeProjector a * M_gen := fun a ↦ by
    let P := rProjC.basisOutcomeProjector a
    have hP_sa : Pᴴ = P := QRegister.basisOutcomeProjector_conjTranspose _ _
    have hDisjQ : (coreElecCosetB1Block pos24_6_le_80).DisjointWires rProjC := by
      rw [QRegister.disjoint_iff]
      intro idx j h
      refine msc_wire_not_in_elecCosetB1 pos24_6_le_80 (rProjC j) (Or.inl ?_) ⟨idx, h⟩
      have := j.isLt
      dsimp [rProjC, MergedVepCoreSliceClosureAlt.qreg_block_apply]
      omega
    have hQftP : (fullSysQftCoreUnitary pos24_6_le_80 qft).1 * P =
        P * (fullSysQftCoreUnitary pos24_6_le_80 qft).1 :=
      QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
        (coreElecCosetB1Block pos24_6_le_80) rProjC hDisjQ qft.uQft654.1 a
    let rProjTw : QRegister 24 (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) :=
      QRegister.block 3924 24 (by
        dsimp [NuclearTwistAndXor654Concrete.fullSysCoreWires,
          systemQubits, numElectrons, electronBits, projectileBits]; omega)
    have hDisjTw : (NuclearTwistAndXor654Concrete.rElecCore (QRegExt.ofFin
        (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))).DisjointWires rProjTw := by
      rw [QRegister.disjoint_iff]
      intro i j hij
      have hv := congrArg Fin.val hij
      have hi := i.isLt; have hj := j.isLt
      dsimp [NuclearTwistAndXor654Concrete.rElecCore, rProjTw, QRegister.slice,
        QRegister.slice_apply,
        MergedVepCoreSliceClosureAlt.qreg_slice_wires,
        MergedVepCoreSliceClosureAlt.qreg_whole_wires,
        MergedVepCoreSliceClosureAlt.emb_trans_apply,
        MergedVepCoreSliceClosureAlt.emb_refl_apply,
        MergedVepCoreSliceClosureAlt.emb_mk_apply,
        MergedVepCoreSliceClosureAlt.qreg_block_apply,
        MergedVepCoreSliceClosureAlt.qreg_block_wires_apply,
        QRegister.compose, QRegister.compose_apply,
        MergedVepCoreSliceClosureAlt.qreg_compose_wires,
        QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits] at hv hi hj
      omega
    have hTwP : (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg).1 * P =
        P * (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg).1 := by
      have hcomm := NuclearTwistRealizes.uTwistParam_comm_highReg_proj true pos24_22_le_80 cfg
        (QRegExt.ofFin (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)) rProjTw hDisjTw a
      rwa [PosSlots24SemanticOracleConcrete80.ofFin_embedUnitary_eq] at hcomm
    have hPhP : (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 * P =
        P * (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 := by
      change _ * rProjC.basisOutcomeProjector a = rProjC.basisOutcomeProjector a * _
      rw [QRegister.basisOutcomeProjector_eq_diagonal]
      exact castRaw_comm_diagonal U_raw φ hRawKet _
    have hConjEq : M_gen = ((fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
        (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg).1)ᴴ *
        (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 * ((fullSysQftCoreUnitary
        pos24_6_le_80 qft).1 * (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg).1)
        := rfl
    rw [hConjEq]
    exact MergedVepTopCoinCollapse.conj_comm_of_parts_comm
      (fullSysQftCoreUnitary pos24_6_le_80 qft).1
      (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg).1
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 P hP_sa hQftP hTwP hPhP
  have hExtr : ∀ z : Fin (2 ^ systemQubits),
      rProjC.extractIndex (coreIdxOf pos24_coreWires80_eq.symm s0 p z) =
        mProj24_sp.extractIndex z := fun z ↦ by
    apply (basisBitsEquiv 24).injective; funext i
    change basisBits 24 (rProjC.extractIndex (coreIdxOf pos24_coreWires80_eq.symm s0 p z)) i =
      basisBits 24 (mProj24_sp.extractIndex z) i
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      PosSlots24SemanticOracleConcrete80.coreIdxOf,
      MergedVepTopCoinCollapse.basisBits_cast_pow2 pos24_coreWires80_eq.symm]
    have hbb : basisBits posCoreWires ((basisBitsEquiv posCoreWires).symm (coreBetaOf s0 p z))
        = coreBetaOf s0 p z := (basisBitsEquiv posCoreWires).apply_symm_apply _
    rw [hbb]
    refine (congrArg (coreBetaOf s0 p z) (Fin.ext ?_)).trans
      (PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 s0 p z (mProj24_sp i))
    rfl
  rw [sysBlock80Raw, PosSlots24SemanticOracleConcrete80.sysBlockAtPayloadGen_apply]
  refine entry_zero_of_comm_basisOutcomeProjector rProjC M_gen hCommAll
    (coreIdxOf pos24_coreWires80_eq.symm s0 p x')
    (coreIdxOf pos24_coreWires80_eq.symm s0 p x) ?_
  rw [hExtr x', hExtr x]
  exact hne

end HpowStep_3
private theorem slotSubGridCoord64_eq_of_lt3924 (β₁ β₂ : BitAssignment posCoreWires)
    (h : ∀ q : Wire posCoreWires, q.val < 3924 → β₁ q = β₂ q) (e : Fin 218) :
    slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β₁ =
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β₂ := by
  funext w
  apply Fin.ext
  dsimp [slotSubGridCoord64]
  refine regVal_eq_of_wire_eq _ β₁ β₂ fun i ↦ h _ ?_
  have := e.isLt
  have := w.isLt
  have := i.isLt
  have hval : (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w i).val =
      18 * e.val + (6 * w.val + (5 - i.val)) := rfl
  omega

private theorem fineCoordOfReg21_head_eq_of_wire_eq (β₁ β₂ : BitAssignment posCoreWires)
    (h : ∀ w : Fin 3, ∀ i : Fin 7,
      β₁ (((rHeadFine21 (QRegExt.ofFin posCoreWires)).slice (7 * w.val) 7
          (by have := w.isLt; omega)) i) =
        β₂ (((rHeadFine21 (QRegExt.ofFin posCoreWires)).slice (7 * w.val) 7
          (by have := w.isLt; omega)) i)) :
    fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₁ =
      fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₂ := by
  funext w
  apply Fin.ext
  dsimp [fineCoordOfReg21]
  exact regVal_eq_of_wire_eq _ β₁ β₂ (h w)

private theorem parity3OfReg_eq_of_wire_eq (r : QRegister 3 posCoreWires)
    (β₁ β₂ : BitAssignment posCoreWires) (h : ∀ w : Fin 3, β₁ (r w) = β₂ (r w)) :
    parity3OfReg r β₁ = parity3OfReg r β₂ :=
  funext fun w ↦ congrArg (fun b ↦ decide (b = 1)) (h w)

private theorem swapCoreScrGenFn_eq_of_ne (jScr : Fin 16) (γ : BitAssignment posCoreWires)
    (q : Wire posCoreWires) (h1 : q.val ≠ 3967) (h2 : ¬(4017 ≤ q.val ∧ q.val < 4033)) :
    swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr γ q = γ q := by
  let qF : Wire (fullSysCoreWires 80) := ⟨q.val, q.isLt⟩
  have hne1 : qF ≠ mWCore3967Gen (le_rfl : 80 ≤ 80) := fun h ↦ h1 (congrArg Fin.val h)
  have hne2 : qF ≠ mWCoreScrGen (le_rfl : 80 ≤ 80) jScr := by
    intro h
    apply h2
    have hv := congrArg Fin.val h
    dsimp [qF, mWCoreScrGen] at hv
    have := jScr.isLt
    omega
  exact congrArg γ (Equiv.swap_apply_of_ne_of_ne hne1 hne2)

theorem msc_phaseBit_swap_coin1_gen
    (φ : BitAssignment posCoreWires → Bool)
    (hEq1 : ∀ (β₁ β₂ : BitAssignment posCoreWires),
      β₁ (wSlot0Core (QRegExt.ofFin posCoreWires)) = 1 →
      β₂ (wSlot0Core (QRegExt.ofFin posCoreWires)) = 1 →
      β₁ (wSlot1Core (QRegExt.ofFin posCoreWires)) =
        β₂ (wSlot1Core (QRegExt.ofFin posCoreWires)) →
      β₁ (wSlot2Core (QRegExt.ofFin posCoreWires)) =
        β₂ (wSlot2Core (QRegExt.ofFin posCoreWires)) →
      β₁ (wSubReject (QRegExt.ofFin posCoreWires)) =
        β₂ (wSubReject (QRegExt.ofFin posCoreWires)) →
      β₁ (wIsHead (QRegExt.ofFin posCoreWires)) =
        β₂ (wIsHead (QRegExt.ofFin posCoreWires)) →
      β₁ (wHeadThresh (QRegExt.ofFin posCoreWires)) =
        β₂ (wHeadThresh (QRegExt.ofFin posCoreWires)) →
      β₁ (wRejectZero (QRegExt.ofFin posCoreWires)) =
        β₂ (wRejectZero (QRegExt.ofFin posCoreWires)) →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx (QRegExt.ofFin
        posCoreWires)) β₁ =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx (QRegExt.ofFin
          posCoreWires)) β₂ →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx (QRegExt.ofFin
        posCoreWires)) β₁ =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx (QRegExt.ofFin
          posCoreWires)) β₂ →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 (QRegExt.ofFin
        posCoreWires)) β₁ =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 (QRegExt.ofFin
          posCoreWires)) β₂ →
      fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₁ =
        fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₂ →
      parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β₁ =
        parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β₂ →
      parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) β₁ =
        parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) β₂ →
      (∀ e : Fin 218,
        slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β₁ =
        slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β₂) →
      φ β₁ = φ β₂)
    (jScr : Fin 16) (γ : BitAssignment posCoreWires)
    (hs0 : γ (wSlot0Core (QRegExt.ofFin posCoreWires)) = 1) :
    φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr γ) = φ γ := by
  let β₁ : BitAssignment posCoreWires := swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr γ
  have heq := swapCoreScrGenFn_eq_of_ne jScr γ
  let rC := QRegExt.ofFin posCoreWires
  exact hEq1 β₁ γ ((heq _ (by decide) (by decide)).trans hs0) hs0
    (heq ⟨3949, by decide⟩ (by decide) (by decide))
    (heq ⟨3950, by decide⟩ (by decide) (by decide))
    (heq ⟨3954 + 62, by decide⟩ (by decide) (by decide))
    (heq ⟨3954 + 30, by decide⟩ (by decide) (by decide))
    (heq ⟨3954 + 31, by decide⟩ (by decide) (by decide))
    (heq ⟨3954 + 79, by decide⟩ (by decide) (by decide))
    (regVal_eq_of_wire_eq (rAnchorIdx rC) β₁ γ fun i ↦
      heq _ (by revert i; decide) (by revert i; decide))
    (regVal_eq_of_wire_eq (rPartnerIdx rC) β₁ γ fun i ↦
      heq _ (by revert i; decide) (by revert i; decide))
    (regVal_eq_of_wire_eq (rTailKeep30 rC) β₁ γ fun i ↦
      heq _ (by revert i; decide) (by revert i; decide))
    (fineCoordOfReg21_head_eq_of_wire_eq β₁ γ fun w i ↦
      heq _ (by revert w i; decide) (by revert w i; decide))
    (parity3OfReg_eq_of_wire_eq (rCosetB0 rC) β₁ γ fun w ↦
      heq _ (by revert w; decide) (by revert w; decide))
    (parity3OfReg_eq_of_wire_eq (rCosetB1 rC) β₁ γ fun w ↦
      heq _ (by revert w; decide) (by revert w; decide))
    (slotSubGridCoord64_eq_of_lt3924 β₁ γ fun q hq ↦ heq q (by omega) (by omega))

theorem msc_phaseBit_swap_coin0_gen
    (φ : BitAssignment posCoreWires → Bool)
    (hEq0 : ∀ (γ1 γ2 : BitAssignment posCoreWires),
      γ1 (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ1 (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ1 (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ2 (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ2 (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ2 (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0 →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx (QRegExt.ofFin
        posCoreWires)) γ1 < 216 →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx (QRegExt.ofFin
        posCoreWires)) γ2 < 216 →
      γ1 (wSubReject (QRegExt.ofFin posCoreWires)) =
        γ2 (wSubReject (QRegExt.ofFin posCoreWires)) →
      γ1 (wIsHead (QRegExt.ofFin posCoreWires)) =
        γ2 (wIsHead (QRegExt.ofFin posCoreWires)) →
      γ1 (wHeadThresh (QRegExt.ofFin posCoreWires)) =
        γ2 (wHeadThresh (QRegExt.ofFin posCoreWires)) →
      γ1 (wRejectZero (QRegExt.ofFin posCoreWires)) =
        γ2 (wRejectZero (QRegExt.ofFin posCoreWires)) →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx (QRegExt.ofFin
        posCoreWires)) γ1 =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx (QRegExt.ofFin
          posCoreWires)) γ2 →
      fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) γ1 =
        fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) γ2 →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 (QRegExt.ofFin
        posCoreWires)) γ1 =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 (QRegExt.ofFin
          posCoreWires)) γ2 →
      parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) γ1 =
        parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) γ2 →
      (∀ e : Fin 218,
        slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) γ1 =
        slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) γ2) →
      φ γ1 = φ γ2)
    (jScr : Fin 16) (γ_act γ_ref : BitAssignment posCoreWires)
    (hScr0 : γ_act (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0)
    (hOut : ∀ q : Wire posCoreWires,
      ¬(3960 ≤ q.val ∧ q.val < 3968) → ¬(4017 ≤ q.val ∧ q.val < 4033) → γ_act q = γ_ref q)
    (hw2_0 : γ_ref (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0)
    (hw1_0 : γ_ref (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0)
    (hw0_0 : γ_ref (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0)
    (hnuc0 : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx (QRegExt.ofFin
      posCoreWires)) γ_ref < 216) :
    φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr γ_act) = φ γ_ref := by
  let γ1 : BitAssignment posCoreWires := swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr γ_act
  have h1Eq : ∀ q : Wire posCoreWires,
      ¬(3960 ≤ q.val ∧ q.val < 3968) → ¬(4017 ≤ q.val ∧ q.val < 4033) → γ1 q = γ_ref q :=
    fun q hN hS ↦ (swapCoreScrGenFn_eq_of_ne jScr γ_act q (by omega) hS).trans (hOut q hN hS)
  let rC := QRegExt.ofFin posCoreWires
  have hnuc1 : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rC) γ1 < 216 :=
    by
    let rN0 := rNucIdx rC
    have hbit7 : γ1 (rN0 7) = 0 := by
      have hwEq : (rN0 7 : Wire (fullSysCoreWires 80)) = mWCore3967Gen (le_rfl : 80 ≤ 80) := rfl
      change γ_act (Equiv.swap (mWCore3967Gen (le_rfl : 80 ≤ 80))
        (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) _) = 0
      rw [hwEq, Equiv.swap_apply_left]
      exact hScr0
    have hlt7 :=
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal_lt_two_pow (fun i : Fin 7 ↦
      γ1 (rN0 i.castSucc))
    unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal at hlt7 ⊢
    dsimp only [rN0] at hbit7
    rw [Fin.sum_univ_castSucc]
    dsimp only
    rw [show (Fin.last 7 : Fin 8) = 7 from rfl, hbit7, ZMod.val_zero, zero_mul, add_zero]
    exact lt_trans hlt7 (by decide)
  exact hEq0 γ1 γ_ref
    ((h1Eq _ (by decide) (by decide)).trans hw2_0)
    ((h1Eq _ (by decide) (by decide)).trans hw1_0)
    ((h1Eq _ (by decide) (by decide)).trans hw0_0)
    hw2_0 hw1_0 hw0_0 hnuc1 hnuc0
    (h1Eq ⟨3954 + 62, by decide⟩ (by decide) (by decide))
    (h1Eq ⟨3954 + 30, by decide⟩ (by decide) (by decide))
    (h1Eq ⟨3954 + 31, by decide⟩ (by decide) (by decide))
    (h1Eq ⟨3954 + 79, by decide⟩ (by decide) (by decide))
    (regVal_eq_of_wire_eq (rAnchorIdx rC) γ1 γ_ref fun i ↦
      h1Eq _ (by revert i; decide) (by revert i; decide))
    (fineCoordOfReg21_head_eq_of_wire_eq γ1 γ_ref fun w i ↦
      h1Eq _ (by revert w i; decide) (by revert w i; decide))
    (regVal_eq_of_wire_eq (rTailKeep30 rC) γ1 γ_ref fun i ↦
      h1Eq _ (by revert i; decide) (by revert i; decide))
    (parity3OfReg_eq_of_wire_eq (rCosetB1 rC) γ1 γ_ref fun w ↦
      h1Eq _ (by revert w; decide) (by revert w; decide))
    (slotSubGridCoord64_eq_of_lt3924 γ1 γ_ref fun q hq ↦ h1Eq q (by omega) (by omega))

theorem msc_sysBlock80Raw_eq_conj (U_raw : Unitary (2 ^ posCoreWires))
    (qft : FullSysQft654Bundle) (cfg : Configuration) (s0 : Bool) (p : BitAssignment 80)
    (x' x : Fin (2 ^ systemQubits)) : sysBlock80Raw U_raw qft cfg s0 p x' x =
    ((fullSysQftCoreUnitary pos24_6_le_80 qft * mscUTwistParam true pos24_22_le_80 cfg).1ᴴ *
    (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 * (fullSysQftCoreUnitary
    pos24_6_le_80 qft * mscUTwistParam true pos24_22_le_80 cfg).1)
    ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta s0 p x'))
    ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta s0 p x)) := by
  have hIdx : ∀ z : Fin (2 ^ systemQubits), coreIdxOf pos24_coreWires80_eq.symm s0 p z =
      (basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta s0 p z) := fun z ↦
      msc_cast_basisBits_symm pos24_coreWires80_eq.symm (coreBetaOf s0 p z)
  rw [sysBlock80Raw, PosSlots24SemanticOracleConcrete80.sysBlockAtPayloadGen_apply,
    hIdx x', hIdx x, pos24ConjCore80Raw, unitaryConj_val,
    msc_mulUnitaryPow2_qft_twist pos24_6_le_80 pos24_22_le_80 qft cfg pos24_core80_eq_twist80]

theorem msc_upos_eq_diagonal_gen (φ : BitAssignment posCoreWires → Bool) (jScr : Fin 16)
    (U_ph : Unitary (2 ^ (fullSysCoreWires 80))) (hUPosKet : ∀ β : BitAssignment
    (fullSysCoreWires 80), U_ph.1.mulVec (ket β) = (if φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80)
    jScr β) then (-1 : ℂ) else 1) • ket β) : U_ph.1 = Matrix.diagonal (fun u ↦ if φ
    (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr (basisBits (fullSysCoreWires 80) u)) then (-1 :
    ℂ) else 1) := by
  apply matrix_ext_of_ket_core
  intro β
  rw [hUPosKet β, msc_diagonal_mulVec_ket
    (fun γ ↦ if φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr γ) then (-1 : ℂ) else 1) β]

theorem msc_mergedCore_comm_rAncFlag80_gen (φ : BitAssignment posCoreWires → Bool)
    (qft : FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft) (cfg : Configuration)
    (jScr : Fin 16) (U_ph : Unitary (2 ^ (fullSysCoreWires 80))) (hUPosKet : ∀ β :
    BitAssignment (fullSysCoreWires 80), U_ph.1.mulVec (ket β) = (if φ (swapCoreScrGenFn
    (le_rfl : 80 ≤ 80) jScr β) then (-1 : ℂ) else 1) • ket β) (a : Fin (2 ^ 86)) :
    (unitaryConj (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80))
    qft * mscUVepTwistRef pos24_22_le_80 cfg) U_ph).1 * rAncFlag80.basisOutcomeProjector a =
    rAncFlag80.basisOutcomeProjector a * (unitaryConj (fullSysQftCoreUnitary (le_trans
    (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft * mscUVepTwistRef pos24_22_le_80 cfg) U_ph).1
    := by
  have hPhP : U_ph.1 * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * U_ph.1 := by
    rw [msc_upos_eq_diagonal_gen φ jScr U_ph hUPosKet,
      QRegister.basisOutcomeProjector_eq_diagonal]
    exact PosSlots24SemanticOracleConcrete80.diagonal_comm_diagonal _ _
  rw [unitaryConj_val, Submonoid.coe_mul]
  exact MergedVepTopCoinCollapse.conj_comm_of_parts_comm (fullSysQftCoreUnitary (le_trans
    (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft).1 (mscUVepTwistRef pos24_22_le_80 cfg).1
    U_ph.1 (rAncFlag80.basisOutcomeProjector a)
    (QRegister.basisOutcomeProjector_conjTranspose _ _) (msc_qft_comm_rAncFlag80 qft hQft a)
    (msc_uVepTwistRef_comm_rAncFlag80 cfg a) hPhP

theorem msc_coreIdx_entry_gen (φ : BitAssignment posCoreWires → Bool)
    (qft : FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft) (cfg : Configuration)
    (jScr : Fin 16) (U_ph : Unitary (2 ^ (fullSysCoreWires 80))) (hUPosKet : ∀ β :
    BitAssignment (fullSysCoreWires 80), U_ph.1.mulVec (ket β) = (if φ (swapCoreScrGenFn
    (le_rfl : 80 ≤ 80) jScr β) then (-1 : ℂ) else 1) • ket β) (s0 : Bool)
    (p : BitAssignment 80) (x' x : Fin (2 ^ systemQubits)) : (coreUnitarySym (unitaryConj
    (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft *
    mscUVepTwistRef pos24_22_le_80 cfg) U_ph)).1 (coreIdxOf hkSym80 s0 p x')
    (coreIdxOf hkSym80 s0 p x) = (unitaryConj (fullSysQftCoreUnitary (le_trans
    (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft * mscUVepTwistRef pos24_22_le_80 cfg) U_ph).1
    ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta s0 p x'))
    ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta s0 p x)) :=
    msc_transport_entry_of_comm _ (msc_mergedCore_comm_rAncFlag80_gen φ qft hQft cfg jScr U_ph
    hUPosKet) s0 p x' x

theorem mergedVepCore_hBlk1_gen (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool) (hRawKet : ∀ η : BitAssignment (fullSysCoreWires
    80), (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) = (if φ η then (-1
    : ℂ) else 1) • ket η) (qft : FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft)
    (cfg : Configuration) (jScr : Fin 16) (hSwap1 : ∀ γ : BitAssignment posCoreWires, γ
    (wSlot0Core (QRegExt.ofFin posCoreWires)) = 1 → φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80)
    jScr γ) = φ γ) (U_ph : Unitary (2 ^ (fullSysCoreWires 80))) (hUPosKet : ∀ β :
    BitAssignment (fullSysCoreWires 80), U_ph.1.mulVec (ket β) = (if φ (swapCoreScrGenFn
    (le_rfl : 80 ≤ 80) jScr β) then (-1 : ℂ) else 1) • ket β) (p : BitAssignment 80)
    (x' x : Fin (2 ^ systemQubits)) : (coreUnitarySym (unitaryConj (fullSysQftCoreUnitary
    (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft * mscUVepTwistRef pos24_22_le_80
    cfg) U_ph)).1 (coreIdxOf hkSym80 true p x') (coreIdxOf hkSym80 true p x) = sysBlock80Raw
    U_raw qft cfg true p x' x := by
  rw [msc_coreIdx_entry_gen φ qft hQft cfg jScr U_ph hUPosKet true p x' x,
    msc_sysBlock80Raw_eq_conj U_raw qft cfg true p x' x, unitaryConj_val,
    msc_fullSysQft_pf_congr _ pos24_6_le_80 qft]
  let Pred1 : BitAssignment (fullSysCoreWires 80) → Prop := fun γ ↦ γ mscWSlot0 = 1
  have hHostKet : ∀ z : Fin (2 ^ systemQubits),
      (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUVepTwistRef pos24_22_le_80 cfg).1.mulVec
        (ket (mscCoreBeta true p z)) =
      (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUTwistParam true pos24_22_le_80 cfg).1.mulVec
        (ket (mscCoreBeta true p z)) := fun z ↦ by
    have hvFalse : mscVepHighNuc pos24_22_le_80 (mscCoreBeta true p z) = false := by
      by_cases hv : mscVepHighNuc pos24_22_le_80 (mscCoreBeta true p z) = true
      · exfalso
        have hc0 := ((vepHighNuc_iff pos24_22_le_80 (mscCoreBeta true p z)).mp hv).1
        have hw1 := msc_coreBetaOf_coin1_wSlot0 p z
        rw [NuclearTwistRealizes.coin0Active, decide_eq_true_eq] at hc0
        change _ ∧ _ ∧ mscCoreBeta true p z mscWSlot0 = 0 at hc0
        rw [hw1] at hc0
        exact absurd hc0.2.2 (by decide)
      · exact Bool.not_eq_true _ |>.mp hv
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      msc_uVepTwistRef_host_ket pos24_22_le_80 cfg _ hvFalse]
  have hCommU : (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUTwistParam true pos24_22_le_80
      cfg).1 * mscDiagPred Pred1 = mscDiagPred Pred1 * (fullSysQftCoreUnitary pos24_6_le_80
      qft * mscUTwistParam true pos24_22_le_80 cfg).1 := by
    have hT := msc_uTwistParam_preserves_diag_ge3924 pos24_22_le_80 cfg Pred1
      fun γ₁ γ₂ h ↦ by dsimp only [Pred1]; rw [h mscWSlot0 (by decide)]
    have hQ := msc_qft_preserves_diag_not_in_elecCosetB1 pos24_6_le_80 qft Pred1
      fun γ₁ γ₂ h ↦ by
        dsimp only [Pred1]
        rw [h mscWSlot0 (msc_wire_not_in_elecCosetB1 pos24_6_le_80 mscWSlot0 (Or.inl (by decide)))]
    rw [Submonoid.coe_mul]
    exact msc_mul2_comm _ _ (mscDiagPred Pred1) hQ hT
  have hPhEq : U_ph.1 * mscDiagPred Pred1 =
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 * mscDiagPred Pred1 := by
    apply matrix_ext_of_ket_core; intro γ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      MergedVepCoreSliceClosure.mscDiagPred_mulVec_ket Pred1 γ]
    by_cases hw : Pred1 γ
    · rw [msc_ite_pos hw, one_smul, hUPosKet γ, hRawKet γ, hSwap1 γ hw]
    · rw [msc_ite_neg hw, zero_smul, Matrix.mulVec_zero, Matrix.mulVec_zero]
  exact msc_conj_entry_eq_of_proj _ _ _ _ (mscDiagPred Pred1)
    (mscCoreBeta true p x') (mscCoreBeta true p x)
    (hHostKet x') (hHostKet x) hCommU
    (by
      rw [MergedVepCoreSliceClosure.mscDiagPred_mulVec_ket Pred1,
        msc_ite_pos (msc_coreBetaOf_coin1_wSlot0 p x), one_smul])
    hPhEq

theorem msc_hBlk0_host_gen
    (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool)
    (hRawKet : ∀ η : BitAssignment (fullSysCoreWires 80),
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) =
        (if φ η then (-1 : ℂ) else 1) • ket η)
    (qft : FullSysQft654Bundle)
    (hQft : QftPreservesCoset3 qft)
    (cfg : Configuration)
    (jScr : Fin 16)
    (hSwap0 : ∀ γ_act γ_ref : BitAssignment posCoreWires,
      γ_act (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0 →
      (∀ q : Wire posCoreWires,
        ¬(3960 ≤ q.val ∧ q.val < 3968) → ¬(4017 ≤ q.val ∧ q.val < 4033) → γ_act q = γ_ref q) →
      γ_ref (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ_ref (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ_ref (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0 →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx (QRegExt.ofFin
        posCoreWires)) γ_ref < 216 →
      φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr γ_act) = φ γ_ref)
    (U_ph : Unitary (2 ^ (fullSysCoreWires 80)))
    (hUPosKet : ∀ β : BitAssignment (fullSysCoreWires 80),
      U_ph.1.mulVec (ket β) =
        (if φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr β)
          then (-1 : ℂ) else 1) • ket β)
    (p : BitAssignment 80)
    (hpScr : p ⟨63 + jScr.val, by omega⟩ = 0)
    (hlt : p80NucVal p < 216)
    (x' x : Fin (2 ^ systemQubits)) :
    (coreUnitarySym
      (unitaryConj
        (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft *
          mscUVepTwistRef pos24_22_le_80 cfg)
        U_ph)).1
        (coreIdxOf hkSym80 false p x') (coreIdxOf hkSym80 false p x) =
      sysBlock80Raw U_raw qft cfg false p x' x := by
  rw [msc_sysBlock80Raw_eq_conj U_raw qft cfg false p x' x,
    msc_coreIdx_entry_gen φ qft hQft cfg jScr U_ph hUPosKet false p x' x,
    unitaryConj_val, msc_fullSysQft_pf_congr _ pos24_6_le_80 qft]
  have hCongrA : ∀ γ₁ γ₂ : BitAssignment (fullSysCoreWires 80),
      (∀ q : Wire (fullSysCoreWires 80),
        q ∉ Set.range (coreElecCosetB1Block pos24_6_le_80).wires → γ₁ q = γ₂ q) →
      (mscPredA jScr γ₁ ↔ mscPredA jScr γ₂) := fun γ₁ γ₂ h ↦ by
    unfold mscPredA
    have hw2 := h MergedVepCoreSliceClosure.mscWSlot2
      (msc_wire_not_in_elecCosetB1 pos24_6_le_80 _ (Or.inl (by decide)))
    have hw1 := h MergedVepCoreSliceClosure.mscWSlot1
      (msc_wire_not_in_elecCosetB1 pos24_6_le_80 _ (Or.inl (by decide)))
    have hw0 :=
      h mscWSlot0 (msc_wire_not_in_elecCosetB1 pos24_6_le_80 mscWSlot0 (Or.inl (by decide)))
    have hsc := h (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) (msc_wire_not_in_elecCosetB1
        pos24_6_le_80 (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) (Or.inr (msc_scr_ge_3957 jScr)))
    have hrn : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore
      pos24_22_le_80) γ₁ =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80) γ₂
          := by
      rw [← msc_regVal_posBranch_eq_twist, ← msc_regVal_posBranch_eq_twist]
      exact regVal_eq_of_wire_eq _ γ₁ γ₂ fun i ↦
        h _ (msc_wire_not_in_elecCosetB1 pos24_6_le_80 _ (Or.inr (msc_rNucBranch_ge_3957 i)))
    rw [hw2, hw1, hw0, hrn, hsc]
  have hCongrGeA : ∀ γ₁ γ₂ : BitAssignment (fullSysCoreWires 80),
      (∀ q : Wire (fullSysCoreWires 80), 3924 ≤ q.val → γ₁ q = γ₂ q) →
      (mscPredA jScr γ₁ ↔ mscPredA jScr γ₂) := fun γ₁ γ₂ h ↦ by
    unfold mscPredA
    have hw2 := h MergedVepCoreSliceClosure.mscWSlot2 (by decide)
    have hw1 := h MergedVepCoreSliceClosure.mscWSlot1 (by decide)
    have hw0 := h mscWSlot0 (by decide)
    have hsc := h (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) (msc_scr_ge_3924 jScr)
    have hrn : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore
      pos24_22_le_80) γ₁ =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80) γ₂
          := by
      rw [← msc_regVal_posBranch_eq_twist, ← msc_regVal_posBranch_eq_twist]
      exact regVal_eq_of_wire_eq _ γ₁ γ₂ fun i ↦ h _ (msc_rNucBranch_ge_3924 i)
    rw [hw2, hw1, hw0, hrn, hsc]
  have hCommUA : (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUTwistParam true
      pos24_22_le_80 cfg).1 * mscDiagPred (mscPredA jScr) = mscDiagPred (mscPredA jScr) *
      (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUTwistParam true pos24_22_le_80 cfg).1
      := by
    have hT := msc_uTwistParam_preserves_diag_ge3924 pos24_22_le_80 cfg (mscPredA jScr) hCongrGeA
    have hQ := msc_qft_preserves_diag_not_in_elecCosetB1 pos24_6_le_80 qft (mscPredA jScr) hCongrA
    rw [Submonoid.coe_mul]
    exact msc_mul2_comm _ _ (mscDiagPred (mscPredA jScr)) hQ hT
  have hHostKetA : ∀ z : Fin (2 ^ systemQubits),
      (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUVepTwistRef pos24_22_le_80 cfg).1.mulVec
        (ket (mscCoreBeta false p z)) =
      (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUTwistParam true pos24_22_le_80 cfg).1.mulVec
        (ket (mscCoreBeta false p z)) := fun z ↦ by
    have hvFalse : mscVepHighNuc pos24_22_le_80 (mscCoreBeta false p z) = false := by
      by_cases hv : mscVepHighNuc pos24_22_le_80 (mscCoreBeta false p z) = true
      · exfalso
        have hge := ((vepHighNuc_iff pos24_22_le_80 (mscCoreBeta false p z)).mp hv).2
        change 216 ≤
          _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80)
          (mscCoreBeta false p z) at hge
        rw [msc_regVal_rNuc_coreBetaOf p z] at hge
        exact Nat.not_lt_of_ge hge hlt
      · exact Bool.not_eq_true _ |>.mp hv
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      msc_uVepTwistRef_host_ket pos24_22_le_80 cfg _ hvFalse]
  have hPhEqOnPA : U_ph.1 * mscDiagPred (mscPredA jScr) =
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 * mscDiagPred (mscPredA jScr) := by
    apply matrix_ext_of_ket_core; intro γ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      MergedVepCoreSliceClosure.mscDiagPred_mulVec_ket (mscPredA jScr) γ]
    by_cases hg : mscPredA jScr γ
    · rw [msc_ite_pos hg, one_smul]
      unfold mscPredA at hg
      rw [hUPosKet γ, hRawKet γ,
        hSwap0 γ γ hg.2.2.2.2 (fun _ _ _ ↦ rfl)
          hg.1 hg.2.1 hg.2.2.1
          ((msc_regVal_posBranch_eq_twist γ).symm ▸ hg.2.2.2.1)]
    · rw [msc_ite_neg hg, zero_smul, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hPredBeta : mscPredA jScr (mscCoreBeta false p x) := by
    unfold mscPredA
    exact ⟨(msc_coreBetaOf_coin0_bits p x).1,
      (msc_coreBetaOf_coin0_bits p x).2.1,
      (msc_coreBetaOf_coin0_bits p x).2.2,
      by rw [msc_regVal_rNuc_coreBetaOf]; exact hlt,
      msc_coreBetaOf_scr_zero jScr p hpScr x⟩
  exact msc_conj_entry_eq_of_proj _ _ _ _ (mscDiagPred (mscPredA jScr))
    (mscCoreBeta false p x') (mscCoreBeta false p x)
    (hHostKetA x') (hHostKetA x) hCommUA
    (by
      rw [MergedVepCoreSliceClosure.mscDiagPred_mulVec_ket (mscPredA jScr),
        msc_ite_pos hPredBeta, one_smul])
    hPhEqOnPA

theorem msc_hPhOnSWB_gen (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool) (hRawKet : ∀ η : BitAssignment (fullSysCoreWires
    80), (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) = (if φ η then (-1
    : ℂ) else 1) • ket η) (jScr : Fin 16) (hSwap0 : ∀ γ_act γ_ref : BitAssignment
    posCoreWires, γ_act (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0 → (∀ q : Wire posCoreWires,
    ¬(3960 ≤ q.val ∧ q.val < 3968) → ¬(4017 ≤ q.val ∧ q.val < 4033) → γ_act q = γ_ref q) →
    γ_ref (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0 → γ_ref (wSlot1Core (QRegExt.ofFin
    posCoreWires)) = 0 → γ_ref (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0 →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    (rNucIdx (QRegExt.ofFin posCoreWires)) γ_ref < 216 → φ (swapCoreScrGenFn (le_rfl : 80 ≤
    80) jScr γ_act) = φ γ_ref) (U_ph : Unitary (2 ^ (fullSysCoreWires 80))) (hUPosKet : ∀ β :
    BitAssignment (fullSysCoreWires 80), U_ph.1.mulVec (ket β) = (if φ (swapCoreScrGenFn
    (le_rfl : 80 ≤ 80) jScr β) then (-1 : ℂ) else 1) • ket β) (lVal : Fin (2 ^ 8))
    (yIdx : Fin (2 ^ 24)) : U_ph.1 *
    ((mscVepSwapNuc pos24_22_le_80 lVal).1 * mscDiagPredB jScr yIdx) =
    (mscVepSwapNuc pos24_22_le_80 lVal).1 * ((castUnitaryPow2 pos24_coreWires80_eq.symm
    U_raw).1 * mscDiagPredB jScr yIdx) := by
  unfold mscDiagPredB
  apply matrix_ext_of_ket_core; intro η
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    MergedVepCoreSliceClosure.mscDiagPred_mulVec_ket (mscPredB jScr yIdx) η]
  by_cases hη : mscPredB jScr yIdx η
  · rw [msc_ite_pos hη, one_smul]
    unfold mscPredB at hη
    have hSWη : (mscVepSwapNuc pos24_22_le_80 lVal).1.mulVec (ket η) = ket (mscGammaAct lVal η) :=
      msc_vepSwapNuc_mulVec_ket pos24_22_le_80 lVal η
    rw [hSWη, hUPosKet (mscGammaAct lVal η), hRawKet η,
      Matrix.mulVec_smul, hSWη,
      hSwap0 (mscGammaAct lVal η) η
        (mscGammaAct_scr_zero jScr lVal η hη.2.2.2.2.1)
        (mscGammaAct_out lVal η)
        hη.1 hη.2.1 hη.2.2.1
        (by rw [msc_regVal_posBranch_eq_twist, hη.2.2.2.1]; decide)]
  · rw [msc_ite_neg hη, zero_smul, Matrix.mulVec_zero, Matrix.mulVec_zero,
      Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem msc_tail_hDComm_gen (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool) (hRawKet : ∀ η : BitAssignment (fullSysCoreWires
    80), (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) = (if φ η then (-1
    : ℂ) else 1) • ket η) (jScr : Fin 16) (yIdx : Fin (2 ^ 24)) :
    (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 * mscDiagPredB jScr yIdx =
    mscDiagPredB jScr yIdx * (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1 := by
  unfold mscDiagPredB
  apply matrix_ext_of_ket_core; intro η
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    MergedVepCoreSliceClosure.mscDiagPred_mulVec_ket (mscPredB jScr yIdx) η,
    hRawKet η, Matrix.mulVec_smul, Matrix.mulVec_smul, hRawKet η,
    MergedVepCoreSliceClosure.mscDiagPred_mulVec_ket (mscPredB jScr yIdx) η, smul_comm]

noncomputable abbrev mscTailMidRaw (U_raw : Unitary (2 ^ posCoreWires))
    (qft : FullSysQft654Bundle) (p : BitAssignment 80) (x' x : Fin (2 ^ systemQubits))
    (yIdx : Fin (2 ^ 24)) : ℂ := sysBlock80Raw U_raw qft (cfgProjZ512 (nyq512ProjEquiv3D
    (mProjGridEquiv24 yIdx, p80CosetP3 p))) false (p80SetNucZero p)
    (mProj24_sp.replaceIndex x' yIdx) (mProj24_sp.replaceIndex x yIdx)

theorem msc_tail_hMid_gen (U_raw : Unitary (2 ^ posCoreWires)) (qft : FullSysQft654Bundle)
    (p : BitAssignment 80) (x' x : Fin (2 ^ systemQubits)) (yIdx : Fin (2 ^ 24)) : dotProduct
    (star (mscTailVH qft p x' yIdx)) ((castUnitaryPow2 pos24_coreWires80_eq.symm
    U_raw).1.mulVec (mscTailVH qft p x yIdx)) = mscTailMidRaw U_raw qft p x' x yIdx := by
  unfold mscTailVH mscTailMidRaw
  have hCfgY : mscCfgY p yIdx =
      cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, p80CosetP3 p)) := rfl
  have h1 := (msc_conj3_entry_eq_dotProduct (fullSysQftCoreUnitary pos24_6_le_80 qft *
      mscUTwistParam true pos24_22_le_80 (mscCfgY p yIdx)).1 (castUnitaryPow2
      pos24_coreWires80_eq.symm U_raw).1 (mscCoreBeta false (p80SetNucZero p)
      (mProj24_sp.replaceIndex x' yIdx)) (mscCoreBeta false (p80SetNucZero p)
      (mProj24_sp.replaceIndex x yIdx))).symm
  have h2 := (msc_sysBlock80Raw_eq_conj U_raw qft (mscCfgY p yIdx) false (p80SetNucZero p)
    (mProj24_sp.replaceIndex x' yIdx) (mProj24_sp.replaceIndex x yIdx)).symm
  exact (h1.trans h2).trans (congrArg (fun c ↦ sysBlock80Raw U_raw qft c false (p80SetNucZero
    p) (mProj24_sp.replaceIndex x' yIdx) (mProj24_sp.replaceIndex x yIdx)) hCfgY)

theorem msc_tail_hout_gen (U_raw : Unitary (2 ^ posCoreWires)) (qft : FullSysQft654Bundle)
    (p : BitAssignment 80) (x' x : Fin (2 ^ systemQubits)) (yIdx : Fin (2 ^ 24)) : star
    (mscTailAlpha p x' yIdx) * mscTailMidRaw U_raw qft p x' x yIdx * mscTailAlpha p x yIdx =
    star ((uProjPlus512_3D (p80CosetP3 p)).1 yIdx (mProj24_sp.extractIndex x')) *
    sysBlock80Raw U_raw qft (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, p80CosetP3
    p))) false (p80SetNucZero p) (mProj24_sp.replaceIndex x' yIdx)
    (mProj24_sp.replaceIndex x yIdx) * (uProjPlus512_3D (p80CosetP3 p)).1 yIdx
    (mProj24_sp.extractIndex x) := msc_congr2 (· * ·)
    (msc_congr2 (· * ·) (congrArg star rfl) rfl) rfl

theorem msc_hBlk0_tail_gen
    (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool)
    (hRawKet : ∀ η : BitAssignment (fullSysCoreWires 80),
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) =
        (if φ η then (-1 : ℂ) else 1) • ket η)
    (qft : FullSysQft654Bundle)
    (hQft : QftPreservesCoset3 qft)
    (cfg : Configuration)
    (jScr : Fin 16)
    (hSwap0 : ∀ γ_act γ_ref : BitAssignment posCoreWires,
      γ_act (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0 →
      (∀ q : Wire posCoreWires,
        ¬(3960 ≤ q.val ∧ q.val < 3968) → ¬(4017 ≤ q.val ∧ q.val < 4033) → γ_act q = γ_ref q) →
      γ_ref (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ_ref (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ_ref (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0 →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx (QRegExt.ofFin
        posCoreWires)) γ_ref < 216 →
      φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr γ_act) = φ γ_ref)
    (U_ph : Unitary (2 ^ (fullSysCoreWires 80)))
    (hUPosKet : ∀ β : BitAssignment (fullSysCoreWires 80),
      U_ph.1.mulVec (ket β) =
        (if φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr β)
          then (-1 : ℂ) else 1) • ket β)
    (p : BitAssignment 80)
    (hpScr : p ⟨63 + jScr.val, by omega⟩ = 0)
    (hge : 216 ≤ p80NucVal p)
    (x' x : Fin (2 ^ systemQubits)) :
    (coreUnitarySym
      (unitaryConj
        (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft *
          mscUVepTwistRef pos24_22_le_80 cfg)
        U_ph)).1
        (coreIdxOf hkSym80 false p x') (coreIdxOf hkSym80 false p x) =
      ∑ yIdx : Fin (2 ^ 24),
        star ((uProjPlus512_3D (p80CosetP3 p)).1 yIdx (mProj24_sp.extractIndex x')) *
          sysBlock80Raw U_raw qft (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx,
            p80CosetP3 p)))
            false (p80SetNucZero p)
            (mProj24_sp.replaceIndex x' yIdx) (mProj24_sp.replaceIndex x yIdx) *
          (uProjPlus512_3D (p80CosetP3 p)).1 yIdx (mProj24_sp.extractIndex x) := by
  have hLhs : (coreUnitarySym (unitaryConj (fullSysQftCoreUnitary (le_trans
      (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft * mscUVepTwistRef pos24_22_le_80 cfg)
      U_ph)).1 (coreIdxOf hkSym80 false p x') (coreIdxOf hkSym80 false p x) =
      ((fullSysQftCoreUnitary pos24_6_le_80 qft * mscUVepTwistRef pos24_22_le_80 cfg).1ᴴ *
      U_ph.1 * (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUVepTwistRef pos24_22_le_80
      cfg).1) ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta false p x'))
      ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta false p x)) :=
      (msc_coreIdx_entry_gen φ qft hQft cfg jScr U_ph hUPosKet false p x' x).trans (congrFun
      (congrFun (unitaryConj_val (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUVepTwistRef
      pos24_22_le_80 cfg) U_ph) ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta
      false p x'))) ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta false p x)))
  exact hLhs.trans
    (msc_conj_entry_eq_finset_sum_of_orth_proj
      (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUVepTwistRef pos24_22_le_80 cfg).1
      U_ph.1
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1
      (mscVepSwapNuc pos24_22_le_80 ⟨p80NucVal p, p80NucVal_lt_256 p⟩).1
      (mscDiagPredB jScr)
      (mscTailAlpha p x')
      (mscTailAlpha p x)
      (mscTailMidRaw U_raw qft p x' x)
      ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta false p x'))
      ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta false p x))
      (ket (mscCoreBeta false p x'))
      (ket (mscCoreBeta false p x))
      (mscTailVH qft p x')
      (mscTailVH qft p x)
      (msc_conj3_entry_eq_dotProduct
        (fullSysQftCoreUnitary pos24_6_le_80 qft * mscUVepTwistRef pos24_22_le_80 cfg).1
        U_ph.1
        (mscCoreBeta false p x') (mscCoreBeta false p x))
      (msc_unitary_adj_mul_self (mscVepSwapNuc pos24_22_le_80 ⟨p80NucVal p, p80NucVal_lt_256 p⟩))
      (msc_hFwdVep qft cfg p hge x')
      (msc_hFwdVep qft cfg p hge x)
      (msc_tail_hs qft p x')
      (msc_tail_hs qft p x)
      (msc_tail_hvIn qft jScr p hpScr x')
      (msc_tail_hvIn qft jScr p hpScr x)
      (msc_hPhOnSWB_gen U_raw φ hRawKet jScr hSwap0 U_ph hUPosKet ⟨p80NucVal p, p80NucVal_lt_256 p⟩)
      (msc_tail_hDComm_gen U_raw φ hRawKet jScr)
      (msc_tail_hOrth jScr)
      (msc_tail_hMid_gen U_raw qft p x' x)
      (msc_tail_hout_gen U_raw qft p x' x))

theorem mergedVepCore_hBlk0_gen
    (U_raw : Unitary (2 ^ posCoreWires))
    (φ : BitAssignment posCoreWires → Bool)
    (hRawKet : ∀ η : BitAssignment (fullSysCoreWires 80),
      (castUnitaryPow2 pos24_coreWires80_eq.symm U_raw).1.mulVec (ket η) =
        (if φ η then (-1 : ℂ) else 1) • ket η)
    (qft : FullSysQft654Bundle)
    (hQft : QftPreservesCoset3 qft)
    (cfg : Configuration)
    (jScr : Fin 16)
    (hSwap0 : ∀ γ_act γ_ref : BitAssignment posCoreWires,
      γ_act (mWCoreScrGen (le_rfl : 80 ≤ 80) jScr) = 0 →
      (∀ q : Wire posCoreWires,
        ¬(3960 ≤ q.val ∧ q.val < 3968) → ¬(4017 ≤ q.val ∧ q.val < 4033) → γ_act q = γ_ref q) →
      γ_ref (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ_ref (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0 →
      γ_ref (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0 →
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx (QRegExt.ofFin
        posCoreWires)) γ_ref < 216 →
      φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr γ_act) = φ γ_ref)
    (U_ph : Unitary (2 ^ (fullSysCoreWires 80)))
    (hUPosKet : ∀ β : BitAssignment (fullSysCoreWires 80),
      U_ph.1.mulVec (ket β) =
        (if φ (swapCoreScrGenFn (le_rfl : 80 ≤ 80) jScr β)
          then (-1 : ℂ) else 1) • ket β)
    (p : BitAssignment 80)
    (hpScr : p ⟨63 + jScr.val, by omega⟩ = 0)
    (x' x : Fin (2 ^ systemQubits)) :
    (coreUnitarySym
      (unitaryConj
        (fullSysQftCoreUnitary (le_trans (by decide : 6 ≤ 80) (le_rfl : 80 ≤ 80)) qft *
          mscUVepTwistRef pos24_22_le_80 cfg)
        U_ph)).1
        (coreIdxOf hkSym80 false p x') (coreIdxOf hkSym80 false p x) =
      mergedSliceGen (fun c' p' ↦ sysBlock80Raw U_raw qft c' false p') cfg p x' x := by
  by_cases hlt : p80NucVal p < 216
  · have hSlice := msc_mergedSliceGen_lt
      (fun c' p' ↦ sysBlock80Raw U_raw qft c' false p') cfg p hlt x' x
    have hBeta : ((fun c' p' ↦ sysBlock80Raw U_raw qft c' false p') cfg p) x' x =
        sysBlock80Raw U_raw qft cfg false p x' x := rfl
    exact (msc_hBlk0_host_gen U_raw φ hRawKet qft hQft cfg jScr hSwap0 U_ph hUPosKet p hpScr hlt x'
      x).trans
      (hSlice.trans hBeta).symm
  · have hTailEntry :
        let bP := p80CosetP3 p
        ((mProj24_sp.embedUnitary (uProjPlus512_3D bP)).1ᴴ *
          (∑ yIdx : Fin (2 ^ 24),
            mProjBasisGen mProj24_sp yIdx *
              sysBlock80Raw U_raw qft (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, bP)))
                false (p80SetNucZero p)) *
          (mProj24_sp.embedUnitary (uProjPlus512_3D bP)).1) x' x =
        ∑ yIdx : Fin (2 ^ 24),
          star ((uProjPlus512_3D bP).1 yIdx (mProj24_sp.extractIndex x')) *
            sysBlock80Raw U_raw qft (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, bP)))
              false (p80SetNucZero p)
              (mProj24_sp.replaceIndex x' yIdx) (mProj24_sp.replaceIndex x yIdx) *
            (uProjPlus512_3D bP).1 yIdx (mProj24_sp.extractIndex x) :=
      msc_proj_sandwich_entry_gen mProj24_sp (uProjPlus512_3D (p80CosetP3 p))
        (fun yIdx ↦ sysBlock80Raw U_raw qft
          (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, p80CosetP3 p)))
          false (p80SetNucZero p))
        (fun _ a b hab ↦
          sysBlock80Raw_projDiag U_raw φ hRawKet qft _ false (p80SetNucZero p) a b hab)
        x' x
    have hSlice := (msc_mergedSliceGen_ge_sum
      (sysSlice := fun c' p' ↦ sysBlock80Raw U_raw qft c' false p')
      cfg p hlt
      (fun yIdx ↦ congrArg (mProjBasisGen mProj24_sp yIdx * ·) rfl) x' x).trans
      hTailEntry
    exact (msc_hBlk0_tail_gen U_raw φ hRawKet qft hQft cfg jScr hSwap0 U_ph hUPosKet p hpScr
      (Nat.le_of_not_lt hlt) x' x).trans hSlice.symm

theorem mbh_ket_uXThCore (γ : BitAssignment posCoreWires) : uXThCore.1.mulVec (ket γ) = ket
    (Function.update γ wThCore (γ wThCore + 1)) := ket_uXThCore γ

theorem uXThCore_mul_self : uXThCore.1 * uXThCore.1 = 1 := by
  apply matrix_ext_of_ket_core; intro γ
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_uXThCore, mbh_ket_uXThCore,
      Function.update_idem, Function.update_self]
  have hcancel : γ wThCore + 1 + 1 = γ wThCore := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hcancel, Function.update_eq_self]

theorem uXThCore_sa : uXThCore.1ᴴ = uXThCore.1 := by
  have h1 : uXThCore.1ᴴ * uXThCore.1 = 1 := msc_unitary_adj_mul_self uXThCore
  calc uXThCore.1ᴴ
      = uXThCore.1ᴴ * (uXThCore.1 * uXThCore.1) := by rw [uXThCore_mul_self, Matrix.mul_one]
    _ = (uXThCore.1ᴴ * uXThCore.1) * uXThCore.1 := (Matrix.mul_assoc _ _ _).symm
    _ = uXThCore.1 := by rw [h1, Matrix.one_mul]

section HpowStep_4
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_4 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem uSwapCore3967_comm_uXThCore :
    uSwapCore3967.1 * uXThCore.1 = uXThCore.1 * uSwapCore3967.1 := by
  apply matrix_ext_of_ket_core; intro γ
  rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_uXThCore,
      uSwapCore3967_mulVec_ket, uSwapCore3967_mulVec_ket, mbh_ket_uXThCore]
  congr 1; funext q
  rw [swapCore3967Fn_eq_swapCoreScrGenFn12, swapCore3967Fn_eq_swapCoreScrGenFn12]
  let sPerm := Equiv.swap (mWCore3967Gen (le_rfl : 80 ≤ 80))
    (mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩)
  have hThSwap : sPerm wThCore = wThCore :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  change Function.update γ wThCore (γ wThCore + 1) (sPerm q) =
    Function.update (fun w ↦ γ (sPerm w)) wThCore (γ (sPerm wThCore) + 1) q
  rw [hThSwap]
  by_cases hq : q = wThCore
  · subst hq; rw [hThSwap, Function.update_self, Function.update_self]
  · have hsq : sPerm q ≠ wThCore := fun h ↦ hq (by
      have h2 := congrArg sPerm h
      rw [Equiv.swap_apply_self, hThSwap] at h2; exact h2)
    rw [Function.update_of_ne hsq, Function.update_of_ne hq]

end HpowStep_4
section HpowStep_5
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_5 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem fullSysQftCoreUnitary_comm_uXThCore (qft : FullSysQft654Bundle) :
    (fullSysQftCoreUnitary pos24_6_le_80 qft).1 * uXThCore.1 =
      uXThCore.1 * (fullSysQftCoreUnitary pos24_6_le_80 qft).1 := by
  have hEmb : ((QRegister.singleton wThCore).embedUnitary
      (permutationUnitary (permThClean 0 (fun _ ↦ true)))).1 = uXThCore.1 :=
    congrArg Subtype.val (embedUnitary_permThClean (QRegister.singleton wThCore) 0 (fun _ ↦ true))
  have hDisj : (coreElecCosetB1Block pos24_6_le_80).DisjointWires (QRegister.singleton wThCore) :=
    by
    rw [QRegister.disjoint_iff]
    intro i j hij
    have hlt := PosSlots24Semantic80Physics.coreElecCosetB1_wire_lt_3957 i
    have hv : ((QRegister.singleton wThCore) j).val = 3985 := rfl
    have hijv := congrArg Fin.val hij
    omega
  rw [← hEmb, fullSysQftCoreUnitary, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisj _ _

end HpowStep_5
section HpowStep_6
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_6 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
open Classical in
theorem mscUTwistParam_comm_uXThCore (cfg : Configuration) :
    (mscUTwistParam true pos24_22_le_80 cfg).1 * uXThCore.1 =
      uXThCore.1 * (mscUTwistParam true pos24_22_le_80 cfg).1 := by
  unfold mscUTwistParam
  apply matrix_ext_of_ket_core; intro γ
  let N80 := fullSysCoreWires 80
  let rId := QRegExt.ofFin N80
  have hEmb : (rId.embedUnitary (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1 =
      (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg).1 :=
    congrArg Subtype.val (PosSlots24SemanticOracleConcrete80.ofFin_embedUnitary_eq _)
  have hIdFn : ∀ β : BitAssignment N80,
      (fun z : Wire N80 ↦
        if hz : z ∈ rId.image then
          NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 (fun q ↦ β (rId q))
            (Classical.choose ((QRegister.mem_image rId z).mp hz))
        else β z) =
      NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 β := fun β ↦ by
    funext z
    have hz : z ∈ rId.image := (QRegister.mem_image rId z).mpr ⟨z, rfl⟩
    have hch : Classical.choose ((QRegister.mem_image rId z).mp hz) = z :=
      Classical.choose_spec ((QRegister.mem_image rId z).mp hz)
    simp only [hz, ↓reduceDIte, hch]; rfl
  have hKetEq : ∀ β : BitAssignment N80,
      (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg).1.mulVec (ket β) =
      NuclearTwistRealizes.twistCorePhase true pos24_22_le_80 cfg β •
        ket (NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 β) := fun β ↦ by
    rw [← hEmb]
    have hv := NuclearTwistRealizes.uTwistParam_mulVec_basisKet true pos24_22_le_80 cfg rId β
    rw [hIdFn β] at hv
    exact hv
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_uXThCore,
      hKetEq (Function.update γ wThCore (γ wThCore + 1)),
      hKetEq γ, Matrix.mulVec_smul, mbh_ket_uXThCore]
  have hlt : ∀ q : Fin N80, q.val < 3976 →
      Function.update γ wThCore (γ wThCore + 1) q = γ q := fun q hq ↦
    Function.update_of_ne (fun h ↦ by have hv : q.val = 3985 := congrArg Fin.val h; omega) _ _
  obtain ⟨hPhEq, hPermLt⟩ := PosSlots24Semantic80Physics.twistCore_eq_of_lt3976 cfg
    (Function.update γ wThCore (γ wThCore + 1)) γ hlt
  have hPermComm : NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80
      (Function.update γ wThCore (γ wThCore + 1)) = Function.update
      (NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ) wThCore
      (NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ wThCore + 1) := by
    funext q
    have hThEq : NuclearTwistRealizes.twistCorePermFn true pos24_22_le_80 γ wThCore = γ wThCore :=
      NuclearTwistRealizes.twistCorePermFn_high_eq true pos24_22_le_80 γ wThCore (by decide)
    rw [hThEq]
    by_cases hq : q.val < 3976
    · rw [hPermLt q hq, Function.update_of_ne (fun h ↦ by
      have hv : q.val = 3985 :=
        congrArg Fin.val h; omega)]
    · rw [NuclearTwistRealizes.twistCorePermFn_high_eq true pos24_22_le_80 _ q (by omega)]
      by_cases hqTh : q = wThCore
      · subst hqTh; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hqTh, Function.update_of_ne hqTh,
            NuclearTwistRealizes.twistCorePermFn_high_eq true pos24_22_le_80 γ q (by omega)]
  rw [hPhEq, hPermComm]

end HpowStep_6
section HpowStep_7
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_7 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem mscVepSwapNuc_comm_uXThCore (lVal : Fin (2 ^ 8)) :
    (mscVepSwapNuc pos24_22_le_80 lVal).1 * uXThCore.1 =
      uXThCore.1 * (mscVepSwapNuc pos24_22_le_80 lVal).1 := by
  have hEmb : ((QRegister.singleton wThCore).embedUnitary
      (permutationUnitary (permThClean 0 (fun _ ↦ true)))).1 = uXThCore.1 :=
    congrArg Subtype.val (embedUnitary_permThClean (QRegister.singleton wThCore) 0 (fun _ ↦ true))
  have hDisj : (mscRNucCore pos24_22_le_80).DisjointWires (QRegister.singleton wThCore) := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    have hr := msc_rNucCore_in_range i
    have hv : ((QRegister.singleton wThCore) j).val = 3985 := rfl
    have hijv := congrArg Fin.val hij
    omega
  rw [← hEmb, mscVepSwapNuc, vepSwapNuc, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisj _ _

end HpowStep_7
section HpowStep_8
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_8 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem mscUVepTwistRef_comm_uXThCore (cfg : Configuration) :
    (mscUVepTwistRef pos24_22_le_80 cfg).1 * uXThCore.1 =
      uXThCore.1 * (mscUVepTwistRef pos24_22_le_80 cfg).1 := by
  apply matrix_ext_of_ket_core; intro γ
  let γ' := Function.update γ wThCore (γ wThCore + 1)
  have hOut : ∀ q : Wire (fullSysCoreWires 80), q.val < 3976 → γ' q = γ q := fun q hq ↦
    Function.update_of_ne (fun h ↦ by have hv : q.val = 3985 := congrArg Fin.val h; omega) _ _
  have hvEq : mscVepHighNuc pos24_22_le_80 γ' = mscVepHighNuc pos24_22_le_80 γ := by
    apply Bool.eq_iff_iff.mpr
    rw [mscVepHighNuc, vepHighNuc_iff, vepHighNuc_iff]
    have hc0 : NuclearTwistRealizes.coin0Active γ' = NuclearTwistRealizes.coin0Active γ := by
      unfold NuclearTwistRealizes.coin0Active
      rw [hOut _ (by decide), hOut _ (by decide), hOut _ (by decide)]
    have hrn : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore
      pos24_22_le_80) γ' =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (mscRNucCore pos24_22_le_80) γ
          :=
      regVal_eq_of_wire_eq _ γ' γ fun i ↦ hOut _ (by have := (msc_rNucCore_in_range i).2; omega)
    rw [hc0]; exact and_congr_right fun _ ↦ by rw [hrn]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_uXThCore]
  change (mscUVepTwistRef pos24_22_le_80 cfg).1.mulVec (ket γ') =
    uXThCore.1.mulVec ((mscUVepTwistRef pos24_22_le_80 cfg).1.mulVec (ket γ))
  by_cases hv : mscVepHighNuc pos24_22_le_80 γ = true
  · have hv' : mscVepHighNuc pos24_22_le_80 γ' = true := hvEq.trans hv
    let lVal := (mscRNucCore pos24_22_le_80).extractIndex ((basisBitsEquiv _).symm γ)
    have hlVal' : (mscRNucCore pos24_22_le_80).extractIndex ((basisBitsEquiv _).symm γ') = lVal :=
      by
      apply (basisBitsEquiv 8).injective; funext i
      change basisBits 8 _ i = basisBits 8 _ i
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
          msc_basisBits_symm, msc_basisBits_symm]
      exact hOut _ (by have := (msc_rNucCore_in_range i).2; omega)
    have hCoset' : mscExtractCosetP3 pos24_22_le_80 γ' = mscExtractCosetP3 pos24_22_le_80 γ := by
      funext w; apply Fin.ext
      dsimp [mscExtractCosetP3, extractCosetP3]
      exact congrArg ZMod.val (hOut _ (by revert w; decide))
    have hProj' : mscExtractProj24 γ' = mscExtractProj24 γ := by
      apply (basisBitsEquiv 24).injective; funext i
      change basisBits 24 _ i = basisBits 24 _ i
      unfold mscExtractProj24 extractProj24
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
          msc_basisBits_symm, msc_basisBits_symm]
      have hrv : ((rProjCore (QRegExt.idReg
          (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))).wires i).val = 3924 + i.val := rfl
      exact hOut _ (by have := i.isLt; omega)
    rw [msc_uVepTwistRef_vep_ket pos24_22_le_80 cfg lVal γ' hv' hlVal',
        msc_uVepTwistRef_vep_ket pos24_22_le_80 cfg lVal γ hv rfl,
        hCoset', hProj', Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun yIdx _ ↦ ?_
    rw [Matrix.mulVec_smul]
    refine congrArg (_ • ·) ?_
    have hWriteComm : vepWriteReg γ' mscRProjCore (basisBits 24 yIdx) =
        Function.update (vepWriteReg γ mscRProjCore (basisBits 24 yIdx)) wThCore
          (vepWriteReg γ mscRProjCore (basisBits 24 yIdx) wThCore + 1) := by
      have hThNotP : wThCore ∉ Set.range (mscRProjCore (mPayload := 80)).wires := by
        rintro ⟨i, hi⟩
        have hrv : ((mscRProjCore (mPayload := 80)) i).val = 3924 + i.val := rfl
        have hv : ((mscRProjCore (mPayload := 80)) i).val = 3985 := congrArg Fin.val hi
        have := i.isLt
        omega
      have hThVal : vepWriteReg γ mscRProjCore (basisBits 24 yIdx) wThCore = γ wThCore :=
        ProjZ512QftAndTwist288.vepWriteReg_not_mem γ mscRProjCore _ wThCore hThNotP
      rw [hThVal]
      funext q
      rcases Classical.em (q ∈ Set.range (mscRProjCore (mPayload := 80)).wires) with hqP | hqP
      · obtain ⟨i, rfl⟩ := hqP
        have hne : mscRProjCore (mPayload := 80) i ≠ wThCore := fun h ↦ hThNotP ⟨i, h⟩
        rw [ProjZ512QftAndTwist288.vepWriteReg_mem, Function.update_of_ne hne,
            ProjZ512QftAndTwist288.vepWriteReg_mem]
      · rw [ProjZ512QftAndTwist288.vepWriteReg_not_mem _ mscRProjCore _ q hqP]
        by_cases hqTh : q = wThCore
        · subst hqTh; rw [Function.update_self]; rfl
        · dsimp only [γ']
          rw [Function.update_of_ne hqTh, Function.update_of_ne hqTh,
              ProjZ512QftAndTwist288.vepWriteReg_not_mem _ mscRProjCore _ q hqP]
    rw [hWriteComm, ← mbh_ket_uXThCore]
    have hCommSW := mscVepSwapNuc_comm_uXThCore lVal
    have hCommTw := mscUTwistParam_comm_uXThCore
      (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx, mscExtractCosetP3 pos24_22_le_80 γ)))
    have hMulComm : (mscVepSwapNuc pos24_22_le_80 lVal).1 * (mscUTwistParam true
        pos24_22_le_80 (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx,
        mscExtractCosetP3 pos24_22_le_80 γ)))).1 * (mscVepSwapNuc pos24_22_le_80 lVal).1 *
        uXThCore.1 = uXThCore.1 * ((mscVepSwapNuc pos24_22_le_80 lVal).1 * (mscUTwistParam
        true pos24_22_le_80 (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx,
        mscExtractCosetP3 pos24_22_le_80 γ)))).1 * (mscVepSwapNuc pos24_22_le_80 lVal).1) :=
        msc_mul2_comm _ _ uXThCore.1 (msc_mul2_comm _ _ uXThCore.1 hCommSW hCommTw) hCommSW
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMulComm, Matrix.mul_assoc]
  · have hvF : mscVepHighNuc pos24_22_le_80 γ = false := Bool.not_eq_true _ |>.mp hv
    have hvF' : mscVepHighNuc pos24_22_le_80 γ' = false := hvEq.trans hvF
    rw [msc_uVepTwistRef_host_ket pos24_22_le_80 cfg γ' hvF',
        msc_uVepTwistRef_host_ket pos24_22_le_80 cfg γ hvF,
        show ket γ' = uXThCore.1.mulVec (ket γ) from (mbh_ket_uXThCore γ).symm,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mscUTwistParam_comm_uXThCore cfg]

end HpowStep_8
/-- Single-bit permutation unitary flipping `wTh86` on the 86-wire ancilla/payload register. -/
noncomputable def uXTh86 : Unitary (2 ^ (selWiresSym 80)) :=
  permutationUnitary (permThClean wTh86 (fun _ ↦ true))

section HpowStep_9
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_9 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem embed_uXTh86_eq_uXThCore : ((coreAncSym 80).embedUnitary uXTh86).1 = uXThCore.1 :=
    congrArg Subtype.val (embedUnitary_permThClean (coreAncSym 80) wTh86 (fun _ ↦ true))

end HpowStep_9
theorem permThClean_wTh86_ancIdx86 (s0 : Bool) (p : BitAssignment 80) :
    permThClean wTh86 (fun _ ↦ true) (ancIdx86 s0 p) =
      ancIdx86 s0 (Function.update p idxTh80 (p idxTh80 + 1)) := by
  apply (basisBitsEquiv 86).injective
  have h1 : basisBits 86 (permThClean wTh86 (fun _ ↦ true) (ancIdx86 s0 p)) =
      flipThClean wTh86 (fun _ ↦ true) (ancBits86 s0 p) := by
    change (basisBitsEquiv 86) ((basisBitsEquiv 86).symm
      (flipThClean wTh86 (fun _ ↦
        true) ((basisBitsEquiv 86) ((basisBitsEquiv 86).symm (ancBits86 s0 p))))) = _
    rw [(basisBitsEquiv 86).apply_symm_apply, (basisBitsEquiv 86).apply_symm_apply]
  have h2 : basisBits 86 (ancIdx86 s0 (Function.update p idxTh80 (p idxTh80 + 1))) = ancBits86
      s0 (Function.update p idxTh80 (p idxTh80 + 1)) := (basisBitsEquiv 86).apply_symm_apply _
  change basisBits 86 (permThClean wTh86 (fun _ ↦ true) (ancIdx86 s0 p)) =
    basisBits 86 (ancIdx86 s0 (Function.update p idxTh80 (p idxTh80 + 1)))
  rw [h1, h2]
  unfold flipThClean flipTh
  simp only [↓reduceIte]
  funext idx
  by_cases hidx : idx = wTh86
  · subst hidx
    rw [Function.update_self]
    have h0 : ((wTh86 : Wire 86).val == 0) = false := rfl
    have h6 : ¬((wTh86 : Wire 86).val < 6) := by decide
    have hsub : (⟨(wTh86 : Wire 86).val - 6,
      PosSlots24SemanticOracleConcrete80.ancIdx86_sub_lt wTh86 h6⟩ : Fin 80) = idxTh80 := rfl
    unfold ancBits86
    simp only [h0, Bool.false_eq_true, ↓reduceIte, h6, ↓reduceDIte, hsub, Function.update_self]
  · rw [Function.update_of_ne hidx]
    by_cases hlt6 : idx.val < 6
    · unfold ancBits86
      by_cases h0 : idx.val == 0
      · simp [h0]
      · simp [h0, hlt6]
    · unfold ancBits86
      have h0 : (idx.val == 0) = false := by
        cases h : idx.val with
        | zero => omega
        | succ _ => rfl
      simp only [h0, Bool.false_eq_true, ↓reduceIte, hlt6, ↓reduceDIte]
      have hne80 : (⟨idx.val - 6, by have := idx.isLt; omega⟩ : Fin 80) ≠ idxTh80 := by
        intro h
        apply hidx
        have hv := congrArg Fin.val h
        dsimp [idxTh80, wTh86] at hv
        ext; dsimp [wTh86]; omega
      exact (Function.update_of_ne hne80 _ _).symm

theorem perm_inv_mul_apply {D : ℕ} (σ : Equiv.Perm (Fin D)) (hσ_inv : ∀ x, σ (σ x) = x)
    (M : Operator D) (i j : Fin D) :
    ((Operator.permutationUnitary σ).1 * M) i j = M (σ i) j := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_eq_single (σ i) (fun k _ hk ↦ ?_)
    (fun habs ↦ absurd (Finset.mem_univ _) habs)).trans ?_
  · rw [ProjZ512QftAndTwist288.permutationUnitary_entry]
    have hne : σ k ≠ i := fun h ↦ hk (by rw [← h, hσ_inv])
    simp only [hne, ↓reduceIte, zero_mul]
  · rw [ProjZ512QftAndTwist288.permutationUnitary_entry]
    simp only [hσ_inv i, ↓reduceIte, one_mul]

theorem uXTh86_mul_col_eq_of_update_31 (V_eff : Unitary (2 ^ (selWiresSym 80))) (s0 : Bool)
    (a_c : Fin (2 ^ (selWiresSym 80))) (hSupp : ∀ b : Fin (2 ^ (selWiresSym 80)), b ∉
    Set.range (ancIdx86 s0) → V_eff.1 b a_c = 0) (hTh : ∀ p : BitAssignment 80, V_eff.1
    (ancIdx86 s0 (Function.update p idxTh80 (p idxTh80 + 1))) a_c = V_eff.1 (ancIdx86 s0 p)
    a_c) (b : Fin (2 ^ (selWiresSym 80))) : (uXTh86.1 * V_eff.1) b a_c = V_eff.1 b a_c := by
  have hσ_inv : ∀ x, permThClean wTh86 (fun _ ↦ true) (permThClean wTh86 (fun _ ↦ true) x) = x :=
    (permThClean wTh86 (fun _ ↦ true)).left_inv
  have hEntry : (uXTh86.1 * V_eff.1) b a_c = V_eff.1 (permThClean wTh86 (fun _ ↦ true) b) a_c :=
    perm_inv_mul_apply (permThClean wTh86 (fun _ ↦ true)) hσ_inv V_eff.1 b a_c
  rw [hEntry]
  rcases Classical.em (b ∈ Set.range (ancIdx86 s0)) with hb | hb
  · obtain ⟨p, rfl⟩ := hb
    rw [permThClean_wTh86_ancIdx86, hTh p]
  · have hσb : permThClean wTh86 (fun _ ↦ true) b ∉ Set.range (ancIdx86 s0) := by
      rintro ⟨p, hp⟩
      apply hb
      let p' := Function.update p idxTh80 (p idxTh80 + 1)
      have hp' : Function.update p' idxTh80 (p' idxTh80 + 1) = p := by
        dsimp only [p']
        rw [Function.update_self, Function.update_idem]
        have hc : p idxTh80 + 1 + 1 = p idxTh80 := by
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        rw [hc, Function.update_eq_self]
      have h1 := permThClean_wTh86_ancIdx86 s0 p'
      rw [hp'] at h1
      exact ⟨p', (permThClean wTh86 (fun _ ↦ true)).injective (h1.trans hp)⟩
    rw [hSupp _ hσb, hSupp b hb]

theorem embedMatrix_mul_basisOutcomeProjector_congr {K A : ℕ}
    (rAnc : QRegister A K) (M₁ M₂ : Operator (2 ^ A)) (a_c : Fin (2 ^ A))
    (hCol : ∀ b : Fin (2 ^ A), M₁ b a_c = M₂ b a_c) :
    rAnc.embedMatrix M₁ * rAnc.basisOutcomeProjector a_c =
      rAnc.embedMatrix M₂ * rAnc.basisOutcomeProjector a_c := by
  ext row col
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases hc : rAnc.extractIndex col = a_c
  · simp only [hc, ↓reduceIte, mul_one]
    by_cases hag : rAnc.AgreeOutside row col
    · rw [embedMatrix_entry_of_agreeOutside rAnc M₁ hag,
          embedMatrix_entry_of_agreeOutside rAnc M₂ hag, hc, hCol]
    · rw [embedMatrix_entry_of_not_agreeOutside rAnc M₁ hag,
          embedMatrix_entry_of_not_agreeOutside rAnc M₂ hag]
  · simp only [hc, ↓reduceIte, mul_zero]

section HpowStep_10
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_10 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem uXThCore_mul_embedAnc_proj_eq (V_eff : Unitary (2 ^ (selWiresSym 80))) (s0 : Bool)
    (a_c : Fin (2 ^ (selWiresSym 80))) (hSupp : ∀ b : Fin (2 ^ (selWiresSym 80)), b ∉
    Set.range (ancIdx86 s0) → V_eff.1 b a_c = 0) (hTh : ∀ p : BitAssignment 80, V_eff.1
    (ancIdx86 s0 (Function.update p idxTh80 (p idxTh80 + 1))) a_c = V_eff.1 (ancIdx86 s0 p)
    a_c) : uXThCore.1 * ((coreAncSym 80).embedMatrix V_eff.1 * (coreAncSym
    80).basisOutcomeProjector a_c) = (coreAncSym 80).embedMatrix V_eff.1 *
    (coreAncSym 80).basisOutcomeProjector a_c := by
  have hEmb : uXThCore.1 = (coreAncSym 80).embedMatrix uXTh86.1 := by
    rw [← embed_uXTh86_eq_uXThCore, QRegister.embedUnitary_val]
  rw [← Matrix.mul_assoc, hEmb, ← (coreAncSym 80).embedMatrix_mul]
  exact embedMatrix_mul_basisOutcomeProjector_congr (coreAncSym 80) _ _ a_c
    (uXTh86_mul_col_eq_of_update_31 V_eff s0 a_c hSupp hTh)

end HpowStep_10
theorem conj_eq_of_one_add_inv_mul_eq {D : ℕ} (X A B W : Operator D) (hX_sa : Xᴴ = X)
    (hXW : X * W = W) (hAB : (1 + X) * A * (1 + X) = (1 + X) * B * (1 + X)) : Wᴴ * A * W = Wᴴ
    * B * W := by
  have h1XW : (1 + X) * W = (2 : ℂ) • W := by
    rw [Matrix.add_mul, Matrix.one_mul, hXW, ← two_smul ℂ W]
  have hWX1 : Wᴴ * (1 + X) = (2 : ℂ) • Wᴴ := by
    have h1X_sa : (1 + X)ᴴ = 1 + X := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX_sa]
    calc Wᴴ * (1 + X)
        = Wᴴ * (1 + X)ᴴ := by rw [h1X_sa]
      _ = ((1 + X) * W)ᴴ := (Matrix.conjTranspose_mul (1 + X) W).symm
      _ = ((2 : ℂ) • W)ᴴ := by rw [h1XW]
      _ = (2 : ℂ) • Wᴴ := by rw [Matrix.conjTranspose_smul, star_ofNat]
  have hScale : ∀ M : Operator D,
      (1 / 4 : ℂ) • (Wᴴ * ((1 + X) * M * (1 + X)) * W) = Wᴴ * M * W := fun M ↦ by
    have hAssoc : Wᴴ * ((1 + X) * M * (1 + X)) * W = (Wᴴ * (1 + X)) * M * ((1 + X) * W) := by
      simp only [Matrix.mul_assoc]
    rw [hAssoc, hWX1, h1XW, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    norm_num
  rw [← hScale A, ← hScale B, hAB]

end ConfigPosS3Bounds
end PosS3Bounds
end
end PosS3Bounds

section PosMod4FermionicBounds
local instance (priority := 1000000) instNeZeroTwoPow_PosMod4FermionicBounds (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace PosMod4FermionicBounds

section ConfigPosMod4FermionicBounds
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner (permElectron)
open SpecsAux.FullScaleBESector (AgreesOnFermionicSector)
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
open SpecsAux.DyadicSubgridToeplitz128
  (NyqFine3D128 NyqGrid3D64 NyqParity3D nyq128Equiv3D nyq128Equiv3D_val kHead128)
open SpecsAux.DyadicSubgridToeplitz128 renaming
  anchorSubTarget3D → ancTgt, anchorParity3D → ancPar
open SpecsAux.DyadicSubgridToeplitz512AndShift (NyqFine3D512)
open SpecsAux.DyadicSubgridToeplitz512AndShift (nyq512ProjEquiv3D)
open Dyadic128CoulombMath (orbitCount47905 canonTriple128 tetRank65)
open Dyadic128OrbitTableCert (w128DualQ30)
open DyadicQft64WalkCircuit
  (nyqParity3DEquivFin8 qft64Ideal654Unitary qft64OffsetUnitary3D)
open CanonRank7Circuit (fineCoordOfReg21)
open MeasureBranchHadamardSem (bit_cases)
open TwosCompAndWire0Cancel
  (smToTwosSysUnitary smToTwos654SysUnitary smToTwosSysUnitary_conjTranspose
   fwdPermUnitary fwdPermUnitary_conj_diagonal karatsubaOutPhase3D karatsubaOutPhase3D_unit)
open TwosCompAndWire0Cancel renaming
  smToTwosProj3Perm → pSmP3
open FullSysCatSegmentBridge
  (FullSysQft654Bundle fullSysCoreWires fullSysQftCoreUnitary)
open TierBClean80Closure (tierBQftFull)
open ProjZ512QftAndTwist288 (cfgProjZ512 uProjPlus512_3D)
open NuclearTwistAndXor654Concrete (slot4CosetDiag18 sysNucDiag48)
open NuclearTwistAndXor654Concrete (uenSubGridKet48)
open NuclearTwistRealizes (uTwistParam slot2GlobalPhase)
open NuclearTwistRealizes (star_slot2GlobalPhase_mul_self)
open PosSlots24MergedVepBound (rProj24_sp smToTwos654SysUnitary_sa)
open PosSlots24MergedVepBound (vepFromSlot2Op)
open SingleAnchorFermionicPauliCap
  (nSub_cubic_mul_fermionicProjector_zero nSub_sp nTot_sp op_sp rEl_sp
   singleAnchorPairOp_cubic_mul_fermionicProjector_zero)
open Slot2Slot4QuantizedChannelBridge
  (veeSubGridKet veeSubGridKet_norm_sq veeSubGridKet_orthonormal)
open PosSlots24BranchConcrete
  (posCoreWires posPayloadWires headPhaseBitSpec tailAndSlackPhaseBitSpec posPhaseBit uPosPhase
   wSlot0Core wSlot1Core wSlot2Core wSubReject wIsHead wHeadThresh wRejectZero
   rNucIdx rAnchorIdx rPartnerIdx rTailKeep30 rHeadFine21 rCosetB0 rCosetB1 rElecSlot
   parity3OfReg slotSubGridCoord64 axisBitRev6)
open PosSlots24TopWrapper (rPosSubLocal)
open PosSlots24SemanticBridge
  (pos24_6_le_80 pos24_22_le_80 pos24_coreWires80_eq pos24_core80_eq_twist80
   pos24CutNyq pos24HeadU56 pos24HeadV56 pos24HeadW56 pos24HeadWeight56
   pos24OhPoint pos24_oh_head_sum_eq pos24TailSign pos24TailMag30 pos24TailSpan8
   castUnitaryPow2 mulUnitaryPow2 sysBlockAtPayloadGen)
open PosSlots24SemanticOracleConcrete80
  (QftPreservesCoset3 coreBetaOf coreBetaOf_lt3948 coreBetaOf_mid coreBetaOf_payload
   rAncFlag80 rAncFlag80_wire_ge_3948
   pos80Slot2Scale pos80Slot4Scale pos80Slot2Scale_pos pos80Slot4Scale_pos
   pos80Slot4TotNat
   norm_sysBlockAtPayloadGen_le_one sysBlockAtPayloadGen_conj_of_preserves
   sysBlockAtPayloadGen_mul_of_preserves uTwistParam_cast_comm_highReg_proj
   qftPreservesCoset3_of_eq_ideal uPosPhase_cast_comm_diagonal
   diagonal_comm_diagonal regVal_eq_of_wire_eq lt_sys_4034)
open PosSlots24SemanticOracleConcrete80 renaming
  coreBetaOf_payload → cB_pay, coreBetaOf → cBeta
open PosSlots24Semantic80Physics
  (HeadSupportIdx TailSupportIdx headWitnessPayload80 tailWitnessPayload80
   pos80SubIdx pos80IdealDist pos80WitnessOf pos80WitnessOf_eval_head
   sum_over_pos80IdealDist_support z2BitOfNat z2BitOfNat_val bitsVal_z2BitOfNat_of_lt
   tailSpan8_lt_two_pow_30)
open PosPostPrep80MergedVepS3 (muSlot2Ideal216 muSlot2Ideal218)
open PosPostPrep80MergedVepS3 (flipTailDpScratch80)
open MergedVepTopCoinCollapse
  (mProj24_sp mProjGridEquiv24 mProjBasisGen mProjBasisGen_eq_basisOutcomeProjector
   p80NucVal p80CosetP3 p80SetCosetAndNuc p80SetNucZero mergedSliceGen mergedCoherentOpGen
   norm_sum_proj_mul_blockDiag_le_one norm_conj_unitary_le_one)
open Pos24MergedVepPrepAndStitch
  (mergedPosSlot2WeightGen mergedPosSlot2BUnitTwosGen
   mergedPosSlot2Gen_smConj_eq smConj_comm_embedMatrix_of_idleTwos smToTwosSysUnitary_sa
   norm_mergedPosSlot2BUnitTwosGen_le_one)
open MergedVepLeaf4GridPerturbation
  (tierBB2RawId tierBB2Id tierBB4Id tierBB2Id_isHermitian tierBB4Id_isHermitian
   tierBQftFull_preservesCoset3)
open Pos24Slot2FermionicBridge
open Pos24Slot4FermionicBridge
open PosSlots24Q30Tight (eps4_q30_tight)
open PosHeadMod4_15476 (headEnBoolSpec headHitSetSpec)
open PosS3Bounds
  (headPhaseBitMod4Spec posPhaseBitMod4 uPosPhaseRealMod4 canonPosCoreBits
    posPhaseBitMod4_eq_of_coin0 pos24ConjCore80Of sysBlock80Of coherentSysOp80Of tierBB2RawIdOf
    tierBB2IdOf tierBB4IdOf pos24ConjCore80Mod4Of sysBlock80Mod4Of coherentSysOp80Mod4Of
    mergedCoherentOp80Mod4Of tierBB2RawIdMod4Of tierBB2IdMod4Of tierBB4IdMod4Of tierBB2RawIdMod4
    tierBB2IdMod4 tierBB4IdMod4)

-- ============================================================================
-- Section 2: Wire-Invariance and Head/Tail Splitting Lemmas for `posPhaseBitMod4`
-- ============================================================================

theorem canonPosCoreBits_eq_of_active (β : BitAssignment posCoreWires) (w : Wire posCoreWires)
    (h : ¬((3924 ≤ w.val ∧ w.val < 3948) ∨ (3951 ≤ w.val ∧ w.val < 3954) ∨ (4017 ≤ w.val ∧
    w.val < 4033))) : canonPosCoreBits β w = β w := ite_eq_right h

private theorem canon_regVal_eq {k : ℕ} (r : QRegister k posCoreWires)
    (β : BitAssignment posCoreWires)
    (h : ∀ i : Fin k, ¬((3924 ≤ (r i).val ∧ (r i).val < 3948) ∨
      (3951 ≤ (r i).val ∧ (r i).val < 3954) ∨ (4017 ≤ (r i).val ∧ (r i).val < 4033))) :
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal r (canonPosCoreBits β) =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal r β :=
  congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun i ↦
    canonPosCoreBits_eq_of_active β _ (h i))

private theorem canon_fine21_eq (β : BitAssignment posCoreWires) :
    fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) (canonPosCoreBits β) =
      fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β := by
  funext w
  dsimp [fineCoordOfReg21]
  exact Fin.ext (canon_regVal_eq _ β fun i ↦ by revert w i; decide)

private theorem canon_parity3_eq (r : QRegister 3 posCoreWires) (β : BitAssignment posCoreWires)
    (h : ∀ w : Fin 3, ¬((3924 ≤ (r w).val ∧ (r w).val < 3948) ∨
      (3951 ≤ (r w).val ∧ (r w).val < 3954) ∨ (4017 ≤ (r w).val ∧ (r w).val < 4033))) :
    parity3OfReg r (canonPosCoreBits β) = parity3OfReg r β :=
  funext fun w ↦ congrArg (fun x ↦ decide (x = 1)) (canonPosCoreBits_eq_of_active β _ (h w))

theorem headEnBoolSpec_canonPosCoreBits (β : BitAssignment posCoreWires) :
    headEnBoolSpec (canonPosCoreBits β) = headEnBoolSpec β := by
  unfold headEnBoolSpec
  simp only [
    canonPosCoreBits_eq_of_active β (wSlot2Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wSlot1Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wSlot0Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wSubReject (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wIsHead (QRegExt.ofFin posCoreWires)) (by decide),
    canon_regVal_eq (rNucIdx (QRegExt.ofFin posCoreWires)) β (fun i ↦ by revert i; decide),
    canon_regVal_eq (rAnchorIdx (QRegExt.ofFin posCoreWires)) β (fun i ↦ by revert i; decide)]

theorem slotSubGridCoord64_canonPosCoreBits (β : BitAssignment posCoreWires) (e : Fin 218) :
    slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) (canonPosCoreBits β) =
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β := by
  funext w
  apply Fin.ext
  dsimp [slotSubGridCoord64]
  refine canon_regVal_eq _ β fun i ↦ ?_
  have := e.isLt
  have := w.isLt
  have := i.isLt
  have hval : (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w i).val =
      18 * e.val + (6 * w.val + (5 - i.val)) := rfl
  omega

theorem headHitSetSpec_canonPosCoreBits (β : BitAssignment posCoreWires) :
    headHitSetSpec (canonPosCoreBits β) = headHitSetSpec β := by
  unfold headHitSetSpec
  simp only [
    canonPosCoreBits_eq_of_active β (wSlot0Core (QRegExt.ofFin posCoreWires)) (by decide),
    canon_fine21_eq β,
    canon_parity3_eq (rCosetB0 (QRegExt.ofFin posCoreWires)) β (fun w ↦ by revert w; decide),
    slotSubGridCoord64_canonPosCoreBits β]

theorem tailAndSlackPhaseBitSpec_canonPosCoreBits (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) : tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign
    tailMag30 (canonPosCoreBits β) = tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign
    tailMag30 β := by
  unfold tailAndSlackPhaseBitSpec
  simp only [
    canonPosCoreBits_eq_of_active β (wSlot2Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wSlot1Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wSlot0Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wSubReject (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wIsHead (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wRejectZero (QRegExt.ofFin posCoreWires)) (by decide),
    canon_regVal_eq (rNucIdx (QRegExt.ofFin posCoreWires)) β (fun i ↦ by revert i; decide),
    canon_regVal_eq (rAnchorIdx (QRegExt.ofFin posCoreWires)) β (fun i ↦ by revert i; decide),
    canon_regVal_eq (rPartnerIdx (QRegExt.ofFin posCoreWires)) β (fun i ↦ by revert i; decide),
    canon_regVal_eq (rTailKeep30 (QRegExt.ofFin posCoreWires)) β (fun i ↦ by revert i; decide),
    canon_parity3_eq (rCosetB0 (QRegExt.ofFin posCoreWires)) β (fun w ↦ by revert w; decide),
    canon_parity3_eq (rCosetB1 (QRegExt.ofFin posCoreWires)) β (fun w ↦ by revert w; decide),
    slotSubGridCoord64_canonPosCoreBits β]

theorem headPhaseBitMod4Spec_canonPosCoreBits (β : BitAssignment posCoreWires) :
    headPhaseBitMod4Spec (canonPosCoreBits β) = headPhaseBitMod4Spec β := by
  unfold headPhaseBitMod4Spec
  simp only [headEnBoolSpec_canonPosCoreBits β, headHitSetSpec_canonPosCoreBits β,
    canonPosCoreBits_eq_of_active β (wSlot0Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wHeadThresh (QRegExt.ofFin posCoreWires)) (by decide)]

theorem posPhaseBitMod4_canonPosCoreBits (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) : posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30
    (canonPosCoreBits β) = posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30 β := by
  unfold posPhaseBitMod4
  rw [headPhaseBitMod4Spec_canonPosCoreBits, tailAndSlackPhaseBitSpec_canonPosCoreBits]

theorem canonPosCoreBits_eq_of_eq_active (β₁ β₂ : BitAssignment posCoreWires) (heq : ∀ w :
    Wire posCoreWires, ¬((3924 ≤ w.val ∧ w.val < 3948) ∨ (3951 ≤ w.val ∧ w.val < 3954) ∨ (4017
    ≤ w.val ∧ w.val < 4033)) → β₁ w = β₂ w) : canonPosCoreBits β₁ = canonPosCoreBits β₂ := by
  funext w; unfold canonPosCoreBits
  split_ifs with h
  · rfl
  · exact heq w h

theorem posPhaseBitMod4_eq_of_eq_active (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (β₁ β₂ : BitAssignment posCoreWires) (heq : ∀ w : Wire posCoreWires, ¬((3924 ≤ w.val ∧
    w.val < 3948) ∨ (3951 ≤ w.val ∧ w.val < 3954) ∨ (4017 ≤ w.val ∧ w.val < 4033)) → β₁ w = β₂
    w) : posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30 β₁ = posPhaseBitMod4
    slot2SwappedTo0 tailSign tailMag30 β₂ := by
  rw [← posPhaseBitMod4_canonPosCoreBits slot2SwappedTo0 tailSign tailMag30 β₁,
      ← posPhaseBitMod4_canonPosCoreBits slot2SwappedTo0 tailSign tailMag30 β₂,
      canonPosCoreBits_eq_of_eq_active β₁ β₂ heq]

theorem headPhaseBitMod4Spec_of_wIsHead_zero (β : BitAssignment posCoreWires)
    (h0 : β (wIsHead (QRegExt.ofFin posCoreWires)) = 0) :
    headPhaseBitMod4Spec β = false := by
  have hen : headEnBoolSpec β = false := by
    unfold headEnBoolSpec
    have h1 : (β (wIsHead (QRegExt.ofFin posCoreWires)) == 1) = false := by
      rw [h0]; rfl
    dsimp only
    rw [h1, Bool.and_false]
  unfold headPhaseBitMod4Spec
  dsimp only
  rw [hen]; rfl

theorem headPhaseBitSpec_of_wIsHead_zero (β : BitAssignment posCoreWires)
    (h0 : β (wIsHead (QRegExt.ofFin posCoreWires)) = 0) : headPhaseBitSpec β = false := by
  unfold headPhaseBitSpec
  have h1 : (β (wIsHead (QRegExt.ofFin posCoreWires)) == 1) = false := by
    rw [h0]; rfl
  dsimp only
  rw [h1, Bool.and_false]; rfl

theorem posPhaseBitMod4_eq_posPhaseBit_of_wIsHead_zero (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) (h0 : β (wIsHead (QRegExt.ofFin posCoreWires)) = 0) :
    posPhaseBitMod4 slot2SwappedTo0 tailSign tailMag30 β = posPhaseBit slot2SwappedTo0
    tailSign tailMag30 β := by
  unfold posPhaseBitMod4 posPhaseBit
  rw [headPhaseBitMod4Spec_of_wIsHead_zero β h0, headPhaseBitSpec_of_wIsHead_zero β h0]

private theorem tailAndSlackPhaseBitSpec_eq_of_wIsHead_one
    (tM₁ tM₂ : Fin orbitCount47905 → Fin (2 ^ 30)) (β : BitAssignment posCoreWires)
    (hHead : β (wIsHead (QRegExt.ofFin posCoreWires)) = 1) :
    tailAndSlackPhaseBitSpec true pos24TailSign tM₁ β =
      tailAndSlackPhaseBitSpec true pos24TailSign tM₂ β := by
  rw [MergedVepTopCoinCollapse.tailAndSlackPhaseBitSpec_eq_orbitBody true pos24TailSign tM₁ β,
      MergedVepTopCoinCollapse.tailAndSlackPhaseBitSpec_eq_orbitBody true pos24TailSign tM₂ β]
  have h1 : (β (wIsHead (QRegExt.ofFin posCoreWires)) == 1) = true := by
    rw [hHead]
    rfl
  dsimp only
  rw [h1, ite_eq_left rfl, ite_eq_left rfl]

theorem posPhaseBitMod4_eq_of_wIsHead_one (tM₁ tM₂ : Fin orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) (hHead : β (wIsHead (QRegExt.ofFin posCoreWires)) = 1) :
    posPhaseBitMod4 true pos24TailSign tM₁ β = posPhaseBitMod4 true pos24TailSign tM₂ β :=
  congrArg (Bool.xor (headPhaseBitMod4Spec β))
    (tailAndSlackPhaseBitSpec_eq_of_wIsHead_one tM₁ tM₂ β hHead)

theorem posPhaseBit_eq_of_wIsHead_one (tM₁ tM₂ : Fin orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) (hHead : β (wIsHead (QRegExt.ofFin posCoreWires)) = 1) :
    posPhaseBit true pos24TailSign tM₁ β = posPhaseBit true pos24TailSign tM₂ β :=
  congrArg (Bool.xor (headPhaseBitSpec β))
    (tailAndSlackPhaseBitSpec_eq_of_wIsHead_one tM₁ tM₂ β hHead)

theorem posPhaseBitMod4_sub_eq_posPhaseBit_sub (tM₁ tM₂ : Fin orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) :
    (if posPhaseBitMod4 true pos24TailSign tM₁ β then (-1 : ℂ) else 1) -
    (if posPhaseBitMod4 true pos24TailSign tM₂ β then (-1 : ℂ) else 1) =
    (if posPhaseBit true pos24TailSign tM₁ β then (-1 : ℂ) else 1) -
    (if posPhaseBit true pos24TailSign tM₂ β then (-1 : ℂ) else 1) := by
  rcases bit_cases (β (wIsHead (QRegExt.ofFin posCoreWires))) with h0 | h1
  · rw [posPhaseBitMod4_eq_posPhaseBit_of_wIsHead_zero true pos24TailSign tM₁ β h0,
        posPhaseBitMod4_eq_posPhaseBit_of_wIsHead_zero true pos24TailSign tM₂ β h0]
  · rw[posPhaseBitMod4_eq_of_wIsHead_one tM₁ tM₂ β h1,
      posPhaseBit_eq_of_wIsHead_one tM₁ tM₂ β h1, sub_self, sub_self]

-- ============================================================================
-- Section 3: `wSlice80` Conjugation, `rProj24_sp` Commutation, and Block-Diagonality
-- ============================================================================

/-- Outer QFT and nuclear-twist conjugation unitary on `fullSysCoreWires 80`. -/
noncomputable def uOutCore80 (cfg : Configuration) : Unitary (2 ^ (fullSysCoreWires 80)) :=
    mulUnitaryPow2 (fullSysQftCoreUnitary pos24_6_le_80 tierBQftFull)
    (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg) pos24_core80_eq_twist80

/-- Payload system-block slice of `uOutCore80` at `(s0, p80)`. -/
noncomputable def wSlice80 (cfg : Configuration) (s0 : Bool) (p80 : BitAssignment 80) :
    Operator (2 ^ systemQubits) :=
  sysBlockAtPayloadGen pos24_coreWires80_eq.symm (uOutCore80 cfg).1 s0 p80

theorem norm_wSlice80_le_one (cfg : Configuration) (s0 : Bool) (p80 : BitAssignment 80) :
    ‖wSlice80 cfg s0 p80‖ ≤ 1 :=
  norm_sysBlockAtPayloadGen_le_one pos24_coreWires80_eq.symm (uOutCore80 cfg) s0 p80

theorem norm_wSlice80_conj_le {D : ℕ} (W M : Operator D) (hW : ‖W‖ ≤ 1) :
    ‖Wᴴ * M * W‖ ≤ ‖M‖ := by
  have hWh : ‖Wᴴ‖ ≤ 1 := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hW
  calc ‖Wᴴ * M * W‖
      ≤ ‖Wᴴ * M‖ * ‖W‖ := norm_mul_le _ _
    _ ≤ (‖Wᴴ‖ * ‖M‖) * ‖W‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖M‖) * 1 :=
        mul_le_mul (mul_le_mul hWh le_rfl (norm_nonneg _) zero_le_one) hW
          (norm_nonneg _) (by linarith [norm_nonneg M])
    _ = ‖M‖ := by ring

section HpowStep_11
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_11 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
private theorem diagonalSignUnitaryN_cast_comm_diagonal (φ : BitAssignment posCoreWires → Bool)
    (d : Fin (2 ^ (fullSysCoreWires 80)) → ℂ) :
    (castUnitaryPow2 pos24_coreWires80_eq.symm (BchCubeDecoder.diagonalSignUnitaryN φ)).1 *
      Matrix.diagonal d = Matrix.diagonal d *
      (castUnitaryPow2 pos24_coreWires80_eq.symm (BchCubeDecoder.diagonalSignUnitaryN φ)).1 := by
  have hEq : (castUnitaryPow2 pos24_coreWires80_eq.symm
      (BchCubeDecoder.diagonalSignUnitaryN φ)).1 =
      Matrix.diagonal (fun x : Fin (2 ^ (fullSysCoreWires 80)) ↦
        if φ (basisBits posCoreWires (pos24_coreWires80_eq ▸ x)) then (-1 : ℂ) else 1) := by
    have h : posCoreWires = fullSysCoreWires 80 := pos24_coreWires80_eq.symm
    cases h
    rfl
  rw [hEq]
  exact diagonal_comm_diagonal _ _

end HpowStep_11
section HpowStep_12
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_12 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
private theorem sysBlockAtPayloadGen_conj_diagSign (qft : FullSysQft654Bundle)
    (hQftPres : ∀ a, (fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
      rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (fullSysQftCoreUnitary pos24_6_le_80 qft).1)
    (cfg : Configuration) (φ : BitAssignment posCoreWires → Bool) (s0 : Bool)
    (p80 : BitAssignment 80) :
    let U_out := (fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
      (castUnitaryPow2 pos24_core80_eq_twist80.symm
        (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1
    let D_pos := (castUnitaryPow2 pos24_coreWires80_eq.symm
      (BchCubeDecoder.diagonalSignUnitaryN φ)).1
    sysBlockAtPayloadGen pos24_coreWires80_eq.symm (U_outᴴ * D_pos * U_out) s0 p80 =
      (sysBlockAtPayloadGen pos24_coreWires80_eq.symm U_out s0 p80)ᴴ *
        Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
          if φ (coreBetaOf s0 p80 z) then (-1 : ℂ) else 1) *
        sysBlockAtPayloadGen pos24_coreWires80_eq.symm U_out s0 p80 := by
  intro U_out D_pos
  have hTw_comm : ∀ a, (castUnitaryPow2 pos24_core80_eq_twist80.symm
      (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1 *
      rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (castUnitaryPow2 pos24_core80_eq_twist80.symm
      (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1 :=
    fun a ↦ uTwistParam_cast_comm_highReg_proj pos24_core80_eq_twist80.symm cfg rAncFlag80
      rAncFlag80_wire_ge_3948 a
  have hD_comm : ∀ a, D_pos * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * D_pos := fun a ↦ by
    rw [QRegister.basisOutcomeProjector_eq_diagonal]
    exact diagonalSignUnitaryN_cast_comm_diagonal φ _
  have hOut_comm : ∀ a, U_out * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * U_out := fun a ↦ by
    dsimp only [U_out]
    rw [Matrix.mul_assoc, hTw_comm a, ← Matrix.mul_assoc, hQftPres a, Matrix.mul_assoc]
  have hDOut_comm : ∀ a, (D_pos * U_out) * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (D_pos * U_out) := fun a ↦ by
    rw [Matrix.mul_assoc, hOut_comm a, ← Matrix.mul_assoc, hD_comm a, Matrix.mul_assoc]
  rw [sysBlockAtPayloadGen_conj_of_preserves pos24_coreWires80_eq.symm U_out D_pos s0 p80
        (pr_a _ hOut_comm s0 p80) (pr_a _ hDOut_comm s0 p80),
      sb_ds φ pos24_coreWires80_eq.symm s0 p80]

end HpowStep_12
theorem sysBlock80Of_eq_wSlice80_conj (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (s0 : Bool) (p80 : BitAssignment 80) : sysBlock80Of tM tierBQftFull
    cfg s0 p80 = (wSlice80 cfg s0 p80)ᴴ * Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦ if
    posPhaseBit true pos24TailSign tM (coreBetaOf s0 p80 z) then (-1 : ℂ) else 1) * wSlice80
    cfg s0 p80 :=
  sysBlockAtPayloadGen_conj_diagSign tierBQftFull
    (qf_an tierBQftFull tierBQftFull_preservesCoset3) cfg (posPhaseBit true pos24TailSign tM) s0
    p80

theorem uPosPhaseRealMod4_cast_comm_diagonal (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (d : Fin (2 ^ (fullSysCoreWires 80)) → ℂ) : (castUnitaryPow2 pos24_coreWires80_eq.symm
    (uPosPhaseRealMod4 slot2SwappedTo0 tailSign tailMag30)).1 * Matrix.diagonal d =
    Matrix.diagonal d * (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhaseRealMod4
    slot2SwappedTo0 tailSign tailMag30)).1 :=
  diagonalSignUnitaryN_cast_comm_diagonal _ d

theorem sysBlock80Mod4Of_eq_wSlice80_conj (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (s0 : Bool) (p80 : BitAssignment 80) : sysBlock80Mod4Of tM
    tierBQftFull cfg s0 p80 = (wSlice80 cfg s0 p80)ᴴ * Matrix.diagonal (fun z : Fin (2 ^
    systemQubits) ↦ if posPhaseBitMod4 true pos24TailSign tM (coreBetaOf s0 p80 z) then (-1 :
    ℂ) else 1) * wSlice80 cfg s0 p80 :=
  sysBlockAtPayloadGen_conj_diagSign tierBQftFull
    (qf_an tierBQftFull tierBQftFull_preservesCoset3) cfg (posPhaseBitMod4 true pos24TailSign tM)
    s0 p80

section HpowStep_13
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_13 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem wSlice80_factor (cfg : Configuration) (s0 : Bool) (p80 : BitAssignment 80) : wSlice80
    cfg s0 p80 = sysBlockAtPayloadGen pos24_coreWires80_eq.symm
    (fullSysQftCoreUnitary pos24_6_le_80 tierBQftFull).1 s0 p80 * sysBlockAtPayloadGen
    pos24_coreWires80_eq.symm (castUnitaryPow2 pos24_core80_eq_twist80.symm
    (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1 s0 p80 := by
  let U_tw := (castUnitaryPow2 pos24_core80_eq_twist80.symm
    (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1
  have hTw_comm : ∀ a, U_tw * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * U_tw := fun a ↦ uTwistParam_cast_comm_highReg_proj
      pos24_core80_eq_twist80.symm cfg rAncFlag80 rAncFlag80_wire_ge_3948 a
  unfold wSlice80 uOutCore80
  exact sysBlockAtPayloadGen_mul_of_preserves pos24_coreWires80_eq.symm _ U_tw s0 p80
    (pr_a _ hTw_comm s0 p80)

end HpowStep_13
private theorem coreBetaOf_eq_of_agreeOutside_rProj24 (s0 : Bool) (p80 : BitAssignment 80)
    {z' z : Fin (2 ^ systemQubits)} (hag : rProj24_sp.AgreeOutside z' z) (w : Wire posCoreWires)
    (hw : ¬((3924 ≤ w.val ∧ w.val < 3948) ∨ (3951 ≤ w.val ∧ w.val < 3954) ∨
      (4017 ≤ w.val ∧ w.val < 4033))) :
    coreBetaOf s0 p80 z' w = coreBetaOf s0 p80 z w := by
  by_cases hlt : w.val < 3924
  · have hsys : w.val < systemQubits := by
      dsimp [systemQubits, numElectrons, electronBits, projectileBits]
      omega
    let qS : Wire systemQubits := ⟨w.val, hsys⟩
    have hw_eq : w = ⟨qS.val, Nat.lt_trans qS.isLt lt_sys_4034⟩ := rfl
    rw [hw_eq, coreBetaOf_lt3948 s0 p80 z' qS, coreBetaOf_lt3948 s0 p80 z qS]
    refine hag qS ?_
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    have := i.isLt
    dsimp [rProj24_sp, qS, qreg_block_wires_slot2] at hv
    omega
  · have hge3948 : 3948 ≤ w.val := by
      have : ¬(3924 ≤ w.val ∧ w.val < 3948) := fun h ↦ hw (Or.inl h)
      omega
    by_cases hlt3954 : w.val < 3954
    · rw [coreBetaOf_mid s0 p80 z' w hge3948 hlt3954, coreBetaOf_mid s0 p80 z w hge3948 hlt3954]
    · have hsub : w.val - 3954 < 80 := by
        have := w.isLt
        dsimp [posCoreWires] at this
        omega
      have hw_p : w = rPosSubLocal ⟨w.val - 3954, hsub⟩ := by
        ext
        change w.val = 3954 + (w.val - 3954)
        omega
      rw [hw_p, coreBetaOf_payload, coreBetaOf_payload]

private theorem coreBetaOf_eq_of_payload_eq_at (s0 : Bool) (p₁ p₂ : BitAssignment 80)
    (z : Fin (2 ^ systemQubits)) (q : Wire posCoreWires)
    (hp : ∀ hsub : q.val - 3954 < 80, 3954 ≤ q.val →
      p₁ ⟨q.val - 3954, hsub⟩ = p₂ ⟨q.val - 3954, hsub⟩) :
    coreBetaOf s0 p₁ z q = coreBetaOf s0 p₂ z q := by
  by_cases hlt3954 : q.val < 3954
  · by_cases hlt3948 : q.val < 3948
    · have hsys : q.val < systemQubits := by
        dsimp [systemQubits, numElectrons, electronBits, projectileBits]
        omega
      let qS : Wire systemQubits := ⟨q.val, hsys⟩
      have hq_eq : q = ⟨qS.val, Nat.lt_trans qS.isLt lt_sys_4034⟩ := rfl
      rw [hq_eq, coreBetaOf_lt3948 s0 p₁ z qS, coreBetaOf_lt3948 s0 p₂ z qS]
    · have hgeSys : systemQubits ≤ q.val := by
        dsimp [systemQubits, numElectrons, electronBits, projectileBits]
        omega
      rw [coreBetaOf_mid s0 p₁ z q hgeSys hlt3954, coreBetaOf_mid s0 p₂ z q hgeSys hlt3954]
  · have hsub : q.val - 3954 < 80 := by
      have := q.isLt
      dsimp [posCoreWires] at this
      omega
    have hq_p : q = rPosSubLocal ⟨q.val - 3954, hsub⟩ := by
      ext
      change q.val = 3954 + (q.val - 3954)
      omega
    rw [hq_p]
    change coreBetaOf s0 p₁ z (rPosSubLocal ⟨q.val - 3954, hsub⟩) =
      coreBetaOf s0 p₂ z (rPosSubLocal ⟨q.val - 3954, hsub⟩)
    rw [coreBetaOf_payload, coreBetaOf_payload]
    exact hp hsub (by omega)

theorem posPhaseBitMod4_coreBetaOf_eq_of_agreeOutside_rProj24
    (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (s0 : Bool) (p80 : BitAssignment 80)
    {z' z : Fin (2 ^ systemQubits)} (hag : rProj24_sp.AgreeOutside z' z) : posPhaseBitMod4
    true pos24TailSign tM (coreBetaOf s0 p80 z') = posPhaseBitMod4 true pos24TailSign tM
    (coreBetaOf s0 p80 z) :=
  posPhaseBitMod4_eq_of_eq_active true pos24TailSign tM _ _
    (coreBetaOf_eq_of_agreeOutside_rProj24 s0 p80 hag)

section HpowStep_14
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_14 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem wSlice80_slot2_comm_rProj24 (cfg : Configuration) (p80 : BitAssignment 80)
    (N : Operator (2 ^ 24)) : wSlice80 cfg false p80 * rProj24_sp.embedMatrix N =
    rProj24_sp.embedMatrix N * wSlice80 cfg false p80 := by
  have hW_eq : wSlice80 cfg false p80 = (((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary
      (qft64OffsetUnitary3D (payloadB1Parity p80))).prod).1 * (slot2RawKickDiag cfg
      (payloadNucNat p80) * (fwdPermUnitary ((barrelSysPerm (payloadAncNat p80)).trans
      xor32SysPerm)).1)) := by
    have hTwEq : (castUnitaryPow2 pos24_core80_eq_twist80.symm
        (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1 =
        (slot2UTwistParam true pos24_22_le_80 cfg).1 := rfl
    rw [wSlice80_factor cfg false p80, hTwEq,
        sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl false p80,
        sysBlockAtPayloadGen_uTwist_slot2_eq cfg p80]
  rw [hW_eq]
  set Q_op := ((List.ofFn fun e : Fin 218 ↦
      (rEl_sp e).embedUnitary (qft64OffsetUnitary3D (payloadB1Parity p80))).prod).1
  set K_op := slot2RawKickDiag cfg (payloadNucNat p80)
  set P_op := (fwdPermUnitary ((barrelSysPerm (payloadAncNat p80)).trans xor32SysPerm)).1
  have hq_c : Q_op * rProj24_sp.embedMatrix N = rProj24_sp.embedMatrix N * Q_op :=
    list_ofFn_rEl_comm_rProj24 (fun _ ↦ qft64OffsetUnitary3D (payloadB1Parity p80)) N
  have hk_c : K_op * rProj24_sp.embedMatrix N = rProj24_sp.embedMatrix N * K_op :=
    slot2RawKickDiag_comm_rProj24 cfg (payloadNucNat p80) N
  have hp_c : P_op * rProj24_sp.embedMatrix N = rProj24_sp.embedMatrix N * P_op := by
    dsimp only [P_op]
    rw [TwosCompAndWire0Cancel.fwdPermUnitary_trans, Submonoid.coe_mul, Matrix.mul_assoc,
      fwdPermUnitary_barrel_comm_rProj24 (payloadAncNat p80) N, ← Matrix.mul_assoc,
      fwdPermUnitary_xor32_comm_rProj24 N, Matrix.mul_assoc]
  calc (Q_op * (K_op * P_op)) * rProj24_sp.embedMatrix N
    _ = Q_op * (K_op * (P_op * rProj24_sp.embedMatrix N)) := by simp only [Matrix.mul_assoc]
    _ = Q_op * (K_op * (rProj24_sp.embedMatrix N * P_op)) := by rw [hp_c]
    _ = Q_op * ((K_op * rProj24_sp.embedMatrix N) * P_op) := by simp only [Matrix.mul_assoc]
    _ = Q_op * ((rProj24_sp.embedMatrix N * K_op) * P_op) := by rw [hk_c]
    _ = (Q_op * rProj24_sp.embedMatrix N) * (K_op * P_op) := by simp only [Matrix.mul_assoc]
    _ = rProj24_sp.embedMatrix N * (Q_op * (K_op * P_op)) := by
      rw [hq_c]; simp only [Matrix.mul_assoc]

end HpowStep_14
private theorem wSlice80_conj_diag_comm_rProj24 (cfg : Configuration) (p80 : BitAssignment 80)
    (φ : BitAssignment posCoreWires → Bool)
    (hag_φ : ∀ {z' z : Fin (2 ^ systemQubits)}, rProj24_sp.AgreeOutside z' z →
      φ (coreBetaOf false p80 z') = φ (coreBetaOf false p80 z))
    (M : Operator (2 ^ 24)) :
    ((wSlice80 cfg false p80)ᴴ *
        Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
          if φ (coreBetaOf false p80 z) then (-1 : ℂ) else 1) *
        wSlice80 cfg false p80) *
      rProj24_sp.embedMatrix M =
    rProj24_sp.embedMatrix M *
      ((wSlice80 cfg false p80)ᴴ *
        Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
          if φ (coreBetaOf false p80 z) then (-1 : ℂ) else 1) *
        wSlice80 cfg false p80) := by
  set W := wSlice80 cfg false p80
  have hW_comm : W * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * W :=
    wSlice80_slot2_comm_rProj24 cfg p80 M
  have hW_adj : Wᴴ * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * Wᴴ := by
    have h1 := congrArg Matrix.conjTranspose (wSlice80_slot2_comm_rProj24 cfg p80 Mᴴ)
    simpa only [Matrix.conjTranspose_mul, QRegister.embedMatrix_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using h1.symm
  have hD_comm := diagonal_comm_embedMatrix_of_agreeOutside rProj24_sp
    (fun z : Fin (2 ^ systemQubits) ↦ if φ (coreBetaOf false p80 z) then (-1 : ℂ) else 1)
    (fun z' z hag ↦ by rw [hag_φ hag]) M
  rw [Matrix.mul_assoc, hW_comm, ← Matrix.mul_assoc,
      Matrix.mul_assoc Wᴴ, hD_comm, ← Matrix.mul_assoc Wᴴ, hW_adj]
  simp only [Matrix.mul_assoc]

theorem sysBlock80Mod4Of_slot2_comm_rProj24 (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p80 : BitAssignment 80) (M : Operator (2 ^ 24)) : sysBlock80Mod4Of
    tM tierBQftFull cfg false p80 * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M *
    sysBlock80Mod4Of tM tierBQftFull cfg false p80 := by
  rw [sysBlock80Mod4Of_eq_wSlice80_conj]
  exact wSlice80_conj_diag_comm_rProj24 cfg p80 (posPhaseBitMod4 true pos24TailSign tM)
    (posPhaseBitMod4_coreBetaOf_eq_of_agreeOutside_rProj24 tM false p80) M

theorem tierBB2RawIdMod4Of_comm_rProj24 (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (M : Operator (2 ^ 24)) : tierBB2RawIdMod4Of tM cfg *
    rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * tierBB2RawIdMod4Of tM cfg := by
  unfold tierBB2RawIdMod4Of coherentSysOp80Mod4Of
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p80 _ ↦ ?_
  rw [smul_mul_assoc, mul_smul_comm, sysBlock80Mod4Of_slot2_comm_rProj24 tM cfg p80 M]

theorem tierBB2RawIdMod4_comm_rProj24 (c : Configuration) (M : Operator (2 ^ 24)) :
    tierBB2RawIdMod4 c * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M *
    tierBB2RawIdMod4 c := tierBB2RawIdMod4Of_comm_rProj24 pos24TailMag30 c M

theorem headPhaseBitSpec_canonPosCoreBits (β : BitAssignment posCoreWires) :
    headPhaseBitSpec (canonPosCoreBits β) = headPhaseBitSpec β := by
  unfold headPhaseBitSpec
  simp only [
    canonPosCoreBits_eq_of_active β (wSlot2Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wSlot1Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wSlot0Core (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wSubReject (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wIsHead (QRegExt.ofFin posCoreWires)) (by decide),
    canonPosCoreBits_eq_of_active β (wHeadThresh (QRegExt.ofFin posCoreWires)) (by decide),
    canon_regVal_eq (rNucIdx (QRegExt.ofFin posCoreWires)) β (fun i ↦ by revert i; decide),
    canon_regVal_eq (rAnchorIdx (QRegExt.ofFin posCoreWires)) β (fun i ↦ by revert i; decide),
    canon_fine21_eq β,
    canon_parity3_eq (rCosetB0 (QRegExt.ofFin posCoreWires)) β (fun w ↦ by revert w; decide),
    slotSubGridCoord64_canonPosCoreBits β]

theorem posPhaseBit_eq_of_eq_active (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (β₁ β₂ : BitAssignment posCoreWires) (heq : ∀ w : Wire posCoreWires, ¬((3924 ≤ w.val ∧
    w.val < 3948) ∨ (3951 ≤ w.val ∧ w.val < 3954) ∨ (4017 ≤ w.val ∧ w.val < 4033)) → β₁ w = β₂
    w) : posPhaseBit slot2SwappedTo0 tailSign tailMag30 β₁ = posPhaseBit slot2SwappedTo0
    tailSign tailMag30 β₂ := by
  have hCan : ∀ β, posPhaseBit slot2SwappedTo0 tailSign tailMag30 (canonPosCoreBits β) =
      posPhaseBit slot2SwappedTo0 tailSign tailMag30 β := fun β ↦ by
    unfold posPhaseBit
    rw [headPhaseBitSpec_canonPosCoreBits, tailAndSlackPhaseBitSpec_canonPosCoreBits]
  rw [← hCan β₁, ← hCan β₂, canonPosCoreBits_eq_of_eq_active β₁ β₂ heq]

theorem posPhaseBit_coreBetaOf_eq_of_agreeOutside_rProj24_of_tM
    (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (s0 : Bool) (p80 : BitAssignment 80)
    {z' z : Fin (2 ^ systemQubits)} (hag : rProj24_sp.AgreeOutside z' z) : posPhaseBit true
    pos24TailSign tM (coreBetaOf s0 p80 z') = posPhaseBit true pos24TailSign tM
    (coreBetaOf s0 p80 z) :=
  posPhaseBit_eq_of_eq_active true pos24TailSign tM _ _
    (coreBetaOf_eq_of_agreeOutside_rProj24 s0 p80 hag)

theorem sysBlock80Of_slot2_comm_rProj24 (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p80 : BitAssignment 80) (M : Operator (2 ^ 24)) : sysBlock80Of tM
    tierBQftFull cfg false p80 * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M *
    sysBlock80Of tM tierBQftFull cfg false p80 := by
  rw [sysBlock80Of_eq_wSlice80_conj]
  exact wSlice80_conj_diag_comm_rProj24 cfg p80 (posPhaseBit true pos24TailSign tM)
    (posPhaseBit_coreBetaOf_eq_of_agreeOutside_rProj24_of_tM tM false p80) M

theorem sysBlock80Mod4_projDiag_slot2 (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p : BitAssignment 80) (x' x : Fin (2 ^ systemQubits))
    (hne : mProj24_sp.extractIndex x' ≠ mProj24_sp.extractIndex x) : sysBlock80Mod4Of tM
    tierBQftFull cfg false p x' x = 0 :=
    PosSlots24SemanticOracleConcrete80.entry_zero_of_comm_basisOutcomeProjector mProj24_sp _
    (fun _ ↦ sysBlock80Mod4Of_slot2_comm_rProj24 tM cfg p _) x' x hne

theorem sysBlock80_projDiag_slot2 (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p : BitAssignment 80) (x' x : Fin (2 ^ systemQubits))
    (hne : mProj24_sp.extractIndex x' ≠ mProj24_sp.extractIndex x) : sysBlock80Of tM
    tierBQftFull cfg false p x' x = 0 :=
    PosSlots24SemanticOracleConcrete80.entry_zero_of_comm_basisOutcomeProjector mProj24_sp _
    (fun _ ↦ sysBlock80Of_slot2_comm_rProj24 tM cfg p _) x' x hne

-- ============================================================================
-- Section 4: `muSlot2Ideal216` / `muSlot2Ideal218` Fermionic Collapse Identities
-- ============================================================================

section HpowStep_15
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_15 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem blkMod4_eq_of_eq_outside_scratch16_of_tM (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p₁ p₂ : BitAssignment 80)
    (heq : ∀ j : Fin 80, ¬(63 ≤ j.val ∧ j.val < 79) → p₁ j = p₂ j) : sysBlock80Mod4Of tM
    tierBQftFull cfg false p₁ = sysBlock80Mod4Of tM tierBQftFull cfg false p₂ := by
  have hB1 : payloadB1Parity p₁ = payloadB1Parity p₂ := by
    funext w; apply Fin.ext; dsimp [payloadB1Parity]
    exact congrArg ZMod.val (heq ⟨w.val, by have := w.isLt; omega⟩ (by
      have :=
        w.isLt; dsimp; omega))
  have hNuc : payloadNucNat p₁ = payloadNucNat p₂ :=
    congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
      heq (pos80SubIdx 6 8 (by decide) j) (by have := j.isLt; dsimp [pos80SubIdx]; omega))
  have hAnc : payloadAncNat p₁ = payloadAncNat p₂ :=
    congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
      heq (pos80SubIdx 14 8 (by decide) j) (by have := j.isLt; dsimp [pos80SubIdx]; omega))
  have hTwEq : (castUnitaryPow2 pos24_core80_eq_twist80.symm (NuclearTwistRealizes.uTwistParam
      true pos24_22_le_80 cfg)).1 = (slot2UTwistParam true pos24_22_le_80 cfg).1 := rfl
  have hW : wSlice80 cfg false p₁ = wSlice80 cfg false p₂ := by
    rw [wSlice80_factor cfg false p₁, wSlice80_factor cfg false p₂, hTwEq,
        sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl false p₁,
        sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl false p₂,
        sysBlockAtPayloadGen_uTwist_slot2_eq cfg p₁,
        sysBlockAtPayloadGen_uTwist_slot2_eq cfg p₂, hB1, hNuc, hAnc]
  have hDiag : ∀ z : Fin (2 ^ systemQubits),
      posPhaseBitMod4 true pos24TailSign tM (coreBetaOf false p₁ z) =
        posPhaseBitMod4 true pos24TailSign tM (coreBetaOf false p₂ z) := fun z ↦
    posPhaseBitMod4_eq_of_eq_active true pos24TailSign tM _ _ fun w hw ↦
      coreBetaOf_eq_of_payload_eq_at false p₁ p₂ z w fun hsub hge ↦
        heq ⟨w.val - 3954, hsub⟩ (fun h63 ↦ hw (Or.inr (Or.inr (by dsimp at h63; omega))))
  rw [sysBlock80Mod4Of_eq_wSlice80_conj, sysBlock80Mod4Of_eq_wSlice80_conj, hW]
  exact congrArg (· * wSlice80 cfg false p₂)
    (congrArg ((wSlice80 cfg false p₂)ᴴ * ·)
      (congrArg Matrix.diagonal (funext fun z ↦ by rw [hDiag z])))

end HpowStep_15
theorem coherentSysOp80Mod4Of_muSlot2Ideal216_eq (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : coherentSysOp80Mod4Of tM tierBQftFull cfg false muSlot2Ideal216 =
    coherentSysOp80Mod4Of tM tierBQftFull cfg false (pos80IdealDist false) := by
  unfold coherentSysOp80Mod4Of
  let e : BitAssignment 80 ≃ BitAssignment 80 :=
    PosPostPrep80L1BoundsS3.flipTailDpScratch80_involutive.toPerm
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have he : e p = flipTailDpScratch80 p := rfl
  rw [he, ← PosPostPrep80L1BoundsS3.pos80IdealDist_eq_physics]
  have hblk := blkMod4_eq_of_eq_outside_scratch16_of_tM tM cfg (flipTailDpScratch80 p) p
      (PosPostPrep80L1BoundsS3.flipTailDpScratch80_eq_outside_scratch16 p)
  rw [hblk]
  unfold muSlot2Ideal216
  rw [PosPostPrep80L1BoundsS3.flipTailDpScratch80_involutive]

set_option exponentiation.threshold 4200 in
theorem sysBlock80Mod4_projIndep_of_tM (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (zP : NyqFine3D512) (bP : Fin 3 → Fin 2) (l : Fin 256) (p : BitAssignment 80)
    (hl : l.val < 216) : sysBlock80Mod4Of tM tierBQftFull (cfgProjZ512 zP) false
    (p80SetCosetAndNuc bP l p) = sysBlock80Mod4Of tM tierBQftFull (cfgProjZ512 zP) false
    (p80SetNucZero p) := by
  let pL := p80SetCosetAndNuc bP l p
  let p0 := p80SetNucZero p
  have hOutL : ∀ j : Fin 80, (j.val < 3 ∨ 14 ≤ j.val) → pL j = p j := fun j hj ↦ by
    dsimp only [pL]; unfold p80SetCosetAndNuc
    split_ifs <;> first | (exfalso; omega) | rfl
  have hOut0 : ∀ j : Fin 80, (j.val < 3 ∨ 14 ≤ j.val) → p0 j = p j := fun j hj ↦ by
    dsimp only [p0]; unfold p80SetNucZero
    split_ifs <;> first | (exfalso; omega) | rfl
  have hNucL : payloadNucNat pL = l.val := by
    have hfn : (fun j : Fin 8 ↦ pL (pos80SubIdx 6 8 (by decide) j)) =
        fun j : Fin 8 ↦ z2BitOfNat l.val j.val := by
      funext j; dsimp only [pL]; unfold p80SetCosetAndNuc pos80SubIdx
      have hnot : ¬(3 ≤ 6 + j.val ∧ 6 + j.val < 6) := by omega
      have hin : 6 ≤ 6 + j.val ∧ 6 + j.val < 14 := ⟨by omega, by omega⟩
      simp only [hnot, ↓reduceDIte, hin]
      rw [PosPostPrep80L1BoundsS3.natModTwoCast_eq_z2BitOfNat]
      exact congrArg (z2BitOfNat l.val) (by omega)
    change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
      pL (pos80SubIdx 6 8 (by decide) j)) = l.val
    rw [hfn]; exact root_bitsVal_z2BitOfNat_of_lt_slot2 l.isLt
  have hNuc0 : payloadNucNat p0 = 0 := by
    have hfn : (fun j : Fin 8 ↦ p0 (pos80SubIdx 6 8 (by decide) j)) =
        fun j : Fin 8 ↦ z2BitOfNat 0 j.val := by
      funext j; dsimp only [p0]; unfold p80SetNucZero pos80SubIdx z2BitOfNat
      have hin : 6 ≤ 6 + j.val ∧ 6 + j.val < 14 := ⟨by omega, by omega⟩
      simp [hin]
    change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
      p0 (pos80SubIdx 6 8 (by decide) j)) = 0
    rw [hfn]; exact root_bitsVal_z2BitOfNat_of_lt_slot2 (by decide : 0 < 2 ^ 8)
  have hB1 : payloadB1Parity pL = payloadB1Parity p0 := by
    funext w; apply Fin.ext; dsimp [payloadB1Parity]
    have hL := hOutL ⟨w.val, by have := w.isLt; omega⟩ (Or.inl w.isLt)
    have h0 := hOut0 ⟨w.val, by have := w.isLt; omega⟩ (Or.inl w.isLt)
    exact congrArg ZMod.val (hL.trans h0.symm)
  have hAnc : payloadAncNat pL = payloadAncNat p0 :=
    congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
      (hOutL (pos80SubIdx 14 8 (by decide) j) (Or.inr (by dsimp [pos80SubIdx]; omega))).trans
      (hOut0 (pos80SubIdx 14 8 (by decide) j) (Or.inr (by dsimp [pos80SubIdx]; omega))).symm)
  have hKickEq : slot2RawKickDiag (cfgProjZ512 zP) (payloadNucNat pL) =
      slot2RawKickDiag (cfgProjZ512 zP) (payloadNucNat p0) := by
    rw [hNucL, hNuc0]; unfold slot2RawKickDiag
    have h0lt : 0 < 216 := by decide
    simp only [hl, h0lt, ↓reduceDIte]; rfl
  have hTwEq : (castUnitaryPow2 pos24_core80_eq_twist80.symm
      (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 (cfgProjZ512 zP))).1 =
      (slot2UTwistParam true pos24_22_le_80 (cfgProjZ512 zP)).1 := rfl
  have hW : wSlice80 (cfgProjZ512 zP) false pL = wSlice80 (cfgProjZ512 zP) false p0 := by
    rw [wSlice80_factor (cfgProjZ512 zP) false pL, wSlice80_factor (cfgProjZ512 zP) false p0, hTwEq,
        sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl false pL,
        sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl false p0,
        sysBlockAtPayloadGen_uTwist_slot2_eq (cfgProjZ512 zP) pL,
        sysBlockAtPayloadGen_uTwist_slot2_eq (cfgProjZ512 zP) p0, hB1, hAnc, hKickEq]
  have hDiag : ∀ z : Fin (2 ^ systemQubits),
      posPhaseBitMod4 true pos24TailSign tM (coreBetaOf false pL z) =
        posPhaseBitMod4 true pos24TailSign tM (coreBetaOf false p0 z) := fun z ↦ by
    let rC := QRegExt.ofFin posCoreWires
    let γL := coreBetaOf false pL z
    let γ0 := coreBetaOf false p0 z
    have hOutCore : ∀ q : Wire posCoreWires,
        ¬(3957 ≤ q.val ∧ q.val < 3968) → γL q = γ0 q := fun q hq ↦
      coreBetaOf_eq_of_payload_eq_at false pL p0 z q fun hsub hge ↦
        (hOutL ⟨q.val - 3954, hsub⟩ (by dsimp; omega)).trans
          (hOut0 ⟨q.val - 3954, hsub⟩ (by dsimp; omega)).symm
    have hNucCore : ∀ p80 : BitAssignment 80,
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rC) (coreBetaOf false
          p80 z) = payloadNucNat p80 := fun p80 ↦ by
      have hfn : (fun j : Fin 8 ↦ coreBetaOf false p80 z (rNucIdx rC j)) =
          fun j : Fin 8 ↦ p80 (pos80SubIdx 6 8 (by decide) j) := by
        funext j
        have hw : rNucIdx rC j = rPosSubLocal (pos80SubIdx 6 8 (by decide) j) := rfl
        rw [hw, coreBetaOf_payload]
      change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
        coreBetaOf false p80 z (rNucIdx rC j)) = _
      rw [hfn]; rfl
    exact posPhaseBitMod4_eq_of_coin0 pos24TailSign tM γL γ0
      (coreBetaOf_mid false pL z _ (by decide) (by decide))
      (coreBetaOf_mid false pL z _ (by decide) (by decide))
      (coreBetaOf_mid false pL z _ (by decide) (by decide))
      (coreBetaOf_mid false p0 z _ (by decide) (by decide))
      (coreBetaOf_mid false p0 z _ (by decide) (by decide))
      (coreBetaOf_mid false p0 z _ (by decide) (by decide))
      (by dsimp only [γL]; rw [hNucCore pL, hNucL]; exact hl)
      (by dsimp only [γ0]; rw [hNucCore p0, hNuc0]; decide)
      (hOutCore _ (by decide)) (hOutCore _ (by decide))
      (hOutCore _ (by decide)) (hOutCore _ (by decide))
      (regVal_eq_of_wire_eq _ γL γ0 fun i ↦ hOutCore _ (by revert i; decide))
      (funext fun w ↦ Fin.ext (regVal_eq_of_wire_eq _ γL γ0 fun i ↦
        hOutCore _ (by revert w i; decide)))
      (regVal_eq_of_wire_eq _ γL γ0 fun i ↦ hOutCore _ (by revert i; decide))
      (funext fun w ↦ congrArg (fun b ↦ decide (b = 1)) (hOutCore _ (by revert w; decide)))
      (fun e ↦ funext fun w ↦ Fin.ext (regVal_eq_of_wire_eq _ γL γ0 fun i ↦ hOutCore _ (by
        have := e.isLt; have := w.isLt; have := i.isLt
        change ¬(3957 ≤ 18 * e.val + (6 * w.val + (5 - i.val)) ∧
          18 * e.val + (6 * w.val + (5 - i.val)) < 3968)
        omega)))
  rw [sysBlock80Mod4Of_eq_wSlice80_conj, sysBlock80Mod4Of_eq_wSlice80_conj, hW]
  exact congrArg (· * wSlice80 (cfgProjZ512 zP) false p0)
    (congrArg ((wSlice80 (cfgProjZ512 zP) false p0)ᴴ * ·)
      (congrArg Matrix.diagonal (funext fun z ↦ by rw [hDiag z])))

theorem mergedCoherentOp80Mod4Of_muSlot2Ideal218_eq (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : mergedCoherentOp80Mod4Of tM tierBQftFull cfg muSlot2Ideal218 =
    mergedPosSlot2BUnitTwosGen (108 / 109 : ℝ) (fun c ↦ coherentSysOp80Mod4Of tM tierBQftFull
    c false (pos80IdealDist false)) cfg := by
  have hCollapse := MergedVepTopCoinCollapse.mergedCoherentOpGen_eq_mergedBUnitTwosGen_of_b0Zero
    (fun c' p' ↦ sysBlock80Mod4Of tM tierBQftFull c' false p')
    (108 / 109 : ℝ) muSlot2Ideal216 muSlot2Ideal218
    (sysBlock80Mod4_projIndep_of_tM tM)
    PosPostPrep80L1BoundsS3.muSlot2Ideal216_eq_zero_of_nuc_ge_216
    PosPostPrep80L1BoundsS3.muSlot2Ideal216_eq_zero_of_b0_ne_zero
    (fun p hp ↦ by
      unfold muSlot2Ideal218; rw [← PosPostPrep80L1BoundsS3.p80NucVal_eq_bitsVal]; simp [hp])
    (fun p hp ↦ by
      unfold muSlot2Ideal218; rw [← PosPostPrep80L1BoundsS3.p80NucVal_eq_bitsVal]
      have h1 : ¬(p80NucVal p < 216) := by omega
      have h2 : ¬(p80NucVal p < 218) := by omega
      simp [h1, h2])
    (fun p l hge hlt hl ↦ by
      unfold muSlot2Ideal218; rw [← PosPostPrep80L1BoundsS3.p80NucVal_eq_bitsVal]
      have hnot : ¬(p80NucVal p < 216) := by omega
      simp only [hnot, ↓reduceIte, hlt]
      have hRat : (27 / 218 : ℝ) = (108 / 109 : ℝ) / 8 := by norm_num
      rw [hRat]; congr 1; unfold muSlot2Ideal216
      rw [PosPostPrep80L1BoundsS3.p80ClearCosetAndNucLocal_eq_set0,
        PosPostPrep80L1BoundsS3.flip_setCosetAndNuc_comm,
        PosPostPrep80L1BoundsS3.flip_setCosetAndNuc_comm,
        PosPostPrep80L1BoundsS3.pos80IdealDist_false_setCosetAndNuc_eq l hl])
    cfg
  refine hCollapse.trans ?_
  have hBase : (fun c ↦ ∑ p : BitAssignment 80, (muSlot2Ideal216 p : ℂ) • sysBlock80Mod4Of tM
      tierBQftFull c false p) = (fun c ↦ coherentSysOp80Mod4Of tM tierBQftFull c false
      (pos80IdealDist false)) := funext fun c ↦ coherentSysOp80Mod4Of_muSlot2Ideal216_eq tM c
  rw [hBase]
  exact PosPostPrep80L1BoundsS3.mMergedBUnitTwosGen_eq_mergedPosSlot2BUnitTwosGen (108 /
    109 : ℝ) _ cfg

-- ============================================================================
-- Section 5: Hermiticity, Unit-Norm Bounds, and Midpoint Perturbation Caps
-- ============================================================================

theorem sysBlock80Mod4Of_conjTranspose
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (s0 : Bool) (p : BitAssignment 80) :
    (sysBlock80Mod4Of tM tierBQftFull cfg s0 p)ᴴ = sysBlock80Mod4Of tM tierBQftFull cfg s0 p := by
  rw [sysBlock80Mod4Of_eq_wSlice80_conj, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose]
  have hd : star (fun z : Fin (2 ^ systemQubits) ↦ if posPhaseBitMod4 true pos24TailSign tM
      (coreBetaOf s0 p z) then (-1 : ℂ) else 1) = (fun z : Fin (2 ^ systemQubits) ↦ if
      posPhaseBitMod4 true pos24TailSign tM (coreBetaOf s0 p z) then (-1 : ℂ) else 1) := by
    funext z; dsimp; split_ifs <;> simp
  rw [hd, Matrix.mul_assoc]

theorem conj_unitary_sa_gen {D : ℕ} (U S : Operator D) (hS : Sᴴ = S) :
    (Uᴴ * S * U)ᴴ = Uᴴ * S * U := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hS, Matrix.mul_assoc]

theorem sum_sa_gen {ι : Type*} {D : ℕ} (s : Finset ι) (f : ι → Operator D)
    (hf : ∀ i ∈ s, (f i)ᴴ = f i) : (∑ i ∈ s, f i)ᴴ = ∑ i ∈ s, f i := by
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i hi ↦ hf i hi

theorem mul_sa_of_comm_gen {D : ℕ} (P A : Operator D) (hP : Pᴴ = P) (hA : Aᴴ = A)
    (hComm : A * P = P * A) : (P * A)ᴴ = P * A := by
  rw [Matrix.conjTranspose_mul, hP, hA, hComm]

theorem coherentSysOp80Mod4Of_isHermitian (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (s0 : Bool) (mu : BitAssignment 80 → ℝ) :
    (coherentSysOp80Mod4Of tM tierBQftFull cfg s0 mu).IsHermitian := by
  rw [Matrix.IsHermitian]; unfold coherentSysOp80Mod4Of; rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal,
    sysBlock80Mod4Of_conjTranspose]

theorem mergedCoherentOp80Mod4Of_isHermitian (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (mu : BitAssignment 80 → ℝ) :
    (mergedCoherentOp80Mod4Of tM tierBQftFull cfg mu).IsHermitian := by
  rw [Matrix.IsHermitian];
  unfold mergedCoherentOp80Mod4Of
    MergedVepTopCoinCollapse.mergedCoherentOpGen
  refine sum_sa_gen Finset.univ _ fun p _ ↦ ?_
  rw [Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal]
  refine congrArg ((mu p : ℂ) • ·) ?_
  unfold mergedSliceGen
  split_ifs with hlt
  · exact sysBlock80Mod4Of_conjTranspose tM cfg false p
  · dsimp only
    refine conj_unitary_sa_gen _ _ (sum_sa_gen Finset.univ _ fun yIdx _ ↦ ?_)
    have hP : mProjBasisGen mProj24_sp yIdx = mProj24_sp.basisOutcomeProjector yIdx :=
      mProjBasisGen_eq_basisOutcomeProjector mProj24_sp yIdx
    have hP_sa : (mProjBasisGen mProj24_sp yIdx)ᴴ = mProjBasisGen mProj24_sp yIdx := by
      rw [hP]; exact QRegister.basisOutcomeProjector_conjTranspose _ _
    have hComm : sysBlock80Mod4Of tM tierBQftFull (cfgProjZ512 (nyq512ProjEquiv3D
        (mProjGridEquiv24 yIdx, p80CosetP3 p))) false (p80SetNucZero p) * mProjBasisGen
        mProj24_sp yIdx = mProjBasisGen mProj24_sp yIdx * sysBlock80Mod4Of tM tierBQftFull
        (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, p80CosetP3 p))) false
        (p80SetNucZero p) := by
      rw [hP]; exact sysBlock80Mod4Of_slot2_comm_rProj24 tM _ (p80SetNucZero p) _
    exact mul_sa_of_comm_gen _ _ hP_sa
      (sysBlock80Mod4Of_conjTranspose tM _ false (p80SetNucZero p)) hComm

theorem tierBB2IdMod4Of_isHermitian (tM : Fin orbitCount47905 →
    Fin (2 ^ 30)) (cfg : Configuration) :
    (tierBB2IdMod4Of tM cfg).IsHermitian := by
  unfold tierBB2IdMod4Of tierBB2RawIdMod4Of
  rw [← mergedCoherentOp80Mod4Of_muSlot2Ideal218_eq tM cfg]
  exact mergedCoherentOp80Mod4Of_isHermitian tM cfg muSlot2Ideal218

theorem tierBB4IdMod4Of_isHermitian (tM : Fin orbitCount47905 →
    Fin (2 ^ 30)) (cfg : Configuration) :
    (tierBB4IdMod4Of tM cfg).IsHermitian :=
  coherentSysOp80Mod4Of_isHermitian tM cfg true (pos80IdealDist true)

theorem tierBB2IdMod4_isHermitian (cfg : Configuration) : (tierBB2IdMod4 cfg).IsHermitian :=
    tierBB2IdMod4Of_isHermitian pos24TailMag30 cfg

theorem tierBB4IdMod4_isHermitian (cfg : Configuration) : (tierBB4IdMod4 cfg).IsHermitian :=
    tierBB4IdMod4Of_isHermitian pos24TailMag30 cfg

theorem coherentSysOp80Mod4Of_norm_le_of_sum_abs_le_one
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration) (s0 : Bool) (mu : BitAssignment 80 → ℝ)
    (hsum : (∑ p : BitAssignment 80, |mu p|) ≤ 1) :
    ‖coherentSysOp80Mod4Of tM qft cfg s0 mu‖ ≤ 1 := by
  unfold coherentSysOp80Mod4Of
  calc ‖∑ p : BitAssignment 80, (mu p : ℂ) • sysBlock80Mod4Of tM qft cfg s0 p‖
      ≤ ∑ p : BitAssignment 80, ‖(mu p : ℂ) • sysBlock80Mod4Of tM qft cfg s0 p‖ := norm_sum_le _ _
    _ ≤ ∑ p : BitAssignment 80, |mu p| := by
        refine Finset.sum_le_sum fun p _ ↦ ?_
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        calc |mu p| * ‖sysBlock80Mod4Of tM qft cfg s0 p‖
            ≤ |mu p| * 1 :=
              mul_le_mul_of_nonneg_left
                (norm_sysBlockAtPayloadGen_le_one pos24_coreWires80_eq.symm
                  (pos24ConjCore80Mod4Of tM qft cfg) s0 p) (abs_nonneg _)
          _ = |mu p| := mul_one _
    _ ≤ 1 := hsum

theorem norm_mergedSliceGen_sysBlock80Mod4Of_le_one (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p : BitAssignment 80) : ‖mergedSliceGen
    (fun c' p' ↦ sysBlock80Mod4Of tM tierBQftFull c' false p') cfg p‖ ≤ 1 := by
  unfold mergedSliceGen
  by_cases h : p80NucVal p < 216
  · rw [MergedVepTopCoinCollapse.ite_eq_of_pos h]
    exact norm_sysBlockAtPayloadGen_le_one pos24_coreWires80_eq.symm
      (pos24ConjCore80Mod4Of tM tierBQftFull cfg) false p
  · rw [MergedVepTopCoinCollapse.ite_eq_of_neg h]
    dsimp only
    set bP := p80CosetP3 p
    set U := mProj24_sp.embedUnitary (uProjPlus512_3D bP)
    have hRew : (∑ yIdx : Fin (2 ^ 24), mProjBasisGen mProj24_sp yIdx * sysBlock80Mod4Of tM
        tierBQftFull (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, bP))) false
        (p80SetNucZero p)) = ∑ yIdx : Fin (2 ^ 24), mProj24_sp.basisOutcomeProjector yIdx *
        sysBlock80Mod4Of tM tierBQftFull
        (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, bP))) false (p80SetNucZero p)
        :=
      Finset.sum_congr rfl fun yIdx _ ↦ by rw [mProjBasisGen_eq_basisOutcomeProjector]
    rw [hRew]
    set S := ∑ yIdx : Fin (2 ^ 24),
      mProj24_sp.basisOutcomeProjector yIdx *
        sysBlock80Mod4Of tM tierBQftFull (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx,
          bP)))
          false (p80SetNucZero p)
    have hMid : ‖S‖ ≤ 1 := norm_sum_proj_mul_blockDiag_le_one mProj24_sp _ (fun yIdx ↦
        norm_sysBlockAtPayloadGen_le_one pos24_coreWires80_eq.symm (pos24ConjCore80Mod4Of tM
        tierBQftFull _) false (p80SetNucZero p)) (fun yIdx x' x hne ↦
        sysBlock80Mod4_projDiag_slot2 tM _ (p80SetNucZero p) x' x hne)
    exact norm_conj_unitary_le_one U S hMid

theorem tierBB2RawIdMod4Of_norm_le_one (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : ‖tierBB2RawIdMod4Of tM cfg‖ ≤ 1 :=
    coherentSysOp80Mod4Of_norm_le_of_sum_abs_le_one tM tierBQftFull cfg false
    (pos80IdealDist false) (le_of_eq (sum_abs_pos80IdealDist_eq_one false))

theorem tierBB2IdMod4Of_norm_le_one (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : ‖tierBB2IdMod4Of tM cfg‖ ≤ 1 :=
  norm_mergedPosSlot2BUnitTwosGen_le_one (by norm_num) (by norm_num) (tierBB2RawIdMod4Of tM)
    (tierBB2RawIdMod4Of_norm_le_one tM) (fun zP M ↦
      tierBB2RawIdMod4Of_comm_rProj24 tM (cfgProjZ512 zP) M) cfg

theorem tierBB4IdMod4Of_norm_le_one (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) : ‖tierBB4IdMod4Of tM cfg‖ ≤ 1 :=
    coherentSysOp80Mod4Of_norm_le_of_sum_abs_le_one tM tierBQftFull cfg true
    (pos80IdealDist true) (le_of_eq (sum_abs_pos80IdealDist_eq_one true))

theorem tierBB2IdMod4_norm_le_one (cfg : Configuration) : ‖tierBB2IdMod4 cfg‖ ≤ 1 :=
    tierBB2IdMod4Of_norm_le_one pos24TailMag30 cfg

theorem tierBB4IdMod4_norm_le_one (cfg : Configuration) : ‖tierBB4IdMod4 cfg‖ ≤ 1 :=
    tierBB4IdMod4Of_norm_le_one pos24TailMag30 cfg

theorem mergedCoherentOp80Mod4Of_sub_norm_le_l1
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (mu₁ mu₂ : BitAssignment 80 → ℝ) :
    ‖mergedCoherentOp80Mod4Of tM tierBQftFull cfg mu₁ -
      mergedCoherentOp80Mod4Of tM tierBQftFull cfg mu₂‖ ≤
      ∑ p : BitAssignment 80, |mu₁ p - mu₂ p| := by
  unfold mergedCoherentOp80Mod4Of MergedVepTopCoinCollapse.mergedCoherentOpGen
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
  have hsub :
      (mu₁ p : ℂ) • mergedSliceGen (fun c' p' ↦
        sysBlock80Mod4Of tM tierBQftFull c' false p') cfg p -
        (mu₂ p : ℂ) • mergedSliceGen (fun c' p' ↦
          sysBlock80Mod4Of tM tierBQftFull c' false p') cfg p =
      ((mu₁ p - mu₂ p : ℝ) : ℂ) •
        mergedSliceGen (fun c' p' ↦ sysBlock80Mod4Of tM tierBQftFull c' false p') cfg p := by
    push_cast; rw [sub_smul]
  rw [hsub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (norm_mergedSliceGen_sysBlock80Mod4Of_le_one tM cfg p) (abs_nonneg _)).trans (mul_one _).le

theorem coherentSysOp80Mod4Of_sub_norm_le_l1
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (qft : FullSysQft654Bundle) (cfg : Configuration) (s0 : Bool)
    (mu₁ mu₂ : BitAssignment 80 → ℝ) :
    ‖coherentSysOp80Mod4Of tM qft cfg s0 mu₁ -
      coherentSysOp80Mod4Of tM qft cfg s0 mu₂‖ ≤
      ∑ p : BitAssignment 80, |mu₁ p - mu₂ p| := by
  unfold coherentSysOp80Mod4Of
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
  have hsub : (mu₁ p : ℂ) • sysBlock80Mod4Of tM qft cfg s0 p - (mu₂ p : ℂ) • sysBlock80Mod4Of
      tM qft cfg s0 p = ((mu₁ p - mu₂ p : ℝ) : ℂ) • sysBlock80Mod4Of tM qft cfg s0 p := by
    push_cast; rw [sub_smul]
  rw [hsub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_sysBlockAtPayloadGen_le_one pos24_coreWires80_eq.symm
    (pos24ConjCore80Mod4Of tM qft cfg) s0 p) (abs_nonneg _)).trans (mul_one _).le

theorem sysBlock80Of_eq_of_p80_30_one (tM₁ tM₂ : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (s0 : Bool) (p80 : BitAssignment 80) (hp30 : p80 30 = 1) :
    sysBlock80Of tM₁ tierBQftFull cfg s0 p80 = sysBlock80Of tM₂ tierBQftFull cfg s0 p80 := by
  rw [sysBlock80Of_eq_wSlice80_conj, sysBlock80Of_eq_wSlice80_conj]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) rfl
  ext z' z
  by_cases hzz : z' = z
  · subst hzz
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    have hHead : coreBetaOf s0 p80 z' (wIsHead (QRegExt.ofFin posCoreWires)) = 1 := by
      change coreBetaOf s0 p80 z' (rPosSubLocal ⟨30, by decide⟩) = 1
      rw [coreBetaOf_payload]
      exact hp30
    rw [posPhaseBit_eq_of_wIsHead_one tM₁ tM₂ _ hHead]
  · rw [Matrix.diagonal_apply_ne _ hzz, Matrix.diagonal_apply_ne _ hzz]

theorem sum_headSupport_sysBlock80Of_sub_eq_zero (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (s0 : Bool) : (∑ x : HeadSupportIdx s0, (pos80IdealDist s0
    (pos80WitnessOf s0 (Sum.inl x)) : ℂ) • (sysBlock80Of tM tierBQftFull cfg s0
    (pos80WitnessOf s0 (Sum.inl x)) - sysBlock80Of pos24TailMag30 tierBQftFull cfg s0
    (pos80WitnessOf s0 (Sum.inl x)))) = 0 := by
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  rcases x with ⟨b0, nuc, anc, k, pid, sm, th, rj⟩
  have hp30 : pos80WitnessOf s0 (Sum.inl (b0, nuc, anc, k, pid, sm, th, rj)) 30 = 1 := rfl
  rw [sysBlock80Of_eq_of_p80_30_one tM pos24TailMag30 cfg s0 _ hp30, sub_self, smul_zero]

section HpowStep_17
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_17 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem wSlice80_tailWitness_eq_zero_slot2 (cfg : Configuration) (l : Fin 216) (anc : Fin 218)
    (dp : Fin 8) (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool) : wSlice80 cfg false
    (tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj) = wSlice80 cfg false
    (tailWitnessPayload80 0 l.val anc.val 0 dp 0 false false) := by
  let p₁ := tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj
  let p₀ := tailWitnessPayload80 0 l.val anc.val 0 dp 0 false false
  have h0 : payloadB1Parity p₁ = payloadB1Parity p₀ := by
    funext w; apply Fin.ext; fin_cases w <;> rfl
  have h1 : payloadNucNat p₁ = payloadNucNat p₀ :=
    congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
      by fin_cases j <;> rfl)
  have h2 : payloadAncNat p₁ = payloadAncNat p₀ :=
    congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
      by fin_cases j <;> rfl)
  have hTwEq : (castUnitaryPow2 pos24_core80_eq_twist80.symm (NuclearTwistRealizes.uTwistParam
      true pos24_22_le_80 cfg)).1 = (slot2UTwistParam true pos24_22_le_80 cfg).1 := rfl
  rw[wSlice80_factor cfg false p₁, wSlice80_factor cfg false p₀, hTwEq,
      sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl false p₁,
      sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl false p₀,
      sysBlockAtPayloadGen_uTwist_slot2_eq cfg p₁,
      sysBlockAtPayloadGen_uTwist_slot2_eq cfg p₀, h0, h1, h2]

end HpowStep_17
section HpowStep_18
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_18 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem wSlice80_tailWitness_eq_zero_slot4 (cfg : Configuration) (b0 : Fin 8) (anc : Fin 218)
    (part : Fin 217) (dp : Fin 8) (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool) : wSlice80
    cfg true (tailWitnessPayload80 b0.val 0 anc.val part.val dp keep.val th rj) = wSlice80 cfg
    true (tailWitnessPayload80 b0.val 0 anc.val part.val dp 0 false false) := by
  let p₁ := tailWitnessPayload80 b0.val 0 anc.val part.val dp keep.val th rj
  let p₀ := tailWitnessPayload80 b0.val 0 anc.val part.val dp 0 false false
  have hB1 : payloadB1Parity p₁ = payloadB1Parity p₀ := by
    funext w; apply Fin.ext; fin_cases w <;> rfl
  have hQ : sysBlockAtPayloadGen pos24_coreWires80_eq.symm
      (fullSysQftCoreUnitary pos24_6_le_80 tierBQftFull).1 true p₁ =
    sysBlockAtPayloadGen pos24_coreWires80_eq.symm
      (fullSysQftCoreUnitary pos24_6_le_80 tierBQftFull).1 true p₀ := by
    rw [sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl true p₁,
      sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl true p₀, hB1]
  have hm₁ := tw_mt b0 anc part dp keep th rj
  have hm₀ := tw_mt b0 anc part dp ⟨0, by fin_cases dp <;> decide⟩ false false
  have hanc₁ : _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
    p₁ (pos80SubIdx 14 8 (by decide) j)) < 218 := by
    rw [hm₁.2.2]; exact anc.isLt
  have hanc₀ : _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
    p₀ (pos80SubIdx 14 8 (by decide) j)) < 218 := by
    rw [hm₀.2.2]; exact anc.isLt
  have hTwMul : sysBlockAtPayloadGen pos24_coreWires80_eq.symm (castUnitaryPow2
      pos24_core80_eq_twist80.symm (NuclearTwistRealizes.uTwistParam true pos24_22_le_80
      cfg)).1 true p₁ * smToTwos654SysUnitary.1 = sysBlockAtPayloadGen
      pos24_coreWires80_eq.symm (castUnitaryPow2 pos24_core80_eq_twist80.symm
      (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1 true p₀ *
      smToTwos654SysUnitary.1 := by
    have h1 := sb_tw cfg p₁ hanc₁
    have h0 := sb_tw cfg p₀ hanc₀
    dsimp only at h1 h0
    have hi_eq : ∀ (p : BitAssignment 80) (hp : 14 + 8 ≤ 80)
        (hlt : _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
          p (pos80SubIdx 14 8 hp j)) < 218),
        _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
          p (pos80SubIdx 14 8 (by decide) j)) = anc.val →
        (⟨_root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
          p (pos80SubIdx 14 8 hp j)), hlt⟩ : Fin 218) = anc :=
      fun _ _ _ hval ↦ Fin.ext hval
    rw [h1, h0, hm₁.1, hm₁.2.1, hi_eq p₁ _ _ hm₁.2.2, hm₀.1, hm₀.2.1, hi_eq p₀ _ _ hm₀.2.2]
  have hSmSq : smToTwos654SysUnitary.1 * smToTwos654SysUnitary.1 = 1 := by
    calc smToTwos654SysUnitary.1 * smToTwos654SysUnitary.1
      _ = smToTwos654SysUnitary.1ᴴ * smToTwos654SysUnitary.1 := by
          rw [smToTwos654SysUnitary_sa]
      _ = 1 := smToTwos654SysUnitary.2.1
  have hTw : sysBlockAtPayloadGen pos24_coreWires80_eq.symm (castUnitaryPow2
      pos24_core80_eq_twist80.symm (NuclearTwistRealizes.uTwistParam true pos24_22_le_80
      cfg)).1 true p₁ = sysBlockAtPayloadGen pos24_coreWires80_eq.symm (castUnitaryPow2
      pos24_core80_eq_twist80.symm (NuclearTwistRealizes.uTwistParam true pos24_22_le_80
      cfg)).1 true p₀ := by
    have hmul := congrArg (· * smToTwos654SysUnitary.1) hTwMul
    simpa only [Matrix.mul_assoc, hSmSq, Matrix.mul_one] using hmul
  rw [wSlice80_factor cfg true p₁, wSlice80_factor cfg true p₀, hQ, hTw]

end HpowStep_18
private theorem coreBetaOf_subIdx8_regVal (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ systemQubits)) (off : ℕ) (hoff : off + 8 ≤ 80) (r : QRegister 8 posCoreWires)
    (hr : ∀ j : Fin 8, r j = rPosSubLocal (pos80SubIdx off 8 hoff j)) :
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal r (coreBetaOf s0 p80 z) =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
        p80 (pos80SubIdx off 8 hoff j)) := by
  have hfn : (fun j : Fin 8 ↦ coreBetaOf s0 p80 z (r j)) =
      fun j : Fin 8 ↦ p80 (pos80SubIdx off 8 hoff j) := by
    funext j
    rw [hr j, coreBetaOf_payload]
  exact congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal hfn

private theorem coreBetaOf_tailWitness_keep30 (s0 : Bool) (b0 nuc anc part : ℕ) (dp : Fin 8)
    (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool) (z : Fin (2 ^ systemQubits)) :
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 (QRegExt.ofFin
      posCoreWires))
      (coreBetaOf s0 (tailWitnessPayload80 b0 nuc anc part dp keep.val th rj) z) = keep.val := by
  let p80 := tailWitnessPayload80 b0 nuc anc part dp keep.val th rj
  let rCore := QRegExt.ofFin posCoreWires
  have hfn : (fun j : Fin 30 ↦ coreBetaOf s0 p80 z (rTailKeep30 rCore j)) =
      fun j : Fin 30 ↦ z2BitOfNat keep.val j.val := by
    funext j
    have hw : rTailKeep30 rCore j = rPosSubLocal (pos80SubIdx 32 30 (by decide) j) := rfl
    rw [hw, coreBetaOf_payload]
    have hj := j.isLt
    dsimp only [p80, tailWitnessPayload80, pos80SubIdx]
    have h1 : ¬(32 + j.val < 3) := by omega
    have h2 : ¬(32 + j.val < 6) := by omega
    have h3 : ¬(32 + j.val < 14) := by omega
    have h4 : ¬(32 + j.val < 22) := by omega
    have h5 : ¬(32 + j.val < 30) := by omega
    have h6 : (32 + j.val == 30) = false := beq_false_of_ne (by omega)
    have h7 : (32 + j.val == 31) = false := beq_false_of_ne (by omega)
    have h8 : 32 + j.val < 62 := by omega
    have h9 : 32 + j.val - 32 = j.val := by omega
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceIte, Bool.false_eq_true]
  change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 30 ↦
    coreBetaOf s0 p80 z (rTailKeep30 rCore j)) = keep.val
  rw [hfn]
  exact root_bitsVal_z2BitOfNat_of_lt_slot2 (lt_of_lt_of_le keep.isLt (tailSpan8_lt_two_pow_30 dp))

private theorem coreBetaOf_headWitness_fine21 (s0 : Bool) (b0 nuc anc : ℕ) (k : Fin 56)
    (pid : Fin 6) (sm : Fin 8) (th rj : Bool) (z : Fin (2 ^ systemQubits)) :
    fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires))
      (coreBetaOf s0 (headWitnessPayload80 b0 nuc anc k pid sm th rj) z) =
      pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm := by
  let p80 := headWitnessPayload80 b0 nuc anc k pid sm th rj
  let dH := pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm
  let rCore := QRegExt.ofFin posCoreWires
  funext w
  apply Fin.ext
  dsimp only [fineCoordOfReg21]
  let fineH := (dH 0).val + 128 * (dH 1).val + 16384 * (dH 2).val
  have hfn : (fun j : Fin 7 ↦
        coreBetaOf s0 p80 z (((rHeadFine21 rCore).slice (7 * w.val) 7 (by omega)) j)) =
      fun j : Fin 7 ↦ z2BitOfNat (dH w).val j.val := by
    funext j
    let idx80 : Fin 80 := ⟨32 + 7 * w.val + j.val, by have := w.isLt; have := j.isLt; omega⟩
    have hw_p : ((rHeadFine21 rCore).slice (7 * w.val) 7 (by omega)) j = rPosSubLocal idx80 := by
      ext
      change 3954 + (32 + (7 * w.val + j.val)) = 3954 + (32 + 7 * w.val + j.val)
      omega
    rw [hw_p, coreBetaOf_payload]
    have hp_bit : p80 idx80 = z2BitOfNat fineH (7 * w.val + j.val) := by
      dsimp only [p80, headWitnessPayload80, fineH, idx80]
      fin_cases w <;> fin_cases j <;> rfl
    rw [hp_bit]
    apply ZMod.val_injective
    rw [z2BitOfNat_val, z2BitOfNat_val, pow_add, ← Nat.div_div_eq_div_mul]
    have hdiv : fineH / 2 ^ (7 * w.val) =
        (dH w).val + 128 * (fineH / 2 ^ (7 * w.val + 7)) := by
      have := (dH 0).isLt
      have := (dH 1).isLt
      have := (dH 2).isLt
      fin_cases w <;> (dsimp [fineH]; omega)
    rw [hdiv]
    have := j.isLt
    have := (dH w).isLt
    fin_cases j <;> (dsimp; omega)
  change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 7 ↦
      coreBetaOf s0 p80 z (((rHeadFine21 rCore).slice (7 * w.val) 7 _) j)) = (dH w).val
  rw [hfn]
  exact root_bitsVal_z2BitOfNat_of_lt_slot2 (dH w).isLt

private theorem parity3OfReg_decide_eq_of_val (r : QRegister 3 posCoreWires)
    (β : BitAssignment posCoreWires) (b : Fin 3 → Fin 2)
    (h : ∀ w : Fin 3, (β (r w)).val = (b w).val) (w : Fin 3) :
    parity3OfReg r β w = decide (b w = 1) := by
  have hfin2 : (⟨(β (r w)).val, ZMod.val_lt _⟩ : Fin 2) = b w := Fin.ext (h w)
  dsimp only [parity3OfReg]
  rw [← hfin2]
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (β (r w)) with hx | hx
  · rw [hx]
    decide
  · rw [hx]
    decide

theorem posPhaseBit_tailWitness_slot2_of_tM
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (l : Fin 216) (anc : Fin 218) (dp : Fin 8) (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool)
    (z : Fin (2 ^ systemQubits)) :
    let p80 := tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj
    let b1 := nyqParity3DEquivFin8.symm dp
    let dTail := nyq128Equiv3D (slotCoordSys z 0, b1)
    let rOrbit := tetRank65 (canonTriple128 dTail)
    posPhaseBit true pos24TailSign tM (coreBetaOf false p80 z) =
      if keep.val < (tM rOrbit).val then Bool.not (pos24TailSign rOrbit) else rj := by
  intro p80 b1 dTail rOrbit
  let rCore := QRegExt.ofFin posCoreWires
  let β := coreBetaOf false p80 z
  have hw2 : β (wSlot2Core rCore) = 0 := coreBetaOf_mid false p80 z _ (by decide) (by decide)
  have hw1 : β (wSlot1Core rCore) = 0 := coreBetaOf_mid false p80 z _ (by decide) (by decide)
  have hw0 : β (wSlot0Core rCore) = 0 := coreBetaOf_mid false p80 z _ (by decide) (by decide)
  have hwSub : β (wSubReject rCore) = 0 := coreBetaOf_payload false p80 z ⟨62, by decide⟩
  have hwHead : β (wIsHead rCore) = 0 := coreBetaOf_payload false p80 z ⟨30, by decide⟩
  have hwRj : (β (wRejectZero rCore) == 1) = rj := by
    have h1 : β (wRejectZero rCore) = (if rj then 1 else 0) :=
      coreBetaOf_payload false p80 z ⟨79, by decide⟩
    rw [h1]
    cases rj <;> rfl
  have hrNuc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rCore) β =
    l.val :=
    (coreBetaOf_subIdx8_regVal false p80 z 6 (by decide) (rNucIdx rCore) fun _ ↦ rfl).trans
      (tailWitnessPayload80_slot2_meta l anc dp keep th rj).1
  have hrAnc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β =
    anc.val :=
    (coreBetaOf_subIdx8_regVal false p80 z 14 (by decide) (rAnchorIdx rCore) fun _ ↦ rfl).trans
      (tailWitnessPayload80_slot2_meta l anc dp keep th rj).2.1
  have hrPart : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx rCore) β =
    0 := by
    rw [coreBetaOf_subIdx8_regVal false p80 z 22 (by decide) (rPartnerIdx rCore) fun _ ↦ rfl]
    have h0 : (fun j : Fin 8 ↦ p80 (pos80SubIdx 22 8 (by decide) j)) =
        fun j : Fin 8 ↦ z2BitOfNat 0 j.val := funext fun j ↦ by
      dsimp only [p80, tailWitnessPayload80]
      fin_cases j <;> rfl
    rw [h0]
    exact root_bitsVal_z2BitOfNat_of_lt_slot2 (by decide)
  have hrKeep : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 rCore) β =
    keep.val :=
    coreBetaOf_tailWitness_keep30 false 0 l.val anc.val 0 dp keep th rj z
  have hB1 : ∀ w : Fin 3, (if parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires))
      (coreBetaOf false p80 z) w then (1 : ℕ) else 0) = (b1 w).val := fun w ↦ by
    have hdec := parity3OfReg_decide_eq_of_val (rCosetB1 rCore) β b1 (fun u ↦ by
      have hw_p : rCosetB1 rCore u = rPosSubLocal ⟨u.val, Nat.lt_trans u.isLt (by decide)⟩ := by
        ext
        change 3954 + (0 + u.val) = 3954 + u.val
        omega
      have hb_eq : β (rCosetB1 rCore u) = p80 ⟨u.val, Nat.lt_trans u.isLt (by decide)⟩ :=
        (congrArg β hw_p).trans (coreBetaOf_payload false p80 z _)
      rw [hb_eq]
      exact congrArg (fun f ↦ (f u).val)
        (tailWitnessPayload80_slot2_meta l anc dp keep th rj).2.2) w
    change (if parity3OfReg (rCosetB1 rCore) β w then (1 : ℕ) else 0) = (b1 w).val
    rw [hdec, ite_decide_fin2_eq_one_nat_slot2]
  have hHead0 : headPhaseBitSpec β = false := by
    unfold headPhaseBitSpec
    have hc1 : ((0 : ZMod 2) == 1) = false := by decide
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hc1, Bool.and_false, Bool.not_false, ↓reduceIte]
  have hTail : tailAndSlackPhaseBitSpec true pos24TailSign tM β =
      if keep.val < (tM rOrbit).val then Bool.not (pos24TailSign rOrbit) else rj := by
    unfold tailAndSlackPhaseBitSpec
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hwRj, hrNuc, l.isLt, hrAnc, anc.isLt,
      hrPart, hrKeep]
    have hb2 : ((0 : ZMod 2) == 1) = false := by decide
    have hacc : ((Bool.not ((0 : ZMod 2) == 1) &&
        decide ((Bool.not ((0 : ZMod 2) == 1)) = true → True) && decide True &&
        decide ((((0 : ZMod 2) == 1 && Bool.not ((0 : ZMod 2) == 1)) = true) → 0 < 217))) = true :=
          by
      decide
    rw [hacc]
    simp only [β, hb2, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      slotSubGridCoord64_coreBetaOf_slot2_eq, hB1]
    have hd_eq : (fun w : Fin 3 ↦
        (⟨2 * (slotCoordSys z 0 w).val + (b1 w).val,
          by have := (slotCoordSys z 0 w).isLt; have := (b1 w).isLt; omega⟩ : Fin 128)) =
        dTail := by
      funext w; apply Fin.ext
      exact (nyq128Equiv3D_val (slotCoordSys z 0) b1 w).symm
    rw [hd_eq]
  unfold posPhaseBit
  change Bool.xor (headPhaseBitSpec β) (tailAndSlackPhaseBitSpec true pos24TailSign tM β) = _
  rw [hHead0, hTail, Bool.false_xor]

theorem posPhaseBit_tailWitness_slot4_of_tM
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (b0 : Fin 8) (anc : Fin 218) (part : Fin 217) (dp : Fin 8)
    (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool)
    (z : Fin (2 ^ systemQubits)) :
    let p80 := tailWitnessPayload80 b0.val 0 anc.val part.val dp keep.val th rj
    let b₀ := Pos24Slot4FermionicBridge.nyqP8 b0
    let dp_nyq := Pos24Slot4FermionicBridge.nyqP8 dp
    let b₁ := ancPar b₀ (nyq128Equiv3D (0, dp_nyq))
    let dTail := Pos24Slot4FermionicBridge.s4TD b₀ b₁ part z
    let rOrbit := tetRank65 (canonTriple128 dTail)
    posPhaseBit true pos24TailSign tM (coreBetaOf true p80 z) =
      if keep.val < (tM rOrbit).val then pos24TailSign rOrbit else rj := by
  intro p80 b₀ dp_nyq b₁ dTail rOrbit
  let rCore := QRegExt.ofFin posCoreWires
  let β := coreBetaOf true p80 z
  have hw2 : β (wSlot2Core rCore) = 0 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hw1 : β (wSlot1Core rCore) = 0 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hw0 : β (wSlot0Core rCore) = 1 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hwSub : β (wSubReject rCore) = 0 := coreBetaOf_payload true p80 z ⟨62, by decide⟩
  have hwHead : β (wIsHead rCore) = 0 := coreBetaOf_payload true p80 z ⟨30, by decide⟩
  have hwRj : (β (wRejectZero rCore) == 1) = rj := by
    have h1 : β (wRejectZero rCore) = (if rj then 1 else 0) :=
      coreBetaOf_payload true p80 z ⟨79, by decide⟩
    rw [h1]
    cases rj <;> rfl
  have hrAnc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β =
    anc.val :=
    (coreBetaOf_subIdx8_regVal true p80 z 14 (by decide) (rAnchorIdx rCore) fun _ ↦ rfl).trans
      (Pos24Slot4FermionicBridge.tw_mt b0 anc part dp keep th rj).2.2
  have hrPart : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx rCore) β =
    part.val := by
    rw [coreBetaOf_subIdx8_regVal true p80 z 22 (by decide) (rPartnerIdx rCore) fun _ ↦ rfl]
    have hp : (fun j : Fin 8 ↦ p80 (pos80SubIdx 22 8 (by decide) j)) =
        fun j : Fin 8 ↦ z2BitOfNat part.val j.val := funext fun j ↦ by
      dsimp only [p80, tailWitnessPayload80]
      fin_cases j <;> rfl
    rw [hp]
    exact bitsVal_z2BitOfNat_of_lt (lt_trans part.isLt (by decide))
  have hrKeep : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 rCore) β =
    keep.val :=
    coreBetaOf_tailWitness_keep30 true b0.val 0 anc.val part.val dp keep th rj z
  have hB0 : ∀ w : Fin 3,
      (if parity3OfReg (rCosetB0 rCore) β w then (1 : ℕ) else 0) = (b₀ w).val := fun w ↦ by
    have hdec := parity3OfReg_decide_eq_of_val (rCosetB0 rCore) β b₀ (fun u ↦ by
      have hb_eq : β (rCosetB0 rCore u) = p80 (pos80SubIdx 3 3 (by decide) u) :=
        coreBetaOf_payload true p80 z _
      rw [hb_eq]
      exact congrArg (fun f ↦ (f u).val)
        (Pos24Slot4FermionicBridge.tw_mt b0 anc part dp keep th rj).1) w
    rw [hdec, Pos24Slot4FermionicBridge.it_f2]
  have hB1 : ∀ w : Fin 3,
      (if parity3OfReg (rCosetB1 rCore) β w then (1 : ℕ) else 0) = (b₁ w).val := fun w ↦ by
    have hdec := parity3OfReg_decide_eq_of_val (rCosetB1 rCore) β b₁ (fun u ↦ by
      have hw_p : rCosetB1 rCore u = rPosSubLocal ⟨u.val, Nat.lt_trans u.isLt (by decide)⟩ := by
        ext
        change 3954 + (0 + u.val) = 3954 + u.val
        omega
      have hb_eq : β (rCosetB1 rCore u) = p80 ⟨u.val, Nat.lt_trans u.isLt (by decide)⟩ :=
        (congrArg β hw_p).trans (coreBetaOf_payload true p80 z _)
      rw [hb_eq]
      exact congrArg (fun f ↦ (f u).val)
        (Pos24Slot4FermionicBridge.tw_mt b0 anc part dp keep th rj).2.1) w
    rw [hdec, Pos24Slot4FermionicBridge.it_f2]
  have hHead0 : headPhaseBitSpec β = false := by
    unfold headPhaseBitSpec
    have h01 : ((0 : ZMod 2) == 1) = false := rfl
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, h01, Bool.and_false, Bool.not_false, ↓reduceIte]
  have hTail : tailAndSlackPhaseBitSpec true pos24TailSign tM β =
      if keep.val < (tM rOrbit).val then pos24TailSign rOrbit else rj := by
    unfold tailAndSlackPhaseBitSpec
    have hb2 : ((0 : ZMod 2) == 1) = false := rfl
    have hs0 : ((1 : ZMod 2) == 1) = true := rfl
    have hslot : ∀ e : Fin 218, slotSubGridCoord64
        (rElecSlot (QRegExt.ofFin posCoreWires) e) β = Pos24Slot4FermionicBridge.sCd z e :=
        Pos24Slot4FermionicBridge.ss_cb true p80 z
    dsimp only [rCore] at hB0 hB1
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hwRj, hrAnc, anc.isLt, hrPart, part.isLt,
      hrKeep, hb2, hs0, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      IsEmpty.forall_iff, imp_self, decide_true, Bool.and_self, hB0, hB1, hslot]
    have horb : ∀ (hp_part : part.val % 217 + 1 < 218) (hp_mod : ∀ w : Fin 3, (2 *
        (Pos24Slot4FermionicBridge.sCd z 0 w).val + (b₀ w).val + 128 - (2 *
        (Pos24Slot4FermionicBridge.sCd z ⟨part.val % 217 + 1, hp_part⟩ w).val + (b₁ w).val)) %
        128 < 128), tetRank65 (canonTriple128 fun w ↦ ⟨(2 * (Pos24Slot4FermionicBridge.sCd z 0
        w).val + (b₀ w).val + 128 - (2 * (Pos24Slot4FermionicBridge.sCd z ⟨part.val % 217 + 1,
        hp_part⟩ w).val + (b₁ w).val)) % 128, hp_mod w⟩) = rOrbit := by
      intro hp_part hp_mod
      have hs_eq : (⟨part.val % 217 + 1, hp_part⟩ : Fin 218) =
          ⟨part.val + 1, by have := part.isLt; omega⟩ := by
        ext; dsimp; rw [Nat.mod_eq_of_lt part.isLt]
      refine congrArg (fun d ↦ tetRank65 (canonTriple128 d)) ?_
      funext w; apply Fin.ext
      dsimp only [dTail, Pos24Slot4FermionicBridge.s4TD]
      rw [hs_eq]
    rw [horb]
  unfold posPhaseBit
  change Bool.xor (headPhaseBitSpec β) (tailAndSlackPhaseBitSpec true pos24TailSign tM β) = _
  rw [hHead0, hTail, Bool.false_xor]

theorem sum_conj_sub_diagonal_eq {D : ℕ} {span : ℕ} (W : Operator D)
    (P : Fin span → Bool → Bool → Operator D) (d₁ d₂ : Fin span → Bool → Bool → Fin D → ℂ) (hP
    : ∀ k th rj, P k th rj = Wᴴ * Matrix.diagonal (d₁ k th rj) * W - Wᴴ * Matrix.diagonal (d₂
    k th rj) * W) : (∑ k : Fin span, ∑ th : Bool, ∑ rj : Bool, P k th rj) = Wᴴ *
    Matrix.diagonal (fun z ↦ ∑ k : Fin span, ∑ th : Bool, ∑ rj : Bool, (d₁ k th rj z - d₂ k th
    rj z)) * W := by
  have h1 : ∀ k th rj, P k th rj = Wᴴ * Matrix.diagonal (fun z ↦ d₁ k th rj z - d₂ k th rj z) * W :=
    fun k th rj ↦ by
      rw [hP k th rj, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]
  simp_rw [h1, ← Pos24Slot2FermionicBridge.conj_finset_sum_eq,
    Pos24Slot2FermionicBridge.sum_diagonal_eq_slot2]

theorem tierBB2RawIdOf_projDiag (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (c : Configuration) (x' x : Fin (2 ^ systemQubits))
    (hne : mProj24_sp.extractIndex x' ≠ mProj24_sp.extractIndex x) :
    tierBB2RawIdOf tM c x' x = 0 := by
  unfold tierBB2RawIdOf coherentSysOp80Of
  rw [Matrix.sum_apply]
  refine Finset.sum_eq_zero fun p80 _ ↦ ?_
  rw [Matrix.smul_apply, sysBlock80_projDiag_slot2 tM c p80 x' x hne, smul_zero]

theorem conj_sum_mul_sub {D : ℕ} {ι : Type*} (s : Finset ι) (W : Operator D) (P A B : ι →
    Operator D) :
    Wᴴ * (∑ i ∈ s, P i * A i) * W - Wᴴ * (∑ i ∈ s, P i * B i) * W =
      Wᴴ * (∑ i ∈ s, P i * (A i - B i)) * W := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Finset.sum_sub_distrib]
  refine congrArg (fun S ↦ Wᴴ * S * W)
    (Finset.sum_congr rfl fun i _ ↦ (Matrix.mul_sub (P i) (A i) (B i)).symm)

theorem norm_sum_proj_mul_blockDiag_le_cap {S m : ℕ} (r : QRegister m S)
    (A : Fin (2 ^ m) → Operator (2 ^ S)) {cCap : ℝ} (hcPos : 0 < cCap)
    (hNorm : ∀ y, ‖A y‖ ≤ cCap)
    (hDiag : ∀ y i j, r.extractIndex i ≠ r.extractIndex j → A y i j = 0) : ‖∑ y : Fin (2 ^ m),
    r.basisOutcomeProjector y * A y‖ ≤ cCap := by
  let A' : Fin (2 ^ m) → Operator (2 ^ S) := fun y ↦ ((cCap⁻¹ : ℝ) : ℂ) • A y
  have h1 : ‖∑ y : Fin (2 ^ m), r.basisOutcomeProjector y * A' y‖ ≤ 1 :=
    norm_sum_proj_mul_blockDiag_le_one r A'
      (fun y ↦ by
        dsimp only [A']
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hcPos.le)]
        exact (mul_le_mul_of_nonneg_left (hNorm y) (inv_nonneg.mpr hcPos.le)).trans
          (inv_mul_cancel₀ hcPos.ne').le)
      (fun y i j hne ↦ by
        dsimp only [A']
        rw [Matrix.smul_apply, hDiag y i j hne, smul_zero])
  have hEq : (∑ y : Fin (2 ^ m), r.basisOutcomeProjector y * A y) =
      (cCap : ℂ) • ∑ y : Fin (2 ^ m), r.basisOutcomeProjector y * A' y := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    dsimp only [A']
    rw [Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hcPos.ne',
      Complex.ofReal_one, one_smul]
  rw [hEq, norm_smul, Complex.norm_real, Real.norm_of_nonneg hcPos.le]
  exact (mul_le_mul_of_nonneg_left h1 hcPos.le).trans (mul_one cCap).le

theorem norm_tail_keep_th_rj_sub_of_tM_le (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (D : ℕ)
    {span : ℕ} (sign : Bool) (idx : Fin orbitCount47905)
    (hLo : (pos24TailMag30 idx).val ≤ (tM idx).val + D)
    (hHi : (tM idx).val ≤ (pos24TailMag30 idx).val + D)
    (hmag : (pos24TailMag30 idx).val ≤ span) : ‖(∑ keep : Fin span, ∑ _th : Bool, ∑ rj : Bool,
    ((if (if keep.val < (tM idx).val then sign else rj) then (-1 : ℂ) else 1) - (if (if
    keep.val < (pos24TailMag30 idx).val then sign else rj) then (-1 : ℂ) else 1)))‖ ≤ 4 *
    (D : ℝ) := by
  simp_rw [Finset.sum_sub_distrib]
  set m' : ℕ := min (tM idx).val span
  have hm' : m' ≤ span := min_le_right (tM idx).val span
  have hClampEq : (∑ keep : Fin span, ∑ _th : Bool, ∑ rj : Bool, (if (if keep.val < (tM
      idx).val then sign else rj) then (-1 : ℂ) else 1)) = (∑ keep : Fin span, ∑ _th : Bool, ∑
      rj : Bool, (if (if keep.val < m' then sign else rj) then (-1 : ℂ) else 1)) := by
    refine Finset.sum_congr rfl fun keep _ ↦ Finset.sum_congr rfl fun _th _ ↦
      Finset.sum_congr rfl fun rj _ ↦ ?_
    have hiff : keep.val < (tM idx).val ↔ keep.val < m' :=
      ⟨fun h ↦ lt_min h keep.isLt, fun h ↦ lt_of_lt_of_le h (min_le_left _ _)⟩
    rw [if_congr hiff rfl rfl]
  rw [hClampEq, Pos24Slot4FermionicBridge.su_tk sign hm', Pos24Slot4FermionicBridge.su_tk sign hmag]
  set m : ℕ := (pos24TailMag30 idx).val
  have hm'_lo : m ≤ m' + D := by dsimp [m', m]; omega
  have hm'_hi : m' ≤ m + D := by dsimp [m', m]; omega
  have h1 : (m : ℝ) ≤ ((m' + D : ℕ) : ℝ) := by exact_mod_cast hm'_lo
  have h2 : (m' : ℝ) ≤ ((m + D : ℕ) : ℝ) := by exact_mod_cast hm'_hi
  push_cast at h1 h2
  have hdiff_abs : |(m' : ℝ) - (m : ℝ)| ≤ (D : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hsign_abs : |if sign then (-1 : ℝ) else 1| = 1 := by
    cases sign <;> norm_num
  have hrew : (4 : ℂ) * (((if sign then (-1 : ℝ) else 1 : ℝ) : ℂ) * ((m' : ℝ) : ℂ)) - (4 : ℂ)
      * (((if sign then (-1 : ℝ) else 1 : ℝ) : ℂ) * ((m : ℝ) : ℂ)) = (((4 : ℝ) * (if sign then
      (-1 : ℝ) else 1) * ((m' : ℝ) - (m : ℝ)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hrew, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, hsign_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

private theorem norm_tail_keep_th_rj_wSlice80_sub_le
    (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (D : ℕ)
    (hLo : ∀ idx, (pos24TailMag30 idx).val ≤ (tM idx).val + D)
    (hHi : ∀ idx, (tM idx).val ≤ (pos24TailMag30 idx).val + D)
    (cfg : Configuration) (s0 : Bool) (b0 nuc anc part : ℕ) (dp : Fin 8)
    (rOrb : Fin (2 ^ systemQubits) → Fin orbitCount47905)
    (sgn : Fin (2 ^ systemQubits) → Bool)
    (hW : ∀ keep : Fin (pos24TailSpan8 dp), ∀ th rj : Bool,
      wSlice80 cfg s0 (tailWitnessPayload80 b0 nuc anc part dp keep.val th rj) =
        wSlice80 cfg s0 (tailWitnessPayload80 b0 nuc anc part dp 0 false false))
    (hPh : ∀ (tM' : Fin orbitCount47905 → Fin (2 ^ 30)) (keep : Fin (pos24TailSpan8 dp))
      (th rj : Bool) (z : Fin (2 ^ systemQubits)),
      posPhaseBit true pos24TailSign tM'
        (coreBetaOf s0 (tailWitnessPayload80 b0 nuc anc part dp keep.val th rj) z) =
        if keep.val < (tM' (rOrb z)).val then sgn z else rj)
    (hSpan : ∀ z, (pos24TailMag30 (rOrb z)).val ≤ pos24TailSpan8 dp) :
    ‖∑ keep : Fin (pos24TailSpan8 dp), ∑ th : Bool, ∑ rj : Bool,
      (sysBlock80Of tM tierBQftFull cfg s0
          (tailWitnessPayload80 b0 nuc anc part dp keep.val th rj) -
        sysBlock80Of pos24TailMag30 tierBQftFull cfg s0
          (tailWitnessPayload80 b0 nuc anc part dp keep.val th rj))‖ ≤ 4 * (D : ℝ) := by
  let W := wSlice80 cfg s0 (tailWitnessPayload80 b0 nuc anc part dp 0 false false)
  let d₁ (keep : Fin (pos24TailSpan8 dp)) (_th rj : Bool) (z : Fin (2 ^ systemQubits)) : ℂ :=
    if (if keep.val < (tM (rOrb z)).val then sgn z else rj) then (-1 : ℂ) else 1
  let d₂ (keep : Fin (pos24TailSpan8 dp)) (_th rj : Bool) (z : Fin (2 ^ systemQubits)) : ℂ :=
    if (if keep.val < (pos24TailMag30 (rOrb z)).val then sgn z else rj) then (-1 : ℂ) else 1
  have hTerm : ∀ (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool),
      sysBlock80Of tM tierBQftFull cfg s0
          (tailWitnessPayload80 b0 nuc anc part dp keep.val th rj) -
        sysBlock80Of pos24TailMag30 tierBQftFull cfg s0
          (tailWitnessPayload80 b0 nuc anc part dp keep.val th rj) =
      Wᴴ * Matrix.diagonal (d₁ keep th rj) * W -
        Wᴴ * Matrix.diagonal (d₂ keep th rj) * W := fun keep th rj ↦ by
    rw [sysBlock80Of_eq_wSlice80_conj, sysBlock80Of_eq_wSlice80_conj, hW keep th rj]
    have hd1 : (fun z : Fin (2 ^ systemQubits) ↦ if posPhaseBit true pos24TailSign tM
        (coreBetaOf s0 (tailWitnessPayload80 b0 nuc anc part dp keep.val th rj) z) then
        (-1 : ℂ) else 1) = d₁ keep th rj := funext fun z ↦ by
      dsimp only [d₁]
      rw [hPh tM keep th rj z]
    have hd2 : (fun z : Fin (2 ^ systemQubits) ↦ if posPhaseBit true pos24TailSign pos24TailMag30
        (coreBetaOf s0 (tailWitnessPayload80 b0 nuc anc part dp keep.val th rj) z) then
        (-1 : ℂ) else 1) = d₂ keep th rj := funext fun z ↦ by
      dsimp only [d₂]
      rw [hPh pos24TailMag30 keep th rj z]
    rw [hd1, hd2]
  rw [sum_conj_sub_diagonal_eq W _ d₁ d₂ hTerm]
  refine (norm_wSlice80_conj_le W _ (norm_wSlice80_le_one cfg s0 _)).trans ?_
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun z ↦ ?_
  exact norm_tail_keep_th_rj_sub_of_tM_le tM D (sgn z) (rOrb z)
    (hLo (rOrb z)) (hHi (rOrb z)) (hSpan z)

theorem norm_tail_keep_th_rj_sysBlock80Of_slot2_of_tM_le
    (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (D : ℕ)
    (hLo : ∀ idx, (pos24TailMag30 idx).val ≤ (tM idx).val + D)
    (hHi : ∀ idx, (tM idx).val ≤ (pos24TailMag30 idx).val + D) (cfg : Configuration)
    (l : Fin 216) (anc : Fin 218) (dp : Fin 8) : ‖∑ keep : Fin (pos24TailSpan8 dp), ∑ th :
    Bool, ∑ rj : Bool, (sysBlock80Of tM tierBQftFull cfg false (tailWitnessPayload80 0 l.val
    anc.val 0 dp keep.val th rj) - sysBlock80Of pos24TailMag30 tierBQftFull cfg false
    (tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj))‖ ≤ 4 * (D : ℝ) :=
  norm_tail_keep_th_rj_wSlice80_sub_le tM D hLo hHi cfg false 0 l.val anc.val 0 dp
    (fun z ↦ tetRank65 (canonTriple128 (nyq128Equiv3D
      (Pos24Slot2FermionicBridge.slotCoordSys z 0, nyqParity3DEquivFin8.symm dp))))
    (fun z ↦ Bool.not (pos24TailSign (tetRank65 (canonTriple128 (nyq128Equiv3D
      (Pos24Slot2FermionicBridge.slotCoordSys z 0, nyqParity3DEquivFin8.symm dp))))))
    (wSlice80_tailWitness_eq_zero_slot2 cfg l anc dp)
    (fun tM' keep th rj z ↦ posPhaseBit_tailWitness_slot2_of_tM tM' l anc dp keep th rj z)
    (fun z ↦ Pos24Slot2FermionicBridge.slot2Tail_mag_le_span dp
      (Pos24Slot2FermionicBridge.slotCoordSys z 0))

theorem norm_tail_keep_th_rj_sysBlock80Of_slot4_of_tM_le
    (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (D : ℕ)
    (hLo : ∀ idx, (pos24TailMag30 idx).val ≤ (tM idx).val + D)
    (hHi : ∀ idx, (tM idx).val ≤ (pos24TailMag30 idx).val + D) (cfg : Configuration)
    (b0 : Fin 8) (anc : Fin 218) (part : Fin 217) (dp : Fin 8) : ‖∑ keep : Fin
    (pos24TailSpan8 dp), ∑ th : Bool, ∑ rj : Bool, (sysBlock80Of tM tierBQftFull cfg true
    (tailWitnessPayload80 b0.val 0 anc.val part.val dp keep.val th rj) - sysBlock80Of
    pos24TailMag30 tierBQftFull cfg true (tailWitnessPayload80 b0.val 0 anc.val part.val dp
    keep.val th rj))‖ ≤ 4 * (D : ℝ) :=
  norm_tail_keep_th_rj_wSlice80_sub_le tM D hLo hHi cfg true b0.val 0 anc.val part.val dp
    (fun z ↦ tetRank65 (canonTriple128 (Pos24Slot4FermionicBridge.s4TD
      (Pos24Slot4FermionicBridge.nyqP8 b0)
      (ancPar (Pos24Slot4FermionicBridge.nyqP8 b0)
        (nyq128Equiv3D (0, Pos24Slot4FermionicBridge.nyqP8 dp))) part z)))
    (fun z ↦ pos24TailSign (tetRank65 (canonTriple128 (Pos24Slot4FermionicBridge.s4TD
      (Pos24Slot4FermionicBridge.nyqP8 b0)
      (ancPar (Pos24Slot4FermionicBridge.nyqP8 b0)
        (nyq128Equiv3D (0, Pos24Slot4FermionicBridge.nyqP8 dp))) part z))))
    (wSlice80_tailWitness_eq_zero_slot4 cfg b0 anc part dp)
    (fun tM' keep th rj z ↦ posPhaseBit_tailWitness_slot4_of_tM tM' b0 anc part dp keep th rj z)
    (fun z ↦ (Pos24Slot4FermionicBridge.td_pr b0 dp part z).2.1)

theorem sysBlock80Mod4Of_sub_eq_sysBlock80Of_sub
    (tM₁ tM₂ : Fin orbitCount47905 → Fin (2 ^ 30)) (cfg : Configuration) (s0 : Bool)
    (p80 : BitAssignment 80) : sysBlock80Mod4Of tM₁ tierBQftFull cfg s0 p80 - sysBlock80Mod4Of
    tM₂ tierBQftFull cfg s0 p80 = sysBlock80Of tM₁ tierBQftFull cfg s0 p80 - sysBlock80Of tM₂
    tierBQftFull cfg s0 p80 := by
  rw [sysBlock80Mod4Of_eq_wSlice80_conj, sysBlock80Mod4Of_eq_wSlice80_conj,
      sysBlock80Of_eq_wSlice80_conj, sysBlock80Of_eq_wSlice80_conj,
      ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub,
      ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  exact congrArg (· * wSlice80 cfg s0 p80) (congrArg ((wSlice80 cfg s0 p80)ᴴ * ·) (congrArg
    Matrix.diagonal (funext fun z ↦ posPhaseBitMod4_sub_eq_posPhaseBit_sub tM₁ tM₂ (coreBetaOf
    s0 p80 z))))

theorem coherentSysOp80Mod4Of_sub_eq_coherentSysOp80Of_sub
    (tM₁ tM₂ : Fin orbitCount47905 → Fin (2 ^ 30)) (cfg : Configuration) (s0 : Bool)
    (mu : BitAssignment 80 → ℝ) : coherentSysOp80Mod4Of tM₁ tierBQftFull cfg s0 mu -
    coherentSysOp80Mod4Of tM₂ tierBQftFull cfg s0 mu = coherentSysOp80Of tM₁ tierBQftFull cfg
    s0 mu - coherentSysOp80Of tM₂ tierBQftFull cfg s0 mu := by
  unfold coherentSysOp80Mod4Of coherentSysOp80Of
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← smul_sub, ← smul_sub, sysBlock80Mod4Of_sub_eq_sysBlock80Of_sub]

theorem tierBB2RawIdMod4Of_sub_eq (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (cfg : Configuration) :
    tierBB2RawIdMod4Of tM cfg - tierBB2RawIdMod4 cfg =
      tierBB2RawIdOf tM cfg - tierBB2RawId cfg :=
  coherentSysOp80Mod4Of_sub_eq_coherentSysOp80Of_sub tM pos24TailMag30 cfg false (pos80IdealDist
    false)

theorem tierBB4IdMod4Of_sub_eq (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (cfg : Configuration)
    : tierBB4IdMod4Of tM cfg - tierBB4IdMod4 cfg = tierBB4IdOf tM cfg - tierBB4Id cfg :=
  coherentSysOp80Mod4Of_sub_eq_coherentSysOp80Of_sub tM pos24TailMag30 cfg true (pos80IdealDist
    true)

theorem tierBB2IdMod4Of_sub_eq (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (cfg : Configuration)
    : tierBB2IdMod4Of tM cfg - tierBB2IdMod4 cfg = tierBB2IdOf tM cfg - tierBB2Id cfg := by
  have hIdRaw : tierBB2RawId = tierBB2RawIdOf pos24TailMag30 := rfl
  unfold tierBB2IdMod4 tierBB2IdMod4Of tierBB2IdOf tierBB2Id
  rw[hIdRaw, ← PosPostPrep80L1BoundsS3.mMergedBUnitTwosGen_eq_mergedPosSlot2BUnitTwosGen,
      ← PosPostPrep80L1BoundsS3.mMergedBUnitTwosGen_eq_mergedPosSlot2BUnitTwosGen,
      ← PosPostPrep80L1BoundsS3.mMergedBUnitTwosGen_eq_mergedPosSlot2BUnitTwosGen,
      ← PosPostPrep80L1BoundsS3.mMergedBUnitTwosGen_eq_mergedPosSlot2BUnitTwosGen]
  unfold MergedVepTopCoinCollapse.mMergedBUnitTwosGen
    MergedVepTopCoinCollapse.mVepFromSlot2TwosOp MergedVepTopCoinCollapse.mVepGen
  rw [← smul_sub, ← smul_sub, add_sub_add_comm, add_sub_add_comm (tierBB2RawIdOf tM cfg),
      ← smul_sub, ← smul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hHead : tierBB2RawIdMod4Of tM cfg - tierBB2RawIdMod4Of pos24TailMag30 cfg =
      tierBB2RawIdOf tM cfg - tierBB2RawIdOf pos24TailMag30 cfg :=
    tierBB2RawIdMod4Of_sub_eq tM cfg
  rw [hHead]
  refine congrArg ((((108 : ℝ) / 109 : ℝ) : ℂ) • ·)
    (congrArg ((tierBB2RawIdOf tM cfg - tierBB2RawIdOf pos24TailMag30 cfg) + ·)
      (congrArg (((1 : ℝ) / (108 * 8) : ℂ) • ·) (Finset.sum_congr rfl fun bP _ ↦ ?_)))
  rw [conj_sum_mul_sub, conj_sum_mul_sub]
  refine congrArg (fun S : Operator (2 ^ systemQubits) ↦ (mProj24_sp.embedUnitary
    (uProjPlus512_3D bP)).1ᴴ * S * (mProj24_sp.embedUnitary (uProjPlus512_3D bP)).1)
    (Finset.sum_congr rfl fun yIdx _ ↦ ?_)
  exact congrArg (mProjBasisGen mProj24_sp yIdx * ·) (tierBB2RawIdMod4Of_sub_eq tM _)

theorem pp_p3_mod4 (s0 : Bool) (p80 : BitAssignment 80) (z : Fin (2 ^ systemQubits)) :
    posPhaseBitMod4 true pos24TailSign pos24TailMag30 (cBeta s0 p80 (pSmP3 z)) =
      posPhaseBitMod4 true pos24TailSign pos24TailMag30 (cBeta s0 p80 z) := by
  refine posPhaseBitMod4_eq_of_eq_active true pos24TailSign pos24TailMag30 _ _ fun w hw ↦ ?_
  refine cb_p3 s0 p80 z w ?_
  by_cases hlt : w.val < 3924
  · exact Or.inl hlt
  · right
    have : ¬(3924 ≤ w.val ∧ w.val < 3948) := fun h ↦ hw (Or.inl h)
    omega

section HpowStep_19
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_19 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem bs_cc_mod4
    (qft : FullSysQft654Bundle) (hqft : qft.uQft654 = qft64Ideal654Unitary)
    (cfg : Configuration) (p80 : BitAssignment 80)
    (hanc : _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
      p80 (pos80SubIdx 14 8 (by decide) j)) < 218) :
    let i : Fin 218 :=
      ⟨_root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
      p80 (pos80SubIdx 14 8 (by decide) j)), hanc⟩
    let b₀ := Pos24Slot4FermionicBridge.pB0 p80
    let b₁ := Pos24Slot4FermionicBridge.pB1 p80
    smToTwosSysUnitary.1 *
        sysBlockAtPayloadGen pos24_coreWires80_eq.symm
          (pos24ConjCore80Mod4Of pos24TailMag30 qft cfg).1 true p80 *
        smToTwosSysUnitary.1 =
      (s4CU b₀ b₁ i).1ᴴ *
        Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
          if posPhaseBitMod4 true pos24TailSign pos24TailMag30 (cBeta true p80 z)
            then (-1 : ℂ) else 1) *
        (s4CU b₀ b₁ i).1 := by
  intro i b₀ b₁
  have hQftPres : QftPreservesCoset3 qft := qftPreservesCoset3_of_eq_ideal qft hqft
  let U_qft := (fullSysQftCoreUnitary pos24_6_le_80 qft).1
  let U_tw := (castUnitaryPow2 pos24_core80_eq_twist80.symm
    (uTwistParam true pos24_22_le_80 cfg)).1
  let d_fn : Fin (2 ^ systemQubits) → ℂ := fun z ↦
    if posPhaseBitMod4 true pos24TailSign pos24TailMag30 (cBeta true p80 z) then (-1 : ℂ) else 1
  let D_kar := Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
    ∏ e : Fin 218, karatsubaOutPhase3D (sCd z e))
  have hQft_mul_off : sysBlockAtPayloadGen pos24_coreWires80_eq.symm U_qft true p80 * oSU.1 =
      D_kar * (vSU b₁).1 := by
    have hoff_def : oSU =
        (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary o18U).prod := rfl
    have hvee_def : vSU b₁ =
        (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (vB18 b₁)).prod := rfl
    rw [sb_qf qft hqft true p80, hoff_def, ← u_mv, lf_pm]
    have h18 : (List.ofFn fun e : Fin 218 ↦
      (rEl_sp e).embedUnitary (qft64OffsetUnitary3D b₁ * o18U)) =
        (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (oP18 * vB18 b₁)) :=
      congrArg List.ofFn (funext fun _ ↦ congrArg (rEl_sp _).embedUnitary
        (Subtype.ext (qf_o1 b₁)))
    rw [h18, ← lf_pm, u_mv, lf_op, ← hvee_def]
  have hKar_cancel : D_karᴴ * Matrix.diagonal d_fn * D_kar = Matrix.diagonal d_fn :=
    ud_cd _ d_fn fun z ↦ by
      rw [star_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun e _ ↦ karatsubaOutPhase3D_unit (sCd z e)
  let P_proj := fwdPermUnitary pSmP3
  have hSm_left : smToTwosSysUnitary.1 = P_proj.1ᴴ * smToTwos654SysUnitary.1ᴴ := by
    rw [← smToTwosSysUnitary_conjTranspose, sm_p3, Matrix.conjTranspose_mul]
  have hSm_right : smToTwosSysUnitary.1 = smToTwos654SysUnitary.1 * P_proj.1 := sm_p3
  have hDiag_proj : P_proj.1ᴴ * Matrix.diagonal d_fn * P_proj.1 = Matrix.diagonal d_fn := by
    rw [fwdPermUnitary_conj_diagonal]
    refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
    dsimp only [Function.comp_apply, d_fn]
    rw [pp_p3_mod4]
  have hB_fac : sysBlockAtPayloadGen pos24_coreWires80_eq.symm
      (pos24ConjCore80Mod4Of pos24TailMag30 qft cfg).1 true p80 = (sysBlockAtPayloadGen
      pos24_coreWires80_eq.symm U_qft true p80 * sysBlockAtPayloadGen
      pos24_coreWires80_eq.symm U_tw true p80)ᴴ * Matrix.diagonal d_fn * (sysBlockAtPayloadGen
      pos24_coreWires80_eq.symm U_qft true p80 * sysBlockAtPayloadGen
      pos24_coreWires80_eq.symm U_tw true p80) := by
    have hTw_comm : ∀ a, U_tw * rAncFlag80.basisOutcomeProjector a =
        rAncFlag80.basisOutcomeProjector a * U_tw :=
      fun a ↦ uTwistParam_cast_comm_highReg_proj pos24_core80_eq_twist80.symm cfg rAncFlag80
        rAncFlag80_wire_ge_3948 a
    have h1 := sysBlockAtPayloadGen_conj_diagSign qft (qf_an qft hQftPres) cfg
      (posPhaseBitMod4 true pos24TailSign pos24TailMag30) true p80
    dsimp only at h1
    rw [sysBlockAtPayloadGen_mul_of_preserves pos24_coreWires80_eq.symm U_qft U_tw true p80
      (pr_a _ hTw_comm true p80)] at h1
    exact h1
  exact bs_af smToTwosSysUnitary.1 smToTwos654SysUnitary.1 P_proj.1 (sysBlockAtPayloadGen
    pos24_coreWires80_eq.symm (pos24ConjCore80Mod4Of pos24TailMag30 qft cfg).1 true p80)
    (sysBlockAtPayloadGen pos24_coreWires80_eq.symm U_qft true p80)
    (sysBlockAtPayloadGen pos24_coreWires80_eq.symm U_tw true p80) oSU.1
    ((rEl_sp 0).embedUnitary (slot4CosetDiag18 b₀ b₁)).1
    (permutationUnitary (permElectron (Equiv.swap i 0))).1 D_kar (vSU b₁).1 (s4CU b₀ b₁ i).1
    (Matrix.diagonal d_fn) hSm_left hSm_right hB_fac (sb_tw cfg p80 hanc) hQft_mul_off
    ((congrArg Subtype.val (rfl : s4CU b₀ b₁ i = _)).trans (u_m3 _ _ _)) hKar_cancel
    (sc_p3 b₀ b₁ i) hDiag_proj

end HpowStep_19
/-- Mod-4 Slot-4 head sign bit on partner hit set `S` for threshold bit `th`. -/
def mod4Slot4HeadBit (th : Bool) (S : Finset (Fin 218)) : Bool :=
  let rawBit := if S.card % 2 == 1 then th else Bool.not (decide (S.card % 4 = 0))
  Bool.not rawBit

theorem mod4Slot4HeadBit_pauliCap_eq (S : Finset (Fin 218)) (hcard : S.card ≤ 2) : (1 / 2 : ℂ)
    * ((if mod4Slot4HeadBit false S then (-1 : ℂ) else 1) + (if mod4Slot4HeadBit true S then
    (-1 : ℂ) else 1)) = (S.card : ℂ) - (1 : ℂ) := by
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  have ite_t : (if true then (-1 : ℂ) else 1) = -1 := ite_eq_left rfl
  have ite_f : (if false then (-1 : ℂ) else 1) = 1 := ite_eq_right Bool.false_ne_true
  unfold mod4Slot4HeadBit
  dsimp only
  rcases hcases with h0 | h1 | h2
  · rw [h0]
    have hf : Bool.not (if 0 % 2 == 1 then false else Bool.not (decide (0 % 4 = 0))) = true := rfl
    have ht : Bool.not (if 0 % 2 == 1 then true else Bool.not (decide (0 % 4 = 0))) = true := rfl
    rw [hf, ht, ite_t, Nat.cast_zero]
    ring
  · rw [h1]
    have hf : Bool.not (if 1 % 2 == 1 then false else Bool.not (decide (1 % 4 = 0))) = true := rfl
    have ht : Bool.not (if 1 % 2 == 1 then true else Bool.not (decide (1 % 4 = 0))) = false := rfl
    rw [hf, ht, ite_t, ite_f, Nat.cast_one]
    ring
  · rw [h2]
    have hf : Bool.not (if 2 % 2 == 1 then false else Bool.not (decide (2 % 4 = 0))) = false := rfl
    have ht : Bool.not (if 2 % 2 == 1 then true else Bool.not (decide (2 % 4 = 0))) = false := rfl
    rw [hf, ht, ite_f, Nat.cast_ofNat]
    ring

theorem pp_hw_mod4
    (b0 : Fin 8) (anc : Fin 218) (k : Fin 56) (pid : Fin 6) (sm : Fin 8) (th rj : Bool)
    (z : Fin (2 ^ systemQubits)) :
    let p80 := headWitnessPayload80 b0.val 0 anc.val k pid sm th rj
    let dH := pos24HeadFine k pid sm
    let b₀ := nyqP8 b0
    let S := s4H0 b₀ dH z
    posPhaseBitMod4 true pos24TailSign pos24TailMag30 (cBeta true p80 z) =
      mod4Slot4HeadBit th S := by
  intro p80 dH b₀ S
  let rCore := QRegExt.ofFin posCoreWires
  let β := cBeta true p80 z
  have hw2 : β (wSlot2Core rCore) = 0 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hw1 : β (wSlot1Core rCore) = 0 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hw0 : β (wSlot0Core rCore) = 1 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hwSub : β (wSubReject rCore) = 0 := cB_pay true p80 z ⟨62, by decide⟩
  have hwHead : β (wIsHead rCore) = 1 := cB_pay true p80 z ⟨30, by decide⟩
  have hwTh : (β (wHeadThresh rCore) == 1) = th := by
    have h1 : β (wHeadThresh rCore) = (if th then 1 else 0) := cB_pay true p80 z ⟨31, by decide⟩
    rw [h1]
    cases th <;> rfl
  have hrAnc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β =
    anc.val :=
    (coreBetaOf_subIdx8_regVal true p80 z 14 (by decide) (rAnchorIdx rCore) fun _ ↦ rfl).trans
      (hw_mt b0 anc k pid sm th rj).2.2
  have hTail0 : tailAndSlackPhaseBitSpec true pos24TailSign pos24TailMag30 β = false := by
    unfold tailAndSlackPhaseBitSpec
    have h01 : ((0 : ZMod 2) == 1) = false := rfl
    have h11 : ((1 : ZMod 2) == 1) = true := rfl
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hrAnc, anc.isLt, h01, h11,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, IsEmpty.forall_iff, decide_true,
      Bool.and_false, Bool.and_self, ↓reduceIte]
  have hFine : fineCoordOfReg21 (rHeadFine21 rCore) β = dH :=
    coreBetaOf_headWitness_fine21 true b0.val 0 anc.val k pid sm th rj z
  have hB0 : ∀ w : Fin 3, (if parity3OfReg (rCosetB0 rCore) β w then (1 : Fin 2) else 0) = b₀ w :=
    fun w ↦ by
      have hdec := parity3OfReg_decide_eq_of_val (rCosetB0 rCore) β b₀ (fun u ↦ by
        have hb_eq : β (rCosetB0 rCore u) = p80 (pos80SubIdx 3 3 (by decide) u) :=
          cB_pay true p80 z _
        rw [hb_eq]
        exact congrArg (fun f ↦ (f u).val) (hw_mt b0 anc k pid sm th rj).1) w
      rw [hdec, it_d2]
  have hEn : headEnBoolSpec β = true := by
    unfold headEnBoolSpec
    have h00 : ((0 : ZMod 2) == 0) = true := rfl
    have h01 : ((0 : ZMod 2) == 1) = false := rfl
    have h11 : ((1 : ZMod 2) == 1) = true := rfl
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hrAnc, anc.isLt,
      h00, h01, h11, Bool.not_false, Bool.not_true, Bool.false_eq_true, IsEmpty.forall_iff,
      decide_true, Bool.and_self]
  have hHit : headHitSetSpec β = S := by
    unfold headHitSetSpec
    have h11 : ((1 : ZMod 2) == 1) = true := rfl
    have hslot : ∀ e : Fin 218, slotSubGridCoord64
        (rElecSlot (QRegExt.ofFin posCoreWires) e) β = sCd z e := ss_cb true p80 z
    dsimp only [rCore] at hB0
    simp only [rCore, hw0, hFine, h11, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Bool.false_or, hB0, hslot]
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true, Bool.and_eq_true,
      decide_eq_true_eq, S, s4H0, Finset.mem_erase]
    exact and_congr (not_congr ⟨fun h ↦ Fin.ext h, congrArg Fin.val⟩) Iff.rfl
  have hHead : headPhaseBitMod4Spec β = mod4Slot4HeadBit th S := by
    unfold headPhaseBitMod4Spec mod4Slot4HeadBit
    have h11 : ((1 : ZMod 2) == 1) = true := rfl
    dsimp only [rCore] at hw0 hwTh
    simp only [hEn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hw0, h11, hwTh, hHit]
  unfold posPhaseBitMod4
  rw [hHead, hTail0, Bool.xor_false]

theorem s4_head_inner_mod4_eq
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
    (b0 : Fin 8) (nuc : Fin 1) (anc : Fin 218) (k : Fin 56) (pid : Fin 6) (sm : Fin 8) :
    let P := fermionicProjector spinUp
    let blkSmMod4 : BitAssignment 80 → Operator (2 ^ systemQubits) := fun p80 ↦
        smToTwosSysUnitary.1 * sysBlock80Mod4Of pos24TailMag30 tierBQftFull cfg true p80 *
        smToTwosSysUnitary.1
    (∑ th : Bool, ∑ rj : Bool,
        blkSmMod4 (headWitnessPayload80 b0.val nuc.val anc.val k pid sm th rj)) * P =
      (4 : ℂ) • ((veePairAt (nyqP8 b0) (pos24HeadFine k pid sm) anc - 1) * P) := by
  intro P blkSmMod4
  have hnuc0 : nuc.val = 0 := Nat.lt_one_iff.mp nuc.isLt
  rw [hnuc0]
  let dH := pos24HeadFine k pid sm
  let b₀ := nyqP8 b0
  let b₁ := ancPar b₀ dH
  let U := s4CU b₀ b₁ anc
  let d_th : Bool → Fin (2 ^ systemQubits) → ℂ := fun th z ↦
    if mod4Slot4HeadBit th (s4H0 b₀ dH z) then (-1 : ℂ) else 1
  let d_avg : Fin (2 ^ systemQubits) → ℂ := fun z ↦ (1 / 2 : ℂ) * (d_th false z + d_th true z)
  have hblk_th : ∀ (th rj : Bool),
      blkSmMod4 (headWitnessPayload80 b0.val 0 anc.val k pid sm th rj) =
        U.1ᴴ * Matrix.diagonal (d_th th) * U.1 := by
    intro th rj
    rcases hw_mt b0 anc k pid sm th rj with ⟨hb0, hb1, hanc_val⟩
    have h1 := bs_cc_mod4 tierBQftFull rfl cfg
      (headWitnessPayload80 b0.val 0 anc.val k pid sm th rj)
      (by rw [hanc_val]; exact anc.isLt)
    dsimp only at h1
    have hi_eq : ∀ (hp : 14 + 8 ≤
      80) (hlt : _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
        headWitnessPayload80 b0.val 0 anc.val k pid sm th rj (pos80SubIdx 14 8 hp j)) < 218),
        (⟨_root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
          headWitnessPayload80 b0.val 0 anc.val k pid sm th rj
        (pos80SubIdx 14 8 hp j)), hlt⟩ : Fin 218) = anc := fun _ _ ↦ Fin.ext hanc_val
    rw [hb0, hb1, hi_eq] at h1
    have hdiag : (fun z : Fin (2 ^ systemQubits) ↦ if posPhaseBitMod4 true pos24TailSign
        pos24TailMag30 (cBeta true (headWitnessPayload80 b0.val 0 anc.val k pid sm th rj) z)
        then (-1 : ℂ) else 1) = d_th th := by
      funext z
      dsimp only [d_th]
      rw [pp_hw_mod4]
    dsimp only [blkSmMod4, sysBlock80Mod4Of, U, b₁, b₀, dH]
    rw [h1, hdiag]
  simp_rw [hblk_th, Fintype.sum_bool]
  have hsum4 : (U.1ᴴ * Matrix.diagonal (d_th true) * U.1 + U.1ᴴ * Matrix.diagonal (d_th true)
      * U.1) + (U.1ᴴ * Matrix.diagonal (d_th false) * U.1 + U.1ᴴ * Matrix.diagonal (d_th
      false) * U.1) = (4 : ℂ) • (U.1ᴴ * Matrix.diagonal d_avg * U.1) := by
    have hd4 : (Matrix.diagonal (d_th true) + Matrix.diagonal (d_th true)) +
        (Matrix.diagonal (d_th false) + Matrix.diagonal (d_th false)) = (4 : ℂ) •
        Matrix.diagonal d_avg := dg_s4 (d_th true) (d_th false)
    calc (U.1ᴴ * Matrix.diagonal (d_th true) * U.1 + U.1ᴴ * Matrix.diagonal (d_th true) * U.1) +
          (U.1ᴴ * Matrix.diagonal (d_th false) * U.1 + U.1ᴴ * Matrix.diagonal (d_th false) * U.1)
      _ = U.1ᴴ * ((Matrix.diagonal (d_th true) + Matrix.diagonal (d_th true)) +
            (Matrix.diagonal (d_th false) + Matrix.diagonal (d_th false))) * U.1 := by
          simp only [Matrix.mul_add, Matrix.add_mul]
      _ = (4 : ℂ) • (U.1ᴴ * Matrix.diagonal d_avg * U.1) := by
          rw [hd4, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsum4, Matrix.smul_mul]
  refine congrArg ((4 : ℂ) • ·) ?_
  have hint := sc_di b₀ dH anc
  dsimp only at hint
  dsimp only [U, b₁]
  refine dg_cz (s4CU b₀ (ancPar b₀ dH) anc) _ P (fun z ↦ (s4H0 b₀ dH z).card) d_avg hint
    (singleAnchorPairOp_cubic_mul_fermionicProjector_zero (fun y₀ ↦ (ancTgt y₀ b₀ dH).1) anc
    spinUp (veeSubGridKet_orthonormal b₀) (veeSubGridKet_norm_sq (ancPar b₀ dH))) fun z hcard
    ↦ mod4Slot4HeadBit_pauliCap_eq (s4H0 b₀ dH z) hcard

theorem s4_fp_mod4 (cfg : Configuration) (spinUp : Finset (Fin numElectrons)) : (∑ x :
    HeadSupportIdx true, ((pos80Slot4Scale * pos80IdealDist true (pos80WitnessOf true (Sum.inl
    x)) : ℝ) : ℂ) • (smToTwosSysUnitary.1 * sysBlock80Mod4Of pos24TailMag30 tierBQftFull cfg
    true (pos80WitnessOf true (Sum.inl x)) * smToTwosSysUnitary.1)) * fermionicProjector
    spinUp = s4HR * fermionicProjector spinUp := by
  let P := fermionicProjector spinUp
  let blkSmMod4 : BitAssignment 80 → Operator (2 ^ systemQubits) := fun p80 ↦
      smToTwosSysUnitary.1 * sysBlock80Mod4Of pos24TailMag30 tierBQftFull cfg true p80 *
      smToTwosSysUnitary.1
  have htot_ne : (pos80Slot4TotNat : ℝ) ≠ 0 := pos80Slot4TotNat_cast_ne_zero
  have hw_eq : ∀ k : Fin 56,
      (pos80Slot4Scale *
          ((pos24HeadWeight56 k : ℝ) / (8 * 218 * 48 * 2 * 2 * pos80Slot4TotNat)) : ℝ) * 4 =
      (1 / 128 : ℝ) * (1 / 48 : ℝ) * ((pos24HeadWeight56 k : ℝ) / 2 ^ 30) := fun k ↦ by
    unfold pos80Slot4Scale
    field_simp [htot_ne]
    ring
  have hinner_smul : ∀ (c : ℂ) (b0 : Fin 8) (nuc : Fin 1) (anc : Fin 218) (k : Fin 56)
      (pid : Fin 6) (sm : Fin 8), (∑ th : Bool, ∑ rj : Bool, c • (blkSmMod4
      (headWitnessPayload80 b0.val nuc.val anc.val k pid sm th rj) * P)) = c • (4 : ℂ) •
      ((veePairAt (nyqP8 b0) (pos24HeadFine k pid sm) anc - 1) * P) := by
    intro c b0 nuc anc k pid sm
    calc (∑ th : Bool, ∑ rj : Bool,
          c • (blkSmMod4 (headWitnessPayload80 b0.val nuc.val anc.val k pid sm th rj) * P))
      _ = c • ((∑ th : Bool, ∑ rj : Bool,
            blkSmMod4 (headWitnessPayload80 b0.val nuc.val anc.val k pid sm th rj)) * P) := by
          simp only [Finset.smul_sum, Finset.sum_mul]
      _ = _ := by rw [s4_head_inner_mod4_eq cfg spinUp b0 nuc anc k pid sm]
  change (∑ x : HeadSupportIdx true, ((pos80Slot4Scale * pos80IdealDist true (pos80WitnessOf
    true (Sum.inl x)) : ℝ) : ℂ) • blkSmMod4 (pos80WitnessOf true (Sum.inl x))) * P = s4HR * P
  rw [Finset.sum_mul]
  dsimp only [HeadSupportIdx, ite_true]
  simp only [Fintype.sum_prod_type, pos80WitnessOf_eval_head, ↓reduceIte]
  dsimp only [pos80WitnessOf]
  simp_rw [Matrix.smul_mul, hinner_smul]
  have h1 : ∀ (b0 : Fin 8), ∑ nuc : Fin 1, ∑ anc : Fin 218, ∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm
      : Fin 8, ((pos80Slot4Scale * ((pos24HeadWeight56 k : ℝ) / (8 * 218 * 48 * 2 * 2 *
      pos80Slot4TotNat)) : ℝ) : ℂ) • (4 : ℂ) •
      ((veePairAt (nyqP8 b0) (pos24HeadFine k pid sm) anc - 1) * P) = ((1 / 128 : ℝ) : ℂ) • ∑
      d : NyqFine3D128, (kHead128 w128DualQ30 pos24CutNyq d : ℂ) •
      ((∑ anc : Fin 218, (veePairAt (nyqP8 b0) d anc - 1)) * P) := by
    intro b0
    rw [Fintype.sum_unique]
    let b₀ := nyqP8 b0
    let F : NyqFine3D128 → Operator (2 ^ systemQubits) := fun d ↦
      (∑ anc : Fin 218, (veePairAt b₀ d anc - 1)) * P
    have hswap : (∑ anc : Fin 218, ∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm : Fin 8,
        ((pos80Slot4Scale * ((pos24HeadWeight56 k : ℝ) / (8 * 218 * 48 * 2 * 2 *
        pos80Slot4TotNat)) : ℝ) : ℂ) • (4 : ℂ) • ((veePairAt b₀ (pos24HeadFine k pid sm) anc -
        1) * P)) = ((1 / 128 : ℝ) : ℂ) • ((1 / 48 : ℝ) : ℂ) • ∑ k : Fin 56, ∑ pid : Fin 6, ∑
        sm : Fin 8, (((pos24HeadWeight56 k : ℝ) / 2 ^ 30 : ℝ) : ℂ) • F (pos24OhPoint
        (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 218)))]
      simp only [Finset.smul_sum, smul_smul, F, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun pid _ ↦
        Finset.sum_congr rfl fun sm _ ↦ Finset.sum_congr rfl fun anc _ ↦ ?_
      refine congrArg (· • _) ?_
      have hc := congrArg (Complex.ofReal : ℝ → ℂ) (hw_eq k)
      push_cast at hc ⊢
      linear_combination hc
    rw [hswap, pos24_oh_head_sum_eq F, smul_smul (((1 / 48 : ℝ) : ℂ)) (48 : ℂ)]
    have h48 : (((1 / 48 : ℝ) : ℂ) * (48 : ℂ)) = 1 := by
      have hr : (1 / 48 : ℝ) * 48 = 1 := one_div_mul_cancel (by positivity)
      exact_mod_cast hr
    rw [h48, one_smul]
  trans (∑ b0 : Fin 8,
    ((1 / 128 : ℝ) : ℂ) •
      ∑ d : NyqFine3D128,
        (kHead128 w128DualQ30 pos24CutNyq d : ℂ) •
          ((∑ anc : Fin 218, (veePairAt (nyqP8 b0) d anc - 1)) * P))
  · exact Finset.sum_congr rfl fun b0 _ ↦ h1 b0
  rw [← Finset.smul_sum, Equiv.sum_comp nyqP8 (fun b₀ ↦
    ∑ d : NyqFine3D128,
      (kHead128 w128DualQ30 pos24CutNyq d : ℂ) •
        ((∑ anc : Fin 218, (veePairAt b₀ d anc - 1)) * P))]
  unfold s4HR
  rw [Matrix.smul_mul, Finset.sum_mul]
  refine congrArg (((1 / 128 : ℝ) : ℂ) • ·) ?_
  refine Finset.sum_congr rfl fun b₀ _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Matrix.smul_mul]

theorem sysBlock80Mod4Of_eq_sysBlock80Of_of_p80_30_zero
    (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (cfg : Configuration) (s0 : Bool)
    (p80 : BitAssignment 80) (hp30 : p80 30 = 0) : sysBlock80Mod4Of tM tierBQftFull cfg s0 p80
    = sysBlock80Of tM tierBQftFull cfg s0 p80 := by
  rw [sysBlock80Mod4Of_eq_wSlice80_conj, sysBlock80Of_eq_wSlice80_conj]
  refine congrArg (· * wSlice80 cfg s0 p80) (congrArg ((wSlice80 cfg s0 p80)ᴴ * ·) (congrArg
    Matrix.diagonal (funext fun z ↦ ?_)))
  have h0 : coreBetaOf s0 p80 z (wIsHead (QRegExt.ofFin posCoreWires)) = 0 := by
    change coreBetaOf s0 p80 z (rPosSubLocal ⟨30, by decide⟩) = 0
    rw [coreBetaOf_payload]
    exact hp30
  rw [posPhaseBitMod4_eq_posPhaseBit_of_wIsHead_zero true pos24TailSign tM _ h0]

theorem tierBB4IdMod4_mul_fermionicProjector_eq (cfg : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    (smToTwosSysUnitary.1 * tierBB4IdMod4 cfg * smToTwosSysUnitary.1) * fermionicProjector
    spinUp = (smToTwosSysUnitary.1 * tierBB4Id cfg * smToTwosSysUnitary.1) *
    fermionicProjector spinUp := by
  have hScaleNe : (pos80Slot4Scale : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt pos80Slot4Scale_pos)
  suffices hScaled :
      ((pos80Slot4Scale : ℂ) •
        (smToTwosSysUnitary.1 * tierBB4IdMod4 cfg * smToTwosSysUnitary.1)) *
        fermionicProjector spinUp =
      ((pos80Slot4Scale : ℂ) •
        (smToTwosSysUnitary.1 * tierBB4Id cfg * smToTwosSysUnitary.1)) *
        fermionicProjector spinUp by
    rw [Matrix.smul_mul, Matrix.smul_mul] at hScaled
    exact smul_right_injective _ hScaleNe hScaled
  have hRhs := Pos24Slot4FermionicBridge.c4_fp tierBQftFull rfl cfg spinUp
  change ((pos80Slot4Scale : ℂ) • (smToTwosSysUnitary.1 * tierBB4Id cfg *
    smToTwosSysUnitary.1)) * fermionicProjector spinUp = Pos24Slot4FermionicBridge.s4S *
    fermionicProjector spinUp at hRhs
  rw [hRhs]
  let F : BitAssignment 80 → ℝ → Operator (2 ^ systemQubits) := fun p80 r ↦
      ((pos80Slot4Scale * r : ℝ) : ℂ) • (smToTwosSysUnitary.1 * sysBlock80Mod4Of
      pos24TailMag30 tierBQftFull cfg true p80 * smToTwosSysUnitary.1)
  have hlhs : ((pos80Slot4Scale : ℂ) • (smToTwosSysUnitary.1 * tierBB4IdMod4 cfg *
      smToTwosSysUnitary.1)) = ∑ p80 : BitAssignment 80, F p80 (pos80IdealDist true p80) := by
    unfold tierBB4IdMod4 tierBB4IdMod4Of coherentSysOp80Mod4Of
    rw [Matrix.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p80 _ ↦ ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    dsimp only [F]
    push_cast
    rfl
  have hTailEq : (∑ y : TailSupportIdx true, F (pos80WitnessOf true (Sum.inr y))
      (pos80IdealDist true (pos80WitnessOf true (Sum.inr y)))) =
      Pos24Slot4FermionicBridge.s4TR := by
    rw [← Pos24Slot4FermionicBridge.st_tr tierBQftFull rfl cfg]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rcases y with ⟨b0, nuc, anc, part, ⟨dp, keep⟩, th, rj⟩
    have hp30 : pos80WitnessOf true (Sum.inr (b0, nuc, anc, part, ⟨dp, keep⟩, th, rj)) 30 = 0 := rfl
    dsimp only [F]
    rw [sysBlock80Mod4Of_eq_sysBlock80Of_of_p80_30_zero pos24TailMag30 cfg true _ hp30]
    rfl
  rw [hlhs, sum_over_pos80IdealDist_support true F (fun p80 ↦ by simp [F]),
      Fintype.sum_sum_type, Matrix.add_mul]
  dsimp only [F] at hTailEq ⊢
  rw [s4_fp_mod4 cfg spinUp, hTailEq, ← Matrix.add_mul, ← Pos24Slot4FermionicBridge.s4_ht]

/-- Mod-4 Slot-2 head sign bit at subgrid coordinate `y0` and threshold bit `th`. -/
def slot2HeadMod4Bit (y0 : NyqGrid3D64) (th : Bool) (z : Fin (2 ^ systemQubits)) : Bool :=
  let hs : Finset (Fin 218) := Finset.univ.filter (fun e ↦ decide (slotCoordSys z e = y0))
  if hs.card % 2 == 1 then th else Bool.not (decide (hs.card % 4 = 0))

theorem slot2HeadMod4Bit_pauliCap_eq (y0 : NyqGrid3D64) (z : Fin (2 ^ systemQubits)) (hle :
    (Finset.univ.filter (fun e : Fin 218 ↦ decide (slotCoordSys z e = y0))).card ≤ 2) :
    (1 / 2 : ℂ) * ((if slot2HeadMod4Bit y0 false z then (-1 : ℂ) else 1) + (if
    slot2HeadMod4Bit y0 true z then (-1 : ℂ) else 1)) = (1 : ℂ) - ((Finset.univ.filter (fun e
    : Fin 218 ↦ decide (slotCoordSys z e = y0))).card : ℂ) := by
  set c := (Finset.univ.filter (fun e : Fin 218 ↦ decide (slotCoordSys z e = y0))).card
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  have ite_t : (if true then (-1 : ℂ) else 1) = -1 := ite_eq_left rfl
  have ite_f : (if false then (-1 : ℂ) else 1) = 1 := ite_eq_right Bool.false_ne_true
  unfold slot2HeadMod4Bit
  change (1 / 2 : ℂ) * ((if (if c % 2 == 1 then false else Bool.not (decide (c % 4 = 0))) then
    (-1 : ℂ) else 1) + (if (if c % 2 == 1 then true else Bool.not (decide (c % 4 = 0))) then
    (-1 : ℂ) else 1)) = (1 : ℂ) - (c : ℂ)
  rcases hcases with h0 | h1 | h2
  · rw [h0]
    have hf : (if 0 % 2 == 1 then false else Bool.not (decide (0 % 4 = 0))) = false := rfl
    have ht : (if 0 % 2 == 1 then true else Bool.not (decide (0 % 4 = 0))) = false := rfl
    rw [hf, ht, ite_f, Nat.cast_zero]
    ring
  · rw [h1]
    have hf : (if 1 % 2 == 1 then false else Bool.not (decide (1 % 4 = 0))) = false := rfl
    have ht : (if 1 % 2 == 1 then true else Bool.not (decide (1 % 4 = 0))) = true := rfl
    rw [hf, ht, ite_f, ite_t, Nat.cast_one]
    ring
  · rw [h2]
    have hf : (if 2 % 2 == 1 then false else Bool.not (decide (2 % 4 = 0))) = true := rfl
    have ht : (if 2 % 2 == 1 then true else Bool.not (decide (2 % 4 = 0))) = true := rfl
    rw [hf, ht, ite_t, Nat.cast_ofNat]
    ring

theorem slot2_headMod4_conj_mul_fermionicProjector (c : Configuration) (l : Fin 216)
    (b : NyqParity3D) (y0 : NyqGrid3D64) (spinUp : Finset (Fin numElectrons)) : ((sysNucDiag48
    c l).1 * ((veeSysProdUnitary b).1ᴴ * ((1 / 2 : ℂ) • (Matrix.diagonal (fun z ↦ if
    slot2HeadMod4Bit y0 false z then (-1 : ℂ) else 1) + Matrix.diagonal (fun z ↦ if
    slot2HeadMod4Bit y0 true z then (-1 : ℂ) else 1))) * (veeSysProdUnitary b).1) *
    (sysNucDiag48 c l).1ᴴ) * fermionicProjector spinUp =
    (1 - nTot_sp (uenSubGridKet48 c l b y0)) * fermionicProjector spinUp := by
  let count : Fin (2 ^ systemQubits) → ℕ :=
    fun z ↦ (Finset.univ.filter (fun e : Fin 218 ↦ decide (slotCoordSys z e = y0))).card
  let mEntry : Fin (2 ^ systemQubits) → ℂ := fun z ↦ (1 / 2 : ℂ) * ((if slot2HeadMod4Bit y0
      false z then (-1 : ℂ) else 1) + (if slot2HeadMod4Bit y0 true z then (-1 : ℂ) else 1))
  let U : Operator (2 ^ systemQubits) := (veeSysProdUnitary b).1 * (sysNucDiag48 c l).1ᴴ
  have hW_u : (veeSysProdUnitary b).1ᴴ * (veeSysProdUnitary b).1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (veeSysProdUnitary b).2.1
  have hW_u' : (veeSysProdUnitary b).1 * (veeSysProdUnitary b).1ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (veeSysProdUnitary b).2.2
  have hD_u : (sysNucDiag48 c l).1ᴴ * (sysNucDiag48 c l).1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (sysNucDiag48 c l).2.1
  have hD_u' : (sysNucDiag48 c l).1 * (sysNucDiag48 c l).1ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (sysNucDiag48 c l).2.2
  have hU : Uᴴ * U = 1 := mul_adj_conjTranspose_mul_self hW_u hD_u'
  have hUU' : U * Uᴴ = 1 := mul_adj_mul_conjTranspose_self hD_u hW_u'
  have hD_sum : Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦ (count z : ℂ)) = ∑ e : Fin
      218, Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦ if slotCoordSys z e = y0 then (1
      : ℂ) else 0) := by
    rw [sum_diagonal_eq_slot2]
    congr 1; funext z
    simp only [count, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
      decide_eq_true_eq, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hconj_N : Uᴴ * Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦ (count z : ℂ)) * U =
      nTot_sp (uenSubGridKet48 c l b y0) := by
    change ((veeSysProdUnitary b).1 * (sysNucDiag48 c l).1ᴴ)ᴴ * Matrix.diagonal
      (fun z : Fin (2 ^ systemQubits) ↦ (count z : ℂ)) *
      ((veeSysProdUnitary b).1 * (sysNucDiag48 c l).1ᴴ) = nTot_sp (uenSubGridKet48 c l b y0)
    rw [← conj_outer_inner_eq (sysNucDiag48 c l).1 (veeSysProdUnitary b).1, hD_sum,
      conj_finset_sum_eq]
    have hinner : (∑ e : Fin 218, (veeSysProdUnitary b).1ᴴ * Matrix.diagonal (fun z : Fin (2 ^
        systemQubits) ↦ if slotCoordSys z e = y0 then (1 : ℂ) else 0) * (veeSysProdUnitary
        b).1) = ∑ e : Fin 218, op_sp (veeSubGridKet b y0) e := Finset.sum_congr rfl fun e _ ↦
        veeSysProdUnitary_conj_slotProj b e y0
    rw [hinner, conj_finset_sum_eq]
    unfold nTot_sp nSub_sp
    exact Finset.sum_congr rfl fun e _ ↦ sysNucDiag48_conj_op_veeSubGridKet c l b y0 e
  have hdiag : U * nTot_sp (uenSubGridKet48 c l b y0) = Matrix.diagonal
      (fun z : Fin (2 ^ systemQubits) ↦ (count z : ℂ)) * U := mul_eq_left_mul_of_conj_eq hUU'
      hconj_N
  have hm : ∀ z : Fin (2 ^ systemQubits), count z ≤ 2 → mEntry z = (1 : ℂ) - (count z : ℂ) :=
    fun z hle ↦ slot2HeadMod4Bit_pauliCap_eq y0 z hle
  have hcub : nTot_sp (uenSubGridKet48 c l b y0) * (nTot_sp (uenSubGridKet48 c l b y0) - 1) *
      (nTot_sp (uenSubGridKet48 c l b y0) - (2 : ℂ) • 1) * fermionicProjector spinUp = 0 :=
      nSub_cubic_mul_fermionicProjector_zero (uenSubGridKet48_norm_sq c l b y0) spinUp
      Finset.univ
  have hmain := diag_bch_lcu_eq_one_sub_of_cubic_zero hcub hU hdiag hm
  have hlhs : (sysNucDiag48 c l).1 * ((veeSysProdUnitary b).1ᴴ * ((1 / 2 : ℂ) •
      (Matrix.diagonal (fun z ↦ if slot2HeadMod4Bit y0 false z then (-1 : ℂ) else 1) +
      Matrix.diagonal (fun z ↦ if slot2HeadMod4Bit y0 true z then (-1 : ℂ) else 1))) *
      (veeSysProdUnitary b).1) * (sysNucDiag48 c l).1ᴴ = Uᴴ * Matrix.diagonal mEntry * U := by
    rw [smul_add_diagonal_eq]
    exact conj_outer_inner_eq (sysNucDiag48 c l).1 (veeSysProdUnitary b).1 (Matrix.diagonal mEntry)
  exact mul_right_eq_of_eq hlhs hmain

theorem posPhaseBitMod4_headWitness_slot2
    (l : Fin 216) (k : Fin 56) (pid : Fin 6) (sm : Fin 8) (th rj : Bool)
    (z : Fin (2 ^ systemQubits)) :
    let p80 := headWitnessPayload80 0 l.val 0 k pid sm th rj
    let dH := pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm
    posPhaseBitMod4 true pos24TailSign pos24TailMag30 (coreBetaOf false p80 z) =
      slot2HeadMod4Bit (nyq128Equiv3D.symm dH).1 th z := by
  intro p80 dH
  let rCore := QRegExt.ofFin posCoreWires
  let β := coreBetaOf false p80 z
  have hw2 : β (wSlot2Core rCore) = 0 := coreBetaOf_mid false p80 z _ (by decide) (by decide)
  have hw1 : β (wSlot1Core rCore) = 0 := coreBetaOf_mid false p80 z _ (by decide) (by decide)
  have hw0 : β (wSlot0Core rCore) = 0 := coreBetaOf_mid false p80 z _ (by decide) (by decide)
  have hwSub : β (wSubReject rCore) = 0 := coreBetaOf_payload false p80 z ⟨62, by decide⟩
  have hwHead : β (wIsHead rCore) = 1 := coreBetaOf_payload false p80 z ⟨30, by decide⟩
  have hwTh : (β (wHeadThresh rCore) == 1) = th := by
    have h1 : β (wHeadThresh rCore) = (if th then 1 else 0) :=
      coreBetaOf_payload false p80 z ⟨31, by decide⟩
    rw [h1]
    cases th <;> rfl
  have hrNuc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rCore) β =
    l.val :=
    (coreBetaOf_subIdx8_regVal false p80 z 6 (by decide) (rNucIdx rCore) fun _ ↦ rfl).trans
      (headWitnessPayload80_slot2_meta l k pid sm th rj).1
  have hrAnc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β =
    0 :=
    (coreBetaOf_subIdx8_regVal false p80 z 14 (by decide) (rAnchorIdx rCore) fun _ ↦ rfl).trans
      (headWitnessPayload80_slot2_meta l k pid sm th rj).2.1
  have hTail0 : tailAndSlackPhaseBitSpec true pos24TailSign pos24TailMag30 β = false := by
    unfold tailAndSlackPhaseBitSpec
    have hc1 : ((0 : ZMod 2) == 1) = false := by decide
    have hc4 : ((1 : ZMod 2) == 1) = true := by decide
    have h0lt : (0 : ℕ) < 218 := by decide
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hrNuc, l.isLt, hrAnc,
      hc1, hc4, h0lt, Bool.not_false, Bool.false_eq_true,
      implies_true, false_implies, decide_true, Bool.and_self, Bool.not_true, ↓reduceIte]
  have hFine : fineCoordOfReg21 (rHeadFine21 rCore) β = dH :=
    coreBetaOf_headWitness_fine21 false 0 l.val 0 k pid sm th rj z
  have hEn : headEnBoolSpec β = true := by
    unfold headEnBoolSpec
    have h00 : ((0 : ZMod 2) == 0) = true := rfl
    have h01 : ((0 : ZMod 2) == 1) = false := rfl
    have h11 : ((1 : ZMod 2) == 1) = true := rfl
    have h0lt : (0 : ℕ) < 218 := by decide
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hrNuc, l.isLt, hrAnc, h0lt,
      h00, h01, h11, Bool.not_false, implies_true, decide_true, Bool.and_self]
  have hHit : headHitSetSpec β =
      Finset.univ.filter (fun e : Fin 218 ↦
        decide (slotCoordSys z e = (nyq128Equiv3D.symm dH).1)) := by
    unfold headHitSetSpec
    have h01 : ((0 : ZMod 2) == 1) = false := rfl
    simp only [rCore, hw0, hFine, h01, Bool.not_false, ↓reduceIte, Bool.true_or, Bool.true_and,
      β, slotSubGridCoord64_coreBetaOf_slot2_eq]
    have hy_eq : (fun w : Fin 3 ↦ (⟨(dH w).val / 2, by have := (dH w).isLt; omega⟩ : Fin 64)) =
        (nyq128Equiv3D.symm dH).1 := by
      funext w; apply Fin.ext
      exact (nyq128Equiv3D_symm_fst_val_slot2 dH w).symm
    rw [hy_eq]
  have hHead : headPhaseBitMod4Spec β = slot2HeadMod4Bit (nyq128Equiv3D.symm dH).1 th z := by
    unfold headPhaseBitMod4Spec slot2HeadMod4Bit
    have h01 : ((0 : ZMod 2) == 1) = false := rfl
    dsimp only [rCore] at hw0 hwTh
    simp only [hEn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hw0, h01, hwTh, hHit]
  unfold posPhaseBitMod4
  rw [hHead, hTail0, Bool.xor_false]

/-- Signed-magnitude-conjugated Mod-4 Slot-2 slice block at payload `p80`. -/
noncomputable def blkSmSlot2Mod4 (c : Configuration) (p80 : BitAssignment 80) : Operator
    (2 ^ systemQubits) := smToTwosSysUnitary.1 * sysBlock80Mod4Of pos24TailMag30 tierBQftFull
    c false p80 * smToTwosSysUnitary.1

section HpowStep_20
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_20 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem blkSmSlot2Mod4_eq_cleanConj (c : Configuration) (p80 : BitAssignment 80) (l : Fin 216)
    (anc : Fin 218) (b₁ : NyqParity3D) (hl : payloadNucNat p80 = l.val)
    (hanc : payloadAncNat p80 = anc.val) (hb₁ : payloadB1Parity p80 = b₁) : blkSmSlot2Mod4 c
    p80 = (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1ᴴ *
    ((sysNucDiag48 c l).1 * ((veeSysProdUnitary b₁).1ᴴ * Matrix.diagonal (fun z : Fin (2 ^
    systemQubits) ↦ if posPhaseBitMod4 true pos24TailSign pos24TailMag30 (coreBetaOf false p80
    z) then (-1 : ℂ) else 1) * (veeSysProdUnitary b₁).1) * (sysNucDiag48 c l).1ᴴ) *
    (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1 := by
  let W := ((List.ofFn fun e : Fin 218 ↦
    (rEl_sp e).embedUnitary (qft64OffsetUnitary3D b₁)).prod).1 *
    (slot2RawKickDiag c l.val *
      (fwdPermUnitary ((barrelSysPerm anc.val).trans xor32SysPerm)).1)
  let f : Fin (2 ^ systemQubits) → ℂ := fun z ↦
    if posPhaseBitMod4 true pos24TailSign pos24TailMag30 (coreBetaOf false p80 z) then (-1 : ℂ) else
      1
  have hFac : sysBlock80Mod4Of pos24TailMag30 tierBQftFull c false p80 =
      Wᴴ * Matrix.diagonal f * W := by
    have hTwEq : (castUnitaryPow2 pos24_core80_eq_twist80.symm
        (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 c)).1 =
        (Pos24Slot2FermionicBridge.slot2UTwistParam true pos24_22_le_80 c).1 := rfl
    have hW_eq : wSlice80 c false p80 = W := by
      rw [wSlice80_factor c false p80, hTwEq,
          sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl false p80,
          sysBlockAtPayloadGen_uTwist_slot2_eq c p80, hl, hanc, hb₁]
    rw [sysBlock80Mod4Of_eq_wSlice80_conj, hW_eq]
  have hX := slot2OuterFactor_eq offsetSysUnitary_eq_fwdPerm c l anc b₁
      (qft64OffsetUnitary3D_mul_offset18Unitary b₁) list_ofFn_rEl_prod_mul
      list_ofFn_rEl_outPhase_eq_diagonal
  unfold blkSmSlot2Mod4
  rw [smConj_eq_sm654Conj_of_comm_rProj24 (sysBlock80Mod4Of_slot2_comm_rProj24 pos24TailMag30 c
    p80),
      hFac, sa_conj_conj_eq smToTwos654SysUnitary_sa W (Matrix.diagonal f)]
  exact conj_phase_diag_outer (slot2GlobalPhase c l) (star_slot2GlobalPhase_mul_self c l)
    (fun z ↦ ∏ e : Fin 218, karatsubaOutPhase3D (slotCoordSys z e)) f
    star_prod_karatsubaOutPhase3D_mul_self (veeSysProdUnitary b₁).1 (sysNucDiag48 c l).1
    (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1
    (W * smToTwos654SysUnitary.1) hX

end HpowStep_20
theorem blkSmSlot2Mod4_head_eq (c : Configuration) (l : Fin 216) (k : Fin 56) (pid : Fin 6)
    (sm : Fin 8) (dH : NyqFine3D128) (hdH : dH = pos24OhPoint (pos24HeadU56 k) (pos24HeadV56
    k) (pos24HeadW56 k) pid sm) (th rj : Bool) : blkSmSlot2Mod4 c
    (headWitnessPayload80 0 l.val 0 k pid sm th rj) = (sysNucDiag48 c l).1 *
    ((veeSysProdUnitary (nyq128Equiv3D.symm dH).2).1ᴴ * Matrix.diagonal (fun z : Fin (2 ^
    systemQubits) ↦ if slot2HeadMod4Bit (nyq128Equiv3D.symm dH).1 th z then (-1 : ℂ) else 1) *
    (veeSysProdUnitary (nyq128Equiv3D.symm dH).2).1) * (sysNucDiag48 c l).1ᴴ := by
  rcases headWitnessPayload80_slot2_meta l k pid sm th rj with ⟨hl, hanc, hb₁⟩
  have hb₁_dH : payloadB1Parity (headWitnessPayload80 0 l.val 0 k pid sm th rj) =
      (nyq128Equiv3D.symm dH).2 :=
    hb₁.trans (congrArg (fun x ↦ (nyq128Equiv3D.symm x).2) hdH.symm)
  rw [blkSmSlot2Mod4_eq_cleanConj c _ l 0 (nyq128Equiv3D.symm dH).2 hl hanc hb₁_dH]
  exact conj_eq_one_diag_eq permutationUnitary_permElectron_swap_zero (fun z ↦ congrArg (fun b
    : Bool ↦ if b then (-1 : ℂ) else 1) ((posPhaseBitMod4_headWitness_slot2 l k pid sm th rj
    z).trans (congrArg (fun x ↦ slot2HeadMod4Bit (nyq128Equiv3D.symm x).1 th z) hdH.symm)))

theorem tierBB2RawIdMod4_mul_fermionicProjector_eq_bModSlot2 (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) : ((pos80Slot2Scale : ℂ) • (smToTwosSysUnitary.1 *
    tierBB2RawIdMod4 c * smToTwosSysUnitary.1)) * fermionicProjector spinUp = bModSlot248 c *
    fermionicProjector spinUp := by
  have hSum : (pos80Slot2Scale : ℂ) •
      (smToTwosSysUnitary.1 * tierBB2RawIdMod4 c * smToTwosSysUnitary.1) = ∑ p80 :
      BitAssignment 80, ((pos80Slot2Scale * pos80IdealDist false p80 : ℝ) : ℂ) •
      blkSmSlot2Mod4 c p80 := by
    unfold tierBB2RawIdMod4 tierBB2RawIdMod4Of coherentSysOp80Mod4Of blkSmSlot2Mod4
    exact smul_conj_sum_real_smul pos80Slot2Scale smToTwosSysUnitary.1 (pos80IdealDist false)
      (fun p80 ↦ sysBlock80Mod4Of pos24TailMag30 tierBQftFull c false p80)
  rw [hSum]
  refine slot2_witnessSum_mul_fermionicProjector_eq c spinUp (blkSmSlot2Mod4 c)
    (fun l k pid sm ↦ ?_) (fun l anc dp ↦ ?_)
  · let dH := pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm
    exact sum_bool_bool_mul_eq_four_smul_of_half (fun th rj ↦ blkSmSlot2Mod4 c
      (headWitnessPayload80 0 l.val 0 k pid sm th rj)) (sysNucDiag48 c l).1
      (veeSysProdUnitary (nyq128Equiv3D.symm dH).2).1 (fun th ↦ Matrix.diagonal (fun z : Fin
      (2 ^ systemQubits) ↦ if slot2HeadMod4Bit (nyq128Equiv3D.symm dH).1 th z then (-1 : ℂ)
      else 1)) (fermionicProjector spinUp) ((1 - nTot_sp (uenSubGridKet48 c l
      (nyq128Equiv3D.symm dH).2 (nyq128Equiv3D.symm dH).1)) * fermionicProjector spinUp)
      (blkSmSlot2Mod4_head_eq c l k pid sm dH rfl) (slot2_headMod4_conj_mul_fermionicProjector
      c l (nyq128Equiv3D.symm dH).2 (nyq128Equiv3D.symm dH).1 spinUp)
  · have hTailEq : ∀ (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool),
        blkSmSlot2Mod4 c (tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj) =
          blkSmSlot2 tierBQftFull c (tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj) := by
      intro keep th rj
      have hp30 : tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj 30 = 0 := rfl
      unfold blkSmSlot2Mod4 blkSmSlot2
      rw [sysBlock80Mod4Of_eq_sysBlock80Of_of_p80_30_zero pos24TailMag30 c false _ hp30]
      rfl
    simp_rw [hTailEq]
    exact slot2_tail_keep_th_rj_sum_eq_of_slices tierBQftFull c l anc dp
      (blkSmSlot2_tail_eq tierBQftFull rfl c l anc dp) (slot2Tail_mag_le_span dp) (fun y ↦
      veeSysProdUnitary_conj_slotProj (nyqParity3DEquivFin8.symm dp) 0 y) (fun y ↦
      sysNucDiag48_conj_op_veeSubGridKet c l (nyqParity3DEquivFin8.symm dp) y 0)

theorem tierBB2RawIdMod4_mul_fermionicProjector_eq (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) : (pos80Slot2Scale : ℂ) • ((smToTwosSysUnitary.1 *
    tierBB2RawIdMod4 c * smToTwosSysUnitary.1) * fermionicProjector spinUp) =
    (pos80Slot2Scale : ℂ) • ((smToTwosSysUnitary.1 * tierBB2RawId c * smToTwosSysUnitary.1) *
    fermionicProjector spinUp) := by
  have h1 := tierBB2RawIdMod4_mul_fermionicProjector_eq_bModSlot2 c spinUp
  have h2 := tierBB2RawId_mul_fermionicProjector_eq c spinUp
  have hEq : ((pos80Slot2Scale : ℂ) • (smToTwosSysUnitary.1 * tierBB2RawIdMod4 c *
      smToTwosSysUnitary.1)) * fermionicProjector spinUp = ((pos80Slot2Scale : ℂ) •
      (smToTwosSysUnitary.1 * tierBB2RawId c * smToTwosSysUnitary.1)) * fermionicProjector
      spinUp := h1.trans h2.symm
  rw [Matrix.smul_mul, Matrix.smul_mul] at hEq
  exact hEq

theorem tierBB2RawIdMod4_smConj_mul_fermionicProjector_eq (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    (smToTwosSysUnitary.1 * tierBB2RawIdMod4 c * smToTwosSysUnitary.1) * fermionicProjector
    spinUp = (smToTwosSysUnitary.1 * tierBB2RawId c * smToTwosSysUnitary.1) *
    fermionicProjector spinUp := by
  have hScaleNe : (pos80Slot2Scale : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt pos80Slot2Scale_pos)
  exact smul_right_injective _ hScaleNe (tierBB2RawIdMod4_mul_fermionicProjector_eq c spinUp)

theorem tierBB2IdMod4_mul_fermionicProjector_eq (cfg : Configuration)
    (spinUp : Finset (Fin numElectrons)) : ((mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _
    ↦ pos80Slot2Scale) cfg : ℂ) • (smToTwosSysUnitary.1 * tierBB2IdMod4 cfg *
    smToTwosSysUnitary.1)) * fermionicProjector spinUp = ((mergedPosSlot2WeightGen ((108 : ℝ)
    / 109) (fun _ ↦ pos80Slot2Scale) cfg : ℂ) • (smToTwosSysUnitary.1 * tierBB2Id cfg *
    smToTwosSysUnitary.1)) * fermionicProjector spinUp := by
  let w2 := mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg
  let A_mod4 : Configuration → Operator (2 ^ systemQubits) := fun c' ↦
    (pos80Slot2Scale : ℂ) • (smToTwosSysUnitary.1 * tierBB2RawIdMod4 c' * smToTwosSysUnitary.1)
  let A_orig : Configuration → Operator (2 ^ systemQubits) := fun c' ↦
    (pos80Slot2Scale : ℂ) • (smToTwosSysUnitary.1 * tierBB2RawId c' * smToTwosSysUnitary.1)
  have hIdleMod4 : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ 24)),
      A_mod4 (PosSlots24MergedVepBound.cfgProjZ512 zP) * rProj24_sp.embedMatrix M =
        rProj24_sp.embedMatrix M * A_mod4 (PosSlots24MergedVepBound.cfgProjZ512 zP) := fun zP M ↦ by
    dsimp only [A_mod4]
    rw [Matrix.smul_mul, Matrix.mul_smul,
      smConj_comm_embedMatrix_of_idleTwos (tierBB2RawIdMod4_comm_rProj24 _) M]
  have hIdleOrig : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ 24)),
      A_orig (PosSlots24MergedVepBound.cfgProjZ512 zP) * rProj24_sp.embedMatrix M =
        rProj24_sp.embedMatrix M * A_orig (PosSlots24MergedVepBound.cfgProjZ512 zP) := fun zP M ↦ by
    dsimp only [A_orig]
    rw [Matrix.smul_mul, Matrix.mul_smul,
      smConj_comm_embedMatrix_of_idleTwos (tierBB2RawId_comm_rProj24 _) M]
  have hVepEq : vepFromSlot2Op A_mod4 * fermionicProjector spinUp = vepFromSlot2Op A_orig *
      fermionicProjector spinUp :=
    vepFromSlot2Op_mul_fermionicProjector_eq spinUp hIdleMod4 hIdleOrig fun zP ↦ by
      dsimp only [A_mod4, A_orig]
      rw [Matrix.smul_mul, Matrix.smul_mul,
          tierBB2RawIdMod4_smConj_mul_fermionicProjector_eq _ spinUp]
  have hSplitMod4 :
      (w2 : ℂ) • (smToTwosSysUnitary.1 * tierBB2IdMod4 cfg * smToTwosSysUnitary.1) =
        A_mod4 cfg + vepFromSlot2Op A_mod4 := by
    dsimp only [w2, A_mod4]
    unfold tierBB2IdMod4 tierBB2IdMod4Of tierBB2RawIdMod4
    exact mergedPosSlot2Gen_smConj_eq (by norm_num : (0 : ℝ) < 108 / 109) pos80Slot2Scale
      (tierBB2RawIdMod4Of pos24TailMag30)
      (fun zP M ↦ tierBB2RawIdMod4Of_comm_rProj24 pos24TailMag30
        (PosSlots24MergedVepBound.cfgProjZ512 zP) M) cfg
  have hSplitOrig : (w2 : ℂ) • (smToTwosSysUnitary.1 * tierBB2Id cfg * smToTwosSysUnitary.1) =
      A_orig cfg + vepFromSlot2Op A_orig :=
    mergedPosSlot2Gen_smConj_eq (by norm_num : (0 : ℝ) < 108 / 109) pos80Slot2Scale
      tierBB2RawId
      (fun zP M ↦ tierBB2RawId_comm_rProj24 (PosSlots24MergedVepBound.cfgProjZ512 zP) M) cfg
  change ((w2 : ℂ) • (smToTwosSysUnitary.1 * tierBB2IdMod4 cfg * smToTwosSysUnitary.1)) *
    fermionicProjector spinUp = ((w2 : ℂ) • (smToTwosSysUnitary.1 * tierBB2Id cfg *
    smToTwosSysUnitary.1)) * fermionicProjector spinUp
  rw [hSplitMod4, hSplitOrig, Matrix.add_mul, Matrix.add_mul, hVepEq]
  dsimp only [A_mod4, A_orig]
  rw [Matrix.smul_mul, Matrix.smul_mul,
    tierBB2RawIdMod4_smConj_mul_fermionicProjector_eq cfg spinUp]

theorem tierBB2IdMod4_smConj_mul_fermionicProjector_eq (cfg : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    (smToTwosSysUnitary.1 * tierBB2IdMod4 cfg * smToTwosSysUnitary.1) * fermionicProjector
    spinUp = (smToTwosSysUnitary.1 * tierBB2Id cfg * smToTwosSysUnitary.1) *
    fermionicProjector spinUp := by
  let w2 := mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg
  have hw2_pos : 0 < w2 := by
    unfold w2 mergedPosSlot2WeightGen
    have := pos80Slot2Scale_pos
    positivity
  have hw2_ne : (w2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hw2_pos)
  have hScaled : ((w2 : ℂ) • (smToTwosSysUnitary.1 * tierBB2IdMod4 cfg *
      smToTwosSysUnitary.1)) * fermionicProjector spinUp = ((w2 : ℂ) • (smToTwosSysUnitary.1 *
      tierBB2Id cfg * smToTwosSysUnitary.1)) * fermionicProjector spinUp :=
      tierBB2IdMod4_mul_fermionicProjector_eq cfg spinUp
  rw [Matrix.smul_mul, Matrix.smul_mul] at hScaled
  exact smul_right_injective _ hw2_ne hScaled

private theorem agreesOnFermionicSector_gridSandwich_smConj (w : ℝ)
    (A B C : Operator (2 ^ systemQubits)) {eps : ℝ} (spinUp : Finset (Fin numElectrons))
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hEq : (smToTwosSysUnitary.1 * A * smToTwosSysUnitary.1) * fermionicProjector spinUp =
      (smToTwosSysUnitary.1 * B * smToTwosSysUnitary.1) * fermionicProjector spinUp)
    (hB_ag : AgreesOnFermionicSector spinUp
      (gridProjector * ((w : ℂ) • (smToTwosSysUnitary.1 * B * smToTwosSysUnitary.1)) *
        gridProjector) C eps) :
    AgreesOnFermionicSector spinUp
      (gridProjector * ((w : ℂ) • (smToTwosSysUnitary.1 * A * smToTwosSysUnitary.1)) *
        gridProjector) C eps := by
  have hHerm : ∀ X : Operator (2 ^ systemQubits), X.IsHermitian →
      (gridProjector * ((w : ℂ) • (smToTwosSysUnitary.1 * X * smToTwosSysUnitary.1)) *
        gridProjector).IsHermitian := fun X hX ↦ by
    refine isHermitian_gridSandwich_slot2 (isHermitian_real_smul_slot2 w ?_)
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      smToTwosSysUnitary_sa, hX.eq, Matrix.mul_assoc]
  have hMulEq :
      (gridProjector * ((w : ℂ) • (smToTwosSysUnitary.1 * A * smToTwosSysUnitary.1)) *
          gridProjector) * fermionicProjector spinUp =
        (gridProjector * ((w : ℂ) • (smToTwosSysUnitary.1 * B * smToTwosSysUnitary.1)) *
          gridProjector) * fermionicProjector spinUp := by
    simp only [Matrix.mul_assoc, Matrix.smul_mul, gridProjector_mul_fermionicProjector spinUp]
    simpa only [Matrix.mul_assoc] using congrArg (fun M ↦ gridProjector * (w : ℂ) • M) hEq
  exact agreesOnFermionicSector_of_isHermitian_and_mul_eq (hHerm A hA) (hHerm B hB) hMulEq hB_ag

theorem tierBB4IdMod4_trunc_agreesOnFermionicSector_q30Tight
    (truncCfg : Configuration → Configuration)
    (c : Configuration) (spinUp0 : Finset (Fin numElectrons)) :
    let E4only : Fin 6 → ℝ := fun q ↦ if q = 4 then pos80Slot4EShiftFn c else 0
    AgreesOnFermionicSector spinUp0
      (gridProjector *
        ((pos80Slot4Scale : ℂ) •
          (smToTwosSysUnitary.1 * tierBB4IdMod4 (truncCfg c) * smToTwosSysUnitary.1)) *
        gridProjector)
      (sixChannelShifted c E4only 4)
      eps4_q30_tight := by
  intro E4only
  have hShiftEq : sixChannelShifted c E4only 4 = sixChannelShifted (truncCfg c) (fun q : Fin 6
      ↦ if q = 4 then pos80Slot4EShiftFn (truncCfg c) else 0) 4 := by
    unfold sixChannelShifted
    rw [← Slot2Slot4QuantizedChannelBridge.vEeManyBody_eq_sixChannelRaw c,
        ← Slot2Slot4QuantizedChannelBridge.vEeManyBody_eq_sixChannelRaw (truncCfg c)]
    rfl
  rw [hShiftEq]
  exact agreesOnFermionicSector_gridSandwich_smConj pos80Slot4Scale
    (tierBB4IdMod4 (truncCfg c)) (tierBB4Id (truncCfg c)) _ spinUp0
    (tierBB4IdMod4_isHermitian (truncCfg c)) (tierBB4Id_isHermitian (truncCfg c))
    (tierBB4IdMod4_mul_fermionicProjector_eq (truncCfg c) spinUp0)
    (PosSlots24Q30Tight.tierBB4Id_agreesOnFermionicSector_q30Tight (truncCfg c) spinUp0)

theorem tierBB2IdMod4_trunc_intrinsic_agrees_tight
    (truncCfg : Configuration → Configuration)
    (htruncProj : ∀ zP : NyqFine3D512,
      truncCfg (PosSlots24MergedVepBound.cfgProjZ512 zP) =
        PosSlots24MergedVepBound.cfgProjZ512 zP)
    (hsecEq : ∀ c : Configuration,
      mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) c =
        mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) (truncCfg c))
    {epsRaw eps2 : ℝ}
    (hErrRaw : ∀ (c : Configuration) (spinUp0 : Finset (Fin numElectrons)),
      let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
      ‖fermionicProjector spinUp0 *
          (Pos24Slot2FermionicBridge.bModSlot248 (truncCfg c) - sixChannelShifted c E2only 2) *
        fermionicProjector spinUp0‖ ≤ epsRaw)
    (heps_comb : epsRaw + (1 / 108 : ℝ) * ((257 : ℝ) / 10000000) ≤ (109 / 108 : ℝ) * eps2)
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
    (E_sp : Fin 6 → ℝ)
    (hEsp2 : E_sp 2 = pos24Slot2E2Const)
    (hEsp5 : E_sp 5 = pos24Slot2E2Const / 108) :
    AgreesOnFermionicSector spinUp
      (gridProjector *
        ((mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg : ℂ) •
          (smToTwosSysUnitary.1 * tierBB2IdMod4 (truncCfg cfg) * smToTwosSysUnitary.1)) *
        gridProjector)
      (sixChannelShifted cfg E_sp 2 + sixChannelShifted cfg E_sp 5)
      ((109 / 108 : ℝ) * eps2) :=
  agreesOnFermionicSector_gridSandwich_smConj
    (mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg)
    (tierBB2IdMod4 (truncCfg cfg)) (tierBB2Id (truncCfg cfg)) _ spinUp
    (tierBB2IdMod4_isHermitian (truncCfg cfg)) (tierBB2Id_isHermitian (truncCfg cfg))
    (tierBB2IdMod4_smConj_mul_fermionicProjector_eq (truncCfg cfg) spinUp)
    (PosSlots24Q30Tight.tierBB2Id_trunc_intrinsic_agrees_tight
      truncCfg htruncProj hsecEq hErrRaw heps_comb cfg spinUp E_sp hEsp2 hEsp5)


end ConfigPosMod4FermionicBounds
end PosMod4FermionicBounds
end
end PosMod4FermionicBounds

section TopClosure
local instance (priority := 1000000) instNeZeroTwoPow_TopClosure (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace TopClosure

section ConfigTopClosure
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

open Real Operator Matrix Circuit SpecsAux.SpecMirror
open InterWalkRSum42Hoist (PreservesFeature)
open scoped Matrix Matrix.Norms.L2Operator BigOperators

/- ## Section 1: Schedule (`Q = 4,265`, `mWork = 137`, `M = 136,021`) & Cost/Error Caps -/

section Part2PrepAndStage2

-- Root solution namespace already active.
open PosPostPrep80MergedVepS3
open PosPostPrep80CertS3
open ZeroAncillaUSP hiding ket


end Part2PrepAndStage2

/- ## Section 3: Stream Init & Parametric Top-Level Closure (`Q = 4,265`) -/

end ConfigTopClosure
end TopClosure
end
end TopClosure

section SelStitchHelper
local instance (priority := 1000000) instNeZeroTwoPow_SelStitchHelper (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-!
# Hoisted `SELECT` Stitch Helper (`SelStitchHelper`)

Packages `SingleCatSelectImpl` (`mkSingleCatSelectImplOfTrunc`),
`HoistedExtHkSelectSpec` (`mkHoistedExtHkSelectSpecT4OfTrunc`) with `rfl`
`.dSelectCtrl` and `.dSelectCat` alignment against `mkExtHkSelectCircuitSpecT4`,
concrete `pCoinSlack010` factor dischargers (`uPass1Cat`, `slot1HadCutLeafSpec`,
`uSlot3HadCutCat36FullSys`, `uPass3Cat`, and Twist coin-3 commutation), and a
`PerHorizonSelAndPertSpec` constructor wiring `prepTableC99` and
`coreQftHadamardPrunedBundle128`.
-/

namespace SelStitchHelper

section ConfigSelStitchHelper
set_option maxRecDepth 65536
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open PosMomSelectSandwich (slotBitProj slotBitProj_conjTranspose)
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge (fullSysCoreWires iSlot0 iSlot1)
open FullSysCatSegmentBridge (iSlot2)
open Barrel3PassSelectStitch (rCTSeg rCoreSeg rCoreInCT80)
open Leaf4Ext48TopStitch (CommutesWithReg)
open SelectHoistLemmas hiding rCoreTopCatInCT
open SelectStitch
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128
   coreQftHadamardPrunedBundle128_uQft654)

/- ## Section 1: Generic Projector Absorption & Coin-`010` Factor Dischargers -/

theorem mul_slotBitProj_id_of_entry {N : ℕ} (U : Operator (2 ^ N)) (w : Wire N) (b : Fin 2)
    (hU : ∀ i j : Fin (2 ^ N), (basisBits N j w).val = b.val → U i j = (1 : Operator (2 ^ N))
    i j) : U * slotBitProj w b = slotBitProj w b := by
  ext i j
  rw [slotBitProj, Matrix.mul_diagonal]
  by_cases hb : (basisBits N j w).val = b.val
  · rw [ite_eq_left hb, mul_one, hU i j hb, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [hb]
    · simp [hij]
  · rw [ite_eq_right hb, mul_zero, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [hb]
    · simp [hij]

theorem unitaryConj_mul_proj_id {D : ℕ} (B M : Unitary D) (P : Operator D) (hP : Pᴴ = P)
    (hB : B.1 * P = P * B.1) (hM : M.1 * P = P) : (unitaryConj B M).1 * P = P := by
  have hBi : (B⁻¹).1 * P = P * (B⁻¹).1 := unitary_inv_comm_selfAdj hP hB
  calc (unitaryConj B M).1 * P
      = (B⁻¹).1 * (M.1 * (B.1 * P)) := by
          change (((B⁻¹).1 * M.1) * B.1) * P = _
          simp only [Matrix.mul_assoc]
    _ = (B⁻¹).1 * (M.1 * (P * B.1)) := by rw [hB]
    _ = (B⁻¹).1 * ((M.1 * P) * B.1) := by rw [Matrix.mul_assoc M.1 P B.1]
    _ = (B⁻¹).1 * (P * B.1) := by rw [hM]
    _ = ((B⁻¹).1 * P) * B.1 := by rw [Matrix.mul_assoc]
    _ = (P * (B⁻¹).1) * B.1 := by rw [hBi]
    _ = P * ((B⁻¹).1 * B.1) := by rw [Matrix.mul_assoc]
    _ = P := by
          have hInv : (B⁻¹).1 * B.1 = 1 := congrArg Subtype.val (inv_mul_cancel B)
          rw [hInv, Matrix.mul_one]

theorem embedMatrix_pCoinSlack010Core {n : ℕ} (r : QRegister (fullSysCoreWires 80) n) :
    r.embedMatrix pCoinSlack010Core = slotBitProj (r (iSlot2 80)) 0 * slotBitProj
    (r (iSlot1 80)) 1 * slotBitProj (r (iSlot0 80)) 0 := by
  unfold pCoinSlack010Core
  rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul,
    embedMatrix_slotBitProj, embedMatrix_slotBitProj, embedMatrix_slotBitProj]

theorem comm_pCoinSlack010Core_of_comm_coin3 {U : Unitary (2 ^ (fullSysCoreWires 80))} (h2 :
    U.1 * slotBitProj (iSlot2 80) 0 = slotBitProj (iSlot2 80) 0 * U.1) (h1 : U.1 * slotBitProj
    (iSlot1 80) 1 = slotBitProj (iSlot1 80) 1 * U.1) (h0 : U.1 * slotBitProj (iSlot0 80) 0 =
    slotBitProj (iSlot0 80) 0 * U.1) : U.1 * pCoinSlack010Core = pCoinSlack010Core * U.1 := by
  unfold pCoinSlack010Core
  calc U.1 * (slotBitProj (iSlot2 80) 0 * slotBitProj (iSlot1 80) 1 * slotBitProj (iSlot0 80) 0)
      = ((U.1 * slotBitProj (iSlot2 80) 0) * slotBitProj (iSlot1 80) 1) *
          slotBitProj (iSlot0 80) 0 := by simp only [Matrix.mul_assoc]
    _ = (slotBitProj (iSlot2 80) 0 * (U.1 * slotBitProj (iSlot1 80) 1)) *
          slotBitProj (iSlot0 80) 0 := by rw [h2]; simp only [Matrix.mul_assoc]
    _ = (slotBitProj (iSlot2 80) 0 * slotBitProj (iSlot1 80) 1) *
          (U.1 * slotBitProj (iSlot0 80) 0) := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = pCoinSlack010Core * U.1 := by
          unfold pCoinSlack010Core; rw [h0]; simp only [Matrix.mul_assoc]

theorem rCTSeg_compose_rCoreInCT80 : rCTSeg.compose rCoreInCT80 = rCoreSeg := by
  apply InterWalkRSum42Hoist.qreg_ext; intro i
  have hc : rCoreInCT80 i = Fin.castAdd 48 i := by ext; simp [rCoreInCT80]
  change rCTSeg (rCoreInCT80 i) = rCoreSeg i
  rw [hc, rCTSeg, QRegister.concat_apply_left]

theorem permutationUnitary_mul_slotBitProj_id {N : ℕ}
    (σ : Equiv.Perm (Fin (2 ^ N))) (w : Wire N) (b : Fin 2)
    (hFix : ∀ j : Fin (2 ^ N), (basisBits N j w).val = b.val → σ j = j) :
    (Operator.permutationUnitary σ).1 * slotBitProj w b = slotBitProj w b := by
  refine mul_slotBitProj_id_of_entry _ w b fun i j hj ↦ ?_
  have hcol : (Operator.permutationUnitary σ).1 i j =
      ((Operator.permutationUnitary σ).1.mulVec (Pi.single j (1 : ℂ))) i := by
    simp [Matrix.mulVec]
  rw [hcol, Operator.permutationUnitary_mulVec_single, hFix j hj]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem dyadicDiagUnitary_mul_slotBitProj_id {N : ℕ} (B : ℕ) (e : BitAssignment N → ℤ)
    (w : Wire N) (b : Fin 2) (hZero : ∀ j : Fin (2 ^ N), (basisBits N j w).val = b.val → e
    (basisBits N j) = 0) : (DyadicQft64.dyadicDiagUnitary N B e).1 * slotBitProj w b =
    slotBitProj w b := by
  refine mul_slotBitProj_id_of_entry _ w b fun i j hj ↦ ?_
  change Matrix.diagonal (fun x : Fin (2 ^ N) ↦ DyadicQft64.dyadicTurn B (e (basisBits N x)))
    i j = (1 : Operator (2 ^ N)) i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, hZero i hj]
    unfold DyadicQft64.dyadicTurn
    simp
  · simp [hij]

theorem slot4Sgn_eq_zero_of_slot1_one (isInv : Bool) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires 80)) (h1 : (γ (iSlot1 80)).val = 1) :
    JunctionApexCSA288.slot4Sgn isInv (by decide : 22 ≤ 80) w γ = 0 := by
  unfold JunctionApexCSA288.slot4Sgn
  have hw1 : NuclearTwistAndXor654Concrete.wSlot1
      (QRegExt.idReg
        (fullSysCoreWires 80)) = iSlot1 80 := rfl
  rw [hw1]
  have hne : γ (iSlot1 80) ≠ 0 := fun h0 ↦ by rw [h0] at h1; simp at h1
  simp [hne]

theorem uSlot4AxisCatT4_mul_slot1_one (isInv : Bool) (w : Fin 3) :
    (Leaf1Pass1And3Width204.uSlot4AxisCatT4 isInv
    (by decide : 22 ≤ 80) w).1 * slotBitProj (Fin.castAdd 4 (iSlot1 80)) 1 = slotBitProj
    (Fin.castAdd 4 (iSlot1 80)) 1 := by
  unfold Leaf1Pass1And3Width204.uSlot4AxisCatT4
  have hrC : Leaf1Pass1And3Width204.rCoreBlock4 80 (iSlot1 80) =
      Fin.castAdd 4 (iSlot1 80) := by
    ext; rfl
  have hTopCore : (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48
      (JunctionApexCSA288.slot4TopExp isInv (by decide : 22 ≤ 80)
      w)).1 * slotBitProj (iSlot1 80) 1 = slotBitProj (iSlot1 80) 1 := by
    refine dyadicDiagUnitary_mul_slotBitProj_id 48 _ (iSlot1 80) 1 fun j hj ↦ ?_
    unfold JunctionApexCSA288.slot4TopExp
    rw [slot4Sgn_eq_zero_of_slot1_one isInv w _ hj]
    ring
  have hTop : ((Leaf1Pass1And3Width204.rCoreBlock4
      80).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48
      (JunctionApexCSA288.slot4TopExp isInv (by decide : 22 ≤ 80)
      w))).1 * slotBitProj (Fin.castAdd 4 (iSlot1 80)) 1 = slotBitProj
      (Fin.castAdd 4 (iSlot1 80)) 1 := by
    rw [← hrC, ← embedMatrix_slotBitProj, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
      hTopCore]
  have hCarry : (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80 + 4) 3
      (Leaf1Pass1And3Width204.t4CarryExp (fullSysCoreWires 80)
      (JunctionApexCSA288.slot4LowShift isInv (by decide : 22 ≤ 80)
      w))).1 * slotBitProj (Fin.castAdd 4 (iSlot1 80)) 1 = slotBitProj
      (Fin.castAdd 4 (iSlot1 80)) 1 := by
    refine dyadicDiagUnitary_mul_slotBitProj_id 3 _ (Fin.castAdd 4 (iSlot1 80)) 1 fun j hj ↦ ?_
    unfold Leaf1Pass1And3Width204.t4CarryExp
    have hLow : JunctionApexCSA288.slot4LowShift
        isInv (by decide : 22 ≤ 80) w
        (fun i ↦ basisBits (fullSysCoreWires 80 + 4) j (Fin.castAdd 4 i)) = 0 := by
      unfold JunctionApexCSA288.slot4LowShift
      rw [slot4Sgn_eq_zero_of_slot1_one isInv w _ hj, zero_mul]
    rw [hLow, add_zero]
    have hbv := Leaf1Pass1And3Width204.bitsVal_fin4_lt (fun k :
        Fin 4 ↦ basisBits (fullSysCoreWires 80 + 4) j (Fin.natAdd (fullSysCoreWires 80) k))
    omega
  have hPerm : (Operator.permutationUnitary
      (Leaf1Pass1And3Width204.t4WinPerm (fullSysCoreWires 80)
      (JunctionApexCSA288.slot4LowShift isInv (by decide : 22 ≤ 80)
      w))).1 * slotBitProj (Fin.castAdd 4 (iSlot1 80)) 1 = slotBitProj
      (Fin.castAdd 4 (iSlot1 80)) 1 := by
    refine permutationUnitary_mul_slotBitProj_id _ (Fin.castAdd 4 (iSlot1 80)) 1 fun j hj ↦ ?_
    let p := DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 j
    have hjEq : j = (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4).symm (p.1, p.2)
        := by
      dsimp only [p]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
    have hp1 : (p.1 (iSlot1 80)).val = 1 := by
      have hbb := JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd
        (kSys := fullSysCoreWires 80) (B := 4) p.1 p.2 (iSlot1 80)
      rw [← hjEq] at hbb
      exact (congrArg ZMod.val hbb.symm).trans hj
    have hLow0 : JunctionApexCSA288.slot4LowShift
        isInv (by decide : 22 ≤ 80) w p.1 = 0 := by
      unfold JunctionApexCSA288.slot4LowShift
      rw [slot4Sgn_eq_zero_of_slot1_one isInv w p.1 hp1, zero_mul]
    conv_lhs => rw [hjEq]
    rw [Leaf1Pass1And3Width204.t4WinPerm_symm_apply,
      hLow0, Leaf1Pass1And3Width204.stepT4Fin_zero, ← hjEq]
  unfold Leaf1Pass1And3Width204.uApexShift4
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc, hTop, Matrix.mul_assoc, hCarry, hPerm]

theorem uSlot4ApexCatT4_mul_slot1_one :
    (Leaf1Pass1And3Width204.uSlot4ApexCatT4
    (by decide : 22 ≤ 80)).1 * slotBitProj (Fin.castAdd 4 (iSlot1 80)) 1 = slotBitProj
    (Fin.castAdd 4 (iSlot1 80)) 1 := by
  unfold Leaf1Pass1And3Width204.uSlot4ApexCatT4
  rw[Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      uSlot4AxisCatT4_mul_slot1_one false 0, uSlot4AxisCatT4_mul_slot1_one false 1,
      uSlot4AxisCatT4_mul_slot1_one false 2]

theorem uSlot4ApexCatT4_inv_mul_slot1_one :
    ((Leaf1Pass1And3Width204.uSlot4ApexCatT4
    (by decide : 22 ≤ 80))⁻¹).1 * slotBitProj (Fin.castAdd 4 (iSlot1 80)) 1 = slotBitProj
    (Fin.castAdd 4 (iSlot1 80)) 1 := by
  unfold Leaf1Pass1And3Width204.uSlot4ApexCatT4
  rw[_root_.mul_inv_rev, _root_.mul_inv_rev,
      Leaf1Pass1And3Width204.uSlot4AxisCatT4_inv_eq,
      Leaf1Pass1And3Width204.uSlot4AxisCatT4_inv_eq,
      Leaf1Pass1And3Width204.uSlot4AxisCatT4_inv_eq,
      Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc,
      uSlot4AxisCatT4_mul_slot1_one true 2, Matrix.mul_assoc,
      uSlot4AxisCatT4_mul_slot1_one true 1, uSlot4AxisCatT4_mul_slot1_one true 0]

theorem pCoinSlack010CT4_eq_slot1_mul :
    (Leaf1Pass1And3Width204.rCoreBlock4 80).embedMatrix
    pCoinSlack010Core = slotBitProj (Fin.castAdd 4 (iSlot1 80)) 1 * (slotBitProj (Fin.castAdd
    4 (iSlot2 80)) 0 * slotBitProj (Fin.castAdd 4 (iSlot0 80)) 0) := by
  have hc0 : Leaf1Pass1And3Width204.rCoreBlock4 80 (iSlot0 80) =
      Fin.castAdd 4 (iSlot0 80) := by ext; rfl
  have hc1 : Leaf1Pass1And3Width204.rCoreBlock4 80 (iSlot1 80) =
      Fin.castAdd 4 (iSlot1 80) := by ext; rfl
  have hc2 : Leaf1Pass1And3Width204.rCoreBlock4 80 (iSlot2 80) =
      Fin.castAdd 4 (iSlot2 80) := by ext; rfl
  rw [embedMatrix_pCoinSlack010Core, hc0, hc1, hc2,
    Barrel3PassCommuteHelpers.slotBitProj_comm
      (Fin.castAdd 4 (iSlot2 80)) (Fin.castAdd 4 (iSlot1 80)),
    Matrix.mul_assoc]

theorem selCT4InCT_compose_rCoreBlock4 :
    (Leaf1Pass1And3Width204.selCT4InCT 80).compose
    (Leaf1Pass1And3Width204.rCoreBlock4 80) = rCoreInCT80 := by
  apply InterWalkRSum42Hoist.qreg_ext; intro i
  have hc : Leaf1Pass1And3Width204.rCoreBlock4 80 i =
      Fin.castAdd 4 i := by
    ext
    simp [Leaf1Pass1And3Width204.rCoreBlock4,
      QRegister.block, Fin.natAddEmb]
  change Leaf1Pass1And3Width204.selCT4InCT 80
    (Leaf1Pass1And3Width204.rCoreBlock4 80 i) = rCoreInCT80 i
  rw [hc]
  unfold Leaf1Pass1And3Width204.selCT4InCT
  rw [QRegister.concat_apply_left]

section HpowStep_21
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_21 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem uPass1Cat_mul_pCoinSlack010Seg :
    (rCTSeg.embedUnitary Pass1Leaf273.uPass1Cat).1 *
      pCoinSlack010Seg = pCoinSlack010Seg := by
  rw [← Leaf1Pass1And3Width204.embed_selCT4InCT_uPass1CatT4,
    ← QRegister.embedUnitary_compose]
  have hComp :
      (rCTSeg.compose (Leaf1Pass1And3Width204.selCT4InCT 80)).compose
        (Leaf1Pass1And3Width204.rCoreBlock4 80) = rCoreSeg := by
    rw [QRegister.compose_assoc, selCT4InCT_compose_rCoreBlock4, rCTSeg_compose_rCoreInCT80]
  unfold pCoinSlack010Seg
  rw [← hComp, QRegister.embedMatrix_compose, QRegister.embedUnitary_val,
    ← QRegister.embedMatrix_mul]
  apply congrArg (rCTSeg.compose
    (Leaf1Pass1And3Width204.selCT4InCT 80)).embedMatrix
  have hB : ((Leaf1Pass1And3Width204.rCoreBlock4
      80).embedUnitary (CoinDispatchedBarrel288.uBarrelFast (le_refl
      80))).1 * (Leaf1Pass1And3Width204.rCoreBlock4
      80).embedMatrix pCoinSlack010Core =
      (Leaf1Pass1And3Width204.rCoreBlock4 80).embedMatrix
      pCoinSlack010Core * ((Leaf1Pass1And3Width204.rCoreBlock4
      80).embedUnitary (CoinDispatchedBarrel288.uBarrelFast (le_refl
      80))).1 := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
    apply congrArg
      (Leaf1Pass1And3Width204.rCoreBlock4 80).embedMatrix
    exact comm_pCoinSlack010Core_of_comm_coin3
      (CoinDispatchedBarrel288.uBarrelFast_comm_high_wire
        (le_refl 80) (iSlot2 80) (by dsimp [iSlot2]; omega) 0)
      (CoinDispatchedBarrel288.uBarrelFast_comm_high_wire
        (le_refl 80) (iSlot1 80) (by dsimp [iSlot1]; omega) 1)
      (CoinDispatchedBarrel288.uBarrelFast_comm_high_wire
        (le_refl 80) (iSlot0 80) (by dsimp [iSlot0]; omega) 0)
  have hPsa : ((Leaf1Pass1And3Width204.rCoreBlock4
      80).embedMatrix pCoinSlack010Core)ᴴ =
      (Leaf1Pass1And3Width204.rCoreBlock4 80).embedMatrix
      pCoinSlack010Core := by
    rw [← QRegister.embedMatrix_conjTranspose, pCoinSlack010Core_conjTranspose]
  refine unitaryConj_mul_proj_id _ _ _ hPsa hB ?_
  unfold Leaf1Pass1And3Width204.uPass1InnerT4
  rw [Submonoid.coe_mul, Matrix.mul_assoc]
  have hS4 : (Leaf1Pass1And3Width204.uSlot4ApexCatT4
      (by decide : 22 ≤ 80)).1 *
      (Leaf1Pass1And3Width204.rCoreBlock4 80).embedMatrix
      pCoinSlack010Core = (Leaf1Pass1And3Width204.rCoreBlock4
      80).embedMatrix pCoinSlack010Core := by
    rw [pCoinSlack010CT4_eq_slot1_mul, ← Matrix.mul_assoc, uSlot4ApexCatT4_mul_slot1_one]
  rw [hS4, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul]
  apply congrArg
    (Leaf1Pass1And3Width204.rCoreBlock4 80).embedMatrix
  unfold pCoinSlack010Core
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Pass1Leaf273.uSlot0LocalXorBit5_mul_P0
      LiteralKineticAndMidpoint128.lambdaSlot0TeHi]

end HpowStep_21
theorem catModAddPerm_apply_of_shift_zero {kSys B : ℕ} (shift : BitAssignment kSys → ℕ)
    (j : Fin (2 ^ (kSys + B))) (h0 : shift (DyadicQft64.splitSysCatEquiv kSys B j).1 = 0) :
    DyadicQft64.catModAddPerm kSys B shift j = j := by
  let p := DyadicQft64.splitSysCatEquiv kSys B j
  have hj : j = (DyadicQft64.splitSysCatEquiv kSys B).symm (p.1, p.2) := by
    dsimp only [p]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
  have hMid : DyadicQft64.catModAddMidPerm kSys B shift (p.1, p.2) = (p.1, p.2) := by
    ext
    · rfl
    · change (p.2.val + shift p.1) % 2 ^ B = p.2.val
      rw [h0, add_zero, Nat.mod_eq_of_lt p.2.isLt]
  change (DyadicQft64.splitSysCatEquiv kSys B).symm
      (DyadicQft64.catModAddMidPerm kSys B shift p) = j
  rw [show p = (p.1, p.2) from (Prod.mk.eta).symm, hMid, ← hj]

theorem splitSysCatEquiv_fst_apply {kSys B : ℕ} (j : Fin (2 ^ (kSys + B))) (i : Fin kSys) :
    (DyadicQft64.splitSysCatEquiv kSys B j).1 i = basisBits (kSys + B) j (Fin.castAdd B i) := rfl

theorem slot3MomCoin_ne_six_of_bit26_zero_assign (α107 : BitAssignment 107)
    (h26 : (α107 ⟨26, by decide⟩).val = 0) :
    ((FullSysMomSlots0135Concrete.momCoinReg 80).extractIndex
      ((basisBitsEquiv
        (FullSysMomSlots0135Concrete.momCoreWires 80)).symm
        (StepBBlock0.embedAlpha107 α107))).val ≠ 6 := by
  intro h6
  let z80 := (basisBitsEquiv
    (FullSysMomSlots0135Concrete.momCoreWires 80)).symm
    (StepBBlock0.embedAlpha107 α107)
  have hcEq :
      (FullSysMomSlots0135Concrete.momCoinReg 80).extractIndex z80 =
        (⟨6, by decide⟩ : Fin 8) := Fin.ext h6
  have hb2 : (basisBits 3 ((FullSysMomSlots0135Concrete.momCoinReg
      80).extractIndex z80) 2).val = 1 := by
    rw [hcEq]; decide
  rw [QRegister.basisBits_extractIndex] at hb2
  have hbb : basisBits (FullSysMomSlots0135Concrete.momCoreWires
      80) z80 = StepBBlock0.embedAlpha107 α107 :=
      (basisBitsEquiv _).apply_symm_apply _
  have hwEq : FullSysMomSlots0135Concrete.momCoinReg 80 2 =
      StepBBlock0.sel107_80 ⟨26, by decide⟩ := Fin.ext rfl
  rw [congrFun hbb _, hwEq,
    StepBBlock0.embedAlpha107_sel107_80, h26] at hb2
  exact zero_ne_one hb2

theorem slot3MomCoin_ne_six_of_bit26_zero (j : Fin (2 ^ 107))
    (hj : (basisBits 107 j ⟨26, by decide⟩).val = 0) :
    ((FullSysMomSlots0135Concrete.momCoinReg 80).extractIndex
      ((basisBitsEquiv
        (FullSysMomSlots0135Concrete.momCoreWires 80)).symm
        (StepBBlock0.embedAlpha107 (basisBits 107 j)))).val ≠ 6 :=
  slot3MomCoin_ne_six_of_bit26_zero_assign (basisBits 107 j) hj

theorem s3AcceptNorm1s_eq_false_of_coin_ne6
    (t : Slot3Norm1s36_161w.Norm1sTier) (z : Fin (2 ^
    (FullSysMomSlots0135Concrete.momCoreWires 80))) (h :
    ((FullSysMomSlots0135Concrete.momCoinReg 80).extractIndex
    z).val ≠ 6) : Slot3Norm1s36Physics80.s3AcceptNorm1s t
    StepBBlock0.hmPay80 z = false := by
  unfold Slot3Norm1s36Physics80.s3AcceptNorm1s
  dsimp only
  rw [decide_eq_false h, Bool.false_and, Bool.false_and, Bool.false_and]

theorem s3Shift36Norm1s_eq_zero_of_accept_false
    (t : Slot3Norm1s36_161w.Norm1sTier) (cfg : Configuration)
    (α107 : BitAssignment 107)
    (h : Slot3Norm1s36Physics80.s3AcceptNorm1s t
      StepBBlock0.hmPay80
      ((basisBitsEquiv
        (FullSysMomSlots0135Concrete.momCoreWires 80)).symm
        (StepBBlock0.embedAlpha107 α107)) = false) :
    Leaf3Slot3Norm1sWidth204.s3Shift36Norm1s t cfg α107 = 0 := by
  have h42 : Slot3Norm1s36Physics80.s3Shift42Norm1s t cfg α107 = 0 :=
    (Slot3Norm1s36Physics80.s3Shift42Norm1s_eq_nuclearM36
      t cfg α107).trans (ite_eq_right (by rw [h]; decide))
  unfold Leaf3Slot3Norm1sWidth204.s3Shift36Norm1s
  rw [h42]

theorem s3CoreMapNorm1s_eq_self_of_accept_false
    (t : Slot3Norm1s36_161w.Norm1sTier)
    (z : Fin (2 ^ (FullSysMomSlots0135Concrete.momCoreWires 80)))
    (h : Slot3Norm1s36Physics80.s3AcceptNorm1s t
      StepBBlock0.hmPay80 z = false) :
    Slot3Norm1s36Physics80.s3CoreMapNorm1s t
      StepBBlock0.hmPay80 z = z := by
  unfold Slot3Norm1s36Physics80.s3CoreMapNorm1s
  rw [ite_eq_right (by rw [h]; decide)]

theorem uKick143Norm1s_mul_bit26_zero
    (t : Slot3Norm1s36_161w.Norm1sTier) (cfg : Configuration) :
    (Leaf3Slot3Norm1sWidth204.uKick143Norm1s t cfg).1 *
      slotBitProj (Fin.castAdd 36 (⟨26, by decide⟩ : Wire 107)) 0 =
      slotBitProj (Fin.castAdd 36 (⟨26, by decide⟩ : Wire 107)) 0 := by
  unfold Leaf3Slot3Norm1sWidth204.uKick143Norm1s
    DyadicQft64.catModAddUnitary
  refine permutationUnitary_mul_slotBitProj_id _
      (Fin.castAdd 36 (⟨26, by decide⟩ : Wire 107)) 0 fun j hj ↦ ?_
  apply catModAddPerm_apply_of_shift_zero
  apply s3Shift36Norm1s_eq_zero_of_accept_false
  apply s3AcceptNorm1s_eq_false_of_coin_ne6
  apply slot3MomCoin_ne_six_of_bit26_zero_assign
  rw [splitSysCatEquiv_fst_apply]
  exact hj

theorem uSwapRej107Norm1s_mul_bit26_zero
    (t : Slot3Norm1s36_161w.Norm1sTier) :
    (Slot3Norm1s36Physics80.uSwapRej107Norm1s t).1 *
      slotBitProj (⟨26, by decide⟩ : Wire 107) 0 =
      slotBitProj (⟨26, by decide⟩ : Wire 107) 0 := by
  let w26 : Wire 107 := ⟨26, by decide⟩
  refine mul_slotBitProj_id_of_entry _ w26 0 fun i j hj ↦ ?_
  unfold Slot3Norm1s36Physics80.uSwapRej107Norm1s
    Slot5MatrixAndScaleCert.signedInvolutionUnitary
  change Slot5MatrixAndScaleCert.signedPermMatrix
      (Slot3Norm1s36Physics80.swapRejPerm107Norm1s t)
      (Slot3Norm1s36Physics80.swapRejPhase107Norm1s t) i j =
    (1 : Operator (2 ^ 107)) i j
  rw [Slot5MatrixAndScaleCert.signedPermMatrix_apply]
  have hne6 := slot3MomCoin_ne_six_of_bit26_zero j hj
  have hAcc := s3AcceptNorm1s_eq_false_of_coin_ne6 t _ hne6
  have hMap := s3CoreMapNorm1s_eq_self_of_accept_false t _ hAcc
  have hPerm : Slot3Norm1s36Physics80.swapRejPerm107Norm1s t j = j := by
    change (basisBitsEquiv 107).symm
        (Slot3Norm1s36Physics80.swapRejMap107Norm1s
          t (basisBits 107 j)) = j
    have hFun : Slot3Norm1s36Physics80.swapRejMap107Norm1s t
        (basisBits 107 j) = basisBits 107 j := by
      funext k
      unfold Slot3Norm1s36Physics80.swapRejMap107Norm1s
      rw [hMap]
      have hbb80 :
          basisBits (FullSysMomSlots0135Concrete.momCoreWires 80)
            ((basisBitsEquiv
              (FullSysMomSlots0135Concrete.momCoreWires 80)).symm
              (StepBBlock0.embedAlpha107 (basisBits 107 j))) =
            StepBBlock0.embedAlpha107 (basisBits 107 j) :=
        (basisBitsEquiv _).apply_symm_apply _
      rw [congrFun hbb80 _, StepBBlock0.embedAlpha107_sel107_80]
    rw [hFun]; exact (basisBitsEquiv 107).symm_apply_apply j
  have hPh : Slot3Norm1s36Physics80.swapRejPhase107Norm1s t j = 1 := by
    unfold Slot3Norm1s36Physics80.swapRejPhase107Norm1s
      Slot3Norm1s36Physics80.s3RejPhaseNorm1s
    exact ite_eq_right (fun h ↦ hne6 h.1)
  by_cases hij : i = j
  · subst hij; rw [hPerm, hPh]; simp
  · have hji : j ≠ i := Ne.symm hij
    rw [Matrix.one_apply_ne hij, ite_eq_right (by rw [hPerm]; exact hji)]

theorem uCore143Norm1s_mul_bit26_zero
    (t : Slot3Norm1s36_161w.Norm1sTier) (cfg : Configuration) :
    (Leaf3Slot3Norm1sWidth204.uCore143Norm1s t cfg).1 *
      slotBitProj (Fin.castAdd 36 (⟨26, by decide⟩ : Wire 107)) 0 =
      slotBitProj (Fin.castAdd 36 (⟨26, by decide⟩ : Wire 107)) 0 := by
  let w26 : Wire 107 := ⟨26, by decide⟩
  have hBlk : QRegister.block 0 107 (by decide : 0 + 107 ≤ 143) w26 = Fin.castAdd 36 w26 :=
    Fin.ext (Nat.zero_add w26.val)
  have hSwap143 : (Leaf3Slot3Norm1sWidth204.uSwapRej143Norm1s
      t).1 * slotBitProj (Fin.castAdd 36 w26) 0 = slotBitProj (Fin.castAdd 36 w26) 0 := by
    unfold Leaf3Slot3Norm1sWidth204.uSwapRej143Norm1s
    rw [← hBlk, ← embedMatrix_slotBitProj, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
      uSwapRej107Norm1s_mul_bit26_zero t]
  unfold Leaf3Slot3Norm1sWidth204.uCore143Norm1s
  rw [Submonoid.coe_mul, Matrix.mul_assoc, uKick143Norm1s_mul_bit26_zero t cfg, hSwap143]

theorem comm_slotBitProj_of_commutesWithReg {k N : ℕ} {r : QRegister k N}
    {A : Operator (2 ^ N)} (hComm : CommutesWithReg r A) (i : Fin k) (b : Fin 2) :
    A * slotBitProj (r i) b = slotBitProj (r i) b * A := by
  rw [← embedMatrix_slotBitProj]
  exact hComm (slotBitProj i b)

theorem fwdPermUnitary_comm_slotBitProj {N : ℕ} (perm : Equiv.Perm (Fin (2 ^ N))) (w : Wire N)
    (b : Fin 2) (hFix : ∀ x : Fin (2 ^ N), basisBits N (perm x) w = basisBits N x w) :
    (TwosCompAndWire0Cancel.fwdPermUnitary perm).1 * slotBitProj w b
    = slotBitProj w b * (TwosCompAndWire0Cancel.fwdPermUnitary
    perm).1 := by
  ext i j
  rw [slotBitProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
  change TwosCompAndWire0Cancel.fwdPermMatrix perm i j * _ =
    _ * TwosCompAndWire0Cancel.fwdPermMatrix perm i j
  rw [TwosCompAndWire0Cancel.fwdPermMatrix_apply]
  by_cases hij : i = perm j
  · subst hij; rw [hFix j]; ring
  · have hji : perm j ≠ i := Ne.symm hij
    simp [hji]

theorem posMomUnitaryConj_mul_proj_id {D : ℕ} (U V : Unitary D) (P : Operator D)
    (hP : Pᴴ = P) (hUP : U.1 * P = P * U.1) (hVP : V.1 * P = P) :
    (PosMomSelectDynamic.unitaryConj U V).1 * P = P :=
  unitaryConj_mul_proj_id U V P hP hUP hVP

section HpowStep_22
attribute [local irreducible] HPow.hPow
local instance (priority := 1000000) instGroupUnitaryFast_aux_22 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 4200 in
theorem uSlot3HadCutCat36FullSys_mul_pCoinSlack010Seg
    (t : Slot3Norm1s36_161w.Norm1sTier) (cfg : Configuration) :
    (rCTSeg.embedUnitary ((rCoreTopCatInCT 36 (by decide)).embedUnitary
    (Leaf3HadCutBridge.uSlot3HadCutCat36FullSys t cfg))).1 *
    pCoinSlack010Seg = pCoinSlack010Seg := by
  let wMom2 : Wire (FullSysMomSlots0135Concrete.momCoreWires 80) :=
    FullSysMomSlots0135Concrete.momCoinReg 80 2
  let rCore0_36 := Leaf3Slot3Norm1sWidth204.rCore0_36
  have hSelW : Leaf3Slot3Norm1sWidth204.sel143_80_36
      (Fin.castAdd 36 (⟨26, by decide⟩ : Wire 107)) = rCore0_36 wMom2 := by
    rw [Leaf3Slot3Norm1sWidth204.sel143_80_36,
      QRegister.concat_apply_left]
    exact congrArg rCore0_36 (Fin.ext rfl)
  have hCoreLift :
      (Leaf3Slot3Norm1sWidth204.sel143_80_36.embedUnitary
        (Leaf3Slot3Norm1sWidth204.uCore143Norm1s t cfg)).1 *
        slotBitProj (rCore0_36 wMom2) 0 = slotBitProj (rCore0_36 wMom2) 0 := by
    rw [← hSelW, ← embedMatrix_slotBitProj, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, uCore143Norm1s_mul_bit26_zero t cfg]
  have hPrepMom : (Slot3Exact216Oracle80.uPrep3_216 (le_refl 80)).1
      * slotBitProj wMom2 0 = slotBitProj wMom2 0 *
      (Slot3Exact216Oracle80.uPrep3_216 (le_refl 80)).1 := by
    let rMom2 := QRegister.singleton wMom2
    have hQ : ∀ j : Fin 3, (Slot3Exact216Oracle80.s3QutritPairCore
        (le_refl 80) j).DisjointWires rMom2 := by
      intro j; rw [QRegister.disjoint_iff]; intro a b heq
      have hv := congrArg Fin.val heq
      have ha := a.isLt; have hb := b.isLt; have hj := j.isLt
      change (4020 + 2 * j.val) + a.val = 3950 at hv; omega
    have hC : (MomSlots35Slot3ProjNuclear.s3Coarse33Core (le_refl
        80)).DisjointWires rMom2 := by
      rw [QRegister.disjoint_iff]; intro a b heq
      have hv := congrArg Fin.val heq
      have ha := a.isLt
      change 3954 + a.val = 3950 at hv; omega
    have hReg : CommutesWithReg rMom2
        (Slot3Exact216Oracle80.uPrep3_216 (le_refl 80)).1 := by
      unfold Slot3Exact216Oracle80.uPrep3_216
        Slot3Exact216Oracle80.uQutrit3
        MomSlots35Slot3ProjNuclear.uPrep3
      rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
      exact ((CommutesWithReg.of_disjoint (hQ 2) _).mul ((CommutesWithReg.of_disjoint (hQ 1)
        _).mul (CommutesWithReg.of_disjoint (hQ 0) _))).mul (CommutesWithReg.of_disjoint hC _)
    exact comm_slotBitProj_of_commutesWithReg hReg 0 0
  have hPiMom :
      Slot3Prep273AndSwap3.uPiSwap3Core.1 * slotBitProj wMom2 0 =
        slotBitProj wMom2 0 * Slot3Prep273AndSwap3.uPiSwap3Core.1 := by
    have hMat : Slot3Prep273AndSwap3.uPiSwap3Core.1 =
        (TwosCompAndWire0Cancel.fwdPermUnitary
          Slot3Prep273AndSwap3.piSwap3CorePerm).1 := by
      ext i j
      rw [Slot3Prep273AndSwap3.uPiSwap3Core_apply]
      change _ = TwosCompAndWire0Cancel.fwdPermMatrix
        Slot3Prep273AndSwap3.piSwap3CorePerm i j
      rw [TwosCompAndWire0Cancel.fwdPermMatrix_apply]
      simp only [eq_comm]
    rw [hMat]
    refine fwdPermUnitary_comm_slotBitProj _ wMom2 0 fun x ↦ ?_
    rw [Slot3Prep273AndSwap3.basisBits_piSwap3CorePerm,
      Slot3Prep273AndSwap3.piSwap3Wire_fix_lt3954 wMom2
        (by change 3950 < 3954; decide)]
  have hPrepLift : (rCore0_36.embedUnitary
      (Slot3Exact216Oracle80.uPrep3_216 (le_refl 80))).1 *
      slotBitProj (rCore0_36 wMom2) 0 = slotBitProj (rCore0_36 wMom2) 0 *
      (rCore0_36.embedUnitary (Slot3Exact216Oracle80.uPrep3_216
      (le_refl 80))).1 := by
    rw [← embedMatrix_slotBitProj, QRegister.embedUnitary_val,
      ← rCore0_36.embedMatrix_mul, ← rCore0_36.embedMatrix_mul, hPrepMom]
  have hPiLift : (rCore0_36.embedUnitary
      Slot3Prep273AndSwap3.uPiSwap3Core).1 * slotBitProj
      (rCore0_36 wMom2) 0 = slotBitProj (rCore0_36 wMom2) 0 * (rCore0_36.embedUnitary
      Slot3Prep273AndSwap3.uPiSwap3Core).1 := by
    rw [← embedMatrix_slotBitProj, QRegister.embedUnitary_val,
      ← rCore0_36.embedMatrix_mul, ← rCore0_36.embedMatrix_mul, hPiMom]
  have hSwap36 :
      (Leaf3Slot3Norm1sWidth204.uSlot3Swap3Cat36Norm1s t cfg).1 *
        slotBitProj (rCore0_36 wMom2) 0 = slotBitProj (rCore0_36 wMom2) 0 := by
    unfold Leaf3Slot3Norm1sWidth204.uSlot3Swap3Cat36Norm1s
      Leaf3Slot3Norm1sWidth204.uSlot3Cat36Norm1s
    exact posMomUnitaryConj_mul_proj_id _ _ _ (slotBitProj_conjTranspose _ 0) hPiLift
      (posMomUnitaryConj_mul_proj_id _ _ _ (slotBitProj_conjTranspose _ 0) hPrepLift hCoreLift)
  let rC36 := Leaf3HadCutBridge.rCoreInCoreCat36
  have hSub : Leaf3HadCutBridge.hCoreCat36_eq = rfl :=
    Subsingleton.elim _ _
  have hwEq : rCore0_36 wMom2 = rC36 (iSlot2 80) := Fin.ext rfl
  have hCast36 : (OraAndPrepBundle.castNatUnitary
      Leaf3HadCutBridge.hCoreCat36_eq
      (Leaf3Slot3Norm1sWidth204.uSlot3Swap3Cat36Norm1s t
      cfg)).1 * slotBitProj (rC36 (iSlot2 80)) 0 = slotBitProj (rC36 (iSlot2 80)) 0 := by
    rw [hSub, ← hwEq]; exact hSwap36
  have hTailInv : (rC36.embedUnitary
      (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹).1 * slotBitProj
      (rC36 (iSlot2 80)) 0 = slotBitProj (rC36 (iSlot2 80)) 0 * (rC36.embedUnitary
      (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹).1 := by
    have h0 := unitary_inv_comm_selfAdj (slotBitProj_conjTranspose (iSlot2 80) 0)
      (Leaf4HadCut570.uTailHad3DCore_comm_slotBitProj
        (by decide : 3948 ≤ (iSlot2 80).val) 0)
    rw [← embedMatrix_slotBitProj, QRegister.embedUnitary_val,
      ← rC36.embedMatrix_mul, ← rC36.embedMatrix_mul, h0]
  have hHad36 : (Leaf3HadCutBridge.uSlot3HadCutCat36FullSys t
      cfg).1 * slotBitProj (rC36 (iSlot2 80)) 0 = slotBitProj (rC36 (iSlot2 80)) 0 :=
      unitaryConj_mul_proj_id _ _ _ (slotBitProj_conjTranspose _ 0) hTailInv hCast36
  have hComp36 : (rCoreTopCatInCT 36 (by decide)).compose rC36 = rCoreInCT80 := by
    apply InterWalkRSum42Hoist.qreg_ext; intro i
    have hc : rC36 i = Fin.castAdd 36 i := Fin.ext (Nat.zero_add i.val)
    change (rCoreTopCatInCT 36 (by decide)) (rC36 i) = rCoreInCT80 i
    rw [hc]; unfold rCoreTopCatInCT; rw [QRegister.concat_apply_left]
  have hSegS2 : (rCTSeg.embedUnitary ((rCoreTopCatInCT 36 (by decide)).embedUnitary
      (Leaf3HadCutBridge.uSlot3HadCutCat36FullSys t cfg))).1 *
      rCoreSeg.embedMatrix (slotBitProj (iSlot2 80) 0) = rCoreSeg.embedMatrix
      (slotBitProj (iSlot2 80) 0) := by
    rw[← rCTSeg_compose_rCoreInCT80, ← hComp36, ← QRegister.compose_assoc,
        ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
        QRegister.embedMatrix_compose (rCTSeg.compose (rCoreTopCatInCT 36 (by decide))) rC36,
        ← QRegister.embedMatrix_mul, embedMatrix_slotBitProj rC36 (iSlot2 80) 0, hHad36]
  unfold pCoinSlack010Seg pCoinSlack010Core
  rw [Matrix.mul_assoc (slotBitProj (iSlot2 80) 0), rCoreSeg.embedMatrix_mul,
    ← Matrix.mul_assoc, hSegS2]

end HpowStep_22
/- ## Section 2: `rCtrl3InSeg`, `rPGIdleOrig`, & Middle/Twist Slack Lemmas -/

theorem uTwCatSub_comm_pCoinSlack010Seg_of_comm_coin3 {mCatTw : ℕ} (hmCatTw : mCatTw ≤ 48)
    (uTwCatSub : Unitary (2 ^ (fullSysCoreWires 80 + mCatTw))) (h2 : uTwCatSub.1 *
    slotBitProj (Fin.castAdd mCatTw (iSlot2 80)) 0 = slotBitProj (Fin.castAdd mCatTw (iSlot2
    80)) 0 * uTwCatSub.1) (h1 : uTwCatSub.1 * slotBitProj (Fin.castAdd mCatTw (iSlot1 80)) 1 =
    slotBitProj (Fin.castAdd mCatTw (iSlot1 80)) 1 * uTwCatSub.1) (h0 : uTwCatSub.1 *
    slotBitProj (Fin.castAdd mCatTw (iSlot0 80)) 0 = slotBitProj (Fin.castAdd mCatTw (iSlot0
    80)) 0 * uTwCatSub.1) : (rCTSeg.embedUnitary ((rCoreTopCatInCT mCatTw
    hmCatTw).embedUnitary uTwCatSub)).1 * pCoinSlack010Seg = pCoinSlack010Seg *
    (rCTSeg.embedUnitary ((rCoreTopCatInCT mCatTw hmCatTw).embedUnitary uTwCatSub)).1 := by
  let rTop := rCTSeg.compose (rCoreTopCatInCT mCatTw hmCatTw)
  have hrTop : ∀ w : Wire (fullSysCoreWires 80),
      rTop (Fin.castAdd mCatTw w) = rCoreSeg w := fun w ↦ by
    change rCTSeg (rCoreTopCatInCT mCatTw hmCatTw (Fin.castAdd mCatTw w)) = rCoreSeg w
    rw [rCoreTopCatInCT, QRegister.concat_apply_left]
    exact congrArg (fun r ↦ r w) rCTSeg_compose_rCoreInCT80
  have hProj : rTop.embedMatrix (slotBitProj (Fin.castAdd mCatTw (iSlot2 80)) 0 * slotBitProj
      (Fin.castAdd mCatTw (iSlot1 80)) 1 * slotBitProj (Fin.castAdd mCatTw (iSlot0 80)) 0) =
      pCoinSlack010Seg := by
    unfold pCoinSlack010Seg pCoinSlack010Core
    rw[QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, embedMatrix_slotBitProj,
        embedMatrix_slotBitProj, embedMatrix_slotBitProj, hrTop, hrTop, hrTop,
        QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, embedMatrix_slotBitProj,
        embedMatrix_slotBitProj, embedMatrix_slotBitProj]
  have hSubComm : uTwCatSub.1 * (slotBitProj (Fin.castAdd mCatTw (iSlot2 80)) 0 * slotBitProj
      (Fin.castAdd mCatTw (iSlot1 80)) 1 * slotBitProj (Fin.castAdd mCatTw (iSlot0 80)) 0) =
      (slotBitProj (Fin.castAdd mCatTw (iSlot2 80)) 0 * slotBitProj (Fin.castAdd mCatTw
      (iSlot1 80)) 1 * slotBitProj (Fin.castAdd mCatTw (iSlot0 80)) 0) * uTwCatSub.1 := by
    rw [← Matrix.mul_assoc uTwCatSub.1, ← Matrix.mul_assoc uTwCatSub.1, h2,
      Matrix.mul_assoc _ _ (slotBitProj (Fin.castAdd mCatTw (iSlot1 80)) 1), h1,
      ← Matrix.mul_assoc (slotBitProj (Fin.castAdd mCatTw (iSlot2 80)) 0),
      Matrix.mul_assoc _ _ (slotBitProj (Fin.castAdd mCatTw (iSlot0 80)) 0), h0,
      ← Matrix.mul_assoc]
  rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val, ← hProj,
    ← rTop.embedMatrix_mul, ← rTop.embedMatrix_mul, hSubComm]

theorem coreQftHadamardPrunedBundle128_eq_ideal654 : coreQftHadamardPrunedBundle128.uQft654 =
    DyadicQft64WalkCircuit220.coreQftHadamardIdeal654 :=
    coreQftHadamardPrunedBundle128_uQft654

/- ## Section 3: `HoistedExtHkSelectSpec` with `rfl` Circuit Alignment -/

end ConfigSelStitchHelper

end SelStitchHelper

end
end SelStitchHelper

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
