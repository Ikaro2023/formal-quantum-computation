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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.FermKrylovSegBrg

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section MomSelectKrylov

section
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
namespace MomSelectKrylov
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowK3 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner (permElectron permElectronWire permElectronWireFun
  basisBits_permElectron signMagnitude_permElectron_electron)
open Slots01AndGridGuardBridge (elecAxisWord6)
open FullSysCatSegmentBridge (fullSysCoreWires)
open GeneralBetaAndAlphaTopEndpoint (zeroMomSlotOracle5)
open CoinDispatchedBarrel288 (swapElec0Bits coinBarrelIdxFast coinBarrelBitFnFast coinBarrelPermFast
  uBarrelFast)
open MomSlot0LocalAndMomCombine288 (uSlot0Local phaseDiagUnitary_val_eq_diag)
open InterWalkRSum42Hoist (qreg_block_apply PreservesFeature preservesFeature_permutationUnitary
  low3924Bits FixesLow3924 IsLow3924Prefix isLow3924Prefix_block0 low3924Bits_extractIndex_of_prefix
  h3924_momCore)
open SyndromeUncomp (badElecCount elecAxisWord6_val_eq_32_iff_signMagnitude)
open FermionicKrylovSegBridge (h3924_sys badElecCount_eq_of_low3924Bits_eq
  CoreOpMapsZeroBadToKrylov3 coreOpMapsZeroBadToKrylov3_of_entry)
/-- Canonical `systemQubits` prefix block inside `fullSysCoreWires mPayload`. -/
abbrev rSysInFullSysCore (mPayload : ℕ) : QRegister systemQubits (fullSysCoreWires mPayload) :=
  QRegister.block 0 systemQubits (by
    dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]; omega)
/-- Feature mapping a `fullSysCoreWires mPayload` basis state to `badElecCount` on
  `systemQubits`. -/
def coreBadElecCount (mPayload : ℕ) (x : Fin (2 ^ (fullSysCoreWires mPayload))) : ℕ :=
  badElecCount ((rSysInFullSysCore mPayload).extractIndex x)
/-- Operator on `fullSysCoreWires mPayload` preserving `badElecCount` on every nonzero
  transition. -/
def PreservesCoreBadElec {mPayload : ℕ} (M : Operator (2 ^ (fullSysCoreWires mPayload))) :
    Prop := PreservesFeature (coreBadElecCount mPayload) M
theorem coreOpMapsZeroBadToKrylov3_of_preservesCoreBadElec {mPayload : ℕ}
    {M : Operator (2 ^ (fullSysCoreWires mPayload))} (hM : PreservesCoreBadElec M) :
    CoreOpMapsZeroBadToKrylov3 M := by
  refine coreOpMapsZeroBadToKrylov3_of_entry (fun y x hne hx0 ↦ ?_)
  have heq : coreBadElecCount mPayload y = coreBadElecCount mPayload x := hM y x hne
  unfold coreBadElecCount rSysInFullSysCore at heq
  omega
theorem preservesCoreBadElec_of_fixesLow3924 {mPayload : ℕ}
    (hm : 3924 ≤ fullSysCoreWires mPayload) {M : Operator (2 ^ (fullSysCoreWires mPayload))}
    (hM : FixesLow3924 hm M) : PreservesCoreBadElec M := by
  intro y x hne
  have hlow := hM y x hne
  have hpref : IsLow3924Prefix h3924_sys hm (rSysInFullSysCore mPayload) :=
    isLow3924Prefix_block0 h3924_sys hm _
  exact badElecCount_eq_of_low3924Bits_eq (by
    rw [low3924Bits_extractIndex_of_prefix hpref y, low3924Bits_extractIndex_of_prefix hpref x]
    exact hlow)
theorem badElecCount_permElectron (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) : badElecCount (permElectron g x) = badElecCount x := by
  have h32 (i : Fin numElectrons) (w : Fin 3) :
      ((elecAxisWord6 (permElectron g x) i w).val = 32) ↔
        ((elecAxisWord6 x (g i) w).val = 32) := by
    rw [elecAxisWord6_val_eq_32_iff_signMagnitude, elecAxisWord6_val_eq_32_iff_signMagnitude,
      signMagnitude_permElectron_electron g x i w]
  unfold badElecCount
  rw [← Finset.card_map g.toEmbedding]
  congr 1; ext j
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.toEmbedding_apply, decide_eq_true_iff]
  refine ⟨?_, fun hj ↦ ⟨g.symm j, by rwa [h32 _ 0, h32 _ 1, h32 _ 2, g.apply_symm_apply],
    g.apply_symm_apply j⟩⟩
  rintro ⟨i, hi, rfl⟩; rwa [← h32 i 0, ← h32 i 1, ← h32 i 2]
theorem low3924Bits_extractIndex_coinBarrelPermFast_eq_permElectron {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) (x : Fin (2 ^ (fullSysCoreWires mPayload))) :
    let e := coinBarrelIdxFast hmPay (basisBits (fullSysCoreWires mPayload) x)
    low3924Bits h3924_sys ((rSysInFullSysCore mPayload).extractIndex (coinBarrelPermFast hmPay x)) =
      low3924Bits h3924_sys
        (permElectron (Equiv.swap (⟨0, by decide⟩ : Fin numElectrons) e)
          ((rSysInFullSysCore mPayload).extractIndex x)) := by
  intro e
  let e0 : Fin numElectrons := ⟨0, by decide⟩
  let rSys := rSysInFullSysCore mPayload
  have hmCore : 3924 ≤ fullSysCoreWires mPayload := by
    dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]; omega
  have hpref : IsLow3924Prefix h3924_sys hmCore rSys := isLow3924Prefix_block0 h3924_sys hmCore _
  rw [low3924Bits_extractIndex_of_prefix hpref (coinBarrelPermFast hmPay x)]
  have hbits : basisBits (fullSysCoreWires mPayload) (coinBarrelPermFast hmPay x) =
      coinBarrelBitFnFast hmPay (basisBits (fullSysCoreWires mPayload) x) :=
    (basisBitsEquiv _).apply_symm_apply _
  funext q
  have hq : q.val < 3924 := q.isLt
  have he : e.val < 218 := e.isLt
  rw [show low3924Bits hmCore (coinBarrelPermFast hmPay x) q =
    swapElec0Bits e (basisBits (fullSysCoreWires mPayload) x) ⟨q.val, lt_of_lt_of_le hq hmCore⟩
    from congrFun hbits _]
  dsimp only [low3924Bits]
  have hR1 : basisBits systemQubits (permElectron (Equiv.swap e0 e) (rSys.extractIndex x))
      ⟨q.val, lt_of_lt_of_le hq h3924_sys⟩ = basisBits systemQubits (rSys.extractIndex x)
      (permElectronWire (Equiv.swap e0 e) ⟨q.val, lt_of_lt_of_le hq h3924_sys⟩) :=
    basisBits_permElectron (permElectronWire (Equiv.swap e0 e)) _ _
  rw [hR1, rSys.basisBits_extractIndex]
  have hWireVal :
      (rSys (permElectronWire (Equiv.swap e0 e) ⟨q.val, lt_of_lt_of_le hq h3924_sys⟩)).val =
        18 * (Equiv.swap e0 e ⟨q.val / 18, by dsimp [numElectrons]; omega⟩).val + q.val % 18 := by
    have hr0 : (rSys (permElectronWire (Equiv.swap e0 e) ⟨q.val,
      lt_of_lt_of_le hq h3924_sys⟩)).val =
        (permElectronWireFun (Equiv.swap e0 e) ⟨q.val, lt_of_lt_of_le hq h3924_sys⟩).val := by
      have hle0 : 0 + systemQubits ≤ fullSysCoreWires mPayload := by
        dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]; omega
      have hfin := congrArg Fin.val (qreg_block_apply 0 systemQubits hle0
        (permElectronWire (Equiv.swap e0 e) ⟨q.val, lt_of_lt_of_le hq h3924_sys⟩))
      dsimp only at hfin
      change (QRegister.block 0 systemQubits hle0 _).val = _
      rw [hfin, Nat.zero_add]; rfl
    rw [hr0]; unfold permElectronWireFun; rw [dite_eq_left_of_eq_true (eq_true hq)]
  by_cases he0 : e.val = 0
  · simp only [swapElec0Bits, he0, ↓reduceIte]
    refine congrArg (basisBits _ x) (Fin.ext ?_)
    rw [hWireVal, show e = e0 from Fin.ext he0, Equiv.swap_self, Equiv.refl_apply]
    dsimp only; omega
  · simp only [swapElec0Bits, he0, ↓reduceIte]
    by_cases hq18 : q.val < 18
    · rw [dite_eq_left_of_eq_true (eq_true hq18)]
      refine congrArg (basisBits _ x) (Fin.ext ?_)
      rw [hWireVal,
        show (⟨q.val / 18, by dsimp [numElectrons]; omega⟩ : Fin numElectrons) = e0
          from Fin.ext (by dsimp [e0]; omega), Equiv.swap_apply_left]
      dsimp only; omega
    · rw [dite_eq_right_of_eq_false (eq_false hq18)]
      by_cases hqe : 18 * e.val ≤ q.val ∧ q.val < 18 * e.val + 18
      · rw [dite_eq_left_of_eq_true (eq_true hqe)]
        refine congrArg (basisBits _ x) (Fin.ext ?_)
        rw [hWireVal,
          show (⟨q.val / 18, by dsimp [numElectrons]; omega⟩ : Fin numElectrons) = e
            from Fin.ext (by dsimp; omega), Equiv.swap_apply_right]
        dsimp only [e0]; omega
      · rw [dite_eq_right_of_eq_false (eq_false hqe)]
        have hne0 : (⟨q.val / 18, by dsimp [numElectrons]; omega⟩ : Fin numElectrons) ≠ e0 :=
          fun h ↦ by have hv := congrArg Fin.val h; dsimp [e0] at hv; omega
        have hnee : (⟨q.val / 18, by dsimp [numElectrons]; omega⟩ : Fin numElectrons) ≠ e :=
          fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega
        refine congrArg (basisBits _ x) (Fin.ext ?_)
        rw [hWireVal, Equiv.swap_apply_of_ne_of_ne hne0 hnee]
        dsimp only; omega
theorem badElecCount_extractIndex_coinBarrelPermFast {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) (x : Fin (2 ^ (fullSysCoreWires mPayload))) :
    coreBadElecCount mPayload (coinBarrelPermFast hmPay x) = coreBadElecCount mPayload x := by
  unfold coreBadElecCount
  rw [badElecCount_eq_of_low3924Bits_eq
    (low3924Bits_extractIndex_coinBarrelPermFast_eq_permElectron hmPay x),
    badElecCount_permElectron]
theorem preservesCoreBadElec_uBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    PreservesCoreBadElec (uBarrelFast hmPay).1 := by
  rw [uBarrelFast]
  exact preservesFeature_permutationUnitary (coreBadElecCount mPayload)
    (coinBarrelPermFast hmPay) (badElecCount_extractIndex_coinBarrelPermFast hmPay)
theorem fixesLow3924_zeroMomSlotOracle5_eff (c : Configuration) :
    FixesLow3924 h3924_momCore ((zeroMomSlotOracle5 80 48).uSlotEff c).1 :=
  PreservesFeature.one (low3924Bits h3924_momCore)
theorem fixesLow3924_uSlot0Local_80 (w : ℝ) :
    FixesLow3924 h3924_momCore (uSlot0Local (le_refl 80) w).1 := by
  rw [uSlot0Local, phaseDiagUnitary_val_eq_diag]
  exact PreservesFeature.diagonal (low3924Bits h3924_momCore) _
end MomSelectKrylov
end
end MomSelectKrylov

noncomputable section PosFermKrylovTail

section
set_option maxRecDepth 131072
set_option exponentiation.threshold 5000
namespace PosFermKrylovTail
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowK4 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner (permElectron)
open Dyadic128CoulombMath (orbitCount47905)
open MeasureBranchHadamardSem (ket)
open ZeroAncillaUSP (omega8)
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open PosMomSelectSandwich (slotBitProj)
open SingleRBEGridGuardWalk (diagProj projGridAncZero)
open GridGuard654ReflAux (electronFieldLinearIdx)
open SixSlotEndpointJunctionBridge (diagProj_gridValidBool_eq_specsGridProjector)
open Slots01AndGridGuardBridge (elecAxisWord6)
open FullSysCatSegmentBridge (fullSysCoreWires fullSysRawAncWires fullSysBEWires beCoreBlock iSlot2
  FullSysQft654Bundle FullSysPrepareBundle FullSysSelectOracleBundle fullSysSelectPosUnitary
  fullSysSelectMomUnitary fullSysSelectEffUnitary fullSysSelectEffUnitary_conjTranspose_and_split
  fullSysRawBEUnitary)
open FullSysFullPrepareAndTopConcrete (selWiresSym coreWiresSym selCoin3Sym coreSysSym coreAncSym
  corePayloadSym coreHadamardUnitary_eq_embed)
open OraAndPrepBundle (PosPostPrepCert)
open ZeroSubwireCoinPrep80 (rCoin3Core)
open ZeroSubwireHarmonicGridPert (zeroSubwireConstPrepUnitary)
open Leaf4Ext48TopStitch (CommutesWithReg)
open InterWalkRSum42Hoist (qreg_block_apply PreservesFeature preservesFeature_permutationUnitary
  h3924_core)
open SingleAnchorFermionicPauliCap (emb_rEl_mul_pe_sp nSub_cubic_mul_fermionicProjector_zero nSub_sp
  rEl_disjoint_of_ne_sp rEl_sp rk1_sp)
open TwosCompAndWire0Cancel (fwdPermUnitary fwdPermUnitary_apply)
open ProjZ512QftAndTwist288 (permutationUnitary_entry)
open PosSlots24MergedVepBound (rProj24_sp matUnit24 projShift0Gen projLift0Gen
  elecFermionicProjector elecFermionicProjector_comm_embedMatrix)
open PosSlots24SemanticOracleConcrete80 (embedMatrix_entry_of_not_agreeOutside)
open PosPostPrep80MergedVep (uSwapCore3967 uSwapCore3967_mulVec_ket swapCore3967Fn
  swapCore3967Fn_involutive)
open MergedVepLeaf4GridPerturbation (swapCore3967Fn_eq_swapCoreScrGenFn12)
open MergedVepTopCoinCollapse (mWCore3967Gen mWCoreScrGen)
open Pos24Slot2FermionicBridge (barrelSysPerm diagonal_comm_embedMatrix_of_agreeOutside
  fwdPermUnitary_barrel_comm_rProj24 list_ofFn_embedUnitary_prod_mul list_prod_conj_comm_of_mem)
open PosHeadMod4_15476 (flipTh flipThClean permThClean headEnBoolSpec posPhaseMod4Z8Spec
  uPosPhaseMod4 headEnBoolSpec_update_wHeadThresh)
open PosS3Bounds (wThCore uXThCore mbh_ket_uXThCore)
open Leaf2PosMod4WidthCore (uPosPhase80Mod4Eff ket_monomialZ8_ket)
open SyndromeUncomp (badElecCount elecFieldBadBits elecFieldBadBits_eq_true_iff
  elecAxisWord6_val_eq_32_iff_signMagnitude)
open FermionicKrylovSegBridge (h3924_sys badElecLeBool krylov3Bool krylov3Proj bad0Proj
  bad0Proj_mul_diagProj_gridValidBool mul_embedMatrix_diagProj_apply embedMatrix_diagProj_mul_apply
  badElecCount_eq_of_low3924Bits_eq CoreOpMapsZeroBadToKrylov3 pFermBE RawBEMapsFermToKrylov3)
open MomSelectKrylov (rSysInFullSysCore coreBadElecCount PreservesCoreBadElec
  preservesCoreBadElec_of_fixesLow3924 badElecCount_permElectron)
open PosSlots24BranchConcrete (posCoreWires)
def CoreMapsToKrylov3On {mPayload : ℕ} (P M : Operator (2 ^ (fullSysCoreWires mPayload))) : Prop :=
  (rSysInFullSysCore mPayload).embedMatrix krylov3Proj * (M * P) = M * P
def CoreFermMapsToKrylov3 (spinUp : Finset (Fin numElectrons)) {mPayload : ℕ}
    (M : Operator (2 ^ (fullSysCoreWires mPayload))) : Prop :=
  CoreMapsToKrylov3On ((rSysInFullSysCore mPayload).embedMatrix (fermionicProjector spinUp)) M
theorem CoreMapsToKrylov3On.zero {mPayload : ℕ}
    (P : Operator (2 ^ (fullSysCoreWires mPayload))) : CoreMapsToKrylov3On P 0 := by
  simp [CoreMapsToKrylov3On]
theorem CoreMapsToKrylov3On.add {mPayload : ℕ}
    {P M₁ M₂ : Operator (2 ^ (fullSysCoreWires mPayload))} (h₁ : CoreMapsToKrylov3On P M₁)
    (h₂ : CoreMapsToKrylov3On P M₂) : CoreMapsToKrylov3On P (M₁ + M₂) := by
  unfold CoreMapsToKrylov3On at h₁ h₂ ⊢; rw [Matrix.add_mul, Matrix.mul_add, h₁, h₂]
theorem CoreMapsToKrylov3On.smul {mPayload : ℕ}
    {P M : Operator (2 ^ (fullSysCoreWires mPayload))} (c : ℂ) (h : CoreMapsToKrylov3On P M) :
    CoreMapsToKrylov3On P (c • M) := by
  unfold CoreMapsToKrylov3On at h ⊢; rw [Matrix.smul_mul, Matrix.mul_smul, h]
theorem CoreMapsToKrylov3On.finset_sum {ι : Type*} {mPayload : ℕ}
    {P : Operator (2 ^ (fullSysCoreWires mPayload))} (s : Finset ι)
    (f : ι → Operator (2 ^ (fullSysCoreWires mPayload)))
    (hf : ∀ i ∈ s, CoreMapsToKrylov3On P (f i)) : CoreMapsToKrylov3On P (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using CoreMapsToKrylov3On.zero P
  | cons a t hat ih =>
      rw [Finset.sum_cons]
      exact (hf a (Finset.mem_cons_self a t)).add (ih fun i hi ↦ hf i (Finset.mem_cons_of_mem hi))
theorem CoreMapsToKrylov3On.mul_right {mPayload : ℕ}
    {P M : Operator (2 ^ (fullSysCoreWires mPayload))}
    (R : Operator (2 ^ (fullSysCoreWires mPayload))) (h : CoreMapsToKrylov3On P M) :
    CoreMapsToKrylov3On (P * R) M := by
  unfold CoreMapsToKrylov3On at h ⊢; rw [← Matrix.mul_assoc M, ← Matrix.mul_assoc, h]
theorem preservesCoreBadElec_comm_krylov3Proj {mPayload : ℕ}
    {U : Operator (2 ^ (fullSysCoreWires mPayload))} (hU : PreservesCoreBadElec U) :
    U * (rSysInFullSysCore mPayload).embedMatrix krylov3Proj =
      (rSysInFullSysCore mPayload).embedMatrix krylov3Proj * U := by
  ext i j
  rw [mul_embedMatrix_diagProj_apply, embedMatrix_diagProj_mul_apply]
  rcases eq_or_ne (U i j) 0 with h0 | h0
  · rw [h0, zero_mul, mul_zero]
  · have hc := hU i j h0; unfold coreBadElecCount at hc
    have heq : krylov3Bool ((rSysInFullSysCore mPayload).extractIndex i) =
        krylov3Bool ((rSysInFullSysCore mPayload).extractIndex j) := by
      unfold krylov3Bool badElecLeBool; rw [hc]
    rw [heq, mul_comm]
theorem CoreMapsToKrylov3On.preserves_mul_left {mPayload : ℕ}
    {P U M : Operator (2 ^ (fullSysCoreWires mPayload))} (hU : PreservesCoreBadElec U)
    (hM : CoreMapsToKrylov3On P M) : CoreMapsToKrylov3On P (U * M) := by
  unfold CoreMapsToKrylov3On at hM ⊢
  rw [Matrix.mul_assoc U M P, ← Matrix.mul_assoc _ U (M * P),
    ← preservesCoreBadElec_comm_krylov3Proj hU, Matrix.mul_assoc U _ (M * P),
    hM, ← Matrix.mul_assoc U M P]
theorem CoreMapsToKrylov3On.of_zeroBad_absorb {mPayload : ℕ}
    {P M : Operator (2 ^ (fullSysCoreWires mPayload))}
    (h0 : (rSysInFullSysCore mPayload).embedMatrix bad0Proj * P = P)
    (hM : CoreOpMapsZeroBadToKrylov3 M) : CoreMapsToKrylov3On P M := by
  have hm : CoreMapsToKrylov3On ((rSysInFullSysCore mPayload).embedMatrix bad0Proj) M := hM
  simpa only [h0] using hm.mul_right P
theorem bad0Proj_mul_fermionicProjector (spinUp : Finset (Fin numElectrons)) :
    bad0Proj * fermionicProjector spinUp = fermionicProjector spinUp := by
  rw [← SpecsAux.gridProjector_mul_fermionicProjector spinUp,
    ← diagProj_gridValidBool_eq_specsGridProjector, ← Matrix.mul_assoc,
    bad0Proj_mul_diagProj_gridValidBool]
theorem coreFermMapsToKrylov3_of_zeroBad (spinUp : Finset (Fin numElectrons)) {mPayload : ℕ}
    {M : Operator (2 ^ (fullSysCoreWires mPayload))} (hM : CoreOpMapsZeroBadToKrylov3 M) :
    CoreFermMapsToKrylov3 spinUp M :=
  CoreMapsToKrylov3On.of_zeroBad_absorb
    (by rw [← (rSysInFullSysCore mPayload).embedMatrix_mul, bad0Proj_mul_fermionicProjector]) hM
theorem slotBitProj_comm_embed_rSysCore {mPayload : ℕ} (b : Fin 2)
    (A : Operator (2 ^ systemQubits)) :
    slotBitProj (iSlot2 mPayload) b * (rSysInFullSysCore mPayload).embedMatrix A =
      (rSysInFullSysCore mPayload).embedMatrix A * slotBitProj (iSlot2 mPayload) b := by
  unfold slotBitProj
  refine diagonal_comm_embedMatrix_of_agreeOutside (rSysInFullSysCore mPayload) _
    (fun z' z hag ↦ ?_) A
  refine congrArg (fun x ↦ if x = b.val then (1 : ℂ) else 0) (congrArg (fun u ↦ (u : ℕ)) ?_)
  exact congrArg Fin.val (hag (iSlot2 mPayload) fun ⟨j, hj⟩ ↦ by
    have hv := congrArg Fin.val hj; have hjlt := j.isLt
    simp only [rSysInFullSysCore, qreg_block_apply, systemQubits, numElectrons, electronBits,
      projectileBits] at hv hjlt
    omega)
theorem coreFermMapsToKrylov3_selectEff_of_posSlot0_mom (spinUp : Finset (Fin numElectrons))
    {mPayload mPGTwist : ℕ} (qft : FullSysQft654Bundle)
    (sel : FullSysSelectOracleBundle mPayload mPGTwist) (c : Configuration) (hPos :
    CoreFermMapsToKrylov3 spinUp ((fullSysSelectPosUnitary qft sel c).1 * slotBitProj (iSlot2
    mPayload) 0)) (hMom : CoreOpMapsZeroBadToKrylov3 (fullSysSelectMomUnitary sel c).1) :
    CoreFermMapsToKrylov3 spinUp (fullSysSelectEffUnitary qft sel c).1 := by
  rw [(fullSysSelectEffUnitary_conjTranspose_and_split qft sel c).1]
  refine CoreMapsToKrylov3On.add hPos ?_
  unfold CoreMapsToKrylov3On
  have hMomF : (rSysInFullSysCore mPayload).embedMatrix krylov3Proj *
      ((fullSysSelectMomUnitary sel c).1 *
        (rSysInFullSysCore mPayload).embedMatrix (fermionicProjector spinUp)) =
      (fullSysSelectMomUnitary sel c).1 *
        (rSysInFullSysCore mPayload).embedMatrix (fermionicProjector spinUp) :=
    coreFermMapsToKrylov3_of_zeroBad spinUp hMom
  rw [Matrix.mul_assoc (fullSysSelectMomUnitary sel c).1,
    slotBitProj_comm_embed_rSysCore 1, ← Matrix.mul_assoc (fullSysSelectMomUnitary sel c).1,
    ← Matrix.mul_assoc _ _ (slotBitProj (iSlot2 mPayload) 1), hMomF,
    Matrix.mul_assoc (fullSysSelectMomUnitary sel c).1,
    ← slotBitProj_comm_embed_rSysCore 1, ← Matrix.mul_assoc]
theorem rawBEMapsFermToKrylov3_of_selectEff_comm
    (spinUp : Finset (Fin numElectrons)) {mPayload mPGTwist : ℕ}
    (qft : FullSysQft654Bundle) (prep : FullSysPrepareBundle mPayload)
    (sel : FullSysSelectOracleBundle mPayload mPGTwist) (c : Configuration)
    (hPrep : CommutesWithReg (coreSysSym mPayload) (prep.uPrep c).1)
    (hSel : CoreFermMapsToKrylov3 spinUp (fullSysSelectEffUnitary qft sel c).1) :
    RawBEMapsFermToKrylov3 spinUp (fullSysRawBEUnitary qft prep sel c) := by
  let rSys : QRegister systemQubits (fullSysBEWires mPayload) := coreSysSym mPayload
  let rAnc : QRegister (fullSysRawAncWires mPayload) (fullSysBEWires mPayload) :=
    QRegister.block systemQubits (fullSysRawAncWires mPayload) le_rfl
  have hComp : (beCoreBlock mPayload).compose (rSysInFullSysCore mPayload) = rSys :=
    QRegister.ext (Function.Embedding.ext fun i ↦ Fin.ext (by
      simp only [QRegister.compose_apply, beCoreBlock, rSysInFullSysCore, rSys,
        coreSysSym, qreg_block_apply]
      omega))
  have hSelBE : rSys.embedMatrix krylov3Proj * (((beCoreBlock mPayload).embedUnitary
      (fullSysSelectEffUnitary qft sel c)).1 * rSys.embedMatrix (fermionicProjector spinUp))
      = ((beCoreBlock mPayload).embedUnitary (fullSysSelectEffUnitary qft sel c)).1 *
      rSys.embedMatrix (fermionicProjector spinUp) := by
    rw [← hComp, QRegister.embedUnitary_val, QRegister.embedMatrix_compose,
      QRegister.embedMatrix_compose, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
    exact congrArg (beCoreBlock mPayload).embedMatrix hSel
  have hPF : (prep.uPrep c).1 * rSys.embedMatrix (fermionicProjector spinUp) =
      rSys.embedMatrix (fermionicProjector spinUp) * (prep.uPrep c).1 :=
    hPrep (fermionicProjector spinUp)
  have hPK : rSys.embedMatrix krylov3Proj * (prep.uPrep c).1ᴴ =
      (prep.uPrep c).1ᴴ * rSys.embedMatrix krylov3Proj := by
    have hU1 : (prep.uPrep c).1ᴴ * (prep.uPrep c).1 = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (prep.uPrep c).2
    have hU2 : (prep.uPrep c).1 * (prep.uPrep c).1ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (prep.uPrep c).2
    have hPKM : (prep.uPrep c).1 * rSys.embedMatrix krylov3Proj =
        rSys.embedMatrix krylov3Proj * (prep.uPrep c).1 := hPrep krylov3Proj
    calc rSys.embedMatrix krylov3Proj * (prep.uPrep c).1ᴴ
      _ = (prep.uPrep c).1ᴴ * ((prep.uPrep c).1 * rSys.embedMatrix krylov3Proj) *
            (prep.uPrep c).1ᴴ := by
            rw [← Matrix.mul_assoc (prep.uPrep c).1ᴴ, hU1, Matrix.one_mul]
      _ = (prep.uPrep c).1ᴴ * rSys.embedMatrix krylov3Proj := by
            rw [hPKM, Matrix.mul_assoc, Matrix.mul_assoc, hU2, Matrix.mul_one]
  unfold RawBEMapsFermToKrylov3 fullSysRawBEUnitary pFermBE projGridAncZero
  change rSys.embedMatrix krylov3Proj * ((unitaryConj (prep.uPrep c) ((beCoreBlock
    mPayload).embedUnitary (fullSysSelectEffUnitary qft sel c))).1 * (rSys.embedMatrix
    (fermionicProjector spinUp) * rAnc.basisOutcomeProjector 0)) = _
  rw [unitaryConj_val]
  set S_emb := ((beCoreBlock mPayload).embedUnitary (fullSysSelectEffUnitary qft sel c)).1
  rw [← Matrix.mul_assoc _ _ (rAnc.basisOutcomeProjector 0),
    ← Matrix.mul_assoc (rSys.embedMatrix krylov3Proj) _ (rAnc.basisOutcomeProjector 0)]
  refine congrArg (· * rAnc.basisOutcomeProjector 0) ?_
  calc rSys.embedMatrix krylov3Proj * (((prep.uPrep c).1ᴴ * S_emb * (prep.uPrep c).1) *
        rSys.embedMatrix (fermionicProjector spinUp))
    _ = (rSys.embedMatrix krylov3Proj * (prep.uPrep c).1ᴴ) * S_emb *
          ((prep.uPrep c).1 * rSys.embedMatrix (fermionicProjector spinUp)) := by
          simp only [Matrix.mul_assoc]
    _ = (prep.uPrep c).1ᴴ * S_emb *
          (rSys.embedMatrix (fermionicProjector spinUp) * (prep.uPrep c).1) := by
          rw [hPK, hPF, Matrix.mul_assoc (prep.uPrep c).1ᴴ, Matrix.mul_assoc (prep.uPrep c).1ᴴ,
            ← Matrix.mul_assoc (rSys.embedMatrix krylov3Proj * S_emb),
            Matrix.mul_assoc (rSys.embedMatrix krylov3Proj) S_emb, hSelBE]
          simp only [Matrix.mul_assoc]
    _ = ((prep.uPrep c).1ᴴ * S_emb * (prep.uPrep c).1) *
          rSys.embedMatrix (fermionicProjector spinUp) := by
          rw [← hPF]; simp only [Matrix.mul_assoc]
theorem commutesWithReg_coreSysSym_zeroSubwireConstPrepUnitary {mPayload : ℕ}
    (post : PosPostPrepCert mPayload) (uCoin : Unitary (2 ^ 3)) (hPost : ∃ V : Unitary (2 ^
    (selWiresSym mPayload)), post.uPosPost = (coreAncSym mPayload).embedUnitary V) :
    CommutesWithReg (coreSysSym mPayload) (zeroSubwireConstPrepUnitary post uCoin).1 := by
  rcases hPost with ⟨V, hV⟩
  have hAncDisj : (coreAncSym mPayload).DisjointWires (coreSysSym mPayload) :=
    (QRegExt.disjointWires_symm (QRegister.block_disjoint_of_le 0 systemQubits systemQubits
      (selWiresSym mPayload)
      (by simp only [selWiresSym]; omega) le_rfl (by omega)))
  have hPayDisj : (corePayloadSym mPayload).DisjointWires (coreSysSym mPayload) :=
    (QRegExt.disjointWires_symm (QRegister.block_disjoint_of_le 0 systemQubits (systemQubits +
      6) mPayload
      (by simp only [coreWiresSym, selWiresSym]; omega)
      (by simp only [coreWiresSym, selWiresSym]; omega) (by omega)))
  have hCoinDisj : (rCoin3Core mPayload).DisjointWires (coreSysSym mPayload) :=
    hAncDisj.compose_left (selCoin3Sym mPayload)
  unfold zeroSubwireConstPrepUnitary
  rw [hV, coreHadamardUnitary_eq_embed, Submonoid.coe_mul, Submonoid.coe_mul,
    QRegister.embedUnitary_val, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  exact (CommutesWithReg.of_disjoint hAncDisj V.1).mul
    ((CommutesWithReg.of_disjoint hPayDisj _).mul (CommutesWithReg.of_disjoint hCoinDisj uCoin.1))
theorem bad0Proj_comm_rProj24 (M : Operator (2 ^ 24)) :
    bad0Proj * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * bad0Proj := by
  unfold bad0Proj diagProj
  refine diagonal_comm_embedMatrix_of_agreeOutside rProj24_sp _ (fun x' x hag ↦ ?_) M
  have hbc : badElecCount x' = badElecCount x :=
    badElecCount_eq_of_low3924Bits_eq (funext fun q ↦ hag ⟨q.val, lt_of_lt_of_le q.isLt h3924_sys⟩
      (by
        rintro ⟨k, hk⟩;
        have hv := congrArg Fin.val hk;
        have :=
          q.isLt; simp only [rProj24_sp, qreg_block_apply] at hv; omega))
  unfold badElecLeBool; rw [hbc]
theorem bad0Proj_mul_elecFermionicProjector (spinUp : Finset (Fin numElectrons)) :
    bad0Proj * elecFermionicProjector spinUp = elecFermionicProjector spinUp := by
  change bad0Proj * projLift0Gen rProj24_sp (fermionicProjector spinUp) = _
  unfold projLift0Gen; rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun yIdx _ ↦ ?_
  unfold projShift0Gen
  rw [← rProj24_sp.embedMatrix_conjTranspose,
    ← Matrix.mul_assoc bad0Proj, ← Matrix.mul_assoc bad0Proj, bad0Proj_comm_rProj24,
    Matrix.mul_assoc _ bad0Proj, bad0Proj_mul_fermionicProjector]
theorem nSub_sp_comm_rProj24 (χ : Fin (2 ^ 18) → ℂ) (S : Finset (Fin numElectrons))
    (M : Operator (2 ^ 24)) :
    nSub_sp χ S * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * nSub_sp χ S := by
  unfold nSub_sp; rw [Finset.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  refine QRegister.embedMatrix_comm_of_disjoint (rEl_sp e) rProj24_sp (by
    rw [QRegister.disjoint_iff]; intro i j hij
    have hv := congrArg Fin.val hij; have := e.isLt; have := i.isLt
    change e.val < 218 at *; simp only [rEl_sp, rProj24_sp, qreg_block_apply] at hv; omega) _ M
private theorem cubic_comm_mul {d : ℕ} (N N' E : Operator d) (h : N * E = E * N') :
    N * (N - 1) * (N - (2 : ℂ) • 1) * E = E * (N' * (N' - 1) * (N' - (2 : ℂ) • 1)) := by
  have h1 : (N - 1) * E = E * (N' - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]
  have h2 : (N - (2 : ℂ) • 1) * E = E * (N' - (2 : ℂ) • 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc (N * (N - 1)) _ E, h2, ← Matrix.mul_assoc (N * (N - 1)) E,
    Matrix.mul_assoc N (N - 1) E, h1, ← Matrix.mul_assoc N E, h]
  simp only [Matrix.mul_assoc]
theorem nSub_cubic_mul_elecFermionicProjector_zero {χ : Fin (2 ^ 18) → ℂ}
    (hnorm : ∑ u : Fin (2 ^ 18), star (χ u) * χ u = 1) (spinUp S : Finset (Fin numElectrons)) :
    nSub_sp χ S * (nSub_sp χ S - 1) * (nSub_sp χ S - (2 : ℂ) • 1) *
      elecFermionicProjector spinUp = 0 := by
  change _ * projLift0Gen rProj24_sp (fermionicProjector spinUp) = 0
  unfold projLift0Gen projShift0Gen; rw [Matrix.mul_sum]
  refine Finset.sum_eq_zero fun yIdx _ ↦ ?_
  rw [← rProj24_sp.embedMatrix_conjTranspose,
    ← Matrix.mul_assoc _ _ (rProj24_sp.embedMatrix (matUnit24 0 yIdx)),
    ← Matrix.mul_assoc _ _ (fermionicProjector spinUp),
    cubic_comm_mul _ _ _ (nSub_sp_comm_rProj24 χ S _),
    Matrix.mul_assoc (rProj24_sp.embedMatrix _),
    nSub_cubic_mul_fermionicProjector_zero hnorm spinUp S, Matrix.mul_zero, Matrix.zero_mul]
noncomputable def swappedElecFermProj (spinUp : Finset (Fin numElectrons))
    (g : Equiv.Perm (Fin numElectrons)) : Operator (2 ^ systemQubits) :=
  (permutationUnitary (permElectron g)).1 * elecFermionicProjector spinUp
theorem bad0Proj_mul_swappedElecFermProj (spinUp : Finset (Fin numElectrons))
    (g : Equiv.Perm (Fin numElectrons)) :
    bad0Proj * swappedElecFermProj spinUp g = swappedElecFermProj spinUp g := by
  have hcomm : bad0Proj * (permutationUnitary (permElectron g)).1 =
      (permutationUnitary (permElectron g)).1 * bad0Proj := by
    change Matrix.diagonal (fun x ↦ if badElecLeBool 0 x = true then (1 : ℂ) else 0) *
      (permutationUnitary (permElectron g)).1 = (permutationUnitary (permElectron g)).1 *
      Matrix.diagonal (fun x ↦ if badElecLeBool 0 x = true then (1 : ℂ) else 0)
    ext i j; rw [Matrix.diagonal_mul, Matrix.mul_diagonal, permutationUnitary_entry]
    by_cases hij : permElectron g j = i
    · subst hij; unfold badElecLeBool; rw [badElecCount_permElectron g j]; simp [mul_comm]
    · simp [hij]
  unfold swappedElecFermProj
  rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, bad0Proj_mul_elecFermionicProjector]
theorem swappedElecFermProj_swap0_comm_rProj24 (spinUp : Finset (Fin numElectrons))
    (e : Fin numElectrons) (M : Operator (2 ^ 24)) :
    swappedElecFermProj spinUp (Equiv.swap 0 e) * rProj24_sp.embedMatrix M =
      rProj24_sp.embedMatrix M * swappedElecFermProj spinUp (Equiv.swap 0 e) := by
  have hpe : (permutationUnitary (permElectron (Equiv.swap 0 e))).1 =
      (fwdPermUnitary (barrelSysPerm e.val)).1 := by
    have he218 : e.val < 218 := e.isLt
    have hb : barrelSysPerm e.val = permElectron (Equiv.swap 0 e) := by
      unfold barrelSysPerm; simp [he218]
    rw [hb]; ext i j; rw [permutationUnitary_entry, fwdPermUnitary_apply]
  unfold swappedElecFermProj
  rw [hpe, Matrix.mul_assoc, elecFermionicProjector_comm_embedMatrix, ← Matrix.mul_assoc,
    fwdPermUnitary_barrel_comm_rProj24, Matrix.mul_assoc]
theorem nSub_cubic_mul_swappedElecFermProj_zero {χ : Fin (2 ^ 18) → ℂ}
    (hnorm : ∑ u : Fin (2 ^ 18), star (χ u) * χ u = 1) (spinUp S : Finset (Fin numElectrons))
    (g : Equiv.Perm (Fin numElectrons)) : nSub_sp χ S * (nSub_sp χ S - 1) *
    (nSub_sp χ S - (2 : ℂ) • 1) * swappedElecFermProj spinUp g = 0 := by
  have hn : nSub_sp χ S * (permutationUnitary (permElectron g)).1 =
      (permutationUnitary (permElectron g)).1 * nSub_sp χ (S.map g.toEmbedding) := by
    unfold nSub_sp; rw [Finset.sum_mul, Finset.sum_map, Matrix.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ emb_rEl_mul_pe_sp g i (rk1_sp χ)
  unfold swappedElecFermProj
  rw [← Matrix.mul_assoc, cubic_comm_mul _ _ _ hn, Matrix.mul_assoc,
    nSub_cubic_mul_elecFermionicProjector_zero hnorm spinUp _, Matrix.mul_zero]
def SysMapsZeroBadToKrylov3 (M : Operator (2 ^ systemQubits)) : Prop :=
  krylov3Proj * (M * bad0Proj) = M * bad0Proj
theorem coreOpMapsZeroBadToKrylov3_embed_sys {mPayload : ℕ}
    {M : Operator (2 ^ systemQubits)} (hM : SysMapsZeroBadToKrylov3 M) :
    CoreOpMapsZeroBadToKrylov3 ((rSysInFullSysCore mPayload).embedMatrix M) := by
  change (rSysInFullSysCore mPayload).embedMatrix krylov3Proj *
      ((rSysInFullSysCore mPayload).embedMatrix M *
        (rSysInFullSysCore mPayload).embedMatrix bad0Proj) = _
  rw [← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
  exact congrArg (rSysInFullSysCore mPayload).embedMatrix hM
noncomputable def elecSysProd (V : Fin numElectrons →
    Unitary (2 ^ 18)) : Unitary (2 ^ systemQubits) :=
  (List.ofFn fun e : Fin numElectrons ↦ (rEl_sp e).embedUnitary (V e)).prod
def outsideElecFeature (S : Finset (Fin numElectrons)) (z : Fin (2 ^ systemQubits)) :
    {e : Fin numElectrons // e ∉ S} → Fin (2 ^ 18) := fun e ↦ (rEl_sp e.1).extractIndex z
theorem preservesFeature_outsideElec_embed_mem {S : Finset (Fin numElectrons)}
    {s : Fin numElectrons} (hs : s ∈ S) (A : Operator (2 ^ 18)) :
    PreservesFeature (outsideElecFeature S) ((rEl_sp s).embedMatrix A) := by
  intro y x hne; by_contra hdiff
  have hag : ¬ (rEl_sp s).AgreeOutside y x := fun hag ↦ hdiff (funext fun e ↦ by
    apply (basisBitsEquiv 18).injective; funext j
    change basisBits 18 ((rEl_sp e.1).extractIndex y) j =
      basisBits 18 ((rEl_sp e.1).extractIndex x) j
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    have hdisj : (rEl_sp s).DisjointWires (rEl_sp e.1) :=
      rEl_disjoint_of_ne_sp (fun hEq ↦ e.2 (hEq ▸ hs))
    exact hag (rEl_sp e.1 j) fun ⟨k, hk⟩ ↦ (QRegister.disjoint_iff.mp hdisj) k j hk)
  exact hne (embedMatrix_entry_of_not_agreeOutside (rEl_sp s) A hag)
theorem sysMapsZeroBadToKrylov3_of_preserves_outsideElec {S : Finset (Fin numElectrons)}
    (hS : S.card ≤ 3) {M : Operator (2 ^ systemQubits)}
    (hM : PreservesFeature (outsideElecFeature S) M) : SysMapsZeroBadToKrylov3 M := by
  change Matrix.diagonal (fun x ↦ if krylov3Bool x = true then (1 : ℂ) else 0) *
      ((M : Matrix (Fin (2 ^ systemQubits)) (Fin (2 ^ systemQubits)) ℂ) *
        Matrix.diagonal (fun x ↦ if badElecLeBool 0 x = true then (1 : ℂ) else 0)) =
    (M : Matrix (Fin (2 ^ systemQubits)) (Fin (2 ^ systemQubits)) ℂ) *
      Matrix.diagonal (fun x ↦ if badElecLeBool 0 x = true then (1 : ℂ) else 0)
  generalize hMeq : (M : Matrix (Fin (2 ^ systemQubits)) (Fin (2 ^ systemQubits)) ℂ) = M'
  ext y x; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases eq_or_ne (M' y x) 0 with h0 | h0
  · rw [h0, zero_mul, mul_zero]
  · by_cases hb0 : badElecLeBool 0 x = true
    · have hx0 : badElecCount x = 0 := Nat.le_zero.mp (of_decide_eq_true hb0)
      have h0M : M y x ≠ 0 := by rwa [show M y x = M' y x from congrFun (congrFun hMeq y) x]
      have hout := congrFun (hM y x h0M)
      have hsub : (Finset.univ.filter fun e : Fin numElectrons ↦
          decide ((elecAxisWord6 y e 0).val = 32 ∨ (elecAxisWord6 y e 1).val = 32 ∨
                  (elecAxisWord6 y e 2).val = 32)) ⊆ S := fun e he ↦ by
        by_contra hnot
        have hex : (rEl_sp e).extractIndex y = (rEl_sp e).extractIndex x := hout ⟨e, hnot⟩
        have h32 : ∀ w : Fin 3,
            ((elecAxisWord6 y e w).val = 32) ↔ ((elecAxisWord6 x e w).val = 32) := fun w ↦ by
          have he218 : e.val < 218 := e.isLt
          have hw3 : w.val < 3 := w.isLt
          let f : Fin 654 := ⟨3 * e.val + w.val, by omega⟩
          have hf_eq : elecFieldBadBits (basisBits systemQubits y) f =
              elecFieldBadBits (basisBits systemQubits x) f := by
            have hbit : ∀ u : Fin 6,
                basisBits systemQubits y (electronFieldLinearIdx f u) =
                  basisBits systemQubits x (electronFieldLinearIdx f u) := fun u ↦ by
              have hu6 : u.val < 6 := u.isLt
              have h1 := congrFun (congrArg (basisBits 18) hex) ⟨6 * w.val + u.val, by omega⟩
              rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex] at h1
              exact (congrArg (basisBits systemQubits y) (Fin.ext (by
                simp only [rEl_sp, electronFieldLinearIdx, qreg_block_apply, f]; omega))).trans
                (h1.trans (congrArg (basisBits systemQubits x) (Fin.ext (by
                  simp only [rEl_sp, electronFieldLinearIdx, qreg_block_apply, f]; omega))))
            unfold elecFieldBadBits
            simp only [fun u : Fin 5 ↦ hbit u.castSucc, hbit 5]
          have hfy := elecFieldBadBits_eq_true_iff y f
          have hfx := elecFieldBadBits_eq_true_iff x f
          rw [show (⟨f.val / 3, by have := f.isLt; simp only [numElectrons]; omega⟩ :
                Fin numElectrons) = e from Fin.ext (by dsimp [f]; omega),
              show (⟨f.val % 3, by omega⟩ : Fin 3) = w
                from Fin.ext (by dsimp [f]; omega)] at hfy hfx
          rw [elecAxisWord6_val_eq_32_iff_signMagnitude, elecAxisWord6_val_eq_32_iff_signMagnitude,
            ← hfy, ← hfx, hf_eq]
        have hxbad : e ∈ Finset.univ.filter fun j : Fin numElectrons ↦
            decide ((elecAxisWord6 x j 0).val = 32 ∨ (elecAxisWord6 x j 1).val = 32 ∨
                    (elecAxisWord6 x j 2).val = 32) := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff,
            ← h32 0, ← h32 1, ← h32 2] using he
        have hxpos : 0 < badElecCount x := Finset.card_pos.mpr ⟨e, hxbad⟩
        omega
      have hy3 : krylov3Bool y = true := decide_eq_true (le_trans (Finset.card_le_card hsub) hS)
      rw [ite_eq_left_of_eq_true _ _ (eq_true hy3), one_mul]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hb0), mul_zero, mul_zero]
theorem sysMapsZeroBadToKrylov3_conj_elecSysProd_diag_le3
    (V : Fin numElectrons → Unitary (2 ^ 18)) {S : Finset (Fin numElectrons)}
    (hS : S.card ≤ 3) (d : Fin (2 ^ systemQubits) → ℂ) (hd : ∀ z₁ z₂ : Fin (2 ^ systemQubits),
    (∀ s ∈ S, (rEl_sp s).extractIndex z₁ = (rEl_sp s).extractIndex z₂) → d z₁ = d z₂) :
    SysMapsZeroBadToKrylov3 ((elecSysProd V).1ᴴ * Matrix.diagonal d * (elecSysProd V).1) := by
  let V_compl : Unitary (2 ^ systemQubits) :=
    (List.ofFn fun e : Fin numElectrons ↦ (rEl_sp e).embedUnitary (if e ∈ S then 1 else V e)).prod
  let V_S : Unitary (2 ^ systemQubits) :=
    (List.ofFn fun e : Fin numElectrons ↦ (rEl_sp e).embedUnitary (if e ∈ S then V e else 1)).prod
  have hfn : (fun e : Fin numElectrons ↦ (rEl_sp e).embedUnitary ((if e ∈ S then (1 : Unitary
      (2 ^ 18)) else V e) * (if e ∈ S then V e else 1))) =
      fun e ↦ (rEl_sp e).embedUnitary (V e) :=
    funext fun e ↦ by by_cases he : e ∈ S <;> simp [he]
  have hprod : V_compl * V_S = elecSysProd V := by
    dsimp only [V_compl, V_S, elecSysProd]
    rw [list_ofFn_embedUnitary_prod_mul rEl_sp (fun _ _ h ↦ rEl_disjoint_of_ne_sp h), hfn]
  have hcomm_compl : V_compl.1ᴴ * Matrix.diagonal d * V_compl.1 = Matrix.diagonal d := by
    refine list_prod_conj_comm_of_mem _ _ fun U hU ↦ ?_
    rcases List.mem_ofFn.mp hU with ⟨e, rfl⟩
    by_cases he : e ∈ S
    · rw [ite_eq_left_of_eq_true _ _ (eq_true he), QRegister.embedUnitary_one, OneMemClass.coe_one,
        Matrix.one_mul, Matrix.mul_one]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false he), QRegister.embedUnitary_val]
      refine (diagonal_comm_embedMatrix_of_agreeOutside (rEl_sp e) d (fun z' z hag ↦
        hd z' z ?_) (V e).1).symm
      intro s hs; apply (basisBitsEquiv 18).injective; funext j
      change basisBits 18 _ j = basisBits 18 _ j
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      have hdisj : (rEl_sp e).DisjointWires (rEl_sp s) :=
        rEl_disjoint_of_ne_sp (by intro hEq; rw [hEq] at he; exact he hs)
      exact hag (rEl_sp s j) fun ⟨k, hk⟩ ↦ (QRegister.disjoint_iff.mp hdisj) k j hk
  have hpres_VS : PreservesFeature (outsideElecFeature S) V_S.1 := by
    suffices ∀ L : List (Unitary (2 ^ systemQubits)),
        (∀ U ∈ L, PreservesFeature (outsideElecFeature S) U.1) →
        PreservesFeature (outsideElecFeature S) L.prod.1 from
      this _ fun U hU ↦ by
        rcases List.mem_ofFn.mp hU with ⟨e, rfl⟩
        by_cases he : e ∈ S
        · rw [ite_eq_left_of_eq_true _ _ (eq_true he), QRegister.embedUnitary_val]
          exact preservesFeature_outsideElec_embed_mem he (V e).1
        · rw [ite_eq_right_of_eq_false _ _ (eq_false he), QRegister.embedUnitary_one,
          OneMemClass.coe_one]
          exact PreservesFeature.one (outsideElecFeature S)
    intro L hL; induction L with
    | nil =>
        rw [List.prod_nil, OneMemClass.coe_one]
        exact PreservesFeature.one (outsideElecFeature S)
    | cons U tail ih =>
        rw [List.prod_cons, Submonoid.coe_mul]
        exact (hL U List.mem_cons_self).mul (ih fun W hW ↦ hL W (List.mem_cons_of_mem U hW))
  have heq : (elecSysProd V).1ᴴ * Matrix.diagonal d * (elecSysProd V).1 =
      V_S.1ᴴ * Matrix.diagonal d * V_S.1 := by
    rw [← hprod, Submonoid.coe_mul, Matrix.conjTranspose_mul,
      show (V_S.1ᴴ * V_compl.1ᴴ) * Matrix.diagonal d * (V_compl.1 * V_S.1) =
        V_S.1ᴴ * (V_compl.1ᴴ * Matrix.diagonal d * V_compl.1) * V_S.1 by
          simp only [Matrix.mul_assoc],
      hcomm_compl]
  rw [heq]
  exact sysMapsZeroBadToKrylov3_of_preserves_outsideElec hS
    ((hpres_VS.conjTranspose.mul (PreservesFeature.diagonal (outsideElecFeature S) d)).mul hpres_VS)
-- Section 3: `uXThCore` & `uPosPhase80Mod4Eff` Ket Decomposition
theorem preservesCoreBadElec_uXThCore : PreservesCoreBadElec (mPayload := 80) uXThCore.1 := by
  have hPoly : ∀ {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool) (c : Fin (2 ^ n)),
      basisBits n (permThClean wTh d c) = flipThClean wTh d (basisBits n c) := by
    intro n wTh d c
    change (basisBitsEquiv n) ((basisBitsEquiv n).symm (flipThClean wTh d (basisBits n c))) = _
    exact (basisBitsEquiv n).apply_symm_apply _
  refine preservesCoreBadElec_of_fixesLow3924 h3924_core ?_
  unfold uXThCore
  refine preservesFeature_permutationUnitary _ _ fun x ↦ funext fun q ↦ ?_
  change basisBits posCoreWires (permThClean wThCore (fun _ ↦ true) x) ⟨q.val, _⟩ =
    basisBits posCoreWires x ⟨q.val, _⟩
  rw [congrFun (hPoly wThCore (fun _ ↦ true) x) _]
  unfold flipThClean flipTh
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  exact Function.update_of_ne (fun h ↦ by
    have hv := congrArg Fin.val h
    have := q.isLt
    change q.val = 3985 at hv
    omega) _ _

theorem ket_uPosPhase80Mod4Eff (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (β : BitAssignment (fullSysCoreWires 80)) :
    (uPosPhase80Mod4Eff tailSign tailMag30).1.mulVec (ket β) =
      (omega8 ^ (posPhaseMod4Z8Spec true tailSign tailMag30 (swapCore3967Fn β)).val) •
        (if headEnBoolSpec (swapCore3967Fn β) then uXThCore.1.mulVec (ket β) else ket β) := by
  change (uSwapCore3967.1 * (uPosPhaseMod4 true tailSign tailMag30).1 *
    uSwapCore3967.1).mulVec (ket β) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uSwapCore3967_mulVec_ket,
    uPosPhaseMod4, ket_monomialZ8_ket, Matrix.mulVec_smul, uSwapCore3967_mulVec_ket]
  congr 1; unfold flipThClean flipTh; rw [headEnBoolSpec_update_wHeadThresh]
  by_cases hen : headEnBoolSpec (swapCore3967Fn β) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hen), ite_eq_left_of_eq_true _ _ (eq_true hen),
    mbh_ket_uXThCore]
    congr 1; funext q
    rw [swapCore3967Fn_eq_swapCoreScrGenFn12, swapCore3967Fn_eq_swapCoreScrGenFn12]
    let sPerm := Equiv.swap (mWCore3967Gen (le_rfl : 80 ≤ 80))
      (mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩)
    have hTh : sPerm wThCore = wThCore := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    change Function.update (fun w ↦ β (sPerm w)) wThCore (β (sPerm wThCore) + 1) (sPerm q) =
      Function.update β wThCore (β wThCore + 1) q
    rw [hTh]
    by_cases hq : q = wThCore
    · subst hq; rw [hTh, Function.update_self, Function.update_self]
    · have hsq : sPerm q ≠ wThCore := fun h ↦ hq (by
        have h2 := congrArg sPerm h; rwa [Equiv.swap_apply_self, hTh] at h2)
      rw [Function.update_of_ne hsq, Function.update_of_ne hq]
      exact congrArg β (Equiv.swap_apply_self _ _ q)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hen), ite_eq_right_of_eq_false _ _ (eq_false hen),
    swapCore3967Fn_involutive]
end PosFermKrylovTail
end
end PosFermKrylovTail

noncomputable section PosFermKrylovHead

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 5000
namespace PosFermKrylovHead
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowK5 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator Matrix Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz128 (NyqParity3D anchorSubTarget1D)
open SpecsAux.BridgeFermionicComm.SpecInner (permElectron permElectronWire permElectronWireFun
  basisBits_permElectron)
open DyadicQft64 (dyadicTurn dyadicTurn_zero dyadicTurn_add dyadicDiagUnitary)
open Dyadic128CoulombMath (orbitCount47905)
open MeasureBranchHadamardSem (ket)
open ZeroAncillaUSP (omega8 omega8_pow_four)
open PosMomSelectDynamic (unitaryConj_val embedMatrix_diagonal)
open PosMomSelectSandwich (slotBitProj)
open FullSysCatSegmentBridge (fullSysCoreWires coreElecBlock coreCosetB1Block coreElecCosetB1Block
  iSlot1 iSlot2 FullSysQft654Bundle FullSysSelectOracleBundle fullSysQftCoreUnitary
  fullSysSelectPosUnitary)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open InterWalkRSum42Hoist (qreg_block_apply FixesLow3924 IsHigh3924Reg fixesLow3924_embedMatrix_high
  h3924_core)
open SingleAnchorFermionicPauliCap (nSub_sp rEl_disjoint_of_ne_sp rEl_sp rk1_sp)
open TwosCompAndWire0Cancel (fwdPermUnitary fwdPermUnitary_apply)
open DyadicQft64WalkCircuit (rElec18In654 rCoset3In654 nyqParity3DEquivFin8 qft64OffsetUnitary3D
  qft64Ideal654Unitary qft64Ideal654Unitary_comm_cosetProj
  qft64Ideal654Unitary_mul_cosetProj_eq_elec3DProd)
open DyadicQft64WalkCircuit288 (qft64Ideal654Unitary_eq_core_mul_preDiag)
open FusedPreDiagFromTwist288 (hm6_of_hm22 uPre654)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128
  coreQftHadamardPrunedBundle128_uQft654)
open NuclearTwistAndXor654Concrete (rElecSlotAxis wSlot0 wSlot1 wSlot2)
open NuclearTwistRealizes (xor32BitFn xor32CorePerm uXor32Core slot4TotalPhaseExp uSlot4KickCore
  coin0Active slot2M48Val slot2AxisSum)
open ProjZ512QftAndTwist288 (rProjAxis ctrl7Active vepHighNuc vepProj9CoreIdx vepOnlyM48Val
  vepSlot2TotalPhaseExp uVepSlot2KickCore permutationUnitary_entry)
open JunctionProj3DCutPos24BridgeGen (uProj3DCut1DCore uProj3DCutCore uVepTwistRestCut
  uVepFusedTwistRestCut uProjAxes3D rProjAxis_wire_bounds wCutAxes wCutAxes_eq_of_high_eq
  uProj3DCut1DCore_mulVec_ket uProj3DCutCore_mulVec_ket)
open CoinDispatchedBarrel288 (coinBarrelIdxFast coinBarrelBitFnFast coinBarrelBitFnFast_high
  coinBarrelPermFast uBarrelFast uBarrelFast_conjTranspose)
open PosSlots24BranchConcrete (posCoreWires rElecSlot wSlot0Core wSlot1Core wSlot2Core rPartnerIdx
  wIsHead wHeadThresh rHeadFine21 rTailKeep30 wSubReject wRejectZero axisBitRev6 slotSubGridCoord64
  parity3OfReg tailAndSlackPhaseBitSpec)
open PosSlots24SemanticBridge (pos24_6_le_80 pos24_22_le_80)
open PosSlots24SemanticOracleConcrete80 (basisOutcomeProjector_compose_local diag_mul_diag_eq
  diagonal_comm_diagonal rAncFlag80 rAncRest83 coreElecCosetB1_compose_rCoset3
  coreElecCosetB1_disjoint_rAncRest83 rAncFlag80_basisOutcomeProjector_factor coreBetaOf
  coreBetaOf_lt3948 lt_sys_4034 regVal_eq_of_wire_eq)
open PosSlots24Semantic80Physics (coreElecCosetB1_wire_lt_3957)
open MergedVepCoreSliceClosureGen (matrix_ext_of_ket_core msc_ket_eq_single msc_diagonal_mulVec_ket
  msc_mul2_comm)
open PosSlots24MergedVepBound (rProj24_sp elecFermionicProjector
  elecFermionicProjector_mul_fermionicProjector)
open Pos24Slot2FermionicBridge (slotCoord18Equiv slotCoordSys list_prod_comm_of_mem
  list_ofFn_prod_conj_rEl diag_slotCoordSys_eq_embed embedMatrix_list_ofFn_prod
  list_ofFn_rEl_prod_mul xor32SysPerm basisBits_xor32SysPerm embedRegPerm
  embedUnitary_fwdPermUnitary_slot2 list_map_fwdPermUnitary_prod
  diagonal_comm_embedMatrix_of_agreeOutside slotSubGridCoord64_coreBetaOf_slot2_eq)
open PosPostPrep80MergedVep (swapCore3967Fn)
open MergedVepLeaf4GridPerturbation (swapCore3967Fn_eq_swapCoreScrGenFn12)
open MergedVepTopCoinCollapse (mWCore3967Gen mWCoreScrGen)
open PosHeadMod4_15476 (permThClean embedUnitary_permThClean headEnBoolSpec headHitSetSpec
  headPhaseMod4Z8Spec posPhaseMod4Z8Spec)
open PosS3Bounds (wThCore uXThCore uXThCore_sa)
open Leaf2PosMod4WidthCore (uPosPhase80Mod4Eff)
open SelectStitch (Leaf2SpecOfTrunc SelectOraHypothesisOfTrunc)
open SelAndPertStitch (uVepFusedTwistRestCut80_eq_bridge)
open MomSelectKrylov (rSysInFullSysCore PreservesCoreBadElec preservesCoreBadElec_of_fixesLow3924
  low3924Bits_extractIndex_coinBarrelPermFast_eq_permElectron preservesCoreBadElec_uBarrelFast)
open PosFermKrylovTail
theorem basisBits_symm_apply {K : ℕ} (f : BitAssignment K) (q : Wire K) :
    basisBits K ((basisBitsEquiv K).symm f) q = f q := by
  change (basisBitsEquiv K) ((basisBitsEquiv K).symm f) q = f q
  exact congrFun ((basisBitsEquiv K).apply_symm_apply f) q
theorem basisBitsEquiv_symm_basisBits {K : ℕ} (x : Fin (2 ^ K)) :
    (basisBitsEquiv K).symm (basisBits K x) = x := by
  change (basisBitsEquiv K).symm ((basisBitsEquiv K) x) = x
  exact (basisBitsEquiv K).symm_apply_apply x
theorem matrix_finset_sum_apply {ι m n α : Type*} [AddCommMonoid α] (s : Finset ι)
    (f : ι → Matrix m n α) (i : m) (j : n) : (∑ a ∈ s, f a) i j = ∑ a ∈ s, f a i j := by
  induction s using Finset.cons_induction with
  | empty => simp [Matrix.zero_apply]
  | cons a t _ ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_apply, ih]
def rProjAnc110 : QRegister 110 (fullSysCoreWires 80) := QRegister.block 3924 110 (by decide)
def proj24Of110 (s110 : Fin (2 ^ 110)) : Fin (2 ^ 24) :=
  (QRegister.block 0 24 (by decide)).extractIndex s110
def anc86Of110 (s110 : Fin (2 ^ 110)) : Fin (2 ^ 86) :=
  (QRegister.block 24 86 (by decide)).extractIndex s110
theorem rProjAnc110_basisOutcomeProjector_factor (s110 : Fin (2 ^ 110)) :
    rProjAnc110.basisOutcomeProjector s110 =
      (rSysInFullSysCore 80).embedMatrix (rProj24_sp.basisOutcomeProjector (proj24Of110 s110)) *
        rAncFlag80.basisOutcomeProjector (anc86Of110 s110) := by
  rw[← basisOutcomeProjector_compose_local, QRegister.basisOutcomeProjector_eq_diagonal,
      QRegister.basisOutcomeProjector_eq_diagonal,
      QRegister.basisOutcomeProjector_eq_diagonal]
  refine diag_mul_diag_eq (fun x ↦ ((rSysInFullSysCore 80).compose rProj24_sp).extractIndex x
    = proj24Of110 s110) (fun x ↦ rAncFlag80.extractIndex x = anc86Of110 s110)
    (fun x ↦ rProjAnc110.extractIndex x = s110) fun x ↦ ⟨fun hx ↦ ?_, fun ⟨h24, h86⟩ ↦ ?_⟩
  · subst hx
    refine ⟨(basisBitsEquiv 24).injective (funext fun i ↦ ?_),
      (basisBitsEquiv 86).injective (funext fun j ↦ ?_)⟩
    · change basisBits 24 _ i = basisBits 24 _ i
      unfold proj24Of110
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        QRegister.basisBits_extractIndex]
      exact congrArg (basisBits _ x) (Fin.ext (by
        have := i.isLt
        simp only [QRegister.compose_apply, rSysInFullSysCore, rProj24_sp, rProjAnc110,
          qreg_block_apply]; omega))
    · change basisBits 86 _ j = basisBits 86 _ j
      unfold anc86Of110
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        QRegister.basisBits_extractIndex]
      exact congrArg (basisBits _ x) (Fin.ext (by
        have := j.isLt
        simp only [rAncFlag80, rProjAnc110, qreg_block_apply]; omega))
  · apply (basisBitsEquiv 110).injective; funext k
    change basisBits 110 (rProjAnc110.extractIndex x) k = basisBits 110 s110 k
    rw [QRegister.basisBits_extractIndex]
    by_cases hk : k.val < 24
    · have hb := congrFun (congrArg (basisBits 24) h24) ⟨k.val, hk⟩
      unfold proj24Of110 at hb
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex] at hb
      refine (congrArg (basisBits _ x) (Fin.ext ?_)).trans
        (hb.trans (congrArg (basisBits 110 s110) (Fin.ext ?_)))
      · simp only [QRegister.compose_apply, rProjAnc110, rSysInFullSysCore, rProj24_sp,
          qreg_block_apply]; omega
      · simp only [qreg_block_apply]; omega
    · have hk86 : k.val - 24 < 86 := by have := k.isLt; omega
      have hb := congrFun (congrArg (basisBits 86) h86) ⟨k.val - 24, hk86⟩
      unfold anc86Of110 at hb
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex] at hb
      refine (congrArg (basisBits _ x) (Fin.ext ?_)).trans
        (hb.trans (congrArg (basisBits 110 s110) (Fin.ext ?_)))
      · simp only [rProjAnc110, rAncFlag80, qreg_block_apply]; omega
      · simp only [qreg_block_apply]; omega
theorem rSysInFullSysCore80_disjoint_rAncFlag80 :
    (rSysInFullSysCore 80).DisjointWires rAncFlag80 := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  have := i.isLt; have := j.isLt
  simp only [rSysInFullSysCore, rAncFlag80, qreg_block_apply,
    systemQubits, numElectrons, electronBits, projectileBits] at hv ⊢
  omega
theorem swappedElecFermProj_embed_comm_rProjAnc110 (spinUp : Finset (Fin numElectrons))
    (e : Fin numElectrons) (s110 : Fin (2 ^ 110)) : (rSysInFullSysCore 80).embedMatrix
    (swappedElecFermProj spinUp (Equiv.swap 0 e)) * rProjAnc110.basisOutcomeProjector s110 =
    rProjAnc110.basisOutcomeProjector s110 * (rSysInFullSysCore 80).embedMatrix
    (swappedElecFermProj spinUp (Equiv.swap 0 e)) := by
  rw [rProjAnc110_basisOutcomeProjector_factor]
  have hc1 : (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 e)) *
      (rSysInFullSysCore 80).embedMatrix (rProj24_sp.basisOutcomeProjector (proj24Of110 s110)) =
      (rSysInFullSysCore 80).embedMatrix (rProj24_sp.basisOutcomeProjector (proj24Of110 s110)) *
        (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 e)) := by
    rw [← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul,
      QRegister.basisOutcomeProjector, swappedElecFermProj_swap0_comm_rProj24]
  have hc2 : (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 e)) *
      rAncFlag80.basisOutcomeProjector (anc86Of110 s110) =
      rAncFlag80.basisOutcomeProjector (anc86Of110 s110) *
        (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 e)) :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      (rSysInFullSysCore 80) rAncFlag80 rSysInFullSysCore80_disjoint_rAncFlag80 _ _
  exact (msc_mul2_comm _ _ _ hc1.symm hc2.symm).symm
noncomputable def liftSys110 (s110 : Fin (2 ^ 110)) (z : Fin (2 ^ systemQubits)) :
    Fin (2 ^ (fullSysCoreWires 80)) :=
  (basisBitsEquiv (fullSysCoreWires 80)).symm fun q ↦
    if h : q.val < 3924 then
      basisBits systemQubits z ⟨q.val, by
        dsimp [systemQubits, numElectrons, electronBits, projectileBits]; omega⟩
    else
      basisBits 110 s110 ⟨q.val - 3924, by
        have := q.isLt
        dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits] at this
        omega⟩
theorem basisBits_liftSys110_lt3924 (s110 : Fin (2 ^ 110)) (z : Fin (2 ^ systemQubits))
    (q : Wire (fullSysCoreWires 80)) (hq : q.val < 3924) :
    basisBits (fullSysCoreWires 80) (liftSys110 s110 z) q =
      basisBits systemQubits z ⟨q.val, by
        dsimp [systemQubits, numElectrons, electronBits, projectileBits]; omega⟩ := by
  unfold liftSys110
  rw [basisBits_symm_apply, dite_eq_left_of_eq_true (eq_true hq)]
theorem basisBits_liftSys110_ge3924 (s110 : Fin (2 ^ 110)) (z : Fin (2 ^ systemQubits))
    (q : Wire (fullSysCoreWires 80)) (hq : 3924 ≤ q.val) :
    basisBits (fullSysCoreWires 80) (liftSys110 s110 z) q =
      basisBits 110 s110 ⟨q.val - 3924, by
        have := q.isLt
        dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits] at this
        omega⟩ := by
  unfold liftSys110
  have hn : ¬ q.val < 3924 := by omega
  rw [basisBits_symm_apply, dite_eq_right_of_eq_false (eq_false hn)]
theorem liftSys110_extractIndex_of_rProjAnc110 {x : Fin (2 ^ (fullSysCoreWires 80))}
    {s110 : Fin (2 ^ 110)} (hx : rProjAnc110.extractIndex x = s110) :
    liftSys110 s110 ((rSysInFullSysCore 80).extractIndex x) = x := by
  subst hx
  apply (basisBitsEquiv (fullSysCoreWires 80)).injective; funext q
  change basisBits (fullSysCoreWires 80) _ q = basisBits (fullSysCoreWires 80) x q
  by_cases hq : q.val < 3924
  · rw [basisBits_liftSys110_lt3924 _ _ q hq, QRegister.basisBits_extractIndex]
    exact congrArg (basisBits _ x) (Fin.ext (by
      simp only [rSysInFullSysCore, qreg_block_apply]; omega))
  · rw [basisBits_liftSys110_ge3924 _ _ q (Nat.le_of_not_lt hq), QRegister.basisBits_extractIndex]
    exact congrArg (basisBits _ x) (Fin.ext (by
      simp only [rProjAnc110, qreg_block_apply]; omega))
theorem diagonal_mul_rProjAnc110 (dCore : Fin (2 ^ (fullSysCoreWires 80)) → ℂ)
    (s110 : Fin (2 ^ 110)) : Matrix.diagonal dCore * rProjAnc110.basisOutcomeProjector s110 =
    (rSysInFullSysCore 80).embedMatrix (Matrix.diagonal (fun z ↦ dCore (liftSys110 s110 z)))
    * rProjAnc110.basisOutcomeProjector s110 := by
  rw [embedMatrix_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  by_cases hx : rProjAnc110.extractIndex x = s110
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hx), liftSys110_extractIndex_of_rProjAnc110 hx]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hx), mul_zero, mul_zero]
noncomputable def xor32Perm18 : Equiv.Perm (Fin (2 ^ 18)) :=
  (basisBitsEquiv 18).trans
    (({ toFun := fun f k ↦ if k.val % 6 = 5 then f k + 1 else f k
        invFun := fun f k ↦ if k.val % 6 = 5 then f k + 1 else f k
        left_inv := fun f ↦ funext fun k ↦ by
          dsimp only; by_cases hk : k.val % 6 = 5
          · simp only [hk, ↓reduceIte]; exact (by decide : ∀ b : ZMod 2, b + 1 + 1 = b) (f k)
          · simp only [hk, ↓reduceIte]
        right_inv := fun f ↦ funext fun k ↦ by
          dsimp only; by_cases hk : k.val % 6 = 5
          · simp only [hk, ↓reduceIte]; exact (by decide : ∀ b : ZMod 2, b + 1 + 1 = b) (f k)
          · simp only [hk, ↓reduceIte] } :
        Equiv.Perm (BitAssignment 18)).trans (basisBitsEquiv 18).symm)
noncomputable def xor32Unitary18 : Unitary (2 ^ 18) := fwdPermUnitary xor32Perm18
noncomputable def foldXor32Perm : List (Fin numElectrons) → Equiv.Perm (Fin (2 ^ systemQubits))
  | [] => Equiv.refl _
  | e :: tail => (foldXor32Perm tail).trans (embedRegPerm (rEl_sp e) xor32Perm18)
theorem elecSysProd_xor32Unitary18_eq :
    elecSysProd (fun _ ↦ xor32Unitary18) = fwdPermUnitary xor32SysPerm := by
  have hfold : ∀ (L : List (Fin numElectrons)), L.Nodup → ∀ u : Fin (2 ^ systemQubits), (∀ e ∈
      L, (rEl_sp e).extractIndex (foldXor32Perm L u) = xor32Perm18 ((rEl_sp e).extractIndex
      u)) ∧ (∀ q : Wire systemQubits, (∀ e ∈ L, q ∉ Set.range (rEl_sp e).wires) → basisBits
      systemQubits (foldXor32Perm L u) q = basisBits systemQubits u q) := by
    intro L hnd
    induction L with
    | nil => exact fun _ ↦ ⟨fun _ h ↦ False.elim (List.not_mem_nil h), fun _ _ ↦ rfl⟩
    | cons e tail ih =>
        rw [List.nodup_cons] at hnd
        rcases hnd with ⟨hnotmem, hnd_t⟩
        intro u
        rcases ih hnd_t u with ⟨ih_ext, ih_out⟩
        set v := foldXor32Perm tail u
        change (∀ e' ∈ e :: tail,
          (rEl_sp e').extractIndex (embedRegPerm (rEl_sp e) xor32Perm18 v) = _) ∧
          (∀ q, _ → basisBits systemQubits (embedRegPerm (rEl_sp e) xor32Perm18 v) q = _)
        refine ⟨fun e' he' ↦ ?_, fun q hq ↦ ?_⟩
        · rcases List.mem_cons.mp he' with rfl | ht
          · dsimp only [embedRegPerm, Equiv.coe_fn_mk]
            rw [QRegister.extractIndex_replaceIndex]
            apply congrArg xor32Perm18
            apply (basisBitsEquiv 18).injective; funext j
            change basisBits 18 _ j = basisBits 18 _ j
            rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
            exact ih_out (rEl_sp e' j) fun e'' he'' ⟨k, hk⟩ ↦
              (QRegister.disjoint_iff.mp
                (rEl_disjoint_of_ne_sp (fun h ↦ hnotmem (by rw [← h]; exact he'')))) k j hk
          · have hee : e' ≠ e := fun h ↦ hnotmem (by rw [← h]; exact ht)
            have hkeep : (rEl_sp e').extractIndex (embedRegPerm (rEl_sp e) xor32Perm18 v) =
                (rEl_sp e').extractIndex v := by
              apply (basisBitsEquiv 18).injective; funext j
              change basisBits 18 _ j = basisBits 18 _ j
              rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
              exact QRegister.basisBits_replaceIndex_of_not_mem (rEl_sp e) v _ _ fun ⟨k, hk⟩ ↦
                (QRegister.disjoint_iff.mp (rEl_disjoint_of_ne_sp hee)) j k hk.symm
            rw [hkeep, ih_ext e' ht]
        · dsimp only [embedRegPerm, Equiv.coe_fn_mk]
          rw [QRegister.basisBits_replaceIndex_of_not_mem (rEl_sp e) v _ q (hq e
            List.mem_cons_self)]
          exact ih_out q fun e' he' ↦ hq e' (List.mem_cons_of_mem _ he')
  unfold elecSysProd
  rw [List.ofFn_eq_map,
    list_map_fwdPermUnitary_prod
      (fun e : Fin numElectrons ↦ embedRegPerm (rEl_sp e) xor32Perm18)
      (fun e : Fin numElectrons ↦ (rEl_sp e).embedUnitary xor32Unitary18)
      (fun e : Fin numElectrons ↦ embedUnitary_fwdPermUnitary_slot2 (rEl_sp e) xor32Perm18)
      foldXor32Perm rfl (fun _ _ ↦ rfl) (List.finRange numElectrons)]
  refine congrArg fwdPermUnitary ?_
  apply Equiv.ext; intro u
  rcases hfold (List.finRange numElectrons) (List.nodup_finRange numElectrons) u with ⟨hext, hout⟩
  apply (basisBitsEquiv systemQubits).injective; funext q
  change basisBits systemQubits _ q = basisBits systemQubits (xor32SysPerm u) q
  rw [basisBits_xor32SysPerm]
  by_cases hlt : q.val < 3924
  · let e : Fin numElectrons := ⟨q.val / 18, by dsimp [numElectrons]; omega⟩
    let j : Fin 18 := ⟨q.val % 18, Nat.mod_lt _ (by omega)⟩
    have hq_eq : rEl_sp e j = q := Fin.ext (by simp only [rEl_sp, qreg_block_apply, e, j]; omega)
    have h1 := congrFun (congrArg (basisBits 18) (hext e (List.mem_finRange e))) j
    rw [QRegister.basisBits_extractIndex, hq_eq] at h1
    rw [h1]
    have h2 : basisBits 18 (xor32Perm18 ((rEl_sp e).extractIndex u)) j =
        if j.val % 6 = 5 then basisBits 18 ((rEl_sp e).extractIndex u) j + 1
        else basisBits 18 ((rEl_sp e).extractIndex u) j := by
      unfold xor32Perm18
      dsimp only [Equiv.trans_apply, Equiv.coe_fn_mk]
      exact basisBits_symm_apply _ j
    rw [h2, QRegister.basisBits_extractIndex, hq_eq]
    have hmod : (j.val % 6 = 5) ↔ (q.val < 3924 ∧ q.val % 6 = 5) := by
      dsimp [j]; omega
    by_cases hm5 : j.val % 6 = 5
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hm5),
      ite_eq_left_of_eq_true _ _ (eq_true (hmod.mp hm5))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hm5),
      ite_eq_right_of_eq_false _ _ (eq_false (mt hmod.mpr hm5))]
  · have hn : ¬(q.val < 3924 ∧ q.val % 6 = 5) := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
    exact hout q fun e _ ⟨j, hj⟩ ↦ hlt (by
      have hv := congrArg Fin.val hj; have := e.isLt; have := j.isLt
      change e.val < 218 at *; simp only [rEl_sp, qreg_block_apply] at hv; omega)
theorem uXor32Core80_eq_embed_elecSysProd : (uXor32Core 80).1 =
    (rSysInFullSysCore 80).embedMatrix (elecSysProd (fun _ ↦ xor32Unitary18)).1 := by
  rw [elecSysProd_xor32Unitary18_eq, ← QRegister.embedUnitary_val,
    embedUnitary_fwdPermUnitary_slot2]
  have hperm : embedRegPerm (rSysInFullSysCore 80) xor32SysPerm = xor32CorePerm 80 := by
    apply Equiv.ext; intro x
    apply (basisBitsEquiv (fullSysCoreWires 80)).injective; funext q
    change basisBits _ (embedRegPerm (rSysInFullSysCore 80) xor32SysPerm x) q =
      basisBits _ (xor32CorePerm 80 x) q
    have hPoly {mPayload : ℕ} (c : Fin (2 ^ fullSysCoreWires mPayload)) :
        basisBits (fullSysCoreWires mPayload) (xor32CorePerm mPayload c) =
          xor32BitFn mPayload (basisBits (fullSysCoreWires mPayload) c) :=
      (basisBitsEquiv _).apply_symm_apply _
    rw [congrFun (hPoly x) q]; unfold xor32BitFn
    by_cases hsys : q.val < 3948
    · let qSys : Wire systemQubits := ⟨q.val, hsys⟩
      have hmem : rSysInFullSysCore 80 qSys = q :=
        Fin.ext (by simp only [rSysInFullSysCore, qreg_block_apply, qSys]; omega)
      rw [← hmem]
      dsimp only [embedRegPerm, Equiv.coe_fn_mk]
      rw [← QRegister.basisBits_extractIndex, QRegister.extractIndex_replaceIndex,
        basisBits_xor32SysPerm, QRegister.basisBits_extractIndex, hmem]
    · have hnot : q ∉ Set.range (rSysInFullSysCore 80).wires := fun ⟨k, hk⟩ ↦ hsys (by
        have hv := congrArg Fin.val hk; have := k.isLt
        simp only [rSysInFullSysCore, qreg_block_apply,
          systemQubits, numElectrons, electronBits, projectileBits] at hv ⊢; omega)
      dsimp only [embedRegPerm, Equiv.coe_fn_mk]
      rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ q hnot]
      have hn : ¬(q.val < 3924 ∧ q.val % 6 = 5) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
  rw [hperm]; unfold uXor32Core
  exact Matrix.ext fun i j ↦ by rw [permutationUnitary_entry, fwdPermUnitary_apply]
def elec18SlotAxisBitsVal (b : BitAssignment 18) (w : Fin 3) : ℕ :=
  _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 6 ↦
    b ⟨6 * w.val + j.val, by have := w.isLt; have := j.isLt; omega⟩)
theorem regVal_rElecSlotAxis_liftSys110 (s110 : Fin (2 ^ 110)) (z : Fin (2 ^ systemQubits))
    (e : Fin numElectrons) (w : Fin 3) :
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rElecSlotAxis (QRegExt.idReg
      (fullSysCoreWires 80)) e w)
        (basisBits (fullSysCoreWires 80) (liftSys110 s110 z)) =
      elec18SlotAxisBitsVal (basisBits 18 ((rEl_sp e).extractIndex z)) w := by
  unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal elec18SlotAxisBitsVal
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only
  have he218 : e.val < 218 := e.isLt
  have hw3 : w.val < 3 := w.isLt
  have hj6 : j.val < 6 := j.isLt
  have hlt : (rElecSlotAxis (QRegExt.idReg (fullSysCoreWires 80)) e w j).val < 3924 := by
    change 18 * e.val + 6 * w.val + j.val < 3924; omega
  rw [basisBits_liftSys110_lt3924 s110 z _ hlt, QRegister.basisBits_extractIndex]
  refine congrArg (fun x : ZMod 2 ↦
    x.val * 2 ^ j.val) (congrArg (basisBits systemQubits z) (Fin.ext ?_))
  change 18 * e.val + 6 * w.val + j.val = 18 * e.val + (6 * w.val + j.val)
  omega
noncomputable def slot4Exp18 (s110 : Fin (2 ^ 110)) (b : BitAssignment 18) : ℤ :=
  let γ0 := basisBits (fullSysCoreWires 80) (liftSys110 s110 0)
  let rId := QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)
  if γ0 (wSlot2 rId) = 0 ∧ γ0 (wSlot1 rId) = 0 ∧ γ0 (wSlot0 rId) = 1 then
    ∑ w : Fin 3,
      (2 ^ 41 : ℤ) *
        ((((γ0 (NuclearTwistAndXor654Concrete.rCosetB1 pos24_22_le_80 rId w)).val : ℤ) -
          ((γ0 (NuclearTwistAndXor654Concrete.rCosetB0 pos24_22_le_80 rId w)).val : ℤ)) *
          (elec18SlotAxisBitsVal b w : ℤ))
  else 0
noncomputable def uSlot4Elec18 (s110 : Fin (2 ^ 110)) (e : Fin numElectrons) : Unitary (2 ^ 18) :=
  if e = 0 then dyadicDiagUnitary 18 48 (slot4Exp18 s110) else 1
noncomputable def slot2SingleExp18 (c' : Configuration) (s110 : Fin (2 ^ 110))
    (b : BitAssignment 18) : ℤ :=
  let γ0 := basisBits (fullSysCoreWires 80) (liftSys110 s110 0)
  ∑ w : Fin 3,
    (elec18SlotAxisBitsVal b w : ℤ) *
      ((slot2M48Val c' pos24_22_le_80 w γ0 + vepOnlyM48Val pos24_22_le_80 w γ0 : ℕ) : ℤ)
noncomputable def uSlot2Single18 (c' : Configuration) (s110 : Fin (2 ^ 110)) : Unitary (2 ^ 18) :=
  dyadicDiagUnitary 18 48 (slot2SingleExp18 c' s110)
theorem elecSysProd_dyadicDiag18_eq_diagonal (f : Fin numElectrons → BitAssignment 18 → ℤ) :
    (elecSysProd (fun e ↦ dyadicDiagUnitary 18 48 (f e))).1 =
      Matrix.diagonal fun z : Fin (2 ^ systemQubits) ↦
        dyadicTurn 48 (∑ e : Fin numElectrons, f e (basisBits 18 ((rEl_sp e).extractIndex z))) := by
  have hgen : ∀ L : List (Fin numElectrons),
      ((L.map fun e ↦ (rEl_sp e).embedUnitary (dyadicDiagUnitary 18 48 (f e))).prod).1 =
        Matrix.diagonal fun z : Fin (2 ^ systemQubits) ↦
          dyadicTurn 48 ((L.map fun e ↦ f e (basisBits 18 ((rEl_sp e).extractIndex z))).sum) := by
    intro L; induction L with
    | nil => simp [dyadicTurn_zero, Matrix.diagonal_one]
    | cons e tail ih =>
        rw [List.map_cons, List.prod_cons, Submonoid.coe_mul, QRegister.embedUnitary_val, ih]
        change (rEl_sp e).embedMatrix (Matrix.diagonal _) * Matrix.diagonal _ = _
        rw [embedMatrix_diagonal, Matrix.diagonal_mul_diagonal]
        refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
        rw [List.map_cons, List.sum_cons, dyadicTurn_add]
  unfold elecSysProd
  rw [List.ofFn_eq_map, hgen (List.finRange numElectrons)]
  refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
  rw [Fin.sum_univ_def]
theorem uSlot4KickCore_mul_rProjAnc110 (s110 : Fin (2 ^ 110)) :
    (uSlot4KickCore pos24_22_le_80).1 * rProjAnc110.basisOutcomeProjector s110 =
      (rSysInFullSysCore 80).embedMatrix (elecSysProd (uSlot4Elec18 s110)).1 *
        rProjAnc110.basisOutcomeProjector s110 := by
  have heq18 : uSlot4Elec18 s110 =
      fun e ↦ dyadicDiagUnitary 18 48 (fun b ↦ if e = 0 then slot4Exp18 s110 b else 0) := by
    funext e; unfold uSlot4Elec18; by_cases he : e = 0
    · simp [he]
    · simp only [he, ↓reduceIte]; apply Subtype.ext
      change (1 : Operator (2 ^ 18)) = Matrix.diagonal fun _ ↦ dyadicTurn 48 0
      simp [dyadicTurn_zero, Matrix.diagonal_one]
  change Matrix.diagonal _ * rProjAnc110.basisOutcomeProjector s110 = _
  rw [diagonal_mul_rProjAnc110, heq18, elecSysProd_dyadicDiag18_eq_diagonal]
  refine congrArg (fun d ↦ (rSysInFullSysCore 80).embedMatrix (Matrix.diagonal d) *
      rProjAnc110.basisOutcomeProjector s110) (funext fun z ↦ ?_)
  rw [Finset.sum_ite_eq' Finset.univ (0 : Fin numElectrons), ite_eq_left (Finset.mem_univ _)]
  refine congrArg (dyadicTurn 48) ?_
  let γz := basisBits (fullSysCoreWires 80) (liftSys110 s110 z)
  let γ0 := basisBits (fullSysCoreWires 80) (liftSys110 s110 0)
  have hhi (q : Wire (fullSysCoreWires 80)) (hq : 3924 ≤ q.val) : γz q = γ0 q := by
    dsimp [γz, γ0]; rw [basisBits_liftSys110_ge3924 _ _ q hq, basisBits_liftSys110_ge3924 _ _ q hq]
  let rId := QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)
  have hs2 := hhi (wSlot2 rId) (by decide)
  have hs1 := hhi (wSlot1 rId) (by decide)
  have hs0 := hhi (wSlot0 rId) (by decide)
  have hb1 (w : Fin 3) : γz (NuclearTwistAndXor654Concrete.rCosetB1 pos24_22_le_80 rId w) =
      γ0 (NuclearTwistAndXor654Concrete.rCosetB1 pos24_22_le_80 rId w) :=
    hhi _ (by have := w.isLt; change 3924 ≤ 3954 + w.val; omega)
  have hb0 (w : Fin 3) : γz (NuclearTwistAndXor654Concrete.rCosetB0 pos24_22_le_80 rId w) =
      γ0 (NuclearTwistAndXor654Concrete.rCosetB0 pos24_22_le_80 rId w) :=
    hhi _ (by have := w.isLt; change 3924 ≤ 3957 + w.val; omega)
  have hel := regVal_rElecSlotAxis_liftSys110 s110 z 0
  unfold slot4TotalPhaseExp slot4Exp18
  dsimp only [γz, γ0, rId] at hs2 hs1 hs0 hb1 hb0 hel ⊢
  simp only [hs2, hs1, hs0, hb1, hb0, hel]
theorem slot2M48_and_vepOnlyM48_congr {c' : Configuration} {w : Fin 3}
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (hh : ∀ q : Wire (fullSysCoreWires 80), 3924 ≤ q.val ∧ q.val < 3968 → γ₁ q = γ₂ q) :
    slot2M48Val c' pos24_22_le_80 w γ₁ = slot2M48Val c' pos24_22_le_80 w γ₂ ∧
      vepOnlyM48Val pos24_22_le_80 w γ₁ = vepOnlyM48Val pos24_22_le_80 w γ₂ := by
  let rId := QRegExt.idReg (fullSysCoreWires 80)
  have hc0 : coin0Active γ₁ = coin0Active γ₂ := by
    unfold coin0Active
    rw [hh (wSlot2 rId) (by decide), hh (wSlot1 rId) (by decide), hh (wSlot0 rId) (by decide)]
  have hrN_w : ∀ k : Fin 8, γ₁ (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80 rId k) =
      γ₂ (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80 rId k) :=
    fun k ↦ hh _ (by have := k.isLt; change 3924 ≤ 3960 + k.val ∧ 3960 + k.val < 3968; omega)
  have hrN : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80 rId) γ₁ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
        (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80 rId) γ₂ :=
    regVal_eq_of_wire_eq _ γ₁ γ₂ hrN_w
  have hvep : vepHighNuc pos24_22_le_80 γ₁ = vepHighNuc pos24_22_le_80 γ₂ := by
    have hrN_tw : ∀ k : Fin 8, γ₁ (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80
        (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires
        80)) k) = γ₂ (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80
        (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires
        80)) k) := hrN_w
    unfold vepHighNuc ctrl7Active; dsimp only; simp only [hc0, hrN_tw]
  have hv9 : (fun j : Fin 9 ↦ γ₁ (vepProj9CoreIdx pos24_22_le_80 w j)) =
      fun j : Fin 9 ↦ γ₂ (vepProj9CoreIdx pos24_22_le_80 w j) := funext fun j ↦ by
    unfold vepProj9CoreIdx; by_cases hj0 : j.val = 0
    · rw [dite_eq_left_of_eq_true (eq_true hj0)]
      exact hh _ (by have := w.isLt; change 3924 ≤ 3957 + w.val ∧ 3957 + w.val < 3968; omega)
    · rw [dite_eq_right_of_eq_false (eq_false hj0)]
      have hb := rProjAxis_wire_bounds (mPayload := 80) w ⟨j.val - 1, by have := j.isLt; omega⟩
      exact hh _ ⟨hb.1, lt_trans hb.2 (by decide)⟩
  refine ⟨?_, by unfold vepOnlyM48Val; rw [hvep, hv9]⟩
  unfold slot2M48Val
  by_cases h1 : coin0Active γ₁ = true ∧
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
        (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80 rId) γ₁ < 216
  · rw [dite_eq_left_of_eq_true (eq_true h1),
      dite_eq_left_of_eq_true (eq_true (by rwa [← hc0, ← hrN]))]
    exact congrArg
      (fun idx ↦ NuclearTwistAndXor654Concrete.nuclearM48 c' idx w)
      (Fin.ext hrN)
  · rw [dite_eq_right_of_eq_false (eq_false h1),
      dite_eq_right_of_eq_false (eq_false (by rwa [← hc0, ← hrN]))]
theorem uVepSlot2KickCore_mul_rProjAnc110 (c' : Configuration) (s110 : Fin (2 ^ 110)) :
    (uVepSlot2KickCore c' pos24_22_le_80).1 * rProjAnc110.basisOutcomeProjector s110 =
      (rSysInFullSysCore 80).embedMatrix (elecSysProd (fun _ ↦ uSlot2Single18 c' s110)).1 *
        rProjAnc110.basisOutcomeProjector s110 := by
  change Matrix.diagonal _ * rProjAnc110.basisOutcomeProjector s110 = _
  rw [diagonal_mul_rProjAnc110]
  unfold uSlot2Single18
  rw [elecSysProd_dyadicDiag18_eq_diagonal]
  refine congrArg (fun d ↦ (rSysInFullSysCore 80).embedMatrix (Matrix.diagonal d) *
      rProjAnc110.basisOutcomeProjector s110) (funext fun z ↦ congrArg (dyadicTurn 48) ?_)
  let γz := basisBits (fullSysCoreWires 80) (liftSys110 s110 z)
  let γ0 := basisBits (fullSysCoreWires 80) (liftSys110 s110 0)
  have hhi : ∀ q : Wire (fullSysCoreWires 80), 3924 ≤ q.val ∧ q.val < 3968 → γz q = γ0 q :=
    fun q hq ↦ by
      dsimp [γz, γ0];
      rw [basisBits_liftSys110_ge3924 _ _ q hq.1,
        basisBits_liftSys110_ge3924 _ _ q hq.1]
  unfold vepSlot2TotalPhaseExp slot2SingleExp18 slot2AxisSum
  trans (∑ w : Fin 3, ∑ e : Fin numElectrons,
      (elec18SlotAxisBitsVal (basisBits 18 ((rEl_sp e).extractIndex z)) w : ℤ) *
        ((slot2M48Val c' pos24_22_le_80 w γ0 + vepOnlyM48Val pos24_22_le_80 w γ0 : ℕ) : ℤ))
  · refine Finset.sum_congr rfl fun w _ ↦ ?_
    rcases slot2M48_and_vepOnlyM48_congr (c' := c') (w := w) hhi with ⟨hm1, hm2⟩
    change ((∑ e : Fin numElectrons,
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal _ γz : ℕ) : ℤ) *
        ((slot2M48Val c' pos24_22_le_80 w γz + vepOnlyM48Val pos24_22_le_80 w γz : ℕ) : ℤ) = _
    rw [hm1, hm2, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [regVal_rElecSlotAxis_liftSys110 s110 z e w]
  · exact Finset.sum_comm
noncomputable def b1Of110 (s110 : Fin (2 ^ 110)) : NyqParity3D :=
  nyqParity3DEquivFin8.symm (Classical.choose (rAncFlag80_basisOutcomeProjector_factor (anc86Of110
    s110)))
noncomputable def wRem18 (c' : Configuration) (s110 : Fin (2 ^ 110)) : Unitary (2 ^ 18) :=
  qft64OffsetUnitary3D (b1Of110 s110) * (uSlot2Single18 c' s110 * xor32Unitary18)
noncomputable def vRemElec (c' : Configuration) (s110 : Fin (2 ^ 110)) (e : Fin numElectrons)
    : Unitary (2 ^ 18) := qft64OffsetUnitary3D (b1Of110 s110) *
    (uSlot2Single18 c' s110 * (uSlot4Elec18 s110 e * xor32Unitary18))
theorem vRemElec_eq_wRem18_of_ne_zero (c' : Configuration) (s110 : Fin (2 ^ 110))
    {e : Fin numElectrons} (he : e ≠ 0) : vRemElec c' s110 e = wRem18 c' s110 := by
  unfold vRemElec wRem18 uSlot4Elec18
  rw [ite_eq_right_of_eq_false _ _ (eq_false he), one_mul]
noncomputable def uRemCore (qft : FullSysQft654Bundle) (c' : Configuration) :
    Unitary (2 ^ (fullSysCoreWires 80)) :=
  (coreElecCosetB1Block pos24_6_le_80).embedUnitary (qft.uQft654 * uPre654) *
    (uVepSlot2KickCore c' pos24_22_le_80 * (uSlot4KickCore pos24_22_le_80 * uXor32Core 80))
theorem uRemCore_comm_uXThCore (qft : FullSysQft654Bundle) (c' : Configuration) :
    (uRemCore qft c').1 * uXThCore.1 = uXThCore.1 * (uRemCore qft c').1 := by
  have hEmbTh : ((QRegister.singleton wThCore).embedUnitary
      (permutationUnitary (permThClean 0 (fun _ ↦ true)))).1 = uXThCore.1 :=
    congrArg Subtype.val (embedUnitary_permThClean (QRegister.singleton wThCore) 0 (fun _ ↦ true))
  have hQ : ((coreElecCosetB1Block pos24_6_le_80).embedUnitary (qft.uQft654 * uPre654)).1 *
      uXThCore.1 =
      uXThCore.1 * ((coreElecCosetB1Block pos24_6_le_80).embedUnitary (qft.uQft654 * uPre654)).1 :=
        by
    rw [← hEmbTh, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    refine QRegister.embedMatrix_comm_of_disjoint _ _ ?_ _ _
    rw [QRegister.disjoint_iff]; intro i j hij
    have hlt := coreElecCosetB1_wire_lt_3957 i
    have hv : ((QRegister.singleton wThCore) j).val = 3985 := rfl
    have hijv := congrArg Fin.val hij; omega
  have hX : (uXor32Core 80).1 * uXThCore.1 = uXThCore.1 * (uXor32Core 80).1 := by
    rw [uXor32Core80_eq_embed_elecSysProd, ← hEmbTh, QRegister.embedUnitary_val]
    refine QRegister.embedMatrix_comm_of_disjoint _ _ ?_ _ _
    rw [QRegister.disjoint_iff]; intro i j hij
    have := i.isLt
    have hv : ((QRegister.singleton wThCore) j).val = 3985 := rfl
    have hijv := congrArg Fin.val hij
    simp only [rSysInFullSysCore, qreg_block_apply,
      systemQubits, numElectrons, electronBits, projectileBits] at hijv this
    omega
  have hDiag : ∀ (e : BitAssignment (fullSysCoreWires 80) → ℤ),
      (∀ γ₁ γ₂ : BitAssignment (fullSysCoreWires 80),
        (∀ q : Wire (fullSysCoreWires 80), q.val < 3968 → γ₁ q = γ₂ q) → e γ₁ = e γ₂) →
      (dyadicDiagUnitary (fullSysCoreWires 80) 48 e).1 * uXThCore.1 =
        uXThCore.1 * (dyadicDiagUnitary (fullSysCoreWires 80) 48 e).1 := fun e he ↦ by
    rw [← hEmbTh, QRegister.embedUnitary_val]
    refine diagonal_comm_embedMatrix_of_agreeOutside (QRegister.singleton wThCore) _
      (fun x' x hag ↦ congrArg (dyadicTurn 48) (he _ _ fun q hq ↦ hag q fun ⟨j, hj⟩ ↦ ?_)) _
    have hv : ((QRegister.singleton wThCore) j).val = 3985 := rfl
    have hjv := congrArg Fin.val hj; omega
  have hS4 : (uSlot4KickCore pos24_22_le_80).1 * uXThCore.1 =
      uXThCore.1 * (uSlot4KickCore pos24_22_le_80).1 :=
    hDiag _ fun γ₁ γ₂ hlt ↦ by
      let rId := QRegExt.idReg
        (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)
      have hs2 := hlt (wSlot2 rId) (by decide)
      have hs1 := hlt (wSlot1 rId) (by decide)
      have hs0 := hlt (wSlot0 rId) (by decide)
      have hb1 (w : Fin 3) := hlt (NuclearTwistAndXor654Concrete.rCosetB1 pos24_22_le_80 rId w)
        (by have := w.isLt; change 3954 + w.val < 3968; omega)
      have hb0 (w : Fin 3) := hlt (NuclearTwistAndXor654Concrete.rCosetB0 pos24_22_le_80 rId w)
        (by have := w.isLt; change 3957 + w.val < 3968; omega)
      have hel (w : Fin 3) := regVal_eq_of_wire_eq (rElecSlotAxis rId 0 w) γ₁ γ₂ fun j ↦ hlt _
        (by have := w.isLt; have := j.isLt; change 18 * 0 + 6 * w.val + j.val < 3968; omega)
      unfold slot4TotalPhaseExp; dsimp only [rId] at hs2 hs1 hs0 hb1 hb0 hel
      simp only [hs2, hs1, hs0, hb1, hb0, hel]
  have hS2 : (uVepSlot2KickCore c' pos24_22_le_80).1 * uXThCore.1 =
      uXThCore.1 * (uVepSlot2KickCore c' pos24_22_le_80).1 :=
    hDiag _ fun γ₁ γ₂ hlt ↦ by
      unfold vepSlot2TotalPhaseExp slot2AxisSum
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rcases slot2M48_and_vepOnlyM48_congr (c' := c') (w := w)
        (fun q hq ↦ hlt q hq.2) with ⟨hm1, hm2⟩
      have hsum : (∑ e : Fin numElectrons,
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rElecSlotAxis
          (QRegExt.idReg _) e w) γ₁) = ∑ e : Fin numElectrons,
          _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rElecSlotAxis (QRegExt.idReg
            _) e w) γ₂ :=
        Finset.sum_congr rfl fun e _ ↦ regVal_eq_of_wire_eq _ γ₁ γ₂ fun j ↦ hlt _ (by
          have he218 : e.val < 218 := e.isLt; have := w.isLt; have := j.isLt
          change 18 * e.val + 6 * w.val + j.val < 3968; omega)
      rw [hsum, hm1, hm2]
  unfold uRemCore; simp only [Submonoid.coe_mul]
  exact msc_mul2_comm _ _ _ hQ (msc_mul2_comm _ _ _ hS2 (msc_mul2_comm _ _ _ hS4 hX))
theorem uRemCore_conjTranspose_comm_uXThCore (qft : FullSysQft654Bundle) (c' : Configuration) :
    (uRemCore qft c').1ᴴ * uXThCore.1 = uXThCore.1 * (uRemCore qft c').1ᴴ := by
  have h := congrArg (fun M : Operator (2 ^ (fullSysCoreWires 80)) ↦ Mᴴ)
    (uRemCore_comm_uXThCore qft c')
  change ((uRemCore qft c').1 * uXThCore.1)ᴴ = (uXThCore.1 * (uRemCore qft c').1)ᴴ at h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, uXThCore_sa] at h
  exact h.symm
theorem embed_elecSysProd_comm_rProjAnc110 (V : Fin numElectrons → Unitary (2 ^ 18))
    (s110 : Fin (2 ^ 110)) : (rSysInFullSysCore 80).embedMatrix (elecSysProd V).1 *
    rProjAnc110.basisOutcomeProjector s110 = rProjAnc110.basisOutcomeProjector s110 *
    (rSysInFullSysCore 80).embedMatrix (elecSysProd V).1 := by
  unfold elecSysProd
  rw [embedMatrix_list_ofFn_prod]
  refine list_prod_comm_of_mem _ _ fun U hU ↦ ?_
  rcases List.mem_ofFn.mp hU with ⟨e, rfl⟩
  refine QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _ ?_ _ _
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val hij
  have := e.isLt; have := i.isLt
  change e.val < 218 at *
  simp only [QRegister.compose_apply, rSysInFullSysCore, rEl_sp, rProjAnc110,
    qreg_block_apply] at hv
  omega
theorem qftPre_comm_and_mul_rProjAnc110 {qft : FullSysQft654Bundle}
    (hqft : qft.uQft654 * uPre654 = qft64Ideal654Unitary) (s110 : Fin (2 ^ 110)) :
    (((coreElecCosetB1Block pos24_6_le_80).embedUnitary (qft.uQft654 * uPre654)).1 *
    rProjAnc110.basisOutcomeProjector s110 = rProjAnc110.basisOutcomeProjector s110 *
    ((coreElecCosetB1Block pos24_6_le_80).embedUnitary (qft.uQft654 * uPre654)).1) ∧
    (((coreElecCosetB1Block pos24_6_le_80).embedUnitary (qft.uQft654 * uPre654)).1 *
    rProjAnc110.basisOutcomeProjector s110 = (rSysInFullSysCore 80).embedMatrix (elecSysProd
    (fun _ ↦ qft64OffsetUnitary3D (b1Of110 s110))).1 * rProjAnc110.basisOutcomeProjector s110)
    := by
  let o3 := Classical.choose (rAncFlag80_basisOutcomeProjector_factor (anc86Of110 s110))
  rcases Classical.choose_spec (rAncFlag80_basisOutcomeProjector_factor (anc86Of110 s110)) with
    ⟨o83, ho86⟩
  have ho3 : nyqParity3DEquivFin8 (b1Of110 s110) = o3 :=
    nyqParity3DEquivFin8.apply_symm_apply o3
  set P24 := (rSysInFullSysCore 80).embedMatrix
    (rProj24_sp.basisOutcomeProjector (proj24Of110 s110))
  set P3 := (coreCosetB1Block pos24_6_le_80).basisOutcomeProjector o3
  set P83 := rAncRest83.basisOutcomeProjector o83
  set Q := ((coreElecCosetB1Block pos24_6_le_80).embedUnitary (qft.uQft654 * uPre654)).1
  have hQ_P24 : Q * P24 = P24 * Q := by
    dsimp only [Q, P24]
    rw [QRegister.embedUnitary_val, ← basisOutcomeProjector_compose_local]
    refine QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _ ?_ _ _
    rw [QRegister.disjoint_iff]; intro i j hij
    have hv := congrArg Fin.val hij
    refine Fin.addCases (motive := fun idx ↦
      ((coreElecCosetB1Block pos24_6_le_80) idx).val =
        (((rSysInFullSysCore 80).compose rProj24_sp) j).val → False)
      (fun a ha ↦ ?_) (fun b hb ↦ ?_) i hv
    · rw [coreElecCosetB1Block, QRegister.concat_apply_left] at ha
      have := a.isLt; have := j.isLt
      simp only [coreElecBlock, QRegister.compose_apply, rSysInFullSysCore, rProj24_sp,
        qreg_block_apply] at ha; omega
    · rw [coreElecCosetB1Block, QRegister.concat_apply_right] at hb
      have := b.isLt; have := j.isLt
      simp only [coreCosetB1Block, QRegister.compose_apply, rSysInFullSysCore, rProj24_sp,
        qreg_block_apply, systemQubits, numElectrons, electronBits, projectileBits] at hb; omega
  have hQ_P3 : Q * P3 = P3 * Q := by
    dsimp only [Q, P3]
    rw [hqft, QRegister.embedUnitary_val, ← coreElecCosetB1_compose_rCoset3,
      basisOutcomeProjector_compose_local, ← QRegister.embedMatrix_mul,
      ← QRegister.embedMatrix_mul, qft64Ideal654Unitary_comm_cosetProj]
  have hQ_P83 : Q * P83 = P83 * Q :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _
      coreElecCosetB1_disjoint_rAncRest83 _ _
  have hComm : Q * rProjAnc110.basisOutcomeProjector s110 =
      rProjAnc110.basisOutcomeProjector s110 * Q := by
    rw [rProjAnc110_basisOutcomeProjector_factor, ho86]
    change Q * (P24 * (P3 * P83)) = (P24 * (P3 * P83)) * Q
    exact (msc_mul2_comm P24 (P3 * P83) Q hQ_P24.symm
      (msc_mul2_comm P3 P83 Q hQ_P3.symm hQ_P83.symm)).symm
  have hQ_mul_P3 : Q * P3 = (rSysInFullSysCore 80).embedMatrix
      (elecSysProd (fun _ ↦ qft64OffsetUnitary3D (b1Of110 s110))).1 * P3 := by
    have hP3_eq : P3 = (coreElecCosetB1Block pos24_6_le_80).embedMatrix
        (rCoset3In654.basisOutcomeProjector (nyqParity3DEquivFin8 (b1Of110 s110))) := by
      dsimp only [P3]
      rw [← ho3, ← coreElecCosetB1_compose_rCoset3, basisOutcomeProjector_compose_local]
    have hL : Q * P3 = ((List.ofFn fun i : Fin 218 ↦ ((coreElecCosetB1Block
        pos24_6_le_80).compose (rElec18In654 i)).embedUnitary (qft64OffsetUnitary3D (b1Of110
        s110))).prod).1 * P3 := by
      rw [hP3_eq]; dsimp only [Q]
      rw [hqft, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
        qft64Ideal654Unitary_mul_cosetProj_eq_elec3DProd (b1Of110 s110),
        QRegister.embedMatrix_mul, embedMatrix_list_ofFn_prod]
    rw [hL]
    refine congrArg (· * P3) ?_
    unfold elecSysProd
    dsimp only [numElectrons]
    rw [embedMatrix_list_ofFn_prod]
    have hreg (i : Fin 218) : (coreElecCosetB1Block pos24_6_le_80).compose (rElec18In654 i) =
        (rSysInFullSysCore 80).compose (rEl_sp i) := by
      apply QRegister.ext; apply Function.Embedding.ext; intro j
      have hi := i.isLt; have hj := j.isLt
      have hlt : (rElec18In654 i j).val < 3924 := by
        simp only [rElec18In654, qreg_block_apply]; omega
      rw [QRegister.compose_apply, QRegister.compose_apply,
        show rElec18In654 i j = Fin.castAdd 3 ⟨(rElec18In654 i j).val, hlt⟩ from Fin.ext rfl,
        coreElecCosetB1Block, QRegister.concat_apply_left]
      exact Fin.ext (by
        simp only [coreElecBlock, rElec18In654, rSysInFullSysCore, rEl_sp, qreg_block_apply])
    simp only [hreg]
  have hEl_P24 : (rSysInFullSysCore 80).embedMatrix
        (elecSysProd (fun _ ↦ qft64OffsetUnitary3D (b1Of110 s110))).1 * P24 =
      P24 * (rSysInFullSysCore 80).embedMatrix
        (elecSysProd (fun _ ↦ qft64OffsetUnitary3D (b1Of110 s110))).1 := by
    dsimp only [P24, elecSysProd]
    rw [← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
    refine congrArg (rSysInFullSysCore 80).embedMatrix (list_prod_comm_of_mem _ _ fun U hU ↦ ?_)
    rcases List.mem_ofFn.mp hU with ⟨e, rfl⟩
    refine QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _ ?_ _ _
    rw [QRegister.disjoint_iff]; intro a b hab
    have hv := congrArg Fin.val hab; have := e.isLt; have := a.isLt
    change e.val < 218 at *; simp only [rEl_sp, rProj24_sp, qreg_block_apply] at hv; omega
  refine ⟨hComm, ?_⟩
  rw [rProjAnc110_basisOutcomeProjector_factor, ho86]
  change Q * (P24 * (P3 * P83)) = _ * (P24 * (P3 * P83))
  rw [← Matrix.mul_assoc Q P24 (P3 * P83), hQ_P24, Matrix.mul_assoc P24 Q (P3 * P83),
    ← Matrix.mul_assoc Q P3 P83, hQ_mul_P3, ← Matrix.mul_assoc P24 _ P83,
    ← Matrix.mul_assoc P24 _ P3, ← hEl_P24]
  simp only [Matrix.mul_assoc]
theorem uRemCore_comm_and_mul_rProjAnc110 {qft : FullSysQft654Bundle}
    (hqft : qft.uQft654 * uPre654 = qft64Ideal654Unitary) (c' : Configuration)
    (s110 : Fin (2 ^ 110)) : ((uRemCore qft c').1 * rProjAnc110.basisOutcomeProjector s110 =
    rProjAnc110.basisOutcomeProjector s110 * (uRemCore qft c').1) ∧ ((uRemCore qft c').1 *
    rProjAnc110.basisOutcomeProjector s110 = (rSysInFullSysCore 80).embedMatrix (elecSysProd
    (vRemElec c' s110)).1 * rProjAnc110.basisOutcomeProjector s110) := by
  let P := rProjAnc110.basisOutcomeProjector s110
  rcases qftPre_comm_and_mul_rProjAnc110 hqft s110 with ⟨hQ_comm, hQ_mul⟩
  have hS2_comm : (uVepSlot2KickCore c' pos24_22_le_80).1 * P =
      P * (uVepSlot2KickCore c' pos24_22_le_80).1 := by
    dsimp only [P, uVepSlot2KickCore, dyadicDiagUnitary]
    rw [QRegister.basisOutcomeProjector_eq_diagonal]; exact diagonal_comm_diagonal _ _
  have hS4_comm : (uSlot4KickCore pos24_22_le_80).1 * P =
      P * (uSlot4KickCore pos24_22_le_80).1 := by
    dsimp only [P, uSlot4KickCore, dyadicDiagUnitary]
    rw [QRegister.basisOutcomeProjector_eq_diagonal]; exact diagonal_comm_diagonal _ _
  have hX_comm : (uXor32Core 80).1 * P = P * (uXor32Core 80).1 := by
    rw [uXor32Core80_eq_embed_elecSysProd]
    exact embed_elecSysProd_comm_rProjAnc110 _ s110
  have hComm : (uRemCore qft c').1 * P = P * (uRemCore qft c').1 := by
    unfold uRemCore; simp only [Submonoid.coe_mul]
    exact msc_mul2_comm _ _ P hQ_comm
      (msc_mul2_comm _ _ P hS2_comm (msc_mul2_comm _ _ P hS4_comm hX_comm))
  refine ⟨hComm, ?_⟩
  unfold uRemCore; simp only [Submonoid.coe_mul]
  set Q := ((coreElecCosetB1Block pos24_6_le_80).embedUnitary (qft.uQft654 * uPre654)).1
  set S2 := (uVepSlot2KickCore c' pos24_22_le_80).1
  set S4 := (uSlot4KickCore pos24_22_le_80).1
  set EX := (rSysInFullSysCore 80).embedMatrix (elecSysProd (fun _ ↦ xor32Unitary18)).1
  set ES4 := (rSysInFullSysCore 80).embedMatrix (elecSysProd (uSlot4Elec18 s110)).1
  set ES2 := (rSysInFullSysCore 80).embedMatrix (elecSysProd (fun _ ↦ uSlot2Single18 c' s110)).1
  set EQ := (rSysInFullSysCore 80).embedMatrix
    (elecSysProd (fun _ ↦ qft64OffsetUnitary3D (b1Of110 s110))).1
  have hcX : EX * P = P * EX := embed_elecSysProd_comm_rProjAnc110 _ s110
  have hc4 : ES4 * P = P * ES4 := embed_elecSysProd_comm_rProjAnc110 _ s110
  have hc2 : ES2 * P = P * ES2 := embed_elecSysProd_comm_rProjAnc110 _ s110
  have h24X_comm : (ES2 * (ES4 * EX)) * P = P * (ES2 * (ES4 * EX)) :=
    msc_mul2_comm ES2 (ES4 * EX) P hc2 (msc_mul2_comm ES4 EX P hc4 hcX)
  have hProd : EQ * (ES2 * (ES4 * EX)) =
      (rSysInFullSysCore 80).embedMatrix (elecSysProd (vRemElec c' s110)).1 := by
    dsimp only [EQ, ES2, ES4, EX]
    rw [← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
    refine congrArg (rSysInFullSysCore 80).embedMatrix ?_
    change ((elecSysProd (fun _ ↦ qft64OffsetUnitary3D (b1Of110 s110))) *
      ((elecSysProd (fun _ ↦ uSlot2Single18 c' s110)) *
        ((elecSysProd (uSlot4Elec18 s110)) * (elecSysProd (fun _ ↦ xor32Unitary18))))).1 = _
    refine congrArg Subtype.val ?_
    unfold elecSysProd vRemElec
    rw [list_ofFn_rEl_prod_mul, list_ofFn_rEl_prod_mul, list_ofFn_rEl_prod_mul]
  rw [uXor32Core80_eq_embed_elecSysProd]
  change (Q * (S2 * (S4 * EX))) * P = _ * P
  rw [Matrix.mul_assoc Q (S2 * (S4 * EX)) P, Matrix.mul_assoc S2 (S4 * EX) P,
    Matrix.mul_assoc S4 EX P, hcX, ← Matrix.mul_assoc S4 P EX,
    uSlot4KickCore_mul_rProjAnc110, hc4, Matrix.mul_assoc P ES4 EX,
    ← Matrix.mul_assoc S2 P (ES4 * EX), uVepSlot2KickCore_mul_rProjAnc110, hc2,
    Matrix.mul_assoc P ES2 (ES4 * EX), ← Matrix.mul_assoc Q P _, hQ_mul,
    Matrix.mul_assoc EQ P (ES2 * (ES4 * EX)), ← h24X_comm,
    ← Matrix.mul_assoc EQ (ES2 * (ES4 * EX)) P, hProd]
theorem uRemCore_conj_diagonal_mul_rProjAnc110 {qft : FullSysQft654Bundle}
    (hqft : qft.uQft654 * uPre654 = qft64Ideal654Unitary) (c' : Configuration)
    (dCore : Fin (2 ^ (fullSysCoreWires 80)) → ℂ) (s110 : Fin (2 ^ 110)) :
    (uRemCore qft c').1ᴴ * Matrix.diagonal dCore * (uRemCore qft c').1 *
    rProjAnc110.basisOutcomeProjector s110 = (rSysInFullSysCore 80).embedMatrix ((elecSysProd
    (vRemElec c' s110)).1ᴴ * Matrix.diagonal (fun z ↦ dCore (liftSys110 s110 z)) *
    (elecSysProd (vRemElec c' s110)).1) * rProjAnc110.basisOutcomeProjector s110 := by
  let P := rProjAnc110.basisOutcomeProjector s110
  set U := (uRemCore qft c').1
  set E := (elecSysProd (vRemElec c' s110)).1
  set Dsys := Matrix.diagonal (fun z ↦ dCore (liftSys110 s110 z))
  rcases uRemCore_comm_and_mul_rProjAnc110 hqft c' s110 with ⟨hU_comm, hU_mul⟩
  have hE_comm : (rSysInFullSysCore 80).embedMatrix E * P = P *
      (rSysInFullSysCore 80).embedMatrix E := embed_elecSysProd_comm_rProjAnc110 _ s110
  have hPU_eq : P * U = P * (rSysInFullSysCore 80).embedMatrix E := by
    rw [← hU_comm, hU_mul, hE_comm]
  have hUadj_mul : Uᴴ * P = (rSysInFullSysCore 80).embedMatrix Eᴴ * P := by
    have hadj := congrArg (fun M : Operator (2 ^ (fullSysCoreWires 80)) ↦ Mᴴ) hPU_eq
    change (P * U)ᴴ = (P * (rSysInFullSysCore 80).embedMatrix E)ᴴ at hadj
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      QRegister.basisOutcomeProjector_conjTranspose, ← QRegister.embedMatrix_conjTranspose] at hadj
  have hD_comm : (rSysInFullSysCore 80).embedMatrix Dsys * P =
      P * (rSysInFullSysCore 80).embedMatrix Dsys := by
    dsimp only [Dsys, P]
    rw [embedMatrix_diagonal, QRegister.basisOutcomeProjector_eq_diagonal]
    exact diagonal_comm_diagonal _ _
  rw [Matrix.mul_assoc (Uᴴ * Matrix.diagonal dCore) U P, hU_mul, hE_comm,
    ← Matrix.mul_assoc (Uᴴ * Matrix.diagonal dCore) P, Matrix.mul_assoc Uᴴ _ P,
    diagonal_mul_rProjAnc110, hD_comm, ← Matrix.mul_assoc Uᴴ P, hUadj_mul,
    Matrix.mul_assoc ((rSysInFullSysCore 80).embedMatrix Eᴴ) P, ← hD_comm,
    ← Matrix.mul_assoc ((rSysInFullSysCore 80).embedMatrix Eᴴ) _ P,
    Matrix.mul_assoc _ P ((rSysInFullSysCore 80).embedMatrix E), ← hE_comm,
    ← Matrix.mul_assoc _ ((rSysInFullSysCore 80).embedMatrix E) P,
    ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
-- Section 2: Newton Binomial Pauli Cap, `uPosPhase80Mod4Eff`, & `fullSysSelectPosUnitary`
open CanonRank7Circuit (fineCoordOfReg21)
open PosSlots24BranchConcrete (rCosetB1 rCosetB0 rNucIdx rAnchorIdx)
noncomputable def βLift (s110 : Fin (2 ^ 110)) (z : Fin (2 ^ systemQubits)) :
    BitAssignment (fullSysCoreWires 80) :=
  swapCore3967Fn (basisBits (fullSysCoreWires 80) (liftSys110 s110 z))
theorem βLift_high_eq (s110 : Fin (2 ^ 110)) (z₁ z₂ : Fin (2 ^ systemQubits))
    {q : Wire (fullSysCoreWires 80)} (hq : 3924 ≤ q.val) :
    βLift s110 z₁ q = βLift s110 z₂ q := by
  unfold βLift
  rw [swapCore3967Fn_eq_swapCoreScrGenFn12, swapCore3967Fn_eq_swapCoreScrGenFn12]
  let sPerm := Equiv.swap (mWCore3967Gen (le_rfl : 80 ≤ 80))
    (mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩)
  have hsp : 3924 ≤ (sPerm q).val := by
    by_cases h1 : q = mWCore3967Gen (le_rfl : 80 ≤ 80)
    · rw [h1, Equiv.swap_apply_left]; decide
    · by_cases h2 : q = mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩
      · rw [h2, Equiv.swap_apply_right]; decide
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hq
  change basisBits _ (liftSys110 s110 z₁) (sPerm q) = basisBits _ (liftSys110 s110 z₂) (sPerm q)
  rw [basisBits_liftSys110_ge3924 s110 z₁ (sPerm q) hsp,
    basisBits_liftSys110_ge3924 s110 z₂ (sPerm q) hsp]
theorem slotSubGridCoord64_βLift_eq (s110 : Fin (2 ^ 110)) (z : Fin (2 ^ systemQubits))
    (e : Fin numElectrons) :
    slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) (βLift s110 z) =
      slotCoordSys z e := by
  have hcoord : slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) (βLift s110 z) =
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) (coreBetaOf false 0 z) := by
    funext w; apply Fin.ext
    exact regVal_eq_of_wire_eq _ (βLift s110 z) (coreBetaOf false 0 z) fun j ↦ by
      have he218 : e.val < 218 := e.isLt; have hw3 := w.isLt; have hj6 := j.isLt
      let qw : Wire (fullSysCoreWires 80) :=
        axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j
      have hqw : qw.val < 3924 := by
        change 18 * e.val + (6 * w.val + (5 - j.val)) < 3924; omega
      let wsys : Fin systemQubits := ⟨qw.val, by
        dsimp [systemQubits, numElectrons, electronBits, projectileBits]; omega⟩
      have hqweq : qw = ⟨wsys.val, Nat.lt_trans wsys.isLt lt_sys_4034⟩ := Fin.ext rfl
      unfold βLift; rw [swapCore3967Fn_eq_swapCoreScrGenFn12]
      let sPerm := Equiv.swap (mWCore3967Gen (le_rfl : 80 ≤ 80))
        (mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩)
      have hne1 : qw ≠ mWCore3967Gen (le_rfl : 80 ≤ 80) := fun h ↦ by
        have hv := congrArg Fin.val h; change qw.val = 3967 at hv; omega
      have hne2 : qw ≠ mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩ := fun h ↦ by
        have hv := congrArg Fin.val h; change qw.val = 4029 at hv; omega
      change basisBits _ (liftSys110 s110 z) (sPerm qw) = coreBetaOf false 0 z qw
      have hR : coreBetaOf false 0 z qw = basisBits systemQubits z wsys := by
        rw [hqweq]; exact coreBetaOf_lt3948 false 0 z wsys
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, basisBits_liftSys110_lt3924 s110 z qw hqw, hR]
  rw [hcoord]
  exact slotSubGridCoord64_coreBetaOf_slot2_eq false 0 z e

theorem slotCoordSys_eq_of_extractIndex_eq {z₁ z₂ : Fin (2 ^ systemQubits)}
    {e : Fin numElectrons} (h : (rEl_sp e).extractIndex z₁ = (rEl_sp e).extractIndex z₂) :
    slotCoordSys z₁ e = slotCoordSys z₂ e := by
  rw [← slotSubGridCoord64_βLift_eq 0 z₁ e, ← slotSubGridCoord64_βLift_eq 0 z₂ e]
  funext w; apply Fin.ext
  exact regVal_eq_of_wire_eq _ (βLift 0 z₁) (βLift 0 z₂) fun j ↦ by
    have he218 : e.val < 218 := e.isLt; have hw3 := w.isLt; have hj6 := j.isLt
    let qw : Wire (fullSysCoreWires 80) :=
      axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j
    have hqw : qw.val < 3924 := by
      change 18 * e.val + (6 * w.val + (5 - j.val)) < 3924; omega
    let k18 : Fin 18 := ⟨6 * w.val + (5 - j.val), by omega⟩
    have hb := congrFun (congrArg (basisBits 18) h) k18
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex] at hb
    unfold βLift; rw [swapCore3967Fn_eq_swapCoreScrGenFn12, swapCore3967Fn_eq_swapCoreScrGenFn12]
    let sPerm := Equiv.swap (mWCore3967Gen (le_rfl : 80 ≤ 80))
      (mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩)
    have hne1 : qw ≠ mWCore3967Gen (le_rfl : 80 ≤ 80) := fun hc ↦ by
      have hv := congrArg Fin.val hc; change qw.val = 3967 at hv; omega
    have hne2 : qw ≠ mWCoreScrGen (le_rfl : 80 ≤ 80) ⟨12, by decide⟩ := fun hc ↦ by
      have hv := congrArg Fin.val hc; change qw.val = 4029 at hv; omega
    change basisBits _ (liftSys110 0 z₁) (sPerm qw) = basisBits _ (liftSys110 0 z₂) (sPerm qw)
    rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2,
      basisBits_liftSys110_lt3924 0 z₁ qw hqw, basisBits_liftSys110_lt3924 0 z₂ qw hqw]
    exact (congrArg (basisBits systemQubits z₁) (Fin.ext (by
      simp only [rEl_sp, qreg_block_apply, qw, k18]; rfl))).trans
      (hb.trans (congrArg (basisBits systemQubits z₂) (Fin.ext (by
        simp only [rEl_sp, qreg_block_apply, qw, k18]; rfl))))
theorem headEnBoolSpec_βLift_eq (s110 : Fin (2 ^ 110)) (z₁ z₂ : Fin (2 ^ systemQubits)) :
    headEnBoolSpec (βLift s110 z₁) = headEnBoolSpec (βLift s110 z₂) := by
  let rCore := QRegExt.ofFin posCoreWires
  have hs2 := βLift_high_eq s110 z₁ z₂ (q := wSlot2Core rCore) (by decide)
  have hs1 := βLift_high_eq s110 z₁ z₂ (q := wSlot1Core rCore) (by decide)
  have hs0 := βLift_high_eq s110 z₁ z₂ (q := wSlot0Core rCore) (by decide)
  have hsub := βLift_high_eq s110 z₁ z₂ (q := wSubReject rCore) (by decide)
  have hish := βLift_high_eq s110 z₁ z₂ (q := wIsHead rCore) (by decide)
  have hnuc : regVal (rNucIdx rCore) (βLift s110 z₁) = regVal (rNucIdx rCore) (βLift s110 z₂) :=
    regVal_eq_of_wire_eq _ (βLift s110 z₁) (βLift s110 z₂) fun j ↦
      βLift_high_eq s110 z₁ z₂ (by revert j; decide)
  have hanc : regVal (rAnchorIdx rCore) (βLift s110 z₁) =
      regVal (rAnchorIdx rCore) (βLift s110 z₂) :=
    regVal_eq_of_wire_eq _ (βLift s110 z₁) (βLift s110 z₂) fun j ↦
      βLift_high_eq s110 z₁ z₂ (by revert j; decide)
  unfold headEnBoolSpec
  simp only [rCore, hs2, hs1, hs0, hsub, hish, hnuc, hanc]

theorem tailAndSlackPhaseBitSpec_eq_false_of_headEn
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    {β : BitAssignment posCoreWires} (hen : headEnBoolSpec β = true) :
    tailAndSlackPhaseBitSpec true tailSign tailMag30 β = false := by
  let rCore := QRegExt.ofFin posCoreWires
  unfold headEnBoolSpec at hen
  simp only [Bool.and_eq_true] at hen
  rcases hen with ⟨⟨⟨⟨hs20, hns1⟩, hnsub⟩, hnuc, hanc⟩, hisHead⟩
  have hb2 : (β (wSlot2Core rCore) == 1) = false := by
    revert hs20; generalize β (wSlot2Core rCore) = z; revert z; decide
  have hb1 : (β (wSlot1Core rCore) == 1) = false := Bool.eq_false_iff.mpr fun h ↦ by
    rw [h] at hns1; cases hns1
  have hpart : decide (((β (wSlot0Core rCore) == 1) && !(β (wIsHead rCore) == 1)) = true →
      regVal (rPartnerIdx rCore) β < 217) = true :=
    decide_eq_true fun h ↦ by rw [hisHead] at h; simp at h
  unfold tailAndSlackPhaseBitSpec
  change (if (β (wSlot2Core rCore) == 1) = true then false else if (β (wSlot1Core rCore) == 1)
    = true then (β (wSlot0Core rCore) == 1) else _) = false
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hb2]; decide)),
    ite_eq_right_of_eq_false _ _ (eq_false (by rw [hb1]; decide))]
  dsimp only
  have hacc : (!(β (wSubReject rCore) == 1) && decide ((!(β (wSlot0Core rCore) == 1)) = true →
      regVal (rNucIdx rCore) β < 216) && decide (regVal (rAnchorIdx rCore) β < 218) && decide
      (((β (wSlot0Core rCore) == 1) && !(β (wIsHead rCore) == 1)) = true → regVal (rPartnerIdx
      rCore) β < 217)) = true := by
    rw [hnsub, hnuc, hanc, hpart]; rfl
  rw [hacc]
  change (if (!true) = true then _ else if (β (wIsHead rCore) == 1) = true then false else
    _) = false
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
    ite_eq_left_of_eq_true _ _ (eq_true hisHead)]
noncomputable def dTailBits (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment (fullSysCoreWires 80)) : ℂ :=
  let β' := swapCore3967Fn γ
  if headEnBoolSpec β' then 0
  else if tailAndSlackPhaseBitSpec true tailSign tailMag30 β' then -1 else 1
noncomputable def dHeadBits (γ : BitAssignment (fullSysCoreWires 80)) : ℂ :=
  let β' := swapCore3967Fn γ
  if headEnBoolSpec β' then omega8 ^ (headPhaseMod4Z8Spec β').val else 0
noncomputable def dTailMod4 (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (x : Fin (2 ^ (fullSysCoreWires 80))) :
    ℂ := dTailBits tailSign tailMag30 (basisBits (fullSysCoreWires 80) x)
noncomputable def dHeadMod4 (x : Fin (2 ^ (fullSysCoreWires 80))) : ℂ :=
  dHeadBits (basisBits (fullSysCoreWires 80) x)
theorem uPosPhase80Mod4Eff_eq_tail_add_head (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhase80Mod4Eff tailSign tailMag30).1 = Matrix.diagonal (dTailMod4 tailSign tailMag30)
    + uXThCore.1 * Matrix.diagonal dHeadMod4 := by
  apply matrix_ext_of_ket_core; intro γ
  rw [ket_uPosPhase80Mod4Eff, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
  unfold dTailMod4 dHeadMod4
  rw [msc_diagonal_mulVec_ket (dTailBits tailSign tailMag30) γ,
    msc_diagonal_mulVec_ket dHeadBits γ, Matrix.mulVec_smul]
  unfold dTailBits dHeadBits; dsimp only
  by_cases hen : headEnBoolSpec (swapCore3967Fn γ) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hen), ite_eq_left_of_eq_true _ _ (eq_true hen),
      ite_eq_left_of_eq_true _ _ (eq_true hen), zero_smul, zero_add]
    unfold posPhaseMod4Z8Spec
    rw [tailAndSlackPhaseBitSpec_eq_false_of_headEn tailSign tailMag30 hen,
      ite_eq_right_of_eq_false _ _ (eq_false (by decide)), add_zero]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hen), ite_eq_right_of_eq_false _ _ (eq_false hen),
      ite_eq_right_of_eq_false _ _ (eq_false hen), zero_smul, add_zero]
    have henF : headEnBoolSpec (swapCore3967Fn γ) = false := Bool.eq_false_iff.mpr hen
    have hhead0 : headPhaseMod4Z8Spec (swapCore3967Fn γ) = 0 := by
      unfold headPhaseMod4Z8Spec; rw [henF]; rfl
    unfold posPhaseMod4Z8Spec; rw [hhead0, zero_add]
    by_cases ht : tailAndSlackPhaseBitSpec true tailSign tailMag30 (swapCore3967Fn γ) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ht), ite_eq_left_of_eq_true _ _ (eq_true ht)]
      have hval4 : ((4 : ZMod 8).val : ℕ) = 4 := rfl
      rw [hval4, omega8_pow_four]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ht), ite_eq_right_of_eq_false _ _ (eq_false ht)]
      have hval0 : ((0 : ZMod 8).val : ℕ) = 0 := rfl
      rw [hval0, pow_zero]
def tailAndSlackPack (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (b2 b1 s0 subRej rejZero isH : Bool)
    (nucVal ancVal partVal tkVal : ℕ) (ySlot2 y0 y1 :
    Dyadic128CoulombMath.SubGridCoord64)
    (coset1 coset0 : Fin 3 → Bool) : Bool :=
  if b2 then false
  else if b1 then s0
  else
    let nucOk := !s0 → nucVal < 216
    let ancOk := ancVal < 218
    let partOk := (s0 && !isH) → partVal < 217
    let accept : Bool := !subRej && decide nucOk && ancOk && decide partOk
    if !accept then rejZero
    else if isH then false
    else
      let dTail : Dyadic128CoulombMath.FineCoord128 := fun w ↦
        if !s0 then
          ⟨2 * (ySlot2 w).val + (if coset1 w then 1 else 0), by
            have := (ySlot2 w).isLt
            cases coset1 w <;> simp <;> omega⟩
        else
          ⟨(2 * (y0 w).val + (if coset0 w then 1 else 0) + 128 -
            (2 * (y1 w).val + (if coset1 w then 1 else 0))) % 128,
            Nat.mod_lt _ (by omega)⟩
      let rOrbit := Dyadic128CoulombMath.tetRank65
        (Dyadic128CoulombMath.canonTriple128 dTail)
      let keepLt := tkVal < (tailMag30 rOrbit).val
      if keepLt then
        if !s0 then !(tailSign rOrbit) else tailSign rOrbit
      else rejZero
theorem tailAndSlackPhaseBitSpec_true_eq_pack
    (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) :
    tailAndSlackPhaseBitSpec true tailSign tailMag30 β =
      let rCore := QRegExt.ofFin posCoreWires
      tailAndSlackPack tailSign tailMag30
        (β (wSlot2Core rCore) == 1)
        (β (wSlot1Core rCore) == 1)
        (β (wSlot0Core rCore) == 1)
        (β (wSubReject rCore) == 1)
        (β (wRejectZero rCore) == 1)
        (β (wIsHead rCore) == 1)
        (regVal (rNucIdx rCore) β)
        (regVal (rAnchorIdx rCore) β)
        (regVal (rPartnerIdx rCore) β)
        (regVal (rTailKeep30 rCore) β)
        (slotSubGridCoord64 (rElecSlot rCore 0) β)
        (slotSubGridCoord64 (rElecSlot rCore 0) β)
        (slotSubGridCoord64 (rElecSlot rCore ⟨(regVal (rPartnerIdx rCore) β % 217) + 1,
          by have := Nat.mod_lt (regVal (rPartnerIdx rCore) β) (by omega : 0 < 217); omega⟩) β)
        (parity3OfReg (rCosetB1 rCore) β)
        (parity3OfReg (rCosetB0 rCore) β) := rfl
theorem tailAndSlackPhaseBitSpec_true_congr
    (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    {β₁ β₂ : BitAssignment posCoreWires} {mIdx0 : ℕ}
    (hs2 : β₁ (wSlot2Core (QRegExt.ofFin posCoreWires)) =
      β₂ (wSlot2Core (QRegExt.ofFin posCoreWires)))
    (hs1 : β₁ (wSlot1Core (QRegExt.ofFin posCoreWires)) =
      β₂ (wSlot1Core (QRegExt.ofFin posCoreWires)))
    (hs0 : β₁ (wSlot0Core (QRegExt.ofFin posCoreWires)) =
      β₂ (wSlot0Core (QRegExt.ofFin posCoreWires)))
    (hsub : β₁ (wSubReject (QRegExt.ofFin posCoreWires)) =
      β₂ (wSubReject (QRegExt.ofFin posCoreWires)))
    (hrej : β₁ (wRejectZero (QRegExt.ofFin posCoreWires)) =
      β₂ (wRejectZero (QRegExt.ofFin posCoreWires)))
    (hish : β₁ (wIsHead (QRegExt.ofFin posCoreWires)) =
      β₂ (wIsHead (QRegExt.ofFin posCoreWires)))
    (hnuc : regVal (rNucIdx (QRegExt.ofFin posCoreWires)) β₁ =
      regVal (rNucIdx (QRegExt.ofFin posCoreWires)) β₂)
    (hanc : regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) β₁ =
      regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) β₂)
    (hp1 : regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) β₁ = mIdx0)
    (hp2 : regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) β₂ = mIdx0)
    (htk : regVal (rTailKeep30 (QRegExt.ofFin posCoreWires)) β₁ =
      regVal (rTailKeep30 (QRegExt.ofFin posCoreWires)) β₂)
    (hcb1 : parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) β₁ =
      parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) β₂)
    (hcb0 : parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β₁ =
      parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β₂)
    (hy0 : slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₁ =
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₂)
    (hy1 : slotSubGridCoord64
        (rElecSlot (QRegExt.ofFin posCoreWires)
          ⟨(mIdx0 % 217) + 1, by have := Nat.mod_lt mIdx0 (by decide : 0 < 217); omega⟩) β₁ =
      slotSubGridCoord64
        (rElecSlot (QRegExt.ofFin posCoreWires)
          ⟨(mIdx0 % 217) + 1, by have := Nat.mod_lt mIdx0 (by decide : 0 < 217); omega⟩) β₂) :
    tailAndSlackPhaseBitSpec true tailSign tailMag30 β₁ =
      tailAndSlackPhaseBitSpec true tailSign tailMag30 β₂ := by
  let eP0 : Fin 218 :=
    ⟨(mIdx0 % 217) + 1, by have := Nat.mod_lt mIdx0 (by decide : 0 < 217); omega⟩
  have hy1_lhs : ∀ (hlt1 : (regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) β₁ % 217) + 1 < 218),
      slotSubGridCoord64
          (rElecSlot (QRegExt.ofFin posCoreWires)
            ⟨(regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) β₁ % 217) + 1, hlt1⟩) β₁ =
        slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) eP0) β₂ := fun hlt1 ↦ by
    have he1 : (⟨(regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) β₁ % 217) + 1,
      hlt1⟩ : Fin 218) =
        eP0 :=
      Fin.ext (by dsimp only [eP0]; rw [hp1])
    rw [he1]; exact hy1
  have hy1_rhs : ∀ (hlt2 : (regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) β₂ % 217) + 1 < 218),
      slotSubGridCoord64
          (rElecSlot (QRegExt.ofFin posCoreWires)
            ⟨(regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) β₂ % 217) + 1, hlt2⟩) β₂ =
        slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) eP0) β₂ := fun hlt2 ↦ by
    have he2 : (⟨(regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) β₂ % 217) + 1,
      hlt2⟩ : Fin 218) =
        eP0 :=
      Fin.ext (by dsimp only [eP0]; rw [hp2])
    rw [he2]
  rw [tailAndSlackPhaseBitSpec_true_eq_pack tailSign tailMag30 β₁,
    tailAndSlackPhaseBitSpec_true_eq_pack tailSign tailMag30 β₂]
  dsimp only
  rw [hy1_lhs, hy1_rhs, hs2, hs1, hs0, hsub, hrej, hish, hnuc, hanc, hp1, hp2,
    htk, hy0, hcb1, hcb0]
theorem tail_slice_mapsToKrylov3 (spinUp : Finset (Fin numElectrons))
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (c' : Configuration) (s110 : Fin (2 ^ 110)) (eAnc : Fin numElectrons) :
    CoreMapsToKrylov3On ((rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp
    (Equiv.swap 0 eAnc))) ((rSysInFullSysCore 80).embedMatrix ((elecSysProd (vRemElec c'
    s110)).1ᴴ * Matrix.diagonal (fun z ↦ dTailMod4 tailSign tailMag30 (liftSys110 s110 z)) *
    (elecSysProd (vRemElec c' s110)).1)) := by
  let rCore := QRegExt.ofFin posCoreWires
  let mIdx0 := regVal (rPartnerIdx rCore) (βLift s110 0)
  let ePartner : Fin numElectrons :=
    ⟨(mIdx0 % 217) + 1, by
      dsimp [numElectrons];
      have :=
        Nat.mod_lt mIdx0 (by decide : 0 < 217); omega⟩
  let S : Finset (Fin numElectrons) := {(0 : Fin numElectrons), ePartner}
  have hScard : S.card ≤ 3 := le_trans (Finset.card_insert_le _ _) (by simp)
  refine CoreMapsToKrylov3On.of_zeroBad_absorb
    (by rw [← (rSysInFullSysCore 80).embedMatrix_mul, bad0Proj_mul_swappedElecFermProj])
    (coreOpMapsZeroBadToKrylov3_embed_sys
      (sysMapsZeroBadToKrylov3_conj_elecSysProd_diag_le3 _ hScard _ fun z₁ z₂ hS ↦ ?_))
  unfold dTailMod4 dTailBits
  change (if headEnBoolSpec (βLift s110 z₁) then (0 : ℂ)
      else if tailAndSlackPhaseBitSpec true tailSign tailMag30 (βLift s110 z₁) then -1 else 1) =
    (if headEnBoolSpec (βLift s110 z₂) then (0 : ℂ)
      else if tailAndSlackPhaseBitSpec true tailSign tailMag30 (βLift s110 z₂) then -1 else 1)
  rw [headEnBoolSpec_βLift_eq s110 z₁ z₂]
  suffices htail : tailAndSlackPhaseBitSpec true tailSign tailMag30 (βLift s110 z₁) =
      tailAndSlackPhaseBitSpec true tailSign tailMag30 (βLift s110 z₂) by rw [htail]
  have hb (q : Wire posCoreWires) (hq : 3924 ≤ q.val) := βLift_high_eq s110 z₁ z₂ hq
  have hr {k : ℕ} (r : QRegister k posCoreWires) (hrw : ∀ j, 3924 ≤ (r j).val) :=
    regVal_eq_of_wire_eq r (βLift s110 z₁) (βLift s110 z₂) fun j ↦ hb _ (hrw j)
  exact tailAndSlackPhaseBitSpec_true_congr tailSign tailMag30
    (hb _ (by decide)) (hb _ (by decide)) (hb _ (by decide))
    (hb _ (by decide)) (hb _ (by decide)) (hb _ (by decide))
    (hr _ (by decide)) (hr _ (by decide))
    (regVal_eq_of_wire_eq _ (βLift s110 z₁) (βLift s110 0) fun j ↦
      βLift_high_eq s110 z₁ 0 (by revert j; decide))
    (regVal_eq_of_wire_eq _ (βLift s110 z₂) (βLift s110 0) fun j ↦
      βLift_high_eq s110 z₂ 0 (by revert j; decide))
    (hr _ (by decide))
    (funext fun w ↦ by unfold parity3OfReg; rw [hb _ (by revert w; decide)])
    (funext fun w ↦ by unfold parity3OfReg; rw [hb _ (by revert w; decide)])
    (by rw [slotSubGridCoord64_βLift_eq, slotSubGridCoord64_βLift_eq]
        exact slotCoordSys_eq_of_extractIndex_eq (hS 0 (Finset.mem_insert_self _ _)))
    (by rw [slotSubGridCoord64_βLift_eq, slotSubGridCoord64_βLift_eq]
        exact slotCoordSys_eq_of_extractIndex_eq
          (hS ePartner (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
theorem omega8_pow_add_nat_mul (a b : ZMod 8) (N : ℕ) :
    omega8 ^ (a + (N : ZMod 8) * b).val = omega8 ^ a.val * (omega8 ^ b.val) ^ N := by
  have h8 : omega8 ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, omega8_pow_four]; norm_num
  have hmod : ∀ k : ℕ, omega8 ^ (k % 8) = omega8 ^ k := fun k ↦ by
    conv_rhs => rw [← Nat.div_add_mod k 8]
    rw [pow_add, pow_mul, h8, one_pow, one_mul]
  have hadd : ∀ x y : ZMod 8, omega8 ^ (x + y).val = omega8 ^ x.val * omega8 ^ y.val :=
    fun x y ↦ by rw [ZMod.val_add, hmod, pow_add]
  have hmul : ∀ m : ℕ, omega8 ^ ((m : ZMod 8) * b).val = (omega8 ^ b.val) ^ m := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih, pow_succ]
  rw [hadd, hmul]
theorem pow_eq_newton_sum_219 (ζ : ℂ) {N : ℕ} (hN : N < 219) :
    ζ ^ N = ∑ k ∈ Finset.range 219, (N.choose k : ℂ) * (ζ - 1) ^ k := by
  have h1 : ζ ^ N = ((ζ - 1) + 1) ^ N := by ring_nf
  rw [h1, add_pow]
  trans (∑ k ∈ Finset.range (N + 1), (N.choose k : ℂ) * (ζ - 1) ^ k)
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [one_pow, mul_one, mul_comm]
  · refine Finset.sum_subset (Finset.range_mono (by omega : N + 1 ≤ 219)) fun k _ hkn ↦ ?_
    have hlt : N < k := by rw [Finset.mem_range] at hkn; omega
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]
theorem factorial_mul_choose_cast_eq_prod : ∀ (n k : ℕ),
    (k.factorial : ℂ) * (n.choose k : ℂ) = ∏ j ∈ Finset.range k, ((n : ℂ) - (j : ℂ))
  | 0, 0 => by simp
  | 0, k + 1 => by
      rw [Nat.choose_zero_succ, Nat.cast_zero, mul_zero, Finset.prod_range_succ']
      simp
  | n + 1, 0 => by simp
  | n + 1, k + 1 => by
      have ih1 := factorial_mul_choose_cast_eq_prod n k
      have ih2 := factorial_mul_choose_cast_eq_prod n (k + 1)
      have hstep : ∏ j ∈ Finset.range (k + 1), (((n + 1 : ℕ) : ℂ) - (j : ℂ)) =
          ((n + 1 : ℕ) : ℂ) * ∏ j ∈ Finset.range k, ((n : ℂ) - (j : ℂ)) := by
        rw [Finset.prod_range_succ', mul_comm]
        simp only [Nat.cast_zero, sub_zero]
        refine congrArg (((n + 1 : ℕ) : ℂ) * ·) (Finset.prod_congr rfl fun j _ ↦ ?_)
        push_cast; ring
      rw [hstep, Nat.choose_succ_succ, Nat.cast_add, mul_add, ih2, Finset.prod_range_succ,
        Nat.factorial_succ, Nat.cast_mul, mul_assoc, ih1]
      set P := ∏ j ∈ Finset.range k, ((n : ℂ) - (j : ℂ))
      push_cast; ring
theorem choose_two_cast_eq (n : ℕ) :
    (n.choose 2 : ℂ) = (2 : ℂ)⁻¹ * ((n : ℂ) * (n : ℂ) - (n : ℂ)) := by
  have h1 := factorial_mul_choose_cast_eq_prod n 2
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero] at h1
  have hfac : ((2 : ℕ).factorial : ℂ) = 2 := by norm_num
  rw [hfac] at h1
  simp only [one_mul, Nat.cast_zero, sub_zero, Nat.cast_one] at h1
  linear_combination (2 : ℂ)⁻¹ * h1
theorem choose_three_add_cast_eq (n m : ℕ) : (n.choose (3 + m) : ℂ) = (((3 + m).factorial :
    ℂ)⁻¹ * ∏ j ∈ Finset.range m, ((n : ℂ) - ((3 + j : ℕ) : ℂ))) *
    ((n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2)) := by
  have hfac : ((3 + m).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (3 + m))
  have h1 := factorial_mul_choose_cast_eq_prod n (3 + m)
  rw [Finset.prod_range_add, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_zero] at h1
  simp only [one_mul, Nat.cast_zero, sub_zero, Nat.cast_one] at h1
  have h2 : ((2 : ℕ) : ℂ) = 2 := by norm_num
  rw [h2] at h1
  calc (n.choose (3 + m) : ℂ)
    _ = ((3 + m).factorial : ℂ)⁻¹ * (((3 + m).factorial : ℂ) * (n.choose (3 + m) : ℂ)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hfac, one_mul]
    _ = _ := by rw [h1]; ring
def hitCountRest (yT : Fin 3 → Fin 64) (z : Fin (2 ^ systemQubits)) : ℕ :=
  ((Finset.univ.erase (0 : Fin numElectrons)).filter fun e ↦ decide (slotCoordSys z e = yT)).card
theorem rk1_sp_of_unitary_row (W : Unitary (2 ^ 18)) (uT : Fin (2 ^ 18)) :
    let χ : Fin (2 ^ 18) → ℂ := fun v ↦ star (W.1 uT v)
    W.1ᴴ * Matrix.diagonal (fun u ↦ if u = uT then (1 : ℂ) else 0) * W.1 = rk1_sp χ ∧
      (∑ v : Fin (2 ^ 18), star (χ v) * χ v = 1) := by
  intro χ
  refine ⟨?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single uT]
    · rw [Matrix.mul_diagonal, ite_eq_left_of_eq_true _ _ (eq_true rfl), mul_one,
        Matrix.conjTranspose_apply]
      unfold rk1_sp; dsimp only [Matrix.of_apply, χ]; rw [star_star]
    · intro k _ hk
      rw [Matrix.mul_diagonal, ite_eq_right_of_eq_false _ _ (eq_false hk), mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ uT) h
  · have hUU : W.1 * W.1ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp W.2
    have hdiag := congrFun (congrFun hUU uT) uT
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hdiag
    refine (Finset.sum_congr rfl fun v _ ↦ ?_).trans hdiag
    dsimp only [χ]; rw [star_star, Matrix.conjTranspose_apply]
theorem elecSysProd_conj_hitCountRest (c' : Configuration) (s110 : Fin (2 ^ 110))
    (yT : Fin 3 → Fin 64) :
    let χ : Fin (2 ^ 18) → ℂ := fun v ↦ star ((wRem18 c' s110).1 (slotCoord18Equiv.symm yT) v)
    (elecSysProd (vRemElec c' s110)).1ᴴ *
        Matrix.diagonal (fun z ↦ (hitCountRest yT z : ℂ)) *
        (elecSysProd (vRemElec c' s110)).1 =
      nSub_sp χ (Finset.univ.erase 0) ∧
    (∑ v : Fin (2 ^ 18), star (χ v) * χ v = 1) := by
  intro χ
  rcases rk1_sp_of_unitary_row (wRem18 c' s110) (slotCoord18Equiv.symm yT) with ⟨hrk, hnorm⟩
  refine ⟨?_, hnorm⟩
  have hdiag_sum : Matrix.diagonal (fun z ↦ (hitCountRest yT z : ℂ)) =
      ∑ e ∈ Finset.univ.erase (0 : Fin numElectrons),
        Matrix.diagonal (fun z ↦ if slotCoordSys z e = yT then (1 : ℂ) else 0) := by
    ext i j
    rw [matrix_finset_sum_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      unfold hitCountRest
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      rw [Matrix.diagonal_apply_eq]
      by_cases heq : slotCoordSys i e = yT
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true heq)),
          ite_eq_left_of_eq_true _ _ (eq_true heq), Nat.cast_one]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using heq)),
          ite_eq_right_of_eq_false _ _ (eq_false heq), Nat.cast_zero]
    · rw [Matrix.diagonal_apply_ne _ hij, Finset.sum_eq_zero]
      intro e _; exact Matrix.diagonal_apply_ne _ hij
  rw [hdiag_sum, Matrix.mul_sum, Finset.sum_mul]
  unfold nSub_sp
  refine Finset.sum_congr rfl fun e he ↦ ?_
  have he0 : e ≠ 0 := Finset.ne_of_mem_erase he
  have h18 : Matrix.diagonal (fun u : Fin (2 ^ 18) ↦
    if slotCoord18Equiv u = yT then (1 : ℂ) else 0) =
      Matrix.diagonal (fun u : Fin (2 ^ 18) ↦
        if u = slotCoord18Equiv.symm yT then (1 : ℂ) else 0) := by
    refine congrArg Matrix.diagonal (funext fun u ↦ ?_)
    have hiff : slotCoord18Equiv u = yT ↔ u = slotCoord18Equiv.symm yT :=
      ⟨fun h ↦ by rw [← h, slotCoord18Equiv.symm_apply_apply],
       fun h ↦ by rw [h, slotCoord18Equiv.apply_symm_apply]⟩
    by_cases hu : u = slotCoord18Equiv.symm yT
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr hu)),
      ite_eq_left_of_eq_true _ _ (eq_true hu)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hu (hiff.mp h))),
        ite_eq_right_of_eq_false _ _ (eq_false hu)]
  rw [diag_slotCoordSys_eq_embed e yT, h18]
  unfold elecSysProd
  rw [list_ofFn_prod_conj_rEl (vRemElec c' s110) e _,
    vRemElec_eq_wRem18_of_ne_zero c' s110 he0, hrk]
  rfl
theorem unitary_conj_mul {d : ℕ} [NeZero d] (U : Unitary d) (A B : Operator d) :
    U.1ᴴ * (A * B) * U.1 = (U.1ᴴ * A * U.1) * (U.1ᴴ * B * U.1) := by
  have hUU : U.1 * U.1ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  calc U.1ᴴ * (A * B) * U.1
    _ = U.1ᴴ * A * (U.1 * U.1ᴴ) * B * U.1 := by
      rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (U.1ᴴ * A * U.1) * (U.1ᴴ * B * U.1) := by simp only [Matrix.mul_assoc]
theorem embedMatrix_finset_sum {ι : Type*} {m N : ℕ} (r : QRegister m N)
    (s : Finset ι) (f : ι → Operator (2 ^ m)) :
    r.embedMatrix (∑ a ∈ s, f a) = ∑ a ∈ s, r.embedMatrix (f a) := by
  induction s using Finset.cons_induction with
  | empty => simp [QRegister.embedMatrix_zero]
  | cons a t _ ih => rw [Finset.sum_cons, Finset.sum_cons, QRegister.embedMatrix_add, ih]
theorem conj_diag_le3_mapsToKrylov3 (spinUp : Finset (Fin numElectrons)) (c' : Configuration)
    (s110 : Fin (2 ^ 110)) (eAnc : Fin numElectrons) {S : Finset (Fin numElectrons)}
    (hS : S.card ≤ 3) (d : Fin (2 ^ systemQubits) → ℂ) (hd : ∀ z₁ z₂ : Fin (2 ^ systemQubits),
    (∀ s ∈ S, (rEl_sp s).extractIndex z₁ = (rEl_sp s).extractIndex z₂) → d z₁ = d z₂) :
    CoreMapsToKrylov3On ((rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp
    (Equiv.swap 0 eAnc))) ((rSysInFullSysCore 80).embedMatrix ((elecSysProd (vRemElec c'
    s110)).1ᴴ * Matrix.diagonal d * (elecSysProd (vRemElec c' s110)).1)) :=
  CoreMapsToKrylov3On.of_zeroBad_absorb
    (by rw [← (rSysInFullSysCore 80).embedMatrix_mul, bad0Proj_mul_swappedElecFermProj])
    (coreOpMapsZeroBadToKrylov3_embed_sys
      (sysMapsZeroBadToKrylov3_conj_elecSysProd_diag_le3 _ hS d hd))
theorem headHitSetSpec_eq_filter_of_params
    (β : BitAssignment posCoreWires)
    (s0 : Bool) (dHead0 : Fin 3 → Fin 128) (y0_0 : Fin 3 → Fin 64) (b0_0 : Fin 3 → Bool)
    (coordFn : Fin 218 → Fin 3 → Fin 64)
    (hs0 : (β (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) = s0)
    (hdH : fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β = dHead0)
    (hy0 : slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β = y0_0)
    (hb0 : parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β = b0_0)
    (hcoord : ∀ e : Fin 218,
      slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β = coordFn e) :
    let yT : Fin 3 → Fin 64 := fun w ↦
      if Bool.not s0 then ⟨(dHead0 w).val / 2, by omega⟩
      else (anchorSubTarget1D (y0_0 w) (if b0_0 w then 1 else 0) (dHead0 w)).1
    headHitSetSpec β =
      Finset.univ.filter fun e : Fin 218 ↦
        ((Bool.not s0 || decide (e.val ≠ 0)) && decide (coordFn e = yT)) = true := by
  intro yT
  unfold headHitSetSpec
  dsimp only
  refine Finset.filter_congr fun e _ ↦ ?_
  have hyT : (fun w : Fin 3 ↦
      if Bool.not (β (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) then
        (⟨(fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β w).val / 2,
          by omega⟩ : Fin 64)
      else
        (anchorSubTarget1D
          (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β w)
          (if parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β w then 1 else 0)
          (fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β w)).1) = yT := by
    funext w; apply Fin.ext; dsimp only [yT]
    by_cases h0 : Bool.not (β (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) = true
    · have h0' : Bool.not s0 = true := by rwa [← hs0]
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0), ite_eq_left_of_eq_true _ _ (eq_true h0')]
      dsimp only; rw [hdH]
    · have h0' : ¬ Bool.not s0 = true := by rwa [← hs0]
      rw [ite_eq_right_of_eq_false _ _ (eq_false h0), ite_eq_right_of_eq_false _ _ (eq_false h0')]
      rw [hy0, hb0, hdH]
  rw [hyT, hs0, hcoord e]
private theorem diagonal_eq_sum_proj {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (p : β → α) (f : β → ℂ) : Matrix.diagonal f = ∑ a : α, Matrix.diagonal
    (fun b ↦ if p b = a then f b else 0) := by
  ext i j; rw [matrix_finset_sum_apply]
  by_cases hij : i = j
  · subst hij; rw [Matrix.diagonal_apply_eq]
    simp only [Matrix.diagonal_apply_eq, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  · rw [Matrix.diagonal_apply_ne _ hij, Finset.sum_eq_zero]
    intro a _; exact Matrix.diagonal_apply_ne _ hij
private theorem diagonal_finset_sum_smul {ι β : Type*} [DecidableEq β] (s : Finset ι)
    (c : ι → ℂ) (g : ι → β → ℂ) : Matrix.diagonal (fun b ↦ ∑ k ∈ s, c k * g k b) = ∑ k ∈ s, c
    k • Matrix.diagonal (g k) := by
  ext i j; rw [matrix_finset_sum_apply]
  by_cases hij : i = j
  · subst hij; rw [Matrix.diagonal_apply_eq]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
  · rw [Matrix.diagonal_apply_ne _ hij, Finset.sum_eq_zero]
    intro k _; rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij, smul_zero]
private theorem hitCountRest_cast_eq_sum (yT : Fin 3 → Fin 64) (z : Fin (2 ^ systemQubits)) :
    (hitCountRest yT z : ℂ) = ∑ e ∈ Finset.univ.erase (0 : Fin numElectrons), if slotCoordSys
    z e = yT then (1 : ℂ) else 0 := by
  unfold hitCountRest; rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  by_cases heq : slotCoordSys z e = yT
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true heq)),
      ite_eq_left_of_eq_true _ _ (eq_true heq), Nat.cast_one]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using heq)),
      ite_eq_right_of_eq_false _ _ (eq_false heq), Nat.cast_zero]
private theorem diagonal_mul_finset_sum {ι β : Type*} [DecidableEq β] (ind : β → ℂ)
    (s : Finset ι) (f : ι → β → ℂ) : Matrix.diagonal (fun b ↦ ind b * ∑ e ∈ s, f e b) = ∑ e ∈
    s, Matrix.diagonal (fun b ↦ ind b * f e b) := by
  ext i j; rw [matrix_finset_sum_apply]
  by_cases hij : i = j
  · subst hij; rw [Matrix.diagonal_apply_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, Finset.sum_eq_zero]
    intro e _; exact Matrix.diagonal_apply_ne _ hij
private theorem diagonal_mul_sq_finset_sum {ι β : Type*} [DecidableEq β]
    (ind : β → ℂ) (s : Finset ι) (f : ι → β → ℂ) :
    Matrix.diagonal (fun b ↦ ind b * ((∑ e ∈ s, f e b) * (∑ e ∈ s, f e b))) =
      ∑ e₁ ∈ s, ∑ e₂ ∈ s, Matrix.diagonal (fun b ↦ ind b * (f e₁ b * f e₂ b)) := by
  ext i j; rw [matrix_finset_sum_apply]
  by_cases hij : i = j
  · subst hij; rw [Matrix.diagonal_apply_eq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e₁ _ ↦ ?_
    rw [matrix_finset_sum_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e₂ _ ↦ ?_
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, Finset.sum_eq_zero]
    intro e₁ _; rw [matrix_finset_sum_apply, Finset.sum_eq_zero]
    intro e₂ _; exact Matrix.diagonal_apply_ne _ hij
private theorem diagonal_choose_two_eq {β : Type*} [DecidableEq β] (ind : β → ℂ) (cnt : β → ℕ)
    : Matrix.diagonal (fun b ↦ ind b * ((cnt b).choose 2 : ℂ)) = (2 : ℂ)⁻¹ • Matrix.diagonal
    (fun b ↦ ind b * ((cnt b : ℂ) * (cnt b : ℂ))) + (-(2 : ℂ)⁻¹) • Matrix.diagonal
    (fun b ↦ ind b * (cnt b : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    rw [choose_two_cast_eq]; ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij,
      smul_zero, add_zero]
private theorem conj_diag_choose_three_add_eq {D : ℕ} [NeZero D] (U : Unitary D)
    (N : Operator D) (ind0 : Fin D → ℂ) (cnt : Fin D → ℕ) (m : ℕ)
    (hH : U.1ᴴ * Matrix.diagonal (fun z ↦ (cnt z : ℂ)) * U.1 = N) : U.1ᴴ * Matrix.diagonal
    (fun z ↦ ind0 z * ((cnt z).choose (3 + m) : ℂ)) * U.1 = (U.1ᴴ * Matrix.diagonal (fun z ↦
    ((3 + m).factorial : ℂ)⁻¹ * ind0 z * ∏ j ∈ Finset.range m, ((cnt z : ℂ) - ((3 + j : ℕ) :
    ℂ))) * U.1) * (N * (N - 1) * (N - (2 : ℂ) • 1)) := by
  let D_L : Operator D := Matrix.diagonal (fun z ↦ ((3 + m).factorial : ℂ)⁻¹ * ind0 z * ∏ j ∈
      Finset.range m, ((cnt z : ℂ) - ((3 + j : ℕ) : ℂ)))
  let D_H : Operator D := Matrix.diagonal (fun z ↦ (cnt z : ℂ))
  have hsub1 : D_H - 1 = Matrix.diagonal (fun z ↦ (cnt z : ℂ) - 1) := by
    dsimp only [D_H]; rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  have hsub2 : D_H - (2 : ℂ) • 1 = Matrix.diagonal (fun z ↦ (cnt z : ℂ) - 2) := by
    dsimp only [D_H]
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
    simp
  have hd_fac : Matrix.diagonal (fun z ↦ ind0 z * ((cnt z).choose (3 + m) : ℂ)) =
      D_L * (D_H * (D_H - 1) * (D_H - (2 : ℂ) • 1)) := by
    dsimp only [D_L]
    rw [hsub1, hsub2]; dsimp only [D_H]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
    rw [choose_three_add_cast_eq]; ring
  have hU11 : U.1ᴴ * (1 : Operator D) * U.1 = 1 := by
    rw [Matrix.mul_one]; exact Matrix.mem_unitaryGroup_iff'.mp U.2
  have hconj_H1 : U.1ᴴ * (D_H - 1) * U.1 = N - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hH, hU11]
  have hconj_H2 : U.1ᴴ * (D_H - (2 : ℂ) • 1) * U.1 = N - (2 : ℂ) • 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hH, hU11]
  rw [hd_fac, unitary_conj_mul U D_L _, unitary_conj_mul U (D_H * (D_H - 1)) _,
    unitary_conj_mul U D_H (D_H - 1), hH, hconj_H1, hconj_H2]
set_option exponentiation.threshold 256 in
private theorem embedMatrix_mul_right_zero {m N : ℕ} (r : QRegister m N)
    (A B P : Operator (2 ^ m)) (hBP : B * P = 0) :
    r.embedMatrix (A * B) * r.embedMatrix P = 0 := by
  rw [QRegister.embedMatrix_mul, Matrix.mul_assoc, ← QRegister.embedMatrix_mul,
    hBP, QRegister.embedMatrix_zero, Matrix.mul_zero]
set_option exponentiation.threshold 256 in
private theorem embedMatrix_conj_finset_sum {ι : Type*} {m N : ℕ} (r : QRegister m N)
    (A : Operator (2 ^ m)) (s : Finset ι) (f : ι → Operator (2 ^ m)) : r.embedMatrix
    (Aᴴ * (∑ i ∈ s, f i) * A) = ∑ i ∈ s, r.embedMatrix (Aᴴ * f i * A) := by
  rw [Matrix.mul_sum, Finset.sum_mul, embedMatrix_finset_sum]
set_option exponentiation.threshold 256 in
private theorem embedMatrix_conj_smul {m N : ℕ}
    (r : QRegister m N) (A : Operator (2 ^ m)) (a : ℂ) (D : Operator (2 ^ m)) :
    r.embedMatrix (Aᴴ * (a • D) * A) = a • r.embedMatrix (Aᴴ * D * A) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, QRegister.embedMatrix_smul]
set_option exponentiation.threshold 256 in
private theorem embedMatrix_conj_add {m N : ℕ} (r : QRegister m N)
    (A D₁ D₂ : Operator (2 ^ m)) : r.embedMatrix (Aᴴ * (D₁ + D₂) * A) = r.embedMatrix
    (Aᴴ * D₁ * A) + r.embedMatrix (Aᴴ * D₂ * A) := by
  rw [Matrix.mul_add, Matrix.add_mul, QRegister.embedMatrix_add]
set_option exponentiation.threshold 256 in
private theorem exists_zRef_extractIndex_zero (u₀ : Fin (2 ^ 18)) :
    ∃ zRef : Fin (2 ^ systemQubits), (rEl_sp 0).extractIndex zRef = u₀ := by
  refine ⟨(basisBitsEquiv systemQubits).symm fun q ↦
    if h : q.val < 18 then basisBits 18 u₀ ⟨q.val, h⟩ else 0, ?_⟩
  apply (basisBitsEquiv 18).injective; funext k
  change basisBits 18 ((rEl_sp 0).extractIndex _) k = basisBits 18 u₀ k
  rw [QRegister.basisBits_extractIndex]
  have hk18 : (rEl_sp 0 k).val < 18 := by
    have := k.isLt; change 18 * 0 + k.val < 18; omega
  rw [basisBits_symm_apply, dite_eq_left_of_eq_true (eq_true hk18)]
  exact congrArg (basisBits 18 u₀) (Fin.ext (by change 18 * 0 + k.val = k.val; omega))
private theorem dHeadBits_eq_of_headEn {γ : BitAssignment (fullSysCoreWires 80)}
    (h : headEnBoolSpec (swapCore3967Fn γ) = true) :
    dHeadBits γ = omega8 ^ (headPhaseMod4Z8Spec (swapCore3967Fn γ)).val := by
  unfold dHeadBits
  change (if headEnBoolSpec (swapCore3967Fn γ) = true then
    omega8 ^ (headPhaseMod4Z8Spec (swapCore3967Fn γ)).val else 0) = _
  exact ite_eq_left_of_eq_true _ _ (eq_true h)
private theorem headPhaseMod4_bits_eq_newton (β₀ : BitAssignment posCoreWires) : ∃
    (yT : Fin 3 → Fin 64) (cPhase ζ : ℂ), ∀ (β : BitAssignment posCoreWires)
    (coord : Fin 218 → Fin 3 → Fin 64), headEnBoolSpec β = true →
    (∀ q : Wire posCoreWires, 3924 ≤ q.val → β q = β₀ q) → (∀ e : Fin 218, slotSubGridCoord64
    (rElecSlot (QRegExt.ofFin posCoreWires) e) β = coord e) → coord 0 = slotSubGridCoord64
    (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₀ → omega8 ^ (headPhaseMod4Z8Spec β).val = ∑
    k ∈ Finset.range 219, (cPhase * (ζ - 1) ^ k) * ((((Finset.univ.erase (0 : Fin 218)).filter
    fun e ↦ decide (coord e = yT)).card).choose k : ℂ) := by
  let rCore := QRegExt.ofFin posCoreWires
  let s0 : Bool := β₀ (wSlot0Core rCore) == 1
  let dHead0 := fineCoordOfReg21 (rHeadFine21 rCore) β₀
  let y0_0 := slotSubGridCoord64 (rElecSlot rCore 0) β₀
  let b0_0 := parity3OfReg (rCosetB0 rCore) β₀
  let yT : Fin 3 → Fin 64 := fun w ↦
    if Bool.not s0 then ⟨(dHead0 w).val / 2, by omega⟩
    else (anchorSubTarget1D (y0_0 w) (if b0_0 w then 1 else 0) (dHead0 w)).1
  let c₀ : ℕ := if (0 : Fin 218) ∈ headHitSetSpec β₀ then 1 else 0
  let s0Z8 : ZMod 8 := if s0 then 4 else 0
  let stepZ8 : ZMod 8 := 2 + (if β₀ (wHeadThresh rCore) == 1 then 4 else 0)
  let cPhase : ℂ := omega8 ^ (s0Z8 + (c₀ : ZMod 8) * stepZ8).val
  let ζ : ℂ := omega8 ^ stepZ8.val
  refine ⟨yT, cPhase, ζ, fun β coord henβ hHigh hcoord h0eq ↦ ?_⟩
  have hset0 := headHitSetSpec_eq_filter_of_params β₀ s0 dHead0 y0_0 b0_0
    (fun e ↦ slotSubGridCoord64 (rElecSlot rCore e) β₀) rfl rfl rfl rfl (fun _ ↦ rfl)
  dsimp only [yT] at hset0
  have hs0_β : β (wSlot0Core rCore) = β₀ (wSlot0Core rCore) := hHigh _ (by decide)
  have hth_β : β (wHeadThresh rCore) = β₀ (wHeadThresh rCore) := hHigh _ (by decide)
  have hdH_β : fineCoordOfReg21 (rHeadFine21 rCore) β = dHead0 :=
    funext fun w ↦ Fin.ext (regVal_eq_of_wire_eq _ β β₀ fun j ↦ hHigh _ (by revert w j; decide))
  have hb0_β : parity3OfReg (rCosetB0 rCore) β = b0_0 :=
    funext fun w ↦ by dsimp only [b0_0]; unfold parity3OfReg; rw [hHigh _ (by revert w; decide)]
  have hset := headHitSetSpec_eq_filter_of_params β s0 dHead0 y0_0 b0_0 coord
    (congrArg (· == 1) hs0_β) hdH_β ((hcoord 0).trans h0eq) hb0_β hcoord
  dsimp only [yT] at hset
  have h0mem : ((0 : Fin 218) ∈ headHitSetSpec β) ↔ ((0 : Fin 218) ∈ headHitSetSpec β₀) := by
    rw [hset, hset0]; simp only [Finset.mem_filter, Finset.mem_univ, true_and, h0eq]; rfl
  have rotAux : (headHitSetSpec β).erase 0 =
      (Finset.univ.erase (0 : Fin 218)).filter fun e ↦ decide (coord e = yT) := by
    ext e; rw [hset]
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    refine ⟨fun ⟨hne, hmem⟩ ↦ ⟨hne, (Bool.and_eq_true _ _).mp hmem |>.2⟩,
      fun ⟨hne, hmem⟩ ↦ ⟨hne, ?_⟩⟩
    have hne_val : decide (e.val ≠ 0) = true := decide_eq_true fun hv ↦ hne (Fin.ext hv)
    rw [hne_val, Bool.or_true, Bool.true_and]; exact hmem
  set restCard := ((Finset.univ.erase (0 : Fin 218)).filter fun e ↦ decide (coord e = yT)).card
  have hrest_lt : restCard < 219 := by
    have hle : restCard ≤ (Finset.univ : Finset (Fin 218)).card :=
      le_trans (Finset.card_le_card (Finset.filter_subset _ _))
        (Finset.card_le_card (Finset.erase_subset _ _))
    have hc : (Finset.univ : Finset (Fin 218)).card = 218 := by decide
    omega
  have hcard : (headHitSetSpec β).card = c₀ + restCard := by
    by_cases h0b : (0 : Fin 218) ∈ headHitSetSpec β₀
    · rw [← Finset.card_erase_add_one (h0mem.mpr h0b), rotAux, add_comm]
      simp [c₀, h0b, restCard]
    · rw [← congrArg Finset.card (Finset.erase_eq_of_notMem (mt h0mem.mp h0b)), rotAux]
      simp [c₀, h0b, restCard]
  have hph : headPhaseMod4Z8Spec β =
      (s0Z8 + (c₀ : ZMod 8) * stepZ8) + (restCard : ZMod 8) * stepZ8 := by
    unfold headPhaseMod4Z8Spec
    rw [henβ]
    change (if (!true) = true then (0 : ZMod 8) else (if (β (wSlot0Core rCore) == 1) = true
      then 4 else 0) + ((headHitSetSpec β).card : ZMod 8) * (2 + if (β (wHeadThresh rCore) ==
      1) = true then 4 else 0)) = _
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), hs0_β, hth_β, hcard]
    dsimp only [s0Z8, s0, stepZ8]; push_cast; ring
  rw [hph, omega8_pow_add_nat_mul]
  dsimp only [cPhase, ζ]
  rw [pow_eq_newton_sum_219 _ hrest_lt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_; ring
set_option exponentiation.threshold 256 in
private theorem head_slice_dHeadMod4_eq_newton_sum (s110 : Fin (2 ^ 110)) (u₀ : Fin (2 ^ 18))
    (zRef : Fin (2 ^ systemQubits)) (hzRef_ext : (rEl_sp 0).extractIndex zRef = u₀)
    (hen : ∀ z, headEnBoolSpec (βLift s110 z) = true) : ∃ (yT : Fin 3 → Fin 64)
    (cPhase ζ : ℂ), (fun z ↦ if (rEl_sp 0).extractIndex z = u₀ then dHeadMod4 (liftSys110 s110
    z) else 0) = fun z ↦ ∑ k ∈ Finset.range 219, (cPhase * (ζ - 1) ^ k) * ((if (rEl_sp
    0).extractIndex z = u₀ then (1 : ℂ) else 0) * ((hitCountRest yT z).choose k : ℂ)) := by
  rcases headPhaseMod4_bits_eq_newton (βLift s110 zRef) with ⟨yT, cPhase, ζ, hbits⟩
  refine ⟨yT, cPhase, ζ, funext fun z ↦ ?_⟩
  by_cases hzu : (rEl_sp 0).extractIndex z = u₀
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hzu)]
    have hd : dHeadMod4 (liftSys110 s110 z) = omega8 ^ (headPhaseMod4Z8Spec (βLift s110 z)).val :=
      dHeadBits_eq_of_headEn (hen z)
    rw [hd, hbits (βLift s110 z) (slotCoordSys z) (hen z)
      (fun q hq ↦ βLift_high_eq s110 z zRef hq)
      (slotSubGridCoord64_βLift_eq s110 z)
      (by
        rw [slotSubGridCoord64_βLift_eq s110 zRef 0];
          exact slotCoordSys_eq_of_extractIndex_eq
            (hzu.trans hzRef_ext.symm))]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [ite_eq_left_of_eq_true _ _ (eq_true hzu), one_mul]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hzu), Finset.sum_eq_zero]
    intro k _
    rw [ite_eq_right_of_eq_false _ _ (eq_false hzu), zero_mul, mul_zero]
set_option exponentiation.threshold 256 in
private theorem head_slice_k1_mapsToKrylov3 (spinUp : Finset (Fin numElectrons))
    (c' : Configuration) (s110 : Fin (2 ^ 110)) (eAnc : Fin numElectrons) (u₀ : Fin (2 ^ 18))
    (yT : Fin 3 → Fin 64) : CoreMapsToKrylov3On ((rSysInFullSysCore 80).embedMatrix
    (swappedElecFermProj spinUp (Equiv.swap 0 eAnc))) ((rSysInFullSysCore 80).embedMatrix
    ((elecSysProd (vRemElec c' s110)).1ᴴ * Matrix.diagonal (fun z ↦ (if (rEl_sp
    0).extractIndex z = u₀ then (1 : ℂ) else 0) * (hitCountRest yT z : ℂ)) * (elecSysProd
    (vRemElec c' s110)).1)) := by
  have h1_fn : (fun z ↦ (if (rEl_sp 0).extractIndex z = u₀ then (1 : ℂ) else 0) *
      (hitCountRest yT z : ℂ)) = fun z ↦
      (if (rEl_sp 0).extractIndex z = u₀ then (1 : ℂ) else 0) * ∑ e ∈ Finset.univ.erase
      (0 : Fin numElectrons), if slotCoordSys z e = yT then (1 : ℂ) else 0 := by
    funext z; rw [hitCountRest_cast_eq_sum]
  rw [h1_fn, diagonal_mul_finset_sum, embedMatrix_conj_finset_sum]
  refine CoreMapsToKrylov3On.finset_sum _ _ fun e _ ↦ ?_
  have hS2 : ({(0 : Fin numElectrons), e} : Finset (Fin numElectrons)).card ≤ 3 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  refine conj_diag_le3_mapsToKrylov3 spinUp c' s110 eAnc
    (S := {(0 : Fin numElectrons), e}) hS2 _ fun z₁ z₂ hS ↦ ?_
  have h0 := hS 0 (Finset.mem_insert_self _ _)
  have he := slotCoordSys_eq_of_extractIndex_eq
    (hS e (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  rw [h0, he]
set_option exponentiation.threshold 256 in
private theorem head_slice_k2sq_mapsToKrylov3 (spinUp : Finset (Fin numElectrons))
    (c' : Configuration) (s110 : Fin (2 ^ 110)) (eAnc : Fin numElectrons) (u₀ : Fin (2 ^ 18))
    (yT : Fin 3 → Fin 64) : CoreMapsToKrylov3On ((rSysInFullSysCore 80).embedMatrix
    (swappedElecFermProj spinUp (Equiv.swap 0 eAnc))) ((rSysInFullSysCore 80).embedMatrix
    ((elecSysProd (vRemElec c' s110)).1ᴴ * Matrix.diagonal (fun z ↦ (if (rEl_sp
    0).extractIndex z = u₀ then (1 : ℂ) else 0) * ((hitCountRest yT z : ℂ) * (hitCountRest yT
    z : ℂ))) * (elecSysProd (vRemElec c' s110)).1)) := by
  have h2_fn : (fun z ↦ (if (rEl_sp 0).extractIndex z = u₀ then (1 : ℂ) else 0) *
      ((hitCountRest yT z : ℂ) * (hitCountRest yT z : ℂ))) = fun z ↦
      (if (rEl_sp 0).extractIndex z = u₀ then (1 : ℂ) else 0) * ((∑ e ∈ Finset.univ.erase (0 :
      Fin numElectrons), if slotCoordSys z e = yT then (1 : ℂ) else 0) * (∑ e ∈
      Finset.univ.erase (0 : Fin numElectrons), if slotCoordSys z e = yT then (1 : ℂ) else 0))
      := by
    funext z; rw [hitCountRest_cast_eq_sum]
  rw [h2_fn, diagonal_mul_sq_finset_sum, embedMatrix_conj_finset_sum]
  refine CoreMapsToKrylov3On.finset_sum _ _ fun e₁ _ ↦ ?_
  rw [embedMatrix_conj_finset_sum]
  refine CoreMapsToKrylov3On.finset_sum _ _ fun e₂ _ ↦ ?_
  have hS3 : ({(0 : Fin numElectrons), e₁, e₂} : Finset (Fin numElectrons)).card ≤ 3 :=
    le_trans (Finset.card_insert_le _ _)
      (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))
  refine conj_diag_le3_mapsToKrylov3 spinUp c' s110 eAnc
    (S := {(0 : Fin numElectrons), e₁, e₂}) hS3 _ fun z₁ z₂ hS ↦ ?_
  have h0 := hS 0 (Finset.mem_insert_self _ _)
  have he1 := slotCoordSys_eq_of_extractIndex_eq
    (hS e₁ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have he2 := slotCoordSys_eq_of_extractIndex_eq
    (hS e₂ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
  rw [h0, he1, he2]
set_option exponentiation.threshold 256 in
private theorem head_slice_kge3_mapsToKrylov3 (spinUp : Finset (Fin numElectrons))
    (c' : Configuration) (s110 : Fin (2 ^ 110)) (eAnc : Fin numElectrons) (u₀ : Fin (2 ^ 18))
    (yT : Fin 3 → Fin 64) (m : ℕ) : CoreMapsToKrylov3On ((rSysInFullSysCore 80).embedMatrix
    (swappedElecFermProj spinUp (Equiv.swap 0 eAnc))) ((rSysInFullSysCore 80).embedMatrix
    ((elecSysProd (vRemElec c' s110)).1ᴴ * Matrix.diagonal (fun z ↦ (if (rEl_sp
    0).extractIndex z = u₀ then (1 : ℂ) else 0) * ((hitCountRest yT z).choose (3 + m) : ℂ)) *
    (elecSysProd (vRemElec c' s110)).1)) := by
  rcases elecSysProd_conj_hitCountRest c' s110 yT with ⟨hH_eq, hnorm⟩
  let χ : Fin (2 ^ 18) → ℂ := fun v ↦ star ((wRem18 c' s110).1 (slotCoord18Equiv.symm yT) v)
  have hzero : (rSysInFullSysCore 80).embedMatrix ((elecSysProd (vRemElec c' s110)).1ᴴ *
      Matrix.diagonal (fun z ↦ (if (rEl_sp 0).extractIndex z = u₀ then (1 : ℂ) else 0) *
      ((hitCountRest yT z).choose (3 + m) : ℂ)) * (elecSysProd (vRemElec c' s110)).1) *
      (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 eAnc)) = 0
      := by
    rw [conj_diag_choose_three_add_eq (elecSysProd (vRemElec c' s110))
      (nSub_sp χ (Finset.univ.erase 0))
      (fun z ↦ if (rEl_sp 0).extractIndex z = u₀ then (1 : ℂ) else 0)
      (hitCountRest yT) m hH_eq]
    exact embedMatrix_mul_right_zero (rSysInFullSysCore 80) _ _ _
      (nSub_cubic_mul_swappedElecFermProj_zero hnorm spinUp (Finset.univ.erase 0)
        (Equiv.swap 0 eAnc))
  unfold CoreMapsToKrylov3On
  rw [hzero, Matrix.mul_zero]
set_option exponentiation.threshold 256 in
theorem head_slice_mapsToKrylov3 (spinUp : Finset (Fin numElectrons)) (c' : Configuration)
    (s110 : Fin (2 ^ 110)) (eAnc : Fin numElectrons) : CoreMapsToKrylov3On
    ((rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 eAnc)))
    ((rSysInFullSysCore 80).embedMatrix ((elecSysProd (vRemElec c' s110)).1ᴴ *
    Matrix.diagonal (fun z ↦ dHeadMod4 (liftSys110 s110 z)) * (elecSysProd (vRemElec c'
    s110)).1)) := by
  by_cases hen0 : headEnBoolSpec (βLift s110 0) = true
  · have hen : ∀ z, headEnBoolSpec (βLift s110 z) = true :=
      fun z ↦ (headEnBoolSpec_βLift_eq s110 z 0).trans hen0
    rw [diagonal_eq_sum_proj (rEl_sp 0).extractIndex (fun z ↦ dHeadMod4 (liftSys110 s110 z)),
      embedMatrix_conj_finset_sum]
    refine CoreMapsToKrylov3On.finset_sum _ _ fun u₀ _ ↦ ?_
    rcases exists_zRef_extractIndex_zero u₀ with ⟨zRef, hzRef_ext⟩
    rcases head_slice_dHeadMod4_eq_newton_sum s110 u₀ zRef hzRef_ext hen with
      ⟨yT, cPhase, ζ, hslice_fn⟩
    rw [hslice_fn, diagonal_finset_sum_smul, embedMatrix_conj_finset_sum]
    refine CoreMapsToKrylov3On.finset_sum _ _ fun k hk219 ↦ ?_
    rw [embedMatrix_conj_smul]
    refine CoreMapsToKrylov3On.smul _ ?_
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ (∃ m < 216, k = 3 + m) := by
      rw [Finset.mem_range] at hk219
      rcases lt_or_ge k 3 with hlt3 | hge3
      · omega
      · exact Or.inr (Or.inr (Or.inr ⟨k - 3, by omega, by omega⟩))
    rcases hk_cases with rfl | rfl | rfl | ⟨m, _, rfl⟩
    · simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
      have hS0 : ({(0 : Fin numElectrons)} : Finset (Fin numElectrons)).card ≤ 3 := by simp
      refine conj_diag_le3_mapsToKrylov3 spinUp c' s110 eAnc
        (S := {(0 : Fin numElectrons)}) hS0 _ fun z₁ z₂ hS ↦ ?_
      rw [hS 0 (Finset.mem_singleton_self 0)]
    · simp only [Nat.choose_one_right]
      exact head_slice_k1_mapsToKrylov3 spinUp c' s110 eAnc u₀ yT
    · rw [diagonal_choose_two_eq, embedMatrix_conj_add, embedMatrix_conj_smul,
      embedMatrix_conj_smul]
      exact ((head_slice_k2sq_mapsToKrylov3 spinUp c' s110 eAnc u₀ yT).smul (2 : ℂ)⁻¹).add
        ((head_slice_k1_mapsToKrylov3 spinUp c' s110 eAnc u₀ yT).smul (-(2 : ℂ)⁻¹))
    · exact head_slice_kge3_mapsToKrylov3 spinUp c' s110 eAnc u₀ yT m
  · have hd0 : (fun z ↦ dHeadMod4 (liftSys110 s110 z)) = fun _ ↦ (0 : ℂ) := by
      funext z; unfold dHeadMod4 dHeadBits
      change (if headEnBoolSpec (βLift s110 z) = true then _ else (0 : ℂ)) = 0
      rw [headEnBoolSpec_βLift_eq s110 z 0, ite_eq_right_of_eq_false _ _ (eq_false hen0)]
    rw [hd0, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul, QRegister.embedMatrix_zero]
    exact CoreMapsToKrylov3On.zero _
theorem uRemCore_conj_uPosPhase80Mod4Eff_mapsToKrylov3 (spinUp : Finset (Fin numElectrons))
    {qft : FullSysQft654Bundle} (hqft : qft.uQft654 * uPre654 = qft64Ideal654Unitary)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (c' : Configuration) (eAnc : Fin numElectrons) : CoreMapsToKrylov3On ((rSysInFullSysCore
    80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 eAnc))) ((uRemCore qft c').1ᴴ *
    (uPosPhase80Mod4Eff tailSign tailMag30).1 * (uRemCore qft c').1) := by
  let P_sf := (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 eAnc))
  have hsplit : (uRemCore qft c').1ᴴ * (uPosPhase80Mod4Eff tailSign tailMag30).1 *
      (uRemCore qft c').1 =
      (uRemCore qft c').1ᴴ * Matrix.diagonal (dTailMod4 tailSign tailMag30) * (uRemCore qft c').1 +
        uXThCore.1 * ((uRemCore qft c').1ᴴ * Matrix.diagonal dHeadMod4 * (uRemCore qft c').1) := by
    rw [uPosPhase80Mod4Eff_eq_tail_add_head, Matrix.mul_add, Matrix.add_mul]
    refine congrArg ((uRemCore qft c').1ᴴ * Matrix.diagonal (dTailMod4 tailSign tailMag30) *
      (uRemCore qft c').1 + ·) ?_
    calc (uRemCore qft c').1ᴴ * (uXThCore.1 * Matrix.diagonal dHeadMod4) * (uRemCore qft c').1
      _ = ((uRemCore qft c').1ᴴ * uXThCore.1) * Matrix.diagonal dHeadMod4 * (uRemCore qft c').1 :=
        by
          simp only [Matrix.mul_assoc]
      _ = uXThCore.1 * ((uRemCore qft c').1ᴴ * Matrix.diagonal dHeadMod4 * (uRemCore qft c').1) :=
        by
          rw [uRemCore_conjTranspose_comm_uXThCore]; simp only [Matrix.mul_assoc]
  rw [hsplit]
  have hslice_lift : ∀ (dCore : Fin (2 ^ (fullSysCoreWires 80)) → ℂ),
      (∀ s110 : Fin (2 ^ 110),
        CoreMapsToKrylov3On P_sf
          ((rSysInFullSysCore 80).embedMatrix
            ((elecSysProd (vRemElec c' s110)).1ᴴ *
              Matrix.diagonal (fun z ↦ dCore (liftSys110 s110 z)) *
              (elecSysProd (vRemElec c' s110)).1))) →
      CoreMapsToKrylov3On P_sf
        ((uRemCore qft c').1ᴴ * Matrix.diagonal dCore * (uRemCore qft c').1) := fun dCore hS ↦ by
    set M := (uRemCore qft c').1ᴴ * Matrix.diagonal dCore * (uRemCore qft c').1
    have hM1 : M = M * ∑ s110 : Fin (2 ^ 110), rProjAnc110.basisOutcomeProjector s110 := by
      rw [QRegister.sum_basisOutcomeProjector, Matrix.mul_one]
    rw [hM1, Matrix.mul_sum]
    refine CoreMapsToKrylov3On.finset_sum _ _ fun s110 _ ↦ ?_
    rw [uRemCore_conj_diagonal_mul_rProjAnc110 hqft c' dCore s110]
    unfold CoreMapsToKrylov3On
    rw [Matrix.mul_assoc _ (rProjAnc110.basisOutcomeProjector s110) P_sf,
      ← swappedElecFermProj_embed_comm_rProjAnc110 spinUp eAnc s110]
    exact (hS s110).mul_right (rProjAnc110.basisOutcomeProjector s110)
  refine (hslice_lift _ fun s110 ↦
    tail_slice_mapsToKrylov3 spinUp tailSign tailMag30 c' s110 eAnc).add ?_
  exact CoreMapsToKrylov3On.preserves_mul_left preservesCoreBadElec_uXThCore
    (hslice_lift _ fun s110 ↦ head_slice_mapsToKrylov3 spinUp c' s110 eAnc)
private theorem mulVec_ket_basisBits_eq_apply {N : ℕ} (A B : Operator (2 ^ N))
    (y x : Fin (2 ^ N)) (h : A.mulVec (ket (basisBits N x)) = B.mulVec (ket (basisBits N x)))
    : A y x = B y x := by
  have hy := congrFun h y
  rw [msc_ket_eq_single, basisBitsEquiv_symm_basisBits,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hy
  dsimp only [Matrix.col_apply] at hy
  exact hy
private theorem mul_basisOutcomeProjector_eq_of_mulVec_ket {K N : ℕ} (A B : Operator (2 ^ N))
    (r : QRegister K N) (a : Fin (2 ^ K)) (h : ∀ x : Fin (2 ^ N), r.extractIndex x = a →
    A.mulVec (ket (basisBits N x)) = B.mulVec (ket (basisBits N x))) : A *
    r.basisOutcomeProjector a = B * r.basisOutcomeProjector a := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal]
  refine Matrix.ext fun y x ↦ ?_
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases hx : r.extractIndex x = a
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hx), mul_one, mul_one]
    exact mulVec_ket_basisBits_eq_apply A B y x (h x hx)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hx), mul_zero, mul_zero]
private theorem fixesLow3924_of_mulVec_ket_embedUnitary {K N : ℕ} (hN : 3924 ≤ N)
    (A : Operator (2 ^ N)) (r : QRegister K N) (hhi : IsHigh3924Reg r)
    (W : Fin (2 ^ N) → Unitary (2 ^ K)) (hket : ∀ x : Fin (2 ^ N), A.mulVec (ket (basisBits N
    x)) = (r.embedUnitary (W x)).1.mulVec (ket (basisBits N x))) : FixesLow3924 hN A :=
  fun y x hne ↦ by
    have hyx := mulVec_ket_basisBits_eq_apply A (r.embedUnitary (W x)).1 y x (hket x)
    rw [hyx, QRegister.embedUnitary_val] at hne
    exact fixesLow3924_embedMatrix_high hN hhi (W x).1 y x hne
set_option exponentiation.threshold 256 in
private theorem fixesLow3924_uProj3DCutCore_gen {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    FixesLow3924
      (by
        dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits,
          projectileBits]; omega :
        3924 ≤ fullSysCoreWires mPayload)
      (uProj3DCutCore hm).1 := by
  have h3924_m : 3924 ≤ fullSysCoreWires mPayload := by
    dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]; omega
  have h1D : ∀ w : Fin 3, FixesLow3924 h3924_m (uProj3DCut1DCore hm w).1 :=
    fun w ↦ fixesLow3924_of_mulVec_ket_embedUnitary h3924_m
      (uProj3DCut1DCore hm w).1
      (rProjAxis (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload)) w)
      (fun k ↦ (rProjAxis_wire_bounds (mPayload := mPayload) w k).1)
      (fun x ↦ wCutAxes hm (basisBits (fullSysCoreWires mPayload) x) w)
      (fun x ↦ uProj3DCut1DCore_mulVec_ket hm w (basisBits (fullSysCoreWires mPayload) x))
  unfold uProj3DCutCore; simp only [Submonoid.coe_mul]
  exact (h1D 0).mul ((h1D 1).mul (h1D 2))
set_option exponentiation.threshold 256 in
theorem fixesLow3924_uProj3DCutCore : FixesLow3924 h3924_core
    (uProj3DCutCore pos24_22_le_80).1 := fixesLow3924_uProj3DCutCore_gen pos24_22_le_80
def anc86BitFn (a86 : Fin (2 ^ 86)) : BitAssignment (fullSysCoreWires 80) :=
  fun q ↦ if h : 3948 ≤ q.val then
    basisBits 86 a86 ⟨q.val - 3948, by
      have := q.isLt
      dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits] at this
      omega⟩
  else 0
theorem basisBits_eq_anc86BitFn_of_extract {x : Fin (2 ^ (fullSysCoreWires 80))}
    {a86 : Fin (2 ^ 86)} (hx : rAncFlag80.extractIndex x = a86)
    {q : Wire (fullSysCoreWires 80)} (hq : 3948 ≤ q.val) :
    basisBits (fullSysCoreWires 80) x q = anc86BitFn a86 q := by
  subst hx
  unfold anc86BitFn
  rw [dite_eq_left_of_eq_true (eq_true hq), QRegister.basisBits_extractIndex]
  exact congrArg (basisBits _ x) (Fin.ext (by
    simp only [rAncFlag80, qreg_block_apply]; omega))
def eAncOf86 (a86 : Fin (2 ^ 86)) : Fin numElectrons :=
  coinBarrelIdxFast (le_refl 80) (anc86BitFn a86)
theorem coinBarrelIdxFast_congr_ge3948 {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (hHigh : ∀ w : Wire (fullSysCoreWires 80), 3948 ≤ w.val → γ₁ w = γ₂ w) :
    coinBarrelIdxFast (le_refl 80) γ₁ = coinBarrelIdxFast (le_refl 80) γ₂ := by
  have hCore : fullSysCoreWires 80 = 4034 := by decide
  have hs1 : γ₁ (iSlot1 80) = γ₂ (iSlot1 80) := hHigh _ (by decide)
  have hs2 : γ₁ (iSlot2 80) = γ₂ (iSlot2 80) := hHigh _ (by decide)
  have hu8 : (fun j : Fin 8 ↦ γ₁ ⟨3968 + j.val, by omega⟩) =
      (fun j : Fin 8 ↦ γ₂ ⟨3968 + j.val, by omega⟩) :=
    funext fun j ↦ hHigh _ (by dsimp; omega)
  have hu36 : (fun j : Fin 36 ↦ γ₁ ⟨3954 + j.val, by omega⟩) =
      (fun j : Fin 36 ↦ γ₂ ⟨3954 + j.val, by omega⟩) :=
    funext fun j ↦ hHigh _ (by dsimp; omega)
  have hbPar : γ₁ ⟨3990, by omega⟩ = γ₂ ⟨3990, by omega⟩ := hHigh _ (by dsimp; omega)
  dsimp only [coinBarrelIdxFast]
  simp only [hs1, hs2, hu8, hu36, hbPar]
theorem coinBarrelIdxFast_eq_eAncOf86 {x : Fin (2 ^ (fullSysCoreWires 80))}
    {a86 : Fin (2 ^ 86)} (hx : rAncFlag80.extractIndex x = a86) :
    coinBarrelIdxFast (le_refl 80) (basisBits (fullSysCoreWires 80) x) = eAncOf86 a86 :=
  coinBarrelIdxFast_congr_ge3948 fun _ hw ↦ basisBits_eq_anc86BitFn_of_extract hx hw
set_option exponentiation.threshold 256 in
theorem uBarrelFast_mul_rAncFlag80 (a86 : Fin (2 ^ 86)) : (uBarrelFast (le_refl 80)).1 *
    rAncFlag80.basisOutcomeProjector a86 = (rSysInFullSysCore 80).embedMatrix
    (permutationUnitary (permElectron (Equiv.swap 0 (eAncOf86 a86)))).1 *
    rAncFlag80.basisOutcomeProjector a86 := by
  let g := Equiv.swap (0 : Fin numElectrons) (eAncOf86 a86)
  have hpe_fwd : (permutationUnitary (permElectron g)).1 = (fwdPermUnitary (permElectron g)).1 :=
    Matrix.ext fun i j ↦ by rw [permutationUnitary_entry, fwdPermUnitary_apply]
  have hemb_fwd : (rSysInFullSysCore 80).embedMatrix (permutationUnitary (permElectron g)).1 =
      (fwdPermUnitary (embedRegPerm (rSysInFullSysCore 80) (permElectron g))).1 := by
    rw [hpe_fwd, ← QRegister.embedUnitary_val,
      embedUnitary_fwdPermUnitary_slot2 (rSysInFullSysCore 80) (permElectron g)]
  rw [hemb_fwd, uBarrelFast, QRegister.basisOutcomeProjector_eq_diagonal]
  refine Matrix.ext fun y x ↦ ?_
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, permutationUnitary_entry, fwdPermUnitary_apply]
  by_cases hx : rAncFlag80.extractIndex x = a86
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hx), mul_one, mul_one]
    have hperm_eq : coinBarrelPermFast (le_refl 80) x =
        embedRegPerm (rSysInFullSysCore 80) (permElectron g) x := by
      apply (basisBitsEquiv (fullSysCoreWires 80)).injective; funext q
      change basisBits (fullSysCoreWires 80) _ q = basisBits (fullSysCoreWires 80) _ q
      have hPoly {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
          (c : Fin (2 ^ fullSysCoreWires mPayload)) :
          basisBits (fullSysCoreWires mPayload) (coinBarrelPermFast hmPay c) =
            coinBarrelBitFnFast hmPay (basisBits (fullSysCoreWires mPayload) c) :=
        (basisBitsEquiv _).apply_symm_apply _
      have hL_fn := congrFun (hPoly (le_refl 80) x) q
      by_cases hqSys : q.val < 3948
      · have hmem : q = (rSysInFullSysCore 80) ⟨q.val, hqSys⟩ :=
          Fin.ext (by simp only [rSysInFullSysCore, qreg_block_apply]; omega)
        have hR : basisBits (fullSysCoreWires 80)
            (embedRegPerm (rSysInFullSysCore 80) (permElectron g) x) q =
            basisBits systemQubits (permElectron g ((rSysInFullSysCore 80).extractIndex x))
              ⟨q.val, hqSys⟩ := by
          conv_lhs => rw [hmem]
          rw [← QRegister.basisBits_extractIndex]; dsimp only [embedRegPerm, Equiv.coe_fn_mk]
          rw [QRegister.extractIndex_replaceIndex]
        by_cases hq3924 : q.val < 3924
        · have hlow := congrFun (low3924Bits_extractIndex_coinBarrelPermFast_eq_permElectron
            (le_refl 80) x) ⟨q.val, hq3924⟩
          rw [coinBarrelIdxFast_eq_eAncOf86 hx] at hlow
          change basisBits systemQubits ((rSysInFullSysCore 80).extractIndex
            (coinBarrelPermFast (le_refl 80) x)) ⟨q.val, hqSys⟩ = basisBits systemQubits
            (permElectron g ((rSysInFullSysCore 80).extractIndex x)) ⟨q.val, hqSys⟩ at hlow
          rw [QRegister.basisBits_extractIndex, ← hmem] at hlow
          exact hlow.trans hR.symm
        · rw [hL_fn, coinBarrelBitFnFast_high (le_refl 80) _ q (by omega), hR,
            permElectron, basisBits_permElectron]
          have hpw : permElectronWire g ⟨q.val, hqSys⟩ = ⟨q.val, hqSys⟩ := by
            apply Fin.ext; change (permElectronWireFun g ⟨q.val, hqSys⟩).val = q.val
            unfold permElectronWireFun
            rw [dite_eq_right_of_eq_false (eq_false hq3924)]
          rw [hpw, QRegister.basisBits_extractIndex, ← hmem]
      · have hnot : q ∉ Set.range (rSysInFullSysCore 80).wires := fun ⟨j, hj⟩ ↦ hqSys (by
          have hv := congrArg Fin.val hj; have := j.isLt
          simp only [rSysInFullSysCore, qreg_block_apply,
            systemQubits, numElectrons, electronBits, projectileBits] at hv this
          omega)
        rw [hL_fn, coinBarrelBitFnFast_high (le_refl 80) _ q (by omega)]
        dsimp only [embedRegPerm, Equiv.coe_fn_mk]
        rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ q hnot]
    rw [hperm_eq]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hx), mul_zero, mul_zero]
set_option exponentiation.threshold 256 in
theorem uProj3DCutCore_mul_rAncFlag80 (a86 : Fin (2 ^ 86)) :
    (uProj3DCutCore pos24_22_le_80).1 * rAncFlag80.basisOutcomeProjector a86 =
      (uProjAxes3D 80 (wCutAxes pos24_22_le_80 (anc86BitFn a86))).1 *
        rAncFlag80.basisOutcomeProjector a86 :=
  mul_basisOutcomeProjector_eq_of_mulVec_ket _ _ rAncFlag80 a86 fun x hx ↦ by
    have hhi : ∀ q : Fin (fullSysCoreWires 80), 3948 ≤ q.val →
        basisBits (fullSysCoreWires 80) x q = anc86BitFn a86 q :=
      fun q hq ↦ basisBits_eq_anc86BitFn_of_extract hx hq
    rw [← wCutAxes_eq_of_high_eq pos24_22_le_80 hhi]
    exact uProj3DCutCore_mulVec_ket pos24_22_le_80 (basisBits (fullSysCoreWires 80) x)
theorem uProjAxes3D_comm_rAncFlag80_and_swappedElecFermProj
    (spinUp : Finset (Fin numElectrons)) (W : Fin 3 → Unitary 256) (a86 : Fin (2 ^ 86))
    (e : Fin numElectrons) : ((uProjAxes3D 80 W).1 * rAncFlag80.basisOutcomeProjector a86 =
    rAncFlag80.basisOutcomeProjector a86 * (uProjAxes3D 80 W).1) ∧ ((uProjAxes3D 80 W).1 *
    (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 e)) =
    (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 e)) *
    (uProjAxes3D 80 W).1) := by
  have hAx_anc : ∀ w : Fin 3,
      ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 *
          rAncFlag80.basisOutcomeProjector a86 =
        rAncFlag80.basisOutcomeProjector a86 *
          ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 := fun w ↦ by
    rw [QRegister.embedUnitary_val]
    refine QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _ ?_ _ _
    rw [QRegister.disjoint_iff]; intro i j hij
    have hb := rProjAxis_wire_bounds (mPayload := 80) w i
    have hv := congrArg Fin.val hij
    simp only [rAncFlag80, qreg_block_apply] at hv; omega
  have hAx_sf : ∀ w : Fin 3,
      ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 *
          (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 e)) =
        (rSysInFullSysCore 80).embedMatrix (swappedElecFermProj spinUp (Equiv.swap 0 e)) *
          ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 := fun w ↦ by
    let subAx : QRegister 8 24 :=
      { wires :=
        { toFun := fun i ↦
            ⟨((rProjAxis (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))
              w).wires i).val - 3924, by
              have hb := rProjAxis_wire_bounds (mPayload := 80) w i; omega⟩
          inj' := fun i₁ i₂ h ↦ by
            have hb1 := rProjAxis_wire_bounds (mPayload := 80) w i₁
            have hb2 := rProjAxis_wire_bounds (mPayload := 80) w i₂
            have hv := congrArg Fin.val h; dsimp at hv
            exact (rProjAxis (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires 80))
              w).wires.injective
              (Fin.ext (by omega)) } }
    have hreg : ((rSysInFullSysCore 80).compose rProj24_sp).compose subAx =
        rProjAxis (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)) w := by
      apply QRegister.ext; apply Function.Embedding.ext; intro i
      have hb := rProjAxis_wire_bounds (mPayload := 80) w i
      apply Fin.ext
      simp only [QRegister.compose_apply, rSysInFullSysCore, rProj24_sp, qreg_block_apply, subAx]
      dsimp; omega
    rw [QRegister.embedUnitary_val, ← hreg, QRegister.embedMatrix_compose,
      QRegister.embedMatrix_compose, ← QRegister.embedMatrix_mul,
      ← swappedElecFermProj_swap0_comm_rProj24, QRegister.embedMatrix_mul]
  refine ⟨?_, ?_⟩
  · unfold uProjAxes3D; simp only [Submonoid.coe_mul]
    exact msc_mul2_comm _ _ _ (hAx_anc 0) (msc_mul2_comm _ _ _ (hAx_anc 1) (hAx_anc 2))
  · unfold uProjAxes3D; simp only [Submonoid.coe_mul]
    exact msc_mul2_comm _ _ _ (hAx_sf 0) (msc_mul2_comm _ _ _ (hAx_sf 1) (hAx_sf 2))
theorem selectPos_slice_reassoc {D : ℕ} (Mrem Pcut B P86 P_ef P_perm P_sf U_ax : Operator D)
    (hB : B * P86 = P_perm * P86) (hPperm : P_perm * P86 = P86 * P_perm)
    (hCut : Pcut * P86 = U_ax * P86) (hpef : P_perm * P_ef = P_sf)
    (hPsf : P_sf * P86 = P86 * P_sf) (hUax : U_ax * P_sf = P_sf * U_ax) :
    ((Mrem * Pcut * B) * P86) * P_ef = Mrem * (P_sf * (U_ax * P86)) := by
  rw [Matrix.mul_assoc (Mrem * Pcut) B P86, hB, hPperm,
    ← Matrix.mul_assoc (Mrem * Pcut) P86 P_perm, Matrix.mul_assoc Mrem Pcut P86, hCut,
    Matrix.mul_assoc _ P_perm P_ef, hpef, Matrix.mul_assoc Mrem (U_ax * P86) P_sf,
    Matrix.mul_assoc U_ax P86 P_sf, ← hPsf, ← Matrix.mul_assoc U_ax P_sf P86,
    hUax, Matrix.mul_assoc P_sf U_ax P86]
/-- Exact `CoreFermMapsToKrylov3` closure for `fullSysSelectPosUnitary qft selOra c` under
`SelectOraHypothesisOfTrunc` and `uPosPhase80Mod4Eff`. -/
theorem coreFermMapsToKrylov3_selectPos_of_oraHyp_mod4Eff (spinUp : Finset (Fin numElectrons))
    {t2Ctrl t2Cat : ℕ} {truncFn : Configuration → Configuration} {qft : FullSysQft654Bundle}
    (hqft : qft.uQft654 * uPre654 = qft64Ideal654Unitary)
    {selOra : FullSysSelectOracleBundle 80 48}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat} {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfTrunc truncFn selOra leaf2 ora3)
    {tailSign : Fin orbitCount47905 → Bool} {tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)}
    (hPos0 : leaf2.uPosPhase0 = uPosPhase80Mod4Eff tailSign tailMag30) (c : Configuration) :
    CoreFermMapsToKrylov3 spinUp (fullSysSelectPosUnitary qft selOra c).1 := by
  have hmEq : selOra.hmPay = pos24_6_le_80 := Subsingleton.elim _ _
  have hTwFactor : fullSysQftCoreUnitary selOra.hmPay qft * selOra.uTwist c =
      uRemCore qft (truncFn c) * (uProj3DCutCore pos24_22_le_80 * uBarrelFast (le_refl 80)) := by
    rw [hmEq, fullSysQftCoreUnitary, hOra.hTw c, uVepFusedTwistRestCut80_eq_bridge]
    unfold uVepFusedTwistRestCut uVepTwistRestCut uRemCore
    have hm6eq : hm6_of_hm22 pos24_22_le_80 = pos24_6_le_80 := Subsingleton.elim _ _
    rw [hm6eq]
    apply Subtype.ext
    simp only [Submonoid.coe_mul, QRegister.embedUnitary_val,
      QRegister.embedMatrix_mul, Matrix.mul_assoc]
  unfold fullSysSelectPosUnitary
  rw [hTwFactor, hOra.hPosEq c, hPos0, unitaryConj_val, Submonoid.coe_mul, Submonoid.coe_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  set B := (uBarrelFast (le_refl 80)).1
  set Pcut := (uProj3DCutCore pos24_22_le_80).1
  set Mrem := (uRemCore qft (truncFn c)).1ᴴ *
    (uPosPhase80Mod4Eff tailSign tailMag30).1 * (uRemCore qft (truncFn c)).1
  rw [show (Bᴴ * Pcutᴴ) * (uRemCore qft (truncFn c)).1ᴴ *
      (uPosPhase80Mod4Eff tailSign tailMag30).1 * ((uRemCore qft (truncFn c)).1 * (Pcut * B)) =
      Bᴴ * (Pcutᴴ * (Mrem * Pcut * B)) by dsimp only [Mrem]; simp only [Matrix.mul_assoc]]
  unfold CoreFermMapsToKrylov3
  refine CoreMapsToKrylov3On.preserves_mul_left
    (by dsimp only [B]; rw [uBarrelFast_conjTranspose]
        exact preservesCoreBadElec_uBarrelFast (le_refl 80))
    (CoreMapsToKrylov3On.preserves_mul_left (preservesCoreBadElec_of_fixesLow3924
      h3924_core fixesLow3924_uProj3DCutCore.conjTranspose) ?_)
  rw [← elecFermionicProjector_mul_fermionicProjector, QRegister.embedMatrix_mul]
  refine CoreMapsToKrylov3On.mul_right _ ?_
  set P_ef := (rSysInFullSysCore 80).embedMatrix (elecFermionicProjector spinUp)
  rw [show Mrem * Pcut * B = (Mrem * Pcut * B) *
      ∑ a86 : Fin (2 ^ 86), rAncFlag80.basisOutcomeProjector a86
      by rw [QRegister.sum_basisOutcomeProjector, Matrix.mul_one], Matrix.mul_sum]
  refine CoreMapsToKrylov3On.finset_sum _ _ fun a86 _ ↦ ?_
  let e := eAncOf86 a86
  let P86 := rAncFlag80.basisOutcomeProjector a86
  let P_perm := (rSysInFullSysCore 80).embedMatrix
    (permutationUnitary (permElectron (Equiv.swap 0 e))).1
  let P_sf := (rSysInFullSysCore 80).embedMatrix
    (swappedElecFermProj spinUp (Equiv.swap 0 e))
  let U_ax := (uProjAxes3D 80 (wCutAxes pos24_22_le_80 (anc86BitFn a86))).1
  have hPperm_anc : P_perm * P86 = P86 * P_perm :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      (rSysInFullSysCore 80) rAncFlag80 rSysInFullSysCore80_disjoint_rAncFlag80 _ _
  have hPsf_anc : P_sf * P86 = P86 * P_sf :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      (rSysInFullSysCore 80) rAncFlag80 rSysInFullSysCore80_disjoint_rAncFlag80 _ _
  rcases uProjAxes3D_comm_rAncFlag80_and_swappedElecFermProj spinUp
    (wCutAxes pos24_22_le_80 (anc86BitFn a86)) a86 e with ⟨_, hUax_sf⟩
  have hperm_ef : P_perm * P_ef = P_sf := by
    dsimp only [P_perm, P_ef, P_sf, swappedElecFermProj]
    rw [← QRegister.embedMatrix_mul]
  have hRight : ((Mrem * Pcut * B) * P86) * P_ef = Mrem * (P_sf * (U_ax * P86)) :=
    selectPos_slice_reassoc Mrem Pcut B P86 P_ef P_perm P_sf U_ax
      (uBarrelFast_mul_rAncFlag80 a86) hPperm_anc (uProj3DCutCore_mul_rAncFlag80 a86)
      hperm_ef hPsf_anc hUax_sf
  unfold CoreMapsToKrylov3On
  rw [hRight]
  exact (uRemCore_conj_uPosPhase80Mod4Eff_mapsToKrylov3 spinUp hqft tailSign tailMag30
    (truncFn c) e).mul_right (U_ax * P86)
theorem coreFermMapsToKrylov3_selectPos_of_oraHyp_mod4Eff_mul_slot0
    (spinUp : Finset (Fin numElectrons)) {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration} {qft : FullSysQft654Bundle}
    (hqft : qft.uQft654 * uPre654 = qft64Ideal654Unitary)
    {selOra : FullSysSelectOracleBundle 80 48}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat} {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfTrunc truncFn selOra leaf2 ora3)
    {tailSign : Fin orbitCount47905 → Bool} {tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)}
    (hPos0 : leaf2.uPosPhase0 = uPosPhase80Mod4Eff tailSign tailMag30) (c : Configuration) :
    CoreFermMapsToKrylov3 spinUp ((fullSysSelectPosUnitary qft selOra c).1 * slotBitProj
    (iSlot2 80) 0) := by
  unfold CoreFermMapsToKrylov3 CoreMapsToKrylov3On
  rw [Matrix.mul_assoc _ (slotBitProj (iSlot2 80) 0), slotBitProj_comm_embed_rSysCore 0]
  exact (coreFermMapsToKrylov3_selectPos_of_oraHyp_mod4Eff spinUp hqft hOra hPos0 c).mul_right
    (slotBitProj (iSlot2 80) 0)
-- Section 3: Turnkey `CoreFermMapsToKrylov3` & `RawBEMapsFermToKrylov3` Endpoints
theorem coreQftHadamardPrunedBundle128_mul_uPre654 :
    coreQftHadamardPrunedBundle128.uQft654 * uPre654 = qft64Ideal654Unitary := by
  rw [coreQftHadamardPrunedBundle128_uQft654]
  exact qft64Ideal654Unitary_eq_core_mul_preDiag.symm
end PosFermKrylovHead
end
end PosFermKrylovHead


end QuantumComputation.Specs.StoppingPowerSolution
end
