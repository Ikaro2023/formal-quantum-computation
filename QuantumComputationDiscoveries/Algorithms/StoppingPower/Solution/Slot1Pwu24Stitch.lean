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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosMomKrylovPres
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import QuantumComputation.QuantumHoareLogic.WP
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80BhmtCert
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Gf8Code18Guard
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.AsymTwistShell
set_option Elab.async false
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option compiler.extract_closed false

/-!
# Slot-1 PWU24, Krylov/BHMT Commutation, and `SELECT` Horizon Stitch

Combines in topological order:
1. `Mux3AnchoredPwu`, `MomSlot1WalkerAliasPWU24`, and `Slot1Pwu24Bridge`
2. `RawBEMapsFermToKrylov3` for `ora1Pwu24OfBSub` and `PosPostPrepCert 80`
3. `RawBEBlockCommutesFerm` for `pos80BhmtPostPrepCert`
4. `Pos512ChiralBhmtPwu24HorizonSelPkg` and `spPos512Opt`
5. `mkComposableGenPwu24HorizonSelPkg_mWork` and `SELECT` at `k_idle = 11`
-/

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

section Shard3Limb_Shims
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open PrimitiveGate (TOFF T)
open scoped Matrix BigOperators
open SpecsAux SpecsAux.SpecMirror

namespace PosSlots24SpectatorPrunedPhase
open MeasureBranchHadamardSem (ket)
open OctahedralOrbit (writeReg writeReg_apply_reg writeReg_apply_of_not_mem)
private theorem p2t_localIdx_singleton_eq {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    ((basisBitsEquiv 1).symm (fun _ => β q) : Fin 2) = if β q = 0 then 0 else 1 := by
  have h : ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ => b) : Fin 2) = if b = 0 then 0 else 1 :=
    by decide
  exact h (β q)
theorem p2t_singleton_embedMatrix_mulVec_ket {n : ℕ} (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
      A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
        A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  let A1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ := A
  change ((QRegister.singleton q).embedMatrix A1).mulVec (ket β) = _
  have hext : (QRegister.singleton q).extractIndex ((basisBitsEquiv n).symm β) =
      if β q = 0 then 0 else 1 := by
    have hsymm : basisBits n ((basisBitsEquiv n).symm β) = β :=
      (basisBitsEquiv n).apply_symm_apply β
    simpa [QRegister.extractIndex, hsymm] using p2t_localIdx_singleton_eq q β
  have hcol (j : Fin (2 ^ 1)) :
      A1.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ 1), A1 l j • Pi.single l 1 := by
    funext x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hw (l : Fin (2 ^ 1)) (b : ZMod 2) (hb : basisBits 1 l = fun _ => b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    funext w
    by_cases hqw : w = q
    · subst hqw
      simpa [hb] using writeReg_apply_reg β (QRegister.singleton w) (basisBits 1 l) 0
    · rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨_, h⟩ ↦ hqw h.symm), Function.update_of_ne hqw]
  have hket (γ : BitAssignment n) : ket γ = Pi.single ((basisBitsEquiv n).symm γ) (1 : ℂ) := by
    funext y; simp [ket, basisState]
  rw [hket β, QRegister.embedMatrix_mulVec_single_factors,
    hext, hcol, QRegister.tensorState_sum_left]
  change (∑ index : Fin 2, _) = _
  rw [Fin.sum_univ_two,
    QRegister.tensorState_smul_left, QRegister.tensorState_smul_left,
    QRegister.tensorState_single_replaceIndex, QRegister.tensorState_single_replaceIndex]
  have hsymm_bb : ∀ {q : ℕ} (j : Fin (2 ^ q)), (basisBitsEquiv q).symm (basisBits q j) = j :=
    fun j ↦ (basisBitsEquiv _).symm_apply_apply j
  have hk (l : Fin (2 ^ 1)) :
      Pi.single ((QRegister.singleton q).replaceIndex ((basisBitsEquiv n).symm β) l) (1 : ℂ) =
        ket (writeReg β (QRegister.singleton q) (basisBits 1 l)) := by
    rw [hket, writeReg, hsymm_bb, hsymm_bb]
  rw [hk 0, hk 1, hw 0 0 (by decide), hw 1 1 (by decide)]
end PosSlots24SpectatorPrunedPhase

namespace InterWalkRSum42Hoist
theorem inv_intertwine_lemma {D : ℕ}
    (U V : Unitary D) (E P : Operator D) (hUV : U.1 * E = P * V.1) :
    (U⁻¹).1 * P = E * (V⁻¹).1 := by
  have hU1 : (U⁻¹).1 * U.1 = 1 := by rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  have hV1 : V.1 * (V⁻¹).1 = 1 := by rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  calc (U⁻¹).1 * P
    _ = ((U⁻¹).1 * P) * (V.1 * (V⁻¹).1) := by rw [hV1, Matrix.mul_one]
    _ = (U⁻¹).1 * (P * V.1) * (V⁻¹).1 := by simp only [Matrix.mul_assoc]
    _ = ((U⁻¹).1 * U.1) * E * (V⁻¹).1 := by rw [← hUV]; simp only [Matrix.mul_assoc]
    _ = E * (V⁻¹).1 := by rw [hU1, Matrix.one_mul]
end InterWalkRSum42Hoist

namespace TruncWAsymHeldTwShell
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_compose_of_disjoint)
open HoistBorrow42ProjBridge (disjointWires_concat_right)
open InterWalkRSum42Hoist (kFull80)
open Leaf4Ext48TopStitch
  (rCoreTopCatFull rPGIdle rExt42IdleFull rCoreTopCatFull_disj_rExt42IdleFull rWorkCtrlTwist)

/-- Symbolic-dimension core for `Slot3InnerSlot3InnerCircuitSpec_mWork`. -/
structure Slot3InnerSlot3InnerCircuitSpecCore_mWork (kSub3 mWork : ℕ)
    (uInnerCatSub : Configuration → Unitary (2 ^ kSub3))
    (t3Ctrl t3Cat : ℕ) where
  /-- Control-pass dynamic circuit (`mWork + 11` clean workspace wires). -/
  dInnerCtrl : Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rSub : QRegister kSub3 n) → (rWB : QRegister (mWork + 11) n) →
      rSub.DisjointWires rWB → DynamicCircuit Var n
  /-- Catalyst-pass dynamic circuit (`mWork + 14` clean workspace wires). -/
  dInnerCat : Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rSub : QRegister kSub3 n) → (rWB : QRegister (mWork + 14) n) →
      rSub.DisjointWires rWB → DynamicCircuit Var n
  /-- Zero `.TOFF` gate count in control pass. -/
  hToffCtrl : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kSub3 n) (rWB : QRegister (mWork + 11) n) (hSW : rSub.DisjointWires rWB),
    (dInnerCtrl c v rSub rWB hSW).count TOFF = 0
  /-- Zero `.TOFF` gate count in catalyst pass. -/
  hToffCat : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kSub3 n) (rWB : QRegister (mWork + 14) n) (hSW : rSub.DisjointWires rWB),
    (dInnerCat c v rSub rWB hSW).count TOFF = 0
  /-- `.T`-gate bound in control pass. -/
  hTCtrl : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kSub3 n) (rWB : QRegister (mWork + 11) n) (hSW : rSub.DisjointWires rWB),
    (dInnerCtrl c v rSub rWB hSW).count T ≤ t3Ctrl
  /-- `.T`-gate bound in catalyst pass. -/
  hTCat : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kSub3 n) (rWB : QRegister (mWork + 14) n) (hSW : rSub.DisjointWires rWB),
    (dInnerCat c v rSub rWB hSW).count T ≤ t3Cat
  /-- Clean-workspace unitary realization in control pass. -/
  hRealCtrl : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rSub : QRegister kSub3 n) (rWB : QRegister (mWork + 11) n)
    (hSW : rSub.DisjointWires rWB),
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rSub rWB
      (uInnerCatSub c) (dInnerCtrl c v rSub rWB hSW)
  /-- Clean-workspace unitary realization in catalyst pass. -/
  hRealCat : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rSub : QRegister kSub3 n) (rWB : QRegister (mWork + 14) n)
    (hSW : rSub.DisjointWires rWB),
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rSub rWB
      (uInnerCatSub c) (dInnerCat c v rSub rWB hSW)

/-- `{mWork}`-polymorphic Slot-3 inner circuit bundle realizing `uInnerCatSub`. -/
abbrev Slot3InnerSlot3InnerCircuitSpec_mWork (mWork : ℕ)
    (uInnerCatSub : Configuration → Unitary (2 ^ (fullSysCoreWires 80 + 36)))
    (t3Ctrl t3Cat : ℕ) : Type 1 :=
  Slot3InnerSlot3InnerCircuitSpecCore_mWork (fullSysCoreWires 80 +
    36) mWork uInnerCatSub t3Ctrl t3Cat

namespace HeldStreamEStream42InterfaceShell
private theorem rCoreTopCatFull_disj_rPGIdle11 {mCat : ℕ} (hkc : 11 + mCat ≤ 48) :
    (rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).DisjointWires
      (rPGIdle 11 (by decide)) := by
  rw [QRegister.disjoint_iff]; intro a q h
  exact (rCoreTopCatFull_disj_rExt42IdleFull 11 mCat hkc).ne a (Fin.natAdd 42 q)
    (by simpa only [rExt42IdleFull, QRegister.concat_apply_right] using h)

theorem rSub3Act_disj_rWorkCtrlTwist11 {mCat mWork n : ℕ} (hkc : 11 + mCat ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (rAct.compose (rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc))).DisjointWires
      (rWorkCtrlTwist 11 (by decide) rAct rWork hDisj) :=
  disjointWires_concat_right (hDisj.compose_left _)
    (disjointWires_compose_of_disjoint rAct (rCoreTopCatFull_disj_rPGIdle11 hkc))
end HeldStreamEStream42InterfaceShell
end TruncWAsymHeldTwShell

namespace SlimNorm1sWideSelect
abbrev t2CtrlSlot3InnerOfB (B : ℕ) : ℕ :=
  BoothOpt_05_Fast3BarrelLeaf123Shave.pass2Ctrl190_64x4BaseT B 190 + 260 * B
abbrev t2CatSlot3InnerOfB (B : ℕ) : ℕ :=
  BoothOpt_05_Fast3BarrelLeaf123Shave.pass2CatCore_64x4BaseT B 196 + 260 * B
end SlimNorm1sWideSelect

namespace ApproxBlockCommFerm
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowFermApproxShim (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority := 1000000) instGroupUnitaryFast_assocShim (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open Dyadic128CoulombMath (orbitCount47905)
open TierBClean80Closure (tierBQftFull)
open PosSlots24SemanticBridge (pos24TailSign)
open PosSlots24SemanticOracleConcrete80 (coreBetaOf)
open NuclearTwistAndXor654Concrete (sysNucDiag48)
open Pos24Slot2FermionicBridge
  (veeBasisUnitary18 veeSysProdUnitary payloadNucNat payloadAncNat payloadB1Parity)
open PosS3Bounds
open PosMod4FermionicBounds

set_option exponentiation.threshold 5000 in
set_option maxRecDepth 2000 in
theorem blkSmSlot2Mod4Of_head_anc0_comm_pElMat
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p : BitAssignment 80)
    (h30 : (p 30 == 1) = true) (hanc0 : payloadAncNat p = 0)
    (hnuc : payloadNucNat p < 216) (g : Equiv.Perm (Fin numElectrons)) :
    sysBlock80Mod4Of tM tierBQftFull cfg false p * pElMat g =
      pElMat g * sysBlock80Mod4Of tM tierBQftFull cfg false p := by
  by_cases h62 : (p ⟨62, by decide⟩ == 1) = true
  · rw [sysBlock80Mod4Of_eq_smul_one_of_phase_const tM cfg false p (p ⟨79, by decide⟩ == 1)
      (posPhaseBitMod4_const_of_rejected tM false p (Or.inl h62)),
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · refine comm_pElMat_of_smConj ?_
    have hswap0 : pElMat (Equiv.swap (0 : Fin 218) 0) = 1 := by
      rw [Equiv.swap_self]; exact pElMat_one
    rw [blkSmSlot2Mod4Of_eq_cleanConj tM cfg p ⟨payloadNucNat p, hnuc⟩ 0 (payloadB1Parity p)
        rfl hanc0 rfl,
      hswap0, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    let Unuc := sysNucDiag48 cfg ⟨payloadNucNat p, hnuc⟩
    let Uvee := veeSysProdUnitary (payloadB1Parity p)
    let d₀ : Fin (2 ^ systemQubits) → ℂ := fun z ↦
      if posPhaseBitMod4 true pos24TailSign tM (coreBetaOf false p z) then (-1 : ℂ) else 1
    have hVee : ∀ h, Uvee.1 * pElMat h = pElMat h * Uvee.1 := fun h ↦ by
      have hLem := list_ofFn_rEl_const_comm_pElMat (veeBasisUnitary18 (payloadB1Parity p)) h
      dsimp only [numElectrons] at hLem
      exact hLem
    have hNuc : ∀ h, Unuc.1 * pElMat h = pElMat h * Unuc.1 :=
      list_ofFn_rEl_const_comm_pElMat _
    have hDiag : Matrix.diagonal d₀ * pElMat g = pElMat g * Matrix.diagonal d₀ :=
      diagonal_comm_pElMat d₀ g fun z ↦ by
        dsimp only [d₀]
        rw [posPhaseBitMod4_head_permElectron_eq tM false p h30 g (fun h ↦ Bool.noConfusion h) z]
    have hMid := conj_comm_pElMat_of_stab Uvee _ (hVee g) (hVee g⁻¹) hDiag
    have hNucAdj : Unuc.1ᴴ * pElMat g = pElMat g * Unuc.1ᴴ := by
      have h1 : Unuc.1 * (pElMat g)ᴴ = (pElMat g)ᴴ * Unuc.1 := by
        rw [pElMat_conjTranspose]; exact hNuc g⁻¹
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
        (congrArg Matrix.conjTranspose h1).symm
    calc (Unuc.1 * (Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * Unuc.1ᴴ) * pElMat g
        = Unuc.1 * (Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * (Unuc.1ᴴ * pElMat g) := by
          simp only [Matrix.mul_assoc]
      _ = Unuc.1 * ((Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * pElMat g) * Unuc.1ᴴ := by
          rw [hNucAdj]; simp only [Matrix.mul_assoc]
      _ = (Unuc.1 * pElMat g) * (Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * Unuc.1ᴴ := by
          rw [hMid]; simp only [Matrix.mul_assoc]
      _ = pElMat g * (Unuc.1 * (Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * Unuc.1ᴴ) := by
          rw [hNuc g]; simp only [Matrix.mul_assoc]
end ApproxBlockCommFerm

namespace ConstructiveAlpha124052Bundle
open TierBClean80Closure (tierBQftFull tierBQftFull_eq_core_mul_uPre654)
open FusedPreDiagFromTwist288 (uPre654)
open CoreQftHadamardPrunedCore
  (coreQftHadamardPrunedBundle128 coreQftHadamardPrunedBundle128_uQft654)
theorem hqftFactor_coreQftPruned128 :
    tierBQftFull.uQft654 = coreQftHadamardPrunedBundle128.uQft654 * uPre654 := by
  rw [coreQftHadamardPrunedBundle128_uQft654]
  exact tierBQftFull_eq_core_mul_uPre654
end ConstructiveAlpha124052Bundle
end Shard3Limb_Shims


set_option maxSynthPendingDepth 3
set_option maxRecDepth 2000

namespace SelAndPertStitchAux
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires iSlot2)
open PosSlots24TopWrapper (PosSlots24DataGen)
open SelectStitch (Leaf2SpecOfTrunc)
/-- `PosSlots24DataGen` (`288w`) built from any `Leaf2SpecOfTrunc`. -/
noncomputable def posDataOfLeaf2 {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat) :
    PosSlots24DataGen (fullSysCoreWires 80) (iSlot2 80) 288 where
  uPosPhase _ := leaf2.uPosPhase0
  hPos_sa _ := leaf2.hPosSA
  hPos_on_P1 _ := leaf2.hPosOnP1
end SelAndPertStitchAux
-- Part: Slot1Pwu24
-- ============================================================================
section PartSlot1Pwu24
noncomputable section

namespace Dir3TwistSlot1Junction.Mux3AnchoredPwu
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open MomSlot1GeomPriority288

open MomSlots01Slot1ProjKinetic (padZeroBits)
open InPlaceFullAddSlice (
  ket bitSign bit_cases matrix_ext_ket
  eval_seq_mulVec ket_X ket_CNOT ket_TOFF ket_projector_zero projZeroAll ket_projZeroAll
  projZeroAll_conjTranspose projZeroAll_eq_basisOutcomeProjector_zero RealizesCleanUnitary
  PreservesStoreConst wire_ne_of_gt mul_mulVec_prog writeRegProg writeRegProg_apply_reg
  writeRegProg_apply_of_not_mem localIdxProg embedMatrix_mulVec_ket_prog CliffProg TempPhaseProg
  cleanRem tailScr tailScr_succ projZeroAll_tailScr_sub ValidCleanRem eval_onRegister_prog_ket
  RealizesCleanUnitary_seq_asym)
open MeasureBranchHadamardSem (sqrtHalf sqrtHalf_mul_sqrtHalf
  hadamardAll count_hadamardAll_t count_hadamardAll_toff
  xReset count_xReset_t count_xReset_toff
  writeSynd writeSynd_apply_of_not_mem syndSign syndSign_congr_of_eq_on
  measureAndBranchSeq measureAndBranchSeq_count_eq_zero)
open scoped Matrix BigOperators Circuit.Notation

local instance (priority := 1000000) instNeZero_Slot1Pwu24_Mux3 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable def zeta8C : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℝ)

private theorem zeta8C_sq : zeta8C * zeta8C = Complex.I := by
  dsimp [zeta8C]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [div_mul_div_comm, h2]
  have hi : (1 + Complex.I) * (1 + Complex.I) = 2 * Complex.I := by
    linear_combination Complex.I_sq
  rw [hi]
  ring

private theorem singleton_embedMatrix_mulVec_ket_local {n : ℕ} (q : Wire n)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
      A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
        A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) :=
          PosSlots24SpectatorPrunedPhase.p2t_singleton_embedMatrix_mulVec_ket (n := n) q A β

private theorem ket_S_local {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket β) =
      (if β q = 0 then (1 : ℂ) else Complex.I) • ket β := by
  rw [Circuit.S, Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![(1 : ℂ), 0; 0, Complex.I]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket_local]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

private theorem ket_T_local {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (ket β) =
      (if β q = 0 then (1 : ℂ) else zeta8C) • ket β := by
  rw [Circuit.T, Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![(1 : ℂ), 0; 0, zeta8C]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket_local]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

def mux3Gad {n : ℕ} (d s a : Wire n) (hd : d ≠ a) (hs : s ≠ a) : Circuit n :=
  Circuit.CNOT d a hd ;;ᶜ Circuit.T a ;;ᶜ Circuit.CNOT s a hs ;;ᶜ
    Circuit.Z a ;;ᶜ Circuit.S a ;;ᶜ Circuit.T a ;;ᶜ
    Circuit.CNOT d a hd ;;ᶜ Circuit.T a ;;ᶜ Circuit.CNOT s a hs

private theorem ket_mux3Gad {n : ℕ} (d s a : Wire n) (hd : d ≠ a) (hs : s ≠ a) (γ : BitAssignment n)
    :
    (mux3Gad d s a hd hs).eval.1.mulVec (ket γ) =
      (if γ a = 0 then
        (if γ d * γ s = 0 then (1 : ℂ) else Complex.I)
       else
        (if γ d * γ s = 0 then zeta8C else -Complex.I * zeta8C)) •
        ket γ := by
  have hketZ : ∀ (w : Wire n) (δ : BitAssignment n),
      (Circuit.Z w).eval.1.mulVec (ket δ) = bitSign (δ w) • ket δ :=
    fun w δ ↦ MeasureBranchHadamardSem.ket_Z w δ
  dsimp only [mux3Gad]
  simp only [eval_seq_mulVec, ket_CNOT, Matrix.mulVec_smul, ket_T_local, hketZ, ket_S_local,
    smul_smul, Function.update_self, Function.update_idem,
    Function.update_of_ne hd, Function.update_of_ne hs]
  have hrestore : Function.update γ a (γ a + γ d + γ s + γ d + γ s) = γ := by
    have hsum : γ a + γ d + γ s + γ d + γ s = γ a := by
      rcases bit_cases (γ a) with ha | ha <;>
        rcases bit_cases (γ d) with hd' | hd' <;>
        rcases bit_cases (γ s) with hs' | hs' <;>
        rw [ha, hd', hs'] <;> decide
    rw [hsum, Function.update_eq_self]
  rw [hrestore]
  congr 1
  have h00 : ((0 : ZMod 2) = 0) = True := by decide
  have h10 : ((1 : ZMod 2) = 0) = False := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hz2 : zeta8C ^ 2 = Complex.I := by linear_combination zeta8C_sq
  have hz3 : zeta8C ^ 3 = Complex.I * zeta8C := by linear_combination zeta8C * zeta8C_sq
  rcases bit_cases (γ d) with hd' | hd' <;>
    rcases bit_cases (γ s) with hs' | hs' <;>
    rcases bit_cases (γ a) with ha' | ha' <;>
    simp only [hd', hs', ha', add_zero, zero_add, h11, mul_zero, mul_one, h10, ↓reduceIte,
      bitSign] <;>
    ring_nf
  · linear_combination -Complex.I * hz3 - zeta8C * Complex.I_sq
  · linear_combination -Complex.I * hz2 - Complex.I_sq
  · linear_combination -Complex.I * hz2 - Complex.I_sq
  · exact hz2

def cLoadMux3_1Bit {n : ℕ} (q0 q1 q2 u1 u2 a : Wire n)
    (hq01 : q0 ≠ q1) (hq02 : q0 ≠ q2) (hq0a : q0 ≠ a)
    (hq1a : q1 ≠ a) (hq2a : q2 ≠ a) (hu1a : u1 ≠ a) (hu2a : u2 ≠ a) : Circuit n :=
  Circuit.CNOT q0 q1 hq01 ;;ᶜ Circuit.CNOT q0 q2 hq02 ;;ᶜ
    Circuit.H a ;;ᶜ Circuit.Z a ;;ᶜ Circuit.S a ;;ᶜ
    mux3Gad q1 u1 a hq1a hu1a ;;ᶜ
    mux3Gad q2 u2 a hq2a hu2a ;;ᶜ
    Circuit.H a ;;ᶜ Circuit.Z a ;;ᶜ Circuit.S a ;;ᶜ
    Circuit.CNOT q0 a hq0a ;;ᶜ
    Circuit.CNOT q0 q2 hq02 ;;ᶜ Circuit.CNOT q0 q1 hq01

@[simp]
theorem cLoadMux3_1Bit_count_toff {n : ℕ} (q0 q1 q2 u1 u2 a : Wire n)
    (hq01 : q0 ≠ q1) (hq02 : q0 ≠ q2) (hq0a : q0 ≠ a)
    (hq1a : q1 ≠ a) (hq2a : q2 ≠ a) (hu1a : u1 ≠ a) (hu2a : u2 ≠ a) :
    (cLoadMux3_1Bit q0 q1 q2 u1 u2 a hq01 hq02 hq0a hq1a hq2a hu1a hu2a).count
      PrimitiveGate.TOFF = 0 := by
  simp [cLoadMux3_1Bit, mux3Gad, Circuit.CNOT, Circuit.T, Circuit.H, Circuit.Z, Circuit.S,
    Circuit.single, Circuit.count]

@[simp]
theorem cLoadMux3_1Bit_count_t {n : ℕ} (q0 q1 q2 u1 u2 a : Wire n)
    (hq01 : q0 ≠ q1) (hq02 : q0 ≠ q2) (hq0a : q0 ≠ a)
    (hq1a : q1 ≠ a) (hq2a : q2 ≠ a) (hu1a : u1 ≠ a) (hu2a : u2 ≠ a) :
    (cLoadMux3_1Bit q0 q1 q2 u1 u2 a hq01 hq02 hq0a hq1a hq2a hu1a hu2a).count
      PrimitiveGate.T = 6 := by
  simp [cLoadMux3_1Bit, mux3Gad, Circuit.CNOT, Circuit.T, Circuit.H, Circuit.Z, Circuit.S,
    Circuit.single, Circuit.count]

private theorem ket_cLoadMux3_1Bit {n : ℕ} (q0 q1 q2 u1 u2 a : Wire n)
    (hq01 : q0 ≠ q1) (hq02 : q0 ≠ q2) (hq12 : q1 ≠ q2)
    (hq0a : q0 ≠ a) (hq1a : q1 ≠ a) (hq2a : q2 ≠ a)
    (hu1q1 : u1 ≠ q1) (hu1q2 : u1 ≠ q2) (hu1a : u1 ≠ a)
    (hu2q1 : u2 ≠ q1) (hu2q2 : u2 ≠ q2) (hu2a : u2 ≠ a)
    (β : BitAssignment n) (ha0 : β a = 0) :
    let d1 := β q1 + β q0
    let d2 := β q2 + β q0
    let p1 := d1 * β u1
    let p2 := d2 * β u2
    (cLoadMux3_1Bit q0 q1 q2 u1 u2 a hq01 hq02 hq0a hq1a hq2a hu1a hu2a).eval.1.mulVec
        (ket β) =
      ((-1 : ℂ) ^ (p1 * p2).val) •
        ket (Function.update β a (β q0 + p1 + p2)) := by
  intro d1 d2 p1 p2
  have hketZ : ∀ (w : Wire n) (δ : BitAssignment n),
      (Circuit.Z w).eval.1.mulVec (ket δ) = bitSign (δ w) • ket δ :=
    fun w δ ↦ MeasureBranchHadamardSem.ket_Z w δ
  dsimp only [cLoadMux3_1Bit]
  let γ : BitAssignment n := Function.update (Function.update β q1 d1) q2 d2
  have hpre : (Circuit.CNOT q0 q1 hq01 ;;ᶜ Circuit.CNOT q0 q2 hq02).eval.1.mulVec
      (ket β) = ket γ := by
    rw [eval_seq_mulVec, ket_CNOT, ket_CNOT, Function.update_of_ne hq12.symm,
      Function.update_of_ne hq01]
  have hγa : γ a = 0 := by
    dsimp [γ]; rw [Function.update_of_ne hq2a.symm, Function.update_of_ne hq1a.symm, ha0]
  have hγq0 : γ q0 = β q0 := by
    dsimp [γ]; rw [Function.update_of_ne hq02, Function.update_of_ne hq01]
  have hγq1 : γ q1 = d1 := by
    dsimp [γ]; rw [Function.update_of_ne hq12, Function.update_self]
  have hγq2 : γ q2 = d2 := by
    dsimp [γ]; rw [Function.update_self]
  have hγu1 : γ u1 = β u1 := by
    dsimp [γ]; rw [Function.update_of_ne hu1q2, Function.update_of_ne hu1q1]
  have hγu2 : γ u2 = β u2 := by
    dsimp [γ]; rw [Function.update_of_ne hu2q2, Function.update_of_ne hu2q1]
  have hcore :
      (Circuit.H a ;;ᶜ Circuit.Z a ;;ᶜ Circuit.S a ;;ᶜ
        mux3Gad q1 u1 a hq1a hu1a ;;ᶜ mux3Gad q2 u2 a hq2a hu2a ;;ᶜ
        Circuit.H a ;;ᶜ Circuit.Z a ;;ᶜ Circuit.S a).eval.1.mulVec
          (ket γ) =
        ((-1 : ℂ) ^ (p1 * p2).val) • ket (Function.update γ a (p1 + p2)) := by
    simp only [eval_seq_mulVec, ket_H_local, hγa, bitSign, ↓reduceIte, one_smul,
      Matrix.mulVec_smul, Matrix.mulVec_add, hketZ, ket_S_local,
      ket_mux3Gad, smul_add, smul_smul, Function.update_self, Function.update_idem,
      Function.update_of_ne hq1a, Function.update_of_ne hq2a,
      Function.update_of_ne hu1a, Function.update_of_ne hu2a,
      hγq1, hγq2, hγu1, hγu2]
    have hp1_def : d1 * β u1 = p1 := rfl
    have hp2_def : d2 * β u2 = p2 := rfl
    rw [hp1_def, hp2_def]
    have h00 : ((0 : ZMod 2) = 0) = True := by decide
    have h10 : ((1 : ZMod 2) = 0) = False := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hz2 : zeta8C ^ 2 = Complex.I := by linear_combination zeta8C_sq
    have hsh2 : (sqrtHalf : ℂ) ^ 2 = 1 / 2 := by linear_combination sqrtHalf_mul_sqrtHalf
    have hI3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * Complex.I_sq
    have hI4 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq
    have hI5 : Complex.I ^ 5 = Complex.I := by linear_combination Complex.I * hI4
    rcases bit_cases p1 with hp1 | hp1 <;> rcases bit_cases p2 with hp2 | hp2
    · simp only [hp1, hp2, add_zero, mul_zero, ZMod.val_zero, _root_.pow_zero, one_smul, h10,
        ↓reduceIte]
      ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf; simp only [hz2, hsh2]; ring_nf; simp only [Complex.I_sq, hI3]; ring
    · simp only [hp1, hp2, zero_add, zero_mul, ZMod.val_zero, _root_.pow_zero, one_smul, h10,
        ↓reduceIte]
      ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf; simp only [hz2, hsh2]; ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring
    · simp only [hp1, hp2, add_zero, mul_zero, ZMod.val_zero, _root_.pow_zero, one_smul, h10,
        ↓reduceIte]
      ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf; simp only [hz2, hsh2]; ring_nf; simp only [Complex.I_sq, hI3, hI4]; ring
    · simp only [hp1, hp2, h11, mul_one, ZMod.val_one, _root_.pow_one, h10, ↓reduceIte]
      ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf; simp only [hz2, hsh2]; ring_nf; simp only [Complex.I_sq, hI3, hI4, hI5]; ring
  have hsplit :
      (Circuit.CNOT q0 q1 hq01 ;;ᶜ Circuit.CNOT q0 q2 hq02 ;;ᶜ
        Circuit.H a ;;ᶜ Circuit.Z a ;;ᶜ Circuit.S a ;;ᶜ
        mux3Gad q1 u1 a hq1a hu1a ;;ᶜ mux3Gad q2 u2 a hq2a hu2a ;;ᶜ
        Circuit.H a ;;ᶜ Circuit.Z a ;;ᶜ Circuit.S a ;;ᶜ
        Circuit.CNOT q0 a hq0a ;;ᶜ Circuit.CNOT q0 q2 hq02 ;;ᶜ Circuit.CNOT q0 q1
          hq01).eval.1.mulVec
          (ket β) =
      (Circuit.CNOT q0 a hq0a ;;ᶜ Circuit.CNOT q0 q2 hq02 ;;ᶜ Circuit.CNOT q0 q1 hq01).eval.1.mulVec
        ((Circuit.H a ;;ᶜ Circuit.Z a ;;ᶜ Circuit.S a ;;ᶜ
          mux3Gad q1 u1 a hq1a hu1a ;;ᶜ mux3Gad q2 u2 a hq2a hu2a ;;ᶜ
          Circuit.H a ;;ᶜ Circuit.Z a ;;ᶜ Circuit.S a).eval.1.mulVec
            ((Circuit.CNOT q0 q1 hq01 ;;ᶜ Circuit.CNOT q0 q2 hq02).eval.1.mulVec
              (ket β))) := by
    simp only [eval_seq_mulVec]
  rw [hsplit, hpre, hcore, Matrix.mulVec_smul]
  simp only [eval_seq_mulVec, ket_CNOT, Function.update_self, Function.update_idem,
    Function.update_of_ne hq0a, Function.update_of_ne hq02, Function.update_of_ne hq2a,
    Function.update_of_ne hq1a, Function.update_of_ne hq12, hγq0, hγq1, hγq2]
  congr 2
  funext w
  by_cases hwa : w = a
  · rw [hwa]
    simp only [Function.update_self, Function.update_of_ne hq1a.symm,
      Function.update_of_ne hq2a.symm]
    ring
  · by_cases hw1 : w = q1
    · rw [hw1]
      simp only [Function.update_self, Function.update_of_ne hq1a, d1]
      exact zmod2_add_assoc_cancel (β q1) (β q0)
    · by_cases hw2 : w = q2
      · rw [hw2]
        simp only [Function.update_of_ne hq12.symm, Function.update_self,
          Function.update_of_ne hq2a, d2]
        exact zmod2_add_assoc_cancel (β q2) (β q0)
      · simp [Function.update_of_ne hw1, Function.update_of_ne hw2, Function.update_of_ne hwa, γ]

structure Mux3Tuple (n : ℕ) where
  q0 : Wire n
  q1 : Wire n
  q2 : Wire n
  u1 : Wire n
  u2 : Wire n
  a : Wire n
  hq01 : q0 ≠ q1
  hq02 : q0 ≠ q2
  hq12 : q1 ≠ q2
  hq0a : q0 ≠ a
  hq1a : q1 ≠ a
  hq2a : q2 ≠ a
  hu1q0 : u1 ≠ q0
  hu1q1 : u1 ≠ q1
  hu1q2 : u1 ≠ q2
  hu1a : u1 ≠ a
  hu2q0 : u2 ≠ q0
  hu2q1 : u2 ≠ q1
  hu2q2 : u2 ≠ q2
  hu2a : u2 ≠ a

def Mux3Tuple.map {m n : ℕ} (r : QRegister m n) (t : Mux3Tuple m) : Mux3Tuple n where
  q0 := r t.q0
  q1 := r t.q1
  q2 := r t.q2
  u1 := r t.u1
  u2 := r t.u2
  a := r t.a
  hq01 := r.wires.injective.ne t.hq01
  hq02 := r.wires.injective.ne t.hq02
  hq12 := r.wires.injective.ne t.hq12
  hq0a := r.wires.injective.ne t.hq0a
  hq1a := r.wires.injective.ne t.hq1a
  hq2a := r.wires.injective.ne t.hq2a
  hu1q0 := r.wires.injective.ne t.hu1q0
  hu1q1 := r.wires.injective.ne t.hu1q1
  hu1q2 := r.wires.injective.ne t.hu1q2
  hu1a := r.wires.injective.ne t.hu1a
  hu2q0 := r.wires.injective.ne t.hu2q0
  hu2q1 := r.wires.injective.ne t.hu2q1
  hu2q2 := r.wires.injective.ne t.hu2q2
  hu2a := r.wires.injective.ne t.hu2a

def Mux3Tuple.outBit {n : ℕ} (t : Mux3Tuple n) (β : BitAssignment n) : ZMod 2 :=
  β t.q0 + (β t.q1 + β t.q0) * β t.u1 + (β t.q2 + β t.q0) * β t.u2

def Mux3Tuple.extraPhase {n : ℕ} (t : Mux3Tuple n) (β : BitAssignment n) : ZMod 2 :=
  ((β t.q1 + β t.q0) * β t.u1) * ((β t.q2 + β t.q0) * β t.u2)

def Mux3Tuple.cLoad {n : ℕ} (t : Mux3Tuple n) : Circuit n :=
  cLoadMux3_1Bit t.q0 t.q1 t.q2 t.u1 t.u2 t.a
    t.hq01 t.hq02 t.hq0a t.hq1a t.hq2a t.hu1a t.hu2a

def Mux3Tuple.cFix {n : ℕ} (t : Mux3Tuple n) : Circuit n :=
  Circuit.CNOT t.q0 t.q1 t.hq01 ;;ᶜ Circuit.CNOT t.q0 t.q2 t.hq02 ;;ᶜ
    Circuit.Z t.q0 ;;ᶜ
    MomSlot1GeomPriority288.czCircuit t.q1 t.u1 t.hu1q1.symm ;;ᶜ
    MomSlot1GeomPriority288.czCircuit t.q2 t.u2 t.hu2q2.symm ;;ᶜ
    Circuit.CNOT t.q0 t.q2 t.hq02 ;;ᶜ Circuit.CNOT t.q0 t.q1 t.hq01

@[simp]
theorem Mux3Tuple.cLoad_count_toff {n : ℕ} (t : Mux3Tuple n) :
    t.cLoad.count PrimitiveGate.TOFF = 0 :=
  cLoadMux3_1Bit_count_toff _ _ _ _ _ _ _ _ _ _ _ _ _

@[simp]
theorem Mux3Tuple.cLoad_count_t {n : ℕ} (t : Mux3Tuple n) :
    t.cLoad.count PrimitiveGate.T = 6 :=
  cLoadMux3_1Bit_count_t _ _ _ _ _ _ _ _ _ _ _ _ _

@[simp]
theorem Mux3Tuple.cFix_count_toff {n : ℕ} (t : Mux3Tuple n) :
    t.cFix.count PrimitiveGate.TOFF = 0 := by
  simp [Mux3Tuple.cFix, Circuit.CNOT, Circuit.Z, Circuit.single, Circuit.count,
    MomSlot1GeomPriority288.czCircuit_count_toff]

@[simp]
theorem Mux3Tuple.cFix_count_t {n : ℕ} (t : Mux3Tuple n) :
    t.cFix.count PrimitiveGate.T = 0 := by
  simp [Mux3Tuple.cFix, Circuit.CNOT, Circuit.Z, Circuit.single, Circuit.count,
    MomSlot1GeomPriority288.czCircuit_count_t]

private theorem Mux3Tuple.ket_cLoad {n : ℕ} (t : Mux3Tuple n) (β : BitAssignment n) (ha0 : β t.a =
    0) :
    t.cLoad.eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (t.extraPhase β).val) • ket (Function.update β t.a (t.outBit β)) :=
  ket_cLoadMux3_1Bit t.q0 t.q1 t.q2 t.u1 t.u2 t.a
    t.hq01 t.hq02 t.hq12 t.hq0a t.hq1a t.hq2a
    t.hu1q1 t.hu1q2 t.hu1a t.hu2q1 t.hu2q2 t.hu2a β ha0

private theorem Mux3Tuple.ket_cFix {n : ℕ} (t : Mux3Tuple n) (β : BitAssignment n) :
    t.cFix.eval.1.mulVec (ket β) = bitSign (t.outBit β) • ket β := by
  have hketZ : ∀ (w : Wire n) (δ : BitAssignment n),
      (Circuit.Z w).eval.1.mulVec (ket δ) = bitSign (δ w) • ket δ :=
    fun w δ ↦ MeasureBranchHadamardSem.ket_Z w δ
  dsimp only [Mux3Tuple.cFix]
  let d1 := β t.q1 + β t.q0
  let d2 := β t.q2 + β t.q0
  let γ : BitAssignment n := Function.update (Function.update β t.q1 d1) t.q2 d2
  have hγq0 : γ t.q0 = β t.q0 := by
    dsimp [γ]; rw [Function.update_of_ne t.hq02, Function.update_of_ne t.hq01]
  have hγq1 : γ t.q1 = d1 := by
    dsimp [γ]; rw [Function.update_of_ne t.hq12, Function.update_self]
  have hγq2 : γ t.q2 = d2 := by
    dsimp [γ]; rw [Function.update_self]
  have hγu1 : γ t.u1 = β t.u1 := by
    dsimp [γ]; rw [Function.update_of_ne t.hu1q2, Function.update_of_ne t.hu1q1]
  have hγu2 : γ t.u2 = β t.u2 := by
    dsimp [γ]; rw [Function.update_of_ne t.hu2q2, Function.update_of_ne t.hu2q1]
  have hpre : (Circuit.CNOT t.q0 t.q1 t.hq01 ;;ᶜ Circuit.CNOT t.q0 t.q2 t.hq02).eval.1.mulVec
      (ket β) = ket γ := by
    rw [eval_seq_mulVec, ket_CNOT, ket_CNOT, Function.update_of_ne t.hq12.symm,
      Function.update_of_ne t.hq01]
  have hsplit :
      (Circuit.CNOT t.q0 t.q1 t.hq01 ;;ᶜ Circuit.CNOT t.q0 t.q2 t.hq02 ;;ᶜ
        Circuit.Z t.q0 ;;ᶜ MomSlot1GeomPriority288.czCircuit t.q1 t.u1 t.hu1q1.symm ;;ᶜ
        MomSlot1GeomPriority288.czCircuit t.q2 t.u2 t.hu2q2.symm ;;ᶜ
        Circuit.CNOT t.q0 t.q2 t.hq02 ;;ᶜ Circuit.CNOT t.q0 t.q1 t.hq01).eval.1.mulVec (ket β) =
      (Circuit.CNOT t.q0 t.q2 t.hq02 ;;ᶜ Circuit.CNOT t.q0 t.q1 t.hq01).eval.1.mulVec
        ((MomSlot1GeomPriority288.czCircuit t.q2 t.u2 t.hu2q2.symm).eval.1.mulVec
          ((MomSlot1GeomPriority288.czCircuit t.q1 t.u1 t.hu1q1.symm).eval.1.mulVec
            ((Circuit.Z t.q0).eval.1.mulVec
              ((Circuit.CNOT t.q0 t.q1 t.hq01 ;;ᶜ Circuit.CNOT t.q0 t.q2 t.hq02).eval.1.mulVec
                (ket β))))) := by
    simp only [eval_seq_mulVec]
  rw [hsplit, hpre, hketZ, Matrix.mulVec_smul, MomSlot1GeomPriority288.ket_czCircuit, smul_smul,
    Matrix.mulVec_smul, MomSlot1GeomPriority288.ket_czCircuit, smul_smul, Matrix.mulVec_smul,
    eval_seq_mulVec, ket_CNOT, ket_CNOT,
    hγq0, hγq1, hγq2, hγu1, hγu2, Function.update_of_ne t.hq02, Function.update_of_ne t.hq12]
  rw [hγq1, hγq0]
  have hrestore : Function.update (Function.update γ t.q2 (d2 + β t.q0)) t.q1 (d1 + β t.q0) = β :=
    by
    funext w
    by_cases hw1 : w = t.q1
    · subst hw1
      simp only [Function.update_self, d1]
      exact zmod2_add_assoc_cancel (β t.q1) (β t.q0)
    · by_cases hw2 : w = t.q2
      · subst hw2
        simp only [Function.update_of_ne hw1, Function.update_self, d2]
        exact zmod2_add_assoc_cancel (β t.q2) (β t.q0)
      · simp [Function.update_of_ne hw1, Function.update_of_ne hw2, γ]
  rw [hrestore]
  congr 1
  have hbs : ∀ b : ZMod 2, bitSign b = (-1 : ℂ) ^ b.val := by
    intro b
    rcases bit_cases b with rfl | rfl
    · simp [bitSign]
    · have h10 : ((1 : ZMod 2) = 0) = False := by decide
      simp [bitSign, h10]
  rw [hbs (β t.q0),
    hbs (t.outBit β),
    InPlaceFullAddSlice.TempPhaseProg.neg_one_pow_zmod2_mul,
    InPlaceFullAddSlice.TempPhaseProg.neg_one_pow_zmod2_mul]
  congr 2

private theorem single_comm_projZeroAll {n : ℕ} (g : PrimitiveGate 1) (w : Wire n)
    (k : ℕ) (scr : Fin k → Wire n) (hw : ∀ j : Fin k, w ≠ scr j) :
    (Circuit.single g w).eval.1 * projZeroAll k scr =
      projZeroAll k scr * (Circuit.single g w).eval.1 := by
  apply matrix_ext_ket; intro β
  rw [Circuit.eval_single, QRegister.embedUnitary_val]
  have hpres (b : ZMod 2) :
      (∀ j : Fin k, (Function.update β w b) (scr j) = 0) ↔ (∀ j : Fin k, β (scr j) = 0) := by
    refine ⟨fun h j => ?_, fun h j => ?_⟩
    · have hj := h j; rwa [Function.update_of_ne (hw j).symm] at hj
    · rw [Function.update_of_ne (hw j).symm]; exact h j
  by_cases hs : ∀ j : Fin k, β (scr j) = 0
  · simp only [InPlaceFullAddSlice.mul_mulVec_prog, singleton_embedMatrix_mulVec_ket_local,
      Matrix.mulVec_add,
      Matrix.mulVec_smul, ket_projZeroAll, hs, (hpres 0).mpr hs, (hpres 1).mpr hs,
      imp_true_iff, ↓reduceIte]
  · simp only [InPlaceFullAddSlice.mul_mulVec_prog, singleton_embedMatrix_mulVec_ket_local,
      Matrix.mulVec_add,
      Matrix.mulVec_smul, ket_projZeroAll, hs, mt (hpres 0).mp hs, mt (hpres 1).mp hs,
      ↓reduceIte, Matrix.mulVec_zero, smul_zero, add_zero]

private theorem cnot_comm_projZeroAll {n : ℕ} (c t : Wire n) (hct : c ≠ t)
    (k : ℕ) (scr : Fin k → Wire n) (ht : ∀ j : Fin k, t ≠ scr j) :
    (Circuit.CNOT c t hct).eval.1 * projZeroAll k scr =
      projZeroAll k scr * (Circuit.CNOT c t hct).eval.1 := by
  apply matrix_ext_ket; intro β
  have hpres :
      (∀ j : Fin k, (Function.update β t (β t + β c)) (scr j) = 0) ↔
        (∀ j : Fin k, β (scr j) = 0) := by
    refine ⟨fun h j => ?_, fun h j => ?_⟩
    · have hj := h j; rwa [Function.update_of_ne (ht j).symm] at hj
    · rw [Function.update_of_ne (ht j).symm]; exact h j
  by_cases hs : ∀ j : Fin k, β (scr j) = 0
  · simp only [InPlaceFullAddSlice.mul_mulVec_prog, ket_CNOT, ket_projZeroAll, hs, hpres.mpr hs,
      imp_true_iff, ↓reduceIte]
  · simp only [InPlaceFullAddSlice.mul_mulVec_prog, ket_CNOT, ket_projZeroAll, hs, mt hpres.mp hs,
      ↓reduceIte, Matrix.mulVec_zero]

private theorem seq_comm_projZeroAll {n k : ℕ} {c₁ c₂ : Circuit n} {scr : Fin k → Wire n}
    (h₁ : c₁.eval.1 * projZeroAll k scr = projZeroAll k scr * c₁.eval.1)
    (h₂ : c₂.eval.1 * projZeroAll k scr = projZeroAll k scr * c₂.eval.1) :
    (c₁ ;;ᶜ c₂).eval.1 * projZeroAll k scr = projZeroAll k scr * (c₁ ;;ᶜ c₂).eval.1 := by
  simp only [Circuit.eval_seq, Submonoid.coe_mul]
  rw [Matrix.mul_assoc, h₁, ← Matrix.mul_assoc, h₂, Matrix.mul_assoc]

private theorem mux3Gad_comm_projZeroAll {n : ℕ} (d s a : Wire n) (hd : d ≠ a) (hs : s ≠ a)
    (k : ℕ) (scr : Fin k → Wire n) (ha : ∀ j : Fin k, a ≠ scr j) :
    (mux3Gad d s a hd hs).eval.1 * projZeroAll k scr =
      projZeroAll k scr * (mux3Gad d s a hd hs).eval.1 := by
  dsimp only [mux3Gad]
  exact seq_comm_projZeroAll (cnot_comm_projZeroAll d a hd k scr ha)
    (seq_comm_projZeroAll (single_comm_projZeroAll _ a k scr ha)
      (seq_comm_projZeroAll (cnot_comm_projZeroAll s a hs k scr ha)
        (seq_comm_projZeroAll (single_comm_projZeroAll _ a k scr ha)
          (seq_comm_projZeroAll (single_comm_projZeroAll _ a k scr ha)
            (seq_comm_projZeroAll (single_comm_projZeroAll _ a k scr ha)
              (seq_comm_projZeroAll (cnot_comm_projZeroAll d a hd k scr ha)
                (seq_comm_projZeroAll (single_comm_projZeroAll _ a k scr ha)
                  (cnot_comm_projZeroAll s a hs k scr ha))))))))

private theorem Mux3Tuple.cLoad_comm_projZeroAll {n : ℕ} (t : Mux3Tuple n)
    (k : ℕ) (scr : Fin k → Wire n)
    (hq1 : ∀ j : Fin k, t.q1 ≠ scr j) (hq2 : ∀ j : Fin k, t.q2 ≠ scr j)
    (ha : ∀ j : Fin k, t.a ≠ scr j) :
    t.cLoad.eval.1 * projZeroAll k scr = projZeroAll k scr * t.cLoad.eval.1 := by
  dsimp only [Mux3Tuple.cLoad, cLoadMux3_1Bit]
  exact seq_comm_projZeroAll (cnot_comm_projZeroAll _ _ _ k scr hq1)
    (seq_comm_projZeroAll (cnot_comm_projZeroAll _ _ _ k scr hq2)
      (seq_comm_projZeroAll (single_comm_projZeroAll _ _ k scr ha)
        (seq_comm_projZeroAll (single_comm_projZeroAll _ _ k scr ha)
          (seq_comm_projZeroAll (single_comm_projZeroAll _ _ k scr ha)
            (seq_comm_projZeroAll (mux3Gad_comm_projZeroAll _ _ _ _ _ k scr ha)
              (seq_comm_projZeroAll (mux3Gad_comm_projZeroAll _ _ _ _ _ k scr ha)
                (seq_comm_projZeroAll (single_comm_projZeroAll _ _ k scr ha)
                  (seq_comm_projZeroAll (single_comm_projZeroAll _ _ k scr ha)
                    (seq_comm_projZeroAll (single_comm_projZeroAll _ _ k scr ha)
                      (seq_comm_projZeroAll (cnot_comm_projZeroAll _ _ _ k scr ha)
                        (seq_comm_projZeroAll (cnot_comm_projZeroAll _ _ _ k scr hq2)
                          (cnot_comm_projZeroAll _ _ _ k scr hq1))))))))))))

def cLoadSeq {n : ℕ} : (m : ℕ) → (Fin m → Mux3Tuple n) → Circuit n
  | 0, _ => .identity
  | m + 1, ts => (ts 0).cLoad ;;ᶜ cLoadSeq m (fun i => ts i.succ)

@[simp]
theorem cLoadSeq_count_toff {n : ℕ} :
    ∀ (m : ℕ) (ts : Fin m → Mux3Tuple n), (cLoadSeq m ts).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, ts => by simp [cLoadSeq, cLoadSeq_count_toff]

@[simp]
theorem cLoadSeq_count_t {n : ℕ} :
    ∀ (m : ℕ) (ts : Fin m → Mux3Tuple n), (cLoadSeq m ts).count PrimitiveGate.T = 6 * m
  | 0, _ => rfl
  | m + 1, ts => by simp [cLoadSeq, cLoadSeq_count_t]; ring

private theorem cLoadSeq_comm_projZeroAll {n : ℕ} :
    ∀ (m : ℕ) (ts : Fin m → Mux3Tuple n) (k : ℕ) (scr : Fin k → Wire n),
      (∀ (i : Fin m) (j : Fin k), (ts i).q1 ≠ scr j) →
      (∀ (i : Fin m) (j : Fin k), (ts i).q2 ≠ scr j) →
      (∀ (i : Fin m) (j : Fin k), (ts i).a ≠ scr j) →
      (cLoadSeq m ts).eval.1 * projZeroAll k scr = projZeroAll k scr * (cLoadSeq m ts).eval.1
  | 0, _, _, _, _, _, _ => by simp [cLoadSeq]
  | m + 1, ts, k, scr, h1, h2, ha =>
      seq_comm_projZeroAll
        ((ts 0).cLoad_comm_projZeroAll k scr (h1 0) (h2 0) (ha 0))
        (cLoadSeq_comm_projZeroAll m (fun i => ts i.succ) k scr
          (fun i => h1 i.succ) (fun i => h2 i.succ) (fun i => ha i.succ))

def Mux3SeqDisj {n : ℕ} (m : ℕ) (ts : Fin m → Mux3Tuple n) : Prop :=
  ∀ r s : Fin m, r ≠ s →
    (ts r).a ≠ (ts s).q0 ∧ (ts r).a ≠ (ts s).q1 ∧ (ts r).a ≠ (ts s).q2 ∧
      (ts r).a ≠ (ts s).u1 ∧ (ts r).a ≠ (ts s).u2 ∧ (ts r).a ≠ (ts s).a

private theorem if_decide_eq_one_zmod2 (b : ZMod 2) :
    (if decide (b = 1) then (1 : ZMod 2) else 0) = b := by
  rcases bit_cases b with rfl | rfl <;> decide

private theorem ket_cLoadSeq {n : ℕ} :
    ∀ (m : ℕ) (ts : Fin m → Mux3Tuple n),
      Mux3SeqDisj m ts →
      ∀ (β : BitAssignment n),
        (∀ r : Fin m, β ((ts r).a) = 0) →
        (cLoadSeq m ts).eval.1.mulVec (ket β) =
          ((-1 : ℂ) ^ (∑ i : Fin m, (ts i).extraPhase β).val) •
            ket (writeSynd m (fun i => (ts i).a) (fun i => decide ((ts i).outBit β = 1)) β)
  | 0, _, _, β, _ => by simp [cLoadSeq, writeSynd]
  | m + 1, ts, hdisj, β, ha0 => by
      let y : Fin (m + 1) → Bool := fun i => decide ((ts i).outBit β = 1)
      let β' : BitAssignment n := Function.update β (ts 0).a (if y 0 then 1 else 0)
      have hy0_eq : (if y 0 then (1 : ZMod 2) else 0) = (ts 0).outBit β :=
        if_decide_eq_one_zmod2 ((ts 0).outBit β)
      have hstep0 : (ts 0).cLoad.eval.1.mulVec (ket β) =
          ((-1 : ℂ) ^ ((ts 0).extraPhase β).val) • ket β' := by
        simpa only [β', hy0_eq] using (ts 0).ket_cLoad β (ha0 0)
      have hdisj_succ : Mux3SeqDisj m (fun i => ts i.succ) :=
        fun r s hrs => hdisj r.succ s.succ (fun h => hrs (Fin.succ_injective _ h))
      have ha0_succ : ∀ r : Fin m, β' ((ts r.succ).a) = 0 := by
        intro r
        have hne := (hdisj 0 r.succ (Fin.succ_ne_zero r).symm).2.2.2.2.2
        dsimp [β']; rw [Function.update_of_ne hne.symm]; exact ha0 r.succ
      have hout_succ : ∀ i : Fin m, (ts i.succ).outBit β' = (ts i.succ).outBit β := by
        intro i
        obtain ⟨hq0, hq1, hq2, hu1, hu2, _⟩ := hdisj 0 i.succ (Fin.succ_ne_zero i).symm
        dsimp [Mux3Tuple.outBit, β']
        rw [Function.update_of_ne hq0.symm, Function.update_of_ne hq1.symm,
          Function.update_of_ne hq2.symm, Function.update_of_ne hu1.symm,
          Function.update_of_ne hu2.symm]
      have hextra_succ : ∀ i : Fin m, (ts i.succ).extraPhase β' = (ts i.succ).extraPhase β := by
        intro i
        obtain ⟨hq0, hq1, hq2, hu1, hu2, _⟩ := hdisj 0 i.succ (Fin.succ_ne_zero i).symm
        dsimp [Mux3Tuple.extraPhase, β']
        rw [Function.update_of_ne hq0.symm, Function.update_of_ne hq1.symm,
          Function.update_of_ne hq2.symm, Function.update_of_ne hu1.symm,
          Function.update_of_ne hu2.symm]
      have hy_succ : (fun i : Fin m => decide ((ts i.succ).outBit β' = 1)) =
          (fun i : Fin m => y i.succ) := by
        funext i; dsimp [y]; rw [hout_succ i]
      dsimp only [cLoadSeq]
      rw [eval_seq_mulVec, hstep0, Matrix.mulVec_smul,
        ket_cLoadSeq m (fun i => ts i.succ) hdisj_succ β' ha0_succ,
        hy_succ, smul_smul]
      simp only [hextra_succ]
      rw [Fin.sum_univ_succ, ← InPlaceFullAddSlice.TempPhaseProg.neg_one_pow_zmod2_mul, mul_comm]
      rfl

def cFixSeq {n : ℕ} : (m : ℕ) → (Fin m → Mux3Tuple n) → (Fin m → Bool) → Circuit n
  | 0, _, _ => .identity
  | m + 1, ts, g =>
      (if g 0 then (ts 0).cFix else .identity) ;;ᶜ
        cFixSeq m (fun i => ts i.succ) (fun i => g i.succ)

@[simp]
theorem cFixSeq_count_toff {n : ℕ} :
    ∀ (m : ℕ) (ts : Fin m → Mux3Tuple n) (g : Fin m → Bool),
      (cFixSeq m ts g).count PrimitiveGate.TOFF = 0
  | 0, _, _ => rfl
  | m + 1, ts, g => by
      simp only [cFixSeq, Circuit.count_seq, cFixSeq_count_toff]
      split <;> simp

@[simp]
theorem cFixSeq_count_t {n : ℕ} :
    ∀ (m : ℕ) (ts : Fin m → Mux3Tuple n) (g : Fin m → Bool),
      (cFixSeq m ts g).count PrimitiveGate.T = 0
  | 0, _, _ => rfl
  | m + 1, ts, g => by
      simp only [cFixSeq, Circuit.count_seq, cFixSeq_count_t]
      split <;> simp

private theorem writeSynd_apply_mem {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n),
      Function.Injective qs →
      ∀ (y : Fin m → Bool) (β : BitAssignment n) (r : Fin m),
        writeSynd m qs y β (qs r) = if y r then 1 else 0 :=
          FastMidKick275Aux.fmkWriteSynd_apply_mem (n := n)

noncomputable def syndSignOfBits : (m : ℕ) → (Fin m → Bool) → (Fin m → Bool) → ℂ
  | 0, _, _ => 1
  | m + 1, g, y =>
      (if g 0 then bitSign (if y 0 then 1 else 0) else 1) *
        syndSignOfBits m (fun i => g i.succ) (fun i => y i.succ)

private theorem syndSign_writeSynd_eq {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n),
      Function.Injective qs →
      ∀ (g y : Fin m → Bool) (β : BitAssignment n),
        syndSign m qs g (writeSynd m qs y β) = syndSignOfBits m g y
  | 0, _, _, _, _, _ => rfl
  | m + 1, qs, hqs, g, y, β => by
      have h0 : writeSynd (m + 1) qs y β (qs 0) = if y 0 then 1 else 0 :=
        writeSynd_apply_mem (m + 1) qs hqs y β 0
      have hrest : syndSign m (fun i => qs i.succ) (fun i => g i.succ)
          (writeSynd (m + 1) qs y β) = syndSignOfBits m (fun i => g i.succ) (fun i => y i.succ) :=
            by
        rw [writeSynd]
        exact syndSign_writeSynd_eq m (fun i => qs i.succ)
          (fun _ _ h => Fin.succ_injective _ (hqs h)) (fun i => g i.succ) (fun i => y i.succ) _
      rw [syndSign, syndSignOfBits, h0, hrest]
      rfl

private theorem ket_cFixSeq {n : ℕ} :
    ∀ (m : ℕ) (ts : Fin m → Mux3Tuple n) (g : Fin m → Bool) (β : BitAssignment n),
      (cFixSeq m ts g).eval.1.mulVec (ket β) =
        syndSignOfBits m g (fun i => decide ((ts i).outBit β = 1)) • ket β
  | 0, _, _, β => by simp [cFixSeq, syndSignOfBits]
  | m + 1, ts, g, β => by
      have hstep0 : (if g 0 then (ts 0).cFix else .identity).eval.1.mulVec (ket β) =
          (if g 0 then bitSign ((ts 0).outBit β) else 1) • ket β := by
        cases g 0
        · simp
        · simpa using (ts 0).ket_cFix β
      dsimp only [cFixSeq, syndSignOfBits]
      rw [eval_seq_mulVec, hstep0, Matrix.mulVec_smul,
        ket_cFixSeq m (fun i => ts i.succ) (fun i => g i.succ) β,
        smul_smul, if_decide_eq_one_zmod2 ((ts 0).outBit β), mul_comm]

private theorem preservesStoreConst_measureAndBranchSeq
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var) :
    ∀ (m : ℕ) (qs : Fin m → QRegister 1 n) (fixup : (Fin m → Bool) → DynamicCircuit Var n),
      (∀ g, PreservesStoreConst (fixup g)) →
      PreservesStoreConst (measureAndBranchSeq v m qs fixup)
  | 0, _, fixup, hfix => by
      unfold measureAndBranchSeq
      exact hfix Fin.elim0
  | m + 1, qs, fixup, hfix => by
      unfold measureAndBranchSeq
      intro M_obs
      obtain ⟨M_T, hT⟩ := preservesStoreConst_measureAndBranchSeq v m (fun i => qs i.succ)
        (fun rest => fixup (Fin.cons true rest)) (fun rest => hfix (Fin.cons true rest)) M_obs
      obtain ⟨M_F, hF⟩ := preservesStoreConst_measureAndBranchSeq v m (fun i => qs i.succ)
        (fun rest => fixup (Fin.cons false rest)) (fun rest => hfix (Fin.cons false rest)) M_obs
      let cStep : DynamicCircuit Var n :=
        .seq (.measure v (qs 0))
          (dynQIfVar v
            (measureAndBranchSeq v m (fun i => qs i.succ) (fun rest => fixup (Fin.cons true rest)))
            (measureAndBranchSeq v m (fun i => qs i.succ) (fun rest =>
              fixup (Fin.cons false rest))))
      refine ⟨wp cStep.compile (fun _ ↦ M_obs) default, ?_⟩
      funext σ
      apply Subtype.ext
      simp only [cStep, DynamicCircuit.compile_seq, DynamicCircuit.compile_measure,
        DynamicCircuit.compile_qIf, QProg.measureRegister, wp_qSeq, wp_qIf,
        wp_qMeasure_apply, qMeasure_obs_map_coe, CQAssertionCompat.subst_apply, hT, hF]
      have hv_eq : ∀ val' : ℤ, (σ.subst v val') v = ((default : Store Var).subst v val') v := by
        intro val'; simp [Store.subst]
      congr 1; funext o
      simp

private theorem toTempCtx_valid_and_bits_probe {M : ℕ} (probe : InPlaceFullAddSlice.TempPhaseProg M)
    :
    ∀ (p : RawSsa M) {cur endCur : ℕ},
      RawSsa.Wf cur endCur p →
      endCur ≤ M →
      InPlaceFullAddSlice.ValidCleanRem M (M - endCur) probe →
      (∀ β : BitAssignment M,
        InPlaceFullAddSlice.cleanRem M (M - endCur) β → probe.evalBits β = β) →
      (∀ β : BitAssignment M, InPlaceFullAddSlice.cleanRem M (M - cur) β →
        (p.toTempCtx.plug probe).evalBits β = β) ∧
      InPlaceFullAddSlice.ValidCleanRem M (M - cur) (p.toTempCtx.plug probe)
  | .done, _, _, hwf, _, hPVal, hPBits => by
      cases hwf
      exact ⟨hPBits, hPVal⟩
  | .x q rest, cur, _, ⟨hq, hwf⟩, hEnd, hPVal, hPBits => by
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_valid_and_bits_probe probe rest hwf hEnd hPVal hPBits
      have hPres : ∀ β : BitAssignment M, InPlaceFullAddSlice.cleanRem M (M - cur) β →
          InPlaceFullAddSlice.cleanRem M (M - cur) (Function.update β q (β q + 1)) := by
        intro β hβ w hw
        rw [Function.update_of_ne (Fin.ne_of_val_ne (by omega))]
        exact hβ w hw
      refine ⟨fun β hβ ↦ ?_, ?_⟩
      · dsimp only [RawSsa.toTempCtx, MomSlot1GeomPriority288.TempCtx.plug,
          InPlaceFullAddSlice.TempPhaseProg.evalBits,
          InPlaceFullAddSlice.CliffProg.eval]
        rw [ihBits _ (hPres β hβ)]
        funext w
        by_cases hw : w = q
        · subst hw; simp only [Function.update_self]; exact zmod2_add_assoc_cancel _ _
        · simp [Function.update_of_ne hw]
      · dsimp only [RawSsa.toTempCtx, MomSlot1GeomPriority288.TempCtx.plug,
          InPlaceFullAddSlice.ValidCleanRem]
        refine ⟨M - cur, Nat.sub_le M cur, trivial,
          ⟨M - cur, Nat.sub_le M cur, ihVal, trivial, fun β₁ hβ₁ ↦ ?_⟩,
          fun β hβ ↦ hPres β hβ⟩
        rw [ihBits β₁ hβ₁]; exact hβ₁
  | .cnot c t hct rest, cur, _, ⟨hc, ht, hwf⟩, hEnd, hPVal, hPBits => by
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_valid_and_bits_probe probe rest hwf hEnd hPVal hPBits
      have hPres : ∀ β : BitAssignment M, InPlaceFullAddSlice.cleanRem M (M - cur) β →
          InPlaceFullAddSlice.cleanRem M (M - cur) (Function.update β t (β t + β c)) := by
        intro β hβ w hw
        rw [Function.update_of_ne (Fin.ne_of_val_ne (by omega))]
        exact hβ w hw
      refine ⟨fun β hβ ↦ ?_, ?_⟩
      · dsimp only [RawSsa.toTempCtx, MomSlot1GeomPriority288.TempCtx.plug,
          InPlaceFullAddSlice.TempPhaseProg.evalBits,
          InPlaceFullAddSlice.CliffProg.eval]
        rw [ihBits _ (hPres β hβ), Function.update_of_ne hct]
        funext w
        by_cases hw : w = t
        · subst hw; simp only [Function.update_self]; exact zmod2_add_assoc_cancel _ _
        · simp [Function.update_of_ne hw]
      · dsimp only [RawSsa.toTempCtx, MomSlot1GeomPriority288.TempCtx.plug,
          InPlaceFullAddSlice.ValidCleanRem]
        refine ⟨M - cur, Nat.sub_le M cur, trivial,
          ⟨M - cur, Nat.sub_le M cur, ihVal, trivial, fun β₁ hβ₁ ↦ ?_⟩,
          fun β hβ ↦ hPres β hβ⟩
        rw [ihBits β₁ hβ₁]; exact hβ₁
  | .skipZero rest, cur, _, ⟨_, hwf⟩, hEnd, hPVal, hPBits => by
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_valid_and_bits_probe probe rest hwf hEnd hPVal hPBits
      exact ⟨fun β hβ ↦ ihBits β (fun w hw ↦ hβ w (by omega)),
        MomSlot1GeomPriority288.validCleanRem_mono (by omega) ihVal⟩
  | .andClean anc c₁ c₂ h₁₂ hc1a hc2a rest, cur, _, ⟨hanc_val, _, _, hwf⟩, hEnd, hPVal, hPBits => by
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_valid_and_bits_probe probe rest hwf hEnd hPVal hPBits
      have hPres : ∀ β : BitAssignment M, InPlaceFullAddSlice.cleanRem M (M - cur) β →
          InPlaceFullAddSlice.cleanRem M (M -
            (cur + 1)) (Function.update β anc (β anc + β c₁ * β c₂)) := by
        intro β hβ w hw
        rw [Function.update_of_ne (Fin.ne_of_val_ne (by omega))]
        exact hβ w (by omega)
      refine ⟨fun β hβ ↦ ?_, ?_⟩
      · dsimp only [RawSsa.toTempCtx, MomSlot1GeomPriority288.TempCtx.plug,
          InPlaceFullAddSlice.TempPhaseProg.evalBits]
        rw [ihBits _ (hPres β hβ), Function.update_of_ne hc1a, Function.update_of_ne hc2a]
        funext w
        by_cases hw : w = anc
        · subst hw; rw [Function.update_self,
            Function.update_self]; exact zmod2_add_assoc_cancel _ _
        · rw [Function.update_of_ne hw, Function.update_of_ne hw]
      · dsimp only [RawSsa.toTempCtx, MomSlot1GeomPriority288.TempCtx.plug,
          InPlaceFullAddSlice.ValidCleanRem]
        refine ⟨by omega, by simpa only [hanc_val] using ihVal, fun β₁ hβ₁ ↦ ?_⟩
        have hβ₁' : InPlaceFullAddSlice.cleanRem M (M - (cur + 1)) β₁ := by
          simpa only [hanc_val] using hβ₁
        rw [ihBits β₁ hβ₁']
        exact ⟨rfl, rfl, rfl⟩

def mux3Tuple185 (i : Fin 8) : Mux3Tuple 185 where
  q0 := ⟨0 + i.val, by omega⟩
  q1 := ⟨8 + i.val, by omega⟩
  q2 := ⟨16 + i.val, by omega⟩
  u1 := ⟨140, by decide⟩
  u2 := ⟨141, by decide⟩
  a := ⟨143 + i.val, by omega⟩
  hq01 := Fin.ne_of_val_ne (by dsimp; omega)
  hq02 := Fin.ne_of_val_ne (by dsimp; omega)
  hq12 := Fin.ne_of_val_ne (by dsimp; omega)
  hq0a := Fin.ne_of_val_ne (by dsimp; omega)
  hq1a := Fin.ne_of_val_ne (by dsimp; omega)
  hq2a := Fin.ne_of_val_ne (by dsimp; omega)
  hu1q0 := Fin.ne_of_val_ne (by dsimp; omega)
  hu1q1 := Fin.ne_of_val_ne (by dsimp; omega)
  hu1q2 := Fin.ne_of_val_ne (by dsimp; omega)
  hu1a := Fin.ne_of_val_ne (by dsimp; omega)
  hu2q0 := Fin.ne_of_val_ne (by dsimp; omega)
  hu2q1 := Fin.ne_of_val_ne (by dsimp; omega)
  hu2q2 := Fin.ne_of_val_ne (by dsimp; omega)
  hu2a := Fin.ne_of_val_ne (by dsimp; omega)

def writeMux8_185 (γ : BitAssignment 185) : BitAssignment 185 :=
  writeSynd 8 (fun i => (mux3Tuple185 i).a) (fun i => decide ((mux3Tuple185 i).outBit γ = 1)) γ

private theorem mux3Tuple185_a_injective : Function.Injective (fun i : Fin 8 =>
    (mux3Tuple185 i).a) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  dsimp [mux3Tuple185] at hv
  exact Fin.ext (by omega)

private theorem writeMux8_185_apply (γ : BitAssignment 185) (w : Wire 185) :
    writeMux8_185 γ w =
      if h : 143 ≤ w.val ∧ w.val < 151 then
        (mux3Tuple185 ⟨w.val - 143, by omega⟩).outBit γ
      else γ w := by
  dsimp only [writeMux8_185]
  by_cases hw : 143 ≤ w.val ∧ w.val < 151
  · rw [dite_eq_left hw]
    let r : Fin 8 := ⟨w.val - 143, by omega⟩
    change writeSynd 8 (fun i => (mux3Tuple185 i).a) (fun i =>
      decide ((mux3Tuple185 i).outBit γ = 1)) γ w =
      (mux3Tuple185 r).outBit γ
    have hwr : w = (mux3Tuple185 r).a := by ext; dsimp [mux3Tuple185, r]; omega
    rw [hwr, writeSynd_apply_mem 8 _ mux3Tuple185_a_injective]
    exact if_decide_eq_one_zmod2 ((mux3Tuple185 r).outBit γ)
  · rw [dite_eq_right hw]
    refine writeSynd_apply_of_not_mem 8 _ _ γ w (fun r h => hw ?_)
    have hv := congrArg Fin.val h
    dsimp [mux3Tuple185] at hv
    omega

private theorem writeSynd_rComb_eq_writeMux8 {n : ℕ} (rComb : QRegister 185 n)
    (m : ℕ) (qs185 : Fin m → Wire 185) (y : Fin m → Bool) (β : BitAssignment n) :
    (fun idx ↦ (writeSynd m (fun i => rComb (qs185 i)) y β) (rComb idx)) =
      writeSynd m qs185 y (fun idx ↦ β (rComb idx)) := by
  induction m generalizing β with
  | zero => rfl
  | succ m ih =>
      simp only [writeSynd]
      have hupd : (fun idx ↦
        Function.update β (rComb (qs185 0)) (if y 0 then 1 else 0) (rComb idx)) =
          Function.update (fun idx ↦ β (rComb idx)) (qs185 0) (if y 0 then 1 else 0) := by
        funext idx
        by_cases h : idx = qs185 0
        · subst h; simp [Function.update_self]
        · simp [Function.update_of_ne h, Function.update_of_ne (rComb.wires.injective.ne h)]
      rw [ih (fun i => qs185 i.succ) (fun i => y i.succ) _, hupd]

def probe143 : InPlaceFullAddSlice.TempPhaseProg 185 :=
  .tempAnd ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨143, by decide⟩
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
    .nil

private theorem probe143_evalBits (γ : BitAssignment 185) : probe143.evalBits γ = γ := by
  dsimp only [probe143, InPlaceFullAddSlice.TempPhaseProg.evalBits]
  have h0 : Function.update γ ⟨143, by decide⟩
      (γ ⟨143, by decide⟩ + γ ⟨0, by decide⟩ * γ ⟨1, by decide⟩) ⟨0, by decide⟩ = γ ⟨0,
        by decide⟩ :=
    Function.update_of_ne (Fin.ne_of_val_ne (by decide)) _ _
  have h1 : Function.update γ ⟨143, by decide⟩
      (γ ⟨143, by decide⟩ + γ ⟨0, by decide⟩ * γ ⟨1, by decide⟩) ⟨1, by decide⟩ = γ ⟨1,
        by decide⟩ :=
    Function.update_of_ne (Fin.ne_of_val_ne (by decide)) _ _
  rw [h0, h1, Function.update_self, Function.update_idem,
    zmod2_add_assoc_cancel (γ ⟨143, by decide⟩) (γ ⟨0, by decide⟩ * γ ⟨1, by decide⟩),
    Function.update_eq_self]

private theorem probe143_valid42 : InPlaceFullAddSlice.ValidCleanRem 185 42 probe143 :=
  ⟨by decide, trivial, fun _ _ ↦ ⟨rfl, rfl, rfl⟩⟩

private theorem probe143_rem_ge {rem : ℕ} (hv : InPlaceFullAddSlice.ValidCleanRem 185 rem probe143)
    : 42 ≤ rem := by
  have h : 185 - rem ≤ 143 := hv.1
  omega

noncomputable def compileAnchoredMux3PwuDyn {Var : Type} {n mWork : ℕ}
    (v : Var) (rAct : QRegister 110 n) (rWork : QRegister mWork n)
    (hdisj : rAct.DisjointWires rWork) (hw_len : 75 ≤ mWork)
    (pOuter : SsaProg 185 110 143)
    (pInner : SsaProg 185 151 185)
    (wPhi wCoin : Wire 185) (hne : wPhi ≠ wCoin) :
    DynamicCircuit Var n :=
  let rSub : QRegister 75 n := rWork.slice 0 75 (by omega)
  let rComb : QRegister 185 n := rAct.concat rSub (hdisj.compose_right _)
  let ts : Fin 8 → Mux3Tuple n := fun i ↦ (mux3Tuple185 i).map rComb
  let qs : Fin 8 → Wire n := fun i ↦ (ts i).a
  let cz : Circuit n :=
    MomSlot1GeomPriority288.czCircuit (rComb wPhi) (rComb wCoin) (rComb.wires.injective.ne hne)
  let cInner : DynamicCircuit Var n := toDynWithDyn v rComb (.circuit cz) pInner.toTempCtx
  let cBody : DynamicCircuit Var n := .seq (.circuit (cLoadSeq 8 ts)) cInner
  let inner143 : DynamicCircuit Var n :=
    .seq cBody
      (.seq (.circuit (hadamardAll 8 qs))
        (measureAndBranchSeq v 8 (fun r => QRegister.singleton (qs r))
          (fun g => .seq (.circuit (xReset 8 qs g)) (.circuit (cFixSeq 8 ts g)))))
  toDynWithDyn v rComb inner143 pOuter.toTempCtx

private theorem compileAnchoredMux3PwuDyn_count_toff {Var : Type} {n mWork : ℕ}
    (v : Var) (rAct : QRegister 110 n) (rWork : QRegister mWork n)
    (hdisj : rAct.DisjointWires rWork) (hw_len : 75 ≤ mWork)
    (pOuter : SsaProg 185 110 143)
    (pInner : SsaProg 185 151 185)
    (wPhi wCoin : Wire 185) (hne : wPhi ≠ wCoin) :
    (compileAnchoredMux3PwuDyn v rAct rWork hdisj hw_len pOuter pInner wPhi wCoin hne).count
      PrimitiveGate.TOFF = 0 := by
  let rSub : QRegister 75 n := rWork.slice 0 75 (by omega)
  let rComb : QRegister 185 n := rAct.concat rSub (hdisj.compose_right _)
  let ts : Fin 8 → Mux3Tuple n := fun i ↦ (mux3Tuple185 i).map rComb
  let qs : Fin 8 → Wire n := fun i ↦ (ts i).a
  have hbr : ∀ g : Fin 8 → Bool,
      (DynamicCircuit.seq (Var := Var)
        (.circuit (xReset 8 qs g))
        (.circuit (cFixSeq 8 ts g))).count PrimitiveGate.TOFF = 0 := by
    intro g; simp [DynamicCircuit.count]
  let cz : Circuit n :=
    MomSlot1GeomPriority288.czCircuit (rComb wPhi) (rComb wCoin) (rComb.wires.injective.ne hne)
  change (toDynWithDyn v rComb
    (.seq (.seq (.circuit (cLoadSeq 8 ts)) (toDynWithDyn v rComb (.circuit cz) pInner.toTempCtx))
      (.seq (.circuit (hadamardAll 8 qs))
        (measureAndBranchSeq v 8 (fun r => QRegister.singleton (qs r))
          (fun g => .seq (.circuit (xReset 8 qs g)) (.circuit (cFixSeq 8 ts g))))))
    pOuter.toTempCtx).count PrimitiveGate.TOFF = 0
  refine toDynWithDyn_count_toff v rComb _ ?_ pOuter.toTempCtx
  have hcz : (DynamicCircuit.circuit (Var := Var) cz).count PrimitiveGate.TOFF = 0 := by
    dsimp only [cz]; simp [DynamicCircuit.count, MomSlot1GeomPriority288.czCircuit_count_toff]
  simp [DynamicCircuit.count, cLoadSeq_count_toff, count_hadamardAll_toff,
    toDynWithDyn_count_toff v rComb _ hcz pInner.toTempCtx,
    measureAndBranchSeq_count_eq_zero v PrimitiveGate.TOFF 8 (fun r =>
      QRegister.singleton (qs r)) _ hbr]

private theorem compileAnchoredMux3PwuDyn_count_t {Var : Type} {n mWork : ℕ}
    (v : Var) (rAct : QRegister 110 n) (rWork : QRegister mWork n)
    (hdisj : rAct.DisjointWires rWork) (hw_len : 75 ≤ mWork)
    (pOuter : SsaProg 185 110 143)
    (pInner : SsaProg 185 151 185)
    (wPhi wCoin : Wire 185) (hne : wPhi ≠ wCoin) :
    (compileAnchoredMux3PwuDyn v rAct rWork hdisj hw_len pOuter pInner wPhi wCoin hne).count
      PrimitiveGate.T = 4 * pOuter.countAnd + 48 + 4 * pInner.countAnd := by
  let rSub : QRegister 75 n := rWork.slice 0 75 (by omega)
  let rComb : QRegister 185 n := rAct.concat rSub (hdisj.compose_right _)
  let ts : Fin 8 → Mux3Tuple n := fun i ↦ (mux3Tuple185 i).map rComb
  let qs : Fin 8 → Wire n := fun i ↦ (ts i).a
  let cz : Circuit n :=
    MomSlot1GeomPriority288.czCircuit (rComb wPhi) (rComb wCoin) (rComb.wires.injective.ne hne)
  have hbr : ∀ g : Fin 8 → Bool,
      (DynamicCircuit.seq (Var := Var)
        (.circuit (xReset 8 qs g))
        (.circuit (cFixSeq 8 ts g))).count PrimitiveGate.T = 0 := by
    intro g; simp [DynamicCircuit.count]
  change (toDynWithDyn v rComb
    (.seq (.seq (.circuit (cLoadSeq 8 ts)) (toDynWithDyn v rComb (.circuit cz) pInner.toTempCtx))
      (.seq (.circuit (hadamardAll 8 qs))
        (measureAndBranchSeq v 8 (fun r => QRegister.singleton (qs r))
          (fun g => .seq (.circuit (xReset 8 qs g)) (.circuit (cFixSeq 8 ts g))))))
    pOuter.toTempCtx).count PrimitiveGate.T = 4 * pOuter.countAnd + 48 + 4 * pInner.countAnd
  have hcz : cz.count PrimitiveGate.T = 0 := by
    dsimp only [cz]; exact MomSlot1GeomPriority288.czCircuit_count_t _ _ _
  rw [toDynWithDyn_count_t]
  simp only [DynamicCircuit.count, cLoadSeq_count_t, count_hadamardAll_t,
    measureAndBranchSeq_count_eq_zero v PrimitiveGate.T 8 (fun r =>
      QRegister.singleton (qs r)) _ hbr,
    toDynWithDyn_count_t, hcz,
    pOuter.toTempCtx_countTempAnd, pInner.toTempCtx_countTempAnd]
  ring

private theorem embedUnitary_phaseDiagAct_mulVec_ket {k n : ℕ} (r : QRegister k n)
    (ph : BitAssignment k → ZMod 2) (β : BitAssignment n) :
    (r.embedUnitary (phaseDiagAct ph)).1.mulVec (ket β) =
      ((-1 : ℂ) ^ (ph (fun idx ↦ β (r idx))).val) • ket β := by
  let γ : BitAssignment k := fun idx ↦ β (r idx)
  have hw : InPlaceFullAddSlice.writeRegProg β r γ = β := by
    funext w
    by_cases hmem : w ∈ Set.range r.wires
    · obtain ⟨idx, rfl⟩ := hmem
      rw [InPlaceFullAddSlice.writeRegProg_apply_reg]
    · exact InPlaceFullAddSlice.writeRegProg_apply_of_not_mem _ _ _ _ hmem
  have hbb : basisBits k (InPlaceFullAddSlice.localIdxProg r β) = γ :=
    (basisBitsEquiv k).apply_symm_apply γ
  rw [QRegister.embedUnitary_val, InPlaceFullAddSlice.embedMatrix_mulVec_ket_prog]
  have hEval : ∀ l : Fin (2 ^ k),
      (phaseDiagAct ph).1 l (InPlaceFullAddSlice.localIdxProg r β) =
        if l = InPlaceFullAddSlice.localIdxProg r β then ((-1 : ℂ) ^ (ph γ).val) else 0 := by
    intro l
    by_cases hl : l = InPlaceFullAddSlice.localIdxProg r β
    · subst hl
      simp [phaseDiagAct, hbb]
    · simp [phaseDiagAct, hl]
  simp_rw [hEval, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hbb, hw]
  rfl

private theorem realizes_compileAnchoredMux3PwuDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mWork : ℕ}
    (v : Var) (rAct : QRegister 110 n) (rWork : QRegister mWork n)
    (hdisj : rAct.DisjointWires rWork) (hw_len : 75 ≤ mWork)
    (pOuter : SsaProg 185 110 143)
    (pInner : SsaProg 185 151 185)
    (wPhi wCoin : Wire 185) (hne : wPhi ≠ wCoin)
    (pred : BitAssignment 110 → ZMod 2)
    (hOrth : ∀ α : BitAssignment 110,
      pOuter.eval (padZeroBits (mClean := 75) α) ⟨140, by decide⟩ *
        pOuter.eval (padZeroBits (mClean := 75) α) ⟨141, by decide⟩ = 0)
    (hKick : ∀ α : BitAssignment 110,
      pInner.eval (writeMux8_185 (pOuter.eval (padZeroBits (mClean := 75) α))) wPhi *
        pInner.eval (writeMux8_185 (pOuter.eval (padZeroBits (mClean := 75) α))) wCoin = pred α) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      (phaseDiagAct pred)
      (compileAnchoredMux3PwuDyn v rAct rWork hdisj hw_len pOuter pInner wPhi wCoin hne) := by
  let rSub : QRegister 75 n := rWork.slice 0 75 (by omega)
  let rComb : QRegister 185 n := rAct.concat rSub (hdisj.compose_right _)
  let ts : Fin 8 → Mux3Tuple n := fun i ↦ (mux3Tuple185 i).map rComb
  let qs : Fin 8 → Wire n := fun i ↦ (ts i).a
  let scr34 : Fin 34 → Wire n := InPlaceFullAddSlice.tailScr rComb 34 (by decide)
  let cz : Circuit n :=
    MomSlot1GeomPriority288.czCircuit (rComb wPhi) (rComb wCoin) (rComb.wires.injective.ne hne)
  let cInner : DynamicCircuit Var n := toDynWithDyn v rComb (.circuit cz) pInner.toTempCtx
  let cLoad8 : Circuit n := cLoadSeq 8 ts
  let cBody : DynamicCircuit Var n := .seq (.circuit cLoad8) cInner
  let inner143 : DynamicCircuit Var n :=
    .seq cBody
      (.seq (.circuit (hadamardAll 8 qs))
        (measureAndBranchSeq v 8 (fun r => QRegister.singleton (qs r))
          (fun g => .seq (.circuit (xReset 8 qs g)) (.circuit (cFixSeq 8 ts g)))))
  have hqs_inj : Function.Injective qs :=
    fun i j hij ↦ mux3Tuple185_a_injective (rComb.wires.injective hij)
  have hwire_scr : ∀ (f : Fin 8 → Fin 185), (∀ i, (f i).val < 151) →
      ∀ (r : Fin 8) (j : Fin 34), rComb (f r) ≠ scr34 j := fun f hf r j h ↦ by
    have hv := congrArg Fin.val (rComb.wires.injective h)
    have hlt := hf r
    dsimp [scr34, InPlaceFullAddSlice.tailScr] at hv
    omega
  have hqs_scr_disj : ∀ (r : Fin 8) (j : Fin 34), qs r ≠ scr34 j :=
    hwire_scr (fun r ↦ (mux3Tuple185 r).a) fun r ↦ by
      dsimp [mux3Tuple185]
      omega
  have hq1_scr_disj : ∀ (r : Fin 8) (j : Fin 34), (ts r).q1 ≠ scr34 j :=
    hwire_scr (fun r ↦ (mux3Tuple185 r).q1) fun r ↦ by
      dsimp [mux3Tuple185]
      omega
  have hq2_scr_disj : ∀ (r : Fin 8) (j : Fin 34), (ts r).q2 ≠ scr34 j :=
    hwire_scr (fun r ↦ (mux3Tuple185 r).q2) fun r ↦ by
      dsimp [mux3Tuple185]
      omega
  have hts_seq_disj : Mux3SeqDisj 8 ts := by
    intro r s hrs
    have hrs_val : r.val ≠ s.val := fun h ↦ hrs (Fin.ext h)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact rComb.wires.injective.ne (Fin.ne_of_val_ne (by dsimp [mux3Tuple185]; omega))
  obtain ⟨hBitsIn, hValIn⟩ := pInner.toTempCtx_valid_and_bits (le_refl 185)
  have hValIn34 : InPlaceFullAddSlice.ValidCleanRem 185 34 (pInner.toTempCtx.plug .nil) := by
    simpa using hValIn
  obtain ⟨U_in, hRealIn, hKetIn⟩ :=
    realizes_toDynWithDyn_of_valid v rComb 0 (Nat.zero_le 185) .nil
      (fun _ _ ↦ Nat.zero_le _) (fun _ ↦ rfl)
      (.circuit cz) cz.eval (RealizesCleanUnitary.circuit v _ cz)
      (fun γ : BitAssignment 185 ↦ γ wPhi * γ wCoin)
      (fun β ↦
        MomSlot1GeomPriority288.ket_czCircuit (rComb wPhi) (rComb wCoin)
        (rComb.wires.injective.ne hne) β)
      pInner.toTempCtx 34 (by decide) hValIn34
  let P_scr34 := projZeroAll 34 scr34
  have hPs34_herm : P_scr34ᴴ = P_scr34 := projZeroAll_conjTranspose 34 _
  have hLoadComm : cLoad8.eval.1 * P_scr34 = P_scr34 * cLoad8.eval.1 :=
    cLoadSeq_comm_projZeroAll 8 ts 34 scr34 hq1_scr_disj hq2_scr_disj hqs_scr_disj
  have hPs34_idem : P_scr34 * P_scr34 = P_scr34 := by
    apply matrix_ext_ket; intro β
    simp only [P_scr34, InPlaceFullAddSlice.mul_mulVec_prog, ket_projZeroAll]
    by_cases hs : ∀ j : Fin 34, β (scr34 j) = 0 <;> simp [hs, ket_projZeroAll]
  have hLoadClean : P_scr34 * (cLoad8.eval.1 * P_scr34) = cLoad8.eval.1 * P_scr34 := by
    rw [← Matrix.mul_assoc, ← hLoadComm, Matrix.mul_assoc, hPs34_idem]
  have hBody : RealizesCleanUnitary v P_scr34 cBody (U_in * cLoad8.eval) :=
    InPlaceFullAddSlice.RealizesCleanUnitary_seq_asym hPs34_herm hPs34_herm
      (RealizesCleanUnitary.circuit v P_scr34 cLoad8) hRealIn hLoadClean
  let phMid : BitAssignment 185 → ZMod 2 := fun γ ↦
    (∑ i : Fin 8, (mux3Tuple185 i).extraPhase γ) +
      pInner.eval (writeMux8_185 γ) wPhi * pInner.eval (writeMux8_185 γ) wCoin
  let U_mid : Unitary (2 ^ n) := rComb.embedUnitary (phaseDiagAct phMid)
  have hUmid_ket : ∀ β : BitAssignment n,
      U_mid.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (phMid (fun idx ↦ β (rComb idx))).val) • ket β :=
    embedUnitary_phaseDiagAct_mulVec_ket rComb phMid
  let syndOf : BitAssignment n → (Fin 8 → Bool) :=
    fun β i ↦ decide ((ts i).outBit β = 1)
  have hBody_ket : ∀ β : BitAssignment n,
      (∀ r : Fin 8, β (qs r) = 0) → (∀ j : Fin 34, β (scr34 j) = 0) →
      (U_in * cLoad8.eval).1.mulVec (ket β) =
        ((-1 : ℂ) ^ (phMid (fun idx ↦ β (rComb idx))).val) •
          ket (writeSynd 8 qs (syndOf β) β) := by
    intro β hqs0 hscr0
    let β₁ := writeSynd 8 qs (syndOf β) β
    have h1 : cLoad8.eval.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (∑ i : Fin 8, (ts i).extraPhase β).val) • ket β₁ :=
      ket_cLoadSeq 8 ts hts_seq_disj β hqs0
    have hβ₁_scr : ∀ j : Fin 34, β₁ (scr34 j) = 0 := by
      intro j
      dsimp only [β₁]
      rw [writeSynd_apply_of_not_mem 8 qs (syndOf β) β (scr34 j) (fun r ↦ (hqs_scr_disj r j).symm)]
      exact hscr0 j
    let γ : BitAssignment 185 := fun idx ↦ β (rComb idx)
    let γ₁ : BitAssignment 185 := fun idx ↦ β₁ (rComb idx)
    have hγ₁_eq : γ₁ = writeMux8_185 γ :=
      writeSynd_rComb_eq_writeMux8 rComb 8 (fun i ↦ (mux3Tuple185 i).a) (syndOf β) β
    have hγ₁_clean : InPlaceFullAddSlice.cleanRem 185 (185 - 151) γ₁ := by
      intro w hw
      have hw_eq : rComb w = scr34 ⟨w.val - 151, by omega⟩ := by
        dsimp only [scr34, InPlaceFullAddSlice.tailScr]
        exact congrArg rComb.wires (Fin.ext (by dsimp; omega))
      change β₁ (rComb w) = 0
      rw [hw_eq]
      exact hβ₁_scr _
    have hw₁ : InPlaceFullAddSlice.writeRegProg β₁ rComb ((pInner.toTempCtx.plug .nil).evalBits γ₁)
      = β₁ := by
      rw [hBitsIn γ₁ hγ₁_clean]
      funext w
      by_cases hmem : w ∈ Set.range rComb.wires
      · obtain ⟨idx, rfl⟩ := hmem; rw [InPlaceFullAddSlice.writeRegProg_apply_reg]
      · exact InPlaceFullAddSlice.writeRegProg_apply_of_not_mem _ _ _ _ hmem
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul,
      hKetIn β₁, pInner.toTempCtx_fwdBits]
    change _ = ((-1 : ℂ) ^ (phMid γ).val) • ket β₁
    change ((-1 : ℂ) ^ (∑ i : Fin 8, (ts i).extraPhase β).val) •
        (((-1 : ℂ) ^ (pInner.eval γ₁ wPhi * pInner.eval γ₁ wCoin).val) •
          ket
            (InPlaceFullAddSlice.writeRegProg β₁ rComb ((pInner.toTempCtx.plug .nil).evalBits γ₁)))
            = _
    rw [hw₁, hγ₁_eq, smul_smul, InPlaceFullAddSlice.TempPhaseProg.neg_one_pow_zmod2_mul]
    rfl
  have hPhase_ket : ∀ (g : Fin 8 → Bool) (β : BitAssignment n),
      (∀ r : Fin 8, β (qs r) = 0) → (∀ j : Fin 34, β (scr34 j) = 0) →
      (cFixSeq 8 ts g).eval.1.mulVec (ket β) =
        syndSign 8 qs g (writeSynd 8 qs (syndOf β) β) • ket β := by
    intro g β _ _
    rw [ket_cFixSeq, syndSign_writeSynd_eq 8 qs hqs_inj g (syndOf β) β]
  have hStream : RealizesCleanUnitary v (projZeroAll 8 qs * P_scr34) inner143 U_mid :=
    MeasureBranchHadamardSem.RealizesCleanUnitary.streamingSyndromeUncompute
      v 8 34 qs hqs_inj scr34 hqs_scr_disj
      cBody (U_in * cLoad8.eval) U_mid
      (fun g => .circuit (cFixSeq 8 ts g)) (fun g => (cFixSeq 8 ts g).eval)
      syndOf (fun β => (-1 : ℂ) ^ (phMid (fun idx ↦ β (rComb idx))).val)
      hBody (fun g => RealizesCleanUnitary.circuit v P_scr34 (cFixSeq 8 ts g))
      hBody_ket hPhase_ket (fun β _ _ => hUmid_ket β)
  have hProj42 : projZeroAll 8 qs * P_scr34 =
    projZeroAll 42 (InPlaceFullAddSlice.tailScr rComb 42 (by decide)) := by
    apply matrix_ext_ket; intro β
    have hiff : ((∀ r : Fin 8, β (qs r) = 0) ∧ (∀ j : Fin 34, β (scr34 j) = 0)) ↔
        (∀ k : Fin 42, β (InPlaceFullAddSlice.tailScr rComb 42 (by decide) k) = 0) := by
      constructor
      · rintro ⟨hq, hs⟩ k
        by_cases hk : k.val < 8
        · have heq : InPlaceFullAddSlice.tailScr rComb 42 (by decide) k = qs ⟨k.val, hk⟩ := rfl
          rw [heq]; exact hq _
        · have heq : InPlaceFullAddSlice.tailScr rComb 42 (by decide) k = scr34 ⟨k.val - 8,
            by omega⟩ := by
            dsimp only [InPlaceFullAddSlice.tailScr, scr34]
            exact congrArg rComb.wires (Fin.ext (by dsimp; omega))
          rw [heq]; exact hs _
      · intro hk
        refine ⟨fun r ↦ ?_, fun j ↦ ?_⟩
        · have heq : qs r = InPlaceFullAddSlice.tailScr rComb 42 (by decide) ⟨r.val, by omega⟩ :=
            rfl
          rw [heq]; exact hk _
        · have heq : scr34 j = InPlaceFullAddSlice.tailScr rComb 42 (by decide) ⟨8 + j.val,
            by omega⟩ := by
            dsimp only [InPlaceFullAddSlice.tailScr, scr34]
            exact congrArg rComb.wires (Fin.ext (by dsimp; omega))
          rw [heq]; exact hk _
    by_cases h42 : ∀ k : Fin 42, β (InPlaceFullAddSlice.tailScr rComb 42 (by decide) k) = 0
    · obtain ⟨hq, hs⟩ := hiff.mpr h42
      simp only [P_scr34, InPlaceFullAddSlice.mul_mulVec_prog, ket_projZeroAll, hq, hs, h42,
        imp_true_iff, ↓reduceIte]
    · by_cases hs : ∀ j : Fin 34, β (scr34 j) = 0
      · have hnq : ¬∀ r : Fin 8, β (qs r) = 0 := fun hq ↦ h42 (hiff.mp ⟨hq, hs⟩)
        simp only [P_scr34, InPlaceFullAddSlice.mul_mulVec_prog, ket_projZeroAll, hs, hnq, h42,
          imp_true_iff, ↓reduceIte]
      · simp only [P_scr34, InPlaceFullAddSlice.mul_mulVec_prog, ket_projZeroAll, hs, h42,
          ↓reduceIte, Matrix.mulVec_zero]
  have hInner143 : RealizesCleanUnitary v
    (projZeroAll 42 (InPlaceFullAddSlice.tailScr rComb 42 (by decide)))
      inner143 U_mid := by
    rwa [← hProj42]
  obtain ⟨hBitsOut, hValOut⟩ :=
    toTempCtx_valid_and_bits_probe probe143 pOuter.raw pOuter.wf (by decide : 143 ≤ 185)
      probe143_valid42 (fun β _ ↦ probe143_evalBits β)
  have hValOut75 : InPlaceFullAddSlice.ValidCleanRem 185 75 (pOuter.toTempCtx.plug probe143) := by
    simpa [SsaProg.toTempCtx] using hValOut
  obtain ⟨U_dyn, hSmall, hKetDyn⟩ :=
    realizes_toDynWithDyn_of_valid v rComb 42 (by decide) probe143
      (fun _ hv ↦ probe143_rem_ge hv) probe143_evalBits
      inner143 U_mid hInner143 phMid hUmid_ket
      pOuter.toTempCtx 75 (by decide) hValOut75
  let P_small := projZeroAll 75 (InPlaceFullAddSlice.tailScr rComb 75 (by decide))
  let P_work := projZeroAll mWork rWork.wires
  have hPs : P_smallᴴ = P_small := projZeroAll_conjTranspose 75 _
  have hPw : P_workᴴ = P_work := projZeroAll_conjTranspose mWork _
  have htail_work : ∀ j : Fin 75,
      InPlaceFullAddSlice.tailScr rComb 75 (by decide) j = rWork ⟨j.val, by omega⟩ := by
    intro j
    dsimp [InPlaceFullAddSlice.tailScr, rComb, rSub]
    have hidx : (⟨(185 - 75) + j.val, by omega⟩ : Fin 185) = Fin.natAdd 110 j := by
      ext; dsimp
    rw [hidx, QRegister.concat_apply_right, QRegister.slice_apply]
    congr 1; ext; dsimp; omega
  have hsub : P_small * P_work = P_work := by
    apply matrix_ext_ket; intro β
    simp only [P_small, P_work, InPlaceFullAddSlice.mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · have hs : ∀ j : Fin 75, β (InPlaceFullAddSlice.tailScr rComb 75 (by decide) j) = 0 := by
        intro j; rw [htail_work j]; exact hw ⟨j.val, by omega⟩
      simp [hw, hs, ket_projZeroAll]
    · simp [hw]
  have hMono := RealizesCleanUnitary.mono_proj hPs hPw hsub hSmall
  have hUeq : U_dyn.1 * P_work = (rAct.embedUnitary (phaseDiagAct pred)).1 * P_work := by
    apply matrix_ext_ket; intro β
    simp only [P_work, InPlaceFullAddSlice.mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · simp only [hw, imp_true_iff, ↓reduceIte, hKetDyn]
      let α : BitAssignment 110 := fun i ↦ β (rAct i)
      let padα : BitAssignment 185 := padZeroBits (mClean := 75) α
      have hpad : (fun idx ↦ β (rComb idx)) = padα := by
        funext idx
        refine Fin.addCases (m := 110) (n := 75) (fun i ↦ ?_) (fun j ↦ ?_) idx
        · dsimp only [rComb, padα, padZeroBits, α]
          rw [QRegister.concat_apply_left, Fin.addCases_left]
        · dsimp only [rComb, rSub, padα, padZeroBits]
          rw [QRegister.concat_apply_right, QRegister.slice_apply, Fin.addCases_right]
          exact hw _
      have hcleanPad : InPlaceFullAddSlice.cleanRem 185 (185 - 110) padα := by
        intro w
        refine Fin.addCases (m := 110) (n := 75) (fun i hw_ge ↦ ?_)
          (fun _ _ ↦ by simp [padα, padZeroBits]) w
        exfalso
        simp only [Fin.val_castAdd] at hw_ge
        omega
      have hextra_zero : ∑ i : Fin 8, (mux3Tuple185 i).extraPhase (pOuter.eval padα) = 0 := by
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        let γ₀ := pOuter.eval padα
        calc (mux3Tuple185 i).extraPhase γ₀
            = ((γ₀ (mux3Tuple185 i).q1 + γ₀ (mux3Tuple185 i).q0) *
                (γ₀ (mux3Tuple185 i).q2 + γ₀ (mux3Tuple185 i).q0)) *
                (γ₀ ⟨140, by decide⟩ * γ₀ ⟨141, by decide⟩) := by
                dsimp [Mux3Tuple.extraPhase, mux3Tuple185]; ring
          _ = 0 := by rw [hOrth α, mul_zero]
      have hph_eq : phMid (pOuter.eval padα) = pred α := by
        dsimp only [phMid]
        rw [hextra_zero, zero_add, hKick α]
      rw [hpad, pOuter.toTempCtx_fwdBits, hph_eq]
      change _ • ket
        (InPlaceFullAddSlice.writeRegProg β rComb
        ((pOuter.raw.toTempCtx.plug probe143).evalBits padα)) = _
      rw [hBitsOut padα hcleanPad]
      have hwComb : InPlaceFullAddSlice.writeRegProg β rComb padα = β := by
        funext w
        by_cases hmem : w ∈ Set.range rComb.wires
        · obtain ⟨idx, rfl⟩ := hmem
          rw [InPlaceFullAddSlice.writeRegProg_apply_reg]
          refine Fin.addCases (m := 110) (n := 75) (fun i ↦ ?_) (fun j ↦ ?_) idx
          · dsimp only [rComb, padα, padZeroBits, α]
            rw [Fin.addCases_left, QRegister.concat_apply_left]
          · dsimp only [rComb, rSub, padα, padZeroBits]
            rw [Fin.addCases_right, QRegister.concat_apply_right, QRegister.slice_apply]
            exact (hw _).symm
        · exact InPlaceFullAddSlice.writeRegProg_apply_of_not_mem _ _ _ _ hmem
      rw [hwComb, embedUnitary_phaseDiagAct_mulVec_ket rAct pred β]
    · simp [hw]
  have hTarget := RealizesCleanUnitary.congr_unitary hPw hMono hUeq
  let dyn := compileAnchoredMux3PwuDyn v rAct rWork hdisj hw_len pOuter pInner wPhi wCoin hne
  have hSC_inner143 : PreservesStoreConst inner143 :=
    PreservesStoreConst.seq
      (PreservesStoreConst.seq (PreservesStoreConst.circuit cLoad8)
        (toDynWithDyn_preservesStoreConst v rComb (.circuit cz)
          (PreservesStoreConst.circuit cz) pInner.toTempCtx))
      (PreservesStoreConst.seq (PreservesStoreConst.circuit (hadamardAll 8 qs))
        (preservesStoreConst_measureAndBranchSeq v 8 _ _
          (fun g => PreservesStoreConst.seq
            (PreservesStoreConst.circuit (xReset 8 qs g))
            (PreservesStoreConst.circuit (cFixSeq 8 ts g)))))
  have hSC : PreservesStoreConst dyn :=
    toDynWithDyn_preservesStoreConst v rComb inner143 hSC_inner143 pOuter.toTempCtx
  intro M_obs
  obtain ⟨M_out, hM_out⟩ := hSC M_obs
  refine ⟨M_out, hM_out, ?_⟩
  have hconj := hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
  have hM_eq : wp dyn.compile (fun _ ↦ M_obs) default = M_out := by
    rw [hM_out]
  rw [← hM_eq, ← projZeroAll_eq_basisOutcomeProjector_zero rWork]
  have hdyn_eq : dyn = toDynWithDyn v rComb inner143 pOuter.toTempCtx := rfl
  rw [hdyn_eq]
  simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
    congrArg Subtype.val hconj

end Dir3TwistSlot1Junction.Mux3AnchoredPwu

namespace Dir3TwistSlot1Junction.MomSlot1WalkerAliasPWU24
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm PosMomSelectSandwich
open PosMomSelectDynamic SingleRBEGridGuardWalk
open SixSlotEndpointJunctionBridge
open FullSysPrepare6Slot
open FullSysPosSlots24AndTopConcrete
open TwosCompAndWire0Cancel
open LiteralKineticAndMidpoint128
open MomSlots01Slot1ProjKinetic
open MomSlot1GeomPriority288
open MomSlot1Dyadic459Sub36w
open Dir3TwistSlot1Junction

open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelRaw sixChannelShifted)
open InPlaceFullAddSlice (bit_cases)
open scoped Matrix BigOperators Matrix.Norms.L2Operator

section ConfigMomSlot1WalkerAliasPWU24

noncomputable def lockValWalker {α : Sort _} (x : α) : α :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : α, y = x)

private theorem lockValWalker_eq {α : Sort _} (x : α) : lockValWalker x = x :=
  Classical.choose_spec (⟨x, rfl⟩ : ∃ y : α, y = x)


abbrev pwuWorkWires : ℕ := 75

def pwuHCol (bSub : ℕ) : ℕ := 2 ^ bSub

def pwuTq : ℕ → ℕ
  | 18 => 617
  | 19 => 1234
  | 20 => 2467
  | 21 => 4934
  | 22 => 9869
  | 23 => 19737
  | _ => 39474

def pwuQuadErr3Num : ℕ → ℕ
  | 18 => 128566
  | 19 => 128566
  | 20 => 19839
  | 21 => 19839
  | 22 => 17263
  | _ => 1289

def pwuCAlias (bSub : ℕ) : ℕ := pwuHCol bSub - pwuTq bSub

noncomputable def pwuC7 : ℝ := ((2 ^ 7 - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 7
noncomputable def pwuC14 : ℝ := ((2 ^ 14 - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 14
noncomputable def pwuC21 : ℝ := ((2 ^ 21 - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 21

private theorem pwuC7_pos : 0 < pwuC7 := by unfold pwuC7; norm_num
private theorem pwuC14_pos : 0 < pwuC14 := by unfold pwuC14; norm_num
private theorem pwuC21_pos : 0 < pwuC21 := by unfold pwuC21; norm_num

noncomputable def pwuEShift (cfg : Configuration) : ℝ :=
  projMidpointOffset cfg + 3 * slot1QuadBranchWeight * (1 / (pwuC7 * pwuC14) - 1)

private theorem pwuTq_lt_hcol {bSub : ℕ} (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) :
    pwuTq bSub < pwuHCol bSub := by
  rcases (by omega : bSub = 18 ∨ bSub = 19 ∨ bSub = 20 ∨ bSub = 21 ∨ bSub = 22 ∨ bSub = 23 ∨ bSub =
    24) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [pwuTq, pwuHCol]

private theorem sum_natAbs_projectileMomentum_le_108715 (c : Configuration) :
    (c.projectileMomentum 0).natAbs + (c.projectileMomentum 1).natAbs +
      (c.projectileMomentum 2).natAbs ≤ 108715 := by
  have hm : waveNumberSq c.projectileMomentum ≤ 29376 ^ 2 := c.momentum_le
  dsimp [waveNumberSq, dotProduct] at hm
  rw [Fin.sum_univ_three] at hm
  have hwv (w : Fin 3) : waveVector c.projectileMomentum w =
      gridKappa * (c.projectileMomentum w : ℝ) := by
    unfold waveVector gridKappa; ring
  rw [hwv 0, hwv 1, hwv 2] at hm
  have hsq_int (z : ℤ) : (z : ℝ) ^ 2 = (z.natAbs : ℝ) ^ 2 := by
    cases z with
    | ofNat n => simp
    | negSucc n => simp only [Int.cast_negSucc, Int.natAbs_negSucc]; push_cast; ring
  have hk_lo : gridKappaRatLo ≤ gridKappa := gridKappa_ge_ratLo
  have hk_lo_pos : (0 : ℝ) < gridKappaRatLo := by unfold gridKappaRatLo; positivity
  have hksq : gridKappaRatLo ^ 2 ≤ gridKappa ^ 2 := sq_le_sq' (by linarith) hk_lo
  set n0 : ℕ := (c.projectileMomentum 0).natAbs
  set n1 : ℕ := (c.projectileMomentum 1).natAbs
  set n2 : ℕ := (c.projectileMomentum 2).natAbs
  have hsum_sq_ge :
      gridKappaRatLo ^ 2 * ((n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) ≤ 29376 ^ 2 := by
    have hnn : 0 ≤ (n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2 := by positivity
    have h1 : gridKappaRatLo ^ 2 * ((n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) ≤
        gridKappa ^ 2 * ((n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hksq hnn
    have h2 : gridKappa ^ 2 * ((n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) =
        (gridKappa * (c.projectileMomentum 0 : ℝ)) * (gridKappa * (c.projectileMomentum 0 : ℝ)) +
        (gridKappa * (c.projectileMomentum 1 : ℝ)) * (gridKappa * (c.projectileMomentum 1 : ℝ)) +
        (gridKappa * (c.projectileMomentum 2 : ℝ)) * (gridKappa * (c.projectileMomentum 2 : ℝ)) :=
          by
      have e0 := hsq_int (c.projectileMomentum 0)
      have e1 := hsq_int (c.projectileMomentum 1)
      have e2 := hsq_int (c.projectileMomentum 2)
      dsimp only [n0, n1, n2]
      linear_combination gridKappa ^ 2 * e0.symm + gridKappa ^ 2 * e1.symm + gridKappa ^ 2 * e2.symm
    linarith
  have hcs : ((n0 + n1 + n2 : ℕ) : ℝ) ^ 2 ≤ 3 * ((n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg ((n0 : ℝ) - n1), sq_nonneg ((n1 : ℝ) - n2), sq_nonneg ((n2 : ℝ) - n0)]
  have hlt_sq : gridKappaRatLo ^ 2 * ((n0 + n1 + n2 : ℕ) : ℝ) ^ 2 <
      gridKappaRatLo ^ 2 * (108716 : ℝ) ^ 2 := by
    have hmul : gridKappaRatLo ^ 2 * ((n0 + n1 + n2 : ℕ) : ℝ) ^ 2 ≤
        3 * (gridKappaRatLo ^ 2 * ((n0 : ℝ) ^ 2 + (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2)) := by
      have hk2_pos : 0 < gridKappaRatLo ^ 2 := sq_pos_of_pos hk_lo_pos
      nlinarith
    have hstrict : (3 : ℝ) * (29376 ^ 2 : ℝ) < gridKappaRatLo ^ 2 * (108716 : ℝ) ^ 2 := by
      unfold gridKappaRatLo; norm_num
    linarith
  have hsq_lt : ((n0 + n1 + n2 : ℕ) : ℝ) ^ 2 < (108716 : ℝ) ^ 2 :=
    lt_of_mul_lt_mul_left hlt_sq (sq_pos_of_pos hk_lo_pos).le
  have hreal_lt : ((n0 + n1 + n2 : ℕ) : ℝ) < (108716 : ℝ) := by
    have hnn : (0 : ℝ) ≤ ((n0 + n1 + n2 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hnat_lt : n0 + n1 + n2 < 108716 := by exact_mod_cast hreal_lt
  omega

private theorem sum_abs_stepVector_projectileMomentum_le_108715 (c : Configuration) :
    (∑ w : Fin 3, |waveVector c.projectileMomentum w|) ≤ gridKappaRatHi * 108715 := by
  have habs_int (z : ℤ) : |(z : ℝ)| = (z.natAbs : ℝ) := by
    cases z with
    | ofNat n => simp
    | negSucc n =>
        simp only [Int.cast_negSucc, Int.natAbs_negSucc]
        rw [abs_of_neg (by push_cast; linarith)]
        push_cast; ring
  have hwv (w : Fin 3) : |waveVector c.projectileMomentum w| =
      gridKappa * ((c.projectileMomentum w).natAbs : ℝ) := by
    have heq : waveVector c.projectileMomentum w = gridKappa * (c.projectileMomentum w : ℝ) := by
      unfold waveVector gridKappa; ring
    rw [heq, abs_mul, abs_of_nonneg gridKappa_nonneg, habs_int]
  rw [Fin.sum_univ_three, hwv 0, hwv 1, hwv 2, ← mul_add, ← mul_add]
  have hnat : (((c.projectileMomentum 0).natAbs + (c.projectileMomentum 1).natAbs +
      (c.projectileMomentum 2).natAbs : ℕ) : ℝ) ≤ 108715 := by
    exact_mod_cast sum_natAbs_projectileMomentum_le_108715 c
  push_cast at hnat
  have hk_le : gridKappa ≤ gridKappaRatHi := gridKappa_le_ratHi
  have hnn : (0 : ℝ) ≤ ((c.projectileMomentum 0).natAbs : ℝ) +
      ((c.projectileMomentum 1).natAbs : ℝ) + ((c.projectileMomentum 2).natAbs : ℝ) := by positivity
  exact mul_le_mul hk_le hnat hnn (by unfold gridKappaRatHi; positivity)

noncomputable def pwuXLin (bSub : ℕ) (cfg : Configuration) (w : Fin 3) : ℝ :=
  (2 : ℝ) ^ (bSub + 3) * ((slot1LinBranchWeight cfg w / pwuC21) / lambdaSlot1TpHi)

private theorem pwuXLin_nonneg (bSub : ℕ) (cfg : Configuration) (w : Fin 3) :
    0 ≤ pwuXLin bSub cfg w := by
  unfold pwuXLin
  have hm : (0 : ℝ) < projectileMass := by unfold projectileMass; norm_num
  have hlam : (0 : ℝ) < lambdaSlot1TpHi := by unfold lambdaSlot1TpHi; norm_num
  have hc21 : (0 : ℝ) < pwuC21 := pwuC21_pos
  have hw : 0 ≤ slot1LinBranchWeight cfg w := by
    unfold slot1LinBranchWeight
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) gridKappa_nonneg) (abs_nonneg _)) hm.le
  positivity

noncomputable def pwuDl (bSub : ℕ) (cfg : Configuration) (w : Fin 3) : ℕ :=
  ⌊pwuXLin bSub cfg w + 1 / 2⌋₊

private theorem pwu_used_lt_two_pow {bSub : ℕ} (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) :
    3 * pwuTq bSub + pwuDl bSub cfg 0 + pwuDl bSub cfg 1 + pwuDl bSub cfg 2 <
      2 ^ (bSub + 3) := by
  have hd0 : (pwuDl bSub cfg 0 : ℝ) ≤ pwuXLin bSub cfg 0 + 1 / 2 :=
    Nat.floor_le (by linarith [pwuXLin_nonneg bSub cfg 0])
  have hd1 : (pwuDl bSub cfg 1 : ℝ) ≤ pwuXLin bSub cfg 1 + 1 / 2 :=
    Nat.floor_le (by linarith [pwuXLin_nonneg bSub cfg 1])
  have hd2 : (pwuDl bSub cfg 2 : ℝ) ≤ pwuXLin bSub cfg 2 + 1 / 2 :=
    Nat.floor_le (by linarith [pwuXLin_nonneg bSub cfg 2])
  have hk_le : gridKappa ≤ gridKappaRatHi := gridKappa_le_ratHi
  have hsum_k : (∑ w : Fin 3, |waveVector cfg.projectileMomentum w|) ≤ gridKappaRatHi * 108715 :=
    sum_abs_stepVector_projectileMomentum_le_108715 cfg
  have hsum_knn : 0 ≤ ∑ w : Fin 3, |waveVector cfg.projectileMomentum w| :=
    Finset.sum_nonneg fun w _ ↦ abs_nonneg _
  have hw_sum : slot1LinBranchWeight cfg 0 + slot1LinBranchWeight cfg 1 +
      slot1LinBranchWeight cfg 2 ≤
      (127 * gridKappaRatHi * (gridKappaRatHi * 108715)) / projectileMass := by
    unfold slot1LinBranchWeight
    have hmul : gridKappa * (∑ w : Fin 3, |waveVector cfg.projectileMomentum w|) ≤
        gridKappaRatHi * (gridKappaRatHi * 108715) :=
      mul_le_mul hk_le hsum_k hsum_knn (by unfold gridKappaRatHi; positivity)
    rw [Fin.sum_univ_three] at hmul
    have hnum : 127 * gridKappa * |waveVector cfg.projectileMomentum 0| +
        127 * gridKappa * |waveVector cfg.projectileMomentum 1| +
        127 * gridKappa * |waveVector cfg.projectileMomentum 2| ≤
        127 * gridKappaRatHi * (gridKappaRatHi * 108715) := by linarith
    calc (127 * gridKappa * |waveVector cfg.projectileMomentum 0|) / projectileMass +
          (127 * gridKappa * |waveVector cfg.projectileMomentum 1|) / projectileMass +
          (127 * gridKappa * |waveVector cfg.projectileMomentum 2|) / projectileMass
        = (127 * gridKappa * |waveVector cfg.projectileMomentum 0| +
            127 * gridKappa * |waveVector cfg.projectileMomentum 1| +
            127 * gridKappa * |waveVector cfg.projectileMomentum 2|) / projectileMass := by ring
      _ ≤ (127 * gridKappaRatHi * (gridKappaRatHi * 108715)) / projectileMass :=
          div_le_div_of_nonneg_right hnum (by unfold projectileMass; positivity)
  have hx_sum : pwuXLin bSub cfg 0 + pwuXLin bSub cfg 1 + pwuXLin bSub cfg 2 ≤
      (2 : ℝ) ^ (bSub + 3) *
        ((((127 * gridKappaRatHi * (gridKappaRatHi * 108715)) / projectileMass) / pwuC21) /
          lambdaSlot1TpHi) := by
    have hsum_eq : pwuXLin bSub cfg 0 + pwuXLin bSub cfg 1 + pwuXLin bSub cfg 2 =
        (2 : ℝ) ^ (bSub + 3) *
          (((slot1LinBranchWeight cfg 0 + slot1LinBranchWeight cfg 1 +
            slot1LinBranchWeight cfg 2) / pwuC21) / lambdaSlot1TpHi) := by
      unfold pwuXLin; ring
    rw [hsum_eq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hw_sum pwuC21_pos.le)
      (by unfold lambdaSlot1TpHi; positivity)
  have hreal_lt :
      ((3 * pwuTq bSub + pwuDl bSub cfg 0 + pwuDl bSub cfg 1 + pwuDl bSub cfg 2 : ℕ) : ℝ) <
        ((2 ^ (bSub + 3) : ℕ) : ℝ) := by
    push_cast
    have hcap : 3 * (pwuTq bSub : ℝ) +
        (2 : ℝ) ^ (bSub + 3) *
          ((((127 * gridKappaRatHi * (gridKappaRatHi * 108715)) / projectileMass) / pwuC21) /
            lambdaSlot1TpHi) + 3 / 2 < (2 : ℝ) ^ (bSub + 3) := by
      rcases (by omega : bSub = 18 ∨ bSub = 19 ∨ bSub = 20 ∨ bSub = 21 ∨ bSub = 22 ∨ bSub = 23 ∨
        bSub = 24) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (unfold pwuTq gridKappaRatHi projectileMass lambdaSlot1TpHi pwuC21; norm_num)
    linarith
  exact_mod_cast hreal_lt



def vec4 {α : Type*} (x0 x1 x2 x3 : α) (i : Fin 4) : α :=
  match i.val with
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | _ => x3

@[simp] theorem vec4_0 {α : Type*} (x0 x1 x2 x3 : α) : vec4 x0 x1 x2 x3 0 = x0 := rfl
@[simp] theorem vec4_1 {α : Type*} (x0 x1 x2 x3 : α) : vec4 x0 x1 x2 x3 1 = x1 := rfl
@[simp] theorem vec4_2 {α : Type*} (x0 x1 x2 x3 : α) : vec4 x0 x1 x2 x3 2 = x2 := rfl
@[simp] theorem vec4_3 {α : Type*} (x0 x1 x2 x3 : α) : vec4 x0 x1 x2 x3 3 = x3 := rfl

def vec8 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) (c : Fin 8) : α :=
  match c.val with
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | 3 => x3
  | 4 => x4
  | 5 => x5
  | 6 => x6
  | _ => x7

@[simp] theorem vec8_0 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) : vec8 x0 x1 x2 x3 x4 x5 x6 x7 0 =
    x0 := rfl
@[simp] theorem vec8_1 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) : vec8 x0 x1 x2 x3 x4 x5 x6 x7 1 =
    x1 := rfl
@[simp] theorem vec8_2 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) : vec8 x0 x1 x2 x3 x4 x5 x6 x7 2 =
    x2 := rfl
@[simp] theorem vec8_3 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) : vec8 x0 x1 x2 x3 x4 x5 x6 x7 3 =
    x3 := rfl
@[simp] theorem vec8_4 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) : vec8 x0 x1 x2 x3 x4 x5 x6 x7 4 =
    x4 := rfl
@[simp] theorem vec8_5 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) : vec8 x0 x1 x2 x3 x4 x5 x6 x7 5 =
    x5 := rfl
@[simp] theorem vec8_6 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) : vec8 x0 x1 x2 x3 x4 x5 x6 x7 6 =
    x6 := rfl
@[simp] theorem vec8_7 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) : vec8 x0 x1 x2 x3 x4 x5 x6 x7 7 =
    x7 := rfl

def lf4 (b : Fin 4) : Fin 8 := ⟨4 + b.val, by omega⟩

private theorem pwu_hcol_calias_bounds {bSub : ℕ} (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) :
    2 ≤ pwuHCol bSub ∧ 0 < pwuCAlias bSub ∧ pwuCAlias bSub < pwuHCol bSub ∧
    pwuHCol bSub ≤ 5 * pwuCAlias bSub := by
  rcases (by omega : bSub = 18 ∨ bSub = 19 ∨ bSub = 20 ∨ bSub = 21 ∨ bSub = 22 ∨ bSub = 23 ∨ bSub =
    24) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [pwuHCol, pwuCAlias, pwuTq]

def IsPerm4 (i0 i1 i2 i3 : Fin 4) : Prop :=
  (((i0.val ^^^ i1.val) ^^^ i2.val) ^^^ i3.val) = 0 ∧
  (((i0.val ^^^ i1.val) ^^^ i3.val) ^^^ i2.val) = 0 ∧
  i0 ≠ i1 ∧ i0 ≠ i2 ∧ i0 ≠ i3 ∧ i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 ∧
  ∀ b : Fin 4, b = i0 ∨ b = i1 ∨ b = i2 ∨ b = i3

local instance instDecidableIsPerm4_Slot1Pwu24 (i0 i1 i2 i3 : Fin 4) : Decidable
    (IsPerm4 i0 i1 i2 i3) := by
  unfold IsPerm4
  infer_instance

def merge22 (w : Fin 4 → ℕ) (x0 x1 y0 y1 : Fin 4) : Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
  if w x0 ≤ w y0 then
    if w x1 ≤ w y0 then (x0, x1, y0, y1)
    else if w x1 ≤ w y1 then (x0, y0, x1, y1)
    else (x0, y0, y1, x1)
  else
    if w y1 ≤ w x0 then (y0, y1, x0, x1)
    else if w y1 ≤ w x1 then (y0, x0, y1, x1)
    else (y0, x0, x1, y1)

def sort4Idx (w : Fin 4 → ℕ) : Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
  if w 0 ≤ w 1 then
    if w 2 ≤ w 3 then merge22 w 0 1 2 3 else merge22 w 0 1 3 2
  else
    if w 2 ≤ w 3 then merge22 w 1 0 2 3 else merge22 w 1 0 3 2

private theorem sort4Idx_spec (w : Fin 4 → ℕ) :
    let (i0, i1, i2, i3) := sort4Idx w
    IsPerm4 i0 i1 i2 i3 ∧
    w i0 ≤ w i1 ∧ w i1 ≤ w i2 ∧ w i2 ≤ w i3 ∧
    w i0 + w i1 + w i2 + w i3 = w 0 + w 1 + w 2 + w 3 := by
  dsimp only [sort4Idx, merge22]
  split_ifs <;> (dsimp only; refine ⟨by decide, by omega, by omega, by omega, by omega⟩)

attribute [local irreducible] sort4Idx

private theorem ite_fin4_sum (a : Fin 4) (c : ℕ) :
    (if a = 0 then c else 0) + (if a = 1 then c else 0) +
    (if a = 2 then c else 0) + (if a = 3 then c else 0) = c := by
  fin_cases a <;> simp

private theorem xor_xxyy (x y : Fin 4) : (((x.val ^^^ x.val) ^^^ y.val) ^^^ y.val) = 0 := by
  fin_cases x <;> fin_cases y <;> decide

private theorem xor_xyyx (x y : Fin 4) : (((x.val ^^^ y.val) ^^^ y.val) ^^^ x.val) = 0 := by
  fin_cases x <;> fin_cases y <;> decide

private theorem exists_peel_w0_to_w3 {H CA : ℕ}
    (_hCA0 : 0 < CA) (hCAH : CA < H) (hH5 : H ≤ 5 * CA)
    (w0 : Fin 4 → ℕ) (hw0 : w0 0 + w0 1 + w0 2 + w0 3 = 5 * H + 3 * CA) :
    ∃ (a0 a1 a2 : Fin 4) (w3 : Fin 4 → ℕ),
      w3 0 + w3 1 + w3 2 + w3 3 = 5 * H ∧
      (∃ imin : Fin 4, w3 imin ≤ H) ∧
      ∀ b : Fin 4,
        (if a0 = b then CA else 0) + (if a1 = b then CA else 0) +
        (if a2 = b then CA else 0) + w3 b = w0 b := by
  have hs := sort4Idx_spec w0
  rcases hsort : sort4Idx w0 with ⟨i0, i1, i2, i3⟩
  rw [hsort] at hs
  obtain ⟨⟨_, _, h01, h02, h03, h12, h13, h23, hexh⟩, hz01, hz12, hz23, hzsum⟩ := hs
  rw [hw0] at hzsum
  have hmk : ∀ (a0 a1 a2 : Fin 4) (w3 : Fin 4 → ℕ),
      w3 i0 ≤ H →
      (∀ b : Fin 4,
        (if a0 = b then CA else 0) + (if a1 = b then CA else 0) +
        (if a2 = b then CA else 0) + w3 b = w0 b) →
      ∃ (a0' a1' a2' : Fin 4) (w3' : Fin 4 → ℕ),
        w3' 0 + w3' 1 + w3' 2 + w3' 3 = 5 * H ∧
        (∃ imin : Fin 4, w3' imin ≤ H) ∧
        ∀ b : Fin 4,
          (if a0' = b then CA else 0) + (if a1' = b then CA else 0) +
          (if a2' = b then CA else 0) + w3' b = w0 b := by
    intro a0 a1 a2 w3 hmin hrest
    refine ⟨a0, a1, a2, w3, ?_, ⟨i0, hmin⟩, hrest⟩
    have r0 := hrest 0; have r1 := hrest 1; have r2 := hrest 2; have r3 := hrest 3
    have s0 := ite_fin4_sum a0 CA; have s1 := ite_fin4_sum a1 CA; have s2 := ite_fin4_sum a2 CA
    omega
  by_cases hz0H : w0 i0 ≤ H
  · by_cases hz3 : 3 * CA ≤ w0 i3
    · refine hmk i3 i3 i3 (fun b ↦ if b = i3 then w0 b - 3 * CA else w0 b)
        (by simp [h03, hz0H]) (fun b ↦ ?_)
      rcases hexh b with rfl | rfl | rfl | rfl <;>
        (simp only [↓reduceIte, h03, h03.symm, h13, h13.symm, h23, h23.symm]; omega)
    · refine hmk i1 i2 i3 (fun b ↦ if b = i0 then w0 b else w0 b - CA)
        (by simp [hz0H]) (fun b ↦ ?_)
      rcases hexh b with rfl | rfl | rfl | rfl <;>
        (simp only [↓reduceIte, h01.symm, h02.symm, h03.symm, h12, h12.symm, h13, h13.symm, h23,
          h23.symm]; omega)
  · by_cases hz0HC : w0 i0 ≤ H + CA
    · refine hmk i0 i1 i2 (fun b ↦ if b = i3 then w0 b else w0 b - CA)
        (by simp only [h03, ↓reduceIte]; omega) (fun b ↦ ?_)
      rcases hexh b with rfl | rfl | rfl | rfl <;>
        (simp only [↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h12, h12.symm, h13, h23]; omega)
    · refine hmk i0 i0 i1
        (fun b ↦ if b = i0 then w0 b - 2 * CA else if b = i1 then w0 b - CA else w0 b)
        (by simp only [↓reduceIte]; omega) (fun b ↦ ?_)
      rcases hexh b with rfl | rfl | rfl | rfl <;>
        (simp only [↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm, h12, h12.symm, h13,
          h13.symm]; omega)

private theorem exists_pack_w3_even {H : ℕ} (hH2 : 2 ≤ H)
    (w3 : Fin 4 → ℕ) (hw3 : w3 0 + w3 1 + w3 2 + w3 3 = 5 * H)
    (hmin : ∃ imin : Fin 4, w3 imin ≤ H) :
    ∃ (a3 p4 a4 p5 a5 p6 a6 p7 : Fin 4) (t4 t5 t6 : ℕ),
      t4 < H ∧ t5 < H ∧ t6 < H ∧
      (((p4.val ^^^ p5.val) ^^^ p6.val) ^^^ p7.val) = 0 ∧
      (((a4.val ^^^ a5.val) ^^^ a6.val) ^^^ p7.val) = 0 ∧
      ∀ b : Fin 4,
        (if a3 = b then H else 0) +
        ((if p4 = b then t4 else 0) + (if a4 = b then H - t4 else 0)) +
        ((if p5 = b then t5 else 0) + (if a5 = b then H - t5 else 0)) +
        ((if p6 = b then t6 else 0) + (if a6 = b then H - t6 else 0)) +
        (if p7 = b then H else 0) = w3 b := by
  have hs := sort4Idx_spec w3
  rcases hsort : sort4Idx w3 with ⟨i0, i1, i2, i3⟩
  rw [hsort] at hs
  obtain ⟨⟨hxp0123, hxp0132, h01, h02, h03, h12, h13, h23, hexh⟩, hy01, hy12, hy23, hysum⟩ := hs
  rw [hw3] at hysum
  have hy0H : w3 i0 ≤ H := by
    obtain ⟨imin, himin⟩ := hmin
    rcases hexh imin with rfl | rfl | rfl | rfl <;> omega
  let rowSum (a3 p4 a4 p5 a5 p6 a6 p7 b : Fin 4) (t4 t5 t6 : ℕ) : ℕ :=
    (if a3 = b then H else 0) + ((if p4 = b then t4 else 0) + (if a4 = b then H - t4 else 0)) +
    ((if p5 = b then t5 else 0) + (if a5 = b then H - t5 else 0)) +
    ((if p6 = b then t6 else 0) + (if a6 = b then H - t6 else 0)) + (if p7 = b then H else 0)
  have hmk : ∀ (a3 p4 a4 p5 a5 p6 a6 p7 : Fin 4) (t4 t5 t6 : ℕ),
      t4 < H → t5 < H → t6 < H →
      (((p4.val ^^^ p5.val) ^^^ p6.val) ^^^ p7.val) = 0 →
      (((a4.val ^^^ a5.val) ^^^ a6.val) ^^^ p7.val) = 0 →
      (rowSum a3 p4 a4 p5 a5 p6 a6 p7 i0 t4 t5 t6 = w3 i0 ∧
       rowSum a3 p4 a4 p5 a5 p6 a6 p7 i1 t4 t5 t6 = w3 i1 ∧
       rowSum a3 p4 a4 p5 a5 p6 a6 p7 i2 t4 t5 t6 = w3 i2 ∧
       rowSum a3 p4 a4 p5 a5 p6 a6 p7 i3 t4 t5 t6 = w3 i3) →
      ∃ (a3' p4' a4' p5' a5' p6' a6' p7' : Fin 4) (t4' t5' t6' : ℕ),
        t4' < H ∧ t5' < H ∧ t6' < H ∧
        (((p4'.val ^^^ p5'.val) ^^^ p6'.val) ^^^ p7'.val) = 0 ∧
        (((a4'.val ^^^ a5'.val) ^^^ a6'.val) ^^^ p7'.val) = 0 ∧
        ∀ b : Fin 4, rowSum a3' p4' a4' p5' a5' p6' a6' p7' b t4' t5' t6' = w3 b := by
    intro a3 p4 a4 p5 a5 p6 a6 p7 t4 t5 t6 ht4 ht5 ht6 hxp hxa ⟨e0, e1, e2, e3⟩
    exact ⟨a3, p4, a4, p5, a5, p6, a6, p7, t4, t5, t6, ht4, ht5, ht6, hxp, hxa, fun b ↦ by
      rcases hexh b with rfl | rfl | rfl | rfl
      · exact e0
      · exact e1
      · exact e2
      · exact e3⟩
  by_cases hy2_lt : w3 i2 < H
  · refine hmk i3 i0 i3 i1 i3 i2 i3 i3 (w3 i0) (w3 i1) (w3 i2)
      (by omega) (by omega) (by omega) hxp0123 (xor_xxyy i3 i3) ?_
    simp only [rowSum, ↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm,
      h12, h12.symm, h13, h13.symm, h23, h23.symm]
    omega
  · by_cases hy1_lt : w3 i1 < H
    · by_cases hy2_2h : w3 i2 < 2 * H
      · refine hmk i2 i0 i3 i1 i3 i2 i3 i3 (w3 i0) (w3 i1) (w3 i2 - H)
          (by omega) (by omega) (by omega) hxp0123 (xor_xxyy i3 i3) ?_
        simp only [rowSum, ↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm,
          h12, h12.symm, h13, h13.symm, h23, h23.symm]
        omega
      · by_cases hy3_eq : w3 i3 = 2 * H
        · refine hmk i3 i2 i0 i2 i1 i3 i2 i3 (H - w3 i0) (H - w3 i1) 0
            (by omega) (by omega) (by omega) (xor_xxyy i2 i3) hxp0123 ?_
          simp only [rowSum, ↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm,
            h12, h12.symm, h13, h13.symm, h23, h23.symm]
          omega
        · refine hmk i3 i0 i2 i1 i2 i2 i3 i3 (w3 i0) (w3 i1) (3 * H - w3 i3)
            (by omega) (by omega) (by omega) hxp0123 (xor_xxyy i2 i3) ?_
          simp only [rowSum, ↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm,
            h12, h12.symm, h13, h13.symm, h23, h23.symm]
          omega
    · by_cases hy0_lt : w3 i0 < H
      · by_cases hy3_le : w3 i3 ≤ 2 * H
        · refine hmk i1 i0 i2 i1 i2 i2 i3 i3 (w3 i0) (w3 i1 - H) (2 * H - w3 i3)
            (by omega) (by omega) (by omega) hxp0123 (xor_xxyy i2 i3) ?_
          simp only [rowSum, ↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm,
            h12, h12.symm, h13, h13.symm, h23, h23.symm]
          omega
        · by_cases hy2_gt : H < w3 i2
          · refine hmk i1 i0 i3 i1 i3 i3 i2 i2 (w3 i0) (w3 i1 - H) (2 * H - w3 i2)
              (by omega) (by omega) (by omega) hxp0132 (xor_xxyy i3 i2) ?_
            simp only [rowSum, ↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm,
              h12, h12.symm, h13, h13.symm, h23, h23.symm]
            omega
          · by_cases hy0_pos : 0 < w3 i0
            · refine hmk i3 i3 i0 i0 i1 i0 i2 i3 (H - w3 i0) 0 0
                (by omega) (by omega) (by omega) (xor_xyyx i3 i0) hxp0123 ?_
              simp only [rowSum, ↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm,
                h12, h12.symm, h13, h13.symm, h23, h23.symm]
              omega
            · refine hmk i3 i3 i3 i1 i2 i1 i2 i3 0 1 (H - 1)
                (by omega) (by omega) (by omega) (xor_xyyx i3 i1) (xor_xyyx i3 i2) ?_
              simp only [rowSum, ↓reduceIte, h01.symm, h02.symm, h03.symm, h12, h12.symm, h13,
                h13.symm, h23, h23.symm]
              omega
      · by_cases hy2_eq : w3 i2 = H
        · refine hmk i3 i0 i0 i1 i1 i2 i2 i3 0 0 0
            (by omega) (by omega) (by omega) hxp0123 hxp0123 ?_
          simp only [rowSum, ↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm,
            h12, h12.symm, h13, h13.symm, h23, h23.symm]
          omega
        · refine hmk i0 i1 i2 i1 i3 i2 i3 i2 (2 * H - w3 i2) (2 * H - w3 i3) 0
            (by omega) (by omega) (by omega) (xor_xxyy i1 i2) (xor_xyyx i2 i3) ?_
          simp only [rowSum, ↓reduceIte, h01, h01.symm, h02, h02.symm, h03, h03.symm,
            h12, h12.symm, h13, h13.symm, h23, h23.symm]
          omega

private theorem exists_pwu_lin_bucket_mass_even {bSub : ℕ} (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (w0 : Fin 4 → ℕ)
    (hw0 : w0 0 + w0 1 + w0 2 + w0 3 = 5 * pwuHCol bSub + 3 * pwuCAlias bSub) :
    ∃ (a0 a1 a2 a3 p4 a4 p5 a5 p6 a6 p7 : Fin 4) (t4 t5 t6 : ℕ),
      t4 < pwuHCol bSub ∧ t5 < pwuHCol bSub ∧ t6 < pwuHCol bSub ∧
      ((t4 ^^^ t5) ^^^ t6) < pwuHCol bSub ∧
      (((p4.val ^^^ p5.val) ^^^ p6.val) ^^^ p7.val) = 0 ∧
      (((a4.val ^^^ a5.val) ^^^ a6.val) ^^^ p7.val) = 0 ∧
      ∀ b : Fin 4,
        (if a0 = b then pwuCAlias bSub else 0) +
        (if a1 = b then pwuCAlias bSub else 0) +
        (if a2 = b then pwuCAlias bSub else 0) +
        (if a3 = b then pwuHCol bSub else 0) +
        ((if p4 = b then t4 else 0) +
          (if a4 = b then pwuHCol bSub - t4 else 0)) +
        ((if p5 = b then t5 else 0) +
          (if a5 = b then pwuHCol bSub - t5 else 0)) +
        ((if p6 = b then t6 else 0) +
          (if a6 = b then pwuHCol bSub - t6 else 0)) +
        (if p7 = b then pwuHCol bSub else 0) = w0 b := by
  obtain ⟨hH2, hCA0, hCAH, hH5⟩ := pwu_hcol_calias_bounds hbLo hbHi
  obtain ⟨a0, a1, a2, w3, hw3, hmin, hpeel⟩ :=
    exists_peel_w0_to_w3 hCA0 hCAH hH5 w0 hw0
  obtain ⟨a3, p4, a4, p5, a5, p6, a6, p7, t4, t5, t6, ht4, ht5, ht6, hp_xor, ha_xor, hpack⟩ :=
    exists_pack_w3_even hH2 w3 hw3 hmin
  have ht7 : ((t4 ^^^ t5) ^^^ t6) < pwuHCol bSub := by
    dsimp only [pwuHCol] at ht4 ht5 ht6 ⊢
    exact @Nat.xor_lt_two_pow (t4 ^^^ t5) t6 bSub
      (@Nat.xor_lt_two_pow t4 t5 bSub ht4 ht5) ht6
  refine ⟨a0, a1, a2, a3, p4, a4, p5, a5, p6, a6, p7, t4, t5, t6,
    ht4, ht5, ht6, ht7, hp_xor, ha_xor, fun b ↦ ?_⟩
  rw [← hpeel b, ← hpack b]
  ring

structure WalkerTable where
  thr : Fin 8 → ℕ
  primLf : Fin 8 → Fin 8
  aliasLf : Fin 8 → Fin 8

def TopHalfEvenLf (L : Fin 8 → Fin 8) : Prop :=
  ∃ x4 x5 x6 x7 : Fin 4,
    L 4 = lf4 x4 ∧ L 5 = lf4 x5 ∧ L 6 = lf4 x6 ∧ L 7 = lf4 x7 ∧
    (((x4.val ^^^ x5.val) ^^^ x6.val) ^^^ x7.val) = 0

private theorem bne4_eq_false_imp (a b c d : Bool) (h : (((a != b) != c) != d) = false) :
    (a != b) = (c != d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases h <;> rfl

private theorem TopHalfEvenLf.even_gL {L : Fin 8 → Fin 8} (hL : TopHalfEvenLf L) :
    (decide (4 ≤ (L 4).val) != decide (4 ≤ (L 5).val)) =
      (decide (4 ≤ (L 6).val) != decide (4 ≤ (L 7).val)) := by
  obtain ⟨x4, x5, x6, x7, h4, h5, h6, h7, _⟩ := hL
  have ht (x : Fin 4) : decide (4 ≤ (lf4 x).val) = true := by fin_cases x <;> decide
  rw [h4, h5, h6, h7, ht, ht, ht, ht]

private theorem TopHalfEvenLf.even_g0 {L : Fin 8 → Fin 8} (hL : TopHalfEvenLf L) :
    (decide ((L 4).val % 2 = 1) != decide ((L 5).val % 2 = 1)) =
      (decide ((L 6).val % 2 = 1) != decide ((L 7).val % 2 = 1)) := by
  obtain ⟨x4, x5, x6, x7, h4, h5, h6, h7, hxor⟩ := hL
  have hb (x : Fin 4) : decide ((lf4 x).val % 2 = 1) = x.val.testBit 0 := by
    fin_cases x <;> decide
  rw [h4, h5, h6, h7, hb, hb, hb, hb]
  have hbit := congrArg (fun n ↦ n.testBit 0) hxor
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hbit
  exact bne4_eq_false_imp _ _ _ _ hbit

private theorem TopHalfEvenLf.even_g1 {L : Fin 8 → Fin 8} (hL : TopHalfEvenLf L) :
    (decide (((L 4).val / 2) % 2 = 1) != decide (((L 5).val / 2) % 2 = 1)) =
      (decide (((L 6).val / 2) % 2 = 1) != decide (((L 7).val / 2) % 2 = 1)) := by
  obtain ⟨x4, x5, x6, x7, h4, h5, h6, h7, hxor⟩ := hL
  have hb (x : Fin 4) : decide (((lf4 x).val / 2) % 2 = 1) = x.val.testBit 1 := by
    fin_cases x <;> decide
  rw [h4, h5, h6, h7, hb, hb, hb, hb]
  have hbit := congrArg (fun n ↦ n.testBit 1) hxor
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hbit
  exact bne4_eq_false_imp _ _ _ _ hbit

noncomputable def pwuPadTot (bSub : ℕ) (cfg : Configuration) : ℕ :=
  2 ^ (bSub + 3) - (3 * pwuTq bSub + pwuDl bSub cfg 0 + pwuDl bSub cfg 1 + pwuDl bSub cfg 2)

private theorem pwu_lin_pad_sum {bSub : ℕ} (hbLo : 18 ≤ bSub) (hbHi : bSub ≤
    24) (cfg : Configuration) :
    pwuDl bSub cfg 0 + pwuDl bSub cfg 1 + pwuDl bSub cfg 2 + pwuPadTot bSub cfg =
      5 * pwuHCol bSub + 3 * pwuCAlias bSub := by
  have hused : 3 * pwuTq bSub + pwuDl bSub cfg 0 + pwuDl bSub cfg 1 + pwuDl bSub cfg 2 <
      2 ^ (bSub + 3) := pwu_used_lt_two_pow hbLo hbHi cfg
  have htq : pwuTq bSub < pwuHCol bSub := pwuTq_lt_hcol hbLo hbHi
  have h2b3 : 2 ^ (bSub + 3) = 8 * pwuHCol bSub := by
    dsimp [pwuHCol]; rw [Nat.pow_add]; ring
  unfold pwuPadTot pwuCAlias
  rw [h2b3] at hused ⊢
  omega

noncomputable def pwuW0 (bSub : ℕ) (cfg : Configuration) : Fin 4 → ℕ :=
  vec4 (pwuDl bSub cfg 0) (pwuDl bSub cfg 1) (pwuDl bSub cfg 2) (pwuPadTot bSub cfg)

private theorem lf4_ne_three (b : Fin 4) : lf4 b ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [lf4] at hv
  omega

private theorem sum_fin_hcol_split {bSub : ℕ} (g : Fin 8 → ℂ) {t : ℕ} (ht : t ≤
    2 ^ bSub) (p a : Fin 8) :
    (∑ v : Fin (2 ^ bSub), g (if v.val < t then p else a)) =
      (t : ℂ) * g p + ((2 ^ bSub - t : ℕ) : ℂ) * g a := by
  have hpt : ∀ v : Fin (2 ^ bSub),
      g (if v.val < t then p else a) =
        (if 0 ≤ v.val ∧ v.val < t then g p else 0) +
        (if t ≤ v.val ∧ v.val < 2 ^ bSub then g a else 0) := fun v ↦ by
    by_cases hv : v.val < t
    · rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 hv,
        MomSlots01Slot1ProjKinetic.ite_pos_s1 ⟨Nat.zero_le _, hv⟩,
        MomSlots01Slot1ProjKinetic.ite_neg_s1 (by omega : ¬(t ≤ v.val ∧ v.val < 2 ^ bSub)),
        add_zero]
    · rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hv,
        MomSlots01Slot1ProjKinetic.ite_neg_s1 (by omega : ¬(0 ≤ v.val ∧ v.val < t)),
        MomSlots01Slot1ProjKinetic.ite_pos_s1 ⟨Nat.le_of_not_lt hv, v.isLt⟩,
        zero_add]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [card_fin_Ico_two_pow (Nat.zero_le t) ht, card_fin_Ico_two_pow ht le_rfl, Nat.sub_zero]

private theorem nat_mul_g_lf4_eq (g : Fin 8 → ℂ) (hg7 : g 7 = 0) (c : ℕ) (x : Fin 4) :
    (c : ℂ) * g (lf4 x) =
      ((if x = 0 then c else 0 : ℕ) : ℂ) * g 4 +
      ((if x = 1 then c else 0 : ℕ) : ℂ) * g 5 +
      ((if x = 2 then c else 0 : ℕ) : ℂ) * g 6 := by
  fin_cases x <;> simp [lf4, hg7]

private theorem sum_fin8_eq {M : Type*} [AddCommMonoid M] (f : Fin 8 → M) :
    (∑ c : Fin 8, f c) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  repeat rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_zero, zero_add]
  rfl

private theorem split_same_add {bSub : ℕ} (g : Fin 8 → ℂ) {t : ℕ} (ht : t ≤ 2 ^ bSub) (a : Fin 8) :
    (t : ℂ) * g a + ((2 ^ bSub - t : ℕ) : ℂ) * g a = (pwuHCol bSub : ℂ) * g a := by
  rw [← add_mul]
  congr 1
  dsimp [pwuHCol]
  exact_mod_cast Nat.add_sub_of_le ht

private theorem pwu_sum_from_atoms {bSub : ℕ} (htq_le : pwuTq bSub ≤ 2 ^ bSub)
    (a0 a1 a2 a3 p4 a4 p5 a5 p6 a6 p7 : Fin 4)
    (t4 t5 t6 d0 d1 d2 : ℕ)
    (ht7_le : ((t4 ^^^ t5) ^^^ t6) ≤ 2 ^ bSub)
    (hm0 : (if a0 = 0 then pwuCAlias bSub else 0) +
           (if a1 = 0 then pwuCAlias bSub else 0) +
           (if a2 = 0 then pwuCAlias bSub else 0) +
           (if a3 = 0 then pwuHCol bSub else 0) +
           ((if p4 = 0 then t4 else 0) + (if a4 = 0 then pwuHCol bSub - t4 else 0)) +
           ((if p5 = 0 then t5 else 0) + (if a5 = 0 then pwuHCol bSub - t5 else 0)) +
           ((if p6 = 0 then t6 else 0) + (if a6 = 0 then pwuHCol bSub - t6 else 0)) +
           (if p7 = 0 then pwuHCol bSub else 0) = d0)
    (hm1 : (if a0 = 1 then pwuCAlias bSub else 0) +
           (if a1 = 1 then pwuCAlias bSub else 0) +
           (if a2 = 1 then pwuCAlias bSub else 0) +
           (if a3 = 1 then pwuHCol bSub else 0) +
           ((if p4 = 1 then t4 else 0) + (if a4 = 1 then pwuHCol bSub - t4 else 0)) +
           ((if p5 = 1 then t5 else 0) + (if a5 = 1 then pwuHCol bSub - t5 else 0)) +
           ((if p6 = 1 then t6 else 0) + (if a6 = 1 then pwuHCol bSub - t6 else 0)) +
           (if p7 = 1 then pwuHCol bSub else 0) = d1)
    (hm2 : (if a0 = 2 then pwuCAlias bSub else 0) +
           (if a1 = 2 then pwuCAlias bSub else 0) +
           (if a2 = 2 then pwuCAlias bSub else 0) +
           (if a3 = 2 then pwuHCol bSub else 0) +
           ((if p4 = 2 then t4 else 0) + (if a4 = 2 then pwuHCol bSub - t4 else 0)) +
           ((if p5 = 2 then t5 else 0) + (if a5 = 2 then pwuHCol bSub - t5 else 0)) +
           ((if p6 = 2 then t6 else 0) + (if a6 = 2 then pwuHCol bSub - t6 else 0)) +
           (if p7 = 2 then pwuHCol bSub else 0) = d2)
    (g : Fin 8 → ℂ) (hg7 : g 7 = 0) :
    let tbl : WalkerTable :=
      { thr :=
        vec8 (pwuTq bSub) (pwuTq bSub) (pwuTq bSub) (pwuTq bSub) t4 t5 t6 ((t4 ^^^ t5) ^^^ t6)
        primLf := vec8 0 1 2 (lf4 a3) (lf4 p4) (lf4 p5) (lf4 p6) (lf4 p7)
        aliasLf := vec8 (lf4 a0) (lf4 a1) (lf4 a2) (lf4 a3) (lf4 a4) (lf4 a5) (lf4 a6) (lf4 p7) }
    (∑ col : Fin 8,
      ((tbl.thr col : ℂ) * g (tbl.primLf col) +
        ((2 ^ bSub - tbl.thr col : ℕ) : ℂ) * g (tbl.aliasLf col))) =
      (pwuTq bSub : ℂ) * g 0 + (pwuTq bSub : ℂ) * g 1 + (pwuTq bSub : ℂ) * g 2 +
      (d0 : ℂ) * g 4 + (d1 : ℂ) * g 5 + (d2 : ℂ) * g 6 := by
  intro tbl
  rw [sum_fin8_eq]
  dsimp only [tbl]
  simp only [vec8_0, vec8_1, vec8_2, vec8_3, vec8_4, vec8_5, vec8_6, vec8_7]
  rw [split_same_add g htq_le, split_same_add g ht7_le]
  have hca_eq : (2 ^ bSub - pwuTq bSub : ℕ) = pwuCAlias bSub := rfl
  have hhc_eq : (2 ^ bSub : ℕ) = pwuHCol bSub := rfl
  rw [hca_eq, hhc_eq]
  repeat rw [nat_mul_g_lf4_eq g hg7]
  have h0_c := congrArg (Nat.cast (R := ℂ)) hm0
  have h1_c := congrArg (Nat.cast (R := ℂ)) hm1
  have h2_c := congrArg (Nat.cast (R := ℂ)) hm2
  simp only [Nat.cast_add] at h0_c h1_c h2_c
  linear_combination h0_c * g 4 + h1_c * g 5 + h2_c * g 6

theorem exists_pwuTable_spec {bSub : ℕ} (hbLo : 18 ≤ bSub) (hbHi : bSub ≤
    24) (cfg : Configuration) :
    ∃ tbl : WalkerTable,
      (∀ col : Fin 8,
        tbl.thr col =
          vec8 (pwuTq bSub) (pwuTq bSub) (pwuTq bSub) (pwuTq bSub)
            (tbl.thr 4) (tbl.thr 5) (tbl.thr 6)
            ((tbl.thr 4 ^^^ tbl.thr 5) ^^^ tbl.thr 6) col) ∧
      (∀ col : Fin 8, tbl.thr col < 2 ^ bSub) ∧
      (∀ col : Fin 8, tbl.primLf col ≠ 3 ∧ tbl.aliasLf col ≠ 3) ∧
      TopHalfEvenLf tbl.primLf ∧
      TopHalfEvenLf tbl.aliasLf ∧
      (∀ (g : Fin 8 → ℂ), g 7 = 0 →
        (∑ col : Fin 8,
          ((tbl.thr col : ℂ) * g (tbl.primLf col) +
            ((2 ^ bSub - tbl.thr col : ℕ) : ℂ) * g (tbl.aliasLf col))) =
          (pwuTq bSub : ℂ) * g 0 + (pwuTq bSub : ℂ) * g 1 + (pwuTq bSub : ℂ) * g 2 +
          (pwuDl bSub cfg 0 : ℂ) * g 4 + (pwuDl bSub cfg 1 : ℂ) * g 5 +
          (pwuDl bSub cfg 2 : ℂ) * g 6) := by
  obtain ⟨a0, a1, a2, a3, p4, a4, p5, a5, p6, a6, p7, t4, t5, t6,
      ht4, ht5, ht6, ht7, hp_xor, ha_xor, hmass⟩ :=
    exists_pwu_lin_bucket_mass_even hbLo hbHi (pwuW0 bSub cfg) (pwu_lin_pad_sum hbLo hbHi cfg)
  have htq_lt : pwuTq bSub < 2 ^ bSub := pwuTq_lt_hcol hbLo hbHi
  dsimp only [pwuHCol] at ht4 ht5 ht6 ht7
  refine ⟨
    { thr := vec8 (pwuTq bSub) (pwuTq bSub) (pwuTq bSub) (pwuTq bSub) t4 t5 t6 ((t4 ^^^ t5) ^^^ t6)
      primLf := vec8 0 1 2 (lf4 a3) (lf4 p4) (lf4 p5) (lf4 p6) (lf4 p7)
      aliasLf := vec8 (lf4 a0) (lf4 a1) (lf4 a2) (lf4 a3) (lf4 a4) (lf4 a5) (lf4 a6) (lf4 p7) },
    ?_, ?_, ?_, ⟨p4, p5, p6, p7, rfl, rfl, rfl, rfl, hp_xor⟩,
    ⟨a4, a5, a6, p7, rfl, rfl, rfl, rfl, ha_xor⟩, ?_⟩
  · intro col
    fin_cases col
    all_goals rfl
  · intro col
    fin_cases col
    exacts [htq_lt, htq_lt, htq_lt, htq_lt, ht4, ht5, ht6, ht7]
  · intro col
    fin_cases col
    exacts [⟨by change (0 : Fin 8) ≠ 3; decide, lf4_ne_three _⟩,
      ⟨by change (1 : Fin 8) ≠ 3; decide, lf4_ne_three _⟩,
      ⟨by change (2 : Fin 8) ≠ 3; decide, lf4_ne_three _⟩,
      ⟨lf4_ne_three _, lf4_ne_three _⟩, ⟨lf4_ne_three _, lf4_ne_three _⟩,
      ⟨lf4_ne_three _, lf4_ne_three _⟩, ⟨lf4_ne_three _, lf4_ne_three _⟩,
      ⟨lf4_ne_three _, lf4_ne_three _⟩]
  · intro g hg7
    exact pwu_sum_from_atoms (le_of_lt htq_lt) a0 a1 a2 a3 p4 a4 p5 a5 p6 a6 p7 t4 t5 t6
      (pwuDl bSub cfg 0) (pwuDl bSub cfg 1) (pwuDl bSub cfg 2) (le_of_lt ht7)
      (hmass 0) (hmass 1) (hmass 2) g hg7

noncomputable def pwuTable (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : WalkerTable :=
  Classical.choose (exists_pwuTable_spec hbLo hbHi cfg)

noncomputable def pwuT4 (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : ℕ := (pwuTable bSub hbLo hbHi cfg).thr 4
noncomputable def pwuT5 (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : ℕ := (pwuTable bSub hbLo hbHi cfg).thr 5
noncomputable def pwuT6 (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : ℕ := (pwuTable bSub hbLo hbHi cfg).thr 6

private theorem pwuTable_thr_eq_vec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (col : Fin 8) :
    (pwuTable bSub hbLo hbHi cfg).thr col =
      vec8 (pwuTq bSub) (pwuTq bSub) (pwuTq bSub) (pwuTq bSub)
        (pwuT4 bSub hbLo hbHi cfg) (pwuT5 bSub hbLo hbHi cfg) (pwuT6 bSub hbLo hbHi cfg)
        ((pwuT4 bSub hbLo hbHi cfg ^^^ pwuT5 bSub hbLo hbHi cfg) ^^^ pwuT6 bSub hbLo hbHi cfg) col
          :=
  (Classical.choose_spec (exists_pwuTable_spec hbLo hbHi cfg)).1 col

private theorem pwuTable_thr_lt (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (col : Fin 8) :
    (pwuTable bSub hbLo hbHi cfg).thr col < 2 ^ bSub :=
  (Classical.choose_spec (exists_pwuTable_spec hbLo hbHi cfg)).2.1 col

private theorem pwuTable_prim_topEven (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : TopHalfEvenLf (pwuTable bSub hbLo hbHi cfg).primLf :=
  (Classical.choose_spec (exists_pwuTable_spec hbLo hbHi cfg)).2.2.2.1

private theorem pwuTable_alias_topEven (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : TopHalfEvenLf (pwuTable bSub hbLo hbHi cfg).aliasLf :=
  (Classical.choose_spec (exists_pwuTable_spec hbLo hbHi cfg)).2.2.2.2.1

noncomputable def pwuLeafIdx (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (col : Fin 8) (vSub : ℕ) : Fin 8 :=
  if vSub < (pwuTable bSub hbLo hbHi cfg).thr col then
    (pwuTable bSub hbLo hbHi cfg).primLf col
  else
    (pwuTable bSub hbLo hbHi cfg).aliasLf col

private theorem pwuLeafIdx_ne_three (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (col : Fin 8) (vSub : ℕ) :
    pwuLeafIdx bSub hbLo hbHi cfg col vSub ≠ 3 := by
  obtain ⟨hp, ha⟩ := (Classical.choose_spec (exists_pwuTable_spec hbLo hbHi cfg)).2.2.1 col
  unfold pwuLeafIdx
  split_ifs
  · exact hp
  · exact ha

private theorem sum_pwuLeafIdx_col (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (g : Fin 8 → ℂ) (col : Fin 8) :
    (∑ v : Fin (2 ^ bSub), g (pwuLeafIdx bSub hbLo hbHi cfg col v.val)) =
      ((pwuTable bSub hbLo hbHi cfg).thr col : ℂ) * g ((pwuTable bSub hbLo hbHi cfg).primLf col) +
        ((2 ^ bSub - (pwuTable bSub hbLo hbHi cfg).thr col : ℕ) : ℂ) *
          g ((pwuTable bSub hbLo hbHi cfg).aliasLf col) := by
  unfold pwuLeafIdx
  exact sum_fin_hcol_split g (le_of_lt (pwuTable_thr_lt bSub hbLo hbHi cfg col)) _ _

private theorem sum_pwuLeafIdx_of_pad_zero (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (g : Fin 8 → ℂ) (hg7 : g 7 = 0) :
    (∑ col : Fin 8, ∑ v : Fin (2 ^ bSub), g (pwuLeafIdx bSub hbLo hbHi cfg col v.val)) =
      (pwuTq bSub : ℂ) * g 0 + (pwuTq bSub : ℂ) * g 1 + (pwuTq bSub : ℂ) * g 2 +
      (pwuDl bSub cfg 0 : ℂ) * g 4 + (pwuDl bSub cfg 1 : ℂ) * g 5 +
      (pwuDl bSub cfg 2 : ℂ) * g 6 := by
  simp_rw [sum_pwuLeafIdx_col bSub hbLo hbHi cfg g]
  exact (Classical.choose_spec (exists_pwuTable_spec hbLo hbHi cfg)).2.2.2.2.2 g hg7

def colFromBits (b0 b1 b2 : ZMod 2) : Fin 8 :=
  ⟨b0.val + 2 * b1.val + 4 * b2.val, by
    have := ZMod.val_lt b0
    have := ZMod.val_lt b1
    have := ZMod.val_lt b2
    omega⟩

structure Anf8Coeffs where
  c0 : Bool
  ci0 : Bool
  ci1 : Bool
  ci2 : Bool
  c01 : Bool
  c02 : Bool
  c12 : Bool
def anf8Coeffs (f : Fin 8 → Bool) : Anf8Coeffs :=
  let v0 := f 0; let v1 := f 1; let v2 := f 2; let v3 := f 3
  let v4 := f 4; let v5 := f 5; let v6 := f 6
  let c01 := (v0 != v1) != (v2 != v3)
  { c0 := v0
    ci0 := v0 != v1
    ci1 := v0 != v2
    ci2 := v0 != v4
    c01 := c01
    c02 := (v0 != v1) != (v4 != v5)
    c12 := (v0 != v2) != (v4 != v6)
    }
private theorem b2z_bne (a b : Bool) : b2z (a != b) = b2z a + b2z b := by
  cases a <;> cases b <;> rfl

private theorem ite_bool_zmod2 (p : Bool) (m : ZMod 2) :
    (if p then m else 0) = b2z p * m := by
  cases p <;> simp [b2z]

private theorem bne_top_even_xor {f0 f1 : Fin 8 → Bool}
    (h0 : (f0 4 != f0 5) = (f0 6 != f0 7))
    (h1 : (f1 4 != f1 5) = (f1 6 != f1 7)) :
    ((f0 4 != f1 4) != (f0 5 != f1 5)) = ((f0 6 != f1 6) != (f0 7 != f1 7)) := by
  have hswap (a b c d : Bool) : ((a != b) != (c != d)) = ((a != c) != (b != d)) := by
    cases a <;> cases b <;> cases c <;> cases d <;> rfl
  rw [hswap (f0 4) (f1 4) (f0 5) (f1 5), hswap (f0 6) (f1 6) (f0 7) (f1 7), h0, h1]

private theorem anf8_eval_monom3 (f : Fin 8 → Bool) (heven : (f 4 != f 5) = (f 6 != f 7))
    (b0 b1 b2 : ZMod 2) :
    let cs := anf8Coeffs f
    b2z cs.c0 +
      ((if cs.ci0 then b0 else 0) +
        ((if cs.ci1 then b1 else 0) +
          ((if cs.ci2 then b2 else 0) +
            ((if cs.c01 then (b0 + b0 * b2) * (b1 + b1 * b2) else 0) +
              ((if cs.c02 then b0 * b2 else 0) +
                ((if cs.c12 then b1 * b2 else 0) + 0)))))) =
      b2z (f (colFromBits b0 b1 b2)) := by
  have hev_z : b2z (f 4) + b2z (f 5) = b2z (f 6) + b2z (f 7) := by
    simpa only [b2z_bne] using congrArg b2z heven
  dsimp only [anf8Coeffs]
  simp only [ite_bool_zmod2, b2z_bne]
  have h2 : (2 : ZMod 2) = 0 := rfl
  have h4 : (4 : ZMod 2) = 0 := rfl
  have h6 : (6 : ZMod 2) = 0 := rfl
  have h8 : (8 : ZMod 2) = 0 := rfl
  rcases bit_cases b0 with rfl | rfl <;>
    rcases bit_cases b1 with rfl | rfl <;>
    rcases bit_cases b2 with rfl | rfl
  · dsimp [colFromBits]; ring_nf
  · dsimp [colFromBits]; ring_nf; try simp [h2]
  · dsimp [colFromBits]; ring_nf; try simp [h2]
  · dsimp [colFromBits]; ring_nf; try simp [h2, h4]
  · dsimp [colFromBits]; ring_nf; try simp [h2]
  · dsimp [colFromBits]; ring_nf; try simp [h2, h4]
  · dsimp [colFromBits]; ring_nf; try simp [h2, h4]
  · dsimp [colFromBits]
    have h11 : (1 : ZMod 2) + 1 * 1 = 0 := rfl
    rw [h11, zero_mul, mul_zero]
    have hid :
        b2z (f 0) +
          ((b2z (f 0) + b2z (f 1)) * 1 +
            ((b2z (f 0) + b2z (f 2)) * 1 +
              ((b2z (f 0) + b2z (f 4)) * 1 +
                (0 +
                  (((b2z (f 0) + b2z (f 1)) + (b2z (f 4) + b2z (f 5))) * (1 * 1) +
                    (((b2z (f 0) + b2z (f 2)) + (b2z (f 4) + b2z (f 6))) * (1 * 1) + 0)))))) =
        b2z (f 7) + ((b2z (f 4) + b2z (f 5)) - (b2z (f 6) + b2z (f 7))) +
          2 * (3 * b2z (f 0) + b2z (f 1) + b2z (f 2) + b2z (f 4) + b2z (f 6)) := by
      ring
    rw [hid, hev_z, sub_self, h2, zero_mul, add_zero, add_zero]

def ssaCastEnd {M cur e1 e2 : ℕ} (h : e1 = e2) (p : SsaProg M cur e1) : SsaProg M cur e2 :=
  ⟨p.raw, h ▸ p.wf⟩

@[simp]
theorem ssaCastEnd_countAnd {M cur e1 e2 : ℕ} (h : e1 = e2) (p : SsaProg M cur e1) :
    (ssaCastEnd h p).countAnd = p.countAnd := rfl

@[simp]
theorem ssaCastEnd_eval {M cur e1 e2 : ℕ} (h : e1 = e2) (p : SsaProg M cur e1) :
    (ssaCastEnd h p).eval = p.eval := rfl

def skipZeroN {M : ℕ} (cur : ℕ) : (n : ℕ) → cur + n ≤ M → SsaProg M cur (cur + n)
  | 0, _ => .done cur
  | n + 1, h => .skipZero (by omega) (ssaCastEnd (by omega) (skipZeroN (cur + 1) n (by omega)))

@[simp]
theorem skipZeroN_countAnd {M : ℕ} :
    ∀ (cur n : ℕ) (h : cur + n ≤ M), (skipZeroN cur n h).countAnd = 0
  | _, 0, _ => rfl
  | cur, n + 1, h => by simp [skipZeroN, skipZeroN_countAnd (cur + 1) n]

@[simp]
theorem skipZeroN_eval {M : ℕ} :
    ∀ (cur n : ℕ) (h : cur + n ≤ M) (β : BitAssignment M), (skipZeroN cur n h).eval β = β
  | _, 0, _, _ => rfl
  | cur, n + 1, h, β => by simp [skipZeroN, SsaProg.eval_skipZero, skipZeroN_eval (cur + 1) n]

private theorem sliceVal_cast_len {M : ℕ} (β : BitAssignment M) (base : ℕ) {l1 l2 : ℕ}
    (hl : l1 = l2) (h1 : base + l1 ≤ M) (h2 : base + l2 ≤ M) :
    sliceVal β base l1 h1 = sliceVal β base l2 h2 := by
  subst hl; try rfl

private theorem prioStarEval_zero_step0 (f : ℕ → ZMod 2) :
    ∀ (k : ℕ) (α : BitAssignment (k + 1)),
      prioStarEval (α 0 * f 0) (fun t ↦ f (t + 1)) k
          (fun i ↦ α ⟨i.val + 1, by omega⟩) =
        prioStarEval 0 f (k + 1) α
  | 0, α => by
      dsimp only [prioStarEval]
      have h0 : (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) = 0 := rfl
      rw [h0]
      rcases bit_cases (α 0) with ha | ha <;> simp [ha]
  | k + 1, α => by
      dsimp only [prioStarEval]
      by_cases htop : α ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ = 1
      · have htop' : α ⟨k + 1, by omega⟩ = 1 := htop
        simp [htop]
      · have htop' : ¬(α ⟨k + 1, by omega⟩ = 1) := htop
        simp only [htop, ↓reduceIte]
        have ih := prioStarEval_zero_step0 f k (fun i ↦ α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        dsimp only [prioStarEval] at ih
        exact ih

def anfMonomTerms (bSub : ℕ) (hbHi : bSub ≤ 24) (cur : ℕ) (wTarget : Wire 185)
    (hlo : 114 ≤ cur) (hwTarget : wTarget.val = 110 ∨ 114 ≤ wTarget.val)
    (cs : Anf8Coeffs) :
    List (Bool × { w : Wire 185 // w.val < cur ∧ w ≠ wTarget }) :=
  [(cs.ci0, ⟨⟨30 + bSub, by omega⟩, ⟨by dsimp; omega, Fin.ne_of_val_ne (by dsimp; omega)⟩⟩),
   (cs.ci1, ⟨⟨31 + bSub, by omega⟩, ⟨by dsimp; omega, Fin.ne_of_val_ne (by dsimp; omega)⟩⟩),
   (cs.ci2, ⟨⟨32 + bSub, by omega⟩, ⟨by dsimp; omega, Fin.ne_of_val_ne (by dsimp; omega)⟩⟩),
   (cs.c01, ⟨⟨113, by decide⟩, ⟨by dsimp; omega, Fin.ne_of_val_ne (by dsimp; omega)⟩⟩),
   (cs.c02, ⟨⟨111, by decide⟩, ⟨by dsimp; omega, Fin.ne_of_val_ne (by dsimp; omega)⟩⟩),
   (cs.c12, ⟨⟨112, by decide⟩, ⟨by dsimp; omega, Fin.ne_of_val_ne (by dsimp; omega)⟩⟩)]

def anfMux1Step (bSub : ℕ) (hbHi : bSub ≤ 24) (cur : ℕ) (hlo : 139 ≤ cur) (hcur : cur < 185)
    (f0 f1 : Fin 8 → Bool) : SsaProg 185 cur (cur + 1) :=
  let wThr : Wire 185 := ⟨110, by decide⟩
  let wCmp : Wire 185 := ⟨138, by decide⟩
  let wOut : Wire 185 := ⟨cur, hcur⟩
  let dCs := anf8Coeffs (fun c ↦ f0 c != f1 c)
  let bCs := anf8Coeffs f0
  let dLs := anfMonomTerms bSub hbHi cur wThr (by omega) (Or.inl rfl) dCs
  let bLs := anfMonomTerms bSub hbHi (cur + 1) wOut (by omega) (Or.inr (by dsimp [wOut]; omega)) bCs
  (((toggleThrWire cur wThr (by dsimp [wThr]; omega) dCs.c0 dLs).append
    (andPol cur hcur wCmp wThr (Fin.ne_of_val_ne (by decide))
      (by dsimp [wCmp]; omega) (by dsimp [wThr]; omega) false false)).append
    (toggleThrWire (cur + 1) wThr (by dsimp [wThr]; omega) dCs.c0
      (widenTerms (Nat.le_succ cur) dLs))).append
    (toggleThrWire (cur + 1) wOut (by dsimp [wOut]; omega) bCs.c0 bLs)

private theorem toggleListOn_countAnd_loc (cur : ℕ) (wThr : Wire 185) (hw : wThr.val < cur) :
    ∀ ls, (toggleListOn cur wThr hw ls).countAnd = 0
  | [] => rfl
  | (en, ⟨_, _, _⟩) :: tl => by
      dsimp only [toggleListOn]; split_ifs <;> simp [toggleListOn_countAnd_loc cur wThr hw tl]

private theorem toggleThrWire_countAnd_loc (cur : ℕ) (wThr : Wire 185) (hw : wThr.val < cur)
    (c0 : Bool) (ls : List (Bool × { w : Wire 185 // w.val < cur ∧ w ≠ wThr })) :
    (toggleThrWire cur wThr hw c0 ls).countAnd = 0 := by
  dsimp only [toggleThrWire]; split_ifs <;> simp [toggleListOn_countAnd_loc]

@[simp]
theorem anfMux1Step_countAnd (bSub : ℕ) (hbHi : bSub ≤ 24) (cur : ℕ)
    (hlo : 139 ≤ cur) (hcur : cur < 185) (f0 f1 : Fin 8 → Bool) :
    (anfMux1Step bSub hbHi cur hlo hcur f0 f1).countAnd = 1 := by
  simp [anfMux1Step, toggleThrWire_countAnd_loc]

private theorem anfMux1_combine_bool (cmp : ZMod 2) (a b : Bool) :
    cmp * b2z (a != b) + b2z a = if cmp = 1 then b2z b else b2z a := by
  rcases bit_cases cmp with rfl | rfl <;> cases a <;> cases b <;> decide

private theorem anfMux1Step_spec (bSub : ℕ) (hbHi : bSub ≤ 24) (cur : ℕ)
    (hlo : 139 ≤ cur) (hcur : cur < 185) (f0 f1 : Fin 8 → Bool)
    (heven0 : (f0 4 != f0 5) = (f0 6 != f0 7))
    (heven1 : (f1 4 != f1 5) = (f1 6 != f1 7)) :
    PreservesOutside cur (cur + 1) (anfMux1Step bSub hbHi cur hlo hcur f0 f1).eval ∧
    ∀ (β : BitAssignment 185),
      β ⟨110, by decide⟩ = 0 →
      β ⟨111, by decide⟩ = β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ →
      β ⟨112, by decide⟩ = β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ →
      β ⟨113, by decide⟩ =
        (β ⟨30 + bSub, by omega⟩ + β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩) *
          (β ⟨31 + bSub, by omega⟩ + β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩) →
      β ⟨cur, hcur⟩ = 0 →
      (anfMux1Step bSub hbHi cur hlo hcur f0 f1).eval β ⟨cur, hcur⟩ =
        let col := colFromBits
          (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩)
        if β ⟨138, by decide⟩ = 1 then b2z (f1 col) else b2z (f0 col) := by
  let wThr : Wire 185 := ⟨110, by decide⟩
  let wCmp : Wire 185 := ⟨138, by decide⟩
  let wOut : Wire 185 := ⟨cur, hcur⟩
  have hto : wThr ≠ wOut := Fin.ne_of_val_ne (by dsimp [wThr, wOut]; omega)
  have hct : wCmp ≠ wThr := Fin.ne_of_val_ne (by decide)
  let dCs := anf8Coeffs (fun c ↦ f0 c != f1 c)
  let bCs := anf8Coeffs f0
  let dLs := anfMonomTerms bSub hbHi cur wThr (by omega) (Or.inl rfl) dCs
  let bLs := anfMonomTerms bSub hbHi (cur + 1) wOut (by omega) (Or.inr (by dsimp [wOut]; omega)) bCs
  let dBit (β : BitAssignment 185) : ZMod 2 := b2z dCs.c0 + thrXorSum cur wThr β dLs
  let sub3 : SsaProg 185 cur (cur + 1) :=
    ((toggleThrWire cur wThr (by dsimp [wThr]; omega) dCs.c0 dLs).append
      (andPol cur hcur wCmp wThr hct (by dsimp [wCmp]; omega) (by dsimp [wThr]; omega) false
        false)).append
      (toggleThrWire (cur +
        1) wThr (by dsimp [wThr]; omega) dCs.c0 (widenTerms (Nat.le_succ cur) dLs))
  have hPres3 : PreservesOutside cur (cur + 1) sub3.eval := by
    intro β w hw
    dsimp only [sub3]
    simp only [SsaProg.append_eval]
    let β₁ := (toggleThrWire cur wThr (by dsimp [wThr]; omega) dCs.c0 dLs).eval β
    have hβ₁ : β₁ = Function.update β wThr (β wThr + dBit β) :=
      toggleThrWire_eval cur wThr _ dCs.c0 dLs β
    let β₂ :=
      (andPol cur hcur wCmp wThr hct (by dsimp [wCmp]; omega) (by dsimp [wThr]; omega) false
      false).eval β₁
    have hPresA :=
      andPol_preserves cur hcur wCmp wThr hct (by dsimp [wCmp]; omega) (by dsimp [wThr]; omega)
      false false
    rw [toggleThrWire_eval (cur + 1) wThr _ dCs.c0 _ β₂, thrXorSum_widen (Nat.le_succ cur) β₂ dLs]
    have hsum₂ : thrXorSum cur wThr β₂ dLs = thrXorSum cur wThr β dLs :=
      thrXorSum_congr cur wThr (fun u hlt hne_u ↦ by
        dsimp only [β₂]
        rw [hPresA β₁ u (Or.inl hlt), hβ₁, Function.update_of_ne hne_u]) dLs
    have ht₂ : β₂ wThr = β wThr + dBit β := by
      dsimp only [β₂]
      rw [hPresA β₁ wThr (Or.inl (by dsimp [wThr]; omega)), hβ₁, Function.update_self]
    rw [hsum₂, ht₂]
    change Function.update β₂ wThr ((β wThr + dBit β) + dBit β) w = β w
    rw [zmod2_add_assoc_cancel]
    by_cases hwt : w = wThr
    · subst hwt; exact Function.update_self _ _ _
    · rw [Function.update_of_ne hwt]
      dsimp only [β₂]
      rw [hPresA β₁ w hw, hβ₁, Function.update_of_ne hwt]
  refine ⟨fun β w hw ↦ ?_, fun β hzt hm02 hm12 hm01e hzc ↦ ?_⟩
  · dsimp only [anfMux1Step]
    rw [SsaProg.append_eval]
    let β₃ := sub3.eval β
    change (toggleThrWire (cur + 1) wOut _ bCs.c0 bLs).eval β₃ w = β w
    rw [toggleThrWire_eval]
    have hw_ne : w ≠ wOut := Fin.ne_of_val_ne (by dsimp [wOut]; omega)
    rw [Function.update_of_ne hw_ne]
    exact hPres3 β w hw
  · dsimp only [anfMux1Step]
    simp only [SsaProg.append_eval]
    let β₁ := (toggleThrWire cur wThr (by dsimp [wThr]; omega) dCs.c0 dLs).eval β
    have hβ₁ : β₁ = Function.update β wThr (β wThr + dBit β) :=
      toggleThrWire_eval cur wThr _ dCs.c0 dLs β
    have hz₁ : β₁ wOut = 0 := by rw [hβ₁, Function.update_of_ne hto.symm, hzc]
    let β₂ :=
      (andPol cur hcur wCmp wThr hct (by dsimp [wCmp]; omega) (by dsimp [wThr]; omega) false
      false).eval β₁
    have hβ₂ : β₂ = Function.update β₁ wOut ((β₁ wCmp + b2z false) * (β₁ wThr + b2z false)) :=
      andPol_eval cur hcur wCmp wThr hct _ _ false false β₁ hz₁
    let β₃ := (toggleThrWire (cur + 1) wThr (by dsimp [wThr]; omega) dCs.c0
      (widenTerms (Nat.le_succ cur) dLs)).eval β₂
    have hβ₃_out : β₃ wOut = β wCmp * dBit β := by
      dsimp only [β₃]
      rw [toggleThrWire_eval, Function.update_of_ne hto.symm, hβ₂, Function.update_self]
      have hc₁ : β₁ wCmp = β wCmp := by rw [hβ₁, Function.update_of_ne hct]
      have ht₁ : β₁ wThr = dBit β := by rw [hβ₁, Function.update_self, hzt, zero_add]
      rw [hc₁, ht₁]
      simp [b2z]
    change (toggleThrWire (cur + 1) wOut _ bCs.c0 bLs).eval β₃ wOut = _
    rw [toggleThrWire_eval, Function.update_self, hβ₃_out]
    have hβ₃_eq : β₃ = sub3.eval β := by
      dsimp only [β₃, β₂, β₁, sub3]
      simp only [SsaProg.append_eval]
    have hPres3_lt : ∀ (i : ℕ) (hi : i < 114), β₃ ⟨i, by omega⟩ = β ⟨i, by omega⟩ :=
      fun i hi ↦ by rw [hβ₃_eq]; exact hPres3 β ⟨i, by omega⟩ (Or.inl (by dsimp; omega))
    have hd_sum : dBit β =
        b2z ((fun c ↦ f0 c != f1 c)
          (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub,
            by omega⟩))) := by
      dsimp only [dBit, dLs, anfMonomTerms, thrXorSum]
      rw [hm01e, hm02, hm12]
      exact anf8_eval_monom3 (fun c ↦ f0 c != f1 c) (bne_top_even_xor heven0 heven1)
        (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩)
    have hb_sum : b2z bCs.c0 + thrXorSum (cur + 1) wOut β₃ bLs =
        b2z (f0 (colFromBits
          (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩))) := by
      dsimp only [bLs, anfMonomTerms, thrXorSum]
      rw [hPres3_lt (30 + bSub) (by omega), hPres3_lt (31 + bSub) (by omega),
        hPres3_lt (32 + bSub) (by omega), hPres3_lt 113 (by decide),
        hPres3_lt 111 (by decide), hPres3_lt 112 (by decide),
        hm01e, hm02, hm12]
      exact anf8_eval_monom3 f0 heven0
        (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩)
    rw [hd_sum, hb_sum]
    exact anfMux1_combine_bool (β wCmp) _ _

private theorem walker_thr_testBit_anf (t0 t4 t5 t6 j : ℕ) (b0 b1 b2 : ZMod 2) :
    b2z (t0.testBit j) +
      ((if (t0 ^^^ t4).testBit j then b2 else 0) +
        ((if (t4 ^^^ t5).testBit j then b0 * b2 else 0) +
          ((if (t4 ^^^ t6).testBit j then b1 * b2 else 0) + 0))) =
      b2z ((vec8 t0 t0 t0 t0 t4 t5 t6 ((t4 ^^^ t5) ^^^ t6)
        (colFromBits b0 b1 b2)).testBit j) := by
  rcases bit_cases b0 with rfl | rfl <;>
    rcases bit_cases b1 with rfl | rfl <;>
    rcases bit_cases b2 with rfl | rfl <;>
    (dsimp [colFromBits, vec8]
     simp only [Nat.testBit_xor]
     generalize t0.testBit j = a0
     generalize t4.testBit j = a4
     generalize t5.testBit j = a5
     generalize t6.testBit j = a6
     cases a0 <;> cases a4 <;> cases a5 <;> cases a6 <;> decide)

def pwuThrTerms (bSub : ℕ) (hbHi : bSub ≤ 24) (cur : ℕ) (hlo : 114 ≤ cur) (t0 t4 t5 t6 j : ℕ) :
    List (Bool × { w : Wire 185 // w.val < cur ∧ w ≠ ⟨110, by decide⟩ }) :=
  [((t0 ^^^ t4).testBit j,
    ⟨⟨32 + bSub, by omega⟩, ⟨by dsimp; omega, Fin.ne_of_val_ne (by dsimp; omega)⟩⟩),
   ((t4 ^^^ t5).testBit j, ⟨⟨111, by decide⟩, ⟨by dsimp; omega, Fin.ne_of_val_ne (by decide)⟩⟩),
   ((t4 ^^^ t6).testBit j, ⟨⟨112, by decide⟩, ⟨by dsimp; omega, Fin.ne_of_val_ne (by decide)⟩⟩)]

def pwuThrCompare (bSub : ℕ) (hbHi : bSub ≤ 24) (t0 t4 t5 t6 : ℕ) :
    (k : ℕ) → (hk : k < bSub) → SsaProg 185 114 (114 + (k + 1))
  | 0, _ =>
      qqLtBaseInlineThr (M := 185) 114 (by decide) ⟨110, by decide⟩ ⟨30, by decide⟩
        (Fin.ne_of_val_ne (by decide)) (by decide) (by decide)
        (t0.testBit 0)
        (pwuThrTerms bSub hbHi 114 le_rfl t0 t4 t5 t6 0)
  | k + 1, hk =>
      (pwuThrCompare bSub hbHi t0 t4 t5 t6 k (by omega)).append <|
        qqLtStepInlineThr (M := 185) (114 + (k + 1)) (by omega)
          ⟨110, by decide⟩ ⟨30 + (k + 1), by omega⟩ ⟨114 + k, by omega⟩
          (Fin.ne_of_val_ne (by dsimp; omega))
          (Fin.ne_of_val_ne (by dsimp; omega))
          (Fin.ne_of_val_ne (by dsimp; omega))
          (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
          (t0.testBit (k + 1))
          (pwuThrTerms bSub hbHi (114 + (k + 1)) (by omega) t0 t4 t5 t6 (k + 1))

@[simp]
theorem pwuThrCompare_countAnd (bSub : ℕ) (hbHi : bSub ≤ 24) (t0 t4 t5 t6 : ℕ) :
    ∀ (k : ℕ) (hk : k < bSub), (pwuThrCompare bSub hbHi t0 t4 t5 t6 k hk).countAnd = k + 1
  | 0, _ => by simp [pwuThrCompare, qqLtBaseInlineThr, toggleThrWire_countAnd_loc]
  | k + 1, hk => by
      simp [pwuThrCompare, qqLtStepInlineThr, toggleThrWire_countAnd_loc,
        pwuThrCompare_countAnd bSub hbHi t0 t4 t5 t6 k]

private theorem pwuThrCompare_spec (bSub : ℕ) (hbHi : bSub ≤ 24) (t0 t4 t5 t6 : ℕ) :
    ∀ (k : ℕ) (hk : k < bSub),
      PreservesOutside 114 (114 + (k + 1)) (pwuThrCompare bSub hbHi t0 t4 t5 t6 k hk).eval ∧
      ∀ (β : BitAssignment 185),
        β ⟨110, by decide⟩ = 0 →
        β ⟨111, by decide⟩ = β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ →
        β ⟨112, by decide⟩ = β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ →
        (∀ w : Wire 185, 114 ≤ w.val → β w = 0) →
        (pwuThrCompare bSub hbHi t0 t4 t5 t6 k hk).eval β ⟨114 + k, by omega⟩ =
          let col := colFromBits
            (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩)
          let T := vec8 t0 t0 t0 t0 t4 t5 t6 ((t4 ^^^ t5) ^^^ t6) col
          if sliceVal β 30 (k + 1) (by omega) < T % 2 ^ (k + 1) then 1 else 0
  | 0, hk => by
      obtain ⟨hPresB, hEvalB⟩ := qqLtBaseInlineThr_spec (M := 185) 114 (by decide)
        ⟨110, by decide⟩ ⟨30, by decide⟩ (Fin.ne_of_val_ne (by decide)) (by decide) (by decide)
        (t0.testBit 0) (pwuThrTerms bSub hbHi 114 le_rfl t0 t4 t5 t6 0)
      refine ⟨hPresB, fun β hzt hm02 hm12 hz ↦ ?_⟩
      dsimp only [pwuThrCompare]
      have hidx0 : (⟨114 + 0, by omega⟩ : Wire 185) = ⟨114, by decide⟩ := Fin.ext rfl
      rw [hidx0, hEvalB β hzt (hz _ le_rfl)]
      dsimp only [pwuThrTerms, thrXorSum]
      rw [hm02, hm12, walker_thr_testBit_anf t0 t4 t5 t6 0
        (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩)]
      let T := vec8 t0 t0 t0 t0 t4 t5 t6 ((t4 ^^^ t5) ^^^ t6)
        (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩))
      have hsl : sliceVal β 30 1 (by decide) = (β ⟨30, by decide⟩).val := by
        dsimp [sliceVal]; omega
      have hTmod : T % 2 ^ 1 = if T.testBit 0 then 1 else 0 := by
        rw [Nat.testBit_zero]
        cases hmod : T % 2 with
        | zero => simp
        | succ m =>
            have hlt : T % 2 < 2 := Nat.mod_lt T (by decide)
            have hm : m = 0 := by omega
            subst hm; simp
      rw [hsl, hTmod]
      generalize T.testBit 0 = tb
      rcases bit_cases (β ⟨30, by decide⟩) with h30 | h30 <;> rw [h30] <;> cases tb <;> decide
  | k + 1, hk => by
      obtain ⟨hPres, ih⟩ := pwuThrCompare_spec bSub hbHi t0 t4 t5 t6 k (by omega)
      obtain ⟨hPresS, hEvalS⟩ := qqLtStepInlineThr_spec (M := 185) (114 + (k + 1)) (by omega)
        ⟨110, by decide⟩ ⟨30 + (k + 1), by omega⟩ ⟨114 + k, by omega⟩
        (Fin.ne_of_val_ne (by dsimp; omega))
        (Fin.ne_of_val_ne (by dsimp; omega))
        (Fin.ne_of_val_ne (by dsimp; omega))
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
        (t0.testBit (k + 1))
        (pwuThrTerms bSub hbHi (114 + (k + 1)) (by omega) t0 t4 t5 t6 (k + 1))
      refine ⟨fun β w hw ↦ ?_, fun β hzt hm02 hm12 hz ↦ ?_⟩
      · simp only [pwuThrCompare, SsaProg.append_eval]
        exact PreservesOutside.comp (by omega) (by omega) hPres hPresS β w hw
      · simp only [pwuThrCompare, SsaProg.append_eval]
        let β₁ := (pwuThrCompare bSub hbHi t0 t4 t5 t6 k (by omega)).eval β
        have hzt₁ : β₁ ⟨110, by decide⟩ = 0 :=
          (hPres β ⟨110, by decide⟩ (Or.inl (by decide))).trans hzt
        have hzc₁ : β₁ ⟨114 + (k + 1), by omega⟩ = 0 :=
          (hPres β ⟨114 + (k + 1),
            by omega⟩ (Or.inr (by dsimp; omega))).trans (hz _ (by dsimp; omega))
        have hi0 : β₁ ⟨30 + bSub, by omega⟩ = β ⟨30 + bSub, by omega⟩ :=
          hPres β ⟨30 + bSub, by omega⟩ (Or.inl (by dsimp; omega))
        have hi1 : β₁ ⟨31 + bSub, by omega⟩ = β ⟨31 + bSub, by omega⟩ :=
          hPres β ⟨31 + bSub, by omega⟩ (Or.inl (by dsimp; omega))
        have hi2 : β₁ ⟨32 + bSub, by omega⟩ = β ⟨32 + bSub, by omega⟩ :=
          hPres β ⟨32 + bSub, by omega⟩ (Or.inl (by dsimp; omega))
        have hm02₁ : β₁ ⟨111, by decide⟩ = β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ :=
          (hPres β ⟨111, by decide⟩ (Or.inl (by decide))).trans hm02
        have hm12₁ : β₁ ⟨112, by decide⟩ = β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ :=
          (hPres β ⟨112, by decide⟩ (Or.inl (by decide))).trans hm12
        have huj₁ : β₁ ⟨30 + (k + 1), by omega⟩ = β ⟨30 + (k + 1), by omega⟩ :=
          hPres β ⟨30 + (k + 1), by omega⟩ (Or.inl (by dsimp; omega))
        let col := colFromBits
          (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩)
        let T := vec8 t0 t0 t0 t0 t4 t5 t6 ((t4 ^^^ t5) ^^^ t6) col
        have hprev : β₁ ⟨114 + k, by omega⟩ =
            if sliceVal β 30 (k + 1) (by omega) < T % 2 ^ (k + 1) then 1 else 0 :=
          ih β hzt hm02 hm12 hz
        change (qqLtStepInlineThr (114 + (k + 1)) _ ⟨110, by decide⟩ ⟨30 + (k + 1), _⟩
          ⟨114 + k, _⟩ _ _ _ _ _ _ (t0.testBit (k + 1)) _).eval β₁ ⟨114 + (k + 1), by omega⟩ = _
        rw [hEvalS β₁ hzt₁ hzc₁]
        dsimp only [pwuThrTerms, thrXorSum]
        rw [hi2, hm02₁, hm12₁, huj₁, hprev,
          walker_thr_testBit_anf t0 t4 t5 t6 (k + 1)
            (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩)]
        have hsl_u : sliceVal β 30 (k + 1 + 1) (by omega) =
            sliceVal β 30 (k + 1) (by omega) +
              (β ⟨30 + (k + 1), by omega⟩).val * 2 ^ (k + 1) := rfl
        rw [hsl_u]
        change (if β ⟨30 + (k + 1), by omega⟩ = b2z (T.testBit (k + 1)) then
            if sliceVal β 30 (k + 1) (by omega) < T % 2 ^ (k + 1) then 1 else 0
          else b2z (T.testBit (k + 1))) =
          if sliceVal β 30 (k + 1) (by omega) + (β ⟨30 + (k + 1), by omega⟩).val * 2 ^ (k + 1) <
              T % 2 ^ ((k + 1) + 1) then 1 else 0
        rw [nat_mod_two_pow_succ T (k + 1)]
        have hstep := nat_lt_step_msb
          (sliceVal_lt_two_pow β 30 (k + 1) (by omega))
          (Nat.mod_lt T (Nat.two_pow_pos (k + 1)))
          (ZMod.val_lt (β ⟨30 + (k + 1), by omega⟩))
          (show (if T.testBit (k + 1) then 1 else 0) < 2 by cases T.testBit (k + 1) <;> decide)
        by_cases hlt : sliceVal β 30 (k + 1) (by omega) +
            (β ⟨30 + (k + 1), by omega⟩).val * 2 ^ (k + 1) <
            T % 2 ^ (k + 1) + (if T.testBit (k + 1) then 1 else 0) * 2 ^ (k + 1)
        · simp only [hlt, ↓reduceIte]
          have hrhs := hstep.mp hlt
          cases htk : T.testBit (k + 1) <;>
            rcases bit_cases (β ⟨30 + (k + 1), by omega⟩) with au | au <;>
            simp_all [b2z]
        · simp only [hlt, ↓reduceIte]
          have hrhs : ¬ (if (β ⟨30 + (k + 1), by omega⟩).val =
              (if T.testBit (k + 1) then 1 else 0) then
              sliceVal β 30 (k + 1) (by omega) < T % 2 ^ (k + 1) else
              (if T.testBit (k + 1) then 1 else 0) = 1) :=
            fun hh ↦ hlt (hstep.mpr hh)
          cases htk : T.testBit (k + 1) <;>
            rcases bit_cases (β ⟨30 + (k + 1), by omega⟩) with au | au <;>
            simp_all [b2z]


def pwuSt0 : SsaProg 185 110 111 :=
  .skipZero (by decide) (.done 111)

def pwuStMonom3Step (bSub : ℕ) (hbHi : bSub ≤ 24) : SsaProg 185 113 114 :=
  (SsaProg.cnot ⟨111, by decide⟩ ⟨30 + bSub, by omega⟩
    (Fin.ne_of_val_ne (by dsimp; omega)) (by decide) (by dsimp; omega)
    (.cnot ⟨112, by decide⟩ ⟨31 + bSub, by omega⟩
      (Fin.ne_of_val_ne (by dsimp; omega)) (by decide) (by dsimp; omega) (.done 113))).append <|
  (andPol (M := 185) 113 (by decide) ⟨30 + bSub, by omega⟩ ⟨31 + bSub, by omega⟩
    (Fin.ne_of_val_ne (by dsimp; omega)) (by dsimp; omega) (by dsimp; omega) false false).append <|
  SsaProg.cnot ⟨112, by decide⟩ ⟨31 + bSub, by omega⟩
    (Fin.ne_of_val_ne (by dsimp; omega)) (by decide) (by dsimp; omega)
    (.cnot ⟨111, by decide⟩ ⟨30 + bSub, by omega⟩
      (Fin.ne_of_val_ne (by dsimp; omega)) (by decide) (by dsimp; omega) (.done 114))

def pwuStMonomRaw (bSub : ℕ) (hbHi : bSub ≤ 24) : SsaProg 185 111 114 :=
  (andPol (M := 185) 111 (by decide) ⟨30 + bSub, by omega⟩ ⟨32 + bSub, by omega⟩
    (Fin.ne_of_val_ne (by dsimp; omega)) (by dsimp; omega) (by dsimp; omega) false false).append <|
  (andPol (M := 185) 112 (by decide) ⟨31 + bSub, by omega⟩ ⟨32 + bSub, by omega⟩
    (Fin.ne_of_val_ne (by dsimp; omega)) (by dsimp; omega) (by dsimp; omega) false false).append <|
  pwuStMonom3Step bSub hbHi

noncomputable def pwuStMonom (bSub : ℕ) (hbHi : bSub ≤ 24) : SsaProg 185 111 114 :=
  lockValWalker (pwuStMonomRaw bSub hbHi)

noncomputable def pwuStCmpRaw (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 114 139 :=
  let cmpProg : SsaProg 185 114 (114 + bSub) :=
    ssaCastEnd (by omega)
      (pwuThrCompare bSub hbHi (pwuTq bSub)
        (pwuT4 bSub hbLo hbHi cfg) (pwuT5 bSub hbLo hbHi cfg) (pwuT6 bSub hbLo hbHi cfg)
        (bSub - 1) (by omega))
  let padProg : SsaProg 185 (114 + bSub) 139 :=
    ssaCastEnd (by omega) (skipZeroN (M := 185) (114 + bSub) (25 - bSub) (by omega))
  let copyCmp : SsaProg 185 139 139 :=
    .cnot ⟨114 + (bSub - 1), by omega⟩ ⟨138, by decide⟩
      (Fin.ne_of_val_ne (by dsimp; omega)) (by dsimp; omega) (by decide) (.done 139)
  (cmpProg.append padProg).append copyCmp

noncomputable def pwuStCmp (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 114 139 :=
  lockValWalker (pwuStCmpRaw bSub hbLo hbHi cfg)

noncomputable def pwuStGLRaw (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 139 140 :=
  anfMux1Step bSub hbHi 139 le_rfl (by decide)
    (fun c ↦ decide (4 ≤ ((pwuTable bSub hbLo hbHi cfg).aliasLf c).val))
    (fun c ↦ decide (4 ≤ ((pwuTable bSub hbLo hbHi cfg).primLf c).val))

noncomputable def pwuStGL (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 139 140 :=
  lockValWalker (pwuStGLRaw bSub hbLo hbHi cfg)

noncomputable def pwuStG0Raw (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 140 141 :=
  anfMux1Step bSub hbHi 140 (by decide) (by decide)
    (fun c ↦ decide (((pwuTable bSub hbLo hbHi cfg).aliasLf c).val % 2 = 1))
    (fun c ↦ decide (((pwuTable bSub hbLo hbHi cfg).primLf c).val % 2 = 1))

noncomputable def pwuStG0 (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 140 141 :=
  lockValWalker (pwuStG0Raw bSub hbLo hbHi cfg)

noncomputable def pwuStG1Raw (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 141 142 :=
  anfMux1Step bSub hbHi 141 (by decide) (by decide)
    (fun c ↦ decide ((((pwuTable bSub hbLo hbHi cfg).aliasLf c).val / 2) % 2 = 1))
    (fun c ↦ decide ((((pwuTable bSub hbLo hbHi cfg).primLf c).val / 2) % 2 = 1))

noncomputable def pwuStG1 (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 141 142 :=
  lockValWalker (pwuStG1Raw bSub hbLo hbHi cfg)

noncomputable def pwuBlockARaw (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 110 142 :=
  pwuSt0.append <| (pwuStMonom bSub hbHi).append <| (pwuStCmp bSub hbLo hbHi cfg).append <|
    (pwuStGL bSub hbLo hbHi cfg).append <|
      (pwuStG0 bSub hbLo hbHi cfg).append (pwuStG1 bSub hbLo hbHi cfg)

noncomputable def pwuBlockA (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 110 142 :=
  lockValWalker (pwuBlockARaw bSub hbLo hbHi cfg)

private theorem pwuStMonom_countAnd (bSub : ℕ) (hbHi : bSub ≤ 24) :
    (pwuStMonom bSub hbHi).countAnd = 3 := by
  rw [pwuStMonom, lockValWalker_eq]
  simp only [pwuStMonomRaw, pwuStMonom3Step, SsaProg.append_countAnd,
    andPol_countAnd, SsaProg.countAnd_cnot, SsaProg.countAnd_done]

private theorem pwuStCmp_countAnd (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : (pwuStCmp bSub hbLo hbHi cfg).countAnd = bSub := by
  rw [pwuStCmp, lockValWalker_eq]
  simp only [pwuStCmpRaw, SsaProg.append_countAnd, ssaCastEnd_countAnd, pwuThrCompare_countAnd,
    skipZeroN_countAnd, SsaProg.countAnd_cnot, SsaProg.countAnd_done]
  omega

private theorem pwuStGL_countAnd (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : (pwuStGL bSub hbLo hbHi cfg).countAnd = 1 := by
  rw [pwuStGL, lockValWalker_eq]; simp only [pwuStGLRaw, anfMux1Step_countAnd]

private theorem pwuStG0_countAnd (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : (pwuStG0 bSub hbLo hbHi cfg).countAnd = 1 := by
  rw [pwuStG0, lockValWalker_eq]; simp only [pwuStG0Raw, anfMux1Step_countAnd]

private theorem pwuStG1_countAnd (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : (pwuStG1 bSub hbLo hbHi cfg).countAnd = 1 := by
  rw [pwuStG1, lockValWalker_eq]; simp only [pwuStG1Raw, anfMux1Step_countAnd]

private theorem pwuSt0_eval : pwuSt0.eval = id := by
  funext γ; dsimp [pwuSt0, SsaProg.eval_skipZero, SsaProg.eval_done]

private theorem pwuStMonom3Step_spec (bSub : ℕ) (hbHi : bSub ≤ 24) :
    PreservesOutside 113 114 (pwuStMonom3Step bSub hbHi).eval ∧
    ∀ (γ : BitAssignment 185), γ ⟨113, by decide⟩ = 0 →
      (pwuStMonom3Step bSub hbHi).eval γ ⟨113, by decide⟩ =
        (γ ⟨30 + bSub, by omega⟩ + γ ⟨111, by decide⟩) *
          (γ ⟨31 + bSub, by omega⟩ + γ ⟨112, by decide⟩) := by
  let w0 : Wire 185 := ⟨30 + bSub, by omega⟩
  let w1 : Wire 185 := ⟨31 + bSub, by omega⟩
  let w111 : Wire 185 := ⟨111, by decide⟩
  let w112 : Wire 185 := ⟨112, by decide⟩
  let w113 : Wire 185 := ⟨113, by decide⟩
  have hne01 : w0 ≠ w1 := Fin.ne_of_val_ne (by dsimp [w0, w1]; omega)
  have hne0_111 : w0 ≠ w111 := Fin.ne_of_val_ne (by dsimp [w0, w111]; omega)
  have hne0_112 : w0 ≠ w112 := Fin.ne_of_val_ne (by dsimp [w0, w112]; omega)
  have hne0_113 : w0 ≠ w113 := Fin.ne_of_val_ne (by dsimp [w0, w113]; omega)
  have hne1_111 : w1 ≠ w111 := Fin.ne_of_val_ne (by dsimp [w1, w111]; omega)
  have hne1_112 : w1 ≠ w112 := Fin.ne_of_val_ne (by dsimp [w1, w112]; omega)
  have hne1_113 : w1 ≠ w113 := Fin.ne_of_val_ne (by dsimp [w1, w113]; omega)
  have hPA := andPol_preserves (M := 185) 113 (by decide) w0 w1 hne01
    (by dsimp [w0]; omega) (by dsimp [w1]; omega) false false
  refine ⟨fun γ w hw ↦ ?_, fun γ hz113 ↦ ?_⟩
  · dsimp only [pwuStMonom3Step]
    simp only [SsaProg.append_eval, SsaProg.eval_cnot, SsaProg.eval_done]
    let γ₁ := Function.update (Function.update γ w0 (γ w0 + γ w111)) w1
      (Function.update γ w0 (γ w0 + γ w111) w1 + Function.update γ w0 (γ w0 + γ w111) w112)
    let γ₂ := (andPol (M := 185) 113 (by decide) w0 w1 hne01
      (by dsimp [w0]; omega) (by dsimp [w1]; omega) false false).eval γ₁
    let γ₃ := Function.update γ₂ w1 (γ₂ w1 + γ₂ w112)
    change Function.update γ₃ w0 (γ₃ w0 + γ₃ w111) w = γ w
    have hγ₁_0 : γ₁ w0 = γ w0 + γ w111 := by
      dsimp only [γ₁]; rw [Function.update_of_ne hne01, Function.update_self]
    have hγ₁_1 : γ₁ w1 = γ w1 + γ w112 := by
      dsimp only [γ₁]
      rw [Function.update_self, Function.update_of_ne hne01.symm,
        Function.update_of_ne hne0_112.symm]
    have hγ₁_111 : γ₁ w111 = γ w111 := by
      dsimp only [γ₁]
      rw [Function.update_of_ne hne1_111.symm, Function.update_of_ne hne0_111.symm]
    have hγ₁_112 : γ₁ w112 = γ w112 := by
      dsimp only [γ₁]
      rw [Function.update_of_ne hne1_112.symm, Function.update_of_ne hne0_112.symm]
    have hγ₂_0 : γ₂ w0 = γ w0 + γ w111 :=
      (hPA γ₁ w0 (Or.inl (by dsimp [w0]; omega))).trans hγ₁_0
    have hγ₂_1 : γ₂ w1 = γ w1 + γ w112 :=
      (hPA γ₁ w1 (Or.inl (by dsimp [w1]; omega))).trans hγ₁_1
    have hγ₂_111 : γ₂ w111 = γ w111 :=
      (hPA γ₁ w111 (Or.inl (by decide))).trans hγ₁_111
    have hγ₂_112 : γ₂ w112 = γ w112 :=
      (hPA γ₁ w112 (Or.inl (by decide))).trans hγ₁_112
    by_cases hw0 : w = w0
    · subst hw0
      rw [Function.update_self]
      dsimp only [γ₃]
      rw [Function.update_of_ne hne01, Function.update_of_ne hne1_111.symm, hγ₂_0, hγ₂_111]
      exact zmod2_add_assoc_cancel _ _
    · rw [Function.update_of_ne hw0]
      by_cases hw1 : w = w1
      · subst hw1
        dsimp only [γ₃]
        rw [Function.update_self, hγ₂_1, hγ₂_112]
        exact zmod2_add_assoc_cancel _ _
      · dsimp only [γ₃, γ₂]
        rw [Function.update_of_ne hw1, hPA γ₁ w hw]
        dsimp only [γ₁]
        rw [Function.update_of_ne hw1, Function.update_of_ne hw0]
  · dsimp only [pwuStMonom3Step]
    simp only [SsaProg.append_eval, SsaProg.eval_cnot, SsaProg.eval_done]
    let γ₁ := Function.update (Function.update γ w0 (γ w0 + γ w111)) w1
      (Function.update γ w0 (γ w0 + γ w111) w1 + Function.update γ w0 (γ w0 + γ w111) w112)
    let γ₂ := (andPol (M := 185) 113 (by decide) w0 w1 hne01
      (by dsimp [w0]; omega) (by dsimp [w1]; omega) false false).eval γ₁
    let γ₃ := Function.update γ₂ w1 (γ₂ w1 + γ₂ w112)
    change Function.update γ₃ w0 (γ₃ w0 + γ₃ w111) w113 = _
    rw [Function.update_of_ne hne0_113.symm]
    dsimp only [γ₃]
    rw [Function.update_of_ne hne1_113.symm]
    have hz₁ : γ₁ w113 = 0 := by
      dsimp only [γ₁]
      rw [Function.update_of_ne hne1_113.symm, Function.update_of_ne hne0_113.symm, hz113]
    have hγ₁_0 : γ₁ w0 = γ w0 + γ w111 := by
      dsimp only [γ₁]; rw [Function.update_of_ne hne01, Function.update_self]
    have hγ₁_1 : γ₁ w1 = γ w1 + γ w112 := by
      dsimp only [γ₁]
      rw [Function.update_self, Function.update_of_ne hne01.symm,
        Function.update_of_ne hne0_112.symm]
    dsimp only [γ₂]
    rw [andPol_eval _ _ _ _ _ _ _ _ _ γ₁ hz₁, Function.update_self, hγ₁_0, hγ₁_1]
    dsimp only [w0, w1, w111, w112]
    simp [b2z]

private theorem pwuStMonom_spec (bSub : ℕ) (hbHi : bSub ≤ 24) :
    PreservesOutside 111 114 (pwuStMonom bSub hbHi).eval ∧
    ∀ (β : BitAssignment 185), (∀ w : Wire 185, 111 ≤ w.val → β w = 0) →
      (pwuStMonom bSub hbHi).eval β ⟨111, by decide⟩ =
        β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ ∧
      (pwuStMonom bSub hbHi).eval β ⟨112, by decide⟩ =
        β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ ∧
      (pwuStMonom bSub hbHi).eval β ⟨113, by decide⟩ =
        (β ⟨30 + bSub, by omega⟩ + β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩) *
          (β ⟨31 + bSub, by omega⟩ + β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩) := by
  have hP1 : PreservesOutside 111 112
      (andPol (M := 185) 111 (by decide) ⟨30 + bSub, by omega⟩ ⟨32 + bSub, by omega⟩
        (Fin.ne_of_val_ne (by dsimp; omega)) (by dsimp; omega) (by dsimp; omega) false false).eval
          :=
    andPol_preserves _ _ _ _ _ _ _ false false
  have hP2 : PreservesOutside 112 113
      (andPol (M := 185) 112 (by decide) ⟨31 + bSub, by omega⟩ ⟨32 + bSub, by omega⟩
        (Fin.ne_of_val_ne (by dsimp; omega)) (by dsimp; omega) (by dsimp; omega) false false).eval
          :=
    andPol_preserves _ _ _ _ _ _ _ false false
  obtain ⟨hP3, hV3⟩ := pwuStMonom3Step_spec bSub hbHi
  have hP12 := PreservesOutside.comp (by decide : 111 ≤ 112) (by decide : 112 ≤ 113) hP1 hP2
  have hP13 := PreservesOutside.comp (by decide : 111 ≤ 113) (by decide : 113 ≤ 114) hP12 hP3
  refine ⟨fun β w hw ↦ by
      rw [pwuStMonom, lockValWalker_eq, pwuStMonomRaw]
      simp only [SsaProg.append_eval]
      exact hP13 β w hw,
    fun β hz ↦ ?_⟩
  rw [pwuStMonom, lockValWalker_eq, pwuStMonomRaw]
  simp only [SsaProg.append_eval]
  let s1 := (andPol (M := 185) 111 (by decide) ⟨30 + bSub, by omega⟩ ⟨32 + bSub, by omega⟩
    (Fin.ne_of_val_ne (by dsimp; omega)) (by dsimp; omega) (by dsimp; omega) false false).eval β
  let s2 := (andPol (M := 185) 112 (by decide) ⟨31 + bSub, by omega⟩ ⟨32 + bSub, by omega⟩
    (Fin.ne_of_val_ne (by dsimp; omega)) (by dsimp; omega) (by dsimp; omega) false false).eval s1
  let s3 := (pwuStMonom3Step bSub hbHi).eval s2
  have hz2 : ∀ w : Wire 185, 112 ≤ w.val → s1 w = 0 := hP1.clean_above hz (by decide)
  have hz3 : ∀ w : Wire 185, 113 ≤ w.val → s2 w = 0 := hP2.clean_above hz2 (by decide)
  have hs1_lt : ∀ w : Wire 185, w.val < 111 → s1 w = β w := fun w hw ↦ hP1.keep_lt β w hw
  have hs2_lt : ∀ w : Wire 185, w.val < 112 → s2 w = s1 w := fun w hw ↦ hP2.keep_lt s1 w hw
  have hs3_lt : ∀ w : Wire 185, w.val < 113 → s3 w = s2 w := fun w hw ↦ hP3.keep_lt s2 w hw
  have hv1 : s1 ⟨111, by decide⟩ = β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ := by
    dsimp only [s1]; rw [andPol_eval _ _ _ _ _ _ _ _ _ β (hz _ le_rfl),
      Function.update_self]; simp [b2z]
  have hv2 : s2 ⟨112, by decide⟩ = β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ := by
    dsimp only [s2]
    rw [andPol_eval _ _ _ _ _ _ _ _ _ s1 (hz2 _ le_rfl), Function.update_self,
      hs1_lt ⟨31 + bSub, by omega⟩ (by dsimp; omega),
        hs1_lt ⟨32 + bSub, by omega⟩ (by dsimp; omega)]
    simp [b2z]
  have hv1_2 : s2 ⟨111, by decide⟩ = β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ :=
    (hs2_lt ⟨111, by decide⟩ (by decide)).trans hv1
  have hv3 : s3 ⟨113, by decide⟩ =
      (β ⟨30 + bSub, by omega⟩ + β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩) *
        (β ⟨31 + bSub, by omega⟩ + β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩) := by
    dsimp only [s3]
    rw [hV3 s2 (hz3 _ le_rfl), hv1_2, hv2,
      hs2_lt ⟨30 + bSub, by omega⟩ (by dsimp; omega),
        hs1_lt ⟨30 + bSub, by omega⟩ (by dsimp; omega),
      hs2_lt ⟨31 + bSub, by omega⟩ (by dsimp; omega),
        hs1_lt ⟨31 + bSub, by omega⟩ (by dsimp; omega)]
  exact ⟨(hs3_lt ⟨111, by decide⟩ (by decide)).trans hv1_2,
    (hs3_lt ⟨112, by decide⟩ (by decide)).trans hv2,
    hv3⟩

private theorem pwuStCmp_spec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤
    24) (cfg : Configuration) :
    PreservesOutside 114 139 (pwuStCmp bSub hbLo hbHi cfg).eval ∧
    ∀ (β : BitAssignment 185),
      β ⟨110, by decide⟩ = 0 →
      β ⟨111, by decide⟩ = β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ →
      β ⟨112, by decide⟩ = β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ →
      (∀ w : Wire 185, 114 ≤ w.val → β w = 0) →
      (pwuStCmp bSub hbLo hbHi cfg).eval β ⟨138, by decide⟩ =
        if sliceVal β 30 bSub (by omega) <
            (pwuTable bSub hbLo hbHi cfg).thr
              (colFromBits
                (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩))
        then 1 else 0 := by
  rw [pwuStCmp, lockValWalker_eq, pwuStCmpRaw]
  obtain ⟨hP, hV⟩ := pwuThrCompare_spec bSub hbHi (pwuTq bSub)
    (pwuT4 bSub hbLo hbHi cfg) (pwuT5 bSub hbLo hbHi cfg) (pwuT6 bSub hbLo hbHi cfg)
    (bSub - 1) (by omega)
  refine ⟨fun β w hw ↦ ?_, fun β hzt hm02 hm12 hz ↦ ?_⟩
  · simp only [SsaProg.append_eval, ssaCastEnd_eval, skipZeroN_eval, SsaProg.eval_cnot,
      SsaProg.eval_done]
    have hw_ne138 : w ≠ ⟨138, by decide⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    rw [Function.update_of_ne hw_ne138]
    exact hP β w (by cases hw with | inl h => exact Or.inl h | inr h => exact Or.inr (by omega))
  · simp only [SsaProg.append_eval, ssaCastEnd_eval, skipZeroN_eval, SsaProg.eval_cnot,
      SsaProg.eval_done]
    rw [Function.update_self]
    let β₁ := (pwuThrCompare bSub hbHi (pwuTq bSub)
      (pwuT4 bSub hbLo hbHi cfg) (pwuT5 bSub hbLo hbHi cfg) (pwuT6 bSub hbLo hbHi cfg)
      (bSub - 1) (by omega)).eval β
    have h138 : β₁ ⟨138, by decide⟩ = 0 :=
      (hP β ⟨138, by decide⟩ (Or.inr (by dsimp; omega))).trans (hz _ (by decide))
    change β₁ ⟨138, by decide⟩ + β₁ ⟨114 + (bSub - 1), by omega⟩ = _
    rw [h138, zero_add]
    have hs := hV β hzt hm02 hm12 hz
    dsimp only at hs
    have hsl_eq : sliceVal β 30 (bSub - 1 + 1) (by omega) = sliceVal β 30 bSub (by omega) :=
      sliceVal_cast_len β 30 (by omega) (by omega) (by omega)
    have hthr_eq :
        vec8 (pwuTq bSub) (pwuTq bSub) (pwuTq bSub) (pwuTq bSub)
          (pwuT4 bSub hbLo hbHi cfg) (pwuT5 bSub hbLo hbHi cfg) (pwuT6 bSub hbLo hbHi cfg)
          ((pwuT4 bSub hbLo hbHi cfg ^^^ pwuT5 bSub hbLo hbHi cfg) ^^^ pwuT6 bSub hbLo hbHi cfg)
          (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub,
            by omega⟩)) %
          2 ^ (bSub - 1 + 1) =
        (pwuTable bSub hbLo hbHi cfg).thr
          (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub,
            by omega⟩)) := by
      rw [← pwuTable_thr_eq_vec bSub hbLo hbHi cfg, show bSub - 1 + 1 = bSub by omega]
      exact Nat.mod_eq_of_lt (pwuTable_thr_lt bSub hbLo hbHi cfg _)
    exact hs.trans (by rw [hsl_eq, hthr_eq])

private abbrev PwuStGBitSpec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (cur : ℕ) (hcur : cur < 185)
    (p : SsaProg 185 cur (cur + 1)) (fLf : Fin 8 → Bool) : Prop :=
    PreservesOutside cur (cur + 1) p.eval ∧
    ∀ (β : BitAssignment 185),
      β ⟨110, by decide⟩ = 0 →
      β ⟨111, by decide⟩ = β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ →
      β ⟨112, by decide⟩ = β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩ →
      β ⟨113, by decide⟩ =
        (β ⟨30 + bSub, by omega⟩ + β ⟨30 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩) *
          (β ⟨31 + bSub, by omega⟩ + β ⟨31 + bSub, by omega⟩ * β ⟨32 + bSub, by omega⟩) →
      β ⟨cur, hcur⟩ = 0 →
      p.eval β ⟨cur, hcur⟩ =
        if β ⟨138, by decide⟩ = 1 then
          b2z (fLf ((pwuTable bSub hbLo hbHi cfg).primLf
            (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩)
              (β ⟨32 + bSub, by omega⟩))))
        else
          b2z (fLf ((pwuTable bSub hbLo hbHi cfg).aliasLf
            (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩)
              (β ⟨32 + bSub, by omega⟩))))

private theorem pwuStGBit_spec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (cur : ℕ) (hlo : 139 ≤ cur) (hcur : cur < 185)
    (p : SsaProg 185 cur (cur + 1)) (fLf : Fin 8 → Bool)
    (hp : let fA := fun c ↦ fLf ((pwuTable bSub hbLo hbHi cfg).aliasLf c)
      let fP := fun c ↦ fLf ((pwuTable bSub hbLo hbHi cfg).primLf c)
      p = lockValWalker (anfMux1Step bSub hbHi cur hlo hcur fA fP))
    (hA : let fA := fun c ↦ fLf ((pwuTable bSub hbLo hbHi cfg).aliasLf c)
      (fA 4 != fA 5) = (fA 6 != fA 7))
    (hP : let fP := fun c ↦ fLf ((pwuTable bSub hbLo hbHi cfg).primLf c)
      (fP 4 != fP 5) = (fP 6 != fP 7)) :
    PwuStGBitSpec bSub hbLo hbHi cfg cur hcur p fLf := by
  rw [hp, lockValWalker_eq]
  exact anfMux1Step_spec bSub hbHi cur hlo hcur _ _ hA hP

private theorem pwuStGL_spec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : PwuStGBitSpec bSub hbLo hbHi cfg 139 (by decide)
      (pwuStGL bSub hbLo hbHi cfg) (fun l ↦ decide (4 ≤ l.val)) :=
  pwuStGBit_spec bSub hbLo hbHi cfg 139 le_rfl (by decide) _ _ rfl
    (pwuTable_alias_topEven bSub hbLo hbHi cfg).even_gL
    (pwuTable_prim_topEven bSub hbLo hbHi cfg).even_gL

private theorem pwuStG0_spec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : PwuStGBitSpec bSub hbLo hbHi cfg 140 (by decide)
      (pwuStG0 bSub hbLo hbHi cfg) (fun l ↦ decide (l.val % 2 = 1)) :=
  pwuStGBit_spec bSub hbLo hbHi cfg 140 (by decide) (by decide) _ _ rfl
    (pwuTable_alias_topEven bSub hbLo hbHi cfg).even_g0
    (pwuTable_prim_topEven bSub hbLo hbHi cfg).even_g0

private theorem pwuStG1_spec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : PwuStGBitSpec bSub hbLo hbHi cfg 141 (by decide)
      (pwuStG1 bSub hbLo hbHi cfg) (fun l ↦ decide ((l.val / 2) % 2 = 1)) :=
  pwuStGBit_spec bSub hbLo hbHi cfg 141 (by decide) (by decide) _ _ rfl
    (pwuTable_alias_topEven bSub hbLo hbHi cfg).even_g1
    (pwuTable_prim_topEven bSub hbLo hbHi cfg).even_g1

private theorem ite_b2z_pwuLeafIdx (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (col : Fin 8) (vSub : ℕ) (p : Fin 8 → Bool) :
    (if vSub < (pwuTable bSub hbLo hbHi cfg).thr col then
      b2z (p ((pwuTable bSub hbLo hbHi cfg).primLf col))
    else
      b2z (p ((pwuTable bSub hbLo hbHi cfg).aliasLf col))) =
    b2z (p (pwuLeafIdx bSub hbLo hbHi cfg col vSub)) := by
  unfold pwuLeafIdx
  by_cases h : vSub < (pwuTable bSub hbLo hbHi cfg).thr col <;> simp [h]

attribute [local irreducible] pwuSt0 pwuStMonom pwuStCmp pwuStGL pwuStG0 pwuStG1

private theorem ite_cmp_zmod2 {α : Type*} (p : Prop) [Decidable p] (x y : α) :
    (if (if p then (1 : ZMod 2) else 0) = 1 then x else y) = if p then x else y := by
  by_cases hp : p <;> simp [hp]

section PWUBlockASpecIrred
attribute [local irreducible] pwuLeafIdx

private theorem pwuBlockA_spec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (β : BitAssignment 185)
    (hz : ∀ w : Wire 185, 110 ≤ w.val → β w = 0) :
    (∀ w : Wire 185, w.val < 110 → (pwuBlockA bSub hbLo hbHi cfg).eval β w = β w) ∧
    (∀ w : Wire 185, 142 ≤ w.val → (pwuBlockA bSub hbLo hbHi cfg).eval β w = 0) ∧
    (pwuBlockA bSub hbLo hbHi cfg).eval β ⟨139, by decide⟩ =
      b2z (decide (4 ≤ (pwuLeafIdx bSub hbLo hbHi cfg
        (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩))
        (sliceVal β 30 bSub (by omega))).val)) ∧
    (pwuBlockA bSub hbLo hbHi cfg).eval β ⟨140, by decide⟩ =
      b2z (decide ((pwuLeafIdx bSub hbLo hbHi cfg
        (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩))
        (sliceVal β 30 bSub (by omega))).val % 2 = 1)) ∧
    (pwuBlockA bSub hbLo hbHi cfg).eval β ⟨141, by decide⟩ =
      b2z (decide (((pwuLeafIdx bSub hbLo hbHi cfg
        (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩))
        (sliceVal β 30 bSub (by omega))).val / 2) % 2 = 1)) := by
  have hP0 : pwuSt0.eval = id := pwuSt0_eval
  have hdecomp : (pwuBlockA bSub hbLo hbHi cfg).eval β =
      (pwuStG1 bSub hbLo hbHi cfg).eval ((pwuStG0 bSub hbLo hbHi cfg).eval
        ((pwuStGL bSub hbLo hbHi cfg).eval
          ((pwuStCmp bSub hbLo hbHi cfg).eval ((pwuStMonom bSub hbHi).eval β)))) := by
    rw [pwuBlockA, lockValWalker_eq, pwuBlockARaw]
    simp only [SsaProg.append_eval, hP0, id_eq]
  rw [hdecomp]
  obtain ⟨col, hcol⟩ : ∃ x, x = colFromBits
    (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩) := ⟨_, rfl⟩
  obtain ⟨vSub, hvSub⟩ : ∃ x, x = sliceVal β 30 bSub (by omega) := ⟨_, rfl⟩
  rw [← hcol, ← hvSub]
  obtain ⟨lf, hlf⟩ : ∃ x, x = pwuLeafIdx bSub hbLo hbHi cfg col vSub := ⟨_, rfl⟩
  rw [← hlf]
  obtain ⟨β₁, hβ₁⟩ : ∃ x, x = (pwuStMonom bSub hbHi).eval β := ⟨_, rfl⟩
  rw [← hβ₁]
  obtain ⟨β₂, hβ₂⟩ : ∃ x, x = (pwuStCmp bSub hbLo hbHi cfg).eval β₁ := ⟨_, rfl⟩
  rw [← hβ₂]
  obtain ⟨β₃, hβ₃⟩ : ∃ x, x = (pwuStGL bSub hbLo hbHi cfg).eval β₂ := ⟨_, rfl⟩
  rw [← hβ₃]
  obtain ⟨β₄, hβ₄⟩ : ∃ x, x = (pwuStG0 bSub hbLo hbHi cfg).eval β₃ := ⟨_, rfl⟩
  rw [← hβ₄]
  obtain ⟨β₅, hβ₅⟩ : ∃ x, x = (pwuStG1 bSub hbLo hbHi cfg).eval β₄ := ⟨_, rfl⟩
  rw [← hβ₅]
  obtain ⟨hPM, hVM⟩ := pwuStMonom_spec bSub hbHi
  obtain ⟨hPC, hVC⟩ := pwuStCmp_spec bSub hbLo hbHi cfg
  obtain ⟨hPL, hVL⟩ := pwuStGL_spec bSub hbLo hbHi cfg
  obtain ⟨hP0m, hV0m⟩ := pwuStG0_spec bSub hbLo hbHi cfg
  obtain ⟨hP1m, hV1m⟩ := pwuStG1_spec bSub hbLo hbHi cfg
  have hz111 : ∀ w : Wire 185, 111 ≤ w.val → β w = 0 := fun w hw ↦ hz w (by omega)
  have hz1 : ∀ w : Wire 185, 114 ≤ w.val → β₁ w = 0 := by
    rw [hβ₁]; exact hPM.clean_above hz111 (by decide)
  have hz2 : ∀ w : Wire 185, 139 ≤ w.val → β₂ w = 0 := by
    rw [hβ₂]; exact hPC.clean_above hz1 (by decide)
  have hz3 : ∀ w : Wire 185, 140 ≤ w.val → β₃ w = 0 := by
    rw [hβ₃]; exact hPL.clean_above hz2 (by decide)
  have hz4 : ∀ w : Wire 185, 141 ≤ w.val → β₄ w = 0 := by
    rw [hβ₄]; exact hP0m.clean_above hz3 (by decide)
  have hz5 : ∀ w : Wire 185, 142 ≤ w.val → β₅ w = 0 := by
    rw [hβ₅]; exact hP1m.clean_above hz4 (by decide)
  obtain ⟨hm02_1, hm12_1, hm01e_1⟩ := hVM β hz111
  rw [← hβ₁] at hm02_1 hm12_1 hm01e_1
  have hk1_lt : ∀ w : Wire 185, w.val < 111 → β₁ w = β w := fun w hw ↦ by
    rw [hβ₁]; exact hPM.keep_lt β w hw
  have hk2_lt : ∀ w : Wire 185, w.val < 114 → β₂ w = β₁ w := fun w hw ↦ by
    rw [hβ₂]; exact hPC.keep_lt β₁ w hw
  have hk3_lt : ∀ w : Wire 185, w.val < 139 → β₃ w = β₂ w := fun w hw ↦ by
    rw [hβ₃]; exact hPL.keep_lt β₂ w hw
  have hk4_lt : ∀ w : Wire 185, w.val < 140 → β₄ w = β₃ w := fun w hw ↦ by
    rw [hβ₄]; exact hP0m.keep_lt β₃ w hw
  have hk5_lt : ∀ w : Wire 185, w.val < 141 → β₅ w = β₄ w := fun w hw ↦ by
    rw [hβ₅]; exact hP1m.keep_lt β₄ w hw
  have h110_1 : β₁ ⟨110, by decide⟩ = 0 := (hk1_lt _ (by decide)).trans (hz _ le_rfl)
  have hi0_1 : β₁ ⟨30 + bSub, by omega⟩ = β ⟨30 + bSub, by omega⟩ := hk1_lt _ (by dsimp; omega)
  have hi1_1 : β₁ ⟨31 + bSub, by omega⟩ = β ⟨31 + bSub, by omega⟩ := hk1_lt _ (by dsimp; omega)
  have hi2_1 : β₁ ⟨32 + bSub, by omega⟩ = β ⟨32 + bSub, by omega⟩ := hk1_lt _ (by dsimp; omega)
  have hvSub_1 : sliceVal β₁ 30 bSub (by omega) = vSub := by
    rw [hvSub]
    exact sliceVal_congr bSub (by omega) fun j _ ↦ hk1_lt _ (by dsimp; omega)
  have hcmp_2 : β₂ ⟨138,
    by decide⟩ = if vSub < (pwuTable bSub hbLo hbHi cfg).thr col then 1 else 0 := by
    rw [hβ₂]
    have hc := hVC β₁ h110_1 (by rw [hm02_1, hi0_1, hi2_1]) (by rw [hm12_1, hi1_1, hi2_1]) hz1
    rw [hi0_1, hi1_1, hi2_1, ← hcol, hvSub_1] at hc
    exact hc
  have hlow2 : ∀ w : Wire 185, w.val < 111 → β₂ w = β w :=
    fun w hw ↦ (hk2_lt w (by omega)).trans (hk1_lt w hw)
  have hlow3 : ∀ w : Wire 185, w.val < 114 → β₃ w = β₂ w :=
    fun w hw ↦ hk3_lt w (by omega)
  have hlow4 : ∀ w : Wire 185, w.val < 114 → β₄ w = β₂ w :=
    fun w hw ↦ (hk4_lt w (by omega)).trans (hlow3 w hw)
  have h110_2 : β₂ ⟨110, by decide⟩ = 0 := (hlow2 _ (by decide)).trans (hz _ le_rfl)
  have hm02_2 : β₂ ⟨111, by decide⟩ = β₂ ⟨30 + bSub, by omega⟩ * β₂ ⟨32 + bSub, by omega⟩ := by
    rw [hk2_lt _ (by decide), hm02_1, hlow2 _ (by dsimp; omega), hlow2 _ (by dsimp; omega)]
  have hm12_2 : β₂ ⟨112, by decide⟩ = β₂ ⟨31 + bSub, by omega⟩ * β₂ ⟨32 + bSub, by omega⟩ := by
    rw [hk2_lt _ (by decide), hm12_1, hlow2 _ (by dsimp; omega), hlow2 _ (by dsimp; omega)]
  have hm01e_2 : β₂ ⟨113, by decide⟩ =
      (β₂ ⟨30 + bSub, by omega⟩ + β₂ ⟨30 + bSub, by omega⟩ * β₂ ⟨32 + bSub, by omega⟩) *
        (β₂ ⟨31 + bSub, by omega⟩ + β₂ ⟨31 + bSub, by omega⟩ * β₂ ⟨32 + bSub, by omega⟩) := by
    rw [hk2_lt _ (by decide), hm01e_1, hlow2 _ (by dsimp; omega),
      hlow2 _ (by dsimp; omega), hlow2 _ (by dsimp; omega)]
  have hcol2 : colFromBits
      (β₂ ⟨30 + bSub, by omega⟩) (β₂ ⟨31 + bSub, by omega⟩) (β₂ ⟨32 + bSub, by omega⟩) = col := by
    rw [hcol, hlow2 _ (by dsimp; omega), hlow2 _ (by dsimp; omega), hlow2 _ (by dsimp; omega)]
  have hgL_3 : β₃ ⟨139, by decide⟩ = b2z (decide (4 ≤ lf.val)) := by
    rw [hβ₃, hVL β₂ h110_2 hm02_2 hm12_2 hm01e_2 (hz2 _ le_rfl),
      hcol2, hcmp_2, ite_cmp_zmod2, hlf]
    exact ite_b2z_pwuLeafIdx bSub hbLo hbHi cfg col vSub (fun x ↦ decide (4 ≤ x.val))
  have hg0_4 : β₄ ⟨140, by decide⟩ = b2z (decide (lf.val % 2 = 1)) := by
    have h110_3 : β₃ ⟨110, by decide⟩ = 0 := (hlow3 _ (by decide)).trans h110_2
    have hm02_3 : β₃ ⟨111, by decide⟩ = β₃ ⟨30 + bSub, by omega⟩ * β₃ ⟨32 + bSub, by omega⟩ := by
      rw [hlow3 _ (by decide), hlow3 _ (by dsimp; omega), hlow3 _ (by dsimp; omega), hm02_2]
    have hm12_3 : β₃ ⟨112, by decide⟩ = β₃ ⟨31 + bSub, by omega⟩ * β₃ ⟨32 + bSub, by omega⟩ := by
      rw [hlow3 _ (by decide), hlow3 _ (by dsimp; omega), hlow3 _ (by dsimp; omega), hm12_2]
    have hm01e_3 : β₃ ⟨113, by decide⟩ =
        (β₃ ⟨30 + bSub, by omega⟩ + β₃ ⟨30 + bSub, by omega⟩ * β₃ ⟨32 + bSub, by omega⟩) *
          (β₃ ⟨31 + bSub, by omega⟩ + β₃ ⟨31 + bSub, by omega⟩ * β₃ ⟨32 + bSub, by omega⟩) := by
      rw [hlow3 _ (by decide), hlow3 _ (by dsimp; omega), hlow3 _ (by dsimp; omega),
        hlow3 _ (by dsimp; omega), hm01e_2]
    rw [hβ₄, hV0m β₃ h110_3 hm02_3 hm12_3 hm01e_3 (hz3 _ le_rfl),
      hlow3 ⟨30 + bSub, by omega⟩ (by dsimp; omega),
      hlow3 ⟨31 + bSub, by omega⟩ (by dsimp; omega),
      hlow3 ⟨32 + bSub, by omega⟩ (by dsimp; omega), hcol2,
      hk3_lt ⟨138, by decide⟩ (by decide), hcmp_2, ite_cmp_zmod2, hlf]
    exact ite_b2z_pwuLeafIdx bSub hbLo hbHi cfg col vSub (fun x ↦ decide (x.val % 2 = 1))
  have hg1_5 : β₅ ⟨141, by decide⟩ = b2z (decide ((lf.val / 2) % 2 = 1)) := by
    have h110_4 : β₄ ⟨110, by decide⟩ = 0 := (hlow4 _ (by decide)).trans h110_2
    have hm02_4 : β₄ ⟨111, by decide⟩ = β₄ ⟨30 + bSub, by omega⟩ * β₄ ⟨32 + bSub, by omega⟩ := by
      rw [hlow4 _ (by decide), hlow4 _ (by dsimp; omega), hlow4 _ (by dsimp; omega), hm02_2]
    have hm12_4 : β₄ ⟨112, by decide⟩ = β₄ ⟨31 + bSub, by omega⟩ * β₄ ⟨32 + bSub, by omega⟩ := by
      rw [hlow4 _ (by decide), hlow4 _ (by dsimp; omega), hlow4 _ (by dsimp; omega), hm12_2]
    have hm01e_4 : β₄ ⟨113, by decide⟩ =
        (β₄ ⟨30 + bSub, by omega⟩ + β₄ ⟨30 + bSub, by omega⟩ * β₄ ⟨32 + bSub, by omega⟩) *
          (β₄ ⟨31 + bSub, by omega⟩ + β₄ ⟨31 + bSub, by omega⟩ * β₄ ⟨32 + bSub, by omega⟩) := by
      rw [hlow4 _ (by decide), hlow4 _ (by dsimp; omega), hlow4 _ (by dsimp; omega),
        hlow4 _ (by dsimp; omega), hm01e_2]
    rw [hβ₅, hV1m β₄ h110_4 hm02_4 hm12_4 hm01e_4 (hz4 _ le_rfl),
      hlow4 ⟨30 + bSub, by omega⟩ (by dsimp; omega),
      hlow4 ⟨31 + bSub, by omega⟩ (by dsimp; omega),
      hlow4 ⟨32 + bSub, by omega⟩ (by dsimp; omega), hcol2,
      hk4_lt ⟨138, by decide⟩ (by decide), hk3_lt ⟨138, by decide⟩ (by decide),
      hcmp_2, ite_cmp_zmod2, hlf]
    exact ite_b2z_pwuLeafIdx bSub hbLo hbHi cfg col vSub (fun x ↦ decide ((x.val / 2) % 2 = 1))
  refine ⟨fun w hw ↦ (hk5_lt w (by omega)).trans ((hlow4 w (by omega)).trans (hlow2 w (by omega))),
    hz5, ?_, ?_, hg1_5⟩
  · exact (hk5_lt _ (by decide)).trans ((hk4_lt _ (by decide)).trans hgL_3)
  · exact (hk5_lt _ (by decide)).trans hg0_4

end PWUBlockASpecIrred


attribute [local irreducible] pwuBlockA
private theorem pwuBlockA_countAnd (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : (pwuBlockA bSub hbLo hbHi cfg).countAnd = bSub + 6 := by
  rw [pwuBlockA, lockValWalker_eq, pwuBlockARaw]
  simp only [pwuSt0, SsaProg.append_countAnd, SsaProg.countAnd_done, SsaProg.countAnd_skipZero,
    pwuStMonom_countAnd, pwuStCmp_countAnd, pwuStGL_countAnd, pwuStG0_countAnd, pwuStG1_countAnd]
  omega

def pwuStPadSplit : SsaProg 185 142 143 :=
  (andPol (M := 185) 142 (by decide) ⟨141, by decide⟩ ⟨140, by decide⟩
    (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) false false).append <|
    .cnot ⟨142, by decide⟩ ⟨140,
      by decide⟩ (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) (.done 143)

private theorem pwuStPadSplit_countAnd : pwuStPadSplit.countAnd = 1 := by
  simp only [pwuStPadSplit, SsaProg.append_countAnd, andPol_countAnd,
    SsaProg.countAnd_cnot, SsaProg.countAnd_done]

private theorem pwuStPadSplit_eval (γ : BitAssignment 185) (hz : ∀ w : Wire 185,
    142 ≤ w.val → γ w = 0) :
    (∀ w : Wire 185, w.val < 140 → pwuStPadSplit.eval γ w = γ w) ∧
    (∀ w : Wire 185, 143 ≤ w.val → pwuStPadSplit.eval γ w = 0) ∧
    pwuStPadSplit.eval γ ⟨140, by decide⟩ = γ ⟨140, by decide⟩ + γ ⟨141, by decide⟩ * γ ⟨140,
      by decide⟩ ∧
    pwuStPadSplit.eval γ ⟨141, by decide⟩ = γ ⟨141, by decide⟩ ∧
    pwuStPadSplit.eval γ ⟨142, by decide⟩ = γ ⟨141, by decide⟩ * γ ⟨140, by decide⟩ := by
  dsimp only [pwuStPadSplit]
  simp only [SsaProg.append_eval, SsaProg.eval_cnot, SsaProg.eval_done]
  rw [andPol_eval _ _ _ _ _ _ _ _ _ γ (hz ⟨142, by decide⟩ le_rfl)]
  have h140_ne_142 : (⟨140, by decide⟩ : Wire 185) ≠ ⟨142, by decide⟩ :=
    Fin.ne_of_val_ne (by decide)
  have h141_ne_140 : (⟨141, by decide⟩ : Wire 185) ≠ ⟨140, by decide⟩ :=
    Fin.ne_of_val_ne (by decide)
  have h141_ne_142 : (⟨141, by decide⟩ : Wire 185) ≠ ⟨142, by decide⟩ :=
    Fin.ne_of_val_ne (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hw140 : w ≠ ⟨140, by decide⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    have hw142 : w ≠ ⟨142, by decide⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    rw [Function.update_of_ne hw140, Function.update_of_ne hw142]
  · intro w hw
    have hw140 : w ≠ ⟨140, by decide⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    have hw142 : w ≠ ⟨142, by decide⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    rw [Function.update_of_ne hw140, Function.update_of_ne hw142]
    exact hz w (by omega)
  · simp only [Function.update_self, Function.update_of_ne h140_ne_142, b2z, Bool.false_eq_true,
      ↓reduceIte]; ring
  · rw [Function.update_of_ne h141_ne_140, Function.update_of_ne h141_ne_142]
  · simp only [Function.update_of_ne h140_ne_142.symm, Function.update_self, b2z,
      Bool.false_eq_true, ↓reduceIte]; ring

noncomputable def pwuOuterSsaRaw (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 110 143 :=
  (pwuBlockA bSub hbLo hbHi cfg).append pwuStPadSplit

noncomputable def pwuOuterSsa (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 110 143 :=
  lockValWalker (pwuOuterSsaRaw bSub hbLo hbHi cfg)

private theorem pwuOuterSsa_countAnd (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : (pwuOuterSsa bSub hbLo hbHi cfg).countAnd = bSub + 7 := by
  rw [pwuOuterSsa, lockValWalker_eq, pwuOuterSsaRaw]
  simp only [SsaProg.append_countAnd, pwuBlockA_countAnd, pwuStPadSplit_countAnd]

private theorem pwuOuterSsa_spec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (β : BitAssignment 185)
    (hz : ∀ w : Wire 185, 110 ≤ w.val → β w = 0) :
    let lf := pwuLeafIdx bSub hbLo hbHi cfg
      (colFromBits (β ⟨30 + bSub, by omega⟩) (β ⟨31 + bSub, by omega⟩) (β ⟨32 + bSub, by omega⟩))
      (sliceVal β 30 bSub (by omega))
    let g0 := b2z (decide (lf.val % 2 = 1))
    let g1 := b2z (decide ((lf.val / 2) % 2 = 1))
    (∀ w : Wire 185, w.val < 110 → (pwuOuterSsa bSub hbLo hbHi cfg).eval β w = β w) ∧
    (∀ w : Wire 185, 143 ≤ w.val → (pwuOuterSsa bSub hbLo hbHi cfg).eval β w = 0) ∧
    (pwuOuterSsa bSub hbLo hbHi cfg).eval β ⟨139, by decide⟩ = b2z (decide (4 ≤ lf.val)) ∧
    (pwuOuterSsa bSub hbLo hbHi cfg).eval β ⟨140, by decide⟩ = g0 + g1 * g0 ∧
    (pwuOuterSsa bSub hbLo hbHi cfg).eval β ⟨141, by decide⟩ = g1 ∧
    (pwuOuterSsa bSub hbLo hbHi cfg).eval β ⟨142, by decide⟩ = g1 * g0 := by
  intro lf g0 g1
  have hdecomp : (pwuOuterSsa bSub hbLo hbHi cfg).eval β =
      pwuStPadSplit.eval ((pwuBlockA bSub hbLo hbHi cfg).eval β) := by
    rw [pwuOuterSsa, lockValWalker_eq, pwuOuterSsaRaw, SsaProg.append_eval]
  rw [hdecomp]
  obtain ⟨hkeepA, hzA, hgLA, hg0A, hg1A⟩ := pwuBlockA_spec bSub hbLo hbHi cfg β hz
  obtain ⟨hkS, hzS, h140S, h141S, h142S⟩ :=
    pwuStPadSplit_eval ((pwuBlockA bSub hbLo hbHi cfg).eval β) hzA
  refine ⟨fun w hw ↦ (hkS w (by omega)).trans (hkeepA w hw), hzS, ?_, ?_, ?_, ?_⟩
  · exact (hkS ⟨139, by decide⟩ (by decide)).trans hgLA
  · rw [h140S, hg0A, hg1A]
  · rw [h141S, hg1A]
  · rw [h142S, hg1A, hg0A]

attribute [local irreducible] pwuStPadSplit pwuOuterSsa

def pwuSt9 : SsaProg 185 151 157 :=
  twosCarryChainG (M := 185) 143 151 (by decide) 5 (by decide) (by decide)

def pwuSt10 : SsaProg 185 157 157 :=
  inplaceMag7G (M := 185) 143 151 157 (by decide) (by decide) (by decide) 6 (by decide)

def pwuBlockBMag7Raw : SsaProg 185 151 157 :=
  pwuSt9.append pwuSt10

noncomputable def pwuBlockBMag7 : SsaProg 185 151 157 :=
  lockValWalker pwuBlockBMag7Raw

def wMag7PWU (b : Fin 7) : Wire 185 :=
  ⟨143 + b.val, by have := b.isLt; omega⟩

theorem wMag7PWU_lt_157 (b : Fin 7) : (wMag7PWU b).val < 157 := by
  have := b.isLt; dsimp [wMag7PWU]; omega

theorem wMag7PWU_ge_143 (b : Fin 7) : 143 ≤ (wMag7PWU b).val := by
  dsimp [wMag7PWU]; omega

private theorem pwuBlockBMag7_spec (u8 : Fin 8 → ZMod 2) (β : BitAssignment 185)
    (hz : ∀ w : Wire 185, 151 ≤ w.val → β w = 0)
    (hu8 : ∀ b : Fin 8, β ⟨143 + b.val, by omega⟩ = u8 b) :
    (∀ w : Wire 185, w.val < 143 → pwuBlockBMag7.eval β w = β w) ∧
    (∀ w : Wire 185, 157 ≤ w.val → pwuBlockBMag7.eval β w = 0) ∧
    pwuBlockBMag7.eval β ⟨150, by decide⟩ = u8 7 ∧
    (∀ b : Fin 7, pwuBlockBMag7.eval β (wMag7PWU b) = mag7Bit u8 b) := by
  have hdecomp : pwuBlockBMag7.eval β = pwuSt10.eval (pwuSt9.eval β) := by
    rw [pwuBlockBMag7, lockValWalker_eq, pwuBlockBMag7Raw, SsaProg.append_eval]
  rw [hdecomp]
  obtain ⟨β₃, hβ₃⟩ : ∃ x, x = pwuSt9.eval β := ⟨_, rfl⟩
  rw [← hβ₃]
  obtain ⟨β₄, hβ₄⟩ : ∃ x, x = pwuSt10.eval β₃ := ⟨_, rfl⟩
  rw [← hβ₄]
  obtain ⟨hP9, hV9⟩ := twosCarryChainG_spec (M := 185) 143 151 (by decide) 5 (by decide) (by decide)
  have hz9 : ∀ w : Wire 185, 157 ≤ w.val → β₃ w = 0 := by
    rw [hβ₃]; exact hP9.clean_above hz (by decide)
  have h10 :=
    inplaceMag7G_spec (M := 185) 143 151 157 (by decide) (by decide) (by decide) 6 (by decide) β₃
  have hkeep143 : ∀ w : Wire 185, w.val < 143 → β₄ w = β w := fun w hw ↦ by
    rw [hβ₄]; dsimp only [pwuSt10]
    rw [h10 w, MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega), hβ₃]
    dsimp only [pwuSt9]
    exact hP9.keep_lt β w (by omega)
  have hz10 : ∀ w : Wire 185, 157 ≤ w.val → β₄ w = 0 := fun w hw ↦ by
    rw [hβ₄]; dsimp only [pwuSt10]
    rw [h10 w, MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega)]
    exact hz9 w hw
  have h150_3 : β₃ ⟨150, by decide⟩ = u8 7 := by
    rw [hβ₃]; dsimp only [pwuSt9]
    exact (hP9.keep_lt β ⟨150, by decide⟩ (by decide)).trans (hu8 7)
  have h150_4 : β₄ ⟨150, by decide⟩ = u8 7 := by
    rw [hβ₄]; dsimp only [pwuSt10]
    rw [h10 ⟨150, by decide⟩, MomSlots01Slot1ProjKinetic.dite_neg_s1 (by decide)]
    exact h150_3
  refine ⟨hkeep143, hz10, h150_4, fun b ↦ ?_⟩
  rw [hβ₄]; dsimp only [pwuSt10]
  rw [h10 (wMag7PWU b)]
  by_cases hb0 : b.val = 0
  · have hn : ¬(143 + 1 ≤ (wMag7PWU b).val ∧ (wMag7PWU b).val < 143 + 1 + 6) := by
      dsimp [wMag7PWU]; omega
    rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 hn, hβ₃]; dsimp only [pwuSt9]
    rw [hP9.keep_lt β _ (by dsimp [wMag7PWU]; omega)]
    have hw0 : wMag7PWU b = ⟨143 + (0 : Fin 8).val, by decide⟩ := by
      ext; dsimp [wMag7PWU]; omega
    have hm0 : mag7Bit u8 b = u8 0 := by unfold mag7Bit; simp [hb0]
    rw [hw0, hm0]
    exact hu8 0
  · have hp : 143 + 1 ≤ (wMag7PWU b).val ∧ (wMag7PWU b).val < 143 + 1 + 6 := by
      have := b.isLt; dsimp [wMag7PWU]; omega
    rw [MomSlots01Slot1ProjKinetic.dite_pos_s1 hp, h150_3]
    have hu_b : β₃ (wMag7PWU b) = u8 ⟨b.val, by have := b.isLt; omega⟩ := by
      rw [hβ₃]; dsimp only [pwuSt9]
      rw [hP9.keep_lt β _ (by have := b.isLt; dsimp [wMag7PWU]; omega)]
      exact hu8 ⟨b.val, by have := b.isLt; omega⟩
    have hc_b : β₃ ⟨151 + ((wMag7PWU b).val - (143 + 1)), by omega⟩ = carryBool u8 b.val := by
      have hidx : (⟨151 + ((wMag7PWU b).val - (143 + 1)), by omega⟩ : Wire 185) =
          ⟨151 + (b.val - 1), by have := b.isLt; omega⟩ := Fin.ext (by dsimp [wMag7PWU]; omega)
      rw [hidx, hβ₃]; dsimp only [pwuSt9]
      have hc := hV9 β hz (b.val - 1) (by have := b.isLt; omega)
      have hfun : (fun b' : Fin 8 ↦ β ⟨143 + b'.val, by omega⟩) = u8 := funext hu8
      have hkb : b.val - 1 + 1 = b.val := by omega
      rw [hfun, hkb] at hc
      exact hc
    rw [hu_b, hc_b]
    unfold mag7Bit
    rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hb0]

attribute [local irreducible] pwuSt9 pwuSt10 pwuBlockBMag7

def pwuChainEval7 (b0 : ZMod 2) (u8 : Fin 8 → ZMod 2) (α : BitAssignment 7) : ZMod 2 :=
  prioStarEval b0 (fun t ↦ mag7Bit u8 ⟨t % 7, Nat.mod_lt _ (by decide)⟩) 7 α

def pwuChainEval14 (b0 : ZMod 2) (u8 : Fin 8 → ZMod 2) (α : BitAssignment 14) : ZMod 2 :=
  prioStarEval b0 (fun t ↦ mag7Bit u8 ⟨t % 7, Nat.mod_lt _ (by decide)⟩) 14 α

def pwuSt11a (bSub : ℕ) (hbHi : bSub ≤ 24) : SsaProg 185 157 158 :=
  andPol (M := 185) 157 (by decide) ⟨47 + bSub, by omega⟩ (wMag7PWU 0)
    (Fin.ne_of_val_ne (by dsimp [wMag7PWU]; omega))
    (by dsimp; omega) (wMag7PWU_lt_157 0) false false

def pwuSt11b (bSub : ℕ) (hbHi : bSub ≤ 24) : SsaProg 185 158 164 :=
  prioChainStar (M := 185) (48 + bSub) 158
    ⟨157, by decide⟩
    (fun t ↦ wMag7PWU ⟨(t + 1) % 7, Nat.mod_lt _ (by decide)⟩)
    (by decide)
    (fun t _ ↦ lt_trans (wMag7PWU_lt_157 _) (by decide))
    (by omega)
    (fun t _ ↦ by have := wMag7PWU_ge_143 ⟨(t + 1) % 7, Nat.mod_lt _ (by decide)⟩; omega)
    (Fin.ne_of_val_ne (by dsimp [wMag7PWU]; decide))
    5 (by decide) (by decide)

def pwuSt12b (bSub : ℕ) (hbHi : bSub ≤ 24) : SsaProg 185 165 179 :=
  prioChainStar (M := 185) (33 + bSub) 165
    ⟨164, by decide⟩
    (fun t ↦ wMag7PWU ⟨t % 7, Nat.mod_lt _ (by decide)⟩)
    (by decide)
    (fun t _ ↦ lt_trans (wMag7PWU_lt_157 _) (by decide))
    (by omega)
    (fun t _ ↦ by have := wMag7PWU_ge_143 ⟨t % 7, Nat.mod_lt _ (by decide)⟩; omega)
    (Fin.ne_of_val_ne (by dsimp [wMag7PWU]; decide))
    13 (by decide) (by decide)

private theorem pwuBlockCPrioGen_spec (bSub : ℕ) (hbHi : bSub ≤ 24)
    (st12a : SsaProg 185 164 165) (blk : SsaProg 185 157 179)
    (seedFn : ZMod 2 → ZMod 2 → ZMod 2)
    (hblk : blk = lockValWalker ((pwuSt11a bSub hbHi).append <|
      (pwuSt11b bSub hbHi).append <| st12a.append (pwuSt12b bSub hbHi)))
    (hP12a : PreservesOutside 164 165 st12a.eval)
    (hV12a : ∀ γ : BitAssignment 185, γ ⟨164, by decide⟩ = 0 → st12a.eval γ
      ⟨164, by decide⟩ = seedFn (γ ⟨139, by decide⟩) (γ ⟨163, by decide⟩))
    (u8 : Fin 8 → ZMod 2)
    (β : BitAssignment 185)
    (hz : ∀ w : Wire 185, 157 ≤ w.val → β w = 0)
    (hmag : ∀ b : Fin 7, β (wMag7PWU b) = mag7Bit u8 b) :
    let outS := pwuChainEval7 0 u8 (fun i : Fin 7 ↦ β ⟨47 + bSub + i.val, by omega⟩)
    (∀ w : Wire 185, w.val < 157 → blk.eval β w = β w) ∧
    (∀ w : Wire 185, 179 ≤ w.val → blk.eval β w = 0) ∧
    blk.eval β ⟨163, by decide⟩ = outS ∧
    blk.eval β ⟨178, by decide⟩ =
      pwuChainEval14 (seedFn (β ⟨139, by decide⟩) outS) u8
        (fun i : Fin 14 ↦ β ⟨33 + bSub + i.val, by omega⟩) := by
  intro outS
  have hdecomp : blk.eval β =
      (pwuSt12b bSub hbHi).eval (st12a.eval ((pwuSt11b bSub hbHi).eval
        ((pwuSt11a bSub hbHi).eval β))) := by
    rw [hblk, lockValWalker_eq]
    simp only [SsaProg.append_eval]
  rw [hdecomp]
  obtain ⟨β₁, hβ₁⟩ : ∃ x, x = (pwuSt11a bSub hbHi).eval β := ⟨_, rfl⟩
  rw [← hβ₁]
  obtain ⟨β₂, hβ₂⟩ : ∃ x, x = (pwuSt11b bSub hbHi).eval β₁ := ⟨_, rfl⟩
  rw [← hβ₂]
  obtain ⟨β₃, hβ₃⟩ : ∃ x, x = st12a.eval β₂ := ⟨_, rfl⟩
  rw [← hβ₃]
  obtain ⟨β₄, hβ₄⟩ : ∃ x, x = (pwuSt12b bSub hbHi).eval β₃ := ⟨_, rfl⟩
  rw [← hβ₄]
  have hP11a : PreservesOutside 157 158 (pwuSt11a bSub hbHi).eval :=
    andPol_preserves 157 (by decide) _ _ _ _ _ false false
  have hz1 : ∀ w : Wire 185, 158 ≤ w.val → β₁ w = 0 := by
    rw [hβ₁]; exact hP11a.clean_above hz (by decide)
  obtain ⟨hP11b, hV11b⟩ := prioChainStar_spec (M := 185) (48 + bSub) 158
    ⟨157, by decide⟩
    (fun t ↦ wMag7PWU ⟨(t + 1) % 7, Nat.mod_lt _ (by decide)⟩)
    (by decide)
    (fun t _ ↦ lt_trans (wMag7PWU_lt_157 _) (by decide))
    (by omega)
    (fun t _ ↦ by have := wMag7PWU_ge_143 ⟨(t + 1) % 7, Nat.mod_lt _ (by decide)⟩; omega)
    (Fin.ne_of_val_ne (by dsimp [wMag7PWU]; decide))
    5 (by decide) (by decide)
  have hz2 : ∀ w : Wire 185, 164 ≤ w.val → β₂ w = 0 := by
    rw [hβ₂]; dsimp only [pwuSt11b]; exact hP11b.clean_above hz1 (by decide)
  have hz3 : ∀ w : Wire 185, 165 ≤ w.val → β₃ w = 0 := by
    rw [hβ₃]; exact hP12a.clean_above hz2 (by decide)
  obtain ⟨hP12b, hV12b⟩ := prioChainStar_spec (M := 185) (33 + bSub) 165
    ⟨164, by decide⟩
    (fun t ↦ wMag7PWU ⟨t % 7, Nat.mod_lt _ (by decide)⟩)
    (by decide)
    (fun t _ ↦ lt_trans (wMag7PWU_lt_157 _) (by decide))
    (by omega)
    (fun t _ ↦ by have := wMag7PWU_ge_143 ⟨t % 7, Nat.mod_lt _ (by decide)⟩; omega)
    (Fin.ne_of_val_ne (by dsimp [wMag7PWU]; decide))
    13 (by decide) (by decide)
  have hz4 : ∀ w : Wire 185, 179 ≤ w.val → β₄ w = 0 := by
    rw [hβ₄]; dsimp only [pwuSt12b]; exact hP12b.clean_above hz3 (by decide)
  have h157_1 : β₁ ⟨157, by decide⟩ = β ⟨47 + bSub, by omega⟩ * mag7Bit u8 0 := by
    rw [hβ₁]; dsimp only [pwuSt11a]
    rw [andPol_eval _ _ _ _ _ _ _ _ _ β (hz _ le_rfl), Function.update_self, hmag 0]
    simp [b2z]
  have hmag1 : ∀ b : Fin 7, β₁ (wMag7PWU b) = mag7Bit u8 b := fun b ↦ by
    rw [hβ₁]; exact (hP11a.keep_lt β _ (wMag7PWU_lt_157 b)).trans (hmag b)
  have h163_2 : β₂ ⟨163, by decide⟩ = outS := by
    rw [hβ₂]; dsimp only [pwuSt11b]
    have hv := hV11b β₁ hz1
    simp_rw [hmag1] at hv
    have hin : (fun i : Fin 6 ↦ β₁ ⟨48 + bSub + i.val, by omega⟩) =
        (fun i : Fin 6 ↦ β ⟨47 + bSub + (i.val + 1), by omega⟩) :=
      funext fun i ↦ (hβ₁ ▸ hP11a.keep_lt β _ (by dsimp; omega)).trans
        (congrArg β (Fin.ext (by dsimp; omega)))
    rw [h157_1, hin] at hv
    have h0_eq : mag7Bit u8 0 = mag7Bit u8 ⟨0 % 7, Nat.mod_lt _ (by decide)⟩ := rfl
    rw [h0_eq] at hv
    exact hv.trans (prioStarEval_zero_step0
      (fun t ↦ mag7Bit u8 ⟨t % 7, Nat.mod_lt _ (by decide)⟩) 6
      (fun i : Fin 7 ↦ β ⟨47 + bSub + i.val, by omega⟩))
  have h139_2 : β₂ ⟨139, by decide⟩ = β ⟨139, by decide⟩ := by
    rw [hβ₂]; dsimp only [pwuSt11b]
    rw [hP11b.keep_lt β₁ ⟨139, by decide⟩ (by decide), hβ₁]
    exact hP11a.keep_lt β ⟨139, by decide⟩ (by decide)
  have h164_3 : β₃ ⟨164, by decide⟩ = seedFn (β ⟨139, by decide⟩) outS := by
    rw [hβ₃, hV12a β₂ (hz2 _ le_rfl), h139_2, h163_2]
  have hkeep3_lt157 : ∀ w : Wire 185, w.val < 157 → β₃ w = β w := fun w hw ↦ by
    rw [hβ₃, hP12a.keep_lt β₂ w (by omega), hβ₂]; dsimp only [pwuSt11b]
    rw [hP11b.keep_lt β₁ w (by omega), hβ₁]
    exact hP11a.keep_lt β w hw
  refine ⟨fun w hw ↦ by
      rw [hβ₄]; dsimp only [pwuSt12b]
      exact (hP12b.keep_lt β₃ w (by omega)).trans (hkeep3_lt157 w hw),
    hz4, ?_, ?_⟩
  · rw [hβ₄]; dsimp only [pwuSt12b]
    rw [hP12b.keep_lt β₃ ⟨163, by decide⟩ (by decide), hβ₃,
      hP12a.keep_lt β₂ ⟨163, by decide⟩ (by decide)]
    exact h163_2
  · rw [hβ₄]; dsimp only [pwuSt12b]
    have hv := hV12b β₃ hz3
    have hmag3 : ∀ b : Fin 7, β₃ (wMag7PWU b) = mag7Bit u8 b :=
      fun b ↦ (hkeep3_lt157 _ (wMag7PWU_lt_157 b)).trans (hmag b)
    have hin3 : (fun i : Fin 14 ↦ β₃ ⟨33 + bSub + i.val, by omega⟩) =
        (fun i : Fin 14 ↦ β ⟨33 + bSub + i.val, by omega⟩) :=
      funext fun i ↦ hkeep3_lt157 _ (by dsimp; omega)
    simp_rw [hmag3] at hv
    rw [h164_3, hin3] at hv
    exact hv

attribute [local irreducible] pwuSt11a pwuSt11b pwuSt12b

def pwuSt13c : SsaProg 185 179 180 :=
  (SsaProg.cnot ⟨142, by decide⟩ ⟨139,
    by decide⟩ (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) (.done 179)).append <|
    (muxBit 179 (by decide) ⟨139, by decide⟩ ⟨163, by decide⟩ ⟨109, by decide⟩
      (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
      (by decide) (by decide) (by decide)).append <|
      .cnot ⟨142, by decide⟩ ⟨139,
        by decide⟩ (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) (.done 180)

def pwuSt13d : SsaProg 185 180 181 :=
  andPol 180 (by decide) ⟨178, by decide⟩ ⟨179, by decide⟩
    (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) false false

noncomputable def pwuSt13e (cfg : Configuration) : SsaProg 185 181 182 :=
  writeXor 181 (by decide) (slot1Sigma cfg 0)
    [((slot1Sigma cfg 0 != slot1Sigma cfg 1), ⟨⟨140, by decide⟩, by decide⟩),
     ((slot1Sigma cfg 0 != slot1Sigma cfg 1), ⟨⟨142, by decide⟩, by decide⟩),
     ((slot1Sigma cfg 0 != slot1Sigma cfg 2), ⟨⟨141, by decide⟩, by decide⟩),
     (true, ⟨⟨150, by decide⟩, by decide⟩),
     (true, ⟨⟨109, by decide⟩, by decide⟩)]

def pwuSt13f : SsaProg 185 182 183 :=
  (andPol 182 (by decide) ⟨139, by decide⟩ ⟨181, by decide⟩
    (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) false false).append <|
    .x ⟨182, by decide⟩ (by decide) <|
      .cnot ⟨139, by decide⟩ ⟨182,
        by decide⟩ (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) <|
        .cnot ⟨180, by decide⟩ ⟨182,
          by decide⟩ (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) <|
          .done 183

def pwuSt13g : SsaProg 185 183 184 :=
  andPol 183 (by decide) ⟨24, by decide⟩ ⟨25, by decide⟩
    (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) false true

def pwuSt13h : SsaProg 185 184 185 :=
  andPol 184 (by decide) ⟨183, by decide⟩ ⟨26, by decide⟩
    (Fin.ne_of_val_ne (by decide)) (by decide) (by decide) false false

noncomputable def pwuBlockDCombineRaw (cfg : Configuration) : SsaProg 185 179 185 :=
  pwuSt13c.append <| pwuSt13d.append <|
    (pwuSt13e cfg).append <| pwuSt13f.append <| pwuSt13g.append pwuSt13h

noncomputable def pwuBlockDCombine (cfg : Configuration) : SsaProg 185 179 185 :=
  lockValWalker (pwuBlockDCombineRaw cfg)

private theorem pwuBlockBMag7_countAnd : pwuBlockBMag7.countAnd = 6 := by
  rw [pwuBlockBMag7, lockValWalker_eq]
  simp only [pwuBlockBMag7Raw, pwuSt9, pwuSt10,
    SsaProg.append_countAnd, twosCarryChainG_countAnd, inplaceMag7G_countAnd]

private theorem pwuBlockDCombine_countAnd (cfg : Configuration) :
    (pwuBlockDCombine cfg).countAnd = 5 := by
  rw [pwuBlockDCombine, lockValWalker_eq]
  simp only [pwuBlockDCombineRaw, pwuSt13c, pwuSt13d, pwuSt13e,
    pwuSt13f, pwuSt13g, pwuSt13h, SsaProg.append_countAnd, SsaProg.countAnd_done,
    SsaProg.countAnd_x, SsaProg.countAnd_cnot, writeXor_countAnd, muxBit_countAnd, andPol_countAnd]

private theorem padZeroBits89_lt_110 (α : BitAssignment 110) (i : ℕ) (hi : i < 110) :
    (padZeroBits (mClean := 75) α) ⟨i, by omega⟩ = α ⟨i, hi⟩ := by
  have h : (⟨i, by omega⟩ : Wire 185) = Fin.castAdd 75 ⟨i, hi⟩ := Fin.ext rfl
  rw [h]; exact Fin.addCases_left _

private theorem padZeroBits89_ge_110 (α : BitAssignment 110) (w : Wire 185) (hw : 110 ≤ w.val) :
    (padZeroBits (mClean := 75) α) w = 0 := by
  let j : Fin 75 := ⟨w.val - 110, by omega⟩
  have h : w = Fin.natAdd 110 j := by ext; dsimp [j]; omega
  rw [h]; exact Fin.addCases_right j

def pwuSub110 (bSub : ℕ) (hbHi : bSub ≤ 24) (α : BitAssignment 110) : ℕ :=
  ∑ j : Fin bSub, (α ⟨30 + j.val, by have := j.isLt; omega⟩).val * 2 ^ j.val

def pwuCol110 (bSub : ℕ) (hbHi : bSub ≤ 24) (α : BitAssignment 110) : Fin 8 :=
  colFromBits (α ⟨30 + bSub, by omega⟩) (α ⟨31 + bSub, by omega⟩) (α ⟨32 + bSub, by omega⟩)

def pwuOutS110 (bSub : ℕ) (hbHi : bSub ≤ 24) (α : BitAssignment 110) (u8 : Fin 8 →
    ZMod 2) : ZMod 2 :=
  pwuChainEval7 0 u8 (fun i : Fin 7 ↦ α ⟨47 + bSub + i.val, by have := i.isLt; omega⟩)

def pwuOutR110 (bSub : ℕ) (hbHi : bSub ≤ 24) (b0 : ZMod 2)
    (α : BitAssignment 110) (u8 : Fin 8 → ZMod 2) : ZMod 2 :=
  pwuChainEval14 b0 u8 (fun i : Fin 14 ↦ α ⟨33 + bSub + i.val, by have := i.isLt; omega⟩)

noncomputable def slot1PWUPred110 (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (α : BitAssignment 110) : ZMod 2 :=
  if α ⟨24, by decide⟩ = 1 ∧ α ⟨25, by decide⟩ = 0 ∧ α ⟨26, by decide⟩ = 1 then
    let lf : Fin 8 := pwuLeafIdx bSub hbLo hbHi cfg (pwuCol110 bSub hbHi α) (pwuSub110 bSub hbHi α)
    let ax : Fin 3 := dyadicAxOfLf lf
    let u8 : Fin 8 → ZMod 2 := slot1U8_110 α ax
    let outS : ZMod 2 := pwuOutS110 bSub hbHi α u8
    let gL : ZMod 2 := b2z (decide (4 ≤ lf.val))
    let outR : ZMod 2 := pwuOutR110 bSub hbHi (gL * outS) α u8
    dyadicPhiLf cfg lf ax u8 outR outS (α ⟨109, by decide⟩)
  else 0

private theorem walkerBlockD_combine_algebra
    (cfg : Configuration) (lf : Fin 8) (hlf3 : lf ≠ 3) (ax : Fin 3)
    (u8 : Fin 8 → ZMod 2) (rVal sVal cHalf : ZMod 2)
    (hax : ax = dyadicAxOfLf lf) :
    let gL := b2z (decide (4 ≤ lf.val))
    let g1 := b2z (decide ((lf.val / 2) % 2 = 1))
    let g0 := b2z (decide (lf.val % 2 = 1))
    let isPad := g1 * g0
    gL *
        (b2z (slot1Sigma cfg 0) +
          ((if (slot1Sigma cfg 0 != slot1Sigma cfg 1) then g0 else 0) +
            ((if (slot1Sigma cfg 0 != slot1Sigma cfg 2) then g1 else 0) +
              (u8 7 + (cHalf + 0))))) +
      1 + gL +
      rVal * (if gL + isPad = 1 then cHalf else sVal) =
    dyadicPhiLf cfg lf ax u8 rVal sVal cHalf := by
  subst hax
  dsimp only
  unfold dyadicPhiLf dyadicAxOfLf
  generalize slot1Sigma cfg = s
  generalize u8 7 = u8_7
  have h20 : (2 : ZMod 2) = 0 := rfl
  have h11_0 : (1 : ZMod 2) + 1 = 0 := rfl
  have hb_xor : ∀ a b : Bool, b2z a + (if (a != b) then (1 : ZMod 2) else 0) = b2z b := by
    intro a b; cases a <;> cases b <;> rfl
  fin_cases lf
  · simp [b2z]
  · simp [b2z]
  · simp [b2z]
  · exact absurd rfl hlf3
  · simp [b2z]; ring
  · have hx1 := hb_xor (s 0) (s 1)
    simp [b2z] at hx1 ⊢
    linear_combination hx1
  · have hx2 := hb_xor (s 0) (s 2)
    simp [b2z] at hx2 ⊢
    linear_combination hx2
  · cases (s 0 != s 1) <;> cases (s 0 != s 2) <;>
      (simp [b2z, h11_0]; ring_nf; try simp [h20])

private theorem mux3_poly_eq_ite (x0 x1 x2 : ZMod 2) (lf : Fin 8) :
    let g0 := b2z (decide (lf.val % 2 = 1))
    let g1 := b2z (decide ((lf.val / 2) % 2 = 1))
    x0 + (x1 + x0) * (g0 + g1 * g0) + (x2 + x0) * g1 =
      if g1 = 1 then x2 else if g0 = 1 then x1 else x0 := by
  rcases bit_cases x0 with rfl | rfl <;>
    rcases bit_cases x1 with rfl | rfl <;>
    rcases bit_cases x2 with rfl | rfl <;>
    fin_cases lf <;> decide

private theorem xor_u1_isPad_eq_g0 (b : Bool) (g0 isPad rest : ZMod 2) :
    (if b then g0 + isPad else 0) + ((if b then isPad else 0) + rest) =
      (if b then g0 else 0) + rest := by
  cases b <;>
    rcases bit_cases g0 with rfl | rfl <;>
    rcases bit_cases isPad with rfl | rfl <;>
    rcases bit_cases rest with rfl | rfl <;> decide

private theorem pwuOuterSsa_orth (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (α : BitAssignment 110) :
    (pwuOuterSsa bSub hbLo hbHi cfg).eval (padZeroBits (mClean := 75) α) ⟨140, by decide⟩ *
      (pwuOuterSsa bSub hbLo hbHi cfg).eval (padZeroBits (mClean := 75) α) ⟨141, by decide⟩ = 0 :=
        by
  obtain ⟨_, _, _, hu1, hu2, _⟩ :=
    pwuOuterSsa_spec bSub hbLo hbHi cfg (padZeroBits (mClean := 75) α) (padZeroBits89_ge_110 α)
  rw [hu1, hu2]
  generalize b2z (decide (_ % 2 = 1)) = g0
  generalize b2z (decide ((_ / 2) % 2 = 1)) = g1
  rcases bit_cases g0 with rfl | rfl <;> rcases bit_cases g1 with rfl | rfl <;> decide

section Slot1PWUEvalKickIrred
attribute [local irreducible] pwuChainEval7 pwuChainEval14 pwuLeafIdx pwuOutR110

set_option maxHeartbeats 1600000 in -- elevated heartbeats for large proof
private theorem dInnerSsaGen_eval_kick (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (dInner : SsaProg 185 151 185) (blkC : SsaProg 185 157 179)
    (seedFn : ZMod 2 → ZMod 2 → ZMod 2) (hdInner : dInner = lockValWalker
      (pwuBlockBMag7.append <| blkC.append (pwuBlockDCombine cfg)))
    (hC : ∀ (u8 : Fin 8 → ZMod 2) (βB : BitAssignment 185),
      (∀ w : Wire 185, 157 ≤ w.val → βB w = 0) →
      (∀ b : Fin 7, βB (wMag7PWU b) = mag7Bit u8 b) →
      (∀ w : Wire 185, w.val < 157 → blkC.eval βB w = βB w) ∧
      (∀ w : Wire 185, 179 ≤ w.val → blkC.eval βB w = 0) ∧
      blkC.eval βB ⟨163, by decide⟩ =
        pwuChainEval7 0 u8 (fun i : Fin 7 ↦ βB ⟨47 + bSub + i.val, by omega⟩) ∧
      blkC.eval βB ⟨178, by decide⟩ = pwuChainEval14 (seedFn (βB ⟨139, by decide⟩)
        (pwuChainEval7 0 u8 (fun i : Fin 7 ↦ βB ⟨47 + bSub + i.val, by omega⟩))) u8
        (fun i : Fin 14 ↦ βB ⟨33 + bSub + i.val, by omega⟩))
    (α : BitAssignment 110)
    (hSeedEq : ∀ (u8 : Fin 8 → ZMod 2) (lf : Fin 8), lf ≠ 3 → ∀ (outS cH : ZMod 2),
      pwuOutR110 bSub hbHi (seedFn (b2z (decide (4 ≤ lf.val))) outS) α u8 *
        (if b2z (decide (4 ≤ lf.val)) +
          b2z (decide ((lf.val / 2) % 2 = 1)) * b2z (decide (lf.val % 2 = 1)) = 1
        then cH else outS) =
      pwuOutR110 bSub hbHi (b2z (decide (4 ≤ lf.val)) * outS) α u8 *
        (if b2z (decide (4 ≤ lf.val)) +
          b2z (decide ((lf.val / 2) % 2 = 1)) * b2z (decide (lf.val % 2 = 1)) = 1
        then cH else outS)) :
    dInner.eval
      (Mux3AnchoredPwu.writeMux8_185 ((pwuOuterSsa bSub hbLo hbHi cfg).eval (padZeroBits (mClean :=
        75) α)))
      ⟨182, by decide⟩ *
    dInner.eval
      (Mux3AnchoredPwu.writeMux8_185 ((pwuOuterSsa bSub hbLo hbHi cfg).eval (padZeroBits (mClean :=
        75) α)))
      ⟨184, by decide⟩ =
      slot1PWUPred110 bSub hbLo hbHi cfg α := by
  obtain ⟨β₀, hβ₀⟩ : ∃ x : BitAssignment 185, x = padZeroBits (mClean := 75) α := ⟨_, rfl⟩
  rw [← hβ₀]
  obtain ⟨βO, hβO⟩ : ∃ x, x = (pwuOuterSsa bSub hbLo hbHi cfg).eval β₀ := ⟨_, rfl⟩
  rw [← hβO]
  obtain ⟨βM, hβM⟩ : ∃ x, x = Mux3AnchoredPwu.writeMux8_185 βO := ⟨_, rfl⟩
  rw [← hβM]
  have htot :
      dInner.eval βM =
        pwuSt13h.eval (pwuSt13g.eval (pwuSt13f.eval ((pwuSt13e cfg).eval
          (pwuSt13d.eval (pwuSt13c.eval
            (blkC.eval (pwuBlockBMag7.eval βM))))))) := by
    rw [hdInner, lockValWalker_eq, pwuBlockDCombine, lockValWalker_eq]
    dsimp only [pwuBlockDCombineRaw]
    simp only [SsaProg.append_eval]
  rw [htot]
  obtain ⟨βB, hβB⟩ : ∃ x, x = pwuBlockBMag7.eval βM := ⟨_, rfl⟩
  rw [← hβB]
  obtain ⟨βC, hβC⟩ : ∃ x, x = blkC.eval βB := ⟨_, rfl⟩
  rw [← hβC]
  obtain ⟨β₃, hβ₃⟩ : ∃ x, x = pwuSt13c.eval βC := ⟨_, rfl⟩
  rw [← hβ₃]
  obtain ⟨β₄, hβ₄⟩ : ∃ x, x = pwuSt13d.eval β₃ := ⟨_, rfl⟩
  rw [← hβ₄]
  obtain ⟨β₅, hβ₅⟩ : ∃ x, x = (pwuSt13e cfg).eval β₄ := ⟨_, rfl⟩
  rw [← hβ₅]
  obtain ⟨β₆, hβ₆⟩ : ∃ x, x = pwuSt13f.eval β₅ := ⟨_, rfl⟩
  rw [← hβ₆]
  obtain ⟨β₇, hβ₇⟩ : ∃ x, x = pwuSt13g.eval β₆ := ⟨_, rfl⟩
  rw [← hβ₇]
  obtain ⟨β₈, hβ₈⟩ : ∃ x, x = pwuSt13h.eval β₇ := ⟨_, rfl⟩
  rw [← hβ₈]
  have hz₀ : ∀ w : Wire 185, 110 ≤ w.val → β₀ w = 0 := by rw [hβ₀]; exact padZeroBits89_ge_110 α
  have hlt₀ : ∀ (i : ℕ) (hi : i < 110), β₀ ⟨i, by omega⟩ = α ⟨i, hi⟩ := by
    intro i hi; rw [hβ₀]; exact padZeroBits89_lt_110 α i hi
  obtain ⟨hkeepO, hzO, hgLO, hu1O, hu2O, hpadO⟩ := pwuOuterSsa_spec bSub hbLo hbHi cfg β₀ hz₀
  rw [← hβO] at hkeepO hzO hgLO hu1O hu2O hpadO
  obtain ⟨col, hcol⟩ : ∃ x, x = colFromBits
    (β₀ ⟨30 + bSub, by omega⟩) (β₀ ⟨31 + bSub, by omega⟩) (β₀ ⟨32 + bSub, by omega⟩) := ⟨_, rfl⟩
  obtain ⟨vSub, hvSub⟩ : ∃ x, x = sliceVal β₀ 30 bSub (by omega) := ⟨_, rfl⟩
  rw [← hcol, ← hvSub] at hgLO hu1O hu2O hpadO
  obtain ⟨lf, hlf⟩ : ∃ x, x = pwuLeafIdx bSub hbLo hbHi cfg col vSub := ⟨_, rfl⟩
  rw [← hlf] at hgLO hu1O hu2O hpadO
  obtain ⟨ax, hax⟩ : ∃ x : Fin 3, x = dyadicAxOfLf lf := ⟨_, rfl⟩
  obtain ⟨u8, hu8⟩ : ∃ x : Fin 8 → ZMod 2, x = slot1U8_110 α ax := ⟨_, rfl⟩
  have hkeepM : ∀ w : Wire 185, w.val < 143 → βM w = βO w := fun w hw ↦ by
    rw [hβM, Mux3AnchoredPwu.writeMux8_185_apply, dite_eq_right (by omega)]
  have hzM : ∀ w : Wire 185, 151 ≤ w.val → βM w = 0 := fun w hw ↦ by
    rw [hβM, Mux3AnchoredPwu.writeMux8_185_apply, dite_eq_right (by omega)]
    exact hzO w (by omega)
  have hu8M : ∀ b : Fin 8, βM ⟨143 + b.val, by omega⟩ = u8 b := fun b ↦ by
    have hcond : 143 ≤ (⟨143 + b.val, by omega⟩ : Wire 185).val ∧
        (⟨143 + b.val, by omega⟩ : Wire 185).val < 151 := by
      have := b.isLt; dsimp; omega
    rw [hβM, Mux3AnchoredPwu.writeMux8_185_apply, dite_eq_left hcond]
    have hb_eq : (⟨(⟨143 + b.val, by omega⟩ : Wire 185).val - 143, by omega⟩ : Fin 8) = b :=
      Fin.ext (by dsimp; omega)
    rw [hb_eq]
    dsimp only [Mux3AnchoredPwu.Mux3Tuple.outBit, Mux3AnchoredPwu.mux3Tuple185]
    have hq0 : βO ⟨0 + b.val, by omega⟩ = α ⟨0 + b.val, by have := b.isLt; omega⟩ :=
      (hkeepO _ (by have := b.isLt; dsimp; omega)).trans (hlt₀ _ _)
    have hq1 : βO ⟨8 + b.val, by omega⟩ = α ⟨8 + b.val, by have := b.isLt; omega⟩ :=
      (hkeepO _ (by have := b.isLt; dsimp; omega)).trans (hlt₀ _ _)
    have hq2 : βO ⟨16 + b.val, by omega⟩ = α ⟨16 + b.val, by have := b.isLt; omega⟩ :=
      (hkeepO _ (by have := b.isLt; dsimp; omega)).trans (hlt₀ _ _)
    rw [hq0, hq1, hq2, hu1O, hu2O, mux3_poly_eq_ite, hu8, hax]
    dsimp only [slot1U8_110, dyadicAxOfLf]
    fin_cases lf <;> simp [b2z]
  obtain ⟨hkeepB, hzB, h150B, hmagB⟩ := pwuBlockBMag7_spec u8 βM hzM hu8M
  rw [← hβB] at hkeepB hzB h150B hmagB
  obtain ⟨hkeepC, hzC, houtSC, houtRC⟩ := hC u8 βB hzB hmagB
  rw [← hβC] at hkeepC hzC houtSC houtRC
  have hkeepBM_O : ∀ w : Wire 185, w.val < 143 → βB w = βO w :=
    fun w hw ↦ (hkeepB w hw).trans (hkeepM w hw)
  have hinS : (fun i : Fin 7 ↦ βB ⟨47 + bSub + i.val, by omega⟩) =
      (fun i : Fin 7 ↦ α ⟨47 + bSub + i.val, by have := i.isLt; omega⟩) :=
    funext fun i ↦ (hkeepBM_O _ (by have := i.isLt; dsimp; omega)).trans <|
      (hkeepO _ (by have := i.isLt; dsimp; omega)).trans (hlt₀ _ _)
  have hinR : (fun i : Fin 14 ↦ βB ⟨33 + bSub + i.val, by omega⟩) =
      (fun i : Fin 14 ↦ α ⟨33 + bSub + i.val, by have := i.isLt; omega⟩) :=
    funext fun i ↦ (hkeepBM_O _ (by have := i.isLt; dsimp; omega)).trans <|
      (hkeepO _ (by have := i.isLt; dsimp; omega)).trans (hlt₀ _ _)
  have hgLB : βB ⟨139, by decide⟩ = b2z (decide (4 ≤ lf.val)) :=
    (hkeepBM_O _ (by decide)).trans hgLO
  rw [hinS] at houtSC houtRC
  rw [hinR, hgLB] at houtRC
  have houtSC' : βC ⟨163, by decide⟩ = pwuOutS110 bSub hbHi α u8 := houtSC
  have houtRC' : βC ⟨178, by decide⟩ =
      pwuOutR110 bSub hbHi
        (seedFn (b2z (decide (4 ≤ lf.val))) (pwuOutS110 bSub hbHi α u8)) α u8 := by
    unfold pwuOutR110; exact houtRC
  have hkeepCB_O : ∀ w : Wire 185, w.val < 143 → βC w = βO w :=
    fun w hw ↦ (hkeepC w (by omega)).trans (hkeepBM_O w hw)
  have h24 : βC ⟨24, by decide⟩ = α ⟨24, by decide⟩ :=
    (hkeepCB_O _ (by decide)).trans ((hkeepO _ (by decide)).trans (hlt₀ 24 (by decide)))
  have h25 : βC ⟨25, by decide⟩ = α ⟨25, by decide⟩ :=
    (hkeepCB_O _ (by decide)).trans ((hkeepO _ (by decide)).trans (hlt₀ 25 (by decide)))
  have h26 : βC ⟨26, by decide⟩ = α ⟨26, by decide⟩ :=
    (hkeepCB_O _ (by decide)).trans ((hkeepO _ (by decide)).trans (hlt₀ 26 (by decide)))
  have h109 : βC ⟨109, by decide⟩ = α ⟨109, by decide⟩ :=
    (hkeepCB_O _ (by decide)).trans ((hkeepO _ (by decide)).trans (hlt₀ 109 (by decide)))
  have hgLC : βC ⟨139, by decide⟩ = b2z (decide (4 ≤ lf.val)) :=
    (hkeepCB_O _ (by decide)).trans hgLO
  have hu1C : βC ⟨140, by decide⟩ =
      b2z (decide (lf.val % 2 = 1)) + b2z (decide ((lf.val / 2) % 2 = 1)) *
        b2z (decide (lf.val % 2 = 1)) :=
    (hkeepCB_O _ (by decide)).trans hu1O
  have hu2C : βC ⟨141, by decide⟩ = b2z (decide ((lf.val / 2) % 2 = 1)) :=
    (hkeepCB_O _ (by decide)).trans hu2O
  have hpadC : βC ⟨142, by decide⟩ =
      b2z (decide ((lf.val / 2) % 2 = 1)) * b2z (decide (lf.val % 2 = 1)) :=
    (hkeepCB_O _ (by decide)).trans hpadO
  have h150C : βC ⟨150, by decide⟩ = u8 7 :=
    (hkeepC _ (by decide)).trans h150B
  have hPc : PreservesOutside 179 180 pwuSt13c.eval := by
    intro γ w hw
    dsimp only [pwuSt13c]
    simp only [SsaProg.append_eval, SsaProg.eval_cnot, SsaProg.eval_done]
    let γ₁ := Function.update γ ⟨139, by decide⟩ (γ ⟨139, by decide⟩ + γ ⟨142, by decide⟩)
    have hPm :=
      muxBit_preserves (M := 185) 179 (by decide) ⟨139, by decide⟩ ⟨163, by decide⟩ ⟨109, by decide⟩
      (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide)) (by decide) (by decide)
        (by decide) γ₁
    by_cases hw139 : w = ⟨139, by decide⟩
    · subst hw139
      rw [Function.update_self, hPm ⟨139, by decide⟩ (Or.inl (by decide)),
        hPm ⟨142, by decide⟩ (Or.inl (by decide))]
      dsimp only [γ₁]
      rw [Function.update_self,
        Function.update_of_ne (Fin.ne_of_val_ne (by decide) : (⟨142, by decide⟩ : Wire 185) ≠ ⟨139,
          by decide⟩)]
      exact zmod2_add_assoc_cancel _ _
    · rw [Function.update_of_ne hw139, hPm w hw]
      exact Function.update_of_ne hw139 _ _
  have hPd : PreservesOutside 180 181 pwuSt13d.eval :=
    andPol_preserves 180 (by decide) _ _ _ _ _ false false
  have hPe : PreservesOutside 181 182 (pwuSt13e cfg).eval := writeXor_preserves 181 (by decide) _ _
  have hPf : PreservesOutside 182 183 pwuSt13f.eval := by
    intro γ w hw
    have hw_ne182 : w ≠ ⟨182, by decide⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    dsimp only [pwuSt13f]
    simp only [SsaProg.append_eval, SsaProg.eval_cnot, SsaProg.eval_x, SsaProg.eval_done]
    rw [Function.update_of_ne hw_ne182, Function.update_of_ne hw_ne182,
      Function.update_of_ne hw_ne182]
    exact andPol_preserves 182 (by decide) _ _ _ _ _ false false _ w hw
  have hPg : PreservesOutside 183 184 pwuSt13g.eval :=
    andPol_preserves 183 (by decide) _ _ _ _ _ false true
  have hPh : PreservesOutside 184 185 pwuSt13h.eval :=
    andPol_preserves 184 (by decide) _ _ _ _ _ false false
  have hzc : ∀ w : Wire 185, 180 ≤ w.val → β₃ w = 0 := by
    rw [hβ₃]; exact hPc.clean_above hzC (by decide)
  have hzd : ∀ w : Wire 185, 181 ≤ w.val → β₄ w = 0 := by
    rw [hβ₄]; exact hPd.clean_above hzc (by decide)
  have hze : ∀ w : Wire 185, 182 ≤ w.val → β₅ w = 0 := by
    rw [hβ₅]; exact hPe.clean_above hzd (by decide)
  have hzf : ∀ w : Wire 185, 183 ≤ w.val → β₆ w = 0 := by
    rw [hβ₆]; exact hPf.clean_above hze (by decide)
  have hzg : ∀ w : Wire 185, 184 ≤ w.val → β₇ w = 0 := by
    rw [hβ₇]; exact hPg.clean_above hzf (by decide)
  have h179_3 : β₃ ⟨179, by decide⟩ =
      if βC ⟨139, by decide⟩ + βC ⟨142, by decide⟩ = 1 then βC ⟨109, by decide⟩ else βC ⟨163,
        by decide⟩ := by
    rw [hβ₃]; dsimp only [pwuSt13c]
    simp only [SsaProg.append_eval, SsaProg.eval_cnot, SsaProg.eval_done]
    let γ₁ := Function.update βC ⟨139, by decide⟩ (βC ⟨139, by decide⟩ + βC ⟨142, by decide⟩)
    have hzγ : γ₁ ⟨179, by decide⟩ = 0 := by
      dsimp only [γ₁]
      rw [Function.update_of_ne (Fin.ne_of_val_ne (by decide))]
      exact hzC _ le_rfl
    change Function.update
      ((muxBit 179 (by decide) ⟨139, by decide⟩ ⟨163, by decide⟩ ⟨109, by decide⟩
        (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
        (by decide) (by decide) (by decide)).eval γ₁)
      ⟨139, by decide⟩ _ ⟨179, by decide⟩ = _
    rw [Function.update_of_ne (Fin.ne_of_val_ne (by decide) : (⟨179, by decide⟩ : Wire 185) ≠ ⟨139,
      by decide⟩),
      muxBit_eval _ _ _ _ _ _ _ _ _ _ γ₁ hzγ, Function.update_self]
    have hγ139 : γ₁ ⟨139, by decide⟩ = βC ⟨139, by decide⟩ + βC ⟨142, by decide⟩ := by
      dsimp only [γ₁]; rw [Function.update_self]
    have hγ109 : γ₁ ⟨109, by decide⟩ = βC ⟨109, by decide⟩ := by
      dsimp only [γ₁]; rw [Function.update_of_ne (Fin.ne_of_val_ne (by decide))]
    have hγ163 : γ₁ ⟨163, by decide⟩ = βC ⟨163, by decide⟩ := by
      dsimp only [γ₁]; rw [Function.update_of_ne (Fin.ne_of_val_ne (by decide))]
    rw [hγ139, hγ109, hγ163]
  have h180_4 : β₄ ⟨180, by decide⟩ = βC ⟨178, by decide⟩ * β₃ ⟨179, by decide⟩ := by
    have hk178 : β₃ ⟨178, by decide⟩ = βC ⟨178, by decide⟩ := by
      rw [hβ₃]; exact hPc.keep_lt βC _ (by decide)
    rw [hβ₄]; dsimp only [pwuSt13d]
    rw [andPol_eval _ _ _ _ _ _ _ _ _ β₃ (hzc _ le_rfl), Function.update_self, hk178]; simp [b2z]
  have hkeep4_C : ∀ w : Wire 185, w.val < 179 → β₄ w = βC w := fun w hw ↦ by
    rw [hβ₄, hPd.keep_lt β₃ w (by omega), hβ₃]
    exact hPc.keep_lt βC w hw
  have h181_5 : β₅ ⟨181, by decide⟩ =
      b2z (slot1Sigma cfg 0) +
        ((if (slot1Sigma cfg 0 != slot1Sigma cfg 1) then βC ⟨140, by decide⟩ else 0) +
          ((if (slot1Sigma cfg 0 != slot1Sigma cfg 1) then βC ⟨142, by decide⟩ else 0) +
            ((if (slot1Sigma cfg 0 != slot1Sigma cfg 2) then βC ⟨141, by decide⟩ else 0) +
              (βC ⟨150, by decide⟩ + (βC ⟨109, by decide⟩ + 0))))) := by
    rw [hβ₅]; dsimp only [pwuSt13e]
    rw [writeXor_eval _ _ _ _ β₄ (hzd _ le_rfl), Function.update_self]
    dsimp only [listXorSum]
    rw [hkeep4_C ⟨140, by decide⟩ (by decide), hkeep4_C ⟨142, by decide⟩ (by decide),
      hkeep4_C ⟨141, by decide⟩ (by decide), hkeep4_C ⟨150, by decide⟩ (by decide),
      hkeep4_C ⟨109, by decide⟩ (by decide)]
    simp only [↓reduceIte]
  have h139_5 : β₅ ⟨139, by decide⟩ = βC ⟨139, by decide⟩ := by
    rw [hβ₅, hPe.keep_lt β₄ _ (by decide)]; exact hkeep4_C _ (by decide)
  have h180_5 : β₅ ⟨180, by decide⟩ = β₄ ⟨180, by decide⟩ := by
    rw [hβ₅]; exact hPe.keep_lt β₄ _ (by decide)
  have h182_6 : β₆ ⟨182, by decide⟩ =
      βC ⟨139, by decide⟩ * β₅ ⟨181, by decide⟩ + 1 + βC ⟨139, by decide⟩ + β₄ ⟨180, by decide⟩ :=
        by
    rw [hβ₆]; dsimp only [pwuSt13f]
    simp only [SsaProg.append_eval, SsaProg.eval_cnot, SsaProg.eval_x, SsaProg.eval_done]
    rw [andPol_eval _ _ _ _ _ _ _ _ _ β₅ (hze _ le_rfl)]
    have hne139 : (⟨139, by decide⟩ : Wire 185) ≠ ⟨182, by decide⟩ := Fin.ne_of_val_ne (by decide)
    have hne180 : (⟨180, by decide⟩ : Wire 185) ≠ ⟨182, by decide⟩ := Fin.ne_of_val_ne (by decide)
    simp only [Function.update_idem, Function.update_self, Function.update_of_ne hne139,
      Function.update_of_ne hne180, b2z, Bool.false_eq_true, ↓reduceIte]
    rw [h139_5, h180_5]
    ring
  have hkeep6_C : ∀ w : Wire 185, w.val < 179 → β₆ w = βC w := fun w hw ↦ by
    rw [hβ₆, hPf.keep_lt β₅ w (by omega), hβ₅, hPe.keep_lt β₄ w (by omega)]
    exact hkeep4_C w hw
  have h183_7 : β₇ ⟨183, by decide⟩ = α ⟨24, by decide⟩ * (α ⟨25, by decide⟩ + 1) := by
    have hk24 : β₆ ⟨24, by decide⟩ = α ⟨24, by decide⟩ := (hkeep6_C _ (by decide)).trans h24
    have hk25 : β₆ ⟨25, by decide⟩ = α ⟨25, by decide⟩ := (hkeep6_C _ (by decide)).trans h25
    rw [hβ₇]; dsimp only [pwuSt13g]
    rw [andPol_eval _ _ _ _ _ _ _ _ _ β₆ (hzf _ le_rfl), Function.update_self, hk24,
      hk25]; simp [b2z]
  have h184_8 : β₈ ⟨184, by decide⟩ =
      α ⟨24, by decide⟩ * (α ⟨25, by decide⟩ + 1) * α ⟨26, by decide⟩ := by
    have hk26 : β₇ ⟨26, by decide⟩ = α ⟨26, by decide⟩ := by
      rw [hβ₇, hPg.keep_lt β₆ _ (by decide)]
      exact (hkeep6_C _ (by decide)).trans h26
    rw [hβ₈]; dsimp only [pwuSt13h]
    rw [andPol_eval _ _ _ _ _ _ _ _ _ β₇ (hzg _ le_rfl), Function.update_self, h183_7,
      hk26]; simp [b2z]
  have h182_8 : β₈ ⟨182, by decide⟩ = β₆ ⟨182, by decide⟩ := by
    rw [hβ₈, hPh.keep_lt β₇ _ (by decide), hβ₇]; exact hPg.keep_lt β₆ _ (by decide)
  rw [h182_8, h184_8]
  have hvSub_eq : pwuSub110 bSub hbHi α = vSub := by
    rw [hvSub]; unfold pwuSub110
    rw [sliceVal_eq_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hlt₀ (30 + j.val) (by have := j.isLt; omega)]
  have hcol_eq : pwuCol110 bSub hbHi α = col := by
    rw [hcol]; unfold pwuCol110
    rw [hlt₀ (30 + bSub) (by omega), hlt₀ (31 + bSub) (by omega), hlt₀ (32 + bSub) (by omega)]
  unfold slot1PWUPred110
  by_cases hcoin : α ⟨24, by decide⟩ = 1 ∧ α ⟨25, by decide⟩ = 0 ∧ α ⟨26, by decide⟩ = 1
  · obtain ⟨hc0, hc1, hc2⟩ := hcoin
    simp only [hc0, hc1, hc2, and_self, ↓reduceIte, zero_add, mul_one]
    rw [hvSub_eq, hcol_eq, ← hlf, ← hax, ← hu8]
    rw [h182_6, h181_5, h180_4, h179_3, hgLC, hu1C, hpadC, hu2C, h150C, h109, houtRC', houtSC',
      xor_u1_isPad_eq_g0]
    have hlf3 : lf ≠ 3 := hlf ▸ pwuLeafIdx_ne_three bSub hbLo hbHi cfg col vSub
    rw [hSeedEq u8 lf hlf3 (pwuOutS110 bSub hbHi α u8) (α ⟨109, by decide⟩)]
    exact walkerBlockD_combine_algebra cfg lf hlf3 ax u8
      (pwuOutR110 bSub hbHi (b2z (decide (4 ≤ lf.val)) * pwuOutS110 bSub hbHi α u8) α u8)
      (pwuOutS110 bSub hbHi α u8)
      (α ⟨109, by decide⟩) hax
  · rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hcoin]
    have hc_zero : α ⟨24, by decide⟩ * (α ⟨25, by decide⟩ + 1) * α ⟨26, by decide⟩ = 0 := by
      rcases bit_cases (α ⟨24, by decide⟩) with c0 | c0 <;>
        rcases bit_cases (α ⟨25, by decide⟩) with c1 | c1 <;>
        rcases bit_cases (α ⟨26, by decide⟩) with c2 | c2 <;>
        simp_all
    rw [hc_zero, mul_zero]

end Slot1PWUEvalKickIrred

attribute [local irreducible]
  pwuSt13c pwuSt13d pwuSt13e pwuSt13f pwuSt13g pwuSt13h
  pwuBlockDCombine



private theorem pwuChainEval7_sum_val (b0 : ZMod 2) (u8 : Fin 8 → ZMod 2) :
    (∑ α : BitAssignment 7, (pwuChainEval7 b0 u8 α).val) = b0.val + mag7Nat u8 := by
  unfold pwuChainEval7
  rw [prioStarEval_sum_val]
  simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero, Fin.val_castSucc, Fin.val_last, zero_add]
  dsimp [mag7Nat]
  omega

private theorem pwuChainEval14_sum_val (b0 : ZMod 2) (u8 : Fin 8 → ZMod 2) :
    (∑ α : BitAssignment 14, (pwuChainEval14 b0 u8 α).val) = b0.val + 129 * mag7Nat u8 := by
  unfold pwuChainEval14
  rw [prioStarEval_sum_val]
  simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero, Fin.val_castSucc, Fin.val_last, zero_add]
  dsimp [mag7Nat]
  omega

attribute [local irreducible] pwuChainEval7 pwuChainEval14 pwuLeafIdx

noncomputable def pwuSlot1 (u8 : Fin 8 → ZMod 2) : ℝ :=
  (mag7Nat u8 : ℝ) / (2 : ℝ) ^ 7

noncomputable def pwuP14 (u8 : Fin 8 → ZMod 2) : ℝ :=
  ((129 : ℝ) * (mag7Nat u8 : ℝ)) / (2 : ℝ) ^ 14

noncomputable def pwuP21 (u8 : Fin 8 → ZMod 2) : ℝ :=
  ((16513 : ℝ) * (mag7Nat u8 : ℝ)) / (2 : ℝ) ^ 21

private theorem pwuSlot1_eq (u8 : Fin 8 → ZMod 2) :
    pwuSlot1 u8 = pwuC7 * ((mag7Nat u8 : ℝ) / 127) := by
  unfold pwuSlot1 pwuC7
  norm_num

private theorem pwuP14_eq (u8 : Fin 8 → ZMod 2) :
    pwuP14 u8 = pwuC14 * ((mag7Nat u8 : ℝ) / 127) := by
  unfold pwuP14 pwuC14
  norm_num
  ring

private theorem pwuP21_eq (u8 : Fin 8 → ZMod 2) :
    pwuP21 u8 = pwuC21 * ((mag7Nat u8 : ℝ) / 127) := by
  unfold pwuP21 pwuC21
  norm_num
  ring

private theorem mag7Nat_le_127 (u8 : Fin 8 → ZMod 2) : mag7Nat u8 ≤ 127 := by
  have hb0 : (mag7Bit u8 0).val < 2 := ZMod.val_lt _
  have hb1 : (mag7Bit u8 1).val < 2 := ZMod.val_lt _
  have hb2 : (mag7Bit u8 2).val < 2 := ZMod.val_lt _
  have hb3 : (mag7Bit u8 3).val < 2 := ZMod.val_lt _
  have hb4 : (mag7Bit u8 4).val < 2 := ZMod.val_lt _
  have hb5 : (mag7Bit u8 5).val < 2 := ZMod.val_lt _
  have hb6 : (mag7Bit u8 6).val < 2 := ZMod.val_lt _
  dsimp [mag7Nat]
  omega

private theorem pwuSlot1_bounds (u8 : Fin 8 → ZMod 2) : 0 ≤ pwuSlot1 u8 ∧ pwuSlot1 u8 ≤ 1 := by
  have hm : (mag7Nat u8 : ℝ) ≤ 127 := mod_cast mag7Nat_le_127 u8
  unfold pwuSlot1
  exact ⟨by positivity, by linarith⟩

private theorem pwuP14_bounds (u8 : Fin 8 → ZMod 2) : 0 ≤ pwuP14 u8 ∧ pwuP14 u8 ≤ 1 := by
  have hm : (mag7Nat u8 : ℝ) ≤ 127 := mod_cast mag7Nat_le_127 u8
  unfold pwuP14
  exact ⟨by positivity, by linarith⟩

private theorem pwuP21_bounds (u8 : Fin 8 → ZMod 2) : 0 ≤ pwuP21 u8 ∧ pwuP21 u8 ≤ 1 := by
  have hm : (mag7Nat u8 : ℝ) ≤ 127 := mod_cast mag7Nat_le_127 u8
  unfold pwuP21
  exact ⟨by positivity, by linarith⟩

noncomputable def pwuValBranch (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) : ℝ :=
  let w : Fin 3 := ⟨b.val / 2, by omega⟩
  let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys w)
  if b.val % 2 = 0 then
    2 * (pwuSlot1 u8 * pwuP14 u8) - 1
  else
    ((-1 : ℝ) ^ (b2z (slot1Sigma cfg w) + u8 7).val) * pwuP21 u8

noncomputable def pwuDelta (bSub : ℕ) (cfg : Configuration) (b : Fin 6) : ℕ :=
  if b.val % 2 = 0 then pwuTq bSub
  else if b.val = 1 then pwuDl bSub cfg 0
  else if b.val = 3 then pwuDl bSub cfg 1
  else pwuDl bSub cfg 2

noncomputable def bUnitTwosSlot1PWU (bSub : ℕ) (cfg : Configuration) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  Matrix.diagonal fun xSys ↦
    (((∑ b : Fin 6,
        ((pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3)) *
          pwuValBranch cfg xSys b) : ℝ) : ℂ)

noncomputable def pwuEffBranchWeight (cfg : Configuration) (b : Fin 6) : ℝ :=
  if b.val % 2 = 0 then slot1QuadBranchWeight / (pwuC7 * pwuC14)
  else if b.val = 1 then slot1LinBranchWeight cfg 0 / pwuC21
  else if b.val = 3 then slot1LinBranchWeight cfg 1 / pwuC21
  else slot1LinBranchWeight cfg 2 / pwuC21

private theorem pwuEffBranchWeight_mul_pwuValBranch_sum (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    (∑ b : Fin 6, pwuEffBranchWeight cfg b * pwuValBranch cfg xSys b) =
      (∑ b : Fin 6, slot1BranchWeight cfg b * slot1IdealValBranch cfg xSys b) -
        3 * slot1QuadBranchWeight * (1 / (pwuC7 * pwuC14) - 1) := by
  rw [sum_fin6_real, sum_fin6_real]
  let u0 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys 0)
  let u1 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys 1)
  let u2 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys 2)
  have hew0 : pwuEffBranchWeight cfg 0 = slot1QuadBranchWeight / (pwuC7 * pwuC14) := rfl
  have hew1 : pwuEffBranchWeight cfg 1 = slot1LinBranchWeight cfg 0 / pwuC21 := rfl
  have hew2 : pwuEffBranchWeight cfg 2 = slot1QuadBranchWeight / (pwuC7 * pwuC14) := rfl
  have hew3 : pwuEffBranchWeight cfg 3 = slot1LinBranchWeight cfg 1 / pwuC21 := rfl
  have hew4 : pwuEffBranchWeight cfg 4 = slot1QuadBranchWeight / (pwuC7 * pwuC14) := rfl
  have hew5 : pwuEffBranchWeight cfg 5 = slot1LinBranchWeight cfg 2 / pwuC21 := rfl
  have hpv0 : pwuValBranch cfg xSys 0 = 2 * (pwuSlot1 u0 * pwuP14 u0) - 1 := rfl
  have hpv1 : pwuValBranch cfg xSys 1 =
      ((-1 : ℝ) ^ (b2z (slot1Sigma cfg 0) + u0 7).val) * pwuP21 u0 := rfl
  have hpv2 : pwuValBranch cfg xSys 2 = 2 * (pwuSlot1 u1 * pwuP14 u1) - 1 := rfl
  have hpv3 : pwuValBranch cfg xSys 3 =
      ((-1 : ℝ) ^ (b2z (slot1Sigma cfg 1) + u1 7).val) * pwuP21 u1 := rfl
  have hpv4 : pwuValBranch cfg xSys 4 = 2 * (pwuSlot1 u2 * pwuP14 u2) - 1 := rfl
  have hpv5 : pwuValBranch cfg xSys 5 =
      ((-1 : ℝ) ^ (b2z (slot1Sigma cfg 2) + u2 7).val) * pwuP21 u2 := rfl
  have hbw0 : slot1BranchWeight cfg 0 = slot1QuadBranchWeight := rfl
  have hbw1 : slot1BranchWeight cfg 1 = slot1LinBranchWeight cfg 0 := rfl
  have hbw2 : slot1BranchWeight cfg 2 = slot1QuadBranchWeight := rfl
  have hbw3 : slot1BranchWeight cfg 3 = slot1LinBranchWeight cfg 1 := rfl
  have hbw4 : slot1BranchWeight cfg 4 = slot1QuadBranchWeight := rfl
  have hbw5 : slot1BranchWeight cfg 5 = slot1LinBranchWeight cfg 2 := rfl
  have hiv0 : slot1IdealValBranch cfg xSys 0 = 2 * ((mag7Nat u0 : ℝ) / 127) ^ 2 - 1 := rfl
  have hiv1 : slot1IdealValBranch cfg xSys 1 =
      ((-1 : ℝ) ^ (b2z (slot1Sigma cfg 0) + u0 7).val) * ((mag7Nat u0 : ℝ) / 127) := rfl
  have hiv2 : slot1IdealValBranch cfg xSys 2 = 2 * ((mag7Nat u1 : ℝ) / 127) ^ 2 - 1 := rfl
  have hiv3 : slot1IdealValBranch cfg xSys 3 =
      ((-1 : ℝ) ^ (b2z (slot1Sigma cfg 1) + u1 7).val) * ((mag7Nat u1 : ℝ) / 127) := rfl
  have hiv4 : slot1IdealValBranch cfg xSys 4 = 2 * ((mag7Nat u2 : ℝ) / 127) ^ 2 - 1 := rfl
  have hiv5 : slot1IdealValBranch cfg xSys 5 =
      ((-1 : ℝ) ^ (b2z (slot1Sigma cfg 2) + u2 7).val) * ((mag7Nat u2 : ℝ) / 127) := rfl
  rw [hew0, hew1, hew2, hew3, hew4, hew5, hpv0, hpv1, hpv2, hpv3, hpv4, hpv5,
    hbw0, hbw1, hbw2, hbw3, hbw4, hbw5, hiv0, hiv1, hiv2, hiv3, hiv4, hiv5,
    pwuSlot1_eq u0, pwuSlot1_eq u1, pwuSlot1_eq u2,
    pwuP14_eq u0, pwuP14_eq u1, pwuP14_eq u2,
    pwuP21_eq u0, pwuP21_eq u1, pwuP21_eq u2]
  have hc7 : pwuC7 ≠ 0 := pwuC7_pos.ne'
  have hc14 : pwuC14 ≠ 0 := pwuC14_pos.ne'
  have hc21 : pwuC21 ≠ 0 := pwuC21_pos.ne'
  field_simp [hc7, hc14, hc21]
  ring

attribute [local irreducible] basisBits QRegister.extractIndex

noncomputable def slot1PWUPhaseCore (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) (β : BitAssignment (coreWiresSym mPayload)) : ZMod 2 :=
  slot1PWUPred110 bSub hbLo hbHi cfg (fun i ↦ β (rActCore hmPay i))

noncomputable def slot1PWUSelectDiag (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) : Operator (2 ^ (coreWiresSym mPayload)) :=
  Matrix.diagonal fun g ↦
    ((-1 : ℂ) ^
      (slot1PWUPhaseCore bSub hbLo hbHi hmPay cfg (basisBits (coreWiresSym mPayload) g)).val)

theorem slot1PWUSelectDiag_conjTranspose (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (cfg : Configuration) :
    (slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg)ᴴ =
      slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [slot1PWUSelectDiag]
  · simp [slot1PWUSelectDiag, hij, Ne.symm hij]

theorem slot1PWUSelectDiag_mul_self (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (cfg : Configuration) :
    slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg *
      slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg = 1 := by
  rw [slot1PWUSelectDiag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext g
  exact MomSlots01Slot1ProjKinetic.neg_one_pow_bit_mul_self _

noncomputable def slot1PWUSelectUnitary (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) : Unitary (2 ^ (coreWiresSym mPayload)) :=
  ⟨slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg, mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, slot1PWUSelectDiag_conjTranspose]
    exact slot1PWUSelectDiag_mul_self bSub hbLo hbHi hmPay cfg)⟩

@[simp]
theorem slot1PWUSelectUnitary_val (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (cfg : Configuration) :
    (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg).1 =
      slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg := rfl

theorem slot1PWUSelectUnitary_sa (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (cfg : Configuration) :
    (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg).1ᴴ =
      (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg).1 :=
  slot1PWUSelectDiag_conjTranspose bSub hbLo hbHi hmPay cfg

private theorem embedUnitary_phaseDiagAct_eq_slot1PWUSelectUnitary
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (cfg : Configuration) :
    (rActCore hmPay).embedUnitary (phaseDiagAct (slot1PWUPred110 bSub hbLo hbHi cfg)) =
      slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg := by
  apply Subtype.ext
  rw [QRegister.embedUnitary_val, slot1PWUSelectUnitary_val]
  dsimp only [phaseDiagAct, slot1PWUSelectDiag]
  rw [MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
  congr 1; funext g
  have hbits : basisBits 110 ((rActCore hmPay).extractIndex g) =
      fun i ↦ basisBits (coreWiresSym mPayload) g (rActCore hmPay i) :=
    funext fun i ↦ (rActCore hmPay).basisBits_extractIndex g i
  rw [hbits]
  rfl

theorem slot1PWUSelectUnitary_offCoin (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (cfg : Configuration) :
    (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg).1 *
      (1 - momCoinProj mPayload (FullSysPrepare6Slot.fullSysCoinIdx 1)) =
      1 - momCoinProj mPayload (FullSysPrepare6Slot.fullSysCoinIdx 1) := by
  have hc5 : FullSysPrepare6Slot.fullSysCoinIdx 1 = 5 := rfl
  have hb0 : (MomSlots01Slot1ProjKinetic.coinBitFin2 5 0).val = 1 := coinBitFin2_5_0
  have hb1 : (MomSlots01Slot1ProjKinetic.coinBitFin2 5 1).val = 0 := coinBitFin2_5_1
  have hb2 : (MomSlots01Slot1ProjKinetic.coinBitFin2 5 2).val = 1 := coinBitFin2_5_2
  rw [Matrix.mul_sub, Matrix.mul_one, slot1PWUSelectUnitary_val, hc5, momCoinProj,
    slotBitProj, slotBitProj, slotBitProj, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, slot1PWUSelectDiag, Matrix.diagonal_mul_diagonal]
  ext g₁ g₂
  by_cases hg : g₁ = g₂
  · subst hg
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    have hw0 : rActCore hmPay ⟨24, by decide⟩ = MomSlots01Slot1ProjKinetic.iSlot0Mom mPayload := by
      ext; dsimp [rActCore, MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
        MomSlots01Slot1ProjKinetic.iSlot0Mom]
    have hw1 : rActCore hmPay ⟨25, by decide⟩ = MomSlots01Slot1ProjKinetic.iSlot1Mom mPayload := by
      ext; dsimp [rActCore, MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
        MomSlots01Slot1ProjKinetic.iSlot1Mom]
    have hw2 : rActCore hmPay ⟨26, by decide⟩ = MomSlots01Slot1ProjKinetic.iSlot2Mom mPayload := by
      ext; dsimp [rActCore, MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
        MomSlots01Slot1ProjKinetic.iSlot2Mom]
    by_cases hAll :
        basisBits (coreWiresSym mPayload) g₁ (MomSlots01Slot1ProjKinetic.iSlot0Mom mPayload) = 1 ∧
        basisBits (coreWiresSym mPayload) g₁ (MomSlots01Slot1ProjKinetic.iSlot1Mom mPayload) = 0 ∧
        basisBits (coreWiresSym mPayload) g₁ (MomSlots01Slot1ProjKinetic.iSlot2Mom mPayload) = 1
    · obtain ⟨hc0, hc1, hc2⟩ := hAll
      have hv0 : (0 : ZMod 2).val = 0 := rfl
      have hv1 : (1 : ZMod 2).val = 1 := rfl
      simp [hb0, hb1, hb2, hc0, hc1, hc2, hv0, hv1]
    · have hnot : ¬(basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay ⟨24, by decide⟩) = 1 ∧
          basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay ⟨25, by decide⟩) = 0 ∧
          basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay ⟨26, by decide⟩) = 1) := by
        intro ⟨h0, h1, h2⟩
        exact hAll ⟨(congrArg (basisBits (coreWiresSym mPayload) g₁) hw0).symm.trans h0,
          (congrArg (basisBits (coreWiresSym mPayload) g₁) hw1).symm.trans h1,
          (congrArg (basisBits (coreWiresSym mPayload) g₁) hw2).symm.trans h2⟩
      have hPhase0 : slot1PWUPhaseCore bSub hbLo hbHi hmPay cfg
        (basisBits (coreWiresSym mPayload) g₁) = 0 := by
        unfold slot1PWUPhaseCore slot1PWUPred110
        dsimp only
        exact MomSlots01Slot1ProjKinetic.ite_neg_s1 hnot
      rw [hPhase0]
      simp
  · simp [hg]

theorem slot1PWUSelectUnitary_conj_highWire (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration)
    (B : Unitary (2 ^ (coreWiresSym mPayload)))
    (hHigh : ∀ q : Wire (coreWiresSym mPayload), 3924 ≤ q.val → ∀ b : Fin 2,
      B.1 * slotBitProj q b = slotBitProj q b * B.1) :
    HoistedSwapSelectBridge.unitaryConj B (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg) =
      slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg := by
  let C := coreWiresSym mPayload
  have hbits_eq : ∀ x y : Fin (2 ^ C), B.1 x y ≠ 0 →
      ∀ q : Wire C, 3924 ≤ q.val → basisBits C x q = basisBits C y q := by
    intro x y hxy q hq
    let b : Fin 2 := ⟨(basisBits C y q).val, ZMod.val_lt _⟩
    have hcomm := congrFun (congrFun (hHigh q hq b) x) y
    simp only [slotBitProj, Matrix.mul_diagonal, Matrix.diagonal_mul] at hcomm
    have hy1 : (basisBits C y q).val = b.val := rfl
    rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 hy1, mul_one] at hcomm
    by_cases hx1 : (basisBits C x q).val = b.val
    · rcases bit_cases (basisBits C x q) with hx | hx <;>
        rcases bit_cases (basisBits C y q) with hy | hy
      · exact hx.trans hy.symm
      · rw [← hy1, hx, hy] at hx1; exact absurd hx1 (by decide)
      · rw [← hy1, hx, hy] at hx1; exact absurd hx1 (by decide)
      · exact hx.trans hy.symm
    · rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hx1, zero_mul] at hcomm
      exact absurd hcomm hxy
  have hphase_eq : ∀ x y : Fin (2 ^ C), B.1 x y ≠ 0 →
      slot1PWUPhaseCore bSub hbLo hbHi hmPay cfg (basisBits C x) =
        slot1PWUPhaseCore bSub hbLo hbHi hmPay cfg (basisBits C y) := by
    intro x y hxy
    unfold slot1PWUPhaseCore
    congr 1; funext i
    exact hbits_eq x y hxy (rActCore hmPay i) (by
      dsimp [rActCore, MomSlots01Slot1ProjKineticAlt.qreg_block_apply]
      omega)
  have hBComm : B.1 * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg =
      slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * B.1 := by
    ext x y
    simp only [slot1PWUSelectDiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hxy : B.1 x y = 0
    · simp [hxy]
    · rw [hphase_eq x y hxy, mul_comm]
  apply Subtype.ext
  have hInv : B.1ᴴ * B.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp B.2
  calc (HoistedSwapSelectBridge.unitaryConj B (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg)).1
      = B.1ᴴ * (B.1 * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg) := by
          rw [HoistedSwapSelectBridge.unitaryConj_val, Matrix.mul_assoc]
          change B.1ᴴ * (slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * B.1) =
            B.1ᴴ * (B.1 * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg)
          rw [← hBComm]
    _ = (B.1ᴴ * B.1) * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg := (Matrix.mul_assoc _ _ _).symm
    _ = slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg := by rw [hInv, Matrix.one_mul]
section Slot1PWUPart3BIrred

noncomputable def payloadWalkerSplitEquiv {mPayload bSub bCol bR bS bGap : ℕ}
    (hmPay : bSub + bCol + bR + bS + bGap + 1 ≤ mPayload) :
    Fin (2 ^ mPayload) ≃
      Fin (2 ^ bSub) × Fin (2 ^ bCol) × BitAssignment bR × BitAssignment bS ×
        BitAssignment bGap × ZMod 2 ×
        BitAssignment (mPayload - (bSub + bCol + bR + bS + bGap + 1)) :=
  (basisBitsEquiv mPayload).trans
  { toFun := fun γ ↦
      ((basisBitsEquiv bSub).symm (fun i ↦ γ ⟨i.val, by omega⟩),
       (basisBitsEquiv bCol).symm (fun i ↦ γ ⟨bSub + i.val, by omega⟩),
       fun i ↦ γ ⟨bSub + bCol + i.val, by omega⟩,
       fun i ↦ γ ⟨bSub + bCol + bR + i.val, by omega⟩,
       fun i ↦ γ ⟨bSub + bCol + bR + bS + i.val, by omega⟩,
       γ ⟨bSub + bCol + bR + bS + bGap, by omega⟩,
       fun i ↦ γ ⟨bSub + bCol + bR + bS + bGap + 1 + i.val, by omega⟩)
    invFun := fun ⟨vSub, vCol, αR, αS, αGap, cHalf, rest⟩ idx ↦
      if h1 : idx.val < bSub then
        basisBits bSub vSub ⟨idx.val, h1⟩
      else if h2 : idx.val < bSub + bCol then
        basisBits bCol vCol ⟨idx.val - bSub, by omega⟩
      else if h3 : idx.val < bSub + bCol + bR then
        αR ⟨idx.val - (bSub + bCol), by omega⟩
      else if h4 : idx.val < bSub + bCol + bR + bS then
        αS ⟨idx.val - (bSub + bCol + bR), by omega⟩
      else if h5 : idx.val < bSub + bCol + bR + bS + bGap then
        αGap ⟨idx.val - (bSub + bCol + bR + bS), by omega⟩
      else if h6 : idx.val = bSub + bCol + bR + bS + bGap then
        cHalf
      else
        rest ⟨idx.val - (bSub + bCol + bR + bS + bGap + 1), by have := idx.isLt; omega⟩
    left_inv := fun γ ↦ by
      funext idx
      dsimp only
      by_cases h1 : idx.val < bSub
      · rw [MomSlots01Slot1ProjKinetic.dite_pos_s1 h1,
          MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1]
      · rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 h1]
        by_cases h2 : idx.val < bSub + bCol
        · rw [MomSlots01Slot1ProjKinetic.dite_pos_s1 h2,
            MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1]
          exact congrArg γ (Fin.ext (by dsimp; omega))
        · rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 h2]
          by_cases h3 : idx.val < bSub + bCol + bR
          · rw [MomSlots01Slot1ProjKinetic.dite_pos_s1 h3]; exact congrArg γ
              (Fin.ext (by dsimp; omega))
          · rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 h3]
            by_cases h4 : idx.val < bSub + bCol + bR + bS
            · rw [MomSlots01Slot1ProjKinetic.dite_pos_s1 h4]; exact congrArg γ
                (Fin.ext (by dsimp; omega))
            · rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 h4]
              by_cases h5 : idx.val < bSub + bCol + bR + bS + bGap
              · rw [MomSlots01Slot1ProjKinetic.dite_pos_s1 h5]; exact congrArg γ
                  (Fin.ext (by dsimp; omega))
              · rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 h5]
                by_cases h6 : idx.val = bSub + bCol + bR + bS + bGap
                · rw [MomSlots01Slot1ProjKinetic.dite_pos_s1 h6]; exact congrArg γ
                    (Fin.ext (by dsimp; omega))
                · rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 h6]; exact congrArg γ
                    (Fin.ext (by dsimp; omega))
    right_inv := fun ⟨vSub, vCol, αR, αS, αGap, cHalf, rest⟩ ↦ by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))))
      · apply (basisBitsEquiv bSub).injective
        rw [(basisBitsEquiv bSub).apply_symm_apply, basisBitsEquiv_apply_eq]
        funext i
        dsimp only
        rw [MomSlots01Slot1ProjKinetic.dite_pos_s1 i.isLt]
      · apply (basisBitsEquiv bCol).injective
        rw [(basisBitsEquiv bCol).apply_symm_apply, basisBitsEquiv_apply_eq]
        funext i
        dsimp only
        rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega : ¬(bSub + i.val < bSub)),
          MomSlots01Slot1ProjKinetic.dite_pos_s1 (by omega : bSub + i.val < bSub + bCol)]
        exact congrArg (basisBits bCol vCol) (Fin.ext (by dsimp; omega))
      · funext i
        dsimp only
        rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_pos_s1 (by omega : bSub + bCol + i.val < bSub + bCol +
            bR)]
        exact congrArg αR (Fin.ext (by dsimp; omega))
      · funext i
        dsimp only
        rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_pos_s1 (by omega : bSub + bCol + bR + i.val < bSub +
            bCol + bR + bS)]
        exact congrArg αS (Fin.ext (by dsimp; omega))
      · funext i
        dsimp only
        rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_pos_s1 (by omega : bSub + bCol + bR + bS + i.val < bSub +
            bCol + bR + bS + bGap)]
        exact congrArg αGap (Fin.ext (by dsimp; omega))
      · dsimp only
        rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_pos_s1 rfl]
      · funext i
        dsimp only
        rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega),
          MomSlots01Slot1ProjKinetic.dite_neg_s1 (by omega)]
        exact congrArg rest (Fin.ext (by dsimp; omega)) }

def pwuSub (bSub : ℕ) (hbHi : bSub ≤ 24) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment mPayload) : ℕ :=
  ∑ j : Fin bSub, (γ ⟨j.val, by have := j.isLt; omega⟩).val * 2 ^ j.val

def pwuCol (bSub : ℕ) (hbHi : bSub ≤ 24) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment mPayload) : Fin 8 :=
  colFromBits
    (γ ⟨bSub, by omega⟩)
    (γ ⟨bSub + 1, by omega⟩)
    (γ ⟨bSub + 2, by omega⟩)

def pwuOutS (bSub : ℕ) (hbHi : bSub ≤ 24) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment mPayload) (u8 : Fin 8 → ZMod 2) : ZMod 2 :=
  pwuChainEval7 0 u8 (fun i : Fin 7 ↦ γ ⟨bSub + 17 + i.val, by have := i.isLt; omega⟩)

def pwuOutR (bSub : ℕ) (hbHi : bSub ≤ 24) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (b0 : ZMod 2) (γ : BitAssignment mPayload) (u8 : Fin 8 → ZMod 2) : ZMod 2 :=
  pwuChainEval14 b0 u8 (fun i : Fin 14 ↦ γ ⟨bSub + 3 + i.val, by have := i.isLt; omega⟩)

noncomputable def pwuPhaseScalar (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) (c : Fin 8)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (u : Fin (2 ^ mPayload)) : ℂ :=
  if c = 5 then
    let γ := basisBits mPayload u
    let lf : Fin 8 :=
      pwuLeafIdx bSub hbLo hbHi cfg (pwuCol bSub hbHi hmPay γ) (pwuSub bSub hbHi hmPay γ)
    let ax : Fin 3 := dyadicAxOfLf lf
    let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys ax)
    let outS : ZMod 2 := pwuOutS bSub hbHi hmPay γ u8
    let gL : ZMod 2 := b2z (decide (4 ≤ lf.val))
    let outR : ZMod 2 := pwuOutR bSub hbHi hmPay (gL * outS) γ u8
    let phi : ZMod 2 := dyadicPhiLf cfg lf ax u8 outR outS (γ ⟨79, by omega⟩)
    ((-1 : ℂ) ^ phi.val)
  else 1

private theorem sixProj_mul_slot1PWUSelectDiag (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) (c : Fin 8) :
    (coreSixSym mPayload).basisOutcomeProjector (coinSixOutcome c) *
        slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg =
      ∑ u : Fin (2 ^ mPayload),
        (corePayloadSym mPayload).basisOutcomeProjector u *
          (coreSixSym mPayload).basisOutcomeProjector (coinSixOutcome c) *
          (coreSysSym mPayload).embedMatrix
            (Matrix.diagonal (fun xSys ↦ pwuPhaseScalar bSub hbLo hbHi hmPay cfg c xSys u)) := by
  have hemb : ∀ u : Fin (2 ^ mPayload),
      (coreSysSym mPayload).embedMatrix
        (Matrix.diagonal (fun xSys ↦ pwuPhaseScalar bSub hbLo hbHi hmPay cfg c xSys u)) =
      Matrix.diagonal (fun g ↦ pwuPhaseScalar bSub hbLo hbHi hmPay cfg c
        ((coreSysSym mPayload).extractIndex g) u) :=
    fun u ↦ MomSlots01Slot1ProjKinetic.embedMatrix_diagonal (coreSysSym mPayload) _
  simp_rw [hemb, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  rw [slot1PWUSelectDiag, Matrix.diagonal_mul_diagonal]
  ext g₁ g₂
  by_cases hg : g₁ = g₂
  · subst hg
    simp only [Matrix.diagonal_apply_eq, Matrix.sum_apply]
    let u₀ : Fin (2 ^ mPayload) := (corePayloadSym mPayload).extractIndex g₁
    rw [Finset.sum_eq_single u₀
      (fun u _ hu ↦ by simp [u₀, Ne.symm hu])
      (fun h ↦ (h (Finset.mem_univ u₀)).elim)]
    simp only [u₀, ↓reduceIte, one_mul]
    by_cases hSix : (coreSixSym mPayload).extractIndex g₁ = coinSixOutcome c
    · simp only [hSix, ↓reduceIte, one_mul]
      have hbit6 : ∀ i : Fin 6,
          basisBits (coreWiresSym mPayload) g₁ ((coreSixSym mPayload) i) =
            basisBits 6 (coinSixOutcome c) i := fun i ↦ by
        rw [← (coreSixSym mPayload).basisBits_extractIndex g₁ i, hSix]
      have h6symm : ∀ i : Fin 6,
          basisBits 6 (coinSixOutcome c) i =
            if h : i.val < 3 then basisBits 3 c ⟨i.val, h⟩ else 0 :=
        MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1 _
      have hc_bit : ∀ i : Fin 3,
          basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay ⟨24 + i.val, by omega⟩) =
            basisBits 3 c i := fun i ↦ by
        have hw : rActCore hmPay ⟨24 + i.val, by omega⟩ =
            (coreSixSym mPayload) ⟨i.val, by omega⟩ := by
          ext
          dsimp [rActCore, coreSixSym, MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
            SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons,
            SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
          omega
        rw [hw, hbit6 ⟨i.val, by omega⟩, h6symm ⟨i.val, by omega⟩, dite_eq_left i.isLt]
      have hc0_raw := hc_bit 0
      have hc1_raw := hc_bit 1
      have hc2_raw := hc_bit 2
      have hpay_raw : ∀ (k : ℕ) (hk : k < 80),
          basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay ⟨30 + k, by omega⟩) =
            basisBits mPayload u₀ ⟨k, by omega⟩ := fun k hk ↦ by
        have hw : rActCore hmPay ⟨30 + k, by omega⟩ = corePayloadSym mPayload ⟨k, by omega⟩ := by
          ext; dsimp [rActCore, corePayloadSym, MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
            SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
              SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]; omega
        rw [hw]
        exact ((corePayloadSym mPayload).basisBits_extractIndex g₁ ⟨k, by omega⟩).symm
      have hproj_raw : ∀ (ax : Fin 3) (b : Fin 8),
          basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay ⟨8 * ax.val + b.val, by omega⟩) =
            u8FromFin (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) b := fun ax b ↦ by
        have hw : rActCore hmPay ⟨8 * ax.val + b.val, by omega⟩ =
            (coreSysSym mPayload) ((proj3Axes ax) b) := by
          ext; dsimp [rActCore, coreSysSym, proj3Axes,
            MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
            MomSlots01Slot1ProjKineticAlt.qreg_block_wires_apply,
            MomSlots01Slot1ProjKineticAlt.qreg_whole_wires,
            MomSlots01Slot1ProjKineticAlt.emb_trans_apply,
            MomSlots01Slot1ProjKineticAlt.emb_refl_apply,
            MomSlots01Slot1ProjKineticAlt.emb_mk_apply,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits]; omega
        rw [hw, ← (coreSysSym mPayload).basisBits_extractIndex g₁ ((proj3Axes ax) b),
          ← (proj3Axes ax).basisBits_extractIndex ((coreSysSym mPayload).extractIndex g₁) b]
        exact basisBits_eq_testBit 8 (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) b
      unfold slot1PWUPhaseCore
      obtain ⟨α, hα⟩ : ∃ x : BitAssignment 110,
          x = fun i ↦ basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay i) := ⟨_, rfl⟩
      rw [← hα]
      have hc0 : α ⟨24, by decide⟩ = basisBits 3 c 0 := (congrFun hα ⟨24, by decide⟩).trans hc0_raw
      have hc1 : α ⟨25, by decide⟩ = basisBits 3 c 1 := (congrFun hα ⟨25, by decide⟩).trans hc1_raw
      have hc2 : α ⟨26, by decide⟩ = basisBits 3 c 2 := (congrFun hα ⟨26, by decide⟩).trans hc2_raw
      have hpay : ∀ (k : ℕ) (hk : k < 80),
          α ⟨30 + k, by omega⟩ = basisBits mPayload u₀ ⟨k, by omega⟩ :=
        fun k hk ↦ (congrFun hα ⟨30 + k, by omega⟩).trans (hpay_raw k hk)
      have hproj : ∀ (ax : Fin 3) (b : Fin 8),
          α ⟨8 * ax.val + b.val, by omega⟩ =
            u8FromFin (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) b :=
        fun ax b ↦ (congrFun hα ⟨8 * ax.val + b.val, by omega⟩).trans (hproj_raw ax b)
      unfold slot1PWUPred110 pwuPhaseScalar
      dsimp only
      rw [hc0, hc1, hc2]
      by_cases hc5 : c = 5
      · have hcond : basisBits 3 c 0 = 1 ∧ basisBits 3 c 1 = 0 ∧ basisBits 3 c 2 = 1 :=
          (coin3_bits_eq_5_iff c).mpr hc5
        rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 hcond, MomSlots01Slot1ProjKinetic.ite_pos_s1 hc5]
        have hvSub : pwuSub110 bSub hbHi α = pwuSub bSub hbHi hmPay (basisBits mPayload u₀) :=
          Finset.sum_congr rfl fun j _ ↦ by
            rw [hpay j.val (by have := j.isLt; omega)]
        have hcol : pwuCol110 bSub hbHi α = pwuCol bSub hbHi hmPay (basisBits mPayload u₀) := by
          unfold pwuCol110 pwuCol
          have h0 : α ⟨30 + bSub, by omega⟩ = basisBits mPayload u₀ ⟨bSub, by omega⟩ :=
            hpay bSub (by omega)
          have h1 : α ⟨31 + bSub, by omega⟩ = basisBits mPayload u₀ ⟨bSub + 1, by omega⟩ :=
            (congrArg α (Fin.ext (by dsimp; omega))).trans (hpay (bSub + 1) (by omega))
          have h2 : α ⟨32 + bSub, by omega⟩ = basisBits mPayload u₀ ⟨bSub + 2, by omega⟩ :=
            (congrArg α (Fin.ext (by dsimp; omega))).trans (hpay (bSub + 2) (by omega))
          rw [h0, h1, h2]
        have hu8 : ∀ ax : Fin 3,
            slot1U8_110 α ax =
              u8FromFin (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) :=
          fun ax ↦ funext fun b ↦ hproj ax b
        have hOutS : ∀ u8 : Fin 8 → ZMod 2,
            pwuOutS110 bSub hbHi α u8 = pwuOutS bSub hbHi hmPay (basisBits mPayload u₀) u8 :=
          fun u8 ↦ congrArg (pwuChainEval7 0 u8) (funext fun i ↦
            (congrArg α (Fin.ext (by dsimp; omega))).trans
              (hpay (bSub + 17 + i.val) (by have := i.isLt; omega)))
        have hOutR : ∀ (b0 : ZMod 2) (u8 : Fin 8 → ZMod 2),
            pwuOutR110 bSub hbHi b0 α u8 = pwuOutR bSub hbHi hmPay b0 (basisBits mPayload u₀) u8 :=
          fun b0 u8 ↦ congrArg (pwuChainEval14 b0 u8) (funext fun i ↦
            (congrArg α (Fin.ext (by dsimp; omega))).trans
              (hpay (bSub + 3 + i.val) (by have := i.isLt; omega)))
        have h79 : α ⟨109, by decide⟩ = basisBits mPayload u₀ ⟨79, by omega⟩ := hpay 79 (by decide)
        rw [hvSub, hcol]
        simp_rw [hu8, hOutS, hOutR]
        rw [h79]
      · have hcond : ¬(basisBits 3 c 0 = 1 ∧ basisBits 3 c 1 = 0 ∧ basisBits 3 c 2 = 1) :=
          fun hh ↦ hc5 ((coin3_bits_eq_5_iff c).mp hh)
        rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hcond, MomSlots01Slot1ProjKinetic.ite_neg_s1 hc5]
        rfl
    · simp [hSix]
  · simp [Matrix.sum_apply, hg]

private theorem colFromBits_basisBits3 (vCol : Fin (2 ^ 3)) :
    colFromBits (basisBits 3 vCol 0) (basisBits 3 vCol 1) (basisBits 3 vCol 2) = vCol := by
  have hsum := sum_basisBits_val_eq (b := 3) vCol
  rw [Fin.sum_univ_three] at hsum
  have hv0 : (0 : Fin 3).val = 0 := rfl
  have hv1 : (1 : Fin 3).val = 1 := rfl
  have hv2 : (2 : Fin 3).val = 2 := rfl
  rw [hv0, hv1, hv2] at hsum
  norm_num at hsum
  apply Fin.ext
  dsimp [colFromBits]
  omega

private theorem inner_sum_pwu_leaf
    (cfg : Configuration) (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (lf : Fin 8) :
    (∑ αR : BitAssignment 14, ∑ αS : BitAssignment 7, ∑ coinHalf : ZMod 2,
      let ax : Fin 3 := dyadicAxOfLf lf
      let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys ax)
      let outS : ZMod 2 := pwuChainEval7 0 u8 αS
      let gL : ZMod 2 := b2z (decide (4 ≤ lf.val))
      let outR : ZMod 2 := pwuChainEval14 (gL * outS) u8 αR
      let phi : ZMod 2 := dyadicPhiLf cfg lf ax u8 outR outS coinHalf
      ((-1 : ℂ) ^ phi.val)) =
    if hpad : lf.val % 4 = 3 then 0
    else
      (2 : ℂ) * ((2 ^ 14 : ℕ) : ℂ) * ((2 ^ 7 : ℕ) : ℂ) *
        ((pwuValBranch cfg xSys (dyadicBranchOfNonPad lf hpad) : ℝ) : ℂ) := by
  have hcard14 : Fintype.card (BitAssignment 14) = 2 ^ 14 := by simp [BitAssignment]
  have hcard7 : Fintype.card (BitAssignment 7) = 2 ^ 7 := by simp [BitAssignment]
  unfold dyadicPhiLf
  by_cases hpad : lf.val % 4 = 3
  · simp only [hpad, ↓reduceIte, ↓reduceDIte]
    refine Finset.sum_eq_zero fun αR _ ↦ Finset.sum_eq_zero fun αS _ ↦ ?_
    rw [sum_zmod2]
    exact neg_one_pow_pad_cancel _
  · simp only [hpad, ↓reduceIte, ↓reduceDIte]
    let b6 : Fin 6 := dyadicBranchOfNonPad lf hpad
    let w : Fin 3 := ⟨b6.val / 2, by omega⟩
    have hax_eq : dyadicAxOfLf lf = w := by
      ext; dsimp only [dyadicAxOfLf, w, b6, dyadicBranchOfNonPad]
      revert hpad; fin_cases lf <;> decide
    let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys w)
    have hsum0R : (∑ α : BitAssignment 14, ((pwuChainEval14 0 u8 α).val : ℂ)) =
        (129 : ℂ) * (mag7Nat u8 : ℂ) := by
      have hz : (0 : ZMod 2).val = 0 := rfl
      have h := pwuChainEval14_sum_val 0 u8
      rw [hz, zero_add] at h
      exact_mod_cast h
    have hsum0S : (∑ α : BitAssignment 7, ((pwuChainEval7 0 u8 α).val : ℂ)) =
        (mag7Nat u8 : ℂ) := by
      have hz : (0 : ZMod 2).val = 0 := rfl
      have h := pwuChainEval7_sum_val 0 u8
      rw [hz, zero_add] at h
      exact_mod_cast h
    by_cases hlt4 : lf.val < 4
    · have hgL0 : b2z (decide (4 ≤ lf.val)) = 0 := by
        have hn4 : ¬(4 ≤ lf.val) := by omega
        simp [hn4, b2z]
      simp only [hlt4, ↓reduceIte, hax_eq, hgL0, zero_mul]
      have h1 : ∀ (αR : BitAssignment 14) (αS : BitAssignment 7),
          (∑ _c : ZMod 2,
            ((-1 : ℂ) ^ (1 + pwuChainEval14 0 u8 αR * pwuChainEval7 0 u8 αS).val)) =
          (4 : ℂ) * ((pwuChainEval14 0 u8 αR).val : ℂ) * ((pwuChainEval7 0 u8 αS).val : ℂ) - 2 :=
        fun αR αS ↦ by rw [sum_zmod2, neg_one_pow_quad_eq]; ring
      rw [Finset.sum_congr rfl fun αR _ ↦ Finset.sum_congr rfl fun αS _ ↦ h1 αR αS]
      have h2 : ∀ αR : BitAssignment 14,
          (∑ αS : BitAssignment 7,
            ((4 : ℂ) * ((pwuChainEval14 0 u8 αR).val : ℂ) *
              ((pwuChainEval7 0 u8 αS).val : ℂ) - 2)) =
          (4 : ℂ) * ((pwuChainEval14 0 u8 αR).val : ℂ) * (mag7Nat u8 : ℂ) -
            2 * ((2 ^ 7 : ℕ) : ℂ) := fun αR ↦ by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum0S,
          Finset.sum_const, Finset.card_univ, hcard7, nsmul_eq_mul]
        ring
      rw [Finset.sum_congr rfl fun αR _ ↦ h2 αR, Finset.sum_sub_distrib]
      have hmulR :
          (∑ αR : BitAssignment 14,
            (4 : ℂ) * ((pwuChainEval14 0 u8 αR).val : ℂ) * (mag7Nat u8 : ℂ)) =
          (4 : ℂ) * ((129 : ℂ) * (mag7Nat u8 : ℂ)) * (mag7Nat u8 : ℂ) := by
        calc _ = ∑ αR : BitAssignment 14,
              ((4 : ℂ) * (mag7Nat u8 : ℂ)) * ((pwuChainEval14 0 u8 αR).val : ℂ) :=
              Finset.sum_congr rfl fun _ _ ↦ by ring
          _ = _ := by rw [← Finset.mul_sum, hsum0R]; ring
      rw [hmulR, Finset.sum_const, Finset.card_univ, hcard14, nsmul_eq_mul]
      unfold pwuValBranch pwuSlot1 pwuP14
      have hb6_even : b6.val % 2 = 0 := by
        dsimp [b6, dyadicBranchOfNonPad]; simp [hlt4]
      rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 hb6_even]
      push_cast
      norm_num
      ring
    · have hgL1 : b2z (decide (4 ≤ lf.val)) = 1 := by
        have hge4 : 4 ≤ lf.val := by omega
        simp [hge4, b2z]
      simp only [hlt4, ↓reduceIte, hax_eq, hgL1, one_mul]
      let sgn : ℂ := (-1 : ℂ) ^ (b2z (slot1Sigma cfg w) + u8 7).val
      have h1 : ∀ (αR : BitAssignment 14) (αS : BitAssignment 7),
          (∑ coinHalf : ZMod 2,
            ((-1 : ℂ) ^ (b2z (slot1Sigma cfg w) + u8 7 +
              coinHalf * (1 + pwuChainEval14 (pwuChainEval7 0 u8 αS) u8 αR)).val)) =
          (2 : ℂ) * sgn * ((pwuChainEval14 (pwuChainEval7 0 u8 αS) u8 αR).val : ℂ) :=
        fun αR αS ↦ by rw [sum_zmod2]; exact neg_one_pow_lin_sum _ _
      rw [Finset.sum_congr rfl fun αR _ ↦ Finset.sum_congr rfl fun αS _ ↦ h1 αR αS]
      rw [Finset.sum_comm]
      have h2 : ∀ αS : BitAssignment 7,
          (∑ αR : BitAssignment 14,
            (2 : ℂ) * sgn * ((pwuChainEval14 (pwuChainEval7 0 u8 αS) u8 αR).val : ℂ)) =
          (2 : ℂ) * sgn *
            (((pwuChainEval7 0 u8 αS).val : ℂ) + (129 : ℂ) * (mag7Nat u8 : ℂ)) := fun αS ↦ by
        rw [← Finset.mul_sum]
        congr 1
        exact_mod_cast pwuChainEval14_sum_val (pwuChainEval7 0 u8 αS) u8
      rw [Finset.sum_congr rfl fun αS _ ↦ h2 αS, ← Finset.mul_sum,
        Finset.sum_add_distrib, hsum0S, Finset.sum_const, Finset.card_univ, hcard7, nsmul_eq_mul]
      unfold pwuValBranch pwuP21
      have hb6_odd : ¬(b6.val % 2 = 0) := by
        dsimp [b6, dyadicBranchOfNonPad]; simp [hlt4]
      rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hb6_odd]
      dsimp only [sgn]
      push_cast
      norm_num
      ring

private theorem avg_pwuPhaseScalar_sym (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) (c : Fin 8)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    ((2 : ℂ)⁻¹ ^ mPayload) *
        (∑ u : Fin (2 ^ mPayload), pwuPhaseScalar bSub hbLo hbHi hmPay cfg c xSys u) =
      if c = 5 then bUnitTwosSlot1PWU bSub cfg xSys xSys else 1 := by
  by_cases hc5 : c = 5
  · subst hc5
    rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 rfl]
    unfold bUnitTwosSlot1PWU
    rw [Matrix.diagonal_apply_eq]
    let bGap : ℕ := 55 - bSub
    have hmPay' : bSub + 3 + 14 + 7 + bGap + 1 ≤ mPayload := by dsimp [bGap]; omega
    let e := payloadWalkerSplitEquiv hmPay'
    rw [← Equiv.sum_comp e.symm (fun u ↦ pwuPhaseScalar bSub hbLo hbHi hmPay cfg 5 xSys u)]
    have hcardBA : ∀ m : ℕ, Fintype.card (BitAssignment m) = 2 ^ m :=
      fun m ↦ by simp [BitAssignment]
    let bPost : ℕ := mPayload - (bSub + 3 + 14 + 7 + bGap + 1)
    have hbody : ∀ (vSub : Fin (2 ^ bSub)) (vCol : Fin (2 ^ 3))
        (αR : BitAssignment 14) (αS : BitAssignment 7)
        (αGap : BitAssignment bGap) (coinHalf : ZMod 2)
        (rest : BitAssignment bPost),
        pwuPhaseScalar bSub hbLo hbHi hmPay cfg 5 xSys
            (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest)) =
          let lf : Fin 8 := pwuLeafIdx bSub hbLo hbHi cfg vCol vSub.val
          let ax : Fin 3 := dyadicAxOfLf lf
          let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys ax)
          let outS : ZMod 2 := pwuChainEval7 0 u8 αS
          let gL : ZMod 2 := b2z (decide (4 ≤ lf.val))
          let outR : ZMod 2 := pwuChainEval14 (gL * outS) u8 αR
          let phi : ZMod 2 := dyadicPhiLf cfg lf ax u8 outR outS coinHalf
          ((-1 : ℂ) ^ phi.val) := by
      intro vSub vCol αR αS αGap coinHalf rest
      have hsymm := e.apply_symm_apply (vSub, vCol, αR, αS, αGap, coinHalf, rest)
      have hvSub : (∑ j : Fin bSub,
          (basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))
            ⟨j.val, by have := j.isLt; omega⟩).val * 2 ^ j.val) = vSub.val := by
        have hbit : ∀ j : Fin bSub,
            basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))
              ⟨j.val, by have := j.isLt; omega⟩ = basisBits bSub vSub j := fun j ↦ by
          have ht := congrArg (fun p ↦ p.1) hsymm
          dsimp only [e, payloadWalkerSplitEquiv, Equiv.trans_apply] at ht
          rw [basisBitsEquiv_apply_eq] at ht
          exact (MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1 _ j).symm.trans
            (congrFun (congrArg (basisBits bSub) ht) j)
        simp_rw [hbit]
        exact sum_basisBits_val_eq vSub
      have hvCol : pwuCol bSub hbHi hmPay
          (basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))) = vCol := by
        have hbit3 : ∀ j : Fin 3,
            basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))
              ⟨bSub + j.val, by have := j.isLt; omega⟩ = basisBits 3 vCol j := fun j ↦ by
          have ht := congrArg (fun p ↦ p.2.1) hsymm
          dsimp only [e, payloadWalkerSplitEquiv, Equiv.trans_apply] at ht
          rw [basisBitsEquiv_apply_eq] at ht
          exact (MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1 _ j).symm.trans
            (congrFun (congrArg (basisBits 3) ht) j)
        unfold pwuCol
        have h0 : basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))
            ⟨bSub, by omega⟩ = basisBits 3 vCol 0 :=
          (congrArg (basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest)))
            (Fin.ext (by dsimp))).trans (hbit3 0)
        have h1 : basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))
            ⟨bSub + 1, by omega⟩ = basisBits 3 vCol 1 := hbit3 1
        have h2 : basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))
            ⟨bSub + 2, by omega⟩ = basisBits 3 vCol 2 := hbit3 2
        rw [h0, h1, h2]
        exact colFromBits_basisBits3 vCol
      have hR : ∀ i : Fin 14,
          basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))
            ⟨bSub + 3 + i.val, by have := i.isLt; omega⟩ = αR i := fun i ↦ by
        have ht := congrFun (congrArg (fun p ↦ p.2.2.1) hsymm) i
        dsimp only [e, payloadWalkerSplitEquiv, Equiv.trans_apply] at ht
        rw [basisBitsEquiv_apply_eq] at ht
        exact (congrArg (basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest)))
          (Fin.ext (by dsimp))).trans ht
      have hS : ∀ i : Fin 7,
          basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))
            ⟨bSub + 17 + i.val, by have := i.isLt; omega⟩ = αS i := fun i ↦ by
        have ht := congrFun (congrArg (fun p ↦ p.2.2.2.1) hsymm) i
        dsimp only [e, payloadWalkerSplitEquiv, Equiv.trans_apply] at ht
        rw [basisBitsEquiv_apply_eq] at ht
        exact (congrArg (basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest)))
          (Fin.ext (by dsimp))).trans ht
      have hcH : basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest))
          ⟨79, by omega⟩ = coinHalf := by
        have ht := congrArg (fun p ↦ p.2.2.2.2.2.1) hsymm
        dsimp only [e, payloadWalkerSplitEquiv, Equiv.trans_apply] at ht
        rw [basisBitsEquiv_apply_eq] at ht
        exact (congrArg (basisBits mPayload (e.symm (vSub, vCol, αR, αS, αGap, coinHalf, rest)))
          (Fin.ext (by dsimp [bGap]; try omega))).trans ht
      unfold pwuPhaseScalar pwuSub pwuOutS pwuOutR
      rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 rfl]
      dsimp only
      rw [hvSub, hvCol, funext hS, funext hR, hcH]
    simp_rw [Fintype.sum_prod_type]
    simp_rw [hbody]
    simp_rw [Finset.sum_const, Finset.card_univ, hcardBA, nsmul_eq_mul]
    let gLeaf : Fin 8 → ℂ := fun lf ↦
      if hpad : lf.val % 4 = 3 then 0
      else
        (2 : ℂ) * ((2 ^ 14 : ℕ) : ℂ) * ((2 ^ 7 : ℕ) : ℂ) *
          ((pwuValBranch cfg xSys (dyadicBranchOfNonPad lf hpad) : ℝ) : ℂ)
    let cExtra : ℂ := ((2 ^ bGap : ℕ) : ℂ) * ((2 ^ bPost : ℕ) : ℂ)
    have hinner_v : ∀ (vSub : Fin (2 ^ bSub)) (vCol : Fin (2 ^ 3)),
        (∑ αR : BitAssignment 14, ∑ αS : BitAssignment 7,
          (((2 ^ bGap : ℕ) : ℂ) * ∑ coinHalf : ZMod 2,
            (((2 ^ bPost : ℕ) : ℂ) *
              (let lf : Fin 8 := pwuLeafIdx bSub hbLo hbHi cfg vCol vSub.val
               let ax : Fin 3 := dyadicAxOfLf lf
               let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys ax)
               let outS : ZMod 2 := pwuChainEval7 0 u8 αS
               let gL : ZMod 2 := b2z (decide (4 ≤ lf.val))
               let outR : ZMod 2 := pwuChainEval14 (gL * outS) u8 αR
               let phi : ZMod 2 := dyadicPhiLf cfg lf ax u8 outR outS coinHalf
               ((-1 : ℂ) ^ phi.val))))) =
        cExtra * gLeaf (pwuLeafIdx bSub hbLo hbHi cfg vCol vSub.val) :=
      fun vSub vCol ↦ by
        dsimp only [cExtra]
        simp_rw [← Finset.mul_sum]
        rw [← mul_assoc]
        congr 1
        exact inner_sum_pwu_leaf cfg xSys _
    rw [Finset.sum_congr rfl fun vSub _ ↦ by
      rw [Finset.sum_congr rfl fun vCol _ ↦ hinner_v vSub vCol, ← Finset.mul_sum]]
    rw [← Finset.mul_sum, Finset.sum_comm]
    change ((2 : ℂ)⁻¹ ^ mPayload) *
        (cExtra * ∑ col : Fin 8, ∑ vSub : Fin (2 ^ bSub),
          gLeaf (pwuLeafIdx bSub hbLo hbHi cfg col vSub.val)) = _
    rw [sum_pwuLeafIdx_of_pad_zero bSub hbLo hbHi cfg gLeaf (by simp [gLeaf])]
    have hg_eq : ∀ (lf : Fin 8) (b : Fin 6) (hpad : ¬(lf.val % 4 = 3)),
        dyadicBranchOfNonPad lf hpad = b →
        gLeaf lf = (2 : ℂ) * ((2 ^ 14 : ℕ) : ℂ) * ((2 ^ 7 : ℕ) : ℂ) *
          ((pwuValBranch cfg xSys b : ℝ) : ℂ) := fun lf b hpad hb ↦ by
      subst hb
      dsimp only [gLeaf]
      rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 hpad]
    rw [hg_eq 0 0 (by decide) rfl, hg_eq 1 2 (by decide) rfl, hg_eq 2 4 (by decide) rfl,
      hg_eq 4 1 (by decide) rfl, hg_eq 5 3 (by decide) rfl, hg_eq 6 5 (by decide) rfl,
      sum_fin6_real]
    have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
    have hm_split : mPayload = bPost + bGap + (bSub + 3) + 22 := by
      dsimp [bPost, bGap]; omega
    have hinv : ((2 : ℂ)⁻¹ ^ mPayload) =
        ((2 : ℂ)⁻¹ ^ bPost) * ((2 : ℂ)⁻¹ ^ bGap) *
          ((2 : ℂ)⁻¹ ^ (bSub + 3)) * ((2 : ℂ)⁻¹ ^ 22) := by
      conv_lhs => rw [hm_split, pow_add, pow_add, pow_add]
    have hcPost : ((2 : ℂ)⁻¹ ^ bPost) * ((2 ^ bPost : ℕ) : ℂ) = 1 := by
      push_cast; rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero _ h2ne)
    have hcGap : ((2 : ℂ)⁻¹ ^ bGap) * ((2 ^ bGap : ℕ) : ℂ) = 1 := by
      push_cast; rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero _ h2ne)
    rw [hinv]
    dsimp only [cExtra, pwuDelta]
    have h_rearrange : ∀ (S : ℂ),
        (((2 : ℂ)⁻¹ ^ bPost) * ((2 : ℂ)⁻¹ ^ bGap) *
            ((2 : ℂ)⁻¹ ^ (bSub + 3)) * ((2 : ℂ)⁻¹ ^ 22)) *
          ((((2 ^ bGap : ℕ) : ℂ) * ((2 ^ bPost : ℕ) : ℂ)) * S) =
        (((2 : ℂ)⁻¹ ^ bPost) * ((2 ^ bPost : ℕ) : ℂ)) *
          (((2 : ℂ)⁻¹ ^ bGap) * ((2 ^ bGap : ℕ) : ℂ)) *
          (((2 : ℂ)⁻¹ ^ (bSub + 3)) * (((2 : ℂ)⁻¹ ^ 22) * S)) := fun _ ↦ by ring
    rw [h_rearrange, hcPost, hcGap, one_mul, one_mul]
    simp only [↓reduceIte, show (0 : Fin 6).val % 2 = 0 by decide,
      show (2 : Fin 6).val % 2 = 0 by decide, show (4 : Fin 6).val % 2 = 0 by decide,
      show (1 : Fin 6).val = 1 by decide, show (3 : Fin 6).val = 3 by decide,
      show ¬((5 : Fin 6).val % 2 = 0) by decide, show ¬((5 : Fin 6).val = 1) by decide,
      show ¬((5 : Fin 6).val = 3) by decide]
    push_cast
    rw [inv_pow]
    simp only [div_eq_mul_inv]
    norm_num
    ring
  · rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hc5]
    have h1 : ∀ u : Fin (2 ^ mPayload), pwuPhaseScalar bSub hbLo hbHi hmPay cfg c xSys u = 1 :=
      fun u ↦ by unfold pwuPhaseScalar; rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hc5]
    simp_rw [h1]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]

open MeasureBranchHadamardSem (hadamardAll)
private theorem slot1PWU_hadamard_topBlock_all (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) (c : Fin 8) :
    let B_c : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
      if c = 5 then bUnitTwosSlot1PWU bSub cfg else 1
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) *
      (unitaryConj (coreHadamardUnitary mPayload)
        (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg)).1 *
      (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) =
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) *
      (coreSysSym mPayload).embedMatrix B_c *
      (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) := by
  intro B_c
  let sys := coreSysSym mPayload
  let six := coreSixSym mPayload
  let pay := corePayloadSym mPayload
  let H := (hadamardAll pay).eval
  let R_c := six.basisOutcomeProjector (coinSixOutcome c)
  let P_0 := pay.basisOutcomeProjector 0
  have hDisj_pay_six : pay.DisjointWires six :=
    QRegister.disjoint_comm.mp <|
      QRegister.block_disjoint_of_le SpecsAux.SpecMirror.systemQubits 6
        (SpecsAux.SpecMirror.systemQubits + 6) mPayload
        (by dsimp [coreWiresSym, selWiresSym]; omega)
        (by dsimp [coreWiresSym, selWiresSym]; omega) le_rfl
  have hDisj_pay_sys : pay.DisjointWires sys :=
    QRegister.disjoint_comm.mp <|
      QRegister.block_disjoint_of_le 0 SpecsAux.SpecMirror.systemQubits
        (SpecsAux.SpecMirror.systemQubits + 6) mPayload
        (by dsimp [coreWiresSym]; omega)
        (by dsimp [coreWiresSym, selWiresSym]; omega) (by omega)
  have hH_sa : H.1ᴴ = H.1 := FullSysPrepare6Slot.hadamardAll_eval_self_adj pay
  have hH_Rc : H.1 * R_c = R_c * H.1 :=
    MomSlots01Slot1ProjKinetic.hadamardAll_comm_embedMatrix_slot1 pay six hDisj_pay_six
      (compProj (coinSixOutcome c))
  have hH_sys : ∀ M : Operator (2 ^ SpecsAux.SpecMirror.systemQubits),
      H.1 * sys.embedMatrix M = sys.embedMatrix M * H.1 := fun M ↦
    MomSlots01Slot1ProjKinetic.hadamardAll_comm_embedMatrix_slot1 pay sys hDisj_pay_sys M
  have hP_Rc : ∀ v : Fin (2 ^ mPayload),
      pay.basisOutcomeProjector v * R_c = R_c * pay.basisOutcomeProjector v := fun v ↦ by
    simp only [R_c, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal, mul_comm]
  have hP0_sys : ∀ M : Operator (2 ^ SpecsAux.SpecMirror.systemQubits),
      P_0 * sys.embedMatrix M = sys.embedMatrix M * P_0 :=
    fun M ↦ (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      sys pay (QRegExt.disjointWires_symm hDisj_pay_sys) M 0).symm
  have hRc_idem : R_c * R_c = R_c := by
    simp only [R_c, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext g; by_cases h : six.extractIndex g = coinSixOutcome c <;> simp [h]
  rw [MomSlots01Slot1ProjKinetic.ancProjector_eq_six_mul_payload mPayload c]
  change (R_c * P_0) * (H.1ᴴ * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * H.1) * (R_c * P_0) =
    (R_c * P_0) * sys.embedMatrix B_c * (R_c * P_0)
  have hLHS1 :
      (R_c * P_0) * (H.1ᴴ * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * H.1) * (R_c * P_0) =
        P_0 * H.1ᴴ * (R_c * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg) * H.1 * P_0 * R_c := by
    have hL : R_c * P_0 = P_0 * R_c := (hP_Rc 0).symm
    have hRP_dup : R_c * P_0 = R_c * (P_0 * R_c) := by
      symm; rw [← Matrix.mul_assoc, ← hP_Rc 0, Matrix.mul_assoc, hRc_idem, hP_Rc 0]
    have hHdag_Rc : R_c * H.1ᴴ = H.1ᴴ * R_c := by rw [hH_sa, ← hH_Rc]
    have hdiag_comm : R_c * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * R_c =
        R_c * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg := by
      have hc : slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * R_c =
          R_c * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg := by
        simp only [R_c, slot1PWUSelectDiag, QRegister.basisOutcomeProjector_eq_diagonal,
          Matrix.diagonal_mul_diagonal, mul_comm]
      rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, hRc_idem]
    calc (R_c * P_0) * (H.1ᴴ * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * H.1) * (R_c * P_0)
        = (P_0 * R_c) * (H.1ᴴ * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * H.1) *
          (R_c * (P_0 * R_c)) :=
            congrArg₂ HMul.hMul (congrArg₂ HMul.hMul hL rfl) hRP_dup
      _ = P_0 *
        ((R_c * H.1ᴴ) *
        (slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * ((H.1 * R_c) * (P_0 * R_c)))) := by
            simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * (R_c * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg * R_c) * H.1 * P_0 *
        R_c := by
            rw [hHdag_Rc, hH_Rc]; simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * (R_c * slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg) * H.1 * P_0 * R_c := by
            rw [hdiag_comm]
  rw [hLHS1, sixProj_mul_slot1PWUSelectDiag bSub hbLo hbHi hmPay cfg c]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  have hterm : ∀ u : Fin (2 ^ mPayload),
      P_0 * H.1ᴴ * (pay.basisOutcomeProjector u * R_c *
          sys.embedMatrix (Matrix.diagonal (fun xSys ↦
            pwuPhaseScalar bSub hbLo hbHi hmPay cfg c xSys u))) *
          H.1 * P_0 * R_c =
        (R_c * P_0) *
          (((2 : ℂ)⁻¹ ^ mPayload) •
            sys.embedMatrix (Matrix.diagonal (fun xSys ↦
              pwuPhaseScalar bSub hbLo hbHi hmPay cfg c xSys u))) *
          (R_c * P_0) := by
    intro u
    let D_u := Matrix.diagonal (fun xSys ↦ pwuPhaseScalar bSub hbLo hbHi hmPay cfg c xSys u)
    have hDu_Rc : sys.embedMatrix D_u * R_c = R_c * sys.embedMatrix D_u := by
      rw [MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
      simp only [R_c, QRegister.basisOutcomeProjector_eq_diagonal,
        Matrix.diagonal_mul_diagonal, mul_comm]
    calc P_0 * H.1ᴴ * (pay.basisOutcomeProjector u * R_c * sys.embedMatrix D_u) * H.1 * P_0 * R_c
        = P_0 * H.1ᴴ * pay.basisOutcomeProjector u * (R_c * (sys.embedMatrix D_u * H.1)) * P_0 *
          R_c := by
            simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * pay.basisOutcomeProjector u * (H.1 * R_c * sys.embedMatrix D_u) * P_0 *
        R_c := by
            rw [← hH_sys D_u, ← Matrix.mul_assoc R_c H.1, ← hH_Rc]
      _ = (P_0 * H.1ᴴ * pay.basisOutcomeProjector u * H.1 * P_0) *
            sys.embedMatrix D_u * (R_c * R_c) := by
            have hstep :
                P_0 * H.1ᴴ * pay.basisOutcomeProjector u * (H.1 * R_c * sys.embedMatrix D_u) * P_0 *
                  R_c =
                P_0 * H.1ᴴ * pay.basisOutcomeProjector u * H.1 *
                  ((R_c * (sys.embedMatrix D_u * P_0)) * R_c) := by
              simp only [Matrix.mul_assoc]
            rw [hstep, ← hP0_sys D_u, ← Matrix.mul_assoc R_c P_0, ← hP_Rc 0,
              Matrix.mul_assoc P_0 R_c (sys.embedMatrix D_u), hDu_Rc.symm]
            simp only [Matrix.mul_assoc]
      _ = (((2 : ℂ)⁻¹ ^ mPayload) • P_0) * sys.embedMatrix D_u * R_c := by
            rw [FullSysPrepare6Slot.hadamardAll_proj_zero_conj pay u, hRc_idem]
      _ = (R_c * P_0) * (((2 : ℂ)⁻¹ ^ mPayload) • sys.embedMatrix D_u) * (R_c * P_0) := by
            rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
            congr 1
            rw [MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
            simp only [P_0, R_c, QRegister.basisOutcomeProjector_eq_diagonal,
              Matrix.diagonal_mul_diagonal]
            congr 1; funext g
            by_cases h1 : pay.extractIndex g = 0 <;>
              by_cases h2 : six.extractIndex g = coinSixOutcome c <;>
              simp [h1, h2]
  rw [Finset.sum_congr rfl fun u _ ↦ hterm u, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  have hsum_emb :
      (∑ x : Fin (2 ^ mPayload),
          ((2 : ℂ)⁻¹ ^ mPayload) •
            sys.embedMatrix (Matrix.diagonal (fun xSys ↦
              pwuPhaseScalar bSub hbLo hbHi hmPay cfg c xSys x))) =
        Matrix.diagonal (fun g ↦
          ((2 : ℂ)⁻¹ ^ mPayload) *
            ∑ u : Fin (2 ^ mPayload),
              pwuPhaseScalar bSub hbLo hbHi hmPay cfg c (sys.extractIndex g) u) := by
    simp_rw [MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
    ext g₁ g₂
    by_cases hg : g₁ = g₂
    · subst hg; simp [Matrix.sum_apply, Finset.mul_sum]
    · simp [Matrix.sum_apply, hg]
  rw [hsum_emb]
  have hBc_diag :
      B_c = Matrix.diagonal (fun xSys ↦
        if c = 5 then bUnitTwosSlot1PWU bSub cfg xSys xSys else 1) := by
    ext i j
    by_cases hc5 : c = 5
    · subst hc5
      by_cases hij : i = j
      · subst hij; simp [B_c]
      · simp [B_c, bUnitTwosSlot1PWU, hij]
    · by_cases hij : i = j
      · subst hij; simp [B_c, hc5]
      · simp [B_c, hc5, Matrix.one_apply_ne hij]
  rw [hBc_diag, MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
  apply congrArg Matrix.diagonal
  funext g
  exact avg_pwuPhaseScalar_sym bSub hbLo hbHi hmPay cfg c (sys.extractIndex g)

theorem slot1PWU_hadamard_topBlock_fullSys (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) :
    let P_anc := (FullSysMomSlots0135Concrete.momAncReg mPayload).basisOutcomeProjector
      (coinSelOutcome (FullSysMomSlots0135Concrete.momCoin3Sel mPayload)
        (FullSysPrepare6Slot.fullSysCoinIdx 1))
    P_anc * (unitaryConj (FullSysMomSlots0135Concrete.coreHadamardMom mPayload)
        (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg)).1 *
      P_anc =
      P_anc * (FullSysMomSlots0135Concrete.momSysReg mPayload).embedMatrix
        (bUnitTwosSlot1PWU bSub cfg) * P_anc := by
  simpa [show FullSysPrepare6Slot.fullSysCoinIdx 1 = 5 from rfl] using
    slot1PWU_hadamard_topBlock_all bSub hbLo hbHi hmPay cfg 5

end Slot1PWUPart3BIrred


private theorem abs_pwuValBranch_le_one (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) :
    |pwuValBranch cfg xSys b| ≤ 1 := by
  unfold pwuValBranch
  dsimp only
  let w : Fin 3 := ⟨b.val / 2, by omega⟩
  let u8 := u8FromFin (projAxisField xSys w)
  obtain ⟨hp7_nn, hp7_le⟩ := pwuSlot1_bounds u8
  obtain ⟨hp14_nn, hp14_le⟩ := pwuP14_bounds u8
  obtain ⟨hp21_nn, hp21_le⟩ := pwuP21_bounds u8
  split_ifs
  · have hprod_le : pwuSlot1 u8 * pwuP14 u8 ≤ 1 := by nlinarith
    have hprod_nn : 0 ≤ pwuSlot1 u8 * pwuP14 u8 := mul_nonneg hp7_nn hp14_nn
    rw [abs_le]
    constructor <;> linarith
  · rw [abs_mul, abs_neg_one_pow_dyadic, one_mul, abs_of_nonneg hp21_nn]
    exact hp21_le

theorem norm_bUnitTwosSlot1PWU_le_one (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) :
    ‖bUnitTwosSlot1PWU bSub cfg‖ ≤ 1 := by
  refine l2_opNorm_diagonal_le _ 1 zero_le_one fun xSys ↦ ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hsum_abs :
      |∑ b : Fin 6, ((pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3)) * pwuValBranch cfg xSys b| ≤
        ∑ b : Fin 6, ((pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ ↦ ?_)
    have hd_nn : (0 : ℝ) ≤ (pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3) := by positivity
    rw [abs_mul, abs_of_nonneg hd_nn]
    exact mul_le_of_le_one_right hd_nn (abs_pwuValBranch_le_one cfg xSys b)
  have hsum_nat : (∑ b : Fin 6, pwuDelta bSub cfg b) ≤ 2 ^ (bSub + 3) := by
    have hlt := le_of_lt (pwu_used_lt_two_pow hbLo hbHi cfg)
    have hsum6 : (∑ b : Fin 6, pwuDelta bSub cfg b) =
        pwuTq bSub + pwuDl bSub cfg 0 + pwuTq bSub + pwuDl bSub cfg 1 +
          pwuTq bSub + pwuDl bSub cfg 2 := by
      rw [Fin.sum_univ_six]; try rfl
    rw [hsum6]; omega
  have hsum_real : (∑ b : Fin 6, (pwuDelta bSub cfg b : ℝ)) ≤ (2 : ℝ) ^ (bSub + 3) := by
    exact_mod_cast hsum_nat
  have hsum_le1 : (∑ b : Fin 6, ((pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3))) ≤ 1 := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact hsum_real
  exact hsum_abs.trans hsum_le1

theorem bUnitTwosSlot1PWU_permElectron (bSub : ℕ) (cfg : Configuration)
    (g : Equiv.Perm (Fin numElectrons))
    (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hx : IsGridState x) (_hy : IsGridState y) :
    (smToTwosSysUnitary.1 * bUnitTwosSlot1PWU bSub cfg * smToTwosSysUnitary.1)
        (permElectron g x) (permElectron g y) =
      (smToTwosSysUnitary.1 * bUnitTwosSlot1PWU bSub cfg * smToTwosSysUnitary.1) x y := by
  rw [bUnitTwosSlot1PWU, MomSlots01Slot1ProjKinetic.smToTwosSys_conj_diagonal_slot1]
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply]
    have hxg : IsGridState (permElectron g x) := (isGridState_permElectron g x).mpr hx
    have hproj_eq : ∀ w : Fin 3,
        projAxisField (smToTwosSysPerm (permElectron g x)) w =
          projAxisField (smToTwosSysPerm x) w := fun w ↦ by
      apply twosComp8Int_injective
      rw [twosComp8_smToTwosSys_eq_momentum hxg w,
        twosComp8_smToTwosSys_eq_momentum hx w,
        momentum_permElectron_projectile]
    apply congrArg Complex.ofReal
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    unfold pwuValBranch
    dsimp only
    rw [hproj_eq]
  · have hne : permElectron g x ≠ permElectron g y :=
      fun heq ↦ hxy ((permElectron g).injective heq)
    rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hxy]


private theorem abs_pwu_quad_weight_err_three (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) :
    3 * |lambdaSlot1TpHi * ((pwuTq bSub : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
        slot1QuadBranchWeight / (pwuC7 * pwuC14)| ≤
      (pwuQuadErr3Num bSub : ℝ) / 1000000000 := by
  have hc714 : 0 < pwuC7 * pwuC14 := mul_pos pwuC7_pos pwuC14_pos
  have hlo : (((16129 / 2 : ℝ) * (gridKappaRatLo ^ 2 / 2)) / projectileMass) / (pwuC7 * pwuC14) ≤
      slot1QuadBranchWeight / (pwuC7 * pwuC14) :=
    div_le_div_of_nonneg_right slot1QuadBranchWeight_ge_ratLo hc714.le
  have hhi : slot1QuadBranchWeight / (pwuC7 * pwuC14) ≤
      (((16129 / 2 : ℝ) * (gridKappaRatHi ^ 2 / 2)) / projectileMass) / (pwuC7 * pwuC14) :=
    div_le_div_of_nonneg_right slot1QuadBranchWeight_le_ratHi hc714.le
  have h1 : 3 * (lambdaSlot1TpHi * ((pwuTq bSub : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
      (((16129 / 2 : ℝ) * (gridKappaRatLo ^ 2 / 2)) / projectileMass) / (pwuC7 * pwuC14)) ≤
      (pwuQuadErr3Num bSub : ℝ) / 1000000000 := by
    rcases (by omega : bSub = 18 ∨ bSub = 19 ∨ bSub = 20 ∨ bSub = 21 ∨ bSub = 22 ∨ bSub = 23 ∨
      bSub = 24) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (unfold pwuTq pwuQuadErr3Num lambdaSlot1TpHi gridKappaRatLo projectileMass pwuC7 pwuC14;
        push_cast; norm_num)
  have h2 : -((pwuQuadErr3Num bSub : ℝ) / 1000000000) ≤
      3 * (lambdaSlot1TpHi * ((pwuTq bSub : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
        (((16129 / 2 : ℝ) * (gridKappaRatHi ^ 2 / 2)) / projectileMass) / (pwuC7 * pwuC14)) := by
    rcases (by omega : bSub = 18 ∨ bSub = 19 ∨ bSub = 20 ∨ bSub = 21 ∨ bSub = 22 ∨ bSub = 23 ∨
      bSub = 24) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (unfold pwuTq pwuQuadErr3Num lambdaSlot1TpHi gridKappaRatHi projectileMass pwuC7 pwuC14;
        push_cast; norm_num)
  have habs : |lambdaSlot1TpHi * ((pwuTq bSub : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
      slot1QuadBranchWeight / (pwuC7 * pwuC14)| ≤
      ((pwuQuadErr3Num bSub : ℝ) / 1000000000) / 3 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

private theorem abs_lambda_mul_pwu_lin_sum (bSub : ℕ) (cfg : Configuration) :
    |lambdaSlot1TpHi * ((pwuDl bSub cfg 0 : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
        slot1LinBranchWeight cfg 0 / pwuC21| +
      |lambdaSlot1TpHi * ((pwuDl bSub cfg 1 : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
        slot1LinBranchWeight cfg 1 / pwuC21| +
      |lambdaSlot1TpHi * ((pwuDl bSub cfg 2 : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
        slot1LinBranchWeight cfg 2 / pwuC21| ≤
      (3 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ (bSub + 3)) := by
  have hlam_pos : (0 : ℝ) < lambdaSlot1TpHi := by unfold lambdaSlot1TpHi; norm_num
  have hscale : (0 : ℝ) < lambdaSlot1TpHi / (2 : ℝ) ^ (bSub + 3) := by positivity
  have herr_w : ∀ w : Fin 3, |(pwuDl bSub cfg w : ℝ) - pwuXLin bSub cfg w| ≤ 1 / 2 := fun w ↦ by
    have hx := pwuXLin_nonneg bSub cfg w
    have hle : (pwuDl bSub cfg w : ℝ) ≤ pwuXLin bSub cfg w + 1 / 2 :=
      Nat.floor_le (by linarith)
    have hgt : pwuXLin bSub cfg w - 1 / 2 < (pwuDl bSub cfg w : ℝ) := by
      unfold pwuDl; linarith [Nat.lt_floor_add_one (pwuXLin bSub cfg w + 1 / 2)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hrew : ∀ w : Fin 3,
      |lambdaSlot1TpHi * ((pwuDl bSub cfg w : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
          slot1LinBranchWeight cfg w / pwuC21| =
        (lambdaSlot1TpHi / (2 : ℝ) ^ (bSub + 3)) *
          |(pwuDl bSub cfg w : ℝ) - pwuXLin bSub cfg w| := fun w ↦ by
    have heq : lambdaSlot1TpHi * ((pwuDl bSub cfg w : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
        slot1LinBranchWeight cfg w / pwuC21 =
      (lambdaSlot1TpHi / (2 : ℝ) ^ (bSub + 3)) *
        ((pwuDl bSub cfg w : ℝ) - pwuXLin bSub cfg w) := by
      unfold pwuXLin
      field_simp [hlam_pos.ne']
    rw [heq, abs_mul, abs_of_pos hscale]
  rw [hrew 0, hrew 1, hrew 2, ← mul_add, ← mul_add]
  have h0 := herr_w 0
  have h1 := herr_w 1
  have h2 := herr_w 2
  nlinarith

theorem bUnitTwosSlot1PWU_fermionic_err_le
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (epsCap : ℝ)
    (heps : (pwuQuadErr3Num bSub : ℝ) / 1000000000 +
      (3 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ (bSub + 3)) ≤ epsCap)
    (cfg : SpecsAux.SpecMirror.Configuration)
    (spinUp : Finset (Fin numElectrons))
    (E : Fin 6 → ℝ) (hE1 : E 1 = pwuEShift cfg) :
    ‖SpecsAux.SpecMirror.fermionicProjector spinUp *
        ((lambdaSlot1TpHi : ℂ) •
            (smToTwosSysUnitary.1 * bUnitTwosSlot1PWU bSub cfg * smToTwosSysUnitary.1) -
          sixChannelShifted cfg E 1) *
        SpecsAux.SpecMirror.fermionicProjector spinUp‖ ≤
      epsCap := by
  let P_F := SpecsAux.SpecMirror.fermionicProjector spinUp
  let G := SpecsAux.gridProjector
  let Δ := (lambdaSlot1TpHi : ℂ) •
      (smToTwosSysUnitary.1 * bUnitTwosSlot1PWU bSub cfg * smToTwosSysUnitary.1) -
    sixChannelShifted cfg E 1
  have hlam_pos : (0 : ℝ) < lambdaSlot1TpHi := by unfold lambdaSlot1TpHi; norm_num
  have heps_nonneg : 0 ≤ epsCap := by
    have hpos : 0 ≤ (pwuQuadErr3Num bSub : ℝ) / 1000000000 +
        (3 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ (bSub + 3)) := by positivity
    linarith
  have hPF_G : P_F * G = P_F := SpecsAux.fermionicProjector_mul_gridProjector spinUp
  have hG_PF : G * P_F = P_F :=
    (SpecsAux.commute_fermionicProjector_gridProjector spinUp).symm.trans hPF_G
  have hwrap : P_F * Δ * P_F = P_F * (G * Δ * G) * P_F := by
    calc P_F * Δ * P_F
        = (P_F * G) * Δ * (G * P_F) := by rw [hPF_G, hG_PF]
      _ = P_F * (G * Δ * G) * P_F := by simp only [Matrix.mul_assoc]
  rw [hwrap]
  have hGΔG_diag : G * Δ * G =
      Matrix.diagonal (fun x ↦
        open Classical in
        if IsGridState x then
          (((lambdaSlot1TpHi *
              (∑ b : Fin 6, ((pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3)) *
                pwuValBranch cfg (smToTwosSysPerm x) b) -
            (waveNumberSq (SpecsAux.SpecMirror.momentum x .projectile - cfg.projectileMomentum) /
              (2 * projectileMass) - pwuEShift cfg)) : ℝ) : ℂ)
        else 0) := by
    have hraw : sixChannelRaw cfg 1 = projectileKineticOp cfg :=
      (projectileKineticOp_eq_matrixOf cfg).symm
    have hshift_diag : sixChannelShifted cfg E 1 =
        Matrix.diagonal (fun x ↦
          open Classical in
          if IsGridState x then
            (((waveNumberSq (SpecsAux.SpecMirror.momentum x .projectile - cfg.projectileMomentum) /
              (2 * projectileMass) - pwuEShift cfg) : ℝ) : ℂ)
          else 0) := by
      classical
      unfold sixChannelShifted
      rw [hraw, hE1, sixChannelGridProjector_eq_specsGridProjector]
      ext x y
      unfold projectileKineticOp SpecsAux.gridProjector
      by_cases hxy : x = y
      · subst hxy
        by_cases hx : IsGridState x <;> simp [hx]
      · simp [hxy]
    change G * ((lambdaSlot1TpHi : ℂ) •
        (smToTwosSysUnitary.1 * bUnitTwosSlot1PWU bSub cfg * smToTwosSysUnitary.1) -
      sixChannelShifted cfg E 1) * G = _
    rw [hshift_diag, bUnitTwosSlot1PWU,
      MomSlots01Slot1ProjKinetic.smToTwosSys_conj_diagonal_slot1]
    classical
    unfold G SpecsAux.gridProjector
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : IsGridState x <;> simp [hx]
    · simp [hxy]
  have hGΔG_norm : ‖G * Δ * G‖ ≤ epsCap := by
    rw [hGΔG_diag]
    refine l2_opNorm_diagonal_le _ _ heps_nonneg fun x ↦ ?_
    classical
    split_ifs with hx
    · rw [Complex.norm_real, Real.norm_eq_abs]
      have hsub_shift :
          waveNumberSq (SpecsAux.SpecMirror.momentum x .projectile - cfg.projectileMomentum) /
              (2 * projectileMass) - pwuEShift cfg =
            (waveNumberSq (SpecsAux.SpecMirror.momentum x .projectile - cfg.projectileMomentum) /
              (2 * projectileMass) - projMidpointOffset cfg) -
            3 * slot1QuadBranchWeight * (1 / (pwuC7 * pwuC14) - 1) := by
        unfold pwuEShift; ring
      rw [hsub_shift, ← sum_projAxisTerm_eq_centered cfg x]
      have haxis_ne128 : ∀ w : Fin 3, (projAxisField (smToTwosSysPerm x) w).val ≠ 128 := by
        intro w h128
        have hmom := twosComp8_smToTwosSys_eq_momentum hx w
        have h128_int : twosComp8Int (projAxisField (smToTwosSysPerm x) w) = -128 := by
          unfold twosComp8Int; rw [h128]; norm_num
        rw [h128_int] at hmom
        have hle127 := abs_momentum_projectile_le_127 x w
        rw [← hmom] at hle127
        norm_num at hle127
      have haxis_int : ∀ w : Fin 3,
          slot1AxisInt (projAxisField (smToTwosSysPerm x) w) =
            SpecsAux.SpecMirror.momentum x .projectile w := by
        intro w
        unfold slot1AxisInt
        rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 (haxis_ne128 w)]
        exact twosComp8_smToTwosSys_eq_momentum hx w
      have hcent_eq :
          (∑ w : Fin 3, projAxisTerm cfg (SpecsAux.SpecMirror.momentum x .projectile w) w) -
              3 * slot1QuadBranchWeight * (1 / (pwuC7 * pwuC14) - 1) =
            ∑ b : Fin 6, pwuEffBranchWeight cfg b * pwuValBranch cfg (smToTwosSysPerm x) b := by
        rw [pwuEffBranchWeight_mul_pwuValBranch_sum,
          slot1BranchWeight_mul_idealVal_sum cfg (smToTwosSysPerm x)]
        congr 1
        exact Finset.sum_congr rfl fun w _ ↦ by rw [haxis_int w]
      rw [hcent_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
      have hterm : ∀ b : Fin 6,
          |lambdaSlot1TpHi * (((pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3)) *
              pwuValBranch cfg (smToTwosSysPerm x) b) -
            pwuEffBranchWeight cfg b * pwuValBranch cfg (smToTwosSysPerm x) b| ≤
          |lambdaSlot1TpHi * ((pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
            pwuEffBranchWeight cfg b| := fun b ↦ by
        have hfac :
            lambdaSlot1TpHi * (((pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3)) *
                pwuValBranch cfg (smToTwosSysPerm x) b) -
              pwuEffBranchWeight cfg b * pwuValBranch cfg (smToTwosSysPerm x) b =
            (lambdaSlot1TpHi * ((pwuDelta bSub cfg b : ℝ) / (2 : ℝ) ^ (bSub + 3)) -
              pwuEffBranchWeight cfg b) * pwuValBranch cfg (smToTwosSysPerm x) b := by ring
        rw [hfac, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (abs_pwuValBranch_le_one cfg (smToTwosSysPerm x) b)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun b _ ↦ hterm b).trans ?_)
      rw [sum_fin6_real]
      have hd0 : pwuDelta bSub cfg 0 = pwuTq bSub := rfl
      have hd1 : pwuDelta bSub cfg 1 = pwuDl bSub cfg 0 := rfl
      have hd2 : pwuDelta bSub cfg 2 = pwuTq bSub := rfl
      have hd3 : pwuDelta bSub cfg 3 = pwuDl bSub cfg 1 := rfl
      have hd4 : pwuDelta bSub cfg 4 = pwuTq bSub := rfl
      have hd5 : pwuDelta bSub cfg 5 = pwuDl bSub cfg 2 := rfl
      have hew0 : pwuEffBranchWeight cfg 0 = slot1QuadBranchWeight / (pwuC7 * pwuC14) := rfl
      have hew1 : pwuEffBranchWeight cfg 1 = slot1LinBranchWeight cfg 0 / pwuC21 := rfl
      have hew2 : pwuEffBranchWeight cfg 2 = slot1QuadBranchWeight / (pwuC7 * pwuC14) := rfl
      have hew3 : pwuEffBranchWeight cfg 3 = slot1LinBranchWeight cfg 1 / pwuC21 := rfl
      have hew4 : pwuEffBranchWeight cfg 4 = slot1QuadBranchWeight / (pwuC7 * pwuC14) := rfl
      have hew5 : pwuEffBranchWeight cfg 5 = slot1LinBranchWeight cfg 2 / pwuC21 := rfl
      rw [hd0, hd1, hd2, hd3, hd4, hd5, hew0, hew1, hew2, hew3, hew4, hew5]
      have hqw := abs_pwu_quad_weight_err_three bSub hbLo hbHi
      have hlw := abs_lambda_mul_pwu_lin_sum bSub cfg
      linarith
    · rw [norm_zero]
      exact heps_nonneg
  exact (MomSlots01Slot1ProjKinetic.norm_sandwich_le_of_norm_le_one P_F (G * Δ * G)
    (norm_fermionicProjector_le_one spinUp)).trans hGΔG_norm

end ConfigMomSlot1WalkerAliasPWU24
end Dir3TwistSlot1Junction.MomSlot1WalkerAliasPWU24

namespace Dir3TwistSlot1Junction.MomSlot1WalkerAliasPWU24
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm PosMomSelectSandwich
open PosMomSelectDynamic SingleRBEGridGuardWalk
open SixSlotEndpointJunctionBridge
open FullSysPrepare6Slot
open FullSysPosSlots24AndTopConcrete
open TwosCompAndWire0Cancel
open LiteralKineticAndMidpoint128
open MomSlots01Slot1ProjKinetic
open MomSlot1GeomPriority288
open MomSlot1Dyadic459Sub36w
open Dir3TwistSlot1Junction

open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelRaw sixChannelShifted)
open InPlaceFullAddSlice (bit_cases)
open scoped Matrix BigOperators Matrix.Norms.L2Operator

section ConfigMomAffMom1PwuAff4
set_option exponentiation.threshold 8192

abbrev pwuTCostR1 (bSub : ℕ) : ℕ := 4 * (bSub + 51)

def pwuSt12aR1 : SsaProg 185 164 165 :=
  writeXor 164 (by decide) true
    [(true, ⟨⟨139, by decide⟩, by decide⟩),
     (true, ⟨⟨163, by decide⟩, by decide⟩)]

def pwuBlockCPrioRawR1 (bSub : ℕ) (hbHi : bSub ≤ 24) : SsaProg 185 157 179 :=
  (pwuSt11a bSub hbHi).append <| (pwuSt11b bSub hbHi).append <|
    pwuSt12aR1.append (pwuSt12b bSub hbHi)

noncomputable def pwuBlockCPrioR1 (bSub : ℕ) (hbHi : bSub ≤ 24) : SsaProg 185 157 179 :=
  lockValWalker (pwuBlockCPrioRawR1 bSub hbHi)

private theorem pwuBlockCPrioR1_countAnd (bSub : ℕ) (hbHi : bSub ≤ 24) :
    (pwuBlockCPrioR1 bSub hbHi).countAnd = 21 := by
  rw [pwuBlockCPrioR1, lockValWalker_eq]
  simp only [pwuBlockCPrioRawR1, pwuSt11a, pwuSt11b, pwuSt12aR1, pwuSt12b,
    SsaProg.append_countAnd, andPol_countAnd, writeXor_countAnd, prioChainStar_countAnd]

private theorem pwuBlockCPrioR1_spec (bSub : ℕ) (hbHi : bSub ≤ 24) (u8 : Fin 8 → ZMod 2)
    (β : BitAssignment 185)
    (hz : ∀ w : Wire 185, 157 ≤ w.val → β w = 0)
    (hmag : ∀ b : Fin 7, β (wMag7PWU b) = mag7Bit u8 b) :
    let outS := pwuChainEval7 0 u8 (fun i : Fin 7 ↦ β ⟨47 + bSub + i.val, by omega⟩)
    (∀ w : Wire 185, w.val < 157 → (pwuBlockCPrioR1 bSub hbHi).eval β w = β w) ∧
    (∀ w : Wire 185, 179 ≤ w.val → (pwuBlockCPrioR1 bSub hbHi).eval β w = 0) ∧
    (pwuBlockCPrioR1 bSub hbHi).eval β ⟨163, by decide⟩ = outS ∧
    (pwuBlockCPrioR1 bSub hbHi).eval β ⟨178, by decide⟩ =
      pwuChainEval14 (1 + β ⟨139, by decide⟩ + outS) u8
        (fun i : Fin 14 ↦ β ⟨33 + bSub + i.val, by omega⟩) := by
  exact pwuBlockCPrioGen_spec bSub hbHi pwuSt12aR1 (pwuBlockCPrioR1 bSub hbHi)
    (fun a b ↦ 1 + a + b) (by
      unfold pwuBlockCPrioR1 pwuBlockCPrioRawR1
      rfl)
    (writeXor_preserves 164 (by decide) _ _)
    (fun γ hγ ↦ by
      dsimp only [pwuSt12aR1]
      rw [writeXor_eval _ _ _ _ γ hγ, Function.update_self]
      dsimp only [listXorSum]
      simp only [↓reduceIte, b2z, add_zero]
      ring)
    u8 β hz hmag

attribute [local irreducible] pwuSt12aR1 pwuBlockCPrioR1

noncomputable def dInnerSsaRawR1 (bSub : ℕ) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 151 185 :=
  pwuBlockBMag7.append <| (pwuBlockCPrioR1 bSub hbHi).append (pwuBlockDCombine cfg)

noncomputable def dInnerSsaR1 (bSub : ℕ) (hbHi : bSub ≤ 24)
    (cfg : Configuration) : SsaProg 185 151 185 :=
  lockValWalker (dInnerSsaRawR1 bSub hbHi cfg)

private theorem dInnerSsaR1_countAnd (bSub : ℕ) (hbHi : bSub ≤ 24) (cfg : Configuration) :
    (dInnerSsaR1 bSub hbHi cfg).countAnd = 32 := by
  rw [dInnerSsaR1, lockValWalker_eq]
  simp only [dInnerSsaRawR1, SsaProg.append_countAnd,
    pwuBlockBMag7_countAnd, pwuBlockCPrioR1_countAnd, pwuBlockDCombine_countAnd]

private theorem r1_pwuOutR110_affine_seed_mul_mux_eq
    (bSub : ℕ) (hbHi : bSub ≤ 24) (α : BitAssignment 110) (u8 : Fin 8 → ZMod 2)
    (lf : Fin 8) (hlf3 : lf ≠ 3) (outS cHalf : ZMod 2) :
    pwuOutR110 bSub hbHi (1 + b2z (decide (4 ≤ lf.val)) + outS) α u8 *
        (if b2z (decide (4 ≤ lf.val)) +
            b2z (decide ((lf.val / 2) % 2 = 1)) * b2z (decide (lf.val % 2 = 1)) = 1 then
          cHalf
        else outS) =
      pwuOutR110 bSub hbHi (b2z (decide (4 ≤ lf.val)) * outS) α u8 *
        (if b2z (decide (4 ≤ lf.val)) +
            b2z (decide ((lf.val / 2) % 2 = 1)) * b2z (decide (lf.val % 2 = 1)) = 1 then
          cHalf
        else outS) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases bit_cases outS with rfl | rfl
  all_goals
    fin_cases lf
    all_goals first | exact absurd rfl hlf3 | simp [b2z, h11]

private theorem dInnerSsaR1_eval_kick (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (cfg : Configuration) (α : BitAssignment 110) :
    (dInnerSsaR1 bSub hbHi cfg).eval
      (Mux3AnchoredPwu.writeMux8_185 ((pwuOuterSsa bSub hbLo hbHi cfg).eval (padZeroBits (mClean :=
        75) α)))
      ⟨182, by decide⟩ *
    (dInnerSsaR1 bSub hbHi cfg).eval
      (Mux3AnchoredPwu.writeMux8_185 ((pwuOuterSsa bSub hbLo hbHi cfg).eval (padZeroBits (mClean :=
        75) α)))
      ⟨184, by decide⟩ =
      slot1PWUPred110 bSub hbLo hbHi cfg α := by
  exact dInnerSsaGen_eval_kick bSub hbLo hbHi cfg (dInnerSsaR1 bSub hbHi cfg)
    (pwuBlockCPrioR1 bSub hbHi) (fun a b ↦ 1 + a + b)
    (by
      unfold dInnerSsaR1 dInnerSsaRawR1
      rfl)
    (pwuBlockCPrioR1_spec bSub hbHi) α
    (fun u8 lf hlf3 outS cH ↦
      r1_pwuOutR110_affine_seed_mul_mux_eq bSub hbHi α u8 lf hlf3 outS cH)

attribute [local irreducible] dInnerSsaR1

noncomputable def dSlot1PWUCoreDynRawR1 (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : pwuWorkWires ≤ mWork)
    (cfg : Configuration) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n)
    (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) : DynamicCircuit Var n :=
  Mux3AnchoredPwu.compileAnchoredMux3PwuDyn v
    (rCore.compose (rActCore hmPay)) rWork
    (hdisj.compose_left (rActCore hmPay)) hw_len
    (pwuOuterSsa bSub hbLo hbHi cfg)
    (dInnerSsaR1 bSub hbHi cfg)
    ⟨182, by decide⟩ ⟨184, by decide⟩ (Fin.ne_of_val_ne (by decide))

noncomputable def dSlot1PWUCoreDynR1 (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : pwuWorkWires ≤ mWork)
    (cfg : Configuration) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n)
    (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) : DynamicCircuit Var n :=
  lockValWalker (dSlot1PWUCoreDynRawR1 bSub hbLo hbHi hmPay hw_len cfg v rCore rWork hdisj)

theorem dSlot1PWUCoreDynR1_count_toff (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : pwuWorkWires ≤ mWork)
    (cfg : Configuration) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n)
    (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    (dSlot1PWUCoreDynR1 bSub hbLo hbHi hmPay hw_len cfg v rCore rWork hdisj).count
      PrimitiveGate.TOFF = 0 := by
  rw [dSlot1PWUCoreDynR1, lockValWalker_eq]
  exact Mux3AnchoredPwu.compileAnchoredMux3PwuDyn_count_toff v _ _ _ hw_len _ _ _ _ _

theorem dSlot1PWUCoreDynR1_count_t (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : pwuWorkWires ≤ mWork)
    (cfg : Configuration) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n)
    (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    (dSlot1PWUCoreDynR1 bSub hbLo hbHi hmPay hw_len cfg v rCore rWork hdisj).count PrimitiveGate.T =
      pwuTCostR1 bSub := by
  rw [dSlot1PWUCoreDynR1, lockValWalker_eq]
  dsimp only [dSlot1PWUCoreDynRawR1, pwuTCostR1]
  rw [Mux3AnchoredPwu.compileAnchoredMux3PwuDyn_count_t, pwuOuterSsa_countAnd, dInnerSsaR1_countAnd]
  omega

theorem dSlot1PWUCoreDynR1_realizes (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWork : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hw_len : pwuWorkWires ≤ mWork)
    (cfg : Configuration) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n)
    (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rCore rWork (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg)
      (dSlot1PWUCoreDynR1 bSub hbLo hbHi hmPay hw_len cfg v rCore rWork hdisj) := by
  rw [dSlot1PWUCoreDynR1, lockValWalker_eq,
    ← embedUnitary_phaseDiagAct_eq_slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg]
  exact (Mux3AnchoredPwu.realizes_compileAnchoredMux3PwuDyn v
    (rCore.compose (rActCore hmPay)) rWork
    (hdisj.compose_left (rActCore hmPay)) hw_len
    (pwuOuterSsa bSub hbLo hbHi cfg) (dInnerSsaR1 bSub hbHi cfg)
    ⟨182, by decide⟩ ⟨184, by decide⟩ (Fin.ne_of_val_ne (by decide))
    (slot1PWUPred110 bSub hbLo hbHi cfg)
    (pwuOuterSsa_orth bSub hbLo hbHi cfg)
    (dInnerSsaR1_eval_kick bSub hbLo hbHi cfg)).widenActive

attribute [local irreducible] dSlot1PWUCoreDynR1

noncomputable def slot1PWUOracleSymR1 (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (epsCap : ℝ)
    (heps : (pwuQuadErr3Num bSub : ℝ) / 1000000000 +
      (3 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ (bSub + 3)) ≤ epsCap)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    FullSysMomSlots0135Concrete.MomSingleSlotCircuit mPayload 48 1 :=
  FullSysMomSlots0135Concrete.MomSingleSlotCircuit.ofCoreOnly
    (mPayload := mPayload) (mPGTwist := 48) (k := 1)
    pwuWorkWires
    (pwuTCostR1 bSub)
    (fun _ ↦ lambdaSlot1TpHi)
    pwuEShift
    epsCap
    (slot1PWUSelectUnitary bSub hbLo hbHi hmPay)
    (bUnitTwosSlot1PWU bSub)
    (fun cfg {Var} {n} v rC rW hCW ↦
      dSlot1PWUCoreDynR1 bSub hbLo hbHi hmPay le_rfl cfg v rC rW hCW)
    (fun _ ↦ by unfold lambdaSlot1TpHi; norm_num)
    (fun cfg {Var} {n} v rC rW hCW ↦
      dSlot1PWUCoreDynR1_count_toff bSub hbLo hbHi hmPay le_rfl cfg v rC rW hCW)
    (fun cfg {Var} {n} v rC rW hCW ↦
      le_of_eq (dSlot1PWUCoreDynR1_count_t bSub hbLo hbHi hmPay le_rfl cfg v rC rW hCW))
    (fun cfg {Var} [Fintype Var] [DecidableEq Var] {n} [NeZero (2 ^ n)] v rC rW hCW ↦
      dSlot1PWUCoreDynR1_realizes bSub hbLo hbHi hmPay le_rfl cfg v rC rW hCW)
    (fun cfg ↦ slot1PWUSelectUnitary_sa bSub hbLo hbHi hmPay cfg)
    (fun cfg ↦
      let hP := MomSlots01Slot1ProjKinetic.momCoinProj_eq_fullSys mPayload
        (FullSysPrepare6Slot.fullSysCoinIdx 1)
      (congrArg (fun P ↦
        (slot1PWUSelectUnitary bSub hbLo hbHi hmPay cfg).1 * (1 - P)) hP.symm).trans
        ((slot1PWUSelectUnitary_offCoin bSub hbLo hbHi hmPay cfg).trans
          (congrArg (fun P ↦ 1 - P) hP)))
    (slot1PWU_hadamard_topBlock_fullSys bSub hbLo hbHi hmPay)
    (norm_bUnitTwosSlot1PWU_le_one bSub hbLo hbHi)
    (bUnitTwosSlot1PWU_permElectron bSub)
    (fun cfg spinUp ↦ by
      intro E_vec
      exact bUnitTwosSlot1PWU_fermionic_err_le bSub hbLo hbHi epsCap heps cfg spinUp E_vec
        (by simp [E_vec]))

end ConfigMomAffMom1PwuAff4
end Dir3TwistSlot1Junction.MomSlot1WalkerAliasPWU24

namespace Dir3TwistSlot1Junction.MomSlot1WalkerAliasPWU24
open SpecsAux
open Dir3TwistSlot1Junction

section ParameterizedScheduleAPI
set_option maxRecDepth 512
set_option exponentiation.threshold 8192

open SpecsAux.SpecMirror
open LiteralKineticAndMidpoint128 (lambdaSlot1TpHi)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)

/-- Tight integer numerator (in units of `10⁻⁹` Ha) for the Slot 1 PWU24 intrinsic error
at sub-bit precision `bSub ∈ {18..24}`. -/
def eps1Pwu24Num (bSub : ℕ) : ℕ :=
  match bSub with
  | 18 => 425375
  | 19 => 276971
  | 20 => 94042
  | 21 => 56941
  | 22 => 35814
  | 23 => 10565
  | _  => 5927

theorem eps1Pwu24Num_heps (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) :
    (pwuQuadErr3Num bSub : ℝ) / 1000000000 +
      (3 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ (bSub + 3)) ≤
      (eps1Pwu24Num bSub : ℝ) / 1000000000 := by
  interval_cases bSub <;>
    (dsimp [eps1Pwu24Num, pwuQuadErr3Num]
     unfold lambdaSlot1TpHi
     push_cast
     norm_num)

/-- Full circuit-bearing 75-wire R1 affine-4 Slot 1 PWU24 oracle for `bSub ∈ {18..24}`. -/
noncomputable def ora1Pwu24OfBSubFull (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    FullSysMomSlots0135Concrete.MomSingleSlotCircuit mPayload 48 1 :=
  slot1PWUOracleSymR1 bSub hbLo hbHi
    ((eps1Pwu24Num bSub : ℝ) / 1000000000)
    (eps1Pwu24Num_heps bSub hbLo hbHi) hmPay

/-- Parameterized 75-wire R1 affine-4 Slot 1 PWU24 oracle for any `bSub ∈ {18..24}`. -/
noncomputable def ora1Pwu24OfBSub (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    MomSingleSlotOracle mPayload 48 1 :=
  (ora1Pwu24OfBSubFull bSub hbLo hbHi hmPay).toMomSingleSlotOracle

theorem ora1Pwu24OfBSub_epsIntr_le (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (ora1Pwu24OfBSub bSub hbLo hbHi hmPay).epsIntr ≤ (eps1Pwu24Num bSub : ℝ) / 1000000000 :=
  le_rfl

end ParameterizedScheduleAPI

end Dir3TwistSlot1Junction.MomSlot1WalkerAliasPWU24

-- ============================================================================
-- Part 3: Slot 1 PWU24 HadCut Leaf Spec, Commutation Certificates & SelectOra Bundle
-- ============================================================================

namespace Dir3TwistSlot1Junction.Slot1Pwu24Bridge

section ConfigSlot1Pwu24Bridge
set_option maxRecDepth 512
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency true

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux
-- Root solution namespace already active.
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

local instance (priority := 1000000) instNeZero_Slot1Pwu24_Bridge (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open scoped BigOperators Matrix
open SpecsAux.SpecMirror
open Dir3TwistSlot1Junction.MomSlot1WalkerAliasPWU24
open HoistedSwapSelectBridge (unitaryConj FullSysHoistedSelectBundle)
open PosMomSelectSandwich (slotBitProj slotBitProj_conjTranspose)
open FullSysPrepare6Slot (fullSysCoinIdx)
open FullSysCatSegmentBridge
  (fullSysCoreWires iSlot0 iSlot1 iSlot2 slotBitProj_zero_add_one
   FullSysSelectOracleBundle fullSys_zero_add_le_of_le)
open FullSysMomSlots0135Concrete
  (MomSingleSlotOracle momCoreWires momCoinProj coinBitFin2 iSlot0Mom iSlot1Mom)
open FullSysHoistedSelectStitch (HoistedBarrelSpec)
open MomSlot0LocalAndMomCombine288
  (slot0LocalWorkWires MomLocalSlotData slot0LocalPhaseBit)
open OraAndPrepBundle
  (coreUnitaryToFullSys catUnitaryToFullSys coreUnitaryFromFullSys
   momCoreWires_eq_fullSysCoreWires momCatWires_eq_fullSysCatWires)
open TierClosure
  (castNatUnitary_comm_slotBitProj mkSlot0LocalDataOfBarrelFast liftSlot3OfBarrelFast)
open TierBClean80Closure (tierBBarrel80)
open GeneralBetaAndAlphaTopEndpoint (zeroMomSlotOracle5)
open NuclearTwistAndXor654Concrete (mWorkTwist wSlot2)
open NuclearTwistRealizes (xor32BitFn)
open ProjZ512QftAndTwist288 (rCoreBlock48)
open CoinDispatchedBarrel288 (uBarrelFast uBarrelFast_comm_high_wire)
open LiteralKineticAndMidpoint128 (lambdaSlot0TeHi)
open Barrel3PassCommuteHelpers (uSlot0LocalXorBit5)
open Barrel3PassSelectStitch
  (CTLeafSpec rCTSeg rCoreSeg rCoreInCT80)
open SchedBranchStitchGen
  (p1_ite_true p1_ite_false dyadicDiagUnitary_eq_diagonal uSlot0LocalXorBit5_eq_diagonal
   unitaryConj_eq_inv_mul unitaryConj_mul uVepFusedTwistRestCut80)
open InterWalkRSum42Hoist
  (qreg_ext kFull80 rAct0 rCoreOrig rCoreFull rSegOrig rSegFull rSegFull_compose_rCoreLoc
   E_rawStream42 E_stream42 FixesLow3924 PreservesFeature h3924_core h3924_actOrig
   isLow3924Prefix_rCoreOrig fixesLow3924_embedMatrix_prefix fixesLow3924_embedMatrix_high
   embedAct0_comm_E_rawStream42 embedAct0_fixesLow3924_comm_E_stream42)
open Pass1Leaf273 (hm22_80 hm80_80 uPass1Cat)
open Leaf1Pass1And3Width204
  (rCoreBlock4 selCT4InCT selCT4InCT_compose_rCoreBlock4_eq embed_selCT4InCT_uPass1CatT4
   uApexShift4 uApexShift4_mulVec_single bitsVal_fin4_lt stepT4Fin_zero t4CarryExp
   t4WinPerm t4WinPerm_apply uPass1CatT4 uPass1InnerT4 uSlot4ApexCatT4 uSlot4AxisCatT4)
open Leaf4Ext48TopStitch
  (FixesCtrl3 h3954_core CommutesWithReg rCtrl3InCore rPGIdleOrig)
open Leaf4HadCut570
  (ctLeafOfMomOracleConjInvTailHad3D unitary_comm_of_mul_proj_id
   uTailHad3DCore_inv_comm_slotBitProj momOracleConjInvTailHad3D_on_P0_and_comm_P1)
open SelectExtStitch
  (fixesCtrl3_uTailHad3DCore commutesWithReg_unitary_inv_ext)
open SelectHoistLemmas
  (pCoinSlack010Core pCoinSlack010Core_conjTranspose pCoinSlack010Seg
   commutesWithReg_rPGIdleOrig_rCoreSeg)
open SelectStitch
  (Leaf2SpecOfTrunc SelectOraHypothesisOfTrunc)
open MomSlot1DyadicTopAdapter
  (HoistedMomLocalSpecS1 mkHoistedMomLocalSpecS1 mkFullSysHoistedSelectBundleOutS1)
open SelStitchHelper
  (rCTSeg_compose_rCoreInCT80)
open SelAndPertStitch
  (cutVepTwistOutBundleOfTrunc mkSelectOraBundleOfTrunc tierBBarrel80_eq_uBarrelFast
  unitaryConj_hoisted_eq_posMom stepBarrelWiden stepSelectOraHypothesisOfTrunc stepZeroSlot5Data)
open SelAndPertStitchAux (posDataOfLeaf2)

/-- `CTLeafSpec` for the `75`-wire parameterized `Slot 1` PWU24 momentum leaf wrapped inside
`JunctionUncondHadTailCut.dConjInvTailHad3D` (`tLeaf = 4 * (bSub + 51)`, `0 .TOFF`). -/
noncomputable def slot1Pwu24HadCutLeafSpec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mWB : ℕ} (hmWB : 75 ≤ mWB) : CTLeafSpec mWB :=
  ctLeafOfMomOracleConjInvTailHad3D
    (ora1Pwu24OfBSubFull bSub hbLo hbHi (le_refl 80))
    hmWB (4 * (bSub + 51)) (le_refl _)

theorem slot1Pwu24HadCutLeafSpec_tLeaf (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mWB : ℕ} (hmWB : 75 ≤ mWB) :
    (slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).tLeaf = 4 * (bSub + 51) := rfl

theorem slot1Pwu24HadCutLeafSpec_uCat (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mWB : ℕ} (hmWB : 75 ≤ mWB) :
    (slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uCat = fun c ↦
      unitaryConj ((rCoreBlock48 80).embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹)
        (catUnitaryToFullSys ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotCat c)) := rfl

theorem slot1Pwu24HadCutLeafSpec_uEff (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mWB : ℕ} (hmWB : 75 ≤ mWB) :
    (slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uEff = fun c ↦
      unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
        (coreUnitaryToFullSys ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c)) := rfl

theorem slot1Pwu24HadCutLeafSpec_uCat_eq_core (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mWB : ℕ} (hmWB : 75 ≤ mWB) (c : Configuration) :
    (slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uCat c =
      rCoreInCT80.embedUnitary ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uEff c) := by
  rw [slot1Pwu24HadCutLeafSpec_uCat, slot1Pwu24HadCutLeafSpec_uEff]
  have hCore : momCoreWires_eq_fullSysCoreWires 80 = rfl := Subsingleton.elim _ _
  have hCat : momCatWires_eq_fullSysCatWires 80 48 = rfl := Subsingleton.elim _ _
  have hCastCat : catUnitaryToFullSys ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotCat c) =
      rCoreInCT80.embedUnitary
        (coreUnitaryToFullSys ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c)) := by
    unfold catUnitaryToFullSys coreUnitaryToFullSys
    rw [hCat, hCore]
    rfl
  have hBlk : (rCoreBlock48 80 : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 48)) =
      rCoreInCT80 := rfl
  change unitaryConj ((rCoreBlock48 80).embedUnitary _) (catUnitaryToFullSys _) =
    rCoreInCT80.embedUnitary (unitaryConj _ (coreUnitaryToFullSys _))
  rw [hCastCat, hBlk, unitaryConj, unitaryConj, ← QRegister.embedUnitary_inv,
    ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]

theorem fixesCtrl3_slot1Pwu24HadCutEff (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mWB : ℕ} (hmWB : 75 ≤ mWB) (c : Configuration) :
    FixesCtrl3 h3954_core ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uEff c).1 := by
  rw [slot1Pwu24HadCutLeafSpec_uEff]
  refine PreservesFeature.unitaryConj fixesCtrl3_uTailHad3DCore.unitary_inv ?_
  have hDiag : (coreUnitaryToFullSys
      ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c)).1 =
      slot1PWUSelectDiag bSub hbLo hbHi (le_refl 80) c := rfl
  rw [hDiag]
  exact PreservesFeature.diagonal _ _

/-- `FixesLow3924` for `uTailHad3DCore`. -/
theorem fixesLow3924_uTailHad3DCore :
    FixesLow3924 h3924_core
      (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 := by
  unfold JunctionUncondHadTailCut.uTailHad3DCore
  dsimp only
  have hAx : ∀ r : QRegister 8 (fullSysCoreWires 80),
      (∀ i : Fin 8, 3924 ≤ (r i).val) →
      FixesLow3924 h3924_core
        (r.embedUnitary JunctionUncondHadTailCut.uTailHadLocal8).1 :=
    fun r hr ↦ by
      rw [QRegister.embedUnitary_val]
      exact fixesLow3924_embedMatrix_high h3924_core hr _
  exact (hAx _ (fun i ↦ by fin_cases i <;> decide)).mul
    ((hAx _ (fun i ↦ by fin_cases i <;> decide)).mul
      (hAx _ (fun i ↦ by fin_cases i <;> decide)))

/-- `FixesLow3924` for `(slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uEff c`. -/
theorem fixesLow3924_slot1Pwu24HadCutEff (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mWB : ℕ} (hmWB : 75 ≤ mWB) (c : Configuration) :
    FixesLow3924 h3924_core ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uEff c).1 := by
  rw [slot1Pwu24HadCutLeafSpec_uEff]
  refine PreservesFeature.unitaryConj fixesLow3924_uTailHad3DCore.unitary_inv ?_
  have hDiag : (coreUnitaryToFullSys
      ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c)).1 =
      slot1PWUSelectDiag bSub hbLo hbHi (le_refl 80) c := rfl
  rw [hDiag]
  exact PreservesFeature.diagonal _ _

/-- Any `rCoreFull`-embedded unitary fixing low `3,924` wires commutes with `E_stream42` and
  `E_rawStream42`. -/
theorem rCoreFull_fixesLow3924_comm_stream42 {U : Unitary (2 ^ (fullSysCoreWires 80))}
    (hLow : FixesLow3924 h3924_core U.1) :
    (rCoreFull.embedUnitary U).1 * E_stream42 = E_stream42 * (rCoreFull.embedUnitary U).1 ∧
    (rCoreFull.embedUnitary U).1 * E_rawStream42 = E_rawStream42 * (rCoreFull.embedUnitary U).1 :=
      by
  have hEq : rCoreFull.embedUnitary U = rAct0.embedUnitary (rCoreOrig.embedUnitary U) :=
    QRegister.embedUnitary_compose rAct0 rCoreOrig U
  have hOrigLow : FixesLow3924 h3924_actOrig (rCoreOrig.embedUnitary U).1 := by
    rw [QRegister.embedUnitary_val]
    exact fixesLow3924_embedMatrix_prefix isLow3924Prefix_rCoreOrig hLow
  rw [hEq]
  exact ⟨embedAct0_fixesLow3924_comm_E_stream42 hOrigLow,
    embedAct0_comm_E_rawStream42 hOrigLow.preservesRawStream42⟩


private theorem unitary_comm_of_compl_proj_id {D : ℕ} (U V : Unitary D) (P0 P1 : Operator D)
    (hSum : P0 + P1 = 1) (hP0_sa : P0ᴴ = P0) (hP1_sa : P1ᴴ = P1)
    (hUP0 : U.1 * P0 = P0) (hVP1 : V.1 * P1 = P1) : U * V = V * U := by
  have hU0 : U.1 * P0 = P0 * U.1 := unitary_comm_of_mul_proj_id U hP0_sa hUP0
  have hV1 : V.1 * P1 = P1 * V.1 := unitary_comm_of_mul_proj_id V hP1_sa hVP1
  have hU1 : U.1 * P1 = P1 * U.1 := by
    rw [eq_sub_of_add_eq' hSum, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hU0]
  have hV0 : V.1 * P0 = P0 * V.1 := by
    rw [eq_sub_of_add_eq hSum, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hV1]
  have h0 : (U * V).1 * P0 = (V * U).1 * P0 := by
    simp only [Submonoid.coe_mul]
    calc U.1 * V.1 * P0 = U.1 * (V.1 * P0) := Matrix.mul_assoc _ _ _
      _ = (U.1 * P0) * V.1 := by rw [hV0, ← Matrix.mul_assoc]
      _ = V.1 * P0 := by rw [hUP0, ← hV0]
      _ = V.1 * (U.1 * P0) := by rw [hUP0]
      _ = V.1 * U.1 * P0 := (Matrix.mul_assoc _ _ _).symm
  have h1 : (U * V).1 * P1 = (V * U).1 * P1 := by
    simp only [Submonoid.coe_mul]
    calc U.1 * V.1 * P1 = P1 * U.1 := by rw [Matrix.mul_assoc, hVP1, hU1]
      _ = (V.1 * P1) * U.1 := by rw [hVP1]
      _ = V.1 * (U.1 * P1) := by rw [Matrix.mul_assoc, ← hU1]
      _ = V.1 * U.1 * P1 := (Matrix.mul_assoc _ _ _).symm
  exact Subtype.ext <| by
    calc (U * V).1 = (U * V).1 * (P0 + P1) := by rw [hSum, Matrix.mul_one]
      _ = (V * U).1 * (P0 + P1) := by rw [Matrix.mul_add, Matrix.mul_add, h0, h1]
      _ = (V * U).1 := by rw [hSum, Matrix.mul_one]

private theorem unitary_comm_of_slotBitProj_id {K : ℕ} (U V : Unitary (2 ^ K)) (w : Wire K)
    (hU0 : U.1 * slotBitProj w 0 = slotBitProj w 0)
    (hV1 : V.1 * slotBitProj w 1 = slotBitProj w 1) : U * V = V * U :=
  unitary_comm_of_compl_proj_id U V (slotBitProj w 0) (slotBitProj w 1)
    (slotBitProj_zero_add_one w) (slotBitProj_conjTranspose w 0)
    (slotBitProj_conjTranspose w 1) hU0 hV1

private theorem unitaryConj_mul_proj_id_slot1 {D : ℕ} (B M : Unitary D) (P : Operator D)
    (hBP : B.1 * P = P * B.1) (hMP : M.1 * P = P) : (unitaryConj B M).1 * P = P := by
  rw [unitaryConj_eq_inv_mul, Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, hBP, ← Matrix.mul_assoc M.1 P B.1, hMP, ← hBP, ← Matrix.mul_assoc,
    ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]

private theorem embedMatrix_slotBitProj_eq {k n : ℕ} (r : QRegister k n) (w₀ : Wire k)
    (b : Fin 2) : r.embedMatrix (slotBitProj w₀ b) = slotBitProj (r w₀) b := by
  unfold slotBitProj
  rw [PosMomSelectDynamic.embedMatrix_diagonal]
  congr 1; funext x
  rw [r.basisBits_extractIndex x w₀]

private theorem embedUnitary_mul_slotBitProj_id {k n : ℕ} (r : QRegister k n)
    (U : Unitary (2 ^ k)) (w₀ : Wire k) (b : Fin 2)
    (hU : U.1 * slotBitProj w₀ b = slotBitProj w₀ b) :
    (r.embedUnitary U).1 * slotBitProj (r w₀) b = slotBitProj (r w₀) b := by
  rw [QRegister.embedUnitary_val, ← embedMatrix_slotBitProj_eq r w₀ b, ← r.embedMatrix_mul, hU]

private theorem embedUnitary_comm_slotBitProj {k n : ℕ} (r : QRegister k n)
    (U : Unitary (2 ^ k)) (w₀ : Wire k) (b : Fin 2)
    (hU : U.1 * slotBitProj w₀ b = slotBitProj w₀ b * U.1) :
    (r.embedUnitary U).1 * slotBitProj (r w₀) b =
      slotBitProj (r w₀) b * (r.embedUnitary U).1 := by
  rw [QRegister.embedUnitary_val, ← embedMatrix_slotBitProj_eq r w₀ b,
    ← r.embedMatrix_mul, ← r.embedMatrix_mul, hU]

private theorem uSlot0LocalXorBit5_mul_iSlot0_one (w_eff : ℝ) :
    (uSlot0LocalXorBit5 (le_refl 80) w_eff).1 * slotBitProj (iSlot0 80) 1 =
      slotBitProj (iSlot0 80) 1 := by
  rw [uSlot0LocalXorBit5_eq_diagonal w_eff, slotBitProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  by_cases hc0 : (basisBits (fullSysCoreWires 80) u (iSlot0 80)).val = (1 : Fin 2).val
  · rw [p1_ite_true hc0, mul_one]
    have hc0z : basisBits (fullSysCoreWires 80) u (iSlot0 80) = 1 := ZMod.val_injective 2 hc0
    have hph : slot0LocalPhaseBit (le_refl 80) w_eff
        (fun q ↦ xor32BitFn 80 (basisBits (fullSysCoreWires 80) u)
          ⟨q.val, by have := q.isLt; change q.val < 4034 at this; exact this⟩) = 0 := by
      unfold slot0LocalPhaseBit
      have hne : xor32BitFn 80 (basisBits (fullSysCoreWires 80) u)
          ⟨SpecsAux.SpecMirror.systemQubits, by decide⟩ ≠ 0 := by
        dsimp only [xor32BitFn]
        have hn : ¬ (SpecsAux.SpecMirror.systemQubits < 3924 ∧
            SpecsAux.SpecMirror.systemQubits % 6 = 5) := by decide
        rw [p1_ite_false hn]
        have hw : (⟨SpecsAux.SpecMirror.systemQubits, by decide⟩ :
            Wire (fullSysCoreWires 80)) = iSlot0 80 := Fin.ext rfl
        rw [hw, hc0z]
        decide
      simp only [hne, false_and, ↓reduceIte]
    rw [hph]; simp
  · rw [p1_ite_false hc0, mul_zero]

private theorem uApexShift4_mul_slotBitProj_one_of_zero {kSys : ℕ} (δ : BitAssignment kSys → ℤ)
    (w : Wire kSys) (hδ0 : ∀ γ : BitAssignment kSys, γ w = 1 → δ γ = 0) :
    (uApexShift4 kSys δ).1 * slotBitProj (Fin.castAdd 4 w) 1 =
      slotBitProj (Fin.castAdd 4 w) 1 := by
  apply TierClosure.matrix_eq_of_mulVec_ket
  intro β
  rw [← Matrix.mulVec_mulVec, TierClosure.slotBitProj_mulVec_ket]
  change (uApexShift4 kSys δ).1 *ᵥ ((if β (Fin.castAdd 4 w) = 1 then (1 : ℂ) else 0) •
      MeasureBranchHadamardSem.ket β) =
    (if β (Fin.castAdd 4 w) = 1 then (1 : ℂ) else 0) • MeasureBranchHadamardSem.ket β
  by_cases hbw : β (Fin.castAdd 4 w) = 1
  · rw [ite_eq_left hbw, one_smul]
    let x := (basisBitsEquiv (kSys + 4)).symm β
    have hβ : basisBits (kSys + 4) x = β := (basisBitsEquiv (kSys + 4)).apply_symm_apply β
    have hsingle : MeasureBranchHadamardSem.ket β =
        (Pi.single x (1 : ℂ) : Fin (2 ^ (kSys + 4)) → ℂ) := by
      funext u; simp [x, MeasureBranchHadamardSem.ket, basisState]
    have hp1 : (DyadicQft64.splitSysCatEquiv kSys 4 x).1 = fun i ↦ β (Fin.castAdd 4 i) := by
      let p := DyadicQft64.splitSysCatEquiv kSys 4 x
      have hx : x = (DyadicQft64.splitSysCatEquiv kSys 4).symm (p.1, p.2) := by
        dsimp only [p]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
      funext i
      rw [← hβ]
      conv_rhs => rw [hx, JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd]
    have hδ_β : δ (fun i ↦ β (Fin.castAdd 4 i)) = 0 := hδ0 _ hbw
    have hCarry0 : t4CarryExp kSys δ (basisBits (kSys + 4) x) = 0 := by
      unfold t4CarryExp
      rw [hβ, hδ_β, add_zero]
      have hlt : (CoinDispatchedBarrel288.Internal.bitsVal
          (fun k : Fin 4 ↦ β (Fin.natAdd kSys k)) : ℤ) < (2 ^ 4 : ℤ) := by
        exact_mod_cast bitsVal_fin4_lt (fun k ↦ β (Fin.natAdd kSys k))
      exact Int.ediv_eq_zero_of_lt (by positivity) hlt
    have hPermId : t4WinPerm kSys δ x = x := by
      rw [t4WinPerm_apply, hp1, hδ_β, stepT4Fin_zero, ← hp1, Prod.mk.eta, Equiv.symm_apply_apply]
    rw [hsingle, uApexShift4_mulVec_single,
      hCarry0, DyadicQft64.dyadicTurn_zero, one_smul, hPermId]
  · rw [ite_eq_right hbw, zero_smul, Matrix.mulVec_zero]

private theorem slot4Sgn_eq_zero_of_iSlot2_one (isInv : Bool) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires 80)) (h2 : γ (iSlot2 80) = 1) :
    JunctionApexCSA288.slot4Sgn isInv hm22_80 w γ = 0 := by
  unfold JunctionApexCSA288.slot4Sgn
  have hw2 : wSlot2 (QRegExt.idReg (fullSysCoreWires 80)) = iSlot2 80 := Fin.ext rfl
  have hne : γ (wSlot2 (QRegExt.idReg (fullSysCoreWires 80))) ≠ 0 := by
    rw [hw2, h2]; decide
  simp only [hne, false_and, ↓reduceIte]

private theorem dyadicDiagUnitary_mul_slotBitProj_one_of_zero {kSys B : ℕ}
    (e : BitAssignment kSys → ℤ) (w : Wire kSys)
    (he0 : ∀ γ : BitAssignment kSys, γ w = 1 → e γ = 0) :
    (DyadicQft64.dyadicDiagUnitary kSys B e).1 * slotBitProj w 1 = slotBitProj w 1 := by
  rw [dyadicDiagUnitary_eq_diagonal, slotBitProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  by_cases hw1 : (basisBits kSys u w).val = (1 : Fin 2).val
  · rw [p1_ite_true hw1, mul_one,
      he0 _ (ZMod.val_injective 2 hw1), DyadicQft64.dyadicTurn_zero]
  · rw [p1_ite_false hw1, mul_zero]

private theorem uSlot4ApexCatT4_mul_iSlot2_one :
    (uSlot4ApexCatT4 hm22_80).1 * slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 =
      slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 := by
  have hCast : rCoreBlock4 80 (iSlot2 80) = Fin.castAdd 4 (iSlot2 80) :=
    Fin.ext (Nat.zero_add _)
  have hAx : ∀ w : Fin 3,
      (uSlot4AxisCatT4 false hm22_80 w).1 * slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 =
        slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 := fun w ↦ by
    unfold uSlot4AxisCatT4
    rw [Submonoid.coe_mul, Matrix.mul_assoc]
    have hD : ((rCoreBlock4 80).embedUnitary
        (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48
          (JunctionApexCSA288.slot4TopExp false hm22_80 w))).1 *
        slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 =
      slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 := by
      refine embedUnitary_mul_slotBitProj_id (rCoreBlock4 80) _ (iSlot2 80) 1 ?_
      refine dyadicDiagUnitary_mul_slotBitProj_one_of_zero _ (iSlot2 80) fun γ h2 ↦ ?_
      unfold JunctionApexCSA288.slot4TopExp
      simp only [slot4Sgn_eq_zero_of_iSlot2_one false w γ h2, mul_zero, zero_mul]
    have hS : (uApexShift4 (fullSysCoreWires 80)
        (JunctionApexCSA288.slot4LowShift false hm22_80 w)).1 *
        slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 =
      slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 := by
      rw [hCast]
      refine uApexShift4_mul_slotBitProj_one_of_zero _ (iSlot2 80) fun γ h2 ↦ ?_
      unfold JunctionApexCSA288.slot4LowShift
      simp only [slot4Sgn_eq_zero_of_iSlot2_one false w γ h2, zero_mul]
    rw [hD, hS]
  unfold uSlot4ApexCatT4
  simp only [Submonoid.coe_mul, Matrix.mul_assoc, hAx 0, hAx 1, hAx 2]

private theorem hiSlot0_ge3924 : 3924 ≤ (iSlot0 80).val := by decide
private theorem hiSlot2_ge3924 : 3924 ≤ (iSlot2 80).val := by decide
private theorem hiSlot0_ge3948 : 3948 ≤ (iSlot0 80).val := by decide

private theorem selCT4InCT_compose_rCoreBlock4_eq_rCoreInCT80 :
    (selCT4InCT 80).compose (rCoreBlock4 80) = rCoreInCT80 :=
  selCT4InCT_compose_rCoreBlock4_eq


private theorem momOracleConjInvTailHad3D_on_iSlot0_zero {k : Fin 6}
    (ora : MomSingleSlotOracle 80 48 k)
    (hk0 : coinBitFin2 (fullSysCoinIdx k) 0 = 1)
    (c : SpecsAux.SpecMirror.Configuration) :
    (unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
        (coreUnitaryToFullSys (ora.uSlotEff c))).1 *
      slotBitProj (iSlot0 80) 0 = slotBitProj (iSlot0 80) 0 := by
  have hOrth : momCoinProj 80 (fullSysCoinIdx k) * slotBitProj (iSlot0Mom 80) 0 = 0 := by
    unfold momCoinProj
    rw [hk0, slotBitProj, slotBitProj, slotBitProj, slotBitProj,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases hxy : x = y
    · subst hxy
      simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
      by_cases hb : (basisBits (momCoreWires 80) x (iSlot0Mom 80)).val = 0 <;> simp [hb]
    · simp [hxy]
  have hSym0 : (ora.uSlotEff c).1 * slotBitProj (iSlot0Mom 80) 0 = slotBitProj (iSlot0Mom 80) 0 :=
    by
    have h := congrArg (· * slotBitProj (iSlot0Mom 80) 0) (ora.hOffCoin c)
    rwa [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hOrth, sub_zero] at h
  let M := coreUnitaryToFullSys (ora.uSlotEff c)
  have hM0 : M.1 * slotBitProj (iSlot0 80) 0 = slotBitProj (iSlot0 80) 0 :=
    TierClosure.castNatUnitary_mul_slotBitProj_id
      (momCoreWires_eq_fullSysCoreWires 80)
      (ora.uSlotEff c) (iSlot0Mom 80) (iSlot0 80) rfl 0 hSym0
  have hTi0 := uTailHad3DCore_inv_comm_slotBitProj (w := iSlot0 80) hiSlot0_ge3948 0
  exact unitaryConj_mul_proj_id_slot1 _ M (slotBitProj (iSlot0 80) 0) hTi0 hM0

/-- **`hComm1_S1` for `slot1Pwu24HadCutLeafSpec`**:
`Slot 1 PWU24` and `Pass 1` (`uPass1Cat`) commute on `(fullSysCoreWires 80 + 48)`
and under `rCTSeg.embedUnitary`. -/
theorem slot1Pwu24HadCutLeafSpec_uCat_comm_uPass1Cat
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) {mWB : ℕ} (hmWB : 75 ≤ mWB)
    (c : Configuration) :
    rCTSeg.embedUnitary ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uCat c) *
      rCTSeg.embedUnitary uPass1Cat =
    rCTSeg.embedUnitary uPass1Cat *
      rCTSeg.embedUnitary ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uCat c) := by
  have hBlock4 :
      (rCoreBlock4 80).embedUnitary ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uEff c) *
        uPass1CatT4 =
      uPass1CatT4 *
        (rCoreBlock4 80).embedUnitary ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uEff c) := by
    unfold uPass1CatT4 uPass1InnerT4
    rw [unitaryConj_mul]
    let S1 := (rCoreBlock4 80).embedUnitary ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uEff c)
    let B4 := (rCoreBlock4 80).embedUnitary (uBarrelFast hm80_80)
    let U0 :=
      unitaryConj B4 ((rCoreBlock4 80).embedUnitary (uSlot0LocalXorBit5 hm80_80 lambdaSlot0TeHi))
    let U4 := unitaryConj B4 (uSlot4ApexCatT4 hm22_80)
    have hS1_i2_0 : S1.1 * slotBitProj (rCoreBlock4 80 (iSlot2 80)) 0 =
        slotBitProj (rCoreBlock4 80 (iSlot2 80)) 0 := by
      dsimp only [S1]
      refine embedUnitary_mul_slotBitProj_id (rCoreBlock4 80) _ (iSlot2 80) 0 ?_
      rw [slot1Pwu24HadCutLeafSpec_uEff]
      exact (momOracleConjInvTailHad3D_on_P0_and_comm_P1
        (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) rfl c).1
    have hS1_i0_0 : S1.1 * slotBitProj (rCoreBlock4 80 (iSlot0 80)) 0 =
        slotBitProj (rCoreBlock4 80 (iSlot0 80)) 0 := by
      dsimp only [S1]
      refine embedUnitary_mul_slotBitProj_id (rCoreBlock4 80) _ (iSlot0 80) 0 ?_
      rw [slot1Pwu24HadCutLeafSpec_uEff]
      exact momOracleConjInvTailHad3D_on_iSlot0_zero
        (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) rfl c
    have hU0_i0_1 : U0.1 * slotBitProj (rCoreBlock4 80 (iSlot0 80)) 1 =
        slotBitProj (rCoreBlock4 80 (iSlot0 80)) 1 := by
      dsimp only [U0, B4]
      refine unitaryConj_mul_proj_id_slot1 _ _ _ ?_ ?_
      · exact embedUnitary_comm_slotBitProj (rCoreBlock4 80) (uBarrelFast hm80_80) (iSlot0 80) 1
          (uBarrelFast_comm_high_wire hm80_80 (iSlot0 80) hiSlot0_ge3924 1)
      · exact embedUnitary_mul_slotBitProj_id (rCoreBlock4 80) _ (iSlot0 80) 1
          (uSlot0LocalXorBit5_mul_iSlot0_one lambdaSlot0TeHi)
    have hU4_i2_1 : U4.1 * slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 =
        slotBitProj (rCoreBlock4 80 (iSlot2 80)) 1 := by
      dsimp only [U4, B4]
      refine unitaryConj_mul_proj_id_slot1 _ _ _ ?_ uSlot4ApexCatT4_mul_iSlot2_one
      exact embedUnitary_comm_slotBitProj (rCoreBlock4 80) (uBarrelFast hm80_80) (iSlot2 80) 1
        (uBarrelFast_comm_high_wire hm80_80 (iSlot2 80) hiSlot2_ge3924 1)
    have hComm0 : S1 * U0 = U0 * S1 :=
      unitary_comm_of_slotBitProj_id S1 U0 (rCoreBlock4 80 (iSlot0 80)) hS1_i0_0 hU0_i0_1
    have hComm4 : S1 * U4 = U4 * S1 :=
      unitary_comm_of_slotBitProj_id S1 U4 (rCoreBlock4 80 (iSlot2 80)) hS1_i2_0 hU4_i2_1
    change S1 * (U0 * U4) = (U0 * U4) * S1
    rw [← mul_assoc, hComm0, mul_assoc, hComm4, ← mul_assoc]
  have hCT : ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uCat c) * uPass1Cat =
      uPass1Cat * ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uCat c) := by
    rw [slot1Pwu24HadCutLeafSpec_uCat_eq_core bSub hbLo hbHi hmWB c, ← embed_selCT4InCT_uPass1CatT4,
      ← selCT4InCT_compose_rCoreBlock4_eq_rCoreInCT80,
        QRegister.embedUnitary_compose (selCT4InCT 80),
      ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
    exact congrArg (selCT4InCT 80).embedUnitary hBlock4
  rw [← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
  exact congrArg rCTSeg.embedUnitary hCT

theorem slot1Pwu24HadCutLeafSpec_uCat_mul_pCoinSlack010Seg
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) {mWB : ℕ} (hmWB : 75 ≤ mWB)
    (c : Configuration) :
    (rCTSeg.embedUnitary ((slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hmWB).uCat c)).1 *
      pCoinSlack010Seg = pCoinSlack010Seg := by
  rw [slot1Pwu24HadCutLeafSpec_uCat_eq_core, ← QRegister.embedUnitary_compose,
    rCTSeg_compose_rCoreInCT80]
  unfold pCoinSlack010Seg
  rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul]
  apply congrArg rCoreSeg.embedMatrix
  have hP0 :=
    (momOracleConjInvTailHad3D_on_P0_and_comm_P1
      (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) (by decide) c).1
  rw [slot1Pwu24HadCutLeafSpec_uEff]
  unfold pCoinSlack010Core
  let uS1 := (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c
  calc (unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
          (coreUnitaryToFullSys uS1)).1 *
          (slotBitProj (iSlot2 80) 0 * slotBitProj (iSlot1 80) 1 * slotBitProj (iSlot0 80) 0)
      = ((unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
          (coreUnitaryToFullSys uS1)).1 *
          slotBitProj (iSlot2 80) 0) *
          (slotBitProj (iSlot1 80) 1 * slotBitProj (iSlot0 80) 0) := by
          simp only [Matrix.mul_assoc]
    _ = slotBitProj (iSlot2 80) 0 * slotBitProj (iSlot1 80) 1 * slotBitProj (iSlot0 80) 0 := by
          rw [hP0, Matrix.mul_assoc]

/-- `MomLocalSlotData` for `ora1Pwu24OfBSub bSub hbLo hbHi hmPay` (`mWork = 75`, `tSlot = 4 *
  (bSub + 51)`). -/
noncomputable def slot1Pwu24FastData (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (uBarrel : SpecsAux.SpecMirror.Configuration →
      Unitary (2 ^ (momCoreWires mPayload)))
    (hBarrelHigh : ∀ cfg (q : Wire (momCoreWires mPayload)),
      3924 ≤ q.val → ∀ b : Fin 2,
        (uBarrel cfg).1 * slotBitProj q b = slotBitProj q b * (uBarrel cfg).1) :
    MomLocalSlotData mPayload 48 1 uBarrel :=
  let ref := ora1Pwu24OfBSub bSub hbLo hbHi hmPay
  MomLocalSlotData.ofCoreOnly
    75
    ref
    ref.uSlotEff
    ref.hSA
    ref.hOffCoin
    (fun cfg ↦ congrArg (· * momCoinProj mPayload 5)
      (congrArg Subtype.val
        (slot1PWUSelectUnitary_conj_highWire bSub hbLo hbHi hmPay cfg (uBarrel cfg)
          (hBarrelHigh cfg))))

noncomputable def mkSlot1Pwu24FastDataOfBarrel (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload mWork : ℕ} (hmPay : 80 ≤ mPayload)
    (barrel : HoistedBarrelSpec mPayload mWork) :
    MomLocalSlotData mPayload 48 1
      (fun cfg ↦ coreUnitaryFromFullSys (barrel.uBarrel cfg)) :=
  slot1Pwu24FastData bSub hbLo hbHi hmPay
    (fun cfg ↦ coreUnitaryFromFullSys (barrel.uBarrel cfg))
    (fun cfg q hq bit ↦
      castNatUnitary_comm_slotBitProj (momCoreWires_eq_fullSysCoreWires mPayload)
        (barrel.uBarrel cfg) (barrel.hHighWireComm cfg) q hq bit)

noncomputable def mkHoistedMomLocalFromPwu24S3L5Fast
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mPayload mWork : ℕ} (hm80 : 80 ≤ mPayload) (hm288 : 288 ≤ mWork)
    (barrel : HoistedBarrelSpec mPayload mWork)
    (hBarrelEq : ∀ cfg, barrel.uBarrel cfg = uBarrelFast hm80)
    (s3 : MomSingleSlotOracle mPayload 48 3)
    (l5 : MomLocalSlotData mPayload 48 5
      (fun cfg ↦ coreUnitaryFromFullSys (barrel.uBarrel cfg)))
    (hw3 : s3.mWork ≤ mWork)
    (hw5 : l5.mWork ≤ mWork) :
    HoistedMomLocalSpecS1 hm80 mWork barrel (ora1Pwu24OfBSub bSub hbLo hbHi hm80) s3 l5.oracle :=
  mkHoistedMomLocalSpecS1 hm80 barrel (ora1Pwu24OfBSub bSub hbLo hbHi hm80)
    (mkSlot0LocalDataOfBarrelFast hm80 barrel.uBarrel hBarrelEq)
    (mkSlot1Pwu24FastDataOfBarrel bSub hbLo hbHi hm80 barrel)
    (liftSlot3OfBarrelFast hm80 s3 barrel.uBarrel hBarrelEq)
    l5
    rfl rfl
    (le_trans (by decide : slot0LocalWorkWires ≤ 288) hm288)
    (le_trans (by decide : 75 ≤ 288) hm288) hw3 hw5

/-- Combined 4-slot local momentum bundle (`Slots 0, 1 (PWU24), 3, 5`) for any `s3` at width
`max 288 s3.mWork`. -/
noncomputable def mkMomLocalOfPwu24S3
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (s3 : MomSingleSlotOracle 80 48 3) :
    HoistedMomLocalSpecS1 (le_refl 80) (max 288 s3.mWork) (stepBarrelWiden s3)
      (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) s3 (zeroMomSlotOracle5 80 48) :=
  mkHoistedMomLocalFromPwu24S3L5Fast bSub hbLo hbHi (le_refl 80) (Nat.le_max_left 288 s3.mWork)
    (stepBarrelWiden s3) tierBBarrel80_eq_uBarrelFast s3 (stepZeroSlot5Data s3)
    (Nat.le_max_right 288 s3.mWork) (Nat.zero_le _)

/-- Width-unrestricted `FullSysHoistedSelectBundle 80 48` (`mWorkSelect = max 288 s3.mWork`)
using `ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)`. -/
noncomputable def mkHoistedSelectBundleOfPwu24Trunc
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {t2Ctrl t2Cat : ℕ}
    (truncFn : Configuration → Configuration)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (s3 : MomSingleSlotOracle 80 48 3) :
    FullSysHoistedSelectBundle 80 48 :=
  mkFullSysHoistedSelectBundleOutS1 (hm22 := (by decide : 22 ≤ 80)) (hm80 := le_refl 80)
    (stepBarrelWiden s3)
    (cutVepTwistOutBundleOfTrunc
      (le_trans (by decide : mWorkTwist ≤ 288) (Nat.le_max_left 288 s3.mWork)) truncFn)
    (posDataOfLeaf2 leaf2)
    (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) s3 (zeroMomSlotOracle5 80 48)
    (mkMomLocalOfPwu24S3 bSub hbLo hbHi s3)
    (Nat.le_max_left 288 s3.mWork)

/-- Turnkey `FullSysSelectOracleBundle 80 48` using `ora1Pwu24OfBSub bSub hbLo hbHi (le_refl
  80)`. -/
noncomputable def mkSelectOraBundleOfPwu24Trunc
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {t2Ctrl t2Cat : ℕ}
    (truncFn : Configuration → Configuration)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (s3 : MomSingleSlotOracle 80 48 3) :
    FullSysSelectOracleBundle 80 48 :=
  (mkHoistedSelectBundleOfPwu24Trunc bSub hbLo hbHi truncFn leaf2 s3).toSelectOracleBundle

/-- Parametric `Slot 1`-aware counterpart of `SelectOraHypothesisOfTrunc`: decomposes
`selOra` with an arbitrary `Slot 1` oracle `s1` (`PWU24` or `Dyadic459`) alongside `leaf2` and `s3`.
-/
structure SelectOraHypothesisOfS1Trunc {t2Ctrl t2Cat : ℕ}
    (truncFn : Configuration → Configuration)
    (selOra : FullSysSelectOracleBundle 80 48)
    (s1 : MomSingleSlotOracle 80 48 1)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (ora3 : MomSingleSlotOracle 80 48 3) : Prop where
  hTw : ∀ c, selOra.uTwist c =
    uVepFusedTwistRestCut80 (truncFn c) * uBarrelFast (le_refl 80)
  hMom : ∀ c, selOra.uMomPhase c =
    unitaryConj (uBarrelFast (le_refl 80))
      (coreUnitaryToFullSys
        (((zeroMomSlotOracle5 80 48).uSlotEff c *
          ora3.uSlotEff c) *
          (s1.uSlotEff c *
            MomSlot0LocalAndMomCombine288.uSlot0Local (le_refl 80)
              lambdaSlot0TeHi)))
  hPosEq : ∀ c, selOra.uPosPhase c = leaf2.uPosPhase0

/-- Discharges `SelectOraHypothesisOfS1Trunc` for `mkSelectOraBundleOfPwu24Trunc` with zero
workspace-width side conditions on `s3`. -/
theorem stepSelectOraHypothesisOfPwu24Trunc
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {t2Ctrl t2Cat : ℕ}
    (truncFn : Configuration → Configuration)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (s3 : MomSingleSlotOracle 80 48 3) :
    SelectOraHypothesisOfS1Trunc truncFn
      (mkSelectOraBundleOfPwu24Trunc bSub hbLo hbHi truncFn leaf2 s3)
      (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) leaf2 s3 where
  hTw c := congrArg (uVepFusedTwistRestCut80 (truncFn c) * ·) (tierBBarrel80_eq_uBarrelFast c)
  hMom c := (unitaryConj_hoisted_eq_posMom (tierBBarrel80.uBarrel c) _).trans
    (congrArg (fun B ↦ unitaryConj B _) (tierBBarrel80_eq_uBarrelFast c))
  hPosEq _ := rfl

private theorem unitaryConj_castNatUnitary_pwu24 {a b : ℕ} (h : a = b)
    (U : Unitary (2 ^ b)) (M : Unitary (2 ^ a)) :
    unitaryConj U (OraAndPrepBundle.castNatUnitary h M) =
      OraAndPrepBundle.castNatUnitary h
        (unitaryConj (OraAndPrepBundle.castNatUnitary h.symm U) M) := by
  subst h; rfl

/-- Direct `FixesLow3924` on the un-conjugated `ora1Pwu24OfBSub` full-system core unitary. -/
theorem fixesLow3924_ora1Pwu24OfBSub_eff
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) (c : Configuration) :
    FixesLow3924 h3924_core
      (coreUnitaryToFullSys ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c)).1 := by
  have hDiag : (coreUnitaryToFullSys
      ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c)).1 =
      slot1PWUSelectDiag bSub hbLo hbHi (le_refl 80) c := rfl
  rw [hDiag]
  exact PreservesFeature.diagonal _ _

/-- Any unitary on `fullSysCoreWires 80` commuting with high-wire (`≥ 3924`) projectors fixes
`coreUnitaryToFullSys ((ora1Pwu24OfBSub ...).uSlotEff c)` under `unitaryConj`. -/
theorem ora1Pwu24OfBSub_conj_highWire
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) (c : Configuration)
    (U : Unitary (2 ^ (fullSysCoreWires 80)))
    (hHigh : ∀ q : Wire (fullSysCoreWires 80), 3924 ≤ q.val → ∀ b : Fin 2,
      U.1 * slotBitProj q b = slotBitProj q b * U.1) :
    unitaryConj U (coreUnitaryToFullSys ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c))
      =
      coreUnitaryToFullSys ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c) := by
  have hEff : (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c =
      slot1PWUSelectUnitary bSub hbLo hbHi (le_refl 80) c := rfl
  rw [hEff]
  have hCast := slot1PWUSelectUnitary_conj_highWire bSub hbLo hbHi (le_refl 80) c
    (coreUnitaryFromFullSys U)
    (fun q hq bit ↦
      castNatUnitary_comm_slotBitProj (momCoreWires_eq_fullSysCoreWires 80) U hHigh q hq bit)
  exact (unitaryConj_castNatUnitary_pwu24 (momCoreWires_eq_fullSysCoreWires 80) U _).trans
    (congrArg coreUnitaryToFullSys hCast)

/-- Parametric `Slot 1` counterpart of `SelectStitch.step_uTwist_comm_slotBitProj`. -/
theorem step_uTwist_comm_slotBitProj_s1 {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    {selOra : FullSysSelectOracleBundle 80 48}
    {s1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1 leaf2 ora3)
    (c : Configuration) {w : Wire (fullSysCoreWires 80)}
    (hwLo : 3948 ≤ w.val) (hwHi : w.val < 3954) (b : Fin 2) :
    (selOra.uTwist c).1 * slotBitProj w b = slotBitProj w b * (selOra.uTwist c).1 := by
  rw [hOra.hTw c, ← SchedBranchStitchGen.uFusedTwistRestCut80_factor (truncFn c)]
  simp only [Submonoid.coe_mul]
  exact SchedBranchStitchGen.op_comm_mul
    (SchedBranchStitchGen.op_comm_mul
      (Barrel3PassSelectStitch.uTrailCliffordXor80_comm_slotBitProj (by omega) hwHi b)
      (SchedBranchStitchGen.op_comm_mul
        (SchedBranchStitchGen.uSlot4KickCore_comm_slotBitProj w b)
        (SchedBranchStitchGen.uTwistEffCut80_comm_slotBitProj (truncFn c) hwLo b)))
    (uBarrelFast_comm_high_wire (le_refl 80) w (by omega) b)

theorem step_hTwist_s2_s1 {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    {selOra : FullSysSelectOracleBundle 80 48}
    {s1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1 leaf2 ora3) (c : Configuration) :
    (selOra.uTwist c).1 * slotBitProj (iSlot2 80) 0 =
      slotBitProj (iSlot2 80) 0 * (selOra.uTwist c).1 :=
  step_uTwist_comm_slotBitProj_s1 hOra c (by decide) (by decide) 0

theorem step_hTwist_s1_s1 {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    {selOra : FullSysSelectOracleBundle 80 48}
    {s1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1 leaf2 ora3) (c : Configuration) :
    (selOra.uTwist c).1 * slotBitProj (iSlot1 80) 1 =
      slotBitProj (iSlot1 80) 1 * (selOra.uTwist c).1 :=
  step_uTwist_comm_slotBitProj_s1 hOra c (by decide) (by decide) 1

theorem step_hTwist_s0_s1 {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    {selOra : FullSysSelectOracleBundle 80 48}
    {s1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1 leaf2 ora3) (c : Configuration) :
    (selOra.uTwist c).1 * slotBitProj (iSlot0 80) 0 =
      slotBitProj (iSlot0 80) 0 * (selOra.uTwist c).1 :=
  step_uTwist_comm_slotBitProj_s1 hOra c (by decide) (by decide) 0


end ConfigSlot1Pwu24Bridge

end Dir3TwistSlot1Junction.Slot1Pwu24Bridge

section
open Dir3TwistSlot1Junction.MomSlot1WalkerAliasPWU24 in
attribute [irreducible] dInnerSsaR1 dSlot1PWUCoreDynR1
end
namespace Slot1Pwu24

export Dir3TwistSlot1Junction.MomSlot1WalkerAliasPWU24
  (eps1Pwu24Num eps1Pwu24Num_heps ora1Pwu24OfBSubFull ora1Pwu24OfBSub ora1Pwu24OfBSub_epsIntr_le)
export Dir3TwistSlot1Junction.Slot1Pwu24Bridge
  (slot1Pwu24HadCutLeafSpec slot1Pwu24HadCutLeafSpec_tLeaf slot1Pwu24HadCutLeafSpec_uCat
  slot1Pwu24HadCutLeafSpec_uEff slot1Pwu24HadCutLeafSpec_uCat_eq_core fixesCtrl3_slot1Pwu24HadCutEff
  fixesLow3924_uTailHad3DCore fixesLow3924_slot1Pwu24HadCutEff rCoreFull_fixesLow3924_comm_stream42
  slot1Pwu24HadCutLeafSpec_uCat_comm_uPass1Cat slot1Pwu24HadCutLeafSpec_uCat_mul_pCoinSlack010Seg
  slot1Pwu24FastData mkSlot1Pwu24FastDataOfBarrel mkHoistedMomLocalFromPwu24S3L5Fast
  mkMomLocalOfPwu24S3 mkHoistedSelectBundleOfPwu24Trunc mkSelectOraBundleOfPwu24Trunc
  SelectOraHypothesisOfS1Trunc stepSelectOraHypothesisOfPwu24Trunc fixesLow3924_ora1Pwu24OfBSub_eff
  ora1Pwu24OfBSub_conj_highWire step_uTwist_comm_slotBitProj_s1 step_hTwist_s2_s1 step_hTwist_s1_s1
  step_hTwist_s0_s1)
end Slot1Pwu24


end
attribute [local semireducible] basisBits QRegister.extractIndex

end PartSlot1Pwu24

-- ============================================================================
-- Part: KrylovS1
-- ============================================================================




namespace KrylovS1

section ConfigKrylovS1

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 512
set_option exponentiation.threshold 5000

open Operator Matrix Real SpecsAux
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPow_KrylovS1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open scoped Matrix BigOperators

open SpecsAux.SpecMirror
open Dyadic128CoulombMath (orbitCount47905)
open PosMomSelectSandwich (slotBitProj)
open FullSysCatSegmentBridge
  (iSlot2 FullSysQft654Bundle FullSysPrepareBundle FullSysSelectOracleBundle
   fullSysSelectMomUnitary fullSysSelectPosUnitary fullSysSelectEffUnitary fullSysRawBEUnitary)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open FullSysFullPrepareAndTopConcrete (coreSysSym coreAncSym)
open OraAndPrepBundle
  (PosPostPrepCert castNatUnitary castNatUnitary_symm_cancel momCoreWires_eq_fullSysCoreWires
   coreUnitaryToFullSys)
open GeneralBetaAndAlphaTopEndpoint (zeroMomSlotOracle5)
open ZeroSubwireHarmonicGridPert (zeroSubwireConstPrepUnitary)
open Leaf4Ext48TopStitch (CommutesWithReg)
open InterWalkRSum42Hoist
  (PreservesFeature FixesLow3924 fixesLow3924_castNatUnitary h3924_core h3924_momCore)
open DyadicQft64WalkCircuit (qft64Ideal654Unitary)
open FusedPreDiagFromTwist288 (uPre654)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open MomSlot0LocalAndMomCombine288 (uSlot0Local)
open LiteralKineticAndMidpoint128 (lambdaSlot0TeHi)
open Leaf2PosMod4WidthCore
  (uPosPhase80Mod4Eff uPosPhase80Mod4OfB)
open SelectStitch (Leaf2SpecOfTrunc)
open SelAndPertStitch
  (cutVepTwistOutBundleOfTrunc mkSelectOraBundleOfTrunc tierBBarrel80_eq_uBarrelFast
  unitaryConj_hoisted_eq_posMom stepBarrelWiden stepSelectOraHypothesisOfTrunc stepZeroSlot5Data)
open SelAndPertStitchAux (posDataOfLeaf2)
open FermionicKrylovSegBridge
  (CoreOpMapsZeroBadToKrylov3 RawBEMapsFermToKrylov3)
open MomSelectKrylov
  (PreservesCoreBadElec preservesCoreBadElec_of_fixesLow3924 preservesCoreBadElec_uBarrelFast
   fixesLow3924_zeroMomSlotOracle5_eff fixesLow3924_uSlot0Local_80
   coreOpMapsZeroBadToKrylov3_of_preservesCoreBadElec)
open PosFermKrylovTail
  (CoreFermMapsToKrylov3 coreFermMapsToKrylov3_selectEff_of_posSlot0_mom
   rawBEMapsFermToKrylov3_of_selectEff_comm
   commutesWithReg_coreSysSym_zeroSubwireConstPrepUnitary)
open PosFermKrylovHead
  (coreFermMapsToKrylov3_selectPos_of_oraHyp_mod4Eff_mul_slot0
   coreQftHadamardPrunedBundle128_mul_uPre654)
open Slot1Pwu24
  (ora1Pwu24OfBSub SelectOraHypothesisOfS1Trunc fixesLow3924_ora1Pwu24OfBSub_eff)

/-- `FixesLow3924 h3924_momCore` on the un-cast `(ora1Pwu24OfBSub ...).uSlotEff c` unitary. -/
theorem fixesLow3924_ora1Pwu24OfBSub_momEff
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) (c : Configuration) :
    FixesLow3924 h3924_momCore
      ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff c).1 := by
  have hBack := fixesLow3924_castNatUnitary (momCoreWires_eq_fullSysCoreWires 80).symm
    h3924_core h3924_momCore (fixesLow3924_ora1Pwu24OfBSub_eff bSub hbLo hbHi c)
  rwa [coreUnitaryToFullSys, castNatUnitary_symm_cancel] at hBack

private theorem preservesCoreBadElec_selectMom_of_oraHypS1 {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    {selOra : FullSysSelectOracleBundle 80 48}
    {ora1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra ora1 leaf2 ora3)
    (c : Configuration)
    (hOra1Eff : FixesLow3924 h3924_momCore (ora1.uSlotEff c).1)
    (hOra3Eff : FixesLow3924 h3924_momCore (ora3.uSlotEff c).1) :
    PreservesCoreBadElec (fullSysSelectMomUnitary selOra c).1 := by
  unfold fullSysSelectMomUnitary
  rw [hOra.hMom c]
  have hMomCore :
      FixesLow3924 h3924_momCore
        (((zeroMomSlotOracle5 80 48).uSlotEff c * ora3.uSlotEff c) *
          (ora1.uSlotEff c * uSlot0Local (le_refl 80) lambdaSlot0TeHi)).1 := by
    simp only [Submonoid.coe_mul]
    exact ((fixesLow3924_zeroMomSlotOracle5_eff c).mul hOra3Eff).mul
      (hOra1Eff.mul (fixesLow3924_uSlot0Local_80 lambdaSlot0TeHi))
  have hMomFlag :
      FixesLow3924 h3924_core
        (coreUnitaryToFullSys
          (((zeroMomSlotOracle5 80 48).uSlotEff c * ora3.uSlotEff c) *
            (ora1.uSlotEff c * uSlot0Local (le_refl 80) lambdaSlot0TeHi))).1 :=
    fixesLow3924_castNatUnitary (momCoreWires_eq_fullSysCoreWires 80)
      h3924_momCore h3924_core hMomCore
  exact (preservesCoreBadElec_uBarrelFast (le_refl 80)).unitaryConj
    (preservesCoreBadElec_of_fixesLow3924 h3924_core hMomFlag)

private theorem coreOpMapsZeroBadToKrylov3_selectMom_of_oraHypS1 {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    {selOra : FullSysSelectOracleBundle 80 48}
    {ora1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra ora1 leaf2 ora3)
    (c : Configuration)
    (hOra1Eff : FixesLow3924 h3924_momCore (ora1.uSlotEff c).1)
    (hOra3Eff : FixesLow3924 h3924_momCore (ora3.uSlotEff c).1) :
    CoreOpMapsZeroBadToKrylov3 (fullSysSelectMomUnitary selOra c).1 :=
  coreOpMapsZeroBadToKrylov3_of_preservesCoreBadElec
    (preservesCoreBadElec_selectMom_of_oraHypS1 hOra c hOra1Eff hOra3Eff)

private theorem fullSysSelectPosUnitary_eq_of_twist_pos
    (qft : FullSysQft654Bundle)
    (sel₁ sel₂ : FullSysSelectOracleBundle 80 48)
    (c : Configuration)
    (hTw : sel₁.uTwist c = sel₂.uTwist c)
    (hPos : sel₁.uPosPhase c = sel₂.uPosPhase c) :
    fullSysSelectPosUnitary qft sel₁ c = fullSysSelectPosUnitary qft sel₂ c := by
  have hm : sel₁.hmPay = sel₂.hmPay := Subsingleton.elim _ _
  unfold fullSysSelectPosUnitary
  rw [hm, hTw, hPos]

private theorem coreFermMapsToKrylov3_selectPos_of_oraHypS1_mod4Eff_mul_slot0
    (spinUp : Finset (Fin numElectrons)) {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    {qft : FullSysQft654Bundle}
    (hqft : qft.uQft654 * uPre654 = qft64Ideal654Unitary)
    {selOra : FullSysSelectOracleBundle 80 48}
    {ora1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra ora1 leaf2 ora3)
    {tailSign : Fin orbitCount47905 → Bool}
    {tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)}
    (hPos0 : leaf2.uPosPhase0 = uPosPhase80Mod4Eff tailSign tailMag30)
    (c : Configuration) :
    CoreFermMapsToKrylov3 spinUp
      ((fullSysSelectPosUnitary qft selOra c).1 * slotBitProj (iSlot2 80) 0) := by
  let selStd := mkSelectOraBundleOfTrunc truncFn leaf2 ora3
  have hStd := stepSelectOraHypothesisOfTrunc truncFn leaf2 ora3
  have hPosEq : fullSysSelectPosUnitary qft selOra c =
      fullSysSelectPosUnitary qft selStd c :=
    fullSysSelectPosUnitary_eq_of_twist_pos qft selOra selStd c
      ((hOra.hTw c).trans (hStd.hTw c).symm)
      ((hOra.hPosEq c).trans (hStd.hPosEq c).symm)
  rw [hPosEq]
  exact coreFermMapsToKrylov3_selectPos_of_oraHyp_mod4Eff_mul_slot0 spinUp hqft hStd hPos0 c

private theorem rawBEMapsFermToKrylov3_of_oraHypS1_mod4Eff
    (spinUp : Finset (Fin numElectrons)) {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    {qft : FullSysQft654Bundle}
    (hqft : qft.uQft654 * uPre654 = qft64Ideal654Unitary)
    {prep : FullSysPrepareBundle 80}
    {selOra : FullSysSelectOracleBundle 80 48}
    {ora1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    {c : Configuration}
    (hPrep : CommutesWithReg (coreSysSym 80) (prep.uPrep c).1)
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra ora1 leaf2 ora3)
    {tailSign : Fin orbitCount47905 → Bool}
    {tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)}
    (hPos0 : leaf2.uPosPhase0 = uPosPhase80Mod4Eff tailSign tailMag30)
    (hOra1Eff : FixesLow3924 h3924_momCore (ora1.uSlotEff c).1)
    (hOra3Eff : FixesLow3924 h3924_momCore (ora3.uSlotEff c).1) :
    RawBEMapsFermToKrylov3 spinUp (fullSysRawBEUnitary qft prep selOra c) :=
  rawBEMapsFermToKrylov3_of_selectEff_comm spinUp qft prep selOra c hPrep
    (coreFermMapsToKrylov3_selectEff_of_posSlot0_mom spinUp qft selOra c
      (coreFermMapsToKrylov3_selectPos_of_oraHypS1_mod4Eff_mul_slot0 spinUp hqft hOra hPos0 c)
      (coreOpMapsZeroBadToKrylov3_selectMom_of_oraHypS1 hOra c hOra1Eff hOra3Eff))

/-- Direct `coreQftHadamardPrunedBundle128` turnkey endpoint for arbitrary `ora1`
(`SelectOraHypothesisOfS1Trunc`) and any `post : PosPostPrepCert 80` (e.g.
`pos80BhmtPostPrepCert`). -/
theorem rawBEMapsFermToKrylov3_pruned128_of_oraHypS1_stepMod
    (spinUp : Finset (Fin numElectrons)) {B t2Ctrl t2Cat : ℕ}
    {hB6 : 6 ≤ B} {hB27 : B ≤ 27}
    {truncFn : Configuration → Configuration}
    {prep : FullSysPrepareBundle 80}
    {selOra : FullSysSelectOracleBundle 80 48}
    {ora1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    {c : Configuration}
    (hPrep : ∃ (post : PosPostPrepCert 80) (uCoin : Unitary (2 ^ 3)),
      (∃ V, post.uPosPost = (coreAncSym 80).embedUnitary V) ∧
        prep.uPrep c = zeroSubwireConstPrepUnitary post uCoin)
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra ora1 leaf2 ora3)
    (hPos0 : leaf2.uPosPhase0 = uPosPhase80Mod4OfB B hB6 hB27)
    (hOra1Eff : FixesLow3924 h3924_momCore (ora1.uSlotEff c).1)
    (hOra3Eff : FixesLow3924 h3924_momCore (ora3.uSlotEff c).1) :
    RawBEMapsFermToKrylov3 spinUp
      (fullSysRawBEUnitary coreQftHadamardPrunedBundle128 prep selOra c) := by
  rcases hPrep with ⟨post, uCoin, hPost, hEq⟩
  exact rawBEMapsFermToKrylov3_of_oraHypS1_mod4Eff spinUp
    coreQftHadamardPrunedBundle128_mul_uPre654
    (by rw [hEq]; exact commutesWithReg_coreSysSym_zeroSubwireConstPrepUnitary post uCoin hPost)
    hOra hPos0 hOra1Eff hOra3Eff

/-- Turnkey `ora1Pwu24OfBSub` specialization of
`rawBEMapsFermToKrylov3_pruned128_of_oraHypS1_stepMod` discharging `hOra1Eff`
automatically via `fixesLow3924_ora1Pwu24OfBSub_momEff`. -/
theorem rawBEMapsFermToKrylov3_pruned128_of_oraHypPwu24_step
    (spinUp : Finset (Fin numElectrons)) {B bSub t2Ctrl t2Cat : ℕ}
    {hB6 : 6 ≤ B} {hB27 : B ≤ 27}
    {hbLo : 18 ≤ bSub} {hbHi : bSub ≤ 24}
    {truncFn : Configuration → Configuration}
    {prep : FullSysPrepareBundle 80}
    {selOra : FullSysSelectOracleBundle 80 48}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {ora3 : MomSingleSlotOracle 80 48 3}
    {c : Configuration}
    (hPrep : ∃ (post : PosPostPrepCert 80) (uCoin : Unitary (2 ^ 3)),
      (∃ V, post.uPosPost = (coreAncSym 80).embedUnitary V) ∧
        prep.uPrep c = zeroSubwireConstPrepUnitary post uCoin)
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra
      (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) leaf2 ora3)
    (hPos0 : leaf2.uPosPhase0 = uPosPhase80Mod4OfB B hB6 hB27)
    (hOra3Eff : FixesLow3924 h3924_momCore (ora3.uSlotEff c).1) :
    RawBEMapsFermToKrylov3 spinUp
      (fullSysRawBEUnitary coreQftHadamardPrunedBundle128 prep selOra c) :=
  rawBEMapsFermToKrylov3_pruned128_of_oraHypS1_stepMod
    spinUp hPrep hOra hPos0 (fixesLow3924_ora1Pwu24OfBSub_momEff bSub hbLo hbHi c) hOra3Eff


end ConfigKrylovS1

end KrylovS1



-- ============================================================================
-- Part: BhmtBlockComm
-- ============================================================================
section PartBhmtBlockComm


namespace BhmtBlockComm

section ConfigBhmtBlockComm

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2000
set_option exponentiation.threshold 5000

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
local instance (priority := 1000000) bhmtbcInstNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux SpecsAux.BridgeFermionicComm
-- Root solution namespace already active.
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.DyadicSubgridToeplitz512AndShift (nyq512ProjEquiv3D)
open Dyadic128CoulombMath (orbitCount47905)
open PosMomSelectSandwich (slotBitProj)
open PosMomSelectDynamic
  (unitaryConj unitaryConj_val embedMatrix_comm_diagonal_of_outside)
open FullSysPrepare6Slot (coinSelOutcome fullSysCoinIdx)
open FullSysCatSegmentBridge
  (FullSysQft654Bundle FullSysPrepareBundle FullSysSelectOracleBundle
   fullSysCoreWires fullSysRawAncWires coreElecCosetB1Block
   iSlot0 iSlot1 iSlot2 fullSysQftCoreUnitary fullSysSelectPosUnitary
   fullSysSelectEffUnitary fullSysRawBEUnitary
   fullSysSelectEffUnitary_conjTranspose_and_split
   fullSysQftCoreUnitary_comm_slotBitProj wire_not_mem_coreElecCosetB1
   fullSysSelectEffUnitary_on_slackCoin)
open FullSysFullPrepareAndTopConcrete
  (coreSysSym coreAncSym selCoin3Sym coreHadamardUnitary unitaryConj_mul_outer)
open FullSysMomSlots0135Concrete
  (momCoreWires iSlot0Mom iSlot1Mom iSlot2Mom momCoinProj MomSingleSlotOracle
   slotBitProj_self_adj slotBitProj_mul_idem coinBitFin2
   conjHadamard_branch_topBlock_of_eq_on_coin)
open MomSlot0CircuitHalf (slot0ElectronKineticOracleSym)
open OraAndPrepBundle
  (PosPostPrepCert coreUnitaryFromFullSys coreUnitaryToFullSys posCoin01Proj posCoin01ProjMom
   momCoreWires_eq_fullSysCoreWires castNatOp castNatOp_val_unitary castNatOp_conjTranspose
   castNatOp_mul castNatOp_smul castNatOp_slotBitProj
   coreAncSym_eq_momAncReg_sym selCoin3Sym_eq_momCoin3Sel_sym
   coreSysSym_eq_momSysReg_sym coreHadamardUnitary_eq_mom_sym
   fullSysSelectEffUnitary_on_momCoin_sym
   postPrep_comm_posCoin01ProjMom postPrep_pos01_branch_eq postPrep_nonPos_topBlock
   coreHadamard_conj_slack_block_gen slackProj_eq_momCoinProj)
open GeneralBetaAndAlphaTopEndpoint
  (zeroMomSlotOracle5 fullSysSelectPosUnitary_eq_on_posCoin01_out)
open TierClosure
  (mkSlot0LocalDataOfBarrelFast liftSlot3OfBarrelFast)
open TierBClean80Closure
  (tierBQftFull tierBBarrel80 tierBBarrel80_onP01 tierBL5Zero80)
open CoinDispatchedBarrel288 (uBarrelFast)
open ProjZ512QftAndTwist288 (cfgProjZ512 uProjPlus512_3D)
open PosSlots24TopWrapper (PosSlots24DataGen)
open PosSlots24SemanticBridge (pos24_22_le_80)
open PosPostPrep80MergedVepS3
  (muActualFactor80 p80ClearB0Local pos80SubIdx)
open MergedVepTopCoinCollapse
  (topCoinPropGen mProj24_sp mProjGridEquiv24 mProjBasisGen p80NucVal p80CosetP3 p80SetNucZero
   mergedSliceGen)
open Pos24Slot2FermionicBridge (payloadNucNat payloadAncNat)
open ZeroSubwireGridPert80
  (elemMat86_conjTranspose embed_elemMat86_diag momCoinProj_80_idem
   momCoinProj_80_sa post_mul_ancProj_mem_coin preserves_proj_of_sa_and_offProj
   posCoin01ProjMom_mul_momCoinProj_01 unitaryConj_comm_proj)
open ZeroSubwireHarmonicGridPert (zeroSubwireConstPrepUnitary)
open JunctionProj3DCutPos24BridgeGen
  (uVepTwistCutRef uVepTwistCutRef_pf_congr fastCutUVepTwistRef_comm_high_wire
   uVepTwistCutRef_comm_slot2 uVepTwistCutRef_comm_slot1)
open PosS3Bounds (sysBlock80Mod4Of)
open Leaf2PosMod4WidthCore
  (b_one_le_of_six_le b_le_29_of_le_27 uPosPhase80Mod4OfB pos24TailMag30Aux
   posDataMod4OfB)
open Leaf2Packed18Mux2DCore
  (uPosPhase80Mod4OfB_comm_slotBitProj)
open MomAdapterGen (topCoinPropGen_comp_truncCfg_of_posPhase_param)
open SelectStitch (Leaf2SpecOfTrunc)
open InterWalkRSum42Hoist (FixesLow3924)
open Leaf4Ext48TopStitch (FixesCtrl3)
open GqspCleanCoinAndGuardBridge
  (Coin3CleanProgSpecOfWeights bCoinGenS1S3S5)
open ConstructiveAlpha124052Bundle
  (prepBundleOfPostCertAndCoin prepBundleOfPostCertAndCoin_uPrep_eq_gen)
open FermionicKrylovSegBridge
  (pgBE RawBEBlockCommutesFerm fermionicProjector_mul_specsGridProjector)
open ApproxBlockCommFerm
  (pElMat setAnc80 setPart80 payloadPartNat sum_bitAssignment80_anc_lt218
    sum_bitAssignment80_anc_part_lt posPhaseBitMod4_const_of_rejected
    sysBlock80Mod4Of_eq_smul_one_of_phase_const blkSmSlot2Mod4Of_head_anc0_comm_pElMat
    blkSmSlot2Mod4Of_tail_sum_anc_comm_pElMat blkSmSlot4Mod4Of_head_sum_anc_comm_pElMat
    blkSmSlot4Mod4Of_tail_sum_anc_part_comm_pElMat mProj24_wrap_comm_pElMat p80NucVal_setAnc80
    p80CosetP3_setAnc80 p80SetNucZero_setAnc80 payloadAncNat_p80SetNucZero
    payloadNucNat_p80SetNucZero gridSandwich_comm_fermionicProjector_of_comm_pElMat
    momSingleSlotOracle_gridSandwich_comm_fermionicProjector pgBE_mul_rawBE_mul_pgBE_eq_sum_coin
    embed_mul_outcomeProj_comm_of_comm)
open PosPostBhmtPrep
open Slot1Pwu24
  (ora1Pwu24OfBSub mkSlot1Pwu24FastDataOfBarrel SelectOraHypothesisOfS1Trunc
   step_uTwist_comm_slotBitProj_s1 step_hTwist_s2_s1 step_hTwist_s1_s1)

private theorem bitsVal8_clear7_eq_zero_of_lt128 (f : Fin 8 → ZMod 2) :
    bitsVal f < 128 →
      bitsVal (fun j : Fin 8 ↦ if j.val < 7 then 0 else f j) = 0 := by
  revert f; decide +kernel

private theorem bitsVal8_bit7_ne_zero_of_not_lt128 (f : Fin 8 → ZMod 2) :
    ¬ bitsVal f < 128 → f ⟨7, by decide⟩ ≠ 0 := by
  revert f; decide +kernel

private theorem bitsVal8_ne_zero_of_bit7_ne_zero (f : Fin 8 → ZMod 2) :
    f ⟨7, by decide⟩ ≠ 0 → bitsVal f ≠ 0 := by
  revert f; decide +kernel

private theorem zmod2_eq_zero_of_not_beq_one (x : ZMod 2) :
    ¬ (x == 1) = true → x = 0 := by
  revert x; decide

private theorem payloadAncNat_eq_subIdx (p : BitAssignment 80) :
    payloadAncNat p = bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 14 8 (by decide) j)) := by
  unfold payloadAncNat
  exact congrArg bitsVal (funext fun _ ↦ rfl)

private theorem blkSmSlot2Mod4Of_head_lt128_comm_pElMat
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p : BitAssignment 80)
    (h30 : (p 30 == 1) = true) (hanc128 : payloadAncNat p < 128)
    (hnuc : payloadNucNat p < 216) (g : Equiv.Perm (Fin numElectrons)) :
    sysBlock80Mod4Of tM tierBQftFull cfg false p * pElMat g =
      pElMat g * sysBlock80Mod4Of tM tierBQftFull cfg false p := by
  by_cases h62 : (p ⟨62, by decide⟩ == 1) = true
  · rw [sysBlock80Mod4Of_eq_smul_one_of_phase_const tM cfg false p (p ⟨79, by decide⟩ == 1)
      (posPhaseBitMod4_const_of_rejected tM false p (Or.inl h62)),
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · have hp62 : p 62 = 0 := zmod2_eq_zero_of_not_beq_one (p ⟨62, by decide⟩) h62
    rw [sysBlock80Mod4Of_slot2_head_clearAnc7_eq tM cfg p h30 hp62 hnuc hanc128]
    let q0 := p80ClearRange 14 7 p
    have hq30 : (q0 30 == 1) = true := h30
    have hqanc0 : payloadAncNat q0 = 0 := by
      rw [payloadAncNat_eq_subIdx] at hanc128 ⊢
      have hclr : (fun j : Fin 8 ↦ q0 (pos80SubIdx 14 8 (by decide) j)) =
          fun j : Fin 8 ↦ if j.val < 7 then 0 else p (pos80SubIdx 14 8 (by decide) j) := by
        funext j; dsimp [q0, p80ClearRange, pos80SubIdx]
        by_cases hj : j.val < 7
        · rw [ite_eq_left (by omega), ite_eq_left hj]
        · rw [ite_eq_right (by omega), ite_eq_right hj]
      rw [hclr]
      exact bitsVal8_clear7_eq_zero_of_lt128 _ hanc128
    have hqnuc : payloadNucNat q0 < 216 := by
      have heq : payloadNucNat q0 = payloadNucNat p := by
        unfold payloadNucNat
        exact congrArg bitsVal (funext fun j ↦ by fin_cases j <;> rfl)
      rwa [heq]
    exact blkSmSlot2Mod4Of_head_anc0_comm_pElMat tM cfg q0 hq30 hqanc0 hqnuc g

private theorem p80ClearB0Local_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    p80ClearB0Local (setAnc80 a p) = setAnc80 a (p80ClearB0Local p) := by
  funext q; dsimp [p80ClearB0Local, setAnc80]
  by_cases h1 : 3 ≤ q.val ∧ q.val < 6
  · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left h1]
  · rw [ite_eq_right h1]; split_ifs <;> rfl

private theorem muActualFactor80_Bhmt_slot2_head_eq_zero_of_anc_ne_z
    (p : BitAssignment 80) (h30 : (p 30 == 1) = true) (hanc : payloadAncNat p ≠ 0) :
    PosPostPrep80MergedVep_Bhmt.muActualFactor80 true false p = 0 := by
  have hp30 : p80ClearB0Local p 30 = p 30 := rfl
  have ha0 : (payloadAncNat p == 0) = false := beq_eq_false_iff_ne.mpr hanc
  unfold PosPostPrep80MergedVep_Bhmt.muActualFactor80
  dsimp only
  simp only [Bool.not_false, ↓reduceIte]
  let q := PosPostPrep80MergedVepS3.flipTailDpScratch80 (p80ClearB0Local p)
  have hq30 : (q 30 == 1) = true := by
    dsimp only [q]
    unfold PosPostPrep80MergedVepS3.flipTailDpScratch80
    rw [hp30, h30, ite_eq_left rfl, hp30, h30]
  have hqanc : Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦
      q (pos80SubIdx 14 8 (by decide) j)) = payloadAncNat p := by
    have hfn : (fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j)) =
        fun j : Fin 8 ↦ p (pos80SubIdx 14 8 (by decide) j) := by
      funext j; dsimp only [q]
      unfold PosPostPrep80MergedVepS3.flipTailDpScratch80
      rw [hp30, h30, ite_eq_left rfl]
      dsimp [p80ClearB0Local, pos80SubIdx]
      rw [ite_eq_right (by have := j.isLt; omega)]
    rw [hfn]; rfl
  dsimp only [q] at hq30 hqanc
  rw [ite_eq_left hq30]
  by_cases hk : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 6 ↦
        PosPostPrep80MergedVepS3.flipTailDpScratch80
          (p80ClearB0Local p) (pos80SubIdx 63 6 (by decide) j)) < 56
  · rw [dite_eq_left hk]
    simp only [hqanc, ha0, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · rw [dite_eq_right hk]

private theorem setAnc80_subIdx_eq {o k : ℕ} (hok : o + k ≤ 80) (hd : o + k ≤ 14 ∨ 22 ≤ o)
    (a : ℕ) (q : BitAssignment 80) :
    (fun j : Fin k ↦ setAnc80 a q (pos80SubIdx o k hok j)) =
      fun j : Fin k ↦ q (pos80SubIdx o k hok j) :=
  funext fun j ↦ ite_eq_right (by
    have := j.isLt
    dsimp [pos80SubIdx]
    omega)

private theorem update62_setAnc80 (a : ℕ) (q : BitAssignment 80) :
    Function.update (setAnc80 a q) 62 0 = setAnc80 a (Function.update q 62 0) := by
  funext i
  dsimp [Function.update, setAnc80]
  by_cases hi : i = 62
  · subst hi
    simp
  · simp [hi]

private theorem setAnc80_zero_update62_of_anc0 (q : BitAssignment 80)
    (hanc : payloadAncNat q = 0) :
    setAnc80 0 (Function.update q 62 0) = Function.update q 62 0 := by
  have hs := ApproxBlockCommFerm.setAnc80_self_zero (Function.update q 62 0)
  have ha : payloadAncNat (Function.update q 62 0) = 0 :=
    (ApproxBlockCommFerm.payloadAncNat_update_62 q).trans hanc
  rwa [ha, ApproxBlockCommFerm.setAnc80_idem] at hs

private theorem beq_eq_of_iff {α : Type*} [BEq α] [LawfulBEq α] {x y z w : α}
    (h : x = y ↔ z = w) : (x == y) = (z == w) := by
  by_cases hzw : z = w
  · rw [beq_iff_eq.mpr (h.mpr hzw), beq_iff_eq.mpr hzw]
  · rw [beq_eq_false_iff_ne.mpr (mt h.mp hzw), beq_eq_false_iff_ne.mpr hzw]

private theorem muActualFactor80_Bhmt_slot2_tail_setAnc80 (a : Fin 218) (p₀ : BitAssignment 80)
    (h30 : ¬ (p₀ 30 == 1) = true) (hanc0 : payloadAncNat p₀ = 0) :
    PosPostPrep80MergedVep_Bhmt.muActualFactor80 true false (setAnc80 a.val p₀) =
      PosPostPrep80MergedVep_Bhmt.muActualFactor80 true false p₀ := by
  have hclear : p80ClearB0Local (setAnc80 a.val p₀) = setAnc80 a.val (p80ClearB0Local p₀) :=
    p80ClearB0Local_setAnc80 a.val p₀
  have hp30' : p80ClearB0Local p₀ 30 = p₀ 30 := rfl
  have hflip :
      PosPostPrep80MergedVepS3.flipTailDpScratch80
          (setAnc80 a.val (p80ClearB0Local p₀)) =
        setAnc80 a.val
          (PosPostPrep80MergedVepS3.flipTailDpScratch80 (p80ClearB0Local p₀)) := by
    let p₁ := p80ClearB0Local p₀
    have hp30 : setAnc80 a.val p₁ 30 = p₀ 30 := rfl
    have h0 : setAnc80 a.val p₁ 0 = p₁ 0 := rfl
    have h1' : setAnc80 a.val p₁ 1 = p₁ 1 := rfl
    have h2 : setAnc80 a.val p₁ 2 = p₁ 2 := rfl
    have h75' : setAnc80 a.val p₁ 75 = p₁ 75 := rfl
    have h76' : setAnc80 a.val p₁ 76 = p₁ 76 := rfl
    have h77' : setAnc80 a.val p₁ 77 = p₁ 77 := rfl
    unfold PosPostPrep80MergedVepS3.flipTailDpScratch80
    rw [hp30, hp30', ite_eq_right h30, ite_eq_right h30]
    funext q
    rw [h0, h1', h2, h75', h76', h77']
    by_cases h1 : 14 ≤ q.val ∧ q.val < 22
    · have h75 : (q.val == 75) = false := beq_eq_false_iff_ne.mpr (by omega)
      have h76 : (q.val == 76) = false := beq_eq_false_iff_ne.mpr (by omega)
      have h77 : (q.val == 77) = false := beq_eq_false_iff_ne.mpr (by omega)
      simp only [h75, h76, h77, Bool.false_eq_true, ↓reduceIte]
      dsimp only [setAnc80]
      rw [ite_eq_left h1, ite_eq_left h1]
    · dsimp only [setAnc80]
      rw [ite_eq_right h1, ite_eq_right h1]
  unfold PosPostPrep80MergedVep_Bhmt.muActualFactor80
  dsimp only
  simp only [Bool.not_false, ↓reduceIte, hclear, hflip]
  let q₀ := PosPostPrep80MergedVepS3.flipTailDpScratch80 (p80ClearB0Local p₀)
  have hq_anc0 : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ q₀ (pos80SubIdx 14 8 (by decide) j)) = 0 := by
    have hfn : (fun j : Fin 8 ↦ q₀ (pos80SubIdx 14 8 (by decide) j)) =
        fun j : Fin 8 ↦ p₀ (pos80SubIdx 14 8 (by decide) j) := by
      funext j; dsimp only [q₀]
      unfold PosPostPrep80MergedVepS3.flipTailDpScratch80
      rw [hp30', ite_eq_right h30]
      fin_cases j <;> rfl
    rw [hfn]; exact hanc0
  have hq30 : ¬ (q₀ 30 == 1) = true := by
    have hq30_eq : q₀ 30 = p₀ 30 := by
      dsimp only [q₀]
      unfold PosPostPrep80MergedVepS3.flipTailDpScratch80
      rw [hp30', ite_eq_right h30]; rfl
    rwa [hq30_eq]
  have hout : ∀ (idx : Fin 80), ¬ (14 ≤ idx.val ∧ idx.val < 22) → setAnc80 a.val q₀ idx = q₀ idx :=
    fun idx h ↦ ite_eq_right h
  have hb0_raw := setAnc80_subIdx_eq (by decide : 3 + 3 ≤ 80) (Or.inl (by decide)) a.val p₀
  have hb0 := setAnc80_subIdx_eq (by decide : 3 + 3 ≤ 80) (Or.inl (by decide)) a.val q₀
  have hnuc := setAnc80_subIdx_eq (by decide : 6 + 8 ≤ 80) (Or.inl (by decide)) a.val q₀
  have hpart := setAnc80_subIdx_eq (by decide : 22 + 8 ≤ 80) (Or.inr (by decide)) a.val q₀
  have hfine := setAnc80_subIdx_eq (by decide : 32 + 30 ≤ 80) (Or.inr (by decide)) a.val q₀
  have hscrIdx := setAnc80_subIdx_eq (by decide : 63 + 12 ≤ 80) (Or.inr (by decide)) a.val q₀
  have hscr : (∀ j : Fin 12, setAnc80 a.val q₀ (pos80SubIdx 63 12 (by decide) j) = 0) ↔
      (∀ j : Fin 12, q₀ (pos80SubIdx 63 12 (by decide) j) = 0) :=
    forall_congr' fun j ↦ by rw [congrFun hscrIdx j]
  have hdp := setAnc80_subIdx_eq (by decide : 75 + 3 ≤ 80) (Or.inr (by decide)) a.val q₀
  have h30' : setAnc80 a.val q₀ 30 = q₀ 30 := hout 30 (by decide)
  have h31' : setAnc80 a.val q₀ 31 = q₀ 31 := hout 31 (by decide)
  have h62' : setAnc80 a.val q₀ 62 = q₀ 62 := hout 62 (by decide)
  have h78' : setAnc80 a.val q₀ 78 = q₀ 78 := hout 78 (by decide)
  have h79' : setAnc80 a.val q₀ 79 = q₀ 79 := hout 79 (by decide)
  have hanc_a : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ setAnc80 a.val q₀ (pos80SubIdx 14 8 (by decide) j)) = a.val :=
    ApproxBlockCommFerm.payloadAncNat_setAnc80 (lt_trans a.isLt (by decide)) q₀
  have hupd := update62_setAnc80 a.val q₀
  have hbeq : ∀ (b0 nuc part : ℕ) (dp : Fin 8) (fine30 : ℕ) (th rj : Bool),
      (setAnc80 a.val (Function.update q₀ 62 0) ==
          PosPostPrep80MergedVepS3.tailWitnessPayload80
            b0 nuc a.val part dp fine30 th rj) =
        (Function.update q₀ 62 0 ==
          PosPostPrep80MergedVepS3.tailWitnessPayload80
            b0 nuc 0 part dp fine30 th rj) := by
    intro b0 nuc part dp fine30 th rj
    refine beq_eq_of_iff ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have h0 := congrArg (setAnc80 0) h
      rwa [ApproxBlockCommFerm.setAnc80_idem,
        ApproxBlockCommFerm.tailWitnessPayload80_setAnc80,
        setAnc80_zero_update62_of_anc0 q₀ hq_anc0] at h0
    · rw [h, ApproxBlockCommFerm.tailWitnessPayload80_setAnc80]
  have hbhmt : ∀ (V : ℕ) (dp : Fin 8) (fine30 : ℕ) (bRej : Bool),
      PosPostPrep80MergedVep_Bhmt.muxTailBhmtProb false a.val V dp fine30 bRej =
        PosPostPrep80MergedVep_Bhmt.muxTailBhmtProb false 0 V dp fine30 bRej := by
    intro V dp fine30 bRej
    unfold PosPostPrep80MergedVep_Bhmt.muxTailBhmtProb
    cases bRej
    · have ha : decide (a.val < 218) = true := decide_eq_true a.isLt
      have h0 : decide (0 < 218) = true := rfl
      simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte, ha, h0, Bool.true_and]
    · rfl
  dsimp only [q₀] at hq_anc0 hq30 hb0 hnuc hpart hfine hscr hdp h30' h31' h62' h78' h79' hanc_a
  dsimp only [q₀] at hupd hbeq
  rw [h30', ite_eq_right hq30, ite_eq_right hq30]
  simp only [hb0_raw, hb0, hnuc, hpart, hfine, hanc_a, hq_anc0,
    Bool.false_eq_true, ↓reduceIte, h31', h62', h78', h79',
    hupd, decide_eq_decide.mpr hscr, hdp, hbeq, hbhmt]

private theorem muActualFactor80_Bhmt_slot4_head_setAnc80 (a : Fin 218) (p₀ : BitAssignment 80)
    (h30 : (p₀ 30 == 1) = true) (hanc0 : payloadAncNat p₀ = 0) :
    PosPostPrep80MergedVep_Bhmt.muActualFactor80 true true (setAnc80 a.val p₀) =
      PosPostPrep80MergedVep_Bhmt.muActualFactor80 true true p₀ := by
  have hout : ∀ (idx : Fin 80), ¬ (14 ≤ idx.val ∧ idx.val < 22) → setAnc80 a.val p₀ idx = p₀ idx :=
    fun idx h ↦ ite_eq_right h
  unfold PosPostPrep80MergedVep_Bhmt.muActualFactor80
  dsimp only
  have hb0 := setAnc80_subIdx_eq (by decide : 3 + 3 ≤ 80) (Or.inl (by decide)) a.val p₀
  have hnuc := setAnc80_subIdx_eq (by decide : 6 + 8 ≤ 80) (Or.inl (by decide)) a.val p₀
  have hpart := setAnc80_subIdx_eq (by decide : 22 + 8 ≤ 80) (Or.inr (by decide)) a.val p₀
  have hkVal := setAnc80_subIdx_eq (by decide : 63 + 6 ≤ 80) (Or.inr (by decide)) a.val p₀
  have hpidVal := setAnc80_subIdx_eq (by decide : 69 + 3 ≤ 80) (Or.inr (by decide)) a.val p₀
  have hsmVal := setAnc80_subIdx_eq (by decide : 72 + 3 ≤ 80) (Or.inr (by decide)) a.val p₀
  have hanc_a : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ setAnc80 a.val p₀ (pos80SubIdx 14 8 (by decide) j)) = a.val :=
    ApproxBlockCommFerm.payloadAncNat_setAnc80 (lt_trans a.isLt (by decide)) p₀
  have hanc_0 : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ p₀ (pos80SubIdx 14 8 (by decide) j)) = 0 := hanc0
  have h30' : setAnc80 a.val p₀ 30 = p₀ 30 := hout 30 (by decide)
  have h31' : setAnc80 a.val p₀ 31 = p₀ 31 := hout 31 (by decide)
  have h62' : setAnc80 a.val p₀ 62 = p₀ 62 := hout 62 (by decide)
  have h75' : setAnc80 a.val p₀ 75 = p₀ 75 := hout 75 (by decide)
  have h76' : setAnc80 a.val p₀ 76 = p₀ 76 := hout 76 (by decide)
  have h77' : setAnc80 a.val p₀ 77 = p₀ 77 := hout 77 (by decide)
  have h78' : setAnc80 a.val p₀ 78 = p₀ 78 := hout 78 (by decide)
  have h79' : setAnc80 a.val p₀ 79 = p₀ 79 := hout 79 (by decide)
  have hupd := update62_setAnc80 a.val p₀
  have hgen_set : ∀ (b0 nuc a₁ a₂ : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8) (th rj : Bool),
      setAnc80 a₁
        (PosPostPrep80MergedVepS3.headGeneralPayload80
          b0 nuc a₂ k pidVal sm th rj) =
      PosPostPrep80MergedVepS3.headGeneralPayload80
        b0 nuc a₁ k pidVal sm th rj := by
    intro b0 nuc a₁ a₂ k pidVal sm th rj
    exact ApproxBlockCommFerm.headJointPayload80_setAnc80 b0 nuc a₁ a₂ 0 k pidVal sm th rj
  have hbeq : ∀ (b0 nuc : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8) (th rj : Bool),
      (setAnc80 a.val (Function.update p₀ 62 0) ==
          PosPostPrep80MergedVepS3.headGeneralPayload80
            b0 nuc a.val k pidVal sm th rj) =
        (Function.update p₀ 62 0 ==
          PosPostPrep80MergedVepS3.headGeneralPayload80
            b0 nuc 0 k pidVal sm th rj) := by
    intro b0 nuc k pidVal sm th rj
    refine beq_eq_of_iff ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have h0 := congrArg (setAnc80 0) h
      rwa [ApproxBlockCommFerm.setAnc80_idem, hgen_set,
        setAnc80_zero_update62_of_anc0 p₀ hanc0] at h0
    · rw [h, hgen_set]
  have hbhmt : ∀ (pidVal : ℕ) (bRej : Bool),
      PosPostPrep80MergedVep_Bhmt.muxHeadBhmtProb a.val pidVal bRej =
        PosPostPrep80MergedVep_Bhmt.muxHeadBhmtProb 0 pidVal bRej := by
    intro pidVal bRej
    unfold PosPostPrep80MergedVep_Bhmt.muxHeadBhmtProb
    cases bRej
    · have ha : decide (a.val < 218) = true := decide_eq_true a.isLt
      have h0 : decide (0 < 218) = true := rfl
      simp only [Bool.not_false, ↓reduceIte, ha, h0, Bool.true_and]
    · rfl
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hb0, hnuc, hpart, hanc_a, hanc_0,
    h30', h30, h31', h62', h75', h76', h77', h78', h79', hkVal, hpidVal, hsmVal, hupd]
  by_cases hk : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 6 ↦ p₀ (pos80SubIdx 63 6 (by decide) j)) < 56
  · rw [dite_eq_left hk, dite_eq_left hk, hbeq, hbhmt]
  · rw [dite_eq_right hk, dite_eq_right hk]

private theorem muActualFactor80_Bhmt_slot4_tail_setAnc80_setPart80
    (a : Fin 218) (pt : Fin 217) (p₀ : BitAssignment 80)
    (h30 : ¬ (p₀ 30 == 1) = true) (hanc0 : payloadAncNat p₀ = 0) (hpart0 : payloadPartNat p₀ = 0) :
    PosPostPrep80MergedVep_Bhmt.muActualFactor80 true true
        (setAnc80 a.val (setPart80 pt.val p₀)) =
      PosPostPrep80MergedVep_Bhmt.muActualFactor80 true true p₀ := by
  set p' := setAnc80 a.val (setPart80 pt.val p₀)
  have hout : ∀ (idx : Fin 80), ¬ (14 ≤ idx.val ∧ idx.val < 30) → p' idx = p₀ idx := by
    intro idx h
    dsimp [p', setAnc80, setPart80]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  unfold PosPostPrep80MergedVep_Bhmt.muActualFactor80
  dsimp only
  have hb0 : (fun j : Fin 3 ↦ p' (pos80SubIdx 3 3 (by decide) j)) =
      fun j : Fin 3 ↦ p₀ (pos80SubIdx 3 3 (by decide) j) :=
    funext fun j ↦ hout _ (by have := j.isLt; dsimp [pos80SubIdx]; omega)
  have hnuc : (fun j : Fin 8 ↦ p' (pos80SubIdx 6 8 (by decide) j)) =
      fun j : Fin 8 ↦ p₀ (pos80SubIdx 6 8 (by decide) j) :=
    funext fun j ↦ hout _ (by have := j.isLt; dsimp [pos80SubIdx]; omega)
  have hfine : (fun j : Fin 30 ↦ p' (pos80SubIdx 32 30 (by decide) j)) =
      fun j : Fin 30 ↦ p₀ (pos80SubIdx 32 30 (by decide) j) :=
    funext fun j ↦ hout _ (by have := j.isLt; dsimp [pos80SubIdx]; omega)
  have hscr : (∀ j : Fin 12, p' (pos80SubIdx 63 12 (by decide) j) = 0) ↔
      (∀ j : Fin 12, p₀ (pos80SubIdx 63 12 (by decide) j) = 0) :=
    forall_congr' fun j ↦ by rw [hout _ (by have := j.isLt; dsimp [pos80SubIdx]; omega)]
  have hdp : (fun j : Fin 3 ↦ p' (pos80SubIdx 75 3 (by decide) j)) =
      fun j : Fin 3 ↦ p₀ (pos80SubIdx 75 3 (by decide) j) :=
    funext fun j ↦ hout _ (by have := j.isLt; dsimp [pos80SubIdx]; omega)
  have hanc_a : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ p' (pos80SubIdx 14 8 (by decide) j)) = a.val :=
    ApproxBlockCommFerm.payloadAncNat_setAnc80 (lt_trans a.isLt (by decide)) (setPart80 pt.val p₀)
  have hpart_pt : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ p' (pos80SubIdx 22 8 (by decide) j)) = pt.val := by
    change payloadPartNat p' = pt.val
    rw [ApproxBlockCommFerm.payloadPartNat_setAnc80,
      ApproxBlockCommFerm.payloadPartNat_setPart80 (lt_trans pt.isLt (by decide))]
  have hanc_0 : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ p₀ (pos80SubIdx 14 8 (by decide) j)) = 0 := hanc0
  have hpart_0 : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ p₀ (pos80SubIdx 22 8 (by decide) j)) = 0 := hpart0
  have h30' : p' 30 = p₀ 30 := hout 30 (by decide)
  have h31' : p' 31 = p₀ 31 := hout 31 (by decide)
  have h62' : p' 62 = p₀ 62 := hout 62 (by decide)
  have h78' : p' 78 = p₀ 78 := hout 78 (by decide)
  have h79' : p' 79 = p₀ 79 := hout 79 (by decide)
  have hupd : Function.update p' 62 0 =
      setAnc80 a.val (setPart80 pt.val (Function.update p₀ 62 0)) := by
    rw [update62_setAnc80]
    congr 1
    funext q
    by_cases hq62 : q = 62
    · subst hq62
      simp [Function.update, setPart80]
    · simp [Function.update, setPart80, hq62]
  have hbeq : ∀ (b0 nuc : ℕ) (dp : Fin 8) (fine30 : ℕ) (th rj : Bool),
      (setAnc80 a.val (setPart80 pt.val (Function.update p₀ 62 0)) ==
          PosPostPrep80MergedVepS3.tailWitnessPayload80
            b0 nuc a.val pt.val dp fine30 th rj) =
        (Function.update p₀ 62 0 ==
          PosPostPrep80MergedVepS3.tailWitnessPayload80
            b0 nuc 0 0 dp fine30 th rj) := by
    intro b0 nuc dp fine30 th rj
    refine beq_eq_of_iff ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have h0 := congrArg (fun x ↦ setPart80 0 (setAnc80 0 x)) h
      rw [ApproxBlockCommFerm.setAnc80_idem,
        ApproxBlockCommFerm.setAnc80_setPart80_comm 0 pt.val,
        ApproxBlockCommFerm.setPart80_idem,
        ApproxBlockCommFerm.tailWitnessPayload80_setAnc80,
        ApproxBlockCommFerm.tailWitnessPayload80_setPart80,
        setAnc80_zero_update62_of_anc0 p₀ hanc0] at h0
      have hp_upd : payloadPartNat (Function.update p₀ 62 0) = 0 :=
        (ApproxBlockCommFerm.payloadPartNat_update_62 p₀).trans hpart0
      have hsP := ApproxBlockCommFerm.setPart80_self_zero (Function.update p₀ 62 0)
      rw [hp_upd, ApproxBlockCommFerm.setPart80_idem] at hsP
      rwa [hsP] at h0
    · rw [h, ApproxBlockCommFerm.tailWitnessPayload80_setPart80,
        ApproxBlockCommFerm.tailWitnessPayload80_setAnc80]
  have hbhmt : ∀ (dp : Fin 8) (fine30 : ℕ) (bRej : Bool),
      PosPostPrep80MergedVep_Bhmt.muxTailBhmtProb true a.val pt.val dp fine30 bRej =
        PosPostPrep80MergedVep_Bhmt.muxTailBhmtProb true 0 0 dp fine30 bRej := by
    intro dp fine30 bRej
    unfold PosPostPrep80MergedVep_Bhmt.muxTailBhmtProb
    cases bRej
    · have ha : decide (a.val < 218) = true := decide_eq_true a.isLt
      have hpt : decide (pt.val < 217) = true := decide_eq_true pt.isLt
      have h0a : decide (0 < 218) = true := rfl
      have h0p : decide (0 < 217) = true := rfl
      simp only [↓reduceIte, Bool.not_false, ha, hpt, h0a, h0p, Bool.true_and]
    · rfl
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hb0, hnuc, hfine, hanc_a, hpart_pt,
    hanc_0, hpart_0, h30', Bool.eq_false_iff.mpr h30, h31', h62', h78', h79', hupd,
    decide_eq_decide.mpr hscr, hdp, hbeq, hbhmt]

private theorem muBhmt_slot2_head_ge128_eq_zero
    (p : BitAssignment 80) (h30 : (p 30 == 1) = true) (hnot : ¬ payloadAncNat p < 128) :
    muBhmt false p = 0 := by
  rw [payloadAncNat_eq_subIdx] at hnot
  have hb7 : p (pos80SubIdx 14 8 (by decide) ⟨7, by decide⟩) ≠ 0 :=
    bitsVal8_bit7_ne_zero_of_not_lt128 _ hnot
  have hqb7 : projBhmt false p (pos80SubIdx 14 8 (by decide) ⟨7, by decide⟩) =
      p (pos80SubIdx 14 8 (by decide) ⟨7, by decide⟩) := by
    unfold projBhmt; simp only [Bool.false_eq_true, ↓reduceIte, h30]; split_ifs <;> rfl
  have hq30 : (projBhmt false p 30 == 1) = true := by
    have heq : projBhmt false p 30 = p 30 := by
      unfold projBhmt; simp only [Bool.false_eq_true, ↓reduceIte, h30]; split_ifs <;> rfl
    rwa [heq]
  have hqanc : payloadAncNat (projBhmt false p) ≠ 0 := by
    rw [payloadAncNat_eq_subIdx]
    exact bitsVal8_ne_zero_of_bit7_ne_zero _ (hqb7.symm ▸ hb7)
  unfold muBhmt
  rw [muActualFactor80_Bhmt_slot2_head_eq_zero_of_anc_ne_z _ hq30 hqanc, mul_zero]

private theorem clrPid12_80_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    clrPid12_80 (setAnc80 a p) = setAnc80 a (clrPid12_80 p) := by
  funext q; dsimp [clrPid12_80, Function.update, setAnc80]
  by_cases h71 : q = 71
  · subst h71; simp
  · by_cases h70 : q = 70
    · subst h70; simp
    · simp [h71, h70]

private theorem p80ClearRange62_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    p80ClearRange 6 2 (setAnc80 a p) = setAnc80 a (p80ClearRange 6 2 p) := by
  funext q; dsimp [p80ClearRange, setAnc80]
  by_cases h1 : 6 ≤ q.val ∧ q.val < 6 + 2
  · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left h1]
  · rw [ite_eq_right h1]; split_ifs <;> rfl

private theorem clrPid12_80_setPart80 (pt : ℕ) (p : BitAssignment 80) :
    clrPid12_80 (setPart80 pt p) = setPart80 pt (clrPid12_80 p) := by
  funext q; dsimp [clrPid12_80, Function.update, setPart80]
  by_cases h71 : q = 71
  · subst h71; simp
  · by_cases h70 : q = 70
    · subst h70; simp
    · simp [h71, h70]

private theorem fiberWeightBhmt_setAnc80 (s0 : Bool) (a : ℕ) (p : BitAssignment 80) :
    fiberWeightBhmt s0 (setAnc80 a p) = fiberWeightBhmt s0 p := by
  have hnuc : (fun j : Fin 8 ↦ setAnc80 a p (pos80SubIdx 6 8 (by decide) j)) =
      fun j : Fin 8 ↦ p (pos80SubIdx 6 8 (by decide) j) :=
    funext fun j ↦ by fin_cases j <;> rfl
  have h30 : setAnc80 a p 30 = p 30 := rfl
  unfold fiberWeightBhmt; dsimp only; rw [hnuc, h30]

private theorem fiberWeightBhmt_setPart80 (s0 : Bool) (pt : ℕ) (p : BitAssignment 80) :
    fiberWeightBhmt s0 (setPart80 pt p) = fiberWeightBhmt s0 p := by
  have hnuc : (fun j : Fin 8 ↦ setPart80 pt p (pos80SubIdx 6 8 (by decide) j)) =
      fun j : Fin 8 ↦ p (pos80SubIdx 6 8 (by decide) j) :=
    funext fun j ↦ by fin_cases j <;> rfl
  have h30 : setPart80 pt p 30 = p 30 := rfl
  unfold fiberWeightBhmt; dsimp only; rw [hnuc, h30]

private theorem muBhmt_slot2_tail_setAnc80 (a : Fin 218) (p₀ : BitAssignment 80)
    (h30 : ¬ (p₀ 30 == 1) = true) (hanc0 : payloadAncNat p₀ = 0) :
    muBhmt false (setAnc80 a.val p₀) = muBhmt false p₀ := by
  have hnuc : (fun j : Fin 8 ↦ setAnc80 a.val p₀ (pos80SubIdx 6 8 (by decide) j)) =
      fun j : Fin 8 ↦ p₀ (pos80SubIdx 6 8 (by decide) j) :=
    funext fun j ↦ by fin_cases j <;> rfl
  have hs30 : setAnc80 a.val p₀ 30 = p₀ 30 := rfl
  have hproj : projBhmt false (setAnc80 a.val p₀) = setAnc80 a.val (projBhmt false p₀) := by
    unfold projBhmt
    simp only [Bool.false_eq_true, ↓reduceIte, hnuc, hs30, h30]
    split_ifs
    · exact clrPid12_80_setAnc80 a.val p₀
    · rw [clrPid12_80_setAnc80, p80ClearB0Local_setAnc80]
  have hq30 : ¬ (projBhmt false p₀ 30 == 1) = true := by
    have heq : projBhmt false p₀ 30 = p₀ 30 := by
      unfold projBhmt; simp only [Bool.false_eq_true, ↓reduceIte, h30]; split_ifs <;> rfl
    rwa [heq]
  have hqanc0 : payloadAncNat (projBhmt false p₀) = 0 := by
    have heq : payloadAncNat (projBhmt false p₀) = payloadAncNat p₀ := by
      unfold projBhmt; simp only [Bool.false_eq_true, ↓reduceIte, h30]
      split_ifs <;>
        (unfold payloadAncNat; exact congrArg bitsVal (funext fun j ↦ by fin_cases j <;> rfl))
    exact heq.trans hanc0
  unfold muBhmt
  rw [fiberWeightBhmt_setAnc80, hproj, muActualFactor80_Bhmt_slot2_tail_setAnc80 a _ hq30 hqanc0]

/-- Exact electron-permutation symmetry of the actual `PosPostBhmt` Mod-4 merged Slot-2 + `V_ep`
operator `tierBB2ActMod4BhmtOf tM cfg` for arbitrary `tM` and `cfg`. -/
theorem tierBB2ActMod4BhmtOf_comm_pElMat
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (g : Equiv.Perm (Fin numElectrons)) :
    tierBB2ActMod4BhmtOf tM cfg * pElMat g = pElMat g * tierBB2ActMod4BhmtOf tM cfg := by
  let sysSlice : Configuration → BitAssignment 80 → Operator (2 ^ systemQubits) :=
    fun c' p' ↦ sysBlock80Mod4Of tM tierBQftFull c' false p'
  let term : BitAssignment 80 → Operator (2 ^ systemQubits) :=
    fun p ↦ (muBhmt false p : ℂ) • mergedSliceGen sysSlice cfg p
  change (∑ p : BitAssignment 80, term p) * pElMat g = pElMat g * (∑ p : BitAssignment 80, term p)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun p : BitAssignment 80 ↦ payloadAncNat p < 218) term,
    Matrix.add_mul, Matrix.mul_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun p : BitAssignment 80 ↦ payloadAncNat p < 218)
      (fun p : BitAssignment 80 ↦ (p 30 == 1) = true) term,
      Matrix.add_mul, Matrix.mul_add]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rcases Finset.mem_filter.mp hp with ⟨_, hp30⟩
      by_cases hanc128 : payloadAncNat p < 128
      · dsimp only [term]
        rw [Matrix.smul_mul, Matrix.mul_smul]
        refine congrArg ((muBhmt false p : ℂ) • ·) ?_
        unfold mergedSliceGen
        by_cases hnuc : p80NucVal p < 216
        · rw [ite_eq_left hnuc]
          exact blkSmSlot2Mod4Of_head_lt128_comm_pElMat tM cfg p hp30 hanc128 hnuc g
        · rw [ite_eq_right hnuc]
          refine mProj24_wrap_comm_pElMat (p80CosetP3 p) _ g fun yIdx ↦ ?_
          have hpz30 : (p80SetNucZero p 30 == 1) = true := hp30
          have hpz_anc : payloadAncNat (p80SetNucZero p) < 128 := by
            rwa [payloadAncNat_p80SetNucZero]
          exact blkSmSlot2Mod4Of_head_lt128_comm_pElMat tM _ (p80SetNucZero p) hpz30 hpz_anc
            (by rw [payloadNucNat_p80SetNucZero]; decide) g
      · dsimp only [term]
        rw [muBhmt_slot2_head_ge128_eq_zero p hp30 hanc128,
          Complex.ofReal_zero, zero_smul, Matrix.zero_mul, Matrix.mul_zero]
    · have hfilt : (Finset.univ.filter fun p : BitAssignment 80 ↦ payloadAncNat p < 218).filter
          (fun p ↦ ¬ (p 30 == 1) = true) =
          Finset.univ.filter (fun p : BitAssignment 80 ↦
            ¬ (p 30 == 1) = true ∧ payloadAncNat p < 218) := by
        ext p; simp [and_comm]
      rw [hfilt, sum_bitAssignment80_anc_lt218
          (fun p ↦ ¬ (p 30 == 1) = true) (fun _ _ ↦ Iff.rfl) term,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p₀ hp₀ ↦ ?_
      rcases (Finset.mem_filter.mp hp₀).2 with ⟨h30, hanc0⟩
      have hpull : (∑ a : Fin 218, term (setAnc80 a.val p₀)) =
          (muBhmt false p₀ : ℂ) •
            ∑ a : Fin 218, mergedSliceGen sysSlice cfg (setAnc80 a.val p₀) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by
          dsimp only [term]; rw [muBhmt_slot2_tail_setAnc80 a p₀ h30 hanc0]
      rw [hpull, Matrix.smul_mul, Matrix.mul_smul]
      refine congrArg ((muBhmt false p₀ : ℂ) • ·) ?_
      by_cases hnuc : p80NucVal p₀ < 216
      · have hsl : ∀ a : Fin 218, mergedSliceGen sysSlice cfg (setAnc80 a.val p₀) =
            sysSlice cfg (setAnc80 a.val p₀) := fun a ↦ by
          unfold mergedSliceGen; rw [p80NucVal_setAnc80, ite_eq_left hnuc]
        simp_rw [hsl]
        exact blkSmSlot2Mod4Of_tail_sum_anc_comm_pElMat tM cfg p₀ h30 hanc0 hnuc g
      · have hsl : ∀ a : Fin 218, mergedSliceGen sysSlice cfg (setAnc80 a.val p₀) =
            (mProj24_sp.embedUnitary (uProjPlus512_3D (p80CosetP3 p₀))).1ᴴ *
              (∑ yIdx : Fin (2 ^ 24), mProjBasisGen mProj24_sp yIdx *
                sysSlice (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, p80CosetP3 p₀)))
                  (setAnc80 a.val (p80SetNucZero p₀))) *
              (mProj24_sp.embedUnitary (uProjPlus512_3D (p80CosetP3 p₀))).1 := fun a ↦ by
          unfold mergedSliceGen
          rw [p80NucVal_setAnc80, ite_eq_right hnuc, p80CosetP3_setAnc80, p80SetNucZero_setAnc80]
        simp_rw [hsl]
        have hswap_sum :
            (∑ a : Fin 218,
              (mProj24_sp.embedUnitary (uProjPlus512_3D (p80CosetP3 p₀))).1ᴴ *
                (∑ yIdx : Fin (2 ^ 24), mProjBasisGen mProj24_sp yIdx *
                  sysSlice (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, p80CosetP3 p₀)))
                    (setAnc80 a.val (p80SetNucZero p₀))) *
                (mProj24_sp.embedUnitary (uProjPlus512_3D (p80CosetP3 p₀))).1) =
            (mProj24_sp.embedUnitary (uProjPlus512_3D (p80CosetP3 p₀))).1ᴴ *
              (∑ yIdx : Fin (2 ^ 24), mProjBasisGen mProj24_sp yIdx *
                (∑ a : Fin 218,
                  sysSlice (cfgProjZ512 (nyq512ProjEquiv3D (mProjGridEquiv24 yIdx, p80CosetP3 p₀)))
                    (setAnc80 a.val (p80SetNucZero p₀)))) *
              (mProj24_sp.embedUnitary (uProjPlus512_3D (p80CosetP3 p₀))).1 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_comm]
          simp_rw [← Finset.mul_sum]
        rw [hswap_sum]
        refine mProj24_wrap_comm_pElMat (p80CosetP3 p₀) _ g fun yIdx ↦ ?_
        exact blkSmSlot2Mod4Of_tail_sum_anc_comm_pElMat tM _ (p80SetNucZero p₀) h30
          ((payloadAncNat_p80SetNucZero p₀).trans hanc0)
          (by rw [payloadNucNat_p80SetNucZero]; decide) g
  · rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hnanc : ¬ payloadAncNat p < 218 := (Finset.mem_filter.mp hp).2
    dsimp only [term]
    rw [Matrix.smul_mul, Matrix.mul_smul]
    refine congrArg ((muBhmt false p : ℂ) • ·) ?_
    unfold mergedSliceGen
    by_cases hnuc : p80NucVal p < 216
    · rw [ite_eq_left hnuc]
      dsimp only [sysSlice]
      rw [sysBlock80Mod4Of_eq_smul_one_of_phase_const tM cfg false p (p ⟨79, by decide⟩ == 1)
          (posPhaseBitMod4_const_of_rejected tM false p (Or.inr (Or.inr (Or.inl hnanc)))),
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    · rw [ite_eq_right hnuc]
      refine mProj24_wrap_comm_pElMat (p80CosetP3 p) _ g fun yIdx ↦ ?_
      dsimp only [sysSlice]
      have hnanc0 : ¬ payloadAncNat (p80SetNucZero p) < 218 := by
        rwa [payloadAncNat_p80SetNucZero]
      rw [sysBlock80Mod4Of_eq_smul_one_of_phase_const tM _ false (p80SetNucZero p)
          (p80SetNucZero p ⟨79, by decide⟩ == 1)
          (posPhaseBitMod4_const_of_rejected tM false _ (Or.inr (Or.inr (Or.inl hnanc0)))),
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

private theorem muBhmt_slot4_head_setAnc80 (a : Fin 218) (p₀ : BitAssignment 80)
    (h30 : (p₀ 30 == 1) = true) (hanc0 : payloadAncNat p₀ = 0) :
    muBhmt true (setAnc80 a.val p₀) = muBhmt true p₀ := by
  have hs30 : setAnc80 a.val p₀ 30 = p₀ 30 := rfl
  have hproj : projBhmt true (setAnc80 a.val p₀) = setAnc80 a.val (projBhmt true p₀) := by
    unfold projBhmt; simp only [↓reduceIte, hs30, h30]
    exact p80ClearRange62_setAnc80 a.val p₀
  have hq30 : (projBhmt true p₀ 30 == 1) = true := by
    have heq : projBhmt true p₀ 30 = p₀ 30 := by
      unfold projBhmt; simp only [↓reduceIte, h30]; rfl
    rwa [heq]
  have hqanc0 : payloadAncNat (projBhmt true p₀) = 0 := by
    have heq : payloadAncNat (projBhmt true p₀) = payloadAncNat p₀ := by
      unfold projBhmt; simp only [↓reduceIte, h30]
      unfold payloadAncNat
      exact congrArg bitsVal (funext fun j ↦ by fin_cases j <;> rfl)
    exact heq.trans hanc0
  unfold muBhmt
  rw [fiberWeightBhmt_setAnc80, hproj, muActualFactor80_Bhmt_slot4_head_setAnc80 a _ hq30 hqanc0]

private theorem muBhmt_slot4_tail_setAnc80_setPart80
    (a : Fin 218) (pt : Fin 217) (p₀ : BitAssignment 80)
    (h30 : ¬ (p₀ 30 == 1) = true) (hanc0 : payloadAncNat p₀ = 0) (hpart0 : payloadPartNat p₀ = 0) :
    muBhmt true (setAnc80 a.val (setPart80 pt.val p₀)) = muBhmt true p₀ := by
  have hs30 : setAnc80 a.val (setPart80 pt.val p₀) 30 = p₀ 30 := rfl
  have hproj : projBhmt true (setAnc80 a.val (setPart80 pt.val p₀)) =
      setAnc80 a.val (setPart80 pt.val (projBhmt true p₀)) := by
    have h30f : (p₀ 30 == 1) = false := Bool.eq_false_iff.mpr h30
    unfold projBhmt; simp only [Bool.false_eq_true, ↓reduceIte, hs30, h30]
    rw [clrPid12_80_setAnc80, clrPid12_80_setPart80]
  have hq30 : ¬ (projBhmt true p₀ 30 == 1) = true := by
    have heq : projBhmt true p₀ 30 = p₀ 30 := by
      unfold projBhmt; simp only [↓reduceIte, h30]; rfl
    rwa [heq]
  have hqanc0 : payloadAncNat (projBhmt true p₀) = 0 := by
    have heq : payloadAncNat (projBhmt true p₀) = payloadAncNat p₀ := by
      unfold projBhmt; simp only [↓reduceIte, h30]
      unfold payloadAncNat
      exact congrArg bitsVal (funext fun j ↦ by fin_cases j <;> rfl)
    exact heq.trans hanc0
  have hqpart0 : payloadPartNat (projBhmt true p₀) = 0 := by
    have heq : payloadPartNat (projBhmt true p₀) = payloadPartNat p₀ := by
      unfold projBhmt; simp only [↓reduceIte, h30]
      unfold payloadPartNat
      exact congrArg bitsVal (funext fun j ↦ by fin_cases j <;> rfl)
    exact heq.trans hpart0
  unfold muBhmt
  rw [fiberWeightBhmt_setAnc80, fiberWeightBhmt_setPart80, hproj,
    muActualFactor80_Bhmt_slot4_tail_setAnc80_setPart80 a pt _ hq30 hqanc0 hqpart0]

/-- Exact electron-permutation symmetry of the actual `PosPostBhmt` Mod-4 Slot-4 operator
`tierBB4ActMod4BhmtOf tM cfg` for arbitrary `tM` and `cfg`. -/
theorem tierBB4ActMod4BhmtOf_comm_pElMat
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (g : Equiv.Perm (Fin numElectrons)) :
    tierBB4ActMod4BhmtOf tM cfg * pElMat g = pElMat g * tierBB4ActMod4BhmtOf tM cfg := by
  let term : BitAssignment 80 → Operator (2 ^ systemQubits) :=
    fun p ↦ (muBhmt true p : ℂ) • sysBlock80Mod4Of tM tierBQftFull cfg true p
  change (∑ p : BitAssignment 80, term p) * pElMat g = pElMat g * (∑ p : BitAssignment 80, term p)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun p : BitAssignment 80 ↦ payloadAncNat p < 218) term,
    Matrix.add_mul, Matrix.mul_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun p : BitAssignment 80 ↦ payloadAncNat p < 218)
      (fun p : BitAssignment 80 ↦ (p 30 == 1) = true) term,
      Matrix.add_mul, Matrix.mul_add]
    refine congrArg₂ (· + ·) ?_ ?_
    · have hfilt : (Finset.univ.filter fun p : BitAssignment 80 ↦ payloadAncNat p < 218).filter
          (fun p ↦ (p 30 == 1) = true) =
          Finset.univ.filter (fun p : BitAssignment 80 ↦
            (p 30 == 1) = true ∧ payloadAncNat p < 218) := by
        ext p; simp [and_comm]
      rw [hfilt, sum_bitAssignment80_anc_lt218
          (fun p ↦ (p 30 == 1) = true) (fun _ _ ↦ Iff.rfl) term,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p₀ hp₀ ↦ ?_
      rcases (Finset.mem_filter.mp hp₀).2 with ⟨h30, hanc0⟩
      have hpull : (∑ a : Fin 218, term (setAnc80 a.val p₀)) =
          (muBhmt true p₀ : ℂ) •
            ∑ a : Fin 218, sysBlock80Mod4Of tM tierBQftFull cfg true (setAnc80 a.val p₀) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by
          dsimp only [term]; rw [muBhmt_slot4_head_setAnc80 a p₀ h30 hanc0]
      rw [hpull, Matrix.smul_mul, Matrix.mul_smul,
        blkSmSlot4Mod4Of_head_sum_anc_comm_pElMat tM cfg p₀ h30 hanc0 g]
    · rw [← Finset.sum_filter_add_sum_filter_not
        ((Finset.univ.filter fun p : BitAssignment 80 ↦ payloadAncNat p < 218).filter
          fun p ↦ ¬ (p 30 == 1) = true)
        (fun p : BitAssignment 80 ↦ payloadPartNat p < 217) term,
        Matrix.add_mul, Matrix.mul_add]
      refine congrArg₂ (· + ·) ?_ ?_
      · have hfilt : (((Finset.univ.filter fun p : BitAssignment 80 ↦ payloadAncNat p < 218).filter
            fun p ↦ ¬ (p 30 == 1) = true).filter fun p ↦ payloadPartNat p < 217) =
            Finset.univ.filter (fun p : BitAssignment 80 ↦
              ¬ (p 30 == 1) = true ∧ payloadAncNat p < 218 ∧ payloadPartNat p < 217) := by
          ext p; simp [and_left_comm, and_comm]
        rw [hfilt, sum_bitAssignment80_anc_part_lt
            (fun p ↦ ¬ (p 30 == 1) = true) (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) term,
          Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p₀ hp₀ ↦ ?_
        rcases (Finset.mem_filter.mp hp₀).2 with ⟨⟨h30, hpart0⟩, hanc0⟩
        have hpull : (∑ a : Fin 218, ∑ pt : Fin 217,
              term (setAnc80 a.val (setPart80 pt.val p₀))) =
            (muBhmt true p₀ : ℂ) •
              ∑ a : Fin 218, ∑ pt : Fin 217,
                sysBlock80Mod4Of tM tierBQftFull cfg true (setAnc80 a.val (setPart80 pt.val p₀)) :=
                  by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun pt _ ↦ by
            dsimp only [term]
            rw [muBhmt_slot4_tail_setAnc80_setPart80 a pt p₀ h30 hanc0 hpart0]
        rw [hpull, Matrix.smul_mul, Matrix.mul_smul,
          blkSmSlot4Mod4Of_tail_sum_anc_part_comm_pElMat tM cfg p₀ h30 hanc0 hpart0 g]
      · rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rcases Finset.mem_filter.mp hp with ⟨hp1, hnpart⟩
        have h30 : (p 30 == 1) = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hp1).2
        dsimp only [term]
        rw [sysBlock80Mod4Of_eq_smul_one_of_phase_const tM cfg true p (p ⟨79, by decide⟩ == 1)
            (posPhaseBitMod4_const_of_rejected tM true p (Or.inr (Or.inr (Or.inr ⟨rfl, h30,
              hnpart⟩)))),
          Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one]
  · rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hnanc : ¬ payloadAncNat p < 218 := (Finset.mem_filter.mp hp).2
    dsimp only [term]
    rw [sysBlock80Mod4Of_eq_smul_one_of_phase_const tM cfg true p (p ⟨79, by decide⟩ == 1)
        (posPhaseBitMod4_const_of_rejected tM true p (Or.inr (Or.inr (Or.inl hnanc)))),
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]

-- ============================================================================
-- Section 3: Arbitrary-`s1` Core Blocks & `PosPostBhmt` `RawBEBlockCommutesFerm`
-- ============================================================================

private theorem combineFourMomSingleSlotOracles_alg
    {uBarrel : Configuration → Unitary (2 ^ (momCoreWires 80))}
    (l0 : MomSlot0LocalAndMomCombine288.MomLocalSlotData 80 48 0 uBarrel)
    (s1 : MomSingleSlotOracle 80 48 1)
    (l3 : MomSlot0LocalAndMomCombine288.MomLocalSlotData 80 48 3 uBarrel)
    (l5 : MomSlot0LocalAndMomCombine288.MomLocalSlotData 80 48 5 uBarrel)
    (cfg : Configuration) :
    let u01 := s1.uSlotEff cfg * l0.uLocalEff cfg
    let u35 := l5.uLocalEff cfg * l3.uLocalEff cfg
    let uAll := u35 * u01
    uAll.1 * momCoinProj 80 4 = (l0.uLocalEff cfg).1 * momCoinProj 80 4 ∧
      uAll.1 * momCoinProj 80 5 = (s1.uSlotEff cfg).1 * momCoinProj 80 5 ∧
      uAll.1 * momCoinProj 80 6 = (l3.uLocalEff cfg).1 * momCoinProj 80 6 ∧
      uAll.1 * momCoinProj 80 7 = (l5.uLocalEff cfg).1 * momCoinProj 80 7 := by
  have hc0 : fullSysCoinIdx 0 = 4 := rfl
  have hc1 : fullSysCoinIdx 1 = 5 := rfl
  have hc3 : fullSysCoinIdx 3 = 6 := rfl
  have hc5 : fullSysCoinIdx 5 = 7 := rfl
  have h01 := FullSysMomSlots0135Concrete.disjoint_two_proj_comm_and_sum
    (momCoinProj 80 4) (momCoinProj 80 5)
    (l0.uLocalEff cfg) (s1.uSlotEff cfg)
    (FullSysMomSlots0135Concrete.momCoinProj_conjTranspose 80 4)
    (FullSysMomSlots0135Concrete.momCoinProj_conjTranspose 80 5)
    (FullSysMomSlots0135Concrete.momCoinProj_mul_of_ne 80 (by decide : (4 : Fin 8) ≠ 5))
    (FullSysMomSlots0135Concrete.momCoinProj_mul_of_ne 80 (by decide : (5 : Fin 8) ≠ 4))
    (hc0 ▸ l0.hLocalOffCoin cfg) (hc1 ▸ s1.hOffCoin cfg)
    (l0.hLocalSA cfg) (s1.hSA cfg)
  have h35 := FullSysMomSlots0135Concrete.disjoint_two_proj_comm_and_sum
    (momCoinProj 80 6) (momCoinProj 80 7)
    (l3.uLocalEff cfg) (l5.uLocalEff cfg)
    (FullSysMomSlots0135Concrete.momCoinProj_conjTranspose 80 6)
    (FullSysMomSlots0135Concrete.momCoinProj_conjTranspose 80 7)
    (FullSysMomSlots0135Concrete.momCoinProj_mul_of_ne 80 (by decide : (6 : Fin 8) ≠ 7))
    (FullSysMomSlots0135Concrete.momCoinProj_mul_of_ne 80 (by decide : (7 : Fin 8) ≠ 6))
    (hc3 ▸ l3.hLocalOffCoin cfg) (hc5 ▸ l5.hLocalOffCoin cfg)
    (l3.hLocalSA cfg) (l5.hLocalSA cfg)
  have hOff01 : (s1.uSlotEff cfg * l0.uLocalEff cfg).1 *
      (1 - FullSysMomSlots0135Concrete.slot45MomProj 80) =
      1 - FullSysMomSlots0135Concrete.slot45MomProj 80 := by
    rw [← FullSysMomSlots0135Concrete.momCoinProj_4_add_5_eq_slot45 80]
    exact h01.2.2.2.2.1
  have hOff35 : (l5.uLocalEff cfg * l3.uLocalEff cfg).1 *
      (1 - FullSysMomSlots0135Concrete.slot67MomProj 80) =
      1 - FullSysMomSlots0135Concrete.slot67MomProj 80 := by
    rw [← FullSysMomSlots0135Concrete.momCoinProj_6_add_7_eq_slot67 80]
    exact h35.2.2.2.2.1
  have hP45_sa : (FullSysMomSlots0135Concrete.slot45MomProj 80)ᴴ =
      FullSysMomSlots0135Concrete.slot45MomProj 80 := by
    rw [FullSysMomSlots0135Concrete.slot45MomProj, Matrix.conjTranspose_mul,
      slotBitProj_self_adj, slotBitProj_self_adj, FullSysMomSlots0135Concrete.slotBitProj_comm_any]
  have hP67_sa : (FullSysMomSlots0135Concrete.slot67MomProj 80)ᴴ =
      FullSysMomSlots0135Concrete.slot67MomProj 80 := by
    rw [FullSysMomSlots0135Concrete.slot67MomProj, Matrix.conjTranspose_mul,
      slotBitProj_self_adj, slotBitProj_self_adj, FullSysMomSlots0135Concrete.slotBitProj_comm_any]
  have hAll := FullSysMomSlots0135Concrete.disjoint_two_proj_comm_and_sum
    (FullSysMomSlots0135Concrete.slot45MomProj 80)
    (FullSysMomSlots0135Concrete.slot67MomProj 80)
    (s1.uSlotEff cfg * l0.uLocalEff cfg)
    (l5.uLocalEff cfg * l3.uLocalEff cfg)
    hP45_sa hP67_sa
    (FullSysMomSlots0135Concrete.slot45MomProj_mul_slot67MomProj 80)
    (FullSysMomSlots0135Concrete.slot67MomProj_mul_slot45MomProj 80)
    hOff01 hOff35 h01.2.1 h35.2.1
  have hAbsorb : ∀ (c : Fin 8) (P U V : Operator (2 ^ momCoreWires 80)),
      P * momCoinProj 80 c = momCoinProj 80 c →
      ((l5.uLocalEff cfg * l3.uLocalEff cfg) *
          (s1.uSlotEff cfg * l0.uLocalEff cfg)).1 * P = U * P →
      U * momCoinProj 80 c = V * momCoinProj 80 c →
      ((l5.uLocalEff cfg * l3.uLocalEff cfg) *
          (s1.uSlotEff cfg * l0.uLocalEff cfg)).1 * momCoinProj 80 c =
        V * momCoinProj 80 c := by
    intro c P U V habs hUP hUV
    rw [← habs, ← Matrix.mul_assoc, hUP, Matrix.mul_assoc, habs, hUV]
  exact ⟨hAbsorb 4 _ _ _
      (FullSysMomSlots0135Concrete.slot45MomProj_mul_momCoinProj 80 (by decide) (by decide))
      hAll.2.2.1 h01.2.2.1,
    hAbsorb 5 _ _ _
      (FullSysMomSlots0135Concrete.slot45MomProj_mul_momCoinProj 80 (by decide) (by decide))
      hAll.2.2.1 h01.2.2.2.1,
    hAbsorb 6 _ _ _
      (FullSysMomSlots0135Concrete.slot67MomProj_mul_momCoinProj 80 (by decide) (by decide))
      hAll.2.2.2.1 h35.2.2.1,
    hAbsorb 7 _ _ _
      (FullSysMomSlots0135Concrete.slot67MomProj_mul_momCoinProj 80 (by decide) (by decide))
      hAll.2.2.2.1 h35.2.2.2.1⟩

set_option backward.isDefEq.respectTransparency false in
theorem ora1Pwu24OfBSub_uBarrelFast_conj_on_coin5
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24) (cfg : Configuration) :
    (HoistedSwapSelectBridge.unitaryConj
        (coreUnitaryFromFullSys (uBarrelFast (le_refl 80)))
        ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff cfg)).1 *
      momCoinProj 80 5 =
    ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff cfg).1 * momCoinProj 80 5 := by
  have h := (mkSlot1Pwu24FastDataOfBarrel bSub hbLo hbHi (le_refl 80) tierBBarrel80).hConjOnCoin cfg
  change (HoistedSwapSelectBridge.unitaryConj
      (coreUnitaryFromFullSys (tierBBarrel80.uBarrel cfg))
      ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff cfg)).1 *
    momCoinProj 80 5 =
    ((ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)).uSlotEff cfg).1 * momCoinProj 80 5 at h
  have hBEq : tierBBarrel80.uBarrel cfg = uBarrelFast (le_refl 80) :=
    FastCoinBarrel288.fastHoistedBarrelSpec145_uBarrel (le_refl 80) cfg
  rwa [hBEq] at h

private theorem step_mom_coins_of_oraHypS1 {t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    {selOra : FullSysSelectOracleBundle 80 48}
    {s1 : MomSingleSlotOracle 80 48 1}
    {leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat}
    {s3 : MomSingleSlotOracle 80 48 3}
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1 leaf2 s3)
    (hS1Conj : ∀ c,
      (HoistedSwapSelectBridge.unitaryConj
          (coreUnitaryFromFullSys (uBarrelFast (le_refl 80)))
          (s1.uSlotEff c)).1 *
        momCoinProj 80 5 =
      (s1.uSlotEff c).1 * momCoinProj 80 5)
    (cfg : Configuration) :
    let uMom := coreUnitaryFromFullSys (selOra.uMomPhase cfg)
    let s0 := slot0ElectronKineticOracleSym (le_refl 80)
    let s5 := zeroMomSlotOracle5 80 48
    uMom.1 * momCoinProj 80 4 = (s0.uSlotEff cfg).1 * momCoinProj 80 4 ∧
      uMom.1 * momCoinProj 80 5 = (s1.uSlotEff cfg).1 * momCoinProj 80 5 ∧
      uMom.1 * momCoinProj 80 6 = (s3.uSlotEff cfg).1 * momCoinProj 80 6 ∧
      uMom.1 * momCoinProj 80 7 = (s5.uSlotEff cfg).1 * momCoinProj 80 7 := by
  let hBEq : ∀ c, tierBBarrel80.uBarrel c = uBarrelFast (le_refl 80) :=
    FastCoinBarrel288.fastHoistedBarrelSpec145_uBarrel (le_refl 80)
  let l0 := mkSlot0LocalDataOfBarrelFast (le_refl 80) tierBBarrel80.uBarrel hBEq
  let l3 := liftSlot3OfBarrelFast (le_refl 80) s3 tierBBarrel80.uBarrel hBEq
  let l5 := tierBL5Zero80
  let B := coreUnitaryFromFullSys (tierBBarrel80.uBarrel cfg)
  let uAll := (l5.uLocalEff cfg * l3.uLocalEff cfg) * (s1.uSlotEff cfg * l0.uLocalEff cfg)
  have hBHigh : ∀ (q : Wire (momCoreWires 80)), 3924 ≤ q.val → ∀ bit : Fin 2,
      B.1 * slotBitProj q bit = slotBitProj q bit * B.1 :=
    fun q hq bit ↦
      TierClosure.castNatUnitary_comm_slotBitProj (momCoreWires_eq_fullSysCoreWires 80)
        (tierBBarrel80.uBarrel cfg) (tierBBarrel80.hHighWireComm cfg) q hq bit
  have hMomEq : (coreUnitaryFromFullSys (selOra.uMomPhase cfg)).1 =
      (HoistedSwapSelectBridge.unitaryConj B uAll).1 := by
    rw [hOra.hMom cfg, ← hBEq cfg]
    exact TierClosure.castNatUnitary_conj_val_eq
      (momCoreWires_eq_fullSysCoreWires 80).symm (tierBBarrel80.uBarrel cfg) uAll
  have hS1B : (HoistedSwapSelectBridge.unitaryConj B (s1.uSlotEff cfg)).1 * momCoinProj 80 5 =
      (s1.uSlotEff cfg).1 * momCoinProj 80 5 := by
    dsimp only [B]; rw [hBEq cfg]; exact hS1Conj cfg
  have hAlg := combineFourMomSingleSlotOracles_alg l0 s1 l3 l5 cfg
  dsimp only
  rw [hMomEq]
  exact ⟨(MomSlot0LocalAndMomCombine288.unitaryConj_on_coin_transfer 4 B uAll _
      (MomSlot0LocalAndMomCombine288.barrel_comm_momCoinProj B hBHigh 4) hAlg.1).trans
      (l0.hConjOnCoin cfg),
    (MomSlot0LocalAndMomCombine288.unitaryConj_on_coin_transfer 5 B uAll _
      (MomSlot0LocalAndMomCombine288.barrel_comm_momCoinProj B hBHigh 5) hAlg.2.1).trans
      hS1B,
    (MomSlot0LocalAndMomCombine288.unitaryConj_on_coin_transfer 6 B uAll _
      (MomSlot0LocalAndMomCombine288.barrel_comm_momCoinProj B hBHigh 6) hAlg.2.2.1).trans
      (l3.hConjOnCoin cfg),
    (MomSlot0LocalAndMomCombine288.unitaryConj_on_coin_transfer 7 B uAll _
      (MomSlot0LocalAndMomCombine288.barrel_comm_momCoinProj B hBHigh 7) hAlg.2.2.2).trans
      (l5.hConjOnCoin cfg)⟩

private theorem step_select_core_blocks_of_oraHypS1
    {mWorkPos t2Ctrl t2Cat : ℕ}
    {truncFn : Configuration → Configuration}
    (qftCore : FullSysQft654Bundle)
    (hqftFactor : tierBQftFull.uQft654 =
      qftCore.uQft654 * FusedPreDiagFromTwist288.uPre654)
    (post : PosPostPrepCert 80)
    (hSuppPost01 : ∀ c : Fin 8, c.val < 2 →
      momCoinProj 80 c *
        ((post.uPosPost * coreHadamardUnitary 80).1 *
          (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)) =
      (post.uPosPost * coreHadamardUnitary 80).1 *
        (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c))
    (selOra : FullSysSelectOracleBundle 80 48)
    (s1 : MomSingleSlotOracle 80 48 1)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (posData : PosSlots24DataGen (fullSysCoreWires 80) (iSlot2 80) mWorkPos)
    (hPosDataEq : ∀ cfg, posData.uPosPhase cfg = leaf2.uPosPhase0)
    (hPosCommSlot : ∀ (wFlag : Wire (fullSysCoreWires 80)),
      3948 ≤ wFlag.val → wFlag.val < 3954 → ∀ b : Fin 2,
        leaf2.uPosPhase0.1 * slotBitProj wFlag b = slotBitProj wFlag b * leaf2.uPosPhase0.1)
    (s3 : MomSingleSlotOracle 80 48 3)
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1 leaf2 s3)
    (hS1Conj : ∀ c0,
      (HoistedSwapSelectBridge.unitaryConj
          (coreUnitaryFromFullSys (uBarrelFast (le_refl 80)))
          (s1.uSlotEff c0)).1 *
        momCoinProj 80 5 =
      (s1.uSlotEff c0).1 * momCoinProj 80 5)
    (b2Act b4Act : Configuration → Operator (2 ^ systemQubits))
    (hTopCoin0 : ∀ cfg,
      topCoinPropGen (le_rfl : 80 ≤ 80) tierBQftFull cfg post
        (fun c0 ↦ uVepTwistCutRef (by decide : 22 ≤ 80) (truncFn c0)) posData 0 (b2Act cfg))
    (hTopCoin1 : ∀ cfg,
      topCoinPropGen (le_rfl : 80 ≤ 80) tierBQftFull cfg post
        (fun c0 ↦ uVepTwistCutRef (by decide : 22 ≤ 80) (truncFn c0)) posData 1 (b4Act cfg))
    (cfg : Configuration) :
    let S_core := unitaryConj (post.uPosPost * coreHadamardUnitary 80)
      (coreUnitaryFromFullSys (fullSysSelectEffUnitary qftCore selOra cfg))
    let B_coin := bCoinGenS1S3S5
      (slot0ElectronKineticOracleSym (le_refl 80)) s1 s3 (zeroMomSlotOracle5 80 48)
      b2Act b4Act cfg
    S_core.1ᴴ = S_core.1 ∧
      (∀ c : Fin 8,
        let P_c := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)
        P_c * S_core.1 * P_c = P_c * (coreSysSym 80).embedMatrix (B_coin c) * P_c) ∧
      (∀ c₁ c₂ : Fin 8, c₁ ≠ c₂ →
        let P₁ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₁)
        let P₂ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₂)
        P₁ * S_core.1 * P₂ = 0) := by
  let s0 := slot0ElectronKineticOracleSym (le_refl 80)
  let s5 := zeroMomSlotOracle5 80 48
  let uPreCore : Configuration → Unitary (2 ^ (fullSysCoreWires 80)) :=
    fun c0 ↦
      (coreElecCosetB1Block (by decide : 6 ≤ 80)).embedUnitary
        FusedPreDiagFromTwist288.uPre654 * uVepTwistCutRef (by decide : 22 ≤ 80) (truncFn c0)
  have hPreBit : ∀ (wq : Wire (fullSysCoreWires 80)),
      3924 ≤ wq.val → wq.val < 3954 → ∀ b : Fin 2,
      ((coreElecCosetB1Block (by decide : 6 ≤ 80)).embedUnitary
          FusedPreDiagFromTwist288.uPre654).1 * slotBitProj wq b =
        slotBitProj wq b *
          ((coreElecCosetB1Block (by decide : 6 ≤ 80)).embedUnitary
            FusedPreDiagFromTwist288.uPre654).1 := fun wq hw1 hw2 b ↦ by
    have hwOut := wire_not_mem_coreElecCosetB1 (by decide : 6 ≤ 80) hw1 hw2
    rw [QRegister.embedUnitary_val, slotBitProj]
    exact embedMatrix_comm_diagonal_of_outside (coreElecCosetB1Block (by decide : 6 ≤ 80))
      FusedPreDiagFromTwist288.uPre654.1 _ fun i j hOut ↦ by rw [hOut wq hwOut]
  have hPreComm2 : (uPreCore cfg).1 * slotBitProj (iSlot2 80) 0 =
      slotBitProj (iSlot2 80) 0 * (uPreCore cfg).1 :=
    FullSysHoistedSelectStitch.mul_comm_of_comm
      (hPreBit (iSlot2 80) (by dsimp [iSlot2]; omega) (by dsimp [iSlot2]; omega) 0)
      (uVepTwistCutRef_comm_slot2 (by decide : 22 ≤ 80) (truncFn cfg))
  have hPreComm1 : (uPreCore cfg).1 * slotBitProj (iSlot1 80) 0 =
      slotBitProj (iSlot1 80) 0 * (uPreCore cfg).1 :=
    FullSysHoistedSelectStitch.mul_comm_of_comm
      (hPreBit (iSlot1 80) (by dsimp [iSlot1]; omega) (by dsimp [iSlot1]; omega) 0)
      (uVepTwistCutRef_comm_slot1 (by decide : 22 ≤ 80) (truncFn cfg))
  have hFactorEq :
      fullSysQftCoreUnitary (by decide : 6 ≤ 80) qftCore * uPreCore cfg =
        fullSysQftCoreUnitary (by decide : 6 ≤ 80) tierBQftFull *
          uVepTwistCutRef (by decide : 22 ≤ 80) (truncFn cfg) := by
    unfold uPreCore fullSysQftCoreUnitary
    rw [← mul_assoc, ← QRegister.embedUnitary_mul, ← hqftFactor]
  let hCoreEq := (momCoreWires_eq_fullSysCoreWires 80).symm
  let S_flag := fullSysSelectEffUnitary qftCore selOra cfg
  let S_raw := coreUnitaryFromFullSys S_flag
  let S_post := unitaryConj post.uPosPost S_raw
  let W_post := post.uPosPost * coreHadamardUnitary 80
  let S_core := unitaryConj W_post S_raw
  have hS_split := fullSysSelectEffUnitary_conjTranspose_and_split qftCore selOra cfg
  have hS_raw_sa : S_raw.1ᴴ = S_raw.1 := by
    dsimp only [S_raw, coreUnitaryFromFullSys]
    rw [castNatOp_val_unitary, ← castNatOp_conjTranspose, hS_split.2]
  have hS_core_sa : S_core.1ᴴ = S_core.1 :=
    PosMomSelectDynamic.unitaryConj_conjTranspose hS_raw_sa
  have hTwistComm2 := step_hTwist_s2_s1 hOra cfg
  have hTwistComm1 := step_hTwist_s1_s1 hOra cfg
  have hTwistComm0 : ∀ b : Fin 2,
      (selOra.uTwist cfg).1 * slotBitProj (iSlot0 80) b =
        slotBitProj (iSlot0 80) b * (selOra.uTwist cfg).1 :=
    fun b ↦ step_uTwist_comm_slotBitProj_s1 hOra cfg
      (by dsimp [iSlot0]; omega) (by dsimp [iSlot0]; omega) b
  have hSelSlack2 :
      let P_c2 := slotBitProj (iSlot2 80) 0 * slotBitProj (iSlot1 80) 1 * slotBitProj (iSlot0 80) 0
      (selOra.uPosPhase cfg).1 * P_c2 = (1 : ℂ) • P_c2 := by
    intro P_c2; rw [hOra.hPosEq cfg, one_smul]; exact leaf2.hPosSlack2
  have hSelSlack3 :
      let P_c3 := slotBitProj (iSlot2 80) 0 * slotBitProj (iSlot1 80) 1 * slotBitProj (iSlot0 80) 1
      (selOra.uPosPhase cfg).1 * P_c3 = (-1 : ℂ) • P_c3 := by
    intro P_c3; rw [hOra.hPosEq cfg, neg_one_smul]; exact leaf2.hPosSlack3
  have hSlack2_S :
      let P_c2 := slotBitProj (iSlot2Mom 80) 0 * slotBitProj (iSlot1Mom 80) 1 *
        slotBitProj (iSlot0Mom 80) 0
      S_raw.1 * P_c2 = (1 : ℂ) • P_c2 := by
    intro P_c2
    have hFlag := fullSysSelectEffUnitary_on_slackCoin qftCore selOra cfg 0
      hTwistComm2 hTwistComm1 (hTwistComm0 0) hSelSlack2
    have hCast := congrArg (castNatOp hCoreEq) hFlag
    simpa only [S_raw, coreUnitaryFromFullSys, P_c2, castNatOp_val_unitary, castNatOp_mul,
      castNatOp_smul, Fin.val_zero, ↓reduceIte,
      castNatOp_slotBitProj hCoreEq (iSlot2 80) (iSlot2Mom 80) rfl 0,
      castNatOp_slotBitProj hCoreEq (iSlot1 80) (iSlot1Mom 80) rfl 1,
      castNatOp_slotBitProj hCoreEq (iSlot0 80) (iSlot0Mom 80) rfl 0] using hCast
  have hSlack3_S :
      let P_c3 := slotBitProj (iSlot2Mom 80) 0 * slotBitProj (iSlot1Mom 80) 1 *
        slotBitProj (iSlot0Mom 80) 1
      S_raw.1 * P_c3 = (-1 : ℂ) • P_c3 := by
    intro P_c3
    have hFlag := fullSysSelectEffUnitary_on_slackCoin qftCore selOra cfg 1
      hTwistComm2 hTwistComm1 (hTwistComm0 1) hSelSlack3
    have hCast := congrArg (castNatOp hCoreEq) hFlag
    simpa only [S_raw, S_flag, coreUnitaryFromFullSys, P_c3, castNatOp_val_unitary, castNatOp_mul,
      castNatOp_smul, Fin.val_one, Nat.one_ne_zero, ↓reduceIte,
      castNatOp_slotBitProj hCoreEq (iSlot2 80) (iSlot2Mom 80) rfl 0,
      castNatOp_slotBitProj hCoreEq (iSlot1 80) (iSlot1Mom 80) rfl 1,
      castNatOp_slotBitProj hCoreEq (iSlot0 80) (iSlot0Mom 80) rfl 1] using hCast
  have hFusedOnP01 : (selOra.uTwist cfg).1 * posCoin01Proj 80 =
      (uPreCore cfg).1 * posCoin01Proj 80 := by
    rw [hOra.hTw cfg]
    exact JunctionProj3DCutPos24BridgeGen.hoistedTwistOut_fastCut_fusedOnP01 (by decide : 22 ≤ 80)
      (uTwistRest := SchedBranchStitchGen.uVepFusedTwistRestCut80)
      (uBarrel := fun _ ↦ CoinDispatchedBarrel288.uBarrelFast (le_refl 80))
      (truncFn cfg) (truncFn cfg) rfl
      (by
        rw [← FastCoinBarrel288.fastHoistedBarrelSpec145_uBarrel (le_refl 80) (truncFn cfg)]
        exact tierBBarrel80_onP01 (truncFn cfg))
  let U_out := fullSysQftCoreUnitary (by decide : 6 ≤ 80) qftCore * uPreCore cfg
  let S_posFlag := unitaryConj U_out (posData.uPosPhase cfg)
  let S_posRef := coreUnitaryFromFullSys S_posFlag
  have hS_pos_flag : S_flag.1 * posCoin01Proj 80 = S_posFlag.1 * posCoin01Proj 80 := by
    have hS_p0 : S_flag.1 * slotBitProj (iSlot2 80) 0 =
        (fullSysSelectPosUnitary qftCore selOra cfg).1 * slotBitProj (iSlot2 80) 0 := by
      rw [hS_split.1, Matrix.add_mul, Matrix.mul_assoc, slotBitProj_mul_idem,
        Matrix.mul_assoc, FullSysMomSlots0135Concrete.slotBitProj_one_mul_zero_eq_zero,
        Matrix.mul_zero, add_zero]
    have hAbs : slotBitProj (iSlot2 80) 0 * posCoin01Proj 80 = posCoin01Proj 80 := by
      unfold posCoin01Proj; rw [← Matrix.mul_assoc, slotBitProj_mul_idem]
    calc S_flag.1 * posCoin01Proj 80
        = (S_flag.1 * slotBitProj (iSlot2 80) 0) * posCoin01Proj 80 := by
            rw [Matrix.mul_assoc, hAbs]
      _ = (fullSysSelectPosUnitary qftCore selOra cfg).1 * posCoin01Proj 80 := by
            rw [hS_p0, Matrix.mul_assoc, hAbs]
      _ = S_posFlag.1 * posCoin01Proj 80 :=
            fullSysSelectPosUnitary_eq_on_posCoin01_out (by decide : 6 ≤ 80) qftCore selOra
              (uPreCore cfg) (posData.uPosPhase cfg) cfg
              (posData.hPos_sa cfg) (posData.hPos_on_P1 cfg)
              (by rw [hPosDataEq cfg]; exact leaf2.hPosSlack2)
              (by rw [hPosDataEq cfg]; exact leaf2.hPosSlack3)
              (by rw [hOra.hPosEq cfg, hPosDataEq cfg])
              hTwistComm1 hPreComm2 hPreComm1 hFusedOnP01
  have hS_pos_branch01 : S_raw.1 * posCoin01ProjMom 80 =
      S_posRef.1 * posCoin01ProjMom 80 := by
    have hCast := congrArg (castNatOp hCoreEq) hS_pos_flag
    simpa only [S_raw, S_posRef, coreUnitaryFromFullSys, posCoin01Proj, posCoin01ProjMom,
      castNatOp_val_unitary, castNatOp_mul,
      castNatOp_slotBitProj hCoreEq (iSlot2 80) (iSlot2Mom 80) rfl 0,
      castNatOp_slotBitProj hCoreEq (iSlot1 80) (iSlot1Mom 80) rfl 0] using hCast
  have hCommP01 := postPrep_comm_posCoin01ProjMom post.uPosPost post.hPosPost_nonPos
  have hMomCoins := step_mom_coins_of_oraHypS1 hOra hS1Conj cfg
  let B_coin := bCoinGenS1S3S5 s0 s1 s3 s5 b2Act b4Act cfg
  have hCoreEqConj : S_core = unitaryConj (coreHadamardUnitary 80) S_post :=
    unitaryConj_mul_outer post.uPosPost (coreHadamardUnitary 80) S_raw
  have hDiag : ∀ c : Fin 8,
      let P_c := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)
      P_c * S_core.1 * P_c = P_c * (coreSysSym 80).embedMatrix (B_coin c) * P_c := by
    intro c
    dsimp only
    rw [hCoreEqConj, (unitaryConj_mul_outer post.uPosPost (coreHadamardUnitary 80) S_raw).symm]
    fin_cases c
    · have h0 := postPrep_pos01_branch_eq post.uPosPost S_raw S_posRef 0 rfl rfl
        hCommP01 hS_pos_branch01
      rw [coreAncSym_eq_momAncReg_sym 80, selCoin3Sym_eq_momCoin3Sel_sym 80,
        coreHadamardUnitary_eq_mom_sym 80]
      exact h0.trans (by
        rw [← coreAncSym_eq_momAncReg_sym 80, ← selCoin3Sym_eq_momCoin3Sel_sym 80,
          ← coreHadamardUnitary_eq_mom_sym 80]
        dsimp only [S_posRef, S_posFlag, U_out, B_coin, bCoinGenS1S3S5]
        rw [hFactorEq]; exact hTopCoin0 cfg)
    · have h1 := postPrep_pos01_branch_eq post.uPosPost S_raw S_posRef 1 rfl rfl
        hCommP01 hS_pos_branch01
      rw [coreAncSym_eq_momAncReg_sym 80, selCoin3Sym_eq_momCoin3Sel_sym 80,
        coreHadamardUnitary_eq_mom_sym 80]
      exact h1.trans (by
        rw [← coreAncSym_eq_momAncReg_sym 80, ← selCoin3Sym_eq_momCoin3Sel_sym 80,
          ← coreHadamardUnitary_eq_mom_sym 80]
        dsimp only [S_posRef, S_posFlag, U_out, B_coin, bCoinGenS1S3S5]
        rw [hFactorEq]; exact hTopCoin1 cfg)
    · rw [coreAncSym_eq_momAncReg_sym 80, selCoin3Sym_eq_momCoin3Sel_sym 80,
        coreSysSym_eq_momSysReg_sym 80, coreHadamardUnitary_eq_mom_sym 80]
      exact (postPrep_nonPos_topBlock post.uPosPost S_raw 2
        (post.hPosPost_nonPos 2 (by decide))).trans
        (coreHadamard_conj_slack_block_gen 0 S_raw hSlack2_S)
    · rw [coreAncSym_eq_momAncReg_sym 80, selCoin3Sym_eq_momCoin3Sel_sym 80,
        coreSysSym_eq_momSysReg_sym 80, coreHadamardUnitary_eq_mom_sym 80]
      exact (postPrep_nonPos_topBlock post.uPosPost S_raw 3
        (post.hPosPost_nonPos 3 (by decide))).trans
        (coreHadamard_conj_slack_block_gen 1 S_raw hSlack3_S)
    all_goals
      rw [coreAncSym_eq_momAncReg_sym 80, selCoin3Sym_eq_momCoin3Sel_sym 80,
        coreSysSym_eq_momSysReg_sym 80, coreHadamardUnitary_eq_mom_sym 80]
      refine (postPrep_nonPos_topBlock post.uPosPost S_raw _
        (post.hPosPost_nonPos _ (by decide))).trans
        ((conjHadamard_branch_topBlock_of_eq_on_coin _ S_raw
          (coreUnitaryFromFullSys (selOra.uMomPhase cfg))
          (fullSysSelectEffUnitary_on_momCoin_sym qftCore selOra cfg _ rfl)).trans ?_)
    · exact (conjHadamard_branch_topBlock_of_eq_on_coin 4 _ _ hMomCoins.1).trans
        (s0.hTopBlock cfg)
    · exact (conjHadamard_branch_topBlock_of_eq_on_coin 5 _ _ hMomCoins.2.1).trans
        (s1.hTopBlock cfg)
    · exact (conjHadamard_branch_topBlock_of_eq_on_coin 6 _ _ hMomCoins.2.2.1).trans
        (s3.hTopBlock cfg)
    · exact (conjHadamard_branch_topBlock_of_eq_on_coin 7 _ _ hMomCoins.2.2.2).trans
        (s5.hTopBlock cfg)
  have hS_posRef_comm_slot : ∀ (wFlag : Wire (fullSysCoreWires 80))
      (wMom : Wire (momCoreWires 80)),
      wFlag.val = wMom.val → 3948 ≤ wFlag.val → wFlag.val < 3954 → ∀ b : Fin 2,
      S_posRef.1 * slotBitProj wMom b = slotBitProj wMom b * S_posRef.1 := by
    intro wFlag wMom hVal hw1 hw2 b
    have hUout_comm : U_out.1 * slotBitProj wFlag b = slotBitProj wFlag b * U_out.1 := by
      dsimp only [U_out]
      rw [hFactorEq, uVepTwistCutRef_pf_congr (by decide : 22 ≤ 80) pos24_22_le_80]
      exact FullSysHoistedSelectStitch.mul_comm_of_comm
        (fullSysQftCoreUnitary_comm_slotBitProj (by decide : 6 ≤ 80) tierBQftFull
          (le_trans (by decide : 3924 ≤ 3948) hw1) hw2 b)
        (fastCutUVepTwistRef_comm_high_wire pos24_22_le_80 (truncFn cfg) wFlag hw1 b)
    have hPosFlag_comm : S_posFlag.1 * slotBitProj wFlag b = slotBitProj wFlag b * S_posFlag.1 :=
      unitaryConj_comm_proj U_out (posData.uPosPhase cfg) (slotBitProj wFlag b)
        (slotBitProj_self_adj wFlag b) hUout_comm
        (by rw [hPosDataEq cfg]; exact hPosCommSlot wFlag hw1 hw2 b)
    have hCast := congrArg (castNatOp hCoreEq) hPosFlag_comm
    simpa only [S_posRef, coreUnitaryFromFullSys, castNatOp_val_unitary, castNatOp_mul,
      castNatOp_slotBitProj hCoreEq wFlag wMom hVal b] using hCast
  have hS_posRef_comm_coin : ∀ c : Fin 8,
      S_posRef.1 * momCoinProj 80 c = momCoinProj 80 c * S_posRef.1 := fun c ↦ by
    have h0 := hS_posRef_comm_slot (iSlot0 80) (iSlot0Mom 80) rfl
      (by dsimp [iSlot0]; omega) (by dsimp [iSlot0]; omega) (coinBitFin2 c 0)
    have h1 := hS_posRef_comm_slot (iSlot1 80) (iSlot1Mom 80) rfl
      (by dsimp [iSlot1]; omega) (by dsimp [iSlot1]; omega) (coinBitFin2 c 1)
    have h2 := hS_posRef_comm_slot (iSlot2 80) (iSlot2Mom 80) rfl
      (by dsimp [iSlot2]; omega) (by dsimp [iSlot2]; omega) (coinBitFin2 c 2)
    unfold momCoinProj
    calc S_posRef.1 * (slotBitProj (iSlot0Mom 80) (coinBitFin2 c 0) *
            slotBitProj (iSlot1Mom 80) (coinBitFin2 c 1) *
            slotBitProj (iSlot2Mom 80) (coinBitFin2 c 2))
        = (S_posRef.1 * slotBitProj (iSlot0Mom 80) (coinBitFin2 c 0)) *
            slotBitProj (iSlot1Mom 80) (coinBitFin2 c 1) *
            slotBitProj (iSlot2Mom 80) (coinBitFin2 c 2) := by simp only [Matrix.mul_assoc]
      _ = slotBitProj (iSlot0Mom 80) (coinBitFin2 c 0) *
            (S_posRef.1 * slotBitProj (iSlot1Mom 80) (coinBitFin2 c 1)) *
            slotBitProj (iSlot2Mom 80) (coinBitFin2 c 2) := by
              rw [h0]; simp only [Matrix.mul_assoc]
      _ = slotBitProj (iSlot0Mom 80) (coinBitFin2 c 0) *
            slotBitProj (iSlot1Mom 80) (coinBitFin2 c 1) *
            (S_posRef.1 * slotBitProj (iSlot2Mom 80) (coinBitFin2 c 2)) := by
              rw [h1]; simp only [Matrix.mul_assoc]
      _ = (slotBitProj (iSlot0Mom 80) (coinBitFin2 c 0) *
            slotBitProj (iSlot1Mom 80) (coinBitFin2 c 1) *
            slotBitProj (iSlot2Mom 80) (coinBitFin2 c 2)) * S_posRef.1 := by
              rw [h2]; simp only [Matrix.mul_assoc]
  have hPosPres : ∀ (c : Fin 8), coinBitFin2 c 2 = 0 → coinBitFin2 c 1 = 0 →
      momCoinProj 80 c * (S_raw.1 * momCoinProj 80 c) = S_raw.1 * momCoinProj 80 c := by
    intro c h2 h1
    have hAbs := posCoin01ProjMom_mul_momCoinProj_01 c h1 h2
    rw [← hAbs, ← Matrix.mul_assoc S_raw.1, hS_pos_branch01, Matrix.mul_assoc S_posRef.1, hAbs,
      ← Matrix.mul_assoc, ← hS_posRef_comm_coin c, Matrix.mul_assoc, momCoinProj_80_idem]
  have hMomPres : ∀ (c : Fin 8) (hc : coinBitFin2 c 2 = 1) (U : Unitary (2 ^ momCoreWires 80)),
      (coreUnitaryFromFullSys (selOra.uMomPhase cfg)).1 * momCoinProj 80 c =
        U.1 * momCoinProj 80 c →
      U.1ᴴ = U.1 → U.1 * (1 - momCoinProj 80 c) = 1 - momCoinProj 80 c →
      momCoinProj 80 c * (S_raw.1 * momCoinProj 80 c) = S_raw.1 * momCoinProj 80 c := by
    intro c hc U hEq hSA hOff
    rw [(fullSysSelectEffUnitary_on_momCoin_sym qftCore selOra cfg c hc).trans hEq]
    exact preserves_proj_of_sa_and_offProj (momCoinProj_80_sa c) (momCoinProj_80_idem c) hSA hOff
  have hS_raw_pres : ∀ c : Fin 8,
      momCoinProj 80 c * (S_raw.1 * momCoinProj 80 c) = S_raw.1 * momCoinProj 80 c := fun c ↦ by
    fin_cases c
    · exact hPosPres 0 (by decide) (by decide)
    · exact hPosPres 1 (by decide) (by decide)
    · change momCoinProj 80 2 * (S_raw.1 * momCoinProj 80 2) = S_raw.1 * momCoinProj 80 2
      have hs0 : slotBitProj (iSlot2Mom 80) 0 * slotBitProj (iSlot1Mom 80) 1 *
          slotBitProj (iSlot0Mom 80) 0 = momCoinProj 80 2 := slackProj_eq_momCoinProj 80 0
      rw [← hs0, hSlack2_S, one_smul, hs0, momCoinProj_80_idem]
    · change momCoinProj 80 3 * (S_raw.1 * momCoinProj 80 3) = S_raw.1 * momCoinProj 80 3
      have hs1 : slotBitProj (iSlot2Mom 80) 0 * slotBitProj (iSlot1Mom 80) 1 *
          slotBitProj (iSlot0Mom 80) 1 = momCoinProj 80 3 := slackProj_eq_momCoinProj 80 1
      rw [← hs1, hSlack3_S, hs1, Matrix.mul_smul, momCoinProj_80_idem]
    · exact hMomPres 4 rfl _ hMomCoins.1 (s0.hSA cfg) (s0.hOffCoin cfg)
    · exact hMomPres 5 rfl _ hMomCoins.2.1 (s1.hSA cfg) (s1.hOffCoin cfg)
    · exact hMomPres 6 rfl _ hMomCoins.2.2.1 (s3.hSA cfg) (s3.hOffCoin cfg)
    · exact hMomPres 7 rfl _ hMomCoins.2.2.2 (s5.hSA cfg) (s5.hOffCoin cfg)
  have hOffDiag : ∀ c₁ c₂ : Fin 8, c₁ ≠ c₂ →
      let P₁ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₁)
      let P₂ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₂)
      P₁ * S_core.1 * P₂ = 0 := by
    intro c₁ c₂ hne P₁ P₂
    have hW1 := post_mul_ancProj_mem_coin post hSuppPost01 c₁
    have hW2 := post_mul_ancProj_mem_coin post hSuppPost01 c₂
    have hP1_sa : P₁ᴴ = P₁ := by
      dsimp only [P₁]
      rw [← embed_elemMat86_diag, ← QRegister.embedMatrix_conjTranspose, elemMat86_conjTranspose]
    have hW1_adj : (P₁ * W_post.1ᴴ) * momCoinProj 80 c₁ = P₁ * W_post.1ᴴ := by
      have h := congrArg (fun M ↦ Mᴴ) hW1
      simpa only [P₁, Matrix.conjTranspose_mul, momCoinProj_80_sa, hP1_sa,
        Matrix.mul_assoc] using h
    have hSR : S_raw.1 * (W_post.1 * P₂) =
        momCoinProj 80 c₂ * ((S_raw.1 * momCoinProj 80 c₂) * (W_post.1 * P₂)) := by
      calc S_raw.1 * (W_post.1 * P₂)
          = S_raw.1 * (momCoinProj 80 c₂ * (W_post.1 * P₂)) := by rw [hW2]
        _ = (S_raw.1 * momCoinProj 80 c₂) * (W_post.1 * P₂) := (Matrix.mul_assoc _ _ _).symm
        _ = (momCoinProj 80 c₂ * (S_raw.1 * momCoinProj 80 c₂)) * (W_post.1 * P₂) := by
              rw [hS_raw_pres c₂]
        _ = momCoinProj 80 c₂ * ((S_raw.1 * momCoinProj 80 c₂) * (W_post.1 * P₂)) :=
              Matrix.mul_assoc _ _ _
    dsimp only [S_core, W_post]
    rw [unitaryConj_val]
    calc P₁ * (W_post.1ᴴ * S_raw.1 * W_post.1) * P₂
        = (P₁ * W_post.1ᴴ) * (S_raw.1 * (W_post.1 * P₂)) := by simp only [Matrix.mul_assoc]
      _ = ((P₁ * W_post.1ᴴ) * momCoinProj 80 c₁) *
            (momCoinProj 80 c₂ * ((S_raw.1 * momCoinProj 80 c₂) * (W_post.1 * P₂))) := by
              rw [hW1_adj, hSR]
      _ = (P₁ * W_post.1ᴴ) * (momCoinProj 80 c₁ * momCoinProj 80 c₂) *
            ((S_raw.1 * momCoinProj 80 c₂) * (W_post.1 * P₂)) := by
              simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [FullSysMomSlots0135Concrete.momCoinProj_mul_of_ne 80 hne,
            Matrix.mul_zero, Matrix.zero_mul]
  exact ⟨hS_core_sa, hDiag, hOffDiag⟩

private theorem rawBEBlockCommutesFerm_Bhmt_of_core_blocks
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (truncFn : Configuration → Configuration)
    (qftCore : FullSysQft654Bundle)
    (prep : FullSysPrepareBundle 80)
    (post : PosPostPrepCert 80)
    (uCoin : Unitary (2 ^ 3))
    (hPrepEq : ∀ c, prep.uPrep c = zeroSubwireConstPrepUnitary post uCoin)
    (selOra : FullSysSelectOracleBundle 80 48)
    (s0 : MomSingleSlotOracle 80 48 0)
    (s1 : MomSingleSlotOracle 80 48 1)
    (s3 : MomSingleSlotOracle 80 48 3)
    (s5 : MomSingleSlotOracle 80 48 5)
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
    (hCoreBlocks :
      let S_core := unitaryConj (post.uPosPost * coreHadamardUnitary 80)
        (coreUnitaryFromFullSys (fullSysSelectEffUnitary qftCore selOra cfg))
      let B_coin := bCoinGenS1S3S5
        s0 s1 s3 s5 (fun c ↦ tierBB2ActMod4BhmtOf tM (truncFn c))
        (fun c ↦ tierBB4ActMod4BhmtOf tM (truncFn c)) cfg
      S_core.1ᴴ = S_core.1 ∧
        (∀ c : Fin 8,
          let P_c := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)
          P_c * S_core.1 * P_c = P_c * (coreSysSym 80).embedMatrix (B_coin c) * P_c) ∧
        (∀ c₁ c₂ : Fin 8, c₁ ≠ c₂ →
          let P₁ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₁)
          let P₂ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₂)
          P₁ * S_core.1 * P₂ = 0)) :
    RawBEBlockCommutesFerm spinUp (fullSysRawBEUnitary qftCore prep selOra cfg) := by
  rcases hCoreBlocks with ⟨_, hDiag, hOffDiag⟩
  unfold RawBEBlockCommutesFerm
  dsimp only
  let rSysBE : QRegister systemQubits (systemQubits + fullSysRawAncWires 80) :=
    QRegister.block 0 systemQubits (by dsimp [fullSysRawAncWires, systemQubits]; omega)
  let rAncBE : QRegister (fullSysRawAncWires 80) (systemQubits + fullSysRawAncWires 80) :=
    QRegister.block systemQubits (fullSysRawAncWires 80) le_rfl
  let G := SpecsAux.gridProjector
  let F := fermionicProjector spinUp
  let B_coin := bCoinGenS1S3S5
    s0 s1 s3 s5 (fun c ↦ tierBB2ActMod4BhmtOf tM (truncFn c))
    (fun c ↦ tierBB4ActMod4BhmtOf tM (truncFn c)) cfg
  let M_sum : Operator (2 ^ systemQubits) :=
    ∑ c : Fin 8, ((‖uCoin.1 c 0‖ ^ 2 : ℝ) : ℂ) • B_coin c
  have hDisj : rSysBE.DisjointWires rAncBE :=
    QRegister.block_disjoint_of_le 0 systemQubits systemQubits (fullSysRawAncWires 80)
      (by dsimp [fullSysRawAncWires, systemQubits]; omega) le_rfl (by omega)
  have hGF : G * F = F := SpecsAux.gridProjector_mul_fermionicProjector spinUp
  have hFG : F * G = F := fermionicProjector_mul_specsGridProjector spinUp
  have hCoinComm : ∀ c : Fin 8, Commute (G * B_coin c * G) F := fun c ↦ by
    match c with
    | ⟨0, _⟩ =>
      exact gridSandwich_comm_fermionicProjector_of_comm_pElMat spinUp _
        (tierBB2ActMod4BhmtOf_comm_pElMat tM (truncFn cfg))
    | ⟨1, _⟩ =>
      exact gridSandwich_comm_fermionicProjector_of_comm_pElMat spinUp _
        (tierBB4ActMod4BhmtOf_comm_pElMat tM (truncFn cfg))
    | ⟨2, _⟩ =>
      change (G * 1 * G) * F = F * (G * 1 * G)
      rw [Matrix.mul_one, Matrix.mul_assoc G G F, hGF, hGF, ← Matrix.mul_assoc F G G, hFG, hFG]
    | ⟨3, _⟩ =>
      change (G * (-1) * G) * F = F * (G * (-1) * G)
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one]
      rw [Matrix.mul_assoc G G F, hGF, hGF, ← Matrix.mul_assoc F G G, hFG, hFG]
    | ⟨4, _⟩ => exact momSingleSlotOracle_gridSandwich_comm_fermionicProjector s0 cfg spinUp
    | ⟨5, _⟩ => exact momSingleSlotOracle_gridSandwich_comm_fermionicProjector s1 cfg spinUp
    | ⟨6, _⟩ => exact momSingleSlotOracle_gridSandwich_comm_fermionicProjector s3 cfg spinUp
    | ⟨7, _⟩ => exact momSingleSlotOracle_gridSandwich_comm_fermionicProjector s5 cfg spinUp
    | ⟨n + 8, hn⟩ => exact absurd hn (by omega)
  have hSumComm : (G * M_sum * G) * F = F * (G * M_sum * G) := by
    have hDist : G * M_sum * G =
        ∑ c : Fin 8, ((‖uCoin.1 c 0‖ ^ 2 : ℝ) : ℂ) • (G * B_coin c * G) := by
      dsimp only [M_sum]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hDist, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, (hCoinComm c).eq]
  change (pgBE (fullSysRawAncWires 80) * (fullSysRawBEUnitary qftCore prep selOra cfg).1 *
      pgBE (fullSysRawAncWires 80)) * rSysBE.embedMatrix F =
    rSysBE.embedMatrix F * (pgBE (fullSysRawAncWires 80) *
      (fullSysRawBEUnitary qftCore prep selOra cfg).1 * pgBE (fullSysRawAncWires 80))
  rw [pgBE_mul_rawBE_mul_pgBE_eq_sum_coin qftCore prep post uCoin hPrepEq selOra cfg B_coin
    hDiag hOffDiag]
  exact embed_mul_outcomeProj_comm_of_comm rSysBE rAncBE hDisj (G * M_sum * G) F 0 hSumComm

/-- Exact fermionic top-block commutation (`RawBEBlockCommutesFerm`) for `pos80BhmtPostPrepCert`
and arbitrary `s1 : MomSingleSlotOracle 80 48 1` satisfying `SelectOraHypothesisOfS1Trunc`
plus coin-5 `uBarrelFast` invariance `hS1Conj`. -/
theorem step_rawBEBlockCommutesFerm_Bhmt_s1
    {t2Ctrl t2Cat B : ℕ}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (truncFn : Configuration → Configuration)
    (qftCore : FullSysQft654Bundle)
    (hqftFactor : tierBQftFull.uQft654 =
      qftCore.uQft654 * FusedPreDiagFromTwist288.uPre654)
    (prep : FullSysPrepareBundle 80)
    (uCoin : Unitary (2 ^ 3))
    (hPrepEq : ∀ c, prep.uPrep c = zeroSubwireConstPrepUnitary pos80BhmtPostPrepCert uCoin)
    (selOra : FullSysSelectOracleBundle 80 48)
    (s1 : MomSingleSlotOracle 80 48 1)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (hLeaf2Pos : leaf2.uPosPhase0 = uPosPhase80Mod4OfB B hB6 hB27)
    (s3 : MomSingleSlotOracle 80 48 3)
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1 leaf2 s3)
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
    (hS1Conj : ∀ c0,
      (HoistedSwapSelectBridge.unitaryConj
          (coreUnitaryFromFullSys (uBarrelFast (le_refl 80)))
          (s1.uSlotEff c0)).1 *
        momCoinProj 80 5 =
      (s1.uSlotEff c0).1 * momCoinProj 80 5) :
    RawBEBlockCommutesFerm spinUp (fullSysRawBEUnitary qftCore prep selOra cfg) := by
  let posData := posDataMod4OfB B hB6 hB27
  let tM := MidKickSub33.pos24TailMag30MidpointB B
    (b_one_le_of_six_le hB6) (b_le_29_of_le_27 hB27)
  have hBlocks := step_select_core_blocks_of_oraHypS1 qftCore hqftFactor
    pos80BhmtPostPrepCert pos80Bhmt_hSuppPost01
    selOra s1 leaf2 posData
    (fun _ ↦ hLeaf2Pos.symm)
    (fun wFlag hw1' hw2' b ↦ by
      rw [hLeaf2Pos]
      exact uPosPhase80Mod4OfB_comm_slotBitProj B hB6 hB27 wFlag hw1' hw2' b)
    s3 hOra hS1Conj
    (fun c ↦ tierBB2ActMod4BhmtOf tM (truncFn c))
    (fun c ↦ tierBB4ActMod4BhmtOf tM (truncFn c))
    (topCoinPropGen_comp_truncCfg_of_posPhase_param pos80BhmtPostPrepCert posData
      (fun _ ↦ rfl) (uVepTwistCutRef (by decide : 22 ≤ 80)) truncFn 0
      (tierBB2ActMod4BhmtOf tM)
      (fun c0 ↦ fastCutMergedVepTopCoin0_80_Bhmt_mod4_midpoint B
        (b_one_le_of_six_le hB6) (b_le_29_of_le_27 hB27) posData c0 rfl))
    (topCoinPropGen_comp_truncCfg_of_posPhase_param pos80BhmtPostPrepCert posData
      (fun _ ↦ rfl) (uVepTwistCutRef (by decide : 22 ≤ 80)) truncFn 1
      (tierBB4ActMod4BhmtOf tM)
      (fun c0 ↦ fastCutMergedVepTopCoin1_80_Bhmt_mod4_midpoint B
        (b_one_le_of_six_le hB6) (b_le_29_of_le_27 hB27) posData c0 rfl))
    cfg
  exact rawBEBlockCommutesFerm_Bhmt_of_core_blocks tM truncFn qftCore prep pos80BhmtPostPrepCert
    uCoin hPrepEq selOra (slot0ElectronKineticOracleSym (le_refl 80)) s1
    s3 (zeroMomSlotOracle5 80 48) cfg spinUp hBlocks

/-- Zero-extra-hypothesis `ora1Pwu24OfBSub` specialization of `step_rawBEBlockCommutesFerm_Bhmt_s1`
(auto-discharging `hS1Conj` via `ora1Pwu24OfBSub_uBarrelFast_conj_on_coin5` and inferring
`{bSub, hbLo, hbHi}` directly from `hOra`). -/
theorem step_rawBEBlockCommutesFerm_Bhmt_pwu24
    {t2Ctrl t2Cat B bSub : ℕ} {hbLo : 18 ≤ bSub} {hbHi : bSub ≤ 24}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (truncFn : Configuration → Configuration)
    (qftCore : FullSysQft654Bundle)
    (hqftFactor : tierBQftFull.uQft654 =
      qftCore.uQft654 * FusedPreDiagFromTwist288.uPre654)
    (prep : FullSysPrepareBundle 80)
    (uCoin : Unitary (2 ^ 3))
    (hPrepEq : ∀ c, prep.uPrep c = zeroSubwireConstPrepUnitary pos80BhmtPostPrepCert uCoin)
    (selOra : FullSysSelectOracleBundle 80 48)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (hLeaf2Pos : leaf2.uPosPhase0 = uPosPhase80Mod4OfB B hB6 hB27)
    (s3 : MomSingleSlotOracle 80 48 3)
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra
      (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) leaf2 s3)
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons)) :
    RawBEBlockCommutesFerm spinUp (fullSysRawBEUnitary qftCore prep selOra cfg) :=
  step_rawBEBlockCommutesFerm_Bhmt_s1 hB6 hB27 truncFn qftCore hqftFactor
    prep uCoin hPrepEq selOra (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80))
    leaf2 hLeaf2Pos s3 hOra cfg spinUp
    (ora1Pwu24OfBSub_uBarrelFast_conj_on_coin5 bSub hbLo hbHi)
end


end ConfigBhmtBlockComm

end BhmtBlockComm

namespace BhmtBlockCommAux
export BhmtBlockComm
  (tierBB2ActMod4BhmtOf_comm_pElMat tierBB4ActMod4BhmtOf_comm_pElMat
  ora1Pwu24OfBSub_uBarrelFast_conj_on_coin5 step_rawBEBlockCommutesFerm_Bhmt_s1
  step_rawBEBlockCommutesFerm_Bhmt_pwu24)
end BhmtBlockCommAux


end PartBhmtBlockComm

-- ============================================================================
-- Part: ParetoSelectStitch
-- ============================================================================


namespace ParetoSelectStitch

section ConfigParetoSelectStitch

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
local instance (priority := 1000000) parInstNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 512
set_option exponentiation.threshold 5000

local instance (priority := 1000000) instNeZeroTwoPow_Stitch (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
  (sixChannelRaw sixChannelShifted)
open SpecsAux.FullScaleBESector
  (IsQubitizedBlockEncodingUnitary AgreesOnFermionicSector)
-- Root solution namespace already active.
open PosMomSelectSandwich (slotBitProj)
open PosMomSelectDynamic
  (unitaryConj unitaryConj_val embedMatrix_comm_diagonal_of_outside)
open TwosCompAndWire0Cancel
  (smToTwosSysUnitary smToTwosSysUnitary_conjTranspose)
open SingleRBEGridGuardWalk (ghostZeroedBE)
open SixSlotEndpointJunctionBridge (gridValidBool)
open FullSysPrepare6Slot (coinSelOutcome)
open FullSysCatSegmentBridge
  (FullSysQft654Bundle FullSysPrepareBundle FullSysSelectOracleBundle
   fullSysCoreWires fullSysRawAncWires coreElecCosetB1Block
   iSlot0 iSlot1 iSlot2 fullSysQftCoreUnitary fullSysSelectPosUnitary
   fullSysSelectEffUnitary fullSysRawBEUnitary
   fullSysSelectEffUnitary_conjTranspose_and_split
   fullSysQftCoreUnitary_comm_slotBitProj wire_not_mem_coreElecCosetB1
   fullSysSelectEffUnitary_on_slackCoin)
open FullSysFullPrepareAndTopConcrete
  (coreSysSym coreAncSym selCoin3Sym coreHadamardUnitary unitaryConj_mul_outer)
open FullSysMomSlots0135Concrete
  (momCoreWires iSlot0Mom iSlot1Mom iSlot2Mom momCoinProj MomSingleSlotOracle
   slotBitProj_self_adj slotBitProj_mul_idem coinBitFin2
   conjHadamard_branch_topBlock_of_eq_on_coin)
open MomSlot0CircuitHalf (slot0ElectronKineticOracleSym)
open MomSlot1DyadicTopAdapter
  (zeroSubwireEpsSlotOfEps2S1 zeroSubwireEpsSlotS1_sum_le_of_bounds)
open OraAndPrepBundle
  (PosPostPrepCert coreUnitaryFromFullSys posCoin01Proj posCoin01ProjMom
   momCoreWires_eq_fullSysCoreWires castNatOp castNatOp_val_unitary castNatOp_conjTranspose
   castNatOp_mul castNatOp_smul castNatOp_slotBitProj
   coreAncSym_eq_momAncReg_sym selCoin3Sym_eq_momCoin3Sel_sym
   coreSysSym_eq_momSysReg_sym coreHadamardUnitary_eq_mom_sym
   fullSysSelectEffUnitary_on_momCoin_sym
   postPrep_comm_posCoin01ProjMom postPrep_pos01_branch_eq postPrep_nonPos_topBlock
   coreHadamard_conj_slack_block_gen slackProj_eq_momCoinProj
   fin6Tuple fin6Tuple_0 fin6Tuple_1 fin6Tuple_2 fin6Tuple_3 fin6Tuple_4 fin6Tuple_5)
open SingleCatClosure (SingleCatSelectImpl)
open GeneralBetaAndAlphaTopEndpoint
  (zeroMomSlotOracle5 fullSysSelectPosUnitary_eq_on_posCoin01_out)
open TierClosure
  (mkSlot0LocalDataOfBarrelFast liftSlot3OfBarrelFast)
open TierBClean80Closure
  (tierBQftFull tierBBarrel80 tierBBarrel80_onP01 tierBL5Zero80)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open PosSlots24TopWrapper (PosSlots24DataGen)
open PosSlots24SemanticBridge (pos24_22_le_80)
open PosSlots24SemanticOracleConcrete80
  (pos80Slot2Scale pos80Slot4Scale)
open MergedVepTopCoinCollapse (topCoinPropGen)
open Pos24MergedVepPrepAndStitch
  (mergedPosSlot2WeightGen mergedPosSlot2Shift)
open Pos24Slot2FermionicBridge (pos24Slot2E2Const)
open Pos24Slot4FermionicBridge (pos80Slot4EShiftFn)
open PosSlots24Q30Tight (eps4_q30_tight)
open ZeroSubwireCoinPrep80 (wIdealRat)
open ZeroSubwireGridPert80
  (elemMat86_conjTranspose embed_elemMat86_diag momCoinProj_80_idem
   momCoinProj_80_sa post_mul_ancProj_mem_coin preserves_proj_of_sa_and_offProj
   posCoin01ProjMom_mul_momCoinProj_01 unitaryConj_comm_proj
   target_slot_agrees_unquantized_sym)
open ZeroSubwireHarmonicGridPert
  (zeroSubwireConstPrepUnitary wActOfUnitary forall_fin6_prop)
open JunctionProj3DCutPos24BridgeGen
  (uVepTwistCutRef fastCutUVepTwistRef uVepTwistCutRef_pf_congr
   fastCutUVepTwistRef_comm_high_wire uVepTwistCutRef_comm_slot2 uVepTwistCutRef_comm_slot1)
open PosS3Bounds (tierBB2IdMod4 tierBB4IdMod4)
open PosMod4FermionicBounds
  (tierBB2IdMod4_isHermitian tierBB4IdMod4_isHermitian
   tierBB2IdMod4_norm_le_one tierBB4IdMod4_norm_le_one
   tierBB4IdMod4_trunc_agreesOnFermionicSector_q30Tight)
open Leaf2PosMod4WidthCore
  (b_one_le_of_six_le b_le_29_of_le_27 uPosPhase80Mod4OfB posDataMod4OfB)
open Leaf2Packed18Mux2DCore
  (uPosPhase80Mod4OfB_comm_slotBitProj)
open MomAdapterGen (topCoinPropGen_comp_truncCfg_of_posPhase_param)
open SelectStitch (Leaf2SpecOfTrunc)
open MidKickSub33 (pos24TailMag30MidpointB)
open TopClosureAux (slot0ElectronKineticOracleSym_80_epsIntr)
open Slot3Norm1s36_161w (Norm1sTier)
open GqspSlot3UltraBkAnd8TierCert
  (IsCertifiedNorm1sTier6 s3EpsUltraBkNano s3Swap3OracleNorm1sUltraBk
   s3Swap3OracleNorm1sUltraBk_wSlot s3Swap3OracleNorm1sUltraBk_epsIntr_le)
open Leaf4Ext48TopStitch (HoistedExtHkSelectSpec)
open GqspCleanCoinAndGuardBridge
  (bCoinGenS1S3S5 Coin3CleanProgSpecOfWeights GenBetaExtHkSelAndPertSpec
    selOra_uCoin_gridPerturbation_arbitraryWeights_of_core_blocks nonS3ChiralChiralNano
    mkZeroSubwireWeights80_eq_of_wSlot3)
open ConstructiveAlpha124052Bundle
  (prepBundleOfPostCertAndCoin prepBundleOfPostCertAndCoin_uPrep_eq_gen
   prepBundleOfPostCertAndCoin_hmPrep hqftFactor_coreQftPruned128)
open Pos512FastPrepAndCoin
  (truncChiralPos512OfW nonS3ChiralPos512Nano)
open PosPostBhmtPrep
open Slot1Pwu24
  (eps1Pwu24Num ora1Pwu24OfBSub ora1Pwu24OfBSub_epsIntr_le
   mkSlot1Pwu24FastDataOfBarrel SelectOraHypothesisOfS1Trunc
   step_uTwist_comm_slotBitProj_s1 step_hTwist_s2_s1 step_hTwist_s1_s1 step_hTwist_s0_s1)

-- ============================================================================
-- Section 1: Parametric `Slot 1` (`s1`) Shifted 6-Channel Target Split
-- ============================================================================

/-- Parametric `s1` counterpart of `Pos24MergedVepPrepAndStitch.mergedSplitShiftVec`, placing
`s1.eShift cfg` at channel `1` instead of hardcoding `slot1ProjKineticOracleSym`. -/
noncomputable def mergedSplitShiftVecS1 {mPayload : ℕ} (hm80 : 80 ≤ mPayload)
    (s1 : MomSingleSlotOracle mPayload 48 1)
    (e2 : Configuration → ℝ)
    (s3 : MomSingleSlotOracle mPayload 48 3)
    (e4 : Configuration → ℝ)
    (cfg : Configuration) : Fin 6 → ℝ :=
  fin6Tuple
    ((slot0ElectronKineticOracleSym hm80).eShift cfg)
    (s1.eShift cfg)
    (e2 cfg)
    (s3.eShift cfg)
    (e4 cfg)
    (e2 cfg / 108)

/-- Parametric `s1` counterpart of `Pos24MergedVepPrepAndStitch.mergedPosTarget`. -/
noncomputable def mergedPosTargetS1 {mPayload : ℕ} (hm80 : 80 ≤ mPayload)
    (s1 : MomSingleSlotOracle mPayload 48 1)
    (e2 : Configuration → ℝ)
    (s3 : MomSingleSlotOracle mPayload 48 3)
    (e4 : Configuration → ℝ)
    (cfg : Configuration) : Fin 6 → Operator (2 ^ systemQubits) :=
  let E_sp := mergedSplitShiftVecS1 hm80 s1 e2 s3 e4 cfg
  fin6Tuple
    (sixChannelShifted cfg E_sp 0)
    (sixChannelShifted cfg E_sp 1)
    (sixChannelShifted cfg E_sp 2 + sixChannelShifted cfg E_sp 5)
    (sixChannelShifted cfg E_sp 3)
    (sixChannelShifted cfg E_sp 4)
    0

/-- Sum identity for `mergedPosTargetS1` with arbitrary `s1.eShift cfg` at channel `1`. -/
private theorem mergedPosTargetS1_sum_eq {mPayload : ℕ} (hm80 : 80 ≤ mPayload)
    (s1 : MomSingleSlotOracle mPayload 48 1)
    (e2 : Configuration → ℝ)
    (s3 : MomSingleSlotOracle mPayload 48 3)
    (e4 : Configuration → ℝ)
    (cfg : Configuration) :
    let E_vec : Fin 6 → ℝ :=
      fin6Tuple
        ((slot0ElectronKineticOracleSym hm80).eShift cfg)
        (s1.eShift cfg)
        (mergedPosSlot2Shift e2 cfg)
        (s3.eShift cfg)
        (e4 cfg)
        ((zeroMomSlotOracle5 mPayload 48).eShift cfg)
    (∑ k : Fin 6, mergedPosTargetS1 hm80 s1 e2 s3 e4 cfg k) =
      ∑ k : Fin 6, sixChannelShifted cfg E_vec k := by
  intro E_vec
  have h25 :
      sixChannelShifted cfg (mergedSplitShiftVecS1 hm80 s1 e2 s3 e4 cfg) 2 +
          sixChannelShifted cfg (mergedSplitShiftVecS1 hm80 s1 e2 s3 e4 cfg) 5 =
        sixChannelShifted cfg E_vec 2 + sixChannelShifted cfg E_vec 5 := by
    dsimp only [E_vec, sixChannelShifted, mergedSplitShiftVecS1, mergedPosSlot2Shift,
      zeroMomSlotOracle5, fin6Tuple]
    have hsc :
        ((e2 cfg : ℂ) • SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector) +
          (((e2 cfg / 108 : ℝ) : ℂ) •
            SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector) =
        (((109 / 108 * e2 cfg : ℝ) : ℂ) •
          SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector) +
          (((0 : ℝ) : ℂ) •
            SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector) := by
      rw [← add_smul, ← add_smul]
      congr 1
      push_cast
      ring
    calc (sixChannelRaw cfg 2 - (e2 cfg : ℂ) • _) +
      (sixChannelRaw cfg 5 - ((e2 cfg / 108 : ℝ) : ℂ) • _)
        = (sixChannelRaw cfg 2 + sixChannelRaw cfg 5) -
            (((e2 cfg : ℂ) • _) + (((e2 cfg / 108 : ℝ) : ℂ) • _)) := by abel
      _ = (sixChannelRaw cfg 2 + sixChannelRaw cfg 5) -
            ((((109 / 108 * e2 cfg : ℝ) : ℂ) • _) + (((0 : ℝ) : ℂ) • _)) := by rw [hsc]
      _ = (sixChannelRaw cfg 2 - ((109 / 108 * e2 cfg : ℝ) : ℂ) • _) +
            (sixChannelRaw cfg 5 - ((0 : ℝ) : ℂ) • _) := by abel
  rw [Fin.sum_univ_six, Fin.sum_univ_six]
  have h0 : mergedPosTargetS1 hm80 s1 e2 s3 e4 cfg 0 = sixChannelShifted cfg E_vec 0 := rfl
  have h1 : mergedPosTargetS1 hm80 s1 e2 s3 e4 cfg 1 = sixChannelShifted cfg E_vec 1 := rfl
  have h2 : mergedPosTargetS1 hm80 s1 e2 s3 e4 cfg 2 =
      sixChannelShifted cfg E_vec 2 + sixChannelShifted cfg E_vec 5 := h25
  have h3 : mergedPosTargetS1 hm80 s1 e2 s3 e4 cfg 3 = sixChannelShifted cfg E_vec 3 := rfl
  have h4 : mergedPosTargetS1 hm80 s1 e2 s3 e4 cfg 4 = sixChannelShifted cfg E_vec 4 := rfl
  have h5 : mergedPosTargetS1 hm80 s1 e2 s3 e4 cfg 5 = 0 := rfl
  rw [h0, h1, h2, h3, h4, h5]
  abel

-- ============================================================================
-- Section 2: `SelectOraHypothesisOfS1Trunc` Core Blocks on `ora1Pwu24OfBSub`
-- ============================================================================

-- Elaborator-only threshold for concrete 4034-wire `FullSysSelectOracleBundle 80 48`
-- (`fullSysCoreWires 80 = 4034`, zero `QRegister` WHNF); reset to 256 at L1220 before `QRegister`
-- defs.

/-- Parametric `(eps2OfW, nonS3Nano)` 6-slot intrinsic error bound when replacing
`slot1Dyadic459Oracle` (`29,000 nHa`) with `ora1Pwu24OfBSub bSub` (`eps1Pwu24Num bSub nHa`). -/
private theorem zeroSubwireEpsSlotS1_pwu24_sum_le_of_eps2_and_nonS3
    (eps2OfW : ℕ → ℝ) (nonS3Nano : ℕ → ℕ)
    (hNonS3 : ∀ W, 28 ≤ W → W ≤ 36 →
      (6 : ℝ) / 10 ^ 7 + (109 / 108 : ℝ) * eps2OfW W + eps4_q30_tight ≤
        ((nonS3Nano W - 29000 : ℕ) : ℝ) / 1000000000)
    (W : ℕ) (hW28 : 28 ≤ W) (hW36 : W ≤ 36)
    (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (s3 : MomSingleSlotOracle 80 48 3) {e3 : ℝ} (hs3Eps : s3.epsIntr ≤ e3) :
    (∑ k : Fin 6, zeroSubwireEpsSlotOfEps2S1 (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) s3
      (eps2OfW W) eps4_q30_tight k) ≤
      (((nonS3Nano W - 29000) + eps1Pwu24Num bSub : ℕ) : ℝ) / 1000000000 + e3 := by
  refine zeroSubwireEpsSlotS1_sum_le_of_bounds
    (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80))
    (ora1Pwu24OfBSub_epsIntr_le bSub hbLo hbHi (le_refl 80))
    s3 hs3Eps le_rfl le_rfl ?_
  rw [slot0ElectronKineticOracleSym_80_epsIntr]
  have hN := hNonS3 W hW28 hW36
  push_cast
  linarith

/-- Fully parametric `(truncOfW, eps2OfW, nonS3Nano, wTarget)` grid-perturbation closure for
`pos80BhmtPostPrepCert` (`1,130 T`) + `ora1Pwu24OfBSub` (`4 * (bSub + 51)` `T`), supporting
arbitrary Slot-2 truncation (`G5` dipole cap) AND arbitrary Slot-3/5 weights (`G7/G8` `wTarget 5 =
0`). -/
theorem selOra_uCoin_gridPerturbation_genSlot2_Bhmt_pwu24_of
    (truncOfW : ℕ → Configuration → Configuration)
    (eps2OfW : ℕ → ℝ)
    (hSlot2Agrees : ∀ (W : ℕ) (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
      (E_sp : Fin 6 → ℝ), E_sp 2 = pos24Slot2E2Const →
      E_sp 5 = pos24Slot2E2Const / 108 →
      AgreesOnFermionicSector spinUp
        (gridProjector *
          ((mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg : ℂ) •
            (smToTwosSysUnitary.1 *
              tierBB2IdMod4 (truncOfW W cfg) *
              smToTwosSysUnitary.1)) *
          gridProjector)
        (sixChannelShifted cfg E_sp 2 + sixChannelShifted cfg E_sp 5)
        ((109 / 108 : ℝ) * eps2OfW W))
    (nonS3Nano : ℕ → ℕ)
    (hNonS3 : ∀ W, 28 ≤ W → W ≤ 36 →
      (6 : ℝ) / 10 ^ 7 + (109 / 108 : ℝ) * eps2OfW W + eps4_q30_tight ≤
        ((nonS3Nano W - 29000 : ℕ) : ℝ) / 1000000000)
    {α_real : ℝ} {t2Ctrl t2Cat coinNano B W bSub s3EpsNano capNano : ℕ}
    (hαPos : 0 < α_real) (hCoinLe : coinNano ≤ 300000)
    (hB : B = 22 ∨ B = 23 ∨ B = 24 ∨ B = 25 ∨ B = 26 ∨ B = 27)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (hW28 : 28 ≤ W) (hW36 : W ≤ 36)
    (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (wTarget : Fin 6 → ℝ)
    (hw0 : wTarget 0 = wIdealRat 0) (hw1 : wTarget 1 = wIdealRat 1)
    (hw2 : wTarget 2 = wIdealRat 2) (hw4 : wTarget 4 = wIdealRat 4)
    (hw5 : wTarget 5 = 0)
    (qftCore : FullSysQft654Bundle)
    (hqftFactor : tierBQftFull.uQft654 =
      qftCore.uQft654 * FusedPreDiagFromTwist288.uPre654)
    (prep : FullSysPrepareBundle 80) (uCoin : Unitary (2 ^ 3))
    (hPrepEq : ∀ c, prep.uPrep c = zeroSubwireConstPrepUnitary pos80BhmtPostPrepCert uCoin)
    (hWeightErr :
      ∑ k : Fin 6, |wActOfUnitary α_real uCoin k - wTarget k| ≤
        (coinNano : ℝ) / 1000000000)
    (selOra : FullSysSelectOracleBundle 80 48)
    (leaf2 : Leaf2SpecOfTrunc (truncOfW W) t2Ctrl t2Cat)
    (hLeaf2Pos : leaf2.uPosPhase0 = uPosPhase80Mod4OfB B hB6 hB27)
    (s3 : MomSingleSlotOracle 80 48 3)
    (hs3Eps : s3.epsIntr ≤ (s3EpsNano : ℝ) / 1000000000)
    (hs3W : ∀ cfg, s3.wSlot cfg = wTarget 3)
    (hOra : SelectOraHypothesisOfS1Trunc (truncOfW W) selOra
      (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) leaf2 s3)
    (hCap : coinNano + deltaPosBhmtExactNatOfB B +
      (nonS3Nano W - 29000) + eps1Pwu24Num bSub + s3EpsNano ≤ capNano)
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ∃ (E₀ δ_prep ε_id : ℝ) (Heff_act Heff_id : Operator (2 ^ systemQubits)),
      δ_prep + ε_id ≤ (capNano : ℝ) / 1000000000 ∧
      Commute (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits))) gridProjector ∧
      IsQubitizedBlockEncodingUnitary α_real
        (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))
        (ghostZeroedBE systemQubits (fullSysRawAncWires 80)
          (by dsimp [fullSysRawAncWires]; omega) gridValidBool
          (fullSysRawBEUnitary qftCore prep selOra cfg)) ∧
      Heff_id.IsHermitian ∧
      Commute Heff_id gridProjector ∧
      ‖gridProjector * (Heff_act - Heff_id) * gridProjector‖ ≤ δ_prep ∧
      AgreesOnFermionicSector spinUp Heff_id
        (smToTwosSysUnitary.1 * hamiltonian cfg * smToTwosSysUnitary.1ᴴ) ε_id := by
  have hCoinR : (coinNano : ℝ) / 1000000000 ≤ (300000 : ℝ) / 1000000000 := by
    have hle : (coinNano : ℝ) ≤ 300000 := by exact_mod_cast hCoinLe
    linarith only [hle]
  let posData := posDataMod4OfB B hB6 hB27
  let tM := pos24TailMag30MidpointB B (b_one_le_of_six_le hB6) (b_le_29_of_le_27 hB27)
  let s0 := slot0ElectronKineticOracleSym (le_refl 80)
  let s1 := ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)
  let s5 := zeroMomSlotOracle5 80 48
  have hBlocks := BhmtBlockComm.step_select_core_blocks_of_oraHypS1
    qftCore hqftFactor pos80BhmtPostPrepCert pos80Bhmt_hSuppPost01 selOra s1 leaf2 posData
    (fun _ ↦ hLeaf2Pos.symm)
    (fun wFlag hw1' hw2' b ↦ by
      rw [hLeaf2Pos]
      exact uPosPhase80Mod4OfB_comm_slotBitProj B hB6 hB27 wFlag hw1' hw2' b)
    s3 hOra
    (BhmtBlockComm.ora1Pwu24OfBSub_uBarrelFast_conj_on_coin5 bSub hbLo hbHi)
    (fun c ↦ tierBB2ActMod4BhmtOf tM (truncOfW W c))
    (fun c ↦ tierBB4ActMod4BhmtOf tM (truncOfW W c))
    (topCoinPropGen_comp_truncCfg_of_posPhase_param pos80BhmtPostPrepCert posData
      (fun _ ↦ rfl) (uVepTwistCutRef (by decide : 22 ≤ 80)) (truncOfW W) 0
      (tierBB2ActMod4BhmtOf tM)
      (fun c0 ↦ fastCutMergedVepTopCoin0_80_Bhmt_mod4_midpoint B
        (b_one_le_of_six_le hB6) (b_le_29_of_le_27 hB27) posData c0 rfl))
    (topCoinPropGen_comp_truncCfg_of_posPhase_param pos80BhmtPostPrepCert posData
      (fun _ ↦ rfl) (uVepTwistCutRef (by decide : 22 ≤ 80)) (truncOfW W) 1
      (tierBB4ActMod4BhmtOf tM)
      (fun c0 ↦ fastCutMergedVepTopCoin1_80_Bhmt_mod4_midpoint B
        (b_one_le_of_six_le hB6) (b_le_29_of_le_27 hB27) posData c0 rfl))
    cfg
  have hWId : ∀ k : Fin 6,
      ZeroSubwireHarmonicGridPert.mkZeroSubwireWeights80 s3 cfg k = wTarget k :=
    mkZeroSubwireWeights80_eq_of_wSlot3 s3 hw0 hw1 hw2 hs3W hw4 hw5 cfg
  have hw2_eq : wTarget 2 =
      mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg :=
    (hWId 2).symm
  have hw4_eq : wTarget 4 = pos80Slot4Scale := (hWId 4).symm
  let E_sp := mergedSplitShiftVecS1 (le_refl 80) s1 (fun _ ↦ pos24Slot2E2Const) s3
    pos80Slot4EShiftFn cfg
  let target := mergedPosTargetS1 (le_refl 80) s1 (fun _ ↦ pos24Slot2E2Const) s3
    pos80Slot4EShiftFn cfg
  let ε_slot := zeroSubwireEpsSlotOfEps2S1 s1 s3 (eps2OfW W) eps4_q30_tight
  have hSlotsSm : ∀ k : Fin 6,
      let B_unit_id : Fin 6 → Operator (2 ^ systemQubits) :=
        fin6Tuple (s0.bUnitTwos cfg) (s1.bUnitTwos cfg)
          (tierBB2IdMod4 (truncOfW W cfg)) (s3.bUnitTwos cfg)
          (tierBB4IdMod4 (truncOfW W cfg)) (s5.bUnitTwos cfg)
      AgreesOnFermionicSector spinUp
        (gridProjector *
          (smToTwosSysUnitary.1 * ((wTarget k : ℂ) • B_unit_id k) * smToTwosSysUnitary.1) *
          gridProjector)
        (target k) (ε_slot k) := by
    refine forall_fin6_prop ?_ ?_ ?_ ?_ ?_ ?_
    · have hEq : sixChannelShifted cfg E_sp 0 =
          sixChannelShifted cfg (fun q : Fin 6 ↦ if q = 0 then s0.eShift cfg else 0) 0 := rfl
      dsimp only [target, mergedPosTargetS1, ε_slot, zeroSubwireEpsSlotOfEps2S1]
      rw [← hWId 0, fin6Tuple_0, hEq]
      exact target_slot_agrees_unquantized_sym (s0.wSlot cfg) spinUp (s0.bUnitTwos cfg) _
        (s0.hPermSm cfg) (s0.hErrIntrSm cfg spinUp)
    · have hEq : sixChannelShifted cfg E_sp 1 =
          sixChannelShifted cfg (fun q : Fin 6 ↦ if q = 1 then s1.eShift cfg else 0) 1 := rfl
      have hs1W : s1.wSlot cfg =
          ZeroSubwireHarmonicGridPert.mkZeroSubwireWeights80 s3 cfg 1 := rfl
      dsimp only [target, mergedPosTargetS1, ε_slot, zeroSubwireEpsSlotOfEps2S1]
      rw [← hWId 1, ← hs1W, fin6Tuple_1, hEq]
      exact target_slot_agrees_unquantized_sym (s1.wSlot cfg) spinUp (s1.bUnitTwos cfg) _
        (s1.hPermSm cfg) (s1.hErrIntrSm cfg spinUp)
    · dsimp only [target, mergedPosTargetS1, ε_slot, zeroSubwireEpsSlotOfEps2S1]
      rw [hw2_eq, fin6Tuple_2, Matrix.mul_smul, Matrix.smul_mul]
      exact hSlot2Agrees W cfg spinUp E_sp rfl rfl
    · have hEq : sixChannelShifted cfg E_sp 3 =
          sixChannelShifted cfg (fun q : Fin 6 ↦ if q = 3 then s3.eShift cfg else 0) 3 := rfl
      dsimp only [target, mergedPosTargetS1, ε_slot, zeroSubwireEpsSlotOfEps2S1]
      rw [← hs3W cfg, fin6Tuple_3, hEq]
      exact target_slot_agrees_unquantized_sym (s3.wSlot cfg) spinUp (s3.bUnitTwos cfg) _
        (s3.hPermSm cfg) (s3.hErrIntrSm cfg spinUp)
    · have hEq : sixChannelShifted cfg E_sp 4 =
          sixChannelShifted cfg
            (fun q : Fin 6 ↦ if q = 4 then pos80Slot4EShiftFn cfg else 0) 4 := rfl
      dsimp only [target, mergedPosTargetS1, ε_slot, zeroSubwireEpsSlotOfEps2S1]
      rw [hw4_eq, fin6Tuple_4, hEq, Matrix.mul_smul, Matrix.smul_mul]
      exact tierBB4IdMod4_trunc_agreesOnFermionicSector_q30Tight
        (truncOfW W) cfg spinUp
    · dsimp only [target, mergedPosTargetS1, ε_slot, zeroSubwireEpsSlotOfEps2S1]
      rw [hw5, fin6Tuple_5, Complex.ofReal_zero, zero_smul,
        Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul]
      exact ⟨by simp, by simp⟩
  let E_vec : Fin 6 → ℝ :=
    fin6Tuple (s0.eShift cfg) (s1.eShift cfg)
      (mergedPosSlot2Shift (fun _ ↦ pos24Slot2E2Const) cfg)
      (s3.eShift cfg) (pos80Slot4EShiftFn cfg) (s5.eShift cfg)
  let nonS3PwuNano : ℕ := (nonS3Nano W - 29000) + eps1Pwu24Num bSub
  have hCapR : ((coinNano : ℝ) + (deltaPosBhmtExactNatOfB B : ℝ) +
      (nonS3PwuNano : ℝ) + (s3EpsNano : ℝ)) ≤ (capNano : ℝ) := by
    have hCapNat : coinNano + deltaPosBhmtExactNatOfB B + nonS3PwuNano + s3EpsNano ≤ capNano := by
      dsimp only [nonS3PwuNano]; omega
    have h1 : (((coinNano + deltaPosBhmtExactNatOfB B + nonS3PwuNano + s3EpsNano : ℕ) : ℝ)) ≤
        (capNano : ℝ) := Nat.cast_le.mpr hCapNat
    push_cast at h1
    linarith
  obtain ⟨E₀, δ_prep₀, ε_id₀, Heff_act, Heff_id, _, _, hSum, hCommAct, hBE,
      hHermId, hCommId, hDiff, hAgree⟩ :=
    selOra_uCoin_gridPerturbation_arbitraryWeights_of_core_blocks
      (err_w := (coinNano : ℝ) / 1000000000)
      (δ_pos := (deltaPosBhmtExactNatOfB B : ℝ) / (10 : ℝ) ^ 9)
      (ε_id := (nonS3PwuNano : ℝ) / 1000000000 + (s3EpsNano : ℝ) / 1000000000)
      (ε_BE := (capNano : ℝ) / 1000000000)
      hαPos
      (div_nonneg (Nat.cast_nonneg coinNano) (by norm_num))
      (div_nonneg (Nat.cast_nonneg (deltaPosBhmtExactNatOfB B)) (by norm_num))
      (add_nonneg (div_nonneg (Nat.cast_nonneg nonS3PwuNano) (by norm_num))
        (div_nonneg (Nat.cast_nonneg s3EpsNano) (by norm_num)))
      wTarget qftCore prep pos80BhmtPostPrepCert uCoin hPrepEq hWeightErr
      (by rw [hw2_eq, hw4_eq]; exact posPostBhmt_prepCap_le_exact_le300000 B hB hCoinR cfg)
      selOra s0 s1 s3 s5
      (fun c ↦ tierBB2ActMod4BhmtOf tM (truncOfW W c))
      (fun c ↦ tierBB4ActMod4BhmtOf tM (truncOfW W c))
      (fun c ↦ tierBB2IdMod4 (truncOfW W c))
      (fun c ↦ tierBB4IdMod4 (truncOfW W c))
      cfg spinUp E_vec target ε_slot
      (mergedPosTargetS1_sum_eq (le_refl 80) s1 (fun _ ↦ pos24Slot2E2Const) s3
        pos80Slot4EShiftFn cfg)
      hSlotsSm
      (zeroSubwireEpsSlotS1_pwu24_sum_le_of_eps2_and_nonS3
        eps2OfW nonS3Nano hNonS3 W hW28 hW36 bSub hbLo hbHi s3 hs3Eps)
      (by rw [show ((10 : ℝ) ^ 9) = 1000000000 by norm_num]; linarith)
      (tierBB2IdMod4_isHermitian (truncOfW W cfg))
      (tierBB4IdMod4_isHermitian (truncOfW W cfg))
      (tierBB2IdMod4_norm_le_one (truncOfW W cfg))
      (tierBB4IdMod4_norm_le_one (truncOfW W cfg))
      (norm_tierBB2ActMod4_Bhmt_midpoint_sub_le B
        (b_one_le_of_six_le hB6) (b_le_29_of_le_27 hB27) (truncOfW W cfg))
      (norm_tierBB4ActMod4_Bhmt_midpoint_sub_le B
        (b_one_le_of_six_le hB6) (b_le_29_of_le_27 hB27) (truncOfW W cfg))
      hBlocks
  exact ⟨E₀, δ_prep₀, ε_id₀, Heff_act, Heff_id,
    hSum, hCommAct, hBE, hHermId, hCommId, hDiff, hAgree⟩

/-- Decidable per-horizon error cap predicate parameterized by `nonS3Nano : ℕ → ℕ`
(enabling 1-line composition with `G5` `nonS3ChiralPos512OptNano`). -/
def ChiralCoinCapBhmtPwu24GenOnHorizon
    (nonS3Nano : ℕ → ℕ) (coinNano B W bSub s3EpsNano capNano : ℕ) : Prop :=
  coinNano ≤ 300000 ∧
    coinNano + deltaPosBhmtExactNatOfB B + (nonS3Nano W - 29000) +
      eps1Pwu24Num bSub + s3EpsNano ≤ capNano

instance instDecidableChiralCoinCapBhmtPwu24Gen
    (nonS3Nano : ℕ → ℕ) (c B W bSub s3 cap : ℕ) :
    Decidable (ChiralCoinCapBhmtPwu24GenOnHorizon nonS3Nano c B W bSub s3 cap) := by
  unfold ChiralCoinCapBhmtPwu24GenOnHorizon; infer_instance

-- ============================================================================
-- Section 4: `Pos512ChiralBhmtPwu24HorizonSelPkg` & `GenBetaExtHkSelAndPertSpec` Builders
-- ============================================================================

/-- Stage-2-free width-polymorphic per-horizon `SELECT` package for `PosPostBhmt` (`1,130 T`)
+ `ora1Pwu24OfBSub` (`4 * (bSub + 51)` `T`) on `truncChiralPos512OfW W`. -/
structure Pos512ChiralBhmtPwu24HorizonSelPkg
    (mWork k_idle : ℕ) (hk : k_idle ≤ 48)
    (W B bSub t2Ctrl t2Cat tSelCtrl tSelCat : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    (s3Ora : MomSingleSlotOracle 80 48 3) where
  hmWorkPost : 128 ≤ mWork
  selOra : FullSysSelectOracleBundle 80 48
  selImpl : SingleCatSelectImpl 80 48 coreQftHadamardPrunedBundle128 selOra
  sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat
    coreQftHadamardPrunedBundle128 selOra selImpl
  leaf2 : Leaf2SpecOfTrunc (truncChiralPos512OfW W) t2Ctrl t2Cat
  hLeaf2Pos : leaf2.uPosPhase0 = uPosPhase80Mod4OfB B hB6 hB27
  hOra : SelectOraHypothesisOfS1Trunc (truncChiralPos512OfW W) selOra
    (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) leaf2 s3Ora
  hTwist_s2 : ∀ c, (selOra.uTwist c).1 * slotBitProj (iSlot2 80) 0 =
    slotBitProj (iSlot2 80) 0 * (selOra.uTwist c).1
  hTwist_s1 : ∀ c, (selOra.uTwist c).1 * slotBitProj (iSlot1 80) 1 =
    slotBitProj (iSlot1 80) 1 * (selOra.uTwist c).1
  hTwist_s0 : ∀ c, (selOra.uTwist c).1 * slotBitProj (iSlot0 80) 0 =
    slotBitProj (iSlot0 80) 0 * (selOra.uTwist c).1
  hPos_slack : ∀ c,
    let P_slack := slotBitProj (iSlot2 80) 0 * slotBitProj (iSlot1 80) 1 *
      slotBitProj (iSlot0 80) 0
    (selOra.uPosPhase c).1 * P_slack = P_slack

/-- Construct a `Pos512ChiralBhmtPwu24HorizonSelPkg` directly from the 6 raw `SELECT` fields
(deriving `hTwist_s2/s1/s0` and `hPos_slack` automatically from `hOra` + `leaf2`). -/
noncomputable def mkPos512ChiralBhmtPwu24PkgOfOra
    {mWork k_idle : ℕ} (hm128 : 128 ≤ mWork) {hk : k_idle ≤ 48}
    {W B bSub t2Ctrl t2Cat tSelCtrl tSelCat : ℕ}
    {hB6 : 6 ≤ B} {hB27 : B ≤ 27}
    {hbLo : 18 ≤ bSub} {hbHi : bSub ≤ 24}
    {s3Ora : MomSingleSlotOracle 80 48 3}
    (selOra : FullSysSelectOracleBundle 80 48)
    (selImpl : SingleCatSelectImpl 80 48 coreQftHadamardPrunedBundle128 selOra)
    (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat
      coreQftHadamardPrunedBundle128 selOra selImpl)
    (leaf2 : Leaf2SpecOfTrunc (truncChiralPos512OfW W) t2Ctrl t2Cat)
    (hLeaf2Pos : leaf2.uPosPhase0 = uPosPhase80Mod4OfB B hB6 hB27)
    (hOra : SelectOraHypothesisOfS1Trunc (truncChiralPos512OfW W) selOra
      (ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)) leaf2 s3Ora) :
    Pos512ChiralBhmtPwu24HorizonSelPkg mWork k_idle hk W B bSub
      t2Ctrl t2Cat tSelCtrl tSelCat hB6 hB27 hbLo hbHi s3Ora where
  hmWorkPost := hm128
  selOra := selOra
  selImpl := selImpl
  sel := sel
  leaf2 := leaf2
  hLeaf2Pos := hLeaf2Pos
  hOra := hOra
  hTwist_s2 := step_hTwist_s2_s1 hOra
  hTwist_s1 := step_hTwist_s1_s1 hOra
  hTwist_s0 := step_hTwist_s0_s1 hOra
  hPos_slack c := by rw [hOra.hPosEq c]; exact leaf2.hPosSlack2

/-- Parametric `(eps2OfW, hSlot2Agrees, nonS3Nano)` (`G5` `NucMatADipSexticCap`-composable)
`GenBetaExtHkSelAndPertSpec` builder for `pos80BhmtPostPrepCert` + `ora1Pwu24OfBSub`. -/
noncomputable def mkSlimChiralBhmtPwu24GenBetaSelAndPertSpecOfEps2AndN
    (eps2OfW : ℕ → ℝ)
    (hSlot2Agrees : ∀ (W : ℕ) (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
      (E_sp : Fin 6 → ℝ), E_sp 2 = pos24Slot2E2Const → E_sp 5 = pos24Slot2E2Const / 108 →
      AgreesOnFermionicSector spinUp
        (gridProjector *
          ((mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg : ℂ) •
            (smToTwosSysUnitary.1 * tierBB2IdMod4 (truncChiralPos512OfW W cfg) *
              smToTwosSysUnitary.1)) * gridProjector)
        (sixChannelShifted cfg E_sp 2 + sixChannelShifted cfg E_sp 5)
        ((109 / 108 : ℝ) * eps2OfW W))
    (nonS3Nano : ℕ → ℕ)
    (hNonS3 : ∀ W, 28 ≤ W → W ≤ 36 →
      (6 : ℝ) / 10 ^ 7 + (109 / 108 : ℝ) * eps2OfW W + eps4_q30_tight ≤
        ((nonS3Nano W - 29000 : ℕ) : ℝ) / 1000000000)
    {mWork k_idle : ℕ} (h100 : 100 ≤ mWork) {hk : k_idle ≤ 48}
    {α : ℝ} (hα : 0 < α)
    {W B bSub tCoin coinNano t2Ctrl t2Cat tSelCtrl tSelCat s3EpsNano epsCapNano : Fin 10 → ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    {hbLo : ∀ j, 18 ≤ bSub j} {hbHi : ∀ j, bSub j ≤ 24}
    (hW28 : ∀ j, 28 ≤ W j) (hW36 : ∀ j, W j ≤ 36)
    (wTarget : Fin 10 → Fin 6 → ℝ)
    (hw0 : ∀ j, wTarget j 0 = wIdealRat 0) (hw1 : ∀ j, wTarget j 1 = wIdealRat 1)
    (hw2 : ∀ j, wTarget j 2 = wIdealRat 2) (hw4 : ∀ j, wTarget j 4 = wIdealRat 4)
    (hw5 : ∀ j, wTarget j 5 = 0)
    (coinSched : ∀ j, Coin3CleanProgSpecOfWeights (wTarget j) α
      (tCoin j) (((coinNano j : ℕ) : ℝ) / 1000000000))
    (hBCases : ∀ j, B j = 22 ∨ B j = 23 ∨ B j = 24 ∨ B j = 25 ∨ B j = 26 ∨ B j = 27)
    (s3Ora : Fin 10 → MomSingleSlotOracle 80 48 3)
    (hs3W : ∀ j cfg, (s3Ora j).wSlot cfg = wTarget j 3)
    (hs3Eps : ∀ j, (s3Ora j).epsIntr ≤ (s3EpsNano j : ℝ) / 1000000000)
    (pkg : ∀ j, Pos512ChiralBhmtPwu24HorizonSelPkg mWork k_idle hk (W j) (B j) (bSub j)
      (t2Ctrl j) (t2Cat j) (tSelCtrl j) (tSelCat j)
      (hB6 j) (hB27 j) (hbLo j) (hbHi j) (s3Ora j))
    (hCap : ∀ j, ChiralCoinCapBhmtPwu24GenOnHorizon nonS3Nano
      (coinNano j) (B j) (W j) (bSub j) (s3EpsNano j) (epsCapNano j)) :
    GenBetaExtHkSelAndPertSpec mWork k_idle hk α
      (fun j ↦ tCoin j + 1130) tSelCtrl tSelCat
      (fun j ↦ (epsCapNano j : ℝ) / 1000000000) where
  qft := coreQftHadamardPrunedBundle128
  prep j := prepBundleOfPostCertAndCoin pos80BhmtPostPrepCert (coinSched j)
  selOra j := (pkg j).selOra
  selImpl j := (pkg j).selImpl
  sel j := (pkg j).sel
  hmPrep j := prepBundleOfPostCertAndCoin_hmPrep
    pos80BhmtPostPrepCert (coinSched j) h100 (pkg j).hmWorkPost
  hTPrep _ := le_rfl
  hPrepLow j c := fixesLow3924_zeroSubwireCleanProgPrep_Bhmt (coinSched j).toDummySpec c
  hPrepCtrl3 j c := fixesCtrl3_zeroSubwireCleanProgPrep_Bhmt (coinSched j).toDummySpec c
  hTwist_s2 j c := (pkg j).hTwist_s2 c
  hTwist_s1 j c := (pkg j).hTwist_s1 c
  hTwist_s0 j c := (pkg j).hTwist_s0 c
  hPos_slack j c := (pkg j).hPos_slack c
  hα := hα
  hPert j c spinUp :=
    selOra_uCoin_gridPerturbation_genSlot2_Bhmt_pwu24_of
      truncChiralPos512OfW eps2OfW hSlot2Agrees
      nonS3Nano hNonS3 hα (hCap j).1 (hBCases j) (hB6 j) (hB27 j)
      (hW28 j) (hW36 j) (hbLo j) (hbHi j)
      (wTarget j) (hw0 j) (hw1 j) (hw2 j) (hw4 j) (hw5 j)
      coreQftHadamardPrunedBundle128 hqftFactor_coreQftPruned128
      (prepBundleOfPostCertAndCoin pos80BhmtPostPrepCert (coinSched j))
      (coinSched j).uCoin
      (prepBundleOfPostCertAndCoin_uPrep_eq_gen pos80BhmtPostPrepCert (coinSched j))
      (coinSched j).hWeightErr
      (pkg j).selOra (pkg j).leaf2 (pkg j).hLeaf2Pos (s3Ora j)
      (hs3Eps j) (hs3W j) (pkg j).hOra (hCap j).2 c spinUp

end ConfigParetoSelectStitch

end ParetoSelectStitch



-- ============================================================================
-- Part: SelectS1
-- ============================================================================
noncomputable section

namespace SelectS1

section ConfigSelectS1
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2000
set_option exponentiation.threshold 5000
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.BridgeDuhamel
open Barrel3PassCommuteHelpers
open Koff3PassSelectBridge
open Leaf1Pass1And3Width204
open Leaf4HadCut570
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
local instance (priority := 1000000) instNeZero_SelectS1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority := 1000000) instGroupUnitaryFast_SelectS1 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary

open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
open PosMomSelectSandwich (slotBitProj)
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge
  (FullSysQft654Bundle FullSysSelectOracleBundle fullSysCoreWires fullSysBEWires
   fullSysQftCoreUnitary iSlot0 iSlot1 iSlot2 IntertwinesLocalCat
   disjointWires_compose_of_disjoint disjointWires_concat_left)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (rTopCatSlice)
open SingleCatClosure (SingleCatSelectImpl compose_concat_eq_singleCat)
open OraAndPrepBundle (coreUnitaryToFullSys)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open NuclearTwistMulKickAndBridge288 (count_dyn_seq)
open NuclearTwistRealizes (uXor32Core uSlot4KickCore)
open CoinDispatchedBarrel288 (uBarrelFast uBarrelFast_comm_high_wire)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open Slot3StreamUncK35Shift3 (rEC80)
open InterWalkRSum42Hoist
  (inv_intertwine_lemma embedUnitary_inv_symm kFull80 rAct0 rCoreFull rSegOrig rSegFull E_stream42
  E_rawStream42 FixesLow3924 h3924_core hCoreFull_disj_PG48Full)
open HoistBorrow42ProjBridge (RealizesOnProj)
open KoffPrunedSlot2ZeroMuxTrunc37 (uKoffDiagCore uKoffDiagCore_comm_slotBitProj)
open SchedBranchStitchGen
  (uFusedTwistRestCut80_factor uSlot4KickCore_comm_slotBitProj uXor32Core80_comm_slotBitProj
   op_comm_mul uSlot0LocalXorBit5_comm_slotBitProj uSlot0LocalXorBit5_eq_diagonal
   unitaryConj_eq_inv_mul unitaryConj_mul unitaryConj_mul_left unitaryConj_cancel_inv
   dyadicDiagUnitary_eq_diagonal)
open Barrel3PassSelectStitch
  (Barrel3PassMidSpec CTLeafSpec CTLeafAlgSpec barrel3PassSelectImpl rCoreSeg rPG48Seg rCTSeg
   rCat80 hCoreSeg_disj_PG48Seg concat_compose_rCoreInCT80 rCoreInCT80 uTrailCliffordXor80
   uTwistSegOfSpec uMidBarrel3PassEff uMidBarrel3PassCat intertwinesCat_uTwistSegOfSpec
   intertwinesCat_ctLeafSpec intertwinesCat_ctLeafAlgSpec unitary_inv_comm_of_comm
   uTrailCliffordXor80_comm_slotBitProj momBranchP1_of_tailId)
open Pass1Leaf273 (uPass1Cat uPass3Cat)
open Leaf4Ext48TopStitch
  (FixesCtrl3 h3954_core CommutesWithReg embedIntertwine2 HoistedExtHkSelectSpec
   rPGIdleOrig rPGIdle rUnusedCtrl3Full rSlack3Full rSlackIdleFull
   pCtrl3Zero pSlack3Zero pPGIdleZero pExt6IdleZero pSlackIdleZero
   pExt6Zero_eq_mul pExt6IdleZero_eq_mul pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle
   E_ctrl3Ext E_segExt pCtrl3ExtOn pHoistExtOn
   rCoreTopCatFull rExt45IdleFull rCoreTopCatFull_disj_rExt45IdleFull rCoreTopCatSum42Full
   rCtrl3InCoreCat rWorkCtrlTwist rWorkSlackIdle basisOutcomeProjector_comm_any)
open SelectCtrlStitch (rTwAct_disj_rWTw rSegFull_compose_rCoreSeg_eq)
open SelectHoistLemmas
  (pCoinSlack010Seg hoistedSelect_mul_pCoinSlack010Orig commutesWithReg_rPGIdleOrig_hoistedSelect)
open SelectExtStitch
  (rCoreTopCatInCT)
open SelectStitch
  (Leaf2SpecOfTrunc uProjPosToCut80 embed_coreElecCosetB1_comm_uProjPosToCut80
    uProjPosToCut80_comm_uBarrelFast uSlot4KickCore_comm_uProjPosToCut80
    uVepSlot2KickCore_comm_uProjPosToCut80 uTailHad3DCore_comm_uKoffMomCore80)
open SelStitchHelper
  (coreQftHadamardPrunedBundle128_eq_ideal654 uSlot3HadCutCat36FullSys_mul_pCoinSlack010Seg)
open Leaf3HadCutBridge (uSlot3HadCutCat36FullSys)
open SingleBarrel7StepSelect (uFoldedPass123Seg)
open TruncWAsymHeldTwShell
  (SlimFoldedPass123Bundle11 Slot3InnerHeldTwSpec Slot3InnerGenAsymHeldTwSpec_mWork
   Slot3InnerSlot3InnerCircuitSpec_mWork FoldedPass123CircuitSpec_mWork
   leaf2Slot3InnerOfTruncB)
open _root_.QuantumComputation.Specs.StoppingPowerSolution.TruncWAsymHeldTwShell
open SingleBarrel128RealizesOnProjShell (realizesOnProj_of_clean_rWork)
open HeldStreamEStream42InterfaceShell
  (E_rawSegExt E_rawCtrl3Ext pRawHoistExtOn pRawCtrl3ExtOn rSub3Act_disj_rWorkCtrlTwist11
   liftSlackIdle151_to_pHoistExt11 liftSlackIdle151_to_pRawHoistExt11
   liftCtrlTwist148_to_streamPGIdle11 liftCtrlTwist148_to_rawStreamPGIdle11
   topCat_comm_E_segExt11_and_rawSegExt11 topCat_comm_streamPGIdle11
   rSub3Act_disj_rWorkSlackIdle11)
open SingleBarrel8StepCleanShell
  (catState48 hkIdle intertwinesCat_of_mul_catOp_eq mul_catOp_of_intertwinesCat
   sandwich_mul_catOp_eq_of_intertwinesCat liftStreamPGIdle11_to_pCtrl3Ext11
   liftRawStreamPGIdle11_to_pRawCtrl3Ext11)
open Slot3InnerSharedCoin06NucTwist_Select
  (Slot3InnerSlot3InnerSpecCore uT0CoreOfTrunc uTwistEffHadCut80 slot3InnerBarrelTwistSpec288
   Slot3InnerSlot3InnerSpec slot3InnerPass2LeafSpec330 uTwHeldFullHeldTw uTwSegHeldTw
   uTwistSegOfSpec_slot3InnerBarrelTwistSpec288 rTwAct_disj_rWorkSlackIdle11
   uTwHeldFullHeldTw_intertwines_ctrl3Ext11 embed_rCoreTopCatFull37_comm_pSlack3Zero
   uTwHeldFullHeldTw_intertwines_segExt11)
open Slot3InnerSlot3Inner (uT0CoreOfTrunc_slot3_comm_slotBitProj)
open Slot3Inner5_MasterHeldTwEndpoints (leaf2Slot3InnerOfTruncB_uPosPhase0)
open Slot3Norm1s36_161w (Norm1sTier)
open SubvoxelNuclearTrunc34And33Physics (truncWCfg)
open Leaf2PosMod4WidthCore (uPosPhase80Mod4OfB)
open GqspSlot3UltraBkAnd8TierCert
  (IsCertifiedNorm1sTier6 s3Swap3OracleNorm1sUltraBk s3Swap3OracleNorm1sUltraBk_commEC)
open Slot3NuclearTruncBkPhysics (truncBkNucCfg)
open UltraSlot3MasterBkBundle
  (tLeaf3CtrlUltraBk tLeaf3CatUltraBk)
open Pos512FastPrepAndCoin (truncChiralPos512OfW)
open SlimNorm1sWideSelect
  (twHeld37Wide52Spec190 mkNorm1sSlot3InnerSlot3InnerSpec truncChiralPos512OfW_eq_truncWCfg
   t2CtrlSlot3InnerOfB t2CatSlot3InnerOfB fixesLow3924_uSlot3HadCutCat36FullSys
   uSlot3HadCutCat36FullSys_comm_uPass1Cat)
open Slot1Pwu24
  (ora1Pwu24OfBSub slot1Pwu24HadCutLeafSpec slot1Pwu24HadCutLeafSpec_tLeaf
   slot1Pwu24HadCutLeafSpec_uCat_eq_core fixesCtrl3_slot1Pwu24HadCutEff
   fixesLow3924_slot1Pwu24HadCutEff rCoreFull_fixesLow3924_comm_stream42
   slot1Pwu24HadCutLeafSpec_uCat_comm_uPass1Cat
   slot1Pwu24HadCutLeafSpec_uCat_mul_pCoinSlack010Seg
   mkSelectOraBundleOfPwu24Trunc SelectOraHypothesisOfS1Trunc
   stepSelectOraHypothesisOfPwu24Trunc ora1Pwu24OfBSub_conj_highWire)
open ParetoSelectStitch
  (Pos512ChiralBhmtPwu24HorizonSelPkg mkPos512ChiralBhmtPwu24PkgOfOra)

/-- Parametric `Slot 1` HadCut leaf specification at workspace width `mWork` and `.T`-gate cap
  `tBound`. -/
structure Slot1HadCutLeafSpec (mWork tBound : ℕ) : Type 1 where
  ora1 : MomSingleSlotOracle 80 48 1
  leaf : CTLeafSpec mWork
  leaf330 : CTLeafSpec 330
  htLeaf : leaf.tLeaf ≤ tBound
  hUEffEq : ∀ c,
    leaf.uEff c =
    unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹ (coreUnitaryToFullSys (ora1.uSlotEff c))
  hLeaf330UEff : ∀ c, leaf330.uEff c = leaf.uEff c
  hLeaf330UCat : ∀ c, leaf330.uCat c = leaf.uCat c
  hUCatEqCore : ∀ c, leaf.uCat c = rCoreInCT80.embedUnitary (leaf.uEff c)
  hFixesLow : ∀ c, FixesLow3924 h3924_core (leaf.uEff c).1
  hFixesCtrl3 : ∀ c, FixesCtrl3 h3954_core (leaf.uEff c).1
  hCommPass1 : ∀ c,
    rCTSeg.embedUnitary (leaf.uCat c) * rCTSeg.embedUnitary uPass1Cat =
      rCTSeg.embedUnitary uPass1Cat * rCTSeg.embedUnitary (leaf.uCat c)
  hMulSlack010 : ∀ c, (rCTSeg.embedUnitary (leaf.uCat c)).1 * pCoinSlack010Seg = pCoinSlack010Seg
  hConjHighWire : ∀ c (U : Unitary (2 ^ (fullSysCoreWires 80))),
    (∀ q : Wire (fullSysCoreWires 80), 3924 ≤ q.val → ∀ b : Fin 2,
      U.1 * slotBitProj q b = slotBitProj q b * U.1) →
    unitaryConj U (coreUnitaryToFullSys (ora1.uSlotEff c)) = coreUnitaryToFullSys (ora1.uSlotEff c)

/-- `Slot1HadCutLeafSpec` instance for `ora1Pwu24OfBSub` (`75 ≤ mWork`, `tBound = 4 * (bSub +
  51)`). -/
noncomputable def slot1Pwu24LeafSpec (bSub : ℕ) (hbLo : 18 ≤ bSub) (hbHi : bSub ≤ 24)
    {mWork : ℕ} (hm75 : 75 ≤ mWork) : Slot1HadCutLeafSpec mWork (4 * (bSub + 51)) where
  ora1 := ora1Pwu24OfBSub bSub hbLo hbHi (le_refl 80)
  leaf := slot1Pwu24HadCutLeafSpec bSub hbLo hbHi hm75
  leaf330 := slot1Pwu24HadCutLeafSpec bSub hbLo hbHi (by decide : 75 ≤ 330)
  htLeaf := le_of_eq (slot1Pwu24HadCutLeafSpec_tLeaf bSub hbLo hbHi hm75)
  hUEffEq _ := rfl
  hLeaf330UEff _ := rfl
  hLeaf330UCat _ := rfl
  hUCatEqCore := slot1Pwu24HadCutLeafSpec_uCat_eq_core bSub hbLo hbHi hm75
  hFixesLow := fixesLow3924_slot1Pwu24HadCutEff bSub hbLo hbHi hm75
  hFixesCtrl3 := fixesCtrl3_slot1Pwu24HadCutEff bSub hbLo hbHi hm75
  hCommPass1 := slot1Pwu24HadCutLeafSpec_uCat_comm_uPass1Cat bSub hbLo hbHi hm75
  hMulSlack010 := slot1Pwu24HadCutLeafSpec_uCat_mul_pCoinSlack010Seg bSub hbLo hbHi hm75
  hConjHighWire := ora1Pwu24OfBSub_conj_highWire bSub hbLo hbHi

/-- `Slot 3` inner specification paired with an arbitrary `s1 : Slot1HadCutLeafSpec mWorkS1 tS1`. -/
abbrev Slot3InnerSlot3InnerSpecS1 (truncFn : Configuration → Configuration)
    {mWorkS1 tS1 tTwPair : ℕ} (s1 : Slot1HadCutLeafSpec mWorkS1 tS1)
    (tw : Slot3InnerHeldTwSpec tTwPair) (t3Ctrl t3Cat : ℕ) :=
  Slot3InnerSlot3InnerSpecCore (fullSysCoreWires 80 + 36) (fullSysCoreWires 80)
    (fullSysCoreWires 80 + 48) (fullSysBEWires 80 + 48) 80 48 190 193
    (rCoreTopCatInCT 36 (by decide))
    rCTSeg
    tw.uTwEff (uT0CoreOfTrunc truncFn)
    s1.leaf.uEff (pass1SpecOfLe (le_refl 154)).uEff
    uPass1Cat
    (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
    coreUnitaryToFullSys
    (Slot3StreamUncK35Shift3.CommutesWithReg rEC80)
    (FixesLow3924 (Nat.le_trans h3924_core (Nat.le_add_right _ 36)))
    (rCtrl3InCoreCat 36)
    (slotBitProj (iSlot2 80) 0) (slotBitProj (iSlot2 80) 1)
    pCoinSlack010Seg
    (IntertwinesLocalCat (kAct := fullSysCoreWires 80) (mCat := 48))
    t3Ctrl t3Cat

/-- `Slot3InnerSlot3InnerSpec` adapter for `leaf3TruncSpec_ultraBk` (`21 ≤ bk ≤
  36`). -/
noncomputable def mkNorm1sSlot3InnerSlot3InnerSpecS1 (trunc : Configuration →
    Configuration) {mWorkS1 tS1 : ℕ} (s1 : Slot1HadCutLeafSpec mWorkS1 tS1) (W bk : ℕ)
    (t : Norm1sTier)
    (hW28 : 28 ≤ W) (hW36 : W ≤ 36) (hTrunc : trunc = truncWCfg W)
    (hbk : 21 ≤ bk ∧ bk ≤ 36) (ht : IsCertifiedNorm1sTier6 t) :
    Slot3InnerSlot3InnerSpecS1 trunc s1 (twHeld37Wide52Spec190 W hW28 hW36) (tLeaf3CtrlUltraBk bk t)
      (tLeaf3CatUltraBk bk t) :=
  { ora3 := s3Swap3OracleNorm1sUltraBk t ht bk hbk
    hSlot3CommEC := s3Swap3OracleNorm1sUltraBk_commEC t ht bk hbk
    uInnerCatSub c := uSlot3HadCutCat36FullSys t (truncBkNucCfg bk c)
    uInnerEff c := unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
      (coreUnitaryToFullSys ((s3Swap3OracleNorm1sUltraBk t ht bk hbk).uSlotEff c))
    hLow3 c := fixesLow3924_uSlot3HadCutCat36FullSys t (truncBkNucCfg bk c)
    hCommCtrl3 := (mkNorm1sSlot3InnerSlot3InnerSpec trunc W bk t hW28 hW36 hTrunc hbk ht).hCommCtrl3
    hCommPass1 c := uSlot3HadCutCat36FullSys_comm_uPass1Cat t (truncBkNucCfg bk c)
    hSlack c := uSlot3HadCutCat36FullSys_mul_pCoinSlack010Seg t (truncBkNucCfg bk c)
    hIntertwinesInner :=
      (mkNorm1sSlot3InnerSlot3InnerSpec trunc W bk t hW28 hW36 hTrunc hbk ht).hIntertwinesInner
    hTwEffCommP0 c := uT0CoreOfTrunc_slot3_comm_slotBitProj (truncWCfg W) c (by decide) 0
    hTwEffP0 c := by subst hTrunc; rfl
    hInnerOnP0 c :=
      (momOracleConjInvTailHad3D_on_P0_and_comm_P1 (s3Swap3OracleNorm1sUltraBk t ht bk hbk) rfl c).1
    hTwEffCommP1 c := uT0CoreOfTrunc_slot3_comm_slotBitProj (truncWCfg W) c (by decide) 1
    hInnerCommP1 c :=
      (momOracleConjInvTailHad3D_on_P0_and_comm_P1 (s3Swap3OracleNorm1sUltraBk t ht bk hbk) rfl c).2
    hMomPreSandwichP1 c := by subst hTrunc; rfl }

/-- Full-width (`kFull80`) parametric `Slot 1` unitary. -/
noncomputable def uSlot1FullS1 {mWorkS1 tS1 : ℕ} (s1 : Slot1HadCutLeafSpec mWorkS1 tS1)
    (c : Configuration) : Unitary (2 ^ kFull80) :=
  rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c))

/-- Segment-level (`fullSysBEWires 80 + 48`) parametric `Slot 1` unitary. -/
noncomputable def uSlot1SegS1 {mWorkS1 tS1 : ℕ} (s1 : Slot1HadCutLeafSpec mWorkS1 tS1)
    (c : Configuration) : Unitary (2 ^ (fullSysBEWires 80 + 48)) :=
  rCTSeg.embedUnitary (s1.leaf.uCat c)

private theorem slot1S1_comm_E_segExt11_and_rawSegExt11 {mWorkS1 tS1 : ℕ}
    (s1 : Slot1HadCutLeafSpec mWorkS1 tS1) (c : Configuration) :
    (rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c))).1 *
        E_segExt 11 (by decide) =
      E_segExt 11 (by decide) *
        (rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c))).1 ∧
    (rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c))).1 *
        E_rawSegExt 11 (by decide) =
      E_rawSegExt 11 (by decide) *
        (rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c))).1 := by
  have hCTCore : rCTSeg.compose rCoreInCT80 = rCoreSeg :=
    concat_compose_rCoreInCT80 rCoreSeg rPG48Seg hCoreSeg_disj_PG48Seg
  have hU : rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c)) =
      rCoreFull.embedUnitary (s1.leaf.uEff c) := by
    rw [(s1.hUCatEqCore c), ← QRegister.embedUnitary_compose rCTSeg, hCTCore,
      ← QRegister.embedUnitary_compose rSegFull, rSegFull_compose_rCoreSeg_eq]
  obtain ⟨hS, hR⟩ := rCoreFull_fixesLow3924_comm_stream42 (s1.hFixesLow c)
  have hC : (rCoreFull.embedUnitary (s1.leaf.uEff c)).1 * pCtrl3Zero =
      pCtrl3Zero * (rCoreFull.embedUnitary (s1.leaf.uEff c)).1 := by
    rw [← rSegFull_compose_rCoreSeg_eq, QRegister.embedUnitary_compose]
    exact SelectExtStitch.rCoreSeg_comm_pCtrl3Zero_of_fixesCtrl3
      (s1.hFixesCtrl3 c)
  have hDisjSlk : rCoreFull.DisjointWires (rSlackIdleFull 11 (by decide)) := by
    rw [QRegister.disjoint_iff]; intro a q h
    exact (rCoreTopCatFull_disj_rExt45IdleFull 11 0 (by decide)).ne
      (Fin.castAdd 0 a) (Fin.natAdd 42 q)
      (by simpa only [rCoreTopCatFull, rExt45IdleFull,
        QRegister.concat_apply_left, QRegister.concat_apply_right] using h)
  have hSlk : (rCoreFull.embedUnitary (s1.leaf.uEff c)).1 *
      pSlackIdleZero 11 (by decide) =
      pSlackIdleZero 11 (by decide) *
        (rCoreFull.embedUnitary (s1.leaf.uEff c)).1 := by
    rw [QRegister.embedUnitary_val]
    exact (CommutesWithReg.of_disjoint hDisjSlk _).comm_basisOutcomeProjector 0
  have hExt6 : (rCoreFull.embedUnitary (s1.leaf.uEff c)).1 *
      pExt6IdleZero 11 (by decide) =
      pExt6IdleZero 11 (by decide) *
        (rCoreFull.embedUnitary (s1.leaf.uEff c)).1 := by
    rw [pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle, ← Matrix.mul_assoc, hC,
      Matrix.mul_assoc, hSlk, ← Matrix.mul_assoc]
  rw [hU]
  unfold E_segExt E_rawSegExt
  exact ⟨by rw [← Matrix.mul_assoc, hS, Matrix.mul_assoc, hExt6, ← Matrix.mul_assoc],
    by rw [← Matrix.mul_assoc, hR, Matrix.mul_assoc, hExt6, ← Matrix.mul_assoc]⟩

private theorem slot1S1_comm_streamPGIdle11 {mWorkS1 tS1 : ℕ}
    (s1 : Slot1HadCutLeafSpec mWorkS1 tS1) (c : Configuration) :
    (rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c))).1 *
        (E_stream42 * pPGIdleZero 11 (by decide)) =
      (E_stream42 * pPGIdleZero 11 (by decide)) *
        (rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c))).1 ∧
    (rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c))).1 *
        (E_rawStream42 * pPGIdleZero 11 (by decide)) =
      (E_rawStream42 * pPGIdleZero 11 (by decide)) *
        (rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c))).1 := by
  have hCTCore : rCTSeg.compose rCoreInCT80 = rCoreSeg :=
    concat_compose_rCoreInCT80 rCoreSeg rPG48Seg hCoreSeg_disj_PG48Seg
  have hU : rSegFull.embedUnitary (rCTSeg.embedUnitary (s1.leaf.uCat c)) =
      rCoreFull.embedUnitary (s1.leaf.uEff c) := by
    rw [(s1.hUCatEqCore c), ← QRegister.embedUnitary_compose rCTSeg, hCTCore,
      ← QRegister.embedUnitary_compose rSegFull, rSegFull_compose_rCoreSeg_eq]
  obtain ⟨hS, hR⟩ := rCoreFull_fixesLow3924_comm_stream42 (s1.hFixesLow c)
  have hDisjI : rCoreFull.DisjointWires (rPGIdle 11 (by decide)) :=
    (hCoreFull_disj_PG48Full.compose_right _)
  have hI : (rCoreFull.embedUnitary (s1.leaf.uEff c)).1 *
      pPGIdleZero 11 (by decide) =
      pPGIdleZero 11 (by decide) *
        (rCoreFull.embedUnitary (s1.leaf.uEff c)).1 := by
    rw [QRegister.embedUnitary_val]
    exact (CommutesWithReg.of_disjoint hDisjI _).comm_basisOutcomeProjector 0
  rw [hU]
  exact ⟨by rw [← Matrix.mul_assoc, hS, Matrix.mul_assoc, hI, ← Matrix.mul_assoc],
    by rw [← Matrix.mul_assoc, hR, Matrix.mul_assoc, hI, ← Matrix.mul_assoc]⟩

private theorem uSlot1FullS1_comm_raw11 {mWorkS1 tS1 : ℕ}
    (s1 : Slot1HadCutLeafSpec mWorkS1 tS1) (c : Configuration) :
    (uSlot1FullS1 s1 c).1 * E_rawCtrl3Ext 11 (by decide) =
      E_rawCtrl3Ext 11 (by decide) * (uSlot1FullS1 s1 c).1 ∧
    (uSlot1FullS1 s1 c).1 * E_rawSegExt 11 (by decide) =
      E_rawSegExt 11 (by decide) * (uSlot1FullS1 s1 c).1 := by
  refine ⟨?_, (slot1S1_comm_E_segExt11_and_rawSegExt11 s1 c).2⟩
  have hSPG : (uSlot1FullS1 s1 c).1 * (E_rawStream42 * pPGIdleZero 11 (by decide)) =
      (E_rawStream42 * pPGIdleZero 11 (by decide)) * (uSlot1FullS1 s1 c).1 :=
    (slot1S1_comm_streamPGIdle11 s1 c).2
  have hCTCore : rCTSeg.compose rCoreInCT80 = rCoreSeg :=
    concat_compose_rCoreInCT80 rCoreSeg rPG48Seg hCoreSeg_disj_PG48Seg
  have hCtrl : (uSlot1FullS1 s1 c).1 * pCtrl3Zero = pCtrl3Zero * (uSlot1FullS1 s1 c).1 := by
    unfold uSlot1FullS1
    rw [s1.hUCatEqCore c, ← QRegister.embedUnitary_compose rCTSeg, hCTCore]
    exact SelectExtStitch.rCoreSeg_comm_pCtrl3Zero_of_fixesCtrl3 (s1.hFixesCtrl3 c)
  have hComm : pPGIdleZero 11 (by decide) * pCtrl3Zero = pCtrl3Zero * pPGIdleZero 11 (by decide) :=
    basisOutcomeProjector_comm_any (rPGIdle 11 (by decide)) 0 rUnusedCtrl3Full 0
  have hRawEq : E_rawCtrl3Ext 11 (by decide) = (E_rawStream42 * pPGIdleZero 11 (by decide)) *
    pCtrl3Zero := by
    unfold E_rawCtrl3Ext; rw [Matrix.mul_assoc, hComm]
  rw [hRawEq, ← Matrix.mul_assoc, hSPG, Matrix.mul_assoc, hCtrl, ← Matrix.mul_assoc]
/-- `330`-wire (`42 + 288`) `CTLeafSpec` for `Slot3InnerSlot3InnerSpec` (`dInnerCtrl` widened
  from `190` to `330`). -/
noncomputable def slot3InnerSlot3InnerLeafSpec330_s1 (truncFn : Configuration → Configuration)
    {mWorkS1 tS1 tTwPair t3Ctrl t3Cat : ℕ} {s1 : Slot1HadCutLeafSpec mWorkS1 tS1}
    {tw : Slot3InnerHeldTwSpec tTwPair}
    (s3 : Slot3InnerSlot3InnerSpecS1 truncFn s1 tw t3Ctrl t3Cat) :
    CTLeafAlgSpec where
  uCat c := (rCoreTopCatInCT 36 (by decide)).embedUnitary (s3.uInnerCatSub c)
  uEff := s3.uInnerEff
  hIntertwines := s3.hIntertwinesInner
private theorem comm_mul_of_comm {D : ℕ} {x a b : Unitary D}
    (ha : x * a = a * x) (hb : x * b = b * x) : x * (a * b) = (a * b) * x := by
  rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]

private theorem conj_cancel_left_of_comm {D : ℕ} {L T M : Unitary D}
    (hLM : M * L = L * M) : (L * T)⁻¹ * (M * (L * T)) = T⁻¹ * (M * T) := by
  calc (L * T)⁻¹ * (M * (L * T)) = (T⁻¹ * L⁻¹) * ((L * M) * T) := by
        rw [_root_.mul_inv_rev, ← mul_assoc M L T, hLM]
    _ = T⁻¹ * ((L⁻¹ * L) * (M * T)) := by simp only [mul_assoc]
    _ = T⁻¹ * (M * T) := by rw [inv_mul_cancel, one_mul]

set_option exponentiation.threshold 5000 in
theorem slot3Inner_posBranchP0_s1 (truncFn : Configuration → Configuration)
    {mWorkS1 tS1 t2Ctrl t2Cat t3Ctrl t3Cat tTwPair : ℕ}
    (s1 : Slot1HadCutLeafSpec mWorkS1 tS1)
    (qft : FullSysQft654Bundle)
    (hQft : qft.uQft654 =
      DyadicQft64WalkCircuit220.coreQftHadamardIdeal654)
    (selOra : FullSysSelectOracleBundle 80 48)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (tw : Slot3InnerHeldTwSpec tTwPair)
    (s3 : Slot3InnerSlot3InnerSpecS1 truncFn s1 tw t3Ctrl t3Cat)
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1.ora1 leaf2 s3.ora3)
    (c : Configuration) :
    (((slot3InnerBarrelTwistSpec288 tw).uTwistEff c)⁻¹ *
      (uMidBarrel3PassEff qft selOra
        (pass1SpecOfLe (by decide : 154 ≤ 330))
        s1.leaf330.toAlg
        (slot3InnerSlot3InnerLeafSpec330_s1 truncFn s3)
        (slot3InnerPass2LeafSpec330 truncFn leaf2)
        (pass3SpecOfLe (by decide : 133 ≤ 330)) c *
        (slot3InnerBarrelTwistSpec288 tw).uTwistEff c)).1 *
      slotBitProj (iSlot2 80) 0 =
    (unitaryConj (fullSysQftCoreUnitary selOra.hmPay qft * selOra.uTwist c)
      (selOra.uPosPhase c)).1 * slotBitProj (iSlot2 80) 0 := by
  let P0 := slotBitProj (iSlot2 80) 0
  let B := uBarrelFast (le_refl 80)
  let Q := fullSysQftCoreUnitary selOra.hmPay qft
  let C_tr := uTrailCliffordXor80
  let S4 := uSlot4KickCore (by decide : 22 ≤ 80)
  let K := uKoffDiagCore (truncFn c) (by decide : 22 ≤ 80)
  let T₀ := uTwistEffBaseCut80 (truncFn c)
  let T := (slot3InnerBarrelTwistSpec288 tw).uTwistEff c
  let pass1 := pass1SpecOfLe (by decide : 154 ≤ 330)
  let slot1 := s1.leaf330
  let slot3 := slot3InnerSlot3InnerLeafSpec330_s1 truncFn s3
  let pass2 := slot3InnerPass2LeafSpec330 truncFn leaf2
  let pass3 := pass3SpecOfLe (by decide : 133 ≤ 330)
  have hSA0 := PosMomSelectSandwich.slotBitProj_conjTranspose (iSlot2 80) 0
  have hKP0 : K.1 * P0 = P0 * K.1 :=
    uKoffDiagCore_comm_slotBitProj (truncFn c) (by decide) (iSlot2 80) 0
  have hTwP0 : T.1 * P0 = P0 * T.1 := s3.hTwEffCommP0 c
  let T_pos :=
    (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
      ProjZ512QftAndTwist288.uVepSlot2KickCore (truncFn c) (by decide : 22 ≤ 80)) *
    (uXor32Core 80 *
      Proj3DCut.uProj3DCutCore (by decide : 22 ≤ 80))
  have hKTposP0 : (K * T_pos).1 * P0 = P0 * (K * T_pos).1 := by
    rw [Submonoid.coe_mul]
    exact op_comm_mul hKP0 (uTwistEffPosCut80_comm_slotBitProj (truncFn c) (by decide) 0)
  have hP1Comm : (pass1.uEff c).1 * P0 = P0 * (pass1.uEff c).1 := by
    dsimp only [pass1]; rw [pass1SpecOfLe_uEff]
    exact Pass1Leaf273.uPass1Eff_comm_slotBitProj (by decide) 0
  have hS1Id : (slot1.uEff c).1 * P0 = P0 := by
    dsimp only [slot1]; rw [s1.hLeaf330UEff c, s1.hUEffEq c]
    exact (momOracleConjInvTailHad3D_on_P0_and_comm_P1 s1.ora1 (by decide) c).1
  have hS3Id : (slot3.uEff c).1 * P0 = P0 := s3.hInnerOnP0 c
  have hPreP0 :
      (slot3.uEff c * (slot1.uEff c * (pass1.uEff c * T))).1 * P0 =
        (unitaryConj B S4 * T).1 * P0 := by
    have hPT : (pass1.uEff c * T).1 * P0 = P0 * (pass1.uEff c * T).1 := op_comm_mul hP1Comm hTwP0
    calc (slot3.uEff c * (slot1.uEff c * (pass1.uEff c * T))).1 * P0
        = (slot3.uEff c).1 * ((slot1.uEff c).1 * ((pass1.uEff c * T).1 * P0)) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (slot3.uEff c).1 * (((slot1.uEff c).1 * P0) * (pass1.uEff c * T).1) := by
            rw [hPT, Matrix.mul_assoc]
      _ = ((slot3.uEff c).1 * P0) * (pass1.uEff c * T).1 := by rw [hS1Id, Matrix.mul_assoc]
      _ = (pass1.uEff c).1 * (T.1 * P0) := by rw [hS3Id, ← hPT, Submonoid.coe_mul, Matrix.mul_assoc]
      _ = ((pass1.uEff c).1 * P0) * T.1 := by rw [hTwP0, Matrix.mul_assoc]
      _ = ((unitaryConj B S4).1 * P0) * T.1 := by
            dsimp only [pass1]
            rw [pass1SpecOfLe_uEff, Pass1Leaf273.uPass1Eff_mul_P0]
      _ = (unitaryConj B S4 * T).1 * P0 := by
            rw [Submonoid.coe_mul, Matrix.mul_assoc, ← hTwP0, Matrix.mul_assoc]
  let M_core := pass3.uEff c * (C_tr⁻¹ * (Q⁻¹ * (pass2.uEff c * (Q * (C_tr * unitaryConj B S4)))))
  have hLHSEq :
      (T⁻¹ * (uMidBarrel3PassEff qft selOra pass1 slot1.toAlg slot3 pass2 pass3 c * T)).1 * P0 =
      (T⁻¹ * (M_core * T)).1 * P0 := by
    dsimp only [uMidBarrel3PassEff, M_core, Q, C_tr, T]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc] at hPreP0 ⊢
    rw [hPreP0]
  rw [hLHSEq]
  have hPass2IdP1 : (pass2.uEff c).1 * slotBitProj (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1 := by
    change (unitaryConj B leaf2.uPosPhase0).1 * slotBitProj (iSlot2 80) 1 = _
    exact SchedBranchStitchGen.unitaryConj_uBarrelFast_mul_proj_id
      (uBarrelFast_comm_high_wire (le_refl 80) (iSlot2 80) (by decide) 1) leaf2.hPosOnP1
  have hQP0 : Q.1 * P0 = P0 * Q.1 :=
    FullSysCatSegmentBridge.fullSysQftCoreUnitary_comm_slotBitProj
      selOra.hmPay qft (by decide) (by decide) 0
  have hCP0 : C_tr.1 * P0 = P0 * C_tr.1 :=
    uTrailCliffordXor80_comm_slotBitProj (by decide) (by decide) 0
  have hP3Comm : (pass3.uEff c).1 * P0 = P0 * (pass3.uEff c).1 := by
    dsimp only [pass3]; rw [pass3SpecOfLe_uEff]
    exact Pass1Leaf273.uPass3Eff_comm_slotBitProj (by decide) 0
  have hMCoreComm : M_core.1 * P0 = P0 * M_core.1 := by
    dsimp only [M_core]
    simp only [Submonoid.coe_mul]
    exact op_comm_mul hP3Comm
      (op_comm_mul (unitary_inv_comm_of_comm C_tr hSA0 hCP0)
        (op_comm_mul (unitary_inv_comm_of_comm Q hSA0 hQP0)
          (op_comm_mul (unitary_comm_p0_of_mul_p1_id _ hPass2IdP1)
            (op_comm_mul hQP0
              (op_comm_mul hCP0
                (SchedBranchStitchGen.unitaryConj_uBarrelFast_comm_slotBitProj
                  (by decide) 0 (uSlot4KickCore_comm_slotBitProj _ 0)))))))
  have hTwEqKTpos : T.1 * P0 = (K * T_pos).1 * P0 := by
    change (tw.uTwEff c).1 * P0 = (K * T_pos).1 * P0
    rw [s3.hTwEffP0 c]
    dsimp only [uT0CoreOfTrunc, uTwistEffHadCut80, T_pos]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    rw [uProj3DHadCutCore80_mul_P0]
  rw [SchedBranchStitchGen.inv_mul_conj_eq_on_proj
      hSA0 hKTposP0 hTwEqKTpos hMCoreComm rfl]
  have hGlobal :
      (K * T_pos)⁻¹ * (M_core * (K * T_pos)) =
        unitaryConj (Q * selOra.uTwist c) (selOra.uPosPhase c) := by
    let D := uProjPosToCut80
    let L := K * D
    let M_pos := pass3.uEff c * (C_tr⁻¹ * (Q⁻¹ * (pass2.uEff c * ((Q * C_tr) * unitaryConj B S4))))
    have hP3Eq : pass3.uEff c = unitaryConj B S4⁻¹ := by
      dsimp only [pass3]; rw [pass3SpecOfLe_uEff]
      unfold Pass1Leaf273.uPass3Eff; rfl
    have hDXor : D * uXor32Core 80 = uXor32Core 80 * D := by
      rw [← FusedPreDiagFromTwist288.embed_bit5Flip654_eq_uXor32Core
        (by decide : 6 ≤ 80)]
      exact embed_coreElecCosetB1_comm_uProjPosToCut80 (by decide) _
    have hDVep : D * ProjZ512QftAndTwist288.uVepSlot2KickCore
          (truncFn c) (by decide : 22 ≤ 80) =
        ProjZ512QftAndTwist288.uVepSlot2KickCore
          (truncFn c) (by decide : 22 ≤ 80) * D :=
      uVepSlot2KickCore_comm_uProjPosToCut80 (truncFn c)
    have hDTilde : D * FusedPreDiagFromTwist288.uTildeFullCore
          (by decide : 6 ≤ 80) =
        FusedPreDiagFromTwist288.uTildeFullCore
          (by decide : 6 ≤ 80) * D :=
      embed_coreElecCosetB1_comm_uProjPosToCut80 (by decide) _
    have hTPosEq : T_pos = D * T₀ := by
      have hDP :
          Proj3DCut.uProj3DCutCore (by decide : 22 ≤ 80) =
            D * JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80) := by
        dsimp only [D, uProjPosToCut80]
        rw [mul_assoc, inv_mul_cancel, mul_one]
      have h3 := comm_mul_of_comm (comm_mul_of_comm hDTilde hDVep) hDXor
      dsimp only [T_pos, T₀, uTwistEffBaseCut80]
      simp only [hDP, ← mul_assoc]
      rw [← h3]
      simp only [mul_assoc]
    have hLComm : ∀ {X : Unitary (2 ^ (fullSysCoreWires 80))},
        K * X = X * K → D * X = X * D → L * X = X * L := fun hKX hDX ↦ by
      dsimp only [L]; rw [mul_assoc, hDX, ← mul_assoc, hKX, mul_assoc]
    have hKB : K * B = B * K := uKoffDiagCore_comm_uBarrelFast (truncFn c)
    have hKS4 : K * S4 = S4 * K := uKoffDiagCore_comm_uSlot4KickCore (truncFn c)
    have hDB : D * B = B * D := uProjPosToCut80_comm_uBarrelFast
    have hDS4 : D * S4 = S4 * D := uSlot4KickCore_comm_uProjPosToCut80
    have hLConjS4 : L * unitaryConj B S4 = unitaryConj B S4 * L :=
      hLComm (unitaryConj_comm_of_comm hKB hKS4) (unitaryConj_comm_of_comm hDB hDS4)
    have hLP3 : L * pass3.uEff c = pass3.uEff c * L := by
      rw [hP3Eq]
      exact hLComm (unitaryConj_comm_of_comm hKB (group_comm_inv_of_comm hKS4))
        (unitaryConj_comm_of_comm hDB (group_comm_inv_of_comm hDS4))
    have hLP2 : L * pass2.uEff c = pass2.uEff c * L :=
      hLComm (unitaryConj_comm_of_comm hKB (leaf2.hPosCommK c))
        (unitaryConj_comm_of_comm hDB leaf2.hPosCommProjCut)
    have hKQC : K * (Q * C_tr) = (Q * C_tr) * K :=
      uKoffDiagCore_comm_qft_mul_uTrailCliffordXor80 (truncFn c) qft selOra.hmPay hQft
    have hDQC : D * (Q * C_tr) = (Q * C_tr) * D := by
      have hDQ : D * Q = Q * D :=
        embed_coreElecCosetB1_comm_uProjPosToCut80 selOra.hmPay qft.uQft654
      have hDC : D * C_tr = C_tr * D := by
        dsimp only [C_tr, uTrailCliffordXor80]
        have hDPc : D * FusedPreDiagFromTwist288.uPreDiagCliffordCore (by decide : 6 ≤ 80) =
            FusedPreDiagFromTwist288.uPreDiagCliffordCore (by decide : 6 ≤ 80) * D :=
          embed_coreElecCosetB1_comm_uProjPosToCut80 (by decide : 6 ≤ 80) _
        rw [← mul_assoc, hDXor, mul_assoc, hDPc, ← mul_assoc]
      rw [← mul_assoc, hDQ, mul_assoc, hDC, ← mul_assoc]
    have hLQC : L * (Q * C_tr) = (Q * C_tr) * L := hLComm hKQC hDQC
    have hLQCi : L * (C_tr⁻¹ * Q⁻¹) = (C_tr⁻¹ * Q⁻¹) * L := by
      rw [(_root_.mul_inv_rev Q C_tr).symm]
      exact group_comm_inv_of_comm hLQC
    have hLM : M_pos * L = L * M_pos := by
      have hc := comm_mul_of_comm hLP3
        (comm_mul_of_comm hLQCi (comm_mul_of_comm hLP2 (comm_mul_of_comm hLQC hLConjS4)))
      dsimp only [M_pos]
      simpa only [mul_assoc] using hc.symm
    have hCancelL : (K * T_pos)⁻¹ * (M_core * (K * T_pos)) = T₀⁻¹ * (M_core * T₀) := by
      have hKT : K * T_pos = L * T₀ := by
        dsimp only [L]
        rw [hTPosEq, mul_assoc]
      have hMC : M_core = M_pos := by
        dsimp only [M_core, M_pos]
        simp only [mul_assoc]
      rw [hKT, hMC]
      exact conj_cancel_left_of_comm hLM
    rw [hCancelL]
    have hT₀B : T₀ * B = B * T₀ :=
      SchedBranchStitchGen.uTwistEffCut80_comm_uBarrelFast (truncFn c)
    have hTwEq : (C_tr * (S4 * T₀)) * B = selOra.uTwist c := by
      dsimp only [C_tr, S4, T₀, B]
      rw [uFusedTwistRestCut80_factor (truncFn c), hOra.hTw c]
    have hPass2Eq : pass2.uEff c = unitaryConj B (selOra.uPosPhase c) := by
      rw [hOra.hPosEq c]; rfl
    dsimp only [M_core]
    simp only [mul_assoc]
    exact SchedBranchStitchGen.pos_global_helper
      (by decide : 6 ≤ 80) (by decide : 22 ≤ 80) (le_refl 80)
      Q (selOra.uPosPhase c) (selOra.uTwist c) T₀ (pass3.uEff c) (pass2.uEff c)
      hP3Eq hPass2Eq
      (SchedBranchStitchGen.fullSysQftCoreIdeal80_comm_uBarrelFast
        selOra.hmPay qft hQft)
      hT₀B hTwEq
  rw [hGlobal]
set_option exponentiation.threshold 5000 in
theorem slot3Inner_momBranchP1_s1 (truncFn : Configuration → Configuration)
    {mWorkS1 tS1 t2Ctrl t2Cat t3Ctrl t3Cat tTwPair : ℕ}
    (s1 : Slot1HadCutLeafSpec mWorkS1 tS1)
    (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (tw : Slot3InnerHeldTwSpec tTwPair)
    (s3 : Slot3InnerSlot3InnerSpecS1 truncFn s1 tw t3Ctrl t3Cat)
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1.ora1 leaf2 s3.ora3)
    (c : Configuration) :
    (((slot3InnerBarrelTwistSpec288 tw).uTwistEff c)⁻¹ *
      (uMidBarrel3PassEff qft selOra
        (pass1SpecOfLe (by decide : 154 ≤ 330))
        s1.leaf330.toAlg
        (slot3InnerSlot3InnerLeafSpec330_s1 truncFn s3)
        (slot3InnerPass2LeafSpec330 truncFn leaf2)
        (pass3SpecOfLe (by decide : 133 ≤ 330)) c *
        (slot3InnerBarrelTwistSpec288 tw).uTwistEff c)).1 *
      slotBitProj (iSlot2 80) 1 =
    (selOra.uMomPhase c).1 * slotBitProj (iSlot2 80) 1 := by
  let P1 := slotBitProj (iSlot2 80) 1
  let pass1 := pass1SpecOfLe (by decide : 154 ≤ 330)
  let slot1 := s1.leaf330
  let slot3 := slot3InnerSlot3InnerLeafSpec330_s1 truncFn s3
  let pass2 := slot3InnerPass2LeafSpec330 truncFn leaf2
  let pass3 := pass3SpecOfLe (by decide : 133 ≤ 330)
  let twB := slot3InnerBarrelTwistSpec288 tw
  have hTwP1 : (twB.uTwistEff c).1 * P1 = P1 * (twB.uTwistEff c).1 := s3.hTwEffCommP1 c
  have hP1Comm : (pass1.uEff c).1 * P1 = P1 * (pass1.uEff c).1 := by
    dsimp only [pass1]; rw [pass1SpecOfLe_uEff]
    exact Pass1Leaf273.uPass1Eff_comm_slotBitProj (by decide) 1
  have hS1Comm : (slot1.uEff c).1 * P1 = P1 * (slot1.uEff c).1 := by
    dsimp only [slot1]; rw [s1.hLeaf330UEff c, s1.hUEffEq c]
    exact (momOracleConjInvTailHad3D_on_P0_and_comm_P1 s1.ora1 (by decide) c).2
  have hS3Comm : (slot3.uEff c).1 * P1 = P1 * (slot3.uEff c).1 := s3.hInnerCommP1 c
  have hPass2Id : (pass2.uEff c).1 * P1 = P1 :=
    SchedBranchStitchGen.unitaryConj_uBarrelFast_mul_proj_id
      (uBarrelFast_comm_high_wire (le_refl 80) (iSlot2 80) (by decide) 1) leaf2.hPosOnP1
  have hPass3Id : (pass3.uEff c).1 * P1 = P1 := by
    dsimp only [pass3]; rw [pass3SpecOfLe_uEff]
    exact Pass1Leaf273.uPass3Eff_mul_P1
  refine momBranchP1_of_tailId qft selOra twB pass1 slot1.toAlg slot3 pass2 pass3 c
    hTwP1 hP1Comm hS1Comm hS3Comm hPass2Id hPass3Id ?_
  have hP1EffEq : pass1.uEff c = (pass1SpecOfLe (le_refl 154)).uEff c := by
    dsimp only [pass1]; rw [pass1SpecOfLe_uEff, pass1SpecOfLe_uEff]
  have hS1EffEq : slot1.toAlg.uEff c = s1.leaf.uEff c := s1.hLeaf330UEff c
  have hS3EffEq : slot3.uEff c = s3.uInnerEff c := rfl
  have hTwEffEq : twB.uTwistEff c = tw.uTwEff c := rfl
  rw [hP1EffEq, hS1EffEq, hS3EffEq, hTwEffEq, s3.hMomPreSandwichP1 c]
  let s3RefEff : Unitary (2 ^ (fullSysCoreWires 80)) :=
    unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
      (coreUnitaryToFullSys (s3.ora3.uSlotEff c))
  have hS3RefComm : s3RefEff.1 * P1 = P1 * s3RefEff.1 :=
    (momOracleConjInvTailHad3D_on_P0_and_comm_P1 s3.ora3 (by decide) c).2
  let T_had := JunctionUncondHadTailCut.uTailHad3DCore *
    (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
      uXor32Core 80)
  let B := uBarrelFast (le_refl 80)
  let P1_mom := unitaryConj B
    (uSlot0LocalXorBit5 (le_refl 80)
      LiteralKineticAndMidpoint128.lambdaSlot0TeHi)
  let T_km := uKoffMomCore80 * T_had
  have hTHadComm : T_had.1 * P1 = P1 * T_had.1 := by
    dsimp only [T_had]; simp only [Submonoid.coe_mul]
    exact op_comm_mul (uTailHad3DCore_comm_slotBitProj (by decide) 1)
      (op_comm_mul (SchedBranchStitchGen.uTildeFullCore80_comm_slotBitProj _ 1)
        (uXor32Core80_comm_slotBitProj (by decide) 1))
  have hTKmComm : T_km.1 * P1 = P1 * T_km.1 := by
    dsimp only [T_km]; simp only [Submonoid.coe_mul]
    exact op_comm_mul (uKoffMomCore80_comm_slotBitProj (iSlot2 80) 1) hTHadComm
  have hP1MomComm : P1_mom.1 * P1 = P1 * P1_mom.1 :=
    SchedBranchStitchGen.unitaryConj_uBarrelFast_comm_slotBitProj (by decide) 1
      (uSlot0LocalXorBit5_comm_slotBitProj _ _ 1)
  have hS1LeafComm : (s1.leaf.uEff c).1 * P1 = P1 * (s1.leaf.uEff c).1 := by
    rw [s1.hUEffEq c]
    exact (momOracleConjInvTailHad3D_on_P0_and_comm_P1 s1.ora1 (by decide) c).2
  have hNComm : (s3RefEff * (s1.leaf.uEff c * P1_mom)).1 * P1 =
      P1 * (s3RefEff * (s1.leaf.uEff c * P1_mom)).1 := by
    simp only [Submonoid.coe_mul]
    exact op_comm_mul hS3RefComm (op_comm_mul hS1LeafComm hP1MomComm)
  have hMNEq : (s3RefEff * (s1.leaf.uEff c *
        (pass1SpecOfLe (le_refl 154)).uEff c)).1 * P1 =
      (s3RefEff * (s1.leaf.uEff c * P1_mom)).1 * P1 := by
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    rw [pass1SpecOfLe_uEff, Pass1Leaf273.uPass1Eff_mul_P1]
  have hTwEqKm : (uT0CoreOfTrunc truncFn c).1 * P1 = T_km.1 * P1 := by
    dsimp only [uT0CoreOfTrunc, uTwistEffHadCut80]
    rw [Submonoid.coe_mul, Matrix.mul_assoc, uTwistEffHadCut80_mul_P1 (truncFn c),
      hTHadComm, ← Matrix.mul_assoc, uKoffDiagCore_mul_P1 (truncFn c)]
    dsimp only [T_km]
    rw [Matrix.mul_assoc, ← hTHadComm, ← Matrix.mul_assoc, ← Submonoid.coe_mul]
  change (((uT0CoreOfTrunc truncFn c)⁻¹ *
      (s3RefEff * (s1.leaf.uEff c *
        ((pass1SpecOfLe (le_refl 154)).uEff c * uT0CoreOfTrunc truncFn c)))).1) * P1 = _
  rw [← mul_assoc (s1.leaf.uEff c)
      ((pass1SpecOfLe (le_refl 154)).uEff c) (uT0CoreOfTrunc truncFn c),
    ← mul_assoc s3RefEff _ (uT0CoreOfTrunc truncFn c),
    SchedBranchStitchGen.inv_mul_conj_eq_on_proj
      (PosMomSelectSandwich.slotBitProj_conjTranspose (iSlot2 80) 1)
      hTKmComm hTwEqKm hNComm hMNEq]
  have hCancelKm :
      T_km⁻¹ * ((s3RefEff * (s1.leaf.uEff c * P1_mom)) * T_km) =
        T_had⁻¹ * ((s3RefEff * (s1.leaf.uEff c * P1_mom)) * T_had) := by
    have hKP1Mom : uKoffMomCore80 * P1_mom = P1_mom * uKoffMomCore80 :=
      unitaryConj_comm_of_comm uKoffMomCore80_comm_uBarrelFast
        (uKoffMomCore80_comm_uSlot0LocalXorBit5 _)
    have hKS1 : uKoffMomCore80 * s1.leaf.uEff c =
        s1.leaf.uEff c * uKoffMomCore80 := by
      rw [s1.hUEffEq c]
      exact unitaryConj_comm_of_comm (group_comm_inv_of_comm uTailHad3DCore_comm_uKoffMomCore80)
        (comm_of_unitaryConj_eq
          (s1.hConjHighWire c uKoffMomCore80
            (fun q _ b ↦ uKoffMomCore80_comm_slotBitProj q b)))
    have hKS3 : uKoffMomCore80 * s3RefEff = s3RefEff * uKoffMomCore80 :=
      unitaryConj_comm_of_comm (group_comm_inv_of_comm uTailHad3DCore_comm_uKoffMomCore80)
        (comm_of_unitaryConj_eq
          (SchedBranchStitchGen.unitaryConj_uSlot3FullSys80_of_embed_rEC80_gen
            s3.ora3 s3.hSlot3CommEC c uKoffMomCoset654))
    dsimp only [T_km]
    exact conj_cancel_left_of_comm (comm_mul_of_comm hKS3 (comm_mul_of_comm hKS1 hKP1Mom)).symm
  rw [hCancelKm]
  have hGlobal :
      T_had⁻¹ * ((s3RefEff * (s1.leaf.uEff c * P1_mom)) * T_had) =
        selOra.uMomPhase c := by
    rw [← mul_assoc, ← unitaryConj_eq_inv_mul]
    dsimp only [T_had]
    rw [unitaryConj_mul_left, unitaryConj_mul_left]
    have hTailP1Mom :
        unitaryConj JunctionUncondHadTailCut.uTailHad3DCore P1_mom = P1_mom := by
      apply SchedBranchStitchGen.unitaryConj_of_comm
      dsimp only [P1_mom]
      rw [HoistedSwapSelectBridge.unitaryConj_val,
        CoinDispatchedBarrel288.uBarrelFast_conjTranspose]
      exact (op_comm_mul
        (op_comm_mul uTailHad3DCore_comm_uBarrelFast.symm
          (uTailHad3DCore_comm_uSlot0LocalXorBit5 _).symm)
        uTailHad3DCore_comm_uBarrelFast.symm).symm
    have hS1E : s1.leaf.uEff c =
        unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
          (coreUnitaryToFullSys (s1.ora1.uSlotEff c)) := s1.hUEffEq c
    rw [unitaryConj_mul JunctionUncondHadTailCut.uTailHad3DCore,
      unitaryConj_mul JunctionUncondHadTailCut.uTailHad3DCore,
      hS1E]
    dsimp only [s3RefEff]
    rw [unitaryConj_cancel_inv, unitaryConj_cancel_inv, hTailP1Mom]
    have hTildeP1Mom :
        unitaryConj
          (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80))
          P1_mom = P1_mom := by
      apply SchedBranchStitchGen.unitaryConj_of_comm
      dsimp only [P1_mom]
      rw [HoistedSwapSelectBridge.unitaryConj_val,
        CoinDispatchedBarrel288.uBarrelFast_conjTranspose]
      have hDiag :
          (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80)).1 *
          (uSlot0LocalXorBit5 (le_refl 80)
            LiteralKineticAndMidpoint128.lambdaSlot0TeHi).1 =
        (uSlot0LocalXorBit5 (le_refl 80)
          LiteralKineticAndMidpoint128.lambdaSlot0TeHi).1 *
          (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80)).1 := by
        rw [FusedPreDiagFromTwist288.uTildeFullCore_eq_dyadicDiag48
            (by decide : 6 ≤ 80),
          dyadicDiagUnitary_eq_diagonal,
          uSlot0LocalXorBit5_eq_diagonal,
          Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1; funext i; exact mul_comm _ _
      exact (op_comm_mul
        (op_comm_mul
          (uTildeFullCore_comm_uBarrelFast (le_refl 80)).symm
          hDiag.symm)
        (uTildeFullCore_comm_uBarrelFast (le_refl 80)).symm).symm
    have hTildeS3 :
        unitaryConj
          (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80))
          (coreUnitaryToFullSys (s3.ora3.uSlotEff c)) =
        coreUnitaryToFullSys (s3.ora3.uSlotEff c) := by
      unfold FusedPreDiagFromTwist288.uTildeFullCore
      exact SchedBranchStitchGen.unitaryConj_uSlot3FullSys80_of_embed_rEC80_gen
        s3.ora3 s3.hSlot3CommEC c
        FusedPreDiagFromTwist288.uTildeFull654
    rw [unitaryConj_mul (FusedPreDiagFromTwist288.uTildeFullCore _),
      unitaryConj_mul (FusedPreDiagFromTwist288.uTildeFullCore _),
      hTildeS3,
      s1.hConjHighWire c _
        (fun q _ b ↦ SchedBranchStitchGen.uTildeFullCore80_comm_slotBitProj q b),
      hTildeP1Mom]
    have hXorS3 :
        unitaryConj (uXor32Core 80) (coreUnitaryToFullSys (s3.ora3.uSlotEff c)) =
          coreUnitaryToFullSys (s3.ora3.uSlotEff c) := by
      rw [← FusedPreDiagFromTwist288.embed_bit5Flip654_eq_uXor32Core
        (by decide : 6 ≤ 80)]
      exact SchedBranchStitchGen.unitaryConj_uSlot3FullSys80_of_embed_rEC80_gen
        s3.ora3 s3.hSlot3CommEC c _
    have hXorP1Mom :
        unitaryConj (uXor32Core 80) P1_mom =
        unitaryConj B
          (coreUnitaryToFullSys
            (MomSlot0LocalAndMomCombine288.uSlot0Local (le_refl 80)
              LiteralKineticAndMidpoint128.lambdaSlot0TeHi)) := by
      dsimp only [P1_mom, B]
      rw [SchedBranchStitchGen.unitaryConj_uBarrelFast_uSlot0LocalXorBit5_eq]
      conv_lhs => arg 2; arg 1; rw [← NuclearTwistRealizes.uXor32Core_inv 80]
      exact unitaryConj_cancel_inv (uXor32Core 80) _
    rw [unitaryConj_mul (uXor32Core 80),
      unitaryConj_mul (uXor32Core 80),
      hXorS3,
      s1.hConjHighWire c _
        (fun q hq b ↦ uXor32Core80_comm_slotBitProj hq b),
      hXorP1Mom, hOra.hMom c]
    have hZ5 : (GeneralBetaAndAlphaTopEndpoint.zeroMomSlotOracle5
        80 48).uSlotEff c = 1 := rfl
    rw [hZ5, one_mul,
      SchedBranchStitchGen.coreUnitaryToFullSys_mul,
      SchedBranchStitchGen.coreUnitaryToFullSys_mul,
      unitaryConj_mul B,
      unitaryConj_mul B,
      SchedBranchStitchGen.unitaryConj_uBarrelFast_uSlot3FullSys80_gen
        s3.ora3 c,
      s1.hConjHighWire c B
        (fun q hq b ↦ uBarrelFast_comm_high_wire (le_refl 80) q hq b)]
  rw [hGlobal]

/-- Assembled `288`-wire `Barrel3PassMidSpec` for `Slot1HadCutLeafSpec` + `Slot3InnerHeldTwSpec`
  + `Slot3InnerSlot3InnerSpecS1`. -/
noncomputable def slot3InnerBarrelMidSpec288_s1 (truncFn : Configuration → Configuration)
    {mWorkS1 tS1 t2Ctrl t2Cat t3Ctrl t3Cat tTwPair : ℕ}
    (s1 : Slot1HadCutLeafSpec mWorkS1 tS1)
    (qft : FullSysQft654Bundle)
    (hQft : qft.uQft654 = DyadicQft64WalkCircuit220.coreQftHadamardIdeal654)
    (selOra : FullSysSelectOracleBundle 80 48)
    (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat)
    (tw : Slot3InnerHeldTwSpec tTwPair)
    (s3 : Slot3InnerSlot3InnerSpecS1 truncFn s1 tw t3Ctrl t3Cat)
    (hOra : SelectOraHypothesisOfS1Trunc truncFn selOra s1.ora1 leaf2 s3.ora3) :
    Barrel3PassMidSpec 288 qft selOra (slot3InnerBarrelTwistSpec288 tw) where
  pass1 := pass1SpecOfLe (by decide : 154 ≤ 330)
  slot1 := s1.leaf330.toAlg
  slot3 := slot3InnerSlot3InnerLeafSpec330_s1 truncFn s3
  pass2 := slot3InnerPass2LeafSpec330 truncFn leaf2
  pass3 := pass3SpecOfLe (by decide : 133 ≤ 330)
  hPosBranchP0 := slot3Inner_posBranchP0_s1 truncFn s1 qft hQft selOra leaf2 tw s3 hOra
  hMomBranchP1 := slot3Inner_momBranchP1_s1 truncFn s1 qft selOra leaf2 tw s3 hOra

/-- Full-width (`kFull80`) inner `Slot 3` unitary for `Slot3InnerSlot3InnerSpecS1`. -/
noncomputable def uSlot3FullInner_s1 (truncFn : Configuration → Configuration)
    {mWorkS1 tS1 tTwPair t3Ctrl t3Cat : ℕ} {s1 : Slot1HadCutLeafSpec mWorkS1 tS1}
    {tw : Slot3InnerHeldTwSpec tTwPair}
    (s3 : Slot3InnerSlot3InnerSpecS1 truncFn s1 tw t3Ctrl t3Cat) (c : Configuration) : Unitary
      (2 ^ kFull80) :=
  rSegFull.embedUnitary (rCTSeg.embedUnitary
    ((rCoreTopCatInCT 36 (by decide)).embedUnitary (s3.uInnerCatSub c)))

/-- Segment-level (`fullSysBEWires 80 + 48`) inner `Slot 3` unitary for
  `Slot3InnerSlot3InnerSpecS1`. -/
noncomputable def uSlot3SegInner_s1 (truncFn : Configuration → Configuration)
    {mWorkS1 tS1 tTwPair t3Ctrl t3Cat : ℕ} {s1 : Slot1HadCutLeafSpec mWorkS1 tS1}
    {tw : Slot3InnerHeldTwSpec tTwPair}
    (s3 : Slot3InnerSlot3InnerSpecS1 truncFn s1 tw t3Ctrl t3Cat) (c : Configuration) :
    Unitary (2 ^ (fullSysBEWires 80 + 48)) :=
  rCTSeg.embedUnitary ((rCoreTopCatInCT 36 (by decide)).embedUnitary (s3.uInnerCatSub c))

/-- Full-width (`kFull80`) 5-step Two-Stage Held-Stream `SELECT` unitary for parametric `s1`. -/
noncomputable def uTwoStageSelectHeldHeldTw_s1
    (truncFn : Fin 10 → Configuration → Configuration)
    {mWorkS1 : ℕ} {tS1 tTwPair t3Ctrl t3Cat : Fin 10 → ℕ}
    (s1 : ∀ j, Slot1HadCutLeafSpec mWorkS1 (tS1 j))
    (uFoldedFull : Fin 10 → Configuration → Unitary (2 ^ kFull80))
    (tw : ∀ j, Slot3InnerHeldTwSpec (tTwPair j))
    (s3 : ∀ j, Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (tw j) (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) : Unitary (2 ^ kFull80) :=
  (uTwHeldFullHeldTw (tw j) c)⁻¹ *
    (uFoldedFull j c * (uSlot3FullInner_s1 (truncFn j) (s3 j) c *
      (uSlot1FullS1 (s1 j) c * uTwHeldFullHeldTw (tw j) c)))

/-- Segment-level (`fullSysBEWires 80 + 48`) Two-Stage `SELECT` unitary for parametric `s1`. -/
noncomputable def uSelCatTwoStageHeldTw_s1
    (truncFn : Fin 10 → Configuration → Configuration)
    {mWorkS1 : ℕ} {tS1 tTwPair t3Ctrl t3Cat : Fin 10 → ℕ}
    (s1 : ∀ j, Slot1HadCutLeafSpec mWorkS1 (tS1 j))
    (uFoldedSeg : Fin 10 → Configuration → Unitary (2 ^ (fullSysBEWires 80 + 48)))
    (tw : ∀ j, Slot3InnerHeldTwSpec (tTwPair j))
    (s3 : ∀ j, Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (tw j) (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) : Unitary (2 ^ (fullSysBEWires 80 + 48)) :=
  (uTwSegHeldTw (tw j) c)⁻¹ *
    ((uFoldedSeg j c * (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c)) *
      uTwSegHeldTw (tw j) c)

/-- Segment-level Two-Stage `SingleCatSelectImpl` matching `uSelCatTwoStageHeldTw_s1` on
  `catState48`. -/
noncomputable def selImplSlot3InnerHeldTw_s1
    (truncFn : Fin 10 → Configuration → Configuration)
    {mBase mWorkS1 : ℕ}
    {B tS1 tTwPair tFoldCtrl tFoldCat t3Ctrl t3Cat : Fin 10 → ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (s1 : ∀ j, Slot1HadCutLeafSpec mWorkS1 (tS1 j))
    (selOra : Fin 10 → FullSysSelectOracleBundle 80 48)
    (folded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tFoldCtrl tFoldCat)
    (tw : ∀ j, Slot3InnerHeldTwSpec (tTwPair j))
    (s3 : ∀ j, Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (tw j) (t3Ctrl j) (t3Cat j))
    (hOra : ∀ j, SelectOraHypothesisOfS1Trunc (truncFn j) (selOra j) (s1 j).ora1
      (leaf2Slot3InnerOfTruncB (truncFn j) (B j) (hB6 j) (hB27 j)) (s3 j).ora3)
    (j : Fin 10) :
    SingleCatSelectImpl 80 48 coreQftHadamardPrunedBundle128 (selOra j) where
  uSelCat := uSelCatTwoStageHeldTw_s1 truncFn s1 folded.uFoldedSeg tw s3 j
  hIntertwinesSel c := by
    let twB := slot3InnerBarrelTwistSpec288 (tw j)
    let l2 := leaf2Slot3InnerOfTruncB (truncFn j) (B j) (hB6 j) (hB27 j)
    let mid288 := slot3InnerBarrelMidSpec288_s1 (truncFn j) (s1 j)
      coreQftHadamardPrunedBundle128
      coreQftHadamardPrunedBundle128_eq_ideal654
      (selOra j) l2 (tw j) (s3 j) (hOra j)
    have hPosEq : l2.uPosPhase0 = uPosPhase80Mod4OfB (B j) (hB6 j) (hB27 j) := rfl
    let s1L := (s1 j).leaf330
    let s3L := slot3InnerSlot3InnerLeafSpec330_s1 (truncFn j) (s3 j)
    have hS1Cat : (uSlot1SegS1 (s1 j) c).1 * catState48 =
        catState48 * (rCoreSeg.embedUnitary (s1L.uEff c)).1 := by
      have h1Eq : uSlot1SegS1 (s1 j) c = rCTSeg.embedUnitary (s1L.uCat c) := by
        dsimp only [s1L, uSlot1SegS1]; rw [(s1 j).hLeaf330UCat c]
      rw [h1Eq]; unfold catState48
      exact mul_catOp_of_intertwinesCat (intertwinesCat_ctLeafSpec s1L c)
    have hS3Cat : (uSlot3SegInner_s1 (truncFn j) (s3 j) c).1 * catState48 =
        catState48 * (rCoreSeg.embedUnitary (s3L.uEff c)).1 := by
      have h3Eq : uSlot3SegInner_s1 (truncFn j) (s3 j) c = rCTSeg.embedUnitary (s3L.uCat c) := rfl
      rw [h3Eq]; unfold catState48
      exact mul_catOp_of_intertwinesCat (intertwinesCat_ctLeafAlgSpec s3L c)
    have hPush : ∀ F : Unitary (2 ^ (fullSysBEWires 80 + 48)),
        (F * (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c)).1 * catState48 =
          (F.1 * catState48) *
            ((rCoreSeg.embedUnitary (s3L.uEff c)).1 * (rCoreSeg.embedUnitary (s1L.uEff c)).1) := by
      intro F
      calc (F * (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c)).1 * catState48
        _ = F.1 *
          ((uSlot3SegInner_s1 (truncFn j) (s3 j) c).1 * ((uSlot1SegS1 (s1 j) c).1 * catState48)) :=
          by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = F.1 * (((uSlot3SegInner_s1 (truncFn j) (s3 j) c).1 * catState48) *
              (rCoreSeg.embedUnitary (s1L.uEff c)).1) := by
              rw [hS1Cat]; simp only [Matrix.mul_assoc]
        _ = (F.1 * catState48) *
              ((rCoreSeg.embedUnitary (s3L.uEff c)).1 * (rCoreSeg.embedUnitary (s1L.uEff c)).1) :=
                by
              rw [hS3Cat]; simp only [Matrix.mul_assoc]
    have hMidBarrelEq :
        uMidBarrel3PassCat coreQftHadamardPrunedBundle128 (selOra j)
          mid288.pass1 mid288.slot1 mid288.slot3 mid288.pass2 mid288.pass3 c =
        uFoldedPass123Seg coreQftHadamardPrunedBundle128 (selOra j) l2.uPosPhase0 *
          (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c) := by
      have hP2Cat : rCTSeg.embedUnitary (mid288.pass2.uCat c) =
          rCoreSeg.embedUnitary (unitaryConj (uBarrelFast (le_refl 80)) l2.uPosPhase0) := by
        have hCTCore : rCTSeg.compose rCoreInCT80 = rCoreSeg :=
          concat_compose_rCoreInCT80 rCoreSeg rPG48Seg hCoreSeg_disj_PG48Seg
        dsimp only [mid288, slot3InnerBarrelMidSpec288_s1, slot3InnerPass2LeafSpec330]
        rw [← QRegister.embedUnitary_compose, hCTCore]
      have hP1Cat : mid288.pass1.uCat c = uPass1Cat := rfl
      have hS1CatEq : mid288.slot1.uCat c = (s1 j).leaf.uCat c := (s1 j).hLeaf330UCat c
      have hP3Cat : mid288.pass3.uCat c = uPass3Cat := rfl
      have hS3CatEq : mid288.slot3.uCat c =
          (rCoreTopCatInCT 36 (by decide)).embedUnitary ((s3 j).uInnerCatSub c) := rfl
      have hComm1_S1 :
          rCTSeg.embedUnitary ((s1 j).leaf.uCat c) * rCTSeg.embedUnitary uPass1Cat =
            rCTSeg.embedUnitary uPass1Cat * rCTSeg.embedUnitary ((s1 j).leaf.uCat c) :=
        (s1 j).hCommPass1 c
      have hComm1_S3 :
          rCTSeg.embedUnitary
            ((rCoreTopCatInCT 36 (by decide)).embedUnitary ((s3 j).uInnerCatSub c)) *
            rCTSeg.embedUnitary uPass1Cat =
          rCTSeg.embedUnitary uPass1Cat *
            rCTSeg.embedUnitary
              ((rCoreTopCatInCT 36 (by decide)).embedUnitary ((s3 j).uInnerCatSub c)) := by
        rw [← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul, (s3 j).hCommPass1 c]
      unfold uMidBarrel3PassCat uFoldedPass123Seg uSlot3SegInner_s1 uSlot1SegS1
      rw [hP3Cat, hP2Cat, hS3CatEq, hS1CatEq, hP1Cat, hComm1_S1,
        ← mul_assoc (rCTSeg.embedUnitary _) (rCTSeg.embedUnitary uPass1Cat), hComm1_S3]
      simp only [mul_assoc]
    have hMidCat :
        (folded.uFoldedSeg j c *
          (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c)).1 *
          catState48 =
        (uMidBarrel3PassCat coreQftHadamardPrunedBundle128 (selOra j)
          mid288.pass1 mid288.slot1 mid288.slot3 mid288.pass2 mid288.pass3 c).1 *
          catState48 := by
      rw [hMidBarrelEq, hPush, hPush, hPosEq, folded.hCat48 (selOra j) j c]
    have hMidCat80 :
        (folded.uFoldedSeg j c *
          (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c)).1 *
          ((rCat80.embedUnitary (U_cat_B_normalized 48)).1 *
            rCat80.basisOutcomeProjector 0) =
        (uMidBarrel3PassCat coreQftHadamardPrunedBundle128 (selOra j)
          mid288.pass1 mid288.slot1 mid288.slot3 mid288.pass2 mid288.pass3 c).1 *
          ((rCat80.embedUnitary (U_cat_B_normalized 48)).1 *
            rCat80.basisOutcomeProjector 0) := by
      simpa only [catState48] using hMidCat
    have hSand := sandwich_mul_catOp_eq_of_intertwinesCat
      ((uTwistSegOfSpec twB c)⁻¹).1
      (uMidBarrel3PassCat coreQftHadamardPrunedBundle128 (selOra j)
        mid288.pass1 mid288.slot1 mid288.slot3 mid288.pass2 mid288.pass3 c).1
      (folded.uFoldedSeg j c * (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c)).1
      (intertwinesCat_uTwistSegOfSpec twB c).1 hMidCat80
    simp only [← Submonoid.coe_mul] at hSand
    let refImpl := barrel3PassSelectImpl coreQftHadamardPrunedBundle128 (selOra j) twB mid288
    have hRefEq :
        (uTwistSegOfSpec twB c)⁻¹ *
          (uMidBarrel3PassCat coreQftHadamardPrunedBundle128 (selOra j)
              mid288.pass1 mid288.slot1 mid288.slot3 mid288.pass2 mid288.pass3 c *
            uTwistSegOfSpec twB c) =
        refImpl.uSelCat c := by
      change _ = (1 : Unitary _) * (_ * (_ * (_ * 1)))
      rw [one_mul, mul_one]
    have hTwEq : uTwistSegOfSpec twB c = uTwSegHeldTw (tw j) c :=
      uTwistSegOfSpec_slot3InnerBarrelTwistSpec288 (tw j) c
    rw [hRefEq, hTwEq] at hSand
    exact intertwinesCat_of_mul_catOp_eq (refImpl.hIntertwinesSel c) hSand

/-- Total `SELECT` `.T`-gate cap at `k_idle = 11` for parametric `Slot 1`: `tFold + tSlot1 + t3 +
  tTwPair`. -/
def tSelSlot3Inner_HeldTw_S1 (tFold tSlot1 t3 tTwPair : ℕ) : ℕ :=
  tFold + tSlot1 + t3 + tTwPair
private theorem uSlot3FullInner_s1_s1_comm_raw11 (truncFn : Configuration → Configuration)
    {mWorkS1 tS1 tTwPair t3Ctrl t3Cat : ℕ} {s1 : Slot1HadCutLeafSpec mWorkS1 tS1}
      {tw : Slot3InnerHeldTwSpec tTwPair}
    (s3 : Slot3InnerSlot3InnerSpecS1 truncFn s1 tw t3Ctrl t3Cat) (c : Configuration) :
    (uSlot3FullInner_s1 truncFn s3 c).1 * E_rawCtrl3Ext 11 (by decide) =
      E_rawCtrl3Ext 11 (by decide) * (uSlot3FullInner_s1 truncFn s3 c).1 ∧
    (uSlot3FullInner_s1 truncFn s3 c).1 * E_rawSegExt 11 (by decide) =
      E_rawSegExt 11 (by decide) * (uSlot3FullInner_s1 truncFn s3 c).1 := by
  refine ⟨?_,
    (topCat_comm_E_segExt11_and_rawSegExt11 (by decide : 11 + 36 ≤ 48)
      (s3.hLow3 c) (s3.hCommCtrl3 c)).2⟩
  have hSPG0 := (topCat_comm_streamPGIdle11 (by decide : 11 + 36 ≤ 48) (s3.hLow3 c)).2
  have hEqInCT :
      SelectCtrlStitch.rCoreTopCatInCTCtrl 36 (by decide) =
        rCoreTopCatInCT 36 (by decide) := rfl
  rw [hEqInCT] at hSPG0
  have hSPG : (uSlot3FullInner_s1 truncFn s3 c).1 * (E_rawStream42 * pPGIdleZero 11 (by decide)) =
      (E_rawStream42 * pPGIdleZero 11 (by decide)) * (uSlot3FullInner_s1 truncFn s3 c).1 := hSPG0
  have hCtrl : (uSlot3FullInner_s1 truncFn s3 c).1 * pCtrl3Zero =
      pCtrl3Zero * (uSlot3FullInner_s1 truncFn s3 c).1 := by
    unfold uSlot3FullInner_s1
    rw [← QRegister.embedUnitary_compose rCTSeg, ← QRegister.embedUnitary_compose rSegFull,
      SelectExtStitch.rSegFull_compose_rCoreTopCatInCT_eq 36 (by decide)]
    have hc := (CommutesWithReg.embedMatrix (rCoreTopCatFull 36 (by decide))
      (s3.hCommCtrl3 c)).comm_basisOutcomeProjector 0
    rwa [SelectExtStitch.rCoreTopCatFull_compose_rCtrl3 36 (by decide)] at hc
  have hComm : pPGIdleZero 11 (by decide) * pCtrl3Zero = pCtrl3Zero * pPGIdleZero 11 (by decide) :=
    basisOutcomeProjector_comm_any (rPGIdle 11 (by decide)) 0 rUnusedCtrl3Full 0
  have hRawEq : E_rawCtrl3Ext 11 (by decide) = (E_rawStream42 * pPGIdleZero 11 (by decide)) *
    pCtrl3Zero := by
    unfold E_rawCtrl3Ext; rw [Matrix.mul_assoc, hComm]
  rw [hRawEq, ← Matrix.mul_assoc, hSPG, Matrix.mul_assoc, hCtrl, ← Matrix.mul_assoc]
/-- `E_ctrl3Ext 11` and `E_segExt 11` intertwining theorem for `uTwoStageSelectHeldTw`. -/
theorem uTwoStageSelectHeldHeldTw_s1_intertwines_11
    (truncFn : Fin 10 → Configuration → Configuration)
    {mBase mWorkS1 : ℕ}
    {B tS1 tTwPair tFoldCtrl tFoldCat t3Ctrl t3Cat : Fin 10 → ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (s1 : ∀ j, Slot1HadCutLeafSpec mWorkS1 (tS1 j))
    (folded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tFoldCtrl tFoldCat)
    (tw : ∀ j, Slot3InnerHeldTwSpec (tTwPair j))
    (s3 : ∀ j, Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (tw j) (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) :
    ((uTwoStageSelectHeldHeldTw_s1 truncFn s1 folded.uFoldedCtrlFull tw s3 j c).1 *
      E_ctrl3Ext 11 (by decide) =
      E_ctrl3Ext 11 (by decide) *
        (rAct0.embedUnitary (rSegOrig.embedUnitary
          (uSelCatTwoStageHeldTw_s1 truncFn s1 folded.uFoldedSeg tw s3 j c))).1) ∧
    ((uTwoStageSelectHeldHeldTw_s1 truncFn s1 folded.uFoldedCatFull tw s3 j c).1 *
      E_segExt 11 (by decide) =
      E_segExt 11 (by decide) *
        (rAct0.embedUnitary (rSegOrig.embedUnitary
          (uSelCatTwoStageHeldTw_s1 truncFn s1 folded.uFoldedSeg tw s3 j c))).1) := by
  let F_seg : Unitary (2 ^ kFull80) := rSegFull.embedUnitary (folded.uFoldedSeg j c)
  let T_0 : Unitary (2 ^ kFull80) :=
    (rCoreTopCatFull 37 (by decide)).embedUnitary ((tw j).uTwCatSub37 c)
  have hT0Ctrl : T_0.1 * pCtrl3Zero = pCtrl3Zero * T_0.1 := by
    have hc := (CommutesWithReg.embedMatrix (rCoreTopCatFull 37 (by decide))
      ((tw j).hCommCtrl3Cat c)).comm_basisOutcomeProjector 0
    rwa [SelectExtStitch.rCoreTopCatFull_compose_rCtrl3 37 (by decide)] at hc
  have hT0Idle : T_0.1 * pPGIdleZero 11 (by decide) = pPGIdleZero 11 (by decide) * T_0.1 :=
    (CommutesWithReg.of_disjoint
      (SelectHoistLemmas.rCoreTopCatFull_disj_rPGIdle 11 37 (by decide))
      ((tw j).uTwCatSub37 c).1).comm_basisOutcomeProjector 0
  have hT0Slk : T_0.1 * pSlack3Zero = pSlack3Zero * T_0.1 :=
    embed_rCoreTopCatFull37_comm_pSlack3Zero _
  have hT0InvCtrl : (T_0⁻¹).1 * pCtrl3Zero = pCtrl3Zero * (T_0⁻¹).1 :=
    SelectHoistLemmas.unitary_inv_comm_selfAdj
      (by unfold pCtrl3Zero; exact QRegister.basisOutcomeProjector_conjTranspose _ 0) hT0Ctrl
  have hT0InvIdle : (T_0⁻¹).1 * pPGIdleZero 11 (by decide) = pPGIdleZero 11 (by decide) *
    (T_0⁻¹).1 :=
    SelectHoistLemmas.unitary_inv_comm_selfAdj
      (by unfold pPGIdleZero; exact QRegister.basisOutcomeProjector_conjTranspose _ 0) hT0Idle
  have hT0InvSlk : (T_0⁻¹).1 * pSlack3Zero = pSlack3Zero * (T_0⁻¹).1 :=
    SelectHoistLemmas.unitary_inv_comm_selfAdj
      (by unfold pSlack3Zero; exact QRegister.basisOutcomeProjector_conjTranspose _ 0) hT0Slk
  have hThInvCtrl :
      ((uTwHeldFullHeldTw (tw j) c)⁻¹).1 * E_rawCtrl3Ext 11 (by decide) =
        E_ctrl3Ext 11 (by decide) * (T_0⁻¹).1 := by
    have hThInv : ((uTwHeldFullHeldTw (tw j) c)⁻¹).1 * E_rawStream42 = E_stream42 * (T_0⁻¹).1 :=
      inv_intertwine_lemma _ _ E_stream42 E_rawStream42 ((tw j).hTwStreamE c)
    unfold E_rawCtrl3Ext E_ctrl3Ext
    calc ((uTwHeldFullHeldTw (tw j) c)⁻¹).1 *
      (E_rawStream42 * (pCtrl3Zero * pPGIdleZero 11 (by decide)))
      _ = (((uTwHeldFullHeldTw (tw j) c)⁻¹).1 * E_rawStream42) *
        (pCtrl3Zero * pPGIdleZero 11 (by decide)) := by
            simp only [Matrix.mul_assoc]
      _ = E_stream42 * (((T_0⁻¹).1 * pCtrl3Zero) * pPGIdleZero 11 (by decide)) := by
            rw [hThInv]; simp only [Matrix.mul_assoc]
      _ = E_stream42 * (pCtrl3Zero * ((T_0⁻¹).1 * pPGIdleZero 11 (by decide))) := by
            rw [hT0InvCtrl]; simp only [Matrix.mul_assoc]
      _ = (E_stream42 * (pCtrl3Zero * pPGIdleZero 11 (by decide))) * (T_0⁻¹).1 := by
            rw [hT0InvIdle]; simp only [Matrix.mul_assoc]
  have hRawSegEq : E_rawSegExt 11 (by decide) = E_rawCtrl3Ext 11 (by decide) * pSlack3Zero := by
    unfold E_rawSegExt E_rawCtrl3Ext
    rw [pExt6IdleZero_eq_mul, pExt6Zero_eq_mul]
    have hc : pSlack3Zero * pPGIdleZero 11 (by decide) = pPGIdleZero 11 (by decide) * pSlack3Zero :=
      basisOutcomeProjector_comm_any rSlack3Full 0 (rPGIdle 11 (by decide)) 0
    simp only [Matrix.mul_assoc, hc]
  have hSegEq : E_segExt 11 (by decide) = E_ctrl3Ext 11 (by decide) * pSlack3Zero :=
    Leaf4Ext48TopStitch.E_segExt_eq_E_ctrl3Ext_mul_pSlack3 11 (by decide)
  have hThInvSeg :
      ((uTwHeldFullHeldTw (tw j) c)⁻¹).1 * E_rawSegExt 11 (by decide) =
        E_segExt 11 (by decide) * (T_0⁻¹).1 := by
    rw [hRawSegEq, hSegEq, ← Matrix.mul_assoc, hThInvCtrl, Matrix.mul_assoc, hT0InvSlk,
      ← Matrix.mul_assoc]
  have hRhsEq :
      rAct0.embedUnitary (rSegOrig.embedUnitary
        (uSelCatTwoStageHeldTw_s1 truncFn s1 folded.uFoldedSeg tw s3 j c)) =
      T_0⁻¹ * ((F_seg * (uSlot3FullInner_s1 (truncFn j) (s3 j) c * uSlot1FullS1 (s1 j) c)) * T_0) :=
        by
    dsimp only [uSelCatTwoStageHeldTw_s1, T_0, F_seg, uSlot3FullInner_s1, uSlot1FullS1,
      uTwSegHeldTw, uSlot3SegInner_s1, uSlot1SegS1]
    rw [← QRegister.embedUnitary_compose,
      ← SelectHoistLemmas.rSegFull_eq_rAct0_compose_rSegOrig]
    have hTwEq : rSegFull.embedUnitary
        (rCTSeg.embedUnitary ((rCoreTopCatInCT 37 (by decide)).embedUnitary
          ((tw j).uTwCatSub37 c))) =
        (rCoreTopCatFull 37 (by decide)).embedUnitary ((tw j).uTwCatSub37 c) := by
      rw [← QRegister.embedUnitary_compose rSegFull,
        ← QRegister.embedUnitary_compose (rSegFull.compose rCTSeg),
        QRegister.compose_assoc,
        SelectHoistLemmas.rSegFull_compose_rCTSeg_rCoreTopCatInCT 37 (by decide)]
    simp only [QRegister.embedUnitary_mul, ← embedUnitary_inv_symm rSegFull, hTwEq]
  have hInter5 : ∀ (uFold : Fin 10 → Configuration → Unitary (2 ^ kFull80))
      (E E_raw : Operator (2 ^ kFull80)),
      (uTwHeldFullHeldTw (tw j) c).1 * E = E_raw * T_0.1 →
      (uSlot1FullS1 (s1 j) c).1 * E_raw = E_raw * (uSlot1FullS1 (s1 j) c).1 →
      (uSlot3FullInner_s1 (truncFn j) (s3 j) c).1 * E_raw =
        E_raw * (uSlot3FullInner_s1 (truncFn j) (s3 j) c).1 →
      (uFold j c).1 * E_raw = E_raw * F_seg.1 →
      ((uTwHeldFullHeldTw (tw j) c)⁻¹).1 * E_raw = E * (T_0⁻¹).1 →
      (uTwoStageSelectHeldHeldTw_s1 truncFn s1 uFold tw s3 j c).1 * E =
        E * (rAct0.embedUnitary (rSegOrig.embedUnitary
          (uSelCatTwoStageHeldTw_s1 truncFn s1 folded.uFoldedSeg tw s3 j c))).1 := by
    intro uFold E E_raw h0 h1 h2 h3 h4
    rw [hRhsEq]
    unfold uTwoStageSelectHeldHeldTw_s1
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    rw [h0, ← Matrix.mul_assoc (uSlot1FullS1 _ _).1, h1, Matrix.mul_assoc E_raw,
      ← Matrix.mul_assoc (uSlot3FullInner_s1 _ _ _).1, h2, Matrix.mul_assoc E_raw,
      ← Matrix.mul_assoc (uFold _ _).1, h3, Matrix.mul_assoc E_raw,
      ← Matrix.mul_assoc ((uTwHeldFullHeldTw _ _)⁻¹).1, h4]
    simp only [Matrix.mul_assoc]
  exact ⟨hInter5 folded.uFoldedCtrlFull _ _
      (uTwHeldFullHeldTw_intertwines_ctrl3Ext11 (tw j) c)
      (uSlot1FullS1_comm_raw11 (s1 j) c).1
      (uSlot3FullInner_s1_s1_comm_raw11 (truncFn j) (s3 j) c).1
      (folded.hInterRawCtrl j c) hThInvCtrl,
    hInter5 folded.uFoldedCatFull _ _
      (uTwHeldFullHeldTw_intertwines_segExt11 (tw j) c)
      (uSlot1FullS1_comm_raw11 (s1 j) c).2
      (uSlot3FullInner_s1_s1_comm_raw11 (truncFn j) (s3 j) c).2
      (folded.hInterRawCat j c) hThInvSeg⟩
theorem selImplSlot3InnerHeldTw_s1_hSelSlack010
    (truncFn : Fin 10 → Configuration → Configuration)
    {mBase mWorkS1 : ℕ}
    {B tS1 tTwPair tFoldCtrl tFoldCat t3Ctrl t3Cat : Fin 10 → ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (s1 : ∀ j, Slot1HadCutLeafSpec mWorkS1 (tS1 j))
    (selOra : Fin 10 → FullSysSelectOracleBundle 80 48)
    (folded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tFoldCtrl tFoldCat)
    (tw : ∀ j, Slot3InnerHeldTwSpec (tTwPair j))
    (s3 : ∀ j, Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (tw j) (t3Ctrl j) (t3Cat j))
    (hOra : ∀ j,
      SelectOraHypothesisOfS1Trunc (truncFn j) (selOra j) (s1 j).ora1
      (leaf2Slot3InnerOfTruncB (truncFn j) (B j) (hB6 j) (hB27 j)) (s3 j).ora3)
    (j : Fin 10) (c : Configuration) :
    (rSegOrig.embedUnitary
      ((selImplSlot3InnerHeldTw_s1 truncFn s1 selOra folded tw s3 hOra j).uSelCat c)).1 *
      Leaf4Ext48TopStitch.pCoinSlack010Orig =
      Leaf4Ext48TopStitch.pCoinSlack010Orig := by
  rw [show (selImplSlot3InnerHeldTw_s1 truncFn s1 selOra folded tw s3 hOra j).uSelCat c =
    uSelCatTwoStageHeldTw_s1 truncFn s1 folded.uFoldedSeg tw s3 j c from rfl]
  have hMidSlack :
      (folded.uFoldedSeg j c * (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c)).1 *
        pCoinSlack010Seg = pCoinSlack010Seg := by
    simp only [uSlot1SegS1, uSlot3SegInner_s1, Submonoid.coe_mul, Matrix.mul_assoc]
    rw [(s1 j).hMulSlack010 c, (s3 j).hSlack c, folded.hSlackSeg j c]
  have hTwComm :
      (uTwSegHeldTw (tw j) c).1 * pCoinSlack010Seg =
        pCoinSlack010Seg * (uTwSegHeldTw (tw j) c).1 :=
    (tw j).hSlack010 c
  have hUSelEq :
      uSelCatTwoStageHeldTw_s1 truncFn s1 folded.uFoldedSeg tw s3 j c =
        (uTwSegHeldTw (tw j) c)⁻¹ *
          ((folded.uFoldedSeg j c *
            (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c)) *
            uTwSegHeldTw (tw j) c) := rfl
  rw [hUSelEq]
  exact hoistedSelect_mul_pCoinSlack010Orig _ _ hTwComm hMidSlack
theorem selImplSlot3InnerHeldTw_s1_hSelIdle
    (truncFn : Fin 10 → Configuration → Configuration)
    {mBase mWorkS1 : ℕ}
    {B tS1 tTwPair tFoldCtrl tFoldCat t3Ctrl t3Cat : Fin 10 → ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (s1 : ∀ j, Slot1HadCutLeafSpec mWorkS1 (tS1 j))
    (selOra : Fin 10 → FullSysSelectOracleBundle 80 48)
    (folded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tFoldCtrl tFoldCat)
    (tw : ∀ j, Slot3InnerHeldTwSpec (tTwPair j))
    (s3 : ∀ j, Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (tw j) (t3Ctrl j) (t3Cat j))
    (hOra : ∀ j,
      SelectOraHypothesisOfS1Trunc (truncFn j) (selOra j) (s1 j).ora1
      (leaf2Slot3InnerOfTruncB (truncFn j) (B j) (hB6 j) (hB27 j)) (s3 j).ora3)
    (j : Fin 10) (c : Configuration) :
    CommutesWithReg (rPGIdleOrig 11 hkIdle)
      (rSegOrig.embedUnitary
        ((selImplSlot3InnerHeldTw_s1 truncFn s1 selOra folded tw s3 hOra j).uSelCat c)).1 := by
  rw [show (selImplSlot3InnerHeldTw_s1 truncFn s1 selOra folded tw s3 hOra j).uSelCat c =
    uSelCatTwoStageHeldTw_s1 truncFn s1 folded.uFoldedSeg tw s3 j c from rfl]
  have hIdle1 :
      CommutesWithReg (rPGIdleOrig 11 hkIdle)
        (rSegOrig.embedUnitary (uSlot1SegS1 (s1 j) c)).1 := by
    have hCTCore : rCTSeg.compose rCoreInCT80 = rCoreSeg :=
      concat_compose_rCoreInCT80 rCoreSeg rPG48Seg hCoreSeg_disj_PG48Seg
    unfold uSlot1SegS1
    rw [(s1 j).hUCatEqCore c, ← QRegister.embedUnitary_compose rCTSeg, hCTCore]
    exact SelectHoistLemmas.commutesWithReg_rPGIdleOrig_rCoreSeg
      11 hkIdle _
  have hIdle3 :
      CommutesWithReg (rPGIdleOrig 11 hkIdle)
        (rSegOrig.embedUnitary (uSlot3SegInner_s1 (truncFn j) (s3 j) c)).1 := by
    unfold uSlot3SegInner_s1
    exact SelectHoistLemmas.commutesWithReg_rPGIdleOrig_rCTSeg_catSlice_ge
      11 36 hkIdle
      (rTopCatSlice 36 48 (by decide))
      (fun t ↦ by simp [rTopCatSlice]; omega)
      _ ((s3 j).uInnerCatSub c)
  have hMidIdle :
      CommutesWithReg (rPGIdleOrig 11 hkIdle)
        (rSegOrig.embedUnitary
          (folded.uFoldedSeg j c *
            (uSlot3SegInner_s1 (truncFn j) (s3 j) c * uSlot1SegS1 (s1 j) c))).1 := by
    rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
      Submonoid.coe_mul, Submonoid.coe_mul]
    exact (folded.hIdle11Seg j c).mul (hIdle3.mul hIdle1)
  exact commutesWithReg_rPGIdleOrig_hoistedSelect 11 37 hkIdle (by decide : 11 + 37 ≤ 48)
    ((tw j).uTwCatSub37 c) _ hMidIdle
/-- 5-step right-nested `DynamicCircuit.seq` combinator. -/
def dSeq5 {Var : Type} {n : ℕ}
    (d₀ d₁ d₂ d₃ d₄ : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq d₀ (.seq d₁ (.seq d₂ (.seq d₃ d₄)))

private theorem dSeq5_count {Var : Type} {n a : ℕ}
    (d₀ d₁ d₂ d₃ d₄ : DynamicCircuit Var n) (g : PrimitiveGate a) :
    (dSeq5 d₀ d₁ d₂ d₃ d₄).count g =
      d₀.count g + (d₁.count g + (d₂.count g + (d₃.count g + d₄.count g))) := rfl

private theorem count_dSeq5_toff {Var : Type} {n : ℕ}
    {d₀ d₁ d₂ d₃ d₄ : DynamicCircuit Var n}
    (h04 : d₀.count .TOFF = 0 ∧ d₄.count .TOFF = 0) (h1 : d₁.count .TOFF = 0)
    (h2 : d₂.count .TOFF = 0) (h3 : d₃.count .TOFF = 0) :
    (dSeq5 d₀ d₁ d₂ d₃ d₄).count .TOFF = 0 := by
  rw [dSeq5_count, h04.1, h1, h2, h3, h04.2]

private theorem count_dSeq5_t_le {Var : Type} {n : ℕ}
    {d₀ d₁ d₂ d₃ d₄ : DynamicCircuit Var n}
    {tFold tLeaf tS1 t3 tTwPair tTot : ℕ} (hTw : d₀.count .T + d₄.count .T ≤ tTwPair)
    (h1 : d₁.count .T ≤ tLeaf) (htS1 : tLeaf ≤ tS1) (h2 : d₂.count .T ≤ t3)
    (h3 : d₃.count .T ≤ tFold) (hTot : tFold + tS1 + t3 + tTwPair ≤ tTot) :
    (dSeq5 d₀ d₁ d₂ d₃ d₄).count .T ≤ tTot := by
  rw [dSeq5_count]
  omega

private theorem dSeq5_embed_realizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var]
    {kAct n : ℕ} [NeZero (2 ^ n)] (rAct : QRegister kAct n)
    {E₀ E₁ E₂ E₃ E₄ V₀ V₁ V₂ V₃ : Operator (2 ^ n)}
    {U₀ U₁ U₂ U₃ U₄ : Unitary (2 ^ kAct)} {d₀ d₁ d₂ d₃ d₄ : DynamicCircuit Var n}
    (hI0 : (rAct.embedUnitary U₀).1 * E₀ = E₁ * V₀)
    (hI1 : (rAct.embedUnitary U₁).1 * E₁ = E₂ * V₁)
    (hI2 : (rAct.embedUnitary U₂).1 * E₂ = E₃ * V₂)
    (hI3 : (rAct.embedUnitary U₃).1 * E₃ = E₄ * V₃)
    (p0 : RealizesOnProj E₀ (rAct.embedUnitary U₀) d₀)
    (p1 : RealizesOnProj E₁ (rAct.embedUnitary U₁) d₁)
    (p2 : RealizesOnProj E₂ (rAct.embedUnitary U₂) d₂)
    (p3 : RealizesOnProj E₃ (rAct.embedUnitary U₃) d₃)
    (p4 : RealizesOnProj E₄ (rAct.embedUnitary U₄) d₄) :
    RealizesOnProj E₀
      (rAct.embedUnitary (U₄ * (U₃ * (U₂ * (U₁ * U₀)))))
      (dSeq5 d₀ d₁ d₂ d₃ d₄) := by
  have hChain := p0.seq_intertwine hI0 (p1.seq_intertwine hI1
    (p2.seq_intertwine hI2 (p3.seq_intertwine hI3 p4)))
  have hMul : (((rAct.embedUnitary U₄ * rAct.embedUnitary U₃) *
      rAct.embedUnitary U₂) * rAct.embedUnitary U₁) * rAct.embedUnitary U₀ =
      rAct.embedUnitary (U₄ * (U₃ * (U₂ * (U₁ * U₀)))) := by
    simp only [← QRegister.embedUnitary_mul, _root_.mul_assoc]
  rwa [hMul] at hChain

/-- 5-step `Ctrl`-branch Two-Stage `SELECT` dynamic circuit at arbitrary `142 ≤ mWork` (`k_idle =
  11`,
`rWB_ctrl : QRegister (mWork + 11) n`, `0 TOFF`). -/
noncomputable def dSlot3InnerTwoStageSelectCtrl_s1_mWork_11
    {mWork : ℕ} {tS1 : Fin 10 → ℕ} (s1 : ∀ j, Slot1HadCutLeafSpec mWork (tS1 j))
    (truncFn : Fin 10 → Configuration → Configuration)
    {B tTwBase tTwPairCtrl tTwPairCat tBaseFoldCtrl tBaseFoldCat
     tFoldCtrl tFoldCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {mBase : ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j,
      Slot3InnerGenAsymHeldTwSpec_mWork mWork (baseTw j).uTwHeldSub37 (tTwPairCtrl j)
      (tTwPairCat j))
    (baseS3 : ∀ j,
      Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j,
      Slot3InnerSlot3InnerCircuitSpec_mWork mWork (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  let rWBCtrl : QRegister (mWork + 11) n := rWorkCtrlTwist 11 (by decide) rAct rWork hDisj
  let rTwSub := rAct.compose (rCoreTopCatSum42Full 37 (by decide))
  let hTwW := rTwAct_disj_rWTw (by decide : 11 + 37 ≤ 48) rAct rWork hDisj
  let rSeg := rAct.compose rSegFull
  let hSW := hDisj.compose_left rSegFull
  let rC := rSeg.compose rCoreSeg
  let rP := rSeg.compose rPG48Seg
  let hCP := disjointWires_compose_of_disjoint rSeg hCoreSeg_disj_PG48Seg
  let hCW := hSW.compose_left rCoreSeg
  let hPW := hSW.compose_left rPG48Seg
  let rSub3 := rAct.compose (rCoreTopCatFull 36 (by decide))
  let hSub3W := rSub3Act_disj_rWorkCtrlTwist11 (by decide : 11 + 36 ≤ 48) rAct rWork hDisj
  dSeq5 ((asymTw j).dTwCtrl c v rTwSub rWBCtrl hTwW)
    (((s1 j).leaf).dLeaf c v rC rP rWork hCP hCW hPW)
    ((s3Circ j).dInnerCtrl c v rSub3 rWBCtrl hSub3W) (foldedCirc.dFoldedCtrl j c v rAct rWork hDisj)
    ((asymTw j).dTwCtrlInv c v rTwSub rWBCtrl hTwW)
/-- 5-step `Cat`-branch Two-Stage `SELECT` dynamic circuit at arbitrary `142 ≤ mWork` (`k_idle =
  11`,
`rWB_cat : QRegister (mWork + 14) n`, `0 TOFF`). -/
noncomputable def dSlot3InnerTwoStageSelectCat_s1_mWork_11
    {mWork : ℕ} {tS1 : Fin 10 → ℕ} (s1 : ∀ j, Slot1HadCutLeafSpec mWork (tS1 j))
    (truncFn : Fin 10 → Configuration → Configuration)
    {B tTwBase tTwPairCtrl tTwPairCat tBaseFoldCtrl tBaseFoldCat
     tFoldCtrl tFoldCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {mBase : ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j,
      Slot3InnerGenAsymHeldTwSpec_mWork mWork (baseTw j).uTwHeldSub37 (tTwPairCtrl j)
      (tTwPairCat j))
    (baseS3 : ∀ j,
      Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j,
      Slot3InnerSlot3InnerCircuitSpec_mWork mWork (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  let rWBCat : QRegister (mWork + 14) n := rWorkSlackIdle 11 (by decide) rAct rWork hDisj
  let rTwSub := rAct.compose (rCoreTopCatSum42Full 37 (by decide))
  let hTwW := rTwAct_disj_rWorkSlackIdle11 (by decide : 11 + 37 ≤ 48) rAct rWork hDisj
  let rSeg := rAct.compose rSegFull
  let hSW := hDisj.compose_left rSegFull
  let rC := rSeg.compose rCoreSeg
  let rP := rSeg.compose rPG48Seg
  let hCP := disjointWires_compose_of_disjoint rSeg hCoreSeg_disj_PG48Seg
  let hCW := hSW.compose_left rCoreSeg
  let hPW := hSW.compose_left rPG48Seg
  let rSub3 := rAct.compose (rCoreTopCatFull 36 (by decide))
  let hSub3W := rSub3Act_disj_rWorkSlackIdle11 (by decide : 11 + 36 ≤ 48) rAct rWork hDisj
  dSeq5 ((asymTw j).dTwCat c v rTwSub rWBCat hTwW)
    (((s1 j).leaf).dLeaf c v rC rP rWork hCP hCW hPW)
    ((s3Circ j).dInnerCat c v rSub3 rWBCat hSub3W) (foldedCirc.dFoldedCat j c v rAct rWork hDisj)
    ((asymTw j).dTwCatInv c v rTwSub rWBCat hTwW)
theorem count_dSlot3InnerTwoStageSelectCtrl_s1_mWork_11_toff
    {mWork : ℕ} {tS1 : Fin 10 → ℕ} (s1 : ∀ j, Slot1HadCutLeafSpec mWork (tS1 j))
    (truncFn : Fin 10 → Configuration → Configuration)
    {B tTwBase tTwPairCtrl tTwPairCat tBaseFoldCtrl tBaseFoldCat
     tFoldCtrl tFoldCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {mBase : ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j,
      Slot3InnerGenAsymHeldTwSpec_mWork mWork (baseTw j).uTwHeldSub37 (tTwPairCtrl j)
      (tTwPairCat j))
    (baseS3 : ∀ j,
      Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j,
      Slot3InnerSlot3InnerCircuitSpec_mWork mWork (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    (dSlot3InnerTwoStageSelectCtrl_s1_mWork_11 s1 truncFn baseFolded foldedCirc baseTw asymTw baseS3
      s3Circ
      j c v rAct rWork hDisj).count .TOFF = 0 := by
  exact count_dSeq5_toff ((asymTw j).hToffPairCtrl c _ _ _ _)
    (((s1 j).leaf).hToff _ _ _ _ _ _ _ _) ((s3Circ j).hToffCtrl _ _ _ _ _)
    (foldedCirc.hToffCtrl _ _ _ _ _ _)
theorem count_dSlot3InnerTwoStageSelectCtrl_s1_mWork_11_t_le
    {mWork : ℕ} {tS1 : Fin 10 → ℕ} (s1 : ∀ j, Slot1HadCutLeafSpec mWork (tS1 j))
    (truncFn : Fin 10 → Configuration → Configuration)
    {B tTwBase tTwPairCtrl tTwPairCat tBaseFoldCtrl tBaseFoldCat
     tFoldCtrl tFoldCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {mBase : ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j,
      Slot3InnerGenAsymHeldTwSpec_mWork mWork (baseTw j).uTwHeldSub37 (tTwPairCtrl j)
      (tTwPairCat j))
    (baseS3 : ∀ j,
      Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j,
      Slot3InnerSlot3InnerCircuitSpec_mWork mWork (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    (dSlot3InnerTwoStageSelectCtrl_s1_mWork_11 s1 truncFn baseFolded foldedCirc baseTw asymTw baseS3
      s3Circ
      j c v rAct rWork hDisj).count .T ≤
      tSelSlot3Inner_HeldTw_S1 (tFoldCtrl j) (tS1 j) (t3Ctrl j) (tTwPairCtrl j) := by
  exact count_dSeq5_t_le
    ((asymTw j).hTPairCtrl c v (rAct.compose (rCoreTopCatSum42Full 37 (by decide)))
      (rWorkCtrlTwist 11 (by decide) rAct rWork hDisj)
      (rTwAct_disj_rWTw (by decide : 11 + 37 ≤ 48) rAct rWork hDisj))
    (((s1 j).leaf).hT c v ((rAct.compose rSegFull).compose rCoreSeg)
      ((rAct.compose rSegFull).compose rPG48Seg) rWork
      (disjointWires_compose_of_disjoint (rAct.compose rSegFull) hCoreSeg_disj_PG48Seg)
      ((hDisj.compose_left rSegFull).compose_left rCoreSeg)
      ((hDisj.compose_left rSegFull).compose_left rPG48Seg)) (s1 j).htLeaf
    ((s3Circ j).hTCtrl c v (rAct.compose (rCoreTopCatFull 36 (by decide)))
      (rWorkCtrlTwist 11 (by decide) rAct rWork hDisj)
      (rSub3Act_disj_rWorkCtrlTwist11 (by decide : 11 + 36 ≤ 48) rAct rWork hDisj))
    (foldedCirc.hTCtrl j c v rAct rWork hDisj) (by
      unfold tSelSlot3Inner_HeldTw_S1
      omega)
theorem count_dSlot3InnerTwoStageSelectCat_s1_mWork_11_toff
    {mWork : ℕ} {tS1 : Fin 10 → ℕ} (s1 : ∀ j, Slot1HadCutLeafSpec mWork (tS1 j))
    (truncFn : Fin 10 → Configuration → Configuration)
    {B tTwBase tTwPairCtrl tTwPairCat tBaseFoldCtrl tBaseFoldCat
     tFoldCtrl tFoldCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {mBase : ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j,
      Slot3InnerGenAsymHeldTwSpec_mWork mWork (baseTw j).uTwHeldSub37 (tTwPairCtrl j)
      (tTwPairCat j))
    (baseS3 : ∀ j,
      Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j,
      Slot3InnerSlot3InnerCircuitSpec_mWork mWork (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    (dSlot3InnerTwoStageSelectCat_s1_mWork_11 s1 truncFn baseFolded foldedCirc baseTw asymTw baseS3
      s3Circ
      j c v rAct rWork hDisj).count .TOFF = 0 := by
  exact count_dSeq5_toff ((asymTw j).hToffPairCat c _ _ _ _)
    (((s1 j).leaf).hToff _ _ _ _ _ _ _ _) ((s3Circ j).hToffCat _ _ _ _ _)
    (foldedCirc.hToffCat _ _ _ _ _ _)
theorem count_dSlot3InnerTwoStageSelectCat_s1_mWork_11_t_le
    {mWork : ℕ} {tS1 : Fin 10 → ℕ} (s1 : ∀ j, Slot1HadCutLeafSpec mWork (tS1 j))
    (truncFn : Fin 10 → Configuration → Configuration)
    {B tTwBase tTwPairCtrl tTwPairCat tBaseFoldCtrl tBaseFoldCat
     tFoldCtrl tFoldCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {mBase : ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j,
      Slot3InnerGenAsymHeldTwSpec_mWork mWork (baseTw j).uTwHeldSub37 (tTwPairCtrl j)
      (tTwPairCat j))
    (baseS3 : ∀ j,
      Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j,
      Slot3InnerSlot3InnerCircuitSpec_mWork mWork (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) {Var : Type} {n : ℕ}
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    (dSlot3InnerTwoStageSelectCat_s1_mWork_11 s1 truncFn baseFolded foldedCirc baseTw asymTw baseS3
      s3Circ
      j c v rAct rWork hDisj).count .T ≤
      tSelSlot3Inner_HeldTw_S1 (tFoldCat j) (tS1 j) (t3Cat j) (tTwPairCat j) := by
  exact count_dSeq5_t_le
    ((asymTw j).hTPairCat c v (rAct.compose (rCoreTopCatSum42Full 37 (by decide)))
      (rWorkSlackIdle 11 (by decide) rAct rWork hDisj)
      (rTwAct_disj_rWorkSlackIdle11 (by decide : 11 + 37 ≤ 48) rAct rWork hDisj))
    (((s1 j).leaf).hT c v ((rAct.compose rSegFull).compose rCoreSeg)
      ((rAct.compose rSegFull).compose rPG48Seg) rWork
      (disjointWires_compose_of_disjoint (rAct.compose rSegFull) hCoreSeg_disj_PG48Seg)
      ((hDisj.compose_left rSegFull).compose_left rCoreSeg)
      ((hDisj.compose_left rSegFull).compose_left rPG48Seg)) (s1 j).htLeaf
    ((s3Circ j).hTCat c v (rAct.compose (rCoreTopCatFull 36 (by decide)))
      (rWorkSlackIdle 11 (by decide) rAct rWork hDisj)
      (rSub3Act_disj_rWorkSlackIdle11 (by decide : 11 + 36 ≤ 48) rAct rWork hDisj))
    (foldedCirc.hTCat j c v rAct rWork hDisj) (by
      unfold tSelSlot3Inner_HeldTw_S1
      omega)
theorem dSlot3InnerTwoStageSelectCtrl_s1_mWork_11_realizesOn
    {mWork : ℕ} {tS1 : Fin 10 → ℕ} (s1 : ∀ j, Slot1HadCutLeafSpec mWork (tS1 j))
    (truncFn : Fin 10 → Configuration → Configuration)
    {B tTwBase tTwPairCtrl tTwPairCat tBaseFoldCtrl tBaseFoldCat
     tFoldCtrl tFoldCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {mBase : ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j,
      Slot3InnerGenAsymHeldTwSpec_mWork mWork (baseTw j).uTwHeldSub37 (tTwPairCtrl j)
      (tTwPairCat j))
    (baseS3 : ∀ j,
      Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j,
      Slot3InnerSlot3InnerCircuitSpec_mWork mWork (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
      [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    RealizesOnProj (pCtrl3ExtOn 11 (by decide) rAct rWork)
      (rAct.embedUnitary
        (uTwoStageSelectHeldHeldTw_s1 truncFn s1 baseFolded.uFoldedCtrlFull baseTw baseS3 j c))
      (dSlot3InnerTwoStageSelectCtrl_s1_mWork_11 s1 truncFn baseFolded foldedCirc baseTw asymTw
        baseS3 s3Circ
        j c v rAct rWork hDisj) := by
  let rWBCtrl : QRegister (mWork + 11) n := rWorkCtrlTwist 11 (by decide) rAct rWork hDisj
  let rTwSub := rAct.compose (rCoreTopCatSum42Full 37 (by decide))
  let hTwW := rTwAct_disj_rWTw (by decide : 11 + 37 ≤ 48) rAct rWork hDisj
  let rSeg := rAct.compose rSegFull
  let hSW := hDisj.compose_left rSegFull
  let rC := rSeg.compose rCoreSeg
  let rP := rSeg.compose rPG48Seg
  let hCP := disjointWires_compose_of_disjoint rSeg hCoreSeg_disj_PG48Seg
  let hCW := hSW.compose_left rCoreSeg
  let hPW := hSW.compose_left rPG48Seg
  let rSub3 := rAct.compose (rCoreTopCatFull 36 (by decide))
  let hSub3W := rSub3Act_disj_rWorkCtrlTwist11 (by decide : 11 + 36 ≤ 48) rAct rWork hDisj
  have pTwPair := (asymTw j).hRealPairCtrl c v rTwSub rWBCtrl hTwW
  have p0 := liftStreamPGIdle11_to_pCtrl3Ext11 hDisj
    (liftCtrlTwist148_to_streamPGIdle11 hDisj pTwPair.fwd)
  rw [show (rCoreTopCatSum42Full 37 (by decide)).embedUnitary ((baseTw j).uTwHeldSub37 c) =
    uTwHeldFullHeldTw (baseTw j) c from rfl] at p0
  have eCT : rC.concat rP hCP = rAct.compose (rSegFull.compose rCTSeg) :=
    compose_concat_eq_singleCat rSeg rCoreSeg rPG48Seg hCoreSeg_disj_PG48Seg
  have s1Raw := ((s1 j).leaf).hReal c v rC rP rWork hCP hCW hPW
  rw [eCT] at s1Raw
  have p1 := realizesOnProj_of_clean_rWork hDisj (rSegFull.compose rCTSeg)
    (E_rawCtrl3Ext 11 (by decide)) s1Raw
  rw [QRegister.embedUnitary_compose,
    show rSegFull.embedUnitary (rCTSeg.embedUnitary ((s1 j).leaf.uCat c)) =
      uSlot1FullS1 (s1 j) c from rfl] at p1
  have p2 := liftRawStreamPGIdle11_to_pRawCtrl3Ext11 hDisj
    (liftCtrlTwist148_to_rawStreamPGIdle11 hDisj
      ((s3Circ j).hRealCtrl c v rSub3 rWBCtrl hSub3W))
  rw [← SelectExtStitch.rSegFull_compose_rCoreTopCatInCT_eq 36 (by decide),
    QRegister.embedUnitary_compose rSegFull, QRegister.embedUnitary_compose rCTSeg,
    show rSegFull.embedUnitary (rCTSeg.embedUnitary
      ((rCoreTopCatInCT 36 (by decide)).embedUnitary ((baseS3 j).uInnerCatSub c))) =
      uSlot3FullInner_s1 (truncFn j) (baseS3 j) c from rfl] at p2
  have p3 := foldedCirc.hRealRawCtrl j c v rAct rWork hDisj
  have p4Raw := liftRawStreamPGIdle11_to_pRawCtrl3Ext11 hDisj
    (liftCtrlTwist148_to_rawStreamPGIdle11 hDisj pTwPair.inv)
  rw [← embedUnitary_inv_symm (rCoreTopCatSum42Full 37 (by decide)),
    show (rCoreTopCatSum42Full 37 (by decide)).embedUnitary ((baseTw j).uTwHeldSub37 c) =
      uTwHeldFullHeldTw (baseTw j) c from rfl] at p4Raw
  unfold pCtrl3ExtOn at p0 ⊢
  unfold pRawCtrl3ExtOn at p2 p3 p4Raw
  dsimp only [dSlot3InnerTwoStageSelectCtrl_s1_mWork_11, uTwoStageSelectHeldHeldTw_s1]
  exact dSeq5_embed_realizesOnProj rAct
    (embedIntertwine2 hDisj (uTwHeldFullHeldTw_intertwines_ctrl3Ext11 (baseTw j) c))
    (embedIntertwine2 hDisj (uSlot1FullS1_comm_raw11 (s1 j) c).1)
    (embedIntertwine2 hDisj (uSlot3FullInner_s1_s1_comm_raw11 (truncFn j) (baseS3 j) c).1)
    (embedIntertwine2 hDisj (baseFolded.hInterRawCtrl j c)) p0 p1 p2 p3 p4Raw
theorem dSlot3InnerTwoStageSelectCat_s1_mWork_11_realizesOnP
    {mWork : ℕ} {tS1 : Fin 10 → ℕ} (s1 : ∀ j, Slot1HadCutLeafSpec mWork (tS1 j))
    (truncFn : Fin 10 → Configuration → Configuration)
    {B tTwBase tTwPairCtrl tTwPairCat tBaseFoldCtrl tBaseFoldCat
     tFoldCtrl tFoldCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {mBase : ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j,
      Slot3InnerGenAsymHeldTwSpec_mWork mWork (baseTw j).uTwHeldSub37 (tTwPairCtrl j)
      (tTwPairCat j))
    (baseS3 : ∀ j,
      Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j,
      Slot3InnerSlot3InnerCircuitSpec_mWork mWork (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (j : Fin 10) (c : Configuration) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
      [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    RealizesOnProj (pHoistExtOn 11 (by decide) rAct rWork)
      (rAct.embedUnitary
        (uTwoStageSelectHeldHeldTw_s1 truncFn s1 baseFolded.uFoldedCatFull baseTw baseS3 j c))
      (dSlot3InnerTwoStageSelectCat_s1_mWork_11 s1 truncFn baseFolded foldedCirc baseTw asymTw
        baseS3 s3Circ
        j c v rAct rWork hDisj) := by
  let rWBCat : QRegister (mWork + 14) n := rWorkSlackIdle 11 (by decide) rAct rWork hDisj
  let rTwSub := rAct.compose (rCoreTopCatSum42Full 37 (by decide))
  let hTwW := rTwAct_disj_rWorkSlackIdle11 (by decide : 11 + 37 ≤ 48) rAct rWork hDisj
  let rSeg := rAct.compose rSegFull
  let hSW := hDisj.compose_left rSegFull
  let rC := rSeg.compose rCoreSeg
  let rP := rSeg.compose rPG48Seg
  let hCP := disjointWires_compose_of_disjoint rSeg hCoreSeg_disj_PG48Seg
  let hCW := hSW.compose_left rCoreSeg
  let hPW := hSW.compose_left rPG48Seg
  let rSub3 := rAct.compose (rCoreTopCatFull 36 (by decide))
  let hSub3W := rSub3Act_disj_rWorkSlackIdle11 (by decide : 11 + 36 ≤ 48) rAct rWork hDisj
  have pTwPair := (asymTw j).hRealPairCat c v rTwSub rWBCat hTwW
  have p0 := liftSlackIdle151_to_pHoistExt11 hDisj pTwPair.fwd
  rw [show (rCoreTopCatSum42Full 37 (by decide)).embedUnitary ((baseTw j).uTwHeldSub37 c) =
    uTwHeldFullHeldTw (baseTw j) c from rfl] at p0
  have eCT : rC.concat rP hCP = rAct.compose (rSegFull.compose rCTSeg) :=
    compose_concat_eq_singleCat rSeg rCoreSeg rPG48Seg hCoreSeg_disj_PG48Seg
  have s1Raw := ((s1 j).leaf).hReal c v rC rP rWork hCP hCW hPW
  rw [eCT] at s1Raw
  have p1 := realizesOnProj_of_clean_rWork hDisj (rSegFull.compose rCTSeg)
    (E_rawSegExt 11 (by decide)) s1Raw
  rw [QRegister.embedUnitary_compose,
    show rSegFull.embedUnitary (rCTSeg.embedUnitary ((s1 j).leaf.uCat c)) =
      uSlot1FullS1 (s1 j) c from rfl] at p1
  have p2 := liftSlackIdle151_to_pRawHoistExt11 hDisj
    ((s3Circ j).hRealCat c v rSub3 rWBCat hSub3W)
  rw [← SelectExtStitch.rSegFull_compose_rCoreTopCatInCT_eq 36 (by decide),
    QRegister.embedUnitary_compose rSegFull, QRegister.embedUnitary_compose rCTSeg,
    show rSegFull.embedUnitary (rCTSeg.embedUnitary
      ((rCoreTopCatInCT 36 (by decide)).embedUnitary ((baseS3 j).uInnerCatSub c))) =
      uSlot3FullInner_s1 (truncFn j) (baseS3 j) c from rfl] at p2
  have p3 := foldedCirc.hRealRawCat j c v rAct rWork hDisj
  have p4Raw := liftSlackIdle151_to_pRawHoistExt11 hDisj pTwPair.inv
  rw [← embedUnitary_inv_symm (rCoreTopCatSum42Full 37 (by decide)),
    show (rCoreTopCatSum42Full 37 (by decide)).embedUnitary ((baseTw j).uTwHeldSub37 c) =
      uTwHeldFullHeldTw (baseTw j) c from rfl] at p4Raw
  unfold pHoistExtOn at p0 ⊢
  unfold pRawHoistExtOn at p2 p3 p4Raw
  dsimp only [dSlot3InnerTwoStageSelectCat_s1_mWork_11, uTwoStageSelectHeldHeldTw_s1]
  exact dSeq5_embed_realizesOnProj rAct
    (embedIntertwine2 hDisj (uTwHeldFullHeldTw_intertwines_segExt11 (baseTw j) c))
    (embedIntertwine2 hDisj (uSlot1FullS1_comm_raw11 (s1 j) c).2)
    (embedIntertwine2 hDisj (uSlot3FullInner_s1_s1_comm_raw11 (truncFn j) (baseS3 j) c).2)
    (embedIntertwine2 hDisj (baseFolded.hInterRawCat j c)) p0 p1 p2 p3 p4Raw
/-- `{mWork}`-polymorphic `HoistedExtHkSelectSpec mWork 11` (`142 ≤ mWork`, `0 TOFF`) for horizon
  `j`. -/
noncomputable def mkSlot3InnerHoistedExtHkSelectSpecS1_mWork
    {mWork : ℕ} {tS1 : Fin 10 → ℕ} (s1 : ∀ j, Slot1HadCutLeafSpec mWork (tS1 j))
    (truncFn : Fin 10 → Configuration → Configuration)
    {B tTwBase tTwPairCtrl tTwPairCat tBaseFoldCtrl tBaseFoldCat
     tFoldCtrl tFoldCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {mBase : ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j,
      Slot3InnerGenAsymHeldTwSpec_mWork mWork (baseTw j).uTwHeldSub37 (tTwPairCtrl j)
      (tTwPairCat j))
    (baseS3 : ∀ j,
      Slot3InnerSlot3InnerSpecS1 (truncFn j) (s1 j) (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j,
      Slot3InnerSlot3InnerCircuitSpec_mWork mWork (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (selOra : Fin 10 → FullSysSelectOracleBundle 80 48)
    (hOra : ∀ j, SelectOraHypothesisOfS1Trunc (truncFn j) (selOra j) (s1 j).ora1
      (leaf2Slot3InnerOfTruncB (truncFn j) (B j) (hB6 j) (hB27 j)) (baseS3 j).ora3)
    (j : Fin 10) :
    HoistedExtHkSelectSpec mWork 11 hkIdle
      (tSelSlot3Inner_HeldTw_S1 (tFoldCtrl j) (tS1 j) (t3Ctrl j) (tTwPairCtrl j))
      (tSelSlot3Inner_HeldTw_S1 (tFoldCat j) (tS1 j) (t3Cat j) (tTwPairCat j))
      coreQftHadamardPrunedBundle128
      (selOra j)
      (selImplSlot3InnerHeldTw_s1 truncFn s1 selOra baseFolded baseTw baseS3 hOra j) :=
  { uSelectCtrl :=
    uTwoStageSelectHeldHeldTw_s1 truncFn s1 baseFolded.uFoldedCtrlFull baseTw baseS3 j
    uSelectCat := uTwoStageSelectHeldHeldTw_s1 truncFn s1 baseFolded.uFoldedCatFull baseTw baseS3 j
    dSelectCtrl := fun c {_} {_} v rAct rWork hDisj ↦
      dSlot3InnerTwoStageSelectCtrl_s1_mWork_11 s1 truncFn baseFolded foldedCirc baseTw asymTw
        baseS3 s3Circ
        j c v rAct rWork hDisj
    dSelectCat := fun c {_} {_} v rAct rWork hDisj ↦
      dSlot3InnerTwoStageSelectCat_s1_mWork_11 s1 truncFn baseFolded foldedCirc baseTw asymTw baseS3
        s3Circ
        j c v rAct rWork hDisj
    hToffCtrl := fun c {_} {_} v rAct rWork hDisj ↦
      count_dSlot3InnerTwoStageSelectCtrl_s1_mWork_11_toff s1 truncFn baseFolded foldedCirc baseTw
        asymTw baseS3 s3Circ
        j c v rAct rWork hDisj
    hToffCat := fun c {_} {_} v rAct rWork hDisj ↦
      count_dSlot3InnerTwoStageSelectCat_s1_mWork_11_toff s1 truncFn baseFolded foldedCirc baseTw
        asymTw baseS3 s3Circ
        j c v rAct rWork hDisj
    hTCtrl := fun c {_} {_} v rAct rWork hDisj ↦
      count_dSlot3InnerTwoStageSelectCtrl_s1_mWork_11_t_le s1 truncFn baseFolded foldedCirc baseTw
        asymTw baseS3 s3Circ
        j c v rAct rWork hDisj
    hTCat := fun c {_} {_} v rAct rWork hDisj ↦
      count_dSlot3InnerTwoStageSelectCat_s1_mWork_11_t_le s1 truncFn baseFolded foldedCirc baseTw
        asymTw baseS3 s3Circ
        j c v rAct rWork hDisj
    hSelCtrlE := fun c ↦
      (uTwoStageSelectHeldHeldTw_s1_intertwines_11 truncFn s1 baseFolded baseTw baseS3 j c).1
    hSelCatE := fun c ↦
      (uTwoStageSelectHeldHeldTw_s1_intertwines_11 truncFn s1 baseFolded baseTw baseS3 j c).2
    hSelSlack010 :=
      selImplSlot3InnerHeldTw_s1_hSelSlack010 truncFn s1 selOra baseFolded baseTw baseS3 hOra j
    hSelIdle :=
      selImplSlot3InnerHeldTw_s1_hSelIdle truncFn s1 selOra baseFolded baseTw baseS3 hOra j
    hRealCtrl := fun c {_} [_] [_] {_} [_] v rAct rWork hDisj ↦
      dSlot3InnerTwoStageSelectCtrl_s1_mWork_11_realizesOn s1 truncFn baseFolded foldedCirc baseTw
        asymTw baseS3 s3Circ
        j c v rAct rWork hDisj
    hRealCat := fun c {_} [_] [_] {_} [_] v rAct rWork hDisj ↦
      dSlot3InnerTwoStageSelectCat_s1_mWork_11_realizesOnP s1 truncFn baseFolded foldedCirc baseTw
        asymTw baseS3 s3Circ
        j c v rAct rWork hDisj }

/-- Generic `{mWork}`-polymorphic (`128 ≤ mWork`) `Pos512ChiralBhmtPwu24HorizonSelPkg` builder
at `k_idle = 11` decoupling `(baseFolded, foldedCirc)`, `(baseTw, asymTw)`, and `(baseS3, s3Circ)`
with `ora1Pwu24OfBSub`. -/
noncomputable def mkComposableGenPwu24HorizonSelPkg_mWork
    {mBase mWork : ℕ} (hm128 : 128 ≤ mWork)
    {W B bSub tBaseFoldCtrl tBaseFoldCat tFoldCtrl tFoldCat
     tTwBase tTwCtrl tTwCat tBase3Ctrl tBase3Cat t3Ctrl t3Cat : Fin 10 → ℕ}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (hbLo : ∀ j, 18 ≤ bSub j) (hbHi : ∀ j, bSub j ≤ 24)
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (baseTw : ∀ j, Slot3InnerHeldTwSpec (tTwBase j))
    (asymTw : ∀ j, Slot3InnerGenAsymHeldTwSpec_mWork mWork
      (baseTw j).uTwHeldSub37 (tTwCtrl j) (tTwCat j))
    (baseS3 : ∀ j, Slot3InnerSlot3InnerSpecS1 (truncChiralPos512OfW (W j))
      (slot1Pwu24LeafSpec (bSub j) (hbLo j) (hbHi j) (by omega : 75 ≤ mWork))
      (baseTw j) (tBase3Ctrl j) (tBase3Cat j))
    (s3Circ : ∀ j, Slot3InnerSlot3InnerCircuitSpec_mWork mWork
      (baseS3 j).uInnerCatSub (t3Ctrl j) (t3Cat j))
    (j : Fin 10) :
    Pos512ChiralBhmtPwu24HorizonSelPkg mWork 11 (by decide)
      (W j) (B j) (bSub j)
      (t2CtrlSlot3InnerOfB (B j)) (t2CatSlot3InnerOfB (B j))
      (tSelSlot3Inner_HeldTw_S1 (tFoldCtrl j) (4 * (bSub j + 51)) (t3Ctrl j) (tTwCtrl j))
      (tSelSlot3Inner_HeldTw_S1 (tFoldCat j) (4 * (bSub j + 51)) (t3Cat j) (tTwCat j))
      (hB6 j) (hB27 j) (hbLo j) (hbHi j)
      (baseS3 j).ora3 :=
  let truncFn := fun i ↦ truncChiralPos512OfW (W i)
  let s1 := fun i ↦ slot1Pwu24LeafSpec (bSub i) (hbLo i) (hbHi i) (by omega : 75 ≤ mWork)
  let selOra := fun i ↦ mkSelectOraBundleOfPwu24Trunc (bSub i) (hbLo i) (hbHi i) (truncFn i)
    (leaf2Slot3InnerOfTruncB (truncFn i) (B i) (hB6 i) (hB27 i)) (baseS3 i).ora3
  let hOra := fun i ↦ stepSelectOraHypothesisOfPwu24Trunc (bSub i) (hbLo i) (hbHi i) (truncFn i)
    (leaf2Slot3InnerOfTruncB (truncFn i) (B i) (hB6 i) (hB27 i)) (baseS3 i).ora3
  mkPos512ChiralBhmtPwu24PkgOfOra hm128
    (selOra j)
    (selImplSlot3InnerHeldTw_s1 truncFn s1 selOra baseFolded baseTw baseS3 hOra j)
    (mkSlot3InnerHoistedExtHkSelectSpecS1_mWork s1 truncFn baseFolded foldedCirc baseTw asymTw
      baseS3
      s3Circ selOra hOra j)
    (leaf2Slot3InnerOfTruncB (truncFn j) (B j) (hB6 j) (hB27 j))
    (leaf2Slot3InnerOfTruncB_uPosPhase0 (truncFn j) (B j) (hB6 j) (hB27 j))
    (hOra j)

/-- Fast projection equality for `mkNorm1sSlot3InnerSlot3InnerSpec.uInnerCatSub` (`O(1)` heartbeats,
isolated from `s1 : Slot1HadCutLeafSpec` so `whnf` never unfolds `slot1Pwu24LeafSpec`). -/
theorem mkNorm1sSlot3InnerSlot3InnerSpec_uInnerCatSub_eq
    (trunc : Configuration → Configuration) (W bk : ℕ) (t : Norm1sTier)
    (hW28 : 28 ≤ W) (hW36 : W ≤ 36) (hTrunc : trunc = truncWCfg W)
    (hbk : 21 ≤ bk ∧ bk ≤ 36) (ht : IsCertifiedNorm1sTier6 t) :
    (mkNorm1sSlot3InnerSlot3InnerSpec trunc W bk t hW28 hW36 hTrunc hbk ht).uInnerCatSub =
      fun c ↦ uSlot3HadCutCat36FullSys t (truncBkNucCfg bk c) := by
  dsimp only [mkNorm1sSlot3InnerSlot3InnerSpec]

/-- Motive-explicit transport of `Slot3InnerSlot3InnerCircuitSpec_mWork` along `uInnerCatSub`
  equality. -/
def castSlot3InnerSlot3InnerCircuitSpec_mWork {mWork t3Ctrl t3Cat : ℕ}
    {u₁ u₂ : Configuration → Unitary (2 ^ (fullSysCoreWires 80 + 36))}
    (hu : u₁ = u₂) (sc : Slot3InnerSlot3InnerCircuitSpec_mWork mWork u₁ t3Ctrl t3Cat) :
    Slot3InnerSlot3InnerCircuitSpec_mWork mWork u₂ t3Ctrl t3Cat :=
  hu ▸ sc

/-- Orthogonal `{mWork}`-polymorphic (`128 ≤ mWork`) `Pos512ChiralBhmtPwu24HorizonSelPkg`
builder at `k_idle = 11` decoupling `(baseFolded, foldedCirc)`, `asymTw`, and asymmetric
`(t3Ctrl, t3Cat)` `s3Circ` with `ora1Pwu24OfBSub`. -/
noncomputable def mkComposable_Pwu24HorizonSelPkg_mWork
    {mBase mWork : ℕ} (hm128 : 128 ≤ mWork)
    {W B bk bSub tBaseFoldCtrl tBaseFoldCat tFoldCtrl tFoldCat
     t3Ctrl t3Cat tTwCtrl tTwCat : Fin 10 → ℕ}
    {tier : Fin 10 → Norm1sTier} {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    (hW28 : ∀ j, 28 ≤ W j) (hW36 : ∀ j, W j ≤ 36)
    (hbk : ∀ j, 21 ≤ bk j ∧ bk j ≤ 36) (ht : ∀ j, IsCertifiedNorm1sTier6 (tier j))
    (hbLo : ∀ j, 18 ≤ bSub j) (hbHi : ∀ j, bSub j ≤ 24)
    (baseFolded : SlimFoldedPass123Bundle11 mBase B hB6 hB27 tBaseFoldCtrl tBaseFoldCat)
    (foldedCirc : FoldedPass123CircuitSpec_mWork mWork
      baseFolded.uFoldedCtrlFull baseFolded.uFoldedCatFull tFoldCtrl tFoldCat)
    (asymTw : ∀ j, Slot3InnerGenAsymHeldTwSpec_mWork mWork
      (twHeld37Wide52Spec190 (W j) (hW28 j) (hW36 j)).uTwHeldSub37 (tTwCtrl j) (tTwCat j))
    (s3Circ : ∀ j, Slot3InnerSlot3InnerCircuitSpec_mWork mWork
      (mkNorm1sSlot3InnerSlot3InnerSpec (truncChiralPos512OfW (W j)) (W j) (bk j) (tier j)
        (hW28 j) (hW36 j) (truncChiralPos512OfW_eq_truncWCfg (W j) (hW28 j) (hW36 j))
        (hbk j) (ht j)).uInnerCatSub
      (t3Ctrl j) (t3Cat j))
    (j : Fin 10) :
    Pos512ChiralBhmtPwu24HorizonSelPkg mWork 11 (by decide)
      (W j) (B j) (bSub j)
      (t2CtrlSlot3InnerOfB (B j)) (t2CatSlot3InnerOfB (B j))
      (tSelSlot3Inner_HeldTw_S1 (tFoldCtrl j) (4 * (bSub j + 51)) (t3Ctrl j) (tTwCtrl j))
      (tSelSlot3Inner_HeldTw_S1 (tFoldCat j) (4 * (bSub j + 51)) (t3Cat j) (tTwCat j))
      (hB6 j) (hB27 j) (hbLo j) (hbHi j)
      (s3Swap3OracleNorm1sUltraBk (tier j) (ht j) (bk j) (hbk j)) :=
  mkComposableGenPwu24HorizonSelPkg_mWork hm128 hbLo hbHi baseFolded foldedCirc
    (fun i ↦ twHeld37Wide52Spec190 (W i) (hW28 i) (hW36 i))
    asymTw
    (fun i ↦ mkNorm1sSlot3InnerSlot3InnerSpecS1 (truncChiralPos512OfW (W i))
      (slot1Pwu24LeafSpec (bSub i) (hbLo i) (hbHi i) (by omega : 75 ≤ mWork))
      (W i) (bk i) (tier i) (hW28 i) (hW36 i)
      (truncChiralPos512OfW_eq_truncWCfg (W i) (hW28 i) (hW36 i)) (hbk i) (ht i))
    (fun i ↦ castSlot3InnerSlot3InnerCircuitSpec_mWork
      (mkNorm1sSlot3InnerSlot3InnerSpec_uInnerCatSub_eq
        (truncChiralPos512OfW (W i)) (W i) (bk i) (tier i)
        (hW28 i) (hW36 i) (truncChiralPos512OfW_eq_truncWCfg (W i) (hW28 i) (hW36 i))
        (hbk i) (ht i))
      (s3Circ i))
    j
end ConfigSelectS1
end SelectS1
end


end QuantumComputation.Specs.StoppingPowerSolution
end
