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

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.FusedWState55Kick

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section SlimFermApproxSec2BAnd3A

section
set_option maxRecDepth 262144
set_option exponentiation.threshold 8192
section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
attribute [-instance] littleWedderburn Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroK3 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
namespace StageAConjHAndStreamBridge
noncomputable section ImplAlt
open HermitianMat LocalClassicalPerm
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror OctahedralOrbit
open Dyadic128CoulombMath
open CanonRank7Circuit
open HoistedSwapSelectBridge (unitaryConj)
open KaratsubaQft64Matrix (omega128 omega128_add bit6)
open DyadicQft64WalkCircuit (u18GridEquiv)
open CoreQftHadamard140And160 (CanonStageSpec128)
open FullSysCatSegmentBridge (fullSysCoreWires)
open StreamingBchComparator PosSlots24BranchConcrete
open PosSlots24SemanticBridge (pos24_6_le_80)
open PosPostPrep80MergedVep (cSwapCore3967 uSwapCore3967 lockPosPostVal_eq)
open NuclearTwistRealizes (slot2AxisSum)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open StageAPosHeadConjugatedCircuit (rSpectatorElec3906InCore rSpectatorSlot elecProd217 uHad217)
open TwistStreamEliminationAux (spectatorSum217)
open Slot0SubAdd14And217Stream (rSum14Slice42 uSlot0Sum42Add)
open StageAPointPhase128OnStep (hL3_le_654 diag6Unitary stage128_seq_uEff stageW16Prefix128_uEff
  activeOneElecForestFullQftStage128 bit7 packHybrid6 hybridStageExp1 hybridStageExp2
  hybridStageExp3 hybridStageExp4 hybridStageExp5 pointCrossXorExp128 pointSumCliffordExp128
  pointElecCliffordExp128 pointCrossXorExp128_eq_sum_hybrid_stages rCoreInCoreSum42
  rSum14InCoreSum42)
open DoubleDutyFoldedRealizesBridge (selPosCoreInCore80)
open ForestQft117BundleNoTopBridge (dCanonStage128Fwd dCanonStage128Inv count_dCanonStage128Fwd_toff
  count_dCanonStage128Inv_toff count_dCanonStage128Fwd_t count_dCanonStage128Inv_t
  dCanonStage128Fwd_realizes dCanonStage128Inv_realizes pStream217Core pStream218Core)
open BoothOpt_06_Stream217ZeroSave0Width128 (rSpec217OfCore disj_rSpec217OfCore_left
  selSpec217InCoreSum14 compose_selSpec217InCoreSum14 selCoreSum14In42
  uThreeAxis217_compute_ket_of_oneAxis uStream217Spec131 uStream217Spec131_slice_compute_ket)
section HeadAndPhi
attribute [local reducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
section Part2_Target18AndPointPhiSave0
open DyadicQft64WalkCircuit (realizes_congr_slice rIdOfCat_concat_rPGOfCat)
section PointPhaseHeldZ18
open DyadicQft64WalkCircuit288 (apexCatUnitary apexCatUnitary_intertwinesCat
  embedUnitary_genCatPhasePermUnitary_mulVec_basisKet)
open CoreQftHadamard140And160 (rQftCanon128 rWorkCanon128 rSysCanon128 rPGCanon128
  rSysCanon128_disjoint_rPGCanon128 rSysCanon128_disjoint_rWorkCanon128
  rPGCanon128_disjoint_rWorkCanon128)
open HeldRSum42TwistQftPass2Stitch (axisProdPrefix)
open StageAPointPhase128OnStep (ForestSlotConfig forestAxisNat xorForestBatchWork
  xorForestBatchTCost xorForestBatch_spec xorForestBatchFwdDyn128 xorForestBatchInvDyn128
  idxForestAx idxForestAx_inj forestTermAxis w16Exp6 stageW16PrefixCanonStage128 forestCfg3
  forestExp3 forestCfg3_exp_eq forestCfg2 forestExp2 forestCfg2_exp_eq forestCfg1 forestExp1
  forestCfg1_exp_eq forestCfg0 forestExp0 forestCfg0_exp_eq
  axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary)
/-- Matrix `M` on `2 ^ N` only changes qubits inside `rMod` (`M x y ≠ 0 → rMod.AgreeOutside x
  y`). -/
def PreservesOutside {k N : ℕ} (rMod : QRegister k N) (M : Operator (2 ^ N)) : Prop :=
  ∀ x y : Fin (2 ^ N), M x y ≠ 0 → rMod.AgreeOutside x y
theorem preservesOutside_diagonal {k N : ℕ} (rMod : QRegister k N) (d : Fin (2 ^ N) → ℂ) :
    PreservesOutside rMod (Matrix.diagonal d) := by
  intro x y hne
  by_cases hxy : x = y
  · subst hxy; exact fun _ _ ↦ rfl
  · exact absurd (Matrix.diagonal_apply_ne d hxy) hne
theorem preservesOutside_mul {k N : ℕ} {rMod : QRegister k N} {A B : Operator (2 ^ N)}
    (hA : PreservesOutside rMod A) (hB : PreservesOutside rMod B) :
    PreservesOutside rMod (A * B) := by
  intro x y hne
  rw [Matrix.mul_apply] at hne
  obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have ha : A x z ≠ 0 := left_ne_zero_of_mul hz
  have hb : B z y ≠ 0 := right_ne_zero_of_mul hz
  exact fun w hw ↦ (hA x z ha w hw).trans (hB z y hb w hw)
theorem preservesOutside_inv {k N : ℕ} {rMod : QRegister k N} {U : Unitary (2 ^ N)}
    (hU : PreservesOutside rMod U.1) : PreservesOutside rMod (U⁻¹).1 := by
  intro x y hne
  have hInvMat : (U⁻¹).1 = (U.1)ᴴ := Matrix.star_eq_conjTranspose U.1
  have hInv : (U⁻¹).1 x y = star (U.1 y x) := by
    rw [congrFun (congrFun hInvMat x) y, Matrix.conjTranspose_apply]
  rw [hInv, star_ne_zero] at hne
  exact fun w hw ↦ (hU y x hne w hw).symm
open Classical in
theorem preservesOutside_comm_diagonal {k N : ℕ} {rMod : QRegister k N}
    {M : Operator (2 ^ N)} (hM : PreservesOutside rMod M)
    (d : Fin (2 ^ N) → ℂ) (hd : ∀ x y, rMod.AgreeOutside x y → d x = d y) :
    M * Matrix.diagonal d = Matrix.diagonal d * M := by
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h0 : M x y = 0
  · simp [h0]
  · rw [hd x y (hM x y h0), mul_comm]
theorem operator_apply_eq_mulVec_basisKet {N : ℕ} (M : Operator (2 ^ N)) (x y : Fin (2 ^ N)) :
    M x y = (M.mulVec (basisKet (basisBits N y))) x := by
  simp [basisKet, basisState, Matrix.mulVec, dotProduct, Pi.single_apply]
open Classical in
theorem preservesOutside_apexCatUnitary {kSys N s : ℕ} (hs : s ≤ 3)
    (rId : QRegister kSys N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG)
    (Φ : BitAssignment kSys → ℤ) (uLow : BitAssignment kSys → ℕ) :
    PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary (apexCatUnitary kSys s hs Φ uLow)).1
      := by
  intro x y hne
  let β := basisBits N y
  have hy : (basisBitsEquiv N).symm β = y := basisBitsEquiv_symm_basisBits y
  have hraw := embedUnitary_genCatPhasePermUnitary_mulVec_basisKet rId rPG hdisj
    (fun γ ↦ DyadicQft64WalkCircuit288.midSlicePerm7 s hs (uLow γ))
    (fun γ m ↦ Φ γ + 16 * (((((m.val / 2 ^ s) % 2 ^ (4 - s)) + uLow γ) / 2 ^ (4 - s) : ℕ) : ℤ)) β
  let M : Operator (2 ^ N) :=
    ((rId.concat rPG hdisj).embedUnitary (apexCatUnitary kSys s hs Φ uLow)).1
  change M x y ≠ 0 at hne
  rw [operator_apply_eq_mulVec_basisKet M x y] at hne
  dsimp only [M, apexCatUnitary] at hne
  rw [hraw] at hne
  simp only [Pi.smul_apply, smul_eq_mul, basisKet, basisState] at hne
  have hSingle := right_ne_zero_of_mul hne
  by_cases hx : x = rPG.replaceIndex ((basisBitsEquiv N).symm β)
      (DyadicQft64WalkCircuit288.midSlicePerm7 s hs (uLow (fun i ↦ β (rId i)))
        ⟨regVal rPG β, regVal_lt_two_pow rPG β⟩)
  · rw [hy] at hx
    subst hx
    exact fun q hq ↦ rPG.basisBits_replaceIndex_of_not_mem y _ q hq
  · simp [hx] at hSingle
open Classical in
theorem preservesOutside_stageW16Prefix128 {N : ℕ}
    (rId : QRegister (3924 +
      3) N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG) (k : Fin 5) :
    PreservesOutside rPG
      ((rId.concat rPG hdisj).embedUnitary (stageW16PrefixCanonStage128 3 hL3_le_654 k).uCat).1 :=
        by
  have hd : ∃ d,
    ((rId.concat rPG hdisj).embedUnitary (stageW16PrefixCanonStage128 3 hL3_le_654 k).uCat).1 =
      Matrix.diagonal d := by
    dsimp only [stageW16PrefixCanonStage128, CanonStageSpec128.congr,
      HeldRSum42TwistQftPass2Stitch.CanonStageSpec128.ofAxisPrefixCircuit]
    rw [axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary, ← QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val, DyadicQft64.dyadicDiagUnitary]
    exact ⟨_, QRegister.embedMatrix_diagonal _ _⟩
  obtain ⟨d, hd⟩ := hd
  rw [hd]
  exact preservesOutside_diagonal rPG d
open Classical in
/-- Explicit `apexCatUnitary`-backed `CanonStageSpec128` for an `L`-axis Hadamard-Forest batch
along with `PreservesOutside rPG` on all catalyst states. -/
theorem xorForestBatch128_explicit (s off L : ℕ) (cfg : ForestSlotConfig s) (φ6 : Fin 64 → ℤ)
    (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u) (hs : s ≤ 3)
    (hL : 1 ≤ L) (hoff : off + L ≤ 654) (hwMax : xorForestBatchWork s cfg L ≤ 128) : ∃ uCat :
    Unitary (2 ^ (3924 + 3 + 7)), (∀ {N : ℕ} (rId : QRegister (3924 + 3) N) (rPG : QRegister 7
    N) (hdisj : rId.DisjointWires rPG), PreservesOutside rPG ((rId.concat rPG
    hdisj).embedUnitary uCat).1) ∧
    (xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax).count TOFF = 0 ∧
    (xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax).count TOFF = 0 ∧
    (xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax).count T = xorForestBatchTCost s cfg
    L ∧ (xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax).count T = xorForestBatchTCost s
    cfg L ∧ RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128 rWorkCanon128 uCat
    (xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax) ∧
    RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128 rWorkCanon128 uCat⁻¹
    (xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax) ∧ (∀ {N : ℕ} [NeZero (2 ^ N)] (rId
    : QRegister (3924 + 3) N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG) (U_cat7 :
    Unitary (2 ^ 7)), U_cat7.1.mulVec (Pi.single 0 1) = DyadicQft64.phaseGradKet 7 →
    DyadicQft64.IntertwinesCatOp (rPG.embedUnitary U_cat7).1 (rPG.basisOutcomeProjector 0)
    ((rId.concat rPG hdisj).embedUnitary uCat).1 (rId.embedUnitary
    (DyadicQft64.dyadicDiagUnitary (3924 + 3) 7 (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off
    + r.val)))).1) := by
  obtain ⟨hToffF, hTF, hToffI, hTI, hRest⟩ := xorForestBatch_spec () s cfg L hs hL
      (le_refl (xorForestBatchWork s cfg L)) rSysCanon128 rPGCanon128 (rWorkCanon128.slice 0
      (xorForestBatchWork s cfg L) (Nat.zero_add _ ▸ hwMax)) rSysCanon128_disjoint_rPGCanon128
      (rSysCanon128_disjoint_rWorkCanon128.compose_right _)
      (rPGCanon128_disjoint_rWorkCanon128.compose_right _) (idxForestAx off L hoff)
      (idxForestAx_inj off L hoff)
  obtain ⟨Φ, uLow, hEqExp, hRF, hRI⟩ := hRest
  refine ⟨apexCatUnitary (3924 + 3) s hs Φ uLow, fun rId rPG hdisj ↦
    preservesOutside_apexCatUnitary hs rId rPG hdisj Φ uLow, hToffF, hToffI, hTF, hTI,
    realizes_congr_slice (Nat.zero_add _ ▸ hwMax) (rIdOfCat_concat_rPGOfCat rQftCanon128) hRF,
    realizes_congr_slice (Nat.zero_add _ ▸ hwMax) (rIdOfCat_concat_rPGOfCat rQftCanon128) hRI,
    ?_⟩
  intro N _ rId rPG hdisj U_cat7 hcol0
  have heff : DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
      (fun γ ↦ Φ γ + ((2 ^ s * uLow γ : ℕ) : ℤ)) = DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
      (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off + r.val)) := by
    congr 1; funext γ
    rw [hEqExp γ]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have ha : off + r.val < 654 := by have := r.isLt; omega
    let b6 : Fin 6 → ZMod 2 := fun q ↦ γ ⟨6 * (off + r.val) + q.val, by omega⟩
    let u6 : Fin 64 := (basisBitsEquiv 6).symm b6
    have hb_eq : b6 = basisBits 6 u6 := (basisBits_basisBitsEquiv_symm b6).symm
    simp only [forestTermAxis, ha, ↓reduceDIte, idxForestAx]
    change (forestAxisNat s cfg b6 : ℤ) = φ6 u6
    rw [hb_eq]
    exact hφ6 u6
  rw [← heff]
  exact apexCatUnitary_intertwinesCat s hs rId rPG hdisj U_cat7 hcol0 Φ uLow
/-- `CanonStageSpec128` constructor exposing `PreservesOutside rPG` via
  `xorForestBatch128_explicit`. -/
noncomputable def xorForestBatchExpStage128 (s off L tB : ℕ) (cfg : ForestSlotConfig s)
    (φ6 : Fin 64 → ℤ) (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u)
    (hs : s ≤ 3) (hL : 1 ≤ L) (hoff : off + L ≤ 654)
    (hwMax : xorForestBatchWork s cfg L ≤ 128)
    (htB : xorForestBatchTCost s cfg L = tB) : CanonStageSpec128 where
  uCat := Classical.choose (xorForestBatch128_explicit s off L cfg φ6 hφ6 hs hL hoff hwMax)
  uEff := DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
    (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off + r.val))
  tCost := tB
  dFwd := xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax
  dInv := xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax
  hToffFwd :=
    (Classical.choose_spec (xorForestBatch128_explicit s off L cfg φ6 hφ6 hs hL hoff hwMax)).2.1
  hToffInv :=
    (Classical.choose_spec (xorForestBatch128_explicit s off L cfg φ6 hφ6 hs hL hoff hwMax)).2.2.1
  hTFwd :=
    (Classical.choose_spec (xorForestBatch128_explicit s off L cfg φ6 hφ6 hs hL hoff
    hwMax)).2.2.2.1.trans htB
  hTInv :=
    (Classical.choose_spec (xorForestBatch128_explicit s off L cfg φ6 hφ6 hs hL hoff
    hwMax)).2.2.2.2.1.trans htB
  hRealFwd :=
    (Classical.choose_spec (xorForestBatch128_explicit s off L cfg φ6 hφ6 hs hL hoff
    hwMax)).2.2.2.2.2.1
  hRealInv :=
    (Classical.choose_spec (xorForestBatch128_explicit s off L cfg φ6 hφ6 hs hL hoff
    hwMax)).2.2.2.2.2.2.1
  hIntertwines :=
    (Classical.choose_spec (xorForestBatch128_explicit s off L cfg φ6 hφ6 hs hL hoff
    hwMax)).2.2.2.2.2.2.2
open Classical in
theorem preservesOutside_xorForestBatchExpStage128 {N : ℕ} (s off L tB : ℕ)
    (cfg : ForestSlotConfig s) (φ6 : Fin 64 → ℤ) (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg
    (basisBits 6 u) : ℤ) = φ6 u) (hs : s ≤ 3) (hL : 1 ≤ L) (hoff : off + L ≤ 654)
    (hwMax : xorForestBatchWork s cfg L ≤ 128) (htB : xorForestBatchTCost s cfg L = tB)
    (rId : QRegister (3924 + 3) N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG) :
    PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary (xorForestBatchExpStage128 s off
    L tB cfg φ6 hφ6 hs hL hoff hwMax htB).uCat).1 := (Classical.choose_spec
    (xorForestBatch128_explicit s off L cfg φ6 hφ6 hs hL hoff hwMax)).1 rId rPG hdisj
/-- Cutoff `c = 5` `CanonStageSpec128` (`3 T`, `count TOFF = 0`) with explicit `PreservesOutside
  rPG`. -/
noncomputable def stagePointCrossExpC5 : CanonStageSpec128 :=
  stageW16PrefixCanonStage128 3 hL3_le_654 4
/-- Cutoff `c = 4` `CanonStageSpec128` (`13 T`, `count TOFF = 0`) with explicit `PreservesOutside
  rPG`. -/
noncomputable def stagePointCrossExpC4 : CanonStageSpec128 :=
  (stageW16PrefixCanonStage128 3 hL3_le_654 3).seq
    (xorForestBatchExpStage128 3 0 3 10 forestCfg3 forestExp3 forestCfg3_exp_eq
      (by decide) (by decide) (by decide) (by decide) (by decide))
/-- Cutoff `c = 3` `CanonStageSpec128` (`30 T`, `count TOFF = 0`) with explicit `PreservesOutside
  rPG`. -/
noncomputable def stagePointCrossExpC3 : CanonStageSpec128 :=
  (stageW16PrefixCanonStage128 3 hL3_le_654 2).seq
    (xorForestBatchExpStage128 2 0 3 27 forestCfg2 forestExp2 forestCfg2_exp_eq
      (by decide) (by decide) (by decide) (by decide) (by decide))
/-- Cutoff `c = 2` `CanonStageSpec128` (`42 T`, `count TOFF = 0`) with explicit `PreservesOutside
  rPG`. -/
noncomputable def stagePointCrossExpC2 : CanonStageSpec128 :=
  (stageW16PrefixCanonStage128 3 hL3_le_654 1).seq
    (xorForestBatchExpStage128 1 0 3 39 forestCfg1 forestExp1 forestCfg1_exp_eq
      (by decide) (by decide) (by decide) (by decide) (by decide))
/-- Cutoff `c = 1` `CanonStageSpec128` (`29 T`, `count TOFF = 0`) with explicit `PreservesOutside
  rPG`. -/
noncomputable def stagePointCrossExpC1 : CanonStageSpec128 :=
  (stageW16PrefixCanonStage128 3 hL3_le_654 0).seq
    (xorForestBatchExpStage128 0 0 3 26 forestCfg0 forestExp0 forestCfg0_exp_eq
      (by decide) (by decide) (by decide) (by decide) (by decide))
@[simp] theorem stagePointCrossExpC5_tCost : stagePointCrossExpC5.tCost = 3 := rfl
@[simp] theorem stagePointCrossExpC4_tCost : stagePointCrossExpC4.tCost = 13 := rfl
@[simp] theorem stagePointCrossExpC3_tCost : stagePointCrossExpC3.tCost = 30 := rfl
@[simp] theorem stagePointCrossExpC2_tCost : stagePointCrossExpC2.tCost = 42 := rfl
@[simp] theorem stagePointCrossExpC1_tCost : stagePointCrossExpC1.tCost = 29 := rfl
theorem xorForestBatchExpStage128_three_uEff (s tB : ℕ) (cfg : ForestSlotConfig s)
    (φ6 : Fin 64 → ℤ) (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u)
    (hs : s ≤ 3) (hL : 1 ≤ 3) (hoff : 0 + 3 ≤ 654) (hwMax : xorForestBatchWork s cfg 3 ≤ 128)
    (htB : xorForestBatchTCost s cfg 3 = tB) : (xorForestBatchExpStage128 s 0 3 tB cfg φ6 hφ6
    hs hL hoff hwMax htB).uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ diag6Unitary φ6) :=
    (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 3 hL3_le_654 φ6).symm
open Classical in
theorem preservesOutside_stagePointCrossExp {N : ℕ}
    (rId : QRegister (3924 + 3) N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG) :
    PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary stagePointCrossExpC5.uCat).1 ∧
    PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary stagePointCrossExpC4.uCat).1 ∧
    PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary stagePointCrossExpC3.uCat).1 ∧
    PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary stagePointCrossExpC2.uCat).1 ∧
    PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary stagePointCrossExpC1.uCat).1 := by
  have hSeq : ∀ (A B : CanonStageSpec128),
      PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary A.uCat).1 →
      PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary B.uCat).1 →
      PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary (A.seq B).uCat).1 := by
    intro A B hA hB
    change PreservesOutside rPG ((rId.concat rPG hdisj).embedUnitary (B.uCat * A.uCat)).1
    rw [(rId.concat rPG hdisj).embedUnitary_mul, Submonoid.coe_mul]
    exact preservesOutside_mul hB hA
  exact ⟨preservesOutside_stageW16Prefix128 rId rPG hdisj 4, hSeq _ _
    (preservesOutside_stageW16Prefix128 rId rPG hdisj 3)
    (preservesOutside_xorForestBatchExpStage128 3 0 3 10 forestCfg3 forestExp3
    forestCfg3_exp_eq _ _ _ _ _ rId rPG hdisj), hSeq _ _ (preservesOutside_stageW16Prefix128
    rId rPG hdisj 2) (preservesOutside_xorForestBatchExpStage128 2 0 3 27 forestCfg2
    forestExp2 forestCfg2_exp_eq _ _ _ _ _ rId rPG hdisj), hSeq _ _
    (preservesOutside_stageW16Prefix128 rId rPG hdisj 1)
    (preservesOutside_xorForestBatchExpStage128 1 0 3 39 forestCfg1 forestExp1
    forestCfg1_exp_eq _ _ _ _ _ rId rPG hdisj), hSeq _ _ (preservesOutside_stageW16Prefix128
    rId rPG hdisj 0) (preservesOutside_xorForestBatchExpStage128 0 0 3 26 forestCfg0
    forestExp0 forestCfg0_exp_eq _ _ _ _ _ rId rPG hdisj)⟩
/-- System wire count `fullSysCoreWires 80 + 42 + 18 = 4094` for `(rCore, rSum42, rZ18)`. -/
abbrev kHeldZ18Sys : ℕ := fullSysCoreWires 80 + 42 + 18
/-- Catalyzed active wire count `kHeldZ18Sys + 7 = 4101` for `(rCore, rSum42, rZ18, rPG7)`. -/
abbrev kHeldZ18Act : ℕ := kHeldZ18Sys + 7
/-- `ℕ`-level cutoff-`c` wire map routing `q < c` to `rSum14(w)[q]` and `q ≥ c` to `rZ18[6w+q]`. -/
def selHybridHeldZ18Nat (c i : ℕ) : ℕ := if i < 18 then if i % 6 < c then fullSysCoreWires 80
    + 14 * (i / 6) + (i % 6) else (fullSysCoreWires 80 + 42) + i else if i < 3924 + 3 then i
    else kHeldZ18Sys + (i - (3924 + 3))
open Classical in
theorem selHybridHeldZ18Nat_sys_lt (c : ℕ) (i : Fin (3924 + 3)) :
    selHybridHeldZ18Nat c i.val < kHeldZ18Sys := by
  have hi := i.isLt
  unfold selHybridHeldZ18Nat kHeldZ18Sys
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
  split_ifs <;> omega
open Classical in
theorem selHybridHeldZ18Nat_act_lt (c : ℕ) (i : Fin (3924 + 3 + 7)) :
    selHybridHeldZ18Nat c i.val < kHeldZ18Act := by
  have hi := i.isLt
  unfold selHybridHeldZ18Nat kHeldZ18Act kHeldZ18Sys
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
  split_ifs <;> omega
open Classical in
theorem selHybridHeldZ18Nat_injective (c : ℕ) {a b : ℕ}
    (ha : a < 3924 + 3 + 7) (hb : b < 3924 + 3 + 7)
    (h : selHybridHeldZ18Nat c a = selHybridHeldZ18Nat c b) : a = b := by
  unfold selHybridHeldZ18Nat kHeldZ18Sys at h
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at h
  split_ifs at h <;> omega
/-- Catalyst-free `(3924 + 3)`-wire hybrid selector inside `kHeldZ18Sys` for cutoff `c`. -/
def selHybridHeldZ18Sys (c : ℕ) : QRegister (3924 + 3) kHeldZ18Sys where
  wires := ⟨fun i ↦ ⟨selHybridHeldZ18Nat c i.val, selHybridHeldZ18Nat_sys_lt c i⟩,
    fun a b h ↦ Fin.ext (selHybridHeldZ18Nat_injective c
      (by have := a.isLt; omega) (by have := b.isLt; omega) (congrArg Fin.val h))⟩
/-- Catalyzed `(3924 + 3 + 7)`-wire hybrid selector inside `kHeldZ18Act` for cutoff `c`. -/
def selHybridHeldZ18Cat (c : ℕ) : QRegister (3924 + 3 + 7) kHeldZ18Act where
  wires := ⟨fun i ↦ ⟨selHybridHeldZ18Nat c i.val, selHybridHeldZ18Nat_act_lt c i⟩,
    fun a b h ↦ Fin.ext (selHybridHeldZ18Nat_injective c a.isLt b.isLt (congrArg Fin.val h))⟩
open Classical in
theorem concat_compose_selHybridHeldZ18Cat {n : ℕ} (c : ℕ)
    (rCSZ : QRegister kHeldZ18Sys n) (rPG7 : QRegister 7 n)
    (hDisj : rCSZ.DisjointWires rPG7) :
    (rCSZ.concat rPG7 hDisj).compose (selHybridHeldZ18Cat c) =
      (rCSZ.compose (selHybridHeldZ18Sys c)).concat rPG7 (hDisj.compose_left (selHybridHeldZ18Sys
        c)) := by
  apply qreg_ext; intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) idx
  · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.compose_apply]
    have hL : selHybridHeldZ18Cat c (Fin.castAdd 7 i) = Fin.castAdd 7 (selHybridHeldZ18Sys c i) :=
      Fin.ext rfl
    rw [hL, QRegister.concat_apply_left]
  · rw [QRegister.compose_apply, QRegister.concat_apply_right]
    have hR : selHybridHeldZ18Cat c (Fin.natAdd (3924 + 3) m) = Fin.natAdd kHeldZ18Sys m := by
      apply Fin.ext
      have hm := m.isLt
      change selHybridHeldZ18Nat c ((3924 + 3) + m.val) = kHeldZ18Sys + m.val
      unfold selHybridHeldZ18Nat kHeldZ18Sys
      dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
      split_ifs <;> omega
    rw [hR, QRegister.concat_apply_right]
/-- Selector `Fin (18 + 42) → Fin kHeldZ18Sys` picking `rZ18` followed by `rSum42`. -/
def selZ18Sum42InHeldZ18Sys : QRegister (18 + 42) kHeldZ18Sys where
  wires := ⟨fun idx ↦
    if h : idx.val < 18 then ⟨(fullSysCoreWires 80 + 42) + idx.val, by dsimp [kHeldZ18Sys]; omega⟩
    else ⟨fullSysCoreWires 80 + (idx.val - 18), by have := idx.isLt; dsimp [kHeldZ18Sys]; omega⟩,
    fun a b hab ↦ by
      have hv := congrArg Fin.val hab
      dsimp only at hv
      have ha := a.isLt; have hb := b.isLt
      by_cases ha18 : a.val < 18 <;> by_cases hb18 : b.val < 18
      · rw [dite_eq_left ha18, dite_eq_left hb18] at hv; simp only at hv; exact Fin.ext (by omega)
      · rw [dite_eq_left ha18, dite_eq_right hb18] at hv; simp only at hv; omega
      · rw [dite_eq_right ha18, dite_eq_left hb18] at hv; simp only at hv; omega
      · rw [dite_eq_right ha18, dite_eq_right hb18] at hv; simp only at hv; exact Fin.ext (by
          omega)⟩
/-- Core register selector `Fin posCoreWires → Fin kHeldZ18Sys` (`0 .. 4033`). -/
def selCoreInHeldZ18Sys : QRegister posCoreWires kHeldZ18Sys :=
  QRegister.block 0 posCoreWires (by
    dsimp [kHeldZ18Sys, posCoreWires, fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
        SpecsAux.SpecMirror.projectileBits]
    omega)
/-- System prefix selector `Fin kHeldZ18Sys → Fin kHeldZ18Act`. -/
def selHeldZ18SysInAct : QRegister kHeldZ18Sys kHeldZ18Act :=
  QRegister.block 0 kHeldZ18Sys (by dsimp [kHeldZ18Act]; omega)
/-- `117-T`, `0-TOFF` forward 3-axis Point-`QFT_64` + Clifford circuit on `(rCore, rSum42, rZ18,
  rPG7)`
using `128 ≤ mWork` clean scratch wires (`dPhiOnHeldZ18Fwd128`). -/
noncomputable def dPhiOnHeldZ18Fwd128 {Var : Type} {n mWork : ℕ} (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  let rSys := rAct.compose selHeldZ18SysInAct
  .seq (dCanonStage128Fwd stagePointCrossExpC5 hm v (rAct.compose (selHybridHeldZ18Cat 5)) rWork
    (hAW.compose_left _))
    (.seq (dCanonStage128Fwd stagePointCrossExpC4 hm v (rAct.compose (selHybridHeldZ18Cat 4)) rWork
      (hAW.compose_left _))
      (.seq (dCanonStage128Fwd stagePointCrossExpC3 hm v (rAct.compose (selHybridHeldZ18Cat 3))
        rWork (hAW.compose_left _))
        (.seq (dCanonStage128Fwd stagePointCrossExpC2 hm v (rAct.compose (selHybridHeldZ18Cat 2))
          rWork (hAW.compose_left _))
          (.seq (dCanonStage128Fwd stagePointCrossExpC1 hm v (rAct.compose (selHybridHeldZ18Cat 1))
            rWork (hAW.compose_left _))
            (.seq (.circuit (cPointSumClifford60.onRegister (rSys.compose selZ18Sum42InHeldZ18Sys)))
              (.circuit (cPointElec217Core.onRegister (rSys.compose selCoreInHeldZ18Sys))))))))
/-- `117-T`, `0-TOFF` inverse 3-axis Point-`QFT_64` + Clifford circuit on `(rCore, rSum42, rZ18,
  rPG7)`
using `128 ≤ mWork` clean scratch wires (`dPhiOnHeldZ18Inv128`). -/
noncomputable def dPhiOnHeldZ18Inv128 {Var : Type} {n mWork : ℕ} (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  let rSys := rAct.compose selHeldZ18SysInAct
  .seq (.circuit (cPointElec217Core.inverse.onRegister (rSys.compose selCoreInHeldZ18Sys)))
    (.seq (.circuit (cPointSumClifford60.inverse.onRegister (rSys.compose selZ18Sum42InHeldZ18Sys)))
      (.seq (dCanonStage128Inv stagePointCrossExpC1 hm v (rAct.compose (selHybridHeldZ18Cat 1))
        rWork (hAW.compose_left _))
        (.seq (dCanonStage128Inv stagePointCrossExpC2 hm v (rAct.compose (selHybridHeldZ18Cat 2))
          rWork (hAW.compose_left _))
          (.seq (dCanonStage128Inv stagePointCrossExpC3 hm v (rAct.compose (selHybridHeldZ18Cat 3))
            rWork (hAW.compose_left _))
            (.seq (dCanonStage128Inv stagePointCrossExpC4 hm v (rAct.compose (selHybridHeldZ18Cat
              4)) rWork (hAW.compose_left _))
              (dCanonStage128Inv stagePointCrossExpC5 hm v (rAct.compose (selHybridHeldZ18Cat 5))
                rWork (hAW.compose_left _)))))))
/-- Catalyzed unitary on `2 ^ kHeldZ18Act` realized by `dPhiOnHeldZ18Fwd128`. -/
noncomputable def uPhiHeldZ18Cat : Unitary (2 ^ kHeldZ18Act) :=
  (selHeldZ18SysInAct.compose selCoreInHeldZ18Sys).embedUnitary uPointElec217Core *
    ((selHeldZ18SysInAct.compose selZ18Sum42InHeldZ18Sys).embedUnitary uPointSumClifford60 *
      ((selHybridHeldZ18Cat 1).embedUnitary stagePointCrossExpC1.uCat *
        ((selHybridHeldZ18Cat 2).embedUnitary stagePointCrossExpC2.uCat *
          ((selHybridHeldZ18Cat 3).embedUnitary stagePointCrossExpC3.uCat *
            ((selHybridHeldZ18Cat 4).embedUnitary stagePointCrossExpC4.uCat *
              (selHybridHeldZ18Cat 5).embedUnitary stagePointCrossExpC5.uCat)))))
/-- Catalyst-free effective unitary on `2 ^ kHeldZ18Sys` intertwined by `uPhiHeldZ18Cat` on
  `catState48`. -/
noncomputable def uPhiHeldZ18Eff : Unitary (2 ^ kHeldZ18Sys) :=
    selCoreInHeldZ18Sys.embedUnitary uPointElec217Core * (selZ18Sum42InHeldZ18Sys.embedUnitary
    uPointSumClifford60 * ((selHybridHeldZ18Sys 1).embedUnitary stagePointCrossExpC1.uEff *
    ((selHybridHeldZ18Sys 2).embedUnitary stagePointCrossExpC2.uEff * ((selHybridHeldZ18Sys
    3).embedUnitary stagePointCrossExpC3.uEff * ((selHybridHeldZ18Sys 4).embedUnitary
    stagePointCrossExpC4.uEff * (selHybridHeldZ18Sys 5).embedUnitary
    stagePointCrossExpC5.uEff)))))
@[simp] theorem count_dPhiOnHeldZ18Fwd128_toff {Var : Type} {n mWork : ℕ}
    (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n) (hAW : rAct.DisjointWires rWork) :
    (dPhiOnHeldZ18Fwd128 hm v rAct rWork hAW).count TOFF = 0 := by
  dsimp only [dPhiOnHeldZ18Fwd128, DynamicCircuit.count]
  rw [count_dCanonStage128Fwd_toff, count_dCanonStage128Fwd_toff,
    count_dCanonStage128Fwd_toff, count_dCanonStage128Fwd_toff, count_dCanonStage128Fwd_toff]
  simp
@[simp] theorem count_dPhiOnHeldZ18Inv128_toff {Var : Type} {n mWork : ℕ}
    (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n) (hAW : rAct.DisjointWires rWork) :
    (dPhiOnHeldZ18Inv128 hm v rAct rWork hAW).count TOFF = 0 := by
  dsimp only [dPhiOnHeldZ18Inv128, DynamicCircuit.count]
  rw [count_dCanonStage128Inv_toff, count_dCanonStage128Inv_toff,
    count_dCanonStage128Inv_toff, count_dCanonStage128Inv_toff, count_dCanonStage128Inv_toff]
  simp
@[simp] theorem count_dPhiOnHeldZ18Fwd128_t {Var : Type} {n mWork : ℕ}
    (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n) (hAW : rAct.DisjointWires rWork) :
    (dPhiOnHeldZ18Fwd128 hm v rAct rWork hAW).count T = 117 := by
  dsimp only [dPhiOnHeldZ18Fwd128, DynamicCircuit.count]
  rw [count_dCanonStage128Fwd_t, count_dCanonStage128Fwd_t,
    count_dCanonStage128Fwd_t, count_dCanonStage128Fwd_t, count_dCanonStage128Fwd_t]
  simp
@[simp] theorem count_dPhiOnHeldZ18Inv128_t {Var : Type} {n mWork : ℕ}
    (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n) (hAW : rAct.DisjointWires rWork) :
    (dPhiOnHeldZ18Inv128 hm v rAct rWork hAW).count T = 117 := by
  dsimp only [dPhiOnHeldZ18Inv128, DynamicCircuit.count]
  rw [count_dCanonStage128Inv_t, count_dCanonStage128Inv_t,
    count_dCanonStage128Inv_t, count_dCanonStage128Inv_t, count_dCanonStage128Inv_t]
  simp
open Classical in
theorem dPhiOnHeldZ18Fwd128_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mWork : ℕ} [NeZero (2 ^ n)] (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
    uPhiHeldZ18Cat (dPhiOnHeldZ18Fwd128 hm v rAct rWork hAW) := by
  have h5 :=
    (dCanonStage128Fwd_realizes stagePointCrossExpC5 hm v (rAct.compose (selHybridHeldZ18Cat 5))
    rWork (hAW.compose_left _)).widenActive
  have h4 :=
    (dCanonStage128Fwd_realizes stagePointCrossExpC4 hm v (rAct.compose (selHybridHeldZ18Cat 4))
    rWork (hAW.compose_left _)).widenActive
  have h3 :=
    (dCanonStage128Fwd_realizes stagePointCrossExpC3 hm v (rAct.compose (selHybridHeldZ18Cat 3))
    rWork (hAW.compose_left _)).widenActive
  have h2 :=
    (dCanonStage128Fwd_realizes stagePointCrossExpC2 hm v (rAct.compose (selHybridHeldZ18Cat 2))
    rWork (hAW.compose_left _)).widenActive
  have h1 :=
    (dCanonStage128Fwd_realizes stagePointCrossExpC1 hm v (rAct.compose (selHybridHeldZ18Cat 1))
    rWork (hAW.compose_left _)).widenActive
  have hSum : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      ((selHeldZ18SysInAct.compose selZ18Sum42InHeldZ18Sys).embedUnitary uPointSumClifford60)
      (.circuit (cPointSumClifford60.onRegister ((rAct.compose selHeldZ18SysInAct).compose
        selZ18Sum42InHeldZ18Sys)) : DynamicCircuit Var n) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rAct rWork _ _ (by
      rw [Circuit.eval_onRegister, cPointSumClifford60_eval, QRegister.compose_assoc,
        QRegister.embedUnitary_compose])
  have hElec : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      ((selHeldZ18SysInAct.compose selCoreInHeldZ18Sys).embedUnitary uPointElec217Core)
      (.circuit (cPointElec217Core.onRegister ((rAct.compose selHeldZ18SysInAct).compose
        selCoreInHeldZ18Sys)) : DynamicCircuit Var n) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rAct rWork _ _ (by
      rw [Circuit.eval_onRegister, cPointElec217Core_eval, QRegister.compose_assoc,
        QRegister.embedUnitary_compose])
  have hSeq := h5.seq hAW (h4.seq hAW (h3.seq hAW (h2.seq hAW (h1.seq hAW (hSum.seq hAW hElec)))))
  unfold dPhiOnHeldZ18Fwd128 uPhiHeldZ18Cat
  simpa only [_root_.mul_assoc] using hSeq
open Classical in
theorem dPhiOnHeldZ18Inv128_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mWork : ℕ} [NeZero (2 ^ n)] (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
    uPhiHeldZ18Cat⁻¹ (dPhiOnHeldZ18Inv128 hm v rAct rWork hAW) := by
  have hElec : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      (((selHeldZ18SysInAct.compose selCoreInHeldZ18Sys).embedUnitary uPointElec217Core)⁻¹)
      (.circuit (cPointElec217Core.inverse.onRegister ((rAct.compose selHeldZ18SysInAct).compose
        selCoreInHeldZ18Sys)) : DynamicCircuit Var n) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rAct rWork _ _ (by
      rw [Circuit.eval_onRegister, Circuit.eval_inverse, cPointElec217Core_eval,
        QRegister.compose_assoc, QRegister.embedUnitary_compose, QRegister.embedUnitary_inv])
  have hSum : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      (((selHeldZ18SysInAct.compose selZ18Sum42InHeldZ18Sys).embedUnitary uPointSumClifford60)⁻¹)
      (.circuit (cPointSumClifford60.inverse.onRegister ((rAct.compose selHeldZ18SysInAct).compose
        selZ18Sum42InHeldZ18Sys)) : DynamicCircuit Var n) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rAct rWork _ _ (by
      rw [Circuit.eval_onRegister, Circuit.eval_inverse, cPointSumClifford60_eval,
        QRegister.compose_assoc, QRegister.embedUnitary_compose, QRegister.embedUnitary_inv])
  have h1 :=
    (dCanonStage128Inv_realizes stagePointCrossExpC1 hm v (rAct.compose (selHybridHeldZ18Cat 1))
    rWork (hAW.compose_left _)).widenActive
  have h2 :=
    (dCanonStage128Inv_realizes stagePointCrossExpC2 hm v (rAct.compose (selHybridHeldZ18Cat 2))
    rWork (hAW.compose_left _)).widenActive
  have h3 :=
    (dCanonStage128Inv_realizes stagePointCrossExpC3 hm v (rAct.compose (selHybridHeldZ18Cat 3))
    rWork (hAW.compose_left _)).widenActive
  have h4 :=
    (dCanonStage128Inv_realizes stagePointCrossExpC4 hm v (rAct.compose (selHybridHeldZ18Cat 4))
    rWork (hAW.compose_left _)).widenActive
  have h5 :=
    (dCanonStage128Inv_realizes stagePointCrossExpC5 hm v (rAct.compose (selHybridHeldZ18Cat 5))
    rWork (hAW.compose_left _)).widenActive
  simp only [QRegister.embedUnitary_inv] at h1 h2 h3 h4 h5
  have hSeq := hElec.seq hAW (hSum.seq hAW (h1.seq hAW (h2.seq hAW (h3.seq hAW (h4.seq hAW h5)))))
  unfold dPhiOnHeldZ18Inv128 uPhiHeldZ18Cat
  simp only [_root_.mul_inv_rev, _root_.mul_assoc] at hSeq ⊢
  exact hSeq
open Classical in
theorem preservesOutside_uPhiHeldZ18Cat {N : ℕ}
    (rCSZ : QRegister kHeldZ18Sys N) (rPG7 : QRegister 7 N) (hDisj : rCSZ.DisjointWires rPG7) :
    PreservesOutside rPG7 ((rCSZ.concat rPG7 hDisj).embedUnitary uPhiHeldZ18Cat).1 ∧
    PreservesOutside rPG7 ((rCSZ.concat rPG7 hDisj).embedUnitary uPhiHeldZ18Cat⁻¹).1 := by
  let rAct := rCSZ.concat rPG7 hDisj
  have hStage : ∀ (c : ℕ) (S : CanonStageSpec128),
      (∀ (rId : QRegister (3924 + 3) N) (hd : rId.DisjointWires rPG7),
        PreservesOutside rPG7 ((rId.concat rPG7 hd).embedUnitary S.uCat).1) →
      PreservesOutside rPG7 (rAct.embedUnitary ((selHybridHeldZ18Cat c).embedUnitary S.uCat)).1 :=
        by
    intro c S hS
    rw [← QRegister.embedUnitary_compose, concat_compose_selHybridHeldZ18Cat c rCSZ rPG7 hDisj]
    exact hS _ _
  have p1 := hStage 1 stagePointCrossExpC1 (fun rId hd ↦
    (preservesOutside_stagePointCrossExp rId rPG7 hd).2.2.2.2)
  have p2 := hStage 2 stagePointCrossExpC2 (fun rId hd ↦
    (preservesOutside_stagePointCrossExp rId rPG7 hd).2.2.2.1)
  have p3 := hStage 3 stagePointCrossExpC3 (fun rId hd ↦
    (preservesOutside_stagePointCrossExp rId rPG7 hd).2.2.1)
  have p4 := hStage 4 stagePointCrossExpC4 (fun rId hd ↦
    (preservesOutside_stagePointCrossExp rId rPG7 hd).2.1)
  have p5 := hStage 5 stagePointCrossExpC5 (fun rId hd ↦
    (preservesOutside_stagePointCrossExp rId rPG7 hd).1)
  have pSum : PreservesOutside rPG7
      (rAct.embedUnitary ((selHeldZ18SysInAct.compose selZ18Sum42InHeldZ18Sys).embedUnitary
        uPointSumClifford60)).1 := by
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val, uPointSumClifford60,
      QRegister.embedMatrix_diagonal]
    exact preservesOutside_diagonal rPG7 _
  have pElec : PreservesOutside rPG7
      (rAct.embedUnitary ((selHeldZ18SysInAct.compose selCoreInHeldZ18Sys).embedUnitary
        uPointElec217Core)).1 := by
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val, uPointElec217Core_eq_diagonal,
      QRegister.embedMatrix_diagonal]
    exact preservesOutside_diagonal rPG7 _
  have pFwd : PreservesOutside rPG7 (rAct.embedUnitary uPhiHeldZ18Cat).1 := by
    unfold uPhiHeldZ18Cat
    simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
    exact preservesOutside_mul pElec (preservesOutside_mul pSum (preservesOutside_mul p1
      (preservesOutside_mul p2 (preservesOutside_mul p3 (preservesOutside_mul p4 p5)))))
  exact ⟨pFwd, by rw [QRegister.embedUnitary_inv]; exact preservesOutside_inv pFwd⟩
set_option maxHeartbeats 1600000 in
-- Case-split over 7 hybrid packing offsets across 6 bits.
open Classical in
theorem basisBits6_packHybrid6_eq (z : Fin 64) (s : Fin 128) (c : ℕ) (q : Fin 6) :
    (basisBits 6 (packHybrid6 z s c) q).val =
      if q.val < c then StageAPointPhase128OnStep.bit7 s ⟨q.val, by have := q.isLt; omega⟩
      else bit6 z q := by
  have hb7 (k : Fin 7) : StageAPointPhase128OnStep.bit7 s k < 2 := Nat.mod_lt _ (by decide)
  have hb6 (r : Fin 6) : bit6 z r < 2 := Nat.mod_lt _ (by decide)
  have h0 := hb7 0; have h1 := hb7 1; have h2 := hb7 2
  have h3 := hb7 3; have h4 := hb7 4; have h5 := hb7 5
  have g0 := hb6 0; have g1 := hb6 1; have g2 := hb6 2
  have g3 := hb6 3; have g4 := hb6 4; have g5 := hb6 5
  have hVal : ∀ (u : Fin 64) (r : Fin 6), (basisBits 6 u r).val = (u.val / 2 ^ r.val) % 2 := by
    decide
  rw [hVal (packHybrid6 z s c) q]
  change (StageAPointPhase128OnStep.packHybrid6Nat z s c / 2 ^ q.val) % 2 = _
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ 6 ≤ c) with
    rfl | rfl | rfl | rfl | rfl | rfl | hc6
  all_goals
    fin_cases q
    · change (StageAPointPhase128OnStep.packHybrid6Nat z s _ / 1) % 2 =
        if 0 < _ then StageAPointPhase128OnStep.bit7 s 0 else bit6 z 0
      unfold StageAPointPhase128OnStep.packHybrid6Nat; split_ifs <;> omega
    · change (StageAPointPhase128OnStep.packHybrid6Nat z s _ / 2) % 2 =
        if 1 < _ then StageAPointPhase128OnStep.bit7 s 1 else bit6 z 1
      unfold StageAPointPhase128OnStep.packHybrid6Nat; split_ifs <;> omega
    · change (StageAPointPhase128OnStep.packHybrid6Nat z s _ / 4) % 2 =
        if 2 < _ then StageAPointPhase128OnStep.bit7 s 2 else bit6 z 2
      unfold StageAPointPhase128OnStep.packHybrid6Nat; split_ifs <;> omega
    · change (StageAPointPhase128OnStep.packHybrid6Nat z s _ / 8) % 2 =
        if 3 < _ then StageAPointPhase128OnStep.bit7 s 3 else bit6 z 3
      unfold StageAPointPhase128OnStep.packHybrid6Nat; split_ifs <;> omega
    · change (StageAPointPhase128OnStep.packHybrid6Nat z s _ / 16) % 2 =
        if 4 < _ then StageAPointPhase128OnStep.bit7 s 4 else bit6 z 4
      unfold StageAPointPhase128OnStep.packHybrid6Nat; split_ifs <;> omega
    · change (StageAPointPhase128OnStep.packHybrid6Nat z s _ / 32) % 2 =
        if 5 < _ then StageAPointPhase128OnStep.bit7 s 5 else bit6 z 5
      unfold StageAPointPhase128OnStep.packHybrid6Nat; split_ifs <;> omega
theorem zWire_lt_kHeldZ18Sys (w : Fin 3) (q : Fin 6) :
    (fullSysCoreWires 80 + 42) + (6 * w.val + q.val) < kHeldZ18Sys := by
  have := w.isLt; have := q.isLt; dsimp [kHeldZ18Sys]; omega
theorem sWire_lt_kHeldZ18Sys (w : Fin 3) (k : Fin 7) :
    fullSysCoreWires 80 + (14 * w.val + k.val) < kHeldZ18Sys := by
  have := w.isLt; have := k.isLt; dsimp [kHeldZ18Sys]; omega
open Classical in
theorem extract_selHybridHeldZ18Sys_eq_packHybrid6
    (x : Fin (2 ^ kHeldZ18Sys)) (c : ℕ) (w : Fin 3) :
    let ξ := basisBits kHeldZ18Sys x
    let z_w : Fin 64 := ⟨bitsVal (fun q : Fin 6 ↦
      ξ ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + q.val),
      zWire_lt_kHeldZ18Sys w q⟩), bitsVal_lt_two_pow _⟩
    let s_w : Fin 128 := ⟨bitsVal (fun k : Fin 7 ↦ ξ ⟨fullSysCoreWires 80 + (14 * w.val + k.val),
      sWire_lt_kHeldZ18Sys w k⟩), bitsVal_lt_two_pow _⟩
    let γ := basisBits (3924 + 3) ((selHybridHeldZ18Sys c).extractIndex x)
    ((basisBitsEquiv 6).symm fun q : Fin 6 ↦ γ ⟨6 * w.val + q.val, by
      have := w.isLt; have := q.isLt; omega⟩) =
      packHybrid6 z_w s_w c := by
  intro ξ z_w s_w γ
  have hz_b : ∀ r : Fin 6, (ξ ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + r.val),
      zWire_lt_kHeldZ18Sys w r⟩).val = bit6 z_w r := fun r ↦ by
    have hb : (fun i : Fin 6 ↦ ξ ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + i.val),
        zWire_lt_kHeldZ18Sys w i⟩) = basisBits 6 z_w := (basisBits6_bitsVal _).symm
    have hr := congrFun hb r
    rw [hr]; exact basisBits6_val_eq_bit6 z_w r
  have hs_b : ∀ k : Fin 7, (ξ ⟨fullSysCoreWires 80 + (14 * w.val + k.val),
      sWire_lt_kHeldZ18Sys w k⟩).val =
      StageAPointPhase128OnStep.bit7 s_w k := fun k ↦ by
    have hb : (fun i : Fin 7 ↦ ξ ⟨fullSysCoreWires 80 + (14 * w.val + i.val),
        sWire_lt_kHeldZ18Sys w i⟩) = basisBits 7 s_w := (basisBits7_bitsVal _).symm
    have hk := congrFun hb k
    rw [hk]; exact basisBits7_val_eq_bit7 s_w k
  rw [Equiv.symm_apply_eq]
  change (fun q : Fin 6 ↦ γ ⟨6 * w.val + q.val, by have := w.isLt; have := q.isLt; omega⟩) =
    basisBits 6 (packHybrid6 z_w s_w c)
  funext q
  apply ZMod.val_injective
  rw [basisBits6_packHybrid6_eq z_w s_w c q]
  dsimp only [γ]
  rw [QRegister.basisBits_extractIndex (selHybridHeldZ18Sys c)]
  have hi_lt : 6 * w.val + q.val < 18 := by have := w.isLt; have := q.isLt; omega
  have hdiv : (6 * w.val + q.val) / 6 = w.val := by have := q.isLt; omega
  have hmod : (6 * w.val + q.val) % 6 = q.val := by have := q.isLt; omega
  by_cases hqc : q.val < c
  · have hWire : selHybridHeldZ18Sys c ⟨6 * w.val + q.val, by omega⟩ =
        ⟨fullSysCoreWires 80 + (14 * w.val + q.val), sWire_lt_kHeldZ18Sys w ⟨q.val, by
          have := q.isLt; omega⟩⟩ := by
      apply Fin.ext
      change selHybridHeldZ18Nat c (6 * w.val + q.val) = fullSysCoreWires 80 + (14 * w.val + q.val)
      unfold selHybridHeldZ18Nat
      rw [ite_eq_left hi_lt, hmod, ite_eq_left hqc, hdiv]; omega
    rw [ite_eq_left hqc, hWire]
    exact hs_b ⟨q.val, by have := q.isLt; omega⟩
  · have hWire : selHybridHeldZ18Sys c ⟨6 * w.val + q.val, by omega⟩ =
        ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + q.val), zWire_lt_kHeldZ18Sys w q⟩ := by
      apply Fin.ext
      change selHybridHeldZ18Nat c (6 * w.val + q.val) = (fullSysCoreWires 80 + 42) + (6 * w.val +
        q.val)
      unfold selHybridHeldZ18Nat
      rw [ite_eq_left hi_lt, hmod, ite_eq_right hqc]
    rw [ite_eq_right hqc, hWire, hz_b q]
set_option maxHeartbeats 1600000 in
-- Diagonal reduction across 3 held Z-axes and 64-entry hybrid table.
open Classical in
theorem uPhiHeldZ18Eff_eq_diagonal :
    uPhiHeldZ18Eff.1 =
      Matrix.diagonal fun x : Fin (2 ^ kHeldZ18Sys) ↦
        let ξ := basisBits kHeldZ18Sys x
        ∏ w : Fin 3,
          let z_w : Fin 64 := ⟨bitsVal (fun q : Fin 6 ↦
            ξ ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + q.val),
            zWire_lt_kHeldZ18Sys w q⟩), bitsVal_lt_two_pow _⟩
          let s_w : Fin 128 := ⟨bitsVal (fun k : Fin 7 ↦
            ξ ⟨fullSysCoreWires 80 + (14 * w.val + k.val),
            sWire_lt_kHeldZ18Sys w k⟩), bitsVal_lt_two_pow _⟩
          let u_w : Fin 217 → Fin 64 := fun e ↦
            u18GridEquiv ((rSpectatorSlot e).extractIndex (selCoreInHeldZ18Sys.extractIndex x)) w
          omega128 (StageAPointPhase128OnStep.pointCrossXorExp128 z_w s_w) *
            omega128 (StageAPointPhase128OnStep.pointSumCliffordExp128 z_w s_w) *
            omega128 (∑ e : Fin 217, StageAPointPhase128OnStep.pointElecCliffordExp128 (u_w e)) :=
              by
  have hW16 : ∀ (c : ℕ) (k : Fin 5),
      ((selHybridHeldZ18Sys c).embedUnitary (stageW16PrefixCanonStage128 3 hL3_le_654 k).uEff).1 =
        Matrix.diagonal fun x : Fin (2 ^ kHeldZ18Sys) ↦
          let ξ := basisBits kHeldZ18Sys x
          ∏ w : Fin 3,
            let z_w : Fin 64 := ⟨bitsVal (fun q : Fin 6 ↦
              ξ ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + q.val),
              zWire_lt_kHeldZ18Sys w q⟩), bitsVal_lt_two_pow _⟩
            let s_w : Fin 128 := ⟨bitsVal (fun r : Fin 7 ↦
              ξ ⟨fullSysCoreWires 80 + (14 * w.val + r.val),
              sWire_lt_kHeldZ18Sys w r⟩), bitsVal_lt_two_pow _⟩
            omega128 (w16Exp6 k (packHybrid6 z_w s_w c)) := by
    intro c k
    change ((selHybridHeldZ18Sys c).embedUnitary (axisProdPrefix 3 hL3_le_654 (fun _ ↦
      diag6Unitary (w16Exp6 k)))).1 = _
    rw [axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary, QRegister.embedUnitary_val,
      DyadicQft64.dyadicDiagUnitary, TrailXorAndRepairedStageAExactEq.embedMatrix_diagonal_eq]
    apply congrArg Matrix.diagonal; funext x
    rw [DyadicQft64.dyadicTurn_eq_omega128, omega128_finset_sum_assoc]
    refine Finset.prod_congr rfl fun w _ ↦ congrArg omega128 ?_
    have hw : w.val < 654 := by have := w.isLt; omega
    simp only [forestTermAxis, Nat.zero_add, hw, ↓reduceDIte]
    exact congrArg (w16Exp6 k) (extract_selHybridHeldZ18Sys_eq_packHybrid6 x c w)
  have hFor : ∀ (c s tB : ℕ) (cfg : ForestSlotConfig s) (φ6 : Fin 64 → ℤ)
      (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u)
      (hs : s ≤ 3) (hL : 1 ≤ 3) (hoff : 0 + 3 ≤ 654) (hwMax : xorForestBatchWork s cfg 3 ≤ 128)
      (htB : xorForestBatchTCost s cfg 3 = tB),
      ((selHybridHeldZ18Sys c).embedUnitary
        (xorForestBatchExpStage128 s 0 3 tB cfg φ6 hφ6 hs hL hoff hwMax htB).uEff).1 =
        Matrix.diagonal fun x : Fin (2 ^ kHeldZ18Sys) ↦
          let ξ := basisBits kHeldZ18Sys x
          ∏ w : Fin 3,
            let z_w : Fin 64 := ⟨bitsVal (fun q : Fin 6 ↦
              ξ ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + q.val),
              zWire_lt_kHeldZ18Sys w q⟩), bitsVal_lt_two_pow _⟩
            let s_w : Fin 128 := ⟨bitsVal (fun r : Fin 7 ↦
              ξ ⟨fullSysCoreWires 80 + (14 * w.val + r.val),
              sWire_lt_kHeldZ18Sys w r⟩), bitsVal_lt_two_pow _⟩
            omega128 (φ6 (packHybrid6 z_w s_w c)) := by
    intro c s tB cfg φ6 hφ6 hs hL hoff hwMax htB
    change ((selHybridHeldZ18Sys c).embedUnitary (DyadicQft64.dyadicDiagUnitary (3924 + 3) 7 _)).1 =
      _
    rw [QRegister.embedUnitary_val, DyadicQft64.dyadicDiagUnitary,
      TrailXorAndRepairedStageAExactEq.embedMatrix_diagonal_eq]
    apply congrArg Matrix.diagonal; funext x
    rw [DyadicQft64.dyadicTurn_eq_omega128, omega128_finset_sum_assoc]
    refine Finset.prod_congr rfl fun w _ ↦ congrArg omega128 ?_
    have hw : w.val < 654 := by have := w.isLt; omega
    simp only [forestTermAxis, Nat.zero_add, hw, ↓reduceDIte]
    exact congrArg φ6 (extract_selHybridHeldZ18Sys_eq_packHybrid6 x c w)
  have hSumEq : (selZ18Sum42InHeldZ18Sys.embedUnitary uPointSumClifford60).1 =
      Matrix.diagonal fun x : Fin (2 ^ kHeldZ18Sys) ↦
        let ξ := basisBits kHeldZ18Sys x
        ∏ w : Fin 3,
          let z_w : Fin 64 := ⟨bitsVal (fun q : Fin 6 ↦
            ξ ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + q.val),
            zWire_lt_kHeldZ18Sys w q⟩), bitsVal_lt_two_pow _⟩
          let s_w : Fin 128 := ⟨bitsVal (fun r : Fin 7 ↦
            ξ ⟨fullSysCoreWires 80 + (14 * w.val + r.val),
            sWire_lt_kHeldZ18Sys w r⟩), bitsVal_lt_two_pow _⟩
          omega128 (StageAPointPhase128OnStep.pointSumCliffordExp128 z_w s_w) := by
    rw [QRegister.embedUnitary_val, uPointSumClifford60,
      TrailXorAndRepairedStageAExactEq.embedMatrix_diagonal_eq]
    apply congrArg Matrix.diagonal; funext x
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    have hZ : (fun r : Fin 6 ↦ basisBits (18 + 42) (selZ18Sum42InHeldZ18Sys.extractIndex x)
        ⟨6 * w.val + r.val, by have := w.isLt; have := r.isLt; omega⟩) =
        fun r : Fin 6 ↦ basisBits kHeldZ18Sys x ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + r.val),
          zWire_lt_kHeldZ18Sys w r⟩ := by
      funext r
      rw [QRegister.basisBits_extractIndex selZ18Sum42InHeldZ18Sys]
      exact congrArg (basisBits kHeldZ18Sys x) (Fin.ext (by
        have := w.isLt; have := r.isLt
        dsimp [selZ18Sum42InHeldZ18Sys]; rw [dite_eq_left (by omega)]))
    have hS : (fun k : Fin 7 ↦ basisBits (18 + 42) (selZ18Sum42InHeldZ18Sys.extractIndex x)
        ⟨18 + 14 * w.val + k.val, by have := w.isLt; have := k.isLt; omega⟩) =
        fun k : Fin 7 ↦ basisBits kHeldZ18Sys x ⟨fullSysCoreWires 80 + (14 * w.val + k.val),
          sWire_lt_kHeldZ18Sys w k⟩ := by
      funext k
      rw [QRegister.basisBits_extractIndex selZ18Sum42InHeldZ18Sys]
      exact congrArg (basisBits kHeldZ18Sys x) (Fin.ext (by
        have := w.isLt; have := k.isLt
        dsimp [selZ18Sum42InHeldZ18Sys]; rw [dite_eq_right (by omega)]; dsimp only; omega))
    have hZFin : (⟨bitsVal (fun r : Fin 6 ↦
      basisBits (18 + 42) (selZ18Sum42InHeldZ18Sys.extractIndex x)
        ⟨6 * w.val + r.val, by
          have := w.isLt; have := r.isLt; omega⟩), bitsVal_lt_two_pow _⟩ : Fin 64) =
        ⟨bitsVal (fun r : Fin 6 ↦
          basisBits kHeldZ18Sys x ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + r.val),
          zWire_lt_kHeldZ18Sys w r⟩), bitsVal_lt_two_pow _⟩ :=
      Fin.ext (congrArg bitsVal hZ)
    have hSFin : (⟨bitsVal (fun k : Fin 7 ↦
      basisBits (18 + 42) (selZ18Sum42InHeldZ18Sys.extractIndex x)
        ⟨18 + 14 * w.val + k.val, by
          have := w.isLt; have := k.isLt; omega⟩), bitsVal_lt_two_pow _⟩ : Fin 128) =
        ⟨bitsVal (fun k : Fin 7 ↦
          basisBits kHeldZ18Sys x ⟨fullSysCoreWires 80 + (14 * w.val + k.val),
          sWire_lt_kHeldZ18Sys w k⟩), bitsVal_lt_two_pow _⟩ :=
      Fin.ext (congrArg bitsVal hS)
    dsimp only; rw [hZFin, hSFin]
  have hElecEq : (selCoreInHeldZ18Sys.embedUnitary uPointElec217Core).1 = Matrix.diagonal fun
      x : Fin (2 ^ kHeldZ18Sys) ↦ ∏ w : Fin 3, omega128 (∑ e : Fin 217,
      StageAPointPhase128OnStep.pointElecCliffordExp128 (u18GridEquiv
      ((rSpectatorSlot e).extractIndex (selCoreInHeldZ18Sys.extractIndex x)) w)) := by
    rw [QRegister.embedUnitary_val, uPointElec217Core_eq_diagonal,
      TrailXorAndRepairedStageAExactEq.embedMatrix_diagonal_eq]
  unfold uPhiHeldZ18Eff stagePointCrossExpC5 stagePointCrossExpC4 stagePointCrossExpC3
    stagePointCrossExpC2 stagePointCrossExpC1 CanonStageSpec128.seq
  simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, hElecEq, hSumEq,
    hW16 5 4, hW16 4 3, hW16 3 2, hW16 2 1, hW16 1 0,
    hFor 4 3 10 forestCfg3 forestExp3 forestCfg3_exp_eq (by
      decide) (by decide) (by decide) (by decide) (by decide),
    hFor 3 2 27 forestCfg2 forestExp2 forestCfg2_exp_eq (by
      decide) (by decide) (by decide) (by decide) (by decide),
    hFor 2 1 39 forestCfg1 forestExp1 forestCfg1_exp_eq (by
      decide) (by decide) (by decide) (by decide) (by decide),
    hFor 1 0 26 forestCfg0 forestExp0 forestCfg0_exp_eq (by
      decide) (by decide) (by decide) (by decide) (by decide),
    diagonal_mul_diagonal_op_assoc]
  apply congrArg Matrix.diagonal; funext x
  simp only [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [StageAPointPhase128OnStep.pointCrossXorExp128_eq_sum_hybrid_stages]
  unfold hybridStageExp5 hybridStageExp4 hybridStageExp3 hybridStageExp2 hybridStageExp1
  simp only [omega128_add]
  ring
end PointPhaseHeldZ18
end Part2_Target18AndPointPhiSave0
end HeadAndPhi
attribute [local reducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
open DyadicQft64WalkCircuit (disjoint_block_sep)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open HeldRSum42TwistQftPass2Stitch (axisProdPrefix stageHPrefixCanonStage128)
open FullSysCatSegmentBridge (fullSysQftCoreUnitary)
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside)
open NuclearTwistRealizes (embedUnitary_idReg_eq)
open InterWalkRSum42Hoist (E_rawStream42 streamProjOp)
open Barrel3PassSelectStitch (uTrailCliffordXor80)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6)
open OriginZeroHeadMod4Circuit14900 (uQft0)
open TwistStreamEliminationAux (spectatorSum217_le_13671)
open Slot0SubAdd14And217Stream (slot0AxisVal uSlot0AxisAdd14 slot0AxisAddSub14_mod_eq_iff)
open StageAPointPhase128OnStep (pStream42Of stageHPrefix128_uEff)
open ZeroHypStageABToUFoldedPass123SegAndCompac (rElec18InCore uHeadPhase80Mod4Eff)
open TrailXorAndRepairedStageAExactEq (embedMatrix_diagonal_eq uControlledPointDiag217)
abbrev embedMatrix_diagonal_local := @embedMatrix_diagonal_eq
theorem rSpectatorElec3906InCore_val_assoc (idx : Fin 3906) :
    (rSpectatorElec3906InCore idx).val = 18 + idx.val := by
  simp [rSpectatorElec3906InCore]
open Classical in
theorem agreeOutside_rSpectatorElec3906InCore_nonSpec {x y : Fin (2 ^ posCoreWires)}
    (hOut : rSpectatorElec3906InCore.AgreeOutside x y) {w : Wire posCoreWires}
    (hw : w.val < 18 ∨ 3924 ≤ w.val) : basisBits posCoreWires x w = basisBits posCoreWires y w
    := by
  refine hOut w ?_
  rintro ⟨i, hi⟩
  have hv : 18 + i.val = w.val := by
    rw [← rSpectatorElec3906InCore_val_assoc i]
    exact congrArg Fin.val hi
  have := i.isLt
  omega
open Classical in
theorem rSpectatorSlot_agreeOutside_imp_rSpectator3906_assoc (e : Fin 217)
    {x y : Fin (2 ^ posCoreWires)} (hOut : (rSpectatorSlot e).AgreeOutside x y) :
    rSpectatorElec3906InCore.AgreeOutside x y := by
  intro w hw
  refine hOut w ?_
  rintro ⟨q, rfl⟩
  refine hw ⟨⟨18 * e.val + q.val, by have := e.isLt; have := q.isLt; omega⟩, ?_⟩
  apply Fin.ext
  have h1 := rSpectatorElec3906InCore_val_assoc ⟨18 * e.val + q.val, by
    have := e.isLt; have := q.isLt; omega⟩
  have h2 : (rSpectatorSlot e q).val = 18 * (e.val + 1) + q.val :=
    PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ q
  rw [h1, h2]
  ring
theorem list_unitary_prod_comm_mat_assoc {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℂ) :
    ∀ (L : List (Unitary D)),
      (∀ u ∈ L, u.1 * M = M * u.1) →
      (L.prod).1 * M = M * (L.prod).1
  | [], _ => by simp
  | u :: us, h => by
      simp only [List.prod_cons, Submonoid.coe_mul]
      calc u.1 * (us.prod).1 * M
          = u.1 * ((us.prod).1 * M) := by simp only [Matrix.mul_assoc]
        _ = u.1 * (M * (us.prod).1) := by
            rw [list_unitary_prod_comm_mat_assoc M us (fun v hv ↦ h v (List.mem_cons_of_mem u hv))]
        _ = (u.1 * M) * (us.prod).1 := by simp only [Matrix.mul_assoc]
        _ = M * (u.1 * (us.prod).1) := by
            rw [h u List.mem_cons_self]; simp only [Matrix.mul_assoc]
open Classical in
theorem elecProd217_comm_diagonal_of_agreeOutside (U_e : Fin 217 → Unitary (2 ^ 18))
    (f : Fin (2 ^ posCoreWires) → ℂ) (hf : ∀ x y : Fin (2 ^ posCoreWires),
    rSpectatorElec3906InCore.AgreeOutside x y → f x = f y) : (elecProd217 U_e).1 *
    Matrix.diagonal f = Matrix.diagonal f * (elecProd217 U_e).1 := by
  unfold elecProd217
  refine list_unitary_prod_comm_mat_assoc (Matrix.diagonal f) _ fun u hu ↦ ?_
  rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩
  rw [QRegister.embedUnitary_val]
  exact embedMatrix_comm_diagonal_of_outside (rSpectatorSlot e) (U_e e).1 f
    (fun x y hOut ↦ hf x y (rSpectatorSlot_agreeOutside_imp_rSpectator3906_assoc e hOut))
theorem headTargetCoord64_congr_outside_spec_and_wTh {β₁ β₂ : BitAssignment posCoreWires} (hS0
    : β₁ (wSlot0Core (QRegExt.ofFin posCoreWires)) = β₂ (wSlot0Core (QRegExt.ofFin
    posCoreWires))) (hFine : ∀ q : Fin 21, β₁ (rHeadFine21 (QRegExt.ofFin posCoreWires) q) =
    β₂ (rHeadFine21 (QRegExt.ofFin posCoreWires) q)) (hElec0 : ∀ q : Fin 18, β₁ (rElecSlot
    (QRegExt.ofFin posCoreWires) 0 q) = β₂ (rElecSlot (QRegExt.ofFin posCoreWires) 0 q))
    (hB0 : ∀ q : Fin 3, β₁ (rCosetB0 (QRegExt.ofFin posCoreWires) q) = β₂ (rCosetB0
    (QRegExt.ofFin posCoreWires) q)) : slotSubGridCoord64
    (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₁ = slotSubGridCoord64
    (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₂ ∧ headTargetCoord64 β₁ = headTargetCoord64
    β₂ := by
  let rCore := QRegExt.ofFin posCoreWires
  have hy0 : slotSubGridCoord64 (rElecSlot rCore 0) β₁ =
      slotSubGridCoord64 (rElecSlot rCore 0) β₂ := by
    funext w; apply Fin.ext
    change bitsVal (fun j : Fin 6 ↦ β₁ (axisBitRev6 (rElecSlot rCore 0) w j)) =
      bitsVal (fun j : Fin 6 ↦ β₂ (axisBitRev6 (rElecSlot rCore 0) w j))
    unfold bitsVal
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hq := hElec0 ⟨6 * w.val + (5 - j.val), by omega⟩
    exact congrArg (·.val * 2 ^ j.val) hq
  have hd : fineCoordOfReg21 (rHeadFine21 rCore) β₁ =
      fineCoordOfReg21 (rHeadFine21 rCore) β₂ := by
    funext w; apply Fin.ext
    change regVal ((rHeadFine21 rCore).slice (7 * w.val) 7 _) β₁ =
      regVal ((rHeadFine21 rCore).slice (7 * w.val) 7 _) β₂
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hq := hFine ⟨7 * w.val + j.val, by omega⟩
    exact congrArg (·.val * 2 ^ j.val) hq
  have hb0 : parity3OfReg (rCosetB0 rCore) β₁ = parity3OfReg (rCosetB0 rCore) β₂ := by
    funext w
    change (β₁ (rCosetB0 rCore w) == 1) = (β₂ (rCosetB0 rCore w) == 1)
    rw [hB0 w]
  have hs0 : headS0Bool β₁ = headS0Bool β₂ := by
    unfold headS0Bool; rw [hS0]
  refine ⟨hy0, ?_⟩
  funext w; apply Fin.ext
  unfold headTargetCoord64
  dsimp only [rCore] at hy0 hd hb0 ⊢
  rw [hs0]
  cases headS0Bool β₂
  · simp only [Bool.not_false, ↓reduceIte]; rw [hd]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rw [hd, hy0, hb0]
theorem unitary_inv_comm_of_comm {D : ℕ} {U V : Unitary D}
    (h : U * V = V * U) : U⁻¹ * V = V * U⁻¹ := by
  calc U⁻¹ * V = U⁻¹ * (V * U) * U⁻¹ := by simp only [_root_.mul_assoc, mul_inv_cancel, mul_one]
    _ = U⁻¹ * (U * V) * U⁻¹ := by rw [← h]
    _ = V * U⁻¹ := by simp only [← _root_.mul_assoc, inv_mul_cancel, one_mul]
-- Aliases bridging Section 2 `*XorTarget18` names to Section 3 `*XorZTarget18` names
noncomputable abbrev uXorZTarget18 := uXorTarget18
abbrev uXorZTarget18_mul_self := uXorTarget18_mul_self
abbrev ket_embedUnitary_uXorZTarget18 := @ket_embedUnitary_uXorTarget18
/-- Explicit-`PreservesOutside` 6-stage 1-electron Hadamard-Forest `QFT_64` `CanonStageSpec128`
  (`117 T`, `TOFF = 0`). -/
noncomputable def rawActiveOneElecExpQftStage128 : CanonStageSpec128 :=
  (((stageHPrefixCanonStage128 3 hL3_le_654 5).seq stagePointCrossExpC5).seq
    (((stageHPrefixCanonStage128 3 hL3_le_654 4).seq stagePointCrossExpC4).seq
      (((stageHPrefixCanonStage128 3 hL3_le_654 3).seq stagePointCrossExpC3).seq
        (((stageHPrefixCanonStage128 3 hL3_le_654 2).seq stagePointCrossExpC2).seq
          (((stageHPrefixCanonStage128 3 hL3_le_654 1).seq stagePointCrossExpC1).seq
            (stageHPrefixCanonStage128 3 hL3_le_654 0))))))
theorem rawActiveOneElecExpQftStage128_uEff_eq :
    rawActiveOneElecExpQftStage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6) := by
  unfold rawActiveOneElecExpQftStage128 stagePointCrossExpC5 stagePointCrossExpC4
    stagePointCrossExpC3 stagePointCrossExpC2 stagePointCrossExpC1
  simp only [stage128_seq_uEff, stageHPrefix128_uEff, stageW16Prefix128_uEff,
    xorForestBatchExpStage128_three_uEff,
    StageAPointPhase128OnStep.axisProdPrefix_mul]
  exact congrArg (fun u6 ↦ axisProdPrefix 3 hL3_le_654 (fun _ ↦ u6))
    StageAPointPhase128OnStep.forest6_eq_orig6
/-- Complete `117-T` 1-electron Hadamard-Forest `QFT_64` `CanonStageSpec128` exposing
  `PreservesOutside rPG7`
on every catalyzed cross stage (`activeOneElecExpQftStage128.uEff =
activeOneElecForestFullQftStage128.uEff`). -/
noncomputable def activeOneElecExpQftStage128 : CanonStageSpec128 :=
  rawActiveOneElecExpQftStage128.congr
    (uEff' := axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6))
    (tCost' := 117)
    rawActiveOneElecExpQftStage128_uEff_eq
    rfl
@[simp] theorem activeOneElecExpQftStage128_tCost : activeOneElecExpQftStage128.tCost = 117 := by
  unfold activeOneElecExpQftStage128 CanonStageSpec128.congr
  rfl
@[simp] theorem activeOneElecExpQftStage128_uEff :
    activeOneElecExpQftStage128.uEff = activeOneElecForestFullQftStage128.uEff := by
  unfold activeOneElecExpQftStage128 activeOneElecForestFullQftStage128 CanonStageSpec128.congr
  rfl
theorem cSwapCore3967_counts : cSwapCore3967.count TOFF = 0 ∧ cSwapCore3967.count T = 0 := by
  decide
theorem uSwapCore3967_eq_eval : uSwapCore3967 = cSwapCore3967.eval := by
  rw [uSwapCore3967, lockPosPostVal_eq]
/-- High 110-wire slice `[3924 .. 4034)` inside `fullSysCoreWires 80`. -/
def rHigh110InCoreFA : QRegister 110 (fullSysCoreWires 80) :=
  QRegister.block 3924 110 (by decide)
open Classical in
theorem uSwapCore3967_eq_embed_rHigh110 :
    uSwapCore3967 =
      rHigh110InCoreFA.embedUnitary
        ((PosPostPrep80MergedVep.cSwap2 ⟨43, by decide⟩ ⟨105, by decide⟩ (by decide)).eval) := by
  have hOnReg :
      (PosPostPrep80MergedVep.cSwap2 ⟨43, by decide⟩ ⟨105, by decide⟩ (by
        decide)).onRegister rHigh110InCoreFA =
        cSwapCore3967 := by
    unfold PosPostPrep80MergedVep.cSwapCore3967 PosPostPrep80MergedVep.cSwap2
    simp only [Circuit.onRegister, Circuit.seq.injEq, Circuit.gate.injEq, heq_eq_eq, true_and,
      rHigh110InCoreFA]
    refine ⟨?_, ?_, ?_⟩ <;>
      (apply qreg_ext; intro i; fin_cases i <;> decide)
  rw [uSwapCore3967_eq_eval, ← hOnReg, Circuit.eval_onRegister]
open Classical in
theorem rElec18InCore80_disj_rHigh110 (i : Fin 218) :
    (rElec18InCore pos24_6_le_80 i).DisjointWires rHigh110InCoreFA := by
  rw [QRegister.disjoint_iff]
  intro q k hqk
  have hv := congrArg Fin.val hqk
  rw [ZeroHypStageABToUFoldedPass123SegAndCompac.rElec18InCore_apply_val] at hv
  have h2 : (rHigh110InCoreFA k).val = 3924 + k.val := by
    simp [rHigh110InCoreFA]
  rw [h2] at hv
  have := i.isLt; have := q.isLt
  omega
open Classical in
/-- **Zero-Hypothesis `unitaryConj` Reduction for `uHeadPhase80Mod4Eff` under Both `Q_{218}` and
`QC = Q_{218} * uTrailCliffordXor80` (`unitaryConj_qftCore_and_QC_uHeadPhase80Mod4Eff_eq_zeroHyp`,
`0 sorry`)**:
Proves unconditionally (`0` hypotheses):
1. `unitaryConj Q_{218} uHeadPhase80Mod4Eff` equals conjugating
   `selPosCoreInCore80.embedUnitary (uQft0⁻¹ * ((uControlledPointDiag217)⁻¹ * ((uHad217)⁻¹ *
   uHeadPhaseMod4Origin0Repaired * uHad217) * uControlledPointDiag217) * uQft0)`
   by the 3-CNOT `uSwapCore3967`, and
2. `unitaryConj (Q_{218} * uTrailCliffordXor80) uHeadPhase80Mod4Eff = unitaryConj
uTrailCliffordXor80 (unitaryConj Q_{218} uHeadPhase80Mod4Eff)`. -/
theorem unitaryConj_qftCore_and_QC_uHeadPhase80Mod4Eff_eq_zeroHyp :
    let Q := fullSysQftCoreUnitary pos24_6_le_80 coreQftHadamardPrunedBundle128
    let QC := Q * uTrailCliffordXor80
    let M_core := selPosCoreInCore80.embedUnitary (uQft0⁻¹ * ((uControlledPointDiag217)⁻¹ *
        ((uHad217)⁻¹ * uHeadPhaseMod4Origin0Repaired * uHad217) * uControlledPointDiag217) *
        uQft0)
    unitaryConj Q uHeadPhase80Mod4Eff = (uSwapCore3967 * M_core) * uSwapCore3967 ∧
    unitaryConj QC uHeadPhase80Mod4Eff =
      uTrailCliffordXor80⁻¹ * ((uSwapCore3967 * M_core) * uSwapCore3967) * uTrailCliffordXor80 := by
  intro Q QC M_core
  have h1 : unitaryConj Q uHeadPhase80Mod4Eff = (uSwapCore3967 * M_core) * uSwapCore3967 := by
    dsimp only [Q, M_core]
    rw [← TrailXorAndRepairedStageAExactEq.uSpectatorHadamard3906_eq_uHad217]
    exact
      TrailXorAndRepairedStageAExactEq.unitaryConj_qftCore218_uHeadPhase80Mod4Eff_eq_zeroHyp.2.2.1
  refine ⟨h1, ?_⟩
  dsimp only [QC]
  unfold unitaryConj at h1 ⊢
  rw [_root_.mul_inv_rev]
  calc (uTrailCliffordXor80⁻¹ * Q⁻¹) * uHeadPhase80Mod4Eff * (Q * uTrailCliffordXor80)
      = uTrailCliffordXor80⁻¹ * (Q⁻¹ * uHeadPhase80Mod4Eff * Q) * uTrailCliffordXor80 := by
          simp only [_root_.mul_assoc]
    _ = uTrailCliffordXor80⁻¹ * ((uSwapCore3967 * M_core) * uSwapCore3967) * uTrailCliffordXor80 :=
      by
          rw [h1]
section Part3_StageAConcreteCircuitsAndStreamBridge
section CleanPrefixAbsorb
/-- Prefix active block `[0 .. kAct)` inside `kAct + kZ`. -/
def rActLoc (kAct kZ : ℕ) : QRegister kAct (kAct + kZ) := QRegister.block 0 kAct (by omega)
/-- Suffix clean-ancilla block `[kAct .. kAct + kZ)` inside `kAct + kZ`. -/
def rZLoc (kAct kZ : ℕ) : QRegister kZ (kAct + kZ) := QRegister.block kAct kZ le_rfl
theorem rActLoc_disj_rZLoc (kAct kZ : ℕ) : (rActLoc kAct kZ).DisjointWires (rZLoc kAct kZ) :=
    disjoint_block_sep (Or.inl (by omega))
/-- Combine an active index `x : Fin (2 ^ kAct)` and ancilla index `z : Fin (2 ^ kZ)` in `Fin (2
  ^ (kAct + kZ))`. -/
def joinAZ {kAct kZ : ℕ} (x : Fin (2 ^ kAct)) (z : Fin (2 ^ kZ)) : Fin (2 ^ (kAct + kZ)) :=
  (rZLoc kAct kZ).replaceIndex ((rActLoc kAct kZ).replaceIndex 0 x) z
@[simp] theorem extract_rActLoc_joinAZ {kAct kZ : ℕ} (x : Fin (2 ^ kAct)) (z : Fin (2 ^ kZ)) :
    (rActLoc kAct kZ).extractIndex (joinAZ x z) = x := by
  rw [joinAZ, QRegister.extractIndex_replaceIndex_of_disjoint _ _ (rActLoc_disj_rZLoc kAct kZ),
    QRegister.extractIndex_replaceIndex]
@[simp] theorem extract_rZLoc_joinAZ {kAct kZ : ℕ} (x : Fin (2 ^ kAct)) (z : Fin (2 ^ kZ)) :
    (rZLoc kAct kZ).extractIndex (joinAZ x z) = z := by
  rw [joinAZ, QRegister.extractIndex_replaceIndex]
theorem joinAZ_extract_self {kAct kZ : ℕ} (a : Fin (2 ^ (kAct + kZ))) :
    joinAZ ((rActLoc kAct kZ).extractIndex a) ((rZLoc kAct kZ).extractIndex a) = a := by
  apply (basisBitsEquiv (kAct + kZ)).injective
  funext q
  change basisBits (kAct + kZ) (joinAZ _ _) q = basisBits (kAct + kZ) a q
  by_cases hq : q.val < kAct
  · let i : Fin kAct := ⟨q.val, hq⟩
    have hi : rActLoc kAct kZ i = q := Fin.ext (by simp [rActLoc, i])
    have hnZ : q ∉ Set.range (rZLoc kAct kZ).wires := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      simp [rZLoc] at hv; omega
    rw [joinAZ, (rZLoc kAct kZ).basisBits_replaceIndex_of_not_mem _ _ q hnZ,
      ← hi, (rActLoc kAct kZ).basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
  · let j : Fin kZ := ⟨q.val - kAct, by have := q.isLt; omega⟩
    have hj : rZLoc kAct kZ j = q := Fin.ext (by
      have := q.isLt; simp [rZLoc, j]; omega)
    rw [joinAZ, ← hj, (rZLoc kAct kZ).basisBits_replaceIndex_apply,
      QRegister.basisBits_extractIndex]
/-- Product-to-joint basis equivalence `Fin (2 ^ kAct) × Fin (2 ^ kZ) ≃ Fin (2 ^ (kAct + kZ))`. -/
def equivAZ (kAct kZ : ℕ) : Fin (2 ^ kAct) × Fin (2 ^ kZ) ≃ Fin (2 ^ (kAct + kZ)) where
  toFun p := joinAZ p.1 p.2
  invFun a := ((rActLoc kAct kZ).extractIndex a, (rZLoc kAct kZ).extractIndex a)
  left_inv p := Prod.ext (extract_rActLoc_joinAZ p.1 p.2) (extract_rZLoc_joinAZ p.1 p.2)
  right_inv a := joinAZ_extract_self a
theorem concat_extractIndex_eq_joinAZ {kAct kZ n : ℕ}
    (rAct : QRegister kAct n) (rZ : QRegister kZ n) (hAZ : rAct.DisjointWires rZ)
    (g : Fin (2 ^ n)) :
    (rAct.concat rZ hAZ).extractIndex g = joinAZ (rAct.extractIndex g) (rZ.extractIndex g) := by
  apply (basisBitsEquiv (kAct + kZ)).injective
  funext q
  change basisBits (kAct + kZ) ((rAct.concat rZ hAZ).extractIndex g) q =
    basisBits (kAct + kZ) (joinAZ (rAct.extractIndex g) (rZ.extractIndex g)) q
  rw [QRegister.basisBits_extractIndex]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) q
  · rw [QRegister.concat_apply_left]
    have hi : rActLoc kAct kZ i = Fin.castAdd kZ i := Fin.ext (by simp [rActLoc])
    have hnZ : Fin.castAdd kZ i ∉ Set.range (rZLoc kAct kZ).wires := by
      rintro ⟨j', hj'⟩; have hv := congrArg Fin.val hj'; simp [rZLoc] at hv; omega
    rw [joinAZ, (rZLoc kAct kZ).basisBits_replaceIndex_of_not_mem _ _ _ hnZ,
      ← hi, (rActLoc kAct kZ).basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
  · rw [QRegister.concat_apply_right]
    have hj : rZLoc kAct kZ j = Fin.natAdd kAct j := Fin.ext (by simp [rZLoc])
    rw [joinAZ, ← hj, (rZLoc kAct kZ).basisBits_replaceIndex_apply,
      QRegister.basisBits_extractIndex]
open Classical in
theorem offDiag_zero_of_comm_projZero {kAct kZ : ℕ} (uFull : Unitary (2 ^ (kAct + kZ))) (hComm
    : uFull.1 * (rZLoc kAct kZ).basisOutcomeProjector 0 = (rZLoc kAct
    kZ).basisOutcomeProjector 0 * uFull.1) (x y : Fin (2 ^ kAct)) {z : Fin (2 ^ kZ)}
    (hz : z ≠ 0) : uFull.1 (joinAZ x z) (joinAZ y 0) = 0 := by
  have h := congrFun (congrFun hComm (joinAZ x z)) (joinAZ y 0)
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    extract_rZLoc_joinAZ, extract_rZLoc_joinAZ, ite_eq_left rfl, ite_eq_right hz, mul_one,
    zero_mul] at h
  exact h
/-- Extract the restricted `kAct`-wire unitary on `{rZ = 0}` from any `(kAct + kZ)`-wire unitary
commuting with `(rZLoc kAct kZ).basisOutcomeProjector 0`. -/
def extractCleanAncillaUnitary {kAct kZ : ℕ} (uFull : Unitary (2 ^ (kAct + kZ))) (hComm :
    uFull.1 * (rZLoc kAct kZ).basisOutcomeProjector 0 = (rZLoc kAct kZ).basisOutcomeProjector
    0 * uFull.1) : Unitary (2 ^ kAct) :=
  ⟨Matrix.of fun x y ↦ uFull.1 (joinAZ x 0) (joinAZ y 0), by
    rw [Matrix.mem_unitaryGroup_iff']
    ext x y
    have hU :=
      congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp uFull.2) (joinAZ x 0)) (joinAZ y 0)
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.one_apply] at hU ⊢
    rw [← (equivAZ kAct kZ).sum_comp, Fintype.sum_prod_type] at hU
    simp only [equivAZ, Equiv.coe_fn_mk] at hU
    have hSum : (∑ w : Fin (2 ^ kAct), ∑ z : Fin (2 ^ kZ), star (uFull.1 (joinAZ w z) (joinAZ
        x 0)) * uFull.1 (joinAZ w z) (joinAZ y 0)) = ∑ w : Fin (2 ^ kAct), star
        (uFull.1 (joinAZ w 0) (joinAZ x 0)) * uFull.1 (joinAZ w 0) (joinAZ y 0) :=
      Finset.sum_congr rfl fun w _ ↦ Finset.sum_eq_single 0
        (fun z _ hz ↦ by rw [offDiag_zero_of_comm_projZero uFull hComm w y hz, mul_zero])
        (fun h0 ↦ (h0 (Finset.mem_univ 0)).elim)
    have hIte : (if joinAZ x (0 : Fin (2 ^ kZ)) = joinAZ y 0 then (1 : ℂ) else 0) =
        if x = y then 1 else 0 := by
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [ite_eq_right hxy, ite_eq_right (fun h ↦ hxy (by
          simpa using congrArg (rActLoc kAct kZ).extractIndex h))]
    exact hSum.symm.trans (hU.trans hIte)⟩
theorem extractCleanAncillaUnitary_apply {kAct kZ : ℕ} (uFull : Unitary (2 ^ (kAct + kZ)))
    (hComm : uFull.1 * (rZLoc kAct kZ).basisOutcomeProjector 0 = (rZLoc kAct
    kZ).basisOutcomeProjector 0 * uFull.1) (x y : Fin (2 ^ kAct)) :
    (extractCleanAncillaUnitary uFull hComm).1 x y = uFull.1 (joinAZ x 0) (joinAZ y 0) := rfl
open Classical in
theorem embedUnitary_extractCleanAncillaUnitary_mul_projZero {kAct kZ n : ℕ}
    (rAct : QRegister kAct n) (rZ : QRegister kZ n) (hAZ : rAct.DisjointWires rZ)
    (uFull : Unitary (2 ^ (kAct + kZ))) (hComm : uFull.1 * (rZLoc kAct
    kZ).basisOutcomeProjector 0 = (rZLoc kAct kZ).basisOutcomeProjector 0 * uFull.1) :
    ((rAct.concat rZ hAZ).embedUnitary uFull).1 * rZ.basisOutcomeProjector 0 =
    (rAct.embedUnitary (extractCleanAncillaUnitary uFull hComm)).1 * rZ.basisOutcomeProjector
    0 := by
  ext i j
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
    QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases hzj : rZ.extractIndex j = 0
  · rw [ite_eq_left hzj, mul_one, mul_one,
      QRegister.embedMatrix_apply_of_agreeOutside, QRegister.embedMatrix_apply_of_agreeOutside,
      concat_extractIndex_eq_joinAZ rAct rZ hAZ i, concat_extractIndex_eq_joinAZ rAct rZ hAZ j, hzj]
    by_cases hzi : rZ.extractIndex i = 0
    · rw [hzi]
      have hAg : (rAct.concat rZ hAZ).AgreeOutside i j ↔ rAct.AgreeOutside i j := by
        constructor
        · intro h q hq
          by_cases hqZ : q ∈ Set.range rZ.wires
          · obtain ⟨idx, rfl⟩ := hqZ
            rw [(QRegExt.extractIndex_eq_zero_iff rZ i).mp hzi idx,
              (QRegExt.extractIndex_eq_zero_iff rZ j).mp hzj idx]
          · refine h q fun ⟨u, hu⟩ ↦ ?_
            revert hu
            refine Fin.addCases (fun a hu ↦ hq ⟨a, ?_⟩) (fun b hu ↦ hqZ ⟨b, ?_⟩) u
            · simpa [QRegister.concat_apply_left] using hu
            · simpa [QRegister.concat_apply_right] using hu
        · intro h q hq
          exact h q fun ⟨a, ha⟩ ↦ hq ⟨Fin.castAdd kZ a, by rw [QRegister.concat_apply_left, ha]⟩
      rw [extractCleanAncillaUnitary_apply, hAg]
    · rw [offDiag_zero_of_comm_projZero uFull hComm _ _ hzi, zero_mul]
      have hnAg : ¬ rAct.AgreeOutside i j := fun hOut ↦ hzi <| by
        rw [← hzj]; apply (basisBitsEquiv kZ).injective; funext idx
        change basisBits kZ (rZ.extractIndex i) idx = basisBits kZ (rZ.extractIndex j) idx
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        exact hOut (rZ idx) (by rintro ⟨u, hu⟩; exact hAZ.ne u idx hu)
      rw [ite_eq_right hnAg, mul_zero]
  · rw [ite_eq_right hzj, mul_zero, mul_zero]
open Classical in
theorem embedMatrix_eq_of_mul_projZero_block {n kZ : ℕ} (A B : Operator (2 ^ n)) (hEq :
    (rActLoc n kZ).embedMatrix A * (rZLoc n kZ).basisOutcomeProjector 0 = (rActLoc n
    kZ).embedMatrix B * (rZLoc n kZ).basisOutcomeProjector 0) : A = B := by
  ext x y
  have h := congrFun (congrFun hEq (joinAZ x 0)) (joinAZ y 0)
  have hAg : (rActLoc n kZ).AgreeOutside (joinAZ x 0) (joinAZ y 0) := by
    intro q hq
    have hge : ¬ q.val < n := fun hlt ↦ hq ⟨⟨q.val, hlt⟩, Fin.ext (by simp [rActLoc])⟩
    let idx : Fin kZ := ⟨q.val - n, by have := q.isLt; omega⟩
    have hqZ : rZLoc n kZ idx = q := Fin.ext (by have := q.isLt; simp [rZLoc, idx]; omega)
    rw [← hqZ, joinAZ, joinAZ, (rZLoc n kZ).basisBits_replaceIndex_apply,
      (rZLoc n kZ).basisBits_replaceIndex_apply]
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal,
    extract_rZLoc_joinAZ, ite_eq_left rfl, mul_one, mul_one,
    QRegister.embedMatrix_apply_of_agreeOutside, QRegister.embedMatrix_apply_of_agreeOutside,
    extract_rActLoc_joinAZ, extract_rActLoc_joinAZ, ite_eq_left hAg, mul_one, mul_one] at h
  exact h
end CleanPrefixAbsorb
section Spec217Stream3Axis
open InterWalkRSum42Hoist (streamTarget42 basisBits_streamTarget42 streamProjOpGen
  streamProjOpGen_mulVec_basisKet E_rawStream42_eq_streamProjOp rAct0 rSum0 rCoreFull rCoreOrig
  hAct0_disj_Sum0 rawStreamVec h3924_actOrig rawStreamOfLow rawStreamOfLow_eq_slot2AxisSum
  low3924Bits isLow3924Prefix_rCoreOrig rSum14In42 kFull80 kActOrig)
/-- Transparent 3-axis 217-spectator stream unitary on `fullSysCoreWires 80 + 42` built directly
from per-axis `(3906 + 14)`-wire unitaries `uSpec w` (manifestly disjoint from Electron `0` and
all core wires `≥ 3924`). -/
noncomputable def uStr3AxisOfSpec (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  ((selCoreSum14In42 80 2).embedUnitary ((selSpec217InCoreSum14 80).embedUnitary (uSpec 2)) *
    (selCoreSum14In42 80 1).embedUnitary ((selSpec217InCoreSum14 80).embedUnitary (uSpec 1))) *
    (selCoreSum14In42 80 0).embedUnitary ((selSpec217InCoreSum14 80).embedUnitary (uSpec 0))
theorem rActLoc_concat_rZLoc_eq_idReg (kAct kZ : ℕ) : (rActLoc kAct kZ).concat (rZLoc kAct kZ)
    (rActLoc_disj_rZLoc kAct kZ) = QRegExt.idReg (kAct + kZ) := by
  apply qreg_ext; intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · rw [QRegister.concat_apply_left]; exact Fin.ext (by simp [QRegExt.idReg, rActLoc])
  · rw [QRegister.concat_apply_right]; exact Fin.ext (by simp [QRegExt.idReg, rZLoc])
/-- Projector onto `rSum42 = |0⟩` inside `fullSysCoreWires 80 + 42`. -/
noncomputable def pSum42CoreZero : Operator (2 ^ (fullSysCoreWires 80 + 42)) :=
  (rZLoc (fullSysCoreWires 80) 42).basisOutcomeProjector 0
/-- Canonical circuit-independent 42-wire stream partial isometry `|γ⟩|0⟩ ↦ |γ⟩|streamTarget42(sumFn
  · γ)⟩`
on `fullSysCoreWires 80 + 42`. -/
noncomputable def eStream42CoreOf (sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ) :
    Operator (2 ^ (fullSysCoreWires 80 + 42)) :=
  streamProjOpGen (rActLoc (fullSysCoreWires 80) 42) (rZLoc (fullSysCoreWires 80) 42)
    (fun a ↦ streamTarget42 (fun w ↦ sumFn w (basisBits (fullSysCoreWires 80) a)))
/-- 217-spectator canonical stream isometry (`rSum14(w) = spectatorSum217 w γ`) on
  `fullSysCoreWires 80 + 42`. -/
noncomputable def eStream217Core : Operator (2 ^ (fullSysCoreWires 80 + 42)) :=
  eStream42CoreOf spectatorSum217
/-- 218-electron canonical stream isometry (`rSum14(w) = slot2AxisSum w γ`) on `fullSysCoreWires
  80 + 42`. -/
noncomputable def eStream218Core : Operator (2 ^ (fullSysCoreWires 80 + 42)) :=
  eStream42CoreOf slot2AxisSum
theorem basisKet_eq_single_symm_assoc {n : ℕ} (β : BitAssignment n) :
    basisKet β = Pi.single ((basisBitsEquiv n).symm β) 1 := by
  ext y; simp [basisKet, basisState, Pi.single_apply]
theorem ket_eq_single_symm_assoc {n : ℕ} (β : BitAssignment n) :
    ket β = Pi.single ((basisBitsEquiv n).symm β) 1 := by
  ext y; simp [ket, basisState, Pi.single_apply]
theorem diagonal_mulVec_ket_assoc {n : ℕ} (d : Fin (2 ^ n) → ℂ) (β : BitAssignment n) :
    (Matrix.diagonal d).mulVec (ket β) = d ((basisBitsEquiv n).symm β) • ket β := by
  rw [ket_eq_single_symm_assoc, Matrix.diagonal_mulVec_single, mul_one]
  ext i; simp [Pi.smul_apply, Pi.single_apply]
theorem mulVec_ket_apply_assoc {n : ℕ} (M : Operator (2 ^ n)) (x y : Fin (2 ^ n)) :
    M x y = (M.mulVec (ket (basisBits n y))) x := by
  have hy : (basisBitsEquiv n).symm (basisBits n y) = y := (basisBitsEquiv n).symm_apply_apply y
  rw [ket_eq_single_symm_assoc, hy, Matrix.mulVec_single_one]
  rfl
open Classical in
theorem ket_apply_eq_ite_assoc {n : ℕ} (β : BitAssignment n) (x : Fin (2 ^ n)) :
    ket β x = if x = (basisBitsEquiv n).symm β then 1 else 0 := by
  rw [ket_eq_single_symm_assoc]
  by_cases h : x = (basisBitsEquiv n).symm β
  · subst h; simp
  · rw [ite_eq_right h, Pi.single_eq_of_ne h]
open Classical in
theorem rZLoc_basisOutcomeProjector_zero_mulVec_basisKet {kAct kZ : ℕ}
    (β : BitAssignment (kAct + kZ)) : ((rZLoc kAct kZ).basisOutcomeProjector 0).mulVec
    (basisKet β) = if (rZLoc kAct kZ).extractIndex ((basisBitsEquiv (kAct + kZ)).symm β) = 0
    then basisKet β else 0 := by
  let y := (basisBitsEquiv (kAct + kZ)).symm β
  rw [QRegister.basisOutcomeProjector_eq_diagonal, basisKet_eq_single_symm_assoc β,
    Matrix.diagonal_mulVec_single]
  by_cases h0 : (rZLoc kAct kZ).extractIndex y = 0
  · rw [ite_eq_left h0, ite_eq_left h0, one_mul]
  · rw [ite_eq_right h0, ite_eq_right h0, zero_mul, Pi.single_zero]
open Classical in
theorem pSum42CoreZero_mulVec_basisKet (β : BitAssignment (fullSysCoreWires 80 + 42)) :
    pSum42CoreZero.mulVec (basisKet β) = if (rZLoc (fullSysCoreWires 80) 42).extractIndex
    ((basisBitsEquiv (fullSysCoreWires 80 + 42)).symm β) = 0 then basisKet β else 0 :=
    rZLoc_basisOutcomeProjector_zero_mulVec_basisKet β
open Classical in
theorem eStream42CoreOf_mulVec_basisKet
    (sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ)
    (β : BitAssignment (fullSysCoreWires 80 + 42)) :
    (eStream42CoreOf sumFn).mulVec (basisKet β) =
      let y := (basisBitsEquiv (fullSysCoreWires 80 + 42)).symm β
      let a := (rActLoc (fullSysCoreWires 80) 42).extractIndex y
      if (rZLoc (fullSysCoreWires 80) 42).extractIndex y = 0 then
        basisKet (basisBits (fullSysCoreWires 80 + 42)
          (joinAZ a (streamTarget42 (fun w ↦ sumFn w (basisBits (fullSysCoreWires 80) a)))))
      else 0 :=
  streamProjOpGen_mulVec_basisKet (rActLoc (fullSysCoreWires 80) 42) (rZLoc (fullSysCoreWires 80)
    42)
    joinAZ
    (fun {x₁ x₂} hA hS ↦ by rw [← joinAZ_extract_self x₁, ← joinAZ_extract_self x₂, hA, hS])
    extract_rActLoc_joinAZ extract_rZLoc_joinAZ _ β
open Classical in
theorem uStr3AxisOfSpec_mul_pSum42CoreZero_eq_eStream217Core
    (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) (hSlice : ∀ (w : Fin 3) {n : ℕ} (rCore :
    QRegister (fullSysCoreWires 80) n) (rSum14 : QRegister 14 n) (hCSum : rCore.DisjointWires
    rSum14) (β₀ : Fin n → ZMod 2), (∀ i : Fin 14, β₀ (rSum14 i) = 0) → ∃ β : Fin n → ZMod 2,
    (((rSpec217OfCore rCore).concat rSum14 (disj_rSpec217OfCore_left hCSum)).embedUnitary
    (uSpec w)).1.mulVec (basisKet β₀) = basisKet β ∧ (∀ g : Fin n, g ∉ rSum14.image → β g = β₀
    g) ∧ (∀ i : Fin 14, β (rSum14 i) = if (spectatorSum217 w (fun q ↦ β₀ (rCore q))).testBit
    i.val then 1 else 0)) : (uStr3AxisOfSpec uSpec).1 * pSum42CoreZero = eStream217Core := by
  let kC := fullSysCoreWires 80
  let rA := rActLoc kC 42
  let rZ := rZLoc kC 42
  have h1Ax : ∀ (w : Fin 3) (rSum14 : QRegister 14 (kC + 42))
      (hCSum : rA.DisjointWires rSum14) (β₀ : Fin (kC + 42) → ZMod 2),
      (∀ i : Fin 14, β₀ (rSum14 i) = 0) → ∃ β : Fin (kC + 42) → ZMod 2, ((rA.concat rSum14
      hCSum).embedUnitary ((selSpec217InCoreSum14 80).embedUnitary (uSpec w))).1.mulVec
      (basisKet β₀) = basisKet β ∧ (∀ g : Fin (kC + 42), g ∉ rSum14.image → β g = β₀ g) ∧ (∀ i
      : Fin 14, β (rSum14 i) = if (spectatorSum217 w (fun q ↦ β₀ (rA q))).testBit i.val then 1
      else 0) := by
    intro w rSum14 hCSum β₀ hz
    obtain ⟨β, hket, hout, hbits⟩ := hSlice w rA rSum14 hCSum β₀ hz
    rw [← QRegister.embedUnitary_compose, compose_selSpec217InCoreSum14]
    exact ⟨β, hket, hout, hbits⟩
  apply matrix_ext_ket; intro β
  rw [ket_eq_basisKet, ← Matrix.mulVec_mulVec, pSum42CoreZero_mulVec_basisKet,
      eStream217Core, eStream42CoreOf_mulVec_basisKet]
  let y := (basisBitsEquiv (kC + 42)).symm β
  by_cases h0 : rZ.extractIndex y = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    have hz42 : ∀ j : Fin 42, β (rZ j) = 0 := by
      have hx := ((QRegExt.extractIndex_eq_zero_iff rZ) y).mp h0
      intro j; simpa [y] using hx j
    obtain ⟨β₁, hk₁, hout₁, hbits₁⟩ :=
      uThreeAxis217_compute_ket_of_oneAxis rA rZ (rActLoc_disj_rZLoc kC 42)
        (fun w ↦ (selSpec217InCoreSum14 80).embedUnitary (uSpec w)) h1Ax β hz42
    rw [rActLoc_concat_rZLoc_eq_idReg kC 42, embedUnitary_idReg_eq] at hk₁
    change (uStr3AxisOfSpec uSpec).1.mulVec (basisKet β) = _
    unfold uStr3AxisOfSpec
    rw [hk₁]
    refine congrArg basisKet (funext fun g ↦ ?_)
    have haBits : basisBits kC (rA.extractIndex y) = fun q ↦ β (rA q) := by
      funext q; simp [-Nat.reducePow, y, QRegister.basisBits_extractIndex]
    by_cases hg : g.val < kC
    · have hnZ : g ∉ rZ.image := by
        intro hm; obtain ⟨j, rfl⟩ := (QRegister.mem_image rZ _).mp hm
        simp [rZ, rZLoc] at hg
      have hga : rA ⟨g.val, hg⟩ = g := Fin.ext (by simp [rA, rActLoc])
      rw [hout₁ g hnZ, joinAZ, rZ.basisBits_replaceIndex_of_not_mem _ _ g
        (fun ⟨j, hj⟩ ↦ hnZ ((QRegister.mem_image rZ _).mpr ⟨j, hj⟩)),
        ← hga, rA.basisBits_replaceIndex_apply, haBits]
    · let j42 : Fin 42 := ⟨g.val - kC, by have := g.isLt; omega⟩
      let w : Fin 3 := ⟨j42.val / 14, by have := j42.isLt; omega⟩
      let i14 : Fin 14 := ⟨j42.val % 14, by omega⟩
      have hgz : rZ j42 = g := Fin.ext (by have := g.isLt; simp [rZ, rZLoc, j42]; omega)
      have hjSlice : BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42 w i14 = j42 :=
        Fin.ext (by simp [BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42, w, i14]; omega)
      have hjIn42 : rSum14In42 w i14 = j42 :=
        Fin.ext (by simp [rSum14In42, w, i14]; omega)
      have hgComp : (rZ.compose (BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42 w)) i14 = g :=
        by
        rw [QRegister.compose_apply, hjSlice, hgz]
      rw [← hgComp, hbits₁ w i14, hgComp, ← hgz, joinAZ, rZ.basisBits_replaceIndex_apply,
        ← hjIn42, basisBits_streamTarget42, haBits]
      rfl
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core :
    (uStr3AxisOfSpec uStream217Spec131).1 * pSum42CoreZero = eStream217Core :=
  uStr3AxisOfSpec_mul_pSum42CoreZero_eq_eStream217Core uStream217Spec131
    (fun w {_} rCore rSum14 hCSum ↦ uStream217Spec131_slice_compute_ket w rCore rSum14 hCSum)
theorem inv_uStr3AxisOfSpec_mul_eStream217Core_eq_pSum42CoreZero
    (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14)))
    (hE : (uStr3AxisOfSpec uSpec).1 * pSum42CoreZero = eStream217Core) :
    ((uStr3AxisOfSpec uSpec)⁻¹).1 * eStream217Core = pSum42CoreZero := by
  calc ((uStr3AxisOfSpec uSpec)⁻¹).1 * eStream217Core
      = ((uStr3AxisOfSpec uSpec)⁻¹).1 * ((uStr3AxisOfSpec uSpec).1 * pSum42CoreZero) := by rw [← hE]
    _ = (((uStr3AxisOfSpec uSpec)⁻¹ * uStr3AxisOfSpec uSpec).1) * pSum42CoreZero := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = pSum42CoreZero := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
open Classical in
theorem streamProjOpGen_rActLoc_conjTranspose_mul_self {kAct kZ : ℕ}
    (T : Fin (2 ^ kAct) → Fin (2 ^ kZ)) :
    (streamProjOpGen (rActLoc kAct kZ) (rZLoc kAct kZ) T)ᴴ * streamProjOpGen (rActLoc kAct kZ)
    (rZLoc kAct kZ) T = (rZLoc kAct kZ).basisOutcomeProjector 0 := by
  ext x y
  rw [Matrix.mul_apply, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single
    (joinAZ ((rActLoc kAct kZ).extractIndex x) (T ((rActLoc kAct kZ).extractIndex x)))]
  · simp only [Matrix.conjTranspose_apply, streamProjOpGen, Matrix.of_apply,
      extract_rActLoc_joinAZ, extract_rZLoc_joinAZ]
    by_cases hxy : x = y
    · subst hxy
      by_cases hx0 : (rZLoc kAct kZ).extractIndex x = 0 <;> simp [hx0]
    · by_cases hx0 : (rZLoc kAct kZ).extractIndex x = 0
      · have hnR : ¬ ((rActLoc kAct kZ).extractIndex x = (rActLoc kAct kZ).extractIndex y ∧
            (rZLoc kAct kZ).extractIndex y = 0 ∧
            T ((rActLoc kAct kZ).extractIndex x) = T ((rActLoc kAct kZ).extractIndex y)) := by
          rintro ⟨hAy, hy0, _⟩
          exact hxy (by rw [← joinAZ_extract_self x, ← joinAZ_extract_self y, hAy, hx0, hy0])
        simp [hx0, hxy, hnR]
      · simp [hx0, hxy]
  · intro z _ hz
    simp only [Matrix.conjTranspose_apply, streamProjOpGen, Matrix.of_apply]
    have hnL : ¬ ((rActLoc kAct kZ).extractIndex z = (rActLoc kAct kZ).extractIndex x ∧
        (rZLoc kAct kZ).extractIndex x = 0 ∧
        (rZLoc kAct kZ).extractIndex z = T ((rActLoc kAct kZ).extractIndex x)) := by
      rintro ⟨h1, _, h3⟩
      exact hz (by rw [← joinAZ_extract_self z, h1, h3])
    rw [ite_eq_right hnL, star_zero, zero_mul]
  · intro h0; exact (h0 (Finset.mem_univ _)).elim
theorem eStream42CoreOf_conjTranspose_mul_self
    (sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ) : (eStream42CoreOf sumFn)ᴴ *
    eStream42CoreOf sumFn = pSum42CoreZero := streamProjOpGen_rActLoc_conjTranspose_mul_self _
theorem extract_rZLoc_eq_streamTarget42_iff (x : Fin (2 ^ (fullSysCoreWires 80 + 42)))
    (S : Fin 3 → ℕ) (hS : ∀ w : Fin 3, S w < 2 ^ 14) :
    (rZLoc (fullSysCoreWires 80) 42).extractIndex x = streamTarget42 S ↔ ∀ w : Fin 3, regVal
    (rSum14InCoreSum42 80 w) (basisBits (fullSysCoreWires 80 + 42) x) = S w := by
  let kC := fullSysCoreWires 80
  let rZ := rZLoc kC 42
  let ξ := basisBits (kC + 42) x
  have hReg (w : Fin 3) : regVal (rSum14InCoreSum42 80 w) ξ =
      bitsVal (fun i : Fin 14 ↦ basisBits 42 (rZ.extractIndex x) (rSum14In42 w i)) := by
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only
    rw [rZ.basisBits_extractIndex]
    have hw : rZ (rSum14In42 w i) = rSum14InCoreSum42 80 w i :=
      Fin.ext (by simp [rZ, rZLoc, rSum14In42, rSum14InCoreSum42]; omega)
    rw [hw]
  have hTgt (w : Fin 3) :
      bitsVal (fun i : Fin 14 ↦ basisBits 42 (streamTarget42 S) (rSum14In42 w i)) = S w :=
    StepBBlock0.bitsVal_eq_of_testBit _ (S w) (hS w)
      (fun i ↦ basisBits_streamTarget42 S w i)
  constructor
  · intro hEq w
    rw [hReg w, hEq, hTgt w]
  · intro hAll
    apply (basisBitsEquiv 42).injective; funext j42
    let w : Fin 3 := ⟨j42.val / 14, by have := j42.isLt; omega⟩
    let i14 : Fin 14 := ⟨j42.val % 14, by omega⟩
    have hj : rSum14In42 w i14 = j42 := Fin.ext (by simp [rSum14In42, w, i14]; omega)
    have hFun : (fun i : Fin 14 ↦ basisBits 42 (rZ.extractIndex x) (rSum14In42 w i)) =
        fun i : Fin 14 ↦ basisBits 42 (streamTarget42 S) (rSum14In42 w i) :=
      bitsVal_inj (by rw [← hReg w, hAll w, ← hTgt w])
    change basisBits 42 (rZ.extractIndex x) j42 = basisBits 42 (streamTarget42 S) j42
    simpa only [hj] using congrFun hFun i14
open Classical in
theorem streamProjOpGen_rActLoc_mul_conjTranspose {kAct kZ : ℕ}
    (T : Fin (2 ^ kAct) → Fin (2 ^ kZ)) : streamProjOpGen (rActLoc kAct kZ) (rZLoc kAct kZ) T
    * (streamProjOpGen (rActLoc kAct kZ) (rZLoc kAct kZ) T)ᴴ = Matrix.diagonal (fun x ↦ if
    (rZLoc kAct kZ).extractIndex x = T ((rActLoc kAct kZ).extractIndex x) then 1 else 0) := by
  ext x y
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (joinAZ ((rActLoc kAct kZ).extractIndex x) 0)]
  · simp only [Matrix.conjTranspose_apply, streamProjOpGen, Matrix.of_apply,
      extract_rActLoc_joinAZ, extract_rZLoc_joinAZ]
    by_cases hxy : x = y
    · subst hxy
      by_cases hTx : (rZLoc kAct kZ).extractIndex x = T ((rActLoc kAct kZ).extractIndex x) <;>
        simp [hTx]
    · by_cases hTx : (rZLoc kAct kZ).extractIndex x = T ((rActLoc kAct kZ).extractIndex x)
      · have hnR : ¬ ((rActLoc kAct kZ).extractIndex y = (rActLoc kAct kZ).extractIndex x ∧
            (0 : Fin (2 ^ kZ)) = 0 ∧
            (rZLoc kAct kZ).extractIndex y = T ((rActLoc kAct kZ).extractIndex x)) := by
          rintro ⟨hAy, _, hTy⟩
          exact hxy (by rw [← joinAZ_extract_self x, ← joinAZ_extract_self y, hAy, hTx, hTy])
        have hnR' : ¬ ((rActLoc kAct kZ).extractIndex y = (rActLoc kAct kZ).extractIndex x ∧
            (rZLoc kAct kZ).extractIndex y = T ((rActLoc kAct kZ).extractIndex x)) :=
          fun ⟨h1, h2⟩ ↦ hnR ⟨h1, rfl, h2⟩
        simp [hTx, hxy, hnR']
      · simp [hTx, hxy]
  · intro b _ hb
    simp only [Matrix.conjTranspose_apply, streamProjOpGen, Matrix.of_apply]
    have hnL : ¬ ((rActLoc kAct kZ).extractIndex x = (rActLoc kAct kZ).extractIndex b ∧
        (rZLoc kAct kZ).extractIndex b = 0 ∧
        (rZLoc kAct kZ).extractIndex x = T ((rActLoc kAct kZ).extractIndex b)) := by
      rintro ⟨hAb, hb0, _⟩
      exact hb (by rw [← joinAZ_extract_self b, ← hAb, hb0])
    rw [ite_eq_right hnL, zero_mul]
  · intro h0; exact (h0 (Finset.mem_univ _)).elim
theorem eStream42CoreOf_mul_conjTranspose_eq_pStream42Of
    (sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ)
    (hBound : ∀ w γ, sumFn w γ < 2 ^ 14) :
    eStream42CoreOf sumFn * (eStream42CoreOf sumFn)ᴴ = pStream42Of sumFn := by
  rw [eStream42CoreOf, streamProjOpGen_rActLoc_mul_conjTranspose, pStream42Of]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  have hCoreBits : basisBits (fullSysCoreWires 80) ((rActLoc (fullSysCoreWires 80) 42).extractIndex
    x) =
      fun q ↦ basisBits (fullSysCoreWires 80 + 42) x (rCoreInCoreSum42 80 q) := by
    funext q; rw [(rActLoc (fullSysCoreWires 80) 42).basisBits_extractIndex]; rfl
  have hiff := extract_rZLoc_eq_streamTarget42_iff x
    (fun w ↦
      sumFn w (basisBits (fullSysCoreWires 80) ((rActLoc (fullSysCoreWires 80) 42).extractIndex x)))
    (fun w ↦ hBound w _)
  dsimp only
  simp only [hiff]
  simp only [hCoreBits]
theorem eStream217Core_mul_conjTranspose :
    eStream217Core * (eStream217Core)ᴴ = pStream217Core 80 :=
  eStream42CoreOf_mul_conjTranspose_eq_pStream42Of spectatorSum217 (fun w γ ↦ by
    have := (spectatorSum217_le_13671 w γ).1; have := (spectatorSum217_le_13671 w γ).2; omega)
theorem eStream218Core_mul_conjTranspose : eStream218Core * (eStream218Core)ᴴ = pStream218Core
    80 := eStream42CoreOf_mul_conjTranspose_eq_pStream42Of slot2AxisSum
    NuclearTwistRealizes.slot2AxisSum_lt
open Classical in
theorem pStream217Core_mul_eStream217Core :
    pStream217Core 80 * eStream217Core = eStream217Core := by
  rw [← eStream217Core_mul_conjTranspose, Matrix.mul_assoc,
    show (eStream217Core)ᴴ * eStream217Core = pSum42CoreZero from
      eStream42CoreOf_conjTranspose_mul_self spectatorSum217]
  apply matrix_ext_ket; intro β
  rw [ket_eq_basisKet, ← Matrix.mulVec_mulVec, pSum42CoreZero_mulVec_basisKet]
  by_cases h0 : (rZLoc (fullSysCoreWires 80) 42).extractIndex
      ((basisBitsEquiv (fullSysCoreWires 80 + 42)).symm β) = 0
  · rw [ite_eq_left h0]
  · rw [ite_eq_right h0, Matrix.mulVec_zero, eStream217Core, eStream42CoreOf_mulVec_basisKet]
    dsimp only; rw [ite_eq_right h0]
open Classical in
theorem pStream218Core_mul_eStream218Core :
    pStream218Core 80 * eStream218Core = eStream218Core := by
  rw [← eStream218Core_mul_conjTranspose, Matrix.mul_assoc,
    show (eStream218Core)ᴴ * eStream218Core = pSum42CoreZero from
      eStream42CoreOf_conjTranspose_mul_self slot2AxisSum]
  apply matrix_ext_ket; intro β
  rw [ket_eq_basisKet, ← Matrix.mulVec_mulVec, pSum42CoreZero_mulVec_basisKet]
  by_cases h0 : (rZLoc (fullSysCoreWires 80) 42).extractIndex
      ((basisBitsEquiv (fullSysCoreWires 80 + 42)).symm β) = 0
  · rw [ite_eq_left h0]
  · rw [ite_eq_right h0, Matrix.mulVec_zero, eStream218Core, eStream42CoreOf_mulVec_basisKet]
    dsimp only; rw [ite_eq_right h0]
open Classical in
theorem uSlot0Sum42Add_mul_eStream217Core :
    (uSlot0Sum42Add 80).1 * eStream217Core = eStream218Core := by
  let kC := fullSysCoreWires 80
  let rA := rActLoc kC 42
  let rZ := rZLoc kC 42
  have hStep : ∀ (w : Fin 3) (a : Fin (2 ^ kC)) (S : Fin 3 → ℕ)
      (hS : ∀ u : Fin 3, S u < 2 ^ 14),
      ((Slot0SubAdd14And217Stream.selCoreSum14In42 80 w).embedUnitary (uSlot0AxisAdd14 w)).1.mulVec
        (basisKet (basisBits (kC + 42) (joinAZ a (streamTarget42 S)))) =
      basisKet (basisBits (kC + 42) (joinAZ a (streamTarget42
        (Function.update S w ((S w + slot0AxisVal w (basisBits kC a)) % 2 ^ 14))))) := by
    intro w a S hS
    let S' := Function.update S w ((S w + slot0AxisVal w (basisBits kC a)) % 2 ^ 14)
    let rS14 := rZ.compose (rSum14Slice42 w)
    have hSel : Slot0SubAdd14And217Stream.selCoreSum14In42 80 w =
        rA.concat rS14 ((rActLoc_disj_rZLoc kC 42).compose_right (rSum14Slice42 w)) := by
      apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · rw [QRegister.concat_apply_left, Slot0SubAdd14And217Stream.selCoreSum14In42,
          QRegister.concat_apply_left]; exact Fin.ext (by simp [rA, rActLoc])
      · rw [QRegister.concat_apply_right, Slot0SubAdd14And217Stream.selCoreSum14In42,
          QRegister.concat_apply_right]; exact Fin.ext (by
            simp [kC, rS14, rZ, rZLoc, rSum14Slice42])
    let β₀ := basisBits (kC + 42) (joinAZ a (streamTarget42 S))
    let β₁ := basisBits (kC + 42) (joinAZ a (streamTarget42 S'))
    have hRegVal : ∀ (T_fn : Fin 3 → ℕ) (hT : ∀ u, T_fn u < 2 ^ 14),
        regVal rS14 (basisBits (kC + 42) (joinAZ a (streamTarget42 T_fn))) = T_fn w := by
      intro T_fn hT
      have hEq : (fun i : Fin 14 ↦ basisBits (kC + 42) (joinAZ a (streamTarget42 T_fn)) (rS14 i)) =
          fun i : Fin 14 ↦ if (T_fn w).testBit i.val then 1 else 0 := by
        funext i
        have hi : rS14 i = rZ (rSum14In42 w i) :=
          Fin.ext (by simp [rS14, rZ, rZLoc, rSum14Slice42, rSum14In42])
        rw [hi, joinAZ, rZ.basisBits_replaceIndex_apply, basisBits_streamTarget42]
      unfold regVal
      change bitsVal (fun i : Fin 14 ↦
        basisBits (kC + 42) (joinAZ a (streamTarget42 T_fn)) (rS14 i)) = T_fn w
      rw [hEq]
      exact StepBBlock0.bitsVal_eq_of_testBit _ (T_fn w) (hT w) (fun _ ↦ rfl)
    have hS' : ∀ u : Fin 3, S' u < 2 ^ 14 := fun u ↦ by
      dsimp only [S']
      by_cases hu : u = w
      · subst hu; rw [Function.update_self]; exact Nat.mod_lt _ (by decide)
      · rw [Function.update_of_ne hu]; exact hS u
    have hCoreEq : (fun q : Fin kC ↦ β₀ (rA q)) = basisBits kC a := by
      funext q
      have hnZ : rA q ∉ Set.range rZ.wires := by
        rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; simp [rA, rActLoc, rZ, rZLoc] at hv; omega
      dsimp only [β₀]
      rw [joinAZ, rZ.basisBits_replaceIndex_of_not_mem _ _ _ hnZ, rA.basisBits_replaceIndex_apply]
    rw [hSel, uSlot0AxisAdd14]
    exact (DyadicQft64.catModAddUnitary_mulVec_basisKet rA rS14 _ (slot0AxisVal w)
      (fun _ ↦ β₁) β₀
      (fun g hg ↦ by
        dsimp only [β₀, β₁]
        by_cases hgC : g.val < kC
        · have hnZ : g ∉ Set.range rZ.wires := by
            rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; simp [rZ, rZLoc] at hv; omega
          rw [joinAZ, joinAZ, rZ.basisBits_replaceIndex_of_not_mem _ _ _ hnZ,
            rZ.basisBits_replaceIndex_of_not_mem _ _ _ hnZ]
        · let j42 : Fin 42 := ⟨g.val - kC, by have := g.isLt; omega⟩
          let u : Fin 3 := ⟨j42.val / 14, by have := j42.isLt; omega⟩
          let i14 : Fin 14 := ⟨j42.val % 14, by omega⟩
          have hgz : rZ j42 = g := Fin.ext (by have := g.isLt; simp [rZ, rZLoc, j42]; omega)
          have hjIn42 : rSum14In42 u i14 = j42 := Fin.ext (by simp [rSum14In42, u, i14]; omega)
          have huw : u ≠ w := fun huw ↦ hg (by
            subst huw
            refine (QRegister.mem_image rS14 g).mpr ⟨i14, ?_⟩
            rw [← hgz]; exact Fin.ext (by simp [rS14, rZ, rZLoc, rSum14Slice42, u, i14]; omega))
          dsimp only [S']
          rw [← hgz, joinAZ, joinAZ, rZ.basisBits_replaceIndex_apply,
            rZ.basisBits_replaceIndex_apply,
            ← hjIn42, basisBits_streamTarget42, basisBits_streamTarget42,
              Function.update_of_ne huw])
      (by
        dsimp only [β₀, β₁]
        rw [hRegVal S' hS', hRegVal S hS, hCoreEq]
        simp [S'])).symm
  apply matrix_ext_ket; intro β
  rw [ket_eq_basisKet, ← Matrix.mulVec_mulVec, eStream217Core, eStream218Core,
    eStream42CoreOf_mulVec_basisKet, eStream42CoreOf_mulVec_basisKet]
  let y := (basisBitsEquiv (kC + 42)).symm β
  by_cases h0 : rZ.extractIndex y = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    let a := rA.extractIndex y
    let S0 : Fin 3 → ℕ := fun w ↦ spectatorSum217 w (basisBits kC a)
    have hS0 : ∀ u : Fin 3, S0 u < 2 ^ 14 := fun u ↦ by
      have := (spectatorSum217_le_13671 u (basisBits kC a)).1
      have := (spectatorSum217_le_13671 u (basisBits kC a)).2; omega
    have hMod : ∀ w : Fin 3, (S0 w + slot0AxisVal w (basisBits kC a)) % 2 ^ 14 =
        slot2AxisSum w (basisBits kC a) :=
      fun w ↦ (slot0AxisAddSub14_mod_eq_iff w (basisBits kC a) (S0 w) (hS0 w)).1.mp rfl
    dsimp only [uSlot0Sum42Add]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [hStep 0 a S0 hS0]
    let S1 := Function.update S0 0 ((S0 0 + slot0AxisVal 0 (basisBits kC a)) % 2 ^ 14)
    have hS1 : ∀ u : Fin 3, S1 u < 2 ^ 14 := fun u ↦ by
      dsimp only [S1]
      by_cases hu : u = 0
      · subst hu; rw [Function.update_self]; exact Nat.mod_lt _ (by decide)
      · rw [Function.update_of_ne hu]; exact hS0 u
    rw [hStep 1 a S1 hS1]
    let S2 := Function.update S1 1 ((S1 1 + slot0AxisVal 1 (basisBits kC a)) % 2 ^ 14)
    have hS2 : ∀ u : Fin 3, S2 u < 2 ^ 14 := fun u ↦ by
      dsimp only [S2]
      by_cases hu : u = 1
      · subst hu; rw [Function.update_self]; exact Nat.mod_lt _ (by decide)
      · rw [Function.update_of_ne hu]; exact hS1 u
    rw [hStep 2 a S2 hS2]
    refine congrArg (fun F ↦
      basisKet (basisBits (kC + 42) (joinAZ a (streamTarget42 F)))) (funext fun w ↦ ?_)
    have hw3 : w = 0 ∨ w = 1 ∨ w = 2 := by fin_cases w <;> decide
    rcases hw3 with rfl | rfl | rfl
    · dsimp only [S2, S1]
      rw [Function.update_of_ne (by
        decide), Function.update_of_ne (by decide), Function.update_self]
      exact hMod 0
    · dsimp only [S2, S1]
      rw [Function.update_of_ne (by decide), Function.update_self]
      exact hMod 1
    · rw [Function.update_self]
      exact hMod 2
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem uSlot0Sum42Sub_mul_eStream218Core :
    ((uSlot0Sum42Add 80)⁻¹).1 * eStream218Core = eStream217Core := by
  calc ((uSlot0Sum42Add 80)⁻¹).1 * eStream218Core
      = ((uSlot0Sum42Add 80)⁻¹).1 * ((uSlot0Sum42Add 80).1 * eStream217Core) := by
          rw [← uSlot0Sum42Add_mul_eStream217Core]
    _ = (((uSlot0Sum42Add 80)⁻¹ * uSlot0Sum42Add 80).1) * eStream217Core := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = eStream217Core := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
open Classical in
theorem streamProjOpGen_apply_assoc {kAct kZ n : ℕ} (rAct : QRegister kAct n)
    (rZ : QRegister kZ n) (T : Fin (2 ^ kAct) → Fin (2 ^ kZ)) (x y : Fin (2 ^ n)) :
    streamProjOpGen rAct rZ T x y = if rAct.extractIndex x = rAct.extractIndex y ∧
    rZ.extractIndex y = 0 ∧ rZ.extractIndex x = T (rAct.extractIndex y) then 1 else 0 := rfl
open Classical in
theorem ite_pos_assoc {α : Sort*} {c : Prop} {inst : Decidable c} (hc : c) (a b : α) :
    @ite α c inst a b = a := @ite_eq_left c inst hc α a b
open Classical in
theorem ite_neg_assoc {α : Sort*} {c : Prop} {inst : Decidable c} (hnc : ¬ c) (a b : α) :
    @ite α c inst a b = b := @ite_eq_right c inst hnc α a b
open Classical in
theorem rCSFull_embedMatrix_eStream218Core_eq_E_rawStream42 : (rCoreFull.concat rSum0
    (hAct0_disj_Sum0.compose_left rCoreOrig)).embedMatrix eStream218Core = E_rawStream42 := by
  let kC := fullSysCoreWires 80
  let rCS := rCoreFull.concat rSum0 (hAct0_disj_Sum0.compose_left rCoreOrig)
  have hkFull : kFull80 = kActOrig + 42 := by decide
  have hExtCore : ∀ z : Fin (2 ^ kFull80),
      (rActLoc kC 42).extractIndex (rCS.extractIndex z) = rCoreFull.extractIndex z := fun z ↦
    (basisBitsEquiv kC).injective (funext fun i ↦ by
      change basisBits kC _ i = basisBits kC _ i
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        QRegister.basisBits_extractIndex]
      have hi : rActLoc kC 42 i = Fin.castAdd 42 i := Fin.ext (by simp [rActLoc])
      rw [hi, QRegister.concat_apply_left])
  have hExtSum : ∀ z : Fin (2 ^ kFull80),
      (rZLoc kC 42).extractIndex (rCS.extractIndex z) = rSum0.extractIndex z := fun z ↦
    (basisBitsEquiv 42).injective (funext fun j ↦ by
      change basisBits 42 _ j = basisBits 42 _ j
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        QRegister.basisBits_extractIndex]
      have hj : rZLoc kC 42 j = Fin.natAdd kC j := Fin.ext (by simp [rZLoc])
      rw [hj, QRegister.concat_apply_right])
  have hActEq : ∀ x y : Fin (2 ^ kFull80),
      ((rCS.basisSplitEquiv x).2 = (rCS.basisSplitEquiv y).2 ∧
        rCoreFull.extractIndex x = rCoreFull.extractIndex y) ↔
      rAct0.extractIndex x = rAct0.extractIndex y := fun x y ↦ by
    rw [rCS.basisSplit_environment_eq_iff]
    constructor
    · rintro ⟨hOut, hCore⟩
      apply (basisBitsEquiv kActOrig).injective; funext q
      change basisBits kActOrig _ q = basisBits kActOrig _ q
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      by_cases hw : rAct0 q ∈ Set.range rCS.wires
      · rcases hw with ⟨idx, hidx⟩
        revert hidx
        refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
        · intro hi; rw [QRegister.concat_apply_left] at hi
          have hx := QRegister.basisBits_extractIndex rCoreFull x i
          have hy := QRegister.basisBits_extractIndex rCoreFull y i
          rw [hi] at hx hy; rw [← hx, ← hy, hCore]
        · intro hj; rw [QRegister.concat_apply_right] at hj
          exact False.elim (hAct0_disj_Sum0.ne q j hj.symm)
      · exact hOut (rAct0 q) hw
    · intro hAct
      refine ⟨fun w hw ↦ ?_, (basisBitsEquiv kC).injective (funext fun i ↦ ?_)⟩
      · have hlt : w.val < kActOrig := by
          by_contra hge
          have hlt42 : w.val - kActOrig < 42 := by have := w.isLt; omega
          refine hw ⟨Fin.natAdd kC ⟨w.val - kActOrig, hlt42⟩, ?_⟩
          rw [QRegister.concat_apply_right]
          ext; simp [rSum0]; omega
        have hwEq : rAct0 ⟨w.val, hlt⟩ = w := by ext; simp [rAct0]
        have hx := QRegister.basisBits_extractIndex rAct0 x ⟨w.val, hlt⟩
        have hy := QRegister.basisBits_extractIndex rAct0 y ⟨w.val, hlt⟩
        rw [hwEq] at hx hy; rw [← hx, ← hy, hAct]
      · change basisBits kC _ i = basisBits kC _ i
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        have hx := QRegister.basisBits_extractIndex rAct0 x (rCoreOrig i)
        have hy := QRegister.basisBits_extractIndex rAct0 y (rCoreOrig i)
        exact hx.symm.trans ((congrArg (fun z ↦ basisBits kActOrig z (rCoreOrig i)) hAct).trans hy)
  have hStreamEq : ∀ y : Fin (2 ^ kFull80),
      streamTarget42 (fun w ↦ slot2AxisSum w (basisBits kC (rCoreFull.extractIndex y))) =
      streamTarget42 (rawStreamVec h3924_actOrig (rAct0.extractIndex y)) := fun y ↦
    congrArg streamTarget42 (funext fun w ↦ by
      rw [← rawStreamOfLow_eq_slot2AxisSum _ w]
      dsimp only [rawStreamVec]
      refine congrFun (congrArg rawStreamOfLow (funext fun q ↦ ?_)) w
      dsimp only [low3924Bits]
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      exact congrArg (basisBits kFull80 y) (congrArg rAct0 (isLow3924Prefix_rCoreOrig q)))
  refine Matrix.ext fun x y ↦ ?_
  rw [E_rawStream42_eq_streamProjOp, QRegister.embedMatrix_apply, eStream218Core, eStream42CoreOf,
    streamProjOp, streamProjOpGen_apply_assoc, streamProjOpGen_apply_assoc]
  rw [hExtCore x, hExtCore y, hExtSum x, hExtSum y, hStreamEq y]
  by_cases hEnv : (rCS.basisSplitEquiv x).2 = (rCS.basisSplitEquiv y).2
  · rw [ite_pos_assoc hEnv, mul_one]
    have hiff : rCoreFull.extractIndex x = rCoreFull.extractIndex y ↔
        rAct0.extractIndex x = rAct0.extractIndex y :=
      ⟨fun hc ↦ (hActEq x y).mp ⟨hEnv, hc⟩, fun ha ↦ ((hActEq x y).mpr ha).2⟩
    by_cases hRest : rSum0.extractIndex y = 0 ∧
        rSum0.extractIndex x = streamTarget42 (rawStreamVec h3924_actOrig (rAct0.extractIndex y))
    · by_cases hc : rCoreFull.extractIndex x = rCoreFull.extractIndex y
      · rw [ite_pos_assoc ⟨hc, hRest⟩, ite_pos_assoc ⟨hiff.mp hc, hRest⟩]
      · rw [ite_neg_assoc (fun h ↦ hc h.1), ite_neg_assoc (fun h ↦ hc (hiff.mpr h.1))]
    · rw [ite_neg_assoc (fun h ↦ hRest h.2), ite_neg_assoc (fun h ↦ hRest h.2)]
  · rw [ite_neg_assoc hEnv, mul_zero]
    have hna : rAct0.extractIndex x ≠ rAct0.extractIndex y :=
      fun ha ↦ hEnv ((hActEq x y).mpr ha).1
    rw [ite_neg_assoc (fun h ↦ hna h.1)]
end Spec217Stream3Axis
end Part3_StageAConcreteCircuitsAndStreamBridge
end ImplAlt
end StageAConjHAndStreamBridge
end SharedScope
end
end SlimFermApproxSec2BAnd3A

noncomputable section SlimStageBOuterDepsB
set_option maxRecDepth 131072

set_option backward.isDefEq.respectTransparency false
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroK11 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open _root_.DynamicCircuit DynCircuitExt
open Circuit hiding TOFF
open Operator QProg Matrix Real HermitianMat SpecsAux
open SpecsAux.SpecMirror
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open scoped Circuit.Notation
namespace StageAPointPhase128OnStep
open DyadicQft64 DyadicQft64WalkCircuit DyadicQft64WalkCircuit288
open CoreQftHadamard140And160 (CanonStageSpec128)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6)
open HeldRSum42TwistQftPass2Stitch (axisProdPrefix stageHPrefixCanonStage128)
/-- 2-electron (`L = 6` axes) Slot-3 Hadamard-Forest stage on `CanonStageSpec128` (`15 T`, `TOFF
  = 0`). -/
noncomputable def activeTwoElecSlot3Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 3 0 6 15 forestCfg3 forestExp3 forestCfg3_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
/-- 2-electron (`L = 6` axes) Slot-2 Hadamard-Forest stage on `CanonStageSpec128` (`54 T`, `TOFF
  = 0`). -/
noncomputable def activeTwoElecSlot2Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 2 0 6 54 forestCfg2 forestExp2 forestCfg2_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
/-- 2-electron (`L = 6` axes) Slot-1 Hadamard-Forest stage on `CanonStageSpec128` (`78 T`, `TOFF
  = 0`). -/
noncomputable def activeTwoElecSlot1Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 1 0 6 78 forestCfg1 forestExp1 forestCfg1_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
/-- 2-electron (`L = 6` axes) Slot-0 Hadamard-Forest stage on `CanonStageSpec128` (`44 T`, `TOFF
  = 0`). -/
noncomputable def activeTwoElecSlot0Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 0 0 6 44 forestCfg0 forestExp0 forestCfg0_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hL6_le_654 : 6 ≤ 654 := by decide
/-- Complete 6-stage Hadamard-Forest `QFT_64` `CanonStageSpec128` on the 2 active electrons (`L = 6`
  axes,
**`221 T` one-way = `442 T/step`**, `TOFF = 0`, saving **`-18 T/step`** below
`activeTwoElecFullQftStage128`'s `230 T`). -/
noncomputable def rawActiveTwoElecForestQftStage128 : CanonStageSpec128 :=
    (((stageHPrefixCanonStage128 6 hL6_le_654 5).seq (stageW16PrefixCanonStage128 6 hL6_le_654
    4)).seq (((stageHPrefixCanonStage128 6 hL6_le_654 4).seq ((stageW16PrefixCanonStage128 6
    hL6_le_654 3).seq activeTwoElecSlot3Stage128)).seq (((stageHPrefixCanonStage128 6
    hL6_le_654 3).seq ((stageW16PrefixCanonStage128 6 hL6_le_654 2).seq
    activeTwoElecSlot2Stage128)).seq (((stageHPrefixCanonStage128 6 hL6_le_654 2).seq
    ((stageW16PrefixCanonStage128 6 hL6_le_654 1).seq activeTwoElecSlot1Stage128)).seq
    (((stageHPrefixCanonStage128 6 hL6_le_654 1).seq ((stageW16PrefixCanonStage128 6
    hL6_le_654 0).seq activeTwoElecSlot0Stage128)).seq (stageHPrefixCanonStage128 6 hL6_le_654
    0))))))
theorem activeTwoElecSlot3_128_uEff :
    activeTwoElecSlot3Stage128.uEff = axisProdPrefix 6 hL6_le_654 (fun _ ↦
      diag6Unitary forestExp3) :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 6 hL6_le_654 forestExp3).symm
theorem activeTwoElecSlot2_128_uEff :
    activeTwoElecSlot2Stage128.uEff = axisProdPrefix 6 hL6_le_654 (fun _ ↦
      diag6Unitary forestExp2) :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 6 hL6_le_654 forestExp2).symm
theorem activeTwoElecSlot1_128_uEff :
    activeTwoElecSlot1Stage128.uEff = axisProdPrefix 6 hL6_le_654 (fun _ ↦
      diag6Unitary forestExp1) :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 6 hL6_le_654 forestExp1).symm
theorem activeTwoElecSlot0_128_uEff :
    activeTwoElecSlot0Stage128.uEff = axisProdPrefix 6 hL6_le_654 (fun _ ↦
      diag6Unitary forestExp0) :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 6 hL6_le_654 forestExp0).symm
theorem rawActiveTwoElecForestQftStage128_uEff_eq :
    rawActiveTwoElecForestQftStage128.uEff = axisProdPrefix 6 hL6_le_654 (fun _ ↦ uCoreHadamard6) :=
      by
  unfold rawActiveTwoElecForestQftStage128
  simp only [stage128_seq_uEff, stageHPrefix128_uEff, stageW16Prefix128_uEff,
    activeTwoElecSlot3_128_uEff, activeTwoElecSlot2_128_uEff,
    activeTwoElecSlot1_128_uEff, activeTwoElecSlot0_128_uEff, axisProdPrefix_mul]
  exact congrArg (fun u6 ↦ axisProdPrefix 6 hL6_le_654 (fun _ ↦ u6)) forest6_eq_orig6
/-- Complete 6-stage `221-T` 2-electron Hadamard-Forest `QFT_64` `CanonStageSpec128` (`221 T`
  one-way = `442 T/step`, `TOFF = 0`). -/
noncomputable def activeTwoElecForestFullQftStage128 : CanonStageSpec128 :=
  rawActiveTwoElecForestQftStage128.congr
    (uEff' := axisProdPrefix 6 hL6_le_654 (fun _ ↦ uCoreHadamard6))
    (tCost' := 221)
    rawActiveTwoElecForestQftStage128_uEff_eq
    rfl
end StageAPointPhase128OnStep
namespace ElecHadConjLoadAndTrueSwapComp
theorem sqrtHalf_sq_mul_two : (MeasureBranchHadamardSem.sqrtHalf *
    MeasureBranchHadamardSem.sqrtHalf : ℂ) * 2 = 1 := by
  rw [MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf]
  ring
/-- Bitwise XOR on `Fin (2 ^ 18)` via `basisBitsEquiv 18`. -/
noncomputable def xor18 (x y : Fin (2 ^ 18)) : Fin (2 ^ 18) :=
  (basisBitsEquiv 18).symm fun j ↦ basisBits 18 x j + basisBits 18 y j
@[simp] theorem basisBits_xor18 (x y : Fin (2 ^ 18)) (j : Fin 18) :
    basisBits 18 (xor18 x y) j = basisBits 18 x j + basisBits 18 y j :=
  congrFun ((basisBitsEquiv 18).apply_symm_apply _) j
theorem basisBits18_zero (j : Fin 18) : basisBits 18 (0 : Fin (2 ^ 18)) j = 0 := by
  simp [-Nat.reducePow, basisBits_eq_div_mod]
@[simp] theorem xor18_zero_left (y : Fin (2 ^ 18)) : xor18 0 y = y := by
  apply (basisBitsEquiv 18).injective; funext j
  change basisBits 18 (xor18 0 y) j = basisBits 18 y j
  rw [basisBits_xor18, basisBits18_zero, zero_add]
@[simp] theorem xor18_self (x : Fin (2 ^ 18)) : xor18 x x = 0 := by
  apply (basisBitsEquiv 18).injective; funext j
  change basisBits 18 (xor18 x x) j = basisBits 18 0 j
  rw [basisBits_xor18, basisBits18_zero, CharTwo.add_self_eq_zero]
@[simp] theorem xor18_cancel_right (x y : Fin (2 ^ 18)) : xor18 (xor18 x y) y = x := by
  apply (basisBitsEquiv 18).injective; funext j
  change basisBits 18 (xor18 (xor18 x y) y) j = basisBits 18 x j
  rw [basisBits_xor18, basisBits_xor18, CharTwo.add_cancel_right]
/-- Forward load map `(d, y) ↦ (d, y ⊕ tbl d)` on `Fin (2 ^ kData) × Fin (2 ^ 18)`. -/
noncomputable def lensLoadPerm {kData : ℕ} (L : Slot18Lens kData)
    (p : Fin (2 ^ kData) × Fin (2 ^ 18)) : Fin (2 ^ kData) × Fin (2 ^ 18) :=
  (p.1, xor18 p.2 (L.tbl p.1))
/-- Reverse write map `(d, y) ↦ (updSlot d (tbl d ⊕ y), y)` (`(I_idx ⊗ H_elec ⊗ H_anc) · Load ·
  (I_idx ⊗ H_elec ⊗ H_anc)`). -/
noncomputable def lensWritePerm {kData : ℕ} (L : Slot18Lens kData)
    (p : Fin (2 ^ kData) × Fin (2 ^ 18)) : Fin (2 ^ kData) × Fin (2 ^ 18) :=
  (L.updSlot p.1 (xor18 (L.tbl p.1) p.2), p.2)
theorem lensLoadPerm_involutive {kData : ℕ} (L : Slot18Lens kData) :
    Function.Involutive (lensLoadPerm L) := by
  rintro ⟨d, y⟩
  dsimp only [lensLoadPerm]
  rw [xor18_cancel_right]
theorem lensWritePerm_involutive {kData : ℕ} (L : Slot18Lens kData) :
    Function.Involutive (lensWritePerm L) := by
  rintro ⟨d, y⟩
  dsimp only [lensWritePerm]
  rw [L.get_put, L.put_put, xor18_cancel_right, L.put_get]
/-- **Lens Erase-to-Zero Identity (`lensWrite_lensLoad_zero_eq_swap`, `0 sorry`)**:
On `y = 0`, `lensWritePerm L (lensLoadPerm L (d, 0)) = (L.updSlot d 0, L.tbl d) = lensSwapPerm L (d,
0)`. -/
@[simp] theorem lensWrite_lensLoad_zero_eq_swap {kData : ℕ} (L : Slot18Lens kData)
    (d : Fin (2 ^ kData)) :
    lensWritePerm L (lensLoadPerm L (d, 0)) = lensSwapPerm L (d, 0) := by
  dsimp only [lensLoadPerm, lensWritePerm, lensSwapPerm]
  rw [xor18_zero_left, xor18_self]
/-- **Lens Duplication Identity (`lensWrite_lensSwap_zero_eq_dup`, `0 sorry`)**:
On `y = 0`, `lensWritePerm L (lensSwapPerm L (d', 0)) = (d', L.tbl d')`. -/
@[simp] theorem lensWrite_lensSwap_zero_eq_dup {kData : ℕ} (L : Slot18Lens kData)
    (d' : Fin (2 ^ kData)) : lensWritePerm L (lensSwapPerm L (d', 0)) = (d', L.tbl d') := by
  dsimp only [lensSwapPerm, lensWritePerm]
  rw [L.get_put, xor18_zero_left, L.put_put, L.put_get]
end ElecHadConjLoadAndTrueSwapComp
namespace ElecHadTrueSwapHCompClosure
open FullConcrete7StepAndTrueSwapSelect (uHadamardAll cHadamardAll eval_cHadamardAll)
open StageADeconstrCore (selDataInAct selMeasInAct concat_compose_selDataInAct
  concat_compose_selMeasInAct)
/-- Unitary `uWriteSub selHad uLoad` conjugating `uLoad : Unitary (2 ^ kAct)` by Hadamards
ONLY on the subregister `selHad : QRegister kHad kAct` (`leaving all wires outside selHad
untouched!`). -/
noncomputable def uWriteSub {kHad kAct : ℕ}
    (selHad : QRegister kHad kAct) (uLoad : Unitary (2 ^ kAct)) : Unitary (2 ^ kAct) :=
  (selHad.embedUnitary (uHadamardAll kHad) * uLoad) * selHad.embedUnitary (uHadamardAll kHad)
open Classical in
theorem eval_cHadamardAll_compose {kHad kAct n : ℕ} (rAct : QRegister kAct n)
    (selHad : QRegister kHad kAct) : (cHadamardAll (rAct.compose selHad)).eval =
    rAct.embedUnitary (selHad.embedUnitary (uHadamardAll kHad)) := by
  rw [eval_cHadamardAll, QRegister.embedUnitary_compose]
theorem extractIndex_compose_eq {n k₁ k₂ : ℕ}
    (r : QRegister k₂ n) (sel : QRegister k₁ k₂) (g : Fin (2 ^ n)) :
    sel.extractIndex (r.extractIndex g) = (r.compose sel).extractIndex g := by
  apply (basisBitsEquiv k₁).injective
  funext i
  change basisBits k₁ (sel.extractIndex (r.extractIndex g)) i =
    basisBits k₁ ((r.compose sel).extractIndex g) i
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      QRegister.basisBits_extractIndex, QRegister.compose_apply]
theorem replaceIndex_compose_eq {n k₁ k₂ : ℕ} (r : QRegister k₂ n) (sel : QRegister k₁ k₂)
    (g : Fin (2 ^ n)) (v : Fin (2 ^ k₁)) : r.replaceIndex g
    (sel.replaceIndex (r.extractIndex g) v) = (r.compose sel).replaceIndex g v := by
  apply (basisBitsEquiv n).injective
  funext w
  change basisBits n (r.replaceIndex g (sel.replaceIndex (r.extractIndex g) v)) w =
    basisBits n ((r.compose sel).replaceIndex g v) w
  by_cases hw : w ∈ Set.range (r.compose sel).wires
  · obtain ⟨i, rfl⟩ := hw
    rw[QRegister.basisBits_replaceIndex_apply (r.compose sel) g v i, QRegister.compose_apply,
        QRegister.basisBits_replaceIndex_apply r g _ (sel i),
        QRegister.basisBits_replaceIndex_apply sel (r.extractIndex g) v i]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem (r.compose sel) g v w hw]
    by_cases hwr : w ∈ Set.range r.wires
    · obtain ⟨u, rfl⟩ := hwr
      have hu_not_sel : u ∉ Set.range sel.wires := by
        rintro ⟨i, rfl⟩
        exact hw ⟨i, rfl⟩
      rw [QRegister.basisBits_replaceIndex_apply r g _ u,
          QRegister.basisBits_replaceIndex_of_not_mem sel (r.extractIndex g) v u hu_not_sel,
          QRegister.basisBits_extractIndex]
    · exact QRegister.basisBits_replaceIndex_of_not_mem r g _ w hwr
end ElecHadTrueSwapHCompClosure
namespace ZeroHypElecHadHCompAndPass123Closure
open InterWalkRSum42Hoist (qreg_block_apply)
open StageADeconstrCore (selDataInAct selMeasInAct)
theorem joinDM_eq_replaceIndex_selMeasInAct {kData : ℕ} (z : Fin (2 ^ (kData + 18)))
    (v : Fin (2 ^ 18)) : joinDM ((selDataInAct kData).extractIndex z, v) =
    (selMeasInAct kData).replaceIndex z v := by
  have hSymm : ∀ idx : Fin (kData + 18),
      basisBits (kData + 18) (joinDM ((selDataInAct kData).extractIndex z, v)) idx =
        Fin.addCases (basisBits kData ((selDataInAct kData).extractIndex z)) (basisBits 18 v) idx :=
    fun idx ↦ congrFun ((basisBitsEquiv (kData + 18)).apply_symm_apply _) idx
  apply (basisBitsEquiv (kData + 18)).injective
  funext idx
  change basisBits (kData + 18) (joinDM ((selDataInAct kData).extractIndex z, v)) idx =
    basisBits (kData + 18) ((selMeasInAct kData).replaceIndex z v) idx
  rw [hSymm idx]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · rw [Fin.addCases_left, QRegister.basisBits_extractIndex]
    have hi : selDataInAct kData i = Fin.castAdd 18 i :=
      Fin.ext (by simp [selDataInAct])
    have hnot : Fin.castAdd 18 i ∉ Set.range (selMeasInAct kData).wires := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      simp only [selMeasInAct, qreg_block_apply, Fin.val_castAdd] at hv
      have := i.isLt
      omega
    rw [hi, QRegister.basisBits_replaceIndex_of_not_mem (selMeasInAct kData) z v _ hnot]
  · rw [Fin.addCases_right]
    have hj : Fin.natAdd kData j = selMeasInAct kData j :=
      Fin.ext (by simp [selMeasInAct])
    rw [hj, QRegister.basisBits_replaceIndex_apply]
end ZeroHypElecHadHCompAndPass123Closure
namespace PartnerAndAnchorSlot18LensAndMidBA
open PosSlots24BranchConcrete (posCoreWires rElecSlot)
theorem rElecSlot_ofFin_val (e : Fin 218) (j : Fin 18) :
    (rElecSlot (QRegExt.ofFin posCoreWires) e j).val = 18 * e.val + j.val := rfl
end PartnerAndAnchorSlot18LensAndMidBA
namespace ElecHadTrueSwapLocalCompClosure
open BchCubeDecoder PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 (aliasPartner217 aliasPartner217_lt partnerTblVal216
  basisBits_partnerTblVal216)
open PosSlots24Barrel3Pass (rDataElec permUnitary_apply)
open StageADeconstrCore (selDataInAct selMeasInAct)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensLoadPerm lensWritePerm lensSwapPerm
  lensLoadPerm_involutive lensWritePerm_involutive lensWrite_lensLoad_zero_eq_swap
  lensWrite_lensSwap_zero_eq_dup)
/-- Wire index of `rPartnerIdx (QRegister.ofFin posCoreWires) d` (`= 3954 + (22 + d.val)`),
proved before marking `posCoreWires` irreducible. -/
theorem rPartnerIdx_ofFin_val (d : Fin 8) : (rPartnerIdx (QRegExt.ofFin posCoreWires) d).val
    = 3954 + (22 + d.val) := rfl
theorem liftPairIdx_congr_at {kData : ℕ} {F G : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^
    kData) × Fin (2 ^ 18)} {g : Fin (2 ^ (kData + 18))}
    (h : F (extractPair g) = G (extractPair g)) : liftPairIdx F g = liftPairIdx G g := by
  dsimp only [liftPairIdx]
  rw [h]
/-- Permutation equivalence on `Fin (2 ^ (kData + 18))` induced by `lensLoadPerm L`. -/
noncomputable def lensLoadEquiv {kData : ℕ} (L : Slot18Lens kData) : Equiv.Perm
    (Fin (2 ^ (kData + 18))) := Equiv.ofBijective (liftPairIdx (lensLoadPerm L))
    (liftPairIdx_involutive (lensLoadPerm_involutive L)).bijective
/-- Permutation equivalence on `Fin (2 ^ (kData + 18))` induced by `lensWritePerm L`. -/
noncomputable def lensWriteEquiv {kData : ℕ} (L : Slot18Lens kData) : Equiv.Perm
    (Fin (2 ^ (kData + 18))) := Equiv.ofBijective (liftPairIdx (lensWritePerm L))
    (liftPairIdx_involutive (lensWritePerm_involutive L)).bijective
/-- Unitary `uLensLoad L : Unitary (2 ^ (kData + 18))` for `lensLoadPerm L`. -/
noncomputable def uLensLoad {kData : ℕ} (L : Slot18Lens kData) : Unitary (2 ^ (kData + 18)) :=
    Operator.permutationUnitary (lensLoadEquiv L)
/-- Unitary `uLensWrite L : Unitary (2 ^ (kData + 18))` for `lensWritePerm L`. -/
noncomputable def uLensWrite {kData : ℕ} (L : Slot18Lens kData) : Unitary (2 ^ (kData + 18))
    := Operator.permutationUnitary (lensWriteEquiv L)
theorem lensWriteEquiv_lensLoadEquiv_of_zero {kData : ℕ} (L : Slot18Lens kData)
    (g : Fin (2 ^ (kData + 18))) (hg0 : (selMeasInAct kData).extractIndex g = 0) :
    (lensWriteEquiv L * lensLoadEquiv L) g = lensSwapEquiv L g := by
  change liftPairIdx (lensWritePerm L) (liftPairIdx (lensLoadPerm L) g) =
    liftPairIdx (lensSwapPerm L) g
  rw [liftPairIdx_comp]
  refine liftPairIdx_congr_at ?_
  dsimp only [extractPair]
  rw [hg0]
  exact lensWrite_lensLoad_zero_eq_swap L ((selDataInAct kData).extractIndex g)
theorem lensWriteEquiv_lensSwapEquiv_of_zero {kData : ℕ} (L : Slot18Lens kData)
    (g : Fin (2 ^ (kData + 18))) (hg0 : (selMeasInAct kData).extractIndex g = 0) :
    (lensWriteEquiv L * lensSwapEquiv L) g =
      (selMeasInAct kData).replaceIndex g (L.tbl ((selDataInAct kData).extractIndex g)) := by
  change liftPairIdx (lensWritePerm L) (liftPairIdx (lensSwapPerm L) g) = _
  rw [liftPairIdx_comp]
  dsimp only [liftPairIdx, extractPair]
  rw [hg0, lensWrite_lensSwap_zero_eq_dup, QRegister.replaceIndex_extractIndex]
open Classical in
/-- Columnwise criterion for equality after right-multiplying by `r.basisOutcomeProjector 0`. -/
theorem mul_basisOutcomeProjector_zero_eq_of_eq_on_zero {n k : ℕ}
    (r : QRegister k n) (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (h : ∀ i j : Fin (2 ^ n), r.extractIndex j = 0 → A i j = B i j) :
    A * r.basisOutcomeProjector 0 = B * r.basisOutcomeProjector 0 := by
  ext i j
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases hj : r.extractIndex j = 0
  · rw [ite_eq_left hj, mul_one, mul_one, h i j hj]
  · rw [ite_eq_right hj, mul_zero, mul_zero]
/-- **Unconditional Matrix-Level Uncompute-Load Identity for Any `Slot18Lens`
  (`uLensWrite_mul_uLensLoad_projZero_eq_uLensSwap`, `0 sorry`)**:
On `(selMeasInAct kData).basisOutcomeProjector 0`, `uLensWrite L * uLensLoad L` equals `uLensSwap
L`! -/
theorem uLensWrite_mul_uLensLoad_projZero_eq_uLensSwap {kData : ℕ} (L : Slot18Lens kData) :
    (uLensWrite L * uLensLoad L).1 * (selMeasInAct kData).basisOutcomeProjector 0 =
      (uLensSwap L).1 * (selMeasInAct kData).basisOutcomeProjector 0 := by
  have hMul : uLensWrite L * uLensLoad L =
      Operator.permutationUnitary (lensWriteEquiv L * lensLoadEquiv L) := by
    dsimp only [uLensWrite, uLensLoad]
    exact (OperatorExt.permutationUnitary_mul (lensWriteEquiv L) (lensLoadEquiv L)).symm
  rw [hMul]
  refine mul_basisOutcomeProjector_zero_eq_of_eq_on_zero (selMeasInAct kData) _ _ fun i j hj0 ↦ ?_
  dsimp only [uLensSwap]
  rw [permUnitary_apply, permUnitary_apply, lensWriteEquiv_lensLoadEquiv_of_zero L j hj0]
/-- **Unconditional Matrix-Level `hDup` Identity for Any `Slot18Lens`
  (`uLensWrite_mul_uLensSwap_projZero_eq_setTableOp`, `0 sorry`)**:
On `(selMeasInAct kData).basisOutcomeProjector 0`, `uLensWrite L * uLensSwap L` equals
`setTableOp (selDataInAct kData) (selMeasInAct kData) L.tbl`! -/
theorem uLensWrite_mul_uLensSwap_projZero_eq_setTableOp {kData : ℕ} (L : Slot18Lens kData) :
    (uLensWrite L * uLensSwap L).1 * (selMeasInAct kData).basisOutcomeProjector 0 =
      setTableOp (selDataInAct kData) (selMeasInAct kData) L.tbl *
        (selMeasInAct kData).basisOutcomeProjector 0 := by
  have hMul : uLensWrite L * uLensSwap L =
      Operator.permutationUnitary (lensWriteEquiv L * lensSwapEquiv L) := by
    dsimp only [uLensWrite, uLensSwap]
    exact (OperatorExt.permutationUnitary_mul (lensWriteEquiv L) (lensSwapEquiv L)).symm
  rw [hMul]
  refine mul_basisOutcomeProjector_zero_eq_of_eq_on_zero (selMeasInAct kData) _ _ fun i j hj0 ↦ ?_
  rw [permUnitary_apply, lensWriteEquiv_lensSwapEquiv_of_zero L j hj0]
  rfl
/-- `8`-wire partner index register inside `kData` via `selCore : QRegister posCoreWires kData`. -/
def rDataPartner {kData : ℕ} (selCore : QRegister posCoreWires kData) : QRegister 8 kData :=
  selCore.compose (rPartnerIdx (QRegExt.ofFin posCoreWires))
theorem rDataElec_disjoint_partner {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (e : Fin 218) : (rDataElec selCore e).DisjointWires (rDataPartner selCore) := by
  rw [QRegister.disjoint_iff]
  intro j d heq
  have hinj := selCore.wires.injective heq
  have hv := congrArg Fin.val hinj
  have h1 : (rElecSlot (QRegExt.ofFin posCoreWires) e j).val = 18 * e.val + j.val := rfl
  have h2 : (rPartnerIdx (QRegExt.ofFin posCoreWires) d).val = 3954 + (22 + d.val) :=
    rPartnerIdx_ofFin_val d
  rw [h1, h2] at hv
  have := e.isLt; have := j.isLt; omega
/-- Active partner electron slot `u + 1 ∈ {1 .. 217}` of data basis state `x : Fin (2 ^ kData)`. -/
def partnerActiveSlot {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (x : Fin (2 ^ kData)) : Fin 218 :=
  let βL := basisBits posCoreWires (selCore.extractIndex x)
  let rCoreL := QRegExt.ofFin posCoreWires
  let u := aliasPartner217 (regVal (rPartnerIdx rCoreL) βL)
  have hu : u + 1 < 218 := by
    have hv : regVal (rPartnerIdx rCoreL) βL < 256 := by
      simpa using regVal_lt_two_pow (rPartnerIdx rCoreL) βL
    have := aliasPartner217_lt hv
    omega
  ⟨u + 1, hu⟩
theorem partnerActiveSlot_eq_of_partner_eq {kData : ℕ}
    (selCore : QRegister posCoreWires kData) {x y : Fin (2 ^ kData)}
    (hPart : (rDataPartner selCore).extractIndex x = (rDataPartner selCore).extractIndex y) :
    partnerActiveSlot selCore x = partnerActiveSlot selCore y := by
  apply Fin.ext; dsimp only [partnerActiveSlot]
  refine congrArg (fun v ↦ aliasPartner217 v + 1) (regVal_congr_cross _ _ _ _ fun d ↦ ?_)
  have h1 : basisBits posCoreWires (selCore.extractIndex x) (rPartnerIdx (QRegExt.ofFin
    posCoreWires) d) =
      basisBits 8 ((rDataPartner selCore).extractIndex x) d := by
    conv_rhs =>
      dsimp [rDataPartner]; rw [QRegister.extractIndex_compose, QRegister.basisBits_extractIndex]
  have h2 : basisBits posCoreWires (selCore.extractIndex y) (rPartnerIdx (QRegExt.ofFin
    posCoreWires) d) =
      basisBits 8 ((rDataPartner selCore).extractIndex y) d := by
    conv_rhs =>
      dsimp [rDataPartner]; rw [QRegister.extractIndex_compose, QRegister.basisBits_extractIndex]
  rw [h1, h2, hPart]
theorem rDataPartner_extract_replace_elec {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (e : Fin 218) (x : Fin (2 ^ kData)) (v : Fin (2 ^ 18)) :
    (rDataPartner selCore).extractIndex ((rDataElec selCore e).replaceIndex x v) =
    (rDataPartner selCore).extractIndex x := QRegister.extractIndex_replaceIndex_of_disjoint
    (rDataPartner selCore) (rDataElec selCore e) (QRegExt.disjointWires_symm
      (rDataElec_disjoint_partner selCore e)) x
    v
theorem partnerActiveSlot_replace_active {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (d : Fin (2 ^ kData)) (v : Fin (2 ^ 18)) : partnerActiveSlot selCore
    ((rDataElec selCore (partnerActiveSlot selCore d)).replaceIndex d v) = partnerActiveSlot
    selCore d := partnerActiveSlot_eq_of_partner_eq selCore (rDataPartner_extract_replace_elec
    selCore (partnerActiveSlot selCore d) d v)
theorem partnerTblVal216_eq_extract (y : Fin (2 ^ posCoreWires)) :
    partnerTblVal216 y =
      (rElecSlot (QRegExt.ofFin posCoreWires)
        ⟨aliasPartner217 (regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires
          y)) + 1,
          by
            have hv : regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires y) <
              256 := by
              simpa using regVal_lt_two_pow (rPartnerIdx (QRegExt.ofFin posCoreWires)) (basisBits
                posCoreWires y)
            have := aliasPartner217_lt hv
            omega⟩).extractIndex y :=
  eq_of_basisBits_eq fun j ↦ by
    rw [basisBits_partnerTblVal216, QRegister.basisBits_extractIndex]
/-- **Concrete `Slot18Lens kData` for the 216-Slot Partner Bank (`partnerLens216`, `0 sorry`)**. -/
noncomputable def partnerLens216 {kData : ℕ}
    (selCore : QRegister posCoreWires kData) : Slot18Lens kData where
  tbl d := (rDataElec selCore (partnerActiveSlot selCore d)).extractIndex d
  updSlot d v := (rDataElec selCore (partnerActiveSlot selCore d)).replaceIndex d v
  get_put d v := by
    rw [partnerActiveSlot_replace_active selCore d v, QRegister.extractIndex_replaceIndex]
  put_get d := QRegister.replaceIndex_extractIndex _ d
  put_put d v₁ v₂ := by
    rw [partnerActiveSlot_replace_active selCore d v₁, QRegister.replaceIndex_replaceIndex]
theorem partnerLens216_tbl_eq {kData : ℕ}
    (selCore : QRegister posCoreWires kData) (d : Fin (2 ^ kData)) :
    (partnerLens216 selCore).tbl d = partnerTblVal216 (selCore.extractIndex d) := by
  dsimp only [partnerLens216, partnerActiveSlot, rDataElec]
  rw [QRegister.extractIndex_compose, ← partnerTblVal216_eq_extract]
end ElecHadTrueSwapLocalCompClosure
section ConjHStreamBody
open StageADeconstrCore (selDataInAct selMeasInAct)
open ZeroHypElecHadHCompAndPass123Closure (joinDM joinDM_eq_replaceIndex_selMeasInAct)
namespace PureCnotLoadAndSlot18LensRealizes
/-- For any `g : Fin (2 ^ (kData + 18))` and `p : Fin (2 ^ kData) × Fin (2 ^ 18)`,
`joinDM p` equals `(selMeasInAct kData).replaceIndex ((selDataInAct kData).replaceIndex g p.1) p.2`.
-/
theorem joinDM_eq_replaceIndex_pair {kData : ℕ} (g : Fin (2 ^ (kData + 18)))
    (p : Fin (2 ^ kData) × Fin (2 ^ 18)) : joinDM p = (selMeasInAct kData).replaceIndex
    ((selDataInAct kData).replaceIndex g p.1) p.2 := by
  rcases p with ⟨d, v⟩
  have h1 : d = (selDataInAct kData).extractIndex ((selDataInAct kData).replaceIndex g d) :=
    (QRegister.extractIndex_replaceIndex (selDataInAct kData) g d).symm
  conv_lhs => rw [h1]
  exact joinDM_eq_replaceIndex_selMeasInAct ((selDataInAct kData).replaceIndex g d) v
end PureCnotLoadAndSlot18LensRealizes
end ConjHStreamBody
namespace ZeroHypSlot0CommAndHMidClosure
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_disj_selMeasInAct)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open ElecHadTrueSwapLocalCompClosure (extractPair liftPairIdx extractPair_liftPairIdx uLensSwap
  mul_basisOutcomeProjector_zero_eq_of_eq_on_zero)
open ZeroHypElecHadHCompAndPass123Closure (splitDM joinDM joinDM_splitDM)
/-- Embeds a pair `(d, y) : Fin (2 ^ kData) × Fin (2 ^ 18)` into `Fin (2 ^ (kData + 18))` via
  `liftPairIdx`. -/
noncomputable def liftPair0 {kData : ℕ} (p : Fin (2 ^ kData) × Fin (2 ^ 18)) : Fin
    (2 ^ (kData + 18)) := liftPairIdx (fun _ ↦ p) 0
@[simp] theorem extractPair_liftPair0 {kData : ℕ} (p : Fin (2 ^ kData) × Fin (2 ^ 18)) :
    extractPair (liftPair0 p) = p := extractPair_liftPairIdx (fun _ ↦ p) 0
@[simp] theorem selDataInAct_extractIndex_liftPair0 {kData : ℕ} (d : Fin (2 ^ kData))
    (y : Fin (2 ^ 18)) : (selDataInAct kData).extractIndex (liftPair0 (d, y)) = d := by
  change (extractPair (liftPair0 (d, y))).1 = d
  rw [extractPair_liftPair0]
@[simp] theorem selMeasInAct_extractIndex_liftPair0 {kData : ℕ} (d : Fin (2 ^ kData))
    (y : Fin (2 ^ 18)) : (selMeasInAct kData).extractIndex (liftPair0 (d, y)) = y := by
  change (extractPair (liftPair0 (d, y))).2 = y
  rw [extractPair_liftPair0]
theorem extractPair_injective {kData : ℕ} {x y : Fin (2 ^ (kData + 18))}
    (h : extractPair x = extractPair y) : x = y := by
  have hx : joinDM (splitDM x) = x := joinDM_splitDM x
  have hy : joinDM (splitDM y) = y := joinDM_splitDM y
  have hsp : splitDM x = splitDM y := h
  rw [← hx, ← hy, hsp]
@[simp] theorem liftPair0_extractPair {kData : ℕ} (z : Fin (2 ^ (kData + 18))) : liftPair0
    (extractPair z) = z := extractPair_injective (extractPair_liftPair0 (extractPair z))
open Classical in
theorem liftPair0_zero_of_meas_zero {kData : ℕ} {z : Fin (2 ^ (kData + 18))}
    (hz : (selMeasInAct kData).extractIndex z = 0) :
    liftPair0 ((selDataInAct kData).extractIndex z, 0) = z := by
  have hPair : ((selDataInAct kData).extractIndex z, (0 : Fin (2 ^ 18))) = extractPair z :=
    Prod.ext rfl hz.symm
  rw [hPair, liftPair0_extractPair]
/-- On `kData + 18` qubits, `x` and `y` have the same environment outside `selDataInAct kData`
if and only if they have the same `selMeasInAct kData` outcome. -/
theorem selDataInAct_basisSplitEquiv_snd_eq_iff {kData : ℕ} (x y : Fin (2 ^ (kData + 18))) :
    ((selDataInAct kData).basisSplitEquiv x).2 = ((selDataInAct kData).basisSplitEquiv y).2 ↔
    (selMeasInAct kData).extractIndex x = (selMeasInAct kData).extractIndex y := by
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let x' := selD.replaceIndex y (selD.extractIndex x)
  have hx'D : selD.extractIndex x' = selD.extractIndex x :=
    selD.extractIndex_replaceIndex y (selD.extractIndex x)
  have hx'M : selM.extractIndex x' = selM.extractIndex y :=
    QRegister.extractIndex_replaceIndex_of_disjoint selM selD
      (QRegExt.disjointWires_symm (selDataInAct_disj_selMeasInAct kData)) y (selD.extractIndex x)
  have hx'Env : (selD.basisSplitEquiv x').2 = (selD.basisSplitEquiv y).2 := by
    dsimp only [x']
    rw [selD.basisSplitEquiv_replaceIndex]
  constructor
  · intro henv
    have h1 : (selD.basisSplitEquiv x').1 = (selD.basisSplitEquiv x).1 := by
      rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst, hx'D]
    have h2 : (selD.basisSplitEquiv x').2 = (selD.basisSplitEquiv x).2 :=
      hx'Env.trans henv.symm
    have hxx' : x' = x := selD.basisSplitEquiv.injective (Prod.ext h1 h2)
    rw [← hxx', hx'M]
  · intro hM
    have hxx' : x' = x := extractPair_injective (Prod.ext hx'D (hx'M.trans hM.symm))
    rw [← hxx', hx'Env]
open Classical in
/-- Explicit matrix entry of `(selDataInAct kData).embedMatrix M` on `kData + 18` qubits. -/
theorem embedMatrix_selDataInAct_apply {kData : ℕ} (M : Operator (2 ^ kData))
    (i j : Fin (2 ^ (kData + 18))) : ((selDataInAct kData).embedMatrix M) i j = if
    (selMeasInAct kData).extractIndex i = (selMeasInAct kData).extractIndex j then M
    ((selDataInAct kData).extractIndex i) ((selDataInAct kData).extractIndex j) else 0 := by
  rw [QRegister.embedMatrix_apply]
  by_cases hM : (selMeasInAct kData).extractIndex i = (selMeasInAct kData).extractIndex j
  · have henv := (selDataInAct_basisSplitEquiv_snd_eq_iff i j).mpr hM
    rw [ite_eq_left henv, ite_eq_left hM, mul_one]
  · have henv : ((selDataInAct kData).basisSplitEquiv i).2 ≠ ((selDataInAct kData).basisSplitEquiv
      j).2 :=
      fun h ↦ hM ((selDataInAct_basisSplitEquiv_snd_eq_iff i j).mp h)
    rw [ite_eq_right henv, ite_eq_right hM, mul_zero]
open Classical in
/-- Injectivity of `M ↦ (selDataInAct kData).embedMatrix M * (selMeasInAct
  kData).basisOutcomeProjector 0`. -/
theorem embedMatrix_selDataInAct_inj_on_Pm {kData : ℕ} {A B : Operator (2 ^ kData)}
    (h : (selDataInAct kData).embedMatrix A * (selMeasInAct kData).basisOutcomeProjector 0 =
      (selDataInAct kData).embedMatrix B * (selMeasInAct kData).basisOutcomeProjector 0) :
    A = B := by
  ext d' d
  let i := liftPair0 (d', (0 : Fin (2 ^ 18)))
  let j := liftPair0 (d, (0 : Fin (2 ^ 18)))
  have hij := congrFun (congrFun h i) j
  have hi0 : (selMeasInAct kData).extractIndex i = 0 := selMeasInAct_extractIndex_liftPair0 d' 0
  have hj0 : (selMeasInAct kData).extractIndex j = 0 := selMeasInAct_extractIndex_liftPair0 d 0
  have hiD : (selDataInAct kData).extractIndex i = d' := selDataInAct_extractIndex_liftPair0 d' 0
  have hjD : (selDataInAct kData).extractIndex j = d := selDataInAct_extractIndex_liftPair0 d 0
  rw[QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal,
      ite_eq_left hj0, mul_one, mul_one, embedMatrix_selDataInAct_apply,
      embedMatrix_selDataInAct_apply, hi0, hj0, ite_eq_left rfl, hiD, hjD] at hij
  exact hij
/-- Restricts any operator `A : Operator (2 ^ (kData + 18))` to its `2^kData × 2^kData` block on
`(selMeasInAct kData).extractIndex = 0` (`(d', 0), (d, 0)`). -/
noncomputable def restrictMat {kData : ℕ} (A : Operator (2 ^ (kData + 18))) : Operator
    (2 ^ kData) := Matrix.of fun d' d ↦ A (liftPair0 (d', 0)) (liftPair0 (d, 0))
@[simp] theorem restrictMat_apply {kData : ℕ} (A : Operator (2 ^ (kData + 18)))
    (d' d : Fin (2 ^ kData)) : restrictMat A d' d = A (liftPair0 (d', 0)) (liftPair0 (d, 0))
    := rfl
open Classical in
/-- Whenever `A` commutes with `Pm := (selMeasInAct kData).basisOutcomeProjector 0`,
`A * Pm = (selDataInAct kData).embedMatrix (restrictMat A) * Pm`. -/
theorem op_mul_Pm_eq_embedMatrix_restrictMat {kData : ℕ}
    (A : Operator (2 ^ (kData + 18)))
    (hComm : A * (selMeasInAct kData).basisOutcomeProjector 0 =
      (selMeasInAct kData).basisOutcomeProjector 0 * A) :
    let selD := selDataInAct kData
    let selM := selMeasInAct kData
    A * selM.basisOutcomeProjector 0 =
      selD.embedMatrix (restrictMat A) * selM.basisOutcomeProjector 0 := by
  intro selD selM
  refine mul_basisOutcomeProjector_zero_eq_of_eq_on_zero selM _ _ fun i j hj0 ↦ ?_
  rw [embedMatrix_selDataInAct_apply, hj0]
  by_cases hi0 : selM.extractIndex i = 0
  · rw [ite_eq_left hi0, restrictMat_apply,
        liftPair0_zero_of_meas_zero hi0, liftPair0_zero_of_meas_zero hj0]
  · rw [ite_eq_right hi0]
    have hij := congrFun (congrFun hComm i) j
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
        ite_eq_left hj0, ite_eq_right hi0, mul_one, zero_mul] at hij
    exact hij
theorem basisOutcomeProjector_zero_conjTranspose {n k : ℕ} (r : QRegister k n) :
    (r.basisOutcomeProjector 0)ᴴ = r.basisOutcomeProjector 0 := by
  ext i j
  simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hz : r.extractIndex i = 0 <;> simp [hz]
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]
/-- Unitarity of `restrictMat V.1` whenever `V : Unitary (2 ^ (kData + 18))` commutes with `Pm`. -/
theorem restrictMat_mem_unitaryGroup_of_comm_Pm {kData : ℕ} (V : Unitary (2 ^ (kData + 18)))
    (hComm : V.1 * (selMeasInAct kData).basisOutcomeProjector 0 = (selMeasInAct
    kData).basisOutcomeProjector 0 * V.1) : restrictMat V.1 ∈ Matrix.unitaryGroup
    (Fin (2 ^ kData)) ℂ := by
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let Pm := selM.basisOutcomeProjector 0
  let M := restrictMat V.1
  have hVPm : V.1 * Pm = selD.embedMatrix M * Pm :=
    op_mul_Pm_eq_embedMatrix_restrictMat V.1 hComm
  have hPmH : Pmᴴ = Pm := basisOutcomeProjector_zero_conjTranspose selM
  have hPm2 : Pm * Pm = Pm := basisOutcomeProjector_zero_mul_self selM
  have hCommM : selD.embedMatrix M * Pm = Pm * selD.embedMatrix M :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selD) selM
      (selDataInAct_disj_selMeasInAct kData) M 0
  have hV2 : V.1ᴴ * V.1 = 1 := by
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp V.2
  have hM2Pm : selD.embedMatrix (Mᴴ * M) * Pm = selD.embedMatrix 1 * Pm := by
    calc
      selD.embedMatrix (Mᴴ * M) * Pm
        = (selD.embedMatrix M)ᴴ * (selD.embedMatrix M * Pm) := by
            rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_conjTranspose, Matrix.mul_assoc]
      _ = (selD.embedMatrix M)ᴴ * (Pm * (V.1 * Pm)) := by
            rw [← hVPm, ← Matrix.mul_assoc Pm V.1 Pm, ← hComm, Matrix.mul_assoc V.1 Pm Pm, hPm2]
      _ = (Pm * selD.embedMatrix M)ᴴ * (V.1 * Pm) := by
            rw [Matrix.conjTranspose_mul, hPmH, Matrix.mul_assoc]
      _ = (selD.embedMatrix M * Pm)ᴴ * (V.1 * Pm) := by
            rw [hCommM]
      _ = (V.1 * Pm)ᴴ * (V.1 * Pm) := by
            rw [hVPm]
      _ = Pm * (V.1ᴴ * V.1) * Pm := by
            rw [Matrix.conjTranspose_mul, hPmH]
            simp only [Matrix.mul_assoc]
      _ = selD.embedMatrix 1 * Pm := by
            rw [hV2, Matrix.mul_one, hPm2, QRegister.embedMatrix_one, Matrix.one_mul]
  have hLeft : star M * M = 1 := by
    rw [star_eq_conjTranspose]
    exact embedMatrix_selDataInAct_inj_on_Pm hM2Pm
  exact Matrix.mem_unitaryGroup_iff'.mpr hLeft
/-- **Invariant-Subspace Unitary Restriction on `Pm` (`restrictToMeasZero`, `0 sorry`)**:
For any `V : Unitary (2 ^ (kData + 18))` commuting with `Pm = (selMeasInAct
kData).basisOutcomeProjector 0`,
constructs the restricted unitary `restrictToMeasZero V hComm : Unitary (2 ^ kData)` with matrix
entry
`V.1 (liftPair0 (d', 0)) (liftPair0 (d, 0))`. -/
noncomputable def restrictToMeasZero {kData : ℕ} (V : Unitary (2 ^ (kData + 18))) (hComm : V.1
    * (selMeasInAct kData).basisOutcomeProjector 0 = (selMeasInAct
    kData).basisOutcomeProjector 0 * V.1) : Unitary (2 ^ kData) :=
    ⟨restrictMat V.1, restrictMat_mem_unitaryGroup_of_comm_Pm V hComm⟩
/-- Swap-conjugated unitary `V := uLensSwap L * uMid * uLensSwap L`. -/
noncomputable def swapConjUnitary {kData : ℕ} (L : Slot18Lens kData)
    (uMid : Unitary (2 ^ (kData + 18))) : Unitary (2 ^ (kData + 18)) :=
  uLensSwap L * uMid * uLensSwap L
/-- Whenever `uMid` commutes with `P_slot0 L`, `swapConjUnitary L uMid` commutes with `Pm`. -/
theorem swapConjUnitary_comm_Pm {kData : ℕ} (L : Slot18Lens kData)
    (uMid : Unitary (2 ^ (kData + 18))) (hCommSlot0 : uMid.1 * P_slot0 L = P_slot0 L * uMid.1)
    : (swapConjUnitary L uMid).1 * (selMeasInAct kData).basisOutcomeProjector 0 =
    (selMeasInAct kData).basisOutcomeProjector 0 * (swapConjUnitary L uMid).1 := by
  let S := (uLensSwap L).1
  let Pm := (selMeasInAct kData).basisOutcomeProjector 0
  have hS2 : S * S = 1 := uLensSwap_val_mul_self L
  change (S * uMid.1 * S) * Pm = Pm * (S * uMid.1 * S)
  change uMid.1 * (S * Pm * S) = (S * Pm * S) * uMid.1 at hCommSlot0
  calc
    (S * uMid.1 * S) * Pm
      = S * (uMid.1 * (S * Pm * S)) * S := by
          calc
            (S * uMid.1 * S) * Pm = (S * uMid.1 * S * Pm) * 1 := (Matrix.mul_one _).symm
            _ = (S * uMid.1 * S * Pm) * (S * S) := by rw [hS2]
            _ = S * (uMid.1 * (S * Pm * S)) * S := by simp only [Matrix.mul_assoc]
    _ = S * ((S * Pm * S) * uMid.1) * S := by rw [hCommSlot0]
    _ = (S * S) * Pm * (S * uMid.1 * S) := by simp only [Matrix.mul_assoc]
    _ = Pm * (S * uMid.1 * S) := by rw [hS2, Matrix.one_mul]
/-- Restricted data unitary `restrictOfCommSlot0 L uMid hCommSlot0 : Unitary (2 ^ kData)` obtained
by conjugating `uMid` by `uLensSwap L` and restricting to `Pm`. -/
noncomputable def restrictOfCommSlot0 {kData : ℕ} (L : Slot18Lens kData)
    (uMid : Unitary (2 ^ (kData + 18))) (hCommSlot0 : uMid.1 * P_slot0 L = P_slot0 L * uMid.1)
    : Unitary (2 ^ kData) := restrictToMeasZero (swapConjUnitary L uMid)
    (swapConjUnitary_comm_Pm L uMid hCommSlot0)
/-- Closure of `P_slot0 L` commutation under unitary multiplication (`mul_comm_P_slot0`, `0
  sorry`). -/
theorem mul_comm_P_slot0 {kData : ℕ} (L : Slot18Lens kData)
    {U₁ U₂ : Unitary (2 ^ (kData + 18))} (h1 : U₁.1 * P_slot0 L = P_slot0 L * U₁.1)
    (h2 : U₂.1 * P_slot0 L = P_slot0 L * U₂.1) : (U₁ * U₂).1 * P_slot0 L = P_slot0 L *
    (U₁ * U₂).1 := by
  rw [Submonoid.coe_mul, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
/-- Closure of `P_slot0 L` commutation under unitary inversion (`inv_comm_P_slot0`, `0 sorry`). -/
theorem inv_comm_P_slot0 {kData : ℕ} (L : Slot18Lens kData) {U : Unitary (2 ^ (kData + 18))}
    (hU : U.1 * P_slot0 L = P_slot0 L * U.1) : (U⁻¹).1 * P_slot0 L = P_slot0 L * (U⁻¹).1 := by
  have h1 : (U⁻¹ * U).1 = 1 := by rw [inv_mul_cancel, Submonoid.coe_one]
  have h2 : (U * U⁻¹).1 = 1 := by rw [mul_inv_cancel, Submonoid.coe_one]
  calc
    (U⁻¹).1 * P_slot0 L
      = (U⁻¹).1 * P_slot0 L * (U * U⁻¹).1 := by rw [h2, Matrix.mul_one]
    _ = (U⁻¹).1 * (P_slot0 L * U.1) * (U⁻¹).1 := by
          rw [Submonoid.coe_mul]; simp only [Matrix.mul_assoc]
    _ = ((U⁻¹).1 * U.1) * P_slot0 L * (U⁻¹).1 := by
          rw [← hU]; simp only [Matrix.mul_assoc]
    _ = P_slot0 L * (U⁻¹).1 := by
          rw [← Submonoid.coe_mul, h1, Matrix.one_mul]
open Classical in
/-- Any embedded `diagSignUnitary` is a diagonal matrix on the ambient space. -/
theorem embedUnitary_diagSignUnitary_eq_diagonal {n k : ℕ}
    (rSub : QRegister k n) (phase : Fin (2 ^ k) → Bool) :
    (rSub.embedUnitary (diagSignUnitary phase)).1 =
      Matrix.diagonal (fun x : Fin (2 ^ n) ↦ if phase (rSub.extractIndex x) then (-1 : ℂ) else 1) :=
        by
  ext i j
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, mul_one, Matrix.diagonal_apply_eq]
    dsimp only [diagSignUnitary]
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij]
    by_cases henv : (rSub.basisSplitEquiv i).2 = (rSub.basisSplitEquiv j).2
    · have h1ne : rSub.extractIndex i ≠ rSub.extractIndex j := by
        intro h1
        apply hij
        apply rSub.basisSplitEquiv.injective
        refine Prod.ext ?_ henv
        rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst, h1]
      dsimp only [diagSignUnitary]
      rw [Matrix.diagonal_apply_ne _ h1ne, zero_mul]
    · rw [ite_eq_right henv, mul_zero]
open Classical in
/-- **100% Zero-Hypothesis `P_slot0 L` Commutation for Any Embedded `diagSignUnitary`
(`diagSignUnitary_embed_comm_P_slot0`, `0 sorry`)**:
Every `rSub.embedUnitary (diagSignUnitary phase)` (such as `uSand18`, `uPointCrossRsum42Cat128`, or
`uInnerAHead128`) is diagonal and therefore commutes with `P_slot0 L` with **0 hypotheses**! -/
theorem diagSignUnitary_embed_comm_P_slot0 {kData k : ℕ} (L : Slot18Lens kData)
    (rSub : QRegister k (kData + 18)) (phase : Fin (2 ^ k) → Bool) :
    (rSub.embedUnitary (diagSignUnitary phase)).1 * P_slot0 L = P_slot0 L *
    (rSub.embedUnitary (diagSignUnitary phase)).1 := by
  rw [embedUnitary_diagSignUnitary_eq_diagonal, P_slot0_eq_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  exact mul_comm _ _
open Classical in
/-- **General Wire-Disjoint Subregister Commutation with Diagonal Operators
(`disjoint_embedMatrix_comm_diagonal_of_extract`, `0 sorry`)**:
If `f : Fin (2 ^ n) → ℂ` depends only on `rCore.extractIndex` (`∀ x y, rCore.extractIndex x =
rCore.extractIndex y → f x = f y`)
and `rSub : QRegister kSub n` is wire-disjoint from `rCore` (`rSub.DisjointWires rCore`), then
`rSub.embedMatrix M` commutes with `Matrix.diagonal f` for any `M : Operator (2 ^ kSub)`! -/
theorem disjoint_embedMatrix_comm_diagonal_of_extract {n kCore kSub : ℕ}
    (rCore : QRegister kCore n) (rSub : QRegister kSub n) (hDisj : rSub.DisjointWires rCore)
    (f : Fin (2 ^ n) → ℂ) (hf : ∀ x y : Fin (2 ^ n), rCore.extractIndex x = rCore.extractIndex
    y → f x = f y) (M : Operator (2 ^ kSub)) : rSub.embedMatrix M * Matrix.diagonal f =
    Matrix.diagonal f * rSub.embedMatrix M := by
  ext x y
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, QRegister.embedMatrix_apply]
  by_cases henv : (rSub.basisSplitEquiv x).2 = (rSub.basisSplitEquiv y).2
  · have hOut : rSub.AgreeOutside x y := (rSub.basisSplit_environment_eq_iff x y).mp henv
    have hCoreEq : rCore.extractIndex x = rCore.extractIndex y := by
      rw [← (basisBitsEquiv kCore).apply_eq_iff_eq]
      funext j
      simp only [basisBitsEquiv, QRegister.basisBits_extractIndex]
      exact hOut (rCore j) (fun ⟨i, hi⟩ ↦ hDisj.ne i j hi)
    rw [ite_eq_left henv, hf x y hCoreEq, mul_comm (f y)]
  · simp [henv]
end ZeroHypSlot0CommAndHMidClosure
namespace PureCnotLoadAndZeroHypSlot18LensClosure
open PosSlots24Barrel3Pass (permUnitary_apply)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensSwapPerm)
open ZeroHypElecHadHCompAndPass123Closure (permMatrix splitDM joinDM joinDM_splitDM lensSwapFin
  uLensSwap)
open ElecHadTrueSwapLocalCompClosure (extractPair liftPairIdx extractPair_liftPairIdx lensSwapEquiv)
/-- `liftPairIdx` and `joinDM ∘ F ∘ splitDM` are identical on all `z`. -/
theorem liftPairIdx_eq_joinDM {kData : ℕ} (F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^
    kData) × Fin (2 ^ 18)) (z : Fin (2 ^ (kData + 18))) : liftPairIdx F z = joinDM
    (F (splitDM z)) := by
  have h1 : extractPair (liftPairIdx F z) = F (splitDM z) := extractPair_liftPairIdx F z
  calc
    liftPairIdx F z = joinDM (splitDM (liftPairIdx F z)) := (joinDM_splitDM _).symm
    _ = joinDM (F (splitDM z)) := congrArg joinDM h1
@[simp] theorem uLensSwap_slot18_eq_partner {kData : ℕ} (L : Slot18Lens kData) :
    ElecHadTrueSwapLocalCompClosure.uLensSwap L = uLensSwap L := by
  apply Subtype.ext; ext i j
  change (Operator.permutationUnitary (lensSwapEquiv L)).1 i j = permMatrix (lensSwapFin L) i j
  rw [permUnitary_apply]
  change (if i = liftPairIdx (lensSwapPerm L) j then (1 : ℂ) else 0) =
    if i = lensSwapFin L j then 1 else 0
  rw [liftPairIdx_eq_joinDM]
  rfl
open Classical in
theorem embedMatrix_permMatrix_mulVec_single {n k : ℕ} (r : QRegister k n)
    (f : Fin (2 ^ k) → Fin (2 ^ k)) (g : Fin (2 ^ n)) : (r.embedMatrix (permMatrix f)).mulVec
    (Pi.single g 1) = Pi.single (r.replaceIndex g (f (r.extractIndex g))) 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change (r.embedMatrix (permMatrix f)) i g =
    (Pi.single (r.replaceIndex g (f (r.extractIndex g))) (1 : ℂ) : Fin (2 ^ n) → ℂ) i
  rw [QRegister.embedMatrix_apply]
  unfold permMatrix
  rw [Matrix.of_apply]
  let zTarget := f (r.extractIndex g)
  change (if r.extractIndex i = zTarget then (1 : ℂ) else 0) *
      (if (r.basisSplitEquiv i).2 = (r.basisSplitEquiv g).2 then 1 else 0) =
    (Pi.single (r.replaceIndex g zTarget) (1 : ℂ) : Fin (2 ^ n) → ℂ) i
  by_cases henv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv g).2
  · rw [ite_eq_left henv, mul_one]
    have hiff : r.extractIndex i = zTarget ↔ i = r.replaceIndex g zTarget := by
      constructor
      · intro hex
        have h1 : (r.basisSplitEquiv i).1 = (r.basisSplitEquiv (r.replaceIndex g zTarget)).1 := by
          rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst,
              r.extractIndex_replaceIndex, hex]
        have h2 : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv (r.replaceIndex g zTarget)).2 := by
          rw [henv, r.basisSplitEquiv_replaceIndex]
        exact r.basisSplitEquiv.injective (Prod.ext h1 h2)
      · rintro rfl
        exact r.extractIndex_replaceIndex g zTarget
    by_cases h1 : r.extractIndex i = zTarget
    · rw [ite_eq_left h1, hiff.mp h1, Pi.single_eq_same]
    · have hne : i ≠ r.replaceIndex g zTarget := fun h2 ↦ h1 (hiff.mpr h2)
      rw [ite_eq_right h1, Pi.single_eq_of_ne hne]
  · rw [ite_eq_right henv, mul_zero]
    have hne : i ≠ r.replaceIndex g zTarget := by
      rintro rfl
      apply henv
      rw [r.basisSplitEquiv_replaceIndex]
    rw [Pi.single_eq_of_ne hne]
export ZeroHypElecHadHCompAndPass123Closure (permMatrix permUnitary splitDM joinDM splitDM_joinDM
  joinDM_splitDM joinDM_eq_replaceIndex_selMeasInAct lensSwapFin lensSwapFin_involutive uLensSwap)
export ElecHadTrueSwapLocalCompClosure (extractPair liftPairIdx extractPair_liftPairIdx
  lensLoadEquiv lensWriteEquiv lensSwapEquiv partnerLens216)
end PureCnotLoadAndZeroHypSlot18LensClosure
namespace PureCnotLensLoadAndZeroHypTrueSwap
open MeasureBranchHadamardSem (eval_seq_mulVec ket_H matrix_ext_ket)
open PosSlots24Barrel3Pass (permUnitary_apply)
open ElecHadTrueSwapHCompClosure (extractIndex_compose_eq replaceIndex_compose_eq)
open StageADeconstrCore (selMeasInAct concat_compose_selDataInAct concat_compose_selMeasInAct)
open ElecHadConjLoadAndTrueSwapComp (xor18 Slot18Lens lensLoadPerm)
open ElecHadTrueSwapLocalCompClosure (extractPair liftPairIdx lensLoadEquiv uLensLoad)
/-- Hadamards on distinct wires commute (`(Circuit.H a).eval * (Circuit.H b).eval = (Circuit.H
  b).eval * (Circuit.H a).eval`). -/
theorem eval_H_comm {k : ℕ} (a b : Wire k) (hne : a ≠ b) :
    (Circuit.H a).eval * (Circuit.H b).eval = (Circuit.H b).eval * (Circuit.H a).eval := by
  change (Circuit.H b ;;ᶜ Circuit.H a).eval = (Circuit.H a ;;ᶜ Circuit.H b).eval
  apply Subtype.ext
  apply matrix_ext_ket; intro β
  simp only [eval_seq_mulVec, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
    Function.update_of_ne hne, Function.update_of_ne hne.symm, Function.update_comm hne]
  ext idx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
open Classical in
/-- Action of `Operator.permutationUnitary σ` on a standard basis vector `Pi.single w 1`. -/
theorem permutationUnitary_mulVec_single {d : ℕ} (σ : Equiv.Perm (Fin d)) (w : Fin d) :
    (Operator.permutationUnitary σ).1.mulVec (Pi.single w 1) = Pi.single (σ w) 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change (Operator.permutationUnitary σ).1 i w = (Pi.single (σ w) (1 : ℂ) : Fin d → ℂ) i
  rw [permUnitary_apply]
  by_cases h : σ w = i
  · subst h; simp
  · have hne : i ≠ σ w := Ne.symm h
    simp [hne]
open Classical in
/-- Action of `r.embedUnitary (Operator.permutationUnitary σ)` on a standard basis vector
  `Pi.single g 1`. -/
theorem embedUnitary_permutationUnitary_mulVec_single {n k : ℕ}
    (r : QRegister k n) (σ : Equiv.Perm (Fin (2 ^ k))) (g : Fin (2 ^ n)) :
    (r.embedUnitary (Operator.permutationUnitary σ)).1.mulVec (Pi.single g 1) =
      Pi.single (r.replaceIndex g (σ (r.extractIndex g))) 1 := by
  rw [QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
      permutationUnitary_mulVec_single, QRegister.tensorState_single_replaceIndex]
open Classical in
/-- Action of `(rData.concat rMeas hDM).embedUnitary (uLensLoad L)` on `Pi.single g 1`. -/
theorem embedUnitary_uLensLoad_mulVec_single {n kData : ℕ} (rData : QRegister kData n)
    (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) (L : Slot18Lens kData)
    (tbl : Fin (2 ^ kData) → Fin (2 ^ 18)) (hTbl : ∀ d, L.tbl d = tbl d) (g : Fin (2 ^ n)) :
    ((rData.concat rMeas hDM).embedUnitary (uLensLoad L)).1.mulVec (Pi.single g 1) = Pi.single
    (rMeas.replaceIndex g (xor18 (rMeas.extractIndex g) (tbl (rData.extractIndex g)))) 1 := by
  let rAct := rData.concat rMeas hDM
  dsimp only [uLensLoad]
  rw [embedUnitary_permutationUnitary_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  have hApp : lensLoadEquiv L (rAct.extractIndex g) = (selMeasInAct kData).replaceIndex
      (rAct.extractIndex g) (xor18 (rMeas.extractIndex g) (tbl (rData.extractIndex g))) := by
    change liftPairIdx (lensLoadPerm L) (rAct.extractIndex g) = _
    dsimp only [liftPairIdx, extractPair, lensLoadPerm, rAct]
    rw [QRegister.replaceIndex_extractIndex, hTbl,
        extractIndex_compose_eq, concat_compose_selMeasInAct rData rMeas hDM,
        extractIndex_compose_eq, concat_compose_selDataInAct rData rMeas hDM]
  rw [hApp, replaceIndex_compose_eq, concat_compose_selMeasInAct rData rMeas hDM]
end PureCnotLensLoadAndZeroHypTrueSwap
namespace BoothOpt_03_CoinBarrelIdxFastTrueSwap
open FullSysCatSegmentBridge (fullSysCoreWires)
open MeasureBranchHadamardSem (ket bitSign sqrtHalf bit_cases matrix_ext_ket eval_seq_mulVec ket_H
  ket_CNOT)
open CoinDispatchedBarrel288 (coinBarrelIdxFast)
open PosSlots24BranchConcrete (posCoreWires rElecSlot)
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open PosSlots24Barrel3Pass (rDataElec permUnitary_apply)
open FullConcrete7StepAndTrueSwapSelect (cHadamardPrefix uHadamardAll eval_cHadamardAll)
open ElecHadConjLoadAndTrueSwapComp (sqrtHalf_sq_mul_two xor18 basisBits_xor18 Slot18Lens
  lensLoadPerm lensWritePerm)
open ElecHadTrueSwapHCompClosure (uWriteSub h3924_le_posCoreWires)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure (extractPair liftPairIdx lensLoadEquiv lensWriteEquiv uLensLoad
  uLensWrite)
/-- Single-qubit Hadamard is self-inverse: `(Circuit.H w).eval * (Circuit.H w).eval = 1`. -/
theorem eval_H_mul_self {N : ℕ} (w : Wire N) :
    (Circuit.H w).eval * (Circuit.H w).eval = 1 := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_H, Matrix.mulVec_add,
      Matrix.mulVec_smul, Function.update_self, Function.update_idem,
      OneMemClass.coe_one, Matrix.one_mulVec]
  have hsqrt := sqrtHalf_sq_mul_two
  have hid0 : β w = 0 → Function.update β w 0 = β := fun h ↦ by
    conv_rhs => rw [← Function.update_eq_self w β, h]
  have hid1 : β w = 1 → Function.update β w 1 = β := fun h ↦ by
    conv_rhs => rw [← Function.update_eq_self w β, h]
  rcases bit_cases (β w) with hw | hw
  · have hu := hid0 hw
    ext idx
    simp only [hw, bitSign, one_ne_zero, ↓reduceIte, hu, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket β idx) * hsqrt
  · have hu := hid1 hw
    ext idx
    simp only [hw, bitSign, one_ne_zero, ↓reduceIte, hu, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket β idx) * hsqrt
/-- Single-qubit Hadamards commute on all wire pairs (`w₁ = w₂` or `w₁ ≠ w₂`). -/
theorem eval_H_comm {N : ℕ} (w₁ w₂ : Wire N) : (Circuit.H w₁).eval * (Circuit.H w₂).eval =
    (Circuit.H w₂).eval * (Circuit.H w₁).eval := by
  by_cases h12 : w₁ = w₂
  · subst h12; rfl
  · have h21 : w₂ ≠ w₁ := Ne.symm h12
    apply Subtype.ext; apply matrix_ext_ket; intro β
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_H,
      Matrix.mulVec_add, Matrix.mulVec_smul,
      Function.update_of_ne h12, Function.update_of_ne h21, Function.update_comm h12]
    ext idx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
theorem basisBitsEquiv_symm_basisBits {N : ℕ} (g : Fin (2 ^ N)) : (basisBitsEquiv N).symm
    (basisBits N g) = g := (basisBitsEquiv N).symm_apply_apply g
/-- Single-qubit Hadamard on `w` commutes with `Circuit.CNOT a b hne` whenever `w ≠ a` and `w ≠
  b`. -/
theorem eval_H_comm_CNOT {N : ℕ} {w a b : Wire N} (hne : a ≠ b) (hwa : w ≠ a) (hwb : w ≠ b) :
    (Circuit.H w).eval * (Circuit.CNOT a b hne).eval = (Circuit.CNOT a b hne).eval *
    (Circuit.H w).eval := by
  have haw : a ≠ w := Ne.symm hwa
  have hbw : b ≠ w := Ne.symm hwb
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only[Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_H, ket_CNOT, Matrix.mulVec_add,
      Matrix.mulVec_smul, Function.update_of_ne hbw, Function.update_of_ne haw,
      Function.update_of_ne hwb, Function.update_comm hbw]
/-- Conjugating `Circuit.CNOT a b hne` by `Circuit.H a` and `Circuit.H b` reverses the CNOT
to `Circuit.CNOT b a hne.symm` directly on `Fin N`. -/
theorem eval_H_ab_conj_CNOT {N : ℕ} {a b : Wire N} (hne : a ≠ b) : (Circuit.H a).eval *
    ((Circuit.H b).eval * ((Circuit.CNOT a b hne).eval * ((Circuit.H b).eval * (Circuit.H
    a).eval))) = (Circuit.CNOT b a hne.symm).eval := by
  have hba : b ≠ a := hne.symm
  have hsqrt := sqrtHalf_sq_mul_two
  apply Subtype.ext; apply matrix_ext_ket; intro β
  have h_upd_b (va : ZMod 2) : Function.update (Function.update β a va) b (β b) =
    Function.update β a va := by
    funext u
    by_cases hub : u = b
    · subst hub; rw [Function.update_self, Function.update_of_ne hba]
    · rw [Function.update_of_ne hub]
  have h_ida : Function.update β a (β a) = β := Function.update_eq_self _ _
  have h_idb : Function.update β b (β b) = β := Function.update_eq_self _ _
  simp only[Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_H, ket_CNOT, Matrix.mulVec_add,
      Matrix.mulVec_smul, Function.update_self, Function.update_of_ne hne,
      Function.update_of_ne hba, Function.update_idem, Function.update_comm hba]
  rcases bit_cases (β a) with ha | ha <;> rcases bit_cases (β b) with hb | hb
  · ext idx
    have hub : ∀ va, Function.update (Function.update β a va) b 0 = Function.update β a va := by
      intro va; rw [← hb]; exact h_upd_b va
    have hua : Function.update β a 0 = β := by rw [← ha]; exact h_ida
    have hub0 : Function.update β b 0 = β := by rw [← hb]; exact h_idb
    simp only [ha, hb, bitSign, one_ne_zero, ↓reduceIte, add_zero, zero_add,
      CharTwo.add_self_eq_zero, hub, hua, hub0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket β idx) * ((2 * sqrtHalf * sqrtHalf + 1) * hsqrt)
  · ext idx
    have hub : ∀ va, Function.update (Function.update β a va) b 1 = Function.update β a va := by
      intro va; rw [← hb]; exact h_upd_b va
    have hua : Function.update β a 0 = β := by rw [← ha]; exact h_ida
    have hub1 : Function.update β b 1 = β := by rw [← hb]; exact h_idb
    simp only [ha, hb, bitSign, one_ne_zero, ↓reduceIte, add_zero, zero_add,
      CharTwo.add_self_eq_zero, hub, hua, hub1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket (Function.update β a 1) idx) * ((2 * sqrtHalf * sqrtHalf + 1) * hsqrt)
  · ext idx
    have hub : ∀ va, Function.update (Function.update β a va) b 0 = Function.update β a va := by
      intro va; rw [← hb]; exact h_upd_b va
    have hua : Function.update β a 1 = β := by rw [← ha]; exact h_ida
    have hub0 : Function.update β b 0 = β := by rw [← hb]; exact h_idb
    simp only [ha, hb, bitSign, one_ne_zero, ↓reduceIte, add_zero, zero_add,
      CharTwo.add_self_eq_zero, hub, hua, hub0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket β idx) * ((2 * sqrtHalf * sqrtHalf + 1) * hsqrt)
  · ext idx
    have hub : ∀ va, Function.update (Function.update β a va) b 1 = Function.update β a va := by
      intro va; rw [← hb]; exact h_upd_b va
    have hua : Function.update β a 1 = β := by rw [← ha]; exact h_ida
    have hub1 : Function.update β b 1 = β := by rw [← hb]; exact h_idb
    simp only [ha, hb, bitSign, one_ne_zero, ↓reduceIte, add_zero, zero_add,
      CharTwo.add_self_eq_zero, hub, hua, hub1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket (Function.update β a 0) idx) * ((2 * sqrtHalf * sqrtHalf + 1) * hsqrt)
/-- Prefix Hadamard unitary applying `Circuit.H` on `selHad ⟨0, _⟩, ..., selHad ⟨m - 1, _⟩`. -/
noncomputable def uHadPref {kHad N : ℕ} (selHad : QRegister kHad N) (m : ℕ) (hm : m ≤ kHad) :
    Unitary (2 ^ N) := ((cHadamardPrefix m hm).onRegister selHad).eval
theorem uHadPref_zero {kHad N : ℕ} (selHad : QRegister kHad N) (hm : 0 ≤ kHad) : uHadPref
    selHad 0 hm = 1 := rfl
open Classical in
theorem uHadPref_succ {kHad N : ℕ} (selHad : QRegister kHad N) (m : ℕ) (hm : m + 1 ≤ kHad) :
    uHadPref selHad (m + 1) hm =
      (Circuit.H (selHad ⟨m, hm⟩)).eval * uHadPref selHad m (Nat.le_of_succ_le hm) := by
  rw [uHadPref, uHadPref, Circuit.eval_onRegister, Circuit.eval_onRegister,
      cHadamardPrefix, Circuit.eval_seq, QRegister.embedUnitary_mul]
  refine congrArg₂ (· * ·) ?_ rfl
  change selHad.embedUnitary ((QRegister.singleton ⟨m, hm⟩).embedUnitary PrimitiveGate.H.eval) =
    (QRegister.singleton (selHad ⟨m, hm⟩)).embedUnitary PrimitiveGate.H.eval
  rw [← QRegister.embedUnitary_compose]
  exact congrArg (fun r ↦ r.embedUnitary PrimitiveGate.H.eval)
    (QRegister.ext (Function.Embedding.ext fun _ ↦ rfl))
open Classical in
theorem uHadPref_top_eq {kHad N : ℕ} (selHad : QRegister kHad N) : uHadPref selHad kHad le_rfl
    = selHad.embedUnitary (uHadamardAll kHad) := eval_cHadamardAll selHad
theorem uHadPref_comm_H {kHad N : ℕ} (selHad : QRegister kHad N) (w : Wire N) :
    ∀ (m : ℕ) (hm : m ≤ kHad),
      (Circuit.H w).eval * uHadPref selHad m hm = uHadPref selHad m hm * (Circuit.H w).eval
  | 0, hm => by rw [uHadPref_zero, mul_one, one_mul]
  | m + 1, hm => by
      rw [uHadPref_succ, ← mul_assoc, eval_H_comm w (selHad ⟨m, hm⟩),
          mul_assoc, uHadPref_comm_H selHad w m (Nat.le_of_succ_le hm), ← mul_assoc]
open Classical in
theorem uHadPref_mul_self {kHad N : ℕ} (selHad : QRegister kHad N) :
    ∀ (m : ℕ) (hm : m ≤ kHad), uHadPref selHad m hm * uHadPref selHad m hm = 1
  | 0, hm => by rw [uHadPref_zero, mul_one]
  | m + 1, hm => by
      let hm' := Nat.le_of_succ_le hm
      rw [uHadPref_succ, mul_assoc, ← mul_assoc (uHadPref selHad m hm'),
          ← uHadPref_comm_H selHad (selHad ⟨m, hm⟩) m hm',
          mul_assoc (Circuit.H (selHad ⟨m, hm⟩)).eval,
          uHadPref_mul_self selHad m hm', mul_one, eval_H_mul_self]
open Classical in
/-- Conditional single-wire Hadamard conjugation helper `if p then H w · U · H w else U`. -/
noncomputable def conjHIf {N : ℕ} (p : Prop) [Decidable p] (w : Wire N) (U : Unitary (2 ^ N))
    : Unitary (2 ^ N) := if p then (Circuit.H w).eval * (U * (Circuit.H w).eval) else U
open Classical in
theorem conjHIf_comm_H {N : ℕ} (p : Prop) [Decidable p] (w u : Wire N) (U : Unitary (2 ^ N))
    (hcomm : (Circuit.H u).eval * U = U * (Circuit.H u).eval) : (Circuit.H u).eval * conjHIf p
    w U = conjHIf p w U * (Circuit.H u).eval := by
  dsimp only [conjHIf]
  split_ifs with hp
  · calc
      (Circuit.H u).eval * ((Circuit.H w).eval * (U * (Circuit.H w).eval))
        = ((Circuit.H u).eval * (Circuit.H w).eval) * U * (Circuit.H w).eval := by
          simp only [mul_assoc]
      _ = (Circuit.H w).eval * ((Circuit.H u).eval * U) * (Circuit.H w).eval := by
            rw [eval_H_comm u w]; simp only [mul_assoc]
      _ = (Circuit.H w).eval * (U * ((Circuit.H u).eval * (Circuit.H w).eval)) := by
            rw [hcomm]; simp only [mul_assoc]
      _ = ((Circuit.H w).eval * (U * (Circuit.H w).eval)) * (Circuit.H u).eval := by
            rw [eval_H_comm u w]; simp only [mul_assoc]
  · exact hcomm
theorem conjHIf_conj_by_other_H {N : ℕ} (p : Prop) [Decidable p] (w u : Wire N)
    (U : Unitary (2 ^ N)) (hcomm : (Circuit.H u).eval * U = U * (Circuit.H u).eval) :
    (Circuit.H u).eval * (conjHIf p w U * (Circuit.H u).eval) = conjHIf p w U := by
  rw [← mul_assoc, conjHIf_comm_H p w u U hcomm, mul_assoc, eval_H_mul_self, mul_one]
open Classical in
/-- Exact prefix invariant for conjugating `Circuit.CNOT a b hne` by `uHadPref selHad m hm`
when `a = selHad ia` and `b = selHad ib`. -/
theorem uHadPref_conj_CNOT_aux {kHad N : ℕ} (selHad : QRegister kHad N)
    {ia ib : Fin kHad} (hne : selHad ia ≠ selHad ib) :
    ∀ (m : ℕ) (hm : m ≤ kHad),
      uHadPref selHad m hm * ((Circuit.CNOT (selHad ia) (selHad ib) hne).eval *
        uHadPref selHad m hm) =
        conjHIf (ia.val < m) (selHad ia)
          (conjHIf (ib.val < m) (selHad ib) (Circuit.CNOT (selHad ia) (selHad ib) hne).eval)
  | 0, hm => by
      rw [uHadPref_zero, one_mul, mul_one]
      dsimp [conjHIf]
  | m + 1, hm => by
      let hm' := Nat.le_of_succ_le hm
      let a := selHad ia
      let b := selHad ib
      let U₀ := (Circuit.CNOT a b hne).eval
      have ih := uHadPref_conj_CNOT_aux selHad hne m hm'
      have hStep : uHadPref selHad (m + 1) hm * (U₀ * uHadPref selHad (m + 1) hm) =
          (Circuit.H (selHad ⟨m, hm⟩)).eval * ((uHadPref selHad m hm' * (U₀ * uHadPref selHad
          m hm')) * (Circuit.H (selHad ⟨m, hm⟩)).eval) := by
        calc
          uHadPref selHad (m + 1) hm * (U₀ * uHadPref selHad (m + 1) hm)
            = ((Circuit.H (selHad ⟨m, hm⟩)).eval * uHadPref selHad m hm') *
                (U₀ * (uHadPref selHad m hm' * (Circuit.H (selHad ⟨m, hm⟩)).eval)) := by
                rw [uHadPref_succ, uHadPref_comm_H selHad (selHad ⟨m, hm⟩) m hm']
          _ = (Circuit.H (selHad ⟨m, hm⟩)).eval *
                ((uHadPref selHad m hm' * (U₀ * uHadPref selHad m hm')) *
                  (Circuit.H (selHad ⟨m, hm⟩)).eval) := by
                simp only [mul_assoc]
      rw [hStep, ih]
      by_cases hma : m = ia.val
      · have hm_eq_ia : (⟨m, hm⟩ : Fin kHad) = ia := Fin.ext hma
        have hia_not : ¬ ia.val < m := by omega
        have hia_lt : ia.val < m + 1 := by omega
        have hib_iff : (ib.val < m) ↔ (ib.val < m + 1) := by
          have hne_val : ia.val ≠ ib.val := fun hv ↦ hne (congrArg selHad (Fin.ext hv))
          omega
        rw [hm_eq_ia]
        dsimp only [conjHIf]
        rw [ite_eq_right hia_not, ite_eq_left hia_lt]
        by_cases hib : ib.val < m
        · rw [ite_eq_left hib, ite_eq_left (hib_iff.mp hib)]
        · rw [ite_eq_right hib, ite_eq_right (fun h ↦ hib (hib_iff.mpr h))]
      · by_cases hmb : m = ib.val
        · have hm_eq_ib : (⟨m, hm⟩ : Fin kHad) = ib := Fin.ext hmb
          have hib_not : ¬ ib.val < m := by omega
          have hib_lt : ib.val < m + 1 := by omega
          have hia_iff : (ia.val < m) ↔ (ia.val < m + 1) := by omega
          rw [hm_eq_ib]
          by_cases hia : ia.val < m
          · dsimp only [conjHIf]
            rw [ite_eq_left hia, ite_eq_right hib_not, ite_eq_left (hia_iff.mp hia),
              ite_eq_left hib_lt]
            calc
              (Circuit.H b).eval * (((Circuit.H a).eval * (U₀ * (Circuit.H a).eval)) *
                (Circuit.H b).eval)
                = ((Circuit.H b).eval * (Circuit.H a).eval) * (U₀ * ((Circuit.H a).eval *
                  (Circuit.H b).eval)) := by
                    simp only [mul_assoc]
              _ = ((Circuit.H a).eval * (Circuit.H b).eval) * (U₀ * ((Circuit.H b).eval *
                (Circuit.H a).eval)) := by
                    rw [eval_H_comm b a, eval_H_comm a b]
              _ = (Circuit.H a).eval * (((Circuit.H b).eval * (U₀ * (Circuit.H b).eval)) *
                (Circuit.H a).eval) := by
                    simp only [mul_assoc]
          · dsimp only [conjHIf]
            rw [ite_eq_right hia, ite_eq_right hib_not, ite_eq_right (fun h ↦ hia (hia_iff.mpr h)),
              ite_eq_left hib_lt]
        · have hwa : selHad ⟨m, hm⟩ ≠ a := fun h ↦ hma (congrArg Fin.val (selHad.wires.injective h))
          have hwb : selHad ⟨m, hm⟩ ≠ b := fun h ↦ hmb (congrArg Fin.val (selHad.wires.injective h))
          have hia_iff : (ia.val < m) ↔ (ia.val < m + 1) := by omega
          have hib_iff : (ib.val < m) ↔ (ib.val < m + 1) := by omega
          have hc0 : (Circuit.H (selHad ⟨m, hm⟩)).eval * U₀ = U₀ * (Circuit.H (selHad ⟨m,
            hm⟩)).eval :=
            eval_H_comm_CNOT hne hwa hwb
          have hc1 : (Circuit.H (selHad ⟨m, hm⟩)).eval * conjHIf (ib.val < m) b U₀ =
              conjHIf (ib.val < m) b U₀ * (Circuit.H (selHad ⟨m, hm⟩)).eval :=
            conjHIf_comm_H (ib.val < m) b (selHad ⟨m, hm⟩) U₀ hc0
          rw [conjHIf_conj_by_other_H (ia.val < m) a (selHad ⟨m, hm⟩) _ hc1]
          dsimp only [conjHIf]
          by_cases hia : ia.val < m <;> by_cases hib : ib.val < m
          · rw [ite_eq_left hia, ite_eq_left hib, ite_eq_left (hia_iff.mp hia),
              ite_eq_left (hib_iff.mp hib)]
          · rw [ite_eq_left hia, ite_eq_right hib, ite_eq_left (hia_iff.mp hia),
              ite_eq_right (fun h ↦ hib (hib_iff.mpr h))]
          · rw [ite_eq_right hia, ite_eq_left hib, ite_eq_right (fun h ↦
              hia (hia_iff.mpr h)), ite_eq_left (hib_iff.mp hib)]
          · rw [ite_eq_right hia, ite_eq_right hib, ite_eq_right (fun h ↦
              hia (hia_iff.mpr h)), ite_eq_right (fun h ↦ hib (hib_iff.mpr h))]
open Classical in
/-- Conjugating `Circuit.CNOT a b hne` by `selHad.embedUnitary (uHadamardAll kHad)` yields
`Circuit.CNOT b a hne.symm` whenever both `a` and `b` lie in `Set.range selHad.wires`. -/
theorem uHadAll_conj_CNOT {kHad N : ℕ} (selHad : QRegister kHad N)
    {a b : Wire N} (hne : a ≠ b)
    (ha : a ∈ Set.range selHad.wires) (hb : b ∈ Set.range selHad.wires) :
    let H_all := selHad.embedUnitary (uHadamardAll kHad)
    (H_all * (Circuit.CNOT a b hne).eval) * H_all = (Circuit.CNOT b a hne.symm).eval := by
  obtain ⟨ia, rfl⟩ := ha
  obtain ⟨ib, rfl⟩ := hb
  intro H_all
  have hTop : H_all = uHadPref selHad kHad le_rfl := (uHadPref_top_eq selHad).symm
  rw [hTop, mul_assoc]
  rw [uHadPref_conj_CNOT_aux selHad hne kHad le_rfl]
  dsimp only [conjHIf]
  rw [ite_eq_left ia.isLt, ite_eq_left ib.isLt]
  simpa only [mul_assoc] using eval_H_ab_conj_CNOT hne
/-- Direct `Fin N` `m`-wire pairwise CNOT circuit from `rSrc` into `rDst` (`0 T`, `0 TOFF`). -/
def cPairCnotPref {N : ℕ} (rSrc rDst : QRegister 18 N) (hSD : rSrc.DisjointWires rDst) :
    (m : ℕ) → (hm : m ≤ 18) → Circuit N
  | 0, _ => .identity
  | m + 1, hm =>
      cPairCnotPref rSrc rDst hSD m (Nat.le_of_succ_le hm) ;;ᶜ
      Circuit.CNOT (rSrc ⟨m, hm⟩) (rDst ⟨m, hm⟩) (hSD.ne ⟨m, hm⟩ ⟨m, hm⟩)
open Classical in
/-- Conjugating `cPairCnotPref rSrc rDst hSD m hm` by `selHad.embedUnitary (uHadamardAll kHad)`
reverses every CNOT to `cPairCnotPref rDst rSrc hSD.symm m hm` whenever `rSrc` and `rDst`
lie inside `Set.range selHad.wires`. -/
theorem uHadAll_conj_cPairCnotPref {kHad N : ℕ} (selHad : QRegister kHad N)
    (rSrc rDst : QRegister 18 N) (hSD : rSrc.DisjointWires rDst)
    (hSrc : ∀ j : Fin 18, rSrc j ∈ Set.range selHad.wires)
    (hDst : ∀ j : Fin 18, rDst j ∈ Set.range selHad.wires) :
    ∀ (m : ℕ) (hm : m ≤ 18),
      (selHad.embedUnitary (uHadamardAll kHad) * (cPairCnotPref rSrc rDst hSD m hm).eval) *
        selHad.embedUnitary (uHadamardAll kHad) =
        (cPairCnotPref rDst rSrc (QRegExt.disjointWires_symm hSD) m hm).eval
  | 0, _ => by
      dsimp only [cPairCnotPref]
      rw [Circuit.eval_identity, mul_one, ← uHadPref_top_eq, uHadPref_mul_self]
  | m + 1, hm => by
      let H_all := selHad.embedUnitary (uHadamardAll kHad)
      let hne := hSD.ne ⟨m, hm⟩ ⟨m, hm⟩
      let U₁ := (Circuit.CNOT (rSrc ⟨m, hm⟩) (rDst ⟨m, hm⟩) hne).eval
      let U₂ := (cPairCnotPref rSrc rDst hSD m (Nat.le_of_succ_le hm)).eval
      have hH2 : H_all * H_all = 1 := by
        dsimp only [H_all]; rw [← uHadPref_top_eq, uHadPref_mul_self]
      dsimp only [cPairCnotPref]
      rw [Circuit.eval_seq]
      calc
        (H_all * (U₁ * U₂)) * H_all
          = H_all * U₁ * 1 * U₂ * H_all := by simp only [mul_one, mul_assoc]
        _ = H_all * U₁ * (H_all * H_all) * U₂ * H_all := by rw [hH2]
        _ = ((H_all * U₁) * H_all) * ((H_all * U₂) * H_all) := by simp only [mul_assoc]
        _ = (Circuit.CNOT (rDst ⟨m, hm⟩) (rSrc ⟨m, hm⟩) hne.symm).eval *
              (cPairCnotPref rDst rSrc (QRegExt.disjointWires_symm hSD) m (Nat.le_of_succ_le
                hm)).eval := by
              dsimp only [U₁, U₂, H_all]
              rw [uHadAll_conj_CNOT selHad hne (hSrc ⟨m, hm⟩) (hDst ⟨m, hm⟩),
                  uHadAll_conj_cPairCnotPref selHad rSrc rDst hSD hSrc hDst m (Nat.le_of_succ_le
                    hm)]
        _ = (cPairCnotPref rDst rSrc (QRegExt.disjointWires_symm hSD) m (Nat.le_of_succ_le hm) ;;ᶜ
              Circuit.CNOT (rDst ⟨m, hm⟩) (rSrc ⟨m, hm⟩) ((QRegExt.disjointWires_symm hSD).ne ⟨m,
                hm⟩ ⟨m, hm⟩)).eval :=
              (Circuit.eval_seq _ _).symm
open Classical in
/-- Prefix bit-assignment update for `cPairCnotPref rSrc rDst hSD m hm`. -/
noncomputable def pairXorBitsPref {N : ℕ} (rSrc rDst : QRegister 18 N) (m : ℕ) (_hm : m ≤ 18)
    (β : BitAssignment N) : BitAssignment N := fun w ↦ if hw : ∃ j : Fin 18, j.val < m ∧ rDst
    j = w then β w + β (rSrc hw.choose) else β w
open Classical in
theorem cPairCnotPref_eval_ket {N : ℕ} (rSrc rDst : QRegister 18 N) (hSD : rSrc.DisjointWires rDst)
    :
    ∀ (m : ℕ) (hm : m ≤ 18) (β : BitAssignment N),
      (cPairCnotPref rSrc rDst hSD m hm).eval.1.mulVec (ket β) =
        ket (pairXorBitsPref rSrc rDst m hm β)
  | 0, hm, β => by
      have hid : pairXorBitsPref rSrc rDst 0 hm β = β := by
        funext w; simp [pairXorBitsPref]
      rw [hid]; simp [cPairCnotPref]
  | m + 1, hm, β => by
      let hm' := Nat.le_of_succ_le hm
      let jm : Fin 18 := ⟨m, hm⟩
      dsimp only [cPairCnotPref]
      rw [eval_seq_mulVec, cPairCnotPref_eval_ket rSrc rDst hSD m hm' β, ket_CNOT]
      congr 1; funext w
      by_cases hwd : w = rDst jm
      · subst hwd
        rw [Function.update_self]
        have hnot_d : ¬ ∃ j : Fin 18, j.val < m ∧ rDst j = rDst jm := by
          rintro ⟨j, hj, heq⟩
          have := congrArg Fin.val (rDst.wires.injective heq)
          dsimp [jm] at this; omega
        have hnot_s : ¬ ∃ j : Fin 18, j.val < m ∧ rDst j = rSrc jm := by
          rintro ⟨j, _, heq⟩
          exact hSD.ne jm j heq.symm
        have hex : ∃ j : Fin 18, j.val < m + 1 ∧ rDst j = rDst jm := ⟨jm, by dsimp [jm]; omega, rfl⟩
        dsimp only [pairXorBitsPref]
        rw [dite_eq_right hnot_d, dite_eq_right hnot_s, dite_eq_left hex]
        have hch : hex.choose = jm := rDst.wires.injective hex.choose_spec.2
        rw [hch]
      · rw [Function.update_of_ne hwd]
        dsimp only [pairXorBitsPref]
        by_cases h1 : ∃ j : Fin 18, j.val < m ∧ rDst j = w
        · have h2 : ∃ j : Fin 18, j.val < m + 1 ∧ rDst j = w := by
            obtain ⟨j, hj, hr⟩ := h1; exact ⟨j, by omega, hr⟩
          rw [dite_eq_left h1, dite_eq_left h2]
          have hch : h1.choose = h2.choose :=
            rDst.wires.injective (h1.choose_spec.2.trans h2.choose_spec.2.symm)
          rw [hch]
        · have h2 : ¬ ∃ j : Fin 18, j.val < m + 1 ∧ rDst j = w := by
            rintro ⟨j, hj, hr⟩
            by_cases hjm : j.val = m
            · exact hwd (hr.symm.trans (congrArg rDst (Fin.ext hjm)))
            · exact h1 ⟨j, by omega, hr⟩
          rw [dite_eq_right h1, dite_eq_right h2]
open Classical in
/-- `cPairCnotPref rSrc rDst hSD 18 le_rfl` acts on computational basis states identically to
  `cXor18`. -/
theorem cPairCnotPref_18_mulVec_single {N : ℕ}
    (rSrc rDst : QRegister 18 N) (hSD : rSrc.DisjointWires rDst) (g : Fin (2 ^ N)) :
    (cPairCnotPref rSrc rDst hSD 18 le_rfl).eval.1.mulVec (Pi.single g 1) =
      Pi.single (rDst.replaceIndex g (xor18 (rDst.extractIndex g) (rSrc.extractIndex g))) 1 := by
  let β := basisBits N g
  have hket : (Pi.single g (1 : ℂ) : Fin (2 ^ N) → ℂ) = ket β := by
    rw [PosPostPrep80MergedVep.ket_eq_single_local,
        basisBitsEquiv_symm_basisBits]
  rw [hket, cPairCnotPref_eval_ket,
      PosPostPrep80MergedVep.ket_eq_single_local]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ N) → ℂ))
    (eq_of_basisBits_eq fun w ↦ ?_)
  have hAt : basisBits N ((basisBitsEquiv N).symm (pairXorBitsPref rSrc rDst 18 le_rfl β)) w =
      pairXorBitsPref rSrc rDst 18 le_rfl β w :=
    congrFun ((basisBitsEquiv N).apply_symm_apply _) w
  rw [hAt]
  by_cases hw : w ∈ Set.range rDst.wires
  · obtain ⟨j, rfl⟩ := hw
    have hex : ∃ j' : Fin 18, j'.val < 18 ∧ rDst j' = rDst j := ⟨j, j.isLt, rfl⟩
    dsimp only [pairXorBitsPref]
    rw [dite_eq_left hex]
    have hch : hex.choose = j := rDst.wires.injective hex.choose_spec.2
    rw [hch, QRegister.basisBits_replaceIndex_apply, basisBits_xor18,
        QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  · have hnot : ¬ ∃ j : Fin 18, j.val < 18 ∧ rDst j = w := fun ⟨j, _, hj⟩ ↦ hw ⟨j, hj⟩
    dsimp only [pairXorBitsPref]
    rw [dite_eq_right hnot, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
theorem sameOutside_refl {N : ℕ} (S : Set (Wire N)) (g₀ : Fin (2 ^ N)) : SameOutside S g₀ g₀
    := fun _ _ ↦ rfl
theorem eval_H_preserves_sameOutside_support {N : ℕ} {S : Set (Wire N)} {g₀ : Fin (2 ^ N)}
    {w₀ : Wire N} (hw₀ : w₀ ∈ S) {ψ : Fin (2 ^ N) → ℂ}
    (hSupp : ∀ z, ψ z ≠ 0 → SameOutside S g₀ z) :
    ∀ z, ((Circuit.H w₀).eval.1.mulVec ψ) z ≠ 0 → SameOutside S g₀ z := by
  have hExpand : ψ = ∑ y : Fin (2 ^ N), ψ y • (Pi.single y (1 : ℂ) : Fin (2 ^ N) → ℂ) := by
    ext y; simp [Pi.single_apply]
  intro z hz
  rw [hExpand, Matrix.mulVec_sum] at hz
  simp only [Finset.sum_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at hz
  obtain ⟨y, _, hy_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hψy : ψ y ≠ 0 := left_ne_zero_of_mul hy_ne
  have hHy : ((Circuit.H w₀).eval.1.mulVec (Pi.single y 1)) z ≠ 0 := right_ne_zero_of_mul hy_ne
  have hSameY := hSupp y hψy
  have hket : (Pi.single y (1 : ℂ) : Fin (2 ^ N) → ℂ) = ket (basisBits N y) := by
    rw [PosPostPrep80MergedVep.ket_eq_single_local,
        basisBitsEquiv_symm_basisBits]
  rw [hket, ket_H] at hHy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hHy
  have hSumNe : ket (Function.update (basisBits N y) w₀ 0) z + bitSign (basisBits N y w₀) *
      ket (Function.update (basisBits N y) w₀ 1) z ≠ 0 := right_ne_zero_of_mul hHy
  intro w hwS
  have hww₀ : w ≠ w₀ := fun h ↦ hwS (h ▸ hw₀)
  by_cases hkz : ket (Function.update (basisBits N y) w₀ 0) z ≠ 0
  · rw [PosPostPrep80MergedVep.ket_eq_single_local] at hkz
    have hzeq : z = (basisBitsEquiv N).symm (Function.update (basisBits N y) w₀ 0) := by
      by_contra hne; exact hkz (Pi.single_eq_of_ne hne 1)
    rw [hzeq]
    have hAt : basisBits N ((basisBitsEquiv N).symm (Function.update (basisBits N y) w₀ 0)) w =
        Function.update (basisBits N y) w₀ 0 w :=
      congrFun ((basisBitsEquiv N).apply_symm_apply _) w
    rw [hAt, Function.update_of_ne hww₀]
    exact hSameY w hwS
  · have hkz0 : ket (Function.update (basisBits N y) w₀ 0) z = 0 := Classical.not_not.mp hkz
    rw [hkz0, zero_add] at hSumNe
    have hkz1 : ket (Function.update (basisBits N y) w₀ 1) z ≠ 0 := right_ne_zero_of_mul hSumNe
    rw [PosPostPrep80MergedVep.ket_eq_single_local] at hkz1
    have hzeq : z = (basisBitsEquiv N).symm (Function.update (basisBits N y) w₀ 1) := by
      by_contra hne; exact hkz1 (Pi.single_eq_of_ne hne 1)
    rw [hzeq]
    have hAt : basisBits N ((basisBitsEquiv N).symm (Function.update (basisBits N y) w₀ 1)) w =
        Function.update (basisBits N y) w₀ 1 w :=
      congrFun ((basisBitsEquiv N).apply_symm_apply _) w
    rw [hAt, Function.update_of_ne hww₀]
    exact hSameY w hwS
theorem uHadPref_preserves_sameOutside_single {kHad N : ℕ} (selHad : QRegister kHad N)
    (g₀ : Fin (2 ^ N)) :
    ∀ (m : ℕ) (hm : m ≤ kHad) (z : Fin (2 ^ N)),
      ((uHadPref selHad m hm).1.mulVec (Pi.single g₀ 1)) z ≠ 0 →
      SameOutside (Set.range selHad.wires) g₀ z
  | 0, hm, z, hz => by
      rw [uHadPref_zero, OneMemClass.coe_one, Matrix.one_mulVec] at hz
      have hzg : z = g₀ := by by_contra hne; exact hz (Pi.single_eq_of_ne hne 1)
      subst hzg; exact sameOutside_refl _ _
  | m + 1, hm, z, hz => by
      rw [uHadPref_succ, Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at hz
      exact eval_H_preserves_sameOutside_support (S := Set.range selHad.wires) ⟨⟨m, hm⟩, rfl⟩
        (uHadPref_preserves_sameOutside_single selHad g₀ m (Nat.le_of_succ_le hm)) z hz
open Classical in
/-- Matrix equality from equality on all standard basis vectors `Pi.single g₀ 1`. -/
theorem unitary_ext_mulVec_single {D : ℕ} {U V : Unitary D} (h : ∀ g₀ : Fin D, U.1.mulVec
    (Pi.single g₀ 1) = V.1.mulVec (Pi.single g₀ 1)) : U = V := by
  apply Subtype.ext; ext i j
  have hij := congrFun (h j) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hij
open Classical in
/-- **Master `0`-Hypothesis Indexed-Slot `hWriteEq` Theorem
  (`uWriteSub_uLensLoad_eq_uLensWrite_of_slotReg`, `0 sorry`)**:
For any `L : Slot18Lens kData` backed by an 18-wire slot selector `slotOf : Fin (2 ^ kData) →
QRegister 18 kData`
such that:
1. `L.tbl d = (slotOf d).extractIndex d` and `L.updSlot d v = (slotOf d).replaceIndex d v`,
2. All wires of `(selDataInAct kData).compose (slotOf d)` and `selMeasInAct kData` lie in `Set.range
selHad.wires`,
3. `slotOf ((selDataInAct kData).extractIndex z)` depends only on wires outside `Set.range
selHad.wires`,
conjugating `uLensLoad L` by `selHad.embedUnitary (uHadamardAll kHad)` equals `uLensWrite L`! -/
theorem uWriteSub_uLensLoad_eq_uLensWrite_of_slotReg {kData kHad : ℕ}
    (selHad : QRegister kHad (kData + 18)) (L : Slot18Lens kData)
    (slotOf : Fin (2 ^ kData) → QRegister 18 kData)
    (hTbl : ∀ d, L.tbl d = (slotOf d).extractIndex d)
    (hUpd : ∀ d v, L.updSlot d v = (slotOf d).replaceIndex d v) (hSlotInHad : ∀ (d : Fin (2 ^
    kData)) (j : Fin 18), selDataInAct kData (slotOf d j) ∈ Set.range selHad.wires)
    (hMeasInHad : ∀ j : Fin 18, selMeasInAct kData j ∈ Set.range selHad.wires) (hSlotOutside :
    ∀ (g₀ z : Fin (2 ^ (kData + 18))), SameOutside (Set.range selHad.wires) g₀ z → slotOf
    ((selDataInAct kData).extractIndex z) = slotOf ((selDataInAct kData).extractIndex g₀)) :
    uWriteSub selHad (uLensLoad L) = uLensWrite L := by
  let N := kData + 18
  let selD := selDataInAct kData
  let rMeas := selMeasInAct kData
  let H_all := selHad.embedUnitary (uHadamardAll kHad)
  refine unitary_ext_mulVec_single fun g₀ ↦ ?_
  let d₀ := selD.extractIndex g₀
  let rSlot₀ : QRegister 18 N := selD.compose (slotOf d₀)
  let hSM₀ : rSlot₀.DisjointWires rMeas :=
    (selDataInAct_disj_selMeasInAct kData).compose_left (slotOf d₀)
  let C_fwd := cPairCnotPref rSlot₀ rMeas hSM₀ 18 le_rfl
  let C_rev := cPairCnotPref rMeas rSlot₀ (QRegExt.disjointWires_symm hSM₀) 18 le_rfl
  have hRevEq : (H_all * C_fwd.eval) * H_all = C_rev.eval :=
    uHadAll_conj_cPairCnotPref selHad rSlot₀ rMeas hSM₀ (hSlotInHad d₀) hMeasInHad 18 le_rfl
  let ψ := H_all.1.mulVec (Pi.single g₀ 1)
  have hLoadAgreeOnSupp : ∀ z : Fin (2 ^ N), ψ z ≠ 0 →
      (uLensLoad L).1.mulVec (Pi.single z 1) = C_fwd.eval.1.mulVec (Pi.single z 1) := by
    intro z hz
    have hSame : SameOutside (Set.range selHad.wires) g₀ z := by
      dsimp only [ψ, H_all] at hz
      rw [← uHadPref_top_eq] at hz
      exact uHadPref_preserves_sameOutside_single selHad g₀ kHad le_rfl z hz
    have hSlotEq : slotOf (selD.extractIndex z) = slotOf d₀ := hSlotOutside g₀ z hSame
    have hLoadSingle : (uLensLoad L).1.mulVec (Pi.single z 1) = Pi.single (lensLoadEquiv L z) 1 :=
      by
      ext i
      have hCol : ((uLensLoad L).1.mulVec (Pi.single z 1)) i = (uLensLoad L).1 i z := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hCol]
      dsimp only [uLensLoad]
      rw [permUnitary_apply]
      by_cases hi : i = lensLoadEquiv L z
      · subst hi; simp
      · simp [hi]
    rw [hLoadSingle, cPairCnotPref_18_mulVec_single rSlot₀ rMeas hSM₀ z]
    refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ N) → ℂ)) ?_
    change liftPairIdx (lensLoadPerm L) z =
      rMeas.replaceIndex z (xor18 (rMeas.extractIndex z) (rSlot₀.extractIndex z))
    dsimp only [liftPairIdx, extractPair, lensLoadPerm]
    rw [QRegister.replaceIndex_extractIndex, hTbl (selD.extractIndex z), hSlotEq]
    dsimp only [rSlot₀]
    rw [← QRegister.extractIndex_compose]
  have hLoadOnΨ : (uLensLoad L).1.mulVec ψ = C_fwd.eval.1.mulVec ψ := by
    have hΨSum : ψ = ∑ z : Fin (2 ^ N), ψ z • (Pi.single z (1 : ℂ) : Fin (2 ^ N) → ℂ) := by
      ext z; simp [Pi.single_apply]
    conv_lhs => rw [hΨSum, Matrix.mulVec_sum]
    conv_rhs => rw [hΨSum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    by_cases hz : ψ z = 0
    · rw [hz, zero_smul, zero_smul]
    · rw [hLoadAgreeOnSupp z hz]
  have hLhs : (uWriteSub selHad (uLensLoad L)).1.mulVec (Pi.single g₀ 1) =
      C_rev.eval.1.mulVec (Pi.single g₀ 1) := by
    calc
      (uWriteSub selHad (uLensLoad L)).1.mulVec (Pi.single g₀ 1)
        = H_all.1.mulVec ((uLensLoad L).1.mulVec ψ) := by
            dsimp only [uWriteSub, ψ, H_all]
            simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      _ = H_all.1.mulVec (C_fwd.eval.1.mulVec ψ) := by rw [hLoadOnΨ]
      _ = ((H_all * C_fwd.eval) * H_all).1.mulVec (Pi.single g₀ 1) := by
            dsimp only [ψ]
            simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      _ = C_rev.eval.1.mulVec (Pi.single g₀ 1) := by rw [hRevEq]
  rw [hLhs, cPairCnotPref_18_mulVec_single rMeas rSlot₀ (QRegExt.disjointWires_symm hSM₀) g₀]
  have hWriteSingle : (uLensWrite L).1.mulVec (Pi.single g₀ 1) =
    Pi.single (lensWriteEquiv L g₀) 1 := by
    ext i
    have hCol : ((uLensWrite L).1.mulVec (Pi.single g₀ 1)) i = (uLensWrite L).1 i g₀ := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hCol]
    dsimp only [uLensWrite]
    rw [permUnitary_apply]
    by_cases hi : i = lensWriteEquiv L g₀
    · subst hi; simp
    · simp [hi]
  rw [hWriteSingle]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ N) → ℂ)) ?_
  change rSlot₀.replaceIndex g₀ (xor18 (rSlot₀.extractIndex g₀) (rMeas.extractIndex g₀)) =
    liftPairIdx (lensWritePerm L) g₀
  dsimp only [liftPairIdx, extractPair, lensWritePerm]
  rw [hUpd d₀, hTbl d₀]
  apply eq_of_basisBits_eq; intro w
  by_cases hwM : w ∈ Set.range rMeas.wires
  · obtain ⟨j, rfl⟩ := hwM
    have hnotS : rMeas j ∉ Set.range rSlot₀.wires := fun ⟨i, hi⟩ ↦ hSM₀.ne i j hi
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotS,
        QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem rMeas _ _ _ hwM]
    by_cases hwD : w ∈ Set.range selD.wires
    · obtain ⟨u, rfl⟩ := hwD
      rw [QRegister.basisBits_replaceIndex_apply]
      by_cases huS : u ∈ Set.range (slotOf d₀).wires
      · obtain ⟨j, rfl⟩ := huS
        have hcomp : selD (slotOf d₀ j) = rSlot₀ j := rfl
        rw [hcomp, QRegister.basisBits_replaceIndex_apply,
            QRegister.basisBits_replaceIndex_apply]
        have hex : (slotOf d₀).extractIndex d₀ = rSlot₀.extractIndex g₀ :=
          (QRegister.extractIndex_compose selD (slotOf d₀) g₀).symm
        rw [hex]
      · have hnotR : selD u ∉ Set.range rSlot₀.wires := fun ⟨j, hj⟩ ↦
          huS ⟨j, selD.wires.injective hj⟩
        rw [QRegister.basisBits_replaceIndex_of_not_mem rSlot₀ _ _ _ hnotR,
            QRegister.basisBits_replaceIndex_of_not_mem (slotOf d₀) _ _ _ huS,
            QRegister.basisBits_extractIndex]
    · have hnotR : w ∉ Set.range rSlot₀.wires := fun ⟨j, hj⟩ ↦ hwD ⟨slotOf d₀ j, hj⟩
      rw [QRegister.basisBits_replaceIndex_of_not_mem rSlot₀ _ _ _ hnotR,
          QRegister.basisBits_replaceIndex_of_not_mem selD _ _ _ hwD]
/-- All `3,924` electron wires `[0 .. 3924)` inside `posCoreWires`. -/
def rElecAllPos : QRegister 3924 posCoreWires :=
  (QRegExt.ofFin posCoreWires).slice 0 3924 (by have := h3924_le_posCoreWires; omega)
theorem rElecAllPos_val (i : Fin 3924) : (rElecAllPos i).val = i.val := by
  simp [rElecAllPos, QRegister.slice, QRegExt.ofFin]
/-- Canonical `(3924 + 18)`-wire Hadamard subregister inside `kData + 18` for any
`selCore : QRegister posCoreWires kData`, selecting `selCore`'s `3,924` electron wires and
`selMeasInAct kData`. -/
def selHadOfPosCore {kData : ℕ} (selCore : QRegister posCoreWires kData) : QRegister
    (3924 + 18) (kData + 18) :=
    ((selDataInAct kData).compose (selCore.compose rElecAllPos)).concat (selMeasInAct kData)
    ((selDataInAct_disj_selMeasInAct kData).compose_left (selCore.compose rElecAllPos))
theorem rDataElec_mem_selHadOfPosCore {kData : ℕ}
    (selCore : QRegister posCoreWires kData) (e : Fin 218) (j : Fin 18) :
    selDataInAct kData (rDataElec selCore e j) ∈ Set.range (selHadOfPosCore selCore).wires := by
  let idx : Fin 3924 := ⟨18 * e.val + j.val, by have := e.isLt; have := j.isLt; omega⟩
  refine ⟨Fin.castAdd 18 idx, ?_⟩
  dsimp only [selHadOfPosCore]
  rw [QRegister.concat_apply_left]
  change selDataInAct kData (selCore (rElecAllPos idx)) =
    selDataInAct kData (selCore (rElecSlot (QRegExt.ofFin posCoreWires) e j))
  refine congrArg (fun u ↦ selDataInAct kData (selCore u)) (Fin.ext ?_)
  rw [rElecAllPos_val, PartnerAndAnchorSlot18LensAndMidBA.rElecSlot_ofFin_val]
theorem selMeasInAct_mem_selHadOfPosCore {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (j : Fin 18) : selMeasInAct kData j ∈ Set.range (selHadOfPosCore selCore).wires :=
    ⟨Fin.natAdd 3924 j, QRegister.concat_apply_right _ _ _ j⟩
/-- `(coinBarrelIdxFast hmPay γ).val < 218` for all `γ` (both `c2 = 0` and `c2 = 1`). -/
theorem coinBarrelIdxFast_val_lt_218 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (coinBarrelIdxFast hmPay γ).val < 218 := by
  have hlt := (coinBarrelIdxFast hmPay γ).isLt
  have h218 : SpecsAux.SpecMirror.numElectrons = 218 := rfl
  omega
end BoothOpt_03_CoinBarrelIdxFastTrueSwap
end SharedScope
end SlimStageBOuterDepsB

noncomputable section SlimFermApproxSec3B
set_option exponentiation.threshold 8192
set_option maxRecDepth 262144
section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
attribute [-instance] littleWedderburn Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroK4 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open _root_.DynamicCircuit DynCircuitExt
open Circuit hiding TOFF
open Operator QProg Matrix Real
local instance (priority := 1000000) instGroupUnitaryFastAux (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFastAux (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open scoped Matrix BigOperators
namespace StageAConjHAndStreamBridge
open LocalClassicalPerm
open SpecsAux.PhaseGradCatalystCore (IntertwinesCat)
open OctahedralOrbit Dyadic128CoulombMath
open CanonRank7Circuit
open HoistedSwapSelectBridge (unitaryConj)
open KaratsubaQft64Matrix (omega128 omega128_zero omega128_add bitRev6)
open DyadicQft64WalkCircuit (u18GridEquiv)
open CoreQftHadamard140And160 (CanonStageSpec128)
open FullSysCatSegmentBridge (fullSysCoreWires coreElecCosetB1Block IntertwinesLocalCat
  disjointWires_concat_left)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (rTopCatSlice)
open SingleCatClosure (intertwinesCat_topCatSlice_of_localCat intertwinesCat_congr_ops
  singleCat_seven_le_of_48)
open PolymorphicTopClosure (intertwinesCat_mul_gen)
open PosSlots24BranchConcrete
open PosSlots24SemanticBridge (pos24_6_le_80)
open PosPostPrep80MergedVep (uSwapCore3967)
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open QRegExt
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open StageAPosHeadConjugatedCircuit (rSpectatorElec3906InCore uCoreHadamard18 rSpectatorSlot
  uHad217)
open TwistStreamEliminationAux (spectatorSum217)
open Slot0SubAdd14And217Stream (rSum14Slice42 uSlot0Sum42Add)
open StageAPointPhase128OnStep (activeOneElecForestFullQftStage128 pointCrossXorExp128
  pointSumCliffordExp128 pointElecCliffordExp128 rCoreInCoreSum42 rSum14InCoreSum42)
open FullConcrete7StepAndTrueSwapSelect (kCoreSum42PG7 selCoreSum42InAct selCatInCoreSum42PG7)
open DoubleDutyFoldedRealizesBridge (selPosCoreInCore80)
open BoothOpt_06_Stream217ZeroSave0Width128 (rSpec217OfCore disj_rSpec217OfCore_left
  selSpec217InCoreSum14 compose_selSpec217InCoreSum14 selCoreSum14In42 compose_selCoreSum14In42
  uStream217Spec131)
open ForestQft117BundleNoTopBridge (pStream217Core pointTargetOnlyExp128
  omega128_sum_217_pointAxisPhaseExp128_eq_of_rSum7)
attribute [local reducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
open DyadicQft64WalkCircuit (block6_extractIndex_u18 disjoint_block_sep)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open FullSysCatSegmentBridge (fullSysQftCoreUnitary)
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside)
open PosPostPrep80MergedVep (wCore3967 wCore4029)
open NuclearTwistRealizes (embedUnitary_idReg_eq)
open InterWalkRSum42Hoist (E_rawStream42)
open Barrel3PassSelectStitch (uTrailCliffordXor80)
open StageAPosHeadConjugatedCircuit (uHadamard18)
open OriginZeroHeadMod4Reduction (rElec0InCore embedUnitary_comm_of_disjoint_local)
open OriginZeroHeadMod4Circuit14900 (uQft0)
open StageAPointPhase128OnStep (pStream42Of)
open ZeroHyp5StepA3StepBMidEqAndUncondExt48
  (activeOneElecForestQftBundle128_uQft654_eq_rElec18In654_zero)
open ZeroHypStageABToUFoldedPass123SegAndCompac (rElec18InCore uHeadPhase80Mod4Eff rElec0InCoreSum42
  monomialZ8UnitaryN_comm_diagonal_of_invariant)
open ZeroHypLHSStageAB7Step3StepCatState48Proje (rIdInCoreSum42 concat_compose_selCatInCoreSum42PG7
  intertwinesLocalCat_canonStageSpec128_zeroHyp)
open TrailXorAndRepairedStageAExactEq (controlledPointDiag217Entry uControlledPointDiag217)
attribute [local reducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
open Leaf4Ext48TopStitch (disj_of_val_ne)
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
theorem qreg_block_wires_apply_assoc {n : ℕ} (offset width : ℕ) (h : offset + width ≤
    n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem emb_trans_apply_assoc {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
theorem posCoreWires_eq_4034_assoc : posCoreWires = 4034 := rfl
theorem fullSysCoreWires80_eq_4034_assoc : fullSysCoreWires 80 = 4034 := rfl
theorem kCoreSum42PG7_eq_4083_assoc : kCoreSum42PG7 = 4083 := rfl
theorem kHeldZ18Sys_eq_4094_assoc : kHeldZ18Sys = 4094 := rfl
theorem kHeldZ18Act_eq_4101_assoc : kHeldZ18Act = 4101 := rfl
theorem wSlot0Core_ofFin_val_assoc : (wSlot0Core (QRegExt.ofFin posCoreWires)).val = 3948 := rfl
theorem wSlot1Core_ofFin_val_assoc : (wSlot1Core (QRegExt.ofFin posCoreWires)).val = 3949 := rfl
theorem wSlot2Core_ofFin_val_assoc : (wSlot2Core (QRegExt.ofFin posCoreWires)).val = 3950 := rfl
theorem wIsHead_ofFin_val_assoc : (wIsHead (QRegExt.ofFin posCoreWires)).val = 3954 + 30 := rfl
theorem wHeadThresh_ofFin_val_assoc : (wHeadThresh (QRegExt.ofFin posCoreWires)).val = 3954 + 31 :=
  rfl
theorem wSubReject_ofFin_val_assoc : (wSubReject (QRegExt.ofFin posCoreWires)).val = 3954 + 62 :=
  rfl
theorem rCosetB0_ofFin_val_assoc (q : Fin 3) :
    (rCosetB0 (QRegExt.ofFin posCoreWires) q).val = 3954 + (3 + q.val) := rfl
theorem rNucIdx_ofFin_val_assoc (q : Fin 8) :
    (rNucIdx (QRegExt.ofFin posCoreWires) q).val = 3954 + (6 + q.val) := rfl
theorem rAnchorIdx_ofFin_val_assoc (q : Fin 8) :
    (rAnchorIdx (QRegExt.ofFin posCoreWires) q).val = 3954 + (14 + q.val) := rfl
theorem rHeadFine21_ofFin_val_assoc (q : Fin 21) :
    (rHeadFine21 (QRegExt.ofFin posCoreWires) q).val = 3954 + (32 + q.val) := rfl
theorem rElecSlot0_ofFin_val_assoc (q : Fin 18) :
    (rElecSlot (QRegExt.ofFin posCoreWires) 0 q).val = 18 * 0 + q.val := rfl
theorem wCore3967_val_assoc : PosPostPrep80MergedVep.wCore3967.val = 3967 := rfl
theorem wCore4029_val_assoc : PosPostPrep80MergedVep.wCore4029.val = 4029 := rfl
theorem iSlot0_80_val_assoc : (FullSysCatSegmentBridge.iSlot0 80).val = 3948 := rfl
theorem iSlot1_80_val_assoc : (FullSysCatSegmentBridge.iSlot1 80).val = 3949 := rfl
theorem iSlot2_80_val_assoc : (FullSysCatSegmentBridge.iSlot2 80).val = 3950 := rfl
theorem basisBits_extractIndex_assoc {k N : ℕ} (r : QRegister k N) (x : Fin (2 ^ N))
    (j : Fin k) : basisBits k (r.extractIndex x) j = basisBits N x (r j) :=
    r.basisBits_extractIndex x j
theorem op_mul_assoc_assoc {D : ℕ} (A B C : Operator D) : A * B * C = A * (B * C) :=
  Matrix.mul_assoc A B C
theorem op_one_mul_assoc {D : ℕ} (A : Operator D) : (1 : Operator D) * A = A :=
  Matrix.one_mul A
theorem op_mul_one_assoc {D : ℕ} (A : Operator D) : A * (1 : Operator D) = A :=
  Matrix.mul_one A
theorem op_mul_diagonal_assoc {D : ℕ} (A : Operator D) (d : Fin D → ℂ) (i j : Fin D) :
    (A * Matrix.diagonal d) i j = A i j * d j := Matrix.mul_diagonal d A i j
theorem op_diagonal_mul_assoc {D : ℕ} (d : Fin D → ℂ) (A : Operator D) (i j : Fin D) :
    (Matrix.diagonal d * A) i j = d i * A i j := Matrix.diagonal_mul d A i j
theorem unitary_coe_mul_assoc {D : ℕ} (a b : Unitary D) : (a * b).1 = a.1 * b.1 := rfl
theorem op_conjTranspose_mul_assoc {D : ℕ} (A B : Operator D) : (A * B)ᴴ = Bᴴ * Aᴴ :=
  Matrix.conjTranspose_mul A B
theorem unitary_inv_val_eq_conjTranspose_assoc {D : ℕ} (U : Unitary D) : (U⁻¹).1 = (U.1)ᴴ := by
  rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
theorem headTargetPoint18_congr_assoc {β₁ β₂ : BitAssignment posCoreWires}
    (h : headTargetCoord64 β₁ = headTargetCoord64 β₂) :
    headTargetPoint18 β₁ = headTargetPoint18 β₂ := by
  unfold headTargetPoint18; rw [h]
theorem op_diagonal_apply_ne_assoc {D : ℕ} (d : Fin D → ℂ) {i j : Fin D} (h : i ≠ j) :
    Matrix.diagonal d i j = 0 := Matrix.diagonal_apply_ne d h
theorem extractIndex_eq_of_basisBits_eq_assoc {m n : ℕ} (r : QRegister m n) {x y : Fin (2 ^ n)}
    (h : ∀ i : Fin m, basisBits n x (r i) = basisBits n y (r i)) : r.extractIndex x =
    r.extractIndex y :=
  (basisBitsEquiv m).injective (funext fun i ↦ by
    change basisBits m (r.extractIndex x) i = basisBits m (r.extractIndex y) i
    rw [basisBits_extractIndex_assoc, basisBits_extractIndex_assoc]
    exact h i)
theorem comm_mul_assoc {D : ℕ} {a b p : Operator D} (ha : a * p = p * a) (hb : b * p = p * b) :
    (a * b) * p = p * (a * b) := by
  rw [op_mul_assoc_assoc, hb, ← op_mul_assoc_assoc, ha, op_mul_assoc_assoc]
theorem comm_conj_prod5_assoc {D : ℕ} {x a b c d e p q : Operator D} (hx : x * x = 1)
    (hConj : x * p * x = q) (ha : a * q = q * a) (hb : b * q = q * b) (hc : c * q = q * c)
    (hd : d * q = q * d) (he : e * q = q * e) : (x * (a * (b * (c * (d * (e * x)))))) * p = p
    * (x * (a * (b * (c * (d * (e * x)))))) := by
  let m := a * (b * (c * (d * e)))
  have hm : m * q = q * m :=
    comm_mul_assoc ha (comm_mul_assoc hb (comm_mul_assoc hc (comm_mul_assoc hd he)))
  have hAssoc : x * (a * (b * (c * (d * (e * x))))) = x * m * x := by
    dsimp only [m]
    simp only [op_mul_assoc_assoc]
  rw [hAssoc]
  calc (x * m * x) * p = ((x * m * x) * p) * (x * x) := by rw [hx, op_mul_one_assoc]
    _ = x * (m * (x * p * x)) * x := by simp only [op_mul_assoc_assoc]
    _ = x * ((x * p * x) * m) * x := by rw [hConj, hm]
    _ = (x * x) * p * (x * m * x) := by simp only [op_mul_assoc_assoc]
    _ = p * (x * m * x) := by rw [hx, op_one_mul_assoc]
open Classical in
theorem embedMatrix_basisOutcomeProjector_zero_assoc {a b c : ℕ}
    (r : QRegister b c) (s : QRegister a b) :
    r.embedMatrix (s.basisOutcomeProjector 0) = (r.compose s).basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    QRegister.embedMatrix_diagonal]
  refine congrArg Matrix.diagonal (funext fun x ↦ congrArg (fun z ↦
    if z = 0 then (1 : ℂ) else 0) ?_)
  apply (basisBitsEquiv a).injective; funext m
  change basisBits a _ m = basisBits a _ m
  rw [basisBits_extractIndex_assoc, basisBits_extractIndex_assoc,
    basisBits_extractIndex_assoc]; rfl
theorem selCoreSum14_compose_selSpec217_val_assoc (w : Fin 3) : (∀ iSpec : Fin 3906,
    (selCoreSum14In42 80 w (selSpec217InCoreSum14 80 (Fin.castAdd 14 iSpec))).val = 18 +
    iSpec.val) ∧ (∀ jSum : Fin 14, (selCoreSum14In42 80 w (selSpec217InCoreSum14 80
    (Fin.natAdd 3906 jSum))).val = fullSysCoreWires 80 + (14 * w.val + jSum.val)) := by
  let rC := rActLoc (fullSysCoreWires 80) 42
  let rS := rZLoc (fullSysCoreWires 80) 42
  have hCS : rC.DisjointWires rS := rActLoc_disj_rZLoc (fullSysCoreWires 80) 42
  have hId (q : Fin (fullSysCoreWires 80 + 42)) : rC.concat rS hCS q = q := by
    rw [rActLoc_concat_rZLoc_eq_idReg]
    rfl
  have hComp : ∀ idx : Fin (3906 + 14), selCoreSum14In42 80 w (selSpec217InCoreSum14 80 idx) =
      ((rSpec217OfCore rC).concat (rS.compose
      (BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42 w)) (disj_rSpec217OfCore_left
      (hCS.compose_right (BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42 w)))) idx :=
      fun idx ↦ by
    rw [← hId (selCoreSum14In42 80 w (selSpec217InCoreSum14 80 idx))]
    change (((rC.concat rS hCS).compose (selCoreSum14In42 80 w)).compose
      (selSpec217InCoreSum14 80)) idx = _
    rw [compose_selCoreSum14In42, compose_selSpec217InCoreSum14]
  refine ⟨fun iSpec ↦ ?_, fun jSum ↦ ?_⟩
  · rw [hComp, QRegister.concat_apply_left]
    simp [rSpec217OfCore, rC, rActLoc, QRegister.slice]
  · rw [hComp, QRegister.concat_apply_right]
    simp [rS, rZLoc, BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42]
/-- `posCoreWires` prefix `[0 .. 4034)` inside `kCoreSum42PG7 + 18`. -/
def selPosCoreInFull : QRegister posCoreWires (kCoreSum42PG7 + 18) :=
  QRegister.block 0 posCoreWires (by
    rw [posCoreWires_eq_4034_assoc, kCoreSum42PG7_eq_4083_assoc]; omega)
/-- `fullSysCoreWires 80 + 42` prefix `[0 .. 4076)` inside `kCoreSum42PG7 + 18`. -/
def selCoreSum42InFull : QRegister (fullSysCoreWires 80 + 42) (kCoreSum42PG7 + 18) :=
  QRegister.block 0 (fullSysCoreWires 80 + 42) (by
    rw [fullSysCoreWires80_eq_4034_assoc, kCoreSum42PG7_eq_4083_assoc]; omega)
theorem hDisjPosCoreZ18Full_assoc : selPosCoreInFull.DisjointWires (rZLoc kCoreSum42PG7 18) :=
  disjoint_block_sep (by rw [posCoreWires_eq_4034_assoc, kCoreSum42PG7_eq_4083_assoc]; omega)
theorem hDisjPosCoreZ18Sys_assoc :
    selCoreInHeldZ18Sys.DisjointWires (rZLoc (fullSysCoreWires 80 + 42) 18) :=
  disjoint_block_sep (by rw [posCoreWires_eq_4034_assoc, fullSysCoreWires80_eq_4034_assoc]; omega)
/-- `(posCoreWires + 18)` selector `rPosCore ++ rZ18` inside `kCoreSum42PG7 + 18`. -/
def selPosCoreZ18InFull : QRegister (posCoreWires + 18) (kCoreSum42PG7 + 18) :=
  selPosCoreInFull.concat (rZLoc kCoreSum42PG7 18) hDisjPosCoreZ18Full_assoc
/-- `(posCoreWires + 18)` selector `rPosCore ++ rZ18` inside `kHeldZ18Sys`. -/
def selPosCoreZ18InSys : QRegister (posCoreWires + 18) kHeldZ18Sys :=
  selCoreInHeldZ18Sys.concat (rZLoc (fullSysCoreWires 80 + 42) 18) hDisjPosCoreZ18Sys_assoc
/-- Permutation selector `Fin kHeldZ18Act → Fin (kCoreSum42PG7 + 18)` swapping the trailing
`(rPG7, rZ18)` blocks so `((rCS ++ rPG7) ++ rZ18).compose selHeldZ18ActInFull = (rCS ++ rZ18) ++
rPG7`. -/
def selHeldZ18ActInFull : QRegister kHeldZ18Act (kCoreSum42PG7 + 18) where
  wires := ⟨fun idx ↦
    if h1 : idx.val < fullSysCoreWires 80 + 42 then
      ⟨idx.val, by
        simp only [kCoreSum42PG7_eq_4083_assoc, fullSysCoreWires80_eq_4034_assoc] at h1 ⊢; omega⟩
    else if h2 : idx.val < kHeldZ18Sys then
      ⟨kCoreSum42PG7 + (idx.val - (fullSysCoreWires 80 + 42)), by
        simp only [kHeldZ18Sys_eq_4094_assoc, kCoreSum42PG7_eq_4083_assoc,
          fullSysCoreWires80_eq_4034_assoc] at h1 h2 ⊢; omega⟩
    else
      ⟨(fullSysCoreWires 80 + 42) + (idx.val - kHeldZ18Sys), by
        have := idx.isLt
        simp only [kHeldZ18Act_eq_4101_assoc, kHeldZ18Sys_eq_4094_assoc,
          kCoreSum42PG7_eq_4083_assoc, fullSysCoreWires80_eq_4034_assoc] at this h2 ⊢; omega⟩,
    fun a b hab ↦ by
      have hv := congrArg Fin.val hab
      have ha := a.isLt; have hb := b.isLt
      dsimp only [] at hv
      split_ifs at hv <;> dsimp only [] at hv <;>
        simp only [kHeldZ18Act_eq_4101_assoc, kHeldZ18Sys_eq_4094_assoc,
          kCoreSum42PG7_eq_4083_assoc, fullSysCoreWires80_eq_4034_assoc] at * <;>
        exact Fin.ext (by omega)⟩
open Classical in
theorem selHeldZ18ActInFull_val_assoc (idx : Fin kHeldZ18Act) : (selHeldZ18ActInFull idx).val =
    if idx.val < fullSysCoreWires 80 + 42 then idx.val else if idx.val < kHeldZ18Sys then
    kCoreSum42PG7 + (idx.val - (fullSysCoreWires 80 + 42)) else (fullSysCoreWires 80 + 42) +
    (idx.val - kHeldZ18Sys) := by
  simp only [selHeldZ18ActInFull, Function.Embedding.coeFn_mk]
  split_ifs <;> rfl
/-- System selector `Fin kHeldZ18Sys → Fin (kCoreSum42PG7 + 18)` (`rCS ++ rZ18`). -/
def selHeldZ18SysInFull : QRegister kHeldZ18Sys (kCoreSum42PG7 + 18) :=
  selHeldZ18ActInFull.compose selHeldZ18SysInAct
theorem unitary_val_inv_comm_of_comm {D : ℕ} (U : Unitary D) {M : Operator D}
    (h : U.1 * M = M * U.1) : (U⁻¹).1 * M = M * (U⁻¹).1 := by
  have hR : U.1 * (U⁻¹).1 = 1 := U.2.2
  have hL : (U⁻¹).1 * U.1 = 1 := U.2.1
  calc (U⁻¹).1 * M = (U⁻¹).1 * M * (U.1 * (U⁻¹).1) := by rw [hR, op_mul_one_assoc]
    _ = (U⁻¹).1 * (M * U.1) * (U⁻¹).1 := by simp only [op_mul_assoc_assoc]
    _ = ((U⁻¹).1 * U.1) * M * (U⁻¹).1 := by rw [← h]; simp only [op_mul_assoc_assoc]
    _ = M * (U⁻¹).1 := by rw [hL, op_one_mul_assoc]
theorem unitary_val_mul_self_eq_one_assoc {D : ℕ} {U : Unitary D} (h : U * U = 1) :
    U.1 * U.1 = 1 := by
  rw [← unitary_coe_mul_assoc, h, OneMemClass.coe_one]
open Classical in
theorem concat_compose_selHeldZ18ActInFull {n : ℕ}
    (rCS : QRegister (fullSysCoreWires 80 + 42) n) (rPG7 : QRegister 7 n) (rZ : QRegister 18 n)
    (hCS_PG : rCS.DisjointWires rPG7) (hCS_Z : rCS.DisjointWires rZ) (hPG_Z : rPG7.DisjointWires rZ)
      :
    ((rCS.concat rPG7 hCS_PG).concat rZ (disjointWires_concat_left hCS_PG hCS_Z hPG_Z)).compose
        selHeldZ18ActInFull =
      (rCS.concat rZ hCS_Z).concat rPG7 (disjointWires_concat_left hCS_Z hCS_PG
        (QRegExt.disjointWires_symm hPG_Z)) := by
  apply qreg_ext; intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun iSys ↦ ?_) (fun mPG ↦ ?_) idx
  · refine Fin.addCases (fun iCS ↦ ?_) (fun jZ ↦ ?_) iSys
    · have hL : selHeldZ18ActInFull (Fin.castAdd 7 (Fin.castAdd 18 iCS)) =
          Fin.castAdd 18 (Fin.castAdd 7 iCS) := by
        apply Fin.ext; have := iCS.isLt
        rw [selHeldZ18ActInFull_val_assoc]
        dsimp only [Fin.val_castAdd]
        rw [ite_eq_left this]
      rw [hL, QRegister.concat_apply_left, QRegister.concat_apply_left,
        QRegister.concat_apply_left, QRegister.concat_apply_left]
    · have hM : selHeldZ18ActInFull (Fin.castAdd 7 (Fin.natAdd (fullSysCoreWires 80 + 42) jZ)) =
          Fin.natAdd kCoreSum42PG7 jZ := by
        apply Fin.ext; have := jZ.isLt
        rw [selHeldZ18ActInFull_val_assoc]
        dsimp only [Fin.val_castAdd, Fin.val_natAdd]
        simp only [kHeldZ18Sys_eq_4094_assoc, fullSysCoreWires80_eq_4034_assoc,
          kCoreSum42PG7_eq_4083_assoc]
        split_ifs <;> omega
      rw [hM, QRegister.concat_apply_right, QRegister.concat_apply_left,
        QRegister.concat_apply_right]
  · have hR : selHeldZ18ActInFull (Fin.natAdd kHeldZ18Sys mPG) =
        Fin.castAdd 18 (Fin.natAdd (fullSysCoreWires 80 + 42) mPG) := by
      apply Fin.ext; have := mPG.isLt
      rw [selHeldZ18ActInFull_val_assoc]
      dsimp only [Fin.val_castAdd, Fin.val_natAdd]
      simp only [kHeldZ18Sys_eq_4094_assoc, fullSysCoreWires80_eq_4034_assoc,
        kCoreSum42PG7_eq_4083_assoc]
      split_ifs <;> omega
    rw [hR, QRegister.concat_apply_left, QRegister.concat_apply_right, QRegister.concat_apply_right]
open Classical in
theorem selHeldZ18SysInFull_compositions :
    selHeldZ18SysInFull.compose (rActLoc (fullSysCoreWires 80 + 42) 18) = selCoreSum42InFull ∧
    selHeldZ18SysInFull.compose (rZLoc (fullSysCoreWires 80 + 42) 18) = rZLoc kCoreSum42PG7 18 ∧
    selHeldZ18SysInFull.compose selCoreInHeldZ18Sys = selPosCoreInFull ∧
    selHeldZ18SysInFull.compose selPosCoreZ18InSys = selPosCoreZ18InFull := by
  have h1 : selHeldZ18SysInFull.compose (rActLoc (fullSysCoreWires 80 + 42) 18) =
    selCoreSum42InFull := by
    apply qreg_ext; intro i; apply Fin.ext; have := i.isLt
    simp only [selHeldZ18SysInFull, QRegister.compose_apply, selHeldZ18ActInFull_val_assoc,
      selHeldZ18SysInAct, rActLoc, selCoreSum42InFull, qreg_block_apply, zero_add]
    split_ifs; omega
  have h2 : selHeldZ18SysInFull.compose (rZLoc (fullSysCoreWires 80 + 42) 18) =
    rZLoc kCoreSum42PG7 18 := by
    apply qreg_ext; intro j; apply Fin.ext; have := j.isLt
    simp only [selHeldZ18SysInFull, QRegister.compose_apply, selHeldZ18ActInFull_val_assoc,
      selHeldZ18SysInAct, rZLoc, qreg_block_apply, zero_add,
      kHeldZ18Sys_eq_4094_assoc, fullSysCoreWires80_eq_4034_assoc, kCoreSum42PG7_eq_4083_assoc]
    split_ifs <;> omega
  have h3 : selHeldZ18SysInFull.compose selCoreInHeldZ18Sys = selPosCoreInFull := by
    apply qreg_ext; intro i; apply Fin.ext; have := i.isLt
    simp only [selHeldZ18SysInFull, QRegister.compose_apply, selHeldZ18ActInFull_val_assoc,
      selHeldZ18SysInAct, selCoreInHeldZ18Sys, selPosCoreInFull, qreg_block_apply, zero_add]
    simp only [posCoreWires_eq_4034_assoc, fullSysCoreWires80_eq_4034_assoc] at this ⊢
    split_ifs <;> omega
  refine ⟨h1, h2, h3, ?_⟩
  apply qreg_ext; intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · rw [QRegister.compose_apply]
    unfold selPosCoreZ18InSys selPosCoreZ18InFull
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    exact congrArg (fun r : QRegister _ _ ↦ r i) h3
  · rw [QRegister.compose_apply]
    unfold selPosCoreZ18InSys selPosCoreZ18InFull
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
    exact congrArg (fun r : QRegister _ _ ↦ r j) h2
/-- Repaired spectator-Hadamard-conjugated Mod-4 head unitary on `posCoreWires`
realized by `dHeadOrigin0RepairedConjH35`. -/
def uHeadConjHCore : Unitary (2 ^ posCoreWires) :=
  (uHad217)⁻¹ * uHeadPhaseMod4Origin0Repaired * uHad217
open Classical in
theorem uHeadConjHCore_comm_diagonal (g : Fin (2 ^ posCoreWires) → ℂ) (hSpec : ∀ x y : Fin (2
    ^ posCoreWires), rSpectatorElec3906InCore.AgreeOutside x y → g x = g y) (hTh : ∀ x y : Fin
    (2 ^ posCoreWires), (∀ w : Wire posCoreWires, w ≠ wHeadThresh (QRegExt.ofFin
    posCoreWires) → basisBits posCoreWires x w = basisBits posCoreWires y w) → g x = g y) :
    uHeadConjHCore.1 * Matrix.diagonal g = Matrix.diagonal g * uHeadConjHCore.1 := by
  have hHad : uHad217.1 * Matrix.diagonal g = Matrix.diagonal g * uHad217.1 :=
    elecProd217_comm_diagonal_of_agreeOutside (fun _ ↦ uHadamard18) g hSpec
  have hHadInv : ((uHad217)⁻¹).1 * Matrix.diagonal g = Matrix.diagonal g * ((uHad217)⁻¹).1 :=
    unitary_val_inv_comm_of_comm uHad217 hHad
  have hMid : uHeadPhaseMod4Origin0Repaired.1 * Matrix.diagonal g =
      Matrix.diagonal g * uHeadPhaseMod4Origin0Repaired.1 :=
    monomialZ8UnitaryN_comm_diagonal_of_invariant _ _ _ g hTh
  unfold uHeadConjHCore
  simp only [unitary_coe_mul_assoc]
  exact comm_mul_assoc (comm_mul_assoc hHadInv hMid) hHad
theorem headTargetCoord64_congr_of_coreBits {β₁ β₂ : BitAssignment posCoreWires}
    (hCoreBit : ∀ w : Wire posCoreWires, (w.val < 18 ∨ 3924 ≤ w.val) → w.val ≠ 3985 → β₁ w = β₂ w) :
    headTargetCoord64 β₁ = headTargetCoord64 β₂ :=
  (headTargetCoord64_congr_outside_spec_and_wTh
    (hCoreBit _ (by decide) (by decide))
    (fun q ↦ hCoreBit _ (by revert q; decide) (by revert q; decide))
    (fun q ↦ hCoreBit _ (by revert q; decide) (by revert q; decide))
    (fun q ↦ hCoreBit _ (by revert q; decide) (by revert q; decide))).2
theorem uHeadConjHCore_comm_diagonal_of_target {g : Fin (2 ^ posCoreWires) → ℂ} (hg : ∀ x y :
    Fin (2 ^ posCoreWires), headTargetCoord64 (basisBits posCoreWires x) = headTargetCoord64
    (basisBits posCoreWires y) → g x = g y) : uHeadConjHCore.1 * Matrix.diagonal g =
    Matrix.diagonal g * uHeadConjHCore.1 := by
  have hwTh : (wHeadThresh (QRegExt.ofFin posCoreWires)).val = 3985 := rfl
  exact uHeadConjHCore_comm_diagonal g
    (fun _ _ hOut ↦ hg _ _ (headTargetCoord64_congr_of_coreBits fun _ hw _ ↦
      agreeOutside_rSpectatorElec3906InCore_nonSpec hOut hw))
    (fun _ _ hNe ↦ hg _ _ (headTargetCoord64_congr_of_coreBits fun _ _ h3985 ↦
      hNe _ fun h ↦ h3985 ((congrArg Fin.val h).trans hwTh)))
open Classical in
theorem uStr_and_uHead_comm_diagonal (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14)))
    (d : Fin (2 ^ kHeldZ18Sys) → ℂ) (hd : ∀ x y : Fin (2 ^ kHeldZ18Sys), headTargetCoord64
    (basisBits posCoreWires (selCoreInHeldZ18Sys.extractIndex x)) = headTargetCoord64
    (basisBits posCoreWires (selCoreInHeldZ18Sys.extractIndex y)) → (rZLoc (fullSysCoreWires
    80 + 42) 18).extractIndex x = (rZLoc (fullSysCoreWires 80 + 42) 18).extractIndex y → d x
    = d y) : ((rActLoc (fullSysCoreWires 80 + 42) 18).embedUnitary (uStr3AxisOfSpec uSpec)).1
    * Matrix.diagonal d = Matrix.diagonal d * ((rActLoc (fullSysCoreWires 80 + 42)
    18).embedUnitary (uStr3AxisOfSpec uSpec)).1 ∧ (((rActLoc (fullSysCoreWires 80 + 42)
    18).embedUnitary (uStr3AxisOfSpec uSpec))⁻¹).1 * Matrix.diagonal d = Matrix.diagonal d *
    (((rActLoc (fullSysCoreWires 80 + 42) 18).embedUnitary (uStr3AxisOfSpec uSpec))⁻¹).1 ∧
    (selCoreInHeldZ18Sys.embedUnitary uHeadConjHCore).1 * Matrix.diagonal d = Matrix.diagonal
    d * (selCoreInHeldZ18Sys.embedUnitary uHeadConjHCore).1 := by
  have hdBit {x y : Fin (2 ^ kHeldZ18Sys)} (hxy : ∀ q : Fin kHeldZ18Sys, (q.val < 18 ∨ (3924 ≤
      q.val ∧ q.val < fullSysCoreWires 80) ∨ fullSysCoreWires 80 + 42 ≤ q.val) → q.val ≠
      3985 → basisBits kHeldZ18Sys x q = basisBits kHeldZ18Sys y q) : d x = d y := by
    refine hd x y (headTargetCoord64_congr_of_coreBits fun w hw h3985 ↦ ?_)
      (extractIndex_eq_of_basisBits_eq_assoc _ fun j ↦ ?_)
    · rw [basisBits_extractIndex_assoc selCoreInHeldZ18Sys,
        basisBits_extractIndex_assoc selCoreInHeldZ18Sys]
      have hwv : (selCoreInHeldZ18Sys w).val = w.val := by simp [selCoreInHeldZ18Sys]
      have hlt80 : w.val < fullSysCoreWires 80 := by
        have h1 := posCoreWires_eq_4034_assoc
        have h2 := w.isLt
        rw [fullSysCoreWires80_eq_4034_assoc]
        omega
      exact hxy (selCoreInHeldZ18Sys w)
        (by rw [hwv]; exact hw.elim Or.inl fun h ↦ Or.inr (Or.inl ⟨h, hlt80⟩))
        (by rw [hwv]; exact h3985)
    · have hjv : (rZLoc (fullSysCoreWires 80 + 42) 18 j).val = (fullSysCoreWires 80 + 42) + j.val :=
        by
        simp [rZLoc]
      exact hxy _ (Or.inr (Or.inr (by
        omega))) (by rw [hjv, fullSysCoreWires80_eq_4034_assoc]; omega)
  let rA := rActLoc (fullSysCoreWires 80 + 42) 18
  have hAx (w : Fin 3) : (rA.embedUnitary ((selCoreSum14In42 80 w).embedUnitary
      ((selSpec217InCoreSum14 80).embedUnitary (uSpec w)))).1 * Matrix.diagonal d =
      Matrix.diagonal d * (rA.embedUnitary ((selCoreSum14In42 80 w).embedUnitary
      ((selSpec217InCoreSum14 80).embedUnitary (uSpec w)))).1 := by
    obtain ⟨hvSpec, hvSum⟩ := selCoreSum14_compose_selSpec217_val_assoc w
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val]
    refine embedMatrix_comm_diagonal_of_outside _ (uSpec w).1 d fun x y hOut ↦ hdBit fun q hq _ ↦
      hOut q ?_
    rintro ⟨idx, rfl⟩
    revert hq
    refine Fin.addCases (fun iSpec hq ↦ ?_) (fun jSum hq ↦ ?_) idx
    · have hv : ((rA.compose (selCoreSum14In42 80 w)).compose (selSpec217InCoreSum14 80)
          (Fin.castAdd 14 iSpec)).val = 18 + iSpec.val := by
        simp only [QRegister.compose_apply, rA, rActLoc, qreg_block_apply, zero_add]
        exact hvSpec iSpec
      have := iSpec.isLt
      rw [hv, fullSysCoreWires80_eq_4034_assoc] at hq
      omega
    · have hv : ((rA.compose (selCoreSum14In42 80 w)).compose (selSpec217InCoreSum14 80)
          (Fin.natAdd 3906 jSum)).val = fullSysCoreWires 80 + (14 * w.val + jSum.val) := by
        simp only [QRegister.compose_apply, rA, rActLoc, qreg_block_apply, zero_add]
        exact hvSum jSum
      have := jSum.isLt
      have := w.isLt
      rw [hv, fullSysCoreWires80_eq_4034_assoc] at hq
      omega
  have hStr : (rA.embedUnitary (uStr3AxisOfSpec uSpec)).1 * Matrix.diagonal d =
      Matrix.diagonal d * (rA.embedUnitary (uStr3AxisOfSpec uSpec)).1 := by
    unfold uStr3AxisOfSpec
    simp only [QRegister.embedUnitary_mul, unitary_coe_mul_assoc]
    exact comm_mul_assoc (comm_mul_assoc (hAx 2) (hAx 1)) (hAx 0)
  have hHead : (selCoreInHeldZ18Sys.embedUnitary uHeadConjHCore).1 * Matrix.diagonal d =
      Matrix.diagonal d * (selCoreInHeldZ18Sys.embedUnitary uHeadConjHCore).1 := by
    let r := selCoreInHeldZ18Sys
    let rZ := rZLoc (fullSysCoreWires 80 + 42) 18
    have hDisj := QRegister.disjoint_comm.mp hDisjPosCoreZ18Sys_assoc
    rw [QRegister.embedUnitary_val]
    refine Matrix.ext fun x y ↦ ?_
    rw [op_mul_diagonal_assoc, op_diagonal_mul_assoc, QRegister.embedMatrix_apply]
    by_cases hEnv : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2
    · rw [ite_eq_left hEnv, mul_one]
      have hxRep : r.replaceIndex y (r.extractIndex x) = x :=
        r.basisSplitEquiv.injective (by
          rw [r.basisSplitEquiv_replaceIndex, ← hEnv, Prod.ext_iff]
          exact ⟨(r.basisSplitEquiv_apply_fst x).symm, rfl⟩)
      have hFib : uHeadConjHCore.1 * Matrix.diagonal (fun a ↦ d (r.replaceIndex y a)) =
          Matrix.diagonal (fun a ↦ d (r.replaceIndex y a)) * uHeadConjHCore.1 :=
        uHeadConjHCore_comm_diagonal_of_target fun a₁ a₂ hT ↦ hd _ _
          (by rwa [selCoreInHeldZ18Sys.extractIndex_replaceIndex,
                selCoreInHeldZ18Sys.extractIndex_replaceIndex])
          ((QRegister.extractIndex_replaceIndex_of_disjoint rZ r hDisj y a₁).trans
            (QRegister.extractIndex_replaceIndex_of_disjoint rZ r hDisj y a₂).symm)
      have hEntry := congrFun (congrFun hFib (r.extractIndex x)) (r.extractIndex y)
      rwa [op_mul_diagonal_assoc, op_diagonal_mul_assoc, hxRep,
        r.replaceIndex_extractIndex y] at hEntry
    · rw [ite_eq_right hEnv, mul_zero, zero_mul, mul_zero]
  exact ⟨hStr, unitary_val_inv_comm_of_comm _ hStr, hHead⟩
/-- Catalyst-free 7-factor inner Stage-A unitary on `kHeldZ18Sys = (fullSysCoreWires 80 + 42) + 18`
before absorbing clean `rZ18`. -/
noncomputable def uStageAInnerSysEff (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ kHeldZ18Sys) :=
  let uXor := selPosCoreZ18InSys.embedUnitary uXorZTarget18
  let uStr := (rActLoc (fullSysCoreWires 80 + 42) 18).embedUnitary (uStr3AxisOfSpec uSpec)
  let uHead := selCoreInHeldZ18Sys.embedUnitary uHeadConjHCore
  uXor * (uPhiHeldZ18Eff⁻¹ * (uStr * (uHead * (uStr⁻¹ * (uPhiHeldZ18Eff * uXor)))))
/-- Catalyzed 7-factor inner Stage-A unitary on `kCoreSum42PG7 + 18` before absorbing clean
  `rZ18`. -/
noncomputable def uStageAInnerFullCat (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ (kCoreSum42PG7 + 18)) :=
  let uXor := selPosCoreZ18InFull.embedUnitary uXorZTarget18
  let uPhi := selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat
  let uStr := selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uSpec)
  let uHead := selPosCoreInFull.embedUnitary uHeadConjHCore
  uXor * (uPhi⁻¹ * (uStr * (uHead * (uStr⁻¹ * (uPhi * uXor)))))
/-- Diagonal entry `1` iff `rZ18` holds `headTargetPoint18` of `rPosCore` inside `kHeldZ18Sys`. -/
def pZMatchSysEntry (x : Fin (2 ^ kHeldZ18Sys)) : ℂ :=
  if (rZLoc (fullSysCoreWires 80 + 42) 18).extractIndex x =
      headTargetPoint18 (basisBits posCoreWires (selCoreInHeldZ18Sys.extractIndex x)) then 1 else 0
/-- Diagonal projector `{rZ18 = headTargetPoint18 rPosCore}` on `2 ^ kHeldZ18Sys`. -/
def pZMatchSys : Operator (2 ^ kHeldZ18Sys) := Matrix.diagonal pZMatchSysEntry
open Classical in
theorem uStr_and_uHead_comm_pZMatchSys (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    ((rActLoc (fullSysCoreWires 80 + 42) 18).embedUnitary (uStr3AxisOfSpec uSpec)).1 * pZMatchSys =
      pZMatchSys * ((rActLoc (fullSysCoreWires 80 +
        42) 18).embedUnitary (uStr3AxisOfSpec uSpec)).1 ∧
    (((rActLoc (fullSysCoreWires 80 + 42) 18).embedUnitary (uStr3AxisOfSpec uSpec))⁻¹).1 *
      pZMatchSys =
      pZMatchSys * (((rActLoc (fullSysCoreWires 80 +
        42) 18).embedUnitary (uStr3AxisOfSpec uSpec))⁻¹).1 ∧
    (selCoreInHeldZ18Sys.embedUnitary uHeadConjHCore).1 * pZMatchSys =
      pZMatchSys * (selCoreInHeldZ18Sys.embedUnitary uHeadConjHCore).1 :=
  uStr_and_uHead_comm_diagonal uSpec pZMatchSysEntry fun _ _ hT hZ ↦ by
    unfold pZMatchSysEntry headTargetPoint18
    rw [hZ, hT]
noncomputable def fXorSys (x : Fin (2 ^ kHeldZ18Sys)) : Fin (2 ^ kHeldZ18Sys) :=
  let β := basisBits kHeldZ18Sys x
  (basisBitsEquiv kHeldZ18Sys).symm
    (writeReg β (rZLoc (fullSysCoreWires 80 + 42) 18) fun k ↦
      β (rZLoc (fullSysCoreWires 80 + 42) 18 k) +
        basisBits 18 (headTargetPoint18 (fun i ↦ β (selCoreInHeldZ18Sys i))) k)

open Classical in
theorem uXorSys_apply_assoc (x y : Fin (2 ^ kHeldZ18Sys)) :
    (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 x y =
      if x = fXorSys y then 1 else 0 := by
  have hKet : ((selPosCoreZ18InSys.embedUnitary uXorZTarget18).1).mulVec
      (ket (basisBits kHeldZ18Sys y)) = ket (writeReg (basisBits kHeldZ18Sys y) (rZLoc
      (fullSysCoreWires 80 + 42) 18) fun k ↦ basisBits kHeldZ18Sys y (rZLoc
      (fullSysCoreWires 80 + 42) 18 k) + basisBits 18 (headTargetPoint18 (fun i ↦ basisBits
      kHeldZ18Sys y (selCoreInHeldZ18Sys i))) k) := ket_embedUnitary_uXorZTarget18
      selCoreInHeldZ18Sys (rZLoc (fullSysCoreWires 80 + 42) 18) hDisjPosCoreZ18Sys_assoc
      (basisBits kHeldZ18Sys y)
  rw [mulVec_ket_apply_assoc (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 x y, hKet,
    ket_apply_eq_ite_assoc]
  rfl

theorem basisBits_fXorSys_rZ (x : Fin (2 ^ kHeldZ18Sys)) (k : Fin 18) : basisBits kHeldZ18Sys
    (fXorSys x) (rZLoc (fullSysCoreWires 80 + 42) 18 k) = basisBits kHeldZ18Sys x
    (rZLoc (fullSysCoreWires 80 + 42) 18 k) + basisBits 18 (headTargetPoint18 (basisBits
    posCoreWires (selCoreInHeldZ18Sys.extractIndex x))) k := by
  have hC : (fun i ↦ basisBits kHeldZ18Sys x (selCoreInHeldZ18Sys i)) =
      basisBits posCoreWires (selCoreInHeldZ18Sys.extractIndex x) :=
    funext fun i ↦ (basisBits_extractIndex_assoc selCoreInHeldZ18Sys x i).symm
  change (basisBitsEquiv kHeldZ18Sys (fXorSys x)) _ = _
  dsimp only [fXorSys]
  rw [(basisBitsEquiv kHeldZ18Sys).apply_symm_apply, writeReg_apply_reg, hC]

theorem basisBits_fXorSys_of_not_mem (x : Fin (2 ^ kHeldZ18Sys)) {q : Fin kHeldZ18Sys}
    (hq : q ∉ Set.range (rZLoc (fullSysCoreWires 80 + 42) 18).wires) :
    basisBits kHeldZ18Sys (fXorSys x) q = basisBits kHeldZ18Sys x q := by
  change (basisBitsEquiv kHeldZ18Sys (fXorSys x)) q = _
  dsimp only [fXorSys]
  rw [(basisBitsEquiv kHeldZ18Sys).apply_symm_apply, writeReg_apply_of_not_mem _ _ _ _ hq]

theorem fXorSys_involutive (x : Fin (2 ^ kHeldZ18Sys)) : fXorSys (fXorSys x) = x := by
  have hC : selCoreInHeldZ18Sys.extractIndex (fXorSys x) = selCoreInHeldZ18Sys.extractIndex x :=
    extractIndex_eq_of_basisBits_eq_assoc _ fun i ↦
      basisBits_fXorSys_of_not_mem x fun ⟨k, hk⟩ ↦ hDisjPosCoreZ18Sys_assoc.ne i k hk.symm
  refine (basisBitsEquiv kHeldZ18Sys).injective (funext fun q ↦ ?_)
  change basisBits kHeldZ18Sys (fXorSys (fXorSys x)) q = basisBits kHeldZ18Sys x q
  by_cases hq : q ∈ Set.range (rZLoc (fullSysCoreWires 80 + 42) 18).wires
  · obtain ⟨k, hk⟩ := hq
    have hk' : rZLoc (fullSysCoreWires 80 + 42) 18 k = q := hk
    rw [← hk', basisBits_fXorSys_rZ, basisBits_fXorSys_rZ, hC,
      add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [basisBits_fXorSys_of_not_mem _ hq, basisBits_fXorSys_of_not_mem _ hq]

open Classical in
private theorem conj_embedUnitary_xorTarget18_projZero_gen {K N : ℕ}
    (U : Unitary (2 ^ (K + 18))) (tgtFn : BitAssignment K → Fin (2 ^ 18))
    (rC : QRegister K N) (rZ : QRegister 18 N) (hCZ : rC.DisjointWires rZ)
    (hSq0 : U * U = 1)
    (hKet : ∀ β : BitAssignment N,
      ((rC.concat rZ hCZ).embedUnitary U).1.mulVec (ket β) =
        ket (writeReg β rZ fun k ↦ β (rZ k) + basisBits 18 (tgtFn (fun i ↦ β (rC i))) k)) :
    ((rC.concat rZ hCZ).embedUnitary U).1 *
        rZ.basisOutcomeProjector 0 *
        ((rC.concat rZ hCZ).embedUnitary U).1 =
      Matrix.diagonal (fun x : Fin (2 ^ N) ↦
        if rZ.extractIndex x = tgtFn (fun i ↦ basisBits N x (rC i)) then 1 else 0) := by
  let uXor := ((rC.concat rZ hCZ).embedUnitary U).1
  apply OctahedralOrbit.matrix_ext_ket
  intro β
  let x := (basisBitsEquiv N).symm β
  have hxβ : basisBits N x = β := (basisBitsEquiv N).apply_symm_apply β
  let tgt := tgtFn (fun i ↦ β (rC i))
  let β' := writeReg β rZ fun k ↦ β (rZ k) + basisBits 18 tgt k
  have hXor1 : uXor.mulVec (ket β) = ket β' := hKet β
  have hXor2 : uXor.mulVec (ket β') = ket β := by
    have hSq : uXor * uXor = 1 :=
      unitary_val_mul_self_eq_one_assoc
        (by rw [← QRegister.embedUnitary_mul, hSq0, QRegister.embedUnitary_one])
    have hInv : (uXor * uXor).mulVec (ket β) = ket β := by rw [hSq, Matrix.one_mulVec]
    rwa [← Matrix.mulVec_mulVec, hXor1] at hInv
  have hIff : rZ.extractIndex ((basisBitsEquiv N).symm β') = 0 ↔ rZ.extractIndex x = tgt := by
    rw [QRegExt.extractIndex_eq_zero_iff]
    have hβ' : ∀ k : Fin 18, basisBits N ((basisBitsEquiv N).symm β') (rZ k) =
        β (rZ k) + basisBits 18 tgt k := fun k ↦ by
      change (basisBitsEquiv N ((basisBitsEquiv N).symm β')) (rZ k) = _
      rw [(basisBitsEquiv N).apply_symm_apply]
      dsimp only [β']
      rw [writeReg_apply_reg]
    have hAdd0 : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
    simp only [hβ', hAdd0]
    refine ⟨fun h ↦ (basisBitsEquiv 18).injective (funext fun k ↦ ?_), fun h k ↦ ?_⟩
    · change basisBits 18 (rZ.extractIndex x) k = basisBits 18 tgt k
      rw [basisBits_extractIndex_assoc rZ, ← h k]
      exact congrFun hxβ (rZ k)
    · rw [← h, basisBits_extractIndex_assoc rZ]
      exact congrFun hxβ.symm (rZ k)
  change (uXor * rZ.basisOutcomeProjector 0 * uXor).mulVec (ket β) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hXor1,
    QRegister.basisOutcomeProjector_eq_diagonal, diagonal_mulVec_ket_assoc,
    Matrix.mulVec_smul, hXor2, diagonal_mulVec_ket_assoc]
  refine congrArg (· • ket β) ?_
  have hTgtEq : tgtFn (fun i ↦ basisBits N x (rC i)) = tgt := by
    dsimp only [tgt]
    rw [hxβ]
  rw [hTgtEq]
  by_cases h0 : rZ.extractIndex x = tgt
  · rw [ite_eq_left (hIff.mpr h0), ite_eq_left h0]
  · rw [ite_eq_right (mt hIff.mp h0), ite_eq_right h0]
section NoPowEvalUXorSys
attribute [local irreducible] HPow.hPow
open Classical in
theorem uXorSys_conj_projZero_eq_pZMatchSys :
    (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 *
        (rZLoc (fullSysCoreWires 80 + 42) 18).basisOutcomeProjector 0 *
        (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 = pZMatchSys := by
  unfold selPosCoreZ18InSys pZMatchSys
  rw [conj_embedUnitary_xorTarget18_projZero_gen uXorZTarget18 headTargetPoint18
    selCoreInHeldZ18Sys (rZLoc (fullSysCoreWires 80 + 42) 18) hDisjPosCoreZ18Sys_assoc
    uXorZTarget18_mul_self
    (ket_embedUnitary_uXorZTarget18 selCoreInHeldZ18Sys
      (rZLoc (fullSysCoreWires 80 + 42) 18) hDisjPosCoreZ18Sys_assoc)]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  dsimp only [pZMatchSysEntry]
  have hBits : (fun i ↦ basisBits kHeldZ18Sys x (selCoreInHeldZ18Sys i)) =
      basisBits posCoreWires (selCoreInHeldZ18Sys.extractIndex x) :=
    funext fun i ↦ (basisBits_extractIndex_assoc selCoreInHeldZ18Sys x i).symm
  rw [hBits]
end NoPowEvalUXorSys
open Classical in
theorem uStageAInnerSysEff_comm_projZero (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    (uStageAInnerSysEff uSpec).1 * (rZLoc (fullSysCoreWires 80 + 42) 18).basisOutcomeProjector 0 =
      (rZLoc (fullSysCoreWires 80 + 42) 18).basisOutcomeProjector 0 *
        (uStageAInnerSysEff uSpec).1 := by
  have hXorSq : (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 *
      (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 = 1 :=
    unitary_val_mul_self_eq_one_assoc
      (by rw [← QRegister.embedUnitary_mul, uXorZTarget18_mul_self, QRegister.embedUnitary_one])
  have hPhi : uPhiHeldZ18Eff.1 * pZMatchSys = pZMatchSys * uPhiHeldZ18Eff.1 := by
    rw [uPhiHeldZ18Eff_eq_diagonal, pZMatchSys]
    exact diagonal_comm_op_assoc _ _
  obtain ⟨hStr, hStrI, hHead⟩ := uStr_and_uHead_comm_pZMatchSys uSpec
  unfold uStageAInnerSysEff
  simp only [unitary_coe_mul_assoc]
  exact comm_conj_prod5_assoc hXorSq uXorSys_conj_projZero_eq_pZMatchSys
    (unitary_val_inv_comm_of_comm uPhiHeldZ18Eff hPhi) hStr hHead hStrI hPhi
/-- `7`-qubit phase-gradient catalyst block `[4076 .. 4083)` inside `kCoreSum42PG7 + 18`. -/
def rPG7InFull : QRegister 7 (kCoreSum42PG7 + 18) :=
  QRegister.block (fullSysCoreWires 80 + 42) 7 (by decide)
open Classical in
theorem selHeldZ18SysInFull_disj_rPG7InFull :
    selHeldZ18SysInFull.DisjointWires rPG7InFull := by
  rw [QRegister.disjoint_iff]; intro i m h
  have hv := congrArg Fin.val h
  have hi := i.isLt; have hm := m.isLt
  simp only [selHeldZ18SysInFull, QRegister.compose_apply, selHeldZ18ActInFull_val_assoc,
    selHeldZ18SysInAct, rPG7InFull, qreg_block_apply, zero_add,
    kHeldZ18Sys_eq_4094_assoc, fullSysCoreWires80_eq_4034_assoc,
      kCoreSum42PG7_eq_4083_assoc] at hi hm hv
  split_ifs at hv <;> omega
open Classical in
theorem selHeldZ18SysInFull_concat_rPG7InFull : selHeldZ18SysInFull.concat rPG7InFull
    selHeldZ18SysInFull_disj_rPG7InFull = selHeldZ18ActInFull := by
  apply qreg_ext; intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) idx
  · rw [QRegister.concat_apply_left]
    dsimp only [selHeldZ18SysInFull, QRegister.compose_apply]
    exact congrArg selHeldZ18ActInFull (Fin.ext (by simp [selHeldZ18SysInAct]))
  · rw [QRegister.concat_apply_right]
    apply Fin.ext; have hm := m.isLt
    simp only [rPG7InFull, qreg_block_apply, selHeldZ18ActInFull_val_assoc, Fin.val_natAdd,
      kHeldZ18Sys_eq_4094_assoc, fullSysCoreWires80_eq_4034_assoc, kCoreSum42PG7_eq_4083_assoc]
    split_ifs <;> omega
open Classical in
theorem uStageAInnerFullCat_comm_projZero (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    (uStageAInnerFullCat uSpec).1 * (rZLoc kCoreSum42PG7 18).basisOutcomeProjector 0 =
      (rZLoc kCoreSum42PG7 18).basisOutcomeProjector 0 * (uStageAInnerFullCat uSpec).1 := by
  obtain ⟨hCompA, hCompZ, hCompC, hCompCZ⟩ := selHeldZ18SysInFull_compositions
  let rSys := selHeldZ18SysInFull
  let uXor := (selPosCoreZ18InFull.embedUnitary uXorZTarget18).1
  let PZ := (rZLoc kCoreSum42PG7 18).basisOutcomeProjector 0
  let pZFull := rSys.embedMatrix pZMatchSys
  have hXorEq : uXor = rSys.embedMatrix (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 := by
    dsimp only [uXor, rSys]; rw [← hCompCZ, QRegister.embedUnitary_compose]; rfl
  have hPZEq : PZ = rSys.embedMatrix ((rZLoc (fullSysCoreWires 80 +
    42) 18).basisOutcomeProjector 0) := by
    dsimp only [PZ, rSys]; rw [← hCompZ, embedMatrix_basisOutcomeProjector_zero_assoc]
  have hXorSq : uXor * uXor = 1 :=
    unitary_val_mul_self_eq_one_assoc
      (by rw [← QRegister.embedUnitary_mul, uXorZTarget18_mul_self, QRegister.embedUnitary_one])
  have hConj : uXor * PZ * uXor = pZFull := by
    rw [hXorEq, hPZEq, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul,
      uXorSys_conj_projZero_eq_pZMatchSys]
  obtain ⟨hPresF, hPresI⟩ := preservesOutside_uPhiHeldZ18Cat selHeldZ18SysInFull rPG7InFull
    selHeldZ18SysInFull_disj_rPG7InFull
  rw [selHeldZ18SysInFull_concat_rPG7InFull] at hPresF hPresI
  rw [QRegister.embedUnitary_inv] at hPresI
  have hPZFullDiag : pZFull = Matrix.diagonal (fun x ↦ pZMatchSysEntry (rSys.extractIndex x)) := by
    dsimp only [pZFull, pZMatchSys]; exact QRegister.embedMatrix_diagonal rSys pZMatchSysEntry
  have hOutEq : ∀ x y, rPG7InFull.AgreeOutside x y →
      pZMatchSysEntry (rSys.extractIndex x) = pZMatchSysEntry (rSys.extractIndex y) :=
    fun x y hOut ↦ congrArg pZMatchSysEntry <| extractIndex_eq_of_basisBits_eq_assoc rSys fun q ↦
      hOut (rSys q) fun ⟨m, hm⟩ ↦ selHeldZ18SysInFull_disj_rPG7InFull.ne q m hm.symm
  have hPhi : (selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat).1 * pZFull =
      pZFull * (selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat).1 := by
    rw [hPZFullDiag]
    exact preservesOutside_comm_diagonal hPresF _ hOutEq
  have hPhiI : ((selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat)⁻¹).1 * pZFull =
      pZFull * ((selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat)⁻¹).1 := by
    rw [hPZFullDiag]
    exact preservesOutside_comm_diagonal hPresI _ hOutEq
  obtain ⟨hStr0, _, hHead0⟩ := uStr_and_uHead_comm_pZMatchSys uSpec
  have hStr : (selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uSpec)).1 * pZFull =
      pZFull * (selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uSpec)).1 := by
    rw [← hCompA, QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, hStr0, QRegister.embedMatrix_mul]
  have hStrI : ((selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uSpec))⁻¹).1 * pZFull =
      pZFull * ((selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uSpec))⁻¹).1 :=
    unitary_val_inv_comm_of_comm _ hStr
  have hHead : (selPosCoreInFull.embedUnitary uHeadConjHCore).1 * pZFull =
      pZFull * (selPosCoreInFull.embedUnitary uHeadConjHCore).1 := by
    rw [← hCompC, QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, hHead0, QRegister.embedMatrix_mul]
  unfold uStageAInnerFullCat
  simp only [unitary_coe_mul_assoc]
  exact comm_conj_prod5_assoc hXorSq hConj hPhiI hStr hHead hStrI hPhi
/-- Catalyst-free inner Stage-A unitary on `fullSysCoreWires 80 + 42` after absorbing clean
  `rZ18`. -/
noncomputable def uStageAInnerEff (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  extractCleanAncillaUnitary (uStageAInnerSysEff uSpec) (uStageAInnerSysEff_comm_projZero uSpec)
/-- Catalyzed inner Stage-A unitary on `kCoreSum42PG7` after absorbing clean `rZ18`. -/
noncomputable def uStageAInnerCat (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ kCoreSum42PG7) :=
  extractCleanAncillaUnitary (uStageAInnerFullCat uSpec) (uStageAInnerFullCat_comm_projZero uSpec)
/-- Catalyst-free inner Stage-A unitary conjugated by `uSwapCore3967` (`3967 ↔ 4029`). -/
noncomputable def uStageAInnerSwapEff (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  let uSw := (rCoreInCoreSum42 80).embedUnitary uSwapCore3967
  (uSw * uStageAInnerEff uSpec) * uSw
/-- Catalyzed inner Stage-A unitary conjugated by `uSwapCore3967` (`3967 ↔ 4029`). -/
noncomputable def uStageAInnerSwapCat (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ kCoreSum42PG7) :=
  let uSw := (selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967
  (uSw * uStageAInnerCat uSpec) * uSw
/-- Catalyst-free 5-step Stage-A unitary (conjugating `uStageAInnerSwapEff` by Electron-`0`
  `QFT_64`). -/
noncomputable def uStageA5StepEff (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  let uQ0 := (rElec0InCoreSum42 80).embedUnitary uCoreHadamard18
  uQ0⁻¹ * (uStageAInnerSwapEff uSpec * uQ0)
/-- Catalyzed 5-step Stage-A unitary (conjugating `uStageAInnerSwapCat` by
  `activeOneElecExpQftStage128.uCat`). -/
noncomputable def uStageA5StepCat (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ kCoreSum42PG7) :=
  let uQ0 := selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat
  uQ0⁻¹ * (uStageAInnerSwapCat uSpec * uQ0)
/-- Catalyst-free 7-step Stage-A unitary on `pStream218Core 80` (`eStream218Core`). -/
noncomputable def uStageA7StepEff (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  let uAdd0 := uSlot0Sum42Add 80
  uAdd0 * (uStageA5StepEff uSpec * uAdd0⁻¹)
/-- Catalyzed 7-step Stage-A unitary on `pStream218Core 80` (`eStream218Core`). -/
noncomputable def uStageA7StepCat (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ kCoreSum42PG7) :=
  let uAdd0 := selCoreSum42InAct.embedUnitary (uSlot0Sum42Add 80)
  uAdd0 * (uStageA5StepCat uSpec * uAdd0⁻¹)
/-- Catalyst-free 7-step `Hoist` (`E_stream42`) Stage-A unitary conjugated by
  `uTrailCliffordXor80`. -/
noncomputable def uStageA7StepHoistEff (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  let uTr := (rCoreInCoreSum42 80).embedUnitary uTrailCliffordXor80
  uTr⁻¹ * (uStageA7StepEff uSpec * uTr)
/-- Catalyzed 7-step `Hoist` (`E_stream42`) Stage-A unitary conjugated by `uTrailCliffordXor80`. -/
noncomputable def uStageA7StepHoistCat (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) :
    Unitary (2 ^ kCoreSum42PG7) :=
  let uTr := (selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uTrailCliffordXor80
  uTr⁻¹ * (uStageA7StepCat uSpec * uTr)
theorem concat_compose_stageAFull_selectors {n : ℕ}
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum42 : QRegister 42 n)
    (rPG7 : QRegister 7 n) (rZ18 : QRegister 18 n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCPG : rCore.DisjointWires rPG7) (hSPG : rSum42.DisjointWires rPG7)
    (hCZ : rCore.DisjointWires rZ18) (hSZ : rSum42.DisjointWires rZ18)
    (hPGZ : rPG7.DisjointWires rZ18) :
    let rCS := rCore.concat rSum42 hCSum42
    let hCS_PG := disjointWires_concat_left hCSum42 hCPG hSPG
    let rAct := rCS.concat rPG7 hCS_PG
    let hCS_Z := disjointWires_concat_left hCSum42 hCZ hSZ
    let hAZ := disjointWires_concat_left hCS_PG hCS_Z hPGZ
    let rFull := rAct.concat rZ18 hAZ
    rFull.compose selPosCoreInFull = rCore.compose selPosCoreInCore80 ∧
    rFull.compose selCoreSum42InFull = rCS ∧
    rFull.compose selPosCoreZ18InFull =
      (rCore.compose selPosCoreInCore80).concat rZ18 (hCZ.compose_left selPosCoreInCore80) := by
  intro rCS hCS_PG rAct hCS_Z hAZ rFull
  have h1 : rFull.compose selPosCoreInFull = rCore.compose selPosCoreInCore80 := by
    apply qreg_ext; intro i
    have hSel : selPosCoreInFull i =
        Fin.castAdd 18 (Fin.castAdd 7 (Fin.castAdd 42 (selPosCoreInCore80 i))) :=
      Fin.ext (by simp [selPosCoreInFull, selPosCoreInCore80])
    rw [QRegister.compose_apply, hSel, QRegister.concat_apply_left,
      QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.compose_apply]
  have h2 : rFull.compose selCoreSum42InFull = rCS := by
    apply qreg_ext; intro i
    have hSel : selCoreSum42InFull i = Fin.castAdd 18 (Fin.castAdd 7 i) :=
      Fin.ext (by simp [selCoreSum42InFull])
    rw [QRegister.compose_apply, hSel, QRegister.concat_apply_left, QRegister.concat_apply_left]
  refine ⟨h1, h2, ?_⟩
  apply qreg_ext; intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · dsimp only [QRegister.compose_apply, selPosCoreZ18InFull]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    exact congrArg (fun r : QRegister _ _ ↦ r i) h1
  · have hZ : selPosCoreZ18InFull (Fin.natAdd posCoreWires j) = Fin.natAdd kCoreSum42PG7 j := by
      dsimp only [selPosCoreZ18InFull]
      rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [rZLoc])
    rw [QRegister.compose_apply, hZ, QRegister.concat_apply_right, QRegister.concat_apply_right]
theorem unitary_mul_assoc_assoc {D : ℕ} (a b c : Unitary D) : a * b * c = a * (b * c) :=
    _root_.mul_assoc a b c
open Classical in
theorem widenActive_of_compose_eq_assoc {Var : Type} [Fintype Var] [DecidableEq Var]
    {kSub kBig mWork n : ℕ} [NeZero (2 ^ n)] {rSub : QRegister kSub n}
    {rBig : QRegister kBig n} {sel : QRegister kSub kBig} {rWork : QRegister mWork n}
    {U : Unitary (2 ^ kSub)} {d : DynamicCircuit Var n} (hEq : rBig.compose sel = rSub)
    (hd : RealizesEmbeddedUnitaryWithCleanWorkspace rSub rWork U d) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rBig rWork (sel.embedUnitary U) d := by
  have hd' : RealizesEmbeddedUnitaryWithCleanWorkspace (rBig.compose sel) rWork U d := by
    rwa [hEq]
  exact hd'.widenActive
open Classical in
theorem widenActive_inv_of_compose_eq_assoc {Var : Type} [Fintype Var] [DecidableEq Var]
    {kSub kBig mWork n : ℕ} [NeZero (2 ^ n)] {rSub : QRegister kSub n}
    {rBig : QRegister kBig n} {sel : QRegister kSub kBig} {rWork : QRegister mWork n}
    {U : Unitary (2 ^ kSub)} {d : DynamicCircuit Var n} (hEq : rBig.compose sel = rSub)
    (hd : RealizesEmbeddedUnitaryWithCleanWorkspace rSub rWork U⁻¹ d) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rBig rWork (sel.embedUnitary U)⁻¹ d := by
  rw [← QRegister.embedUnitary_inv]
  exact widenActive_of_compose_eq_assoc hEq hd
open Classical in
theorem intertwinesCat_embed_concat_of_localCat {kAct mCat N : ℕ} (rId : QRegister kAct N)
    (rPG : QRegister mCat N) (hDisj : rId.DisjointWires rPG) {U_cat : Unitary (2 ^ mCat)}
    {W_cat : Unitary (2 ^ (kAct + mCat))} {U_eff : Unitary (2 ^ kAct)}
    (hLoc : IntertwinesLocalCat U_cat W_cat U_eff) : IntertwinesCat (rPG.embedUnitary U_cat).1
    (rPG.basisOutcomeProjector 0) ((rId.concat rPG hDisj).embedUnitary W_cat).1
    (rId.embedUnitary U_eff).1 := by
  let r := rId.concat rPG hDisj
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (by omega)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  have hCA : r.compose rAct0 = rId :=
    qreg_ext fun i ↦ by
      have hi : rAct0 i = Fin.castAdd mCat i := Fin.ext (by simp [rAct0])
      rw [QRegister.compose_apply, hi, QRegister.concat_apply_left]
  have hCC : r.compose rCat0 = rPG :=
    qreg_ext fun j ↦ by
      have hj : rCat0 j = Fin.natAdd kAct j := Fin.ext (by simp [rCat0])
      rw [QRegister.compose_apply, hj, QRegister.concat_apply_right]
  have hEW : r.embedMatrix W_cat.1 = (r.embedUnitary W_cat).1 :=
    (QRegister.embedUnitary_val r W_cat).symm
  have hEU : r.embedMatrix (rCat0.embedUnitary U_cat).1 = (rPG.embedUnitary U_cat).1 := by
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      hCC]
  have hEE : r.embedMatrix (rAct0.embedUnitary U_eff).1 = (rId.embedUnitary U_eff).1 := by
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      hCA]
  have hEP : r.embedMatrix (rCat0.basisOutcomeProjector 0) = rPG.basisOutcomeProjector 0 := by
    rw [embedMatrix_basisOutcomeProjector_zero_assoc, hCC]
  dsimp only [rAct0, rCat0] at hEU hEE hEP
  have e1 := congrArg r.embedMatrix hLoc.1
  have e2 := congrArg r.embedMatrix hLoc.2.1
  have e3 := congrArg r.embedMatrix hLoc.2.2
  simp only [QRegister.embedMatrix_mul, hEW, hEU, hEE, hEP] at e1 e2 e3
  exact ⟨e1, e2, e3⟩
theorem rIdInCoreSum42_wires_val_of_lt3924_assoc (i : Fin (3924 + 3)) (hi : i.val < 3924) :
    (rIdInCoreSum42.wires i).val = i.val := by
  have h : i = Fin.castAdd 3 ⟨i.val, hi⟩ := Fin.ext rfl
  change (rCoreInCoreSum42 80 (coreElecCosetB1Block pos24_6_le_80 i)).val = i.val
  rw [h, QRegister.concat_apply_left]
  simp [rCoreInCoreSum42, FullSysCatSegmentBridge.coreElecBlock]
open Classical in
theorem intertwinesCat_uStageA_on_catState48_zeroHyp {n : ℕ}
    (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14)))
    (rCS : QRegister (fullSysCoreWires 80 + 42) n) (rCat : QRegister 48 n)
    (hDisj : rCS.DisjointWires rCat) :
    let rPG7 := rCat.compose (rTopCatSlice 7 48 (singleCat_seven_le_of_48 le_rfl))
    let rAct := rCS.concat rPG7 (hDisj.compose_right _)
    let U48 := (rCat.embedUnitary (U_cat_B_normalized 48)).1
    let P48 := rCat.basisOutcomeProjector 0
    SpecsAux.PhaseGradCatalystCore.IntertwinesCat U48 P48
      (rAct.embedUnitary (uStageAInnerCat uSpec)).1 (rCS.embedUnitary (uStageAInnerEff uSpec)).1 ∧
    SpecsAux.PhaseGradCatalystCore.IntertwinesCat U48 P48
      (rAct.embedUnitary (uStageAInnerSwapCat uSpec)).1 (rCS.embedUnitary (uStageAInnerSwapEff
        uSpec)).1 ∧
    SpecsAux.PhaseGradCatalystCore.IntertwinesCat U48 P48
      (rAct.embedUnitary (uStageA5StepCat uSpec)).1 (rCS.embedUnitary (uStageA5StepEff uSpec)).1 ∧
    SpecsAux.PhaseGradCatalystCore.IntertwinesCat U48 P48
      (rAct.embedUnitary (uStageA7StepCat uSpec)).1 (rCS.embedUnitary (uStageA7StepEff uSpec)).1 ∧
    SpecsAux.PhaseGradCatalystCore.IntertwinesCat U48 P48
      (rAct.embedUnitary (uStageA7StepHoistCat uSpec)).1 (rCS.embedUnitary (uStageA7StepHoistEff
        uSpec)).1 := by
  have h4076_le : fullSysCoreWires 80 + 42 ≤ kCoreSum42PG7 := by
    rw [fullSysCoreWires80_eq_4034_assoc, kCoreSum42PG7_eq_4083_assoc]
    omega
  let rAct0 : QRegister (fullSysCoreWires 80 + 42) kCoreSum42PG7 :=
    .block 0 (fullSysCoreWires 80 + 42) h4076_le
  let rCat0 : QRegister 7 kCoreSum42PG7 := .block (fullSysCoreWires 80 + 42) 7 le_rfl
  have hDisj0 : rAct0.DisjointWires rCat0 := disjoint_block_sep (Or.inl (by omega))
  have hAct0Eq : QRegister.block 0 (fullSysCoreWires 80 + 42) h4076_le = selCoreSum42InAct := rfl
  have hPhiL : IntertwinesLocalCat (U_cat_B_normalized 7) uPhiHeldZ18Cat uPhiHeldZ18Eff := by
    have hSysLt : kHeldZ18Sys ≤ kHeldZ18Act := by
      rw [kHeldZ18Sys_eq_4094_assoc, kHeldZ18Act_eq_4101_assoc]
      omega
    let rSys0 : QRegister kHeldZ18Sys kHeldZ18Act := .block 0 kHeldZ18Sys hSysLt
    let rPG0 : QRegister 7 kHeldZ18Act := .block kHeldZ18Sys 7 le_rfl
    have hDisjS0 : rSys0.DisjointWires rPG0 := disjoint_block_sep (Or.inl (by omega))
    have hIdS : rSys0.concat rPG0 hDisjS0 = QRegExt.idReg kHeldZ18Act :=
      rActLoc_concat_rZLoc_eq_idReg kHeldZ18Sys 7
    have hSysEq : QRegister.block 0 kHeldZ18Sys hSysLt = selHeldZ18SysInAct := rfl
    have hStage (c : ℕ) (S : CanonStageSpec128) : IntertwinesLocalCat (U_cat_B_normalized 7)
        ((selHybridHeldZ18Cat c).embedUnitary S.uCat)
        ((selHybridHeldZ18Sys c).embedUnitary S.uEff) := by
      have hEmb := intertwinesCat_embed_concat_of_localCat
        (rSys0.compose (selHybridHeldZ18Sys c)) rPG0 (hDisjS0.compose_left _)
        (intertwinesLocalCat_canonStageSpec128_zeroHyp S).1
      have hCatEq : (rSys0.compose (selHybridHeldZ18Sys c)).concat rPG0 (hDisjS0.compose_left _) =
          selHybridHeldZ18Cat c := by
        rw [← concat_compose_selHybridHeldZ18Cat c rSys0 rPG0 hDisjS0, hIdS]
        rfl
      exact intertwinesCat_congr_ops hEmb (by rw [hCatEq])
        (by dsimp only [rSys0]; rw [← QRegister.embedUnitary_compose])
    have iSum := FullSysCatSegmentBridge.liftCleanCoreToTwistCat (U_cat_B_normalized 7)
      (selZ18Sum42InHeldZ18Sys.embedUnitary uPointSumClifford60)
    have iElec := FullSysCatSegmentBridge.liftCleanCoreToTwistCat (U_cat_B_normalized 7)
      (selCoreInHeldZ18Sys.embedUnitary uPointElec217Core)
    exact intertwinesCat_congr_ops
      (intertwinesCat_mul_gen iElec (intertwinesCat_mul_gen iSum
        (intertwinesCat_mul_gen (hStage 1 stagePointCrossExpC1)
          (intertwinesCat_mul_gen (hStage 2 stagePointCrossExpC2)
            (intertwinesCat_mul_gen (hStage 3 stagePointCrossExpC3)
              (intertwinesCat_mul_gen (hStage 4 stagePointCrossExpC4)
                (hStage 5 stagePointCrossExpC5)))))))
      (by unfold uPhiHeldZ18Cat
          rw [← hSysEq, QRegister.embedUnitary_compose, QRegister.embedUnitary_compose]
          simp only [unitary_coe_mul_assoc])
      (by unfold uPhiHeldZ18Eff; simp only [QRegister.embedUnitary_mul, unitary_coe_mul_assoc])
  have hInner : IntertwinesLocalCat (U_cat_B_normalized 7)
      (uStageAInnerCat uSpec) (uStageAInnerEff uSpec) := by
    obtain ⟨hCompA, hCompZ, hCompC, hCompCZ⟩ := selHeldZ18SysInFull_compositions
    let rActF := rActLoc kCoreSum42PG7 18
    let rZF := rZLoc kCoreSum42PG7 18
    let rSysF := selHeldZ18SysInFull
    let rPG7F := rPG7InFull
    have iPhi0 := intertwinesCat_embed_concat_of_localCat rSysF rPG7F
      selHeldZ18SysInFull_disj_rPG7InFull hPhiL
    have iPhiI0 := intertwinesCat_embed_concat_of_localCat rSysF rPG7F
      selHeldZ18SysInFull_disj_rPG7InFull (IntertwinesLocalCat.inv hPhiL)
    rw [selHeldZ18SysInFull_concat_rPG7InFull] at iPhi0 iPhiI0
    rw [QRegister.embedUnitary_inv, QRegister.embedUnitary_inv] at iPhiI0
    have mkSys (V : Unitary (2 ^ kHeldZ18Sys)) :
        IntertwinesCat (rPG7F.embedUnitary (U_cat_B_normalized 7)).1 (rPG7F.basisOutcomeProjector 0)
          (rSysF.embedUnitary V).1 (rSysF.embedUnitary V).1 :=
      IntertwinesCat.refl_of_comm
        (rSysF.embedMatrix_comm_of_disjoint rPG7F selHeldZ18SysInFull_disj_rPG7InFull V.1 _)
        ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rSysF) rPG7F
          selHeldZ18SysInFull_disj_rPG7InFull V.1 0)
    have mkSel {k : ℕ} {selSys : QRegister k kHeldZ18Sys} {selFull : QRegister k (kCoreSum42PG7 +
      18)}
        (hC : rSysF.compose selSys = selFull) (U : Unitary (2 ^ k)) :
        IntertwinesCat (rPG7F.embedUnitary (U_cat_B_normalized 7)).1 (rPG7F.basisOutcomeProjector 0)
          (selFull.embedUnitary U).1 (rSysF.embedUnitary (selSys.embedUnitary U)).1 :=
      intertwinesCat_congr_ops (mkSys (selSys.embedUnitary U))
        (by dsimp only [rSysF]; rw [← QRegister.embedUnitary_compose, hC]) rfl
    have iXor := mkSel hCompCZ uXorZTarget18
    have iStr := mkSel hCompA (uStr3AxisOfSpec uSpec)
    have iStrI := intertwinesCat_congr_ops (mkSel hCompA (uStr3AxisOfSpec uSpec)⁻¹)
      (by rw [QRegister.embedUnitary_inv]) (by rw [QRegister.embedUnitary_inv])
    have iHead := mkSel hCompC uHeadConjHCore
    have hFull : IntertwinesCat
        (rPG7F.embedUnitary (U_cat_B_normalized 7)).1 (rPG7F.basisOutcomeProjector 0)
        (uStageAInnerFullCat uSpec).1 (rSysF.embedUnitary (uStageAInnerSysEff uSpec)).1 :=
      intertwinesCat_congr_ops
        (intertwinesCat_mul_gen iXor (intertwinesCat_mul_gen iPhiI0
          (intertwinesCat_mul_gen iStr (intertwinesCat_mul_gen iHead
            (intertwinesCat_mul_gen iStrI (intertwinesCat_mul_gen iPhi0 iXor))))))
        (by unfold uStageAInnerFullCat; simp only [unitary_coe_mul_assoc])
        (by unfold uStageAInnerSysEff
            simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv,
              unitary_coe_mul_assoc])
    have hDisjSysZ : selCoreSum42InFull.DisjointWires rZF :=
      disj_of_val_ne fun i j ↦ by
        have := i.isLt
        simp only [selCoreSum42InFull, rZF, rZLoc, qreg_block_apply,
          fullSysCoreWires80_eq_4034_assoc, kCoreSum42PG7_eq_4083_assoc] at this ⊢
        omega
    have hSysConcat : selCoreSum42InFull.concat rZF hDisjSysZ = rSysF :=
      qreg_ext fun idx ↦ Fin.addCases
        (fun i ↦ by
          rw [QRegister.concat_apply_left, ← hCompA, QRegister.compose_apply]
          exact congrArg rSysF (Fin.ext (by simp [rActLoc])))
        (fun j ↦ by
          dsimp only [rZF]
          rw [QRegister.concat_apply_right, ← hCompZ, QRegister.compose_apply]
          exact congrArg rSysF (Fin.ext (by simp [rZLoc]))) idx
    have hRedCat : (uStageAInnerFullCat uSpec).1 * rZF.basisOutcomeProjector 0 =
        rActF.embedMatrix (uStageAInnerCat uSpec).1 * rZF.basisOutcomeProjector 0 := by
      have h0 := embedUnitary_extractCleanAncillaUnitary_mul_projZero rActF rZF
        (rActLoc_disj_rZLoc kCoreSum42PG7 18) (uStageAInnerFullCat uSpec)
          (uStageAInnerFullCat_comm_projZero uSpec)
      rwa [rActLoc_concat_rZLoc_eq_idReg kCoreSum42PG7 18, embedUnitary_idReg_eq] at h0
    have hRedEff : (rSysF.embedUnitary (uStageAInnerSysEff uSpec)).1 * rZF.basisOutcomeProjector 0 =
        rActF.embedMatrix (rAct0.embedUnitary (uStageAInnerEff uSpec)).1 *
          rZF.basisOutcomeProjector 0 := by
      have h0 := embedUnitary_extractCleanAncillaUnitary_mul_projZero selCoreSum42InFull rZF
        hDisjSysZ (uStageAInnerSysEff uSpec) (uStageAInnerSysEff_comm_projZero uSpec)
      have hCA : rActF.compose rAct0 = selCoreSum42InFull :=
        qreg_ext fun i ↦ Fin.ext (by simp [rActF, rActLoc, rAct0, selCoreSum42InFull])
      rw [hSysConcat] at h0
      rw [h0, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
        ← QRegister.embedMatrix_compose, hCA]
      rfl
    have hCC : rActF.compose rCat0 = rPG7F :=
      qreg_ext fun m ↦ Fin.ext (by simp [rActF, rActLoc, rCat0, rPG7F, rPG7InFull])
    have hU7 : (rPG7F.embedUnitary (U_cat_B_normalized 7)).1 =
        rActF.embedMatrix (rCat0.embedUnitary (U_cat_B_normalized 7)).1 := by
      rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
        hCC]
    have hP7 : rPG7F.basisOutcomeProjector 0 = rActF.embedMatrix (rCat0.basisOutcomeProjector 0) :=
      by
      rw [← hCC, embedMatrix_basisOutcomeProjector_zero_assoc]
    have hCommZ (X : Operator (2 ^ kCoreSum42PG7)) : rActF.embedMatrix X *
        rZF.basisOutcomeProjector 0 = rZF.basisOutcomeProjector 0 * rActF.embedMatrix X :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rActF) rZF (rActLoc_disj_rZLoc _
        _) X 0
    have absorbZ_comm (X : Operator (2 ^ kCoreSum42PG7))
        (he : (rSysF.embedUnitary (uStageAInnerSysEff uSpec)).1 * rActF.embedMatrix X =
          rActF.embedMatrix X * (rSysF.embedUnitary (uStageAInnerSysEff uSpec)).1) :
        (rAct0.embedUnitary (uStageAInnerEff uSpec)).1 * X =
          X * (rAct0.embedUnitary (uStageAInnerEff uSpec)).1 :=
      embedMatrix_eq_of_mul_projZero_block (kZ := 18) _ _ <| by
        calc rActF.embedMatrix ((rAct0.embedUnitary (uStageAInnerEff uSpec)).1 * X) *
          rZF.basisOutcomeProjector 0
            = (rActF.embedMatrix (rAct0.embedUnitary (uStageAInnerEff uSpec)).1 *
              rZF.basisOutcomeProjector 0) *
                rActF.embedMatrix X := by
              rw [QRegister.embedMatrix_mul, op_mul_assoc_assoc, hCommZ X, ← op_mul_assoc_assoc]
          _ = (rSysF.embedUnitary (uStageAInnerSysEff uSpec)).1 * rActF.embedMatrix X *
                rZF.basisOutcomeProjector 0 := by
              rw [← hRedEff, op_mul_assoc_assoc, ← hCommZ X, ← op_mul_assoc_assoc]
          _ = rActF.embedMatrix (X * (rAct0.embedUnitary (uStageAInnerEff uSpec)).1) *
                rZF.basisOutcomeProjector 0 := by
              rw [he, op_mul_assoc_assoc, hRedEff, QRegister.embedMatrix_mul, op_mul_assoc_assoc]
    refine ⟨embedMatrix_eq_of_mul_projZero_block (kZ := 18) _ _ ?_,
      absorbZ_comm _ (hU7 ▸ hFull.2.1), absorbZ_comm _ (hP7 ▸ hFull.2.2)⟩
    have e1 := congrArg (· * rZF.basisOutcomeProjector 0) hFull.1
    rw [hU7, hP7] at e1
    let U7 := rActF.embedMatrix (rCat0.embedUnitary (U_cat_B_normalized 7)).1
    let P7 := rActF.embedMatrix (rCat0.basisOutcomeProjector 0)
    let PZ := rZF.basisOutcomeProjector 0
    have hCommP7 : P7 * PZ = PZ * P7 := hCommZ _
    have hCommU7 : U7 * PZ = PZ * U7 := hCommZ _
    calc rActF.embedMatrix ((uStageAInnerCat uSpec).1 *
      (rCat0.embedUnitary (U_cat_B_normalized 7)).1 * rCat0.basisOutcomeProjector 0) * PZ
        = rActF.embedMatrix (uStageAInnerCat uSpec).1 * (U7 * (P7 * PZ)) := by
            rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul]
            dsimp only [U7, P7]
            simp only [op_mul_assoc_assoc]
      _ = (rActF.embedMatrix (uStageAInnerCat uSpec).1 * PZ) * U7 * P7 := by
            rw [hCommP7, ← op_mul_assoc_assoc U7 PZ P7, hCommU7]
            simp only [op_mul_assoc_assoc]
      _ = (uStageAInnerFullCat uSpec).1 * U7 * P7 * PZ := by
            rw [← hRedCat]
            simp only [op_mul_assoc_assoc]
            rw [← op_mul_assoc_assoc PZ U7 P7, ← hCommU7, op_mul_assoc_assoc U7 PZ P7, ← hCommP7]
      _ = U7 * ((rSysF.embedUnitary (uStageAInnerSysEff uSpec)).1 * PZ) * P7 := by
            rw [e1]
            simp only [op_mul_assoc_assoc]
            rw [hCommP7]
      _ = rActF.embedMatrix ((rCat0.embedUnitary (U_cat_B_normalized 7)).1 *
            (rAct0.embedUnitary (uStageAInnerEff uSpec)).1 * rCat0.basisOutcomeProjector 0) * PZ :=
              by
            rw [hRedEff, QRegister.embedMatrix_mul, QRegister.embedMatrix_mul]
            change U7 * (rActF.embedMatrix (rAct0.embedUnitary (uStageAInnerEff uSpec)).1 * PZ) *
              P7 =
              (U7 * rActF.embedMatrix (rAct0.embedUnitary (uStageAInnerEff uSpec)).1 * P7) * PZ
            simp only [op_mul_assoc_assoc]
            rw [← hCommP7]
  have iSw := FullSysCatSegmentBridge.liftCleanCoreToTwistCat (U_cat_B_normalized 7)
    ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967)
  have hSwap : IntertwinesLocalCat (U_cat_B_normalized 7)
      (uStageAInnerSwapCat uSpec) (uStageAInnerSwapEff uSpec) :=
    intertwinesCat_congr_ops (intertwinesCat_mul_gen (intertwinesCat_mul_gen iSw hInner) iSw)
      (by
        unfold uStageAInnerSwapCat; rw [← hAct0Eq, QRegister.embedUnitary_compose];
        simp only [unitary_coe_mul_assoc])
      (by unfold uStageAInnerSwapEff; simp only [QRegister.embedUnitary_mul, unitary_coe_mul_assoc])
  have hQ0Eff : rIdInCoreSum42.embedUnitary activeOneElecForestFullQftStage128.uEff =
      (rElec0InCoreSum42 80).embedUnitary uCoreHadamard18 := by
    have hEff : activeOneElecForestFullQftStage128.uEff =
        (DyadicQft64WalkCircuit.rElec18In654 0).embedUnitary uCoreHadamard18 := by
      have h0 := activeOneElecForestQftBundle128_uQft654_eq_rElec18In654_zero
      rwa [ForestQft117BundleNoTopBridge.activeOneElecForestQftBundle_uQft654 128 le_rfl] at h0
    have hComp : rIdInCoreSum42.compose (DyadicQft64WalkCircuit.rElec18In654 0) =
      rElec0InCoreSum42 80 := by
      refine qreg_ext fun i ↦ Fin.ext ?_
      have hi : i.val < 3924 := by have := i.isLt; omega
      have h18 : DyadicQft64WalkCircuit.rElec18In654 0 i = Fin.castAdd 3 ⟨i.val, hi⟩ :=
        Fin.ext (by simp [DyadicQft64WalkCircuit.rElec18In654])
      change (rCoreInCoreSum42 80 (coreElecCosetB1Block pos24_6_le_80
        (DyadicQft64WalkCircuit.rElec18In654 0 i))).val = _
      rw [h18, QRegister.concat_apply_left]
      simp [rCoreInCoreSum42, rElec0InCoreSum42]
    rw [hEff, ← QRegister.embedUnitary_compose, hComp]
  have hIdCS : rAct0.concat rCat0 hDisj0 = QRegExt.idReg kCoreSum42PG7 :=
    rActLoc_concat_rZLoc_eq_idReg (fullSysCoreWires 80 + 42) 7
  have hSelCatEq : (rAct0.compose rIdInCoreSum42).concat rCat0 (hDisj0.compose_left _) =
      selCatInCoreSum42PG7 := by
    rw [← concat_compose_selCatInCoreSum42PG7 rAct0 rCat0 hDisj0, hIdCS]
    rfl
  have iQ0 : IntertwinesLocalCat (U_cat_B_normalized 7)
      (selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat)
      ((rElec0InCoreSum42 80).embedUnitary uCoreHadamard18) :=
    intertwinesCat_congr_ops
      (intertwinesCat_embed_concat_of_localCat (rAct0.compose rIdInCoreSum42) rCat0
        (hDisj0.compose_left _) (intertwinesLocalCat_canonStageSpec128_zeroHyp
          activeOneElecExpQftStage128).1)
      (by rw [hSelCatEq])
      (by
        dsimp only [rAct0];
        rw [QRegister.embedUnitary_compose, activeOneElecExpQftStage128_uEff, hQ0Eff])
  have h5 : IntertwinesLocalCat (U_cat_B_normalized 7)
      (uStageA5StepCat uSpec) (uStageA5StepEff uSpec) :=
    intertwinesCat_congr_ops (intertwinesCat_mul_gen (IntertwinesLocalCat.inv iQ0)
      (intertwinesCat_mul_gen hSwap iQ0))
      (by unfold uStageA5StepCat; simp only [unitary_coe_mul_assoc])
      (by
        unfold uStageA5StepEff;
        simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv, unitary_coe_mul_assoc])
  have iAdd :=
    FullSysCatSegmentBridge.liftCleanCoreToTwistCat (U_cat_B_normalized 7) (uSlot0Sum42Add 80)
  have h7 : IntertwinesLocalCat (U_cat_B_normalized 7)
      (uStageA7StepCat uSpec) (uStageA7StepEff uSpec) :=
    intertwinesCat_congr_ops (intertwinesCat_mul_gen iAdd (intertwinesCat_mul_gen h5
      (IntertwinesLocalCat.inv iAdd)))
      (by dsimp only [uStageA7StepCat]; rw [← hAct0Eq]; simp only [unitary_coe_mul_assoc])
      (by
        unfold uStageA7StepEff;
        simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv, unitary_coe_mul_assoc])
  have iTr := FullSysCatSegmentBridge.liftCleanCoreToTwistCat (U_cat_B_normalized 7)
    ((rCoreInCoreSum42 80).embedUnitary uTrailCliffordXor80)
  have h7H : IntertwinesLocalCat (U_cat_B_normalized 7)
      (uStageA7StepHoistCat uSpec) (uStageA7StepHoistEff uSpec) :=
    intertwinesCat_congr_ops (intertwinesCat_mul_gen (IntertwinesLocalCat.inv iTr)
      (intertwinesCat_mul_gen h7 iTr))
      (by
        dsimp only [uStageA7StepHoistCat]; rw [← hAct0Eq, QRegister.embedUnitary_compose];
        simp only [unitary_coe_mul_assoc])
      (by
        unfold uStageA7StepHoistEff;
        simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv, unitary_coe_mul_assoc])
  have lift := fun W E hL ↦
    intertwinesCat_topCatSlice_of_localCat (singleCat_seven_le_of_48 le_rfl) rCS rCat hDisj W E hL
  exact ⟨lift _ _ hInner, lift _ _ hSwap, lift _ _ h5, lift _ _ h7, lift _ _ h7H⟩
/-- Target-only 3-axis phase entry `∏ w, omega128 (- pointTargetOnlyExp128 (bitRev6
  (headTargetCoord64 β w)))`
on `kHeldZ18Sys`. -/
noncomputable def targetOnlyInvEntrySys (x : Fin (2 ^ kHeldZ18Sys)) : ℂ := ∏ w : Fin 3,
    omega128 (- pointTargetOnlyExp128 (bitRev6 (headTargetCoord64 (basisBits posCoreWires
    (selCoreInHeldZ18Sys.extractIndex x)) w)))
open Classical in
theorem uPhiHeldZ18Eff_mul_pZMatchSys_mul_pStream217 :
    let rA := rActLoc (fullSysCoreWires 80 + 42) 18
    let P217 := rA.embedMatrix (pStream217Core 80)
    let C := selCoreInHeldZ18Sys.embedUnitary uControlledPointDiag217
    uPhiHeldZ18Eff.1 * (pZMatchSys * P217) =
      Matrix.diagonal targetOnlyInvEntrySys * C.1 * (pZMatchSys * P217) := by
  intro rA P217 C
  have hP217Diag : P217 = Matrix.diagonal fun x ↦
      if ∀ w : Fin 3,
        regVal (rSum14InCoreSum42 80 w) (basisBits (fullSysCoreWires 80 + 42) (rA.extractIndex x)) =
          spectatorSum217 w (fun q ↦
            basisBits (fullSysCoreWires 80 + 42) (rA.extractIndex x) (rCoreInCoreSum42 80 q))
      then 1 else 0 := QRegister.embedMatrix_diagonal rA _
  have hCDiag : C.1 = Matrix.diagonal (fun x ↦
    controlledPointDiag217Entry (selCoreInHeldZ18Sys.extractIndex x)) :=
    QRegister.embedMatrix_diagonal selCoreInHeldZ18Sys controlledPointDiag217Entry
  rw [uPhiHeldZ18Eff_eq_diagonal, pZMatchSys, hP217Diag, hCDiag]
  simp only [diagonal_mul_diagonal_op_assoc]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  dsimp only [pZMatchSysEntry]
  by_cases hZ : (rZLoc (fullSysCoreWires 80 + 42) 18).extractIndex x =
      headTargetPoint18 (basisBits posCoreWires (selCoreInHeldZ18Sys.extractIndex x))
  · by_cases hS : ∀ w : Fin 3,
        regVal (rSum14InCoreSum42 80 w) (basisBits (fullSysCoreWires 80 + 42) (rA.extractIndex x)) =
          spectatorSum217 w (fun q ↦
            basisBits (fullSysCoreWires 80 + 42) (rA.extractIndex x) (rCoreInCoreSum42 80 q))
    · rw [ite_eq_left hZ, ite_eq_left hS]
      simp only [mul_one]
      unfold targetOnlyInvEntrySys controlledPointDiag217Entry
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun w _ ↦ ?_
      let ξ := basisBits kHeldZ18Sys x
      let βCore := basisBits posCoreWires (selCoreInHeldZ18Sys.extractIndex x)
      let z_w : Fin 64 := ⟨bitsVal (fun q : Fin 6 ↦
        ξ ⟨(fullSysCoreWires 80 + 42) + (6 * w.val + q.val),
        zWire_lt_kHeldZ18Sys w q⟩), bitsVal_lt_two_pow _⟩
      let s_w : Fin 128 := ⟨bitsVal (fun k : Fin 7 ↦ ξ ⟨fullSysCoreWires 80 + (14 * w.val + k.val),
        sWire_lt_kHeldZ18Sys w k⟩), bitsVal_lt_two_pow _⟩
      let u_w : Fin 217 → Fin 64 := fun e ↦
        u18GridEquiv ((rSpectatorSlot e).extractIndex (selCoreInHeldZ18Sys.extractIndex x)) w
      have hw18 : 6 * w.val + 6 ≤ 18 := by have := w.isLt; omega
      have hz_eq : z_w = bitRev6 (headTargetCoord64 βCore w) := by
        have h1 : z_w = (QRegister.block (6 * w.val) 6 hw18).extractIndex
            ((rZLoc (fullSysCoreWires 80 + 42) 18).extractIndex x) := Fin.ext <| by
          rw [← bitsVal_basisBits6 ((QRegister.block (6 * w.val) 6 hw18).extractIndex _)]
          exact congrArg bitsVal (funext fun q ↦ by
            rw [basisBits_extractIndex_assoc, basisBits_extractIndex_assoc]
            exact congrArg ξ (Fin.ext (by simp [rZLoc])))
        rw [h1, hZ, block6_extractIndex_u18 w hw18, u18GridEquiv_headTargetPoint18]
      have hs_val : (∑ e : Fin 217, (u_w e).val) % 128 = s_w.val := by
        have hu_eq (e : Fin 217) : (u_w e).val =
            regVal (rElecSlotAxis (QRegExt.idReg _) e.succ w)
              (fun q ↦
                basisBits (fullSysCoreWires 80 + 42) (rA.extractIndex x) (rCoreInCoreSum42 80 q)) :=
                by
          dsimp only [u_w]
          rw [← bitsVal_basisBits6, ← block6_extractIndex_u18 w hw18]
          unfold regVal
          refine congrArg bitsVal (funext fun q ↦ ?_)
          dsimp only []
          rw [basisBits_extractIndex_assoc, basisBits_extractIndex_assoc,
            basisBits_extractIndex_assoc, basisBits_extractIndex_assoc]
          refine congrArg ξ (Fin.ext ?_)
          have h1 :=
            PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ ⟨6 * w.val + q.val, by omega⟩
          have := e.isLt
          have := w.isLt
          have := q.isLt
          simp [selCoreInHeldZ18Sys, rA, rActLoc, rCoreInCoreSum42, rSpectatorSlot,
            rElecSlotAxis,
            QRegister.slice, QRegister.compose, QRegExt.idReg, h1]
          omega
        let r14 := rSum14InCoreSum42 80 w
        let ξA := basisBits (fullSysCoreWires 80 + 42) (rA.extractIndex x)
        have hSumEq : ∑ e : Fin 217, (u_w e).val = regVal r14 ξA :=
          (Finset.sum_congr rfl fun e _ ↦ hu_eq e).trans (hS w).symm
        have hSplit : regVal r14 ξA = bitsVal (fun k : Fin 7 ↦ ξA (r14 (Fin.castAdd 7 k))) +
            128 * ∑ b : Fin 7, (ξA (r14 (Fin.natAdd 7 b))).val * 2 ^ b.val := by
          change (∑ idx : Fin (7 + 7), (ξA (r14 idx)).val * 2 ^ idx.val) = _
          rw [Fin.sum_univ_add, Finset.mul_sum]
          exact congrArg (_ + ·) (Finset.sum_congr rfl fun b _ ↦ by
            rw [show (Fin.natAdd 7 b).val = 7 + b.val from rfl, Nat.pow_add]
            ring)
        have h7lt : bitsVal (fun k : Fin 7 ↦ ξA (r14 (Fin.castAdd 7 k))) < 128 :=
          bitsVal_lt_two_pow _
        rw [hSumEq, hSplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h7lt]
        change bitsVal _ = bitsVal _
        refine congrArg bitsVal (funext fun k ↦ ?_)
        dsimp only [ξA, r14]
        rw [basisBits_extractIndex_assoc]
        exact congrArg ξ (Fin.ext (by
          simp [rA, rActLoc, rSum14InCoreSum42]
          omega))
      have hCoord04c :
          TrailXorAndRepairedStageAExactEq.headTargetCoord64 βCore w =
            headTargetCoord64 βCore w := rfl
      have hOm := omega128_sum_217_pointAxisPhaseExp128_eq_of_rSum7 z_w u_w s_w hs_val
      dsimp only [ξ, βCore, z_w, s_w, u_w] at hCoord04c hz_eq hOm ⊢
      rw [hCoord04c, ← hz_eq, hOm]
      calc omega128 (pointCrossXorExp128 z_w s_w) * omega128 (pointSumCliffordExp128 z_w s_w) *
              omega128 (∑ e : Fin 217, pointElecCliffordExp128 (u_w e))
          = 1 * (omega128 (pointCrossXorExp128 z_w s_w) *
            omega128 (pointSumCliffordExp128 z_w s_w) *
              omega128 (∑ e : Fin 217, pointElecCliffordExp128 (u_w e))) := (one_mul _).symm
        _ = (omega128 (- pointTargetOnlyExp128 z_w) * omega128 (pointTargetOnlyExp128 z_w)) *
              (omega128 (pointCrossXorExp128 z_w s_w) * omega128 (pointSumCliffordExp128 z_w s_w) *
                omega128 (∑ e : Fin 217, pointElecCliffordExp128 (u_w e))) := by
              rw [← omega128_add (- pointTargetOnlyExp128 z_w) (pointTargetOnlyExp128 z_w),
                neg_add_cancel, omega128_zero]
        _ = omega128 (- pointTargetOnlyExp128 z_w) *
              (omega128 (pointCrossXorExp128 z_w s_w) * omega128 (pointTargetOnlyExp128 z_w) *
                omega128 (pointSumCliffordExp128 z_w s_w) *
                omega128 (∑ e : Fin 217, pointElecCliffordExp128 (u_w e))) := by ring
    · rw [ite_eq_left hZ, ite_eq_right hS]
      simp only [mul_zero]
  · rw [ite_eq_right hZ]
    simp only [mul_zero, zero_mul]

open Classical in
theorem uXorSys_comm_rActLoc_embedMatrix_of_preserves_target
    (M : Operator (2 ^ (fullSysCoreWires 80 + 42))) (hTgt : ∀ a b : Fin (2 ^
    (fullSysCoreWires 80 + 42)), M a b ≠ 0 → headTargetPoint18 (basisBits posCoreWires
    (((rCoreInCoreSum42 80).compose selPosCoreInCore80).extractIndex a)) = headTargetPoint18
    (basisBits posCoreWires (((rCoreInCoreSum42 80).compose selPosCoreInCore80).extractIndex
    b))) : (rActLoc (fullSysCoreWires 80 + 42) 18).embedMatrix M *
    (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 =
    (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 *
    (rActLoc (fullSysCoreWires 80 + 42) 18).embedMatrix M := by
  let kAct := fullSysCoreWires 80 + 42
  let rA := rActLoc kAct 18
  let rCP := (rCoreInCoreSum42 80).compose selPosCoreInCore80
  ext x y
  have hEx (w : Fin (2 ^ kHeldZ18Sys)) : rA.extractIndex (fXorSys w) = rA.extractIndex w :=
    extractIndex_eq_of_basisBits_eq_assoc rA fun i ↦
      basisBits_fXorSys_of_not_mem w fun ⟨k, hk⟩ ↦ (rActLoc_disj_rZLoc kAct 18).ne i k hk.symm
  have hCompCP : rA.compose rCP = selCoreInHeldZ18Sys :=
    qreg_ext fun i ↦ Fin.ext (by
      simp [selCoreInHeldZ18Sys, rA, rActLoc, rCP, rCoreInCoreSum42,
        selPosCoreInCore80])
  have hCore (w : Fin (2 ^ kHeldZ18Sys)) :
      selCoreInHeldZ18Sys.extractIndex w = rCP.extractIndex (rA.extractIndex w) := by
    rw [← hCompCP, QRegister.extractIndex_compose]
  have hL : (rA.embedMatrix M * (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1) x y =
      (rA.embedMatrix M) x (fXorSys y) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (fXorSys y)
      (fun b _ hb ↦ by rw [uXorSys_apply_assoc, ite_eq_right hb, mul_zero])
      (fun h0 ↦ (h0 (Finset.mem_univ _)).elim), uXorSys_apply_assoc, ite_eq_left rfl, mul_one]
  have hR : ((selPosCoreZ18InSys.embedUnitary uXorZTarget18).1 * rA.embedMatrix M) x y =
      (rA.embedMatrix M) (fXorSys x) y := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (fXorSys x)
      (fun b _ hb ↦ by
        rw [uXorSys_apply_assoc,
          ite_eq_right (fun h ↦ hb (by rw [← fXorSys_involutive b, ← h])), zero_mul])
      (fun h0 ↦ (h0 (Finset.mem_univ _)).elim), uXorSys_apply_assoc,
      ite_eq_left (fXorSys_involutive x).symm, one_mul]
  rw [hL, hR, rA.embedMatrix_apply_of_agreeOutside, rA.embedMatrix_apply_of_agreeOutside, hEx, hEx]
  by_cases hM0 : M (rA.extractIndex x) (rA.extractIndex y) = 0
  · simp [hM0]
  · have hT := hTgt (rA.extractIndex x) (rA.extractIndex y) hM0
    have hSwap : ∀ a b c : ZMod 2, (a = b + c) ↔ (a + c = b) := by decide
    have hBitIff (q : Fin kHeldZ18Sys) (hq : q ∉ Set.range rA.wires) :
        (basisBits kHeldZ18Sys x q = basisBits kHeldZ18Sys (fXorSys y) q) ↔
          (basisBits kHeldZ18Sys (fXorSys x) q = basisBits kHeldZ18Sys y q) := by
      have hge : ¬ q.val < kAct := fun hlt ↦
        hq ⟨⟨q.val, hlt⟩, Fin.ext (by simp [rA, rActLoc])⟩
      let k : Fin 18 := ⟨q.val - kAct, by
        have := q.isLt
        dsimp [kHeldZ18Sys, kAct] at this ⊢
        omega⟩
      have hqZ : rZLoc (fullSysCoreWires 80 + 42) 18 k = q :=
        Fin.ext (by
          have := q.isLt
          simp [rZLoc, k, kAct]
          omega)
      rw [← hqZ, basisBits_fXorSys_rZ, basisBits_fXorSys_rZ, hCore, hCore]
      dsimp only [rCP] at hT ⊢
      rw [hT]
      exact hSwap _ _ _
    have hAgIff : rA.AgreeOutside x (fXorSys y) ↔ rA.AgreeOutside (fXorSys x) y :=
      ⟨fun h q hq ↦ (hBitIff q hq).mp (h q hq), fun h q hq ↦ (hBitIff q hq).mpr (h q hq)⟩
    by_cases hAg : rA.AgreeOutside x (fXorSys y)
    · rw [ite_eq_left hAg, ite_eq_left (hAgIff.mp hAg)]
    · rw [ite_eq_right hAg, ite_eq_right (mt hAgIff.mpr hAg)]

open InterWalkRSum42Hoist (rAct0 rSum0 rCoreFull rCoreOrig hAct0_disj_Sum0)
theorem unitary_comm_proj_of_intertwines_isometry {N : ℕ} (U V : Unitary N) (E P : Operator N)
    (hUV : U.1 * E = E * V.1) (hEP : E * Eᴴ = P) : U.1 * P = P * U.1 := by
  have hUVStar : (U.1 * E)ᴴ = (E * V.1)ᴴ := congrArg (·ᴴ) hUV
  rw [op_conjTranspose_mul_assoc, op_conjTranspose_mul_assoc] at hUVStar
  have hUU : U.1ᴴ * U.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp U.2
  have hVV : V.1 * V.1ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp V.2
  calc U.1 * P
      = U.1 * (E * Eᴴ) * (U.1ᴴ * U.1) := by rw [hEP, hUU, op_mul_one_assoc]
    _ = (U.1 * E) * (Eᴴ * U.1ᴴ) * U.1 := by simp only [op_mul_assoc_assoc]
    _ = (E * V.1) * (V.1ᴴ * Eᴴ) * U.1 := by rw [hUV, hUVStar]
    _ = (E * (V.1 * V.1ᴴ) * Eᴴ) * U.1 := by simp only [op_mul_assoc_assoc]
    _ = P * U.1 := by rw [hVV, op_mul_one_assoc, hEP]

open Classical in
theorem embedCoreSub_comm_eStream217Core {kSub : ℕ}
    (rSub : QRegister kSub (fullSysCoreWires 80)) (U : Unitary (2 ^ kSub))
    (hNonSpec : ∀ k : Fin kSub, (rSub k).val < 18 ∨ 3924 ≤ (rSub k).val) :
    ((rCoreInCoreSum42 80).embedUnitary (rSub.embedUnitary U)).1 * eStream217Core =
      eStream217Core * ((rCoreInCoreSum42 80).embedUnitary (rSub.embedUnitary U)).1 := by
  let r := (rCoreInCoreSum42 80).compose rSub
  let uAx (w : Fin 3) := ((selCoreSum14In42 80 w).embedUnitary
    ((selSpec217InCoreSum14 80).embedUnitary (uStream217Spec131 w))).1
  have hrVal (k : Fin kSub) : (r k).val = (rSub k).val := by
    simp [r, rCoreInCoreSum42]
  rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
    ← uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core]
  have hP0 : r.embedMatrix U.1 * pSum42CoreZero = pSum42CoreZero * r.embedMatrix U.1 := by
    unfold pSum42CoreZero
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint r) _ (disj_of_val_ne fun k j ↦
      by
      have := (rSub k).isLt
      simp only [hrVal, rZLoc, qreg_block_apply]
      omega) U.1 0
  have hAx (w : Fin 3) : r.embedMatrix U.1 * uAx w = uAx w * r.embedMatrix U.1 := by
    obtain ⟨hvSpec, hvSum⟩ := selCoreSum14_compose_selSpec217_val_assoc w
    dsimp only [uAx]
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
    refine r.embedMatrix_comm_of_disjoint _ (disj_of_val_ne fun k idx ↦ ?_) U.1 _
    have hk := hNonSpec k
    have hkLt := (rSub k).isLt
    rw [hrVal, QRegister.compose_apply]
    refine Fin.addCases (fun iSpec ↦ ?_) (fun jSum ↦ ?_) idx
    · rw [hvSpec iSpec]
      have := iSpec.isLt
      omega
    · rw [hvSum jSum]
      omega
  unfold uStr3AxisOfSpec
  simp only [unitary_coe_mul_assoc]
  exact (comm_mul_assoc (comm_mul_assoc (comm_mul_assoc (hAx 2).symm (hAx 1).symm) (hAx 0).symm)
    hP0.symm).symm

theorem selCatInCoreSum42PG7_wires_val_ne_mid_assoc (idx : Fin ((3924 + 3) + 7)) {w : ℕ}
    (hlo : 3924 ≤ w) (hhi : w < 3954) : (selCatInCoreSum42PG7.wires idx).val ≠ w := by
  let rAct0 := rActLoc (fullSysCoreWires 80 + 42) 7
  let rCat0 := rZLoc (fullSysCoreWires 80 + 42) 7
  have hDisj0 := rActLoc_disj_rZLoc (fullSysCoreWires 80 + 42) 7
  have hSelCatEq : (rAct0.compose rIdInCoreSum42).concat rCat0 (hDisj0.compose_left _) =
      selCatInCoreSum42PG7 := by
    rw [← concat_compose_selCatInCoreSum42PG7 rAct0 rCat0 hDisj0, rActLoc_concat_rZLoc_eq_idReg]
    rfl
  rw [← hSelCatEq]
  change (((rAct0.compose rIdInCoreSum42).concat rCat0 (hDisj0.compose_left _)) idx).val ≠ w
  refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) idx
  · rw [QRegister.concat_apply_left]
    refine Fin.addCases (fun iEl ↦ ?_) (fun iCo ↦ ?_) i
    · have hv := rIdInCoreSum42_wires_val_of_lt3924_assoc (Fin.castAdd 3 iEl) iEl.isLt
      simp [rAct0, rActLoc, QRegister.compose,
        hv]
      omega
    · have := iCo.isLt
      change (rAct0 (rCoreInCoreSum42 80 (coreElecCosetB1Block pos24_6_le_80 (Fin.natAdd 3924
        iCo)))).val ≠ w
      rw [coreElecCosetB1Block, QRegister.concat_apply_right]
      simp [rAct0, rActLoc, rCoreInCoreSum42, FullSysCatSegmentBridge.coreCosetB1Block]
      omega
  · rw [QRegister.concat_apply_right]
    have := m.isLt
    simp [rCat0, rZLoc, fullSysCoreWires80_eq_4034_assoc]
    omega
attribute [local semireducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
  PosSlots24BranchConcrete.posCoreWires
open Classical in
theorem uStageAInnerEff_mul_eStream217Core (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14)))
    (hE : (uStr3AxisOfSpec uSpec).1 * pSum42CoreZero = eStream217Core) :
    (uStageAInnerEff uSpec).1 * eStream217Core = eStream217Core * ((rCoreInCoreSum42
    80).embedUnitary (selPosCoreInCore80.embedUnitary ((uControlledPointDiag217)⁻¹ *
    uHeadConjHCore * uControlledPointDiag217))).1 := by
  rw [← QRegister.embedUnitary_compose]
  let kCS := fullSysCoreWires 80 + 42
  let rA : QRegister kCS kHeldZ18Sys := rActLoc kCS 18
  let rZ : QRegister 18 kHeldZ18Sys := rZLoc kCS 18
  let PZ : Operator (2 ^ kHeldZ18Sys) := rZ.basisOutcomeProjector 0
  let U_core : Unitary (2 ^ posCoreWires) :=
    (uControlledPointDiag217)⁻¹ * uHeadConjHCore * uControlledPointDiag217
  let rCP := (rCoreInCoreSum42 80).compose selPosCoreInCore80
  let U_cs : Unitary (2 ^ kCS) := rCP.embedUnitary U_core
  let E : Operator (2 ^ kHeldZ18Sys) := rA.embedMatrix eStream217Core
  let P217 : Operator (2 ^ kHeldZ18Sys) := rA.embedMatrix (pStream217Core 80)
  let P0 : Operator (2 ^ kHeldZ18Sys) := rA.embedMatrix pSum42CoreZero
  let uXor : Operator (2 ^ kHeldZ18Sys) := (selPosCoreZ18InSys.embedUnitary uXorZTarget18).1
  let uStr : Operator (2 ^ kHeldZ18Sys) := (rA.embedUnitary (uStr3AxisOfSpec uSpec)).1
  let uStrI : Operator (2 ^ kHeldZ18Sys) := ((rA.embedUnitary (uStr3AxisOfSpec uSpec))⁻¹).1
  let C : Operator (2 ^ kHeldZ18Sys) := (selCoreInHeldZ18Sys.embedUnitary uControlledPointDiag217).1
  let CI : Operator (2 ^ kHeldZ18Sys) :=
    ((selCoreInHeldZ18Sys.embedUnitary uControlledPointDiag217)⁻¹).1
  let H : Operator (2 ^ kHeldZ18Sys) := (selCoreInHeldZ18Sys.embedUnitary uHeadConjHCore).1
  let D_inv : Operator (2 ^ kHeldZ18Sys) := Matrix.diagonal targetOnlyInvEntrySys
  have hInvE := inv_uStr3AxisOfSpec_mul_eStream217Core_eq_pSum42CoreZero uSpec hE
  have hStrIE : uStrI * E = P0 := by
    dsimp only [uStrI, E, P0]
    rw [← QRegister.embedUnitary_inv, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
      hInvE]
  have hStrP0 : uStr * P0 = E := by
    dsimp only [uStr, E, P0]
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hE]
  have hP217E : P217 * E = E := by
    dsimp only [P217, E]
    rw [← QRegister.embedMatrix_mul, pStream217Core_mul_eStream217Core]
  have hXorSq : uXor * uXor = 1 :=
    unitary_val_mul_self_eq_one_assoc (by
      rw [← QRegister.embedUnitary_mul, uXorZTarget18_mul_self, QRegister.embedUnitary_one])
  have hXorPZ : uXor * PZ = pZMatchSys * uXor := by
    calc uXor * PZ = (uXor * PZ * uXor) * uXor := by
            rw [op_mul_assoc_assoc, op_mul_assoc_assoc, hXorSq, op_mul_one_assoc]
      _ = pZMatchSys * uXor := by rw [uXorSys_conj_projZero_eq_pZMatchSys]
  have hPZXor : uXor * pZMatchSys = PZ * uXor := by
    calc uXor * pZMatchSys = uXor * (uXor * PZ * uXor) := by
            rw [← uXorSys_conj_projZero_eq_pZMatchSys]
      _ = (uXor * uXor) * PZ * uXor := by simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = PZ * uXor := by rw [hXorSq, op_one_mul_assoc]
  have hAZComm (M : Operator (2 ^ kCS)) : rA.embedMatrix M * PZ = PZ * rA.embedMatrix M := by
    dsimp only [PZ, QRegister.basisOutcomeProjector]
    exact rA.embedMatrix_comm_of_disjoint rZ (rActLoc_disj_rZLoc kCS 18) M _
  have hComp : rA.compose rCP = selCoreInHeldZ18Sys := by
    apply qreg_ext
    intro i
    ext
    simp [rA, rActLoc, rCP, rCoreInCoreSum42, selPosCoreInCore80, selCoreInHeldZ18Sys]
  have hCP {a b : Fin (2 ^ kCS)} (hne : eStream217Core a b ≠ 0) :
      rCP.extractIndex a = rCP.extractIndex b := by
    rw [eStream217Core, eStream42CoreOf, streamProjOpGen_apply_assoc] at hne
    have hEqIdx : (rActLoc (fullSysCoreWires 80) 42).extractIndex a =
        (rActLoc (fullSysCoreWires 80) 42).extractIndex b := by
      by_contra hna
      rw [ite_neg_assoc (fun h ↦ hna h.1)] at hne
      exact hne rfl
    refine extractIndex_eq_of_basisBits_eq_assoc rCP fun i ↦ ?_
    have h1 := congrArg (fun z ↦ basisBits (fullSysCoreWires 80) z (selPosCoreInCore80 i)) hEqIdx
    simpa [rActLoc, rCP, rCoreInCoreSum42, qreg_block_apply, basisBits_extractIndex_assoc] using h1
  have hEXor : E * uXor = uXor * E :=
    uXorSys_comm_rActLoc_embedMatrix_of_preserves_target eStream217Core fun _ _ hne ↦ by
      rw [hCP hne]
  have hUcsXor : rA.embedMatrix U_cs.1 * uXor = uXor * rA.embedMatrix U_cs.1 := by
    refine uXorSys_comm_rActLoc_embedMatrix_of_preserves_target U_cs.1 fun a b hne ↦ ?_
    let g : Fin (2 ^ posCoreWires) → ℂ := fun c ↦
      ((headTargetPoint18 (basisBits posCoreWires c)).val : ℂ)
    have hH : uHeadConjHCore.1 * Matrix.diagonal g = Matrix.diagonal g * uHeadConjHCore.1 :=
      uHeadConjHCore_comm_diagonal_of_target fun _ _ hT ↦
        congrArg (fun p : Fin (2 ^ 18) ↦ (p.val : ℂ)) (headTargetPoint18_congr_assoc hT)
    have hC1 : uControlledPointDiag217.1 * Matrix.diagonal g = Matrix.diagonal g *
      uControlledPointDiag217.1 := by
      dsimp only [uControlledPointDiag217]
      exact diagonal_comm_op_assoc _ _
    have hUg : U_core.1 * Matrix.diagonal g = Matrix.diagonal g * U_core.1 := by
      dsimp only [U_core]
      simp -zeta -zetaDelta only [unitary_coe_mul_assoc]
      exact comm_mul_assoc (comm_mul_assoc (unitary_val_inv_comm_of_comm uControlledPointDiag217
        hC1) hH) hC1
    have hUcsG : U_cs.1 * Matrix.diagonal (fun z ↦ g (rCP.extractIndex z)) =
        Matrix.diagonal (fun z ↦ g (rCP.extractIndex z)) * U_cs.1 := by
      have hd := QRegister.embedMatrix_diagonal rCP g
      dsimp only [U_cs]
      rw [← hd, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hUg,
        QRegister.embedMatrix_mul]
    have hEntry := congrFun (congrFun hUcsG a) b
    rw [op_mul_diagonal_assoc, op_diagonal_mul_assoc, mul_comm (U_cs.1 a b)] at hEntry
    exact Fin.ext (Nat.cast_injective (mul_right_cancel₀ hne hEntry).symm)
  have hCDiag : C = Matrix.diagonal (fun x ↦
    controlledPointDiag217Entry (selCoreInHeldZ18Sys.extractIndex x)) :=
    QRegister.embedMatrix_diagonal selCoreInHeldZ18Sys controlledPointDiag217Entry
  have hCE : C * E = E * C := by
    have hd : (rCP.embedUnitary uControlledPointDiag217).1 =
        Matrix.diagonal (fun z ↦ controlledPointDiag217Entry (rCP.extractIndex z)) :=
      QRegister.embedMatrix_diagonal rCP controlledPointDiag217Entry
    have hCE0 : (rCP.embedUnitary uControlledPointDiag217).1 * eStream217Core =
        eStream217Core * (rCP.embedUnitary uControlledPointDiag217).1 := by
      rw [hd]
      refine Matrix.ext fun a b ↦ ?_
      rw [op_diagonal_mul_assoc, op_mul_diagonal_assoc]
      by_cases hne : eStream217Core a b = 0
      · simp only [hne, mul_zero, zero_mul]
      · rw [hCP hne, mul_comm]
    dsimp only [C, E]
    rw [← hComp, QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, hCE0, QRegister.embedMatrix_mul]
  have hCIE : CI * E = E * CI :=
    unitary_val_inv_comm_of_comm (selCoreInHeldZ18Sys.embedUnitary uControlledPointDiag217) hCE
  have ⟨hStrD, hStrID, hHD⟩ : uStr * D_inv = D_inv * uStr ∧
      uStrI * D_inv = D_inv * uStrI ∧ H * D_inv = D_inv * H :=
    uStr_and_uHead_comm_diagonal uSpec targetOnlyInvEntrySys fun _ _ hT _ ↦ by
      unfold targetOnlyInvEntrySys
      rw [hT]
  have ⟨hStrPZ, hStrIPZ, hHPZ⟩ : uStr * pZMatchSys = pZMatchSys * uStr ∧
      uStrI * pZMatchSys = pZMatchSys * uStrI ∧ H * pZMatchSys = pZMatchSys * H :=
    uStr_and_uHead_comm_pZMatchSys uSpec
  change uStr * D_inv = D_inv * uStr at hStrD
  change uStrI * D_inv = D_inv * uStrI at hStrID
  change H * D_inv = D_inv * H at hHD
  change uStr * pZMatchSys = pZMatchSys * uStr at hStrPZ
  change uStrI * pZMatchSys = pZMatchSys * uStrI at hStrIPZ
  change H * pZMatchSys = pZMatchSys * H at hHPZ
  have hPZE : pZMatchSys * E = E * pZMatchSys := by
    have hP0PZ : P0 * pZMatchSys = pZMatchSys * P0 := by
      dsimp only [P0, pSum42CoreZero, pZMatchSys]
      rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.embedMatrix_diagonal]
      exact diagonal_comm_op_assoc _ _
    rw [← hStrP0]
    exact (comm_mul_assoc hStrPZ hP0PZ).symm
  have hHP0 : H * P0 = P0 * H := by
    dsimp only [H, P0, pSum42CoreZero, QRegister.basisOutcomeProjector]
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose]
    refine selCoreInHeldZ18Sys.embedMatrix_comm_of_disjoint _ (disj_of_val_ne fun i j ↦ ?_) _ _
    intro hv
    have hi : i.val < 4034 := i.isLt
    have h1 : (selCoreInHeldZ18Sys.wires i).val = 0 + i.val := rfl
    have h2 : ((rA.compose (rZLoc (fullSysCoreWires 80) 42)).wires j).val =
        0 + (fullSysCoreWires 80 + j.val) := rfl
    rw [h1, h2, fullSysCoreWires80_eq_4034_assoc] at hv
    omega
  have hPhiF : uPhiHeldZ18Eff.1 * (pZMatchSys * P217) = D_inv * C * (pZMatchSys * P217) :=
    uPhiHeldZ18Eff_mul_pZMatchSys_mul_pStream217
  obtain ⟨d217, hP217Diag⟩ : ∃ d217 : Fin (2 ^ kHeldZ18Sys) → ℂ, P217 = Matrix.diagonal d217 := by
    dsimp only [P217, pStream217Core, StageAPointPhase128OnStep.pStream42Of]
    exact ⟨_, QRegister.embedMatrix_diagonal rA _⟩
  have hCCommP : C * (pZMatchSys * P217) = (pZMatchSys * P217) * C := by
    rw [hCDiag, pZMatchSys, hP217Diag]
    simp -zeta -zetaDelta only [diagonal_mul_diagonal_op_assoc]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  have hDPComm : D_inv * pZMatchSys * P217 = (pZMatchSys * P217) * D_inv := by
    dsimp only [D_inv, pZMatchSys]
    rw [hP217Diag]
    simp -zeta -zetaDelta only [diagonal_mul_diagonal_op_assoc]
    exact congrArg Matrix.diagonal (funext fun _ ↦ (mul_assoc _ _ _).trans (mul_comm _ _))
  have hPhiInvCancel : (uPhiHeldZ18Eff⁻¹).1 * ((pZMatchSys * P217) * D_inv) =
      pZMatchSys * P217 * CI := by
    have hCCI : C * CI = 1 := (selCoreInHeldZ18Sys.embedUnitary uControlledPointDiag217).2.2
    have hPhiL : (uPhiHeldZ18Eff⁻¹).1 * uPhiHeldZ18Eff.1 = 1 := uPhiHeldZ18Eff.2.1
    have hRHS : uPhiHeldZ18Eff.1 * (pZMatchSys * P217 * CI) = (pZMatchSys * P217) * D_inv := by
      calc uPhiHeldZ18Eff.1 * (pZMatchSys * P217 * CI)
          = (uPhiHeldZ18Eff.1 * (pZMatchSys * P217)) * CI := by
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
        _ = D_inv * (C * (pZMatchSys * P217)) * CI := by
            rw [hPhiF]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
        _ = (D_inv * pZMatchSys * P217) * (C * CI) := by
            rw [hCCommP]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
        _ = (pZMatchSys * P217) * D_inv := by rw [hCCI, op_mul_one_assoc, hDPComm]
    rw [← hRHS, ← op_mul_assoc_assoc, hPhiL, op_one_mul_assoc]
  have hUcsEmb : CI * (H * C) = rA.embedMatrix U_cs.1 := by
    have h1 : selCoreInHeldZ18Sys.embedUnitary U_core = rA.embedUnitary U_cs := by
      dsimp only [U_cs]
      rw [← QRegister.embedUnitary_compose, hComp]
    have h2 : (selCoreInHeldZ18Sys.embedUnitary U_core).1 = CI * (H * C) := by
      dsimp only [U_core, CI, H, C]
      rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, QRegister.embedUnitary_inv]
      simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
    rw [← h2, h1, QRegister.embedUnitary_val]
  refine embedMatrix_eq_of_mul_projZero_block (kZ := 18) _ _ ?_
  have hExtPZ : (uStageAInnerSysEff uSpec).1 * PZ = (rA.embedUnitary (uStageAInnerEff uSpec)).1 *
    PZ := by
    have h := embedUnitary_extractCleanAncillaUnitary_mul_projZero rA rZ (rActLoc_disj_rZLoc kCS 18)
      (uStageAInnerSysEff uSpec) (uStageAInnerSysEff_comm_projZero uSpec)
    rwa [rActLoc_concat_rZLoc_eq_idReg kCS 18, embedUnitary_idReg_eq] at h
  have hStep1 : uXor * (E * PZ) = (pZMatchSys * P217) * E * uXor := by
    calc uXor * (E * PZ) = (uXor * E) * PZ := (op_mul_assoc_assoc _ _ _).symm
      _ = E * (uXor * PZ) := by rw [← hEXor, op_mul_assoc_assoc]
      _ = (E * pZMatchSys) * uXor := by rw [hXorPZ, op_mul_assoc_assoc]
      _ = (pZMatchSys * P217) * E * uXor := by
          rw [← hPZE]
          nth_rw 1 [← hP217E]
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
  have hStep2 : uPhiHeldZ18Eff.1 * ((pZMatchSys * P217) * E * uXor) = D_inv * pZMatchSys * E * C *
    uXor := by
    calc uPhiHeldZ18Eff.1 * ((pZMatchSys * P217) * E * uXor)
        = (uPhiHeldZ18Eff.1 * (pZMatchSys * P217)) * E * uXor := by
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = D_inv * (C * (pZMatchSys * P217)) * E * uXor := by
          rw [hPhiF]
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = D_inv * pZMatchSys * P217 * (C * E) * uXor := by
          rw [hCCommP]
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = D_inv * pZMatchSys * (P217 * E) * C * uXor := by
          rw [hCE]
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = D_inv * pZMatchSys * E * C * uXor := by rw [hP217E]
  have hStep345 : uStr * (H * (uStrI * (D_inv * pZMatchSys * E * C * uXor))) =
      ((pZMatchSys * P217) * D_inv) * E * (H * C) * uXor := by
    have h3 : uStrI * (D_inv * pZMatchSys * E * C * uXor) = D_inv * pZMatchSys * P0 * C * uXor := by
      calc uStrI * (D_inv * pZMatchSys * E * C * uXor)
          = (uStrI * D_inv) * pZMatchSys * E * C * uXor := by
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
        _ = D_inv * (uStrI * pZMatchSys) * E * C * uXor := by
            rw [hStrID]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
        _ = D_inv * pZMatchSys * (uStrI * E) * C * uXor := by
            rw [hStrIPZ]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
        _ = D_inv * pZMatchSys * P0 * C * uXor := by rw [hStrIE]
    have h4 : H * (D_inv * pZMatchSys * P0 * C * uXor) = D_inv * pZMatchSys * P0 * (H * C) * uXor :=
      by
      calc H * (D_inv * pZMatchSys * P0 * C * uXor)
          = (H * D_inv) * pZMatchSys * P0 * C * uXor := by
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
        _ = D_inv * (H * pZMatchSys) * P0 * C * uXor := by
            rw [hHD]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
        _ = D_inv * pZMatchSys * (H * P0) * C * uXor := by
            rw [hHPZ]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
        _ = D_inv * pZMatchSys * P0 * (H * C) * uXor := by
            rw [hHP0]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    rw [h3, h4]
    calc uStr * (D_inv * pZMatchSys * P0 * (H * C) * uXor)
        = (uStr * D_inv) * pZMatchSys * P0 * (H * C) * uXor := by
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = D_inv * (uStr * pZMatchSys) * P0 * (H * C) * uXor := by
          rw [hStrD]
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = D_inv * pZMatchSys * (uStr * P0) * (H * C) * uXor := by
          rw [hStrPZ]
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = (D_inv * pZMatchSys * P217) * E * (H * C) * uXor := by
          rw [hStrP0]
          nth_rw 1 [← hP217E]
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = ((pZMatchSys * P217) * D_inv) * E * (H * C) * uXor := by rw [hDPComm]
  have hStep6 : (uPhiHeldZ18Eff⁻¹).1 * (((pZMatchSys * P217) * D_inv) * E * (H * C) * uXor) =
      pZMatchSys * E * rA.embedMatrix U_cs.1 * uXor := by
    calc (uPhiHeldZ18Eff⁻¹).1 * (((pZMatchSys * P217) * D_inv) * E * (H * C) * uXor)
        = ((uPhiHeldZ18Eff⁻¹).1 * ((pZMatchSys * P217) * D_inv)) * E * (H * C) * uXor := by
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = pZMatchSys * P217 * (CI * E) * (H * C) * uXor := by
            rw [hPhiInvCancel]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = pZMatchSys * (P217 * E) * (CI * (H * C)) * uXor := by
            rw [hCIE]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = pZMatchSys * E * rA.embedMatrix U_cs.1 * uXor := by rw [hP217E, hUcsEmb]
  calc rA.embedMatrix ((uStageAInnerEff uSpec).1 * eStream217Core) * PZ
      = (uStageAInnerSysEff uSpec).1 * (E * PZ) := by
          rw [QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val, op_mul_assoc_assoc,
            hAZComm eStream217Core, ← op_mul_assoc_assoc, ← hExtPZ, op_mul_assoc_assoc,
              ← hAZComm eStream217Core]
    _ = uXor * ((uPhiHeldZ18Eff⁻¹).1 * (uStr * (H * (uStrI * (uPhiHeldZ18Eff.1 * (uXor * (E *
      PZ))))))) := by
          unfold uStageAInnerSysEff
          dsimp only [uXor, uStr, uStrI, H, rA, kCS]
          simp -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
    _ = uXor * (pZMatchSys * E * rA.embedMatrix U_cs.1 * uXor) := by
          rw [hStep1, hStep2, hStep345, hStep6]
    _ = (uXor * pZMatchSys) * E * (rA.embedMatrix U_cs.1 * uXor) := by
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = PZ * (uXor * E) * (uXor * rA.embedMatrix U_cs.1) := by
          rw [hPZXor, hUcsXor]
          simp -zetaDelta only [op_mul_assoc_assoc]
    _ = PZ * E * (uXor * uXor) * rA.embedMatrix U_cs.1 := by
          rw [← hEXor]
          simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = rA.embedMatrix (eStream217Core * U_cs.1) * PZ := by
          rw [hXorSq, op_mul_one_assoc, ← hAZComm eStream217Core, op_mul_assoc_assoc,
            ← hAZComm U_cs.1, ← op_mul_assoc_assoc, ← QRegister.embedMatrix_mul]
open Classical in
theorem uSwapCore3967_comm_eStream217Core :
    ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1 * eStream217Core =
      eStream217Core * ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1 := by
  rw [uSwapCore3967_eq_embed_rHigh110]
  refine embedCoreSub_comm_eStream217Core rHigh110InCoreFA _ fun k ↦ Or.inr ?_
  have h1 : (rHigh110InCoreFA.wires k).val = 3924 + k.val := rfl
  change 3924 ≤ (rHigh110InCoreFA.wires k).val
  omega
open Classical in
theorem rCSFull_uStageA7StepEff_mul_E_rawStream42
    (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14)))
    (hE : (uStr3AxisOfSpec uSpec).1 * pSum42CoreZero = eStream217Core) :
    let rCSFull := rCoreFull.concat rSum0 (hAct0_disj_Sum0.compose_left rCoreOrig)
    let Q := fullSysQftCoreUnitary pos24_6_le_80 coreQftHadamardPrunedBundle128
    (rCSFull.embedUnitary (uStageA7StepEff uSpec)).1 * E_rawStream42 =
      E_rawStream42 * (rCoreFull.embedUnitary (unitaryConj Q uHeadPhase80Mod4Eff)).1 := by
  intro rCSFull Q
  have conjComm {L M R1 R2 : Unitary (2 ^ (fullSysCoreWires 80 + 42))}
      (hL : L.1 * eStream217Core = eStream217Core * L.1)
      (hR : R2.1 * eStream217Core = eStream217Core * R2.1)
      (hM : M.1 * eStream217Core = eStream217Core * R1.1) :
      (L * (M * R2)).1 * eStream217Core = eStream217Core * (L * R1 * R2).1 := by
    simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
    rw [hR, ← op_mul_assoc_assoc M.1, hM, op_mul_assoc_assoc eStream217Core,
      ← op_mul_assoc_assoc L.1, hL, op_mul_assoc_assoc]
  let uSw := (rCoreInCoreSum42 80).embedUnitary uSwapCore3967
  let U_core := (uControlledPointDiag217)⁻¹ * uHeadConjHCore * uControlledPointDiag217
  have hSwap : (uStageAInnerSwapEff uSpec).1 * eStream217Core =
      eStream217Core * (uSw *
        (rCoreInCoreSum42 80).embedUnitary (selPosCoreInCore80.embedUnitary U_core) * uSw).1 := by
    unfold uStageAInnerSwapEff
    dsimp only [uSw]
    rw [unitary_mul_assoc_assoc _ (uStageAInnerEff uSpec) _]
    exact conjComm uSwapCore3967_comm_eStream217Core uSwapCore3967_comm_eStream217Core
      (uStageAInnerEff_mul_eStream217Core uSpec hE)
  let uQ0 := (rElec0InCoreSum42 80).embedUnitary uCoreHadamard18
  have hQ0CommE : uQ0.1 * eStream217Core = eStream217Core * uQ0.1 := by
    have hComp : (rCoreInCoreSum42 80).compose (rElec18InCore pos24_6_le_80 0) =
      rElec0InCoreSum42 80 := by
      apply qreg_ext
      intro q
      ext
      simp [rCoreInCoreSum42, rElec0InCoreSum42,
        ZeroHypStageABToUFoldedPass123SegAndCompac.rElec18InCore_apply_val]
    dsimp only [uQ0]
    rw [← hComp, QRegister.embedUnitary_compose]
    refine embedCoreSub_comm_eStream217Core (rElec18InCore pos24_6_le_80 0) uCoreHadamard18 fun k ↦
      Or.inl ?_
    have := k.isLt
    change (rElec18InCore pos24_6_le_80 0 k).val < 18
    rw [ZeroHypStageABToUFoldedPass123SegAndCompac.rElec18InCore_apply_val]
    omega
  have hQ0Eq : (rElec0InCoreSum42 80).embedUnitary uCoreHadamard18 =
      (rCoreInCoreSum42 80).embedUnitary (selPosCoreInCore80.embedUnitary uQft0) := by
    unfold uQft0
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
    congr 1
    apply qreg_ext
    intro q
    ext
    simp [rCoreInCoreSum42, selPosCoreInCore80, rElec0InCore, rElec0InCoreSum42]
  have hQ0Sw : selPosCoreInCore80.embedUnitary uQft0 * uSwapCore3967 =
      uSwapCore3967 * selPosCoreInCore80.embedUnitary uQft0 := by
    have hr0 : selPosCoreInCore80.compose rElec0InCore = rElec18InCore pos24_6_le_80 0 := by
      apply qreg_ext
      intro q
      ext
      simp [selPosCoreInCore80, rElec0InCore,
        ZeroHypStageABToUFoldedPass123SegAndCompac.rElec18InCore_apply_val]
    unfold uQft0
    rw [← QRegister.embedUnitary_compose, hr0, uSwapCore3967_eq_embed_rHigh110]
    exact embedUnitary_comm_of_disjoint_local _ _ (rElec18InCore80_disj_rHigh110 0) _ _
  have hCoreEq : (selPosCoreInCore80.embedUnitary uQft0)⁻¹ *
      ((uSwapCore3967 * selPosCoreInCore80.embedUnitary U_core) * uSwapCore3967) *
      selPosCoreInCore80.embedUnitary uQft0 = unitaryConj Q uHeadPhase80Mod4Eff := by
    rw [unitaryConj_qftCore_and_QC_uHeadPhase80Mod4Eff_eq_zeroHyp.1]
    calc (selPosCoreInCore80.embedUnitary uQft0)⁻¹ *
            ((uSwapCore3967 * selPosCoreInCore80.embedUnitary U_core) * uSwapCore3967) *
            selPosCoreInCore80.embedUnitary uQft0
        = ((selPosCoreInCore80.embedUnitary uQft0)⁻¹ * uSwapCore3967) *
            selPosCoreInCore80.embedUnitary U_core *
            (uSwapCore3967 * selPosCoreInCore80.embedUnitary uQft0) := by
              simp -zeta -zetaDelta only [unitary_mul_assoc_assoc]
      _ = (uSwapCore3967 *
            ((selPosCoreInCore80.embedUnitary uQft0)⁻¹ *
              selPosCoreInCore80.embedUnitary U_core *
              selPosCoreInCore80.embedUnitary uQft0)) * uSwapCore3967 := by
            rw [unitary_inv_comm_of_comm hQ0Sw, ← hQ0Sw]
            simp -zeta -zetaDelta only [unitary_mul_assoc_assoc]
      _ = _ := by
            rw [← QRegister.embedUnitary_inv, ← QRegister.embedUnitary_mul,
              ← QRegister.embedUnitary_mul]
            rfl
  have h5 : (uStageA5StepEff uSpec).1 * eStream217Core =
      eStream217Core * ((rCoreInCoreSum42 80).embedUnitary (unitaryConj Q uHeadPhase80Mod4Eff)).1 :=
        by
    unfold uStageA5StepEff
    dsimp only [uQ0]
    refine (conjComm (unitary_val_inv_comm_of_comm uQ0 hQ0CommE) hQ0CommE hSwap).trans
      (congrArg (fun U : Unitary _ ↦ eStream217Core * U.1) ?_)
    dsimp only [uQ0, uSw]
    rw [hQ0Eq, ← QRegister.embedUnitary_inv]
    simp -zeta -zetaDelta only [← QRegister.embedUnitary_mul]
    exact congrArg (rCoreInCoreSum42 80).embedUnitary hCoreEq
  have h7 : (uStageA7StepEff uSpec).1 * eStream218Core =
      eStream218Core * ((rCoreInCoreSum42 80).embedUnitary (unitaryConj Q uHeadPhase80Mod4Eff)).1 :=
        by
    let uAdd0 := uSlot0Sum42Add 80
    calc (uStageA7StepEff uSpec).1 * eStream218Core
        = uAdd0.1 * ((uStageA5StepEff uSpec).1 * ((uAdd0⁻¹).1 * eStream218Core)) := by
            unfold uStageA7StepEff
            dsimp only [uAdd0]
            simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
      _ = (uAdd0.1 * eStream217Core) *
            ((rCoreInCoreSum42 80).embedUnitary (unitaryConj Q uHeadPhase80Mod4Eff)).1 := by
            rw [uSlot0Sum42Sub_mul_eStream218Core, h5, op_mul_assoc_assoc]
      _ = eStream218Core *
            ((rCoreInCoreSum42 80).embedUnitary (unitaryConj Q uHeadPhase80Mod4Eff)).1 := by
            rw [uSlot0Sum42Add_mul_eStream217Core]
  have hrComp : rCSFull.compose (rCoreInCoreSum42 80) = rCoreFull := by
    apply qreg_ext
    intro i
    have hi : rCoreInCoreSum42 80 i = Fin.castAdd 42 i :=
      Fin.ext (by simp [rCoreInCoreSum42])
    rw [QRegister.compose_apply, hi, QRegister.concat_apply_left]
  have hCS : rCSFull.embedMatrix eStream218Core = E_rawStream42 :=
    rCSFull_embedMatrix_eStream218Core_eq_E_rawStream42
  rw [← hCS, ← hrComp,
    QRegister.embedUnitary_compose, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
    ← QRegister.embedMatrix_mul, h7, QRegister.embedMatrix_mul]
end StageAConjHAndStreamBridge
end SharedScope
end SlimFermApproxSec3B

noncomputable section SlimFermApproxSec4AndStream218

section
set_option maxRecDepth 262144
set_option exponentiation.threshold 8192
section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
attribute [-instance] littleWedderburn Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroK5 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
local instance (priority := 1000000) instGroupUnitaryFastAlt (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFastAlt (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open Circuit hiding TOFF
open scoped Matrix BigOperators
namespace StageAConjHAndStreamBridge
noncomputable section ImplAlt
open HermitianMat LocalClassicalPerm
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror OctahedralOrbit
open Dyadic128CoulombMath
open CanonRank7Circuit
open ZeroAncillaUSP (omega8)
open HoistedSwapSelectBridge (unitaryConj)
open CoreQftHadamard140And160 (CanonStageSpec128)
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires disjointWires_concat_left)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (rTopCatSlice)
open SingleCatClosure (singleCat_seven_le_of_48)
open StreamingBchComparator PosSlots24BranchConcrete
open PosSlots24SemanticBridge (pos24_6_le_80)
open PosPostPrep80MergedVep (uSwapCore3967)
open PosHeadMod4_15476
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open QRegExt
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open Barrel3PassSelectStitch (rCat80)
open StageAPosHeadConjugatedCircuit (rSpectatorSlot elecProd217 uHad217)
open TwistStreamEliminationAux (spectatorSum217)
open Slot0SubAdd14And217Stream (rSum14Slice42 uSlot0Sum42Add)
open StageAPointPhase128OnStep (hL3_le_654 rCoreInCoreSum42 rSum14InCoreSum42)
open FullConcrete7StepAndTrueSwapSelect (kCoreSum42PG7 selCoreSum42InAct selCatInCoreSum42PG7)
open DoubleDutyFoldedRealizesBridge (selPosCoreInCore80)
open ForestQft117BundleNoTopBridge (pStream217Core pStream218Core)
open BoothOpt_06_Stream217ZeroSave0Width128 (selSpec217InCoreSum14 selCoreSum14In42
  uStream217Spec131)
open DyadicQft64WalkCircuit (disjoint_block_sep)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open HeldRSum42TwistQftPass2Stitch (rAxisPrefix axisProdPrefix stageHPrefixCanonStage128)
open FullSysCatSegmentBridge (fullSysQftCoreUnitary)
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside)
open PosPostPrep80MergedVep (wCore3967 wCore4029 swapCore3967Fn uSwapCore3967_mulVec_ket
  uSwapCore3967_mul_self)
open NuclearTwistRealizes (embedUnitary_idReg_eq)
open InterWalkRSum42Hoist (E_rawStream42 pSum42Zero)
open StageAPosHeadConjugatedCircuit (uHadamard18)
open Slot0SubAdd14And217Stream (slot0AxisVal uSlot0AxisAdd14)
open ZeroHypCatState48StageABMidCoreReductionAn (catState48)
open ZeroHypStageABToUFoldedPass123SegAndCompac (uHeadPhase80Mod4Eff rElec0InCoreSum42)
open ZeroHypLHSStageAB7Step3StepCatState48Proje (rIdInCoreSum42 concat_compose_selCatInCoreSum42PG7)
section Part4_RawFull80AndUncondCounts
attribute [local semireducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
  PosSlots24BranchConcrete.posCoreWires
open InterWalkRSum42Hoist (kFull80 rAct0 rCoreOrig rSegOrig rPG48Orig rSegFull rCoreFull rPG48Full
  rSum0 hAct0_disj_Sum0 E_rawStream42 pSum42Zero)
open Barrel3PassSelectStitch (rCoreSeg hCoreSeg_disj_Cat80)
open PosMomSelectSandwich (slotBitProj)
open PosPostPrep80MergedVep (uSwapCore3967_comm_slotBitProj op_comm_mul3)
open Leaf4Ext48TopStitch (CommutesWithReg disj_of_val_ne rCoreFull_disj_rSum0 rCoreFull_val_eq
  rSum0_val_eq rPG48Full_val_eq rPGIdle rPGIdle_val_eq rPGIdleOrig rUnusedCtrl3Full
  rUnusedCtrl3Full_val_eq)
open SelectHoistLemmas (rCtrl3InSeg pCoinSlack010Core pCoinSlack010Seg
  rSegFull_eq_rAct0_compose_rSegOrig)
open SelectExtStitch (rSegFull_compose_rCoreSeg_eq)
open DoubleDutyFoldedRealizesBridge (rPG7Full rPG7Full_val_eq hCoreFull_disj_rPG7Full
  rSum0_disj_rPG7Full)
open StageBCachedSwapAndRawCancelBridge (seg_mul_catState48_eq_of_intertwineRaw
  seg_mul_pCoinSlack010Seg_eq_of_intertwineRaw commutesWithReg_rCtrl3InSeg_of_intertwineRaw
  commutesWithReg_rPGIdleOrig12_of_intertwineRaw)
def rCSFull80 : QRegister (fullSysCoreWires 80 + 42) kFull80 :=
  rCoreFull.concat rSum0 (hAct0_disj_Sum0.compose_left rCoreOrig)
theorem hCSFull80_disj_rPG7Full : rCSFull80.DisjointWires rPG7Full :=
  disjointWires_concat_left _ hCoreFull_disj_rPG7Full rSum0_disj_rPG7Full
/-- Active `kCoreSum42PG7` register `(rCoreFull ++ rSum0) ++ rPG7Full` inside `kFull80` for Stage
  A. -/
def rActStageAFull80 : QRegister kCoreSum42PG7 kFull80 :=
  rCSFull80.concat rPG7Full hCSFull80_disj_rPG7Full
/-- Full-width (`kFull80`) raw catalyzed 7-step Stage-A unitary (`149w` zero-`rSave0`
  217-stream). -/
noncomputable def uStageARawFull : Unitary (2 ^ kFull80) :=
  rActStageAFull80.embedUnitary (uStageA7StepCat uStream217Spec131)
theorem preservesOutside_mono_assoc {k m N : ℕ} (rSub : QRegister k N) (rBig : QRegister m N)
    (hSub : ∀ i : Fin k, rSub i ∈ Set.range rBig.wires) {M : Operator (2 ^ N)}
    (hM : PreservesOutside rSub M) : PreservesOutside rBig M := fun x y hne q hq ↦ hM x y hne
    q fun ⟨i, hi⟩ ↦ hq (hi ▸ hSub i)
open Classical in
theorem preservesOutside_embedMatrix_of_range_subset_assoc {k m N : ℕ} (rSub : QRegister k N)
    (rBig : QRegister m N) (hSub : ∀ i : Fin k, rSub i ∈ Set.range rBig.wires)
    (A : Operator (2 ^ k)) : PreservesOutside rBig (rSub.embedMatrix A) := by
  intro x y hne
  rw [QRegister.embedMatrix_apply_of_agreeOutside] at hne
  by_cases hOut : rSub.AgreeOutside x y
  · exact fun q hq ↦ hOut q fun ⟨i, hi⟩ ↦ hq (hi ▸ hSub i)
  · rw [ite_eq_right hOut, mul_zero] at hne; exact False.elim (hne rfl)
open Classical in
theorem selCatInCoreSum42PG7_expQft_comm_high18Diag_assoc
    (d : Fin (2 ^ (fullSysCoreWires 80 + 42)) → ℂ)
    (hd : ∀ a b : Fin (2 ^ (fullSysCoreWires 80 + 42)),
      (rElec0InCoreSum42 80).AgreeOutside a b → d a = d b) :
    let uQ0 := selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat
    let D := selCoreSum42InAct.embedMatrix (Matrix.diagonal d)
    uQ0.1 * D = D * uQ0.1 ∧ (uQ0⁻¹).1 * D = D * (uQ0⁻¹).1 := by
  intro uQ0 D
  have h4076_le : fullSysCoreWires 80 + 42 ≤ kCoreSum42PG7 := by
    rw [fullSysCoreWires80_eq_4034_assoc, kCoreSum42PG7_eq_4083_assoc]; omega
  let rAct0CS : QRegister (fullSysCoreWires 80 + 42) kCoreSum42PG7 :=
    .block 0 (fullSysCoreWires 80 + 42) h4076_le
  let rCat0 : QRegister 7 kCoreSum42PG7 := .block (fullSysCoreWires 80 + 42) 7 le_rfl
  have hDisj0 : rAct0CS.DisjointWires rCat0 := disjoint_block_sep (Or.inl (by omega))
  let rE0Act : QRegister 18 kCoreSum42PG7 := rAct0CS.compose (rElec0InCoreSum42 80)
  have hDisjE0Cat : rE0Act.DisjointWires rCat0 := hDisj0.compose_left (rElec0InCoreSum42 80)
  let rE0PG7 : QRegister (18 + 7) kCoreSum42PG7 := rE0Act.concat rCat0 hDisjE0Cat
  have hIdCS : rAct0CS.concat rCat0 hDisj0 = QRegExt.idReg kCoreSum42PG7 := by
    apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      apply Fin.ext
      change 0 + i.val = i.val
      omega
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [rCat0, QRegExt.idReg])
  have hSelCatEq : (rAct0CS.compose rIdInCoreSum42).concat rCat0 (hDisj0.compose_left _) =
      selCatInCoreSum42PG7 := by
    rw [← concat_compose_selCatInCoreSum42PG7 rAct0CS rCat0 hDisj0, hIdCS]
    rfl
  have hCatSub : ∀ m : Fin 7, rCat0 m ∈ Set.range rE0PG7.wires := fun m ↦
    ⟨Fin.natAdd 18 m, by rw [QRegister.concat_apply_right]⟩
  have hCross0 := preservesOutside_stagePointCrossExp (rAct0CS.compose rIdInCoreSum42) rCat0
    (hDisj0.compose_left _)
  rw [hSelCatEq] at hCross0
  obtain ⟨hP5, hP4, hP3, hP2, hP1⟩ := hCross0
  have hStageH : ∀ kf : Fin 6, PreservesOutside rE0PG7 (selCatInCoreSum42PG7.embedUnitary
      (stageHPrefixCanonStage128 3 hL3_le_654 kf).uCat).1 := by
    intro kf
    change PreservesOutside rE0PG7 (selCatInCoreSum42PG7.embedUnitary
      (DyadicQft64WalkCircuit.rIdInCat.embedUnitary
      (HeldRSum42TwistQftPass2Stitch.axisProdPrefix 3 hL3_le_654 (fun _ ↦
      DyadicQft64Engine.wireHadamard6 kf)))).1
    have hIdComp : selCatInCoreSum42PG7.compose DyadicQft64WalkCircuit.rIdInCat =
        rAct0CS.compose rIdInCoreSum42 := by
      rw [← hSelCatEq]
      exact DyadicQft64WalkCircuit.concat_compose_rIdInCat
        (rAct0CS.compose rIdInCoreSum42) rCat0 _
    rw [← QRegister.embedUnitary_compose, hIdComp]
    have hAxis : ∀ a : Fin 3, PreservesOutside rE0PG7 ((rAct0CS.compose
        rIdInCoreSum42).embedUnitary
        ((HeldRSum42TwistQftPass2Stitch.rAxisPrefix 3 hL3_le_654
        a).embedUnitary (DyadicQft64Engine.wireHadamard6 kf))).1 := by
      intro a
      rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
      refine preservesOutside_embedMatrix_of_range_subset_assoc _ rE0PG7 (fun q ↦ ?_) _
      have ha := a.isLt; have hq := q.isLt
      refine ⟨Fin.castAdd 7 ⟨6 * a.val + q.val, by omega⟩, ?_⟩
      rw [QRegister.concat_apply_left]
      apply Fin.ext
      have hAxVal : (HeldRSum42TwistQftPass2Stitch.rAxisPrefix 3 hL3_le_654 a q).val =
          6 * a.val + q.val := by
        simp [HeldRSum42TwistQftPass2Stitch.rAxisPrefix,
          DyadicQft64WalkCircuit.rAxis654]
      have hLt3924 : (HeldRSum42TwistQftPass2Stitch.rAxisPrefix 3 hL3_le_654 a q).val < 3924 := by
        rw [hAxVal]; omega
      have hL : (rE0Act ⟨6 * a.val + q.val, by omega⟩).val = 0 + (0 + (6 * a.val + q.val)) := rfl
      have hR : (rAct0CS (rIdInCoreSum42 (HeldRSum42TwistQftPass2Stitch.rAxisPrefix 3 hL3_le_654 a
        q))).val =
          0 + (rIdInCoreSum42 (HeldRSum42TwistQftPass2Stitch.rAxisPrefix 3 hL3_le_654 a q)).val :=
            rfl
      change (rE0Act ⟨6 * a.val + q.val, by omega⟩).val =
        (rAct0CS (rIdInCoreSum42 (HeldRSum42TwistQftPass2Stitch.rAxisPrefix 3 hL3_le_654 a q))).val
      rw [hL, hR, rIdInCoreSum42_wires_val_of_lt3924_assoc _ hLt3924, hAxVal]
      omega
    dsimp only [HeldRSum42TwistQftPass2Stitch.axisProdPrefix]
    rw[List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
        List.prod_cons, List.prod_cons, List.prod_nil, mul_one, QRegister.embedUnitary_mul,
        QRegister.embedUnitary_mul, unitary_coe_mul_assoc, unitary_coe_mul_assoc]
    exact preservesOutside_mul (hAxis 0) (preservesOutside_mul (hAxis 1) (hAxis 2))
  have hSeq : ∀ (A B : CanonStageSpec128),
      PreservesOutside rE0PG7 (selCatInCoreSum42PG7.embedUnitary A.uCat).1 →
      PreservesOutside rE0PG7 (selCatInCoreSum42PG7.embedUnitary B.uCat).1 →
      PreservesOutside rE0PG7 (selCatInCoreSum42PG7.embedUnitary (A.seq B).uCat).1 := by
    intro A B hA hB
    change PreservesOutside rE0PG7 (selCatInCoreSum42PG7.embedUnitary (B.uCat * A.uCat)).1
    rw [QRegister.embedUnitary_mul, unitary_coe_mul_assoc]
    exact preservesOutside_mul hB hA
  have hPres : PreservesOutside rE0PG7 uQ0.1 := by
    change PreservesOutside rE0PG7
      (selCatInCoreSum42PG7.embedUnitary rawActiveOneElecExpQftStage128.uCat).1
    unfold rawActiveOneElecExpQftStage128
    exact hSeq _ _ (hSeq _ _ (hStageH 5) (preservesOutside_mono_assoc _ _ hCatSub hP5)) (hSeq _
      _ (hSeq _ _ (hStageH 4) (preservesOutside_mono_assoc _ _ hCatSub hP4)) (hSeq _ _ (hSeq _
      _ (hStageH 3) (preservesOutside_mono_assoc _ _ hCatSub hP3)) (hSeq _ _ (hSeq _ _ (hStageH
      2) (preservesOutside_mono_assoc _ _ hCatSub hP2)) (hSeq _ _ (hSeq _ _ (hStageH 1)
      (preservesOutside_mono_assoc _ _ hCatSub hP1)) (hStageH 0)))))
  have hDDiag : D = Matrix.diagonal (fun x ↦ d (selCoreSum42InAct.extractIndex x)) :=
    embedMatrix_diagonal_local selCoreSum42InAct d
  have hComm : uQ0.1 * D = D * uQ0.1 := by
    rw [hDDiag]
    refine preservesOutside_comm_diagonal hPres _ fun x y hOut ↦ hd _ _ fun q hq ↦ ?_
    rw [basisBits_extractIndex_assoc selCoreSum42InAct,
      basisBits_extractIndex_assoc selCoreSum42InAct]
    refine hOut (selCoreSum42InAct q) fun ⟨idx, hidx⟩ ↦ ?_
    revert hidx
    refine Fin.addCases (fun i hi ↦ hq ⟨i, ?_⟩) (fun m hm ↦ ?_) idx
    · dsimp only [rE0PG7] at hi
      rw [QRegister.concat_apply_left] at hi
      have hv := congrArg Fin.val hi
      have h1 : (rE0Act i).val = 0 + (rElec0InCoreSum42 80 i).val := rfl
      have h2 : (selCoreSum42InAct q).val = 0 + q.val := rfl
      rw [h1, h2] at hv
      exact Fin.ext (by omega)
    · dsimp only [rE0PG7] at hm
      rw [QRegister.concat_apply_right] at hm
      have hv := congrArg Fin.val hm
      have hqLt := q.isLt
      have h1 : (rCat0 m).val = (fullSysCoreWires 80 + 42) + m.val := rfl
      have h2 : (selCoreSum42InAct q).val = 0 + q.val := rfl
      rw [h1, h2] at hv
      omega
  exact ⟨hComm, unitary_val_inv_comm_of_comm uQ0 hComm⟩
theorem conj_comm_of_conj_eq_assoc {D : ℕ} (U M : Unitary D) {Q P : Operator D}
    (hP : P = U.1 * Q * (U⁻¹).1) (hM : M.1 * Q = Q * M.1) :
    (U * (M * U⁻¹)).1 * P = P * (U * (M * U⁻¹)).1 := by
  have hUI : (U⁻¹).1 * U.1 = 1 := U.2.1
  calc (U * (M * U⁻¹)).1 * P
      = U.1 * M.1 * ((U⁻¹).1 * U.1) * Q * (U⁻¹).1 := by
          rw [hP]; simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
    _ = U.1 * (M.1 * Q) * (U⁻¹).1 := by
          rw [hUI, op_mul_one_assoc]; simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = U.1 * Q * ((U⁻¹).1 * U.1) * M.1 * (U⁻¹).1 := by
          rw [hM, hUI]; simp -zeta -zetaDelta only [op_mul_assoc_assoc, op_one_mul_assoc]
    _ = P * (U * (M * U⁻¹)).1 := by
          rw [hP]; simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
theorem conj_fix_of_comm_assoc {D : ℕ} (U M : Unitary D) {P : Operator D}
    (hU : U.1 * P = P * U.1) (hM : M.1 * P = P) : (U * (M * U⁻¹)).1 * P = P := by
  have hUI := unitary_val_inv_comm_of_comm U hU
  have hIU : U.1 * (U⁻¹).1 = 1 := U.2.2
  calc (U * (M * U⁻¹)).1 * P
      = U.1 * (M.1 * ((U⁻¹).1 * P)) := by
        simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
    _ = U.1 * ((M.1 * P) * (U⁻¹).1) := by rw [hUI]; simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = (U.1 * P) * (U⁻¹).1 := by rw [hM]; simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = P * (U.1 * (U⁻¹).1) := by rw [hU, op_mul_assoc_assoc]
    _ = P := by rw [hIU, op_mul_one_assoc]
theorem conj_self_comm_assoc {D : ℕ} (A B : Operator D) {P : Operator D} (hA : A * P = P * A)
    (hB : B * P = P * B) : (A * (B * A)) * P = P * (A * (B * A)) := by
  calc (A * (B * A)) * P
      = A * (B * (A * P)) := by simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = A * ((B * P) * A) := by rw [hA]; simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = (A * P) * (B * A) := by rw [hB]; simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = P * (A * (B * A)) := by rw [hA, op_mul_assoc_assoc]
theorem conj_inv_comm_assoc {D : ℕ} (U M : Unitary D) {P : Operator D} (hU : U.1 * P = P * U.1)
    (hM : M.1 * P = P * M.1) : (U⁻¹ * (M * U)).1 * P = P * (U⁻¹ * (M * U)).1 := by
  have hUI := unitary_val_inv_comm_of_comm U hU
  calc (U⁻¹ * (M * U)).1 * P
      = (U⁻¹).1 * (M.1 * (U.1 * P)) := by
        simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
    _ = (U⁻¹).1 * ((M.1 * P) * U.1) := by rw [hU]; simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = ((U⁻¹).1 * P) * (M.1 * U.1) := by rw [hM]; simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    _ = P * (U⁻¹ * (M * U)).1 := by
      rw [hUI]; simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
theorem extractCleanAncillaUnitary_comm_and_fix_assoc {kAct kZ : ℕ}
    (U : Unitary (2 ^ (kAct + kZ))) (hZ : U.1 * (rZLoc kAct kZ).basisOutcomeProjector 0 =
    (rZLoc kAct kZ).basisOutcomeProjector 0 * U.1) (A : Operator (2 ^ kAct)) : (U.1 * (rActLoc
    kAct kZ).embedMatrix A = (rActLoc kAct kZ).embedMatrix A * U.1 →
    (extractCleanAncillaUnitary U hZ).1 * A = A * (extractCleanAncillaUnitary U hZ).1) ∧ (U.1
    * (rActLoc kAct kZ).embedMatrix A = (rActLoc kAct kZ).embedMatrix A →
    (extractCleanAncillaUnitary U hZ).1 * A = A) := by
  let rA := rActLoc kAct kZ
  let rZ := rZLoc kAct kZ
  let PZ := rZ.basisOutcomeProjector 0
  have hId : rA.concat rZ (rActLoc_disj_rZLoc kAct kZ) = QRegExt.idReg (kAct + kZ) := by
    apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]; exact Fin.ext (by simp [rA, rActLoc, QRegExt.idReg])
    · rw [QRegister.concat_apply_right]; exact Fin.ext (by simp [rZ, rZLoc, QRegExt.idReg])
  have hRed : U.1 * PZ = rA.embedMatrix (extractCleanAncillaUnitary U hZ).1 * PZ := by
    have h0 :=
      embedUnitary_extractCleanAncillaUnitary_mul_projZero rA rZ (rActLoc_disj_rZLoc kAct kZ) U hZ
    rwa [hId, embedUnitary_idReg_eq, QRegister.embedUnitary_val] at h0
  have hCZ : rA.embedMatrix A * PZ = PZ * rA.embedMatrix A :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rA) rZ (rActLoc_disj_rZLoc kAct kZ)
      A 0
  refine ⟨fun hUA ↦ embedMatrix_eq_of_mul_projZero_block (kZ := kZ) _ _ ?_,
    fun hFix ↦ embedMatrix_eq_of_mul_projZero_block (kZ := kZ) _ _ ?_⟩
  · calc rA.embedMatrix ((extractCleanAncillaUnitary U hZ).1 * A) * PZ
        = (rA.embedMatrix (extractCleanAncillaUnitary U hZ).1 * PZ) * rA.embedMatrix A := by
            rw [QRegister.embedMatrix_mul, op_mul_assoc_assoc, hCZ, ← op_mul_assoc_assoc]
      _ = (U.1 * rA.embedMatrix A) * PZ := by
        rw [← hRed, op_mul_assoc_assoc, ← hCZ, ← op_mul_assoc_assoc]
      _ = rA.embedMatrix A * (U.1 * PZ) := by rw [hUA, op_mul_assoc_assoc]
      _ = rA.embedMatrix (A * (extractCleanAncillaUnitary U hZ).1) * PZ := by
            rw [hRed, ← op_mul_assoc_assoc, ← QRegister.embedMatrix_mul]
  · calc rA.embedMatrix ((extractCleanAncillaUnitary U hZ).1 * A) * PZ
        = (rA.embedMatrix (extractCleanAncillaUnitary U hZ).1 * PZ) * rA.embedMatrix A := by
            rw [QRegister.embedMatrix_mul, op_mul_assoc_assoc, hCZ, ← op_mul_assoc_assoc]
      _ = (U.1 * rA.embedMatrix A) * PZ := by
        rw [← hRed, op_mul_assoc_assoc, ← hCZ, ← op_mul_assoc_assoc]
      _ = rA.embedMatrix A * PZ := by rw [hFix]
open Classical in
theorem uPhiFull_and_uXorFull_comm_selCoreSum42_diagonal_ass
    (f : Fin (2 ^ (fullSysCoreWires 80 + 42)) → ℂ) :
    let D := selCoreSum42InFull.embedMatrix (Matrix.diagonal f)
    let uPhi := selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat
    let uXor := selPosCoreZ18InFull.embedUnitary uXorZTarget18
    uPhi.1 * D = D * uPhi.1 ∧ (uPhi⁻¹).1 * D = D * (uPhi⁻¹).1 ∧ uXor.1 * D = D * uXor.1 := by
  intro D uPhi uXor
  obtain ⟨hPresF, _⟩ := preservesOutside_uPhiHeldZ18Cat selHeldZ18SysInFull rPG7InFull
    selHeldZ18SysInFull_disj_rPG7InFull
  rw [selHeldZ18SysInFull_concat_rPG7InFull] at hPresF
  have hPhi : uPhi.1 * D = D * uPhi.1 := by
    dsimp only [D]; rw [embedMatrix_diagonal_local selCoreSum42InFull f]
    refine preservesOutside_comm_diagonal hPresF _ fun x y hOut ↦
      congrArg f (extractIndex_eq_of_basisBits_eq_assoc selCoreSum42InFull fun i ↦
        hOut (selCoreSum42InFull i) fun ⟨m, hm⟩ ↦ by
          have hv := congrArg Fin.val hm; have := i.isLt
          simp [selCoreSum42InFull, rPG7InFull] at hv; omega)
  obtain ⟨hCompA, _, _, hCompXZ⟩ := selHeldZ18SysInFull_compositions
  have hSys :=
    uXorSys_comm_rActLoc_embedMatrix_of_preserves_target (Matrix.diagonal f) fun a b hne ↦ by
    by_cases hab : a = b
    · rw [hab]
    · exact False.elim (hne (op_diagonal_apply_ne_assoc f hab))
  have hXor : uXor.1 * D = D * uXor.1 := by
    dsimp only [D, uXor]
    rw [← hCompA, ← hCompXZ, QRegister.embedMatrix_compose, QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, ← hSys, QRegister.embedMatrix_mul]
  exact ⟨hPhi, unitary_val_inv_comm_of_comm uPhi hPhi, hXor⟩
open Classical in
theorem basisOutcomeProjector_mul_conjTranspose_assoc {k n : ℕ}
    (r : QRegister k n) (v : Fin (2 ^ k)) :
    r.basisOutcomeProjector v * (r.basisOutcomeProjector v)ᴴ = r.basisOutcomeProjector v := by
  rw [QRegister.basisOutcomeProjector_conjTranspose, QRegister.basisOutcomeProjector_eq_diagonal,
    diagonal_mul_diagonal_op_assoc]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  by_cases h : r.extractIndex x = v
  · rw [ite_eq_left h, mul_one]
  · rw [ite_eq_right h, mul_zero]
open Classical in
/-- Unconditional commutation of `uStageA7StepCat uSpec` with `pStream218Core 80` across ALL
  `rPG7` states. -/
theorem uStageA7StepCat_comm_pStream218Core (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14)))
    (hE : (uStr3AxisOfSpec uSpec).1 * pSum42CoreZero = eStream217Core) :
    (uStageA7StepCat uSpec).1 * selCoreSum42InAct.embedMatrix (pStream218Core 80) =
    selCoreSum42InAct.embedMatrix (pStream218Core 80) * (uStageA7StepCat uSpec).1 := by
  have hP0Adj : pSum42CoreZero * (pSum42CoreZero)ᴴ = pSum42CoreZero :=
    basisOutcomeProjector_mul_conjTranspose_assoc _ _
  have hP217Eq : pStream217Core 80 =
      (uStr3AxisOfSpec uSpec).1 * pSum42CoreZero * ((uStr3AxisOfSpec uSpec)⁻¹).1 := by
    rw [← eStream217Core_mul_conjTranspose, ← hE, op_conjTranspose_mul_assoc,
      unitary_inv_val_eq_conjTranspose_assoc]
    simp -zeta -zetaDelta only [op_mul_assoc_assoc]
    rw [← op_mul_assoc_assoc pSum42CoreZero, hP0Adj]
  have hP218Eq : pStream218Core 80 =
      (uSlot0Sum42Add 80).1 * pStream217Core 80 * ((uSlot0Sum42Add 80)⁻¹).1 := by
    rw [← eStream218Core_mul_conjTranspose, ← uSlot0Sum42Add_mul_eStream217Core,
      op_conjTranspose_mul_assoc, ← eStream217Core_mul_conjTranspose,
      unitary_inv_val_eq_conjTranspose_assoc]
    simp -zeta -zetaDelta only [op_mul_assoc_assoc]
  have hHeadP0 : (selPosCoreInFull.embedUnitary uHeadConjHCore).1 *
      selCoreSum42InFull.embedMatrix pSum42CoreZero = selCoreSum42InFull.embedMatrix
      pSum42CoreZero * (selPosCoreInFull.embedUnitary uHeadConjHCore).1 := by
    rw [pSum42CoreZero, embedMatrix_basisOutcomeProjector_zero_assoc,
      QRegister.basisOutcomeProjector_eq_diagonal, QRegister.embedUnitary_val]
    refine embedMatrix_comm_diagonal_of_outside selPosCoreInFull uHeadConjHCore.1 _ fun x y hOut ↦
      ?_
    refine congrArg (fun z ↦ if z = 0 then (1 : ℂ) else 0)
      ((basisBitsEquiv 42).injective (funext fun j ↦ ?_))
    change basisBits 42 _ j = basisBits 42 _ j
    rw [basisBits_extractIndex_assoc, basisBits_extractIndex_assoc]
    refine hOut _ fun ⟨i, hi⟩ ↦ ?_
    have hv := congrArg Fin.val hi
    have hiLt : i.val < 4034 := i.isLt
    have h1 : (selPosCoreInFull.wires i).val = 0 + i.val := rfl
    have h2 : ((selCoreSum42InFull.compose (rZLoc (fullSysCoreWires 80) 42)).wires j).val =
        0 + (fullSysCoreWires 80 + j.val) := rfl
    rw [h1, h2, fullSysCoreWires80_eq_4034_assoc] at hv
    omega
  have hStrHead : ((selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uSpec)) *
      (selPosCoreInFull.embedUnitary uHeadConjHCore * (selCoreSum42InFull.embedUnitary
      (uStr3AxisOfSpec uSpec))⁻¹)).1 * selCoreSum42InFull.embedMatrix (pStream217Core 80) =
      selCoreSum42InFull.embedMatrix (pStream217Core 80) * ((selCoreSum42InFull.embedUnitary
      (uStr3AxisOfSpec uSpec)) * (selPosCoreInFull.embedUnitary uHeadConjHCore *
      (selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uSpec))⁻¹)).1 :=
    conj_comm_of_conj_eq_assoc _ _
      (by rw [hP217Eq, ← QRegister.embedUnitary_inv, QRegister.embedUnitary_val,
            QRegister.embedUnitary_val, QRegister.embedMatrix_mul,
              QRegister.embedMatrix_mul]) hHeadP0
  let f217 : Fin (2 ^ (fullSysCoreWires 80 + 42)) → ℂ := fun x ↦
    if ∀ w, regVal (rSum14InCoreSum42 80 w) (basisBits _ x) =
      spectatorSum217 w (fun q ↦ basisBits _ x (rCoreInCoreSum42 80 q)) then 1 else 0
  have hP217D : pStream217Core 80 = Matrix.diagonal f217 := rfl
  obtain ⟨hPhi, _, hXor⟩ := uPhiFull_and_uXorFull_comm_selCoreSum42_diagonal_ass f217
  rw [← hP217D] at hPhi hXor
  have hFull : (uStageAInnerFullCat uSpec).1 * selCoreSum42InFull.embedMatrix (pStream217Core 80) =
      selCoreSum42InFull.embedMatrix (pStream217Core 80) * (uStageAInnerFullCat uSpec).1 := by
    have hMid :=
      conj_inv_comm_assoc (selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat) _ hPhi hStrHead
    have hEqU : (uStageAInnerFullCat uSpec).1 = (selPosCoreZ18InFull.embedUnitary uXorZTarget18).1 *
        (((selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat)⁻¹ *
          ((selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uSpec) *
            (selPosCoreInFull.embedUnitary uHeadConjHCore *
              (selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uSpec))⁻¹)) *
            selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat)).1 *
          (selPosCoreZ18InFull.embedUnitary uXorZTarget18).1) := by
      dsimp only [uStageAInnerFullCat];
        simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
    rw [hEqU]
    exact conj_self_comm_assoc _ _ hXor hMid
  have hCSComp : (rActLoc kCoreSum42PG7 18).compose selCoreSum42InAct = selCoreSum42InFull := by
    apply qreg_ext; intro i; exact Fin.ext (by
      simp [rActLoc, selCoreSum42InAct, selCoreSum42InFull])
  have hInCat : (uStageAInnerCat uSpec).1 * selCoreSum42InAct.embedMatrix (pStream217Core 80) =
      selCoreSum42InAct.embedMatrix (pStream217Core 80) * (uStageAInnerCat uSpec).1 :=
    (extractCleanAncillaUnitary_comm_and_fix_assoc (uStageAInnerFullCat uSpec)
      (uStageAInnerFullCat_comm_projZero uSpec) _).1
      (by rwa [← QRegister.embedMatrix_compose, hCSComp])
  have hSw0 := unitary_comm_proj_of_intertwines_isometry _ _ _ _
    uSwapCore3967_comm_eStream217Core eStream217Core_mul_conjTranspose
  have hSw : ((selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967).1 *
      selCoreSum42InAct.embedMatrix (pStream217Core 80) =
      selCoreSum42InAct.embedMatrix (pStream217Core 80) *
        ((selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967).1 := by
    rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, hSw0, QRegister.embedMatrix_mul]
  have hSwCat : (uStageAInnerSwapCat uSpec).1 * selCoreSum42InAct.embedMatrix (pStream217Core 80) =
      selCoreSum42InAct.embedMatrix (pStream217Core 80) * (uStageAInnerSwapCat uSpec).1 := by
    have hEqSw : (uStageAInnerSwapCat uSpec).1 =
        ((selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967).1 *
          ((uStageAInnerCat uSpec).1 *
            ((selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967).1) := by
      dsimp only [uStageAInnerSwapCat]
      rw [unitary_coe_mul_assoc, unitary_coe_mul_assoc, op_mul_assoc_assoc]
    rw [hEqSw]
    exact conj_self_comm_assoc _ _ hSw hInCat
  have hQ0 := selCatInCoreSum42PG7_expQft_comm_high18Diag_assoc
    (fun x ↦ if ∀ w, regVal (rSum14InCoreSum42 80 w) (basisBits _ x) =
      spectatorSum217 w (fun q ↦ basisBits _ x (rCoreInCoreSum42 80 q)) then 1 else 0)
    fun a b hOut ↦ by
      have hSumEq : ∀ w, regVal (rSum14InCoreSum42 80 w) (basisBits _ a) =
          regVal (rSum14InCoreSum42 80 w) (basisBits _ b) := fun w ↦
        congrArg bitsVal (funext fun j ↦ hOut _ fun ⟨k, hk⟩ ↦ by
          have hv := congrArg Fin.val hk; have := k.isLt
          have h1 : ((rElec0InCoreSum42 80).wires k).val = 0 + k.val := rfl
          have h2 : (rSum14InCoreSum42 80 w j).val = (fullSysCoreWires 80 + 14 * w.val) + j.val :=
            rfl
          rw [h1, h2, fullSysCoreWires80_eq_4034_assoc] at hv; omega)
      have hSpecEq : ∀ w, spectatorSum217 w (fun q ↦ basisBits _ a (rCoreInCoreSum42 80 q)) =
          spectatorSum217 w (fun q ↦ basisBits _ b (rCoreInCoreSum42 80 q)) := fun w ↦
        Finset.sum_congr rfl fun e _ ↦ congrArg bitsVal (funext fun r ↦ hOut _ fun ⟨k, hk⟩ ↦ by
          have hv := congrArg Fin.val hk; have := k.isLt; have := e.isLt; have := w.isLt; have :=
            r.isLt
          have h1 : ((rElec0InCoreSum42 80).wires k).val = 0 + k.val := rfl
          have h2 : (rCoreInCoreSum42 80 (rElecSlotAxis (QRegExt.idReg _) e.succ w r)).val =
              0 + ((18 * e.succ.val + 6 * w.val) + r.val) := rfl
          rw [h1, h2, Fin.val_succ] at hv; omega)
      have hIff : (∀ w, regVal (rSum14InCoreSum42 80 w) (basisBits _ a) =
            spectatorSum217 w (fun q ↦ basisBits _ a (rCoreInCoreSum42 80 q))) ↔
          (∀ w, regVal (rSum14InCoreSum42 80 w) (basisBits _ b) =
            spectatorSum217 w (fun q ↦ basisBits _ b (rCoreInCoreSum42 80 q))) :=
        forall_congr' fun w ↦ by rw [hSumEq w, hSpecEq w]
      by_cases hC : ∀ w, regVal (rSum14InCoreSum42 80 w) (basisBits _ a) =
          spectatorSum217 w (fun q ↦ basisBits _ a (rCoreInCoreSum42 80 q))
      · rw [ite_eq_left hC, ite_eq_left (hIff.mp hC)]
      · rw [ite_eq_right hC, ite_eq_right (mt hIff.mpr hC)]
  have h5Cat : (uStageA5StepCat uSpec).1 * selCoreSum42InAct.embedMatrix (pStream217Core 80) =
      selCoreSum42InAct.embedMatrix (pStream217Core 80) * (uStageA5StepCat uSpec).1 :=
    conj_inv_comm_assoc _ _ hQ0.1 hSwCat
  exact conj_comm_of_conj_eq_assoc _ _
    (by rw [hP218Eq, ← QRegister.embedUnitary_inv, QRegister.embedUnitary_val,
          QRegister.embedUnitary_val, QRegister.embedMatrix_mul, QRegister.embedMatrix_mul]) h5Cat
/-- 218-electron raw-stream computation unitary `uSlot0Sum42Add 80 * uStr3AxisOfSpec
  uStream217Spec131` on `4034 + 42`. -/
noncomputable def u218CS_assoc : Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  uSlot0Sum42Add 80 * uStr3AxisOfSpec uStream217Spec131
/-- Active-width (`kCoreSum42PG7`) embedding of `u218CS_assoc`. -/
noncomputable def u218Act_assoc : Unitary (2 ^ kCoreSum42PG7) :=
  selCoreSum42InAct.embedUnitary u218CS_assoc
/-- `pSum42CoreZero`-conjugated Stage-A active unitary on `kCoreSum42PG7`. -/
noncomputable def uStageA7Conj0_assoc : Unitary (2 ^ kCoreSum42PG7) :=
  u218Act_assoc⁻¹ * (uStageA7StepCat uStream217Spec131 * u218Act_assoc)
/-- Permutation selector `Fin kCoreSum42PG7 → Fin ((fullSysCoreWires 80 + 7) + 42)` routing
  `rSum42` to `rZLoc _ 42`. -/
def selActInCP7Z42_assoc : QRegister kCoreSum42PG7 ((fullSysCoreWires 80 + 7) + 42) :=
  let rC : QRegister (fullSysCoreWires 80) ((fullSysCoreWires 80 + 7) + 42) :=
    QRegister.block 0 (fullSysCoreWires 80) (by omega)
  let rZ : QRegister 42 ((fullSysCoreWires 80 + 7) + 42) :=
    QRegister.block (fullSysCoreWires 80 + 7) 42 (by omega)
  let rP : QRegister 7 ((fullSysCoreWires 80 + 7) + 42) :=
    QRegister.block (fullSysCoreWires 80) 7 (by omega)
  (rC.concat rZ (disjoint_block_sep (Or.inl (by omega)))).concat rP
    (disjointWires_concat_left _ (disjoint_block_sep (Or.inl (by omega)))
      (disjoint_block_sep (Or.inr (by omega))))
open Classical in
theorem uStageA7Conj0_comm_projZero42_assoc :
    (selActInCP7Z42_assoc.embedUnitary uStageA7Conj0_assoc).1 *
      (rZLoc (fullSysCoreWires 80 + 7) 42).basisOutcomeProjector 0 =
    (rZLoc (fullSysCoreWires 80 + 7) 42).basisOutcomeProjector 0 *
      (selActInCP7Z42_assoc.embedUnitary uStageA7Conj0_assoc).1 := by
  have h218E : u218CS_assoc.1 * pSum42CoreZero = eStream218Core := by
    unfold u218CS_assoc
    rw [unitary_coe_mul_assoc, op_mul_assoc_assoc,
      uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core, uSlot0Sum42Add_mul_eStream217Core]
  have hInvE : (u218CS_assoc⁻¹).1 * eStream218Core = pSum42CoreZero := by
    rw [← h218E, ← op_mul_assoc_assoc, ← unitary_coe_mul_assoc, inv_mul_cancel,
      OneMemClass.coe_one, op_one_mul_assoc]
  have hP0Adj : pSum42CoreZero = pSum42CoreZero * (pSum42CoreZero)ᴴ :=
    (basisOutcomeProjector_mul_conjTranspose_assoc _ _).symm
  have hP0Eq : pSum42CoreZero = (u218CS_assoc⁻¹).1 * pStream218Core 80 * u218CS_assoc.1 := by
    calc pSum42CoreZero = pSum42CoreZero * (pSum42CoreZero)ᴴ := hP0Adj
      _ = ((u218CS_assoc⁻¹).1 * eStream218Core) * ((u218CS_assoc⁻¹).1 * eStream218Core)ᴴ := by
        rw [hInvE]
      _ = (u218CS_assoc⁻¹).1 * (eStream218Core * (eStream218Core)ᴴ) * u218CS_assoc.1 := by
            rw [op_conjTranspose_mul_assoc,
              ← unitary_inv_val_eq_conjTranspose_assoc (u218CS_assoc⁻¹), inv_inv]
            simp -zeta -zetaDelta only [op_mul_assoc_assoc]
      _ = (u218CS_assoc⁻¹).1 * pStream218Core 80 * u218CS_assoc.1 := by
            rw [eStream218Core_mul_conjTranspose]
  have hAct0 : uStageA7Conj0_assoc.1 * selCoreSum42InAct.embedMatrix pSum42CoreZero =
      selCoreSum42InAct.embedMatrix pSum42CoreZero * uStageA7Conj0_assoc.1 := by
    have h1 := conj_comm_of_conj_eq_assoc u218Act_assoc⁻¹
      (uStageA7StepCat uStream217Spec131)
      (Q := selCoreSum42InAct.embedMatrix (pStream218Core 80))
      (P := selCoreSum42InAct.embedMatrix pSum42CoreZero)
      (by dsimp only [u218Act_assoc]; rw [inv_inv, ← QRegister.embedUnitary_inv,
            QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
            ← QRegister.embedMatrix_mul, ← hP0Eq])
      (uStageA7StepCat_comm_pStream218Core uStream217Spec131
        uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core)
    simpa only [uStageA7Conj0_assoc, inv_inv] using h1
  have hCompZ : (selActInCP7Z42_assoc.compose selCoreSum42InAct).compose
      (rZLoc (fullSysCoreWires 80) 42) = rZLoc (fullSysCoreWires 80 + 7) 42 := by
    apply qreg_ext; intro j
    have hj : selCoreSum42InAct (rZLoc (fullSysCoreWires 80) 42 j) =
        Fin.castAdd 7 (Fin.natAdd (fullSysCoreWires 80) j) :=
      Fin.ext (by simp [selCoreSum42InAct, rZLoc])
    change selActInCP7Z42_assoc (selCoreSum42InAct (rZLoc (fullSysCoreWires 80) 42 j)) = _
    rw [hj]; dsimp only [selActInCP7Z42_assoc]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_right]; rfl
  have hPZ : selActInCP7Z42_assoc.embedMatrix (selCoreSum42InAct.embedMatrix pSum42CoreZero) =
      (rZLoc (fullSysCoreWires 80 + 7) 42).basisOutcomeProjector 0 := by
    rw [pSum42CoreZero, embedMatrix_basisOutcomeProjector_zero_assoc,
      embedMatrix_basisOutcomeProjector_zero_assoc, ← QRegister.compose_assoc, hCompZ]
  rw [← hPZ, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hAct0,
    QRegister.embedMatrix_mul]
/-- Stream-free `(fullSysCoreWires 80 + 7)` Stage-A unitary extracted on `{rSum42 = 0}`. -/
noncomputable def uStageACorePG7 : Unitary (2 ^ (fullSysCoreWires 80 + 7)) :=
  extractCleanAncillaUnitary (selActInCP7Z42_assoc.embedUnitary uStageA7Conj0_assoc)
    uStageA7Conj0_comm_projZero42_assoc
/-- `rCoreSeg ++ rPG7Seg` register inside `fullSysBEWires 80 + 48`. -/
def rCorePG7InSeg : QRegister (fullSysCoreWires 80 + 7) (fullSysBEWires 80 + 48) :=
  rCoreSeg.concat (rCat80.compose (rTopCatSlice 7 48 (singleCat_seven_le_of_48 le_rfl)))
    (hCoreSeg_disj_Cat80.compose_right _)
/-- Streamless segment unitary `uStageARawSeg` on `fullSysBEWires 80 + 48`. -/
noncomputable def uStageARawSeg : Unitary (2 ^ (fullSysBEWires 80 + 48)) :=
  rCorePG7InSeg.embedUnitary uStageACorePG7
open Classical in
/-- Unconditional `E_rawStream42` intertwining of `uStageARawFull` with `rSegFull.embedUnitary
  uStageARawSeg`. -/
theorem uStageARawFull_mul_E_rawStream42 : uStageARawFull.1 * E_rawStream42 = E_rawStream42 *
    (rSegFull.embedUnitary uStageARawSeg).1 := by
  let rCP7Full : QRegister (fullSysCoreWires 80 + 7) kFull80 :=
    rCoreFull.concat rPG7Full hCoreFull_disj_rPG7Full
  have hCP7DisjSum : rCP7Full.DisjointWires rSum0 :=
    disjointWires_concat_left _ rCoreFull_disj_rSum0 (QRegExt.disjointWires_symm
      rSum0_disj_rPG7Full)
  have hSegCat : rSegFull.compose rCat80 = rPG48Full := by
    rw [rSegFull_eq_rAct0_compose_rSegOrig, QRegister.compose_assoc]
    change rAct0.compose (rSegOrig.compose rCat80) = rAct0.compose rPG48Orig
    congr 1; apply qreg_ext; intro j
    change rSegOrig (rCat80 j) = rSegOrig (InterWalkRSum42Hoist.rPG48Loc j)
    congr 1; apply Fin.ext
    simp [rCat80, InterWalkRSum42Hoist.rPG48Loc, SingleCatSpine.rTopCatSlice]
  have hSegCP7 : rSegFull.compose rCorePG7InSeg = rCP7Full := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) idx
    · dsimp only [rCorePG7InSeg, rCP7Full]
      rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
        ← QRegister.compose_apply, rSegFull_compose_rCoreSeg_eq]
    · dsimp only [rCorePG7InSeg, rCP7Full]
      rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right]
      change (rSegFull.compose rCat80) (rTopCatSlice 7 48 (singleCat_seven_le_of_48 le_rfl) m) =
        rPG7Full m
      rw [hSegCat]; apply Fin.ext
      rw [rPG48Full_val_eq, rPG7Full_val_eq]
      simp [rTopCatSlice]; omega
  have hPermFull : (rCP7Full.concat rSum0 hCP7DisjSum).compose selActInCP7Z42_assoc =
      rActStageAFull80 := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun iCS ↦ ?_) (fun m ↦ ?_) idx
    · refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) iCS
      · have hL : selActInCP7Z42_assoc (Fin.castAdd 7 (Fin.castAdd 42 i)) =
            Fin.castAdd 42 (Fin.castAdd 7 i) :=
          Fin.ext (by simp [selActInCP7Z42_assoc, QRegister.concat_apply_left])
        rw [QRegister.compose_apply, hL, QRegister.concat_apply_left]
        dsimp only [rCP7Full, rActStageAFull80]
        rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
        dsimp only [rCSFull80]; rw [QRegister.concat_apply_left]
      · have hM : selActInCP7Z42_assoc (Fin.castAdd 7 (Fin.natAdd (fullSysCoreWires 80) j)) =
            Fin.natAdd (fullSysCoreWires 80 + 7) j :=
          Fin.ext (by simp [selActInCP7Z42_assoc, QRegister.concat_apply_left,
            QRegister.concat_apply_right])
        rw [QRegister.compose_apply, hM, QRegister.concat_apply_right]
        dsimp only [rActStageAFull80]; rw [QRegister.concat_apply_left]
        dsimp only [rCSFull80]; rw [QRegister.concat_apply_right]
    · have hR : selActInCP7Z42_assoc (Fin.natAdd (fullSysCoreWires 80 + 42) m) =
          Fin.castAdd 42 (Fin.natAdd (fullSysCoreWires 80) m) :=
        Fin.ext (by simp [selActInCP7Z42_assoc, QRegister.concat_apply_right])
      rw [QRegister.compose_apply, hR, QRegister.concat_apply_left]
      dsimp only [rCP7Full, rActStageAFull80]
      rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
  have hRed := embedUnitary_extractCleanAncillaUnitary_mul_projZero rCP7Full rSum0 hCP7DisjSum
    (selActInCP7Z42_assoc.embedUnitary uStageA7Conj0_assoc) uStageA7Conj0_comm_projZero42_assoc
  rw [← QRegister.embedUnitary_compose, hPermFull] at hRed
  have hCSComp : rActStageAFull80.compose selCoreSum42InAct = rCSFull80 := by
    apply qreg_ext; intro i
    have hi : selCoreSum42InAct i = Fin.castAdd 7 i :=
      Fin.ext (by simp [selCoreSum42InAct])
    rw [QRegister.compose_apply, hi]; dsimp only [rActStageAFull80];
      rw [QRegister.concat_apply_left]
  let U218F := rCSFull80.embedUnitary u218CS_assoc
  have hU218Eq : rActStageAFull80.embedUnitary u218Act_assoc = U218F := by
    dsimp only [u218Act_assoc, U218F]; rw [← QRegister.embedUnitary_compose, hCSComp]
  have h218E : u218CS_assoc.1 * pSum42CoreZero = eStream218Core := by
    unfold u218CS_assoc
    rw [unitary_coe_mul_assoc, op_mul_assoc_assoc,
      uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core, uSlot0Sum42Add_mul_eStream217Core]
  have hP0Full : rCSFull80.embedMatrix pSum42CoreZero = pSum42Zero := by
    rw [pSum42CoreZero, pSum42Zero, embedMatrix_basisOutcomeProjector_zero_assoc]
    congr 1; apply qreg_ext; intro j
    have hj : rZLoc (fullSysCoreWires 80) 42 j = Fin.natAdd (fullSysCoreWires 80) j :=
      Fin.ext (by simp [rZLoc])
    rw [QRegister.compose_apply, hj]; dsimp only [rCSFull80]; rw [QRegister.concat_apply_right]
  have hU218P0 : U218F.1 * pSum42Zero = E_rawStream42 := by
    dsimp only [U218F, rCSFull80] at hP0Full ⊢
    rw [← hP0Full, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, h218E,
      rCSFull_embedMatrix_eStream218Core_eq_E_rawStream42]
  have hInvU218E : (U218F⁻¹).1 * E_rawStream42 = pSum42Zero := by
    rw [← hU218P0, ← op_mul_assoc_assoc, ← unitary_coe_mul_assoc, inv_mul_cancel,
      OneMemClass.coe_one, op_one_mul_assoc]
  have hSegEmb : rSegFull.embedUnitary uStageARawSeg = rCP7Full.embedUnitary uStageACorePG7 := by
    dsimp only [uStageARawSeg]; rw [← QRegister.embedUnitary_compose, hSegCP7]
  have hConjUnfold : rActStageAFull80.embedUnitary uStageA7Conj0_assoc =
      U218F⁻¹ * (uStageARawFull * U218F) := by
    dsimp only [uStageA7Conj0_assoc, uStageARawFull]
    rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, QRegister.embedUnitary_inv, hU218Eq]
  rw [hConjUnfold] at hRed
  rw [hSegEmb]
  calc uStageARawFull.1 * E_rawStream42
      = (U218F.1 * (U218F⁻¹).1) * uStageARawFull.1 * (U218F.1 * pSum42Zero) := by
          rw [← unitary_coe_mul_assoc U218F U218F⁻¹, mul_inv_cancel, OneMemClass.coe_one,
            op_one_mul_assoc, hU218P0]
    _ = U218F.1 * (((U218F⁻¹ * (uStageARawFull * U218F)).1) * rSum0.basisOutcomeProjector 0) := by
          rw [pSum42Zero]; simp -zeta -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
    _ = U218F.1 * ((rCP7Full.embedUnitary uStageACorePG7).1 * rSum0.basisOutcomeProjector 0) := by
          rw [hRed]; rfl
    _ = (U218F.1 * pSum42Zero) * (rCP7Full.embedUnitary uStageACorePG7).1 := by
          have hComm : (rCP7Full.embedUnitary uStageACorePG7).1 * rSum0.basisOutcomeProjector 0 =
              rSum0.basisOutcomeProjector 0 * (rCP7Full.embedUnitary uStageACorePG7).1 :=
            (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCP7Full) rSum0 hCP7DisjSum
              _ 0
          rw [hComm, ← pSum42Zero, op_mul_assoc_assoc]
    _ = E_rawStream42 * (rCP7Full.embedUnitary uStageACorePG7).1 := by rw [hU218P0]
open Classical in
/-- Segment catalyst-state action of `uStageARawSeg` on `catState48`. -/
theorem uStageARawSeg_mul_catState48 : uStageARawSeg.1 * catState48 = (rCoreSeg.embedUnitary
    (unitaryConj (fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128)
    uHeadPhase80Mod4Eff)).1 * catState48 := by
  have hSegCat : rSegFull.compose rCat80 = rPG48Full := by
    rw [rSegFull_eq_rAct0_compose_rSegOrig, QRegister.compose_assoc]
    change rAct0.compose (rSegOrig.compose rCat80) = rAct0.compose rPG48Orig
    congr 1; apply qreg_ext; intro j
    change rSegOrig (rCat80 j) = rSegOrig (InterWalkRSum42Hoist.rPG48Loc j)
    congr 1; exact Fin.ext (by simp [rCat80, InterWalkRSum42Hoist.rPG48Loc,
      SingleCatSpine.rTopCatSlice])
  have hDisjCSPG48 : rCSFull80.DisjointWires rPG48Full :=
    disjointWires_concat_left _
      (disj_of_val_ne fun i j ↦ by
        rw [rCoreFull_val_eq, rPG48Full_val_eq]; have := i.isLt
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
          SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at this; omega)
      (disj_of_val_ne fun i j ↦ by rw [rSum0_val_eq, rPG48Full_val_eq]; have := j.isLt; omega)
  have hInt48 :=
    (intertwinesCat_uStageA_on_catState48_zeroHyp uStream217Spec131 rCSFull80 rPG48Full
      hDisjCSPG48).2.2.2.1
  have hActEq : rCSFull80.concat (rPG48Full.compose (rTopCatSlice 7 48
      (singleCat_seven_le_of_48 le_rfl))) (hDisjCSPG48.compose_right _) = rActStageAFull80 :=
      qreg_ext fun _ ↦ rfl
  have hCatEmb : rSegFull.embedMatrix catState48 =
      (rPG48Full.embedUnitary (U_cat_B_normalized 48)).1 * rPG48Full.basisOutcomeProjector 0 := by
    change rSegFull.embedMatrix ((rCat80.embedUnitary (U_cat_B_normalized 48)).1 *
      rCat80.basisOutcomeProjector 0) = _
    rw [QRegister.embedMatrix_mul, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      embedMatrix_basisOutcomeProjector_zero_assoc, hSegCat, ← QRegister.embedUnitary_val]
  have hInt1 : uStageARawFull.1 * (rPG48Full.embedUnitary (U_cat_B_normalized 48)).1 *
      rPG48Full.basisOutcomeProjector 0 = (rPG48Full.embedUnitary (U_cat_B_normalized 48)).1 *
      (rCSFull80.embedUnitary (uStageA7StepEff uStream217Spec131)).1 *
      rPG48Full.basisOutcomeProjector 0 := by
    have e1 := hInt48.1; rw [hActEq] at e1; exact e1
  have hCatFull : uStageARawFull.1 * rSegFull.embedMatrix catState48 =
      (rCSFull80.embedUnitary (uStageA7StepEff uStream217Spec131)).1 *
        rSegFull.embedMatrix catState48 := by
    rw [hCatEmb, ← op_mul_assoc_assoc, hInt1, ← hInt48.2.1, op_mul_assoc_assoc]
  have hNoCatRaw : (rCSFull80.embedUnitary (uStageA7StepEff uStream217Spec131)).1 *
      E_rawStream42 = E_rawStream42 * rSegFull.embedMatrix (rCoreSeg.embedUnitary (unitaryConj
      (fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128)
      uHeadPhase80Mod4Eff)).1 := by
    have h0 := rCSFull_uStageA7StepEff_mul_E_rawStream42 uStream217Spec131
      uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core
    have h6 : pos24_6_le_80 = (by decide : 6 ≤ 80) := Subsingleton.elim _ _
    change (rCSFull80.embedUnitary (uStageA7StepEff uStream217Spec131)).1 * E_rawStream42 = _ at h0
    rw [h0, h6, ← rSegFull_compose_rCoreSeg_eq, QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val]
  exact seg_mul_catState48_eq_of_intertwineRaw _ _ _ _
    (by rw [uStageARawFull_mul_E_rawStream42, QRegister.embedUnitary_val]) hNoCatRaw hCatFull
open Classical in
/-- `uStageARawSeg` embedded on `rSegOrig` commutes with the 12 idle catalyst wires `rPGIdleOrig
  12`. -/
theorem commutesWithReg_rPGIdleOrig12_uStageARawSeg :
    CommutesWithReg (rPGIdleOrig 12 (by decide)) (rSegOrig.embedUnitary uStageARawSeg).1 := by
  have hDisjIdle : rActStageAFull80.DisjointWires (rPGIdle 12 (by decide)) :=
    disjointWires_concat_left _
      (disjointWires_concat_left _
        (disj_of_val_ne fun i j ↦ by
          rw [rCoreFull_val_eq, rPGIdle_val_eq]; have := i.isLt
          dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons,
            SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at this; omega)
        (disj_of_val_ne fun i j ↦ by rw [rSum0_val_eq, rPGIdle_val_eq]; have := j.isLt; omega))
      (disj_of_val_ne fun m j ↦ by rw [rPG7Full_val_eq, rPGIdle_val_eq]; have := j.isLt; omega)
  exact commutesWithReg_rPGIdleOrig12_of_intertwineRaw uStageARawFull.1 uStageARawSeg
    uStageARawFull_mul_E_rawStream42 (CommutesWithReg.of_disjoint hDisjIdle _)
theorem commutesWithReg_mul_assoc {k N : ℕ} {r : QRegister k N} {A B : Operator (2 ^ N)}
    (hA : CommutesWithReg r A) (hB : CommutesWithReg r B) :
    CommutesWithReg r (A * B) := fun X ↦ by
  rw [op_mul_assoc_assoc, hB X, ← op_mul_assoc_assoc, hA X, op_mul_assoc_assoc]
theorem commutesWithReg_inv_assoc {k N : ℕ} {r : QRegister k N} (U : Unitary (2 ^ N))
    (hU : CommutesWithReg r U.1) : CommutesWithReg r (U⁻¹).1 := fun X ↦
    unitary_val_inv_comm_of_comm U (hU X)
theorem commutesWithReg_compose_assoc {k m N : ℕ} {s : QRegister m N}
    {rSub : QRegister k m} {r : QRegister k N} (hComp : s.compose rSub = r)
    {M : Operator (2 ^ m)} (hM : CommutesWithReg rSub M) :
    CommutesWithReg r (s.embedMatrix M) := fun B ↦ by
  rw [← hComp, QRegister.embedMatrix_compose, ← QRegister.embedMatrix_mul, hM B,
    QRegister.embedMatrix_mul]
theorem commutesWithReg_of_mulVec_ket_assoc {k N : ℕ} (r : QRegister k N) (M : Operator (2 ^ N))
    (c : BitAssignment N → ℂ) (g : BitAssignment N → BitAssignment N)
    (hM : ∀ β : BitAssignment N, M.mulVec (ket β) = c β • ket (g β))
    (hc : ∀ β w, c (writeReg β r w) = c β)
    (hg : ∀ β w, g (writeReg β r w) = writeReg (g β) r w)
    (hfix : ∀ β (t : Fin k), g β (r t) = β (r t)) :
    CommutesWithReg r M := fun B ↦ by
  apply matrix_ext_ket; intro β
  have hLoc : localIdx r (g β) = localIdx r β :=
    congrArg (basisBitsEquiv k).symm (funext fun t ↦ hfix β t)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, embedMatrix_mulVec_ket, Matrix.mulVec_sum,
    hM, Matrix.mulVec_smul, embedMatrix_mulVec_ket, Finset.smul_sum, hLoc]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Matrix.mulVec_smul, hM, hc, hg, smul_smul, smul_smul, mul_comm]
theorem commutesWithReg_elecProd217_of_ge3924_assoc {k : ℕ} (r : QRegister k posCoreWires)
    (hr : ∀ t : Fin k, 3924 ≤ (r t).val) (F : Fin 217 → Unitary (2 ^ 18)) :
    CommutesWithReg r (elecProd217 F).1 := by
  have hList : ∀ L : List (Unitary (2 ^ posCoreWires)),
      (∀ U ∈ L, CommutesWithReg r U.1) → CommutesWithReg r L.prod.1 := by
    intro L; induction L with
    | nil => intro _ B; simp
    | cons U TL ih =>
      intro hMem; rw [List.prod_cons, unitary_coe_mul_assoc]
      exact commutesWithReg_mul_assoc (hMem U List.mem_cons_self)
        (ih fun V hV ↦ hMem V (List.mem_cons_of_mem U hV))
  refine hList _ fun U hU ↦ ?_
  obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hU
  refine CommutesWithReg.of_disjoint (disj_of_val_ne fun j t ↦ ?_) (F e).1
  unfold rSpectatorSlot
  rw [PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ j]
  have := e.isLt; have := j.isLt; have := hr t; omega
open Classical in
theorem commutesWithReg_uSlot0Sum42Add_of_mid_assoc {k : ℕ}
    (rMid : QRegister k (fullSysCoreWires 80 + 42)) (hLo : ∀ t : Fin k, 18 ≤ (rMid t).val)
    (hHi : ∀ t : Fin k, (rMid t).val < fullSysCoreWires 80) : CommutesWithReg rMid
    (uSlot0Sum42Add 80).1 := by
  let kC := fullSysCoreWires 80
  let rA := rActLoc kC 42
  have hAx : ∀ w : Fin 3,
      CommutesWithReg rMid
        ((Slot0SubAdd14And217Stream.selCoreSum14In42 80 w).embedUnitary (uSlot0AxisAdd14 w)).1 :=
          fun w ↦ by
    let rS14 := (rZLoc kC 42).compose (rSum14Slice42 w)
    have hSel : Slot0SubAdd14And217Stream.selCoreSum14In42 80 w =
        rA.concat rS14 ((rActLoc_disj_rZLoc kC 42).compose_right (rSum14Slice42 w)) := by
      apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · rw [QRegister.concat_apply_left, Slot0SubAdd14And217Stream.selCoreSum14In42,
          QRegister.concat_apply_left]
        exact Fin.ext (by simp [rA, rActLoc])
      · rw [QRegister.concat_apply_right, Slot0SubAdd14And217Stream.selCoreSum14In42,
          QRegister.concat_apply_right]
        exact Fin.ext (by simp [kC, rS14, rZLoc, rSum14Slice42])
    let b14 (v : ℕ) : BitAssignment 14 := fun j ↦ if v.testBit j.val then 1 else 0
    let g (β : BitAssignment (kC + 42)) : BitAssignment (kC + 42) :=
      writeReg β rS14 (b14 ((regVal rS14 β + slot0AxisVal w (fun i ↦ β (rA i))) % 2 ^ 14))
    have hnMidS : ∀ j : Fin 14, rS14 j ∉ Set.range rMid.wires := by
      rintro j ⟨t, ht⟩; have hv := congrArg Fin.val ht; have := hHi t
      simp [rS14, rZLoc, rSum14Slice42] at hv; omega
    have hnSMid : ∀ t : Fin k, rMid t ∉ Set.range rS14.wires := by
      rintro t ⟨j, hj⟩; exact hnMidS j ⟨t, hj.symm⟩
    have hnMidE0 : ∀ (e0 : Fin SpecsAux.SpecMirror.numElectrons) (r : Fin 6), e0.val = 0 →
        rA (rElecSlotAxis (QRegExt.idReg kC) e0 w r) ∉ Set.range rMid.wires := by
      rintro e0 r he0 ⟨t, ht⟩; have hv := congrArg Fin.val ht; have := hLo t; have := w.isLt;
        have := r.isLt
      simp [rA, rActLoc, rElecSlotAxis, QRegister.slice, QRegister.compose,
        he0] at hv; omega
    refine commutesWithReg_of_mulVec_ket_assoc rMid _ (fun _ ↦ 1) g (fun β ↦ ?_)
      (fun _ _ ↦ rfl) (fun β u ↦ ?_) (fun β t ↦ writeReg_apply_of_not_mem _ _ _ _ (hnSMid t))
    · rw [one_smul, ket_eq_basisKet, ket_eq_basisKet, hSel, uSlot0AxisAdd14]
      exact (DyadicQft64.catModAddUnitary_mulVec_basisKet rA rS14
        ((rActLoc_disj_rZLoc kC 42).compose_right (rSum14Slice42 w)) (slot0AxisVal w) g β
        (fun q hq ↦ writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦
          hq ((QRegister.mem_image rS14 q).mpr ⟨j, hj⟩))
        (by change bitsVal (fun j ↦ g β (rS14 j)) = _
            rw [show (fun j ↦ g β (rS14 j)) = _ from funext fun _ ↦ writeReg_apply_reg _ _ _ _]
            exact StepBBlock0.bitsVal_eq_of_testBit _ _
              (Nat.mod_lt _ (by decide)) (fun _ ↦ rfl))).symm
    · have h1 : regVal rS14 (writeReg β rMid u) = regVal rS14 β :=
        congrArg bitsVal (funext fun j ↦ writeReg_apply_of_not_mem _ _ _ _ (hnMidS j))
      have h2 : slot0AxisVal w (fun i ↦ writeReg β rMid u (rA i)) =
          slot0AxisVal w (fun i ↦ β (rA i)) :=
        congrArg bitsVal (funext fun r ↦ writeReg_apply_of_not_mem _ _ _ _ (hnMidE0 _ r rfl))
      dsimp only [g]; rw [h1, h2]; funext q
      by_cases hqM : q ∈ Set.range rMid.wires
      · obtain ⟨t, rfl⟩ := hqM
        rw [writeReg_apply_of_not_mem _ _ _ _ (hnSMid t), writeReg_apply_reg, writeReg_apply_reg]
      · by_cases hqS : q ∈ Set.range rS14.wires
        · obtain ⟨j, rfl⟩ := hqS
          rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ (hnMidS j), writeReg_apply_reg]
        · rw [writeReg_apply_of_not_mem _ _ _ _ hqS, writeReg_apply_of_not_mem _ _ _ _ hqM,
            writeReg_apply_of_not_mem _ _ _ _ hqM, writeReg_apply_of_not_mem _ _ _ _ hqS]
  unfold uSlot0Sum42Add
  simp -zeta -zetaDelta only [unitary_coe_mul_assoc]
  exact commutesWithReg_mul_assoc (commutesWithReg_mul_assoc (hAx 2) (hAx 1)) (hAx 0)
open Classical in
theorem commutesWithReg_uStr3Axis_of_ge3924_assoc {k : ℕ}
    (r : QRegister k (fullSysCoreWires 80 + 42)) (hLo : ∀ t : Fin k, 3924 ≤ (r t).val)
    (hHi : ∀ t : Fin k, (r t).val < fullSysCoreWires 80)
    (uSpec : Fin 3 → Unitary (2 ^ (3906 + 14))) : CommutesWithReg r (uStr3AxisOfSpec uSpec).1
    := by
  have hStrAx : ∀ w : Fin 3, CommutesWithReg r
      ((selCoreSum14In42 80 w).embedUnitary
        ((selSpec217InCoreSum14 80).embedUnitary (uSpec w))).1 := fun w ↦ by
    obtain ⟨hvSpec, hvSum⟩ := selCoreSum14_compose_selSpec217_val_assoc w
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
    refine CommutesWithReg.of_disjoint (disj_of_val_ne fun idx t ↦ ?_) _
    refine Fin.addCases (fun iSpec h ↦ ?_) (fun jSum h ↦ ?_) idx
    · dsimp only [QRegister.compose_apply] at h
      rw [hvSpec iSpec] at h
      have := iSpec.isLt; have := hLo t; omega
    · dsimp only [QRegister.compose_apply] at h
      rw [hvSum jSum] at h
      have := hHi t; omega
  unfold uStr3AxisOfSpec; simp -zeta -zetaDelta only [unitary_coe_mul_assoc]
  exact commutesWithReg_mul_assoc (commutesWithReg_mul_assoc (hStrAx 2) (hStrAx 1)) (hStrAx 0)
theorem decide_congr_eq_assoc {p q : Prop} [dp : Decidable p] [dq : Decidable q] (h : p = q) :
    @decide p dp = @decide q dq := by
  subst h; exact congrArg (@decide p) (Subsingleton.elim dp dq)
open Classical in
theorem filter_bool_congr_assoc {α : Type*} (s : Finset α) (f g : α → Bool) (h : ∀ x, f x = g x) :
    s.filter (fun x ↦ f x) = s.filter (fun x ↦ g x) := by
  have hfg : f = g := funext h; subst hfg; rfl
open Classical in
theorem headSpec_congr_outside_ctrl3_assoc {β₁ β₂ : BitAssignment posCoreWires}
    (hOut : ∀ q : Wire posCoreWires, q.val < 3951 ∨ 3954 ≤ q.val → β₁ q = β₂ q) :
    headEnBoolSpec β₁ = headEnBoolSpec β₂ ∧
      headPhaseMod4Origin0RepairedZ8Spec β₁ = headPhaseMod4Origin0RepairedZ8Spec β₂ := by
  let rC0 := QRegExt.ofFin posCoreWires
  have hS2 : β₁ (wSlot2Core rC0) = β₂ (wSlot2Core rC0) :=
    hOut _ (Or.inl (by dsimp only [rC0]; rw [wSlot2Core_ofFin_val_assoc]; omega))
  have hS1 : β₁ (wSlot1Core rC0) = β₂ (wSlot1Core rC0) :=
    hOut _ (Or.inl (by dsimp only [rC0]; rw [wSlot1Core_ofFin_val_assoc]; omega))
  have hS0w : β₁ (wSlot0Core rC0) = β₂ (wSlot0Core rC0) :=
    hOut _ (Or.inl (by dsimp only [rC0]; rw [wSlot0Core_ofFin_val_assoc]; omega))
  have hNuc : regVal (rNucIdx rC0) β₁ = regVal (rNucIdx rC0) β₂ :=
    congrArg bitsVal (funext fun q ↦ hOut _ (Or.inr (by
      dsimp only [rC0]; rw [rNucIdx_ofFin_val_assoc]; omega)))
  have hAnc : regVal (rAnchorIdx rC0) β₁ = regVal (rAnchorIdx rC0) β₂ :=
    congrArg bitsVal (funext fun q ↦ hOut _ (Or.inr (by
      dsimp only [rC0]; rw [rAnchorIdx_ofFin_val_assoc]; omega)))
  have hRej : β₁ (wSubReject rC0) = β₂ (wSubReject rC0) :=
    hOut _ (Or.inr (by dsimp only [rC0]; rw [wSubReject_ofFin_val_assoc]; omega))
  have hIsH : β₁ (wIsHead rC0) = β₂ (wIsHead rC0) :=
    hOut _ (Or.inr (by dsimp only [rC0]; rw [wIsHead_ofFin_val_assoc]; omega))
  have hEn : headEnBoolSpec β₁ = headEnBoolSpec β₂ := by
    dsimp only [headEnBoolSpec]
    dsimp only [rC0] at hS2 hS1 hS0w hRej hIsH hNuc hAnc
    rw [hS2, hS1, hS0w, hRej, hIsH, hNuc, hAnc]
  have hS0 : headS0Bool β₁ = headS0Bool β₂ := by
    unfold headS0Bool; dsimp only [rC0] at hS0w; rw [hS0w]
  have hTgt : headTargetCoord64 β₁ = headTargetCoord64 β₂ :=
    (headTargetCoord64_congr_outside_spec_and_wTh hS0w
      (fun q ↦ hOut _ (Or.inr (by rw [rHeadFine21_ofFin_val_assoc]; omega)))
      (fun q ↦ hOut _ (Or.inl (by rw [rElecSlot0_ofFin_val_assoc]; have := q.isLt; omega)))
      (fun q ↦ hOut _ (Or.inr (by rw [rCosetB0_ofFin_val_assoc]; omega)))).2
  have hEl : ∀ e : Fin 218,
      slotSubGridCoord64 (rElecSlot rC0 e) β₁ = slotSubGridCoord64 (rElecSlot rC0 e) β₂ := fun e ↦
        by
    funext w; apply Fin.ext
    change bitsVal (fun j : Fin 6 ↦ β₁ (axisBitRev6 (rElecSlot rC0 e) w j)) =
      bitsVal (fun j : Fin 6 ↦ β₂ (axisBitRev6 (rElecSlot rC0 e) w j))
    refine congrArg bitsVal (funext fun j ↦ ?_)
    have hq : axisBitRev6 (rElecSlot rC0 e) w j =
        rElecSlot rC0 e ⟨6 * w.val + (5 - j.val), by omega⟩ := rfl
    rw [hq]
    exact hOut _ (Or.inl <| by
      rw [PosSlots24UnbarreledWide.rElecSlot_ofFin_val e _]
      have := e.isLt; have := w.isLt; have := j.isLt; omega)
  have hHit : headHitSetOrigin0RepairedSpec β₁ = headHitSetOrigin0RepairedSpec β₂ := by
    dsimp only [headHitSetOrigin0RepairedSpec]
    dsimp only [rC0] at hEl
    refine filter_bool_congr_assoc Finset.univ _ _ fun e ↦ ?_
    by_cases he : e.val = 0
    · rw [ite_eq_left he, ite_eq_left he, hS0, decide_congr_eq_assoc (by rw [hEl 0, hTgt])]
    · rw [ite_eq_right he, ite_eq_right he, decide_congr_eq_assoc (by rw [hEl e])]
  have hTh : β₁ (wHeadThresh rC0) = β₂ (wHeadThresh rC0) :=
    hOut _ (Or.inr (by dsimp only [rC0]; rw [wHeadThresh_ofFin_val_assoc]; omega))
  dsimp only [rC0] at hTh
  exact ⟨hEn, by dsimp only [headPhaseMod4Origin0RepairedZ8Spec]; rw [hEn, hS0, hTh, hHit]⟩
open Classical in
/-- `uStageARawSeg` commutes with the 3 control wires `rCtrl3InSeg` (`[3951 .. 3954)`). -/
theorem commutesWithReg_rCtrl3InSeg_uStageARawSeg :
    CommutesWithReg rCtrl3InSeg uStageARawSeg.1 := by
  let rCtrlPos : QRegister 3 posCoreWires := QRegister.block 3951 3 (by
    rw [posCoreWires_eq_4034_assoc]; omega)
  let rCtrlCore : QRegister 3 (fullSysCoreWires 80) := QRegister.block 3951 3 (by
    rw [fullSysCoreWires80_eq_4034_assoc]; omega)
  let rCtrlCS : QRegister 3 (fullSysCoreWires 80 + 42) := QRegister.block 3951 3 (by
    rw [fullSysCoreWires80_eq_4034_assoc]; omega)
  let rCtrlHAct : QRegister 3 kHeldZ18Act := QRegister.block 3951 3 (by
    rw [kHeldZ18Act_eq_4101_assoc]; omega)
  let rCtrlAct : QRegister 3 kCoreSum42PG7 := QRegister.block 3951 3 (by
    rw [kCoreSum42PG7_eq_4083_assoc]; omega)
  let rCtrlFullZ : QRegister 3 (kCoreSum42PG7 + 18) := QRegister.block 3951 3 (by
    rw [kCoreSum42PG7_eq_4083_assoc]; omega)
  let wTh := wHeadThresh (QRegExt.ofFin posCoreWires)
  have hwThNe : ∀ t : Fin 3, rCtrlPos t ≠ wTh := fun t h ↦ by
    have hv := congrArg Fin.val h; have := t.isLt
    have hw : wTh.val = 3985 := wHeadThresh_ofFin_val_assoc
    simp [rCtrlPos, hw] at hv; omega
  have hnCtrl : ∀ q : Wire posCoreWires,
      q.val < 3951 ∨ 3954 ≤ q.val → q ∉ Set.range rCtrlPos.wires := by
    rintro q hq ⟨t, ht⟩; have hv := congrArg Fin.val ht; have := t.isLt
    simp [rCtrlPos] at hv; omega
  have hHeadMid : CommutesWithReg rCtrlPos uHeadPhaseMod4Origin0Repaired.1 :=
    commutesWithReg_of_mulVec_ket_assoc rCtrlPos uHeadPhaseMod4Origin0Repaired.1
      (fun β ↦ omega8 ^ (headPhaseMod4Origin0RepairedZ8Spec β).val)
      (flipThClean wTh headEnBoolSpec) (ket_monomialZ8UnitaryN _ _ _)
      (fun β u ↦ by rw [(headSpec_congr_outside_ctrl3_assoc fun q hq ↦
        writeReg_apply_of_not_mem _ _ _ _ (hnCtrl q hq)).2])
      (fun β u ↦ by
        have hEnU : headEnBoolSpec (Function.update (writeReg β rCtrlPos u) wTh 0) =
            headEnBoolSpec (Function.update β wTh 0) :=
          (headSpec_congr_outside_ctrl3_assoc fun q hq ↦ by
            by_cases hqw : q = wTh
            · subst hqw; simp
            · rw [Function.update_of_ne hqw, Function.update_of_ne hqw,
                writeReg_apply_of_not_mem _ _ _ _ (hnCtrl q hq)]).1
        unfold flipThClean flipTh; rw [hEnU]; funext q
        by_cases hb : headEnBoolSpec (Function.update β wTh 0) = true
        · rw [ite_eq_left hb, ite_eq_left hb]
          by_cases hqC : q ∈ Set.range rCtrlPos.wires
          · obtain ⟨t, rfl⟩ := hqC
            rw [Function.update_of_ne (hwThNe t), writeReg_apply_reg, writeReg_apply_reg]
          · by_cases hqw : q = wTh
            · subst hqw
              rw [Function.update_self, writeReg_apply_of_not_mem _ _ _ _ hqC,
                writeReg_apply_of_not_mem _ _ _ _ hqC, Function.update_self]
            · rw [Function.update_of_ne hqw, writeReg_apply_of_not_mem _ _ _ _ hqC,
                writeReg_apply_of_not_mem _ _ _ _ hqC, Function.update_of_ne hqw]
        · rw [ite_eq_right hb, ite_eq_right hb])
      (fun β t ↦ flipThClean_apply_ne wTh headEnBoolSpec β (hwThNe t))
  have hHad := commutesWithReg_elecProd217_of_ge3924_assoc rCtrlPos
    (fun t ↦ by simp [rCtrlPos]; omega) (fun _ ↦ uHadamard18)
  have hHead : CommutesWithReg rCtrlPos uHeadConjHCore.1 :=
    commutesWithReg_mul_assoc (commutesWithReg_mul_assoc (commutesWithReg_inv_assoc uHad217 hHad)
      hHeadMid) hHad
  have hStr : CommutesWithReg rCtrlCS (uStr3AxisOfSpec uStream217Spec131).1 :=
    commutesWithReg_uStr3Axis_of_ge3924_assoc rCtrlCS
      (fun t ↦ by simp [rCtrlCS]; omega)
      (fun t ↦ by
        have ht : (rCtrlCS t).val = 3951 + t.val := by simp [rCtrlCS]
        have := t.isLt; rw [ht, fullSysCoreWires80_eq_4034_assoc]; omega)
      uStream217Spec131
  have hHyb : ∀ (c : ℕ) (S : CanonStageSpec128),
      CommutesWithReg rCtrlHAct ((selHybridHeldZ18Cat c).embedUnitary S.uCat).1 := fun c S ↦
    CommutesWithReg.of_disjoint (disj_of_val_ne fun idx t ↦ by
      have := idx.isLt; have := t.isLt
      change selHybridHeldZ18Nat c idx.val ≠ 3951 + t.val
      unfold selHybridHeldZ18Nat kHeldZ18Sys
      simp only [fullSysCoreWires80_eq_4034_assoc]
      split_ifs <;> omega) _
  have hPhi : CommutesWithReg rCtrlHAct uPhiHeldZ18Cat.1 := by
    have hEl : CommutesWithReg rCtrlHAct
        ((selHeldZ18SysInAct.compose selCoreInHeldZ18Sys).embedUnitary uPointElec217Core).1 :=
      commutesWithReg_compose_assoc
        (by apply qreg_ext; intro t; exact Fin.ext (by simp [selHeldZ18SysInAct,
              selCoreInHeldZ18Sys,
              rCtrlPos, rCtrlHAct]))
        (commutesWithReg_elecProd217_of_ge3924_assoc rCtrlPos
          (fun t ↦ by simp [rCtrlPos]; omega) _)
    have hSum : CommutesWithReg rCtrlHAct
        ((selHeldZ18SysInAct.compose selZ18Sum42InHeldZ18Sys).embedUnitary uPointSumClifford60).1 :=
      CommutesWithReg.of_disjoint (disj_of_val_ne fun idx t ↦ by
        intro h
        have := idx.isLt; have := t.isLt
        simp only [QRegister.compose_apply, selHeldZ18SysInAct, selZ18Sum42InHeldZ18Sys,
          rCtrlHAct, qreg_block_apply, Function.Embedding.coeFn_mk, zero_add] at h
        by_cases h18 : idx.val < 18
        · rw [dite_eq_left h18] at h; dsimp only [] at h;
            rw [fullSysCoreWires80_eq_4034_assoc] at h; omega
        · rw [dite_eq_right h18] at h; dsimp only [] at h;
            rw [fullSysCoreWires80_eq_4034_assoc] at h; omega) _
    unfold uPhiHeldZ18Cat; simp -zeta -zetaDelta only [unitary_coe_mul_assoc]
    exact commutesWithReg_mul_assoc hEl (commutesWithReg_mul_assoc hSum
      (commutesWithReg_mul_assoc (hHyb 1 _) (commutesWithReg_mul_assoc (hHyb 2 _)
        (commutesWithReg_mul_assoc (hHyb 3 _) (commutesWithReg_mul_assoc (hHyb 4 _) (hHyb 5 _))))))
  obtain ⟨hCompA, _, _, hCompXZ⟩ := selHeldZ18SysInFull_compositions
  have hXor : CommutesWithReg rCtrlFullZ (selPosCoreZ18InFull.embedUnitary uXorZTarget18).1 :=
    fun B ↦ by
    have hSys :=
      uXorSys_comm_rActLoc_embedMatrix_of_preserves_target (rCtrlCS.embedMatrix B) fun a b hne ↦ by
      rw [QRegister.embedMatrix_apply_of_agreeOutside] at hne
      have hOut : rCtrlCS.AgreeOutside a b := by
        by_contra hc; rw [ite_eq_right hc, mul_zero] at hne; exact hne rfl
      have hBit : ∀ q : Wire posCoreWires, q.val < 3951 ∨ 3954 ≤ q.val →
          basisBits posCoreWires (((rCoreInCoreSum42 80).compose selPosCoreInCore80).extractIndex a)
            q =
            basisBits posCoreWires (((rCoreInCoreSum42 80).compose selPosCoreInCore80).extractIndex
              b) q :=
        fun q hq ↦ by
          rw [basisBits_extractIndex_assoc, basisBits_extractIndex_assoc]
          refine hOut _ fun ⟨t, ht⟩ ↦ ?_
          have hv := congrArg Fin.val ht; have := t.isLt
          simp [rCoreInCoreSum42, selPosCoreInCore80, rCtrlCS] at hv; omega
      exact headTargetPoint18_congr_assoc
        (headTargetCoord64_congr_outside_spec_and_wTh
          (hBit _ (Or.inl (by rw [wSlot0Core_ofFin_val_assoc]; omega)))
          (fun q ↦ hBit _ (Or.inr (by rw [rHeadFine21_ofFin_val_assoc]; omega)))
          (fun q ↦ hBit _ (Or.inl (by rw [rElecSlot0_ofFin_val_assoc]; have := q.isLt; omega)))
          (fun q ↦ hBit _ (Or.inr (by rw [rCosetB0_ofFin_val_assoc]; omega)))).2
    have hCtrlFullEq : selCoreSum42InFull.compose rCtrlCS = rCtrlFullZ := by
      apply qreg_ext; intro t; exact Fin.ext (by simp [selCoreSum42InFull, rCtrlCS, rCtrlFullZ])
    rw [← hCtrlFullEq, ← hCompA, ← hCompXZ, QRegister.embedMatrix_compose,
      QRegister.embedMatrix_compose, QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, ← hSys, QRegister.embedMatrix_mul]
  have hFullZ : CommutesWithReg rCtrlFullZ (uStageAInnerFullCat uStream217Spec131).1 := by
    have hPhiF : CommutesWithReg rCtrlFullZ (selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat).1 :=
      commutesWithReg_compose_assoc
        (by apply qreg_ext; intro t; apply Fin.ext; have := t.isLt
            change (selHeldZ18ActInFull (rCtrlHAct t)).val = 3951 + t.val
            have h1 : (rCtrlHAct t).val = 3951 + t.val := rfl
            rw [selHeldZ18ActInFull_val_assoc, h1, fullSysCoreWires80_eq_4034_assoc]
            split_ifs <;> omega)
        hPhi
    have hStrF : CommutesWithReg rCtrlFullZ (selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec
      uStream217Spec131)).1 :=
      commutesWithReg_compose_assoc
        (by
          apply qreg_ext; intro t; exact Fin.ext (by
          simp [selCoreSum42InFull, rCtrlCS, rCtrlFullZ]))
        hStr
    have hHeadF : CommutesWithReg rCtrlFullZ (selPosCoreInFull.embedUnitary uHeadConjHCore).1 :=
      commutesWithReg_compose_assoc
        (by
          apply qreg_ext; intro t; exact Fin.ext (by simp [selPosCoreInFull, rCtrlPos, rCtrlFullZ]))
        hHead
    unfold uStageAInnerFullCat; simp -zetaDelta only [unitary_coe_mul_assoc]
    exact commutesWithReg_mul_assoc hXor (commutesWithReg_mul_assoc (commutesWithReg_inv_assoc _
      hPhiF)
      (commutesWithReg_mul_assoc hStrF (commutesWithReg_mul_assoc hHeadF
        (commutesWithReg_mul_assoc (commutesWithReg_inv_assoc _ hStrF) (commutesWithReg_mul_assoc
          hPhiF hXor)))))
  have hInCat : CommutesWithReg rCtrlAct (uStageAInnerCat uStream217Spec131).1 := fun B ↦
    (extractCleanAncillaUnitary_comm_and_fix_assoc _ (uStageAInnerFullCat_comm_projZero _) _).1 <|
      by
      have hc : (rActLoc kCoreSum42PG7 18).compose rCtrlAct = rCtrlFullZ := by
        apply qreg_ext; intro t; exact Fin.ext (by simp [rActLoc, rCtrlAct, rCtrlFullZ])
      rw [← QRegister.embedMatrix_compose, hc]; exact hFullZ B
  have hSw : CommutesWithReg rCtrlCore uSwapCore3967.1 := by
    have hn3967 : wCore3967 ∉ Set.range rCtrlCore.wires := by
      rintro ⟨t, ht⟩; have hv := congrArg Fin.val ht; have := t.isLt
      have hw : wCore3967.val = 3967 := wCore3967_val_assoc
      simp [rCtrlCore, hw] at hv; omega
    have hn4029 : wCore4029 ∉ Set.range rCtrlCore.wires := by
      rintro ⟨t, ht⟩; have hv := congrArg Fin.val ht; have := t.isLt
      have hw : wCore4029.val = 4029 := wCore4029_val_assoc
      simp [rCtrlCore, hw] at hv; omega
    refine commutesWithReg_of_mulVec_ket_assoc rCtrlCore uSwapCore3967.1 (fun _ ↦ 1) swapCore3967Fn
      (fun β ↦ by rw [one_smul]; exact uSwapCore3967_mulVec_ket β) (fun _ _ ↦ rfl)
      (fun β u ↦ ?_) (fun β t ↦ ?_)
    · funext q; unfold swapCore3967Fn
      by_cases hq : q ∈ Set.range rCtrlCore.wires
      · obtain ⟨t, rfl⟩ := hq
        have h1 : rCtrlCore t ≠ wCore3967 := fun h ↦ hn3967 ⟨t, h⟩
        have h2 : rCtrlCore t ≠ wCore4029 := fun h ↦ hn4029 ⟨t, h⟩
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, writeReg_apply_reg, writeReg_apply_reg]
      · have hEq : Equiv.swap wCore3967 wCore4029 q ∉ Set.range rCtrlCore.wires := by
          rintro ⟨t, ht⟩
          have h1 : rCtrlCore t ≠ wCore3967 := fun h ↦ hn3967 ⟨t, h⟩
          have h2 : rCtrlCore t ≠ wCore4029 := fun h ↦ hn4029 ⟨t, h⟩
          have hq' := congrArg (Equiv.swap wCore3967 wCore4029) ht
          rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_self] at hq'
          exact hq ⟨t, hq'⟩
        rw [writeReg_apply_of_not_mem _ _ _ _ hq, writeReg_apply_of_not_mem _ _ _ _ hEq]
    · unfold swapCore3967Fn
      rw [Equiv.swap_apply_of_ne_of_ne (fun h ↦ hn3967 ⟨t, h⟩) (fun h ↦ hn4029 ⟨t, h⟩)]
  have hSwAct : CommutesWithReg rCtrlAct
      ((selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967).1 :=
    commutesWithReg_compose_assoc
      (by
        apply qreg_ext; intro t; exact Fin.ext (by
        simp [selCoreSum42InAct, rCoreInCoreSum42, rCtrlCore, rCtrlAct]))
      hSw
  have hQ0 : CommutesWithReg rCtrlAct (selCatInCoreSum42PG7.embedUnitary
    activeOneElecExpQftStage128.uCat).1 :=
    CommutesWithReg.of_disjoint (disj_of_val_ne fun idx t ↦ by
      have ht : (rCtrlAct.wires t).val = 3951 + t.val := by
        simp [rCtrlAct]
      have := t.isLt
      rw [ht]
      exact selCatInCoreSum42PG7_wires_val_ne_mid_assoc idx (by omega) (by omega)) _
  have hAddAct : CommutesWithReg rCtrlAct (selCoreSum42InAct.embedUnitary (uSlot0Sum42Add 80)).1 :=
    commutesWithReg_compose_assoc
      (by apply qreg_ext; intro t; exact Fin.ext (by simp [selCoreSum42InAct, rCtrlCS, rCtrlAct]))
      (commutesWithReg_uSlot0Sum42Add_of_mid_assoc rCtrlCS
        (fun t ↦ by simp [rCtrlCS]; omega)
        (fun t ↦ by
          have ht : (rCtrlCS t).val = 3951 + t.val := by simp [rCtrlCS]
          have := t.isLt; rw [ht, fullSysCoreWires80_eq_4034_assoc]; omega))
  have h7Act : CommutesWithReg rCtrlAct (uStageA7StepCat uStream217Spec131).1 := by
    unfold uStageA7StepCat uStageA5StepCat uStageAInnerSwapCat
    simp -zetaDelta only [unitary_coe_mul_assoc, op_mul_assoc_assoc]
    exact commutesWithReg_mul_assoc hAddAct (commutesWithReg_mul_assoc (commutesWithReg_inv_assoc
      _ hQ0) (commutesWithReg_mul_assoc hSwAct (commutesWithReg_mul_assoc hInCat
      (commutesWithReg_mul_assoc hSwAct (commutesWithReg_mul_assoc hQ0 (commutesWithReg_inv_assoc
      _ hAddAct))))))
  have hFullCtrl : CommutesWithReg rUnusedCtrl3Full uStageARawFull.1 :=
    commutesWithReg_compose_assoc
      (by apply qreg_ext; intro t
          have ht : rCtrlAct t = Fin.castAdd 7 (Fin.castAdd 42 ⟨3951 + t.val, by
            have := t.isLt; dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
              SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
                SpecsAux.SpecMirror.projectileBits]; omega⟩) :=
            Fin.ext (by simp [rCtrlAct])
          rw [QRegister.compose_apply, ht]
          dsimp only [rActStageAFull80]; rw [QRegister.concat_apply_left]
          dsimp only [rCSFull80]; rw [QRegister.concat_apply_left]
          apply Fin.ext; rw [rCoreFull_val_eq, rUnusedCtrl3Full_val_eq])
      h7Act
  exact commutesWithReg_rCtrl3InSeg_of_intertwineRaw uStageARawFull.1 uStageARawSeg.1
    (by rw [uStageARawFull_mul_E_rawStream42, QRegister.embedUnitary_val]) hFullCtrl
theorem monomialZ8UnitaryN_mul_diagonal_eq_self_assoc {N : ℕ} (wTh : Wire N)
    (en : BitAssignment N → Bool) (ph : BitAssignment N → ZMod 8) (f : Fin (2 ^ N) → ℂ) (hFix
    : ∀ x : Fin (2 ^ N), f x ≠ 0 → ph (basisBits N x) = 0 ∧ en (Function.update (basisBits N
    x) wTh 0) = false) : (monomialZ8UnitaryN wTh en ph).1 * Matrix.diagonal f =
    Matrix.diagonal f := by
  apply matrix_ext_ket; intro β
  let x := (basisBitsEquiv N).symm β
  have hx : basisBits N x = β := (basisBitsEquiv N).apply_symm_apply β
  rw [← Matrix.mulVec_mulVec, diagonal_mulVec_ket_assoc, Matrix.mulVec_smul]
  by_cases hf : f x = 0
  · rw [hf, zero_smul, zero_smul]
  · obtain ⟨hPh, hEnU⟩ := hFix x hf
    rw [hx] at hPh hEnU
    have hFl : flipThClean wTh en β = β := by unfold flipThClean flipTh; rw [hEnU]; rfl
    rw [ket_monomialZ8UnitaryN, hPh, hFl]; simp
open Classical in
/-- Unconditional fixation of `pCoinSlack010Seg` by `uStageARawSeg` (`slot1 = 1 ⇒ headEnBoolSpec
  = false`). -/
theorem uStageARawSeg_mul_pCoinSlack010Seg :
    uStageARawSeg.1 * pCoinSlack010Seg = pCoinSlack010Seg := by
  let rSlackPos : QRegister 3 posCoreWires := QRegister.block 3948 3 (by
    rw [posCoreWires_eq_4034_assoc]; omega)
  let rSlackCore : QRegister 3 (fullSysCoreWires 80) := QRegister.block 3948 3 (by
    rw [fullSysCoreWires80_eq_4034_assoc]; omega)
  let rSlackCS : QRegister 3 (fullSysCoreWires 80 + 42) := QRegister.block 3948 3 (by
    rw [fullSysCoreWires80_eq_4034_assoc]; omega)
  let pLoc3 : Operator (2 ^ 3) :=
    slotBitProj (n := 3) ⟨2, by decide⟩ 0 *
      slotBitProj (n := 3) ⟨1, by decide⟩ 1 *
      slotBitProj (n := 3) ⟨0, by decide⟩ 0
  have hSlackCore : pCoinSlack010Core = rSlackCore.embedMatrix pLoc3 := by
    have hwC0 : rSlackCore ⟨0, by decide⟩ = FullSysCatSegmentBridge.iSlot0 80 :=
      Fin.ext (by rw [iSlot0_80_val_assoc]; simp [rSlackCore])
    have hwC1 : rSlackCore ⟨1, by decide⟩ = FullSysCatSegmentBridge.iSlot1 80 :=
      Fin.ext (by rw [iSlot1_80_val_assoc]; simp [rSlackCore])
    have hwC2 : rSlackCore ⟨2, by decide⟩ = FullSysCatSegmentBridge.iSlot2 80 :=
      Fin.ext (by rw [iSlot2_80_val_assoc]; simp [rSlackCore])
    unfold pCoinSlack010Core pLoc3 slotBitProj
    rw [diagonal_mul_diagonal_op_assoc, diagonal_mul_diagonal_op_assoc,
      diagonal_mul_diagonal_op_assoc, diagonal_mul_diagonal_op_assoc, embedMatrix_diagonal_local]
    refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
    rw [basisBits_extractIndex_assoc rSlackCore x ⟨0, by decide⟩,
      basisBits_extractIndex_assoc rSlackCore x ⟨1, by decide⟩,
      basisBits_extractIndex_assoc rSlackCore x ⟨2, by decide⟩, hwC0, hwC1, hwC2]
  have hSlackCS : (rCoreInCoreSum42 80).embedMatrix pCoinSlack010Core =
    rSlackCS.embedMatrix pLoc3 := by
    rw [hSlackCore, ← QRegister.embedMatrix_compose]
    exact congrArg (fun r : QRegister 3 (fullSysCoreWires 80 + 42) ↦ r.embedMatrix pLoc3)
      (qreg_ext fun t ↦ Fin.ext (by simp [rCoreInCoreSum42, rSlackCore, rSlackCS]))
  have hHeadMidFix : uHeadPhaseMod4Origin0Repaired.1 * rSlackPos.embedMatrix pLoc3 =
      rSlackPos.embedMatrix pLoc3 := by
    have hwP1 : rSlackPos ⟨1, by decide⟩ = wSlot1Core (QRegExt.ofFin posCoreWires) :=
      Fin.ext (by rw [wSlot1Core_ofFin_val_assoc]; simp [rSlackPos])
    unfold pLoc3 slotBitProj
    rw [diagonal_mul_diagonal_op_assoc, diagonal_mul_diagonal_op_assoc, embedMatrix_diagonal_local]
    unfold uHeadPhaseMod4Origin0Repaired
    refine monomialZ8UnitaryN_mul_diagonal_eq_self_assoc _ _ _ _ fun x hfx ↦ ?_
    rw [basisBits_extractIndex_assoc rSlackPos x ⟨1, by decide⟩, hwP1] at hfx
    let β := basisBits posCoreWires x
    have h1 : (β (wSlot1Core (QRegExt.ofFin posCoreWires))).val = (1 : Fin 2).val := by
      by_contra hne
      apply hfx; rw [ite_eq_right hne, mul_zero, zero_mul]
    have hb1 : β (wSlot1Core (QRegExt.ofFin posCoreWires)) = 1 := ZMod.val_injective 2 h1
    have hb1Beq : (β (wSlot1Core (QRegExt.ofFin posCoreWires)) == 1) = true := beq_iff_eq.mpr hb1
    have hEn : headEnBoolSpec β = false := by
      dsimp only [headEnBoolSpec]
      rw [hb1Beq]; simp only [Bool.not_true, Bool.and_false, Bool.false_and]
    have hEnU : headEnBoolSpec (Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) 0) =
      false := by
      dsimp only [headEnBoolSpec]
      have hwNe : wSlot1Core (QRegExt.ofFin posCoreWires) ≠
          wHeadThresh (QRegExt.ofFin posCoreWires) :=
        fun h ↦ by
          have hv := congrArg Fin.val h;
          rw [wSlot1Core_ofFin_val_assoc, wHeadThresh_ofFin_val_assoc] at hv; omega
      rw [Function.update_of_ne hwNe, hb1Beq]
      simp only [Bool.not_true, Bool.and_false, Bool.false_and]
    refine ⟨?_, hEnU⟩
    unfold headPhaseMod4Origin0RepairedZ8Spec; rw [hEn]; rfl
  have hHadSlack := commutesWithReg_elecProd217_of_ge3924_assoc rSlackPos
    (fun t ↦ by simp [rSlackPos]; omega) (fun _ ↦ uHadamard18) pLoc3
  have hHeadFix : uHeadConjHCore.1 * rSlackPos.embedMatrix pLoc3 = rSlackPos.embedMatrix pLoc3 := by
    have h0 := conj_fix_of_comm_assoc (uHad217)⁻¹ uHeadPhaseMod4Origin0Repaired
      (unitary_val_inv_comm_of_comm uHad217 hHadSlack) hHeadMidFix
    simpa -zeta -zetaDelta only [uHeadConjHCore, inv_inv, unitary_coe_mul_assoc,
      op_mul_assoc_assoc] using h0
  have hSlackFullEq : selPosCoreInFull.embedMatrix (rSlackPos.embedMatrix pLoc3) =
      selCoreSum42InFull.embedMatrix (rSlackCS.embedMatrix pLoc3) := by
    rw [← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose]
    exact congrArg (fun r : QRegister 3 (kCoreSum42PG7 + 18) ↦ r.embedMatrix pLoc3)
      (qreg_ext fun t ↦ Fin.ext (by
        simp [selPosCoreInFull, selCoreSum42InFull, rSlackPos, rSlackCS]))
  have hHeadFullFix : (selPosCoreInFull.embedUnitary uHeadConjHCore).1 *
      selCoreSum42InFull.embedMatrix (rSlackCS.embedMatrix pLoc3) =
      selCoreSum42InFull.embedMatrix (rSlackCS.embedMatrix pLoc3) := by
    rw [← hSlackFullEq, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hHeadFix]
  have hStrSlack : (selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uStream217Spec131)).1 *
      selCoreSum42InFull.embedMatrix (rSlackCS.embedMatrix pLoc3) =
      selCoreSum42InFull.embedMatrix (rSlackCS.embedMatrix pLoc3) *
        (selCoreSum42InFull.embedUnitary (uStr3AxisOfSpec uStream217Spec131)).1 := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
    exact congrArg selCoreSum42InFull.embedMatrix
      (commutesWithReg_uStr3Axis_of_ge3924_assoc rSlackCS
        (fun t ↦ by simp [rSlackCS]; omega)
        (fun t ↦ by
          have ht : (rSlackCS t).val = 3948 + t.val := by simp [rSlackCS]
          have := t.isLt; rw [ht, fullSysCoreWires80_eq_4034_assoc]; omega)
        uStream217Spec131 pLoc3)
  obtain ⟨fCS, hfCS⟩ : ∃ fCS, rSlackCS.embedMatrix pLoc3 = Matrix.diagonal fCS := by
    unfold pLoc3 slotBitProj
    rw [diagonal_mul_diagonal_op_assoc, diagonal_mul_diagonal_op_assoc]
    exact ⟨_, embedMatrix_diagonal_local rSlackCS _⟩
  obtain ⟨hPhi, hPhiI, hXor⟩ := uPhiFull_and_uXorFull_comm_selCoreSum42_diagonal_ass fCS
  rw [← hfCS] at hPhi hPhiI hXor
  have hFullFix : (uStageAInnerFullCat uStream217Spec131).1 *
      selCoreSum42InFull.embedMatrix (rSlackCS.embedMatrix pLoc3) =
      selCoreSum42InFull.embedMatrix (rSlackCS.embedMatrix pLoc3) := by
    have h1 := conj_fix_of_comm_assoc _ _ hStrSlack hHeadFullFix
    have h2 := conj_fix_of_comm_assoc (selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat)⁻¹ _ hPhiI h1
    rw [inv_inv] at h2
    have hXorSelf : (selPosCoreZ18InFull.embedUnitary uXorZTarget18)⁻¹ =
        selPosCoreZ18InFull.embedUnitary uXorZTarget18 :=
      inv_eq_of_mul_eq_one_right (by rw [← QRegister.embedUnitary_mul, uXorZTarget18_mul_self,
        QRegister.embedUnitary_one])
    have h3 := conj_fix_of_comm_assoc (selPosCoreZ18InFull.embedUnitary uXorZTarget18) _ hXor h2
    rw [hXorSelf] at h3
    simpa -zetaDelta only [uStageAInnerFullCat, unitary_coe_mul_assoc, op_mul_assoc_assoc] using h3
  have hInFix : (uStageAInnerCat uStream217Spec131).1 *
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) =
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) :=
    (extractCleanAncillaUnitary_comm_and_fix_assoc _ (uStageAInnerFullCat_comm_projZero _) _).2 <|
      by
      have hc : (rActLoc kCoreSum42PG7 18).compose selCoreSum42InAct = selCoreSum42InFull := by
        apply qreg_ext; intro i; exact Fin.ext (by
          simp [rActLoc, selCoreSum42InAct, selCoreSum42InFull])
      rwa [← QRegister.embedMatrix_compose, hc]
  have hSwSlack0 : uSwapCore3967.1 * pCoinSlack010Core = pCoinSlack010Core * uSwapCore3967.1 :=
    op_comm_mul3 _ _ _ _
      (uSwapCore3967_comm_slotBitProj (FullSysCatSegmentBridge.iSlot2 80) 0
        (fun h ↦ by
          have hv := congrArg Fin.val h; rw [iSlot2_80_val_assoc, wCore3967_val_assoc] at hv; omega)
        (fun h ↦ by
          have hv := congrArg Fin.val h; rw [iSlot2_80_val_assoc, wCore4029_val_assoc] at hv;
          omega))
      (uSwapCore3967_comm_slotBitProj (FullSysCatSegmentBridge.iSlot1 80) 1
        (fun h ↦ by
          have hv := congrArg Fin.val h; rw [iSlot1_80_val_assoc, wCore3967_val_assoc] at hv; omega)
        (fun h ↦ by
          have hv := congrArg Fin.val h; rw [iSlot1_80_val_assoc, wCore4029_val_assoc] at hv;
          omega))
      (uSwapCore3967_comm_slotBitProj (FullSysCatSegmentBridge.iSlot0 80) 0
        (fun h ↦ by
          have hv := congrArg Fin.val h; rw [iSlot0_80_val_assoc, wCore3967_val_assoc] at hv; omega)
        (fun h ↦ by
          have hv := congrArg Fin.val h; rw [iSlot0_80_val_assoc, wCore4029_val_assoc] at hv;
          omega))
  have hSwSlack : ((selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967).1 *
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) =
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) *
        ((selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967).1 := by
    rw [← hSlackCS, QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
      hSwSlack0, QRegister.embedMatrix_mul, QRegister.embedMatrix_mul]
  have hSwSelf : ((selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967)⁻¹ =
      (selCoreSum42InAct.compose (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967 :=
    inv_eq_of_mul_eq_one_right (by rw [← QRegister.embedUnitary_mul,
      PosPostPrep80MergedVep.uSwapCore3967_mul_self, QRegister.embedUnitary_one])
  have hSwFix : (uStageAInnerSwapCat uStream217Spec131).1 *
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) =
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) := by
    have h0 := conj_fix_of_comm_assoc _ _ hSwSlack hInFix
    rw [hSwSelf] at h0;
      simpa -zetaDelta only [uStageAInnerSwapCat, unitary_coe_mul_assoc,
      op_mul_assoc_assoc] using h0
  have hQ0Slack : (selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat).1 *
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) =
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) *
        (selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat).1 := by
    rw [← QRegister.embedMatrix_compose]
    refine CommutesWithReg.of_disjoint (disj_of_val_ne fun idx t ↦ ?_) _ pLoc3
    have ht : ((selCoreSum42InAct.compose rSlackCS).wires t).val = 3948 + t.val := by
      simp [selCoreSum42InAct, rSlackCS]
    have := t.isLt
    rw [ht]
    exact selCatInCoreSum42PG7_wires_val_ne_mid_assoc idx (by omega) (by omega)
  have h5Fix : (uStageA5StepCat uStream217Spec131).1 *
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) =
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) := by
    have h0 :=
      conj_fix_of_comm_assoc (selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat)⁻¹
      _
      (unitary_val_inv_comm_of_comm _ hQ0Slack) hSwFix
    rw [inv_inv] at h0; exact h0
  have hAddSlack : (selCoreSum42InAct.embedUnitary (uSlot0Sum42Add 80)).1 *
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) =
      selCoreSum42InAct.embedMatrix (rSlackCS.embedMatrix pLoc3) *
        (selCoreSum42InAct.embedUnitary (uSlot0Sum42Add 80)).1 := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
    exact congrArg selCoreSum42InAct.embedMatrix
      (commutesWithReg_uSlot0Sum42Add_of_mid_assoc rSlackCS
        (fun t ↦ by simp [rSlackCS]; omega)
        (fun t ↦ by
          have ht : (rSlackCS t).val = 3948 + t.val := by simp [rSlackCS]
          have := t.isLt; rw [ht, fullSysCoreWires80_eq_4034_assoc]; omega) pLoc3)
  have h7Fix : (uStageA7StepCat uStream217Spec131).1 *
      selCoreSum42InAct.embedMatrix ((rCoreInCoreSum42 80).embedMatrix pCoinSlack010Core) =
      selCoreSum42InAct.embedMatrix ((rCoreInCoreSum42 80).embedMatrix pCoinSlack010Core) := by
    rw [hSlackCS]
    exact conj_fix_of_comm_assoc _ _ hAddSlack h5Fix
  have hRawFullFix : uStageARawFull.1 * rSegFull.embedMatrix pCoinSlack010Seg =
      rSegFull.embedMatrix pCoinSlack010Seg := by
    have hReg : rActStageAFull80.compose (selCoreSum42InAct.compose (rCoreInCoreSum42 80)) =
        rSegFull.compose rCoreSeg := by
      rw [rSegFull_compose_rCoreSeg_eq]; apply qreg_ext; intro i
      have hi : selCoreSum42InAct (rCoreInCoreSum42 80 i) = Fin.castAdd 7 (Fin.castAdd 42 i) :=
        Fin.ext (by simp [selCoreSum42InAct, rCoreInCoreSum42])
      rw [QRegister.compose_apply, QRegister.compose_apply, hi]
      dsimp only [rActStageAFull80]; rw [QRegister.concat_apply_left]
      dsimp only [rCSFull80]; rw [QRegister.concat_apply_left]
    dsimp only [uStageARawFull, pCoinSlack010Seg]
    rw [← QRegister.embedMatrix_compose rSegFull rCoreSeg, ← hReg, QRegister.embedMatrix_compose,
      QRegister.embedMatrix_compose, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, h7Fix]
  exact seg_mul_pCoinSlack010Seg_eq_of_intertwineRaw _ _
    (by rw [uStageARawFull_mul_E_rawStream42, QRegister.embedUnitary_val]) hRawFullFix
end Part4_RawFull80AndUncondCounts
end ImplAlt
end StageAConjHAndStreamBridge
namespace StageADeconstrAndQftShare
section Part1_Stream218
open LocalClassicalPerm SpecsAux
open SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open CanonRank7Circuit (ket_eq_basisKet)
open InPlaceFullAddSlice
open NuclearTwistRealizes (slot2AxisSum embedUnitary_idReg_eq)
open SinglePassNuclearTwist288
open InterWalkRSum42Hoist (qreg_block_apply basisBits_streamTarget42 rSum14In42)
open HoistBorrow42ProjBridge (RealizesOnProj)
open HybridStream288Aux HybridStream168Aux
open BoothOpt_06_Stream217ZeroSave0Width128 (rSum14Slice42 selCoreSum14In42 compose_selCoreSum14In42
  rSum14Slice42_disjoint_of_ne)
open StageAConjHAndStreamBridge (rActLoc rZLoc rActLoc_disj_rZLoc rActLoc_concat_rZLoc_eq_idReg
  pSum42CoreZero eStream218Core pSum42CoreZero_mulVec_basisKet eStream42CoreOf_mulVec_basisKet
  joinAZ)
open BoothOpt_Anchor218CachedTrueSwapOuter (realizesOnProj_congr_unitary)
theorem sum_fin218_split5 {a b c d e ab abc abcd : ℕ}
    (hab : a + b = ab) (habc : ab + c = abc) (habcd : abc + d = abcd) (h : abcd + e = 218)
    (f : Fin numElectrons → ℕ) :
    (∑ i : Fin a, f ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin b, f ⟨a + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin c, f ⟨ab + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin d, f ⟨abc + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin e, f ⟨abcd + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) =
      ∑ el : Fin numElectrons, f el := by
  subst hab; subst habc; subst habcd
  let e218 : Fin ((((a + b) + c) + d) + e) ≃ Fin numElectrons := finCongr h
  rw [← Equiv.sum_comp e218, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· +
    ·) ?_ ?_) ?_) ?_) ?_
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
theorem hybrid218TenBatch_eq_slot2AxisSum {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : (((((((((weightedGenBatchVal
    (threePlaneGenChunkWire w 0 0 17 0 119 0 0 (by decide) (by decide) (by decide)
    (by decide)) γ + 2 ^ 0 * weightedGenBatchVal (threePlaneGenChunkWire w 0 17 66 119 31 0 32
    (by decide) (by decide) (by decide) (by decide)) γ) + 2 ^ 0 * weightedGenBatchVal
    (threePlaneGenChunkWire w 0 83 66 150 31 32 32 (by decide) (by decide) (by decide)
    (by decide)) γ) + 2 ^ 0 * weightedGenBatchVal (threePlaneGenChunkWire w 0 149 66 181 31 64
    32 (by decide) (by decide) (by decide) (by decide)) γ) + 2 ^ 0 * weightedGenBatchVal
    (threePlaneGenChunkWire w 0 215 3 212 6 96 122 (by decide) (by decide) (by decide)
    (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal (threePlaneGenChunkWire w 3 0 42 0 71 0 18
    (by decide) (by decide) (by decide) (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal
    (threePlaneGenChunkWire w 3 42 42 71 71 18 18 (by decide) (by decide) (by decide)
    (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal (threePlaneGenChunkWire w 3 84 42 142 71 36
    18 (by decide) (by decide) (by decide) (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal
    (threePlaneGenChunkWire w 3 126 86 213 3 54 41 (by decide) (by decide) (by decide)
    (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal (threePlaneGenChunkWire w 3 212 6 216 2 95
    123 (by decide) (by decide) (by decide) (by decide)) γ) = slot2AxisSum w γ := by
  simp only [Nat.pow_zero, one_mul, weightedGenBatchVal_threePlaneGenChunk]
  let p0 : Fin numElectrons → ℕ := fun e ↦ (γ (elecAxisBitWire w 0 e)).val
  let p1 : Fin numElectrons → ℕ := fun e ↦ 2 * (γ (elecAxisBitWire w 1 e)).val
  let p2 : Fin numElectrons → ℕ := fun e ↦ 4 * (γ (elecAxisBitWire w 2 e)).val
  let p3 : Fin numElectrons → ℕ := fun e ↦ (γ (elecAxisBitWire w 3 e)).val
  let p4 : Fin numElectrons → ℕ := fun e ↦ 2 * (γ (elecAxisBitWire w 4 e)).val
  let p5 : Fin numElectrons → ℕ := fun e ↦ 4 * (γ (elecAxisBitWire w 5 e)).val
  have hp0 := sum_fin218_split5 (a := 17) (b := 66) (c := 66) (d := 66) (e := 3) (ab := 83) (abc :=
    149) (abcd := 215) rfl rfl rfl rfl p0
  have hp1 := sum_fin218_split5 (a := 119) (b := 31) (c := 31) (d := 31) (e := 6) (ab :=
    150) (abc := 181) (abcd := 212) rfl rfl rfl rfl p1
  have hp2 := sum_fin218_split5 (a := 0) (b := 32) (c := 32) (d := 32) (e := 122) (ab := 32) (abc :=
    64) (abcd := 96) rfl rfl rfl rfl p2
  have hp3 := sum_fin218_split5 (a := 42) (b := 42) (c := 42) (d := 86) (e := 6) (ab := 84) (abc :=
    126) (abcd := 212) rfl rfl rfl rfl p3
  have hp4 := sum_fin218_split5 (a := 71) (b := 71) (c := 71) (d := 3) (e := 2) (ab := 142) (abc :=
    213) (abcd := 216) rfl rfl rfl rfl p4
  have hp5 := sum_fin218_split5 (a := 18) (b := 18) (c := 18) (d := 41) (e := 123) (ab :=
    36) (abc := 54) (abcd := 95) rfl rfl rfl rfl p5
  have hGroup :
      (((((((((
          ((∑ i : Fin 17, p0 ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 119, p1 ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 0, p2 ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩)) +
          ((∑ i : Fin 66, p0 ⟨17 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 31, p1 ⟨119 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 32, p2 ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩))) +
          ((∑ i : Fin 66, p0 ⟨83 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 31, p1 ⟨150 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 32, p2 ⟨32 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩))) +
          ((∑ i : Fin 66, p0 ⟨149 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 31, p1 ⟨181 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 32, p2 ⟨64 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩))) +
          ((∑ i : Fin 3, p0 ⟨215 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 6, p1 ⟨212 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 122, p2 ⟨96 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩))) +
          2 ^ 3 * ((∑ i : Fin 42, p3 ⟨0 + i.val, by
            dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 71, p4 ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 18, p5 ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩))) +
          2 ^ 3 * ((∑ i : Fin 42, p3 ⟨42 + i.val, by
            dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 71, p4 ⟨71 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 18, p5 ⟨18 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩))) +
          2 ^ 3 * ((∑ i : Fin 42, p3 ⟨84 + i.val, by
            dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 71, p4 ⟨142 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 18, p5 ⟨36 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩))) +
          2 ^ 3 * ((∑ i : Fin 86, p3 ⟨126 + i.val, by
            dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 3, p4 ⟨213 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 41, p5 ⟨54 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩))) +
          2 ^ 3 * ((∑ i : Fin 6, p3 ⟨212 + i.val, by
            dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 2, p4 ⟨216 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
            (∑ i : Fin 123, p5 ⟨95 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩))) =
      ((∑ e : Fin numElectrons, p0 e) + (∑ e : Fin numElectrons, p1 e) + (∑ e : Fin numElectrons,
        p2 e)) +
        8 * ((∑ e : Fin numElectrons, p3 e) + (∑ e : Fin numElectrons,
          p4 e) + (∑ e : Fin numElectrons, p5 e)) := by
    rw [← hp0, ← hp1, ← hp2, ← hp3, ← hp4, ← hp5]
    ring
  refine hGroup.trans ?_
  rw [slot2AxisSum_eq_bitPlane_sum w γ, Fin.sum_univ_six]
  dsimp only [p0, p1, p2, p3, p4, p5]
  simp only [← Finset.mul_sum,
    show (0 : Fin 6).val = 0 from rfl,
    show (1 : Fin 6).val = 1 from rfl,
    show (2 : Fin 6).val = 2 from rfl,
    show (3 : Fin 6).val = 3 from rfl,
    show (4 : Fin 6).val = 4 from rfl,
    show (5 : Fin 6).val = 5 from rfl]
  ring
/-- Ideal unitary on `2 ^ (fullSysCoreWires mPayload + 14)` realized by `dStream218CoreAdd133`. -/
noncomputable def uStream218Core133 {mPayload : ℕ} (w : Fin 3) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 14)) :=
  let kC := fullSysCoreWires mPayload
  let w1 := threePlaneGenChunkWire (mPayload := mPayload) w 0 0 17 0 119 0 0 (by
    decide) (by decide) (by decide) (by decide)
  let w2 := threePlaneGenChunkWire (mPayload := mPayload) w 0 17 66 119 31 0 32 (by
    decide) (by decide) (by decide) (by decide)
  let w3 := threePlaneGenChunkWire (mPayload := mPayload) w 0 83 66 150 31 32 32 (by
    decide) (by decide) (by decide) (by decide)
  let w4 := threePlaneGenChunkWire (mPayload := mPayload) w 0 149 66 181 31 64 32 (by
    decide) (by decide) (by decide) (by decide)
  let w5 := threePlaneGenChunkWire (mPayload := mPayload) w 0 215 3 212 6 96 122 (by
    decide) (by decide) (by decide) (by decide)
  let w6 := threePlaneGenChunkWire (mPayload := mPayload) w 3 0 42 0 71 0 18 (by
    decide) (by decide) (by decide) (by decide)
  let w7 := threePlaneGenChunkWire (mPayload := mPayload) w 3 42 42 71 71 18 18 (by
    decide) (by decide) (by decide) (by decide)
  let w8 := threePlaneGenChunkWire (mPayload := mPayload) w 3 84 42 142 71 36 18 (by
    decide) (by decide) (by decide) (by decide)
  let w9 := threePlaneGenChunkWire (mPayload := mPayload) w 3 126 86 213 3 54 41 (by
    decide) (by decide) (by decide) (by decide)
  let w10 := threePlaneGenChunkWire (mPayload := mPayload) w 3 212 6 216 2 95 123 (by
    decide) (by decide) (by decide) (by decide)
  ((selCoreSlice kC 3 11 (by
    decide)).embedUnitary (catModAddUnitary kC 11 (weightedGenBatchVal w10)) *
    ((selCoreSlice kC 3 11 (by
      decide)).embedUnitary (catModAddUnitary kC 11 (weightedGenBatchVal w9)) *
    ((selCoreSlice kC 3 10 (by
      decide)).embedUnitary (catModAddUnitary kC 10 (weightedGenBatchVal w8)) *
    ((selCoreSlice kC 3 10 (by
      decide)).embedUnitary (catModAddUnitary kC 10 (weightedGenBatchVal w7)) *
    ((selCoreSlice kC 3 9 (by
      decide)).embedUnitary (catModAddUnitary kC 9 (weightedGenBatchVal w6)) *
    ((selCoreSlice kC 0 11 (by
      decide)).embedUnitary (catModAddUnitary kC 11 (weightedGenBatchVal w5)) *
    ((selCoreSlice kC 0 10 (by
      decide)).embedUnitary (catModAddUnitary kC 10 (weightedGenBatchVal w4)) *
    ((selCoreSlice kC 0 10 (by
      decide)).embedUnitary (catModAddUnitary kC 10 (weightedGenBatchVal w3)) *
    ((selCoreSlice kC 0 9 (by
      decide)).embedUnitary (catModAddUnitary kC 9 (weightedGenBatchVal w2)) *
    (selCoreSlice kC 0 8 (by decide)).embedUnitary (uBitXor kC 8 (weightedGenBatchVal w1)))))))))))
open Classical in
theorem uStream218Core133_compute_ket {mPayload n : ℕ} [NeZero (2 ^ n)] (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) : ∀ β₀ : Fin n → ZMod 2,
    (∀ i : Fin 14, β₀ (rSum14 i) = 0) → ∃ β : Fin n → ZMod 2, ((rCore.concat rSum14
    hCSum).embedUnitary (uStream218Core133 w)).1.mulVec (basisKet β₀) = basisKet β ∧
    (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧ (∀ i : Fin 14, β (rSum14 i) = if
    (slot2AxisSum w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0) := by
  intro β₀ hz
  let w1 := threePlaneGenChunkWire (mPayload := mPayload) w 0 0 17 0 119 0 0 (by
    decide) (by decide) (by decide) (by decide)
  have hb1 : weightedGenBatchVal w1 (fun q ↦ β₀ (rCore q)) ≤ 255 := weightedGenBatchVal_le w1 _
  let w2 := threePlaneGenChunkWire (mPayload := mPayload) w 0 17 66 119 31 0 32 (by
    decide) (by decide) (by decide) (by decide)
  have hb2 : weightedGenBatchVal w2 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w2 _
  let w3 := threePlaneGenChunkWire (mPayload := mPayload) w 0 83 66 150 31 32 32 (by
    decide) (by decide) (by decide) (by decide)
  have hb3 : weightedGenBatchVal w3 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w3 _
  let w4 := threePlaneGenChunkWire (mPayload := mPayload) w 0 149 66 181 31 64 32 (by
    decide) (by decide) (by decide) (by decide)
  have hb4 : weightedGenBatchVal w4 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w4 _
  let w5 := threePlaneGenChunkWire (mPayload := mPayload) w 0 215 3 212 6 96 122 (by
    decide) (by decide) (by decide) (by decide)
  have hb5 : weightedGenBatchVal w5 (fun q ↦ β₀ (rCore q)) ≤ 503 := weightedGenBatchVal_le w5 _
  let w6 := threePlaneGenChunkWire (mPayload := mPayload) w 3 0 42 0 71 0 18 (by
    decide) (by decide) (by decide) (by decide)
  have hb6 : weightedGenBatchVal w6 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w6 _
  let w7 := threePlaneGenChunkWire (mPayload := mPayload) w 3 42 42 71 71 18 18 (by
    decide) (by decide) (by decide) (by decide)
  have hb7 : weightedGenBatchVal w7 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w7 _
  let w8 := threePlaneGenChunkWire (mPayload := mPayload) w 3 84 42 142 71 36 18 (by
    decide) (by decide) (by decide) (by decide)
  have hb8 : weightedGenBatchVal w8 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w8 _
  let w9 := threePlaneGenChunkWire (mPayload := mPayload) w 3 126 86 213 3 54 41 (by
    decide) (by decide) (by decide) (by decide)
  have hb9 : weightedGenBatchVal w9 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w9 _
  let w10 := threePlaneGenChunkWire (mPayload := mPayload) w 3 212 6 216 2 95 123 (by
    decide) (by decide) (by decide) (by decide)
  have hb10 : weightedGenBatchVal w10 (fun q ↦ β₀ (rCore q)) ≤ 502 := weightedGenBatchVal_le w10 _
  obtain ⟨b1, hket1, hInv1⟩ := accInvar_step1_bitXor8 rCore rSum14 hCSum (weightedGenBatchVal w1)
    β₀ (accInvar_zero rSum14 β₀ hz) (by omega)
  obtain ⟨b2, hket2, hInv2⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 0 9 (by decide)
    (weightedGenBatchVal w2) _ β₀ b1 hInv1 (by omega) (by omega)
  obtain ⟨b3, hket3, hInv3⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 0 10 (by decide)
    (weightedGenBatchVal w3) _ β₀ b2 hInv2 (by omega) (by omega)
  obtain ⟨b4, hket4, hInv4⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 0 10 (by decide)
    (weightedGenBatchVal w4) _ β₀ b3 hInv3 (by omega) (by omega)
  obtain ⟨b5, hket5, hInv5⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 0 11 (by decide)
    (weightedGenBatchVal w5) _ β₀ b4 hInv4 (by omega) (by omega)
  obtain ⟨b6, hket6, hInv6⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 9 (by decide)
    (weightedGenBatchVal w6) _ β₀ b5 hInv5 (by omega) (by omega)
  obtain ⟨b7, hket7, hInv7⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 10 (by decide)
    (weightedGenBatchVal w7) _ β₀ b6 hInv6 (by omega) (by omega)
  obtain ⟨b8, hket8, hInv8⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 10 (by decide)
    (weightedGenBatchVal w8) _ β₀ b7 hInv7 (by omega) (by omega)
  obtain ⟨b9, hket9, hInv9⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 11 (by decide)
    (weightedGenBatchVal w9) _ β₀ b8 hInv8 (by omega) (by omega)
  obtain ⟨b10, hket10, hInv10⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 11 (by decide)
    (weightedGenBatchVal w10) _ β₀ b9 hInv9 (by omega) (by omega)
  have hSumEq := hybrid218TenBatch_eq_slot2AxisSum w (fun q ↦ β₀ (rCore q))
  rw [hSumEq] at hInv10
  refine ⟨b10, ?_, hInv10.1, hInv10.2⟩
  simp only [uStream218Core133, QRegister.embedUnitary_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  rw [hket1, hket2, hket3, hket4, hket5, hket6, hket7, hket8, hket9, hket10]
attribute [irreducible] uStream218Core133
/-- Generic 3-axis `218`-electron stream unitary on `fullSysCoreWires 80 + 42` for any per-axis
  unitary family `uAx`. -/
noncomputable def uStr218_3AxisOf (uAx : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) :
    Unitary (2 ^ (fullSysCoreWires 80 + 42)) := ((selCoreSum14In42 80 2).embedUnitary (uAx 2)
    * (selCoreSum14In42 80 1).embedUnitary (uAx 1)) * (selCoreSum14In42 80 0).embedUnitary
    (uAx 0)
/-- Per-axis unitary family (`Axis 0` = `uHybridStream164 0`, `Axes 1, 2` = `uStream218Core133
  w`). -/
noncomputable def uStr218Ax {mPayload : ℕ} : Fin 3 → Unitary (2 ^ (fullSysCoreWires mPayload + 14))
  | 0 => uHybridStream164 0
  | 1 => uStream218Core133 1
  | 2 => uStream218Core133 2
/-- 3-axis `218`-electron stream unitary on `fullSysCoreWires 80 + 42`. -/
noncomputable def uStr218_3Axis : Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  uStr218_3AxisOf uStr218Ax
open Classical in
theorem uStr218Ax_compute_ket {mPayload n : ℕ} [NeZero (2 ^ n)] (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) : ∀ β₀ : Fin n → ZMod 2,
    (∀ i : Fin 14, β₀ (rSum14 i) = 0) → ∃ β : Fin n → ZMod 2,
    ((rCore.concat rSum14 hCSum).embedUnitary (uStr218Ax w)).1.mulVec (basisKet β₀) = basisKet
    β ∧ (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧ (∀ i : Fin 14, β (rSum14 i) = if
    (slot2AxisSum w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0) := by
  fin_cases w
  · exact uHybridStream164_compute_ket 0 rCore rSum14 hCSum
  · exact uStream218Core133_compute_ket 1 rCore rSum14 hCSum
  · exact uStream218Core133_compute_ket 2 rCore rSum14 hCSum
open Classical in
theorem uStr218_3AxisOf_compute_ket (uAx : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14)))
    (hAx : ∀ (w : Fin 3) {n : ℕ} [NeZero (2 ^ n)] (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum14 : QRegister 14 n) (hCSum : rCore.DisjointWires rSum14) (β₀ : Fin n → ZMod 2), (∀ i
    : Fin 14, β₀ (rSum14 i) = 0) → ∃ β : Fin n → ZMod 2, ((rCore.concat rSum14
    hCSum).embedUnitary (uAx w)).1.mulVec (basisKet β₀) = basisKet β ∧ (∀ g : Fin n, g ∉
    rSum14.image → β g = β₀ g) ∧ (∀ i : Fin 14, β (rSum14 i) = if (slot2AxisSum w (fun q ↦ β₀
    (rCore q))).testBit i.val then 1 else 0)) {n : ℕ} [NeZero (2 ^ n)]
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum42 : QRegister 42 n)
    (hCSum42 : rCore.DisjointWires rSum42) : ∀ β₀ : Fin n → ZMod 2,
    (∀ j : Fin 42, β₀ (rSum42 j) = 0) → ∃ β : Fin n → ZMod 2, ((rCore.concat rSum42
    hCSum42).embedUnitary (uStr218_3AxisOf uAx)).1.mulVec (basisKet β₀) = basisKet β ∧
    (∀ g : Fin n, g ∉ rSum42.image → β g = β₀ g) ∧ (∀ w : Fin 3, ∀ i : Fin 14, β
    ((rSum42.compose (rSum14Slice42 w)) i) = if (slot2AxisSum w (fun q ↦ β₀ (rCore
    q))).testBit i.val then 1 else 0) := by
  intro β₀ hz42
  let rS (w : Fin 3) := rSum42.compose (rSum14Slice42 w)
  have hSub (w : Fin 3) : (rS w).image ⊆ rSum42.image := QRegister.image_compose_subset rSum42 _
  have hDisjS {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂) : (rS w₁).DisjointWires (rS w₂) := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    exact (rSum14Slice42_disjoint_of_ne hne).ne i j (rSum42.wires.injective hij)
  have hMat (w : Fin 3) :
      ((rCore.concat rSum42 hCSum42).embedUnitary ((selCoreSum14In42 80 w).embedUnitary (uAx w))).1
        =
        ((rCore.concat (rS w) (hCSum42.compose_right (rSum14Slice42 w))).embedUnitary (uAx w)).1 :=
          by
    simp only [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      compose_selCoreSum14In42, rS]
  obtain ⟨β₁, hk₁, ho₁, hb₁⟩ := hAx 0 rCore (rS 0) (hCSum42.compose_right _) β₀ (fun i ↦ hz42 _)
  have hz₁_1 : ∀ i : Fin 14, β₁ (rS 1 i) = 0 := fun i ↦ by
    rw [ho₁ _ ((hDisjS (by decide : (1 : Fin 3) ≠ 0)).apply_not_mem_right i)]; exact hz42 _
  obtain ⟨β₂, hk₂, ho₂, hb₂⟩ := hAx 1 rCore (rS 1) (hCSum42.compose_right _) β₁ hz₁_1
  have hz₂_2 : ∀ i : Fin 14, β₂ (rS 2 i) = 0 := fun i ↦ by
    rw [ho₂ _ ((hDisjS (by decide : (2 : Fin 3) ≠ 1)).apply_not_mem_right i),
      ho₁ _ ((hDisjS (by decide : (2 : Fin 3) ≠ 0)).apply_not_mem_right i)]
    exact hz42 _
  obtain ⟨β₃, hk₃, ho₃, hb₃⟩ := hAx 2 rCore (rS 2) (hCSum42.compose_right _) β₂ hz₂_2
  have hCore₁ : (fun q ↦ β₁ (rCore q)) = (fun q ↦ β₀ (rCore q)) :=
    funext fun q ↦ ho₁ _ ((hCSum42.compose_right _).apply_not_mem_right q)
  have hCore₂ : (fun q ↦ β₂ (rCore q)) = (fun q ↦ β₀ (rCore q)) :=
    funext fun q ↦
      (ho₂ _ ((hCSum42.compose_right _).apply_not_mem_right q)).trans (congrFun hCore₁ q)
  refine ⟨β₃, ?_, fun g hg ↦ ?_, fun w i ↦ ?_⟩
  · simp only [uStr218_3AxisOf, QRegister.embedUnitary_mul, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec,
      hMat 0, hMat 1, hMat 2]
    rw [hk₁, hk₂, hk₃]
  · rw [ho₃ g (fun m ↦ hg (hSub 2 m)), ho₂ g (fun m ↦ hg (hSub 1 m)), ho₁ g (fun m ↦ hg (hSub 0 m))]
  · fin_cases w
    · have hg : β₃ (rS 0 i) = if (slot2AxisSum 0 (fun q ↦
        β₀ (rCore q))).testBit i.val then 1 else 0 := by
        rw [ho₃ _ ((hDisjS (by decide : (0 : Fin 3) ≠ 2)).apply_not_mem_right i),
          ho₂ _ ((hDisjS (by decide : (0 : Fin 3) ≠ 1)).apply_not_mem_right i), hb₁ i]
      exact hg
    · have hg : β₃ (rS 1 i) = if (slot2AxisSum 1 (fun q ↦
        β₀ (rCore q))).testBit i.val then 1 else 0 := by
        rw [ho₃ _ ((hDisjS (by decide : (1 : Fin 3) ≠ 2)).apply_not_mem_right i), hb₂ i, hCore₁]
      exact hg
    · have hg : β₃ (rS 2 i) = if (slot2AxisSum 2 (fun q ↦
        β₀ (rCore q))).testBit i.val then 1 else 0 := by
        rw [hb₃ i, hCore₂]
      exact hg
open Classical in
theorem uStr218_3AxisOf_mul_pSum42CoreZero_eq_eStream218Core
    (uAx : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) (hAx : ∀ (w : Fin 3) {n : ℕ}
    [NeZero (2 ^ n)] (rCore : QRegister (fullSysCoreWires 80) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) (β₀ : Fin n → ZMod 2), (∀ i : Fin 14, β₀ (rSum14 i) =
    0) → ∃ β : Fin n → ZMod 2, ((rCore.concat rSum14 hCSum).embedUnitary (uAx w)).1.mulVec
    (basisKet β₀) = basisKet β ∧ (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧ (∀ i : Fin 14,
    β (rSum14 i) = if (slot2AxisSum w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0)) :
    (uStr218_3AxisOf uAx).1 * pSum42CoreZero = eStream218Core := by
  let kC := fullSysCoreWires 80
  let rA := rActLoc kC 42
  let rZ := rZLoc kC 42
  apply OctahedralOrbit.matrix_ext_ket; intro β
  rw [ket_eq_basisKet, ← Matrix.mulVec_mulVec, pSum42CoreZero_mulVec_basisKet,
      eStream218Core, eStream42CoreOf_mulVec_basisKet]
  let y := (basisBitsEquiv (kC + 42)).symm β
  by_cases h0 : rZ.extractIndex y = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    have hz42 : ∀ j : Fin 42, β (rZ j) = 0 := by
      have hx := ((QRegExt.extractIndex_eq_zero_iff rZ) y).mp h0
      intro j; simpa [y] using hx j
    obtain ⟨β₁, hk₁, hout₁, hbits₁⟩ :=
      uStr218_3AxisOf_compute_ket uAx hAx rA rZ (rActLoc_disj_rZLoc kC 42) β hz42
    rw [rActLoc_concat_rZLoc_eq_idReg kC 42, embedUnitary_idReg_eq] at hk₁
    rw [hk₁]
    refine congrArg basisKet (funext fun g ↦ ?_)
    have haBits : basisBits kC (rA.extractIndex y) = fun q ↦ β (rA q) := by
      funext q; simp [-Nat.reducePow, y, QRegister.basisBits_extractIndex]
    by_cases hg : g.val < kC
    · have hnZ : g ∉ rZ.image := by
        intro hm; obtain ⟨j, rfl⟩ := (QRegister.mem_image rZ _).mp hm
        simp [rZ, rZLoc] at hg
      have hga : rA ⟨g.val, hg⟩ = g := Fin.ext (by simp [rA, rActLoc])
      rw [hout₁ g hnZ, joinAZ, rZ.basisBits_replaceIndex_of_not_mem _ _ g
        (fun ⟨j, hj⟩ ↦ hnZ ((QRegister.mem_image rZ _).mpr ⟨j, hj⟩)),
        ← hga, rA.basisBits_replaceIndex_apply, haBits]
    · let j42 : Fin 42 := ⟨g.val - kC, by have := g.isLt; omega⟩
      let w : Fin 3 := ⟨j42.val / 14, by have := j42.isLt; omega⟩
      let i14 : Fin 14 := ⟨j42.val % 14, by omega⟩
      have hgz : rZ j42 = g := Fin.ext (by have := g.isLt; simp [rZ, rZLoc, j42]; omega)
      have hjSlice : rSum14Slice42 w i14 = j42 :=
        Fin.ext (by simp [rSum14Slice42, w, i14]; omega)
      have hjIn42 : rSum14In42 w i14 = j42 :=
        Fin.ext (by simp [rSum14In42, w, i14]; omega)
      have hgComp : (rZ.compose (rSum14Slice42 w)) i14 = g := by
        rw [QRegister.compose_apply, hjSlice, hgz]
      rw [← hgComp, hbits₁ w i14, hgComp, ← hgz, joinAZ, rZ.basisBits_replaceIndex_apply,
        ← hjIn42, basisBits_streamTarget42, haBits]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem uStr218_3Axis_mul_pSum42CoreZero_eq_eStream218Core : uStr218_3Axis.1 * pSum42CoreZero
    = eStream218Core := uStr218_3AxisOf_mul_pSum42CoreZero_eq_eStream218Core uStr218Ax
    (fun w {_} _ rC rS hCS ↦ uStr218Ax_compute_ket w rC rS hCS)
theorem inv_uStr218_3Axis_mul_eStream218Core_eq_pSum42CoreZero :
    (uStr218_3Axis⁻¹).1 * eStream218Core = pSum42CoreZero := by
  calc (uStr218_3Axis⁻¹).1 * eStream218Core
      = (uStr218_3Axis⁻¹).1 * (uStr218_3Axis.1 * pSum42CoreZero) := by
          rw [← uStr218_3Axis_mul_pSum42CoreZero_eq_eStream218Core]
    _ = ((uStr218_3Axis⁻¹ * uStr218_3Axis).1) * pSum42CoreZero := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = pSum42CoreZero := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
attribute [irreducible] uStr218_3Axis
end Part1_Stream218
end StageADeconstrAndQftShare
end SharedScope
end
end SlimFermApproxSec4AndStream218

noncomputable section GhostAndMaskedAnchorHead

section
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
attribute [-instance] littleWedderburn Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroK6 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  concat_compose_selDataInAct selDataInAct_disj_selMeasInAct)
namespace StageADeconstrAndQftShare
open HermitianMat SpecsAux SpecsAux.SpecMirror
open StageAConjHAndStreamBridge
open BoothOpt_Anchor218CachedTrueSwapOuter LocalClassicalPerm OctahedralOrbit
open PosSlots24BranchConcrete PosHeadRev18CacheAux
open PosHeadMod4_15476
open scoped ComplexOrder MatrixOrder Circuit.Notation
open QRegExt
open MultiBankWStateRouter (SubspaceStep.seq SubspaceStep.toConstCleanUnitary)
open MultiBankWStateRouter (SubspaceStep.ofConstCleanUnitary)
section Part2_GhostAndQftAnchor
open FullSysCatSegmentBridge (fullSysCoreWires)
open ButterflyBarrelSlot0Conj (spectatorElecReg ActsAsIdOnSpectatorWires PreservesHigh3924On)
open Leaf4Ext48TopStitch (CommutesWithReg)
open ZeroHypLHSStageAB7Step3StepCatState48Proje (rIdInCoreSum42 concat_compose_selCatInCoreSum42PG7)
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply kFull80 rCoreFull embedUnitary_inv_symm)
open DyadicQft64WalkCircuit (rIdInCat rPGInCat disjoint_block_sep)
open CoreQftHadamard140And160 (CanonStageSpec128 rQftCanon128 rSysCanon128 rPGCanon128 rWorkCanon128
  rSysCanon128_disjoint_rPGCanon128 rSysCanon128_disjoint_rWorkCanon128
  rPGCanon128_disjoint_rWorkCanon128 rQftCanon128_disjoint_rWorkCanon128)
open HeldRSum42TwistQftPass2Stitch (rAxisPrefix axisProdPrefix stageHPrefixCanonStage128)
open StageAPointPhase128OnStep (hL3_le_654 ForestSlotConfig xorForestBatchWork
  xorForestBatchFwdDyn128 xorForestBatch_spec stageW16PrefixCanonStage128 forestCfg0 forestCfg1
  forestCfg2 forestCfg3 rCoreInCoreSum42)
open Slot0SubAdd14And217Stream (uSlot0Sum42Add)
open FullConcrete7StepAndTrueSwapSelect (kCoreSum42PG7 selCoreSum42InAct selCatInCoreSum42PG7)
open ZeroHypSlot0CommAndHMidClosure (basisOutcomeProjector_zero_mul_self)
open MasterZeroHypCompactAndCompactTopBridge (embedMatrix_inj_on_work_zero sel25InCat sel18InSys
  concat_sel18InSys_rPGCanon128_eq)
open ZeroHypStageBPureCnotAndHMidBClosure (idxForestAx18 idxForestAx18_inj)
theorem idReg_extractIndex_eq {k : ℕ} (z : Fin (2 ^ k)) :
    (QRegExt.idReg k).extractIndex z = z := by
  apply eq_of_basisBits_eq; intro u
  rw [QRegister.basisBits_extractIndex]; rfl
open Classical in
theorem embedMatrix_idReg_basisOutcomeProjector {n k : ℕ} (rAct : QRegister k n)
    (o : Fin (2 ^ k)) : rAct.embedMatrix ((QRegExt.idReg k).basisOutcomeProjector o) =
    rAct.basisOutcomeProjector o := by
  ext i j
  rw [QRegister.embedMatrix_apply, QRegister.basisOutcomeProjector_eq_diagonal,
      QRegister.basisOutcomeProjector_eq_diagonal]
  dsimp only [Matrix.diagonal, Matrix.of_apply]
  rw [idReg_extractIndex_eq]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [hij, ↓reduceIte]
    by_cases henv : (rAct.basisSplitEquiv i).2 = (rAct.basisSplitEquiv j).2
    · have hne : rAct.extractIndex i ≠ rAct.extractIndex j := by
        intro h1; apply hij
        apply rAct.basisSplitEquiv.injective
        refine Prod.ext ?_ henv
        simpa [QRegister.basisSplitEquiv_apply_fst] using h1
      simp [henv, hne]
    · simp [henv]
open Classical in
/-- Any two unitaries `Q₁, Q₂ : Unitary (2 ^ k)` realized on `(rAct, rWork)` (`rAct.DisjointWires
  rWork`)
by the same dynamic circuit `d` agree up to a global scalar `c : ℂ` (`Q₁.1 = c • Q₂.1`). -/
theorem realizes_eq_smul_of_same {Var : Type} [Fintype Var] [DecidableEq Var] [Inhabited Var]
    {k m n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister k n} {rWork : QRegister m n}
    (hDisj : rAct.DisjointWires rWork) {Q₁ Q₂ : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (h₁ : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork Q₁ d)
    (h₂ : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork Q₂ d) : ∃ c : ℂ, Q₁.1 = c •
    Q₂.1 := by
  let W : Unitary (2 ^ k) := Q₁ * Q₂⁻¹
  have hQ1Eq : Q₁ = W * Q₂ := by simp [W, _root_.mul_assoc]
  have hComm : ∀ (V : Unitary (2 ^ k)) (o : Fin (2 ^ k)),
      let B := V.1 * (QRegExt.idReg k).basisOutcomeProjector o * V.1ᴴ
      W.1 * B = B * W.1 := by
    intro V o B
    let M : Observable (Fin (2 ^ n)) :=
      (rAct.basisOutcomeObservable o).conjUnitary (rAct.embedUnitary V)
    have hM : M.1.1 = rAct.embedMatrix B := by
      have hCoe : M.1.1 =
          (rAct.embedUnitary V).1 * rAct.basisOutcomeProjector o * (rAct.embedUnitary V).1ᴴ := by
        simp [M, Matrix.mul_assoc]
      rw [hCoe, ← embedMatrix_idReg_basisOutcomeProjector rAct o,
          QRegister.embedUnitary_val, ← QRegister.embedMatrix_conjTranspose,
          ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
    obtain ⟨M₁', hwp₁, hp₁⟩ := h₁ M
    obtain ⟨M₂', hwp₂, hp₂⟩ := h₂ M
    have hM' : M₁' = M₂' := by
      have := congrFun (hwp₁.symm.trans hwp₂) default
      simpa using this
    rw [hM'] at hp₁
    have hP0Eq := hp₁.symm.trans hp₂
    rw [hM] at hP0Eq
    have hFold : ∀ Q : Unitary (2 ^ k),
        rWork.basisOutcomeProjector 0 *
          ((rAct.embedUnitary Q).1ᴴ * rAct.embedMatrix B * (rAct.embedUnitary Q).1) *
          rWork.basisOutcomeProjector 0 =
        rAct.embedMatrix (Q.1ᴴ * B * Q.1) * rWork.basisOutcomeProjector 0 := fun Q ↦ by
      have hE : (rAct.embedUnitary Q).1ᴴ * rAct.embedMatrix B * (rAct.embedUnitary Q).1 =
          rAct.embedMatrix (Q.1ᴴ * B * Q.1) := by
        rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_conjTranspose,
            ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
      rw [hE, ← ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hDisj _ 0),
          Matrix.mul_assoc, basisOutcomeProjector_zero_mul_self]
    rw [hFold Q₁, hFold Q₂] at hP0Eq
    have hConjEq : Q₁.1ᴴ * B * Q₁.1 = Q₂.1ᴴ * B * Q₂.1 :=
      embedMatrix_inj_on_work_zero rAct rWork hDisj hP0Eq
    have hWConj : W.1ᴴ * B * W.1 = B := by
      have hQ1Val : Q₁.1 = W.1 * Q₂.1 := congrArg Subtype.val hQ1Eq
      have hQ1H : Q₁.1ᴴ = Q₂.1ᴴ * W.1ᴴ := by
        rw [hQ1Val, Matrix.conjTranspose_mul]
      have hQ2U : Q₂.1 * Q₂.1ᴴ = 1 := by
        rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp Q₂.2
      rw [hQ1H, hQ1Val] at hConjEq
      calc W.1ᴴ * B * W.1
          = (Q₂.1 * Q₂.1ᴴ) * (W.1ᴴ * B * W.1) * (Q₂.1 * Q₂.1ᴴ) := by
              rw [hQ2U, Matrix.one_mul, Matrix.mul_one]
        _ = Q₂.1 * ((Q₂.1ᴴ * W.1ᴴ) * B * (W.1 * Q₂.1)) * Q₂.1ᴴ := by simp only [Matrix.mul_assoc]
        _ = Q₂.1 * (Q₂.1ᴴ * B * Q₂.1) * Q₂.1ᴴ := by rw [hConjEq]
        _ = (Q₂.1 * Q₂.1ᴴ) * B * (Q₂.1 * Q₂.1ᴴ) := by simp only [Matrix.mul_assoc]
        _ = B := by rw [hQ2U, Matrix.one_mul, Matrix.mul_one]
    have hWU : W.1 * W.1ᴴ = 1 := by
      rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp W.2
    calc W.1 * B
        = W.1 * (W.1ᴴ * B * W.1) := by rw [hWConj]
      _ = (W.1 * W.1ᴴ) * B * W.1 := by simp only [Matrix.mul_assoc]
      _ = B * W.1 := by rw [hWU, Matrix.one_mul]
  have hDiag : ∀ x y : Fin (2 ^ k), x ≠ y → W.1 x y = 0 := by
    intro x y hxy
    let P_y := (QRegExt.idReg k).basisOutcomeProjector y
    have hc : (W.1 * ((1 : Unitary (2 ^ k)).1 * P_y * (1 : Unitary (2 ^ k)).1ᴴ)) x y =
        (((1 : Unitary (2 ^ k)).1 * P_y * (1 : Unitary (2 ^ k)).1ᴴ) * W.1) x y :=
      congrFun (congrFun (hComm 1 y) x) y
    rw [OneMemClass.coe_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hc
    dsimp only [P_y] at hc
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
    simp only [idReg_extractIndex_eq, ↓reduceIte, hxy, mul_one, zero_mul] at hc
    exact hc
  have hWDiag : W.1 = Matrix.diagonal (fun x ↦ W.1 x x) := by
    ext x y
    by_cases hxy : x = y
    · subst hxy; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hxy, hDiag x y hxy]
  have hConst : ∀ x : Fin (2 ^ k), W.1 x x = W.1 0 0 := by
    intro x
    let Hk : Unitary (2 ^ k) := hadamardUnitary
    let Bplus : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ :=
      Hk.1 * (QRegExt.idReg k).basisOutcomeProjector 0 * Hk.1ᴴ
    have hc : (W.1 * Bplus) x 0 = (Bplus * W.1) x 0 := congrFun (congrFun (hComm Hk 0) x) 0
    rw [hWDiag, Matrix.diagonal_mul, Matrix.mul_diagonal] at hc
    have hB0 : Bplus x 0 ≠ 0 := by
      have hBval : Bplus x 0 = (1 : ℂ) / ((2 : ℝ) ^ k : ℝ) := by
        change ((Hk.1 * (QRegExt.idReg k).basisOutcomeProjector 0) * Hk.1ᴴ) x 0 = _
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single (0 : Fin (2 ^ k))]
        · rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal]
          dsimp only [Hk, hadamardUnitary]
          rw [idReg_extractIndex_eq, ite_eq_left rfl, mul_one, Matrix.conjTranspose_apply,
              hadamardMatrix_apply_zero k x, ← hadamardMatrix_apply_zero k 0,
              mul_comm, hadamardMatrix_star_mul_self k 0 0]
        · intro z _ hz0
          rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal,
              idReg_extractIndex_eq, ite_eq_right hz0, mul_zero, zero_mul]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      rw [hBval]
      exact one_div_ne_zero (by positivity)
    exact mul_right_cancel₀ hB0 (hc.trans (mul_comm _ _))
  let c : ℂ := W.1 0 0
  refine ⟨c, ?_⟩
  have hWSmul : W.1 = c • (1 : Operator (2 ^ k)) := by
    ext x y
    by_cases hxy : x = y
    · subst hxy; simp [c, hConst x]
    · simp [hxy, hDiag x y hxy]
  rw [hQ1Eq, Submonoid.coe_mul, hWSmul, Matrix.smul_mul, Matrix.one_mul]
/-- Predicate that `U : Unitary (2 ^ (3924 + 3 + 7))` equals a scalar multiple of a `25`-wire
  unitary
embedded on `sel25InCat` (`[0..18) ++ [3927..3934)`). -/
def SupportedOnSel25 (U : Unitary (2 ^ (3924 + 3 + 7))) : Prop :=
  ∃ (c : ℂ) (u25 : Unitary (2 ^ (18 + 7))), U.1 = c • (sel25InCat.embedUnitary u25).1
theorem SupportedOnSel25.mul {U V : Unitary (2 ^ (3924 + 3 + 7))} (hU : SupportedOnSel25 U)
    (hV : SupportedOnSel25 V) : SupportedOnSel25 (U * V) := by
  obtain ⟨cU, u25, hU'⟩ := hU
  obtain ⟨cV, v25, hV'⟩ := hV
  refine ⟨cU * cV, u25 * v25, ?_⟩
  rw [Submonoid.coe_mul, hU', hV', Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      sel25InCat.embedUnitary_mul, Submonoid.coe_mul]
theorem SupportedOnSel25.inv {U : Unitary (2 ^ (3924 + 3 + 7))} (hU : SupportedOnSel25 U) :
    SupportedOnSel25 U⁻¹ := by
  obtain ⟨c, u25, hU'⟩ := hU
  refine ⟨star c, u25⁻¹, ?_⟩
  have hInvEq : ∀ {D : ℕ} (X : Unitary D), (X⁻¹).1 = X.1ᴴ := fun X ↦ by
    rw [← star_eq_conjTranspose]
    exact (congrArg Subtype.val (Unitary.star_eq_inv X)).symm
  rw [hInvEq U, hU', Matrix.conjTranspose_smul, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_conjTranspose, ← hInvEq u25, ← QRegister.embedUnitary_val]
open Classical in
theorem SupportedOnSel25.comm_of_disj {N k : ℕ} {rEmb : QRegister (3924 + 3 + 7) N}
    {rOther : QRegister k N} (hDisj : (rEmb.compose sel25InCat).DisjointWires rOther)
    {U : Unitary (2 ^ (3924 + 3 + 7))} (hU : SupportedOnSel25 U) : CommutesWithReg rOther
    (rEmb.embedUnitary U).1 := by
  obtain ⟨c, u25, hU'⟩ := hU
  intro A
  have hE : (rEmb.embedUnitary U).1 = c • ((rEmb.compose sel25InCat).embedUnitary u25).1 := by
    rw [QRegister.embedUnitary_val, hU', rEmb.embedMatrix_smul,
        QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, QRegister.embedUnitary_val]
  rw [hE, Matrix.smul_mul, Matrix.mul_smul, QRegister.embedUnitary_val,
      (rEmb.compose sel25InCat).embedMatrix_comm_of_disjoint rOther hDisj u25.1 A]
open Classical in
theorem supportedOnSel25_axisProdPrefix3 (u6 : Fin 3 → Unitary 64) :
    SupportedOnSel25 (rIdInCat.embedUnitary (axisProdPrefix 3 hL3_le_654 u6)) := by
  let rAx25 (i : Fin 3) : QRegister 6 (18 + 7) :=
    QRegister.block (6 * i.val) 6 (by have := i.isLt; omega)
  have hAxEq : ∀ i : Fin 3,
      rIdInCat.compose (rAxisPrefix 3 hL3_le_654 i) = sel25InCat.compose (rAx25 i) := fun i ↦ by
    apply qreg_ext; intro q
    have hlt : (sel25InCat (rAx25 i q)).val = 6 * i.val + q.val := by
      have : (rAx25 i q).val < 18 := by
        have := i.isLt; have := q.isLt; simp [rAx25]; omega
      have hCast : rAx25 i q = Fin.castAdd 7 ⟨(rAx25 i q).val, this⟩ := Fin.ext rfl
      rw [hCast, sel25InCat, QRegister.concat_apply_left]
      simp [rAx25, sel18InSys, rIdInCat]
    apply Fin.ext
    change (rIdInCat (rAxisPrefix 3 hL3_le_654 i q)).val = (sel25InCat (rAx25 i q)).val
    rw [hlt]
    simp [rIdInCat, rAxisPrefix, DyadicQft64WalkCircuit.rAxis654]
  have hProd : axisProdPrefix 3 hL3_le_654 u6 = (rAxisPrefix 3 hL3_le_654 0).embedUnitary
      (u6 0) * ((rAxisPrefix 3 hL3_le_654 1).embedUnitary (u6 1) * (rAxisPrefix 3 hL3_le_654
      2).embedUnitary (u6 2)) := by
    dsimp only [axisProdPrefix]
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
        List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
    rfl
  refine ⟨1, (rAx25 0).embedUnitary (u6 0) *
    ((rAx25 1).embedUnitary (u6 1) * (rAx25 2).embedUnitary (u6 2)), ?_⟩
  rw [one_smul, hProd]
  simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, hAxEq]
theorem supportedOnSel25_of_realizes_25 (S : CanonStageSpec128) (h25 : ∃ u25 : Unitary (2 ^
    (18 + 7)), RealizesEmbeddedUnitaryWithCleanWorkspace (rQftCanon128.compose sel25InCat)
    rWorkCanon128 u25 S.dFwd) : SupportedOnSel25 S.uCat := by
  obtain ⟨u25, hRF25⟩ := h25
  obtain ⟨c, hc⟩ := realizes_eq_smul_of_same rQftCanon128_disjoint_rWorkCanon128
    S.hRealFwd hRF25.widenActive
  exact ⟨c, u25, hc⟩
theorem xorForestBatchFwdDyn128_0_3_realizes_25 (s : ℕ) (cfg : ForestSlotConfig s)
    (hs : s ≤ 3) (hL : 1 ≤ 3) (hoff : 0 + 3 ≤ 654) (hwMax : xorForestBatchWork s cfg 3 ≤ 128)
    (hEqDyn : xorForestBatchFwdDyn128 s 0 3 cfg hs hL hoff hwMax =
    StageAPointPhase128OnStep.xorForestBatchFwdDyn () s cfg 3 hs hL
    (le_refl (xorForestBatchWork s cfg 3)) (rSysCanon128.compose sel18InSys) rPGCanon128
    (rWorkCanon128.slice 0 (xorForestBatchWork s cfg 3) (Nat.zero_add _ ▸ hwMax))
    (rSysCanon128_disjoint_rPGCanon128.compose_left sel18InSys)
    ((rSysCanon128_disjoint_rWorkCanon128.compose_left sel18InSys).compose_right _)
    (rPGCanon128_disjoint_rWorkCanon128.compose_right _) idxForestAx18 idxForestAx18_inj) : ∃
    u25 : Unitary (2 ^ (18 + 7)), RealizesEmbeddedUnitaryWithCleanWorkspace
    (rQftCanon128.compose sel25InCat) rWorkCanon128 u25
    (xorForestBatchFwdDyn128 s 0 3 cfg hs hL hoff hwMax) := by
  obtain ⟨_, _, _, _, hRest⟩ := xorForestBatch_spec () s cfg 3 hs hL
      (le_refl (xorForestBatchWork s cfg 3)) (rSysCanon128.compose sel18InSys) rPGCanon128
      (rWorkCanon128.slice 0 (xorForestBatchWork s cfg 3) (Nat.zero_add _ ▸ hwMax))
      (rSysCanon128_disjoint_rPGCanon128.compose_left sel18InSys)
      ((rSysCanon128_disjoint_rWorkCanon128.compose_left sel18InSys).compose_right _)
      (rPGCanon128_disjoint_rWorkCanon128.compose_right _) idxForestAx18 idxForestAx18_inj
  obtain ⟨Φ₁₈, uLow₁₈, _, hRF18, _⟩ := hRest
  rw [← hEqDyn] at hRF18
  exact ⟨DyadicQft64WalkCircuit288.apexCatUnitary 18 s hs Φ₁₈ uLow₁₈,
    DyadicQft64WalkCircuit.realizes_congr_slice
      (Nat.zero_add _ ▸ hwMax) concat_sel18InSys_rPGCanon128_eq hRF18⟩
section UnfoldForestFwdDyn
open DyadicQft64WalkCircuit (finMapList)
open StageAPointPhase128OnStep (cnotPairsCircuit axisCnotPairs batchCnotPairs expandColWires
  idxForestAx idxForestAx_inj)
attribute [local semireducible]
  StageAPointPhase128OnStep.xorForestBatchFwdDyn
private theorem axisCnotPairs_congr {n k₁ k₂ : ℕ} (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (g₁ : Fin 6 → Fin k₁) (g₂ : Fin 6 → Fin k₂) (hW : ∀ q : Fin 6, r₁ (g₁ q) = r₂ (g₂ q))
    (pairs6 : List (Fin 6 × Fin 6)) : axisCnotPairs r₁ g₁ pairs6 = axisCnotPairs r₂ g₂ pairs6
    := by
  simp only [axisCnotPairs, hW]
private theorem batchCnotPairs_congr {n k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ} (idx₁ : Fin L → Fin 6 → Fin k₁) (idx₂ : Fin L → Fin 6 → Fin k₂),
      (∀ (l : Fin L) (q : Fin 6), r₁ (idx₁ l q) = r₂ (idx₂ l q)) →
      batchCnotPairs r₁ pairs6 idx₁ = batchCnotPairs r₂ pairs6 idx₂
  | 0, _, _, _ => rfl
  | _ + 1, idx₁, idx₂, hW => by
      simp only [batchCnotPairs, axisCnotPairs_congr r₁ r₂ (idx₁ 0) (idx₂ 0) (hW 0),
        batchCnotPairs_congr r₁ r₂ pairs6 (fun l ↦ idx₁ l.succ) (fun l ↦ idx₂ l.succ)
          (fun l q ↦ hW l.succ q)]
private theorem expandColWires_congr {n L k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (idx₁ : Fin L → Fin 6 → Fin k₁) (idx₂ : Fin L → Fin 6 → Fin k₂)
    (hW : ∀ (l : Fin L) (q : Fin 6), r₁ (idx₁ l q) = r₂ (idx₂ l q)) :
    ∀ (qs : List (Fin 6)), expandColWires r₁ idx₁ qs = expandColWires r₂ idx₂ qs
  | [] => rfl
  | q :: qs => by
      have hf : (fun l : Fin L ↦ r₁ (idx₁ l q)) = (fun l : Fin L ↦ r₂ (idx₂ l q)) :=
        funext fun l ↦ hW l q
      simp only [expandColWires, hf, expandColWires_congr r₁ r₂ idx₁ idx₂ hW qs]
private theorem cnotPairsCircuit_congr {n : ℕ} {wp₁ wp₂ : List (Wire n × Wire n)}
    (hw : wp₁ = wp₂) (h₁ : ∀ p ∈ wp₁, p.1 ≠ p.2) (h₂ : ∀ p ∈ wp₂, p.1 ≠ p.2) :
    cnotPairsCircuit wp₁ h₁ = cnotPairsCircuit wp₂ h₂ := by
  subst hw; rfl
private theorem compressBuckets_congr {n m_anc : ℕ} (rAnc : QRegister m_anc n)
    {b₁ b₂ : List (List (Wire n))} (hb : b₁ = b₂)
    (hf₁ : 0 + DyadicQft64.compressStepsCount b₁ 0 ≤ m_anc) (hn₁ : ∀ B ∈ b₁, B.Nodup)
    (hd₁ : b₁.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂) (ha₁ : ∀ B ∈ b₁, ∀ x ∈ B, x ∉ rAnc.image)
    (hf₂ : 0 + DyadicQft64.compressStepsCount b₂ 0 ≤ m_anc) (hn₂ : ∀ B ∈ b₂, B.Nodup)
    (hd₂ : b₂.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂) (ha₂ : ∀ B ∈ b₂, ∀ x ∈ B, x ∉ rAnc.image)
    : DyadicQft64.compressBuckets rAnc b₁ 0 hf₁ hn₁ hd₁ ha₁ = DyadicQft64.compressBuckets rAnc
    b₂ 0 hf₂ hn₂ hd₂ ha₂ := by
  subst hb; rfl
private theorem forestTail_congr {Var : Type} {n mWork : ℕ}
    (v : Var) (s : ℕ) (hs : s ≤ 3)
    (rPG : QRegister 7 n) (rWork : QRegister mWork n)
    {cF₁ cF₂ cI₁ cI₂ : Circuit n} (hcF : cF₁ = cF₂) (hcI : cI₁ = cI₂)
    {out₁ out₂ : DyadicQft64.CompressOut n} (hout : out₁ = out₂)
    {wCin₁ wCin₂ : Wire n} (hwc : wCin₁ = wCin₂)
    (hm₁ : 0 + out₁.steps.length + (4 - s) ≤ mWork)
    (hm₂ : 0 + out₂.steps.length + (4 - s) ≤ mWork)
    (hz₁ : out₁.steps.length + (4 - s) < mWork)
    (hz₂ : out₂.steps.length + (4 - s) < mWork)
    (hsw₁ : ∀ j : Fin (4 - s), j.val < out₁.sumWires.length)
    (hsw₂ : ∀ j : Fin (4 - s), j.val < out₂.sumWires.length)
    (huT₁ : ∀ j : Fin (4 - s),
      DyadicQft64.optWireOrZero (rWork ⟨out₁.steps.length + (4 - s), hz₁⟩)
        (out₁.sumWires.get ⟨j.val, hsw₁ j⟩) ∉ (rPG.slice s (4 - s) (by omega)).image)
    (huC₁ : ∀ j : Fin (4 - s),
      DyadicQft64.optWireOrZero (rWork ⟨out₁.steps.length + (4 - s), hz₁⟩)
        (out₁.sumWires.get ⟨j.val,
          hsw₁ j⟩) ∉ (rWork.slice (0 + out₁.steps.length) (4 - s) hm₁).image)
    (hTC₁ : (rPG.slice s (4 - s) (by
      omega)).DisjointWires (rWork.slice (0 + out₁.steps.length) (4 - s) hm₁))
    (hcU₁ : ∀ j : Fin (4 - s),
      wCin₁ ≠ DyadicQft64.optWireOrZero (rWork ⟨out₁.steps.length + (4 - s), hz₁⟩)
        (out₁.sumWires.get ⟨j.val, hsw₁ j⟩))
    (hcT₁ : wCin₁ ∉ (rPG.slice s (4 - s) (by omega)).image)
    (hcC₁ : wCin₁ ∉ (rWork.slice (0 + out₁.steps.length) (4 - s) hm₁).image)
    (huT₂ : ∀ j : Fin (4 - s),
      DyadicQft64.optWireOrZero (rWork ⟨out₂.steps.length + (4 - s), hz₂⟩)
        (out₂.sumWires.get ⟨j.val, hsw₂ j⟩) ∉ (rPG.slice s (4 - s) (by omega)).image)
    (huC₂ : ∀ j : Fin (4 - s),
      DyadicQft64.optWireOrZero (rWork ⟨out₂.steps.length + (4 - s), hz₂⟩)
        (out₂.sumWires.get ⟨j.val,
          hsw₂ j⟩) ∉ (rWork.slice (0 + out₂.steps.length) (4 - s) hm₂).image)
    (hTC₂ : (rPG.slice s (4 - s) (by
      omega)).DisjointWires (rWork.slice (0 + out₂.steps.length) (4 - s) hm₂))
    (hcU₂ : ∀ j : Fin (4 - s),
      wCin₂ ≠ DyadicQft64.optWireOrZero (rWork ⟨out₂.steps.length + (4 - s), hz₂⟩)
        (out₂.sumWires.get ⟨j.val, hsw₂ j⟩))
    (hcT₂ : wCin₂ ∉ (rPG.slice s (4 - s) (by omega)).image)
    (hcC₂ : wCin₂ ∉ (rWork.slice (0 + out₂.steps.length) (4 - s) hm₂).image) :
    (DynamicCircuit.circuit cF₁).seq
      ((DyadicQft64.symWrapDynList v out₁.steps
        ((DynamicCircuit.circuit (DyadicQft64.tList out₁.carries)).seq
          ((DyadicQft64WalkCircuit288.gidneyApexChainDyn v false (4 - s)
              (fun j ↦ DyadicQft64.optWireOrZero (rWork ⟨out₁.steps.length + (4 - s), hz₁⟩)
                (out₁.sumWires.get ⟨j.val, hsw₁ j⟩))
              (rPG.slice s (4 - s) (by omega))
              (rWork.slice (0 + out₁.steps.length) (4 - s) hm₁)
              wCin₁ huT₁ huC₁ hTC₁ hcU₁ hcT₁ hcC₁).seq
            (DynamicCircuit.circuit Circuit.identity)))).seq
        (DynamicCircuit.circuit cI₁)) =
    (DynamicCircuit.circuit cF₂).seq
      ((DyadicQft64.symWrapDynList v out₂.steps
        ((DynamicCircuit.circuit (DyadicQft64.tList out₂.carries)).seq
          ((DyadicQft64WalkCircuit288.gidneyApexChainDyn v false (4 - s)
              (fun j ↦ DyadicQft64.optWireOrZero (rWork ⟨out₂.steps.length + (4 - s), hz₂⟩)
                (out₂.sumWires.get ⟨j.val, hsw₂ j⟩))
              (rPG.slice s (4 - s) (by omega))
              (rWork.slice (0 + out₂.steps.length) (4 - s) hm₂)
              wCin₂ huT₂ huC₂ hTC₂ hcU₂ hcT₂ hcC₂).seq
            (DynamicCircuit.circuit Circuit.identity)))).seq
        (DynamicCircuit.circuit cI₂)) := by
  subst hcF; subst hcI; subst hout; subst hwc
  have hhsw : hsw₁ = hsw₂ := funext fun _ ↦ Subsingleton.elim _ _
  subst hhsw
  rfl
private theorem xorForestBatchFwdDyn_congr_wires {Var : Type} {n k₁ k₂ mWork : ℕ} (v : Var)
    (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) (hs : s ≤ 3) (hL : 1 ≤ L)
    (hm : xorForestBatchWork s cfg L ≤ mWork) (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (rPG : QRegister 7 n) (rWork : QRegister mWork n) (hSP₁ : r₁.DisjointWires rPG)
    (hSW₁ : r₁.DisjointWires rWork) (hSP₂ : r₂.DisjointWires rPG)
    (hSW₂ : r₂.DisjointWires rWork) (hPW : rPG.DisjointWires rWork)
    (idx₁ : Fin L → Fin 6 → Fin k₁)
    (hinj₁ : Function.Injective (fun p : Fin L × Fin 6 ↦ idx₁ p.1 p.2))
    (idx₂ : Fin L → Fin 6 → Fin k₂)
    (hinj₂ : Function.Injective (fun p : Fin L × Fin 6 ↦ idx₂ p.1 p.2))
    (hW : ∀ (l : Fin L) (q : Fin 6), r₁ (idx₁ l q) = r₂ (idx₂ l q)) :
    StageAPointPhase128OnStep.xorForestBatchFwdDyn v s cfg L hs hL hm
    r₁ rPG rWork hSP₁ hSW₁ hPW idx₁ hinj₁ =
    StageAPointPhase128OnStep.xorForestBatchFwdDyn v s cfg L hs hL hm
    r₂ rPG rWork hSP₂ hSW₂ hPW idx₂ hinj₂ := by
  unfold StageAPointPhase128OnStep.xorForestBatchFwdDyn
    StageAPointPhase128OnStep.xorForestBatchDyn
  dsimp only [↓reduceIte]
  have hwp : batchCnotPairs r₁ cfg.pairs idx₁ = batchCnotPairs r₂ cfg.pairs idx₂ :=
    batchCnotPairs_congr r₁ r₂ cfg.pairs idx₁ idx₂ hW
  have hc0 : (fun i : Fin (L - 1) ↦ r₁ (idx₁ ⟨i.val + 1, by omega⟩ cfg.qCin0)) =
      (fun i : Fin (L - 1) ↦ r₂ (idx₂ ⟨i.val + 1, by omega⟩ cfg.qCin0)) :=
    funext fun i ↦ hW ⟨i.val + 1, by omega⟩ cfg.qCin0
  have hcr : (fun r : Fin (3 - s) ↦ expandColWires r₁ idx₁ (cfg.colRest6 r)) =
      (fun r : Fin (3 - s) ↦ expandColWires r₂ idx₂ (cfg.colRest6 r)) :=
    funext fun r ↦ expandColWires_congr r₁ r₂ idx₁ idx₂ hW (cfg.colRest6 r)
  have hb : (finMapList (fun i : Fin (L - 1) ↦ r₁ (idx₁ ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
        expandColWires r₁ idx₁ cfg.col0Tail6) ::
        finMapList (fun r : Fin (3 - s) ↦ expandColWires r₁ idx₁ (cfg.colRest6 r)) =
      (finMapList (fun i : Fin (L - 1) ↦ r₂ (idx₂ ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
        expandColWires r₂ idx₂ cfg.col0Tail6) ::
        finMapList (fun r : Fin (3 - s) ↦ expandColWires r₂ idx₂ (cfg.colRest6 r)) := by
    rw [hc0, expandColWires_congr r₁ r₂ idx₁ idx₂ hW cfg.col0Tail6, hcr]
  exact forestTail_congr v s hs rPG rWork (cnotPairsCircuit_congr hwp _ _)
    (cnotPairsCircuit_congr (congrArg List.reverse hwp) _ _)
    (compressBuckets_congr rWork hb _ _ _ _ _ _ _ _) (hW ⟨0, hL⟩ cfg.qCin0) _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _
theorem xorForestBatchFwdDyn128_0_3_eq (s : ℕ) (cfg : ForestSlotConfig s) (hs : s ≤ 3)
    (hL : 1 ≤ 3) (hoff : 0 + 3 ≤ 654) (hwMax : xorForestBatchWork s cfg 3 ≤ 128) :
    xorForestBatchFwdDyn128 s 0 3 cfg hs hL hoff hwMax =
    StageAPointPhase128OnStep.xorForestBatchFwdDyn () s cfg 3 hs hL
    (le_refl (xorForestBatchWork s cfg 3)) (rSysCanon128.compose sel18InSys) rPGCanon128
    (rWorkCanon128.slice 0 (xorForestBatchWork s cfg 3) (Nat.zero_add _ ▸ hwMax))
    (rSysCanon128_disjoint_rPGCanon128.compose_left sel18InSys)
    ((rSysCanon128_disjoint_rWorkCanon128.compose_left sel18InSys).compose_right _)
    (rPGCanon128_disjoint_rWorkCanon128.compose_right _) idxForestAx18 idxForestAx18_inj := by
  unfold xorForestBatchFwdDyn128
  refine xorForestBatchFwdDyn_congr_wires () s cfg 3 hs hL _
    rSysCanon128 (rSysCanon128.compose sel18InSys) rPGCanon128 _ _ _ _ _ _
    (idxForestAx 0 3 hoff) (idxForestAx_inj 0 3 hoff) idxForestAx18 idxForestAx18_inj ?_
  intro l q
  rw [QRegister.compose_apply]
  exact congrArg rSysCanon128 (Fin.ext (by simp [idxForestAx, sel18InSys, idxForestAx18]))
end UnfoldForestFwdDyn
theorem supportedOnSel25_stagePointCrossExp : SupportedOnSel25 stagePointCrossExpC5.uCat ∧
    SupportedOnSel25 stagePointCrossExpC4.uCat ∧ SupportedOnSel25 stagePointCrossExpC3.uCat ∧
    SupportedOnSel25 stagePointCrossExpC2.uCat ∧ SupportedOnSel25 stagePointCrossExpC1.uCat
    := by
  have hW16 : ∀ k : Fin 5, SupportedOnSel25 (stageW16PrefixCanonStage128 3 hL3_le_654 k).uCat :=
    fun k ↦ supportedOnSel25_axisProdPrefix3 _
  have hSeq : ∀ {A B : CanonStageSpec128}, SupportedOnSel25 A.uCat → SupportedOnSel25 B.uCat →
      SupportedOnSel25 (A.seq B).uCat := fun hA hB ↦ hB.mul hA
  exact ⟨hW16 4, hSeq (hW16 3) (supportedOnSel25_of_realizes_25 _
    (xorForestBatchFwdDyn128_0_3_realizes_25 3 forestCfg3 (by decide) (by decide) (by decide)
    (by decide) (xorForestBatchFwdDyn128_0_3_eq 3 forestCfg3 (by decide) (by decide)
    (by decide) (by decide)))), hSeq (hW16 2) (supportedOnSel25_of_realizes_25 _
    (xorForestBatchFwdDyn128_0_3_realizes_25 2 forestCfg2 (by decide) (by decide) (by decide)
    (by decide) (xorForestBatchFwdDyn128_0_3_eq 2 forestCfg2 (by decide) (by decide)
    (by decide) (by decide)))), hSeq (hW16 1) (supportedOnSel25_of_realizes_25 _
    (xorForestBatchFwdDyn128_0_3_realizes_25 1 forestCfg1 (by decide) (by decide) (by decide)
    (by decide) (xorForestBatchFwdDyn128_0_3_eq 1 forestCfg1 (by decide) (by decide)
    (by decide) (by decide)))), hSeq (hW16 0) (supportedOnSel25_of_realizes_25 _
    (xorForestBatchFwdDyn128_0_3_realizes_25 0 forestCfg0 (by decide) (by decide) (by decide)
    (by decide) (xorForestBatchFwdDyn128_0_3_eq 0 forestCfg0 (by decide) (by decide)
    (by decide) (by decide))))⟩
theorem supportedOnSel25_activeOneElecExpQftStage128 :
    SupportedOnSel25 activeOneElecExpQftStage128.uCat := by
  obtain ⟨hC5, hC4, hC3, hC2, hC1⟩ := supportedOnSel25_stagePointCrossExp
  have hH : ∀ kf : Fin 6, SupportedOnSel25 (stageHPrefixCanonStage128 3 hL3_le_654 kf).uCat :=
    fun kf ↦ supportedOnSel25_axisProdPrefix3 _
  have hSeq : ∀ {A B : CanonStageSpec128}, SupportedOnSel25 A.uCat → SupportedOnSel25 B.uCat →
      SupportedOnSel25 (A.seq B).uCat := fun hA hB ↦ hB.mul hA
  change SupportedOnSel25 rawActiveOneElecExpQftStage128.uCat
  unfold rawActiveOneElecExpQftStage128
  exact hSeq (hSeq (hH 5) hC5) (hSeq (hSeq (hH 4) hC4) (hSeq (hSeq (hH 3) hC3) (hSeq (hSeq (hH
    2) hC2) (hSeq (hSeq (hH 1) hC1) (hH 0)))))
set_option exponentiation.threshold 8192
theorem rActStageAFull80_compose_core_eq :
    (rActStageAFull80.compose selCoreSum42InAct).compose (rCoreInCoreSum42 80) = rCoreFull := by
  apply qreg_ext; intro i
  have hi : selCoreSum42InAct (rCoreInCoreSum42 80 i) = Fin.castAdd 7 (Fin.castAdd 42 i) :=
    Fin.ext (by simp [selCoreSum42InAct, rCoreInCoreSum42])
  rw [QRegister.compose_apply, QRegister.compose_apply, hi]
  dsimp only [rActStageAFull80]; rw [QRegister.concat_apply_left]
  dsimp only [rCSFull80]; rw [QRegister.concat_apply_left]
theorem selCatInCoreSum42PG7_sel25InCat_val_lt18_or_ge4076 (idx : Fin (18 + 7)) :
    (selCatInCoreSum42PG7 (sel25InCat idx)).val < 18 ∨
      fullSysCoreWires 80 + 42 ≤ (selCatInCoreSum42PG7 (sel25InCat idx)).val := by
  have h4076_le : fullSysCoreWires 80 + 42 ≤ kCoreSum42PG7 := by
    rw [fullSysCoreWires80_eq_4034_assoc, kCoreSum42PG7_eq_4083_assoc]; omega
  let rAct0 : QRegister (fullSysCoreWires 80 + 42) kCoreSum42PG7 :=
    .block 0 (fullSysCoreWires 80 + 42) h4076_le
  let rCat0 : QRegister 7 kCoreSum42PG7 := .block (fullSysCoreWires 80 + 42) 7 le_rfl
  have hDisj0 : rAct0.DisjointWires rCat0 := disjoint_block_sep (Or.inl (by omega))
  have hIdCS : rAct0.concat rCat0 hDisj0 = QRegExt.idReg kCoreSum42PG7 := by
    apply qreg_ext; intro q; refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) q
    · rw [QRegister.concat_apply_left]; exact Fin.ext (by simp [rAct0, QRegExt.idReg])
    · rw [QRegister.concat_apply_right]; exact Fin.ext (by simp [rCat0, QRegExt.idReg])
  have hSelCatEq : (rAct0.compose rIdInCoreSum42).concat
        rCat0 (hDisj0.compose_left _) = selCatInCoreSum42PG7 := by
    rw [← concat_compose_selCatInCoreSum42PG7 rAct0 rCat0 hDisj0, hIdCS]
    rfl
  rw [← hSelCatEq]
  refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) idx
  · left
    let jSys : Fin (3924 + 3) := sel18InSys i
    have hi : sel25InCat (Fin.castAdd 7 i) = Fin.castAdd 7 jSys := by
      change ((rIdInCat.compose sel18InSys).concat rPGInCat _) (Fin.castAdd 7 i) =
        Fin.castAdd 7 jSys
      rw [QRegister.concat_apply_left]
      exact Fin.ext (by simp [jSys, sel18InSys, rIdInCat])
    change (((rAct0.compose rIdInCoreSum42).concat
      rCat0 (hDisj0.compose_left _)) (sel25InCat (Fin.castAdd 7 i))).val < 18
    rw [hi, QRegister.concat_apply_left]
    have hAct0 : ((rAct0.compose rIdInCoreSum42) jSys).val = (rIdInCoreSum42 jSys).val := by
      simp [rAct0]
    have hv := rIdInCoreSum42_wires_val_of_lt3924_assoc jSys (by
      have := i.isLt; simp [jSys, sel18InSys]; omega)
    rw [hAct0, hv]
    simp [jSys, sel18InSys]
  · right
    have hk : sel25InCat (Fin.natAdd 18 k) = Fin.natAdd (3924 + 3) k := by
      change ((rIdInCat.compose sel18InSys).concat rPGInCat _) (Fin.natAdd 18 k) =
        Fin.natAdd (3924 + 3) k
      rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [rPGInCat])
    change fullSysCoreWires 80 + 42 ≤ (((rAct0.compose rIdInCoreSum42).concat rCat0
      (hDisj0.compose_left _)) (sel25InCat (Fin.natAdd 18 k))).val
    rw [hk, QRegister.concat_apply_right]
    simp [rCat0]
open Classical in
theorem uSlot0MeasSwap_conj_uSlot0Sum42Add_eq :
    let U := rActStageAFull80.embedUnitary (selCoreSum42InAct.embedUnitary (uSlot0Sum42Add 80))
    (uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary U * uSlot0MeasSwap = uAnchorFrame U) ∧
    (uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary U⁻¹ * uSlot0MeasSwap =
      uAnchorFrame U⁻¹) := by
  intro U
  have hSpecCS : ActsAsIdOnSpectatorWires (rCoreInCoreSum42 80) (uSlot0Sum42Add 80) :=
    commutesWithReg_uSlot0Sum42Add_of_mid_assoc (spectatorElecReg (rCoreInCoreSum42 80))
      (fun t ↦ by simp [spectatorElecReg, rCoreInCoreSum42])
      (fun t ↦ by
        have := t.isLt
        simp [spectatorElecReg, rCoreInCoreSum42, fullSysCoreWires80_eq_4034_assoc]
        omega)
  have hHighCS : PreservesHigh3924On (rCoreInCoreSum42 80) (uSlot0Sum42Add 80) := fun w hw b ↦
    commutesWithReg_uSlot0Sum42Add_of_mid_assoc (QRegister.singleton (rCoreInCoreSum42 80 w))
      (fun _ ↦ by simp [QRegister.singleton, rCoreInCoreSum42]; omega)
      (fun _ ↦ by simp [QRegister.singleton, rCoreInCoreSum42]) _
  have hSpecInvCS : ActsAsIdOnSpectatorWires (rCoreInCoreSum42 80) (uSlot0Sum42Add 80)⁻¹ :=
    fun A ↦ unitary_val_inv_comm_of_comm (uSlot0Sum42Add 80) (hSpecCS A)
  have hHighInvCS : PreservesHigh3924On (rCoreInCoreSum42 80) (uSlot0Sum42Add 80)⁻¹ :=
    fun w hw b ↦ unitary_val_inv_comm_of_comm (uSlot0Sum42Add 80) (hHighCS w hw b)
  have hUEq : U = (rActStageAFull80.compose selCoreSum42InAct).embedUnitary (uSlot0Sum42Add 80) :=
    by
    dsimp only [U]; rw [QRegister.embedUnitary_compose]
  have hUInvEq : U⁻¹ =
    (rActStageAFull80.compose selCoreSum42InAct).embedUnitary (uSlot0Sum42Add 80)⁻¹ := by
    rw [hUEq, embedUnitary_inv_symm]
  refine ⟨uSlot0MeasSwap_conj_eq_uAnchorFrame U ?_ ?_,
    uSlot0MeasSwap_conj_eq_uAnchorFrame U⁻¹ ?_ ?_⟩
  · rw [hUEq, ← rActStageAFull80_compose_core_eq]
    exact actsAsIdOnSpectatorWires_embed _ _ hSpecCS
  · rw [hUEq, ← rActStageAFull80_compose_core_eq]
    exact preservesHigh3924On_embed _ _ hHighCS
  · rw [hUInvEq, ← rActStageAFull80_compose_core_eq]
    exact actsAsIdOnSpectatorWires_embed _ _ hSpecInvCS
  · rw [hUInvEq, ← rActStageAFull80_compose_core_eq]
    exact preservesHigh3924On_embed _ _ hHighInvCS
open Classical in
theorem uSlot0MeasSwap_conj_activeOneElecExpQft_eq :
    let U := rActStageAFull80.embedUnitary
      (selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat)
    (uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary U * uSlot0MeasSwap = uAnchorFrame U) ∧
    (uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary U⁻¹ * uSlot0MeasSwap =
      uAnchorFrame U⁻¹) := by
  intro U
  let rCoreInAct : QRegister (fullSysCoreWires 80) kCoreSum42PG7 :=
    selCoreSum42InAct.compose (rCoreInCoreSum42 80)
  have hMidDisj : ∀ {k : ℕ} (rMid : QRegister k kCoreSum42PG7),
      (∀ t : Fin k, 18 ≤ (rMid t).val ∧ (rMid t).val < fullSysCoreWires 80 + 42) →
      (selCatInCoreSum42PG7.compose sel25InCat).DisjointWires rMid := by
    intro k rMid hBnd
    rw [QRegister.disjoint_iff]
    intro idx t hEq
    have hv := congrArg Fin.val hEq
    change (selCatInCoreSum42PG7 (sel25InCat idx)).val = (rMid t).val at hv
    obtain ⟨h18, h4076⟩ := hBnd t
    rcases selCatInCoreSum42PG7_sel25InCat_val_lt18_or_ge4076 idx with hlt | hge <;> omega
  have hForQ : ∀ {Q : Unitary (2 ^ (3924 + 3 + 7))}, SupportedOnSel25 Q →
      ActsAsIdOnSpectatorWires rCoreInAct (selCatInCoreSum42PG7.embedUnitary Q) ∧
      PreservesHigh3924On rCoreInAct (selCatInCoreSum42PG7.embedUnitary Q) := by
    intro Q hQ
    refine ⟨?_, fun w hw b ↦ ?_⟩
    · refine hQ.comm_of_disj (hMidDisj (spectatorElecReg rCoreInAct) fun t ↦ ?_)
      have := t.isLt
      simp [spectatorElecReg, rCoreInAct, selCoreSum42InAct, rCoreInCoreSum42,
        fullSysCoreWires80_eq_4034_assoc]
      omega
    · refine hQ.comm_of_disj (hMidDisj (QRegister.singleton (rCoreInAct w)) fun _ ↦ ?_) _
      have := w.isLt
      simp [QRegister.singleton, rCoreInAct, selCoreSum42InAct, rCoreInCoreSum42]
      omega
  obtain ⟨hSpec0, hHigh0⟩ := hForQ supportedOnSel25_activeOneElecExpQftStage128
  obtain ⟨hSpecI, hHighI⟩ := hForQ supportedOnSel25_activeOneElecExpQftStage128.inv
  have hCoreEq : rActStageAFull80.compose rCoreInAct = rCoreFull := rActStageAFull80_compose_core_eq
  have hUInvEq : U⁻¹ = rActStageAFull80.embedUnitary
      (selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat⁻¹) := by
    dsimp only [U]; rw [embedUnitary_inv_symm, embedUnitary_inv_symm]
  refine ⟨uSlot0MeasSwap_conj_eq_uAnchorFrame U ?_ ?_,
    uSlot0MeasSwap_conj_eq_uAnchorFrame U⁻¹ ?_ ?_⟩
  · rw [← hCoreEq]; exact actsAsIdOnSpectatorWires_embed _ _ hSpec0
  · rw [← hCoreEq]; exact preservesHigh3924On_embed _ _ hHigh0
  · rw [hUInvEq, ← hCoreEq]; exact actsAsIdOnSpectatorWires_embed _ _ hSpecI
  · rw [hUInvEq, ← hCoreEq]; exact preservesHigh3924On_embed _ _ hHighI
/-! ## Part 2C: `234 T` `218`-Slot `dPhiOnHeldZ18AnchorFwd128` / `Inv128` & Non-`rCore` Commutation
-/
/-- `0-T`, `0-TOFF` selector for Electron `0` (`0..17`) inside `kHeldZ18Act`. -/
def selSlot0InHeldZ18Act : QRegister 18 kHeldZ18Act :=
  selHeldZ18SysInAct.compose (selCoreInHeldZ18Sys.compose (rElecSlot (QRegExt.idReg posCoreWires)
    0))
/-- `117-T`, `0-TOFF` forward 3-axis Point-`QFT_64` + `218`-slot Clifford circuit on `(rCore,
  rSum42, rZ18, rPG7)`. -/
noncomputable def dPhiOnHeldZ18AnchorFwd128 {Var : Type} {n mWork : ℕ} (hm : 128 ≤ mWork)
    (v : Var) (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) : DynamicCircuit Var n := .seq
    (dPhiOnHeldZ18Fwd128 hm v rAct rWork hAW) (.circuit (cPointElec18.onRegister (rAct.compose
    selSlot0InHeldZ18Act)))
/-- `117-T`, `0-TOFF` inverse 3-axis Point-`QFT_64` + `218`-slot Clifford circuit on `(rCore,
  rSum42, rZ18, rPG7)`. -/
noncomputable def dPhiOnHeldZ18AnchorInv128 {Var : Type} {n mWork : ℕ} (hm : 128 ≤ mWork)
    (v : Var) (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) : DynamicCircuit Var n := .seq (.circuit
    (cPointElec18.inverse.onRegister (rAct.compose selSlot0InHeldZ18Act)))
    (dPhiOnHeldZ18Inv128 hm v rAct rWork hAW)
/-- `218`-slot core Point-QFT Clifford unitary (`uPointElec18` on `slot[0]` + `uPointElec217Core`
  on `1..217`). -/
noncomputable def uPointElec218Core : Unitary (2 ^ posCoreWires) :=
  (rElecSlot (QRegExt.idReg posCoreWires) 0).embedUnitary uPointElec18 * uPointElec217Core
/-- Non-`rCore` prefix of `uPhiHeldZ18Cat` (`cPointSumClifford60` + `stagePointCrossExpC1..C5` on
  `(rSum42, rZ18, rPG7)`). -/
noncomputable def uPhiNonCoreCat : Unitary (2 ^ kHeldZ18Act) :=
  (selHeldZ18SysInAct.compose selZ18Sum42InHeldZ18Sys).embedUnitary uPointSumClifford60 *
    ((selHybridHeldZ18Cat 1).embedUnitary stagePointCrossExpC1.uCat *
      ((selHybridHeldZ18Cat 2).embedUnitary stagePointCrossExpC2.uCat *
        ((selHybridHeldZ18Cat 3).embedUnitary stagePointCrossExpC3.uCat *
          ((selHybridHeldZ18Cat 4).embedUnitary stagePointCrossExpC4.uCat *
            (selHybridHeldZ18Cat 5).embedUnitary stagePointCrossExpC5.uCat))))
/-- Catalyzed `218`-slot Point-QFT unitary on `2 ^ kHeldZ18Act` realized by
  `dPhiOnHeldZ18AnchorFwd128`. -/
noncomputable def uPhiHeldZ18AnchorCat : Unitary (2 ^ kHeldZ18Act) :=
  selSlot0InHeldZ18Act.embedUnitary uPointElec18 * uPhiHeldZ18Cat
open Classical in
theorem uPhiHeldZ18Cat_eq_elec217_mul_nonCore : uPhiHeldZ18Cat =
    (selHeldZ18SysInAct.compose selCoreInHeldZ18Sys).embedUnitary uPointElec217Core *
    uPhiNonCoreCat := rfl
open Classical in
theorem uPhiHeldZ18AnchorCat_eq_elec218_mul_nonCore :
    uPhiHeldZ18AnchorCat =
      (selHeldZ18SysInAct.compose selCoreInHeldZ18Sys).embedUnitary uPointElec218Core *
        uPhiNonCoreCat := by
  unfold uPhiHeldZ18AnchorCat uPointElec218Core selSlot0InHeldZ18Act
  rw [uPhiHeldZ18Cat_eq_elec217_mul_nonCore, QRegister.embedUnitary_mul,
      ← QRegister.embedUnitary_compose, QRegister.compose_assoc, _root_.mul_assoc]
open Classical in
theorem commutesWithReg_core_uPhiNonCoreCat :
    CommutesWithReg (selHeldZ18SysInAct.compose selCoreInHeldZ18Sys) uPhiNonCoreCat.1 := by
  let rC := selHeldZ18SysInAct.compose selCoreInHeldZ18Sys
  have hCVal : ∀ j : Fin posCoreWires, (rC j).val = j.val := fun j ↦ by
    simp [rC, selHeldZ18SysInAct, selCoreInHeldZ18Sys]
  have hHybDisj : ∀ c : ℕ, ((selHybridHeldZ18Cat c).compose sel25InCat).DisjointWires rC := by
    intro c; rw [QRegister.disjoint_iff]; intro idx j hEq
    have hv := congrArg Fin.val hEq
    change (selHybridHeldZ18Cat c (sel25InCat idx)).val = (rC j).val at hv
    rw [hCVal j] at hv
    have hj : j.val < fullSysCoreWires 80 :=
      j.isLt.trans_eq (posCoreWires_eq_4034_assoc.trans fullSysCoreWires80_eq_4034_assoc.symm)
    revert hv
    refine Fin.addCases (fun i hv ↦ ?_) (fun k hv ↦ ?_) idx
    · have hi18 : (sel25InCat (Fin.castAdd 7 i)).val < 18 := by
        have := i.isLt
        change (((rIdInCat.compose sel18InSys).concat rPGInCat _) (Fin.castAdd 7 i)).val < 18
        rw [QRegister.concat_apply_left]
        dsimp [sel18InSys, rIdInCat]; omega
      change selHybridHeldZ18Nat c (sel25InCat (Fin.castAdd 7 i)).val = j.val at hv
      unfold selHybridHeldZ18Nat at hv
      rw [ite_eq_left hi18] at hv
      split_ifs at hv <;> omega
    · have hk3927 : 3924 + 3 ≤ (sel25InCat (Fin.natAdd 18 k)).val := by
        change 3924 + 3 ≤ (((rIdInCat.compose sel18InSys).concat rPGInCat _) (Fin.natAdd 18 k)).val
        rw [QRegister.concat_apply_right]
        dsimp [rPGInCat]; omega
      change selHybridHeldZ18Nat c (sel25InCat (Fin.natAdd 18 k)).val = j.val at hv
      unfold selHybridHeldZ18Nat kHeldZ18Sys at hv
      rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hv
      omega
  have hSumDisj : (selHeldZ18SysInAct.compose selZ18Sum42InHeldZ18Sys).DisjointWires rC := by
    rw [QRegister.disjoint_iff]; intro idx j hEq
    have hv := congrArg Fin.val hEq
    change (selHeldZ18SysInAct (selZ18Sum42InHeldZ18Sys idx)).val = (rC j).val at hv
    rw [hCVal j] at hv
    have hj : j.val < fullSysCoreWires 80 :=
      j.isLt.trans_eq (posCoreWires_eq_4034_assoc.trans fullSysCoreWires80_eq_4034_assoc.symm)
    simp only [selHeldZ18SysInAct, selZ18Sum42InHeldZ18Sys, qreg_block_apply, zero_add,
      Function.Embedding.coeFn_mk] at hv
    split_ifs at hv <;> simp only at hv <;> omega
  obtain ⟨hC5, hC4, hC3, hC2, hC1⟩ := supportedOnSel25_stagePointCrossExp
  have hMul : ∀ {U V : Operator (2 ^ kHeldZ18Act)},
      CommutesWithReg rC U → CommutesWithReg rC V → CommutesWithReg rC (U * V) := by
    intro U V hU hV A
    rw [Matrix.mul_assoc, hV A, ← Matrix.mul_assoc, hU A, Matrix.mul_assoc]
  unfold uPhiNonCoreCat
  simp only [Submonoid.coe_mul]
  exact hMul (fun A ↦ (selHeldZ18SysInAct.compose
    selZ18Sum42InHeldZ18Sys).embedMatrix_comm_of_disjoint rC hSumDisj uPointSumClifford60.1 A)
    (hMul (hC1.comm_of_disj (hHybDisj 1)) (hMul (hC2.comm_of_disj (hHybDisj 2)) (hMul
    (hC3.comm_of_disj (hHybDisj 3)) (hMul (hC4.comm_of_disj (hHybDisj 4)) (hC5.comm_of_disj
    (hHybDisj 5))))))
@[simp] theorem count_dPhiOnHeldZ18AnchorFwd128_toff {Var : Type} {n mWork : ℕ}
    (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n) (hAW : rAct.DisjointWires rWork) :
    (dPhiOnHeldZ18AnchorFwd128 hm v rAct rWork hAW).count TOFF = 0 := by
  simp [dPhiOnHeldZ18AnchorFwd128]
@[simp] theorem count_dPhiOnHeldZ18AnchorInv128_toff {Var : Type} {n mWork : ℕ}
    (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n) (hAW : rAct.DisjointWires rWork) :
    (dPhiOnHeldZ18AnchorInv128 hm v rAct rWork hAW).count TOFF = 0 := by
  simp [dPhiOnHeldZ18AnchorInv128]
@[simp] theorem count_dPhiOnHeldZ18AnchorFwd128_t {Var : Type} {n mWork : ℕ}
    (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n) (hAW : rAct.DisjointWires rWork) :
    (dPhiOnHeldZ18AnchorFwd128 hm v rAct rWork hAW).count T = 117 := by
  simp [dPhiOnHeldZ18AnchorFwd128]
@[simp] theorem count_dPhiOnHeldZ18AnchorInv128_t {Var : Type} {n mWork : ℕ}
    (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n) (hAW : rAct.DisjointWires rWork) :
    (dPhiOnHeldZ18AnchorInv128 hm v rAct rWork hAW).count T = 117 := by
  simp [dPhiOnHeldZ18AnchorInv128]
open Classical in
theorem dPhiOnHeldZ18AnchorFwd128_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mWork : ℕ} [NeZero (2 ^ n)] (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
    uPhiHeldZ18AnchorCat (dPhiOnHeldZ18AnchorFwd128 hm v rAct rWork hAW) := by
  have hBase := dPhiOnHeldZ18Fwd128_realizes hm v rAct rWork hAW
  have hE0 : RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rAct rWork
      (selSlot0InHeldZ18Act.embedUnitary uPointElec18)
      (.circuit (cPointElec18.onRegister (rAct.compose selSlot0InHeldZ18Act))) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rAct rWork _ _ (by
      rw [Circuit.eval_onRegister, cPointElec18_eval, QRegister.embedUnitary_compose])
  exact hBase.seq hAW hE0
open Classical in
theorem dPhiOnHeldZ18AnchorInv128_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mWork : ℕ} [NeZero (2 ^ n)] (hm : 128 ≤ mWork) (v : Var)
    (rAct : QRegister kHeldZ18Act n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
    uPhiHeldZ18AnchorCat⁻¹ (dPhiOnHeldZ18AnchorInv128 hm v rAct rWork hAW) := by
  have hE0Inv : RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rAct rWork
      (selSlot0InHeldZ18Act.embedUnitary uPointElec18)⁻¹
      (.circuit (cPointElec18.inverse.onRegister (rAct.compose selSlot0InHeldZ18Act))) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rAct rWork _ _ (by
      rw [Circuit.eval_onRegister, Circuit.eval_inverse, cPointElec18_eval,
          QRegister.embedUnitary_compose, ← embedUnitary_inv_symm, ← embedUnitary_inv_symm])
  have hBaseInv := dPhiOnHeldZ18Inv128_realizes hm v rAct rWork hAW
  have hSeq := hE0Inv.seq hAW hBaseInv
  unfold dPhiOnHeldZ18AnchorInv128 uPhiHeldZ18AnchorCat
  rwa [_root_.mul_inv_rev]
attribute [irreducible] dPhiOnHeldZ18AnchorFwd128 dPhiOnHeldZ18AnchorInv128
end Part2_GhostAndQftAnchor
section Part3_MaskedOrigin0AnchorHead
open FullSysCatSegmentBridge (disjointWires_concat_left fullSysCoreWires iSlot1 iSlot2)
open MeasureBranchHadamardSem (bit_cases projZeroAll ket_projZeroAll projZeroAll_conjTranspose
  projZeroAll_eq_basisOutcomeProjector_zero)
open PosSlots24SpectatorPrunedPhase (p2t_RealizesConstCleanUnitary
  p2t_RealizesConstCleanUnitary_toEmbeddedCleanWorkspace)
open MultiBankWStateRouter (SubspaceStep subspaceStep_of_circuit subspaceStep_congr_out)
open GridGuard654ReflAux (symWrapDynList symStepFwdList symWrapDynList_count_TOFF
  symWrapDynList_count_T ValidSymStepList)
open ZeroAncillaUSP (omega8)
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open PosSlots24Barrel3Pass (permUnitary_apply)
open CoinDispatchedBarrel288 (uBarrelFast uBarrelFast_mul_self coinBarrelPermFast
  coinBarrelBitFnFast coinBarrelIdxFast swapElec0Bits)
open OriginZeroHeadMod4Reduction (cHadamard18 cHadamard18_eval cHadamard18_count_T
  cHadamard18_count_TOFF cHad217 cHad217Inv cHad217_count_T cHad217_count_TOFF cHad217Inv_count_T
  cHad217Inv_count_TOFF cHad217_eval cHad217Inv_eval)
open StageAPosHeadConjugatedCircuit (uHadamard18 uHad217 elecProd217 rSpectatorSlot)
open Origin0Head34RealizesAndLeaf2Spec (origin0HeadEnSteps16 length_origin0HeadEnSteps16
  origin0HeadEnSteps16_valid_and_sub origin0HeadEnSteps16_eval
  wHeadThresh_not_mem_origin0HeadEnSteps16 wHeadThresh_ne_scr)
open ElecHadTrueSwapLocalCompClosure (extractPair lensSwapEquiv uLensSwap)
open PureCnotLensLoadAndZeroHypTrueSwap (uLensSwap_mul_self_eq_one)
open DoubleDutyFoldedRealizesBridge (selPosCoreInCore80)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (rFullSysElecSlot rFullSysElecSlot_val)
open InterWalkRSum42Hoist (qreg_ext kFull80 rCoreFull embedUnitary_inv_symm)
open ButterflyBarrelSlot0Conj (spectatorElecReg ActsAsIdOnSpectatorWires PreservesHigh3924On)
open Barrel3PassCommuteHelpers (swapElec0Wire swapElec0Wire_involutive swapElec0Bits_eq_comp_wire
  swapElec0Perm swapElec0Perm_involutive basisBits_swapElec0Perm embedUnitary_list_prod
  comm_uBarrelFast_of_fixesHigh3948_and_swapInv embedMatrix_mid3924_3948_fixesHigh3948
  list_prod_fixesHigh3948 conj_selfInv_list_prod ofFn_comp_perm_prod_eq selfInv_perm_conj_apply)
open ZeroHypStageABToUFoldedPass123SegAndCompac (rElec18InCore rElec18InCore_apply_val
  rElec18InCore_disjoint elecProd218)
open Classical in
theorem ite_true_eq {α : Sort _} {P : Prop} [inst : Decidable P] {a b : α} (h : P) :
    (if P then a else b) = a := by
  cases inst with
  | isFalse hnp => exact False.elim (hnp h)
  | isTrue _ => rfl
open Classical in
theorem ite_false_eq {α : Sort _} {P : Prop} [inst : Decidable P] {a b : α} (h : ¬P) :
    (if P then a else b) = b := by
  cases inst with
  | isFalse _ => rfl
  | isTrue hp => exact False.elim (h hp)
open StageADeconstrCore hiding wHeadThresh_ne_scr headEnBoolSpec_update_wHeadThresh
/-- Local wrapper for `origin0HeadEnSteps16` marked `[irreducible]` to prevent `whnf` list
  expansion. -/
def headEnSteps16 {n mScr : ℕ} (hm16 : 16 ≤ mScr) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) : List (SymTempAndStep n) :=
    origin0HeadEnSteps16 hm16 rCore rScr hCS
@[simp] theorem length_headEnSteps16 {n mScr : ℕ} (hm16 : 16 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) :
    (headEnSteps16 hm16 rCore rScr hCS).length = 16 :=
  length_origin0HeadEnSteps16 hm16 rCore rScr hCS
theorem headEnSteps16_valid_and_sub {n mScr : ℕ} (hm16 : 16 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) :
    ValidSymStepList (∅ : Finset (Wire n)) rScr 0 (headEnSteps16 hm16 rCore rScr hCS) ∧
      ∀ s ∈ headEnSteps16 hm16 rCore rScr hCS, s.S ⊆ rCore.image ∪ (rScr.slice 0 16 hm16).image :=
  origin0HeadEnSteps16_valid_and_sub hm16 rCore rScr hCS
open Classical in
theorem headEnSteps16_eval {n mScr : ℕ} (hm16 : 16 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (β : BitAssignment n) (hClean : ∀ idx : Fin 16, β (rScr ⟨idx.val, by omega⟩) = 0) :
    (∀ z,
      z ∉ (rScr.slice 0 16 hm16).image → symStepFwdList (headEnSteps16 hm16 rCore rScr hCS) β z =
      β z) ∧
      symStepFwdList (headEnSteps16 hm16 rCore rScr hCS) β (rScr ⟨15, by omega⟩) =
        if headEnBoolSpec (fun i ↦ β (rCore i)) = true then 1 else 0 :=
  origin0HeadEnSteps16_eval hm16 rCore rScr hCS β hClean
theorem wHeadThresh_not_mem_headEnSteps16 {n mScr : ℕ} (hm16 : 16 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) :
    ∀ s ∈ headEnSteps16 hm16 rCore rScr hCS, wHeadThresh rCore ∉ s.S :=
  wHeadThresh_not_mem_origin0HeadEnSteps16 hm16 rCore rScr hCS
attribute [irreducible] headEnSteps16
/-- Core unshifted `219`-slot `2-T` parity-leaf masked origin-`0` anchor head (`15,882 T`, `0
  TOFF`, `172 ≤ mScr`). -/
noncomputable def dHeadAnchorCore172 {Var : Type} {n mScr : ℕ} (hm172 : 172 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rScr : QRegister mScr n)
    (hCA : rCore.DisjointWires rAnchor18) (hCS : rCore.DisjointWires rScr)
    (hAS : rAnchor18.DisjointWires rScr) : DynamicCircuit Var n :=
  let dWithPre := dHeadAnchorWithPre172 hm172 v rCore rAnchor18 rScr hCA hCS hAS
  let cFlip := Circuit.CNOT (rScr ⟨15, by omega⟩) (wHeadThresh rCore)
    (wHeadThresh_ne_scr rCore rScr hCS _).symm
  symWrapDynList v (headEnSteps16 (by omega : 16 ≤ mScr) rCore rScr hCS)
    (.seq dWithPre (.circuit cFlip))
@[simp]
theorem count_dHeadAnchorCore172_toff {Var : Type} {n mScr : ℕ} (hm172 : 172 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rScr : QRegister mScr n)
    (hCA : rCore.DisjointWires rAnchor18) (hCS : rCore.DisjointWires rScr)
    (hAS : rAnchor18.DisjointWires rScr) :
    (dHeadAnchorCore172 hm172 v rCore rAnchor18 rScr hCA hCS hAS).count TOFF = 0 := by
  dsimp only [dHeadAnchorCore172]
  rw [symWrapDynList_count_TOFF]
  dsimp only [DynamicCircuit.count]
  rw [count_dHeadAnchorWithPre172_toff]
  simp [Circuit.CNOT]
@[simp]
theorem count_dHeadAnchorCore172_t {Var : Type} {n mScr : ℕ} (hm172 : 172 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rScr : QRegister mScr n)
    (hCA : rCore.DisjointWires rAnchor18) (hCS : rCore.DisjointWires rScr)
    (hAS : rAnchor18.DisjointWires rScr) :
    (dHeadAnchorCore172 hm172 v rCore rAnchor18 rScr hCA hCS hAS).count T = 15882 := by
  dsimp only [dHeadAnchorCore172]
  rw [symWrapDynList_count_T, length_headEnSteps16]
  dsimp only [DynamicCircuit.count]
  rw [count_dHeadAnchorWithPre172_t]
  have hFlip : (Circuit.CNOT (rScr ⟨15, by omega⟩) (wHeadThresh rCore)
      (wHeadThresh_ne_scr rCore rScr hCS _).symm).count T = 0 := by simp [Circuit.CNOT]
  rw [hFlip]
theorem ket_injective_part3 {n : ℕ} {α β : BitAssignment n} (h : ket α = ket β) : α = β := by
  have hx := congrFun h ((basisBitsEquiv n).symm α)
  simp only [ket, basisState, Pi.single_eq_same] at hx
  have hEq : (basisBitsEquiv n).symm β = (basisBitsEquiv n).symm α := by
    by_contra hne
    rw [Pi.single_eq_of_ne (Ne.symm hne)] at hx
    exact one_ne_zero hx
  exact (basisBitsEquiv n).symm.injective hEq.symm
open Classical in
/-- Clean-workspace realization of `dHeadAnchorCore172` (`172 ≤ mScr`, `15,882 T`, `0 TOFF`). -/
theorem dHeadAnchorCore172_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n mScr : ℕ}
    (hm172 : 172 ≤ mScr) (v : Var) (rCore : QRegister posCoreWires n)
    (rAnchor18 : QRegister 18 n) (rScr : QRegister mScr n)
    (hCA : rCore.DisjointWires rAnchor18) (hCS : rCore.DisjointWires rScr)
    (hAS : rAnchor18.DisjointWires rScr) : RealizesEmbeddedUnitaryWithCleanWorkspace
    (rCore.concat rAnchor18 hCA) rScr uHeadAnchorCore
    (dHeadAnchorCore172 hm172 v rCore rAnchor18 rScr hCA hCS hAS) := by
  let rCA := rCore.concat rAnchor18 hCA
  have hCAS : rCA.DisjointWires rScr := disjointWires_concat_left _ hCS hAS
  let P_156 := projZeroAll 156 (headScr156 hm172 rScr)
  let P_all := projZeroAll mScr rScr.wires
  let pPre := pHeadAnchorPre hm172 rCore rAnchor18 rScr hCS
  have hWithPreConst : p2t_RealizesConstCleanUnitary P_156
      (dHeadAnchorWithPre172 hm172 v rCore rAnchor18 rScr hCA hCS hAS) (diagZ8UnitaryN pPre)
      := dHeadAnchorWithPre172_constClean_export hm172 v rCore rAnchor18 rScr hCA hCS hAS
  let L16 := headEnSteps16 (by omega : 16 ≤ mScr) rCore rScr hCS
  obtain ⟨hv16, _⟩ := headEnSteps16_valid_and_sub (by omega : 16 ≤ mScr) rCore rScr hCS
  let cFlip := Circuit.CNOT (rScr ⟨15, by omega⟩) (wHeadThresh rCore)
    (wHeadThresh_ne_scr rCore rScr hCS _).symm
  let U_all := rCA.embedUnitary uHeadAnchorCore
  have hLen16 : L16.length = 16 := length_headEnSteps16 (by omega : 16 ≤ mScr) rCore rScr hCS
  have hSingAll : ∀ i : Fin L16.length,
      (QRegister.singleton (rScr ⟨0 + i.val, by omega⟩)).basisOutcomeProjector 0 * P_all = P_all :=
        fun i ↦ by
    rw [← projZeroAll_eq_basisOutcomeProjector_zero (QRegister.singleton (rScr ⟨0 + i.val,
      by omega⟩))]
    exact projZeroAll_mul_of_mem _ _ fun _ ↦ ⟨⟨0 + i.val, by omega⟩, rfl⟩
  have hSingAllOut : ∀ i : Fin L16.length,
      (QRegister.singleton (rScr ⟨0 + i.val,
        by omega⟩)).basisOutcomeProjector 0 * (U_all.1 * P_all) =
        U_all.1 * P_all := fun i ↦ by
    let rSing := QRegister.singleton (rScr ⟨0 + i.val, by omega⟩)
    have hDisjSing : rCA.DisjointWires rSing := by
      rw [QRegister.disjoint_iff]
      intro a _ hEq
      exact hCAS.ne a ⟨0 + i.val, by omega⟩ hEq
    have hComm : rSing.basisOutcomeProjector 0 * U_all.1 = U_all.1 *
      rSing.basisOutcomeProjector 0 :=
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCA) rSing hDisjSing
        uHeadAnchorCore.1 0).symm
    rw [← Matrix.mul_assoc, hComm, Matrix.mul_assoc, hSingAll i]
  have hP156_L16 : P_156 * ((cSymStepFwdList L16).eval.1 * P_all) =
      (cSymStepFwdList L16).eval.1 * P_all := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projZeroAll]
    by_cases hAll : ∀ idx : Fin mScr, β (rScr idx) = 0
    · rw [ite_true_eq hAll, mbh_ket_eq_ket, cSymStepFwdList_mulVec_ket, ← mbh_ket_eq_ket,
        ket_projZeroAll]
      obtain ⟨hout16, _⟩ := headEnSteps16_eval (by omega : 16 ≤ mScr) rCore rScr hCS β
        (fun idx ↦ hAll ⟨idx.val, by omega⟩)
      have h156 : ∀ m : Fin 156, symStepFwdList L16 β (headScr156 hm172 rScr m) = 0 := fun m ↦ by
        have hnot : headScr156 hm172 rScr m ∉ (rScr.slice 0 16 (by omega)).image := by
          intro hm
          obtain ⟨j, hj⟩ := QRegister.mem_image _ _ |>.mp hm
          rw [QRegister.slice_apply] at hj
          have hv := congrArg Fin.val (rScr.wires.injective hj)
          have hjlt := j.isLt; dsimp [headScr156] at hv; omega
        rw [hout16 _ hnot]
        exact hAll ⟨16 + m.val, by omega⟩
      rw [ite_true_eq h156]
    · rw [ite_false_eq hAll, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hL16_X_comm : ∀ γ : BitAssignment n,
      symStepFwdList L16 (Function.update γ (wHeadThresh rCore) (γ (wHeadThresh rCore) + 1)) =
        Function.update (symStepFwdList L16 γ) (wHeadThresh rCore)
          (symStepFwdList L16 γ (wHeadThresh rCore) + 1) := fun γ ↦ by
    have hnotSup : wHeadThresh rCore ∉ (cSymStepFwdList L16).support :=
      cSymStepFwdList_support_not_mem
        (wHeadThresh_not_mem_headEnSteps16 (by omega : 16 ≤ mScr) rCore rScr hCS)
    have hMat := congrArg (fun M : Operator (2 ^ n) ↦ M.mulVec (ket γ))
      (eval_X_comm_of_not_mem_support (wHeadThresh rCore) (cSymStepFwdList L16) hnotSup)
    rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cSymStepFwdList_mulVec_ket,
        OctahedralOrbit.ket_X, OctahedralOrbit.ket_X, cSymStepFwdList_mulVec_ket] at hMat
    exact (ket_injective_part3 hMat).symm
  have hEn_upd_th : ∀ γL : BitAssignment posCoreWires,
      headEnBoolSpec (Function.update γL (wHeadThresh (QRegExt.ofFin posCoreWires)) 0) =
        headEnBoolSpec γL := fun γL ↦ headEnBoolSpec_update_wHeadThresh γL 0
  have hCoreEq16 : cFlip.eval.1 * ((diagZ8UnitaryN pPre).1 * ((cSymStepFwdList L16).eval.1 *
    P_all)) =
      (cSymStepFwdList L16).eval.1 * (U_all.1 * P_all) := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projZeroAll]
    by_cases hAll : ∀ idx : Fin mScr, β (rScr idx) = 0
    · rw [ite_true_eq hAll]
      have hrCA_data : ∀ i : Fin posCoreWires, rCA (selDataInAct posCoreWires i) = rCore i :=
        fun i ↦ congrArg (fun r ↦ r i) (concat_compose_selDataInAct rCore rAnchor18 hCA)
      have hwTh_rCA : rCA (wHeadThresh (selDataInAct posCoreWires)) = wHeadThresh rCore :=
        hrCA_data _
      have hEnCA : (fun γ : BitAssignment n ↦ headEnBoolSpec (fun i ↦
        γ (rCA (selDataInAct posCoreWires i)))) =
          (fun γ : BitAssignment n ↦ headEnBoolSpec (fun i ↦ γ (rCore i))) := by
        funext γ; congr 1; funext i; exact congrArg γ (hrCA_data i)
      have hU_all_eq : U_all = monomialZ8UnitaryN (wHeadThresh rCore)
          (fun γ ↦ headEnBoolSpec (fun i ↦ γ (rCore i)))
          (fun γ ↦ headAnchorCoreZ8Spec (fun i ↦ γ (rCA i))) := by
        dsimp only [U_all, uHeadAnchorCore]
        rw [embedUnitary_monomialZ8UnitaryN, hwTh_rCA, hEnCA]
      rw [mbh_ket_eq_ket, cSymStepFwdList_mulVec_ket, ket_diagZ8UnitaryN,
          Matrix.mulVec_smul, OctahedralOrbit.ket_CNOT,
          hU_all_eq, ket_monomialZ8UnitaryN, Matrix.mulVec_smul, cSymStepFwdList_mulVec_ket]
      let b16 := symStepFwdList L16 β
      obtain ⟨hout16, hvEn16⟩ := headEnSteps16_eval (by omega : 16 ≤ mScr) rCore rScr hCS β
        (fun idx ↦ hAll ⟨idx.val, by omega⟩)
      have hnot16 (w : Wire n) (hw : ∀ j : Fin 16, w ≠ rScr ⟨0 + j.val, by omega⟩) :
          w ∉ (rScr.slice 0 16 (by omega)).image := by
        intro hm
        obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
        rw [QRegister.slice_apply] at hj
        exact hw j hj.symm
      have hnot16_core : ∀ i : Fin posCoreWires, rCore i ∉ (rScr.slice 0 16 (by omega)).image :=
        fun i ↦ hnot16 _ fun j ↦ hCS.ne i ⟨0 + j.val, by omega⟩
      have hnot16_anc : ∀ q : Fin 18, rAnchor18 q ∉ (rScr.slice 0 16 (by omega)).image :=
        fun q ↦ hnot16 _ fun j ↦ hAS.ne q ⟨0 + j.val, by omega⟩
      have hb16_scr : ∀ (k : ℕ) (hk : k < mScr), 16 ≤ k → b16 (rScr ⟨k, hk⟩) = 0 := fun k hk hge ↦
        (hout16 _ (hnot16 _ fun j hj ↦ by
          have hv := congrArg Fin.val (rScr.wires.injective hj)
          have hjlt := j.isLt
          dsimp only at hv
          omega)).trans (hAll ⟨k, hk⟩)
      let βL : BitAssignment posCoreWires := fun i ↦ β (rCore i)
      have hFlipKet : Function.update b16 (wHeadThresh rCore)
            (b16 (wHeadThresh rCore) + b16 (rScr ⟨15, by omega⟩)) =
          symStepFwdList L16 (flipThClean (wHeadThresh rCore)
            (fun γ ↦ headEnBoolSpec (fun i ↦ γ (rCore i))) β) := by
        have hUpdCore : (fun i ↦ Function.update β (wHeadThresh rCore) 0 (rCore i)) =
            Function.update βL (wHeadThresh (QRegExt.ofFin posCoreWires)) 0 := by
          have hwThEq : rCore (wHeadThresh (QRegExt.ofFin posCoreWires)) = wHeadThresh rCore := rfl
          funext i
          by_cases hi : i = wHeadThresh (QRegExt.ofFin posCoreWires)
          · subst hi; rw [hwThEq, Function.update_self, Function.update_self]
          · have hne : rCore i ≠ wHeadThresh rCore := fun h ↦ hi (rCore.wires.injective h)
            rw [Function.update_of_ne hne, Function.update_of_ne hi]
        unfold flipThClean
        dsimp only
        rw [hUpdCore, hEn_upd_th βL]
        change Function.update b16 (wHeadThresh rCore)
            (b16 (wHeadThresh rCore) + b16 (rScr ⟨15, by omega⟩)) =
          symStepFwdList L16 (flipTh (wHeadThresh rCore) (headEnBoolSpec βL) β)
        have hb16_en : b16 (rScr ⟨15, by omega⟩) = if headEnBoolSpec βL = true then 1 else 0 :=
          hvEn16
        rw [hb16_en]
        cases hEnB : headEnBoolSpec βL
        · have hFlFalse : flipTh (wHeadThresh rCore) false β = β := by
            unfold flipTh; simp
          rw [hFlFalse]; simp [b16]
        · have hFlTrue : flipTh (wHeadThresh rCore) true β =
              Function.update β (wHeadThresh rCore) (β (wHeadThresh rCore) + 1) := by
            unfold flipTh; simp
          rw [hFlTrue, hL16_X_comm β]; simp [b16]
      refine congrArg₂ (fun (k : ZMod 8) (u : BitAssignment n) ↦
        (omega8 ^ k.val) • ket u) ?_ hFlipKet
      exact pHeadAnchorPre_eval hm172 rCore rAnchor18 rScr hCA hCS hAS β b16
        (fun i ↦ hout16 (rCore i) (hnot16_core i))
        (fun q ↦ hout16 (rAnchor18 q) (hnot16_anc q)) hvEn16 hb16_scr
    · rw [ite_false_eq hAll, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero,
          Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hInner16 : SubspaceStep ((cSymStepFwdList L16).eval.1 * P_all)
      ((cSymStepFwdList L16).eval.1 * (U_all.1 * P_all)) (.seq (dHeadAnchorWithPre172 hm172 v
      rCore rAnchor18 rScr hCA hCS hAS) (.circuit cFlip)) := subspaceStep_congr_out
      ((SubspaceStep.ofConstCleanUnitary (projZeroAll_conjTranspose _ _) hWithPreConst
      hP156_L16).seq (subspaceStep_of_circuit _ cFlip)) hCoreEq16
  have hFullStep : SubspaceStep P_all (U_all.1 * P_all)
      (dHeadAnchorCore172 hm172 v rCore rAnchor18 rScr hCA hCS hAS) := by
    dsimp only [dHeadAnchorCore172]
    exact subspaceStep_symWrapDynList v rScr 0 L16 hv16 (by rw [hLen16]; omega)
      hSingAll hSingAllOut hInner16
  have hConstAll : p2t_RealizesConstCleanUnitary (rScr.basisOutcomeProjector 0)
      (dHeadAnchorCore172 hm172 v rCore rAnchor18 rScr hCA hCS hAS) U_all := by
    rw [← projZeroAll_eq_basisOutcomeProjector_zero rScr]
    exact SubspaceStep.toConstCleanUnitary (projZeroAll_conjTranspose _ _) hFullStep
  exact p2t_RealizesConstCleanUnitary_toEmbeddedCleanWorkspace rCA rScr uHeadAnchorCore _ hConstAll
attribute [irreducible] dHeadAnchorCore172
theorem swapElec0Wire_rElec18InCore {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (e : Fin SpecsAux.SpecMirror.numElectrons) (i : Fin 218) (q : Fin 18) :
    swapElec0Wire e (rElec18InCore hm6 i q) =
      rElec18InCore hm6 (Equiv.swap (0 : Fin 218) ⟨e.val, e.isLt⟩ i) q := by
  have heLt : e.val < 218 := e.isLt
  have hiLt : i.val < 218 := i.isLt
  have hq18 : q.val < 18 := q.isLt
  let e' : Fin 218 := ⟨e.val, heLt⟩
  have hw1 : (rElec18InCore hm6 i q).val = 18 * i.val + q.val := rElec18InCore_apply_val hm6 i q
  have hw2 : (rElec18InCore hm6 (Equiv.swap (0 : Fin 218) e' i) q).val =
      18 * (Equiv.swap (0 : Fin 218) e' i).val + q.val := rElec18InCore_apply_val hm6 _ q
  apply Fin.ext
  rw [hw2]
  by_cases he0 : e.val = 0
  · have he'0 : e' = 0 := Fin.ext he0
    rw [he'0, Equiv.swap_self, Equiv.refl_apply]
    unfold swapElec0Wire
    rw [ite_true_eq he0, hw1]
  · unfold swapElec0Wire
    rw [ite_false_eq he0]
    by_cases hi0 : i = 0
    · have hi0v : i.val = 0 := congrArg Fin.val hi0
      have hwLt : (rElec18InCore hm6 i q).val < 18 := by omega
      rw [dite_true_eq hwLt, Fin.val_mk, hw1, hi0, Equiv.swap_apply_left]
      dsimp only [e']
      omega
    · have hi0v : i.val ≠ 0 := fun h ↦ hi0 (Fin.ext h)
      have hwGe : ¬ (rElec18InCore hm6 i q).val < 18 := by omega
      rw [dite_false_eq hwGe]
      by_cases hie : i = e'
      · have hiev : i.val = e.val := congrArg Fin.val hie
        have hRange : 18 * e.val ≤ (rElec18InCore hm6 i q).val ∧
            (rElec18InCore hm6 i q).val < 18 * e.val + 18 := by omega
        rw [dite_true_eq hRange, Fin.val_mk, hw1, hie, Equiv.swap_apply_right]
        dsimp only [e']
        omega
      · have hiev : i.val ≠ e.val := fun h ↦ hie (Fin.ext h)
        have hNotRange : ¬ (18 * e.val ≤ (rElec18InCore hm6 i q).val ∧
            (rElec18InCore hm6 i q).val < 18 * e.val + 18) := by omega
        rw [dite_false_eq hNotRange, Equiv.swap_apply_of_ne_of_ne hi0 hie, hw1]
open Classical in
theorem rElec18InCore_embedMatrix_swap {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (e : Fin SpecsAux.SpecMirror.numElectrons) (i : Fin 218) (M : Operator (2 ^ 18))
    (x y : Fin (2 ^ (fullSysCoreWires mPayload))) :
    (rElec18InCore hm6 i).embedMatrix M (swapElec0Perm mPayload e x) (swapElec0Perm mPayload e y) =
      (rElec18InCore hm6 (Equiv.swap (0 : Fin 218) ⟨e.val, e.isLt⟩ i)).embedMatrix M x y := by
  let e' : Fin 218 := ⟨e.val, e.isLt⟩
  let rA := rElec18InCore hm6 i
  let rB := rElec18InCore hm6 (Equiv.swap (0 : Fin 218) e' i)
  have hExt : ∀ z, rA.extractIndex (swapElec0Perm mPayload e z) = rB.extractIndex z := fun z ↦ by
    apply eq_of_basisBits_eq; intro q
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        basisBits_swapElec0Perm, swapElec0Bits_eq_comp_wire,
        swapElec0Wire_rElec18InCore hm6 e i q]
  have hMemIff : ∀ q, q ∈ Set.range rA.wires ↔ swapElec0Wire e q ∈ Set.range rB.wires := fun q ↦ by
    refine ⟨fun ⟨r, hr⟩ ↦ ⟨r, ?_⟩, fun ⟨r, hr⟩ ↦ ⟨r, ?_⟩⟩
    · rw [← hr]; exact (swapElec0Wire_rElec18InCore hm6 e i r).symm
    · have h1 := congrArg (swapElec0Wire e) hr
      rw [swapElec0Wire_involutive] at h1
      have h2 := swapElec0Wire_rElec18InCore hm6 e (Equiv.swap 0 e' i) r
      rw [Equiv.swap_apply_self] at h2
      exact h2.symm.trans h1
  have hEnvIff : ((rA.basisSplitEquiv (swapElec0Perm mPayload e x)).2 = (rA.basisSplitEquiv
      (swapElec0Perm mPayload e y)).2) ↔ ((rB.basisSplitEquiv x).2 = (rB.basisSplitEquiv y).2)
      := by
    rw [rA.basisSplit_environment_eq_iff, rB.basisSplit_environment_eq_iff]
    refine ⟨fun h q hq ↦ ?_, fun h q hq ↦ ?_⟩
    · have hq' : swapElec0Wire e q ∉ Set.range rA.wires := fun hm ↦
        hq (by have hm' := (hMemIff _).mp hm; rwa [swapElec0Wire_involutive] at hm')
      have h1 := h (swapElec0Wire e q) hq'
      rwa [basisBits_swapElec0Perm, basisBits_swapElec0Perm, swapElec0Bits_eq_comp_wire,
        swapElec0Bits_eq_comp_wire, swapElec0Wire_involutive] at h1
    · rw [basisBits_swapElec0Perm, basisBits_swapElec0Perm,
          swapElec0Bits_eq_comp_wire, swapElec0Bits_eq_comp_wire]
      exact h (swapElec0Wire e q) (fun hm ↦ hq ((hMemIff q).mpr hm))
  rw [QRegister.embedMatrix_apply, QRegister.embedMatrix_apply, hExt x, hExt y]
  by_cases hE : (rB.basisSplitEquiv x).2 = (rB.basisSplitEquiv y).2
  · rw [ite_true_eq (hEnvIff.mpr hE), ite_true_eq hE]
  · rw [ite_false_eq (mt hEnvIff.mp hE), ite_false_eq hE]
open Classical in
/-- Any homogeneous `218`-electron `18`-qubit unitary product `elecProd218 hm6 U` commutes
with `uBarrelFast hmPay` (`80 ≤ mPayload`). -/
theorem elecProd218_comm_uBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (U : Unitary (2 ^ 18)) :
    let hm6 : 6 ≤ mPayload := Nat.le_trans (by decide : 6 ≤ 80) hmPay
    (elecProd218 hm6 U).1 * (uBarrelFast hmPay).1 =
      (uBarrelFast hmPay).1 * (elecProd218 hm6 U).1 := by
  intro hm6
  let factor (i : Fin 218) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
    (rElec18InCore hm6 i).embedUnitary U
  have hFixes : ∀ x y, (elecProd218 hm6 U).1 x y ≠ 0 → ∀ q : Wire
      (fullSysCoreWires mPayload), 3948 ≤ q.val → basisBits (fullSysCoreWires mPayload) x q
      = basisBits (fullSysCoreWires mPayload) y q := by
    unfold elecProd218
    rw [DyadicQft64WalkCircuit.submonoid_coe_list_prod]
    refine list_prod_fixesHigh3948 _ ?_
    intro A hA x y hnz q hq
    rw [List.mem_map] at hA
    rcases hA with ⟨u, hu, rfl⟩
    rw [List.mem_ofFn] at hu
    rcases hu with ⟨i, rfl⟩
    exact embedMatrix_mid3924_3948_fixesHigh3948 (rElec18InCore hm6 i)
      (fun r ↦ by rw [rElec18InCore_apply_val]; have := i.isLt; have := r.isLt; omega)
      U.1 hnz q hq
  have hConjProd : ∀ e : Fin SpecsAux.SpecMirror.numElectrons,
      Operator.permutationUnitary (swapElec0Perm mPayload e) * elecProd218 hm6 U *
        Operator.permutationUnitary (swapElec0Perm mPayload e) =
      elecProd218 hm6 U := fun e ↦ by
    let e' : Fin 218 := ⟨e.val, e.isLt⟩
    set σ := swapElec0Perm mPayload e
    have hσ_invol : ∀ z, σ (σ z) = z := swapElec0Perm_involutive mPayload e
    have hσ_inv : ∀ z, σ⁻¹ z = σ z := fun z ↦ σ.symm_apply_eq.mpr (hσ_invol z).symm
    set S := Operator.permutationUnitary σ
    have hS2 : S * S = 1 := by
      have hsq : σ * σ = 1 := by apply Equiv.ext; exact hσ_invol
      dsimp only [S]
      rw [← OperatorExt.permutationUnitary_mul, hsq, OperatorExt.permutationUnitary_one]
    have hConjEach : ∀ i : Fin 218,
        S * factor i * S = factor (Equiv.swap (0 : Fin 218) e' i) := fun i ↦ by
      unfold factor
      apply Subtype.ext; ext z w
      change ((S.1 * ((rElec18InCore hm6 i).embedUnitary U).1) * S.1) z w =
        ((rElec18InCore hm6 (Equiv.swap 0 e' i)).embedUnitary U).1 z w
      rw [CommutedRSum42ApexTwistHoist288.mul_permutationUnitary_apply,
          CommutedRSum42ApexTwistHoist288.permutationUnitary_mul_apply,
          hσ_inv z]
      exact rElec18InCore_embedMatrix_swap hm6 e i U.1 z w
    have hDef : elecProd218 hm6 U = (List.ofFn factor).prod := rfl
    rw [hDef, conj_selfInv_list_prod S hS2, List.map_ofFn]
    have hfn : (fun X ↦ S * X * S) ∘ factor = factor ∘ Equiv.swap (0 : Fin 218) e' :=
      funext hConjEach
    rw [hfn]
    refine ofFn_comp_perm_prod_eq (Equiv.swap (0 : Fin 218) e') factor fun i j hne ↦ ?_
    unfold factor
    apply Subtype.ext
    exact QRegister.embedMatrix_comm_of_disjoint
      (rElec18InCore hm6 i) (rElec18InCore hm6 j) (rElec18InCore_disjoint hm6 hne) U.1 U.1
  refine comm_uBarrelFast_of_fixesHigh3948_and_swapInv hmPay (elecProd218 hm6 U).1 hFixes
    fun e x y ↦ ?_
  exact selfInv_perm_conj_apply (swapElec0Perm mPayload e) (fun z ↦ (swapElec0Perm mPayload
    e).symm_apply_eq.mpr (swapElec0Perm_involutive mPayload e z).symm) (elecProd218 hm6 U)
    (hConjProd e) x y
/-- `18`-wire Electron `0` register on `posCoreWires`. -/
def rSlot0Pos : QRegister 18 posCoreWires := rElecSlot (QRegExt.ofFin posCoreWires) 0
theorem fullSysCoreWires80_le_posCoreWires : fullSysCoreWires 80 ≤ posCoreWires := by
  rw [fullSysCoreWires80_eq_4034_assoc, posCoreWires_eq_4034_assoc]
theorem posCoreWires_eq_fullSysCoreWires80 : posCoreWires = fullSysCoreWires 80 :=
  posCoreWires_eq_4034_assoc.trans fullSysCoreWires80_eq_4034_assoc.symm
/-- Identity block isomorphism `fullSysCoreWires 80 → posCoreWires` (`4034 = 4034`). -/
def selCore80InPos : QRegister (fullSysCoreWires 80) posCoreWires :=
  QRegister.block 0 (fullSysCoreWires 80) fullSysCoreWires80_le_posCoreWires
/-- `18`-pair swap unitary between `rSlot0Pos` and `selMeasInAct posCoreWires` on `posCoreWires +
  18`. -/
noncomputable def σ_0_pos : Unitary (2 ^ (posCoreWires + 18)) :=
  uLensSwap (L_slot0Of rSlot0Pos)
/-- `uBarrelFast (le_refl 80)` embedded on `(selDataInAct posCoreWires).compose selCore80InPos`. -/
noncomputable def τ_pos : Unitary (2 ^ (posCoreWires + 18)) :=
  ((selDataInAct posCoreWires).compose selCore80InPos).embedUnitary (uBarrelFast (le_refl 80))
theorem σ_0_pos_mul_self : σ_0_pos * σ_0_pos = 1 :=
  uLensSwap_mul_self_eq_one (L_slot0Of rSlot0Pos)
theorem τ_pos_mul_self : τ_pos * τ_pos = 1 := by
  dsimp only [τ_pos]
  rw [← QRegister.embedUnitary_mul, uBarrelFast_mul_self (le_refl 80), QRegister.embedUnitary_one]
open Classical in
theorem slot0_mul_elecProd217_eq_elecProd218 (U : Unitary (2 ^ 18)) :
    rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦ U) =
      selCore80InPos.embedUnitary (elecProd218 (by decide : 6 ≤ 80) U) := by
  have h0 : selCore80InPos.compose (rElec18InCore (by decide : 6 ≤ 80) 0) = rSlot0Pos := by
    apply qreg_ext; intro q; apply Fin.ext
    simp [selCore80InPos, rElec18InCore_apply_val, rSlot0Pos, rElecSlot]
  have hs : ∀ s : Fin 217,
      selCore80InPos.compose (rElec18InCore (by
        decide : 6 ≤ 80) s.succ) = rSpectatorSlot s := fun s ↦ by
    apply qreg_ext; intro q; apply Fin.ext
    simp [selCore80InPos, rElec18InCore_apply_val, rSpectatorSlot, rElecSlot]
  unfold elecProd218
  rw [List.ofFn_succ, List.prod_cons, QRegister.embedUnitary_mul,
      ← QRegister.embedUnitary_compose, h0]
  apply congrArg (rSlot0Pos.embedUnitary U * ·)
  unfold elecProd217
  rw [embedUnitary_list_prod, List.map_ofFn]
  apply congrArg List.prod; apply congrArg List.ofFn; funext s
  rw [Function.comp_apply, ← QRegister.embedUnitary_compose, hs s]
open Classical in
theorem elecProd218Pos_eq_anchorConj (U : Unitary (2 ^ 18)) : (σ_0_pos * τ_pos) *
    (selDataInAct posCoreWires).embedUnitary
    (rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦ U)) * (τ_pos * σ_0_pos) =
    (selMeasInAct posCoreWires).embedUnitary U * (selDataInAct posCoreWires).embedUnitary
    (elecProd217 (fun _ ↦ U)) := by
  have hCommτ : (selDataInAct posCoreWires).embedUnitary
        (rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦ U)) * τ_pos =
      τ_pos * (selDataInAct posCoreWires).embedUnitary
        (rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦ U)) := by
    rw [slot0_mul_elecProd217_eq_elecProd218 U, ← QRegister.embedUnitary_compose]
    dsimp only [τ_pos]
    apply Subtype.ext
    simp only [Submonoid.coe_mul, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul]
    exact congrArg ((selDataInAct posCoreWires).compose selCore80InPos).embedMatrix
      (elecProd218_comm_uBarrelFast (le_refl 80) U)
  have hConjσ : σ_0_pos * (selDataInAct posCoreWires).embedUnitary
        (rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦ U)) * σ_0_pos =
      (selMeasInAct posCoreWires).embedUnitary U *
        (selDataInAct posCoreWires).embedUnitary (elecProd217 (fun _ ↦ U)) := by
    have hSubst : (selSubstSlot0 rSlot0Pos).embedUnitary
          (rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦ U)) =
        σ_0_pos * (selDataInAct posCoreWires).embedUnitary
          (rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦ U)) * σ_0_pos := by
      apply Subtype.ext
      exact embedMatrix_selSubstSlot0_eq rSlot0Pos _
    rw [← hSubst, QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
    have hM : (selSubstSlot0 rSlot0Pos).compose rSlot0Pos = selMeasInAct posCoreWires := by
      apply qreg_ext; intro q
      dsimp only [selSubstSlot0, QRegister.compose_apply]
      exact rDataSubstSlot0_apply_slot0 rSlot0Pos (selDataInAct posCoreWires)
        (selMeasInAct posCoreWires) (selDataInAct_disj_selMeasInAct posCoreWires) q
    have hS : ∀ s : Fin 217,
        (selSubstSlot0 rSlot0Pos).compose (rSpectatorSlot s) =
          (selDataInAct posCoreWires).compose (rSpectatorSlot s) := fun s ↦ by
      apply qreg_ext; intro q
      have hnot : rSpectatorSlot s q ∉ Set.range rSlot0Pos.wires := by
        rintro ⟨q', hq'⟩
        have hv := congrArg Fin.val hq'
        simp [rSlot0Pos, rSpectatorSlot, rElecSlot, QRegExt.ofFin] at hv
        have := q'.isLt; have := q.isLt; omega
      dsimp only [selSubstSlot0, QRegister.compose_apply]
      exact rDataSubstSlot0_apply_of_not_mem rSlot0Pos (selDataInAct posCoreWires)
        (selMeasInAct posCoreWires) (selDataInAct_disj_selMeasInAct posCoreWires) hnot
    rw [hM]; apply congrArg ((selMeasInAct posCoreWires).embedUnitary U * ·)
    unfold elecProd217
    rw [embedUnitary_list_prod, embedUnitary_list_prod, List.map_ofFn, List.map_ofFn]
    apply congrArg List.prod; apply congrArg List.ofFn; funext s
    rw [Function.comp_apply, Function.comp_apply,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose, hS s]
  have hτDτ : τ_pos * ((selDataInAct posCoreWires).embedUnitary (rSlot0Pos.embedUnitary U *
      elecProd217 (fun _ ↦ U)) * τ_pos) = (selDataInAct posCoreWires).embedUnitary
      (rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦ U)) := by
    rw [← _root_.mul_assoc, ← hCommτ, _root_.mul_assoc, τ_pos_mul_self, mul_one]
  calc (σ_0_pos * τ_pos) *
          (selDataInAct posCoreWires).embedUnitary (rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦
            U)) *
          (τ_pos * σ_0_pos)
      = σ_0_pos * (τ_pos * ((selDataInAct posCoreWires).embedUnitary
          (rSlot0Pos.embedUnitary U * elecProd217 (fun _ ↦ U)) * τ_pos)) * σ_0_pos := by
          simp only [_root_.mul_assoc]
    _ = (selMeasInAct posCoreWires).embedUnitary U *
          (selDataInAct posCoreWires).embedUnitary (elecProd217 (fun _ ↦ U)) := by
          rw [hτDτ, hConjσ]
noncomputable def permBits {N : ℕ} (σ : Equiv.Perm (Fin (2 ^ N))) (β : BitAssignment N) :
    BitAssignment N := basisBits N (σ ((basisBitsEquiv N).symm β))
theorem ket_permutationUnitary {N : ℕ} (σ : Equiv.Perm (Fin (2 ^ N))) (β : BitAssignment N) :
    (Operator.permutationUnitary σ).1.mulVec (ket β) = ket (permBits σ β) := by
  let g := (basisBitsEquiv N).symm β
  have hb_ket : (Pi.single g (1 : ℂ) : Fin (2 ^ N) → ℂ) = ket β := by
    funext x
    simp [g, ket, basisState]
  rw [← hb_ket, Matrix.mulVec_single, MulOpposite.op_one, one_smul]
  funext x
  change (Operator.permutationUnitary σ).1 x g = ket (permBits σ β) x
  rw [permUnitary_apply]
  have heq : basisBitsEquiv N (σ g) = permBits σ β := rfl
  simp only [ket, basisState, ← heq, Equiv.symm_apply_apply]
  by_cases hx : x = σ g <;> simp [hx]

theorem permBits_involutive {N : ℕ} {σ : Equiv.Perm (Fin (2 ^ N))} (hInv : ∀ z, σ (σ z) = z)
    (β : BitAssignment N) : permBits σ (permBits σ β) = β := by
  dsimp only [permBits]
  have h1 : (basisBitsEquiv N).symm (basisBits N (σ ((basisBitsEquiv N).symm β))) = σ
      ((basisBitsEquiv N).symm β) := (basisBitsEquiv N).symm_apply_apply _
  rw [h1, hInv]
  exact (basisBitsEquiv N).apply_symm_apply β
noncomputable def eS0Pos : Equiv.Perm (Fin (2 ^ (posCoreWires + 18))) :=
  lensSwapEquiv (L_slot0Of rSlot0Pos)
noncomputable def eBarPos : Equiv.Perm (Fin (2 ^ (posCoreWires + 18))) :=
  liftRegPerm ((selDataInAct posCoreWires).compose selCore80InPos) (coinBarrelPermFast (le_refl 80))
theorem eS0Pos_involutive (z : Fin (2 ^ (posCoreWires + 18))) : eS0Pos (eS0Pos z) = z :=
    lensSwapEquiv_involutive (L_slot0Of rSlot0Pos) z
theorem eBarPos_involutive (z : Fin (2 ^ (posCoreWires + 18))) : eBarPos (eBarPos z) = z := by
  dsimp only [eBarPos]
  rw [BoothOpt_Anchor218CachedTrueSwapOuter.liftRegPerm_apply,
      BoothOpt_Anchor218CachedTrueSwapOuter.liftRegPerm_apply,
      QRegister.extractIndex_replaceIndex,
      CoinDispatchedBarrel288.coinBarrelPermFast_apply_self,
      QRegister.replaceIndex_replaceIndex]
  exact PartnerAndAnchorSlot18LensAndMidBA.replaceIndex_extractIndex _ z
theorem ket_σ_0_pos (β : BitAssignment (posCoreWires + 18)) :
    σ_0_pos.1.mulVec (ket β) = ket (permBits eS0Pos β) :=
  ket_permutationUnitary eS0Pos β

theorem ket_τ_pos (β : BitAssignment (posCoreWires + 18)) :
    τ_pos.1.mulVec (ket β) = ket (permBits eBarPos β) := by
  have hEq : τ_pos = Operator.permutationUnitary eBarPos := embedUnitary_permutationUnitary_eq
      ((selDataInAct posCoreWires).compose selCore80InPos) (coinBarrelPermFast (le_refl 80))
  rw [hEq]
  exact ket_permutationUnitary eBarPos β

theorem permBits_eS0Pos_meas (δ : BitAssignment (posCoreWires + 18)) (q : Fin 18) : permBits
    eS0Pos δ (selMeasInAct posCoreWires q) = δ (selDataInAct posCoreWires (rSlot0Pos q)) := by
  dsimp only [permBits, eS0Pos]
  rw [basisBits_lensSwapEquiv_L_slot0Of_meas rSlot0Pos _ q]
  exact congrFun ((basisBitsEquiv (posCoreWires + 18)).apply_symm_apply δ) _
theorem basisBits_lensSwapEquiv_L_slot0Of_data_slot0 {kData : ℕ}
    (rSlot0 : QRegister 18 kData) (z : Fin (2 ^ (kData + 18))) (j : Fin 18) :
    basisBits (kData + 18) (lensSwapEquiv (L_slot0Of rSlot0) z) (selDataInAct kData (rSlot0 j)) =
      basisBits (kData + 18) z (selMeasInAct kData j) := by
  have hPair : (selDataInAct kData).extractIndex (lensSwapEquiv (L_slot0Of rSlot0) z) =
      rSlot0.replaceIndex ((selDataInAct kData).extractIndex z)
        ((selMeasInAct kData).extractIndex z) := by
    have h0 := congrArg Prod.fst (extractPair_lensSwapEquiv (L_slot0Of rSlot0) z)
    dsimp only [extractPair,
      ElecHadConjLoadAndTrueSwapComp.lensSwapPerm] at h0
    rwa [L_slot0Of_updSlot] at h0
  rw [← QRegister.basisBits_extractIndex (selDataInAct kData) _ (rSlot0 j), hPair,
      QRegister.basisBits_replaceIndex_apply,
      QRegister.basisBits_extractIndex (selMeasInAct kData) z j]
theorem basisBits_lensSwapEquiv_L_slot0Of_data_of_not_mem {kData : ℕ}
    (rSlot0 : QRegister 18 kData) (z : Fin (2 ^ (kData + 18)))
    {i : Fin kData} (hi : i ∉ Set.range rSlot0.wires) :
    basisBits (kData + 18) (lensSwapEquiv (L_slot0Of rSlot0) z) (selDataInAct kData i) =
      basisBits (kData + 18) z (selDataInAct kData i) := by
  have hPair : (selDataInAct kData).extractIndex (lensSwapEquiv (L_slot0Of rSlot0) z) =
      rSlot0.replaceIndex ((selDataInAct kData).extractIndex z)
        ((selMeasInAct kData).extractIndex z) := by
    have h0 := congrArg Prod.fst (extractPair_lensSwapEquiv (L_slot0Of rSlot0) z)
    dsimp only [extractPair,
      ElecHadConjLoadAndTrueSwapComp.lensSwapPerm] at h0
    rwa [L_slot0Of_updSlot] at h0
  rw [← QRegister.basisBits_extractIndex (selDataInAct kData) _ i, hPair,
      QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hi,
      QRegister.basisBits_extractIndex (selDataInAct kData) z i]
theorem permBits_eS0Pos_data_slot0 (δ : BitAssignment (posCoreWires + 18)) (q : Fin 18) :
    permBits eS0Pos δ (selDataInAct posCoreWires (rSlot0Pos q)) =
      δ (selMeasInAct posCoreWires q) := by
  dsimp only [permBits, eS0Pos]
  rw [basisBits_lensSwapEquiv_L_slot0Of_data_slot0 rSlot0Pos _ q]
  exact congrFun ((basisBitsEquiv (posCoreWires + 18)).apply_symm_apply δ) _
theorem permBits_eS0Pos_data_of_not_mem (δ : BitAssignment (posCoreWires + 18))
    {i : Fin posCoreWires} (hi : i ∉ Set.range rSlot0Pos.wires) : permBits eS0Pos δ
    (selDataInAct posCoreWires i) = δ (selDataInAct posCoreWires i) := by
  dsimp only [permBits, eS0Pos]
  rw [basisBits_lensSwapEquiv_L_slot0Of_data_of_not_mem rSlot0Pos _ hi]
  exact congrFun ((basisBitsEquiv (posCoreWires + 18)).apply_symm_apply δ) _
theorem permBits_eBarPos_meas (γ : BitAssignment (posCoreWires + 18)) (q : Fin 18) : permBits
    eBarPos γ (selMeasInAct posCoreWires q) = γ (selMeasInAct posCoreWires q) := by
  let z := (basisBitsEquiv (posCoreWires + 18)).symm γ
  have hz : basisBits (posCoreWires + 18) z = γ := (basisBitsEquiv _).apply_symm_apply γ
  let rBar := (selDataInAct posCoreWires).compose selCore80InPos
  have hnot : selMeasInAct posCoreWires q ∉ Set.range rBar.wires :=
    fun ⟨k, hk⟩ ↦ (selDataInAct_disj_selMeasInAct posCoreWires).ne (selCore80InPos k) q hk
  dsimp only [permBits, eBarPos]
  rw [BoothOpt_Anchor218CachedTrueSwapOuter.liftRegPerm_apply,
      QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnot, hz]
theorem permBits_eBarPos_data (γ : BitAssignment (posCoreWires + 18))
    (i : Fin posCoreWires) :
    let γ80 : BitAssignment (fullSysCoreWires 80) :=
      fun k ↦ γ (selDataInAct posCoreWires (selCore80InPos k))
    permBits eBarPos γ (selDataInAct posCoreWires i) =
      swapElec0Bits (coinBarrelIdxFast (le_refl 80) γ80) γ80
        (⟨i.val, i.isLt.trans_eq posCoreWires_eq_fullSysCoreWires80⟩ :
          Fin (fullSysCoreWires 80)) := by
  intro γ80
  let z := (basisBitsEquiv (posCoreWires + 18)).symm γ
  have hz : basisBits (posCoreWires + 18) z = γ := (basisBitsEquiv _).apply_symm_apply γ
  let rBar := (selDataInAct posCoreWires).compose selCore80InPos
  let i80 : Fin (fullSysCoreWires 80) :=
    ⟨i.val, i.isLt.trans_eq posCoreWires_eq_fullSysCoreWires80⟩
  have hrBar : rBar i80 = selDataInAct posCoreWires i := by
    change selDataInAct posCoreWires (selCore80InPos i80) = selDataInAct posCoreWires i
    congr 1; apply Fin.ext; simp [selCore80InPos, i80]
  have hexBits : basisBits (fullSysCoreWires 80) (rBar.extractIndex z) = γ80 := by
    funext k
    rw [QRegister.basisBits_extractIndex, hz]; rfl
  dsimp only [permBits, eBarPos]
  rw [← hrBar, BoothOpt_Anchor218CachedTrueSwapOuter.liftRegPerm_apply,
      QRegister.basisBits_replaceIndex_apply,
      congrFun (basisBits_coinBarrelPermFast_eq (le_refl 80) (rBar.extractIndex z)) i80]
  dsimp only [coinBarrelBitFnFast]
  rw [hexBits]
theorem unitary_conj_monomialZ8UnitaryN_of_ket {N : ℕ} (U₁ U₂ : Unitary (2 ^ N))
    (f₁ f₂ : BitAssignment N → BitAssignment N) (hU₁ : ∀ β, U₁.1.mulVec (ket β) = ket (f₁ β))
    (hU₂ : ∀ β, U₂.1.mulVec (ket β) = ket (f₂ β)) (wTh : Wire N)
    (d₁ d₂ : BitAssignment N → Bool) (p₁ p₂ : BitAssignment N → ZMod 8)
    (hPhase : ∀ β, p₁ β = p₂ (f₂ (f₁ β))) (hKet : ∀ β, flipThClean wTh d₁ β = f₁ (f₂
    (flipThClean wTh d₂ (f₂ (f₁ β))))) : monomialZ8UnitaryN wTh d₁ p₁ = (U₁ * U₂) *
    monomialZ8UnitaryN wTh d₂ p₂ * (U₂ * U₁) := by
  apply Subtype.ext
  apply OctahedralOrbit.matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul]
  rw[ket_monomialZ8UnitaryN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hU₁, hU₂, ket_monomialZ8UnitaryN,
      Matrix.mulVec_smul, hU₂, Matrix.mulVec_smul, hU₁, hPhase β, hKet β]
attribute [irreducible] permBits eS0Pos eBarPos
open Classical in
theorem anchor_bits_high
    {s0B barB : BitAssignment (posCoreWires + 18) → BitAssignment (posCoreWires + 18)}
    (hs0Not : ∀ δ {i : Fin posCoreWires}, i ∉ Set.range rSlot0Pos.wires →
      s0B δ (selDataInAct posCoreWires i) = δ (selDataInAct posCoreWires i))
    (hbarD : ∀ γ (i : Fin posCoreWires),
      let γ80 : BitAssignment (fullSysCoreWires 80) :=
        fun k ↦ γ (selDataInAct posCoreWires (selCore80InPos k))
      barB γ (selDataInAct posCoreWires i) =
        swapElec0Bits (coinBarrelIdxFast (le_refl 80) γ80) γ80
          ⟨i.val, i.isLt.trans_eq posCoreWires_eq_fullSysCoreWires80⟩)
    (β : BitAssignment (posCoreWires + 18))
    (i : Fin posCoreWires) (hi : 3924 ≤ i.val) :
    s0B (barB β) (selDataInAct posCoreWires i) = β (selDataInAct posCoreWires i) := by
  have hnot : i ∉ Set.range rSlot0Pos.wires := by
    rintro ⟨q, hq⟩
    have hv := congrArg Fin.val hq
    simp [rSlot0Pos, rElecSlot, QRegExt.ofFin] at hv
    have := q.isLt; omega
  rw [hs0Not _ hnot, hbarD]
  let β80 : BitAssignment (fullSysCoreWires 80) :=
    fun k ↦ β (selDataInAct posCoreWires (selCore80InPos k))
  let i80 : Fin (fullSysCoreWires 80) :=
    ⟨i.val, i.isLt.trans_eq posCoreWires_eq_fullSysCoreWires80⟩
  rw [swapElec0Bits_eq_comp_wire]
  have hsw : swapElec0Wire (coinBarrelIdxFast (le_refl 80) β80) i80 = i80 := by
    have hidxLt := (coinBarrelIdxFast (le_refl 80) β80).isLt
    dsimp [SpecsAux.SpecMirror.numElectrons] at hidxLt
    have hi80 : 3924 ≤ i80.val := hi
    unfold swapElec0Wire
    split_ifs <;> first | rfl | omega
  rw [hsw]
  change β (selDataInAct posCoreWires (selCore80InPos i80)) = _
  apply congrArg (fun k ↦ β (selDataInAct posCoreWires k))
  apply Fin.ext; simp [selCore80InPos, i80]
theorem headEnBoolSpec_of_high_eq {β β' : BitAssignment (posCoreWires + 18)} (hHigh : ∀ i :
    Fin posCoreWires, 3924 ≤ i.val → β' (selDataInAct posCoreWires i) = β (selDataInAct
    posCoreWires i)) : headEnBoolSpec (fun i ↦ β' (selDataInAct posCoreWires i)) =
    headEnBoolSpec (fun i ↦ β (selDataInAct posCoreWires i)) := by
  let rC := QRegExt.ofFin posCoreWires
  have hNuc : regVal (rNucIdx rC) (fun i ↦ β' (selDataInAct posCoreWires i)) =
      regVal (rNucIdx rC) (fun i ↦ β (selDataInAct posCoreWires i)) := by
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    have hd : 3924 ≤ (rNucIdx rC d).val := by
      have := d.isLt; simp [rC, rNucIdx, rSubPayloadCore]; omega
    exact congrArg (fun b : ZMod 2 ↦ b.val * 2 ^ d.val) (hHigh (rNucIdx rC d) hd)
  have hAnc : regVal (rAnchorIdx rC) (fun i ↦ β' (selDataInAct posCoreWires i)) =
      regVal (rAnchorIdx rC) (fun i ↦ β (selDataInAct posCoreWires i)) := by
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    have hd : 3924 ≤ (rAnchorIdx rC d).val := by
      have := d.isLt; simp [rC, rAnchorIdx, rSubPayloadCore]; omega
    exact congrArg (fun b : ZMod 2 ↦ b.val * 2 ^ d.val) (hHigh (rAnchorIdx rC d) hd)
  unfold headEnBoolSpec
  dsimp only
  rw [hHigh (wSlot2Core rC) (by simp [rC, wSlot2Core]),
      hHigh (wSlot1Core rC) (by simp [rC, wSlot1Core]),
      hHigh (wSlot0Core rC) (by simp [rC, wSlot0Core]),
      hHigh (wSubReject rC) (by simp [rC, wSubReject, rSubPayloadCore]),
      hHigh (wIsHead rC) (by simp [rC, wIsHead, rSubPayloadCore]),
      hNuc, hAnc]
theorem coinBarrelIdxFast_of_headEn (β : BitAssignment (posCoreWires + 18)) (hEn :
    headEnBoolSpec (fun i ↦ β (selDataInAct posCoreWires i)) = true) : (coinBarrelIdxFast
    (le_refl 80) (fun k ↦ β (selDataInAct posCoreWires (selCore80InPos k)))).val = regVal
    (rAnchorIdx (selDataInAct posCoreWires)) β := by
  have hEnBool := hEn
  unfold headEnBoolSpec at hEnBool
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    decide_eq_true_eq] at hEnBool
  have hc2 : β (selDataInAct posCoreWires (wSlot2Core (QRegExt.ofFin posCoreWires))) = 0 :=
    hEnBool.1.1.1.1
  have hc1 : β (selDataInAct posCoreWires (wSlot1Core (QRegExt.ofFin posCoreWires))) ≠ 1 :=
    hEnBool.1.1.1.2
  have hu218 : regVal (rAnchorIdx (selDataInAct posCoreWires)) β < 218 :=
    regVal_rAnchorIdx_lt_218_of_headEnBoolSpec (selDataInAct posCoreWires) β hEn
  let β80 : BitAssignment (fullSysCoreWires 80) :=
    fun k ↦ β (selDataInAct posCoreWires (selCore80InPos k))
  have hc1_80 : β80 (iSlot1 80) ≠ 1 := by
    intro h; apply hc1
    exact (congrArg (fun i ↦ β (selDataInAct posCoreWires i))
      (Fin.ext (by simp [selCore80InPos, iSlot1, wSlot1Core]))).symm.trans h
  have hc2_80 : β80 (iSlot2 80) = 0 :=
    (congrArg (fun i ↦ β (selDataInAct posCoreWires i))
      (Fin.ext (by simp [selCore80InPos, iSlot2, wSlot2Core]))).trans hc2
  have hj80 : ∀ j : Fin 8, 3968 + j.val < fullSysCoreWires 80 := fun j ↦ by
    rw [fullSysCoreWires80_eq_4034_assoc]; have := j.isLt; omega
  have hu8_eq : CoinDispatchedBarrel288.Internal.bitsVal
        (fun j : Fin 8 ↦ β80 ⟨3968 + j.val, hj80 j⟩) =
      regVal (rAnchorIdx (selDataInAct posCoreWires)) β := by
    unfold CoinDispatchedBarrel288.Internal.bitsVal regVal bitsVal
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : selCore80InPos ⟨3968 + j.val, hj80 j⟩ =
        rAnchorIdx (QRegExt.ofFin posCoreWires) j := by
      apply Fin.ext; simp [selCore80InPos, rAnchorIdx, rSubPayloadCore]; omega
    dsimp only [β80]
    rw [hj]; rfl
  unfold coinBarrelIdxFast
  rw [ite_false_eq hc1_80, ite_true_eq hc2_80]
  dsimp only
  rw [hu8_eq, dite_true_eq hu218]
open Classical in
theorem headAnchorCoreZ8Spec_of_abstract
    {s0B barB : BitAssignment (posCoreWires + 18) → BitAssignment (posCoreWires + 18)}
    (hs0D0 : ∀ δ (q : Fin 18),
      s0B δ (selDataInAct posCoreWires (rSlot0Pos q)) = δ (selMeasInAct posCoreWires q))
    (hs0Not : ∀ δ {i : Fin posCoreWires}, i ∉ Set.range rSlot0Pos.wires →
      s0B δ (selDataInAct posCoreWires i) = δ (selDataInAct posCoreWires i))
    (hbarM : ∀ γ (q : Fin 18),
      barB γ (selMeasInAct posCoreWires q) = γ (selMeasInAct posCoreWires q))
    (hbarD : ∀ γ (i : Fin posCoreWires),
      let γ80 : BitAssignment (fullSysCoreWires 80) :=
        fun k ↦ γ (selDataInAct posCoreWires (selCore80InPos k))
      barB γ (selDataInAct posCoreWires i) =
        swapElec0Bits (coinBarrelIdxFast (le_refl 80) γ80) γ80
          ⟨i.val, i.isLt.trans_eq posCoreWires_eq_fullSysCoreWires80⟩)
    (β : BitAssignment (posCoreWires + 18)) :
    headAnchorCoreZ8Spec β =
      headPhaseMod4Origin0AllZeroZ8Spec
        (fun i ↦ s0B (barB β) (selDataInAct posCoreWires i)) := by
  have hHigh : ∀ i : Fin posCoreWires, 3924 ≤ i.val →
      s0B (barB β) (selDataInAct posCoreWires i) = β (selDataInAct posCoreWires i) :=
    anchor_bits_high hs0Not hbarD β
  let dEn : BitAssignment (posCoreWires + 18) → Bool :=
    fun γ ↦ headEnBoolSpec (fun i ↦ γ (selDataInAct posCoreWires i))
  let β' := s0B (barB β)
  unfold headAnchorCoreZ8Spec headPhaseMod4Origin0AllZeroZ8Spec
  have hdEq : dEn β' = dEn β := headEnBoolSpec_of_high_eq hHigh
  change (if Bool.not (dEn β) then 0 else _) = (if Bool.not (dEn β') then 0 else _)
  rw [hdEq]
  cases hEn : dEn β
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    let rC := QRegExt.ofFin posCoreWires
    have hs0 : headS0Bool (fun i ↦ s0B (barB β) (selDataInAct posCoreWires i)) =
        (β (wSlot0Core (selDataInAct posCoreWires)) == 1) := by
      unfold headS0Bool
      dsimp only
      rw [hHigh (wSlot0Core rC) (by simp [rC, wSlot0Core])]; rfl
    have hth : (if ((fun i ↦ s0B (barB β) (selDataInAct posCoreWires i))
          (wHeadThresh (QRegExt.ofFin posCoreWires)) == 1) = true then (4 : ZMod 8) else 0) =
        (if (β (wHeadThresh (selDataInAct posCoreWires)) == 1) = true then 4 else 0) :=
      congrArg (fun x : ZMod 2 ↦ if (x == 1) = true then (4 : ZMod 8) else 0)
        (hHigh (wHeadThresh rC) (by simp [rC, wHeadThresh, rSubPayloadCore]))
    rw [hs0, hth]
    congr 1; congr 1
    let β'L : BitAssignment posCoreWires := fun i ↦ β' (selDataInAct posCoreWires i)
    let S_all := headHitSetOrigin0AllZeroSpec β'L
    let S_0 := S_all.filter (fun e : Fin 218 ↦ e = 0)
    let S_pos := S_all.filter (fun e : Fin 218 ↦ e ≠ 0)
    have hSplitCard : (S_all.card : ZMod 8) = (S_pos.card : ZMod 8) + (S_0.card : ZMod 8) := by
      have hUnion : S_all = S_pos ∪ S_0 := by
        ext x; simp only [S_pos, S_0, Finset.mem_union, Finset.mem_filter]
        by_cases hx : x = 0 <;> simp [hx]
      have hDisjS : Disjoint S_pos S_0 :=
        Finset.disjoint_left.mpr fun x h1 h2 ↦
          (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      have hAdd : S_all.card = S_pos.card + S_0.card := by
        rw [hUnion, Finset.card_union_of_disjoint hDisjS]
      rw [hAdd, Nat.cast_add]
    have hCoordZeroIff : ∀ {M : ℕ} (rS : QRegister 18 M) (γ : BitAssignment M),
        slotSubGridCoord64 rS γ = (fun _ ↦ 0) ↔ ∀ q : Fin 18, γ (rS q) = 0 := by
      intro M rS γ
      constructor
      · intro h0 q
        let hw : Fin 3 := ⟨q.val / 6, by have := q.isLt; omega⟩
        let hj : Fin 6 := ⟨5 - q.val % 6, by omega⟩
        have hCoord := congrArg Fin.val (congrFun h0 hw)
        change regVal (axisBitRev6 rS hw) γ = 0 at hCoord
        have hbv : bitsVal (fun k : Fin 6 ↦ γ (axisBitRev6 rS hw k)) =
            bitsVal (fun _ : Fin 6 ↦ (0 : ZMod 2)) := by
          simpa [regVal, bitsVal] using hCoord
        have hfn := congrFun (bitsVal_injective hbv) hj
        change γ (rS ⟨6 * hw.val + (5 - hj.val), _⟩) = 0 at hfn
        have hidx : (⟨6 * hw.val + (5 - hj.val), by omega⟩ : Fin 18) = q := by
          apply Fin.ext; dsimp [hw, hj]; have := q.isLt; omega
        rwa [hidx] at hfn
      · intro hall
        funext w; apply Fin.ext
        change regVal (axisBitRev6 rS w) γ = 0
        unfold regVal bitsVal
        simp [axisBitRev6, hall]
    change _ = (S_all.card : ZMod 8)
    rw [hSplitCard]
    refine congrArg₂ (· + ·) ?_ ?_
    · let β80 : BitAssignment (fullSysCoreWires 80) :=
        fun k ↦ β (selDataInAct posCoreWires (selCore80InPos k))
      let idx : Fin 218 :=
        ⟨(coinBarrelIdxFast (le_refl 80) β80).val, (coinBarrelIdxFast (le_refl 80) β80).isLt⟩
      have hIdxVal : idx.val = regVal (rAnchorIdx (selDataInAct posCoreWires)) β :=
        coinBarrelIdxFast_of_headEn β hEn
      have hSlotSwap (e : Fin 218) (hev0 : e.val ≠ 0) (q : Fin 18) :
          s0B (barB β) (selDataInAct posCoreWires (rElecSlot rC e q)) =
            β (selDataInAct posCoreWires (rElecSlot rC (Equiv.swap (0 : Fin 218) idx e) q)) := by
        have hnot0 : rElecSlot rC e q ∉ Set.range rSlot0Pos.wires := by
          rintro ⟨q', hq'⟩
          have hv := congrArg Fin.val hq'
          simp [rC, QRegExt.ofFin, rSlot0Pos, rElecSlot] at hv
          have hqLt := q'.isLt
          have hePos : 1 ≤ e.val := Nat.pos_of_ne_zero hev0
          omega
        rw [hs0Not _ hnot0, hbarD, swapElec0Bits_eq_comp_wire]
        have hW1 : (⟨(rElecSlot rC e q).val, (rElecSlot rC e q).isLt.trans_eq
            posCoreWires_eq_fullSysCoreWires80⟩ : Wire (fullSysCoreWires 80)) =
            rElec18InCore (by decide : 6 ≤ 80) e q := by
          apply Fin.ext
          simp [rC, QRegExt.ofFin, rElecSlot, rElec18InCore_apply_val]
        rw [hW1, swapElec0Wire_rElec18InCore (by
          decide : 6 ≤ 80) (coinBarrelIdxFast (le_refl 80) β80) e q]
        have hSwapIdx : Equiv.swap (0 : Fin 218) ⟨(coinBarrelIdxFast (le_refl 80) β80).val, _⟩ e =
            Equiv.swap 0 idx e := rfl
        have hSelEq : selCore80InPos (rElec18InCore (by decide : 6 ≤ 80) (Equiv.swap 0 idx e) q) =
            rElecSlot rC (Equiv.swap 0 idx e) q := by
          apply Fin.ext
          simp [rC, QRegExt.ofFin, selCore80InPos, rElec18InCore_apply_val, rElecSlot]
        rw [hSwapIdx, hSelEq]
      have hCardEq : S_pos.card = (anchorCoreHitSet β).card := by
        refine Finset.card_bij (fun e _ ↦ Equiv.swap (0 : Fin 218) idx e) ?_ ?_ ?_
        · intro e he
          simp only [S_pos, S_all, headHitSetOrigin0AllZeroSpec, Finset.mem_filter, Finset.mem_univ,
            true_and] at he
          obtain ⟨he1, he0⟩ := he
          have hev0 : e.val ≠ 0 := fun h ↦ he0 (Fin.ext h)
          rw [ite_false_eq hev0, decide_eq_true_eq] at he1
          have hCoord' : slotSubGridCoord64 ((selDataInAct posCoreWires).compose (rElecSlot rC e))
            β' =
              slotSubGridCoord64 (rElecSlot rC e) β'L := rfl
          rw [← hCoord', hCoordZeroIff] at he1
          simp only [anchorCoreHitSet, Finset.mem_filter, Finset.mem_univ, true_and,
            decide_eq_true_eq]
          have hneIdx : (Equiv.swap (0 : Fin 218) idx e).val ≠
              regVal (rAnchorIdx (selDataInAct posCoreWires)) β := by
            rw [← hIdxVal]
            intro hval
            have hEqIdx : Equiv.swap (0 : Fin 218) idx e = idx := Fin.ext hval
            have : e = 0 := by
              have h2 := congrArg (Equiv.swap (0 : Fin 218) idx) hEqIdx
              rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
            exact he0 this
          refine ⟨hneIdx, fun q ↦ ?_⟩
          have hq := he1 q
          change β' (selDataInAct posCoreWires (rElecSlot rC e q)) = 0 at hq
          dsimp only [β'] at hq
          rw [hSlotSwap e hev0 q] at hq
          exact hq
        · intro e₁ _ e₂ _ hEq
          exact (Equiv.swap (0 : Fin 218) idx).injective hEq
        · intro e' he'
          simp only [anchorCoreHitSet, Finset.mem_filter, Finset.mem_univ, true_and,
            decide_eq_true_eq] at he'
          obtain ⟨hneU, hall0⟩ := he'
          let e := Equiv.swap (0 : Fin 218) idx e'
          refine ⟨e, ?_, Equiv.swap_apply_self _ _ _⟩
          have he_ne0 : e ≠ 0 := by
            intro h0
            have : e' = idx := by
              have h2 := congrArg (Equiv.swap (0 : Fin 218) idx) h0
              simpa [e] using h2
            exact hneU ((congrArg Fin.val this).trans hIdxVal)
          have hev0 : e.val ≠ 0 := fun h ↦ he_ne0 (Fin.ext h)
          simp only [S_pos, S_all, headHitSetOrigin0AllZeroSpec, Finset.mem_filter, Finset.mem_univ,
            true_and]
          refine ⟨?_, he_ne0⟩
          rw [ite_false_eq hev0, decide_eq_true_eq]
          change slotSubGridCoord64 ((selDataInAct posCoreWires).compose (rElecSlot rC e)) β' = _
          rw [hCoordZeroIff]
          intro q
          change s0B (barB β) (selDataInAct posCoreWires (rElecSlot rC e q)) = 0
          rw [hSlotSwap e hev0 q, Equiv.swap_apply_self 0 idx e']
          exact hall0 q
      exact congrArg Nat.cast hCardEq.symm
    · have hSlot0Bits : ∀ q : Fin 18, β'L (rElecSlot rC 0 q) = β (selMeasInAct posCoreWires q) :=
        fun q ↦ by
        change s0B (barB β) (selDataInAct posCoreWires (rSlot0Pos q)) = _
        rw [hs0D0, hbarM]
      have hCoordZero0 : slotSubGridCoord64 (rElecSlot rC 0) β'L = (fun _ ↦ 0) ↔
          ∀ q : Fin 18, β (selMeasInAct posCoreWires q) = 0 := by
        rw [hCoordZeroIff]
        simp_rw [hSlot0Bits]
      have h0Mem : (0 : Fin 218) ∈ S_all ↔ (β (wSlot0Core (selDataInAct posCoreWires)) = 0 ∧ ∀
          q : Fin 18, β (selMeasInAct posCoreWires q) = 0) := by
        simp only [S_all, headHitSetOrigin0AllZeroSpec, Finset.mem_filter, Finset.mem_univ,
          true_and, Fin.val_zero, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true',
            decide_eq_true_eq]
        change (headS0Bool (fun i ↦ s0B (barB β) (selDataInAct posCoreWires i)) = false ∧
          slotSubGridCoord64 (rElecSlot rC 0) β'L = (fun _ ↦ 0)) ↔ _
        rw [hs0, hCoordZero0]
        rcases bit_cases (β (wSlot0Core (selDataInAct posCoreWires))) with hb | hb <;> simp [hb]
      unfold anchorSlotHitZ8
      by_cases hCond : β (wSlot0Core (selDataInAct posCoreWires)) = 0 ∧
          ∀ q : Fin 18, β (selMeasInAct posCoreWires q) = 0
      · have hS0Eq : S_0 = {(0 : Fin 218)} := by
          ext x; simp only [S_0, Finset.mem_filter, Finset.mem_singleton]
          exact ⟨fun h ↦ h.2, fun hx ↦ ⟨hx ▸ h0Mem.mpr hCond, hx⟩⟩
        rw [ite_true_eq hCond, hS0Eq]; rfl
      · have hS0Eq : S_0 = ∅ := by
          ext x; simp only [S_0, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hmem hx; exact hCond (h0Mem.mp (hx ▸ hmem))
        rw [ite_false_eq hCond, hS0Eq]; rfl
open Classical in
theorem flipThClean_headAnchorCore_of_abstract
    {s0B barB : BitAssignment (posCoreWires + 18) → BitAssignment (posCoreWires + 18)}
    (hs0Inv : ∀ γ, s0B (s0B γ) = γ)
    (hbarInv : ∀ γ, barB (barB γ) = γ)
    (hs0M : ∀ δ (q : Fin 18),
      s0B δ (selMeasInAct posCoreWires q) = δ (selDataInAct posCoreWires (rSlot0Pos q)))
    (hs0D0 : ∀ δ (q : Fin 18),
      s0B δ (selDataInAct posCoreWires (rSlot0Pos q)) = δ (selMeasInAct posCoreWires q))
    (hs0Not : ∀ δ {i : Fin posCoreWires}, i ∉ Set.range rSlot0Pos.wires →
      s0B δ (selDataInAct posCoreWires i) = δ (selDataInAct posCoreWires i))
    (hbarM : ∀ γ (q : Fin 18),
      barB γ (selMeasInAct posCoreWires q) = γ (selMeasInAct posCoreWires q))
    (hbarD : ∀ γ (i : Fin posCoreWires),
      let γ80 : BitAssignment (fullSysCoreWires 80) :=
        fun k ↦ γ (selDataInAct posCoreWires (selCore80InPos k))
      barB γ (selDataInAct posCoreWires i) =
        swapElec0Bits (coinBarrelIdxFast (le_refl 80) γ80) γ80
          ⟨i.val, i.isLt.trans_eq posCoreWires_eq_fullSysCoreWires80⟩)
    (β : BitAssignment (posCoreWires + 18)) :
    let wTh := wHeadThresh (selDataInAct posCoreWires)
    let dEn : BitAssignment (posCoreWires + 18) → Bool :=
      fun γ ↦ headEnBoolSpec (fun i ↦ γ (selDataInAct posCoreWires i))
    flipThClean wTh dEn β =
      barB (s0B (flipThClean wTh dEn (s0B (barB β)))) := by
  intro wTh dEn
  let β' := s0B (barB β)
  have hdClean : ∀ γ : BitAssignment (posCoreWires + 18),
      dEn (Function.update γ wTh 0) = dEn γ := fun γ ↦ by
    have hUpd : (fun i ↦ Function.update γ wTh 0 (selDataInAct posCoreWires i)) =
        Function.update (fun i ↦
          γ (selDataInAct posCoreWires i)) (wHeadThresh (QRegExt.ofFin posCoreWires)) 0 := by
      funext i
      by_cases hi : i = wHeadThresh (QRegExt.ofFin posCoreWires)
      · subst hi; exact Function.update_self _ 0 γ
      · have hne : selDataInAct posCoreWires i ≠ wTh :=
          fun h ↦ hi ((selDataInAct posCoreWires).wires.injective h)
        rw [Function.update_of_ne hne, Function.update_of_ne hi]
    dsimp only [dEn]
    rw [hUpd, headEnBoolSpec_update_wHeadThresh]
  have hdEq : dEn β' = dEn β := headEnBoolSpec_of_high_eq (anchor_bits_high hs0Not hbarD β)
  unfold flipThClean
  change flipTh wTh (dEn (Function.update β wTh 0)) β =
    barB (s0B (flipTh wTh (dEn (Function.update β' wTh 0)) β'))
  rw [hdClean β, hdClean β', hdEq]
  cases hEn : dEn β
  · have hF0 : ∀ γ, flipTh wTh false γ = γ := fun γ ↦ by unfold flipTh; simp
    rw [hF0, hF0]
    dsimp only [β']
    rw [hs0Inv, hbarInv]
  · have hF1 : ∀ γ, flipTh wTh true γ = Function.update γ wTh (γ wTh + 1) :=
      fun γ ↦ by unfold flipTh; simp
    rw [hF1, hF1]
    have hwThNot0 : wHeadThresh (QRegExt.ofFin posCoreWires) ∉ Set.range rSlot0Pos.wires := by
      rintro ⟨q, hq⟩
      have hv := congrArg Fin.val hq
      have h1 : (rSlot0Pos q).val = q.val := by simp [rSlot0Pos, rElecSlot]
      have h2 : (wHeadThresh (QRegExt.ofFin posCoreWires)).val = 3985 := by
        simp [wHeadThresh, rSubPayloadCore]
      have := q.isLt; omega
    have hS0Upd : s0B (Function.update β' wTh (β' wTh + 1)) =
        Function.update (barB β) wTh (barB β wTh + 1) := by
      have hInvS0 : s0B β' = barB β := hs0Inv _
      funext w
      revert w
      refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_)
      · rw [← selDataInAct_apply i]
        by_cases hi0 : i ∈ Set.range rSlot0Pos.wires
        · obtain ⟨q', rfl⟩ := hi0
          have hneM : selMeasInAct posCoreWires q' ≠ wTh :=
            ((selDataInAct_disj_selMeasInAct posCoreWires).ne _ q').symm
          have hneD : selDataInAct posCoreWires (rSlot0Pos q') ≠ wTh :=
            fun h ↦ hwThNot0 ⟨q', (selDataInAct posCoreWires).wires.injective h⟩
          rw[hs0D0, Function.update_of_ne hneM, Function.update_of_ne hneD, ← hInvS0, hs0D0]
        · rw [hs0Not _ hi0]
          by_cases hiTh : selDataInAct posCoreWires i = wTh
          · rw [hiTh, Function.update_self, Function.update_self,
                ← hInvS0, ← hiTh, hs0Not _ hi0]
          · rw[Function.update_of_ne hiTh, Function.update_of_ne hiTh, ← hInvS0, hs0Not _ hi0]
      · rw [← selMeasInAct_apply q, hs0M]
        have hneD : selDataInAct posCoreWires (rSlot0Pos q) ≠ wTh :=
          fun h ↦ hwThNot0 ⟨q, (selDataInAct posCoreWires).wires.injective h⟩
        have hneM : selMeasInAct posCoreWires q ≠ wTh :=
          ((selDataInAct_disj_selMeasInAct posCoreWires).ne _ q).symm
        rw[Function.update_of_ne hneD, Function.update_of_ne hneM, ← hInvS0, hs0M]
    rw [hS0Upd]
    let δ := barB β
    have hSwFixHigh (u : Fin SpecsAux.SpecMirror.numElectrons) (k : Fin (fullSysCoreWires 80))
        (hk : 3924 ≤ k.val) : swapElec0Wire u k = k := by
      have hu := u.isLt
      dsimp [SpecsAux.SpecMirror.numElectrons] at hu
      unfold swapElec0Wire
      split_ifs
      all_goals first | rfl | omega
    have hδHigh : ∀ k : Fin (fullSysCoreWires 80), 3924 ≤ k.val →
        δ (selDataInAct posCoreWires (selCore80InPos k)) =
          β (selDataInAct posCoreWires (selCore80InPos k)) := by
      intro k hk
      dsimp only [δ]
      rw [hbarD]
      let β80 : BitAssignment (fullSysCoreWires 80) :=
        fun m ↦ β (selDataInAct posCoreWires (selCore80InPos m))
      rw [swapElec0Bits_eq_comp_wire]
      have hkEq : (⟨(selCore80InPos k).val, (selCore80InPos k).isLt.trans_eq
          posCoreWires_eq_fullSysCoreWires80⟩ : Wire (fullSysCoreWires 80)) = k := by
        apply Fin.ext
        simp [selCore80InPos]
      rw [hkEq, hSwFixHigh _ k hk]
    let δUpd := Function.update δ wTh (δ wTh + 1)
    let δ80 : BitAssignment (fullSysCoreWires 80) :=
      fun k ↦ δ (selDataInAct posCoreWires (selCore80InPos k))
    let δUpd80 : BitAssignment (fullSysCoreWires 80) :=
      fun k ↦ δUpd (selDataInAct posCoreWires (selCore80InPos k))
    have hEnBool := hEn
    dsimp only [dEn, headEnBoolSpec] at hEnBool
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hEnBool
    have hc2_β : β (selDataInAct posCoreWires (wSlot2Core (QRegExt.ofFin posCoreWires))) = 0 :=
      hEnBool.1.1.1.1
    have hc1_β : β (selDataInAct posCoreWires (wSlot1Core (QRegExt.ofFin posCoreWires))) ≠ 1 :=
      hEnBool.1.1.1.2
    have hNotTh : ∀ k : Fin (fullSysCoreWires 80), k.val ≠ 3985 → δUpd80 k = δ80 k := by
      intro k hk
      have hne : selDataInAct posCoreWires (selCore80InPos k) ≠ wTh := by
        intro h
        apply hk
        simpa [selCore80InPos] using
          congrArg Fin.val ((selDataInAct posCoreWires).wires.injective h)
      dsimp only [δUpd80, δ80, δUpd]
      exact Function.update_of_ne hne (δ wTh + 1) δ
    have hIdxEq : coinBarrelIdxFast (le_refl 80) δUpd80 = coinBarrelIdxFast (le_refl 80) δ80 := by
      have hc1_δ : δ80 (iSlot1 80) ≠ 1 := by
        dsimp only [δ80]
        rw [hδHigh (iSlot1 80) (by simp)]
        intro h; apply hc1_β
        exact (congrArg (fun i ↦ β (selDataInAct posCoreWires i))
          (Fin.ext (by simp [selCore80InPos, iSlot1, wSlot1Core]))).symm.trans h
      have hc2_δ : δ80 (iSlot2 80) = 0 := by
        dsimp only [δ80]
        rw [hδHigh (iSlot2 80) (by simp)]
        exact (congrArg (fun i ↦ β (selDataInAct posCoreWires i))
          (Fin.ext (by simp [selCore80InPos, iSlot2, wSlot2Core]))).trans hc2_β
      have hc1_u : δUpd80 (iSlot1 80) = δ80 (iSlot1 80) := hNotTh (iSlot1 80) (by simp)
      have hc2_u : δUpd80 (iSlot2 80) = δ80 (iSlot2 80) := hNotTh (iSlot2 80) (by simp)
      have hj80 : ∀ j : Fin 8, 3968 + j.val < fullSysCoreWires 80 := fun j ↦ by
        rw [fullSysCoreWires80_eq_4034_assoc]; have := j.isLt; omega
      have hu8 : (fun j : Fin 8 ↦ δUpd80 ⟨3968 + j.val, hj80 j⟩) =
          (fun j : Fin 8 ↦ δ80 ⟨3968 + j.val, hj80 j⟩) :=
        funext fun j ↦ hNotTh _ (by have := j.isLt; dsimp; omega)
      unfold coinBarrelIdxFast
      rw [hc1_u, hc2_u, ite_false_eq hc1_δ, ite_false_eq hc1_δ,
          ite_true_eq hc2_δ, ite_true_eq hc2_δ, hu8]
    have hInvBar : barB δ = β := hbarInv β
    let w3985_80 : Fin (fullSysCoreWires 80) :=
      ⟨3985, by rw [fullSysCoreWires80_eq_4034_assoc]; omega⟩
    funext w; revert w
    refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_)
    · rw [← selDataInAct_apply i]
      have hLHS : Function.update β wTh (β wTh + 1) (selDataInAct posCoreWires i) =
          if selDataInAct posCoreWires i = wTh then β wTh + 1 else
            β (selDataInAct posCoreWires i) := by
        by_cases h : selDataInAct posCoreWires i = wTh
        · rw [h, Function.update_self, ite_true_eq rfl]
        · rw [Function.update_of_ne h, ite_false_eq h]
      let i80 : Fin (fullSysCoreWires 80) :=
        ⟨i.val, i.isLt.trans_eq posCoreWires_eq_fullSysCoreWires80⟩
      rw [hLHS, hbarD δUpd i, hIdxEq, swapElec0Bits_eq_comp_wire]
      by_cases hThI : selDataInAct posCoreWires i = wTh
      · rw [ite_true_eq hThI]
        have hiVal : i80.val = 3985 :=
          congrArg Fin.val ((selDataInAct posCoreWires).wires.injective hThI)
        rw [hSwFixHigh _ i80 (by omega)]
        have hSelTh : selDataInAct posCoreWires (selCore80InPos i80) = wTh := by
          rw [← hThI]; apply congrArg (selDataInAct posCoreWires); apply Fin.ext;
            simp [selCore80InPos, i80]
        change β wTh + 1 = δUpd (selDataInAct posCoreWires (selCore80InPos i80))
        rw [hSelTh]
        change β wTh + 1 = Function.update δ wTh (δ wTh + 1) wTh
        rw [Function.update_self]
        have hδTh : δ wTh = β wTh := by
          have := hδHigh w3985_80 (by dsimp [w3985_80]; omega)
          have hSel3985 : selDataInAct posCoreWires (selCore80InPos w3985_80) = wTh := by
            dsimp [wTh, wHeadThresh, rSubPayloadCore]; apply congrArg (selDataInAct posCoreWires);
              apply Fin.ext
            simp [selCore80InPos, w3985_80]
          rwa [hSel3985] at this
        rw [hδTh]
      · rw [ite_false_eq hThI]
        have hiNe3985 : i.val ≠ 3985 := fun hv ↦
          hThI (congrArg (selDataInAct posCoreWires) (Fin.ext hv))
        have hswNe3985 : (swapElec0Wire (coinBarrelIdxFast (le_refl 80) δ80) i80).val ≠ 3985 := by
          intro hv
          have hEqW : swapElec0Wire (coinBarrelIdxFast (le_refl 80) δ80) i80 = w3985_80 :=
            Fin.ext hv
          have hInv := congrArg (swapElec0Wire (coinBarrelIdxFast (le_refl 80) δ80)) hEqW
          rw [swapElec0Wire_involutive, hSwFixHigh _ w3985_80 (by dsimp [w3985_80]; omega)] at hInv
          exact hiNe3985 (congrArg Fin.val hInv)
        change β (selDataInAct posCoreWires i) =
          δUpd80 (swapElec0Wire (coinBarrelIdxFast (le_refl 80) δ80) i80)
        rw [hNotTh _ hswNe3985,
            ← swapElec0Bits_eq_comp_wire (coinBarrelIdxFast (le_refl 80) δ80) δ80 i80,
            ← hbarD δ i, hInvBar]
    · rw [← selMeasInAct_apply q]
      have hneM : selMeasInAct posCoreWires q ≠ wTh :=
        ((selDataInAct_disj_selMeasInAct posCoreWires).ne _ q).symm
      rw [Function.update_of_ne hneM, hbarM]
      change β (selMeasInAct posCoreWires q) =
        Function.update (barB β) wTh (barB β wTh + 1) (selMeasInAct posCoreWires q)
      rw [Function.update_of_ne hneM, hbarM]
open Classical in
/-- Exact anchor-frame conjugation identity identifying `uHeadAnchorCore` (`dHeadAnchorCore172`)
with `(τ_pos * σ_0_pos) * uHeadOrigin0Core35 * (σ_0_pos * τ_pos)`. -/
theorem uHeadAnchorCore_eq_anchorConj : uHeadAnchorCore = (τ_pos * σ_0_pos) *
    (selDataInAct posCoreWires).embedUnitary uHeadOrigin0Core35 * (σ_0_pos * τ_pos) := by
  let wTh := wHeadThresh (selDataInAct posCoreWires)
  let dEn : BitAssignment (posCoreWires + 18) → Bool :=
    fun γ ↦ headEnBoolSpec (fun i ↦ γ (selDataInAct posCoreWires i))
  have hEmbOrig : (selDataInAct posCoreWires).embedUnitary uHeadOrigin0Core35 =
      monomialZ8UnitaryN wTh dEn
        (fun γ ↦ headPhaseMod4Origin0AllZeroZ8Spec (fun i ↦ γ (selDataInAct posCoreWires i))) := by
    dsimp only [uHeadOrigin0Core35, wTh, dEn]
    exact embedUnitary_monomialZ8UnitaryN (selDataInAct posCoreWires) _ _ _
  have hConj := unitary_conj_monomialZ8UnitaryN_of_ket τ_pos σ_0_pos (permBits eBarPos)
      (permBits eS0Pos) ket_τ_pos ket_σ_0_pos wTh dEn dEn headAnchorCoreZ8Spec (fun γ ↦
      headPhaseMod4Origin0AllZeroZ8Spec (fun i ↦ γ (selDataInAct posCoreWires i)))
      (headAnchorCoreZ8Spec_of_abstract permBits_eS0Pos_data_slot0 (fun δ _ hi ↦
      permBits_eS0Pos_data_of_not_mem δ hi) permBits_eBarPos_meas permBits_eBarPos_data)
      (flipThClean_headAnchorCore_of_abstract (permBits_involutive eS0Pos_involutive)
      (permBits_involutive eBarPos_involutive) permBits_eS0Pos_meas permBits_eS0Pos_data_slot0
      (fun δ _ hi ↦ permBits_eS0Pos_data_of_not_mem δ hi) permBits_eBarPos_meas
      permBits_eBarPos_data)
  exact hConj.trans (congrArg (fun X ↦ (τ_pos * σ_0_pos) * X * (σ_0_pos * τ_pos)) hEmbOrig.symm)
/-- `0-T`, `0-TOFF` anchor pre-shift static circuit XORing `phcHead_rQRev18 rCore` onto
  `rAnchor18`. -/
noncomputable def cPreShiftAnchor {n : ℕ} (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister
    18 n)
    (hCA : rCore.DisjointWires rAnchor18) : Circuit n :=
  cPreShift0Core.onRegister (rDataSubstSlot0 rSlot0Pos rCore rAnchor18 hCA)
@[simp] theorem count_cPreShiftAnchor_toff {n : ℕ} (rCore : QRegister posCoreWires n)
    (rAnchor18 : QRegister 18 n) (hCA : rCore.DisjointWires rAnchor18) :
    (cPreShiftAnchor rCore rAnchor18 hCA).count TOFF = 0 := by
  simp [cPreShiftAnchor, count_cPreShift0Core_toff]
@[simp] theorem count_cPreShiftAnchor_t {n : ℕ} (rCore : QRegister posCoreWires n)
    (rAnchor18 : QRegister 18 n) (hCA : rCore.DisjointWires rAnchor18) :
    (cPreShiftAnchor rCore rAnchor18 hCA).count T = 0 := by
  simp [cPreShiftAnchor, count_cPreShift0Core_t]
/-- Anchor-frame pre-shift unitary `(τ_pos * σ_0_pos) * cPreShift0Core.eval * (σ_0_pos * τ_pos)`. -/
noncomputable def uPreShiftAnchor : Unitary (2 ^ (posCoreWires + 18)) := (τ_pos * σ_0_pos) *
    (selDataInAct posCoreWires).embedUnitary cPreShift0Core.eval * (σ_0_pos * τ_pos)
open Classical in
theorem comm_singleton_proj_of_ket_perm {N : ℕ} (M : Operator (2 ^ N))
    (f : BitAssignment N → BitAssignment N)
    (hKet : ∀ β : BitAssignment N, M.mulVec (ket β) = ket (f β)) (q : Wire N)
    (hq : ∀ β : BitAssignment N, f β q = β q) (b : Fin 2) : M *
    (QRegister.singleton q).basisOutcomeProjector b =
    (QRegister.singleton q).basisOutcomeProjector b * M := by
  apply OctahedralOrbit.matrix_ext_ket; intro β
  let g0 := (basisBitsEquiv N).symm β
  let g1 := (basisBitsEquiv N).symm (f β)
  have hk0 : (Pi.single g0 (1 : ℂ) : Fin (2 ^ N) → ℂ) = ket β := by
    funext x; simp [g0, ket, basisState]
  have hk1 : (Pi.single g1 (1 : ℂ) : Fin (2 ^ N) → ℂ) = ket (f β) := by
    funext x; simp [g1, ket, basisState]
  have hexEq : (QRegister.singleton q).extractIndex g1 = (QRegister.singleton q).extractIndex g0 :=
    by
    apply eq_of_basisBits_eq; intro idx
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    have hb0 : basisBits N g0 = β := (basisBitsEquiv N).apply_symm_apply β
    have hb1 : basisBits N g1 = f β := (basisBitsEquiv N).apply_symm_apply _
    rw [hb0, hb1]
    have hsq : QRegister.singleton q idx = q := rfl
    rw [hsq, hq β]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hKet β, QRegister.basisOutcomeProjector_eq_diagonal]
  have hL : (Matrix.diagonal fun x ↦
    if (QRegister.singleton q).extractIndex x = b then (1 : ℂ) else 0).mulVec
        (ket (f β)) =
      (if (QRegister.singleton q).extractIndex g1 = b then (1 : ℂ) else 0) • ket (f β) := by
    rw [← hk1, Matrix.diagonal_mulVec_single, mul_one]
    funext x; simp [Pi.single_apply]
  have hR : (Matrix.diagonal fun x ↦
    if (QRegister.singleton q).extractIndex x = b then (1 : ℂ) else 0).mulVec
        (ket β) =
      (if (QRegister.singleton q).extractIndex g0 = b then (1 : ℂ) else 0) • ket β := by
    rw [← hk0, Matrix.diagonal_mulVec_single, mul_one]
    funext x; simp [Pi.single_apply]
  rw [hL, hR, Matrix.mulVec_smul, hKet β, hexEq]
open Classical in
theorem cPreShiftAnchor_eval {n : ℕ} (rCore : QRegister posCoreWires n)
    (rAnchor18 : QRegister 18 n) (hCA : rCore.DisjointWires rAnchor18) :
    (cPreShiftAnchor rCore rAnchor18 hCA).eval =
      (rCore.concat rAnchor18 hCA).embedUnitary uPreShiftAnchor := by
  unfold cPreShiftAnchor uPreShiftAnchor
  rw [Circuit.eval_onRegister, embedUnitary_rDataSubstSlot0_eq]
  apply congrArg (rCore.concat rAnchor18 hCA).embedUnitary
  have hSlot0Eq : selCore80InPos.compose (rFullSysElecSlot (le_refl 80) 0) = rSlot0Pos := by
    apply qreg_ext; intro q; apply Fin.ext
    simp [selCore80InPos, rFullSysElecSlot_val, rSlot0Pos, rElecSlot]
  have hSpec : ActsAsIdOnSpectatorWires selCore80InPos cPreShift0Core.eval := by
    let rSpec := spectatorElecReg selCore80InPos
    have hrSpecRange : ∀ t, 18 ≤ (rSpec t).val ∧ (rSpec t).val < 3924 := fun t ↦ by
      have := t.isLt
      simp [rSpec, spectatorElecReg, selCore80InPos]
      omega
    have hQRevHi : ∀ q : Fin 18, 3924 ≤ (phcHead_rQRev18 (QRegExt.ofFin posCoreWires) q).val :=
      fun q ↦ by revert q; decide
    exact commutesWithReg_of_mulVec_ket_assoc rSpec cPreShift0Core.eval.1
      (fun _ ↦ 1) preShift0Bits
      (fun β ↦ by rw [one_smul]; exact ket_cPreShift0Core β)
      (fun _ _ ↦ rfl)
      (fun β u ↦ by
        funext w
        by_cases hw18 : 18 ≤ w.val
        · rw [preShift0Bits_high _ hw18]
          by_cases hwR : w ∈ Set.range rSpec.wires
          · obtain ⟨t, rfl⟩ := hwR
            rw [writeReg_apply_reg, writeReg_apply_reg]
          · rw [writeReg_apply_of_not_mem _ _ _ _ hwR, writeReg_apply_of_not_mem _ _ _ _ hwR,
                preShift0Bits_high _ hw18]
        · have hlt : w.val < 18 := Nat.lt_of_not_ge hw18
          let q0 : Fin 18 := ⟨w.val, hlt⟩
          have hw0 : w = rElecSlot (QRegExt.ofFin posCoreWires) 0 q0 := by
            apply Fin.ext; simp [rElecSlot, q0]
          have hnot0 : rElecSlot (QRegExt.ofFin posCoreWires) 0 q0 ∉ Set.range rSpec.wires :=
            fun ⟨t, ht⟩ ↦ by
            have := (hrSpecRange t).1; rw [ht, ← hw0] at this; omega
          have hnotQ : phcHead_rQRev18 (QRegExt.ofFin posCoreWires) q0 ∉ Set.range rSpec.wires :=
            fun ⟨t, ht⟩ ↦ by
              have h1 := (hrSpecRange t).2
              have h2 := hQRevHi q0
              rw [← ht] at h2; omega
          rw [hw0, preShift0Bits_elec0,
              writeReg_apply_of_not_mem _ _ _ _ hnot0,
              writeReg_apply_of_not_mem _ _ _ _ hnotQ,
              writeReg_apply_of_not_mem _ _ _ _ hnot0,
              preShift0Bits_elec0])
      (fun β t ↦ preShift0Bits_high β (hrSpecRange t).1)
  have hHigh : PreservesHigh3924On selCore80InPos cPreShift0Core.eval := by
    intro w hw b
    let q := selCore80InPos w
    have hq18 : 18 ≤ q.val := by simp [q, selCore80InPos]; omega
    exact comm_singleton_proj_of_ket_perm cPreShift0Core.eval.1 preShift0Bits
      ket_cPreShift0Core q (fun β ↦ preShift0Bits_high β hq18) b
  have hConj :=
    uLensSwap_slot0_conj_eq_gen (le_refl 80) selCore80InPos cPreShift0Core.eval hSpec hHigh
  dsimp only at hConj
  rw [hSlot0Eq] at hConj
  exact hConj
/-- `0-T`, `0-TOFF` `218`-slot Hadamard circuit on `rCore : QRegister posCoreWires n`
(`cHad217 rCore ;;ᶜ cHadamard18.onRegister (rCore.compose rSlot0Pos)`). -/
def cHad218 {n : ℕ} (rCore : QRegister posCoreWires n) : Circuit n :=
  cHad217 rCore ;;ᶜ cHadamard18.onRegister (rCore.compose rSlot0Pos)
/-- `0-T`, `0-TOFF` inverse `218`-slot Hadamard circuit on `rCore : QRegister posCoreWires n`. -/
def cHad218Inv {n : ℕ} (rCore : QRegister posCoreWires n) : Circuit n :=
  cHadamard18.inverse.onRegister (rCore.compose rSlot0Pos) ;;ᶜ cHad217Inv rCore
/-- `218`-slot Hadamard unitary `rSlot0Pos.embedUnitary uHadamard18 * uHad217` on `posCoreWires`. -/
noncomputable def uHad218 : Unitary (2 ^ posCoreWires) :=
  rSlot0Pos.embedUnitary uHadamard18 * uHad217
@[simp] theorem count_cHad218_toff {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad218 rCore).count TOFF = 0 := by
  simp [cHad218, cHad217_count_TOFF, cHadamard18_count_TOFF]
@[simp] theorem count_cHad218_t {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad218 rCore).count T = 0 := by
  simp [cHad218, cHad217_count_T, cHadamard18_count_T]
@[simp] theorem count_cHad218Inv_toff {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad218Inv rCore).count TOFF = 0 := by
  have h0 : cHadamard18.inverse.count TOFF = 0 := rfl
  simp [cHad218Inv, h0, cHad217Inv_count_TOFF]
@[simp] theorem count_cHad218Inv_t {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad218Inv rCore).count T = 0 := by
  have h0 : cHadamard18.inverse.count T = 0 := rfl
  simp [cHad218Inv, h0, cHad217Inv_count_T]
open Classical in
theorem cHad218_eval {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad218 rCore).eval = rCore.embedUnitary uHad218 := by
  unfold cHad218 uHad218
  rw [Circuit.eval_seq, cHad217_eval, Circuit.eval_onRegister, cHadamard18_eval,
      QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul]
open Classical in
theorem cHad218Inv_eval {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad218Inv rCore).eval = rCore.embedUnitary uHad218⁻¹ := by
  unfold cHad218Inv uHad218
  rw [Circuit.eval_seq, cHad217Inv_eval, Circuit.eval_onRegister, Circuit.eval_inverse,
      cHadamard18_eval, QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul,
      _root_.mul_inv_rev, embedUnitary_inv_symm]
/-- `15,882-T`, `0-TOFF` Hadamard-conjugated shifted `219`-slot masked origin-`0` anchor head
  (`172 ≤ mScr`). -/
noncomputable def dHeadAnchorConjH172 {Var : Type} {n mScr : ℕ} (hm172 : 172 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rScr : QRegister mScr n)
    (hCA : rCore.DisjointWires rAnchor18) (hCS : rCore.DisjointWires rScr)
    (hAS : rAnchor18.DisjointWires rScr) : DynamicCircuit Var n := .seq
    (.circuit (cHad218 rCore)) (.seq (.circuit (cPreShiftAnchor rCore rAnchor18 hCA)) (.seq
    (dHeadAnchorCore172 hm172 v rCore rAnchor18 rScr hCA hCS hAS) (.seq (.circuit
    (cPreShiftAnchor rCore rAnchor18 hCA)) (.circuit (cHad218Inv rCore)))))
@[simp]
theorem count_dHeadAnchorConjH172_toff {Var : Type} {n mScr : ℕ} (hm172 : 172 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rScr : QRegister mScr n)
    (hCA : rCore.DisjointWires rAnchor18) (hCS : rCore.DisjointWires rScr)
    (hAS : rAnchor18.DisjointWires rScr) :
    (dHeadAnchorConjH172 hm172 v rCore rAnchor18 rScr hCA hCS hAS).count TOFF = 0 := by
  simp [dHeadAnchorConjH172]
@[simp]
theorem count_dHeadAnchorConjH172_t {Var : Type} {n mScr : ℕ} (hm172 : 172 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rScr : QRegister mScr n)
    (hCA : rCore.DisjointWires rAnchor18) (hCS : rCore.DisjointWires rScr)
    (hAS : rAnchor18.DisjointWires rScr) :
    (dHeadAnchorConjH172 hm172 v rCore rAnchor18 rScr hCA hCS hAS).count T = 15882 := by
  simp [dHeadAnchorConjH172]
/-- Anchor-frame Hadamard-conjugated head unitary realized by `dHeadAnchorConjH172` on
  `posCoreWires + 18`. -/
noncomputable def uHeadAnchorConjH : Unitary (2 ^ (posCoreWires + 18)) :=
    (selDataInAct posCoreWires).embedUnitary uHad218⁻¹ * (uPreShiftAnchor * (uHeadAnchorCore *
    (uPreShiftAnchor * (selDataInAct posCoreWires).embedUnitary uHad218)))
open Classical in
theorem dHeadAnchorConjH172_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n mScr : ℕ}
    (hm172 : 172 ≤ mScr) (v : Var) (rCore : QRegister posCoreWires n)
    (rAnchor18 : QRegister 18 n) (rScr : QRegister mScr n)
    (hCA : rCore.DisjointWires rAnchor18) (hCS : rCore.DisjointWires rScr)
    (hAS : rAnchor18.DisjointWires rScr) : RealizesEmbeddedUnitaryWithCleanWorkspace
    (rCore.concat rAnchor18 hCA) rScr uHeadAnchorConjH
    (dHeadAnchorConjH172 hm172 v rCore rAnchor18 rScr hCA hCS hAS) := by
  let rCA := rCore.concat rAnchor18 hCA
  have hCAS : rCA.DisjointWires rScr := disjointWires_concat_left _ hCS hAS
  have hData : rCA.compose (selDataInAct posCoreWires) = rCore :=
    concat_compose_selDataInAct rCore rAnchor18 hCA
  have h1 : RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rCA rScr
      ((selDataInAct posCoreWires).embedUnitary uHad218) (.circuit (cHad218 rCore)) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rCA rScr _ _ (by
      rw [cHad218_eval, ← QRegister.embedUnitary_compose, hData])
  have h2 : RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rCA rScr
      uPreShiftAnchor (.circuit (cPreShiftAnchor rCore rAnchor18 hCA)) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rCA rScr _ _ (cPreShiftAnchor_eval rCore
      rAnchor18 hCA)
  have h3 := dHeadAnchorCore172_realizes hm172 v rCore rAnchor18 rScr hCA hCS hAS
  have h5 : RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rCA rScr
      ((selDataInAct posCoreWires).embedUnitary uHad218⁻¹) (.circuit (cHad218Inv rCore)) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rCA rScr _ _ (by
      rw [cHad218Inv_eval, ← QRegister.embedUnitary_compose, hData])
  unfold dHeadAnchorConjH172 uHeadAnchorConjH
  simpa only [_root_.mul_assoc] using h1.seq hCAS (h2.seq hCAS (h3.seq hCAS (h2.seq hCAS h5)))
open Classical in
theorem uHeadAnchorConjH_eq_anchorConj : uHeadAnchorConjH = (τ_pos * σ_0_pos) *
    (selDataInAct posCoreWires).embedUnitary uHeadConjHCore * (σ_0_pos * τ_pos) := by
  let F := τ_pos * σ_0_pos
  let Finv := σ_0_pos * τ_pos
  have hFF : Finv * F = 1 := by
    calc (σ_0_pos * τ_pos) * (τ_pos * σ_0_pos)
        = σ_0_pos * (τ_pos * τ_pos) * σ_0_pos := by simp only [_root_.mul_assoc]
      _ = 1 := by rw [τ_pos_mul_self, mul_one, σ_0_pos_mul_self]
  have hFF' : F * Finv = 1 := by
    calc (τ_pos * σ_0_pos) * (σ_0_pos * τ_pos)
        = τ_pos * (σ_0_pos * σ_0_pos) * τ_pos := by simp only [_root_.mul_assoc]
      _ = 1 := by rw [σ_0_pos_mul_self, mul_one, τ_pos_mul_self]
  have hHadConj : (selDataInAct posCoreWires).embedUnitary uHad218 =
      F * ((selMeasInAct posCoreWires).embedUnitary uHadamard18 *
        (selDataInAct posCoreWires).embedUnitary uHad217) * Finv := by
    have h1 := elecProd218Pos_eq_anchorConj uHadamard18
    change Finv * (selDataInAct posCoreWires).embedUnitary uHad218 * F =
      (selMeasInAct posCoreWires).embedUnitary uHadamard18 *
        (selDataInAct posCoreWires).embedUnitary uHad217 at h1
    calc (selDataInAct posCoreWires).embedUnitary uHad218
        = (F * Finv) * (selDataInAct posCoreWires).embedUnitary uHad218 * (F * Finv) := by
            rw [hFF', one_mul, mul_one]
      _ = F * (Finv * (selDataInAct posCoreWires).embedUnitary uHad218 * F) * Finv := by
            simp only [_root_.mul_assoc]
      _ = F * ((selMeasInAct posCoreWires).embedUnitary uHadamard18 *
            (selDataInAct posCoreWires).embedUnitary uHad217) * Finv := by rw [h1]
  have hσ_inv : σ_0_pos⁻¹ = σ_0_pos := inv_eq_of_mul_eq_one_right σ_0_pos_mul_self
  have hτ_inv : τ_pos⁻¹ = τ_pos := inv_eq_of_mul_eq_one_right τ_pos_mul_self
  have hCommMD : ∀ (A : Unitary (2 ^ posCoreWires)) (B : Unitary (2 ^ 18)),
      (selDataInAct posCoreWires).embedUnitary A * (selMeasInAct posCoreWires).embedUnitary B =
        (selMeasInAct posCoreWires).embedUnitary B * (selDataInAct posCoreWires).embedUnitary A :=
          by
    intro A B; apply Subtype.ext
    exact (selDataInAct posCoreWires).embedMatrix_comm_of_disjoint
      (selMeasInAct posCoreWires) (selDataInAct_disj_selMeasInAct posCoreWires) A.1 B.1
  have hHadInvConj : (selDataInAct posCoreWires).embedUnitary uHad218⁻¹ =
      F * ((selDataInAct posCoreWires).embedUnitary uHad217⁻¹ *
        (selMeasInAct posCoreWires).embedUnitary uHadamard18⁻¹) * Finv := by
    rw [← embedUnitary_inv_symm, hHadConj]
    simp only [F, Finv, _root_.mul_inv_rev, hσ_inv, hτ_inv, embedUnitary_inv_symm, _root_.mul_assoc]
  have hF_mul : ∀ X Y : Unitary (2 ^ (posCoreWires + 18)),
      (F * X * Finv) * (F * Y * Finv) = F * (X * Y) * Finv := fun X Y ↦ by
    calc (F * X * Finv) * (F * Y * Finv)
        = F * X * (Finv * F) * Y * Finv := by simp only [_root_.mul_assoc]
      _ = F * (X * Y) * Finv := by rw [hFF, mul_one]; simp only [_root_.mul_assoc]
  have hMid3 : uPreShiftAnchor * (uHeadAnchorCore * uPreShiftAnchor) =
      F * (selDataInAct posCoreWires).embedUnitary uHeadPhaseMod4Origin0Repaired * Finv := by
    rw [uHeadAnchorCore_eq_anchorConj]
    change (F * (selDataInAct posCoreWires).embedUnitary cPreShift0Core.eval * Finv) *
        ((F * (selDataInAct posCoreWires).embedUnitary uHeadOrigin0Core35 * Finv) *
          (F * (selDataInAct posCoreWires).embedUnitary cPreShift0Core.eval * Finv)) = _
    rw [hF_mul, hF_mul, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul,
        ← _root_.mul_assoc cPreShift0Core.eval, cPreShift0Core_conj_uHeadOrigin0Core35_eq]
  unfold uHeadAnchorConjH
  have hReassoc : (selDataInAct posCoreWires).embedUnitary uHad218⁻¹ * (uPreShiftAnchor *
      (uHeadAnchorCore * (uPreShiftAnchor * (selDataInAct posCoreWires).embedUnitary
      uHad218))) = (selDataInAct posCoreWires).embedUnitary uHad218⁻¹ * ((uPreShiftAnchor *
      (uHeadAnchorCore * uPreShiftAnchor)) * (selDataInAct posCoreWires).embedUnitary uHad218)
      := by
    simp only [_root_.mul_assoc]
  rw [hReassoc, hHadInvConj, hMid3, hHadConj, hF_mul, hF_mul]
  apply congrArg (fun X ↦ F * X * Finv)
  calc ((selDataInAct posCoreWires).embedUnitary uHad217⁻¹ *
          (selMeasInAct posCoreWires).embedUnitary uHadamard18⁻¹) *
        ((selDataInAct posCoreWires).embedUnitary uHeadPhaseMod4Origin0Repaired *
          ((selMeasInAct posCoreWires).embedUnitary uHadamard18 *
            (selDataInAct posCoreWires).embedUnitary uHad217))
      = (selDataInAct posCoreWires).embedUnitary uHad217⁻¹ *
          ((selMeasInAct posCoreWires).embedUnitary uHadamard18⁻¹ *
            ((selDataInAct posCoreWires).embedUnitary uHeadPhaseMod4Origin0Repaired *
              (selMeasInAct posCoreWires).embedUnitary uHadamard18)) *
          (selDataInAct posCoreWires).embedUnitary uHad217 := by
          simp only [_root_.mul_assoc]
    _ = (selDataInAct posCoreWires).embedUnitary uHad217⁻¹ *
          (((selMeasInAct posCoreWires).embedUnitary uHadamard18⁻¹ *
              (selMeasInAct posCoreWires).embedUnitary uHadamard18) *
            (selDataInAct posCoreWires).embedUnitary uHeadPhaseMod4Origin0Repaired) *
          (selDataInAct posCoreWires).embedUnitary uHad217 := by
          rw [hCommMD uHeadPhaseMod4Origin0Repaired uHadamard18,
              ← _root_.mul_assoc ((selMeasInAct posCoreWires).embedUnitary uHadamard18⁻¹)]
    _ = (selDataInAct posCoreWires).embedUnitary uHeadConjHCore := by
          rw [← QRegister.embedUnitary_mul, inv_mul_cancel, QRegister.embedUnitary_one, one_mul,
              ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
          rfl
/-- Selector `rCoreFull.compose selPosCoreInCore80 : QRegister posCoreWires kFull80`. -/
def rPosCoreInFull : QRegister posCoreWires kFull80 := rCoreFull.compose selPosCoreInCore80
open Classical in
theorem selLiftAct_rPosCoreInFull_τ_σ :
    (selLiftAct rPosCoreInFull).embedUnitary τ_pos = uBarrelFastAct ∧
    (selLiftAct rPosCoreInFull).embedUnitary σ_0_pos = uSlot0MeasSwap := by
  have hτ : (selLiftAct rPosCoreInFull).embedUnitary τ_pos = uBarrelFastAct := by
    dsimp only [τ_pos, uBarrelFastAct]
    rw [← QRegister.embedUnitary_compose]
    have hRegEq : (selLiftAct rPosCoreInFull).compose ((selDataInAct posCoreWires).compose
      selCore80InPos) =
        (selDataInAct kFull80).compose rCoreFull := by
      apply qreg_ext; intro i
      dsimp only [selLiftAct, rPosCoreInFull]
      rw [QRegister.compose_apply, QRegister.compose_apply, selDataInAct_apply,
        QRegister.concat_apply_left]
      change selDataInAct kFull80 (rCoreFull (selPosCoreInCore80 (selCore80InPos i))) =
        selDataInAct kFull80 (rCoreFull i)
      congr 2; apply Fin.ext
      simp [selPosCoreInCore80, selCore80InPos]
    rw [hRegEq]
  have hσ : (selLiftAct rPosCoreInFull).embedUnitary σ_0_pos = uSlot0MeasSwap := by
    dsimp only [σ_0_pos, uSlot0MeasSwap, L_slot0, uLensSwap]
    rw [embedUnitary_permutationUnitary_eq]
    apply congrArg Operator.permutationUnitary
    apply Equiv.ext; intro z
    apply eq_of_basisBits_eq; intro w
    have hSlot0Full : rPosCoreInFull.compose rSlot0Pos = rSlot0InFull := by
      dsimp only [rPosCoreInFull, rSlot0InFull]
      rw [QRegister.compose_assoc]
      apply congrArg (rCoreFull.compose ·)
      apply qreg_ext; intro q; apply Fin.ext
      simp [selPosCoreInCore80, rSlot0Pos, rElecSlot, rSlot0InCore, rFullSysElecSlot_val]
    revert w
    refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_)
    · rw [← selDataInAct_apply i]
      by_cases hiPos : i ∈ Set.range rPosCoreInFull.wires
      · obtain ⟨ip, rfl⟩ := hiPos
        have hLiftD : selLiftAct rPosCoreInFull (selDataInAct posCoreWires ip) =
            selDataInAct kFull80 (rPosCoreInFull ip) := by
          dsimp only [selLiftAct]
          rw [selDataInAct_apply, QRegister.concat_apply_left]; rfl
        rw [← hLiftD, BoothOpt_Anchor218CachedTrueSwapOuter.liftRegPerm_apply,
            QRegister.basisBits_replaceIndex_apply]
        by_cases hip0 : ip ∈ Set.range rSlot0Pos.wires
        · obtain ⟨q', rfl⟩ := hip0
          have hrS0 : rPosCoreInFull (rSlot0Pos q') = rSlot0InFull q' :=
            congrArg (fun r ↦ r q') hSlot0Full
          rw [basisBits_lensSwapEquiv_L_slot0Of_data_slot0 rSlot0Pos _ q',
              QRegister.basisBits_extractIndex, hLiftD, hrS0,
              basisBits_lensSwapEquiv_L_slot0Of_data_slot0 rSlot0InFull z q']
          apply congrArg (basisBits (kFull80 + 18) z)
          dsimp only [selLiftAct]
          rw [selMeasInAct_apply, QRegister.concat_apply_right]
        · have hnotFull : rPosCoreInFull ip ∉ Set.range rSlot0InFull.wires := by
            rintro ⟨q', hq'⟩
            rw [← hSlot0Full] at hq'
            exact hip0 ⟨q', rPosCoreInFull.wires.injective hq'⟩
          rw [basisBits_lensSwapEquiv_L_slot0Of_data_of_not_mem rSlot0Pos _ hip0,
              QRegister.basisBits_extractIndex, hLiftD,
              basisBits_lensSwapEquiv_L_slot0Of_data_of_not_mem rSlot0InFull z hnotFull]
      · have hnotLift : selDataInAct kFull80 i ∉ Set.range (selLiftAct rPosCoreInFull).wires := by
          rintro ⟨u, hu⟩
          revert u; refine Fin.addCases (fun ip hu ↦ ?_) (fun q' hu ↦ ?_)
          · dsimp only [selLiftAct] at hu
            rw [QRegister.concat_apply_left] at hu
            exact hiPos ⟨ip, (selDataInAct kFull80).wires.injective hu⟩
          · dsimp only [selLiftAct] at hu
            rw [QRegister.concat_apply_right] at hu
            exact (selDataInAct_disj_selMeasInAct kFull80).ne i q' hu.symm
        have hnotS0 : i ∉ Set.range rSlot0InFull.wires := by
          rintro ⟨q', hq'⟩
          rw [← hSlot0Full] at hq'
          exact hiPos ⟨rSlot0Pos q', hq'⟩
        rw [BoothOpt_Anchor218CachedTrueSwapOuter.liftRegPerm_apply,
            QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotLift,
            basisBits_lensSwapEquiv_L_slot0Of_data_of_not_mem rSlot0InFull z hnotS0]
    · rw [← selMeasInAct_apply q]
      have hLiftM : selLiftAct rPosCoreInFull (selMeasInAct posCoreWires q) =
        selMeasInAct kFull80 q := by
        dsimp only [selLiftAct]
        rw [selMeasInAct_apply, QRegister.concat_apply_right]
      have hrS0 : rPosCoreInFull (rSlot0Pos q) = rSlot0InFull q :=
        congrArg (fun r ↦ r q) hSlot0Full
      rw [← hLiftM, BoothOpt_Anchor218CachedTrueSwapOuter.liftRegPerm_apply,
          QRegister.basisBits_replaceIndex_apply,
          basisBits_lensSwapEquiv_L_slot0Of_meas rSlot0Pos _ q,
          QRegister.basisBits_extractIndex, hLiftM,
          basisBits_lensSwapEquiv_L_slot0Of_meas rSlot0InFull z q, ← hrS0]
      apply congrArg (basisBits (kFull80 + 18) z)
      dsimp only [selLiftAct]
      rw [selDataInAct_apply, QRegister.concat_apply_left]; rfl
  exact ⟨hτ, hσ⟩

open Classical in
/-- Embedding `uHeadAnchorConjH` via `selLiftAct rPosCoreInFull` into `kFull80 + 18` yields
`uAnchorFrame (rPosCoreInFull.embedUnitary uHeadConjHCore)`. -/
theorem selLiftAct_embedUnitary_uHeadAnchorConjH_eq : (selLiftAct rPosCoreInFull).embedUnitary
    uHeadAnchorConjH = uAnchorFrame (rPosCoreInFull.embedUnitary uHeadConjHCore) := by
  obtain ⟨hτ, hσ⟩ := selLiftAct_rPosCoreInFull_τ_σ
  have hD : (selLiftAct rPosCoreInFull).embedUnitary ((selDataInAct posCoreWires).embedUnitary
    uHeadConjHCore) =
      (selDataInAct kFull80).embedUnitary (rPosCoreInFull.embedUnitary uHeadConjHCore) := by
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
    exact congrArg (fun r ↦ r.embedUnitary uHeadConjHCore) (concat_compose_selDataInAct _ _ _)
  rw [uHeadAnchorConjH_eq_anchorConj]
  simp only [QRegister.embedUnitary_mul, hτ, hσ, hD]
  rfl
attribute [irreducible] dHeadAnchorConjH172
end Part3_MaskedOrigin0AnchorHead
section Part4_AnchorStageA48062
set_option exponentiation.threshold 8192
open CanonRank7Circuit
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_concat_left
  disjointWires_compose_of_disjoint)
open DyadicQft64WalkCircuit (disjoint_block_sep)
open ButterflyBarrelSlot0Conj (spectatorElecReg)
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open NuclearTwistRealizes (slot2AxisSum)
open TwistStreamEliminationAux (spectatorSum217)
open ZeroHypStageABToUFoldedPass123SegAndCompac (rElec0InCoreSum42)
open InterWalkRSum42Hoist (kFull80 rCoreFull rSum0 qreg_ext qreg_block_apply)
open Leaf4Ext48TopStitch (disj_of_val_ne rCoreFull_disj_rSum0 rCoreFull_val_eq rPGIdle
  rPGIdle_val_eq hSum0_disj_PGIdle)
open DoubleDutyFoldedRealizesBridge (selPosCoreInCore80 rPG7Full rPG7Full_val_eq
  hCoreFull_disj_rPG7Full rSum0_disj_rPG7Full)
open StageAPointPhase128OnStep (rCoreInCoreSum42)
open FullConcrete7StepAndTrueSwapSelect (kCoreSum42PG7)
open BoothOpt_06_Stream217ZeroSave0Width128 (selSpec217InCoreSum14)
@[simp]
theorem qreg_block_wires_apply_part4 {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n)
    (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
@[simp] theorem qreg_slice_wires_apply_part4 {m n : ℕ} (r : QRegister m n)
    (offset width : ℕ) (h : offset + width ≤ m) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem spectatorElecReg_disj_rZLoc80 :
    (spectatorElecReg (rCoreInCoreSum42 80)).DisjointWires (rZLoc (fullSysCoreWires 80) 42) :=
  disj_of_val_ne fun i j ↦ by
    have := fullSysCoreWires80_eq_4034_assoc; have := i.isLt
    simp only [spectatorElecReg, rCoreInCoreSum42, rZLoc,
      QRegister.slice_apply, QRegister.block_apply_val]; omega
def rSpecSumInCS80 : QRegister (3906 + 42) (fullSysCoreWires 80 + 42) :=
  (spectatorElecReg (rCoreInCoreSum42 80)).concat (rZLoc (fullSysCoreWires 80) 42)
    spectatorElecReg_disj_rZLoc80
def selSpecSum14In3948 (w : Fin 3) : QRegister (3906 + 14) (3906 + 42) :=
    (QRegister.block 0 3906 (by omega)).concat ((QRegister.block 3906 42 (by omega)).compose
    (BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42 w))
    ((disjoint_block_sep (Or.inl (by omega))).compose_right _)
theorem rSpecSumInCS80_compose_selSpecSum14In3948 (w : Fin 3) :
    rSpecSumInCS80.compose (selSpecSum14In3948 w) =
      (BoothOpt_06_Stream217ZeroSave0Width128.selCoreSum14In42 80 w).compose
        (selSpec217InCoreSum14 80) := by
  apply qreg_ext; intro idx
  obtain ⟨hvSpec, hvSum⟩ := selCoreSum14_compose_selSpec217_val_assoc w
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · rw [QRegister.compose_apply rSpecSumInCS80, selSpecSum14In3948, QRegister.concat_apply_left,
        QRegister.compose_apply]
    apply Fin.ext
    rw [hvSpec i]
    have hi0 : (QRegister.block 0 3906 (by omega) : QRegister 3906 (3906 + 42)) i =
        Fin.castAdd 42 i := Fin.ext (by
          simp only [QRegister.block_apply_val, Fin.val_castAdd, zero_add])
    rw [hi0, rSpecSumInCS80, QRegister.concat_apply_left]
    simp only [spectatorElecReg, rCoreInCoreSum42, QRegister.slice_apply, QRegister.block_apply_val,
      zero_add]
  · rw [QRegister.compose_apply rSpecSumInCS80, selSpecSum14In3948, QRegister.concat_apply_right,
        QRegister.compose_apply
          (BoothOpt_06_Stream217ZeroSave0Width128.selCoreSum14In42 80 w)]
    apply Fin.ext
    rw [hvSum j]
    have hj0 : ((QRegister.block 3906 42 (by omega)).compose
          (BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42 w)) j =
        Fin.natAdd 3906 (BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42 w j) :=
      Fin.ext (by simp only [QRegister.compose_apply, QRegister.block_apply_val, Fin.val_natAdd])
    rw [hj0, rSpecSumInCS80, QRegister.concat_apply_right]
    simp only [rZLoc, BoothOpt_06_Stream217ZeroSave0Width128.rSum14Slice42,
      QRegister.block_apply_val]
theorem rSpecSumInCS80_compose_block3906 : rSpecSumInCS80.compose
    (QRegister.block 3906 42 (by omega)) = rZLoc (fullSysCoreWires 80) 42 := by
  apply qreg_ext; intro j
  rw [QRegister.compose_apply]
  have hj : (QRegister.block 3906 42 (by omega) : QRegister 42 (3906 + 42)) j =
      Fin.natAdd 3906 j := Fin.ext (by simp only [QRegister.block_apply_val, Fin.val_natAdd])
  rw [hj, rSpecSumInCS80, QRegister.concat_apply_right]
open Classical in
theorem basisOutcomeProjector_zero_mulVec_basisKet_gen {n m : ℕ} (r : QRegister m n)
    (β : BitAssignment n) : (r.basisOutcomeProjector 0).mulVec (basisKet β) = if
    r.extractIndex ((basisBitsEquiv n).symm β) = 0 then basisKet β else 0 := by
  let y := (basisBitsEquiv n).symm β
  rw [QRegister.basisOutcomeProjector_eq_diagonal, basisKet_eq_single_symm_assoc β,
    Matrix.diagonal_mulVec_single]
  by_cases h0 : r.extractIndex y = 0
  · rw [ite_eq_left h0, ite_eq_left h0, one_mul]
  · rw [ite_eq_right h0, ite_eq_right h0, zero_mul, Pi.single_zero]
theorem slot2AxisSum_eq_spectatorSum217_of_elec0_zero
    (γ : BitAssignment (fullSysCoreWires 80))
    (haZero : ∀ q : Fin 18,
      γ ⟨q.val, by have := fullSysCoreWires80_eq_4034_assoc; have := q.isLt; omega⟩ = 0) :
    (fun w ↦ slot2AxisSum w γ) = (fun w ↦ spectatorSum217 w γ) := by
  funext w
  rw [TwistStreamEliminationAux.slot2AxisSum_eq_anchor_add_spectatorSum217]
  have h0val : regVal (rElecSlotAxis (QRegExt.idReg (fullSysCoreWires 80)) 0 w) γ = 0 := by
    unfold regVal bitsVal
    refine Finset.sum_eq_zero fun r _ ↦ ?_
    have hr : γ (rElecSlotAxis (QRegExt.idReg (fullSysCoreWires 80)) 0 w r) = 0 := by
      have hidx : rElecSlotAxis (QRegExt.idReg (fullSysCoreWires 80)) 0 w r =
          ⟨6 * w.val + r.val, by
            have := fullSysCoreWires80_eq_4034_assoc; have := w.isLt; have := r.isLt; omega⟩ :=
        Fin.ext (by simp [rElecSlotAxis, QRegExt.idReg])
      rw [hidx]
      exact haZero ⟨6 * w.val + r.val, by have := w.isLt; have := r.isLt; omega⟩
    dsimp only; rw [hr]; simp
  rw [h0val, zero_add]
open Classical in
theorem eStream218Core_mul_elec0Zero_eq_eStream217Core :
    eStream218Core * (rElec0InCoreSum42 80).basisOutcomeProjector 0 =
      eStream217Core * (rElec0InCoreSum42 80).basisOutcomeProjector 0 := by
  let kC := fullSysCoreWires 80
  apply matrix_ext_ket; intro β
  rw [ket_eq_basisKet, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      basisOutcomeProjector_zero_mulVec_basisKet_gen]
  let y := (basisBitsEquiv (kC + 42)).symm β
  by_cases he0 : (rElec0InCoreSum42 80).extractIndex y = 0
  · rw [ite_eq_left he0, eStream218Core, eStream217Core, eStream42CoreOf_mulVec_basisKet,
        eStream42CoreOf_mulVec_basisKet]
    dsimp only
    by_cases hz : (rZLoc kC 42).extractIndex y = 0
    · rw [ite_eq_left hz, ite_eq_left hz]
      have haZero : ∀ q : Fin 18,
          basisBits kC ((rActLoc kC 42).extractIndex y)
            ⟨q.val, by have := fullSysCoreWires80_eq_4034_assoc; have := q.isLt; omega⟩ = 0 := by
        have hbits := ((QRegExt.extractIndex_eq_zero_iff (rElec0InCoreSum42 80)) y).mp he0
        intro q
        rw [QRegister.basisBits_extractIndex]
        have hq : (rActLoc kC 42)
            ⟨q.val, by have := fullSysCoreWires80_eq_4034_assoc; have := q.isLt; omega⟩ =
            rElec0InCoreSum42 80 q :=
          Fin.ext (by simp [rActLoc, rElec0InCoreSum42])
        rw [hq]; exact hbits q
      exact congrArg (fun F ↦ basisKet (basisBits (kC + 42)
        (StageAConjHAndStreamBridge.joinAZ
          ((rActLoc kC 42).extractIndex y)
          (InterWalkRSum42Hoist.streamTarget42 F))))
        (slot2AxisSum_eq_spectatorSum217_of_elec0_zero _ haZero)
    · rw [ite_eq_right hz, ite_eq_right hz]
  · rw [ite_eq_right he0, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem disj_concat_right_part4 {a b c n : ℕ} {rA : QRegister a n} {rB : QRegister b n}
    {rC : QRegister c n} (hBC : rB.DisjointWires rC) (hAB : rA.DisjointWires rB)
    (hAC : rA.DisjointWires rC) : rA.DisjointWires (rB.concat rC hBC) :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hBC (QRegExt.disjointWires_symm hAB)
      (QRegExt.disjointWires_symm hAC)))
theorem rCoreFull_disj_rPGIdle11 : rCoreFull.DisjointWires (rPGIdle 11 (by decide)) :=
  disj_of_val_ne fun i j ↦ by
    rw [rCoreFull_val_eq, rPGIdle_val_eq]
    have := i.isLt; have := fullSysCoreWires80_eq_4034_assoc; omega
theorem rPG7Full_disj_rPGIdle11 : rPG7Full.DisjointWires (rPGIdle 11 (by decide)) :=
  disj_of_val_ne fun m j ↦ by
    rw [rPG7Full_val_eq, rPGIdle_val_eq]; have := j.isLt; omega
theorem rActStageAFull80_disj_rPGIdle11 : rActStageAFull80.DisjointWires
    (rPGIdle 11 (by decide)) := disjointWires_concat_left _ (disjointWires_concat_left _
    rCoreFull_disj_rPGIdle11 (hSum0_disj_PGIdle 11 (by decide))) rPG7Full_disj_rPGIdle11
theorem rSlot0InFull_disj_rPGIdle11 : rSlot0InFull.DisjointWires (rPGIdle 11 (by decide)) :=
  rCoreFull_disj_rPGIdle11.compose_left rSlot0InCore
/-- Ambient `(rAct ++ rAnchor18)` selector inside `(kFull80 + 18) + 18`. -/
abbrev selAAZ_AA : QRegister (kFull80 + 18) ((kFull80 + 18) + 18) :=
  selDataInAct (kFull80 + 18)
/-- Ambient held-`Z18` selector inside `(kFull80 + 18) + 18`. -/
abbrev selAAZ_Z : QRegister 18 ((kFull80 + 18) + 18) := selMeasInAct (kFull80 + 18)
/-- Ambient `kFull80` data selector inside `(kFull80 + 18) + 18`. -/
abbrev selAAZ_Data : QRegister kFull80 ((kFull80 + 18) + 18) :=
  selAAZ_AA.compose (selDataInAct kFull80)
abbrev selAAZ_Anc : QRegister 18 ((kFull80 + 18) + 18) :=
  selAAZ_AA.compose (selMeasInAct kFull80)
noncomputable def selAAZ_Subst : QRegister kFull80 ((kFull80 + 18) + 18) :=
  selAAZ_AA.compose (selSubstSlot0 rSlot0InFull)
theorem selAAZ_Data_disj_Z : selAAZ_Data.DisjointWires selAAZ_Z :=
  (selDataInAct_disj_selMeasInAct (kFull80 + 18)).compose_left (selDataInAct kFull80)
theorem selAAZ_Anc_disj_Data : selAAZ_Anc.DisjointWires selAAZ_Data :=
  disjointWires_compose_of_disjoint selAAZ_AA (QRegExt.disjointWires_symm
    (selDataInAct_disj_selMeasInAct kFull80))
theorem selAAZ_Anc_disj_Z : selAAZ_Anc.DisjointWires selAAZ_Z :=
  (selDataInAct_disj_selMeasInAct (kFull80 + 18)).compose_left (selMeasInAct kFull80)
theorem selAAZ_Subst_disj_Z : selAAZ_Subst.DisjointWires selAAZ_Z :=
  (selDataInAct_disj_selMeasInAct (kFull80 + 18)).compose_left (selSubstSlot0 rSlot0InFull)
def selAAZ_HeldAct : QRegister kHeldZ18Act ((kFull80 + 18) + 18) :=
  let rCS := selAAZ_Data.compose rCSFull80
  let rPG7 := selAAZ_Data.compose rPG7Full
  let hCS_Z : rCS.DisjointWires selAAZ_Z := selAAZ_Data_disj_Z.compose_left rCSFull80
  let hCS_PG : rCS.DisjointWires rPG7 :=
    disjointWires_compose_of_disjoint selAAZ_Data hCSFull80_disj_rPG7Full
  let hPG_Z : rPG7.DisjointWires selAAZ_Z := selAAZ_Data_disj_Z.compose_left rPG7Full
  (rCS.concat selAAZ_Z hCS_Z).concat rPG7 (disjointWires_concat_left hCS_Z hCS_PG
    (QRegExt.disjointWires_symm hPG_Z))
/-- Active Stage-A plus held-`Z18` selector inside `(kFull80 + 18) + 18`. -/
def selAAZ_ActStageAZ : QRegister (kCoreSum42PG7 + 18) ((kFull80 + 18) + 18) :=
  (selAAZ_Data.compose rActStageAFull80).concat selAAZ_Z
    (selAAZ_Data_disj_Z.compose_left rActStageAFull80)
theorem selAAZ_ActStageAZ_compositions : selAAZ_ActStageAZ.compose selHeldZ18ActInFull =
    selAAZ_HeldAct ∧ selAAZ_ActStageAZ.compose selCoreSum42InFull = selAAZ_Data.compose
    rCSFull80 ∧ selAAZ_ActStageAZ.compose selPosCoreInFull = selAAZ_Data.compose
    rPosCoreInFull ∧ selAAZ_ActStageAZ.compose selPosCoreZ18InFull =
    (selAAZ_Data.compose rPosCoreInFull).concat selAAZ_Z
    (selAAZ_Data_disj_Z.compose_left rPosCoreInFull) := by
  let rCore := selAAZ_Data.compose rCoreFull
  let rSum42 := selAAZ_Data.compose rSum0
  let rPG7 := selAAZ_Data.compose rPG7Full
  have hCSum42 := disjointWires_compose_of_disjoint selAAZ_Data rCoreFull_disj_rSum0
  have hCPG := disjointWires_compose_of_disjoint selAAZ_Data hCoreFull_disj_rPG7Full
  have hSPG := disjointWires_compose_of_disjoint selAAZ_Data rSum0_disj_rPG7Full
  have hCZ := selAAZ_Data_disj_Z.compose_left rCoreFull
  have hSZ := selAAZ_Data_disj_Z.compose_left rSum0
  have hPGZ := selAAZ_Data_disj_Z.compose_left rPG7Full
  have hActEq : (((rCore.concat rSum42 hCSum42).concat rPG7 (disjointWires_concat_left hCSum42
      hCPG hSPG)).concat selAAZ_Z (disjointWires_concat_left _ (disjointWires_concat_left
      hCSum42 hCZ hSZ) hPGZ)) = selAAZ_ActStageAZ := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun iAct ↦ ?_) (fun jZ ↦ ?_) idx
    · dsimp only [selAAZ_ActStageAZ]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
      refine Fin.addCases (fun iCS ↦ ?_) (fun mPG ↦ ?_) iAct
      · rw [QRegister.concat_apply_left]
        refine Fin.addCases (fun iC ↦ ?_) (fun jS ↦ ?_) iCS
        · simp [rCore, rActStageAFull80, rCSFull80, QRegister.concat_apply_left]
        · simp [rSum42, rActStageAFull80, rCSFull80, QRegister.concat_apply_left,
            QRegister.concat_apply_right]
      · simp [rPG7, rActStageAFull80, QRegister.concat_apply_right]
    · dsimp only [selAAZ_ActStageAZ]
      rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
  obtain ⟨hP, hCS, hPZ⟩ := concat_compose_stageAFull_selectors rCore rSum42 rPG7 selAAZ_Z
    hCSum42 hCPG hSPG hCZ hSZ hPGZ
  have hHeld := concat_compose_selHeldZ18ActInFull (rCore.concat rSum42 hCSum42) rPG7 selAAZ_Z
    (disjointWires_concat_left hCSum42 hCPG hSPG)
    (disjointWires_concat_left hCSum42 hCZ hSZ) hPGZ
  rw [hActEq] at hP hCS hPZ hHeld
  have hCSEq : rCore.concat rSum42 hCSum42 = selAAZ_Data.compose rCSFull80 := by
    apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simp [rCore, rCSFull80, QRegister.concat_apply_left]
    · simp [rSum42, rCSFull80, QRegister.concat_apply_right]
  have hPosEq : rCore.compose selPosCoreInCore80 = selAAZ_Data.compose rPosCoreInFull := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hHeld]; apply qreg_ext; intro idx
    refine Fin.addCases (fun iCZ ↦ ?_) (fun mPG ↦ ?_) idx
    · refine Fin.addCases (fun iCS ↦ ?_) (fun jZ ↦ ?_) iCZ
      · dsimp only [selAAZ_HeldAct]
        rw [QRegister.concat_apply_left, QRegister.concat_apply_left,
            QRegister.concat_apply_left, QRegister.concat_apply_left, hCSEq]
      · dsimp only [selAAZ_HeldAct]
        rw [QRegister.concat_apply_left, QRegister.concat_apply_right,
            QRegister.concat_apply_left, QRegister.concat_apply_right]
    · dsimp only [selAAZ_HeldAct, rPG7]
      rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
  · rw [hCS, hCSEq]
  · rw [hP, hPosEq]
  · rw [hPZ]; apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left, QRegister.concat_apply_left]; rfl
    · rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
end Part4_AnchorStageA48062
end StageADeconstrAndQftShare
end SharedScope
end
end GhostAndMaskedAnchorHead

noncomputable section StageAAAZUnitaryEquiv

section
set_option maxRecDepth 131072
set_option exponentiation.threshold 1024
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroK7 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
open Circuit hiding TOFF
open scoped Matrix BigOperators
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  concat_compose_selDataInAct concat_compose_selMeasInAct selDataInAct_disj_selMeasInAct)
namespace StageADeconstrAndQftShare
open LocalClassicalPerm SpecsAux
open SpecsAux.SpecMirror OctahedralOrbit PosSlots24BranchConcrete
open PosSlots24CompactHead123 PosHeadMod4_15476
open StageAConjHAndStreamBridge
open BoothOpt_Anchor218CachedTrueSwapOuter
open scoped ComplexOrder MatrixOrder Circuit.Notation
open QRegExt
section Part4_AnchorStageA48062
set_option exponentiation.threshold 8192
open CanonRank7Circuit
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open Barrel3PassSelectStitch (rCoreSeg)
open ElecHadTrueSwapLocalCompClosure (lensSwapEquiv extractPair)
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_concat_left
  disjointWires_compose_of_disjoint iSlot1 iSlot2)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (SameOutside embedMatrix_apply_sameOutside
  rFullSysElecSlot rFullSysElecSlot_val)
open ButterflyBarrelSlot0Conj (spectatorElecReg ActsAsIdOnSpectatorWires PreservesHigh3924On)
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open StageAPosHeadConjugatedCircuit (uHadamard18 uHad217)
open NuclearTwistRealizes (slot2AxisSum)
open TwistStreamEliminationAux (spectatorSum217)
open ZeroHypStageABToUFoldedPass123SegAndCompac (rElec0InCoreSum42)
open InterWalkRSum42Hoist (kFull80 rCoreFull rSegFull rSum0 E_rawStream42 pSum42Zero qreg_ext
  qreg_block_apply)
open PosMomSelectSandwich (slotBitProj)
open PosPostPrep80MergedVep (uSwapCore3967 wCore3967 wCore4029 swapCore3967Fn
  uSwapCore3967_mulVec_ket uSwapCore3967_comm_slotBitProj uSwapCore3967_mul_self)
open CoinDispatchedBarrel288 (uBarrelFast coinBarrelBitFnFast coinBarrelIdxFast swapElec0Bits
  swapElec0Bits_high swapElec0Bits_self uBarrelFast_mulVec_ket uBarrelFast_comm_high_wire)
open Leaf4Ext48TopStitch (CommutesWithReg disj_of_val_ne rCoreFull_disj_rSum0 rPGIdle
  hSum0_disj_PGIdle pPGIdleZero)
open DoubleDutyFoldedRealizesBridge (selPosCoreInCore80 rPG7Full)
open ZeroHypSlot0CommAndHMidClosure (basisOutcomeProjector_zero_mul_self)
open ForestQft117BundleNoTopBridge (pStream42Of pStream217Core pStream218Core)
open MasterZeroHypCompactAndCompactTopBridge (sel25InCat)
open ElecHadTrueSwapLocalCompClosure (uLensSwap)
open StageAPointPhase128OnStep (rCoreInCoreSum42 rSum14InCoreSum42)
open Slot0SubAdd14And217Stream (uSlot0Sum42Add)
open FullConcrete7StepAndTrueSwapSelect (selCoreSum42InAct selCatInCoreSum42PG7)
open BoothOpt_06_Stream217ZeroSave0Width128 (uStream217Spec131 selSpec217InCoreSum14)
open CoinBarrelPureCnotLoad (uBarrelFast_comm_E_rawStream42)
/-- `217`-spectator raw stream partial isometry embedded on `rCSFull80` inside `kFull80`. -/
noncomputable def E_raw217 : Operator (2 ^ kFull80) := rCSFull80.embedMatrix eStream217Core
theorem rCSFull80_embedMatrix_eStream218Core : rCSFull80.embedMatrix eStream218Core =
    E_rawStream42 := rCSFull_embedMatrix_eStream218Core_eq_E_rawStream42
theorem inv_uSlot0Sum42Add_mul_eStream218Core :
    ((uSlot0Sum42Add 80)⁻¹).1 * eStream218Core = eStream217Core := by
  calc ((uSlot0Sum42Add 80)⁻¹).1 * eStream218Core
      = ((uSlot0Sum42Add 80)⁻¹).1 * ((uSlot0Sum42Add 80).1 * eStream217Core) := by
          rw [← uSlot0Sum42Add_mul_eStream217Core]
    _ = (((uSlot0Sum42Add 80)⁻¹ * uSlot0Sum42Add 80).1) * eStream217Core := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = eStream217Core := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
open Classical in
theorem uSlot0Sum42Full_inv_mul_E_rawStream42 :
    let UAdd := rActStageAFull80.embedUnitary (selCoreSum42InAct.embedUnitary (uSlot0Sum42Add 80))
    (UAdd⁻¹).1 * E_rawStream42 = E_raw217 ∧ UAdd.1 * E_raw217 = E_rawStream42 := by
  intro UAdd
  have hCSComp : rActStageAFull80.compose selCoreSum42InAct = rCSFull80 := by
    apply qreg_ext; intro i
    have hi : selCoreSum42InAct i = Fin.castAdd 7 i :=
      Fin.ext (by simp [selCoreSum42InAct])
    rw [QRegister.compose_apply, hi]; dsimp only [rActStageAFull80];
      rw [QRegister.concat_apply_left]
  have hUAdd : UAdd = rCSFull80.embedUnitary (uSlot0Sum42Add 80) := by
    dsimp only [UAdd]; rw [← QRegister.embedUnitary_compose, hCSComp]
  rw [hUAdd, ← QRegister.embedUnitary_inv, ← rCSFull80_embedMatrix_eStream218Core]
  unfold E_raw217
  refine ⟨?_, ?_⟩
  · rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
      inv_uSlot0Sum42Add_mul_eStream218Core]
  · rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, uSlot0Sum42Add_mul_eStream217Core]
open Classical in
theorem uExpQft0Full_comm_E_raw217 :
    let UQ0 := rActStageAFull80.embedUnitary
      (selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat)
    UQ0.1 * E_raw217 = E_raw217 * UQ0.1 := by
  intro UQ0
  have hDisj : ((rActStageAFull80.compose selCatInCoreSum42PG7).compose sel25InCat).DisjointWires
      (rCSFull80.compose rSpecSumInCS80) := by
    have hCSComp : rCSFull80 = rActStageAFull80.compose selCoreSum42InAct := by
      apply qreg_ext; intro i
      have hi : selCoreSum42InAct i = Fin.castAdd 7 i :=
        Fin.ext (by simp [selCoreSum42InAct])
      rw [QRegister.compose_apply, hi]; dsimp only [rActStageAFull80];
        rw [QRegister.concat_apply_left]
    rw [hCSComp, QRegister.compose_assoc rActStageAFull80, QRegister.compose_assoc rActStageAFull80]
    refine disjointWires_compose_of_disjoint rActStageAFull80 ?_
    rw [QRegister.disjoint_iff]; intro idx t hEq
    have hv := congrArg Fin.val hEq
    change (selCatInCoreSum42PG7 (sel25InCat idx)).val =
      (selCoreSum42InAct (rSpecSumInCS80 t)).val at hv
    have hSpecVal : 18 ≤ (selCoreSum42InAct (rSpecSumInCS80 t)).val ∧
        (selCoreSum42InAct (rSpecSumInCS80 t)).val < fullSysCoreWires 80 + 42 := by
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) t
      · have ht : rSpecSumInCS80 (Fin.castAdd 42 i) =
            spectatorElecReg (rCoreInCoreSum42 80) i := QRegister.concat_apply_left _ _ _ i
        rw [ht]
        have := fullSysCoreWires80_eq_4034_assoc; have := i.isLt
        simp only [selCoreSum42InAct, spectatorElecReg, rCoreInCoreSum42,
          QRegister.slice_apply, QRegister.block_apply_val]; omega
      · have ht : rSpecSumInCS80 (Fin.natAdd 3906 j) =
            rZLoc (fullSysCoreWires 80) 42 j := QRegister.concat_apply_right _ _ _ j
        rw [ht]
        have := fullSysCoreWires80_eq_4034_assoc; have := j.isLt
        simp only [selCoreSum42InAct, rZLoc, QRegister.block_apply_val]; omega
    rcases selCatInCoreSum42PG7_sel25InCat_val_lt18_or_ge4076 idx with hlt | hge <;> omega
  have hUQ0 : UQ0 = (rActStageAFull80.compose selCatInCoreSum42PG7).embedUnitary
      activeOneElecExpQftStage128.uCat := by
    dsimp only [UQ0]; rw [QRegister.embedUnitary_compose]
  rw [hUQ0]
  have hCommSpecSum := supportedOnSel25_activeOneElecExpQftStage128.comm_of_disj hDisj
  have hStrComm : ∀ w : Fin 3,
      let rAx : QRegister (3906 + 14) kFull80 := rCSFull80.compose
          ((BoothOpt_06_Stream217ZeroSave0Width128.selCoreSum14In42
          80 w).compose (selSpec217InCoreSum14 80))
      ((rActStageAFull80.compose selCatInCoreSum42PG7).embedUnitary
        activeOneElecExpQftStage128.uCat).1 *
        (rAx.embedUnitary (uStream217Spec131 w)).1 =
      (rAx.embedUnitary (uStream217Spec131 w)).1 *
        ((rActStageAFull80.compose selCatInCoreSum42PG7).embedUnitary
          activeOneElecExpQftStage128.uCat).1 := by
    intro w rAx
    have hSel : (rCSFull80.compose rSpecSumInCS80).compose (selSpecSum14In3948 w) = rAx := by
      dsimp only [rAx]
      rw [QRegister.compose_assoc, rSpecSumInCS80_compose_selSpecSum14In3948 w]
    rw [← hSel, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
        (rCSFull80.compose rSpecSumInCS80).embedMatrix_compose (selSpecSum14In3948 w)]
    exact hCommSpecSum ((selSpecSum14In3948 w).embedMatrix (uStream217Spec131 w).1)
  have hP0Comm : ((rActStageAFull80.compose selCatInCoreSum42PG7).embedUnitary
      activeOneElecExpQftStage128.uCat).1 * rCSFull80.embedMatrix pSum42CoreZero =
      rCSFull80.embedMatrix pSum42CoreZero * ((rActStageAFull80.compose
      selCatInCoreSum42PG7).embedUnitary activeOneElecExpQftStage128.uCat).1 := by
    have hSub : (rCSFull80.compose rSpecSumInCS80).compose (QRegister.block 3906 42 (by omega)) =
        rCSFull80.compose (rZLoc (fullSysCoreWires 80) 42) := by
      rw [QRegister.compose_assoc, rSpecSumInCS80_compose_block3906]
    rw [pSum42CoreZero, embedMatrix_basisOutcomeProjector_zero_assoc rCSFull80,
        ← hSub, ← embedMatrix_basisOutcomeProjector_zero_assoc (rCSFull80.compose rSpecSumInCS80)]
    exact hCommSpecSum _
  unfold E_raw217
  rw [← uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core, rCSFull80.embedMatrix_mul]
  have hU3 : rCSFull80.embedMatrix (uStr3AxisOfSpec uStream217Spec131).1 =
      (rCSFull80.embedUnitary (uStr3AxisOfSpec uStream217Spec131)).1 := rfl
  rw [hU3]
  unfold uStr3AxisOfSpec
  simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← QRegister.embedUnitary_compose,
    Matrix.mul_assoc]
  have h2 := hStrComm 2; have h1 := hStrComm 1; have h0 := hStrComm 0
  dsimp only at h2 h1 h0
  let A := ((rActStageAFull80.compose selCatInCoreSum42PG7).embedUnitary
    activeOneElecExpQftStage128.uCat).1
  let U := fun w : Fin 3 ↦ ((rCSFull80.compose
      ((BoothOpt_06_Stream217ZeroSave0Width128.selCoreSum14In42 80
      w).compose (selSpec217InCoreSum14 80))).embedUnitary (uStream217Spec131 w)).1
  let P0 := rCSFull80.embedMatrix pSum42CoreZero
  change A * (U 2 * (U 1 * (U 0 * P0))) = U 2 * (U 1 * (U 0 * (P0 * A)))
  calc A * (U 2 * (U 1 * (U 0 * P0)))
      = (A * U 2) * (U 1 * (U 0 * P0)) := (Matrix.mul_assoc _ _ _).symm
    _ = U 2 * (A * (U 1 * (U 0 * P0))) := by rw [h2, Matrix.mul_assoc]
    _ = U 2 * ((A * U 1) * (U 0 * P0)) := by rw [← Matrix.mul_assoc A (U 1)]
    _ = U 2 * (U 1 * (A * (U 0 * P0))) := by rw [h1, Matrix.mul_assoc (U 1)]
    _ = U 2 * (U 1 * ((A * U 0) * P0)) := by rw [← Matrix.mul_assoc A (U 0)]
    _ = U 2 * (U 1 * (U 0 * (A * P0))) := by rw [h0, Matrix.mul_assoc (U 0) A P0]
    _ = U 2 * (U 1 * (U 0 * (P0 * A))) := by rw [hP0Comm]
theorem selSubstSlot0_embedMatrix_E_raw217_eq : (selSubstSlot0 rSlot0InFull).embedMatrix
    E_raw217 = (selDataInAct kFull80).embedMatrix E_raw217 := by
  have hNotSlot0 : ∀ t : Fin (3906 + 42),
      rCSFull80 (rSpecSumInCS80 t) ∉ Set.range rSlot0InFull.wires := by
    intro t ⟨q, hq⟩
    revert hq
    refine Fin.addCases (fun i hq ↦ ?_) (fun j hq ↦ ?_) t
    · rw [rSpecSumInCS80, QRegister.concat_apply_left] at hq
      let iCore : Wire (fullSysCoreWires 80) :=
        ⟨18 + i.val, by have := fullSysCoreWires80_eq_4034_assoc; have := i.isLt; omega⟩
      have hiEq : spectatorElecReg (rCoreInCoreSum42 80) i = Fin.castAdd 42 iCore :=
        Fin.ext (by simp only [spectatorElecReg, rCoreInCoreSum42,
          QRegister.slice_apply, QRegister.block_apply_val, Fin.val_castAdd, zero_add, iCore])
      rw [hiEq] at hq
      dsimp only [rCSFull80, rSlot0InFull] at hq
      rw [QRegister.concat_apply_left] at hq
      have hv := congrArg Fin.val (rCoreFull.wires.injective hq)
      have := q.isLt
      rw [rSlot0InCore, rFullSysElecSlot_val] at hv
      simp [iCore] at hv; omega
    · rw [rSpecSumInCS80, QRegister.concat_apply_right] at hq
      have hjEq : rZLoc (fullSysCoreWires 80) 42 j = Fin.natAdd (fullSysCoreWires 80) j :=
        Fin.ext (by simp only [rZLoc, QRegister.block_apply_val, Fin.val_natAdd])
      rw [hjEq] at hq
      dsimp only [rCSFull80, rSlot0InFull] at hq
      rw [QRegister.concat_apply_right] at hq
      exact rCoreFull_disj_rSum0.ne (rSlot0InCore q) j hq
  have hCompEq : (selSubstSlot0 rSlot0InFull).compose (rCSFull80.compose rSpecSumInCS80) =
      (selDataInAct kFull80).compose (rCSFull80.compose rSpecSumInCS80) := by
    apply qreg_ext; intro t
    rw [QRegister.compose_apply, QRegister.compose_apply, selSubstSlot0,
        rDataSubstSlot0_apply_of_not_mem _ _ _ _ (hNotSlot0 t),
        QRegister.compose_apply (selDataInAct kFull80), QRegister.compose_apply rCSFull80]
  have hAxEq : ∀ w : Fin 3, ((selSubstSlot0 rSlot0InFull).compose rCSFull80).embedMatrix
      (((BoothOpt_06_Stream217ZeroSave0Width128.selCoreSum14In42 80
      w).compose (selSpec217InCoreSum14 80)).embedMatrix (uStream217Spec131 w).1) =
      ((selDataInAct kFull80).compose rCSFull80).embedMatrix
      (((BoothOpt_06_Stream217ZeroSave0Width128.selCoreSum14In42 80
      w).compose (selSpec217InCoreSum14 80)).embedMatrix (uStream217Spec131 w).1) := by
    intro w
    have hCompSel :
        ((selSubstSlot0 rSlot0InFull).compose rCSFull80).compose (rSpecSumInCS80.compose
          (selSpecSum14In3948 w)) =
        ((selDataInAct kFull80).compose rCSFull80).compose (rSpecSumInCS80.compose
          (selSpecSum14In3948 w)) := by
      calc ((selSubstSlot0 rSlot0InFull).compose rCSFull80).compose (rSpecSumInCS80.compose
        (selSpecSum14In3948 w))
          =
            ((selSubstSlot0 rSlot0InFull).compose (rCSFull80.compose rSpecSumInCS80)).compose
            (selSpecSum14In3948 w) := by
              apply qreg_ext; intro; rfl
        _ =
          ((selDataInAct kFull80).compose (rCSFull80.compose rSpecSumInCS80)).compose
          (selSpecSum14In3948 w) := by
              rw [hCompEq]
        _ =
          ((selDataInAct kFull80).compose rCSFull80).compose (rSpecSumInCS80.compose
          (selSpecSum14In3948 w)) := by
              apply qreg_ext; intro; rfl
    rw[← rSpecSumInCS80_compose_selSpecSum14In3948 w,
        ← QRegister.embedMatrix_compose ((selSubstSlot0 rSlot0InFull).compose rCSFull80),
        ← QRegister.embedMatrix_compose ((selDataInAct kFull80).compose rCSFull80), hCompSel]
  have hP0Eq : ((selSubstSlot0 rSlot0InFull).compose rCSFull80).embedMatrix pSum42CoreZero =
      ((selDataInAct kFull80).compose rCSFull80).embedMatrix pSum42CoreZero := by
    rw [pSum42CoreZero, ← rSpecSumInCS80_compose_block3906,
        ← embedMatrix_basisOutcomeProjector_zero_assoc rSpecSumInCS80,
        ← QRegister.embedMatrix_compose ((selSubstSlot0 rSlot0InFull).compose rCSFull80),
        ← QRegister.embedMatrix_compose ((selDataInAct kFull80).compose rCSFull80),
        QRegister.compose_assoc (selSubstSlot0 rSlot0InFull) rCSFull80 rSpecSumInCS80,
        QRegister.compose_assoc (selDataInAct kFull80) rCSFull80 rSpecSumInCS80, hCompEq]
  unfold E_raw217
  rw [← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose,
      ← uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core]
  unfold uStr3AxisOfSpec
  simp only [Submonoid.coe_mul, QRegister.embedUnitary_val, QRegister.embedMatrix_mul,
    ← QRegister.embedMatrix_compose
      (BoothOpt_06_Stream217ZeroSave0Width128.selCoreSum14In42 80 _)]
  rw [hAxEq 2, hAxEq 1, hAxEq 0, hP0Eq]
/-- **Lemma A**: Under `rSlot0InFull ↦ selMeasInAct`, `E_rawStream42` restricted to `P_anc0`
coincides with `(selDataInAct kFull80).embedMatrix E_raw217 * P_anc0`. -/
theorem selSubstSlot0_embedMatrix_E_rawStream42_mul_P_anc0 :
    (selSubstSlot0 rSlot0InFull).embedMatrix E_rawStream42 * P_anc0 =
      (selDataInAct kFull80).embedMatrix E_raw217 * P_anc0 := by
  have hPanc : P_anc0 = ((selSubstSlot0 rSlot0InFull).compose rCSFull80).embedMatrix
      ((rElec0InCoreSum42 80).basisOutcomeProjector 0) := by
    have hReg : ((selSubstSlot0 rSlot0InFull).compose rCSFull80).compose (rElec0InCoreSum42 80) =
        selMeasInAct kFull80 := by
      apply qreg_ext; intro q
      have hCS0 : rCSFull80 (rElec0InCoreSum42 80 q) = rSlot0InFull q := by
        dsimp only [rCSFull80, rSlot0InFull]
        have hq : rElec0InCoreSum42 80 q = Fin.castAdd 42 (rSlot0InCore q) :=
          Fin.ext (by
            rw [Fin.val_castAdd, rSlot0InCore, rFullSysElecSlot_val]
            simp [rElec0InCoreSum42])
        rw [hq, QRegister.concat_apply_left]; rfl
      rw [QRegister.compose_apply, QRegister.compose_apply, hCS0,
          selSubstSlot0, rDataSubstSlot0_apply_slot0]
    unfold P_anc0
    rw [embedMatrix_basisOutcomeProjector_zero_assoc, hReg]
  rw [← rCSFull80_embedMatrix_eStream218Core, ← QRegister.embedMatrix_compose]
  conv_lhs => rw [hPanc]
  rw [← QRegister.embedMatrix_mul, eStream218Core_mul_elec0Zero_eq_eStream217Core,
      QRegister.embedMatrix_mul, ← hPanc, QRegister.embedMatrix_compose,
      ← E_raw217, selSubstSlot0_embedMatrix_E_raw217_eq]
open Classical in
/-- **Lemma B**: `E_anchorLoc E_raw217` factors with `(selDataInAct kFull80).embedMatrix
  E_rawStream42`
on the left, guaranteeing the `218`-electron stream invariant throughout the anchor-frame inner
block. -/
theorem E_anchorLoc_E_raw217_eq_rawStream42_mul : E_anchorLoc E_raw217 =
    (selDataInAct kFull80).embedMatrix E_rawStream42 * (uBarrelFastAct * uSlot0MeasSwap).1 *
    P_anc0 := by
  have hS0Sq : uSlot0MeasSwap.1 * uSlot0MeasSwap.1 = 1 := by
    rw [← Submonoid.coe_mul, uSlot0MeasSwap_mul_self, OneMemClass.coe_one]
  have hBComm : uBarrelFastAct.1 * (selDataInAct kFull80).embedMatrix E_rawStream42 =
      (selDataInAct kFull80).embedMatrix E_rawStream42 * uBarrelFastAct.1 := by
    have hBFull : rCoreFull.embedUnitary (uBarrelFast (le_refl 80)) =
        rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80))) := by
      rw [← QRegister.embedUnitary_compose, SelectExtStitch.rSegFull_compose_rCoreSeg_eq]
    rw [uBarrelFastAct_eq_embedData_rCoreFull, QRegister.embedUnitary_val,
        ← (selDataInAct kFull80).embedMatrix_mul, hBFull, uBarrelFast_comm_E_rawStream42,
        ← hBFull, (selDataInAct kFull80).embedMatrix_mul]
  unfold E_anchorLoc
  rw [← selSubstSlot0_embedMatrix_E_rawStream42_mul_P_anc0,
      embedMatrix_selSubstSlot0_eq rSlot0InFull E_rawStream42]
  change (uBarrelFastAct.1 * uSlot0MeasSwap.1) *
      ((uSlot0MeasSwap.1 * (selDataInAct kFull80).embedMatrix E_rawStream42 * uSlot0MeasSwap.1) *
        P_anc0) = _
  calc (uBarrelFastAct.1 * uSlot0MeasSwap.1) *
          ((uSlot0MeasSwap.1 * (selDataInAct kFull80).embedMatrix E_rawStream42 *
            uSlot0MeasSwap.1) * P_anc0)
      = uBarrelFastAct.1 * (uSlot0MeasSwap.1 * uSlot0MeasSwap.1) *
          (selDataInAct kFull80).embedMatrix E_rawStream42 * uSlot0MeasSwap.1 * P_anc0 := by
          simp only [Matrix.mul_assoc]
    _ = (uBarrelFastAct.1 * (selDataInAct kFull80).embedMatrix E_rawStream42) *
          uSlot0MeasSwap.1 * P_anc0 := by
          rw [hS0Sq, Matrix.mul_one]
    _ = (selDataInAct kFull80).embedMatrix E_rawStream42 *
          (uBarrelFastAct * uSlot0MeasSwap).1 * P_anc0 := by
          rw [hBComm]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
theorem pStream218_mul_E_anchorLoc_E_raw217 :
    ((selDataInAct kFull80).compose rCSFull80).embedMatrix (pStream218Core 80) *
      E_anchorLoc E_raw217 = E_anchorLoc E_raw217 := by
  have hP218Raw : rCSFull80.embedMatrix (pStream218Core 80) * E_rawStream42 = E_rawStream42 := by
    rw [← rCSFull80_embedMatrix_eStream218Core, ← rCSFull80.embedMatrix_mul,
        pStream218Core_mul_eStream218Core]
  rw [E_anchorLoc_E_raw217_eq_rawStream42_mul, QRegister.embedMatrix_compose,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← (selDataInAct kFull80).embedMatrix_mul, hP218Raw]
theorem uBarrelSlot0_comm_pSum42Zero :
    (uBarrelFastAct * uSlot0MeasSwap).1 * (selDataInAct kFull80).embedMatrix pSum42Zero =
      (selDataInAct kFull80).embedMatrix pSum42Zero * (uBarrelFastAct * uSlot0MeasSwap).1 := by
  have hBarComm : uBarrelFastAct.1 * (selDataInAct kFull80).embedMatrix pSum42Zero =
      (selDataInAct kFull80).embedMatrix pSum42Zero * uBarrelFastAct.1 := by
    rw [uBarrelFastAct_eq_embedData_rCoreFull, QRegister.embedUnitary_val,
      QRegister.embedUnitary_val, pSum42Zero,
        ← (selDataInAct kFull80).embedMatrix_mul,
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreFull) rSum0
          rCoreFull_disj_rSum0 _ 0,
        (selDataInAct kFull80).embedMatrix_mul]
  have hS0Comm : uSlot0MeasSwap.1 * (selDataInAct kFull80).embedMatrix pSum42Zero =
      (selDataInAct kFull80).embedMatrix pSum42Zero * uSlot0MeasSwap.1 := by
    have hSubst : (selSubstSlot0 rSlot0InFull).embedMatrix pSum42Zero =
        (selDataInAct kFull80).embedMatrix pSum42Zero := by
      rw [pSum42Zero, embedMatrix_basisOutcomeProjector_zero_assoc,
          embedMatrix_basisOutcomeProjector_zero_assoc]
      apply congrArg (fun r : QRegister 42 (kFull80 + 18) ↦ r.basisOutcomeProjector 0)
      apply qreg_ext; intro j
      rw [QRegister.compose_apply, QRegister.compose_apply, selSubstSlot0,
          rDataSubstSlot0_apply_of_not_mem _ _ _ _
            (fun ⟨q, hq⟩ ↦ rCoreFull_disj_rSum0.ne (rSlot0InCore q) j hq)]
    have hConj : (selSubstSlot0 rSlot0InFull).embedMatrix pSum42Zero =
        uSlot0MeasSwap.1 * (selDataInAct kFull80).embedMatrix pSum42Zero * uSlot0MeasSwap.1 :=
      embedMatrix_selSubstSlot0_eq rSlot0InFull pSum42Zero
    rw [hSubst] at hConj
    have hSq : uSlot0MeasSwap.1 * uSlot0MeasSwap.1 = 1 := by
      rw [← Submonoid.coe_mul, uSlot0MeasSwap_mul_self, OneMemClass.coe_one]
    calc uSlot0MeasSwap.1 * (selDataInAct kFull80).embedMatrix pSum42Zero
        = (uSlot0MeasSwap.1 * (selDataInAct kFull80).embedMatrix pSum42Zero * uSlot0MeasSwap.1) *
            uSlot0MeasSwap.1 := by
            rw [Matrix.mul_assoc _ uSlot0MeasSwap.1 uSlot0MeasSwap.1, hSq, Matrix.mul_one]
      _ = (selDataInAct kFull80).embedMatrix pSum42Zero * uSlot0MeasSwap.1 := by
            rw [← hConj]
  rw [Submonoid.coe_mul, Matrix.mul_assoc, hS0Comm, ← Matrix.mul_assoc, hBarComm, Matrix.mul_assoc]
open Classical in
/-- Stream `S-fwd` identity: conjugating `uStr218_3Axis` by `uBarrelFastAct * uSlot0MeasSwap`
matches `uStr3AxisOfSpec uStream217Spec131` on `pSum42Zero ⊗ P_anc0`. -/
theorem conj_uStr218_eq_uStr217_on_pSum42Zero_P_anc0 :
    let F := uBarrelFastAct * uSlot0MeasSwap
    let Finv := uSlot0MeasSwap * uBarrelFastAct
    let uStr218FA := (selDataInAct kFull80).embedUnitary (rCSFull80.embedUnitary uStr218_3Axis)
    let uStr217FA := (selDataInAct kFull80).embedUnitary
      (rCSFull80.embedUnitary (uStr3AxisOfSpec uStream217Spec131))
    (Finv * uStr218FA * F).1 * ((selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0) =
      uStr217FA.1 * ((selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0) ∧
    ((Finv * uStr218FA * F)⁻¹).1 *
        ((selDataInAct kFull80).embedMatrix (rCSFull80.embedMatrix (pStream217Core 80)) * P_anc0) =
      (uStr217FA⁻¹).1 *
        ((selDataInAct kFull80).embedMatrix (rCSFull80.embedMatrix (pStream217Core 80)) * P_anc0) :=
          by
  intro F Finv uStr218FA uStr217FA
  have hP0CS : rCSFull80.embedMatrix pSum42CoreZero = pSum42Zero := by
    rw [pSum42CoreZero, pSum42Zero, embedMatrix_basisOutcomeProjector_zero_assoc]
    congr 1; apply qreg_ext; intro j
    have hj : rZLoc (fullSysCoreWires 80) 42 j = Fin.natAdd (fullSysCoreWires 80) j :=
      Fin.ext (by simp [rZLoc])
    rw [QRegister.compose_apply, hj]; dsimp only [rCSFull80]; rw [QRegister.concat_apply_right]
  have hFinvF : Finv * F = 1 := by
    dsimp only [F, Finv]
    calc (uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap)
        = uSlot0MeasSwap * (uBarrelFastAct * uBarrelFastAct) * uSlot0MeasSwap := by
          simp only [mul_assoc]
      _ = uSlot0MeasSwap * uSlot0MeasSwap := by rw [uBarrelFastAct_mul_self, mul_one]
      _ = 1 := uSlot0MeasSwap_mul_self
  have hFinvFM : Finv.1 * F.1 = 1 := by rw [← Submonoid.coe_mul, hFinvF, OneMemClass.coe_one]
  have h218P0 : uStr218FA.1 * (selDataInAct kFull80).embedMatrix pSum42Zero =
      (selDataInAct kFull80).embedMatrix E_rawStream42 := by
    dsimp only [uStr218FA]
    rw [← hP0CS, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
        ← (selDataInAct kFull80).embedMatrix_mul, ← rCSFull80.embedMatrix_mul,
        uStr218_3Axis_mul_pSum42CoreZero_eq_eStream218Core, rCSFull80_embedMatrix_eStream218Core]
  have h217P0 : uStr217FA.1 * (selDataInAct kFull80).embedMatrix pSum42Zero =
      (selDataInAct kFull80).embedMatrix E_raw217 := by
    dsimp only [uStr217FA, E_raw217]
    rw [← hP0CS, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
        ← (selDataInAct kFull80).embedMatrix_mul, ← rCSFull80.embedMatrix_mul,
        uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core]
  have hFwd : (Finv * uStr218FA * F).1 * ((selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0) =
      (selDataInAct kFull80).embedMatrix E_raw217 * P_anc0 := by
    calc (Finv * uStr218FA * F).1 * ((selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0)
        = Finv.1 * (uStr218FA.1 * (F.1 * (selDataInAct kFull80).embedMatrix pSum42Zero) * P_anc0) :=
          by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = Finv.1 * ((uStr218FA.1 * (selDataInAct kFull80).embedMatrix pSum42Zero) * F.1 * P_anc0) :=
        by
            rw [uBarrelSlot0_comm_pSum42Zero]; simp only [F, Matrix.mul_assoc]
      _ = Finv.1 * E_anchorLoc E_raw217 := by
            rw [h218P0, ← E_anchorLoc_E_raw217_eq_rawStream42_mul]
      _ = (Finv.1 * F.1) * ((selDataInAct kFull80).embedMatrix E_raw217 * P_anc0) := by
            unfold E_anchorLoc; simp only [F, Matrix.mul_assoc]
      _ = (selDataInAct kFull80).embedMatrix E_raw217 * P_anc0 := by
            rw [hFinvFM, Matrix.one_mul]
  have hFwdEq : (Finv * uStr218FA * F).1 * ((selDataInAct kFull80).embedMatrix pSum42Zero *
    P_anc0) =
      uStr217FA.1 * ((selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0) := by
    rw [hFwd, ← Matrix.mul_assoc, h217P0]
  refine ⟨hFwdEq, ?_⟩
  let cStr := Finv * uStr218FA * F
  have hcInv : (cStr⁻¹).1 * ((selDataInAct kFull80).embedMatrix E_raw217 * P_anc0) =
      (selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0 := by
    calc (cStr⁻¹).1 * ((selDataInAct kFull80).embedMatrix E_raw217 * P_anc0)
        = (cStr⁻¹).1 * (cStr.1 * ((selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0)) := by
            rw [← hFwd]
      _ = ((cStr⁻¹ * cStr).1) * ((selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0 := by
            rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  have h217Inv : (uStr217FA⁻¹).1 * ((selDataInAct kFull80).embedMatrix E_raw217 * P_anc0) =
      (selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0 := by
    calc (uStr217FA⁻¹).1 * ((selDataInAct kFull80).embedMatrix E_raw217 * P_anc0)
        = (uStr217FA⁻¹).1 * (uStr217FA.1 * ((selDataInAct kFull80).embedMatrix pSum42Zero *
          P_anc0)) := by
            rw [← Matrix.mul_assoc uStr217FA.1, h217P0]
      _ = ((uStr217FA⁻¹ * uStr217FA).1) * ((selDataInAct kFull80).embedMatrix pSum42Zero *
        P_anc0) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (selDataInAct kFull80).embedMatrix pSum42Zero * P_anc0 := by
            rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  have hP217Decomp : (selDataInAct kFull80).embedMatrix (rCSFull80.embedMatrix (pStream217Core 80))
    * P_anc0 =
      ((selDataInAct kFull80).embedMatrix E_raw217 * P_anc0) *
        ((selDataInAct kFull80).embedMatrix E_raw217)ᴴ := by
    have hCommH : P_anc0 * ((selDataInAct kFull80).embedMatrix E_raw217)ᴴ =
        ((selDataInAct kFull80).embedMatrix E_raw217)ᴴ * P_anc0 := by
      rw [← QRegister.embedMatrix_conjTranspose]
      exact (selDataInAct_embedMatrix_comm_P_anc0 E_raw217ᴴ).symm
    rw [Matrix.mul_assoc, hCommH, ← Matrix.mul_assoc, ← QRegister.embedMatrix_conjTranspose,
        ← (selDataInAct kFull80).embedMatrix_mul]
    apply congrArg (· * P_anc0)
    unfold E_raw217
    rw [← QRegister.embedMatrix_conjTranspose, ← rCSFull80.embedMatrix_mul,
        eStream217Core_mul_conjTranspose]
  rw [hP217Decomp, ← Matrix.mul_assoc, hcInv, ← Matrix.mul_assoc (uStr217FA⁻¹).1, h217Inv]
/-- Full-width (`kFull80`) `uStageAInnerSwapCat uStream217Spec131` unitary. -/
noncomputable def uInnerSwapFull : Unitary (2 ^ kFull80) :=
  rActStageAFull80.embedUnitary (uStageAInnerSwapCat uStream217Spec131)
open Classical in
theorem uInnerSwapFull_def :
    uInnerSwapFull = rActStageAFull80.embedUnitary (uStageAInnerSwapCat uStream217Spec131) := rfl
-- The 9 unitary factors on `(kFull80 + 18) + 18`
noncomputable def uSw_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  (selAAZ_Data.compose rCoreFull).embedUnitary uSwapCore3967
noncomputable def uXorSubst_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  ((selAAZ_Subst.compose rPosCoreInFull).concat selAAZ_Z
    (selAAZ_Subst_disj_Z.compose_left rPosCoreInFull)).embedUnitary uXorZTarget18
noncomputable def uXorData_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  ((selAAZ_Data.compose rPosCoreInFull).concat selAAZ_Z
    (selAAZ_Data_disj_Z.compose_left rPosCoreInFull)).embedUnitary uXorZTarget18
noncomputable def uPhiAnc_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  selAAZ_HeldAct.embedUnitary uPhiHeldZ18AnchorCat
noncomputable def uPhi217_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  selAAZ_HeldAct.embedUnitary uPhiHeldZ18Cat
noncomputable def uStr218_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  (selAAZ_Data.compose rCSFull80).embedUnitary uStr218_3Axis
noncomputable def uStr217_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  (selAAZ_Data.compose rCSFull80).embedUnitary (uStr3AxisOfSpec uStream217Spec131)
noncomputable def uHeadAnc_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  (selAAZ_AA.compose (selLiftAct rPosCoreInFull)).embedUnitary uHeadAnchorConjH
noncomputable def uHeadData_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  (selAAZ_Data.compose rPosCoreInFull).embedUnitary uHeadConjHCore
noncomputable def uC9_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
    (uSw_AAZ * (uXorSubst_AAZ * uPhiAnc_AAZ⁻¹)) * ((uStr218_AAZ * (uHeadAnc_AAZ *
    uStr218_AAZ⁻¹)) * (uPhiAnc_AAZ * (uXorSubst_AAZ * uSw_AAZ)))
theorem uC9_AAZ_def : uC9_AAZ = (uSw_AAZ * (uXorSubst_AAZ * uPhiAnc_AAZ⁻¹)) * ((uStr218_AAZ *
    (uHeadAnc_AAZ * uStr218_AAZ⁻¹)) * (uPhiAnc_AAZ * (uXorSubst_AAZ * uSw_AAZ))) := rfl
attribute [irreducible] uC9_AAZ
noncomputable def uData9_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  uSw_AAZ * (selAAZ_ActStageAZ.embedUnitary (uStageAInnerFullCat uStream217Spec131) * uSw_AAZ)
noncomputable def F_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  selAAZ_AA.embedUnitary (uBarrelFastAct * uSlot0MeasSwap)
noncomputable def Finv_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  selAAZ_AA.embedUnitary (uSlot0MeasSwap * uBarrelFastAct)
theorem F_AAZ_mul_Finv_AAZ : F_AAZ * Finv_AAZ = 1 ∧ Finv_AAZ * F_AAZ = 1 := by
  have h1 : (uBarrelFastAct * uSlot0MeasSwap) * (uSlot0MeasSwap * uBarrelFastAct) = 1 := by
    calc (uBarrelFastAct * uSlot0MeasSwap) * (uSlot0MeasSwap * uBarrelFastAct)
        = uBarrelFastAct * (uSlot0MeasSwap * uSlot0MeasSwap) * uBarrelFastAct := by
          simp only [mul_assoc]
      _ = uBarrelFastAct * uBarrelFastAct := by rw [uSlot0MeasSwap_mul_self, mul_one]
      _ = 1 := uBarrelFastAct_mul_self
  have h2 : (uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap) = 1 := by
    calc (uSlot0MeasSwap * uBarrelFastAct) * (uBarrelFastAct * uSlot0MeasSwap)
        = uSlot0MeasSwap * (uBarrelFastAct * uBarrelFastAct) * uSlot0MeasSwap := by
          simp only [mul_assoc]
      _ = uSlot0MeasSwap * uSlot0MeasSwap := by rw [uBarrelFastAct_mul_self, mul_one]
      _ = 1 := uSlot0MeasSwap_mul_self
  exact ⟨by
    dsimp only [F_AAZ, Finv_AAZ]; rw [← QRegister.embedUnitary_mul, h1, QRegister.embedUnitary_one],
         by
           dsimp only [F_AAZ, Finv_AAZ];
           rw [← QRegister.embedUnitary_mul, h2, QRegister.embedUnitary_one]⟩
theorem uData9_AAZ_eq_prod9 : uData9_AAZ = (uSw_AAZ * (uXorData_AAZ * uPhi217_AAZ⁻¹)) *
    ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) * (uPhi217_AAZ * (uXorData_AAZ *
    uSw_AAZ))) := by
  obtain ⟨hHeld, hCS, hPos, hPZ⟩ := selAAZ_ActStageAZ_compositions
  unfold uData9_AAZ uStageAInnerFullCat uXorData_AAZ uPhi217_AAZ uStr217_AAZ uHeadData_AAZ
  simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv,
    ← QRegister.embedUnitary_compose, hHeld, hCS, hPos, hPZ, _root_.mul_assoc]
open Classical in
theorem uData9_AAZ_mul_PZ_eq : uData9_AAZ.1 * selAAZ_Z.basisOutcomeProjector 0 =
    (selAAZ_Data.embedUnitary uInnerSwapFull).1 * selAAZ_Z.basisOutcomeProjector 0 := by
  have hSwComm : uSw_AAZ.1 * selAAZ_Z.basisOutcomeProjector 0 =
      selAAZ_Z.basisOutcomeProjector 0 * uSw_AAZ.1 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selAAZ_Data.compose rCoreFull))
      selAAZ_Z (selAAZ_Data_disj_Z.compose_left rCoreFull) _ 0
  have hRed := embedUnitary_extractCleanAncillaUnitary_mul_projZero
    (selAAZ_Data.compose rActStageAFull80) selAAZ_Z
    (selAAZ_Data_disj_Z.compose_left rActStageAFull80)
    (uStageAInnerFullCat uStream217Spec131)
    (uStageAInnerFullCat_comm_projZero uStream217Spec131)
  have hSwEq : (selAAZ_Data.compose rActStageAFull80).embedUnitary ((selCoreSum42InAct.compose
      (rCoreInCoreSum42 80)).embedUnitary uSwapCore3967) = uSw_AAZ := by
    have hActCore : rActStageAFull80.compose (selCoreSum42InAct.compose (rCoreInCoreSum42 80)) =
      rCoreFull := by
      apply qreg_ext; intro i
      have hi : selCoreSum42InAct (rCoreInCoreSum42 80 i) = Fin.castAdd 7 (Fin.castAdd 42 i) :=
        Fin.ext (by simp [selCoreSum42InAct, rCoreInCoreSum42])
      rw [QRegister.compose_apply, QRegister.compose_apply, hi]
      dsimp only [rActStageAFull80]; rw [QRegister.concat_apply_left]
      dsimp only [rCSFull80]; rw [QRegister.concat_apply_left]
    rw [← QRegister.embedUnitary_compose, QRegister.compose_assoc, hActCore]
    rfl
  unfold uData9_AAZ uInnerSwapFull uStageAInnerSwapCat selAAZ_ActStageAZ
  change (uSw_AAZ.1 * ((((selAAZ_Data.compose rActStageAFull80).concat selAAZ_Z
    (selAAZ_Data_disj_Z.compose_left rActStageAFull80)).embedUnitary (uStageAInnerFullCat
    uStream217Spec131)).1 * uSw_AAZ.1)) * selAAZ_Z.basisOutcomeProjector 0 = _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hSwComm,
      ← Matrix.mul_assoc (((selAAZ_Data.compose rActStageAFull80).concat selAAZ_Z _).embedUnitary
        _).1, hRed,
      ← hSwEq]
  simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, QRegister.embedUnitary_val,
    Matrix.mul_assoc]
  rw [← (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selAAZ_Data.compose
    rActStageAFull80))
        selAAZ_Z (selAAZ_Data_disj_Z.compose_left rActStageAFull80) _ 0]
  simp only [QRegister.embedMatrix_compose]
  rfl
attribute [irreducible] uData9_AAZ
theorem basisBits_lensSwapEquiv_L_slot0Of_data_slot0_part4 {kData : ℕ}
    (rSlot0 : QRegister 18 kData) (z : Fin (2 ^ (kData + 18))) (j : Fin 18) :
    basisBits (kData + 18) (lensSwapEquiv (L_slot0Of rSlot0) z) (selDataInAct kData (rSlot0 j)) =
      basisBits (kData + 18) z (selMeasInAct kData j) := by
  have hPair : (selDataInAct kData).extractIndex (lensSwapEquiv (L_slot0Of rSlot0) z) =
      rSlot0.replaceIndex ((selDataInAct kData).extractIndex z)
        ((selMeasInAct kData).extractIndex z) := by
    have h0 := congrArg Prod.fst (extractPair_lensSwapEquiv (L_slot0Of rSlot0) z)
    dsimp only [extractPair,
      ElecHadConjLoadAndTrueSwapComp.lensSwapPerm] at h0
    rwa [L_slot0Of_updSlot] at h0
  rw [← QRegister.basisBits_extractIndex (selDataInAct kData) _ (rSlot0 j), hPair,
      QRegister.basisBits_replaceIndex_apply,
      QRegister.basisBits_extractIndex (selMeasInAct kData) z j]
theorem basisBits_lensSwapEquiv_L_slot0Of_data_of_not_mem_pa {kData : ℕ}
    (rSlot0 : QRegister 18 kData) (z : Fin (2 ^ (kData + 18)))
    {i : Fin kData} (hi : i ∉ Set.range rSlot0.wires) :
    basisBits (kData + 18) (lensSwapEquiv (L_slot0Of rSlot0) z) (selDataInAct kData i) =
      basisBits (kData + 18) z (selDataInAct kData i) := by
  have hPair : (selDataInAct kData).extractIndex (lensSwapEquiv (L_slot0Of rSlot0) z) =
      rSlot0.replaceIndex ((selDataInAct kData).extractIndex z)
        ((selMeasInAct kData).extractIndex z) := by
    have h0 := congrArg Prod.fst (extractPair_lensSwapEquiv (L_slot0Of rSlot0) z)
    dsimp only [extractPair,
      ElecHadConjLoadAndTrueSwapComp.lensSwapPerm] at h0
    rwa [L_slot0Of_updSlot] at h0
  rw [← QRegister.basisBits_extractIndex (selDataInAct kData) _ i, hPair,
      QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hi,
      QRegister.basisBits_extractIndex (selDataInAct kData) z i]
open Classical in
theorem uLensSwap_L_slot0Of_eq_embed18 {kData : ℕ} (rSlot0 : QRegister 18 kData) :
    (selLiftAct rSlot0).embedUnitary (uLensSwap (L_slot0Of (QRegExt.idReg 18))) =
      uLensSwap (L_slot0Of rSlot0) := by
  dsimp only [uLensSwap]
  rw [embedUnitary_permutationUnitary_eq]
  apply congrArg Operator.permutationUnitary
  apply Equiv.ext; intro z
  apply eq_of_basisBits_eq; intro w
  revert w
  refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_)
  · rw [← selDataInAct_apply i]
    by_cases hi : i ∈ Set.range rSlot0.wires
    · obtain ⟨q, rfl⟩ := hi
      have hLiftD : selLiftAct rSlot0 (selDataInAct 18 (QRegExt.idReg 18 q)) =
          selDataInAct kData (rSlot0 q) := by
        dsimp only [selLiftAct]
        rw [selDataInAct_apply, QRegister.concat_apply_left]; rfl
      rw [← hLiftD, liftRegPerm_apply, QRegister.basisBits_replaceIndex_apply,
          basisBits_lensSwapEquiv_L_slot0Of_data_slot0_part4 (QRegExt.idReg 18) _ q,
          QRegister.basisBits_extractIndex, hLiftD,
          basisBits_lensSwapEquiv_L_slot0Of_data_slot0_part4 rSlot0 z q]
      apply congrArg (basisBits (kData + 18) z)
      dsimp only [selLiftAct]
      rw [selMeasInAct_apply, QRegister.concat_apply_right]
    · have hnotLift : selDataInAct kData i ∉ Set.range (selLiftAct rSlot0).wires := by
        rintro ⟨u, hu⟩
        revert u; refine Fin.addCases (fun q hu ↦ ?_) (fun q hu ↦ ?_)
        · dsimp only [selLiftAct] at hu
          rw [QRegister.concat_apply_left] at hu
          exact hi ⟨q, (selDataInAct kData).wires.injective hu⟩
        · dsimp only [selLiftAct] at hu
          rw [QRegister.concat_apply_right] at hu
          exact (selDataInAct_disj_selMeasInAct kData).ne i q hu.symm
      rw [liftRegPerm_apply, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnotLift,
          basisBits_lensSwapEquiv_L_slot0Of_data_of_not_mem_pa rSlot0 z hi]
  · rw [← selMeasInAct_apply q]
    have hLiftM : selLiftAct rSlot0 (selMeasInAct 18 q) = selMeasInAct kData q := by
      dsimp only [selLiftAct]
      rw [selMeasInAct_apply, QRegister.concat_apply_right]
    rw [← hLiftM, liftRegPerm_apply, QRegister.basisBits_replaceIndex_apply,
        basisBits_lensSwapEquiv_L_slot0Of_meas (QRegExt.idReg 18) _ q,
        QRegister.basisBits_extractIndex, hLiftM,
        basisBits_lensSwapEquiv_L_slot0Of_meas rSlot0 z q]
    apply congrArg (basisBits (kData + 18) z)
    dsimp only [selLiftAct]
    rw [selDataInAct_apply, QRegister.concat_apply_left]; rfl
open Classical in
theorem uLensSwap_L_slot0Of_conj_eq_self_of_comm {kData : ℕ} (rSlot0 : QRegister 18 kData)
    (V : Unitary (2 ^ kData)) (hComm : CommutesWithReg rSlot0 V.1) : uLensSwap
    (L_slot0Of rSlot0) * (selDataInAct kData).embedUnitary V * uLensSwap (L_slot0Of rSlot0) =
    (selDataInAct kData).embedUnitary V := by
  apply Subtype.ext; ext x y
  change ((Operator.permutationUnitary (lensSwapEquiv (L_slot0Of rSlot0))).1 * (selDataInAct
    kData).embedMatrix V.1 * (Operator.permutationUnitary (lensSwapEquiv (L_slot0Of
    rSlot0))).1) x y = ((selDataInAct kData).embedMatrix V.1) x y
  rw [permUnitary_inv_conj_apply_part2 (lensSwapEquiv (L_slot0Of rSlot0))
        (lensSwapEquiv_involutive (L_slot0Of rSlot0)),
      embedMatrix_apply_sameOutside, embedMatrix_apply_sameOutside]
  have hSameMeas : ∀ a b : Fin (2 ^ (kData + 18)),
      SameOutside (Set.range (selDataInAct kData).wires) b a ↔
        (extractPair a).2 = (extractPair b).2 := fun a b ↦ by
    dsimp only [extractPair]
    constructor
    · intro hOut
      apply eq_of_basisBits_eq; intro q
      rw [QRegister.basisBits_extractIndex (selMeasInAct kData) a q,
          QRegister.basisBits_extractIndex (selMeasInAct kData) b q]
      exact hOut (selMeasInAct kData q)
        (fun ⟨i, hi⟩ ↦ (selDataInAct_disj_selMeasInAct kData).ne i q hi)
    · intro hm w; revert w
      refine Fin.addCases (fun i hw ↦ False.elim (hw ⟨i, selDataInAct_apply i⟩)) (fun q _ ↦ ?_)
      rw [← selMeasInAct_apply q, ← QRegister.basisBits_extractIndex,
          ← QRegister.basisBits_extractIndex]
      exact congrArg (fun m ↦ basisBits 18 m q) hm
  let dx := (extractPair x).1; let mx := (extractPair x).2
  let dy := (extractPair y).1; let my := (extractPair y).2
  have hx_p : extractPair (lensSwapEquiv (L_slot0Of rSlot0) x) =
      (rSlot0.replaceIndex dx mx, rSlot0.extractIndex dx) := by
    rw [extractPair_lensSwapEquiv,
        ElecHadConjLoadAndTrueSwapComp.lensSwapPerm,
        L_slot0Of_updSlot, L_slot0Of_tbl]
  have hy_p : extractPair (lensSwapEquiv (L_slot0Of rSlot0) y) =
      (rSlot0.replaceIndex dy my, rSlot0.extractIndex dy) := by
    rw [extractPair_lensSwapEquiv,
        ElecHadConjLoadAndTrueSwapComp.lensSwapPerm,
        L_slot0Of_updSlot, L_slot0Of_tbl]
  have hx1 : (selDataInAct kData).extractIndex (lensSwapEquiv (L_slot0Of rSlot0) x) =
      rSlot0.replaceIndex dx mx := by
    change (extractPair (lensSwapEquiv (L_slot0Of rSlot0) x)).1 = _
    rw [hx_p]
  have hx2 : (extractPair (lensSwapEquiv (L_slot0Of rSlot0) x)).2 =
      rSlot0.extractIndex dx := by
    rw [hx_p]
  have hy1 : (selDataInAct kData).extractIndex (lensSwapEquiv (L_slot0Of rSlot0) y) =
      rSlot0.replaceIndex dy my := by
    change (extractPair (lensSwapEquiv (L_slot0Of rSlot0) y)).1 = _
    rw [hy_p]
  have hy2 : (extractPair (lensSwapEquiv (L_slot0Of rSlot0) y)).2 =
      rSlot0.extractIndex dy := by
    rw [hy_p]
  by_cases hSP : SameOutside (Set.range (selDataInAct kData).wires)
      (lensSwapEquiv (L_slot0Of rSlot0) y) (lensSwapEquiv (L_slot0Of rSlot0) x)
  · rw [ite_eq_left hSP, hx1, hy1]
    have hEx : rSlot0.extractIndex dx = rSlot0.extractIndex dy := by
      have h2 := (hSameMeas _ _).mp hSP; rwa [hx2, hy2] at h2
    by_cases hS : SameOutside (Set.range (selDataInAct kData).wires) y x
    · rw [ite_eq_left hS]
      have hm : mx = my := (hSameMeas x y).mp hS
      rw [hm]
      exact commutesWithReg_entry_replaceIndex_eq hComm my hEx
    · rw [ite_eq_right hS]
      have hm : mx ≠ my := fun h ↦ hS ((hSameMeas x y).mpr h)
      refine commutesWithReg_entry_eq_zero_of_ne hComm ?_
      rwa [QRegister.extractIndex_replaceIndex, QRegister.extractIndex_replaceIndex]
  · rw [ite_eq_right hSP]
    have hEx : rSlot0.extractIndex dx ≠ rSlot0.extractIndex dy := fun h ↦
      hSP ((hSameMeas _ _).mpr (by rw [hx2, hy2]; exact h))
    by_cases hS : SameOutside (Set.range (selDataInAct kData).wires) y x
    · rw [ite_eq_left hS]
      exact (commutesWithReg_entry_eq_zero_of_ne hComm hEx).symm
    · rw [ite_eq_right hS]
-- Shared `(kFull80 + 18) + 18` `(Data ++ Z) ++ Anc` isomorphism and `uXorZTarget18` conjugation
abbrev kDZ_part4 : ℕ := kFull80 + 18
def isoDZ_part4 : QRegister kDZ_part4 ((kFull80 + 18) + 18) :=
  selAAZ_Data.concat selAAZ_Z selAAZ_Data_disj_Z
theorem isoDZ_part4_disj_Anc : isoDZ_part4.DisjointWires selAAZ_Anc :=
  disjointWires_concat_left selAAZ_Data_disj_Z (QRegExt.disjointWires_symm selAAZ_Anc_disj_Data)
    (QRegExt.disjointWires_symm selAAZ_Anc_disj_Z)
def isoAAZ_part4 : QRegister (kDZ_part4 + 18) ((kFull80 + 18) + 18) :=
  isoDZ_part4.concat selAAZ_Anc isoDZ_part4_disj_Anc
theorem isoAAZ_part4_applies : (∀ w, isoAAZ_part4 (selDataInAct kDZ_part4 w) = isoDZ_part4 w) ∧
    (∀ q, isoAAZ_part4 (selMeasInAct kDZ_part4 q) = selAAZ_Anc q) ∧
    (∀ w, isoDZ_part4 (selDataInAct kFull80 w) = selAAZ_Data w) ∧
    (∀ q, isoDZ_part4 (selMeasInAct kFull80 q) = selAAZ_Z q) :=
  ⟨fun w ↦ by
    dsimp only [isoAAZ_part4];
    rw [← QRegister.compose_apply _ (selDataInAct kDZ_part4), concat_compose_selDataInAct],
   fun q ↦ by
     dsimp only [isoAAZ_part4];
     rw [← QRegister.compose_apply _ (selMeasInAct kDZ_part4), concat_compose_selMeasInAct],
   fun w ↦ by
     dsimp only [isoDZ_part4];
     rw [← QRegister.compose_apply _ (selDataInAct kFull80), concat_compose_selDataInAct],
   fun q ↦ by
     dsimp only [isoDZ_part4];
     rw [← QRegister.compose_apply _ (selMeasInAct kFull80), concat_compose_selMeasInAct]⟩
def rSlot0DZ_part4 : QRegister 18 kDZ_part4 := (selDataInAct kFull80).compose rSlot0InFull
open Classical in
theorem isoAAZ_embedUnitary_uLensSwap_slot0 : isoAAZ_part4.embedUnitary
    (uLensSwap (L_slot0Of rSlot0DZ_part4)) = selAAZ_AA.embedUnitary uSlot0MeasSwap := by
  obtain ⟨hiso_D, hiso_M, hisoDZ_D, _⟩ := isoAAZ_part4_applies
  rw [← uLensSwap_L_slot0Of_eq_embed18 rSlot0DZ_part4,
      uSlot0MeasSwap, L_slot0, ← uLensSwap_L_slot0Of_eq_embed18 rSlot0InFull,
      ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
  have hR : isoAAZ_part4.compose (selLiftAct rSlot0DZ_part4) =
      selAAZ_AA.compose (selLiftAct rSlot0InFull) := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun q ↦ ?_) (fun q ↦ ?_) idx
    · simp only [selLiftAct, rSlot0DZ_part4, QRegister.compose_apply, QRegister.concat_apply_left,
        hiso_D, hisoDZ_D, selAAZ_Data]
    · simp only [selLiftAct, QRegister.compose_apply, QRegister.concat_apply_right, hiso_M,
        selAAZ_Anc]
  rw [hR]
def selCoreDZ_part4 : QRegister (fullSysCoreWires 80) kDZ_part4 :=
  (selDataInAct kFull80).compose rCoreFull
def rC_DZ_part4 : QRegister posCoreWires kDZ_part4 :=
  (selDataInAct kFull80).compose rPosCoreInFull
def rZ_DZ_part4 : QRegister 18 kDZ_part4 := selMeasInAct kFull80
def rPZ_DZ_part4 : QRegister (posCoreWires + 18) kDZ_part4 :=
  rC_DZ_part4.concat rZ_DZ_part4 ((selDataInAct_disj_selMeasInAct kFull80).compose_left
    rPosCoreInFull)
noncomputable def uXorDZ_part4 : Unitary (2 ^ kDZ_part4) :=
  rPZ_DZ_part4.embedUnitary uXorZTarget18
noncomputable def gXorDZ_part4 (β : BitAssignment kDZ_part4) : BitAssignment kDZ_part4 :=
  writeReg β rZ_DZ_part4 fun k ↦
    β (rZ_DZ_part4 k) + basisBits 18 (headTargetPoint18 (fun i ↦ β (rC_DZ_part4 i))) k
theorem ket_uXorDZ_part4 (β : BitAssignment kDZ_part4) : uXorDZ_part4.1.mulVec (ket β) = ket
    (gXorDZ_part4 β) := ket_embedUnitary_uXorZTarget18 rC_DZ_part4 rZ_DZ_part4 _ β
theorem hSpec_uXorDZ_part4 : ActsAsIdOnSpectatorWires selCoreDZ_part4 uXorDZ_part4 := by
  have hSpecDisjZ : (spectatorElecReg selCoreDZ_part4).DisjointWires rZ_DZ_part4 :=
    ((selDataInAct_disj_selMeasInAct kFull80).compose_left rCoreFull).compose_left _
  have hnSpec : ∀ q : Wire posCoreWires, q.val < 18 ∨ 3924 ≤ q.val →
      rC_DZ_part4 q ∉ Set.range (spectatorElecReg selCoreDZ_part4).wires := by
    rintro q hq ⟨t, ht⟩
    have hCoreEq := rCoreFull.wires.injective ((selDataInAct kFull80).wires.injective ht)
    have hv := congrArg Fin.val hCoreEq
    have := t.isLt
    simp [selPosCoreInCore80] at hv
    omega
  have hTgtInv : ∀ (β : BitAssignment kDZ_part4) (u : BitAssignment 3906),
      headTargetPoint18 (fun i ↦ writeReg β (spectatorElecReg selCoreDZ_part4) u (rC_DZ_part4 i)) =
        headTargetPoint18 (fun i ↦ β (rC_DZ_part4 i)) := fun β u ↦ by
    have hBit : ∀ q : Wire posCoreWires, q.val < 18 ∨ 3924 ≤ q.val →
        writeReg β (spectatorElecReg selCoreDZ_part4) u (rC_DZ_part4 q) = β (rC_DZ_part4 q) :=
      fun q hq ↦ writeReg_apply_of_not_mem _ _ _ _ (hnSpec q hq)
    exact headTargetPoint18_congr_assoc
      (headTargetCoord64_congr_outside_spec_and_wTh
        (hBit _ (Or.inr (by rw [wSlot0Core_ofFin_val_assoc]; omega)))
        (fun q ↦ hBit _ (Or.inr (by rw [rHeadFine21_ofFin_val_assoc]; omega)))
        (fun q ↦ hBit _ (Or.inl (by rw [rElecSlot0_ofFin_val_assoc]; have := q.isLt; omega)))
        (fun q ↦ hBit _ (Or.inr (by rw [rCosetB0_ofFin_val_assoc]; omega)))).2
  refine commutesWithReg_of_mulVec_ket_assoc (spectatorElecReg selCoreDZ_part4) uXorDZ_part4.1
    (fun _ ↦ 1) gXorDZ_part4 (fun β ↦ by rw [one_smul]; exact ket_uXorDZ_part4 β) (fun _ _ ↦ rfl)
    (fun β u ↦ ?_) (fun β t ↦ writeReg_apply_of_not_mem _ _ _ _
      (fun ⟨k, hk⟩ ↦ hSpecDisjZ.ne t k hk.symm))
  funext w
  unfold gXorDZ_part4
  rw [hTgtInv β u]
  by_cases hwS : w ∈ Set.range (spectatorElecReg selCoreDZ_part4).wires
  · obtain ⟨t, rfl⟩ := hwS
    have hnZ : spectatorElecReg selCoreDZ_part4 t ∉ Set.range rZ_DZ_part4.wires :=
      fun ⟨k, hk⟩ ↦ hSpecDisjZ.ne t k hk.symm
    rw [writeReg_apply_of_not_mem _ _ _ _ hnZ, writeReg_apply_reg, writeReg_apply_reg]
  · by_cases hwZ : w ∈ Set.range rZ_DZ_part4.wires
    · obtain ⟨k, rfl⟩ := hwZ
      have hnS : ∀ k' : Fin 18,
        rZ_DZ_part4 k' ∉ Set.range (spectatorElecReg selCoreDZ_part4).wires :=
        fun k' ⟨t, ht⟩ ↦ hSpecDisjZ.ne t k' ht
      rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ (hnS k),
          writeReg_apply_of_not_mem _ _ _ _ (hnS k), writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hwZ, writeReg_apply_of_not_mem _ _ _ _ hwS,
          writeReg_apply_of_not_mem _ _ _ _ hwS, writeReg_apply_of_not_mem _ _ _ _ hwZ]
theorem hHigh_uXorDZ_part4 : PreservesHigh3924On selCoreDZ_part4 uXorDZ_part4 := fun w _ b ↦
    comm_singleton_proj_of_ket_perm uXorDZ_part4.1 gXorDZ_part4 ket_uXorDZ_part4
    (selCoreDZ_part4 w) (fun _ ↦ writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦
    (selDataInAct_disj_selMeasInAct kFull80).ne (rCoreFull w) k hk.symm)) b
open Classical in
theorem isoAAZ_embedUnitary_uXorDZ_data :
    isoAAZ_part4.embedUnitary ((selDataInAct kDZ_part4).embedUnitary uXorDZ_part4) = uXorData_AAZ :=
      by
  obtain ⟨hiso_D, _, hisoDZ_D, hisoDZ_M⟩ := isoAAZ_part4_applies
  unfold uXorDZ_part4 uXorData_AAZ
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose, QRegister.compose_assoc]
  have hR : isoAAZ_part4.compose ((selDataInAct kDZ_part4).compose rPZ_DZ_part4) =
      (selAAZ_Data.compose rPosCoreInFull).concat selAAZ_Z
        (selAAZ_Data_disj_Z.compose_left rPosCoreInFull) := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simp only [rPZ_DZ_part4, rC_DZ_part4, QRegister.compose_apply, QRegister.concat_apply_left,
        hiso_D, hisoDZ_D]
    · simp only [rPZ_DZ_part4, rZ_DZ_part4, QRegister.compose_apply, QRegister.concat_apply_right,
        hiso_D, hisoDZ_M]
  rw [hR]
open Classical in
theorem isoAAZ_embedUnitary_uXorDZ_subst : isoAAZ_part4.embedUnitary
    ((selSubstSlot0 rSlot0DZ_part4).embedUnitary uXorDZ_part4) = uXorSubst_AAZ := by
  obtain ⟨hiso_D, hiso_M, hisoDZ_D, hisoDZ_M⟩ := isoAAZ_part4_applies
  unfold uXorDZ_part4 uXorSubst_AAZ
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose, QRegister.compose_assoc]
  have hR : isoAAZ_part4.compose ((selSubstSlot0 rSlot0DZ_part4).compose rPZ_DZ_part4) =
      (selAAZ_Subst.compose rPosCoreInFull).concat selAAZ_Z
        (selAAZ_Subst_disj_Z.compose_left rPosCoreInFull) := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simp only [rPZ_DZ_part4, rC_DZ_part4, QRegister.compose_apply, QRegister.concat_apply_left]
      by_cases hi0 : rPosCoreInFull i ∈ Set.range rSlot0InFull.wires
      · obtain ⟨q, hq⟩ := hi0
        have hDZ0 : selDataInAct kFull80 (rPosCoreInFull i) = rSlot0DZ_part4 q := by
          dsimp only [rSlot0DZ_part4]; rw [QRegister.compose_apply, hq]
        dsimp only [selAAZ_Subst]
        simp only [QRegister.compose_apply]
        rw [hDZ0, selSubstSlot0, rDataSubstSlot0_apply_slot0, hiso_M,
            ← hq, selSubstSlot0, rDataSubstSlot0_apply_slot0]; rfl
      · have hnDZ0 : selDataInAct kFull80 (rPosCoreInFull i) ∉ Set.range rSlot0DZ_part4.wires := by
          rintro ⟨q, hq⟩
          exact hi0 ⟨q, (selDataInAct kFull80).wires.injective hq⟩
        dsimp only [selAAZ_Subst]
        simp only [QRegister.compose_apply]
        rw [selSubstSlot0, rDataSubstSlot0_apply_of_not_mem _ _ _ _ hnDZ0,
            hiso_D, hisoDZ_D, selSubstSlot0,
            rDataSubstSlot0_apply_of_not_mem _ _ _ _ hi0]; rfl
    · simp only [rPZ_DZ_part4, rZ_DZ_part4, QRegister.compose_apply, QRegister.concat_apply_right]
      have hnDZ0 : selMeasInAct kFull80 j ∉ Set.range rSlot0DZ_part4.wires := by
        rintro ⟨q, hq⟩
        exact (selDataInAct_disj_selMeasInAct kFull80).ne (rSlot0InFull q) j hq
      rw [selSubstSlot0, rDataSubstSlot0_apply_of_not_mem _ _ _ _ hnDZ0, hiso_D, hisoDZ_M]
  rw [hR]
attribute [irreducible] uXorDZ_part4
open Classical in
theorem Finv_mul_uXorSubst_mul_F_eq : Finv_AAZ * uXorSubst_AAZ * F_AAZ = uXorData_AAZ := by
  obtain ⟨hiso_D, _, hisoDZ_D, _⟩ := isoAAZ_part4_applies
  have hSlot0DZEq : selCoreDZ_part4.compose (rFullSysElecSlot (le_refl 80) 0) = rSlot0DZ_part4 := by
    apply qreg_ext; intro q; rfl
  have hLens : uLensSwap (L_slot0Of (selCoreDZ_part4.compose (rFullSysElecSlot (le_refl 80)
      0))) * (selDataInAct kDZ_part4).embedUnitary uXorDZ_part4 * uLensSwap (L_slot0Of
      (selCoreDZ_part4.compose (rFullSysElecSlot (le_refl 80) 0))) = (((selDataInAct
      kDZ_part4).compose selCoreDZ_part4).embedUnitary (uBarrelFast (le_refl 80)) * uLensSwap
      (L_slot0Of (selCoreDZ_part4.compose (rFullSysElecSlot (le_refl 80) 0)))) *
      (selDataInAct kDZ_part4).embedUnitary uXorDZ_part4 * (uLensSwap (L_slot0Of
      (selCoreDZ_part4.compose (rFullSysElecSlot (le_refl 80) 0))) * ((selDataInAct
      kDZ_part4).compose selCoreDZ_part4).embedUnitary (uBarrelFast (le_refl 80))) :=
      uLensSwap_slot0_conj_eq_gen (le_refl 80) selCoreDZ_part4 uXorDZ_part4 hSpec_uXorDZ_part4
      hHigh_uXorDZ_part4
  rw [hSlot0DZEq] at hLens
  have hLHS : uLensSwap (L_slot0Of rSlot0DZ_part4) *
    (selDataInAct kDZ_part4).embedUnitary uXorDZ_part4 *
        uLensSwap (L_slot0Of rSlot0DZ_part4) =
      (selSubstSlot0 rSlot0DZ_part4).embedUnitary uXorDZ_part4 :=
    Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0DZ_part4 uXorDZ_part4.1).symm
  rw [hLHS] at hLens
  have hIsoBar : isoAAZ_part4.embedUnitary
        (((selDataInAct kDZ_part4).compose selCoreDZ_part4).embedUnitary (uBarrelFast (le_refl 80)))
          =
      selAAZ_AA.embedUnitary uBarrelFastAct := by
    rw [← QRegister.embedUnitary_compose, uBarrelFastAct, ← QRegister.embedUnitary_compose]
    have hR : isoAAZ_part4.compose ((selDataInAct kDZ_part4).compose selCoreDZ_part4) =
        selAAZ_AA.compose ((selDataInAct kFull80).compose rCoreFull) := by
      apply qreg_ext; intro i
      simp only [selCoreDZ_part4, QRegister.compose_apply, hiso_D, hisoDZ_D, selAAZ_Data]
    rw [hR]
  have hIsoEmb := congrArg isoAAZ_part4.embedUnitary hLens
  rw[isoAAZ_embedUnitary_uXorDZ_subst, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
      QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, hIsoBar,
      isoAAZ_embedUnitary_uLensSwap_slot0, isoAAZ_embedUnitary_uXorDZ_data] at hIsoEmb
  have hFEq : selAAZ_AA.embedUnitary uBarrelFastAct * selAAZ_AA.embedUnitary uSlot0MeasSwap =
    F_AAZ :=
    (QRegister.embedUnitary_mul _ _ _).symm
  have hFinvEq : selAAZ_AA.embedUnitary uSlot0MeasSwap * selAAZ_AA.embedUnitary uBarrelFastAct =
    Finv_AAZ :=
    (QRegister.embedUnitary_mul _ _ _).symm
  rw [hFEq, hFinvEq] at hIsoEmb
  calc Finv_AAZ * uXorSubst_AAZ * F_AAZ
      = Finv_AAZ * (F_AAZ * uXorData_AAZ * Finv_AAZ) * F_AAZ := by rw [hIsoEmb]
    _ = (Finv_AAZ * F_AAZ) * uXorData_AAZ * (Finv_AAZ * F_AAZ) := by simp only [mul_assoc]
    _ = uXorData_AAZ := by rw [F_AAZ_mul_Finv_AAZ.2, one_mul, mul_one]
private theorem selAAZ_HeldAct_disj_Anc : selAAZ_HeldAct.DisjointWires selAAZ_Anc := by
  dsimp only [selAAZ_HeldAct]
  exact disjointWires_concat_left _ (disjointWires_concat_left _
    (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right rCSFull80))
      (QRegExt.disjointWires_symm selAAZ_Anc_disj_Z))
    (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right rPG7Full))
open Classical in
private theorem uPE18_inv_comm_uPhi217_inv : (selAAZ_Anc.embedUnitary uPointElec18)⁻¹ *
    uPhi217_AAZ⁻¹ = uPhi217_AAZ⁻¹ * (selAAZ_Anc.embedUnitary uPointElec18)⁻¹ := by
  apply Subtype.ext
  unfold uPhi217_AAZ
  rw [← QRegister.embedUnitary_inv, ← QRegister.embedUnitary_inv selAAZ_HeldAct uPhiHeldZ18Cat]
  exact selAAZ_Anc.embedMatrix_comm_of_disjoint selAAZ_HeldAct (QRegExt.disjointWires_symm
    selAAZ_HeldAct_disj_Anc) _ _
-- Conjugation of Factor 3 & 7 (`uPhiAnc_AAZ` and `uPhiAnc_AAZ⁻¹`) by `F_AAZ`: exact global identity
open Classical in
theorem Finv_mul_uPhiAnc_mul_F_eq : Finv_AAZ * uPhiAnc_AAZ * F_AAZ = selAAZ_Anc.embedUnitary
    uPointElec18 * uPhi217_AAZ ∧ Finv_AAZ * uPhiAnc_AAZ⁻¹ * F_AAZ =
    (selAAZ_Anc.embedUnitary uPointElec18)⁻¹ * uPhi217_AAZ⁻¹ := by
  let rC := selHeldZ18SysInAct.compose selCoreInHeldZ18Sys
  have hHeldCore : selAAZ_HeldAct.compose rC = selAAZ_Data.compose rPosCoreInFull := by
    apply qreg_ext; intro i
    have hiSys : selCoreInHeldZ18Sys i =
        Fin.castAdd 18 (Fin.castAdd 42 (selPosCoreInCore80 i)) :=
      Fin.ext (by simp [selCoreInHeldZ18Sys, selPosCoreInCore80])
    have hiAct : selHeldZ18SysInAct (selCoreInHeldZ18Sys i) =
      Fin.castAdd 7 (selCoreInHeldZ18Sys i) :=
      Fin.ext (by simp [selHeldZ18SysInAct])
    dsimp only [rC, selAAZ_HeldAct, rPosCoreInFull]
    rw [QRegister.compose_apply, QRegister.compose_apply, hiAct, QRegister.concat_apply_left,
        hiSys, QRegister.concat_apply_left]
    dsimp only [rCSFull80]
    rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.compose_apply]
    rfl
  let rLiftPos := selAAZ_AA.compose (selLiftAct rPosCoreInFull)
  have hLiftTau : rLiftPos.embedUnitary τ_pos = selAAZ_AA.embedUnitary uBarrelFastAct := by
    dsimp only [rLiftPos]; rw [QRegister.embedUnitary_compose, selLiftAct_rPosCoreInFull_τ_σ.1]
  have hLiftSig : rLiftPos.embedUnitary σ_0_pos = selAAZ_AA.embedUnitary uSlot0MeasSwap := by
    dsimp only [rLiftPos]; rw [QRegister.embedUnitary_compose, selLiftAct_rPosCoreInFull_τ_σ.2]
  have hLiftF : rLiftPos.embedUnitary (τ_pos * σ_0_pos) = F_AAZ := by
    rw [QRegister.embedUnitary_mul, hLiftTau, hLiftSig, ← QRegister.embedUnitary_mul]; rfl
  have hLiftFinv : rLiftPos.embedUnitary (σ_0_pos * τ_pos) = Finv_AAZ := by
    rw [QRegister.embedUnitary_mul, hLiftSig, hLiftTau, ← QRegister.embedUnitary_mul]; rfl
  have hLiftData : rLiftPos.compose (selDataInAct posCoreWires) =
    selAAZ_Data.compose rPosCoreInFull := by
    dsimp only [rLiftPos, selLiftAct, selAAZ_Data]
    rw [QRegister.compose_assoc, concat_compose_selDataInAct, ← QRegister.compose_assoc]
  have hLiftMeas : rLiftPos.compose (selMeasInAct posCoreWires) = selAAZ_Anc := by
    dsimp only [rLiftPos, selLiftAct, selAAZ_Anc]
    rw [QRegister.compose_assoc, concat_compose_selMeasInAct]
  have hElecConj : Finv_AAZ * (selAAZ_Data.compose rPosCoreInFull).embedUnitary uPointElec218Core *
    F_AAZ =
      selAAZ_Anc.embedUnitary uPointElec18 *
        (selAAZ_Data.compose rPosCoreInFull).embedUnitary uPointElec217Core := by
    have hPos := congrArg rLiftPos.embedUnitary (elecProd218Pos_eq_anchorConj uPointElec18)
    simp only [QRegister.embedUnitary_mul, hLiftFinv, hLiftF,
      ← QRegister.embedUnitary_compose, ← QRegister.compose_assoc, hLiftData, hLiftMeas] at hPos
    have hSlot0IdEq : rElecSlot (QRegExt.idReg posCoreWires) 0 = rSlot0Pos := by
      apply qreg_ext; intro q
      exact Fin.ext (by simp [rSlot0Pos, rElecSlot, QRegExt.idReg, QRegExt.ofFin])
    unfold uPointElec218Core uPointElec217Core
    rw [hSlot0IdEq]
    simpa only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose] using hPos
  -- `uPhiNonCoreCat` commutes with `F_AAZ` (commutes with `rPosCoreInFull` + disjoint from
  -- `selAAZ_Anc`)
  let uNonCore_AAZ := selAAZ_HeldAct.embedUnitary uPhiNonCoreCat
  have hNC_comm_Pos : CommutesWithReg (selAAZ_Data.compose rPosCoreInFull) uNonCore_AAZ.1 :=
    commutesWithReg_compose_assoc hHeldCore commutesWithReg_core_uPhiNonCoreCat
  have hNC_comm_Bar : (selAAZ_AA.embedUnitary uBarrelFastAct) * uNonCore_AAZ =
      uNonCore_AAZ * (selAAZ_AA.embedUnitary uBarrelFastAct) := by
    let selCore80InPos : QRegister (fullSysCoreWires 80) posCoreWires :=
      ⟨⟨fun i ↦ ⟨i.val, by
          have := posCoreWires_eq_4034_assoc
          have := fullSysCoreWires80_eq_4034_assoc
          have := i.isLt; omega⟩,
        fun i j h ↦ Fin.ext (by simpa using congrArg Fin.val h)⟩⟩
    have hCompCore : (selAAZ_Data.compose rPosCoreInFull).compose selCore80InPos =
        selAAZ_AA.compose ((selDataInAct kFull80).compose rCoreFull) := by
      apply qreg_ext; intro i
      dsimp only [rPosCoreInFull, selAAZ_Data]
      rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.compose_apply,
          QRegister.compose_apply, QRegister.compose_apply]
      apply congrArg (selAAZ_AA.compose (selDataInAct kFull80))
      apply congrArg rCoreFull
      exact Fin.ext (by simp [selPosCoreInCore80, selCore80InPos])
    apply Subtype.ext
    simp only [Submonoid.coe_mul]
    dsimp only [uBarrelFastAct]
    rw [← QRegister.embedUnitary_compose, ← hCompCore, QRegister.embedUnitary_val,
        QRegister.embedMatrix_compose]
    exact (hNC_comm_Pos _).symm
  have hNC_comm_S0 : (selAAZ_AA.embedUnitary uSlot0MeasSwap) * uNonCore_AAZ =
      uNonCore_AAZ * (selAAZ_AA.embedUnitary uSlot0MeasSwap) := by
    obtain ⟨hiso_D, _, hisoDZ_D, hisoDZ_M⟩ := isoAAZ_part4_applies
    let rHeldDZ : QRegister kHeldZ18Act kDZ_part4 :=
      let rCS := (selDataInAct kFull80).compose rCSFull80
      let rPG7 := (selDataInAct kFull80).compose rPG7Full
      let hCS_Z := (selDataInAct_disj_selMeasInAct kFull80).compose_left rCSFull80
      let hCS_PG := disjointWires_compose_of_disjoint (selDataInAct kFull80) hCSFull80_disj_rPG7Full
      let hPG_Z := (selDataInAct_disj_selMeasInAct kFull80).compose_left rPG7Full
      (rCS.concat (selMeasInAct kFull80) hCS_Z).concat rPG7
        (disjointWires_concat_left hCS_Z hCS_PG (QRegExt.disjointWires_symm hPG_Z))
    have hSlot0InHeldDZ : rHeldDZ.compose (rC.compose rSlot0Pos) = rSlot0DZ_part4 := by
      apply qreg_ext; intro q
      have hqSys : selCoreInHeldZ18Sys (rSlot0Pos q) =
          Fin.castAdd 18 (Fin.castAdd 42 (rSlot0InCore q)) :=
        Fin.ext (by
          rw [Fin.val_castAdd, Fin.val_castAdd, rSlot0InCore, rFullSysElecSlot_val]
          simp [selCoreInHeldZ18Sys, rSlot0Pos, rElecSlot,
            QRegExt.ofFin])
      have hqAct : rC (rSlot0Pos q) = Fin.castAdd 7 (selCoreInHeldZ18Sys (rSlot0Pos q)) :=
        Fin.ext (by simp [rC, selHeldZ18SysInAct])
      dsimp only [rHeldDZ, rSlot0DZ_part4]
      rw [QRegister.compose_apply, QRegister.compose_apply, hqAct, QRegister.concat_apply_left,
          hqSys, QRegister.concat_apply_left]
      dsimp only [rCSFull80, rSlot0InFull]
      rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.compose_apply]
      rfl
    have hCommSlot0DZ : CommutesWithReg rSlot0DZ_part4 (rHeldDZ.embedUnitary uPhiNonCoreCat).1 :=
      commutesWithReg_compose_assoc hSlot0InHeldDZ
        (fun A ↦ by
          rw [QRegister.embedMatrix_compose rC rSlot0Pos A]
          exact commutesWithReg_core_uPhiNonCoreCat (rSlot0Pos.embedMatrix A))
    have hConjDZ := uLensSwap_L_slot0Of_conj_eq_self_of_comm rSlot0DZ_part4
      (rHeldDZ.embedUnitary uPhiNonCoreCat) hCommSlot0DZ
    have hIsoNC : isoAAZ_part4.embedUnitary ((selDataInAct kDZ_part4).embedUnitary
        (rHeldDZ.embedUnitary uPhiNonCoreCat)) = uNonCore_AAZ := by
      dsimp only [uNonCore_AAZ]
      rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
        QRegister.compose_assoc]
      have hR : isoAAZ_part4.compose ((selDataInAct kDZ_part4).compose rHeldDZ) = selAAZ_HeldAct :=
        by
        apply qreg_ext; intro idx
        refine Fin.addCases (fun iCZ ↦ ?_) (fun mPG ↦ ?_) idx
        · refine Fin.addCases (fun iCS ↦ ?_) (fun jZ ↦ ?_) iCZ
          · simp only [rHeldDZ, selAAZ_HeldAct, QRegister.compose_apply,
              QRegister.concat_apply_left, hiso_D, hisoDZ_D]
          · simp only [rHeldDZ, selAAZ_HeldAct, QRegister.compose_apply,
              QRegister.concat_apply_left, QRegister.concat_apply_right, hiso_D, hisoDZ_M]
        · simp only [rHeldDZ, selAAZ_HeldAct, QRegister.compose_apply,
            QRegister.concat_apply_right, hiso_D, hisoDZ_D]
      rw [hR]
    have hIsoConj := congrArg isoAAZ_part4.embedUnitary hConjDZ
    rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
        isoAAZ_embedUnitary_uLensSwap_slot0, hIsoNC] at hIsoConj
    have hS0Sq : selAAZ_AA.embedUnitary uSlot0MeasSwap * selAAZ_AA.embedUnitary uSlot0MeasSwap =
      1 := by
      rw [← QRegister.embedUnitary_mul, uSlot0MeasSwap_mul_self, QRegister.embedUnitary_one]
    calc selAAZ_AA.embedUnitary uSlot0MeasSwap * uNonCore_AAZ
        = (selAAZ_AA.embedUnitary uSlot0MeasSwap * uNonCore_AAZ *
            selAAZ_AA.embedUnitary uSlot0MeasSwap) * selAAZ_AA.embedUnitary uSlot0MeasSwap := by
            rw [mul_assoc _ (selAAZ_AA.embedUnitary uSlot0MeasSwap), hS0Sq, mul_one]
      _ = uNonCore_AAZ * selAAZ_AA.embedUnitary uSlot0MeasSwap := by rw [hIsoConj]
  have hNC_conj : Finv_AAZ * uNonCore_AAZ * F_AAZ = uNonCore_AAZ := by
    have hCommF : uNonCore_AAZ * F_AAZ = F_AAZ * uNonCore_AAZ := by
      dsimp only [F_AAZ]
      rw [QRegister.embedUnitary_mul, ← mul_assoc, ← hNC_comm_Bar, mul_assoc, ← hNC_comm_S0,
        ← mul_assoc]
    calc Finv_AAZ * uNonCore_AAZ * F_AAZ
        = Finv_AAZ * (uNonCore_AAZ * F_AAZ) := by rw [mul_assoc]
      _ = (Finv_AAZ * F_AAZ) * uNonCore_AAZ := by rw [hCommF, ← mul_assoc]
      _ = uNonCore_AAZ := by rw [F_AAZ_mul_Finv_AAZ.2, one_mul]
  have hFwd : Finv_AAZ * uPhiAnc_AAZ * F_AAZ =
      selAAZ_Anc.embedUnitary uPointElec18 * uPhi217_AAZ := by
    have hAncDecomp : uPhiAnc_AAZ =
        (selAAZ_Data.compose rPosCoreInFull).embedUnitary uPointElec218Core * uNonCore_AAZ := by
      unfold uPhiAnc_AAZ
      rw [uPhiHeldZ18AnchorCat_eq_elec218_mul_nonCore, QRegister.embedUnitary_mul,
          ← QRegister.embedUnitary_compose, hHeldCore]
    have h217Decomp : uPhi217_AAZ =
        (selAAZ_Data.compose rPosCoreInFull).embedUnitary uPointElec217Core * uNonCore_AAZ := by
      unfold uPhi217_AAZ
      rw [uPhiHeldZ18Cat_eq_elec217_mul_nonCore, QRegister.embedUnitary_mul,
          ← QRegister.embedUnitary_compose, hHeldCore]
    calc Finv_AAZ * uPhiAnc_AAZ * F_AAZ
        = Finv_AAZ * ((selAAZ_Data.compose rPosCoreInFull).embedUnitary uPointElec218Core *
            (F_AAZ * Finv_AAZ) * uNonCore_AAZ) * F_AAZ := by
            rw [hAncDecomp, F_AAZ_mul_Finv_AAZ.1, mul_one]
      _ = (Finv_AAZ * (selAAZ_Data.compose rPosCoreInFull).embedUnitary uPointElec218Core * F_AAZ) *
            (Finv_AAZ * uNonCore_AAZ * F_AAZ) := by simp only [mul_assoc]
      _ = selAAZ_Anc.embedUnitary uPointElec18 * uPhi217_AAZ := by
            rw [hElecConj, hNC_conj, h217Decomp, mul_assoc]
  refine ⟨hFwd, ?_⟩
  have hProdEq1 : (Finv_AAZ * uPhiAnc_AAZ⁻¹ * F_AAZ) * (Finv_AAZ * uPhiAnc_AAZ * F_AAZ) = 1 := by
    calc (Finv_AAZ * uPhiAnc_AAZ⁻¹ * F_AAZ) * (Finv_AAZ * uPhiAnc_AAZ * F_AAZ)
        = Finv_AAZ * uPhiAnc_AAZ⁻¹ * (F_AAZ * Finv_AAZ) * uPhiAnc_AAZ * F_AAZ := by
          simp only [mul_assoc]
      _ = Finv_AAZ * (uPhiAnc_AAZ⁻¹ * uPhiAnc_AAZ) * F_AAZ := by
            rw [F_AAZ_mul_Finv_AAZ.1, mul_one]
            simp only [mul_assoc]
      _ = 1 := by rw [inv_mul_cancel, mul_one, F_AAZ_mul_Finv_AAZ.2]
  rw [hFwd] at hProdEq1
  rw [uPE18_inv_comm_uPhi217_inv, ← _root_.mul_inv_rev]
  exact eq_inv_of_mul_eq_one_left hProdEq1
-- Conjugation of Factor 5 (`uHeadAnc_AAZ`) by `F_AAZ`: exact global identity
private theorem uHeadAnc_AAZ_eq_F_conj : uHeadAnc_AAZ = F_AAZ * uHeadData_AAZ * Finv_AAZ := by
  unfold uHeadAnc_AAZ uHeadData_AAZ F_AAZ Finv_AAZ
  rw [QRegister.embedUnitary_compose, selLiftAct_embedUnitary_uHeadAnchorConjH_eq]
  unfold uAnchorFrame
  simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose,
    ← QRegister.compose_assoc, selAAZ_Data, _root_.mul_assoc]
theorem Finv_mul_uHeadAnc_mul_F_eq : Finv_AAZ * uHeadAnc_AAZ * F_AAZ = uHeadData_AAZ := by
  calc Finv_AAZ * uHeadAnc_AAZ * F_AAZ
      = (Finv_AAZ * F_AAZ) * uHeadData_AAZ * (Finv_AAZ * F_AAZ) := by
          rw [uHeadAnc_AAZ_eq_F_conj]
          simp only [mul_assoc]
    _ = uHeadData_AAZ := by rw [F_AAZ_mul_Finv_AAZ.2, one_mul, mul_one]
-- Conjugation of Factor 1 & 9 (`uSw_AAZ`) by `F_AAZ` on `iSlot2 80 = 0`
noncomputable def Pc2_AAZ (b : Fin 2) : Operator (2 ^ ((kFull80 + 18) + 18)) :=
  (selAAZ_Data.compose rCoreFull).embedMatrix (slotBitProj (iSlot2 80) b)
theorem ket_eq_mbhs_ket_part4 {m : ℕ} (β : BitAssignment m) :
    ket β = MeasureBranchHadamardSem.ket β := rfl
theorem uSwapCore3967_mulVec_ket_part4 (β : BitAssignment (fullSysCoreWires 80)) :
    uSwapCore3967.1.mulVec (ket β) = ket (swapCore3967Fn β) := by
  rw [ket_eq_mbhs_ket_part4 β, ket_eq_mbhs_ket_part4 (swapCore3967Fn β)]
  exact uSwapCore3967_mulVec_ket β
theorem uBarrelFast_mulVec_ket_part4 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uBarrelFast hmPay).1.mulVec (ket γ) = ket (coinBarrelBitFnFast hmPay γ) := by
  rw [ket_eq_mbhs_ket_part4 γ, ket_eq_mbhs_ket_part4 (coinBarrelBitFnFast hmPay γ)]
  exact uBarrelFast_mulVec_ket hmPay γ
theorem perm_comm_diagonal_of_octKet {N : ℕ} (B : Operator (2 ^ N))
    (fB : BitAssignment N → BitAssignment N) (hB : ∀ β, B.mulVec (ket β) = ket (fB β))
    (g : Fin (2 ^ N) → ℂ) (hg : ∀ β : BitAssignment N, g ((basisBitsEquiv N).symm (fB β)) = g
    ((basisBitsEquiv N).symm β)) : B * Matrix.diagonal g = Matrix.diagonal g * B := by
  apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
  have hk : ∀ δ : BitAssignment N, MeasureBranchHadamardSem.ket δ = ket δ := fun _ ↦ rfl
  rw [hk β, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, diagonal_mulVec_ket_assoc,
      Matrix.mulVec_smul, hB β, diagonal_mulVec_ket_assoc, hg β]
open Classical in
theorem conj_perm_mul_slotBitProj_of_ket {N : ℕ} (B S : Operator (2 ^ N))
    (fB fS : BitAssignment N → BitAssignment N) (hB : ∀ β, B.mulVec
    (MeasureBranchHadamardSem.ket β) = MeasureBranchHadamardSem.ket (fB β)) (hS : ∀ β,
    S.mulVec (MeasureBranchHadamardSem.ket β) = MeasureBranchHadamardSem.ket (fS β))
    (w : Wire N) (b : Fin 2) (hEq : ∀ γ : BitAssignment N, (γ w).val = b.val → fB (fS (fB γ))
    = fS γ) : (B * S * B) * slotBitProj w b = S * slotBitProj w b := by
  apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
  have hProj : (slotBitProj w b).mulVec (MeasureBranchHadamardSem.ket γ) =
      (if (γ w).val = b.val then (1 : ℂ) else 0) • MeasureBranchHadamardSem.ket γ := by
    unfold slotBitProj
    have hket : MeasureBranchHadamardSem.ket γ = ket γ := rfl
    rw [hket, diagonal_mulVec_ket_assoc, basisBits_basisBitsEquiv_symm γ]
  rw[← Matrix.mulVec_mulVec (MeasureBranchHadamardSem.ket γ) (B * S * B),
      ← Matrix.mulVec_mulVec (MeasureBranchHadamardSem.ket γ) S, hProj]
  by_cases hw : (γ w).val = b.val
  · rw[ite_eq_left hw, one_smul, hS γ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hB γ,
      hS (fB γ), hB (fS (fB γ)), hEq γ hw]
  · rw [ite_eq_right hw, zero_smul, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem unitary_comm_val_of_inv_conj {N : ℕ} (S U : Unitary N)
    (hSq : S * S = 1) (hConj : S * U * S = U) : S.1 * U.1 = U.1 * S.1 := by
  have h : S * U = U * S := by
    calc S * U = (S * U * S) * S := by rw [_root_.mul_assoc _ S, hSq, mul_one]
      _ = U * S := by rw [hConj]
  simpa only [Submonoid.coe_mul] using congrArg (fun x : Unitary N ↦ x.1) h
theorem Pc2_AAZ_zero_add_one : Pc2_AAZ 0 + Pc2_AAZ 1 = 1 := by
  unfold Pc2_AAZ
  rw [← QRegister.embedMatrix_add,
      PosMomSelectSandwich.slotBitProj_zero_add_one (iSlot2 80),
      QRegister.embedMatrix_one]
theorem slotBitProj_congr_wire_part4 {N : ℕ} {w₁ w₂ : Wire N} (h : w₁ = w₂) (b : Fin 2) :
    slotBitProj w₁ b = slotBitProj w₂ b := congrArg (fun w ↦ slotBitProj w b) h
theorem embedMatrix_slotBitProj_part4 {k N : ℕ} (r : QRegister k N) (q : Wire k) (b : Fin 2) :
    r.embedMatrix (slotBitProj q b) = slotBitProj (r q) b := by
  unfold slotBitProj
  rw [embedMatrix_diagonal_local]
  apply congrArg Matrix.diagonal; funext x
  rw [basisBits_extractIndex_assoc]
theorem embedMatrix_slotBitProj_eq_singleton_part4 {k N : ℕ}
    (r : QRegister k N) (q : Wire k) (b : Fin 2) :
    r.embedMatrix (slotBitProj q b) =
      (QRegister.singleton (r q)).embedMatrix (slotBitProj ⟨0, by decide⟩ b) := by
  rw [embedMatrix_slotBitProj_part4, embedMatrix_slotBitProj_part4]; rfl
open Classical in
theorem uBarrelFast80_conj_uSwapCore3967_mul_slot2Zero : ((uBarrelFast (le_refl 80)).1 *
    uSwapCore3967.1 * (uBarrelFast (le_refl 80)).1) * slotBitProj (iSlot2 80) 0 =
    uSwapCore3967.1 * slotBitProj (iSlot2 80) 0 := by
  refine conj_perm_mul_slotBitProj_of_ket (uBarrelFast (le_refl 80)).1 uSwapCore3967.1
    (coinBarrelBitFnFast (le_refl 80)) swapCore3967Fn (uBarrelFast_mulVec_ket (le_refl 80))
    uSwapCore3967_mulVec_ket (iSlot2 80) 0 fun γ hc2 ↦ ?_
  have hc2z : γ (iSlot2 80) = 0 := by
    generalize γ (iSlot2 80) = z at hc2 ⊢
    fin_cases z
    · rfl
    · cases hc2
  let e := coinBarrelIdxFast (le_refl 80) γ
  let δ := swapCore3967Fn (coinBarrelBitFnFast (le_refl 80) γ)
  have hSwNe : ∀ (w : Wire (fullSysCoreWires 80)),
      w.val ≠ 3967 → w.val ≠ 4029 → ∀ β, swapCore3967Fn β w = β w := fun w h1 h2 β ↦ by
    unfold swapCore3967Fn
    rw [Equiv.swap_apply_of_ne_of_ne
      (fun h ↦ h1 (by rw [h, wCore3967_val_assoc]))
      (fun h ↦ h2 (by rw [h, wCore4029_val_assoc]))]
  have hIdxEq : coinBarrelIdxFast (le_refl 80) δ = e := by
    have hs1 : δ (iSlot1 80) = γ (iSlot1 80) := by
      dsimp only [δ]
      rw [hSwNe _ (by rw [iSlot1_80_val_assoc]; omega) (by rw [iSlot1_80_val_assoc]; omega),
          coinBarrelBitFnFast, swapElec0Bits_high _ _ _ (by rw [iSlot1_80_val_assoc]; omega)]
    have hs2 : δ (iSlot2 80) = γ (iSlot2 80) := by
      dsimp only [δ]
      rw [hSwNe _ (by rw [iSlot2_80_val_assoc]; omega) (by rw [iSlot2_80_val_assoc]; omega),
          coinBarrelBitFnFast, swapElec0Bits_high _ _ _ (by rw [iSlot2_80_val_assoc]; omega)]
    have hu8 : ∀ j : Fin 8,
        δ ⟨3968 + j.val, by have := fullSysCoreWires80_eq_4034_assoc; have := j.isLt; omega⟩ =
        γ ⟨3968 + j.val, by
          have := fullSysCoreWires80_eq_4034_assoc; have := j.isLt; omega⟩ := fun j ↦ by
      have hj := j.isLt
      dsimp only [δ]
      rw [hSwNe _ (by dsimp only; omega) (by dsimp only; omega),
          coinBarrelBitFnFast, swapElec0Bits_high _ _ _ (by dsimp only; omega)]
    dsimp only [coinBarrelIdxFast, e]
    rw [hs1, hs2, hc2z]
    by_cases hc1 : γ (iSlot1 80) = 1
    · rw [ite_eq_left hc1, ite_eq_left hc1]
    · rw [ite_eq_right hc1, ite_eq_right hc1, ite_eq_left rfl, ite_eq_left (rfl : (0 : ZMod 2) = 0)]
      have hfn : (fun j : Fin 8 ↦ δ ⟨3968 + j.val, _⟩) =
          (fun j : Fin 8 ↦ γ ⟨3968 + j.val, _⟩) := funext hu8
      simp only [hfn]
  change swapElec0Bits (coinBarrelIdxFast (le_refl 80) δ) δ = swapCore3967Fn γ
  rw [hIdxEq]
  funext w
  by_cases hw : 3924 ≤ w.val
  · rw [swapElec0Bits_high e δ w hw]
    dsimp only [δ, swapCore3967Fn, coinBarrelBitFnFast]
    exact swapElec0Bits_high e γ (Equiv.swap wCore3967 wCore4029 w) (by
      by_cases h1 : w = wCore3967
      · subst h1; rw [Equiv.swap_apply_left, wCore4029_val_assoc]; omega
      · by_cases h2 : w = wCore4029
        · subst h2; rw [Equiv.swap_apply_right, wCore3967_val_assoc]; omega
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hw)
  · have hw : w.val < 3924 := Nat.lt_of_not_ge hw
    have he218 : e.val < 218 := by
      have := e.isLt; dsimp [SpecsAux.SpecMirror.numElectrons] at this; omega
    have hfc4034 := fullSysCoreWires80_eq_4034_assoc
    have hSameSwap : swapElec0Bits e δ w = swapElec0Bits e (coinBarrelBitFnFast (le_refl 80) γ) w :=
      by
      unfold swapElec0Bits
      by_cases he0 : e.val = 0
      · rw [ite_eq_left he0, ite_eq_left he0]
        exact hSwNe w (by omega) (by omega) _
      · rw [ite_eq_right he0, ite_eq_right he0]
        by_cases hw18 : w.val < 18
        · rw [dite_eq_left hw18, dite_eq_left hw18]
          exact hSwNe _ (by dsimp only; omega) (by dsimp only; omega) _
        · rw [dite_eq_right hw18, dite_eq_right hw18]
          by_cases hwe : 18 * e.val ≤ w.val ∧ w.val < 18 * e.val + 18
          · rw [dite_eq_left hwe, dite_eq_left hwe]
            exact hSwNe _ (by dsimp only; omega) (by dsimp only; omega) _
          · rw [dite_eq_right hwe, dite_eq_right hwe]
            exact hSwNe w (by omega) (by omega) _
    rw[hSameSwap, coinBarrelBitFnFast, swapElec0Bits_self, hSwNe w (by omega) (by omega) γ]
open Classical in
theorem Bar_AAZ_comm_Pc2_AAZ (b : Fin 2) : (selAAZ_AA.embedUnitary uBarrelFastAct).1 * Pc2_AAZ
    b = Pc2_AAZ b * (selAAZ_AA.embedUnitary uBarrelFastAct).1 := by
  have hBar0 : (uBarrelFast (le_refl 80)).1 * slotBitProj (iSlot2 80) b =
      slotBitProj (iSlot2 80) b * (uBarrelFast (le_refl 80)).1 :=
    uBarrelFast_comm_high_wire (le_refl 80) (iSlot2 80) (by rw [iSlot2_80_val_assoc]; omega) b
  dsimp only [uBarrelFastAct, Pc2_AAZ, selAAZ_Data]
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_compose selAAZ_AA, QRegister.compose_assoc,
      ← QRegister.embedMatrix_mul, hBar0, QRegister.embedMatrix_mul]
open Classical in
theorem S0_AAZ_comm_Pc2_AAZ (b : Fin 2) : (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 * Pc2_AAZ
    b = Pc2_AAZ b * (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 := by
  have hSubst : (selSubstSlot0 rSlot0InFull).embedMatrix (rCoreFull.embedMatrix (slotBitProj (iSlot2
    80) b)) =
      (selDataInAct kFull80).embedMatrix (rCoreFull.embedMatrix (slotBitProj (iSlot2 80) b)) := by
    rw [embedMatrix_slotBitProj_part4, embedMatrix_slotBitProj_part4,
        embedMatrix_slotBitProj_part4]
    refine slotBitProj_congr_wire_part4 ?_ b
    rw [selSubstSlot0]
    exact rDataSubstSlot0_apply_of_not_mem _ _ _ _ (fun ⟨q, hq⟩ ↦ by
      have hv := congrArg Fin.val (rCoreFull.wires.injective hq)
      have := q.isLt
      rw [rSlot0InCore, rFullSysElecSlot_val] at hv
      simp at hv; omega)
  have hConj : (selSubstSlot0 rSlot0InFull).embedMatrix (rCoreFull.embedMatrix (slotBitProj (iSlot2
    80) b)) =
      uSlot0MeasSwap.1 *
        (selDataInAct kFull80).embedMatrix (rCoreFull.embedMatrix (slotBitProj (iSlot2 80) b)) *
        uSlot0MeasSwap.1 :=
    embedMatrix_selSubstSlot0_eq rSlot0InFull (rCoreFull.embedMatrix (slotBitProj (iSlot2 80) b))
  rw [hSubst] at hConj
  have hEmb := congrArg selAAZ_AA.embedMatrix hConj
  rw[QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose] at hEmb
  have hSq : (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 *
      (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 = 1 := by
    rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uSlot0MeasSwap_mul_self,
        QRegister.embedUnitary_one, OneMemClass.coe_one]
  change (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 *
      (selAAZ_Data.compose rCoreFull).embedMatrix (slotBitProj (iSlot2 80) b) = _
  calc (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 *
          (selAAZ_Data.compose rCoreFull).embedMatrix (slotBitProj (iSlot2 80) b)
      = ((selAAZ_AA.embedUnitary uSlot0MeasSwap).1 *
          (selAAZ_Data.compose rCoreFull).embedMatrix (slotBitProj (iSlot2 80) b) *
          (selAAZ_AA.embedUnitary uSlot0MeasSwap).1) *
          (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 := by
          rw [Matrix.mul_assoc _ _ (selAAZ_AA.embedUnitary uSlot0MeasSwap).1, hSq, Matrix.mul_one]
    _ = Pc2_AAZ b * (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 := by rw [← hEmb]; rfl
theorem F_AAZ_comm_Pc2_AAZ (b : Fin 2) : F_AAZ.1 * Pc2_AAZ b = Pc2_AAZ b * F_AAZ.1 ∧
    Finv_AAZ.1 * Pc2_AAZ b = Pc2_AAZ b * Finv_AAZ.1 := by
  have hBar := Bar_AAZ_comm_Pc2_AAZ b
  have hS0 := S0_AAZ_comm_Pc2_AAZ b
  refine ⟨?_, ?_⟩
  · dsimp only [F_AAZ]
    rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, Matrix.mul_assoc, hS0,
        ← Matrix.mul_assoc, hBar, Matrix.mul_assoc]
  · dsimp only [Finv_AAZ]
    rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, Matrix.mul_assoc, hBar,
        ← Matrix.mul_assoc, hS0, Matrix.mul_assoc]
open Classical in
theorem Finv_mul_uSw_mul_F_on_Pc20 :
    (Finv_AAZ * uSw_AAZ * F_AAZ).1 * Pc2_AAZ 0 = uSw_AAZ.1 * Pc2_AAZ 0 := by
  have hS0CommSw : (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 * uSw_AAZ.1 =
      uSw_AAZ.1 * (selAAZ_AA.embedUnitary uSlot0MeasSwap).1 := by
    have hComm0 : CommutesWithReg rSlot0InCore uSwapCore3967.1 := by
      have hn1 : ∀ q : Fin 18, rSlot0InCore q ≠ wCore3967 := fun q h ↦ by
        have hv := congrArg Fin.val h; have := q.isLt
        rw [rSlot0InCore, rFullSysElecSlot_val, wCore3967_val_assoc] at hv; simp at hv; omega
      have hn2 : ∀ q : Fin 18, rSlot0InCore q ≠ wCore4029 := fun q h ↦ by
        have hv := congrArg Fin.val h; have := q.isLt
        rw [rSlot0InCore, rFullSysElecSlot_val, wCore4029_val_assoc] at hv; simp at hv; omega
      refine commutesWithReg_of_mulVec_ket_assoc rSlot0InCore uSwapCore3967.1
        (fun _ ↦ 1) swapCore3967Fn (fun β ↦ by
          rw [one_smul]; exact uSwapCore3967_mulVec_ket_part4 β)
        (fun _ _ ↦ rfl) (fun β u ↦ ?_)
        (fun β q ↦ by unfold swapCore3967Fn; rw [Equiv.swap_apply_of_ne_of_ne (hn1 q) (hn2 q)])
      funext w; unfold swapCore3967Fn
      by_cases hw : w ∈ Set.range rSlot0InCore.wires
      · obtain ⟨q, rfl⟩ := hw
        rw [Equiv.swap_apply_of_ne_of_ne (hn1 q) (hn2 q), writeReg_apply_reg, writeReg_apply_reg]
      · have hnSw : Equiv.swap wCore3967 wCore4029 w ∉ Set.range rSlot0InCore.wires := by
          rintro ⟨q, hq⟩
          have hq' := congrArg (Equiv.swap wCore3967 wCore4029) hq
          rw [Equiv.swap_apply_of_ne_of_ne (hn1 q) (hn2 q), Equiv.swap_apply_self] at hq'
          exact hw ⟨q, hq'⟩
        rw [writeReg_apply_of_not_mem _ _ _ _ hw, writeReg_apply_of_not_mem _ _ _ _ hnSw]
    have hCommFull : CommutesWithReg rSlot0InFull (rCoreFull.embedUnitary uSwapCore3967).1 :=
      commutesWithReg_compose_assoc rfl hComm0
    have hConj0 : uSlot0MeasSwap *
      (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary uSwapCore3967) *
        uSlot0MeasSwap =
          (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary uSwapCore3967) :=
      uLensSwap_L_slot0Of_conj_eq_self_of_comm rSlot0InFull
        (rCoreFull.embedUnitary uSwapCore3967) hCommFull
    have hConj := congrArg selAAZ_AA.embedUnitary hConj0
    have hSwEmb : selAAZ_AA.embedUnitary ((selDataInAct kFull80).embedUnitary
        (rCoreFull.embedUnitary uSwapCore3967)) = uSw_AAZ := by
      rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
        QRegister.compose_assoc]
      rfl
    simp only [QRegister.embedUnitary_mul, hSwEmb] at hConj
    have hSq : selAAZ_AA.embedUnitary uSlot0MeasSwap * selAAZ_AA.embedUnitary uSlot0MeasSwap = 1 :=
      by
      rw [← QRegister.embedUnitary_mul, uSlot0MeasSwap_mul_self, QRegister.embedUnitary_one]
    exact unitary_comm_val_of_inv_conj (selAAZ_AA.embedUnitary uSlot0MeasSwap) uSw_AAZ hSq hConj
  let S0 := (selAAZ_AA.embedUnitary uSlot0MeasSwap).1
  let Bar := (selAAZ_AA.embedUnitary uBarrelFastAct).1
  have hS0Sq : S0 * S0 = 1 := by
    dsimp only [S0]
    rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uSlot0MeasSwap_mul_self,
        QRegister.embedUnitary_one, OneMemClass.coe_one]
  have hBarConj0 : (Bar * uSw_AAZ.1 * Bar) * Pc2_AAZ 0 = uSw_AAZ.1 * Pc2_AAZ 0 := by
    have hBarEmb : Bar = (selAAZ_Data.compose rCoreFull).embedMatrix (uBarrelFast (le_refl 80)).1 :=
      by
      dsimp only [Bar, uBarrelFastAct, selAAZ_Data]
      rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
          ← QRegister.embedMatrix_compose, QRegister.compose_assoc]
    rw [hBarEmb]
    unfold uSw_AAZ Pc2_AAZ
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul,
        ← QRegister.embedMatrix_mul, uBarrelFast80_conj_uSwapCore3967_mul_slot2Zero,
        QRegister.embedMatrix_mul]
  have hFinv : Finv_AAZ.1 = S0 * Bar := by
    dsimp only [Finv_AAZ, S0, Bar]; rw [QRegister.embedUnitary_mul, Submonoid.coe_mul]
  have hF : F_AAZ.1 = Bar * S0 := by
    dsimp only [F_AAZ, S0, Bar]; rw [QRegister.embedUnitary_mul, Submonoid.coe_mul]
  have hS0Pc2 : S0 * Pc2_AAZ 0 = Pc2_AAZ 0 * S0 := S0_AAZ_comm_Pc2_AAZ 0
  have hS0Sw : S0 * uSw_AAZ.1 = uSw_AAZ.1 * S0 := hS0CommSw
  change (Finv_AAZ.1 * uSw_AAZ.1 * F_AAZ.1) * Pc2_AAZ 0 = _
  rw [hFinv, hF]
  calc ((S0 * Bar) * uSw_AAZ.1 * (Bar * S0)) * Pc2_AAZ 0
      = S0 * ((Bar * uSw_AAZ.1 * Bar) * (S0 * Pc2_AAZ 0)) := by simp only [Matrix.mul_assoc]
    _ = S0 * (((Bar * uSw_AAZ.1 * Bar) * Pc2_AAZ 0) * S0) := by
          rw [hS0Pc2]; simp only [Matrix.mul_assoc]
    _ = (S0 * uSw_AAZ.1) * (Pc2_AAZ 0 * S0) := by
          rw [hBarConj0]; simp only [Matrix.mul_assoc]
    _ = uSw_AAZ.1 * ((S0 * S0) * Pc2_AAZ 0) := by
          rw [hS0Sw, ← hS0Pc2]; simp only [Matrix.mul_assoc]
    _ = uSw_AAZ.1 * Pc2_AAZ 0 := by rw [hS0Sq, Matrix.one_mul]
theorem uSw_AAZ_mul_self : uSw_AAZ * uSw_AAZ = 1 := by
  unfold uSw_AAZ
  rw[← QRegister.embedUnitary_mul, uSwapCore3967_mul_self, QRegister.embedUnitary_one]
theorem uXorSubst_AAZ_mul_self : uXorSubst_AAZ * uXorSubst_AAZ = 1 := by
  unfold uXorSubst_AAZ
  rw [← QRegister.embedUnitary_mul, uXorZTarget18_mul_self, QRegister.embedUnitary_one]
theorem rCSFull80_compose_rCoreInCoreSum42_eq :
    rCSFull80.compose (rCoreInCoreSum42 80) = rCoreFull := by
  apply qreg_ext; intro i
  have hi : rCoreInCoreSum42 80 i = Fin.castAdd 42 i :=
    Fin.ext (by simp [rCoreInCoreSum42])
  rw [QRegister.compose_apply, hi]; dsimp only [rCSFull80]; rw [QRegister.concat_apply_left]
open Classical in
theorem uCSDiag_comm_AAZ (f : Fin (2 ^ (fullSysCoreWires 80 + 42)) → ℂ) :
    let D := (selAAZ_Data.compose rCSFull80).embedMatrix (Matrix.diagonal f)
    uPhi217_AAZ.1 * D = D * uPhi217_AAZ.1 ∧
    (uPhi217_AAZ⁻¹).1 * D = D * (uPhi217_AAZ⁻¹).1 ∧
    uXorData_AAZ.1 * D = D * uXorData_AAZ.1 ∧
    uPhiAnc_AAZ.1 * D = D * uPhiAnc_AAZ.1 ∧
    (uPhiAnc_AAZ⁻¹).1 * D = D * (uPhiAnc_AAZ⁻¹).1 ∧
    uXorSubst_AAZ.1 * D = D * uXorSubst_AAZ.1 := by
  intro D
  obtain ⟨hHeld, hCS, _, hPZ⟩ := selAAZ_ActStageAZ_compositions
  obtain ⟨hPhi0, hPhiI0, hXor0⟩ := uPhiFull_and_uXorFull_comm_selCoreSum42_diagonal_ass f
  have hDEq : selAAZ_ActStageAZ.embedMatrix (selCoreSum42InFull.embedMatrix (Matrix.diagonal f)) =
    D := by
    rw [← QRegister.embedMatrix_compose, hCS]
  have hPhiEq : selAAZ_ActStageAZ.embedUnitary (selHeldZ18ActInFull.embedUnitary uPhiHeldZ18Cat) =
      uPhi217_AAZ := by
    rw [← QRegister.embedUnitary_compose, hHeld]; rfl
  have hXorEq : selAAZ_ActStageAZ.embedUnitary (selPosCoreZ18InFull.embedUnitary uXorZTarget18) =
      uXorData_AAZ := by
    rw [← QRegister.embedUnitary_compose, hPZ]; rfl
  have hPhi : uPhi217_AAZ.1 * D = D * uPhi217_AAZ.1 := by
    have h := congrArg selAAZ_ActStageAZ.embedMatrix hPhi0
    simpa only [QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val, hPhiEq, hDEq] using h
  have hPhiI : (uPhi217_AAZ⁻¹).1 * D = D * (uPhi217_AAZ⁻¹).1 := by
    have h := congrArg selAAZ_ActStageAZ.embedMatrix hPhiI0
    simpa only [QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val,
      QRegister.embedUnitary_inv, hPhiEq, hDEq] using h
  have hXorD : uXorData_AAZ.1 * D = D * uXorData_AAZ.1 := by
    have h := congrArg selAAZ_ActStageAZ.embedMatrix hXor0
    simpa only [QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val, hXorEq, hDEq] using h
  let uPE_Held := selAAZ_HeldAct.embedUnitary (selSlot0InHeldZ18Act.embedUnitary uPointElec18)
  have hPE : uPE_Held.1 * D = D * uPE_Held.1 := by
    dsimp only [uPE_Held, D, uPointElec18]
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
        embedMatrix_diagonal_local, embedMatrix_diagonal_local, embedMatrix_diagonal_local]
    exact diagonal_comm_op_assoc _ _
  have hPEI : (uPE_Held⁻¹).1 * D = D * (uPE_Held⁻¹).1 :=
    unitary_val_inv_comm_of_comm uPE_Held hPE
  have hAncDef : uPhiAnc_AAZ = uPE_Held * uPhi217_AAZ := by
    unfold uPhiAnc_AAZ uPhiHeldZ18AnchorCat uPE_Held uPhi217_AAZ
    rw [QRegister.embedUnitary_mul]
  have hPhiAnc : uPhiAnc_AAZ.1 * D = D * uPhiAnc_AAZ.1 := by
    rw [hAncDef, Submonoid.coe_mul, Matrix.mul_assoc, hPhi, ← Matrix.mul_assoc, hPE,
      Matrix.mul_assoc]
  have hPhiAncI : (uPhiAnc_AAZ⁻¹).1 * D = D * (uPhiAnc_AAZ⁻¹).1 := by
    rw [hAncDef, _root_.mul_inv_rev, Submonoid.coe_mul, Matrix.mul_assoc, hPEI,
        ← Matrix.mul_assoc, hPhiI, Matrix.mul_assoc]
  refine ⟨hPhi, hPhiI, hXorD, hPhiAnc, hPhiAncI, ?_⟩
  dsimp only [D]
  rw [embedMatrix_diagonal_local]
  let rC := selAAZ_Subst.compose rPosCoreInFull
  refine perm_comm_diagonal_of_octKet uXorSubst_AAZ.1 (fun β ↦ writeReg β selAAZ_Z fun k ↦ β
    (selAAZ_Z k) + basisBits 18 (headTargetPoint18 (fun i ↦ β (rC i))) k) (fun β ↦
    ket_embedUnitary_uXorZTarget18 rC selAAZ_Z (selAAZ_Subst_disj_Z.compose_left
    rPosCoreInFull) β) _ fun β ↦ ?_
  have hEx : (selAAZ_Data.compose rCSFull80).extractIndex ((basisBitsEquiv ((kFull80 + 18) +
      18)).symm (writeReg β selAAZ_Z fun k ↦ β (selAAZ_Z k) + basisBits 18 (headTargetPoint18
      (fun i ↦ β (rC i))) k)) = (selAAZ_Data.compose rCSFull80).extractIndex
      ((basisBitsEquiv ((kFull80 + 18) + 18)).symm β) := by
    refine extractIndex_eq_of_basisBits_eq_assoc _ fun j ↦ ?_
    rw [basisBits_basisBitsEquiv_symm, basisBits_basisBitsEquiv_symm]
    exact writeReg_apply_of_not_mem _ _ _ _
      (fun ⟨k, hk⟩ ↦ (selAAZ_Data_disj_Z.compose_left rCSFull80).ne j k hk.symm)
  rw [hEx]
open Classical in
noncomputable def stream42DiagFn (sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ)
    (x : Fin (2 ^ (fullSysCoreWires 80 + 42))) : ℂ :=
  let ξ := basisBits (fullSysCoreWires 80 + 42) x
  let γ : BitAssignment (fullSysCoreWires 80) :=
    fun q ↦ ξ (ForestQft117BundleNoTopBridge.rCoreInCoreSum42 80 q)
  if ∀ w : Fin 3,
      regVal (ForestQft117BundleNoTopBridge.rSum14InCoreSum42 80 w) ξ = sumFn w γ
  then (1 : ℂ) else 0
noncomputable def P218_AAZ : Operator (2 ^ ((kFull80 + 18) + 18)) :=
  (selAAZ_Data.compose rCSFull80).embedMatrix (pStream218Core 80)
noncomputable def P217_AAZ : Operator (2 ^ ((kFull80 + 18) + 18)) :=
  (selAAZ_Data.compose rCSFull80).embedMatrix (pStream217Core 80)
noncomputable def P_anc_AAZ : Operator (2 ^ ((kFull80 + 18) + 18)) :=
  selAAZ_AA.embedMatrix P_anc0
theorem P_anc_AAZ_eq_anc_proj0 : P_anc_AAZ = selAAZ_Anc.basisOutcomeProjector 0 := by
  unfold P_anc_AAZ P_anc0 selAAZ_Anc
  exact embedMatrix_basisOutcomeProjector_zero_assoc selAAZ_AA (selMeasInAct kFull80)
theorem P_anc_AAZ_mul_self : P_anc_AAZ * P_anc_AAZ = P_anc_AAZ := by
  rw [P_anc_AAZ_eq_anc_proj0]; exact basisOutcomeProjector_zero_mul_self selAAZ_Anc
open Classical in
theorem slotBitProj_conjTranspose_part4 {N : ℕ} (q : Wire N) (b : Fin 2) :
    (slotBitProj q b)ᴴ = slotBitProj q b := by
  unfold slotBitProj
  rw [Matrix.diagonal_conjTranspose]
  apply congrArg Matrix.diagonal; funext x
  dsimp only [Pi.star_apply]
  by_cases h : (basisBits N x q).val = b.val
  · rw [ite_eq_left h, star_one]
  · rw [ite_eq_right h, star_zero]
theorem Pc2_AAZ_conjTranspose (b : Fin 2) : (Pc2_AAZ b)ᴴ = Pc2_AAZ b := by
  unfold Pc2_AAZ
  rw [← QRegister.embedMatrix_conjTranspose, slotBitProj_conjTranspose_part4]
open Classical in
theorem embedUnitary_perm_mulVec_ket_part4 {N M : ℕ} (r : QRegister N M) (U : Unitary (2 ^ N))
    (f : BitAssignment N → BitAssignment N)
    (hU : ∀ γ : BitAssignment N, U.1.mulVec (ket γ) = ket (f γ)) (β : BitAssignment M) :
    (r.embedUnitary U).1.mulVec (ket β) = ket (writeReg β r (f (fun i ↦ β (r i)))) := by
  rw [QRegister.embedUnitary_val, embedMatrix_mulVec_ket]
  have hLoc : basisBits N (localIdx r β) = fun i ↦ β (r i) := basisBits_basisBitsEquiv_symm _
  have hCoeff : ∀ c : Fin (2 ^ N), U.1 c (localIdx r β) = if c = (basisBitsEquiv N).symm
      (f (fun i ↦ β (r i))) then 1 else 0 := by
    intro c
    rw [mulVec_ket_apply_assoc U.1 c (localIdx r β), hLoc, hU, ket_apply_eq_ite_assoc]
  simp only [hCoeff, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), basisBits_basisBitsEquiv_symm]
theorem unitary_fix_herm_imp_comm {k : ℕ} (U : Unitary (2 ^ k)) {P : Operator (2 ^ k)}
    (hPH : Pᴴ = P) (hFix : U.1 * P = P) : (U⁻¹).1 * P = P ∧ U.1 * P = P * U.1 := by
  have hInv : (U⁻¹).1 * P = P := by
    calc (U⁻¹).1 * P = (U⁻¹).1 * (U.1 * P) := by rw [hFix]
      _ = (U⁻¹ * U).1 * P := by simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = P := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  have hUU : U.1ᴴ * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hAdj : U.1ᴴ * P = P := by
    calc U.1ᴴ * P = U.1ᴴ * (U.1 * P) := by rw [hFix]
      _ = (U.1ᴴ * U.1) * P := by rw [Matrix.mul_assoc]
      _ = P := by rw [hUU, Matrix.one_mul]
  have hRight : P * U.1 = P := by
    have h := congrArg (·ᴴ) hAdj
    rwa [Matrix.conjTranspose_mul, hPH, Matrix.conjTranspose_conjTranspose] at h
  exact ⟨hInv, hFix.trans hRight.symm⟩
open Classical in
theorem uSw_AAZ_comm_Pc2_and_streams :
    (∀ b : Fin 2, uSw_AAZ.1 * Pc2_AAZ b = Pc2_AAZ b * uSw_AAZ.1) ∧ uSw_AAZ.1 * P218_AAZ =
    P218_AAZ * uSw_AAZ.1 ∧ uSw_AAZ.1 * P217_AAZ = P217_AAZ * uSw_AAZ.1 := by
  have hPc2 : ∀ b : Fin 2, uSw_AAZ.1 * Pc2_AAZ b = Pc2_AAZ b * uSw_AAZ.1 := fun b ↦ by
    have h0 := uSwapCore3967_comm_slotBitProj (iSlot2 80) b
      (fun h ↦ by
        have hv := congrArg Fin.val h; rw [iSlot2_80_val_assoc, wCore3967_val_assoc] at hv; omega)
      (fun h ↦ by
        have hv := congrArg Fin.val h; rw [iSlot2_80_val_assoc, wCore4029_val_assoc] at hv; omega)
    unfold uSw_AAZ Pc2_AAZ
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, h0, QRegister.embedMatrix_mul]
  have hSwStream : ∀ (sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ),
      (∀ (w : Fin 3) (γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)),
        (∀ u : Wire (fullSysCoreWires 80), u.val < 3924 → γ₁ u = γ₂ u) → sumFn w γ₁ = sumFn w γ₂) →
      ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1 *
        pStream42Of (mPayload := 80) sumFn =
      pStream42Of (mPayload := 80) sumFn *
        ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1 := by
    intro sumFn hLow
    let rC := rCoreInCoreSum42 80
    have hn3967 : ∀ u : Wire (fullSysCoreWires 80), u.val < 3924 → u ≠ wCore3967 ∧ u ≠ wCore4029 :=
      fun u hu ↦ ⟨fun h ↦ by subst h; rw [wCore3967_val_assoc] at hu; omega,
                   fun h ↦ by subst h; rw [wCore4029_val_assoc] at hu; omega⟩
    have hKetSw : ∀ β : BitAssignment (fullSysCoreWires 80 + 42),
        ((rC.embedUnitary uSwapCore3967).1).mulVec (ket β) =
          ket (writeReg β rC (swapCore3967Fn (fun i ↦ β (rC i)))) :=
      embedUnitary_perm_mulVec_ket_part4 rC uSwapCore3967 swapCore3967Fn
        uSwapCore3967_mulVec_ket_part4
    unfold pStream42Of
    refine perm_comm_diagonal_of_octKet (rC.embedUnitary uSwapCore3967).1
      (fun β ↦ writeReg β rC (swapCore3967Fn (fun i ↦ β (rC i)))) hKetSw _ fun β ↦ ?_
    let β' := writeReg β rC (swapCore3967Fn (fun i ↦ β (rC i)))
    have hβ : basisBits (fullSysCoreWires 80 + 42) ((basisBitsEquiv _).symm β) = β :=
      basisBits_basisBitsEquiv_symm β
    have hβ' : basisBits (fullSysCoreWires 80 + 42) ((basisBitsEquiv _).symm β') = β' :=
      basisBits_basisBitsEquiv_symm β'
    have hHigh : ∀ (w : Fin 3),
        regVal (rSum14InCoreSum42 80 w) β' =
          regVal (rSum14InCoreSum42 80 w) β := fun w ↦ by
      unfold regVal bitsVal
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      have hn : rSum14InCoreSum42 80 w r ∉ Set.range rC.wires := by
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val hi; have := i.isLt
        simp only [rC, rCoreInCoreSum42, rSum14InCoreSum42, QRegister.block_apply_val] at hv
        omega
      dsimp only [β']
      rw [writeReg_apply_of_not_mem _ _ _ _ hn]
    have hLowEq : ∀ w : Fin 3, sumFn w (fun u ↦ β' (rCoreInCoreSum42 80 u)) = sumFn w
        (fun u ↦ β (rCoreInCoreSum42 80 u)) :=
      fun w ↦ hLow w _ _ fun u hu ↦ by
        dsimp only [β', rC]
        rw [writeReg_apply_reg]
        unfold swapCore3967Fn
        rw [Equiv.swap_apply_of_ne_of_ne (hn3967 u hu).1 (hn3967 u hu).2]
    have hrC03i : ForestQft117BundleNoTopBridge.rCoreInCoreSum42 80 =
        rCoreInCoreSum42 80 := rfl
    have hrS03i : ForestQft117BundleNoTopBridge.rSum14InCoreSum42 80 =
        rSum14InCoreSum42 80 := rfl
    dsimp only
    rw [hβ, hβ']
    simp only [hrC03i, hrS03i, hHigh, hLowEq]
  have hLow218 : ∀ (w : Fin 3) (γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)),
      (∀ u : Wire (fullSysCoreWires 80), u.val < 3924 → γ₁ u = γ₂ u) →
        slot2AxisSum w γ₁ = slot2AxisSum w γ₂ := fun w γ₁ γ₂ h ↦ by
    unfold slot2AxisSum
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    dsimp only
    rw [h _ (by have he : e.val < 218 := by
                  have := e.isLt; dsimp [SpecsAux.SpecMirror.numElectrons] at this; omega
                have := w.isLt; have := r.isLt
                simp [rElecSlotAxis, QRegExt.idReg,
                  SpecsAux.SpecMirror.numElectrons]; omega)]
  have hLow217 : ∀ (w : Fin 3) (γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)),
      (∀ u : Wire (fullSysCoreWires 80), u.val < 3924 → γ₁ u = γ₂ u) →
        spectatorSum217 w γ₁ = spectatorSum217 w γ₂ := fun w γ₁ γ₂ h ↦ by
    unfold spectatorSum217
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    dsimp only
    rw [h _ (by have := e.isLt; have := w.isLt; have := r.isLt
                simp [rElecSlotAxis, QRegExt.idReg,
                  SpecsAux.SpecMirror.numElectrons]; omega)]
  have hSwEq : uSw_AAZ =
      (selAAZ_Data.compose rCSFull80).embedUnitary ((rCoreInCoreSum42 80).embedUnitary
        uSwapCore3967) := by
    rw [← QRegister.embedUnitary_compose, QRegister.compose_assoc,
      rCSFull80_compose_rCoreInCoreSum42_eq]
    rfl
  refine ⟨hPc2, ?_, ?_⟩
  · rw [hSwEq]; unfold P218_AAZ pStream218Core
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hSwStream slot2AxisSum hLow218,
        QRegister.embedMatrix_mul]
  · rw [hSwEq]; unfold P217_AAZ pStream217Core
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hSwStream spectatorSum217 hLow217,
        QRegister.embedMatrix_mul]
open Classical in
theorem uHeadData_and_Anc_Pc2 : uHeadData_AAZ.1 * Pc2_AAZ 1 = Pc2_AAZ 1 ∧ uHeadData_AAZ.1 *
    Pc2_AAZ 0 = Pc2_AAZ 0 * uHeadData_AAZ.1 ∧ uHeadAnc_AAZ.1 * Pc2_AAZ 1 = Pc2_AAZ 1 := by
  let w2Pos := wSlot2Core (QRegExt.ofFin posCoreWires)
  let rSingPos : QRegister 1 posCoreWires := QRegister.singleton w2Pos
  have hMidFix : uHeadPhaseMod4Origin0Repaired.1 * slotBitProj w2Pos 1 = slotBitProj w2Pos 1 := by
    unfold slotBitProj uHeadPhaseMod4Origin0Repaired
    refine monomialZ8UnitaryN_mul_diagonal_eq_self_assoc _ _ _ _ fun x hfx ↦ ?_
    let β := basisBits posCoreWires x
    have h1 : β w2Pos = 1 := by
      change (if (β w2Pos).val = (1 : Fin 2).val then (1 : ℂ) else 0) ≠ 0 at hfx
      generalize hbw : β w2Pos = bw at hfx ⊢
      fin_cases bw
      · exfalso; exact hfx rfl
      · rfl
    have hb1 : (β w2Pos == 0) = false := by rw [h1]; decide
    have hEn : headEnBoolSpec β = false := by
      unfold headEnBoolSpec; dsimp only
      dsimp only [w2Pos] at hb1
      rw [hb1]; simp
    have hEnU : headEnBoolSpec
        (Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) 0) = false := by
      have hwNe : w2Pos ≠ wHeadThresh (QRegExt.ofFin posCoreWires) := fun h ↦ by
        have hv := congrArg Fin.val h
        rw [wSlot2Core_ofFin_val_assoc, wHeadThresh_ofFin_val_assoc] at hv; omega
      unfold headEnBoolSpec; dsimp only
      dsimp only [w2Pos] at hwNe hb1
      rw [Function.update_of_ne hwNe, hb1]; simp
    refine ⟨?_, hEnU⟩
    unfold headPhaseMod4Origin0RepairedZ8Spec
    rw [hEn]; rfl
  have hSingProj : slotBitProj w2Pos 1 = rSingPos.embedMatrix (slotBitProj ⟨0, by decide⟩ 1) :=
    (embedMatrix_slotBitProj_part4 rSingPos ⟨0, by decide⟩ 1).symm
  have hHadComm : uHad217.1 * slotBitProj w2Pos 1 = slotBitProj w2Pos 1 * uHad217.1 := by
    rw [hSingProj]
    exact commutesWithReg_elecProd217_of_ge3924_assoc rSingPos
      (fun t ↦ by
        have ht : rSingPos t = w2Pos := rfl
        rw [ht, wSlot2Core_ofFin_val_assoc]; omega)
      (fun _ ↦ uHadamard18) _
  have hCoreFix : uHeadConjHCore.1 * slotBitProj w2Pos 1 = slotBitProj w2Pos 1 := by
    have h0 := conj_fix_of_comm_assoc uHad217⁻¹ uHeadPhaseMod4Origin0Repaired
      (unitary_val_inv_comm_of_comm uHad217 hHadComm) hMidFix
    simpa -zeta -zetaDelta only [uHeadConjHCore, inv_inv, unitary_coe_mul_assoc,
      op_mul_assoc_assoc] using h0
  have hPosEmbed : selPosCoreInCore80.embedMatrix (slotBitProj w2Pos 1) =
    slotBitProj (iSlot2 80) 1 := by
    rw [embedMatrix_slotBitProj_part4]
    exact slotBitProj_congr_wire_part4 (Fin.ext (by
      rw [iSlot2_80_val_assoc]
      simp [selPosCoreInCore80, w2Pos, wSlot2Core_ofFin_val_assoc])) 1
  have hPc2Pos : Pc2_AAZ 1 =
    (selAAZ_Data.compose rPosCoreInFull).embedMatrix (slotBitProj w2Pos 1) := by
    dsimp only [Pc2_AAZ, rPosCoreInFull]
    rw [← hPosEmbed, ← QRegister.embedMatrix_compose, QRegister.compose_assoc]
  have hDataFix : uHeadData_AAZ.1 * Pc2_AAZ 1 = Pc2_AAZ 1 := by
    rw [hPc2Pos]; unfold uHeadData_AAZ
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hCoreFix]
  have hDataComm1 := (unitary_fix_herm_imp_comm uHeadData_AAZ (Pc2_AAZ_conjTranspose 1) hDataFix).2
  have hDataComm0 : uHeadData_AAZ.1 * Pc2_AAZ 0 = Pc2_AAZ 0 * uHeadData_AAZ.1 := by
    have h0eq : Pc2_AAZ 0 = 1 - Pc2_AAZ 1 := eq_sub_of_add_eq Pc2_AAZ_zero_add_one
    rw [h0eq, mul_sub, mul_one, sub_mul, one_mul, hDataComm1]
  have hAncFix : uHeadAnc_AAZ.1 * Pc2_AAZ 1 = Pc2_AAZ 1 := by
    have hUnf := uHeadAnc_AAZ_eq_F_conj
    calc uHeadAnc_AAZ.1 * Pc2_AAZ 1
        = F_AAZ.1 * (uHeadData_AAZ.1 * (Finv_AAZ.1 * Pc2_AAZ 1)) := by
            rw [hUnf]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = F_AAZ.1 * ((uHeadData_AAZ.1 * Pc2_AAZ 1) * Finv_AAZ.1) := by
            rw [(F_AAZ_comm_Pc2_AAZ 1).2, ← Matrix.mul_assoc uHeadData_AAZ.1]
      _ = Pc2_AAZ 1 * (F_AAZ.1 * Finv_AAZ.1) := by
            rw [hDataFix, ← Matrix.mul_assoc, (F_AAZ_comm_Pc2_AAZ 1).1, Matrix.mul_assoc]
      _ = Pc2_AAZ 1 := by
            rw [← Submonoid.coe_mul, F_AAZ_mul_Finv_AAZ.1, OneMemClass.coe_one, Matrix.mul_one]
  exact ⟨hDataFix, hDataComm0, hAncFix⟩
theorem rCoreInCoreSum42_iSlot2_val : (rCoreInCoreSum42 80 (iSlot2 80)).val = 3950 := by
  simp [rCoreInCoreSum42, QRegister.block, iSlot2_80_val_assoc]
theorem uStr217_AAZ_comm_Pc2 (b : Fin 2) : uStr217_AAZ.1 * Pc2_AAZ b = Pc2_AAZ b *
    uStr217_AAZ.1 ∧ (uStr217_AAZ⁻¹).1 * Pc2_AAZ b = Pc2_AAZ b * (uStr217_AAZ⁻¹).1 := by
  let rSingCS : QRegister 1 (fullSysCoreWires 80 + 42) :=
    QRegister.singleton (rCoreInCoreSum42 80 (iSlot2 80))
  have hCSProj : (rCoreInCoreSum42 80).embedMatrix (slotBitProj (iSlot2 80) b) =
      rSingCS.embedMatrix (slotBitProj ⟨0, by decide⟩ b) :=
    embedMatrix_slotBitProj_eq_singleton_part4 (rCoreInCoreSum42 80) (iSlot2 80) b
  have hCommCS : (uStr3AxisOfSpec uStream217Spec131).1 * (rCoreInCoreSum42 80).embedMatrix
      (slotBitProj (iSlot2 80) b) = (rCoreInCoreSum42 80).embedMatrix
      (slotBitProj (iSlot2 80) b) * (uStr3AxisOfSpec uStream217Spec131).1 := by
    rw [hCSProj]
    exact commutesWithReg_uStr3Axis_of_ge3924_assoc rSingCS
      (fun t ↦ by
        change 3924 ≤ (rCoreInCoreSum42 80 (iSlot2 80)).val
        rw [rCoreInCoreSum42_iSlot2_val]; decide)
      (fun t ↦ by
        change (rCoreInCoreSum42 80 (iSlot2 80)).val < fullSysCoreWires 80
        rw [rCoreInCoreSum42_iSlot2_val, fullSysCoreWires80_eq_4034_assoc]; decide)
      uStream217Spec131 _
  have hPc2CS : Pc2_AAZ b = (selAAZ_Data.compose rCSFull80).embedMatrix
      ((rCoreInCoreSum42 80).embedMatrix (slotBitProj (iSlot2 80) b)) := by
    unfold Pc2_AAZ
    rw [← QRegister.embedMatrix_compose,
        QRegister.compose_assoc selAAZ_Data rCSFull80 (rCoreInCoreSum42 80),
        rCSFull80_compose_rCoreInCoreSum42_eq]
  have hFwd : uStr217_AAZ.1 * Pc2_AAZ b = Pc2_AAZ b * uStr217_AAZ.1 := by
    rw [hPc2CS]; unfold uStr217_AAZ
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hCommCS, QRegister.embedMatrix_mul]
  exact ⟨hFwd, unitary_val_inv_comm_of_comm uStr217_AAZ hFwd⟩
theorem Pc2_AAZ_eq_rCS_diagonal (b : Fin 2) :
    ∃ f, Pc2_AAZ b = (selAAZ_Data.compose rCSFull80).embedMatrix (Matrix.diagonal f) := by
  have hPc2CS : Pc2_AAZ b = (selAAZ_Data.compose rCSFull80).embedMatrix
      ((rCoreInCoreSum42 80).embedMatrix (slotBitProj (iSlot2 80) b)) := by
    unfold Pc2_AAZ
    rw [← QRegister.embedMatrix_compose,
        QRegister.compose_assoc selAAZ_Data rCSFull80 (rCoreInCoreSum42 80),
        rCSFull80_compose_rCoreInCoreSum42_eq]
  rw [hPc2CS]; unfold slotBitProj
  exact ⟨_, congrArg (selAAZ_Data.compose rCSFull80).embedMatrix (embedMatrix_diagonal_local _ _)⟩
theorem uData9_AAZ_fix_Pc21 : uData9_AAZ.1 * Pc2_AAZ 1 = Pc2_AAZ 1 := by
  obtain ⟨f1, hf1⟩ := Pc2_AAZ_eq_rCS_diagonal 1
  obtain ⟨hPhi, hPhiI, hXorD, _, _, _⟩ := uCSDiag_comm_AAZ f1
  rw [← hf1] at hPhi hPhiI hXorD
  have hStr := uStr217_AAZ_comm_Pc2 1
  have hSw := uSw_AAZ_comm_Pc2_and_streams.1 1
  have hHead := uHeadData_and_Anc_Pc2.1
  have h1 := conj_fix_of_comm_assoc uStr217_AAZ _ hStr.1 hHead
  have h2 := conj_fix_of_comm_assoc uPhi217_AAZ⁻¹ _ hPhiI h1
  rw [inv_inv] at h2
  have hXorInv : uXorData_AAZ⁻¹ = uXorData_AAZ :=
    inv_eq_of_mul_eq_one_right (by
      unfold uXorData_AAZ
      rw [← QRegister.embedUnitary_mul, uXorZTarget18_mul_self, QRegister.embedUnitary_one])
  have h3 := conj_fix_of_comm_assoc uXorData_AAZ _ hXorD h2
  rw [hXorInv] at h3
  have hSwInv : uSw_AAZ⁻¹ = uSw_AAZ := inv_eq_of_mul_eq_one_right uSw_AAZ_mul_self
  have h4 := conj_fix_of_comm_assoc uSw_AAZ _ hSw h3
  rw [hSwInv] at h4
  rw [uData9_AAZ_eq_prod9]
  simpa only [Submonoid.coe_mul, Matrix.mul_assoc] using h4
noncomputable def E_init_AAZ : Operator (2 ^ ((kFull80 + 18) + 18)) :=
  selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) * selAAZ_Z.basisOutcomeProjector 0
noncomputable def E_base_AAZ : Operator (2 ^ ((kFull80 + 18) + 18)) :=
  selAAZ_Data.embedMatrix E_raw217 * P_anc_AAZ * selAAZ_Z.basisOutcomeProjector 0
theorem E_init_AAZ_eq_F_mul_E_base : E_init_AAZ = F_AAZ.1 * E_base_AAZ := by
  unfold E_init_AAZ E_base_AAZ E_anchorLoc F_AAZ P_anc_AAZ selAAZ_Data
  rw [QRegister.embedUnitary_val, selAAZ_AA.embedMatrix_mul, selAAZ_AA.embedMatrix_mul,
      ← QRegister.embedMatrix_compose]
  simp only [Matrix.mul_assoc]
open Classical in
theorem F_AAZ_InnerSwap_Finv_eq : F_AAZ * selAAZ_Data.embedUnitary uInnerSwapFull * Finv_AAZ =
    selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull) := by
  unfold F_AAZ Finv_AAZ selAAZ_Data uAnchorFrame
  rw [QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
attribute [irreducible] F_AAZ Finv_AAZ
private theorem uStr218_AAZ_steps_of_comm_CS
    (B_CS : Operator (2 ^ (fullSysCoreWires 80 + 42)))
    (hAdd : (uSlot0Sum42Add 80).1 * B_CS = B_CS * (uSlot0Sum42Add 80).1) (hStr217 :
    (uStr3AxisOfSpec uStream217Spec131).1 * B_CS = B_CS * (uStr3AxisOfSpec
    uStream217Spec131).1) (hP0 : pSum42CoreZero * B_CS = B_CS * pSum42CoreZero) :
    (uStr218_AAZ⁻¹).1 * ((selAAZ_Data.compose rCSFull80).embedMatrix B_CS *
    (selAAZ_Data.compose rCSFull80).embedMatrix eStream218Core) =
    (selAAZ_Data.compose rCSFull80).embedMatrix B_CS *
    (selAAZ_Data.compose rCSFull80).embedMatrix pSum42CoreZero ∧ uStr218_AAZ.1 *
    ((selAAZ_Data.compose rCSFull80).embedMatrix B_CS * (selAAZ_Data.compose
    rCSFull80).embedMatrix pSum42CoreZero) = (selAAZ_Data.compose rCSFull80).embedMatrix B_CS
    * (selAAZ_Data.compose rCSFull80).embedMatrix eStream218Core := by
  let rCS := selAAZ_Data.compose rCSFull80
  have hCommE218 : eStream218Core * B_CS = B_CS * eStream218Core := by
    rw [← uSlot0Sum42Add_mul_eStream217Core, ← uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core]
    calc ((uSlot0Sum42Add 80).1 * ((uStr3AxisOfSpec uStream217Spec131).1 * pSum42CoreZero)) * B_CS
        = (uSlot0Sum42Add 80).1 * ((uStr3AxisOfSpec uStream217Spec131).1 * (pSum42CoreZero *
          B_CS)) := by
            simp only [Matrix.mul_assoc]
      _ = (uSlot0Sum42Add 80).1 * (B_CS * ((uStr3AxisOfSpec uStream217Spec131).1 *
        pSum42CoreZero)) := by
            rw [hP0, ← Matrix.mul_assoc (uStr3AxisOfSpec uStream217Spec131).1, hStr217,
              Matrix.mul_assoc]
      _ = B_CS * ((uSlot0Sum42Add 80).1 * ((uStr3AxisOfSpec uStream217Spec131).1 *
        pSum42CoreZero)) := by
            rw [← Matrix.mul_assoc (uSlot0Sum42Add 80).1, hAdd, Matrix.mul_assoc]
  have hStrFwd : uStr218_3Axis.1 * (B_CS * pSum42CoreZero) = B_CS * eStream218Core := by
    rw [← hP0, ← Matrix.mul_assoc, uStr218_3Axis_mul_pSum42CoreZero_eq_eStream218Core, hCommE218]
  have hStrInv : (uStr218_3Axis⁻¹).1 * (B_CS * eStream218Core) = B_CS * pSum42CoreZero := by
    rw [← hCommE218, ← Matrix.mul_assoc, inv_uStr218_3Axis_mul_eStream218Core_eq_pSum42CoreZero,
      hP0]
  refine ⟨?_, ?_⟩
  · unfold uStr218_AAZ
    rw [← QRegister.embedUnitary_inv, QRegister.embedUnitary_val,
        ← rCS.embedMatrix_mul, ← rCS.embedMatrix_mul, hStrInv, rCS.embedMatrix_mul]
  · unfold uStr218_AAZ
    rw [QRegister.embedUnitary_val, ← rCS.embedMatrix_mul, ← rCS.embedMatrix_mul,
        hStrFwd, rCS.embedMatrix_mul]
theorem uMid3_AAZ_fix_Pc21_P218 : (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1 *
    (Pc2_AAZ 1 * P218_AAZ) = Pc2_AAZ 1 * P218_AAZ := by
  let P1_CS := (rCoreInCoreSum42 80).embedMatrix (slotBitProj (iSlot2 80) 1)
  let rSingCS : QRegister 1 (fullSysCoreWires 80 + 42) :=
    QRegister.singleton (rCoreInCoreSum42 80 (iSlot2 80))
  have hSingEq : P1_CS = rSingCS.embedMatrix (slotBitProj ⟨0, by decide⟩ 1) :=
    embedMatrix_slotBitProj_eq_singleton_part4 (rCoreInCoreSum42 80) (iSlot2 80) 1
  have hCommAdd : (uSlot0Sum42Add 80).1 * P1_CS = P1_CS * (uSlot0Sum42Add 80).1 := by
    rw [hSingEq]
    exact commutesWithReg_uSlot0Sum42Add_of_mid_assoc rSingCS
      (fun t ↦ by
        change 18 ≤ (rCoreInCoreSum42 80 (iSlot2 80)).val
        rw [rCoreInCoreSum42_iSlot2_val]; decide)
      (fun t ↦ by
        change (rCoreInCoreSum42 80 (iSlot2 80)).val < fullSysCoreWires 80
        rw [rCoreInCoreSum42_iSlot2_val, fullSysCoreWires80_eq_4034_assoc]; decide) _
  have hCommStr217 : (uStr3AxisOfSpec uStream217Spec131).1 * P1_CS =
      P1_CS * (uStr3AxisOfSpec uStream217Spec131).1 := by
    rw [hSingEq]
    exact commutesWithReg_uStr3Axis_of_ge3924_assoc rSingCS
      (fun t ↦ by
        change 3924 ≤ (rCoreInCoreSum42 80 (iSlot2 80)).val
        rw [rCoreInCoreSum42_iSlot2_val]; decide)
      (fun t ↦ by
        change (rCoreInCoreSum42 80 (iSlot2 80)).val < fullSysCoreWires 80
        rw [rCoreInCoreSum42_iSlot2_val, fullSysCoreWires80_eq_4034_assoc];
          decide) uStream217Spec131 _
  have hCommP0 : pSum42CoreZero * P1_CS = P1_CS * pSum42CoreZero := by
    dsimp only [P1_CS]; unfold pSum42CoreZero slotBitProj
    rw [QRegister.basisOutcomeProjector_eq_diagonal, embedMatrix_diagonal_local]
    exact diagonal_comm_op_assoc _ _
  let rCS := selAAZ_Data.compose rCSFull80
  have hPc2CS : Pc2_AAZ 1 = rCS.embedMatrix P1_CS := by
    dsimp only [rCS, P1_CS]
    unfold Pc2_AAZ
    rw [← QRegister.embedMatrix_compose,
        QRegister.compose_assoc selAAZ_Data rCSFull80 (rCoreInCoreSum42 80),
        rCSFull80_compose_rCoreInCoreSum42_eq]
  have hDecomp : Pc2_AAZ 1 * P218_AAZ =
      (Pc2_AAZ 1 * rCS.embedMatrix eStream218Core) * rCS.embedMatrix eStream218Coreᴴ := by
    rw [hPc2CS]
    unfold P218_AAZ
    rw [← eStream218Core_mul_conjTranspose, rCS.embedMatrix_mul, ← Matrix.mul_assoc]
  obtain ⟨hInvCS, hFwdCS⟩ := uStr218_AAZ_steps_of_comm_CS P1_CS hCommAdd hCommStr217 hCommP0
  have hInvStep : (uStr218_AAZ⁻¹).1 * (Pc2_AAZ 1 * rCS.embedMatrix eStream218Core) =
      Pc2_AAZ 1 * rCS.embedMatrix pSum42CoreZero := by
    rw [hPc2CS]
    exact hInvCS
  have hFwdStep : uStr218_AAZ.1 * (Pc2_AAZ 1 * rCS.embedMatrix pSum42CoreZero) =
      Pc2_AAZ 1 * rCS.embedMatrix eStream218Core := by
    rw [hPc2CS]
    exact hFwdCS
  rw [hDecomp]
  calc (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1 *
          ((Pc2_AAZ 1 * rCS.embedMatrix eStream218Core) * rCS.embedMatrix eStream218Coreᴴ)
      = uStr218_AAZ.1 * (uHeadAnc_AAZ.1 *
          ((uStr218_AAZ⁻¹).1 * (Pc2_AAZ 1 * rCS.embedMatrix eStream218Core))) *
          rCS.embedMatrix eStream218Coreᴴ := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (uStr218_AAZ.1 * ((uHeadAnc_AAZ.1 * Pc2_AAZ 1) * rCS.embedMatrix pSum42CoreZero)) *
          rCS.embedMatrix eStream218Coreᴴ := by
          rw [hInvStep]; simp only [Matrix.mul_assoc]
    _ = (Pc2_AAZ 1 * rCS.embedMatrix eStream218Core) * rCS.embedMatrix eStream218Coreᴴ := by
          rw [uHeadData_and_Anc_Pc2.2.2, hFwdStep]
theorem uC9_AAZ_eq_on_Pc21 : uC9_AAZ.1 * (Pc2_AAZ 1 * E_init_AAZ) =
    (F_AAZ * uData9_AAZ * Finv_AAZ).1 * (Pc2_AAZ 1 * E_init_AAZ) := by
  have hRHS : (F_AAZ * uData9_AAZ * Finv_AAZ).1 * (Pc2_AAZ 1 * E_init_AAZ) =
      Pc2_AAZ 1 * E_init_AAZ := by
    calc (F_AAZ * uData9_AAZ * Finv_AAZ).1 * (Pc2_AAZ 1 * E_init_AAZ)
        = F_AAZ.1 * ((uData9_AAZ.1 * Pc2_AAZ 1) * (Finv_AAZ.1 * E_init_AAZ)) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Finv_AAZ.1, (F_AAZ_comm_Pc2_AAZ 1).2];
              simp only [Matrix.mul_assoc]
      _ = Pc2_AAZ 1 * ((F_AAZ.1 * Finv_AAZ.1) * E_init_AAZ) := by
            rw [uData9_AAZ_fix_Pc21, ← Matrix.mul_assoc F_AAZ.1, (F_AAZ_comm_Pc2_AAZ 1).1]
            simp only [Matrix.mul_assoc]
      _ = Pc2_AAZ 1 * E_init_AAZ := by
            rw [← Submonoid.coe_mul, F_AAZ_mul_Finv_AAZ.1, OneMemClass.coe_one, Matrix.one_mul]
  rw [hRHS]
  have hP218Init : P218_AAZ * E_init_AAZ = E_init_AAZ := by
    unfold P218_AAZ E_init_AAZ selAAZ_Data
    rw [QRegister.compose_assoc, QRegister.embedMatrix_compose, ← Matrix.mul_assoc,
        ← selAAZ_AA.embedMatrix_mul, pStream218_mul_E_anchorLoc_E_raw217]
  let uPre3 := uPhiAnc_AAZ * (uXorSubst_AAZ * uSw_AAZ)
  let uPost3 := uSw_AAZ * (uXorSubst_AAZ * uPhiAnc_AAZ⁻¹)
  have hPostPre : uPost3.1 * uPre3.1 = 1 := by
    rw [← Submonoid.coe_mul]
    have h1 : uPost3 * uPre3 = 1 := by
      dsimp only [uPost3, uPre3]
      calc (uSw_AAZ * (uXorSubst_AAZ * uPhiAnc_AAZ⁻¹)) * (uPhiAnc_AAZ * (uXorSubst_AAZ * uSw_AAZ))
          = uSw_AAZ * (uXorSubst_AAZ * ((uPhiAnc_AAZ⁻¹ * uPhiAnc_AAZ) * (uXorSubst_AAZ *
            uSw_AAZ))) := by
              simp only [mul_assoc]
        _ = uSw_AAZ * ((uXorSubst_AAZ * uXorSubst_AAZ) * uSw_AAZ) := by
              rw [inv_mul_cancel, one_mul, mul_assoc]
        _ = 1 := by rw [uXorSubst_AAZ_mul_self, one_mul, uSw_AAZ_mul_self]
    rw [h1, OneMemClass.coe_one]
  obtain ⟨f1, hf1⟩ := Pc2_AAZ_eq_rCS_diagonal 1
  obtain ⟨_, _, _, hPhiAnc1, _, hXorS1⟩ := uCSDiag_comm_AAZ f1
  rw [← hf1] at hPhiAnc1 hXorS1
  have hPrePc2 : uPre3.1 * Pc2_AAZ 1 = Pc2_AAZ 1 * uPre3.1 := by
    dsimp only [uPre3]
    simp only [Submonoid.coe_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, uSw_AAZ_comm_Pc2_and_streams.1 1,
        ← Matrix.mul_assoc uXorSubst_AAZ.1, hXorS1,
        Matrix.mul_assoc (Pc2_AAZ 1), ← Matrix.mul_assoc uPhiAnc_AAZ.1, hPhiAnc1]
    simp only [Matrix.mul_assoc]
  have hPreP218 : uPre3.1 * P218_AAZ = P218_AAZ * uPre3.1 := by
    obtain ⟨_, _, _, hPhiAnc218, _, hXorS218⟩ :=
      uCSDiag_comm_AAZ (stream42DiagFn slot2AxisSum)
    change _ * P218_AAZ = P218_AAZ * _ at hPhiAnc218 hXorS218
    dsimp only [uPre3]
    simp only [Submonoid.coe_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, uSw_AAZ_comm_Pc2_and_streams.2.1,
        ← Matrix.mul_assoc uXorSubst_AAZ.1, hXorS218,
        Matrix.mul_assoc P218_AAZ, ← Matrix.mul_assoc uPhiAnc_AAZ.1, hPhiAnc218]
    simp only [Matrix.mul_assoc]
  have hC9 : uC9_AAZ.1 = uPost3.1 * ((uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1 * uPre3.1) :=
    by
    rw [uC9_AAZ_def]
    dsimp only [uPost3, uPre3]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  have hMove : uPre3.1 * (Pc2_AAZ 1 * (P218_AAZ * E_init_AAZ)) =
      (Pc2_AAZ 1 * P218_AAZ) * (uPre3.1 * E_init_AAZ) := by
    rw [← Matrix.mul_assoc uPre3.1, hPrePc2, Matrix.mul_assoc (Pc2_AAZ 1),
        ← Matrix.mul_assoc uPre3.1, hPreP218]; simp only [Matrix.mul_assoc]
  rw [hC9]
  conv_lhs => rw [← hP218Init]
  calc (uPost3.1 * ((uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1 * uPre3.1)) *
          (Pc2_AAZ 1 * (P218_AAZ * E_init_AAZ))
      = uPost3.1 * ((uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1 *
          ((Pc2_AAZ 1 * P218_AAZ) * (uPre3.1 * E_init_AAZ))) := by
          rw [Matrix.mul_assoc uPost3.1, Matrix.mul_assoc (uStr218_AAZ * _).1, hMove]
    _ = (uPost3.1 * uPre3.1) * (Pc2_AAZ 1 * (P218_AAZ * E_init_AAZ)) := by
          rw [← Matrix.mul_assoc (uStr218_AAZ * _).1, uMid3_AAZ_fix_Pc21_P218,
              ← hMove, ← Matrix.mul_assoc uPost3.1]
    _ = Pc2_AAZ 1 * E_init_AAZ := by rw [hPostPre, Matrix.one_mul, hP218Init]
private theorem embed_comm_P_anc_AAZ {k : ℕ} {r : QRegister k ((kFull80 + 18) + 18)}
    (h : r.DisjointWires selAAZ_Anc) (M : Operator (2 ^ k)) :
    r.embedMatrix M * P_anc_AAZ = P_anc_AAZ * r.embedMatrix M := by
  rw [P_anc_AAZ_eq_anc_proj0]
  exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint r) selAAZ_Anc h M 0
private theorem embedData_comm_P_anc_AAZ {k : ℕ} (r : QRegister k kFull80) (M : Operator (2 ^ k)) :
    (selAAZ_Data.compose r).embedMatrix M * P_anc_AAZ = P_anc_AAZ *
      (selAAZ_Data.compose r).embedMatrix M :=
  embed_comm_P_anc_AAZ (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right r)) M
open Classical in
theorem uC9_AAZ_eq_on_Pc20 : uC9_AAZ.1 * (Pc2_AAZ 0 * E_init_AAZ) =
    (F_AAZ * uData9_AAZ * Finv_AAZ).1 * (Pc2_AAZ 0 * E_init_AAZ) := by
  have hConjMul : ∀ A B : Unitary (2 ^ ((kFull80 + 18) + 18)),
      Finv_AAZ * (A * B) * F_AAZ = (Finv_AAZ * A * F_AAZ) * (Finv_AAZ * B * F_AAZ) := fun A B ↦ by
    calc Finv_AAZ * (A * B) * F_AAZ
        = Finv_AAZ * (A * (F_AAZ * Finv_AAZ) * B) * F_AAZ := by rw [F_AAZ_mul_Finv_AAZ.1, mul_one]
      _ = (Finv_AAZ * A * F_AAZ) * (Finv_AAZ * B * F_AAZ) := by simp only [mul_assoc]
  let cStr218 := Finv_AAZ * uStr218_AAZ * F_AAZ
  have hcStr218Inv : Finv_AAZ * uStr218_AAZ⁻¹ * F_AAZ = cStr218⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hConjMul, inv_mul_cancel, mul_one, F_AAZ_mul_Finv_AAZ.2]
  let uPE18_AAZ := selAAZ_Anc.embedUnitary uPointElec18
  let M_anc := (uXorData_AAZ * (uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹)) *
        ((cStr218 * (uHeadData_AAZ * cStr218⁻¹)) * ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ))
  let M_data := (uXorData_AAZ * uPhi217_AAZ⁻¹) *
        ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) * (uPhi217_AAZ * uXorData_AAZ))
  have hHeldDisjAnc := selAAZ_HeldAct_disj_Anc
  have hPEPhiComm : uPE18_AAZ⁻¹ * uPhi217_AAZ⁻¹ = uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹ :=
    uPE18_inv_comm_uPhi217_inv
  have hConjC9 : Finv_AAZ * uC9_AAZ * F_AAZ =
      (Finv_AAZ * uSw_AAZ * F_AAZ) * (M_anc * (Finv_AAZ * uSw_AAZ * F_AAZ)) := by
    have hPhiI : Finv_AAZ * uPhiAnc_AAZ⁻¹ * F_AAZ = uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹ := by
      rw [Finv_mul_uPhiAnc_mul_F_eq.2]; exact hPEPhiComm
    have hcStr218Def : Finv_AAZ * uStr218_AAZ * F_AAZ = cStr218 := rfl
    rw [uC9_AAZ_def]
    simp only [hConjMul, Finv_mul_uXorSubst_mul_F_eq, Finv_mul_uPhiAnc_mul_F_eq.1,
      hPhiI, Finv_mul_uHeadAnc_mul_F_eq, hcStr218Def, hcStr218Inv]
    dsimp only [M_anc, uPE18_AAZ]
    simp only [_root_.mul_assoc]
  obtain ⟨d18, hd18⟩ : ∃ d : Fin (2 ^ 18) → ℂ, uPointElec18.1 = Matrix.diagonal d := ⟨_, rfl⟩
  let c0 : ℂ := d18 0
  have hc0Unit : star c0 * c0 = 1 := by
    have hU := Matrix.mem_unitaryGroup_iff'.mp uPointElec18.2
    have h00 := congrFun (congrFun hU 0) 0
    rw [Matrix.star_eq_conjTranspose, hd18, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal] at h00
    simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply] using h00
  have hPE_Panc : uPE18_AAZ.1 * P_anc_AAZ = c0 • P_anc_AAZ ∧
      (uPE18_AAZ⁻¹).1 * P_anc_AAZ = star c0 • P_anc_AAZ := by
    have h18 : uPointElec18.1 * (QRegExt.idReg 18).basisOutcomeProjector 0 =
        c0 • (QRegExt.idReg 18).basisOutcomeProjector 0 := by
      rw [hd18, QRegister.basisOutcomeProjector_eq_diagonal,
          Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      apply congrArg Matrix.diagonal; funext z
      have hidz : (QRegExt.idReg 18).extractIndex z = z :=
        eq_of_basisBits_eq fun q ↦ by rw [basisBits_extractIndex_assoc]; rfl
      simp only [Pi.smul_apply, smul_eq_mul, hidz]
      by_cases hz : z = 0
      · subst hz; simp [c0]
      · simp [hz]
    have h18I : (uPointElec18⁻¹).1 * (QRegExt.idReg 18).basisOutcomeProjector 0 =
        star c0 • (QRegExt.idReg 18).basisOutcomeProjector 0 := by
      have hUU : uPointElec18.1 * uPointElec18.1ᴴ = 1 :=
        Matrix.mem_unitaryGroup_iff.mp uPointElec18.2
      have hInvDiag : (uPointElec18⁻¹).1 = uPointElec18.1ᴴ := by
        calc (uPointElec18⁻¹).1
            = (uPointElec18⁻¹).1 * (uPointElec18.1 * uPointElec18.1ᴴ) := by
                rw [hUU, Matrix.mul_one]
          _ = ((uPointElec18⁻¹ * uPointElec18).1) * uPointElec18.1ᴴ := by
                simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          _ = uPointElec18.1ᴴ := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
      rw [hInvDiag, hd18, QRegister.basisOutcomeProjector_eq_diagonal,
          Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      apply congrArg Matrix.diagonal; funext z
      have hidz : (QRegExt.idReg 18).extractIndex z = z :=
        eq_of_basisBits_eq fun q ↦ by rw [basisBits_extractIndex_assoc]; rfl
      simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, hidz]
      by_cases hz : z = 0
      · subst hz; simp [c0]
      · simp [hz]
    have hP0Emb : selAAZ_Anc.embedMatrix ((QRegExt.idReg 18).basisOutcomeProjector 0) = P_anc_AAZ :=
      by
      rw [P_anc_AAZ_eq_anc_proj0, embedMatrix_basisOutcomeProjector_zero_assoc]; rfl
    refine ⟨?_, ?_⟩
    · dsimp only [uPE18_AAZ]
      rw [← hP0Emb, QRegister.embedUnitary_val, ← selAAZ_Anc.embedMatrix_mul, h18,
          selAAZ_Anc.embedMatrix_smul]
    · dsimp only [uPE18_AAZ]
      rw [← hP0Emb, ← QRegister.embedUnitary_inv, QRegister.embedUnitary_val,
          ← selAAZ_Anc.embedMatrix_mul, h18I, selAAZ_Anc.embedMatrix_smul]
  have hPZDisjAnc : ((selAAZ_Data.compose rPosCoreInFull).concat selAAZ_Z
      (selAAZ_Data_disj_Z.compose_left rPosCoreInFull)).DisjointWires selAAZ_Anc :=
    disjointWires_concat_left _ (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right
      rPosCoreInFull)) (QRegExt.disjointWires_symm selAAZ_Anc_disj_Z)
  have hXorPanc : uXorData_AAZ.1 * P_anc_AAZ = P_anc_AAZ * uXorData_AAZ.1 :=
    embed_comm_P_anc_AAZ hPZDisjAnc _
  have hPhiPanc : uPhi217_AAZ.1 * P_anc_AAZ = P_anc_AAZ * uPhi217_AAZ.1 ∧ (uPhi217_AAZ⁻¹).1 *
      P_anc_AAZ = P_anc_AAZ * (uPhi217_AAZ⁻¹).1 := ⟨embed_comm_P_anc_AAZ hHeldDisjAnc _,
      unitary_val_inv_comm_of_comm uPhi217_AAZ (embed_comm_P_anc_AAZ hHeldDisjAnc _)⟩
  have hMidEq : M_anc.1 * (P217_AAZ * P_anc_AAZ) = M_data.1 * (P217_AAZ * P_anc_AAZ) := by
    obtain ⟨hPhi217, _, hXor217, _, _, _⟩ := uCSDiag_comm_AAZ (stream42DiagFn spectatorSum217)
    change uPhi217_AAZ.1 * P217_AAZ = P217_AAZ * uPhi217_AAZ.1 at hPhi217
    change uXorData_AAZ.1 * P217_AAZ = P217_AAZ * uXorData_AAZ.1 at hXor217
    have hPE_P217 : uPE18_AAZ.1 * P217_AAZ = P217_AAZ * uPE18_AAZ.1 :=
      selAAZ_Anc.embedMatrix_comm_of_disjoint (selAAZ_Data.compose rCSFull80)
        (selAAZ_Anc_disj_Data.compose_right rCSFull80) _ _
    have hPEI_P217 : (uPE18_AAZ⁻¹).1 * P217_AAZ = P217_AAZ * (uPE18_AAZ⁻¹).1 :=
      unitary_val_inv_comm_of_comm uPE18_AAZ hPE_P217
    obtain ⟨hStrF0, hStrI0⟩ := conj_uStr218_eq_uStr217_on_pSum42Zero_P_anc0
    let P_sum0_AAZ := selAAZ_Data.embedMatrix pSum42Zero
    have hcStr218Emb : selAAZ_AA.embedUnitary ((uSlot0MeasSwap * uBarrelFastAct) *
        (selDataInAct kFull80).embedUnitary (rCSFull80.embedUnitary uStr218_3Axis) *
        (uBarrelFastAct * uSlot0MeasSwap)) = cStr218 := by
      dsimp only [cStr218]
      rw[QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, ← F_AAZ.eq_1,
          ← Finv_AAZ.eq_1, ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
      rfl
    have huStr217Emb : selAAZ_AA.embedUnitary ((selDataInAct kFull80).embedUnitary
        (rCSFull80.embedUnitary (uStr3AxisOfSpec uStream217Spec131))) = uStr217_AAZ := by
      rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
      rfl
    have hStrF : cStr218.1 * (P_sum0_AAZ * P_anc_AAZ) = uStr217_AAZ.1 * (P_sum0_AAZ * P_anc_AAZ) :=
      by
      have h := congrArg selAAZ_AA.embedMatrix hStrF0
      simp only [QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val,
        hcStr218Emb, huStr217Emb, ← QRegister.embedMatrix_compose] at h
      exact h
    have hStrI : (cStr218⁻¹).1 * (P217_AAZ * P_anc_AAZ) = (uStr217_AAZ⁻¹).1 * (P217_AAZ *
      P_anc_AAZ) := by
      have h := congrArg selAAZ_AA.embedMatrix hStrI0
      simp only [QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val,
        QRegister.embedUnitary_inv,
        hcStr218Emb, huStr217Emb, ← QRegister.embedMatrix_compose, ← QRegister.compose_assoc] at h
      exact h
    have hP217Decomp : P217_AAZ =
        (uStr217_AAZ.1 * P_sum0_AAZ) * (selAAZ_Data.embedMatrix E_raw217)ᴴ := by
      have hP0CS : rCSFull80.embedMatrix pSum42CoreZero = pSum42Zero := by
        rw [pSum42CoreZero, pSum42Zero, embedMatrix_basisOutcomeProjector_zero_assoc]
        congr 1; apply qreg_ext; intro j
        have hj : rZLoc (fullSysCoreWires 80) 42 j = Fin.natAdd (fullSysCoreWires 80) j :=
          Fin.ext (by simp [rZLoc])
        rw [QRegister.compose_apply, hj]; dsimp only [rCSFull80]; rw [QRegister.concat_apply_right]
      have hU217P0 : uStr217_AAZ.1 * P_sum0_AAZ = selAAZ_Data.embedMatrix E_raw217 := by
        dsimp only [uStr217_AAZ, P_sum0_AAZ, E_raw217]
        rw [← hP0CS, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
            ← (selAAZ_Data.compose rCSFull80).embedMatrix_mul,
            uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core, QRegister.embedMatrix_compose]
      rw [hU217P0, ← QRegister.embedMatrix_conjTranspose, ← selAAZ_Data.embedMatrix_mul]
      unfold P217_AAZ E_raw217
      rw [QRegister.embedMatrix_compose, ← QRegister.embedMatrix_conjTranspose,
          ← rCSFull80.embedMatrix_mul, eStream217Core_mul_conjTranspose]
    have hStr217InvP : (uStr217_AAZ⁻¹).1 * (P217_AAZ * P_anc_AAZ) =
        (P_sum0_AAZ * P_anc_AAZ) * (selAAZ_Data.embedMatrix E_raw217)ᴴ := by
      have hDataPanc : (selAAZ_Data.embedMatrix E_raw217)ᴴ * P_anc_AAZ =
          P_anc_AAZ * (selAAZ_Data.embedMatrix E_raw217)ᴴ := by
        rw [← QRegister.embedMatrix_conjTranspose]
        exact embed_comm_P_anc_AAZ (QRegExt.disjointWires_symm selAAZ_Anc_disj_Data) _
      rw [hP217Decomp, Matrix.mul_assoc _ _ P_anc_AAZ, hDataPanc]
      calc (uStr217_AAZ⁻¹).1 * ((uStr217_AAZ.1 * P_sum0_AAZ) * (P_anc_AAZ *
        (selAAZ_Data.embedMatrix E_raw217)ᴴ))
          = ((uStr217_AAZ⁻¹ * uStr217_AAZ).1) * P_sum0_AAZ * P_anc_AAZ *
              (selAAZ_Data.embedMatrix E_raw217)ᴴ := by
                simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = (P_sum0_AAZ * P_anc_AAZ) * (selAAZ_Data.embedMatrix E_raw217)ᴴ := by
              rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul, Matrix.mul_assoc]
    have hHeadCommP0 : uHeadData_AAZ.1 * P_sum0_AAZ = P_sum0_AAZ * uHeadData_AAZ.1 := by
      unfold uHeadData_AAZ P_sum0_AAZ pSum42Zero
      rw [embedMatrix_basisOutcomeProjector_zero_assoc, QRegister.embedUnitary_val]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selAAZ_Data.compose
        rPosCoreInFull))
        (selAAZ_Data.compose rSum0)
        (disjointWires_compose_of_disjoint selAAZ_Data
          (rCoreFull_disj_rSum0.compose_left selPosCoreInCore80)) _ 0
    have hHeadCommPanc : uHeadData_AAZ.1 * P_anc_AAZ = P_anc_AAZ * uHeadData_AAZ.1 :=
      embedData_comm_P_anc_AAZ rPosCoreInFull _
    have hStr217Panc : uStr217_AAZ.1 * P_anc_AAZ = P_anc_AAZ * uStr217_AAZ.1 :=
      embedData_comm_P_anc_AAZ rCSFull80 _
    have hCoreBlock :
        (cStr218 * (uHeadData_AAZ * cStr218⁻¹)).1 * (P217_AAZ * P_anc_AAZ) =
        P_anc_AAZ * ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * (P217_AAZ * P_anc_AAZ)) :=
          by
      calc (cStr218 * (uHeadData_AAZ * cStr218⁻¹)).1 * (P217_AAZ * P_anc_AAZ)
          = cStr218.1 * (uHeadData_AAZ.1 * ((cStr218⁻¹).1 * (P217_AAZ * P_anc_AAZ))) := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = cStr218.1 * (uHeadData_AAZ.1 *
              ((P_sum0_AAZ * P_anc_AAZ) * (selAAZ_Data.embedMatrix E_raw217)ᴴ)) := by
              rw [hStrI, hStr217InvP]
        _ = (cStr218.1 * (P_sum0_AAZ * P_anc_AAZ)) *
              (uHeadData_AAZ.1 * (selAAZ_Data.embedMatrix E_raw217)ᴴ) := by
              rw [← Matrix.mul_assoc uHeadData_AAZ.1, ← Matrix.mul_assoc uHeadData_AAZ.1,
                  hHeadCommP0, Matrix.mul_assoc P_sum0_AAZ, hHeadCommPanc]
              simp only [Matrix.mul_assoc]
        _ = (uStr217_AAZ.1 * ((P_sum0_AAZ * P_anc_AAZ) * P_anc_AAZ)) *
              (uHeadData_AAZ.1 * (selAAZ_Data.embedMatrix E_raw217)ᴴ) := by
              rw [hStrF, Matrix.mul_assoc P_sum0_AAZ, P_anc_AAZ_mul_self]
        _ = P_anc_AAZ * (uStr217_AAZ.1 *
              ((P_sum0_AAZ * P_anc_AAZ) * (uHeadData_AAZ.1 *
                (selAAZ_Data.embedMatrix E_raw217)ᴴ))) := by
              have hP0Panc : P_sum0_AAZ * P_anc_AAZ = P_anc_AAZ * P_sum0_AAZ :=
                embed_comm_P_anc_AAZ (QRegExt.disjointWires_symm selAAZ_Anc_disj_Data) _
              rw [hP0Panc, Matrix.mul_assoc P_anc_AAZ P_sum0_AAZ P_anc_AAZ,
                  ← Matrix.mul_assoc uStr217_AAZ.1 P_anc_AAZ, hStr217Panc]
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc P_sum0_AAZ P_anc_AAZ, hP0Panc,
                Matrix.mul_assoc P_anc_AAZ P_sum0_AAZ]
        _ = P_anc_AAZ * ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * (P217_AAZ *
          P_anc_AAZ)) := by
              have hRev : (P_sum0_AAZ * P_anc_AAZ) * (uHeadData_AAZ.1 *
                (selAAZ_Data.embedMatrix E_raw217)ᴴ) =
                  uHeadData_AAZ.1 * ((uStr217_AAZ⁻¹).1 * (P217_AAZ * P_anc_AAZ)) := by
                rw [hStr217InvP, ← Matrix.mul_assoc uHeadData_AAZ.1,
                  ← Matrix.mul_assoc uHeadData_AAZ.1,
                    hHeadCommP0, Matrix.mul_assoc P_sum0_AAZ uHeadData_AAZ.1 P_anc_AAZ,
                      hHeadCommPanc]
                simp only [Matrix.mul_assoc]
              rw [hRev]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    have hPreComm : (uPhi217_AAZ * uXorData_AAZ).1 * (P217_AAZ * P_anc_AAZ) =
        (P217_AAZ * P_anc_AAZ) * (uPhi217_AAZ * uXorData_AAZ).1 := by
      simp only [Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc uXorData_AAZ.1, hXor217,
          Matrix.mul_assoc P217_AAZ, hXorPanc, ← Matrix.mul_assoc uPhi217_AAZ.1, hPhi217,
          Matrix.mul_assoc P217_AAZ, ← Matrix.mul_assoc uPhi217_AAZ.1, hPhiPanc.1]
      simp only [Matrix.mul_assoc]
    have hPE_In : uPE18_AAZ.1 * (P217_AAZ * P_anc_AAZ) = c0 • (P217_AAZ * P_anc_AAZ) := by
      rw [← Matrix.mul_assoc, hPE_P217, Matrix.mul_assoc, hPE_Panc.1, mul_smul_comm]
    dsimp only [M_anc, M_data]
    calc ((uXorData_AAZ * (uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹)) *
            ((cStr218 * (uHeadData_AAZ * cStr218⁻¹)) * ((uPE18_AAZ * uPhi217_AAZ) *
              uXorData_AAZ))).1 *
            (P217_AAZ * P_anc_AAZ)
        = (uXorData_AAZ * uPhi217_AAZ⁻¹).1 * ((uPE18_AAZ⁻¹).1 *
            ((cStr218 * (uHeadData_AAZ * cStr218⁻¹)).1 *
              (uPE18_AAZ.1 * ((uPhi217_AAZ * uXorData_AAZ).1 * (P217_AAZ * P_anc_AAZ))))) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = c0 • ((uXorData_AAZ * uPhi217_AAZ⁻¹).1 *
            (((uPE18_AAZ⁻¹).1 * P_anc_AAZ) *
              ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * (P217_AAZ * P_anc_AAZ)) *
              (uPhi217_AAZ * uXorData_AAZ).1)) := by
            rw [hPreComm, ← Matrix.mul_assoc uPE18_AAZ.1, hPE_In]
            simp only [Matrix.mul_smul, smul_mul_assoc, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc P217_AAZ P_anc_AAZ,
                ← Matrix.mul_assoc (cStr218 * _).1 (P217_AAZ * P_anc_AAZ), hCoreBlock]
            simp only [Matrix.mul_assoc]
      _ = (star c0 * c0) • ((uXorData_AAZ * uPhi217_AAZ⁻¹).1 *
            (P_anc_AAZ *
              (((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * (P217_AAZ * P_anc_AAZ)) *
                (uPhi217_AAZ * uXorData_AAZ).1))) := by
            rw [hPE_Panc.2]
            simp only [smul_mul_assoc, Matrix.mul_smul, smul_smul, mul_comm c0 (star c0),
              Matrix.mul_assoc]
      _ = M_data.1 * (P217_AAZ * P_anc_AAZ) := by
            rw [hc0Unit, one_smul]
            have hAbsorb : P_anc_AAZ *
                ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * (P217_AAZ * P_anc_AAZ)) =
                (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * (P217_AAZ * P_anc_AAZ) := by
              have hComm3 : (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * P_anc_AAZ =
                  P_anc_AAZ * (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 := by
                have hStr217IPanc := unitary_val_inv_comm_of_comm uStr217_AAZ hStr217Panc
                simp only [Submonoid.coe_mul]
                rw [Matrix.mul_assoc, Matrix.mul_assoc, hStr217IPanc,
                    ← Matrix.mul_assoc uHeadData_AAZ.1, hHeadCommPanc,
                    Matrix.mul_assoc P_anc_AAZ, ← Matrix.mul_assoc uStr217_AAZ.1, hStr217Panc]
                simp only [Matrix.mul_assoc]
              have hP217Panc : P217_AAZ * P_anc_AAZ = P_anc_AAZ * P217_AAZ :=
                embedData_comm_P_anc_AAZ rCSFull80 _
              rw [hP217Panc, ← Matrix.mul_assoc (uStr217_AAZ * _).1 P_anc_AAZ P217_AAZ, hComm3,
                  ← Matrix.mul_assoc P_anc_AAZ (P_anc_AAZ * _) P217_AAZ,
                  ← Matrix.mul_assoc P_anc_AAZ P_anc_AAZ, P_anc_AAZ_mul_self,
                  ← hComm3, Matrix.mul_assoc _ P_anc_AAZ P217_AAZ, ← hP217Panc]
            rw [← Matrix.mul_assoc P_anc_AAZ, hAbsorb, Matrix.mul_assoc _ _ (uPhi217_AAZ * _).1,
                ← hPreComm]
            dsimp only [M_data]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  have hMDataComm0 : M_data.1 * Pc2_AAZ 0 = Pc2_AAZ 0 * M_data.1 := by
    obtain ⟨f0, hf0⟩ := Pc2_AAZ_eq_rCS_diagonal 0
    obtain ⟨hPhi0, hPhiI0, hXor0, _, _, _⟩ := uCSDiag_comm_AAZ f0
    rw [← hf0] at hPhi0 hPhiI0 hXor0
    have hStr0 := uStr217_AAZ_comm_Pc2 0
    have hHead0 := uHeadData_and_Anc_Pc2.2.1
    dsimp only [M_data]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    rw [hXor0, ← Matrix.mul_assoc uPhi217_AAZ.1, hPhi0,
        Matrix.mul_assoc (Pc2_AAZ 0), ← Matrix.mul_assoc (uStr217_AAZ⁻¹).1, hStr0.2,
        Matrix.mul_assoc (Pc2_AAZ 0), ← Matrix.mul_assoc uHeadData_AAZ.1, hHead0,
        Matrix.mul_assoc (Pc2_AAZ 0), ← Matrix.mul_assoc uStr217_AAZ.1, hStr0.1,
        Matrix.mul_assoc (Pc2_AAZ 0), ← Matrix.mul_assoc (uPhi217_AAZ⁻¹).1, hPhiI0,
        Matrix.mul_assoc (Pc2_AAZ 0), ← Matrix.mul_assoc uXorData_AAZ.1, hXor0]
    simp only [Matrix.mul_assoc]
  have hSwBase : (P217_AAZ * P_anc_AAZ) * (uSw_AAZ.1 * E_base_AAZ) = uSw_AAZ.1 * E_base_AAZ := by
    have hSwPanc : uSw_AAZ.1 * P_anc_AAZ = P_anc_AAZ * uSw_AAZ.1 :=
      embedData_comm_P_anc_AAZ rCoreFull _
    have hP217E : P217_AAZ * selAAZ_Data.embedMatrix E_raw217 = selAAZ_Data.embedMatrix E_raw217 :=
      by
      unfold P217_AAZ E_raw217
      rw [QRegister.embedMatrix_compose, ← selAAZ_Data.embedMatrix_mul,
          ← rCSFull80.embedMatrix_mul, pStream217Core_mul_eStream217Core]
    have hBaseFixed : (P217_AAZ * P_anc_AAZ) * E_base_AAZ = E_base_AAZ := by
      unfold E_base_AAZ
      have hDataPanc : selAAZ_Data.embedMatrix E_raw217 * P_anc_AAZ = P_anc_AAZ *
          selAAZ_Data.embedMatrix E_raw217 :=
            embed_comm_P_anc_AAZ (QRegExt.disjointWires_symm selAAZ_Anc_disj_Data) _
      calc (P217_AAZ * P_anc_AAZ) * (selAAZ_Data.embedMatrix E_raw217 * P_anc_AAZ *
        selAAZ_Z.basisOutcomeProjector 0)
          = P217_AAZ * (selAAZ_Data.embedMatrix E_raw217 * (P_anc_AAZ * P_anc_AAZ)) *
              selAAZ_Z.basisOutcomeProjector 0 := by
              rw [Matrix.mul_assoc P217_AAZ,
                  ← Matrix.mul_assoc P_anc_AAZ (selAAZ_Data.embedMatrix E_raw217 * P_anc_AAZ),
                  ← Matrix.mul_assoc P_anc_AAZ (selAAZ_Data.embedMatrix E_raw217) P_anc_AAZ,
                  ← hDataPanc]
              simp only [Matrix.mul_assoc]
        _ = selAAZ_Data.embedMatrix E_raw217 * P_anc_AAZ * selAAZ_Z.basisOutcomeProjector 0 := by
              rw [P_anc_AAZ_mul_self, ← Matrix.mul_assoc P217_AAZ, hP217E]
    calc (P217_AAZ * P_anc_AAZ) * (uSw_AAZ.1 * E_base_AAZ)
        = uSw_AAZ.1 * ((P217_AAZ * P_anc_AAZ) * E_base_AAZ) := by
            rw [Matrix.mul_assoc P217_AAZ, ← Matrix.mul_assoc P_anc_AAZ, ← hSwPanc,
                ← Matrix.mul_assoc P217_AAZ (uSw_AAZ.1 * P_anc_AAZ) E_base_AAZ,
                ← Matrix.mul_assoc P217_AAZ uSw_AAZ.1 P_anc_AAZ,
                ← uSw_AAZ_comm_Pc2_and_streams.2.2]
            simp only [Matrix.mul_assoc]
      _ = uSw_AAZ.1 * E_base_AAZ := by rw [hBaseFixed]
  have hPc20CommPA : Pc2_AAZ 0 * (P217_AAZ * P_anc_AAZ) = (P217_AAZ * P_anc_AAZ) * Pc2_AAZ 0 := by
    obtain ⟨f0, hf0⟩ := Pc2_AAZ_eq_rCS_diagonal 0
    have h1 : Pc2_AAZ 0 * P217_AAZ = P217_AAZ * Pc2_AAZ 0 := by
      rw [hf0]; unfold P217_AAZ pStream217Core pStream42Of
      rw [← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
      exact congrArg (selAAZ_Data.compose rCSFull80).embedMatrix (diagonal_comm_op_assoc _ _)
    have h2 : Pc2_AAZ 0 * P_anc_AAZ = P_anc_AAZ * Pc2_AAZ 0 :=
      embedData_comm_P_anc_AAZ rCoreFull _
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc P217_AAZ, h2, Matrix.mul_assoc]
  have hBaseEq : (Finv_AAZ * uC9_AAZ * F_AAZ).1 * (Pc2_AAZ 0 * E_base_AAZ) =
      uData9_AAZ.1 * (Pc2_AAZ 0 * E_base_AAZ) := by
    rw [hConjC9]
    let cSw := Finv_AAZ * uSw_AAZ * F_AAZ
    calc (cSw * (M_anc * cSw)).1 * (Pc2_AAZ 0 * E_base_AAZ)
        = cSw.1 * (M_anc.1 * ((cSw.1 * Pc2_AAZ 0) * E_base_AAZ)) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = cSw.1 * (M_anc.1 * (Pc2_AAZ 0 * ((P217_AAZ * P_anc_AAZ) * (uSw_AAZ.1 * E_base_AAZ)))) :=
        by
            rw [Finv_mul_uSw_mul_F_on_Pc20, uSw_AAZ_comm_Pc2_and_streams.1 0,
                Matrix.mul_assoc (Pc2_AAZ 0), hSwBase]
      _ = cSw.1 * ((M_anc.1 * (P217_AAZ * P_anc_AAZ)) * (Pc2_AAZ 0 * (uSw_AAZ.1 * E_base_AAZ))) :=
        by
            rw [← Matrix.mul_assoc (Pc2_AAZ 0), hPc20CommPA]; simp only [Matrix.mul_assoc]
      _ = cSw.1 * (M_data.1 * (Pc2_AAZ 0 * (uSw_AAZ.1 * E_base_AAZ))) := by
            rw [hMidEq, Matrix.mul_assoc M_data.1,
              ← Matrix.mul_assoc (P217_AAZ * P_anc_AAZ) (Pc2_AAZ 0),
                ← hPc20CommPA, Matrix.mul_assoc (Pc2_AAZ 0), hSwBase]
      _ = (cSw.1 * Pc2_AAZ 0) * (M_data.1 * (uSw_AAZ.1 * E_base_AAZ)) := by
            rw [← Matrix.mul_assoc M_data.1, hMDataComm0]; simp only [Matrix.mul_assoc]
      _ = uData9_AAZ.1 * (Pc2_AAZ 0 * E_base_AAZ) := by
            rw[Finv_mul_uSw_mul_F_on_Pc20, Matrix.mul_assoc uSw_AAZ.1,
                ← Matrix.mul_assoc (Pc2_AAZ 0) M_data.1, ← hMDataComm0,
                Matrix.mul_assoc M_data.1, ← Matrix.mul_assoc (Pc2_AAZ 0) uSw_AAZ.1,
                ← uSw_AAZ_comm_Pc2_and_streams.1 0, uData9_AAZ_eq_prod9]
            dsimp only [M_data]
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  have hInit0 : Pc2_AAZ 0 * E_init_AAZ = F_AAZ.1 * (Pc2_AAZ 0 * E_base_AAZ) := by
    rw [E_init_AAZ_eq_F_mul_E_base, ← Matrix.mul_assoc, ← (F_AAZ_comm_Pc2_AAZ 0).1,
      Matrix.mul_assoc]
  rw [hInit0]
  calc uC9_AAZ.1 * (F_AAZ.1 * (Pc2_AAZ 0 * E_base_AAZ))
      = (F_AAZ.1 * Finv_AAZ.1) * (uC9_AAZ.1 * (F_AAZ.1 * (Pc2_AAZ 0 * E_base_AAZ))) := by
          rw [← Submonoid.coe_mul, F_AAZ_mul_Finv_AAZ.1, OneMemClass.coe_one, Matrix.one_mul]
    _ = F_AAZ.1 * ((Finv_AAZ * uC9_AAZ * F_AAZ).1 * (Pc2_AAZ 0 * E_base_AAZ)) := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = F_AAZ.1 * (uData9_AAZ.1 * ((Finv_AAZ.1 * F_AAZ.1) * (Pc2_AAZ 0 * E_base_AAZ))) := by
          rw [hBaseEq, ← Submonoid.coe_mul, F_AAZ_mul_Finv_AAZ.2, OneMemClass.coe_one,
            Matrix.one_mul]
    _ = (F_AAZ * uData9_AAZ * Finv_AAZ).1 * (F_AAZ.1 * (Pc2_AAZ 0 * E_base_AAZ)) := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
open Classical in
theorem uC9_AAZ_eq_on_E_init : uC9_AAZ.1 * E_init_AAZ =
    (selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 * E_init_AAZ := by
  have hSum : uC9_AAZ.1 * E_init_AAZ = (F_AAZ * uData9_AAZ * Finv_AAZ).1 * E_init_AAZ := by
    have hSplit : E_init_AAZ = Pc2_AAZ 0 * E_init_AAZ + Pc2_AAZ 1 * E_init_AAZ := by
      rw [← add_mul, Pc2_AAZ_zero_add_one, Matrix.one_mul]
    calc uC9_AAZ.1 * E_init_AAZ
        = uC9_AAZ.1 * (Pc2_AAZ 0 * E_init_AAZ + Pc2_AAZ 1 * E_init_AAZ) := congrArg _ hSplit
      _ = (F_AAZ * uData9_AAZ * Finv_AAZ).1 * (Pc2_AAZ 0 * E_init_AAZ + Pc2_AAZ 1 * E_init_AAZ) :=
        by
            rw [mul_add, mul_add, uC9_AAZ_eq_on_Pc20, uC9_AAZ_eq_on_Pc21]
      _ = (F_AAZ * uData9_AAZ * Finv_AAZ).1 * E_init_AAZ := congrArg _ hSplit.symm
  rw [hSum]
  have hFinvZ : Finv_AAZ.1 * selAAZ_Z.basisOutcomeProjector 0 =
      selAAZ_Z.basisOutcomeProjector 0 * Finv_AAZ.1 := by
    rw [Finv_AAZ.eq_1, QRegister.embedUnitary_val]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZ_AA) selAAZ_Z
      (selDataInAct_disj_selMeasInAct (kFull80 + 18)) _ 0
  unfold E_init_AAZ
  calc (F_AAZ * uData9_AAZ * Finv_AAZ).1 *
          (selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) * selAAZ_Z.basisOutcomeProjector 0)
      = F_AAZ.1 * ((uData9_AAZ.1 * selAAZ_Z.basisOutcomeProjector 0) *
          (Finv_AAZ.1 * selAAZ_AA.embedMatrix (E_anchorLoc E_raw217))) := by
          have hAAZ : selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) *
            selAAZ_Z.basisOutcomeProjector 0 =
              selAAZ_Z.basisOutcomeProjector 0 * selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) :=
            (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZ_AA) selAAZ_Z
              (selDataInAct_disj_selMeasInAct (kFull80 + 18)) _ 0
          rw [hAAZ]
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Finv_AAZ.1 (selAAZ_Z.basisOutcomeProjector 0), hFinvZ,
              Matrix.mul_assoc (selAAZ_Z.basisOutcomeProjector 0)]
    _ = (F_AAZ * selAAZ_Data.embedUnitary uInnerSwapFull * Finv_AAZ).1 *
          (selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) * selAAZ_Z.basisOutcomeProjector 0) := by
          rw [uData9_AAZ_mul_PZ_eq]
          have hAAZ : selAAZ_Z.basisOutcomeProjector 0 *
            selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) =
              selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) * selAAZ_Z.basisOutcomeProjector 0 :=
            ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZ_AA) selAAZ_Z
              (selDataInAct_disj_selMeasInAct (kFull80 + 18)) _ 0).symm
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (selAAZ_Z.basisOutcomeProjector 0) Finv_AAZ.1, ← hFinvZ,
              Matrix.mul_assoc Finv_AAZ.1, hAAZ]
    _ = (selAAZ_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 *
          (selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) * selAAZ_Z.basisOutcomeProjector 0) := by
          rw [F_AAZ_InnerSwap_Finv_eq]
open Classical in
theorem uSw_AAZ_def :
    uSw_AAZ = (selAAZ_Data.compose rCoreFull).embedUnitary uSwapCore3967 := rfl
open Classical in
theorem uXorSubst_AAZ_def :
    uXorSubst_AAZ = ((selAAZ_Subst.compose rPosCoreInFull).concat selAAZ_Z
      (selAAZ_Subst_disj_Z.compose_left rPosCoreInFull)).embedUnitary uXorZTarget18 := rfl
open Classical in
theorem uPhiAnc_AAZ_def :
    uPhiAnc_AAZ = selAAZ_HeldAct.embedUnitary uPhiHeldZ18AnchorCat := rfl
open Classical in
theorem uHeadAnc_AAZ_def :
    uHeadAnc_AAZ = (selAAZ_AA.compose (selLiftAct rPosCoreInFull)).embedUnitary uHeadAnchorConjH :=
      rfl
open Classical in
theorem uStr218_AAZ_def :
    uStr218_AAZ = (selAAZ_Data.compose rCSFull80).embedUnitary uStr218_3Axis := rfl
theorem P218_AAZ_def :
    P218_AAZ = (selAAZ_Data.compose rCSFull80).embedMatrix (pStream218Core 80) := rfl
theorem P218_AAZ_eq_diag : (selAAZ_Data.compose rCSFull80).embedMatrix
    (Matrix.diagonal (stream42DiagFn slot2AxisSum)) = P218_AAZ := rfl
theorem E_init_AAZ_def :
    E_init_AAZ = selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) * selAAZ_Z.basisOutcomeProjector 0 :=
      rfl
-- Pebbled carry-wire diagonal decomposition on `AAZ` & commutation with `uMid5_AAZ` on `P218_AAZ`
def carryBit18Pos (γ : BitAssignment posCoreWires) (k : Fin 18) : ZMod 2 :=
  let w : Fin 3 := ⟨k.val / 6, by have := k.isLt; omega⟩
  let j : Fin 6 := ⟨k.val % 6, by omega⟩
  carrySeq6
    (fun i ↦ γ (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) w i))
    (fun i ↦ γ (rHeadFine21 (QRegExt.ofFin posCoreWires)
      ⟨7 * w.val + i.val + 1, by have := w.isLt; have := i.isLt; omega⟩))
    (1 + (γ (rCosetB0 (QRegExt.ofFin posCoreWires) w) + 1) *
      γ (rHeadFine21 (QRegExt.ofFin posCoreWires) ⟨7 * w.val, by have := w.isLt; omega⟩))
    j.val
noncomputable def carryIdx18_AAZ (x : Fin (2 ^ ((kFull80 + 18) + 18))) : Fin (2 ^ 18) :=
  (basisBitsEquiv 18).symm
    (carryBit18Pos (fun i ↦
      basisBits ((kFull80 + 18) + 18) x ((selAAZ_Subst.compose rPosCoreInFull) i)))
open Classical in
noncomputable def D_carry_AAZ (u : Fin (2 ^ 18)) : Operator (2 ^ ((kFull80 + 18) + 18)) :=
  Matrix.diagonal (fun x ↦ if carryIdx18_AAZ x = u then (1 : ℂ) else 0)
theorem sum_diagonal_part4 {D : ℕ} {ι : Type*} (S : Finset ι) (F : ι → Fin D → ℂ) :
    (∑ a ∈ S, (Matrix.diagonal (F a) : Operator D)) = Matrix.diagonal (fun x ↦ ∑ a ∈ S, F a x) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]
theorem D_carry_AAZ_comm_P218 (u : Fin (2 ^ 18)) :
    D_carry_AAZ u * P218_AAZ = P218_AAZ * D_carry_AAZ u := by
  rw [← P218_AAZ_eq_diag]
  unfold D_carry_AAZ
  rw [embedMatrix_diagonal_local]
  exact diagonal_comm_op_assoc _ _
theorem embedMatrix_basisOutcomeProjector_gen_part4 {k m N : ℕ}
    (r : QRegister m N) (s : QRegister k m) (a : Fin (2 ^ k)) :
    r.embedMatrix (s.basisOutcomeProjector a) = (r.compose s).basisOutcomeProjector a := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      embedMatrix_diagonal_local]
  apply congrArg Matrix.diagonal; funext x
  have h : s.extractIndex (r.extractIndex x) = (r.compose s).extractIndex x :=
    eq_of_basisBits_eq fun q ↦ by
      rw [basisBits_extractIndex_assoc, basisBits_extractIndex_assoc,
          basisBits_extractIndex_assoc, QRegister.compose_apply]
  rw [h]
def rCore24InPos : QRegister (3 + 21) posCoreWires :=
  (rCosetB0 (QRegExt.ofFin posCoreWires)).concat (rHeadFine21 (QRegExt.ofFin posCoreWires))
    (disj_of_val_ne fun i j ↦ by
      rw [rCosetB0_ofFin_val_assoc, rHeadFine21_ofFin_val_assoc]
      have := i.isLt; have := j.isLt; omega)
theorem rCore24InPos_val_bounds (t : Fin (3 + 21)) :
    3957 ≤ (rCore24InPos t).val ∧ (rCore24InPos t).val < 4034 ∧ (rCore24InPos t).val ≠ 3985 := by
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) t
  · dsimp only [rCore24InPos]
    rw [QRegister.concat_apply_left, rCosetB0_ofFin_val_assoc]
    have := i.isLt; omega
  · dsimp only [rCore24InPos]
    rw [QRegister.concat_apply_right, rHeadFine21_ofFin_val_assoc]
    have := j.isLt; omega
noncomputable def carryIdxOfAncAnd24 (a : Fin (2 ^ 18)) (c : Fin (2 ^ (3 + 21))) : Fin (2 ^ 18) :=
  (basisBitsEquiv 18).symm fun k ↦
    let w : Fin 3 := ⟨k.val / 6, by have := k.isLt; omega⟩
    let j : Fin 6 := ⟨k.val % 6, by omega⟩
    carrySeq6
      (fun i ↦ basisBits 18 a ⟨6 * w.val + (5 - i.val), by have := w.isLt; have := i.isLt; omega⟩)
      (fun i ↦ basisBits (3 + 21) c
        (Fin.natAdd 3 ⟨7 * w.val + i.val + 1, by have := w.isLt; have := i.isLt; omega⟩))
      (1 + (basisBits (3 + 21) c (Fin.castAdd 21 w) + 1) *
        basisBits (3 + 21) c (Fin.natAdd 3 ⟨7 * w.val, by have := w.isLt; omega⟩))
      j.val
open Classical in
theorem diagonal_eq_sum_proj_embed_diagonal_part4 {k m l N : ℕ} (rAnc : QRegister k N)
    (rC : QRegister m N) (f : Fin (2 ^ N) → Fin (2 ^ l))
    (g : Fin (2 ^ k) → Fin (2 ^ m) → Fin (2 ^ l)) (u : Fin (2 ^ l)) (hfg : ∀ x : Fin (2 ^ N),
    f x = g (rAnc.extractIndex x) (rC.extractIndex x)) : (Matrix.diagonal (fun x ↦ if f x = u
    then (1 : ℂ) else 0) : Operator (2 ^ N)) = ∑ a : Fin (2 ^ k), rAnc.basisOutcomeProjector a
    * rC.embedMatrix (Matrix.diagonal (fun c ↦ if g a c = u then (1 : ℂ) else 0)) := by
  have hTerm : ∀ a : Fin (2 ^ k),
      rAnc.basisOutcomeProjector a *
        rC.embedMatrix (Matrix.diagonal (fun c ↦ if g a c = u then (1 : ℂ) else 0)) =
      Matrix.diagonal (fun x ↦
        (if rAnc.extractIndex x = a then (1 : ℂ) else 0) *
          (if g a (rC.extractIndex x) = u then (1 : ℂ) else 0)) := fun a ↦ by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, embedMatrix_diagonal_local,
        diagonal_mul_diagonal_op_assoc]
  simp only [hTerm]
  rw [sum_diagonal_part4]
  apply congrArg Matrix.diagonal; funext x
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), hfg x]
theorem embedMatrix_congr_reg_part4 {k N : ℕ} {r₁ r₂ : QRegister k N}
    (h : r₁ = r₂) (M : Operator (2 ^ k)) : r₁.embedMatrix M = r₂.embedMatrix M :=
  congrArg (fun r ↦ r.embedMatrix M) h
open Classical in
theorem D_carry_AAZ_eq_sum_anc_core24 (u : Fin (2 ^ 18)) :
    let rCore24_AAZ := (selAAZ_Data.compose rPosCoreInFull).compose rCore24InPos
    D_carry_AAZ u = ∑ a : Fin (2 ^ 18),
      selAAZ_Anc.basisOutcomeProjector a *
        rCore24_AAZ.embedMatrix
          (Matrix.diagonal (fun c ↦ if carryIdxOfAncAnd24 a c = u then (1 : ℂ) else 0)) := by
  intro rCore24_AAZ
  have hCarryEq : ∀ x : Fin (2 ^ ((kFull80 + 18) + 18)),
      carryIdx18_AAZ x =
        carryIdxOfAncAnd24 (selAAZ_Anc.extractIndex x) (rCore24_AAZ.extractIndex x) := by
    intro x
    unfold carryIdx18_AAZ carryIdxOfAncAnd24 carryBit18Pos
    apply congrArg (basisBitsEquiv 18).symm
    funext k
    let w : Fin 3 := ⟨k.val / 6, by have := k.isLt; omega⟩
    let j : Fin 6 := ⟨k.val % 6, by omega⟩
    have hy : (fun i : Fin 6 ↦
          basisBits ((kFull80 + 18) + 18) x
            ((selAAZ_Subst.compose rPosCoreInFull)
              (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) w i))) =
        (fun i : Fin 6 ↦
          basisBits 18 (selAAZ_Anc.extractIndex x)
            ⟨6 * w.val + (5 - i.val), by have := w.isLt; have := i.isLt; omega⟩) := by
      funext i
      let q : Fin 18 := ⟨6 * w.val + (5 - i.val), by have := w.isLt; have := i.isLt; omega⟩
      rw [basisBits_extractIndex_assoc selAAZ_Anc x q]
      apply congrArg (basisBits ((kFull80 + 18) + 18) x)
      have hPos0 : rPosCoreInFull (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) w i) =
          rSlot0InFull q := by
        dsimp only [rPosCoreInFull, rSlot0InFull]
        apply congrArg rCoreFull; apply Fin.ext
        have h1 : (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) w i) =
            rElecSlot (QRegExt.ofFin posCoreWires) 0 q := rfl
        rw [h1, rSlot0InCore, rFullSysElecSlot_val]
        simp [selPosCoreInCore80, rElecSlot0_ofFin_val_assoc]
      dsimp only [selAAZ_Subst, selAAZ_Anc]
      rw [QRegister.compose_apply, hPos0, QRegister.compose_apply, selSubstSlot0,
          rDataSubstSlot0_apply_slot0, QRegister.compose_apply]
    have h24 : ∀ t : Fin (3 + 21),
        basisBits ((kFull80 + 18) + 18) x ((selAAZ_Subst.compose rPosCoreInFull) (rCore24InPos t)) =
        basisBits (3 + 21) (rCore24_AAZ.extractIndex x) t := fun t ↦ by
      rw [basisBits_extractIndex_assoc rCore24_AAZ x t]
      apply congrArg (basisBits ((kFull80 + 18) + 18) x)
      have hnot0 : rPosCoreInFull (rCore24InPos t) ∉ Set.range rSlot0InFull.wires := by
        rintro ⟨q, hq⟩
        have hv := congrArg Fin.val (rCoreFull.wires.injective hq)
        have hb := (rCore24InPos_val_bounds t).1
        have := q.isLt
        rw [rSlot0InCore, rFullSysElecSlot_val] at hv
        simp [selPosCoreInCore80] at hv; omega
      dsimp only [selAAZ_Subst, rCore24_AAZ, selAAZ_Data]
      rw [QRegister.compose_apply, QRegister.compose_apply, selSubstSlot0,
          rDataSubstSlot0_apply_of_not_mem _ _ _ _ hnot0]
      rfl
    have hq : (fun i : Fin 6 ↦
          basisBits ((kFull80 + 18) + 18) x
            ((selAAZ_Subst.compose rPosCoreInFull)
              (rHeadFine21 (QRegExt.ofFin posCoreWires)
                ⟨7 * w.val + i.val + 1, by have := w.isLt; have := i.isLt; omega⟩))) =
        (fun i : Fin 6 ↦
          basisBits (3 + 21) (rCore24_AAZ.extractIndex x)
            (Fin.natAdd 3 ⟨7 * w.val + i.val + 1, by have := w.isLt; have := i.isLt; omega⟩)) := by
      funext i
      rw [← h24 (Fin.natAdd 3 ⟨7 * w.val + i.val + 1, by have := w.isLt; have := i.isLt; omega⟩)]
      dsimp only [rCore24InPos]; rw [QRegister.concat_apply_right]
    have hb0 : basisBits ((kFull80 + 18) + 18) x
          ((selAAZ_Subst.compose rPosCoreInFull) (rCosetB0 (QRegExt.ofFin posCoreWires) w)) =
        basisBits (3 + 21) (rCore24_AAZ.extractIndex x) (Fin.castAdd 21 w) := by
      rw [← h24 (Fin.castAdd 21 w)]; dsimp only [rCore24InPos]; rw [QRegister.concat_apply_left]
    have hd0 : basisBits ((kFull80 + 18) + 18) x
          ((selAAZ_Subst.compose rPosCoreInFull)
            (rHeadFine21 (QRegExt.ofFin posCoreWires) ⟨7 * w.val, by have := w.isLt; omega⟩)) =
        basisBits (3 + 21) (rCore24_AAZ.extractIndex x)
          (Fin.natAdd 3 ⟨7 * w.val, by have := w.isLt; omega⟩) := by
      rw [← h24 (Fin.natAdd 3 ⟨7 * w.val, by have := w.isLt; omega⟩)]
      dsimp only [rCore24InPos]; rw [QRegister.concat_apply_right]
    dsimp only [w, j] at hy hq hb0 hd0 ⊢
    rw [hy, hq, hb0, hd0]
  unfold D_carry_AAZ
  exact diagonal_eq_sum_proj_embed_diagonal_part4 selAAZ_Anc rCore24_AAZ
    carryIdx18_AAZ carryIdxOfAncAnd24 u hCarryEq
open Classical in
theorem uMid5_AAZ_comm_D_carry_on_P218 (u : Fin (2 ^ 18)) : ((uPhiAnc_AAZ⁻¹ * (uStr218_AAZ *
    (uHeadAnc_AAZ * uStr218_AAZ⁻¹))) * uPhiAnc_AAZ).1 * (D_carry_AAZ u * P218_AAZ) =
    D_carry_AAZ u * (((uPhiAnc_AAZ⁻¹ * (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))) *
    uPhiAnc_AAZ).1 * P218_AAZ) := by
  let rCS := selAAZ_Data.compose rCSFull80
  let rCore24_AAZ := (selAAZ_Data.compose rPosCoreInFull).compose rCore24InPos
  let rCore24InCS : QRegister (3 + 21) (fullSysCoreWires 80 + 42) :=
    (rCoreInCoreSum42 80).compose (selPosCoreInCore80.compose rCore24InPos)
  have hCore24_eq_CS : rCS.compose rCore24InCS = rCore24_AAZ := by
    dsimp only [rCS, rCore24InCS, rCore24_AAZ, rPosCoreInFull]
    rw [← QRegister.compose_assoc rCS (rCoreInCoreSum42 80),
        QRegister.compose_assoc selAAZ_Data rCSFull80 (rCoreInCoreSum42 80),
        rCSFull80_compose_rCoreInCoreSum42_eq,
        ← QRegister.compose_assoc (selAAZ_Data.compose rCoreFull) selPosCoreInCore80 rCore24InPos,
        QRegister.compose_assoc selAAZ_Data rCoreFull selPosCoreInCore80]
  have hCore24InCS_val : ∀ t : Fin (3 + 21),
      (rCore24InCS t).val = (rCore24InPos t).val := fun t ↦ by
    simp [rCore24InCS, rCoreInCoreSum42, selPosCoreInCore80]
  have hHeldDisjAnc := selAAZ_HeldAct_disj_Anc
  have hHeadUnf := uHeadAnc_AAZ_eq_F_conj
  obtain ⟨_, _, _, hPhiP218, _, _⟩ := uCSDiag_comm_AAZ (stream42DiagFn slot2AxisSum)
  rw [P218_AAZ_eq_diag] at hPhiP218
  -- Commutation of a single term `A_a * B_d`
  have hTermComm : ∀ (a : Fin (2 ^ 18)) (d : Fin (2 ^ (3 + 21)) → ℂ),
      let A := selAAZ_Anc.basisOutcomeProjector a
      let B := rCore24_AAZ.embedMatrix (Matrix.diagonal d)
      ((uPhiAnc_AAZ⁻¹ * (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))) * uPhiAnc_AAZ).1 *
          ((A * B) * P218_AAZ) =
        (A * B) *
          (((uPhiAnc_AAZ⁻¹ * (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))) * uPhiAnc_AAZ).1 *
            P218_AAZ) := by
    intro a d A B
    have hPhiA : uPhiAnc_AAZ.1 * A = A * uPhiAnc_AAZ.1 :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZ_HeldAct) selAAZ_Anc
        hHeldDisjAnc _ a
    have hPhiIA : (uPhiAnc_AAZ⁻¹).1 * A = A * (uPhiAnc_AAZ⁻¹).1 :=
      unitary_val_inv_comm_of_comm uPhiAnc_AAZ hPhiA
    have hB_CS : B = rCS.embedMatrix (rCore24InCS.embedMatrix (Matrix.diagonal d)) := by
      dsimp only [B]; rw [← hCore24_eq_CS, QRegister.embedMatrix_compose]
    have hPhiB : uPhiAnc_AAZ.1 * B = B * uPhiAnc_AAZ.1 ∧
        (uPhiAnc_AAZ⁻¹).1 * B = B * (uPhiAnc_AAZ⁻¹).1 := by
      obtain ⟨_, _, _, h1, h2, _⟩ := uCSDiag_comm_AAZ (fun y ↦ d (rCore24InCS.extractIndex y))
      have hdEq : rCS.embedMatrix (Matrix.diagonal (fun y ↦ d (rCore24InCS.extractIndex y))) = B :=
        by
        rw [hB_CS, embedMatrix_diagonal_local rCore24InCS d]
      rw [hdEq] at h1 h2; exact ⟨h1, h2⟩
    have hStrA : uStr218_AAZ.1 * A = A * uStr218_AAZ.1 :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) selAAZ_Anc
        (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right rCSFull80)) _ a
    have hStrIA : (uStr218_AAZ⁻¹).1 * A = A * (uStr218_AAZ⁻¹).1 :=
      unitary_val_inv_comm_of_comm uStr218_AAZ hStrA
    let S0 := (selAAZ_AA.embedUnitary uSlot0MeasSwap).1
    let Bar := (selAAZ_AA.embedUnitary uBarrelFastAct).1
    have hS0Sq : S0 * S0 = 1 := by
      dsimp only [S0]
      rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uSlot0MeasSwap_mul_self,
          QRegister.embedUnitary_one, OneMemClass.coe_one]
    -- `uHeadAnc_AAZ` commutes with `A`
    have hHeadA : uHeadAnc_AAZ.1 * A = A * uHeadAnc_AAZ.1 := by
      let P0_slot0 := (selAAZ_Data.compose rSlot0InFull).basisOutcomeProjector a
      have hBarA : Bar * A = A * Bar := by
        dsimp only [Bar, A]; rw [uBarrelFastAct_eq_embedData_rCoreFull, QRegister.embedUnitary_val,
            QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose]
        exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZ_Data) selAAZ_Anc
          (QRegExt.disjointWires_symm selAAZ_Anc_disj_Data) _ a
      have hS0Conj : S0 * P0_slot0 * S0 = A := by
        have hSub0 : (selSubstSlot0 rSlot0InFull).compose rSlot0InFull = selMeasInAct kFull80 := by
          apply qreg_ext; intro q
          rw [QRegister.compose_apply, selSubstSlot0, rDataSubstSlot0_apply_slot0]
        have hConj0 :=
          embedMatrix_selSubstSlot0_eq rSlot0InFull (rSlot0InFull.basisOutcomeProjector a)
        rw [embedMatrix_basisOutcomeProjector_gen_part4, hSub0,
            embedMatrix_basisOutcomeProjector_gen_part4] at hConj0
        have hEmb := congrArg selAAZ_AA.embedMatrix hConj0
        rw[embedMatrix_basisOutcomeProjector_gen_part4, QRegister.embedMatrix_mul,
            QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val,
            embedMatrix_basisOutcomeProjector_gen_part4,
            ← QRegister.compose_assoc selAAZ_AA] at hEmb
        exact hEmb.symm
      have hFinvA : Finv_AAZ.1 * A = P0_slot0 * Finv_AAZ.1 := by
        have hFinvDef : Finv_AAZ.1 = S0 * Bar := by
          rw [Finv_AAZ.eq_1, QRegister.embedUnitary_mul, Submonoid.coe_mul]
        rw [hFinvDef, ← hS0Conj]
        calc (S0 * Bar) * (S0 * P0_slot0 * S0)
            = S0 * ((Bar * (S0 * P0_slot0 * S0))) := by simp only [Matrix.mul_assoc]
          _ = S0 * ((S0 * P0_slot0 * S0) * Bar) := by rw [hS0Conj, hBarA]
          _ = (S0 * S0) * P0_slot0 * (S0 * Bar) := by simp only [Matrix.mul_assoc]
          _ = P0_slot0 * (S0 * Bar) := by rw [hS0Sq, Matrix.one_mul]
      have hFA : F_AAZ.1 * P0_slot0 = A * F_AAZ.1 := by
        have hFDef : F_AAZ.1 = Bar * S0 := by
          rw [F_AAZ.eq_1, QRegister.embedUnitary_mul, Submonoid.coe_mul]
        rw [hFDef]
        calc (Bar * S0) * P0_slot0
            = Bar * ((S0 * P0_slot0 * S0) * S0) := by
                simp only [Matrix.mul_assoc, hS0Sq, Matrix.mul_one]
          _ = (Bar * A) * S0 := by rw [hS0Conj]; simp only [Matrix.mul_assoc]
          _ = A * (Bar * S0) := by rw [hBarA, Matrix.mul_assoc]
      have hSlot0Pos : rPosCoreInFull.compose (rElecSlot (QRegExt.ofFin posCoreWires) 0) =
        rSlot0InFull := by
        apply qreg_ext; intro q
        dsimp only [rPosCoreInFull, rSlot0InFull]
        apply congrArg rCoreFull; apply Fin.ext
        rw [rSlot0InCore, rFullSysElecSlot_val]
        simp [selPosCoreInCore80, rElecSlot0_ofFin_val_assoc]
      have hDataP0 : uHeadData_AAZ.1 * P0_slot0 = P0_slot0 * uHeadData_AAZ.1 := by
        have hP0Eq : P0_slot0 = (selAAZ_Data.compose rPosCoreInFull).embedMatrix ((rElecSlot
            (QRegExt.ofFin posCoreWires) 0).basisOutcomeProjector a) := by
          dsimp only [P0_slot0]
          rw [embedMatrix_basisOutcomeProjector_gen_part4,
              QRegister.compose_assoc selAAZ_Data rPosCoreInFull
                (rElecSlot (QRegExt.ofFin posCoreWires) 0),
              hSlot0Pos]
        let rE0 := rElecSlot (QRegExt.ofFin posCoreWires) 0
        let g0 : Fin (2 ^ posCoreWires) → ℂ := fun x ↦ if rE0.extractIndex x = a then 1 else 0
        have hCore0 : uHeadConjHCore.1 * rE0.basisOutcomeProjector a =
            rE0.basisOutcomeProjector a * uHeadConjHCore.1 := by
          rw [QRegister.basisOutcomeProjector_eq_diagonal]
          exact uHeadConjHCore_comm_diagonal g0
            (fun x y hOut ↦ by
              have hex : rE0.extractIndex x = rE0.extractIndex y :=
                extractIndex_eq_of_basisBits_eq_assoc rE0 fun q ↦
                  agreeOutside_rSpectatorElec3906InCore_nonSpec hOut
                    (Or.inl (by
                      dsimp only [rE0]; rw [rElecSlot0_ofFin_val_assoc]; have := q.isLt; omega))
              dsimp only [g0]; rw [hex])
            (fun x y hNe ↦ by
              have hex : rE0.extractIndex x = rE0.extractIndex y :=
                extractIndex_eq_of_basisBits_eq_assoc rE0 fun q ↦
                  hNe _ (fun h ↦ by
                    have hv := congrArg Fin.val h
                    dsimp only [rE0] at hv
                    rw [rElecSlot0_ofFin_val_assoc, wHeadThresh_ofFin_val_assoc] at hv
                    have := q.isLt; omega)
              dsimp only [g0]; rw [hex])
        rw [hP0Eq]; unfold uHeadData_AAZ
        rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hCore0,
          QRegister.embedMatrix_mul]
      rw [hHeadUnf]
      calc (F_AAZ * uHeadData_AAZ * Finv_AAZ).1 * A
          = F_AAZ.1 * (uHeadData_AAZ.1 * (Finv_AAZ.1 * A)) := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = (F_AAZ.1 * P0_slot0) * uHeadData_AAZ.1 * Finv_AAZ.1 := by
              rw [hFinvA, ← Matrix.mul_assoc uHeadData_AAZ.1, hDataP0]; simp only [Matrix.mul_assoc]
        _ = A * (F_AAZ * uHeadData_AAZ * Finv_AAZ).1 := by
              rw [hFA]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    -- `uHeadAnc_AAZ` commutes with `B`
    have hHeadB : uHeadAnc_AAZ.1 * B = B * uHeadAnc_AAZ.1 := by
      have hS0B : S0 * B = B * S0 := by
        let M_full := (rPosCoreInFull.compose rCore24InPos).embedMatrix (Matrix.diagonal d)
        have hSubEq : (selSubstSlot0 rSlot0InFull).embedMatrix M_full =
            (selDataInAct kFull80).embedMatrix M_full := by
          dsimp only [M_full]
          rw [← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose]
          refine embedMatrix_congr_reg_part4 (qreg_ext fun t ↦ ?_) (Matrix.diagonal d)
          rw [QRegister.compose_apply, QRegister.compose_apply, selSubstSlot0]
          exact rDataSubstSlot0_apply_of_not_mem _ _ _ _ (fun ⟨q, hq⟩ ↦ by
            have hv := congrArg Fin.val (rCoreFull.wires.injective hq)
            have hb := (rCore24InPos_val_bounds t).1
            have := q.isLt
            rw [rSlot0InCore, rFullSysElecSlot_val] at hv
            simp [selPosCoreInCore80] at hv; omega)
        have hConj0 := embedMatrix_selSubstSlot0_eq rSlot0InFull M_full
        rw [hSubEq] at hConj0
        have hEmb := congrArg selAAZ_AA.embedMatrix hConj0
        have hBEq : selAAZ_AA.embedMatrix ((selDataInAct kFull80).embedMatrix M_full) = B := by
          dsimp only [M_full, B, rCore24_AAZ, selAAZ_Data]
          rw [← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose,
              ← QRegister.compose_assoc]
        simp only [QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val, hBEq] at hEmb
        change B = S0 * B * S0 at hEmb
        calc S0 * B = (S0 * B * S0) * S0 := by rw [Matrix.mul_assoc _ S0 S0, hS0Sq, Matrix.mul_one]
          _ = B * S0 := by rw [← hEmb]
      have hBarB : Bar * B = B * Bar := by
        have hBarCore : (uBarrelFast (le_refl 80)).1 *
              (selPosCoreInCore80.compose rCore24InPos).embedMatrix (Matrix.diagonal d) =
            (selPosCoreInCore80.compose rCore24InPos).embedMatrix (Matrix.diagonal d) *
              (uBarrelFast (le_refl 80)).1 := by
          rw [embedMatrix_diagonal_local]
          refine perm_comm_diagonal_of_octKet (uBarrelFast (le_refl 80)).1
            (coinBarrelBitFnFast (le_refl 80)) (uBarrelFast_mulVec_ket_part4 (le_refl 80)) _ fun γ ↦
              ?_
          have hex : (selPosCoreInCore80.compose rCore24InPos).extractIndex
                ((basisBitsEquiv _).symm (coinBarrelBitFnFast (le_refl 80) γ)) =
              (selPosCoreInCore80.compose rCore24InPos).extractIndex ((basisBitsEquiv _).symm γ) :=
            extractIndex_eq_of_basisBits_eq_assoc _ fun t ↦ by
              rw [basisBits_basisBitsEquiv_symm, basisBits_basisBitsEquiv_symm]
              exact swapElec0Bits_high _ γ _ (by
                have hb := (rCore24InPos_val_bounds t).1
                simp [selPosCoreInCore80]; omega)
          rw [hex]
        have hBarEmb : Bar =
          (selAAZ_Data.compose rCoreFull).embedMatrix (uBarrelFast (le_refl 80)).1 := by
          dsimp only [Bar, uBarrelFastAct, selAAZ_Data]
          rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
              ← QRegister.embedMatrix_compose, QRegister.compose_assoc]
        have hBEq : B = (selAAZ_Data.compose rCoreFull).embedMatrix
            ((selPosCoreInCore80.compose rCore24InPos).embedMatrix (Matrix.diagonal d)) := by
          dsimp only [B, rCore24_AAZ, rPosCoreInFull]
          rw [← QRegister.embedMatrix_compose,
              QRegister.compose_assoc selAAZ_Data (rCoreFull.compose selPosCoreInCore80)
                rCore24InPos,
              QRegister.compose_assoc rCoreFull selPosCoreInCore80 rCore24InPos,
              ← QRegister.compose_assoc selAAZ_Data rCoreFull
                (selPosCoreInCore80.compose rCore24InPos)]
        rw [hBarEmb, hBEq, ← QRegister.embedMatrix_mul, hBarCore, QRegister.embedMatrix_mul]
      have hFB : F_AAZ.1 * B = B * F_AAZ.1 ∧ Finv_AAZ.1 * B = B * Finv_AAZ.1 := by
        have hFDef : F_AAZ.1 = Bar * S0 := by
          rw [F_AAZ.eq_1, QRegister.embedUnitary_mul, Submonoid.coe_mul]
        have hFinvDef : Finv_AAZ.1 = S0 * Bar := by
          rw [Finv_AAZ.eq_1, QRegister.embedUnitary_mul, Submonoid.coe_mul]
        exact ⟨by rw [hFDef, Matrix.mul_assoc, hS0B, ← Matrix.mul_assoc, hBarB, Matrix.mul_assoc],
               by rw [hFinvDef, Matrix.mul_assoc, hBarB, ← Matrix.mul_assoc, hS0B,
                 Matrix.mul_assoc]⟩
      have hDataB : uHeadData_AAZ.1 * B = B * uHeadData_AAZ.1 := by
        let g24 : Fin (2 ^ posCoreWires) → ℂ := fun x ↦ d (rCore24InPos.extractIndex x)
        have hCore24 : uHeadConjHCore.1 * rCore24InPos.embedMatrix (Matrix.diagonal d) =
            rCore24InPos.embedMatrix (Matrix.diagonal d) * uHeadConjHCore.1 := by
          rw [embedMatrix_diagonal_local]
          exact uHeadConjHCore_comm_diagonal g24
            (fun x y hOut ↦ by
              have hex : rCore24InPos.extractIndex x = rCore24InPos.extractIndex y :=
                extractIndex_eq_of_basisBits_eq_assoc rCore24InPos fun t ↦
                  agreeOutside_rSpectatorElec3906InCore_nonSpec hOut
                    (Or.inr (by have hb := (rCore24InPos_val_bounds t).1; omega))
              dsimp only [g24]; rw [hex])
            (fun x y hNe ↦ by
              have hex : rCore24InPos.extractIndex x = rCore24InPos.extractIndex y :=
                extractIndex_eq_of_basisBits_eq_assoc rCore24InPos fun t ↦
                  hNe _ (fun h ↦ (rCore24InPos_val_bounds t).2.2 (by
                    rw [congrArg Fin.val h, wHeadThresh_ofFin_val_assoc]))
              dsimp only [g24]; rw [hex])
        dsimp only [B, rCore24_AAZ]; unfold uHeadData_AAZ
        rw [QRegister.embedMatrix_compose, QRegister.embedUnitary_val,
            ← QRegister.embedMatrix_mul, hCore24, QRegister.embedMatrix_mul]
      rw [hHeadUnf]
      calc (F_AAZ * uHeadData_AAZ * Finv_AAZ).1 * B
          = F_AAZ.1 * (uHeadData_AAZ.1 * (Finv_AAZ.1 * B)) := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = (F_AAZ.1 * B) * uHeadData_AAZ.1 * Finv_AAZ.1 := by
              rw [hFB.2, ← Matrix.mul_assoc uHeadData_AAZ.1, hDataB]; simp only [Matrix.mul_assoc]
        _ = B * (F_AAZ * uHeadData_AAZ * Finv_AAZ).1 := by
              rw [hFB.1]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    -- `uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)` commutes with `A * B` on `P218_AAZ`
    have hMid3AB : (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1 * ((A * B) * P218_AAZ) =
        (A * B) * ((uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1 * P218_AAZ) := by
      let B_CS := rCore24InCS.embedMatrix (Matrix.diagonal d)
      have hCommAdd : (uSlot0Sum42Add 80).1 * B_CS = B_CS * (uSlot0Sum42Add 80).1 :=
        commutesWithReg_uSlot0Sum42Add_of_mid_assoc rCore24InCS
          (fun t ↦ by rw [hCore24InCS_val]; have := (rCore24InPos_val_bounds t).1; omega)
          (fun t ↦ by
            rw [hCore24InCS_val, fullSysCoreWires80_eq_4034_assoc];
            exact (rCore24InPos_val_bounds t).2.1)
          (Matrix.diagonal d)
      have hCommStr217 : (uStr3AxisOfSpec uStream217Spec131).1 * B_CS =
          B_CS * (uStr3AxisOfSpec uStream217Spec131).1 :=
        commutesWithReg_uStr3Axis_of_ge3924_assoc rCore24InCS
          (fun t ↦ by rw [hCore24InCS_val]; have := (rCore24InPos_val_bounds t).1; omega)
          (fun t ↦ by
            rw [hCore24InCS_val, fullSysCoreWires80_eq_4034_assoc];
            exact (rCore24InPos_val_bounds t).2.1)
          uStream217Spec131 (Matrix.diagonal d)
      have hCommP0 : pSum42CoreZero * B_CS = B_CS * pSum42CoreZero := by
        dsimp only [B_CS]; unfold pSum42CoreZero
        rw [QRegister.basisOutcomeProjector_eq_diagonal, embedMatrix_diagonal_local]
        exact diagonal_comm_op_assoc _ _
      have hP218Decomp : P218_AAZ = rCS.embedMatrix eStream218Core *
        rCS.embedMatrix eStream218Coreᴴ := by
        unfold P218_AAZ
        rw [← eStream218Core_mul_conjTranspose, rCS.embedMatrix_mul]
      obtain ⟨hInvCS, hFwdCS⟩ := uStr218_AAZ_steps_of_comm_CS B_CS hCommAdd hCommStr217 hCommP0
      have hInvStep : (uStr218_AAZ⁻¹).1 * (B * rCS.embedMatrix eStream218Core) =
          B * rCS.embedMatrix pSum42CoreZero := by
        rw [hB_CS]
        exact hInvCS
      have hFwdStep : uStr218_AAZ.1 * (B * rCS.embedMatrix pSum42CoreZero) =
          B * rCS.embedMatrix eStream218Core := by
        rw [hB_CS]
        exact hFwdCS
      have hInvPlain : (uStr218_AAZ⁻¹).1 * rCS.embedMatrix eStream218Core =
          rCS.embedMatrix pSum42CoreZero := by
        unfold uStr218_AAZ
        rw [← QRegister.embedUnitary_inv, QRegister.embedUnitary_val, ← rCS.embedMatrix_mul,
            inv_uStr218_3Axis_mul_eStream218Core_eq_pSum42CoreZero]
      have hFwdPlain : uStr218_AAZ.1 * rCS.embedMatrix pSum42CoreZero =
          rCS.embedMatrix eStream218Core := by
        unfold uStr218_AAZ
        rw [QRegister.embedUnitary_val, ← rCS.embedMatrix_mul,
            uStr218_3Axis_mul_pSum42CoreZero_eq_eStream218Core]
      have hP0Eq : rCS.embedMatrix pSum42CoreZero =
          (selAAZ_Data.compose rSum0).basisOutcomeProjector 0 := by
        rw [pSum42CoreZero, embedMatrix_basisOutcomeProjector_gen_part4]
        apply congrArg (fun r : QRegister 42 ((kFull80 + 18) + 18) ↦ r.basisOutcomeProjector 0)
        apply qreg_ext; intro j
        have hj : rZLoc (fullSysCoreWires 80) 42 j = Fin.natAdd (fullSysCoreWires 80) j :=
          Fin.ext (by simp [rZLoc])
        dsimp only [rCS, rCSFull80]
        rw [QRegister.compose_apply, QRegister.compose_apply, hj, QRegister.concat_apply_right]
        rfl
      have hHeadDisjSum : (selAAZ_AA.compose (selLiftAct rPosCoreInFull)).DisjointWires
          (selAAZ_Data.compose rSum0) := by
        rw [QRegister.disjoint_iff]; intro idx j heq
        revert idx heq
        refine Fin.addCases (fun i heq ↦ ?_) (fun q heq ↦ ?_)
        · dsimp only [selLiftAct] at heq
          rw [QRegister.compose_apply, QRegister.concat_apply_left] at heq
          exact (rCoreFull_disj_rSum0.compose_left selPosCoreInCore80).ne i j
            ((selDataInAct kFull80).wires.injective (selAAZ_AA.wires.injective heq))
        · dsimp only [selLiftAct] at heq
          rw [QRegister.compose_apply, QRegister.concat_apply_right] at heq
          exact (selAAZ_Anc_disj_Data.compose_right rSum0).ne q j heq
      have hHeadP0 : uHeadAnc_AAZ.1 * rCS.embedMatrix pSum42CoreZero =
          rCS.embedMatrix pSum42CoreZero * uHeadAnc_AAZ.1 := by
        rw [hP0Eq]; unfold uHeadAnc_AAZ; rw [QRegister.embedUnitary_val]
        exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selAAZ_AA.compose
          (selLiftAct rPosCoreInFull)))
          (selAAZ_Data.compose rSum0) hHeadDisjSum _ 0
      rw [hP218Decomp]
      calc (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1 *
              ((A * B) * (rCS.embedMatrix eStream218Core * rCS.embedMatrix eStream218Coreᴴ))
          = uStr218_AAZ.1 * (uHeadAnc_AAZ.1 * (((uStr218_AAZ⁻¹).1 * A) *
              (B * rCS.embedMatrix eStream218Core))) * rCS.embedMatrix eStream218Coreᴴ := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = uStr218_AAZ.1 * ((uHeadAnc_AAZ.1 * A) * (B * rCS.embedMatrix pSum42CoreZero)) *
              rCS.embedMatrix eStream218Coreᴴ := by
              rw [hStrIA, Matrix.mul_assoc A, hInvStep]; simp only [Matrix.mul_assoc]
        _ = (uStr218_AAZ.1 * A) * ((B * rCS.embedMatrix pSum42CoreZero) * uHeadAnc_AAZ.1) *
              rCS.embedMatrix eStream218Coreᴴ := by
              rw [hHeadA, Matrix.mul_assoc A, ← Matrix.mul_assoc uHeadAnc_AAZ.1 B, hHeadB,
                  Matrix.mul_assoc B, hHeadP0]
              simp only [Matrix.mul_assoc]
        _ = A * ((uStr218_AAZ.1 * (B * rCS.embedMatrix pSum42CoreZero)) * uHeadAnc_AAZ.1) *
              rCS.embedMatrix eStream218Coreᴴ := by
              rw [hStrA]; simp only [Matrix.mul_assoc]
        _ = (A * B) * ((uStr218_AAZ.1 * rCS.embedMatrix pSum42CoreZero) * uHeadAnc_AAZ.1) *
              rCS.embedMatrix eStream218Coreᴴ := by
              rw [hFwdStep, ← hFwdPlain]; simp only [Matrix.mul_assoc]
        _ = (A * B) * ((uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1 *
              (rCS.embedMatrix eStream218Core * rCS.embedMatrix eStream218Coreᴴ)) := by
              rw [Matrix.mul_assoc uStr218_AAZ.1, ← hHeadP0, ← hInvPlain]
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    let M3 := (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)).1
    have hPhiAB : uPhiAnc_AAZ.1 * (A * B) = (A * B) * uPhiAnc_AAZ.1 := by
      rw [← Matrix.mul_assoc, hPhiA, Matrix.mul_assoc, hPhiB.1, ← Matrix.mul_assoc]
    have hPhiIAB : (uPhiAnc_AAZ⁻¹).1 * (A * B) = (A * B) * (uPhiAnc_AAZ⁻¹).1 := by
      rw [← Matrix.mul_assoc, hPhiIA, Matrix.mul_assoc, hPhiB.2, ← Matrix.mul_assoc]
    calc ((uPhiAnc_AAZ⁻¹ * (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))) * uPhiAnc_AAZ).1 *
            ((A * B) * P218_AAZ)
        = (uPhiAnc_AAZ⁻¹).1 * (M3 * ((uPhiAnc_AAZ.1 * (A * B)) * P218_AAZ)) := by
            simp only [M3, Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (uPhiAnc_AAZ⁻¹).1 * (M3 * ((A * B) * P218_AAZ) * uPhiAnc_AAZ.1) := by
            rw [hPhiAB, Matrix.mul_assoc (A * B), hPhiP218]; simp only [Matrix.mul_assoc]
      _ = ((uPhiAnc_AAZ⁻¹).1 * (A * B)) * (M3 * (P218_AAZ * uPhiAnc_AAZ.1)) := by
            dsimp only [M3]; rw [hMid3AB]; simp only [Matrix.mul_assoc]
      _ = (A * B) *
            (((uPhiAnc_AAZ⁻¹ * (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))) * uPhiAnc_AAZ).1 *
              P218_AAZ) := by
            rw [hPhiIAB, ← hPhiP218]; dsimp only [M3];
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  rw [D_carry_AAZ_eq_sum_anc_core24 u, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  exact hTermComm a (fun c ↦ if carryIdxOfAncAnd24 a c = u then (1 : ℂ) else 0)
theorem selAAZ_Z_proj0_mul_E_init_AAZ :
    selAAZ_Z.basisOutcomeProjector 0 * E_init_AAZ = E_init_AAZ := by
  unfold E_init_AAZ
  have hComm := ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZ_AA) selAAZ_Z
    (selDataInAct_disj_selMeasInAct (kFull80 + 18)) (E_anchorLoc E_raw217) 0).symm
  rw [← Matrix.mul_assoc, hComm, Matrix.mul_assoc, basisOutcomeProjector_zero_mul_self]
theorem unitary_mul_partial_isom_part4 {D : ℕ} (U : Unitary D) {B : Operator D}
    (hB : (B * Bᴴ) * B = B) : ((U.1 * B) * (U.1 * B)ᴴ) * (U.1 * B) = U.1 * B := by
  have hUU : U.1ᴴ * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  rw [Matrix.conjTranspose_mul]
  calc ((U.1 * B) * (Bᴴ * U.1ᴴ)) * (U.1 * B)
      = U.1 * (B * (Bᴴ * ((U.1ᴴ * U.1) * B))) := by simp only [Matrix.mul_assoc]
    _ = U.1 * ((B * Bᴴ) * B) := by rw [hUU, Matrix.one_mul, Matrix.mul_assoc B Bᴴ B]
    _ = U.1 * B := by rw [hB]
theorem conjTranspose_comm_of_comm_selfAdj_part4 {D : ℕ} {A P : Operator D}
    (hPH : Pᴴ = P) (hComm : A * P = P * A) : P * Aᴴ = Aᴴ * P := by
  have h := congrArg (·ᴴ) hComm
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH] at h
theorem partial_isom_mul_proj_part4 {D : ℕ} {A P : Operator D}
    (hA : (A * Aᴴ) * A = A) (hPH : Pᴴ = P) (hPI : P * P = P) (hComm : A * P = P * A) :
    ((A * P) * (A * P)ᴴ) * (A * P) = A * P := by
  have hCommH : P * Aᴴ = Aᴴ * P := conjTranspose_comm_of_comm_selfAdj_part4 hPH hComm
  rw [Matrix.conjTranspose_mul, hPH]
  calc ((A * P) * (P * Aᴴ)) * (A * P)
      = A * ((P * P) * Aᴴ) * (A * P) := by simp only [Matrix.mul_assoc]
    _ = A * ((Aᴴ * P) * (A * P)) := by rw [hPI, hCommH, Matrix.mul_assoc]
    _ = ((A * Aᴴ) * A) * (P * P) := by
          rw [Matrix.mul_assoc Aᴴ P (A * P), ← Matrix.mul_assoc P A P, ← hComm];
            simp only [Matrix.mul_assoc]
    _ = A * P := by rw [hA, hPI]
theorem E_init_AAZ_mul_conjTranspose_mul_self :
    (E_init_AAZ * E_init_AAZᴴ) * E_init_AAZ = E_init_AAZ := by
  have hP0 : (pSum42CoreZero * pSum42CoreZeroᴴ) * pSum42CoreZero = pSum42CoreZero := by
    unfold pSum42CoreZero
    rw [QRegister.basisOutcomeProjector_conjTranspose, basisOutcomeProjector_zero_mul_self,
        basisOutcomeProjector_zero_mul_self]
  have hE217 : (eStream217Core * eStream217Coreᴴ) * eStream217Core = eStream217Core := by
    rw [← uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core]
    exact unitary_mul_partial_isom_part4 (uStr3AxisOfSpec uStream217Spec131) hP0
  have hERaw : (E_raw217 * E_raw217ᴴ) * E_raw217 = E_raw217 := by
    unfold E_raw217
    rw [← QRegister.embedMatrix_conjTranspose, ← rCSFull80.embedMatrix_mul,
        ← rCSFull80.embedMatrix_mul, hE217]
  let ED := (selDataInAct kFull80).embedMatrix E_raw217
  have hED : (ED * EDᴴ) * ED = ED := by
    dsimp only [ED]
    rw [← QRegister.embedMatrix_conjTranspose, ← (selDataInAct kFull80).embedMatrix_mul,
        ← (selDataInAct kFull80).embedMatrix_mul, hERaw]
  have hEDP : ((ED * P_anc0) * (ED * P_anc0)ᴴ) * (ED * P_anc0) = ED * P_anc0 :=
      partial_isom_mul_proj_part4 hED (QRegister.basisOutcomeProjector_conjTranspose _ 0)
      (basisOutcomeProjector_zero_mul_self _) (selDataInAct_embedMatrix_comm_P_anc0 E_raw217)
  have hLoc : (E_anchorLoc E_raw217 * (E_anchorLoc E_raw217)ᴴ) * E_anchorLoc E_raw217 =
      E_anchorLoc E_raw217 := by
    unfold E_anchorLoc
    exact unitary_mul_partial_isom_part4 (uBarrelFastAct * uSlot0MeasSwap) hEDP
  let EA := selAAZ_AA.embedMatrix (E_anchorLoc E_raw217)
  have hEA : (EA * EAᴴ) * EA = EA := by
    dsimp only [EA]
    rw [← QRegister.embedMatrix_conjTranspose, ← selAAZ_AA.embedMatrix_mul,
        ← selAAZ_AA.embedMatrix_mul, hLoc]
  unfold E_init_AAZ
  exact partial_isom_mul_proj_part4 hEA (QRegister.basisOutcomeProjector_conjTranspose _ 0)
    (basisOutcomeProjector_zero_mul_self _)
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZ_AA) selAAZ_Z
    (selDataInAct_disj_selMeasInAct (kFull80 + 18)) _ 0)
open Classical in
theorem uBarrelAndSlot0_comm_pPGIdle11 :
    let P11 := (selDataInAct kFull80).embedMatrix (pPGIdleZero 11 (by decide))
    uBarrelFastAct.1 * P11 = P11 * uBarrelFastAct.1 ∧
    uSlot0MeasSwap.1 * P11 = P11 * uSlot0MeasSwap.1 := by
  intro P11
  have hP11 : P11 = ((selDataInAct kFull80).compose (rPGIdle 11 (by
    decide))).basisOutcomeProjector 0 := by
    dsimp only [P11]; unfold pPGIdleZero
    exact embedMatrix_basisOutcomeProjector_zero_assoc (selDataInAct kFull80) (rPGIdle 11 (by
      decide))
  rw [hP11]
  refine ⟨?_, ?_⟩
  · unfold uBarrelFastAct
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint ((selDataInAct
      kFull80).compose rCoreFull))
      _ (disjointWires_compose_of_disjoint (selDataInAct kFull80) rCoreFull_disj_rPGIdle11) _ 0
  · have hEq : uSlot0MeasSwap =
        (selLiftAct rSlot0InFull).embedUnitary (uLensSwap (L_slot0Of (QRegExt.idReg 18))) := by
      rw [uSlot0MeasSwap, L_slot0, ← uLensSwap_L_slot0Of_eq_embed18 rSlot0InFull]
    have hDisj : (selLiftAct rSlot0InFull).DisjointWires
        ((selDataInAct kFull80).compose (rPGIdle 11 (by decide))) :=
      disjointWires_concat_left _
        (disjointWires_compose_of_disjoint (selDataInAct kFull80) rSlot0InFull_disj_rPGIdle11)
        (QRegExt.disjointWires_symm ((selDataInAct_disj_selMeasInAct kFull80).compose_left (rPGIdle
          11 (by decide))))
    rw [hEq]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selLiftAct rSlot0InFull)) _
      hDisj _ 0
theorem E_init_AAZ_comm_pPGIdle11 :
    let P_idle_AAZ := (selAAZ_Data.compose (rPGIdle 11 (by decide))).basisOutcomeProjector 0
    E_init_AAZ * P_idle_AAZ = P_idle_AAZ * E_init_AAZ ∧
    (E_init_AAZ * E_init_AAZᴴ) * P_idle_AAZ = P_idle_AAZ * (E_init_AAZ * E_init_AAZᴴ) := by
  intro P_idle_AAZ
  obtain ⟨hBar, hS0⟩ := uBarrelAndSlot0_comm_pPGIdle11
  let P11 := (selDataInAct kFull80).embedMatrix (pPGIdleZero 11 (by decide))
  change uBarrelFastAct.1 * P11 = P11 * uBarrelFastAct.1 at hBar
  change uSlot0MeasSwap.1 * P11 = P11 * uSlot0MeasSwap.1 at hS0
  have hCS_Idle : rCSFull80.DisjointWires (rPGIdle 11 (by decide)) :=
    disjointWires_concat_left _ rCoreFull_disj_rPGIdle11 (hSum0_disj_PGIdle 11 (by decide))
  have hERaw : E_raw217 * pPGIdleZero 11 (by decide) = pPGIdleZero 11 (by decide) * E_raw217 := by
    unfold E_raw217 pPGIdleZero
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCSFull80) _ hCS_Idle _ 0
  have hED : (selDataInAct kFull80).embedMatrix E_raw217 * P11 =
      P11 * (selDataInAct kFull80).embedMatrix E_raw217 := by
    dsimp only [P11]
    rw [← (selDataInAct kFull80).embedMatrix_mul, hERaw, (selDataInAct kFull80).embedMatrix_mul]
  have hPanc : P_anc0 * P11 = P11 * P_anc0 :=
    (selDataInAct_embedMatrix_comm_P_anc0 (pPGIdleZero 11 (by decide))).symm
  have hLoc : E_anchorLoc E_raw217 * P11 = P11 * E_anchorLoc E_raw217 := by
    unfold E_anchorLoc
    simp only [Submonoid.coe_mul]
    calc (uBarrelFastAct.1 * uSlot0MeasSwap.1) *
            ((selDataInAct kFull80).embedMatrix E_raw217 * P_anc0) * P11
        = uBarrelFastAct.1 * (uSlot0MeasSwap.1 *
            ((selDataInAct kFull80).embedMatrix E_raw217 * (P_anc0 * P11))) := by
            simp only [Matrix.mul_assoc]
      _ = P11 * ((uBarrelFastAct.1 * uSlot0MeasSwap.1) *
            ((selDataInAct kFull80).embedMatrix E_raw217 * P_anc0)) := by
            rw [hPanc, ← Matrix.mul_assoc _ P11, hED, Matrix.mul_assoc P11,
                ← Matrix.mul_assoc uSlot0MeasSwap.1 P11, hS0, Matrix.mul_assoc P11,
                ← Matrix.mul_assoc uBarrelFastAct.1 P11, hBar]
            simp only [Matrix.mul_assoc]
  have hPIdleEq : selAAZ_AA.embedMatrix P11 = P_idle_AAZ := by
    dsimp only [P11, P_idle_AAZ, selAAZ_Data]; unfold pPGIdleZero
    rw [← QRegister.embedMatrix_compose, embedMatrix_basisOutcomeProjector_zero_assoc]
  have hEA : selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) * P_idle_AAZ =
      P_idle_AAZ * selAAZ_AA.embedMatrix (E_anchorLoc E_raw217) := by
    rw [← hPIdleEq, ← selAAZ_AA.embedMatrix_mul, hLoc, selAAZ_AA.embedMatrix_mul]
  have hPZ : selAAZ_Z.basisOutcomeProjector 0 * P_idle_AAZ =
      P_idle_AAZ * selAAZ_Z.basisOutcomeProjector 0 := by
    dsimp only [P_idle_AAZ]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal]
    exact diagonal_comm_op_assoc _ _
  have hE : E_init_AAZ * P_idle_AAZ = P_idle_AAZ * E_init_AAZ := by
    unfold E_init_AAZ
    rw [Matrix.mul_assoc, hPZ, ← Matrix.mul_assoc, hEA, Matrix.mul_assoc]
  refine ⟨hE, ?_⟩
  have hEH : E_init_AAZᴴ * P_idle_AAZ = P_idle_AAZ * E_init_AAZᴴ :=
    (conjTranspose_comm_of_comm_selfAdj_part4
      (QRegister.basisOutcomeProjector_conjTranspose _ 0) hE).symm
  rw [Matrix.mul_assoc, hEH, ← Matrix.mul_assoc, hE, Matrix.mul_assoc]
attribute [irreducible]
  uSw_AAZ uXorSubst_AAZ uXorData_AAZ uPhiAnc_AAZ uPhi217_AAZ uStr218_AAZ uStr217_AAZ
  uHeadAnc_AAZ uHeadData_AAZ Pc2_AAZ P218_AAZ P217_AAZ P_anc_AAZ E_init_AAZ E_base_AAZ
  E_raw217 uInnerSwapFull
end Part4_AnchorStageA48062
end StageADeconstrAndQftShare
end SharedScope
end
end StageAAAZUnitaryEquiv

end QuantumComputation.Specs.StoppingPowerSolution
end
