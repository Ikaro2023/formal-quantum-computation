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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Barrel3PassStitch

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosSlots24UnbarreledWide
local instance (priority := 1000000) instNeZeroTwoPow_PosSlots24UnbarreledWide (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Unbarreled `262`-Clean-Wire `Pass 2` Leaf (`PosSlots24UnbarreledWide`)

Implements the `262`-clean-wire `Pass 2` leaf (`56,032 T` =
`(8,688 + 840) + (22,072 + 24,432)`, `0` `.TOFF`, `262 <= mWB`) over `AnchorCode26Path3A`,
`PosHeadWithAnchor26_236` (`C = 125`, `236w`), and `PosTailWithAnchor18_244` (`k_drop = 3`
nearest-multiple-of-8 `roundTailMag27` / `liftTailMag27`, `244w`):

1. **Convention-B & `26`-Wire Pre-Load Equivalence**:
   - Exact ket-level Convention-B equivalence (`headConvBPhaseBitSpec_eq_headPhaseBitSpec_convB`,
     `posPhaseBit_effectiveSwap0Bits_convB`, `posAnchor18PhaseBit_convB`) and `26`-wire
     `(rAnchor18, rCode8)` pre-load bridges
     (`headConvB26PhaseBitSpec_eq_headConvBPhaseBitSpec_of_codeTbl`,
     `headAnchor26_xor_tailAnchor18_convB`).
2. **2-Stage `X`-Reset `swap0` Core & `CTLeafSpec` (`262 <= mWB`, `56,032 T`, `0` `.TOFF`)**:
   - `dAnchorSwap0Path3AGen262`, `dPass2Path3ACore262`, `pass2Path3ASpec262Gen`, `pass2SpecOfLe`,
     and `pass2Spec262` (`tLeaf = 56,032`, `0` `.TOFF`), realizing `uPass2UnbarreledEff`.
3. **Turnkey Semantic `PosSlots24Data80 288` (`posDataRound27_288`)**:
   - Zero-extra-DAG `PosSlots24Data80 288` (`posDataPath3AGen288`, `posDataRound27_288`) with
     `(pass2SpecOfLe hmWB).uEff cfg =`
     `unitaryConj (uBarrelFast (le_refl 80)) (posDataRound27_288.uPosPhase cfg)`
     definitionally (`rfl`), plus `slack2`, `slack3`, and `hUPosKet` bridges.
-/

public section

namespace PosSlots24UnbarreledWide

section ConfigPosSlots24UnbarreledWide

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
-- Root solution namespace already active.
open QRegExt
open PosSlots24BranchConcrete

local instance (priority := 1000000)
    instLoc_PosSlots24UnbarreledWide_1InstNeZeroTwoPowUn (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-- Cast a `BitAssignment a` along `h : a = b` without unfolding `2 ^ a`. -/
def castBits {a b : ℕ} (h : a = b) (γ : BitAssignment a) : BitAssignment b :=
  fun w ↦ γ ⟨w.val, h ▸ w.isLt⟩

theorem rElecSlot_ofFin_val (s : Fin 218) (q : Fin 18) :
    (rElecSlot (QRegExt.ofFin posCoreWires) s q).val = 18 * s.val + q.val := by
  revert s q; decide

theorem swapCore3967Fn_high (γ : BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires 80))
    (w : Wire (FullSysCatSegmentBridge.fullSysCoreWires 80)) (hw : w.val ≠ 3967 ∧ w.val ≠ 4029) :
    PosPostPrep80MergedVep.swapCore3967Fn γ w = γ w := by
  dsimp only [PosPostPrep80MergedVep.swapCore3967Fn]
  have h1 : w ≠ PosPostPrep80MergedVep.wCore3967 := fun h ↦ hw.1 (congrArg Fin.val h)
  have h2 : w ≠ PosPostPrep80MergedVep.wCore4029 := fun h ↦ hw.2 (congrArg Fin.val h)
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

set_option maxRecDepth 512

end ConfigPosSlots24UnbarreledWide

end PosSlots24UnbarreledWide

end
set_option exponentiation.threshold 256
end PosSlots24UnbarreledWide

section HarmonicTwoAngleBridge
local instance (priority := 1000000) instNeZeroTwoPow_HarmonicTwoAngleBridge (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
Additive Two-Angle SU(2) Segment, Intertwining & Harmonic Schedule Bridge
(`HarmonicTwoAngleBridge`).

Provides:
1. Generic 1-qubit-gate Bi-GQSP loop/segment operators (`biGqspGenLoopOp`, `biGqspGenSegmentOp`,
   `biCatGenSegmentOp`, `biCatGenSegmentUnitary`, `physBiGenSegmentUnitary`), congruence on
   `j ≤ M`, polymorphic ghost-guard conjugation, and physical ghost-free
   `ApproximatesTimeEvolution`.
2. Canonical 2-angle 1-qubit signal unitary (`twoAngleSigUnitary42`, `twoAngleDiagHMatrix`),
   2-angle Bi-GQSP segment unitaries (`biCatTwoAngleSegmentUnitary`,
   `physBiTwoAngleSegmentUnitaryGen`), and lightweight `TwoAngleGeneralBetaSegmentCert`.
3. `43`-wire and `SingleCat` 2-angle Gidney signal rotations, guard-wrap unitaries, prefix/segment
   unitaries (`uSignalRotTwoAngle43`, `uSigMidTwoAngle43`, `uSignalRotTwoAngleSingleCat`,
   `uGuardWrapTwoAngleSingleCat`, `uSingleGuardPrefixTwoAngleSingleCat`,
   `uSegTwoAngleSingleCat`), exact dual-kick step Toffoli-equivalent cost
   `gidneyTwoAngleRotToffEquiv`, and full catalyst intertwining
   `uSegTwoAngleSingleCat_intertwinesCat`.
4. Parametric and unbundled 2-angle single-catalyst time-slice closures
   (`customSingleCatSeg_of_gridPerturbation_twos_step_gen`,
   `twoAngleSingleCat_of_gridPerturbation_twos_step_gen`).
-/

public section

namespace HarmonicTwoAngleBridge

section ConfigHarmonicTwoAngleBridge

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance instLoc_HarmonicTwoAngleBridge_1InstNeZeroTwoPowTwoA
    (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open PhaseGradSignalRot hiding IntertwinesCat
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open FullSysCatSegmentBridge
open CatalystPrep
open BiGqspSegmentSpine
open PolymorphicTopClosure
open GeneralBetaAndAlphaTopEndpoint
open SingleCatSpine
open SingleCatClosure
open GidneySignalRotPart1

theorem qreg_ext_sched {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)

noncomputable def biGqspGenLoopOp {n : ℕ} (q_sig : Wire n) (W_emb W_inv_emb : Operator (2 ^ n))
    (G : ℕ → Operator 2) : ℕ → Operator (2 ^ n)
  | 0 => (QRegister.singleton q_sig).embedMatrix (G 0)
  | t + 1 =>
      ((QRegister.singleton q_sig).embedMatrix (G (t + 1)) *
        biWalkStepOp q_sig W_emb W_inv_emb) *
      biGqspGenLoopOp q_sig W_emb W_inv_emb G t

/-- Generic Bi-GQSP segment operator with arbitrary 1-qubit signal schedule `G : ℕ → Operator 2`. -/
noncomputable def biGqspGenSegmentOp {n : ℕ} (q_sig : Wire n) (W_emb W_inv_emb : Operator (2 ^ n))
    (G : ℕ → Operator 2) (M : ℕ) : Operator (2 ^ n) :=
  let P_sig0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
  let P_sig1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
  let H_sig := (Circuit.H q_sig).eval.1
  H_sig * (W_inv_emb * P_sig0 + P_sig1) *
    biGqspGenLoopOp q_sig W_emb W_inv_emb G M *
    (P_sig0 + W_emb * P_sig1) * H_sig

theorem embedMatrix_biGqspGenLoopOp {m n : ℕ} (r : QRegister m n) (q_sig : Wire m)
    (W_emb W_inv_emb : Operator (2 ^ m)) (G : ℕ → Operator 2) (t : ℕ) :
    r.embedMatrix (biGqspGenLoopOp q_sig W_emb W_inv_emb G t) =
      biGqspGenLoopOp (r q_sig) (r.embedMatrix W_emb) (r.embedMatrix W_inv_emb) G t := by
  induction t with
  | zero =>
      dsimp only [biGqspGenLoopOp]
      exact embedMatrix_singleton_embedMatrix r q_sig _
  | succ t ih =>
      dsimp only [biGqspGenLoopOp]
      rw [r.embedMatrix_mul, r.embedMatrix_mul, ih,
        embedMatrix_singleton_embedMatrix, embedMatrix_biWalkStepOp]

theorem embedMatrix_biGqspGenSegmentOp {m n : ℕ} (r : QRegister m n) (q_sig : Wire m)
    (W_emb W_inv_emb : Operator (2 ^ m)) (G : ℕ → Operator 2) (M : ℕ) :
    r.embedMatrix (biGqspGenSegmentOp q_sig W_emb W_inv_emb G M) =
      biGqspGenSegmentOp (r q_sig) (r.embedMatrix W_emb) (r.embedMatrix W_inv_emb) G M := by
  unfold biGqspGenSegmentOp
  rw[r.embedMatrix_mul, r.embedMatrix_mul, r.embedMatrix_mul, r.embedMatrix_mul,
      embedMatrix_eval_H, embedMatrix_biGqspGenLoopOp, r.embedMatrix_add, r.embedMatrix_mul,
      r.embedMatrix_add, r.embedMatrix_mul, embedMatrix_singleton_basisOutcomeProjector,
      embedMatrix_singleton_basisOutcomeProjector]

theorem biGqspGenLoopOp_mem_unitaryGroup {n : ℕ} (q_sig : Wire n)
    (W_emb W_inv_emb : Operator (2 ^ n)) (hStep : biWalkStepOp q_sig W_emb W_inv_emb ∈
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (G : ℕ → Operator 2) (t : ℕ)
    (hG : ∀ j ≤ t, G j ∈ Matrix.unitaryGroup (Fin 2) ℂ) : biGqspGenLoopOp q_sig W_emb
    W_inv_emb G t ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  induction t with
  | zero =>
      dsimp only [biGqspGenLoopOp]
      exact ((QRegister.singleton q_sig).embedUnitary ⟨G 0, hG 0 (le_refl 0)⟩).2
  | succ t ih =>
      dsimp only [biGqspGenLoopOp]
      refine Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ hStep)
        (ih (fun j hj ↦ hG j (Nat.le_succ_of_le hj)))
      exact ((QRegister.singleton q_sig).embedUnitary ⟨G (t + 1), hG (t + 1) (le_refl _)⟩).2

theorem add_zero_le_add_succ_sched (k m : ℕ) : 0 + (k + m) ≤ k + (m + 1) := by omega

theorem lt_add_succ_sched (k m : ℕ) : k + m < k + (m + 1) := by omega

theorem rBE_disjoint_qSig_sched (k m : ℕ) :
    (QRegister.block 0 (k + m) (add_zero_le_add_succ_sched k m)).DisjointWires
      (QRegister.singleton (⟨k + m, lt_add_succ_sched k m⟩ : Wire (k + (m + 1)))) := by
  rw [QRegister.disjoint_iff]; intro i j h
  have hv := congrArg Fin.val h; simp [QRegister.singleton] at hv; omega

noncomputable def physBiGenSegmentUnitary {k m : ℕ} (b : Fin (2 ^ k) → Bool) (M : ℕ)
    (G : ℕ → Operator 2) (hG : ∀ j ≤ M, G j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (U_raw : Unitary (2 ^ (k + m))) : Unitary (2 ^ (k + (m + 1))) :=
  let rBE : QRegister (k + m) (k + (m + 1)) :=
    QRegister.block 0 (k + m) (add_zero_le_add_succ_sched k m)
  let q_sig : Wire (k + (m + 1)) := ⟨k + m, lt_add_succ_sched k m⟩
  have hBE_sig : rBE.DisjointWires (QRegister.singleton q_sig) := rBE_disjoint_qSig_sched k m
  have hW_mem : rBE.embedMatrix (physLaurentWalkGen b U_raw) ∈
      Matrix.unitaryGroup (Fin (2 ^ (k + (m + 1)))) ℂ :=
    (rBE.embedUnitary ⟨physLaurentWalkGen b U_raw, physLaurentWalkGen_mem_unitary b U_raw⟩).2
  have hWinv_mem : rBE.embedMatrix (physLaurentWalkInvGen b U_raw) ∈
      Matrix.unitaryGroup (Fin (2 ^ (k + (m + 1)))) ℂ :=
    (rBE.embedUnitary ⟨physLaurentWalkInvGen b U_raw, physLaurentWalkInvGen_mem_unitary b U_raw⟩).2
  have hW_0 := embedMatrix_comm_sig_proj rBE q_sig hBE_sig (physLaurentWalkGen b U_raw) 0
  have hW_1 := embedMatrix_comm_sig_proj rBE q_sig hBE_sig (physLaurentWalkGen b U_raw) 1
  have hWinv_0 := embedMatrix_comm_sig_proj rBE q_sig hBE_sig (physLaurentWalkInvGen b U_raw) 0
  have hWinv_1 := embedMatrix_comm_sig_proj rBE q_sig hBE_sig (physLaurentWalkInvGen b U_raw) 1
  ⟨biGqspGenSegmentOp q_sig
      (rBE.embedMatrix (physLaurentWalkGen b U_raw))
      (rBE.embedMatrix (physLaurentWalkInvGen b U_raw))
      G M,
    Submonoid.mul_mem _
      (Submonoid.mul_mem _
        (Submonoid.mul_mem _
          (Submonoid.mul_mem _ (Circuit.H q_sig).eval.2
            (c0_step_mem_unitaryGroup q_sig _ hWinv_mem hWinv_0))
          (biGqspGenLoopOp_mem_unitaryGroup q_sig _ _
            (biWalkStepOp_mem_unitaryGroup q_sig _ _ hW_mem hWinv_mem hW_0 hWinv_0 hWinv_1)
            G M hG))
        (c1_step_mem_unitaryGroup q_sig _ hW_mem hW_1))
      (Circuit.H q_sig).eval.2⟩

noncomputable def twoAngleSigUnitary42 (C_d D_d : Fin (2 ^ 42)) : Unitary 2 :=
  Qubit.H * (twoPhaseDiagUnitary 42 D_d.val (2 ^ 42 - D_d.val) *
    (Qubit.H * twoPhaseDiagUnitary 42 C_d.val (2 ^ 42 - C_d.val)))

/-- Exact 1-qubit `Operator 2` matrix of `twoAngleSigUnitary42 C_d D_d` (`rfl`-defeq to
`Qubit.H.1 * (twoPhaseDiagMatrix 42 D_d.val (2 ^ 42 - D_d.val) *
  (Qubit.H.1 * twoPhaseDiagMatrix 42 C_d.val (2 ^ 42 - C_d.val)))`). -/
noncomputable abbrev twoAngleDiagHMatrix (C_d D_d : Fin (2 ^ 42)) : Operator 2 :=
  (twoAngleSigUnitary42 C_d D_d).1

theorem twoAngleDiagHMatrix_mem_unitaryGroup (C_d D_d : Fin (2 ^ 42)) : twoAngleDiagHMatrix
    C_d D_d ∈ Matrix.unitaryGroup (Fin 2) ℂ := (twoAngleSigUnitary42 C_d D_d).2

/-- Step-indexed 2-angle 1-qubit gate schedule
`t ↦ twoAngleDiagHMatrix (biCode M C t) (biCode M D t)`. -/
noncomputable abbrev biTwoAngleGate (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (t : ℕ) :
    Operator 2 := twoAngleDiagHMatrix (biCode M C t) (biCode M D t)

theorem biTwoAngleGate_mem_unitaryGroup (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (j : ℕ) :
    biTwoAngleGate M C D j ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  twoAngleDiagHMatrix_mem_unitaryGroup (biCode M C j) (biCode M D j)

/-- Concrete 2-angle Bi-GQSP loop operator. -/
noncomputable abbrev biGqspTwoAngleLoopOp {n : ℕ} (q_sig : Wire n)
    (W_emb W_inv_emb : Operator (2 ^ n)) (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (t : ℕ) :
    Operator (2 ^ n) := biGqspGenLoopOp q_sig W_emb W_inv_emb (biTwoAngleGate M C D) t

noncomputable def physBiTwoAngleSegmentUnitaryGen {k m : ℕ} (b : Fin (2 ^ k) → Bool) (M : ℕ)
    (C D : Fin (M + 1) → Fin (2 ^ 42)) (U_raw : Unitary (2 ^ (k + m))) : Unitary
    (2 ^ (k + (m + 1))) := physBiGenSegmentUnitary b M (biTwoAngleGate M C D)
    (fun j _ ↦ biTwoAngleGate_mem_unitaryGroup M C D j) U_raw

noncomputable def uSignalRotTwoAngle43 (C_d D_d : Fin (2 ^ 42)) : Unitary (2 ^ (1 + 42)) :=
  (Circuit.H ⟨0, by decide⟩).eval *
    (uKickGidney43 D_d * ((Circuit.H ⟨0, by decide⟩).eval * uKickGidney43 C_d))

/-- Active unitary of the 2-angle Gidney `0-rConst42` signal rotation on `kActSingleCatClosure`. -/
noncomputable def uSignalRotTwoAngleSingleCat {mPayload B_tot kWorkConst : ℕ}
    (hB42 : 42 ≤ B_tot) (C_d D_d : Fin (2 ^ 42)) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
  (rMid43InSingleCat mPayload B_tot kWorkConst hB42).embedUnitary (uSignalRotTwoAngle43 C_d D_d)

theorem intertwinesCat_uKickGidney43 (C_d : Fin (2 ^ 42))
    (U_cat_0 : Unitary (2 ^ 42))
    (hU : ∀ m : Fin (2 ^ 42), U_cat_0.1 m 0 = FullScaleBESector.phaseGradientState 42 m) :
    let q0 : Wire (1 + 42) := ⟨0, by decide⟩
    let rSig : QRegister 1 (1 + 42) := QRegister.singleton q0
    let rK0 : QRegister 42 (1 + 42) := QRegister.block 1 42 (by decide)
    PhaseGradSignalRot.IntertwinesCat
      (rK0.embedUnitary U_cat_0).1 (rK0.basisOutcomeProjector 0)
      (uKickGidney43 C_d).1
      (rSig.embedUnitary (twoPhaseDiagUnitary 42 C_d.val (2 ^ 42 - C_d.val))).1 := by
  intro q0 rSig rK0
  let U_pre : Unitary 2 := Qubit.H * (Qubit.Z * Qubit.S)
  let U_post : Unitary 2 := Qubit.S * Qubit.H
  have hPrePost : U_pre * U_post = 1 := by
    calc U_pre * U_post
      _ = Qubit.H * ((Qubit.Z * Qubit.S) * Qubit.S) * Qubit.H := by
            dsimp only [U_pre, U_post]; group
      _ = Qubit.H * (Qubit.S⁻¹ * Qubit.S) * Qubit.H := by rw [Qubit.Z_mul_S_eq_S_inv]
      _ = Qubit.H * Qubit.H := by rw [inv_mul_cancel, mul_one]
      _ = 1 := Qubit.H_sq
  have hPre_eval : cPre43.eval = rSig.embedUnitary U_pre := by
    dsimp only [cPre43, U_pre, rSig, q0]
    rw [rSig.embedUnitary_mul, rSig.embedUnitary_mul]; rfl
  have hPost_eval : cPost43.eval = rSig.embedUnitary U_post := by
    dsimp only [cPost43, U_post, rSig, q0]
    rw [rSig.embedUnitary_mul]; rfl
  have hSigCat : rSig.DisjointWires rK0 := by
    rw [QRegister.disjoint_iff]; intro i j h; fin_cases i
    have hv := congrArg Fin.val h; simp [rSig, q0, rK0, QRegister.singleton] at hv
  have hOne_comm : ∀ M : Operator 2,
      rSig.embedMatrix M * (1 : Operator (2 ^ (1 + 42))) =
        (1 : Operator (2 ^ (1 + 42))) * rSig.embedMatrix M := fun _ ↦ by simp
  have hPre := by
    simpa [mul_one] using intertwinesCat_singleton_q_sig q0 rK0 1 hSigCat hOne_comm U_cat_0 U_pre
  have hPost := by
    simpa [mul_one] using intertwinesCat_singleton_q_sig q0 rK0 1 hSigCat hOne_comm U_cat_0 U_post
  have hRot := intertwinesCat_uSignalRotGidney43 C_d U_cat_0 hU
  dsimp only at hRot
  have hComb := hPre.mul (hRot.mul hPost)
  have hKickEq : (rSig.embedUnitary U_pre).1 *
      ((uSignalRotGidney43 C_d).1 * (rSig.embedUnitary U_post).1) = (uKickGidney43 C_d).1
      := by
    change (rSig.embedUnitary U_pre * (uSignalRotGidney43 C_d * rSig.embedUnitary U_post)).1 = _
    refine congrArg Subtype.val ?_
    rw [uSignalRotGidney43, hPre_eval, hPost_eval]
    calc rSig.embedUnitary U_pre *
            ((rSig.embedUnitary U_post * (uKickGidney43 C_d * rSig.embedUnitary U_pre)) *
              rSig.embedUnitary U_post)
      _ = (rSig.embedUnitary U_pre * rSig.embedUnitary U_post) * uKickGidney43 C_d *
            (rSig.embedUnitary U_pre * rSig.embedUnitary U_post) := by group
      _ = uKickGidney43 C_d := by
            rw [← rSig.embedUnitary_mul, hPrePost, rSig.embedUnitary_one, one_mul, mul_one]
  let θ_d : ℝ := -((4 * Real.pi * (C_d.val : ℝ)) / 2 ^ 42)
  have hLocRot :
      U_post * (twoPhaseDiagUnitary 42 C_d.val (2 ^ 42 - C_d.val) * U_pre) = ryUnitary θ_d := by
    apply Subtype.ext
    change (Qubit.S.1 * Qubit.H.1) * (twoPhaseDiagMatrix 42 C_d.val (2 ^ 42 - C_d.val) *
      (Qubit.H.1 * (Qubit.Z.1 * Qubit.S.1))) = (ryUnitary θ_d).1
    rw [← Matrix.mul_assoc, twoPhaseDiagMatrix_sym 42 C_d.val (le_of_lt C_d.isLt),
      sH_conj_rzDiagMatrix]
    congr 2; dsimp only [θ_d]; ring
  have hLocDiag : U_pre * (ryUnitary θ_d * U_post) = twoPhaseDiagUnitary 42 C_d.val
      (2 ^ 42 - C_d.val) := by
    rw [← hLocRot]
    calc U_pre * ((U_post * (twoPhaseDiagUnitary 42 C_d.val (2 ^ 42 - C_d.val) * U_pre)) * U_post)
      _ = (U_pre * U_post) * twoPhaseDiagUnitary 42 C_d.val (2 ^ 42 - C_d.val) *
            (U_pre * U_post) := by
            group
      _ = twoPhaseDiagUnitary 42 C_d.val (2 ^ 42 - C_d.val) := by
            rw [hPrePost, one_mul, mul_one]
  have hEffEq : (rSig.embedUnitary U_pre).1 * ((rSig.embedUnitary (ryUnitary θ_d)).1 *
      (rSig.embedUnitary U_post).1) = (rSig.embedUnitary (twoPhaseDiagUnitary 42 C_d.val (2 ^
      42 - C_d.val))).1 := by
    rw [← embedUnitary_mul_val, ← embedUnitary_mul_val, hLocDiag]
  rw [← hKickEq, ← hEffEq]
  exact hComb

/-- Catalyst intertwining for `uSignalRotTwoAngle43 C_d D_d` on `1 + 42` wires. -/
theorem intertwinesCat_uSignalRotTwoAngle43 (C_d D_d : Fin (2 ^ 42))
    (U_cat_0 : Unitary (2 ^ 42))
    (hU : ∀ m : Fin (2 ^ 42), U_cat_0.1 m 0 = FullScaleBESector.phaseGradientState 42 m) :
    let q0 : Wire (1 + 42) := ⟨0, by decide⟩
    let rSig : QRegister 1 (1 + 42) := QRegister.singleton q0
    let rK0 : QRegister 42 (1 + 42) := QRegister.block 1 42 (by decide)
    PhaseGradSignalRot.IntertwinesCat
      (rK0.embedUnitary U_cat_0).1 (rK0.basisOutcomeProjector 0)
      (uSignalRotTwoAngle43 C_d D_d).1
      (rSig.embedUnitary (twoAngleSigUnitary42 C_d D_d)).1 := by
  intro q0 rSig rK0
  have hSigCat : rSig.DisjointWires rK0 := by
    rw [QRegister.disjoint_iff]; intro i j h; fin_cases i
    have hv := congrArg Fin.val h; simp [rSig, q0, rK0, QRegister.singleton] at hv
  have hOne_comm : ∀ M : Operator 2,
      rSig.embedMatrix M * (1 : Operator (2 ^ (1 + 42))) =
        (1 : Operator (2 ^ (1 + 42))) * rSig.embedMatrix M := fun _ ↦ by simp
  have hH := by
    simpa [mul_one] using intertwinesCat_singleton_q_sig q0 rK0 1 hSigCat hOne_comm U_cat_0 Qubit.H
  have hKC := intertwinesCat_uKickGidney43 C_d U_cat_0 hU
  have hKD := intertwinesCat_uKickGidney43 D_d U_cat_0 hU
  dsimp only at hKC hKD
  have hComb := hH.mul (hKD.mul (hH.mul hKC))
  have hH_eval : (Circuit.H q0).eval = rSig.embedUnitary Qubit.H := by
    rw [Circuit.H, Circuit.eval_single]; rfl
  have hLHS : (uSignalRotTwoAngle43 C_d D_d).1 = (rSig.embedUnitary Qubit.H).1 *
      ((uKickGidney43 D_d).1 * ((rSig.embedUnitary Qubit.H).1 * (uKickGidney43 C_d).1)) := by
    simp only [uSignalRotTwoAngle43, Submonoid.coe_mul, hH_eval, q0]
  have hRHS : (rSig.embedUnitary Qubit.H).1 * ((rSig.embedUnitary (twoPhaseDiagUnitary 42
      D_d.val (2 ^ 42 - D_d.val))).1 * ((rSig.embedUnitary Qubit.H).1 * (rSig.embedUnitary
      (twoPhaseDiagUnitary 42 C_d.val (2 ^ 42 - C_d.val))).1)) =
      (rSig.embedUnitary (twoAngleSigUnitary42 C_d D_d)).1 := by
    rw [← embedUnitary_mul_val, ← embedUnitary_mul_val, ← embedUnitary_mul_val]
    rfl
  rw [hLHS, ← hRHS]
  exact hComb

/-- Catalyst intertwining for `uSignalRotTwoAngleSingleCat` on `kActSingleCatClosure` for any
`kWorkConst : ℕ`. -/
theorem intertwinesCat_signalRotTwoAngleSingleCat {mPayload B_tot kWorkConst : ℕ}
    (hB42 : 42 ≤ B_tot) (C_d D_d : Fin (2 ^ 42)) : IntertwinesCat
    (uCatNormSingleCat mPayload B_tot kWorkConst).1 (pCat0SingleCat mPayload B_tot kWorkConst)
    (uSignalRotTwoAngleSingleCat hB42 C_d D_d).1 ((QRegister.singleton (qSigInSingleCat
    mPayload B_tot kWorkConst)).embedMatrix (twoAngleDiagHMatrix C_d D_d)) := by
  let rMid := rMid43InSingleCat mPayload B_tot kWorkConst hB42
  let q0 : Wire (1 + 42) := ⟨0, by decide⟩
  let rK0 : QRegister 42 (1 + 42) := QRegister.block 1 42 (by decide)
  let rLowA := (rCatTotInSingleCat mPayload B_tot kWorkConst).compose (rLowCatSlice 42 B_tot hB42)
  let rTopA := (rCatTotInSingleCat mPayload B_tot kWorkConst).compose (rTopCatSlice 42 B_tot hB42)
  have hLoc0 := intertwinesCat_uSignalRotTwoAngle43 C_d D_d
    (U_cat_B_normalized 42) (U_cat_B_normalized_col_zero 42)
  have hLoc : IntertwinesCat (rK0.embedUnitary (U_cat_B_normalized 42)).1
      (rK0.basisOutcomeProjector 0) (uSignalRotTwoAngle43 C_d D_d).1 ((QRegister.singleton
      q0).embedUnitary (twoAngleSigUnitary42 C_d D_d)).1 := ⟨hLoc0.1, hLoc0.2.1, hLoc0.2.2⟩
  have hPush := embedMatrix_intertwinesCat rMid hLoc
  have hCompSig : rMid.compose (QRegister.singleton q0) =
      QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst) := by
    apply qreg_ext_sched; intro i; fin_cases i
    exact rMid43InSingleCat_zero hB42
  have hCompTop : rMid.compose rK0 = rTopA := by
    apply qreg_ext_sched; intro i
    have h1 : rK0 i = Fin.natAdd 1 i := by ext; simp [rK0]; omega
    change rMid (rK0 i) = rTopA i
    dsimp only [rMid]; rw [h1, rMid43InSingleCat, QRegister.concat_apply_right]
  have hE1 : rMid.embedMatrix ((rK0.embedUnitary (U_cat_B_normalized 42)).1) =
      (rTopA.embedUnitary (U_cat_B_normalized 42)).1 := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, hCompTop,
      QRegister.embedUnitary_val]
  have hE2 : rMid.embedMatrix (rK0.basisOutcomeProjector 0) =
      rTopA.basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hCompTop,
      ← QRegister.basisOutcomeProjector]
  let E_A := (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).embedMatrix
    (twoAngleDiagHMatrix C_d D_d)
  have hE3 : rMid.embedMatrix
      (((QRegister.singleton q0).embedUnitary (twoAngleSigUnitary42 C_d D_d)).1) = E_A := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, hCompSig]
  have hM_eq : rMid.embedMatrix (uSignalRotTwoAngle43 C_d D_d).1 =
      (uSignalRotTwoAngleSingleCat hB42 C_d D_d).1 := by
    rw [uSignalRotTwoAngleSingleCat, QRegister.embedUnitary_val]
  rw [hE1, hE2, hE3, hM_eq] at hPush
  have hLowTopA : rLowA.DisjointWires rTopA :=
    disjointWires_compose_of_disjoint (rCatTotInSingleCat mPayload B_tot kWorkConst)
      (rLowCatSlice_disjoint_rTopCatSlice 42 B_tot hB42)
  let U_low_A := (rLowA.embedUnitary (uLowCatTailNorm 42 (B_tot - 42))).1
  let U_top_A := (rTopA.embedUnitary (U_cat_B_normalized 42)).1
  have hUNormFact : (uCatNormSingleCat mPayload B_tot kWorkConst).1 = U_low_A * U_top_A := by
    unfold uCatNormSingleCat
    rw[U_cat_B_normalized_eq_topSlice_mul_lowTail 42 B_tot hB42, QRegister.embedUnitary_mul,
        Submonoid.coe_mul, ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
    exact (rLowA.embedMatrix_comm_of_disjoint rTopA hLowTopA _ _).symm
  have hMidDisjLow : rMid.DisjointWires rLowA := by
    have hSigLow :
        (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).DisjointWires rLowA :=
      ((qSigInSingleCat_disj_catScratch mPayload B_tot kWorkConst).compose_right _).compose_right _
    exact FullSysCatSegmentBridge.disjointWires_concat_left _ hSigLow hLowTopA.symm
  have hM_Low : (uSignalRotTwoAngleSingleCat hB42 C_d D_d).1 * U_low_A =
      U_low_A * (uSignalRotTwoAngleSingleCat hB42 C_d D_d).1 := by
    rw [← hM_eq]
    dsimp only [U_low_A]
    rw [QRegister.embedUnitary_val]
    exact rMid.embedMatrix_comm_of_disjoint rLowA hMidDisjLow _ _
  have hAbsK : rTopA.basisOutcomeProjector 0 *
      pCat0SingleCat mPayload B_tot kWorkConst = pCat0SingleCat mPayload B_tot kWorkConst :=
    TFreeLaurentGQSP.basisOutcomeProjector_zero_compose_mul
      (rCatScratchInSingleCat mPayload B_tot kWorkConst)
      ((inCatTotSingleCat B_tot kWorkConst).compose (rTopCatSlice 42 B_tot hB42))
  have hSigDisjTot : (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).DisjointWires
      (rCatTotInSingleCat mPayload B_tot kWorkConst) :=
    (qSigInSingleCat_disj_catScratch mPayload B_tot kWorkConst).compose_right _
  refine ⟨?_, ?_, (QRegister.singleton (qSigInSingleCat mPayload B_tot
    kWorkConst)).embedMatrix_comm_of_disjoint (rCatScratchInSingleCat mPayload B_tot
    kWorkConst) (qSigInSingleCat_disj_catScratch mPayload B_tot kWorkConst) _ (compProj 0)⟩
  · calc (uSignalRotTwoAngleSingleCat hB42 C_d D_d).1 *
          (uCatNormSingleCat mPayload B_tot kWorkConst).1 *
          pCat0SingleCat mPayload B_tot kWorkConst
      _ = U_low_A *
            (((uSignalRotTwoAngleSingleCat hB42 C_d D_d).1 * U_top_A *
                rTopA.basisOutcomeProjector 0) *
              pCat0SingleCat mPayload B_tot kWorkConst) := by
          rw [hUNormFact, ← Matrix.mul_assoc (uSignalRotTwoAngleSingleCat hB42 C_d D_d).1, hM_Low]
          nth_rw 1 [← hAbsK]
          simp only [Matrix.mul_assoc]
      _ = U_low_A *
            ((U_top_A * E_A * rTopA.basisOutcomeProjector 0) *
              pCat0SingleCat mPayload B_tot kWorkConst) := by
          rw [hPush.1]
      _ = (uCatNormSingleCat mPayload B_tot kWorkConst).1 * E_A *
            pCat0SingleCat mPayload B_tot kWorkConst := by
          rw [Matrix.mul_assoc (U_top_A * E_A), hAbsK, hUNormFact]
          simp only [Matrix.mul_assoc]
  · unfold uCatNormSingleCat
    rw [QRegister.embedUnitary_val]
    exact (QRegister.singleton
      (qSigInSingleCat mPayload B_tot kWorkConst)).embedMatrix_comm_of_disjoint
      (rCatTotInSingleCat mPayload B_tot kWorkConst) hSigDisjTot _ _

theorem biWalkStepOp_eq_ctrlNegRefl_mul {N : ℕ} (qSig : Wire N)
    (R0_emb U_raw_emb W_emb W_inv_emb : Operator (2 ^ N))
    (hW_eq : W_emb = Complex.I • (R0_emb * U_raw_emb))
    (hWinv_eq : W_inv_emb = (-Complex.I) • (U_raw_emb * R0_emb)) (hU0 : U_raw_emb *
    (QRegister.singleton qSig).basisOutcomeProjector 0 = (QRegister.singleton
    qSig).basisOutcomeProjector 0 * U_raw_emb) (hU1 : U_raw_emb * (QRegister.singleton
    qSig).basisOutcomeProjector 1 = (QRegister.singleton qSig).basisOutcomeProjector 1 *
    U_raw_emb) (hR0 : R0_emb * (QRegister.singleton qSig).basisOutcomeProjector 0 =
    (QRegister.singleton qSig).basisOutcomeProjector 0 * R0_emb) (hR1 : R0_emb *
    (QRegister.singleton qSig).basisOutcomeProjector 1 = (QRegister.singleton
    qSig).basisOutcomeProjector 1 * R0_emb) (hRX : R0_emb * (Circuit.X qSig).eval.1 =
    (Circuit.X qSig).eval.1 * R0_emb) : (Circuit.X qSig).eval.1 * (ctrlNegRefl true qSig
    R0_emb * (((Circuit.X qSig).eval.1 * (((-Complex.I) • (1 : Operator (2 ^ N))) *
    (QRegister.singleton qSig).basisOutcomeProjector 0 + (Complex.I • (1 : Operator (2 ^ N)))
    * (QRegister.singleton qSig).basisOutcomeProjector 1)) * (U_raw_emb * ctrlNegRefl true
    qSig R0_emb))) = biWalkStepOp qSig W_emb W_inv_emb := by
  set P0 := (QRegister.singleton qSig).basisOutcomeProjector 0
  set P1 := (QRegister.singleton qSig).basisOutcomeProjector 1
  have hFalse : (Circuit.X qSig).eval.1 *
      (ctrlNegRefl true qSig R0_emb * (Circuit.X qSig).eval.1) =
      ctrlNegRefl false qSig R0_emb := by
    rw [ctrlNegRefl_true_eq,
      conj_X_sig_swap qSig 1 (-R0_emb) (by simp) (by rw [neg_mul, hRX, mul_neg]),
      ctrlNegRefl_false_eq]
  have hMid : (((-Complex.I) • (1 : Operator (2 ^ N))) * P0 +
        (Complex.I • (1 : Operator (2 ^ N))) * P1) * U_raw_emb =
      ((-Complex.I) • U_raw_emb) * P0 + (Complex.I • U_raw_emb) * P1 := by
    rw [Matrix.add_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [Matrix.mul_assoc, ← hU0, smul_mul_assoc, one_mul, ← smul_mul_assoc]
    · rw [Matrix.mul_assoc, ← hU1, smul_mul_assoc, one_mul, ← smul_mul_assoc]
  calc (Circuit.X qSig).eval.1 *
        (ctrlNegRefl true qSig R0_emb *
          (((Circuit.X qSig).eval.1 *
              (((-Complex.I) • (1 : Operator (2 ^ N))) * P0 +
                (Complex.I • (1 : Operator (2 ^ N))) * P1)) *
            (U_raw_emb * ctrlNegRefl true qSig R0_emb)))
    _ = ((Circuit.X qSig).eval.1 *
          (ctrlNegRefl true qSig R0_emb * (Circuit.X qSig).eval.1)) *
        (((((-Complex.I) • (1 : Operator (2 ^ N))) * P0 +
            (Complex.I • (1 : Operator (2 ^ N))) * P1) * U_raw_emb) *
          ctrlNegRefl true qSig R0_emb) := by simp only [Matrix.mul_assoc]
    _ = ctrlNegRefl false qSig R0_emb *
          ((((-Complex.I) • U_raw_emb) * P0 + (Complex.I • U_raw_emb) * P1) *
            ctrlNegRefl true qSig R0_emb) := by rw [hFalse, hMid]
    _ = biWalkStepOp qSig W_emb W_inv_emb := by
          rw [← Matrix.mul_assoc,
            biInteriorWalk_refl_algebra qSig R0_emb U_raw_emb hU0 hU1 hR0 hR1,
            biWalkStepOp, hW_eq, hWinv_eq]

/-- General `N`-qubit right-boundary Bi-GQSP reflection algebra. -/
theorem biRightBoundary_ctrlNegRefl_mul_eq {N : ℕ} (qSig : Wire N)
    (R0_emb U_raw_emb W_emb : Operator (2 ^ N))
    (hW_eq : W_emb = Complex.I • (R0_emb * U_raw_emb)) (hU0 : U_raw_emb * (QRegister.singleton
    qSig).basisOutcomeProjector 0 = (QRegister.singleton qSig).basisOutcomeProjector 0 *
    U_raw_emb) (hU1 : U_raw_emb * (QRegister.singleton qSig).basisOutcomeProjector 1 =
    (QRegister.singleton qSig).basisOutcomeProjector 1 * U_raw_emb) : ctrlNegRefl true qSig
    R0_emb * (((1 : Operator (2 ^ N)) * (QRegister.singleton qSig).basisOutcomeProjector 0 +
    ((-Complex.I) • (1 : Operator (2 ^ N))) * (QRegister.singleton qSig).basisOutcomeProjector
    1) * ((QRegister.singleton qSig).basisOutcomeProjector 0 + U_raw_emb *
    (QRegister.singleton qSig).basisOutcomeProjector 1)) =
    (QRegister.singleton qSig).basisOutcomeProjector 0 + W_emb *
    (QRegister.singleton qSig).basisOutcomeProjector 1 := by
  set P0 := (QRegister.singleton qSig).basisOutcomeProjector 0
  set P1 := (QRegister.singleton qSig).basisOutcomeProjector 1
  have hMid : ((1 : Operator (2 ^ N)) * P0 + ((-Complex.I) • (1 : Operator (2 ^ N))) * P1) *
      (P0 + U_raw_emb * P1) =
      (1 : Operator (2 ^ N)) * P0 + ((-Complex.I) • U_raw_emb) * P1 := by
    rw [show P0 + U_raw_emb * P1 = (1 : Operator (2 ^ N)) * P0 + U_raw_emb * P1 by rw [one_mul],
      sig_block_diag_mul qSig 1 ((-Complex.I) • 1) 1 U_raw_emb
        (by simp) (by simp) hU0 hU1,
      one_mul, one_mul, smul_mul_assoc, one_mul]
  rw [hMid, biRightBoundary_refl_algebra qSig R0_emb U_raw_emb hU0 hU1, hW_eq]

/-- General `N`-qubit left-boundary Bi-GQSP reflection algebra. -/
theorem biLeftBoundary_ctrlNegRefl_mul_eq {N : ℕ} (qSig : Wire N)
    (R0_emb U_raw_emb W_inv_emb : Operator (2 ^ N))
    (hWinv_eq : W_inv_emb = (-Complex.I) • (U_raw_emb * R0_emb)) (hU0 : U_raw_emb *
    (QRegister.singleton qSig).basisOutcomeProjector 0 = (QRegister.singleton
    qSig).basisOutcomeProjector 0 * U_raw_emb) (hU1 : U_raw_emb * (QRegister.singleton
    qSig).basisOutcomeProjector 1 = (QRegister.singleton qSig).basisOutcomeProjector 1 *
    U_raw_emb) (hR0 : R0_emb * (QRegister.singleton qSig).basisOutcomeProjector 0 =
    (QRegister.singleton qSig).basisOutcomeProjector 0 * R0_emb) (hR1 : R0_emb *
    (QRegister.singleton qSig).basisOutcomeProjector 1 = (QRegister.singleton
    qSig).basisOutcomeProjector 1 * R0_emb) (hUX : U_raw_emb * (Circuit.X qSig).eval.1 =
    (Circuit.X qSig).eval.1 * U_raw_emb) (hRX : R0_emb * (Circuit.X qSig).eval.1 = (Circuit.X
    qSig).eval.1 * R0_emb) : ((Circuit.X qSig).eval.1 * (Circuit.S qSig).eval.1) *
    (((QRegister.singleton qSig).basisOutcomeProjector 0 + U_raw_emb * (QRegister.singleton
    qSig).basisOutcomeProjector 1) * (ctrlNegRefl true qSig R0_emb * (Circuit.X qSig).eval.1))
    = W_inv_emb * (QRegister.singleton qSig).basisOutcomeProjector 0 +
    (QRegister.singleton qSig).basisOutcomeProjector 1 := by
  set P0 := (QRegister.singleton qSig).basisOutcomeProjector 0
  set P1 := (QRegister.singleton qSig).basisOutcomeProjector 1
  have iS_proj : (Circuit.S qSig).eval.1 =
      (1 : Operator (2 ^ N)) * P0 + (Complex.I • (1 : Operator (2 ^ N))) * P1 := by
    apply matrix_ext_ket; intro β
    have hS : (Circuit.S qSig).eval.1 = (QRegister.singleton qSig).embedMatrix Qubit.S.1 := by
      rw [Circuit.S, Circuit.eval_single, QRegister.embedUnitary_val]; rfl
    rw [hS, singleton_embedMatrix_mulVec_ket, Matrix.add_mulVec, one_mul,
      smul_mul_assoc, one_mul, Matrix.smul_mulVec,
      singleton_proj_zero_mulVec_ket, singleton_proj_one_mulVec_ket]
    rcases bit_cases (β qSig) with hq | hq
    · have hup : Function.update β qSig 0 = β := Function.update_eq_self_iff.mpr hq.symm
      simp [hq, hup, Qubit.S]
    · have hup : Function.update β qSig 1 = β := Function.update_eq_self_iff.mpr hq.symm
      simp [hq, hup, Qubit.S]
  have hInner : (Circuit.S qSig).eval.1 *
      ((P0 + U_raw_emb * P1) * ctrlNegRefl true qSig R0_emb) =
      (1 : Operator (2 ^ N)) * P0 + W_inv_emb * P1 := by
    have hRneg0 : (-R0_emb) * P0 = P0 * (-R0_emb) := by rw [neg_mul, hR0, mul_neg]
    have hRneg1 : (-R0_emb) * P1 = P1 * (-R0_emb) := by rw [neg_mul, hR1, mul_neg]
    have hProd1 : (P0 + U_raw_emb * P1) * ctrlNegRefl true qSig R0_emb =
        (1 : Operator (2 ^ N)) * P0 + (-(U_raw_emb * R0_emb)) * P1 := by
      rw [show P0 + U_raw_emb * P1 = (1 : Operator (2 ^ N)) * P0 + U_raw_emb * P1 by rw [one_mul],
        ctrlNegRefl_true_eq,
        sig_block_diag_mul qSig 1 U_raw_emb 1 (-R0_emb) (by simp) (by simp) hRneg0 hRneg1,
        one_mul, mul_neg]
    have hUR0 : (-(U_raw_emb * R0_emb)) * P0 = P0 * (-(U_raw_emb * R0_emb)) := by
      rw [neg_mul, mul_neg, Matrix.mul_assoc, hR0, ← Matrix.mul_assoc, hU0, Matrix.mul_assoc]
    have hUR1 : (-(U_raw_emb * R0_emb)) * P1 = P1 * (-(U_raw_emb * R0_emb)) := by
      rw [neg_mul, mul_neg, Matrix.mul_assoc, hR1, ← Matrix.mul_assoc, hU1, Matrix.mul_assoc]
    rw [hProd1, iS_proj,
      sig_block_diag_mul qSig 1 (Complex.I • 1) 1 (-(U_raw_emb * R0_emb))
        (by simp) (by simp) hUR0 hUR1,
      one_mul, one_mul, mul_neg, smul_mul_assoc, one_mul, ← neg_smul, ← hWinv_eq]
  calc ((Circuit.X qSig).eval.1 * (Circuit.S qSig).eval.1) *
        ((P0 + U_raw_emb * P1) * (ctrlNegRefl true qSig R0_emb * (Circuit.X qSig).eval.1))
    _ = (Circuit.X qSig).eval.1 *
          (((Circuit.S qSig).eval.1 *
            ((P0 + U_raw_emb * P1) * ctrlNegRefl true qSig R0_emb)) *
            (Circuit.X qSig).eval.1) := by simp only [Matrix.mul_assoc]
    _ = (Circuit.X qSig).eval.1 *
          (((1 : Operator (2 ^ N)) * P0 + W_inv_emb * P1) * (Circuit.X qSig).eval.1) := by
          rw [hInner]
    _ = W_inv_emb * P0 + P1 := by
          have hWX : W_inv_emb * (Circuit.X qSig).eval.1 =
              (Circuit.X qSig).eval.1 * W_inv_emb := by
            rw [hWinv_eq, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, hRX,
              ← Matrix.mul_assoc, hUX, Matrix.mul_assoc]
          rw [conj_X_sig_swap qSig 1 W_inv_emb (by simp) hWX, one_mul]
/-- Catalyst intertwining for `(diagNegIPosICircuit qSig).seq (Circuit.X qSig)`. -/
theorem intertwinesCat_diagNegIPosIX_singleCat (mPayload B_tot kWorkConst : ℕ) :
    let qSig := qSigInSingleCat mPayload B_tot kWorkConst
    IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      ((diagNegIPosICircuit qSig).seq (Circuit.X qSig)).eval.1
      ((Circuit.X qSig).eval.1 *
        (((-Complex.I) • (1 : Operator (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)))) *
            (QRegister.singleton qSig).basisOutcomeProjector 0 +
          (Complex.I • (1 : Operator (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)))) *
            (QRegister.singleton qSig).basisOutcomeProjector 1)) := by
  set qSig := qSigInSingleCat mPayload B_tot kWorkConst
  set P0 := (QRegister.singleton qSig).basisOutcomeProjector 0
  set P1 := (QRegister.singleton qSig).basisOutcomeProjector 1
  have iX := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.X
  have iS := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.S
  have iZ := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.Z
  have iDiag : IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst) (diagNegIPosICircuit qSig).eval.1
      (((-Complex.I) • (1 : Operator _)) * P0 + (Complex.I • (1 : Operator _)) * P1) := by
    have h1 := intertwinesCat_mul_gen iS
      (intertwinesCat_mul_gen (intertwinesCat_mul_gen iX (intertwinesCat_mul_gen iZ iS)) iX)
    have hD1 : (diagNegIPosICircuit qSig).eval.1 = (Circuit.S qSig).eval.1 * (((Circuit.X
        qSig).eval.1 * ((Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1)) * (Circuit.X
        qSig).eval.1) := by
      unfold diagNegIPosICircuit
      simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
    have hD2 : (Circuit.S qSig).eval.1 * (((Circuit.X qSig).eval.1 * ((Circuit.Z qSig).eval.1
        * (Circuit.S qSig).eval.1)) * (Circuit.X qSig).eval.1) =
        ((-Complex.I) • (1 : Operator _)) * P0 + (Complex.I • (1 : Operator _)) * P1 := by
      rw [← hD1, diagNegIPosICircuit_eval_eq_proj]
    exact ⟨by rw [hD1, ← hD2]; exact h1.1,
           by rw [← hD2]; exact h1.2.1,
           by rw [← hD2]; exact h1.2.2⟩
  simpa only [Circuit.eval_seq, Submonoid.coe_mul] using intertwinesCat_mul_gen iX iDiag

def gidneyTwoAngleRotToffEquiv (c d : ℕ) : ℕ := (activeMsbWidth42 c - 2) +
    (activeMsbWidth42 d - 2) + max (activeMsbWidth42 c - 2) (activeMsbWidth42 d - 2)

/-- `43`-wire 2-angle Gidney signal rotation `dKick(C_d) ;; H ;; dKick(D_d) ;; H`
on `(qSig, rCat42)`. -/
def biPrefixTwoAngleRotToffSum (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (t + 1), gidneyTwoAngleRotToffEquiv (biCode M C j).val (biCode M D j).val

theorem biPrefixTwoAngleRotToffSum_eq_univ_sum (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) :
    biPrefixTwoAngleRotToffSum M C D M = ∑ t : Fin (M + 1), gidneyTwoAngleRotToffEquiv
    (C t).val (D t).val := by
  unfold biPrefixTwoAngleRotToffSum
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hjC : biCode M C j.val = C j := by simp [biCode, j.isLt]
  have hjD : biCode M D j.val = D j := by simp [biCode, j.isLt]
  rw [hjC, hjD]

set_option maxRecDepth 2000

end ConfigHarmonicTwoAngleBridge
end HarmonicTwoAngleBridge
end
set_option exponentiation.threshold 256
end HarmonicTwoAngleBridge

section Koff3PassSelectBridge
local instance (priority := 1000000) instNeZeroTwoPow_Koff3PassSelectBridge (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
# Mode-1 `k_off` 3-Pass Barrel SELECT Closure Bridge (`mWork >= 220`)

Assembles the turnkey `220`-wire `GidneyGuardWrapDynBundle` (`31,384 T`), the `31,200 T`
`Stream1300` init/uninit pair bound, the stripped `36`-bit Mode-1 `k_off` `Barrel3PassTwistSpec`
(`pref.tProjPrefix + 21,376 T`), and exact `0.0 Ha` cancellation of `uKoffDiagCore` across both
the position (`P0`, `s₂ = 0`) and momentum (`P1`, `s₂ = 1`) branches of `SingleCatSelectImpl` /
`HoistedBorrow42SelectSpec`.
-/

namespace Koff3PassSelectBridge

section ConfigKoff3PassSelectBridge

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

local instance (priority := 1000000)
    instLoc_Koff3PassSelectBridge_1InstNeZeroTwoPowW6Kof (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open FullSysCatSegmentBridge
open PosMomSelectDynamic
open DyadicQft64WalkCircuit220
  (qft64Ideal654Unitary_eq_coreIdeal_mul_preDiag)
open NuclearTwistRealizes
open FusedPreDiagFromTwist288
  (hm6_of_hm22 uPre654 uTildeFullCore uTildeFullCore_eq_dyadicDiag48
   embed_uPre654_eq_xor32_clifford_uTildeCore)
open ProjZ512QftAndTwist288
open InterWalkRSum42Hoist
open Barrel3PassSelectStitch
open Barrel3PassCommuteHelpers
open SchedBranchStitchGen
open TierBClean80Closure (tierBQftFull)
open MergedVepLeaf4GridPerturbation (tierBQftFull_preservesCoset3)
open KoffPrunedSlot2ZeroMuxTrunc37

/- ## Section 2: Stripped `36`-Bit Mode-1 `k_off` Hoisted Twist (`pref.tProjPrefix + 21,376 T`) -/

noncomputable abbrev uTwistEffBaseCut80 (c' : Configuration) : Unitary
    (2 ^ (fullSysCoreWires 80)) :=
    (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
    uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80))

theorem uTildeFullCore80_comm_uKoffDiagCore (c' : Configuration) :
    FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
      uKoffDiagCore c' (by decide : 22 ≤ 80) =
    uKoffDiagCore c' (by decide : 22 ≤ 80) *
      FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) := by
  rw [FusedPreDiagFromTwist288.uTildeFullCore_eq_dyadicDiag48
    (by decide : 6 ≤ 80), uKoffDiagCore]
  simp only [dyadicDiagUnitary_mul]
  apply dyadicDiagUnitary_congr
  intro _
  exact add_comm _ _

/- ## Section 3: Exact `0.0 Ha` Cancellation of `uKoffDiagCore` on `P0` and `P1` -/

theorem swapElec0Bits_eq_of_ge3924 {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (q : Fin (fullSysCoreWires mPayload))
    (hq : 3924 ≤ q.val) : CoinDispatchedBarrel288.swapElec0Bits e γ
    q = γ q := by
  have he := e.isLt
  dsimp [SpecsAux.SpecMirror.numElectrons] at he
  rw [Barrel3PassCommuteHelpers.swapElec0Bits_eq_comp_wire]
  exact congrArg γ (Fin.ext (by
    dsimp [Barrel3PassCommuteHelpers.swapElec0Wire]
    split_ifs <;> simp only <;> omega))

theorem uKoffDiagCore_comm_uBarrelFast (c' : Configuration) : uKoffDiagCore c'
    (by decide : 22 ≤ 80) * CoinDispatchedBarrel288.uBarrelFast
    (le_refl 80) = CoinDispatchedBarrel288.uBarrelFast (le_refl 80)
    * uKoffDiagCore c' (by decide : 22 ≤ 80) := by
  apply Subtype.ext
  exact dyadicDiag_comm_uBarrelFast (le_refl 80) (kOffTotalPhaseExp c' (by decide : 22 ≤ 80))
    (fun e γ ↦ kOffTotalPhaseExp_eq_of_ge3924 c' (by decide : 22 ≤ 80)
    (swapElec0Bits_eq_of_ge3924 e γ))

theorem uKoffDiagCore_comm_uSlot4KickCore (c' : Configuration) :
    uKoffDiagCore c' (by decide : 22 ≤ 80) * uSlot4KickCore (by decide : 22 ≤ 80) =
      uSlot4KickCore (by decide : 22 ≤ 80) * uKoffDiagCore c' (by decide : 22 ≤ 80) := by
  rw [uKoffDiagCore, uSlot4KickCore]
  simp only [dyadicDiagUnitary_mul]
  apply dyadicDiagUnitary_congr
  intro _
  exact add_comm _ _

theorem group_comm_inv_of_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    a * b⁻¹ = b⁻¹ * a := by
  calc a * b⁻¹
      = (b⁻¹ * b) * (a * b⁻¹) := by rw [inv_mul_cancel, one_mul]
    _ = b⁻¹ * (b * a) * b⁻¹ := by simp only [mul_assoc]
    _ = b⁻¹ * (a * b) * b⁻¹ := by rw [← h]
    _ = b⁻¹ * a * (b * b⁻¹) := by simp only [mul_assoc]
    _ = b⁻¹ * a := by rw [mul_inv_cancel, mul_one]

theorem unitaryConj_comm_of_comm {d : ℕ} {K B M : Unitary d} (hKB : K * B = B * K)
    (hKM : K * M = M * K) : K * HoistedSwapSelectBridge.unitaryConj
    B M = HoistedSwapSelectBridge.unitaryConj B M * K := by
  rw [unitaryConj_eq_inv_mul]
  have hKBi : K * B⁻¹ = B⁻¹ * K := group_comm_inv_of_comm hKB
  calc K * (B⁻¹ * M * B)
      = (K * B⁻¹) * M * B := by simp only [mul_assoc]
    _ = B⁻¹ * (K * M) * B := by rw [hKBi]; simp only [mul_assoc]
    _ = B⁻¹ * M * (K * B) := by rw [hKM]; simp only [mul_assoc]
    _ = (B⁻¹ * M * B) * K := by rw [hKB]; simp only [mul_assoc]

theorem uKoffDiagCore_comm_qft_mul_uTrailCliffordXor80
    (c' : Configuration) (qft : FullSysQft654Bundle) (hmPay : 6 ≤ 80)
    (hQft :
      qft.uQft654 = DyadicQft64WalkCircuit220.coreQftHadamardIdeal654) :
    uKoffDiagCore c' (by decide : 22 ≤ 80) *
      (fullSysQftCoreUnitary hmPay qft * uTrailCliffordXor80) =
    (fullSysQftCoreUnitary hmPay qft * uTrailCliffordXor80) *
      uKoffDiagCore c' (by decide : 22 ≤ 80) := by
  let hm22 : 22 ≤ 80 := by decide
  let hm6 : 6 ≤ 80 := hm6_of_hm22 hm22
  have hmEq : hmPay = hm6 := Subsingleton.elim _ _
  have hPre :
      uTrailCliffordXor80 * FusedPreDiagFromTwist288.uTildeFullCore hm6 =
        (coreElecCosetB1Block hm6).embedUnitary
          FusedPreDiagFromTwist288.uPre654 := by
    unfold uTrailCliffordXor80
    have hm6Eq : Barrel3PassSelectStitch.hm6_80 = hm6 :=
      Subsingleton.elim _ _
    rw [hm6Eq, mul_assoc]
    exact
      (FusedPreDiagFromTwist288.embed_uPre654_eq_xor32_clifford_uTildeCore
        hm6).symm
  have hQFull : fullSysQftCoreUnitary hmPay qft * uTrailCliffordXor80 =
      fullSysQftCoreUnitary hm6 tierBQftFull *
      (FusedPreDiagFromTwist288.uTildeFullCore hm6)⁻¹ := by
    apply eq_mul_inv_of_mul_eq
    rw [hmEq, mul_assoc, hPre]
    unfold fullSysQftCoreUnitary
    rw [← QRegister.embedUnitary_mul, hQft]
    refine congrArg (coreElecCosetB1Block hm6).embedUnitary ?_
    unfold tierBQftFull FusedPreDiagFromTwist288.uPre654
    rw [DyadicQft64WalkCircuit288.fullSysQft654Bundle288_uQft654]
    exact qft64Ideal654Unitary_eq_coreIdeal_mul_preDiag.symm
  have hKF : uKoffDiagCore c' hm22 * fullSysQftCoreUnitary hm6 tierBQftFull =
      fullSysQftCoreUnitary hm6 tierBQftFull * uKoffDiagCore c' hm22 :=
    (fullSysQftCoreUnitary_comm_uKoffDiagCore hm22 c' tierBQftFull
      tierBQftFull_preservesCoset3).symm
  have hKT : uKoffDiagCore c' hm22 *
      (FusedPreDiagFromTwist288.uTildeFullCore hm6)⁻¹ =
      (FusedPreDiagFromTwist288.uTildeFullCore hm6)⁻¹ *
        uKoffDiagCore c' hm22 :=
    group_comm_inv_of_comm (uTildeFullCore80_comm_uKoffDiagCore c').symm
  rw [hQFull, ← mul_assoc, hKF, mul_assoc, hKT, ← mul_assoc]

/-- Momentum-branch (`s₂ = 1`) residual `654*6 + 3`-wire `k_off` phase exponent
depending only on `b₁`. -/
def koffMomCosetExp654 (γ : BitAssignment (3924 + 3)) : ℤ :=
  - ∑ w : Fin 3, kOffFromEff (((1 - (γ (Fin.natAdd 3924 w)).val) * 2 ^ 41) % 2 ^ 48)

/-- Momentum-branch (`s₂ = 1`) residual `k_off` diagonal unitary on `coreElecCosetB1Block`. -/
noncomputable def uKoffMomCoset654 : Unitary (2 ^ (3924 + 3)) :=
  DyadicQft64.dyadicDiagUnitary (3924 + 3) 48 koffMomCosetExp654

/-- Momentum-branch (`s₂ = 1`) residual `k_off` diagonal unitary embedded on
`fullSysCoreWires 80`. -/
noncomputable def uKoffMomCore80 : Unitary (2 ^ (fullSysCoreWires 80)) :=
  (coreElecCosetB1Block (by decide : 6 ≤ 80)).embedUnitary uKoffMomCoset654

theorem uKoffMomCore80_eq_dyadicDiag : uKoffMomCore80 = DyadicQft64.dyadicDiagUnitary
    (fullSysCoreWires 80) 48 (fun γ ↦ - ∑ w : Fin 3, kOffFromEff (((1 - (γ (coreCosetB1Block
    (by decide : 6 ≤ 80) w)).val) * 2 ^ 41) % 2 ^ 48)) := by
  apply Subtype.ext
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro γ
  have hket : MeasureBranchHadamardSem.ket γ = basisKet γ := rfl
  rw [hket, uKoffMomCore80, uKoffMomCoset654,
    DyadicQft64.embedUnitary_dyadicDiagUnitary_mulVec_basisKet,
    dyadicDiagUnitary_mulVec_basisKet]
  refine congrArg (fun z ↦ DyadicQft64.dyadicTurn 48 z • basisKet γ) ?_
  unfold koffMomCosetExp654
  refine congrArg (- ·) (Finset.sum_congr rfl fun w _ ↦ ?_)
  have hw : coreElecCosetB1Block (by decide : 6 ≤ 80) (Fin.natAdd 3924 w) = coreCosetB1Block
      (by decide : 6 ≤ 80) w := QRegister.concat_apply_right _ _ _ w
  dsimp only
  rw [hw]

theorem uKoffMomCore80_comm_slotBitProj (q : Wire (fullSysCoreWires 80)) (b : Fin 2) :
    uKoffMomCore80.1 * PosMomSelectSandwich.slotBitProj q b =
    PosMomSelectSandwich.slotBitProj q b * uKoffMomCore80.1 :=
    diag_unitary_comm_slotBitProj ((congrArg Subtype.val uKoffMomCore80_eq_dyadicDiag).trans
    (dyadicDiagUnitary_eq_diagonal _)) q b

theorem uKoffDiagCore_mul_P1 (c' : Configuration) : (uKoffDiagCore c' (by decide : 22 ≤ 80)).1
    * PosMomSelectSandwich.slotBitProj (iSlot2 80) 1 =
    uKoffMomCore80.1 * PosMomSelectSandwich.slotBitProj (iSlot2 80)
    1 := by
  let hm22 : 22 ≤ 80 := by decide
  rw [uKoffDiagCore, uKoffMomCore80_eq_dyadicDiag,
    dyadicDiagUnitary_eq_diagonal, dyadicDiagUnitary_eq_diagonal,
    PosMomSelectSandwich.slotBitProj,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  dsimp only [Fin.val_one]
  by_cases hc : (basisBits (fullSysCoreWires 80) u (iSlot2 80)).val = 1
  · simp only [hc, ↓reduceIte, mul_one]
    have hne : basisBits (fullSysCoreWires 80) u
        (NuclearTwistAndXor654Concrete.wSlot2
          (QRegExt.idReg _)) ≠ 0 := by
      intro h0
      have hwEq : NuclearTwistAndXor654Concrete.wSlot2
          (QRegExt.idReg (fullSysCoreWires 80)) = iSlot2 80 := Fin.ext rfl
      rw [hwEq] at h0; rw [h0] at hc; cases hc
    obtain ⟨hc0, hv0⟩ :=
      Slot3StreamUncK35Shift3.coin0Active_false_of_wSlot2_ne_zero hne
    have hm48 : ∀ w, slot2M48Val c' hm22 w (basisBits _ u) = 0 := fun w ↦ by
      unfold slot2M48Val
      simp only [hc0, Bool.false_eq_true, false_and, ↓reduceDIte]
    have hvep : ∀ w, vepOnlyM48Val hm22 w (basisBits _ u) = 0 := fun w ↦ by
      unfold vepOnlyM48Val
      rw [hv0]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine congrArg (DyadicQft64.dyadicTurn 48) ?_
    unfold kOffTotalPhaseExp vepEffSlope48
    simp only [hm48, hvep, zero_add]
  · simp only [hc, ↓reduceIte, mul_zero]

theorem uKoffMomCore80_comm_uBarrelFast : uKoffMomCore80 *
    CoinDispatchedBarrel288.uBarrelFast (le_refl 80) =
    CoinDispatchedBarrel288.uBarrelFast (le_refl 80) *
    uKoffMomCore80 := by
  apply Subtype.ext
  exact embed_dyadicDiag654_comm_uBarrelFast (le_refl 80) koffMomCosetExp654
    (fun e γ ↦ by
      unfold koffMomCosetExp654
      refine congrArg (- ·) (Finset.sum_congr rfl fun w _ ↦ ?_)
      have hge : 3924 ≤ (coreElecCosetB1Block
          (Nat.le_trans (by decide : 6 ≤ 80) (le_refl 80)) (Fin.natAdd 3924 w)).val :=
        coreElecCosetB1_ge3924 _ (by dsimp; omega)
      dsimp only
      rw [swapElec0Bits_eq_of_ge3924 e γ _ hge])

theorem uKoffMomCore80_comm_uSlot0LocalXorBit5 (w_eff : ℝ) :
    uKoffMomCore80 * uSlot0LocalXorBit5 (le_refl 80) w_eff =
      uSlot0LocalXorBit5 (le_refl 80) w_eff * uKoffMomCore80 := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, uKoffMomCore80_eq_dyadicDiag,
    dyadicDiagUnitary_eq_diagonal, uSlot0LocalXorBit5_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; exact mul_comm _ _

theorem comm_of_unitaryConj_eq {d : ℕ} {V M : Unitary d}
    (h : HoistedSwapSelectBridge.unitaryConj V M = M) :
    V * M = M * V := by
  rw [unitaryConj_eq_inv_mul, mul_assoc] at h
  exact (inv_mul_eq_iff_eq_mul.mp h).symm

set_option exponentiation.threshold 256
set_option maxRecDepth 2000

end ConfigKoff3PassSelectBridge

end Koff3PassSelectBridge

end
set_option exponentiation.threshold 256
end Koff3PassSelectBridge

section Leaf1Pass1And3Width204
local instance (priority := 1000000) instNeZeroTwoPow_Leaf1Pass1And3Width204 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Compact `Pass 1` & `Pass 3` Width-Parametric Leaves (`Leaf1Pass1And3Width204`)

Width-compact implementations for Unclamped `Pass 1` (`uPass1CatT4` / `uPass1Cat` / `uPass1Eff`)
and Clamped `Pass 3` (`uPass3CatT4` / `uPass3Cat` / `uPass3Eff`) on both the `4`-catalyst-wire
(`rT4 = rPG48.slice 41 4`) seam (`dSlot4StandaloneT4_13`, `dPass3T4`, `dPass1T4`) and the
`48`-catalyst-wire `CTLeafSpec` seam (`dSlot4Standalone13`, `pass3SpecOfLe`, `pass1SpecOfLe`),
eliminating `dSlot4Standalone`'s `256`-wire padding floor and streaming unheld `AnchorMux218`
unary wires while holding a read-only `TempAnd` bank across the inner block.
-/

public section

namespace Leaf1Pass1And3Width204

section ConfigLeaf1Pass1And3Width204

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance (priority := 1000000)
    instLoc_Leaf1Pass1And3Width204_1InstNeZeroTwoPowLeaf (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation

open DyadicQft64 hiding dyadicTurn phaseGradKet
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open SpecsAux.PhaseGradCatalystCore
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open ProjZ512QftAndTwist288 hiding
  basisBits_symm_apply fullSysCoreWires_eq_add
open FusedVepCore288
open JunctionApexCSA288 (fullSysCoreWires_eq_3954_add
   intModFinPow2 intModFinPow2_nat_lt intModFinPow2_add_right ediv_mul_add_intModFinPow2
   bitsVal_basisBits_eq_val symm_bitsVal_eq
   shiftRegInt eq_shiftRegInt_of_outside_and_regVal qreg_ext_local
   basisBits_splitSysCatEquiv_symm_castAdd basisBits_splitSysCatEquiv_symm_natAdd
   uSlot4AxisCat uSlot4ApexCat
   rHigh
   wSlot0_mem_rHigh wSlot1_mem_rHigh wSlot2_mem_rHigh
   slice_apply_eq
   slice_sub_slice_b2 qreg_image_concat
   reg_mem_slice_b2 reg_not_mem_slice_b2
   genBoolBit dGenBoolWrap
   compose_rCoreBlock48_eq embed_uApexShift45_mulVec_basisKet
   slot4Sgn slot4LowShift slot4TopExp
     apexCarryPhase
   CondStageSpec)

/- ## Section 1A: `4`-Catalyst-Wire `Slot 4` Unitaries (`uSlot4ApexCatT4`, `selCT4InCT`) -/

/-- Exact clean-workspace width (`2` coin-peel + `1` `wAct` + `6` `rM6` + `4` `rC4` = `13` wires)
needed by `dSlot4StandaloneT4_13` and `dSlot4Standalone13`. -/
abbrev mWork13 : ℕ := 13

/-- Modular `2 ^ 4` step on `Fin (2 ^ 4)` shifting by `d : ℤ`. -/
def stepT4Fin (d : ℤ) (m : Fin (2 ^ 4)) : Fin (2 ^ 4) := intModFinPow2 4 ((m.val : ℤ) + d)

theorem stepT4Fin_zero (m : Fin (2 ^ 4)) : stepT4Fin 0 m = m := by
  unfold stepT4Fin
  rw [add_zero, intModFinPow2_nat_lt m.isLt]

theorem stepT4Fin_step (d₁ d₂ : ℤ) (m : Fin (2 ^ 4)) :
    stepT4Fin d₂ (stepT4Fin d₁ m) = stepT4Fin (d₁ + d₂) m := by
  unfold stepT4Fin
  rw [intModFinPow2_add_right, add_assoc]

/-- Product-space permutation shifting the `4`-bit catalyst register by `δ(γ) mod 16`. -/
def t4WinMidPerm (kSys : ℕ) (δ : BitAssignment kSys → ℤ) :
    Equiv.Perm (BitAssignment kSys × Fin (2 ^ 4)) where
  toFun p := (p.1, stepT4Fin (δ p.1) p.2)
  invFun p := (p.1, stepT4Fin (-δ p.1) p.2)
  left_inv p := by
    ext
    · rfl
    · dsimp; rw [stepT4Fin_step, add_neg_cancel, stepT4Fin_zero]
  right_inv p := by
    ext
    · rfl
    · dsimp; rw [stepT4Fin_step, neg_add_cancel, stepT4Fin_zero]

/-- Basis-index permutation on `Fin (2 ^ (kSys + 4))` shifting the `4` catalyst wires by `δ`. -/
def t4WinPerm (kSys : ℕ) (δ : BitAssignment kSys → ℤ) : Equiv.Perm (Fin (2 ^ (kSys + 4))) :=
    (splitSysCatEquiv kSys 4).trans
    ((t4WinMidPerm kSys δ).trans (splitSysCatEquiv kSys 4).symm)

theorem t4WinPerm_apply (kSys : ℕ) (δ : BitAssignment kSys → ℤ) (x : Fin (2 ^ (kSys + 4))) :
    t4WinPerm kSys δ x = (splitSysCatEquiv kSys 4).symm ((splitSysCatEquiv kSys 4 x).1,
    stepT4Fin (δ (splitSysCatEquiv kSys 4 x).1) (splitSysCatEquiv kSys 4 x).2) := by
  unfold t4WinPerm t4WinMidPerm
  simp only [Equiv.trans_apply, Equiv.coe_fn_mk]

/-- Carry exponent (`⌊(val(rT4) + δ) / 16⌋`) for `uApexShift4`. -/
def t4CarryExp (kSys : ℕ) (δ : BitAssignment kSys → ℤ) : BitAssignment (kSys + 4) → ℤ := fun β
    ↦ ((bitsVal (fun k : Fin 4 ↦ β (Fin.natAdd kSys k)) : ℤ) + δ (fun i ↦ β (Fin.castAdd 4
    i))) / (2 ^ 4 : ℤ)

/-- Direct `(kSys + 4)`-wire `4`-bit catalyst shift-and-carry-phase unitary. -/
noncomputable def uApexShift4 (kSys : ℕ) (δ : BitAssignment kSys → ℤ) : Unitary
    (2 ^ (kSys + 4)) := Operator.permutationUnitary (t4WinPerm kSys δ) *
    DyadicQft64.dyadicDiagUnitary (kSys + 4) 3 (t4CarryExp kSys δ)

theorem t4WinPerm_symm_apply (kSys : ℕ) (δ : BitAssignment kSys → ℤ) (γ : BitAssignment kSys)
    (m : Fin (2 ^ 4)) : t4WinPerm kSys δ ((splitSysCatEquiv kSys 4).symm (γ, m)) =
    (splitSysCatEquiv kSys 4).symm (γ, stepT4Fin (δ γ) m) := by
  unfold t4WinPerm t4WinMidPerm
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.coe_fn_mk]

theorem uApexShift4_mulVec_single {kSys : ℕ} (δ : BitAssignment kSys → ℤ)
    (x : Fin (2 ^ (kSys + 4))) : (uApexShift4 kSys δ).1.mulVec (Pi.single x (1 : ℂ)) =
    DyadicQft64.dyadicTurn 3 (t4CarryExp kSys δ (basisBits (kSys + 4) x)) • Pi.single
    (t4WinPerm kSys δ x) (1 : ℂ) := by
  have hsingle : (Pi.single x (1 : ℂ) : Fin (2 ^ (kSys + 4)) → ℂ) =
      basisKet (basisBits (kSys + 4) x) := pi_single_eq_basisKet x
  have hdiag : (DyadicQft64.dyadicDiagUnitary (kSys + 4) 3 (t4CarryExp kSys δ)).1.mulVec
      (Pi.single x (1 : ℂ)) = DyadicQft64.dyadicTurn 3
      (t4CarryExp kSys δ (basisBits (kSys + 4) x)) • Pi.single x (1 : ℂ) := by
    have hemb := embedUnitary_dyadicDiagUnitary_mulVec_basisKet (QRegExt.idReg (kSys + 4)) 3
        (t4CarryExp kSys δ) (basisBits (kSys + 4) x)
    rw [embedUnitary_idReg_eq] at hemb
    have hid : (fun i ↦ basisBits (kSys + 4) x (QRegExt.idReg (kSys + 4) i)) =
        basisBits (kSys + 4) x := rfl
    rw [hsingle, hemb, hid]
  unfold uApexShift4
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_smul,
    Operator.permutationUnitary_mulVec_single]

theorem bitsVal_fin4_lt (γ : BitAssignment 4) : bitsVal γ < 16 := by
  have h := ((basisBitsEquiv 4).symm γ).isLt
  rwa [symm_bitsVal_eq] at h

theorem uApexShift4_zero (kSys : ℕ) : uApexShift4 kSys (fun _ ↦ (0 : ℤ)) = 1 := by
  apply Subtype.ext
  apply mat_ext_basisKet
  intro β
  let x := (basisBitsEquiv (kSys + 4)).symm β
  have hket : basisKet β = Pi.single x (1 : ℂ) := rfl
  rw [hket, uApexShift4_mulVec_single, OneMemClass.coe_one, Matrix.one_mulVec]
  have hexp : t4CarryExp kSys (fun _ ↦ 0) (basisBits (kSys + 4) x) = 0 := by
    unfold t4CarryExp
    rw [add_zero]
    have hlt : (bitsVal (fun k : Fin 4 ↦ basisBits (kSys + 4) x (Fin.natAdd kSys k)) : ℤ) <
        (2 ^ 4 : ℤ) := by
      exact_mod_cast bitsVal_fin4_lt (fun k ↦ basisBits (kSys + 4) x (Fin.natAdd kSys k))
    exact Int.ediv_eq_zero_of_lt (by positivity) hlt
  have hperm : t4WinPerm kSys (fun _ ↦ 0) x = x := by
    rw [t4WinPerm_apply, stepT4Fin_zero, Prod.mk.eta, Equiv.symm_apply_apply]
  rw [hexp, DyadicQft64.dyadicTurn_zero, one_smul, hperm]

theorem uApexShift4_mul (kSys : ℕ) (δ₁ δ₂ : BitAssignment kSys → ℤ) : uApexShift4 kSys δ₂ *
    uApexShift4 kSys δ₁ = uApexShift4 kSys (fun γ ↦ δ₁ γ + δ₂ γ) := by
  apply Subtype.ext
  apply mat_ext_basisKet
  intro β
  let x := (basisBitsEquiv (kSys + 4)).symm β
  have hket : basisKet β = Pi.single x (1 : ℂ) := rfl
  rw [Submonoid.coe_mul, hket, ← Matrix.mulVec_mulVec, uApexShift4_mulVec_single,
    Matrix.mulVec_smul, uApexShift4_mulVec_single, uApexShift4_mulVec_single,
    smul_smul, DyadicQft64.dyadicTurn_add]
  let γ : BitAssignment kSys := (splitSysCatEquiv kSys 4 x).1
  let m : Fin (2 ^ 4) := (splitSysCatEquiv kSys 4 x).2
  have hx_symm : x = (splitSysCatEquiv kSys 4).symm (γ, m) := by
    dsimp only [γ, m]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
  have hperm1 : t4WinPerm kSys δ₁ x =
      (splitSysCatEquiv kSys 4).symm (γ, stepT4Fin (δ₁ γ) m) := by
    conv_lhs => rw [hx_symm]; exact t4WinPerm_symm_apply kSys δ₁ γ m
  have hperm12 : t4WinPerm kSys (fun γ' ↦ δ₁ γ' + δ₂ γ') x =
      (splitSysCatEquiv kSys 4).symm (γ, stepT4Fin (δ₁ γ + δ₂ γ) m) := by
    conv_lhs => rw [hx_symm]; exact t4WinPerm_symm_apply kSys (fun γ' ↦ δ₁ γ' + δ₂ γ') γ m
  have hperm2 : t4WinPerm kSys δ₂ (t4WinPerm kSys δ₁ x) =
      t4WinPerm kSys (fun γ' ↦ δ₁ γ' + δ₂ γ') x := by
    rw [hperm1, t4WinPerm_symm_apply, stepT4Fin_step, hperm12]
  rw [hperm2]
  congr 2
  have hNatAdd_x :
      (fun k : Fin 4 ↦ basisBits (kSys + 4) x (Fin.natAdd kSys k)) = basisBits 4 m := by
    funext k; conv_lhs => rw [hx_symm]; exact basisBits_splitSysCatEquiv_symm_natAdd γ m k
  have hCastAdd_x : (fun i : Fin kSys ↦ basisBits (kSys + 4) x (Fin.castAdd 4 i)) = γ := by
    funext i; conv_lhs => rw [hx_symm]; exact basisBits_splitSysCatEquiv_symm_castAdd γ m i
  let x₁ := t4WinPerm kSys δ₁ x
  have hNatAdd_x1 : (fun k : Fin 4 ↦ basisBits (kSys + 4) x₁ (Fin.natAdd kSys k)) =
      basisBits 4 (stepT4Fin (δ₁ γ) m) := by
    funext k; dsimp only [x₁]; rw [hperm1]; exact basisBits_splitSysCatEquiv_symm_natAdd γ _ k
  have hCastAdd_x1 : (fun i : Fin kSys ↦ basisBits (kSys + 4) x₁ (Fin.castAdd 4 i)) = γ := by
    funext i; dsimp only [x₁]; rw [hperm1]; exact basisBits_splitSysCatEquiv_symm_castAdd γ _ i
  let K : ℤ := (m.val : ℤ)
  let r₁ := intModFinPow2 4 (K + δ₁ γ)
  let r₂ := intModFinPow2 4 ((r₁.val : ℤ) + δ₂ γ)
  let r₁₂ := intModFinPow2 4 (K + (δ₁ γ + δ₂ γ))
  have hr : r₂ = r₁₂ := by
    dsimp only [r₂, r₁, r₁₂]; rw [intModFinPow2_add_right, add_assoc]
  have hexp1 : t4CarryExp kSys δ₁ (basisBits (kSys + 4) x) = (K + δ₁ γ) / (2 ^ 4 : ℤ) := by
    unfold t4CarryExp; rw [hNatAdd_x, hCastAdd_x, bitsVal_basisBits_eq_val]
  have hexp2 : t4CarryExp kSys δ₂ (basisBits (kSys + 4) x₁) =
      ((r₁.val : ℤ) + δ₂ γ) / (2 ^ 4 : ℤ) := by
    unfold t4CarryExp; rw [hNatAdd_x1, hCastAdd_x1, bitsVal_basisBits_eq_val]; rfl
  have hexp12 : t4CarryExp kSys (fun γ' ↦ δ₁ γ' + δ₂ γ') (basisBits (kSys + 4) x) =
      (K + (δ₁ γ + δ₂ γ)) / (2 ^ 4 : ℤ) := by
    unfold t4CarryExp; rw [hNatAdd_x, hCastAdd_x, bitsVal_basisBits_eq_val]
  rw [hexp1, hexp2, hexp12]
  have hdiv1 := ediv_mul_add_intModFinPow2 4 (K + δ₁ γ)
  have hdiv2 := ediv_mul_add_intModFinPow2 4 ((r₁.val : ℤ) + δ₂ γ)
  have hdiv12 := ediv_mul_add_intModFinPow2 4 (K + (δ₁ γ + δ₂ γ))
  have hr_coe : (r₂.val : ℤ) = (r₁₂.val : ℤ) := congrArg (fun u : Fin (2 ^ 4) ↦ (u.val : ℤ)) hr
  have hmul : (2 ^ 4 : ℤ) * (((r₁.val : ℤ) + δ₂ γ) / (2 ^ 4 : ℤ) + (K + δ₁ γ) / (2 ^ 4 : ℤ) -
      (K + (δ₁ γ + δ₂ γ)) / (2 ^ 4 : ℤ)) = 0 := by
    dsimp only [r₁, r₂, r₁₂] at hr_coe
    linear_combination hdiv1 + hdiv2 - hdiv12 - hr_coe
  have hsub := (mul_eq_zero.mp hmul).resolve_left (by positivity : (2 ^ 4 : ℤ) ≠ 0)
  linarith

theorem uApexShift4_inv (kSys : ℕ) (δ : BitAssignment kSys → ℤ) :
    (uApexShift4 kSys δ)⁻¹ = uApexShift4 kSys (fun γ ↦ -δ γ) := by
  apply inv_eq_of_mul_eq_one_left
  rw [uApexShift4_mul]
  have h0 : (fun γ ↦ δ γ + -δ γ) = (fun _ ↦ (0 : ℤ)) := by funext γ; ring
  rw [h0, uApexShift4_zero]

theorem uApexShift4_comm_coreDiag (kSys B : ℕ) (e : BitAssignment kSys → ℤ)
    (δ : BitAssignment kSys → ℤ) : (QRegister.block 0 kSys
    (by omega : 0 + kSys ≤ kSys + 4)).embedUnitary (DyadicQft64.dyadicDiagUnitary kSys B e) *
    uApexShift4 kSys δ = uApexShift4 kSys δ * (QRegister.block 0 kSys
    (by omega : 0 + kSys ≤ kSys + 4)).embedUnitary (DyadicQft64.dyadicDiagUnitary kSys B e)
    := by
  let rSys0 : QRegister kSys (kSys + 4) := QRegister.block 0 kSys (by omega)
  apply Subtype.ext
  apply mat_ext_basisKet
  intro β
  let x := (basisBitsEquiv (kSys + 4)).symm β
  have hket : basisKet β = Pi.single x (1 : ℂ) := rfl
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul]
  rw [hket, uApexShift4_mulVec_single, Matrix.mulVec_smul, smul_smul]
  let x' := t4WinPerm kSys δ x
  rw [pi_single_eq_basisKet x', embedUnitary_dyadicDiagUnitary_mulVec_basisKet, smul_smul]
  congr 1
  have hSysEq : (fun i ↦ basisBits (kSys + 4) x' (rSys0 i)) = (fun i ↦ β (rSys0 i)) := by
    funext i
    have hr : rSys0 i = Fin.castAdd 4 i := Fin.ext (by simp [rSys0])
    dsimp only [x']
    rw [hr, t4WinPerm_apply, basisBits_splitSysCatEquiv_symm_castAdd]
    change basisBits (kSys + 4) x (Fin.castAdd 4 i) = β (Fin.castAdd 4 i)
    rw [basisBits_basisBitsEquiv_symm_eq]
  rw [hSysEq, mul_comm]

theorem embed_uApexShift4_mulVec_basisKet {kSys n : ℕ}
    (rSys : QRegister kSys n) (rT4 : QRegister 4 n) (hdisj : rSys.DisjointWires rT4)
    (δ : BitAssignment kSys → ℤ) (ξ : BitAssignment n) :
    ((rSys.concat rT4 hdisj).embedUnitary (uApexShift4 kSys δ)).1.mulVec (basisKet ξ) =
      apexCarryPhase rT4 ξ (δ (fun i ↦ ξ (rSys i))) •
        basisKet (shiftRegInt rT4 ξ (δ (fun i ↦ ξ (rSys i)))) := by
  let rSC := rSys.concat rT4 hdisj
  let idx₀ := (basisBitsEquiv n).symm ξ
  let x₀ := rSC.extractIndex idx₀
  have hsingle : basisKet ξ = Pi.single idx₀ (1 : ℂ) := rfl
  rw [QRegister.embedUnitary_val, hsingle, rSC.embedMatrix_mulVec_single_factors,
    uApexShift4_mulVec_single, rSC.tensorState_smul_left, rSC.tensorState_single_replaceIndex]
  have hext_sys :
      (fun i : Fin kSys ↦ basisBits (kSys + 4) x₀ (Fin.castAdd 4 i)) = fun i ↦ ξ (rSys i) := by
    funext i; simp [x₀, rSC, idx₀]
  have hext_cat :
      (fun k : Fin 4 ↦ basisBits (kSys + 4) x₀ (Fin.natAdd kSys k)) = fun k ↦ ξ (rT4 k) := by
    funext k; simp [x₀, rSC, idx₀]
  have hWinEq : bitsVal (fun k : Fin 4 ↦ ξ (rT4 k)) = regVal rT4 ξ := rfl
  have hPhase : DyadicQft64.dyadicTurn 3 (t4CarryExp kSys δ (basisBits (kSys + 4) x₀)) =
      apexCarryPhase rT4 ξ (δ (fun i ↦ ξ (rSys i))) := by
    unfold t4CarryExp apexCarryPhase
    rw [hext_cat, hext_sys, hWinEq]
  rw [hPhase]
  congr 1
  rw [pi_single_eq_basisKet]
  congr 1
  let p₀ := splitSysCatEquiv kSys 4 x₀
  have hp1 : p₀.1 = fun i ↦ ξ (rSys i) := hext_sys
  have hp2 : basisBits 4 p₀.2 = fun k ↦ ξ (rT4 k) := by
    change basisBits 4 ((basisBitsEquiv 4).symm _) = _
    rw [basisBits_basisBitsEquiv_symm_eq]
    exact hext_cat
  have hperm : t4WinPerm kSys δ x₀ = (splitSysCatEquiv kSys 4).symm
      (p₀.1, stepT4Fin (δ p₀.1) p₀.2) := t4WinPerm_apply kSys δ x₀
  apply eq_shiftRegInt_of_outside_and_regVal rT4 _ ξ (δ (fun i ↦ ξ (rSys i)))
  · intro w hwNotWin
    by_cases hwSC : w ∈ Set.range rSC.wires
    · rcases hwSC with ⟨idx, rfl⟩
      rw [rSC.basisBits_replaceIndex_apply, hperm]
      revert hwNotWin
      refine Fin.addCases (fun i _ ↦ ?_) (fun k hwNotWin ↦ ?_) idx
      · rw [QRegister.concat_apply_left, basisBits_splitSysCatEquiv_symm_castAdd, hp1]
      · exfalso
        apply hwNotWin
        rw [QRegister.mem_image]
        exact ⟨k, (QRegister.concat_apply_right rSys rT4 hdisj k).symm⟩
    · rw [rSC.basisBits_replaceIndex_of_not_mem idx₀ _ w hwSC]
      simp [idx₀]
  · conv_lhs => unfold regVal
    have hInWin : (fun j : Fin 4 ↦
        basisBits n (rSC.replaceIndex idx₀ (t4WinPerm kSys δ x₀)) (rT4 j)) =
        basisBits 4 (intModFinPow2 4 ((regVal rT4 ξ : ℤ) + δ (fun i ↦ ξ (rSys i)))) := by
      funext j
      have hrw : rT4 j = rSC (Fin.natAdd kSys j) :=
        (QRegister.concat_apply_right rSys rT4 hdisj j).symm
      rw [hrw, rSC.basisBits_replaceIndex_apply, hperm, basisBits_splitSysCatEquiv_symm_natAdd]
      unfold stepT4Fin
      have hmEq : (p₀.2.val : ℤ) = (regVal rT4 ξ : ℤ) := by
        have hv := bitsVal_basisBits_eq_val p₀.2
        rw [hp2, hWinEq] at hv
        exact_mod_cast hv.symm
      rw [hmEq, hp1]
    rw [hInWin, bitsVal_basisBits_eq_val]

/-- Core `fullSysCoreWires mPayload` block inside `fullSysCoreWires mPayload + 4`. -/
def rCoreBlock4 (mPayload : ℕ) :
    QRegister (fullSysCoreWires mPayload) (fullSysCoreWires mPayload + 4) :=
  QRegister.block 0 (fullSysCoreWires mPayload) (by omega)

theorem compose_rCoreBlock4_eq {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (hCT4 : rCore.DisjointWires rT4) :
    (rCore.concat rT4 hCT4).compose (rCoreBlock4 mPayload) = rCore := by
  apply qreg_ext_local
  intro i
  change (rCore.concat rT4 hCT4) ⟨0 + i.val, _⟩ = rCore i
  have hEq : (⟨0 + i.val, by have := i.isLt; omega⟩ : Fin (fullSysCoreWires mPayload + 4)) =
      Fin.castAdd 4 i := Fin.ext (Nat.zero_add i.val)
  rw [hEq, QRegister.concat_apply_left]

/-- Single-axis `Slot 4` catalyzed unitary directly on `fullSysCoreWires mPayload + 4` (`rT4`). -/
noncomputable def uSlot4AxisCatT4 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) (w : Fin 3) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 4)) :=
  uApexShift4 (fullSysCoreWires mPayload) (slot4LowShift isInv hm w) *
    (rCoreBlock4 mPayload).embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (slot4TopExp isInv hm w))

theorem uSlot4AxisCatT4_inv_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    (uSlot4AxisCatT4 false hm w)⁻¹ = uSlot4AxisCatT4 true hm w := by
  unfold uSlot4AxisCatT4
  rw [_root_.mul_inv_rev, uApexShift4_inv, ← QRegister.embedUnitary_inv,
    DyadicQft64.dyadicDiagUnitary_inv]
  have h1 : (fun γ ↦ -slot4LowShift false hm w γ) = slot4LowShift true hm w := by
    funext γ; unfold slot4LowShift slot4Sgn
    split_ifs <;> (try contradiction) <;> ring
  have h2 : (fun γ ↦ -slot4TopExp false hm w γ) = slot4TopExp true hm w := by
    funext γ; unfold slot4TopExp slot4Sgn
    split_ifs <;> (try contradiction) <;> ring
  rw [h1, h2]
  exact uApexShift4_comm_coreDiag (fullSysCoreWires mPayload) 48
    (slot4TopExp true hm w) (slot4LowShift true hm w)

/-- Three-axis `Slot 4` catalyzed unitary directly on `fullSysCoreWires mPayload + 4` (`rT4`). -/
noncomputable def uSlot4ApexCatT4 {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 4)) :=
  uSlot4AxisCatT4 false hm 2 * (uSlot4AxisCatT4 false hm 1 * uSlot4AxisCatT4 false hm 0)

/-- Embedding selector mapping `(rCore, rT4)` (`4` catalyst wires `[41..45)`) into
`(rCore, rPG48)`. -/
def selCT4InCT (mPayload : ℕ) :
    QRegister (fullSysCoreWires mPayload + 4) (fullSysCoreWires mPayload + 48) :=
  let rC := rCoreBlock48 mPayload
  let rT := (QRegister.block (fullSysCoreWires mPayload) 48 (by omega)).slice 41 4 (by omega)
  have hDisj : rC.DisjointWires rT := by
    rw [QRegister.disjoint_iff]
    intro i j h
    have hv := congrArg Fin.val h
    simp [rC, rT, QRegister.slice, QRegister.block] at hv
    have := i.isLt
    omega
  rC.concat rT hDisj

theorem compose_selCT4InCT_eq {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (hCP : rCore.DisjointWires rPGTwist) :
    (rCore.concat rPGTwist hCP).compose (selCT4InCT mPayload) =
      rCore.concat (rPGTwist.slice 41 4 (by omega)) (hCP.compose_right _) := by
  apply qreg_ext_local
  intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · change (rCore.concat rPGTwist hCP) ((selCT4InCT mPayload) (Fin.castAdd 4 i)) = _
    unfold selCT4InCT
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hEq : (rCoreBlock48 mPayload) i = Fin.castAdd 48 i := Fin.ext (Nat.zero_add i.val)
    rw [hEq, QRegister.concat_apply_left]
  · change (rCore.concat rPGTwist hCP) ((selCT4InCT mPayload) (Fin.natAdd _ j)) = _
    unfold selCT4InCT
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
    have h1 : ((QRegister.block (fullSysCoreWires mPayload) 48
        (by omega : fullSysCoreWires mPayload + 48 ≤ fullSysCoreWires mPayload + 48)).slice
          41 4 (by omega)) j =
        Fin.natAdd (fullSysCoreWires mPayload) ⟨41 + j.val, by omega⟩ :=
      Fin.ext (by simp [QRegister.slice, QRegister.block, Fin.natAddEmb, Nat.add_assoc])
    rw [h1, QRegister.concat_apply_right]
    exact (slice_apply_eq rPGTwist (by omega) j).symm

theorem embed_selCT4InCT_uSlot4AxisCatT4 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    (w : Fin 3) : (selCT4InCT mPayload).embedUnitary (uSlot4AxisCatT4 isInv hm w) =
    uSlot4AxisCat isInv hm w := by
  let rC : QRegister (fullSysCoreWires mPayload) (fullSysCoreWires mPayload + 48) :=
    rCoreBlock48 mPayload
  let rP : QRegister 48 (fullSysCoreWires mPayload + 48) :=
    QRegister.block (fullSysCoreWires mPayload) 48 (by omega)
  have hCP : rC.DisjointWires rP := by
    rw [QRegister.disjoint_iff]; intro i j h
    have hv := congrArg Fin.val h
    simp [rC, rP, QRegister.block] at hv
    have := i.isLt; omega
  have hId : rC.concat rP hCP = QRegExt.idReg (fullSysCoreWires mPayload + 48) := by
    apply qreg_ext_local
    intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (Nat.zero_add i.val)
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [rP, QRegister.block])
  apply Subtype.ext
  apply mat_ext_basisKet
  intro ξ
  have hL : (selCT4InCT mPayload).embedUnitary (uSlot4AxisCatT4 isInv hm w) =
      (rC.concat (rP.slice 41 4 (by omega)) (hCP.compose_right _)).embedUnitary
        (uSlot4AxisCatT4 isInv hm w) := rfl
  have hR : uSlot4AxisCat isInv hm w =
      (rC.concat rP hCP).embedUnitary (uSlot4AxisCat isInv hm w) := by
    rw [hId, embedUnitary_idReg_eq]
  rw [hL, hR]
  unfold uSlot4AxisCatT4 uSlot4AxisCat
  rw[QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, Submonoid.coe_mul,
      Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
      compose_rCoreBlock4_eq rC (rP.slice 41 4 (by omega)) (hCP.compose_right _),
      compose_rCoreBlock48_eq rC rP hCP, embedUnitary_dyadicDiagUnitary_mulVec_basisKet,
      Matrix.mulVec_smul, Matrix.mulVec_smul,
      embed_uApexShift4_mulVec_basisKet rC (rP.slice 41 4 (by omega)) (hCP.compose_right _),
      embed_uApexShift45_mulVec_basisKet (by omega) rC rP hCP]

theorem embed_selCT4InCT_uSlot4ApexCatT4 {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    (selCT4InCT mPayload).embedUnitary (uSlot4ApexCatT4 hm) = uSlot4ApexCat hm := by
  unfold uSlot4ApexCatT4 uSlot4ApexCat
  simp only [QRegister.embedUnitary_mul, embed_selCT4InCT_uSlot4AxisCatT4]

/- ## Section 1B: `13`-Wire Pruned `Slot 4`
(`dSlot4StandaloneT4_13` & `dSlot4Standalone13`, `146 T`) -/

/-- Seals a noncomputable value behind `Classical.choose` to block accidental kernel unfolding. -/
noncomputable def lockValW7 {α : Sort _} (x : α) : α :=
  Classical.choose (p := fun y ↦ y = x) ⟨x, rfl⟩

theorem lockValW7_eq {α : Sort _} (x : α) : lockValW7 x = x :=
  Classical.choose_spec (p := fun y ↦ y = x) ⟨x, rfl⟩

theorem peelWorkT4_13 {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload n : ℕ} (k : ℕ) (hk : k + 1 ≤ 13)
    (b₁ b₂ bOut : Bool) (v : Var)
    (c₁ c₂ : Wire n)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork)
    (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ rWork ⟨k, by dsimp [mWork13]; omega⟩)
    (h₂a : c₂ ≠ rWork ⟨k, by dsimp [mWork13]; omega⟩)
    (hc1Tot : c₁ ∉ (rWork.slice k (13 - k) (by dsimp [mWork13]; omega)).image)
    (hc2Tot : c₂ ∉ (rWork.slice k (13 - k) (by dsimp [mWork13]; omega)).image)
    (hc1S : c₁ ∈ (rHigh rCore).image ∪
      (rWork.slice 0 k (by dsimp [mWork13]; omega)).image)
    (hc2S : c₂ ∈ (rHigh rCore).image ∪
      (rWork.slice 0 k (by dsimp [mWork13]; omega)).image)
    {H_outer : BitAssignment n → Prop}
    (hH_anc : ∀ ξ₁ ξ₂ : BitAssignment n,
      (∀ w, w ≠ rWork ⟨k, by dsimp [mWork13]; omega⟩ → ξ₁ w = ξ₂ w) →
      H_outer ξ₁ → H_outer ξ₂)
    {H_inner : BitAssignment n → Prop}
    (hH_imp : ∀ η : BitAssignment n,
      H_outer η ∧
        η (rWork ⟨k, by dsimp [mWork13]; omega⟩) =
          genBoolBit b₁ b₂ bOut (η c₁) (η c₂) →
      H_inner η)
    {U : Unitary (2 ^ (fullSysCoreWires mPayload + 4))}
    {dInner : DynamicCircuit Var n}
    (hsInner : CondStageSpec (rCore.concat rT4 hCT4)
      (rWork.slice (k + 1) (13 - (k + 1)) (by dsimp [mWork13]; omega))
      ((rHigh rCore).image ∪
        (rWork.slice 0 (k + 1) (by dsimp [mWork13]; omega)).image)
      H_inner U dInner) :
    CondStageSpec (rCore.concat rT4 hCT4)
      (rWork.slice k (13 - k) (by dsimp [mWork13]; omega))
      ((rHigh rCore).image ∪
        (rWork.slice 0 k (by dsimp [mWork13]; omega)).image)
      H_outer U
      (dGenBoolWrap b₁ b₂ bOut v c₁ c₂
        (rWork ⟨k, by dsimp [mWork13]; omega⟩) h₁₂ h₁a h₂a dInner) := by
  have hMW : mWork13 = 13 := rfl
  let anc : Wire n := rWork ⟨k, by omega⟩
  let rSub := rWork.slice (k + 1) (13 - (k + 1)) (by omega)
  let rTot := rWork.slice k (13 - k) (by omega)
  let S_inner := (rHigh rCore).image ∪ (rWork.slice 0 (k + 1) (by omega)).image
  let S_outer := (rHigh rCore).image ∪ (rWork.slice 0 k (by omega)).image
  have hSubTot : rSub.image ⊆ rTot.image := slice_sub_slice_b2 rWork (k + 1) (13 - (k + 1)) k
      (13 - k) (by omega) (by omega) (by omega) (by omega)
  have hAncTot : anc ∈ rTot.image :=
    reg_mem_slice_b2 rWork k (13 - k) (by omega) ⟨k, by omega⟩
      (by dsimp; omega) (by dsimp; omega)
  have hancSub : anc ∉ rSub.image :=
    reg_not_mem_slice_b2 rWork (k + 1) (13 - (k + 1)) (by omega) ⟨k, by omega⟩
      (by dsimp; omega)
  have hancAct : anc ∉ (rCore.concat rT4 hCT4).image := by
    rw [qreg_image_concat]
    intro hm_in
    have hancWork : anc ∈ rWork.image := (QRegister.mem_image rWork _).mpr ⟨⟨k, by omega⟩, rfl⟩
    rcases Finset.mem_union.mp hm_in with hC | hT
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC hancWork
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hTW) hT hancWork
  have hCov : S_outer ∪ rTot.image ⊆ S_inner ∪ rSub.image := by
    intro w hw
    rcases Finset.mem_union.mp hw with hSo | hWt
    · rcases Finset.mem_union.mp hSo with hH | hSk
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hH)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (slice_sub_slice_b2 rWork 0 k
          0 (k + 1) (by omega) (by omega) (by omega) (by omega) hSk))
    · rcases (QRegister.mem_image rTot w).mp hWt with ⟨j, rfl⟩
      rw [slice_apply_eq]
      have hj := j.isLt
      by_cases hj0 : j.val = 0
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        exact reg_mem_slice_b2 rWork 0 (k + 1) (by omega) ⟨k + j.val, by omega⟩
          (by dsimp; omega) (by dsimp; omega)
      · refine Finset.mem_union_right _ ?_
        exact reg_mem_slice_b2 rWork (k + 1) (13 - (k + 1)) (by omega) ⟨k + j.val, by omega⟩
          (by dsimp; omega) (by dsimp; omega)
  exact CondStageSpec.dGenBoolWrap b₁ b₂ bOut v c₁ c₂ anc h₁₂ h₁a h₂a rSub rTot hSubTot
    hAncTot hc1Tot hc2Tot hancSub hancAct hc1S hc2S hCov hH_anc (hsInner.weaken_H hH_imp)

/-- Coin-`0` flag invariant (`rWork 1 = [s2 = 0 ∧ s1 = 0 ∧ s0 = 0]`) on `13`-wire workspace. -/
def hCoin0Flag13 {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWork13 n) (ξ : BitAssignment n) : Prop := ξ (rWork 1) = if coin0Active
    (fun q ↦ ξ (rCore q)) then 1 else 0

/-- `Slot 4` active-coin flag invariant (`rWork 0 = [s2 = 0 ∧ s1 = 0 ∧ s0 = 1]`) on `13` wires. -/
def hSlot4Flag13 {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWork13 n) (ξ : BitAssignment n) : Prop := ξ (rWork 0) = if
    (ξ (wSlot2 rCore) = 0 ∧ ξ (wSlot1 rCore) = 0 ∧ ξ (wSlot0 rCore) = 1) then 1 else 0

theorem hSlot4Flag13_congr_S {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWork : QRegister mWork13 n)
    {S : Finset (Wire n)} (hHigh : (rHigh rCore).image ⊆ S) (hw0 : rWork 0 ∈ S) : ∀ ξ₁ ξ₂ :
    BitAssignment n, (∀ w ∈ S, ξ₁ w = ξ₂ w) →
    (hSlot4Flag13 rCore rWork ξ₁ ↔ hSlot4Flag13 rCore rWork ξ₂) := by
  intro ξ₁ ξ₂ hEq
  unfold hSlot4Flag13
  rw[hEq (rWork 0) hw0, hEq (wSlot2 rCore) (hHigh (wSlot2_mem_rHigh rCore)),
      hEq (wSlot1 rCore) (hHigh (wSlot1_mem_rHigh rCore)),
      hEq (wSlot0 rCore) (hHigh (wSlot0_mem_rHigh rCore))]

/-- Combined `(pos01, coin0)` flag invariant on `rWork[0..2)` of the `13`-wire workspace. -/
def hPos01AndCoin0_13 {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWork13 n) (ξ : BitAssignment n) : Prop := (ξ (rWork 0) = if (ξ (wSlot2
    rCore) = 0 ∧ ξ (wSlot1 rCore) = 0) then 1 else 0) ∧ hCoin0Flag13 rCore rWork ξ

theorem slot4_coset_b0_ne_b1 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) :
    rCosetB0 hm rCore w ≠ rCosetB1 hm rCore w := by
  have := w.isLt
  have hfcw := fullSysCoreWires_eq_3954_add mPayload
  unfold rCosetB0 rCosetB1
  simp only [slice_apply_eq]
  exact core_wire_ne rCore (by dsimp; omega)

theorem slot4_s2_ne_s1 {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    wSlot2 rCore ≠ wSlot1 rCore := by
  have hfcw := fullSysCoreWires_eq_3954_add mPayload
  unfold wSlot2 wSlot1
  exact core_wire_ne rCore (by dsimp; omega)

theorem slot4_w0_ne_w1 {n : ℕ} (rWork : QRegister mWork13 n) :
    rWork 0 ≠ rWork ⟨1, by decide⟩ := fun h ↦ by
  have hv := congrArg Fin.val (rWork.wires.injective h); dsimp [mWork13] at hv; omega

open Barrel3PassCommuteHelpers
open Barrel3PassSelectStitch
open HoistedSwapSelectBridge (unitaryConj unitaryConj_val)
open CoinDispatchedBarrel288 (uBarrelFast)
open LiteralKineticAndMidpoint128 (lambdaSlot0TeHi)
open Pass1Leaf273 hiding
  pass1SpecOfLe pass1SpecOfLe_tLeaf pass1SpecOfLe_uEff
  pass3SpecOfLe pass3SpecOfLe_tLeaf pass3SpecOfLe_uEff

theorem embedUnitary_unitaryConj {k m : ℕ} (emb : QRegister k m) (B U : Unitary (2 ^ k)) :
    emb.embedUnitary (unitaryConj B U) = unitaryConj (emb.embedUnitary B) (emb.embedUnitary U)
    := by
  apply Subtype.ext
  have hB : (B⁻¹).1 = B.1ᴴ := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  have hEB : ((emb.embedUnitary B)⁻¹).1 = (emb.embedUnitary B).1ᴴ := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  rw [unitaryConj_val, ← hEB, ← Submonoid.coe_mul, ← Submonoid.coe_mul,
    ← QRegister.embedUnitary_inv, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
  congr 2

/-- Combined Pass-1 inner unitary on `4,034 + 4` wires (`Slot 4` followed by `Slot 0` `XorBit5`). -/
noncomputable def uPass1InnerT4 : Unitary (2 ^ (fullSysCoreWires 80 + 4)) :=
  (rCoreBlock4 80).embedUnitary (uSlot0LocalXorBit5 hm80_80 lambdaSlot0TeHi) *
    uSlot4ApexCatT4 hm22_80

/-- Catalyzed `4,038`-wire (`rCore ++ rT4`) unitary realized by Unclamped `Pass 1`. -/
noncomputable def uPass1CatT4 : Unitary (2 ^ (fullSysCoreWires 80 + 4)) :=
  unitaryConj ((rCoreBlock4 80).embedUnitary (uBarrelFast hm80_80)) uPass1InnerT4

section Part2B_Pullbacks
set_option exponentiation.threshold 8192

theorem selCT4InCT_compose_rCoreBlock4_eq :
    (selCT4InCT 80).compose (rCoreBlock4 80) = rCoreBlock48 80 := by
  apply QRegister.ext (Function.Embedding.ext fun i ↦ ?_)
  change (selCT4InCT 80) ((rCoreBlock4 80) i) = (rCoreBlock48 80) i
  have h1 : (rCoreBlock4 80) i = Fin.castAdd 4 i := Fin.ext (Nat.zero_add i.val)
  rw [h1]
  unfold selCT4InCT
  rw [QRegister.concat_apply_left]

theorem embed_selCT4InCT_uPass1InnerT4 :
    (selCT4InCT 80).embedUnitary uPass1InnerT4 = uPass1InnerCT := by
  unfold uPass1InnerT4 uPass1InnerCT
  rw [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose,
    selCT4InCT_compose_rCoreBlock4_eq, embed_selCT4InCT_uSlot4ApexCatT4]

theorem embed_selCT4InCT_uPass1CatT4 :
    (selCT4InCT 80).embedUnitary uPass1CatT4 = uPass1Cat := by
  unfold uPass1CatT4 uPass1Cat
  rw [embedUnitary_unitaryConj, ← QRegister.embedUnitary_compose,
    selCT4InCT_compose_rCoreBlock4_eq, embed_selCT4InCT_uPass1InnerT4]

set_option exponentiation.threshold 256
end Part2B_Pullbacks

section Part2D_CTLeafSpec
set_option exponentiation.threshold 8192

/-- Turnkey `Pass 3` `CTLeafAlgSpec` for any `133 ≤ mWB`. -/
noncomputable def pass3SpecOfLe {mWB : ℕ} (_hmWB : 133 ≤ mWB) : CTLeafAlgSpec where
  uCat := fun _ ↦ uPass3Cat
  uEff := fun _ ↦ uPass3Eff
  hIntertwines := fun _ U_cat48 hcol ↦ uPass3Cat_intertwinesLocal U_cat48 hcol

@[simp] theorem pass3SpecOfLe_uEff {mWB : ℕ} (hmWB : 133 ≤ mWB) (c : Configuration) :
    (pass3SpecOfLe hmWB).uEff c = uPass3Eff := rfl

/-- Turnkey `Pass 1` `CTLeafAlgSpec` for any `154 ≤ mWB`. -/
noncomputable def pass1SpecOfLe {mWB : ℕ} (_hmWB : 154 ≤ mWB) : CTLeafAlgSpec where
  uCat := fun _ ↦ uPass1Cat
  uEff := fun _ ↦ uPass1Eff
  hIntertwines := fun _ U_cat48 hcol ↦ uPass1Cat_intertwinesLocal U_cat48 hcol

@[simp] theorem pass1SpecOfLe_uEff {mWB : ℕ} (hmWB : 154 ≤ mWB) (c : Configuration) :
    (pass1SpecOfLe hmWB).uEff c = uPass1Eff := rfl

set_option exponentiation.threshold 256
end Part2D_CTLeafSpec

set_option maxRecDepth 512

end ConfigLeaf1Pass1And3Width204

end Leaf1Pass1And3Width204

end
set_option exponentiation.threshold 256
end Leaf1Pass1And3Width204

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
