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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosSlot2FermBridge

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModPos24Slot4FermionicBridge
@[expose] public section
namespace Pos24Slot4FermionicBridge
open Operator QProg Matrix Real
open SpecsAux.BridgeFermionicComm (commutes_groupAvgProj)
open SpecsAux.BridgeFermionicComm.SpecInner (basisBits_permElectron
  div_18_lt_numElectrons fermionicProjector_eq_groupAvgProj fermionicProjector_idem permElectron
    permElectronWire permElectronWireFun spinGroupAux)
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 NyqGrid3D64 NyqParity3D
  anchorParity1D anchorSubTarget1D kHead128 kHead128_add_kTail128 kTailShifted128 nyq128Equiv3D_val
    omega128_add subGridUnitary64)
open SpecsAux.SpecMirror (Configuration IsGridState electronBits
  fermionicProjector numElectrons projectileBits systemQubits)
open SpecsAux.FullScaleBESector (AgreesOnFermionicSector)
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (norm_projector_le_one)
open BchCubeDecoder (diagonalSignUnitaryN proj38ZeroBit
  proj38OddXorZeroBit proj38_zeroParity_slot4_pauliCap_eq zeroParityThreshExp)
open CanonRank7Circuit (fineCoordOfReg21)
open Dyadic128CoulombMath (FineCoord128 canonTriple128 orbitCount47905
  orbitParityWeight subGridWeight128_eq_orbit tetRank65)
open Dyadic128OrbitTableCert (w128DualQ30)
open DyadicQft64WalkCircuit (nyqParity3DEquivFin8 qft64Ideal654Unitary
  qft64Ideal654Unitary_mul_cosetProj_eq_elec3DProd qft64OffsetUnitary3D qft64OffsetUnitary3D_apply
    rCoset3In654 rElec18In654 u18GridEquiv)
open FullSysCatSegmentBridge (FullSysQft654Bundle coreCosetB1Block
  coreElecBlock fullSysCoreWires)
open KaratsubaQft64Matrix (bitRev6Equiv karatsubaOffsetUnitary128)
open NuclearTwistAndXor654Concrete (dyadicTurn
  dyadicTurn48_shift41_eq_omega128 rElecSlotAxis slot4CosetDiag18 slot4_barrelSwap_and_coset_conj
    wSlot0 wSlot1 wSlot2)
open NuclearTwistRealizes (uTwistParam)
open PosSlots24BranchConcrete (axisBitRev6 headPhaseBitSpec parity3OfReg
  posCoreWires posPayloadWires posPhaseBit rAnchorIdx rCosetB0 rCosetB1 rElecSlot rHeadFine21
    rNucIdx rPartnerIdx rSubPayloadCore rTailKeep30 slotSubGridCoord64 tailAndSlackPhaseBitSpec
      tailFineDiff1D_eq uPosPhase wHeadThresh wIsHead wRejectZero wSlot0Core wSlot1Core wSlot2Core
        wSubReject)
open PosSlots24Semantic80Physics (HeadSupportIdx TailSupportIdx
  bitsVal_z2BitOfNat_of_lt headWitnessPayload80 pos80IdealDist pos80SubIdx pos80WitnessOf
    pos80WitnessOf_eval_head pos80WitnessOf_eval_tail sum_over_pos80IdealDist_support
      tailSpan8_lt_two_pow_30 tailWitnessPayload80 z2BitOfNat z2BitOfNat_val)
open PosSlots24SemanticBridge (castUnitaryPow2 mulUnitaryPow2 pos24CutNyq
  pos24HalfSpanQb pos24HeadU56 pos24HeadV56 pos24HeadW56 pos24HeadWeight56 pos24MinNyq pos24OhPoint
    pos24TailMag30_le_halfSpan pos24TailSpan8 pos24_core80_eq_twist80 pos24_coreWires80_eq
      pos24_oh_head_sum_eq pos24_shell_cert pos24ConjCore80 subGridParityWeight3_nyqParityToBool
        subGridWeight128_eq_nyqParity)
open PosSlots24SemanticOracleConcrete80 (PreservesCoreAnc
  QftPreservesCoset3 basisBits_symm_apply_fun basisOutcomeProjector_compose_local coherentSysOp80
    coreBetaOf_lt3948 coreBetaOf_mid coreElecCosetB1_compose_rCoset3
      coreElecCosetB1_disjoint_rAncRest83 coreIdxOf coreIdxOf_injective
        embedMatrix_entry_of_agreeOutside embedMatrix_entry_of_not_agreeOutside
          entry_zero_of_comm_basisOutcomeProjector lt_sys_4034 ofFin_embedUnitary_eq pos80Slot4Scale
            pos80Slot4Scale_pos pos80Slot4TotNat qftPreservesCoset3_of_eq_ideal rAncFlag80
              rAncFlag80_basisOutcomeProjector_factor rAncFlag80_wire_ge_3948 rAncRest83
                regVal_eq_of_wire_eq sysBlockAtPayloadGen_apply
                  sysBlockAtPayloadGen_conj_of_preserves sysBlockAtPayloadGen_mul_of_preserves
                    uPosPhase_cast_comm_diagonal uTwistParam_cast_comm_highReg_proj)
open PosSlots24TopWrapper (rPosSubLocal)
open SingleAnchorFermionicPauliCap (emb_rEl_mul_pe_sp
  gridProjector_comm_permutationUnitary gridProjector_eq_predProjector nSub_sp op_sp
    rEl_disjoint_of_ne_sp rEl_sp rk1_sp sandwich_comm_of_comm sandwich_mul_idem_comm
      singleAnchorPairOp_cubic_mul_fermionicProjector_zero singleAnchorPairOp_isHermitian)
open Slot2Slot4QuantizedChannelBridge (anchorSubTargetEquiv
  signedMagToOffset6Equiv sum_dy_singleAnchorPairOp_eq_const u18AxisSplitEquiv veeCenteredShift
    veeMidpointShift veeSingleAnchorRaw veeSingleAnchorRaw_comm_perm veeSubGridKet_complete
      veeSubGridKet_norm_sq veeSubGridKet_orthonormal)
open TwosCompAndWire0Cancel (bitRev6GridEquiv elec654Axes elecAxisField
  elecAxisField_smToTwos654 elecAxisField_smToTwosProj3 elecAxisField_smToTwosSys
    extractIndex_block_val fwdPermUnitary_apply fwdPermUnitary_conj_diagonal
      karatsubaOffset3D128_apply karatsubaOutPhase3D karatsubaOutPhase3D_unit proj3Axes
        projAxisField projAxisField_smToTwos654 projAxisField_smToTwosProj3
          projAxisField_smToTwosSys smToTwos654SysUnitary smToTwosAxisPerm smToTwosAxisPerm_self
            smToTwosAxisPerm_val smToTwosSysPerm smToTwosSysUnitary
              smToTwosSysUnitary_conjTranspose)
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators
open NuclearTwistAndXor654Concrete renaming fullSysCoreWires → twCW,
  rAnchorIdx → twAnc
open SpecsAux.DyadicSubgridToeplitz128 renaming anchorSubTarget3D → ancTgt,
  nyq128Equiv3D → nyq3D, anchorParity3D → ancPar
open Slot2Slot4QuantizedChannelBridge renaming veeSubGridKet → vKet,
  elecOffsetGridEquiv18 → eOff18
open PosSlots24SemanticBridge renaming sysBlockAtPayloadGen → sysBlk,
  pos24_22_le_80 → h22_80, pos24_6_le_80 → h6_80, pos24TailMag30 → tMag30, pos24TailSign → tSgn
open TwosCompAndWire0Cancel renaming smToTwosProj3Perm → pSmP3,
  smToTwos654SysPerm → pSm654, fwdPermUnitary → fwdPU
open SingleAnchorFermionicPauliCap renaming singleAnchorPairOp → saPair
open FullSysCatSegmentBridge renaming coreElecCosetB1Block → cElB1,
  fullSysQftCoreUnitary → fQftU
open PosSlots24SemanticOracleConcrete80 renaming coreBetaOf_payload →
  cB_pay, coreBetaOf → cBeta
section ConfigPos24Slot4FermionicBridge
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowSlot4Bridge (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
abbrev idReg (n : ℕ) : QRegister n n := QRegExt.idReg n
abbrev SysIdx : Type := Fin (2 ^ systemQubits)
abbrev SysOp : Type := Operator (2 ^ systemQubits)
abbrev Pay80 : Type := BitAssignment 80
abbrev nyqP8 : Fin 8 ≃ NyqParity3D := nyqParity3DEquivFin8.symm
theorem bb_ext {k n : ℕ} (r : QRegister k n) (x : Fin (2 ^ n)) (i : Fin k) : basisBits k
    (r.extractIndex x) i = basisBits n x (r i) := QRegister.basisBits_extractIndex r x i
theorem m_assoc {D : ℕ} (A B C : Operator D) : A * B * C = A * (B * C) :=
  Matrix.mul_assoc A B C
theorem embU_val {k m : ℕ} (r : QRegister k m) (U : Unitary (2 ^ k)) : (r.embedUnitary U).1 =
    r.embedMatrix U.1 := QRegister.embedUnitary_val r U
theorem q_bw {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) : (QRegister.block
    offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem q_sw {m n : ℕ} (r : QRegister m n) (offset width : ℕ) (h : offset + width ≤ m) (i : Fin
    width) : (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem q_cw {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
theorem q_fw {n : ℕ} (i : Fin n) : (QRegExt.ofFin n).wires i = i := rfl
theorem q_iw {n : ℕ} (i : Fin n) : (idReg n).wires i = i := rfl
theorem ax_rw {n : ℕ} (r : QRegister 18 n) (w : Fin 3) (j : Fin 6) : (axisBitRev6 r w).wires j =
    r.wires ⟨6 * w.val + (5 - j.val), by omega⟩ := rfl
theorem q_b {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) : QRegister.block
    offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem q_s {m n : ℕ} (r : QRegister m n) (offset width : ℕ) (h : offset + width ≤ m) (i : Fin
    width) : r.slice offset width h i = r ⟨offset + i.val, by omega⟩ := rfl
theorem q_f {n : ℕ} (i : Fin n) : QRegExt.ofFin n i = i := rfl
theorem r_e {α : Type*} (x : α) : Function.Embedding.refl α x = x := rfl
theorem q_i {n : ℕ} (i : Fin n) : idReg n i = i := rfl
theorem ax_r {n : ℕ} (r : QRegister 18 n) (w : Fin 3) (j : Fin 6) : axisBitRev6 r w j = r ⟨6 *
    w.val + (5 - j.val), by omega⟩ := rfl
theorem bb_p (x : SysIdx) (w : Fin 3) (j : Fin 8) : basisBits 8 (projAxisField x w) j =
    basisBits systemQubits x (proj3Axes w j) :=
  bb_ext (proj3Axes w) x j
theorem bb_e (x : SysIdx) (i : Fin numElectrons) (w : Fin 3) (j : Fin 6) :
    basisBits 6 (elecAxisField x i w) j =
      basisBits systemQubits x (elec654Axes ⟨3 * i.val + w.val, by
        have : numElectrons = 218 := rfl
        omega⟩ j) :=
  bb_ext _ x j
open NuclearTwistRealizes (barrelBitFn twistCorePermFn) in
theorem tw_p (γ : BitAssignment (twCW 80)) (q : Wire (twCW 80)) : twistCorePermFn true h22_80
    γ q = (if q.val < 3924 ∧ q.val % 6 = 5 then barrelBitFn true h22_80 γ q + 1 else barrelBitFn
      true h22_80 γ q) := rfl
open NuclearTwistRealizes (slot2TotalPhaseExp slot4TotalPhaseExp
  twistCorePermFn twistCorePhase)
theorem tw_h (cfg : Configuration) (γ : BitAssignment (twCW 80)) : twistCorePhase true h22_80
    cfg γ = dyadicTurn 48 (slot4TotalPhaseExp h22_80 (twistCorePermFn true h22_80 γ) +
      slot2TotalPhaseExp cfg h22_80 (twistCorePermFn true h22_80 γ)) := rfl
noncomputable def pos80Slot4EShift : ℝ :=
  veeCenteredShift w128DualQ30 pos24CutNyq pos24MinNyq Finset.univ
noncomputable def pos80Slot4EShiftFn : Configuration → ℝ := fun _ ↦ pos80Slot4EShift
noncomputable def s4S : SysOp := veeSingleAnchorRaw w128DualQ30 - (pos80Slot4EShift : ℂ) • 1
noncomputable def s4HR : SysOp := ((1 / 128 : ℝ) : ℂ) • ∑ b₀ : NyqParity3D, ∑ d :
    NyqFine3D128, (kHead128 w128DualQ30 pos24CutNyq d : ℂ) • ∑ i : Fin numElectrons, (saPair
    (vKet b₀) (vKet (ancPar b₀ d)) (fun y₀ ↦ (ancTgt y₀ b₀ d).1) i - 1)
noncomputable def s4TR : SysOp := ((1 / 128 : ℝ) : ℂ) • ∑ b₀ : NyqParity3D, ∑ d :
    NyqFine3D128, (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq d : ℂ) • ∑ i : Fin
    numElectrons, saPair (vKet b₀) (vKet (ancPar b₀ d)) (fun y₀ ↦ (ancTgt y₀ b₀ d).1) i
lemma ih_sm {D : ℕ} (r : ℝ) {A : Operator D} (hA : A.IsHermitian) : ((r : ℂ) • A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal, hA.eq]
lemma ih_su {ι : Type*} {D : ℕ} (s : Finset ι) (f : ι → Operator D) (hf : ∀ i ∈ s,
    (f i).IsHermitian) : (∑ i ∈ s, f i).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i hi ↦ (hf i hi).eq
theorem s4_ih : s4S.IsHermitian :=
  (ih_sm (1 / 128) (ih_su Finset.univ _ fun b₀ _ ↦ ih_su Finset.univ _ fun d _ ↦
    ih_sm (w128DualQ30 d) (ih_su Finset.univ _ fun i _ ↦
      singleAnchorPairOp_isHermitian (vKet b₀) (vKet (ancPar b₀ d))
        (fun y₀ ↦ (ancTgt y₀ b₀ d).1) i))) |>.sub
    (ih_sm pos80Slot4EShift Matrix.isHermitian_one)
theorem s4_cp (g : Equiv.Perm (Fin numElectrons)) : s4S * (permutationUnitary (permElectron g)).1 =
    (permutationUnitary (permElectron g)).1 * s4S := by
  unfold s4S
  rw [Matrix.sub_mul, Matrix.mul_sub, veeSingleAnchorRaw_comm_perm w128DualQ30 g, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
theorem ag_g4 {spinUp : Finset (Fin numElectrons)} {A B : SysOp} {ε : ℝ} (hcomm_perm : ∀ g :
    Equiv.Perm (Fin numElectrons),
    A * (permutationUnitary (permElectron g)).1 = (permutationUnitary (permElectron g)).1 *
      A) (hnorm : ‖A - B‖ ≤ ε) :
    AgreesOnFermionicSector spinUp (gridProjector * A * gridProjector) (gridProjector * B *
      gridProjector) ε := by
  let P := fermionicProjector spinUp
  refine ⟨?_, ?_⟩
  · rw [fermionicProjector_eq_groupAvgProj spinUp]
    refine commutes_groupAvgProj (spinGroupAux spinUp) _ IsGridState permElectron _ ?_
      fun g _ ↦ sandwich_comm_of_comm (gridProjector_comm_permutationUnitary g) (hcomm_perm g)
    rw [← gridProjector_eq_predProjector]
    exact sandwich_mul_idem_comm gridProjector_mul_self
  · have hP1 : ‖P‖ ≤ 1 := norm_projector_le_one P
      (fermionicProjector_isHermitian spinUp) (fermionicProjector_idem spinUp)
    have hcol : P * (gridProjector * A * gridProjector - gridProjector * B * gridProjector) * P =
      P * (A - B) * P := by
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      calc P * (gridProjector * (A - B) * gridProjector) * P
        _ = (P * gridProjector) * (A - B) * (gridProjector * P) := by simp only [m_assoc]
        _ = P * (A - B) * P := by
            rw [fermionicProjector_mul_gridProjector, gridProjector_mul_fermionicProjector]
    rw [hcol]
    refine ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg P))).trans ?_
    simpa only [one_mul, mul_one] using mul_le_mul
      (mul_le_mul hP1 hnorm (norm_nonneg _) zero_le_one) hP1 (norm_nonneg P)
      (by linarith [norm_nonneg (A - B)])
theorem s4_ht : s4S = s4HR + s4TR := by
  have hcardP : Fintype.card NyqParity3D = 8 := by decide
  have hcardE : Fintype.card (Fin numElectrons) = numElectrons := Fintype.card_fin _
  let pairOp (b₀ : NyqParity3D) (d : NyqFine3D128) : SysOp :=
    ∑ i : Fin numElectrons,
      saPair (vKet b₀) (vKet (ancPar b₀ d)) (fun y₀ ↦ (ancTgt y₀ b₀ d).1) i
  let midW (b : NyqParity3D) : ℂ := (((pos24CutNyq b + pos24MinNyq b) / 2 : ℝ) : ℂ)
  let cE : ℂ := (((numElectrons : ℝ) * ((numElectrons : ℝ) - 1) : ℝ) : ℂ)
  have hconst_b₀ (b₀ : NyqParity3D) : (∑ d : NyqFine3D128, midW (nyq3D.symm d).2 • pairOp b₀ d) =
    cE • ((∑ b : NyqParity3D, midW b) • (1 : SysOp)) := by
    rw [← Equiv.sum_comp nyq3D, Fintype.sum_prod_type_right]
    simp_rw [Equiv.symm_apply_apply]
    have hdp (dp : NyqParity3D) : (∑ dy : NyqGrid3D64, midW dp • pairOp b₀ (nyq3D (dy, dp))) =
      midW dp • (cE • (1 : SysOp)) := by
      dsimp only [pairOp, cE]
      rw [← Finset.smul_sum, Finset.sum_comm]
      simp_rw [sum_dy_singleAnchorPairOp_eq_const b₀ dp]
      rw [Finset.sum_const, Finset.card_univ, hcardE, ← Nat.cast_smul_eq_nsmul ℂ]
      simp only [smul_smul]
      refine congrArg (fun z : ℂ ↦ z • (1 : SysOp)) ?_
      push_cast
      ring
    simp_rw [hdp]
    rw [← Finset.sum_smul]
    exact smul_comm _ _ _
  have hmid : (veeMidpointShift pos24CutNyq pos24MinNyq : ℂ) • (1 : SysOp) = ((1 / 128 : ℝ) : ℂ) • ∑
    _b₀ : NyqParity3D, cE • ((∑ b : NyqParity3D, midW b) • (1 : SysOp)) := by
    unfold veeMidpointShift
    rw [Finset.sum_const, Finset.card_univ, hcardP, ← Nat.cast_smul_eq_nsmul ℂ]
    simp only [smul_smul, midW, cE]
    refine congrArg (fun z : ℂ ↦ z • (1 : SysOp)) ?_
    push_cast
    ring
  have hhead_shift : ((((numElectrons : ℝ) / 16) * (∑ d : NyqFine3D128, kHead128 w128DualQ30
    pos24CutNyq d) : ℝ) : ℂ) • (1 : SysOp) =
      ((1 / 128 : ℝ) : ℂ) • ∑ _b₀ : NyqParity3D, ∑ d : NyqFine3D128, (kHead128 w128DualQ30
        pos24CutNyq d : ℂ) • ∑ _i : Fin numElectrons, (1 : SysOp) := by
    simp_rw [Finset.sum_const, Finset.card_univ, hcardE, hcardP,
      ← Nat.cast_smul_eq_nsmul ℂ, ← Finset.sum_smul]
    simp only [smul_smul, ← Complex.ofReal_sum]
    refine congrArg (fun z : ℂ ↦ z • (1 : SysOp)) ?_
    push_cast
    ring
  have hpt (b₀ : NyqParity3D) (d : NyqFine3D128) : (kHead128 w128DualQ30 pos24CutNyq d : ℂ) • pairOp
    b₀ d + (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq d : ℂ) • pairOp b₀ d =
      (w128DualQ30 d : ℂ) • pairOp b₀ d - midW (nyq3D.symm d).2 • pairOp b₀ d := by
    rw [← add_smul, ← sub_smul]
    refine congrArg (fun z : ℂ ↦ z • _) ?_
    have hs := kHead128_add_kTail128 w128DualQ30 pos24CutNyq d
    unfold kTailShifted128
    dsimp only [midW]
    push_cast [← hs]
    ring
  unfold s4S pos80Slot4EShift veeCenteredShift s4HR s4TR
  rw [Complex.ofReal_add, add_smul, ← sub_sub, hmid, hhead_shift]
  have hsplit_mid : veeSingleAnchorRaw w128DualQ30 - ((1 / 128 : ℝ) : ℂ) • ∑ _b₀ : NyqParity3D,
    cE • ((∑ b : NyqParity3D, midW b) • (1 : SysOp)) =
      ((1 / 128 : ℝ) : ℂ) • ∑ b₀ : NyqParity3D, ∑ d : NyqFine3D128, ((kHead128 w128DualQ30
        pos24CutNyq d : ℂ) • pairOp b₀ d +
      (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq d : ℂ) • pairOp b₀ d) := by
    simp_rw [hpt, Finset.sum_sub_distrib, hconst_b₀]
    unfold veeSingleAnchorRaw
    rw [smul_sub]
  rw [sub_right_comm, hsplit_mid, ← smul_sub, ← smul_add, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun b₀ _ ↦ ?_)
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  simp only [pairOp, Finset.sum_sub_distrib, smul_sub]
  abel
def sC18 : Fin (2 ^ 18) ≃ NyqGrid3D64 := u18GridEquiv.trans bitRev6GridEquiv
def sCd (z : SysIdx) (e : Fin 218) : NyqGrid3D64 := sC18 ((rEl_sp e).extractIndex z)
noncomputable def vM18 (b : NyqParity3D) : Operator (2 ^ 18) :=
  Matrix.of fun z u ↦ star (vKet b (sC18 z) u)
private theorem u_cs1 {D : ℕ} (U : Unitary D) : U.1ᴴ * U.1 = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using U.2.1
private theorem u_sc1 {D : ℕ} (U : Unitary D) : U.1 * U.1ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using U.2.2
noncomputable def vB18 (b : NyqParity3D) : Unitary (2 ^ 18) :=
  ⟨vM18 b, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext u v
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, vM18, Matrix.of_apply, star_star,
      Matrix.one_apply]
    rw [← Equiv.sum_comp sC18.symm]
    simp_rw [Equiv.apply_symm_apply]
    exact veeSubGridKet_complete b u v⟩
private theorem m_ced {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (ket : β → α → ℂ) (U : Matrix α α ℂ) (hU : ∀ z u, U z u = star (ket (e z) u)) (y : β) : Uᴴ *
      diagonal (fun z : α ↦ if e z = y then (1 : ℂ) else 0) * U =
    Matrix.of (fun u v ↦ ket y u * star (ket y v)) := by
  ext u v
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.of_apply,
    hU, star_star]
  have hsum (z : α) : (∑ w : α, ket (e w) u * (if w = z then if e w = y then (1 : ℂ) else 0 else 0))
    * star (ket (e z) v) = if z = e.symm y then ket y u * star (ket y v) else 0 := by
    rw [Finset.sum_eq_single z (fun w _ hw ↦ by simp [hw])
      (fun hz ↦ False.elim (hz (Finset.mem_univ z)))]
    simp only [↓reduceIte]
    by_cases hzy : e z = y
    · simp [e.eq_symm_apply.mpr hzy]
    · simp [hzy, show z ≠ e.symm y from fun h ↦ hzy (by rw [h, Equiv.apply_symm_apply])]
  simp_rw [hsum]
  rw [Finset.sum_eq_single (e.symm y) (fun _ _ hz ↦ ite_eq_right hz)
    (fun h ↦ False.elim (h (Finset.mem_univ _))), ite_eq_left rfl]
private theorem vb_cp (b : NyqParity3D) (y : NyqGrid3D64) : (vB18 b).1ᴴ * diagonal (fun z : Fin (2 ^
    18) ↦ if sC18 z = y then (1 : ℂ) else 0) * (vB18 b).1 = rk1_sp (vKet b y) :=
  m_ced sC18 (vKet b) (vB18 b).1 (fun _ _ ↦ rfl) y
noncomputable def vSU (b₁ : NyqParity3D) : Unitary (2 ^ systemQubits) :=
  (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (vB18 b₁)).prod
noncomputable def s4CU (b₀ b₁ : NyqParity3D) (i : Fin 218) : Unitary (2 ^ systemQubits) :=
  vSU b₁ * (rEl_sp 0).embedUnitary (slot4CosetDiag18 b₀ b₁) *
    permutationUnitary (permElectron (Equiv.swap i 0))
private theorem lp_cm {D : ℕ} :
    ∀ (L : List (Unitary D)) (X : Operator D),
      (∀ U ∈ L, U.1 * X = X * U.1) → L.prod.1ᴴ * X * L.prod.1 = X
  | [], _, _ => by simp
  | U :: tail, X, hcomm => by
      calc (U :: tail).prod.1ᴴ * X * (U :: tail).prod.1
        _ = tail.prod.1ᴴ * (U.1ᴴ * (X * U.1)) * tail.prod.1 := by
            rw [List.prod_cons, Submonoid.coe_mul, Matrix.conjTranspose_mul]
            simp only [m_assoc]
        _ = X := by
            rw [← hcomm U List.mem_cons_self, ← m_assoc U.1ᴴ U.1 X, u_cs1 U, Matrix.one_mul]
            exact lp_cm tail X fun V hV ↦ hcomm V (List.mem_cons_of_mem U hV)
private theorem lf_cr (V : Fin 218 → Unitary (2 ^ 18)) (e : Fin 218) (M : Operator (2 ^ 18)) :
    ((List.ofFn fun s : Fin 218 ↦ (rEl_sp s).embedUnitary (V s)).prod).1ᴴ * (rEl_sp e).embedMatrix M
      *
    ((List.ofFn fun s : Fin 218 ↦ (rEl_sp s).embedUnitary (V s)).prod).1 = (rEl_sp e).embedMatrix
      ((V e).1ᴴ * M * (V e).1) := by
  let f := fun s : Fin 218 ↦ (rEl_sp s).embedUnitary (V s)
  have hget : (List.finRange 218)[e.val]'(by simp [e.isLt]) = e := List.getElem_finRange e.isLt
  have hfr : List.finRange 218 = (List.finRange 218).take e.val ++ e :: (List.finRange 218).drop
    (e.val + 1) := by
    conv_lhs => rw [← List.take_append_drop e.val (List.finRange 218)]
    rw [List.drop_eq_getElem_cons (by simp [e.isLt]), hget]
  have hsplit : List.ofFn f = ((List.finRange 218).take e.val).map f ++ f e :: ((List.finRange
    218).drop (e.val + 1)).map f := by
    conv_lhs => rw [List.ofFn_eq_map, hfr]
    rw [List.map_append, List.map_cons]
  have hcomm_ne (s : Fin 218) (hs : s.val ≠ e.val) (Y : Operator (2 ^ 18)) : (f s).1 *
    (rEl_sp e).embedMatrix Y = (rEl_sp e).embedMatrix Y * (f s).1 :=
    QRegister.embedMatrix_comm_of_disjoint (rEl_sp s) (rEl_sp e)
      (rEl_disjoint_of_ne_sp fun h ↦ hs (congrArg Fin.val h)) (V s).1 Y
  set L₁ := ((List.finRange 218).take e.val).map f
  set L₂ := ((List.finRange 218).drop (e.val + 1)).map f
  rw [hsplit, List.prod_append, List.prod_cons, Submonoid.coe_mul, Submonoid.coe_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have hstep₁ : (L₂.prod.1ᴴ * (f e).1ᴴ * L₁.prod.1ᴴ) * (rEl_sp e).embedMatrix M *
      (L₁.prod.1 * ((f e).1 * L₂.prod.1)) =
      L₂.prod.1ᴴ * ((f e).1ᴴ * (L₁.prod.1ᴴ * (rEl_sp e).embedMatrix M * L₁.prod.1) *
        (f e).1) * L₂.prod.1 := by simp only [m_assoc]
  rw [hstep₁, lp_cm L₁ _ (fun U hU ↦ by
    rcases List.mem_map.mp hU with ⟨s, hs, rfl⟩
    rcases List.mem_iff_getElem.mp hs with ⟨n, hn, hsn⟩
    simp only [List.length_take, List.length_finRange, List.getElem_take, List.getElem_finRange]
      at hn hsn
    refine hcomm_ne s (fun h ↦ ?_) M
    have hv := congrArg Fin.val hsn
    dsimp at hv
    omega)]
  have hmid : (f e).1ᴴ * (rEl_sp e).embedMatrix M * (f e).1 = (rEl_sp e).embedMatrix ((V e).1ᴴ * M *
    (V e).1) := by
    simp only [f, embU_val, ← QRegister.embedMatrix_conjTranspose, ← QRegister.embedMatrix_mul]
  rw [hmid]
  exact lp_cm L₂ _ fun U hU ↦ by
    rcases List.mem_map.mp hU with ⟨s, hs, rfl⟩
    rcases List.mem_iff_getElem.mp hs with ⟨n, hn, hsn⟩
    simp only [List.length_drop, List.length_finRange, List.getElem_drop, List.getElem_finRange]
      at hn hsn
    refine hcomm_ne s (fun h ↦ ?_) _
    have hv := congrArg Fin.val hsn
    dsimp at hv
    omega
private theorem eq_of_ag_ext {k m : ℕ} (r : QRegister k m) {a b : Fin (2 ^ m)} (hag : r.AgreeOutside
    a b) (hext : r.extractIndex a = r.extractIndex b) : a = b :=
  (basisBitsEquiv m).injective (funext fun q ↦ by
    change basisBits m a q = basisBits m b q
    by_cases hq : q ∈ Set.range r.wires
    · rcases hq with ⟨j, rfl⟩
      simpa only [bb_ext] using congrFun (congrArg (basisBits k) hext) j
    · exact hag q hq)
private theorem em_dg {k m : ℕ} (r : QRegister k m) (d : Fin (2 ^ k) → ℂ) : r.embedMatrix (diagonal
    d) = diagonal (fun z : Fin (2 ^ m) ↦ d (r.extractIndex z)) := by
  ext z' z
  by_cases hzz : z' = z
  · subst hzz
    rw [diagonal_apply_eq, embedMatrix_entry_of_agreeOutside r _ fun _ _ ↦ rfl,
      diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hzz]
    by_cases hag : r.AgreeOutside z' z
    · rw [embedMatrix_entry_of_agreeOutside r _ hag]
      exact diagonal_apply_ne _ fun hext ↦ hzz (eq_of_ag_ext r hag hext)
    · exact embedMatrix_entry_of_not_agreeOutside r _ hag
private theorem vs_sp (b₁ : NyqParity3D) (e : Fin 218) (y : NyqGrid3D64) : (vSU b₁).1ᴴ *
    diagonal (fun z : SysIdx ↦ if sCd z e = y then (1 : ℂ) else 0) * (vSU b₁).1 = op_sp (vKet b₁ y)
      e := by
  rw [show diagonal (fun z : SysIdx ↦ if sCd z e = y then (1 : ℂ) else 0) =
    (rEl_sp e).embedMatrix (diagonal (fun u : Fin (2 ^ 18) ↦ if sC18 u = y then (1 : ℂ) else 0))
    from (em_dg (rEl_sp e) (fun u ↦ if sC18 u = y then (1 : ℂ) else 0)).symm, vSU, lf_cr, vb_cp]
  rfl
private theorem sc_pp (b₀ b₁ : NyqParity3D) (i s : Fin 218) (hs0 : s ≠ 0) (y₀ y₁ : NyqGrid3D64) :
    (s4CU b₀ b₁ i).1ᴴ * diagonal (fun z : SysIdx ↦ if sCd z 0 = y₀ ∧ sCd z s = y₁ then (1 : ℂ) else
      0) * (s4CU b₀ b₁ i).1 = op_sp (vKet b₀ y₀) i * op_sp (vKet b₁ y₁) ((Equiv.swap i 0) s) := by
  let D0s := diagonal (fun z ↦ if sCd z 0 = y₀ then (1 : ℂ) else 0) *
      diagonal (fun z ↦ if sCd z s = y₁ then (1 : ℂ) else 0)
  have hdiag_prod : diagonal (fun z : SysIdx ↦ if sCd z 0 = y₀ ∧ sCd z s = y₁ then (1 : ℂ) else 0) =
    D0s := by
    dsimp only [D0s]
    rw [diagonal_mul_diagonal]
    refine congrArg diagonal (funext fun z ↦ ?_)
    by_cases h0 : sCd z 0 = y₀
    · simp [h0]
    · simp [h0]
  let Uv := vSU b₁
  let Uc := (rEl_sp 0).embedUnitary (slot4CosetDiag18 b₀ b₁)
  let Up := permutationUnitary (permElectron (Equiv.swap i 0))
  have hUv_prod : Uv.1ᴴ * D0s * Uv.1 = op_sp (vKet b₁ y₀) 0 * op_sp (vKet b₁ y₁) s := by
    dsimp only [D0s]
    rw [← vs_sp b₁ 0 y₀, ← vs_sp b₁ s y₁]
    simp only [m_assoc]
    rw [← m_assoc Uv.1 Uv.1ᴴ, u_sc1 Uv, Matrix.one_mul]
  have hcomm_s : op_sp (vKet b₁ y₁) s * Uc.1 = Uc.1 * op_sp (vKet b₁ y₁) s :=
    QRegister.embedMatrix_comm_of_disjoint (rEl_sp s) (rEl_sp 0)
      (rEl_disjoint_of_ne_sp fun h ↦ hs0 (Fin.ext (congrArg Fin.val h))) _ _
  have h0_conj : Uc.1ᴴ * op_sp (vKet b₁ y₀) 0 * Uc.1 = op_sp (vKet b₀ y₀) 0 := by
    simp only [Uc, op_sp, embU_val, ← QRegister.embedMatrix_conjTranspose,
      ← QRegister.embedMatrix_mul]
    exact congrArg (rEl_sp 0).embedMatrix
      (slot4_barrelSwap_and_coset_conj b₀ b₁ y₀ (vKet b₀) (vKet b₁) id 0).1
  have h0_sw : op_sp (vKet b₀ y₀) 0 * Up.1 = Up.1 * op_sp (vKet b₀ y₀) i := by
    simpa only [op_sp, Equiv.swap_apply_right] using
      emb_rEl_mul_pe_sp (Equiv.swap i 0) 0 (rk1_sp (vKet b₀ y₀))
  have hs_sw : op_sp (vKet b₁ y₁) s * Up.1 = Up.1 * op_sp (vKet b₁ y₁) ((Equiv.swap i 0) s) :=
    emb_rEl_mul_pe_sp (Equiv.swap i 0) s (rk1_sp (vKet b₁ y₁))
  change (Uv * Uc * Up).1ᴴ * _ * (Uv * Uc * Up).1 = _
  rw [hdiag_prod, Submonoid.coe_mul, Submonoid.coe_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul]
  calc Up.1ᴴ * (Uc.1ᴴ * Uv.1ᴴ) * D0s * (Uv.1 * Uc.1 * Up.1)
    _ = Up.1ᴴ * (Uc.1ᴴ * (Uv.1ᴴ * D0s * Uv.1) * Uc.1) * Up.1 := by simp only [m_assoc]
    _ = Up.1ᴴ * (Uc.1ᴴ * op_sp (vKet b₁ y₀) 0 *
          (op_sp (vKet b₁ y₁) s * Uc.1)) * Up.1 := by
        rw [hUv_prod]
        simp only [m_assoc]
    _ = Up.1ᴴ * op_sp (vKet b₀ y₀) 0 * (op_sp (vKet b₁ y₁) s * Up.1) := by
        rw [hcomm_s, ← m_assoc _ Uc.1, h0_conj]
        simp only [m_assoc]
    _ = _ := by
        rw [hs_sw, ← m_assoc _ Up.1, m_assoc Up.1ᴴ _ Up.1, h0_sw, ← m_assoc Up.1ᴴ Up.1, u_cs1 Up,
          Matrix.one_mul]
def s4H0 (b₀ : NyqParity3D) (d : NyqFine3D128) (z : SysIdx) : Finset (Fin 218) :=
  (Finset.univ.erase 0).filter fun s ↦ sCd z s = (ancTgt (sCd z 0) b₀ d).1
private theorem sc_hc (b₀ : NyqParity3D) (d : NyqFine3D128) (i : Fin 218) :
    let b₁ := ancPar b₀ d
    (s4CU b₀ b₁ i).1ᴴ * diagonal (fun z : SysIdx ↦ ((s4H0 b₀ d z).card : ℂ)) *
      (s4CU b₀ b₁ i).1 = saPair (vKet b₀) (vKet b₁) (fun y₀ ↦ (ancTgt y₀ b₀ d).1) i := by
  intro b₁
  have hdiag_sum : diagonal (fun z : SysIdx ↦ ((s4H0 b₀ d z).card : ℂ)) = ∑ y₀ : NyqGrid3D64,
    ∑ s ∈ Finset.univ.erase (0 : Fin 218),
      diagonal (fun z : SysIdx ↦ if sCd z 0 = y₀ ∧ sCd z s = (ancTgt y₀ b₀ d).1 then (1 : ℂ) else
        0) := by
    ext z' z
    by_cases hzz : z' = z
    · subst hzz
      simp only [diagonal_apply_eq, Matrix.sum_apply]
      rw [Finset.sum_eq_single (sCd z' 0)
        (fun y₀ _ hy₀ ↦ Finset.sum_eq_zero fun s _ ↦ by simp [hy₀.symm]) (by simp)]
      simp only [true_and, s4H0, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
        apply_ite (Nat.cast : ℕ → ℂ), Nat.cast_one, Nat.cast_zero]
    · simp only [diagonal_apply_ne _ hzz, Matrix.sum_apply, Finset.sum_const_zero]
  rw [hdiag_sum, Matrix.mul_sum, Finset.sum_mul]
  unfold saPair nSub_sp
  refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
  rw [Matrix.mul_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_congr rfl fun s hs ↦
    sc_pp b₀ b₁ i s (Finset.mem_erase.mp hs).1 y₀ (ancTgt y₀ b₀ d).1]
  exact Finset.sum_bij (fun s _ ↦ (Equiv.swap i 0) s)
    (fun s hs ↦ Finset.mem_erase.mpr
      ⟨fun h ↦ (Finset.mem_erase.mp hs).1
        ((Equiv.swap i 0).injective (h.trans (Equiv.swap_apply_right i 0).symm)),
       Finset.mem_univ _⟩)
    (fun _ _ _ _ h ↦ (Equiv.swap i 0).injective h)
    (fun j hj ↦ ⟨(Equiv.swap i 0) j, Finset.mem_erase.mpr
      ⟨fun h ↦ (Finset.mem_erase.mp hj).1
        (by rw [← Equiv.swap_apply_self i 0 j, h, Equiv.swap_apply_right]),
       Finset.mem_univ _⟩, Equiv.swap_apply_self i 0 j⟩)
    fun _ _ ↦ rfl
theorem sc_di (b₀ : NyqParity3D) (d : NyqFine3D128) (i : Fin 218) :
    let b₁ := ancPar b₀ d
    (s4CU b₀ b₁ i).1 * saPair (vKet b₀) (vKet b₁) (fun y₀ ↦ (ancTgt y₀ b₀ d).1) i =
      diagonal (fun z : SysIdx ↦ ((s4H0 b₀ d z).card : ℂ)) * (s4CU b₀ b₁ i).1 := by
  intro b₁
  have hconj := sc_hc b₀ d i
  dsimp only [b₁] at hconj ⊢
  rw [← hconj, ← m_assoc, ← m_assoc, u_sc1 (s4CU b₀ b₁ i), Matrix.one_mul]
theorem it_t {α : Sort*} {c : Prop} [Decidable c] (h : c) (t e : α) : (if c then t else e) = t := by
  cases ‹Decidable c› with
  | isTrue _ => rfl
  | isFalse hnc => exact False.elim (hnc h)
theorem it_f {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (t e : α) : (if c then t else e) = e :=
  by
  cases ‹Decidable c› with
  | isTrue hc => exact False.elim (h hc)
  | isFalse _ => rfl
theorem dt_t {α : Sort*} {c : Prop} [Decidable c] (h : c) (t : c → α) (e : ¬ c → α) : (dite c t e) =
    t h := by
  cases ‹Decidable c› with
  | isTrue _ => rfl
  | isFalse hnc => exact False.elim (hnc h)
theorem dt_f {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (t : c → α) (e : ¬ c → α) : (dite c t
    e) = e h := by
  cases ‹Decidable c› with
  | isTrue hc => exact False.elim (h hc)
  | isFalse _ => rfl
theorem mu_pv {a b : ℕ} (U₁ : Unitary (2 ^ a)) (U₂ : Unitary (2 ^ b)) (hab : a =
    b) : (mulUnitaryPow2 U₁ U₂ hab).1 = U₁.1 * (@castUnitaryPow2 b a hab.symm U₂).1 := rfl
theorem u_mv {N : ℕ} (U V : Unitary N) : (U * V).1 = U.1 * V.1 := rfl
theorem u_m3 {N : ℕ} (U V W : Unitary N) : (U * V * W).1 = U.1 * V.1 * W.1 := rfl
theorem ds_ve {k : ℕ} (f : BitAssignment k → Bool) : (diagonalSignUnitaryN f).1 = diagonal (fun
    idx : Fin (2 ^ k) ↦ if f (basisBits k idx) then (-1 : ℂ) else 1) := rfl
theorem u_nl {α : Type*} {N : ℕ} (f : α → Unitary N) : (([] : List α).map f).prod.1 = 1 := by
  simp only [List.map_nil, List.prod_nil, OneMemClass.coe_one]
theorem u_cs {α : Type*} {N : ℕ} (f : α → Unitary N) (a : α) (t : List α) : ((a :: t).map
    f).prod.1 = (f a).1 * (t.map f).prod.1 := by
  simp only [List.map_cons, List.prod_cons, Submonoid.coe_mul]
theorem u_cm {α : Type*} {N : ℕ} (f : α → Unitary N) (L : List α) (P : Operator N) (h : ∀ x ∈ L,
    (f x).1 * P = P * (f x).1) : (L.map f).prod.1 * P = P * (L.map f).prod.1 := by
  induction L with
  | nil => rw [u_nl, Matrix.one_mul, Matrix.mul_one]
  | cons a t ih =>
    rw [u_cs, m_assoc, ih (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)),
      ← m_assoc, h a List.mem_cons_self, m_assoc]
theorem u_fn {n N : ℕ} (f : Fin n → Unitary N) : (List.ofFn f).prod.1 = ((List.finRange n).map
    f).prod.1 :=
  congrArg (fun L : List (Unitary N) ↦ L.prod.1) (List.ofFn_eq_map (f := f))
theorem u_fcm {n N : ℕ} (f : Fin n → Unitary N) (P : Operator N) (h : ∀ i : Fin n, (f i).1 * P = P *
    (f i).1) : (List.ofFn f).prod.1 * P = P * (List.ofFn f).prod.1 := by
  rw [u_fn]
  exact u_cm f (List.finRange n) P fun i _ ↦ h i
theorem u_fh {n M N : ℕ} (Φ : Operator M → Operator N) (h1 : Φ 1 = 1) (f : Fin n → Unitary M) (g :
    Fin n → Unitary N) (hstep : ∀ (i : Fin n) (tail : List (Fin n)), Φ ((f i).1 *
    (tail.map f).prod.1) = (g i).1 * Φ (tail.map f).prod.1) : Φ (List.ofFn f).prod.1 =
      (List.ofFn g).prod.1 := by
  rw [u_fn, u_fn]
  suffices hL : ∀ L : List (Fin n), Φ (L.map f).prod.1 = (L.map g).prod.1 from hL (List.finRange n)
  intro L
  induction L with
  | nil => rw [u_nl, u_nl, h1]
  | cons i tail ih => rw [u_cs, u_cs, hstep i tail, ih]
theorem u_fma {n N : ℕ} (f g fg : Fin n → Unitary N) (hfg : ∀ i : Fin n, (f i).1 * (g i).1 =
    (fg i).1) (hcomm : ∀ i j : Fin n, i ≠ j → (f i).1
    * (g j).1 = (g j).1 * (f i).1) : (List.ofFn f).prod * (List.ofFn g).prod =
      (List.ofFn fg).prod := by
  apply Subtype.ext
  rw [u_mv, u_fn, u_fn, u_fn]
  suffices hL : ∀ L : List (Fin n), L.Nodup →
      (L.map f).prod.1 * (L.map g).prod.1 = (L.map fg).prod.1 from
    hL (List.finRange n) (List.nodup_finRange n)
  intro L hnd
  induction L with
  | nil => rw [u_nl, u_nl, u_nl, Matrix.one_mul]
  | cons i tail ih =>
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨hnotmem, hnd_t⟩
    rw [u_cs, u_cs, u_cs]
    have hc : (tail.map f).prod.1 * (g i).1 = (g i).1 * (tail.map f).prod.1 := u_cm f tail
        (g i).1 fun j hj ↦ hcomm j i (fun hji ↦ hnotmem (hji ▸ hj))
    calc ((f i).1 * (tail.map f).prod.1) * ((g i).1 * (tail.map g).prod.1)
      _ = (f i).1 * (((tail.map f).prod.1 * (g i).1) * (tail.map g).prod.1) := by
          simp only [m_assoc]
      _ = ((f i).1 * (g i).1) * ((tail.map f).prod.1 * (tail.map g).prod.1) := by
          rw [hc]; simp only [m_assoc]
      _ = (fg i).1 * (tail.map fg).prod.1 := by
          rw [hfg i, ih hnd_t]
theorem u_fd {n N : ℕ} (f : Fin n → Unitary N) (d : Fin n → Fin N → ℂ) (hd : ∀ i : Fin n, (f i).1 =
    diagonal (d i)) : (List.ofFn f).prod.1 = diagonal (fun z : Fin N ↦ ∏ i : Fin n, d i z) := by
  rw [u_fn]
  have hL : ∀ L : List (Fin n), (L.map f).prod.1 = diagonal (fun z : Fin N ↦ (L.map fun i ↦
    d i z).prod) := by
    intro L
    induction L with
    | nil =>
      rw [u_nl]
      simp only [List.map_nil, List.prod_nil, Matrix.diagonal_one]
    | cons i tail ih =>
      rw [u_cs, hd i, ih, diagonal_mul_diagonal]
      exact congrArg diagonal (funext fun z ↦ by simp only [List.map_cons, List.prod_cons])
  rw [hL (List.finRange n)]
  exact congrArg diagonal (funext fun z ↦ (Fin.prod_univ_def (fun i ↦ d i z)).symm)
theorem m_fp {N : ℕ} (M : Operator N) (σ : Equiv.Perm (Fin N)) (z u : Fin N) : (M * (fwdPU σ).1) z
    u = M z (σ u) := by
  rw [Matrix.mul_apply]
  simp_rw [fwdPermUnitary_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (σ u)
    (fun w _ hw ↦ it_f hw.symm _ _)
    (fun h ↦ False.elim (h (Finset.mem_univ _))), it_t rfl]
theorem fp_mm {N : ℕ} (σ : Equiv.Perm (Fin N)) (M : Operator N) (z u : Fin N) : ((fwdPU σ).1 *
    M) z u = M (σ.symm z) u := by
  rw [Matrix.mul_apply]
  simp_rw [fwdPermUnitary_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm z)
    (fun w _ hw ↦ it_f (fun heq ↦ hw (σ.eq_symm_apply.mpr heq)) _ _)
    (fun h ↦ False.elim (h (Finset.mem_univ _))), it_t (σ.apply_symm_apply z)]
theorem fp_cm {N : ℕ} (σ τ : Equiv.Perm (Fin N)) (h : ∀ x, σ (τ x) = τ (σ x)) : (fwdPU σ).1 *
    (fwdPU τ).1 = (fwdPU τ).1 * (fwdPU σ).1 := by
  ext y x
  rw[m_fp, m_fp, fwdPermUnitary_apply, fwdPermUnitary_apply, h x]
theorem m_pc {N : ℕ} (A P : Operator N) (row col : Fin N) (hdiag : P col col = 1) (hoff : ∀ j,
    j ≠ col → P j col = 0) : (A * P) row col = A row col := by
  rw [Matrix.mul_apply, Finset.sum_eq_single col
    (fun j _ hj ↦ by rw [hoff j hj, mul_zero])
    (fun h ↦ False.elim (h (Finset.mem_univ col))), hdiag, mul_one]
theorem m_mir {N : ℕ} (E B : Operator N) (row col mid : Fin N) (hE : ∀ w, E row w = if w =
    mid then 1 else 0) : (E * B) row col = B mid col := by
  rw [Matrix.mul_apply]
  simp_rw [hE, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single mid (fun w _ hw ↦ it_f hw _ _)
    (fun h ↦ False.elim (h (Finset.mem_univ _))), it_t rfl]
theorem mv_s1 {N : ℕ} (M : Operator N) (col row : Fin N) : M.mulVec (Pi.single col (1 : ℂ)) row =
    M row col := by
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
theorem ss_eq {N : ℕ} (c : ℂ) (col : Fin N) : (c • Pi.single col (1 : ℂ)) col = c := by
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
theorem ss_ne {N : ℕ} (c : ℂ) {col row : Fin N} (h : row ≠ col) : (c • Pi.single col (1 : ℂ)) row =
    0 := by
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne h, mul_zero]
theorem bk_sg {n : ℕ} (idx : Fin (2 ^ n)) : basisKet (basisBits n idx) = Pi.single idx (1 : ℂ) := by
  change basisState ((basisBitsEquiv n).symm (basisBitsEquiv n idx)) = Pi.single idx (1 : ℂ)
  rw [(basisBitsEquiv n).symm_apply_apply]
theorem ud_cd {D : ℕ} (u d : Fin D → ℂ) (hu : ∀ z, star (u z) * u z = 1) : (diagonal u)ᴴ *
    diagonal d * diagonal u = diagonal d := by
  rw [Matrix.diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  refine congrArg diagonal (funext fun z ↦ ?_)
  calc star (u z) * d z * u z = d z * (star (u z) * u z) := by ring
    _ = d z := by rw [hu z, mul_one]
theorem sb_cp {k₁ k₂ : ℕ} (hk₁ : posCoreWires = k₁) (hk₂ : posCoreWires = k₂) (h12 : k₁ = k₂)
    (U : Unitary (2 ^ k₁)) (s0 : Bool) (p80 : Pay80) : sysBlk hk₂ (castUnitaryPow2 h12 U).1 s0 p80 =
      sysBlk hk₁ U.1 s0 p80 := by
  subst h12
  have hh : hk₂ = hk₁ := Subsingleton.elim _ _
  rw [hh]
  rfl
theorem mul3_comm_of_comm {N : ℕ} (A B C P : Operator N) (hA : A * P = P * A) (hB : B * P = P *
    B) (hC : C * P = P * C) : (A * B * C) * P = P * (A * B * C) := by
  calc (A * B * C) * P
    _ = A * B * (C * P) := by simp only [m_assoc]
    _ = A * (B * P) * C := by rw [hC]; simp only [m_assoc]
    _ = (A * P) * B * C := by rw [hB]; simp only [m_assoc]
    _ = P * (A * B * C) := by rw [hA]; simp only [m_assoc]
theorem bs_af {N : ℕ} (Sm Sm654 P_proj B U_qft U_tw U_off C_diag P_sw D_kar V_sys U_cl D_fn :
    Operator N) (hSm_l : Sm = P_projᴴ * Sm654ᴴ) (hSm_r : Sm = Sm654 * P_proj) (hB_fac : B = (U_qft *
      U_tw)ᴴ * D_fn * (U_qft * U_tw))
    (hTw_sm : U_tw * Sm654 = U_off * C_diag * P_sw) (hQft_off : U_qft * U_off = D_kar *
      V_sys) (hCl_def : U_cl = V_sys * C_diag * P_sw) (hKar : D_karᴴ * D_fn * D_kar = D_fn)
    (hCl_comm : U_cl * P_proj = P_proj * U_cl) (hDiag_proj : P_projᴴ * D_fn * P_proj = D_fn) : Sm *
      B * Sm = U_clᴴ * D_fn * U_cl := by
  have hFwd : U_qft * U_tw * Sm654 = D_kar * U_cl := by
    calc U_qft * U_tw * Sm654
      _ = U_qft * (U_tw * Sm654) := by rw [m_assoc]
      _ = (U_qft * U_off) * C_diag * P_sw := by rw [hTw_sm]; simp only [m_assoc]
      _ = D_kar * U_cl := by rw [hQft_off, hCl_def]; simp only [m_assoc]
  have h654 : Sm654ᴴ * B * Sm654 = U_clᴴ * D_fn * U_cl := by
    have hct : Sm654ᴴ * (U_qft * U_tw)ᴴ = (U_qft * U_tw * Sm654)ᴴ :=
      (Matrix.conjTranspose_mul (U_qft * U_tw) Sm654).symm
    calc Sm654ᴴ * B * Sm654
      _ = (Sm654ᴴ * (U_qft * U_tw)ᴴ) * D_fn * (U_qft * U_tw * Sm654) := by
          rw [hB_fac]; simp only [m_assoc]
      _ = (U_qft * U_tw * Sm654)ᴴ * D_fn * (U_qft * U_tw * Sm654) := by
          rw [hct]
      _ = U_clᴴ * (D_karᴴ * D_fn * D_kar) * U_cl := by
          rw [hFwd, Matrix.conjTranspose_mul]; simp only [m_assoc]
      _ = U_clᴴ * D_fn * U_cl := by rw [hKar]
  have hCl_comm_inv : P_projᴴ * U_clᴴ = U_clᴴ * P_projᴴ := by
    have hc := congrArg Matrix.conjTranspose hCl_comm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at hc
    exact hc
  have hSm_both : Sm * B * Sm = (P_projᴴ * Sm654ᴴ) * B * (Sm654 * P_proj) :=
    congrArg₂ (· * ·) (congrArg₂ (· * ·) hSm_l rfl) hSm_r
  calc Sm * B * Sm
    _ = P_projᴴ * (Sm654ᴴ * B * Sm654) * P_proj := by
        rw [hSm_both]; simp only [m_assoc]
    _ = (P_projᴴ * U_clᴴ) * D_fn * (U_cl * P_proj) := by
        rw [h654]; simp only [m_assoc]
    _ = U_clᴴ * (P_projᴴ * D_fn * P_proj) * U_cl := by
        rw [hCl_comm_inv, hCl_comm]; simp only [m_assoc]
    _ = U_clᴴ * D_fn * U_cl := by rw [hDiag_proj]
private theorem em_fp {n k m : ℕ} (r : Fin n → QRegister k m) (hr : ∀ i j : Fin n, i ≠ j →
    (r i).DisjointWires (r j))
    (U : Unitary (2 ^ k)) (τ : Equiv.Perm (Fin (2 ^ k))) (hU : U = fwdPU τ) (σ : Equiv.Perm (Fin (2
      ^ m))) (hex : ∀ (u : Fin (2 ^ m)) (i : Fin n),
    (r i).extractIndex (σ u) = τ ((r i).extractIndex u)) (hkeep : ∀ (u : Fin (2 ^ m)) (q : Wire m),
      (∀ i : Fin n, q ∉ Set.range (r i).wires) → basisBits m (σ u) q = basisBits m u q) :
    (List.ofFn fun i : Fin n ↦ (r i).embedUnitary U).prod = fwdPU σ := by
  subst hU
  let f : Fin n → Unitary (2 ^ m) := fun i ↦ (r i).embedUnitary (fwdPU τ)
  have hdisj {e' e : Fin n} (hne : e' ≠ e) (j : Fin k) : r e' j ∉ Set.range (r e).wires :=
    fun ⟨j₂, hj₂⟩ ↦ (QRegister.disjoint_iff.mp (hr e' e hne)) j j₂ hj₂.symm
  have hext_eq {e' : Fin n} {a b : Fin (2 ^ m)} (hb : ∀ j : Fin k, basisBits m a (r e' j) =
    basisBits m b (r e' j)) : (r e').extractIndex a = (r e').extractIndex b :=
    (basisBitsEquiv k).injective (funext fun j ↦ by
      change basisBits k _ j = basisBits k _ j
      rw [bb_ext, bb_ext, hb j])
  have hmat (L : List (Fin n)) (hnd : L.Nodup) (z u : Fin (2 ^ m)) : (L.map f).prod.1 z u =
    if (∀ i ∈ L, (r i).extractIndex z = τ ((r i).extractIndex u)) ∧
      (∀ q : Wire m, (∀ i ∈ L, q ∉ Set.range (r i).wires) → basisBits m z q = basisBits m u q) then
        1 else 0 := by
    induction L generalizing z with
    | nil =>
      rw [u_nl]
      change (1 : Operator (2 ^ m)) z u = _
      rw [Matrix.one_apply]
      by_cases hzu : z = u
      · subst hzu
        simp
      · have hne : ¬ (∀ q, basisBits m z q = basisBits m u q) :=
          fun hall ↦ hzu ((basisBitsEquiv m).injective (funext hall))
        simp [hzu, hne]
    | cons e tail ih =>
      rcases List.nodup_cons.mp hnd with ⟨hnotmem, hnd_t⟩
      rw [u_cs f]
      let zMid : Fin (2 ^ m) := (r e).replaceIndex z (τ.symm ((r e).extractIndex z))
      have hag_zM : (r e).AgreeOutside z zMid := fun q hq ↦
        (QRegister.basisBits_replaceIndex_of_not_mem _ _ _ q hq).symm
      have hex_zM : (r e).extractIndex zMid = τ.symm ((r e).extractIndex z) :=
        QRegister.extractIndex_replaceIndex _ _ _
      have hentry_e (w : Fin (2 ^ m)) : (f e).1 z w = if w = zMid then 1 else 0 := by
        rw [embU_val]
        by_cases hag : (r e).AgreeOutside z w
        · rw [embedMatrix_entry_of_agreeOutside (r e) _ hag, fwdPermUnitary_apply]
          refine if_congr ⟨fun heq ↦ eq_of_ag_ext (r e)
            (fun q hq ↦ (hag q hq).symm.trans (hag_zM q hq))
            ((τ.eq_symm_apply.mpr heq).trans hex_zM.symm), fun h ↦ ?_⟩ rfl rfl
          rw [h, hex_zM, Equiv.apply_symm_apply]
        · rw [embedMatrix_entry_of_not_agreeOutside (r e) _ hag]
          exact (ite_eq_right fun h : w = zMid ↦ hag (h ▸ hag_zM)).symm
      rw [m_mir _ _ z u zMid hentry_e, ih hnd_t zMid]
      have hex_ne (e' : Fin n) (he' : e' ∈ tail) : (r e').extractIndex zMid = (r e').extractIndex
        z :=
        hext_eq fun j ↦ QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _
          (hdisj (fun h : e' = e ↦ hnotmem (h ▸ he')) j)
      refine if_congr ⟨fun ⟨ht_ext, ht_out⟩ ↦ ⟨fun e' he' ↦ ?_, fun q hq ↦ ?_⟩,
        fun ⟨hc_ext, hc_out⟩ ↦ ⟨fun e' he' ↦ ?_, fun q hq ↦ ?_⟩⟩ rfl rfl
      · rcases List.mem_cons.mp he' with rfl | htail
        · have he_u : (r e').extractIndex zMid = (r e').extractIndex u :=
            hext_eq fun j ↦ ht_out (r e' j) fun i hi ↦
              hdisj (fun h : e' = i ↦ hnotmem (h.symm ▸ hi)) j
          rw [hex_zM] at he_u
          exact τ.symm.injective (by rwa [Equiv.symm_apply_apply])
        · exact (hex_ne e' htail).symm.trans (ht_ext e' htail)
      · rw [← QRegister.basisBits_replaceIndex_of_not_mem _ _ _ q (hq e List.mem_cons_self)]
        exact ht_out q fun e' he' ↦ hq e' (List.mem_cons_of_mem _ he')
      · exact (hex_ne e' he').trans (hc_ext e' (List.mem_cons_of_mem _ he'))
      · by_cases hqe : q ∈ Set.range (r e).wires
        · rcases hqe with ⟨j, rfl⟩
          simpa only [bb_ext] using congrFun (congrArg (basisBits k)
            (hex_zM.trans (τ.symm_apply_eq.mpr (hc_ext e List.mem_cons_self)))) j
        · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ q hqe]
          exact hc_out q fun e' he' ↦
            (List.mem_cons.mp he').elim (fun h ↦ h ▸ hqe) (hq e')
  apply Subtype.ext
  ext z u
  rw [u_fn f, hmat (List.finRange n) (List.nodup_finRange n) z u, fwdPermUnitary_apply]
  refine if_congr ⟨fun ⟨hext_all, hout_all⟩ ↦ ?_, fun h ↦ ?_⟩ rfl rfl
  · apply (basisBitsEquiv m).injective
    funext q
    change basisBits m (σ u) q = basisBits m z q
    by_cases hq_any : ∃ i : Fin n, q ∈ Set.range (r i).wires
    · rcases hq_any with ⟨i, j, rfl⟩
      simpa only [bb_ext] using congrFun (congrArg (basisBits k)
        ((hex u i).trans (hext_all i (List.mem_finRange i)).symm)) j
    · have hq_none : ∀ i : Fin n, q ∉ Set.range (r i).wires := fun i hi ↦ hq_any ⟨i, hi⟩
      rw [hkeep u q hq_none, hout_all q fun i _ ↦ hq_none i]
  · subst h
    exact ⟨fun i _ ↦ hex u i, fun q hq ↦ hkeep u q fun i ↦ hq i (List.mem_finRange i)⟩
abbrev hkF : posCoreWires = fullSysCoreWires 80 := pos24_coreWires80_eq.symm
abbrev hkT : posCoreWires = twCW 80 := hkF.trans pos24_core80_eq_twist80
theorem fw_c (q : Wire (fullSysCoreWires 80)) : q.val < posCoreWires := by
  rw [hkF]
  exact q.isLt
theorem ci_b {kC : ℕ} (hk : posCoreWires = kC) (s0 : Bool) (p80 : Pay80) (z : SysIdx) (q : Wire
    kC) : basisBits kC (coreIdxOf hk s0 p80 z) q = cBeta s0 p80 z ⟨q.val, hk.symm ▸ q.isLt⟩ := by
  subst hk
  dsimp only [coreIdxOf]
  exact congrFun ((basisBitsEquiv posCoreWires).apply_symm_apply (cBeta s0 p80 z)) q
theorem bb_pe (g : Equiv.Perm (Fin numElectrons)) (x : SysIdx) (q : Wire systemQubits) :
    basisBits systemQubits (permElectron g x) q = basisBits systemQubits x (permElectronWire g q) :=
      basisBits_permElectron (permElectronWire g) x q
theorem ci_f (s0 : Bool) (p80 : Pay80) (z : SysIdx) (q : Wire (fullSysCoreWires 80)) : basisBits
    (fullSysCoreWires 80) (coreIdxOf hkF s0 p80 z) q = cBeta s0 p80 z ⟨q.val, fw_c q⟩ := by
  have hgen : ∀ {kC : ℕ} (hk : posCoreWires = kC) (q' : Wire kC), basisBits kC (coreIdxOf hk s0 p80
    z) q' = cBeta s0 p80 z ⟨q'.val, hk.symm ▸ q'.isLt⟩ := by
    intro kC hk q'
    subst hk
    dsimp only [coreIdxOf]
    exact congrFun ((basisBitsEquiv posCoreWires).apply_symm_apply (cBeta s0 p80 z)) q'
  exact hgen hkF q
theorem ra_c (s0 : Bool) (p80 : Pay80) (z₁ z₂ : SysIdx) : rAncFlag80.extractIndex (coreIdxOf hkF s0
    p80 z₁) = rAncFlag80.extractIndex (coreIdxOf hkF s0 p80 z₂) := by
  apply (basisBitsEquiv 86).injective
  funext j
  change basisBits 86 _ j = basisBits 86 _ j
  rw[bb_ext, bb_ext, ci_f, ci_f]
  by_cases hj : j.val < 6
  · have hlo : systemQubits ≤ (rAncFlag80 j).val := by
      dsimp [rAncFlag80, q_b, q_bw, systemQubits, numElectrons, electronBits, projectileBits]
      omega
    have hhi : (rAncFlag80 j).val < 3954 := by
      dsimp [rAncFlag80, q_b, q_bw, systemQubits, numElectrons, electronBits, projectileBits]
      omega
    let wj : Wire posCoreWires := ⟨(rAncFlag80 j).val, fw_c (rAncFlag80 j)⟩
    rw [coreBetaOf_mid s0 p80 z₁ wj hlo hhi, coreBetaOf_mid s0 p80 z₂ wj hlo hhi]
  · have hw : (⟨(rAncFlag80 j).val, fw_c (rAncFlag80 j)⟩ : Wire posCoreWires) =
        rPosSubLocal ⟨j.val - 6, by have := j.isLt; dsimp [posPayloadWires]; omega⟩ := by
      apply Fin.ext
      dsimp [rAncFlag80, rPosSubLocal, rSubPayloadCore, QRegister.compose_apply, q_cw, q_s, q_sw,
        q_f, q_fw, q_b, q_bw, systemQubits, numElectrons,
        electronBits, projectileBits, posCoreWires, posPayloadWires, r_e,
          Function.Embedding.refl_apply, Function.Embedding.coeFn_mk]
      omega
    rw [hw, cB_pay, cB_pay]
private theorem bb_ge3948_eq {a b : Fin (2 ^ fullSysCoreWires 80)} (hext : rAncFlag80.extractIndex
    a = rAncFlag80.extractIndex b)
    (q : Wire (fullSysCoreWires 80)) (hq : ¬ q.val < systemQubits) : basisBits (fullSysCoreWires
      80) a q = basisBits (fullSysCoreWires 80) b q := by
  have ⟨hql, hge⟩ : q.val < 4034 ∧ 3948 ≤ q.val := ⟨q.isLt, Nat.le_of_not_lt hq⟩
  have hqAnc : q = rAncFlag80 ⟨q.val - 3948, by omega⟩ := Fin.ext (by
    change q.val = 3948 + (q.val - 3948)
    omega)
  rw [hqAnc, ← bb_ext rAncFlag80 a, ← bb_ext rAncFlag80 b, hext]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pr_a (M : Operator (2 ^ fullSysCoreWires 80)) (hcomm : ∀ a : Fin (2 ^ 86),
    M * rAncFlag80.basisOutcomeProjector a = rAncFlag80.basisOutcomeProjector a * M) (s0 : Bool)
      (p80 : Pay80) : PreservesCoreAnc hkF M s0 p80 := by
  intro x row hnz
  have hext : rAncFlag80.extractIndex row = rAncFlag80.extractIndex (coreIdxOf hkF s0 p80 x) := by
    by_contra hne
    exact hnz (entry_zero_of_comm_basisOutcomeProjector rAncFlag80 M hcomm row _ hne)
  let rSys : QRegister systemQubits (fullSysCoreWires 80) :=
    QRegister.block 0 systemQubits (by decide)
  refine ⟨rSys.extractIndex row,
    (basisBitsEquiv (fullSysCoreWires 80)).injective (funext fun q ↦ ?_)⟩
  change basisBits (fullSysCoreWires 80) row q =
    basisBits (fullSysCoreWires 80) (coreIdxOf hkF s0 p80 (rSys.extractIndex row)) q
  by_cases hq : q.val < systemQubits
  · rw [ci_f, show (⟨q.val, fw_c q⟩ : Wire posCoreWires) =
      ⟨(⟨q.val, hq⟩ : Fin systemQubits).val, Nat.lt_trans hq lt_sys_4034⟩ from rfl,
      coreBetaOf_lt3948 s0 p80 _ ⟨q.val, hq⟩, bb_ext]
    exact congrArg (basisBits _ row) (Fin.ext (Nat.zero_add q.val).symm)
  · exact bb_ge3948_eq (hext.trans (ra_c s0 p80 x _)) q hq
theorem qf_an (qft : FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft) (a : Fin (2 ^ 86)) :
    (fQftU h6_80 qft).1 * rAncFlag80.basisOutcomeProjector a =
    rAncFlag80.basisOutcomeProjector a * (fQftU h6_80 qft).1 := by
  obtain ⟨o3, o83, hfac⟩ := rAncFlag80_basisOutcomeProjector_factor a
  have h3 : (fQftU h6_80 qft).1 * (coreCosetB1Block h6_80).basisOutcomeProjector o3 =
    (coreCosetB1Block h6_80).basisOutcomeProjector o3 * (fQftU h6_80 qft).1 := by
    rw [← coreElecCosetB1_compose_rCoset3, basisOutcomeProjector_compose_local, fQftU, embU_val,
      ← QRegister.embedMatrix_mul, hQft o3, QRegister.embedMatrix_mul]
  have h83 : (fQftU h6_80 qft).1 * rAncRest83.basisOutcomeProjector o83 =
    rAncRest83.basisOutcomeProjector o83 * (fQftU h6_80 qft).1 := by
    rw [fQftU, embU_val]
    exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (cElB1 h6_80)
      rAncRest83 coreElecCosetB1_disjoint_rAncRest83 qft.uQft654.1 o83
  rw [hfac, ← m_assoc, h3, m_assoc, h83, ← m_assoc]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem sb_c8 (qft : FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft)
    (cfg : Configuration) (s0 : Bool) (p80 : Pay80) :
    let U_qft := (fQftU h6_80 qft).1
    let U_tw := (@castUnitaryPow2 (twCW 80) (fullSysCoreWires 80) pos24_core80_eq_twist80.symm
      (uTwistParam true h22_80 cfg)).1
    let D_pos := (castUnitaryPow2 hkF (uPosPhase true tSgn tMag30)).1
    sysBlk hkF (pos24ConjCore80 qft cfg).1 s0 p80 =
      (sysBlk hkF U_qft s0 p80 * sysBlk hkF U_tw s0 p80)ᴴ *
        sysBlk hkF D_pos s0 p80 * (sysBlk hkF U_qft s0 p80 * sysBlk hkF U_tw s0 p80) := by
  intro U_qft U_tw D_pos
  have hTw : ∀ a, U_tw * rAncFlag80.basisOutcomeProjector a = rAncFlag80.basisOutcomeProjector a *
    U_tw :=
    uTwistParam_cast_comm_highReg_proj pos24_core80_eq_twist80.symm cfg rAncFlag80
      rAncFlag80_wire_ge_3948
  have hOut : ∀ a, (U_qft * U_tw) * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (U_qft * U_tw) := fun a ↦ by
    rw [m_assoc, hTw a, ← m_assoc, qf_an qft hQft a, m_assoc]
  have hDOut : ∀ a, (D_pos * (U_qft * U_tw)) * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (D_pos * (U_qft * U_tw)) := fun a ↦ by
    rw [m_assoc, hOut a, ← m_assoc, QRegister.basisOutcomeProjector_eq_diagonal,
      uPosPhase_cast_comm_diagonal hkF true tSgn tMag30 _, m_assoc]
  have hmul_out : (@mulUnitaryPow2 (fullSysCoreWires 80) (twCW 80) (fQftU h6_80 qft)
      (uTwistParam true h22_80 cfg) pos24_core80_eq_twist80).1 = U_qft * U_tw := mu_pv _ _ _
  unfold pos24ConjCore80
  rw [PosMomSelectDynamic.unitaryConj_val, hmul_out, sysBlockAtPayloadGen_conj_of_preserves hkF
    (U_qft * U_tw) D_pos s0 p80
    (pr_a _ hOut s0 p80) (pr_a _ hDOut s0 p80), sysBlockAtPayloadGen_mul_of_preserves hkF U_qft U_tw
      s0 p80 (pr_a _ hTw s0 p80)]
theorem sb_ds (f : BitAssignment posCoreWires → Bool) {kC : ℕ} (hk : posCoreWires = kC) (s0 : Bool)
    (p80 : Pay80) : sysBlk hk (castUnitaryPow2 hk (diagonalSignUnitaryN f)).1 s0
    p80 = diagonal (fun z : SysIdx ↦ if f (cBeta s0 p80 z) then (-1 : ℂ) else 1) := by
  subst hk
  have hc : (castUnitaryPow2 rfl (diagonalSignUnitaryN f)).1 = diagonal (fun idx : Fin (2 ^
      posCoreWires) ↦ if f (basisBits posCoreWires idx) then (-1 : ℂ) else 1) := ds_ve f
  rw [hc]
  ext x' x
  rw [sysBlockAtPayloadGen_apply]
  by_cases hxx : x' = x
  · subst hxx
    rw [diagonal_apply_eq, diagonal_apply_eq]
    have hidx : basisBits posCoreWires (coreIdxOf rfl s0 p80 x') = cBeta s0 p80 x' :=
      funext (basisBits_symm_apply_fun (cBeta s0 p80 x'))
    rw [hidx]
  · have hne : coreIdxOf rfl s0 p80 x' ≠ coreIdxOf rfl s0 p80 x :=
      fun h ↦ hxx (coreIdxOf_injective rfl s0 p80 h)
    rw [diagonal_apply_ne _ hne, diagonal_apply_ne _ hxx]
theorem sb_pp (s0 : Bool) (p80 : Pay80) : sysBlk hkF (castUnitaryPow2 hkF (uPosPhase true tSgn
    tMag30)).1 s0 p80 = diagonal (fun z : SysIdx ↦
    if posPhaseBit true tSgn tMag30 (cBeta s0 p80 z) then (-1 : ℂ) else 1) := sb_ds
    (posPhaseBit true tSgn tMag30) hkF s0 p80
def pB1 (p80 : Pay80) : NyqParity3D :=
  fun w ↦ ⟨(p80 ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩).val, ZMod.val_lt _⟩
def pB0 (p80 : Pay80) : NyqParity3D :=
  fun w ↦ ⟨(p80 (pos80SubIdx 3 3 (by decide) w)).val, ZMod.val_lt _⟩
theorem ex_cb (s0 : Bool) (p80 : Pay80) (z : SysIdx) : (coreCosetB1Block h6_80).extractIndex
    (coreIdxOf hkF s0 p80 z) = nyqParity3DEquivFin8 (pB1 p80) := by
  apply (basisBitsEquiv 3).injective
  funext w
  change basisBits 3 _ w = basisBits 3 _ w
  rw [bb_ext, ci_f]
  have hw : (⟨(coreCosetB1Block h6_80 w).val, fw_c (coreCosetB1Block h6_80 w)⟩ : Wire posCoreWires)
    = rPosSubLocal ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩ := by
    ext
    dsimp [coreCosetB1Block, rPosSubLocal, rSubPayloadCore, QRegister.compose_apply, q_cw, q_s,
      q_sw,
      q_f, q_fw, q_b, q_bw, systemQubits, numElectrons,
      electronBits, projectileBits, posCoreWires, posPayloadWires, r_e,
        Function.Embedding.refl_apply, Function.Embedding.coeFn_mk]
  rw [hw, cB_pay]
  dsimp only [nyqParity3DEquivFin8, Equiv.coe_fn_mk, pB1]
  have hsym := congrFun ((basisBitsEquiv 3).apply_symm_apply
    (fun w' : Fin 3 ↦ (((p80 ⟨w'.val, Nat.lt_trans w'.isLt (by decide)⟩).val : ℕ) : ZMod 2))) w
  change basisBits 3 ((basisBitsEquiv 3).symm _) w = _ at hsym
  rw [hsym, ZMod.natCast_zmod_val]
private theorem ce_wv (e : Fin 218) (j : Fin 18) : (((cElB1 h6_80).compose (rElec18In654 e))
    j).val = 18 * e.val + j.val := by
  have hj : 18 * e.val + j.val < 3924 := by
    have := e.isLt
    have := j.isLt
    omega
  change ((cElB1 h6_80).wires (rElec18In654 e j)).val = _
  rw [show rElec18In654 e j = Fin.castAdd 3 ⟨18 * e.val + j.val, hj⟩ from Fin.ext rfl]
  change (((coreElecBlock 80).wires ⊕ᵥ (coreCosetB1Block h6_80).wires)
    (finSumFinEquiv.symm (Fin.castAdd 3 ⟨18 * e.val + j.val, hj⟩))).val = _
  rw [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  dsimp [coreElecBlock, q_b, q_bw]
  omega
private theorem sb_er (e : Fin 218) (M : Operator (2 ^ 18)) (s0 : Bool) (p80 : Pay80) : sysBlk hkF
    (((cElB1 h6_80).compose (rElec18In654 e)).embedMatrix M) s0 p80 = (rEl_sp e).embedMatrix M := by
  let rC := (cElB1 h6_80).compose (rElec18In654 e)
  have hwire (j : Fin 18) : (rC j).val = (rEl_sp e j).val := ce_wv e j
  have hextract (z : SysIdx) : rC.extractIndex (coreIdxOf hkF s0 p80 z) = (rEl_sp e).extractIndex
    z := by
    apply (basisBitsEquiv 18).injective
    funext j
    change basisBits 18 _ j = basisBits 18 _ j
    rw [bb_ext, bb_ext, ci_f, show (⟨(rC j).val, fw_c (rC j)⟩ : Wire posCoreWires) =
      ⟨(rEl_sp e j).val, Nat.lt_trans (rEl_sp e j).isLt lt_sys_4034⟩ from Fin.ext (hwire j),
        coreBetaOf_lt3948 s0 p80 z (rEl_sp e j)]
  ext x' x
  rw [sysBlockAtPayloadGen_apply]
  have hag_iff : rC.AgreeOutside (coreIdxOf hkF s0 p80 x') (coreIdxOf hkF s0 p80 x) ↔
    (rEl_sp e).AgreeOutside x' x := by
    refine ⟨fun hag q hq ↦ ?_, fun hag qC hqC ↦ ?_⟩
    · let qC : Wire (fullSysCoreWires 80) := ⟨q.val, lt_trans q.isLt (by decide)⟩
      have hb := hag qC fun ⟨j, hjC⟩ ↦
        hq ⟨j, Fin.ext ((hwire j).symm.trans (congrArg Fin.val hjC))⟩
      rw [ci_f, ci_f] at hb
      exact (coreBetaOf_lt3948 s0 p80 x' q).symm.trans
        (hb.trans (coreBetaOf_lt3948 s0 p80 x q))
    · by_cases hlt : qC.val < systemQubits
      · let qS : Wire systemQubits := ⟨qC.val, hlt⟩
        rw [ci_f, ci_f]
        exact (coreBetaOf_lt3948 s0 p80 x' qS).trans
          ((hag qS fun ⟨j, hjS⟩ ↦
            hqC ⟨j, Fin.ext ((hwire j).trans (congrArg Fin.val hjS))⟩).trans
            (coreBetaOf_lt3948 s0 p80 x qS).symm)
      · exact bb_ge3948_eq (ra_c s0 p80 x' x) qC hlt
  by_cases hag : (rEl_sp e).AgreeOutside x' x
  · rw [embedMatrix_entry_of_agreeOutside rC M (hag_iff.mpr hag),
      embedMatrix_entry_of_agreeOutside (rEl_sp e) M hag, hextract, hextract]
  · rw [embedMatrix_entry_of_not_agreeOutside rC M (mt hag_iff.mp hag),
      embedMatrix_entry_of_not_agreeOutside (rEl_sp e) M hag]
private theorem re_dj (e' : Fin 218) : (((cElB1 h6_80).compose (rElec18In654 e'))).DisjointWires
    rAncFlag80 :=
  QRegister.disjoint_iff.mpr fun j₁ j₂ h ↦ by
    have hv := congrArg Fin.val h
    rw [ce_wv] at hv
    have := e'.isLt
    have := j₁.isLt
    have := rAncFlag80_wire_ge_3948 j₂
    omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
private theorem sb_lr (V : Fin 218 → Unitary (2 ^ 18)) (s0 : Bool) (p80 : Pay80) : sysBlk hkF
    ((List.ofFn fun e : Fin 218 ↦ ((cElB1 h6_80).compose (rElec18In654 e)).embedUnitary (V
      e)).prod).1
    s0 p80 = ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (V e)).prod).1 := by
  refine u_fh (fun A ↦ sysBlk hkF A s0 p80) ?_
    (fun e : Fin 218 ↦ ((cElB1 h6_80).compose (rElec18In654 e)).embedUnitary (V e))
    (fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (V e)) fun e tail ↦ ?_
  · ext x' x
    rw [sysBlockAtPayloadGen_apply, Matrix.one_apply, Matrix.one_apply]
    exact if_congr ⟨fun h ↦ coreIdxOf_injective hkF s0 p80 h, fun h ↦ h ▸ rfl⟩ rfl rfl
  · have hcomm_tail (a : Fin (2 ^ 86)) :
        (tail.map fun e' : Fin 218 ↦ ((cElB1 h6_80).compose (rElec18In654 e')).embedUnitary
          (V e')).prod.1 * rAncFlag80.basisOutcomeProjector a =
          rAncFlag80.basisOutcomeProjector a *
            (tail.map fun e' : Fin 218 ↦ ((cElB1 h6_80).compose (rElec18In654 e')).embedUnitary
              (V e')).prod.1 :=
      u_cm _ tail _ fun e' _ ↦
        QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ rAncFlag80 (re_dj e')
          (V e').1 a
    rw [sysBlockAtPayloadGen_mul_of_preserves hkF _ _ s0 p80 (pr_a _ hcomm_tail s0 p80), embU_val,
      sb_er e (V e).1 s0 p80, embU_val]
theorem sb_qf (qft : FullSysQft654Bundle) (hqft : qft.uQft654 = qft64Ideal654Unitary)
    (s0 : Bool) (p80 : Pay80) :
    let b₁ := pB1 p80
    sysBlk hkF (fQftU h6_80 qft).1 s0 p80 =
      ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (qft64OffsetUnitary3D b₁)).prod).1 := by
  intro b₁
  have hSlice_gen (M_prod : Operator (2 ^ fullSysCoreWires 80)) (hprod_eq : (cElB1
    h6_80).embedMatrix (List.ofFn fun e : Fin 218 ↦
      (rElec18In654 e).embedUnitary (qft64OffsetUnitary3D b₁)).prod.1 = M_prod) : sysBlk hkF (fQftU
        h6_80 qft).1 s0 p80 = sysBlk hkF M_prod s0 p80 := by
    ext x' x
    rw [sysBlockAtPayloadGen_apply, sysBlockAtPayloadGen_apply]
    let col := coreIdxOf hkF s0 p80 x
    let row := coreIdxOf hkF s0 p80 x'
    let P3 := (coreCosetB1Block h6_80).basisOutcomeProjector (nyqParity3DEquivFin8 b₁)
    have hP3_diag : P3 col col = 1 := by
      dsimp only [P3]
      rw [QRegister.basisOutcomeProjector_eq_diagonal, diagonal_apply_eq, ex_cb]
      exact it_t (rfl : nyqParity3DEquivFin8 (pB1 p80) = nyqParity3DEquivFin8 b₁) 1 0
    have hP3_off : ∀ j, j ≠ col → P3 j col = 0 := fun j hj ↦ by
      dsimp only [P3]
      rw [QRegister.basisOutcomeProjector_eq_diagonal]
      exact diagonal_apply_ne _ hj
    have hP3_comp : P3 = (cElB1 h6_80).embedMatrix (rCoset3In654.basisOutcomeProjector
      (nyqParity3DEquivFin8 b₁)) := by
      dsimp only [P3]
      rw [← coreElecCosetB1_compose_rCoset3]
      exact basisOutcomeProjector_compose_local _ _ _
    have hQft_val : (fQftU h6_80 qft).1 = (cElB1 h6_80).embedMatrix qft64Ideal654Unitary.1 := by
      dsimp only [fQftU]
      rw [hqft, embU_val]
    have hmat_eq : (fQftU h6_80 qft).1 * P3 = M_prod * P3 :=
      (congrArg₂ (· * ·) hQft_val hP3_comp).trans (((QRegister.embedMatrix_mul _ _ _).symm).trans
        ((congrArg (cElB1 h6_80).embedMatrix
          (qft64Ideal654Unitary_mul_cosetProj_eq_elec3DProd b₁)).trans
          ((QRegister.embedMatrix_mul _ _ _).trans (congrArg₂ (· * ·) hprod_eq hP3_comp.symm))))
    exact ((m_pc _ P3 row col hP3_diag hP3_off).symm).trans
      ((congrFun (congrFun hmat_eq row) col).trans (m_pc M_prod P3 row col hP3_diag hP3_off))
  exact (hSlice_gen _ (u_fh (cElB1 h6_80).embedMatrix (QRegister.embedMatrix_one _)
    (fun e : Fin 218 ↦ (rElec18In654 e).embedUnitary (qft64OffsetUnitary3D b₁))
    (fun e : Fin 218 ↦ ((cElB1 h6_80).compose (rElec18In654 e)).embedUnitary
      (qft64OffsetUnitary3D b₁))
    fun _ _ ↦ by
      rw [QRegister.embedMatrix_mul, embU_val, embU_val, QRegister.embedMatrix_compose])).trans
    (sb_lr _ s0 p80)
def o18P : Equiv.Perm (Fin (2 ^ 18)) := u18AxisSplitEquiv.trans
  ((Equiv.arrowCongr (Equiv.refl (Fin 3)) signedMagToOffset6Equiv).trans u18GridEquiv.symm)
def o18U : Unitary (2 ^ 18) := fwdPU o18P
noncomputable def oSU : Unitary (2 ^ systemQubits) :=
  (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary o18U).prod
private theorem u18_o (u : Fin (2 ^ 18)) : u18GridEquiv (o18P u) = eOff18 u :=
  u18GridEquiv.apply_symm_apply _
theorem qf_o1 (b₁ : NyqParity3D) : (qft64OffsetUnitary3D b₁ * o18U).1 = diagonal (fun z : Fin (2 ^
    18) ↦ karatsubaOutPhase3D (sC18 z)) * (vB18 b₁).1 := by
  rw [u_mv, show (vB18 b₁).1 = vM18 b₁ from rfl, show o18U = fwdPU o18P from rfl]
  ext z u
  rw [m_fp, Matrix.diagonal_mul, qft64OffsetUnitary3D_apply, u18_o]
  have hk : (∏ w : Fin 3, karatsubaOffsetUnitary128 (b₁ w) (u18GridEquiv z w) (eOff18 u w)) =
    karatsubaOutPhase3D (bitRev6GridEquiv (u18GridEquiv z)) *
      subGridUnitary64 b₁ (bitRev6GridEquiv (u18GridEquiv z)) (eOff18 u) :=
    karatsubaOffset3D128_apply b₁ (u18GridEquiv z) (eOff18 u)
  rw [hk]
  unfold vM18 vKet sC18
  simp only [Matrix.of_apply, Equiv.trans_apply, star_star]
theorem lf_pm (F G : Fin 218 → Unitary (2 ^ 18)) : (List.ofFn fun e : Fin 218 ↦
    (rEl_sp e).embedUnitary (F e)).prod *
    (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (G e)).prod = (List.ofFn fun e : Fin 218 ↦
      (rEl_sp e).embedUnitary (F e * G e)).prod :=
  u_fma (fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (F e))
    (fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (G e))
    (fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (F e * G e))
    (fun _ ↦ by rw [embU_val, embU_val, embU_val, ← QRegister.embedMatrix_mul, u_mv])
    (fun i j hij ↦ QRegister.embedMatrix_comm_of_disjoint (rEl_sp i) (rEl_sp j)
      (rEl_disjoint_of_ne_sp (fun h : (⟨i.val, i.isLt⟩ : Fin numElectrons) = ⟨j.val, j.isLt⟩ ↦
        hij (Fin.ext (congrArg Fin.val h)))) _ _)
noncomputable def oP18 : Unitary (2 ^ 18) :=
  ⟨diagonal (fun z : Fin (2 ^ 18) ↦ karatsubaOutPhase3D (sC18 z)), by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg diagonal (funext fun z ↦ karatsubaOutPhase3D_unit (sC18 z))⟩
theorem lf_op : ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary oP18).prod).1 = diagonal (fun
    z : SysIdx ↦ ∏ e : Fin 218, karatsubaOutPhase3D (sCd z e)) :=
  u_fd (fun e : Fin 218 ↦ (rEl_sp e).embedUnitary oP18)
    (fun e z ↦ karatsubaOutPhase3D (sCd z e)) fun e ↦ em_dg (rEl_sp e) _
def xor32BitsPerm : Equiv.Perm (BitAssignment systemQubits) where
  toFun f q := if q.val < 3924 ∧ q.val % 6 = 5 then f q + 1 else f q
  invFun f q := if q.val < 3924 ∧ q.val % 6 = 5 then f q + 1 else f q
  left_inv f := by
    funext q; dsimp only
    by_cases h : q.val < 3924 ∧ q.val % 6 = 5
    · rw [it_t h, it_t h, add_assoc]; exact add_zero (f q)
    · rw [it_f h, it_f h]
  right_inv f := by
    funext q; dsimp only
    by_cases h : q.val < 3924 ∧ q.val % 6 = 5
    · rw [it_t h, it_t h, add_assoc]; exact add_zero (f q)
    · rw [it_f h, it_f h]
noncomputable def x32P : Equiv.Perm (SysIdx) :=
  (basisBitsEquiv systemQubits).trans (xor32BitsPerm.trans (basisBitsEquiv systemQubits).symm)
theorem bb_x3 (x : SysIdx) (q : Wire systemQubits) : basisBits systemQubits (x32P x) q =
    if q.val < 3924 ∧ q.val % 6 = 5 then basisBits systemQubits x q + 1 else basisBits systemQubits
      x q := by
  have hPoly : ∀ {n : ℕ} (e : Equiv.Perm (BitAssignment n)) (c : Fin (2 ^ n)), basisBits n
    (((basisBitsEquiv n).trans (e.trans (basisBitsEquiv n).symm)) c) = e (basisBits n c) := by
    intro n e c
    change (basisBitsEquiv n) ((basisBitsEquiv n).symm (e (basisBits n c))) = _
    exact (basisBitsEquiv n).apply_symm_apply _
  exact congrFun (hPoly xor32BitsPerm x) q
private theorem ea_u (x : SysIdx) (e : Fin 218) (w : Fin 3) : elecAxisField x e w =
    u18AxisSplitEquiv ((rEl_sp e).extractIndex x) w := by
  apply Fin.ext
  dsimp [elecAxisField, elec654Axes, u18AxisSplitEquiv, rEl_sp]
  rw [extractIndex_block_val, extractIndex_block_val,
    show 6 * (3 * e.val + w.val) = 18 * e.val + 6 * w.val by omega,
    pow_add, ← Nat.div_div_eq_div_mul]
  set A := x.val / 2 ^ (18 * e.val)
  fin_cases w
  · dsimp
    omega
  · dsimp
    omega
  · dsimp
    omega
private theorem bv6_v (v : Fin 64) : v.val = bitsVal (basisBits 6 v) := by
  revert v
  decide
private theorem ea_xp (x : SysIdx) (e : Fin 218) (w : Fin 3) : (elecAxisField (x32P x) e w).val =
    (elecAxisField x e w).val ^^^ 32 := by
  let u := elecAxisField x e w
  let u' := elecAxisField (x32P x) e w
  let m : Fin 654 := ⟨3 * e.val + w.val, by
    have := e.isLt
    have := w.isLt
    omega⟩
  have hbit (j : Fin 6) : basisBits 6 u' j = if j.val = 5 then basisBits 6 u j + 1 else basisBits 6
    u j := by
    change basisBits 6 ((elec654Axes m).extractIndex (x32P x)) j = _
    rw [bb_ext, bb_x3, ← bb_ext (elec654Axes m) x j]
    refine if_congr ?_ rfl rfl
    have := m.isLt
    have := j.isLt
    dsimp [elec654Axes, q_b, q_bw]
    omega
  have hx6 : ∀ v : Fin 64, bitsVal (fun j : Fin 6 ↦ if j.val = 5 then basisBits 6 v j +
    1 else basisBits 6 v j) = v.val ^^^ 32 := by
    decide
  exact (bv6_v u').trans ((congrArg bitsVal (funext hbit)).trans (hx6 u))
private theorem ea_x6 (z : SysIdx) (e : Fin 218) (w : Fin 3) : elecAxisField (x32P (pSm654 z)) e w =
    signedMagToOffset6Equiv (elecAxisField z e w) := by
  have hsm (v : Fin 64) : (smToTwosAxisPerm 3 v).val ^^^ 32 = (signedMagToOffset6Equiv v).val := by
    rw [smToTwosAxisPerm_val 3 v]
    revert v
    decide
  exact Fin.ext (by rw [ea_xp, elecAxisField_smToTwos654, hsm])
private theorem ex_x6 (z : SysIdx) (e : Fin 218) : (rEl_sp e).extractIndex (x32P (pSm654 z)) =
    o18P ((rEl_sp e).extractIndex z) :=
  u18GridEquiv.injective (by
    rw [u18_o]
    exact funext fun w ↦ by
      change u18AxisSplitEquiv _ w = _
      rw [← ea_u, ea_x6, ea_u]
      rfl)
private theorem sysWire_cases (q : Wire systemQubits) :
    (∃ (e : Fin numElectrons) (w : Fin 3) (j : Fin 6),
      q = elec654Axes ⟨3 * e.val + w.val, by
        have : numElectrons = 218 := rfl
        have := e.isLt
        have := w.isLt
        omega⟩ j) ∨
    (∃ (w : Fin 3) (j : Fin 8), q = proj3Axes w j) := by
  by_cases hq : q.val < 3924
  · refine Or.inl ⟨⟨q.val / 18, div_18_lt_numElectrons hq⟩, ⟨(q.val % 18) / 6, by omega⟩,
      ⟨q.val % 6, by omega⟩, Fin.ext ?_⟩
    dsimp [elec654Axes, q_b, q_bw]
    omega
  · have hlt : q.val < 3948 := q.isLt
    refine Or.inr ⟨⟨(q.val - 3924) / 8, by omega⟩, ⟨(q.val - 3924) % 8, by omega⟩, Fin.ext ?_⟩
    dsimp [proj3Axes, q_b, q_bw]
    omega
private theorem fs_ef {a b : SysIdx} (helec : ∀ i w, elecAxisField a i w = elecAxisField b i w)
    (hproj : ∀ w, projAxisField a w = projAxisField b w) : a = b := by
  apply (basisBitsEquiv systemQubits).injective
  funext q
  change basisBits systemQubits a q = basisBits systemQubits b q
  rcases sysWire_cases q with ⟨i, w, j, rfl⟩ | ⟨w, j, rfl⟩
  · simpa only [bb_e] using congrFun (congrArg (basisBits 6) (helec i w)) j
  · simpa only [bb_p] using congrFun (congrArg (basisBits 8) (hproj w)) j
theorem sm_p3 : smToTwosSysUnitary.1 = smToTwos654SysUnitary.1 * (fwdPU pSmP3).1 := by
  have hperm (x : SysIdx) : smToTwosSysPerm x = pSm654 (pSmP3 x) :=
    fs_ef (fun i w ↦ by
      rw [elecAxisField_smToTwosSys, elecAxisField_smToTwos654, elecAxisField_smToTwosProj3])
      fun w ↦ by
        rw [projAxisField_smToTwosSys, projAxisField_smToTwos654, projAxisField_smToTwosProj3]
  rw [show smToTwosSysUnitary = fwdPU smToTwosSysPerm from rfl, show smToTwos654SysUnitary =
    fwdPU pSm654 from rfl]
  ext y x
  rw [m_fp, fwdPermUnitary_apply, fwdPermUnitary_apply, hperm x]
theorem pu_fp {N : ℕ} (σ : Equiv.Perm (Fin N)) : permutationUnitary σ = fwdPU σ := by
  apply Subtype.ext
  ext i j
  have hmv := congrFun (permutationUnitary_mulVec_single σ j (1 : ℂ)) i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hmv
  rw [hmv, fwdPermUnitary_apply]
  exact if_congr eq_comm rfl rfl
abbrev rEl218 (e : Fin 218) : QRegister 18 systemQubits := rEl_sp e
theorem os_fp : oSU = fwdPU (pSm654.trans x32P) := by
  have hoff : oSU = (List.ofFn fun e : Fin 218 ↦ (rEl218 e).embedUnitary o18U).prod :=
      congrArg List.prod (congrArg List.ofFn (funext fun e ↦ congrArg (fun r : QRegister 18
      systemQubits ↦ r.embedUnitary o18U) rfl))
  rw [hoff]
  refine em_fp rEl218
    (fun i j hij ↦ by
      have hne : (⟨i.val, by have : numElectrons = 218 := rfl; exact i.isLt⟩ : Fin numElectrons) ≠
          ⟨j.val, by have : numElectrons = 218 := rfl; exact j.isLt⟩ :=
        fun h ↦ hij (Fin.ext (congrArg Fin.val h))
      exact rEl_disjoint_of_ne_sp hne)
    o18U o18P rfl (pSm654.trans x32P)
    (fun u e ↦ by
      rw [Equiv.trans_apply]
      exact ex_x6 u e)
    (fun u q hq ↦ ?_)
  have hge : 3924 ≤ q.val := by
    by_contra hlt
    have hlt : q.val < 3924 := Nat.lt_of_not_ge hlt
    let e : Fin 218 := ⟨q.val / 18, div_18_lt_numElectrons hlt⟩
    let k : Fin 18 := ⟨q.val % 18, Nat.mod_lt _ (by decide)⟩
    exact hq e ⟨k, Fin.ext (by dsimp [rEl218, rEl_sp, q_b, q_bw, e, k]; omega)⟩
  rw [Equiv.trans_apply, bb_x3, it_f (by omega)]
  have hq_lt : q.val < 3948 := by
    have := q.isLt
    dsimp [systemQubits, numElectrons, electronBits, projectileBits] at this; exact this
  let w : Fin 3 := ⟨(q.val - 3924) / 8, by omega⟩
  let j : Fin 8 := ⟨(q.val - 3924) % 8, by omega⟩
  have hq_eq : q = proj3Axes w j := by ext; dsimp [proj3Axes, q_b, q_bw, w, j]; omega
  have hp := congrFun (congrArg (basisBits 8) (projAxisField_smToTwos654 u w)) j
  rwa [bb_p, bb_p, ← hq_eq] at hp
theorem ea_pe (g : Equiv.Perm (Fin numElectrons)) (x : SysIdx) (e : Fin numElectrons) (w : Fin 3) :
    elecAxisField (permElectron g x) e w = elecAxisField x (g e) w := by
  have hext : (rEl_sp e).extractIndex (permElectron g x) = (rEl_sp (g e)).extractIndex x := by
    apply (basisBitsEquiv 18).injective
    funext b
    change basisBits 18 _ b = basisBits 18 _ b
    rw[bb_ext, bb_ext, bb_pe g x (rEl_sp e b)]
    refine congrArg (basisBits systemQubits x) ?_
    apply Fin.ext
    change (permElectronWireFun g (rEl_sp e b)).val = 18 * (g e).val + b.val
    unfold permElectronWireFun
    have hlt : (rEl_sp e b).val < 3924 := by
      have := e.isLt; have := b.isLt; dsimp [rEl_sp, q_b, q_bw, numElectrons] at *; omega
    simp only [hlt, ↓reduceDIte]
    have hdiv : (⟨(rEl_sp e b).val / 18, div_18_lt_numElectrons hlt⟩ : Fin numElectrons) = e := by
      ext; have := b.isLt; dsimp [rEl_sp, q_b, q_bw]; omega
    have hmod : (rEl_sp e b).val % 18 = b.val := by
      have := b.isLt; dsimp [rEl_sp, q_b, q_bw]; omega
    rw [hdiv, hmod]
  rw [ea_u, ea_u, hext]
private theorem pa_pe (g : Equiv.Perm (Fin numElectrons)) (x : SysIdx) (w : Fin 3) : projAxisField
    (permElectron g x) w = projAxisField x w := by
  apply (basisBitsEquiv 8).injective
  funext j
  change basisBits 8 _ j = basisBits 8 _ j
  rw [bb_p, bb_p, bb_pe g x (proj3Axes w j)]
  refine congrArg (basisBits systemQubits x) (Fin.ext ?_)
  change (permElectronWireFun g (proj3Axes w j)).val = (proj3Axes w j).val
  unfold permElectronWireFun
  have hge : ¬(proj3Axes w j).val < 3924 := by
    dsimp [proj3Axes, q_b, q_bw]
    omega
  simp only [hge, ↓reduceDIte]
theorem pe_65 (g : Equiv.Perm (Fin numElectrons)) (z : SysIdx) : permElectron g (pSm654 z) =
    pSm654 (permElectron g z) :=
  fs_ef (fun e w ↦ by rw [ea_pe, elecAxisField_smToTwos654, elecAxisField_smToTwos654, ea_pe])
    fun w ↦ by rw [pa_pe, projAxisField_smToTwos654, projAxisField_smToTwos654, pa_pe]
theorem pe_p3 (g : Equiv.Perm (Fin numElectrons)) (z : SysIdx) : permElectron g (pSmP3 z) =
    pSmP3 (permElectron g z) :=
  fs_ef
    (fun e w ↦ by rw [ea_pe, elecAxisField_smToTwosProj3, elecAxisField_smToTwosProj3, ea_pe])
    fun w ↦ by rw [pa_pe, projAxisField_smToTwosProj3, projAxisField_smToTwosProj3, pa_pe]
private theorem em_cd (b₀ b₁ : NyqParity3D) : ((rEl_sp 0).embedUnitary (slot4CosetDiag18 b₀ b₁)).1 =
    diagonal (fun z : SysIdx ↦ ∏ w : Fin 3, dyadicTurn 48 ((2 ^ 41 : ℤ) * ((((b₁ w).val : ℤ) -
      ((b₀ w).val : ℤ)) * ((eOff18 ((rEl_sp 0).extractIndex z) w).val : ℤ)))) := by
  rw [embU_val]
  exact em_dg (rEl_sp 0) _
theorem bv_b6 (v : Fin 64) : bitsVal (basisBits 6 v) = v.val := (bv6_v v).symm
theorem dt_s3 (m : Fin 3 → ℤ) : dyadicTurn 48 (∑ w : Fin 3, (2 ^ 41 : ℤ) * m w) = ∏ w : Fin 3,
    dyadicTurn 48 ((2 ^ 41 : ℤ) * m w) := by
  rw [Fin.sum_univ_three, Fin.prod_univ_three, ← Int.mul_add, ← Int.mul_add]
  simp only [dyadicTurn48_shift41_eq_omega128, omega128_add]
theorem rt_c (s0 : Bool) (p80 : Pay80) (z₁ z₂ : SysIdx) {q : Wire (twCW 80)} (hq : 3948 ≤ q.val) :
    basisBits _ (coreIdxOf hkT s0 p80 z₁) q = basisBits _ (coreIdxOf hkT s0 p80 z₂) q := by
  rw [ci_b hkT, ci_b hkT]
  have hlt : q.val < posCoreWires := hkT.symm ▸ q.isLt
  let wq : Wire posCoreWires := ⟨q.val, hlt⟩
  by_cases hmid : q.val < 3954
  · exact (coreBetaOf_mid s0 p80 z₁ wq hq hmid).trans (coreBetaOf_mid s0 p80 z₂ wq hq hmid).symm
  · have hsub : q.val - 3954 < 80 := by dsimp [posCoreWires] at hlt; omega
    have hw : wq = rPosSubLocal ⟨q.val - 3954, hsub⟩ := by
      ext
      dsimp [wq, rPosSubLocal, rSubPayloadCore, q_s, q_sw, q_b, q_bw, q_f, q_fw,
        posCoreWires, posPayloadWires, r_e, Function.Embedding.refl_apply,
          Function.Embedding.coeFn_mk]
      try omega
    change cBeta s0 p80 z₁ wq = cBeta s0 p80 z₂ wq
    rw [hw, cB_pay, cB_pay]
open NuclearTwistRealizes (barrelActive barrelBitFn coin0Active
  slot2AxisDelta slot2M48Val slot2TotalPhaseExp slot4TotalPhaseExp twistCorePermFn
    twistCorePermFn_high_eq twistCorePhase uTwistParam_mulVec_basisKet)
theorem sb_tw
    (cfg : Configuration) (p80 : Pay80)
    (hanc : bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)) < 218) :
    let i : Fin 218 := ⟨bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)), hanc⟩
    let b₀ := pB0 p80
    let b₁ := pB1 p80
    sysBlk hkF
        (@castUnitaryPow2 (twCW 80) (fullSysCoreWires 80) pos24_core80_eq_twist80.symm
          (uTwistParam true h22_80 cfg)).1 true p80 *
        smToTwos654SysUnitary.1 =
      oSU.1 *
        ((rEl_sp 0).embedUnitary (slot4CosetDiag18 b₀ b₁)).1 *
        (permutationUnitary (permElectron (Equiv.swap i 0))).1 := by
  intro i b₀ b₁
  have htw_lt : ∀ w : Wire (twCW 80), w.val < posCoreWires := fun w ↦ hkT.symm ▸ w.isLt
  have h654_def : smToTwos654SysUnitary = fwdPU pSm654 := rfl
  rw[sb_cp hkT hkF pos24_core80_eq_twist80.symm (uTwistParam true h22_80 cfg) true p80, h654_def,
    os_fp, em_cd, pu_fp]
  let φ : SysIdx → ℂ := fun y ↦ ∏ w : Fin 3, dyadicTurn 48 ((2 ^ 41 : ℤ) * ((((b₁ w).val : ℤ)
      - ((b₀ w).val : ℤ)) * ((eOff18 ((rEl_sp 0).extractIndex y) w).val : ℤ)))
  ext x' z
  let x_in := pSm654 z
  let z_sw := permElectron (Equiv.swap i 0) z
  let x_out := x32P (pSm654 z_sw)
  have hx_out_alt : x_out = x32P (permElectron (Equiv.swap i 0) x_in) :=
    congrArg x32P (pe_65 (Equiv.swap i 0) z).symm
  have hRHS : ((fwdPU (pSm654.trans x32P)).1 * diagonal φ * (fwdPU (permElectron (Equiv.swap i
    0))).1) x' z = if x' = x_out then φ z_sw else 0 := by
    rw [m_fp, Matrix.mul_diagonal, fwdPermUnitary_apply, Equiv.trans_apply]
    by_cases h : x' = x_out
    · rw [it_t h.symm, one_mul, it_t h]
    · rw [it_f (Ne.symm h), zero_mul, it_f h]
  rw [m_fp _ pSm654 x' z, hRHS, sysBlockAtPayloadGen_apply]
  let col := coreIdxOf hkT true p80 x_in
  let col' := coreIdxOf hkT true p80 x_out
  let γ := basisBits (twCW 80) col
  let γ' := basisBits (twCW 80) col'
  have hw2 : γ (wSlot2 (idReg (twCW 80))) = 0 :=
    (ci_b hkT true p80 x_in _).trans (coreBetaOf_mid true p80 x_in _
      (by
        dsimp only [wSlot2, q_i, q_iw, twCW, posCoreWires, systemQubits, numElectrons, electronBits,
          projectileBits]; omega)
      (by
        dsimp only [wSlot2, q_i, q_iw, twCW, systemQubits, numElectrons, electronBits,
          projectileBits]; omega))
  have hw1 : γ (wSlot1 (idReg (twCW 80))) = 0 :=
    (ci_b hkT true p80 x_in _).trans (coreBetaOf_mid true p80 x_in _
      (by
        dsimp only [wSlot1, q_i, q_iw, twCW, posCoreWires, systemQubits, numElectrons, electronBits,
          projectileBits]; omega)
      (by
        dsimp only [wSlot1, q_i, q_iw, twCW, systemQubits, numElectrons, electronBits,
          projectileBits]; omega))
  have hw0 : γ (wSlot0 (idReg (twCW 80))) = 1 :=
    (ci_b hkT true p80 x_in _).trans (coreBetaOf_mid true p80 x_in _
      (by
        dsimp only [wSlot0, q_i, q_iw, twCW, posCoreWires, systemQubits, numElectrons, electronBits,
          projectileBits]; omega)
      (by
        dsimp only [wSlot0, q_i, q_iw, twCW, systemQubits, numElectrons, electronBits,
          projectileBits]; omega))
  have hpay_bit {x : SysIdx} (w : Wire (twCW 80)) (idx : Fin 80) (hw : w.val = 3954 +
    idx.val) : basisBits (twCW 80) (coreIdxOf hkT true p80 x) w = p80 idx := by
    rw [ci_b hkT, show (⟨w.val, htw_lt w⟩ : Wire posCoreWires) = rPosSubLocal idx from
      Fin.ext (by
        dsimp [rPosSubLocal, rSubPayloadCore, q_f, q_fw, posCoreWires, posPayloadWires,
          r_e, Function.Embedding.refl_apply, Function.Embedding.coeFn_mk]
        exact hw), cB_pay]
  have hanc_eq : regVal (twAnc h22_80 (idReg (twCW 80))) γ = i.val := by
    dsimp only [i]
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun j _ ↦ congrArg (fun b : ZMod 2 ↦ b.val * 2 ^ j.val) ?_
    exact hpay_bit _ (pos80SubIdx 14 8 (by decide) j) (by
      dsimp [twAnc, pos80SubIdx, q_s, q_sw, q_b, q_bw, q_i, q_iw, twCW, posCoreWires,
        systemQubits, numElectrons, electronBits, projectileBits]
      omega)
  have hperm_eq : twistCorePermFn true h22_80 γ = γ' := by
    funext q
    by_cases hq : q.val < 3924
    · have hq_sys : q.val < systemQubits := by
        dsimp [systemQubits, numElectrons, electronBits, projectileBits]
        omega
      let qS : Wire systemQubits := ⟨q.val, hq_sys⟩
      have hact : barrelActive true γ = true ∧ regVal (twAnc h22_80 (idReg (twCW 80))) γ < 218 :=
        ⟨by simp [barrelActive, hw2, hw1], hanc_eq ▸ i.isLt⟩
      have hbar : barrelBitFn true h22_80 γ q = basisBits systemQubits (permElectron (Equiv.swap i
        0) x_in) qS := by
        rw [bb_pe (Equiv.swap i 0) x_in qS]
        unfold barrelBitFn
        rw [dt_t hact]
        let e : Fin numElectrons := ⟨q.val / 18, div_18_lt_numElectrons hq⟩
        let qP : Wire systemQubits := permElectronWire (Equiv.swap i 0) qS
        have hpew : qP.val = 18 * ((Equiv.swap i 0) e).val + q.val % 18 := by
          change (permElectronWireFun (Equiv.swap i 0) qS).val = _
          unfold permElectronWireFun
          simp only [qS, hq, ↓reduceDIte]
          rfl
        have hcb_qP (w : Wire (twCW 80)) (hw : w.val = qP.val) : γ w = basisBits systemQubits x_in
          qP := by
          rw [show γ w = _ from ci_b hkT true p80 x_in w, show (⟨w.val, htw_lt w⟩ : Wire
            posCoreWires) =
            ⟨qP.val, Nat.lt_trans qP.isLt lt_sys_4034⟩ from Fin.ext hw, coreBetaOf_lt3948 true p80
              x_in qP]
        have hev : e.val = q.val / 18 := rfl
        have hne {c : Fin numElectrons} (hc : q.val / 18 ≠ c.val) : e ≠ c :=
          fun h ↦ hc (hev.symm.trans (congrArg Fin.val h))
        by_cases hk0 : q.val < 18
        · rw [dt_t hk0]
          have he0 : e = 0 := Fin.ext (by dsimp [e]; omega)
          exact hcb_qP ⟨18 * regVal (twAnc h22_80 (idReg (twCW 80))) γ + q.val, by
            rw [hanc_eq]; have := i.isLt
            dsimp [twCW, systemQubits, numElectrons, electronBits, projectileBits]; omega⟩
            (by dsimp only; rw [hanc_eq, hpew, he0, Equiv.swap_apply_right, Nat.mod_eq_of_lt hk0])
        · rw [dt_f hk0]
          by_cases hk1 : 18 * i.val ≤ q.val ∧ q.val < 18 * i.val + 18
          · rw [dt_t (by rwa [hanc_eq])]
            have hei : e = i := Fin.ext (by dsimp [e]; omega)
            exact hcb_qP ⟨q.val - 18 * regVal (twAnc h22_80 (idReg (twCW 80))) γ,
              Nat.lt_of_le_of_lt (Nat.sub_le _ _) q.isLt⟩
              (by dsimp only; rw [hanc_eq, hpew, hei, Equiv.swap_apply_left, Fin.val_zero]; omega)
          · rw [dt_f (by rwa [hanc_eq])]
            exact hcb_qP q (by
              rw [hpew, Equiv.swap_apply_of_ne_of_ne (hne (by omega))
                (hne (show q.val / 18 ≠ 0 by omega))]
              omega)
      rw [tw_p, hbar, show γ' q = _ from ci_b hkT true p80 x_out q]
      have hw_sys : (⟨q.val, htw_lt q⟩ : Wire posCoreWires) =
          ⟨qS.val, Nat.lt_trans qS.isLt lt_sys_4034⟩ := rfl
      rw [hw_sys, coreBetaOf_lt3948 true p80 x_out qS, hx_out_alt, bb_x3]
    · rw [twistCorePermFn_high_eq true h22_80 γ q (Nat.le_of_not_lt hq)]
      by_cases hlt_sys : q.val < systemQubits
      · let qS : Wire systemQubits := ⟨q.val, hlt_sys⟩
        rw [show γ q = _ from ci_b hkT true p80 x_in q, show γ' q = _ from ci_b hkT true p80 x_out
          q]
        have hw1' : (⟨q.val, htw_lt q⟩ : Wire posCoreWires) =
            ⟨qS.val, Nat.lt_trans qS.isLt lt_sys_4034⟩ := rfl
        rw [hw1', coreBetaOf_lt3948 true p80 x_in qS, coreBetaOf_lt3948 true p80 x_out qS,
          hx_out_alt, bb_x3, it_f (show ¬(q.val < 3924 ∧ q.val % 6 = 5) by omega),
          bb_pe (Equiv.swap i 0) x_in qS]
        refine congrArg (basisBits systemQubits x_in) (Fin.ext ?_)
        change q.val = (permElectronWireFun (Equiv.swap i 0) qS).val
        unfold permElectronWireFun
        simp only [qS, hq, ↓reduceDIte]
      · exact rt_c true p80 x_in x_out (Nat.le_of_not_lt hlt_sys)
  have hphase_eq : twistCorePhase true h22_80 cfg γ = φ z_sw := by
    rw [tw_h cfg γ, hperm_eq]
    have hhigh' (w : Wire (twCW 80)) (hw : 3924 ≤ w.val) : γ' w = γ w := by
      rw [← hperm_eq, twistCorePermFn_high_eq _ _ _ _ hw]
    have hw2' : γ' (wSlot2 (idReg (twCW 80))) = 0 :=
      (hhigh' _ (by
        dsimp only [wSlot2, q_i, q_iw, twCW, systemQubits, numElectrons, electronBits,
          projectileBits]; omega)).trans hw2
    have hw1' : γ' (wSlot1 (idReg (twCW 80))) = 0 :=
      (hhigh' _ (by
        dsimp only [wSlot1, q_i, q_iw, twCW, systemQubits, numElectrons, electronBits,
          projectileBits]; omega)).trans hw1
    have hw0' : γ' (wSlot0 (idReg (twCW 80))) = 1 :=
      (hhigh' _ (by
        dsimp only [wSlot0, q_i, q_iw, twCW, systemQubits, numElectrons, electronBits,
          projectileBits]; omega)).trans hw0
    have hs2_zero : slot2TotalPhaseExp cfg h22_80 γ' = 0 :=
      Finset.sum_eq_zero fun w _ ↦ by
        simp [slot2AxisDelta, slot2M48Val, coin0Active, hw2', hw1', hw0']
    rw [hs2_zero, Int.add_zero]
    unfold slot4TotalPhaseExp
    dsimp only [idReg] at hw2' hw1' hw0'
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hw2', hw1', hw0'⟩)]
    refine (congrArg (dyadicTurn 48) (Finset.sum_congr rfl fun w _ ↦
      congrArg ((2 ^ 41 : ℤ) * ·) ?_)).trans (dt_s3 _)
    let rId := idReg (twCW 80)
    have hb1_w : (γ' (NuclearTwistAndXor654Concrete.rCosetB1 h22_80 rId w)).val = (b₁ w).val :=
      congrArg ZMod.val (hpay_bit _ ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩ (by
        dsimp [NuclearTwistAndXor654Concrete.rCosetB1, rId, q_s, q_sw, q_b, q_bw, q_i, q_iw,
          twCW, posCoreWires, systemQubits, numElectrons, electronBits, projectileBits]))
    have hb0_w : (γ' (NuclearTwistAndXor654Concrete.rCosetB0 h22_80 rId w)).val = (b₀ w).val :=
      congrArg ZMod.val (hpay_bit _ (pos80SubIdx 3 3 (by decide) w) (by
        dsimp [NuclearTwistAndXor654Concrete.rCosetB0, rId, pos80SubIdx, q_s, q_sw, q_b, q_bw,
          q_i, q_iw, twCW, posCoreWires, systemQubits, numElectrons, electronBits,
          projectileBits]
        try omega))
    have hax_w : regVal (rElecSlotAxis (idReg (twCW 80)) 0 w) γ' = (eOff18 ((rEl_sp 0).extractIndex
      z_sw) w).val := by
      let m : Fin 654 := ⟨3 * (0 : Fin numElectrons).val + w.val, by
        have : numElectrons = 218 := rfl
        have := w.isLt
        omega⟩
      have hbits_eq : (fun j : Fin 6 ↦ γ' (rElecSlotAxis (idReg (twCW 80)) 0 w j)) =
          basisBits 6 (elecAxisField x_out 0 w) := funext fun j ↦ by
        rw [show γ' _ = _ from ci_b hkT true p80 x_out _,
          show (⟨(rElecSlotAxis (idReg (twCW 80)) 0 w j).val, htw_lt _⟩ : Wire posCoreWires) =
            ⟨(elec654Axes m j).val, Nat.lt_trans (elec654Axes m j).isLt lt_sys_4034⟩ from
            Fin.ext (by
              dsimp [rElecSlotAxis, elec654Axes, q_s, q_sw, q_i, q_iw, twCW, posCoreWires,
                systemQubits, numElectrons, electronBits, projectileBits, q_b, q_bw, r_e,
                Function.Embedding.refl_apply, m]
              omega),
          coreBetaOf_lt3948 true p80 x_out (elec654Axes m j)]
        exact (bb_e x_out 0 w j).symm
      change bitsVal (fun j : Fin 6 ↦ γ' (rElecSlotAxis (idReg (twCW 80)) 0 w j)) = _
      rw [hbits_eq, bv_b6, show x_out = x32P (pSm654 z_sw) from rfl, ea_x6, ea_u]
      rfl
    rw [hb1_w, hb0_w, hax_w]
  have hmv := uTwistParam_mulVec_basisKet true h22_80 cfg
    (QRegExt.ofFin (twCW 80)) (basisBits (twCW 80) col)
  rw [ofFin_embedUnitary_eq] at hmv
  have hket_out : (fun w : Wire (twCW 80) ↦ if hw : w ∈ (QRegExt.ofFin (twCW 80)).image then
      twistCorePermFn true h22_80 γ (Classical.choose ((QRegister.mem_image _ w).mp hw)) else
      basisBits (twCW 80) col w) = γ' := funext fun w ↦ by
    have hw_mem : w ∈ (QRegExt.ofFin (twCW 80)).image := (QRegister.mem_image _ w).mpr ⟨w, rfl⟩
    have hch : Classical.choose ((QRegister.mem_image _ w).mp hw_mem) = w :=
      (QRegExt.ofFin (twCW 80)).wires.injective
        (Classical.choose_spec ((QRegister.mem_image _ w).mp hw_mem))
    simp only [hw_mem, ↓reduceDIte, hch, hperm_eq]
  rw [show (fun q ↦ basisBits (twCW 80) col ((QRegExt.ofFin (twCW 80)) q)) = γ from rfl,
    hket_out, hphase_eq, @bk_sg (twCW 80) col, @bk_sg (twCW 80) col'] at hmv
  have hrow := congrFun hmv (coreIdxOf hkT true p80 x')
  rw [mv_s1] at hrow
  by_cases hxx : x' = x_out
  · subst hxx
    rw [ss_eq] at hrow
    rw [hrow, it_t rfl]
  · rw [ss_ne _ fun h ↦ hxx (coreIdxOf_injective hkT true p80 h)] at hrow
    rw [hrow, it_f hxx]
private theorem em_p3 (e : Fin 218) (M : Operator (2 ^ 18)) : (rEl_sp e).embedMatrix M *
    (fwdPU pSmP3).1 = (fwdPU pSmP3).1 * (rEl_sp e).embedMatrix M := by
  let σ := pSmP3
  have hex (y : SysIdx) : (rEl_sp e).extractIndex (σ y) = (rEl_sp e).extractIndex y :=
    u18AxisSplitEquiv.injective (funext fun w ↦ by
      rw [← ea_u, ← ea_u]
      exact elecAxisField_smToTwosProj3 y e w)
  have hσ_inv (u : SysIdx) : σ (σ u) = u :=
    fs_ef (fun i w ↦ by rw [elecAxisField_smToTwosProj3, elecAxisField_smToTwosProj3])
      fun w ↦ by
        rw [projAxisField_smToTwosProj3, projAxisField_smToTwosProj3, smToTwosAxisPerm_self]
  have hag_mp (y' y : SysIdx) (hag : (rEl_sp e).AgreeOutside (σ y') (σ y)) : (rEl_sp e).AgreeOutside
    y' y := by
    intro q hq
    rcases sysWire_cases q with ⟨i, w, j, rfl⟩ | ⟨w, j, rfl⟩
    · let m : Fin 654 := ⟨3 * i.val + w.val, by
        have : numElectrons = 218 := rfl
        have := i.isLt
        have := w.isLt
        omega⟩
      have hb (u : SysIdx) : basisBits systemQubits (σ u) (elec654Axes m j) = basisBits systemQubits
        u (elec654Axes m j) := by
        simpa only [bb_e] using
          congrFun (congrArg (basisBits 6) (elecAxisField_smToTwosProj3 u i w)) j
      rw [← hb y', ← hb y]
      exact hag (elec654Axes m j) hq
    · have hp_σ : projAxisField (σ y') w = projAxisField (σ y) w :=
        (basisBitsEquiv 8).injective (funext fun j' ↦ by
          change basisBits 8 _ j' = basisBits 8 _ j'
          rw [bb_p, bb_p]
          refine hag (proj3Axes w j') fun ⟨k, hk⟩ ↦ ?_
          have hv := congrArg Fin.val hk
          have := e.isLt
          have := k.isLt
          dsimp [rEl_sp, proj3Axes, q_b, q_bw] at hv
          omega)
      rw [projAxisField_smToTwosProj3, projAxisField_smToTwosProj3] at hp_σ
      simpa only [bb_p] using
        congrFun (congrArg (basisBits 8) ((smToTwosAxisPerm 5).injective hp_σ)) j
  have hag_iff (y' y : SysIdx) : (rEl_sp e).AgreeOutside (σ y') (σ y) ↔ (rEl_sp e).AgreeOutside y'
    y :=
    ⟨hag_mp y' y, fun hag ↦ hag_mp (σ y') (σ y) (by rwa [hσ_inv, hσ_inv])⟩
  ext x' x
  rw [m_fp _ σ x' x, fp_mm σ _ x' x]
  let y' := σ.symm x'
  rw [show x' = σ y' from (σ.apply_symm_apply x').symm, σ.symm_apply_apply]
  by_cases hag : (rEl_sp e).AgreeOutside y' x
  · rw [embedMatrix_entry_of_agreeOutside (rEl_sp e) M ((hag_iff y' x).mpr hag),
      embedMatrix_entry_of_agreeOutside (rEl_sp e) M hag, hex, hex]
  · rw [embedMatrix_entry_of_not_agreeOutside (rEl_sp e) M (mt (hag_iff y' x).mp hag),
      embedMatrix_entry_of_not_agreeOutside (rEl_sp e) M hag]
theorem sc_p3 (b₀ b₁ : NyqParity3D) (i : Fin 218) : (s4CU b₀ b₁ i).1 * (fwdPU pSmP3).1 =
    (fwdPU pSmP3).1 * (s4CU b₀ b₁ i).1 := by
  rw [(congrArg Subtype.val (rfl : s4CU b₀ b₁ i = _)).trans (u_m3 _ _ _)]
  exact mul3_comm_of_comm _ _ _ _
    (u_fcm (fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (vB18 b₁)) (fwdPU pSmP3).1 fun e ↦
      em_p3 e (vB18 b₁).1)
    (em_p3 0 _)
    (by rw [pu_fp]; exact fp_cm _ pSmP3 (pe_p3 (Equiv.swap i 0)))
theorem cb_p3 (s0 : Bool) (p80 : Pay80) (z : SysIdx) (w : Wire posCoreWires) (hw : w.val < 3924 ∨
    3948 ≤ w.val) : cBeta s0 p80 (pSmP3 z) w = cBeta s0 p80 z w := by
  rcases hw with hlt | hge
  · let qS : Wire systemQubits := ⟨w.val, by
      dsimp [systemQubits, numElectrons, electronBits, projectileBits]
      omega⟩
    rw [show w = ⟨qS.val, Nat.lt_trans qS.isLt lt_sys_4034⟩ from rfl, coreBetaOf_lt3948 s0 p80
      (pSmP3 z) qS, coreBetaOf_lt3948 s0 p80 z qS]
    let e : Fin numElectrons := ⟨w.val / 18, div_18_lt_numElectrons hlt⟩
    let ax : Fin 3 := ⟨(w.val % 18) / 6, by omega⟩
    let j : Fin 6 := ⟨w.val % 6, by omega⟩
    have hq_eq : qS = elec654Axes ⟨3 * e.val + ax.val, by
        have : numElectrons = 218 := rfl
        have := e.isLt
        have := ax.isLt
        omega⟩ j := Fin.ext (by
          dsimp [qS, elec654Axes, q_b, q_bw, e, ax, j]
          omega)
    have h1 := congrFun (congrArg (basisBits 6) (elecAxisField_smToTwosProj3 z e ax)) j
    rwa [bb_e, bb_e, ← hq_eq] at h1
  · by_cases hlt3954 : w.val < 3954
    · rw [coreBetaOf_mid s0 p80 _ w hge hlt3954, coreBetaOf_mid s0 p80 _ w hge hlt3954]
    · have hsub : w.val - 3954 < 80 := by
        have := w.isLt
        dsimp [posCoreWires] at this
        omega
      rw [show w = rPosSubLocal ⟨w.val - 3954, hsub⟩ from Fin.ext (by
        dsimp [rPosSubLocal, rSubPayloadCore, q_s, q_sw, q_b, q_bw, q_f, q_fw,
          posCoreWires, posPayloadWires, r_e, Function.Embedding.refl_apply,
          Function.Embedding.coeFn_mk]
        omega), cB_pay, cB_pay]
private theorem pp_p3 (s0 : Bool) (p80 : Pay80) (z : SysIdx) : posPhaseBit true tSgn tMag30 (cBeta
    s0 p80 (pSmP3 z)) = posPhaseBit true tSgn tMag30 (cBeta s0 p80 z) := by
  let β₁ := cBeta s0 p80 (pSmP3 z)
  let β₂ := cBeta s0 p80 z
  let rCore := QRegExt.ofFin posCoreWires
  have hw_high (w : Wire posCoreWires) (hw : 3948 ≤ w.val) : β₁ w = β₂ w :=
    cb_p3 s0 p80 z w (Or.inr hw)
  have hsub_ge (k : Fin 80) : 3948 ≤ (rSubPayloadCore rCore k).val := by
    have := k.isLt
    dsimp [rSubPayloadCore, rCore, q_s, q_sw, q_b, q_bw, q_f, q_fw, posCoreWires, posPayloadWires,
      r_e, Function.Embedding.refl_apply, Function.Embedding.coeFn_mk]
    omega
  have hreg_sub (off len : ℕ) (h : off + len ≤ 80) : regVal ((rSubPayloadCore rCore).slice off len
    h) β₁ = regVal ((rSubPayloadCore rCore).slice off len h) β₂ :=
    regVal_eq_of_wire_eq _ β₁ β₂ fun j ↦ hw_high _ (by
      rw [QRegister.slice_apply]
      exact hsub_ge _)
  have hpar_sub (off : ℕ) (h : off + 3 ≤ 80) : parity3OfReg ((rSubPayloadCore rCore).slice off 3 h)
    β₁ = parity3OfReg ((rSubPayloadCore rCore).slice off 3 h) β₂ :=
    funext fun w ↦ by
      dsimp only [parity3OfReg]
      rw [QRegister.slice_apply, hw_high _ (hsub_ge _)]
  have hslot (e : Fin 218) : slotSubGridCoord64 (rElecSlot rCore e) β₁ = slotSubGridCoord64
    (rElecSlot rCore e) β₂ := by
    funext w
    apply Fin.ext
    dsimp only [slotSubGridCoord64]
    refine regVal_eq_of_wire_eq _ β₁ β₂ fun j ↦ cb_p3 s0 p80 z _ (Or.inl ?_)
    have := e.isLt
    have := w.isLt
    have := j.isLt
    dsimp [ax_r, ax_rw, rElecSlot, rCore, q_s, q_sw, q_b, q_bw, q_f, q_fw,
      posCoreWires, posPayloadWires, r_e, Function.Embedding.refl_apply,
      Function.Embedding.coeFn_mk]
    try omega
  have hrFine : fineCoordOfReg21 (rHeadFine21 rCore) β₁ = fineCoordOfReg21 (rHeadFine21 rCore) β₂ :=
    funext fun w ↦ Fin.ext (regVal_eq_of_wire_eq _ β₁ β₂ fun j ↦ hw_high _ (by
      dsimp only [rHeadFine21]
      rw [QRegister.slice_apply, QRegister.slice_apply]
      exact hsub_ge _))
  have hH : headPhaseBitSpec β₁ = headPhaseBitSpec β₂ := by
    unfold headPhaseBitSpec
    simp only [rCore, hw_high _ (by decide : 3948 ≤ (wSlot2Core rCore).val),
      hw_high _ (by decide : 3948 ≤ (wSlot1Core rCore).val),
      hw_high _ (by decide : 3948 ≤ (wSlot0Core rCore).val),
      hw_high _ (by decide : 3948 ≤ (wSubReject rCore).val),
      hw_high _ (by decide : 3948 ≤ (wIsHead rCore).val),
      hw_high _ (by decide : 3948 ≤ (wHeadThresh rCore).val),
      show regVal (rNucIdx rCore) β₁ = regVal (rNucIdx rCore) β₂ from hreg_sub 6 8 (by decide),
      show regVal (rAnchorIdx rCore) β₁ = regVal (rAnchorIdx rCore) β₂ from
        hreg_sub 14 8 (by decide),
      hrFine,
      show parity3OfReg (rCosetB0 rCore) β₁ = parity3OfReg (rCosetB0 rCore) β₂ from
        hpar_sub 3 (by decide), hslot]
  have hT : tailAndSlackPhaseBitSpec true tSgn tMag30 β₁ = tailAndSlackPhaseBitSpec true tSgn tMag30
    β₂ := by
    unfold tailAndSlackPhaseBitSpec
    simp only [rCore, hw_high _ (by decide : 3948 ≤ (wSlot2Core rCore).val),
      hw_high _ (by decide : 3948 ≤ (wSlot1Core rCore).val),
      hw_high _ (by decide : 3948 ≤ (wSlot0Core rCore).val),
      hw_high _ (by decide : 3948 ≤ (wSubReject rCore).val),
      hw_high _ (by decide : 3948 ≤ (wIsHead rCore).val),
      hw_high _ (by decide : 3948 ≤ (wRejectZero rCore).val),
      show regVal (rNucIdx rCore) β₁ = regVal (rNucIdx rCore) β₂ from hreg_sub 6 8 (by decide),
      show regVal (rAnchorIdx rCore) β₁ = regVal (rAnchorIdx rCore) β₂ from
        hreg_sub 14 8 (by decide),
      show regVal (rPartnerIdx rCore) β₁ = regVal (rPartnerIdx rCore) β₂ from
        hreg_sub 22 8 (by decide),
      show regVal (rTailKeep30 rCore) β₁ = regVal (rTailKeep30 rCore) β₂ from
        hreg_sub 32 30 (by decide),
      show parity3OfReg (rCosetB0 rCore) β₁ = parity3OfReg (rCosetB0 rCore) β₂ from
        hpar_sub 3 (by decide),
      show parity3OfReg (rCosetB1 rCore) β₁ = parity3OfReg (rCosetB1 rCore) β₂ from
        hpar_sub 0 (by decide), hslot]
  unfold posPhaseBit
  rw [hH, hT]
private theorem bs_cc (qft : FullSysQft654Bundle) (hqft : qft.uQft654 = qft64Ideal654Unitary)
    (cfg : Configuration) (p80 : Pay80)
    (hanc : bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)) < 218) :
    let i : Fin 218 := ⟨bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)), hanc⟩
    let b₀ := pB0 p80
    let b₁ := pB1 p80
    smToTwosSysUnitary.1 * sysBlk hkF (pos24ConjCore80 qft cfg).1 true p80 *
        smToTwosSysUnitary.1 =
      (s4CU b₀ b₁ i).1ᴴ *
        diagonal (fun z : SysIdx ↦
          if posPhaseBit true tSgn tMag30 (cBeta true p80 z) then (-1 : ℂ) else 1) *
        (s4CU b₀ b₁ i).1 := by
  intro i b₀ b₁
  let U_qft := (fQftU h6_80 qft).1
  let U_tw := (@castUnitaryPow2 (twCW 80) (fullSysCoreWires 80) pos24_core80_eq_twist80.symm
    (uTwistParam true h22_80 cfg)).1
  let d_fn : SysIdx → ℂ := fun z ↦
    if posPhaseBit true tSgn tMag30 (cBeta true p80 z) then (-1 : ℂ) else 1
  let D_kar := diagonal (fun z : SysIdx ↦ ∏ e : Fin 218, karatsubaOutPhase3D (sCd z e))
  have hQft_mul_off : sysBlk hkF U_qft true p80 * oSU.1 = D_kar * (vSU b₁).1 := by
    have hoff_def : oSU = (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary o18U).prod := rfl
    have hvee_def : vSU b₁ = (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (vB18 b₁)).prod :=
      rfl
    rw [sb_qf qft hqft true p80, hoff_def, ← u_mv, lf_pm]
    have h18 : (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (qft64OffsetUnitary3D b₁ *
      o18U)) = (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (oP18 * vB18 b₁)) :=
      congrArg List.ofFn (funext fun e ↦ congrArg (rEl_sp e).embedUnitary (Subtype.ext (qf_o1 b₁)))
    rw [h18, ← lf_pm, u_mv, lf_op, ← hvee_def]
  have hKar_cancel : D_karᴴ * diagonal d_fn * D_kar = diagonal d_fn :=
    ud_cd _ d_fn fun z ↦ by
      rw [star_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun e _ ↦ karatsubaOutPhase3D_unit (sCd z e)
  let P_proj := fwdPU pSmP3
  have hSm_left : smToTwosSysUnitary.1 = P_proj.1ᴴ * smToTwos654SysUnitary.1ᴴ := by
    rw [← smToTwosSysUnitary_conjTranspose, sm_p3, Matrix.conjTranspose_mul]
  have hDiag_proj : P_proj.1ᴴ * diagonal d_fn * P_proj.1 = diagonal d_fn := by
    rw [fwdPermUnitary_conj_diagonal]
    refine congrArg diagonal (funext fun z ↦ ?_)
    dsimp only [Function.comp_apply, d_fn]
    rw [pp_p3]
  have hB_fac : sysBlk hkF (pos24ConjCore80 qft cfg).1 true p80 = (sysBlk hkF U_qft true p80 *
    sysBlk hkF U_tw true p80)ᴴ * diagonal d_fn *
      (sysBlk hkF U_qft true p80 * sysBlk hkF U_tw true p80) := by
    rw [sb_c8 qft (qftPreservesCoset3_of_eq_ideal qft hqft) cfg true p80, sb_pp true p80]
  have hs4_mul : (s4CU b₀ b₁ i).1 = (vSU b₁).1 * ((rEl_sp 0).embedUnitary (slot4CosetDiag18 b₀
    b₁)).1 * (permutationUnitary (permElectron (Equiv.swap i 0))).1 :=
    (congrArg Subtype.val (rfl : s4CU b₀ b₁ i = _)).trans (u_m3 _ _ _)
  exact bs_af smToTwosSysUnitary.1 smToTwos654SysUnitary.1 P_proj.1
    (sysBlk hkF (pos24ConjCore80 qft cfg).1 true p80) (sysBlk hkF U_qft true p80)
    (sysBlk hkF U_tw true p80) oSU.1 ((rEl_sp 0).embedUnitary (slot4CosetDiag18 b₀ b₁)).1
    (permutationUnitary (permElectron (Equiv.swap i 0))).1 D_kar (vSU b₁).1 (s4CU b₀ b₁ i).1
    (diagonal d_fn) hSm_left sm_p3 hB_fac (sb_tw cfg p80 hanc) hQft_mul_off hs4_mul
    hKar_cancel (sc_p3 b₀ b₁ i) hDiag_proj
private noncomputable abbrev blkSm80 (qft : FullSysQft654Bundle) (cfg : Configuration) (p80 :
    Pay80) : SysOp :=
  smToTwosSysUnitary.1 * sysBlk hkF (pos24ConjCore80 qft cfg).1 true p80 *
    smToTwosSysUnitary.1
private theorem bs_cc_mt (qft : FullSysQft654Bundle) (hqft : qft.uQft654 = qft64Ideal654Unitary)
    (cfg : Configuration) (p80 : Pay80) (b₀ b₁ : NyqParity3D) (anc : Fin 218) (hmt : pB0 p80 = b₀ ∧
      pB1 p80 = b₁ ∧
    bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)) = anc.val) (d : SysIdx →
      ℂ) (hd : ∀ z, (if posPhaseBit true tSgn tMag30 (cBeta true p80 z) then (-1 : ℂ) else 1) =
        d z) :
    blkSm80 qft cfg p80 = (s4CU b₀ b₁ anc).1ᴴ * diagonal d * (s4CU b₀ b₁ anc).1 := by
  rcases hmt with ⟨hb0, hb1, hanc_val⟩
  have hanc : bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)) < 218 :=
    hanc_val ▸ anc.isLt
  have hi_eq : (⟨bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)), hanc⟩ :
      Fin 218) = anc := Fin.ext hanc_val
  simpa only [blkSm80, hb0, hb1, hi_eq, funext hd] using bs_cc qft hqft cfg p80 hanc
abbrev pos24HeadFine (k : Fin 56) (pid : Fin 6) (sm : Fin 8) : NyqFine3D128 :=
  pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm
noncomputable abbrev veePairAt (b₀ : NyqParity3D) (d : NyqFine3D128) (i : Fin numElectrons) :
    SysOp := saPair (vKet b₀) (vKet (ancPar b₀ d)) (fun y₀ ↦ (ancTgt y₀ b₀ d).1) i
theorem pos80Slot4TotNat_cast_ne_zero : (pos80Slot4TotNat : ℝ) ≠ 0 := fun h0 ↦ by
  have hp := pos80Slot4Scale_pos
  unfold pos80Slot4Scale at hp
  rw [h0] at hp
  norm_num at hp
theorem ss_cb (s0 : Bool) (p80 : Pay80) (z : SysIdx) (e : Fin 218) : slotSubGridCoord64 (rElecSlot
    (QRegExt.ofFin posCoreWires) e) (cBeta s0 p80 z) = sCd z e := by
  funext w
  apply Fin.ext
  let m : Fin 654 := ⟨3 * e.val + w.val,
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left w.isLt _) (by have := e.isLt; omega)⟩
  have hbits : (fun j : Fin 6 ↦
      cBeta s0 p80 z (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j)) =
      fun j : Fin 6 ↦ basisBits 6 (elecAxisField z e w) ⟨5 - j.val, by omega⟩ := funext fun j ↦ by
    have hw_eq : axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j = ⟨(elec654Axes m ⟨5 -
      j.val, by omega⟩).val,
        Nat.lt_trans (elec654Axes m ⟨5 - j.val, by omega⟩).isLt lt_sys_4034⟩ := by
      ext
      change 18 * e.val + (6 * w.val + (5 - j.val)) = 6 * (3 * e.val + w.val) + (5 - j.val)
      omega
    rw [hw_eq, coreBetaOf_lt3948 s0 p80 z (elec654Axes m ⟨5 - j.val, by omega⟩)]
    exact (bb_ext (elec654Axes m) z ⟨5 - j.val, by omega⟩).symm
  change bitsVal (fun j : Fin 6 ↦ cBeta s0 p80 z (axisBitRev6 (rElecSlot (QRegExt.ofFin
    posCoreWires) e) w j)) = (bitRev6Equiv (u18GridEquiv ((rEl_sp e).extractIndex z) w)).val
  rw [hbits, (by decide : ∀ v : Fin 64,
    bitsVal (fun j : Fin 6 ↦ basisBits 6 v ⟨5 - j.val, by omega⟩) = (bitRev6Equiv v).val),
    show u18GridEquiv ((rEl_sp e).extractIndex z) w =
      u18AxisSplitEquiv ((rEl_sp e).extractIndex z) w from rfl, ← ea_u]
private theorem f8_n (o : Fin 8) (w : Fin 3) : (o.val / 2 ^ w.val) % 2 = (nyqP8 o w).val := by
  revert o w
  decide
private theorem ap_x (u : Fin 2) (d : Fin 128) : (anchorParity1D u d).val = Nat.xor u.val (d.val %
    2) := by
  revert u d
  decide
private theorem nat_xor_fin8_bit (o dp : Fin 8) (w : Fin 3) : ((Nat.xor o.val dp.val) / 2 ^ w.val) %
    2 = Nat.xor ((o.val / 2 ^ w.val) % 2) ((dp.val / 2 ^ w.val) % 2) := by
  revert o dp w
  decide
theorem it_d2 (u : Fin 2) : (if decide (u = 1) then (1 : Fin 2) else 0) = u := by
  revert u
  decide
theorem hw_mt (b0 : Fin 8) (anc : Fin 218) (k : Fin 56) (pid : Fin 6) (sm : Fin 8)
    (th rj : Bool) :
    let p80 := headWitnessPayload80 b0.val 0 anc.val k pid sm th rj
    let dH := pos24HeadFine k pid sm
    let b₀ := nyqP8 b0
    pB0 p80 = b₀ ∧ pB1 p80 = ancPar b₀ dH ∧
      bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)) = anc.val := by
  intro p80 dH b₀
  refine ⟨funext fun w ↦ Fin.ext ?_, funext fun w ↦ Fin.ext ?_, ?_⟩
  · dsimp only [pB0]
    have hp : p80 (pos80SubIdx 3 3 (by decide) w) = z2BitOfNat b0.val w.val := by
      dsimp only [p80, headWitnessPayload80]
      fin_cases w <;> rfl
    rw [hp, z2BitOfNat_val, f8_n]
  · dsimp only [pB1, ancPar]
    let dpFin : Fin 8 := ⟨((dH 0).val % 2) + 2 * ((dH 1).val % 2) + 4 * ((dH 2).val % 2), by
      have := (dH 0).isLt
      have := (dH 1).isLt
      have := (dH 2).isLt
      omega⟩
    have hp : p80 ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩ = z2BitOfNat (Nat.xor b0.val dpFin.val)
      w.val := by
      dsimp only [p80, headWitnessPayload80, dpFin]
      fin_cases w <;> rfl
    have hdp_bit : (dpFin.val / 2 ^ w.val) % 2 = (dH w).val % 2 := by
      dsimp only [dpFin]
      fin_cases w <;> (dsimp; omega)
    rw [hp, z2BitOfNat_val, nat_xor_fin8_bit, f8_n, hdp_bit, ap_x]
  · rw [show (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)) =
      fun j : Fin 8 ↦ z2BitOfNat anc.val j.val from funext fun j ↦ by
        dsimp only [p80, headWitnessPayload80]
        fin_cases j <;> rfl]
    exact bitsVal_z2BitOfNat_of_lt (lt_trans anc.isLt (by decide))
private theorem z2_beq1_eq_fin2 {x : ZMod 2} {u : Fin 2} (h : x.val = u.val) : (x == 1) =
    decide (u = 1) := by
  revert h
  revert x u
  decide
private theorem cb_anc_val (p80 : Pay80) (z : SysIdx) {anc : Fin 218} (hmt : bitsVal (fun j : Fin 8
    ↦ p80 (pos80SubIdx 14 8 (by decide) j)) = anc.val) :
    regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (cBeta true p80 z) = anc.val := by
  change bitsVal (fun j : Fin 8 ↦
    cBeta true p80 z (rPosSubLocal (pos80SubIdx 14 8 (by decide) j))) = anc.val
  simp only [cB_pay]
  exact hmt
private theorem cb_b0_dec (p80 : Pay80) (z : SysIdx) {b₀ : NyqParity3D} (hmt : pB0 p80 =
    b₀) (w : Fin 3) :
    parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) (cBeta true p80 z) w = decide (b₀ w =
      1) := by
  refine z2_beq1_eq_fin2 ?_
  rw [show cBeta true p80 z (rCosetB0 (QRegExt.ofFin posCoreWires) w) =
    p80 (pos80SubIdx 3 3 (by decide) w) from cB_pay true p80 z _]
  exact congrArg (fun f ↦ (f w).val) hmt
private theorem pp_hw (b0 : Fin 8) (anc : Fin 218) (k : Fin 56) (pid : Fin 6) (sm : Fin 8)
    (th rj : Bool) (z : SysIdx) :
    let p80 := headWitnessPayload80 b0.val 0 anc.val k pid sm th rj
    let dH := pos24HeadFine k pid sm
    let b₀ := nyqP8 b0
    let S := s4H0 b₀ dH z
    posPhaseBit true tSgn tMag30 (cBeta true p80 z) =
      zeroParityThreshExp false th (proj38ZeroBit S) (proj38OddXorZeroBit S) := by
  intro p80 dH b₀ S
  let rCore := QRegExt.ofFin posCoreWires
  let β := cBeta true p80 z
  have hw2 : β (wSlot2Core rCore) = 0 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hw1 : β (wSlot1Core rCore) = 0 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hw0 : β (wSlot0Core rCore) = 1 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hwSub : β (wSubReject rCore) = 0 := cB_pay true p80 z ⟨62, by decide⟩
  have hwHead : β (wIsHead rCore) = 1 := cB_pay true p80 z ⟨30, by decide⟩
  have hwTh : (β (wHeadThresh rCore) == 1) = th := by
    rw [show β (wHeadThresh rCore) = if th then 1 else 0 from cB_pay true p80 z ⟨31, by decide⟩]
    cases th <;> rfl
  have hrAnc : regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) β = anc.val :=
    cb_anc_val p80 z (hw_mt b0 anc k pid sm th rj).2.2
  have hslot : ∀ e : Fin 218, slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β =
    sCd z e :=
    ss_cb true p80 z
  have hTail0 : tailAndSlackPhaseBitSpec true tSgn tMag30 β = false := by
    unfold tailAndSlackPhaseBitSpec
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hrAnc, anc.isLt, show ((0 : ZMod 2) == 1) =
      false from rfl, show ((1 : ZMod 2) == 1) = true from rfl,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, IsEmpty.forall_iff, decide_true,
        Bool.and_false, Bool.and_self, ↓reduceIte]
  have hFine : fineCoordOfReg21 (rHeadFine21 rCore) β = dH := funext fun w ↦ Fin.ext (by
    dsimp only [fineCoordOfReg21]
    let fineH := (dH 0).val + 128 * (dH 1).val + 16384 * (dH 2).val
    have hfn : (fun j : Fin 7 ↦ β (((rHeadFine21 rCore).slice (7 * w.val) 7 (by omega)) j)) =
        fun j : Fin 7 ↦ z2BitOfNat (dH w).val j.val := funext fun j ↦ by
      have hw_lt : 32 + 7 * w.val + j.val < 80 := by
        have := w.isLt
        have := j.isLt
        omega
      have hw_p : ((rHeadFine21 rCore).slice (7 * w.val) 7 (by omega)) j = rPosSubLocal ⟨32 + 7 *
        w.val + j.val, hw_lt⟩ :=
        Fin.ext (by
          change 3954 + (32 + (7 * w.val + j.val)) = 3954 + (32 + 7 * w.val + j.val)
          omega)
      change cBeta true p80 z _ = _
      rw [hw_p, cB_pay, show p80 ⟨32 + 7 * w.val + j.val, hw_lt⟩ =
        z2BitOfNat fineH (7 * w.val + j.val) by
          dsimp only [p80, headWitnessPayload80, fineH]
          fin_cases w <;> fin_cases j <;> rfl]
      apply ZMod.val_injective
      rw [z2BitOfNat_val, z2BitOfNat_val, pow_add, ← Nat.div_div_eq_div_mul,
        show fineH / 2 ^ (7 * w.val) = (dH w).val + 128 * (fineH / 2 ^ (7 * w.val + 7)) by
          have := (dH 0).isLt
          have := (dH 1).isLt
          have := (dH 2).isLt
          fin_cases w <;> (dsimp [fineH]; omega)]
      have := j.isLt
      have := (dH w).isLt
      fin_cases j <;> (dsimp; omega)
    change bitsVal (fun j : Fin 7 ↦ β (((rHeadFine21 rCore).slice (7 * w.val) 7 _) j)) =
      (dH w).val
    rw [hfn]
    exact bitsVal_z2BitOfNat_of_lt (dH w).isLt)
  have hB0 (w : Fin 3) : (if parity3OfReg (rCosetB0 rCore) β w then (1 : Fin 2) else 0) = b₀ w := by
    rw [cb_b0_dec p80 z (hw_mt b0 anc k pid sm th rj).1 w, it_d2]
  have hHead : headPhaseBitSpec β = zeroParityThreshExp false th (proj38ZeroBit S)
    (proj38OddXorZeroBit S) := by
    unfold headPhaseBitSpec
    dsimp only [rCore] at hB0
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hwTh, hrAnc, anc.isLt, hFine, show ((0 : ZMod 2)
      == 0) = true from rfl, show ((0 : ZMod 2) == 1) = false from rfl,
      show ((1 : ZMod 2) == 1) = true from rfl, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        IsEmpty.forall_iff, decide_true, Bool.and_self, ↓reduceIte, Bool.false_or, hB0, hslot]
    rw [show (Finset.univ.filter fun e : Fin 218 ↦ decide (e.val ≠ 0) && decide (sCd z e =
        fun w ↦ (anchorSubTarget1D (sCd z 0 w) (b₀ w) (dH w)).1)) = S by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true, Bool.and_eq_true,
        decide_eq_true_eq, S, s4H0, Finset.mem_erase]
      exact and_congr (not_congr ⟨fun h ↦ Fin.ext h, congrArg Fin.val⟩) Iff.rfl]
  unfold posPhaseBit
  change Bool.xor (headPhaseBitSpec β) (tailAndSlackPhaseBitSpec true tSgn tMag30 β) = _
  rw [hHead, hTail0, Bool.xor_false]
theorem dg_cz {D : ℕ} (U : Unitary D) (X P : Operator D) (c : Fin D → ℕ) (d_avg : Fin D →
    ℂ) (hint : U.1 * X = diagonal (fun z ↦ (c z : ℂ)) * U.1)
    (hcub : X * (X - 1) * (X - (2 : ℂ) • 1) * P = 0) (hcap : ∀ z, c z ≤ 2 → d_avg z = (c z : ℂ) -
      1) : (U.1ᴴ * diagonal d_avg * U.1) * P = (X - 1) * P := by
  let D_c : Operator D := diagonal (fun z ↦ (c z : ℂ))
  have hX_eq : X = U.1ᴴ * D_c * U.1 := by
    rw [← Matrix.one_mul X, ← u_cs1 U, m_assoc, hint, ← m_assoc]
  have hUX1 : U.1 * (X - 1) = (D_c - 1) * U.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hint, Matrix.mul_one, Matrix.one_mul]
  have hUX2 : U.1 * (X - (2 : ℂ) • 1) = (D_c - (2 : ℂ) • 1) * U.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hint, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  have hDc_cub : diagonal (fun z ↦ (c z : ℂ) * ((c z : ℂ) - 1) * ((c z : ℂ) - 2)) * (U.1 * P) = 0 :=
    by
    have hdiag : D_c * (D_c - 1) * (D_c - (2 : ℂ) • 1) = diagonal (fun z ↦ (c z : ℂ) * ((c z : ℂ) -
      1) * ((c z : ℂ) - 2)) := by
      have h2 : (2 : ℂ) • (1 : Operator D) = diagonal (fun _ ↦ (2 : ℂ)) := by
        rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]
        exact congrArg diagonal (funext fun _ ↦ by simp)
      rw [h2, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_sub,
        diagonal_mul_diagonal, diagonal_mul_diagonal]
    rw [← hdiag]
    calc D_c * (D_c - 1) * (D_c - (2 : ℂ) • 1) * (U.1 * P)
      _ = D_c * (D_c - 1) * ((D_c - (2 : ℂ) • 1) * U.1) * P := by simp only [m_assoc]
      _ = D_c * ((D_c - 1) * U.1) * (X - (2 : ℂ) • 1) * P := by
          rw [← hUX2]
          simp only [m_assoc]
      _ = (D_c * U.1) * (X - 1) * (X - (2 : ℂ) • 1) * P := by
          rw [← hUX1]
          simp only [m_assoc]
      _ = U.1 * (X * (X - 1) * (X - (2 : ℂ) • 1) * P) := by
          rw [← hint]
          simp only [m_assoc]
      _ = 0 := by rw [hcub, Matrix.mul_zero]
  let Δ : Operator D := diagonal (fun z ↦ d_avg z - ((c z : ℂ) - 1))
  have hΔ_zero : Δ * (U.1 * P) = 0 := by
    ext z col
    rw [Matrix.diagonal_mul, Matrix.zero_apply]
    by_cases hle : c z ≤ 2
    · rw [hcap z hle, sub_self, zero_mul]
    · have hqz := congrFun (congrFun hDc_cub z) col
      rw [Matrix.diagonal_mul, Matrix.zero_apply] at hqz
      have hnz : (c z : ℂ) * ((c z : ℂ) - 1) * ((c z : ℂ) - 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
          (sub_ne_zero.mpr (by exact_mod_cast (show c z ≠ 1 by omega))))
          (sub_ne_zero.mpr (by exact_mod_cast (show c z ≠ 2 by omega)))
      exact (mul_eq_zero.mp hqz).elim (fun h ↦ False.elim (hnz h)) fun h ↦ by rw [h, mul_zero]
  have hdiff : U.1ᴴ * diagonal d_avg * U.1 - (X - 1) = U.1ᴴ * Δ * U.1 := by
    have h1 : U.1ᴴ * diagonal (fun _ : Fin D ↦ (1 : ℂ)) * U.1 = 1 := by
      rw [Matrix.diagonal_one, Matrix.mul_one, u_cs1 U]
    have hsub : Δ = diagonal d_avg - (D_c - diagonal (fun _ ↦ (1 : ℂ))) := by
      dsimp only [Δ, D_c]
      rw [← Matrix.diagonal_sub, ← Matrix.diagonal_sub]
    rw [hX_eq, ← h1, hsub]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
  refine sub_eq_zero.mp ?_
  rw [← Matrix.sub_mul, hdiff, m_assoc, m_assoc, hΔ_zero, Matrix.mul_zero]
theorem dg_s4 {D : ℕ} (d_t d_f : Fin D → ℂ) : (diagonal d_t + diagonal d_t) + (diagonal d_f +
    diagonal d_f) = (4 : ℂ) • diagonal (fun z ↦ (1 / 2 : ℂ) * (d_f z + d_t z)) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul]; ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply_ne _ hij, add_zero, smul_zero]
private theorem s4_fp (qft : FullSysQft654Bundle) (hqft : qft.uQft654 = qft64Ideal654Unitary)
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons)) :
    (∑ x : HeadSupportIdx true, ((pos80Slot4Scale * pos80IdealDist true (pos80WitnessOf true
      (Sum.inl x)) : ℝ) : ℂ) •
    blkSm80 qft cfg (pos80WitnessOf true (Sum.inl x))) * fermionicProjector spinUp = s4HR *
      fermionicProjector spinUp := by
  let P := fermionicProjector spinUp
  let blkSm := blkSm80 qft cfg
  have hinner (c : ℂ) (b0 : Fin 8) (nuc : Fin 1) (anc : Fin 218) (k : Fin 56) (pid : Fin 6) (sm :
    Fin 8) : (∑ th : Bool, ∑ rj : Bool,
      c • (blkSm (headWitnessPayload80 b0.val nuc.val anc.val k pid sm th rj) * P)) = c • (4 : ℂ) •
        ((veePairAt (nyqP8 b0) (pos24HeadFine k pid sm) anc - 1) * P) := by
    rw [Nat.lt_one_iff.mp nuc.isLt]
    simp_rw [← Finset.smul_sum, ← Finset.sum_mul]
    refine congrArg (c • ·) ?_
    let dH := pos24HeadFine k pid sm
    let b₀ := nyqP8 b0
    let b₁ := ancPar b₀ dH
    let U := s4CU b₀ b₁ anc
    let d_th (th : Bool) (z : SysIdx) : ℂ :=
      if zeroParityThreshExp false th (proj38ZeroBit (s4H0 b₀ dH z))
        (proj38OddXorZeroBit (s4H0 b₀ dH z)) then (-1 : ℂ) else 1
    let d_avg (z : SysIdx) : ℂ := (1 / 2 : ℂ) * (d_th false z + d_th true z)
    have hblk (th rj : Bool) : blkSm (headWitnessPayload80 b0.val 0 anc.val k pid sm th rj) = U.1ᴴ *
      diagonal (d_th th) * U.1 :=
      bs_cc_mt qft hqft cfg _ b₀ b₁ anc (hw_mt b0 anc k pid sm th rj) (d_th th) fun z ↦ by
        dsimp only [d_th]
        rw [pp_hw]
    simp_rw [hblk, Fintype.sum_bool]
    have hsum4 : (U.1ᴴ * diagonal (d_th true) * U.1 + U.1ᴴ * diagonal (d_th true) * U.1) +
        (U.1ᴴ * diagonal (d_th false) * U.1 + U.1ᴴ * diagonal (d_th false) * U.1) = (4 : ℂ) • (U.1ᴴ
          * diagonal d_avg * U.1) := by
      calc (U.1ᴴ * diagonal (d_th true) * U.1 + U.1ᴴ * diagonal (d_th true) * U.1) +
            (U.1ᴴ * diagonal (d_th false) * U.1 + U.1ᴴ * diagonal (d_th false) * U.1)
        _ = U.1ᴴ * ((diagonal (d_th true) + diagonal (d_th true)) +
              (diagonal (d_th false) + diagonal (d_th false))) * U.1 := by
            simp only [Matrix.mul_add, Matrix.add_mul]
        _ = (4 : ℂ) • (U.1ᴴ * diagonal d_avg * U.1) := by
            rw [dg_s4 (d_th true) (d_th false), Matrix.mul_smul, Matrix.smul_mul]
    rw [hsum4, Matrix.smul_mul]
    refine congrArg ((4 : ℂ) • ·) ?_
    have hint := sc_di b₀ dH anc
    dsimp only at hint
    dsimp only [U, b₁]
    refine dg_cz (s4CU b₀ (ancPar b₀ dH) anc) _ P (fun z ↦ (s4H0 b₀ dH z).card) d_avg hint
      (singleAnchorPairOp_cubic_mul_fermionicProjector_zero (fun y₀ ↦ (ancTgt y₀ b₀ dH).1) anc
        spinUp (veeSubGridKet_orthonormal b₀) (veeSubGridKet_norm_sq b₁)) fun z hcard ↦ ?_
    simpa only [Nat.min_eq_left hcard] using
      proj38_zeroParity_slot4_pauliCap_eq (s4H0 b₀ dH z) hcard
  have htot_ne : (pos80Slot4TotNat : ℝ) ≠ 0 := pos80Slot4TotNat_cast_ne_zero
  have hw_eq (k : Fin 56) : (pos80Slot4Scale * ((pos24HeadWeight56 k : ℝ) / (8 * 218 * 48 * 2 * 2 *
    pos80Slot4TotNat)) : ℝ) * 4 =
      (1 / 128 : ℝ) * (1 / 48 : ℝ) * ((pos24HeadWeight56 k : ℝ) / 2 ^ 30) := by
    unfold pos80Slot4Scale
    field_simp [htot_ne]
    ring
  change (∑ x : HeadSupportIdx true, ((pos80Slot4Scale * pos80IdealDist true (pos80WitnessOf
    true (Sum.inl x)) : ℝ) : ℂ) • blkSm (pos80WitnessOf true (Sum.inl x))) * P = s4HR * P
  rw [Finset.sum_mul]
  dsimp only [HeadSupportIdx, ite_true]
  simp only [Fintype.sum_prod_type, pos80WitnessOf_eval_head, ↓reduceIte]
  dsimp only [pos80WitnessOf]
  simp_rw [Matrix.smul_mul, hinner]
  have h1 (b0 : Fin 8) : (∑ nuc : Fin 1, ∑ anc : Fin 218, ∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm : Fin 8,
    ((pos80Slot4Scale * ((pos24HeadWeight56 k : ℝ) /
      (8 * 218 * 48 * 2 * 2 * pos80Slot4TotNat)) : ℝ) : ℂ) • (4 : ℂ) • ((veePairAt (nyqP8 b0)
        (pos24HeadFine k pid sm) anc - 1) * P)) =
      ((1 / 128 : ℝ) : ℂ) • ∑ d : NyqFine3D128, (kHead128 w128DualQ30 pos24CutNyq d : ℂ) • ((∑ anc :
        Fin 218, (veePairAt (nyqP8 b0) d anc - 1)) * P) := by
    rw [Fintype.sum_unique]
    let F (d : NyqFine3D128) : SysOp :=
      (∑ anc : Fin 218, (veePairAt (nyqP8 b0) d anc - 1)) * P
    have hswap : (∑ anc : Fin 218, ∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm : Fin 8, ((pos80Slot4Scale *
      ((pos24HeadWeight56 k : ℝ) /
        (8 * 218 * 48 * 2 * 2 * pos80Slot4TotNat)) : ℝ) : ℂ) • (4 : ℂ) • ((veePairAt (nyqP8 b0)
          (pos24HeadFine k pid sm) anc - 1) * P)) =
        ((1 / 128 : ℝ) : ℂ) • ((1 / 48 : ℝ) : ℂ) • ∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm : Fin 8,
          (((pos24HeadWeight56 k : ℝ) / 2 ^ 30 : ℝ) : ℂ) •
        F (pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 218)))]
      simp only [Finset.smul_sum, smul_smul, F, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun pid _ ↦
        Finset.sum_congr rfl fun sm _ ↦ Finset.sum_congr rfl fun anc _ ↦ congrArg (· • _) ?_
      have hc := congrArg (Complex.ofReal : ℝ → ℂ) (hw_eq k)
      push_cast at hc ⊢
      linear_combination hc
    rw [hswap, pos24_oh_head_sum_eq F, smul_smul (((1 / 48 : ℝ) : ℂ)) (48 : ℂ),
      show (((1 / 48 : ℝ) : ℂ) * (48 : ℂ)) = 1 from by
        exact_mod_cast (one_div_mul_cancel (by positivity : (48 : ℝ) ≠ 0)),
      one_smul]
  trans (∑ b0 : Fin 8, ((1 / 128 : ℝ) : ℂ) • ∑ d : NyqFine3D128,
    (kHead128 w128DualQ30 pos24CutNyq d : ℂ) •
      ((∑ anc : Fin 218, (veePairAt (nyqP8 b0) d anc - 1)) * P))
  · exact Finset.sum_congr rfl fun b0 _ ↦ h1 b0
  rw [← Finset.smul_sum,
    Equiv.sum_comp nyqP8 (fun b₀ ↦ ∑ d : NyqFine3D128,
      (kHead128 w128DualQ30 pos24CutNyq d : ℂ) •
        ((∑ anc : Fin 218, (veePairAt b₀ d anc - 1)) * P))]
  unfold s4HR
  rw [Matrix.smul_mul, Finset.sum_mul]
  refine congrArg (((1 / 128 : ℝ) : ℂ) • ·) (Finset.sum_congr rfl fun b₀ _ ↦ ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun d _ ↦ (Matrix.smul_mul _ _ _).symm
theorem it_f2 (u : Fin 2) : (if decide (u = 1) then (1 : ℕ) else 0) = u.val := by
  revert u; decide
theorem td_m2 (y₀ y₁ : Fin 64) (u₀ p : Fin 2) : ((2 * y₀.val + u₀.val + 128 - (2 * y₁.val +
    Nat.xor u₀.val p.val)) % 128) % 2 = p.val := by
  have hy0 := y₀.isLt
  have hy1 := y₁.isLt
  fin_cases u₀ <;> fin_cases p <;> (dsimp; omega)
private theorem ny_s (d : NyqFine3D128) (w : Fin 3) : ((nyq3D.symm d).2 w).val = (d w).val % 2 := by
  have h := congrArg (fun x ↦ (x w).val) (nyq3D.apply_symm_apply d)
  rw [nyq128Equiv3D_val] at h
  have hb := ((nyq3D.symm d).2 w).isLt
  omega
private theorem ap_z0 (b₀ dp : NyqParity3D) (dy : NyqGrid3D64) : ancPar b₀ (nyq3D (dy, dp)) =
    ancPar b₀ (nyq3D (0, dp)) :=
  funext fun w ↦ Fin.ext (by
    dsimp only [ancPar]
    rw [ap_x, ap_x, ← ny_s, ← ny_s, nyq3D.symm_apply_apply, nyq3D.symm_apply_apply])
theorem tw_mt (b0 : Fin 8) (anc : Fin 218) (part : Fin 217) (dp : Fin 8)
    (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool) :
    let p80 := tailWitnessPayload80 b0.val 0 anc.val part.val dp keep.val th rj
    let b₀ := nyqP8 b0
    let dp_nyq := nyqP8 dp
    pB0 p80 = b₀ ∧ pB1 p80 = ancPar b₀ (nyq3D (0, dp_nyq)) ∧
      bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)) = anc.val := by
  intro p80 b₀ dp_nyq
  refine ⟨funext fun w ↦ Fin.ext ?_, funext fun w ↦ Fin.ext ?_, ?_⟩
  · dsimp only [pB0]
    have hp : p80 (pos80SubIdx 3 3 (by decide) w) = z2BitOfNat b0.val w.val := by
      dsimp only [p80, tailWitnessPayload80]
      fin_cases w <;> rfl
    rw [hp, z2BitOfNat_val, f8_n]
  · dsimp only [pB1, ancPar]
    have hp : p80 ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩ = z2BitOfNat (Nat.xor b0.val dp.val)
      w.val := by
      dsimp only [p80, tailWitnessPayload80]
      fin_cases w <;> rfl
    rw [hp, z2BitOfNat_val, nat_xor_fin8_bit, f8_n, f8_n, ap_x,
      show (nyq3D (0, dp_nyq) w).val % 2 = (dp_nyq w).val by
        rw [← ny_s, nyq3D.symm_apply_apply]]
  · rw [show (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j)) =
      fun j : Fin 8 ↦ z2BitOfNat anc.val j.val from funext fun j ↦ by
        dsimp only [p80, tailWitnessPayload80]
        fin_cases j <;> rfl]
    exact bitsVal_z2BitOfNat_of_lt (lt_trans anc.isLt (by decide))
def s4TD (b₀ b₁ : NyqParity3D) (part : Fin 217) (z : SysIdx) : FineCoord128 :=
  fun w ↦ ⟨(2 * (sCd z 0 w).val + (b₀ w).val + 128 -
    (2 * (sCd z ⟨part.val + 1, Nat.succ_lt_succ part.isLt⟩ w).val + (b₁ w).val)) % 128,
    Nat.mod_lt _ (by omega)⟩
private theorem cb_b1_dec (p80 : Pay80) (z : SysIdx) {b₁ : NyqParity3D} (hmt : pB1 p80 =
    b₁) (w : Fin 3) :
    parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) (cBeta true p80 z) w = decide (b₁ w =
      1) := by
  refine z2_beq1_eq_fin2 ?_
  have hw_p : rCosetB1 (QRegExt.ofFin posCoreWires) w = rPosSubLocal ⟨w.val, Nat.lt_trans w.isLt
    (by decide)⟩ :=
    Fin.ext (by
      change 3954 + (0 + w.val) = 3954 + w.val
      omega)
  change (cBeta true p80 z (rCosetB1 (QRegExt.ofFin posCoreWires) w)).val = (b₁ w).val
  rw [hw_p, cB_pay]
  exact congrArg (fun f ↦ (f w).val) hmt
private theorem pp_tw (b0 : Fin 8) (anc : Fin 218) (part : Fin 217) (dp : Fin 8)
    (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool) (z : SysIdx) :
    let p80 := tailWitnessPayload80 b0.val 0 anc.val part.val dp keep.val th rj
    let b₀ := nyqP8 b0
    let b₁ := ancPar b₀ (nyq3D (0, nyqP8 dp))
    let rOrbit := tetRank65 (canonTriple128 (s4TD b₀ b₁ part z))
    posPhaseBit true tSgn tMag30 (cBeta true p80 z) =
      if keep.val < (tMag30 rOrbit).val then tSgn rOrbit else rj := by
  intro p80 b₀ b₁ rOrbit
  let rCore := QRegExt.ofFin posCoreWires
  let β := cBeta true p80 z
  have hw2 : β (wSlot2Core rCore) = 0 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hw1 : β (wSlot1Core rCore) = 0 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hw0 : β (wSlot0Core rCore) = 1 := coreBetaOf_mid true p80 z _ (by decide) (by decide)
  have hwSub : β (wSubReject rCore) = 0 := (cB_pay true p80 z ⟨62, by decide⟩).trans rfl
  have hwHead : β (wIsHead rCore) = 0 := (cB_pay true p80 z ⟨30, by decide⟩).trans rfl
  have hwRj : (β (wRejectZero rCore) == 1) = rj := by
    rw [show β (wRejectZero rCore) = if rj then 1 else 0 from cB_pay true p80 z ⟨79, by decide⟩]
    cases rj <;> rfl
  have hrAnc : regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) β = anc.val :=
    cb_anc_val p80 z (tw_mt b0 anc part dp keep th rj).2.2
  have hslot : ∀ e : Fin 218, slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β =
    sCd z e :=
    ss_cb true p80 z
  have hrPart : regVal (rPartnerIdx rCore) β = part.val := by
    change bitsVal (fun j : Fin 8 ↦
      cBeta true p80 z (rPosSubLocal (pos80SubIdx 22 8 (by decide) j))) = part.val
    simp only [cB_pay]
    rw [show (fun j : Fin 8 ↦ p80 (pos80SubIdx 22 8 (by decide) j)) =
      fun j : Fin 8 ↦ z2BitOfNat part.val j.val from funext fun j ↦ by
        dsimp only [p80, tailWitnessPayload80]
        fin_cases j <;> rfl]
    exact bitsVal_z2BitOfNat_of_lt (lt_trans part.isLt (by decide))
  have hrKeep : regVal (rTailKeep30 rCore) β = keep.val := by
    change bitsVal (fun j : Fin 30 ↦
      cBeta true p80 z (rPosSubLocal (pos80SubIdx 32 30 (by decide) j))) = keep.val
    simp only [cB_pay]
    rw [show (fun j : Fin 30 ↦ p80 (pos80SubIdx 32 30 (by decide) j)) =
      fun j : Fin 30 ↦ z2BitOfNat keep.val j.val from funext fun j ↦ by
        have hj := j.isLt
        dsimp only [p80, tailWitnessPayload80, pos80SubIdx]
        simp only [show ¬(32 + j.val < 3) by omega, show ¬(32 + j.val < 6) by omega,
          show ¬(32 + j.val < 14) by omega, show ¬(32 + j.val < 22) by omega,
          show ¬(32 + j.val < 30) by omega,
          show (32 + j.val == 30) = false from beq_eq_false_iff_ne.mpr (by omega),
          show (32 + j.val == 31) = false from beq_eq_false_iff_ne.mpr (by omega),
          show 32 + j.val < 62 by omega, show 32 + j.val - 32 = j.val by omega,
          ↓reduceIte, Bool.false_eq_true]]
    exact bitsVal_z2BitOfNat_of_lt (lt_of_lt_of_le keep.isLt (tailSpan8_lt_two_pow_30 dp))
  have hB0 (w : Fin 3) : (if parity3OfReg (rCosetB0 rCore) β w then (1 : ℕ) else 0) = (b₀ w).val :=
    by
    rw [cb_b0_dec p80 z (tw_mt b0 anc part dp keep th rj).1 w, it_f2]
  have hB1 (w : Fin 3) : (if parity3OfReg (rCosetB1 rCore) β w then (1 : ℕ) else 0) = (b₁ w).val :=
    by
    rw [cb_b1_dec p80 z (tw_mt b0 anc part dp keep th rj).2.1 w, it_f2]
  have hHead0 : headPhaseBitSpec β = false := by
    unfold headPhaseBitSpec
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, show ((0 : ZMod 2) == 1) = false from rfl,
      Bool.and_false, Bool.not_false, ↓reduceIte]
  have hTail : tailAndSlackPhaseBitSpec true tSgn tMag30 β = if keep.val < (tMag30 rOrbit).val then
    tSgn rOrbit else rj := by
    unfold tailAndSlackPhaseBitSpec
    dsimp only [rCore] at hB0 hB1
    simp only [rCore, hw2, hw1, hw0, hwSub, hwHead, hwRj, hrAnc, anc.isLt, hrPart, part.isLt,
      hrKeep, show ((0 : ZMod 2) == 1) = false from rfl, show ((1 : ZMod 2) == 1) = true from rfl,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true, IsEmpty.forall_iff, imp_self,
        decide_true, Bool.and_self, hB0, hB1, hslot]
    have horb : ∀ (hp_part : part.val % 217 + 1 < 218) (hp_mod : ∀ w : Fin 3, (2 * (sCd z 0
        w).val + (b₀ w).val + 128 - (2 * (sCd z ⟨part.val % 217 + 1, hp_part⟩ w).val + (b₁
        w).val)) % 128 < 128), tetRank65 (canonTriple128 fun w ↦ ⟨(2 * (sCd z 0 w).val + (b₀
        w).val + 128 - (2 * (sCd z ⟨part.val % 217 + 1, hp_part⟩ w).val + (b₁ w).val)) % 128,
        hp_mod w⟩) = rOrbit := fun hp_part _ ↦ congrArg (fun d ↦ tetRank65 (canonTriple128 d))
      (funext fun w ↦ Fin.ext (by
        dsimp only [s4TD]
        rw [show (⟨part.val % 217 + 1, hp_part⟩ : Fin 218) =
          ⟨part.val + 1, Nat.succ_lt_succ part.isLt⟩ from
          Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt part.isLt])]))
    rw [horb]
  unfold posPhaseBit
  change Bool.xor (headPhaseBitSpec β) (tailAndSlackPhaseBitSpec true tSgn tMag30 β) = _
  rw [hHead0, hTail, Bool.false_xor]
private theorem tm_hs (idx : Fin orbitCount47905) : (tMag30 idx).val ≤ pos24HalfSpanQb
    (orbitParityWeight idx) := by
  dsimp only [tMag30]
  exact pos24TailMag30_le_halfSpan idx
theorem td_pr (b0 dp : Fin 8) (part : Fin 217) (z : SysIdx) :
    let b₀ := nyqP8 b0
    let dp_nyq := nyqP8 dp
    let b₁ := ancPar b₀ (nyq3D (0, dp_nyq))
    let s : Fin 218 := ⟨part.val + 1, by have := part.isLt; omega⟩
    let dTail := s4TD b₀ b₁ part z
    (nyq3D.symm dTail).2 = dp_nyq ∧
      (tMag30 (tetRank65 (canonTriple128 dTail))).val ≤ pos24TailSpan8 dp ∧
      (ancTgt (sCd z 0) b₀ dTail).1 = sCd z s := by
  intro b₀ dp_nyq b₁ s dTail
  have hpar : (nyq3D.symm dTail).2 = dp_nyq := funext fun w ↦ Fin.ext (by
    rw [ny_s]
    dsimp only [dTail, s4TD, b₁, ancPar]
    rw [ap_x, ← ny_s, nyq3D.symm_apply_apply]
    exact td_m2 (sCd z 0 w) (sCd z s w) (b₀ w) (dp_nyq w))
  refine ⟨hpar, ?_, funext fun w ↦ ?_⟩
  · have hw_eq : orbitParityWeight (tetRank65 (canonTriple128 dTail)) =
        ⟨(dp.val % 2) + ((dp.val / 2) % 2) + ((dp.val / 4) % 2), by omega⟩ := Fin.ext (by
      rw [(subGridWeight128_eq_orbit dTail).symm.trans (subGridWeight128_eq_nyqParity dTail), hpar,
        subGridParityWeight3_nyqParityToBool]
      have b0_eq := f8_n dp 0
      have b1_eq := f8_n dp 1
      have b2_eq := f8_n dp 2
      dsimp only [dp_nyq] at *
      rw [← b0_eq, ← b1_eq, ← b2_eq]
      dsimp
      omega)
    rw [show pos24TailSpan8 dp = pos24HalfSpanQb (orbitParityWeight (tetRank65 (canonTriple128
      dTail))) from congrArg pos24HalfSpanQb hw_eq.symm]
    exact tm_hs (tetRank65 (canonTriple128 dTail))
  · have hdiff := (tailFineDiff1D_eq (sCd z 0 w) (sCd z s w)
      (decide (b₀ w = 1)) (decide (b₁ w = 1))).1
    rw [it_d2 (b₀ w), show (⟨(2 * (sCd z 0 w).val + (if decide (b₀ w = 1) then 1 else 0) + 128 -
        (2 * (sCd z s w).val + (if decide (b₁ w = 1) then 1 else 0))) % 128,
      Nat.mod_lt _ (by omega)⟩ : Fin 128) = dTail w from
      Fin.ext (by dsimp only [dTail, s4TD]; rw [it_f2, it_f2])] at hdiff
    exact hdiff
theorem sum_fin_lt_const {span mag : ℕ} (h : mag ≤ span) (c : ℂ) : (∑ k : Fin span, if k.val < mag
    then c else 0) = (mag : ℂ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  have hbij : (Finset.univ : Finset (Fin mag)).map ⟨fun i : Fin mag ↦ (⟨i.val, lt_of_lt_of_le i.isLt
    h⟩ : Fin span),
      fun i j hij ↦ Fin.ext (by simpa using congrArg Fin.val hij)⟩ = Finset.univ.filter (fun k : Fin
        span ↦ k.val < mag) := by
    ext k
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
      Finset.mem_filter]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ i.isLt, fun hk ↦ ⟨⟨k.val, hk⟩, Fin.ext rfl⟩⟩
  rw [← hbij, Finset.card_map, Finset.card_fin]
theorem su_tk {span : ℕ} (sign : Bool) {mag : ℕ} (hmag : mag ≤ span) : (∑ keep : Fin span,
    ∑ _th : Bool, ∑ rj : Bool,
    (if (if keep.val < mag then sign else rj) then (-1 : ℂ) else 1)) = (4 : ℂ) * ((if sign then
      (-1 : ℝ) else 1 : ℝ) * (mag : ℝ) : ℂ) := by
  have hinner (keep : Fin span) : (∑ _th : Bool, ∑ rj : Bool, (if (if keep.val < mag then sign else
    rj) then (-1 : ℂ) else 1)) =
      if keep.val < mag then (4 : ℂ) * ((if sign then (-1 : ℝ) else 1 : ℝ) : ℂ) else 0 := by
    simp only [Fintype.sum_bool]
    by_cases hk : keep.val < mag
    · cases sign <;> simp [hk] <;> norm_num
    · simp [hk]
  simp_rw [hinner]
  rw [sum_fin_lt_const hmag]
  push_cast
  ring
theorem su_e0 {M : Type*} [AddCommMonoid M] (f : Fin 218 → M) :
    (∑ part : Fin 217, f ⟨part.val + 1, by have := part.isLt; omega⟩) =
      ∑ s ∈ Finset.univ.erase (0 : Fin 218), f s := by
  refine Finset.sum_bij (fun (part : Fin 217) _ ↦ (⟨part.val + 1, by have := part.isLt; omega⟩ : Fin
    218))
    (fun part _ ↦ Finset.mem_erase.mpr ⟨fun h ↦ by
      have := congrArg Fin.val h; dsimp at this; omega, Finset.mem_univ _⟩)
    (fun p₁ _ p₂ _ h ↦ Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
    (fun s hs ↦ ?_)
    (fun _ _ ↦ rfl)
  have hs0 : s.val ≠ 0 := fun h ↦ (Finset.mem_erase.mp hs).1 (Fin.ext h)
  have hslt : s.val - 1 < 217 := by have := s.isLt; omega
  exact ⟨⟨s.val - 1, hslt⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
theorem st_tr (qft : FullSysQft654Bundle) (hqft : qft.uQft654 = qft64Ideal654Unitary) (cfg :
    Configuration) : (∑ y : TailSupportIdx true,
    ((pos80Slot4Scale * pos80IdealDist true (pos80WitnessOf true (Sum.inr y)) : ℝ) : ℂ) •
    (smToTwosSysUnitary.1 * sysBlk hkF (pos24ConjCore80 qft cfg).1 true (pos80WitnessOf true
      (Sum.inr y)) * smToTwosSysUnitary.1)) = s4TR := by
  let blkSm := blkSm80 qft cfg
  let kt (d : NyqFine3D128) : ℂ :=
    (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq d : ℂ)
  let c30 : ℂ := ((4 * (2 : ℝ) ^ 30 : ℝ) : ℂ)
  have hkeep_sum (b0 : Fin 8) (anc : Fin 218) (part : Fin 217) (dp : Fin 8) : (∑ keep : Fin
    (pos24TailSpan8 dp), ∑ th : Bool, ∑ rj : Bool,
      blkSm (tailWitnessPayload80 b0.val 0 anc.val part.val dp keep.val th rj)) =
      c30 • ((s4CU (nyqP8 b0) (ancPar (nyqP8 b0) (nyq3D (0, nyqP8 dp))) anc).1ᴴ *
        (∑ dy : NyqGrid3D64, kt (nyq3D (dy, nyqP8 dp)) •
      diagonal (fun z : SysIdx ↦ if sCd z ⟨part.val + 1, Nat.succ_lt_succ part.isLt⟩ = (ancTgt (sCd
        z 0) (nyqP8 b0) (nyq3D (dy, nyqP8 dp))).1 then (1 : ℂ) else 0)) *
      (s4CU (nyqP8 b0) (ancPar (nyqP8 b0) (nyq3D (0, nyqP8 dp))) anc).1) := by
    let b₀ := nyqP8 b0
    let dp_nyq := nyqP8 dp
    let b₁ := ancPar b₀ (nyq3D (0, dp_nyq))
    let U := s4CU b₀ b₁ anc
    let s : Fin 218 := ⟨part.val + 1, Nat.succ_lt_succ part.isLt⟩
    let d_k (keep : Fin (pos24TailSpan8 dp)) (_th rj : Bool) (z : SysIdx) : ℂ :=
      let rOrbit := tetRank65 (canonTriple128 (s4TD b₀ b₁ part z))
      if (if keep.val < (tMag30 rOrbit).val then tSgn rOrbit else rj) then (-1 : ℂ) else 1
    have hblk_one (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool) : blkSm (tailWitnessPayload80
      b0.val 0 anc.val part.val dp keep.val th rj) = U.1ᴴ * diagonal (d_k keep th rj) * U.1 :=
      bs_cc_mt qft hqft cfg _ b₀ b₁ anc (tw_mt b0 anc part dp keep th rj) (d_k keep th rj)
        fun z ↦ by
          dsimp only [d_k]
          rw [pp_tw]
    simp_rw [hblk_one, ← Finset.sum_mul, ← Finset.mul_sum]
    have hdiag_pull : (∑ keep : Fin (pos24TailSpan8 dp), ∑ th : Bool, ∑ rj : Bool, diagonal (d_k
      keep th rj)) = c30 • ∑ dy : NyqGrid3D64, kt (nyq3D (dy, dp_nyq)) • diagonal (fun z : SysIdx ↦
        if sCd z s = (ancTgt (sCd z 0) b₀ (nyq3D (dy, dp_nyq))).1 then (1 : ℂ) else 0) := by
      ext z' z
      by_cases hzz : z' = z
      · subst hzz
        simp only [Matrix.sum_apply, diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
        have hprops := td_pr b0 dp part z'
        let dTail := s4TD b₀ b₁ part z'
        let rOrbit := tetRank65 (canonTriple128 dTail)
        rw [su_tk (tSgn rOrbit) hprops.2.1]
        have h4 : (4 : ℂ) * ((if tSgn rOrbit then (-1 : ℝ) else 1 : ℝ) * (tMag30 rOrbit : ℝ) : ℂ) =
          c30 * kt dTail := by
          have hr : (4 : ℝ) * ((if tSgn rOrbit then (-1 : ℝ) else 1) * (tMag30 rOrbit : ℝ)) = (4 *
            (2 : ℝ) ^ 30) * kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq dTail := by
            rw [← (pos24_shell_cert dTail).1]
            ring
          have hc := congrArg (Complex.ofReal : ℝ → ℂ) hr
          dsimp only [c30, kt]
          push_cast at hc ⊢
          exact hc
        rw [h4]
        refine congrArg (c30 * ·) ?_
        let dy₀ : NyqGrid3D64 := (nyq3D.symm dTail).1
        have hdTail_eq : dTail = nyq3D (dy₀, dp_nyq) := by
          conv_lhs => rw [← nyq3D.apply_symm_apply dTail]
          exact congrArg nyq3D (Prod.ext rfl hprops.1)
        rw [Finset.sum_eq_single_of_mem dy₀ (Finset.mem_univ dy₀) fun dy _ hne ↦ ?_]
        · have hhit : sCd z' s = (ancTgt (sCd z' 0) b₀ (nyq3D (dy₀, dp_nyq))).1 :=
            hdTail_eq ▸ hprops.2.2.symm
          simp only [hhit, ↓reduceIte, mul_one, hdTail_eq]
        · have hne_tgt : sCd z' s ≠ (ancTgt (sCd z' 0) b₀ (nyq3D (dy, dp_nyq))).1 :=
            fun heq ↦ hne ((anchorSubTargetEquiv b₀ dp_nyq (sCd z' 0)).injective (by
              change (ancTgt (sCd z' 0) b₀ (nyq3D (dy₀, dp_nyq))).1 =
                (ancTgt (sCd z' 0) b₀ (nyq3D (dy, dp_nyq))).1
              rw [← hdTail_eq, hprops.2.2, heq])).symm
          simp only [hne_tgt, ↓reduceIte, mul_zero]
      · simp only [Matrix.sum_apply, diagonal_apply_ne _ hzz, Matrix.smul_apply,
          Finset.sum_const_zero, smul_zero]
    rw [hdiag_pull, Matrix.mul_smul, Matrix.smul_mul]
  have hpart_sum (b0 : Fin 8) (anc : Fin 218) (dp : Fin 8) : (∑ part : Fin 217, ∑ keep : Fin
    (pos24TailSpan8 dp), ∑ th : Bool, ∑ rj : Bool,
      blkSm (tailWitnessPayload80 b0.val 0 anc.val part.val dp keep.val th rj)) = c30 • ∑ dy :
        NyqGrid3D64, kt (nyq3D (dy, nyqP8 dp)) • veePairAt (nyqP8 b0) (nyq3D (dy, nyqP8 dp)) anc :=
          by
    rw [Finset.sum_congr rfl fun part _ ↦ hkeep_sum b0 anc part dp,
      ← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    refine congrArg (c30 • ·) ?_
    rw [Finset.sum_comm, Matrix.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun dy _ ↦ ?_
    let d := nyq3D (dy, nyqP8 dp)
    simp_rw [← Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]
    refine congrArg (kt d • ·) ?_
    have hdiag_card : (∑ part : Fin 217, diagonal (fun z : SysIdx ↦ if sCd z ⟨part.val + 1,
      Nat.succ_lt_succ part.isLt⟩ =
        (ancTgt (sCd z 0) (nyqP8 b0) d).1 then (1 : ℂ) else 0)) = diagonal (fun z : SysIdx ↦
          ((s4H0 (nyqP8 b0) d z).card : ℂ)) := by
      trans (∑ s ∈ Finset.univ.erase (0 : Fin 218),
        diagonal (fun z : SysIdx ↦
          if sCd z s = (ancTgt (sCd z 0) (nyqP8 b0) d).1 then (1 : ℂ) else 0))
      · exact su_e0 (fun s : Fin 218 ↦ diagonal (fun z : SysIdx ↦
          if sCd z s = (ancTgt (sCd z 0) (nyqP8 b0) d).1 then (1 : ℂ) else 0))
      ext z' z
      by_cases hzz : z' = z
      · subst hzz
        simp only [Matrix.sum_apply, diagonal_apply_eq, s4H0, Finset.card_eq_sum_ones, Nat.cast_sum,
          Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      · simp only [Matrix.sum_apply, diagonal_apply_ne _ hzz, Finset.sum_const_zero]
    rw [hdiag_card]
    have hconj := sc_hc (nyqP8 b0) d anc
    dsimp only [d] at hconj ⊢
    conv at hconj =>
      lhs
      rw [ap_z0 (nyqP8 b0) (nyqP8 dp) dy]
    exact hconj
  have htot_ne : (pos80Slot4TotNat : ℝ) ≠ 0 := pos80Slot4TotNat_cast_ne_zero
  have hw_tail : (pos80Slot4Scale * ((1 : ℝ) / (8 * 218 * 2 * 2 * pos80Slot4TotNat)) : ℝ) * (4 *
    (2 : ℝ) ^ 30) = (1 / 128 : ℝ) := by
    unfold pos80Slot4Scale
    field_simp [htot_ne]
    ring
  change (∑ y : TailSupportIdx true, ((pos80Slot4Scale * pos80IdealDist true (pos80WitnessOf
    true (Sum.inr y)) : ℝ) : ℂ) • blkSm (pos80WitnessOf true (Sum.inr y))) = s4TR
  dsimp only [TailSupportIdx, ite_true]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma, pos80WitnessOf_eval_tail, ↓reduceIte]
  dsimp only [pos80WitnessOf]
  simp_rw [← Finset.smul_sum]
  have h1 (b0 : Fin 8) : (∑ nuc : Fin 1, ∑ anc : Fin 218, ∑ part : Fin 217, ∑ dp : Fin 8,
    ∑ keep : Fin (pos24TailSpan8 dp), ∑ th : Bool, ∑ rj : Bool,
      blkSm (tailWitnessPayload80 b0.val nuc.val anc.val part.val dp keep.val th rj)) = c30 • ∑ d :
        NyqFine3D128, kt d • ∑ anc : Fin 218, veePairAt (nyqP8 b0) d anc := by
    rw [Fintype.sum_unique, show (default : Fin 1).val = 0 from rfl]
    let b₀ := nyqP8 b0
    have hswap : (∑ anc : Fin 218, ∑ part : Fin 217, ∑ dp : Fin 8, ∑ keep : Fin (pos24TailSpan8 dp),
      ∑ th : Bool, ∑ rj : Bool,
        blkSm (tailWitnessPayload80 b0.val 0 anc.val part.val dp keep.val th rj)) = ∑ anc : Fin 218,
          ∑ dp : Fin 8, c30 • ∑ dy : NyqGrid3D64,
        kt (nyq3D (dy, nyqP8 dp)) • veePairAt b₀ (nyq3D (dy, nyqP8 dp)) anc :=
      Finset.sum_congr rfl fun anc _ ↦ by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun dp _ ↦ hpart_sum b0 anc dp
    rw [hswap]
    simp_rw [← Finset.smul_sum]
    rw [Finset.sum_comm]
    refine congrArg (c30 • ·) ?_
    let G (d : NyqFine3D128) : SysOp := kt d • ∑ anc : Fin 218, veePairAt b₀ d anc
    rw [Equiv.sum_comp nyqP8 (fun dp_nyq : NyqParity3D ↦
      ∑ anc : Fin 218, ∑ dy : NyqGrid3D64, kt (nyq3D (dy, dp_nyq)) •
        veePairAt b₀ (nyq3D (dy, dp_nyq)) anc)]
    simp_rw [show ∀ dp_nyq : NyqParity3D, (∑ anc : Fin 218, ∑ dy : NyqGrid3D64,
        kt (nyq3D (dy, dp_nyq)) • veePairAt b₀ (nyq3D (dy, dp_nyq)) anc) =
        ∑ dy : NyqGrid3D64, G (nyq3D (dy, dp_nyq)) from fun dp_nyq ↦ by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun dy _ ↦ Finset.smul_sum.symm]
    rw [Finset.sum_comm,
      ← Fintype.sum_prod_type (fun p : NyqGrid3D64 × NyqParity3D ↦ G (nyq3D p)),
      Equiv.sum_comp nyq3D G]
  trans (((pos80Slot4Scale * ((1 : ℝ) / (8 * 218 * 2 * 2 * pos80Slot4TotNat)) : ℝ) : ℂ) •
    ∑ b0 : Fin 8, c30 • ∑ d : NyqFine3D128, kt d • ∑ anc : Fin 218, veePairAt (nyqP8 b0) d anc)
  · exact congrArg (_ • ·) (Finset.sum_congr rfl fun b0 _ ↦ h1 b0)
  rw [← Finset.smul_sum, smul_smul,
    Equiv.sum_comp nyqP8 (fun b₀ ↦
      ∑ d : NyqFine3D128, kt d • ∑ anc : Fin 218, veePairAt b₀ d anc)]
  unfold s4TR
  refine congrArg (· • _) ?_
  have hc := congrArg (Complex.ofReal : ℝ → ℂ) hw_tail
  dsimp only [c30]
  push_cast at hc ⊢
  exact hc
theorem c4_fp (qft : FullSysQft654Bundle) (hqft : qft.uQft654 = qft64Ideal654Unitary) (cfg :
    Configuration) (spinUp : Finset (Fin numElectrons)) :
    ((pos80Slot4Scale : ℂ) • (smToTwosSysUnitary.1 * coherentSysOp80 qft cfg true (pos80IdealDist
      true) *
    smToTwosSysUnitary.1)) * fermionicProjector spinUp = s4S * fermionicProjector spinUp := by
  let f (p80 : Pay80) (r : ℝ) : SysOp := ((pos80Slot4Scale * r : ℝ) : ℂ) • blkSm80 qft cfg p80
  have hlhs : ((pos80Slot4Scale : ℂ) • (smToTwosSysUnitary.1 * coherentSysOp80 qft cfg true
    (pos80IdealDist true) * smToTwosSysUnitary.1)) = ∑ p80 : Pay80, f p80 (pos80IdealDist true
      p80) := by
    unfold coherentSysOp80
    rw [Matrix.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p80 _ ↦ ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    dsimp only [f, blkSm80, hkF]
    push_cast
    rfl
  rw [hlhs, sum_over_pos80IdealDist_support true f (fun p80 ↦ by simp [f]),
    Fintype.sum_sum_type, Matrix.add_mul]
  dsimp only [f]
  rw [s4_fp qft hqft cfg spinUp, show (∑ x : TailSupportIdx true, ((pos80Slot4Scale * pos80IdealDist
    true (pos80WitnessOf true (Sum.inr x)) : ℝ) : ℂ) •
    blkSm80 qft cfg (pos80WitnessOf true (Sum.inr x))) = s4TR from st_tr qft hqft cfg,
      ← Matrix.add_mul, ← s4_ht]
end ConfigPos24Slot4FermionicBridge
end Pos24Slot4FermionicBridge
end
end ModPos24Slot4FermionicBridge

end QuantumComputation.Specs.StoppingPowerSolution
