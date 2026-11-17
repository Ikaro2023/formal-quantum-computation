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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.HybridStream288
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModPos24Slot2FermionicBridge
@[expose] public section
namespace Pos24Slot2FermionicBridge
open Operator QProg Matrix Real
open SpecsAux.SpecMirror (Configuration IsGridState electronBits fermionicProjector numElectrons
  projectileBits systemQubits)
open SpecsAux.BridgeFermionicComm.SpecInner (basisBits_permElectron div_18_lt_numElectrons
  permElectron permElectronWire permElectronWireFun)
open SpecsAux.DyadicSubgridToeplitz128 (NyqFine3D128 NyqGrid3D64 NyqParity3D kHead128
  kHead128_add_kTail128 kTailShifted128 nyq128Equiv3D nyq128Equiv3D_val shiftedMom3D)
open SpecsAux.DyadicSubgridToeplitz512AndShift (NyqFine3D512 nyq512ProjEquiv3D)
open SpecsAux.FullScaleBESector (AgreesOnFermionicSector)
open BchCubeDecoder (proj38ZeroBit proj38OddXorZeroBit proj38_zeroParity_negated_lcu_eq_min_card
  zeroParityThreshExp)
open CanonRank7Circuit (fineCoordOfReg21)
open Dyadic128CoulombMath (canonTriple128 orbitParityWeight subGridWeight128_eq_orbit tetRank65)
open Dyadic128OrbitTableCert (w128DualQ30)
open DyadicQft64 (dyadicTurn dyadicTurn_zero)
open DyadicQft64WalkCircuit (nyqParity3DEquivFin8 qft64Ideal654Unitary
  qft64Ideal654Unitary_mul_cosetProj_eq_elec3DProd qft64OffsetUnitary3D qft64OffsetUnitary3D_apply
  rElec18In654 u18GridEquiv wSlot2)
open FullSysCatSegmentBridge (FullSysQft654Bundle coreCosetB1Block coreElecCosetB1Block
  fullSysCoreWires)
open MergedVepLeaf4GridPerturbation (tierBB2RawId)
open NuclearTwistAndXor654Concrete (nuclearM48 oneElecNucDiag48 oneElectronPhase48 sysNucDiag48
  uenSubGridKet48)
open NuclearTwistRealizes (barrelActive barrelBitFn coin0Active slot2AxisDelta slot2AxisSum
  slot2GlobalPhase slot2M48Val slot2TotalPhaseExp
  slot2_offsetDiag_eq_smul_sysNucDiag48_conjTranspose slot4TotalPhaseExp
  star_slot2GlobalPhase_mul_self xor32BitFn)
open Pos24MergedVepPrepAndStitch (smToTwosSysUnitary_sa)
open PosSlots24BranchConcrete (axisBitRev6 headPhaseBitSpec parity3OfReg posCoreWires
  posPayloadWires posPhaseBit rAnchorIdx rCosetB0 rCosetB1 rElecSlot rHeadFine21 rNucIdx rPartnerIdx
  rTailKeep30 slotSubGridCoord64 tailAndSlackPhaseBitSpec uPosPhase wHeadThresh wIsHead wRejectZero
  wSlot0Core wSlot1Core wSlot2Core wSubReject)
open PosSlots24MergedVepBound (cfgProjZ512 dite_eq_of_neg dite_eq_of_pos elecFermionicProjector
  elecFermionicProjector_comm_embedMatrix elecFermionicProjector_mul_fermionicProjector matUnit24
  permMatrix_comm_embedMatrix_gen projBasisGen projBasisGen_isHermitian projGridEquiv24 projLift0Gen
  projShift0Gen projSignedMagToTwos24Equiv rProj24_sp smToTwos654SysUnitary_comm_embedMatrix
  smToTwos654SysUnitary_sa smToTwosSysUnitary_eq_proj_mul_elec uProjPlus512SM_3D vepFromSlot2Op
  vepFromSlot2Op_sub vepGen)
open PosSlots24Semantic80Physics (HeadSupportIdx Pos80SupportIdx TailSupportIdx
  bitsVal_z2BitOfNat_of_lt headWitnessPayload80 pos80IdealDist pos80IdealDist_eq_zero_of_not_mem
  pos80SubIdx pos80WitnessOf pos80WitnessOf_eval_head pos80WitnessOf_eval_tail
  sum_over_pos80IdealDist_support sum_pos80IdealDist_eq_one tailSpan8_lt_two_pow_30
  tailWitnessPayload80 z2BitOfNat z2BitOfNat_val)
open PosSlots24SemanticBridge (castUnitaryPow2 pos24ConjCore80 pos24CutNyq pos24HalfSpanQb
  pos24HeadU56 pos24HeadV56 pos24HeadW56 pos24HeadWeight56 pos24MinNyq pos24OhPoint pos24TailMag30
  pos24TailMag30_le_halfSpan pos24TailSign pos24TailSpan8 pos24_22_le_80 pos24_6_le_80
  pos24_core80_eq_twist80 pos24_coreWires80_eq pos24_oh_head_sum_eq pos24_shell_cert
  subGridParityWeight3_nyqParityToBool subGridWeight128_eq_nyqParity sysBlockAtPayloadGen)
open PosSlots24SemanticOracleConcrete80 (PreservesCoreAnc basisOutcomeProjector_compose_local
  coherentSysOp80 coreBetaOf coreBetaOf_lt3948 coreBetaOf_mid coreBetaOf_payload
  coreElecCosetB1_compose_rCoset3 coreElecCosetB1_disjoint_rAncRest83 coreIdxOf coreIdxOf_injective
  embedMatrix_entry_of_agreeOutside embedMatrix_entry_of_not_agreeOutside
  entry_zero_of_comm_basisOutcomeProjector lt_sys_4034 ofFin_embedUnitary_eq pos80Slot2Scale
  pos80Slot2Scale_pos pos80Slot2TotNat qftPreservesCoset3_of_eq_ideal rAncFlag80
  rAncFlag80_basisOutcomeProjector_factor rAncFlag80_wire_ge_3948 rAncRest83 regVal_eq_of_wire_eq
  sysBlockAtPayloadGen_apply sysBlockAtPayloadGen_conj_of_preserves
  sysBlockAtPayloadGen_mul_of_preserves uPosPhase_cast_comm_diagonal
  uTwistParam_cast_comm_highReg_proj)
open PosSlots24TopWrapper (rPosSubLocal)
open SingleAnchorFermionicPauliCap (emb_rEl_mul_pe_sp nSub_cubic_mul_fermionicProjector_zero
  nSub_isHermitian_any nSub_sp nTot_sp op_sp rEl_disjoint_of_ne_sp rEl_sp rk1_sp sum_perm_finset_eq)
open Slot2SingleElecTwistBound (rEl_prod_conj_embed_eq_single)
open Slot2Slot4QuantizedChannelBridge (elecOffsetGridEquiv18 signedMagToOffset6Equiv
  u18AxisSplitEquiv uenMidpointShift veeSubGridKet veeSubGridKet_complete veeSubGridKet_norm_sq)
open Slots01AndGridGuardBridge (signedMagToOffset6_eq_xor32 signedMagToTwos6Perm)
open TwosCompAndWire0Cancel (bitRev6GridEquiv elec654Axes elecAxisField elecAxisField_smToTwos654
  extractIndex_block_val fwdPermUnitary fwdPermUnitary_apply fwdPermUnitary_refl
  fwdPermUnitary_trans karatsubaOffset3D128 karatsubaOffset3D128_apply karatsubaOutPhase3D
  karatsubaOutPhase3D_unit proj3Axes projAxisField projAxisField_smToTwos654 smToTwos654SysPerm
  smToTwos654SysUnitary smToTwosAxisPerm smToTwosSysUnitary)
open TierBClean80Closure (tierBQftFull)
open KaratsubaQft64Matrix (bitRev6Equiv)
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators
section ConfigPos24Slot2FermionicBridge
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 512
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowSlot2Bridge (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
theorem qreg_block_wires_slot2 {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n)
    (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem sum_abs_pos80IdealDist_eq_one (s0 : Bool) :
    (∑ p80 : BitAssignment 80, |pos80IdealDist s0 p80|) = 1 := by
  rw [← sum_pos80IdealDist_eq_one s0]
  refine Finset.sum_congr rfl fun p80 _ ↦ abs_of_nonneg ?_
  by_cases hmem : ∃ w : Pos80SupportIdx s0, pos80WitnessOf s0 w = p80
  · rcases hmem with ⟨⟨_, _, _, _, _, _, _, _⟩ | ⟨_, _, _, _, ⟨_, _⟩, _, _⟩, rfl⟩
    · rw [pos80WitnessOf_eval_head]
      cases s0 <;> positivity
    · rw [pos80WitnessOf_eval_tail]
      cases s0 <;> positivity
  · rw [pos80IdealDist_eq_zero_of_not_mem s0 hmem]
def slotCoord18Equiv : Fin (2 ^ 18) ≃ NyqGrid3D64 := u18GridEquiv.trans bitRev6GridEquiv
def slotCoordSys (z : Fin (2 ^ systemQubits)) (e : Fin 218) : NyqGrid3D64 :=
  slotCoord18Equiv ((rEl_sp e).extractIndex z)
noncomputable def veeBasisMat18 (b : NyqParity3D) : Operator (2 ^ 18) :=
  Matrix.of fun z u ↦ star (veeSubGridKet b (slotCoord18Equiv z) u)
noncomputable def veeBasisUnitary18 (b : NyqParity3D) : Unitary (2 ^ 18) :=
  ⟨veeBasisMat18 b, by
    rw [Matrix.mem_unitaryGroup_iff']
    ext u v
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      veeBasisMat18, Matrix.of_apply, star_star, Matrix.one_apply]
    rw [← Equiv.sum_comp slotCoord18Equiv.symm]
    simp_rw [Equiv.apply_symm_apply]
    exact veeSubGridKet_complete b u v⟩
noncomputable def veeSysProdUnitary (b₁ : NyqParity3D) : Unitary (2 ^ systemQubits) :=
  (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (veeBasisUnitary18 b₁)).prod
theorem list_prod_comm_of_mem {D : ℕ} :
    ∀ (L : List (Unitary D)) (X : Operator D),
      (∀ U ∈ L, U.1 * X = X * U.1) →
      L.prod.1 * X = X * L.prod.1
  | [], _, _ => by simp
  | U :: tail, X, hcomm => by
      simp only [List.prod_cons, Submonoid.coe_mul]
      rw [Matrix.mul_assoc,
        list_prod_comm_of_mem tail X (fun V hV ↦ hcomm V (List.mem_cons_of_mem U hV)),
        ← Matrix.mul_assoc, hcomm U List.mem_cons_self, Matrix.mul_assoc]
theorem list_prod_conj_comm_of_mem {D : ℕ} :
    ∀ (L : List (Unitary D)) (X : Operator D),
      (∀ U ∈ L, U.1 * X = X * U.1) →
      L.prod.1ᴴ * X * L.prod.1 = X
  | [], _, _ => by simp
  | U :: tail, X, hcomm => by
      simp only [List.prod_cons, Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc X U.1, ← hcomm U List.mem_cons_self, Matrix.mul_assoc U.1 X,
        ← Matrix.mul_assoc U.1ᴴ U.1, show U.1ᴴ * U.1 = 1 by
          simpa only [Matrix.star_eq_conjTranspose] using U.2.1, Matrix.one_mul, ← Matrix.mul_assoc]
      exact list_prod_conj_comm_of_mem tail X fun V hV ↦ hcomm V (List.mem_cons_of_mem U hV)
theorem unitary_coe_mul {D : ℕ} (A B : Unitary D) : (A * B).1 = A.1 * B.1 :=
  Submonoid.coe_mul _ A B
theorem mul_left_congr {D : ℕ} {A₁ A₂ : Operator D} (B : Operator D) (h : A₁ = A₂) :
    A₁ * B = A₂ * B := h ▸ rfl
theorem list_ofFn_prod_conj_rEl (V : Fin 218 → Unitary (2 ^ 18)) (e : Fin 218)
    (M : Operator (2 ^ 18)) :
    ((List.ofFn fun s : Fin 218 ↦ (rEl_sp s).embedUnitary (V s)).prod).1ᴴ *
        (rEl_sp e).embedMatrix M *
        ((List.ofFn fun s : Fin 218 ↦ (rEl_sp s).embedUnitary (V s)).prod).1 =
      (rEl_sp e).embedMatrix ((V e).1ᴴ * M * (V e).1) := by
  have hfr : List.finRange 218 =
      (List.finRange 218).take e.val ++ e :: (List.finRange 218).drop (e.val + 1) := by
    have hget : (List.finRange 218)[e.val]'(by simp [e.isLt]) = e :=
      List.getElem_finRange e.isLt
    conv_lhs => rw [← List.take_append_drop e.val (List.finRange 218)]
    rw [List.drop_eq_getElem_cons (by simp [e.isLt]), hget]
  obtain ⟨_, hnd₂, hdisj⟩ := List.nodup_append.mp (hfr ▸ List.nodup_finRange 218)
  have hconj_sub (S : List (Fin 218)) (hne : ∀ s ∈ S, s ≠ e) (Y : Operator (2 ^ 18)) :
      (S.map fun s ↦ (rEl_sp s).embedUnitary (V s)).prod.1ᴴ * (rEl_sp e).embedMatrix Y *
        (S.map fun s ↦ (rEl_sp s).embedUnitary (V s)).prod.1 = (rEl_sp e).embedMatrix Y :=
    list_prod_conj_comm_of_mem _ _ fun U hU ↦ by
      rcases List.mem_map.mp hU with ⟨s, hs, rfl⟩
      exact QRegister.embedMatrix_comm_of_disjoint _ _ (rEl_disjoint_of_ne_sp (hne s hs)) _ _
  have hsplit : List.ofFn (fun s : Fin 218 ↦ (rEl_sp s).embedUnitary (V s)) =
      ((List.finRange 218).take e.val).map (fun s ↦ (rEl_sp s).embedUnitary (V s)) ++
        ((rEl_sp e).embedUnitary (V e)) ::
          ((List.finRange 218).drop (e.val + 1)).map
            (fun s ↦ (rEl_sp s).embedUnitary (V s)) := by
    conv_lhs => rw [List.ofFn_eq_map, hfr]
    rw [List.map_append, List.map_cons]
  rw [hsplit]
  simp only [List.prod_append, List.prod_cons, Submonoid.coe_mul, Matrix.conjTranspose_mul]
  set L₁ := List.map (fun s ↦ (rEl_sp s).embedUnitary (V s)) ((List.finRange 218).take e.val)
  set L₂ := List.map (fun s ↦ (rEl_sp s).embedUnitary (V s)) ((List.finRange 218).drop (e.val + 1))
  rw [show L₂.prod.1ᴴ * ((rEl_sp e).embedUnitary (V e)).1ᴴ * L₁.prod.1ᴴ * (rEl_sp e).embedMatrix M *
      (L₁.prod.1 * (((rEl_sp e).embedUnitary (V e)).1 * L₂.prod.1)) =
      L₂.prod.1ᴴ * (((rEl_sp e).embedUnitary (V e)).1ᴴ *
        (L₁.prod.1ᴴ * (rEl_sp e).embedMatrix M * L₁.prod.1) *
        ((rEl_sp e).embedUnitary (V e)).1) * L₂.prod.1 by simp only [Matrix.mul_assoc],
    hconj_sub _ (fun s hs ↦ hdisj s hs e List.mem_cons_self) M]
  simp only [QRegister.embedUnitary_val, ← QRegister.embedMatrix_conjTranspose,
    ← QRegister.embedMatrix_mul]
  exact hconj_sub _ (fun _ hs hse ↦ (List.nodup_cons.mp hnd₂).1
    (Eq.ndrec (motive := (· ∈ (List.finRange 218).drop (e.val + 1))) hs hse)) _
theorem diag_slotCoordSys_eq_embed (e : Fin 218) (y : NyqGrid3D64) :
    Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
        if slotCoordSys z e = y then (1 : ℂ) else 0) =
      (rEl_sp e).embedMatrix (Matrix.diagonal fun u : Fin (2 ^ 18) ↦
        if slotCoord18Equiv u = y then (1 : ℂ) else 0) :=
  ((rEl_sp e).embedMatrix_diagonal
    (fun u : Fin (2 ^ 18) ↦ if slotCoord18Equiv u = y then (1 : ℂ) else 0)).symm
theorem veeSysProdUnitary_conj_slotProj (b₁ : NyqParity3D) (e : Fin 218) (y : NyqGrid3D64) :
    (veeSysProdUnitary b₁).1ᴴ *
        Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
          if slotCoordSys z e = y then (1 : ℂ) else 0) *
        (veeSysProdUnitary b₁).1 =
      op_sp (veeSubGridKet b₁ y) e := by
  rw [diag_slotCoordSys_eq_embed, veeSysProdUnitary, list_ofFn_prod_conj_rEl]
  refine congrArg (rEl_sp e).embedMatrix ?_
  rw [Matrix.mul_assoc]
  ext u v
  rw [Matrix.mul_apply]
  simp only [veeBasisUnitary18, veeBasisMat18, rk1_sp, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Matrix.of_apply, star_star, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero]
  rw [← Equiv.sum_comp slotCoord18Equiv.symm]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single y (fun z _ hz ↦ by simp [hz])
    (fun hy ↦ False.elim (hy (Finset.mem_univ y)))]
  simp
abbrev hkFlag80 : posCoreWires = fullSysCoreWires 80 := pos24_coreWires80_eq.symm
theorem coreIdxOf_hkFlag80_bits (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ systemQubits)) (q : Wire (fullSysCoreWires 80)) :
    basisBits (fullSysCoreWires 80) (coreIdxOf hkFlag80 s0 p80 z) q =
      coreBetaOf s0 p80 z ⟨q.val, Nat.lt_of_lt_of_eq q.isLt hkFlag80.symm⟩ := by
  have hgen {kC : ℕ} (hk : posCoreWires = kC) (q' : Wire kC) :
      basisBits kC (coreIdxOf hk s0 p80 z) q' =
        coreBetaOf s0 p80 z ⟨q'.val, Nat.lt_of_lt_of_eq q'.isLt hk.symm⟩ := by
    subst hk
    exact congrFun ((basisBitsEquiv posCoreWires).apply_symm_apply (coreBetaOf s0 p80 z)) q'
  exact hgen hkFlag80 q
theorem coreBetaOf_lt_sys (s0 : Bool) (p80 : BitAssignment 80) (z : Fin (2 ^ systemQubits))
    {n : ℕ} {hn : n < posCoreWires} (hq : n < systemQubits) :
    coreBetaOf s0 p80 z ⟨n, hn⟩ = basisBits systemQubits z ⟨n, hq⟩ :=
  coreBetaOf_lt3948 s0 p80 z ⟨n, hq⟩
theorem coreBetaOf_ge_sys (s0 : Bool) (p80 : BitAssignment 80)
    (z₁ z₂ : Fin (2 ^ systemQubits)) (q : Wire posCoreWires) (hq : systemQubits ≤ q.val) :
    coreBetaOf s0 p80 z₁ q = coreBetaOf s0 p80 z₂ q := by
  by_cases hmid : q.val < 3954
  · exact (coreBetaOf_mid s0 p80 z₁ q hq hmid).trans (coreBetaOf_mid s0 p80 z₂ q hq hmid).symm
  · have hj80 : q.val - 3954 < PosSlots24BranchConcrete.posPayloadWires :=
      (by have : q.val < 4034 := q.isLt; change q.val - 3954 < 80; omega)
    rw [show q = rPosSubLocal ⟨q.val - 3954, hj80⟩ from
      Fin.ext (by change q.val = 3954 + (q.val - 3954); omega),
      coreBetaOf_payload, coreBetaOf_payload]
theorem preservesCoreAnc_of_comm_rAncFlag80 (M : Operator (2 ^ fullSysCoreWires 80))
    (hcomm : ∀ a : Fin (2 ^ 86),
      M * rAncFlag80.basisOutcomeProjector a = rAncFlag80.basisOutcomeProjector a * M)
    (s0 : Bool) (p80 : BitAssignment 80) :
    PreservesCoreAnc hkFlag80 M s0 p80 := by
  intro x row hnz
  have hext : rAncFlag80.extractIndex row =
      rAncFlag80.extractIndex (coreIdxOf hkFlag80 s0 p80 x) :=
    by_contra fun hne ↦ hnz (entry_zero_of_comm_basisOutcomeProjector rAncFlag80 M hcomm row _ hne)
  let rSys : QRegister systemQubits (fullSysCoreWires 80) :=
    QRegister.block 0 systemQubits (by change 0 + 3948 ≤ 4034; omega)
  let y : Fin (2 ^ systemQubits) := rSys.extractIndex row
  refine ⟨y, (basisBitsEquiv (fullSysCoreWires 80)).injective (funext fun q ↦ ?_)⟩
  change basisBits (fullSysCoreWires 80) row q =
    basisBits (fullSysCoreWires 80) (coreIdxOf hkFlag80 s0 p80 y) q
  by_cases hq : q.val < systemQubits
  · rw [coreIdxOf_hkFlag80_bits, coreBetaOf_lt_sys s0 p80 y hq, QRegister.basisBits_extractIndex,
      show rSys ⟨q.val, hq⟩ = q from Fin.ext (Nat.zero_add q.val)]
  · have hql : q.val < 4034 := q.isLt
    have hlt_s : ¬ q.val < 3948 := hq
    let idx86 : Fin 86 := ⟨q.val - 3948, by omega⟩
    have h1 := congrFun (congrArg (basisBits 86) hext) idx86
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      show rAncFlag80 idx86 = q from Fin.ext (by change 3948 + (q.val - 3948) = q.val; omega),
      coreIdxOf_hkFlag80_bits] at h1
    rw [h1, coreIdxOf_hkFlag80_bits]
    exact coreBetaOf_ge_sys s0 p80 x y _ (Nat.le_of_not_lt hq)
open NuclearTwistRealizes (uTwistParam) in
noncomputable def slot2UTwistParam {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (c : Configuration) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uTwistParam swapOnSlot2 hm c
open NuclearTwistRealizes
  (twistCorePermFn twistCorePhase uTwistParam uTwistParam_mulVec_basisKet) in
theorem slot2UTwistParam_mulVec_basisKet {mPayload : ℕ} (swapOnSlot2 : Bool)
    (hm : 22 ≤ mPayload) (c : Configuration)
    (β : BitAssignment (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload)) :
    (slot2UTwistParam swapOnSlot2 hm c).1.mulVec (basisKet β) =
      twistCorePhase swapOnSlot2 hm c β • basisKet (twistCorePermFn swapOnSlot2 hm β) := by
  unfold slot2UTwistParam
  let rId := QRegExt.ofFin (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload)
  rw [← congrArg Subtype.val (ofFin_embedUnitary_eq (uTwistParam swapOnSlot2 hm c))]
  refine (uTwistParam_mulVec_basisKet swapOnSlot2 hm c rId β).trans
    (congrArg (twistCorePhase swapOnSlot2 hm c β • basisKet ·) ?_)
  funext z
  have hz : z ∈ rId.image := (QRegister.mem_image rId z).mpr ⟨z, rfl⟩
  simp only [hz, ↓reduceDIte,
    show Classical.choose ((QRegister.mem_image rId z).mp hz) = z from
      Classical.choose_spec ((QRegister.mem_image rId z).mp hz)]
  rfl
def payloadB1Parity (p80 : BitAssignment 80) : NyqParity3D :=
  fun w ↦ ⟨(p80 ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩).val, ZMod.val_lt _⟩
theorem embedMatrix_list_ofFn_prod {m k N : ℕ} (rOuter : QRegister k N) :
    ∀ {n : ℕ} (rInner : Fin n → QRegister m k) (V : Fin n → Unitary (2 ^ m)),
      rOuter.embedMatrix ((List.ofFn fun i ↦ (rInner i).embedUnitary (V i)).prod).1 =
        ((List.ofFn fun i ↦ (rOuter.compose (rInner i)).embedUnitary (V i)).prod).1
  | 0, _, _ => by simp [QRegister.embedMatrix_one]
  | n + 1, rInner, V => by
      simp only [List.ofFn_succ, List.prod_cons, Submonoid.coe_mul, QRegister.embedMatrix_mul,
        embedMatrix_list_ofFn_prod rOuter (fun i ↦ rInner i.succ) (fun i ↦ V i.succ)]
      exact mul_left_congr _
        (by simp only [QRegister.embedUnitary_val, QRegister.embedMatrix_compose])
open FullSysCatSegmentBridge (fullSysQftCoreUnitary) in
theorem sysBlockAtPayloadGen_fullSysQft_eq
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (hqft : qft.uQft654 = qft64Ideal654Unitary)
    (s0 : Bool) (p80 : BitAssignment 80) :
    let b₁ := payloadB1Parity p80
    sysBlockAtPayloadGen hkFlag80 (fullSysQftCoreUnitary pos24_6_le_80 qft).1 s0 p80 =
      ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary
        (qft64OffsetUnitary3D b₁)).prod).1 := by
  intro b₁
  let fC := fun e : Fin 218 ↦
    ((coreElecCosetB1Block pos24_6_le_80).compose (rElec18In654 e)).embedUnitary
      (qft64OffsetUnitary3D b₁)
  have rC_val (e : Fin 218) (j : Fin 18) :
      (((coreElecCosetB1Block pos24_6_le_80).compose (rElec18In654 e)) j).val =
        18 * e.val + j.val := by
    have hj : 18 * e.val + j.val < 3924 := by
      have := e.isLt
      have := j.isLt
      omega
    change ((coreElecCosetB1Block pos24_6_le_80) (rElec18In654 e j)).val = _
    rw [show rElec18In654 e j = Fin.castAdd 3 ⟨18 * e.val + j.val, hj⟩ from Fin.ext rfl,
      QRegister.concat_apply_left]
    exact Nat.zero_add _
  have hemb (e : Fin 218) :
      sysBlockAtPayloadGen hkFlag80 (fC e).1 s0 p80 =
        (rEl_sp e).embedMatrix (qft64OffsetUnitary3D b₁).1 := by
    let rC := (coreElecCosetB1Block pos24_6_le_80).compose (rElec18In654 e)
    let M := (qft64OffsetUnitary3D b₁).1
    have hwire : ∀ j : Fin 18, (rC j).val = (rEl_sp e j).val := rC_val e
    have hextract (z : Fin (2 ^ systemQubits)) :
        rC.extractIndex (coreIdxOf hkFlag80 s0 p80 z) = (rEl_sp e).extractIndex z :=
      (basisBitsEquiv 18).injective (funext fun j ↦ by
        change basisBits 18 _ j = basisBits 18 _ j
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
          coreIdxOf_hkFlag80_bits, coreBetaOf_lt_sys s0 p80 z (hwire j ▸ (rEl_sp e j).isLt)]
        exact congrArg (basisBits systemQubits z) (Fin.ext (hwire j)))
    ext x' x
    rw [sysBlockAtPayloadGen_apply, QRegister.embedUnitary_val]
    have hag_iff : rC.AgreeOutside (coreIdxOf hkFlag80 s0 p80 x')
          (coreIdxOf hkFlag80 s0 p80 x) ↔ (rEl_sp e).AgreeOutside x' x :=
      ⟨fun hag q hq ↦ by
        have hb := hag ⟨q.val, Nat.lt_trans q.isLt (by
          change 3948 < 4034
          omega)⟩ fun ⟨j, hjC⟩ ↦
          hq ⟨j, Fin.ext ((hwire j).symm.trans (congrArg Fin.val hjC))⟩
        rwa [coreIdxOf_hkFlag80_bits, coreIdxOf_hkFlag80_bits,
          coreBetaOf_lt_sys s0 p80 x' q.isLt, coreBetaOf_lt_sys s0 p80 x q.isLt] at hb,
      fun hag qC hqC ↦ by
        rw [coreIdxOf_hkFlag80_bits, coreIdxOf_hkFlag80_bits]
        by_cases hlt : qC.val < systemQubits
        · rw [coreBetaOf_lt_sys s0 p80 x' hlt, coreBetaOf_lt_sys s0 p80 x hlt]
          exact hag ⟨qC.val, hlt⟩ fun ⟨j, hjS⟩ ↦
            hqC ⟨j, Fin.ext ((hwire j).trans (congrArg Fin.val hjS))⟩
        · exact coreBetaOf_ge_sys s0 p80 x' x _ (Nat.le_of_not_lt hlt)⟩
    by_cases hag : (rEl_sp e).AgreeOutside x' x
    · rw [embedMatrix_entry_of_agreeOutside rC M (hag_iff.mpr hag),
        embedMatrix_entry_of_agreeOutside (rEl_sp e) M hag, hextract, hextract]
    · rw [embedMatrix_entry_of_not_agreeOutside rC M (fun h ↦ hag (hag_iff.mp h)),
        embedMatrix_entry_of_not_agreeOutside (rEl_sp e) M hag]
  have hlist (L : List (Fin 218)) :
      sysBlockAtPayloadGen hkFlag80 ((L.map fC).prod).1 s0 p80 =
        ((L.map fun e ↦ (rEl_sp e).embedUnitary (qft64OffsetUnitary3D b₁)).prod).1 := by
    induction L with
    | nil =>
      simp only [List.map_nil, List.prod_nil, OneMemClass.coe_one]
      ext x' x
      rw [sysBlockAtPayloadGen_apply, Matrix.one_apply, Matrix.one_apply]
      exact if_congr ⟨fun h ↦ coreIdxOf_injective hkFlag80 s0 p80 h, fun h ↦ h ▸ rfl⟩ rfl rfl
    | cons e tail ih =>
      simp only [List.map_cons, List.prod_cons, Submonoid.coe_mul]
      have hcomm_tail (a : Fin (2 ^ 86)) :
          ((tail.map fC).prod).1 * rAncFlag80.basisOutcomeProjector a =
            rAncFlag80.basisOutcomeProjector a * ((tail.map fC).prod).1 :=
        list_prod_comm_of_mem (tail.map fC) (rAncFlag80.basisOutcomeProjector a) fun U hU ↦ by
          rcases List.mem_map.mp hU with ⟨e', _, rfl⟩
          refine QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ rAncFlag80 ?_ _ a
          rw [QRegister.disjoint_iff]
          intro j₁ j₂ h
          have hv := (rC_val e' j₁).symm.trans (congrArg Fin.val h)
          have hge := rAncFlag80_wire_ge_3948 j₂
          have := e'.isLt
          have := j₁.isLt
          omega
      rw [sysBlockAtPayloadGen_mul_of_preserves hkFlag80 _ _ s0 p80
        (preservesCoreAnc_of_comm_rAncFlag80 _ hcomm_tail s0 p80), ih]
      exact mul_left_congr _ (hemb e)
  have hEqP3 : (fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
      (coreCosetB1Block pos24_6_le_80).basisOutcomeProjector (nyqParity3DEquivFin8 b₁) =
      ((List.ofFn fC).prod).1 *
      (coreCosetB1Block pos24_6_le_80).basisOutcomeProjector (nyqParity3DEquivFin8 b₁) := by
    rw [← coreElecCosetB1_compose_rCoset3, basisOutcomeProjector_compose_local,
      fullSysQftCoreUnitary, hqft, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
      qft64Ideal654Unitary_mul_cosetProj_eq_elec3DProd b₁, QRegister.embedMatrix_mul,
      embedMatrix_list_ofFn_prod (coreElecCosetB1Block pos24_6_le_80) rElec18In654]
  rw [List.ofFn_eq_map, ← hlist (List.finRange 218), ← List.ofFn_eq_map]
  ext x' x
  have hext_b1 : (coreCosetB1Block pos24_6_le_80).extractIndex (coreIdxOf hkFlag80 s0 p80 x) =
      nyqParity3DEquivFin8 b₁ :=
    (basisBitsEquiv 3).injective (funext fun w ↦ by
      change basisBits 3 _ w = basisBits 3 _ w
      rw [QRegister.basisBits_extractIndex, coreIdxOf_hkFlag80_bits,
        show (⟨(coreCosetB1Block pos24_6_le_80 w).val, _⟩ : Wire posCoreWires) =
          rPosSubLocal ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩ from Fin.ext rfl,
        coreBetaOf_payload]
      dsimp only [nyqParity3DEquivFin8, Equiv.coe_fn_mk, b₁, payloadB1Parity]
      have hsym := congrFun ((basisBitsEquiv 3).apply_symm_apply (fun w' : Fin 3 ↦
        (((p80 ⟨w'.val, Nat.lt_trans w'.isLt (by decide)⟩).val : ℕ) : ZMod 2))) w
      change basisBits 3 ((basisBitsEquiv 3).symm _) w = _ at hsym
      rw [hsym, ZMod.natCast_zmod_val])
  have hrc := congrFun (congrFun hEqP3 (coreIdxOf hkFlag80 s0 p80 x'))
    (coreIdxOf hkFlag80 s0 p80 x)
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal,
    hext_b1, ite_eq_left rfl, mul_one, mul_one] at hrc
  rw [sysBlockAtPayloadGen_apply, sysBlockAtPayloadGen_apply]
  exact hrc
def offset18Perm : Equiv.Perm (Fin (2 ^ 18)) := u18AxisSplitEquiv.trans ((Equiv.arrowCongr
    (Equiv.refl (Fin 3)) signedMagToOffset6Equiv).trans u18GridEquiv.symm)
def offset18Unitary : Unitary (2 ^ 18) := fwdPermUnitary offset18Perm
noncomputable def offsetSysUnitary : Unitary (2 ^ systemQubits) :=
  (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary offset18Unitary).prod
theorem u18GridEquiv_offset18Perm (u : Fin (2 ^ 18)) :
    u18GridEquiv (offset18Perm u) = elecOffsetGridEquiv18 u :=
  u18GridEquiv.apply_symm_apply _
theorem qft64OffsetUnitary3D_mul_offset18Unitary (b₁ : NyqParity3D) :
    (qft64OffsetUnitary3D b₁ * offset18Unitary).1 =
      Matrix.diagonal (fun z : Fin (2 ^ 18) ↦ karatsubaOutPhase3D (slotCoord18Equiv z)) *
        (veeBasisUnitary18 b₁).1 := by
  ext z u
  rw [Submonoid.coe_mul, Matrix.mul_apply, Matrix.diagonal_mul]
  change (∑ w : Fin (2 ^ 18), qft64OffsetUnitary3D b₁ z w *
      (fwdPermUnitary offset18Perm).1 w u) =
    karatsubaOutPhase3D (slotCoord18Equiv z) * star (veeSubGridKet b₁ (slotCoord18Equiv z) u)
  simp_rw [fwdPermUnitary_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (offset18Perm u) (fun w _ hw ↦ by simp only [hw.symm, ↓reduceIte])
    (fun h ↦ False.elim (h (Finset.mem_univ _))), ite_eq_left rfl, qft64OffsetUnitary3D_apply,
    u18GridEquiv_offset18Perm]
  have hk := karatsubaOffset3D128_apply b₁ (u18GridEquiv z) (elecOffsetGridEquiv18 u)
  dsimp only [karatsubaOffset3D128, Matrix.of_apply] at hk
  rw [hk]
  simp [slotCoord18Equiv, veeSubGridKet]
theorem list_ofFn_embedUnitary_prod_mul {m N : ℕ} :
    ∀ {n : ℕ} (r : Fin n → QRegister m N)
      (_hdisj : ∀ i j : Fin n, i ≠ j → (r i).DisjointWires (r j))
      (F G : Fin n → Unitary (2 ^ m)),
      (List.ofFn fun i ↦ (r i).embedUnitary (F i)).prod *
          (List.ofFn fun i ↦ (r i).embedUnitary (G i)).prod =
        (List.ofFn fun i ↦ (r i).embedUnitary (F i * G i)).prod
  | 0, _, _, _, _ => by simp
  | n + 1, r, hdisj, F, G => by
      apply Subtype.ext
      simp only [List.ofFn_succ, List.prod_cons, Submonoid.coe_mul]
      have ih := congrArg Subtype.val (list_ofFn_embedUnitary_prod_mul (fun i ↦ r i.succ)
        (fun i j hij ↦ hdisj i.succ j.succ (Fin.succ_inj.ne.mpr hij))
        (fun i ↦ F i.succ) (fun i ↦ G i.succ))
      simp only [Submonoid.coe_mul] at ih
      rw [Matrix.mul_assoc ((r 0).embedUnitary (F 0)).1,
        ← Matrix.mul_assoc _ ((r 0).embedUnitary (G 0)).1,
        list_prod_comm_of_mem _ ((r 0).embedUnitary (G 0)).1 (fun U hU ↦ by
          rcases List.mem_ofFn.mp hU with ⟨i, rfl⟩
          exact QRegister.embedMatrix_comm_of_disjoint (r i.succ) (r 0)
            (hdisj i.succ 0 (Fin.succ_ne_zero i)) _ _),
        Matrix.mul_assoc ((r 0).embedUnitary (G 0)).1,
        ← Matrix.mul_assoc ((r 0).embedUnitary (F 0)).1, ih,
        ← Submonoid.coe_mul, QRegister.embedUnitary_mul]
theorem list_ofFn_rEl_prod_mul (F G : Fin 218 → Unitary (2 ^ 18)) :
    (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (F e)).prod *
      (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (G e)).prod =
    (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (F e * G e)).prod :=
  list_ofFn_embedUnitary_prod_mul (fun e : Fin 218 ↦ rEl_sp e)
    (fun _ _ hne ↦ rEl_disjoint_of_ne_sp hne) F G
noncomputable def outPhase18Unitary : Unitary (2 ^ 18) :=
  ⟨Matrix.diagonal fun z : Fin (2 ^ 18) ↦ karatsubaOutPhase3D (slotCoord18Equiv z), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal
      (funext fun z ↦ karatsubaOutPhase3D_unit (slotCoord18Equiv z))⟩
theorem list_ofFn_rEl_outPhase_eq_diagonal :
    ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary outPhase18Unitary).prod).1 =
      Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
        ∏ e : Fin 218, karatsubaOutPhase3D (slotCoordSys z e)) := by
  have hgen (L : List (Fin 218)) :
      ((L.map fun e ↦ (rEl_sp e).embedUnitary outPhase18Unitary).prod).1 =
        Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
          (L.map fun e ↦ karatsubaOutPhase3D (slotCoordSys z e)).prod) := by
    induction L with
    | nil => simp [Matrix.diagonal_one]
    | cons e _ ih =>
      simp only [List.map_cons, List.prod_cons, Submonoid.coe_mul,
        show ((rEl_sp e).embedUnitary outPhase18Unitary).1 =
          Matrix.diagonal (fun z ↦ karatsubaOutPhase3D (slotCoordSys z e)) from
          (rEl_sp e).embedMatrix_diagonal _, ih, Matrix.diagonal_mul_diagonal]
  rw [List.ofFn_eq_map, hgen (List.finRange 218)]
  exact congrArg Matrix.diagonal (funext fun _ ↦ by rw [Fin.prod_univ_def])
noncomputable def xor32SysPerm : Equiv.Perm (Fin (2 ^ systemQubits)) :=
  (basisBitsEquiv systemQubits).trans
    (({ toFun := fun f q ↦ if q.val < 3924 ∧ q.val % 6 = 5 then f q + 1 else f q
        invFun := fun f q ↦ if q.val < 3924 ∧ q.val % 6 = 5 then f q + 1 else f q
        left_inv := fun f ↦ by
          funext q; dsimp only; split_ifs
          · rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f q) with h | h <;> rw [h] <;> decide
          · rfl
        right_inv := fun f ↦ by
          funext q; dsimp only; split_ifs
          · rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f q) with h | h <;> rw [h] <;> decide
          · rfl } : Equiv.Perm (BitAssignment systemQubits)).trans (basisBitsEquiv
            systemQubits).symm)
theorem basisBits_xor32SysPerm (x : Fin (2 ^ systemQubits)) (q : Wire systemQubits) :
    basisBits systemQubits (xor32SysPerm x) q = if q.val < 3924 ∧ q.val % 6 = 5 then basisBits
    systemQubits x q + 1 else basisBits systemQubits x q := by
  have hPoly : ∀ {k : ℕ} (e : Equiv.Perm (BitAssignment k)) (z : Fin (2 ^ k)) (w : Wire k),
      basisBits k (((basisBitsEquiv k).trans (e.trans (basisBitsEquiv k).symm)) z) w =
        e (basisBits k z) w := by
    intro k e z w
    change (basisBitsEquiv k) ((basisBitsEquiv k).symm (e (basisBits k z))) w = _
    exact congrFun ((basisBitsEquiv k).apply_symm_apply (e (basisBits k z))) w
  exact hPoly _ x q
theorem elecAxisField_eq_extract_u18 (x : Fin (2 ^ systemQubits)) (e : Fin 218) (w : Fin 3) :
    elecAxisField x e w = u18AxisSplitEquiv ((rEl_sp e).extractIndex x) w := by
  apply Fin.ext
  have h1 : (elecAxisField x e w).val = (x.val / 2 ^ (18 * e.val + 6 * w.val)) % 64 := by
    dsimp [elecAxisField, TwosCompAndWire0Cancel.elec654Axes]
    rw [extractIndex_block_val,
      show 6 * (3 * e.val + w.val) = 18 * e.val + 6 * w.val by omega]
    rfl
  have h2 : (u18AxisSplitEquiv ((rEl_sp e).extractIndex x) w).val =
      (x.val / 2 ^ (18 * e.val + 6 * w.val)) % 64 := by
    dsimp only [u18AxisSplitEquiv, Equiv.coe_fn_mk, rEl_sp]
    rw [extractIndex_block_val, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    fin_cases w <;> dsimp <;> omega
  exact h1.trans h2.symm
theorem extractIndex_rEl_smToTwos654_xor32 (u : Fin (2 ^ systemQubits)) (e : Fin 218) :
    (rEl_sp e).extractIndex (xor32SysPerm (smToTwos654SysPerm u)) =
      offset18Perm ((rEl_sp e).extractIndex u) := by
  apply u18AxisSplitEquiv.injective
  funext w
  rw [← elecAxisField_eq_extract_u18 _ e w]
  have hsm3 : ∀ v : Fin 64, (smToTwosAxisPerm 3 v).val = (signedMagToTwos6Perm v).val := by
    decide
  have hsplit : ∀ v : Fin (2 ^ 18), u18AxisSplitEquiv v w = u18GridEquiv v w := fun v ↦ by
    fin_cases w <;> rfl
  dsimp only [offset18Perm, Equiv.trans_apply]
  rw [hsplit, u18GridEquiv.apply_symm_apply]
  change elecAxisField _ e w =
    signedMagToOffset6Equiv (u18AxisSplitEquiv ((rEl_sp e).extractIndex u) w)
  rw [← elecAxisField_eq_extract_u18 u e w]
  let f : Fin 64 → Fin 64 := fun v ↦ (basisBitsEquiv 6).symm
    (fun j : Fin 6 ↦ if j.val = 5 then basisBits 6 v j + 1 else basisBits 6 v j)
  have hxor : (elecAxisField (xor32SysPerm (smToTwos654SysPerm u)) e w).val =
      (elecAxisField (smToTwos654SysPerm u) e w).val ^^^ 32 := by
    have hb_fld : ∀ (y : Fin (2 ^ systemQubits)) (j : Fin 6),
        basisBits 6 (elecAxisField y e w) j =
          basisBits systemQubits y ⟨18 * e.val + 6 * w.val + j.val,
            by have := e.isLt; have := w.isLt; have := j.isLt; change _ < 3948; omega⟩ :=
      fun y j ↦ (QRegister.basisBits_extractIndex _ y j).trans
        (congrArg (basisBits systemQubits y) (Fin.ext (by
          change 6 * (3 * e.val + w.val) + j.val = 18 * e.val + 6 * w.val + j.val; omega)))
    have heq : elecAxisField (xor32SysPerm (smToTwos654SysPerm u)) e w =
        f (elecAxisField (smToTwos654SysPerm u) e w) :=
      (basisBitsEquiv 6).injective (funext fun j ↦ by
        change basisBits 6 _ j = basisBits 6 (f _) j
        have hsym := congrFun ((basisBitsEquiv 6).apply_symm_apply
          (fun j' : Fin 6 ↦ if j'.val = 5 then
            basisBits 6 (elecAxisField (smToTwos654SysPerm u) e w) j' + 1
            else basisBits 6 (elecAxisField (smToTwos654SysPerm u) e w) j')) j
        change basisBits 6 (f _) j = _ at hsym
        rw [hb_fld, basisBits_xor32SysPerm, hsym, hb_fld]
        have hcond : (18 * e.val + 6 * w.val + j.val < 3924 ∧
            (18 * e.val + 6 * w.val + j.val) % 6 = 5) ↔ j.val = 5 := by
          have := e.isLt; have := w.isLt; have := j.isLt; omega
        simp only [hcond])
    rw [heq]
    exact (by decide : ∀ v : Fin 64, (f v).val = v.val ^^^ 32) _
  apply Fin.ext
  dsimp only [signedMagToOffset6Equiv, Equiv.coe_fn_mk]
  rw [hxor, elecAxisField_smToTwos654, hsm3, signedMagToOffset6_eq_xor32]
noncomputable def embedRegPerm {m N : ℕ} (r : QRegister m N)
    (perm : Equiv.Perm (Fin (2 ^ m))) : Equiv.Perm (Fin (2 ^ N)) where
  toFun u := r.replaceIndex u (perm (r.extractIndex u))
  invFun u := r.replaceIndex u (perm.symm (r.extractIndex u))
  left_inv u := by
    simp only [QRegister.extractIndex_replaceIndex, Equiv.symm_apply_apply,
      QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_extractIndex]
  right_inv u := by
    simp only [QRegister.extractIndex_replaceIndex, Equiv.apply_symm_apply,
      QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_extractIndex]
theorem embedUnitary_fwdPermUnitary_slot2 {m N : ℕ} [NeZero (2 ^ m)] [NeZero (2 ^ N)]
    (r : QRegister m N) (perm : Equiv.Perm (Fin (2 ^ m))) :
    r.embedUnitary (fwdPermUnitary perm) = fwdPermUnitary (embedRegPerm r perm) := by
  apply Subtype.ext
  ext z u
  rw [QRegister.embedUnitary_val, fwdPermUnitary_apply]
  by_cases hag : r.AgreeOutside z u
  · rw [embedMatrix_entry_of_agreeOutside r _ hag, fwdPermUnitary_apply]
    refine if_congr ⟨fun h ↦ r.replaceIndex_eq_of_extractIndex_eq_of_agreeOutside u z _ h.symm
      hag, fun h ↦ ?_⟩ rfl rfl
    rw [← h]
    exact (QRegister.extractIndex_replaceIndex r u _).symm
  · rw [embedMatrix_entry_of_not_agreeOutside r _ hag]
    have hne : embedRegPerm r perm u ≠ z := by
      rintro rfl
      exact hag fun q hq ↦ QRegister.basisBits_replaceIndex_of_not_mem r u _ q hq
    simp [hne]
theorem list_map_fwdPermUnitary_prod {α : Type*} {D : ℕ}
    (g : α → Equiv.Perm (Fin D)) (F : α → Unitary D)
    (hF : ∀ a, F a = fwdPermUnitary (g a))
    (foldG : List α → Equiv.Perm (Fin D))
    (hnil : foldG [] = Equiv.refl (Fin D))
    (hcons : ∀ a t, foldG (a :: t) = (foldG t).trans (g a)) :
    ∀ L : List α, (L.map F).prod = fwdPermUnitary (foldG L)
  | [] => by rw [List.map_nil, List.prod_nil, hnil, fwdPermUnitary_refl]
  | a :: t => by
      rw [List.map_cons, List.prod_cons, hF a,
        list_map_fwdPermUnitary_prod g F hF foldG hnil hcons t,
        hcons a t, fwdPermUnitary_trans]
noncomputable def foldElOffsetPerm : List (Fin 218) → Equiv.Perm (Fin (2 ^ systemQubits))
  | [] => Equiv.refl _
  | e :: tail => (foldElOffsetPerm tail).trans (embedRegPerm (rEl_sp e) offset18Perm)
theorem offsetSysUnitary_eq_fwdPerm :
    offsetSysUnitary = fwdPermUnitary (smToTwos654SysPerm.trans xor32SysPerm) := by
  let σ := smToTwos654SysPerm.trans xor32SysPerm
  have hfold_ext (L : List (Fin 218)) (hnd : L.Nodup) (u : Fin (2 ^ systemQubits)) :
      (∀ e ∈ L, (rEl_sp e).extractIndex (foldElOffsetPerm L u) =
        offset18Perm ((rEl_sp e).extractIndex u)) ∧
      (∀ q : Wire systemQubits, (∀ e ∈ L, q ∉ Set.range (rEl_sp e).wires) →
        basisBits systemQubits (foldElOffsetPerm L u) q = basisBits systemQubits u q) := by
    induction L with
    | nil => exact ⟨fun _ h ↦ False.elim (List.not_mem_nil h), fun _ _ ↦ rfl⟩
    | cons e tail ih =>
      rcases List.nodup_cons.mp hnd with ⟨hnotmem, hnd_t⟩
      rcases ih hnd_t with ⟨ih_ext, ih_out⟩
      set v := foldElOffsetPerm tail u
      have hv_step : foldElOffsetPerm (e :: tail) u =
          embedRegPerm (rEl_sp e) offset18Perm v := rfl
      rw [hv_step]
      refine ⟨fun e' he' ↦ ?_, fun q hq ↦ ?_⟩
      · rcases List.mem_cons.mp he' with rfl | ht
        · dsimp only [embedRegPerm, Equiv.coe_fn_mk]
          rw [QRegister.extractIndex_replaceIndex]
          refine congrArg offset18Perm ((basisBitsEquiv 18).injective (funext fun j ↦ ?_))
          change basisBits 18 _ j = basisBits 18 _ j
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
          exact ih_out (rEl_sp e' j) fun e'' he'' ⟨k, hk⟩ ↦
            (QRegister.disjoint_iff.mp
              (rEl_disjoint_of_ne_sp (fun h : e'' = e' ↦ hnotmem (h ▸ he'')))) k j hk
        · rw [show (rEl_sp e').extractIndex (embedRegPerm (rEl_sp e) offset18Perm v) =
              (rEl_sp e').extractIndex v from
            (basisBitsEquiv 18).injective (funext fun j ↦ by
              change basisBits 18 _ j = basisBits 18 _ j
              rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
              dsimp only [embedRegPerm, Equiv.coe_fn_mk]
              exact QRegister.basisBits_replaceIndex_of_not_mem (rEl_sp e) v _ _ fun ⟨k, hk⟩ ↦
                (QRegister.disjoint_iff.mp
                  (rEl_disjoint_of_ne_sp (fun h : e' = e ↦ hnotmem (h ▸ ht)))) j k hk.symm),
            ih_ext e' ht]
      · dsimp only [embedRegPerm, Equiv.coe_fn_mk]
        rw [QRegister.basisBits_replaceIndex_of_not_mem (rEl_sp e) v _ q
          (hq e List.mem_cons_self)]
        exact ih_out q fun e' he' ↦ hq e' (List.mem_cons_of_mem _ he')
  rw [offsetSysUnitary, List.ofFn_eq_map,
    list_map_fwdPermUnitary_prod (fun e : Fin 218 ↦ embedRegPerm (rEl_sp e) offset18Perm)
      (fun e : Fin 218 ↦ (rEl_sp e).embedUnitary offset18Unitary)
      (fun e : Fin 218 ↦ embedUnitary_fwdPermUnitary_slot2 (rEl_sp e) offset18Perm)
      foldElOffsetPerm rfl (fun _ _ ↦ rfl) (List.finRange 218)]
  refine congrArg fwdPermUnitary ?_
  ext u : 1
  rcases hfold_ext (List.finRange 218) (List.nodup_finRange 218) u with ⟨hext, hout⟩
  apply (basisBitsEquiv systemQubits).injective
  funext q
  change basisBits systemQubits _ q = basisBits systemQubits (σ u) q
  dsimp only [σ]
  rw [Equiv.trans_apply]
  by_cases hlt : q.val < 3924
  · let e : Fin 218 := ⟨q.val / 18, by omega⟩
    let j : Fin 18 := ⟨q.val % 18, Nat.mod_lt _ (by omega)⟩
    have h1 := congrFun (congrArg (basisBits 18) ((hext e (List.mem_finRange e)).trans
      (extractIndex_rEl_smToTwos654_xor32 u e).symm)) j
    rwa [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      show rEl_sp e j = q from Fin.ext (by
        dsimp [rEl_sp, qreg_block_wires_slot2, e, j]
        omega)] at h1
  · have hlt_sys : q.val < 3948 := q.isLt
    rw [hout q fun e _ ⟨j, hj⟩ ↦ hlt (by
        have := e.isLt
        have := j.isLt
        have hv := congrArg Fin.val hj
        dsimp [rEl_sp, qreg_block_wires_slot2] at hv
        omega),
      basisBits_xor32SysPerm, ite_eq_right (by omega : ¬(q.val < 3924 ∧ q.val % 6 = 5))]
    let ax : Fin 3 := ⟨(q.val - 3924) / 8, by omega⟩
    let jb : Fin 8 := ⟨(q.val - 3924) % 8, Nat.mod_lt _ (by omega)⟩
    have hproj_bit (y : Fin (2 ^ systemQubits)) :
        basisBits 8 (projAxisField y ax) jb = basisBits systemQubits y q := by
      dsimp [projAxisField, TwosCompAndWire0Cancel.proj3Axes]
      rw [← show (QRegister.block (3924 + 8 * ax.val) 8 (by
          have := ax.isLt
          dsimp [systemQubits, numElectrons, electronBits, projectileBits]
          omega) jb) = q from Fin.ext (by
          dsimp [qreg_block_wires_slot2, ax, jb]
          omega)]
      exact QRegister.basisBits_extractIndex _ y jb
    rw [← hproj_bit, ← hproj_bit, projAxisField_smToTwos654]
def payloadAncNat (p80 : BitAssignment 80) : ℕ :=
  _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
    p80 (pos80SubIdx 14 8 (by decide) j))
def payloadNucNat (p80 : BitAssignment 80) : ℕ :=
  _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
    p80 (pos80SubIdx 6 8 (by decide) j))
def barrelSysPerm (anc : ℕ) : Equiv.Perm (Fin (2 ^ systemQubits)) :=
  if h : anc < 218 then permElectron (Equiv.swap 0 ⟨anc, h⟩) else Equiv.refl _
theorem basisBits_barrelSysPerm_high (anc : ℕ) (x : Fin (2 ^ systemQubits))
    (q : Wire systemQubits) (hq : 3924 ≤ q.val) :
    basisBits systemQubits (barrelSysPerm anc x) q = basisBits systemQubits x q := by
  unfold barrelSysPerm
  by_cases h : anc < 218
  · simp only [h, ↓reduceDIte]
    rw [permElectron,
      basisBits_permElectron (permElectronWire (Equiv.swap (0 : Fin 218) ⟨anc, h⟩)) x q]
    refine congrArg (basisBits systemQubits x) ?_
    change permElectronWireFun _ q = q
    unfold permElectronWireFun
    exact PosSlots24MergedVepBound.dite_eq_of_neg (by omega)
  · simp only [h, ↓reduceDIte, Equiv.refl_apply]
theorem basisBits_barrelSysPerm_low (anc : ℕ) (x : Fin (2 ^ systemQubits))
    (q : Wire systemQubits) (hq : q.val < 3924) :
    basisBits systemQubits (barrelSysPerm anc x) q =
      if h : anc < 218 then
        if h0 : q.val < 18 then
          basisBits systemQubits x ⟨18 * anc + q.val, by change _ < 3948; omega⟩
        else if h1 : 18 * anc ≤ q.val ∧ q.val < 18 * anc + 18 then
          basisBits systemQubits x ⟨q.val - 18 * anc, by change _ < 3948; omega⟩
        else basisBits systemQubits x q
      else basisBits systemQubits x q := by
  unfold barrelSysPerm
  by_cases h : anc < 218
  · simp only [h, ↓reduceDIte]
    let g : Equiv.Perm (Fin numElectrons) := Equiv.swap (0 : Fin 218) ⟨anc, h⟩
    let eQ : Fin 218 := ⟨q.val / 18, div_18_lt_numElectrons hq⟩
    have hw_val : (permElectronWire g q).val = 18 * (g eQ).val + q.val % 18 := by
      change (permElectronWireFun g q).val = _
      unfold permElectronWireFun
      rw [PosSlots24MergedVepBound.dite_eq_of_pos hq]
    rw [permElectron, basisBits_permElectron (permElectronWire g) x q]
    by_cases h0 : q.val < 18
    · rw [PosSlots24MergedVepBound.dite_eq_of_pos h0]
      have he0 : eQ = (0 : Fin 218) := Fin.ext (by dsimp [eQ]; omega)
      exact congrArg (basisBits _ x) (Fin.ext (by
        rw [hw_val, he0, Equiv.swap_apply_left]; dsimp; omega))
    · rw [PosSlots24MergedVepBound.dite_eq_of_neg h0]
      by_cases h1 : 18 * anc ≤ q.val ∧ q.val < 18 * anc + 18
      · rw [PosSlots24MergedVepBound.dite_eq_of_pos h1]
        have heA : eQ = ⟨anc, h⟩ := Fin.ext (by dsimp [eQ]; omega)
        have hgeA : g eQ = (0 : Fin 218) := by dsimp [g]; rw [heA, Equiv.swap_apply_right]
        exact congrArg (basisBits _ x) (Fin.ext (by
          rw [hw_val, hgeA]; change 18 * 0 + q.val % 18 = q.val - 18 * anc; omega))
      · rw [PosSlots24MergedVepBound.dite_eq_of_neg h1]
        have hne0 : eQ ≠ 0 :=
          fun he ↦ h0 (by have := congrArg Fin.val he; dsimp [eQ] at this; omega)
        have hneA : eQ ≠ ⟨anc, h⟩ :=
          fun he ↦ h1 (by have := congrArg Fin.val he; dsimp [eQ] at this; omega)
        exact congrArg (basisBits _ x) (Fin.ext (by
          rw [hw_val, Equiv.swap_apply_of_ne_of_ne hne0 hneA]; dsimp [eQ]; omega))
  · simp only [h, ↓reduceDIte, Equiv.refl_apply]
noncomputable def slot2RawKickDiag (cfg : Configuration) (nuc : ℕ) : Operator
    (2 ^ systemQubits) := Matrix.diagonal fun z : Fin (2 ^ systemQubits) ↦ if h : nuc < 216
    then dyadicTurn 48 (∑ w : Fin 3, (∑ e : Fin numElectrons, ((u18GridEquiv ((rEl_sp
    e).extractIndex z) w).val : ℤ)) * (nuclearM48 cfg ⟨nuc, h⟩ w : ℤ)) else 1
open NuclearTwistRealizes
    (twistCorePermFn twistCorePhase twistCorePermFn_high_eq) in
theorem sysBlockAtPayloadGen_uTwist_slot2_eq (cfg : Configuration) (p80 : BitAssignment 80) :
    sysBlockAtPayloadGen hkFlag80 (slot2UTwistParam true pos24_22_le_80 cfg).1 false p80 =
      slot2RawKickDiag cfg (payloadNucNat p80) *
        (fwdPermUnitary ((barrelSysPerm (payloadAncNat p80)).trans xor32SysPerm)).1 := by
  let σ_tw := (barrelSysPerm (payloadAncNat p80)).trans xor32SysPerm
  let N80 := NuclearTwistAndXor654Concrete.fullSysCoreWires 80
  let rId := QRegExt.idReg N80
  ext x' x
  rw [sysBlockAtPayloadGen_apply]
  let colT : Fin (2 ^ N80) := coreIdxOf hkFlag80 false p80 x
  let rowT : Fin (2 ^ N80) := coreIdxOf hkFlag80 false p80 x'
  generalize hγ_def : basisBits N80 colT = γ
  change (slot2UTwistParam true pos24_22_le_80 cfg).1 rowT colT = _
  rw [show (slot2UTwistParam true pos24_22_le_80 cfg).1 rowT colT =
      ((slot2UTwistParam true pos24_22_le_80 cfg).1.mulVec (basisKet γ)) rowT by
        rw [← hγ_def, show basisKet (basisBits N80 colT) = Pi.single colT (1 : ℂ) from
          congrArg (Pi.single · (1 : ℂ)) ((basisBitsEquiv N80).symm_apply_apply colT),
          Matrix.mulVec_single_one, Matrix.col_apply],
    slot2UTwistParam_mulVec_basisKet true pos24_22_le_80 cfg γ]
  have hγ_bits (q : Wire N80) : γ q = coreBetaOf false p80 x ⟨q.val, Nat.lt_of_lt_of_eq
      q.isLt (pos24_core80_eq_twist80.symm.trans hkFlag80.symm)⟩ :=
    hγ_def ▸ coreIdxOf_hkFlag80_bits false p80 x
      ⟨q.val, Nat.lt_of_lt_of_eq q.isLt pos24_core80_eq_twist80.symm⟩
  have hw2 : γ (NuclearTwistAndXor654Concrete.wSlot2 rId) = 0 :=
    (hγ_bits _).trans (coreBetaOf_mid false p80 x _ (by decide) (by decide))
  have hw1 : γ (NuclearTwistAndXor654Concrete.wSlot1 rId) = 0 :=
    (hγ_bits _).trans (coreBetaOf_mid false p80 x _ (by decide) (by decide))
  have hw0 : γ (NuclearTwistAndXor654Concrete.wSlot0 rId) = 0 := by
    rw [hγ_bits, coreBetaOf_mid false p80 x _ (by decide) (by decide)]
    simp
  have hreg8 (r : QRegister 8 N80) (off : ℕ) (hoff : off + 8 ≤ 80)
      (hr : ∀ i : Fin 8, (r i).val = 3954 + (off + i.val)) :
      regVal r γ = _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun i : Fin 8 ↦
        p80 (pos80SubIdx off 8 hoff i)) := by
    unfold regVal _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only
    rw [hγ_bits, show (⟨(r i).val, _⟩ : Wire posCoreWires) =
        rPosSubLocal (pos80SubIdx off 8 hoff i) from Fin.ext (hr i), coreBetaOf_payload]
  have hanc : regVal (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80 rId) γ =
      payloadAncNat p80 :=
    hreg8 _ 14 (by decide) fun i ↦ by change 3968 + i.val = 3954 + (14 + i.val); omega
  have hnuc : regVal (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80 rId) γ =
      payloadNucNat p80 :=
    hreg8 _ 6 (by decide) fun i ↦ by change 3960 + i.val = 3954 + (6 + i.val); omega
  set γ' := twistCorePermFn true pos24_22_le_80 γ
  let colTw : Fin (2 ^ N80) := coreIdxOf hkFlag80 false p80 (σ_tw x)
  have hperm_match : γ' = basisBits N80 colTw := by
    funext q
    change γ' q = basisBits (FullSysCatSegmentBridge.fullSysCoreWires 80)
      (coreIdxOf hkFlag80 false p80 (σ_tw x))
      ⟨q.val, Nat.lt_of_lt_of_eq q.isLt pos24_core80_eq_twist80.symm⟩
    rw [coreIdxOf_hkFlag80_bits]
    by_cases hq3924 : q.val < 3924
    · have hlt_sys : q.val < systemQubits := Nat.lt_trans hq3924 (by decide)
      rw [coreBetaOf_lt_sys false p80 (σ_tw x) hlt_sys]
      dsimp only [σ_tw, Equiv.trans_apply, γ', twistCorePermFn, xor32BitFn]
      rw [basisBits_xor32SysPerm]
      suffices barrelBitFn true pos24_22_le_80 γ q =
          basisBits systemQubits (barrelSysPerm (payloadAncNat p80) x) ⟨q.val, hlt_sys⟩ by
        rw [this]
      rw [← hanc, basisBits_barrelSysPerm_low _ x ⟨q.val, hlt_sys⟩ hq3924]
      unfold barrelBitFn
      have hb_act : barrelActive true γ = true := by
        unfold barrelActive
        dsimp only [rId, N80] at hw2 hw1
        simp [hw2, hw1]
      by_cases hlt218 : regVal (NuclearTwistAndXor654Concrete.rAnchorIdx pos24_22_le_80
          (QRegExt.idReg N80)) γ < 218
      · rw [PosSlots24MergedVepBound.dite_eq_of_pos ⟨hb_act, hlt218⟩,
          PosSlots24MergedVepBound.dite_eq_of_pos hlt218]
        dsimp only
        split_ifs with _ h1
        · exact (hγ_bits _).trans (coreBetaOf_lt_sys false p80 x (by
            dsimp [N80, systemQubits, numElectrons, electronBits, projectileBits] at hlt218 ⊢
            omega))
        · exact (hγ_bits _).trans (coreBetaOf_lt_sys false p80 x (by
            dsimp [N80, systemQubits, numElectrons, electronBits, projectileBits] at hlt218 h1 ⊢
            omega))
        · exact (hγ_bits _).trans (coreBetaOf_lt_sys false p80 x hlt_sys)
      · rw [PosSlots24MergedVepBound.dite_eq_of_neg (fun hc ↦ hlt218 hc.2),
          PosSlots24MergedVepBound.dite_eq_of_neg hlt218, hγ_bits]
        exact coreBetaOf_lt_sys false p80 x hlt_sys
    · dsimp only [γ']
      rw [twistCorePermFn_high_eq true pos24_22_le_80 γ q (Nat.le_of_not_lt hq3924), hγ_bits]
      by_cases hlt_sys : q.val < systemQubits
      · rw [coreBetaOf_lt_sys false p80 x hlt_sys, coreBetaOf_lt_sys false p80 (σ_tw x) hlt_sys,
          Equiv.trans_apply, basisBits_xor32SysPerm,
          ite_eq_right (by omega : ¬(q.val < 3924 ∧ q.val % 6 = 5)),
          basisBits_barrelSysPerm_high _ x ⟨q.val, hlt_sys⟩ (Nat.le_of_not_lt hq3924)]
      · exact coreBetaOf_ge_sys false p80 x (σ_tw x) _ (Nat.le_of_not_lt hlt_sys)
  have hphase_match : twistCorePhase true pos24_22_le_80 cfg γ =
      slot2RawKickDiag cfg (payloadNucNat p80) (σ_tw x) (σ_tw x) := by
    unfold slot2RawKickDiag
    rw [Matrix.diagonal_apply_eq]
    have hγ'_high := twistCorePermFn_high_eq true pos24_22_le_80 γ
    have hw2' : γ' (NuclearTwistAndXor654Concrete.wSlot2
        (QRegExt.idReg N80)) = 0 := (hγ'_high _ (by decide)).trans hw2
    have hw1' : γ' (NuclearTwistAndXor654Concrete.wSlot1
        (QRegExt.idReg N80)) = 0 := (hγ'_high _ (by decide)).trans hw1
    have hw0' : γ' (NuclearTwistAndXor654Concrete.wSlot0
        (QRegExt.idReg N80)) = 0 := (hγ'_high _ (by decide)).trans hw0
    change dyadicTurn 48 (slot4TotalPhaseExp pos24_22_le_80 γ' +
      slot2TotalPhaseExp cfg pos24_22_le_80 γ') = _
    rw [show slot4TotalPhaseExp pos24_22_le_80 γ' = 0 by
      unfold slot4TotalPhaseExp
      rw [hw0']
      simp [show ((0 : ZMod 2) = 1) = False by decide], zero_add]
    have hcoin0 : coin0Active γ' = true := by
      unfold coin0Active
      dsimp only [N80] at hw2' hw1' hw0'
      simp [hw2', hw1', hw0']
    have hnuc' : regVal (NuclearTwistAndXor654Concrete.rNucIdx pos24_22_le_80
        (QRegExt.idReg N80)) γ' = payloadNucNat p80 :=
      (regVal_eq_of_wire_eq _ γ' γ fun i ↦
        hγ'_high _ (by change 3924 ≤ 3960 + i.val; omega)).trans hnuc
    have hel_val (e : Fin numElectrons) (w : Fin 3) :
        regVal (NuclearTwistAndXor654Concrete.rElecSlotAxis
            (QRegExt.idReg N80) e w) γ' =
          (u18GridEquiv ((rEl_sp e).extractIndex (σ_tw x)) w).val := by
      unfold regVal
      rw [show (fun j : Fin 6 ↦ γ' (NuclearTwistAndXor654Concrete.rElecSlotAxis
          (QRegExt.idReg N80) e w j)) =
          basisBits 6 (u18GridEquiv ((rEl_sp e).extractIndex (σ_tw x)) w) from funext fun j ↦ by
        rw [show u18GridEquiv ((rEl_sp e).extractIndex (σ_tw x)) w =
            u18AxisSplitEquiv ((rEl_sp e).extractIndex (σ_tw x)) w by fin_cases w <;> rfl]
        have h1 := congrFun hperm_match (NuclearTwistAndXor654Concrete.rElecSlotAxis
          (QRegExt.idReg N80) e w j)
        change γ' _ = basisBits (FullSysCatSegmentBridge.fullSysCoreWires 80)
          (coreIdxOf hkFlag80 false p80 (σ_tw x)) _ at h1
        have hlt_ew : (NuclearTwistAndXor654Concrete.rElecSlotAxis
            (QRegExt.idReg N80) e w j).val < systemQubits := by
          have he : e.val < 218 := e.isLt
          have := w.isLt
          have := j.isLt
          change 18 * e.val + 6 * w.val + j.val < 3948
          omega
        rw [h1, coreIdxOf_hkFlag80_bits, coreBetaOf_lt_sys false p80 (σ_tw x) hlt_ew,
          ← elecAxisField_eq_extract_u18]
        exact ((QRegister.basisBits_extractIndex _ (σ_tw x) j).trans
          (congrArg (basisBits systemQubits (σ_tw x)) (Fin.ext (by
            change 6 * (3 * e.val + w.val) + j.val = 18 * e.val + 6 * w.val + j.val
            omega)))).symm]
      exact (by decide : ∀ v : Fin 64,
        _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (basisBits 6 v) = v.val) _
    by_cases hlt216 : payloadNucNat p80 < 216
    · rw [PosSlots24MergedVepBound.dite_eq_of_pos hlt216]
      refine congrArg (dyadicTurn 48) (Finset.sum_congr rfl fun w _ ↦ ?_)
      unfold slot2AxisDelta slot2AxisSum slot2M48Val
      have hcond : coin0Active γ' = true ∧ regVal (NuclearTwistAndXor654Concrete.rNucIdx
          pos24_22_le_80 (QRegExt.idReg _)) γ' < 216 :=
        ⟨hcoin0, hnuc' ▸ hlt216⟩
      rw [PosSlots24MergedVepBound.dite_eq_of_pos hcond,
        (Fin.ext hnuc' : (⟨_, hcond.2⟩ : Fin 216) = ⟨payloadNucNat p80, hlt216⟩)]
      dsimp only [N80] at hel_val
      simp_rw [hel_val]
      push_cast
      rfl
    · rw [PosSlots24MergedVepBound.dite_eq_of_neg hlt216,
        show slot2TotalPhaseExp cfg pos24_22_le_80 γ' = 0 from Finset.sum_eq_zero fun _ _ ↦ by
          unfold slot2AxisDelta slot2M48Val
          dsimp only [N80] at hnuc'
          rw [PosSlots24MergedVepBound.dite_eq_of_neg (fun h ↦ hlt216 (hnuc' ▸ h.2)),
            mul_zero, Nat.cast_zero],
        dyadicTurn_zero]
  rw [show (slot2RawKickDiag cfg (payloadNucNat p80) * (fwdPermUnitary σ_tw).1) x' x =
      slot2RawKickDiag cfg (payloadNucNat p80) x' x' * (if σ_tw x = x' then 1 else 0) by
        unfold slot2RawKickDiag
        rw [Matrix.diagonal_mul, fwdPermUnitary_apply, Matrix.diagonal_apply_eq],
    hperm_match, Pi.smul_apply, smul_eq_mul]
  dsimp only [basisKet, basisState, N80]
  rw [show basisBits (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) colTw =
      basisBitsEquiv (NuclearTwistAndXor654Concrete.fullSysCoreWires 80) colTw from rfl,
    (basisBitsEquiv (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)).symm_apply_apply,
    Pi.single_apply,
    show (if rowT = colTw then (1 : ℂ) else 0) = if σ_tw x = x' then 1 else 0 from
      if_congr ⟨fun h ↦ (coreIdxOf_injective hkFlag80 false p80 h).symm,
        fun h ↦ congrArg (coreIdxOf hkFlag80 false p80) h.symm⟩ rfl rfl]
  by_cases hsx : σ_tw x = x'
  · subst hsx
    simp only [↓reduceIte, mul_one, hphase_match]
  · simp only [hsx, ↓reduceIte, mul_zero]
open FullSysCatSegmentBridge (fullSysQftCoreUnitary) in
theorem sysBlockAtPayloadGen_pos24ConjCore80_slot2_raw
    (qft : FullSysQft654Bundle) (hqft : qft.uQft654 = qft64Ideal654Unitary)
    (cfg : Configuration) (p80 : BitAssignment 80) :
    let W := ((List.ofFn fun e : Fin 218 ↦
        (rEl_sp e).embedUnitary (qft64OffsetUnitary3D (payloadB1Parity p80))).prod).1 *
      (slot2RawKickDiag cfg (payloadNucNat p80) *
        (fwdPermUnitary ((barrelSysPerm (payloadAncNat p80)).trans xor32SysPerm)).1)
    sysBlockAtPayloadGen hkFlag80 (pos24ConjCore80 qft cfg).1 false p80 =
      Wᴴ * Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
        if posPhaseBit true pos24TailSign pos24TailMag30 (coreBetaOf false p80 z)
        then (-1 : ℂ) else 1) * W := by
  intro W
  let U_qft := (fullSysQftCoreUnitary pos24_6_le_80 qft).1
  let U_tw := (slot2UTwistParam true pos24_22_le_80 cfg).1
  let D_pos := (castUnitaryPow2 hkFlag80 (uPosPhase true pos24TailSign pos24TailMag30)).1
  have hmul_anc {X Y : Operator (2 ^ fullSysCoreWires 80)}
      (hX : ∀ a, X * rAncFlag80.basisOutcomeProjector a = rAncFlag80.basisOutcomeProjector a * X)
      (hY : ∀ a, Y * rAncFlag80.basisOutcomeProjector a = rAncFlag80.basisOutcomeProjector a * Y)
      (a : Fin (2 ^ 86)) : (X * Y) * rAncFlag80.basisOutcomeProjector a =
        rAncFlag80.basisOutcomeProjector a * (X * Y) := by
    rw [Matrix.mul_assoc, hY a, ← Matrix.mul_assoc, hX a, Matrix.mul_assoc]
  have hQft_c (a : Fin (2 ^ 86)) : U_qft * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * U_qft := by
    obtain ⟨o3, o83, hfac⟩ := rAncFlag80_basisOutcomeProjector_factor a
    rw [hfac, ← Matrix.mul_assoc,
      show U_qft * (coreCosetB1Block pos24_6_le_80).basisOutcomeProjector o3 =
        (coreCosetB1Block pos24_6_le_80).basisOutcomeProjector o3 * U_qft by
      rw [← coreElecCosetB1_compose_rCoset3, basisOutcomeProjector_compose_local]
      dsimp only [U_qft, fullSysQftCoreUnitary]
      rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
        qftPreservesCoset3_of_eq_ideal qft hqft o3, QRegister.embedMatrix_mul],
      Matrix.mul_assoc,
      show U_qft * rAncRest83.basisOutcomeProjector o83 =
        rAncRest83.basisOutcomeProjector o83 * U_qft from
        QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
          (coreElecCosetB1Block pos24_6_le_80) rAncRest83 coreElecCosetB1_disjoint_rAncRest83
          qft.uQft654.1 o83, ← Matrix.mul_assoc]
  have hTw_c : ∀ a, U_tw * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * U_tw :=
    uTwistParam_cast_comm_highReg_proj pos24_core80_eq_twist80.symm cfg rAncFlag80
      rAncFlag80_wire_ge_3948
  have hD_c (a : Fin (2 ^ 86)) : D_pos * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * D_pos := by
    rw [QRegister.basisOutcomeProjector_eq_diagonal]
    exact uPosPhase_cast_comm_diagonal hkFlag80 true pos24TailSign pos24TailMag30 _
  have hD_diag : sysBlockAtPayloadGen hkFlag80 D_pos false p80 =
      Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
        if posPhaseBit true pos24TailSign pos24TailMag30 (coreBetaOf false p80 z)
        then (-1 : ℂ) else 1) :=
    (fun {kC : ℕ} (hk : posCoreWires = kC) ↦ by
      subst hk
      ext x' x
      rw [sysBlockAtPayloadGen_apply]
      change (Matrix.diagonal fun g : Fin (2 ^ posCoreWires) ↦
          if posPhaseBit true pos24TailSign pos24TailMag30 (basisBits posCoreWires g)
          then (-1 : ℂ) else 1) (coreIdxOf rfl false p80 x') (coreIdxOf rfl false p80 x) = _
      by_cases hxx : x' = x
      · subst hxx
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
          show basisBits posCoreWires (coreIdxOf rfl false p80 x') = coreBetaOf false p80 x' from
            (basisBitsEquiv posCoreWires).apply_symm_apply _]
      · rw [Matrix.diagonal_apply_ne _ (fun h ↦ hxx (coreIdxOf_injective rfl false p80 h)),
          Matrix.diagonal_apply_ne _ hxx]) hkFlag80
  change sysBlockAtPayloadGen hkFlag80 ((U_qft * U_tw)ᴴ * D_pos * (U_qft * U_tw)) false p80 = _
  rw [sysBlockAtPayloadGen_conj_of_preserves hkFlag80 (U_qft * U_tw) D_pos false p80
      (preservesCoreAnc_of_comm_rAncFlag80 _ (hmul_anc hQft_c hTw_c) false p80)
      (preservesCoreAnc_of_comm_rAncFlag80 _ (hmul_anc hD_c (hmul_anc hQft_c hTw_c)) false p80),
    sysBlockAtPayloadGen_mul_of_preserves hkFlag80 U_qft U_tw false p80
      (preservesCoreAnc_of_comm_rAncFlag80 _ hTw_c false p80),
    sysBlockAtPayloadGen_fullSysQft_eq qft hqft false p80,
    sysBlockAtPayloadGen_uTwist_slot2_eq cfg p80, hD_diag]
theorem diagonal_comm_embedMatrix_of_agreeOutside {m N : ℕ} (r : QRegister m N)
    (f : Fin (2 ^ N) → ℂ) (hag_eq : ∀ z' z, r.AgreeOutside z' z → f z' = f z)
    (M : Operator (2 ^ m)) : Matrix.diagonal f * r.embedMatrix M = r.embedMatrix M *
    Matrix.diagonal f := by
  ext z' z
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hag : r.AgreeOutside z' z
  · rw [hag_eq z' z hag, mul_comm]
  · rw [embedMatrix_entry_of_not_agreeOutside r M hag, mul_zero, zero_mul]
theorem rEl_sp_disjoint_rProj24 (e : Fin numElectrons) :
    (rEl_sp e).DisjointWires rProj24_sp := by
  rw [QRegister.disjoint_iff]
  intro j₁ j₂ h
  have hv := congrArg Fin.val h
  have he : e.val < 218 := e.isLt
  have hj₁ := j₁.isLt
  have hj₂ := j₂.isLt
  dsimp [rEl_sp, rProj24_sp, qreg_block_wires_slot2] at hv
  omega
theorem list_ofFn_rEl_comm_rProj24 (V : Fin 218 → Unitary (2 ^ 18)) (M : Operator (2 ^ 24)) :
    ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (V e)).prod).1 *
    rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M *
    ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (V e)).prod).1 :=
  list_prod_comm_of_mem _ _ fun U hU ↦ by
    rcases List.mem_ofFn.mp hU with ⟨e, rfl⟩
    exact QRegister.embedMatrix_comm_of_disjoint (rEl_sp e) rProj24_sp
      (rEl_sp_disjoint_rProj24 e) (V e).1 M
theorem extractIndex_rEl_eq_of_agreeOutside_rProj24
    {z' z : Fin (2 ^ systemQubits)} (hag : rProj24_sp.AgreeOutside z' z)
    (e : Fin numElectrons) :
    (rEl_sp e).extractIndex z' = (rEl_sp e).extractIndex z :=
  (basisBitsEquiv 18).injective (funext fun j ↦ by
    change basisBits 18 _ j = basisBits 18 _ j
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    exact hag (rEl_sp e j) fun ⟨k, hk⟩ ↦
      (QRegister.disjoint_iff.mp (rEl_sp_disjoint_rProj24 e)) j k hk.symm)
theorem slot2RawKickDiag_comm_rProj24 (cfg : Configuration) (nuc : ℕ)
    (M : Operator (2 ^ 24)) :
    slot2RawKickDiag cfg nuc * rProj24_sp.embedMatrix M =
      rProj24_sp.embedMatrix M * slot2RawKickDiag cfg nuc := by
  unfold slot2RawKickDiag
  refine diagonal_comm_embedMatrix_of_agreeOutside rProj24_sp _ (fun z' z hag ↦ ?_) M
  by_cases h : nuc < 216
  · simp only [h, ↓reduceDIte]
    simp_rw [extractIndex_rEl_eq_of_agreeOutside_rProj24 hag]
  · simp only [h, ↓reduceDIte]
theorem fwdPermUnitary_xor32_comm_rProj24 (M : Operator (2 ^ 24)) :
    (fwdPermUnitary xor32SysPerm).1 * rProj24_sp.embedMatrix M =
      rProj24_sp.embedMatrix M * (fwdPermUnitary xor32SysPerm).1 := by
  have hoff : offsetSysUnitary = fwdPermUnitary xor32SysPerm * smToTwos654SysUnitary := by
    rw [offsetSysUnitary_eq_fwdPerm, fwdPermUnitary_trans]
    rfl
  have hsq : smToTwos654SysUnitary.1 * smToTwos654SysUnitary.1 = 1 := by
    nth_rw 1 [← smToTwos654SysUnitary_sa]
    exact smToTwos654SysUnitary.2.1
  have hfac : offsetSysUnitary.1 * smToTwos654SysUnitary.1 =
      (fwdPermUnitary xor32SysPerm).1 := by
    rw [hoff, Submonoid.coe_mul, Matrix.mul_assoc, hsq, Matrix.mul_one]
  rw [← hfac, Matrix.mul_assoc, smToTwos654SysUnitary_comm_embedMatrix M,
    ← Matrix.mul_assoc, offsetSysUnitary, list_ofFn_rEl_comm_rProj24 _ M, Matrix.mul_assoc]
set_option exponentiation.threshold 32 in
theorem fwdPermUnitary_barrel_comm_rProj24 (anc : ℕ) (M : Operator (2 ^ 24)) :
    (fwdPermUnitary (barrelSysPerm anc)).1 * rProj24_sp.embedMatrix M =
      rProj24_sp.embedMatrix M * (fwdPermUnitary (barrelSysPerm anc)).1 := by
  have hself (x : Fin (2 ^ systemQubits)) : barrelSysPerm anc (barrelSysPerm anc x) = x := by
    unfold barrelSysPerm
    by_cases h : anc < 218
    · simp only [h, ↓reduceDIte]
      let g : Equiv.Perm (Fin numElectrons) := Equiv.swap (0 : Fin 218) ⟨anc, h⟩
      refine (basisBitsEquiv systemQubits).injective (funext fun q ↦ ?_)
      change basisBits systemQubits (permElectron g (permElectron g x)) q = _
      rw [permElectron, basisBits_permElectron (permElectronWire g) _ q,
        basisBits_permElectron (permElectronWire g) x _,
        show permElectronWire g (permElectronWire g q) =
          (permElectronWire g).symm (permElectronWire g q) by
          change permElectronWireFun g _ = permElectronWireFun g.symm _
          rw [Equiv.symm_swap], Equiv.symm_apply_apply]
    · simp only [h, ↓reduceDIte, Equiv.refl_apply]
  have hfwd (a b : Fin (2 ^ systemQubits))
      (heq : (rProj24_sp.basisSplitEquiv a).2 = (rProj24_sp.basisSplitEquiv b).2) :
      (rProj24_sp.basisSplitEquiv (barrelSysPerm anc a)).2 =
        (rProj24_sp.basisSplitEquiv (barrelSysPerm anc b)).2 := by
    have hlow (u : Wire systemQubits) (hu : u.val < 3924) :
        basisBits systemQubits a u = basisBits systemQubits b u := by
      simpa only [QRegister.basisSplitEquiv_apply_snd] using congrFun heq ⟨u, fun ⟨j, hj⟩ ↦ by
        have hv := congrArg Fin.val hj; dsimp [rProj24_sp, qreg_block_wires_slot2] at hv; omega⟩
    funext ⟨w, hw⟩
    rw [QRegister.basisSplitEquiv_apply_snd, QRegister.basisSplitEquiv_apply_snd]
    have hw_lt : w.val < 3924 := by
      by_contra hge
      have hw_sys : w.val < 3948 := w.isLt
      exact hw ⟨⟨w.val - 3924, by omega⟩, Fin.ext (by
        dsimp [rProj24_sp, qreg_block_wires_slot2]; omega)⟩
    unfold barrelSysPerm
    by_cases h : anc < 218
    · simp only [h, ↓reduceDIte]
      let g : Equiv.Perm (Fin numElectrons) := Equiv.swap (0 : Fin 218) ⟨anc, h⟩
      rw [permElectron, basisBits_permElectron (permElectronWire g) a w,
        basisBits_permElectron (permElectronWire g) b w]
      refine hlow (permElectronWire g w) ?_
      change (permElectronWireFun g w).val < 3924
      unfold permElectronWireFun
      rw [PosSlots24MergedVepBound.dite_eq_of_pos hw_lt]
      have hlt_g : (g ⟨w.val / 18, div_18_lt_numElectrons hw_lt⟩).val < 218 :=
        (g ⟨w.val / 18, div_18_lt_numElectrons hw_lt⟩).isLt
      change 18 * (g ⟨w.val / 18, div_18_lt_numElectrons hw_lt⟩).val + w.val % 18 < 3924
      omega
    · simp only [h, ↓reduceDIte, Equiv.refl_apply, hlow w hw_lt]
  exact permMatrix_comm_embedMatrix_gen rProj24_sp (barrelSysPerm anc) hself
    (fun z ↦ (basisBitsEquiv 24).injective (funext fun j ↦ by
      change basisBits 24 _ j = basisBits 24 _ j
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      exact basisBits_barrelSysPerm_high anc z (rProj24_sp j)
        (by dsimp [rProj24_sp, qreg_block_wires_slot2]; omega)))
    (fun z₁ z₂ ↦ ⟨fun h ↦ by simpa only [hself] using hfwd _ _ h, hfwd z₁ z₂⟩) M
theorem root_bitsVal_z2BitOfNat_of_lt_slot2 {m x : ℕ} (hx : x < 2 ^ m) :
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin m ↦
      z2BitOfNat x j.val) = x :=
  bitsVal_z2BitOfNat_of_lt hx
theorem slotSubGridCoord64_coreBetaOf_slot2_eq (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ systemQubits)) (e : Fin 218) :
    slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) (coreBetaOf s0 p80 z) =
      slotCoordSys z e := by
  funext w
  apply Fin.ext
  let m : Fin 654 := ⟨3 * e.val + w.val, by
    have := e.isLt
    have := w.isLt
    omega⟩
  have hbits : (fun j : Fin 6 ↦
      coreBetaOf s0 p80 z (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j)) =
      fun j : Fin 6 ↦ basisBits 6 (elecAxisField z e w) ⟨5 - j.val, by omega⟩ := by
    funext j
    have hw_eq : axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j =
        ⟨(elec654Axes m ⟨5 - j.val, by omega⟩).val,
          Nat.lt_trans (elec654Axes m ⟨5 - j.val, by omega⟩).isLt lt_sys_4034⟩ := Fin.ext (by
      have := e.isLt
      have := w.isLt
      have := j.isLt
      change 18 * e.val + (6 * w.val + (5 - j.val)) = 6 * (3 * e.val + w.val) + (5 - j.val)
      omega)
    rw [hw_eq, coreBetaOf_lt3948 s0 p80 z (elec654Axes m ⟨5 - j.val, by omega⟩)]
    exact (QRegister.basisBits_extractIndex (elec654Axes m) z ⟨5 - j.val, by omega⟩).symm
  change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 6 ↦
    coreBetaOf s0 p80 z (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) e) w j)) =
    (bitRev6Equiv (u18GridEquiv ((rEl_sp e).extractIndex z) w)).val
  have hrev : ∀ v : Fin 64,
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 6 ↦
        basisBits 6 v ⟨5 - j.val, by omega⟩) =
        (bitRev6Equiv v).val := by decide
  rw [hbits, hrev]
  change (bitRev6Equiv (elecAxisField z e w)).val =
    (bitRev6Equiv (u18AxisSplitEquiv ((rEl_sp e).extractIndex z) w)).val
  rw [elecAxisField_eq_extract_u18]
theorem pos24ConjCore80_slice_slot2_comm_rProj24
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (hqft : qft.uQft654 = qft64Ideal654Unitary) (cfg : Configuration) (p80 : BitAssignment 80)
    (M : Operator (2 ^ 24)) :
    sysBlockAtPayloadGen hkFlag80 (pos24ConjCore80 qft cfg).1 false p80 *
        rProj24_sp.embedMatrix M =
      rProj24_sp.embedMatrix M *
        sysBlockAtPayloadGen hkFlag80 (pos24ConjCore80 qft cfg).1 false p80 := by
  rw [sysBlockAtPayloadGen_pos24ConjCore80_slot2_raw qft hqft cfg p80]
  set W := ((List.ofFn fun e : Fin 218 ↦
      (rEl_sp e).embedUnitary (qft64OffsetUnitary3D (payloadB1Parity p80))).prod).1 *
    (slot2RawKickDiag cfg (payloadNucNat p80) *
      (fwdPermUnitary ((barrelSysPerm (payloadAncNat p80)).trans xor32SysPerm)).1)
  have hmul {X Y P : Operator (2 ^ systemQubits)} (hX : X * P = P * X) (hY : Y * P = P * Y) :
      (X * Y) * P = P * (X * Y) := by
    rw [Matrix.mul_assoc, hY, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  have hOut (N : Operator (2 ^ 24)) :
      W * rProj24_sp.embedMatrix N = rProj24_sp.embedMatrix N * W :=
    hmul (list_ofFn_rEl_comm_rProj24 _ N) (hmul (slot2RawKickDiag_comm_rProj24 cfg _ N) (by
      rw [fwdPermUnitary_trans, Submonoid.coe_mul]
      exact hmul (fwdPermUnitary_xor32_comm_rProj24 N) (fwdPermUnitary_barrel_comm_rProj24 _ N)))
  refine hmul (hmul (by
    simpa only [Matrix.conjTranspose_mul, QRegister.embedMatrix_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using (congrArg Matrix.conjTranspose (hOut Mᴴ)).symm)
    (diagonal_comm_embedMatrix_of_agreeOutside rProj24_sp _
      (fun z' z hag ↦ congrArg (fun b : Bool ↦ if b then (-1 : ℂ) else 1) ?_) M)) (hOut M)
  let β₁ := coreBetaOf false p80 z'
  let β₂ := coreBetaOf false p80 z
  let rC := QRegExt.ofFin posCoreWires
  have hw : ∀ (q : Wire posCoreWires), systemQubits ≤ q.val → β₁ q = β₂ q :=
    coreBetaOf_ge_sys false p80 z' z
  have h3954 {k : ℕ} : systemQubits ≤ 3954 + k := Nat.le_trans (by decide) (Nat.le_add_right 3954 _)
  have hreg {m : ℕ} (r : QRegister m posCoreWires) (hr : ∀ i, systemQubits ≤ (r i).val) :
      regVal r β₁ = regVal r β₂ := regVal_eq_of_wire_eq r β₁ β₂ fun i ↦ hw (r i) (hr i)
  have hpar (r : QRegister 3 posCoreWires) (hr : ∀ i, systemQubits ≤ (r i).val) :
      parity3OfReg r β₁ = parity3OfReg r β₂ :=
    funext fun i ↦ congrArg (fun b ↦ decide (b = 1)) (hw (r i) (hr i))
  have hslot (e : Fin 218) :
      slotSubGridCoord64 (rElecSlot rC e) β₁ = slotSubGridCoord64 (rElecSlot rC e) β₂ := by
    rw [slotSubGridCoord64_coreBetaOf_slot2_eq, slotSubGridCoord64_coreBetaOf_slot2_eq,
      slotCoordSys, slotCoordSys, extractIndex_rEl_eq_of_agreeOutside_rProj24 hag e]
  have hf21 : fineCoordOfReg21 (rHeadFine21 rC) β₁ = fineCoordOfReg21 (rHeadFine21 rC) β₂ :=
    funext fun _ ↦ Fin.ext (hreg _ fun _ ↦ h3954)
  have hhead : headPhaseBitSpec β₁ = headPhaseBitSpec β₂ := by
    unfold headPhaseBitSpec
    simp only [rC, hw (wSlot0Core rC) (by decide), hw (wSlot1Core rC) (by decide),
      hw (wSlot2Core rC) (by decide), hw (wSubReject rC) (by decide),
      hw (wIsHead rC) (by decide), hw (wHeadThresh rC) (by decide),
      hreg (rNucIdx rC) (fun _ ↦ h3954), hreg (rAnchorIdx rC) (fun _ ↦ h3954),
      hf21, hpar (rCosetB0 rC) (fun _ ↦ h3954), hslot]
  have htail : tailAndSlackPhaseBitSpec true pos24TailSign pos24TailMag30 β₁ =
      tailAndSlackPhaseBitSpec true pos24TailSign pos24TailMag30 β₂ := by
    unfold tailAndSlackPhaseBitSpec
    simp only [rC, hw (wSlot0Core rC) (by decide), hw (wSlot1Core rC) (by decide),
      hw (wSlot2Core rC) (by decide), hw (wSubReject rC) (by decide),
      hw (wIsHead rC) (by decide), hw (wRejectZero rC) (by decide),
      hreg (rNucIdx rC) (fun _ ↦ h3954), hreg (rAnchorIdx rC) (fun _ ↦ h3954),
      hreg (rPartnerIdx rC) (fun _ ↦ h3954), hreg (rTailKeep30 rC) (fun _ ↦ h3954),
      hpar (rCosetB0 rC) (fun _ ↦ h3954), hpar (rCosetB1 rC) (fun _ ↦ h3954), hslot]
  unfold posPhaseBit
  change Bool.xor (headPhaseBitSpec β₁) _ = Bool.xor (headPhaseBitSpec β₂) _
  rw [hhead, htail]
theorem tierBB2RawId_comm_rProj24 (cfg : Configuration) (M : Operator (2 ^ 24)) :
    tierBB2RawId cfg * rProj24_sp.embedMatrix M =
      rProj24_sp.embedMatrix M * tierBB2RawId cfg := by
  change coherentSysOp80 tierBQftFull cfg false (pos80IdealDist false) *
      rProj24_sp.embedMatrix M =
    rProj24_sp.embedMatrix M * coherentSysOp80 tierBQftFull cfg false (pos80IdealDist false)
  unfold coherentSysOp80
  rw [Finset.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun p80 _ ↦ ?_
  rw [smul_mul_assoc, mul_smul_comm,
    pos24ConjCore80_slice_slot2_comm_rProj24 tierBQftFull rfl cfg p80 M]
def slot2HeadBchBit (y0 : NyqGrid3D64) (th : Bool) (z : Fin (2 ^ systemQubits)) : Bool :=
  let hs : Finset (Fin 218) := Finset.univ.filter (fun e ↦ decide (slotCoordSys z e = y0))
  zeroParityThreshExp true th (proj38ZeroBit hs) (proj38OddXorZeroBit hs)
theorem diagonal_conj_rk1_sp (φ ψ : Fin (2 ^ 18) → ℂ) : Matrix.diagonal φ * rk1_sp ψ *
    (Matrix.diagonal φ)ᴴ = rk1_sp (fun u ↦ φ u * ψ u) := by
  rw [Matrix.diagonal_conjTranspose]
  ext u v
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply, rk1_sp, Matrix.of_apply,
    star_mul']
  ring
theorem sysNucDiag48_conj_op_veeSubGridKet (c : Configuration) (l : Fin 216) (b : NyqParity3D)
    (y0 : NyqGrid3D64) (e : Fin 218) : (sysNucDiag48 c l).1 * op_sp (veeSubGridKet b y0) e *
    (sysNucDiag48 c l).1ᴴ = op_sp (uenSubGridKet48 c l b y0) e := by
  unfold sysNucDiag48 op_sp
  rw [rEl_prod_conj_embed_eq_single (fun _ ↦ oneElecNucDiag48 c l) e
    (rk1_sp (veeSubGridKet b y0))]
  simp only [QRegister.embedUnitary_val, ← QRegister.embedMatrix_conjTranspose,
    ← QRegister.embedMatrix_mul]
  exact congrArg (rEl_sp e).embedMatrix (diagonal_conj_rk1_sp _ _)
theorem uenSubGridKet48_norm_sq (c : Configuration) (l : Fin 216)
    (b : NyqParity3D) (y0 : NyqGrid3D64) :
    (∑ u : Fin (2 ^ 18),
      star (uenSubGridKet48 c l b y0 u) * uenSubGridKet48 c l b y0 u) = 1 := by
  have hunit : (oneElecNucDiag48 c l).1ᴴ * (oneElecNucDiag48 c l).1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (oneElecNucDiag48 c l).2.1
  rw [← veeSubGridKet_norm_sq b y0]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  have hu := congrFun (congrFun hunit u) u
  have hcoe : (oneElecNucDiag48 c l).1 = Matrix.diagonal (fun w : Fin (2 ^ 18) ↦
      oneElectronPhase48 c l (shiftedMom3D (elecOffsetGridEquiv18 w))) := rfl
  rw [hcoe, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at hu
  simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply] at hu
  unfold uenSubGridKet48
  rw [star_mul']
  linear_combination (star (veeSubGridKet b y0 u) * veeSubGridKet b y0 u) * hu
theorem sum_diagonal_eq_slot2 {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℂ) :
    (∑ i ∈ s, Matrix.diagonal (f i)) = Matrix.diagonal (fun z ↦ ∑ i ∈ s, f i z) := by
  induction s using Finset.cons_induction with
  | empty => exact Matrix.diagonal_zero.symm
  | cons a t _ ih =>
      simp only [Finset.sum_cons, ih]
      ext x y
      by_cases hxy : x = y <;> simp [hxy]
theorem smul_add_diagonal_eq {d : ℕ} (α : ℂ) (f g : Fin d → ℂ) :
    α • (Matrix.diagonal f + Matrix.diagonal g) =
      Matrix.diagonal (fun z ↦ α * (f z + g z)) := by
  ext x y
  by_cases hxy : x = y <;> simp [hxy, mul_add]
theorem diag_bch_lcu_eq_one_sub_of_cubic_zero {d : ℕ} {N P U : Operator d} {count : Fin d → ℕ}
    {mEntry : Fin d → ℂ} (hcub : N * (N - 1) * (N - (2 : ℂ) • 1) * P = 0) (hU : Uᴴ * U = 1)
    (hdiag : U * N = Matrix.diagonal (fun z ↦ (count z : ℂ)) * U)
    (hm : ∀ z : Fin d, count z ≤ 2 → mEntry z = (1 : ℂ) - (count z : ℂ)) :
    (Uᴴ * Matrix.diagonal mEntry * U) * P = (1 - N) * P := by
  let D : Operator d := Matrix.diagonal fun z ↦ (count z : ℂ)
  have h1 : U * (N - 1) = (D - 1) * U := by
    rw [Matrix.mul_sub, hdiag, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  have h2 : U * (N - (2 : ℂ) • 1) = (D - (2 : ℂ) • 1) * U := by
    rw [Matrix.mul_sub, hdiag, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hcomm3 : D * (D - 1) * (D - (2 : ℂ) • 1) * U =
      U * (N * (N - 1) * (N - (2 : ℂ) • 1)) := by
    rw [Matrix.mul_assoc (D * (D - 1)), ← h2, ← Matrix.mul_assoc (D * (D - 1)) U,
      Matrix.mul_assoc D (D - 1) U, ← h1, ← Matrix.mul_assoc D U, ← hdiag]
    simp only [Matrix.mul_assoc]
  have hD_cub : D * (D - 1) * (D - (2 : ℂ) • 1) * (U * P) = 0 := by
    rw [← Matrix.mul_assoc _ U P, hcomm3, Matrix.mul_assoc U _ P, hcub, Matrix.mul_zero]
  have hM_eq : Matrix.diagonal mEntry * (U * P) = ((1 : Operator d) - D) * (U * P) := by
    have hs : ∀ c : ℂ, D - c • 1 = Matrix.diagonal (fun y ↦ (count y : ℂ) - c) := fun c ↦ by
      ext a b; by_cases hab : a = b <;> simp [D, hab]
    have hs1D : (1 : Operator d) - D = Matrix.diagonal (fun y ↦ (1 : ℂ) - (count y : ℂ)) := by
      ext a b; by_cases hab : a = b <;> simp [D, hab]
    rw [hs1D]
    ext x z
    simp only [Matrix.diagonal_mul]
    by_cases hQ : (U * P) x z = 0
    · simp [hQ]
    · have h0 := congrFun (congrFun hD_cub x) z
      rw [show D - 1 = D - (1 : ℂ) • 1 by rw [one_smul], hs 1, hs 2,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
        Matrix.zero_apply] at h0
      have hle : count x ≤ 2 := by
        rcases mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hQ) with h01 | hc2
        · rcases mul_eq_zero.mp h01 with hc0 | hc1
          · have := Nat.cast_eq_zero.mp hc0; omega
          · have := Nat.cast_eq_one.mp (sub_eq_zero.mp hc1); omega
        · have h2' : (count x : ℂ) = ((2 : ℕ) : ℂ) := by push_cast; linear_combination hc2
          have := Nat.cast_inj.mp h2'; omega
      rw [hm x hle]
  rw [Matrix.mul_assoc (Uᴴ * Matrix.diagonal mEntry) U P,
    Matrix.mul_assoc Uᴴ (Matrix.diagonal mEntry) (U * P), hM_eq, Matrix.sub_mul,
    Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc Uᴴ U P,
    ← Matrix.mul_assoc D U P, ← hdiag, ← Matrix.mul_assoc Uᴴ (U * N) P,
    ← Matrix.mul_assoc Uᴴ U N, hU, Matrix.one_mul, Matrix.one_mul,
    Matrix.sub_mul, Matrix.one_mul]
theorem mul_adj_conjTranspose_mul_self {d : ℕ} {W D : Operator d} (hW : Wᴴ * W = 1)
    (hD' : D * Dᴴ = 1) : (W * Dᴴ)ᴴ * (W * Dᴴ) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Wᴴ, hW, Matrix.one_mul, hD']
theorem mul_adj_mul_conjTranspose_self {d : ℕ} {W D : Operator d} (hD : Dᴴ * D = 1)
    (hW' : W * Wᴴ = 1) : (W * Dᴴ) * (W * Dᴴ)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Dᴴ, hD, Matrix.one_mul, hW']
theorem conj_outer_inner_eq {d : ℕ} (D W M : Operator d) :
    D * (Wᴴ * M * W) * Dᴴ = (W * Dᴴ)ᴴ * M * (W * Dᴴ) := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
theorem conj_finset_sum_eq {d : ℕ} {ι : Type*} (s : Finset ι) (A B : Operator d)
    (f : ι → Operator d) :
    A * (∑ i ∈ s, f i) * B = ∑ i ∈ s, A * f i * B := by
  rw [Matrix.mul_sum, Finset.sum_mul]
theorem mul_eq_left_mul_of_conj_eq {d : ℕ} {U X N : Operator d} (hUU' : U * Uᴴ = 1)
    (hconj : Uᴴ * X * U = N) : U * N = X * U := by
  rw [← hconj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
theorem mul_right_eq_of_eq {d : ℕ} {A A' P R : Operator d}
    (hA : A = A') (hR : A' * P = R) : A * P = R :=
  hA ▸ hR
noncomputable def uenSubGridRaw48 (c : Configuration) (K128 : NyqFine3D128 → ℝ) :
    Operator (2 ^ systemQubits) :=
  (-((1 / 8 : ℝ) : ℂ)) • ∑ l : Fin 216, ∑ b : NyqParity3D, ∑ y : NyqGrid3D64,
    (K128 (nyq128Equiv3D (y, b)) : ℂ) • nTot_sp (uenSubGridKet48 c l b y)
noncomputable def pos24Slot2E2Const : ℝ :=
  -(27 : ℝ) * (∑ d : NyqFine3D128, kHead128 w128DualQ30 pos24CutNyq d) +
    uenMidpointShift pos24CutNyq pos24MinNyq
noncomputable def bModSlot248 (c : Configuration) : Operator (2 ^ systemQubits) :=
  uenSubGridRaw48 c w128DualQ30 - (pos24Slot2E2Const : ℂ) • (1 : Operator (2 ^ systemQubits))
theorem sum_op_sp_veeSubGridKet_eq_one (b : NyqParity3D) (e : Fin numElectrons) :
    (∑ y : NyqGrid3D64, op_sp (veeSubGridKet b y) e) = 1 := by
  have hrk : (∑ y : NyqGrid3D64, rk1_sp (veeSubGridKet b y)) = 1 := by
    ext u v
    rw [Matrix.sum_apply, Matrix.one_apply]
    exact veeSubGridKet_complete b u v
  unfold op_sp
  rw [← (rEl_sp e).embedMatrix_sum Finset.univ _, hrk, (rEl_sp e).embedMatrix_one]
theorem sum_smul_sum_sub_comm {M : Type*} [AddCommGroup M] [Module ℂ M] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (w : ι → ℂ) (f g : ι → κ → M) :
    (∑ y : ι, w y • ∑ e : κ, f y e) - (∑ y : ι, w y • ∑ e : κ, g y e) =
      ∑ e : κ, ((∑ y : ι, w y • f y e) - (∑ y : ι, w y • g y e)) := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun y e ↦ w y • g y e), ← Finset.sum_sub_distrib]
theorem uenSubGridRaw48_comm_of_nTot (c : Configuration) (K128 : NyqFine3D128 → ℝ)
    {X : Operator (2 ^ systemQubits)}
    (hnTot : ∀ χ : Fin (2 ^ 18) → ℂ, nTot_sp χ * X = X * nTot_sp χ) :
    uenSubGridRaw48 c K128 * X = X * uenSubGridRaw48 c K128 := by
  unfold uenSubGridRaw48
  simp only [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Matrix.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ congrArg _ (hnTot _))
theorem bModSlot248_inGridPerm (c : Configuration) (g : Equiv.Perm (Fin numElectrons))
    (a b : Fin (2 ^ systemQubits)) (_ha : IsGridState a) (_hb : IsGridState b) :
    bModSlot248 c (permElectron g a) (permElectron g b) = bModSlot248 c a b := by
  have hentry {N : ℕ} (e : Equiv.Perm (Fin N)) {A : Operator N}
      (hcomm : A * (permutationUnitary e).1 = (permutationUnitary e).1 * A) (x y : Fin N) :
      A (e x) (e y) = A x y := by
    have hv := congrArg (fun M : Operator N ↦ (M.mulVec (Pi.single y (1 : ℂ))) (e x)) hcomm
    have hlhs : ((A * (permutationUnitary e).1).mulVec (Pi.single y 1)) (e x) =
        A (e x) (e y) := by
      rw [← Matrix.mulVec_mulVec, permutationUnitary_mulVec_single, Matrix.mulVec_single_one]
      rfl
    have hrhs : (((permutationUnitary e).1 * A).mulVec (Pi.single y 1)) (e x) = A x y := by
      rw [← Matrix.mulVec_mulVec]
      change (Equiv.Perm.permMatrix ℂ (e⁻¹)).mulVec (A.mulVec (Pi.single y 1)) (e x) = A x y
      rw [Matrix.permMatrix_mulVec]
      change (A.mulVec (Pi.single y 1)) (e⁻¹ (e x)) = A x y
      rw [show e⁻¹ (e x) = x from e.symm_apply_apply x, Matrix.mulVec_single_one]
      rfl
    exact hlhs.symm.trans (hv.trans hrhs)
  refine hentry (permElectron g) ?_ a b
  unfold bModSlot248
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, uenSubGridRaw48_comm_of_nTot c w128DualQ30 fun χ ↦ by
      unfold nTot_sp nSub_sp op_sp
      rw [Finset.sum_mul, Matrix.mul_sum]
      exact (Finset.sum_congr rfl fun i _ ↦ emb_rEl_mul_pe_sp g i (rk1_sp χ)).trans
        (sum_perm_finset_eq Finset.univ g (fun _ ↦ by simp)
          (fun i ↦ (permutationUnitary (permElectron g)).1 * (rEl_sp i).embedMatrix (rk1_sp χ)))]
theorem bModSlot248_comm_rProj24 (c : Configuration) (M : Operator (2 ^ 24)) :
    bModSlot248 c * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * bModSlot248 c := by
  unfold bModSlot248
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, uenSubGridRaw48_comm_of_nTot c w128DualQ30 fun χ ↦ by
      unfold nTot_sp nSub_sp op_sp
      rw [Finset.sum_mul, Matrix.mul_sum]
      exact Finset.sum_congr rfl fun e _ ↦ QRegister.embedMatrix_comm_of_disjoint
        (rEl_sp e) rProj24_sp (rEl_sp_disjoint_rProj24 e) (rk1_sp χ) M]
theorem isHermitian_real_smul_slot2 {d : Type*} (r : ℝ)
    {M : Matrix d d ℂ} (hM : M.IsHermitian) : ((r : ℂ) • M).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal, hM.eq]
open Classical in
theorem bModSlot248_isHermitian (c : Configuration) : (bModSlot248 c).IsHermitian := by
  have hsum : ∀ {α : Type} (s : Finset α) (f : α → Operator (2 ^ systemQubits)),
      (∀ a ∈ s, (f a).IsHermitian) → (∑ a ∈ s, f a).IsHermitian := by
    intro α s f hf
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (hf a (Finset.mem_insert_self a s)).add
          (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))
  refine ( ?_ : (uenSubGridRaw48 c w128DualQ30).IsHermitian).sub
    (isHermitian_real_smul_slot2 pos24Slot2E2Const Matrix.isHermitian_one)
  unfold uenSubGridRaw48
  rw [← Complex.ofReal_neg]
  exact isHermitian_real_smul_slot2 (-(1 / 8 : ℝ)) (hsum Finset.univ _ fun l _ ↦
    hsum Finset.univ _ fun b _ ↦ hsum Finset.univ _ fun y _ ↦
      isHermitian_real_smul_slot2 _
        (nSub_isHermitian_any (uenSubGridKet48 c l b y) Finset.univ))
theorem norm_proj_sandwich_le_part4A {d : ℕ} (P D : Operator d) {ε : ℝ} (hε : 0 ≤ ε)
    (hP : ‖P‖ ≤ 1) (hD : ‖D‖ ≤ ε) : ‖P * D * P‖ ≤ ε := by
  refine ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
    (norm_nonneg P))).trans ((mul_le_mul (mul_le_mul hP hD (norm_nonneg _) zero_le_one) hP
      (norm_nonneg P) (by linarith)).trans_eq (by ring))
theorem smConj_eq_sm654Conj_of_comm_rProj24 {A : Operator (2 ^ systemQubits)}
    (hIdle : ∀ M : Operator (2 ^ 24),
      A * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * A) :
    smToTwosSysUnitary.1 * A * smToTwosSysUnitary.1 =
      smToTwos654SysUnitary.1 * A * smToTwos654SysUnitary.1 := by
  set P := rProj24_sp.embedMatrix (fwdPermUnitary projSignedMagToTwos24Equiv).1
  have hUsys : smToTwosSysUnitary.1 = P * smToTwos654SysUnitary.1 := by
    rw [smToTwosSysUnitary_eq_proj_mul_elec, unitary_coe_mul, QRegister.embedUnitary_val]
  have hP_inv : Pᴴ * P = 1 := by
    dsimp only [P]
    rw [← QRegister.embedUnitary_val]
    simpa only [Matrix.star_eq_conjTranspose] using
      (rProj24_sp.embedUnitary (fwdPermUnitary projSignedMagToTwos24Equiv)).2.1
  nth_rw 1 [← smToTwosSysUnitary_sa]
  rw [hUsys, Matrix.conjTranspose_mul, smToTwos654SysUnitary_sa,
    Matrix.mul_assoc (smToTwos654SysUnitary.1 * Pᴴ) A,
    Matrix.mul_assoc smToTwos654SysUnitary.1 Pᴴ,
    ← Matrix.mul_assoc A P, hIdle _, ← Matrix.mul_assoc Pᴴ,
    ← Matrix.mul_assoc Pᴴ P, hP_inv, Matrix.one_mul, ← Matrix.mul_assoc]
theorem permutationUnitary_eq_fwdPermUnitary {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    permutationUnitary σ = fwdPermUnitary σ := by
  apply Subtype.ext
  ext i j
  have hmv := congrFun (permutationUnitary_mulVec_single σ j (1 : ℂ)) i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hmv
  rw [hmv, fwdPermUnitary_apply]
  exact if_congr eq_comm rfl rfl
theorem diagonal_mul_fwdPermUnitary {N : ℕ} (f : Fin N → ℂ) (σ : Equiv.Perm (Fin N)) :
    Matrix.diagonal f * (fwdPermUnitary σ).1 =
      (fwdPermUnitary σ).1 * Matrix.diagonal (fun j ↦ f (σ j)) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, fwdPermUnitary_apply]
  by_cases h : σ j = i
  · subst h
    simp
  · simp [h]
theorem finSys_ext_fields {a b : Fin (2 ^ systemQubits)}
    (helec : ∀ (e : Fin 218) (w : Fin 3), elecAxisField a e w = elecAxisField b e w)
    (hproj : ∀ w : Fin 3, projAxisField a w = projAxisField b w) : a = b := by
  apply (basisBitsEquiv systemQubits).injective
  funext q
  by_cases hlt : q.val < 3924
  · let e : Fin 218 := ⟨q.val / 18, by omega⟩
    let w : Fin 3 := ⟨(q.val % 18) / 6, by omega⟩
    let j : Fin 6 := ⟨q.val % 6, Nat.mod_lt _ (by omega)⟩
    let m : Fin 654 := ⟨3 * e.val + w.val, by omega⟩
    have hq_eq : q = elec654Axes m j := Fin.ext (by
      dsimp [elec654Axes, qreg_block_wires_slot2, m, e, w, j]
      omega)
    have h1 := congrFun (congrArg (basisBits 6) (helec e w)) j
    change basisBits 6 ((elec654Axes m).extractIndex a) j =
      basisBits 6 ((elec654Axes m).extractIndex b) j at h1
    rwa [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, ← hq_eq] at h1
  · have hlt_sys : q.val < 3948 := q.isLt
    let w : Fin 3 := ⟨(q.val - 3924) / 8, by omega⟩
    let j : Fin 8 := ⟨(q.val - 3924) % 8, Nat.mod_lt _ (by omega)⟩
    have hq_eq : q = proj3Axes w j := Fin.ext (by
      dsimp [proj3Axes, qreg_block_wires_slot2, w, j]
      omega)
    have h1 := congrFun (congrArg (basisBits 8) (hproj w)) j
    change basisBits 8 ((proj3Axes w).extractIndex a) j =
      basisBits 8 ((proj3Axes w).extractIndex b) j at h1
    rwa [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, ← hq_eq] at h1
theorem elecAxisField_permElectron (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) (e : Fin numElectrons) (w : Fin 3) :
    elecAxisField (permElectron g x) e w = elecAxisField x (g e) w := by
  rw [elecAxisField_eq_extract_u18, elecAxisField_eq_extract_u18]
  refine congrFun (congrArg u18AxisSplitEquiv
    ((basisBitsEquiv 18).injective (funext fun b ↦ ?_))) w
  change basisBits 18 _ b = basisBits 18 _ b
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, permElectron,
    basisBits_permElectron (permElectronWire g) x (rEl_sp e b)]
  refine congrArg (basisBits _ _) (Fin.ext ?_)
  change (permElectronWireFun g (rEl_sp e b)).val = 18 * (g e).val + b.val
  unfold permElectronWireFun
  have hlt : (rEl_sp e b).val < 3924 := by
    have he : e.val < 218 := e.isLt
    have hb := b.isLt
    dsimp [rEl_sp, qreg_block_wires_slot2]
    omega
  rw [dite_eq_of_pos hlt]
  change 18 * (g ⟨(rEl_sp e b).val / 18, div_18_lt_numElectrons hlt⟩).val +
      (rEl_sp e b).val % 18 = 18 * (g e).val + b.val
  have hdiv : (⟨(rEl_sp e b).val / 18, div_18_lt_numElectrons hlt⟩ : Fin numElectrons) = e :=
    Fin.ext (by have := b.isLt; dsimp [rEl_sp, qreg_block_wires_slot2]; omega)
  have hmod : (rEl_sp e b).val % 18 = b.val := by
    have := b.isLt; dsimp [rEl_sp, qreg_block_wires_slot2]; omega
  rw [hdiv, hmod]
theorem projAxisField_permElectron (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    projAxisField (permElectron g x) w = projAxisField x w :=
  (basisBitsEquiv 8).injective (funext fun j ↦ by
    change basisBits 8 ((proj3Axes w).extractIndex (permElectron g x)) j =
      basisBits 8 ((proj3Axes w).extractIndex x) j
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, permElectron,
      basisBits_permElectron (permElectronWire g) x (proj3Axes w j)]
    refine congrArg (basisBits _ _) (Fin.ext ?_)
    change (permElectronWireFun g (proj3Axes w j)).val = (proj3Axes w j).val
    unfold permElectronWireFun
    exact congrArg Fin.val (dite_eq_of_neg (by
      dsimp [proj3Axes, qreg_block_wires_slot2]
      omega)))
theorem permutationUnitary_permElectron_swap_zero :
    (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) 0))).1 =
      (1 : Operator (2 ^ systemQubits)) := by
  have hrefl : permElectron (Equiv.refl (Fin numElectrons)) =
      Equiv.refl (Fin (2 ^ systemQubits)) :=
    Equiv.ext fun z ↦ finSys_ext_fields
      (fun e w ↦ by rw [elecAxisField_permElectron]; rfl)
      (fun w ↦ projAxisField_permElectron (Equiv.refl _) z w)
  change (permutationUnitary (permElectron (Equiv.swap (0 : Fin numElectrons) 0))).1 = 1
  rw [Equiv.swap_self 0, hrefl, permutationUnitary_eq_fwdPermUnitary, fwdPermUnitary_refl]
  rfl
theorem conj_phase_diag_outer {D : ℕ} (ζ : ℂ) (hζ : star ζ * ζ = 1) (φ f : Fin D → ℂ)
    (hφ : ∀ z, star (φ z) * φ z = 1) (V N B X : Operator D)
    (hX : X = (Matrix.diagonal φ * V) * (ζ • Nᴴ) * B) : Xᴴ * Matrix.diagonal f * X = Bᴴ *
    (N * (Vᴴ * Matrix.diagonal f * V) * Nᴴ) * B := by
  have hdiag : (Matrix.diagonal φ)ᴴ * Matrix.diagonal f * Matrix.diagonal φ =
      Matrix.diagonal f := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun z ↦ by
      dsimp only [Pi.star_apply]; rw [mul_right_comm, hφ z, one_mul])
  rw [hX]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [mul_comm ζ (star ζ), hζ, one_smul]
  have hassoc : (Bᴴ * (N * (Vᴴ * (Matrix.diagonal φ)ᴴ))) * Matrix.diagonal f *
      (Matrix.diagonal φ * V * Nᴴ * B) = Bᴴ * (N * (Vᴴ *
        ((Matrix.diagonal φ)ᴴ * Matrix.diagonal f * Matrix.diagonal φ) * V) * Nᴴ) * B := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, hdiag]
theorem star_prod_karatsubaOutPhase3D_mul_self (z : Fin (2 ^ systemQubits)) :
    star (∏ e : Fin 218, karatsubaOutPhase3D (slotCoordSys z e)) *
      (∏ e : Fin 218, karatsubaOutPhase3D (slotCoordSys z e)) = 1 := by
  rw [star_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun e _ ↦ karatsubaOutPhase3D_unit (slotCoordSys z e)
theorem sum_fin_lt_const {span mag : ℕ} (h : mag ≤ span) (c : ℂ) :
    (∑ k : Fin span, if k.val < mag then c else 0) = (mag : ℂ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  have hbij : (Finset.univ : Finset (Fin mag)).map ⟨fun i : Fin mag ↦ (⟨i.val, lt_of_lt_of_le
      i.isLt h⟩ : Fin span), fun i j hij ↦ Fin.ext (congrArg (fun x : Fin span ↦ x.val) hij)⟩
      = Finset.univ.filter (fun k : Fin span ↦ k.val < mag) := by
    ext k
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
      Finset.mem_filter]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ i.isLt, fun hk ↦ ⟨⟨k.val, hk⟩, Fin.ext rfl⟩⟩
  rw [← hbij, Finset.card_map, Finset.card_fin]
theorem unitary_coe_mul_of_eq {N : ℕ} {U A B : Unitary N} (h : U = A * B) :
    U.1 = A.1 * B.1 :=
  (congrArg Subtype.val h).trans (unitary_coe_mul A B)
theorem fwdPermUnitary_comm_of_perm_comm {N : ℕ} (a b : Equiv.Perm (Fin N))
    (h : ∀ x, a (b x) = b (a x)) :
    (fwdPermUnitary a).1 * (fwdPermUnitary b).1 =
      (fwdPermUnitary b).1 * (fwdPermUnitary a).1 := by
  have htr : b.trans a = a.trans b := Equiv.ext h
  rw [← unitary_coe_mul, ← fwdPermUnitary_trans, htr, fwdPermUnitary_trans, unitary_coe_mul]
theorem barrelTwist_mul_smToTwos654 (hoff_perm : offsetSysUnitary = fwdPermUnitary
    (smToTwos654SysPerm.trans xor32SysPerm)) (anc : Fin 218) :
    (fwdPermUnitary ((barrelSysPerm anc.val).trans xor32SysPerm)).1 *
      smToTwos654SysUnitary.1 =
    offsetSysUnitary.1 *
      (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1 := by
  let g := permElectron (Equiv.swap (0 : Fin numElectrons) anc)
  have hbar : barrelSysPerm anc.val = g := by
    unfold barrelSysPerm
    exact dite_eq_of_pos anc.isLt
  have hcomm_perm : ∀ z, g (smToTwos654SysPerm z) = smToTwos654SysPerm (g z) := fun z ↦
    finSys_ext_fields
      (fun e w ↦ by
        dsimp only [g]
        rw [elecAxisField_permElectron, elecAxisField_smToTwos654,
          elecAxisField_smToTwos654, elecAxisField_permElectron])
      (fun w ↦ by
        dsimp only [g]
        rw [projAxisField_permElectron, projAxisField_smToTwos654,
          projAxisField_smToTwos654, projAxisField_permElectron])
  have hcomm := fwdPermUnitary_comm_of_perm_comm g smToTwos654SysPerm hcomm_perm
  have hsm : smToTwos654SysUnitary.1 = (fwdPermUnitary smToTwos654SysPerm).1 := rfl
  have hoff_coe : (fwdPermUnitary xor32SysPerm).1 * (fwdPermUnitary smToTwos654SysPerm).1 =
      offsetSysUnitary.1 := by
    rw [hoff_perm, unitary_coe_mul_of_eq (fwdPermUnitary_trans smToTwos654SysPerm xor32SysPerm)]
  have htrans_coe : (fwdPermUnitary ((barrelSysPerm anc.val).trans xor32SysPerm)).1 =
      (fwdPermUnitary xor32SysPerm).1 * (fwdPermUnitary g).1 := by
    rw [hbar, unitary_coe_mul_of_eq (fwdPermUnitary_trans g xor32SysPerm)]
  rw [htrans_coe, hsm, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hoff_coe,
    ← permutationUnitary_eq_fwdPermUnitary]
theorem slot2RawKickDiag_mul_offsetSysUnitary (hoff_perm : offsetSysUnitary = fwdPermUnitary
    (smToTwos654SysPerm.trans xor32SysPerm)) (c : Configuration) (l : Fin 216) :
    slot2RawKickDiag c l.val * offsetSysUnitary.1 =
      offsetSysUnitary.1 * (slot2GlobalPhase c l • (sysNucDiag48 c l).1ᴴ) := by
  have hK : slot2RawKickDiag c l.val = Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
      dyadicTurn 48 (∑ w : Fin 3, (∑ e : Fin numElectrons,
        ((u18GridEquiv ((rEl_sp e).extractIndex z) w).val : ℤ)) *
        (nuclearM48 c l w : ℤ))) :=
    congrArg Matrix.diagonal (funext fun _ ↦ dite_eq_of_pos l.isLt)
  rw [hK, congrArg Subtype.val hoff_perm, diagonal_mul_fwdPermUnitary,
    ← slot2_offsetDiag_eq_smul_sysNucDiag48_conjTranspose c l]
  refine congrArg ((fwdPermUnitary _).1 * ·) (congrArg Matrix.diagonal (funext fun x ↦
    congrArg (dyadicTurn 48) (Finset.sum_congr rfl fun w _ ↦
      congrArg (· * (nuclearM48 c l w : ℤ)) (Finset.sum_congr rfl fun e _ ↦ ?_))))
  rw [Equiv.trans_apply, extractIndex_rEl_smToTwos654_xor32 x e, u18GridEquiv_offset18Perm]
theorem qftProd_mul_offsetSysUnitary (b₁ : NyqParity3D) (hqft18 : (qft64OffsetUnitary3D b₁ *
    offset18Unitary).1 = Matrix.diagonal (fun z : Fin (2 ^ 18) ↦ karatsubaOutPhase3D
    (slotCoord18Equiv z)) * (veeBasisUnitary18 b₁).1) (hprod_mul : ∀ F G : Fin 218 → Unitary
    (2 ^ 18), (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (F e)).prod * (List.ofFn
    fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (G e)).prod = (List.ofFn fun e : Fin 218 ↦
    (rEl_sp e).embedUnitary (F e * G e)).prod) (hout_diag : ((List.ofFn fun e : Fin 218 ↦
    (rEl_sp e).embedUnitary outPhase18Unitary).prod).1 = Matrix.diagonal (fun z : Fin (2 ^
    systemQubits) ↦ ∏ e : Fin 218, karatsubaOutPhase3D (slotCoordSys z e))) :
    ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (qft64OffsetUnitary3D b₁)).prod).1 *
      offsetSysUnitary.1 =
    Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
      ∏ e : Fin 218, karatsubaOutPhase3D (slotCoordSys z e)) * (veeSysProdUnitary b₁).1 := by
  have hu18 : qft64OffsetUnitary3D b₁ * offset18Unitary =
      outPhase18Unitary * veeBasisUnitary18 b₁ :=
    Subtype.ext (hqft18.trans (unitary_coe_mul outPhase18Unitary (veeBasisUnitary18 b₁)).symm)
  have h1 := (unitary_coe_mul ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary
      (qft64OffsetUnitary3D b₁)).prod) offsetSysUnitary).symm.trans (congrArg Subtype.val
      (hprod_mul (fun _ ↦ qft64OffsetUnitary3D b₁) (fun _ ↦ offset18Unitary)))
  have h2 := (unitary_coe_mul ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary
      outPhase18Unitary).prod) (veeSysProdUnitary b₁)).symm.trans (congrArg Subtype.val
      (hprod_mul (fun _ ↦ outPhase18Unitary) (fun _ ↦ veeBasisUnitary18 b₁)))
  rw [h1]
  simp_rw [hu18]
  rw [← h2, hout_diag]
theorem slot2OuterFactor_eq (hoff_perm : offsetSysUnitary = fwdPermUnitary
    (smToTwos654SysPerm.trans xor32SysPerm)) (c : Configuration) (l : Fin 216) (anc : Fin 218)
    (b₁ : NyqParity3D) (hqft18 : (qft64OffsetUnitary3D b₁ * offset18Unitary).1 =
    Matrix.diagonal (fun z : Fin (2 ^ 18) ↦ karatsubaOutPhase3D (slotCoord18Equiv z)) *
    (veeBasisUnitary18 b₁).1) (hprod_mul : ∀ F G : Fin 218 → Unitary (2 ^ 18), (List.ofFn fun
    e : Fin 218 ↦ (rEl_sp e).embedUnitary (F e)).prod * (List.ofFn fun e : Fin 218 ↦ (rEl_sp
    e).embedUnitary (G e)).prod = (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (F e *
    G e)).prod) (hout_diag : ((List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary
    outPhase18Unitary).prod).1 = Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦ ∏ e : Fin
    218, karatsubaOutPhase3D (slotCoordSys z e))) : (((List.ofFn fun e : Fin 218 ↦ (rEl_sp
    e).embedUnitary (qft64OffsetUnitary3D b₁)).prod).1 * (slot2RawKickDiag c l.val *
    (fwdPermUnitary ((barrelSysPerm anc.val).trans xor32SysPerm)).1)) *
    smToTwos654SysUnitary.1 = (Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦ ∏ e : Fin
    218, karatsubaOutPhase3D (slotCoordSys z e)) * (veeSysProdUnitary b₁).1) *
    (slot2GlobalPhase c l • (sysNucDiag48 c l).1ᴴ) *
    (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, barrelTwist_mul_smToTwos654 hoff_perm anc,
    ← Matrix.mul_assoc (slot2RawKickDiag c l.val),
    slot2RawKickDiag_mul_offsetSysUnitary hoff_perm c l, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc _ offsetSysUnitary.1,
    qftProd_mul_offsetSysUnitary b₁ hqft18 hprod_mul hout_diag, Matrix.mul_assoc]
theorem smul_conj_sum_real_smul {D : ℕ} {ι : Type*} [Fintype ι] (s : ℝ) (S : Operator D)
    (w : ι → ℝ) (B : ι → Operator D) : (s : ℂ) • (S * (∑ i : ι, (w i : ℂ) • B i) * S) = ∑ i :
    ι, ((s * w i : ℝ) : ℂ) • (S * B i * S) := by
  rw [Matrix.mul_sum, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.ofReal_mul]
noncomputable def blkSmSlot2 (qft : FullSysQft654Bundle) (c : Configuration)
    (p80 : BitAssignment 80) : Operator (2 ^ systemQubits) := smToTwosSysUnitary.1 *
    sysBlockAtPayloadGen hkFlag80 (pos24ConjCore80 qft c).1 false p80 * smToTwosSysUnitary.1
theorem sa_conj_conj_eq {D : ℕ} {S : Operator D} (hsa : Sᴴ = S) (W M : Operator D) :
    S * (Wᴴ * M * W) * S = (W * S)ᴴ * M * (W * S) := by
  nth_rw 1 [← hsa]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
theorem sum_bool_bool_mul_eq_four_smul_of_half {d : ℕ} (F : Bool → Bool → Operator d)
    (N V : Operator d) (D : Bool → Operator d) (P R : Operator d)
    (hF : ∀ th rj, F th rj = N * (Vᴴ * D th * V) * Nᴴ) (hHalf : (N * (Vᴴ * ((1 / 2 : ℂ) • (D
    false + D true)) * V) * Nᴴ) * P = R) : (∑ th : Bool, ∑ rj : Bool, F th rj) * P = (4 : ℂ) •
    R := by
  have hsum : (∑ th : Bool, ∑ rj : Bool, F th rj) =
      (4 : ℂ) • (N * (Vᴴ * ((1 / 2 : ℂ) • (D false + D true)) * V) * Nᴴ) := by
    simp_rw [hF]
    simp only [Fintype.sum_bool, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, smul_smul]
    rw [show (4 : ℂ) * (1 / 2 : ℂ) = 2 by norm_num, smul_add, two_smul, two_smul]
    abel
  rw [hsum, Matrix.smul_mul, hHalf]
theorem conj3_finset_sum_eq {D : ℕ} {ι : Type*} (B N V : Operator D) (s : Finset ι)
    (M : ι → Operator D) : (∑ i ∈ s, Bᴴ * (N * (Vᴴ * M i * V) * Nᴴ) * B) =
      Bᴴ * (N * (Vᴴ * (∑ i ∈ s, M i) * V) * Nᴴ) * B := by
  simp only [Matrix.mul_sum, Finset.sum_mul]
theorem slot2_tail_keep_th_rj_sum_eq_of_slices
    (qft : FullSysQft654Bundle) (c : Configuration)
    (l : Fin 216) (anc : Fin 218) (dp : Fin 8)
    (hCleanTail : ∀ (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool),
      let b₁ := nyqParity3DEquivFin8.symm dp
      let p80 := tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj
      blkSmSlot2 qft c p80 =
        (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1ᴴ *
          ((sysNucDiag48 c l).1 *
            ((veeSysProdUnitary b₁).1ᴴ *
              Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
                let rOrbit := tetRank65 (canonTriple128 (nyq128Equiv3D (slotCoordSys z 0, b₁)))
                if (if keep.val < (pos24TailMag30 rOrbit).val then !(pos24TailSign rOrbit)
                  else rj)
                then (-1 : ℂ) else 1) *
              (veeSysProdUnitary b₁).1) *
            (sysNucDiag48 c l).1ᴴ) *
          (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1)
    (hSpan : ∀ y : NyqGrid3D64,
      (pos24TailMag30
        (tetRank65 (canonTriple128 (nyq128Equiv3D (y, nyqParity3DEquivFin8.symm dp))))).val ≤
      pos24TailSpan8 dp)
    (hSlotProj : ∀ y : NyqGrid3D64,
      (veeSysProdUnitary (nyqParity3DEquivFin8.symm dp)).1ᴴ *
          Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
            if slotCoordSys z 0 = y then (1 : ℂ) else 0) *
          (veeSysProdUnitary (nyqParity3DEquivFin8.symm dp)).1 =
        op_sp (veeSubGridKet (nyqParity3DEquivFin8.symm dp) y) 0)
    (hNucConj : ∀ y : NyqGrid3D64,
      (sysNucDiag48 c l).1 * op_sp (veeSubGridKet (nyqParity3DEquivFin8.symm dp) y) 0 *
          (sysNucDiag48 c l).1ᴴ =
        op_sp (uenSubGridKet48 c l (nyqParity3DEquivFin8.symm dp) y) 0) :
    let b₁ := nyqParity3DEquivFin8.symm dp
    (∑ keep : Fin (pos24TailSpan8 dp), ∑ th : Bool, ∑ rj : Bool,
      blkSmSlot2 qft c (tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj)) =
    ((-4 * (2 : ℝ) ^ 30 : ℝ) : ℂ) •
      ∑ y : NyqGrid3D64,
        (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq (nyq128Equiv3D (y, b₁)) : ℂ) •
          op_sp (uenSubGridKet48 c l b₁ y) anc := by
  intro b₁
  simp_rw [hCleanTail, conj3_finset_sum_eq, sum_diagonal_eq_slot2]
  have hdiag :
      Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
        ∑ keep : Fin (pos24TailSpan8 dp), ∑ _th : Bool, ∑ rj : Bool,
          let rOrbit := tetRank65 (canonTriple128 (nyq128Equiv3D (slotCoordSys z 0, b₁)))
          if (if keep.val < (pos24TailMag30 rOrbit).val then !(pos24TailSign rOrbit) else rj)
          then (-1 : ℂ) else 1) =
      ((-4 * (2 : ℝ) ^ 30 : ℝ) : ℂ) •
        ∑ y : NyqGrid3D64,
          (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq (nyq128Equiv3D (y, b₁)) : ℂ) •
            Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
              if slotCoordSys z 0 = y then (1 : ℂ) else 0) := by
    simp_rw [← Matrix.diagonal_smul, sum_diagonal_eq_slot2, ← Matrix.diagonal_smul]
    refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
    dsimp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    let y := slotCoordSys z 0
    let dTail := nyq128Equiv3D (y, b₁)
    let rOrbit := tetRank65 (canonTriple128 dTail)
    have hinner (keep : Fin (pos24TailSpan8 dp)) :
        (∑ _th : Bool, ∑ rj : Bool,
          if (if keep.val < (pos24TailMag30 rOrbit).val then !(pos24TailSign rOrbit) else rj)
          then (-1 : ℂ) else 1) =
        if keep.val < (pos24TailMag30 rOrbit).val then
          (-4 : ℂ) * ((if pos24TailSign rOrbit then (-1 : ℝ) else 1 : ℝ) : ℂ) else 0 := by
      by_cases hk : keep.val < (pos24TailMag30 rOrbit).val
      · simp only [hk, ↓reduceIte, Fintype.sum_bool]
        cases pos24TailSign rOrbit <;> simp <;> ring
      · simp [hk]
    dsimp only [rOrbit, dTail, y] at hinner ⊢
    simp_rw [hinner]
    rw [sum_fin_lt_const (hSpan y)]
    have hc := congrArg (Complex.ofReal : ℝ → ℂ) (by
      linear_combination (-4 * (2 : ℝ) ^ 30) * (pos24_shell_cert dTail).1 :
      (-4 : ℝ) * ((if pos24TailSign rOrbit then (-1 : ℝ) else 1) *
        ((pos24TailMag30 rOrbit).val : ℝ)) =
      (-4 * (2 : ℝ) ^ 30) * kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq dTail)
    push_cast at hc ⊢
    linear_combination hc
  rw [hdiag]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Finset.sum_mul]
  refine congrArg (((-4 * (2 : ℝ) ^ 30 : ℝ) : ℂ) • ·) (Finset.sum_congr rfl fun y _ ↦
    congrArg
      ((kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq (nyq128Equiv3D (y, b₁)) : ℂ) • ·) ?_)
  rw [hSlotProj y, hNucConj y]
  let P := permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))
  rw [Matrix.mul_assoc, show op_sp (uenSubGridKet48 c l b₁ y) 0 * P.1 =
      P.1 * op_sp (uenSubGridKet48 c l b₁ y) anc by
    simpa only [op_sp, P, Equiv.swap_apply_left] using
      emb_rEl_mul_pe_sp (Equiv.swap (0 : Fin 218) anc) 0 _,
    ← Matrix.mul_assoc, show P.1ᴴ * P.1 = 1 by
      simpa only [Matrix.star_eq_conjTranspose] using P.2.1, Matrix.one_mul]
theorem fin8_bit_eq_nyqParitySymm_slot2 (o : Fin 8) (w : Fin 3) :
    (o.val / 2 ^ w.val) % 2 = (nyqParity3DEquivFin8.symm o w).val := by
  revert o w
  decide
theorem ite_decide_fin2_eq_one_nat_slot2 (u : Fin 2) :
    (if decide (u = 1) then (1 : ℕ) else 0) = u.val := by
  revert u
  decide
theorem nyq128Equiv3D_symm_fst_val_slot2 (d : NyqFine3D128) (w : Fin 3) :
    ((nyq128Equiv3D.symm d).1 w).val = (d w).val / 2 := by
  have h := congrArg (fun x ↦ (x w).val) (nyq128Equiv3D.apply_symm_apply d)
  rw [nyq128Equiv3D_val] at h
  have hb := ((nyq128Equiv3D.symm d).2 w).isLt
  omega
theorem headWitnessPayload80_slot2_meta
    (l : Fin 216) (k : Fin 56) (pid : Fin 6) (sm : Fin 8) (th rj : Bool) :
    let p80 := headWitnessPayload80 0 l.val 0 k pid sm th rj
    let dH := pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm
    payloadNucNat p80 = l.val ∧
      payloadAncNat p80 = 0 ∧
      payloadB1Parity p80 = (nyq128Equiv3D.symm dH).2 := by
  intro p80 dH
  refine ⟨?_, ?_, funext fun w ↦ Fin.ext ?_⟩
  · exact (congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j :
    Fin 8 ↦ by
      dsimp only [p80, headWitnessPayload80]
      fin_cases j <;> rfl)).trans
      (root_bitsVal_z2BitOfNat_of_lt_slot2 (lt_trans l.isLt (by decide)))
  · exact (congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j :
    Fin 8 ↦ by
      dsimp only [p80, headWitnessPayload80]
      fin_cases j <;> rfl)).trans (root_bitsVal_z2BitOfNat_of_lt_slot2 (by decide))
  · dsimp only [payloadB1Parity]
    let dpH := ((dH 0).val % 2) + 2 * ((dH 1).val % 2) + 4 * ((dH 2).val % 2)
    rw [show p80 ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩ = z2BitOfNat (Nat.xor 0 dpH) w.val by
      dsimp only [p80, headWitnessPayload80, dpH]
      fin_cases w <;> rfl, show Nat.xor 0 dpH = dpH from Nat.zero_xor dpH, z2BitOfNat_val]
    have h := congrArg (fun x ↦ (x w).val) (nyq128Equiv3D.apply_symm_apply dH)
    rw [nyq128Equiv3D_val] at h
    have hb := ((nyq128Equiv3D.symm dH).2 w).isLt
    fin_cases w <;> dsimp [dpH] at h hb ⊢ <;> omega
theorem tailWitnessPayload80_slot2_meta
    (l : Fin 216) (anc : Fin 218) (dp : Fin 8) (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool) :
    let p80 := tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj
    payloadNucNat p80 = l.val ∧
      payloadAncNat p80 = anc.val ∧
      payloadB1Parity p80 = nyqParity3DEquivFin8.symm dp := by
  intro p80
  refine ⟨?_, ?_, funext fun w ↦ Fin.ext ?_⟩
  · exact (congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j :
    Fin 8 ↦ by
      dsimp only [p80, tailWitnessPayload80]
      fin_cases j <;> rfl)).trans
      (root_bitsVal_z2BitOfNat_of_lt_slot2 (lt_trans l.isLt (by decide)))
  · exact (congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j :
    Fin 8 ↦ by
      dsimp only [p80, tailWitnessPayload80]
      fin_cases j <;> rfl)).trans
      (root_bitsVal_z2BitOfNat_of_lt_slot2 (lt_trans anc.isLt (by decide)))
  · dsimp only [payloadB1Parity]
    rw [show p80 ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩ = z2BitOfNat (Nat.xor 0 dp.val) w.val by
      dsimp only [p80, tailWitnessPayload80]
      fin_cases w <;> rfl, show Nat.xor 0 dp.val = dp.val from Nat.zero_xor dp.val,
      z2BitOfNat_val, fin8_bit_eq_nyqParitySymm_slot2]
theorem regVal_coreBetaOf_payload {m : ℕ} (r : QRegister m posCoreWires) (off : ℕ)
    (hoff : off + m ≤ 80) (hr : ∀ j : Fin m, r j = rPosSubLocal (pos80SubIdx off m hoff j))
    (s0 : Bool) (p80 : BitAssignment 80) (z : Fin (2 ^ systemQubits)) :
    regVal r (coreBetaOf s0 p80 z) =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin m ↦
        p80 (pos80SubIdx off m hoff j)) := by
  change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _ =
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _
  refine congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦ ?_)
  rw [hr j, coreBetaOf_payload]
theorem coreBetaOf_false_wSlots (p80 : BitAssignment 80) (z : Fin (2 ^ systemQubits)) :
    coreBetaOf false p80 z (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0 ∧
      coreBetaOf false p80 z (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0 ∧
      coreBetaOf false p80 z (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0 :=
  ⟨(coreBetaOf_mid false p80 z _ (by decide) (by decide)).trans (by decide),
   (coreBetaOf_mid false p80 z _ (by decide) (by decide)).trans (by decide),
   (coreBetaOf_mid false p80 z _ (by decide) (by decide)).trans (by decide)⟩
theorem slot2Tail_mag_le_span (dp : Fin 8) (y : NyqGrid3D64) : (pos24TailMag30 (tetRank65
    (canonTriple128 (nyq128Equiv3D (y, nyqParity3DEquivFin8.symm dp))))).val ≤ pos24TailSpan8
    dp := by
  let b1 := nyqParity3DEquivFin8.symm dp
  let dTail := nyq128Equiv3D (y, b1)
  suffices h : pos24HalfSpanQb (orbitParityWeight (tetRank65 (canonTriple128 dTail))) =
      pos24TailSpan8 dp by
    rw [← h]
    exact pos24TailMag30_le_halfSpan _
  dsimp only [pos24TailSpan8]
  refine congrArg pos24HalfSpanQb (Fin.ext ?_)
  rw [← subGridWeight128_eq_orbit dTail, subGridWeight128_eq_nyqParity dTail,
    nyq128Equiv3D.symm_apply_apply, subGridParityWeight3_nyqParityToBool]
  dsimp only [b1]
  rw [← fin8_bit_eq_nyqParitySymm_slot2 dp 0, ← fin8_bit_eq_nyqParitySymm_slot2 dp 1,
    ← fin8_bit_eq_nyqParitySymm_slot2 dp 2]
  dsimp
  omega
theorem slot2_witnessSum_mul_fermionicProjector_eq
    (c : Configuration) (spinUp : Finset (Fin numElectrons))
    (blkSm : BitAssignment 80 → Operator (2 ^ systemQubits))
    (hHead4 : ∀ (l : Fin 216) (k : Fin 56) (pid : Fin 6) (sm : Fin 8),
      let dH := pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm
      (∑ th : Bool, ∑ rj : Bool, blkSm (headWitnessPayload80 0 l.val 0 k pid sm th rj)) *
        fermionicProjector spinUp =
      (4 : ℂ) •
        ((1 - nTot_sp (uenSubGridKet48 c l (nyq128Equiv3D.symm dH).2
          (nyq128Equiv3D.symm dH).1)) * fermionicProjector spinUp))
    (hTailKeep : ∀ (l : Fin 216) (anc : Fin 218) (dp : Fin 8),
      let b1 := nyqParity3DEquivFin8.symm dp
      (∑ keep : Fin (pos24TailSpan8 dp), ∑ th : Bool, ∑ rj : Bool,
        blkSm (tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj)) =
      ((-4 * (2 : ℝ) ^ 30 : ℝ) : ℂ) •
        ∑ y : NyqGrid3D64,
          (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq (nyq128Equiv3D (y, b1)) : ℂ) •
            op_sp (uenSubGridKet48 c l b1 y) anc) :
    (∑ p80 : BitAssignment 80,
        ((pos80Slot2Scale * pos80IdealDist false p80 : ℝ) : ℂ) • blkSm p80) *
      fermionicProjector spinUp =
    bModSlot248 c * fermionicProjector spinUp := by
  let P := fermionicProjector spinUp
  have htot : (pos80Slot2TotNat : ℝ) ≠ 0 := fun h0 ↦ by
    have hp := pos80Slot2Scale_pos
    unfold pos80Slot2Scale at hp
    norm_num [h0] at hp
  have hHeadSum :
      (∑ x : HeadSupportIdx false,
        ((pos80Slot2Scale *
          pos80IdealDist false (pos80WitnessOf false (Sum.inl x)) : ℝ) : ℂ) •
          blkSm (pos80WitnessOf false (Sum.inl x))) * P =
      (((1 / 8 : ℝ) : ℂ) •
        ∑ l : Fin 216, ∑ d : NyqFine3D128,
          (kHead128 w128DualQ30 pos24CutNyq d : ℂ) •
            (1 - nTot_sp (uenSubGridKet48 c l (nyq128Equiv3D.symm d).2
              (nyq128Equiv3D.symm d).1))) * P := by
    have hw_eq (k : Fin 56) :
        (pos80Slot2Scale *
            ((pos24HeadWeight56 k : ℝ) / (216 * 48 * 2 * 2 * pos80Slot2TotNat)) : ℝ) * 4 =
        ((1 / 8 : ℝ) * (1 / 48 : ℝ)) * ((pos24HeadWeight56 k : ℝ) / 2 ^ 30) := by
      unfold pos80Slot2Scale
      field_simp
      ring
    rw [Finset.sum_mul]
    change (∑ x : Fin 1 × Fin 216 × Fin 1 × Fin 56 × Fin 6 × Fin 8 × Bool × Bool,
        (((pos80Slot2Scale *
          pos80IdealDist false (pos80WitnessOf false (Sum.inl x)) : ℝ) : ℂ) •
          blkSm (pos80WitnessOf false (Sum.inl x))) * P) = _
    simp only [Fintype.sum_prod_type, Fintype.sum_unique]
    change (∑ l : Fin 216, ∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm : Fin 8,
        ∑ th : Bool, ∑ rj : Bool,
        (((pos80Slot2Scale *
          pos80IdealDist false (pos80WitnessOf false (Sum.inl ((0 : Fin 1), l,
          (0 : Fin 1), k, pid, sm, th, rj))) : ℝ) : ℂ) •
          blkSm (headWitnessPayload80 0 l.val 0 k pid sm th rj)) * P) = _
    have hev (l : Fin 216) (k : Fin 56) (pid : Fin 6) (sm : Fin 8) (th rj : Bool) :
        pos80IdealDist false
          (pos80WitnessOf false (Sum.inl ((0 : Fin 1), l, (0 : Fin 1), k, pid, sm, th, rj))) =
        (pos24HeadWeight56 k : ℝ) / (216 * 48 * 2 * 2 * pos80Slot2TotNat) := by
      simpa using pos80WitnessOf_eval_head false 0 l 0 k pid sm th rj
    trans (∑ l : Fin 216, ((1 / 8 : ℝ) : ℂ) • ∑ d : NyqFine3D128,
        (kHead128 w128DualQ30 pos24CutNyq d : ℂ) •
          ((1 - nTot_sp (uenSubGridKet48 c l (nyq128Equiv3D.symm d).2
            (nyq128Equiv3D.symm d).1)) * P))
    · refine Finset.sum_congr rfl fun l _ ↦ ?_
      let F_l : NyqFine3D128 → Operator (2 ^ systemQubits) := fun d ↦
        (1 - nTot_sp (uenSubGridKet48 c l (nyq128Equiv3D.symm d).2 (nyq128Equiv3D.symm d).1)) * P
      let c48 : ℂ := (((1 / 8 : ℝ) * (1 / 48 : ℝ) : ℝ) : ℂ)
      have h4 (k : Fin 56) (pid : Fin 6) (sm : Fin 8) :
          (∑ th : Bool, ∑ rj : Bool,
            (((pos80Slot2Scale * pos80IdealDist false
              (pos80WitnessOf false
                (Sum.inl ((0 : Fin 1), l, (0 : Fin 1), k, pid, sm, th, rj))) : ℝ) : ℂ) •
              blkSm (headWitnessPayload80 0 l.val 0 k pid sm th rj)) * P) =
          c48 • ((((pos24HeadWeight56 k : ℝ) / 2 ^ 30 : ℝ) : ℂ) •
            F_l (pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm)) := by
        simp_rw [hev, Matrix.smul_mul, ← Finset.smul_sum]
        rw [show (∑ th : Bool, ∑ rj : Bool,
              blkSm (headWitnessPayload80 0 l.val 0 k pid sm th rj) * P) =
            (∑ th : Bool, ∑ rj : Bool,
              blkSm (headWitnessPayload80 0 l.val 0 k pid sm th rj)) * P by
          simp only [Finset.sum_mul], hHead4 l k pid sm, smul_smul, smul_smul]
        refine congrArg (· • F_l _) ?_
        have hc := congrArg (Complex.ofReal : ℝ → ℂ) (hw_eq k)
        dsimp only [c48]
        push_cast at hc ⊢
        linear_combination hc
      have hsm3 (g : Fin 56 → Fin 6 → Fin 8 → Operator (2 ^ systemQubits)) :
          (∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm : Fin 8, c48 • g k pid sm) =
            c48 • ∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm : Fin 8, g k pid sm := by
        simp_rw [Finset.smul_sum]
      simp_rw [h4]
      rw [hsm3 (fun k pid sm ↦
          (((pos24HeadWeight56 k : ℝ) / 2 ^ 30 : ℝ) : ℂ) •
            F_l (pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm)),
        pos24_oh_head_sum_eq F_l, smul_smul]
      exact congrArg (· • ∑ d : NyqFine3D128, (kHead128 w128DualQ30 pos24CutNyq d : ℂ) • F_l d)
        (by
          dsimp only [c48]
          push_cast
          ring)
    · rw [← Finset.smul_sum, Matrix.smul_mul, Finset.sum_mul]
      refine congrArg (((1 / 8 : ℝ) : ℂ) • ·) (Finset.sum_congr rfl fun l _ ↦ ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun d _ ↦ (Matrix.smul_mul _ _ P).symm
  have hTailSum :
      (∑ y : TailSupportIdx false,
        ((pos80Slot2Scale *
          pos80IdealDist false (pos80WitnessOf false (Sum.inr y)) : ℝ) : ℂ) •
          blkSm (pos80WitnessOf false (Sum.inr y))) =
        (-((1 / 8 : ℝ) : ℂ)) •
          ∑ l : Fin 216, ∑ b : NyqParity3D, ∑ y : NyqGrid3D64,
            (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq (nyq128Equiv3D (y, b)) : ℂ) •
              nTot_sp (uenSubGridKet48 c l b y) := by
    have hw_tail : (pos80Slot2Scale * ((1 : ℝ) / (216 * 2 * 2 * pos80Slot2TotNat)) : ℝ) *
        (-4 * (2 : ℝ) ^ 30) = -(1 / 8 : ℝ) := by
      unfold pos80Slot2Scale
      field_simp
      ring
    change (∑ y : Fin 1 × Fin 216 × Fin 218 × Fin 1 ×
        (Σ dp : Fin 8, Fin (pos24TailSpan8 dp)) × Bool × Bool,
        ((pos80Slot2Scale * pos80IdealDist false (pos80WitnessOf false (Sum.inr y)) : ℝ) : ℂ) •
          blkSm (pos80WitnessOf false (Sum.inr y))) = _
    simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_unique]
    change (∑ l : Fin 216, ∑ anc : Fin 218, ∑ dp : Fin 8, ∑ keep : Fin (pos24TailSpan8 dp),
        ∑ th : Bool, ∑ rj : Bool,
        ((pos80Slot2Scale * pos80IdealDist false
          (pos80WitnessOf false (Sum.inr ((0 : Fin 1), l,
          anc, (0 : Fin 1), ⟨dp, keep⟩, th, rj))) : ℝ) : ℂ) •
          blkSm (tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj)) = _
    have hev (l : Fin 216) (anc : Fin 218) (dp : Fin 8) (keep : Fin (pos24TailSpan8 dp))
        (th rj : Bool) :
        pos80IdealDist false (pos80WitnessOf false
          (Sum.inr ((0 : Fin 1), l, anc, (0 : Fin 1), ⟨dp, keep⟩, th, rj))) =
        (1 : ℝ) / (216 * 2 * 2 * pos80Slot2TotNat) := by
      simpa using pos80WitnessOf_eval_tail false 0 l anc 0 dp keep th rj
    simp_rw [hev, ← Finset.smul_sum, hTailKeep]
    simp only [← Finset.smul_sum, smul_smul]
    rw [show ((pos80Slot2Scale * ((1 : ℝ) / (216 * 2 * 2 * pos80Slot2TotNat)) : ℝ) : ℂ) *
        ((-4 * (2 : ℝ) ^ 30 : ℝ) : ℂ) = -((1 / 8 : ℝ) : ℂ) by
      have h := congrArg (Complex.ofReal : ℝ → ℂ) hw_tail
      push_cast at h ⊢
      exact h]
    refine congrArg ((-((1 / 8 : ℝ) : ℂ)) • ·) (Finset.sum_congr rfl fun l _ ↦ ?_)
    rw [Finset.sum_comm, ← Equiv.sum_comp nyqParity3DEquivFin8.symm]
    refine Finset.sum_congr rfl fun dp _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ ↦ by
      rw [← Finset.smul_sum]
      rfl
  have hAlg (oneV : Operator (2 ^ systemQubits))
      (N : Fin 216 → NyqParity3D → NyqGrid3D64 → Operator (2 ^ systemQubits))
      (hN : ∀ (l : Fin 216) (b : NyqParity3D),
        (∑ y : NyqGrid3D64, N l b y) = (numElectrons : ℂ) • oneV) :
      ((1 / 8 : ℝ) : ℂ) • (∑ l : Fin 216, ∑ d : NyqFine3D128,
          (kHead128 w128DualQ30 pos24CutNyq d : ℂ) •
            (oneV - N l (nyq128Equiv3D.symm d).2 (nyq128Equiv3D.symm d).1)) +
        (-((1 / 8 : ℝ) : ℂ)) • (∑ l : Fin 216, ∑ b : NyqParity3D, ∑ y : NyqGrid3D64,
          (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq (nyq128Equiv3D (y, b)) : ℂ) •
            N l b y) =
        (-((1 / 8 : ℝ) : ℂ)) • (∑ l : Fin 216, ∑ b : NyqParity3D, ∑ y : NyqGrid3D64,
          (w128DualQ30 (nyq128Equiv3D (y, b)) : ℂ) • N l b y) -
          (pos24Slot2E2Const : ℂ) • oneV := by
    have hd_reindex : ∀ l : Fin 216,
        (∑ d : NyqFine3D128, (kHead128 w128DualQ30 pos24CutNyq d : ℂ) •
          N l (nyq128Equiv3D.symm d).2 (nyq128Equiv3D.symm d).1) =
        ∑ b : NyqParity3D, ∑ y : NyqGrid3D64,
          (kHead128 w128DualQ30 pos24CutNyq (nyq128Equiv3D (y, b)) : ℂ) • N l b y :=
      fun l ↦ by
        rw [← Equiv.sum_comp nyq128Equiv3D, Fintype.sum_prod_type_right]
        exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun y _ ↦ by
          rw [nyq128Equiv3D.symm_apply_apply]
    have hhead_c : ((1 / 8 : ℝ) : ℂ) • (∑ _l : Fin 216, ∑ d : NyqFine3D128,
        (kHead128 w128DualQ30 pos24CutNyq d : ℂ) • oneV) =
        (((27 : ℝ) *
          ∑ d : NyqFine3D128, kHead128 w128DualQ30 pos24CutNyq d : ℝ) : ℂ) • oneV := by
      simp only [← Finset.sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      exact congrArg (· • oneV) (by push_cast; ring)
    have hmid_c : (-((1 / 8 : ℝ) : ℂ)) • (∑ _l : Fin 216, ∑ b : NyqParity3D,
        (((pos24CutNyq b + pos24MinNyq b) / 2 : ℝ) : ℂ) • ((numElectrons : ℂ) • oneV)) =
        (uenMidpointShift pos24CutNyq pos24MinNyq : ℂ) • oneV := by
      unfold uenMidpointShift
      simp only [smul_smul, ← Finset.sum_smul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, ← Finset.sum_mul]
      exact congrArg (· • oneV) (by push_cast; ring)
    have hpt : ∀ (l : Fin 216) (b : NyqParity3D) (y : NyqGrid3D64),
        (kHead128 w128DualQ30 pos24CutNyq (nyq128Equiv3D (y, b)) : ℂ) • N l b y +
          (kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq (nyq128Equiv3D (y, b)) : ℂ) •
            N l b y =
        (w128DualQ30 (nyq128Equiv3D (y, b)) : ℂ) • N l b y -
          (((pos24CutNyq b + pos24MinNyq b) / 2 : ℝ) : ℂ) • N l b y := fun l b y ↦ by
      rw [← add_smul, ← sub_smul]
      refine congrArg (· • N l b y) ?_
      have hs := kHead128_add_kTail128 w128DualQ30 pos24CutNyq (nyq128Equiv3D (y, b))
      unfold kTailShifted128
      rw [Equiv.symm_apply_apply]
      dsimp only
      push_cast [← hs]
      ring
    simp_rw [smul_sub, Finset.sum_sub_distrib, hd_reindex]
    rw [smul_sub, hhead_c, sub_eq_add_neg, ← neg_smul, add_assoc, ← smul_add,
      ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, hpt, Finset.sum_sub_distrib, ← Finset.smul_sum, hN]
    rw [smul_sub, hmid_c]
    have he2 : (pos24Slot2E2Const : ℂ) • oneV =
        -(((27 : ℝ) *
          ∑ d : NyqFine3D128, kHead128 w128DualQ30 pos24CutNyq d : ℝ) : ℂ) • oneV +
          (uenMidpointShift pos24CutNyq pos24MinNyq : ℂ) • oneV := by
      unfold pos24Slot2E2Const
      rw [show (-(27 : ℝ)) * (∑ d : NyqFine3D128, kHead128 w128DualQ30 pos24CutNyq d) =
        -((27 : ℝ) * ∑ d : NyqFine3D128, kHead128 w128DualQ30 pos24CutNyq d) by ring,
        Complex.ofReal_add, Complex.ofReal_neg, add_smul, neg_smul]
    rw [he2]
    simp only [neg_smul, sub_eq_add_neg]
    abel
  let F : BitAssignment 80 → ℝ → Operator (2 ^ systemQubits) := fun p80 r ↦
    ((pos80Slot2Scale * r : ℝ) : ℂ) • blkSm p80
  change (∑ p80 : BitAssignment 80, F p80 (pos80IdealDist false p80)) *
    fermionicProjector spinUp = bModSlot248 c * fermionicProjector spinUp
  rw [sum_over_pos80IdealDist_support false F (fun p80 ↦ by simp [F]),
    Fintype.sum_sum_type, Matrix.add_mul]
  dsimp only [F]
  rw [hHeadSum, hTailSum, ← Matrix.add_mul]
  refine congrArg (· * fermionicProjector spinUp)
    (hAlg (1 : Operator (2 ^ systemQubits))
      (fun l b y ↦ nTot_sp (uenSubGridKet48 c l b y)) fun l b ↦ ?_)
  have hrk : (∑ y : NyqGrid3D64, rk1_sp (uenSubGridKet48 c l b y)) = 1 := by
    have hvee : (∑ y : NyqGrid3D64, rk1_sp (veeSubGridKet b y)) = 1 := by
      ext u v
      rw [Matrix.sum_apply, Matrix.one_apply]
      exact veeSubGridKet_complete b u v
    simp_rw [show ∀ y, rk1_sp (uenSubGridKet48 c l b y) =
      (oneElecNucDiag48 c l).1 * rk1_sp (veeSubGridKet b y) * (oneElecNucDiag48 c l).1ᴴ from
        fun y ↦ (diagonal_conj_rk1_sp _ _).symm]
    rw [← Finset.sum_mul, ← Matrix.mul_sum, hvee, Matrix.mul_one]
    simpa only [Matrix.star_eq_conjTranspose] using (oneElecNucDiag48 c l).2.2
  simp only [nTot_sp, nSub_sp, op_sp]
  rw [Finset.sum_comm]
  simp_rw [← QRegister.embedMatrix_sum, hrk, QRegister.embedMatrix_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
theorem blkSmSlot2_eq_cleanConj (qft : FullSysQft654Bundle)
    (hqft : qft.uQft654 = qft64Ideal654Unitary) (c : Configuration) (p80 : BitAssignment 80)
    (l : Fin 216) (anc : Fin 218) (b₁ : NyqParity3D) (hl : payloadNucNat p80 = l.val)
    (hanc : payloadAncNat p80 = anc.val) (hb₁ : payloadB1Parity p80 = b₁) :
    blkSmSlot2 qft c p80 =
      (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1ᴴ *
        ((sysNucDiag48 c l).1 * ((veeSysProdUnitary b₁).1ᴴ * Matrix.diagonal
          (fun z : Fin (2 ^ systemQubits) ↦ if posPhaseBit true pos24TailSign pos24TailMag30
            (coreBetaOf false p80 z) then (-1 : ℂ) else 1) *
          (veeSysProdUnitary b₁).1) * (sysNucDiag48 c l).1ᴴ) *
        (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1 := by
  unfold blkSmSlot2
  rw [smConj_eq_sm654Conj_of_comm_rProj24
      (pos24ConjCore80_slice_slot2_comm_rProj24 qft hqft c p80),
    sysBlockAtPayloadGen_pos24ConjCore80_slot2_raw qft hqft c p80,
    hl, hanc, hb₁, sa_conj_conj_eq smToTwos654SysUnitary_sa]
  exact conj_phase_diag_outer (slot2GlobalPhase c l) (star_slot2GlobalPhase_mul_self c l)
    (fun z ↦ ∏ e : Fin 218, karatsubaOutPhase3D (slotCoordSys z e)) _
    star_prod_karatsubaOutPhase3D_mul_self (veeSysProdUnitary b₁).1 (sysNucDiag48 c l).1
    (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1 _
    (slot2OuterFactor_eq offsetSysUnitary_eq_fwdPerm c l anc b₁
      (qft64OffsetUnitary3D_mul_offset18Unitary b₁) list_ofFn_rEl_prod_mul
      list_ofFn_rEl_outPhase_eq_diagonal)
theorem conj_eq_one_diag_eq {D : ℕ} {P N V : Operator D} {f g : Fin D → ℂ} (hP : P = 1)
    (hfg : ∀ z, f z = g z) : Pᴴ * (N * (Vᴴ * Matrix.diagonal f * V) * Nᴴ) * P = N *
    (Vᴴ * Matrix.diagonal g * V) * Nᴴ := by
  rw [hP, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    congrArg Matrix.diagonal (funext hfg)]
theorem blkSmSlot2_tail_eq
    (qft : FullSysQft654Bundle) (hqft : qft.uQft654 = qft64Ideal654Unitary)
    (c : Configuration) (l : Fin 216) (anc : Fin 218) (dp : Fin 8)
    (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool) :
    let b₁ := nyqParity3DEquivFin8.symm dp
    let p80 := tailWitnessPayload80 0 l.val anc.val 0 dp keep.val th rj
    blkSmSlot2 qft c p80 =
      (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1ᴴ *
        ((sysNucDiag48 c l).1 *
          ((veeSysProdUnitary b₁).1ᴴ *
            Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
              let rOrbit := tetRank65 (canonTriple128 (nyq128Equiv3D (slotCoordSys z 0, b₁)))
              if (if keep.val < (pos24TailMag30 rOrbit).val then !(pos24TailSign rOrbit)
                else rj)
              then (-1 : ℂ) else 1) *
            (veeSysProdUnitary b₁).1) *
          (sysNucDiag48 c l).1ᴴ) *
        (permutationUnitary (permElectron (Equiv.swap (0 : Fin 218) anc))).1 := by
  intro b₁ p80
  rcases tailWitnessPayload80_slot2_meta l anc dp keep th rj with ⟨hl, hanc, hb₁⟩
  rw [blkSmSlot2_eq_cleanConj qft hqft c p80 l anc b₁ hl hanc hb₁]
  suffices hfg : (fun z : Fin (2 ^ systemQubits) ↦
      if posPhaseBit true pos24TailSign pos24TailMag30 (coreBetaOf false p80 z)
      then (-1 : ℂ) else 1) = _ by rw [hfg]
  funext z
  refine congrArg (fun b : Bool ↦ if b then (-1 : ℂ) else 1) ?_
  let dTail := nyq128Equiv3D (slotCoordSys z 0, b₁)
  let rOrbit := tetRank65 (canonTriple128 dTail)
  let rCore := QRegExt.ofFin posCoreWires
  let β := coreBetaOf false p80 z
  rcases coreBetaOf_false_wSlots p80 z with ⟨hw2, hw1, hw0⟩
  have hwSub : β (wSubReject rCore) = 0 := coreBetaOf_payload false p80 z ⟨62, by decide⟩
  have hwHead : β (wIsHead rCore) = 0 := coreBetaOf_payload false p80 z ⟨30, by decide⟩
  have hwRj : (β (wRejectZero rCore) == 1) = rj := by
    rw [show β (wRejectZero rCore) = if rj then 1 else 0 from
      coreBetaOf_payload false p80 z ⟨79, by decide⟩]
    cases rj <;> rfl
  have hrNuc : regVal (rNucIdx rCore) β = l.val :=
    (regVal_coreBetaOf_payload _ 6 (by decide) (fun _ ↦ rfl) false p80 z).trans hl
  have hrAnc : regVal (rAnchorIdx rCore) β = anc.val :=
    (regVal_coreBetaOf_payload _ 14 (by decide) (fun _ ↦ rfl) false p80 z).trans hanc
  have hrPart : regVal (rPartnerIdx rCore) β = 0 :=
    (regVal_coreBetaOf_payload _ 22 (by decide) (fun _ ↦ rfl) false p80 z).trans
      ((congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j : Fin 8
        ↦ by
        dsimp only [p80, tailWitnessPayload80]
        fin_cases j <;> rfl)).trans (root_bitsVal_z2BitOfNat_of_lt_slot2 (by decide)))
  have hrKeep : regVal (rTailKeep30 rCore) β = keep.val :=
    (regVal_coreBetaOf_payload _ 32 (by decide) (fun _ ↦ rfl) false p80 z).trans
      ((congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j : Fin
        30 ↦ by
        have := j.isLt
        dsimp only [p80, tailWitnessPayload80, pos80SubIdx]
        simp only [show ¬(32 + j.val < 3) by omega, show ¬(32 + j.val < 6) by omega,
          show ¬(32 + j.val < 14) by omega, show ¬(32 + j.val < 22) by omega,
          show ¬(32 + j.val < 30) by omega, beq_false_of_ne (by omega : 32 + j.val ≠ 30),
          beq_false_of_ne (by omega : 32 + j.val ≠ 31), show 32 + j.val < 62 by omega,
          show 32 + j.val - 32 = j.val by omega, ↓reduceIte, Bool.false_eq_true])).trans
        (root_bitsVal_z2BitOfNat_of_lt_slot2
          (lt_of_lt_of_le keep.isLt (tailSpan8_lt_two_pow_30 dp))))
  have hB1 (w : Fin 3) :
      (if parity3OfReg (rCosetB1 rCore) β w then (1 : ℕ) else 0) = (b₁ w).val := by
    let idx80 : Fin 80 := ⟨w.val, Nat.lt_trans w.isLt (by decide)⟩
    have hb_eq : β (rCosetB1 rCore w) = p80 idx80 := by
      change coreBetaOf false p80 z ((rCosetB1 rCore) w) = p80 idx80
      rw [show (rCosetB1 rCore) w = rPosSubLocal idx80 from
        Fin.ext (congrArg (3954 + ·) (Nat.zero_add w.val)), coreBetaOf_payload]
    have hfin2 : (⟨(β (rCosetB1 rCore w)).val, ZMod.val_lt _⟩ : Fin 2) = b₁ w :=
      Fin.ext (hb_eq ▸ congrArg (fun f ↦ (f w).val) hb₁)
    rw [show parity3OfReg (rCosetB1 rCore) β w = decide (b₁ w = 1) by
      dsimp only [parity3OfReg]
      rw [← hfin2]
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (β (rCosetB1 rCore w)) with h | h <;>
        rw [h] <;> decide, ite_decide_fin2_eq_one_nat_slot2]
  have hHead0 : headPhaseBitSpec β = false := by
    unfold headPhaseBitSpec
    dsimp only [β, rCore] at hwSub hwHead ⊢
    simp only [hw2, hw1, hw0, hwSub, hwHead, show ((0 : ZMod 2) == 1) = false by decide,
      Bool.and_false, Bool.not_false, ↓reduceIte]
  have hTail : tailAndSlackPhaseBitSpec true pos24TailSign pos24TailMag30 β =
      if keep.val < (pos24TailMag30 rOrbit).val then !(pos24TailSign rOrbit) else rj := by
    unfold tailAndSlackPhaseBitSpec
    dsimp only [β, rCore] at hwSub hwHead hwRj hrNuc hrAnc hrPart hrKeep hB1 ⊢
    simp only [hw2, hw1, hw0, hwSub, hwHead, hwRj, hrNuc, l.isLt, hrAnc, anc.isLt, hrPart, hrKeep]
    rw [show ((!((0 : ZMod 2) == 1) &&
        decide ((!((0 : ZMod 2) == 1)) = true → True) && decide True &&
        decide ((((0 : ZMod 2) == 1 && !((0 : ZMod 2) == 1)) = true) → 0 < 217))) = true by decide]
    simp only [show ((0 : ZMod 2) == 1) = false by decide, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, hB1, slotSubGridCoord64_coreBetaOf_slot2_eq]
    rw [show (fun w : Fin 3 ↦ (⟨2 * (slotCoordSys z 0 w).val + (b₁ w).val, by
        have := (slotCoordSys z 0 w).isLt
        have := (b₁ w).isLt
        omega⟩ : Fin 128)) = dTail
      from funext fun w ↦ Fin.ext (nyq128Equiv3D_val (slotCoordSys z 0) b₁ w).symm]
  unfold posPhaseBit
  change Bool.xor (headPhaseBitSpec β)
    (tailAndSlackPhaseBitSpec true pos24TailSign pos24TailMag30 β) = _
  rw [hHead0, hTail, Bool.false_xor]
theorem tierBB2RawId_mul_fermionicProjector_eq (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) : ((pos80Slot2Scale : ℂ) • (smToTwosSysUnitary.1 *
    tierBB2RawId c * smToTwosSysUnitary.1)) * fermionicProjector spinUp = bModSlot248 c *
    fermionicProjector spinUp := by
  change ((pos80Slot2Scale : ℂ) • (smToTwosSysUnitary.1 *
    coherentSysOp80 tierBQftFull c false (pos80IdealDist false) * smToTwosSysUnitary.1)) *
    fermionicProjector spinUp = _
  unfold coherentSysOp80
  rw [smul_conj_sum_real_smul pos80Slot2Scale smToTwosSysUnitary.1 (pos80IdealDist false)
    (fun p80 ↦ sysBlockAtPayloadGen hkFlag80 (pos24ConjCore80 tierBQftFull c).1 false p80)]
  refine slot2_witnessSum_mul_fermionicProjector_eq c spinUp (blkSmSlot2 tierBQftFull c)
    (fun l k pid sm ↦ ?_) (fun l anc dp ↦ slot2_tail_keep_th_rj_sum_eq_of_slices
      tierBQftFull c l anc dp (blkSmSlot2_tail_eq tierBQftFull rfl c l anc dp)
      (slot2Tail_mag_le_span dp)
      (fun y ↦ veeSysProdUnitary_conj_slotProj (nyqParity3DEquivFin8.symm dp) 0 y)
      (fun y ↦ sysNucDiag48_conj_op_veeSubGridKet c l (nyqParity3DEquivFin8.symm dp) y 0))
  let dH := pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm
  let y0 := (nyq128Equiv3D.symm dH).1
  let b := (nyq128Equiv3D.symm dH).2
  refine sum_bool_bool_mul_eq_four_smul_of_half
    (fun th rj ↦ blkSmSlot2 tierBQftFull c (headWitnessPayload80 0 l.val 0 k pid sm th rj))
    (sysNucDiag48 c l).1 (veeSysProdUnitary b).1
    (fun th ↦ Matrix.diagonal fun z : Fin (2 ^ systemQubits) ↦
      if slot2HeadBchBit y0 th z then (-1 : ℂ) else 1)
    (fermionicProjector spinUp) _ (fun th rj ↦ ?_) ?_
  · let p80 := headWitnessPayload80 0 l.val 0 k pid sm th rj
    rcases headWitnessPayload80_slot2_meta l k pid sm th rj with ⟨hl, hanc, hb₁⟩
    rw [blkSmSlot2_eq_cleanConj tierBQftFull rfl c p80 l 0 b hl hanc hb₁]
    refine conj_eq_one_diag_eq permutationUnitary_permElectron_swap_zero fun z ↦
      congrArg (fun flag : Bool ↦ if flag then (-1 : ℂ) else 1) ?_
    let rCore := QRegExt.ofFin posCoreWires
    let β := coreBetaOf false p80 z
    rcases coreBetaOf_false_wSlots p80 z with ⟨hw2, hw1, hw0⟩
    have hwSub : β (wSubReject rCore) = 0 := coreBetaOf_payload false p80 z ⟨62, by decide⟩
    have hwHead : β (wIsHead rCore) = 1 := coreBetaOf_payload false p80 z ⟨30, by decide⟩
    have hwTh : (β (wHeadThresh rCore) == 1) = th := by
      rw [show β (wHeadThresh rCore) = if th then 1 else 0 from
        coreBetaOf_payload false p80 z ⟨31, by decide⟩]
      cases th <;> rfl
    have hrNuc : regVal (rNucIdx rCore) β = l.val :=
      (regVal_coreBetaOf_payload _ 6 (by decide) (fun _ ↦ rfl) false p80 z).trans hl
    have hrAnc : regVal (rAnchorIdx rCore) β = 0 :=
      (regVal_coreBetaOf_payload _ 14 (by decide) (fun _ ↦ rfl) false p80 z).trans hanc
    have hTail0 : tailAndSlackPhaseBitSpec true pos24TailSign pos24TailMag30 β = false := by
      unfold tailAndSlackPhaseBitSpec
      dsimp only [β, rCore] at hwSub hwHead hrNuc hrAnc ⊢
      simp only [hw2, hw1, hw0, hwSub, hwHead, hrNuc, l.isLt, hrAnc,
        show ((0 : ZMod 2) == 1) = false by decide, show ((1 : ZMod 2) == 1) = true by decide,
        show (0 : ℕ) < 218 by decide, Bool.not_false, Bool.false_eq_true, implies_true,
        false_implies, decide_true, Bool.and_self, Bool.not_true, ↓reduceIte]
    have hFine : fineCoordOfReg21 (rHeadFine21 rCore) β = dH := funext fun w ↦ Fin.ext (by
      dsimp only [fineCoordOfReg21]
      let fineH := (dH 0).val + 128 * (dH 1).val + 16384 * (dH 2).val
      refine (congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j :
        Fin 7 ↦ ?_)).trans
        (root_bitsVal_z2BitOfNat_of_lt_slot2 (dH w).isLt)
      let idx80 : Fin 80 := ⟨32 + 7 * w.val + j.val, by linarith [w.isLt, j.isLt]⟩
      change coreBetaOf false p80 z _ = _
      rw [show ((rHeadFine21 rCore).slice (7 * w.val) 7 (by omega)) j = rPosSubLocal idx80 from
        Fin.ext (by
          change 3954 + (32 + (7 * w.val + j.val)) = 3954 + (32 + 7 * w.val + j.val)
          omega),
        coreBetaOf_payload,
        show p80 idx80 = z2BitOfNat fineH (7 * w.val + j.val) by
          dsimp only [p80, headWitnessPayload80, fineH, idx80]
          fin_cases w <;> fin_cases j <;> rfl]
      apply ZMod.val_injective
      rw [z2BitOfNat_val, z2BitOfNat_val, pow_add, ← Nat.div_div_eq_div_mul,
        show fineH / 2 ^ (7 * w.val) = (dH w).val + 128 * (fineH / 2 ^ (7 * w.val + 7)) by
          have := (dH 0).isLt
          have := (dH 1).isLt
          have := (dH 2).isLt
          fin_cases w <;> dsimp [fineH] <;> omega]
      have := (dH w).isLt
      fin_cases j <;> dsimp <;> omega)
    have hHead : headPhaseBitSpec β = slot2HeadBchBit y0 th z := by
      unfold headPhaseBitSpec
      dsimp only [β, rCore] at hwSub hwHead hwTh hrNuc hrAnc hFine ⊢
      simp only [hw2, hw1, hw0, hwSub, hwHead, hwTh, hrNuc, l.isLt, hrAnc, hFine]
      rw [show (((((0 : ZMod 2) == 0) && !((0 : ZMod 2) == 1)) && !((0 : ZMod 2) == 1) &&
          (decide ((!((0 : ZMod 2) == 1)) = true → True) && decide (0 < 218)) &&
          ((1 : ZMod 2) == 1))) = true by decide]
      simp only [show (!((0 : ZMod 2) == 1)) = true by decide, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, Bool.true_or, Bool.true_and,
        slotSubGridCoord64_coreBetaOf_slot2_eq]
      rw [show (fun w : Fin 3 ↦ (⟨(dH w).val / 2, Nat.div_lt_of_lt_mul (dH w).isLt⟩ : Fin 64)) = y0
        from funext fun w ↦ Fin.ext (nyq128Equiv3D_symm_fst_val_slot2 dH w).symm]
      rfl
    unfold posPhaseBit
    change Bool.xor (headPhaseBitSpec β)
      (tailAndSlackPhaseBitSpec true pos24TailSign pos24TailMag30 β) = _
    rw [hHead, hTail0, Bool.xor_false]
  · let count : Fin (2 ^ systemQubits) → ℕ :=
      fun z ↦ (Finset.univ.filter (fun e : Fin 218 ↦ decide (slotCoordSys z e = y0))).card
    let U : Operator (2 ^ systemQubits) := (veeSysProdUnitary b).1 * (sysNucDiag48 c l).1ᴴ
    have hU : Uᴴ * U = 1 := mul_adj_conjTranspose_mul_self
      (by simpa only [Matrix.star_eq_conjTranspose] using (veeSysProdUnitary b).2.1)
      (by simpa only [Matrix.star_eq_conjTranspose] using (sysNucDiag48 c l).2.2)
    have hUU' : U * Uᴴ = 1 := mul_adj_mul_conjTranspose_self
      (by simpa only [Matrix.star_eq_conjTranspose] using (sysNucDiag48 c l).2.1)
      (by simpa only [Matrix.star_eq_conjTranspose] using (veeSysProdUnitary b).2.2)
    have hD_sum : Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦ (count z : ℂ)) =
        ∑ e : Fin 218, Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
          if slotCoordSys z e = y0 then (1 : ℂ) else 0) := by
      rw [sum_diagonal_eq_slot2]
      refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
      simp only [count, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
        decide_eq_true_eq, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    have hconj_N : Uᴴ * Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦ (count z : ℂ)) * U =
        nTot_sp (uenSubGridKet48 c l b y0) := by
      dsimp only [U]
      rw [← conj_outer_inner_eq (sysNucDiag48 c l).1 (veeSysProdUnitary b).1, hD_sum,
        conj_finset_sum_eq]
      simp_rw [veeSysProdUnitary_conj_slotProj b _ y0]
      rw [conj_finset_sum_eq]
      exact Finset.sum_congr rfl fun e _ ↦ sysNucDiag48_conj_op_veeSubGridKet c l b y0 e
    rw [smul_add_diagonal_eq,
      conj_outer_inner_eq (sysNucDiag48 c l).1 (veeSysProdUnitary b).1]
    refine diag_bch_lcu_eq_one_sub_of_cubic_zero
      (nSub_cubic_mul_fermionicProjector_zero
        (uenSubGridKet48_norm_sq c l b y0) spinUp Finset.univ)
      hU (mul_eq_left_mul_of_conj_eq hUU' hconj_N) fun z hle ↦ ?_
    have hsign : ∀ flag : Bool, (if flag then (-1 : ℂ) else 1) = (-1 : ℂ) ^ flag.toNat := by
      rintro (_ | _) <;> simp
    rw [hsign, hsign]
    simpa only [slot2HeadBchBit, count, Nat.min_eq_left hle] using
      proj38_zeroParity_negated_lcu_eq_min_card
        (Finset.univ.filter (fun e : Fin 218 ↦ decide (slotCoordSys z e = y0))) hle
theorem vepFromSlot2Op_mul_fermionicProjector_eq (spinUp : Finset (Fin numElectrons))
    {A B : Configuration → Operator (2 ^ systemQubits)} (hIdleA : ∀ (zP : NyqFine3D512) (M :
    Operator (2 ^ 24)), A (cfgProjZ512 zP) * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix
    M * A (cfgProjZ512 zP)) (hIdleB : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ 24)), B
    (cfgProjZ512 zP) * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * B (cfgProjZ512
    zP)) (hEq : ∀ zP : NyqFine3D512, A (cfgProjZ512 zP) * fermionicProjector spinUp = B
    (cfgProjZ512 zP) * fermionicProjector spinUp) : vepFromSlot2Op A * fermionicProjector
    spinUp = vepFromSlot2Op B * fermionicProjector spinUp := by
  suffices hsub : (vepFromSlot2Op A - vepFromSlot2Op B) * elecFermionicProjector spinUp = 0 by
    refine sub_eq_zero.mp ?_
    rw [← sub_mul, ← elecFermionicProjector_mul_fermionicProjector spinUp, ← Matrix.mul_assoc,
      hsub, Matrix.zero_mul]
  rw [← vepFromSlot2Op_sub A B]
  unfold vepFromSlot2Op vepGen
  rw [smul_mul_assoc, Finset.sum_mul]
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun bP _ ↦ ?_)
  let U := (rProj24_sp.embedUnitary (uProjPlus512SM_3D bP)).1
  have hUPe : U * elecFermionicProjector spinUp = elecFermionicProjector spinUp * U :=
    (elecFermionicProjector_comm_embedMatrix spinUp (uProjPlus512SM_3D bP).1).symm
  rw [Matrix.mul_assoc, hUPe]
  let S := ∑ yIdx : Fin (2 ^ 24), projBasisGen rProj24_sp yIdx *
    (A (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP))) -
      B (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP))))
  suffices hS : S * elecFermionicProjector spinUp = 0 by
    rw [show (Uᴴ * S) * (elecFermionicProjector spinUp * U) =
      Uᴴ * (S * elecFermionicProjector spinUp) * U by simp only [Matrix.mul_assoc],
      hS, Matrix.mul_zero, Matrix.zero_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun yIdx _ ↦ ?_
  let zP := nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP)
  rw [Matrix.mul_assoc]
  suffices hz :
      (A (cfgProjZ512 zP) - B (cfgProjZ512 zP)) * elecFermionicProjector spinUp = 0 by
    rw [hz, Matrix.mul_zero]
  change (A (cfgProjZ512 zP) - B (cfgProjZ512 zP)) *
    projLift0Gen rProj24_sp (fermionicProjector spinUp) = 0
  unfold projLift0Gen
  rw [Matrix.mul_sum]
  refine Finset.sum_eq_zero fun uIdx _ ↦ ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    show (A (cfgProjZ512 zP) - B (cfgProjZ512 zP)) * (projShift0Gen rProj24_sp uIdx)ᴴ =
      (projShift0Gen rProj24_sp uIdx)ᴴ * (A (cfgProjZ512 zP) - B (cfgProjZ512 zP)) by
      unfold projShift0Gen
      rw [← rProj24_sp.embedMatrix_conjTranspose, sub_mul, mul_sub, hIdleA zP, hIdleB zP],
    Matrix.mul_assoc _ _ (fermionicProjector _),
    sub_mul, hEq zP, sub_self, Matrix.mul_zero, Matrix.zero_mul]
theorem isHermitian_gridSandwich_slot2 {M : Operator (2 ^ systemQubits)} (hM : M.IsHermitian) :
    (SpecsAux.gridProjector * M *
      SpecsAux.gridProjector).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    SpecsAux.gridProjector_isHermitian.eq, hM.eq, Matrix.mul_assoc]
theorem vepFromSlot2Op_isHermitian_of_idle {B : Configuration → Operator (2 ^ systemQubits)}
    (hHerm : ∀ zP : NyqFine3D512, (B (cfgProjZ512 zP)).IsHermitian) (hIdle : ∀ (zP :
    NyqFine3D512) (M : Operator (2 ^ 24)), B (cfgProjZ512 zP) * rProj24_sp.embedMatrix M =
    rProj24_sp.embedMatrix M * B (cfgProjZ512 zP)) : (vepFromSlot2Op B).IsHermitian := by
  rw [Matrix.IsHermitian, vepFromSlot2Op, vepGen, Matrix.conjTranspose_smul,
    show star (((1 : ℝ) / (108 * 8) : ℂ)) = ((1 : ℝ) / (108 * 8) : ℂ) by norm_num,
    Matrix.conjTranspose_sum]
  refine congrArg (((1 : ℝ) / (108 * 8) : ℂ) • ·) (Finset.sum_congr rfl fun bP _ ↦ ?_)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_sum]
  have hinner : (∑ yIdx : Fin (2 ^ 24), (projBasisGen rProj24_sp yIdx * B (cfgProjZ512
      (nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP))))ᴴ) = ∑ yIdx : Fin (2 ^ 24), projBasisGen
      rProj24_sp yIdx * B (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP))) :=
    Finset.sum_congr rfl fun yIdx _ ↦ by
      let zP := nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP)
      rw [Matrix.conjTranspose_mul, (hHerm zP).eq,
        (projBasisGen_isHermitian rProj24_sp yIdx).eq]
      exact hIdle zP (matUnit24 yIdx yIdx)
  rw [hinner, Matrix.mul_assoc]
theorem agreesOnFermionicSector_of_isHermitian_and_mul_eq {spinUp : Finset (Fin numElectrons)}
    {M₁ M₂ T : Operator (2 ^ systemQubits)} {ε : ℝ} (hHerm₁ : M₁.IsHermitian)
    (hHerm₂ : M₂.IsHermitian) (hMulEq : M₁ * fermionicProjector spinUp = M₂ *
    fermionicProjector spinUp) (hAgrees₂ : AgreesOnFermionicSector spinUp M₂ T ε) :
    AgreesOnFermionicSector spinUp M₁ T ε := by
  let P := fermionicProjector spinUp
  have hLeftEq : P * M₁ = P * M₂ := by
    simpa only [P, Matrix.conjTranspose_mul, (fermionicProjector_isHermitian spinUp).eq,
      hHerm₁.eq, hHerm₂.eq] using congrArg Matrix.conjTranspose hMulEq
  refine ⟨hMulEq.trans (hAgrees₂.1.trans hLeftEq.symm), ?_⟩
  change ‖P * (M₁ - T) * P‖ ≤ ε
  rw [mul_sub, sub_mul, Matrix.mul_assoc, hMulEq, ← Matrix.mul_assoc, ← sub_mul, ← mul_sub]
  exact hAgrees₂.2
end ConfigPos24Slot2FermionicBridge

end Pos24Slot2FermionicBridge
end
end ModPos24Slot2FermionicBridge

end QuantumComputation.Specs.StoppingPowerSolution
