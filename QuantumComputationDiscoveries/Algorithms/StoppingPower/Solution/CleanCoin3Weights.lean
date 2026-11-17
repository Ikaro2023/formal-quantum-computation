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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.CatPrepUltra1q
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3BoothPartner

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspCleanCoinAndGuardBridge

section
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency true
namespace GqspCleanCoinAndGuardBridge
section Part1_ArbitraryWeightCoinAndSub1622Bundles
set_option exponentiation.threshold 5000
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority := 1000000) instNeZeroTwoPowChiralSec1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysPrepare6Slot (fullSysCoinIdx)
open SegmentAndTopClosure (rCleanSubW compressCleanUnitary)
open ZeroAncillaUSP (HSTGate)
open ZeroSubwireCoinPrep80 (coinHwa wIdealRat)
open Coin3PerHorizon5799 (CleanPrepProg AffineLayer2 AnfLayer3 sCoinAnc4)
open Leaf3MidKickAndPrepCore (Coin3CleanProgSpec)
open CoinPrepSub85AndAlphaOpt (pCoinPrepParityGen validDyn_pCoinPrepParityGen
  pCoinPrepParityGen_preserves_clean uCoin3ParityGen)
/-- Certified 4-wire `CleanPrepProg 4` 3-coin synthesis witness for an arbitrary 6-channel target
weight vector `wTarget : Fin 6 → ℝ` at block-encoding scale `α_real`. -/
structure Coin3CleanProgSpecOfWeights
    (wTarget : Fin 6 → ℝ) (α_real : ℝ) (tCoin : ℕ) (err_w : ℝ) where
  /-- Underlying 4-wire `.TOFF`-free `CleanPrepProg 4` program (`3` coin wires + `1` clean
  ancilla). -/
  pPrep : CleanPrepProg 4
  /-- Certified `.T`-gate upper bound `pPrep.tBound ≤ tCoin`. -/
  hT : pPrep.tBound ≤ tCoin
  /-- Dynamic-AND workspace validity on `sCoinAnc4`. -/
  hValid : CleanPrepProg.ValidDyn sCoinAnc4 pPrep
  /-- Clean-ancilla preservation on `wCoinAnc`. -/
  hClean :
    (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 * pPrep.toCircuit.eval.1 *
        (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 =
      pPrep.toCircuit.eval.1 * (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0
  /-- Compressed 3-qubit coin unitary `Unitary (2 ^ 3)`. -/
  uCoin : Unitary (2 ^ 3)
  /-- Exact agreement between `uCoin` and `compressCleanUnitary coinHwa`. -/
  hUCoin : uCoin = compressCleanUnitary coinHwa pPrep.toCircuit.eval hClean
  /-- Certified 6-channel L1 weight error bound against `wTarget`. -/
  hWeightErr : ∑ k : Fin 6, |α_real * ‖uCoin.1 (fullSysCoinIdx k) 0‖ ^ 2 - wTarget k| ≤ err_w
/-- Forgetful projection from `Coin3CleanProgSpecOfWeights` to `Coin3CleanProgSpec` preserving the
identical `pPrep` and `uCoin` data so all `zeroSubwireCleanProgPrepBundle` combinators reuse
directly. -/
noncomputable def Coin3CleanProgSpecOfWeights.toDummySpec
    {wTarget : Fin 6 → ℝ} {α_real : ℝ} {tCoin : ℕ} {err_w : ℝ}
    (s : Coin3CleanProgSpecOfWeights wTarget α_real tCoin err_w) :
    Coin3CleanProgSpec 1 tCoin (∑ k : Fin 6, |(1 : ℝ) * ‖s.uCoin.1 (fullSysCoinIdx k) 0‖ ^ 2 -
      wIdealRat k|) :=
  ⟨s.pPrep, s.hT, s.hValid, s.hClean, s.uCoin, s.hUCoin, le_rfl⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Turnkey constructor building `Coin3CleanProgSpecOfWeights` from `pCoinPrepParityGen w0 ls2
ls3`. -/
noncomputable def mkCoin3CleanProgSpecOfParityGenWeights
    {wTarget : Fin 6 → ℝ} {α_real err_w : ℝ} {tCoin : ℕ}
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3)
    (hT : (pCoinPrepParityGen w0 ls2 ls3).tBound ≤ tCoin)
    (hWeightErr : ∑ k : Fin 6, |α_real * ‖(uCoin3ParityGen w0 ls2 ls3).1 (fullSysCoinIdx k) 0‖ ^ 2 -
      wTarget k| ≤ err_w) :
    Coin3CleanProgSpecOfWeights wTarget α_real tCoin err_w :=
  ⟨pCoinPrepParityGen w0 ls2 ls3, hT, validDyn_pCoinPrepParityGen w0 ls2 ls3,
    pCoinPrepParityGen_preserves_clean w0 ls2 ls3, uCoin3ParityGen w0 ls2 ls3, rfl, hWeightErr⟩
end
end Part1_ArbitraryWeightCoinAndSub1622Bundles
section Part2_ArbitraryWeightPertCore
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority := 1000000) instNeZeroTwoPowChiralSec2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
open SpecsAux.FullScaleBESector (IsQubitizedBlockEncodingUnitary AgreesOnFermionicSector)
-- Root solution namespace already active.
open PosMomSelectDynamic (unitaryConj)
open SingleRBEGridGuardWalk (ghostZeroedBE)
open SixSlotEndpointJunctionBridge (gridValidBool endpointHeff isQubitizedBE_ghostZeroedBE)
open FullSysPrepare6Slot (coinSelOutcome)
open OraAndPrepBundle (PosPostPrepCert coreUnitaryFromFullSys fin6Tuple fin6Tuple_0 fin6Tuple_1
  fin6Tuple_2 fin6Tuple_3 fin6Tuple_4 fin6Tuple_5)
open FullSysCatSegmentBridge (FullSysQft654Bundle FullSysPrepareBundle FullSysSelectOracleBundle
  fullSysRawAncWires fullSysSelectEffUnitary fullSysRawBEUnitary)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open FullSysFullPrepareAndTopConcrete (coreAncSym coreSysSym selCoin3Sym coreHadamardUnitary
  unitaryConj_mul_outer)
open FullSysPosSlots24AndTopConcrete (smToTwosSys_mul_self_val)
open TwosCompAndWire0Cancel (smToTwosSysUnitary smToTwosSysUnitary_conjTranspose
  smToTwosSys_comm_gridProjector smToTwosSys_comm_fermionicProjector)
open GeneralBetaAndAlphaTopEndpoint (endpoint_heff_of_target_sum)
open CoherentEndpoint (commute_gridProjector_of_sandwiched)
open ZeroSubwireCoinPrep80 (rCoin3Core)
open ZeroSubwireGridPert80 (beCoreBlock_eq_coreUnitaryFromFullSys norm_triple_mul_le_local)
open ZeroSubwireHarmonicGridPert (zeroSubwireConstPrepUnitary
  zeroSubwire_coin_topBlock_sum_of_unitary wActOfUnitary wActOfUnitary_nonneg
  norm_sq_uCoin_eq_inv_mul_wActOfUnitary forall_fin6_prop)
/-- Generalized 8-coin block-encoding operator table supporting arbitrary `s5 : MomSingleSlotOracle
80 48 5`
(specializing to `bCoinTierBS1 s1 s3 b2Act b4Act cfg` when `s5 = zeroMomSlotOracle5 80 48`, and to
the
two-slot `(s3, s5)` `(momResOp, posCuspOp)` split on coins `6` and `7`). -/
noncomputable def bCoinGenS1S3S5
    (s0 : MomSingleSlotOracle 80 48 0)
    (s1 : MomSingleSlotOracle 80 48 1)
    (s3 : MomSingleSlotOracle 80 48 3)
    (s5 : MomSingleSlotOracle 80 48 5)
    (b2Act b4Act : Configuration → Operator (2 ^ systemQubits))
    (cfg : Configuration) : Fin 8 → Operator (2 ^ systemQubits) := fun c ↦
  match c.val with
  | 0 => b2Act cfg
  | 1 => b4Act cfg
  | 2 => 1
  | 3 => -1
  | 4 => s0.bUnitTwos cfg
  | 5 => s1.bUnitTwos cfg
  | 6 => s3.bUnitTwos cfg
  | _ => s5.bUnitTwos cfg
theorem wActOfUnitary_le_wTarget_add_err {α_real err_w : ℝ} {uCoin : Unitary (2 ^ 3)}
    {wTarget : Fin 6 → ℝ}
    (hWeightErr : ∑ k : Fin 6, |wActOfUnitary α_real uCoin k - wTarget k| ≤ err_w)
    (k : Fin 6) :
    wActOfUnitary α_real uCoin k ≤ wTarget k + err_w := by
  have hk : |wActOfUnitary α_real uCoin k - wTarget k| ≤ err_w :=
    (Finset.single_le_sum (fun i _ ↦ abs_nonneg _) (Finset.mem_univ k)).trans hWeightErr
  linarith [(abs_le.mp hk).2]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Arbitrary-`(α_real > 0, wTarget)` 6-channel / two-slot `(s3, s5)` `SELECT`+`PREPARE`
grid-perturbation
theorem: bridges any `uCoin` approximating `wTarget` within `err_w` and any 6-slot ideal
target family `target : Fin 6 → Operator (2 ^ systemQubits)` summing to `∑ sixChannelShifted cfg E`
directly to `IsQubitizedBlockEncodingUnitary α_real (Heff_act - E₀ • 1)` +
`AgreesOnFermionicSector`. -/
theorem selOra_uCoin_gridPerturbation_arbitraryWeights_of_core_blocks
    {α_real err_w δ2 δ4 δ_pos ε_id ε_BE : ℝ}
    (hαPos : 0 < α_real) (herr_w : 0 ≤ err_w) (hδ_pos : 0 ≤ δ_pos) (hε_id : 0 ≤ ε_id)
    (wTarget : Fin 6 → ℝ)
    (qftCore : FullSysQft654Bundle)
    (prep : FullSysPrepareBundle 80)
    (post : PosPostPrepCert 80)
    (uCoin : Unitary (2 ^ 3))
    (hPrepEq : ∀ c, prep.uPrep c = zeroSubwireConstPrepUnitary post uCoin)
    (hWeightErr : ∑ k : Fin 6, |wActOfUnitary α_real uCoin k - wTarget k| ≤ err_w)
    (hPrepCap : (wTarget 2 + err_w) * δ2 + (wTarget 4 + err_w) * δ4 ≤ δ_pos)
    (selOra : FullSysSelectOracleBundle 80 48)
    (s0 : MomSingleSlotOracle 80 48 0)
    (s1 : MomSingleSlotOracle 80 48 1)
    (s3 : MomSingleSlotOracle 80 48 3)
    (s5 : MomSingleSlotOracle 80 48 5)
    (b2Act b4Act b2Id b4Id : Configuration → Operator (2 ^ systemQubits))
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
    (E : Fin 6 → ℝ)
    (target : Fin 6 → Operator (2 ^ systemQubits))
    (ε_slot : Fin 6 → ℝ)
    (hTargetSum : ∑ k : Fin 6, target k = ∑ k : Fin 6, sixChannelShifted cfg E k)
    (hSlotsSm : ∀ k : Fin 6,
      let B_unit_id : Fin 6 → Operator (2 ^ systemQubits) := fin6Tuple (s0.bUnitTwos cfg)
          (s1.bUnitTwos cfg) (b2Id cfg) (s3.bUnitTwos cfg) (b4Id cfg) (s5.bUnitTwos cfg)
      AgreesOnFermionicSector spinUp
        (gridProjector *
          (smToTwosSysUnitary.1 * ((wTarget k : ℂ) • B_unit_id k) * smToTwosSysUnitary.1) *
          gridProjector)
        (target k) (ε_slot k))
    (hEpsId : (∑ k : Fin 6, ε_slot k) ≤ ε_id)
    (hEpsBECap : err_w + δ_pos + ε_id ≤ ε_BE)
    (hb2IdHerm : (b2Id cfg).IsHermitian) (hb4IdHerm : (b4Id cfg).IsHermitian)
    (hb2IdNorm : ‖b2Id cfg‖ ≤ 1) (hb4IdNorm : ‖b4Id cfg‖ ≤ 1)
    (hDiff2 : ‖b2Act cfg - b2Id cfg‖ ≤ δ2) (hDiff4 : ‖b4Act cfg - b4Id cfg‖ ≤ δ4)
    (hCoreBlocks :
      let S_core := unitaryConj (post.uPosPost * coreHadamardUnitary 80)
        (coreUnitaryFromFullSys (fullSysSelectEffUnitary qftCore selOra cfg))
      let B_coin := bCoinGenS1S3S5 s0 s1 s3 s5 b2Act b4Act cfg
      S_core.1ᴴ = S_core.1 ∧
        (∀ c : Fin 8,
          let P_c := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)
          P_c * S_core.1 * P_c = P_c * (coreSysSym 80).embedMatrix (B_coin c) * P_c) ∧
        (∀ c₁ c₂ : Fin 8, c₁ ≠ c₂ →
          let P₁ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₁)
          let P₂ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₂)
          P₁ * S_core.1 * P₂ = 0)) :
    ∃ (E₀ δ_prep₀ ε_id₀ : ℝ) (Heff_act Heff_id : Operator (2 ^ systemQubits)),
      0 ≤ δ_prep₀ ∧ 0 ≤ ε_id₀ ∧ δ_prep₀ + ε_id₀ ≤ ε_BE ∧
      Commute (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits))) gridProjector ∧
      IsQubitizedBlockEncodingUnitary α_real
        (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))
        (ghostZeroedBE systemQubits (fullSysRawAncWires 80)
          (by dsimp [fullSysRawAncWires]; omega) gridValidBool
          (fullSysRawBEUnitary qftCore prep selOra cfg)) ∧
      Heff_id.IsHermitian ∧
      Commute Heff_id gridProjector ∧
      ‖gridProjector * (Heff_act - Heff_id) * gridProjector‖ ≤ δ_prep₀ ∧
      AgreesOnFermionicSector spinUp Heff_id
        (smToTwosSysUnitary.1 * hamiltonian cfg * smToTwosSysUnitary.1ᴴ) ε_id₀ := by
  let B_unit_act : Fin 6 → Operator (2 ^ systemQubits) := fin6Tuple (s0.bUnitTwos cfg)
      (s1.bUnitTwos cfg) (b2Act cfg) (s3.bUnitTwos cfg) (b4Act cfg) (s5.bUnitTwos cfg)
  let B_unit_id : Fin 6 → Operator (2 ^ systemQubits) := fin6Tuple (s0.bUnitTwos cfg)
      (s1.bUnitTwos cfg) (b2Id cfg) (s3.bUnitTwos cfg) (b4Id cfg) (s5.bUnitTwos cfg)
  let B_twos_act : Fin 6 → Operator (2 ^ systemQubits) :=
    fun k ↦ (wActOfUnitary α_real uCoin k : ℂ) • B_unit_act k
  let B_twos_id : Fin 6 → Operator (2 ^ systemQubits) := fun k ↦ (wTarget k : ℂ) • B_unit_id k
  let G := gridProjector
  let U := smToTwosSysUnitary.1
  let B_sm_id : Fin 6 → Operator (2 ^ systemQubits) := fun k ↦ U * B_twos_id k * U
  let Heff_sm_id := endpointHeff E (fun k ↦ G * B_sm_id k * G)
  let Heff_id := U * Heff_sm_id * U
  let E₀_id : ℝ := ∑ k : Fin 6, E k
  let δ_s : ℝ := α_real * (‖uCoin.1 2 0‖ ^ 2 - ‖uCoin.1 3 0‖ ^ 2)
  let E₀ : ℝ := E₀_id - δ_s
  let M_act : Operator (2 ^ systemQubits) :=
    (∑ k : Fin 6, B_twos_act k) + (δ_s : ℂ) • (1 : Operator (2 ^ systemQubits))
  let Heff_act : Operator (2 ^ systemQubits) :=
    G * M_act * G + (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits))
  rcases hCoreBlocks with ⟨hS_core_sa, hDiag, hOffDiag⟩
  let S_core := unitaryConj (post.uPosPost * coreHadamardUnitary 80)
    (coreUnitaryFromFullSys (fullSysSelectEffUnitary qftCore selOra cfg))
  let B_coin := bCoinGenS1S3S5 s0 s1 s3 s5 b2Act b4Act cfg
  let U_BE := fullSysRawBEUnitary qftCore prep selOra cfg
  let U_coin := (rCoin3Core 80).embedUnitary uCoin
  have hUBE_eq : U_BE = unitaryConj U_coin S_core := by
    dsimp only [U_BE, fullSysRawBEUnitary, S_core, U_coin]
    rw [hPrepEq cfg, zeroSubwireConstPrepUnitary, beCoreBlock_eq_coreUnitaryFromFullSys,
      ← mul_assoc, unitaryConj_mul_outer (post.uPosPost * coreHadamardUnitary 80) ((rCoin3Core
      80).embedUnitary uCoin)
        (coreUnitaryFromFullSys (fullSysSelectEffUnitary qftCore selOra cfg))]
  have hUBE_sa : U_BE.1ᴴ = U_BE.1 := by
    rw [hUBE_eq]
    exact PosMomSelectDynamic.unitaryConj_conjTranspose hS_core_sa
  have hCoinSum_eq :
      (∑ c : Fin 8, ((‖uCoin.1 c 0‖ ^ 2 : ℝ) : ℂ) • B_coin c) = (α_real : ℂ)⁻¹ • M_act := by
    have hk := norm_sq_uCoin_eq_inv_mul_wActOfUnitary hαPos uCoin
    have hα_ne : (α_real : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hαPos.ne'
    have hδs : ((‖uCoin.1 2 0‖ ^ 2 : ℝ) : ℂ) - ((‖uCoin.1 3 0‖ ^ 2 : ℝ) : ℂ) =
        (α_real : ℂ)⁻¹ * (δ_s : ℂ) := by
      dsimp only [δ_s]
      rw [Complex.ofReal_mul, Complex.ofReal_sub, ← mul_assoc, inv_mul_cancel₀ hα_ne, one_mul]
    dsimp only [M_act, B_twos_act, B_unit_act, B_coin, bCoinGenS1S3S5]
    rw [Fin.sum_univ_eight, Fin.sum_univ_six]
    simp only [fin6Tuple_0, fin6Tuple_1, fin6Tuple_2, fin6Tuple_3, fin6Tuple_4, fin6Tuple_5]
    change _ = _
    rw [show ((‖uCoin.1 0 0‖ ^ 2 : ℝ) : ℂ) = _ from hk 2, show ((‖uCoin.1 1 0‖ ^ 2 : ℝ) : ℂ) =
      _ from hk 4, show ((‖uCoin.1 4 0‖ ^ 2 : ℝ) : ℂ) = _ from hk 0, show ((‖uCoin.1 5 0‖ ^ 2 : ℝ) :
      ℂ) = _ from hk 1,
        show ((‖uCoin.1 6 0‖ ^ 2 : ℝ) : ℂ) = _ from hk 3, show ((‖uCoin.1 7 0‖ ^ 2 : ℝ) : ℂ) =
          _ from hk 5]
    exact MomSlot1DyadicTopAdapter.sum_rearrange_gen
      (α_real : ℂ)⁻¹ (wActOfUnitary α_real uCoin 0) (wActOfUnitary α_real uCoin 1)
      (wActOfUnitary α_real uCoin 2) (wActOfUnitary α_real uCoin 3)
      (wActOfUnitary α_real uCoin 4) (wActOfUnitary α_real uCoin 5)
      ((‖uCoin.1 2 0‖ ^ 2 : ℝ) : ℂ) ((‖uCoin.1 3 0‖ ^ 2 : ℝ) : ℂ) (δ_s : ℂ) hδs
      (s0.bUnitTwos cfg) (s1.bUnitTwos cfg) (b2Act cfg) (s3.bUnitTwos cfg) (b4Act cfg)
      (s5.bUnitTwos cfg) (1 : Operator (2 ^ systemQubits))
  have hTopRaw :
      let sys0 : QRegister systemQubits (systemQubits + fullSysRawAncWires 80) :=
        .block 0 systemQubits (by dsimp [fullSysRawAncWires, systemQubits]; omega)
      let anc0 : QRegister (fullSysRawAncWires 80) (systemQubits + fullSysRawAncWires 80) :=
        .block systemQubits (fullSysRawAncWires 80) le_rfl
      anc0.basisOutcomeProjector 0 * U_BE.1 * anc0.basisOutcomeProjector 0 =
        (α_real : ℂ)⁻¹ •
          (anc0.basisOutcomeProjector 0 * sys0.embedMatrix M_act *
            anc0.basisOutcomeProjector 0) := by
    intro sys0 anc0
    have hSysEq : sys0 = coreSysSym 80 := QRegister.ext (Function.Embedding.ext fun _ ↦ rfl)
    have hAncEq : anc0 = coreAncSym 80 := QRegister.ext (Function.Embedding.ext fun _ ↦ rfl)
    rw [hSysEq, hAncEq, hUBE_eq, zeroSubwire_coin_topBlock_sum_of_unitary uCoin S_core B_coin hDiag
      hOffDiag, hCoinSum_eq, QRegister.embedMatrix_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hSubAct : Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)) = G * M_act * G :=
    add_sub_cancel_right _ _
  have hBEAct : IsQubitizedBlockEncodingUnitary α_real
      (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))
      (ghostZeroedBE systemQubits (fullSysRawAncWires 80)
        (by dsimp [fullSysRawAncWires]; omega) gridValidBool U_BE) := by
    rw [hSubAct]
    exact isQubitizedBE_ghostZeroedBE (by dsimp [fullSysRawAncWires]; omega)
      hαPos M_act U_BE hUBE_sa hTopRaw
  have hAGridAct : Commute (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits))) G :=
    commute_gridProjector_of_sandwiched hSubAct
  have hEndSm := endpoint_heff_of_target_sum cfg spinUp E (fun k ↦ G * B_sm_id k * G)
    target ε_slot ε_id hTargetSum hSlotsSm hEpsId
  have hSub_sm : Heff_sm_id - (E₀_id : ℂ) • (1 : Operator (2 ^ systemQubits)) =
      G * (∑ k : Fin 6, B_sm_id k) * G := by
    rw [hEndSm.1, Finset.mul_sum, Finset.sum_mul]
  have hUU : U * U = 1 := smToTwosSys_mul_self_val
  have hUG : U * G = G * U := smToTwosSys_comm_gridProjector
  have hUP : U * fermionicProjector spinUp = fermionicProjector spinUp * U :=
    smToTwosSys_comm_fermionicProjector spinUp
  have hSum_conj : U * (∑ k : Fin 6, B_sm_id k) * U = ∑ k : Fin 6, B_twos_id k := by
    dsimp only [B_sm_id]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ ↦
      (show U * (U * B_twos_id k * U) * U = (U * U) * B_twos_id k * (U * U) by
        simp only [Matrix.mul_assoc]).trans (by rw [hUU, one_mul, mul_one])
  have hSubId : Heff_id - (E₀_id : ℂ) • (1 : Operator (2 ^ systemQubits)) = G *
      (∑ k : Fin 6, B_twos_id k) * G := by
    have hshift : Heff_id - (E₀_id : ℂ) • (1 : Operator (2 ^ systemQubits)) = U *
        (Heff_sm_id - (E₀_id : ℂ) • (1 : Operator (2 ^ systemQubits))) * U := by
      dsimp only [Heff_id]
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU]
    rw [hshift, hSub_sm]
    exact (show U * (G * (∑ k : Fin 6, B_sm_id k) * G) * U =
        (U * G) * (∑ k : Fin 6, B_sm_id k) * (G * U) by simp only [Matrix.mul_assoc]).trans
      ((congrArg₂ (· * ·) (congrArg₂ (· * ·) hUG rfl) hUG.symm).trans
        ((show (G * U) * (∑ k : Fin 6, B_sm_id k) * (U * G) =
          G * (U * (∑ k : Fin 6, B_sm_id k) * U) * G by simp only [Matrix.mul_assoc]).trans
          (by rw [hSum_conj])))
  have hIdGrid : Commute Heff_id G := by
    rw [show Heff_id = (Heff_id - (E₀_id : ℂ) • (1 : Operator (2 ^ systemQubits))) + (E₀_id : ℂ) •
      (1 : Operator (2 ^ systemQubits)) from (sub_add_cancel _ _).symm]
    exact (commute_gridProjector_of_sandwiched hSubId).add_left
      (Commute.smul_left (Commute.one_left G) (E₀_id : ℂ))
  have hUnitIdHerm : ∀ k : Fin 6, (B_unit_id k).IsHermitian :=
    forall_fin6_prop
      (by
        simpa only [B_unit_id, fin6Tuple_0] using
        ZeroSubwireGridPert80.momSingleSlotOracle_bUnitTwos_isHermitian s0 cfg)
      (by
        simpa only [B_unit_id, fin6Tuple_1] using
        ZeroSubwireGridPert80.momSingleSlotOracle_bUnitTwos_isHermitian s1 cfg)
      (by simpa only [B_unit_id, fin6Tuple_2] using hb2IdHerm)
      (by
        simpa only [B_unit_id, fin6Tuple_3] using
        ZeroSubwireGridPert80.momSingleSlotOracle_bUnitTwos_isHermitian s3 cfg)
      (by simpa only [B_unit_id, fin6Tuple_4] using hb4IdHerm)
      (by
        simpa only [B_unit_id, fin6Tuple_5] using
        ZeroSubwireGridPert80.momSingleSlotOracle_bUnitTwos_isHermitian s5 cfg)
  have hIdHerm : Heff_id.IsHermitian := by
    have hSumIdHerm : (∑ k : Fin 6, B_twos_id k).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      dsimp only [B_twos_id]
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (hUnitIdHerm k).eq]
    have hGIdGHerm : (G * (∑ k : Fin 6, B_twos_id k) * G).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        gridProjector_isHermitian.eq, hSumIdHerm.eq, Matrix.mul_assoc]
    have hEHerm : ((E₀_id : ℂ) • (1 : Operator (2 ^ systemQubits))).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
    rw [show Heff_id = G * (∑ k : Fin 6, B_twos_id k) * G + (E₀_id : ℂ) • (1 : Operator (2 ^
      systemQubits)) by
      rw [← hSubId, sub_add_cancel]]
    exact hGIdGHerm.add hEHerm
  let Δ_w : Operator (2 ^ systemQubits) :=
    ∑ k : Fin 6, ((wActOfUnitary α_real uCoin k - wTarget k : ℝ) : ℂ) • B_unit_id k
  let Δ_pos : Operator (2 ^ systemQubits) := (wActOfUnitary α_real uCoin 2 : ℂ) •
      (b2Act cfg - b2Id cfg) + (wActOfUnitary α_real uCoin 4 : ℂ) • (b4Act cfg - b4Id cfg)
  let Δ : Operator (2 ^ systemQubits) := Δ_w + Δ_pos
  have hSumDiff : (∑ k : Fin 6, B_twos_act k) - (∑ k : Fin 6, B_twos_id k) = Δ := by
    dsimp only [Δ, Δ_w, Δ_pos, B_twos_act, B_twos_id, B_unit_act, B_unit_id]
    rw [Fin.sum_univ_six, Fin.sum_univ_six, Fin.sum_univ_six]
    simp only [fin6Tuple_0, fin6Tuple_1, fin6Tuple_2, fin6Tuple_3, fin6Tuple_4, fin6Tuple_5]
    exact ZeroSubwireHarmonicGridPert.sixSlot_diff_rearrange
      (wActOfUnitary α_real uCoin 0) (wActOfUnitary α_real uCoin 1)
      (wActOfUnitary α_real uCoin 2) (wActOfUnitary α_real uCoin 3)
      (wActOfUnitary α_real uCoin 4) (wActOfUnitary α_real uCoin 5) (wTarget 0) (wTarget 1)
      (wTarget 2) (wTarget 3) (wTarget 4) (wTarget 5) (s0.bUnitTwos cfg) (s1.bUnitTwos cfg)
      (b2Act cfg) (b2Id cfg) (s3.bUnitTwos cfg) (b4Act cfg) (b4Id cfg) (s5.bUnitTwos cfg)
  have hUnitIdNorm : ∀ k : Fin 6, ‖B_unit_id k‖ ≤ 1 :=
    forall_fin6_prop
      (by simpa only [B_unit_id, fin6Tuple_0] using s0.hUnitNorm cfg)
      (by simpa only [B_unit_id, fin6Tuple_1] using s1.hUnitNorm cfg)
      (by simpa only [B_unit_id, fin6Tuple_2] using hb2IdNorm)
      (by simpa only [B_unit_id, fin6Tuple_3] using s3.hUnitNorm cfg)
      (by simpa only [B_unit_id, fin6Tuple_4] using hb4IdNorm)
      (by simpa only [B_unit_id, fin6Tuple_5] using s5.hUnitNorm cfg)
  have hΔw_norm : ‖Δ_w‖ ≤ err_w :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ ↦ by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hUnitIdNorm k) (abs_nonneg _)).trans_eq (mul_one _)).trans
        hWeightErr)
  have hΔpos_norm : ‖Δ_pos‖ ≤ δ_pos := by
    have hw_nn (k : Fin 6) : 0 ≤ wActOfUnitary α_real uCoin k := wActOfUnitary_nonneg hαPos.le uCoin
      k
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hw_nn 2),
      Real.norm_of_nonneg (hw_nn 4)]
    exact (add_le_add (mul_le_mul_of_nonneg_left hDiff2 (hw_nn 2))
        (mul_le_mul_of_nonneg_left hDiff4 (hw_nn 4))).trans
      ((add_le_add (mul_le_mul_of_nonneg_right (wActOfUnitary_le_wTarget_add_err hWeightErr 2)
        ((norm_nonneg _).trans hDiff2))
        (mul_le_mul_of_nonneg_right (wActOfUnitary_le_wTarget_add_err hWeightErr 4) ((norm_nonneg
          _).trans hDiff4))).trans hPrepCap)
  let δ_prep₀ : ℝ := err_w + δ_pos
  have hδ_prep₀_nn : 0 ≤ δ_prep₀ := add_nonneg herr_w hδ_pos
  have hDiffGrid : ‖G * (Heff_act - Heff_id) * G‖ ≤ δ_prep₀ := by
    have hGn : ‖G‖ ≤ 1 :=
      PosSlots24SemanticOracleConcrete80.norm_le_one_of_isProj G
        gridProjector_isHermitian.eq gridProjector_mul_self
    have hΔn : ‖Δ‖ ≤ δ_prep₀ := (norm_add_le _ _).trans (add_le_add hΔw_norm hΔpos_norm)
    rw [MomSlot1DyadicTopAdapter.heff_shift_diff_eq G (∑ k : Fin 6, B_twos_act k) (∑ k : Fin 6,
      B_twos_id k) Heff_id Δ gridProjector_mul_self E₀_id δ_s hSubId
        hSumDiff]
    exact (norm_triple_mul_le_local G Δ G hGn hΔn hGn zero_le_one ((norm_nonneg _).trans
      hΔn)).trans_eq (by ring)
  have hAgree_twos : AgreesOnFermionicSector spinUp Heff_id (U * hamiltonian cfg * U) ε_id := by
    rcases hEndSm.2 with ⟨hCommP_sm, hNorm_sm⟩
    refine ⟨FullSysPosSlots24AndTopConcrete.conj_comm_local
      U Heff_sm_id (fermionicProjector spinUp) hUP hCommP_sm, ?_⟩
    rw [show Heff_id - U * hamiltonian cfg * U = U * (Heff_sm_id - hamiltonian cfg) * U by
      dsimp only [Heff_id]
      rw [Matrix.mul_sub, Matrix.sub_mul]]
    rw [FullSysPosSlots24AndTopConcrete.conj_middle_swap_local U (Heff_sm_id - hamiltonian cfg)
      (fermionicProjector spinUp) hUP]
    have hUnorm : ‖U‖ ≤ 1 := l2_opNorm_unitary_le_one smToTwosSysUnitary
    exact (norm_triple_mul_le_local U _ U hUnorm hNorm_sm hUnorm zero_le_one
      ((norm_nonneg _).trans hNorm_sm)).trans_eq (by ring)
  refine ⟨E₀, δ_prep₀, ε_id, Heff_act, Heff_id,
    hδ_prep₀_nn, hε_id, hEpsBECap, hAGridAct, hBEAct, hIdHerm, hIdGrid, hDiffGrid, ?_⟩
  rw [smToTwosSysUnitary_conjTranspose]
  exact hAgree_twos
end
end Part2_ArbitraryWeightPertCore
section Part3A_Chiral34To35AndCompressedSingleSlotPert
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority := 1000000) instNeZeroTwoPowChiralSec3A (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open OraAndPrepBundle (fin6Tuple)
open PosSlots24SemanticOracleConcrete80 (pos80Slot2Scale pos80Slot4Scale)
open Pos24MergedVepPrepAndStitch (mergedPosSlot2WeightGen)
open ZeroSubwireCoinPrep80 (wIdealRat)
open ZeroSubwireHarmonicGridPert (forall_fin6_prop mkZeroSubwireWeights80)
open SubvoxelNuclearTrunc34And33Physics (truncWCfg)
open Leaf2Packed18Mux2DCore (truncChiralOfW)
open Tier72bAndScheduleClosure (nonS3ChiralNano)
/-- Chiral subvoxel nuclear configuration truncation maps at `W = 34` and `W = 35`. -/
abbrev trunc34Cfg : Configuration → Configuration := truncWCfg 34
abbrev trunc35Cfg : Configuration → Configuration := truncWCfg 35
/-- Extended chiral truncation map `W ∈ {28..35}` (`W = 34, 35` added for `scheduleK12_10432`). -/
def truncChiralChiralOfW (W : ℕ) : Configuration → Configuration :=
  if W = 34 then trunc34Cfg else if W = 35 then trunc35Cfg else truncChiralOfW W
/-- Extended non-`S3` intrinsic error cap in nano-Hartree (`W = 34 → 196,577`, `W = 35 →
132,243`). -/
def nonS3ChiralChiralNano (W : ℕ) : ℕ :=
  if W = 34 then 196577 else if W = 35 then 132243 else nonS3ChiralNano W
open PosSlots24SemanticOracleConcrete80 (pos80Slot2TotNat pos80Slot4TotNat pos80HeadWeightNat
  pos80TailWeightNat) in
theorem mkZeroSubwireWeights80_eq_of_wSlot3 (s3 : MomSingleSlotOracle 80 48 3) {wTarget : Fin 6 →
    ℝ} (hw0 : wTarget 0 = wIdealRat 0) (hw1 : wTarget 1 = wIdealRat 1) (hw2 : wTarget 2 =
    wIdealRat 2) (hw3 : ∀ cfg,
    s3.wSlot cfg = wTarget 3) (hw4 : wTarget 4 = wIdealRat 4) (hw5 : wTarget 5 =
      0) (cfg : Configuration) : ∀ k : Fin 6, mkZeroSubwireWeights80 s3 cfg k = wTarget k := by
  refine forall_fin6_prop ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hw0]; change (3441613 : ℝ) / 100 = wIdealRat 0; unfold wIdealRat; norm_num
  · rw [hw1]; change (414968 : ℝ) / 1000 = wIdealRat 1; unfold wIdealRat; norm_num
  · rw [hw2]
    dsimp only [mkZeroSubwireWeights80, fin6Tuple]
    unfold mergedPosSlot2WeightGen pos80Slot2Scale pos80Slot2TotNat
      pos80HeadWeightNat pos80TailWeightNat wIdealRat
    norm_num
  · exact hw3 cfg
  · rw [hw4]
    dsimp only [mkZeroSubwireWeights80, fin6Tuple]
    unfold pos80Slot4Scale pos80Slot4TotNat pos80HeadWeightNat pos80TailWeightNat wIdealRat
    norm_num
  · rw [hw5]; rfl
end
end Part3A_Chiral34To35AndCompressedSingleSlotPert
section CleanChiralBMasterStitch
attribute [local reducible] InterWalkRSum42Hoist.kActOrig
local instance (priority := 1000000) instNeZeroTwoPowChiralB (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
section ChiralBBody
attribute [local irreducible]
  SpecsAux.SpecMirror.gridStates
  SpecsAux.SpecMirror.fermionicProjector
  SpecsAux.SpecMirror.hamiltonian
  SpecsAux.ApproximatesTimeEvolution
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror SpecsAux.PhaseGradCatalystCore SpecsAux.BridgeDuhamel
open SpecsAux.FullScaleBESector hiding phaseGradientState
open PhaseGradSignalRot hiding IntertwinesCat
open TFreeLaurentGQSP CatalyzedLaurentGQSP BidirectionalCatalyzedGQSP
  BidirectionalCatalyzedGQSPBridge
open PosMomSelectSandwich (slotBitProj)
open TwosCompAndWire0Cancel (smToTwosSysUnitary)
open SixSlotEndpointJunctionBridge (gridValidBool)
open SingleRBEGridGuardWalk FullSysCatSegmentBridge BiGqspSegmentSpine
open PolymorphicTopClosure GeneralBetaAndAlphaTopEndpoint
open SingleCatClosure
open GidneySignalRotPart1
open HarmonicTwoAngleBridge hiding gidneyTwoAngleRotToffEquiv biPrefixTwoAngleRotToffSum
  biPrefixTwoAngleRotToffSum_eq_univ_sum uSignalRotTwoAngle43 uSignalRotTwoAngleSingleCat
open HoistBorrow42TwoAngleBridge (gidneyTwoAngleRotToffEquiv)
open InterWalkRSum42Hoist (qreg_ext kFull80 rAct0 rPG48Orig rPG48Full FixesLow3924 h3924_be
  embedUnitary_inv_symm pSum42Zero embedAct0_comm_pSum42Zero)
open NuclearTwistAndXor654Concrete (dyn_seq_toff_zero)
open NuclearTwistMulKickAndBridge288 (count_dyn_seq)
open HoistBorrow42ProjBridge (RealizesOnProj embedIntertwine)
open Leaf4Ext48TopStitch (RealizesClean CommutesWithReg comm_op_mul disj_of_val_ne
  singleton_disj_of_ne sequence_ofFn_extract_single comm_block0_proj_of_comm_singletons
  rCatTotInSingleCat80_eq_rPG48Orig rPG48Full_val_eq rUnusedCtrl3Full_val_eq rSlack3Full_val_eq
  rPGIdle pPGIdleZeroOrig pPGIdleZero pCtrl3Zero pSlack3Zero pExt6IdleZero pExt6IdleZero_eq_mul
  pExt6Zero_eq_mul pZeroInitExt pZeroInitExt_eq_mul pZeroExtOn cHadIdle48 cHadIdleOrig uHadIdleOrig
  uHadIdleFull cHadIdleDyn cHadIdleInvDyn count_t_cHadIdleDyn count_t_cHadIdleInvDyn
  uStreamInit_inv_mul_E_segExt h3954_be FixesCtrl3 E_segExt pHoistExtOn rPGIdleOrig
  Stream42ExtInitSpec HoistedExtHkSelectSpec qSig_single_comm_E_segExt)
open GqspCatPrepSub600Nano (catPrepWordUltra catPrepWordUltra_of_ge31 cCatPrepUltra1qGen
  cInitUltraSingleCat cInitUltraSingleCat_T vPrepUltraSingleCat vInvUltraSingleCat
  mkInitUltraSingleCatDyn mkUninitUltraSingleCatDyn count_toff_mkInitUltraSingleCatDyn
  count_toff_mkUninitUltraSingleCatDyn count_t_mkInitUltraSingleCat_add_uninit_le
  realizesCleanWorkspace_mkInitUltraSingleCatDyn realizesCleanWorkspace_mkUninitUltraSingleCatDyn)
/-- Setting `c = 0` in `gidneyTwoAngleRotToffEquiv c d` collapses with zero overhead to
`2 * (activeMsbWidth42 d - 2) = gidneyRotToffEquiv d`. -/
theorem gidneyTwoAngleRotToffEquiv_zero_left (d : ℕ) : gidneyTwoAngleRotToffEquiv 0 d =
    gidneyRotToffEquiv d := by
  have h0 : activeMsbWidth42 0 = 0 := (activeMsbWidth42_eq_zero_iff (by decide : 0 < 2 ^ 42)).mpr
    rfl
  unfold gidneyTwoAngleRotToffEquiv gidneyRotToffEquiv
  rw [h0]
  omega
theorem sum_gidneyTwoAngleRotToffEquiv_zero_left {M : ℕ} (D : Fin (M + 1) → Fin (2 ^ 42)) : (∑ t :
    Fin (M + 1), gidneyTwoAngleRotToffEquiv ((0 : Fin (2 ^ 42))).val (D t).val) = ∑ t : Fin (M + 1),
    gidneyRotToffEquiv (D t).val := by
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  exact gidneyTwoAngleRotToffEquiv_zero_left (D t).val
/-- Pre-segment 0-`T` Clifford wrapper `H ;; S ;; Z ;; H` on wire `q`, evaluating to `H * (Z * S) *
H`. -/
def cPreOneAngle {n : ℕ} (q : Wire n) : Circuit n :=
  (((Circuit.H q).seq (Circuit.S q)).seq (Circuit.Z q)).seq (Circuit.H q)
/-- Post-segment 0-`T` Clifford wrapper `H ;; S ;; H` on wire `q`, evaluating to `H * S * H`. -/
def cPostOneAngle {n : ℕ} (q : Wire n) : Circuit n :=
  ((Circuit.H q).seq (Circuit.S q)).seq (Circuit.H q)
open PrimitiveGate (TOFF T)
theorem cPreOneAngle_counts {n : ℕ} (q : Wire n) : (cPreOneAngle q).count TOFF = 0 ∧ (cPreOneAngle
    q).count T = 0 := by
  simp [cPreOneAngle, Circuit.count_seq, Circuit.H, Circuit.S, Circuit.Z, Circuit.single]
theorem cPostOneAngle_counts {n : ℕ} (q : Wire n) : (cPostOneAngle q).count TOFF = 0 ∧
    (cPostOneAngle q).count T = 0 := by
  simp [cPostOneAngle, Circuit.count_seq, Circuit.H, Circuit.S, Circuit.single]
theorem twoPhaseDiagMatrix_42_zero : twoPhaseDiagMatrix 42 0 (2 ^ 42 - 0) = 1 := by
  rw [twoPhaseDiagMatrix_sym 42 0 (by decide), Nat.cast_zero, mul_zero, zero_div,
    rzDiagMatrix_eq_cos_add_sin_iZ]
  simp
/-- Conjugating `twoAngleDiagHMatrix 0 d = H * D_42(d) * H` by `S` on the left and `Z * S = S⁻¹` on
the right produces the exact 1-angle `ryMatrix (catCS42 d).1 (catCS42 d).2`. -/
theorem s_mul_twoAngleDiagHMatrix_zero_mul_zs (d : Fin (2 ^ 42)) : Qubit.S.1 * (twoAngleDiagHMatrix
    0 d * (Qubit.Z.1 * Qubit.S.1)) = TFreeLaurentGQSP.ryMatrix (catCS42 d).1 (catCS42 d).2 := by
  have h0 : twoPhaseDiagMatrix 42 ((0 : Fin (2 ^ 42))).val (2 ^ 42 - ((0 : Fin (2 ^ 42))).val) =
    1 :=
    twoPhaseDiagMatrix_42_zero
  change Qubit.S.1 * ((Qubit.H.1 * (twoPhaseDiagMatrix 42 d.val (2 ^ 42 - d.val) * (Qubit.H.1
    * twoPhaseDiagMatrix 42 ((0 : Fin (2 ^ 42))).val (2 ^ 42 - ((0 : Fin (2 ^ 42))).val)))) *
    (Qubit.Z.1 * Qubit.S.1)) = _
  rw [h0, Matrix.mul_one]
  calc Qubit.S.1 * ((Qubit.H.1 * (twoPhaseDiagMatrix 42 d.val (2 ^ 42 - d.val) * Qubit.H.1)) *
          (Qubit.Z.1 * Qubit.S.1))
    _ = (Qubit.S.1 * Qubit.H.1) *
          (twoPhaseDiagMatrix 42 d.val (2 ^ 42 - d.val) * (Qubit.H.1 * (Qubit.Z.1 * Qubit.S.1))) :=
            by
          simp only [Matrix.mul_assoc]
    _ = (ryUnitary (catAngle42 d)).1 := by
          rw [← Matrix.mul_assoc, twoPhaseDiagMatrix_sym 42 d.val d.isLt.le, sH_conj_rzDiagMatrix]
          congr 2
          unfold catAngle42
          ring
    _ = TFreeLaurentGQSP.ryMatrix (catCS42 d).1 (catCS42 d).2 := ryUnitary_catAngle42_val d
theorem eval_S_eq_proj_chiralB {N : ℕ} (qSig : Wire N) : (Circuit.S qSig).eval.1 = (1 : Operator (2
    ^ N)) * (QRegister.singleton qSig).basisOutcomeProjector 0 + (Complex.I • (1 : Operator (2 ^
    N))) *
    (QRegister.singleton qSig).basisOutcomeProjector 1 := by
  apply matrix_ext_ket; intro β
  have hS : (Circuit.S qSig).eval.1 = (QRegister.singleton qSig).embedMatrix Qubit.S.1 := by
    rw [Circuit.S, Circuit.eval_single, QRegister.embedUnitary_val]; rfl
  rw [hS, singleton_embedMatrix_mulVec_ket, Matrix.add_mulVec, one_mul, smul_mul_assoc, one_mul,
    Matrix.smul_mulVec, singleton_proj_zero_mulVec_ket, singleton_proj_one_mulVec_ket]
  rcases bit_cases (β qSig) with hq | hq
  · have hup : Function.update β qSig 0 = β := Function.update_eq_self_iff.mpr hq.symm
    simp [hq, hup, Qubit.S]
  · have hup : Function.update β qSig 1 = β := Function.update_eq_self_iff.mpr hq.symm
    simp [hq, hup, Qubit.S]
theorem s_conj_sig_block_diag {N : ℕ} (qSig : Wire N) (A B : Operator (2 ^ N)) (hA0 : A *
    (QRegister.singleton qSig).basisOutcomeProjector 0 = (QRegister.singleton
    qSig).basisOutcomeProjector 0 * A) (hB0 : B *
    (QRegister.singleton qSig).basisOutcomeProjector 0 = (QRegister.singleton
      qSig).basisOutcomeProjector 0 * B) (hA1 : A * (QRegister.singleton qSig).basisOutcomeProjector
      1 = (QRegister.singleton
    qSig).basisOutcomeProjector 1 * A) (hB1 : B * (QRegister.singleton qSig).basisOutcomeProjector
      1 = (QRegister.singleton qSig).basisOutcomeProjector 1 * B) : (Circuit.S qSig).eval.1 * ((A *
    (QRegister.singleton qSig).basisOutcomeProjector 0 + B * (QRegister.singleton
      qSig).basisOutcomeProjector 1) * ((Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1)) = A *
      (QRegister.singleton
    qSig).basisOutcomeProjector 0 + B * (QRegister.singleton qSig).basisOutcomeProjector 1 := by
  set P0 := (QRegister.singleton qSig).basisOutcomeProjector 0
  set P1 := (QRegister.singleton qSig).basisOutcomeProjector 1
  have hSZ : (Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1 =
      (1 : Operator (2 ^ N)) * P0 + ((-Complex.I) • (1 : Operator (2 ^ N))) * P1 := by
    rw [← Submonoid.coe_mul, ← Circuit.eval_seq, eval_SZ_eq_proj]
  rw [hSZ, eval_S_eq_proj_chiralB qSig,
    sig_block_diag_mul qSig A B 1 ((-Complex.I) • 1) (by simp) (by simp) (by simp) (by simp),
    mul_one]
  have hBneg0 : (B * ((-Complex.I) • 1)) * P0 = P0 * (B * ((-Complex.I) • 1)) := by
    rw [mul_smul_comm, mul_one, smul_mul_assoc, hB0, mul_smul_comm]
  have hBneg1 : (B * ((-Complex.I) • 1)) * P1 = P1 * (B * ((-Complex.I) • 1)) := by
    rw [mul_smul_comm, mul_one, smul_mul_assoc, hB1, mul_smul_comm]
  rw [sig_block_diag_mul qSig 1 (Complex.I • 1) A (B * ((-Complex.I) • 1)) hA0 hA1 hBneg0 hBneg1,
    one_mul]
  refine congrArg (HMul.hMul A P0 + ·) ?_
  rw [mul_smul_comm, mul_one, smul_mul_assoc, one_mul, smul_smul]
  have hII : Complex.I * (-Complex.I) = 1 := by simp [Complex.I_mul_I]
  rw [hII, one_smul]
theorem s_conj_biGqspTwoAngleLoopOp_zero_left {N : ℕ} (qSig : Wire N)
    (W_emb W_inv_emb : Operator (2 ^ N))
    (hW0 : W_emb * (QRegister.singleton qSig).basisOutcomeProjector 0 =
      (QRegister.singleton qSig).basisOutcomeProjector 0 * W_emb)
    (hW1 : W_emb * (QRegister.singleton qSig).basisOutcomeProjector 1 =
      (QRegister.singleton qSig).basisOutcomeProjector 1 * W_emb)
    (hWinv0 : W_inv_emb * (QRegister.singleton qSig).basisOutcomeProjector 0 =
      (QRegister.singleton qSig).basisOutcomeProjector 0 * W_inv_emb)
    (hWinv1 : W_inv_emb * (QRegister.singleton qSig).basisOutcomeProjector 1 =
      (QRegister.singleton qSig).basisOutcomeProjector 1 * W_inv_emb)
    (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42)) :
    ∀ t : ℕ, (Circuit.S qSig).eval.1 * (biGqspTwoAngleLoopOp qSig W_emb W_inv_emb M (fun _ ↦
      0) D t *
      ((Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1)) = biGqspLoopOp qSig W_emb W_inv_emb (biCS
        M D) t := by
  have hS : (Circuit.S qSig).eval.1 = (QRegister.singleton qSig).embedMatrix Qubit.S.1 := by
    rw [Circuit.S, Circuit.eval_single, QRegister.embedUnitary_val]
    rfl
  have hZ : (Circuit.Z qSig).eval.1 = (QRegister.singleton qSig).embedMatrix Qubit.Z.1 := by
    rw [Circuit.Z, Circuit.eval_single, QRegister.embedUnitary_val]
    rfl
  have hCode0 (k : ℕ) : biCode M (fun _ : Fin (M + 1) ↦ (0 : Fin (2 ^ 42))) k = 0 := by
    unfold biCode
    split_ifs <;> rfl
  have hRot (k : ℕ) : (Circuit.S qSig).eval.1 * ((QRegister.singleton qSig).embedMatrix
      (twoAngleDiagHMatrix 0 (biCode M D k)) * ((Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1))
        =
      (QRegister.singleton qSig).embedMatrix (TFreeLaurentGQSP.ryMatrix (biCS M D k).1 (biCS M D
        k).2) := by
    dsimp only [biCS]
    rw [hS, hZ, ← (QRegister.singleton qSig).embedMatrix_mul, ← (QRegister.singleton
      qSig).embedMatrix_mul, ← (QRegister.singleton qSig).embedMatrix_mul,
      s_mul_twoAngleDiagHMatrix_zero_mul_zs]
  intro t
  induction t with
  | zero =>
      dsimp only [biGqspTwoAngleLoopOp, biGqspGenLoopOp, biTwoAngleGate, biGqspLoopOp]
      rw [hCode0 0]
      exact hRot 0
  | succ t ih =>
      have hZS_S : ((Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1) * (Circuit.S qSig).eval.1 =
        1 := by
        rw [hZ, hS, ← (QRegister.singleton qSig).embedMatrix_mul, ← (QRegister.singleton
          qSig).embedMatrix_mul,
          show (Qubit.Z.1 * Qubit.S.1) * Qubit.S.1 = 1 by
            change ((Qubit.Z * Qubit.S) * Qubit.S).1 = (1 : Unitary 2).1
            rw [Qubit.Z_mul_S_eq_S_inv, inv_mul_cancel],
          QRegister.embedMatrix_one]
      have hWalk : (Circuit.S qSig).eval.1 * (biWalkStepOp qSig W_emb W_inv_emb *
          ((Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1)) = biWalkStepOp qSig W_emb
            W_inv_emb := by
        have hEqW : biWalkStepOp qSig W_emb W_inv_emb =
            W_emb * (QRegister.singleton qSig).basisOutcomeProjector 0 +
              W_inv_emb * (QRegister.singleton qSig).basisOutcomeProjector 1 := by
          rw [biWalkStepOp_eq_mul_c0_c1 qSig W_emb W_inv_emb hWinv0 hWinv1,
            show W_emb * (QRegister.singleton qSig).basisOutcomeProjector 0 +
                (QRegister.singleton qSig).basisOutcomeProjector 1 =
              W_emb * (QRegister.singleton qSig).basisOutcomeProjector 0 +
                1 * (QRegister.singleton qSig).basisOutcomeProjector 1 by rw [one_mul],
            show (QRegister.singleton qSig).basisOutcomeProjector 0 +
                W_inv_emb * (QRegister.singleton qSig).basisOutcomeProjector 1 =
              1 * (QRegister.singleton qSig).basisOutcomeProjector 0 +
                W_inv_emb * (QRegister.singleton qSig).basisOutcomeProjector 1 by rw [one_mul],
            sig_block_diag_mul qSig W_emb 1 1 W_inv_emb (by simp) (by simp) hWinv0 hWinv1, mul_one,
              one_mul]
        rw [hEqW]
        exact s_conj_sig_block_diag qSig W_emb W_inv_emb hW0 hWinv0 hW1 hWinv1
      dsimp only [biGqspTwoAngleLoopOp, biGqspGenLoopOp, biTwoAngleGate, biGqspLoopOp] at ih ⊢
      rw [hCode0 (t + 1)]
      set R_t := (QRegister.singleton qSig).embedMatrix (twoAngleDiagHMatrix 0 (biCode M D (t + 1)))
      set W_op := biWalkStepOp qSig W_emb W_inv_emb
      set L_t := biGqspGenLoopOp qSig W_emb W_inv_emb (biTwoAngleGate M (fun _ ↦ 0) D) t
      set S_op := (Circuit.S qSig).eval.1
      set ZS_op := (Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1
      calc S_op * (((R_t * W_op) * L_t) * ZS_op)
        _ = (S_op * (R_t * ZS_op)) * (S_op * (W_op * ZS_op)) * (S_op * (L_t * ZS_op)) := by
              have h1 : S_op * (((R_t * W_op) * L_t) * ZS_op) =
                  (S_op * R_t * (ZS_op * S_op)) * W_op * (ZS_op * S_op) * L_t * ZS_op := by
                rw [hZS_S, Matrix.mul_one, Matrix.mul_one]
                simp only [Matrix.mul_assoc]
              rw [h1]
              simp only [Matrix.mul_assoc]
        _ = ((QRegister.singleton qSig).embedMatrix
              (TFreeLaurentGQSP.ryMatrix (biCS M D (t + 1)).1 (biCS M D (t + 1)).2) * W_op) *
            biGqspLoopOp qSig W_emb W_inv_emb (biCS M D) t := by rw [hRot (t + 1), hWalk, ih]
/-- Wrapping `physBiTwoAngleSegmentUnitaryGen b M (fun _ ↦ 0) D U_raw` with `cPreOneAngle` before
and
`cPostOneAngle` after on `qSig` yields the exact 1-angle `physBiSegmentUnitaryGen b M D U_raw`. -/
theorem cPost_mul_physBiTwoAngleSegment_zero_mul_cPre
    {k m : ℕ} (b : Fin (2 ^ k) → Bool) (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42))
    (U_raw : Unitary (2 ^ (k + m))) :
    let qSig : Wire (k + (m + 1)) := ⟨k + m, by omega⟩
    (cPostOneAngle qSig).eval *
      (physBiTwoAngleSegmentUnitaryGen b M (fun _ ↦ 0) D U_raw * (cPreOneAngle qSig).eval) =
      physBiSegmentUnitaryGen b M D U_raw := by
  intro qSig
  apply Subtype.ext
  let rBE : QRegister (k + m) (k + (m + 1)) := QRegister.block 0 (k + m) (by omega)
  let W_emb := rBE.embedMatrix (physLaurentWalkGen b U_raw)
  let W_inv_emb := rBE.embedMatrix (physLaurentWalkInvGen b U_raw)
  have hDisj : rBE.DisjointWires (QRegister.singleton qSig) := by
    rw [QRegister.disjoint_iff]; intro i j h; fin_cases j
    have hv := congrArg Fin.val h; simp [rBE, qSig, QRegister.singleton] at hv; omega
  have hW0 := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rBE) _ hDisj
    (physLaurentWalkGen b U_raw) 0
  have hW1 := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rBE) _ hDisj
    (physLaurentWalkGen b U_raw) 1
  have hWinv0 := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rBE) _ hDisj
    (physLaurentWalkInvGen b U_raw) 0
  have hWinv1 := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rBE) _ hDisj
    (physLaurentWalkInvGen b U_raw) 1
  have hHH : (Circuit.H qSig).eval.1 * (Circuit.H qSig).eval.1 = 1 := by
    rw [← Submonoid.coe_mul, Circuit.H, Circuit.eval_single, ← QRegister.embedUnitary_mul,
      show PrimitiveGate.H.eval = Qubit.H from rfl, Qubit.H_sq, QRegister.embedUnitary_one,
      OneMemClass.coe_one]
  have hZS_S : ((Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1) * (Circuit.S qSig).eval.1 = 1 :=
    by
    rw [Circuit.Z, Circuit.S, Circuit.eval_single, Circuit.eval_single, ← Submonoid.coe_mul,
      ← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul,
      show PrimitiveGate.Z.eval = Qubit.Z
        from rfl, show PrimitiveGate.S.eval = Qubit.S from rfl, Qubit.Z_mul_S_eq_S_inv,
          inv_mul_cancel, QRegister.embedUnitary_one, OneMemClass.coe_one]
  have hPostH : (cPostOneAngle qSig).eval.1 * (Circuit.H qSig).eval.1 =
      (Circuit.H qSig).eval.1 * (Circuit.S qSig).eval.1 := by
    unfold cPostOneAngle
    simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, hHH, Matrix.mul_one]
  have hHPre : (Circuit.H qSig).eval.1 * (cPreOneAngle qSig).eval.1 =
      ((Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1) * (Circuit.H qSig).eval.1 := by
    unfold cPreOneAngle
    simp only [Circuit.eval_seq, Submonoid.coe_mul]
    calc (Circuit.H qSig).eval.1 *
          ((Circuit.H qSig).eval.1 * ((Circuit.Z qSig).eval.1 * ((Circuit.S qSig).eval.1 *
            (Circuit.H qSig).eval.1)))
      _ = ((Circuit.H qSig).eval.1 * (Circuit.H qSig).eval.1) *
            (((Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1) * (Circuit.H qSig).eval.1) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hHH, Matrix.one_mul]
  set P0 := (QRegister.singleton qSig).basisOutcomeProjector 0
  set P1 := (QRegister.singleton qSig).basisOutcomeProjector 1
  have hC0 : (Circuit.S qSig).eval.1 * ((W_inv_emb * P0 + P1) * ((Circuit.Z qSig).eval.1 *
      (Circuit.S qSig).eval.1)) = W_inv_emb * P0 + P1 := by
    simpa only [one_mul] using
      s_conj_sig_block_diag qSig W_inv_emb 1 hWinv0 (by simp) hWinv1 (by simp)
  have hC1 : (Circuit.S qSig).eval.1 * ((P0 + W_emb * P1) * ((Circuit.Z qSig).eval.1 *
      (Circuit.S qSig).eval.1)) = P0 + W_emb * P1 := by
    simpa only [one_mul] using
      s_conj_sig_block_diag qSig 1 W_emb (by simp) hW0 (by simp) hW1
  have hLoop := s_conj_biGqspTwoAngleLoopOp_zero_left qSig W_emb W_inv_emb hW0 hW1 hWinv0 hWinv1 M D
    M
  change (cPostOneAngle qSig).eval.1 * (biGqspGenSegmentOp qSig W_emb W_inv_emb
    (biTwoAngleGate M (fun _ ↦ 0) D) M * (cPreOneAngle qSig).eval.1) = biGqspSegmentOp qSig
    W_emb W_inv_emb (biCS M D) M
  unfold biGqspGenSegmentOp biGqspSegmentOp
  set H_op := (Circuit.H qSig).eval.1
  set S_op := (Circuit.S qSig).eval.1
  set ZS_op := (Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1
  set C0_op := W_inv_emb * P0 + P1
  set L2_op := biGqspGenLoopOp qSig W_emb W_inv_emb (biTwoAngleGate M (fun _ ↦ 0) D) M
  set C1_op := P0 + W_emb * P1
  calc (cPostOneAngle qSig).eval.1 *
        ((((H_op * C0_op) * L2_op) * C1_op * H_op) * (cPreOneAngle qSig).eval.1)
    _ = ((cPostOneAngle qSig).eval.1 * H_op) * C0_op * L2_op * C1_op *
          (H_op * (cPreOneAngle qSig).eval.1) := by
          simp only [Matrix.mul_assoc]
    _ = H_op * S_op * C0_op * (ZS_op * S_op) * L2_op * (ZS_op * S_op) * C1_op * (ZS_op * H_op) := by
          rw [hPostH, hHPre, hZS_S, Matrix.mul_one, Matrix.mul_one]
    _ = H_op * (S_op * (C0_op * ZS_op)) * (S_op * (L2_op * ZS_op)) * (S_op * (C1_op * ZS_op)) *
      H_op := by
          simp only [Matrix.mul_assoc]
    _ = (((H_op * C0_op) * biGqspLoopOp qSig W_emb W_inv_emb (biCS M D) M) * C1_op) * H_op := by
          rw [hC0, hC1]
          dsimp only [biGqspTwoAngleLoopOp] at hLoop
          rw [hLoop]
theorem cPreOneAngle_comm_E_segExt (k_idle : ℕ) (hk : k_idle ≤ 48) : (rAct0.embedUnitary
    (cPreOneAngle (qSigInSingleCat 80 48 40)).eval).1 * E_segExt k_idle hk = E_segExt k_idle hk *
    (rAct0.embedUnitary
    (cPreOneAngle (qSigInSingleCat 80 48 40)).eval).1 := by
  unfold cPreOneAngle Circuit.H Circuit.S Circuit.Z
  simp only [Circuit.eval_seq, QRegister.embedUnitary_mul, Submonoid.coe_mul]
  exact comm_op_mul (qSig_single_comm_E_segExt k_idle hk .H) (comm_op_mul
    (qSig_single_comm_E_segExt k_idle hk .Z) (comm_op_mul (qSig_single_comm_E_segExt k_idle hk
    .S) (qSig_single_comm_E_segExt k_idle hk .H)))
theorem cPostOneAngle_comm_E_segExt (k_idle : ℕ) (hk : k_idle ≤ 48) : (rAct0.embedUnitary
    (cPostOneAngle (qSigInSingleCat 80 48 40)).eval).1 * E_segExt k_idle hk = E_segExt k_idle hk *
    (rAct0.embedUnitary
    (cPostOneAngle (qSigInSingleCat 80 48 40)).eval).1 := by
  unfold cPostOneAngle Circuit.H Circuit.S
  simp only [Circuit.eval_seq, QRegister.embedUnitary_mul, Submonoid.coe_mul]
  exact comm_op_mul (qSig_single_comm_E_segExt k_idle hk .H) (comm_op_mul
    (qSig_single_comm_E_segExt k_idle hk .S) (qSig_single_comm_E_segExt k_idle hk .H))
theorem commutesWithReg_single_catPrepUltra_seq_cHadIdle48 (k_idle : ℕ) (hk : k_idle ≤ 48) (hk17 :
    k_idle ≤ 17) (q : Fin k_idle) : CommutesWithReg (QRegister.singleton ⟨q.val,
    by omega⟩) ((cCatPrepUltra1qGen
    48).seq (cHadIdle48 k_idle hk)).eval.1 := by
  let w : Wire 48 := ⟨q.val, by omega⟩
  let H₀ : Operator 2 := (PrimitiveGate.eval PrimitiveGate.H).1
  have hPrep : ∃ M₁ : Operator (2 ^ 48), CommutesWithReg (QRegister.singleton w) M₁ ∧
      (cCatPrepUltra1qGen 48).eval.1 = (QRegister.singleton w).embedMatrix H₀ * M₁ := by
    let f : Fin 48 → Circuit 48 := fun i ↦
      ZeroAncillaUSP.hstWordCircuit (catPrepWordUltra i.val) i.rev
    obtain ⟨M₁, hM₁, _, hL⟩ := sequence_ofFn_extract_single w H₀ f w.rev
      (fun j hj ↦ by
        rw [ZeroAncillaUSP.hstWordCircuit_eval_eq_embedMatrix]
        exact CommutesWithReg.of_disjoint (singleton_disj_of_ne fun h ↦
          hj (by simpa [Fin.rev_rev] using congrArg Fin.rev h)) _)
      (by
        have hw31 : 31 ≤ (w.rev).val := by
          have hq := q.isLt; simp only [Fin.val_rev, w]; omega
        dsimp only [f]
        rw [catPrepWordUltra_of_ge31 hw31, Fin.rev_rev]
        change (Circuit.seq (Circuit.H w) .identity).eval.1 = _
        rw [Circuit.eval_seq, Circuit.eval_identity, Submonoid.coe_mul, OneMemClass.coe_one,
          one_mul, Circuit.H, Circuit.eval_single, QRegister.embedUnitary_val])
    exact ⟨M₁, hM₁, hL⟩
  have hHad : ∃ M₂ : Operator (2 ^ 48), CommutesWithReg (QRegister.singleton w) M₂ ∧
      (cHadIdle48 k_idle hk).eval.1 = M₂ * (QRegister.singleton w).embedMatrix H₀ := by
    let g : Fin k_idle → Circuit 48 := fun q' ↦ Circuit.H ⟨q'.val, by omega⟩
    obtain ⟨M₂, hM₂, hR, _⟩ := sequence_ofFn_extract_single w H₀ g q
      (fun j hj ↦ by
        dsimp only [g]
        rw [Circuit.H, Circuit.eval_single, QRegister.embedUnitary_val]
        exact CommutesWithReg.of_disjoint
          (singleton_disj_of_ne (n := 48) (w₁ := ⟨j.val, by omega⟩) (w₂ := w)
            fun h : (⟨j.val, _⟩ : Wire 48) = w ↦
              hj (Fin.ext (show j.val = q.val from congrArg (Fin.val (n := 48)) h))) _)
      (by dsimp only [g]; rw [Circuit.H, Circuit.eval_single, QRegister.embedUnitary_val])
    exact ⟨M₂, hM₂, hR⟩
  obtain ⟨M₁, hM₁, e₁⟩ := hPrep
  obtain ⟨M₂, hM₂, e₂⟩ := hHad
  have hHsq : (QRegister.singleton w).embedMatrix H₀ *
      (QRegister.singleton w).embedMatrix H₀ = 1 := by
    have heq : (QRegister.singleton w).embedMatrix H₀ = (Circuit.H w).eval.1 := by
      rw [Circuit.H, Circuit.eval_single, QRegister.embedUnitary_val]
    rw [heq, eval_H_mul_self]
  rw [Circuit.eval_seq, Submonoid.coe_mul, e₂, e₁, Matrix.mul_assoc, ← Matrix.mul_assoc
    ((QRegister.singleton w).embedMatrix H₀), hHsq, one_mul]
  exact hM₂.mul hM₁
theorem uHadIdleOrig_mul_vPrepUltraSingleCat_eval_eq (k_idle : ℕ) (hk : k_idle ≤ 48) : (uHadIdleOrig
    k_idle hk * vPrepUltraSingleCat 80 48 40).1 = rPG48Orig.embedMatrix ((cCatPrepUltra1qGen 48).seq
    (cHadIdle48
    k_idle hk)).eval.1 := by
  unfold uHadIdleOrig cHadIdleOrig vPrepUltraSingleCat cInitUltraSingleCat
  rw [rCatTotInSingleCat80_eq_rPG48Orig, Submonoid.coe_mul, ← Submonoid.coe_mul, ← Circuit.eval_seq,
    ← Circuit.onRegister_seq, Circuit.eval_onRegister, QRegister.embedUnitary_val]
theorem uHadIdleOrig_mul_vPrepUltraSingleCat_comm_pPGIdleZeroOrig (k_idle : ℕ) (hk : k_idle ≤ 48)
    (hk17 : k_idle ≤ 17) : (uHadIdleOrig k_idle hk * vPrepUltraSingleCat 80 48 40).1 *
    pPGIdleZeroOrig k_idle hk =
    pPGIdleZeroOrig k_idle hk * (uHadIdleOrig k_idle hk * vPrepUltraSingleCat 80 48 40).1 := by
  have hSlice : rPGIdleOrig k_idle hk =
      rPG48Orig.compose (QRegister.block 0 k_idle (fullSys_zero_add_le_of_le hk)) := by
    apply qreg_ext; intro i; ext; simp [rPGIdleOrig]
  have hProj : pPGIdleZeroOrig k_idle hk = rPG48Orig.embedMatrix ((QRegister.block 0 k_idle
      (fullSys_zero_add_le_of_le hk)).basisOutcomeProjector 0) := by
    unfold pPGIdleZeroOrig
    rw [hSlice, QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
      ← QRegister.basisOutcomeProjector]
  rw [hProj, uHadIdleOrig_mul_vPrepUltraSingleCat_eval_eq k_idle hk, ← QRegister.embedMatrix_mul,
    ← QRegister.embedMatrix_mul]
  exact congrArg rPG48Orig.embedMatrix (comm_block0_proj_of_comm_singletons _ k_idle hk
    (commutesWithReg_single_catPrepUltra_seq_cHadIdle48 k_idle hk hk17))
/-- Hoisted ultra catalyst + `H^{⊗ k_idle}` + stream forward preparation unitary on `kFull80`. -/
noncomputable def vPrepUltraExtHk (k_idle : ℕ) (hk : k_idle ≤ 48)
    (uStream : Unitary (2 ^ kFull80)) : Unitary (2 ^ kFull80) :=
  uStream * (uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40))
/-- Hoisted ultra catalyst + `H^{⊗ k_idle}` + stream inverse teardown unitary on `kFull80`. -/
noncomputable def vInvUltraExtHk (k_idle : ℕ) (hk : k_idle ≤ 48)
    (uStream : Unitary (2 ^ kFull80)) : Unitary (2 ^ kFull80) :=
  (rAct0.embedUnitary (vInvUltraSingleCat 80 48 40) * (uHadIdleFull k_idle hk)⁻¹) * uStream⁻¹
/-- Dynamic hoisted ultra catalyst + `cHadIdleDyn` + stream setup circuit (`28 ≤ mWork`). -/
noncomputable def mkInitUltraExtHkDyn {Var : Type} {mWork k_idle tStreamPair n : ℕ}
    (hk : k_idle ≤ 48) (hm28 : 28 ≤ mWork)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n := .seq (.seq
    (mkInitUltraSingleCatDyn hm28 v (rAct.compose rAct0) rWork (hDisj.compose_left
    rAct0)) (cHadIdleDyn k_idle hk (Nat.le_trans (by decide : 1 ≤ 28) hm28) v (rAct.compose
    rAct0) rWork)) (initSpec.dStreamInit v rAct rWork hDisj)
/-- Dynamic hoisted stream teardown + `cHadIdleInvDyn` + ultra catalyst teardown circuit (`28 ≤
mWork`). -/
noncomputable def mkUninitUltraExtHkDyn {Var : Type} {mWork k_idle tStreamPair n : ℕ}
    (hk : k_idle ≤ 48) (hm28 : 28 ≤ mWork)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n := .seq
    (initSpec.dStreamUninit v rAct rWork hDisj) (.seq (cHadIdleInvDyn k_idle hk (Nat.le_trans
    (by decide : 1 ≤ 28) hm28) v (rAct.compose rAct0) rWork) (mkUninitUltraSingleCatDyn
    hm28 v (rAct.compose rAct0) rWork (hDisj.compose_left rAct0)))
theorem count_toff_mkInitUltraExtHkDyn {Var : Type} {mWork k_idle tStreamPair n : ℕ}
    (hk : k_idle ≤ 48) (hm28 : 28 ≤ mWork)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    (mkInitUltraExtHkDyn hk hm28 initSpec v rAct rWork hDisj).count TOFF = 0 :=
    dyn_seq_toff_zero (dyn_seq_toff_zero (count_toff_mkInitUltraSingleCatDyn hm28 v _
    rWork _) (substActiveSingleCat_count_TOFF _ v _ rWork _))
    (initSpec.hToffInit v rAct rWork hDisj)
theorem count_toff_mkUninitUltraExtHkDyn {Var : Type} {mWork k_idle tStreamPair n : ℕ}
    (hk : k_idle ≤ 48) (hm28 : 28 ≤ mWork)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : (mkUninitUltraExtHkDyn hk hm28 initSpec v rAct
    rWork hDisj).count TOFF = 0 := dyn_seq_toff_zero (initSpec.hToffUninit v rAct rWork hDisj)
    (dyn_seq_toff_zero (substActiveSingleCat_count_TOFF _ v _ rWork _)
    (count_toff_mkUninitUltraSingleCatDyn hm28 v _ rWork _))
theorem count_t_mkInitUltraExtHk_add_uninit_le {Var : Type} {mWork k_idle tStreamPair n : ℕ} (hk :
    k_idle ≤ 48) (hm28 : 28 ≤ mWork) (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair)
    (v :
    Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires
      rWork) : (mkInitUltraExtHkDyn hk hm28 initSpec v rAct rWork hDisj).count T +
      (mkUninitUltraExtHkDyn hk
    hm28 initSpec v rAct rWork hDisj).count T ≤ cInitUltraSingleCat_T + tStreamPair := by
  have hCat := count_t_mkInitUltraSingleCat_add_uninit_le
    (mPayload := 80) (B_tot := 48) (kWorkConst := 40)
    hm28 v (rAct.compose rAct0) rWork (hDisj.compose_left rAct0)
  have hs := initSpec.hTSum v rAct rWork hDisj
  dsimp only [mkInitUltraExtHkDyn, mkUninitUltraExtHkDyn]
  simp only [count_dyn_seq, count_t_cHadIdleDyn, count_t_cHadIdleInvDyn]
  omega
theorem uHadIdleFull_mul_vPrepUltra_comm_pExt6IdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) (hk17 :
    k_idle ≤ 17) : (uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)).1 *
    pExt6IdleZero
    k_idle hk = pExt6IdleZero k_idle hk * (uHadIdleFull k_idle hk * rAct0.embedUnitary
      (vPrepUltraSingleCat 80 48 40)).1 := by
  let U0 := (uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)).1
  have hUEq : U0 = rPG48Full.embedMatrix ((cCatPrepUltra1qGen 48).seq (cHadIdle48 k_idle hk)).eval.1
    := by
    dsimp only [U0]
    rw [uHadIdleFull, ← QRegister.embedUnitary_mul, QRegister.embedUnitary_val,
      uHadIdleOrig_mul_vPrepUltraSingleCat_eval_eq k_idle hk, ← QRegister.embedMatrix_compose]
    rfl
  have hCtrl3 : U0 * pCtrl3Zero = pCtrl3Zero * U0 := by
    rw [hUEq]
    refine (CommutesWithReg.of_disjoint (disj_of_val_ne fun i j ↦ ?_) _).comm_basisOutcomeProjector
      0
    rw [rPG48Full_val_eq, rUnusedCtrl3Full_val_eq]
    have := i.isLt; have := j.isLt; omega
  have hSlack3 : U0 * pSlack3Zero = pSlack3Zero * U0 := by
    rw [hUEq]
    refine (CommutesWithReg.of_disjoint (disj_of_val_ne fun i j ↦ ?_) _).comm_basisOutcomeProjector
      0
    rw [rPG48Full_val_eq, rSlack3Full_val_eq]
    have := i.isLt; have := j.isLt; omega
  have hIdle : U0 * pPGIdleZero k_idle hk = pPGIdleZero k_idle hk * U0 := by
    have hP : pPGIdleZero k_idle hk = rAct0.embedMatrix (pPGIdleZeroOrig k_idle hk) := by
      unfold pPGIdleZero pPGIdleZeroOrig rPGIdle
      rw [QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
        ← QRegister.basisOutcomeProjector]
    dsimp only [U0]
    rw [uHadIdleFull, ← QRegister.embedUnitary_mul, QRegister.embedUnitary_val, hP,
      ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul,
        uHadIdleOrig_mul_vPrepUltraSingleCat_comm_pPGIdleZeroOrig k_idle hk hk17]
  change U0 * pExt6IdleZero k_idle hk = pExt6IdleZero k_idle hk * U0
  rw [pExt6IdleZero_eq_mul, pExt6Zero_eq_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hCtrl3,
    Matrix.mul_assoc pCtrl3Zero, hSlack3, ← Matrix.mul_assoc pCtrl3Zero, Matrix.mul_assoc
    (pCtrl3Zero * pSlack3Zero),
      hIdle, ← Matrix.mul_assoc]
theorem uHadIdleFull_mul_vPrepUltra_comm_pZeroInitExt (k_idle : ℕ) (hk : k_idle ≤ 48) (hk17 : k_idle
    ≤ 17) : (uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)).1 *
    pZeroInitExt k_idle
    hk = pZeroInitExt k_idle hk * (uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat
      80 48 40)).1 := by
  have hSum : (uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)).1 *
      pSum42Zero = pSum42Zero *
      (uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)).1 := by
    rw [uHadIdleFull, ← QRegister.embedUnitary_mul, QRegister.embedUnitary_val]
    exact embedAct0_comm_pSum42Zero _
  rw [pZeroInitExt_eq_mul, ← Matrix.mul_assoc, hSum, Matrix.mul_assoc,
    uHadIdleFull_mul_vPrepUltra_comm_pExt6IdleZero k_idle hk hk17, ← Matrix.mul_assoc]
theorem vPrepUltraExtHk_mul_pZeroInitExt {mWork k_idle tStreamPair : ℕ} (hk : k_idle ≤ 48) (hk17 :
    k_idle ≤ 17) (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) : (vPrepUltraExtHk
    k_idle hk
    initSpec.uStreamInit).1 * pZeroInitExt k_idle hk = E_segExt k_idle hk * (uHadIdleFull k_idle hk
      * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)).1 := by
  unfold vPrepUltraExtHk E_segExt
  rw[Submonoid.coe_mul, Matrix.mul_assoc, uHadIdleFull_mul_vPrepUltra_comm_pZeroInitExt k_idle hk
    hk17, pZeroInitExt_eq_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, initSpec.hMulPSum42Zero,
    Matrix.mul_assoc]
theorem mkInitUltraExtHkDyn_realizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var] {mWork
    k_idle tStreamPair n : ℕ} [NeZero (2 ^ n)] (hk : k_idle ≤ 48) (hk17 : k_idle ≤ 17) (hm28 : 28 ≤
    mWork)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (v : Var) (rAct : QRegister kFull80
      n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : RealizesOnProj (pZeroExtOn
      k_idle hk
    rAct rWork) (rAct.embedUnitary (vPrepUltraExtHk k_idle hk initSpec.uStreamInit))
      (mkInitUltraExtHkDyn hk hm28 initSpec v rAct rWork hDisj) := by
  let hm1 : 1 ≤ mWork := Nat.le_trans (by decide : 1 ≤ 28) hm28
  have pCat : RealizesClean rAct rWork (rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)) _
      := (realizesCleanWorkspace_mkInitUltraSingleCatDyn hm28 v (rAct.compose rAct0)
      rWork (hDisj.compose_left rAct0)).widenActive
  have pHad : RealizesClean rAct rWork (uHadIdleFull k_idle hk)
      (cHadIdleDyn k_idle hk hm1 v (rAct.compose rAct0) rWork) :=
    (realizesCleanWorkspace_substActiveSingleCat hm1 v (rAct.compose rAct0) rWork
      (hDisj.compose_left rAct0) (cHadIdleOrig k_idle hk)).widenActive
  have pPre : RealizesOnProj (pZeroExtOn k_idle hk rAct rWork) (rAct.embedUnitary
      (uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40))) _ :=
      RealizesOnProj.of_clean_embed hDisj (pZeroInitExt k_idle hk) (pCat.seq hDisj pHad)
  have hInter := embedIntertwine hDisj (uHadIdleFull_mul_vPrepUltra_comm_pZeroInitExt k_idle hk
    hk17)
  have hChain := pPre.seq_intertwine hInter (initSpec.hRealInit v rAct rWork hDisj)
  rw [← QRegister.embedUnitary_mul] at hChain
  exact hChain
theorem mkUninitUltraExtHkDyn_realizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var] {mWork
    k_idle tStreamPair n : ℕ} [NeZero (2 ^ n)] (hk : k_idle ≤ 48) (hm28 : 28 ≤ mWork) (initSpec :
    Stream42ExtInitSpec mWork k_idle hk tStreamPair) (v : Var) (rAct : QRegister kFull80 n) (rWork :
      QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : RealizesOnProj (pHoistExtOn k_idle hk
      rAct
    rWork) (rAct.embedUnitary (vInvUltraExtHk k_idle hk initSpec.uStreamInit))
      (mkUninitUltraExtHkDyn hk hm28 initSpec v rAct rWork hDisj) := by
  let hm1 : 1 ≤ mWork := Nat.le_trans (by decide : 1 ≤ 28) hm28
  have pHadInv : RealizesClean rAct rWork (uHadIdleFull k_idle hk)⁻¹
      (cHadIdleInvDyn k_idle hk hm1 v (rAct.compose rAct0) rWork) := by
    have h0 := (realizesCleanWorkspace_substActiveSingleCat hm1 v (rAct.compose rAct0) rWork
      (hDisj.compose_left rAct0) (cHadIdleOrig k_idle hk).inverse).widenActive
    rw [Circuit.eval_inverse, ← embedUnitary_inv_symm] at h0
    exact h0
  have pCatInv : RealizesClean rAct rWork (rAct0.embedUnitary (vInvUltraSingleCat 80 48 40)) _
      := (realizesCleanWorkspace_mkUninitUltraSingleCatDyn hm28 v (rAct.compose rAct0)
      rWork (hDisj.compose_left rAct0)).widenActive
  have pPost : RealizesOnProj (pZeroExtOn k_idle hk rAct rWork) (rAct.embedUnitary
      (rAct0.embedUnitary (vInvUltraSingleCat 80 48 40) * (uHadIdleFull k_idle hk)⁻¹)) _ :=
      RealizesOnProj.of_clean_embed hDisj (pZeroInitExt k_idle hk) (pHadInv.seq hDisj pCatInv)
  have hInter : (rAct.embedUnitary initSpec.uStreamInit⁻¹).1 * pHoistExtOn k_idle hk rAct rWork =
      pZeroExtOn k_idle hk rAct rWork * 1 := by
    have h0 : (initSpec.uStreamInit⁻¹).1 * E_segExt k_idle hk = pZeroInitExt k_idle hk * 1 := by
      rw [mul_one]; exact uStreamInit_inv_mul_E_segExt hk initSpec
    have h1 := embedIntertwine hDisj h0
    rwa [rAct.embedMatrix_one] at h1
  have hChain := (initSpec.hRealUninit v rAct rWork hDisj).seq_intertwine hInter pPost
  rw [← QRegister.embedUnitary_mul] at hChain
  exact hChain
section Part2bCertPackages
/-- Packaged 10-horizon 1-angle Stage-2 certificate table for `ExtHk` at idle width `k_idle`. -/
structure OneAngleExtHkHorizonCertTable (β_nat M k_idle : ℕ) where
  nSeg : Fin 10 → ℕ
  rotToffSum : Fin 10 → ℕ
  cert : ∀ j : Fin 10, GeneralBetaSegmentCert β_nat M (nSeg j)
  hDiv : ∀ (j : Fin 10) (i : Fin (M + 1)), 2 ^ (k_idle - 6) ∣ ((cert j).C i).val
  hRot : ∀ j : Fin 10, ∑ t : Fin (M + 1), gidneyRotToffEquiv ((cert j).C t).val ≤ rotToffSum j
end Part2bCertPackages
section Part3TopMasterClosure
structure GenBetaExtHkSelAndPertSpec (mWork k_idle : ℕ) (hk : k_idle ≤ 48)
    (α : ℝ) (tPrep tSelCtrl tSelCat : Fin 10 → ℕ) (ε_BE : Fin 10 → ℝ) where
  qft : FullSysQft654Bundle
  prep : Fin 10 → FullSysPrepareBundle 80
  selOra : Fin 10 → FullSysSelectOracleBundle 80 48
  selImpl : ∀ j, SingleCatSelectImpl 80 48 qft (selOra j)
  sel : ∀ j, HoistedExtHkSelectSpec mWork k_idle hk (tSelCtrl j) (tSelCat j)
    qft (selOra j) (selImpl j)
  hmPrep : ∀ j, (prep j).mWorkPrep ≤ mWork
  hTPrep : ∀ j, (prep j).tPrep ≤ tPrep j
  hPrepLow : ∀ j c, FixesLow3924 h3924_be ((prep j).uPrep c).1
  hPrepCtrl3 : ∀ j c, FixesCtrl3 h3954_be ((prep j).uPrep c).1
  hTwist_s2 : ∀ j c, ((selOra j).uTwist c).1 * slotBitProj (iSlot2 80) 0 =
    slotBitProj (iSlot2 80) 0 * ((selOra j).uTwist c).1
  hTwist_s1 : ∀ j c, ((selOra j).uTwist c).1 * slotBitProj (iSlot1 80) 1 =
    slotBitProj (iSlot1 80) 1 * ((selOra j).uTwist c).1
  hTwist_s0 : ∀ j c, ((selOra j).uTwist c).1 * slotBitProj (iSlot0 80) 0 =
    slotBitProj (iSlot0 80) 0 * ((selOra j).uTwist c).1
  hPos_slack : ∀ j c,
    let P_slack := slotBitProj (iSlot2 80) 0 * slotBitProj (iSlot1 80) 1 * slotBitProj (iSlot0 80) 0
    ((selOra j).uPosPhase c).1 * P_slack = P_slack
  hα : 0 < α
  hPert : ∀ (j : Fin 10) (c : Configuration) (spinUp : Finset (Fin numElectrons)),
    ∃ (E₀ δ_prep ε_id : ℝ) (Heff_act Heff_id : Operator (2 ^ systemQubits)),
      δ_prep + ε_id ≤ ε_BE j ∧
      Commute (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))
        SpecsAux.gridProjector ∧
      IsQubitizedBlockEncodingUnitary α
        (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))
        (ghostZeroedBE systemQubits (fullSysRawAncWires 80)
          (by dsimp [fullSysRawAncWires]; omega) gridValidBool
          (fullSysRawBEUnitary qft (prep j) (selOra j) c)) ∧
      Heff_id.IsHermitian ∧
      Commute Heff_id SpecsAux.gridProjector ∧
      ‖SpecsAux.gridProjector * (Heff_act - Heff_id) *
          SpecsAux.gridProjector‖ ≤ δ_prep ∧
      AgreesOnFermionicSector spinUp Heff_id
        (smToTwosSysUnitary.1 * hamiltonian c * smToTwosSysUnitary.1ᴴ) ε_id
end Part3TopMasterClosure
end ChiralBBody
end CleanChiralBMasterStitch
end GqspCleanCoinAndGuardBridge
end
end GqspCleanCoinAndGuardBridge

end QuantumComputation.Specs.StoppingPowerSolution
end
