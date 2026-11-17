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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.DualBellReflStage5Stack
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option allowUnsafeReducibility true

set_option autoImplicit false
open scoped Matrix BigOperators
noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84
  QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst
  QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
  QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
  QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
set_option exponentiation.threshold 8192
open PhotochemistrySolution.ProviderZeroFloor PhotochemistrySolution.PotOraclePortB
  PhotochemistrySolution.PotOraclePortBStream PhotochemistrySolution.PotOraclePortBStage4
  PhotochemistrySolution.Kinetic664 PhotochemistrySolution.Kinetic664Stage4
  PhotochemistrySolution.PortBSharedPoly
open PhotochemistrySolution.DynQromUncompA PhotochemistrySolution.FineLegendre
  PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.XMeasChunkQromUnldA
  PhotochemistrySolution.XMeasChunkQromUnld
open PhotochemistrySolution.PotOracleGen
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local semireducible] projBit chunkXorOp
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState phaseFlipUnitary bSpeciesSwap50 Stage4KinFull.bAxisMux27 clampOneHot
    packPortBSt
/- ## Section 1: Unpack-Free Reflected `PortB` Potential Wrapper `pPotWrapReflCoinKPortBNoUnpack` -/

theorem reflPackPair_ne {W n : ℕ} (r : QRegister (122 + W) n) (h24 : 24 ≤ W) {i : ℕ} (hi : i < 24) :
    r ⟨4, (packUnpack_b h24 hi).1⟩ ≠ r ⟨57 + i, (packUnpack_b h24 hi).2.1⟩ :=
  r.wires.injective.ne fun e ↦ (packUnpack_b h24 hi).2.2.2.2.2.1 (congrArg Fin.val e)

theorem val_wPotFlags_rPot0Layout :
    (wPotIsScreen rPot0Layout).val = 5747 ∧ (wPotIsPot rPot0Layout).val = 5748 ∧
        (wPotIsNN rPot0Layout).val = 5750 :=
  ⟨val_potZeroNEremWireFn pot0_le_690 (j := ⟨1, by omega⟩),
   val_potZeroNEremWireFn pot0_le_690 (j := ⟨2, by omega⟩),
   val_potZeroNEremWireFn pot0_le_690 (j := ⟨4, by omega⟩)⟩

theorem routedKet_validFlags_portB {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {α : BitAssignment dLayout} (hScr : CleanScr α) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    let rk := routedKet decodeCoin α c z
    (rk (wPotIsPot rPot0Layout) = 0 → rk (wPotIsScreen rPot0Layout) = 0 ∧
        rk (wPotIsNN rPot0Layout) = 0) ∧
    (rk (wPotIsScreen rPot0Layout) = 0 → rk (wPotIsNN rPot0Layout) = 0) := by
  intro rk
  let lt {k m} (x : Fin k) (h : k < m := by decide) : x.val < m := Nat.lt_trans x.isLt h
  have checkSec {hN1 hN2 : Bool} {n1 n2 : ℕ} {hE1 hE2 : Bool} {e1 e2 : ℕ}
      {isScreen isPot isKin isNN : Bool} {sp1 aux2 : ℕ}
      (heq : zeroNEremOutMask (decodeCoin c) =
          packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2)
      (ln1 : n1 < 64 := by
        omega) (ln2 : n2 < 64 := by omega) (le1 : e1 < 256 := by omega) (le2 : e2 < 256 := by omega)
      (impP : isPot = false → isScreen = false ∧ isNN = false := by decide)
      (impS : isScreen = false → isNN = false := by decide) :
      (rk (wPotIsPot rPot0Layout) = 0 → rk (wPotIsScreen rPot0Layout) = 0 ∧
          rk (wPotIsNN rPot0Layout) = 0) ∧
      (rk (wPotIsScreen rPot0Layout) = 0 → rk (wPotIsNN rPot0Layout) = 0) := by
    have F :=
        packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2
        ln1 ln2 le1 le2 rk
      fun j ↦ (routedKet_out40 hScr c z j).trans (by dsimp [outMaskBits40]; rw [heq])
    rw [show wPotIsPot rPot0Layout = wIsFine from
        Fin.ext (val_wPotFlags_rPot0Layout.2.1.trans (val_rOut40Layout ⟨33, by omega⟩).symm),
      F.2.2.2.2.2.2.2.2.2.1, F.2.2.2.2.2.2.2.2.1, F.2.2.2.2.2.2.2.2.2.2.2.1]
    cases isPot <;> cases isScreen <;> cases isNN <;> simp_all [one_ne_zero]
  cases hc : decodeCoin c with
  | idle =>
        exact checkSec (show _ =
        packOut40ZeroNErem false false 0 0 false false 0 0 false false false false 0 0
        by rw [hc]; rfl)
  | ee n1 e1 e2 => exact checkSec (by rw [hc, zeroNEremOutMask]) (lt n1) (by omega) (lt e1) (lt e2)
  | nn n1 n2 e1 => exact checkSec (by rw [hc, zeroNEremOutMask]) (lt n1) (lt n2) (lt e1)
  | en n1 e1 => exact checkSec (by rw [hc, zeroNEremOutMask]) (lt n1) (le1 := lt e1)
  | kin i ax =>
      have _ := i.isLt
      exact if hi : i.val < 47 then checkSec (by rw [hc, zeroNEremOutMask, ite_eq_left hi])
        else checkSec (by rw [hc, zeroNEremOutMask, ite_eq_right hi])

/--
Clamped bit-assignment enforcing `ValidPotBFlags` (`isPot = 0 → isScreen = 0 ∧ isNN = 0` and
`isScreen = 0 → isNN = 0`) identically on all `δ`.
-/
def clampFlags {n : ℕ} (rTot : QRegister dLayout n) (δ : BitAssignment n) : BitAssignment n :=
  let wP := rTot (wPotIsPot rPot0Layout); let wS := rTot (wPotIsScreen rPot0Layout);
  let wN := rTot (wPotIsNN rPot0Layout)
  Function.update (Function.update δ wS (δ wP * δ wS)) wN (δ wP * δ wS * δ wN)

/-- Combined reflected `PortB` clamp enforcing both `ValidPotBFlags` and `OneHot` on all `δ`. -/
def clampPotBRefl {n : ℕ} (rTot : QRegister dLayout n) (δ : BitAssignment n) : BitAssignment n :=
    clampOneHot rTot (clampFlags rTot δ)

theorem clampFlags_apply {n : ℕ} (rTot : QRegister dLayout n) (δ : BitAssignment n) :
    let wP := rTot (wPotIsPot rPot0Layout); let wS := rTot (wPotIsScreen rPot0Layout);
    let wN := rTot (wPotIsNN rPot0Layout)
    clampFlags rTot δ wP = δ wP ∧ clampFlags rTot δ wS = δ wP * δ wS ∧
    clampFlags rTot δ wN = δ wP * δ wS * δ wN ∧ (∀ w : Wire n, w ≠ wS → w ≠ wN →
        clampFlags rTot δ w = δ w) := by
  intro wP wS wN
  obtain ⟨hvS, hvP, hvN⟩ := val_wPotFlags_rPot0Layout
  have hne {u v : Wire dLayout} (h : u.val ≠ v.val) : rTot u ≠ rTot v :=
    rTot.wires.injective.ne fun e ↦ h (congrArg Fin.val e)
  dsimp only [clampFlags]
  exact ⟨by rw [Function.update_of_ne (hne (by omega)), Function.update_of_ne (hne (by omega))],
    by rw [Function.update_of_ne (hne (by omega)), Function.update_self],
        Function.update_self _ _ _,
    fun w hwS hwN ↦ by rw [Function.update_of_ne hwN, Function.update_of_ne hwS]⟩

theorem clampPotBRefl_props_portB151 {n Wp : ℕ} (hWp : Wp ≤ 738) (rTot : QRegister dLayout n) :
    let hMax := maxWp24_le_738 hWp; let rW := rTot.compose rClean714Layout
    let rB := rTot.compose (rPotZeroNEremPortB151 (max Wp 24) hMax)
    let rSub := rB.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le (Nat.le_max_left Wp 24)))
    let st0 := clampPotBRefl rTot
    (∀ δ, ValidPotBFlags rSub (packPortBSt rB (Nat.le_max_right Wp 24) st0 δ)) ∧
    (∀ δ (b : Fin 24),
      (st0 δ (rB ⟨4, by omega⟩) = 0 → st0 δ (rB ⟨122 + b.val, by omega⟩) = 0) ∧
      (st0 δ (rB ⟨4, by omega⟩) = 1 → st0 δ (rB ⟨57 + b.val, by omega⟩) = 0)) ∧
    (∀ δ (u : Fin (max Wp 24)), 24 ≤ u.val → (∀ q : Fin 714, δ (rW q) = 0) →
      st0 δ (rB ⟨122 + u.val, by omega⟩) = 0) := by
  intro hMax rW rB rSub st0
  obtain ⟨hvS, hvP, hvN⟩ := val_wPotFlags_rPot0Layout
  obtain ⟨hOHBase, hClnBase⟩ := clampOneHot_props_portB151 hWp rTot
  have hne {u v : Wire dLayout} (h : u.val ≠ v.val) : rTot u ≠ rTot v :=
      rTot.wires.injective.ne fun e ↦ h (congrArg Fin.val e)
  refine ⟨fun δ ↦ ?_, fun δ b ↦ hOHBase (clampFlags rTot δ) b, fun δ u hu24 hz ↦ ?_⟩
  · have hKeep (c : ℕ) (hc : c < 33) {u : Wire dLayout} (heq : rPot0Layout ⟨c, by omega⟩ = u := by
      rfl) (hu : u.val ≤ 5750 := by omega) :
        packPortBSt rB (Nat.le_max_right Wp 24) st0 δ (rSub ⟨c, by omega⟩) =
            clampFlags rTot δ (rTot u) := by
      rw [show rSub ⟨c, by omega⟩ =
          rB ⟨c, by omega⟩ from congrArg rB.wires (Fin.ext (Nat.zero_add c)), packPortBSt,
        writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem rB 122 _ c (by omega) (by omega)),
        writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem rB 57 _ c (by omega) (by omega))]
      refine (congrArg (fun w ↦ st0 δ (rTot w))
          (Fin.ext ?_)).trans ((clampOneHot_apply rTot (clampFlags rTot δ)).2.2 _
        (fun b ↦ hne (by rw [val_rBufHi_rNucLayout]; omega))
            (fun b ↦ hne (by rw [val_rBufHi_rElecLayout]; omega)))
      rw [← heq]
      change (potZeroNEremPortB151WireFn _ hMax _).val = (potZeroNEremWireFn 0 pot0_le_690 _).val
      rw [val_potZeroNEremPortB151WireFn hMax, val_potZeroNEremWireFn pot0_le_690]
      dsimp; split_ifs <;> omega
    obtain ⟨fP, fS, fN, _⟩ := clampFlags_apply rTot δ
    dsimp only [ValidPotBFlags]
    rw [(hKeep 2 (by omega)).trans fP, (hKeep 1 (by omega)).trans fS, (hKeep 4 (by omega)).trans fN]
    exact ⟨fun hp0 ↦ by simp [hp0], fun hs0 ↦ by simp [hs0]⟩
  · refine hClnBase (clampFlags rTot δ) u hu24 fun q ↦ ?_
    have hqNot {w : Wire dLayout} (hw : w.val = 5747 ∨ w.val = 5750) : rW q ≠ rTot w := hne fun e ↦
        by
      have _ := q.isLt
      have hq := val_rClean714Layout q
      split_ifs at hq <;> omega
    exact ((clampFlags_apply rTot δ).2.2.2 (rW q) (hqNot (Or.inl hvS))
        (hqNot (Or.inr hvN))).trans (hz q)

/-
## Section 1: Generic Coin-Band Disjointness & Unpack-Free `PortB` (`151`-wire) Potential Wrapper
-/

/-- Empty `0`-wire register on `n` qubits for unconditional `mkKetOpW` ket-map lifting. -/
def rEmptyRefl (n : ℕ) : QRegister 0 n := ⟨⟨Fin.elim0, fun a ↦ a.elim0⟩⟩

theorem rPotPortB151_disj_coinBand7256 {K Wp : ℕ} (hWp : Wp ≤ 738) (rCoin : QRegister K dLayout)
    (hBand : ∀ j : Fin K, 7143 ≤ (rCoin j).val ∧ (rCoin j).val < 7256) :
        (rPotZeroNEremPortB151 Wp hWp).DisjointWires rCoin :=
  disj_of_ne fun i j e ↦ by
    have _ := i.isLt
    have _ := hBand j
    have hv := (val_potZeroNEremPortB151WireFn hWp i).symm.trans (congrArg Fin.val e)
    split_ifs at hv <;> omega

theorem writeReg_writeReg_compose {d m n : ℕ} (β : BitAssignment n) (rTot : QRegister d n)
    (rSub0 : QRegister m d) (z : BitAssignment m) :
    writeReg β rTot (writeReg (fun k ↦ β (rTot k)) rSub0 z) =
        writeReg β (rTot.compose rSub0) z := by
  funext w
  by_cases hm : ∃ j : Fin m, (rTot.compose rSub0) j = w
  · obtain ⟨j, rfl⟩ := hm
    change writeReg β rTot _ (rTot (rSub0 j)) =
        writeReg β (rTot.compose rSub0) z ((rTot.compose rSub0) j)
    rw [writeReg_apply_reg, writeReg_apply_reg, writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ (rTot.compose rSub0) z w hm]
    by_cases hk : ∃ k : Fin d, rTot k = w
    · obtain ⟨k, rfl⟩ := hk
      rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ rSub0 z k (fun ⟨j, hj⟩ ↦
          hm ⟨j, congrArg rTot.wires hj⟩)]
    · exact writeReg_apply_of_not_mem _ rTot _ w hk

theorem embedUnitary_uPotReflMuxZeroNErem_mulVec_ket {K n : ℕ} [NeZero (2 ^ n)]
    {peK : BitAssignment K → PotExpectFn}
    (rTot : QRegister dLayout n) (rCoin : QRegister K dLayout)
        (hBand : ∀ j : Fin K, 7143 ≤ (rCoin j).val ∧ (rCoin j).val < 7256)
    (specK : ∀ γ : BitAssignment K, ReflPotSliceSpec (peK γ)) (isCsel : Bool)
        (β : BitAssignment n) :
    let r0 := rTot.compose rPot0Layout; let rC := rTot.compose rCoin
    (rTot.embedUnitary (uPotReflMuxZeroNErem rCoin hBand specK isCsel)).1.mulVec (ket β) =
      QubitizationWalkSem.bitSign (potReflPh4 (specK (fun j ↦ β (rC j))) isCsel r0 β) •
        ket (potReflSwap4 (specK (fun j ↦ β (rC j))) isCsel r0 β) := by
  intro r0 rC
  let bS := PhotochemistrySolution.QubitizationWalkSem.bitSign
  let phL (α : BitAssignment dLayout) :=
      potReflPh4 (specK (fun j ↦ α (rCoin j))) isCsel rPot0Layout α
  let gL (α : BitAssignment dLayout) :=
      potReflSwap4 (specK (fun j ↦ α (rCoin j))) isCsel rPot0Layout α
  let V : Operator (2 ^ n) := mkKetOpW (rEmptyRefl n)
    (fun δ ↦ writeReg δ rTot (gL (fun k ↦ δ (rTot k)))) (fun δ ↦ phL (fun k ↦ δ (rTot k)))
  have hV (δ : BitAssignment n) : V.mulVec (ket δ) =
      bS (phL (fun k ↦ δ (rTot k))) • ket (writeReg δ rTot (gL (fun k ↦ δ (rTot k)))) := by
    rw [mkKetOpW_mulVec_ket, ite_eq_left fun q : Fin 0 ↦ q.elim0]
  rw [show (rTot.embedUnitary (uPotReflMuxZeroNErem rCoin hBand specK isCsel)).1 = V from
      embedMatrix_eq_of_ketMap rTot (uPotReflMuxZeroNErem rCoin hBand specK isCsel).1 V
        (fun α ↦ bS (phL α)) gL
        (fun α ↦ (muxMat_mulVec_ket_c70 rCoin (fun γ ↦ uPotReflZeroNErem (specK γ) isCsel) α).trans
          (uPotReflZeroNErem_mulVec_ket _ isCsel α)) hV, hV]
  refine congrArg (bS _ • ket ·) ?_
  dsimp only [gL, potReflSwap4]
  change writeReg β rTot (if potGateActive4 isCsel r0 β then _ else _) = _
  split_ifs
  · exact writeReg_writeReg_compose β rTot (rPotCoin41 rPot0Layout) _
  · exact writeReg_self rTot β

theorem swapHi24Bits_writeReg_rPotCoin41 {n : ℕ} (rTot : QRegister dLayout n) (η : BitAssignment n)
    (z' : BitAssignment 41) :
    swapHi24Bits rTot (writeReg η (rPotCoin41 (rTot.compose rPot0Layout)) z') =
      writeReg (swapHi24Bits rTot η) (rPotCoin41 (rTot.compose rPot0Layout)) z' := by
  let rC41 := rPotCoin41 (rTot.compose rPot0Layout)
  obtain ⟨_, _, hvN⟩ := val_wPotFlags_rPot0Layout
  have keep (δ : BitAssignment n) {u : Wire dLayout} (hu : u.val < 7256) :
      writeReg δ rC41 z' (rTot u) = δ (rTot u) :=
    writeReg_apply_of_not_mem δ rC41 z' _ fun ⟨m, hm⟩ ↦ by
      have hv := (val_potZeroNEremWireFn pot0_le_690 ⟨105 + m.val, _⟩).symm.trans
        (congrArg Fin.val (rTot.wires.injective hm))
      dsimp at hv; split_ifs at hv <;> omega
  obtain ⟨sE1, sN1, sO1⟩ := swapHi24Bits_apply rTot (writeReg η rC41 z')
  obtain ⟨sE2, sN2, sO2⟩ := swapHi24Bits_apply rTot η
  have kE (δ) (b : Fin 24) :=
      keep δ (u := rBufHi rElecLayout b)
      (by rw [val_rBufHi_rElecLayout]; have _ := b.isLt; omega)
  have kN (δ) (b : Fin 24) :=
      keep δ (u := rBufHi rNucLayout b)
      (by rw [val_rBufHi_rNucLayout]; have _ := b.isLt; omega)
  funext w
  by_cases hwE : ∃ b : Fin 24, w = rTot (rBufHi rElecLayout b)
  · obtain ⟨b, rfl⟩ := hwE
    rw [sE1 b, keep η (by omega), kN η b, kE η b, kE _ b, sE2 b]
  · by_cases hwN : ∃ b : Fin 24, w = rTot (rBufHi rNucLayout b)
    · obtain ⟨b, rfl⟩ := hwN
      rw [sN1 b, keep η (by omega), kE η b, kN η b, kN _ b, sN2 b]
    · rw [sO1 w (fun b e ↦ hwE ⟨b, e⟩) (fun b e ↦ hwN ⟨b, e⟩)]
      by_cases hwC : ∃ m : Fin 41, rC41 m = w
      · obtain ⟨m, rfl⟩ := hwC
        rw [writeReg_apply_reg, writeReg_apply_reg]
      · rw [writeReg_apply_of_not_mem _ rC41 z' w hwC, writeReg_apply_of_not_mem _ rC41 z' w hwC,
          sO2 w (fun b e ↦ hwE ⟨b, e⟩) (fun b e ↦ hwN ⟨b, e⟩)]
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4

namespace QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
set_option exponentiation.threshold 256
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat PhotochemistrySolution.XMeasUnld PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.SortedRouterSpec
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.Sub5885
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream (rClean714Layout
    clean714LayoutWireFn rClean714Layout_apply cHiNSub341 cHiNSub341_disj_rCoinExt)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
/- ## Section 7D.2: `routerChain_sharedPortB341_ext` -/

theorem routerChain_sharedPortB341_ext {kExt w1 n : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {rNuc : RouterReg 47 6 dLayout} {rElec : RouterReg 187 8 dLayout}
    (hk : kExt ≤ 72) (hRegs : ValidMuxD1Stage2Regs rNuc rElec)
    (hCtrlN : ∀ p q : Fin 47, cHiNSub341 p ≠ rCtrlLo rNuc q)
    (hCtrlE : ∀ (p : Fin 47) (q : Fin 187), cHiNSub341 p ≠ rCtrlLo rElec q)
    (dN : ∀ i j, rNuc i ≠ rCoinExt kExt hk j) (dE : ∀ i j, rElec i ≠ rCoinExt kExt hk j)
    (hSort : SortedZeroNEremCoin decodeCoin) (rTot : QRegister dLayout n)
        (o1 : Stage1ZeroNEremLayout w1 decodeCoin)
    {X : Operator (2 ^ n)} (hX : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 * X = X) :
    let W_cl := rTot.embedUnitary (uStage1Clean_c70 decodeCoin)
    let Wnh_cl := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decodeCoin))
    SupportedOn (SharedPortBInput341 rTot (rTot.compose rNuc) (rTot.compose rElec)) (W_cl.1 * X) ∧
    SupportedOn (ValidZeroGatedSortedRouterInput (rTot.compose rElec)) (W_cl.1 * X) ∧
    SupportedOn (ValidZeroGatedSortedRouterInput (rTot.compose rNuc))
        ((uRouterSwapConj (rTot.compose rElec)).1 * (W_cl.1 * X)) ∧
    (uRouterSwapConj (rTot.compose rNuc)).1 * ((uRouterSwapConj (rTot.compose rElec)).1 *
        (W_cl.1 * X)) = Wnh_cl.1 * X ∧
    SupportedOn (HBZMergeInput (rTot.compose rNuc) (rTot.compose rElec)) (Wnh_cl.1 * X) ∧
    (rTot.compose rClean714Layout).basisOutcomeProjector 0 * (Wnh_cl.1 * X) = Wnh_cl.1 * X := by
  intro W_cl Wnh_cl
  obtain ⟨hSharedOld, hSE, hSN, hEq, h690⟩ :=
      routerChain_sharedPortB_ext hk hRegs dN dE hSort rTot o1 hX
  let rC := rTot.compose (rCoinExt kExt hk);
  let R₀ := (rTot.compose rScrLayout).basisOutcomeProjector 0
  let rE := rTot.compose rElec; let rN := rTot.compose rNuc
  let w := SharedPortBWiring.ofValidMuxD1_341 hRegs hCtrlN hCtrlE rTot
  have hSup341Zero : SupportedOn (fun β ↦ ∀ p : Fin 47, β (rTot (cHiNSub341 p)) = 0) (W_cl.1 * X)
      := by
    rw [show W_cl.1 * X = ∑ γ : BitAssignment kExt,
        (uTogGen_c70 rC γ).1 * (W_cl.1 * (R₀ * ((uTogGen_c70 rC γ).1 * X))) by
      nth_rw 1 [← hX]
      rw [pScrExt_eq_sum_tog_c70 hk rTot, Finset.sum_mul, Matrix.mul_sum]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      have cU : W_cl.1 * (uTogGen_c70 rC γ).1 = (uTogGen_c70 rC γ).1 * W_cl.1 := by
        rw [← embedUnitary_uTogLocal_c70]
        exact wStage1Clean_comm_rCoinExt_c70 decodeCoin hk rTot (uTogLocal_c70 γ)
      simp only [R₀, rC, ← Matrix.mul_assoc, cU]]
    refine supportedOn_sum_c70 fun γ ↦ supportedOn_uTogGen_mul_c70 rC γ
      (fun _ hβ p ↦ (DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦
        cHiNSub341_disj_rCoinExt hk p j (rTot.wires.injective hj.symm)).trans (hβ p)) ?_
    have h0 := supportedOn_cHiNSub341_zero_of_scr rTot o1
      (show R₀ * (R₀ * ((uTogGen_c70 rC γ).1 * X)) = _ by
        rw [← Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self])
    rwa [← Matrix.mul_assoc, ← wStage1Clean_mul_rScrLayout_c70 o1 rTot, Matrix.mul_assoc] at h0
  have hSupShared341 : SupportedOn (SharedPortBInput341 rTot rN rE) (W_cl.1 * X) :=
    supportedOn_mono_sorted (fun β ⟨⟨h1, h2, _, h4, h5⟩, hc341⟩ ↦ ⟨h1, h2, hc341, h4, h5⟩)
        (supportedOn_and hSharedOld hSup341Zero)
  have fixedSwap_pres {M B : ℕ} (r : RouterReg M B n) (P : BitAssignment n → Prop)
      (δ : BitAssignment n) (h0 : P δ)
      (hStep : ∀ {u}, AllPlaneMod r u → (∀ b, rHB r b ≠ u) → rRawHas2 r ≠ u → ∀ α val, P α →
          P (Function.update α u val)) :
      PreservesKetPred P ((cFixedSwapCirc r (routerCtrlLo r δ)
          (routerCtrlHi r δ)).eval.1.mulVec (ket δ)) :=
    (HCNOTSupportedIn.seq
      (hcnotSupportedIn_fixedSwapVec (S := fun u ↦ (∃ b, u = rBufLo r b ∨ u = rBufHi r b) ∨ ∃ q b,
          u = rSys r q b) _ 24 _ _ _
        (fun b ↦ Or.inl ⟨b, Or.inl rfl⟩) (fun b q _ ↦ Or.inr ⟨q, b, rfl⟩))
      (hcnotSupportedIn_fixedSwapVec _ 24 _ _ _
        (fun b ↦ Or.inl ⟨b, Or.inr rfl⟩) (fun b q _ ↦ Or.inr ⟨q, b, rfl⟩))).preservesKetPred
      (fun {u} hu α val hP ↦
        have notHdr {k : Fin (routerWidth M B)} (hk : k.val = 1 ∨ (74 + 2 * B ≤ k.val ∧ k.val < 98 +
            2 * B)) : r k ≠ u := by
          rcases hu with ⟨b', rfl | rfl⟩ | ⟨q', b', rfl⟩ <;> refine rr_ne r ?_ <;>
            have _ := b'.isLt <;> dsimp [routerWidth] at hk ⊢ <;> omega
        hStep
          (by rcases hu with ⟨b, rfl | rfl⟩ | ⟨q, b, rfl⟩
              · exact ⟨b, Or.inl rfl⟩
              · exact ⟨b, Or.inr (Or.inl rfl)⟩
              · exact ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨q, (planeOfRouter_sys r b q).symm⟩)))⟩)
          (fun b ↦ notHdr (Or.inr (by dsimp [rHB]; have _ := b.isLt; omega)))
              (notHdr (Or.inl (by dsimp [routerWidth]))) α val hP)
      (preservesKetPred_ket h0)
  have hSupHBZ : SupportedOn (HBZMergeInput rN rE) (Wnh_cl.1 * X) := by
    rw [← hEq]
    intro A B hAB
    let UN := (uRouterSwapConj rN).1
    rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B, ← Matrix.mul_assoc (A * _),
        ← Matrix.mul_assoc (B * _)]
    refine hSupShared341 _ _ fun β hβ ↦ ?_
    simp only [← Matrix.mulVec_mulVec]
    rw [show PhotochemistrySolution.SplitRouterSeqBell26k.ket β = ket β from rfl,
      uRouterSwapConj_mulVec_ket rE hβ.1.1, Matrix.mulVec_mulVec _ A UN,
          Matrix.mulVec_mulVec _ B UN]
    refine fixedSwap_pres rE
      (fun α ↦ (∀ i, α (rN i) = β (rN i)) ∧ (∀ b, α (rHB rE b) = 0) ∧ α (rRawHas2 rE) =
          β (rRawHas2 rE))
      β ⟨fun _ ↦ rfl, fun b ↦ (hβ.1.1.2.2.2.1 b).2.2.2, rfl⟩
      (fun {u} huMod hHBE_ne hRawE_ne α val ⟨hN_eq, hHBE, hRawE⟩ ↦
        ⟨fun i ↦ (Function.update_of_ne (w.rN_disj_rE_mod i u huMod) _ _).trans (hN_eq i),
         fun b ↦ (Function.update_of_ne (hHBE_ne b) _ _).trans (hHBE b),
         (Function.update_of_ne hRawE_ne _ _).trans hRawE⟩)
      (A * UN) (B * UN) fun α ⟨hN_eq, hHBE_α, hRawE_α⟩ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        uRouterSwapConj_mulVec_ket rN ((validZeroGatedSorted_congr_c70 rN (fun i ↦
            (hN_eq i).symm) hβ.2.1).1)]
    exact fixedSwap_pres rN (HBZMergeInput rN rE) α
      ⟨fun b ↦ (hN_eq _).trans (hβ.2.1.1.2.2.2.1 b).2.2.2, hHBE_α,
       fun ho ↦ hRawE_α.trans (hβ.2.2.2.2 ((hN_eq _).symm.trans ho))⟩
      (fun {u} huModN hHBN_ne hdRawN η val ⟨hHBN, hHBE, hEx⟩ ↦
        ⟨fun b ↦ (Function.update_of_ne (hHBN_ne b) _ _).trans (hHBN b),
         fun b ↦ (Function.update_of_ne
           (fun e ↦ w.modN_ne_modE huModN ⟨b,
               Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ e.symm) _ _).trans (hHBE b),
         fun ho ↦
             (Function.update_of_ne (fun e ↦
             w.modN_ne_hdrE huModN (Or.inr (Or.inl rfl)) e.symm) _ _).trans
           (hEx ((Function.update_of_ne hdRawN _ _).symm.trans ho))⟩) A B hAB
  have h714 : (rTot.compose rClean714Layout).basisOutcomeProjector 0 * (Wnh_cl.1 * X) = Wnh_cl.1 *
      X := by
    nth_rw 1 [← h690]
    rw [← Matrix.mul_assoc]
    refine (hSupHBZ (_ * _) _ fun η hHBZ ↦ ?_).trans h690
    rw [← Matrix.mulVec_mulVec, show SplitRouterSeqBell26k.ket η = DynCircExt.ket η from rfl,
      PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
    split_ifs with hC690
    · rw [PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left]
      intro q
      rw [show (rTot.compose rClean714Layout) q =
          rTot (clean714LayoutWireFn q) from congrArg rTot.wires (rClean714Layout_apply q)]
      dsimp only [clean714LayoutWireFn]
      by_cases h24 : q.val < 24
      · rw [dite_eq_left h24, show rTot (rHB rNucLayout ⟨q.val, h24⟩) = rHB rN ⟨q.val, h24⟩ from
          congrArg rTot.wires (hRegs.pubNuc ⟨86 + q.val, rw_ltHB 47 6 ⟨q.val, h24⟩⟩
              (by dsimp; omega)).symm]
        exact hHBZ.1 ⟨q.val, h24⟩
      · exact (congrArg (η ∘ rTot) (dite_eq_right h24)).trans (hC690 ⟨q.val - 24, by omega⟩)
    · exact Matrix.mulVec_zero _
  exact ⟨hSupShared341, hSE, hSN, hEq, hSupHBZ, h714⟩
end QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
end
end
