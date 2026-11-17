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
public import QuantumComputation.QuantumHoareLogic.CQAssertion
public import QuantumComputation.QuantumHoareLogic.CQState
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.AsymTwistShell
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.OpenAnchorTwoLoad
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.StageBOneWireFused
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Bell18StageABrg

set_option Elab.async false

/-!
# One-Wire Stage-B + Slot-3 Adapter (`OpenQft`, `47,617 T`)
-/

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

section StageBOneWireBridge
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 256

namespace StageBOneWireBridge
open BoothOpt_StageBPartnerCoreShave (orbitSandAnchorBoothOptBaseT)

/-- Automatic held-bit count `K = min 18 (mClean - 138)` from `mClean` clean Stage-B wires. -/
def kOneWire (mClean : ℕ) : ℕ := min 18 (mClean - 138)

/-- Parametric-`K` 1-wire anchored Stage-B `T`-count
(`(24860 - 444*K + ite) + 874` outer+inner base). -/
def stageBOneWireKBoothOptAnchorT (K B mCleanInner : ℕ) : ℕ :=
  (((24860 - 444 * K) + if K = 0 then 0 else 436) + 874) +
    orbitSandAnchorBoothOptBaseT B mCleanInner + 260 * B

/-- Automatic-`K` 1-wire anchored Stage-B `T`-count at `mClean` clean wires (`138 ≤ mClean`). -/
def stageBOneWireBoothOptAnchorT (B mClean : ℕ) : ℕ :=
  stageBOneWireKBoothOptAnchorT (kOneWire mClean) B (mClean - kOneWire mClean)

theorem kOneWire_le_18 (mClean : ℕ) : kOneWire mClean ≤ 18 := Nat.min_le_left 18 _

end StageBOneWireBridge
end StageBOneWireBridge

end QuantumComputation.Specs.StoppingPowerSolution
end


namespace QuantumComputation.Specs.StoppingPowerSolution
noncomputable section StageBOneWireCore
set_option allowUnsafeReducibility true

section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 256

namespace StageBOneWireCore
set_option exponentiation.threshold 256
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPow1w (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Real HermitianMat
open SpecsAux.SpecMirror
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF T
open PrimitiveGate (TOFF T)
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket bitSign sqrtHalf bit_cases eval_seq_mulVec ket_H matrix_ext_ket)
open FullSysCatSegmentBridge (disjointWires_concat_left)
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_neg dite_pos
open PosSlots24Barrel3Pass
open AnchorSwap0Split133
open MultiBankWStateRouter
open ParticleOneHotWState
open BoothOpt_StageBPartnerCoreShave (DiagCtxWG DiagCtxWGWritesAbove ctxShiftedPartnerFast
  ctxShiftedPartnerFast_countT ctxShiftedPartnerFast_writesAbove ctxShiftedPartnerFast_spec
  InvHoleShifted218 rShiftedIdx17OfFin rShiftedIdx17Core rShiftedIdx17OfFin_zero
  rShiftedIdx17OfFin_anc rShiftedIdx17OfFin_part rComb133 rComb133_apply_lt rComb133_apply_ge
  CleanScr116 InvShifted64x4Fast scr_zero_iff_cleanScr116 invHoleShifted218_of_invShifted64x4Fast
  selShiftedIdx17 actPreservesShifted17_to_comb133Pres wSlot1Core_ofFin_val
  rAnchorIdx_ofFin_val_local rPartnerIdx_ofFin_val_local rElecSlot_ofFin_val_local
  shiftedPartnerSlotFast_congr shiftedPartnerSlotFast_congr_outside)
open BoothOpt_P4_10_TwoLoadHeldRowTrueSwap

attribute [local irreducible] ctxShiftedPartnerFast uLensSwap shiftedPartnerLens218

-- ============================================================================
-- Section 1: 1-Wire Partner Bit Holding Unitaries (`uHold1WireBit`, `uHold1WirePrefix`)
-- ============================================================================

theorem unitary_comm_mul {d : ℕ} (A V₁ V₂ : Unitary d)
    (h₁ : A * V₁ = V₁ * A) (h₂ : A * V₂ = V₂ * A) :
    A * (V₁ * V₂) = (V₁ * V₂) * A := by
  apply Subtype.ext
  change A.1 * (V₁.1 * V₂.1) = (V₁.1 * V₂.1) * A.1
  have hi1 : A.1 * V₁.1 = V₁.1 * A.1 := congrArg Subtype.val h₁
  have hi2 : A.1 * V₂.1 = V₂.1 * A.1 := congrArg Subtype.val h₂
  rw [← Matrix.mul_assoc, hi1, Matrix.mul_assoc, hi2, ← Matrix.mul_assoc]

private theorem zmod2_add_eq_iff (a b d : ZMod 2) : a + d = b ↔ a = b + d := by
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases d with rfl | rfl <;> decide

/-- Z-basis XOR map toggling the active shifted-partner bit `j : Fin 18` into a single wire
  `wOut`. -/
noncomputable def hold1WireMap {n : ℕ} (rCore : QRegister posCoreWires n) (wOut : Wire n)
    (j : Fin 18) (β : BitAssignment n) : BitAssignment n :=
  let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
  Function.update β wOut (β wOut + β (rElecSlot rCore s₀ j))

private theorem hold1WireMap_involutive {n : ℕ} (rCore : QRegister posCoreWires n) (wOut : Wire n)
    (j : Fin 18) (hCW : ∀ w : Wire posCoreWires, rCore w ≠ wOut) :
    Function.Involutive (hold1WireMap rCore wOut j) := fun β ↦ by
  let α := hold1WireMap rCore wOut j β
  have hCoreEq : ∀ w : Wire posCoreWires, α (rCore w) = β (rCore w) :=
    fun w ↦ Function.update_of_ne (hCW w) _ _
  have hSlot : shiftedPartnerSlotFast (fun w ↦ α (rCore w)) =
      shiftedPartnerSlotFast (fun w ↦ β (rCore w)) :=
    congrArg shiftedPartnerSlotFast (funext hCoreEq)
  have hElec : ∀ e : Fin 218, α (rElecSlot rCore e j) = β (rElecSlot rCore e j) := fun e ↦
    Function.update_of_ne (by dsimp only [rElecSlot, QRegister.slice_apply]; exact hCW _) _ _
  funext w
  change Function.update α wOut (α wOut +
    α (rElecSlot rCore (shiftedPartnerSlotFast (fun u ↦ α (rCore u))) j)) w = β w
  rw [hSlot, hElec]
  by_cases hw : w = wOut
  · subst hw
    rw [Function.update_self]
    dsimp only [α, hold1WireMap]
    rw [Function.update_self, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · exact (Function.update_of_ne hw _ _).trans (Function.update_of_ne hw _ _)

/-- Involutive basis permutation corresponding to `hold1WireMap`. -/
noncomputable def hold1WireEquiv {n : ℕ} (rCore : QRegister posCoreWires n) (wOut : Wire n)
    (j : Fin 18) (hCW : ∀ w : Wire posCoreWires, rCore w ≠ wOut) : Equiv.Perm (Fin (2 ^ n)) :=
  let F : Fin (2 ^ n) → Fin (2 ^ n) := fun g ↦
    (basisBitsEquiv n).symm (hold1WireMap rCore wOut j (basisBits n g))
  have hInv : Function.Involutive F := fun g ↦ by
    dsimp only [F]
    have h1 : basisBits n ((basisBitsEquiv n).symm (hold1WireMap rCore wOut j (basisBits n g))) =
        hold1WireMap rCore wOut j (basisBits n g) := (basisBitsEquiv n).apply_symm_apply _
    rw [h1, hold1WireMap_involutive rCore wOut j hCW]
    exact (basisBitsEquiv n).symm_apply_apply g
  Equiv.ofBijective F hInv.bijective

/-- Involutive Z-basis unitary XORing active shifted-partner bit `j` into `wOut`. -/
noncomputable def uHold1WireBit {n : ℕ} (rCore : QRegister posCoreWires n) (wOut : Wire n)
    (j : Fin 18) (hCW : ∀ w : Wire posCoreWires, rCore w ≠ wOut) : Unitary (2 ^ n) :=
  Operator.permutationUnitary (hold1WireEquiv rCore wOut j hCW)

private theorem uHold1WireBit_mulVec_ket {n : ℕ} (rCore : QRegister posCoreWires n) (wOut : Wire n)
    (j : Fin 18) (hCW : ∀ w : Wire posCoreWires, rCore w ≠ wOut) (β : BitAssignment n) :
    (uHold1WireBit rCore wOut j hCW).1 *ᵥ ket β = ket (hold1WireMap rCore wOut j β) := by
  let g := (basisBitsEquiv n).symm β
  have hg : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  have hKet : ket β = Pi.single g 1 := rfl
  rw [hKet]
  dsimp only [uHold1WireBit]
  change (Operator.permutationUnitary (hold1WireEquiv rCore wOut j hCW)).1.mulVec (Pi.single g 1) =
    _
  rw [permUnitary_mulVec_single_one]
  dsimp only [hold1WireEquiv]
  rw [Equiv.ofBijective_apply, hg]
  rfl

private theorem hold1WireMap_eq_update_of_zero {n : ℕ}
    (rCore : QRegister posCoreWires n) (wOut : Wire n) (j : Fin 18)
    {β : BitAssignment n} (h0 : β wOut = 0) :
    hold1WireMap rCore wOut j β =
      Function.update β wOut
        (β (rElecSlot rCore (shiftedPartnerSlotFast (fun w ↦ β (rCore w))) j)) := by
  dsimp only [hold1WireMap]
  rw [h0, zero_add]

/-- Prefix product of `uHold1WireBit` across the first `k ≤ K` single-bit wires of `rHeld :
  QRegister K n`. -/
noncomputable def uHold1WirePrefix {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n)
    (hCH : rCore.DisjointWires rHeld) : ∀ (k : ℕ), k ≤ K → Unitary (2 ^ n)
  | 0, _ => 1
  | k + 1, hk =>
      uHold1WireBit rCore (rHeld ⟨k, hk⟩) ⟨k, by omega⟩ (fun w ↦ hCH.ne w ⟨k, hk⟩) *
      uHold1WirePrefix K hK rCore rHeld hCH k (by omega)

/-- Active shifted-partner values for the first `k` indices of `Fin K` (`0` for `k ≤ t.val`). -/
noncomputable def held1WirePrefixVals {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n)
    (k : ℕ) (_hk : k ≤ K) (t : Fin K) : ZMod 2 :=
  if t.val < k then
    β (rElecSlot rCore (shiftedPartnerSlotFast (fun w ↦ β (rCore w))) ⟨t.val, by omega⟩)
  else 0

/-- Full `K`-bit active shifted-partner value vector on `Fin K`. -/
noncomputable def held1WireVals {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n) (t : Fin K) : ZMod 2 :=
  β (rElecSlot rCore (shiftedPartnerSlotFast (fun w ↦ β (rCore w))) ⟨t.val, by omega⟩)

private theorem uHold1WirePrefix_mulVec_ket_of_zero {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n)
    (hCH : rCore.DisjointWires rHeld) (β : BitAssignment n)
    (hZero : ∀ t : Fin K, β (rHeld t) = 0) :
    ∀ (k : ℕ) (hk : k ≤ K),
      (uHold1WirePrefix K hK rCore rHeld hCH k hk).1 *ᵥ ket β =
        ket (p2d_writeReg β rHeld (held1WirePrefixVals K hK rCore β k hk))
  | 0, hk => by
      dsimp only [uHold1WirePrefix]
      rw [OneMemClass.coe_one, Matrix.one_mulVec]
      refine congrArg ket (funext fun w ↦ ?_)
      by_cases hm : w ∈ Set.range rHeld.wires
      · obtain ⟨t, rfl⟩ := hm
        rw [p2d_writeReg_apply_reg, hZero t]
        dsimp [held1WirePrefixVals]
      · exact (p2d_writeReg_apply_of_not_mem _ _ _ _ hm).symm
  | k + 1, hk => by
      dsimp only [uHold1WirePrefix]
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          uHold1WirePrefix_mulVec_ket_of_zero K hK rCore rHeld hCH β hZero k (by omega),
          uHold1WireBit_mulVec_ket]
      let α := p2d_writeReg β rHeld (held1WirePrefixVals K hK rCore β k (by omega))
      have hCore : (fun w ↦ α (rCore w)) = fun w ↦ β (rCore w) :=
        funext fun w ↦ p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨t, ht⟩ ↦ hCH.ne w t ht.symm
      have hSlot : shiftedPartnerSlotFast (fun w ↦ α (rCore w)) =
          shiftedPartnerSlotFast (fun w ↦ β (rCore w)) := congrArg shiftedPartnerSlotFast hCore
      have hElec : α (rElecSlot rCore (shiftedPartnerSlotFast (fun w ↦
        α (rCore w))) ⟨k, by omega⟩) =
          β (rElecSlot rCore (shiftedPartnerSlotFast (fun w ↦ β (rCore w))) ⟨k, by omega⟩) := by
        rw [hSlot]
        exact p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨t, ht⟩ ↦ by
          dsimp only [rElecSlot, QRegister.slice_apply] at ht
          exact hCH.ne _ t ht.symm
      have hαk0 : α (rHeld ⟨k, hk⟩) = 0 := by
        dsimp only [α]
        rw [p2d_writeReg_apply_reg]
        dsimp [held1WirePrefixVals]
        exact ite_eq_right (Nat.lt_irrefl k)
      refine congrArg ket (funext fun w ↦ ?_)
      change Function.update α (rHeld ⟨k, hk⟩)
          (α (rHeld ⟨k, hk⟩) + α (rElecSlot rCore (shiftedPartnerSlotFast (fun u ↦
            α (rCore u))) ⟨k, by omega⟩)) w =
        p2d_writeReg β rHeld (held1WirePrefixVals K hK rCore β (k + 1) hk) w
      rw [hαk0, zero_add, hElec]
      by_cases hm : w ∈ Set.range rHeld.wires
      · obtain ⟨t, rfl⟩ := hm
        rw [p2d_writeReg_apply_reg]
        by_cases htk : t = ⟨k, hk⟩
        · subst htk
          rw [Function.update_self]
          dsimp [held1WirePrefixVals]
          exact (ite_eq_left (Nat.lt_succ_self k)).symm
        · have hne_w : rHeld t ≠ rHeld ⟨k, hk⟩ := rHeld.wires.injective.ne htk
          rw [Function.update_of_ne hne_w]
          dsimp only [α]
          rw [p2d_writeReg_apply_reg]
          dsimp [held1WirePrefixVals]
          have hlt_iff : t.val < k ↔ t.val < k + 1 := by
            have hvne : t.val ≠ k := fun hv ↦ htk (Fin.ext hv)
            omega
          by_cases hlt : t.val < k
          · rw [ite_eq_left hlt, ite_eq_left (hlt_iff.mp hlt)]
          · rw [ite_eq_right hlt, ite_eq_right (mt hlt_iff.mpr hlt)]
      · have hne_w : w ≠ rHeld ⟨k, hk⟩ := fun h ↦ hm ⟨⟨k, hk⟩, h.symm⟩
        rw [Function.update_of_ne hne_w, p2d_writeReg_apply_of_not_mem _ _ _ _ hm]
        exact p2d_writeReg_apply_of_not_mem _ _ _ _ hm

theorem uHold1WirePrefix_eq_writeReg_of_zero {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n)
    (hCH : rCore.DisjointWires rHeld) (β : BitAssignment n)
    (hZero : ∀ t : Fin K, β (rHeld t) = 0) :
    (uHold1WirePrefix K hK rCore rHeld hCH K le_rfl).1 *ᵥ ket β =
      ket (p2d_writeReg β rHeld (held1WireVals K hK rCore β)) := by
  rw [uHold1WirePrefix_mulVec_ket_of_zero K hK rCore rHeld hCH β hZero K le_rfl]
  refine congrArg (fun v ↦ ket (p2d_writeReg β rHeld v)) (funext fun t ↦ ?_)
  dsimp [held1WirePrefixVals, held1WireVals]
  exact ite_eq_left t.isLt

-- ============================================================================
-- Section 2: Commutation & Invariant Preservation Lemmas for `uHold1Wire*`
-- ============================================================================

private theorem uHold1WireBit_comm_uKick1Bit218 {n : ℕ}
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (wOut : Wire n)
    (j₁ j₂ : Fin 18)
    (hCW : ∀ w : Wire posCoreWires, rCore w ≠ wOut)
    (hMW : ∀ m : Fin 18, rMeas m ≠ wOut) :
    uHold1WireBit rCore wOut j₁ hCW * uKick1Bit218 j₂ rCore rMeas =
      uKick1Bit218 j₂ rCore rMeas * uHold1WireBit rCore wOut j₁ hCW := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      uKick1Bit218_mulVec_ket, Matrix.mulVec_smul, uHold1WireBit_mulVec_ket,
        uKick1Bit218_mulVec_ket]
  let α := hold1WireMap rCore wOut j₁ β
  have hCore : (fun w ↦ α (rCore w)) = fun w ↦ β (rCore w) :=
    funext fun w ↦ Function.update_of_ne (hCW w) _ _
  have hSlot : shiftedPartnerSlotFast (fun w ↦ α (rCore w)) =
      shiftedPartnerSlotFast (fun w ↦ β (rCore w)) := congrArg shiftedPartnerSlotFast hCore
  have hE : ∀ e : Fin 218, α (rElecSlot rCore e j₂) = β (rElecSlot rCore e j₂) :=
    fun e ↦
      Function.update_of_ne (by dsimp only [rElecSlot, QRegister.slice_apply]; exact hCW _) _ _
  have hM : α (rMeas j₂) = β (rMeas j₂) :=
    Function.update_of_ne (hMW j₂) _ _
  dsimp only [α] at hSlot hE hM
  dsimp only
  rw [hSlot, hE, hM]

private theorem uHold1WirePrefix_comm_uKick1Bit218 {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hCH : rCore.DisjointWires rHeld) (hMH : rMeas.DisjointWires rHeld) (j : Fin 18) :
    ∀ (k : ℕ) (hk : k ≤ K),
      uHold1WirePrefix K hK rCore rHeld hCH k hk * uKick1Bit218 j rCore rMeas =
        uKick1Bit218 j rCore rMeas * uHold1WirePrefix K hK rCore rHeld hCH k hk
  | 0, _ => by dsimp only [uHold1WirePrefix]; rw [one_mul, mul_one]
  | k + 1, hk => by
      dsimp only [uHold1WirePrefix]
      exact (unitary_comm_mul (uKick1Bit218 j rCore rMeas) _ _
        (uHold1WireBit_comm_uKick1Bit218 rCore rMeas (rHeld ⟨k, hk⟩) ⟨k, by omega⟩ j
          (fun w ↦ hCH.ne w ⟨k, hk⟩) (fun m ↦ hMH.ne m ⟨k, hk⟩)).symm
        (uHold1WirePrefix_comm_uKick1Bit218 K hK rCore rMeas rHeld hCH hMH j k (by
          omega)).symm).symm

theorem uHold1WirePrefix_comm_uKickPrefix218 {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hCH : rCore.DisjointWires rHeld) (hMH : rMeas.DisjointWires rHeld)
    (k : ℕ) (hk : k ≤ K) :
    ∀ (m : ℕ) (hm : m ≤ 18),
      uHold1WirePrefix K hK rCore rHeld hCH k hk * uKickPrefix218 m hm rCore rMeas =
        uKickPrefix218 m hm rCore rMeas * uHold1WirePrefix K hK rCore rHeld hCH k hk
  | 0, _ => by rw [uKickPrefix218_zero, mul_one, one_mul]
  | m + 1, hm => by
      rw [uKickPrefix218_succ]
      exact unitary_comm_mul _ _ _
        (uHold1WirePrefix_comm_uKick1Bit218 K hK rCore rMeas rHeld hCH hMH ⟨m, hm⟩ k hk)
        (uHold1WirePrefix_comm_uKickPrefix218 K hK rCore rMeas rHeld hCH hMH k hk m (by omega))

private theorem supportedOn_uHold1WirePrefix {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n)
    (hCH : rCore.DisjointWires rHeld)
    {P : BitAssignment n → Prop}
    (hP : ∀ β₁ β₂ : BitAssignment n,
      (∀ w, w ∉ Set.range rHeld.wires → β₁ w = β₂ w) → (P β₁ ↔ P β₂))
    {R : Operator (2 ^ n)}
    (hSupp : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧ P β) R) :
    ∀ (k : ℕ) (hk : k ≤ K),
      SupportedOn (fun β ↦ (∀ (t : Fin K), k ≤ t.val → β (rHeld t) = 0) ∧ P β)
        ((uHold1WirePrefix K hK rCore rHeld hCH k hk).1 * R)
  | 0, _ => by
      dsimp only [uHold1WirePrefix]
      rw [Submonoid.coe_one, Matrix.one_mul]
      exact supportedOn_mono (fun _ ⟨hH, hPβ⟩ ↦ ⟨fun t _ ↦ hH t, hPβ⟩) hSupp
  | k + 1, hk => by
      dsimp only [uHold1WirePrefix]
      rw [Submonoid.coe_mul, Matrix.mul_assoc]
      have ih := supportedOn_uHold1WirePrefix K hK rCore rHeld hCH hP hSupp k (by omega)
      refine supportedOn_unitary_mul _ _
        (uHold1WireBit_mulVec_ket rCore (rHeld ⟨k, hk⟩) ⟨k, by omega⟩ (fun w ↦ hCH.ne w ⟨k, hk⟩))
        (fun β ⟨hRem, hPβ⟩ ↦ ⟨fun t ht ↦ ?_, ?_⟩) ih
      · have hne : rHeld t ≠ rHeld ⟨k, hk⟩ :=
          rHeld.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
        exact (Function.update_of_ne hne _ _).trans (hRem t (by omega))
      · exact (hP _ β fun w hw ↦
          Function.update_of_ne (fun h ↦ hw ⟨⟨k, hk⟩, h.symm⟩) _ _).mpr hPβ

private theorem invHoleShifted218_ignores_held1w {n mScr K : ℕ} (hm : 75 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCH : rCore.DisjointWires rHeld) (hHS : rHeld.DisjointWires rScr)
    (β₁ β₂ : BitAssignment n)
    (h : ∀ w, w ∉ Set.range rHeld.wires → β₁ w = β₂ w) :
    InvHoleShifted218 hm rCore rScr β₁ ↔ InvHoleShifted218 hm rCore rScr β₂ := by
  have hCore : (fun w ↦ β₁ (rCore w)) = fun w ↦ β₂ (rCore w) :=
    funext fun w ↦ h (rCore w) fun ⟨i, hi⟩ ↦ hCH.ne w i hi.symm
  have hSlot : shiftedPartnerSlotFast (fun w ↦ β₁ (rCore w)) =
      shiftedPartnerSlotFast (fun w ↦ β₂ (rCore w)) := congrArg shiftedPartnerSlotFast hCore
  have hScr : ∀ s : Fin mScr, β₁ (rScr s) = β₂ (rScr s) :=
    fun s ↦ h (rScr s) fun ⟨i, hi⟩ ↦ hHS.ne i s hi
  have hSub : ∀ r : Fin 4,
      β₁ (p2dSubReg rScr 70 4 (by omega) r) = β₂ (p2dSubReg rScr 70 4 (by omega) r) :=
    fun r ↦ hScr ⟨70 + r.val, by omega⟩
  dsimp only [InvHoleShifted218]
  simp only [hSlot, hScr, hSub]

-- ============================================================================
-- Section 3: Pre-Pass 1-Wire Loader + Pre-`dInner` `CZ` (`dPre1WireLoadAux`, `444 * k` `T`)
-- ============================================================================

/-- Selects the active row from `rRow70 := p2dSubReg rScr 70 4` into `wOut` (`8 T`, `0 TOFF`)
and applies the mandatory pre-`dInner` `0-T` `czCircuit wOut wMeas`. -/
noncomputable def cSelectHoldKick1Wire {n mScr : ℕ} (hm : 75 ≤ mScr)
    (rScr : QRegister mScr n) (wOut wMeas : Wire n)
    (hSW : ∀ s : Fin mScr, rScr s ≠ wOut) (hMW : wOut ≠ wMeas) : Circuit n :=
  let rRow70 := p2dSubReg rScr 70 4 (by omega)
  let uHi : Fin 4 → Wire n := fun h ↦ rScr ⟨64 + h.val, by omega⟩
  cLoadRowAnchored1Bit 4 4 (by decide) le_rfl uHi (uHi ⟨0, by decide⟩)
    (rRow70 ⟨0, by decide⟩)
    (fun i : Fin 3 ↦ rRow70 ⟨1 + i.val, by omega⟩)
    wOut
    (fun i ↦ rRow70.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)))
    (fun i ↦ by
      have hr : rRow70 ⟨1 + i.val, by omega⟩ = rScr ⟨71 + i.val, by omega⟩ :=
        congrArg rScr.wires (Fin.ext (by dsimp [rRow70, p2dSubReg]; omega))
      exact hr ▸ hSW ⟨71 + i.val, by omega⟩)
    (by
      have hr : rRow70 ⟨0, by decide⟩ = rScr ⟨70, by omega⟩ :=
        congrArg rScr.wires (Fin.ext (by dsimp [rRow70, p2dSubReg]))
      exact hr ▸ hSW ⟨70, by omega⟩)
    (fun h ↦ hSW ⟨64 + h.val, by omega⟩)
    (hSW ⟨64, by omega⟩) ;;ᶜ
  czCircuit wOut wMeas hMW

private theorem cSelectHoldKick1Wire_count_toff {n mScr : ℕ} (hm : 75 ≤ mScr)
    (rScr : QRegister mScr n) (wOut wMeas : Wire n)
    (hSW : ∀ s : Fin mScr, rScr s ≠ wOut) (hMW : wOut ≠ wMeas) :
    (cSelectHoldKick1Wire hm rScr wOut wMeas hSW hMW).count TOFF = 0 := by
  dsimp only [cSelectHoldKick1Wire]
  rw [Circuit.count_seq, cLoadRowAnchored1Bit_count_toff, czCircuit_count_toff]

private theorem cSelectHoldKick1Wire_count_t {n mScr : ℕ} (hm : 75 ≤ mScr)
    (rScr : QRegister mScr n) (wOut wMeas : Wire n)
    (hSW : ∀ s : Fin mScr, rScr s ≠ wOut) (hMW : wOut ≠ wMeas) :
    (cSelectHoldKick1Wire hm rScr wOut wMeas hSW hMW).count T = 8 := by
  dsimp only [cSelectHoldKick1Wire]
  rw [Circuit.count_seq, cLoadRowAnchored1Bit_count_t, czCircuit_count_t]

private theorem cSelectHoldKick1Wire_eval_ket {n mScr : ℕ} (hm : 75 ≤ mScr)
    (rScr : QRegister mScr n) (wOut wMeas : Wire n)
    (hSW : ∀ s : Fin mScr, rScr s ≠ wOut) (hMW : wOut ≠ wMeas)
    (α : BitAssignment n) (hOut0 : α wOut = 0)
    (h₀ : ℕ) (hh₀ : h₀ < 4)
    (hHi : ∀ h : Fin 4, α (rScr ⟨64 + h.val, by omega⟩) = if h.val = h₀ then 1 else 0) :
    (cSelectHoldKick1Wire hm rScr wOut wMeas hSW hMW).eval.1.mulVec (ket α) =
      ((-1 : ℂ) ^ (α (p2dSubReg rScr 70 4 (by omega) ⟨h₀, hh₀⟩) * α wMeas).val) •
        ket (Function.update α wOut (α (p2dSubReg rScr 70 4 (by omega) ⟨h₀, hh₀⟩))) := by
  let rRow70 := p2dSubReg rScr 70 4 (by omega)
  let uHi : Fin 4 → Wire n := fun h ↦ rScr ⟨64 + h.val, by omega⟩
  let wAct : Fin 3 → Wire n := fun i ↦ rRow70 ⟨1 + i.val, by omega⟩
  have hxInj : Function.Injective wAct := fun i₁ i₂ heq ↦ by
    have hv := congrArg Fin.val (rRow70.wires.injective heq)
    dsimp [wAct] at hv
    exact Fin.ext (by omega)
  have huNotAct : ∀ (h : Fin 4) (i : Fin 3), uHi h ≠ wAct i := fun h i heq ↦ by
    have hr : wAct i = rScr ⟨71 + i.val, by omega⟩ :=
      congrArg rScr.wires (Fin.ext (by dsimp [wAct, rRow70, p2dSubReg]; omega))
    have hv := congrArg Fin.val (rScr.wires.injective (heq.trans hr))
    dsimp [uHi] at hv
    have := h.isLt; have := i.isLt; omega
  have hbNotAct : ∀ i : Fin 3, uHi ⟨0, by decide⟩ ≠ wAct i := fun i ↦ huNotAct ⟨0, by decide⟩ i
  have hBndVal : α (uHi ⟨0, by decide⟩) = if (h₀ = 0 ∨ 4 ≤ h₀) then 1 else 0 := by
    rw [hHi ⟨0, by decide⟩]
    dsimp
    by_cases h0 : h₀ = 0
    · subst h0; simp
    · have h1 : (0 : ℕ) ≠ h₀ := Ne.symm h0
      have h2 : ¬ (h₀ = 0 ∨ 4 ≤ h₀) := by omega
      rw [ite_eq_right h1, ite_eq_right h2]
  dsimp only [cSelectHoldKick1Wire]
  rw [eval_seq_mulVec,
      cLoadRowAnchored1Bit_eval_ket 4 4 (by decide) le_rfl uHi (uHi ⟨0, by decide⟩)
        (rRow70 ⟨0, by decide⟩) wAct wOut _ _ _ _ _ hxInj huNotAct hbNotAct
        α hOut0 h₀ hh₀ hHi hBndVal]
  have hyEq : (if h0 : h₀ = 0 then α (rRow70 ⟨0, by decide⟩)
      else if hlt : h₀ < 4 then α (wAct ⟨h₀ - 1, by omega⟩)
      else α (rRow70 ⟨0, by decide⟩)) = α (rRow70 ⟨h₀, hh₀⟩) := by
    by_cases h0 : h₀ = 0
    · rw [dite_eq_left h0]
      exact congrArg (fun r ↦ α (rRow70 r)) (Fin.ext (by dsimp; omega))
    · rw [dite_eq_right h0, dite_eq_left hh₀]
      exact congrArg (fun r ↦ α (rRow70 r)) (Fin.ext (by dsimp [wAct]; omega))
  rw [hyEq, ket_czCircuit wOut wMeas hMW]
  rw [Function.update_self, Function.update_of_ne hMW.symm]

/-- Pre-pass `.hole` 1-wire loader + pre-`dInner` `CZ` kick for the first `k ≤ K` bits (`444 * k`
  `T`, `TOFF = 0`). -/
noncomputable def dPre1WireLoadAux {Var : Type} {n mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hHS : rHeld.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) :
    ∀ (k : ℕ), k ≤ K → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | k + 1, hk =>
      let rRow70 := p2dSubReg rScr 70 4 (by omega)
      let hBuf := rowBufDisj_scr70 hm rCore rScr hCS
      let j : Fin 18 := ⟨k, by omega⟩
      .seq (dPre1WireLoadAux K hK hm v rCore rMeas rHeld rScr hCS hHS hMH k (by omega))
        (.seq (.circuit (cLoad4Rows218Into hm j rCore rScr rRow70 hCS hBuf ;;ᶜ
                cSelectHoldKick1Wire hm rScr (rHeld ⟨k, hk⟩) (rMeas j)
                  (fun s ↦ (hHS.ne ⟨k, hk⟩ s).symm) (hMH.ne j ⟨k, hk⟩).symm))
              (dUncompute4Rows218 hm v j rCore rScr rRow70 hCS))

theorem dPre1WireLoadAux_count {Var : Type} {n mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hHS : rHeld.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) :
    ∀ (k : ℕ) (hk : k ≤ K),
      (dPre1WireLoadAux (Var :=
        Var) K hK hm v rCore rMeas rHeld rScr hCS hHS hMH k hk).count TOFF = 0 ∧
      (dPre1WireLoadAux (Var :=
        Var) K hK hm v rCore rMeas rHeld rScr hCS hHS hMH k hk).count T = 444 * k
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      dsimp only [dPre1WireLoadAux, DynamicCircuit.count]
      obtain ⟨h1, h2⟩ :=
        dPre1WireLoadAux_count K hK hm v rCore rMeas rHeld rScr hCS hHS hMH k (by omega)
      rw [h1, h2, Circuit.count_seq, Circuit.count_seq,
          cLoad4Rows218Into_count_toff, cLoad4Rows218Into_count_t,
          cSelectHoldKick1Wire_count_toff, cSelectHoldKick1Wire_count_t,
          dUncompute4Rows218_count_toff, dUncompute4Rows218_count_t]
      exact ⟨rfl, by omega⟩

open Classical in
theorem subspaceStep_dPre1WireLoadAux {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} [NeZero (2 ^ n)] (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCH : rCore.DisjointWires rHeld) (hCS : rCore.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) :
    ∀ (k : ℕ) (hk : k ≤ K) {R : Operator (2 ^ n)},
      SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
        InvHoleShifted218 hm rCore rScr β) R →
      SubspaceStep R
        ((uHold1WirePrefix K hK rCore rHeld hCH k hk * uKickPrefix218 k (by omega) rCore rMeas).1 *
          R)
        (dPre1WireLoadAux K hK hm v rCore rMeas rHeld rScr hCS hHS hMH k hk)
  | 0, hk, R, _ => by
      dsimp only [dPre1WireLoadAux, uHold1WirePrefix]
      rw [uKickPrefix218_zero, mul_one, Submonoid.coe_one, Matrix.one_mul]
      exact subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) R .identity) (by simp)
  | k + 1, hk, R, hSupp => by
      dsimp only [dPre1WireLoadAux]
      let rRow70 := p2dSubReg rScr 70 4 (by omega)
      let hBuf := rowBufDisj_scr70 hm rCore rScr hCS
      let j : Fin 18 := ⟨k, by omega⟩
      let wOut : Wire n := rHeld ⟨k, hk⟩
      let wMeas : Wire n := rMeas j
      have hCW : ∀ w : Wire posCoreWires, rCore w ≠ wOut := fun w ↦ hCH.ne w ⟨k, hk⟩
      have hSW : ∀ s : Fin mScr, rScr s ≠ wOut := fun s ↦ (hHS.ne ⟨k, hk⟩ s).symm
      have hMW : wOut ≠ wMeas := (hMH.ne j ⟨k, hk⟩).symm
      have ih := subspaceStep_dPre1WireLoadAux K hK hm v rCore rMeas rHeld rScr
        hCH hCS hHS hMS hMH k (by omega) hSupp
      let RK := (uKickPrefix218 k (by omega) rCore rMeas).1 * R
      have hSuppRK : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
          InvHoleShifted218 hm rCore rScr β) RK :=
        supportedOn_diagSignUnitary_mul _ hSupp
      let R_prev := (uHold1WirePrefix K hK rCore rHeld hCH k (by omega) *
        uKickPrefix218 k (by omega) rCore rMeas).1 * R
      have hSuppPrev : SupportedOn (fun β ↦ β wOut = 0 ∧
          (∀ r : Fin 4, β (rRow70 r) = 0) ∧ InvHoleBase218 hm rCore rScr β) R_prev := by
        dsimp only [R_prev]
        rw [Submonoid.coe_mul, Matrix.mul_assoc]
        exact supportedOn_mono
          (fun β ⟨hRem, hInv⟩ ↦
            ⟨hRem ⟨k, hk⟩ le_rfl, (invHoleShifted218_iff_base hm rCore rScr β).mp hInv⟩)
          (supportedOn_uHold1WirePrefix K hK rCore rHeld hCH
            (invHoleShifted218_ignores_held1w hm rCore rHeld rScr hCH hHS) hSuppRK k (by omega))
      let cPre := cLoad4Rows218Into hm j rCore rScr rRow70 hCS hBuf ;;ᶜ
        cSelectHoldKick1Wire hm rScr wOut wMeas hSW hMW
      let R_step := (uHold1WireBit rCore wOut j hCW).1 * ((uKick1Bit218 j rCore rMeas).1 * R_prev)
      have s1 : SubspaceStep (Var := Var) R_prev
          ((uHold1Bit rCore rRow70 j hBuf.1).1 * R_step) (.circuit cPre) := by
        refine subspaceStep_congr_out (subspaceStep_of_circuit R_prev cPre) ?_
        have hEq : cPre.eval.1 * R_prev =
            ((uHold1Bit rCore rRow70 j hBuf.1).1 *
              ((uHold1WireBit rCore wOut j hCW).1 * (uKick1Bit218 j rCore rMeas).1)) * R_prev :=
          hSuppPrev cPre.eval.1
            ((uHold1Bit rCore rRow70 j hBuf.1).1 *
              ((uHold1WireBit rCore wOut j hCW).1 * (uKick1Bit218 j rCore rMeas).1))
            fun β ⟨hOut0, hRow0, hLo, hHi, hPar0, _⟩ ↦ by
              let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
              have hh₀ : s₀.val / 64 < 4 := by have := s₀.isLt; omega
              have hl₀ : s₀.val % 64 < 64 := Nat.mod_lt _ (by decide)
              let vals := rowBit218 rCore j β (s₀.val % 64)
              let α₁ := p2d_writeReg β rRow70 vals
              have hα₁_out : α₁ wOut = 0 :=
                (p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦ by
                  have hr' : rRow70 r = rScr ⟨70 + r.val, by omega⟩ :=
                    congrArg rScr.wires (Fin.ext (by dsimp [rRow70, p2dSubReg]))
                  exact hSW ⟨70 + r.val, by omega⟩ (hr'.symm.trans hr)).trans hOut0
              have hα₁_hi : ∀ h : Fin 4, α₁ (rScr ⟨64 + h.val, by
                omega⟩) = if h.val = s₀.val / 64 then 1 else 0 :=
                fun h ↦ (p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦
                  (hBuf.2 ⟨64 + h.val, by
                    omega⟩ r (Or.inl (by dsimp; omega))) hr.symm).trans (hHi h)
              have hα₁_meas : α₁ wMeas = β wMeas :=
                p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦ by
                  have hr' : rRow70 r = rScr ⟨70 + r.val, by omega⟩ :=
                    congrArg rScr.wires (Fin.ext (by dsimp [rRow70, p2dSubReg]))
                  exact hMS.ne j ⟨70 + r.val, by omega⟩ (hr.symm.trans hr')
              rw [eval_seq_mulVec,
                  cLoad4Rows218Into_eval_ket hm j rCore rScr rRow70 hCS hBuf β hRow0 hPar0 (s₀.val %
                    64) hl₀ hLo,
                  cSelectHoldKick1Wire_eval_ket hm rScr wOut wMeas hSW hMW α₁ hα₁_out (s₀.val /
                    64) hh₀ hα₁_hi]
              have hActVal : α₁ (rRow70 ⟨s₀.val / 64, hh₀⟩) = β (rElecSlot rCore s₀ j) := by
                dsimp only [α₁]
                rw [p2d_writeReg_apply_reg]
                exact rowBit218_at_active rCore j β s₀
              rw [hActVal, hα₁_meas,
                  ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
                  uKick1Bit218_mulVec_ket, Matrix.mulVec_smul,
                  uHold1WireBit_mulVec_ket, hold1WireMap_eq_update_of_zero rCore wOut j hOut0,
                  Matrix.mulVec_smul, uHold1Bit_mulVec_ket]
              let β' := Function.update β wOut (β (rElecSlot rCore s₀ j))
              have hβ'_row0 : ∀ r : Fin 4, β' (rRow70 r) = 0 := fun r ↦ by
                have hr' : rRow70 r = rScr ⟨70 + r.val, by omega⟩ :=
                  congrArg rScr.wires (Fin.ext (by dsimp [rRow70, p2dSubReg]))
                exact (Function.update_of_ne (hr' ▸ hSW ⟨70 + r.val, by omega⟩) _ _).trans (hRow0 r)
              have hβ'_core : (fun w ↦ β' (rCore w)) = fun w ↦ β (rCore w) :=
                funext fun w ↦ Function.update_of_ne (hCW w) _ _
              have hβ'_slot : shiftedPartnerSlotFast (fun w ↦ β' (rCore w)) = s₀ :=
                congrArg shiftedPartnerSlotFast hβ'_core
              have hβ'_vals : rowBit218 rCore j β' ((shiftedPartnerSlotFast (fun w ↦
                β' (rCore w))).val % 64) = vals := by
                funext r
                rw [hβ'_slot]
                exact rowBit218_congr_elec rCore j
                  (fun e ↦
                    Function.update_of_ne (by
                      dsimp only [rElecSlot,
                        QRegister.slice_apply]; exact hCW _) _ _) _ r
              rw [hold1BitMap_eq_writeReg_of_zero rCore rRow70 j hβ'_row0, hβ'_vals]
              refine congrArg (fun x ↦
                ((-1 : ℂ) ^ (β (rElecSlot rCore s₀ j) * β wMeas).val) • ket x) (funext fun w ↦ ?_)
              dsimp only [α₁, β']
              by_cases hwOut : w = wOut
              · subst w
                have hnm : wOut ∉ Set.range rRow70.wires := fun ⟨r, hr⟩ ↦ by
                  have hr' : rRow70 r = rScr ⟨70 + r.val, by omega⟩ :=
                    congrArg rScr.wires (Fin.ext (by dsimp [rRow70, p2dSubReg]))
                  exact hSW ⟨70 + r.val, by omega⟩ (hr'.symm.trans hr)
                rw [Function.update_self, p2d_writeReg_apply_of_not_mem _ _ _ _ hnm,
                    Function.update_self]
              · rw [Function.update_of_ne hwOut]
                by_cases hwR : w ∈ Set.range rRow70.wires
                · obtain ⟨r, rfl⟩ := hwR
                  rw [p2d_writeReg_apply_reg, p2d_writeReg_apply_reg]
                · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hwR,
                      p2d_writeReg_apply_of_not_mem _ _ _ _ hwR,
                      Function.update_of_ne hwOut]
        rw [hEq]
        dsimp only [R_step]
        rw [Matrix.mul_assoc (uHold1Bit rCore rRow70 j hBuf.1).1,
            Matrix.mul_assoc (uHold1WireBit rCore wOut j hCW).1]
      have hSuppKickPrev : SupportedOn (fun β ↦ (∀ r : Fin 4, β (rRow70 r) = 0) ∧
          InvHoleBase218 hm rCore rScr β) ((uKick1Bit218 j rCore rMeas).1 * R_prev) :=
        supportedOn_diagSignUnitary_mul _ (supportedOn_mono (fun _ h ↦ h.2) hSuppPrev)
      have hSuppStep : SupportedOn (fun β ↦ (∀ r : Fin 4, β (rRow70 r) = 0) ∧
          InvHoleBase218 hm rCore rScr β) R_step := by
        dsimp only [R_step]
        refine supportedOn_unitary_mul _ _ (uHold1WireBit_mulVec_ket rCore wOut j hCW)
          (fun β ⟨hRow0, hBase⟩ ↦ ⟨fun r ↦ ?_, ?_⟩) hSuppKickPrev
        · have hr' : rRow70 r = rScr ⟨70 + r.val, by omega⟩ :=
            congrArg rScr.wires (Fin.ext (by dsimp [rRow70, p2dSubReg]))
          exact (Function.update_of_ne (hr' ▸ hSW ⟨70 + r.val, by omega⟩) _ _).trans (hRow0 r)
        · have hCore : (fun w ↦ hold1WireMap rCore wOut j β (rCore w)) = fun w ↦ β (rCore w) :=
            funext fun w ↦ Function.update_of_ne (hCW w) _ _
          have hScr : ∀ s : Fin mScr, hold1WireMap rCore wOut j β (rScr s) = β (rScr s) :=
            fun s ↦ Function.update_of_ne (hSW s) _ _
          dsimp only [InvHoleBase218] at hBase ⊢
          rw [hCore]
          exact ⟨fun l ↦ (hScr ⟨l.val, by omega⟩).trans (hBase.1 l),
            fun h ↦ (hScr ⟨64 + h.val, by omega⟩).trans (hBase.2.1 h),
            (hScr ⟨69, by omega⟩).trans hBase.2.2.1,
            (hScr ⟨74, by omega⟩).trans hBase.2.2.2⟩
      have s2 := subspaceStep_dUncompute4Rows218 hm v j rCore rScr rRow70 hCS hBuf.1 hSuppStep
      refine subspaceStep_congr_out (ih.seq (s1.seq s2)) ?_
      dsimp only [R_step, R_prev, uHold1WirePrefix, j]
      rw [uKickPrefix218_succ]
      have hComm := uHold1WirePrefix_comm_uKick1Bit218 K hK rCore rMeas rHeld hCH hMH
        ⟨k, by omega⟩ k (by omega)
      calc (uHold1WireBit rCore wOut ⟨k, by omega⟩ hCW).1 *
            ((uKick1Bit218 ⟨k, by omega⟩ rCore rMeas).1 *
              ((uHold1WirePrefix K hK rCore rHeld hCH k (by omega) *
                uKickPrefix218 k (by omega) rCore rMeas).1 * R))
          = (uHold1WireBit rCore wOut ⟨k, by omega⟩ hCW *
              (uKick1Bit218 ⟨k, by omega⟩ rCore rMeas *
                uHold1WirePrefix K hK rCore rHeld hCH k (by omega)) *
              uKickPrefix218 k (by omega) rCore rMeas).1 * R := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = ((uHold1WireBit rCore wOut ⟨k, by omega⟩ hCW *
              uHold1WirePrefix K hK rCore rHeld hCH k (by omega)) *
              (uKick1Bit218 ⟨k, by omega⟩ rCore rMeas *
                uKickPrefix218 k (by omega) rCore rMeas)).1 * R := by
              rw [← hComm]; simp only [mul_assoc]

-- ============================================================================
-- Section 5: Public Wrapper & Projector Algebra Helpers
-- ============================================================================

private theorem uFwdFast_comm_uHold1WireBit {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (wOut : Wire n)
    (hCS : rCore.DisjointWires rScr)
    (hCW : ∀ w : Wire posCoreWires, rCore w ≠ wOut)
    (hSW : ∀ s : Fin mScr, rScr s ≠ wOut) (j : Fin 18) :
    uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast * uHold1WireBit rCore wOut j hCW =
      uHold1WireBit rCore wOut j hCW * uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast :=
        by
  let rComb := rComb133 hm rCore rScr hCS
  have hwNotComb : wOut ∉ Set.range rComb.wires := by
    rintro ⟨idx, hidx⟩
    by_cases hlt : idx.val < 17
    · rw [rComb133_apply_lt hm rCore rScr hCS idx hlt] at hidx
      dsimp only [rShiftedIdx17Core, QRegister.compose_apply] at hidx
      exact hCW _ hidx
    · rw [rComb133_apply_ge hm rCore rScr hCS idx (by omega)] at hidx
      exact hSW _ hidx
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      uHold1WireBit_mulVec_ket, uFwdWG_mulVec_ket, uFwdWG_mulVec_ket, uHold1WireBit_mulVec_ket]
  let αH := hold1WireMap rCore wOut j β
  let αF := fwdFastBits hm rCore rScr hCS β
  change ket (fwdFastBits hm rCore rScr hCS αH) = ket (hold1WireMap rCore wOut j αF)
  have hCombH : (fun idx ↦ αH (rComb idx)) = fun idx ↦ β (rComb idx) :=
    funext fun idx ↦ Function.update_of_ne (fun h ↦ hwNotComb ⟨idx, h⟩) _ _
  have hCoreF : (fun w ↦ αF (rCore w)) = fun w ↦ β (rCore w) :=
    funext fun w ↦ fwdFastBits_outside_scr116 hm rCore rScr hCS β (rCore w) fun k ↦ hCS.ne w _
  have hSlotF : shiftedPartnerSlotFast (fun w ↦ αF (rCore w)) =
      shiftedPartnerSlotFast (fun w ↦ β (rCore w)) := congrArg shiftedPartnerSlotFast hCoreF
  have hElecF : ∀ e : Fin 218, αF (rElecSlot rCore e j) = β (rElecSlot rCore e j) := fun e ↦
    fwdFastBits_outside_scr116 hm rCore rScr hCS β _ fun k ↦ by
      dsimp only [rElecSlot, QRegister.slice_apply]
      exact hCS.ne _ _
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : w = wOut
  · subst w
    rw [fwdFastBits_outside_scr116 hm rCore rScr hCS αH wOut (fun k ↦ (hSW _).symm)]
    dsimp only [αH, hold1WireMap]
    rw [Function.update_self, Function.update_self, hSlotF, hElecF]
    dsimp only [αF]
    rw [fwdFastBits_outside_scr116 hm rCore rScr hCS β wOut (fun k ↦ (hSW _).symm)]
  · rw [show hold1WireMap rCore wOut j αF w = αF w from Function.update_of_ne hw _ _]
    dsimp only [αF, fwdFastBits]
    by_cases hwC : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hwC
      rw [p2d_writeReg_apply_reg, p2d_writeReg_apply_reg, hCombH]
    · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hwC,
          p2d_writeReg_apply_of_not_mem _ _ _ _ hwC]
      exact Function.update_of_ne hw _ _

private theorem uFwdFast_comm_uHold1WirePrefix {n mScr : ℕ} (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCH : rCore.DisjointWires rHeld) (hCS : rCore.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) :
    ∀ (k : ℕ) (hk : k ≤ K),
      uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast *
        uHold1WirePrefix K hK rCore rHeld hCH k hk =
      uHold1WirePrefix K hK rCore rHeld hCH k hk *
        uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast
  | 0, _ => by dsimp only [uHold1WirePrefix]; rw [mul_one, one_mul]
  | k + 1, hk => by
      dsimp only [uHold1WirePrefix]
      exact unitary_comm_mul _ _ _
        (uFwdFast_comm_uHold1WireBit hm rCore rScr (rHeld ⟨k, hk⟩) hCS
          (fun w ↦ hCH.ne w ⟨k, hk⟩) (fun s ↦ (hHS.ne ⟨k, hk⟩ s).symm) ⟨k, by omega⟩)
        (uFwdFast_comm_uHold1WirePrefix K hK hm rCore rHeld rScr hCH hCS hHS k (by omega))

private theorem uHold1WireBit_comm_embed_uMid {n kData : ℕ}
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (wOut : Wire n) (j : Fin 18)
    (hDM : rData.DisjointWires rMeas)
    (hDW : ∀ d : Fin kData, rData d ≠ wOut)
    (hMW : ∀ m : Fin 18, rMeas m ≠ wOut)
    {uMid : Unitary (2 ^ (kData + 18))}
    (hElec : Elec3924Preserved selCore uMid)
    (hPres17 : ActPreservesShifted17 selCore uMid) :
    uHold1WireBit (rData.compose selCore) wOut j (fun w ↦ hDW (selCore w)) *
        (rData.concat rMeas hDM).embedUnitary uMid =
      (rData.concat rMeas hDM).embedUnitary uMid *
        uHold1WireBit (rData.compose selCore) wOut j (fun w ↦ hDW (selCore w)) := by
  let rCore := rData.compose selCore
  let rAct := rData.concat rMeas hDM
  let hCW : ∀ w : Wire posCoreWires, rCore w ≠ wOut := fun w ↦ hDW (selCore w)
  let rW : QRegister 1 n := ⟨⟨fun _ ↦ wOut, fun _ _ _ ↦ Subsingleton.elim _ _⟩⟩
  have hAW_disj : rAct.DisjointWires rW :=
    disjointWires_concat_left hDM
      (QRegister.disjoint_iff.mpr fun d _ ↦ hDW d)
      (QRegister.disjoint_iff.mpr fun m _ ↦ hMW m)
  have hAW : ∀ u : Fin (kData + 18), rAct u ≠ wOut := fun u ↦ hAW_disj.ne u 0
  have hD : rAct.compose (selDataInAct kData) = rData :=
    concat_compose_selDataInAct rData rMeas hDM
  let σ := hold1WireEquiv rCore wOut j hCW
  have hσ_inv : ∀ x : Fin (2 ^ n), σ (σ x) = x := fun x ↦ by
    dsimp only [σ, hold1WireEquiv]
    rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply]
    have h1 : basisBits n ((basisBitsEquiv n).symm (hold1WireMap rCore wOut j (basisBits n x))) =
        hold1WireMap rCore wOut j (basisBits n x) := (basisBitsEquiv n).apply_symm_apply _
    rw [h1, hold1WireMap_involutive rCore wOut j hCW]
    exact (basisBitsEquiv n).symm_apply_apply x
  have hσ_bits : ∀ x : Fin (2 ^ n), basisBits n (σ x) = hold1WireMap rCore wOut j (basisBits n x) :=
    fun x ↦
      by dsimp only [σ,
      hold1WireEquiv]; rw [Equiv.ofBijective_apply]; exact (basisBitsEquiv n).apply_symm_apply _
  have hσ_ext : ∀ x : Fin (2 ^ n), rAct.extractIndex (σ x) = rAct.extractIndex x := fun x ↦ by
    apply basisBits_inj; intro u
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hσ_bits]
    exact Function.update_of_ne (hAW u) _ _
  apply Subtype.ext; ext i g
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  have hL : ((uHold1WireBit rCore wOut j hCW).1 * (rAct.embedUnitary uMid).1) i g =
      (rAct.embedUnitary uMid).1 (σ i) g := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
    · dsimp only [uHold1WireBit]; rw [permUnitary_apply, ite_eq_left (hσ_inv i).symm, one_mul]
    · intro m _ hm; dsimp only [uHold1WireBit]
      rw [permUnitary_apply, ite_eq_right (fun h ↦
        hm (by change i = σ m at h; rw [h, hσ_inv])), zero_mul]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  have hR : ((rAct.embedUnitary uMid).1 * (uHold1WireBit rCore wOut j hCW).1) i g =
      (rAct.embedUnitary uMid).1 i (σ g) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ g)]
    · dsimp only [uHold1WireBit]; rw [permUnitary_apply, ite_eq_left rfl, mul_one]
    · intro m _ hm; dsimp only [uHold1WireBit]; rw [permUnitary_apply, ite_eq_right hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  rw [hL, hR, QRegister.embedUnitary_val, QRegister.embedMatrix_apply,
      QRegister.embedMatrix_apply, hσ_ext i, hσ_ext g]
  by_cases hnz : uMid.1 (rAct.extractIndex i) (rAct.extractIndex g) = 0
  · simp [hnz]
  · have hBitEq :
        basisBits n i (rElecSlot rCore (shiftedPartnerSlotFast (fun w ↦
          basisBits n i (rCore w))) j) =
        basisBits n g (rElecSlot rCore (shiftedPartnerSlotFast (fun w ↦
          basisBits n g (rCore w))) j) := by
      have h17 := hPres17 (rAct.extractIndex g) (rAct.extractIndex i) hnz
      have h17Wire : ∀ (x : Fin (2 ^ n)) (idx : Fin 17),
          basisBits 17 ((selShiftedIdx17 selCore).extractIndex
            ((selDataInAct kData).extractIndex (rAct.extractIndex x))) idx =
            basisBits n x (rCore (rShiftedIdx17OfFin idx)) := fun x idx ↦ by
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
            QRegister.basisBits_extractIndex]
        refine congrArg (basisBits n x) ?_
        dsimp only [selShiftedIdx17, QRegister.compose_apply, rCore]
        exact congrArg (fun reg : QRegister kData n ↦ reg (selCore (rShiftedIdx17OfFin idx))) hD
      have h17Bits : ∀ idx : Fin 17,
          basisBits n i (rCore (rShiftedIdx17OfFin idx)) =
            basisBits n g (rCore (rShiftedIdx17OfFin idx)) := fun idx ↦ by
        rw [← h17Wire i idx, ← h17Wire g idx, h17]
      have hSlotEq : shiftedPartnerSlotFast (fun w ↦ basisBits n i (rCore w)) =
          shiftedPartnerSlotFast (fun w ↦ basisBits n g (rCore w)) := by
        refine shiftedPartnerSlotFast_congr ?_ (fun a ↦ ?_) (fun b ↦ ?_)
        · have h0 := h17Bits ⟨0, by decide⟩; rwa [rShiftedIdx17OfFin_zero] at h0
        · have ha := h17Bits ⟨1 + a.val, by
          have :=
            a.isLt; omega⟩; rwa [rShiftedIdx17OfFin_anc a] at ha
        · have hb := h17Bits ⟨9 + b.val, by
          have :=
            b.isLt; omega⟩; rwa [rShiftedIdx17OfFin_part b] at hb
      rw [hSlotEq]
      let e := shiftedPartnerSlotFast (fun w ↦ basisBits n g (rCore w))
      have hEWire : ∀ x : Fin (2 ^ n),
          basisBits (kData + 18) (rAct.extractIndex x)
            (rElecInAct selCore ⟨18 * e.val + j.val, by have := e.isLt; have := j.isLt; omega⟩) =
          basisBits n x (rElecSlot rCore e j) := fun x ↦ by
        rw [QRegister.basisBits_extractIndex]
        refine congrArg (basisBits n x) ?_
        rw [rElecSlot_eq_rElec3924]
        dsimp only [rElecInAct, QRegister.compose_apply, rCore, rElec3924, QRegister.slice_apply]
        exact congrArg (fun reg : QRegister kData n ↦ reg _) hD
      rw [← hEWire i, ← hEWire g]
      exact hElec.2 _ _ _ hnz
    have hEnvIff : ((rAct.basisSplitEquiv (σ i)).2 = (rAct.basisSplitEquiv g).2) ↔
        ((rAct.basisSplitEquiv i).2 = (rAct.basisSplitEquiv (σ g)).2) := by
      rw [rAct.basisSplit_environment_eq_iff, rAct.basisSplit_environment_eq_iff]
      refine forall_congr' fun w ↦ imp_congr_right fun hw ↦ ?_
      rw [hσ_bits i, hσ_bits g]
      by_cases hwOut : w = wOut
      · subst hwOut
        dsimp only [hold1WireMap]
        rw [Function.update_self, Function.update_self, hBitEq]
        exact zmod2_add_eq_iff _ _ _
      · dsimp only [hold1WireMap]
        rw [Function.update_of_ne hwOut, Function.update_of_ne hwOut]
    by_cases h1 : (rAct.basisSplitEquiv (σ i)).2 = (rAct.basisSplitEquiv g).2
    · rw [ite_eq_left h1, ite_eq_left (hEnvIff.mp h1)]
    · rw [ite_eq_right h1, ite_eq_right (mt hEnvIff.mpr h1)]

theorem uHold1WirePrefix_comm_embed_uMid {n kData : ℕ}
    (K : ℕ) (hK : K ≤ 18)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hMH : rMeas.DisjointWires rHeld)
    {uMid : Unitary (2 ^ (kData + 18))}
    (hElec : Elec3924Preserved selCore uMid)
    (hPres17 : ActPreservesShifted17 selCore uMid) :
    ∀ (k : ℕ) (hk : k ≤ K),
      uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) k hk *
          (rData.concat rMeas hDM).embedUnitary uMid =
        (rData.concat rMeas hDM).embedUnitary uMid *
          uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) k hk
  | 0, _ => by dsimp only [uHold1WirePrefix]; rw [one_mul, mul_one]
  | k + 1, hk => by
      dsimp only [uHold1WirePrefix]
      exact (unitary_comm_mul ((rData.concat rMeas hDM).embedUnitary uMid) _ _
        (uHold1WireBit_comm_embed_uMid rData selCore rMeas (rHeld ⟨k, hk⟩)
          ⟨k, by omega⟩ hDM (fun d ↦ hDH.ne d ⟨k, hk⟩) (fun m ↦ hMH.ne m ⟨k, hk⟩)
          hElec hPres17).symm
        (uHold1WirePrefix_comm_embed_uMid K hK rData selCore rMeas rHeld hDM hDH hMH
          hElec hPres17 k (by omega)).symm).symm

theorem basisOutcomeProjector_zero_comm {n k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) :
    r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 * r₁.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)

theorem basisOutcomeProjector_zero_idem {n k : ℕ} (r : QRegister k n) :
    r.basisOutcomeProjector 0 * r.basisOutcomeProjector 0 = r.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  by_cases h : r.extractIndex x = 0 <;> simp [h]

private theorem supportedOn_of_basisOutcomeProjector_zero_mul {n k : ℕ}
    (r : QRegister k n) {R : Operator (2 ^ n)}
    (h : r.basisOutcomeProjector 0 * R = R) :
    SupportedOn (fun β ↦ ∀ i : Fin k, β (r i) = 0) R := by
  rw [← h]
  exact supportedOn_mul_right (supportedOn_basisOutcomeProjector_zero r) R

private theorem basisOutcomeProjector_zero_comm_of_ket_map {n k : ℕ}
    (r : QRegister k n) (U : Operator (2 ^ n))
    (F : BitAssignment n → BitAssignment n)
    (hU : ∀ β, U.mulVec (ket β) = ket (F β))
    (hFix : ∀ β (i : Fin k), F β (r i) = β (r i)) :
    r.basisOutcomeProjector 0 * U = U * r.basisOutcomeProjector 0 := by
  rw [p2d_basisOutcomeProjector_zero_eq_ketPredProj]
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hU β,
      p2d_ketPredProj_mul_ket, p2d_ketPredProj_mul_ket]
  simp only [hFix β]
  by_cases h0 : ∀ i : Fin k, β (r i) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, hU β]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]

private theorem basisOutcomeProjector_zero_comm_cHadReg {n k m : ℕ}
    (r : QRegister k n) (rH : QRegister m n) (hDisj : r.DisjointWires rH) :
    r.basisOutcomeProjector 0 * (cHadReg rH).eval.1 =
      (cHadReg rH).eval.1 * r.basisOutcomeProjector 0 := by
  rw [p2d_basisOutcomeProjector_zero_eq_ketPredProj]
  exact cHadReg_preserves_ketPredProj rH _ fun β₁ β₂ h ↦
    forall_congr' fun i ↦ by rw [h (r i) fun t ↦ hDisj.ne i t]

private theorem basisOutcomeProjector_zero_comm_uHold1WirePrefix {n mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCH : rCore.DisjointWires rHeld) (hHS : rHeld.DisjointWires rScr) :
    ∀ (k : ℕ) (hk : k ≤ K),
      rScr.basisOutcomeProjector 0 * (uHold1WirePrefix K hK rCore rHeld hCH k hk).1 =
        (uHold1WirePrefix K hK rCore rHeld hCH k hk).1 * rScr.basisOutcomeProjector 0
  | 0, _ => by dsimp only [uHold1WirePrefix]; rw [Submonoid.coe_one, mul_one, one_mul]
  | k + 1, hk => by
      dsimp only [uHold1WirePrefix]
      rw [Submonoid.coe_mul]
      have h1 : rScr.basisOutcomeProjector 0 *
          (uHold1WireBit rCore (rHeld ⟨k, hk⟩) ⟨k, by omega⟩ (fun w ↦ hCH.ne w ⟨k, hk⟩)).1 =
          (uHold1WireBit rCore (rHeld ⟨k, hk⟩) ⟨k, by omega⟩ (fun w ↦ hCH.ne w ⟨k, hk⟩)).1 *
          rScr.basisOutcomeProjector 0 :=
        basisOutcomeProjector_zero_comm_of_ket_map rScr _ _
          (uHold1WireBit_mulVec_ket rCore _ _ _)
          (fun _ s ↦ Function.update_of_ne (hHS.ne ⟨k, hk⟩ s).symm _ _)
      have ih :=
        basisOutcomeProjector_zero_comm_uHold1WirePrefix K hK rCore rHeld rScr hCH hHS k (by omega)
      rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]

theorem basisOutcomeProjector_zero_comm_uFwdFast {n mScr k : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr)
    (r : QRegister k n) (hRS : r.DisjointWires rScr) :
    r.basisOutcomeProjector 0 *
        (uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast).1 =
      (uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast).1 *
        r.basisOutcomeProjector 0 :=
  basisOutcomeProjector_zero_comm_of_ket_map r _ (fwdFastBits hm rCore rScr hCS)
    (uFwdWG_mulVec_ket _ ctxShiftedPartnerFast)
    (fun β i ↦ fwdFastBits_outside_scr116 hm rCore rScr hCS β (r i) fun _ ↦ hRS.ne i _)

theorem subspaceStep_of_realizesCleanWorkspace
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kAct mScr : ℕ} [NeZero (2 ^ n)]
    (rAct : QRegister kAct n) (rScr : QRegister mScr n)
    (u : Unitary (2 ^ kAct)) (d : DynamicCircuit Var n)
    (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rScr u d)
    {R : Operator (2 ^ n)} (hPs : rScr.basisOutcomeProjector 0 * R = R) :
    SubspaceStep R ((rAct.embedUnitary u).1 * R) d := by
  let Ps := rScr.basisOutcomeProjector 0
  have hBase : SubspaceStep Ps ((rAct.embedUnitary u).1 * Ps) d := fun M ↦ by
    obtain ⟨M', hwp, hEq⟩ := hd M
    refine ⟨M', hwp, ?_⟩
    rw [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose rScr 0]
    simpa only [Matrix.mul_assoc] using hEq.symm
  have hMul := MultiBankWStateRouter.subspaceStep_mul_right R hBase
  rwa [hPs, Matrix.mul_assoc, hPs] at hMul

theorem realizesCleanWorkspace_of_subspaceStep
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kAct mWork : ℕ} [NeZero (2 ^ n)]
    (rAct : QRegister kAct n) (rWork : QRegister mWork n)
    (u : Unitary (2 ^ kAct)) (d : DynamicCircuit Var n)
    (h : SubspaceStep (rWork.basisOutcomeProjector 0)
      ((rAct.embedUnitary u).1 * rWork.basisOutcomeProjector 0) d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d := fun M ↦ by
  obtain ⟨M', hwp, hEq⟩ := h M
  refine ⟨M', hwp, ?_⟩
  rw [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose rWork 0] at hEq
  simpa only [Matrix.mul_assoc] using hEq.symm

theorem supportedOn_invHeld1wHole_of_perm_pres17 {n kData mScr K : ℕ}
    (hm : 75 ≤ mScr)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) (hMS : rMeas.DisjointWires rScr)
    (σ : Equiv.Perm (Fin (2 ^ (kData + 18))))
    (hPres : ActPreservesShifted17 selCore (Operator.permutationUnitary σ))
    {R : Operator (2 ^ n)}
    (hSupp : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
      InvHoleShifted218 hm (rData.compose selCore) rScr β) R) :
    SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
      InvHoleShifted218 hm (rData.compose selCore) rScr β)
      (((rData.concat rMeas hDM).embedUnitary (Operator.permutationUnitary σ)).1 * R) := by
  let rCore := rData.compose selCore
  let rAct := rData.concat rMeas hDM
  have hAH : rAct.DisjointWires rHeld := disjointWires_concat_left hDM hDH hMH
  have hAS : rAct.DisjointWires rScr := disjointWires_concat_left hDM hDS hMS
  have hD : rAct.compose (selDataInAct kData) = rData := concat_compose_selDataInAct rData rMeas hDM
  let F : BitAssignment n → BitAssignment n := fun β ↦
    let g := (basisBitsEquiv n).symm β
    basisBits n (rAct.replaceIndex g (σ (rAct.extractIndex g)))
  have hKet : ∀ β,
    (rAct.embedUnitary (Operator.permutationUnitary σ)).1.mulVec (ket β) = ket (F β) :=
    fun β ↦ by
      rw [p2d_ket_eq_single β, embedUnitary_permutationUnitary_mulVec_single,
        p2d_ket_eq_single (F β)]
      refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
      exact ((basisBitsEquiv n).symm_apply_apply _).symm
  refine supportedOn_unitary_mul _ F hKet (fun β ⟨hH0, hInv⟩ ↦ ?_) hSupp
  let g := (basisBitsEquiv n).symm β
  have hgβ : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  have hF_out : ∀ w, w ∉ Set.range rAct.wires → F β w = β w := fun w hw ↦ by
    dsimp only [F]; rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ w hw, hgβ]
  have hH' : ∀ i : Fin K, F β (rHeld i) = 0 :=
    fun i ↦ (hF_out (rHeld i) fun ⟨u, hu⟩ ↦ hAH.ne u i hu).trans (hH0 i)
  have hS' : ∀ s : Fin mScr, F β (rScr s) = β (rScr s) :=
    fun s ↦ hF_out (rScr s) fun ⟨u, hu⟩ ↦ hAS.ne u s hu
  have hSub' : ∀ r : Fin 4,
      F β (p2dSubReg rScr 70 4 (by omega) r) = β (p2dSubReg rScr 70 4 (by omega) r) :=
    fun r ↦ hS' ⟨70 + r.val, by omega⟩
  have hnz : (Operator.permutationUnitary σ).1 (σ (rAct.extractIndex g)) (rAct.extractIndex g) ≠ 0
    := by
    rw [permUnitary_apply, ite_eq_left rfl]; exact one_ne_zero
  have h17 := hPres (rAct.extractIndex g) (σ (rAct.extractIndex g)) hnz
  have h17Wire : ∀ (x : Fin (2 ^ n)) (idx : Fin 17),
      basisBits 17 ((selShiftedIdx17 selCore).extractIndex
        ((selDataInAct kData).extractIndex (rAct.extractIndex x))) idx =
        basisBits n x (rCore (rShiftedIdx17OfFin idx)) := fun x idx ↦ by
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        QRegister.basisBits_extractIndex]
    refine congrArg (basisBits n x) ?_
    dsimp only [selShiftedIdx17, QRegister.compose_apply, rCore]
    exact congrArg (fun reg : QRegister kData n ↦ reg (selCore (rShiftedIdx17OfFin idx))) hD
  have h17Bits : ∀ idx : Fin 17,
      F β (rCore (rShiftedIdx17OfFin idx)) = β (rCore (rShiftedIdx17OfFin idx)) := fun idx ↦ by
    dsimp only [F]
    rw [← h17Wire (rAct.replaceIndex g (σ (rAct.extractIndex g))) idx,
        QRegister.extractIndex_replaceIndex, h17, h17Wire g idx, hgβ]
  have hSlot' : shiftedPartnerSlotFast (fun w ↦ F β (rCore w)) =
      shiftedPartnerSlotFast (fun w ↦ β (rCore w)) := by
    refine shiftedPartnerSlotFast_congr ?_ (fun a ↦ ?_) (fun b ↦ ?_)
    · have h0 := h17Bits ⟨0, by decide⟩; rwa [rShiftedIdx17OfFin_zero] at h0
    · have ha := h17Bits ⟨1 + a.val, by have := a.isLt; omega⟩; rwa [rShiftedIdx17OfFin_anc a] at ha
    · have hb := h17Bits ⟨9 + b.val, by
      have :=
        b.isLt; omega⟩; rwa [rShiftedIdx17OfFin_part b] at hb
  refine ⟨hH', ?_⟩
  dsimp only [rCore] at hSlot'
  dsimp only [InvHoleShifted218] at hInv ⊢
  simp only [hSlot', hS', hSub']
  exact hInv

theorem invHeld1wHole_ignores_elec3924 {n mScr K : ℕ} (hm : 75 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCH : rCore.DisjointWires rHeld) (hCS : rCore.DisjointWires rScr)
    (β₁ β₂ : BitAssignment n)
    (h : ∀ w, (∀ t : Fin 3924, w ≠ rElec3924 rCore t) → β₁ w = β₂ w) :
    ((∀ i : Fin K, β₁ (rHeld i) = 0) ∧ InvHoleShifted218 hm rCore rScr β₁) ↔
      ((∀ i : Fin K, β₂ (rHeld i) = 0) ∧ InvHoleShifted218 hm rCore rScr β₂) := by
  have hH : ∀ i : Fin K, β₁ (rHeld i) = β₂ (rHeld i) := fun i ↦
    h (rHeld i) fun t ht ↦ by
      dsimp only [rElec3924, QRegister.slice_apply] at ht
      exact hCH.ne _ i ht.symm
  have hS : ∀ s : Fin mScr, β₁ (rScr s) = β₂ (rScr s) := fun s ↦
    h (rScr s) fun t ht ↦ by
      dsimp only [rElec3924, QRegister.slice_apply] at ht
      exact hCS.ne _ s ht.symm
  have hSub : ∀ r : Fin 4,
      β₁ (p2dSubReg rScr 70 4 (by omega) r) = β₂ (p2dSubReg rScr 70 4 (by omega) r) :=
    fun r ↦ hS ⟨70 + r.val, by omega⟩
  have hSlot : shiftedPartnerSlotFast (fun w ↦ β₁ (rCore w)) =
      shiftedPartnerSlotFast (fun w ↦ β₂ (rCore w)) :=
    shiftedPartnerSlotFast_congr_outside fun w hwLo _ ↦
      h (rCore w) fun t ht ↦ by
        dsimp only [rElec3924, QRegister.slice_apply] at ht
        have hv := congrArg Fin.val (rCore.wires.injective ht)
        dsimp only at hv; have := t.isLt; omega
  dsimp only [InvHoleShifted218]
  simp only [hH, hS, hSub, hSlot]

theorem validAt_ctxFast_of_scr_projZero {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr)
    {R : Operator (2 ^ n)} (hPs : rScr.basisOutcomeProjector 0 * R = R) :
    SupportedOn (fun β ↦ ctxShiftedPartnerFast.ValidAt
      (fun idx ↦ β (rComb133 hm rCore rScr hCS idx))) R :=
  supportedOn_mono
    (fun β h0 ↦ (ctxShiftedPartnerFast_spec _
      ((scr_zero_iff_cleanScr116 hm rCore rScr hCS β).mp h0).2).1)
    (supportedOn_of_basisOutcomeProjector_zero_mul rScr hPs)

theorem supportedOn_invHeld1wHole_uFwdFast {n mScr K : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hHS : rHeld.DisjointWires rScr)
    {R : Operator (2 ^ n)}
    (hPh : rHeld.basisOutcomeProjector 0 * R = R)
    (hPs : rScr.basisOutcomeProjector 0 * R = R) :
    SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
      InvHoleShifted218 (by omega : 75 ≤ mScr) rCore rScr β)
      ((uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast).1 * R) := by
  have hSupp0 : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
      (∀ k : Fin mScr, β (rScr k) = 0)) R :=
    supportedOn_and
      (supportedOn_of_basisOutcomeProjector_zero_mul rHeld hPh)
      (supportedOn_of_basisOutcomeProjector_zero_mul rScr hPs)
  refine supportedOn_unitary_mul
    (uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast)
    (fwdFastBits hm rCore rScr hCS)
    (uFwdWG_mulVec_ket (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast)
    (fun β ⟨hH0, hS0⟩ ↦ ?_) hSupp0
  let α := fwdFastBits hm rCore rScr hCS β
  have hHα : ∀ i : Fin K, α (rHeld i) = 0 := fun i ↦
    (fwdFastBits_outside_scr116 hm rCore rScr hCS β (rHeld i) fun _ ↦ hHS.ne i _).trans (hH0 i)
  have hClean : CleanScr116 (fun idx ↦ β (rComb133 hm rCore rScr hCS idx)) :=
    ((scr_zero_iff_cleanScr116 hm rCore rScr hCS β).mp hS0).2
  have hInvFast : InvShifted64x4Fast (fun idx ↦ α (rComb133 hm rCore rScr hCS idx)) := by
    have hEq : (fun idx ↦ α (rComb133 hm rCore rScr hCS idx)) =
        ctxShiftedPartnerFast.fwdBits (fun idx ↦ β (rComb133 hm rCore rScr hCS idx)) :=
      funext fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx
    rw [hEq]
    exact (ctxShiftedPartnerFast_spec _ hClean).2
  exact ⟨hHα, invHoleShifted218_of_invShifted64x4Fast hm rCore rScr hCS α hInvFast⟩

private theorem proj_comm_three_mul {m : Type*} [Fintype m]
    (P A B C : Matrix m m ℂ)
    (hA : P * A = A * P) (hB : P * B = B * P) (hC : P * C = C * P) :
    P * (A * B * C) = (A * B * C) * P := by
  rw [← Matrix.mul_assoc P (A * B) C, ← Matrix.mul_assoc P A B, hA,
      Matrix.mul_assoc A P B, hB, ← Matrix.mul_assoc A B P,
      Matrix.mul_assoc (A * B) P C, hC, ← Matrix.mul_assoc (A * B) C P]

theorem scr_projZero_comm_uPreTarget1w {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    rScr.basisOutcomeProjector 0 *
        (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
          (cHadReg (rElec3924 (rData.compose selCore))).eval *
          (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 =
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
          (cHadReg (rElec3924 (rData.compose selCore))).eval *
          (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        rScr.basisOutcomeProjector 0 := by
  have hSE : rScr.DisjointWires (rElec3924 (rData.compose selCore)) := by
    rw [QRegister.disjoint_iff]
    intro s i h
    rw [rElec3924, QRegister.slice_apply] at h
    exact (hDS.compose_left selCore).ne _ s h.symm
  have hAS : (rData.concat rMeas hDM).DisjointWires rScr := disjointWires_concat_left hDM hDS hMS
  have h1 :=
    basisOutcomeProjector_zero_comm_uHold1WirePrefix K hK (rData.compose selCore) rHeld rScr
    (hDH.compose_left selCore) hHS K le_rfl
  have h2 := basisOutcomeProjector_zero_comm_cHadReg rScr (rElec3924 (rData.compose selCore)) hSE
  have h3 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rData.concat rMeas hDM)) rScr hAS
    (uLensSwap (shiftedPartnerLens218 selCore)).1 0).symm
  rw [Submonoid.coe_mul, Submonoid.coe_mul, QRegister.embedUnitary_val]
  exact proj_comm_three_mul _ _ _ _ h1 h2 h3

theorem uFwdFast_comm_uPreTarget1w {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    uFwdWG (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
        ctxShiftedPartnerFast *
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))) =
    (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))) *
      uFwdWG (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
        ctxShiftedPartnerFast := by
  have h1 := uFwdFast_comm_uHold1WirePrefix K hK hm (rData.compose selCore) rHeld rScr
    (hDH.compose_left selCore) (hDS.compose_left selCore) hHS K le_rfl
  have h2 := (uFwdFast_comm_cHadReg_elec hm (rData.compose selCore) rScr
    (hDS.compose_left selCore)).symm
  have h3 := uFwdFast_comm_uLensSwap hm rData selCore rMeas rScr hDM hDS hMS
  exact unitary_comm_mul _ _ _ (unitary_comm_mul _ _ _ h1 h2) h3


attribute [irreducible] cSelectHoldKick1Wire dPre1WireLoadAux

end StageBOneWireCore

end
end StageBOneWireCore

noncomputable section StageBOneWireHeld
set_option allowUnsafeReducibility true

section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 256

namespace StageBOneWireHeld
set_option exponentiation.threshold 256

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instNeZeroTwoPow1wHeld (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Real HermitianMat
open SpecsAux.SpecMirror
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF T
open PrimitiveGate (TOFF T)
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket bitSign sqrtHalf bit_cases ket_H matrix_ext_ket)
open FullSysCatSegmentBridge (disjointWires_concat_left)
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_neg dite_pos
open PosSlots24Barrel3Pass
open AnchorSwap0Split133
open MultiBankWStateRouter
open ParticleOneHotWState
open BoothOpt_StageBPartnerCoreShave
  (DiagCtxWG DiagCtxWGWritesAbove ctxShiftedPartnerFast ctxShiftedPartnerFast_countT
   ctxShiftedPartnerFast_writesAbove ctxShiftedPartnerFast_spec InvHoleShifted218
   rShiftedIdx17OfFin rShiftedIdx17Core rShiftedIdx17OfFin_zero rShiftedIdx17OfFin_anc
   rShiftedIdx17OfFin_part rComb133 rComb133_apply_lt rComb133_apply_ge CleanScr116
   InvShifted64x4Fast scr_zero_iff_cleanScr116 invHoleShifted218_of_invShifted64x4Fast
   selShiftedIdx17 actPreservesShifted17_to_comb133Pres wSlot1Core_ofFin_val
   rAnchorIdx_ofFin_val_local rPartnerIdx_ofFin_val_local rElecSlot_ofFin_val_local
   shiftedPartnerSlotFast_congr shiftedPartnerSlotFast_congr_outside)
open BoothOpt_P4_10_TwoLoadHeldRowTrueSwap
open StageBOneWireCore

attribute [local irreducible] ctxShiftedPartnerFast shiftedPartnerLens218

private theorem supportedOn_uHold1WirePrefix_full {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n)
    (hCH : rCore.DisjointWires rHeld)
    {P : BitAssignment n → Prop}
    (hP : ∀ β₁ β₂ : BitAssignment n,
      (∀ w, w ∉ Set.range rHeld.wires → β₁ w = β₂ w) → (P β₁ ↔ P β₂))
    {R : Operator (2 ^ n)}
    (hSupp : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧ P β) R) :
    SupportedOn P ((uHold1WirePrefix K hK rCore rHeld hCH K le_rfl).1 * R) :=
  fun A B hAB ↦ by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact hSupp (A * (uHold1WirePrefix K hK rCore rHeld hCH K le_rfl).1)
      (B * (uHold1WirePrefix K hK rCore rHeld hCH K le_rfl).1) fun β ⟨hZero, hPβ⟩ ↦ by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          uHold1WirePrefix_eq_writeReg_of_zero K hK rCore rHeld hCH β hZero]
      exact hAB _ ((hP _ β fun w hw ↦ p2d_writeReg_apply_of_not_mem _ _ _ w hw).mpr hPβ)

private theorem invHoleShifted218_ignores_held1w {n mScr K : ℕ} (hm : 75 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCH : rCore.DisjointWires rHeld) (hHS : rHeld.DisjointWires rScr)
    (β₁ β₂ : BitAssignment n)
    (h : ∀ w, w ∉ Set.range rHeld.wires → β₁ w = β₂ w) :
    InvHoleShifted218 hm rCore rScr β₁ ↔ InvHoleShifted218 hm rCore rScr β₂ := by
  have hCore : (fun w ↦ β₁ (rCore w)) = fun w ↦ β₂ (rCore w) :=
    funext fun w ↦ h (rCore w) fun ⟨i, hi⟩ ↦ hCH.ne w i hi.symm
  have hSlot : shiftedPartnerSlotFast (fun w ↦ β₁ (rCore w)) =
      shiftedPartnerSlotFast (fun w ↦ β₂ (rCore w)) := congrArg shiftedPartnerSlotFast hCore
  have hScr : ∀ s : Fin mScr, β₁ (rScr s) = β₂ (rScr s) :=
    fun s ↦ h (rScr s) fun ⟨i, hi⟩ ↦ hHS.ne i s hi
  have hSub : ∀ r : Fin 4,
      β₁ (p2dSubReg rScr 70 4 (by omega) r) = β₂ (p2dSubReg rScr 70 4 (by omega) r) :=
    fun r ↦ hScr ⟨70 + r.val, by omega⟩
  dsimp only [InvHoleShifted218]
  simp only [hSlot, hScr, hSub]

/-- Pre-pass `.hole` circuit (`15,984 T`, `TOFF = 0`) loading `rMeas`, opening `cHadReg rElec3924`,
loading + pre-kicking the first `K` partner bits into `1`-wire `rHeld : QRegister K n`, and running
unheld kicks on `K .. 17`. -/
noncomputable def dPreHoleHeld1wK218 {Var : Type} {n mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hHS : rHeld.DisjointWires rScr)
    (hMS : rMeas.DisjointWires rScr) (hMH : rMeas.DisjointWires rHeld) : DynamicCircuit Var n :=
  .seq (dLoadHole218 hm v rCore rMeas rScr hCS hMS)
    (.seq (.circuit (cHadReg (rElec3924 rCore)))
      (.seq (dPre1WireLoadAux K hK hm v rCore rMeas rHeld rScr hCS hHS hMH K le_rfl)
            (dUnheldTailAux K hm v rCore rMeas rScr hCS hMS (18 - K) (by omega))))

private theorem dPreHoleHeld1wK218_count {Var : Type} {n mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hHS : rHeld.DisjointWires rScr)
    (hMS : rMeas.DisjointWires rScr) (hMH : rMeas.DisjointWires rHeld) :
    (dPreHoleHeld1wK218 (Var :=
      Var) K hK hm v rCore rMeas rHeld rScr hCS hHS hMS hMH).count TOFF = 0 ∧
    (dPreHoleHeld1wK218 (Var :=
      Var) K hK hm v rCore rMeas rHeld rScr hCS hHS hMS hMH).count T = 15984 := by
  dsimp only [dPreHoleHeld1wK218, DynamicCircuit.count]
  obtain ⟨hL1, hL2⟩ := dLoadHole218_count (Var := Var) hm v rCore rMeas rScr hCS hMS
  obtain ⟨hP1, hP2⟩ := dPre1WireLoadAux_count (Var :=
    Var) K hK hm v rCore rMeas rHeld rScr hCS hHS hMH K le_rfl
  obtain ⟨hT1, hT2⟩ := dUnheldTailAux_count (Var :=
    Var) K hm v rCore rMeas rScr hCS hMS (18 - K) (by omega)
  rw [hL1, hL2, cHadReg_count_toff, cHadReg_count_t, hP1, hP2, hT1, hT2]
  exact ⟨rfl, by omega⟩

private theorem subspaceStep_dPreHoleHeld1wK218 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)]
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) (hMS : rMeas.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr)
    {R : Operator (2 ^ n)}
    (hPm : rMeas.basisOutcomeProjector 0 * R = R)
    (hSupp : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
      InvHoleShifted218 hm (rData.compose selCore) rScr β) R) :
    SubspaceStep R
      ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R)
      (dPreHoleHeld1wK218 K hK hm v (rData.compose selCore) rMeas rHeld rScr
        (hDS.compose_left selCore) hHS hMS hMH) := by
  have s1 := subspaceStep_dLoadHole218 (Var := Var) hm v rData selCore rMeas rScr
    hDM (hDS.compose_left selCore) hMS (supportedOn_mono (fun _ h ↦ h.2) hSupp)
  have hSupp1 : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
      InvHoleShifted218 hm (rData.compose selCore) rScr β)
      (((rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 * R) :=
    supportedOn_invHeld1wHole_of_perm_pres17 hm rData selCore rMeas rHeld rScr
      hDM hDH hDS hMH hMS (lensLoadEquiv (shiftedPartnerLens218 selCore))
      (actPreservesShifted17_uLensLoad selCore) hSupp
  have s2 := subspaceStep_of_circuit (Var := Var)
    (((rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 * R)
    (cHadReg (rElec3924 (rData.compose selCore)))
  have hSupp2 : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
      InvHoleShifted218 hm (rData.compose selCore) rScr β)
      ((cHadReg (rElec3924 (rData.compose selCore))).eval.1 *
        (((rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
          R)) :=
    supportedOn_cHadReg_mul (rElec3924 (rData.compose selCore))
      (invHeld1wHole_ignores_elec3924 hm (rData.compose selCore) rHeld rScr
        (hDH.compose_left selCore) (hDS.compose_left selCore)) hSupp1
  have s3 := subspaceStep_dPre1WireLoadAux K hK hm v (rData.compose selCore) rMeas rHeld rScr
    (hDH.compose_left selCore) (hDS.compose_left selCore) hHS hMS hMH K le_rfl hSupp2
  have hCommK :
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        uKickPrefix218 K hK (rData.compose selCore) rMeas).1 *
        ((cHadReg (rElec3924 (rData.compose selCore))).eval.1 *
          (((rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
            R)) =
      (uKickPrefix218 K hK (rData.compose selCore) rMeas).1 *
        ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl).1
          *
          ((cHadReg (rElec3924 (rData.compose selCore))).eval.1 *
            (((rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
              R))) := by
    rw [uHold1WirePrefix_comm_uKickPrefix218 K hK (rData.compose selCore) rMeas rHeld
          (hDH.compose_left selCore) hMH K le_rfl K hK, Submonoid.coe_mul, Matrix.mul_assoc]
  have hSuppHold : SupportedOn (InvHoleShifted218 hm (rData.compose selCore) rScr)
      ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl).1 *
        ((cHadReg (rElec3924 (rData.compose selCore))).eval.1 *
          (((rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
            R))) :=
    supportedOn_uHold1WirePrefix_full K hK (rData.compose selCore) rHeld (hDH.compose_left selCore)
      (invHoleShifted218_ignores_held1w hm (rData.compose selCore) rHeld rScr
        (hDH.compose_left selCore) hHS) hSupp2
  have s4 := subspaceStep_dUnheldTailAux K hK hm v (rData.compose selCore) rMeas rScr
    (hDS.compose_left selCore) hMS (18 - K) (by omega) hSuppHold
  refine subspaceStep_congr_out (s1.seq (s2.seq ((subspaceStep_congr_out s3 hCommK).seq s4))) ?_
  have hK18 : uKickPrefix218 (K + (18 - K)) (by omega) (rData.compose selCore) rMeas =
      uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas := by
    have hadd : K + (18 - K) = 18 := by omega
    exact (by generalize_proofs pf1 pf2; revert pf1; rw [hadd]; intro _; rfl)
  rw [hK18]
  have hComm18 := (uHold1WirePrefix_comm_uKickPrefix218 K hK (rData.compose selCore) rMeas rHeld
    (hDH.compose_left selCore) hMH K le_rfl 18 le_rfl).symm
  have hProjM : (rData.concat rMeas hDM).embedMatrix ((selMeasInAct kData).basisOutcomeProjector 0)
    =
      rMeas.basisOutcomeProjector 0 := by
    dsimp only [QRegister.basisOutcomeProjector]
    rw [← QRegister.embedMatrix_compose, concat_compose_selMeasInAct rData rMeas hDM]
  have hWLPm :
      ((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
        (rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
        rMeas.basisOutcomeProjector 0 =
      ((rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        rMeas.basisOutcomeProjector 0 := by
    rw [← (rData.concat rMeas hDM).embedUnitary_mul, QRegister.embedUnitary_val,
        QRegister.embedUnitary_val, ← hProjM,
        ← (rData.concat rMeas hDM).embedMatrix_mul, ← (rData.concat rMeas hDM).embedMatrix_mul,
        uLensWrite_mul_uLensLoad_projZero_eq_uLensSwap (shiftedPartnerLens218 selCore)]
  have hUK_HE :
      uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas *
        (cHadReg (rElec3924 (rData.compose selCore))).eval =
      (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) :=
    uKickPrefix218_mul_cHadReg_elec_eq rData selCore rMeas hDM
  have hWL_R :
      ((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
        (rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 * R =
      ((rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R :=
        by
    calc ((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
            (rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 * R
        = (((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
            (rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
            rMeas.basisOutcomeProjector 0) * R := by
            rw [Matrix.mul_assoc, hPm]
      _ = ((rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
            (rMeas.basisOutcomeProjector 0 * R) := by
            rw [hWLPm, Matrix.mul_assoc]
      _ = ((rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        R := by
            rw [hPm]
  calc (uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas).1 *
        ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl).1
          *
          ((cHadReg (rElec3924 (rData.compose selCore))).eval.1 *
            (((rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
              R)))
      = ((uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas *
          uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl) *
          (cHadReg (rElec3924 (rData.compose selCore))).eval *
          (rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
            R := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
          (uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas *
            (cHadReg (rElec3924 (rData.compose selCore))).eval) *
          (rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
            R := by
          rw [hComm18]; simp only [mul_assoc]
    _ = (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
          (cHadReg (rElec3924 (rData.compose selCore))).eval).1 *
          (((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
            (rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore))).1 *
              R) := by
          rw [hUK_HE]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
          (cHadReg (rElec3924 (rData.compose selCore))).eval *
          (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
            R := by
          rw [hWL_R]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]

/-- Pre-pass shifted-partner wrapper (`16,208 T`, `TOFF = 0`, `116 ≤ mScr`) holding `K ≤ 18`
partner bits in `1`-wire `rHeld : QRegister K n` while returning `rScr` to `|0⟩`. -/
noncomputable def dPreOneWireKShiftedPartner {Var : Type} {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (_hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) : DynamicCircuit Var n :=
  toDynWGLocal v (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
    (dPreHoleHeld1wK218 K hK (by omega) v (rData.compose selCore) rMeas rHeld rScr
      (hDS.compose_left selCore) hHS hMS hMH)
    ctxShiftedPartnerFast

private theorem dPreOneWireKShiftedPartner_count_toff {Var : Type} {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) :
    (dPreOneWireKShiftedPartner (Var := Var) K hK hm v rData selCore rMeas rHeld rScr
      hDH hDS hHS hMS hMH).count TOFF = 0 := by
  dsimp only [dPreOneWireKShiftedPartner]
  rw [toDynWGLocal_count_toff]
  exact (dPreHoleHeld1wK218_count K hK (by omega) v _ rMeas rHeld rScr _ hHS hMS hMH).1

private theorem dPreOneWireKShiftedPartner_count_t {Var : Type} {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) :
    (dPreOneWireKShiftedPartner (Var := Var) K hK hm v rData selCore rMeas rHeld rScr
      hDH hDS hHS hMS hMH).count T = 16208 := by
  dsimp only [dPreOneWireKShiftedPartner]
  rw [toDynWGLocal_count_t, ctxShiftedPartnerFast_countT,
      (dPreHoleHeld1wK218_count K hK (by omega) v _ rMeas rHeld rScr _ hHS hMS hMH).2]

private theorem subspaceStep_dPreOneWireKShiftedPartner {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)]
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) (hMS : rMeas.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr)
    {R : Operator (2 ^ n)}
    (hPm : rMeas.basisOutcomeProjector 0 * R = R)
    (hPh : rHeld.basisOutcomeProjector 0 * R = R)
    (hPs : rScr.basisOutcomeProjector 0 * R = R) :
    SubspaceStep R
      ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R)
      (dPreOneWireKShiftedPartner K hK hm v rData selCore rMeas rHeld rScr hDH hDS hHS hMS hMH) :=
        by
  have hPsOut : rScr.basisOutcomeProjector 0 *
      ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R) =
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R :=
          by
    rw [← Matrix.mul_assoc,
        scr_projZero_comm_uPreTarget1w K hK rData selCore rMeas rHeld rScr hDM hDH hDS hHS hMS,
        Matrix.mul_assoc, hPs]
  dsimp only [dPreOneWireKShiftedPartner]
  refine subspaceStep_toDynWGLocal v
    (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
    (dPreHoleHeld1wK218 K hK (by omega) v (rData.compose selCore) rMeas rHeld rScr
      (hDS.compose_left selCore) hHS hMS hMH)
    ctxShiftedPartnerFast
    (validAt_ctxFast_of_scr_projZero hm (rData.compose selCore) rScr (hDS.compose_left selCore) hPs)
    (validAt_ctxFast_of_scr_projZero hm (rData.compose selCore) rScr
      (hDS.compose_left selCore) hPsOut) ?_
  have hPmFwd : rMeas.basisOutcomeProjector 0 *
      ((uFwdWG (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
        ctxShiftedPartnerFast).1 * R) =
      (uFwdWG (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
        ctxShiftedPartnerFast).1 * R := by
    rw [← Matrix.mul_assoc,
        basisOutcomeProjector_zero_comm_uFwdFast hm (rData.compose selCore) rScr
          (hDS.compose_left selCore) rMeas hMS,
        Matrix.mul_assoc, hPm]
  refine subspaceStep_congr_out
    (subspaceStep_dPreHoleHeld1wK218 (Var := Var) K hK (by omega) v
      rData selCore rMeas rHeld rScr hDM hDH hDS hMH hMS hHS hPmFwd
      (supportedOn_invHeld1wHole_uFwdFast hm (rData.compose selCore) rHeld rScr
        (hDS.compose_left selCore) hHS hPh hPs)) ?_
  rw [← Matrix.mul_assoc, ← Submonoid.coe_mul,
      ← uFwdFast_comm_uPreTarget1w K hK hm rData selCore rMeas rHeld rScr hDM hDH hDS hHS hMS,
      Submonoid.coe_mul, Matrix.mul_assoc]

/-- Post-pass `.hole` circuit (`≤ 8,428 - 444 * K` `T`, `TOFF = 0`) fusing `1`-wire `rHeld` (`K`
wires) and `rMeas` (`18` wires) `X`-measurement parity fixups into one `436-T` `dFixHole218`. -/
noncomputable def dPostHoleHeld1wK218 {Var : Type} {n mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) : DynamicCircuit Var n :=
  StageBOneWireFusedCaller47493.dPostHoleHeld1wKQSlotFused
    K hK v (rElec3924 rCore) rMeas rHeld hMH
    (dUnheldTailAux K hm v rCore rMeas rScr hCS hMS (18 - K) (by omega))
    (fun m ↦ dFixHole218 hm v m rCore rScr hCS)

private theorem dPostHoleHeld1wK218_count_toff {Var : Type} {n mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) :
    (dPostHoleHeld1wK218 (Var := Var) K hK hm v rCore rMeas rHeld rScr hCS hMS hMH).count TOFF =
      0 :=
  StageBOneWireFusedCaller47493.dPostHoleHeld1wKQSlotFused_count_toff
    K hK v (rElec3924 rCore) rMeas rHeld hMH _ _
    (dUnheldTailAux_count (Var := Var) K hm v rCore rMeas rScr hCS hMS (18 - K) (by omega)).1
    (fun m ↦ dFixHole218_count_toff hm v m rCore rScr hCS)

private theorem dPostHoleHeld1wK218_count_t_le {Var : Type} {n mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) :
    (dPostHoleHeld1wK218 (Var := Var) K hK hm v rCore rMeas rHeld rScr hCS hMS hMH).count T ≤
      8428 - 444 * K :=
  StageBOneWireFusedCaller47493.dPostHoleHeld1wKQSlotFused_count_t_le_8428
    K hK v (rElec3924 rCore) rMeas rHeld hMH _ _
    (le_of_eq
      (dUnheldTailAux_count (Var := Var) K hm v rCore rMeas rScr hCS hMS (18 - K) (by omega)).2)
    (fun m ↦ dFixHole218_count_t_le hm v m rCore rScr hCS)

section UnsealCHadReg
unseal cHadReg cHadRegAux

private theorem cHadReg_eq_cHadWall {n M : ℕ} (r : QRegister M n) :
    cHadReg r = StageBOneWireFusedPost436.cHadWall r :=
  StageBOneWireFusedCaller47493.cHadWall_eq_of_rec r
    (fun k hk ↦ cHadRegAux r k hk) (fun _ ↦ rfl) (fun _ _ ↦ rfl)

end UnsealCHadReg
attribute [local irreducible] StageBOneWireFusedPost436.cHadWall

private theorem diagSign_f2Parity_eq_caller {k : ℕ} (m : Fin 18 → Bool)
    (tbl : Fin (2 ^ k) → Fin (2 ^ 18)) :
    diagSignUnitary (fun d ↦ f2Parity 18 m (tbl d)) =
      StageBUnheldTailCommBridge.diagSignUnitary
        (fun d ↦ StageBOneWireFusedCaller47493.f2Parity 18 m (tbl d)) :=
  Subtype.ext rfl

private theorem setTableOp_eq_caller {n k b : ℕ}
    (rData : QRegister k n) (rMeas : QRegister b n) (tbl : Fin (2 ^ k) → Fin (2 ^ b)) :
    setTableOp rData rMeas tbl =
      StageBOneWireFusedCaller47493.setTableOp rData rMeas tbl :=
  rfl


private theorem qreg_218_18_apply_eq {n : ℕ} {α : Sort*}
    (F : ∀ M : ℕ, QRegister M n → α)
    (r₁ : QRegister (218 * 18) n) (r₂ : QRegister 3924 n)
    (hw : ∀ i : Fin 3924, r₁ ⟨i.val, by omega⟩ = r₂ i) :
    F (218 * 18) r₁ = F 3924 r₂ := by
  have h1 : ∀ (M : ℕ) (hM : M = 3924) (x : QRegister M n),
      (∀ i : Fin 3924, x ⟨i.val, by omega⟩ = r₂ i) → F M x = F 3924 r₂ := by
    intro M hM x hx
    subst hM
    have hxeq : x = r₂ := by
      cases x with | mk wx =>
      cases r₂ with | mk w2 =>
      congr 1
      ext i
      exact congrArg Fin.val (hx i)
    rw [hxeq]
  exact h1 (218 * 18) (by decide) r₁ hw

private theorem kickEntry_eq {n : ℕ} (k : ℕ) (hk : k ≤ 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (β : BitAssignment n) (s₀ : Fin 218) :
    (if decide ((∑ j : Fin k,
          β (rElecSlot rCore s₀ ⟨j.val, by omega⟩) * β (rMeas ⟨j.val, by omega⟩)) = 1)
      then (-1 : ℂ) else 1) =
    (if decide ((∑ j : Fin k,
          β (rElec3924 rCore (StageBOneWireFusedPost436.elecFlatIdx s₀ ⟨j.val, by omega⟩)) *
            β (rMeas ⟨j.val, by omega⟩)) = 1)
      then (-1 : ℂ) else 1) := by
  refine congrArg (fun b : Bool ↦ if b then (-1 : ℂ) else 1) (decide_eq_decide.mpr (iff_of_eq ?_))
  refine congrArg (· = (1 : ZMod 2)) (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [rElecSlot_eq_rElec3924]
  rfl

private theorem uKickPrefix218_val_eq_kickPrefixPhase {n : ℕ}
    (k : ℕ) (hk : k ≤ 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n)
    (rElec : QRegister (218 * 18) n)
    (hw : ∀ i : Fin 3924, rElec ⟨i.val, by omega⟩ = rElec3924 rCore i) :
    (uKickPrefix218 k hk rCore rMeas).1 =
      (StageBUnheldTailCommBridge.diagSignUnitary
        (StageBOneWireFusedCaller47493.kickPrefixPhase k hk rElec rMeas
          (fun β ↦ shiftedPartnerSlotFast (fun w ↦ β (rCore w))))).1 := by
  refine congrArg Matrix.diagonal (funext fun g ↦ (kickEntry_eq k hk rCore rMeas (basisBits n g)
    (shiftedPartnerSlotFast (fun w ↦ basisBits n g (rCore w)))).trans ?_)
  dsimp only [StageBOneWireFusedCaller47493.kickPrefixPhase]
  refine congrArg (fun b : Bool ↦ if b then (-1 : ℂ) else 1) (decide_eq_decide.mpr (iff_of_eq ?_))
  refine congrArg (· = (1 : ZMod 2)) (Finset.sum_congr rfl fun j _ ↦ ?_)
  let idx := StageBOneWireFusedPost436.elecFlatIdx
    (shiftedPartnerSlotFast (fun w ↦ basisBits n g (rCore w))) ⟨j.val, by omega⟩
  have hidx : rElec idx = rElec3924 rCore ⟨idx.val, by have := idx.isLt; omega⟩ :=
    hw ⟨idx.val, by have := idx.isLt; omega⟩
  rw [hidx]

private theorem subspaceStep_dPostHoleHeld1wK218_gen {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)]
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rCore : QRegister posCoreWires n) (hrCore : rCore = rData.compose selCore)
    (rElec : QRegister (218 * 18) n)
    (hwElec : ∀ i : Fin 3924, rElec ⟨i.val, by omega⟩ = rElec3924 rCore i)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) (hMS : rMeas.DisjointWires rScr)
    {R : Operator (2 ^ n)}
    (hPm : rMeas.basisOutcomeProjector 0 * R = R)
    (hSupp : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
      InvHoleShifted218 hm rCore rScr β) R) :
    SubspaceStep
      ((uHold1WirePrefix K hK rCore rHeld (hrCore ▸ hDH.compose_left selCore) K le_rfl *
        (cHadReg rElec).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R)
      R
      (StageBOneWireFusedCaller47493.dPostHoleHeld1wKQSlotFused
        K hK v rElec rMeas rHeld hMH
        (dUnheldTailAux K hm v rCore rMeas rScr (hrCore ▸ hDS.compose_left selCore) hMS (18 -
          K) (by omega))
        (fun m ↦ dFixHole218 hm v m rCore rScr (hrCore ▸ hDS.compose_left selCore))) := by
  subst hrCore
  let slotOf : BitAssignment n → Fin 218 := fun β ↦ shiftedPartnerSlotFast (fun w ↦
    β ((rData.compose selCore) w))
  have hME : rMeas.DisjointWires rElec := by
    rw [QRegister.disjoint_iff]
    intro m i h
    have hi := hwElec ⟨i.val, by have := i.isLt; omega⟩
    have hi' : rElec i = rElec3924 (rData.compose selCore) ⟨i.val, by have := i.isLt; omega⟩ := hi
    rw [hi', rElec3924, QRegister.slice_apply] at h
    exact (hDM.compose_left selCore).ne _ m h.symm
  have hSuppSwap := supportedOn_invHeld1wHole_of_perm_pres17 hm rData selCore rMeas rHeld rScr
    hDM hDH hDS hMH hMS (lensSwapEquiv (shiftedPartnerLens218 selCore))
    (actPreservesShifted17_uLensSwap selCore) hSupp
  have hIgnElec : ∀ (α β : BitAssignment n),
      (∀ w, (∀ t : Fin (218 * 18), w ≠ rElec t) → α w = β w) →
      (((∀ i : Fin K, α (rHeld i) = 0) ∧ InvHoleShifted218 hm (rData.compose selCore) rScr α) ↔
        ((∀ i : Fin K, β (rHeld i) = 0) ∧ InvHoleShifted218 hm (rData.compose selCore) rScr β)) :=
    qreg_218_18_apply_eq
      (fun M reg ↦ ∀ (α β : BitAssignment n),
        (∀ w, (∀ t : Fin M, w ≠ reg t) → α w = β w) →
        (((∀ i : Fin K, α (rHeld i) = 0) ∧ InvHoleShifted218 hm (rData.compose selCore) rScr α) ↔
          ((∀ i : Fin K, β (rHeld i) = 0) ∧ InvHoleShifted218 hm (rData.compose selCore) rScr β)))
      rElec (rElec3924 (rData.compose selCore)) hwElec ▸
      invHeld1wHole_ignores_elec3924 hm (rData.compose selCore) rHeld rScr
        (hDH.compose_left selCore) (hDS.compose_left selCore)
  have hSuppMid := supportedOn_cHadReg_mul rElec hIgnElec hSuppSwap
  have hInEq :
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg rElec).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R =
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl).1 *
        ((cHadReg rElec).eval.1 *
          (((rData.concat rMeas hDM).embedUnitary
            (uLensSwap (shiftedPartnerLens218 selCore))).1 * R)) := by
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hInEq]
  have hK18 : uKickPrefix218 (K + (18 - K)) (by omega) (rData.compose selCore) rMeas =
      uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas := by
    have hadd : K + (18 - K) = 18 := by omega
    exact (by generalize_proofs pf1 pf2; revert pf1; rw [hadd]; intro _; rfl)
  have hProjM :
      (rData.concat rMeas hDM).embedMatrix ((selMeasInAct kData).basisOutcomeProjector 0) =
        rMeas.basisOutcomeProjector 0 := by
    dsimp only [QRegister.basisOutcomeProjector]
    rw [← QRegister.embedMatrix_compose, concat_compose_selMeasInAct rData rMeas hDM]
  have hWSPm :
      ((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        rMeas.basisOutcomeProjector 0 =
      setTableOp rData rMeas (shiftedPartnerLens218 selCore).tbl *
        rMeas.basisOutcomeProjector 0 := by
    rw [← (rData.concat rMeas hDM).embedUnitary_mul, QRegister.embedUnitary_val, ← hProjM,
        ← (rData.concat rMeas hDM).embedMatrix_mul,
        uLensWrite_mul_uLensSwap_projZero_eq_setTableOp (shiftedPartnerLens218 selCore),
        (rData.concat rMeas hDM).embedMatrix_mul,
        embedMatrix_setTableOp_local rData rMeas hDM (shiftedPartnerLens218 selCore).tbl, hProjM]
  have hHadEq : (cHadReg rElec).eval = (cHadReg (rElec3924 (rData.compose selCore))).eval :=
    qreg_218_18_apply_eq (fun M reg ↦ (@cHadReg n M reg).eval)
      rElec (rElec3924 (rData.compose selCore)) hwElec
  have hConjHE :
      (cHadReg rElec).eval * uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas *
        (cHadReg rElec).eval =
        (rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) := by
    rw [hHadEq]
    exact cHadReg_elec_conj_uKickPrefix218_eq_uLensWrite rData selCore rMeas hDM
  have hWS_R :
      ((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R =
      setTableOp rData rMeas (shiftedPartnerLens218 selCore).tbl * R := by
    calc ((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
            (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R
        = (((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
            (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
            rMeas.basisOutcomeProjector 0) * R := by
            rw [Matrix.mul_assoc, hPm]
      _ = setTableOp rData rMeas (shiftedPartnerLens218 selCore).tbl *
            (rMeas.basisOutcomeProjector 0 * R) := by
            rw [hWSPm, Matrix.mul_assoc]
      _ = setTableOp rData rMeas (shiftedPartnerLens218 selCore).tbl * R := by rw [hPm]
  have hPreMeasEq :
      (cHadReg rElec).eval.1 *
        ((uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas).1 *
          ((cHadReg rElec).eval.1 *
            (((rData.concat rMeas hDM).embedUnitary
              (uLensSwap (shiftedPartnerLens218 selCore))).1 * R))) =
      setTableOp rData rMeas (shiftedPartnerLens218 selCore).tbl * R := by
    calc (cHadReg rElec).eval.1 *
          ((uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas).1 *
            ((cHadReg rElec).eval.1 *
              (((rData.concat rMeas hDM).embedUnitary
                (uLensSwap (shiftedPartnerLens218 selCore))).1 * R)))
        = (((cHadReg rElec).eval * uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas *
          (cHadReg rElec).eval) *
            (rData.concat rMeas hDM).embedUnitary
              (uLensSwap (shiftedPartnerLens218 selCore))).1 * R := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = ((rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) *
            (rData.concat rMeas hDM).embedUnitary
              (uLensSwap (shiftedPartnerLens218 selCore))).1 * R := by
            rw [hConjHE]
      _ = setTableOp rData rMeas (shiftedPartnerLens218 selCore).tbl * R := hWS_R
  refine
    StageBOneWireFusedCaller47493.subspaceStep_dPostHoleHeld1wKQSlotFused
      K hK v rData rElec rMeas rHeld hDM hME hMH slotOf (shiftedPartnerLens218 selCore).tbl
      (Inv_mid := fun β ↦
        (∀ i : Fin K, β (rHeld i) = 0) ∧ InvHoleShifted218 hm (rData.compose selCore) rScr β)
      (Inv_post := InvHoleShifted218 hm (rData.compose selCore) rScr)
      (U_kickK := (uKickPrefix218 K hK (rData.compose selCore) rMeas).1)
      (U_kick18 := (uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas).1)
      (fun α β h ↦ by
        have hIff := qreg_218_18_apply_eq
          (fun M reg ↦ ∀ (α₁ β₁ : BitAssignment n),
            (∀ w, (∀ t : Fin M, w ≠ reg t) → α₁ w = β₁ w) →
            (((∀ i : Fin 0, α₁ ((rHeld.slice 0 0 (by omega)) i) = 0) ∧
                InvHoleShifted218 hm (rData.compose selCore) rScr α₁) ↔
              ((∀ i : Fin 0, β₁ ((rHeld.slice 0 0 (by omega)) i) = 0) ∧
                InvHoleShifted218 hm (rData.compose selCore) rScr β₁)))
          rElec (rElec3924 (rData.compose selCore)) hwElec ▸
          invHeld1wHole_ignores_elec3924 (K := 0) hm (rData.compose selCore)
            (rHeld.slice 0 0 (by omega)) rScr
            (by rw [QRegister.disjoint_iff]; rintro _ ⟨_, ⟨⟩⟩)
            (hDS.compose_left selCore)
        have hIff' := hIff α β (fun w hw ↦ h w fun ⟨t, ht⟩ ↦ hw t ht.symm)
        exact ⟨fun hp ↦ (hIff'.mp ⟨fun i ↦ Fin.elim0 i, hp⟩).2,
          fun hp ↦ (hIff'.mpr ⟨fun i ↦ Fin.elim0 i, hp⟩).2⟩)
      (fun α β h ↦ shiftedPartnerSlotFast_congr_outside fun w _ _ ↦
        h ((rData.compose selCore) w) fun ⟨t, ht⟩ ↦ by
        have ht' : rElec t = rElec3924 (rData.compose selCore) ⟨t.val, by have := t.isLt; omega⟩ :=
          hwElec ⟨t.val, by have := t.isLt; omega⟩
        rw [ht', rElec3924, QRegister.slice_apply] at ht
        have hv := congrArg Fin.val ((rData.compose selCore).wires.injective ht)
        dsimp only at hv
        have := t.isLt
        omega)
      (fun g j ↦ by
        rw [basisBits_shiftedPartnerLens218_tbl_eq rData selCore g j, rElecSlot_eq_rElec3924]
        let idx := StageBOneWireFusedPost436.elecFlatIdx (slotOf (basisBits n g)) j
        exact (congrArg (basisBits n g) (hwElec ⟨idx.val, by have := idx.isLt; omega⟩)).symm)
      (uKickPrefix218_val_eq_kickPrefixPhase K hK (rData.compose selCore) rMeas rElec hwElec)
      (uKickPrefix218_val_eq_kickPrefixPhase 18 le_rfl (rData.compose selCore) rMeas rElec hwElec)
      (fun β ⟨hZero, _⟩ ↦ ⟨p2d_writeReg β rHeld (held1WireVals K hK (rData.compose selCore) β),
        uHold1WirePrefix_eq_writeReg_of_zero K hK (rData.compose selCore) rHeld (hDH.compose_left
          selCore) β hZero,
        hZero,
        fun t ↦ by
          rw [p2d_writeReg_apply_reg]
          dsimp [held1WireVals]
          rw [rElecSlot_eq_rElec3924]
          let idx := StageBOneWireFusedPost436.elecFlatIdx (slotOf β) ⟨t.val, by omega⟩
          exact (congrArg β (hwElec ⟨idx.val, by have := idx.isLt; omega⟩)).symm,
        fun w hw ↦ p2d_writeReg_apply_of_not_mem _ _ _ w hw⟩)
      hSuppMid
      (supportedOn_mono (fun _ h ↦ h.2) hSupp)
      hPm
      (fun hS ↦ subspaceStep_congr_out
        (subspaceStep_dUnheldTailAux K hK hm v (rData.compose selCore) rMeas rScr (hDS.compose_left
          selCore) hMS
          (18 - K) (by omega) (supportedOn_mono (fun _ h ↦ h.2) hS))
        (by rw [hK18]))
      ((congrArg₂ (· * ·)
          (congrArg (fun c : Circuit n ↦ c.eval.1) (cHadReg_eq_cHadWall rElec).symm) rfl).trans
        (hPreMeasEq.trans
          (congrArg₂ (· * ·)
            (setTableOp_eq_caller rData rMeas (shiftedPartnerLens218 selCore).tbl) rfl)))
      (fun m {R₀} hS ↦ subspaceStep_congr_out
        (subspaceStep_dFixHole218 hm v m rData selCore rScr (hDS.compose_left selCore) hS)
        (by rw [diagSign_f2Parity_eq_caller]))

private theorem subspaceStep_dPostHoleHeld1wK218 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)]
    (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) (hMS : rMeas.DisjointWires rScr)
    {R : Operator (2 ^ n)}
    (hPm : rMeas.basisOutcomeProjector 0 * R = R)
    (hSupp : SupportedOn (fun β ↦ (∀ i : Fin K, β (rHeld i) = 0) ∧
      InvHoleShifted218 hm (rData.compose selCore) rScr β) R) :
    SubspaceStep
      ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R)
      R
      (dPostHoleHeld1wK218 K hK hm v (rData.compose selCore) rMeas rHeld rScr
        (hDS.compose_left selCore) hMS hMH) := by
  let rE218 : QRegister (218 * 18) n :=
    ⟨⟨fun i ↦ rElec3924 (rData.compose selCore) ⟨i.val, by have := i.isLt; omega⟩,
      fun i j hij ↦
        Fin.ext (congrArg Fin.val ((rElec3924 (rData.compose selCore)).wires.injective hij))⟩⟩
  have hStep := subspaceStep_dPostHoleHeld1wK218_gen K hK hm v rData selCore
    (rData.compose selCore) rfl rE218 (fun _ ↦ rfl) rMeas rHeld rScr hDM hDH hDS hMH hMS hPm hSupp
  have hIn : (cHadReg rE218).eval = (cHadReg (rElec3924 (rData.compose selCore))).eval :=
    qreg_218_18_apply_eq (fun M reg ↦ (@cHadReg n M reg).eval)
      rE218 (rElec3924 (rData.compose selCore)) (fun _ ↦ rfl)
  have hProg :
      StageBOneWireFusedCaller47493.dPostHoleHeld1wKQSlotFused
        K hK v rE218 rMeas rHeld hMH
        (dUnheldTailAux K hm v (rData.compose selCore) rMeas rScr (hDS.compose_left selCore) hMS (18
          - K) (by omega))
        (fun m ↦ dFixHole218 hm v m (rData.compose selCore) rScr (hDS.compose_left selCore)) =
      dPostHoleHeld1wK218 K hK hm v (rData.compose selCore) rMeas rHeld rScr
        (hDS.compose_left selCore) hMS hMH := by
    dsimp only [dPostHoleHeld1wK218]
    exact qreg_218_18_apply_eq
      (fun M (reg : QRegister M n) ↦
        if hM : M = 218 * 18 then
          StageBOneWireFusedCaller47493.dPostHoleHeld1wKQSlotFused
            K hK v (hM ▸ reg) rMeas rHeld hMH
            (dUnheldTailAux K hm v (rData.compose selCore) rMeas rScr (hDS.compose_left selCore) hMS
              (18 - K) (by omega))
            (fun m ↦ dFixHole218 hm v m (rData.compose selCore) rScr (hDS.compose_left selCore))
        else dPostHoleHeld1wK218 K hK hm v (rData.compose selCore) rMeas rHeld rScr
          (hDS.compose_left selCore) hMS hMH)
      rE218 (rElec3924 (rData.compose selCore)) (fun _ ↦ rfl)
  rw [hIn, hProg] at hStep
  exact hStep


/-- Post-pass shifted-partner wrapper (`≤ (8,652 - 444 * K) + if K = 0 then 0 else 436` `T`,
`TOFF = 0`, `116 ≤ mScr`) saving `444 * K - 436` `T` by reusing and MBU-resetting `1`-wire
`rHeld : QRegister K n` to `|0⟩`. -/
noncomputable def dPostOneWireKShiftedPartner {Var : Type} {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (_hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (_hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) : DynamicCircuit Var n :=
  toDynWGLocal v (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
    (dPostHoleHeld1wK218 K hK (by omega) v (rData.compose selCore) rMeas rHeld rScr
      (hDS.compose_left selCore) hMS hMH)
    ctxShiftedPartnerFast

private theorem dPostOneWireKShiftedPartner_count_toff {Var : Type} {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) :
    (dPostOneWireKShiftedPartner (Var := Var) K hK hm v rData selCore rMeas rHeld rScr
      hDH hDS hHS hMS hMH).count TOFF = 0 := by
  dsimp only [dPostOneWireKShiftedPartner]
  rw [toDynWGLocal_count_toff]
  exact dPostHoleHeld1wK218_count_toff K hK (by omega) v _ rMeas rHeld rScr _ hMS hMH

private theorem dPostOneWireKShiftedPartner_count_t_le {Var : Type} {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) :
    (dPostOneWireKShiftedPartner (Var := Var) K hK hm v rData selCore rMeas rHeld rScr
      hDH hDS hHS hMS hMH).count T ≤
      8652 - 444 * K := by
  dsimp only [dPostOneWireKShiftedPartner]
  rw [toDynWGLocal_count_t, ctxShiftedPartnerFast_countT]
  have h := dPostHoleHeld1wK218_count_t_le (Var := Var) K hK (by omega) v
    (rData.compose selCore) rMeas rHeld rScr (hDS.compose_left selCore) hMS hMH
  omega

private theorem subspaceStep_dPostOneWireKShiftedPartner {Var : Type} [Fintype Var] [DecidableEq
    Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)]
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) (hMS : rMeas.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr)
    {R : Operator (2 ^ n)}
    (hPm : rMeas.basisOutcomeProjector 0 * R = R)
    (hPh : rHeld.basisOutcomeProjector 0 * R = R)
    (hPs : rScr.basisOutcomeProjector 0 * R = R) :
    SubspaceStep
      ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R)
      R
      (dPostOneWireKShiftedPartner K hK hm v rData selCore rMeas rHeld rScr hDH hDS hHS hMS hMH) :=
        by
  have hPsIn : rScr.basisOutcomeProjector 0 *
      ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R) =
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 * R :=
          by
    rw [← Matrix.mul_assoc,
        scr_projZero_comm_uPreTarget1w K hK rData selCore rMeas rHeld rScr hDM hDH hDS hHS hMS,
        Matrix.mul_assoc, hPs]
  dsimp only [dPostOneWireKShiftedPartner]
  refine subspaceStep_toDynWGLocal v
    (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
    (dPostHoleHeld1wK218 K hK (by omega) v (rData.compose selCore) rMeas rHeld rScr
      (hDS.compose_left selCore) hMS hMH)
    ctxShiftedPartnerFast
    (validAt_ctxFast_of_scr_projZero hm (rData.compose selCore) rScr
      (hDS.compose_left selCore) hPsIn)
    (validAt_ctxFast_of_scr_projZero hm (rData.compose selCore) rScr
      (hDS.compose_left selCore) hPs) ?_
  have hComm :
      (uFwdWG (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
        ctxShiftedPartnerFast).1 *
        ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
          (cHadReg (rElec3924 (rData.compose selCore))).eval *
          (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
            R) =
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        ((uFwdWG (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
          ctxShiftedPartnerFast).1 * R) := by
    rw [← Matrix.mul_assoc, ← Submonoid.coe_mul,
        uFwdFast_comm_uPreTarget1w K hK hm rData selCore rMeas rHeld rScr hDM hDH hDS hHS hMS,
        Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hComm]
  have hPmFwd : rMeas.basisOutcomeProjector 0 *
      ((uFwdWG (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
        ctxShiftedPartnerFast).1 * R) =
      (uFwdWG (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
        ctxShiftedPartnerFast).1 * R := by
    rw [← Matrix.mul_assoc,
        basisOutcomeProjector_zero_comm_uFwdFast hm (rData.compose selCore) rScr
          (hDS.compose_left selCore) rMeas hMS,
        Matrix.mul_assoc, hPm]
  exact subspaceStep_dPostHoleHeld1wK218 (Var := Var) K hK (by omega) v
    rData selCore rMeas rHeld rScr hDM hDH hDS hMH hMS hPmFwd
    (supportedOn_invHeld1wHole_uFwdFast hm (rData.compose selCore) rHeld rScr
      (hDS.compose_left selCore) hHS hPh hPs)

/-- Parametric `K ≤ 18` one-wire held-partner true-swap wrapper for `shiftedPartnerLens218`
(`≤ ((24,860 - 444 * K) + if K = 0 then 0 else 436) + dInner.count T` `T`,
`TOFF = dInner.count TOFF`, `116 ≤ mScr`): holds `K` partner bits in `rHeld : QRegister K n`
across `dInner` while releasing `100%` of `rScr` (`|0⟩`) to `dInner` and restoring `rMeas`,
`rHeld`, and `rScr` to `|0⟩`. -/
noncomputable def dOneWireHeldKTrueSwapShiftedPartner {Var : Type} {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld)
    (dInner : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.seq (dPreOneWireKShiftedPartner K hK hm v rData selCore rMeas rHeld rScr hDH hDS hHS hMS
    hMH)
             dInner)
       (dPostOneWireKShiftedPartner K hK hm v rData selCore rMeas rHeld rScr hDH hDS hHS hMS hMH)

theorem dOneWireHeldKTrueSwapShiftedPartner_count_toff {Var : Type} {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld)
    (dInner : DynamicCircuit Var n) :
    (dOneWireHeldKTrueSwapShiftedPartner K hK hm v rData selCore rMeas rHeld rScr
      hDH hDS hHS hMS hMH dInner).count TOFF = dInner.count TOFF := by
  dsimp only [dOneWireHeldKTrueSwapShiftedPartner, DynamicCircuit.count]
  rw [dPreOneWireKShiftedPartner_count_toff, dPostOneWireKShiftedPartner_count_toff, zero_add,
    add_zero]

theorem dOneWireHeldKTrueSwapShiftedPartner_count_t_le {Var : Type} {n kData mScr : ℕ}
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld)
    (dInner : DynamicCircuit Var n) :
    (dOneWireHeldKTrueSwapShiftedPartner K hK hm v rData selCore rMeas rHeld rScr
      hDH hDS hHS hMS hMH dInner).count T ≤
      (24860 - 444 * K) + dInner.count T := by
  dsimp only [dOneWireHeldKTrueSwapShiftedPartner, DynamicCircuit.count]
  rw [dPreOneWireKShiftedPartner_count_t]
  have hPost := dPostOneWireKShiftedPartner_count_t_le (Var := Var) K hK hm v
    rData selCore rMeas rHeld rScr hDH hDS hHS hMS hMH
  omega

theorem dOneWireHeldKTrueSwapShiftedPartner_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)]
    (K : ℕ) (hK : K ≤ 18) (hm : 116 ≤ mScr) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rHeld : QRegister K n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDH : rData.DisjointWires rHeld) (hDS : rData.DisjointWires rScr)
    (hMH : rMeas.DisjointWires rHeld) (hMS : rMeas.DisjointWires rScr)
    (hHS : rHeld.DisjointWires rScr)
    (uMid : Unitary (2 ^ (kData + 18))) (dInner : DynamicCircuit Var n)
    (hdInner : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rData.concat rMeas hDM) rScr uMid dInner)
    (hElec : Elec3924Preserved selCore uMid)
    (hPres17 : ActPreservesShifted17 selCore uMid) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData
      (rMeas.concat (rHeld.concat rScr hHS) (disjointWires_concat_right rMeas rHeld rScr hHS hMH
        hMS))
      (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
        (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))
      (dOneWireHeldKTrueSwapShiftedPartner K hK hm v rData selCore rMeas rHeld rScr
        hDH hDS hHS hMS hMH dInner) := by
  have hR₀_eq :
      (rMeas.concat (rHeld.concat rScr hHS)
        (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 =
      rMeas.basisOutcomeProjector 0 *
        (rHeld.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0) := by
    rw [QRegExt.basisOutcomeProjector_concat_zero, QRegExt.basisOutcomeProjector_concat_zero]
  have hPm0 : rMeas.basisOutcomeProjector 0 *
      (rMeas.concat (rHeld.concat rScr hHS)
        (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 =
      (rMeas.concat (rHeld.concat rScr hHS)
        (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 := by
    rw [hR₀_eq, ← Matrix.mul_assoc, basisOutcomeProjector_zero_idem]
  have hPh0 : rHeld.basisOutcomeProjector 0 *
      (rMeas.concat (rHeld.concat rScr hHS)
        (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 =
      (rMeas.concat (rHeld.concat rScr hHS)
        (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 := by
    calc rHeld.basisOutcomeProjector 0 *
          (rMeas.concat (rHeld.concat rScr hHS)
            (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0
        = (rHeld.basisOutcomeProjector 0 * rMeas.basisOutcomeProjector 0) *
            (rHeld.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0) := by
            rw [hR₀_eq]; simp only [Matrix.mul_assoc]
      _ = rMeas.basisOutcomeProjector 0 *
            ((rHeld.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0) *
              rScr.basisOutcomeProjector 0) := by
            rw [basisOutcomeProjector_zero_comm rHeld rMeas]; simp only [Matrix.mul_assoc]
      _ = (rMeas.concat (rHeld.concat rScr hHS)
            (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 := by
            rw [basisOutcomeProjector_zero_idem, ← hR₀_eq]
  have hPs0 : rScr.basisOutcomeProjector 0 *
      (rMeas.concat (rHeld.concat rScr hHS)
        (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 =
      (rMeas.concat (rHeld.concat rScr hHS)
        (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 := by
    calc rScr.basisOutcomeProjector 0 *
          (rMeas.concat (rHeld.concat rScr hHS)
            (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0
        = (rScr.basisOutcomeProjector 0 * rMeas.basisOutcomeProjector 0) *
            (rHeld.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0) := by
            rw [hR₀_eq]; simp only [Matrix.mul_assoc]
      _ = rMeas.basisOutcomeProjector 0 *
            ((rScr.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0) *
              rScr.basisOutcomeProjector 0) := by
            rw [basisOutcomeProjector_zero_comm rScr rMeas]; simp only [Matrix.mul_assoc]
      _ = rMeas.basisOutcomeProjector 0 *
            (rHeld.basisOutcomeProjector 0 *
              (rScr.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0)) := by
            rw [basisOutcomeProjector_zero_comm rScr rHeld]; simp only [Matrix.mul_assoc]
      _ = (rMeas.concat (rHeld.concat rScr hHS)
            (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 := by
            rw [basisOutcomeProjector_zero_idem, ← hR₀_eq]
  have sPre := subspaceStep_dPreOneWireKShiftedPartner (Var := Var) K hK hm v
    rData selCore rMeas rHeld rScr hDM hDH hDS hMH hMS hHS hPm0 hPh0 hPs0
  have hPs1 : rScr.basisOutcomeProjector 0 *
      ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        (rMeas.concat (rHeld.concat rScr hHS)
          (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0) =
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        (rMeas.concat (rHeld.concat rScr hHS)
          (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 := by
    rw [← Matrix.mul_assoc,
        scr_projZero_comm_uPreTarget1w K hK rData selCore rMeas rHeld rScr hDM hDH hDS hHS hMS,
        Matrix.mul_assoc, hPs0]
  have sMid := subspaceStep_of_realizesCleanWorkspace (rData.concat rMeas hDM) rScr uMid dInner
    hdInner hPs1
  have hProjM : (rData.concat rMeas hDM).embedMatrix ((selMeasInAct kData).basisOutcomeProjector 0)
    =
      rMeas.basisOutcomeProjector 0 := by
    dsimp only [QRegister.basisOutcomeProjector]
    rw [← QRegister.embedMatrix_compose, concat_compose_selMeasInAct rData rMeas hDM]
  have hEmbD : (rData.concat rMeas hDM).embedMatrix
      ((selDataInAct kData).embedMatrix
        (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
          (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17)).1) =
      (rData.embedUnitary
        (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
          (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 := by
    rw [← QRegister.embedMatrix_compose, concat_compose_selDataInAct rData rMeas hDM,
        QRegister.embedUnitary_val]
  have hInterEmb :
      ((rData.concat rMeas hDM).embedUnitary uMid *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        rMeas.basisOutcomeProjector 0 =
      ((rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        (rData.embedUnitary
          (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
            (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
        rMeas.basisOutcomeProjector 0 := by
    rw [← (rData.concat rMeas hDM).embedUnitary_mul, QRegister.embedUnitary_val, ← hProjM,
        ← (rData.concat rMeas hDM).embedMatrix_mul,
        uMid_intertwines_uLensSwap_of_comm_P_slot0 (shiftedPartnerLens218 selCore) uMid
          (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17),
        (rData.concat rMeas hDM).embedMatrix_mul, (rData.concat rMeas hDM).embedMatrix_mul]
    simp only [QRegister.embedUnitary_val, hEmbD, hProjM]
  have hCommUMidPre :
      (rData.concat rMeas hDM).embedUnitary uMid *
        (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
          (cHadReg (rElec3924 (rData.compose selCore))).eval) =
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval) *
        (rData.concat rMeas hDM).embedUnitary uMid :=
    unitary_comm_mul ((rData.concat rMeas hDM).embedUnitary uMid)
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl)
      (cHadReg (rElec3924 (rData.compose selCore))).eval
      (uHold1WirePrefix_comm_embed_uMid K hK rData selCore rMeas rHeld hDM hDH hMH
        hElec hPres17 K le_rfl).symm
      (cHadReg_elec_comm_of_elec3924Preserved rData selCore rMeas hDM hElec).symm
  have hMidEq :
      ((rData.concat rMeas hDM).embedUnitary uMid).1 *
        ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
          (cHadReg (rElec3924 (rData.compose selCore))).eval *
          (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
          (rMeas.concat (rHeld.concat rScr hHS)
            (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0) =
      (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
        (cHadReg (rElec3924 (rData.compose selCore))).eval *
        (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
        ((rData.embedUnitary
          (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
            (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
          (rMeas.concat (rHeld.concat rScr hHS)
            (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0) :=
              by
    calc ((rData.concat rMeas hDM).embedUnitary uMid).1 *
          ((uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl
            *
            (cHadReg (rElec3924 (rData.compose selCore))).eval *
            (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
            (rMeas.concat (rHeld.concat rScr hHS)
              (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0)
        = (((rData.concat rMeas hDM).embedUnitary uMid *
            (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl
              *
              (cHadReg (rElec3924 (rData.compose selCore))).eval)) *
            (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
            (rMeas.basisOutcomeProjector 0 *
              (rHeld.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0)) := by
            rw [hR₀_eq]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
            (cHadReg (rElec3924 (rData.compose selCore))).eval).1 *
            ((((rData.concat rMeas hDM).embedUnitary uMid *
              (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
              rMeas.basisOutcomeProjector 0) *
              (rHeld.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0)) := by
            rw [hCommUMidPre]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
            (cHadReg (rElec3924 (rData.compose selCore))).eval).1 *
            ((((rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1
              *
              (rData.embedUnitary
                (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
                  (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
              rMeas.basisOutcomeProjector 0) *
              (rHeld.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0)) := by
            rw [hInterEmb]
      _ = (uHold1WirePrefix K hK (rData.compose selCore) rHeld (hDH.compose_left selCore) K le_rfl *
            (cHadReg (rElec3924 (rData.compose selCore))).eval *
            (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore))).1 *
            ((rData.embedUnitary
              (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
                (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
              (rMeas.concat (rHeld.concat rScr hHS)
                (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0)
                  := by
            rw [hR₀_eq]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  have hPmRes : rMeas.basisOutcomeProjector 0 *
      ((rData.embedUnitary
        (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
          (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
        (rMeas.concat (rHeld.concat rScr hHS)
          (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0) =
      (rData.embedUnitary
        (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
          (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
        (rMeas.concat (rHeld.concat rScr hHS)
          (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 := by
    dsimp only [QRegister.embedUnitary_val]
    rw [← Matrix.mul_assoc,
        ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rData) rMeas hDM _ 0).symm,
        Matrix.mul_assoc, hPm0]
  have hPhRes : rHeld.basisOutcomeProjector 0 *
      ((rData.embedUnitary
        (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
          (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
        (rMeas.concat (rHeld.concat rScr hHS)
          (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0) =
      (rData.embedUnitary
        (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
          (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
        (rMeas.concat (rHeld.concat rScr hHS)
          (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 := by
    dsimp only [QRegister.embedUnitary_val]
    rw [← Matrix.mul_assoc,
        ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rData) rHeld hDH _ 0).symm,
        Matrix.mul_assoc, hPh0]
  have hPsRes : rScr.basisOutcomeProjector 0 *
      ((rData.embedUnitary
        (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
          (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
        (rMeas.concat (rHeld.concat rScr hHS)
          (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0) =
      (rData.embedUnitary
        (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
          (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))).1 *
        (rMeas.concat (rHeld.concat rScr hHS)
          (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS)).basisOutcomeProjector 0 := by
    dsimp only [QRegister.embedUnitary_val]
    rw [← Matrix.mul_assoc,
        ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rData) rScr hDS _ 0).symm,
        Matrix.mul_assoc, hPs0]
  have sPost := subspaceStep_dPostOneWireKShiftedPartner (Var := Var) K hK hm v
    rData selCore rMeas rHeld rScr hDM hDH hDS hMH hMS hHS hPmRes hPhRes hPsRes
  exact realizesCleanWorkspace_of_subspaceStep rData
    (rMeas.concat (rHeld.concat rScr hHS) (disjointWires_concat_right rMeas rHeld rScr hHS hMH hMS))
    (restrictOfCommSlot0 (shiftedPartnerLens218 selCore) uMid
      (comm_P_slot0_of_elec3924Preserved selCore uMid hElec hPres17))
    _ ((subspaceStep_congr_out (sPre.seq sMid) hMidEq).seq sPost)

attribute [irreducible]
  dPreHoleHeld1wK218
  dPreOneWireKShiftedPartner
  dPostHoleHeld1wK218
  dPostOneWireKShiftedPartner
  dOneWireHeldKTrueSwapShiftedPartner

end StageBOneWireHeld

end
end StageBOneWireHeld

section LocalStageBOneWireOpenAdd0
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 4200

namespace StageBOneWireOpenAdd0

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instNeZero_G6Open (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

local instance (priority := 1000000) instGroupUnitaryFast_G6Open (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instSemigroupUnitaryFast_G6Open (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  (instGroupUnitaryFast_G6Open D).toSemigroup

open SpecsAux
open Operator QProg Matrix Real
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators

section Part1_OpenOneWireStageB

open PosSlots24BranchConcrete (posCoreWires)
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_compose_of_disjoint disjointWires_concat_left)
open PosPostPrep80MergedVep (cSwapCore3967 uSwapCore3967 lockPosPostVal_eq)
open HoistBorrow42ProjBridge (RealizesOnProj)
open InterWalkRSum42Hoist (kFull80 rSum0 qreg_block_apply)
open Leaf4Ext48TopStitch (rExt6IdleFull)
open LocalHeldStreamFoldedPass123Bridge (pRawCtrl3ExtOn pRawHoistExtOn)
open StageADeconstrCore
  (selDataInAct selDataInAct_apply selMeasInAct selMeasInAct_apply)
open ZeroHypSlot0CommAndHMidClosure (restrictOfCommSlot0)
open DoubleDutyFoldedRealizesBridge (rPG7Full)
open StageBTwoElecQftStream218Inner
  (posCoreWires_eq_4034 selCoreInCoreSum42PG7 selPG7InCoreSum42PG7)
open LocalStageBTwoElecQftStream218Inner
  (selSum42InCoreSum42PG7 uElec18Sum42Add uStageBTwoElecStreamInner)
open LocalMidUnitaryConjZeroRoot (rCoreSwapPG3Sum42PG7Full)
open LocalStageBCachedTrueSwapIdle
  (rCtrl3IdleFull rWorkCtrl3Idle rCoreSwapPG3Sum42PG7Full_disj_rCtrl3IdleFull)
open LocalStageBPartnerTrueSwapStream218Closure
  (uStageBFull rCoreSwapPG3Sum42PG7Full_disj_rExt6IdleFull)
open LocalStageBFastInnerPartnerShift
  (p3_qreg_ext basisOutcomeProjector_zero_eq_of_bij kStageBData kStageBData_eq_4083
   shiftedPartnerLens218
   selCoreInDataAnchor selCoreInDataAnchor_val_eq selDataAnchorSubst selSubstWithPartner
   uAnchorInner uAnchorInner_comm_P_slot0_shiftedPartner uAnchorStageBStream218PG7
   liftDataMeas concat_compose_liftDataMeas
   liftDataMeas_rCoreSwapPG3Sum42PG7Full_uAnchorStageBStream218PG7
   uAnchorTrueSwapFull uBarrelFastOnActFull uAnchorFrame uAnchorFrame_eq_p3_01
   rCtrl3IdleFull_projZero_comm_anchorSwap_and_barrel
   rExt6IdleFull_projZero_comm_anchorSwap_and_barrel
   rWorkCtrl3Idle_projZero_mul_pRawCtrl3ExtOn rWorkGuardExt_projZero_mul_pRawHoistExtOn)
open BoothOpt_StageBPartnerCoreShave (actPreservesShifted17_mul orbitSandAnchorBoothOptBaseT)
open BoothOpt_P4_10_TwoLoadHeldRowTrueSwap (elec3924Preserved_mul)
open TwoLoadStageBCircuits
  (elec3924Preserved_uAnchorInner actPreservesShifted17_uAnchorInner
   restrictOfCommSlot0_p410_eq_fused)
open P1_OpenAnchorAdd0TwoLoad
  (posCoreWires_eq_fullSysCoreWires80
   selAncSum0InFull18 uAdd0AncFull18 compose_selAncSum0InFull18_eq
   uExpQft25 uJunctionRawFull selAncPG7InFull18 uQft0AncFull18 uJunctionAncFull18
   compose_selAncPG7InFull18_eq uAnchorFrame_uJunctionRawFull_eq
   dStageBTwoElecStreamInnerOpenQftOnData count_dStageBTwoElecStreamInnerOpenQftOnData_toff
   count_dStageBTwoElecStreamInnerOpenQftOnData_t_le
   dStageBTwoElecStreamInnerOpenQftOnData_realizes
   uStageBOpenQftStreamInner_eq_uStageBTwoElecStreamInner
   uJunctionRawInActB42 selAncSum42InDA selAncPG7InDA uAdd0AncPG7 uQft0AncPG7 uJunctionRawAncPG7
   uAnchorInnerOpenQft elec3924Preserved_selSubst_uJunctionRawInActB42
   actPreservesShifted17_selSubst_uJunctionRawInActB42
   uAnchorInnerOpenQft_comm_P_slot0_shiftedPartner restrictOfCommSlot0_uAnchorInnerOpenQft_eq
   selCoreInDataAnchor_disj_selAncSum42InDA
   rCoreSwapPG3Sum42PG7Full_selSum42
   liftDataMeas_rCoreSwapPG3Sum42PG7Full_uJunctionRawAn)
open StageBOneWireHeld
  (dOneWireHeldKTrueSwapShiftedPartner dOneWireHeldKTrueSwapShiftedPartner_count_toff
   dOneWireHeldKTrueSwapShiftedPartner_count_t_le dOneWireHeldKTrueSwapShiftedPartner_realizes)
open StageBOneWireBridge
  (kOneWire kOneWire_le_18 stageBOneWireKBoothOptAnchorT stageBOneWireBoothOptAnchorT)

attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires

private theorem selCoreInDataAnchor_disj_selAncPG7InDA :
    selCoreInDataAnchor.DisjointWires selAncPG7InDA := by
  have h4034 := posCoreWires_eq_4034
  have h4083 := kStageBData_eq_4083
  rw [QRegister.disjoint_iff]
  intro i j
  have hi := i.isLt
  refine Fin.addCases (fun q ↦ ?_) (fun m ↦ ?_) j
  · intro h
    have hv := congrArg Fin.val h
    rw [selCoreInDataAnchor_val_eq, selAncPG7InDA, QRegister.concat_apply_left,
        selMeasInAct_apply, Fin.val_natAdd] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    have hmVal : (selPG7InCoreSum42PG7 m).val = posCoreWires + 42 + m.val := by
      simp [selPG7InCoreSum42PG7]
    rw [selCoreInDataAnchor_val_eq, selAncPG7InDA, QRegister.concat_apply_right,
        QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd, hmVal] at hv
    omega

private theorem rCoreSwapPG3Sum42PG7Full_selPG7 (off : ℕ) (hoff : off + 3 ≤ 41) (m : Fin 7) :
    rCoreSwapPG3Sum42PG7Full off hoff (selPG7InCoreSum42PG7 m) = rPG7Full m := by
  have hm : selPG7InCoreSum42PG7 m = Fin.natAdd (fullSysCoreWires 80 + 42) m := by
    ext
    simp [selPG7InCoreSum42PG7, posCoreWires_eq_fullSysCoreWires80]
  rw [hm, rCoreSwapPG3Sum42PG7Full, QRegister.concat_apply_right]

/-- Open-seam no-swap 1-wire Stage B at explicit held wire count `K ≤ 18` (`138 + K ≤ mClean`),
slicing `rHeld` (`K` wires) and `rClIn` (`mClean - K` wires) from `rClean`. -/
noncomputable def dAnchorStageBOpenNoSwapOneWireK {Var : Type} {n mClean : ℕ}
    (K : ℕ) (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 + K ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDP : rData.DisjointWires rPartner18)
    (hDO : rData.DisjointWires rOrbit16) (hDC : rData.DisjointWires rClean)
    (hAP : rAnchor18.DisjointWires rPartner18)
    (hAO : rAnchor18.DisjointWires rOrbit16) (hAC : rAnchor18.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16) (hPC : rPartner18.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  let rDA := rData.concat rAnchor18 hDA
  let rHeld := rClean.compose (QRegister.block 0 K (by omega))
  let rClIn := rClean.compose (QRegister.block K (mClean - K) (by omega))
  let hHCl : rHeld.DisjointWires rClIn :=
    disjointWires_compose_of_disjoint rClean
      (QRegister.block_disjoint_of_le 0 K K (mClean - K)
        (by omega) (by omega) (by omega))
  let hOCl : rOrbit16.DisjointWires rClIn := hOC.compose_right _
  let rScr := rOrbit16.concat rClIn hOCl
  let hDAP : rDA.DisjointWires rPartner18 := disjointWires_concat_left hDA hDP hAP
  let hDAO : rDA.DisjointWires rOrbit16 := disjointWires_concat_left hDA hDO hAO
  let hDAC : rDA.DisjointWires rClean := disjointWires_concat_left hDA hDC hAC
  let hDAH : rDA.DisjointWires rHeld := hDAC.compose_right _
  let hDACl : rDA.DisjointWires rClIn := hDAC.compose_right _
  let hDAS : rDA.DisjointWires rScr :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOCl (QRegExt.disjointWires_symm hDAO)
    (QRegExt.disjointWires_symm hDACl)))
  let hHS : rHeld.DisjointWires rScr :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOCl (hOC.compose_right _)
      (QRegExt.disjointWires_symm hHCl)))
  let hPS : rPartner18.DisjointWires rScr :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOCl (QRegExt.disjointWires_symm hPO)
      (QRegExt.disjointWires_symm (hPC.compose_right _))))
  let hPH : rPartner18.DisjointWires rHeld := hPC.compose_right _
  dOneWireHeldKTrueSwapShiftedPartner K hK (by omega) v
    rDA selCoreInDataAnchor rPartner18 rHeld rScr
    hDAH hDAS hHS hPS hPH
    (dStageBTwoElecStreamInnerOpenQftOnData B hB6 hB27 (by omega : 138 ≤ mClean - K)
      slot2SwappedTo0 v (rDA.compose selDataAnchorSubst) rPartner18 rOrbit16 rClIn
      (hDAP.compose_left _) (hDAO.compose_left _) (hDACl.compose_left _)
      hPO (hPC.compose_right _) hOCl)

private theorem dAnchorStageBOpenNoSwapOneWireK_count_toff {Var : Type} {n mClean : ℕ}
    (K : ℕ) (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 + K ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDP : rData.DisjointWires rPartner18)
    (hDO : rData.DisjointWires rOrbit16) (hDC : rData.DisjointWires rClean)
    (hAP : rAnchor18.DisjointWires rPartner18)
    (hAO : rAnchor18.DisjointWires rOrbit16) (hAC : rAnchor18.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16) (hPC : rPartner18.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (dAnchorStageBOpenNoSwapOneWireK K hK B hB6 hB27 hmClean slot2SwappedTo0 v
      rData rAnchor18 rPartner18 rOrbit16 rClean
      hDA hDP hDO hDC hAP hAO hAC hPO hPC hOC).count TOFF = 0 := by
  dsimp only [dAnchorStageBOpenNoSwapOneWireK]
  rw [dOneWireHeldKTrueSwapShiftedPartner_count_toff,
      count_dStageBTwoElecStreamInnerOpenQftOnData_toff]


private theorem projZero_comm {n k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) :
    r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 * r₁.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)

private theorem dAnchorStageBOpenNoSwapOneWireK_count_t_le_fused
    {Var : Type} {n mClean : ℕ}
    (K : ℕ) (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 138 + K ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hDA : rData.DisjointWires rAnchor18) (hDP : rData.DisjointWires rPartner18)
    (hDO : rData.DisjointWires rOrbit16) (hDC : rData.DisjointWires rClean)
    (hAP : rAnchor18.DisjointWires rPartner18)
    (hAO : rAnchor18.DisjointWires rOrbit16) (hAC : rAnchor18.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16) (hPC : rPartner18.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (dAnchorStageBOpenNoSwapOneWireK K hK B hB6 hB27 hmClean slot2SwappedTo0 v
      rData rAnchor18 rPartner18 rOrbit16 rClean
      hDA hDP hDO hDC hAP hAO hAC hPO hPC hOC).count T ≤
      stageBOneWireKBoothOptAnchorT K B (mClean - K) - 164 -
        if K = 0 then 0 else 436 := by
  dsimp only [dAnchorStageBOpenNoSwapOneWireK, stageBOneWireKBoothOptAnchorT]
  refine le_trans (dOneWireHeldKTrueSwapShiftedPartner_count_t_le
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  refine le_trans (Nat.add_le_add_left (count_dStageBTwoElecStreamInnerOpenQftOnData_t_le
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _) ?_
  by_cases h0 : K = 0
  · rw [ite_eq_left h0]
    omega
  · rw [ite_eq_right h0]
    omega

private theorem dAnchorStageBOpenNoSwapOneWireK_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mClean : ℕ} [NeZero (2 ^ n)]
    (K : ℕ) (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 + K ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDP : rData.DisjointWires rPartner18)
    (hDO : rData.DisjointWires rOrbit16) (hDC : rData.DisjointWires rClean)
    (hAP : rAnchor18.DisjointWires rPartner18)
    (hAO : rAnchor18.DisjointWires rOrbit16) (hAC : rAnchor18.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16) (hPC : rPartner18.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rData.concat rAnchor18 hDA)
      (rPartner18.concat (rOrbit16.concat rClean hOC)
        (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm hPO)
          (QRegExt.disjointWires_symm hPC))))
      (restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
        (uAnchorInner B (by omega) hB27 slot2SwappedTo0)
        (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 slot2SwappedTo0) *
          uJunctionRawAncPG7)
      (dAnchorStageBOpenNoSwapOneWireK K hK B hB6 hB27 hmClean slot2SwappedTo0 v
        rData rAnchor18 rPartner18 rOrbit16 rClean
        hDA hDP hDO hDC hAP hAO hAC hPO hPC hOC) := by
  let rDA := rData.concat rAnchor18 hDA
  let rHeld := rClean.compose (QRegister.block 0 K (by omega))
  let rClIn := rClean.compose (QRegister.block K (mClean - K) (by omega))
  let hHCl : rHeld.DisjointWires rClIn :=
    disjointWires_compose_of_disjoint rClean
      (QRegister.block_disjoint_of_le 0 K K (mClean - K)
        (by omega) (by omega) (by omega))
  let hOCl : rOrbit16.DisjointWires rClIn := hOC.compose_right _
  let rScr := rOrbit16.concat rClIn hOCl
  let hDAP : rDA.DisjointWires rPartner18 := disjointWires_concat_left hDA hDP hAP
  let hDAO : rDA.DisjointWires rOrbit16 := disjointWires_concat_left hDA hDO hAO
  let hDAC : rDA.DisjointWires rClean := disjointWires_concat_left hDA hDC hAC
  let hDAH : rDA.DisjointWires rHeld := hDAC.compose_right _
  let hDACl : rDA.DisjointWires rClIn := hDAC.compose_right _
  let hDAS : rDA.DisjointWires rScr :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOCl (QRegExt.disjointWires_symm hDAO)
    (QRegExt.disjointWires_symm hDACl)))
  let hPH : rPartner18.DisjointWires rHeld := hPC.compose_right _
  let hHS : rHeld.DisjointWires rScr :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOCl (hOC.compose_right _)
      (QRegExt.disjointWires_symm hHCl)))
  let hPS : rPartner18.DisjointWires rScr :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOCl (QRegExt.disjointWires_symm hPO)
      (QRegExt.disjointWires_symm (hPC.compose_right _))))
  have hInnerRaw := dStageBTwoElecStreamInnerOpenQftOnData_realizes
    B hB6 hB27 (by omega : 138 ≤ mClean - K) slot2SwappedTo0 v
    (rDA.compose selDataAnchorSubst) rPartner18 rOrbit16 rClIn
    (hDAP.compose_left _) (hDAO.compose_left _) (hDACl.compose_left _)
    hPO (hPC.compose_right _) hOCl
  rw [uStageBOpenQftStreamInner_eq_uStageBTwoElecStreamInner] at hInnerRaw
  have hRegEq :
      (rDA.compose selDataAnchorSubst).concat rPartner18 (hDAP.compose_left _) =
        (rDA.concat rPartner18 hDAP).compose selSubstWithPartner := by
    apply p3_qreg_ext
    intro idx
    rw [QRegister.compose_apply]
    refine Fin.addCases (fun iD ↦ ?_) (fun jP ↦ ?_) idx
    · rw [QRegister.concat_apply_left, selSubstWithPartner, QRegister.concat_apply_left]
      change rDA (selDataAnchorSubst iD) =
        (rDA.concat rPartner18 hDAP) (selDataInAct (kStageBData + 18) (selDataAnchorSubst iD))
      rw [selDataInAct_apply, QRegister.concat_apply_left]
    · rw [QRegister.concat_apply_right, selSubstWithPartner, QRegister.concat_apply_right,
        selMeasInAct_apply, QRegister.concat_apply_right]
  rw [hRegEq] at hInnerRaw
  have hInnerWide := hInnerRaw.widenActive
  have hOpenEq :
      selSubstWithPartner.embedUnitary
        (uStageBTwoElecStreamInner B (by omega) hB27 slot2SwappedTo0 * uJunctionRawInActB42) =
      uAnchorInnerOpenQft B (by omega) hB27 slot2SwappedTo0 := by
    rw [QRegister.embedUnitary_mul]
    rfl
  rw [hOpenEq] at hInnerWide
  have hRaw := dOneWireHeldKTrueSwapShiftedPartner_realizes K hK
    (by omega) v
    rDA selCoreInDataAnchor rPartner18 rHeld rScr
    hDAP hDAH hDAS hPH hPS hHS
    (uAnchorInnerOpenQft B (by omega) hB27 slot2SwappedTo0) _
    hInnerWide
    (elec3924Preserved_mul _
      (elec3924Preserved_uAnchorInner B (by omega) hB27 slot2SwappedTo0)
      elec3924Preserved_selSubst_uJunctionRawInActB42)
    (actPreservesShifted17_mul _
      (actPreservesShifted17_uAnchorInner B (by omega) hB27 slot2SwappedTo0)
      actPreservesShifted17_selSubst_uJunctionRawInActB42)
  rw [restrictOfCommSlot0_p410_eq_fused selCoreInDataAnchor
      (uAnchorInnerOpenQft B (by omega) hB27 slot2SwappedTo0) _
      (uAnchorInnerOpenQft_comm_P_slot0_shiftedPartner B (by omega) hB27 slot2SwappedTo0),
    restrictOfCommSlot0_uAnchorInnerOpenQft_eq B (by omega) hB27 slot2SwappedTo0] at hRaw
  have hClMul : rHeld.basisOutcomeProjector 0 * rClIn.basisOutcomeProjector 0 =
      rClean.basisOutcomeProjector 0 := by
    have h0 : (rHeld.concat rClIn hHCl).basisOutcomeProjector 0 =
        rClean.basisOutcomeProjector 0 := by
      refine basisOutcomeProjector_zero_eq_of_bij (rHeld.concat rClIn hHCl) rClean (by omega)
        fun idx ↦ ⟨⟨idx.val, by omega⟩, rfl, ?_⟩
      refine Fin.addCases (fun q ↦ ?_) (fun rest ↦ ?_) idx
      · rw [QRegister.concat_apply_left]
        dsimp only [rHeld, QRegister.compose_apply]
        exact congrArg rClean (Fin.ext (by simp))
      · rw [QRegister.concat_apply_right]
        dsimp only [rClIn, QRegister.compose_apply]
        exact congrArg rClean (Fin.ext (by simp))
    rwa [QRegExt.basisOutcomeProjector_concat_zero] at h0
  let rWorkHeld := rPartner18.concat (rHeld.concat rScr hHS)
    (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.disjointWires_concat_right
      rPartner18 rHeld rScr hHS hPH hPS)
  let rWorkStd := rPartner18.concat (rOrbit16.concat rClean hOC)
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm hPO)
      (QRegExt.disjointWires_symm hPC)))
  have hWorkProj : rWorkHeld.basisOutcomeProjector 0 = rWorkStd.basisOutcomeProjector 0 := by
    dsimp only [rWorkHeld, rWorkStd, rScr]
    rw [QRegExt.basisOutcomeProjector_concat_zero,
        QRegExt.basisOutcomeProjector_concat_zero,
        QRegExt.basisOutcomeProjector_concat_zero,
        QRegExt.basisOutcomeProjector_concat_zero,
        QRegExt.basisOutcomeProjector_concat_zero,
        ← Matrix.mul_assoc (rHeld.basisOutcomeProjector 0),
        projZero_comm rHeld rOrbit16,
        Matrix.mul_assoc (rOrbit16.basisOutcomeProjector 0), hClMul]
  dsimp only [rWorkHeld, rWorkStd] at hWorkProj
  intro M
  obtain ⟨M', hwp, hEq⟩ := hRaw M
  rw [hWorkProj] at hEq
  exact ⟨M', hwp, hEq⟩

attribute [irreducible] dAnchorStageBOpenNoSwapOneWireK

/-- Open-QFT `cSwapCore3967`-conjugated 1-wire Stage B on `rWork : QRegister mWork n`
(`172 + K ≤ mWork`), slicing `rP18`, `rO16`, `rCl` from `rWork`. -/
noncomputable def dAnchorStageBOpenSwap3967OfWorkOneWireK {Var : Type} {n mWork : ℕ}
    (K : ℕ) (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmWork : 172 + K ≤ mWork)
    (v : Var) (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWork)
    (hAW : rAnchor18.DisjointWires rWork) : DynamicCircuit Var n :=
  let rP18 := rWork.compose (QRegister.block 0 18 (by omega))
  let rO16 := rWork.compose (QRegister.block 18 16 (by omega))
  let rCl := rWork.compose (QRegister.block 34 (mWork - 34) (by omega))
  let hPO : rP18.DisjointWires rO16 :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 0 18 18 16 (by omega) (by omega) (by omega))
  let hPC : rP18.DisjointWires rCl :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 0 18 34 (mWork - 34) (by omega) (by omega) (by omega))
  let hOC : rO16.DisjointWires rCl :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 18 16 34 (mWork - 34) (by omega) (by omega) (by omega))
  let cSw : DynamicCircuit Var n :=
    .circuit (cSwapCore3967.onRegister (rData.compose selCoreInCoreSum42PG7))
  .seq cSw (.seq
    (dAnchorStageBOpenNoSwapOneWireK K hK B hB6 hB27 (by omega) true v
      rData rAnchor18 rP18 rO16 rCl
      hDA (hDW.compose_right _) (hDW.compose_right _) (hDW.compose_right _)
      (hAW.compose_right _) (hAW.compose_right _) (hAW.compose_right _)
      hPO hPC hOC)
    cSw)

private theorem dAnchorStageBOpenSwap3967OfWorkOneWireK_count_toff {Var : Type} {n mWork : ℕ}
    (K : ℕ) (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmWork : 172 + K ≤ mWork)
    (v : Var) (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWork)
    (hAW : rAnchor18.DisjointWires rWork) :
    (dAnchorStageBOpenSwap3967OfWorkOneWireK K hK B hB6 hB27 hmWork v
      rData rAnchor18 rWork hDA hDW hAW).count TOFF = 0 := by
  let rCore : QRegister (fullSysCoreWires 80) n := rData.compose selCoreInCoreSum42PG7
  let cSw : DynamicCircuit Var n := .circuit (cSwapCore3967.onRegister rCore)
  have hSw : cSw.count TOFF = 0 := rfl
  let rP18 := rWork.compose (QRegister.block 0 18 (by omega))
  let rO16 := rWork.compose (QRegister.block 18 16 (by omega))
  let rCl := rWork.compose (QRegister.block 34 (mWork - 34) (by omega))
  let hPO : rP18.DisjointWires rO16 :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 0 18 18 16 (by omega) (by omega) (by omega))
  let hPC : rP18.DisjointWires rCl :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 0 18 34 (mWork - 34) (by omega) (by omega) (by omega))
  let hOC : rO16.DisjointWires rCl :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 18 16 34 (mWork - 34) (by omega) (by omega) (by omega))
  have hMid := dAnchorStageBOpenNoSwapOneWireK_count_toff K hK B hB6 hB27
    (by omega : 138 + K ≤ mWork - 34) true v rData rAnchor18 rP18 rO16 rCl
    hDA (hDW.compose_right _) (hDW.compose_right _) (hDW.compose_right _)
    (hAW.compose_right _) (hAW.compose_right _) (hAW.compose_right _) hPO hPC hOC
  change (DynamicCircuit.seq cSw (DynamicCircuit.seq _ cSw)).count TOFF = 0
  dsimp only [DynamicCircuit.count]
  rw [hSw, hMid]


private theorem dAnchorStageBOpenSwap3967OfWorkOneWireK_count_t_le_fused
    {Var : Type} {n mWork : ℕ}
    (K : ℕ) (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (hmWork : 172 + K ≤ mWork) (v : Var)
    (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWork) (hAW : rAnchor18.DisjointWires rWork) :
    (dAnchorStageBOpenSwap3967OfWorkOneWireK K hK B hB6 hB27 hmWork v
      rData rAnchor18 rWork hDA hDW hAW).count T ≤
      stageBOneWireKBoothOptAnchorT K B ((mWork - 34) - K) - 164 -
        if K = 0 then 0 else 436 := by
  let rCore : QRegister (fullSysCoreWires 80) n := rData.compose selCoreInCoreSum42PG7
  let cSw : DynamicCircuit Var n := .circuit (cSwapCore3967.onRegister rCore)
  have hSw : cSw.count T = 0 := rfl
  let rP18 := rWork.compose (QRegister.block 0 18 (by omega))
  let rO16 := rWork.compose (QRegister.block 18 16 (by omega))
  let rCl := rWork.compose (QRegister.block 34 (mWork - 34) (by omega))
  let hPO : rP18.DisjointWires rO16 :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 0 18 18 16 (by omega) (by omega) (by omega))
  let hPC : rP18.DisjointWires rCl :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 0 18 34 (mWork - 34)
        (by omega) (by omega) (by omega))
  let hOC : rO16.DisjointWires rCl :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 18 16 34 (mWork - 34)
        (by omega) (by omega) (by omega))
  have hMid := dAnchorStageBOpenNoSwapOneWireK_count_t_le_fused K hK B hB6 hB27
    (by omega : 138 + K ≤ mWork - 34) true v rData rAnchor18 rP18 rO16 rCl
    hDA (hDW.compose_right _) (hDW.compose_right _) (hDW.compose_right _)
    (hAW.compose_right _) (hAW.compose_right _) (hAW.compose_right _) hPO hPC hOC
  change (DynamicCircuit.seq cSw
    (DynamicCircuit.seq
      (dAnchorStageBOpenNoSwapOneWireK K hK B hB6 hB27 (by omega) true v
        rData rAnchor18 rP18 rO16 rCl
        hDA (hDW.compose_right _) (hDW.compose_right _) (hDW.compose_right _)
        (hAW.compose_right _) (hAW.compose_right _) (hAW.compose_right _) hPO hPC hOC)
      cSw)).count T ≤ _
  dsimp only [DynamicCircuit.count]
  rw [hSw]
  omega

private theorem dAnchorStageBOpenSwap3967OfWorkOneWireK_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mWork : ℕ} [NeZero (2 ^ n)]
    (K : ℕ) (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmWork : 172 + K ≤ mWork)
    (v : Var) (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWork)
    (hAW : rAnchor18.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rData.concat rAnchor18 hDA)
      rWork
      (uAnchorStageBStream218PG7 B hB6 hB27 * uJunctionRawAncPG7)
      (dAnchorStageBOpenSwap3967OfWorkOneWireK K hK B hB6 hB27 hmWork v
        rData rAnchor18 rWork hDA hDW hAW) := by
  let rDA := rData.concat rAnchor18 hDA
  let rP18 := rWork.compose (QRegister.block 0 18 (by omega))
  let rO16 := rWork.compose (QRegister.block 18 16 (by omega))
  let rCl := rWork.compose (QRegister.block 34 (mWork - 34) (by omega))
  let hPO : rP18.DisjointWires rO16 :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 0 18 18 16 (by omega) (by omega) (by omega))
  let hPC : rP18.DisjointWires rCl :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 0 18 34 (mWork - 34) (by omega) (by omega) (by omega))
  let hOC : rO16.DisjointWires rCl :=
    disjointWires_compose_of_disjoint rWork
      (QRegister.block_disjoint_of_le 18 16 34 (mWork - 34) (by omega) (by omega) (by omega))
  let rWorkSplit := rP18.concat (rO16.concat rCl hOC)
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm hPO)
      (QRegExt.disjointWires_symm hPC)))
  have hDAW : rDA.DisjointWires rWork := disjointWires_concat_left hDA hDW hAW
  have hSwCore : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rDA.compose selCoreInDataAnchor) rWork uSwapCore3967
      (DynamicCircuit.circuit (Var := Var)
        (cSwapCore3967.onRegister (rData.compose selCoreInCoreSum42PG7))) := by
    have hCompEq : rDA.compose selCoreInDataAnchor = rData.compose selCoreInCoreSum42PG7 := by
      apply p3_qreg_ext
      intro i
      rw [QRegister.compose_apply, selCoreInDataAnchor, QRegister.compose_apply,
        selDataInAct_apply, QRegister.concat_apply_left, QRegister.compose_apply]
    rw [hCompEq, uSwapCore3967, lockPosPostVal_eq]
    exact DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
      (Var := Var) (rData.compose selCoreInCoreSum42PG7) rWork cSwapCore3967.eval
      (cSwapCore3967.onRegister (rData.compose selCoreInCoreSum42PG7))
      (Circuit.eval_onRegister _ _)
  have hSw := hSwCore.widenActive
  have hMid0 := dAnchorStageBOpenNoSwapOneWireK_realizes K hK B hB6 hB27
    (by omega : 138 + K ≤ mWork - 34) true v rData rAnchor18 rP18 rO16 rCl
    hDA (hDW.compose_right _) (hDW.compose_right _) (hDW.compose_right _)
    (hAW.compose_right _) (hAW.compose_right _) (hAW.compose_right _) hPO hPC hOC
  have hWorkProj : rWorkSplit.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 := by
    refine basisOutcomeProjector_zero_eq_of_bij rWorkSplit rWork (by omega) fun idx ↦
      ⟨⟨idx.val, by omega⟩, rfl, ?_⟩
    refine Fin.addCases (fun q ↦ ?_) (fun rest ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      dsimp only [rP18, QRegister.compose_apply]
      exact congrArg rWork (Fin.ext (by simp))
    · rw [QRegister.concat_apply_right]
      refine Fin.addCases (fun o ↦ ?_) (fun c ↦ ?_) rest
      · rw [QRegister.concat_apply_left]
        dsimp only [rO16, QRegister.compose_apply]
        exact congrArg rWork (Fin.ext (by simp))
      · rw [QRegister.concat_apply_right]
        dsimp only [rCl, QRegister.compose_apply]
        exact congrArg rWork (Fin.ext (by
          simp
          omega))
  have hMid : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rDA rWork
      (restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
        (uAnchorInner B (by omega) hB27 true)
        (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 true) * uJunctionRawAncPG7)
      (dAnchorStageBOpenNoSwapOneWireK K hK B hB6 hB27 (by omega) true v
        rData rAnchor18 rP18 rO16 rCl
        hDA (hDW.compose_right _) (hDW.compose_right _) (hDW.compose_right _)
        (hAW.compose_right _) (hAW.compose_right _) (hAW.compose_right _) hPO hPC hOC) := by
    intro M
    obtain ⟨M', hwp, hEq⟩ := hMid0 M
    rw [hWorkProj] at hEq
    exact ⟨M', hwp, hEq⟩
  have hSeq := hSw.seq hDAW (hMid.seq hDAW hSw)
  have hCommAdd : uAdd0AncPG7 * selCoreInDataAnchor.embedUnitary uSwapCore3967 =
      selCoreInDataAnchor.embedUnitary uSwapCore3967 * uAdd0AncPG7 := by
    apply Subtype.ext
    unfold uAdd0AncPG7
    simp only [Submonoid.coe_mul, QRegister.embedUnitary_val]
    exact (QRegister.embedMatrix_comm_of_disjoint selCoreInDataAnchor selAncSum42InDA
      selCoreInDataAnchor_disj_selAncSum42InDA uSwapCore3967.1 uElec18Sum42Add.1).symm
  have hCommQftInv : uQft0AncPG7⁻¹ * selCoreInDataAnchor.embedUnitary uSwapCore3967 =
      selCoreInDataAnchor.embedUnitary uSwapCore3967 * uQft0AncPG7⁻¹ := by
    have hInv : uQft0AncPG7⁻¹ = selAncPG7InDA.embedUnitary uExpQft25⁻¹ := by
      apply Subtype.ext
      change star (selAncPG7InDA.embedMatrix uExpQft25.1) =
        selAncPG7InDA.embedMatrix (star uExpQft25.1)
      rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
          QRegister.embedMatrix_conjTranspose]
    apply Subtype.ext
    rw [hInv]
    simp only [Submonoid.coe_mul, QRegister.embedUnitary_val]
    exact (QRegister.embedMatrix_comm_of_disjoint selCoreInDataAnchor selAncPG7InDA
      selCoreInDataAnchor_disj_selAncPG7InDA uSwapCore3967.1 (uExpQft25⁻¹).1).symm
  have hCommSw : uJunctionRawAncPG7 * selCoreInDataAnchor.embedUnitary uSwapCore3967 =
      selCoreInDataAnchor.embedUnitary uSwapCore3967 * uJunctionRawAncPG7 := by
    unfold uJunctionRawAncPG7
    calc (uAdd0AncPG7 * uQft0AncPG7⁻¹) * selCoreInDataAnchor.embedUnitary uSwapCore3967
        = uAdd0AncPG7 * (uQft0AncPG7⁻¹ * selCoreInDataAnchor.embedUnitary uSwapCore3967) := by
            simp only [_root_.mul_assoc]
      _ = (uAdd0AncPG7 * selCoreInDataAnchor.embedUnitary uSwapCore3967) * uQft0AncPG7⁻¹ := by
            rw [hCommQftInv]; simp only [_root_.mul_assoc]
      _ = selCoreInDataAnchor.embedUnitary uSwapCore3967 * (uAdd0AncPG7 * uQft0AncPG7⁻¹) := by
            rw [hCommAdd]; simp only [_root_.mul_assoc]
  have hConjEq :
      (selCoreInDataAnchor.embedUnitary uSwapCore3967 *
        (restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
          (uAnchorInner B (by omega) hB27 true)
          (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 true) *
          uJunctionRawAncPG7)) *
        selCoreInDataAnchor.embedUnitary uSwapCore3967 =
      uAnchorStageBStream218PG7 B hB6 hB27 * uJunctionRawAncPG7 := by
    unfold uAnchorStageBStream218PG7
    calc (selCoreInDataAnchor.embedUnitary uSwapCore3967 *
            (restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
              (uAnchorInner B (by omega) hB27 true)
              (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 true) *
              uJunctionRawAncPG7)) *
            selCoreInDataAnchor.embedUnitary uSwapCore3967
        = (selCoreInDataAnchor.embedUnitary uSwapCore3967 *
            restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
              (uAnchorInner B (by omega) hB27 true)
              (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 true)) *
            (uJunctionRawAncPG7 * selCoreInDataAnchor.embedUnitary uSwapCore3967) := by
            simp only [_root_.mul_assoc]
      _ = (selCoreInDataAnchor.embedUnitary uSwapCore3967 *
            restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
              (uAnchorInner B (by omega) hB27 true)
              (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 true)) *
            selCoreInDataAnchor.embedUnitary uSwapCore3967 * uJunctionRawAncPG7 := by
            rw [hCommSw]
            simp only [_root_.mul_assoc]
  rw [hConjEq] at hSeq
  exact hSeq

attribute [irreducible] dAnchorStageBOpenSwap3967OfWorkOneWireK

/-- Auto-dispatched open-QFT 1-wire Stage B (`172 ≤ mWork`, `K := kOneWire (mWork - 34)`). -/
noncomputable def dAnchorStageBOpenSwap3967OfWorkOneWire {Var : Type} {n mWork : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hm172 : 172 ≤ mWork) (v : Var)
    (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWork)
    (hAW : rAnchor18.DisjointWires rWork) : DynamicCircuit Var n :=
  dAnchorStageBOpenSwap3967OfWorkOneWireK
    (kOneWire (mWork - 34)) (kOneWire_le_18 (mWork - 34))
    B hB6 hB27 (by
        unfold kOneWire
        omega) v rData rAnchor18 rWork hDA hDW hAW

private theorem dAnchorStageBOpenSwap3967OfWorkOneWire_count_toff {Var : Type} {n mWork : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hm172 : 172 ≤ mWork) (v : Var)
    (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWork)
    (hAW : rAnchor18.DisjointWires rWork) :
    (dAnchorStageBOpenSwap3967OfWorkOneWire B hB6 hB27 hm172 v
      rData rAnchor18 rWork hDA hDW hAW).count TOFF = 0 :=
  dAnchorStageBOpenSwap3967OfWorkOneWireK_count_toff _ _ B hB6 hB27 _ v
    rData rAnchor18 rWork hDA hDW hAW


private theorem dAnchorStageBOpenSwap3967OfWorkOneWire_count_t_le_fused
    {Var : Type} {n mWork : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hm172 : 172 ≤ mWork) (v : Var)
    (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWork) (hAW : rAnchor18.DisjointWires rWork) :
    (dAnchorStageBOpenSwap3967OfWorkOneWire B hB6 hB27 hm172 v
      rData rAnchor18 rWork hDA hDW hAW).count T ≤
      stageBOneWireBoothOptAnchorT B (mWork - 34) - 164 -
        if kOneWire (mWork - 34) = 0 then 0 else 436 :=
  dAnchorStageBOpenSwap3967OfWorkOneWireK_count_t_le_fused _ _ B hB6 hB27 _ v
    rData rAnchor18 rWork hDA hDW hAW

private theorem dAnchorStageBOpenSwap3967OfWorkOneWire_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mWork : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hm172 : 172 ≤ mWork) (v : Var)
    (rData : QRegister kStageBData n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n)
    (hDA : rData.DisjointWires rAnchor18)
    (hDW : rData.DisjointWires rWork)
    (hAW : rAnchor18.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rData.concat rAnchor18 hDA) rWork
      (uAnchorStageBStream218PG7 B hB6 hB27 * uJunctionRawAncPG7)
      (dAnchorStageBOpenSwap3967OfWorkOneWire B hB6 hB27 hm172 v
        rData rAnchor18 rWork hDA hDW hAW) :=
  dAnchorStageBOpenSwap3967OfWorkOneWireK_realizes _ _ B hB6 hB27 _ v
    rData rAnchor18 rWork hDA hDW hAW

section ParAuxOpenOneWireVariants
open LocalStageBFastInnerPartnerShift.RealizesOnProj
  (of_clean_fixedByWorkZero)

private theorem uJunctionAncFull18_inv_eq :
    uJunctionAncFull18⁻¹ = uQft0AncFull18 * uAdd0AncFull18⁻¹ :=
  inv_eq_of_mul_eq_one_left (by
    unfold uJunctionAncFull18
    calc (uQft0AncFull18 * uAdd0AncFull18⁻¹) * (uAdd0AncFull18 * uQft0AncFull18⁻¹)
        = uQft0AncFull18 * (uAdd0AncFull18⁻¹ * uAdd0AncFull18) * uQft0AncFull18⁻¹ := by
            simp only [_root_.mul_assoc]
      _ = uQft0AncFull18 * uQft0AncFull18⁻¹ := by rw [inv_mul_cancel, mul_one]
      _ = 1 := mul_inv_cancel uQft0AncFull18)

/-- `Ctrl` (`3 + k_idle` borrowed clean wires) open-seam 1-wire Stage B on `kFull80`. -/
noncomputable def dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire
    {Var : Type} {n mWork k_idle off : ℕ}
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (3 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork)
    (hAncW : rAnchor18.DisjointWires rWork) : DynamicCircuit Var n :=
  dAnchorStageBOpenSwap3967OfWorkOneWire B hB6 hB27 hm172 v
    (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)) rAnchor18
    (rWorkCtrl3Idle k_idle (by omega) rAct rWork hAW)
    (hAA.compose_left _)
    (HoistBorrow42ProjBridge.disjointWires_concat_right
      (hAW.compose_left _)
      (disjointWires_compose_of_disjoint rAct
        (rCoreSwapPG3Sum42PG7Full_disj_rCtrl3IdleFull k_idle off hk_off hoff)))
    (HoistBorrow42ProjBridge.disjointWires_concat_right hAncW (QRegExt.disjointWires_symm
      (hAA.compose_left _)))

private theorem dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire_count_toff
    {Var : Type} {n mWork k_idle off : ℕ}
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (3 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork)
    (hAncW : rAnchor18.DisjointWires rWork) :
    (dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire hk_off hoff hm172 B hB6 hB27 v
      rAct rAnchor18 rWork hAA hAW hAncW).count TOFF = 0 :=
  dAnchorStageBOpenSwap3967OfWorkOneWire_count_toff B hB6 hB27 hm172 v _ _ _ _ _ _


private theorem dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire_count_t_le_fused
    {Var : Type} {n mWork k_idle off : ℕ}
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (3 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAncW : rAnchor18.DisjointWires rWork) :
    (dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire hk_off hoff hm172 B hB6 hB27 v
      rAct rAnchor18 rWork hAA hAW hAncW).count T ≤
      stageBOneWireBoothOptAnchorT B ((mWork + (3 + k_idle)) - 34) - 164 -
        if kOneWire ((mWork + (3 + k_idle)) - 34) = 0 then 0 else 436 :=
  dAnchorStageBOpenSwap3967OfWorkOneWire_count_t_le_fused B hB6 hB27 hm172 v _ _ _ _ _ _

private theorem dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire_realizes_clean
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mWork k_idle off : ℕ} [NeZero (2 ^ n)]
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (3 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork)
    (hAncW : rAnchor18.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rAct.concat rAnchor18 hAA)
      (rWorkCtrl3Idle k_idle (by omega) rAct rWork hAW)
      (BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame
        (uStageBFull B hB6 hB27 * uJunctionRawFull))
      (dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire hk_off hoff hm172 B hB6 hB27 v
        rAct rAnchor18 rWork hAA hAW hAncW) := by
  have h0 := dAnchorStageBOpenSwap3967OfWorkOneWire_realizes B hB6 hB27 hm172 v
    (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)) rAnchor18
    (rWorkCtrl3Idle k_idle (by omega) rAct rWork hAW)
    (hAA.compose_left _)
    (HoistBorrow42ProjBridge.disjointWires_concat_right
      (hAW.compose_left _)
      (disjointWires_compose_of_disjoint rAct
        (rCoreSwapPG3Sum42PG7Full_disj_rCtrl3IdleFull k_idle off hk_off hoff)))
    (HoistBorrow42ProjBridge.disjointWires_concat_right hAncW (QRegExt.disjointWires_symm
      (hAA.compose_left _)))
  rw [← concat_compose_liftDataMeas rAct rAnchor18 hAA (rCoreSwapPG3Sum42PG7Full off hoff)] at h0
  have h1 := h0.widenActive
  have hUEq : (liftDataMeas (rCoreSwapPG3Sum42PG7Full off hoff)).embedUnitary
      (uAnchorStageBStream218PG7 B hB6 hB27 * uJunctionRawAncPG7) =
      BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame
        (uStageBFull B hB6 hB27 * uJunctionRawFull) := by
    rw [QRegister.embedUnitary_mul,
        liftDataMeas_rCoreSwapPG3Sum42PG7Full_uAnchorStageBStream218PG7 off hoff B hB6 hB27,
        uAnchorFrame_eq_p3_01,
        liftDataMeas_rCoreSwapPG3Sum42PG7Full_uJunctionRawAn off hoff,
        ← uAnchorFrame_uJunctionRawFull_eq,
        BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame_mul]
  rwa [hUEq] at h1

private theorem dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire_realizesOnProj_mid
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mWork k_idle off : ℕ} [NeZero (2 ^ n)]
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (3 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork)
    (hAncW : rAnchor18.DisjointWires rWork)
    (G : Operator (2 ^ n)) :
    RealizesOnProj
      ((rAct.concat rAnchor18 hAA).embedMatrix (uJunctionAncFull18⁻¹).1 *
        ((rAct.concat rAnchor18 hAA).embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
          pRawCtrl3ExtOn k_idle (by omega) rAct rWork * G))
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame
          (uStageBFull B hB6 hB27 * uJunctionRawFull)))
      (dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire hk_off hoff hm172 B hB6 hB27 v
        rAct rAnchor18 rWork hAA hAW hAncW) := by
  let rDA := rAct.concat rAnchor18 hAA
  let rCI := rCtrl3IdleFull k_idle (by omega)
  let rWC := rWorkCtrl3Idle k_idle (by omega) rAct rWork hAW
  let F := rDA.embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1
  have hDAW : rDA.DisjointWires rWork := disjointWires_concat_left hAA hAW hAncW
  have hComp : rDA.compose ((selDataInAct kFull80).compose rCI) = rAct.compose rCI := by
    apply p3_qreg_ext
    intro idx
    rw [QRegister.compose_apply, QRegister.compose_apply, selDataInAct_apply,
        QRegister.concat_apply_left, QRegister.compose_apply]
  obtain ⟨hCA, hCB⟩ := rCtrl3IdleFull_projZero_comm_anchorSwap_and_barrel k_idle (by omega)
  have hAB_comm : (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
      ((selDataInAct kFull80).compose rCI).basisOutcomeProjector 0 =
      ((selDataInAct kFull80).compose rCI).basisOutcomeProjector 0 *
        (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 := by
    rw [Submonoid.coe_mul, Matrix.mul_assoc, hCB, ← Matrix.mul_assoc, hCA, Matrix.mul_assoc]
  have hF_ci : (rAct.compose rCI).basisOutcomeProjector 0 * F =
      F * (rAct.compose rCI).basisOutcomeProjector 0 := by
    rw [← hComp, QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
        ← QRegister.basisOutcomeProjector]
    dsimp only [F]
    rw [← rDA.embedMatrix_mul, ← rDA.embedMatrix_mul, hAB_comm]
  have hF_w : rWork.basisOutcomeProjector 0 * F = F * rWork.basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rDA) rWork hDAW _ 0).symm
  have hF_ext : rWC.basisOutcomeProjector 0 * F = F * rWC.basisOutcomeProjector 0 := by
    dsimp only [rWC]
    rw [rWorkCtrl3Idle, QRegExt.basisOutcomeProjector_concat_zero,
        Matrix.mul_assoc, hF_ci, ← Matrix.mul_assoc, hF_w, Matrix.mul_assoc]
  have hDataDisj : (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)).DisjointWires rWC :=
    HoistBorrow42ProjBridge.disjointWires_concat_right
      (hAW.compose_left _)
      (disjointWires_compose_of_disjoint rAct
        (rCoreSwapPG3Sum42PG7Full_disj_rCtrl3IdleFull k_idle off hk_off hoff))
  have hSumEq : rAct.compose rSum0 =
      (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)).compose selSum42InCoreSum42PG7 := by
    apply p3_qreg_ext
    intro s
    rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.compose_apply]
    exact congrArg rAct (rCoreSwapPG3Sum42PG7Full_selSum42 off hoff s).symm
  have hAncSumDisj : (rDA.compose selAncSum0InFull18).DisjointWires rWC := by
    rw [compose_selAncSum0InFull18_eq rAct rAnchor18 hAA]
    refine disjointWires_concat_left (QRegExt.disjointWires_symm (hAA.compose_left rSum0))
      (HoistBorrow42ProjBridge.disjointWires_concat_right hAncW (QRegExt.disjointWires_symm
        (hAA.compose_left _))) ?_
    rw [hSumEq]
    exact hDataDisj.compose_left selSum42InCoreSum42PG7
  have hAdd_ext : rWC.basisOutcomeProjector 0 * rDA.embedMatrix (uAdd0AncFull18⁻¹).1 =
      rDA.embedMatrix (uAdd0AncFull18⁻¹).1 * rWC.basisOutcomeProjector 0 := by
    have hEmbed : rDA.embedMatrix (uAdd0AncFull18⁻¹).1 =
        (rDA.compose selAncSum0InFull18).embedMatrix (uElec18Sum42Add⁻¹).1 := by
      rw [uAdd0AncFull18, InterWalkRSum42Hoist.embedUnitary_inv_symm,
          QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose]
    rw [hEmbed]
    exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rDA.compose
      selAncSum0InFull18))
      rWC hAncSumDisj (uElec18Sum42Add⁻¹).1 0).symm
  have hPG7Eq : rAct.compose rPG7Full =
      (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)).compose selPG7InCoreSum42PG7 := by
    apply p3_qreg_ext
    intro m
    rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.compose_apply]
    exact congrArg rAct (rCoreSwapPG3Sum42PG7Full_selPG7 off hoff m).symm
  have hAncPG7Disj : (rDA.compose selAncPG7InFull18).DisjointWires rWC := by
    rw [compose_selAncPG7InFull18_eq rAct rAnchor18 hAA]
    refine disjointWires_concat_left (QRegExt.disjointWires_symm (hAA.compose_left rPG7Full))
      (HoistBorrow42ProjBridge.disjointWires_concat_right hAncW (QRegExt.disjointWires_symm
        (hAA.compose_left _))) ?_
    rw [hPG7Eq]
    exact hDataDisj.compose_left selPG7InCoreSum42PG7
  have hQft_ext : rWC.basisOutcomeProjector 0 * rDA.embedMatrix uQft0AncFull18.1 =
      rDA.embedMatrix uQft0AncFull18.1 * rWC.basisOutcomeProjector 0 := by
    have hEmbedQ : rDA.embedMatrix uQft0AncFull18.1 =
        (rDA.compose selAncPG7InFull18).embedMatrix uExpQft25.1 := by
      rw [uQft0AncFull18, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose]
    rw [hEmbedQ]
    exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rDA.compose
      selAncPG7InFull18))
      rWC hAncPG7Disj uExpQft25.1 0).symm
  have hJunction_ext : rWC.basisOutcomeProjector 0 * rDA.embedMatrix (uJunctionAncFull18⁻¹).1 =
      rDA.embedMatrix (uJunctionAncFull18⁻¹).1 * rWC.basisOutcomeProjector 0 := by
    rw [uJunctionAncFull18_inv_eq, Submonoid.coe_mul, rDA.embedMatrix_mul]
    calc rWC.basisOutcomeProjector 0 *
            (rDA.embedMatrix uQft0AncFull18.1 * rDA.embedMatrix (uAdd0AncFull18⁻¹).1)
        = (rWC.basisOutcomeProjector 0 * rDA.embedMatrix uQft0AncFull18.1) *
            rDA.embedMatrix (uAdd0AncFull18⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = rDA.embedMatrix uQft0AncFull18.1 *
            (rWC.basisOutcomeProjector 0 * rDA.embedMatrix (uAdd0AncFull18⁻¹).1) := by
            rw [hQft_ext]; simp only [Matrix.mul_assoc]
      _ = (rDA.embedMatrix uQft0AncFull18.1 * rDA.embedMatrix (uAdd0AncFull18⁻¹).1) *
            rWC.basisOutcomeProjector 0 := by
            rw [hAdd_ext]; simp only [Matrix.mul_assoc]
  refine of_clean_fixedByWorkZero ?_
    (dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire_realizes_clean hk_off hoff hm172 B hB6 hB27 v
      rAct rAnchor18 rWork hAA hAW hAncW)
  change rWC.basisOutcomeProjector 0 *
    (rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
      (F * pRawCtrl3ExtOn k_idle (by omega) rAct rWork * G)) = _
  calc rWC.basisOutcomeProjector 0 *
        (rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          (F * pRawCtrl3ExtOn k_idle (by omega) rAct rWork * G))
      = (rWC.basisOutcomeProjector 0 * rDA.embedMatrix (uJunctionAncFull18⁻¹).1) *
          (F * pRawCtrl3ExtOn k_idle (by omega) rAct rWork * G) := by simp only [Matrix.mul_assoc]
    _ = rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          ((rWC.basisOutcomeProjector 0 * F) *
            pRawCtrl3ExtOn k_idle (by omega) rAct rWork * G) := by
          rw [hJunction_ext]; simp only [Matrix.mul_assoc]
    _ = rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          (F * (rWC.basisOutcomeProjector 0 *
            pRawCtrl3ExtOn k_idle (by omega) rAct rWork) * G) := by
          rw [hF_ext]; simp only [Matrix.mul_assoc]
    _ = rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          (F * pRawCtrl3ExtOn k_idle (by omega) rAct rWork * G) := by
          dsimp only [rWC]
          rw [rWorkCtrl3Idle_projZero_mul_pRawCtrl3ExtOn]

/-- `Cat` (`6 + k_idle` borrowed clean wires) open-seam 1-wire Stage B on `kFull80`. -/
noncomputable def dStageBOpenAnchorCat_borrowExt6IdleOneWire
    {Var : Type} {n mWork k_idle off : ℕ}
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (6 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork)
    (hAncW : rAnchor18.DisjointWires rWork) : DynamicCircuit Var n :=
  dAnchorStageBOpenSwap3967OfWorkOneWire B hB6 hB27 hm172 v
    (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)) rAnchor18
    (Leaf4Ext48TopStitch.rWorkGuardExt k_idle (by omega) rAct rWork hAW)
    (hAA.compose_left _)
    (HoistBorrow42ProjBridge.disjointWires_concat_right
      (hAW.compose_left _)
      (disjointWires_compose_of_disjoint rAct
        (rCoreSwapPG3Sum42PG7Full_disj_rExt6IdleFull k_idle off hk_off hoff)))
    (HoistBorrow42ProjBridge.disjointWires_concat_right hAncW (QRegExt.disjointWires_symm
      (hAA.compose_left _)))

private theorem dStageBOpenAnchorCat_borrowExt6IdleOneWire_count_toff
    {Var : Type} {n mWork k_idle off : ℕ}
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (6 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork)
    (hAncW : rAnchor18.DisjointWires rWork) :
    (dStageBOpenAnchorCat_borrowExt6IdleOneWire hk_off hoff hm172 B hB6 hB27 v
      rAct rAnchor18 rWork hAA hAW hAncW).count TOFF = 0 :=
  dAnchorStageBOpenSwap3967OfWorkOneWire_count_toff B hB6 hB27 hm172 v _ _ _ _ _ _


private theorem dStageBOpenAnchorCat_borrowExt6IdleOneWire_count_t_le_fused
    {Var : Type} {n mWork k_idle off : ℕ}
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (6 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAncW : rAnchor18.DisjointWires rWork) :
    (dStageBOpenAnchorCat_borrowExt6IdleOneWire hk_off hoff hm172 B hB6 hB27 v
      rAct rAnchor18 rWork hAA hAW hAncW).count T ≤
      stageBOneWireBoothOptAnchorT B ((mWork + (6 + k_idle)) - 34) - 164 -
        if kOneWire ((mWork + (6 + k_idle)) - 34) = 0 then 0 else 436 :=
  dAnchorStageBOpenSwap3967OfWorkOneWire_count_t_le_fused B hB6 hB27 hm172 v _ _ _ _ _ _

private theorem dStageBOpenAnchorCat_borrowExt6IdleOneWire_realizes_clean
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mWork k_idle off : ℕ} [NeZero (2 ^ n)]
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (6 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork)
    (hAncW : rAnchor18.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rAct.concat rAnchor18 hAA)
      (Leaf4Ext48TopStitch.rWorkGuardExt k_idle (by omega) rAct rWork hAW)
      (BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame
        (uStageBFull B hB6 hB27 * uJunctionRawFull))
      (dStageBOpenAnchorCat_borrowExt6IdleOneWire hk_off hoff hm172 B hB6 hB27 v
        rAct rAnchor18 rWork hAA hAW hAncW) := by
  have h0 := dAnchorStageBOpenSwap3967OfWorkOneWire_realizes B hB6 hB27 hm172 v
    (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)) rAnchor18
    (Leaf4Ext48TopStitch.rWorkGuardExt k_idle (by omega) rAct rWork hAW)
    (hAA.compose_left _)
    (HoistBorrow42ProjBridge.disjointWires_concat_right
      (hAW.compose_left _)
      (disjointWires_compose_of_disjoint rAct
        (rCoreSwapPG3Sum42PG7Full_disj_rExt6IdleFull k_idle off hk_off hoff)))
    (HoistBorrow42ProjBridge.disjointWires_concat_right hAncW (QRegExt.disjointWires_symm
      (hAA.compose_left _)))
  rw [← concat_compose_liftDataMeas rAct rAnchor18 hAA (rCoreSwapPG3Sum42PG7Full off hoff)] at h0
  have h1 := h0.widenActive
  have hUEq : (liftDataMeas (rCoreSwapPG3Sum42PG7Full off hoff)).embedUnitary
      (uAnchorStageBStream218PG7 B hB6 hB27 * uJunctionRawAncPG7) =
      BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame
        (uStageBFull B hB6 hB27 * uJunctionRawFull) := by
    rw [QRegister.embedUnitary_mul,
        liftDataMeas_rCoreSwapPG3Sum42PG7Full_uAnchorStageBStream218PG7 off hoff B hB6 hB27,
        uAnchorFrame_eq_p3_01,
        liftDataMeas_rCoreSwapPG3Sum42PG7Full_uJunctionRawAn off hoff,
        ← uAnchorFrame_uJunctionRawFull_eq,
        BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame_mul]
  rwa [hUEq] at h1

private theorem dStageBOpenAnchorCat_borrowExt6IdleOneWire_realizesOnProj_mid
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mWork k_idle off : ℕ} [NeZero (2 ^ n)]
    (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) (hm172 : 172 ≤ mWork + (6 + k_idle))
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork)
    (hAncW : rAnchor18.DisjointWires rWork)
    (G : Operator (2 ^ n)) :
    RealizesOnProj
      ((rAct.concat rAnchor18 hAA).embedMatrix (uJunctionAncFull18⁻¹).1 *
        ((rAct.concat rAnchor18 hAA).embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
          pRawHoistExtOn k_idle (by omega) rAct rWork * G))
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame
          (uStageBFull B hB6 hB27 * uJunctionRawFull)))
      (dStageBOpenAnchorCat_borrowExt6IdleOneWire hk_off hoff hm172 B hB6 hB27 v
        rAct rAnchor18 rWork hAA hAW hAncW) := by
  let rDA := rAct.concat rAnchor18 hAA
  let rEI := rExt6IdleFull k_idle (by omega)
  let rWG := Leaf4Ext48TopStitch.rWorkGuardExt k_idle (by omega) rAct rWork hAW
  let F := rDA.embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1
  have hDAW : rDA.DisjointWires rWork := disjointWires_concat_left hAA hAW hAncW
  have hComp : rDA.compose ((selDataInAct kFull80).compose rEI) = rAct.compose rEI := by
    apply p3_qreg_ext
    intro idx
    rw [QRegister.compose_apply, QRegister.compose_apply, selDataInAct_apply,
        QRegister.concat_apply_left, QRegister.compose_apply]
  obtain ⟨hCA, hCB⟩ := rExt6IdleFull_projZero_comm_anchorSwap_and_barrel k_idle (by omega)
  have hAB_comm : (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
      ((selDataInAct kFull80).compose rEI).basisOutcomeProjector 0 =
      ((selDataInAct kFull80).compose rEI).basisOutcomeProjector 0 *
        (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 := by
    rw [Submonoid.coe_mul, Matrix.mul_assoc, hCB, ← Matrix.mul_assoc, hCA, Matrix.mul_assoc]
  have hF_ei : (rAct.compose rEI).basisOutcomeProjector 0 * F =
      F * (rAct.compose rEI).basisOutcomeProjector 0 := by
    rw [← hComp, QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
        ← QRegister.basisOutcomeProjector]
    dsimp only [F]
    rw [← rDA.embedMatrix_mul, ← rDA.embedMatrix_mul, hAB_comm]
  have hF_w : rWork.basisOutcomeProjector 0 * F = F * rWork.basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rDA) rWork hDAW _ 0).symm
  have hF_ext : rWG.basisOutcomeProjector 0 * F = F * rWG.basisOutcomeProjector 0 := by
    dsimp only [rWG]
    rw [Leaf4Ext48TopStitch.rWorkGuardExt, QRegExt.basisOutcomeProjector_concat_zero,
        Matrix.mul_assoc, hF_ei, ← Matrix.mul_assoc, hF_w, Matrix.mul_assoc]
  have hDataDisj : (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)).DisjointWires rWG :=
    HoistBorrow42ProjBridge.disjointWires_concat_right
      (hAW.compose_left _)
      (disjointWires_compose_of_disjoint rAct
        (rCoreSwapPG3Sum42PG7Full_disj_rExt6IdleFull k_idle off hk_off hoff))
  have hSumEq : rAct.compose rSum0 =
      (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)).compose selSum42InCoreSum42PG7 := by
    apply p3_qreg_ext
    intro s
    rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.compose_apply]
    exact congrArg rAct (rCoreSwapPG3Sum42PG7Full_selSum42 off hoff s).symm
  have hAncSumDisj : (rDA.compose selAncSum0InFull18).DisjointWires rWG := by
    rw [compose_selAncSum0InFull18_eq rAct rAnchor18 hAA]
    refine disjointWires_concat_left (QRegExt.disjointWires_symm (hAA.compose_left rSum0))
      (HoistBorrow42ProjBridge.disjointWires_concat_right hAncW (QRegExt.disjointWires_symm
        (hAA.compose_left _))) ?_
    rw [hSumEq]
    exact hDataDisj.compose_left selSum42InCoreSum42PG7
  have hAdd_ext : rWG.basisOutcomeProjector 0 * rDA.embedMatrix (uAdd0AncFull18⁻¹).1 =
      rDA.embedMatrix (uAdd0AncFull18⁻¹).1 * rWG.basisOutcomeProjector 0 := by
    have hEmbed : rDA.embedMatrix (uAdd0AncFull18⁻¹).1 =
        (rDA.compose selAncSum0InFull18).embedMatrix (uElec18Sum42Add⁻¹).1 := by
      rw [uAdd0AncFull18, InterWalkRSum42Hoist.embedUnitary_inv_symm,
          QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose]
    rw [hEmbed]
    exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rDA.compose
      selAncSum0InFull18))
      rWG hAncSumDisj (uElec18Sum42Add⁻¹).1 0).symm
  have hPG7Eq : rAct.compose rPG7Full =
      (rAct.compose (rCoreSwapPG3Sum42PG7Full off hoff)).compose selPG7InCoreSum42PG7 := by
    apply p3_qreg_ext
    intro m
    rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.compose_apply]
    exact congrArg rAct (rCoreSwapPG3Sum42PG7Full_selPG7 off hoff m).symm
  have hAncPG7Disj : (rDA.compose selAncPG7InFull18).DisjointWires rWG := by
    rw [compose_selAncPG7InFull18_eq rAct rAnchor18 hAA]
    refine disjointWires_concat_left (QRegExt.disjointWires_symm (hAA.compose_left rPG7Full))
      (HoistBorrow42ProjBridge.disjointWires_concat_right hAncW (QRegExt.disjointWires_symm
        (hAA.compose_left _))) ?_
    rw [hPG7Eq]
    exact hDataDisj.compose_left selPG7InCoreSum42PG7
  have hQft_ext : rWG.basisOutcomeProjector 0 * rDA.embedMatrix uQft0AncFull18.1 =
      rDA.embedMatrix uQft0AncFull18.1 * rWG.basisOutcomeProjector 0 := by
    have hEmbedQ : rDA.embedMatrix uQft0AncFull18.1 =
        (rDA.compose selAncPG7InFull18).embedMatrix uExpQft25.1 := by
      rw [uQft0AncFull18, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose]
    rw [hEmbedQ]
    exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rDA.compose
      selAncPG7InFull18))
      rWG hAncPG7Disj uExpQft25.1 0).symm
  have hJunction_ext : rWG.basisOutcomeProjector 0 * rDA.embedMatrix (uJunctionAncFull18⁻¹).1 =
      rDA.embedMatrix (uJunctionAncFull18⁻¹).1 * rWG.basisOutcomeProjector 0 := by
    rw [uJunctionAncFull18_inv_eq, Submonoid.coe_mul, rDA.embedMatrix_mul]
    calc rWG.basisOutcomeProjector 0 *
            (rDA.embedMatrix uQft0AncFull18.1 * rDA.embedMatrix (uAdd0AncFull18⁻¹).1)
        = (rWG.basisOutcomeProjector 0 * rDA.embedMatrix uQft0AncFull18.1) *
            rDA.embedMatrix (uAdd0AncFull18⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = rDA.embedMatrix uQft0AncFull18.1 *
            (rWG.basisOutcomeProjector 0 * rDA.embedMatrix (uAdd0AncFull18⁻¹).1) := by
            rw [hQft_ext]; simp only [Matrix.mul_assoc]
      _ = (rDA.embedMatrix uQft0AncFull18.1 * rDA.embedMatrix (uAdd0AncFull18⁻¹).1) *
            rWG.basisOutcomeProjector 0 := by
            rw [hAdd_ext]; simp only [Matrix.mul_assoc]
  refine of_clean_fixedByWorkZero ?_
    (dStageBOpenAnchorCat_borrowExt6IdleOneWire_realizes_clean hk_off hoff hm172 B hB6 hB27 v
      rAct rAnchor18 rWork hAA hAW hAncW)
  change rWG.basisOutcomeProjector 0 *
    (rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
      (F * pRawHoistExtOn k_idle (by omega) rAct rWork * G)) = _
  calc rWG.basisOutcomeProjector 0 *
        (rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          (F * pRawHoistExtOn k_idle (by omega) rAct rWork * G))
      = (rWG.basisOutcomeProjector 0 * rDA.embedMatrix (uJunctionAncFull18⁻¹).1) *
          (F * pRawHoistExtOn k_idle (by omega) rAct rWork * G) := by simp only [Matrix.mul_assoc]
    _ = rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          ((rWG.basisOutcomeProjector 0 * F) *
            pRawHoistExtOn k_idle (by omega) rAct rWork * G) := by
          rw [hJunction_ext]; simp only [Matrix.mul_assoc]
    _ = rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          (F * (rWG.basisOutcomeProjector 0 *
            pRawHoistExtOn k_idle (by omega) rAct rWork) * G) := by
          rw [hF_ext]; simp only [Matrix.mul_assoc]
    _ = rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          (F * pRawHoistExtOn k_idle (by omega) rAct rWork * G) := by
          dsimp only [rWG]
          rw [rWorkGuardExt_projZero_mul_pRawHoistExtOn]

end ParAuxOpenOneWireVariants
end Part1_OpenOneWireStageB

/-! ## Section 2: Fused Open-QFT 1-Wire `FoldedPass123CircuitSpec_mWork` (`48054 -> 47617`) -/


attribute [local irreducible]
  SpecsAux.SpecMirror.systemQubits
  PosSlots24BranchConcrete.posCoreWires

/-! ## Section 3: Sites 2 & 3 Bell-18 Top-Splice (`17,696 T` Outer Pair) -/

section Part3_Bell18Sites2And3

set_option backward.isDefEq.respectTransparency true
set_option genSizeOf false
set_option exponentiation.threshold 256

set_option exponentiation.threshold 256

open _root_.QuantumComputation.Specs.StoppingPowerSolution.DyadicQft64
  (sList sDagList count_sList_toff count_sList_t count_sDagList_toff count_sDagList_t)
open FullSysCatSegmentBridge (disjointWires_concat_left)
open InterWalkRSum42Hoist (kFull80 rCoreFull)
open BoothOpt_P4_10_TwoLoadHeldRowTrueSwap
  (selDataInAct selMeasInAct selDataInAct_disj_selMeasInAct concat_compose_selDataInAct)
open MeasureBranchHadamardSem (ket bit_cases matrix_ext_ket)
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open ElecHadConjLoadAndTrueSwapComp
  (Slot18Lens xor18 lensLoadPerm lensWritePerm lensSwapPerm)
open ElecHadTrueSwapLocalCompClosure
  (uLensSwap lensSwapEquiv liftPairIdx uLensLoad uLensWrite lensLoadEquiv lensWriteEquiv
   uLensWrite_mul_uLensLoad_projZero_eq_uLensSwap)
open ZeroHypSlot0CommAndHMidClosure
  (P_slot0 P_slot0_eq_diagonal)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap
  (rFullSysElecSlot coinBarrelFastOnDataLens)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (L_anchor P_anc0 uAnchorFrame uBarrelFastAct uAnchorLensSwap uAnchorLensSwap_mul_self
   uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct
   uSlot0MeasSwap_mul_uBarrelFastAct_eq_uBarrelFastAct_mul_uAnchorLensSwap
   dPass1Anchor dPass1Anchor_count_toff dPass1Anchor_count_t dPass1Anchor_realizesOnProj
   dPass3Anchor dPass3Anchor_count_toff dPass3Anchor_count_t dPass3Anchor_realizesOnProj
   cS18 cSDag18 cSK cSDagK cPreDiagCliffordAnchor cPreDiagCliffordAnchorInv
   dPreDiagCliffordAnchor_realizesOnProj dPreDiagCliffordAnchorInv_realizesOnProj
   realizesOnProj_mul_right selDataInAct_embedMatrix_comm_P_anc0
   uAnchorLensSwap_mul_data_P_anc0 uAnchorLensSwap_conj_uAnchorFrame_four)
open BoothOpt_FastAnchorOuterAndStageBShave
  (pi_single_eq_ket embedUnitary_permUnitary_mulVec_single_fast
   concat_replaceIndex_liftPairIdx_fast embed_intertwine_op_fast)


private theorem ket_eq_single_loc {n : ℕ} (β : BitAssignment n) :
    ket β = Pi.single ((basisBitsEquiv n).symm β) 1 := rfl

private def toSlotK18 {kData : ℕ} (L : Slot18Lens kData) :
    Bell18TeleportCore.SlotKLens 18 kData :=
  ⟨L.tbl, L.updSlot, L.get_put, L.put_get, L.put_put⟩

private theorem toSlotK18_updSlot {kData : ℕ} (L : Slot18Lens kData) :
    (toSlotK18 L).updSlot = L.updSlot := rfl

private theorem toSlotK18_tbl {kData : ℕ} (L : Slot18Lens kData) :
    (toSlotK18 L).tbl = L.tbl := rfl

private theorem tcXorK18_eq_xor18 (a b : Fin (2 ^ 18)) :
    Bell18TeleportCore.xorK a b = xor18 a b := by
  apply eq_of_basisBits_eq; intro j
  simp [Bell18TeleportCore.xorK, xor18, basisBitsEquiv]

private theorem tcEmbed_uLensLoad_eq {n kData : ℕ}
    (rD : QRegister kData n) (rM : QRegister 18 n) (hDM : rD.DisjointWires rM)
    (L : Slot18Lens kData) :
    (rD.concat rM hDM).embedUnitary (Bell18TeleportCore.uLensLoad (toSlotK18 L)) =
      (rD.concat rM hDM).embedUnitary (uLensLoad L) := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [ket_eq_single_loc β, Bell18TeleportCore.embedUnitary_uLensLoad_mulVec_single]
  dsimp only [uLensLoad, toSlotK18]
  rw [embedUnitary_permUnitary_mulVec_single_fast]
  dsimp only [lensLoadEquiv]; simp only [Equiv.ofBijective_apply]
  rw [concat_replaceIndex_liftPairIdx_fast rD rM hDM (lensLoadPerm L)]
  dsimp only [lensLoadPerm]
  rw [tcXorK18_eq_xor18, QRegister.replaceIndex_extractIndex]

private theorem tcEmbed_uLensWrite_eq {n kData : ℕ}
    (rD : QRegister kData n) (rM : QRegister 18 n) (hDM : rD.DisjointWires rM)
    (L : Slot18Lens kData) :
    (rD.concat rM hDM).embedUnitary (Bell18TeleportCore.uLensWrite (toSlotK18 L)) =
      (rD.concat rM hDM).embedUnitary (uLensWrite L) := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [ket_eq_single_loc β, Bell18TeleportCore.embedUnitary_uLensWrite_mulVec_single]
  dsimp only [uLensWrite, toSlotK18]
  rw [embedUnitary_permUnitary_mulVec_single_fast]
  dsimp only [lensWriteEquiv]; simp only [Equiv.ofBijective_apply]
  rw [concat_replaceIndex_liftPairIdx_fast rD rM hDM (lensWritePerm L)]
  dsimp only [lensWritePerm]
  rw [tcXorK18_eq_xor18]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  conv_rhs => rw [QRegister.replaceIndex_comm_of_disjoint rM rD (QRegExt.disjointWires_symm hDM)]
  rw [QRegister.replaceIndex_extractIndex]

private theorem tcEmbed_uLensSwap_eq {n kData : ℕ}
    (rD : QRegister kData n) (rM : QRegister 18 n) (hDM : rD.DisjointWires rM)
    (L : Slot18Lens kData) :
    (rD.concat rM hDM).embedUnitary (Bell18TeleportCore.uLensSwap (toSlotK18 L)) =
      (rD.concat rM hDM).embedUnitary (uLensSwap L) := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [ket_eq_single_loc β, Bell18TeleportCore.embedUnitary_uLensSwap_mulVec_single]
  dsimp only [uLensSwap, toSlotK18]
  rw [embedUnitary_permUnitary_mulVec_single_fast]
  dsimp only [lensSwapEquiv]; simp only [Equiv.ofBijective_apply]
  rw [concat_replaceIndex_liftPairIdx_fast rD rM hDM (lensSwapPerm L)]
  rfl

private theorem tcULensLoad_mul_write_eq {kData : ℕ} (L : Slot18Lens kData) :
    Bell18TeleportCore.uLensWrite (toSlotK18 L) *
      Bell18TeleportCore.uLensLoad (toSlotK18 L) =
      uLensWrite L * uLensLoad L := by
  let rId := QRegExt.idReg (kData + 18)
  have hCat : (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct kData).concat
      (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selMeasInAct kData)
      (selDataInAct_disj_selMeasInAct kData) = rId := by
    apply InterWalkRSum42Hoist.qreg_ext; intro i
    refine Fin.addCases (motive := fun i ↦
      ((BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct kData).concat
        (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selMeasInAct kData)
        (selDataInAct_disj_selMeasInAct kData)) i = rId i)
      (fun a ↦ ?_) (fun b ↦ ?_) i
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (by
        simp [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct,
          BoothOpt_StageBPartnerCoreShave.selDataInAct,
          QRegister.block,
          rId, QRegExt.idReg])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by
        simp [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selMeasInAct, QRegister.block,
          rId, QRegExt.idReg])
  have hEmb : ∀ u₁ u₂ : Unitary (2 ^ (kData + 18)),
      rId.embedUnitary u₁ = rId.embedUnitary u₂ → u₁ = u₂ := by
    intro u₁ u₂ h
    simpa [rId, NuclearTwistRealizes.embedUnitary_idReg_eq] using h
  apply hEmb;
  rw [← hCat, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
    tcEmbed_uLensWrite_eq, tcEmbed_uLensLoad_eq]

private theorem tcULensSwap_eq {kData : ℕ} (L : Slot18Lens kData) :
    Bell18TeleportCore.uLensSwap (toSlotK18 L) = uLensSwap L := by
  let rId := QRegExt.idReg (kData + 18)
  have hCat : (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct kData).concat
      (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selMeasInAct kData)
      (selDataInAct_disj_selMeasInAct kData) = rId := by
    apply InterWalkRSum42Hoist.qreg_ext; intro i
    refine Fin.addCases (motive := fun i ↦
      ((BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct kData).concat
        (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selMeasInAct kData)
        (selDataInAct_disj_selMeasInAct kData)) i = rId i)
      (fun a ↦ ?_) (fun b ↦ ?_) i
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (by
        simp [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct,
          BoothOpt_StageBPartnerCoreShave.selDataInAct,
          QRegister.block,
          rId, QRegExt.idReg])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by
        simp [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selMeasInAct, QRegister.block,
          rId, QRegExt.idReg])
  have hEmb : ∀ u₁ u₂ : Unitary (2 ^ (kData + 18)),
      rId.embedUnitary u₁ = rId.embedUnitary u₂ → u₁ = u₂ := by
    intro u₁ u₂ h
    simpa [rId, NuclearTwistRealizes.embedUnitary_idReg_eq] using h
  apply hEmb
  rw [← hCat, tcEmbed_uLensSwap_eq]

private theorem tcPSlot0_eq {kData : ℕ} (L : Slot18Lens kData) :
    Bell18TeleportCore.P_slot0 (toSlotK18 L) = P_slot0 L := by
  have hMeas : Bell18TeleportCore.selMeasInAct 18 kData =
      StageADeconstrCore.selMeasInAct kData := by
    apply InterWalkRSum42Hoist.qreg_ext; intro j
    exact Fin.ext (by
      simp [Bell18TeleportCore.selMeasInAct,
        StageADeconstrCore.selMeasInAct, QRegister.block])
  dsimp only [Bell18TeleportCore.P_slot0, P_slot0]
  rw [tcULensSwap_eq L, hMeas]

/-- Trivial `18`-bit identity lens on `Fin (2 ^ 18)` for `(rHeld, rAnc)` XOR. -/
private def idSlotK18 : Bell18TeleportCore.SlotKLens 18 18 where
  tbl d := d
  updSlot _ v := v
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl

/-- Abstract lens conjugation: `S_anc * W_held * S_anc = Load(rHeld -> rAnc)`,
disjoint from `rD`! -/
private theorem uLensSwap_conj_uLensWrite_eq_loadHeldAnc {n kData : ℕ}
    (rD : QRegister kData n) (rAnc rHeld : QRegister 18 n)
    (hDA : rD.DisjointWires rAnc) (hDH : rD.DisjointWires rHeld)
    (hAH : rAnc.DisjointWires rHeld) (L : Bell18TeleportCore.SlotKLens 18 kData) :
    let S := (rD.concat rAnc hDA).embedUnitary (Bell18TeleportCore.uLensSwap L)
    let W := (rD.concat rHeld hDH).embedUnitary (Bell18TeleportCore.uLensWrite L)
    S * W * S =
      (rHeld.concat rAnc (QRegExt.disjointWires_symm hAH)).embedUnitary
        (Bell18TeleportCore.uLensLoad idSlotK18) := by
  intro S W
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [ket_eq_single_loc β]
  generalize (basisBitsEquiv n).symm β = g₀
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [Bell18TeleportCore.embedUnitary_uLensSwap_mulVec_single,
      Bell18TeleportCore.embedUnitary_uLensWrite_mulVec_single,
      Bell18TeleportCore.embedUnitary_uLensSwap_mulVec_single,
      Bell18TeleportCore.embedUnitary_uLensLoad_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  let g₁ := rAnc.replaceIndex (rD.replaceIndex g₀
    (L.updSlot (rD.extractIndex g₀) (rAnc.extractIndex g₀))) (L.tbl (rD.extractIndex g₀))
  have hD₁ : rD.extractIndex g₁ = L.updSlot (rD.extractIndex g₀) (rAnc.extractIndex g₀) := by
    dsimp only [g₁]
    rw [QRegister.extractIndex_replaceIndex_of_disjoint rD rAnc hDA,
        QRegister.extractIndex_replaceIndex]
  have hA₁ : rAnc.extractIndex g₁ = L.tbl (rD.extractIndex g₀) := by
    dsimp only [g₁]; rw [QRegister.extractIndex_replaceIndex]
  have hH₁ : rHeld.extractIndex g₁ = rHeld.extractIndex g₀ := by
    dsimp only [g₁]
    rw [QRegister.extractIndex_replaceIndex_of_disjoint rHeld rAnc (QRegExt.disjointWires_symm hAH),
        QRegister.extractIndex_replaceIndex_of_disjoint rHeld rD (QRegExt.disjointWires_symm hDH)]
  let vNew := Bell18TeleportCore.xorK (rAnc.extractIndex g₀) (rHeld.extractIndex g₀)
  have hUpd₁ : L.updSlot (rD.extractIndex g₁)
      (Bell18TeleportCore.xorK (L.tbl (rD.extractIndex g₁))
      (rHeld.extractIndex g₁)) = L.updSlot (rD.extractIndex g₀) vNew := by
    rw [hD₁, hH₁, L.get_put, L.put_put]
  let g₂ := rD.replaceIndex g₁ (L.updSlot (rD.extractIndex g₀) vNew)
  have hG₂ : rD.replaceIndex g₁ (L.updSlot (rD.extractIndex g₁)
      (Bell18TeleportCore.xorK (L.tbl (rD.extractIndex g₁)) (rHeld.extractIndex g₁))) = g₂ := by
    rw [hUpd₁]
  rw [hG₂]
  have hD₂ : rD.extractIndex g₂ = L.updSlot (rD.extractIndex g₀) vNew := by
    dsimp only [g₂]; rw [QRegister.extractIndex_replaceIndex]
  have hA₂ : rAnc.extractIndex g₂ = L.tbl (rD.extractIndex g₀) := by
    dsimp only [g₂]
    rw [QRegister.extractIndex_replaceIndex_of_disjoint rAnc rD (QRegExt.disjointWires_symm hDA),
      hA₁]
  rw [hD₂, hA₂, L.put_put, L.put_get, L.get_put]
  dsimp only [g₂, g₁, idSlotK18]
  rw [QRegister.replaceIndex_replaceIndex,
      QRegister.replaceIndex_comm_of_disjoint rD rAnc hDA,
      QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_replaceIndex,
      QRegister.replaceIndex_extractIndex]

/-- Universal exact commutation: EVERY anchor-framed unitary `uAnchorFrame U` commutes with
`Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)` (`0` hypotheses on `U`)! -/
private theorem uAnchorFrame_comm_uBellSlot {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc) (hAH : rAct.DisjointWires rHeld)
    (hAnH : rAnc.DisjointWires rHeld) (U : Unitary (2 ^ kFull80)) :
    (rAct.concat rAnc hAA).embedUnitary (uAnchorFrame U) *
        Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor) =
      Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor) *
        (rAct.concat rAnc hAA).embedUnitary (uAnchorFrame U) := by
  let rDA := rAct.concat rAnc hAA
  let B_core := rCoreFull.embedUnitary
    (CoinDispatchedBarrel288.uBarrelFast (le_refl 80))
  let U' : Unitary (2 ^ kFull80) := B_core * U * B_core
  have hFrameEq : rDA.embedUnitary (uAnchorFrame U) =
      rDA.embedUnitary (Bell18TeleportCore.uLensSwap (toSlotK18 L_anchor)) *
        rAct.embedUnitary U' *
        rDA.embedUnitary (Bell18TeleportCore.uLensSwap (toSlotK18 L_anchor)) := by
    have hLoc : uAnchorFrame U =
        uAnchorLensSwap *
          (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct kFull80).embedUnitary U' *
          uAnchorLensSwap := by
      dsimp only [uAnchorFrame, U']
      rw [uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct,
          uSlot0MeasSwap_mul_uBarrelFastAct_eq_uBarrelFastAct_mul_uAnchorLensSwap]
      have hSelEq :
          StageADeconstrCore.selDataInAct kFull80 =
            BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct kFull80 := by
        apply InterWalkRSum42Hoist.qreg_ext; intro i
        exact Fin.ext (by
          simp [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct,
            StageADeconstrCore.selDataInAct,
            BoothOpt_StageBPartnerCoreShave.selDataInAct,
            QRegister.block])
      have hB : uBarrelFastAct =
          (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct kFull80).embedUnitary B_core := by
        dsimp only [uBarrelFastAct, B_core]
        rw [← QRegister.embedUnitary_compose]; rfl
      rw [hSelEq, hB, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul]
      simp only [mul_assoc]
    rw [hLoc, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
        ← QRegister.embedUnitary_compose, concat_compose_selDataInAct]
    dsimp only [uAnchorLensSwap]
    rw [tcEmbed_uLensSwap_eq]
  let S := rDA.embedUnitary (Bell18TeleportCore.uLensSwap (toSlotK18 L_anchor))
  let W := (rAct.concat rHeld hAH).embedUnitary
    (Bell18TeleportCore.uLensWrite (toSlotK18 L_anchor))
  have hSS : S * S = 1 := by
    dsimp only [S]
    rw [tcEmbed_uLensSwap_eq, ← QRegister.embedUnitary_mul]
    change rDA.embedUnitary (uAnchorLensSwap * uAnchorLensSwap) = 1
    rw [uAnchorLensSwap_mul_self, QRegister.embedUnitary_one]
  have hDisjHA : rAct.DisjointWires (rHeld.concat rAnc (QRegExt.disjointWires_symm hAnH)) :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left (QRegExt.disjointWires_symm hAnH)
      (QRegExt.disjointWires_symm hAH) (QRegExt.disjointWires_symm hAA)))
  have hCommSW : rAct.embedUnitary U' * (S * W * S) = (S * W * S) * rAct.embedUnitary U' := by
    rw [uLensSwap_conj_uLensWrite_eq_loadHeldAnc rAct rAnc rHeld hAA hAH hAnH]
    exact Subtype.ext (rAct.embedMatrix_comm_of_disjoint _ hDisjHA U'.1 _)
  have hCommW : rDA.embedUnitary (uAnchorFrame U) * W =
      W * rDA.embedUnitary (uAnchorFrame U) := by
    rw [hFrameEq]
    have h1 : (S * rAct.embedUnitary U' * S) * W =
        S * (rAct.embedUnitary U' * (S * W * S)) * S := by
      nth_rw 1 [← mul_one ((S * rAct.embedUnitary U' * S) * W)]
      rw [← hSS]; simp only [mul_assoc]
    have h2 : S * ((S * W * S) * rAct.embedUnitary U') * S =
        W * (S * rAct.embedUnitary U' * S) := by
      have hAssoc : S * ((S * W * S) * rAct.embedUnitary U') * S =
          (S * S) * W * (S * rAct.embedUnitary U' * S) := by simp only [mul_assoc]
      rw [hAssoc, hSS, one_mul]
    rw [h1, hCommSW, h2]
  have hDAH : rDA.DisjointWires rHeld := disjointWires_concat_left hAA hAH hAnH
  have hCommH : rDA.embedUnitary (uAnchorFrame U) * (Bell18TeleportCore.cHadReg rHeld).eval =
      (Bell18TeleportCore.cHadReg rHeld).eval * rDA.embedUnitary (uAnchorFrame U) := by
    apply Subtype.ext
    exact (Bell18TeleportCore.cHadReg_comm_embedMatrix_of_disjoint rHeld rDA
      (QRegExt.disjointWires_symm hDAH)
      (uAnchorFrame U).1).symm
  dsimp only [Bell18TeleportCore.uBellSlot]
  rw [← mul_assoc, hCommW, mul_assoc, hCommH, ← mul_assoc]

/-! ### Section 3B: Site 2 — `1,292 T` Gated-Tree `dPostBell18Fast` Closure -/

section Part3B_PostBell18Fast

open _root_ (diagSignUnitary f2Parity)
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (writeRegProg writeRegProg_apply_reg writeRegProg_apply_of_not_mem eval_onRegister_prog_ket)
open FullSysCatSegmentBridge (fullSysCoreWires)
open CoinDispatchedBarrel288.Internal (CliffProg)
open PosSlots24BranchConcrete (posCoreWires rElecSlot)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (rElecAllPos)
open AnchorSwap0Split133
  (p2d_ketPredProj p2d_ketPredProj_conjTranspose p2d_ketPredProj_mul_ket
   p2d_ketPredProj_mul_imp p2d_RealizesConstCleanUnitary)
open MultiBankWStateRouter
  (SupportedOn SubspaceStep WRouterDisj uOneHotToggle uOneHotToggle_mulVec_ket
   toggleOneHotBits idxValD idxValD_lt_two_pow)
open ParticleOneHotWState
  (ketPredProj_comm_of_preserves supportedOn_of_ketPredProj_mul_eq idxValD_eq_bitsVal)
open Pass1BarrelIdxLoad273 (qreg_disjoint_concat_left)
open Pass1BarrelIdxPebbled273
open BoothOpt_P4_10_TwoLoadHeldRowTrueSwap (concat_compose_selMeasInAct)
open BoothOpt_02_Cached64x4TrueSwapEngine
  (S_slot0Lens CliffWritesAbove)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap
  (selHadOfPosCore rDataElec_mem_selHadOfPosCore coinBarrelFastSlot18Lens)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (selLiftAct concat_compose_selLiftAct uLensWrite_liftSlot18Lens uLensSwap_liftSlot18Lens
   P_slot0_liftSlot18Lens P_slot0_conjTranspose P_slot0_mul_E_anchorLoc E_anchorLoc E_anchor)
open StageBFastInnerPartnerShift
  (dFixHole218 dFixHole218_count_toff dFixHole218_count_t_le)
open BoothOpt_StageBPartnerCoreShave
  (ValidWCohGateIn ValidWCohGateClean
   subspaceStep_wStateComputeCohGate1 subspaceStep_wStateUncomputeCohGate1)
open BoothOpt_FastAnchorOuterAndStageBShave
  (DiagCtxWG DiagCtxWGWritesAbove DiagCtxWGCommutesWith toDynWG rEnIdx9 selCoreEI
   fastEILens fastEISlotReg sFnEI hsFnEI_had hTblBit_fastEILens compose_replaceIndex_eq_fast
   embedMatrix_p_slot0_mulVec_ket wRouterDisj_onRegister
   rComb93 ctxFastTrees93 invTreesIn93 invHole93 invHole93_iff_invHoleSlot218
   p2d_ketPredProj_congr_fast ctxFastTrees93_writesAbove18 validAtWith_ctxFastTrees93
   fast64_hdLo fast64_hdHi cZeroFallback93 invHoleSlot218
   dWrapFast68 count_dWrapFast68_toff count_dWrapFast68_t dWrapFast68_realizes_gen
   rScr75 disj_rScr75_right rPeb10_disj_rScr75 vLinUnitary vLinUnitary_mulVec_ket
   vLinUnitary_intertwines_write vLinUnitary_intertwines_swap
   fastLinState fastLinState_extract_and_tbl fastLinState_invTrees_and_sFnEI
   hCombPres_mul hCombPres_fastEILens_write hCombPres_fastEILens_swap
   rComb93_above18_not_mem_actEI cPreLin93 rComb93_enIdx9 rComb93_scr75
   diagCtxWGWritesAbove_to_commutesWith hasCleanTailFrom_embedMatrix_mul_proj0
   hoist_realizesOnProj_of_peb)

open PartnerAndAnchorSlot18LensAndMidBA
  (mkSlot18LensOfSlotReg)

section InlinedFix218_FixHole218
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open _root_ (diagSignUnitary diagSignUnitary_false f2Parity sign_f2Parity_eq_prod)
open MeasureBranchHadamardSem (ket bitSign sqrtHalf bit_cases eval_seq_mulVec ket_H ket_X ket_CNOT
  ket_TOFF matrix_ext_ket)
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg
open AnchorSwap0Split133
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_concat_left)
open CoinDispatchedBarrel288
open FastCoinBarrelDecoder279
open Pass1BarrelIdxLoad273
open Pass1BarrelIdxPebbled273
open PosSlots24BranchConcrete (posCoreWires rElecSlot)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open ElecHadTrueSwapHCompClosure (uWriteSub)
open PartnerAndAnchorSlot18LensAndMidBA (mkSlot18LensOfSlotReg)
open ElecHadTrueSwapLocalCompClosure (uLensLoad uLensWrite uLensSwap
  uLensWrite_mul_uLensSwap_projZero_eq_setTableOp)
open ZeroHypSlot0CommAndHMidClosure (P_slot0)
open BoothOpt_02_Cached64x4TrueSwapEngine
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (selPosInFullSys rFullSysElecSlot selHadOfPosCore
  rDataElec_mem_selHadOfPosCore selMeasInAct_mem_selHadOfPosCore
  uWriteSub_uLensLoad_eq_uLensWrite_of_slotReg)
open StageBFastInnerPartnerShift (cLoad4Rows218 cBranchFix4Rows218Aux dKick1Bit218
  dPhaseKickHole218Aux dPhaseKickHole218 dLoadHole218 dWriteHole218 dWriteHole218_count_toff
  dWriteHole218_count_t dPreHole218 count_measureXResetAndBranch_TOFF_le_noFintype
  count_measureXResetAndBranch_T_le_noFintype semigroup_comm2_idem monoid_invol_conj
  semigroup_write_conj matrix_post_core matrix_post_tail cBranchFix4Rows218Aux_eval_ket
  cLoad4Rows218_eval_ket dFixHole218 dFixHole218_count_t_le dFixHole218_count_toff dPostHole218
  dZKick1BitHole218 rowBit218 rowBit218_at_active)
/-- Single-bit `Z` kick unitary on coordinate `j₀` of a generic `218`-slot selector `sFn`. -/
private noncomputable def uZKick1BitSlot218 {n kData : ℕ} (j₀ : Fin 18)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (sFn : BitAssignment kData → Fin 218) : Unitary (2 ^ n) :=
  diagSignUnitary fun g ↦
    let β := basisBits n g
    let s₀ := sFn (fun u ↦ β (rData u))
    decide (β (rElecSlot (rData.compose selCore) s₀ j₀) = 1)
open Classical in
private theorem dZKick1BitHole218_slot_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var) (j₀ : Fin 18)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (sFn : BitAssignment kData → Fin 218) (rScr : QRegister mScr n)
    (hCS : (rData.compose selCore).DisjointWires rScr) (S_ext : BitAssignment n → Prop) :
    let P_hole := p2d_ketPredProj (fun β ↦ S_ext β ∧ invHoleSlot218 hm rData sFn rScr β)
    p2d_RealizesConstCleanUnitary P_hole
      (dZKick1BitHole218 hm v j₀ (rData.compose selCore) rScr hCS)
      (uZKick1BitSlot218 j₀ rData selCore sFn) := by
  intro P_hole
  let rCore := rData.compose selCore
  let rRow4 : QRegister 4 n := p2dSubReg rScr 70 4 (by omega)
  let P_lo := p2d_ketPredProj (fun α : BitAssignment n ↦
    ∃ l₀ < 64, ∀ l : Fin 64, α (rScr ⟨l.val, by omega⟩) = if l.val = l₀ then 1 else 0)
  have hcPre : ∀ (β : BitAssignment n), invHoleSlot218 hm rData sFn rScr β →
      let s₀ := sFn (fun u ↦ β (rData u))
      have hs := s₀.isLt
      let hl₀ : s₀.val % 64 < 64 := Nat.mod_lt _ (by decide)
      let vals := rowBit218 rCore j₀ β (s₀.val % 64) hl₀
      (cLoad4Rows218 hm j₀ rCore rScr hCS ;;ᶜ cCz4RowHi hm rScr).eval.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (β (rElecSlot rCore s₀ j₀)).val) •
          ket (p2d_writeReg β rRow4 vals) := by
    intro β ⟨hLo, hHi, hPar0, hRow0, _⟩ s₀ hs hl₀ vals
    let α₁ := p2d_writeReg β rRow4 vals
    have hh₀ : s₀.val / 64 < 4 := by omega
    have hα₁_hi : ∀ h : Fin 4, α₁ (rScr ⟨64 + h.val, by omega⟩) = if h.val = s₀.val / 64 then 1 else
      0 := fun h ↦ by
      dsimp only [α₁]
      rw [p2d_writeReg_apply_of_not_mem _ _ _ _
        (fun ⟨r, hr⟩ ↦ by
          have hrEq : rRow4 r = rScr ⟨70 + r.val, by omega⟩ :=
            congrArg rScr.wires (Fin.ext (by dsimp [rRow4, p2dSubReg]))
          exact rSub_ne_of_ne rScr (by omega) (by omega) (by omega) (hrEq ▸ hr).symm)]
      exact hHi h
    rw [eval_seq_mulVec,
        cLoad4Rows218_eval_ket hm j₀ rCore rScr hCS β hRow0 hPar0 (s₀.val % 64) hl₀ hLo,
        cCz4RowHi_eval_ket hm rScr α₁ (s₀.val / 64) hh₀ hα₁_hi]
    change ((-1 : ℂ) ^ (p2d_writeReg β rRow4 vals (rRow4 ⟨s₀.val / 64, hh₀⟩)).val) • ket α₁ = _
    rw [p2d_writeReg_apply_reg β rRow4 vals ⟨s₀.val / 64, hh₀⟩]
    dsimp only [vals]
    rw [rowBit218_at_active rCore j₀ β s₀]
  refine p2d_RealizesConstCleanUnitary_seq_measureXReset v rRow4
    (p2d_ketPredProj_conjTranspose _) (p2d_ketPredProj_conjTranspose _)
    (p2d_RealizesConstCleanUnitary_circuit _ _)
    (fun fRow ↦ p2d_RealizesConstCleanUnitary_circuit P_lo
      (cBranchFix4Rows218Aux hm j₀ rCore rScr hCS fRow 4 le_rfl))
    (fun fRow ↦ ?_) (fun fRow ↦ ?_)
  · apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        p2d_ketPredProj_mul_ket]
    by_cases hβ : S_ext β ∧ invHoleSlot218 hm rData sFn rScr β
    · rw [ite_eq_left hβ, hcPre β hβ.2, Matrix.mulVec_smul, p2d_xResetKraus_mulVec_ket,
          p2d_writeReg_reset_zero_of_zero β rRow4 _ hβ.2.2.2.2.1,
          smul_smul, Matrix.mulVec_smul, p2d_ketPredProj_mul_ket,
          ite_eq_left ⟨_, Nat.mod_lt _ (by decide), hβ.2.1⟩]
    · simp [hβ]
  · apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
    by_cases hβ : S_ext β ∧ invHoleSlot218 hm rData sFn rScr β
    · rw [ite_eq_left hβ, hcPre β hβ.2, Matrix.mulVec_smul, p2d_xResetKraus_mulVec_ket]
      let s₀ := sFn (fun u ↦ β (rData u))
      have hl₀ : s₀.val % 64 < 64 := Nat.mod_lt _ (by decide)
      let vals := rowBit218 rCore j₀ β (s₀.val % 64) hl₀
      simp only [p2d_writeReg_apply_reg]
      rw [p2d_writeReg_reset_zero_of_zero β rRow4 vals hβ.2.2.2.2.1,
          smul_smul, Matrix.mulVec_smul,
          cBranchFix4Rows218Aux_eval_ket hm j₀ rCore rScr hCS fRow β (s₀.val % 64) hl₀ hβ.2.1 4
            le_rfl,
          smul_smul,
          uZKick1BitSlot218, diagSignUnitary_mulVec_ket, smul_smul]
      have hβEq : basisBits n ((basisBitsEquiv n).symm β) = β :=
        (basisBitsEquiv n).apply_symm_apply β
      simp only [hβEq, ite_decide_eq_one_zmod2]
      refine congrArg (· • ket β) ?_
      have hProdSq : (∏ b : Fin 4, if fRow b then
            (-1 : ℂ) ^ (rowBit218 rCore j₀ β (s₀.val % 64) hl₀ b).val else 1) *
          (∏ r : Fin 4, if fRow ⟨r.val, by omega⟩ then
            (-1 : ℂ) ^ (rowBit218 rCore j₀ β (s₀.val % 64) hl₀ ⟨r.val, by omega⟩).val else 1) = 1 :=
              by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun b _ ↦ ?_
        have hbEq : (⟨b.val, by omega⟩ : Fin 4) = b := Fin.ext rfl
        rw [hbEq]
        by_cases hfb : fRow b
        · rw [ite_eq_left hfb]
          rcases bit_cases (rowBit218 rCore j₀ β (s₀.val % 64) hl₀ b) with hv | hv <;> simp [hv]
        · simp [hfb]
      dsimp only [s₀] at hProdSq ⊢
      linear_combination
        ((((√(1 / 2)) ^ 4 : ℝ) : ℂ) *
          (-1 : ℂ) ^ (β (rElecSlot rCore (sFn (fun u ↦ β (rData u))) j₀)).val) *
          hProdSq
    · simp [hβ]
private theorem dFixHole218_slot_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var) (f : Fin 18 → Bool)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (sFn : BitAssignment kData → Fin 218) (L : Slot18Lens kData)
    (rScr : QRegister mScr n)
    (hDS : rData.DisjointWires rScr)
    (hsFn_had : ∀ γ₁ γ₂ : BitAssignment kData,
      (∀ u : Wire kData,
        StageADeconstrCore.selDataInAct kData u ∉ Set.range (selHadOfPosCore selCore).wires →
        γ₁ u = γ₂ u) →
      sFn γ₁ = sFn γ₂)
    (hTblBit : ∀ (g : Fin (2 ^ n)) (j : Fin 18),
      basisBits 18 (L.tbl (rData.extractIndex g)) j =
        basisBits n g (rElecSlot (rData.compose selCore)
          (sFn (fun u ↦ basisBits n g (rData u))) j))
    (S_ext : BitAssignment n → Prop)
    (hExtE : ∀ β₁ β₂ : BitAssignment n,
      (∀ w, (∀ (e : Fin 218) (j : Fin 18), w ≠ rElecSlot (rData.compose selCore) e j) →
        β₁ w = β₂ w) →
      (S_ext β₁ ↔ S_ext β₂)) :
    let rCore := rData.compose selCore
    let hCS : rCore.DisjointWires rScr := hDS.compose_left selCore
    let P_hole := p2d_ketPredProj (fun β ↦ S_ext β ∧ invHoleSlot218 hm rData sFn rScr β)
    p2d_RealizesConstCleanUnitary P_hole
      (dFixHole218 hm v f rCore rScr hCS)
      (rData.embedUnitary (diagSignUnitary (fun d ↦ f2Parity 18 f (L.tbl d)))) := by
  intro rCore hCS P_hole
  dsimp only [dFixHole218, BoothOpt_Anchor218CachedTrueSwapOuter.dFixHole218]
  obtain ⟨hSome, hNone⟩ := findTrueBitAux_spec f 18 le_rfl
  cases hfind : findTrueBitAux f 18 le_rfl with
  | none =>
      have hfFalse : ∀ j : Fin 18, f j = false := fun j ↦ hNone hfind j.val j.isLt
      have hParFalse : (fun d : Fin (2 ^ kData) ↦ f2Parity 18 f (L.tbl d)) =
          fun _ ↦ false := by
        funext d
        have hprod := sign_f2Parity_eq_prod 18 f (L.tbl d)
        simp only [hfFalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          Finset.prod_const_one] at hprod
        cases hfp : f2Parity 18 f (L.tbl d)
        · rfl
        · rw [hfp] at hprod; norm_num at hprod
      rw [hParFalse, diagSignUnitary_false, rData.embedUnitary_one]
      refine ⟨fun M ↦ ⟨M, rfl⟩, fun M σ ↦ ?_⟩
      change P_hole * M.1.1 * P_hole =
        P_hole * ((1 : Unitary (2 ^ n)).1ᴴ * M.1.1 * (1 : Unitary (2 ^ n)).1) * P_hole
      rw [OneMemClass.coe_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  | some j₀ =>
      have hf0 : f j₀ = true := hSome j₀ hfind
      let cFan := cSlotParityFanIn f j₀ rCore
      let UZ := uZKick1BitSlot218 j₀ rData selCore sFn
      have hFanOther : ∀ (β : BitAssignment n) (w : Wire n),
          (∀ e : Fin 218, w ≠ rElecSlot rCore e j₀) →
          fanInBits f j₀ rCore 218 le_rfl β w = β w := fun β w hw ↦
        fanInBits_apply_other f j₀ rCore β 218 le_rfl w fun e ↦ hw ⟨e.val, by omega⟩
      have hSlotInHad : ∀ (e : Fin 218),
          StageADeconstrCore.selDataInAct kData (selCore (rElecSlot (QRegExt.ofFin posCoreWires) e
            j₀)) ∈
            Set.range (selHadOfPosCore selCore).wires :=
        fun e ↦ BoothOpt_03_CoinBarrelIdxFastTrueSwap.rDataElec_mem_selHadOfPosCore
          selCore e j₀
      have hFanSlotEq : ∀ β : BitAssignment n,
          sFn (fun u ↦ fanInBits f j₀ rCore 218 le_rfl β (rData u)) =
            sFn (fun u ↦ β (rData u)) := fun β ↦
        hsFn_had _ _ fun u hu ↦
          hFanOther β (rData u) fun e heq ↦ by
            have h1 : rElecSlot rCore e j₀ =
              rData (selCore (rElecSlot (QRegExt.ofFin posCoreWires) e j₀)) :=
              (rElecSlot_apply_ofFin rCore e j₀).trans (QRegister.compose_apply rData selCore _)
            exact hu (rData.wires.injective (heq.trans h1) ▸ hSlotInHad e)
      have hS_Fan : ∀ β : BitAssignment n,
          (S_ext (fanInBits f j₀ rCore 218 le_rfl β) ∧
           invHoleSlot218 hm rData sFn rScr (fanInBits f j₀ rCore 218 le_rfl β)) ↔
          (S_ext β ∧ invHoleSlot218 hm rData sFn rScr β) := fun β ↦ by
        refine and_congr (hExtE _ _ fun w hw ↦ hFanOther β w fun e ↦ hw e j₀) ?_
        have hSlot := hFanSlotEq β
        have hS : ∀ k : Fin mScr, fanInBits f j₀ rCore 218 le_rfl β (rScr k) = β (rScr k) :=
          fun k ↦ hFanOther β _ fun e ↦ (rCore_ne_rSub hCS _ _ _).symm
        have hSub : ∀ r : Fin 4,
            fanInBits f j₀ rCore 218 le_rfl β (p2dSubReg rScr 70 4 (by omega) r) =
            β (p2dSubReg rScr 70 4 (by omega) r) :=
          fun r ↦ hS ⟨70 + r.val, by omega⟩
        dsimp only [invHoleSlot218]
        simp only [hSlot, hS, hSub]
      have hCommFan : P_hole * cFan.eval.1 = cFan.eval.1 * P_hole := by
        classical
        apply matrix_ext_ket; intro β
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
        have hKet : cFan.eval.1.mulVec (ket β) = ket (fanInBits f j₀ rCore 218 le_rfl β) :=
          cSlotParityFanInAux_eval_ket f j₀ rCore β 218 le_rfl
        by_cases hβ : S_ext β ∧ invHoleSlot218 hm rData sFn rScr β
        · rw [ite_eq_left hβ, hKet, p2d_ketPredProj_mul_ket, ite_eq_left ((hS_Fan β).mpr hβ)]
        · rw [ite_eq_right hβ, Matrix.mulVec_zero, hKet, p2d_ketPredProj_mul_ket,
              ite_eq_right (mt (hS_Fan β).mp hβ)]
      have hCommUZ : P_hole * UZ.1 = UZ.1 * P_hole := by
        classical
        apply matrix_ext_ket; intro α
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
        dsimp only [UZ, uZKick1BitSlot218]
        rw [diagSignUnitary_mulVec_ket, Matrix.mulVec_smul, p2d_ketPredProj_mul_ket]
        by_cases hα : S_ext α ∧ invHoleSlot218 hm rData sFn rScr α
        · rw [ite_eq_left hα, diagSignUnitary_mulVec_ket]
        · simp [hα]
      have hIdem : P_hole * P_hole = P_hole := p2d_ketPredProj_mul_imp (fun _ h ↦ h)
      have hPresC : P_hole * (cFan.eval.1 * P_hole) = cFan.eval.1 * P_hole := by
        rw [← mul_assoc, hCommFan, mul_assoc, hIdem]
      have hPresUC : P_hole * ((UZ * cFan.eval).1 * P_hole) = (UZ * cFan.eval).1 * P_hole := by
        rw [Submonoid.coe_mul, ← mul_assoc, ← mul_assoc, hCommUZ,
            mul_assoc _ P_hole, hCommFan, mul_assoc, mul_assoc, hIdem, ← mul_assoc]
      have hConj := p2d_RealizesConstCleanUnitary_conj_circuit (p2d_ketPredProj_conjTranspose _)
        cFan (dZKick1BitHole218 hm v j₀ rCore rScr hCS) UZ
        (dZKick1BitHole218_slot_realizes hm v j₀ rData selCore sFn rScr hCS S_ext) hPresC hPresUC
      refine p2d_RealizesConstCleanUnitary_congr_unitary (p2d_ketPredProj_conjTranspose _) hConj ?_
      refine congrArg (fun U : Unitary (2 ^ n) ↦ U.1 * P_hole) ?_
      apply Subtype.ext; apply matrix_ext_ket; intro β
      rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      let β' := fanInBits f j₀ rCore 218 le_rfl β
      have hKet1 : cFan.eval.1.mulVec (ket β) = ket β' :=
        cSlotParityFanInAux_eval_ket f j₀ rCore β 218 le_rfl
      have hKet2 : cFan.eval.1.mulVec (ket β') = ket β := by
        dsimp only [cFan, cSlotParityFanIn]
        rw [cSlotParityFanInAux_eval_ket f j₀ rCore β' 218 le_rfl,
            fanInBits_involutive f j₀ rCore β]
      dsimp only [UZ, uZKick1BitSlot218]
      rw [hKet1, diagSignUnitary_mulVec_ket, Matrix.mulVec_smul, hKet2,
          embedUnitary_diagSignUnitary, diagSignUnitary_mulVec_ket]
      have hβ'Eq : basisBits n ((basisBitsEquiv n).symm β') = β' :=
        (basisBitsEquiv n).apply_symm_apply β'
      let g := (basisBitsEquiv n).symm β
      have hgβ : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
      simp only [hβ'Eq, ite_decide_eq_one_zmod2]
      refine congrArg (· • ket β) ?_
      let eAct : Fin 218 := sFn (fun u ↦ β (rData u))
      have hActSlot : sFn (fun u ↦ β' (rData u)) = eAct := hFanSlotEq β
      have hValβ' : β' (rElecSlot rCore eAct j₀) =
          ∑ j : Fin 18, if f j = true then β (rElecSlot rCore eAct j) else 0 := by
        dsimp only [β']
        have hSlot := fanInBits_apply_slot f j₀ rCore β 218 le_rfl eAct
        have heEq : (⟨eAct.val, by omega⟩ : Fin 218) = eAct := Fin.ext rfl
        simp only [heEq] at hSlot
        rw [hSlot]
        have hSingle : β (rElecSlot rCore eAct j₀) =
            ∑ j : Fin 18, if j = j₀ then (if f j = true then β (rElecSlot rCore eAct j) else 0) else
              0 := by
          rw [Finset.sum_ite_eq' Finset.univ j₀]
          simp [hf0]
        rw [hSingle, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        by_cases hj : j = j₀
        · subst hj; simp [hf0]
        · simp [hj]
      rw [hActSlot, hValβ', BoothOpt_02_Cached64x4TrueSwapEngine.neg_one_pow_sum_zmod2,
        sign_f2Parity_eq_prod]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      have hTblBit_g : basisBits 18 (L.tbl (rData.extractIndex g)) j =
          β (rElecSlot rCore eAct j) := by
        rw [hTblBit g j]
        have hSlotG : sFn (fun u ↦ basisBits n g (rData u)) = eAct := by
          dsimp only [eAct]; rw [hgβ]
        rw [hSlotG, hgβ]
      rw [← hTblBit_g]
      exact sign_zmod2_bool_if (f j) (basisBits 18 (L.tbl (rData.extractIndex g)) j)
end InlinedFix218_FixHole218


open Classical in
private theorem p2d_proj_ket {n : ℕ} (S : BitAssignment n → Prop) (β : BitAssignment n) :
    (p2d_ketPredProj S).mulVec (ket β) = if S β then ket β else 0 := by
  classical
  convert p2d_ketPredProj_mul_ket S β

private theorem tcSub_of_pos {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {E₁ E₂ : Operator (2 ^ n)} {d : DynamicCircuit Var n}
    (h : SubspaceStep E₁ E₂ d) :
    Bell18TeleportCore.SubspaceStep E₁ E₂ d :=
  fun M ↦ let ⟨N, hwp, heq⟩ := h M; ⟨N, hwp, heq.symm⟩

private theorem tcSub_mul_right {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {E₁ E₂ : Operator (2 ^ n)} {d : DynamicCircuit Var n}
    (R : Operator (2 ^ n)) (h : Bell18TeleportCore.SubspaceStep E₁ E₂ d) :
    Bell18TeleportCore.SubspaceStep (E₁ * R) (E₂ * R) d := fun M ↦ by
  obtain ⟨M', hwp, heq⟩ := h M
  refine ⟨M', hwp, ?_⟩
  calc (E₁ * R)ᴴ * M'.1.1 * (E₁ * R)
      = Rᴴ * (E₁ᴴ * M'.1.1 * E₁) * R := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Rᴴ * (E₂ᴴ * M.1.1 * E₂) * R := by rw [heq]
    _ = (E₂ * R)ᴴ * M.1.1 * (E₂ * R) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem pebRealizes_of_tc {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P : Operator (2 ^ n)} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (hP : Pᴴ = P) (h : Bell18TeleportCore.RealizesOnProj P U d) :
    Pass1BarrelIdxPebbled273.RealizesOnProj P U.1 d := fun M ↦ by
  obtain ⟨M', hwp, heq⟩ := h M
  refine ⟨M', hwp, ?_⟩
  simpa only [hP, Matrix.mul_assoc] using heq

private theorem tcUSlotFix_eq {kData : ℕ} (L : Slot18Lens kData) (f : Fin 18 → Bool) :
    Bell18TeleportCore.uSlotFix (toSlotK18 L) f =
      diagSignUnitary (fun d ↦ f2Parity 18 f (L.tbl d)) := by
  have hPar : ∀ d,
      Bell18TeleportCore.bellF2Parity 18 f ((toSlotK18 L).tbl d) =
        f2Parity 18 f (L.tbl d) := fun d ↦ by
    simp only [Bell18TeleportCore.bellF2Parity, f2Parity, toSlotK18]
    congr 1
  apply Subtype.ext; ext i j
  simp [Bell18TeleportCore.uSlotFix, Bell18TeleportCore.bellDiagSign,
    diagSignUnitary, hPar]

/-- `IsBankSlotLens` witness for `fastEILens hmPay` over `rElecEI`. -/
private noncomputable def isBankSlotLens_fastEILens {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) :=
      (hCW.compose_right _).compose_right _
    let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
    Bell18TeleportCore.IsBankSlotLens rDataEI
      ((rDataEI.compose (selCoreEI hmPay)).compose rElecAllPos)
      (toSlotK18 (fastEILens hmPay)) := by
  intro hCEI rDataEI
  refine
    { slotWires := fun α ↦ rElecSlot (rDataEI.compose (selCoreEI hmPay))
        (sFnEI (fullSysCoreWires mPayload) (fun u ↦ α (rDataEI u)))
      slot_ignores_elec := fun α₁ α₂ h ↦ by
        refine congrArg (rElecSlot (rDataEI.compose (selCoreEI hmPay))) ?_
        refine hsFnEI_had hmPay _ _ fun u hu ↦ h (rDataEI u) fun t ht ↦ hu ?_
        have ht0 : selCoreEI hmPay (rElecAllPos t) = u := rDataEI.wires.injective ht.symm
        obtain ⟨k, hk⟩ := rDataElec_mem_selHadOfPosCore (selCoreEI hmPay)
          ⟨t.val / 18, by have := t.isLt; omega⟩ ⟨t.val % 18, Nat.mod_lt _ (by decide)⟩
        refine ⟨k, hk.trans ?_⟩
        rw [← ht0]
        simp only [PosSlots24Barrel3Pass.rDataElec,
          rElecAllPos, rElecSlot, QRegister.compose_apply]
        refine congrArg _ (congrArg _ (congrArg _ (Fin.ext ?_)))
        simp [QRegister.block, Fin.natAddEmb, Fin.castLEEmb]; omega
      slot_in_elec := fun α j ↦ by
        let e := sFnEI (fullSysCoreWires mPayload) (fun u ↦ α (rDataEI u))
        refine ⟨⟨18 * e.val + j.val, by have := e.isLt; have := j.isLt; omega⟩, ?_⟩
        simp only [rElecAllPos, rElecSlot, QRegister.compose_apply]
        refine congrArg (fun x ↦ rDataEI (selCoreEI hmPay x)) (Fin.ext ?_)
        dsimp only [e]
        simp [QRegister.block, Fin.natAddEmb, Fin.castLEEmb]
      tbl_eq_slot := fun g j ↦ hTblBit_fastEILens hmPay rCore (rEnIdx9 hmWB rWB) hCEI g j
      updSlot_eq_writeReg := fun g v ↦ ?_ }
  apply funext; intro w
  dsimp only [toSlotK18, fastEILens,
    mkSlot18LensOfSlotReg]
  let slotD := fastEISlotReg hmPay (rDataEI.extractIndex g)
  have hSlotEq : rDataEI.compose slotD =
      rElecSlot (rDataEI.compose (selCoreEI hmPay))
        (sFnEI (fullSysCoreWires mPayload) (fun u ↦ basisBits n g (rDataEI u))) := by
    apply InterWalkRSum42Hoist.qreg_ext; intro j
    dsimp only [slotD, fastEISlotReg]
    simp only [QRegister.compose_apply]
    refine congrArg (fun e ↦ rElecSlot (rDataEI.compose (selCoreEI hmPay)) e j) ?_
    refine congrArg (sFnEI (fullSysCoreWires mPayload)) (funext fun u ↦ ?_)
    exact QRegister.basisBits_extractIndex rDataEI g u
  rw [← compose_replaceIndex_eq_fast rDataEI slotD g v, hSlotEq]
  let rSl := rElecSlot (rDataEI.compose (selCoreEI hmPay))
    (sFnEI (fullSysCoreWires mPayload) (fun u ↦ basisBits n g (rDataEI u)))
  by_cases hw : w ∈ Set.range rSl.wires
  · obtain ⟨j, rfl⟩ := hw
    rw [QRegister.basisBits_replaceIndex_apply, Bell18TeleportCore.writeReg_apply_reg]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw,
        Bell18TeleportCore.writeReg_apply_of_not_mem _ _ _ _ hw]

private def DiagCtxWGCohAbove {M : ℕ} (base : ℕ) : DiagCtxWG M → Prop
  | .hole => True
  | .cliffConj _ K => DiagCtxWGCohAbove base K
  | .wStateTreeCohGate1 _ _ _ _ qEnc _ K => base ≤ qEnc.val ∧ DiagCtxWGCohAbove base K
  | .tempAnd _ _ _ _ _ _ _ => False
  | .wStateTree _ _ _ _ _ _ => False

private theorem cCohShiftPre_p304_eq_p408 {D n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hHasQ : wHas ≠ qEnc) (hIdxQ : ∀ d, wIdx d ≠ qEnc) (hOutQ : ∀ p, wOut p ≠ qEnc)
    (d : ℕ) (hd : d < D) :
    BoothOpt_FastAnchorOuterAndStageBShave.cCohShiftPre
      wHas wIdx wOut qEnc hHasQ hIdxQ hOutQ d hd =
    BoothOpt_StageBPartnerCoreShave.cCohShiftPre
      wHas wIdx wOut qEnc hHasQ hIdxQ hOutQ d hd := by
  unfold BoothOpt_FastAnchorOuterAndStageBShave.cCohShiftPre
    BoothOpt_StageBPartnerCoreShave.cCohShiftPre
  rfl

private theorem wCohShiftLevel_p304_eq_p408 {Var : Type} {D n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin D → Wire n) (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hHasQ : wHas ≠ qEnc) (hIdxQ : ∀ d, wIdx d ≠ qEnc)
    (hOutInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) (hOutQ : ∀ p, wOut p ≠ qEnc)
    (d : ℕ) (hd : d < D) :
    BoothOpt_FastAnchorOuterAndStageBShave.wCohShiftLevel
      v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ d hd =
    BoothOpt_StageBPartnerCoreShave.wCohShiftLevel
      v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ d hd := by
  unfold BoothOpt_FastAnchorOuterAndStageBShave.wCohShiftLevel
    BoothOpt_StageBPartnerCoreShave.wCohShiftLevel
  rw [cCohShiftPre_p304_eq_p408]

private theorem wCohShiftLevels_p304_eq_p408 {Var : Type} {D n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin D → Wire n) (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hHasQ : wHas ≠ qEnc) (hIdxQ : ∀ d, wIdx d ≠ qEnc)
    (hOutInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) (hOutQ : ∀ p, wOut p ≠ qEnc) :
    ∀ (m : ℕ) (hm : m ≤ D),
      BoothOpt_FastAnchorOuterAndStageBShave.wCohShiftLevels
        v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ m hm =
      BoothOpt_StageBPartnerCoreShave.wCohShiftLevels
        v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ m hm
  | 0, _ => by
      unfold BoothOpt_FastAnchorOuterAndStageBShave.wCohShiftLevels
        BoothOpt_StageBPartnerCoreShave.wCohShiftLevels
      rfl
  | d + 1, hd => by
      unfold BoothOpt_FastAnchorOuterAndStageBShave.wCohShiftLevels
        BoothOpt_StageBPartnerCoreShave.wCohShiftLevels
      exact congrArg₂ DynamicCircuit.seq
        (wCohShiftLevels_p304_eq_p408 v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ d
          (Nat.le_of_succ_le hd))
        (wCohShiftLevel_p304_eq_p408 v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ d hd)

private theorem wStateComputeCohGate1_p304_eq_p408 (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (wHas : Wire n) (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n)
    (qEnc : Wire n) :
    BoothOpt_FastAnchorOuterAndStageBShave.wStateComputeCohGate1
      k v wHas wIdx wOut qEnc =
    BoothOpt_StageBPartnerCoreShave.wStateComputeCohGate1
      k v wHas wIdx wOut qEnc := by
  unfold BoothOpt_FastAnchorOuterAndStageBShave.wStateComputeCohGate1
    BoothOpt_StageBPartnerCoreShave.wStateComputeCohGate1
  split_ifs with h
  · exact congrArg (DynamicCircuit.seq _)
      (wCohShiftLevels_p304_eq_p408 v wHas wIdx wOut qEnc
        h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 (k + 1) le_rfl)
  · rfl

private theorem wStateUncomputeCohGate1_p304_eq_p408 (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (wHas : Wire n) (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) :
    BoothOpt_FastAnchorOuterAndStageBShave.wStateUncomputeCohGate1
      k v wHas wIdx wOut =
    BoothOpt_StageBPartnerCoreShave.wStateUncomputeCohGate1
      k v wHas wIdx wOut := by
  unfold BoothOpt_FastAnchorOuterAndStageBShave.wStateUncomputeCohGate1
    BoothOpt_StageBPartnerCoreShave.wStateUncomputeCohGate1
  rfl

private theorem subspaceStep_toDynWG_bell
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (base : ℕ) (v : Var) (rComb : QRegister M n)
    (S_ext : BitAssignment n → Prop)
    (hExt : ∀ β₁ β₂ : BitAssignment n,
      (∀ w : Wire n, (∀ idx : Wire M, base ≤ idx.val → w ≠ rComb idx) → β₁ w = β₂ w) →
      (S_ext β₁ ↔ S_ext β₂))
    (InvHole : BitAssignment M → Prop)
    (inner : DynamicCircuit Var n) (B S : Unitary (2 ^ n))
    (hBAbove : ∀ (idx : Wire M), base ≤ idx.val → ∀ g' g : Fin (2 ^ n),
      B.1 g' g ≠ 0 → basisBits n g' (rComb idx) = basisBits n g (rComb idx))
    (hInner : Bell18TeleportCore.SubspaceStep
      (B.1 * p2d_ketPredProj fun β ↦ S_ext β ∧ InvHole (fun idx ↦ β (rComb idx)))
      (S.1 * p2d_ketPredProj fun β ↦ S_ext β ∧ InvHole (fun idx ↦ β (rComb idx)))
      inner) :
    ∀ (K : DiagCtxWG M) (Inv : BitAssignment M → Prop),
      DiagCtxWGCohAbove base K →
      DiagCtxWGWritesAbove base K →
      DiagCtxWGCommutesWith rComb B K →
      DiagCtxWGCommutesWith rComb S K →
      (∀ γ : BitAssignment M, Inv γ → K.ValidAtWith InvHole γ) →
      Bell18TeleportCore.SubspaceStep
        (B.1 * p2d_ketPredProj fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx)))
        (S.1 * p2d_ketPredProj fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx)))
        (toDynWG v rComb inner K) := by
  have hReadWrite : ∀ (β : BitAssignment n) (f : BitAssignment M),
      (fun idx ↦ writeRegProg β rComb f (rComb idx)) = f := fun β f ↦
    funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
  have hWriteSelf : ∀ β : BitAssignment n,
      writeRegProg β rComb (fun idx ↦ β (rComb idx)) = β := fun β ↦ by
    funext w
    by_cases hm : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hm; exact writeRegProg_apply_reg _ _ _ _
    · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
  have hWriteIdem : ∀ (β : BitAssignment n) (f g : BitAssignment M),
      writeRegProg (writeRegProg β rComb f) rComb g = writeRegProg β rComb g := fun β f g ↦ by
    funext w
    by_cases hm : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hm; simp [writeRegProg_apply_reg]
    · simp [writeRegProg_apply_of_not_mem _ _ _ _ hm]
  intro K
  induction K with
  | hole =>
      intro Inv _ _ _ _ hImp
      have hMul := p2d_ketPredProj_mul_imp
        (S₁ := fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx)))
        (S₂ := fun β ↦ S_ext β ∧ InvHole (fun idx ↦ β (rComb idx)))
        (fun β ⟨hE, hI⟩ ↦ ⟨hE, hImp _ hI⟩)
      have hStep := tcSub_mul_right
        (p2d_ketPredProj fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx))) hInner
      rwa [Matrix.mul_assoc, Matrix.mul_assoc, hMul] at hStep
  | tempAnd _ _ _ _ _ _ _ _ => intro _ hCoh; exact False.elim hCoh
  | wStateTree _ _ _ _ _ _ _ => intro _ hCoh; exact False.elim hCoh
  | cliffConj c K₁ ih =>
      intro Inv hCoh ⟨hcW, hKW⟩ ⟨hCommBPost, hCommB₁⟩ ⟨hCommSPost, hCommS₁⟩ hImp
      have hBody := ih (K₁.ValidAtWith InvHole) hCoh hKW hCommB₁ hCommS₁ (fun _ h ↦ h)
      let cPre := (c.onRegister rComb).toCircuit
      let cPost := (c.inv.onRegister rComb).toCircuit
      have hcPreKet : ∀ β : BitAssignment n,
          cPre.eval.1.mulVec (ket β) =
            ket (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) :=
        fun β ↦ (eval_onRegister_prog_ket rComb (.cliff c) β).trans
          (by simp [TempPhaseProg.evalSign,
                    TempPhaseProg.evalBits, ZMod.val_zero, one_smul])
      have hcPostKet : ∀ β : BitAssignment n,
          cPost.eval.1.mulVec (ket β) =
            ket (writeRegProg β rComb (c.inv.eval (fun idx ↦ β (rComb idx)))) :=
        fun β ↦ (eval_onRegister_prog_ket rComb (.cliff c.inv) β).trans
          (by simp [TempPhaseProg.evalSign,
                    TempPhaseProg.evalBits, ZMod.val_zero, one_smul])
      have hPostPre : cPost.eval * cPre.eval = 1 := by
        apply Subtype.ext; apply matrix_ext_ket; intro β
        simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec,
          Matrix.one_mulVec, hcPreKet, hcPostKet, hReadWrite, hWriteIdem,
          CliffProg.inv_eval, hWriteSelf]
      have hPrePost : cPre.eval * cPost.eval = 1 := mul_eq_one_comm.mp hPostPre
      have hCommBPre : cPre.eval * B = B * cPre.eval := by
        calc cPre.eval * B
            = cPre.eval * B * (cPost.eval * cPre.eval) := by rw [hPostPre, mul_one]
          _ = cPre.eval * (B * cPost.eval) * cPre.eval := by simp only [mul_assoc]
          _ = (cPre.eval * cPost.eval) * B * cPre.eval := by
                dsimp only [cPost]; rw [← hCommBPost]; simp only [mul_assoc]
          _ = B * cPre.eval := by rw [hPrePost, one_mul]
      have hExtCliff : ∀ β : BitAssignment n,
          S_ext (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) ↔ S_ext β := fun β ↦
        hExt _ _ fun w hw ↦ by
          by_cases hm : w ∈ Set.range rComb.wires
          · obtain ⟨idx, rfl⟩ := hm
            have hlt : idx.val < base := Nat.lt_of_not_ge fun hge ↦ hw idx hge rfl
            rw [writeRegProg_apply_reg]
            exact hcW.eval_lt (fun i ↦ β (rComb i)) idx hlt
          · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
      let P₁ := p2d_ketPredProj fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx))
      let P₂ := p2d_ketPredProj fun β ↦
        S_ext β ∧ K₁.ValidAtWith InvHole (fun idx ↦ β (rComb idx))
      have hclean1 : P₂ * (cPre.eval.1 * P₁) = cPre.eval.1 * P₁ := by
        apply matrix_ext_ket; intro β
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_proj_ket]
        by_cases hs : S_ext β ∧ Inv (fun idx ↦ β (rComb idx))
        · rw [ite_eq_left hs, hcPreKet, p2d_proj_ket]
          have hs₂ : S_ext (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) ∧
              K₁.ValidAtWith InvHole
                (fun idx ↦ writeRegProg β rComb
                  (c.eval (fun idx ↦ β (rComb idx))) (rComb idx)) := by
            rw [hExtCliff, hReadWrite]; exact ⟨hs.1, hImp _ hs.2⟩
          rw [ite_eq_left hs₂]
        · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
      have s1 := Bell18TeleportCore.subspaceStep_of_circuit (Var := Var) cPre (B.1 * P₁)
      have hInMid : cPre.eval.1 * (B.1 * P₁) = (B.1 * P₂) * (cPre.eval.1 * P₁) := by
        calc cPre.eval.1 * (B.1 * P₁)
            = (cPre.eval * B).1 * P₁ := by simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          _ = B.1 * (cPre.eval.1 * P₁) := by
                rw [hCommBPre]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          _ = (B.1 * P₂) * (cPre.eval.1 * P₁) := by symm; rw [Matrix.mul_assoc, hclean1]
      have s2 := tcSub_mul_right (cPre.eval.1 * P₁) hBody
      have hOutMid : (S.1 * P₂) * (cPre.eval.1 * P₁) = S.1 * (cPre.eval.1 * P₁) := by
        rw [Matrix.mul_assoc, hclean1]
      have s3 := Bell18TeleportCore.subspaceStep_of_circuit (Var := Var)
        cPost (S.1 * (cPre.eval.1 * P₁))
      have hOutEnd : cPost.eval.1 * (S.1 * (cPre.eval.1 * P₁)) = S.1 * P₁ := by
        calc cPost.eval.1 * (S.1 * (cPre.eval.1 * P₁))
            = (cPost.eval * S).1 * (cPre.eval.1 * P₁) := by
                simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          _ = S.1 * ((cPost.eval * cPre.eval).1 * P₁) := by
                dsimp only [cPost]; rw [hCommSPost]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          _ = S.1 * P₁ := by rw [hPostPre, OneMemClass.coe_one, Matrix.one_mul]
      exact (Bell18TeleportCore.subspaceStep_congr_out hInMid s1).seq
        ((Bell18TeleportCore.subspaceStep_congr_out hOutMid s2).seq
          (Bell18TeleportCore.subspaceStep_congr_out hOutEnd s3))
  | wStateTreeCohGate1 k wHas wIdx wOut qEnc hd K₁ ih =>
      intro Inv ⟨hqGe, hCoh⟩ ⟨hOutW, hKW⟩ ⟨hCommBOH, _, hCommB₁⟩ ⟨hCommSOH, hPresSOut, hCommS₁⟩ hImp
      have hBody := ih (K₁.ValidAtWith InvHole) hCoh hKW hCommB₁ hCommS₁ (fun _ h ↦ h)
      let wHasN : Wire n := rComb wHas
      let wIdxN : Fin (k + 1) → Wire n := fun d ↦ rComb (wIdx d)
      let wOutN : Fin (2 ^ (k + 1)) → Wire n := fun l ↦ rComb (wOut l)
      let qEncN : Wire n := rComb qEnc
      have hdN : WRouterDisj wHasN wIdxN wOutN qEncN := wRouterDisj_onRegister rComb hd
      let uOH := uOneHotToggle wHasN wIdxN wOutN hdN.has_ne_out hdN.idx_ne_out
      let S₀ : BitAssignment n → Prop := fun β ↦ S_ext β ∧ Inv (fun idx ↦ β (rComb idx))
      let S₁ : BitAssignment n → Prop :=
        fun β ↦ S_ext β ∧ K₁.ValidAtWith InvHole (fun idx ↦ β (rComb idx))
      let P₀ := p2d_ketPredProj S₀
      let P₁ := p2d_ketPredProj S₁
      have hIdxEq : ∀ β : BitAssignment n,
          idxValD wIdxN β = idxValD wIdx (fun idx ↦ β (rComb idx)) := fun β ↦ by
        rw [idxValD_eq_bitsVal, idxValD_eq_bitsVal]
      have hReadOH : ∀ β : BitAssignment n,
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          let j : Fin (2 ^ (k + 1)) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
          (fun idx ↦ Function.update β (wOutN j) (β (wOutN j) + β wHasN) (rComb idx)) =
            Function.update γ (wOut j) (γ (wOut j) + γ wHas) := fun β ↦ by
        intro γ j; funext idx
        by_cases hij : idx = wOut j
        · subst hij; simp [wOutN, wHasN, γ, Function.update_self]
        · simp [wOutN, wHasN, γ, Function.update_of_ne hij,
            Function.update_of_ne (rComb.wires.injective.ne hij)]
      have hExtOH : ∀ (β : BitAssignment n) (j : Fin (2 ^ (k + 1))),
          S_ext (Function.update β (wOutN j) (β (wOutN j) + β wHasN)) ↔ S_ext β := fun β j ↦
        hExt _ _ fun w hw ↦ Function.update_of_ne (hw (wOut j) (hOutW j)) _ _
      have hP₁_uOH : P₁ * (uOH.1 * P₀) = uOH.1 * P₀ := by
        apply matrix_ext_ket; intro β
        dsimp only [P₀, P₁, uOH]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_proj_ket]
        by_cases hs : S₀ β
        · have hLt : idxValD wIdxN β < 2 ^ (k + 1) := idxValD_lt_two_pow wIdxN β
          have hToggle : toggleOneHotBits wHasN wIdxN wOutN β =
              Function.update β (wOutN ⟨idxValD wIdxN β, hLt⟩)
                (β (wOutN ⟨idxValD wIdxN β, hLt⟩) + β wHasN) :=
            dite_eq_left hLt
          rw [ite_eq_left hs, uOneHotToggle_mulVec_ket, hToggle, p2d_proj_ket]
          have hjEq : (⟨idxValD wIdxN β, hLt⟩ : Fin (2 ^ (k + 1))) =
              ⟨idxValD wIdx (fun idx ↦ β (rComb idx)), idxValD_lt_two_pow wIdx _⟩ :=
            Fin.ext (hIdxEq β)
          have hs₁ : S₁ (Function.update β (wOutN ⟨idxValD wIdxN β, hLt⟩)
              (β (wOutN ⟨idxValD wIdxN β, hLt⟩) + β wHasN)) := by
            dsimp only [S₁]; rw [hjEq, hExtOH β, hReadOH β]; exact ⟨hs.1, (hImp _ hs.2).2.2⟩
          rw [ite_eq_left hs₁]
        · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
      have hInP₀ : p2d_ketPredProj (ValidWCohGateIn wOutN qEncN) * P₀ = P₀ :=
        p2d_ketPredProj_mul_imp (S₁ := S₀) (S₂ := ValidWCohGateIn wOutN qEncN)
          (fun β hs ↦ ⟨(hImp _ hs.2).1, (hImp _ hs.2).2.1⟩)
      have hInProj : p2d_ketPredProj (ValidWCohGateIn wOutN qEncN) * (B.1 * P₀) = B.1 * P₀ := by
        rw [← Matrix.mul_assoc,
            ketPredProj_comm_of_preserves (ValidWCohGateIn wOutN qEncN) B
              (fun i j hnz ↦ and_congr
                (forall_congr' fun l ↦ by rw [hBAbove (wOut l) (hOutW l) i j hnz])
                (by rw [hBAbove qEnc hqGe i j hnz])),
            Matrix.mul_assoc, hInP₀]
      have hSuppIn : SupportedOn (ValidWCohGateIn wOutN qEncN) (B.1 * P₀) :=
        supportedOn_of_ketPredProj_mul_eq hInProj
      have hCleanP₀ : p2d_ketPredProj (ValidWCohGateClean wOutN) * P₀ = P₀ :=
        p2d_ketPredProj_mul_imp (S₁ := S₀) (S₂ := ValidWCohGateClean wOutN)
          (fun β hs ↦ (hImp _ hs.2).1)
      have hCleanProj :
          p2d_ketPredProj (ValidWCohGateClean wOutN) * (S.1 * P₀) = S.1 * P₀ := by
        rw [← Matrix.mul_assoc,
            ketPredProj_comm_of_preserves (ValidWCohGateClean wOutN) S
              (fun i j hnz ↦ forall_congr' fun l ↦ by rw [hPresSOut l i j hnz]),
            Matrix.mul_assoc, hCleanP₀]
      have hSuppOut : SupportedOn (ValidWCohGateClean wOutN) (S.1 * P₀) :=
        supportedOn_of_ketPredProj_mul_eq hCleanProj
      have sComp := tcSub_of_pos
        (subspaceStep_wStateComputeCohGate1 k v wHasN wIdxN wOutN qEncN hdN (B.1 * P₀) hSuppIn)
      rw [← wStateComputeCohGate1_p304_eq_p408] at sComp
      have hMidIn : uOH.1 * (B.1 * P₀) = (B.1 * P₁) * (uOH.1 * P₀) := by
        calc uOH.1 * (B.1 * P₀)
            = (uOH * B).1 * P₀ := by simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          _ = B.1 * (uOH.1 * P₀) := by
                dsimp only [uOH, wHasN, wIdxN, wOutN]
                rw [hCommBOH]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          _ = (B.1 * P₁) * (uOH.1 * P₀) := by symm; rw [Matrix.mul_assoc, hP₁_uOH]
      have sBody := tcSub_mul_right (uOH.1 * P₀) hBody
      have hMidOut : (S.1 * P₁) * (uOH.1 * P₀) = uOH.1 * (S.1 * P₀) := by
        calc (S.1 * P₁) * (uOH.1 * P₀)
            = S.1 * (uOH.1 * P₀) := by rw [Matrix.mul_assoc, hP₁_uOH]
          _ = (S * uOH).1 * P₀ := (Matrix.mul_assoc _ _ _).symm
          _ = uOH.1 * (S.1 * P₀) := by
                dsimp only [uOH, wHasN, wIdxN, wOutN]
                rw [← hCommSOH]; exact Matrix.mul_assoc _ _ _
      have sUnc := tcSub_of_pos
        (subspaceStep_wStateUncomputeCohGate1 k v wHasN wIdxN wOutN
          hdN.has_ne_out hdN.idx_ne_out hdN.out_inj (S.1 * P₀) hSuppOut)
      rw [← wStateUncomputeCohGate1_p304_eq_p408] at sUnc
      dsimp only [toDynWG]
      exact (Bell18TeleportCore.subspaceStep_congr_out hMidIn sComp).seq
        ((Bell18TeleportCore.subspaceStep_congr_out hMidOut sBody).seq sUnc)

private theorem ctxFastTrees93_cohAbove : DiagCtxWGCohAbove 18 ctxFastTrees93 :=
  ⟨by decide, by decide, trivial⟩

/-- Slot-bit index `t % 18` for each wire of the `3,924`-wire electron register. -/
def bitOfElec3924 : Fin 3924 → Fin 18 :=
  fun t ↦ ⟨t.val % 18, Nat.mod_lt _ (by decide)⟩

private theorem bitOfElec3924_fastEILens {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) :=
      (hCW.compose_right _).compose_right _
    let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
    let rElecEI := (rDataEI.compose (selCoreEI hmPay)).compose rElecAllPos
    ∀ (t : Fin 3924) (α : BitAssignment n) (j : Fin 18),
      rElecEI t = (isBankSlotLens_fastEILens hmPay hmWB rCore rWB hCW).slotWires α j →
      bitOfElec3924 t = j := by
  intro hCEI rDataEI rElecEI t α j hEq
  dsimp only [isBankSlotLens_fastEILens] at hEq
  let e := sFnEI (fullSysCoreWires mPayload) (fun u ↦ α (rDataEI u))
  have hSlot : rElecSlot (rDataEI.compose (selCoreEI hmPay)) e j =
      rElecEI ⟨18 * e.val + j.val, by have := e.isLt; have := j.isLt; omega⟩ := by
    dsimp only [rElecEI, e]
    simp only [rElecAllPos, rElecSlot, QRegister.compose_apply]
    exact congrArg (fun x ↦ rDataEI (selCoreEI hmPay x)) (Fin.ext (Nat.zero_add _).symm)
  rw [hSlot] at hEq
  have hv := congrArg Fin.val (rElecEI.wires.injective hEq)
  dsimp only at hv
  exact Fin.ext (by dsimp [bitOfElec3924]; have := j.isLt; omega)

/-- Core `420 T`-wrapped `64 × 4` gated W-state Bell-18 fused post-pass (`≤ 856 T`, `0 TOFF`)
on `(rCore, rAnchor18, rHeld18, rWB)` (`80 ≤ mPayload`, `143 ≤ mWB`). -/
noncomputable def dPostCoreBell18Fast {Var : Type} {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 rHeld18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (hAH : rAnchor18.DisjointWires rHeld18) :
    DynamicCircuit Var n :=
  let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) :=
    (hCW.compose_right _).compose_right _
  let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
  let rElecEI := (rDataEI.compose (selCoreEI hmPay)).compose rElecAllPos
  let hDS_EI : rDataEI.DisjointWires (rScr75 hmWB rWB) :=
    qreg_disjoint_concat_left (disj_rScr75_right hmWB hCW)
      ((rPeb10_disj_rScr75 hmWB rWB).compose_left _)
  let hCS_EI := hDS_EI.compose_left (selCoreEI hmPay)
  let dFix : (Fin 18 → Bool) → DynamicCircuit Var n := fun f ↦
    dFixHole218 (le_refl 75) v f (rDataEI.compose (selCoreEI hmPay)) (rScr75 hmWB rWB) hCS_EI
  dWrapFast68 hmPay hmWB v rCore rWB hCW
    (Bell18TeleportCore.dPostBellInnerFused v rElecEI bitOfElec3924 rAnchor18 rHeld18
      (QRegExt.disjointWires_symm hAH) dFix)

private theorem dPostCoreBell18Fast_count_toff {Var : Type} {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 rHeld18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (hAH : rAnchor18.DisjointWires rHeld18) :
    (dPostCoreBell18Fast hmPay hmWB v rCore rAnchor18 rHeld18 rWB hCW hAH).count TOFF = 0 := by
  dsimp only [dPostCoreBell18Fast]
  rw [count_dWrapFast68_toff]
  exact Bell18TeleportCore.dPostBellInnerFused_count_toff v _ bitOfElec3924
    rAnchor18 rHeld18 (QRegExt.disjointWires_symm hAH) (fun f ↦
      dFixHole218_count_toff (le_refl 75) v f _ _ _)

private theorem dPostCoreBell18Fast_count_t_le {Var : Type} {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 rHeld18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (hAH : rAnchor18.DisjointWires rHeld18) :
    (dPostCoreBell18Fast hmPay hmWB v rCore rAnchor18 rHeld18 rWB hCW hAH).count T ≤ 856 := by
  dsimp only [dPostCoreBell18Fast]
  rw [count_dWrapFast68_t]
  let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) :=
    (hCW.compose_right _).compose_right _
  let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
  let rElecEI := (rDataEI.compose (selCoreEI hmPay)).compose rElecAllPos
  let hDS_EI : rDataEI.DisjointWires (rScr75 hmWB rWB) :=
    qreg_disjoint_concat_left (disj_rScr75_right hmWB hCW)
      ((rPeb10_disj_rScr75 hmWB rWB).compose_left _)
  let hCS_EI := hDS_EI.compose_left (selCoreEI hmPay)
  let dFix : (Fin 18 → Bool) → DynamicCircuit Var n := fun f ↦
    dFixHole218 (le_refl 75) v f (rDataEI.compose (selCoreEI hmPay)) (rScr75 hmWB rWB) hCS_EI
  have hInner := Bell18TeleportCore.dPostBellInnerFused_count_t_le
    (B := 436) (dFix :=
      dFix) v rElecEI bitOfElec3924 rAnchor18 rHeld18 (QRegExt.disjointWires_symm hAH)
    (fun f ↦ dFixHole218_count_t_le (le_refl 75) v f
      (rDataEI.compose (selCoreEI hmPay)) (rScr75 hmWB rWB) hCS_EI)
  change 420 + (Bell18TeleportCore.dPostBellInnerFused v rElecEI bitOfElec3924
    rAnchor18 rHeld18 (QRegExt.disjointWires_symm hAH) dFix).count T ≤ 856
  omega

private theorem tcSub_of_p2d_selfInv {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P R : Operator (2 ^ n)} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n}
    (hP : Pᴴ = P) (hPR : P * (U.1 * R) = U.1 * R) (hSq : U * U = 1)
    (hd : p2d_RealizesConstCleanUnitary P d U) :
    Bell18TeleportCore.SubspaceStep (U.1 * R) R d := fun M ↦ by
  obtain ⟨M', hwp⟩ := hd.1 M
  have heq : P * M'.1.1 * P = P * (U.1ᴴ * M.1.1 * U.1) * P := by
    simpa [hwp] using hd.2 M default
  refine ⟨M', hwp, ?_⟩
  have hUU : U.1 * (U.1 * R) = R := by
    rw [← Matrix.mul_assoc, ← Submonoid.coe_mul, hSq, OneMemClass.coe_one, Matrix.one_mul]
  calc (U.1 * R)ᴴ * M'.1.1 * (U.1 * R)
      = (P * (U.1 * R))ᴴ * M'.1.1 * (P * (U.1 * R)) := by rw [hPR]
    _ = (U.1 * R)ᴴ * (P * M'.1.1 * P) * (U.1 * R) := by
          simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
    _ = (U.1 * R)ᴴ * (P * (U.1ᴴ * M.1.1 * U.1) * P) * (U.1 * R) := by rw [heq]
    _ = (U.1 * (P * (U.1 * R)))ᴴ * M.1.1 * (U.1 * (P * (U.1 * R))) := by
          simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
    _ = Rᴴ * M.1.1 * R := by rw [hPR, hUU]

private theorem diagSignUnitary_mul_self {k : ℕ} (p : Fin (2 ^ k) → Bool) :
    diagSignUnitary p * diagSignUnitary p = 1 := by
  apply Subtype.ext; ext i j
  simp only [Submonoid.coe_mul, diagSignUnitary, OneMemClass.coe_one,
    Matrix.diagonal_mul_diagonal, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp only [Matrix.diagonal_apply_eq, ↓reduceIte]; cases p i <;> norm_num
  · simp [hij]

private theorem ketPredProj_comm_diag {n : ℕ} (S : BitAssignment n → Prop)
    (f : Fin (2 ^ n) → ℂ) :
    p2d_ketPredProj S * Matrix.diagonal f = Matrix.diagonal f * p2d_ketPredProj S := by
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_proj_ket]
  let g := (basisBitsEquiv n).symm β
  have hket : ket β = Pi.single g 1 := rfl
  have hDiag : (Matrix.diagonal f).mulVec (ket β) = f g • ket β := by
    rw [hket]; ext y
    simp only [Matrix.mulVec_diagonal, Pi.single_apply, Pi.smul_apply, smul_eq_mul, mul_boole]
    split_ifs with hy <;> simp [hy]
  by_cases hs : S β
  · rw [ite_eq_left hs, hDiag, Matrix.mulVec_smul, p2d_proj_ket, ite_eq_left hs]
  · rw [ite_eq_right hs, Matrix.mulVec_zero, hDiag, Matrix.mulVec_smul,
        p2d_proj_ket, ite_eq_right hs, smul_zero]

private theorem cHadReg_eval_eq_embed {n K : ℕ} (rHeld : QRegister K n) :
    (Bell18TeleportCore.cHadReg rHeld).eval =
      rHeld.embedUnitary
        (Bell18TeleportCore.cHadReg
          (QRegExt.idReg K)).eval := by
  let rId := QRegExt.idReg K
  have hOn : (Bell18TeleportCore.cHadReg rId).onRegister rHeld =
      Bell18TeleportCore.cHadReg rHeld := by
    unfold Bell18TeleportCore.cHadReg
    suffices ∀ k (hk : k ≤ K),
        (Bell18TeleportCore.cHadRegAux rId k hk).onRegister rHeld =
          Bell18TeleportCore.cHadRegAux rHeld k hk from this K le_rfl
    intro k
    induction k with
    | zero => intro _; rfl
    | succ m ih =>
        intro hm
        dsimp only [Bell18TeleportCore.cHadRegAux]
        rw [Circuit.onRegister_seq, ih (Nat.le_of_succ_le hm)]
        rfl
  rw [← hOn, Circuit.eval_onRegister]

open Pass1BarrelIdxPebbled273
  (progLoadInternal68 progLoadInternal68_end_le progLoadInternal68_stats cliffOfProgGen)
open FastCoinBarrelDecoder279
  (DecStep progEndCur progWellFormed)
open Pass1BarrelIdxPebbled273
  (stepFwdCircuit progFwdCircuit pebBitFnGen)

private theorem hasCleanTailFrom_of_comm_wbSingleton {n mPayload mWB : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hWB : 114 ≤ mWB) (hCW : rCore.DisjointWires rWB)
    (E : Operator (2 ^ n))
    (hComm : ∀ k : Fin 106,
      (QRegister.singleton (rWB ⟨8 + k.val, by have := k.isLt; omega⟩)).basisOutcomeProjector 0 *
        E =
      E * (QRegister.singleton
        (rWB ⟨8 + k.val, by have := k.isLt; omega⟩)).basisOutcomeProjector 0) :
    HasCleanTailFrom (rCombPeb rCore rWB hWB hCW) (fullSysCoreWires mPayload + 8)
      (E * rWB.basisOutcomeProjector 0) := by
  intro q hq
  let k : Fin 106 := ⟨q.val - (fullSysCoreWires mPayload + 8), by have := q.isLt; omega⟩
  have hqk : q = ⟨fullSysCoreWires mPayload + 8 + k.val, by have := q.isLt; omega⟩ :=
    Fin.ext (by dsimp [k]; omega)
  rw [hqk, rCombPeb_cln106, ← Matrix.mul_assoc, hComm k, Matrix.mul_assoc,
      singleton_rWB_mul_proj0]

private theorem sg_mul3_comm_right {R : Type} [Semigroup R] {a b c m : R}
    (hc : c * m = m * c) (hb : b * m = m * b) (ha : a * m = m * a) :
    (a * (b * c)) * m = m * (a * (b * c)) := by
  calc (a * (b * c)) * m = a * (b * (c * m)) := by simp only [mul_assoc]
    _ = a * ((b * m) * c) := by rw [hc]; simp only [mul_assoc]
    _ = (a * m) * (b * c) := by rw [hb]; simp only [mul_assoc]
    _ = m * (a * (b * c)) := by rw [ha]; simp only [mul_assoc]

private theorem vLinUnitary_comm_of_disj {n mPayload mWB kH : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB)
    (rH : QRegister kH n) (hCH : rCore.DisjointWires rH) (hWH : rWB.DisjointWires rH)
    (M : Operator (2 ^ kH)) :
    (vLinUnitary hmPay hmWB rCore rWB hCW).1 * rH.embedMatrix M =
      rH.embedMatrix M * (vLinUnitary hmPay hmWB rCore rWB hCW).1 := by
  have hCombH : ∀ h114 : 114 ≤ mWB, (rCombPeb rCore rWB h114 hCW).DisjointWires rH := by
    intro h114; unfold rCombPeb
    exact qreg_disjoint_concat_left
      (qreg_disjoint_concat_left hCH (hWH.compose_left _)) (hWH.compose_left _)
  let rC93 := rComb93 hmPay hmWB rCore rWB hCW
  have hC93H : rC93.DisjointWires rH :=
    qreg_disjoint_concat_left
      (qreg_disjoint_concat_left (hCH.compose_left _) (hWH.compose_left _))
      (QRegExt.disjointWires_symm (disj_rScr75_right hmWB (QRegExt.disjointWires_symm hWH)))
  have hEmbCircuit : ∀ {K : ℕ} (r : QRegister K n) (hr : r.DisjointWires rH) (c : Circuit K),
      (c.onRegister r).eval.1 * rH.embedMatrix M =
        rH.embedMatrix M * (c.onRegister r).eval.1 := fun r hr c ↦ by
    rw [Circuit.eval_onRegister, QRegister.embedUnitary_val]
    exact r.embedMatrix_comm_of_disjoint rH hr c.eval.1 M
  have hCliff : ∀ {K : ℕ} (r : QRegister K n) (hr : r.DisjointWires rH) (cp : CliffProg K),
      (cp.onRegister r).toCircuit.eval.1 * rH.embedMatrix M =
        rH.embedMatrix M * (cp.onRegister r).toCircuit.eval.1 := fun r hr cp ↦ by
    rw [CliffProg.onRegister_toCircuit_eval]
    exact hEmbCircuit r hr _
  have hCliffInt : ∀ {K : ℕ} (r : QRegister K n) (hr : r.DisjointWires rH)
      (cp : CoinDispatchedBarrel288.Internal.CliffProg K),
      (cp.onRegister r).toCircuit.eval.1 * rH.embedMatrix M =
        rH.embedMatrix M * (cp.onRegister r).toCircuit.eval.1 := fun r hr cp ↦ by
    rw [CoinDispatchedBarrel288.Internal.CliffProg.onRegister_toCircuit_eval]
    exact hEmbCircuit r hr _
  have hGate : ∀ {K m : ℕ} (r : QRegister K n) (hr : r.DisjointWires rH)
      (g : PrimitiveGate m) (rg : QRegister m n) (hsub : ∀ i, rg i ∈ Set.range r.wires),
      (Circuit.gate g rg).eval.1 * rH.embedMatrix M =
        rH.embedMatrix M * (Circuit.gate g rg).eval.1 := fun r hr g rg hsub ↦ by
    have hrg : rg.DisjointWires rH := by
      rw [QRegister.disjoint_iff]; intro i j hij
      obtain ⟨u, hu⟩ := hsub i; exact hr.ne u j (hu.trans hij)
    dsimp only [Circuit.eval]
    rw [QRegister.embedUnitary_val]
    exact rg.embedMatrix_comm_of_disjoint rH hrg g.eval.1 M
  have hStep : ∀ (r : QRegister (fullSysCoreWires mPayload + 8 + 106) n)
      (hr : r.DisjointWires rH) (cur : ℕ) (h61 : 61 ≤ cur) (hcur : cur ≤ 61 + 106)
      (s : DecStep) (hwf : s.wellFormed cur = true) (hnext : s.nextCur cur ≤ 61 + 106),
      (stepFwdCircuit hmPay r cur h61 hcur s hwf hnext).eval.1 * rH.embedMatrix M =
        rH.embedMatrix M * (stepFwdCircuit hmPay r cur h61 hcur s hwf hnext).eval.1 := by
    intro r hr cur h61 hcur s hwf hnext
    cases s with
    | allocZero => dsimp only [stepFwdCircuit, Circuit.eval]; simp
    | x q =>
        dsimp only [stepFwdCircuit, Circuit.X, Circuit.single]
        exact hGate r hr _ _ fun i ↦ by fin_cases i; exact ⟨_, rfl⟩
    | cnot src dst =>
        dsimp only [stepFwdCircuit, Circuit.CNOT]
        exact hGate r hr _ _ fun i ↦ by fin_cases i <;> exact ⟨_, rfl⟩
    | andAlloc a b =>
        dsimp only [stepFwdCircuit]
        exact hGate r hr _ _ fun i ↦ by fin_cases i <;> exact ⟨_, rfl⟩
  have hFwd : ∀ (r : QRegister (fullSysCoreWires mPayload + 8 + 106) n)
      (hr : r.DisjointWires rH) (p : List DecStep) (cur : ℕ) (h61 : 61 ≤ cur)
      (hend : progEndCur cur p ≤ 61 + 106) (hwf : progWellFormed cur p = true),
      (progFwdCircuit hmPay r p cur h61 hend hwf).eval.1 * rH.embedMatrix M =
        rH.embedMatrix M * (progFwdCircuit hmPay r p cur h61 hend hwf).eval.1 := by
    intro r hr p; induction p with
    | nil => intro cur h61 hend hwf; dsimp only [progFwdCircuit, Circuit.eval]; simp
    | cons s rest ih =>
        intro cur h61 hend hwf
        dsimp only [progFwdCircuit]
        rw [Circuit.eval_seq, Submonoid.coe_mul, mul_assoc,
            hStep r hr cur h61 _ s _ _, ← mul_assoc, ih _ _ hend _, mul_assoc]
  let hWB114 : 114 ≤ mWB := by omega
  let cPeb := cliffOfProgGen hmPay 8 106 progLoadInternal68 61
    progLoadInternal68_end_le progLoadInternal68_stats.1
  let rCP := rCombPeb rCore rWB hWB114 hCW
  have hCPH : rCP.DisjointWires rH := hCombH hWB114
  let U_68 := (progFwdCircuit hmPay rCP progLoadInternal68 61 le_rfl
    progLoadInternal68_end_le progLoadInternal68_stats.1).eval
  let C_inv := ((cPeb.inv.onRegister rCP).toCircuit).eval
  let L_93 := ((cPreLin93.onRegister rC93).toCircuit).eval
  have hV_val : (vLinUnitary hmPay hmWB rCore rWB hCW).1 =
      L_93.1 * (C_inv.1 * U_68.1) := by
    dsimp only [vLinUnitary, L_93, C_inv, U_68, rC93, rCP, cPeb, hWB114]
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
  have h1 : U_68.1 * rH.embedMatrix M = rH.embedMatrix M * U_68.1 :=
    hFwd rCP hCPH progLoadInternal68 61 le_rfl
      progLoadInternal68_end_le progLoadInternal68_stats.1
  have h2 : C_inv.1 * rH.embedMatrix M = rH.embedMatrix M * C_inv.1 :=
    hCliffInt rCP hCPH cPeb.inv
  have h3 : L_93.1 * rH.embedMatrix M = rH.embedMatrix M * L_93.1 :=
    hCliff rC93 hC93H cPreLin93
  rw [hV_val]
  generalize U_68.1 = u68 at h1 ⊢
  generalize C_inv.1 = cinv at h2 ⊢
  generalize L_93.1 = l93 at h3 ⊢
  exact sg_mul3_comm_right h1 h2 h3
private theorem fastLinState_apply_of_disj {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB)
    (w : Wire n) (hwC : w ∉ Set.range rCore.wires) (hwW : w ∉ Set.range rWB.wires)
    (β : BitAssignment n) :
    fastLinState hmPay hmWB rCore rWB hCW β w = β w := by
  have hCSing : rCore.DisjointWires (QRegister.singleton w) := by
    rw [QRegister.disjoint_iff]; rintro i _ h; exact hwC ⟨i, h⟩
  have hWSing : rWB.DisjointWires (QRegister.singleton w) := by
    rw [QRegister.disjoint_iff]; rintro i _ h; exact hwW ⟨i, h⟩
  have hC93Sing : (rComb93 hmPay hmWB rCore rWB hCW).DisjointWires (QRegister.singleton w) :=
    qreg_disjoint_concat_left
      (qreg_disjoint_concat_left (hCSing.compose_left _) (hWSing.compose_left _))
      (QRegExt.disjointWires_symm (disj_rScr75_right hmWB (QRegExt.disjointWires_symm hWSing)))
  have hw93 : w ∉ Set.range (rComb93 hmPay hmWB rCore rWB hCW).wires := by
    rintro ⟨idx, hidx⟩; exact hC93Sing.ne idx ⟨0, by decide⟩ hidx
  have hwSl : ∀ h114 : 114 ≤ mWB, w ∉ Set.range (rWB.slice 8 106 h114).wires :=
    fun _ ⟨m, hm⟩ ↦ hwW ⟨_, hm⟩
  dsimp only [fastLinState, pebBitFnGen]
  rw [writeRegProg_apply_of_not_mem _ _ _ _ hw93]
  exact CoinDispatchedBarrel288.Internal.writeRegProg_apply_of_not_mem
    _ _ _ _ (hwSl _)

open BoothOpt_03_CoinBarrelIdxFastTrueSwap (selPosInFullSys)
open BoothOpt_FastAnchorOuterAndStageBShave
  (rComb93_u8 selU8InCore_ge_3924 selCoreInEI rU8Core8)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (realizesOnProj_mul_right L_anchor)

attribute [local irreducible]
  dWrapFast68 vLinUnitary fastLinState dFixHole218 ctxFastTrees93

private theorem sg_conj_comm_right {R : Type} [Semigroup R] (a b w c : R)
    (hc : w * c = c * w) : a * (b * w) * c = (a * b * c) * w := by
  simp only [mul_assoc]; rw [hc]

private theorem sg_comm3 {R : Type} [Semigroup R] (p a b c : R)
    (ha : p * a = a * p) (hb : p * b = b * p) (hc : p * c = c * p) :
    p * ((a * b) * c) = ((a * b) * c) * p := by
  calc p * ((a * b) * c) = (p * a) * (b * c) := by simp only [mul_assoc]
    _ = a * ((p * b) * c) := by rw [ha]; simp only [mul_assoc]
    _ = a * (b * (p * c)) := by rw [hb]; simp only [mul_assoc]
    _ = ((a * b) * c) * p := by rw [hc]; simp only [mul_assoc]

private theorem mon_star_cancel_wb {R : Type} [Monoid R] (s sb b p w bh : R)
    (hsb : sb * b = 1) (hw : w * bh = bh * w) :
    (s * sb) * (b * (p * w) * bh) = ((s * p) * bh) * w := by
  calc (s * sb) * (b * (p * w) * bh)
      = s * (sb * b) * p * (w * bh) := by simp only [mul_assoc]
    _ = ((s * p) * bh) * w := by rw [hsb, mul_one, hw]; simp only [mul_assoc]

private theorem mon_star_cancel3 {R : Type} [Monoid R] (s sb b p bh : R)
    (hsb : sb * b = 1) : (s * sb) * (b * p * bh) = s * p * bh := by
  calc (s * sb) * (b * p * bh)
      = s * (sb * b) * p * bh := by simp only [mul_assoc]
    _ = s * p * bh := by rw [hsb, mul_one]

private theorem sg_vbc_intertwine {R : Type} [Semigroup R] (v wc wei h pch pwb : R)
    (hvw : v * (wc * pwb) = wei * (v * pwb)) (hvh : v * h = h * v)
    (hhw : h * pwb = pwb * h) (hcw : pch * pwb = pwb * pch) :
    v * ((wc * h) * (pch * pwb)) = (wei * h) * (v * (pch * pwb)) := by
  calc v * ((wc * h) * (pch * pwb))
      = v * (wc * (h * pwb) * pch) := by rw [hcw]; simp only [mul_assoc]
    _ = (v * (wc * pwb)) * (h * pch) := by rw [hhw]; simp only [mul_assoc]
    _ = wei * (v * (pwb * h) * pch) := by rw [hvw]; simp only [mul_assoc]
    _ = wei * ((v * h) * (pwb * pch)) := by rw [← hhw]; simp only [mul_assoc]
    _ = (wei * h) * (v * (pch * pwb)) := by rw [hvh, ← hcw]; simp only [mul_assoc]

private theorem sg_idem_pair {R : Type} [Semigroup R] (a b : R)
    (hab : b * a = a * b) (ha : a * a = a) (hb : b * b = b) :
    (a * b) * (a * b) = a * b := by
  calc (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = (a * a) * (b * b) := by rw [hab]; simp only [mul_assoc]
    _ = a * b := by rw [ha, hb]

private theorem mon_proj_absorb {R : Type} [Monoid R] (b p bh : R)
    (hbb : bh * b = 1) (hp : p * p = p) :
    (b * p * bh) * (b * p) = b * p := by
  calc (b * p * bh) * (b * p) = b * p * (bh * b) * p := by simp only [mul_assoc]
    _ = b * (p * p) := by rw [hbb, mul_one, mul_assoc]
    _ = b * p := by rw [hp]

private theorem mon_sub_trees {R : Type} [Monoid R] (bei pt beih v bc pb bch : R)
    (hvbc : v * (bc * pb) = bei * (v * pb)) (hbb : beih * bei = 1)
    (hpt : pt * (v * pb) = v * pb) :
    (bei * pt * beih) * (v * (bc * pb * bch)) = v * (bc * pb * bch) := by
  calc (bei * pt * beih) * (v * (bc * pb * bch))
      = (bei * pt * beih) * ((v * (bc * pb)) * bch) := by simp only [mul_assoc]
    _ = bei * pt * (beih * bei) * (v * pb) * bch := by rw [hvbc]; simp only [mul_assoc]
    _ = bei * (pt * (v * pb)) * bch := by rw [hbb, mul_one]; simp only [mul_assoc]
    _ = (bei * (v * pb)) * bch := by rw [hpt]
    _ = v * (bc * pb * bch) := by rw [← hvbc]; simp only [mul_assoc]

private theorem mon_int_trees {R : Type} [Monoid R]
    (sei sbei bei v bc sc sbc pch pwb bch : R)
    (hvbc : v * (bc * (pch * pwb)) = bei * (v * (pch * pwb)))
    (hbb_ei : sbei * bei = 1) (hbb_c : sbc * bc = 1)
    (hcw : pch * pwb = pwb * pch)
    (hsw : sei * (v * pwb) = v * (sc * pwb)) :
    (sei * sbei) * (v * (bc * (pch * pwb) * bch)) =
      v * ((sc * sbc) * (bc * (pch * pwb) * bch)) := by
  have hR := mon_star_cancel3 sc sbc bc (pch * pwb) bch hbb_c
  calc (sei * sbei) * (v * (bc * (pch * pwb) * bch))
      = (sei * sbei) * ((v * (bc * (pch * pwb))) * bch) := by simp only [mul_assoc]
    _ = sei * (sbei * bei) * (v * (pch * pwb)) * bch := by rw [hvbc]; simp only [mul_assoc]
    _ = (sei * (v * pwb)) * pch * bch := by rw [hbb_ei, mul_one, hcw]; simp only [mul_assoc]
    _ = v * (sc * (pwb * pch)) * bch := by rw [hsw]; simp only [mul_assoc]
    _ = v * (sc * (pch * pwb) * bch) := by rw [← hcw]; simp only [mul_assoc]
    _ = v * ((sc * sbc) * (bc * (pch * pwb) * bch)) := by rw [hR]

private theorem sg_anchor_ext {R : Type} [Semigroup R] (b p0 h0 w0 e : R)
    (hcw : w0 * e = e * w0) (hch : h0 * e = e * h0) (hhw : h0 * w0 = w0 * h0) :
    (b * ((p0 * h0) * w0)) * e = b * (((p0 * e) * w0) * h0) := by
  calc (b * ((p0 * h0) * w0)) * e
      = b * (p0 * h0 * (w0 * e)) := by simp only [mul_assoc]
    _ = b * (p0 * (h0 * e) * w0) := by rw [hcw]; simp only [mul_assoc]
    _ = b * ((p0 * e) * (h0 * w0)) := by rw [hch]; simp only [mul_assoc]
    _ = b * (((p0 * e) * w0) * h0) := by rw [hhw]; simp only [mul_assoc]

private theorem proj0_comm_of_disj {k₁ k₂ n : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (h : r₁.DisjointWires r₂) :
    r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 * r₁.basisOutcomeProjector 0 := by
  change r₁.embedMatrix _ * r₂.basisOutcomeProjector 0 =
    r₂.basisOutcomeProjector 0 * r₁.embedMatrix _
  exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint r₁) r₂ h _ 0

private theorem proj0_comm_embedUnitary_of_disj {k₁ k₂ n : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (h : r₁.DisjointWires r₂)
    (U : Unitary (2 ^ k₂)) :
    r₁.basisOutcomeProjector 0 * (r₂.embedUnitary U).1 =
      (r₂.embedUnitary U).1 * r₁.basisOutcomeProjector 0 := by
  rw [QRegister.embedUnitary_val]
  exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint r₂) r₁
    (QRegExt.disjointWires_symm h) U.1 0).symm

private theorem embedUnitary_comm_proj0_of_disj {k₁ k₂ n : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (h : r₁.DisjointWires r₂)
    (U : Unitary (2 ^ k₁)) :
    (r₁.embedUnitary U).1 * r₂.basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 * (r₁.embedUnitary U).1 := by
  rw [QRegister.embedUnitary_val]
  exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint r₁) r₂ h U.1 0

private theorem rElecEI_disj_rComb93 {n mPayload mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) :=
      (hCW.compose_right _).compose_right _
    let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
    (((rDataEI.compose (selCoreEI hmPay)).compose rElecAllPos).DisjointWires
      (rComb93 hmPay hmWB rCore rWB hCW)) := by
  intro hCEI rDataEI
  rw [QRegister.disjoint_iff]; intro t idx hEq
  have hL : ((rDataEI.compose (selCoreEI hmPay)).compose rElecAllPos) t =
      rCore (selPosInFullSys hmPay (rElecAllPos t)) := by
    dsimp only [rDataEI, selCoreEI, selCoreInEI, QRegister.compose_apply, QRegister.block,
      Fin.natAddEmb]
    have hc := QRegister.concat_apply_left rCore (rEnIdx9 hmWB rWB) hCEI
      (selPosInFullSys hmPay (rElecAllPos t))
    exact (congrArg rDataEI.wires (Fin.ext (by simp))).trans hc
  rw [hL] at hEq
  by_cases h8 : idx.val < 8
  · have hR := rComb93_u8 hmPay hmWB rCore rWB hCW ⟨idx.val, h8⟩
    have hi : (⟨(⟨idx.val, h8⟩ : Fin 8).val, by omega⟩ : Fin 93) = idx := Fin.ext rfl
    rw [hi] at hR; rw [hR] at hEq
    have hv := congrArg Fin.val (rCore.wires.injective hEq)
    have hge := selU8InCore_ge_3924 hmPay ⟨idx.val, h8⟩
    have hlt : (selPosInFullSys hmPay (rElecAllPos t)).val < 3924 := by
      have ht := t.isLt
      simp [selPosInFullSys, rElecAllPos, QRegister.block, QRegister.slice, QRegExt.ofFin]
    omega
  · by_cases h18 : idx.val < 18
    · have hR := rComb93_enIdx9 hmPay hmWB rCore rWB hCW ⟨idx.val - 9, by omega⟩
      by_cases h9 : idx.val = 8
      · have hidx8 : idx = ⟨8, by decide⟩ := Fin.ext h9
        subst hidx8
        have h8eq : rComb93 hmPay hmWB rCore rWB hCW ⟨8, by decide⟩ =
            BoothOpt_FastAnchorOuterAndStageBShave.rPeb10
              hmWB rWB ⟨0, by decide⟩ :=
          (QRegister.concat_apply_left _ _ _ (Fin.natAdd 8 (⟨0, by decide⟩ : Fin 10))).trans
            (QRegister.concat_apply_right _ _ _ ⟨0, by decide⟩)
        rw [h8eq] at hEq
        exact (hCW.compose_right _).ne _ _ hEq
      · have hi : (⟨9 + (idx.val - 9), by omega⟩ : Fin 93) = idx := Fin.ext (by dsimp; omega)
        rw [hi] at hR; rw [hR] at hEq
        exact ((hCW.compose_right _).compose_right _).ne _ _ hEq
    · have hR := rComb93_scr75 hmPay hmWB rCore rWB hCW ⟨idx.val - 18, by omega⟩
      have hi : (⟨18 + (idx.val - 18), by omega⟩ : Fin 93) = idx := Fin.ext (by dsimp; omega)
      rw [hi] at hR; rw [hR] at hEq
      exact (disj_rScr75_right hmWB hCW).ne _ _ hEq

private theorem hCombPres_above18_of_disj {n mPayload mWB K : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB)
    (r : QRegister K n) (hDisj : r.DisjointWires (rScr75 hmWB rWB))
    (U : Operator.Unitary (2 ^ K)) :
    ∀ (idx : Wire 93), 18 ≤ idx.val → ∀ g' g : Fin (2 ^ n),
      (r.embedUnitary U).1 g' g ≠ 0 →
      basisBits n g' (rComb93 hmPay hmWB rCore rWB hCW idx) =
        basisBits n g (rComb93 hmPay hmWB rCore rWB hCW idx) := by
  intro idx hge g' g hnz
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply] at hnz
  have hR := rComb93_scr75 hmPay hmWB rCore rWB hCW ⟨idx.val - 18, by omega⟩
  have hi : (⟨18 + (idx.val - 18), by omega⟩ : Fin 93) = idx := Fin.ext (by dsimp; omega)
  rw [hi] at hR; rw [hR]
  by_contra hne; apply hnz
  have hnot : rScr75 hmWB rWB ⟨idx.val - 18, by omega⟩ ∉ Set.range r.wires :=
    fun ⟨u, hu⟩ ↦ hDisj.ne u _ hu
  have hrest : (r.basisSplitEquiv g').2 ≠ (r.basisSplitEquiv g).2 :=
    fun hr ↦ hne (congrFun hr ⟨_, hnot⟩)
  simp [hrest]

private theorem ketPredProj_ext_and_eq_mul {M n kD : ℕ}
    (rData : QRegister kD n) (rAnc rHeld : QRegister 18 n)
    (hDA : rData.DisjointWires rAnc) (_hAH : (rData.concat rAnc hDA).DisjointWires rHeld)
    (L : Slot18Lens kD) (rComb : QRegister M n) (Inv : BitAssignment M → Prop) :
    p2d_ketPredProj (fun β ↦ (S_slot0Lens rData L β ∧ ∀ j : Fin 18, β (rHeld j) = 0) ∧
        Inv (fun idx ↦ β (rComb idx))) =
      ((rData.concat rAnc hDA).embedMatrix (P_slot0 L) * rHeld.basisOutcomeProjector 0) *
        p2d_ketPredProj (fun β ↦ Inv (fun idx ↦ β (rComb idx))) := by
  apply matrix_ext_ket; intro β
  rw [p2d_proj_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_proj_ket]
  by_cases hInv : Inv (fun idx ↦ β (rComb idx))
  · rw [ite_eq_left hInv, ket_basisOutcomeProjector_zero]
    by_cases hH : ∀ j : Fin 18, β (rHeld j) = 0
    · rw [ite_eq_left hH, embedMatrix_p_slot0_mulVec_ket rData rAnc hDA L β]
      by_cases hS : S_slot0Lens rData L β
      · rw [ite_eq_left hS, ite_eq_left ⟨⟨hS, hH⟩, hInv⟩]
      · rw [ite_eq_right hS, ite_eq_right (fun h ↦ hS h.1.1)]
    · rw [ite_eq_right hH, Matrix.mulVec_zero, ite_eq_right (fun h ↦ hH h.1.2)]
  · rw [ite_eq_right hInv, Matrix.mulVec_zero, Matrix.mulVec_zero, ite_eq_right (fun h ↦ hInv h.2)]

private theorem dPostTreesBell18Fast_subspace {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWB : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 rHeld18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18) (hCH : rCore.DisjointWires rHeld18)
    (hCW : rCore.DisjointWires rWB) (hAH : rAnchor18.DisjointWires rHeld18)
    (hAW : rAnchor18.DisjointWires rWB) (hHW : rHeld18.DisjointWires rWB) :
    let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) :=
      (hCW.compose_right _).compose_right _
    let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
    let hDA_EI : rDataEI.DisjointWires rAnchor18 :=
      qreg_disjoint_concat_left hCA (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right
        _))
    let hDH_EI : rDataEI.DisjointWires rHeld18 :=
      qreg_disjoint_concat_left hCH (QRegExt.disjointWires_symm ((hHW.compose_right _).compose_right
        _))
    let rActEI := rDataEI.concat rAnchor18 hDA_EI
    let rElecEI := (rDataEI.compose (selCoreEI hmPay)).compose rElecAllPos
    let hDS_EI : rDataEI.DisjointWires (rScr75 hmWB rWB) :=
      qreg_disjoint_concat_left (disj_rScr75_right hmWB hCW)
        ((rPeb10_disj_rScr75 hmWB rWB).compose_left _)
    let hCS_EI := hDS_EI.compose_left (selCoreEI hmPay)
    let L_ei := fastEILens hmPay
    let rC93 := rComb93 hmPay hmWB rCore rWB hCW
    let dFix : (Fin 18 → Bool) → DynamicCircuit Var n := fun f ↦
      dFixHole218 (le_refl 75) v f (rDataEI.compose (selCoreEI hmPay)) (rScr75 hmWB rWB) hCS_EI
    let dInner := Bell18TeleportCore.dPostBellInnerFused v rElecEI bitOfElec3924
      rAnchor18 rHeld18 (QRegExt.disjointWires_symm hAH) dFix
    let B_ei := Bell18TeleportCore.uBellSlot rDataEI rHeld18 hDH_EI (toSlotK18 L_ei)
    let S_ei := rActEI.embedUnitary (uLensSwap L_ei)
    let S_ext : BitAssignment n → Prop := fun β ↦
      S_slot0Lens rDataEI L_ei β ∧ ∀ j : Fin 18, β (rHeld18 j) = 0
    Bell18TeleportCore.SubspaceStep
      (B_ei.1 * p2d_ketPredProj (fun β ↦ S_ext β ∧ invTreesIn93 (fun idx ↦ β (rC93 idx))))
      (S_ei.1 * p2d_ketPredProj (fun β ↦ S_ext β ∧ invTreesIn93 (fun idx ↦ β (rC93 idx))))
      (toDynWG v rC93 dInner ctxFastTrees93) := by
  intro hCEI rDataEI hDA_EI hDH_EI rActEI rElecEI hDS_EI hCS_EI L_ei rC93 dFix dInner B_ei S_ei
    S_ext
  have hActH : rActEI.DisjointWires rHeld18 := qreg_disjoint_concat_left hDH_EI hAH
  have hEH : rElecEI.DisjointWires rHeld18 := (hDH_EI.compose_left _).compose_left _
  have hEM : rElecEI.DisjointWires rAnchor18 := (hDA_EI.compose_left _).compose_left _
  let P_h := p2d_ketPredProj (fun β ↦ invHole93 (fun idx ↦ β (rC93 idx)))
  let P_base := rActEI.embedMatrix (P_slot0 L_ei) * rHeld18.basisOutcomeProjector 0
  let R_h := P_base * P_h
  have hPh_herm : P_hᴴ = P_h := p2d_ketPredProj_conjTranspose _
  have hPh_idem : P_h * P_h = P_h := by
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, p2d_proj_ket]
    by_cases h : invHole93 (fun idx ↦ β (rC93 idx))
    · rw [ite_eq_left h, p2d_proj_ket, ite_eq_left h]
    · rw [ite_eq_right h, Matrix.mulVec_zero]
  have hFixStep : ∀ (f : Fin 18 → Bool) (R : Operator (2 ^ n)), P_h * R = R →
      Bell18TeleportCore.SubspaceStep
        ((rDataEI.embedUnitary (Bell18TeleportCore.uSlotFix (toSlotK18 L_ei) f)).1 * R)
        R (dFix f) := fun f R hPR ↦ by
    have hRaw := dFixHole218_slot_realizes (le_refl 75) v f rDataEI (selCoreEI hmPay)
      (sFnEI (fullSysCoreWires mPayload)) L_ei (rScr75 hmWB rWB) hDS_EI (hsFnEI_had hmPay)
      (hTblBit_fastEILens hmPay rCore (rEnIdx9 hmWB rWB) hCEI)
      (fun _ ↦ True) (fun _ _ _ ↦ Iff.rfl)
    have hPEq : P_h = p2d_ketPredProj (fun β ↦ True ∧
        invHoleSlot218 (le_refl 75) rDataEI (sFnEI (fullSysCoreWires mPayload))
          (rScr75 hmWB rWB) β) :=
      p2d_ketPredProj_congr_fast fun β ↦ (invHole93_iff_invHoleSlot218 hmPay hmWB rCore rWB hCW
        β).trans ⟨fun h ↦ ⟨trivial, h⟩, And.right⟩
    rw [← hPEq, ← tcUSlotFix_eq L_ei f] at hRaw
    have hUFixSq : rDataEI.embedUnitary (Bell18TeleportCore.uSlotFix (toSlotK18 L_ei) f) *
        rDataEI.embedUnitary (Bell18TeleportCore.uSlotFix (toSlotK18 L_ei) f) = 1 := by
      rw [← QRegister.embedUnitary_mul, tcUSlotFix_eq, diagSignUnitary_mul_self,
          QRegister.embedUnitary_one]
    have hCommFix : P_h *
        (rDataEI.embedUnitary (Bell18TeleportCore.uSlotFix (toSlotK18 L_ei) f)).1 =
        (rDataEI.embedUnitary (Bell18TeleportCore.uSlotFix (toSlotK18 L_ei) f)).1 * P_h := by
      rw [tcUSlotFix_eq, QRegister.embedUnitary_val, diagSignUnitary]
      change P_h * rDataEI.embedMatrix (Matrix.diagonal _) = _
      rw [QRegister.embedMatrix_diagonal]
      exact ketPredProj_comm_diag _ _
    have hPR' : P_h *
        ((rDataEI.embedUnitary (Bell18TeleportCore.uSlotFix (toSlotK18 L_ei) f)).1 * R) =
        (rDataEI.embedUnitary (Bell18TeleportCore.uSlotFix (toSlotK18 L_ei) f)).1 * R := by
      rw [← Matrix.mul_assoc, hCommFix, Matrix.mul_assoc, hPR]
    exact tcSub_of_p2d_selfInv hPh_herm hPR' hUFixSq hRaw
  have hCommBase : P_h * P_base = P_base * P_h := by
    have hEq := ketPredProj_ext_and_eq_mul rDataEI rAnchor18 rHeld18 hDA_EI hActH L_ei rC93
      invHole93
    have hEq2 : p2d_ketPredProj (fun β ↦ invHole93 (fun idx ↦ β (rC93 idx)) ∧ S_ext β) =
        P_h * P_base := by
      have hSym := p2d_ketPredProj_congr_fast (n := n)
        (S₁ := fun β ↦ S_ext β ∧ invHole93 (fun idx ↦ β (rC93 idx)))
        (S₂ := fun β ↦ invHole93 (fun idx ↦ β (rC93 idx)) ∧ S_ext β) (fun _ ↦ And.comm)
      have hH1 := p2d_ketPredProj_conjTranspose
        (fun β ↦ S_ext β ∧ invHole93 (fun idx ↦ β (rC93 idx)))
      have hPbH : P_baseᴴ = P_base := by
        dsimp only [P_base]
        rw [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose,
            ← rActEI.embedMatrix_conjTranspose, P_slot0_conjTranspose,
            (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rActEI) rHeld18 hActH _ 0]
      rw [← hSym, ← hH1, hEq, Matrix.conjTranspose_mul, hPh_herm, hPbH]
    exact hEq2.symm.trans ((p2d_ketPredProj_congr_fast (fun _ ↦ And.comm)).trans hEq)
  have hPh_Rh : P_h * R_h = R_h := by
    dsimp only [R_h]; rw [← Matrix.mul_assoc, hCommBase, Matrix.mul_assoc, hPh_idem]
  have hPh_out : P_h *
      (((rDataEI.concat rAnchor18 hDA_EI).embedUnitary
        (Bell18TeleportCore.uLensSwap (toSlotK18 L_ei))).1 * R_h) =
      ((rDataEI.concat rAnchor18 hDA_EI).embedUnitary
        (Bell18TeleportCore.uLensSwap (toSlotK18 L_ei))).1 * R_h := by
    rw [tcEmbed_uLensSwap_eq]
    have hCSw : P_h * S_ei.1 = S_ei.1 * P_h :=
      ketPredProj_comm_of_preserves (fun β ↦ invHole93 (fun idx ↦ β (rC93 idx))) _
        (fun i j hnz ↦ by
          refine iff_of_eq (congrArg invHole93 (funext fun idx ↦ ?_))
          by_cases heq :
              (rActEI.basisSplitEquiv i).2 = (rActEI.basisSplitEquiv j).2
          · have hnz' : (uLensSwap L_ei).1 (rActEI.extractIndex i)
                (rActEI.extractIndex j) ≠ 0 := by
              intro h0; apply hnz
              rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply,
                  ite_eq_left heq, mul_one]
              exact h0
            have hi : rActEI.replaceIndex j (rActEI.extractIndex i) = i := by
              rw [QRegister.replaceIndex, ← heq,
                  ← QRegister.basisSplitEquiv_apply_fst,
                  Prod.mk.eta, Equiv.symm_apply_apply]
            rw [← hi]
            exact hCombPres_fastEILens_swap hmPay hmWB rCore rAnchor18 rWB
              hCA hCW hAW idx j (rActEI.extractIndex i) hnz'
          · exfalso; apply hnz
            rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply,
                ite_eq_right heq, mul_zero])
    rw [← Matrix.mul_assoc, hCSw, Matrix.mul_assoc, hPh_Rh]
  have hSlot0_Rh : rActEI.embedMatrix (Bell18TeleportCore.P_slot0 (toSlotK18 L_ei)) * R_h =
      R_h := by
    rw [tcPSlot0_eq]; dsimp only [R_h, P_base]
    have hIdem : P_slot0 L_ei * P_slot0 L_ei = P_slot0 L_ei := by
      rw [P_slot0_eq_diagonal, Matrix.diagonal_mul_diagonal]
      apply congrArg Matrix.diagonal; funext z; split_ifs <;> simp only [mul_one, mul_zero]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rActEI.embedMatrix_mul, hIdem]
  have hH0_Rh : rHeld18.basisOutcomeProjector 0 * R_h = R_h := by
    dsimp only [R_h, P_base]
    have hC0 := ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rActEI) rHeld18 hActH
      (P_slot0 L_ei) 0).symm
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hC0, Matrix.mul_assoc (rActEI.embedMatrix _),
        QRegister.basisOutcomeProjector_mul_self]
  have hPh_fwd : ∀ f₁ f₂ : Fin 18 → Bool,
      P_h * ((Bell18TeleportCore.cPauliBankFwd rElecEI bitOfElec3924 f₁ f₂).eval.1 *
        (((rDataEI.concat rAnchor18 hDA_EI).embedUnitary
          (Bell18TeleportCore.uLensSwap (toSlotK18 L_ei))).1 * R_h)) =
      (Bell18TeleportCore.cPauliBankFwd rElecEI bitOfElec3924 f₁ f₂).eval.1 *
        (((rDataEI.concat rAnchor18 hDA_EI).embedUnitary
          (Bell18TeleportCore.uLensSwap (toSlotK18 L_ei))).1 * R_h) := fun f₁ f₂ ↦ by
    have hCFwd : P_h *
        (Bell18TeleportCore.cPauliBankFwd rElecEI bitOfElec3924 f₁ f₂).eval.1 =
        (Bell18TeleportCore.cPauliBankFwd rElecEI bitOfElec3924 f₁ f₂).eval.1 * P_h :=
      ketPredProj_comm_of_preserves (fun β ↦ invHole93 (fun idx ↦ β (rC93 idx))) _
        (fun i j hnz ↦ iff_of_eq (congrArg invHole93 (funext fun idx ↦
          Bell18TeleportCore.cPauliBankFwd_preserves_disjoint_wire
            rElecEI bitOfElec3924 f₁ f₂ rC93
            (rElecEI_disj_rComb93 hmPay hmWB rCore rWB hCW) idx i j hnz)))
    rw [← Matrix.mul_assoc, hCFwd, Matrix.mul_assoc, hPh_out]
  have hHoleStep := Bell18TeleportCore.subspaceStep_dPostBellInnerFused v rDataEI rElecEI
    bitOfElec3924 rAnchor18 rHeld18 hDA_EI hDH_EI (QRegExt.disjointWires_symm hAH) hEH hEM
      (toSlotK18 L_ei)
    (isBankSlotLens_fastEILens hmPay hmWB rCore rWB hCW)
    (bitOfElec3924_fastEILens hmPay hmWB rCore rWB hCW) hSlot0_Rh hH0_Rh
    (fun f f₁ f₂ ↦ hFixStep f _ (hPh_fwd f₁ f₂))
  dsimp only [R_h, P_base, P_h] at hHoleStep
  rw [tcEmbed_uLensSwap_eq, ← ketPredProj_ext_and_eq_mul rDataEI rAnchor18 rHeld18 hDA_EI hActH
      L_ei rC93 invHole93] at hHoleStep
  let rDH_EI := rDataEI.concat rHeld18 hDH_EI
  let V_H := (selMeasInAct (fullSysCoreWires mPayload + 9)).embedUnitary
    (Bell18TeleportCore.cHadReg
      (QRegExt.idReg 18)).eval
  have hH_emb : (Bell18TeleportCore.cHadReg rHeld18).eval = rDH_EI.embedUnitary V_H := by
    dsimp only [V_H]
    rw [cHadReg_eval_eq_embed rHeld18]
    exact (congrArg (fun r : QRegister 18 n ↦ r.embedUnitary
      (Bell18TeleportCore.cHadReg
        (QRegExt.idReg 18)).eval)
      (concat_compose_selMeasInAct rDataEI rHeld18 hDH_EI).symm).trans
      (QRegister.embedUnitary_compose _ _ _)
  have hBei_emb : B_ei = rDH_EI.embedUnitary (uLensWrite L_ei * V_H) := by
    dsimp only [B_ei, Bell18TeleportCore.uBellSlot]
    rw [tcEmbed_uLensWrite_eq, hH_emb, ← QRegister.embedUnitary_mul]
  have hC93H : rC93.DisjointWires rHeld18 :=
    qreg_disjoint_concat_left
      (qreg_disjoint_concat_left (hCH.compose_left _) ((QRegExt.disjointWires_symm hHW).compose_left
        _))
      (QRegExt.disjointWires_symm (disj_rScr75_right hmWB hHW))
  have hPresVH : ∀ (idx : Wire 93) (g : Fin (2 ^ n))
      (y : Fin (2 ^ ((fullSysCoreWires mPayload + 9) + 18))),
      V_H.1 y (rDH_EI.extractIndex g) ≠ 0 →
      basisBits n (rDH_EI.replaceIndex g y) (rC93 idx) = basisBits n g (rC93 idx) := by
    intro idx g y hnz
    by_cases hm : rC93 idx ∈ Set.range rDH_EI.wires
    · obtain ⟨u, hu⟩ := hm
      have hEx : basisBits _ (rDH_EI.extractIndex g) u = basisBits n g (rDH_EI u) :=
        QRegister.basisBits_extractIndex rDH_EI g u
      rw [← hu, QRegister.basisBits_replaceIndex_apply, ← hEx]
      rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply] at hnz
      by_contra hne; apply hnz
      have hnot : u ∉ Set.range (selMeasInAct (fullSysCoreWires mPayload + 9)).wires := by
        rintro ⟨j, rfl⟩
        have h1 : rDH_EI (selMeasInAct (fullSysCoreWires mPayload + 9) j) = rHeld18 j := by
          change (rDH_EI.compose (selMeasInAct _)) j = rHeld18 j
          rw [concat_compose_selMeasInAct]
        exact hC93H.ne idx j (hu.symm.trans h1)
      have hrest :
          ((selMeasInAct (fullSysCoreWires mPayload + 9)).basisSplitEquiv y).2 ≠
            ((selMeasInAct (fullSysCoreWires mPayload + 9)).basisSplitEquiv
              (rDH_EI.extractIndex g)).2 :=
        fun hr ↦ hne (congrFun hr ⟨_, hnot⟩)
      simp [hrest]
    · exact QRegister.basisBits_replaceIndex_of_not_mem rDH_EI g y (rC93 idx) hm
  have hDHScr : rDH_EI.DisjointWires (rScr75 hmWB rWB) :=
    qreg_disjoint_concat_left hDS_EI (disj_rScr75_right hmWB hHW)
  have hBAbove : ∀ (idx : Wire 93), 18 ≤ idx.val → ∀ g' g : Fin (2 ^ n),
      B_ei.1 g' g ≠ 0 → basisBits n g' (rC93 idx) = basisBits n g (rC93 idx) := by
    rw [hBei_emb]
    exact hCombPres_above18_of_disj hmPay hmWB rCore rWB hCW rDH_EI hDHScr
      (uLensWrite L_ei * V_H)
  have hCommB : DiagCtxWGCommutesWith rC93 B_ei ctxFastTrees93 := by
    rw [hBei_emb]
    exact diagCtxWGWritesAbove_to_commutesWith rDH_EI (uLensWrite L_ei * V_H) rC93 18
      (rComb93_above18_not_mem_actEI hmPay hmWB rCore rHeld18 rWB hCH hCW hHW)
      (hCombPres_mul rDH_EI rC93
        (hCombPres_fastEILens_write hmPay hmWB rCore rHeld18 rWB hCH hCW hHW) hPresVH)
      ctxFastTrees93_writesAbove18
  have hCommS : DiagCtxWGCommutesWith rC93 S_ei ctxFastTrees93 :=
    diagCtxWGWritesAbove_to_commutesWith rActEI (uLensSwap L_ei) rC93 18
      (rComb93_above18_not_mem_actEI hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW)
      (hCombPres_fastEILens_swap hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW)
      ctxFastTrees93_writesAbove18
  have hExt : ∀ β₁ β₂ : BitAssignment n,
      (∀ w : Wire n, (∀ idx : Wire 93, 18 ≤ idx.val → w ≠ rC93 idx) → β₁ w = β₂ w) →
      (S_ext β₁ ↔ S_ext β₂) := by
    intro β₁ β₂ hEq
    have hD : (fun u ↦ β₁ (rDataEI u)) = (fun u ↦ β₂ (rDataEI u)) := funext fun u ↦
      hEq (rDataEI u) fun idx hge h ↦ by
        have hR := rComb93_scr75 hmPay hmWB rCore rWB hCW ⟨idx.val - 18, by omega⟩
        have hi : (⟨18 + (idx.val - 18), by omega⟩ : Fin 93) = idx := Fin.ext (by dsimp; omega)
        rw [hi] at hR; exact hDS_EI.ne u _ (h.trans hR)
    have hS0 : S_slot0Lens rDataEI L_ei β₁ ↔ S_slot0Lens rDataEI L_ei β₂ := by
      dsimp only [S_slot0Lens]
      have hdEq : (basisBitsEquiv _).symm (fun u ↦ β₁ (rDataEI u)) =
          (basisBitsEquiv _).symm (fun u ↦ β₂ (rDataEI u)) := congrArg _ hD
      have hEx : ∀ β : BitAssignment n,
          rDataEI.extractIndex ((basisBitsEquiv n).symm β) =
            (basisBitsEquiv _).symm (fun u ↦ β (rDataEI u)) := fun β ↦ by
        apply (basisBitsEquiv _).injective; ext u
        rw [QRegister.basisBits_extractIndex, (basisBitsEquiv n).apply_symm_apply,
            (basisBitsEquiv _).apply_symm_apply]
      rw [hEx β₁, hEx β₂, hdEq]
    have hH0 : (∀ j : Fin 18, β₁ (rHeld18 j) = 0) ↔ (∀ j : Fin 18, β₂ (rHeld18 j) = 0) :=
      forall_congr' fun j ↦ by
        rw [hEq (rHeld18 j) fun idx hge h ↦ by
          have hR := rComb93_scr75 hmPay hmWB rCore rWB hCW ⟨idx.val - 18, by omega⟩
          have hi : (⟨18 + (idx.val - 18), by omega⟩ : Fin 93) = idx := Fin.ext (by dsimp; omega)
          rw [hi] at hR; exact (disj_rScr75_right hmWB hHW).ne j _ (h.trans hR)]
    exact and_congr hS0 hH0
  exact subspaceStep_toDynWG_bell 18 v rC93 S_ext hExt invHole93 dInner B_ei S_ei hBAbove
    hHoleStep ctxFastTrees93 invTreesIn93 ctxFastTrees93_cohAbove ctxFastTrees93_writesAbove18
    hCommB hCommS validAtWith_ctxFastTrees93

private theorem dPostCoreBell18Fast_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWB : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rAnchor18 rHeld18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hCA : rCore.DisjointWires rAnchor18) (hCH : rCore.DisjointWires rHeld18)
    (hCW : rCore.DisjointWires rWB) (hAH : rAnchor18.DisjointWires rHeld18)
    (hAW : rAnchor18.DisjointWires rWB) (hHW : rHeld18.DisjointWires rWB) :
    let L_core := coinBarrelFastSlot18Lens hmPay
    let rCoreAnchor := rCore.concat rAnchor18 hCA
    let B_c := Bell18TeleportCore.uBellSlot rCore rHeld18 hCH (toSlotK18 L_core)
    let P_base := (rCoreAnchor.embedMatrix (P_slot0 L_core) * rHeld18.basisOutcomeProjector 0) *
      rWB.basisOutcomeProjector 0
    HoistBorrow42ProjBridge.RealizesOnProj (B_c.1 * P_base)
      (rCoreAnchor.embedUnitary (uLensSwap L_core) * star B_c)
      (dPostCoreBell18Fast hmPay hmWB v rCore rAnchor18 rHeld18 rWB hCW hAH) := by
  intro L_core rCoreAnchor B_c P_base
  have hCAW : rCoreAnchor.DisjointWires rWB := qreg_disjoint_concat_left hCW hAW
  have hCAH : rCoreAnchor.DisjointWires rHeld18 := qreg_disjoint_concat_left hCH hAH
  have hCHW : (rCore.concat rHeld18 hCH).DisjointWires rWB := qreg_disjoint_concat_left hCW hHW
  let P_wb := rWB.basisOutcomeProjector 0
  let P_ch0 := rCoreAnchor.embedMatrix (P_slot0 L_core) * rHeld18.basisOutcomeProjector 0
  let P_out := B_c.1 * P_base * B_c.1ᴴ
  let S_c := rCoreAnchor.embedUnitary (uLensSwap L_core)
  let U_out := S_c * star B_c
  have hPch0_herm : P_ch0ᴴ = P_ch0 := by
    dsimp only [P_ch0]
    rw [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose,
        ← rCoreAnchor.embedMatrix_conjTranspose, P_slot0_conjTranspose,
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreAnchor) rHeld18 hCAH _ 0]
  have hPbase_herm : P_baseᴴ = P_base := by
    dsimp only [P_base]
    have hComm : P_ch0 * P_wb = P_wb * P_ch0 := by
      dsimp only [P_ch0, P_wb]
      rw [Matrix.mul_assoc,
          proj0_comm_of_disj rHeld18 rWB hHW,
          ← Matrix.mul_assoc,
          (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreAnchor) rWB hCAW _ 0,
          Matrix.mul_assoc]
    rw [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose, hPch0_herm, hComm]
  have hPout_herm : P_outᴴ = P_out := by
    dsimp only [P_out]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hPbase_herm]
    exact (mul_assoc B_c.1 P_base B_c.1ᴴ).symm
  have hBc_comm_wb : B_c.1 * P_wb = P_wb * B_c.1 := by
    dsimp only [B_c, Bell18TeleportCore.uBellSlot, P_wb]
    rw [Submonoid.coe_mul, cHadReg_eval_eq_embed, Matrix.mul_assoc,
        embedUnitary_comm_proj0_of_disj rHeld18 rWB hHW _,
        ← Matrix.mul_assoc,
        embedUnitary_comm_proj0_of_disj (rCore.concat rHeld18 hCH) rWB hCHW _,
        Matrix.mul_assoc]
  have hBcH_comm_wb : P_wb * B_c.1ᴴ = B_c.1ᴴ * P_wb := by
    dsimp only [P_wb] at hBc_comm_wb ⊢
    simpa only [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
      congrArg Matrix.conjTranspose hBc_comm_wb
  have hCommSing : ∀ (M : Operator (2 ^ n)),
      (∀ (r : QRegister 1 n), (∀ i, r i ∈ Set.range rWB.wires) →
        r.basisOutcomeProjector 0 * M = M * r.basisOutcomeProjector 0) →
      HasCleanTailFrom (rCombPeb rCore rWB (by omega) hCW) (fullSysCoreWires mPayload + 8)
        (M * P_wb) := fun M hM ↦
    hasCleanTailFrom_of_comm_wbSingleton rCore rWB (by omega) hCW M fun k ↦
      hM _ fun _ ↦ ⟨_, rfl⟩
  have hSing_Bc : ∀ (r : QRegister 1 n), r.DisjointWires (rCore.concat rHeld18 hCH) →
      r.basisOutcomeProjector 0 * B_c.1 = B_c.1 * r.basisOutcomeProjector 0 := fun r hr ↦ by
    have hrH : r.DisjointWires rHeld18 := by
      rw [QRegister.disjoint_iff]; intro i j hij
      exact hr.ne i (Fin.natAdd _ j) (hij.trans (QRegister.concat_apply_right _ _ _ j).symm)
    dsimp only [B_c, Bell18TeleportCore.uBellSlot]
    rw [Submonoid.coe_mul, cHadReg_eval_eq_embed, ← Matrix.mul_assoc,
        proj0_comm_embedUnitary_of_disj r (rCore.concat rHeld18 hCH) hr _, Matrix.mul_assoc,
        proj0_comm_embedUnitary_of_disj r rHeld18 hrH _, ← Matrix.mul_assoc]
  have hTailOut : HasCleanTailFrom (rCombPeb rCore rWB (by omega) hCW)
      (fullSysCoreWires mPayload + 8) P_out := by
    have hEq : P_out = (B_c.1 * P_ch0 * B_c.1ᴴ) * P_wb :=
      sg_conj_comm_right B_c.1 P_ch0 P_wb B_c.1ᴴ hBcH_comm_wb
    rw [hEq]
    refine hCommSing _ fun r hr ↦ ?_
    have hrCH : r.DisjointWires (rCore.concat rHeld18 hCH) := by
      rw [QRegister.disjoint_iff]; intro i j hij
      obtain ⟨w, hw⟩ := hr i; exact hCHW.ne j w (hij.symm.trans hw.symm)
    have hrCA : r.DisjointWires rCoreAnchor := by
      rw [QRegister.disjoint_iff]; intro i j hij
      obtain ⟨w, hw⟩ := hr i; exact hCAW.ne j w (hij.symm.trans hw.symm)
    have hrH : r.DisjointWires rHeld18 := by
      rw [QRegister.disjoint_iff]; intro i j hij
      obtain ⟨w, hw⟩ := hr i; exact hHW.ne j w (hij.symm.trans hw.symm)
    have h1 := hSing_Bc r hrCH
    have h1H : r.basisOutcomeProjector 0 * B_c.1ᴴ = B_c.1ᴴ * r.basisOutcomeProjector 0 := by
      simpa only [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
        (congrArg Matrix.conjTranspose h1).symm
    have h2 : r.basisOutcomeProjector 0 * P_ch0 = P_ch0 * r.basisOutcomeProjector 0 := by
      dsimp only [P_ch0]
      rw [← Matrix.mul_assoc,
          ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreAnchor) r
            (QRegExt.disjointWires_symm hrCA) _ 0).symm,
          Matrix.mul_assoc, proj0_comm_of_disj r rHeld18 hrH, ← Matrix.mul_assoc]
    exact sg_comm3 _ B_c.1 P_ch0 B_c.1ᴴ h1 h2 h1H
  have hUoutP : U_out.1 * P_out = ((S_c.1 * P_ch0) * B_c.1ᴴ) * P_wb := by
    have hBB : (star B_c).1 * B_c.1 = 1 := congrArg Subtype.val (Unitary.star_mul_self B_c)
    dsimp only [U_out, P_out, P_base]
    rw [Submonoid.coe_mul]
    exact mon_star_cancel_wb S_c.1 (star B_c).1 B_c.1 P_ch0 P_wb B_c.1ᴴ hBB hBcH_comm_wb
  have hTailU : HasCleanTailFrom (rCombPeb rCore rWB (by omega) hCW)
      (fullSysCoreWires mPayload + 8) (U_out.1 * P_out) := by
    rw [hUoutP]
    refine hCommSing _ fun r hr ↦ ?_
    have hrCH : r.DisjointWires (rCore.concat rHeld18 hCH) := by
      rw [QRegister.disjoint_iff]; intro i j hij
      obtain ⟨w, hw⟩ := hr i; exact hCHW.ne j w (hij.symm.trans hw.symm)
    have hrCA : r.DisjointWires rCoreAnchor := by
      rw [QRegister.disjoint_iff]; intro i j hij
      obtain ⟨w, hw⟩ := hr i; exact hCAW.ne j w (hij.symm.trans hw.symm)
    have hrH : r.DisjointWires rHeld18 := by
      rw [QRegister.disjoint_iff]; intro i j hij
      obtain ⟨w, hw⟩ := hr i; exact hHW.ne j w (hij.symm.trans hw.symm)
    have h1H : r.basisOutcomeProjector 0 * B_c.1ᴴ = B_c.1ᴴ * r.basisOutcomeProjector 0 := by
      simpa only [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
        (congrArg Matrix.conjTranspose (hSing_Bc r hrCH)).symm
    have hSc : r.basisOutcomeProjector 0 * S_c.1 = S_c.1 * r.basisOutcomeProjector 0 :=
      proj0_comm_embedUnitary_of_disj r rCoreAnchor hrCA _
    have h2 : r.basisOutcomeProjector 0 * P_ch0 = P_ch0 * r.basisOutcomeProjector 0 := by
      dsimp only [P_ch0]
      rw [← Matrix.mul_assoc,
          ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreAnchor) r
            (QRegExt.disjointWires_symm hrCA) _ 0).symm,
          Matrix.mul_assoc, proj0_comm_of_disj r rHeld18 hrH, ← Matrix.mul_assoc]
    exact sg_comm3 _ S_c.1 P_ch0 B_c.1ᴴ hSc h2 h1H
  let hCEI : rCore.DisjointWires (rEnIdx9 hmWB rWB) :=
    (hCW.compose_right _).compose_right _
  let rDataEI := rCore.concat (rEnIdx9 hmWB rWB) hCEI
  let hDA_EI : rDataEI.DisjointWires rAnchor18 :=
    qreg_disjoint_concat_left hCA (QRegExt.disjointWires_symm ((hAW.compose_right _).compose_right
      _))
  let hDH_EI : rDataEI.DisjointWires rHeld18 :=
    qreg_disjoint_concat_left hCH (QRegExt.disjointWires_symm ((hHW.compose_right _).compose_right
      _))
  let rActEI := rDataEI.concat rAnchor18 hDA_EI
  let L_ei := fastEILens hmPay
  let rC93 := rComb93 hmPay hmWB rCore rWB hCW
  let B_ei := Bell18TeleportCore.uBellSlot rDataEI rHeld18 hDH_EI (toSlotK18 L_ei)
  let S_ei := rActEI.embedUnitary (uLensSwap L_ei)
  let P_t0 := p2d_ketPredProj (fun β ↦
    (S_slot0Lens rDataEI L_ei β ∧ ∀ j : Fin 18, β (rHeld18 j) = 0) ∧
      invTreesIn93 (fun idx ↦ β (rC93 idx)))
  let P_trees := B_ei.1 * P_t0 * B_ei.1ᴴ
  have hPt_herm : P_treesᴴ = P_trees := by
    dsimp only [P_trees]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        p2d_ketPredProj_conjTranspose, Matrix.mul_assoc]
  have hSubTrees := tcSub_mul_right B_ei.1ᴴ
    (dPostTreesBell18Fast_subspace hmPay hmWB v rCore rAnchor18 rHeld18 rWB
      hCA hCH hCW hAH hAW hHW)
  have hUeiPt : (S_ei * star B_ei).1 * P_trees = S_ei.1 * P_t0 * B_ei.1ᴴ := by
    have hBB : (star B_ei).1 * B_ei.1 = 1 := congrArg Subtype.val (Unitary.star_mul_self B_ei)
    dsimp only [P_trees]
    rw [Submonoid.coe_mul]
    exact mon_star_cancel3 S_ei.1 (star B_ei).1 B_ei.1 P_t0 B_ei.1ᴴ hBB
  have hTrees := pebRealizes_of_tc hPt_herm
    (Bell18TeleportCore.RealizesOnProj.of_subspaceStep
      (Bell18TeleportCore.subspaceStep_congr_out hUeiPt.symm hSubTrees))
  let V := (vLinUnitary hmPay hmWB rCore rWB hCW).1
  have hVBc : V * (B_c.1 * P_base) = B_ei.1 * (V * P_base) := by
    have hVH : V * (Bell18TeleportCore.cHadReg rHeld18).eval.1 =
        (Bell18TeleportCore.cHadReg rHeld18).eval.1 * V := by
      rw [cHadReg_eval_eq_embed, QRegister.embedUnitary_val]
      exact vLinUnitary_comm_of_disj hmPay hmWB rCore rWB hCW rHeld18 hCH
        (QRegExt.disjointWires_symm hHW) _
    have hVW :=
      (vLinUnitary_intertwines_write hmPay hmWB rCore rHeld18 rWB hCH
      hCW hHW).symm
    have hH_wb : (Bell18TeleportCore.cHadReg rHeld18).eval.1 * P_wb =
        P_wb * (Bell18TeleportCore.cHadReg rHeld18).eval.1 := by
      rw [cHadReg_eval_eq_embed, QRegister.embedUnitary_val]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHeld18) rWB hHW _ 0
    have hCh_wb : P_ch0 * P_wb = P_wb * P_ch0 := by
      dsimp only [P_ch0, P_wb]
      rw [Matrix.mul_assoc,
          proj0_comm_of_disj rHeld18 rWB hHW,
          ← Matrix.mul_assoc,
          (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreAnchor) rWB hCAW _ 0,
          Matrix.mul_assoc]
    dsimp only [V] at hVH ⊢
    generalize (vLinUnitary hmPay hmWB rCore rWB hCW).1 = V0 at hVW hVH ⊢
    dsimp only [B_c, B_ei, Bell18TeleportCore.uBellSlot, P_base]
    rw [Submonoid.coe_mul, Submonoid.coe_mul, tcEmbed_uLensWrite_eq, tcEmbed_uLensWrite_eq]
    let W_c := ((rCore.concat rHeld18 hCH).embedUnitary (uLensWrite L_core)).1
    let W_ei := ((rDataEI.concat rHeld18 hDH_EI).embedUnitary (uLensWrite L_ei)).1
    let H := (Bell18TeleportCore.cHadReg rHeld18).eval.1
    exact sg_vbc_intertwine V0 W_c W_ei H P_ch0 P_wb hVW hVH hH_wb hCh_wb
  have hPt_VP : P_t0 * (V * P_base) = V * P_base := by
    apply matrix_ext_ket; intro β
    generalize hPt : P_t0 = Pt
    generalize hV : V = V0
    dsimp only [P_base, P_ch0, P_wb]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ket_basisOutcomeProjector_zero]
    by_cases hWB0 : ∀ j : Fin mWB, β (rWB j) = 0
    · rw [ite_eq_left hWB0, ← Matrix.mulVec_mulVec, ket_basisOutcomeProjector_zero]
      by_cases hH0 : ∀ j : Fin 18, β (rHeld18 j) = 0
      · rw [ite_eq_left hH0, embedMatrix_p_slot0_mulVec_ket rCore rAnchor18 hCA L_core β]
        by_cases hS0 : S_slot0Lens rCore L_core β
        · rw [ite_eq_left hS0, ← hV, vLinUnitary_mulVec_ket hmPay hmWB rCore rWB hCW β hWB0,
              ← hPt]
          dsimp only [P_t0]
          rw [p2d_proj_ket]
          obtain ⟨_, _, _, hTblEq⟩ :=
            fastLinState_extract_and_tbl hmPay hmWB rCore rAnchor18 rWB hCW hAW β hWB0
          have hS0_ei : S_slot0Lens rDataEI L_ei (fastLinState hmPay hmWB rCore rWB hCW β) :=
            hTblEq.trans hS0
          have hH0_lin : ∀ j : Fin 18,
              fastLinState hmPay hmWB rCore rWB hCW β (rHeld18 j) = 0 := fun j ↦ by
            rw [fastLinState_apply_of_disj hmPay hmWB rCore rWB hCW (rHeld18 j)
              (fun ⟨c, hc⟩ ↦ hCH.ne c j hc) (fun ⟨w, hw⟩ ↦ hHW.ne j w hw.symm)]
            exact hH0 j
          exact ite_eq_left ⟨⟨hS0_ei, hH0_lin⟩,
            (fastLinState_invTrees_and_sFnEI hmPay hmWB rCore rWB hCW β hWB0).1⟩
        · rw [ite_eq_right hS0, Matrix.mulVec_zero, Matrix.mulVec_zero]
      · rw [ite_eq_right hH0, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
    · rw [ite_eq_right hWB0, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hWrap := hoist_realizesOnProj_of_peb hPout_herm
    (dWrapFast68_realizes_gen hmPay hmWB v rCore rWB hCW hPout_herm hPt_herm hTailOut hTailU
      hTrees ?_ ?_)
  · have hMul := realizesOnProj_mul_right (B_c.1 * P_base) hWrap
    have hIdem : P_base * P_base = P_base := by
      have hCh_wb : P_ch0 * P_wb = P_wb * P_ch0 := by
        dsimp only [P_ch0, P_wb]
        rw [Matrix.mul_assoc,
            proj0_comm_of_disj rHeld18 rWB hHW,
            ← Matrix.mul_assoc,
            (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreAnchor) rWB hCAW _ 0,
            Matrix.mul_assoc]
      have hCh2 : P_ch0 * P_ch0 = P_ch0 := by
        have hId0 : P_slot0 L_core * P_slot0 L_core = P_slot0 L_core := by
          rw [P_slot0_eq_diagonal, Matrix.diagonal_mul_diagonal]
          apply congrArg Matrix.diagonal; funext z; split_ifs <;> simp
        dsimp only [P_ch0]
        rw [Matrix.mul_assoc _ _ P_ch0, ← Matrix.mul_assoc (rHeld18.basisOutcomeProjector 0),
            ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreAnchor) rHeld18 hCAH _
              0).symm,
            Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self,
            ← Matrix.mul_assoc, ← rCoreAnchor.embedMatrix_mul, hId0]
      exact sg_idem_pair P_ch0 P_wb hCh_wb.symm hCh2
        (QRegister.basisOutcomeProjector_mul_self _ _)
    have hProjSimp : P_out * (B_c.1 * P_base) = B_c.1 * P_base :=
      mon_proj_absorb B_c.1 P_base B_c.1ᴴ
        (congrArg Subtype.val (Unitary.star_mul_self B_c)) hIdem
    rw [hProjSimp] at hMul
    unfold dPostCoreBell18Fast
    exact hMul
  · dsimp only [P_trees, P_out]
    dsimp only [V] at hVBc hPt_VP ⊢
    generalize (vLinUnitary hmPay hmWB rCore rWB hCW).1 = V0 at hVBc hPt_VP ⊢
    exact mon_sub_trees B_ei.1 P_t0 B_ei.1ᴴ V0 B_c.1 P_base B_c.1ᴴ hVBc
      (congrArg Subtype.val (Unitary.star_mul_self B_ei)) hPt_VP
  · have hCh_wb : P_ch0 * P_wb = P_wb * P_ch0 := by
      dsimp only [P_ch0, P_wb]
      rw [Matrix.mul_assoc, proj0_comm_of_disj rHeld18 rWB hHW, ← Matrix.mul_assoc,
          (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreAnchor) rWB hCAW _ 0,
          Matrix.mul_assoc]
    have hSw : S_ei.1 * (V * P_wb) = V * (S_c.1 * P_wb) :=
      vLinUnitary_intertwines_swap hmPay hmWB rCore rAnchor18 rWB hCA hCW hAW
    dsimp only [U_out, P_out, P_base]
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
    dsimp only [V] at hVBc hSw ⊢
    generalize (vLinUnitary hmPay hmWB rCore rWB hCW).1 = V0 at hVBc hSw ⊢
    exact mon_int_trees S_ei.1 (star B_ei).1 B_ei.1 V0 B_c.1 S_c.1 (star B_c).1
      P_ch0 P_wb B_c.1ᴴ hVBc
      (congrArg Subtype.val (Unitary.star_mul_self B_ei))
      (congrArg Subtype.val (Unitary.star_mul_self B_c)) hCh_wb hSw
/-- Data-lifted `420 T`-wrapped `64 × 4` gated W-state Bell-18 post-pass (`≤ 1,292 T`, `0 TOFF`)
for `coinBarrelFastOnDataLens hmPay selCore` on `(rData, rAnchor18, rHeld18, rWB)`. -/
noncomputable def dPostBell18AnchorFast {Var : Type} {n mPayload kData mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister (fullSysCoreWires mPayload) kData)
    (rAnchor18 rHeld18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hDW : rData.DisjointWires rWB) (hAH : rAnchor18.DisjointWires rHeld18) :
    DynamicCircuit Var n :=
  dPostCoreBell18Fast hmPay hmWB v (rData.compose selCore) rAnchor18 rHeld18 rWB
    (hDW.compose_left selCore) hAH

private theorem dPostBell18AnchorFast_count_toff {Var : Type} {n mPayload kData mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister (fullSysCoreWires mPayload) kData)
    (rAnchor18 rHeld18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hDW : rData.DisjointWires rWB) (hAH : rAnchor18.DisjointWires rHeld18) :
    (dPostBell18AnchorFast hmPay hmWB v rData selCore rAnchor18 rHeld18 rWB hDW hAH).count TOFF =
      0 :=
  dPostCoreBell18Fast_count_toff hmPay hmWB v _ rAnchor18 rHeld18 rWB _ hAH

private theorem dPostBell18AnchorFast_count_t_le {Var : Type} {n mPayload kData mWB : ℕ}
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister (fullSysCoreWires mPayload) kData)
    (rAnchor18 rHeld18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hDW : rData.DisjointWires rWB) (hAH : rAnchor18.DisjointWires rHeld18) :
    (dPostBell18AnchorFast hmPay hmWB v rData selCore rAnchor18 rHeld18 rWB hDW hAH).count T ≤
      856 :=
  dPostCoreBell18Fast_count_t_le hmPay hmWB v _ rAnchor18 rHeld18 rWB _ hAH

private theorem dPostBell18AnchorFast_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload kData mWB : ℕ} [NeZero (2 ^ n)]
    (hmPay : 80 ≤ mPayload) (hmWB : 143 ≤ mWB) (v : Var)
    (rData : QRegister kData n) (selCore : QRegister (fullSysCoreWires mPayload) kData)
    (rAnchor18 rHeld18 : QRegister 18 n) (rWB : QRegister mWB n)
    (hDA : rData.DisjointWires rAnchor18) (hDH : rData.DisjointWires rHeld18)
    (hDW : rData.DisjointWires rWB) (hAH : rAnchor18.DisjointWires rHeld18)
    (hAW : rAnchor18.DisjointWires rWB) (hHW : rHeld18.DisjointWires rWB) :
    let L := coinBarrelFastOnDataLens hmPay selCore
    let rAct := rData.concat rAnchor18 hDA
    let B := Bell18TeleportCore.uBellSlot rData rHeld18 hDH (toSlotK18 L)
    HoistBorrow42ProjBridge.RealizesOnProj
      (B.1 * ((rAct.embedMatrix (P_slot0 L) * rHeld18.basisOutcomeProjector 0) *
        rWB.basisOutcomeProjector 0))
      (rAct.embedUnitary (uLensSwap L) * star B)
      (dPostBell18AnchorFast hmPay hmWB v rData selCore rAnchor18 rHeld18 rWB hDW hAH) := by
  intro L rAct B
  have hCore := dPostCoreBell18Fast_realizes hmPay hmWB v (rData.compose selCore)
    rAnchor18 rHeld18 rWB (hDA.compose_left selCore) (hDH.compose_left selCore)
    (hDW.compose_left selCore) hAH hAW hHW
  have hP : rAct.embedMatrix (P_slot0 L) =
      ((rData.compose selCore).concat rAnchor18 (hDA.compose_left selCore)).embedMatrix
        (P_slot0 (coinBarrelFastSlot18Lens hmPay)) := by
    dsimp only [L, coinBarrelFastOnDataLens, rAct]
    rw [← P_slot0_liftSlot18Lens, ← QRegister.embedMatrix_compose, concat_compose_selLiftAct]
  have hU : rAct.embedUnitary (uLensSwap L) =
      ((rData.compose selCore).concat rAnchor18 (hDA.compose_left selCore)).embedUnitary
        (uLensSwap (coinBarrelFastSlot18Lens hmPay)) := by
    dsimp only [L, coinBarrelFastOnDataLens, rAct]
    rw [← uLensSwap_liftSlot18Lens, ← QRegister.embedUnitary_compose, concat_compose_selLiftAct]
  have hB : B = Bell18TeleportCore.uBellSlot (rData.compose selCore) rHeld18
      (hDH.compose_left selCore) (toSlotK18 (coinBarrelFastSlot18Lens hmPay)) := by
    dsimp only [B, Bell18TeleportCore.uBellSlot, L, coinBarrelFastOnDataLens]
    apply congrArg (· * (Bell18TeleportCore.cHadReg rHeld18).eval)
    apply Subtype.ext
    rw [tcEmbed_uLensWrite_eq, tcEmbed_uLensWrite_eq]
    refine congrArg Subtype.val ?_
    rw [← uLensWrite_liftSlot18Lens, ← QRegister.embedUnitary_compose, concat_compose_selLiftAct]
  unfold dPostBell18AnchorFast
  rw [hP, hU, hB]
  exact hCore

set_option exponentiation.threshold 3950 in
private theorem dPostBell18AnchorFast_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWork n : ℕ} [NeZero (2 ^ n)]
    (hm143 : 143 ≤ mWork) (E_ext : Operator (2 ^ kFull80)) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 rHeld18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18) (hAH : rAct.DisjointWires rHeld18)
    (hAW : rAct.DisjointWires rWork) (hAnH : rAnchor18.DisjointWires rHeld18)
    (hAnW : rAnchor18.DisjointWires rWork) (hHW : rHeld18.DisjointWires rWork) :
    let L_anc := coinBarrelFastOnDataLens (le_refl 80) rCoreFull
    let B_act := Bell18TeleportCore.uBellSlot rAct rHeld18 hAH (toSlotK18 L_anc)
    HoistBorrow42ProjBridge.RealizesOnProj
      (B_act.1 * (E_anchor E_ext rAct rAnchor18 rWork hAA * rHeld18.basisOutcomeProjector 0))
      ((rAct.concat rAnchor18 hAA).embedUnitary (uLensSwap L_anc) * star B_act)
      (dPostBell18AnchorFast (le_refl 80) hm143 v rAct rCoreFull rAnchor18 rHeld18 rWork
        hAW hAnH) := by
  intro L_anc B_act
  let rDA := rAct.concat rAnchor18 hAA
  have hDAW : rDA.DisjointWires rWork := qreg_disjoint_concat_left hAW hAnW
  have hDAH : rDA.DisjointWires rHeld18 := qreg_disjoint_concat_left hAH hAnH
  have hBase := dPostBell18AnchorFast_realizes (le_refl 80) hm143 v rAct rCoreFull
    rAnchor18 rHeld18 rWork hAA hAH hAW hAnH hAnW hHW
  have hMul := realizesOnProj_mul_right (rDA.embedMatrix (E_anchorLoc E_ext)) hBase
  have hCW : rWork.basisOutcomeProjector 0 * rDA.embedMatrix (E_anchorLoc E_ext) =
      rDA.embedMatrix (E_anchorLoc E_ext) * rWork.basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rDA) rWork hDAW _ 0).symm
  have hCH : rHeld18.basisOutcomeProjector 0 * rDA.embedMatrix (E_anchorLoc E_ext) =
      rDA.embedMatrix (E_anchorLoc E_ext) * rHeld18.basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rDA) rHeld18 hDAH _ 0).symm
  have hHW0 : rHeld18.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * rHeld18.basisOutcomeProjector 0 :=
    proj0_comm_of_disj rHeld18 rWork hHW
  have hEq : (B_act.1 * ((rDA.embedMatrix (P_slot0 L_anc) * rHeld18.basisOutcomeProjector 0) *
        rWork.basisOutcomeProjector 0)) * rDA.embedMatrix (E_anchorLoc E_ext) =
      B_act.1 * (E_anchor E_ext rAct rAnchor18 rWork hAA * rHeld18.basisOutcomeProjector 0) := by
    have h1 := sg_anchor_ext B_act.1 (rDA.embedMatrix (P_slot0 L_anc))
      (rHeld18.basisOutcomeProjector 0) (rWork.basisOutcomeProjector 0)
      (rDA.embedMatrix (E_anchorLoc E_ext)) hCW hCH hHW0
    have hLAnc : L_anc = L_anchor := by unfold L_anchor; rfl
    rw [h1, ← rDA.embedMatrix_mul, hLAnc, P_slot0_mul_E_anchorLoc]
    unfold E_anchor; rfl
  rwa [hEq] at hMul

end Part3B_PostBell18Fast

section Part3C_Bell18FusedBundle

set_option backward.isDefEq.respectTransparency true

open _root_.QuantumComputation.Specs.StoppingPowerSolution.DyadicQft64
  (dyadicTurn dyadicTurn_add sList sDagList count_sList_toff count_sList_t
   count_sDagList_toff count_sDagList_t)
open scoped Circuit.Notation
open HoistBorrow42ProjBridge (RealizesOnProj)
open Barrel3PassSelectStitch (hm6_80)
open CoinDispatchedBarrel288 (uBarrelFast)
open FullSysCatSegmentBridge (fullSysCoreWires coreElecCosetB1Block)
open FusedPreDiagFromTwist288 (uPreDiagCliffordCore)
open InterWalkRSum42Hoist (rSegFull)
open Pass1BarrelIdxLoad273 (qreg_disjoint_concat_left)
open HeldStreamFoldedPass123Bridge
  (E_rawCtrl3Ext E_rawSegExt)
open LocalHeldStreamFoldedPass123Bridge
  (pRawCtrl3ExtOn pRawHoistExtOn)
open StageAConjHAndStreamBridge (uStageARawFull)
open BarrelPass2AndHeld3PassSelectStitch
  (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt
   uPass1InnerSeg_and_uPass3InnerSeg_comm_rawStream_ctrl3_idle12
   uSingleBarrelFolded6Full uPass1InnerSeg uPass3InnerSeg)
open SingleBarrel8StepClean
  (commutesWithReg_rPGIdleOrig11_of_12)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (E_anchorLoc E_anchor P_slot0_mul_E_anchorLoc uSlot0MeasSwap uSlot0MeasSwap_mul_self
   uBarrelFastAct_mul_self uBarrelFastAct_eq_embedData_rCoreFull
   uPreDiagCliffordAnchorLoc uPreDiagCliffordAnchorInvLoc
   cPreDiagCliffordAnchor_eval cPreDiagCliffordAnchorInv_eval
   uAnchorFrame_of_uBarrelFast_conj_eq
   uBarrelFast_conj_uPreDiagCliffordCore uBarrelFast_conj_uPreDiagCliffordCore_inv
   uLensSwap_conj_uPreDiagCliffordCore_eq_diagonal_gen
   uLensSwap_conj_uPreDiagCliffordCore_inv_eq_diagonal_gen
   preDiagExp_updSlot_of_tbl_zero_gen extractPair_lensSwapEquiv
   embedUnitary_uSDagK_eq_diagonal embedUnitary_uSDagK_inv_eq_diagonal
   uPreDiagCliffordCore_eq_diagonal_gen uPreDiagCliffordCore_inv_eq_diagonal_gen
   uSDag18 uSDagK cSK_eval cSDagK_eval
   uPreDiagCliffordCore_comm_E_rawCtrl3Ext_and_E_rawSegExt
   uWrapPreDiagCliffordFull realizesOnProj_congr_unitary
   uAnchorFrame_mul uAnchorFrame_intertwines_E_anchorLoc embedIntertwineOp
   realizesOnProj_mul_right embedMatrix_diagonal_part2)
open BoothOpt_FastAnchorOuterAndStageBShave
  (FoldedPass123CircuitSpec_mWork rAnchor18OfMWork rWorkRemOfMWork
   rAnchor18OfMWork_disj_rWorkRemOfMWork rAnchor18OfMWork_proj0_mul_rWorkRemOfMWork_proj0
   dPreAnchor64x4Fast dPreAnchor64x4Fast_count_toff dPreAnchor64x4Fast_count_t_le
   dPreAnchor64x4Fast_realizes)
open ChiralDStageABridge (rawABorrow48054)
open LocalBoothOpt_Anchor218CachedTrueSwapOuter
  (E_anchor_eq)
open LocalStageBFastInnerPartnerShift
  (uAnchorTrueSwapFull uBarrelFastOnActFull)
open LocalStageBPartnerTrueSwapStream218Closure
  (uStageBFull uStageBFull_mul_E_rawStream42_eq commutesWithReg_rCtrl3InSeg_uStageBSeg
   commutesWithReg_rPGIdleOrig_uStageBSeg)
open P1_OpenAnchorAdd0TwoLoad
  (uJunctionRawFull uJunctionAncFull18 uAnchorFrame_uJunctionRawFull_inv_eq
   uAnchorFrame_one mul_intertwine_same uWrapPreDiagCliffordFull_mul
   uSingleBarrelFolded6Full_mul_one)
open StageBOneWireBridge
  (kOneWire_le_18 stageBOneWireKBoothOptAnchorT stageBOneWireBoothOptAnchorT)
open Bell18StageABridge
  (eqRegFn pEqReg E_bell18Gen uAnchorFrame_step_E_bell18Gen StageABell18Witness)
open Bell18Seq6Bridge
  (dPreBellWrap dPreBellWrap_counts dWrapPreDiagBell dWrapPreDiagBell_counts
   tOuterAnchorBell18PairFused seq6Bell18_realizesOnProj_fused)

private abbrev sData80 := StageADeconstrCore.selDataInAct kFull80
private abbrev sMeas80 := StageADeconstrCore.selMeasInAct kFull80

private theorem ccData {n kData : ℕ}
    (rD : QRegister kData n) (rM : QRegister 18 n) (hDM : rD.DisjointWires rM) :
    (rD.concat rM hDM).compose (StageADeconstrCore.selDataInAct kData) = rD :=
  StageADeconstrCore.concat_compose_selDataInAct rD rM hDM

private theorem ccMeas {n kData : ℕ}
    (rD : QRegister kData n) (rM : QRegister 18 n) (hDM : rD.DisjointWires rM) :
    (rD.concat rM hDM).compose (StageADeconstrCore.selMeasInAct kData) = rM :=
  StageADeconstrCore.concat_compose_selMeasInAct rD rM hDM

private theorem proj0_comm_3c {k₁ k₂ n : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (h : r₁.DisjointWires r₂) :
    r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 * r₁.basisOutcomeProjector 0 := by
  conv_lhs => enter [1]; unfold QRegister.basisOutcomeProjector
  conv_rhs => enter [2]; unfold QRegister.basisOutcomeProjector
  exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint r₁) r₂ h _ 0

private theorem xorK18_zero_left (x : Fin (2 ^ 18)) :
    Bell18TeleportCore.xorK 0 x = x :=
  Bell18TeleportCore.xorK_zero_left x

private theorem xorK18_cancel_right (a b : Fin (2 ^ 18)) :
    Bell18TeleportCore.xorK (Bell18TeleportCore.xorK a b) a = b := by
  rw [Bell18TeleportCore.xorK_comm a b, Bell18TeleportCore.xorK_cancel_right]

private noncomputable def uBellInit {n : ℕ}
    (rAnc rHeld : QRegister 18 n) (hAnH : rAnc.DisjointWires rHeld) : Unitary (2 ^ n) :=
  (rHeld.concat rAnc (QRegExt.disjointWires_symm hAnH)).embedUnitary (Bell18TeleportCore.uLensLoad
    idSlotK18) *
    (Bell18TeleportCore.cHadReg rHeld).eval

private noncomputable def G_bell18Init {n : ℕ}
    (rAnc rHeld : QRegister 18 n) (hAnH : rAnc.DisjointWires rHeld) : Operator (2 ^ n) :=
  (uBellInit rAnc rHeld hAnH).1 *
    (rAnc.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0)

private theorem pEqReg_mul_G_bell18Init {n : ℕ}
    (rAnc rHeld : QRegister 18 n) (hAnH : rAnc.DisjointWires rHeld) :
    pEqReg rAnc rHeld * G_bell18Init rAnc rHeld hAnH = G_bell18Init rAnc rHeld hAnH := by
  let L_ha := (rHeld.concat rAnc (QRegExt.disjointWires_symm hAnH)).embedUnitary
    (Bell18TeleportCore.uLensLoad idSlotK18)
  have hLoad0 : pEqReg rAnc rHeld * (L_ha.1 * rAnc.basisOutcomeProjector 0) =
      L_ha.1 * rAnc.basisOutcomeProjector 0 := by
    apply matrix_ext_ket; intro β
    rw [ket_eq_single_loc β, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mulVec_single]
    set g := (basisBitsEquiv n).symm β
    by_cases ha0 : rAnc.extractIndex g = 0
    · rw [ite_eq_left ha0, one_mul]
      dsimp only [L_ha]
      rw [Bell18TeleportCore.embedUnitary_uLensLoad_mulVec_single, pEqReg,
          Matrix.diagonal_mulVec_single]
      dsimp only [idSlotK18]
      rw [ha0, xorK18_zero_left]
      let g' := rAnc.replaceIndex g (rHeld.extractIndex g)
      have hEqBits : ∀ i : Fin 18, basisBits n g' (rAnc i) = basisBits n g' (rHeld i) := fun i ↦ by
        dsimp only [g']
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex,
            QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ hAnH.ne j i hj)]
      have hFn : eqRegFn rAnc rHeld g' = 1 := ite_eq_left hEqBits
      rw [hFn, one_mul]
    · simp only [ite_eq_right ha0, zero_mul, Pi.single_zero, Matrix.mulVec_zero]
  have hCH : (Bell18TeleportCore.cHadReg rHeld).eval.1 * rAnc.basisOutcomeProjector 0 =
      rAnc.basisOutcomeProjector 0 * (Bell18TeleportCore.cHadReg rHeld).eval.1 :=
    Bell18TeleportCore.cHadReg_comm_basisOutcomeProjector rHeld rAnc (QRegExt.disjointWires_symm
      hAnH) 0
  dsimp only [G_bell18Init, uBellInit]
  calc pEqReg rAnc rHeld * ((L_ha * (Bell18TeleportCore.cHadReg rHeld).eval).1 *
          (rAnc.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0))
      = pEqReg rAnc rHeld * (L_ha.1 *
          ((Bell18TeleportCore.cHadReg rHeld).eval.1 * rAnc.basisOutcomeProjector 0) *
          rHeld.basisOutcomeProjector 0) := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (pEqReg rAnc rHeld * (L_ha.1 * rAnc.basisOutcomeProjector 0)) *
          ((Bell18TeleportCore.cHadReg rHeld).eval.1 * rHeld.basisOutcomeProjector 0) := by
          rw [hCH]; simp only [Matrix.mul_assoc]
    _ = (L_ha * (Bell18TeleportCore.cHadReg rHeld).eval).1 *
          (rAnc.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0) := by
          rw [hLoad0]
          calc (L_ha.1 * rAnc.basisOutcomeProjector 0) *
                ((Bell18TeleportCore.cHadReg rHeld).eval.1 * rHeld.basisOutcomeProjector 0)
              = L_ha.1 * (rAnc.basisOutcomeProjector 0 *
                  (Bell18TeleportCore.cHadReg rHeld).eval.1) *
                  rHeld.basisOutcomeProjector 0 := by simp only [Matrix.mul_assoc]
            _ = (L_ha * (Bell18TeleportCore.cHadReg rHeld).eval).1 *
                  (rAnc.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0) := by
                  rw [← hCH]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]

private theorem embedMatrix_comm_uBellInit {k n : ℕ}
    (rM : QRegister k n) (rAnc rHeld : QRegister 18 n)
    (hMA : rM.DisjointWires rAnc) (hMH : rM.DisjointWires rHeld)
    (hAnH : rAnc.DisjointWires rHeld) (V : Operator (2 ^ k)) :
    rM.embedMatrix V * (uBellInit rAnc rHeld hAnH).1 =
      (uBellInit rAnc rHeld hAnH).1 * rM.embedMatrix V := by
  have hDisjHA : rM.DisjointWires (rHeld.concat rAnc (QRegExt.disjointWires_symm hAnH)) :=
    (QRegExt.disjointWires_symm (qreg_disjoint_concat_left (QRegExt.disjointWires_symm hMH)
      (QRegExt.disjointWires_symm hMA)))
  have h1 : rM.embedMatrix V *
      ((rHeld.concat rAnc (QRegExt.disjointWires_symm hAnH)).embedUnitary
        (Bell18TeleportCore.uLensLoad idSlotK18)).1 =
      ((rHeld.concat rAnc (QRegExt.disjointWires_symm hAnH)).embedUnitary
        (Bell18TeleportCore.uLensLoad idSlotK18)).1 * rM.embedMatrix V := by
    rw [QRegister.embedUnitary_val]
    exact rM.embedMatrix_comm_of_disjoint _ hDisjHA V _
  have h2 := (Bell18TeleportCore.cHadReg_comm_embedMatrix_of_disjoint
    rHeld rM (QRegExt.disjointWires_symm hMH) V).symm
  dsimp only [uBellInit]
  rw [Submonoid.coe_mul, ← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2, ← Matrix.mul_assoc]

private theorem embedMatrix_comm_G_bell18Init {k n : ℕ}
    (rM : QRegister k n) (rAnc rHeld : QRegister 18 n)
    (hMA : rM.DisjointWires rAnc) (hMH : rM.DisjointWires rHeld)
    (hAnH : rAnc.DisjointWires rHeld) (V : Operator (2 ^ k)) :
    rM.embedMatrix V * G_bell18Init rAnc rHeld hAnH =
      G_bell18Init rAnc rHeld hAnH * rM.embedMatrix V := by
  have hU := embedMatrix_comm_uBellInit rM rAnc rHeld hMA hMH hAnH V
  have hA := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rM) rAnc hMA V 0
  have hH := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rM) rHeld hMH V 0
  dsimp only [G_bell18Init]
  calc rM.embedMatrix V *
          ((uBellInit rAnc rHeld hAnH).1 *
            (rAnc.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0))
      = (rM.embedMatrix V * (uBellInit rAnc rHeld hAnH).1) *
          (rAnc.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0) := by
          simp only [Matrix.mul_assoc]
    _ = (uBellInit rAnc rHeld hAnH).1 *
          ((rM.embedMatrix V * rAnc.basisOutcomeProjector 0) * rHeld.basisOutcomeProjector 0) := by
          rw [hU]; simp only [Matrix.mul_assoc]
    _ = (uBellInit rAnc rHeld hAnH).1 *
          (rAnc.basisOutcomeProjector 0 * (rM.embedMatrix V * rHeld.basisOutcomeProjector 0)) := by
          rw [hA]; simp only [Matrix.mul_assoc]
    _ = ((uBellInit rAnc rHeld hAnH).1 *
          (rAnc.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0)) * rM.embedMatrix V := by
          rw [hH]; simp only [Matrix.mul_assoc]

private theorem semigrp_bell_reassoc {R : Type} [Semigroup R]
    (b s u m1 m2 pA pW pH : R)
    (hBS : b * s = s * u) (hM1 : u * m1 = m1 * u)
    (hM2 : u * m2 = m2 * u) (hPW : u * pW = pW * u)
    (hAW : pA * pW = pW * pA) :
    b * ((s * m1 * (m2 * pA) * pW) * pH) =
      (s * m1) * (m2 * pW * (u * (pA * pH))) := by
  have h1 : b * ((s * m1 * (m2 * pA) * pW) * pH) =
      s * (u * (m1 * (m2 * ((pA * pW) * pH)))) := by
    simp only [← mul_assoc]; rw [hBS]
  rw [h1, hAW]
  simp only [← mul_assoc]
  have h2 : s * u * m1 = s * m1 * u := by rw [mul_assoc s u m1, hM1, ← mul_assoc]
  have h3 : s * m1 * u * m2 = s * m1 * m2 * u := by rw [mul_assoc (s * m1) u m2, hM2, ← mul_assoc]
  have h4 : s * m1 * m2 * u * pW = s * m1 * m2 * pW * u := by
    rw [mul_assoc (s * m1 * m2) u pW, hPW, ← mul_assoc]
  rw [h2, h3, h4]

private theorem semigrp_unitAnc0 {R : Type} [Semigroup R]
    (X Y H P : R) (hHP : H * P = P * H) (hXY : X * P = Y * P) :
    (X * H) * P = (Y * H) * P := by
  rw [mul_assoc, hHP, ← mul_assoc, hXY, mul_assoc, ← hHP, ← mul_assoc]

private theorem semigrp_pinEq {R : Type} [Semigroup R]
    (pW e pA pH : R) (hWE : pW * e = e * pW) (hAE : pA * e = e * pA)
    (hWA : pW * pA = pA * pW) (hWH : pW * pH = pH * pW) :
    pW * (e * (pA * pH)) = pA * (e * (pH * pW)) := by
  simp only [← mul_assoc]
  rw [hWE, mul_assoc e pW pA, hWA, ← mul_assoc e pA pW, ← hAE,
      mul_assoc (pA * e) pW pH, hWH]
  simp only [mul_assoc]

private theorem uBellSlot_mul_E_anchor_eq_E_bell18Gen {mW n : ℕ}
    (E_ext : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAH : rAct.DisjointWires rHeld)
    (_hAW : rAct.DisjointWires rW) (hAnH : rAnc.DisjointWires rHeld)
    (hAnW : rAnc.DisjointWires rW) (hHW : rHeld.DisjointWires rW) :
    let B_anc := Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)
    B_anc.1 * (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0) =
      E_bell18Gen E_ext rAct rAnc rW hAA (G_bell18Init rAnc rHeld hAnH) := by
  intro B_anc
  let rDA := rAct.concat rAnc hAA
  let S := rDA.embedUnitary (Bell18TeleportCore.uLensSwap (toSlotK18 L_anchor))
  let W_h := (rAct.concat rHeld hAH).embedUnitary
    (Bell18TeleportCore.uLensWrite (toSlotK18 L_anchor))
  let L_ha := (rHeld.concat rAnc (QRegExt.disjointWires_symm hAnH)).embedUnitary
    (Bell18TeleportCore.uLensLoad idSlotK18)
  have hSS : S * S = 1 := by
    dsimp only [S]
    rw [tcEmbed_uLensSwap_eq, ← QRegister.embedUnitary_mul]
    change rDA.embedUnitary (uAnchorLensSwap * uAnchorLensSwap) = 1
    rw [uAnchorLensSwap_mul_self, QRegister.embedUnitary_one]
  have hWS : W_h * S = S * L_ha := by
    have hConj := uLensSwap_conj_uLensWrite_eq_loadHeldAnc rAct rAnc rHeld
      hAA hAH hAnH (toSlotK18 L_anchor)
    calc W_h * S
        = (S * S) * (W_h * S) := by rw [hSS, one_mul]
      _ = S * (S * W_h * S) := by simp only [mul_assoc]
      _ = S * L_ha := by rw [hConj]
  have hDAH : rDA.DisjointWires rHeld := disjointWires_concat_left hAA hAH hAnH
  have hHS : (Bell18TeleportCore.cHadReg rHeld).eval * S =
      S * (Bell18TeleportCore.cHadReg rHeld).eval :=
    Bell18TeleportCore.cHadReg_comm_embedUnitary_of_disjoint rHeld rDA (QRegExt.disjointWires_symm
      hDAH) _
  have hBS : B_anc * S = S * uBellInit rAnc rHeld hAnH := by
    dsimp only [B_anc, Bell18TeleportCore.uBellSlot, uBellInit]
    calc (W_h * (Bell18TeleportCore.cHadReg rHeld).eval) * S
        = W_h * ((Bell18TeleportCore.cHadReg rHeld).eval * S) := by simp only [mul_assoc]
      _ = (W_h * S) * (Bell18TeleportCore.cHadReg rHeld).eval := by
          rw [hHS]; simp only [mul_assoc]
      _ = S * (L_ha * (Bell18TeleportCore.cHadReg rHeld).eval) := by
          rw [hWS]; simp only [mul_assoc]
  let uBar := rCoreFull.embedUnitary (uBarrelFast (le_refl 80))
  have hFbs : rDA.embedMatrix (uBarrelFastAct * uSlot0MeasSwap).1 =
      S.1 * rAct.embedMatrix uBar.1 := by
    rw [uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct,
        uBarrelFastAct_eq_embedData_rCoreFull, Submonoid.coe_mul, rDA.embedMatrix_mul,
        QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, ccData]
    have hS : rDA.embedMatrix uAnchorLensSwap.1 = S.1 := by
      dsimp only [S, uAnchorLensSwap]
      rw [tcEmbed_uLensSwap_eq, QRegister.embedUnitary_val]
    rw [hS, QRegister.embedUnitary_val]
  have hUBarComm := (embedMatrix_comm_uBellInit rAct rAnc rHeld hAA hAH hAnH uBar.1).symm
  have hUExtComm := (embedMatrix_comm_uBellInit rAct rAnc rHeld hAA hAH hAnH E_ext).symm
  have hDisjHAW : (rHeld.concat rAnc (QRegExt.disjointWires_symm hAnH)).DisjointWires rW :=
    qreg_disjoint_concat_left hHW hAnW
  have hUWComm : (uBellInit rAnc rHeld hAnH).1 * rW.basisOutcomeProjector 0 =
      rW.basisOutcomeProjector 0 * (uBellInit rAnc rHeld hAnH).1 := by
    dsimp only [uBellInit]
    rw [Submonoid.coe_mul, Matrix.mul_assoc,
        Bell18TeleportCore.cHadReg_comm_basisOutcomeProjector rHeld rW hHW 0,
        ← Matrix.mul_assoc, QRegister.embedUnitary_val,
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rHeld.concat rAnc
          (QRegExt.disjointWires_symm hAnH)))
          rW hDisjHAW _ 0, Matrix.mul_assoc]
  have hAW0 := proj0_comm_3c rAnc rW hAnW
  have hEqAnc := E_anchor_eq E_ext rAct rAnc rW hAA
  unfold BoothOpt_Anchor218CachedTrueSwapOuter.E_anchor at hEqAnc ⊢
  rw [hEqAnc]
  unfold E_bell18Gen G_bell18Init
  rw [hFbs]
  have hBSv : B_anc.1 * S.1 = S.1 * (uBellInit rAnc rHeld hAnH).1 :=
    congrArg Subtype.val hBS
  exact semigrp_bell_reassoc _ _ _ _ _ _ _ _ hBSv hUBarComm hUExtComm hUWComm hAW0

/-- `+0 T`, `0 TOFF` Bell-18 Site-2 pre-swap (`c1`, `≤ 16,404 T`) wrapping `dPreAnchor64x4Fast`. -/
noncomputable def dPreBell18AnchorFast {Var : Type} {mW n : ℕ}
    (hm143 : 143 ≤ mW) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAW : rAct.DisjointWires rW)
    (hAnH : rAnc.DisjointWires rHeld) (hAnW : rAnc.DisjointWires rW) : DynamicCircuit Var n :=
  dPreBellWrap
    (Bell18TeleportCore.cBellPrep rAnc rHeld hAnH)
    (Bell18TeleportCore.cCnotReg rHeld rAnc (QRegExt.disjointWires_symm hAnH))
    (dPreAnchor64x4Fast (le_refl 80) hm143 v rAct rCoreFull rAnc rW hAA hAW hAnW)

private theorem dPreBell18AnchorFast_counts {Var : Type} {mW n : ℕ}
    (hm143 : 143 ≤ mW) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAW : rAct.DisjointWires rW)
    (hAnH : rAnc.DisjointWires rHeld) (hAnW : rAnc.DisjointWires rW) :
    (dPreBell18AnchorFast hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW).count TOFF = 0 ∧
      (dPreBell18AnchorFast hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW).count T ≤ 16404 :=
  dPreBellWrap_counts
    (Bell18TeleportCore.cBellPrep_count_toff rAnc rHeld hAnH)
    (Bell18TeleportCore.cCnotReg_count_toff rHeld rAnc (QRegExt.disjointWires_symm hAnH))
    (dPreAnchor64x4Fast_count_toff (le_refl 80) hm143 v rAct rCoreFull rAnc rW hAA hAW hAnW)
    (Bell18TeleportCore.cBellPrep_count_t rAnc rHeld hAnH)
    (Bell18TeleportCore.cCnotReg_count_t rHeld rAnc (QRegExt.disjointWires_symm hAnH))
    (dPreAnchor64x4Fast_count_t_le (le_refl 80) hm143 v rAct rCoreFull rAnc rW hAA hAW hAnW)

private theorem dPreBell18AnchorFast_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ} [NeZero (2 ^ n)]
    (hm143 : 143 ≤ mW) (E_ext : Operator (2 ^ kFull80)) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAH : rAct.DisjointWires rHeld)
    (hAW : rAct.DisjointWires rW) (hAnH : rAnc.DisjointWires rHeld)
    (hAnW : rAnc.DisjointWires rW) (hHW : rHeld.DisjointWires rW) :
    let B_anc := Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)
    let S_anc := (rAct.concat rAnc hAA).embedUnitary uAnchorLensSwap
    RealizesOnProj
      (rAct.embedMatrix E_ext *
        (rAnc.basisOutcomeProjector 0 *
          (rHeld.basisOutcomeProjector 0 * rW.basisOutcomeProjector 0)))
      (B_anc * S_anc)
      (dPreBell18AnchorFast hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW) := by
  intro B_anc S_anc
  let rDA := rAct.concat rAnc hAA
  let cPrep := Bell18TeleportCore.cBellPrep rAnc rHeld hAnH
  let cCnot := Bell18TeleportCore.cCnotReg rHeld rAnc (QRegExt.disjointWires_symm hAnH)
  let U_wl := rDA.embedUnitary (uLensWrite L_anchor * uLensLoad L_anchor)
  let P_rest := rAct.embedMatrix E_ext *
    (rAnc.basisOutcomeProjector 0 * rHeld.basisOutcomeProjector 0)
  let P_in := rW.basisOutcomeProjector 0 * P_rest
  have hClean := dPreAnchor64x4Fast_realizes (le_refl 80) hm143 v rAct rCoreFull rAnc rW
    hAA hAW hAnW
  have h1 : Bell18Seq6Bridge.RealizesOnProj (Var := Var) P_in cPrep.eval (.circuit cPrep) :=
    Bell18Seq6Bridge.RealizesOnProj.of_circuit P_in cPrep
  have h2 : Bell18Seq6Bridge.RealizesOnProj (Var := Var)
      (rW.basisOutcomeProjector 0 * (cPrep.eval.1 * P_rest)) U_wl
      (dPreAnchor64x4Fast (le_refl 80) hm143 v rAct rCoreFull rAnc rW hAA hAW hAnW) :=
    Bell18Seq6Bridge.RealizesOnProj.of_cleanWorkspace_proj (cPrep.eval.1 * P_rest) hClean
  have h3 : Bell18Seq6Bridge.RealizesOnProj (Var := Var)
      (U_wl.1 * (rW.basisOutcomeProjector 0 * (cPrep.eval.1 * P_rest))) cCnot.eval
      (.circuit cCnot) :=
    Bell18Seq6Bridge.RealizesOnProj.of_circuit _ cCnot
  have hPrepW : cPrep.eval.1 * rW.basisOutcomeProjector 0 =
      rW.basisOutcomeProjector 0 * cPrep.eval.1 := by
    dsimp only [cPrep, Bell18TeleportCore.cBellPrep]
    rw [Circuit.eval_seq, Submonoid.coe_mul]
    have hH := Bell18TeleportCore.cHadReg_comm_basisOutcomeProjector rHeld rW hHW 0
    have hC : cCnot.eval.1 * rW.basisOutcomeProjector 0 =
        rW.basisOutcomeProjector 0 * cCnot.eval.1 := by
      have hEqC : cCnot.eval = (rHeld.concat rAnc (QRegExt.disjointWires_symm hAnH)).embedUnitary
          (Bell18TeleportCore.uLensLoad idSlotK18) := by
        apply Subtype.ext; apply matrix_ext_ket; intro β
        rw [ket_eq_single_loc β, Bell18TeleportCore.cCnotReg_mulVec_single,
            Bell18TeleportCore.embedUnitary_uLensLoad_mulVec_single]
        rfl
      rw [hEqC, QRegister.embedUnitary_val]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rHeld.concat rAnc
        (QRegExt.disjointWires_symm hAnH)))
        rW (qreg_disjoint_concat_left hHW hAnW) _ 0
    rw [Matrix.mul_assoc, hH, ← Matrix.mul_assoc, hC, Matrix.mul_assoc]
  have hI1 : cPrep.eval.1 * P_in = (rW.basisOutcomeProjector 0 * (cPrep.eval.1 * P_rest)) * 1 := by
    dsimp only [P_in]
    rw [Matrix.mul_one, ← Matrix.mul_assoc, hPrepW, Matrix.mul_assoc]
  have hI2 : U_wl.1 * (rW.basisOutcomeProjector 0 * (cPrep.eval.1 * P_rest)) =
      (U_wl.1 * (rW.basisOutcomeProjector 0 * (cPrep.eval.1 * P_rest))) * 1 := by
    rw [Matrix.mul_one]
  have hSeq0 : Bell18Seq6Bridge.RealizesOnProj P_in ((cCnot.eval * U_wl) * cPrep.eval)
      (dPreBell18AnchorFast hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW) :=
    h1.seq_intertwine hI1 (h2.seq_intertwine hI2 h3)
  have hSeq : RealizesOnProj P_in (cCnot.eval * (U_wl * cPrep.eval))
      (dPreBell18AnchorFast hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW) := by
    unfold RealizesOnProj; unfold Bell18Seq6Bridge.RealizesOnProj at hSeq0
    rw [← mul_assoc]; exact hSeq0
  have hPermEq : (cCnot.eval * (U_wl * cCnot.eval)).1 * rAnc.basisOutcomeProjector 0 =
      ((rAct.concat rHeld hAH).embedUnitary
        (Bell18TeleportCore.uLensWrite (toSlotK18 L_anchor)) * S_anc).1 *
        rAnc.basisOutcomeProjector 0 := by
    have hUwl : U_wl = rDA.embedUnitary (Bell18TeleportCore.uLensWrite (toSlotK18 L_anchor)) *
        rDA.embedUnitary (Bell18TeleportCore.uLensLoad (toSlotK18 L_anchor)) := by
      dsimp only [U_wl]
      rw [← tcULensLoad_mul_write_eq, QRegister.embedUnitary_mul]
    have hSanc : S_anc = rDA.embedUnitary
        (Bell18TeleportCore.uLensSwap (toSlotK18 L_anchor)) := by
      dsimp only [S_anc, uAnchorLensSwap]; rw [tcEmbed_uLensSwap_eq]
    rw [hUwl, hSanc]
    apply matrix_ext_ket; intro β
    rw [ket_eq_single_loc β]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mulVec_single]
    set g := (basisBitsEquiv n).symm β
    by_cases ha0 : rAnc.extractIndex g = 0
    · rw [ite_eq_left ha0, one_mul]
      rw [Bell18TeleportCore.cCnotReg_mulVec_single,
          Bell18TeleportCore.embedUnitary_uLensLoad_mulVec_single,
          Bell18TeleportCore.embedUnitary_uLensWrite_mulVec_single,
          Bell18TeleportCore.cCnotReg_mulVec_single,
          Bell18TeleportCore.embedUnitary_uLensSwap_mulVec_single,
          Bell18TeleportCore.embedUnitary_uLensWrite_mulVec_single]
      refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
      dsimp only [toSlotK18]
      let d := rAct.extractIndex g
      let z := rHeld.extractIndex g
      have ha_g : rAnc.extractIndex g = 0 := ha0
      rw [ha_g, xorK18_zero_left]
      let g1 := rAnc.replaceIndex g z
      have hD1 : rAct.extractIndex g1 = d :=
        QRegister.extractIndex_replaceIndex_of_disjoint rAct rAnc hAA g z
      have hA1 : rAnc.extractIndex g1 = z := QRegister.extractIndex_replaceIndex rAnc g z
      change rAnc.replaceIndex _ _ = _
      dsimp only [g1] at hD1 hA1
      rw [hD1, hA1]
      set m1 := Bell18TeleportCore.xorK z (L_anchor.tbl d)
      rw [QRegister.replaceIndex_replaceIndex rAnc g (rHeld.extractIndex g)]
      have hD2 : rAct.extractIndex (rAnc.replaceIndex g m1) = d :=
        QRegister.extractIndex_replaceIndex_of_disjoint rAct rAnc hAA g m1
      have hA2 : rAnc.extractIndex (rAnc.replaceIndex g m1) = m1 :=
        QRegister.extractIndex_replaceIndex rAnc g m1
      rw [hD2, hA2]
      have hValL : Bell18TeleportCore.xorK (L_anchor.tbl d) m1 = z := by
        dsimp only [m1]
        rw [Bell18TeleportCore.xorK_comm (L_anchor.tbl d),
            Bell18TeleportCore.xorK_cancel_right]
      rw [hValL]
      let g3 := rAct.replaceIndex (rAnc.replaceIndex g m1) (L_anchor.updSlot d z)
      have hA3 : rAnc.extractIndex g3 = m1 := by
        dsimp only [g3]
        rw [QRegister.extractIndex_replaceIndex_of_disjoint rAnc rAct (QRegExt.disjointWires_symm
          hAA), hA2]
      have hH3 : rHeld.extractIndex g3 = z := by
        dsimp only [g3]
        rw [QRegister.extractIndex_replaceIndex_of_disjoint rHeld rAct (QRegExt.disjointWires_symm
          hAH),
            QRegister.extractIndex_replaceIndex_of_disjoint rHeld rAnc (QRegExt.disjointWires_symm
              hAnH)]
      dsimp only [g3] at hH3
      rw [hA3, hH3]; dsimp only [m1]; rw [xorK18_cancel_right]
      rw [QRegister.replaceIndex_comm_of_disjoint rAct rAnc hAA,
          QRegister.replaceIndex_replaceIndex]
      let r1 := rAnc.replaceIndex (rAct.replaceIndex g (L_anchor.updSlot d 0)) (L_anchor.tbl d)
      have hDr1 : rAct.extractIndex r1 = L_anchor.updSlot d 0 := by
        dsimp only [r1]
        rw [QRegister.extractIndex_replaceIndex_of_disjoint rAct rAnc hAA,
            QRegister.extractIndex_replaceIndex]
      have hHr1 : rHeld.extractIndex r1 = z := by
        dsimp only [r1]
        rw [QRegister.extractIndex_replaceIndex_of_disjoint rHeld rAnc (QRegExt.disjointWires_symm
          hAnH),
            QRegister.extractIndex_replaceIndex_of_disjoint rHeld rAct (QRegExt.disjointWires_symm
              hAH)]
      dsimp only [r1] at hDr1 hHr1
      rw [hDr1, hHr1, L_anchor.get_put, xorK18_zero_left, L_anchor.put_put,
          QRegister.replaceIndex_comm_of_disjoint rAct rAnc hAA,
          QRegister.replaceIndex_replaceIndex]
    · simp only [ite_eq_right ha0, zero_mul, Pi.single_zero, Matrix.mulVec_zero]
  have hDAH : rDA.DisjointWires rHeld := disjointWires_concat_left hAA hAH hAnH
  have hHS : (Bell18TeleportCore.cHadReg rHeld).eval * S_anc =
      S_anc * (Bell18TeleportCore.cHadReg rHeld).eval :=
    Bell18TeleportCore.cHadReg_comm_embedUnitary_of_disjoint rHeld rDA (QRegExt.disjointWires_symm
      hDAH) _
  have hHA0 :=
    Bell18TeleportCore.cHadReg_comm_basisOutcomeProjector rHeld rAnc (QRegExt.disjointWires_symm
    hAnH) 0
  have hUnitAnc0 : (cCnot.eval * (U_wl * cPrep.eval)).1 * rAnc.basisOutcomeProjector 0 =
      (B_anc * S_anc).1 * rAnc.basisOutcomeProjector 0 := by
    dsimp only [cPrep, Bell18TeleportCore.cBellPrep, B_anc, Bell18TeleportCore.uBellSlot]
    rw [Circuit.eval_seq]
    have hL : (cCnot.eval * (U_wl * (cCnot.eval * (Bell18TeleportCore.cHadReg rHeld).eval))).1 =
        (cCnot.eval * (U_wl * cCnot.eval)).1 * (Bell18TeleportCore.cHadReg rHeld).eval.1 := by
      have hG : ∀ {G : Type} [Semigroup G] (a b c d : G),
          a * (b * (c * d)) = (a * (b * c)) * d := by
        intro G _ a b c d; simp only [mul_assoc]
      rw [hG, Submonoid.coe_mul]
    have hR : (((rAct.concat rHeld hAH).embedUnitary
          (Bell18TeleportCore.uLensWrite (toSlotK18 L_anchor)) *
          (Bell18TeleportCore.cHadReg rHeld).eval) * S_anc).1 =
        ((rAct.concat rHeld hAH).embedUnitary
          (Bell18TeleportCore.uLensWrite (toSlotK18 L_anchor)) * S_anc).1 *
          (Bell18TeleportCore.cHadReg rHeld).eval.1 := by
      have hG : ∀ {G : Type} [Semigroup G] (w h s : G),
          h * s = s * h → (w * h) * s = (w * s) * h := by
        intro G _ w h s hs; rw [mul_assoc, hs, ← mul_assoc]
      rw [hG _ _ _ hHS, Submonoid.coe_mul]
    rw [hL, hR]
    exact semigrp_unitAnc0 _ _ _ _ hHA0 hPermEq
  have hPinEq : P_in = rAnc.basisOutcomeProjector 0 *
      (rAct.embedMatrix E_ext *
        (rHeld.basisOutcomeProjector 0 * rW.basisOutcomeProjector 0)) := by
    dsimp only [P_in, P_rest]
    have hWE :=
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rW hAW E_ext 0).symm
    have hAE :=
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rAnc hAA E_ext 0).symm
    have hWA := proj0_comm_3c rW rAnc (QRegExt.disjointWires_symm hAnW)
    have hWH := proj0_comm_3c rW rHeld (QRegExt.disjointWires_symm hHW)
    exact semigrp_pinEq _ _ _ _ hWE hAE hWA hWH
  have hPinGoal : P_in = rAct.embedMatrix E_ext *
      (rAnc.basisOutcomeProjector 0 *
        (rHeld.basisOutcomeProjector 0 * rW.basisOutcomeProjector 0)) := by
    rw [hPinEq, ← Matrix.mul_assoc,
        ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rAnc hAA E_ext 0).symm,
        Matrix.mul_assoc]
  have hCongr : (cCnot.eval * (U_wl * cPrep.eval)).1 * P_in = (B_anc * S_anc).1 * P_in := by
    rw [hPinEq, ← Matrix.mul_assoc, hUnitAnc0, Matrix.mul_assoc]
  have hSeq2 := realizesOnProj_congr_unitary hCongr hSeq
  rwa [hPinGoal] at hSeq2

open FusedPreDiagFromTwist288 (preDiagCliffordExp128)
open ElecHadTrueSwapLocalCompClosure (extractPair extractPair_liftPairIdx)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (dPreDiagCliffordAnchor dPreDiagCliffordAnchorInv
   dPreDiagCliffordAnchor_count_toff dPreDiagCliffordAnchor_count_t
   dPreDiagCliffordAnchorInv_count_toff dPreDiagCliffordAnchorInv_count_t
   uAnchorFrame_mul embedIntertwineOp)
open LocalStageBFastInnerPartnerShift
  (E_anchor_ctrl11_eq E_anchor_cat11_eq)

/-- `+0 T`, `0 TOFF` Bell-18 PreDiag Clifford wrapper (`cS18`/`cSDag18` on `rHeld`). -/
def dWrapPreDiagCliffordBell18 {Var : Type} {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n)
    (dInner : DynamicCircuit Var n) : DynamicCircuit Var n :=
  dWrapPreDiagBell
    (cPreDiagCliffordAnchor rAct rAnc) (cS18.onRegister rHeld)
    (cPreDiagCliffordAnchorInv rAct rAnc) (cSDag18.onRegister rHeld)
    dInner

private theorem dWrapPreDiagCliffordBell18_counts {Var : Type} {n cT : ℕ}
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n)
    {dInner : DynamicCircuit Var n}
    (hToff : dInner.count TOFF = 0) (hT : dInner.count T ≤ cT) :
    (dWrapPreDiagCliffordBell18 rAct rAnc rHeld dInner).count TOFF = 0 ∧
      (dWrapPreDiagCliffordBell18 rAct rAnc rHeld dInner).count T ≤ cT := by
  refine dWrapPreDiagBell_counts ⟨?_, ?_, ?_, ?_, hToff⟩ ⟨?_, ?_, ?_, ?_⟩ hT
  · exact dPreDiagCliffordAnchor_count_toff (Var := PUnit) rAct rAnc
  · unfold cS18 cSK; simp only [Circuit.count_onRegister, count_sList_toff]
  · exact dPreDiagCliffordAnchorInv_count_toff (Var := PUnit) rAct rAnc
  · unfold cSDag18 cSDagK; simp only [Circuit.count_onRegister, count_sDagList_toff]
  · exact dPreDiagCliffordAnchor_count_t (Var := PUnit) rAct rAnc
  · unfold cS18 cSK; simp only [Circuit.count_onRegister, count_sList_t]
  · exact dPreDiagCliffordAnchorInv_count_t (Var := PUnit) rAct rAnc
  · unfold cSDag18 cSDagK; simp only [Circuit.count_onRegister, count_sDagList_t]

private noncomputable def P_slotEqHeldGen {kData n : ℕ} (L : Slot18Lens kData)
    (rAct : QRegister kData n) (rHeld : QRegister 18 n) : Operator (2 ^ n) :=
  Matrix.diagonal (fun z : Fin (2 ^ n) ↦
    if L.tbl (rAct.extractIndex z) = rHeld.extractIndex z then (1 : ℂ) else 0)

private noncomputable def P_slotEqHeld {n : ℕ}
    (rAct : QRegister kFull80 n) (rHeld : QRegister 18 n) : Operator (2 ^ n) :=
  Matrix.diagonal (fun z : Fin (2 ^ n) ↦
    if L_anchor.tbl (rAct.extractIndex z) = rHeld.extractIndex z then (1 : ℂ) else 0)

private theorem p_slotEqHeldGen_mul_uLensWrite_p_slot0 {kData n : ℕ}
    (L : Slot18Lens kData)
    (rAct : QRegister kData n) (rAnc rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc) (hAH : rAct.DisjointWires rHeld) :
    let rDA := rAct.concat rAnc hAA
    let W_h := (rAct.concat rHeld hAH).embedUnitary
      (Bell18TeleportCore.uLensWrite (toSlotK18 L))
    P_slotEqHeldGen L rAct rHeld * (W_h.1 * rDA.embedMatrix (P_slot0 L)) =
      W_h.1 * rDA.embedMatrix (P_slot0 L) := by
  intro rDA W_h
  let sData := StageADeconstrCore.selDataInAct kData
  apply matrix_ext_ket; intro β
  rw [ket_eq_single_loc β, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      P_slot0_eq_diagonal, embedMatrix_diagonal_part2, Matrix.diagonal_mulVec_single]
  set g := (basisBitsEquiv n).symm β
  by_cases h0 : L.tbl (sData.extractIndex (rDA.extractIndex g)) = 0
  · have h0' : L.tbl (rAct.extractIndex g) = 0 := by
      rwa [← QRegister.extractIndex_compose, ccData] at h0
    rw [ite_eq_left h0, one_mul]
    dsimp only [W_h]
    rw [Bell18TeleportCore.embedUnitary_uLensWrite_mulVec_single, toSlotK18_updSlot,
        toSlotK18_tbl]
    rw [h0', xorK18_zero_left, P_slotEqHeldGen, Matrix.diagonal_mulVec_single]
    let g' := rAct.replaceIndex g (L.updSlot (rAct.extractIndex g) (rHeld.extractIndex g))
    have hCond : L.tbl (rAct.extractIndex g') = rHeld.extractIndex g' := by
      dsimp only [g']
      rw [QRegister.extractIndex_replaceIndex, L.get_put,
          QRegister.extractIndex_replaceIndex_of_disjoint rHeld rAct (QRegExt.disjointWires_symm
            hAH)]
    rw [ite_eq_left hCond, one_mul]
  · rw [ite_eq_right h0, zero_mul, Pi.single_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]

private theorem P_slotEqHeld_mul_uBellSlot_E_anchor {mW n : ℕ}
    (E_ext : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAH : rAct.DisjointWires rHeld)
    (hAnH : rAnc.DisjointWires rHeld) :
    let B_anc := Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)
    P_slotEqHeld rAct rHeld *
      (B_anc.1 * (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0)) =
      B_anc.1 * (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0) := by
  intro B_anc
  let rDA := rAct.concat rAnc hAA
  let W_h := (rAct.concat rHeld hAH).embedUnitary
    (Bell18TeleportCore.uLensWrite (toSlotK18 L_anchor))
  have hWP0 : P_slotEqHeld rAct rHeld * (W_h.1 * rDA.embedMatrix (P_slot0 L_anchor)) =
      W_h.1 * rDA.embedMatrix (P_slot0 L_anchor) := by
    change P_slotEqHeldGen L_anchor rAct rHeld * (W_h.1 * rDA.embedMatrix (P_slot0 L_anchor)) =
      W_h.1 * rDA.embedMatrix (P_slot0 L_anchor)
    exact p_slotEqHeldGen_mul_uLensWrite_p_slot0 L_anchor rAct rAnc rHeld hAA hAH
  have hDAH : rDA.DisjointWires rHeld := disjointWires_concat_left hAA hAH hAnH
  have hHP0 : (Bell18TeleportCore.cHadReg rHeld).eval.1 *
      rDA.embedMatrix (P_slot0 L_anchor) =
      rDA.embedMatrix (P_slot0 L_anchor) * (Bell18TeleportCore.cHadReg rHeld).eval.1 :=
    Bell18TeleportCore.cHadReg_comm_embedMatrix_of_disjoint rHeld rDA (QRegExt.disjointWires_symm
      hDAH) _
  have hEAnc : E_anchor E_ext rAct rAnc rW hAA =
      rDA.embedMatrix (P_slot0 L_anchor) * E_anchor E_ext rAct rAnc rW hAA := by
    unfold E_anchor
    rw [← Matrix.mul_assoc, ← rDA.embedMatrix_mul, P_slot0_mul_E_anchorLoc]
  dsimp only [B_anc, Bell18TeleportCore.uBellSlot]
  conv_lhs => rw [hEAnc]
  have hGen : ∀ {R : Type} [Semigroup R] (Peq W H P0 E pH : R),
      H * P0 = P0 * H → Peq * (W * P0) = W * P0 → P0 * E = E →
      Peq * ((W * H) * ((P0 * E) * pH)) = (W * H) * (E * pH) := by
    intro R _ Peq W H P0 E pH h1 h2 h3
    have hL : Peq * ((W * H) * ((P0 * E) * pH)) = (Peq * (W * P0)) * (H * (E * pH)) := by
      simp only [← mul_assoc]; rw [mul_assoc (Peq * W) H P0, h1]; simp only [mul_assoc]
    rw [hL, h2]; simp only [← mul_assoc]
    rw [mul_assoc W P0 H, ← h1]; simp only [mul_assoc]; rw [← mul_assoc P0 E pH, h3]
  rw [Submonoid.coe_mul]
  exact hGen _ _ _ _ _ _ hHP0 hWP0 hEAnc.symm

set_option exponentiation.threshold 4050

private theorem preDiagSwapExp_eq_of_slotEqHeld {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc) (z : Fin (2 ^ n))
    (hEq : L_anchor.tbl (rAct.extractIndex z) = rHeld.extractIndex z) :
    preDiagCliffordExp128 (fun k ↦ basisBits (fullSysCoreWires 80)
      (rCoreFull.extractIndex (sData80.extractIndex
        (lensSwapEquiv L_anchor ((rAct.concat rAnc hAA).extractIndex z))))
      (coreElecCosetB1Block hm6_80 k)) =
    preDiagCliffordExp128 (fun k ↦ basisBits (fullSysCoreWires 80)
      ((rAct.compose rCoreFull).extractIndex z) (coreElecCosetB1Block hm6_80 k)) -
      (-32 * ∑ j : Fin 18, ((basisBits 18 (rHeld.extractIndex z) j).val : ℤ)) +
      (-32 * ∑ j : Fin 18, ((basisBits 18 (rAnc.extractIndex z) j).val : ℤ)) := by
  let d := rAct.extractIndex z
  let m := rAnc.extractIndex z
  let h := rHeld.extractIndex z
  let d₀ := L_anchor.updSlot d 0
  let z0 : Fin (2 ^ (kFull80 + 18)) := ⟨0, Nat.two_pow_pos _⟩
  let z_m : Fin (2 ^ (kFull80 + 18)) := liftPairIdx (fun _ ↦ (d₀, m)) z0
  let z_h : Fin (2 ^ (kFull80 + 18)) := liftPairIdx (fun _ ↦ (d₀, h)) z0
  have hd_m : sData80.extractIndex z_m = d₀ := by
    have h0 := congrArg Prod.fst (extractPair_liftPairIdx (fun _ ↦ (d₀, m)) z0)
    dsimp only [extractPair] at h0; exact h0
  have hm_m : sMeas80.extractIndex z_m = m := by
    have h0 := congrArg Prod.snd (extractPair_liftPairIdx (fun _ ↦ (d₀, m)) z0)
    dsimp only [extractPair] at h0; exact h0
  have hd_h : sData80.extractIndex z_h = d₀ := by
    have h0 := congrArg Prod.fst (extractPair_liftPairIdx (fun _ ↦ (d₀, h)) z0)
    dsimp only [extractPair] at h0; exact h0
  have hm_h : sMeas80.extractIndex z_h = h := by
    have h0 := congrArg Prod.snd (extractPair_liftPairIdx (fun _ ↦ (d₀, h)) z0)
    dsimp only [extractPair] at h0; exact h0
  have h0_m : L_anchor.tbl (sData80.extractIndex z_m) = 0 := by
    rw [hd_m]; exact L_anchor.get_put d 0
  have h0_h : L_anchor.tbl (sData80.extractIndex z_h) = 0 := by
    rw [hd_h]; exact L_anchor.get_put d 0
  have hExp_m := preDiagExp_updSlot_of_tbl_zero_gen (le_refl 80) hm6_80 rCoreFull z_m h0_m
  have hExp_h := preDiagExp_updSlot_of_tbl_zero_gen (le_refl 80) hm6_80 rCoreFull z_h h0_h
  have hSwZ : sData80.extractIndex
      (lensSwapEquiv L_anchor ((rAct.concat rAnc hAA).extractIndex z)) = L_anchor.updSlot d m := by
    have hPair := congrArg Prod.fst
      (extractPair_lensSwapEquiv L_anchor ((rAct.concat rAnc hAA).extractIndex z))
    dsimp only [extractPair, lensSwapPerm] at hPair
    rw [← QRegister.extractIndex_compose, ccData,
        ← QRegister.extractIndex_compose, ccMeas] at hPair
    exact hPair
  have hSwM : sData80.extractIndex (lensSwapEquiv L_anchor z_m) =
      L_anchor.updSlot d m := by
    have hPair := congrArg Prod.fst (extractPair_lensSwapEquiv L_anchor z_m)
    dsimp only [extractPair, lensSwapPerm] at hPair
    rw [hd_m, hm_m, L_anchor.put_put] at hPair
    exact hPair
  have hSwH : sData80.extractIndex (lensSwapEquiv L_anchor z_h) = d := by
    have hPair := congrArg Prod.fst (extractPair_lensSwapEquiv L_anchor z_h)
    dsimp only [extractPair, lensSwapPerm] at hPair
    rw [hd_h, hm_h, L_anchor.put_put] at hPair
    dsimp only [h, d] at hPair
    rw [← hEq, L_anchor.put_get] at hPair
    exact hPair
  have hComp : (rAct.compose rCoreFull).extractIndex z = rCoreFull.extractIndex d :=
    QRegister.extractIndex_compose rAct rCoreFull z
  change preDiagCliffordExp128 _ = _ at hExp_m hExp_h
  unfold L_anchor at hSwM hSwH
  dsimp only [sData80, sMeas80] at hSwM hSwH hd_m hm_m hd_h hm_h
  rw [hSwM, hd_m, hm_m] at hExp_m
  rw [hSwH, hd_h, hm_h] at hExp_h
  rw [hSwZ, hComp]
  unfold L_anchor
  rw [hExp_m, hExp_h]
  change _ + (-32 * ∑ j : Fin 18, ((basisBits 18 m j).val : ℤ)) =
    (_ + (-32 * ∑ j : Fin 18, ((basisBits 18 h j).val : ℤ))) -
      (-32 * ∑ j : Fin 18, ((basisBits 18 h j).val : ℤ)) +
      (-32 * ∑ j : Fin 18, ((basisBits 18 m j).val : ℤ))
  ring

private theorem cPreDiagBell18_mul_P_slotEqHeld {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc) :
    (cPreDiagCliffordAnchor rAct rAnc ;;ᶜ cS18.onRegister rHeld).eval.1 *
        P_slotEqHeld rAct rHeld =
      ((rAct.concat rAnc hAA).embedUnitary
        (uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)))).1 *
        P_slotEqHeld rAct rHeld := by
  let rDA := rAct.concat rAnc hAA
  rw [Circuit.eval_seq, cPreDiagCliffordAnchor_eval rAct rAnc hAA]
  unfold cS18 uPreDiagCliffordAnchorLoc uSDag18
  rw [Circuit.eval_onRegister, cSK_eval, QRegister.embedUnitary_mul,
      Submonoid.coe_mul, Submonoid.coe_mul,
      ← QRegister.embedUnitary_compose, ccMeas,
      ← QRegister.embedUnitary_compose, ccData,
      ← QRegister.embedUnitary_compose,
      embedUnitary_uSDagK_inv_eq_diagonal rHeld, embedUnitary_uSDagK_eq_diagonal rAnc,
      QRegister.embedUnitary_val, uPreDiagCliffordCore_eq_diagonal_gen hm6_80,
      embedMatrix_diagonal_part2,
      uAnchorFrame_of_uBarrelFast_conj_eq (uPreDiagCliffordCore hm6_80)
        uBarrelFast_conj_uPreDiagCliffordCore,
      QRegister.embedUnitary_val]
  unfold uAnchorLensSwap L_anchor
  rw [uLensSwap_conj_uPreDiagCliffordCore_eq_diagonal_gen (le_refl 80) hm6_80 rCoreFull,
      embedMatrix_diagonal_part2, P_slotEqHeld,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal; funext z
  by_cases hEq : L_anchor.tbl (rAct.extractIndex z) = rHeld.extractIndex z
  · rw [ite_eq_left hEq, mul_one, mul_one, dyadicTurn_add, dyadicTurn_add]
    have hExp := preDiagSwapExp_eq_of_slotEqHeld rAct rAnc rHeld hAA z hEq
    dsimp only [sData80, L_anchor] at hExp
    rw [hExp]
    exact congrArg (dyadicTurn 7) (by ring)
  · rw [ite_eq_right hEq, mul_zero, mul_zero]

private theorem cPreDiagBell18Inv_mul_P_slotEqHeld {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc) :
    (cPreDiagCliffordAnchorInv rAct rAnc ;;ᶜ cSDag18.onRegister rHeld).eval.1 *
        P_slotEqHeld rAct rHeld =
      ((rAct.concat rAnc hAA).embedUnitary
        (uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹))).1 *
        P_slotEqHeld rAct rHeld := by
  let rDA := rAct.concat rAnc hAA
  rw [Circuit.eval_seq, cPreDiagCliffordAnchorInv_eval rAct rAnc hAA]
  unfold cSDag18 uPreDiagCliffordAnchorInvLoc uSDag18
  rw [Circuit.eval_onRegister, cSDagK_eval, QRegister.embedUnitary_mul,
      Submonoid.coe_mul, Submonoid.coe_mul,
      ← QRegister.embedUnitary_compose, ccMeas,
      ← QRegister.embedUnitary_compose, ccData,
      ← QRegister.embedUnitary_compose,
      embedUnitary_uSDagK_eq_diagonal rHeld, embedUnitary_uSDagK_inv_eq_diagonal rAnc,
      QRegister.embedUnitary_val, uPreDiagCliffordCore_inv_eq_diagonal_gen hm6_80,
      embedMatrix_diagonal_part2,
      uAnchorFrame_of_uBarrelFast_conj_eq (uPreDiagCliffordCore hm6_80)⁻¹
        uBarrelFast_conj_uPreDiagCliffordCore_inv,
      QRegister.embedUnitary_val]
  unfold uAnchorLensSwap L_anchor
  rw [uLensSwap_conj_uPreDiagCliffordCore_inv_eq_diagonal_gen (le_refl 80) hm6_80 rCoreFull,
      embedMatrix_diagonal_part2, P_slotEqHeld,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal; funext z
  by_cases hEq : L_anchor.tbl (rAct.extractIndex z) = rHeld.extractIndex z
  · rw [ite_eq_left hEq, mul_one, mul_one, dyadicTurn_add, dyadicTurn_add]
    have hExp := preDiagSwapExp_eq_of_slotEqHeld rAct rAnc rHeld hAA z hEq
    dsimp only [sData80, L_anchor] at hExp
    rw [hExp]
    exact congrArg (dyadicTurn 7) (by ring)
  · rw [ite_eq_right hEq, mul_zero, mul_zero]

private theorem uAnchorFrame_intertwines_E_bellAnchor {mW n : ℕ}
    {E_ext : Operator (2 ^ kFull80)} {U : Unitary (2 ^ kFull80)}
    {V_loc : Operator (2 ^ (kFull80 + 18))}
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAH : rAct.DisjointWires rHeld)
    (hAW : rAct.DisjointWires rW) (hAnH : rAnc.DisjointWires rHeld)
    (hAnW : rAnc.DisjointWires rW)
    (hLoc : (uAnchorFrame U).1 * E_anchorLoc E_ext = E_anchorLoc E_ext * V_loc) :
    let B_anc := Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)
    let E_bell := B_anc.1 * (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0)
    ((rAct.concat rAnc hAA).embedUnitary (uAnchorFrame U)).1 * E_bell =
      E_bell * (rAct.concat rAnc hAA).embedMatrix V_loc := by
  intro B_anc E_bell
  let rDA := rAct.concat rAnc hAA
  have hAAW : rDA.DisjointWires rW := disjointWires_concat_left hAA hAW hAnW
  have hDAH : rDA.DisjointWires rHeld := disjointWires_concat_left hAA hAH hAnH
  have h1 : (rDA.embedUnitary (uAnchorFrame U)).1 * E_anchor E_ext rAct rAnc rW hAA =
      E_anchor E_ext rAct rAnc rW hAA * rDA.embedMatrix V_loc :=
    embedIntertwineOp hAAW hLoc
  have hCB : (rDA.embedUnitary (uAnchorFrame U)).1 * B_anc.1 =
      B_anc.1 * (rDA.embedUnitary (uAnchorFrame U)).1 :=
    congrArg Subtype.val (uAnchorFrame_comm_uBellSlot rAct rAnc rHeld hAA hAH hAnH U)
  have hCH : rDA.embedMatrix V_loc * rHeld.basisOutcomeProjector 0 =
      rHeld.basisOutcomeProjector 0 * rDA.embedMatrix V_loc :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rDA) rHeld hDAH V_loc 0
  dsimp only [E_bell]
  have hGen : ∀ {R : Type} [Semigroup R] (F B E pH V : R),
      F * B = B * F → F * E = E * V → V * pH = pH * V →
      F * (B * (E * pH)) = (B * (E * pH)) * V := by
    intro R _ F B E pH V hFB hFE hVH
    rw [← mul_assoc F B, hFB, mul_assoc B F, ← mul_assoc F E, hFE, mul_assoc E V pH, hVH]
    simp only [mul_assoc]
  exact hGen _ _ _ _ _ hCB h1 hCH

private theorem dWrapPreDiagCliffordBell18_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ} [NeZero (2 ^ n)]
    {E_ext : Operator (2 ^ kFull80)}
    {V_D V_raw : Operator (2 ^ (kFull80 + 18))}
    {uRawFull : Unitary (2 ^ kFull80)} {dInner : DynamicCircuit Var n}
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAH : rAct.DisjointWires rHeld)
    (hAW : rAct.DisjointWires rW) (hAnH : rAnc.DisjointWires rHeld)
    (hAnW : rAnc.DisjointWires rW)
    (hDE : (uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))).1 *
      E_anchorLoc E_ext = E_anchorLoc E_ext * V_D)
    (hInterRaw : (uAnchorFrame uRawFull).1 * E_anchorLoc E_ext = E_anchorLoc E_ext * V_raw)
    (hRealRaw : RealizesOnProj
      ((Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)).1 *
        (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0))
      ((rAct.concat rAnc hAA).embedUnitary (uAnchorFrame uRawFull))
      dInner) :
    RealizesOnProj
      ((Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)).1 *
        (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0))
      ((rAct.concat rAnc hAA).embedUnitary (uAnchorFrame (uWrapPreDiagCliffordFull uRawFull)))
      (dWrapPreDiagCliffordBell18 rAct rAnc rHeld dInner) := by
  let rDA := rAct.concat rAnc hAA
  let B_anc := Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)
  let E_bell := B_anc.1 * (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0)
  let D := uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))
  let DInv := uAnchorFrame (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹)
  have hAbs := P_slotEqHeld_mul_uBellSlot_E_anchor E_ext rAct rAnc rHeld rW hAA hAH hAnH
  have p1 : RealizesOnProj (Var := Var) E_bell (rDA.embedUnitary D)
      (.circuit (cPreDiagCliffordAnchor rAct rAnc ;;ᶜ cS18.onRegister rHeld)) := by
    refine realizesOnProj_congr_unitary ?_
      (Bell18Seq6Bridge.RealizesOnProj.of_circuit (Var := Var) E_bell _)
    dsimp only [E_bell, B_anc] at hAbs ⊢
    rw [← hAbs, ← Matrix.mul_assoc, cPreDiagBell18_mul_P_slotEqHeld rAct rAnc rHeld hAA,
        Matrix.mul_assoc]
  have p3 : RealizesOnProj (Var := Var) E_bell (rDA.embedUnitary DInv)
      (.circuit (cPreDiagCliffordAnchorInv rAct rAnc ;;ᶜ cSDag18.onRegister rHeld)) := by
    refine realizesOnProj_congr_unitary ?_
      (Bell18Seq6Bridge.RealizesOnProj.of_circuit (Var := Var) E_bell _)
    dsimp only [E_bell, B_anc] at hAbs ⊢
    rw [← hAbs, ← Matrix.mul_assoc, cPreDiagBell18Inv_mul_P_slotEqHeld rAct rAnc rHeld hAA,
        Matrix.mul_assoc]
  have hI1 := uAnchorFrame_intertwines_E_bellAnchor rAct rAnc rHeld rW
    hAA hAH hAW hAnH hAnW hDE
  have hI2 := uAnchorFrame_intertwines_E_bellAnchor rAct rAnc rHeld rW
    hAA hAH hAW hAnH hAnW hInterRaw
  have hCh := p1.seq_intertwine hI1 (hRealRaw.seq_intertwine hI2 p3)
  have hComb : rDA.embedUnitary DInv *
        (rDA.embedUnitary (uAnchorFrame uRawFull) * rDA.embedUnitary D) =
      rDA.embedUnitary (uAnchorFrame (uWrapPreDiagCliffordFull uRawFull)) := by
    rw [← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
    apply congrArg rDA.embedUnitary
    dsimp only [DInv, D, uWrapPreDiagCliffordFull]
    rw [uAnchorFrame_mul, uAnchorFrame_mul]
  change RealizesOnProj _
    ((rDA.embedUnitary DInv * rDA.embedUnitary (uAnchorFrame uRawFull)) *
      rDA.embedUnitary D) _ at hCh
  unfold dWrapPreDiagCliffordBell18 dWrapPreDiagBell
  rwa [mul_assoc, hComb] at hCh

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
set_option exponentiation.threshold 4200

/-- Fused Bell-18 `OpenQft` Stage-A + 1-wire Stage-B `Ctrl` circuit
(`≤ 47,929 + stageBOneWireBoothOptAnchorT B (mWorkSub18 - 20)`, `0 TOFF`). -/
noncomputable def dFusedBell18OpenAnchorCtrlOneWire {Var : Type} {mWorkSub18 n : ℕ}
    (stA : StageABell18Witness)
    (hm161 : 161 ≤ mWorkSub18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc : QRegister 18 n)
    (rW : QRegister mWorkSub18 n) (rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc)
    (hAW : rAct.DisjointWires rW) (hAnW : rAnc.DisjointWires rW) : DynamicCircuit Var n :=
  dWrapPreDiagCliffordBell18 rAct rAnc rHeld
    (.seq
      (stA.dStageA hm161 v rAct rAnc rW rHeld hAA hAW hAnW)
      (dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire (le_refl 11) (by decide : 11 + 3 ≤ 41)
        (by omega : 172 ≤ mWorkSub18 + (3 + 11)) B hB6 hB27 v rAct rAnc rW hAA hAW hAnW))

/-- Fused Bell-18 `OpenQft` Stage-A + 1-wire Stage-B `Cat` circuit
(`≤ 47,929 + stageBOneWireBoothOptAnchorT B (mWorkSub18 - 17)`, `0 TOFF`). -/
noncomputable def dFusedBell18OpenAnchorCatOneWire {Var : Type} {mWorkSub18 n : ℕ}
    (stA : StageABell18Witness)
    (hm161 : 161 ≤ mWorkSub18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc : QRegister 18 n)
    (rW : QRegister mWorkSub18 n) (rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc)
    (hAW : rAct.DisjointWires rW) (hAnW : rAnc.DisjointWires rW) : DynamicCircuit Var n :=
  dWrapPreDiagCliffordBell18 rAct rAnc rHeld
    (.seq
      (stA.dStageA hm161 v rAct rAnc rW rHeld hAA hAW hAnW)
      (dStageBOpenAnchorCat_borrowExt6IdleOneWire (le_refl 11) (by decide : 11 + 3 ≤ 41)
        (by omega : 172 ≤ mWorkSub18 + (6 + 11)) B hB6 hB27 v rAct rAnc rW hAA hAW hAnW))

theorem dFusedBell18OpenAnchorCtrlOneWire_count_toff {Var : Type} {mWorkSub18 n : ℕ}
    (stA : StageABell18Witness)
    (hm161 : 161 ≤ mWorkSub18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc : QRegister 18 n)
    (rW : QRegister mWorkSub18 n) (rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc)
    (hAW : rAct.DisjointWires rW) (hAnW : rAnc.DisjointWires rW) :
    (dFusedBell18OpenAnchorCtrlOneWire stA hm161 B hB6 hB27 v rAct rAnc rW rHeld
      hAA hAW hAnW).count TOFF = 0 := by
  refine (dWrapPreDiagCliffordBell18_counts rAct rAnc rHeld ?_ (le_refl _)).1
  dsimp only [DynamicCircuit.count]
  rw [stA.count_toff hm161 v rAct rAnc rW rHeld hAA hAW hAnW,
      dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire_count_toff]

theorem dFusedBell18OpenAnchorCatOneWire_count_toff {Var : Type} {mWorkSub18 n : ℕ}
    (stA : StageABell18Witness)
    (hm161 : 161 ≤ mWorkSub18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc : QRegister 18 n)
    (rW : QRegister mWorkSub18 n) (rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc)
    (hAW : rAct.DisjointWires rW) (hAnW : rAnc.DisjointWires rW) :
    (dFusedBell18OpenAnchorCatOneWire stA hm161 B hB6 hB27 v rAct rAnc rW rHeld
      hAA hAW hAnW).count TOFF = 0 := by
  refine (dWrapPreDiagCliffordBell18_counts rAct rAnc rHeld ?_ (le_refl _)).1
  dsimp only [DynamicCircuit.count]
  rw [stA.count_toff hm161 v rAct rAnc rW rHeld hAA hAW hAnW,
      dStageBOpenAnchorCat_borrowExt6IdleOneWire_count_toff]

theorem stageBOneWireBoothOptAnchorT_ge_600 (B mClean : ℕ) (hm : 139 ≤ mClean) :
    600 ≤ stageBOneWireBoothOptAnchorT B mClean ∧
      StageBOneWireBridge.kOneWire mClean ≠ 0 := by
  have hk := kOneWire_le_18 mClean
  unfold stageBOneWireBoothOptAnchorT stageBOneWireKBoothOptAnchorT
    StageBOneWireBridge.kOneWire at *
  omega

theorem dFusedBell18OpenAnchorCtrlOneWire_count_t_le {Var : Type} {mWorkSub18 n : ℕ}
    (stA : StageABell18Witness)
    (hm161 : 161 ≤ mWorkSub18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc : QRegister 18 n)
    (rW : QRegister mWorkSub18 n) (rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc)
    (hAW : rAct.DisjointWires rW) (hAnW : rAnc.DisjointWires rW) :
    (dFusedBell18OpenAnchorCtrlOneWire stA hm161 B hB6 hB27 v rAct rAnc rW rHeld
      hAA hAW hAnW).count T ≤
      47493 + stageBOneWireBoothOptAnchorT B (mWorkSub18 - 20) := by
  refine (dWrapPreDiagCliffordBell18_counts rAct rAnc rHeld ?_ ?_).2
  · dsimp only [DynamicCircuit.count]
    rw [stA.count_toff hm161 v rAct rAnc rW rHeld hAA hAW hAnW,
        dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire_count_toff]
  · dsimp only [DynamicCircuit.count]
    have hA := stA.count_t_le hm161 v rAct rAnc rW rHeld hAA hAW hAnW
    have hB := dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire_count_t_le_fused
      (le_refl 11) (by decide) (by omega : 172 ≤ mWorkSub18 + (3 + 11))
      B hB6 hB27 v rAct rAnc rW hAA hAW hAnW
    have hSub : (mWorkSub18 + (3 + 11)) - 34 = mWorkSub18 - 20 := by omega
    rw [hSub] at hB
    obtain ⟨hGe, hk0⟩ := stageBOneWireBoothOptAnchorT_ge_600 B (mWorkSub18 - 20) (by omega)
    simp only [hk0, ↓reduceIte] at hB
    omega

theorem dFusedBell18OpenAnchorCatOneWire_count_t_le {Var : Type} {mWorkSub18 n : ℕ}
    (stA : StageABell18Witness)
    (hm161 : 161 ≤ mWorkSub18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc : QRegister 18 n)
    (rW : QRegister mWorkSub18 n) (rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc)
    (hAW : rAct.DisjointWires rW) (hAnW : rAnc.DisjointWires rW) :
    (dFusedBell18OpenAnchorCatOneWire stA hm161 B hB6 hB27 v rAct rAnc rW rHeld
      hAA hAW hAnW).count T ≤
      47493 + stageBOneWireBoothOptAnchorT B (mWorkSub18 - 17) := by
  refine (dWrapPreDiagCliffordBell18_counts rAct rAnc rHeld ?_ ?_).2
  · dsimp only [DynamicCircuit.count]
    rw [stA.count_toff hm161 v rAct rAnc rW rHeld hAA hAW hAnW,
        dStageBOpenAnchorCat_borrowExt6IdleOneWire_count_toff]
  · dsimp only [DynamicCircuit.count]
    have hA := stA.count_t_le hm161 v rAct rAnc rW rHeld hAA hAW hAnW
    have hB := dStageBOpenAnchorCat_borrowExt6IdleOneWire_count_t_le_fused
      (le_refl 11) (by decide) (by omega : 172 ≤ mWorkSub18 + (6 + 11))
      B hB6 hB27 v rAct rAnc rW hAA hAW hAnW
    have hSub : (mWorkSub18 + (6 + 11)) - 34 = mWorkSub18 - 17 := by omega
    rw [hSub] at hB
    obtain ⟨hGe, hk0⟩ := stageBOneWireBoothOptAnchorT_ge_600 B (mWorkSub18 - 17) (by omega)
    simp only [hk0, ↓reduceIte] at hB
    omega

private theorem uBarrelFastAct_mul_uSlot0MeasSwap_eq_trueSwap :
    uBarrelFastAct * uSlot0MeasSwap = uAnchorTrueSwapFull * uBarrelFastOnActFull := by
  rw [uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct,
      uBarrelFastAct_eq_embedData_rCoreFull]
  unfold uAnchorTrueSwapFull uAnchorLensSwap L_anchor uBarrelFastOnActFull
  refine congrArg (uLensSwap (coinBarrelFastOnDataLens (le_refl 80) rCoreFull) * ·) ?_
  refine congrArg (fun r : QRegister kFull80 (kFull80 + 18) ↦
    r.embedUnitary (rCoreFull.embedUnitary (uBarrelFast (le_refl 80)))) ?_
  apply InterWalkRSum42Hoist.qreg_ext; intro i; rfl

theorem dFusedBell18OpenAnchorCtrlOneWire_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWorkSub18 n : ℕ} [NeZero (2 ^ n)]
    (stA : StageABell18Witness)
    (hm161 : 161 ≤ mWorkSub18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc : QRegister 18 n)
    (rW : QRegister mWorkSub18 n) (rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc) (hAW : rAct.DisjointWires rW)
    (hAnW : rAnc.DisjointWires rW) (hAH : rAct.DisjointWires rHeld)
    (hAnH : rAnc.DisjointWires rHeld) (hWH : rW.DisjointWires rHeld) :
    RealizesOnProj
      ((Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)).1 *
        (E_anchor (E_rawCtrl3Ext 11 (by decide)) rAct rAnc rW hAA *
          rHeld.basisOutcomeProjector 0))
      ((rAct.concat rAnc hAA).embedUnitary
        (uAnchorFrame
          (uWrapPreDiagCliffordFull
            (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull
              B hB6 hB27 * uStageARawFull))))
      (dFusedBell18OpenAnchorCtrlOneWire stA hm161 B hB6 hB27 v rAct rAnc rW rHeld
        hAA hAW hAnW) := by
  let rDA := rAct.concat rAnc hAA
  let G0 := G_bell18Init rAnc rHeld hAnH
  have hDE := uAnchorFrame_intertwines_E_anchorLoc
    (uPreDiagCliffordCore_comm_E_rawCtrl3Ext_and_E_rawSegExt (by decide : 11 ≤ 48)).1
  have hRawExtA :=
    (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      (rawABorrow48054.uRawACtrlFull 0).1 (rawABorrow48054.uRawASeg 0)
      (rawABorrow48054.hRawACtrl 0) (rawABorrow48054.hRawACtrl3 0)
      (rawABorrow48054.hRawAIdle11 0)).1
  have hRawExtB :=
    (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      (uStageBFull B hB6 hB27).1
      (StageBPartnerTrueSwapStream218Closure.uStageBSeg B hB6 hB27)
      (uStageBFull_mul_E_rawStream42_eq B hB6 hB27)
      (commutesWithReg_rCtrl3InSeg_uStageBSeg B hB6 hB27)
      (commutesWithReg_rPGIdleOrig_uStageBSeg 11 (by decide) (by decide) B hB6 hB27)).1
  have hA := stA.realizesOnProj_ctrl_gen hm161 v rAct rAnc rW rHeld
    hAA hAW hAnW hAH hAnH hWH (pEqReg_mul_G_bell18Init rAnc rHeld hAnH)
  have hB : RealizesOnProj
      (rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
        E_bell18Gen (E_rawCtrl3Ext 11 (by decide)) rAct rAnc rW hAA G0)
      (rDA.embedUnitary (uAnchorFrame
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull
          B hB6 hB27 * uJunctionRawFull)))
      (dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire (le_refl 11) (by decide)
        (by omega : 172 ≤ mWorkSub18 + (3 + 11)) B hB6 hB27 v rAct rAnc rW hAA hAW hAnW) := by
    have hMid := dStageBOpenAnchorCtrl_borrowCtrl3IdleOneWire_realizesOnProj_mid
      (le_refl 11) (by decide) (by omega) B hB6 hB27 v rAct rAnc rW hAA hAW hAnW G0
    have hEqP : rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          (rDA.embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
            pRawCtrl3ExtOn 11 (by decide) rAct rW * G0) =
        rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          E_bell18Gen (E_rawCtrl3Ext 11 (by decide)) rAct rAnc rW hAA G0 := by
      unfold E_bell18Gen pRawCtrl3ExtOn
      rw [uBarrelFastAct_mul_uSlot0MeasSwap_eq_trueSwap]
      dsimp only [rDA]
      simp only [Matrix.mul_assoc]
    dsimp only [rDA] at hEqP
    rwa [hEqP] at hMid
  have hUACtrl : rawABorrow48054.uRawACtrlFull 0 = uStageARawFull := by
    dsimp only [ChiralDStageABridge.rawABorrow48054,
      StageADeconstrAndQftShare.rawA]
  have hRawA0 : uStageARawFull.1 * E_rawCtrl3Ext 11 (by decide) =
      E_rawCtrl3Ext 11 (by decide) *
        (rSegFull.embedUnitary (rawABorrow48054.uRawASeg 0)).1 := by
    rwa [hUACtrl] at hRawExtA
  have hIntA : (rDA.embedUnitary (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull))).1 *
        E_bell18Gen (E_rawCtrl3Ext 11 (by decide)) rAct rAnc rW hAA G0 =
      (rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
        E_bell18Gen (E_rawCtrl3Ext 11 (by decide)) rAct rAnc rW hAA G0) *
        rAct.embedMatrix (rSegFull.embedUnitary (rawABorrow48054.uRawASeg 0)).1 := by
    dsimp only [rDA]
    rw [← uAnchorFrame_mul, uAnchorFrame_uJunctionRawFull_inv_eq,
        QRegister.embedUnitary_mul, Submonoid.coe_mul,
        (rAct.concat rAnc hAA).embedUnitary_val uJunctionAncFull18⁻¹,
        Matrix.mul_assoc,
        uAnchorFrame_step_E_bell18Gen hRawA0 rAct rAnc rW hAA hAW
          (embedMatrix_comm_G_bell18Init rAct rAnc rHeld hAA hAH hAnH _),
        ← Matrix.mul_assoc]
  have hSeq := hA.seq_intertwine hIntA hB
  have hProdEq :
      rDA.embedUnitary (uAnchorFrame
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull
          B hB6 hB27 * uJunctionRawFull)) *
      rDA.embedUnitary (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)) =
      rDA.embedUnitary (uAnchorFrame
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull
          B hB6 hB27 * uStageARawFull)) := by
    rw [← QRegister.embedUnitary_mul, uAnchorFrame_mul]
    refine congrArg (fun u ↦ rDA.embedUnitary (uAnchorFrame u)) ?_
    have hGrp : ∀ {G : Type} [Group G] (a b c : G), (a * b) * (b⁻¹ * c) = a * c := by
      intro G _ a b c; rw [mul_assoc a b, ← mul_assoc b b⁻¹, mul_inv_cancel, one_mul]
    exact hGrp _ _ _
  rw [hProdEq, ← uBellSlot_mul_E_anchor_eq_E_bell18Gen
    (E_rawCtrl3Ext 11 (by decide)) rAct rAnc rHeld rW hAA hAH hAW hAnH hAnW
      (QRegExt.disjointWires_symm hWH)] at hSeq
  exact dWrapPreDiagCliffordBell18_realizesOnProj rAct rAnc rHeld rW
    hAA hAH hAW hAnH hAnW hDE
    (uAnchorFrame_intertwines_E_anchorLoc (mul_intertwine_same hRawExtB hRawA0)) hSeq

theorem dFusedBell18OpenAnchorCatOneWire_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWorkSub18 n : ℕ} [NeZero (2 ^ n)]
    (stA : StageABell18Witness)
    (hm161 : 161 ≤ mWorkSub18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc : QRegister 18 n)
    (rW : QRegister mWorkSub18 n) (rHeld : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnc) (hAW : rAct.DisjointWires rW)
    (hAnW : rAnc.DisjointWires rW) (hAH : rAct.DisjointWires rHeld)
    (hAnH : rAnc.DisjointWires rHeld) (hWH : rW.DisjointWires rHeld) :
    RealizesOnProj
      ((Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)).1 *
        (E_anchor (E_rawSegExt 11 (by decide)) rAct rAnc rW hAA *
          rHeld.basisOutcomeProjector 0))
      ((rAct.concat rAnc hAA).embedUnitary
        (uAnchorFrame
          (uWrapPreDiagCliffordFull
            (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull
              B hB6 hB27 * uStageARawFull))))
      (dFusedBell18OpenAnchorCatOneWire stA hm161 B hB6 hB27 v rAct rAnc rW rHeld
        hAA hAW hAnW) := by
  let rDA := rAct.concat rAnc hAA
  let G0 := G_bell18Init rAnc rHeld hAnH
  have hDE := uAnchorFrame_intertwines_E_anchorLoc
    (uPreDiagCliffordCore_comm_E_rawCtrl3Ext_and_E_rawSegExt (by decide : 11 ≤ 48)).2
  have hRawExtA :=
    (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      (rawABorrow48054.uRawACatFull 0).1 (rawABorrow48054.uRawASeg 0)
      (rawABorrow48054.hRawACat 0) (rawABorrow48054.hRawACtrl3 0)
      (rawABorrow48054.hRawAIdle11 0)).2
  have hRawExtB :=
    (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      (uStageBFull B hB6 hB27).1
      (StageBPartnerTrueSwapStream218Closure.uStageBSeg B hB6 hB27)
      (uStageBFull_mul_E_rawStream42_eq B hB6 hB27)
      (commutesWithReg_rCtrl3InSeg_uStageBSeg B hB6 hB27)
      (commutesWithReg_rPGIdleOrig_uStageBSeg 11 (by decide) (by decide) B hB6 hB27)).2
  have hA := stA.realizesOnProj_cat_gen hm161 v rAct rAnc rW rHeld
    hAA hAW hAnW hAH hAnH hWH (pEqReg_mul_G_bell18Init rAnc rHeld hAnH)
  have hB : RealizesOnProj
      (rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
        E_bell18Gen (E_rawSegExt 11 (by decide)) rAct rAnc rW hAA G0)
      (rDA.embedUnitary (uAnchorFrame
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull
          B hB6 hB27 * uJunctionRawFull)))
      (dStageBOpenAnchorCat_borrowExt6IdleOneWire (le_refl 11) (by decide)
        (by omega : 172 ≤ mWorkSub18 + (6 + 11)) B hB6 hB27 v rAct rAnc rW hAA hAW hAnW) := by
    have hMid := dStageBOpenAnchorCat_borrowExt6IdleOneWire_realizesOnProj_mid
      (le_refl 11) (by decide) (by omega) B hB6 hB27 v rAct rAnc rW hAA hAW hAnW G0
    have hEqP : rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          (rDA.embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
            pRawHoistExtOn 11 (by decide) rAct rW * G0) =
        rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
          E_bell18Gen (E_rawSegExt 11 (by decide)) rAct rAnc rW hAA G0 := by
      unfold E_bell18Gen pRawHoistExtOn
      rw [uBarrelFastAct_mul_uSlot0MeasSwap_eq_trueSwap]
      dsimp only [rDA]
      simp only [Matrix.mul_assoc]
    dsimp only [rDA] at hEqP
    rwa [hEqP] at hMid
  have hUACat : rawABorrow48054.uRawACatFull 0 = uStageARawFull := by
    dsimp only [ChiralDStageABridge.rawABorrow48054,
      StageADeconstrAndQftShare.rawA]
  have hRawA0 : uStageARawFull.1 * E_rawSegExt 11 (by decide) =
      E_rawSegExt 11 (by decide) *
        (rSegFull.embedUnitary (rawABorrow48054.uRawASeg 0)).1 := by
    rwa [hUACat] at hRawExtA
  have hIntA : (rDA.embedUnitary (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull))).1 *
        E_bell18Gen (E_rawSegExt 11 (by decide)) rAct rAnc rW hAA G0 =
      (rDA.embedMatrix (uJunctionAncFull18⁻¹).1 *
        E_bell18Gen (E_rawSegExt 11 (by decide)) rAct rAnc rW hAA G0) *
        rAct.embedMatrix (rSegFull.embedUnitary (rawABorrow48054.uRawASeg 0)).1 := by
    dsimp only [rDA]
    rw [← uAnchorFrame_mul, uAnchorFrame_uJunctionRawFull_inv_eq,
        QRegister.embedUnitary_mul, Submonoid.coe_mul,
        (rAct.concat rAnc hAA).embedUnitary_val uJunctionAncFull18⁻¹,
        Matrix.mul_assoc,
        uAnchorFrame_step_E_bell18Gen hRawA0 rAct rAnc rW hAA hAW
          (embedMatrix_comm_G_bell18Init rAct rAnc rHeld hAA hAH hAnH _),
        ← Matrix.mul_assoc]
  have hSeq := hA.seq_intertwine hIntA hB
  have hProdEq :
      rDA.embedUnitary (uAnchorFrame
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull
          B hB6 hB27 * uJunctionRawFull)) *
      rDA.embedUnitary (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)) =
      rDA.embedUnitary (uAnchorFrame
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull
          B hB6 hB27 * uStageARawFull)) := by
    rw [← QRegister.embedUnitary_mul, uAnchorFrame_mul]
    refine congrArg (fun u ↦ rDA.embedUnitary (uAnchorFrame u)) ?_
    have hGrp : ∀ {G : Type} [Group G] (a b c : G), (a * b) * (b⁻¹ * c) = a * c := by
      intro G _ a b c; rw [mul_assoc a b, ← mul_assoc b b⁻¹, mul_inv_cancel, one_mul]
    exact hGrp _ _ _
  rw [hProdEq, ← uBellSlot_mul_E_anchor_eq_E_bell18Gen
    (E_rawSegExt 11 (by decide)) rAct rAnc rHeld rW hAA hAH hAW hAnH hAnW
      (QRegExt.disjointWires_symm hWH)] at hSeq
  exact dWrapPreDiagCliffordBell18_realizesOnProj rAct rAnc rHeld rW
    hAA hAH hAW hAnH hAnW hDE
    (uAnchorFrame_intertwines_E_anchorLoc (mul_intertwine_same hRawExtB hRawA0)) hSeq

/-- 6-step `17,696 + 724 + tA + tB` `T` (`0 TOFF`) Bell-18 Single-Barrel `FoldedPass123`
circuit on `(rAct, rAnc, rHeld, rW)` (`143 ≤ mW`). -/
noncomputable def dSingleBarrel6StepBell18Fast {Var : Type} {mW n : ℕ}
    (hm143 : 143 ≤ mW) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAW : rAct.DisjointWires rW)
    (hAnH : rAnc.DisjointWires rHeld) (hAnW : rAnc.DisjointWires rW)
    (dStageA dStageB : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (dPreBell18AnchorFast hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW)
    (.seq (dPass1Anchor (by omega : 130 ≤ mW) v rAct rAnc rW hAA hAW hAnW)
      (.seq dStageA
        (.seq dStageB
          (.seq (dPass3Anchor (by omega : 13 ≤ mW) v rAct rAnc rW hAA hAW hAnW)
            (dPostBell18AnchorFast (le_refl 80) hm143 v rAct rCoreFull rAnc rHeld rW
              hAW hAnH)))))

theorem count_dSingleBarrel6StepBell18Fast_toff {Var : Type} {mW n : ℕ}
    (hm143 : 143 ≤ mW) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAW : rAct.DisjointWires rW)
    (hAnH : rAnc.DisjointWires rHeld) (hAnW : rAnc.DisjointWires rW)
    {dStageA dStageB : DynamicCircuit Var n}
    (hToffA : dStageA.count TOFF = 0) (hToffB : dStageB.count TOFF = 0) :
    (dSingleBarrel6StepBell18Fast hm143 v rAct rAnc rHeld rW
      hAA hAW hAnH hAnW dStageA dStageB).count TOFF = 0 := by
  unfold dSingleBarrel6StepBell18Fast
  have z1 := (dPreBell18AnchorFast_counts hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW).1
  have z2 := dPass1Anchor_count_toff (by omega : 130 ≤ mW) v rAct rAnc rW hAA hAW hAnW
  have z5 := dPass3Anchor_count_toff (by omega : 13 ≤ mW) v rAct rAnc rW hAA hAW hAnW
  have z6 := dPostBell18AnchorFast_count_toff (le_refl 80) hm143 v rAct rCoreFull
    rAnc rHeld rW hAW hAnH
  simp only [DynamicCircuit.count, z1, z2, hToffA, hToffB, z5, z6, add_zero]

theorem count_dSingleBarrel6StepBell18Fast_t_le {Var : Type} {mW tA tB n : ℕ}
    (hm143 : 143 ≤ mW) (v : Var)
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAW : rAct.DisjointWires rW)
    (hAnH : rAnc.DisjointWires rHeld) (hAnW : rAnc.DisjointWires rW)
    {dStageA dStageB : DynamicCircuit Var n}
    (hTA : dStageA.count T ≤ tA) (hTB : dStageB.count T ≤ tB) :
    (dSingleBarrel6StepBell18Fast hm143 v rAct rAnc rHeld rW
      hAA hAW hAnH hAnW dStageA dStageB).count T ≤ 17260 + 724 + tA + tB := by
  unfold dSingleBarrel6StepBell18Fast
  have h1 := (dPreBell18AnchorFast_counts hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW).2
  have h2 := dPass1Anchor_count_t (by omega : 130 ≤ mW) v rAct rAnc rW hAA hAW hAnW
  have h5 := dPass3Anchor_count_t (by omega : 13 ≤ mW) v rAct rAnc rW hAA hAW hAnW
  have h6 := dPostBell18AnchorFast_count_t_le (le_refl 80) hm143 v rAct rCoreFull
    rAnc rHeld rW hAW hAnH
  simp only [DynamicCircuit.count, h2, h5]
  omega

private theorem proj0_rW_mul_E_bellAnchor {mW n : ℕ}
    (E_ext : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAH : rAct.DisjointWires rHeld)
    (hAW : rAct.DisjointWires rW) (hAnW : rAnc.DisjointWires rW)
    (hHW : rHeld.DisjointWires rW) :
    let B_anc := Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)
    rW.basisOutcomeProjector 0 *
        (B_anc.1 * (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0)) =
      B_anc.1 * (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0) := by
  intro B_anc
  let rDA := rAct.concat rAnc hAA
  have hAAW : rDA.DisjointWires rW := disjointWires_concat_left hAA hAW hAnW
  have hAHW : (rAct.concat rHeld hAH).DisjointWires rW :=
    disjointWires_concat_left hAH hAW hHW
  have hCB : rW.basisOutcomeProjector 0 * B_anc.1 = B_anc.1 * rW.basisOutcomeProjector 0 := by
    dsimp only [B_anc, Bell18TeleportCore.uBellSlot]
    have h1 := ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rAct.concat rHeld hAH))
      rW hAHW (Bell18TeleportCore.uLensWrite (toSlotK18 L_anchor)).1 0).symm
    have h2 := (Bell18TeleportCore.cHadReg_comm_basisOutcomeProjector rHeld rW hHW 0).symm
    rw [Submonoid.coe_mul, QRegister.embedUnitary_val, ← Matrix.mul_assoc, h1,
        Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
  have hCDA := ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rDA)
    rW hAAW (E_anchorLoc E_ext) 0).symm
  unfold E_anchor
  have hGen : ∀ {R : Type} [Semigroup R] (pW B D pH : R),
      pW * B = B * pW → pW * D = D * pW → pW * pW = pW →
      pW * (B * ((D * pW) * pH)) = B * ((D * pW) * pH) := by
    intro R _ pW B D pH h1 h2 h3
    rw [← mul_assoc pW B, h1, mul_assoc B pW, ← mul_assoc pW (D * pW),
        ← mul_assoc pW D, h2, mul_assoc D pW pW, h3]
  exact hGen _ _ _ _ hCB hCDA (rW.basisOutcomeProjector_mul_self 0)

private theorem uAnchorLensSwap_intertwine_E0_aux {mW n : ℕ}
    {E_ext : Operator (2 ^ kFull80)}
    (rAct : QRegister kFull80 n) (rAnc : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAW : rAct.DisjointWires rW)
    (hAnW : rAnc.DisjointWires rW)
    (hBE : (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 * E_ext =
      E_ext * (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1) :
    ((rAct.concat rAnc hAA).embedUnitary uAnchorLensSwap).1 *
      (rAct.embedMatrix E_ext *
        (rAnc.basisOutcomeProjector 0 * rW.basisOutcomeProjector 0)) =
    E_anchor E_ext rAct rAnc rW hAA *
      (rAct.concat rAnc hAA).embedMatrix
        (sData80.embedUnitary
          (rCoreFull.embedUnitary (uBarrelFast (le_refl 80)))).1 := by
  let rDA := rAct.concat rAnc hAA
  have hAAW : rDA.DisjointWires rW := disjointWires_concat_left hAA hAW hAnW
  have hInitBase : rDA.embedMatrix (sData80.embedMatrix E_ext * P_anc0) *
        rW.basisOutcomeProjector 0 =
      rAct.embedMatrix E_ext *
        (rAnc.basisOutcomeProjector 0 * rW.basisOutcomeProjector 0) := by
    unfold P_anc0
    rw [rDA.embedMatrix_mul, ← QRegister.embedMatrix_compose, ccData,
        QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose,
        ccMeas, ← QRegister.basisOutcomeProjector, Matrix.mul_assoc]
  have hS0 := embed_intertwine_op_fast hAAW (uAnchorLensSwap_mul_data_P_anc0 hBE)
  have hEA : rDA.embedMatrix (E_anchorLoc E_ext) * rW.basisOutcomeProjector 0 =
      E_anchor E_ext rAct rAnc rW hAA := by unfold E_anchor; rfl
  rwa [hInitBase, uBarrelFastAct_eq_embedData_rCoreFull, hEA] at hS0

set_option exponentiation.threshold 256
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true

theorem dSingleBarrel6StepBell18Fast_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ} [NeZero (2 ^ n)]
    (hm143 : 143 ≤ mW) (E_ext : Operator (2 ^ kFull80))
    {U_A U_B : Unitary (2 ^ kFull80)} {V_A V_B : Operator (2 ^ kFull80)}
    {dStageA dStageB : DynamicCircuit Var n}
    (v : Var) (rAct : QRegister kFull80 n) (rAnc rHeld : QRegister 18 n) (rW : QRegister mW n)
    (hAA : rAct.DisjointWires rAnc) (hAH : rAct.DisjointWires rHeld)
    (hAW : rAct.DisjointWires rW) (hAnH : rAnc.DisjointWires rHeld)
    (hAnW : rAnc.DisjointWires rW) (hHW : rHeld.DisjointWires rW)
    (hBE : (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 * E_ext =
      E_ext * (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1)
    (hP1E : (rSegFull.embedUnitary uPass1InnerSeg).1 * E_ext =
      E_ext * (rSegFull.embedUnitary uPass1InnerSeg).1)
    (hP3E : (rSegFull.embedUnitary uPass3InnerSeg).1 * E_ext =
      E_ext * (rSegFull.embedUnitary uPass3InnerSeg).1)
    (hAE : U_A.1 * E_ext = E_ext * V_A)
    (hBStE : U_B.1 * E_ext = E_ext * V_B)
    (hToffA : dStageA.count TOFF = 0) (hToffB : dStageB.count TOFF = 0)
    (pA : RealizesOnProj
      ((Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)).1 *
        (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0))
      ((rAct.concat rAnc hAA).embedUnitary (uAnchorFrame U_A))
      dStageA)
    (pB : RealizesOnProj
      ((Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)).1 *
        (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0))
      ((rAct.concat rAnc hAA).embedUnitary (uAnchorFrame U_B))
      dStageB) :
    RealizesOnProj
      (rAct.embedMatrix E_ext *
        (rAnc.basisOutcomeProjector 0 *
          (rHeld.basisOutcomeProjector 0 * rW.basisOutcomeProjector 0)))
      (rAct.embedUnitary (uSingleBarrelFolded6Full U_A U_B))
      (dSingleBarrel6StepBell18Fast hm143 v rAct rAnc rHeld rW
        hAA hAW hAnH hAnW dStageA dStageB) := by
  let rDA := rAct.concat rAnc hAA
  let B_anc := Bell18TeleportCore.uBellSlot rAct rHeld hAH (toSlotK18 L_anchor)
  let S_anc := rDA.embedUnitary uAnchorLensSwap
  let E0 := rAct.embedMatrix E_ext *
    (rAnc.basisOutcomeProjector 0 *
      (rHeld.basisOutcomeProjector 0 * rW.basisOutcomeProjector 0))
  let E_bell := B_anc.1 * (E_anchor E_ext rAct rAnc rW hAA * rHeld.basisOutcomeProjector 0)
  let U2 := rDA.embedUnitary (uAnchorFrame (rSegFull.embedUnitary uPass1InnerSeg))
  let U3 := rDA.embedUnitary (uAnchorFrame U_A)
  let U4 := rDA.embedUnitary (uAnchorFrame U_B)
  let U5 := rDA.embedUnitary (uAnchorFrame (rSegFull.embedUnitary uPass3InnerSeg))
  have hAAW : rDA.DisjointWires rW := disjointWires_concat_left hAA hAW hAnW
  have hDAH : rDA.DisjointWires rHeld := disjointWires_concat_left hAA hAH hAnH
  have hI1 : (B_anc * S_anc).1 * E0 =
      E_bell * rDA.embedMatrix (rCoreFull.embedUnitary (uBarrelFast (le_refl 80)) |>
        sData80.embedUnitary).1 := by
    have hS0 := uAnchorLensSwap_intertwine_E0_aux rAct rAnc rW hAA hAW hAnW hBE
    have hHW0 := proj0_comm_3c rHeld rW hHW
    have hCH := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rDA) rHeld hDAH
      (sData80.embedUnitary (rCoreFull.embedUnitary (uBarrelFast (le_refl 80)))).1 0
    dsimp only [E0, E_bell, S_anc]
    rw [Submonoid.coe_mul]
    have hGen1 : ∀ {R : Type} [Semigroup R] (B S E pA pH pW EA V : R),
        pH * pW = pW * pH → S * (E * (pA * pW)) = EA * V → V * pH = pH * V →
        (B * S) * (E * (pA * (pH * pW))) = (B * (EA * pH)) * V := by
      intro R _ B S E pA pH pW EA V h1 h2 h3
      rw [h1, ← mul_assoc pA pW pH, ← mul_assoc E (pA * pW) pH,
          mul_assoc B S, ← mul_assoc S _ pH, h2, mul_assoc EA V pH, h3]
      simp only [mul_assoc]
    exact hGen1 (R := Operator (2 ^ n)) _ _ _ _ _ _ _ _ hHW0 hS0 hCH
  have hAbsW : rW.basisOutcomeProjector 0 * E_bell = E_bell :=
    proj0_rW_mul_E_bellAnchor E_ext rAct rAnc rHeld rW hAA hAH hAW hAnW hHW
  have hR2 : RealizesOnProj E_bell U2
      (dPass1Anchor (by omega : 130 ≤ mW) v rAct rAnc rW hAA hAW hAnW) := by
    have h0 := dPass1Anchor_realizesOnProj (by omega : 130 ≤ mW) 1 v rAct rAnc rW hAA hAW hAnW
    rw [rDA.embedMatrix_one, Matrix.one_mul] at h0
    have hM := realizesOnProj_mul_right E_bell h0
    rwa [hAbsW] at hM
  have hR5 : RealizesOnProj E_bell U5
      (dPass3Anchor (by omega : 13 ≤ mW) v rAct rAnc rW hAA hAW hAnW) := by
    have h0 := dPass3Anchor_realizesOnProj (by omega : 13 ≤ mW) 1 v rAct rAnc rW hAA hAW hAnW
    rw [rDA.embedMatrix_one, Matrix.one_mul] at h0
    have hM := realizesOnProj_mul_right E_bell h0
    rwa [hAbsW] at hM
  have hTot : rAct.embedUnitary (uSingleBarrelFolded6Full U_A U_B) =
      (S_anc * star B_anc) * (U5 * (U4 * (U3 * (U2 * (B_anc * S_anc))))) := by
    have c2 := uAnchorFrame_comm_uBellSlot rAct rAnc rHeld hAA hAH hAnH
      (rSegFull.embedUnitary uPass1InnerSeg)
    have c3 := uAnchorFrame_comm_uBellSlot rAct rAnc rHeld hAA hAH hAnH U_A
    have c4 := uAnchorFrame_comm_uBellSlot rAct rAnc rHeld hAA hAH hAnH U_B
    have c5 := uAnchorFrame_comm_uBellSlot rAct rAnc rHeld hAA hAH hAnH
      (rSegFull.embedUnitary uPass3InnerSeg)
    have hGenM : ∀ {G : Type} [Monoid G] (S Binv B u5 u4 u3 u2 : G),
        Binv * B = 1 → u2 * B = B * u2 → u3 * B = B * u3 →
        u4 * B = B * u4 → u5 * B = B * u5 →
        S * (u5 * (u4 * (u3 * (u2 * S)))) =
          (S * Binv) * (u5 * (u4 * (u3 * (u2 * (B * S))))) := by
      intro G _ S Binv B u5 u4 u3 u2 hInv hc2 hc3 hc4 hc5
      have hC : u5 * (u4 * (u3 * (u2 * (B * S)))) =
          B * (u5 * (u4 * (u3 * (u2 * S)))) := by
        rw [← mul_assoc u2 B S, hc2, mul_assoc B u2 S,
            ← mul_assoc u3 B, hc3, mul_assoc B u3,
            ← mul_assoc u4 B, hc4, mul_assoc B u4,
            ← mul_assoc u5 B, hc5, mul_assoc B u5]
      rw [hC, mul_assoc S Binv, ← mul_assoc Binv B, hInv, one_mul]
    rw [← hGenM S_anc (star B_anc) B_anc U5 U4 U3 U2
      (Unitary.star_mul_self B_anc) c2 c3 c4 c5]
    dsimp only [S_anc, U5, U4, U3, U2]
    rw [← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul,
        ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul,
        ← QRegister.embedUnitary_mul, uAnchorLensSwap_conj_uAnchorFrame_four U_A U_B,
        ← QRegister.embedUnitary_compose, ccData]
  exact (seq6Bell18_realizesOnProj_fused hTot hI1
    (uAnchorFrame_intertwines_E_bellAnchor rAct rAnc rHeld rW hAA hAH hAW hAnH hAnW
      (uAnchorFrame_intertwines_E_anchorLoc hP1E))
    (uAnchorFrame_intertwines_E_bellAnchor rAct rAnc rHeld rW hAA hAH hAW hAnH hAnW
      (uAnchorFrame_intertwines_E_anchorLoc hAE))
    (uAnchorFrame_intertwines_E_bellAnchor rAct rAnc rHeld rW hAA hAH hAW hAnH hAnW
      (uAnchorFrame_intertwines_E_anchorLoc hBStE))
    (uAnchorFrame_intertwines_E_bellAnchor rAct rAnc rHeld rW hAA hAH hAW hAnH hAnW
      (uAnchorFrame_intertwines_E_anchorLoc hP3E))
    (dPreBell18AnchorFast_realizesOnProj hm143 E_ext v rAct rAnc rHeld rW
      hAA hAH hAW hAnH hAnW hHW)
    hR2 pA pB hR5
    (dPostBell18AnchorFast_realizesOnProj hm143 E_ext v rAct rAnc rHeld rW
      hAA hAH hAW hAnH hAnW hHW)
    ⟨(dPreBell18AnchorFast_counts hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW).1,
     dPass1Anchor_count_toff (by omega) v rAct rAnc rW hAA hAW hAnW,
     hToffA, hToffB,
     dPass3Anchor_count_toff (by omega) v rAct rAnc rW hAA hAW hAnW,
     dPostBell18AnchorFast_count_toff (le_refl 80) hm143 v rAct rCoreFull rAnc rHeld rW
       hAW hAnH⟩
    (dPreBell18AnchorFast_counts hm143 v rAct rAnc rHeld rW hAA hAW hAnH hAnW).2
    (le_refl _) (le_refl _) (le_refl _) (le_refl _)
    (dPostBell18AnchorFast_count_t_le (le_refl 80) hm143 v rAct rCoreFull rAnc rHeld rW
      hAW hAnH)).2.2

/-- `{mWork}`-polymorphic Bell-18 `6`-step barrel wrapper (`179 ≤ mWork`, i.e.
`143 ≤ (mWork - 18) - 18`, `≤ 17,696 + 724 + tA + tB` `T`, `0 TOFF`). -/
noncomputable def dSingleBarrel6StepBell18MWork {Var : Type} {mWork n : ℕ}
    (hm179 : 179 ≤ mWork)
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork)
    (dStageA dStageB : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let rAnc := rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork
  let rRem1 := rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
  let rHeld := rAnchor18OfMWork (by omega : 18 ≤ mWork - 18) rRem1
  let rW := rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
  have hAncRem1 := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
  dSingleBarrel6StepBell18Fast (by omega : 143 ≤ (mWork - 18) - 18) v rAct rAnc rHeld rW
    (hDisj.compose_right _) ((hDisj.compose_right _).compose_right _)
    (hAncRem1.compose_right _) (hAncRem1.compose_right _)
    dStageA dStageB

theorem count_dSingleBarrel6StepBell18MWork_toff {Var : Type} {mWork n : ℕ}
    (hm179 : 179 ≤ mWork)
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork)
    {dStageA dStageB : DynamicCircuit Var n}
    (hToffA : dStageA.count TOFF = 0) (hToffB : dStageB.count TOFF = 0) :
    (dSingleBarrel6StepBell18MWork hm179 v rAct rWork hDisj dStageA dStageB).count TOFF = 0 :=
  count_dSingleBarrel6StepBell18Fast_toff (by omega) v rAct _ _ _ _ _ _ _ hToffA hToffB

theorem count_dSingleBarrel6StepBell18MWork_t_le_split {Var : Type} {mWork tA tB n : ℕ}
    (hm179 : 179 ≤ mWork)
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork)
    {dStageA dStageB : DynamicCircuit Var n}
    (hTA : dStageA.count T ≤ tA) (hTB : dStageB.count T ≤ tB) :
    (dSingleBarrel6StepBell18MWork hm179 v rAct rWork hDisj dStageA dStageB).count T ≤
      17260 + 724 + tA + tB :=
  count_dSingleBarrel6StepBell18Fast_t_le (by omega) v rAct _ _ _ _ _ _ _ hTA hTB

theorem dSingleBarrel6StepBell18MWork_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWork n : ℕ} [NeZero (2 ^ n)]
    (hm179 : 179 ≤ mWork)
    (E_ext : Operator (2 ^ kFull80))
    {U_A U_B : Unitary (2 ^ kFull80)} {V_A V_B : Operator (2 ^ kFull80)}
    {dStageA dStageB : DynamicCircuit Var n}
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork)
    (hBE : (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1 * E_ext =
      E_ext * (rCoreFull.embedUnitary (uBarrelFast (le_refl 80))).1)
    (hP1E : (rSegFull.embedUnitary uPass1InnerSeg).1 * E_ext =
      E_ext * (rSegFull.embedUnitary uPass1InnerSeg).1)
    (hP3E : (rSegFull.embedUnitary uPass3InnerSeg).1 * E_ext =
      E_ext * (rSegFull.embedUnitary uPass3InnerSeg).1)
    (hAE : U_A.1 * E_ext = E_ext * V_A)
    (hBStE : U_B.1 * E_ext = E_ext * V_B)
    (hToffA : dStageA.count TOFF = 0) (hToffB : dStageB.count TOFF = 0)
    (pA : RealizesOnProj
      ((Bell18TeleportCore.uBellSlot rAct
          (rAnchor18OfMWork (by omega : 18 ≤ mWork - 18)
            (rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork))
          ((hDisj.compose_right _).compose_right _) (toSlotK18 L_anchor)).1 *
        (E_anchor E_ext rAct (rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork)
          (rWorkRemOfMWork (by omega : 18 ≤ mWork - 18)
            (rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork))
          (hDisj.compose_right _) *
          (rAnchor18OfMWork (by omega : 18 ≤ mWork - 18)
            (rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork)).basisOutcomeProjector 0))
      ((rAct.concat (rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork)
          (hDisj.compose_right _)).embedUnitary (uAnchorFrame U_A))
      dStageA)
    (pB : RealizesOnProj
      ((Bell18TeleportCore.uBellSlot rAct
          (rAnchor18OfMWork (by omega : 18 ≤ mWork - 18)
            (rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork))
          ((hDisj.compose_right _).compose_right _) (toSlotK18 L_anchor)).1 *
        (E_anchor E_ext rAct (rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork)
          (rWorkRemOfMWork (by omega : 18 ≤ mWork - 18)
            (rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork))
          (hDisj.compose_right _) *
          (rAnchor18OfMWork (by omega : 18 ≤ mWork - 18)
            (rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork)).basisOutcomeProjector 0))
      ((rAct.concat (rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork)
          (hDisj.compose_right _)).embedUnitary (uAnchorFrame U_B))
      dStageB) :
    RealizesOnProj
      (rAct.embedMatrix E_ext * rWork.basisOutcomeProjector 0)
      (rAct.embedUnitary (uSingleBarrelFolded6Full U_A U_B))
      (dSingleBarrel6StepBell18MWork hm179 v rAct rWork hDisj dStageA dStageB) := by
  let rAnc := rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork
  let rRem1 := rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
  let rHeld := rAnchor18OfMWork (by omega : 18 ≤ mWork - 18) rRem1
  let rW := rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
  have hAncRem1 := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
  have hHW := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
  have hProj : rAct.embedMatrix E_ext *
        (rAnc.basisOutcomeProjector 0 *
          (rHeld.basisOutcomeProjector 0 * rW.basisOutcomeProjector 0)) =
      rAct.embedMatrix E_ext * rWork.basisOutcomeProjector 0 := by
    dsimp only [rAnc, rHeld, rW, rRem1]
    rw [rAnchor18OfMWork_proj0_mul_rWorkRemOfMWork_proj0 (by omega : 18 ≤ mWork - 18)
          (rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork),
        rAnchor18OfMWork_proj0_mul_rWorkRemOfMWork_proj0 (by omega : 18 ≤ mWork) rWork]
  have hFast := @dSingleBarrel6StepBell18Fast_realizesOnProj Var _ _ ((mWork - 18) - 18) n _
    (by omega) E_ext U_A U_B V_A V_B dStageA dStageB v rAct rAnc rHeld rW
    (hDisj.compose_right _) ((hDisj.compose_right _).compose_right _)
    ((hDisj.compose_right _).compose_right _)
    (hAncRem1.compose_right _) (hAncRem1.compose_right _) hHW
    hBE hP1E hP3E hAE hBStE hToffA hToffB pA pB
  rwa [hProj] at hFast

attribute [irreducible] dPostBell18AnchorFast
attribute [irreducible]
  dPreBell18AnchorFast
  dFusedBell18OpenAnchorCtrlOneWire
  dFusedBell18OpenAnchorCatOneWire
  dSingleBarrel6StepBell18Fast
  dSingleBarrel6StepBell18MWork

end Part3C_Bell18FusedBundle
end Part3_Bell18Sites2And3

end StageBOneWireOpenAdd0
set_option exponentiation.threshold 256
end LocalStageBOneWireOpenAdd0

end QuantumComputation.Specs.StoppingPowerSolution
public section

namespace QuantumComputation.Specs.StoppingPowerSolution
section ExportStageBOneWireOpenAdd0
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 4200

attribute [local semireducible]
  SpecsAux.SpecMirror.systemQubits
  PosSlots24BranchConcrete.posCoreWires

namespace StageBOneWireOpenAdd0

local instance (priority := 1000000) instNeZero_G6OpenPub (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

local instance (priority := 1000000) instGroupUnitaryFast_G6OpenPub (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instSemigroupUnitaryFast_G6OpenPub (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  (instGroupUnitaryFast_G6OpenPub D).toSemigroup

open SpecsAux
open Operator QProg Matrix Real
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators

open FullSysCatSegmentBridge (disjointWires_concat_left)
open HoistBorrow42ProjBridge (RealizesOnProj)
open InterWalkRSum42Hoist (kFull80 rCoreFull)
open Barrel3PassSelectStitch (hm6_80)
open FusedPreDiagFromTwist288 (uPreDiagCliffordCore)
open HeldStreamFoldedPass123Bridge (E_rawCtrl3Ext E_rawSegExt)
open StageAConjHAndStreamBridge (uStageARawFull)
open BarrelPass2AndHeld3PassSelectStitch
  (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt
   uPass1InnerSeg_and_uPass3InnerSeg_comm_rawStream_ctrl3_idle12
   uSingleBarrelFolded6Full uPass1InnerSeg uPass3InnerSeg)
open SingleBarrel8StepClean (commutesWithReg_rPGIdleOrig11_of_12)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (E_anchorLoc E_anchor P_slot0_mul_E_anchorLoc uAnchorFrame uAnchorFrame_mul
   uSlot0MeasSwap uBarrelFastAct uSlot0MeasSwap_mul_self uBarrelFastAct_mul_self
   uAnchorFrame_intertwines_E_anchorLoc embedIntertwineOp
   uPreDiagCliffordCore_comm_E_rawCtrl3Ext_and_E_rawSegExt
   uBarrelFast_comm_E_rawCtrl3Ext_and_E_rawSegExt
   uWrapPreDiagCliffordFull dWrapPreDiagCliffordAnchor
   dWrapPreDiagCliffordAnchor_count_toff dWrapPreDiagCliffordAnchor_count_t
   dWrapPreDiagCliffordAnchor_realizesOnProj realizesOnProj_congr_unitary)
open TruncWAsymHeldTwShell (FoldedPass123CircuitSpec_mWork)
open BoothOpt_FastAnchorOuterAndStageBShave
  (rAnchor18OfMWork rWorkRemOfMWork rAnchor18OfMWork_disj_rWorkRemOfMWork)
open ChiralDStageABridge (stageAAnchorInputBorrow48054_179_11)
open LocalStageBFastInnerPartnerShift
  (E_anchor_ctrl11_eq E_anchor_cat11_eq)
open LocalStageBPartnerTrueSwapStream218Closure
  (uStageBFull uStageBFull_mul_E_rawStream42_eq commutesWithReg_rCtrl3InSeg_uStageBSeg
   commutesWithReg_rPGIdleOrig_uStageBSeg)
open SlimStageBAnchorInput (slimFoldedBundle179_Borrow48054)
open SlimStageBCircuits (mkStageBAnchorInput179_11_boothOpt)
open P1_OpenAnchorAdd0TwoLoad
  (uJunctionRawFull uJunctionAncFull18 uAnchorFrame_one mul_intertwine_same
   uWrapPreDiagCliffordFull_mul uSingleBarrelFolded6Full_mul_one)
open StageBOneWireBridge
  (kOneWire_le_18 stageBOneWireKBoothOptAnchorT stageBOneWireBoothOptAnchorT)



attribute [local irreducible]
  SpecsAux.SpecMirror.systemQubits
  PosSlots24BranchConcrete.posCoreWires
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option genSizeOf false

open BoothOpt_Anchor218CachedTrueSwapOuter (L_anchor)
open Bell18StageABridge (StageABell18Witness stageABell18Witness)

theorem bell18_disj_rAnchor18 {k mWork n : ℕ} {rA : QRegister k n}
    {rWork : QRegister mWork n} (hD : rA.DisjointWires rWork) (hm18 : 18 ≤ mWork) :
    rA.DisjointWires (rAnchor18OfMWork hm18 rWork) := by
  unfold rAnchor18OfMWork; exact hD.compose_right _

theorem bell18_disj_rWorkRem {k mWork n : ℕ} {rA : QRegister k n}
    {rWork : QRegister mWork n} (hD : rA.DisjointWires rWork) (hm18 : 18 ≤ mWork) :
    rA.DisjointWires (rWorkRemOfMWork hm18 rWork) := by
  unfold rWorkRemOfMWork; exact hD.compose_right _

/-- `{mWork}`-polymorphic (`197 ≤ mWork`) Bell-18 open-seam 1-wire
`FoldedPass123CircuitSpec_mWork` parameterized by `stA : StageABell18Witness`
(`17,696 + 724 + 47,929 + stageB`, `0 TOFF`), sharing the exact `uFoldedCtrlFull`
and `uFoldedCatFull` unitaries of `slimFoldedBundle179_Borrow48054`. -/
noncomputable def foldedCircuitSpec_Bell18OpenQft_OneWire_mWork_ofStageA
    (stA : StageABell18Witness) {mWork : ℕ} (hm197 : 197 ≤ mWork)
    (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27) :
    FoldedPass123CircuitSpec_mWork mWork
      (slimFoldedBundle179_Borrow48054 B hB6 hB27).uFoldedCtrlFull
      (slimFoldedBundle179_Borrow48054 B hB6 hB27).uFoldedCatFull
      (fun j ↦ 17260 + 724 + 47493 + stageBOneWireBoothOptAnchorT (B j) (mWork - 56))
      (fun j ↦ 17260 + 724 + 47493 + stageBOneWireBoothOptAnchorT (B j) (mWork - 53)) where
  dFoldedCtrl j _ {_} {_} v rAct rWork hD :=
    let rAnc := rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork
    let rRem1 := rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    let rHeld := rAnchor18OfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let rW := rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let hAncRem1 := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    dSingleBarrel6StepBell18MWork (by omega : 179 ≤ mWork) v rAct rWork hD
      (dFusedBell18OpenAnchorCtrlOneWire stA (by omega : 161 ≤ (mWork - 18) - 18)
        (B j) (hB6 j) (hB27 j) v rAct rAnc rW rHeld
        (bell18_disj_rAnchor18 hD _) (bell18_disj_rWorkRem (bell18_disj_rWorkRem hD _) _)
        (bell18_disj_rWorkRem hAncRem1 _))
      DynamicCircuit.identity
  dFoldedCat j _ {_} {_} v rAct rWork hD :=
    let rAnc := rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork
    let rRem1 := rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    let rHeld := rAnchor18OfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let rW := rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let hAncRem1 := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    dSingleBarrel6StepBell18MWork (by omega : 179 ≤ mWork) v rAct rWork hD
      (dFusedBell18OpenAnchorCatOneWire stA (by omega : 161 ≤ (mWork - 18) - 18)
        (B j) (hB6 j) (hB27 j) v rAct rAnc rW rHeld
        (bell18_disj_rAnchor18 hD _) (bell18_disj_rWorkRem (bell18_disj_rWorkRem hD _) _)
        (bell18_disj_rWorkRem hAncRem1 _))
      DynamicCircuit.identity
  hToffCtrl j _ {_} {_} v rAct rWork hD := by
    exact count_dSingleBarrel6StepBell18MWork_toff (by omega) v rAct rWork hD
      (dFusedBell18OpenAnchorCtrlOneWire_count_toff stA (by omega)
        (B j) (hB6 j) (hB27 j) v _ _ _ _ _ _ _) rfl
  hToffCat j _ {_} {_} v rAct rWork hD := by
    exact count_dSingleBarrel6StepBell18MWork_toff (by omega) v rAct rWork hD
      (dFusedBell18OpenAnchorCatOneWire_count_toff stA (by omega)
        (B j) (hB6 j) (hB27 j) v _ _ _ _ _ _ _) rfl
  hTCtrl j _ {_} {_} v rAct rWork hD := by
    let rAnc := rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork
    let rRem1 := rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    let rHeld := rAnchor18OfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let rW := rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let hAncRem1 := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    have h := count_dSingleBarrel6StepBell18MWork_t_le_split (by omega : 179 ≤ mWork)
      v rAct rWork hD
      (dFusedBell18OpenAnchorCtrlOneWire_count_t_le stA
        (by omega : 161 ≤ (mWork - 18) - 18) (B j) (hB6 j) (hB27 j) v rAct rAnc rW rHeld
        (bell18_disj_rAnchor18 hD _) (bell18_disj_rWorkRem (bell18_disj_rWorkRem hD _) _)
        (bell18_disj_rWorkRem hAncRem1 _))
      (by rfl : (DynamicCircuit.identity : DynamicCircuit _ _).count T ≤ 0)
    have hSub : ((mWork - 18) - 18) - 20 = mWork - 56 := by omega
    rw [hSub] at h
    exact Nat.le_trans h (by omega)
  hTCat j _ {_} {_} v rAct rWork hD := by
    let rAnc := rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork
    let rRem1 := rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    let rHeld := rAnchor18OfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let rW := rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let hAncRem1 := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    have h := count_dSingleBarrel6StepBell18MWork_t_le_split (by omega : 179 ≤ mWork)
      v rAct rWork hD
      (dFusedBell18OpenAnchorCatOneWire_count_t_le stA
        (by omega : 161 ≤ (mWork - 18) - 18) (B j) (hB6 j) (hB27 j) v rAct rAnc rW rHeld
        (bell18_disj_rAnchor18 hD _) (bell18_disj_rWorkRem (bell18_disj_rWorkRem hD _) _)
        (bell18_disj_rWorkRem hAncRem1 _))
      (by rfl : (DynamicCircuit.identity : DynamicCircuit _ _).count T ≤ 0)
    have hSub : ((mWork - 18) - 18) - 17 = mWork - 53 := by omega
    rw [hSub] at h
    exact Nat.le_trans h (by omega)
  hRealRawCtrl j _ {Var} [_] [_] {n} [_] v rAct rWork hD := by
    let stA0 := stageAAnchorInputBorrow48054_179_11
    let stB := mkStageBAnchorInput179_11_boothOpt B hB6 hB27
    let rAnc := rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork
    let rRem1 := rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    let rHeld := rAnchor18OfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let rW := rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
    have hAncRem1 := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    have hHW := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
    obtain ⟨⟨hP1Raw, hP1C, hP1I12⟩, ⟨hP3Raw, hP3C, hP3I12⟩⟩ :=
      uPass1InnerSeg_and_uPass3InnerSeg_comm_rawStream_ctrl3_idle12
    have hP1Ext := (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      _ _ hP1Raw hP1C (commutesWithReg_rPGIdleOrig11_of_12 hP1I12)).1
    have hP3Ext := (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      _ _ hP3Raw hP3C (commutesWithReg_rPGIdleOrig11_of_12 hP3I12)).1
    have hAExt := (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      (stA0.uStageACtrlFull j).1 (stA0.uStageASeg j)
      (stA0.hACtrlRaw j) (stA0.hACtrl3 j) (stA0.hAIdle11 j)).1
    have hBExt := (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      (stB.uStageBCtrlFull j).1 (stB.uStageBSeg j)
      (stB.hBCtrlRaw j) (stB.hBCtrl3 j) (stB.hBIdle11 j)).1
    have hABExt : (stB.uStageBCtrlFull j * stA0.uStageACtrlFull j).1 *
        E_rawCtrl3Ext 11 (by decide) = _ :=
      mul_intertwine_same hBExt hAExt
    have hOneExt : (1 : Unitary (2 ^ kFull80)).1 * E_rawCtrl3Ext 11 (by decide) =
        E_rawCtrl3Ext 11 (by decide) * 1 := by
      rw [OneMemClass.coe_one, Matrix.one_mul, Matrix.mul_one]
    have pA : RealizesOnProj
        ((Bell18TeleportCore.uBellSlot rAct rHeld
            ((hD.compose_right _).compose_right _) (toSlotK18 L_anchor)).1 *
          (E_anchor (E_rawCtrl3Ext 11 (by decide)) rAct rAnc rW
            (hD.compose_right _) * rHeld.basisOutcomeProjector 0))
        ((rAct.concat rAnc (hD.compose_right _)).embedUnitary
          (uAnchorFrame (stB.uStageBCtrlFull j * stA0.uStageACtrlFull j)))
        (dFusedBell18OpenAnchorCtrlOneWire stA (by omega : 161 ≤ (mWork - 18) - 18)
          (B j) (hB6 j) (hB27 j) v rAct rAnc rW rHeld
          (bell18_disj_rAnchor18 hD _) (bell18_disj_rWorkRem (bell18_disj_rWorkRem hD _) _)
          (bell18_disj_rWorkRem hAncRem1 _)) := by
      have h0 := dFusedBell18OpenAnchorCtrlOneWire_realizesOnProj stA
        (by omega : 161 ≤ (mWork - 18) - 18) (B j) (hB6 j) (hB27 j) v rAct rAnc rW rHeld
        (bell18_disj_rAnchor18 hD _) (bell18_disj_rWorkRem (bell18_disj_rWorkRem hD _) _)
        (bell18_disj_rWorkRem hAncRem1 _) ((hD.compose_right _).compose_right _)
        (hAncRem1.compose_right _) (QRegExt.disjointWires_symm hHW)
      rwa [uWrapPreDiagCliffordFull_mul] at h0
    have pB : RealizesOnProj
        ((Bell18TeleportCore.uBellSlot rAct rHeld
            ((hD.compose_right _).compose_right _) (toSlotK18 L_anchor)).1 *
          (E_anchor (E_rawCtrl3Ext 11 (by decide)) rAct rAnc rW
            (hD.compose_right _) * rHeld.basisOutcomeProjector 0))
        ((rAct.concat rAnc (hD.compose_right _)).embedUnitary
          (uAnchorFrame (1 : Unitary (2 ^ kFull80))))
        (DynamicCircuit.identity : DynamicCircuit Var n) := by
      rw [uAnchorFrame_one, QRegister.embedUnitary_one]
      exact RealizesOnProj.identity _
    change RealizesOnProj
      (rAct.embedMatrix (E_rawCtrl3Ext 11 (by decide)) * rWork.basisOutcomeProjector 0)
      (rAct.embedUnitary
        (uSingleBarrelFolded6Full (stA0.uStageACtrlFull j) (stB.uStageBCtrlFull j))) _
    rw [← uSingleBarrelFolded6Full_mul_one (stA0.uStageACtrlFull j) (stB.uStageBCtrlFull j)]
    exact dSingleBarrel6StepBell18MWork_realizesOnProj (by omega) (E_rawCtrl3Ext 11 (by decide))
      v rAct rWork hD
      (uBarrelFast_comm_E_rawCtrl3Ext_and_E_rawSegExt (by decide : 11 ≤ 48)).1
      hP1Ext hP3Ext hABExt hOneExt
      (dFusedBell18OpenAnchorCtrlOneWire_count_toff stA (by omega)
        (B j) (hB6 j) (hB27 j) v _ _ _ _ _ _ _) rfl
      pA pB
  hRealRawCat j _ {Var} [_] [_] {n} [_] v rAct rWork hD := by
    let stA0 := stageAAnchorInputBorrow48054_179_11
    let stB := mkStageBAnchorInput179_11_boothOpt B hB6 hB27
    let rAnc := rAnchor18OfMWork (by omega : 18 ≤ mWork) rWork
    let rRem1 := rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    let rHeld := rAnchor18OfMWork (by omega : 18 ≤ mWork - 18) rRem1
    let rW := rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
    have hAncRem1 := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork) rWork
    have hHW := rAnchor18OfMWork_disj_rWorkRemOfMWork (by omega : 18 ≤ mWork - 18) rRem1
    obtain ⟨⟨hP1Raw, hP1C, hP1I12⟩, ⟨hP3Raw, hP3C, hP3I12⟩⟩ :=
      uPass1InnerSeg_and_uPass3InnerSeg_comm_rawStream_ctrl3_idle12
    have hP1Ext := (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      _ _ hP1Raw hP1C (commutesWithReg_rPGIdleOrig11_of_12 hP1I12)).2
    have hP3Ext := (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      _ _ hP3Raw hP3C (commutesWithReg_rPGIdleOrig11_of_12 hP3I12)).2
    have hAExt := (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      (stA0.uStageACatFull j).1 (stA0.uStageASeg j)
      (stA0.hACatRaw j) (stA0.hACtrl3 j) (stA0.hAIdle11 j)).2
    have hBExt := (rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt (by decide : 11 ≤ 48)
      (stB.uStageBCatFull j).1 (stB.uStageBSeg j)
      (stB.hBCatRaw j) (stB.hBCtrl3 j) (stB.hBIdle11 j)).2
    have hABExt : (stB.uStageBCatFull j * stA0.uStageACatFull j).1 *
        E_rawSegExt 11 (by decide) = _ :=
      mul_intertwine_same hBExt hAExt
    have hOneExt : (1 : Unitary (2 ^ kFull80)).1 * E_rawSegExt 11 (by decide) =
        E_rawSegExt 11 (by decide) * 1 := by
      rw [OneMemClass.coe_one, Matrix.one_mul, Matrix.mul_one]
    have pA : RealizesOnProj
        ((Bell18TeleportCore.uBellSlot rAct rHeld
            ((hD.compose_right _).compose_right _) (toSlotK18 L_anchor)).1 *
          (E_anchor (E_rawSegExt 11 (by decide)) rAct rAnc rW
            (hD.compose_right _) * rHeld.basisOutcomeProjector 0))
        ((rAct.concat rAnc (hD.compose_right _)).embedUnitary
          (uAnchorFrame (stB.uStageBCatFull j * stA0.uStageACatFull j)))
        (dFusedBell18OpenAnchorCatOneWire stA (by omega : 161 ≤ (mWork - 18) - 18)
          (B j) (hB6 j) (hB27 j) v rAct rAnc rW rHeld
          (bell18_disj_rAnchor18 hD _) (bell18_disj_rWorkRem (bell18_disj_rWorkRem hD _) _)
          (bell18_disj_rWorkRem hAncRem1 _)) := by
      have h0 := dFusedBell18OpenAnchorCatOneWire_realizesOnProj stA
        (by omega : 161 ≤ (mWork - 18) - 18) (B j) (hB6 j) (hB27 j) v rAct rAnc rW rHeld
        (bell18_disj_rAnchor18 hD _) (bell18_disj_rWorkRem (bell18_disj_rWorkRem hD _) _)
        (bell18_disj_rWorkRem hAncRem1 _) ((hD.compose_right _).compose_right _)
        (hAncRem1.compose_right _) (QRegExt.disjointWires_symm hHW)
      rwa [uWrapPreDiagCliffordFull_mul] at h0
    have pB : RealizesOnProj
        ((Bell18TeleportCore.uBellSlot rAct rHeld
            ((hD.compose_right _).compose_right _) (toSlotK18 L_anchor)).1 *
          (E_anchor (E_rawSegExt 11 (by decide)) rAct rAnc rW
            (hD.compose_right _) * rHeld.basisOutcomeProjector 0))
        ((rAct.concat rAnc (hD.compose_right _)).embedUnitary
          (uAnchorFrame (1 : Unitary (2 ^ kFull80))))
        (DynamicCircuit.identity : DynamicCircuit Var n) := by
      rw [uAnchorFrame_one, QRegister.embedUnitary_one]
      exact RealizesOnProj.identity _
    change RealizesOnProj
      (rAct.embedMatrix (E_rawSegExt 11 (by decide)) * rWork.basisOutcomeProjector 0)
      (rAct.embedUnitary
        (uSingleBarrelFolded6Full (stA0.uStageACatFull j) (stB.uStageBCatFull j))) _
    rw [← uSingleBarrelFolded6Full_mul_one (stA0.uStageACatFull j) (stB.uStageBCatFull j)]
    exact dSingleBarrel6StepBell18MWork_realizesOnProj (by omega) (E_rawSegExt 11 (by decide))
      v rAct rWork hD
      (uBarrelFast_comm_E_rawCtrl3Ext_and_E_rawSegExt (by decide : 11 ≤ 48)).2
      hP1Ext hP3Ext hABExt hOneExt
      (dFusedBell18OpenAnchorCatOneWire_count_toff stA (by omega)
        (B j) (hB6 j) (hB27 j) v _ _ _ _ _ _ _) rfl
      pA pB

end StageBOneWireOpenAdd0
set_option exponentiation.threshold 256
end ExportStageBOneWireOpenAdd0
end QuantumComputation.Specs.StoppingPowerSolution
end

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
namespace Local
end Local
end QuantumComputation.Specs.StoppingPowerSolution
end
