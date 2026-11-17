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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.HadCut570Tail3D

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section SelectPass13Gen
local instance (priority := 1000000) instNeZeroTwoPow_SelectPass13Gen (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Hoisted `Pass 1` / `Pass 3` Parameterized `SELECT` Stitch (`SelectPass13Gen`)

Parameterized `SELECT` stitcher over `SelectCtrlStitch` and
`SelectExtStitch` for `mWork = 137`, `k_idle = 11`:
1. Parameterizes the `Pass 1` (`9,958 T`) and `Pass 3` (`8,934 T`) terms in both
   `dSelectCtrl` (`190w` `T4`-seam and `179w` `CTLeafSpec 179`) and `dSelectCat` (`196w`
   `rCoreSwapCtrl3PG3At 11` `T4`-seam, `193w` unswapped `T4`-seam, and `179w` `CTLeafSpec 179`).
2. Preserves `uSelectHoistGen` and `uSelectCatRawHoistGen` directly for
   `uMidHoistSegGen_comm_pCtrl3Zero` and `HoistedExtHkSelectSpec` bridges.
-/

public section

namespace SelectPass13Gen

section ConfigSelectPass13Gen

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

local instance (priority := 1000000) instLoc_SelectPass13Gen_1InstNeZeroTwoPowSelectPass1 (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped BigOperators
open SpecsAux SpecsAux.SpecMirror
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge
  (fullSysCoreWires fullSysBEWires fullSysRawAncWires coreElecBlock coreCosetB1Block
   coreElecCosetB1Block)
open OraAndPrepBundle (coreUnitaryToFullSys)
open NuclearTwistRealizes (uXor32Core)
open FusedPreDiagFromTwist288 (embed_bit5Flip654_eq_uXor32Core)
open Barrel3PassCommuteHelpers (uSlot0LocalXorBit5)
open TwosCompAndWire0Cancel (fwdPermUnitary fwdPermUnitary_apply)
open SpecsAux.BridgeFermionicComm (permutationUnitary_apply)
open InterWalkRSum42Hoist (qreg_ext kFull80 rCoreFull rPG48Full)
open InterWalkRSum42Hoist (hCoreFull_disj_PG48Full)
open Leaf1Pass1And3Width204 (rCoreBlock4 t4CarryExp t4WinPerm)
open Leaf1Pass1And3Width204 (t4WinPerm_apply uApexShift4)
open Leaf1Pass1And3Width204 (uSlot4ApexCatT4 uSlot4AxisCatT4)
open Leaf4Ext48TopStitch (CommutesWithReg commutesWithReg_fwdPermUnitary disj_of_val_ne rCtrl3InCore
  rCtrl3InCoreCat)
open SelectExtStitch (commutesWithReg_unitary_inv_ext h22_80)
open SelectExtStitch (h6_80)

/- ## Section 1: `CommutesWithReg (rCtrl3InCoreCat 4)` & `190w` / `193w` / `196w` `T4` Lifters -/

theorem commutesWithReg_diagonal_of_agreeOutside {m n : ℕ}
    (r : QRegister m n) (d : Fin (2 ^ n) → ℂ)
    (hd : ∀ i j : Fin (2 ^ n), r.AgreeOutside i j → d i = d j) :
    CommutesWithReg r (Matrix.diagonal d) := fun B ↦ by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, QRegister.embedMatrix_apply_of_agreeOutside]
  by_cases ho : r.AgreeOutside i j
  · simp [ho, hd i j ho, mul_comm]
  · simp [ho]

theorem not_mem_rCtrl3InCore_of_val {w : Wire (fullSysCoreWires 80)}
    (hw : w.val < 3951 ∨ 3954 ≤ w.val) : w ∉ Set.range rCtrl3InCore.wires := by
  rintro ⟨t, ht⟩
  have h0 := congrArg Fin.val ht
  simp [rCtrl3InCore, QRegister.block, Fin.castLEEmb, Fin.natAddEmb] at h0
  have := t.isLt
  omega

theorem rCoreBlock4_compose_rCtrl3InCore :
    (rCoreBlock4 80).compose rCtrl3InCore = rCtrl3InCoreCat 4 := by
  apply qreg_ext; intro t
  ext; simp [rCoreBlock4, rCtrl3InCore, rCtrl3InCoreCat, QRegister.block]

theorem coreElecCosetB1_disj_rCtrl3InCore :
    (coreElecCosetB1Block h6_80).DisjointWires rCtrl3InCore :=
  disj_of_val_ne fun idx t ↦ Fin.addCases
    (fun i h ↦ by
      rw [QRegister.concat_apply_left] at h
      have := i.isLt
      have := t.isLt
      simp [coreElecBlock, rCtrl3InCore, QRegister.block, Fin.castLEEmb, Fin.natAddEmb] at h
      omega)
    (fun j h ↦ by
      rw [QRegister.concat_apply_right] at h
      have := j.isLt
      have := t.isLt
      simp [coreCosetB1Block, rCtrl3InCore, QRegister.block, Fin.castLEEmb, Fin.natAddEmb] at h
      omega) idx

theorem commutesWithReg_rCtrl3InCore_uXor32Core80 :
    CommutesWithReg rCtrl3InCore (uXor32Core 80).1 := by
  rw [← embed_bit5Flip654_eq_uXor32Core h6_80, QRegister.embedUnitary_val]
  exact CommutesWithReg.of_disjoint coreElecCosetB1_disj_rCtrl3InCore _

theorem slot0LocalPhaseBit_congr_outside_ctrl3 (w_eff : ℝ)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (ho : ∀ w ∉ Set.range rCtrl3InCore.wires, γ₁ w = γ₂ w) :
    MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit (le_refl 80)
    w_eff γ₁ = MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit
    (le_refl 80) w_eff γ₂ := by
  have hAt (w : Wire (fullSysCoreWires 80)) (hw : w.val < 3951 ∨ 3954 ≤ w.val) : γ₁ w = γ₂ w :=
    ho w (not_mem_rCtrl3InCore_of_val hw)
  have hc (k : ℕ) (hk : k < 3951) (hk' : k < fullSysCoreWires 80) : γ₁ ⟨k, hk'⟩ = γ₂ ⟨k, hk'⟩ :=
    hAt ⟨k, hk'⟩ (Or.inl hk)
  have hPay (k : Fin 80) :
      γ₁ (MomSlots01Slot1ProjKinetic.corePayloadSym 80 k) =
      γ₂ (MomSlots01Slot1ProjKinetic.corePayloadSym 80 k) :=
    hAt _ (Or.inr (by simp [MomSlots01Slot1ProjKinetic.corePayloadSym,
      QRegister.block, Fin.castLEEmb, Fin.natAddEmb, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
        SpecsAux.SpecMirror.projectileBits]))
  have hBits (x : ℕ) (h : ∀ b : Fin 6, 6 * (x % 3) + b.val < fullSysCoreWires 80) :
      (fun b : Fin 6 ↦ γ₁ ⟨6 * (x % 3) + b.val, h b⟩) =
      (fun b : Fin 6 ↦ γ₂ ⟨6 * (x % 3) + b.val, h b⟩) :=
    funext fun b ↦ hAt _ (Or.inl (by
      have := Nat.mod_lt x (by decide : 0 < 3)
      have := b.isLt
      change 6 * (x % 3) + b.val < 3951
      omega))
  dsimp only [MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit]
  simp only [hc SpecsAux.SpecMirror.systemQubits (by decide) (by decide),
    hc (SpecsAux.SpecMirror.systemQubits + 1) (by decide) (by decide),
    hc (SpecsAux.SpecMirror.systemQubits + 2) (by decide) (by decide), hPay, hBits]

theorem commutesWithReg_rCtrl3InCore_uSlot0LocalXorBit5 : CommutesWithReg rCtrl3InCore
    (uSlot0LocalXorBit5 (le_refl 80)
    LiteralKineticAndMidpoint128.lambdaSlot0TeHi).1 := by
  unfold uSlot0LocalXorBit5 unitaryConj
  have hDiag : (coreUnitaryToFullSys
      (MomSlot0LocalAndMomCombine288.uSlot0Local (le_refl 80)
        LiteralKineticAndMidpoint128.lambdaSlot0TeHi)).1 =
      Matrix.diagonal (fun g ↦ (-1 : ℂ) ^
        (MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit (le_refl 80)
          LiteralKineticAndMidpoint128.lambdaSlot0TeHi
          (basisBits (fullSysCoreWires 80) g)).val) := rfl
  refine ((commutesWithReg_unitary_inv_ext commutesWithReg_rCtrl3InCore_uXor32Core80).mul ?_).mul
    commutesWithReg_rCtrl3InCore_uXor32Core80
  rw [hDiag]
  exact commutesWithReg_diagonal_of_agreeOutside rCtrl3InCore _ fun i j ho ↦ by
    rw [slot0LocalPhaseBit_congr_outside_ctrl3 _ ho]

abbrev aux_rIdCore80 := QRegExt.idReg (fullSysCoreWires 80)

theorem slot4Sgn_congr_outside_ctrl3 (isInv : Bool) (w : Fin 3)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (ho : ∀ q ∉ Set.range rCtrl3InCore.wires, γ₁ q = γ₂ q) :
    JunctionApexCSA288.slot4Sgn isInv h22_80 w γ₁ =
      JunctionApexCSA288.slot4Sgn isInv h22_80 w γ₂ := by
  have hb1_val : ∀ u : Fin 3,
      (NuclearTwistAndXor654Concrete.rCosetB1
        h22_80 aux_rIdCore80 u).val < 3951 ∨
      3954 ≤ (NuclearTwistAndXor654Concrete.rCosetB1
        h22_80 aux_rIdCore80 u).val := by decide
  have hb0_val : ∀ u : Fin 3,
      (NuclearTwistAndXor654Concrete.rCosetB0
        h22_80 aux_rIdCore80 u).val < 3951 ∨
      3954 ≤ (NuclearTwistAndXor654Concrete.rCosetB0
        h22_80 aux_rIdCore80 u).val := by decide
  have hs2 := ho (NuclearTwistAndXor654Concrete.wSlot2 aux_rIdCore80)
    (not_mem_rCtrl3InCore_of_val (by decide))
  have hs1 := ho (NuclearTwistAndXor654Concrete.wSlot1 aux_rIdCore80)
    (not_mem_rCtrl3InCore_of_val (by decide))
  have hs0 := ho (NuclearTwistAndXor654Concrete.wSlot0 aux_rIdCore80)
    (not_mem_rCtrl3InCore_of_val (by decide))
  have hb1 := ho _ (not_mem_rCtrl3InCore_of_val (hb1_val w))
  have hb0 := ho _ (not_mem_rCtrl3InCore_of_val (hb0_val w))
  dsimp only [JunctionApexCSA288.slot4Sgn, aux_rIdCore80]
    at hs2 hs1 hs0 hb1 hb0 ⊢
  simp only [hs2, hs1, hs0, hb1, hb0]

theorem slot4LowShift_congr_outside_ctrl3 (isInv : Bool) (w : Fin 3)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (ho : ∀ q ∉ Set.range rCtrl3InCore.wires, γ₁ q = γ₂ q) :
    JunctionApexCSA288.slot4LowShift isInv h22_80 w γ₁ =
      JunctionApexCSA288.slot4LowShift isInv h22_80 w γ₂ := by
  have hEl : ∀ (u : Fin 3) (j : Fin 4),
      (((NuclearTwistAndXor654Concrete.rElecSlotAxis
        aux_rIdCore80 0 u).slice 0 4 (by omega)) j).val < 3951 ∨
      3954 ≤ (((NuclearTwistAndXor654Concrete.rElecSlotAxis
        aux_rIdCore80 0 u).slice 0 4 (by omega)) j).val := by decide
  dsimp only [JunctionApexCSA288.slot4LowShift]
  rw [slot4Sgn_congr_outside_ctrl3 isInv w ho,
    show _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
      ((NuclearTwistAndXor654Concrete.rElecSlotAxis
        aux_rIdCore80 0 w).slice 0 4 (by omega)) γ₁ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
        ((NuclearTwistAndXor654Concrete.rElecSlotAxis
        aux_rIdCore80 0 w).slice 0 4 (by omega)) γ₂ from
      congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
        ho _ (not_mem_rCtrl3InCore_of_val (hEl w j)))]

theorem slot4TopExp_congr_outside_ctrl3 (isInv : Bool) (w : Fin 3)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (ho : ∀ q ∉ Set.range rCtrl3InCore.wires, γ₁ q = γ₂ q) :
    JunctionApexCSA288.slot4TopExp isInv h22_80 w γ₁ =
      JunctionApexCSA288.slot4TopExp isInv h22_80 w γ₂ := by
  have he4 : ∀ u : Fin 3,
      (NuclearTwistAndXor654Concrete.rElecSlotAxis
        aux_rIdCore80 0 u 4).val < 3951 ∨
      3954 ≤ (NuclearTwistAndXor654Concrete.rElecSlotAxis
        aux_rIdCore80 0 u 4).val := by decide
  have he5 : ∀ u : Fin 3,
      (NuclearTwistAndXor654Concrete.rElecSlotAxis
        aux_rIdCore80 0 u 5).val < 3951 ∨
      3954 ≤ (NuclearTwistAndXor654Concrete.rElecSlotAxis
        aux_rIdCore80 0 u 5).val := by decide
  dsimp only [JunctionApexCSA288.slot4TopExp]
  rw [slot4Sgn_congr_outside_ctrl3 isInv w ho,
    ho _ (not_mem_rCtrl3InCore_of_val (he4 w)), ho _ (not_mem_rCtrl3InCore_of_val (he5 w))]

theorem t4WinPerm_symm_eq {kSys : ℕ} (δ : BitAssignment kSys → ℤ) :
    (t4WinPerm kSys δ).symm = t4WinPerm kSys (fun γ ↦ -δ γ) := by
  apply Equiv.ext; intro x
  unfold t4WinPerm
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.trans_apply]
  rfl

theorem commutesWithReg_rCtrl3InCoreCat4_uApexShift4
    (δ : BitAssignment (fullSysCoreWires 80) → ℤ) (hδ : ∀ {γ₁ γ₂ : BitAssignment
    (fullSysCoreWires 80)}, (∀ q ∉ Set.range rCtrl3InCore.wires, γ₁ q = γ₂ q) → δ γ₁ = δ γ₂)
    : CommutesWithReg (rCtrl3InCoreCat 4) (uApexShift4 (fullSysCoreWires 80) δ).1 := by
  have hCastNotMem : ∀ {q : Wire (fullSysCoreWires 80)}, q ∉ Set.range rCtrl3InCore.wires →
      Fin.castAdd 4 q ∉ Set.range (rCtrl3InCoreCat 4).wires := by
    intro q hq ⟨t, ht⟩
    apply hq
    refine ⟨t, Fin.ext ?_⟩
    have hv := congrArg Fin.val ht
    simpa [rCtrl3InCore, rCtrl3InCoreCat, QRegister.block] using hv
  have hNatNotMem : ∀ k : Fin 4,
      Fin.natAdd (fullSysCoreWires 80) k ∉ Set.range (rCtrl3InCoreCat 4).wires := by
    intro k ⟨t, ht⟩
    have hv := congrArg Fin.val ht
    have hk := k.isLt; have ht' := t.isLt
    dsimp [rCtrl3InCoreCat, QRegister.block, Fin.castLEEmb, Fin.natAddEmb,
      fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
      SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hv
    omega
  have hPermAux : ∀ (δ' : BitAssignment (fullSysCoreWires 80) → ℤ), (∀ {γ₁ γ₂ : BitAssignment
      (fullSysCoreWires 80)}, (∀ q ∉ Set.range rCtrl3InCore.wires, γ₁ q = γ₂ q) → δ' γ₁ = δ'
      γ₂) → (∀ x : Fin (2 ^ (fullSysCoreWires 80 + 4)), (rCtrl3InCoreCat 4).extractIndex
      (t4WinPerm (fullSysCoreWires 80) δ' x) = (rCtrl3InCoreCat 4).extractIndex x) ∧ (∀ x y :
      Fin (2 ^ (fullSysCoreWires 80 + 4)), (rCtrl3InCoreCat 4).AgreeOutside x y →
      (rCtrl3InCoreCat 4).AgreeOutside (t4WinPerm (fullSysCoreWires 80) δ' x) (t4WinPerm
      (fullSysCoreWires 80) δ' y)) := by
    intro δ' hδ'
    let eSC := DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4
    have hSysBits (z : Fin (2 ^ (fullSysCoreWires 80 + 4))) :
        (eSC z).1 = fun i ↦ basisBits (fullSysCoreWires 80 + 4) z (Fin.castAdd 4 i) := by
      funext i; conv_rhs => rw [← eSC.symm_apply_apply z, ← Prod.mk.eta (p := eSC z),
        JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd]
    have hCatBits (z : Fin (2 ^ (fullSysCoreWires 80 + 4))) :
        basisBits 4 (eSC z).2 =
          fun k ↦ basisBits (fullSysCoreWires 80 + 4) z (Fin.natAdd (fullSysCoreWires 80) k) := by
      funext k; conv_rhs => rw [← eSC.symm_apply_apply z, ← Prod.mk.eta (p := eSC z),
        JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_natAdd]
    refine ⟨fun x ↦ ?_, fun x y ho q ↦ ?_⟩
    · apply (basisBitsEquiv 3).injective; funext t
      change basisBits 3 _ t = basisBits 3 _ t
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      have hrc : rCtrl3InCoreCat 4 t = Fin.castAdd 4 (rCtrl3InCore t) := by
        ext; simp [rCtrl3InCoreCat, rCtrl3InCore, QRegister.block]
      rw [hrc, t4WinPerm_apply,
        JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd]
      exact congrFun (hSysBits x) (rCtrl3InCore t)
    · refine Fin.addCases (fun i hqi ↦ ?_) (fun k _ ↦ ?_) q
      · rw [t4WinPerm_apply, t4WinPerm_apply,
          JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd,
          JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd,
          hSysBits x, hSysBits y]
        exact ho (Fin.castAdd 4 i) hqi
      · have hCatEq : (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 x).2 =
            (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 y).2 := by
          apply (basisBitsEquiv 4).injective
          change basisBits 4 _ = basisBits 4 _
          rw [hCatBits x, hCatBits y]
          funext l; exact ho _ (hNatNotMem l)
        have hDelEq : δ' (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 x).1 =
            δ' (DyadicQft64.splitSysCatEquiv (fullSysCoreWires 80) 4 y).1 := by
          rw [hSysBits x, hSysBits y]
          exact hδ' fun c hc ↦ ho (Fin.castAdd 4 c) (hCastNotMem hc)
        rw [t4WinPerm_apply, t4WinPerm_apply,
          JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_natAdd,
          JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_natAdd,
          hCatEq, hDelEq]
  unfold uApexShift4
  rw [Submonoid.coe_mul]
  have hFwdEq : (Operator.permutationUnitary (t4WinPerm (fullSysCoreWires 80) δ)).1 =
      (fwdPermUnitary (t4WinPerm (fullSysCoreWires 80) δ)).1 := by
    ext a b; rw [permutationUnitary_apply, fwdPermUnitary_apply]; simp only [eq_comm]
  refine CommutesWithReg.mul ?_ ?_
  · rw [hFwdEq]
    refine commutesWithReg_fwdPermUnitary (rCtrl3InCoreCat 4) _
      (hPermAux δ hδ).1 (hPermAux δ hδ).2 ?_
    rw [t4WinPerm_symm_eq]
    exact (hPermAux (fun γ ↦ -δ γ) fun ho ↦ congrArg Neg.neg (hδ ho)).2
  · exact commutesWithReg_diagonal_of_agreeOutside (rCtrl3InCoreCat 4) _ fun i j ho ↦ by
      congr 1
      unfold t4CarryExp
      rw [show (fun k : Fin 4 ↦ basisBits (fullSysCoreWires 80 + 4) i
          (Fin.natAdd (fullSysCoreWires 80) k)) =
          (fun k : Fin 4 ↦ basisBits (fullSysCoreWires 80 + 4) j
            (Fin.natAdd (fullSysCoreWires 80) k)) from funext fun k ↦ ho _ (hNatNotMem k),
        hδ fun c hc ↦ ho (Fin.castAdd 4 c) (hCastNotMem hc)]

theorem commutesWithReg_rCtrl3InCoreCat4_uSlot4ApexCatT4 :
    CommutesWithReg (rCtrl3InCoreCat 4) (uSlot4ApexCatT4 h22_80).1 := by
  have hAx : ∀ w : Fin 3, CommutesWithReg (rCtrl3InCoreCat 4) (uSlot4AxisCatT4 false h22_80 w).1 :=
    fun w ↦ by
      unfold uSlot4AxisCatT4
      rw [Submonoid.coe_mul]
      refine (commutesWithReg_rCtrl3InCoreCat4_uApexShift4 _
        (slot4LowShift_congr_outside_ctrl3 false w)).mul ?_
      rw [QRegister.embedUnitary_val, ← rCoreBlock4_compose_rCtrl3InCore]
      refine CommutesWithReg.embedMatrix (rCoreBlock4 80) ?_
      exact commutesWithReg_diagonal_of_agreeOutside rCtrl3InCore _ fun i j ho ↦ by
        rw [slot4TopExp_congr_outside_ctrl3 false w ho]
  unfold uSlot4ApexCatT4
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  exact (hAx 2).mul ((hAx 1).mul (hAx 0))

abbrev rT4Full : QRegister 4 kFull80 := rPG48Full.slice 41 4 (by decide)

theorem hCoreFull_disj_rT4Full : rCoreFull.DisjointWires rT4Full :=
  hCoreFull_disj_PG48Full.compose_right (QRegister.block 41 4 (by decide))

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512

end ConfigSelectPass13Gen

end SelectPass13Gen

end
set_option exponentiation.threshold 256
end SelectPass13Gen

section CoreQftHadamardPrunedCore
local instance (priority := 1000000) instNeZeroTwoPow_CoreQftHadamardPrunedCore (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Pruned `128`-Wire Core QFT-Hadamard Bundle (`CoreQftHadamardPrunedCore`)

Constructs the flexible column-pruned XOR-apex batch engine (`FlexApexEngine`),
`coreQftHadamardPrunedStages128 : CanonStageSpec128`, `toCanonQft654PrunedBundleOfLe128`,
and `coreQftHadamardPrunedBundle128 : FullSysCatSegmentBridge.FullSysQft654Bundle`
(`mWorkQft = 128`, `tQft = 23425`, `0` `.TOFF`).
-/

public section
namespace CoreQftHadamardPrunedCore
section ConfigCoreQftHadamardPrunedCore
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux
open SpecsAux.SpecMirror
open DyadicQft64
open DyadicQft64WalkCircuit
open DyadicQft64WalkCircuit288
open FullSysCatSegmentBridge
open CoreQftHadamard140And160
open scoped Matrix BigOperators Circuit.Notation
local instance (priority :=
  1000000) instLoc_CoreQftHadamardPrunedCore_1InstNeZeroTwoPowQ (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
attribute [local irreducible] DyadicQft64.dyadicDiagUnitary stageH654
attribute [local irreducible] stageD654
attribute [local semireducible] stageD654
noncomputable def coreQftHadamardPrunedBundle128 : FullSysCatSegmentBridge.FullSysQft654Bundle :=
  FullSysCatSegmentBridge.FullSysQft654Bundle.ofIdeal654 128 coreQftHadamardStages288.uEff
@[scoped simp]
theorem coreQftHadamardPrunedBundle128_mWorkQft : coreQftHadamardPrunedBundle128.mWorkQft = 128 :=
  rfl
@[scoped simp] theorem coreQftHadamardPrunedBundle128_uQft654 :
    coreQftHadamardPrunedBundle128.uQft654 = coreQftHadamardStages288.uEff := rfl
set_option exponentiation.threshold 256
set_option maxRecDepth 512
end ConfigCoreQftHadamardPrunedCore
end CoreQftHadamardPrunedCore
end
set_option exponentiation.threshold 256
end CoreQftHadamardPrunedCore

section ZeroSubwireHarmonicGridPert
local instance (priority := 1000000) instNeZeroTwoPow_ZeroSubwireHarmonicGridPert (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
Zero-Subwire Constant-Alpha & Truncation-Polymorphic Grid-Perturbation Bridge
(`ZeroSubwireHarmonicGridPert`).

Provides:
1. Constant-alpha zero-subwire `FullSysPrepareBundle 80` (`Coin3ConstAlphaSpec`,
   `zeroSubwireConstPrepBundle`) with width-polymorphic `hmPrep` (`128 <= mWork`, covering
   `mWork = 288` and `mWork in {248, 220}`) and `InterWalkRSum42Hoist.FixesLow3924`
   preservation.
2. Generic `U3 : Unitary (2 ^ 3)` 4,034-wire zero-subwire top-block collapse, 6-slot weight
   bounds (`sixSlotWeight_lt_135598`), `37b` and `36b` intrinsic error sums,
   and `PosPostPrep80FastCircuit` (`L = 23` `<= 2,992 T` and `L = 26` `<= 3,010 T`)
   position operator perturbation bounds.
3. Width-, barrel-, position-oracle-, and `truncCfg`-polymorphic select decomposition
   and `hGridPert` closures for `HarmonicScheduleBridge`.
-/

public section

namespace ZeroSubwireHarmonicGridPert

section ConfigZeroSubwireHarmonicGridPert

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority :=
  1000000) instLoc_ZeroSubwireHarmonicGridPert_1InstNeZeroTwoPo (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysPrepare6Slot (fullSysCoinIdx coinSelOutcome)
open FullSysFullPrepareAndTopConcrete (selWiresSym coreWiresSym coreSysSym coreAncSym selCoin3Sym
  coreHadamardUnitary)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open MomSlot0CircuitHalf (slot0ElectronKineticOracleSym)
open MomSlots01Slot1ProjKinetic (slot1ProjKineticOracleSym)
open OraAndPrepBundle (fin6Tuple PosPostPrepCert)
open PosSlots24SemanticOracleConcrete80 (pos80Slot2Scale pos80Slot4Scale)
open ZeroSubwireCoinPrep80 (rCoin3Core)

/-- Constant-`α` zero-subwire `PREPARE` unitary on `coreWiresSym mPayload`
(`= fullSysBEWires mPayload` by `rfl`). -/
noncomputable def zeroSubwireConstPrepUnitary {mPayload : ℕ} (post : PosPostPrepCert mPayload)
    (uCoin : Unitary (2 ^ 3)) : Unitary (2 ^ (coreWiresSym mPayload)) := post.uPosPost *
    (coreHadamardUnitary mPayload * (rCoin3Core mPayload).embedUnitary uCoin)

/- Section 2: Generic `U3 : Unitary (2 ^ 3)` Top-Block Collapse & Error Caps -/

open ZeroSubwireGridPert80 (coinSelOutcome_80_zero extractIndex_coinSelOutcome_80
  eq_coinSelOutcome_80_of_outside_zero elemMat86) in
theorem coin3Anc86_mul_elem00_of_unitary (U3 : Unitary (2 ^ 3)) :
    ((selCoin3Sym 80).embedUnitary U3).1 * elemMat86 0 0 = ∑ c : Fin 8, (U3.1 c 0) • elemMat86
    (coinSelOutcome (selCoin3Sym 80) c) 0 := by
  ext x y
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  by_cases hy : y = 0
  · subst hy
    rw [Finset.sum_eq_single 0 (fun z _ hz ↦ by simp [elemMat86, hz])
      (fun h0 ↦ absurd (Finset.mem_univ 0) h0)]
    have he00 : elemMat86 0 0 0 0 = 1 := rfl
    rw [he00, mul_one, QRegister.embedUnitary_val, QRegister.embedMatrix_apply]
    by_cases hEnv :
        ((selCoin3Sym 80).basisSplitEquiv x).2 = ((selCoin3Sym 80).basisSplitEquiv 0).2
    · have hAgree : (selCoin3Sym 80).AgreeOutside x 0 :=
        ((selCoin3Sym 80).basisSplit_environment_eq_iff x 0).mp hEnv
      have hOut0 : ∀ w ∉ (selCoin3Sym 80).image, basisBits (selWiresSym 80) x w = 0 := by
        intro w hw
        have hwR : w ∉ Set.range (selCoin3Sym 80).wires :=
          fun ⟨j, hj⟩ ↦ hw ((QRegister.mem_image (selCoin3Sym 80) w).mpr ⟨j, hj⟩)
        simpa only [basisBits_zero_at] using hAgree w hwR
      let cx := (selCoin3Sym 80).extractIndex x
      have hxeq : x = coinSelOutcome (selCoin3Sym 80) cx :=
        eq_coinSelOutcome_80_of_outside_zero x hOut0
      have hz0 : (selCoin3Sym 80).extractIndex 0 = 0 := by
        rw [← coinSelOutcome_80_zero, extractIndex_coinSelOutcome_80]
      simp only [hEnv, ↓reduceIte, mul_one, hz0]
      symm
      refine (Finset.sum_eq_single cx ?_ ?_).trans ?_
      · intro c _ hne
        have hne_o : x ≠ coinSelOutcome (selCoin3Sym 80) c := by
          intro h; apply hne
          have := congrArg (selCoin3Sym 80).extractIndex (h.symm.trans hxeq)
          simpa only [extractIndex_coinSelOutcome_80] using this
        simp [elemMat86, hne_o]
      · intro hmem; exact absurd (Finset.mem_univ cx) hmem
      · simp [elemMat86, cx, ← hxeq]
    · simp only [hEnv, ↓reduceIte, mul_zero]
      refine (Finset.sum_eq_zero fun c _ ↦ ?_).symm
      have hne_o : x ≠ coinSelOutcome (selCoin3Sym 80) c := fun h ↦ hEnv <| by
        subst h
        rw [(selCoin3Sym 80).basisSplit_environment_eq_iff]
        exact fun w hwR ↦ (FullSysPrepare6Slot.basisBits_coinSelOutcome_outside _ _
          (fun hm ↦ hwR ((QRegister.mem_image (selCoin3Sym 80) w).mp hm))).trans
          (basisBits_zero_at _ w).symm
      simp [elemMat86, hne_o]
  · rw [Finset.sum_eq_zero fun j _ ↦ by simp [elemMat86, hy],
      Finset.sum_eq_zero fun c _ ↦ by simp [elemMat86, hy]]

open ZeroSubwireGridPert80 (elemMat86 elemMat86_conjTranspose embed_elemMat86_diag
  embedMatrix_sum_fin8 ancTransition_sandwich_sysEmbed ancTransition_left_proj
  ancTransition_right_proj_adj) in
theorem zeroSubwire_coin_topBlock_sum_of_unitary
    (U3 : Unitary (2 ^ 3))
    (S_core : Unitary (2 ^ (coreWiresSym 80)))
    (B_coin : Fin 8 → Operator (2 ^ systemQubits))
    (hDiag : ∀ c : Fin 8,
      let P_c := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)
      P_c * S_core.1 * P_c = P_c * (coreSysSym 80).embedMatrix (B_coin c) * P_c)
    (hOffDiag : ∀ c₁ c₂ : Fin 8, c₁ ≠ c₂ →
      let P₁ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₁)
      let P₂ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₂)
      P₁ * S_core.1 * P₂ = 0) :
    let P0 := (coreAncSym 80).basisOutcomeProjector 0
    let U_coin := (rCoin3Core 80).embedUnitary U3
    P0 * (unitaryConj U_coin S_core).1 * P0 =
      P0 * (coreSysSym 80).embedMatrix
        (∑ c : Fin 8, ((‖U3.1 c 0‖ ^ 2 : ℝ) : ℂ) • B_coin c) * P0 := by
  intro P0 U_coin
  let o : Fin 8 → Fin (2 ^ (selWiresSym 80)) := coinSelOutcome (selCoin3Sym 80)
  let T : Fin 8 → Operator (2 ^ (coreWiresSym 80)) :=
    fun c ↦ (coreAncSym 80).embedMatrix (elemMat86 (o c) 0)
  have hU_comp : U_coin =
      (coreAncSym 80).embedUnitary ((selCoin3Sym 80).embedUnitary U3) := by
    dsimp only [U_coin, rCoin3Core]
    exact QRegister.embedUnitary_compose (coreAncSym 80) (selCoin3Sym 80) U3
  have hRight : U_coin.1 * P0 = ∑ c : Fin 8, (U3.1 c 0) • T c := by
    dsimp only [P0, T, o]
    rw [hU_comp, QRegister.embedUnitary_val, ← embed_elemMat86_diag 0,
      ← QRegister.embedMatrix_mul, coin3Anc86_mul_elem00_of_unitary U3, embedMatrix_sum_fin8]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    exact QRegister.embedMatrix_smul (coreAncSym 80) _ _
  have hP0_sa : P0ᴴ = P0 := by
    dsimp only [P0]
    rw [← embed_elemMat86_diag 0, ← QRegister.embedMatrix_conjTranspose, elemMat86_conjTranspose]
  have hLeft : P0 * U_coin.1ᴴ = ∑ c : Fin 8, star (U3.1 c 0) • (T c)ᴴ := by
    have h := congrArg (fun M ↦ Mᴴ) hRight
    simpa only [Matrix.conjTranspose_mul, hP0_sa, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul] using h
  have hLHS : P0 * (unitaryConj U_coin S_core).1 * P0 =
      (P0 * U_coin.1ᴴ) * S_core.1 * (U_coin.1 * P0) := by
    rw [unitaryConj_val]; simp only [Matrix.mul_assoc]
  rw [hLHS, hLeft, hRight, Finset.sum_mul, Finset.sum_mul]
  have hTerm : ∀ c₁ : Fin 8,
      ((star (U3.1 c₁ 0) • (T c₁)ᴴ) * S_core.1) *
          (∑ c₂ : Fin 8, (U3.1 c₂ 0) • T c₂) =
        (((‖U3.1 c₁ 0‖ ^ 2 : ℝ) : ℂ)) •
          (P0 * (coreSysSym 80).embedMatrix (B_coin c₁) * P0) := fun c₁ ↦ by
    rw [Finset.mul_sum, Finset.sum_eq_single c₁]
    · have hMid : (T c₁)ᴴ * S_core.1 * T c₁ =
          P0 * (coreSysSym 80).embedMatrix (B_coin c₁) * P0 := by
        dsimp only [T, o]
        nth_rw 1 [← ancTransition_right_proj_adj c₁]
        nth_rw 2 [← ancTransition_left_proj c₁]
        have h1 := hDiag c₁
        dsimp only at h1
        have hAssoc {A B C D E : Operator (2 ^ (coreWiresSym 80))} :
            (A * B) * C * (D * E) = A * (B * C * D) * E := by simp only [Matrix.mul_assoc]
        rw [hAssoc, h1, ← hAssoc, ancTransition_right_proj_adj c₁, ancTransition_left_proj c₁]
        exact ancTransition_sandwich_sysEmbed c₁ (B_coin c₁)
      have hNorm (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hNorm, hMid]
    · intro c₂ _ hne
      have hZero : (T c₁)ᴴ * S_core.1 * T c₂ = 0 := by
        dsimp only [T, o]
        conv_lhs => rw [← ancTransition_right_proj_adj c₁, ← ancTransition_left_proj c₂]
        have hAssoc {A B C D E : Operator (2 ^ (coreWiresSym 80))} :
            (A * B) * C * (D * E) = A * (B * C * D) * E := by simp only [Matrix.mul_assoc]
        rw [hAssoc, hOffDiag c₁ c₂ hne.symm, Matrix.mul_zero, Matrix.zero_mul]
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hZero, smul_zero]
    · intro hmem; exact absurd (Finset.mem_univ c₁) hmem
  rw [Finset.sum_congr rfl fun c₁ _ ↦ hTerm c₁]
  simp only [Fin.sum_univ_eight, QRegister.embedMatrix_add, QRegister.embedMatrix_smul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Realized 6-slot weight `α * ‖U3[coin k, 0]‖²` for a generic `3`-coin unitary `U3`. -/
noncomputable def wActOfUnitary (α : ℝ) (U3 : Unitary (2 ^ 3)) (k : Fin 6) : ℝ :=
  α * ‖U3.1 (fullSysCoinIdx k) 0‖ ^ 2

theorem wActOfUnitary_nonneg {α : ℝ} (hα : 0 ≤ α) (U3 : Unitary (2 ^ 3)) (k : Fin 6) : 0 ≤
    wActOfUnitary α U3 k := mul_nonneg hα (sq_nonneg _)

theorem norm_sq_uCoin_eq_inv_mul_wActOfUnitary {α : ℝ} (hα : 0 < α) (U3 : Unitary (2 ^ 3))
    (k : Fin 6) : ((‖U3.1 (fullSysCoinIdx k) 0‖ ^ 2 : ℝ) : ℂ) = (α : ℂ)⁻¹ *
    (wActOfUnitary α U3 k : ℂ) := by
  have hα0 : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  unfold wActOfUnitary
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hα0, one_mul]

theorem sixSlot_diff_rearrange {V : Type*} [AddCommGroup V] [Module ℂ V]
    (wa0 wa1 wa2 wa3 wa4 wa5 wi0 wi1 wi2 wi3 wi4 wi5 : ℝ) (b0 b1 b2a b2i b3 b4a b4i b5 : V) :
    ((wa0 : ℂ) • b0 + (wa1 : ℂ) • b1 + (wa2 : ℂ) • b2a + (wa3 : ℂ) • b3 + (wa4 : ℂ) • b4a +
    (wa5 : ℂ) • b5) - ((wi0 : ℂ) • b0 + (wi1 : ℂ) • b1 + (wi2 : ℂ) • b2i + (wi3 : ℂ) • b3 +
    (wi4 : ℂ) • b4i + (wi5 : ℂ) • b5) = (((wa0 - wi0 : ℝ) : ℂ) • b0 + ((wa1 - wi1 : ℝ) : ℂ) •
    b1 + ((wa2 - wi2 : ℝ) : ℂ) • b2i + ((wa3 - wi3 : ℝ) : ℂ) • b3 + ((wa4 - wi4 : ℝ) : ℂ) •
    b4i + ((wa5 - wi5 : ℝ) : ℂ) • b5) + ((wa2 : ℂ) • (b2a - b2i) + (wa4 : ℂ) • (b4a - b4i))
    := by
  simp only [Complex.ofReal_sub, sub_smul, smul_sub]
  abel

theorem forall_fin6_prop {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) : ∀ k : Fin 6, P k := fun k ↦ by
  fin_cases k <;> assumption

open Pos24MergedVepPrepAndStitch (mergedPosSlot2WeightGen) in
/-- Pure 6-slot weight vector with literal `0` on Slot 5, avoiding `mkTierBWeights80` /
  `tierBBarrel80`. -/
noncomputable def mkZeroSubwireWeights80 (s3 : MomSingleSlotOracle 80 48 3)
    (cfg : Configuration) : Fin 6 → ℝ := fin6Tuple
    ((slot0ElectronKineticOracleSym (le_refl 80)).wSlot cfg)
    ((slot1ProjKineticOracleSym (le_refl 80)).wSlot cfg) (mergedPosSlot2WeightGen ((108 : ℝ) /
    109) (fun _ ↦ pos80Slot2Scale) cfg) (s3.wSlot cfg) pos80Slot4Scale 0

set_option maxRecDepth 512
set_option exponentiation.threshold 256

end ConfigZeroSubwireHarmonicGridPert

end ZeroSubwireHarmonicGridPert
end
set_option exponentiation.threshold 256
end ZeroSubwireHarmonicGridPert

section PosSlots24Q30Tight
local instance (priority := 1000000) instNeZeroTwoPow_PosSlots24Q30Tight (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

-- Tight Q30 Orbit Certificate + Analytic Global-Optimum C_cut* Shift (PosSlots24Q30Tight)
--
-- Pure proof-only tightening (zero circuit, QROM, or uPosPhase modifications):
--   1. `abs_w128Orbit_sub_q30_le_tight` (`≤ 5615 / (10000 * 2 ^ 30)` vs `1 / 2 ^ 30`), tightening
--      both `Slot 4` (`eps4_q30_tight = 12.369 uHa`, `-9.660 uHa`) and `Slot 2` (`-19.23 uHa`).
-- 2. Analytic `C_cut*` head + per-parity shifted-tail split on `uenSubGridRaw48 (truncCfg c) -
-- uenSubGridRaw c`
-- (`optCutQb = ![2053805300, 2046201215, 2037550263, 2030148282]`, only `94` active orbits out of
-- `286`
--      with `w < 11`), plus exact zero-nuclear-rounding `V_ep` split on `cfgProjZ512 zP`, cutting
-- `(109 / 108) * eps2` to `340.83 uHa` (`36b`, `-84 uHa` total) and `182.88 uHa` (`37b`, `-57 uHa`
-- total).

public section

namespace PosSlots24Q30Tight
open SpecsAux.SpecMirror

section ConfigPosSlots24Q30Tight

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 512
set_option maxRecDepth 4096
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

local instance (priority :=
  1000000) instLoc_PosSlots24Q30Tight_1InstNeZeroTwoPowPos24Q30 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux
  (fermionicProjector_isHermitian fermionicProjector_mul_gridProjector gridProjector
   gridProjector_mul_fermionicProjector gridProjector_mul_self)
open SpecsAux.BridgeFermionicComm.SpecInner (fermionicProjector_idem)
open SpecsAux.FullScaleBESector (AgreesOnFermionicSector)
open SpecsAux.FullScaleBESector (agreesOnFermionicSector_trans)
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
  (norm_projector_le_one sixChannelShifted)
open SpecsAux.DyadicSubgridToeplitz128 (coulombDual128Real)
open SpecsAux.DyadicSubgridToeplitz512AndShift (NyqFine3D512)
open Dyadic128CoulombMath
  (canonTriple128 mem_momentumTransferBox62 momentumTransferBox62 orbitCount47905
   tetRank65
   tetUnrank65 w128Dual_eq_orbit w128Orbit)
open Dyadic128OrbitTableCert (abs_inv_sub_laplace_le abs_prefactor_sub_p80_le b2BiasNat b56Nat
  b80Nat bBiasNat canonicalTriple_orbitOk card_erase_zero_box62 cellSide checkScalarConsts
  checkScalarConsts_true coulombKernel_eq_of_ne_zero coulombKernel_zero dot160 evalTripleBiasedQ30
  evalTriple_round_error g1DReal g1DReal_bounds laplaceSumReal momentumTransferBox62_eq_piFinset
  negConst328Nat normSqInt orbitTripleOk p80Nat posConst328Nat pw160Vec r80Vec real_mul_le_one
  scalarConsts_lanes shift298Nat sum160 sum160_eq sumPW160Nat sumU328 u56Col vec160Get w128DualQ30
  w128OrbitBiasedQ30 w128OrbitQ30 w128OrbitQ30Real w80Vec wqVec160)
open SingleAnchorFermionicPauliCap
  (agreesOnFermionicSector_gridSandwich_of_mul_eq)
open SixSlotEndpointJunctionBridge
  (sixChannelGridProjector_eq_specsGridProjector)
open Slot2Slot4QuantizedChannelBridge
  (coulombDual128Real_eq_orbit coulombDual128Real_eq_w128Dual
   gridSandwich_uenSubGridRaw_coulomb_eq gridSandwich_veeSingleAnchorRaw_coulomb_eq
    norm_uenSubGridRaw_sub_le norm_veeSingleAnchorRaw_sub_le
   uEnManyBody_eq_sixChannelRaw uenSubGridRaw vEeManyBody_eq_sixChannelRaw
   veeSingleAnchorRaw veeSingleAnchorRaw_comm_perm)
open PosSlots24MergedVepBound
  (cfgProjZ512 rProj24_sp vepFromSlot2Op vepFromSlot2_agreesOnFermionicSector)
open TwosCompAndWire0Cancel (smToTwosSysUnitary)
open TwosCompAndWire0Cancel (smToTwosSysUnitary_conjTranspose)
open PosSlots24Semantic80Physics (coherentSysOp80_isHermitian)
open PosSlots24Semantic80Physics (pos80IdealDist)
open PosSlots24SemanticOracleConcrete80
  (coherentSysOp80 pos80Slot2Scale pos80Slot4Scale)
open Pos24MergedVepPrepAndStitch
  (mergedPosSlot2Gen_smConj_eq mergedPosSlot2WeightGen smConj_comm_embedMatrix_of_idleTwos
   smToTwosSysUnitary_sa)
open MergedVepLeaf4GridPerturbation
  (tierBB2Id tierBB2Id_isHermitian tierBB2RawId tierBB4Id)
open TierBClean80Closure (tierBQftFull)
open Pos24Slot2FermionicBridge
  (agreesOnFermionicSector_gridSandwich_slot2Mod agreesOnFermionicSector_of_isHermitian_and_mul_eq
   bModSlot248 bModSlot248_comm_rProj24 bModSlot248_inGridPerm bModSlot248_isHermitian
   isHermitian_gridSandwich_slot2 isHermitian_real_smul_slot2
   norm_proj_sandwich_le_part4A norm_uenSubGridRaw48_sub_exact_le pos24Slot2E2Const
   tierBB2RawId_comm_rProj24 tierBB2RawId_mul_fermionicProjector_eq
   uenSubGridRaw48 vepFromSlot2Op_isHermitian_of_idle
   vepFromSlot2Op_mul_fermionicProjector_eq)
open Pos24Slot4FermionicBridge (ag_g4 c4_fp ih_sm pos80Slot4EShift)
open Pos24Slot4FermionicBridge (pos80Slot4EShiftFn s4S s4_cp s4_ih)

/- ## Section 1: Factored `sTabOrbit` Rounding Lemma & Tight `Q30` (`≤ 5615 / (10000 * 2 ^ 30)`) -/

/-- Pure-`Nat` 160-lane Laplace-tensor sum `S_tab(idx)` before `Q30` rounding. -/
noncomputable def sTabOrbit (idx : Fin orbitCount47905) : ℝ :=
  let t := tetRank65.symm idx
  ∑ blk : Fin 10, ∑ i : Fin 16,
    ((vec160Get pw160Vec blk i : ℝ) / 2 ^ 160) *
      ((((vec160Get (u56Col t.w.val) blk i : ℝ) - 2 ^ 63) / 2 ^ 56) *
       (((vec160Get (u56Col t.v.val) blk i : ℝ) - 2 ^ 63) / 2 ^ 56) *
       (((vec160Get (u56Col t.u.val) blk i : ℝ) - 2 ^ 63) / 2 ^ 56) - 1)

theorem abs_sTabOrbit_sub_q30_le (idx : Fin orbitCount47905) :
    |sTabOrbit idx - (w128OrbitQ30 idx : ℝ) / 2 ^ 30| ≤ (1 : ℝ) / 2 ^ 31 := by
  set t := tetRank65.symm idx
  have ht_eq : tetUnrank65 idx = t := rfl
  have hsc := checkScalarConsts_true
  simp only [checkScalarConsts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsc
  rcases hsc with ⟨⟨⟨⟨⟨⟨hsum_pw, _⟩, _⟩, hpos_c⟩, hneg_c⟩, hsumU_all⟩, _⟩
  have hpw_sum_r : (∑ blk : Fin 10, ∑ i : Fin 16, (vec160Get pw160Vec blk i : ℝ)) =
      (sumPW160Nat : ℝ) := by exact_mod_cast (hsum_pw.symm.trans (sum160_eq pw160Vec)).symm
  have hok := canonicalTriple_orbitOk t
  simp only [orbitTripleOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hsumU_eq : sumU328 t.u.val = b2BiasNat * dot160 pw160Vec (u56Col t.u.val) :=
    List.all_eq_true.mp hsumU_all t.u.val (List.mem_range.mpr t.u.isLt) |> of_decide_eq_true
  unfold w128OrbitQ30
  simp only [w128OrbitBiasedQ30, ht_eq, evalTripleBiasedQ30, Int.cast_sub, Int.cast_natCast,
    show ((1073741824 : ℤ) : ℝ) = 2 ^ 30 by norm_num]
  exact evalTriple_round_error (u56Col t.w.val) (u56Col t.v.val) (u56Col t.u.val)
    (sumU328 t.u.val) hpw_sum_r hpos_c hneg_c
    (fun blk i ↦ ⟨(g1DReal_bounds blk i t.w.isLt).1, (g1DReal_bounds blk i t.w.isLt).2.1⟩)
    (fun blk i ↦ ⟨(g1DReal_bounds blk i t.v.isLt).1, (g1DReal_bounds blk i t.v.isLt).2.1⟩)
    hsumU_eq hok.1.1.1.1

theorem abs_w128Orbit_sub_q30_le_tight (idx : Fin orbitCount47905) :
    |w128Orbit idx - (w128OrbitQ30 idx : ℝ) / 2 ^ 30| ≤
      (5615 : ℝ) / (10000 * 2 ^ 30) := by
  set t := tetRank65.symm idx
  set u := t.u.val
  set v := t.v.val
  set w := t.w.val
  set mVec : Fin 3 → ℕ := ![u, v, w]
  let S_exp : ℝ := ∑ blk : Fin 10, ∑ i : Fin 16, ((vec160Get pw160Vec blk i : ℝ) / 2 ^ 160) *
      (g1DReal blk i w * g1DReal blk i v * g1DReal blk i u - 1)
  have hsc := checkScalarConsts_true
  simp only [checkScalarConsts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsc
  rcases hsc with ⟨⟨⟨⟨⟨⟨hsum_pw, hpw_le⟩, hp80_le⟩, _⟩, _⟩, _⟩, _⟩
  have hpw_entry : ∀ blk : Fin 10, ∀ i : Fin 16, vec160Get pw160Vec blk i = p80Nat * vec160Get
      w80Vec blk i := fun blk i ↦ (scalarConsts_lanes blk i).2
  have hS_exp_box : S_exp = ∑ ν ∈ momentumTransferBox62.erase 0,
      ((p80Nat : ℝ) / 2 ^ 80) * laplaceSumReal (normSqInt ν) *
        ∏ j : Fin 3, Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128) := by
    have hprod3 : ∀ (blk : Fin 10) (i : Fin 16), g1DReal blk i w * g1DReal blk i v * g1DReal
        blk i u - 1 = ∑ ν ∈ momentumTransferBox62.erase 0,
        (((vec160Get r80Vec blk i : ℝ) / 2 ^ 80) ^ (normSqInt ν)) * ∏ j : Fin 3, Real.cos
        (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128) := by
      intro blk i
      set r := (vec160Get r80Vec blk i : ℝ) / 2 ^ 80
      have hbox_sum : (∑ ν ∈ momentumTransferBox62,
          r ^ (normSqInt ν) * ∏ j : Fin 3, Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128)) =
          g1DReal blk i w * g1DReal blk i v * g1DReal blk i u := by
        rw [momentumTransferBox62_eq_piFinset]
        have hf : ∀ ν : Fin 3 → ℤ,
            r ^ (normSqInt ν) * (∏ j : Fin 3, Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128)) =
            ∏ j : Fin 3, (r ^ ((ν j).natAbs ^ 2) *
              Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128)) := fun ν ↦ by
          rw [Fin.prod_univ_three, Fin.prod_univ_three]
          unfold normSqInt
          rw [pow_add, pow_add]
          ring
        simp_rw [hf]
        rw [Finset.sum_prod_piFinset (Finset.Icc (-62 : ℤ) 62)
          (fun (j : Fin 3) (a : ℤ) ↦
            r ^ a.natAbs ^ 2 * Real.cos (2 * π * (a : ℝ) * (mVec j : ℝ) / 128)),
          Fin.prod_univ_three]
        dsimp [g1DReal, mVec]
        ring
      have hmem0 : (0 : Fin 3 → ℤ) ∈ momentumTransferBox62 := by
        rw [mem_momentumTransferBox62]; intro _; simp
      have h0term : r ^ (normSqInt 0) *
          (∏ j : Fin 3, Real.cos (2 * π * ((0 : Fin 3 → ℤ) j : ℝ) * (mVec j : ℝ) / 128)) = 1 := by
        unfold normSqInt; simp
      have rotAux := Finset.add_sum_erase momentumTransferBox62 (fun ν ↦ r ^ (normSqInt ν) * ∏
          j : Fin 3, Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128)) hmem0
      linarith
    dsimp [S_exp]
    simp_rw [hprod3, Finset.mul_sum]
    conv_lhs => arg 2; ext blk; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ ↦ ?_
    unfold laplaceSumReal
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun blk _ ↦ ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hpw_entry blk i]
    push_cast
    ring
  have herr_quad : |w128Orbit idx - S_exp| ≤ 1953124 * ((33 : ℝ) / 2 ^ 60) := by
    have hw_erase : w128Orbit idx = ∑ ν ∈ momentumTransferBox62.erase 0,
        coulombKernel ν * ∏ j : Fin 3, Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128) := by
      unfold w128Orbit
      have hmem0 : (0 : Fin 3 → ℤ) ∈ momentumTransferBox62 := by
        rw [mem_momentumTransferBox62]; intro _; simp
      have her := Finset.add_sum_erase momentumTransferBox62 (fun ν ↦ coulombKernel ν * ∏ j :
          Fin 3, Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128)) hmem0
      rw [← her, coulombKernel_zero, zero_mul, zero_add]
    rw [hw_erase, hS_exp_box, ← Finset.sum_sub_distrib]
    calc |∑ ν ∈ momentumTransferBox62.erase 0, _|
        ≤ ∑ ν ∈ momentumTransferBox62.erase 0,
            |coulombKernel ν * ∏ j : Fin 3, Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128) -
             ((p80Nat : ℝ) / 2 ^ 80) * laplaceSumReal (normSqInt ν) *
              ∏ j : Fin 3, Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ν ∈ momentumTransferBox62.erase 0, ((33 : ℝ) / 2 ^ 60) := by
          refine Finset.sum_le_sum fun ν hν ↦ ?_
          rw [Finset.mem_erase] at hν
          rcases hν with ⟨hν0, hν_box⟩
          rw [← sub_mul, abs_mul]
          have hcos_prod_le1 :
              |∏ j : Fin 3, Real.cos (2 * π * (ν j : ℝ) * (mVec j : ℝ) / 128)| ≤ 1 := by
            rw [Fin.prod_univ_three, abs_mul, abs_mul]
            exact real_mul_le_one (real_mul_le_one (Real.abs_cos_le_one _) (abs_nonneg _)
              (Real.abs_cos_le_one _)) (abs_nonneg _) (Real.abs_cos_le_one _)
          have hs_ge1 : 1 ≤ normSqInt ν := by
            by_contra hlt
            unfold normSqInt at hlt
            refine hν0 (funext fun j ↦ ?_)
            fin_cases j
            · exact Int.natAbs_eq_zero.mp (by nlinarith : (ν 0).natAbs = 0)
            · exact Int.natAbs_eq_zero.mp (by nlinarith : (ν 1).natAbs = 0)
            · exact Int.natAbs_eq_zero.mp (by nlinarith : (ν 2).natAbs = 0)
          have hs_le : normSqInt ν ≤ 11532 := by
            rw [mem_momentumTransferBox62] at hν_box
            have h0 := hν_box 0
            have h1 := hν_box 1
            have h2 := hν_box 2
            unfold normSqInt
            nlinarith [Nat.pow_le_pow_left (by omega : (ν 0).natAbs ≤ 62) 2,
              Nat.pow_le_pow_left (by omega : (ν 1).natAbs ≤ 62) 2,
              Nat.pow_le_pow_left (by omega : (ν 2).natAbs ≤ 62) 2]
          rw [coulombKernel_eq_of_ne_zero hν0]
          have hinv_le1 : |(1 : ℝ) / (normSqInt ν : ℝ)| ≤ 1 := by
            rw [abs_of_nonneg (by positivity)]
            exact div_le_one_of_le₀ (by exact_mod_cast hs_ge1) (by positivity)
          have hp_le : |(p80Nat : ℝ) / 2 ^ 80| ≤ (1 : ℝ) / 32 := by
            rw [abs_of_nonneg (by positivity)]
            have hr : 32 * (p80Nat : ℝ) ≤ 2 ^ 80 := by
              unfold b80Nat at hp80_le
              exact_mod_cast hp80_le
            linarith
          have hcoef : |(1 : ℝ) / (π * cellSide) * ((1 : ℝ) / (normSqInt ν : ℝ)) -
              (p80Nat : ℝ) / 2 ^ 80 * laplaceSumReal (normSqInt ν)| ≤ (33 : ℝ) / 2 ^ 60 := by
            rw [show (1 : ℝ) / (π * cellSide) * ((1 : ℝ) / (normSqInt ν : ℝ)) -
                (p80Nat : ℝ) / 2 ^ 80 * laplaceSumReal (normSqInt ν) =
              ((1 : ℝ) / (π * cellSide) - (p80Nat : ℝ) / 2 ^ 80) * ((1 : ℝ) / (normSqInt ν : ℝ)) +
              ((p80Nat : ℝ) / 2 ^ 80) * ((1 : ℝ) / (normSqInt ν : ℝ) -
                laplaceSumReal (normSqInt ν)) by ring]
            have htri := abs_add_le
              (((1 : ℝ) / (π * cellSide) - (p80Nat : ℝ) / 2 ^ 80) * ((1 : ℝ) / (normSqInt ν : ℝ)))
              (((p80Nat : ℝ) / 2 ^ 80) *
                ((1 : ℝ) / (normSqInt ν : ℝ) - laplaceSumReal (normSqInt ν)))
            rw [abs_mul, abs_mul] at htri
            linarith [mul_le_mul abs_prefactor_sub_p80_le hinv_le1 (abs_nonneg _) (by positivity),
              mul_le_mul hp_le (abs_inv_sub_laplace_le hs_ge1 hs_le) (abs_nonneg _)
                (by positivity)]
          exact (mul_le_mul hcoef hcos_prod_le1 (abs_nonneg _) (by positivity)).trans (by norm_num)
      _ = 1953124 * ((33 : ℝ) / 2 ^ 60) := by simp [card_erase_zero_box62]
  have hpw_sum_r : (∑ blk : Fin 10, ∑ i : Fin 16, (vec160Get pw160Vec blk i : ℝ)) =
      (sumPW160Nat : ℝ) := by
    have hs := sum160_eq pw160Vec
    rw [hsum_pw] at hs
    exact_mod_cast hs.symm
  have herr_tab : |S_exp - sTabOrbit idx| ≤ 2 * ((46875 : ℝ) / 2 ^ 56) := by
    dsimp [S_exp, sTabOrbit]
    rw [← Finset.sum_sub_distrib]
    calc |∑ blk : Fin 10, _|
        ≤ ∑ blk : Fin 10, ∑ i : Fin 16,
            |((vec160Get pw160Vec blk i : ℝ) / 2 ^ 160) *
              (g1DReal blk i t.w.val * g1DReal blk i t.v.val * g1DReal blk i t.u.val -
               ((vec160Get (u56Col t.w.val) blk i : ℝ) - 2 ^ 63) / 2 ^ 56 *
               (((vec160Get (u56Col t.v.val) blk i : ℝ) - 2 ^ 63) / 2 ^ 56) *
               (((vec160Get (u56Col t.u.val) blk i : ℝ) - 2 ^ 63) / 2 ^ 56))| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun blk _ ↦ ?_)
          rw [← Finset.sum_sub_distrib]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
          exact le_of_eq (congrArg abs (by ring))
      _ ≤ ∑ blk : Fin 10, ∑ i : Fin 16,
            ((vec160Get pw160Vec blk i : ℝ) / 2 ^ 160) * ((46875 : ℝ) / 2 ^ 56) := by
          refine Finset.sum_le_sum fun blk _ ↦ Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (by positivity)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases g1DReal_bounds blk i t.w.isLt with ⟨_, _, hcw, hgw, hew⟩
          rcases g1DReal_bounds blk i t.v.isLt with ⟨_, _, hcv, hgv, hev⟩
          rcases g1DReal_bounds blk i t.u.isLt with ⟨_, _, _, hgu, heu⟩
          set gw := g1DReal blk i t.w.val
          set gv := g1DReal blk i t.v.val
          set gu := g1DReal blk i t.u.val
          set cw_r := ((vec160Get (u56Col t.w.val) blk i : ℝ) - 2 ^ 63) / 2 ^ 56
          set cv_r := ((vec160Get (u56Col t.v.val) blk i : ℝ) - 2 ^ 63) / 2 ^ 56
          set cu_r := ((vec160Get (u56Col t.u.val) blk i : ℝ) - 2 ^ 63) / 2 ^ 56
          have htel : gw * gv * gu - cw_r * cv_r * cu_r =
              (gw - cw_r) * (gv * gu) + cw_r * ((gv - cv_r) * gu) +
              (cw_r * cv_r) * (gu - cu_r) := by ring
          rw [htel]
          have hterm {x y z : ℝ} (hx : |x| ≤ 1 / 2 ^ 56) (hy : |y| ≤ 125) (hz : |z| ≤ 125) :
              |x * (y * z)| ≤ (15625 : ℝ) / 2 ^ 56 := by
            rw [abs_mul, abs_mul]
            have hp : |y| * |z| ≤ 15625 :=
              (mul_le_mul hy hz (abs_nonneg _) (by positivity)).trans (by norm_num)
            linarith [mul_le_mul hx hp (by positivity) (by positivity)]
          have h1 := hterm hew hgv hgu
          have h2 : |cw_r * ((gv - cv_r) * gu)| ≤ (15625 : ℝ) / 2 ^ 56 := by
            rw [mul_left_comm]; exact hterm hev hcw hgu
          have h3 : |(cw_r * cv_r) * (gu - cu_r)| ≤ (15625 : ℝ) / 2 ^ 56 := by
            rw [mul_comm]; exact hterm heu hcw hcv
          linarith [abs_add_le ((gw - cw_r) * (gv * gu) + cw_r * ((gv - cv_r) * gu))
            ((cw_r * cv_r) * (gu - cu_r)),
            abs_add_le ((gw - cw_r) * (gv * gu)) (cw_r * ((gv - cv_r) * gu))]
      _ ≤ 2 * ((46875 : ℝ) / 2 ^ 56) := by
          have hfactor : (∑ blk : Fin 10, ∑ i : Fin 16, ((vec160Get pw160Vec blk i : ℝ) / 2 ^
              160) * ((46875 : ℝ) / 2 ^ 56)) = ((sumPW160Nat : ℝ) / 2 ^ 160) *
              ((46875 : ℝ) / 2 ^ 56) := by
            rw [← hpw_sum_r, Finset.sum_div, Finset.sum_mul]
            exact Finset.sum_congr rfl fun blk _ ↦ by rw [Finset.sum_div, Finset.sum_mul]
          rw [hfactor]
          have hpw_r : (sumPW160Nat : ℝ) ≤ 2 * (2 ^ 80 : ℝ) * (2 ^ 80 : ℝ) := by
            unfold b80Nat at hpw_le; exact_mod_cast hpw_le
          linarith
  have herr_round := abs_sTabOrbit_sub_q30_le idx
  have hnum : 1953124 * ((33 : ℝ) / 2 ^ 60) + 2 * ((46875 : ℝ) / 2 ^ 56) + (1 : ℝ) / 2 ^ 31 ≤
      (5615 : ℝ) / (10000 * 2 ^ 30) := by norm_num
  have htri1 := abs_sub_le (w128Orbit idx) S_exp ((w128OrbitQ30 idx : ℝ) / 2 ^ 30)
  have htri2 := abs_sub_le S_exp (sTabOrbit idx) ((w128OrbitQ30 idx : ℝ) / 2 ^ 30)
  linarith

theorem abs_w128OrbitQ30Real_sub_le_tight (idx : Fin orbitCount47905) :
    |w128OrbitQ30Real idx - w128Orbit idx| ≤ (5615 : ℝ) / (10000 * 2 ^ 30) := by
  unfold w128OrbitQ30Real
  rw [abs_sub_comm]
  exact abs_w128Orbit_sub_q30_le_tight idx

/- ## Section 2: Tight `Slot 4` (`V_ee`) Fermionic Bridges (`eps4_q30_tight`) -/

/-- Tightened `Slot 4` (`V_ee`) `Q30` orbit-quantization error cap `23653 * 0.5615 / 2^30`
  (`12.369 uHa`). -/
noncomputable def eps4_q30_tight : ℝ := (23653 * 5615 : ℝ) / (10000 * 2 ^ 30)

theorem agreesOnFermionicSector_slot4SymRef_q30Tight (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) (E : Fin 6 → ℝ) (hE4 : E 4 = pos80Slot4EShift) :
    AgreesOnFermionicSector spinUp (gridProjector * s4S * gridProjector)
    (sixChannelShifted c E 4) eps4_q30_tight := by
  have hraw : AgreesOnFermionicSector spinUp
      (gridProjector * veeSingleAnchorRaw w128DualQ30 * gridProjector) (gridProjector *
      veeSingleAnchorRaw coulombDual128Real * gridProjector) eps4_q30_tight := by
    have hbound : ‖veeSingleAnchorRaw w128DualQ30 - veeSingleAnchorRaw coulombDual128Real‖ ≤
        23653 * ((5615 : ℝ) / (10000 * 2 ^ 30)) :=
      norm_veeSingleAnchorRaw_sub_le w128DualQ30 coulombDual128Real (by positivity) fun d ↦ by
        rw [coulombDual128Real_eq_orbit d]
        exact abs_w128OrbitQ30Real_sub_le_tight (tetRank65 (canonTriple128 d))
    rw [← show (23653 : ℝ) * ((5615 : ℝ) / (10000 * 2 ^ 30)) = eps4_q30_tight by
      unfold eps4_q30_tight; ring]
    exact ag_g4 (veeSingleAnchorRaw_comm_perm w128DualQ30) hbound
  have hG_lhs : gridProjector * s4S * gridProjector = gridProjector * veeSingleAnchorRaw
      w128DualQ30 * gridProjector - (pos80Slot4EShift : ℂ) • gridProjector := by
    unfold s4S
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      gridProjector_mul_self]
  have hG_rhs : sixChannelShifted c E 4 = gridProjector * veeSingleAnchorRaw
      coulombDual128Real * gridProjector - (pos80Slot4EShift : ℂ) • gridProjector := by
    rw [sixChannelShifted, sixChannelGridProjector_eq_specsGridProjector, hE4,
      ← vEeManyBody_eq_sixChannelRaw c, ← gridSandwich_veeSingleAnchorRaw_coulomb_eq]
  rw [hG_lhs, hG_rhs]
  have hGP_comm : gridProjector * fermionicProjector spinUp =
      fermionicProjector spinUp * gridProjector :=
    (gridProjector_mul_fermionicProjector spinUp).trans
      (fermionicProjector_mul_gridProjector spinUp).symm
  refine ⟨by
    rw [Matrix.sub_mul, Matrix.mul_sub, hraw.1, Matrix.smul_mul, Matrix.mul_smul, hGP_comm], ?_⟩
  rw [show (gridProjector * veeSingleAnchorRaw w128DualQ30 * gridProjector -
        (pos80Slot4EShift : ℂ) • gridProjector) -
      (gridProjector * veeSingleAnchorRaw coulombDual128Real * gridProjector -
        (pos80Slot4EShift : ℂ) • gridProjector) =
      gridProjector * veeSingleAnchorRaw w128DualQ30 * gridProjector -
        gridProjector * veeSingleAnchorRaw coulombDual128Real * gridProjector by abel]
  exact hraw.2

theorem tierBB4Id_agreesOnFermionicSector_q30Tight
    (c : Configuration) (spinUp0 : Finset (Fin numElectrons)) :
    let E4only : Fin 6 → ℝ := fun q ↦ if q = 4 then pos80Slot4EShiftFn c else 0
    AgreesOnFermionicSector spinUp0
      (gridProjector *
        ((pos80Slot4Scale : ℂ) • (smToTwosSysUnitary.1 * tierBB4Id c * smToTwosSysUnitary.1)) *
        gridProjector)
      (sixChannelShifted c E4only 4)
      eps4_q30_tight := by
  let M₁ : Operator (2 ^ systemQubits) := (pos80Slot4Scale : ℂ) •
      (smToTwosSysUnitary.1 * coherentSysOp80 tierBQftFull c true (pos80IdealDist true) *
        smToTwosSysUnitary.1)
  have hCoh_herm := coherentSysOp80_isHermitian tierBQftFull c true (pos80IdealDist true)
  have hM₁_herm : M₁.IsHermitian := by
    refine ih_sm pos80Slot4Scale ?_
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      smToTwosSysUnitary_conjTranspose, hCoh_herm.eq, Matrix.mul_assoc]
  have htr := agreesOnFermionicSector_trans
    (agreesOnFermionicSector_gridSandwich_of_mul_eq hM₁_herm s4_ih (fun g _ ↦ s4_cp g)
      (c4_fp tierBQftFull rfl c spinUp0))
    (agreesOnFermionicSector_slot4SymRef_q30Tight c spinUp0
      (fun q ↦ if q = 4 then pos80Slot4EShiftFn c else 0) rfl)
  rwa [zero_add] at htr

theorem bModSlot248_collapse_proj (c' c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let P := fermionicProjector spinUp
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    P * (bModSlot248 c' - sixChannelShifted c E2only 2) * P =
      P * (uenSubGridRaw48 c' w128DualQ30 - uenSubGridRaw c coulombDual128Real) * P := by
  intro P E2only
  let G := gridProjector
  have hPG : P * G = P := fermionicProjector_mul_gridProjector spinUp
  have hGP : G * P = P := gridProjector_mul_fermionicProjector spinUp
  unfold bModSlot248
  rw [sixChannelShifted, sixChannelGridProjector_eq_specsGridProjector,
    show E2only 2 = pos24Slot2E2Const from rfl,
    ← uEnManyBody_eq_sixChannelRaw c, ← gridSandwich_uenSubGridRaw_coulomb_eq c]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [show P * (G * uenSubGridRaw c coulombDual128Real * G) * P =
      (P * G) * uenSubGridRaw c coulombDual128Real * (G * P) by simp only [Matrix.mul_assoc],
    show P * G * P = (P * G) * P from rfl, hPG, hGP]
  abel

theorem bModSlot248_shifted_err_le_tight (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 c - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (257 : ℝ) / 10000000 := by
  intro E2only
  let P := fermionicProjector spinUp
  have hP_le : ‖P‖ ≤ 1 :=
    norm_projector_le_one P (fermionicProjector_isHermitian spinUp) (fermionicProjector_idem spinUp)
  rw [bModSlot248_collapse_proj c c spinUp,
    show uenSubGridRaw48 c w128DualQ30 - uenSubGridRaw c coulombDual128Real =
      (uenSubGridRaw48 c w128DualQ30 - uenSubGridRaw c w128DualQ30) +
      (uenSubGridRaw c w128DualQ30 - uenSubGridRaw c coulombDual128Real) by abel,
    Matrix.mul_add, Matrix.add_mul]
  have h48 := norm_proj_sandwich_le_part4A P _ (by positivity) hP_le
    (norm_uenSubGridRaw48_sub_exact_le c)
  have hq30_raw : ‖uenSubGridRaw c w128DualQ30 - uenSubGridRaw c coulombDual128Real‖ ≤
      47088 * ((5615 : ℝ) / (10000 * 2 ^ 30)) :=
    norm_uenSubGridRaw_sub_le c w128DualQ30 coulombDual128Real (by positivity) fun d ↦ by
      rw [coulombDual128Real_eq_w128Dual d]
      unfold w128DualQ30
      rw [w128Dual_eq_orbit]
      exact abs_w128OrbitQ30Real_sub_le_tight _
  have hq30 := norm_proj_sandwich_le_part4A P _ (by positivity) hP_le hq30_raw
  exact (norm_add_le _ _).trans ((add_le_add h48 hq30).trans (by norm_num))

theorem tierBB2Id_trunc_intrinsic_agrees_tight
    (truncCfg : Configuration → Configuration)
    (htruncProj : ∀ zP : NyqFine3D512, truncCfg (cfgProjZ512 zP) = cfgProjZ512 zP)
    (hsecEq : ∀ c : Configuration,
      mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) c =
        mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) (truncCfg c))
    {epsRaw eps2 : ℝ}
    (hErrRaw : ∀ (c : Configuration) (spinUp0 : Finset (Fin numElectrons)),
      let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
      ‖fermionicProjector spinUp0 * (bModSlot248 (truncCfg c) - sixChannelShifted c E2only 2) *
        fermionicProjector spinUp0‖ ≤ epsRaw)
    (heps_comb : epsRaw + (1 / 108 : ℝ) * ((257 : ℝ) / 10000000) ≤ (109 / 108 : ℝ) * eps2)
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
    (E_sp : Fin 6 → ℝ)
    (hEsp2 : E_sp 2 = pos24Slot2E2Const)
    (hEsp5 : E_sp 5 = pos24Slot2E2Const / 108) :
    AgreesOnFermionicSector spinUp
      (gridProjector *
        ((mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg : ℂ) •
          (smToTwosSysUnitary.1 * tierBB2Id (truncCfg cfg) * smToTwosSysUnitary.1)) *
        gridProjector)
      (sixChannelShifted cfg E_sp 2 + sixChannelShifted cfg E_sp 5)
      ((109 / 108 : ℝ) * eps2) := by
  let B_mod : Configuration → Operator (2 ^ systemQubits) := fun c ↦ bModSlot248 (truncCfg c)
  let A : Configuration → Operator (2 ^ systemQubits) := fun c ↦
    (pos80Slot2Scale : ℂ) • (smToTwosSysUnitary.1 * tierBB2RawId c * smToTwosSysUnitary.1)
  have hIdleA : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ 24)),
      A (cfgProjZ512 zP) * rProj24_sp.embedMatrix M =
        rProj24_sp.embedMatrix M * A (cfgProjZ512 zP) := fun zP M ↦ by
    dsimp only [A]
    rw [Matrix.smul_mul, Matrix.mul_smul,
      smConj_comm_embedMatrix_of_idleTwos (tierBB2RawId_comm_rProj24 (cfgProjZ512 zP)) M]
  have hIdleMod : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ 24)),
      B_mod (cfgProjZ512 zP) * rProj24_sp.embedMatrix M =
        rProj24_sp.embedMatrix M * B_mod (cfgProjZ512 zP) := fun zP M ↦ by
    dsimp only [B_mod]; rw [htruncProj zP]; exact bModSlot248_comm_rProj24 (cfgProjZ512 zP) M
  have hVepEq : vepFromSlot2Op A * fermionicProjector spinUp = vepFromSlot2Op B_mod *
      fermionicProjector spinUp :=
    vepFromSlot2Op_mul_fermionicProjector_eq spinUp hIdleA hIdleMod fun zP ↦ by
      dsimp only [A, B_mod]; rw [htruncProj zP]
      exact tierBB2RawId_mul_fermionicProjector_eq (cfgProjZ512 zP) spinUp
  let G := gridProjector
  let w2 := mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg
  let M₁ : Operator (2 ^ systemQubits) :=
    G * ((w2 : ℂ) • (smToTwosSysUnitary.1 * tierBB2Id (truncCfg cfg) * smToTwosSysUnitary.1)) * G
  let M₂ : Operator (2 ^ systemQubits) := G * B_mod cfg * G + G * vepFromSlot2Op B_mod * G
  have hM₁_split : M₁ = G * A (truncCfg cfg) * G + G * vepFromSlot2Op A * G := by
    dsimp only [M₁, w2, A]; rw [hsecEq cfg]; unfold tierBB2Id
    rw [mergedPosSlot2Gen_smConj_eq (by positivity : (0 : ℝ) < 108 / 109) pos80Slot2Scale
        tierBB2RawId (fun zP M ↦ tierBB2RawId_comm_rProj24 (cfgProjZ512 zP) M) (truncCfg cfg),
      Matrix.mul_add, Matrix.add_mul]
  have hM₁_herm : M₁.IsHermitian := by
    refine isHermitian_gridSandwich_slot2 (isHermitian_real_smul_slot2 w2 ?_)
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      smToTwosSysUnitary_sa, (tierBB2Id_isHermitian (truncCfg cfg)).eq, Matrix.mul_assoc]
  have hM₂_herm : M₂.IsHermitian := (isHermitian_gridSandwich_slot2 (bModSlot248_isHermitian
      (truncCfg cfg))).add (isHermitian_gridSandwich_slot2 (vepFromSlot2Op_isHermitian_of_idle
      (fun zP ↦ bModSlot248_isHermitian (truncCfg (cfgProjZ512 zP))) hIdleMod))
  have hGP : G * fermionicProjector spinUp = fermionicProjector spinUp :=
    gridProjector_mul_fermionicProjector spinUp
  have hMulEq : M₁ * fermionicProjector spinUp = M₂ * fermionicProjector spinUp := by
    rw [hM₁_split]; dsimp only [M₂]
    calc (G * A (truncCfg cfg) * G + G * vepFromSlot2Op A * G) * fermionicProjector spinUp
        = G * (A (truncCfg cfg) * (G * fermionicProjector spinUp)) +
            G * (vepFromSlot2Op A * (G * fermionicProjector spinUp)) := by
            rw [add_mul]; simp only [Matrix.mul_assoc]
      _ = G * (B_mod cfg * fermionicProjector spinUp) +
            G * (vepFromSlot2Op B_mod * fermionicProjector spinUp) := by
            rw [hGP, tierBB2RawId_mul_fermionicProjector_eq (truncCfg cfg) spinUp, hVepEq]
      _ = G * (B_mod cfg * (G * fermionicProjector spinUp)) +
            G * (vepFromSlot2Op B_mod * (G * fermionicProjector spinUp)) := by rw [hGP]
      _ = (G * B_mod cfg * G + G * vepFromSlot2Op B_mod * G) * fermionicProjector spinUp := by
            rw [add_mul]; simp only [Matrix.mul_assoc]
  have hSlot2 := agreesOnFermionicSector_gridSandwich_slot2Mod B_mod pos24Slot2E2Const
    (fun c g a b ha hb ↦ bModSlot248_inGridPerm (truncCfg c) g a b ha hb)
    hErrRaw cfg spinUp E_sp hEsp2
  have hSlot5 := vepFromSlot2_agreesOnFermionicSector cfg spinUp E_sp
    (by positivity : (0 : ℝ) ≤ 257 / 10000000)
    (by rw [hEsp2, hEsp5]) B_mod hIdleMod
    (fun zP g a b ha hb ↦ bModSlot248_inGridPerm (truncCfg (cfgProjZ512 zP)) g a b ha hb)
    fun zP ↦ by
      dsimp only [B_mod]; rw [htruncProj zP]
      rw [show sixChannelShifted (cfgProjZ512 zP) E_sp 2 = sixChannelShifted
          (cfgProjZ512 zP) (fun q : Fin 6 ↦ if q = 2 then pos24Slot2E2Const else 0) 2 by
        unfold sixChannelShifted; rw [hEsp2]; rfl]
      exact bModSlot248_shifted_err_le_tight (cfgProjZ512 zP) spinUp
  refine agreesOnFermionicSector_of_isHermitian_and_mul_eq hM₁_herm hM₂_herm hMulEq
    ⟨by rw [add_mul, mul_add, hSlot2.1, hSlot5.1], ?_⟩
  let P := fermionicProjector spinUp
  change ‖P * ((_ + _) - (_ + _)) * P‖ ≤ _
  rw [show (G * B_mod cfg * G + G * vepFromSlot2Op B_mod * G) -
        (sixChannelShifted cfg E_sp 2 + sixChannelShifted cfg E_sp 5) =
      (G * B_mod cfg * G - sixChannelShifted cfg E_sp 2) +
        (G * vepFromSlot2Op B_mod * G - sixChannelShifted cfg E_sp 5) by abel,
    Matrix.mul_add, Matrix.add_mul]
  exact (norm_add_le _ _).trans ((add_le_add hSlot2.2 hSlot5.2).trans heps_comb)

set_option exponentiation.threshold 256
set_option maxRecDepth 2000

end ConfigPosSlots24Q30Tight

end PosSlots24Q30Tight
end
set_option exponentiation.threshold 256
end PosSlots24Q30Tight

section SubvoxelNuclearTrunc34And33PhysicsAux
local instance (priority := 1000000) instNeZeroTwoPow_SubvoxelNuclearTrunc34And33Physics (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩


public section
section SubvoxelNuclearTrunc34And33Physics

section ModSubvoxelNuclearTrunc34And33Physics
public section
namespace SubvoxelNuclearTrunc34And33Physics
section ConfigSubvoxelNuclearTrunc34And33Physics
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option exponentiation.threshold 256
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority :=
  1000000) instLoc_SubvoxelNuclearTrunc34And33Physics_1InstNeZe (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner (fermionicProjector_idem)
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
open SpecsAux.DyadicSubgridToeplitz128 (InMomGrid1D InMomGrid3D inMomGrid3D_electron_of_state
  oneElectronPhase oneElectronPhase_mul_star shiftedMom3D shiftedFin64ToInt uEnManyBody)
open OctahedralOrbit Dyadic128CoulombMath
open Dyadic128OrbitTableCert (withStrictNat withStrictNat_eq cellSide cellSide_pos cellSide_cubed
  normSqInt coulombKernel_eq_of_ne_zero)
open SingleAnchorFermionicPauliCap (rEl_sp rk1_sp op_sp nSub_sp nSub_isHermitian_any
  nSub_mul_self_mul_fermionicProjector)
open Slot2Slot4QuantizedChannelBridge (elecOffsetGridEquiv18 embedMatrix_sum
  norm_conj_diagonal_of_real_le norm_sum_op_sp_le_of_orthonormal agreeOutside_rEl_sp_iff_momentum
  shiftedMom3D_elecOffsetGridEquiv18_extractIndex uEnManyBody_eq_sixChannelRaw)
open NuclearTwistAndXor654Concrete (oneElecNucDiagExact)
open PosSlots24MergedVepBound (cellLength_ne_zero)
open Pos24Slot2FermionicBridge (pos24Slot2E2Const bModSlot248)
open PosSlots24Q30Tight (bModSlot248_shifted_err_le_tight)
noncomputable def nuclearMW (W : ℕ) (c : Configuration) (l : Fin 216) (w : Fin 3) : ℕ :=
  ⌊(2 ^ W : ℝ) * Int.fract (c.nuclei l w / cellVolume ^ ((1 : ℝ) / 3)) + 1 / 2⌋₊ % 2 ^ W
theorem nuclearMW_lt (W : ℕ) (c : Configuration) (l : Fin 216) (w : Fin 3) : nuclearMW W c l w
    < 2 ^ W := Nat.mod_lt _ (Nat.two_pow_pos W)
noncomputable def truncWCfg (W : ℕ) (c : Configuration) : Configuration where
  nuclei := fun l w ↦ (nuclearMW W c l w : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / (2 ^ W : ℝ))
  projectileMomentum := c.projectileMomentum
  momentum_le := c.momentum_le
noncomputable def lLoRat : ℝ := (134251603 : ℝ) / 10000000
theorem lLoRat_pos : 0 < lLoRat := by
  unfold lLoRat; norm_num
theorem lLoRat_le_cellSide : lLoRat ≤ cellSide := by
  by_contra hlt
  have hpow : cellSide ^ 3 < lLoRat ^ 3 :=
    pow_lt_pow_left₀ (lt_of_not_ge hlt) cellSide_pos.le (by norm_num)
  rw [cellSide_cubed] at hpow
  linarith [show lLoRat ^ 3 ≤ cellVolume by unfold lLoRat cellVolume; norm_num]
theorem star_mul_self_re_eq_norm_sq (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [mul_comm, RCLike.star_def, Complex.mul_conj', ← Complex.ofReal_pow ‖z‖ 2, Complex.ofReal_re]
noncomputable def rk1Gen {d : ℕ} (χ : Fin d → ℂ) : Operator d :=
  Matrix.of fun u v ↦ χ u * star (χ v)
theorem conj_rk1Gen {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (φ : Fin d → ℂ) :
    M * rk1Gen φ * Mᴴ = rk1Gen (fun u ↦ ∑ a : Fin d, M u a * φ a) := by
  ext u v
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rk1Gen, Matrix.of_apply]
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [star_mul']
  ring
theorem hermitian_spectral_columns {d : ℕ} (H : Operator d) (hH : H.IsHermitian) :
    let U : Operator d := (hH.eigenvectorUnitary : Operator d)
    let lam : Fin d → ℝ := hH.eigenvalues
    let φ : Fin d → Fin d → ℂ := fun k u ↦ U u k
    U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      (∀ a b : Fin d, ∑ u : Fin d, star (φ a u) * φ b u = if a = b then 1 else 0) ∧
      (∀ u v : Fin d, ∑ k : Fin d, φ k u * star (φ k v) = if u = v then 1 else 0) ∧
      H = U * Matrix.diagonal (fun k ↦ (lam k : ℂ)) * Uᴴ ∧
      H = ∑ k : Fin d, (lam k : ℂ) • rk1Gen (φ k) := by
  intro U lam φ
  have hUUh : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hUhU : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have horth (a b : Fin d) : ∑ u : Fin d, star (φ a u) * φ b u = if a = b then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, φ] using
      congrFun (congrFun hUhU a) b
  have hcomp (u v : Fin d) : ∑ k : Fin d, φ k u * star (φ k v) = if u = v then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, φ] using
      congrFun (congrFun hUUh u) v
  have hspec : H = U * Matrix.diagonal (fun k ↦ (lam k : ℂ)) * Uᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    exact congrArg (fun M ↦ U * M * Uᴴ) (congrArg Matrix.diagonal (funext fun _ ↦ rfl))
  have hrk : H = ∑ k : Fin d, (lam k : ℂ) • rk1Gen (φ k) := by
    rw [hspec]; ext u v; rw [Matrix.mul_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.mul_diagonal]
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, rk1Gen, Matrix.of_apply,
      smul_eq_mul, φ]
    ring
  exact ⟨hUUh, hUhU, horth, hcomp, hspec, hrk⟩
theorem hermitian_eigenvalues_sq_sum_eq_frob {d : ℕ} (H : Operator d) (hH : H.IsHermitian) :
    (∑ k : Fin d, (hH.eigenvalues k) ^ 2) = ∑ u : Fin d, ∑ v : Fin d, ‖H u v‖ ^ 2 := by
  obtain ⟨_hUUh, hUhU, horth, _hcomp, hspec, _hrk⟩ := hermitian_spectral_columns H hH
  set U : Operator d := (hH.eigenvectorUnitary : Operator d)
  set lam : Fin d → ℝ := hH.eigenvalues
  set D : Operator d := Matrix.diagonal (fun k ↦ (lam k : ℂ))
  have hH2_lhs : (∑ u : Fin d, ((Hᴴ * H) u u).re) = ∑ u : Fin d, ∑ v : Fin d, ‖H u v‖ ^ 2 := by
    have h1 : ∀ u : Fin d, ((Hᴴ * H) u u).re = ∑ v : Fin d, ‖H v u‖ ^ 2 := fun u ↦ by
      rw [Matrix.mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [Matrix.conjTranspose_apply, star_mul_self_re_eq_norm_sq]
    simp_rw [h1]
    exact Finset.sum_comm
  have hD2 : D * D = Matrix.diagonal (fun k ↦ ((lam k ^ 2 : ℝ) : ℂ)) := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext k; push_cast; ring
  have hH2_eq : Hᴴ * H = U * Matrix.diagonal (fun k ↦ ((lam k ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hH.eq]
    conv_lhs => rw [hspec]
    calc (U * D * Uᴴ) * (U * D * Uᴴ)
        = U * (D * (Uᴴ * U) * D) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * (D * D) * Uᴴ := by rw [hUhU, Matrix.mul_one]
      _ = U * Matrix.diagonal (fun k ↦ ((lam k ^ 2 : ℝ) : ℂ)) * Uᴴ := by rw [hD2]
  have hH2_rhs : (∑ u : Fin d, ((Hᴴ * H) u u).re) = ∑ k : Fin d, (lam k) ^ 2 := by
    rw [hH2_eq]
    have hdiag_u : ∀ u : Fin d,
        (U * Matrix.diagonal (fun k ↦ ((lam k ^ 2 : ℝ) : ℂ)) * Uᴴ) u u =
          ∑ k : Fin d, ((lam k ^ 2 : ℝ) : ℂ) * (star (U u k) * U u k) := fun u ↦ by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Matrix.mul_apply]
      simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, Matrix.conjTranspose_apply]
      ring
    simp_rw [hdiag_u, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← Complex.re_sum, ← Finset.mul_sum, horth k k]
    simp only [↓reduceIte, mul_one, Complex.ofReal_re]
  linarith
theorem chiral_sign_eigenvalues_sq_sum_le_half_frob {d : ℕ} (H : Operator d)
    (hH : H.IsHermitian) (hImag : ∀ u v : Fin d, star (H u v) = -H u v) (sgn : ℝ)
    (hsgn : sgn = 1 ∨ sgn = -1) : 2 * (∑ k ∈ Finset.univ.filter (fun k : Fin d ↦ 0 < sgn *
    hH.eigenvalues k), (hH.eigenvalues k) ^ 2) ≤ ∑ u : Fin d, ∑ v : Fin d, ‖H u v‖ ^ 2 := by
  obtain ⟨_hUUh, hUhU, horth, hcomp, hspec, _hrk⟩ := hermitian_spectral_columns H hH
  set U : Operator d := (hH.eigenvectorUnitary : Operator d)
  set lam : Fin d → ℝ := hH.eigenvalues
  let φ : Fin d → Fin d → ℂ := fun k u ↦ U u k
  let ψ : Fin d → Fin d → ℂ := fun k u ↦ star (φ k u)
  let c : Fin d → Fin d → ℂ := fun k j ↦ ∑ u : Fin d, star (φ j u) * ψ k u
  let K_s := Finset.univ.filter (fun k : Fin d ↦ 0 < sgn * lam k)
  have hHU : H * U = U * Matrix.diagonal (fun k ↦ (lam k : ℂ)) := by
    conv_lhs => rw [hspec]
    rw [Matrix.mul_assoc, hUhU, Matrix.mul_one]
  have hHeig : ∀ (j u : Fin d), ∑ v : Fin d, H u v * φ j v = (lam j : ℂ) * φ j u := fun j u ↦ by
    have h1 := congrFun (congrFun hHU u) j
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at h1
    simpa only [φ, mul_comm] using h1
  have hHpsi : ∀ (k u : Fin d), ∑ v : Fin d, H u v * ψ k v = (-(lam k) : ℂ) * ψ k u := fun k u ↦ by
    have hst := congrArg star (hHeig k u)
    simp only [star_sum, star_mul', RCLike.star_def, Complex.conj_ofReal] at hst
    simp_rw [← RCLike.star_def, hImag u _, neg_mul] at hst
    rw [Finset.sum_neg_distrib] at hst
    have hneg := congrArg Neg.neg hst
    simpa only [neg_neg, ψ, Complex.ofReal_neg, neg_mul] using hneg
  have hc_eig : ∀ k j : Fin d, ((lam j + lam k : ℝ) : ℂ) * c k j = 0 := fun k j ↦ by
    have hS1 : (∑ u : Fin d, ∑ v : Fin d, star (φ j u) * (H u v * ψ k v)) =
        (-(lam k) : ℂ) * c k j := by
      simp_rw [← Finset.mul_sum, hHpsi k _, ← mul_assoc, mul_comm (star (φ j _)) (-(lam k) : ℂ),
        mul_assoc]
      rw [← Finset.mul_sum]
    have hS2 : (∑ u : Fin d, ∑ v : Fin d, star (φ j u) * (H u v * ψ k v)) =
        (lam j : ℂ) * c k j := by
      rw [Finset.sum_comm]
      have hv : ∀ v : Fin d, (∑ u : Fin d, star (φ j u) * (H u v * ψ k v)) =
          ((lam j : ℂ) * star (φ j v)) * ψ k v := fun v ↦ by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul]
        congr 1
        have hcol : ∀ u : Fin d, star (φ j u) * H u v = star (H v u * φ j u) := fun u ↦ by
          have hh : H u v = star (H v u) := by
            have := congrFun (congrFun hH.eq u) v
            simpa only [Matrix.conjTranspose_apply] using this.symm
          rw [hh, star_mul', mul_comm]
        simp_rw [hcol, ← star_sum, hHeig j v, star_mul', RCLike.star_def, Complex.conj_ofReal]
      simp_rw [hv, mul_assoc]
      rw [← Finset.mul_sum]
    have hsub : (lam j : ℂ) * c k j - (-(lam k) : ℂ) * c k j = 0 := by rw [← hS2, ← hS1, sub_self]
    calc ((lam j + lam k : ℝ) : ℂ) * c k j
        = (lam j : ℂ) * c k j - (-(lam k) : ℂ) * c k j := by push_cast; ring
      _ = 0 := hsub
  have hc_sq_eq : ∀ k j : Fin d, (lam k) ^ 2 * ‖c k j‖ ^ 2 = (lam j) ^ 2 * ‖c k j‖ ^ 2 :=
    fun k j ↦ by
      rcases mul_eq_zero.mp (hc_eig k j) with hsum0 | hc0
      · have hreal : lam j + lam k = 0 := Complex.ofReal_eq_zero.mp hsum0
        have hlk : lam k = -lam j := by linarith
        rw [hlk, neg_sq]
      · rw [hc0, norm_zero, zero_pow (by decide), mul_zero, mul_zero]
  have hc_same_zero : ∀ k ∈ K_s, ∀ j ∈ K_s, c k j = 0 := fun k hk j hj ↦ by
    simp only [K_s, Finset.mem_filter, Finset.mem_univ, true_and] at hk hj
    have hne : ((lam j + lam k : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      rcases hsgn with rfl | rfl <;> linarith
    exact (mul_eq_zero.mp (hc_eig k j)).resolve_left hne
  have hc_row_sum : ∀ k : Fin d, (∑ j : Fin d, ‖c k j‖ ^ 2) = 1 := fun k ↦ by
    have hC : (∑ j : Fin d, star (c k j) * c k j) = 1 := by
      have hexp : ∀ j : Fin d, star (c k j) * c k j =
          ∑ u : Fin d, ∑ v : Fin d, star (ψ k u) * (φ j u * star (φ j v)) * ψ k v := fun j ↦ by
        dsimp only [c]
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [star_mul', star_star]
        ring
      simp_rw [hexp]
      rw [Finset.sum_comm]
      have hu : ∀ u : Fin d,
          (∑ j : Fin d, ∑ v : Fin d, star (ψ k u) * (φ j u * star (φ j v)) * ψ k v) =
            star (ψ k u) * ψ k u := fun u ↦ by
        rw [Finset.sum_comm]
        have hsum_v : ∀ v : Fin d,
            (∑ j : Fin d, star (ψ k u) * (φ j u * star (φ j v)) * ψ k v) =
              if u = v then star (ψ k u) * ψ k v else 0 := fun v ↦ by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hcomp u v, mul_ite, mul_one, mul_zero,
            ite_mul, zero_mul]
        rw [Finset.sum_congr rfl fun v _ ↦ hsum_v v, Finset.sum_ite_eq,
          ite_eq_left_iff.mpr fun h ↦ absurd (Finset.mem_univ u) h]
      rw [Finset.sum_congr rfl fun u _ ↦ hu u]
      have hpsi_norm : ∀ u : Fin d, star (ψ k u) * ψ k u = star (φ k u) * φ k u := fun u ↦ by
        dsimp only [ψ]; rw [star_star, mul_comm]
      rw [Finset.sum_congr rfl fun u _ ↦ hpsi_norm u]
      simpa using horth k k
    have hre := congrArg Complex.re hC
    simpa only [Complex.re_sum, star_mul_self_re_eq_norm_sq, Complex.one_re] using hre
  have hpsi_orth : ∀ a b : Fin d, ∑ u : Fin d, star (ψ a u) * ψ b u = if a = b then 1 else 0 :=
    fun a b ↦ by
      have h1 : ∀ u : Fin d, star (ψ a u) * ψ b u = star (φ b u) * φ a u := fun u ↦ by
        dsimp only [ψ]; rw [star_star, mul_comm]
      rw [Finset.sum_congr rfl fun u _ ↦ h1 u, horth b a]
      exact if_congr eq_comm rfl rfl
  have hc_col_le : ∀ j : Fin d, (∑ k ∈ K_s, ‖c k j‖ ^ 2) ≤ 1 := fun j ↦ by
    let r : Fin d → ℂ := fun u ↦ φ j u - ∑ k ∈ K_s, star (c k j) * ψ k u
    have hr_nn : 0 ≤ ∑ u : Fin d, ‖r u‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hr_eq : (∑ u : Fin d, star (r u) * r u) = 1 - ∑ k ∈ K_s, star (c k j) * c k j := by
      have hexp (u : Fin d) : star (r u) * r u =
          star (φ j u) * φ j u -
            (∑ k ∈ K_s, star (c k j) * (star (φ j u) * ψ k u)) -
            (∑ k ∈ K_s, c k j * (star (ψ k u) * φ j u)) +
            ∑ a ∈ K_s, ∑ b ∈ K_s, (c a j * star (c b j)) * (star (ψ a u) * ψ b u) := by
        let S : ℂ := ∑ k ∈ K_s, star (c k j) * ψ k u
        have hS1 : star (φ j u) * S = ∑ k ∈ K_s, star (c k j) * (star (φ j u) * ψ k u) := by
          dsimp only [S]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
        have hS2 : star S * φ j u = ∑ k ∈ K_s, c k j * (star (ψ k u) * φ j u) := by
          dsimp only [S]
          rw [star_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ ↦ by
            rw [star_mul, star_star, star_star]
            ring
        have hS3 : star S * S =
            ∑ a ∈ K_s, ∑ b ∈ K_s, (c a j * star (c b j)) * (star (ψ a u) * ψ b u) := by
          dsimp only [S]
          rw [star_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun _ _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ ↦ by
            rw [star_mul, star_star, star_star]
            ring
        change star (φ j u - S) * (φ j u - S) = _
        rw [star_sub, show (star (φ j u) - star S) * (φ j u - S) =
            star (φ j u) * φ j u - star (φ j u) * S - star S * φ j u + star S * S by ring,
          hS1, hS2, hS3]
      rw [Finset.sum_congr rfl fun u _ ↦ hexp u]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have ht1 : ∑ u : Fin d, star (φ j u) * φ j u = 1 := by simpa using horth j j
      have ht2 : (∑ u : Fin d, ∑ k ∈ K_s, star (c k j) * (star (φ j u) * ψ k u)) =
          ∑ k ∈ K_s, star (c k j) * c k j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ ↦ by rw [← Finset.mul_sum]
      have ht3 : (∑ u : Fin d, ∑ k ∈ K_s, c k j * (star (ψ k u) * φ j u)) =
          ∑ k ∈ K_s, c k j * star (c k j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← Finset.mul_sum]
        congr 1
        dsimp only [c, ψ]
        rw [star_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [star_mul, star_star, star_star, mul_comm]
      have ht4 : (∑ u : Fin d, ∑ a ∈ K_s, ∑ b ∈ K_s, (c a j * star (c b j)) * (star (ψ a u) *
          ψ b u)) = ∑ k ∈ K_s, c k j * star (c k j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a ha ↦ ?_
        rw [Finset.sum_comm]
        have hb : ∀ b ∈ K_s, (∑ u : Fin d, (c a j * star (c b j)) * (star (ψ a u) * ψ b u)) =
            if a = b then c a j * star (c b j) else 0 := fun b _ ↦ by
          rw [← Finset.mul_sum, hpsi_orth a b, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_congr rfl hb, Finset.sum_ite_eq K_s a (fun b ↦ c a j * star (c b j)),
          ite_eq_left_iff.mpr fun h ↦ absurd ha h]
      rw [ht1, ht2, ht3, ht4]
      ring
    have hre := congrArg Complex.re hr_eq
    simp only [Complex.re_sum, Complex.sub_re, Complex.one_re, star_mul_self_re_eq_norm_sq] at hre
    linarith
  have hmain : (∑ k ∈ K_s, (lam k) ^ 2) ≤ ∑ j ∈ K_sᶜ, (lam j) ^ 2 := by
    have hswap : (∑ k ∈ K_s, (lam k) ^ 2) =
        ∑ j : Fin d, (lam j) ^ 2 * (∑ k ∈ K_s, ‖c k j‖ ^ 2) := by
      calc (∑ k ∈ K_s, (lam k) ^ 2)
          = ∑ k ∈ K_s, ∑ j : Fin d, (lam j) ^ 2 * ‖c k j‖ ^ 2 :=
            Finset.sum_congr rfl fun k _ ↦ by
              rw [← mul_one ((lam k) ^ 2), ← hc_row_sum k, Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ ↦ hc_sq_eq k j
        _ = _ := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ ↦ (Finset.mul_sum _ _ _).symm
    rw [hswap, ← Finset.sum_add_sum_compl K_s,
      Finset.sum_eq_zero fun j hj ↦ by
        rw [Finset.sum_eq_zero fun k hk ↦ by rw [hc_same_zero k hk j hj, norm_zero, sq, mul_zero],
          mul_zero],
      zero_add]
    exact Finset.sum_le_sum fun j _ ↦ mul_le_of_le_one_right (sq_nonneg _) (hc_col_le j)
  have htot : (∑ j ∈ K_s, (lam j) ^ 2) + (∑ j ∈ K_sᶜ, (lam j) ^ 2) =
      ∑ u : Fin d, ∑ v : Fin d, ‖H u v‖ ^ 2 := by
    rw [Finset.sum_add_sum_compl]
    exact hermitian_eigenvalues_sq_sum_eq_frob H hH
  linarith
theorem norm_hermitian_le_of_unit_quad_form {D : ℕ} (M : Operator D) (hM : M.IsHermitian)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hquad : ∀ v : Fin D → ℂ, (∑ x : Fin D, ‖v x‖ ^ 2) = 1 →
      |(∑ x : Fin D, star (v x) * (M *ᵥ v) x).re| ≤ C) :
    ‖M‖ ≤ C := by
  obtain ⟨hUUh, hUhU, horth, _hcomp, hspec, _hrk⟩ := hermitian_spectral_columns M hM
  set U : Operator D := (hM.eigenvectorUnitary : Operator D)
  set μ : Fin D → ℝ := hM.eigenvalues
  have hMU : M * U = U * Matrix.diagonal (fun a ↦ (μ a : ℂ)) := by
    calc M * U = (U * Matrix.diagonal (fun a ↦ (μ a : ℂ)) * Uᴴ) * U := by rw [hspec]
      _ = U * Matrix.diagonal (fun a ↦ (μ a : ℂ)) * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun a ↦ (μ a : ℂ)) := by rw [hUhU, Matrix.mul_one]
  have hbound : ∀ a : Fin D, |μ a| ≤ C := fun a ↦ by
    let v : Fin D → ℂ := fun x ↦ U x a
    have hv_norm : (∑ x : Fin D, ‖v x‖ ^ 2) = 1 := by
      have h1 : ∑ x : Fin D, star (v x) * v x = 1 := by simpa [v] using horth a a
      have hre := congrArg Complex.re h1
      simpa only [Complex.re_sum, star_mul_self_re_eq_norm_sq, Complex.one_re] using hre
    have hMv : ∀ x : Fin D, (M *ᵥ v) x = (μ a : ℂ) * v x := fun x ↦ by
      have h1 := congrFun (congrFun hMU x) a
      rw [Matrix.mul_apply, Matrix.mul_diagonal] at h1
      simpa only [Matrix.mulVec, dotProduct, v, mul_comm] using h1
    have hq_eq : (∑ x : Fin D, star (v x) * (M *ᵥ v) x).re = μ a := by
      simp_rw [hMv, ← mul_assoc, mul_comm (star (v _)) (μ a : ℂ), mul_assoc]
      rw [← Finset.mul_sum, horth a a]
      simp only [↓reduceIte, mul_one, Complex.ofReal_re]
    rw [← hq_eq]
    exact hquad v hv_norm
  have hM_conj : M = (Uᴴ)ᴴ * Matrix.diagonal (fun a ↦ (μ a : ℂ)) * Uᴴ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hspec
  rw [hM_conj]
  exact norm_conj_diagonal_of_real_le Uᴴ
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hUUh)
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hUhU)
    μ hC0 hbound
theorem aux_proj_quad_le {D : ℕ} (P : Operator D) (hP_herm : P.IsHermitian)
    (v : Fin D → ℂ) (hPw : P *ᵥ (P *ᵥ v) = P *ᵥ v) :
    (∑ x : Fin D, star (v x) * (P *ᵥ v) x) = (∑ x : Fin D, star ((P *ᵥ v) x) * (P *ᵥ v) x) ∧
    (∑ x : Fin D, ‖(P *ᵥ v) x‖ ^ 2) ≤ ∑ x : Fin D, ‖v x‖ ^ 2 := by
  let w := P *ᵥ v
  have hvw : (∑ x : Fin D, star (v x) * w x) = ∑ x : Fin D, star (w x) * w x := by
    have h1 : (∑ x : Fin D, star (w x) * w x) = ∑ x : Fin D, star ((P *ᵥ v) x) * w x := rfl
    rw [h1]
    simp only [Matrix.mulVec, dotProduct, star_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hy : (∑ x : Fin D, star (P x y * v y) * w x) =
        star (v y) * (∑ x : Fin D, P y x * w x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hp : star (P x y) = P y x := by
        simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hP_herm.eq y) x
      rw [star_mul', hp]; ring
    rw [hy, show (∑ x : Fin D, P y x * w x) = w y from congrFun hPw y]
  refine ⟨hvw, ?_⟩
  let r : Fin D → ℂ := fun x ↦ v x - w x
  have hr_nn : 0 ≤ ∑ x : Fin D, ‖r x‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hwv : (∑ x : Fin D, star (w x) * v x) = ∑ x : Fin D, star (w x) * w x := by
    simpa only [star_sum, star_mul', star_star, mul_comm] using congrArg star hvw
  have hr_eq : (∑ x : Fin D, star (r x) * r x) =
      (∑ x : Fin D, star (v x) * v x) - (∑ x : Fin D, star (w x) * w x) := by
    have hexp : ∀ x : Fin D, star (r x) * r x =
        star (v x) * v x - star (v x) * w x - star (w x) * v x + star (w x) * w x := fun x ↦ by
      dsimp only [r]; rw [star_sub]; ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, hvw, hwv]; ring
  have hre := congrArg Complex.re hr_eq
  simp only [Complex.re_sum, Complex.sub_re, star_mul_self_re_eq_norm_sq] at hre
  linarith
theorem proj_vec_norm_sq_le {D : ℕ} (P : Operator D) (hP_herm : P.IsHermitian)
    (hP_idem : P * P = P) (v : Fin D → ℂ) :
    let w := P *ᵥ v
    P *ᵥ w = w ∧ (∑ x : Fin D, ‖w x‖ ^ 2) ≤ ∑ x : Fin D, ‖v x‖ ^ 2 := by
  intro w
  have hPw : P *ᵥ w = w := by dsimp only [w]; rw [Matrix.mulVec_mulVec, hP_idem]
  exact ⟨hPw, (aux_proj_quad_le P hP_herm v hPw).2⟩
theorem norm_proj_sandwich_two_sector_chiral_le {D m : ℕ} (P : Operator D)
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P) (lam : Fin m → ℝ) {F : ℝ} (hF0 : 0 ≤ F)
    (hpos_half : ∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ 0 < 1 * lam k), (lam k) ^ 2 ≤ ((1 :
    ℝ) / 2) * F ^ 2) (hneg_half : ∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ 0 < (-1) * lam k),
    (lam k) ^ 2 ≤ ((1 : ℝ) / 2) * F ^ 2) (N_up N_dn : Fin m → Operator D) (s_up s_dn : ℕ)
    (hs_sum : s_up + s_dn = 218) (hN_up_herm : ∀ k, (N_up k).IsHermitian)
    (hN_dn_herm : ∀ k, (N_dn k).IsHermitian)
    (hN_up_idem : ∀ k, N_up k * N_up k * P = N_up k * P)
    (hN_dn_idem : ∀ k, N_dn k * N_dn k * P = N_dn k * P)
    (hN_up_sum : (∑ k : Fin m, N_up k) = (s_up : ℂ) • (1 : Operator D))
    (hN_dn_sum : (∑ k : Fin m, N_dn k) = (s_dn : ℂ) • (1 : Operator D)) : ‖P *
    (∑ k : Fin m, (lam k : ℂ) • (N_up k + N_dn k)) * P‖ ≤ Real.sqrt 218 * F := by
  let M_tot : Operator D := ∑ k : Fin m, (lam k : ℂ) • (N_up k + N_dn k)
  let H_sys : Operator D := P * M_tot * P
  have hM_herm : M_tot.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal,
      ((hN_up_herm k).add (hN_dn_herm k)).eq]
  have hH_sys_herm : H_sys.IsHermitian := by
    rw [Matrix.IsHermitian]
    dsimp only [H_sys]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP_herm.eq, hM_herm.eq,
      Matrix.mul_assoc]
  refine norm_hermitian_le_of_unit_quad_form H_sys hH_sys_herm (by positivity) fun v hv_norm ↦ ?_
  obtain ⟨_hPw, hw_le⟩ := proj_vec_norm_sq_le P hP_herm hP_idem v
  let w := P *ᵥ v
  have hw_le1 : (∑ x : Fin D, ‖w x‖ ^ 2) ≤ 1 := hw_le.trans (le_of_eq hv_norm)
  have hquad_rew : (∑ x : Fin D, star (v x) * (H_sys *ᵥ v) x) =
      ∑ x : Fin D, star (w x) * (M_tot *ᵥ w) x := by
    change star v ⬝ᵥ ((P * M_tot * P) *ᵥ v) = star (P *ᵥ v) ⬝ᵥ (M_tot *ᵥ (P *ᵥ v))
    rw [Matrix.mul_assoc P M_tot P, ← Matrix.mulVec_mulVec v P (M_tot * P),
      ← Matrix.mulVec_mulVec v M_tot P, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hP_herm.eq]
  have hsector : ∀ (N_s : Fin m → Operator D) (s : ℕ),
      (∀ k, (N_s k).IsHermitian) →
      (∀ k, N_s k * N_s k * P = N_s k * P) →
      ((∑ k : Fin m, N_s k) = (s : ℂ) • (1 : Operator D)) →
      |(∑ x : Fin D,
          star (w x) * ((∑ k : Fin m, (lam k : ℂ) • N_s k) *ᵥ w) x).re| ≤
        Real.sqrt (s : ℝ) * Real.sqrt (((1 : ℝ) / 2) * F ^ 2) := by
    intro N_s s hNs_herm hNs_idem hNs_sum
    let n_occ : Fin m → ℝ := fun k ↦ (∑ x : Fin D, star (w x) * (N_s k *ᵥ w) x).re
    have hlin : (∑ x : Fin D, star (w x) * ((∑ k : Fin m, (lam k : ℂ) • N_s k) *ᵥ w) x).re = ∑
        k : Fin m, lam k * n_occ k := by
      have hmv : ∀ x : Fin D,
          ((∑ k : Fin m, (lam k : ℂ) • N_s k) *ᵥ w) x =
            ∑ k : Fin m, (lam k : ℂ) * (N_s k *ᵥ w) x := fun x ↦ by
        simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
          Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ ↦ by
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
      simp_rw [hmv, Finset.mul_sum]
      rw [Finset.sum_comm, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp_rw [← mul_assoc, mul_comm (star (w _)) (lam k : ℂ), mul_assoc]
      rw [← Finset.mul_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
    have hn_bounds : ∀ k : Fin m, 0 ≤ n_occ k ∧ n_occ k ≤ 1 := fun k ↦ by
      let Nk := N_s k
      let uk := Nk *ᵥ w
      have hNk_uk : Nk *ᵥ uk = uk := by
        dsimp only [uk, w, Nk]
        rw [Matrix.mulVec_mulVec (P *ᵥ v) (N_s k) (N_s k),
          Matrix.mulVec_mulVec v (N_s k * N_s k) P, hNs_idem k,
          ← Matrix.mulVec_mulVec v (N_s k) P]
      obtain ⟨hw_uk, huk_le⟩ := aux_proj_quad_le Nk (hNs_herm k) w hNk_uk
      have hn_eq_uk : n_occ k = ∑ x : Fin D, ‖uk x‖ ^ 2 := by
        dsimp only [n_occ]
        change (∑ x, star (w x) * uk x).re = _
        rw [hw_uk, Complex.re_sum]
        exact Finset.sum_congr rfl fun x _ ↦ star_mul_self_re_eq_norm_sq (uk x)
      exact ⟨hn_eq_uk ▸ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _, by linarith⟩
    have hn_sum_le : (∑ k : Fin m, n_occ k) ≤ (s : ℝ) := by
      have hsum_re : (∑ k : Fin m, n_occ k) = (s : ℝ) * (∑ x : Fin D, ‖w x‖ ^ 2) := by
        dsimp only [n_occ]
        rw [← Complex.re_sum]
        have hmv : (∑ k : Fin m, ∑ x : Fin D, star (w x) * (N_s k *ᵥ w) x) =
            ∑ x : Fin D, star (w x) * (((∑ k : Fin m, N_s k) *ᵥ w) x) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [← Finset.mul_sum]
          congr 1
          simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_mul]
          exact Finset.sum_comm
        rw [hmv, hNs_sum]
        have hone : ∀ x : Fin D, (((s : ℂ) • (1 : Operator D)) *ᵥ w) x = (s : ℂ) * w x :=
          fun x ↦ by
            simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
              mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
              ↓reduceIte]
        simp_rw [hone, ← mul_assoc, mul_comm (star (w _)) (s : ℂ), mul_assoc]
        rw [← Finset.mul_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
          sub_zero]
        congr 1
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun x _ ↦ star_mul_self_re_eq_norm_sq (w x)
      rw [hsum_re]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hw_le1
    have hn_sq_sum_le : ∀ K : Finset (Fin m), (∑ k ∈ K, (n_occ k) ^ 2) ≤ (s : ℝ) := fun K ↦ by
      have h1 : (∑ k ∈ K, (n_occ k) ^ 2) ≤ ∑ k ∈ K, n_occ k := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        obtain ⟨h0, h1⟩ := hn_bounds k
        nlinarith
      have h2 : (∑ k ∈ K, n_occ k) ≤ ∑ k : Fin m, n_occ k :=
        Finset.sum_le_univ_sum_of_nonneg fun k ↦ (hn_bounds k).1
      exact h1.trans (h2.trans hn_sum_le)
    let K_pos := Finset.univ.filter (fun k : Fin m ↦ 0 < 1 * lam k)
    let K_neg := Finset.univ.filter (fun k : Fin m ↦ 0 < (-1) * lam k)
    let X := ∑ k ∈ K_pos, lam k * n_occ k
    let Y := ∑ k ∈ K_neg, (-lam k) * n_occ k
    have hX_nn : 0 ≤ X := Finset.sum_nonneg fun k hk ↦ by
      simp only [K_pos, Finset.mem_filter, one_mul] at hk
      exact mul_nonneg hk.2.le (hn_bounds k).1
    have hY_nn : 0 ≤ Y := Finset.sum_nonneg fun k hk ↦ by
      simp only [K_neg, Finset.mem_filter, neg_one_mul] at hk
      exact mul_nonneg hk.2.le (hn_bounds k).1
    have hsplit_XY : (∑ k : Fin m, lam k * n_occ k) = X - Y := by
      have hdisj : Disjoint K_pos K_neg := Finset.disjoint_left.mpr fun k h1 h2 ↦ by
        simp only [K_pos, K_neg, Finset.mem_filter] at h1 h2; linarith
      have hrest : ∑ k ∈ (K_pos ∪ K_neg)ᶜ, lam k * n_occ k = 0 := by
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        simp only [Finset.mem_compl, Finset.mem_union, K_pos, K_neg, Finset.mem_filter,
          Finset.mem_univ, true_and, not_or, not_lt] at hk
        have hl0 : lam k = 0 := by linarith
        rw [hl0, zero_mul]
      rw [← Finset.sum_add_sum_compl (K_pos ∪ K_neg), hrest, add_zero, Finset.sum_union hdisj]
      dsimp only [X, Y]
      simp_rw [neg_mul, Finset.sum_neg_distrib]
      ring
    set B := Real.sqrt (s : ℝ) * Real.sqrt (((1 : ℝ) / 2) * F ^ 2)
    have hB_nn : 0 ≤ B := by positivity
    have hB_sq : B ^ 2 = (s : ℝ) * (((1 : ℝ) / 2) * F ^ 2) := by
      dsimp only [B]
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (by positivity)]
    have hcs_le (K : Finset (Fin m)) (g : Fin m → ℝ)
        (hg : (∑ k ∈ K, (g k) ^ 2) ≤ ((1 : ℝ) / 2) * F ^ 2) :
        (∑ k ∈ K, g k * n_occ k) ≤ B := by
      have hprod : (∑ k ∈ K, (g k) ^ 2) * (∑ k ∈ K, (n_occ k) ^ 2) ≤ B ^ 2 := by
        rw [hB_sq, mul_comm (s : ℝ)]
        exact mul_le_mul hg (hn_sq_sum_le K) (Finset.sum_nonneg fun _ _ ↦
          sq_nonneg _) (by positivity)
      have hsq := (Finset.sum_mul_sq_le_sq_mul_sq K g n_occ).trans hprod
      nlinarith
    have hX_le : X ≤ B := hcs_le K_pos lam hpos_half
    have hY_le : Y ≤ B := hcs_le K_neg (fun k ↦ -lam k) (by simpa only [neg_sq] using hneg_half)
    rw [hlin, hsplit_XY, abs_le]
    constructor <;> linarith
  have hM_split : M_tot =
      (∑ k : Fin m, (lam k : ℂ) • N_up k) + (∑ k : Fin m, (lam k : ℂ) • N_dn k) := by
    dsimp only [M_tot]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ smul_add (lam k : ℂ) (N_up k) (N_dn k)
  rw [hquad_rew, hM_split]
  have hadd_mv : (∑ x : Fin D, star (w x) * (((∑ k : Fin m, (lam k : ℂ) • N_up k) + (∑ k : Fin
      m, (lam k : ℂ) • N_dn k)) *ᵥ w) x).re = (∑ x : Fin D, star (w x) * ((∑ k : Fin m, (lam k
      : ℂ) • N_up k) *ᵥ w) x).re + (∑ x : Fin D, star (w x) * ((∑ k : Fin m, (lam k : ℂ) •
      N_dn k) *ᵥ w) x).re := by
    simp_rw [Matrix.add_mulVec, Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib, Complex.add_re]
  rw [hadd_mv]
  have hup := hsector N_up s_up hN_up_herm hN_up_idem hN_up_sum
  have hdn := hsector N_dn s_dn hN_dn_herm hN_dn_idem hN_dn_sum
  have hsum_roots : Real.sqrt (s_up : ℝ) + Real.sqrt (s_dn : ℝ) ≤ Real.sqrt 436 := by
    have hsumR : (s_up : ℝ) + (s_dn : ℝ) = 218 := by exact_mod_cast hs_sum
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg s_up), Real.sq_sqrt (Nat.cast_nonneg s_dn),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 436), Real.sqrt_nonneg (s_up : ℝ),
      Real.sqrt_nonneg (s_dn : ℝ), Real.sqrt_nonneg 436,
      sq_nonneg (Real.sqrt (s_up : ℝ) - Real.sqrt (s_dn : ℝ))]
  have htri := abs_add_le ((∑ x, star (w x) * ((∑ k, (lam k : ℂ) • N_up k) *ᵥ w) x).re)
      ((∑ x, star (w x) * ((∑ k, (lam k : ℂ) • N_dn k) *ᵥ w) x).re)
  refine (htri.trans (by linarith [add_le_add hup hdn] : _ ≤
    (Real.sqrt (s_up : ℝ) + Real.sqrt (s_dn : ℝ)) * Real.sqrt (((1 : ℝ) / 2) * F ^ 2))).trans ?_
  refine (mul_le_mul_of_nonneg_right hsum_roots (by positivity)).trans_eq ?_
  rw [← Real.sqrt_mul (by positivity),
    show (436 : ℝ) * (((1 : ℝ) / 2) * F ^ 2) = 218 * F ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hF0]
theorem exists_hermitian_conj_orthonormal_basis {d : ℕ}
    (H : Operator d) (hH : H.IsHermitian) (V : Unitary d)
    {F : ℝ} (hF0 : 0 ≤ F)
    (hFrob : (∑ u : Fin d, ∑ v : Fin d, ‖H u v‖ ^ 2) ≤ F ^ 2) :
    ∃ (χ : Fin d → Fin d → ℂ) (lam : Fin d → ℝ),
      (∀ a b : Fin d, ∑ u : Fin d, star (χ a u) * χ b u = if a = b then 1 else 0) ∧
      (∀ u v : Fin d, ∑ k : Fin d, χ k u * star (χ k v) = if u = v then 1 else 0) ∧
      (∑ k : Fin d, rk1Gen (χ k)) = 1 ∧
      V.1 * H * V.1ᴴ = ∑ k : Fin d, (lam k : ℂ) • rk1Gen (χ k) ∧
      (∀ k : Fin d, |lam k| ≤ F) ∧
      ((∀ u v : Fin d, star (H u v) = -H u v) →
        (∑ k ∈ Finset.univ.filter (fun k : Fin d ↦ 0 < 1 * lam k), (lam k) ^ 2 ≤
            ((1 : ℝ) / 2) * F ^ 2) ∧
        (∑ k ∈ Finset.univ.filter (fun k : Fin d ↦ 0 < (-1) * lam k), (lam k) ^ 2 ≤
            ((1 : ℝ) / 2) * F ^ 2)) := by
  obtain ⟨hUUh, hUhU, _horth, _hcomp, _hspec, hrk⟩ := hermitian_spectral_columns H hH
  set U : Operator d := (hH.eigenvectorUnitary : Operator d)
  set lam : Fin d → ℝ := hH.eigenvalues
  have hVVh : V.1 * V.1ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp V.2)
  have hVhV : V.1ᴴ * V.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp V.2)
  let W : Operator d := V.1 * U
  have hWUh : W * Wᴴ = 1 := by
    dsimp only [W]; rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc U Uᴴ, hUUh, Matrix.one_mul, hVVh]
  have hWhW : Wᴴ * W = 1 := by
    dsimp only [W]; rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc V.1ᴴ V.1, hVhV, Matrix.one_mul, hUhU]
  let χ : Fin d → Fin d → ℂ := fun k u ↦ W u k
  have horth_χ (a b : Fin d) : ∑ u : Fin d, star (χ a u) * χ b u = if a = b then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, χ] using
      congrFun (congrFun hWhW a) b
  have hcomp_χ (u v : Fin d) : ∑ k : Fin d, χ k u * star (χ k v) = if u = v then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, χ] using
      congrFun (congrFun hWUh u) v
  have hχ_comp : (∑ k : Fin d, rk1Gen (χ k)) = 1 := by
    ext u v
    rw [Matrix.sum_apply, Matrix.one_apply]
    simpa only [rk1Gen, Matrix.of_apply] using hcomp_χ u v
  have hVHV : V.1 * H * V.1ᴴ = ∑ k : Fin d, (lam k : ℂ) • rk1Gen (χ k) := by
    conv_lhs => rw [hrk]
    rw [Matrix.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
    apply congr_arg
    exact conj_rk1Gen V.1 (fun u ↦ U u k)
  have hlam_sq_sum : (∑ k : Fin d, (lam k) ^ 2) ≤ F ^ 2 := by
    rw [hermitian_eigenvalues_sq_sum_eq_frob H hH]
    exact hFrob
  have hlam_le : ∀ k : Fin d, |lam k| ≤ F := fun k ↦ by
    have h := (Finset.single_le_sum (fun j _ ↦
      sq_nonneg (lam j)) (Finset.mem_univ k)).trans hlam_sq_sum
    rw [← sq_abs (lam k)] at h; nlinarith [abs_nonneg (lam k)]
  refine ⟨χ, lam, horth_χ, hcomp_χ, hχ_comp, hVHV, hlam_le, fun hImag ↦ ⟨?_, ?_⟩⟩
  · linarith [(chiral_sign_eigenvalues_sq_sum_le_half_frob H hH hImag 1 (Or.inl rfl)).trans hFrob]
  · linarith [(chiral_sign_eigenvalues_sq_sum_le_half_frob H hH hImag (-1) (Or.inr rfl)).trans
      hFrob]
theorem norm_proj_sandwich_embed_chiral_le (A : Operator (2 ^ 18)) (hA_herm : A.IsHermitian)
    (hA_imag : ∀ u v : Fin (2 ^ 18), star (A u v) = -A u v) (V : Unitary (2 ^ 18)) {F : ℝ}
    (hF0 : 0 ≤ F) (hFrob : (∑ u : Fin (2 ^ 18), ∑ v : Fin (2 ^ 18), ‖A u v‖ ^ 2) ≤ F ^ 2)
    (spinUp : Finset (Fin numElectrons)) : ‖fermionicProjector spinUp *
    (∑ i : Fin numElectrons, (rEl_sp i).embedMatrix (V.1 * A * V.1ᴴ)) * fermionicProjector
    spinUp‖ ≤ Real.sqrt 218 * F := by
  obtain ⟨χ, lam, horth_χ, _hcomp_χ, hχ_comp, hVAV, _hlam_le, hchiral⟩ :=
    exists_hermitian_conj_orthonormal_basis A hA_herm V hF0 hFrob
  obtain ⟨hpos_half, hneg_half⟩ := hchiral hA_imag
  have hχ_norm : ∀ k : Fin (2 ^ 18), ∑ u : Fin (2 ^ 18), star (χ k u) * χ k u = 1 :=
    fun k ↦ by simpa using horth_χ k k
  have hχ_comp_sp : (∑ k : Fin (2 ^ 18), rk1_sp (χ k)) = 1 := hχ_comp
  have hemb_tot : (∑ i : Fin numElectrons, (rEl_sp i).embedMatrix (V.1 * A * V.1ᴴ)) =
      ∑ k : Fin (2 ^ 18), (lam k : ℂ) • (nSub_sp (χ k) spinUp + nSub_sp (χ k) spinUpᶜ) := by
    rw [hVAV]
    have hi : ∀ i : Fin numElectrons,
        (rEl_sp i).embedMatrix (∑ k : Fin (2 ^ 18), (lam k : ℂ) • rk1Gen (χ k)) =
          ∑ k : Fin (2 ^ 18), (lam k : ℂ) • op_sp (χ k) i := fun i ↦ by
      rw [embedMatrix_sum]
      exact Finset.sum_congr rfl fun k _ ↦ (rEl_sp i).embedMatrix_smul (lam k : ℂ) (rk1_sp (χ k))
    simp_rw [hi]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← Finset.smul_sum]
    apply congr_arg
    unfold nSub_sp
    exact (Finset.sum_add_sum_compl spinUp (fun i ↦ op_sp (χ k) i)).symm
  rw [hemb_tot]
  have hsum_sub : ∀ S : Finset (Fin numElectrons),
      (∑ k : Fin (2 ^ 18), nSub_sp (χ k) S) = (S.card : ℂ) • (1 : Operator (2 ^ systemQubits)) :=
    fun S ↦ by
      unfold nSub_sp op_sp
      rw [Finset.sum_comm]
      have hi : ∀ i ∈ S, (∑ k : Fin (2 ^ 18), (rEl_sp i).embedMatrix (rk1_sp (χ k))) = 1 :=
        fun i _ ↦ by rw [← embedMatrix_sum, hχ_comp_sp, (rEl_sp i).embedMatrix_one]
      rw [Finset.sum_congr rfl hi]
      rw [Finset.sum_const, Nat.cast_smul_eq_nsmul ℂ]
  have hcard_sum : spinUp.card + spinUpᶜ.card = 218 := Finset.card_add_card_compl spinUp
  exact norm_proj_sandwich_two_sector_chiral_le
    (fermionicProjector spinUp)
    (fermionicProjector_isHermitian spinUp)
    (fermionicProjector_idem spinUp)
    lam hF0 hpos_half hneg_half
    (fun k ↦ nSub_sp (χ k) spinUp)
    (fun k ↦ nSub_sp (χ k) spinUpᶜ)
    spinUp.card spinUpᶜ.card hcard_sum
    (fun k ↦ nSub_isHermitian_any (χ k) spinUp)
    (fun k ↦ nSub_isHermitian_any (χ k) spinUpᶜ)
    (fun k ↦ nSub_mul_self_mul_fermionicProjector (hχ_norm k) spinUp spinUp
      (fun _ hi _ hj ↦ ⟨fun _ ↦ hj, fun _ ↦ hi⟩))
    (fun k ↦ nSub_mul_self_mul_fermionicProjector (hχ_norm k) spinUp spinUpᶜ
      (fun _ hi _ hj ↦ by
        simp only [Finset.mem_compl] at hi hj
        exact ⟨fun h ↦ (hi h).elim, fun h ↦ (hj h).elim⟩))
    (hsum_sub spinUp)
    (hsum_sub spinUpᶜ)
theorem norm_embed_hermitian_le_frob (B : Operator (2 ^ 18)) (hB : B.IsHermitian)
    (V : Unitary (2 ^ 18)) {F : ℝ} (hF0 : 0 ≤ F) (hFrob : (∑ u : Fin (2 ^ 18), ∑ v : Fin (2 ^
    18), ‖B u v‖ ^ 2) ≤ F ^ 2) (i : Fin numElectrons) : ‖(rEl_sp i).embedMatrix
    (V.1 * B * V.1ᴴ)‖ ≤ F := by
  obtain ⟨χ, μ, horth_χ, hcomp_χ, _hχ_comp, hVBV_loc, hμ_le, _hchiral⟩ :=
    exists_hermitian_conj_orthonormal_basis B hB V hF0 hFrob
  have hVBV : (rEl_sp i).embedMatrix (V.1 * B * V.1ᴴ) =
      ∑ k : Fin (2 ^ 18), (μ k : ℂ) • op_sp (χ k) i := by
    rw [hVBV_loc, embedMatrix_sum]
    exact Finset.sum_congr rfl fun k _ ↦ (rEl_sp i).embedMatrix_smul (μ k : ℂ) (rk1_sp (χ k))
  rw [hVBV]
  exact norm_sum_op_sp_le_of_orthonormal (Equiv.refl _) χ horth_χ hcomp_χ i μ hF0 hμ_le
noncomputable def nucDelta (W : ℕ) (c : Configuration) (l : Fin 216) (w : Fin 3) : ℝ :=
  let fr := Int.fract (c.nuclei l w / cellVolume ^ ((1 : ℝ) / 3))
  (⌊(2 ^ W : ℝ) * fr + 1 / 2⌋₊ : ℝ) / (2 ^ W : ℝ) - fr
theorem abs_nucDelta_le (W : ℕ) (c : Configuration) (l : Fin 216) (w : Fin 3) :
    |nucDelta W c l w| ≤ (1 / 2 : ℝ) / (2 ^ W : ℝ) := by
  dsimp only [nucDelta]
  set fr := Int.fract (c.nuclei l w / cellVolume ^ ((1 : ℝ) / 3))
  set N := ⌊(2 ^ W : ℝ) * fr + 1 / 2⌋₊
  have hfr0 : 0 ≤ fr := Int.fract_nonneg _
  have hpos : 0 ≤ (2 ^ W : ℝ) * fr + 1 / 2 := by positivity
  have hfl1 : (N : ℝ) ≤ (2 ^ W : ℝ) * fr + 1 / 2 := Nat.floor_le hpos
  have hfl2 : (2 ^ W : ℝ) * fr + 1 / 2 < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [abs_le]
  constructor <;> field_simp <;> linarith
noncomputable def nucTheta (W : ℕ) (c : Configuration) (l : Fin 216) (ν : Fin 3 → ℤ) : ℝ :=
  -(2 * π * ∑ w : Fin 3, (ν w : ℝ) * nucDelta W c l w)
theorem nucTheta_neg (W : ℕ) (c : Configuration) (l : Fin 216) (ν : Fin 3 → ℤ) :
    nucTheta W c l (-ν) = -nucTheta W c l ν := by
  unfold nucTheta
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring
theorem oneElectronPhase_truncWCfg_eq (W : ℕ) (c : Configuration) (l : Fin 216) (ν : Fin 3 → ℤ) :
    oneElectronPhase ((truncWCfg W c).nuclei l) ν =
      oneElectronPhase (c.nuclei l) ν * Complex.exp ((nucTheta W c l ν : ℂ) * Complex.I) := by
  set L : ℝ := cellVolume ^ ((1 : ℝ) / 3)
  have hL_eq : cellVolume ^ (1 / 3 : ℝ) = L := by dsimp [L, one_div]
  have hL_ne : L ≠ 0 := by
    dsimp [L]; simpa [one_div] using cellLength_ne_zero
  have h2W_ne : (2 ^ W : ℝ) ≠ 0 := by positivity
  let x : Fin 3 → ℝ := fun w ↦ c.nuclei l w / L
  let fr : Fin 3 → ℝ := fun w ↦ Int.fract (x w)
  let N : Fin 3 → ℕ := fun w ↦ ⌊(2 ^ W : ℝ) * fr w + 1 / 2⌋₊
  set q : Fin 3 → ℕ := fun w ↦ N w / 2 ^ W
  set r : Fin 3 → ℕ := fun w ↦ N w % 2 ^ W
  have hdot_c : waveVector ν ⬝ᵥ c.nuclei l = 2 * π * ∑ w : Fin 3, (ν w : ℝ) * x w := by
    unfold waveVector
    simp only [dotProduct, hL_eq, x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    field_simp [hL_ne]
  have hdot_t : waveVector ν ⬝ᵥ (truncWCfg W c).nuclei l =
      2 * π * ∑ w : Fin 3, (ν w : ℝ) * ((r w : ℝ) / (2 ^ W : ℝ)) := by
    unfold waveVector truncWCfg nuclearMW
    simp only [dotProduct, hL_eq, r, N, fr, x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    field_simp [hL_ne, h2W_ne]
  have hcoord (w : Fin 3) :
      (r w : ℝ) / (2 ^ W : ℝ) = x w + nucDelta W c l w - (q w : ℝ) - (⌊x w⌋ : ℝ) := by
    have hr_eq : (r w : ℝ) = (N w : ℝ) - (2 ^ W : ℝ) * (q w : ℝ) := by
      linarith [show (r w : ℝ) + (2 ^ W : ℝ) * (q w : ℝ) = (N w : ℝ) by
        exact_mod_cast Nat.mod_add_div (N w) (2 ^ W)]
    have hfr_eq : fr w = x w - (⌊x w⌋ : ℝ) := by linarith [Int.floor_add_fract (x w)]
    change (r w : ℝ) / (2 ^ W : ℝ) =
      x w + ((N w : ℝ) / (2 ^ W : ℝ) - fr w) - (q w : ℝ) - (⌊x w⌋ : ℝ)
    rw [hr_eq, hfr_eq]
    field_simp [h2W_ne]
    ring
  unfold oneElectronPhase
  rw [← Complex.exp_add, hdot_t, hdot_c]
  set kInt : ℤ := ∑ w : Fin 3, ν w * (q w : ℤ) + ∑ w : Fin 3, ν w * ⌊x w⌋
  have harg : -((2 * π * ∑ w : Fin 3, (ν w : ℝ) * ((r w : ℝ) / (2 ^ W : ℝ)) : ℝ) : ℂ) *
      Complex.I = (-(2 * π * ∑ w : Fin 3, (ν w : ℝ) * x w : ℝ) : ℂ) * Complex.I +
      (nucTheta W c l ν : ℂ) * Complex.I + (kInt : ℂ) * (2 * ↑π * Complex.I) := by
    unfold nucTheta
    dsimp only [kInt]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
      Fin.sum_univ_three, Fin.sum_univ_three, hcoord 0, hcoord 1, hcoord 2]
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
def pOf18 (u : Fin (2 ^ 18)) : Fin 3 → ℤ := shiftedMom3D (elecOffsetGridEquiv18 u)
def inGrid18 (u : Fin (2 ^ 18)) : Prop := InMomGrid3D (pOf18 u)
open Classical in
noncomputable def nucMatA (W : ℕ) (c : Configuration) (l : Fin 216) : Operator (2 ^ 18) :=
    Matrix.of fun u v ↦ if inGrid18 u ∧ inGrid18 v then ((-(coulombKernel (pOf18 u - pOf18 v)
    * nucTheta W c l (pOf18 u - pOf18 v)) : ℝ) : ℂ) * Complex.I else 0
open Classical in
noncomputable def nucMatB (W : ℕ) (c : Configuration) (l : Fin 216) : Operator (2 ^ 18) :=
    Matrix.of fun u v ↦ if inGrid18 u ∧ inGrid18 v then -((coulombKernel (pOf18 u - pOf18 v) :
    ℂ) * (Complex.exp ((nucTheta W c l (pOf18 u - pOf18 v) : ℂ) * Complex.I) - 1 - (nucTheta W
    c l (pOf18 u - pOf18 v) : ℂ) * Complex.I)) else 0
theorem nucMatA_imag (W : ℕ) (c : Configuration) (l : Fin 216) (u v : Fin (2 ^ 18)) :
    star (nucMatA W c l u v) = -nucMatA W c l u v := by
  unfold nucMatA
  simp only [Matrix.of_apply]
  split_ifs with h
  · rw [star_mul, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    ring
  · simp
theorem ite_pos {α : Type*} {P : Prop} [Decidable P] (h : P) (a b : α) :
    (if P then a else b) = a := by
  split_ifs; rfl
theorem ite_neg {α : Type*} {P : Prop} [Decidable P] (h : ¬ P) (a b : α) :
    (if P then a else b) = b := by
  split_ifs; rfl
open Classical in
theorem nucMatA_isHermitian (W : ℕ) (c : Configuration) (l : Fin 216) :
    (nucMatA W c l).IsHermitian := by
  ext u v
  rw [Matrix.conjTranspose_apply, nucMatA_imag]
  unfold nucMatA
  simp only [Matrix.of_apply]
  by_cases h : inGrid18 u ∧ inGrid18 v
  · have hswap : inGrid18 v ∧ inGrid18 u := ⟨h.2, h.1⟩
    rw [ite_pos hswap, ite_pos h]
    have hneg : pOf18 v - pOf18 u = -(pOf18 u - pOf18 v) := by abel
    rw [hneg, Dyadic128CoulombMath.coulombKernel_neg, nucTheta_neg]
    push_cast; ring
  · have hswap : ¬ (inGrid18 v ∧ inGrid18 u) := fun hs ↦ h ⟨hs.2, hs.1⟩
    rw [ite_neg hswap, ite_neg h, neg_zero]
open Classical in
theorem nucMatB_isHermitian (W : ℕ) (c : Configuration) (l : Fin 216) :
    (nucMatB W c l).IsHermitian := by
  ext u v
  rw [Matrix.conjTranspose_apply]
  unfold nucMatB
  simp only [Matrix.of_apply]
  by_cases h : inGrid18 u ∧ inGrid18 v
  · have hswap : inGrid18 v ∧ inGrid18 u := ⟨h.2, h.1⟩
    rw [ite_pos hswap, ite_pos h]
    have hneg : pOf18 v - pOf18 u = -(pOf18 u - pOf18 v) := by abel
    rw [hneg, Dyadic128CoulombMath.coulombKernel_neg, nucTheta_neg]
    set θ := nucTheta W c l (pOf18 u - pOf18 v)
    set K := coulombKernel (pOf18 u - pOf18 v)
    rw [star_neg, star_mul, RCLike.star_def, Complex.conj_ofReal]
    have hexp_conj : (starRingEnd ℂ) (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) - 1 - ((-θ : ℝ)
        : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I := by
      rw [map_sub, map_sub, map_one, ← Complex.exp_conj]
      have h1 : (starRingEnd ℂ) (((-θ : ℝ) : ℂ) * Complex.I) = (θ : ℂ) * Complex.I := by
        simp [Complex.conj_ofReal]
      rw [h1]
    rw [hexp_conj, mul_comm]
  · have hswap : ¬ (inGrid18 v ∧ inGrid18 u) := fun hs ↦ h ⟨hs.2, hs.1⟩
    rw [ite_neg hswap, ite_neg h, star_zero]
theorem diag_mul_entry {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) (M : Matrix n n ℂ)
    (i j : n) : (Matrix.diagonal d * M) i j = d i * M i j := by
  rw [Matrix.mul_apply]
  simp [Matrix.diagonal_apply]
theorem mul_diag_entry {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (d : n → ℂ)
    (i j : n) : (M * Matrix.diagonal d) i j = M i j * d j := by
  rw [Matrix.mul_apply]
  simp [Matrix.diagonal_apply]
theorem diag_exact_conj_apply (c : Configuration) (l : Fin 216) (M : Operator (2 ^ 18))
    (u v : Fin (2 ^ 18)) : ((oneElecNucDiagExact c l).1 * M * (oneElecNucDiagExact c l).1ᴴ) u
    v = oneElectronPhase (c.nuclei l) (pOf18 u - pOf18 v) * M u v := by
  change (Matrix.diagonal (fun z ↦ oneElectronPhase (c.nuclei l) (pOf18 z)) * M *
    (Matrix.diagonal (fun z ↦ oneElectronPhase (c.nuclei l) (pOf18 z)))ᴴ) u v = _
  rw [Matrix.diagonal_conjTranspose, mul_diag_entry, diag_mul_entry]
  dsimp only [Pi.star_apply]
  rw [mul_right_comm, oneElectronPhase_mul_star]
theorem uEnManyBody_sub_grid_apply (c' c : Configuration) {x y : Fin (2 ^ systemQubits)}
    (hx : IsGridState x) (hy : IsGridState y) : (uEnManyBody c' - uEnManyBody c) x y = ∑ i :
    Fin numElectrons, if ∀ b ≠ Particle.electron i, momentum x b = momentum y b then ∑ l : Fin
    216, -((oneElectronPhase (c'.nuclei l) (momentum x (.electron i) - momentum y (.electron
    i)) - oneElectronPhase (c.nuclei l) (momentum x (.electron i) - momentum y (.electron i)))
    * (coulombKernel (momentum x (.electron i) - momentum y (.electron i)) : ℂ)) else 0 := by
  unfold uEnManyBody structureFactor oneElectronPhase
  simp only [Matrix.sub_apply, Matrix.of_apply, hx, hy, and_self, ↓reduceIte]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs with hmom
  · rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  · ring
theorem proj_sum_add_split {D : ℕ} (P : Matrix (Fin D) (Fin D) ℂ)
    (fA fB : Fin 216 → Fin numElectrons → Matrix (Fin D) (Fin D) ℂ) :
    P * (∑ l : Fin 216, ∑ i : Fin numElectrons, (fA l i + fB l i)) * P =
      (∑ l : Fin 216, P * (∑ i : Fin numElectrons, fA l i) * P) +
      (∑ l : Fin 216, ∑ i : Fin numElectrons, P * fB l i * P) := by
  simp_rw [Finset.sum_add_distrib]
  rw [mul_add, add_mul]
  congr 1
  · rw [Finset.mul_sum, Finset.sum_mul]
  · rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [Finset.mul_sum, Finset.sum_mul]
open Classical in
theorem proj_uEnManyBody_truncWCfg_sub_eq (W : ℕ) (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let P := fermionicProjector spinUp
    let V := oneElecNucDiagExact c
    P * (uEnManyBody (truncWCfg W c) - uEnManyBody c) * P =
      (∑ l : Fin 216, P * (∑ i : Fin numElectrons,
        (rEl_sp i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ)) * P) +
      (∑ l : Fin 216, ∑ i : Fin numElectrons,
        P * (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P) := by
  intro P V
  let G : Operator (2 ^ systemQubits) :=
    Matrix.diagonal fun z ↦ if IsGridState z then (1 : ℂ) else 0
  have hPG : P * G = P := by
    ext x y; rw [mul_diag_entry]
    by_cases hy : IsGridState y
    · simp [hy]
    · simp [show P x y = 0 by simp [P, fermionicProjector, hy]]
  have hGP : G * P = P := by
    ext x y; rw [diag_mul_entry]
    by_cases hx : IsGridState x
    · simp [hx]
    · simp [show P x y = 0 by simp [P, fermionicProjector, hx]]
  let S_op : Operator (2 ^ systemQubits) := ∑ l : Fin 216, ∑ i : Fin numElectrons, ((rEl_sp
      i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ) + (rEl_sp i).embedMatrix ((V l).1 *
      nucMatB W c l * (V l).1ᴴ))
  have hGSG : G * (uEnManyBody (truncWCfg W c) - uEnManyBody c) * G = G * S_op * G := by
    ext x y
    have hdiag (M : Operator (2 ^ systemQubits)) :
        (G * M * G) x y = if IsGridState x ∧ IsGridState y then M x y else 0 := by
      rw [mul_diag_entry, diag_mul_entry]
      by_cases hx : IsGridState x <;> by_cases hy : IsGridState y <;> simp [hx, hy]
    rw [hdiag, hdiag]
    by_cases hgrid : IsGridState x ∧ IsGridState y
    · rw [ite_pos hgrid, ite_pos hgrid]
      rcases hgrid with ⟨hx, hy⟩
      rw [uEnManyBody_sub_grid_apply (truncWCfg W c) c hx hy]
      change _ = (∑ l : Fin 216, ∑ i : Fin numElectrons,
        ((rEl_sp i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ) +
          (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ))) x y
      simp only [Matrix.sum_apply, Matrix.add_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hao_iff := agreeOutside_rEl_sp_iff_momentum hx hy i
      split_ifs with hmom
      · have hao : (rEl_sp i).AgreeOutside x y := hao_iff.mpr hmom
        set ux := (rEl_sp i).extractIndex x
        set uy := (rEl_sp i).extractIndex y
        have hpx : pOf18 ux = momentum x (.electron i) :=
          shiftedMom3D_elecOffsetGridEquiv18_extractIndex hx i
        have hpy : pOf18 uy = momentum y (.electron i) :=
          shiftedMom3D_elecOffsetGridEquiv18_extractIndex hy i
        have higx : inGrid18 ux := by
          unfold inGrid18; rw [hpx]; exact inMomGrid3D_electron_of_state x i
        have higy : inGrid18 uy := by
          unfold inGrid18; rw [hpy]; exact inMomGrid3D_electron_of_state y i
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [QRegister.embedMatrix_apply_of_agreeOutside, ite_pos hao, mul_one,
          QRegister.embedMatrix_apply_of_agreeOutside, ite_pos hao, mul_one]
        change _ = ((V l).1 * nucMatA W c l * (V l).1ᴴ) ux uy +
          ((V l).1 * nucMatB W c l * (V l).1ᴴ) ux uy
        rw [diag_exact_conj_apply, diag_exact_conj_apply]
        unfold nucMatA nucMatB
        simp only [Matrix.of_apply, higx, higy, and_self, ↓reduceIte]
        rw [← hpx, ← hpy, oneElectronPhase_truncWCfg_eq W c l (pOf18 ux - pOf18 uy)]
        push_cast; ring
      · have hnao : ¬ (rEl_sp i).AgreeOutside x y := mt hao_iff.mp hmom
        symm
        refine Finset.sum_eq_zero fun l _ ↦ ?_
        rw [QRegister.embedMatrix_apply_of_agreeOutside, ite_neg hnao, mul_zero,
          QRegister.embedMatrix_apply_of_agreeOutside, ite_neg hnao, mul_zero, add_zero]
    · rw [ite_neg hgrid, ite_neg hgrid]
  have hAssoc (M : Operator (2 ^ systemQubits)) :
      (P * G) * M * (G * P) = P * (G * M * G) * P := by
    simp only [Matrix.mul_assoc]
  rw [show P * (uEnManyBody (truncWCfg W c) - uEnManyBody c) * P = P * S_op * P by
    rw [show P * (uEnManyBody (truncWCfg W c) - uEnManyBody c) * P =
        (P * G) * (uEnManyBody (truncWCfg W c) - uEnManyBody c) * (G * P) by rw [hPG, hGP],
      hAssoc, hGSG, ← hAssoc, hPG, hGP]]
  exact proj_sum_add_split P
    (fun l i ↦ (rEl_sp i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ))
    (fun l i ↦ (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ))
def multGen (N d : ℕ) : ℕ := if d = 0 then N else 2 * (N - d)
def mult1D (a : ℕ) : ℕ :=
  match a with
  | 0 => 63
  | _ => 2 * (63 - a)
def natAbsDiff (a b : ℕ) : ℕ := if a < b then b - a else a - b
theorem natAbs_sub_eq_natAbsDiff (a b : ℕ) : ((a : ℤ) - (b : ℤ)).natAbs = natAbsDiff a b := by
  unfold natAbsDiff
  split_ifs with h <;> omega
theorem sum_natAbsDiff_range (h : ℕ → ℝ) : ∀ N : ℕ,
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, h (natAbsDiff i j)) =
      ∑ d ∈ Finset.range N, (multGen N d : ℝ) * h d
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ]
    simp_rw [Finset.sum_range_succ (fun j ↦ h (natAbsDiff _ j)) N]
    rw [Finset.sum_add_distrib, sum_natAbsDiff_range h N]
    have hdiag : natAbsDiff N N = 0 := by unfold natAbsDiff; simp
    have hrefl (f : ℕ → ℕ) (hf : ∀ i < N, f i = N - i) :
        (∑ i ∈ Finset.range N, h (f i)) = ∑ k ∈ Finset.range N, h (k + 1) := by
      have hsub : (∑ i ∈ Finset.range N, h (f i)) = ∑ i ∈ Finset.range N, h (N - i) :=
        Finset.sum_congr rfl fun i hi ↦ congrArg h (hf i (Finset.mem_range.mp hi))
      rw [hsub, ← Finset.sum_range_reflect (fun i ↦ h (N - i)) N]
      exact Finset.sum_congr rfl fun k hk ↦ congrArg h (by have := Finset.mem_range.mp hk; omega)
    have h1 := hrefl (fun i ↦ natAbsDiff i N) fun i hi ↦ by unfold natAbsDiff; simp [hi]
    have h2 := hrefl (fun j ↦ natAbsDiff N j) fun j hj ↦ by
      unfold natAbsDiff; simp [show ¬ N < j by omega]
    rw [hdiag, h1, h2]
    cases N with
    | zero =>
      simp [multGen]
    | succ M =>
      rw [Finset.sum_range_succ' _ (M + 1), Finset.sum_range_succ' _ M,
        Finset.sum_range_succ (fun k ↦ h (k + 1)) M]
      have htail : (∑ k ∈ Finset.range M, (multGen (M + 1) (k + 1) : ℝ) * h (k + 1)) +
          2 * ∑ k ∈ Finset.range M, h (k + 1) =
          ∑ k ∈ Finset.range M, (multGen (M + 2) (k + 1) : ℝ) * h (k + 1) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk' : k < M := Finset.mem_range.mp hk
        have hm1 : multGen (M + 1) (k + 1) = 2 * (M - k) := by
          unfold multGen; simp
        have hm2 : multGen (M + 2) (k + 1) = 2 * (M + 1 - k) := by
          unfold multGen; simp
        rw [hm1, hm2]
        have hnat : 2 * (M - k) + 2 = 2 * (M + 1 - k) := by omega
        have hcast : ((2 * (M - k) : ℕ) : ℝ) + 2 = ((2 * (M + 1 - k) : ℕ) : ℝ) := by
          exact_mod_cast hnat
        rw [← hcast]
        ring
      have htop : multGen (M + 2) (M + 1) = 2 := by unfold multGen; simp
      have hzero1 : multGen (M + 1) 0 = M + 1 := rfl
      have hzero2 : multGen (M + 2) 0 = M + 2 := rfl
      rw [Finset.sum_range_succ (fun k ↦ (multGen (M + 2) (k + 1) : ℝ) * h (k + 1)) M,
        hzero1, hzero2, htop]
      push_cast
      linarith [htail]
def sumC16 (a2b2 mab : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc =>
    withStrictNat (a2b2 + k * k) fun r2 ↦
    withStrictNat (match r2 with
      | 0 => 0
      | _ => (mab * mult1D k * 16 + r2 - 1) / r2) fun term ↦
    withStrictNat (acc + term) (sumC16 a2b2 mab k)
def sumB16 (a2 ma : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | b + 1, acc =>
    withStrictNat (a2 + b * b) fun a2b2 ↦
    withStrictNat (ma * mult1D b) fun mab ↦
    withStrictNat (sumC16 a2b2 mab 63 acc) (sumB16 a2 ma b)
def sumARange16 : ℕ → ℕ → ℕ → ℕ
  | _, 0, acc => acc
  | base, cnt + 1, acc =>
    withStrictNat (base + cnt) fun a ↦
    withStrictNat (a * a) fun a2 ↦
    withStrictNat (mult1D a) fun ma ↦
    withStrictNat (sumB16 a2 ma 63 acc) (sumARange16 base cnt)
theorem chunk16_0 : sumARange16 0 9 0 = 782956838 := by decide +kernel
theorem chunk16_1 : sumARange16 9 9 0 = 306103197 := by decide +kernel
theorem chunk16_2 : sumARange16 18 9 0 = 151556020 := by decide +kernel
theorem chunk16_3 : sumARange16 27 9 0 = 79650188 := by decide +kernel
theorem chunk16_4 : sumARange16 36 9 0 = 41058423 := by decide +kernel
theorem chunk16_5 : sumARange16 45 9 0 = 18769708 := by decide +kernel
theorem chunk16_6 : sumARange16 54 9 0 = 5300082 := by decide +kernel
def term16Nat (a b c : ℕ) : ℕ :=
  let r2 := a * a + b * b + c * c
  if r2 = 0 then 0 else (mult1D a * mult1D b * mult1D c * 16 + r2 - 1) / r2
theorem sumC16_eq (a b : ℕ) : ∀ (n acc : ℕ),
    sumC16 (a * a + b * b) (mult1D a * mult1D b) n acc =
      acc + ∑ c ∈ Finset.range n, term16Nat a b c
  | 0, acc => by simp [sumC16]
  | k + 1, acc => by
    rw [sumC16, withStrictNat_eq, withStrictNat_eq, withStrictNat_eq,
      sumC16_eq a b k, Finset.sum_range_succ _ k]
    have hm : (match a * a + b * b + k * k with
        | 0 => 0
        | _ => (mult1D a * mult1D b * mult1D k * 16 + (a * a + b * b + k * k) - 1) /
            (a * a + b * b + k * k)) =
        term16Nat a b k := by
      unfold term16Nat
      dsimp only
      cases a * a + b * b + k * k <;> rfl
    rw [hm, Nat.add_assoc, Nat.add_comm (term16Nat a b k)]
theorem sumB16_eq (a : ℕ) : ∀ (n acc : ℕ),
    sumB16 (a * a) (mult1D a) n acc =
      acc + ∑ b ∈ Finset.range n, ∑ c ∈ Finset.range 63, term16Nat a b c
  | 0, acc => by simp [sumB16]
  | b + 1, acc => by
    rw [sumB16, withStrictNat_eq, withStrictNat_eq, withStrictNat_eq,
      sumC16_eq a b 63 acc, sumB16_eq a b, Finset.sum_range_succ _ b]
    rw [Nat.add_assoc, Nat.add_comm (∑ c ∈ Finset.range 63, term16Nat a b c)]
theorem sumARange16_eq (base : ℕ) : ∀ (cnt acc : ℕ),
    sumARange16 base cnt acc =
      acc + ∑ k ∈ Finset.range cnt, ∑ b ∈ Finset.range 63, ∑ c ∈ Finset.range 63,
        term16Nat (base + k) b c
  | 0, acc => by simp [sumARange16]
  | cnt + 1, acc => by
    rw [sumARange16, withStrictNat_eq, withStrictNat_eq, withStrictNat_eq, withStrictNat_eq,
      sumB16_eq (base + cnt) 63 acc, sumARange16_eq base cnt, Finset.sum_range_succ _ cnt]
    rw [Nat.add_assoc,
      Nat.add_comm (∑ b ∈ Finset.range 63, ∑ c ∈ Finset.range 63, term16Nat (base + cnt) b c)]
theorem sum_term16Nat_63_eq : (∑ a ∈ Finset.range 63, ∑ b ∈ Finset.range 63, ∑ c ∈
    Finset.range 63, term16Nat a b c) = 1385394456 := by
  let f : ℕ → ℕ := fun a ↦ ∑ b ∈ Finset.range 63, ∑ c ∈ Finset.range 63, term16Nat a b c
  have hstep (n : ℕ) : (∑ a ∈ Finset.range (n + 9), f a) =
      (∑ a ∈ Finset.range n, f a) + sumARange16 n 9 0 := by
    rw [Finset.sum_range_add f n 9, sumARange16_eq n 9 0, zero_add]
  change (∑ a ∈ Finset.range (0 + 9 + 9 + 9 + 9 + 9 + 9 + 9), f a) = 1385394456
  rw [hstep, hstep, hstep, hstep, hstep, hstep, hstep]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add,
    chunk16_0, chunk16_1, chunk16_2, chunk16_3, chunk16_4, chunk16_5, chunk16_6]
theorem real_term_le_term16Nat (a b c : ℕ) : (mult1D a : ℝ) * (mult1D b : ℝ) * (mult1D c : ℝ)
    * (if a * a + b * b + c * c = 0 then (0 : ℝ) else 1 / ((a * a + b * b + c * c : ℕ) : ℝ)) ≤
    (term16Nat a b c : ℝ) / 16 := by
  unfold term16Nat
  dsimp only
  set r2 := a * a + b * b + c * c
  by_cases hr2 : r2 = 0
  · simp [hr2]
  · simp only [hr2, ↓reduceIte]
    have hr2_pos : 0 < r2 := Nat.pos_of_ne_zero hr2
    have hr2R : (0 : ℝ) < (r2 : ℝ) := by exact_mod_cast hr2_pos
    set X := mult1D a * mult1D b * mult1D c * 16
    have hceil_nat : X ≤ ((X + r2 - 1) / r2) * r2 := by
      have hdiv := Nat.div_add_mod (X + r2 - 1) r2
      have hmod := Nat.mod_lt (X + r2 - 1) hr2_pos
      have : r2 * ((X + r2 - 1) / r2) = ((X + r2 - 1) / r2) * r2 := Nat.mul_comm _ _
      omega
    have hceilR : (X : ℝ) ≤ (((X + r2 - 1) / r2 : ℕ) : ℝ) * (r2 : ℝ) := by
      exact_mod_cast hceil_nat
    have hX : (X : ℝ) = (mult1D a : ℝ) * (mult1D b : ℝ) * (mult1D c : ℝ) * 16 := by
      dsimp [X]; push_cast; ring
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    rw [show (mult1D a : ℝ) * (mult1D b : ℝ) * (mult1D c : ℝ) * (1 / (r2 : ℝ)) * 16 =
      (X : ℝ) / (r2 : ℝ) by rw [hX]; ring]
    exact (div_le_iff₀ hr2R).mpr hceilR
abbrev Grid63_3 := Fin 63 × Fin 63 × Fin 63
abbrev PairGrid63_3 := Grid63_3 × Grid63_3
def fin3EquivProd3 (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun f := (f 0, f 1, f 2)
  invFun p w := match w with | 0 => p.1 | 1 => p.2.1 | _ => p.2.2
  left_inv f := by ext w; fin_cases w <;> rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl
theorem inMomGrid1D_shiftedFin64ToInt_iff (u : Fin 64) :
    InMomGrid1D (shiftedFin64ToInt u) ↔ u ≠ 0 := by
  unfold InMomGrid1D shiftedFin64ToInt
  constructor
  · intro h h0
    subst h0
    simp at h
  · intro hne
    have hpos : 0 < u.val := Nat.pos_of_ne_zero (fun hv ↦ hne (Fin.ext hv))
    have hlt := u.isLt
    omega
open Classical in
theorem sum_fin64_if_inMomGrid1D (f : Fin 64 → ℝ) :
    (∑ u : Fin 64, if InMomGrid1D (shiftedFin64ToInt u) then f u else 0) =
      ∑ i : Fin 63, f i.succ := by
  rw [Fin.sum_univ_succ]
  have h0 : ¬ InMomGrid1D (shiftedFin64ToInt 0) := by
    rw [inMomGrid1D_shiftedFin64ToInt_iff]; exact not_not.mpr rfl
  simp only [h0, ↓reduceIte, zero_add]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs : InMomGrid1D (shiftedFin64ToInt i.succ) :=
    (inMomGrid1D_shiftedFin64ToInt_iff i.succ).mpr (Fin.succ_ne_zero i)
  simp [hs]
def flip63 : Fin 63 ≃ Fin 63 where
  toFun k := ⟨62 - k.val, by omega⟩
  invFun k := ⟨62 - k.val, by omega⟩
  left_inv k := by ext; dsimp; omega
  right_inv k := by ext; dsimp; omega
@[scoped simp] theorem flip63_flip63 (k : Fin 63) : flip63 (flip63 k) = k := flip63.left_inv k
theorem flip63_sub_int (i j : Fin 63) :
    ((flip63 i).val : ℤ) - ((flip63 j).val : ℤ) = -((i.val : ℤ) - (j.val : ℤ)) := by
  dsimp [flip63]
  have hi := i.isLt
  have hj := j.isLt
  omega
theorem sum_eq_zero_of_involutive_neg {α : Type*} [Fintype α] (σ : α ≃ α) (f : α → ℝ)
    (hneg : ∀ x, f (σ x) = -f x) : (∑ x : α, f x) = 0 := by
  have h := Equiv.sum_comp σ f
  simp_rw [hneg, Finset.sum_neg_distrib] at h
  linarith
def d0P (x : PairGrid63_3) : ℤ := (x.1.1.val : ℤ) - (x.2.1.val : ℤ)
def d1P (x : PairGrid63_3) : ℤ := (x.1.2.1.val : ℤ) - (x.2.2.1.val : ℤ)
def d2P (x : PairGrid63_3) : ℤ := (x.1.2.2.val : ℤ) - (x.2.2.2.val : ℤ)
def r2P (x : PairGrid63_3) : ℕ := (d0P x).natAbs ^ 2 + (d1P x).natAbs ^ 2 + (d2P x).natAbs ^ 2
theorem cast_natAbs_sq_int (z : ℤ) : (((z.natAbs : ℕ) : ℝ)) ^ 2 = (z : ℝ) ^ 2 := by
  cases z with
  | ofNat n => simp [Int.natAbs]
  | negSucc n => simp [Int.natAbs]; ring
theorem r2P_cast_eq (x : PairGrid63_3) :
    (r2P x : ℝ) = (d0P x : ℝ) ^ 2 + (d1P x : ℝ) ^ 2 + (d2P x : ℝ) ^ 2 := by
  unfold r2P
  push_cast
  rw [cast_natAbs_sq_int, cast_natAbs_sq_int, cast_natAbs_sq_int]
def flipAxis0P : PairGrid63_3 ≃ PairGrid63_3 where
  toFun x := ((flip63 x.1.1, x.1.2.1, x.1.2.2), (flip63 x.2.1, x.2.2.1, x.2.2.2))
  invFun x := ((flip63 x.1.1, x.1.2.1, x.1.2.2), (flip63 x.2.1, x.2.2.1, x.2.2.2))
  left_inv x := by rcases x with ⟨⟨i0, i1, i2⟩, ⟨j0, j1, j2⟩⟩; simp
  right_inv x := by rcases x with ⟨⟨i0, i1, i2⟩, ⟨j0, j1, j2⟩⟩; simp
def flipAxis1P : PairGrid63_3 ≃ PairGrid63_3 where
  toFun x := ((x.1.1, flip63 x.1.2.1, x.1.2.2), (x.2.1, flip63 x.2.2.1, x.2.2.2))
  invFun x := ((x.1.1, flip63 x.1.2.1, x.1.2.2), (x.2.1, flip63 x.2.2.1, x.2.2.2))
  left_inv x := by rcases x with ⟨⟨i0, i1, i2⟩, ⟨j0, j1, j2⟩⟩; simp
  right_inv x := by rcases x with ⟨⟨i0, i1, i2⟩, ⟨j0, j1, j2⟩⟩; simp
def rotAxesP : PairGrid63_3 ≃ PairGrid63_3 where
  toFun x := ((x.1.2.1, x.1.2.2, x.1.1), (x.2.2.1, x.2.2.2, x.2.1))
  invFun x := ((x.1.2.2, x.1.1, x.1.2.1), (x.2.2.2, x.2.1, x.2.2.1))
  left_inv x := by rcases x with ⟨⟨i0, i1, i2⟩, ⟨j0, j1, j2⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨i0, i1, i2⟩, ⟨j0, j1, j2⟩⟩; rfl
noncomputable def invR2SqP (x : PairGrid63_3) : ℝ :=
  if r2P x = 0 then 0 else 1 / ((r2P x : ℝ) ^ 2)
noncomputable def invR2P (x : PairGrid63_3) : ℝ := if r2P x = 0 then 0 else 1 / (r2P x : ℝ)
def pairGridReorder :
    PairGrid63_3 ≃ (Fin 63 × Fin 63) × (Fin 63 × Fin 63) × (Fin 63 × Fin 63) where
  toFun x := ((x.1.1, x.2.1), (x.1.2.1, x.2.2.1), (x.1.2.2, x.2.2.2))
  invFun y := ((y.1.1, y.2.1.1, y.2.2.1), (y.1.2, y.2.1.2, y.2.2.2))
  left_inv x := by rcases x with ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩; rfl
  right_inv y := by rcases y with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩; rfl
theorem sum_fin63_pair_eq_toeplitz (h : ℕ → ℝ) :
    (∑ i : Fin 63, ∑ j : Fin 63, h (natAbsDiff i.val j.val)) =
      ∑ a ∈ Finset.range 63, (mult1D a : ℝ) * h a := by
  have h1 : (∑ i : Fin 63, ∑ j : Fin 63, h (natAbsDiff i.val j.val)) =
      ∑ i ∈ Finset.range 63, ∑ j ∈ Finset.range 63, h (natAbsDiff i j) := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ ∑ j : Fin 63, h (natAbsDiff i j)) 63]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact Fin.sum_univ_eq_sum_range (fun j ↦ h (natAbsDiff i j)) 63
  rw [h1, sum_natAbsDiff_range h 63]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [show mult1D a = multGen 63 a by cases a <;> rfl]
theorem sum_invR2P_eq_toeplitz : (∑ x : PairGrid63_3, invR2P x) = ∑ a ∈ Finset.range 63, ∑ b ∈
    Finset.range 63, ∑ c ∈ Finset.range 63, (mult1D a : ℝ) * (mult1D b : ℝ) * (mult1D c : ℝ) *
    (if a * a + b * b + c * c = 0 then 0 else 1 / ((a * a + b * b + c * c : ℕ) : ℝ)) := by
  let g : ℕ → ℕ → ℕ → ℝ := fun a b c ↦
    if a * a + b * b + c * c = 0 then 0 else 1 / ((a * a + b * b + c * c : ℕ) : ℝ)
  rw [← Equiv.sum_comp pairGridReorder.symm invR2P]
  simp only [Fintype.sum_prod_type]
  have hleaf : ∀ (i0 j0 i1 j1 i2 j2 : Fin 63),
      invR2P (pairGridReorder.symm ((i0, j0), (i1, j1), (i2, j2))) =
        g (natAbsDiff i0.val j0.val) (natAbsDiff i1.val j1.val) (natAbsDiff i2.val j2.val) := by
    intro i0 j0 i1 j1 i2 j2
    unfold invR2P r2P d0P d1P d2P pairGridReorder g
    simp only [Equiv.coe_fn_symm_mk, natAbs_sub_eq_natAbsDiff, sq]
  simp_rw [hleaf]
  have hc : ∀ (a b : ℕ), (∑ i2 : Fin 63, ∑ j2 : Fin 63, g a b (natAbsDiff i2.val j2.val)) = ∑
      c ∈ Finset.range 63, (mult1D c : ℝ) * g a b c := fun a b ↦ sum_fin63_pair_eq_toeplitz
      (fun c ↦ g a b c)
  simp_rw [hc]
  have hb : ∀ (a : ℕ), (∑ i1 : Fin 63, ∑ j1 : Fin 63, ∑ c ∈ Finset.range 63, (mult1D c : ℝ) *
      g a (natAbsDiff i1.val j1.val) c) = ∑ b ∈ Finset.range 63, (mult1D b : ℝ) * ∑ c ∈
      Finset.range 63, (mult1D c : ℝ) * g a b c := fun a ↦ sum_fin63_pair_eq_toeplitz
      (fun b ↦ ∑ c ∈ Finset.range 63, (mult1D c : ℝ) * g a b c)
  simp_rw [hb]
  rw [sum_fin63_pair_eq_toeplitz
    (fun a ↦ ∑ b ∈ Finset.range 63, (mult1D b : ℝ) *
      ∑ c ∈ Finset.range 63, (mult1D c : ℝ) * g a b c)]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  dsimp only [g]
  ring
theorem sum_invR2P_le : (∑ x : PairGrid63_3, invR2P x) ≤ (1385394456 : ℝ) / 16 := by
  rw [sum_invR2P_eq_toeplitz]
  calc (∑ a ∈ Finset.range 63, ∑ b ∈ Finset.range 63, ∑ c ∈ Finset.range 63,
          (mult1D a : ℝ) * (mult1D b : ℝ) * (mult1D c : ℝ) *
            (if a * a + b * b + c * c = 0 then 0 else 1 / ((a * a + b * b + c * c : ℕ) : ℝ)))
      ≤ ∑ a ∈ Finset.range 63, ∑ b ∈ Finset.range 63, ∑ c ∈ Finset.range 63,
          ((term16Nat a b c : ℝ) / 16) :=
        Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦
          Finset.sum_le_sum fun c _ ↦ real_term_le_term16Nat a b c
    _ = ((∑ a ∈ Finset.range 63, ∑ b ∈ Finset.range 63, ∑ c ∈ Finset.range 63,
          term16Nat a b c : ℕ) : ℝ) / 16 := by
        push_cast
        simp only [Finset.sum_div]
    _ = (1385394456 : ℝ) / 16 := by rw [sum_term16Nat_63_eq]; norm_num
theorem cubic_sym_pairGrid (δ : Fin 3 → ℝ) : (∑ x : PairGrid63_3, ((d0P x : ℝ) * δ 0 + (d1P x
    : ℝ) * δ 1 + (d2P x : ℝ) * δ 2) ^ 2 * invR2SqP x) = ((δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) / 3) *
    (∑ x : PairGrid63_3, invR2P x) := by
  have hexp : ∀ x : PairGrid63_3,
      ((d0P x : ℝ) * δ 0 + (d1P x : ℝ) * δ 1 + (d2P x : ℝ) * δ 2) ^ 2 * invR2SqP x =
        δ 0 ^ 2 * ((d0P x : ℝ) ^ 2 * invR2SqP x) +
        δ 1 ^ 2 * ((d1P x : ℝ) ^ 2 * invR2SqP x) +
        δ 2 ^ 2 * ((d2P x : ℝ) ^ 2 * invR2SqP x) +
        (2 * δ 0 * δ 1) * ((d0P x : ℝ) * (d1P x : ℝ) * invR2SqP x) +
        (2 * δ 0 * δ 2) * ((d0P x : ℝ) * (d2P x : ℝ) * invR2SqP x) +
        (2 * δ 1 * δ 2) * ((d1P x : ℝ) * (d2P x : ℝ) * invR2SqP x) := fun x ↦ by ring
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hinv0 (x : PairGrid63_3) : invR2SqP (flipAxis0P x) = invR2SqP x := by
    unfold invR2SqP
    rw [show r2P (flipAxis0P x) = r2P x by
      simp only [r2P, d0P, d1P, d2P, flipAxis0P, Equiv.coe_fn_mk, flip63_sub_int, Int.natAbs_neg]]
  have hinv1 (x : PairGrid63_3) : invR2SqP (flipAxis1P x) = invR2SqP x := by
    unfold invR2SqP
    rw [show r2P (flipAxis1P x) = r2P x by
      simp only [r2P, d0P, d1P, d2P, flipAxis1P, Equiv.coe_fn_mk, flip63_sub_int, Int.natAbs_neg]]
  have hinvR (x : PairGrid63_3) : invR2SqP (rotAxesP x) = invR2SqP x := by
    unfold invR2SqP
    rw [show r2P (rotAxesP x) = r2P x by
      simp only [r2P, d0P, d1P, d2P, rotAxesP, Equiv.coe_fn_mk]; ring]
  have hcross (e : PairGrid63_3 ≃ PairGrid63_3) (da db : PairGrid63_3 → ℤ)
      (hinv : ∀ x, invR2SqP (e x) = invR2SqP x)
      (hda : ∀ x, (da (e x) : ℝ) = -(da x : ℝ)) (hdb : ∀ x, db (e x) = db x) :
      (∑ x : PairGrid63_3, (da x : ℝ) * (db x : ℝ) * invR2SqP x) = 0 :=
    sum_eq_zero_of_involutive_neg e _ fun x ↦ by rw [hda x, hdb x, hinv x]; ring
  have hd0_flip (x : PairGrid63_3) : (d0P (flipAxis0P x) : ℝ) = -(d0P x : ℝ) := by
    simp only [d0P, flipAxis0P, Equiv.coe_fn_mk]; exact_mod_cast flip63_sub_int x.1.1 x.2.1
  have hd1_flip (x : PairGrid63_3) : (d1P (flipAxis1P x) : ℝ) = -(d1P x : ℝ) := by
    simp only [d1P, flipAxis1P, Equiv.coe_fn_mk]; exact_mod_cast flip63_sub_int x.1.2.1 x.2.2.1
  have hc01 := hcross flipAxis0P d0P d1P hinv0 hd0_flip (fun _ ↦ rfl)
  have hc02 := hcross flipAxis0P d0P d2P hinv0 hd0_flip (fun _ ↦ rfl)
  have hc12 := hcross flipAxis1P d1P d2P hinv1 hd1_flip (fun _ ↦ rfl)
  have hrot (da db : PairGrid63_3 → ℤ) (hd : ∀ x, da (rotAxesP x) = db x) :
      (∑ x : PairGrid63_3, (da x : ℝ) ^ 2 * invR2SqP x) =
        ∑ x : PairGrid63_3, (db x : ℝ) ^ 2 * invR2SqP x := by
    rw [← Equiv.sum_comp rotAxesP (fun x ↦ (da x : ℝ) ^ 2 * invR2SqP x)]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [hd x, hinvR]
  have hrot01 := hrot d0P d1P (fun _ ↦ rfl)
  have hrot12 := hrot d1P d2P (fun _ ↦ rfl)
  have hsum3 : (∑ x : PairGrid63_3, (d0P x : ℝ) ^ 2 * invR2SqP x) +
      (∑ x : PairGrid63_3, (d1P x : ℝ) ^ 2 * invR2SqP x) +
      (∑ x : PairGrid63_3, (d2P x : ℝ) ^ 2 * invR2SqP x) = ∑ x : PairGrid63_3, invR2P x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    unfold invR2SqP invR2P
    by_cases hr : r2P x = 0
    · simp [hr]
    · simp only [hr, ↓reduceIte]
      have hr_ne : (r2P x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
      rw [show (d0P x : ℝ) ^ 2 * (1 / (r2P x : ℝ) ^ 2) +
            (d1P x : ℝ) ^ 2 * (1 / (r2P x : ℝ) ^ 2) +
            (d2P x : ℝ) ^ 2 * (1 / (r2P x : ℝ) ^ 2) =
          ((d0P x : ℝ) ^ 2 + (d1P x : ℝ) ^ 2 + (d2P x : ℝ) ^ 2) * (1 / (r2P x : ℝ) ^ 2) by ring,
        ← r2P_cast_eq x]
      field_simp [hr_ne]
  have hS0 : (∑ x : PairGrid63_3, (d0P x : ℝ) ^ 2 * invR2SqP x) =
      (∑ x : PairGrid63_3, invR2P x) / 3 := by linarith [hrot01, hrot12, hsum3]
  rw [hc01, hc02, hc12, ← hrot12, ← hrot01, hS0]
  ring
def u18ToGrid64_3 : Fin (2 ^ 18) ≃ Fin 64 × Fin 64 × Fin 64 :=
  elecOffsetGridEquiv18.trans (fin3EquivProd3 (Fin 64))
def succGrid63_3 (g : Grid63_3) : Fin 64 × Fin 64 × Fin 64 :=
  (g.1.succ, g.2.1.succ, g.2.2.succ)
open Classical in
theorem sum_u18_inGrid18 (f : Fin (2 ^ 18) → ℝ) :
    (∑ u : Fin (2 ^ 18), if inGrid18 u then f u else 0) =
      ∑ g : Grid63_3, f (u18ToGrid64_3.symm (succGrid63_3 g)) := by
  rw [← Equiv.sum_comp u18ToGrid64_3.symm (fun u ↦ if inGrid18 u then f u else 0)]
  have hig : ∀ p : Fin 64 × Fin 64 × Fin 64,
      inGrid18 (u18ToGrid64_3.symm p) ↔
        InMomGrid1D (shiftedFin64ToInt p.1) ∧
        InMomGrid1D (shiftedFin64ToInt p.2.1) ∧
        InMomGrid1D (shiftedFin64ToInt p.2.2) := fun p ↦ by
    unfold inGrid18 pOf18 InMomGrid3D shiftedMom3D u18ToGrid64_3
    simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
    exact ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ w ↦ by fin_cases w <;> assumption⟩
  simp only [Fintype.sum_prod_type]
  have hite64 (P : Prop) [Decidable P] (g : Fin 64 → ℝ) :
      (∑ k : Fin 64, if P then (if InMomGrid1D (shiftedFin64ToInt k) then g k else 0) else 0) =
        if P then ∑ i : Fin 63, g i.succ else 0 := by
    by_cases hP : P
    · simp only [hP, ↓reduceIte]; exact sum_fin64_if_inMomGrid1D g
    · simp [hP]
  have hrew (a b c : Fin 64) : (if inGrid18 (u18ToGrid64_3.symm (a, b, c)) then
        f (u18ToGrid64_3.symm (a, b, c)) else 0) =
      if InMomGrid1D (shiftedFin64ToInt a) then
        (if InMomGrid1D (shiftedFin64ToInt b) then
          (if InMomGrid1D (shiftedFin64ToInt c) then f (u18ToGrid64_3.symm (a, b, c)) else 0)
        else 0)
      else 0 := by
    rw [hig (a, b, c)]
    by_cases ha : InMomGrid1D (shiftedFin64ToInt a) <;>
      by_cases hb : InMomGrid1D (shiftedFin64ToInt b) <;>
      by_cases hc : InMomGrid1D (shiftedFin64ToInt c) <;> simp [ha, hb, hc]
  have hc_sum (a b : Fin 64) :
      (∑ c : Fin 64, if InMomGrid1D (shiftedFin64ToInt a) then
        (if InMomGrid1D (shiftedFin64ToInt b) then
          (if InMomGrid1D (shiftedFin64ToInt c) then f (u18ToGrid64_3.symm (a, b, c)) else 0)
        else 0) else 0) =
      if InMomGrid1D (shiftedFin64ToInt a) then
        (if InMomGrid1D (shiftedFin64ToInt b) then
          ∑ i2 : Fin 63, f (u18ToGrid64_3.symm (a, b, i2.succ)) else 0)
      else 0 := by
    by_cases ha : InMomGrid1D (shiftedFin64ToInt a)
    · simp only [ha, ↓reduceIte]; exact hite64 _ _
    · simp [ha]
  simp_rw [hrew, hc_sum, hite64]
  exact sum_fin64_if_inMomGrid1D
    (fun a ↦ ∑ i1 : Fin 63, ∑ i2 : Fin 63, f (u18ToGrid64_3.symm (a, i1.succ, i2.succ)))
theorem aux_normSqInt_ne_zero {ν : Fin 3 → ℤ} (hν0 : ν ≠ 0) : normSqInt ν ≠ 0 := fun hz ↦ by
  unfold normSqInt at hz
  refine hν0 (funext fun w ↦ ?_)
  fin_cases w
  · exact Int.natAbs_eq_zero.mp (by nlinarith : (ν 0).natAbs = 0)
  · exact Int.natAbs_eq_zero.mp (by nlinarith : (ν 1).natAbs = 0)
  · exact Int.natAbs_eq_zero.mp (by nlinarith : (ν 2).natAbs = 0)
theorem pOf18_succGrid_sub (g1 g2 : Grid63_3) :
    pOf18 (u18ToGrid64_3.symm (succGrid63_3 g1)) -
      pOf18 (u18ToGrid64_3.symm (succGrid63_3 g2)) =
      fun w ↦ match w with
        | 0 => d0P (g1, g2)
        | 1 => d1P (g1, g2)
        | _ => d2P (g1, g2) := by
  ext w
  unfold pOf18 u18ToGrid64_3 succGrid63_3 shiftedMom3D shiftedFin64ToInt d0P d1P d2P
  simp only [Pi.sub_apply, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  fin_cases w <;> (dsimp [fin3EquivProd3]; simp only [Fin.val_succ]; push_cast; ring)
open Classical in
theorem frob_nucMatA_le (W : ℕ) (c : Configuration) (l : Fin 216) :
    (∑ u : Fin (2 ^ 18), ∑ v : Fin (2 ^ 18), ‖nucMatA W c l u v‖ ^ 2) ≤
      ((2 / lLoRat) * ((1 / 2 : ℝ) / (2 ^ W : ℝ)) * Real.sqrt ((1385394456 : ℝ) / 16)) ^ 2 := by
  have hcell_ne : cellSide ≠ 0 := cellSide_pos.ne'
  have hlLo_pos : 0 < lLoRat := lLoRat_pos
  have hlLo_le : lLoRat ≤ cellSide := lLoRat_le_cellSide
  have hrew_uv : ∀ u v : Fin (2 ^ 18),
      ‖nucMatA W c l u v‖ ^ 2 =
        if inGrid18 u then
          (if inGrid18 v then
            (coulombKernel (pOf18 u - pOf18 v) * nucTheta W c l (pOf18 u - pOf18 v)) ^ 2
           else 0)
        else 0 := fun u v ↦ by
    unfold nucMatA
    simp only [Matrix.of_apply]
    by_cases hu : inGrid18 u <;> by_cases hv : inGrid18 v
    · simp only [hu, hv, and_self, ↓reduceIte, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    all_goals simp [hu, hv]
  simp_rw [hrew_uv]
  have hv_sum (u : Fin (2 ^ 18)) :
      (∑ v : Fin (2 ^ 18), if inGrid18 u then
        (if inGrid18 v then
          (coulombKernel (pOf18 u - pOf18 v) * nucTheta W c l (pOf18 u - pOf18 v)) ^ 2
         else 0) else 0) =
      if inGrid18 u then
        ∑ g2 : Grid63_3,
          (coulombKernel (pOf18 u - pOf18 (u18ToGrid64_3.symm (succGrid63_3 g2))) *
            nucTheta W c l (pOf18 u - pOf18 (u18ToGrid64_3.symm (succGrid63_3 g2)))) ^ 2
      else 0 := by
    by_cases hu : inGrid18 u
    · simp only [hu, ↓reduceIte]
      exact sum_u18_inGrid18 _
    · simp [hu]
  simp_rw [hv_sum]
  rw [sum_u18_inGrid18]
  rw [← Fintype.sum_prod_type'
    (fun g1 g2 : Grid63_3 ↦
      (coulombKernel
          (pOf18 (u18ToGrid64_3.symm (succGrid63_3 g1)) -
            pOf18 (u18ToGrid64_3.symm (succGrid63_3 g2))) *
        nucTheta W c l
          (pOf18 (u18ToGrid64_3.symm (succGrid63_3 g1)) -
            pOf18 (u18ToGrid64_3.symm (succGrid63_3 g2)))) ^ 2)]
  set δ := nucDelta W c l
  have hleaf : ∀ x : PairGrid63_3, (coulombKernel (pOf18 (u18ToGrid64_3.symm (succGrid63_3
      x.1)) - pOf18 (u18ToGrid64_3.symm (succGrid63_3 x.2))) * nucTheta W c l (pOf18
      (u18ToGrid64_3.symm (succGrid63_3 x.1)) - pOf18 (u18ToGrid64_3.symm (succGrid63_3
      x.2)))) ^ 2 = (2 / cellSide) ^ 2 * (((d0P x : ℝ) * δ 0 + (d1P x : ℝ) * δ 1 + (d2P x : ℝ)
      * δ 2) ^ 2 * invR2SqP x) := by
    intro x
    set ν := pOf18 (u18ToGrid64_3.symm (succGrid63_3 x.1)) -
      pOf18 (u18ToGrid64_3.symm (succGrid63_3 x.2))
    have hν_eq := pOf18_succGrid_sub x.1 x.2
    have hν0_eq : ν 0 = d0P x := congrFun hν_eq 0
    have hν1_eq : ν 1 = d1P x := congrFun hν_eq 1
    have hν2_eq : ν 2 = d2P x := congrFun hν_eq 2
    have hns : normSqInt ν = r2P x := by
      unfold normSqInt r2P
      change (ν 0).natAbs ^ 2 + (ν 1).natAbs ^ 2 + (ν 2).natAbs ^ 2 = _
      rw [hν0_eq, hν1_eq, hν2_eq]
    by_cases hν0 : ν = 0
    · have hr0 : r2P x = 0 := by rw [← hns, hν0]; simp [normSqInt]
      rw [hν0, coulombKernel_zero]
      unfold invR2SqP
      simp [hr0]
    · have hr_ne : r2P x ≠ 0 := fun hz ↦ aux_normSqInt_ne_zero hν0 (hns.trans hz)
      rw [coulombKernel_eq_of_ne_zero hν0, hns]
      unfold nucTheta invR2SqP
      simp only [hr_ne, ↓reduceIte, Fin.sum_univ_three]
      change ((1 : ℝ) / (π * cellSide) * (1 / (r2P x : ℝ)) *
        -(2 * π * ((ν 0 : ℝ) * δ 0 + (ν 1 : ℝ) * δ 1 + (ν 2 : ℝ) * δ 2))) ^ 2 = _
      rw [hν0_eq, hν1_eq, hν2_eq]
      have hrR_ne : (r2P x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr_ne
      field_simp [Real.pi_ne_zero, hcell_ne, hrR_ne]
  simp_rw [hleaf, ← Finset.mul_sum]
  rw [cubic_sym_pairGrid δ]
  set dmax : ℝ := (1 / 2 : ℝ) / (2 ^ W : ℝ)
  have hδ_sq : ∀ w : Fin 3, δ w ^ 2 ≤ dmax ^ 2 := fun w ↦ by
    have habs : |δ w| ≤ dmax := abs_nucDelta_le W c l w
    have hd0 : 0 ≤ dmax := by dsimp [dmax]; positivity
    nlinarith [abs_le.mp habs]
  have havg_le : (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) / 3 ≤ dmax ^ 2 := by
    linarith [hδ_sq 0, hδ_sq 1, hδ_sq 2]
  have htwo_div_le : (2 / cellSide) ^ 2 ≤ (2 / lLoRat) ^ 2 := by
    have h1 : 2 / cellSide ≤ 2 / lLoRat :=
      div_le_div_of_nonneg_left zero_le_two hlLo_pos hlLo_le
    exact pow_le_pow_left₀ (by have := cellSide_pos; positivity) h1 2
  have hS_nonneg : 0 ≤ ∑ x : PairGrid63_3, invR2P x :=
    Finset.sum_nonneg fun x _ ↦ by unfold invR2P; split_ifs <;> positivity
  have havg_nn : 0 ≤ (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) / 3 :=
    div_nonneg (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) (by norm_num)
  have hprod1 : (2 / cellSide) ^ 2 *
        (((δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) / 3) * ∑ x : PairGrid63_3, invR2P x) ≤
      (2 / lLoRat) ^ 2 * (dmax ^ 2 * ((1385394456 : ℝ) / 16)) := by
    have hinner : ((δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) / 3) * (∑ x : PairGrid63_3, invR2P x) ≤
        dmax ^ 2 * ((1385394456 : ℝ) / 16) :=
      mul_le_mul havg_le sum_invR2P_le hS_nonneg (sq_nonneg dmax)
    exact mul_le_mul htwo_div_le hinner (mul_nonneg havg_nn hS_nonneg) (sq_nonneg _)
  have hrt_sq : ((2 / lLoRat) * dmax * Real.sqrt ((1385394456 : ℝ) / 16)) ^ 2 =
      (2 / lLoRat) ^ 2 * (dmax ^ 2 * ((1385394456 : ℝ) / 16)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1385394456 : ℝ) / 16)]
    ring
  rw [hrt_sq]
  exact hprod1
theorem norm_exp_ofReal_mul_I_sub_one_sub_le {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ ≤ θ ^ 2 := by
  have hsq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ ^ 2 =
      2 + θ ^ 2 - 2 * Real.cos θ - 2 * (θ * Real.sin θ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.exp_ofReal_mul_I]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
      add_zero, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add,
      Complex.one_im]
    linear_combination Real.sin_sq_add_cos_sq θ
  have htsin : |θ| * Real.sin |θ| = θ * Real.sin θ := by
    rcases le_or_gt 0 θ with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, Real.sin_neg]; ring
  have htcos : Real.cos |θ| = Real.cos θ := Real.cos_abs θ
  rcases eq_or_lt_of_le (abs_nonneg θ) with ht0 | ht_pos
  · have h0 : θ = 0 := abs_eq_zero.mp ht0.symm
    subst h0; simp
  · have hc : 1 - |θ| ^ 2 / 2 ≤ Real.cos |θ| := one_sub_sq_div_two_le_cos
    have hs : |θ| - |θ| ^ 3 / 6 < Real.sin |θ| := Real.sin_gt_sub_cube ht_pos
    have hmul : |θ| * (|θ| - |θ| ^ 3 / 6) ≤ |θ| * Real.sin |θ| :=
      mul_le_mul_of_nonneg_left hs.le ht_pos.le
    rw [htcos] at hc
    rw [htsin] at hmul
    have habs2 : |θ| ^ 2 = θ ^ 2 := sq_abs θ
    have habs4 : |θ| * (|θ| - |θ| ^ 3 / 6) = θ ^ 2 - (θ ^ 2) ^ 2 / 6 := by
      calc |θ| * (|θ| - |θ| ^ 3 / 6)
          = |θ| ^ 2 - (|θ| ^ 2) ^ 2 / 6 := by ring
        _ = θ ^ 2 - (θ ^ 2) ^ 2 / 6 := by rw [habs2]
    rw [habs2] at hc
    rw [habs4] at hmul
    have hle_sq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ * ‖Complex.exp
        ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ ≤ θ ^ 2 * θ ^ 2 := by
      nlinarith [hsq, hc, hmul, sq_nonneg (θ ^ 2)]
    exact (mul_self_le_mul_self_iff (norm_nonneg _) (sq_nonneg θ)).mpr hle_sq
open Classical in
theorem frob_nucMatB_le {W : ℕ} (hW20 : 20 ≤ W) (c : Configuration) (l : Fin 216) :
    (∑ u : Fin (2 ^ 18), ∑ v : Fin (2 ^ 18), ‖nucMatB W c l u v‖ ^ 2) ≤
      ((2 ^ 18 : ℝ) * ((12 * (315 / 100) / lLoRat) * ((1 / 2 : ℝ) / (2 ^ W : ℝ)) ^ 2)) ^ 2 := by
  set dmax : ℝ := (1 / 2 : ℝ) / (2 ^ W : ℝ)
  set M : ℝ := (12 * (315 / 100) / lLoRat) * dmax ^ 2
  have hlLo_pos : 0 < lLoRat := lLoRat_pos
  have hlLo_le : lLoRat ≤ cellSide := lLoRat_le_cellSide
  have hM_nonneg : 0 ≤ M := by dsimp [M, dmax]; positivity
  have hentry : ∀ u v : Fin (2 ^ 18), ‖nucMatB W c l u v‖ ≤ M := fun u v ↦ by
    unfold nucMatB
    simp only [Matrix.of_apply]
    by_cases h : inGrid18 u ∧ inGrid18 v
    · rw [ite_pos h, norm_neg, norm_mul]
      set ν := pOf18 u - pOf18 v
      by_cases hν0 : ν = 0
      · rw [hν0, coulombKernel_zero]; simp [hM_nonneg]
      · have hK_eq := coulombKernel_eq_of_ne_zero hν0
        have hK_nonneg : 0 ≤ coulombKernel ν := by
          rw [hK_eq]
          have := Real.pi_pos
          have := cellSide_pos
          positivity
        rw [Complex.norm_real, Real.norm_of_nonneg hK_nonneg]
        have hθ_abs : |nucTheta W c l ν| ≤ 1 := by
          unfold nucTheta
          rw [abs_neg, abs_mul, abs_of_pos Real.two_pi_pos]
          have hν_le : ∀ w : Fin 3, |(ν w : ℝ)| ≤ 62 := fun w ↦ by
            have hu := h.1 w
            have hv := h.2 w
            unfold InMomGrid1D at hu hv
            have hw : |ν w| ≤ 62 := by
              change |pOf18 u w - pOf18 v w| ≤ 62
              rw [abs_le]; omega
            exact_mod_cast hw
          have hsum_le : |∑ w : Fin 3, (ν w : ℝ) * nucDelta W c l w| ≤ 3 * (62 * dmax) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            have ht : ∀ w : Fin 3, |(ν w : ℝ) * nucDelta W c l w| ≤ 62 * dmax := fun w ↦ by
              rw [abs_mul]
              exact mul_le_mul (hν_le w) (abs_nucDelta_le W c l w) (abs_nonneg _) (by norm_num)
            calc (∑ w : Fin 3, |(ν w : ℝ) * nucDelta W c l w|)
                ≤ ∑ _w : Fin 3, (62 * dmax) := Finset.sum_le_sum fun w _ ↦ ht w
              _ = 3 * (62 * dmax) := by norm_num
          have hdmax20 : dmax ≤ (1 / 2 : ℝ) / (2 ^ 20 : ℝ) := by
            dsimp [dmax]
            have hpow : (2 ^ 20 : ℝ) ≤ (2 ^ W : ℝ) := by
              exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) hW20
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
          have hpi : π < 3.15 := Real.pi_lt_d2
          nlinarith [Real.pi_pos]
        have hexp_le := norm_exp_ofReal_mul_I_sub_one_sub_le hθ_abs
        have hprod1 : coulombKernel ν * ‖Complex.exp ((nucTheta W c l ν : ℂ) * Complex.I) - 1
            - (nucTheta W c l ν : ℂ) * Complex.I‖ ≤ coulombKernel ν * (nucTheta W c l ν) ^ 2
            := mul_le_mul_of_nonneg_left hexp_le hK_nonneg
        refine hprod1.trans ?_
        rw [hK_eq]
        unfold nucTheta
        have hns_pos : 0 < normSqInt ν := Nat.pos_of_ne_zero (aux_normSqInt_ne_zero hν0)
        have hns_cast : (normSqInt ν : ℝ) = (ν 0 : ℝ) ^ 2 + (ν 1 : ℝ) ^ 2 + (ν 2 : ℝ) ^ 2 := by
          unfold normSqInt
          push_cast
          rw [cast_natAbs_sq_int, cast_natAbs_sq_int, cast_natAbs_sq_int]
        set δ := nucDelta W c l
        have hδ_sq : ∀ w : Fin 3, δ w ^ 2 ≤ dmax ^ 2 := fun w ↦ by
          have habs := abs_nucDelta_le W c l w
          have hd0 : 0 ≤ dmax := by dsimp [dmax]; positivity
          nlinarith [abs_le.mp habs]
        have hcs : (∑ w : Fin 3, (ν w : ℝ) * δ w) ^ 2 ≤
            (normSqInt ν : ℝ) * (3 * dmax ^ 2) := by
          rw [Fin.sum_univ_three, hns_cast]
          have hcs0 : ((ν 0 : ℝ) * δ 0 + (ν 1 : ℝ) * δ 1 + (ν 2 : ℝ) * δ 2) ^ 2 ≤
              ((ν 0 : ℝ) ^ 2 + (ν 1 : ℝ) ^ 2 + (ν 2 : ℝ) ^ 2) *
                (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) := by
            nlinarith [sq_nonneg ((ν 0 : ℝ) * δ 1 - (ν 1 : ℝ) * δ 0),
              sq_nonneg ((ν 0 : ℝ) * δ 2 - (ν 2 : ℝ) * δ 0),
              sq_nonneg ((ν 1 : ℝ) * δ 2 - (ν 2 : ℝ) * δ 1)]
          have hsum_δ : δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2 ≤ 3 * dmax ^ 2 := by
            linarith [hδ_sq 0, hδ_sq 1, hδ_sq 2]
          have hns_nn : 0 ≤ (ν 0 : ℝ) ^ 2 + (ν 1 : ℝ) ^ 2 + (ν 2 : ℝ) ^ 2 := by positivity
          exact hcs0.trans (mul_le_mul_of_nonneg_left hsum_δ hns_nn)
        have hnsR_pos : (0 : ℝ) < (normSqInt ν : ℝ) := by exact_mod_cast hns_pos
        have h1 : (1 : ℝ) / (π * cellSide) * (1 / (normSqInt ν : ℝ)) *
            (-(2 * π * ∑ w : Fin 3, (ν w : ℝ) * δ w)) ^ 2 ≤
            (12 * π / cellSide) * dmax ^ 2 := by
          have hθ_sq : (-(2 * π * ∑ w : Fin 3, (ν w : ℝ) * δ w)) ^ 2 ≤
              4 * π ^ 2 * ((normSqInt ν : ℝ) * (3 * dmax ^ 2)) := by
            have : (-(2 * π * ∑ w : Fin 3, (ν w : ℝ) * δ w)) ^ 2 =
                4 * π ^ 2 * (∑ w : Fin 3, (ν w : ℝ) * δ w) ^ 2 := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_left hcs (by positivity)
          have hpref_nn : 0 ≤ (1 : ℝ) / (π * cellSide) * (1 / (normSqInt ν : ℝ)) := by
            have := Real.pi_pos; have := cellSide_pos; positivity
          calc (1 : ℝ) / (π * cellSide) * (1 / (normSqInt ν : ℝ)) *
                (-(2 * π * ∑ w : Fin 3, (ν w : ℝ) * δ w)) ^ 2
              ≤ (1 : ℝ) / (π * cellSide) * (1 / (normSqInt ν : ℝ)) *
                  (4 * π ^ 2 * ((normSqInt ν : ℝ) * (3 * dmax ^ 2))) :=
                mul_le_mul_of_nonneg_left hθ_sq hpref_nn
            _ = (12 * π / cellSide) * dmax ^ 2 := by
                field_simp [Real.pi_ne_zero, cellSide_pos.ne', hnsR_pos.ne']
                ring
        refine h1.trans ?_
        dsimp only [M]
        have hpi_le : π ≤ 315 / 100 := by
          have := Real.pi_lt_d2; norm_num at this ⊢; linarith
        have hdiv_le : 12 * π / cellSide ≤ 12 * (315 / 100) / lLoRat := by
          calc 12 * π / cellSide
              ≤ 12 * (315 / 100) / cellSide := by
                exact div_le_div_of_nonneg_right (by linarith) cellSide_pos.le
            _ ≤ 12 * (315 / 100) / lLoRat :=
                div_le_div_of_nonneg_left (by norm_num) hlLo_pos hlLo_le
        exact mul_le_mul_of_nonneg_right hdiv_le (sq_nonneg dmax)
    · simp [h, hM_nonneg]
  have hsq_le : ∀ u v : Fin (2 ^ 18), ‖nucMatB W c l u v‖ ^ 2 ≤ M ^ 2 := fun u v ↦ by
    have h1 := hentry u v
    have h0 := norm_nonneg (nucMatB W c l u v)
    nlinarith
  calc (∑ u : Fin (2 ^ 18), ∑ v : Fin (2 ^ 18), ‖nucMatB W c l u v‖ ^ 2)
      ≤ ∑ _u : Fin (2 ^ 18), ∑ _v : Fin (2 ^ 18), M ^ 2 :=
        Finset.sum_le_sum fun u _ ↦ Finset.sum_le_sum fun v _ ↦ hsq_le u v
    _ = ((2 ^ 18 : ℝ) * M) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
theorem norm_fermionicProjector_le_one (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp‖ ≤ 1 := by
  let P := fermionicProjector spinUp
  have hP_herm : P.IsHermitian := fermionicProjector_isHermitian spinUp
  have hP_idem : P * P = P := fermionicProjector_idem spinUp
  have hsq : ‖P‖ * ‖P‖ = ‖P‖ := by
    calc ‖P‖ * ‖P‖ = ‖Pᴴ * P‖ := (Matrix.l2_opNorm_conjTranspose_mul_self P).symm
      _ = ‖P * P‖ := by rw [hP_herm.eq]
      _ = ‖P‖ := by rw [hP_idem]
  nlinarith [norm_nonneg P]
theorem norm_op_add_le {D : ℕ} [NeZero D] (X Y : Operator D) : ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ :=
  norm_add_le X Y
theorem norm_op_sum_le {D : ℕ} [NeZero D] {ι : Type*} (s : Finset ι) (f : ι → Operator D) :
    ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ s, ‖f x‖ :=
  norm_sum_le s f
theorem norm_proj_mul_op_mul_proj_le {D : ℕ} [NeZero D] (P M : Operator D) (hP : ‖P‖ ≤ 1)
    {B : ℝ} (hB0 : 0 ≤ B) (hM : ‖M‖ ≤ B) : ‖P * M * P‖ ≤ B := by
  calc ‖P * M * P‖ ≤ ‖P * M‖ * ‖P‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖M‖) * ‖P‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg P)
    _ ≤ (1 * B) * 1 := mul_le_mul (mul_le_mul hP hM (norm_nonneg _) zero_le_one) hP
        (norm_nonneg P) (by linarith)
    _ = B := by ring
theorem norm_proj_uEnManyBody_truncWCfg_sub_le {W : ℕ} (hW20 : 20 ≤ W)
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    let dmax : ℝ := (1 / 2 : ℝ) / (2 ^ W : ℝ)
    let FA : ℝ := (2 / lLoRat) * dmax * Real.sqrt ((1385394456 : ℝ) / 16)
    let FB : ℝ := (2 ^ 18 : ℝ) * ((12 * (315 / 100) / lLoRat) * dmax ^ 2)
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg W c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤
      216 * (Real.sqrt 218 * FA) + 216 * (218 * FB) := by
  intro dmax FA FB
  set P := fermionicProjector spinUp
  set V := oneElecNucDiagExact c
  have hP1 : ‖P‖ ≤ 1 := norm_fermionicProjector_le_one spinUp
  have hFA0 : 0 ≤ FA := by dsimp [FA, dmax]; have := lLoRat_pos; positivity
  have hFB0 : 0 ≤ FB := by dsimp [FB, dmax]; have := lLoRat_pos; positivity
  rw [proj_uEnManyBody_truncWCfg_sub_eq W c spinUp]
  have hA_sum : ‖∑ l : Fin 216, P * (∑ i : Fin numElectrons, (rEl_sp i).embedMatrix ((V l).1 *
      nucMatA W c l * (V l).1ᴴ)) * P‖ ≤ 216 * (Real.sqrt 218 * FA) := by
    calc ‖∑ l : Fin 216, P * (∑ i : Fin numElectrons,
            (rEl_sp i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ)) * P‖
        ≤ ∑ l : Fin 216, ‖P * (∑ i : Fin numElectrons,
            (rEl_sp i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ)) * P‖ := norm_op_sum_le _ _
      _ ≤ ∑ _l : Fin 216, (Real.sqrt 218 * FA) :=
          Finset.sum_le_sum fun l _ ↦ norm_proj_sandwich_embed_chiral_le (nucMatA W c l)
            (nucMatA_isHermitian W c l) (nucMatA_imag W c l) (V l) hFA0 (frob_nucMatA_le W c l)
              spinUp
      _ = 216 * (Real.sqrt 218 * FA) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
  have hB_sum : ‖∑ l : Fin 216, ∑ i : Fin numElectrons, P * (rEl_sp i).embedMatrix
      ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P‖ ≤ 216 * (218 * FB) := by
    have hper (l : Fin 216) (i : Fin numElectrons) :
        ‖P * (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P‖ ≤ FB :=
      norm_proj_mul_op_mul_proj_le P _ hP1 hFB0 (norm_embed_hermitian_le_frob (nucMatB W c l)
        (nucMatB_isHermitian W c l) (V l) hFB0 (frob_nucMatB_le hW20 c l) i)
    calc ‖∑ l : Fin 216, ∑ i : Fin numElectrons,
            P * (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P‖
        ≤ ∑ l : Fin 216, ‖∑ i : Fin numElectrons,
            P * (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P‖ :=
          norm_op_sum_le _ _
      _ ≤ ∑ l : Fin 216, ∑ i : Fin numElectrons,
            ‖P * (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P‖ :=
          Finset.sum_le_sum fun _ _ ↦ norm_op_sum_le _ _
      _ ≤ ∑ _l : Fin 216, ∑ _i : Fin numElectrons, FB :=
          Finset.sum_le_sum fun l _ ↦ Finset.sum_le_sum fun i _ ↦ hper l i
      _ = 216 * (218 * FB) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, numElectrons,
            nsmul_eq_mul]; ring
  exact (norm_op_add_le _ _).trans (add_le_add hA_sum hB_sum)
theorem bModSlot248_trunc_shifted_err_le_of_uEn
    (c' c : Configuration) {εu epsRaw : ℝ}
    (huEn : ∀ spinUp0 : Finset (Fin numElectrons),
      ‖fermionicProjector spinUp0 * (uEnManyBody c' - uEnManyBody c) *
        fermionicProjector spinUp0‖ ≤ εu)
    (harith : (257 : ℝ) / 10000000 + εu ≤ epsRaw)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 c' - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ epsRaw := by
  intro E2only
  let P := fermionicProjector spinUp
  have hsub2 : sixChannelShifted c' E2only 2 - sixChannelShifted c E2only 2 =
      uEnManyBody c' - uEnManyBody c := by
    unfold sixChannelShifted
    rw [← uEnManyBody_eq_sixChannelRaw c', ← uEnManyBody_eq_sixChannelRaw c]; abel
  rw [show bModSlot248 c' - sixChannelShifted c E2only 2 =
      (bModSlot248 c' - sixChannelShifted c' E2only 2) + (uEnManyBody c' - uEnManyBody c) by
      rw [← hsub2]; abel,
    Matrix.mul_add, Matrix.add_mul]
  exact (norm_add_le _ _).trans
    ((add_le_add (bModSlot248_shifted_err_le_tight c' spinUp) (huEn spinUp)).trans harith)
set_option maxRecDepth 2000
end ConfigSubvoxelNuclearTrunc34And33Physics
end SubvoxelNuclearTrunc34And33Physics
end
end ModSubvoxelNuclearTrunc34And33Physics
end SubvoxelNuclearTrunc34And33Physics
end
set_option exponentiation.threshold 256
end SubvoxelNuclearTrunc34And33PhysicsAux

section SubvoxelNuclearTrunc28To35ChiralAux
local instance (priority := 1000000) instNeZeroTwoPow_SubvoxelNuclearTrunc28To35Chiral (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩


public section
section SubvoxelNuclearTrunc28To35Chiral

section ModSubvoxelNuclearTrunc28To35Chiral
public section
namespace SubvoxelNuclearTrunc28To35Chiral
section ConfigSubvoxelNuclearTrunc28To35Chiral
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option exponentiation.threshold 256
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority :=
  1000000) instLoc_SubvoxelNuclearTrunc28To35Chiral_1InstNeZero (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
open SpecsAux.DyadicSubgridToeplitz512AndShift (NyqFine3D512)
open NuclearTwistAndXor654Concrete (nuclearM48)
open PosSlots24MergedVepBound (cfgProjZ512 cellLength_ne_zero)
open Pos24Slot2FermionicBridge (pos24Slot2E2Const bModSlot248)
open SubvoxelNuclearTrunc37Physics (nuclearM37 trunc37Cfg)
open SubvoxelNuclearTrunc34And33Physics (nuclearMW nuclearMW_lt truncWCfg lLoRat lLoRat_pos
  norm_proj_uEnManyBody_truncWCfg_sub_le bModSlot248_trunc_shifted_err_le_of_uEn)
theorem aux_nuclearMK_of_mW_arith {K W : ℕ} (hW : W ≤ K) (m : ℕ) (hm : m < 2 ^ W) :
    (m : ℝ) / (2 ^ W : ℝ) < 1 ∧
    (2 ^ K : ℝ) * ((m : ℝ) / (2 ^ W : ℝ)) + 1 / 2 = ((2 ^ (K - W) * m : ℕ) : ℝ) + 1 / 2 ∧
    ⌊((2 ^ (K - W) * m : ℕ) : ℝ) + 1 / 2⌋₊ = 2 ^ (K - W) * m ∧
    (2 ^ (K - W) * m) % 2 ^ K = 2 ^ (K - W) * m := by
  have hmR : (m : ℝ) < (2 ^ W : ℝ) := by exact_mod_cast hm
  have hpow : 2 ^ (K - W) * 2 ^ W = 2 ^ K := by rw [← pow_add, Nat.sub_add_cancel hW]
  have hlt : 2 ^ (K - W) * m < 2 ^ K := hpow ▸ Nat.mul_lt_mul_of_pos_left hm (Nat.two_pow_pos _)
  have hpowR : ((2 : ℝ) ^ (K - W)) * ((2 : ℝ) ^ W) = (2 : ℝ) ^ K := by
    rw [← pow_add, Nat.sub_add_cancel hW]
  refine ⟨(div_lt_one (by positivity)).mpr hmR, ?_, ?_, Nat.mod_eq_of_lt hlt⟩
  · have h2W : ((2 : ℝ) ^ W) ≠ 0 := by positivity
    rw [show (2 ^ K : ℝ) = (2 : ℝ) ^ K by norm_num,
      show (2 ^ W : ℝ) = (2 : ℝ) ^ W by norm_num, ← hpowR]
    push_cast; field_simp [h2W]
  · rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
theorem nuclearM48_truncWCfg {W : ℕ} (hW : W ≤ 48) (c : Configuration) (l : Fin 216) (w : Fin 3) :
    nuclearM48 (truncWCfg W c) l w = 2 ^ (48 - W) * nuclearMW W c l w := by
  have hL : cellVolume ^ (1 / 3 : ℝ) ≠ 0 := by simpa [one_div] using cellLength_ne_zero
  obtain ⟨h1, h2, h3, h4⟩ := aux_nuclearMK_of_mW_arith hW (nuclearMW W c l w) (nuclearMW_lt W c l w)
  unfold nuclearM48 truncWCfg
  have hdiv : (nuclearMW W c l w : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / (2 ^ W : ℝ)) /
      cellVolume ^ (1 / 3 : ℝ) = (nuclearMW W c l w : ℝ) / (2 ^ W : ℝ) := by field_simp [hL]
  rw [hdiv, Int.fract_eq_self.mpr ⟨by positivity, h1⟩, h2, h3]
  exact h4
theorem nuclearM48_truncWCfg_dvd {W : ℕ} (hW : W ≤ 48) (c : Configuration) (l : Fin 216)
    (w : Fin 3) : 2 ^ (48 - W) ∣ nuclearM48 (truncWCfg W c) l w := by
  rw [nuclearM48_truncWCfg hW]
  exact dvd_mul_right (2 ^ (48 - W)) _
theorem nuclearMW_cfgProjZ512_eq {W : ℕ} (hW : 9 ≤ W) (zP : NyqFine3D512) (l : Fin 216)
    (w : Fin 3) : nuclearMW W (cfgProjZ512 zP) l w = 2 ^ (W - 9) * (zP w).val := by
  have hL : cellVolume ^ ((1 : ℝ) / 3) ≠ 0 := by simpa [one_div] using cellLength_ne_zero
  have hz9 : (zP w).val < 2 ^ 9 := lt_of_lt_of_eq (zP w).isLt (by norm_num)
  obtain ⟨h1, h2, h3, h4⟩ := aux_nuclearMK_of_mW_arith hW (zP w).val hz9
  rw [show (2 ^ 9 : ℝ) = 512 by norm_num] at h1 h2
  unfold nuclearMW cfgProjZ512
  have hdiv : ((zP w).val : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / 512) /
      cellVolume ^ ((1 : ℝ) / 3) = ((zP w).val : ℝ) / 512 := by field_simp [hL]
  rw [hdiv, Int.fract_eq_self.mpr ⟨by positivity, h1⟩, h2, h3]
  exact h4
theorem truncWCfg_cfgProjZ512 {W : ℕ} (hW : 9 ≤ W) (zP : NyqFine3D512) :
    truncWCfg W (cfgProjZ512 zP) = cfgProjZ512 zP := by
  have hpowR : ((2 : ℝ) ^ (W - 9)) * 512 = (2 : ℝ) ^ W := by
    have hpow : 2 ^ (W - 9) * 2 ^ 9 = 2 ^ W := by rw [← pow_add, Nat.sub_add_cancel hW]
    exact_mod_cast hpow
  have hN : (fun (l : Fin 216) (w : Fin 3) ↦ (nuclearMW W (cfgProjZ512 zP) l w : ℝ) *
      (cellVolume ^ ((1 : ℝ) / 3) / (2 ^ W : ℝ))) = (cfgProjZ512 zP).nuclei := by
    funext l w
    rw [nuclearMW_cfgProjZ512_eq hW]
    unfold cfgProjZ512
    have h2W : ((2 : ℝ) ^ W) ≠ 0 := by positivity
    rw [show (2 ^ W : ℝ) = (2 : ℝ) ^ W by norm_num, ← hpowR]
    push_cast; field_simp [h2W]
  unfold truncWCfg; rw [hN]
theorem nuclearM37_truncWCfg {W : ℕ} (hW : W ≤ 37) (c : Configuration) (l : Fin 216) (w : Fin 3) :
    nuclearM37 (truncWCfg W c) l w = 2 ^ (37 - W) * nuclearMW W c l w := by
  have hL : cellVolume ^ ((1 : ℝ) / 3) ≠ 0 := by simpa [one_div] using cellLength_ne_zero
  obtain ⟨h1, h2, h3, h4⟩ := aux_nuclearMK_of_mW_arith hW (nuclearMW W c l w) (nuclearMW_lt W c l w)
  unfold nuclearM37 truncWCfg
  have hdiv : (nuclearMW W c l w : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / (2 ^ W : ℝ)) /
      cellVolume ^ ((1 : ℝ) / 3) = (nuclearMW W c l w : ℝ) / (2 ^ W : ℝ) := by field_simp [hL]
  rw [hdiv, Int.fract_eq_self.mpr ⟨by positivity, h1⟩, h2, h3]
  exact h4
theorem trunc37Cfg_truncWCfg {W : ℕ} (hW : W ≤ 37) (c : Configuration) :
    trunc37Cfg (truncWCfg W c) = truncWCfg W c := by
  have hpowR : ((2 : ℝ) ^ (37 - W)) * ((2 : ℝ) ^ W) = (2 : ℝ) ^ 37 := by
    rw [← pow_add, Nat.sub_add_cancel hW]
  have hN : (fun (l : Fin 216) (w : Fin 3) ↦ (nuclearM37 (truncWCfg W c) l w : ℝ) *
      (cellVolume ^ ((1 : ℝ) / 3) / (2 ^ 37 : ℝ))) = (truncWCfg W c).nuclei := by
    funext l w
    rw [nuclearM37_truncWCfg hW]
    unfold truncWCfg
    have h2W : ((2 : ℝ) ^ W) ≠ 0 := by positivity
    rw [show (2 ^ 37 : ℝ) = (2 : ℝ) ^ 37 by norm_num,
      show (2 ^ W : ℝ) = (2 : ℝ) ^ W by norm_num, ← hpowR]
    push_cast; field_simp [h2W]
  unfold trunc37Cfg; rw [hN]
theorem aux_bModSlot248_truncW_shifted_err_le_chiral (W : ℕ) (aN bN uN sN : ℝ)
    (c : Configuration) (spinUp : Finset (Fin numElectrons))
    (hW : 20 ≤ W := by decide) (ha_nn : 0 ≤ aN := by norm_num)
    (hA : 216 ^ 2 * 218 * ((2 / lLoRat) * ((1 / 2 : ℝ) / (2 ^ W : ℝ))) ^ 2 *
      ((1385394456 : ℝ) / 16) ≤ aN ^ 2 := by dsimp [lLoRat]; norm_num)
    (hB : 216 * (218 * ((2 ^ 18 : ℝ) * ((12 * (315 / 100) / lLoRat) *
      ((1 / 2 : ℝ) / (2 ^ W : ℝ)) ^ 2))) ≤ bN := by dsimp [lLoRat]; norm_num)
    (hu : aN + bN ≤ uN := by norm_num) (hs : uN + (257 : ℝ) / 10000000 ≤ sN := by norm_num) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg W c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ sN := by
  refine bModSlot248_trunc_shifted_err_le_of_uEn (εu := uN) (truncWCfg W c) c (fun sp ↦ ?_)
    (by linarith) spinUp
  refine (norm_proj_uEnManyBody_truncWCfg_sub_le hW c sp).trans ?_
  set dmax : ℝ := (1 / 2 : ℝ) / (2 ^ W : ℝ)
  set FA : ℝ := (2 / lLoRat) * dmax * Real.sqrt ((1385394456 : ℝ) / 16)
  have hA_sq : (216 * (Real.sqrt 218 * FA)) ^ 2 ≤ aN ^ 2 := by
    refine (?_ : (216 * (Real.sqrt 218 * FA)) ^ 2 = _).trans_le hA
    dsimp [FA]; rw [mul_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 218),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1385394456 : ℝ) / 16)]; ring
  have hnn : 0 ≤ 216 * (Real.sqrt 218 * FA) := by dsimp [FA, dmax]; have := lLoRat_pos; positivity
  have hA_le := (mul_self_le_mul_self_iff hnn ha_nn).mpr (by simpa [sq] using hA_sq)
  linarith [hB, hu]
noncomputable abbrev trunc28Cfg : Configuration → Configuration := truncWCfg 28
noncomputable def eps2_trunc28_chiral : ℝ := (8185003 : ℝ) / 1000000000
theorem bModSlot248_trunc28_shifted_err_le_chiral (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (trunc28Cfg c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (8260552 : ℝ) / 1000000000 :=
  aux_bModSlot248_truncW_shifted_err_le_chiral 28 ((8234731 : ℝ) / 1000000000)
    ((121 : ℝ) / 1000000000) ((8234852 : ℝ) / 1000000000) _ c spinUp
noncomputable abbrev trunc29Cfg : Configuration → Configuration := truncWCfg 29
noncomputable def eps2_trunc29_chiral : ℝ := (4105323 : ℝ) / 1000000000
theorem bModSlot248_trunc29_shifted_err_le_chiral (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (trunc29Cfg c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (4143097 : ℝ) / 1000000000 :=
  aux_bModSlot248_truncW_shifted_err_le_chiral 29 ((4117366 : ℝ) / 1000000000)
    ((31 : ℝ) / 1000000000) ((4117397 : ℝ) / 1000000000) _ c spinUp
noncomputable abbrev trunc30Cfg : Configuration → Configuration := truncWCfg 30
noncomputable def eps2_trunc30_chiral : ℝ := (2065504 : ℝ) / 1000000000
theorem bModSlot248_trunc30_shifted_err_le_chiral (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (trunc30Cfg c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (2084391 : ℝ) / 1000000000 :=
  aux_bModSlot248_truncW_shifted_err_le_chiral 30 ((2058683 : ℝ) / 1000000000)
    ((8 : ℝ) / 1000000000) ((2058691 : ℝ) / 1000000000) _ c spinUp
noncomputable abbrev trunc31Cfg : Configuration → Configuration := truncWCfg 31
noncomputable def eps2_trunc31_chiral : ℝ := (1045601 : ℝ) / 1000000000
theorem bModSlot248_trunc31_shifted_err_le_chiral (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (trunc31Cfg c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (1055044 : ℝ) / 1000000000 :=
  aux_bModSlot248_truncW_shifted_err_le_chiral 31 ((1029342 : ℝ) / 1000000000)
    ((2 : ℝ) / 1000000000) ((1029344 : ℝ) / 1000000000) _ c spinUp
noncomputable abbrev trunc32Cfg : Configuration → Configuration := truncWCfg 32
noncomputable def eps2_trunc32_chiral : ℝ := (535651 : ℝ) / 1000000000
theorem bModSlot248_trunc32_shifted_err_le_chiral (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (trunc32Cfg c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (540372 : ℝ) / 1000000000 :=
  aux_bModSlot248_truncW_shifted_err_le_chiral 32 ((514671 : ℝ) / 1000000000)
    ((1 : ℝ) / 1000000000) ((514672 : ℝ) / 1000000000) _ c spinUp
noncomputable abbrev trunc33Cfg : Configuration → Configuration := truncWCfg 33
noncomputable def eps2_trunc33_chiral : ℝ := (280677 : ℝ) / 1000000000
theorem bModSlot248_trunc33_shifted_err_le_chiral (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (trunc33Cfg c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (283037 : ℝ) / 1000000000 :=
  aux_bModSlot248_truncW_shifted_err_le_chiral 33 ((257336 : ℝ) / 1000000000)
    ((1 : ℝ) / 1000000000) ((257337 : ℝ) / 1000000000) _ c spinUp
set_option maxRecDepth 2000
end ConfigSubvoxelNuclearTrunc28To35Chiral
end SubvoxelNuclearTrunc28To35Chiral
end
end ModSubvoxelNuclearTrunc28To35Chiral
end SubvoxelNuclearTrunc28To35Chiral
end
set_option exponentiation.threshold 256
end SubvoxelNuclearTrunc28To35ChiralAux

section SharedUnaryTrunc37Stitch220
local instance (priority := 1000000) instNeZeroTwoPow_SharedUnaryTrunc37Stitch220 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Shared-Unary `Apex-T` 3-Axis Stitch on `mWork ≥ 220`

Parametric zero-`.TOFF` 3-axis shared-unary and `0-T` `X`-uncompute stitch for
`Slot2ZeroMuxSignedMul46.apexCatModAddZ` (`45`-bit low modular add + `dyadicTurn 48` phase):

1. `UnitaryPhasePerm` & `withSharedBank114_phasePerm_const`: lifts `withSharedBank114` (`456 T`,
   `0` `.TOFF`) from classical permutations (`UnitaryPerm`) to arbitrary computational-basis
   phase-permutations (`|β⟩ ↦ φ β • |f β⟩`) modifying only `M_set` disjoint from
   `rCore`, `rS7`, `rU108`.
2. `apexCatModAddZ_mul`, `uInner3AxesApex`, & `dHeldBankApexAxisInner`: proves the exact group
   homomorphism law for `apexCatModAddZ` and bridges any per-axis `uXorRawBank` load + Order-B
   `apexCatModAddZ` kick (`mScr ≤ 57`) + `0-T` `dZeroTXUncM48Tail` on `rTail : QRegister 105 n`.
3. `mkSharedUnaryApex3AxesKoff` & `mkSharedUnaryApex3AxesO1`: packages `6,636 T/side`
   (`184 + 1,876 T/ax`), `6,401 T/side` (`184 + 1,648 T/ax + 449 T`), and `6,213 T/side`
   (`180 + 1,592 T/ax + 441 T`) into `SharedUnary3AxisApexInnerSpec mWork c'`
   for all `220 ≤ mWork` (covering `220`, `248`, and `288` clean workspace widths).
-/

public section

namespace SharedUnaryTrunc37Stitch220

section ConfigSharedUnaryTrunc37Stitch220

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real HermitianMat
open scoped Matrix BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder Circuit.Notation

open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64.PhasePerm SpecsAux
open SpecsAux.SpecMirror
open QRegExt

local instance (priority :=
  1000000) instLoc_SharedUnaryTrunc37Stitch220_1InstNeZeroTwoPo (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

def UnitaryPhasePerm {n : ℕ} (U : Unitary (2 ^ n))
    (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n) : Prop :=
  ∀ β : BitAssignment n, U.1.mulVec (basisKet β) = φ β • basisKet (f β)

theorem UnitaryPhasePerm.mul {n : ℕ} {U₁ U₂ : Unitary (2 ^ n)}
    {φ₁ φ₂ : BitAssignment n → ℂ} {f₁ f₂ : BitAssignment n → BitAssignment n}
    (h₁ : UnitaryPhasePerm U₁ φ₁ f₁) (h₂ : UnitaryPhasePerm U₂ φ₂ f₂) :
    UnitaryPhasePerm (U₂ * U₁) (fun β ↦ φ₁ β * φ₂ (f₁ β)) (f₂ ∘ f₁) := fun β ↦ by
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h₁ β, Matrix.mulVec_smul,
    Function.comp_apply, h₂ (f₁ β), smul_smul]

/- ## Section 3: `220`-Wire Workspace Partition, Held-Bank `abbrev`s, & `uInner3AxesApex` -/

end ConfigSharedUnaryTrunc37Stitch220

set_option maxRecDepth 512
set_option exponentiation.threshold 256

end SharedUnaryTrunc37Stitch220
end
set_option exponentiation.threshold 256
end SharedUnaryTrunc37Stitch220

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
