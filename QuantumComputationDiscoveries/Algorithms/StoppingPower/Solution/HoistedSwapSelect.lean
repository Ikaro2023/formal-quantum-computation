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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DyadicQft64Walk288
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModHoistedSwapSelectBridge
@[expose] public section
namespace HoistedSwapSelectBridge
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open PosMomSelectSandwich
open FullSysCatSegmentBridge
open scoped Matrix BigOperators
instance (priority := 100000) instNeZeroTwoPowHoisted (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
noncomputable def unitaryConj {d : ℕ} (B M : Unitary d) : Unitary d := B⁻¹ * M * B
theorem unitaryConj_val {d : ℕ} (B M : Unitary d) :
    (unitaryConj B M).1 = B.1ᴴ * M.1 * B.1 := by
  have hB : (B⁻¹).1 = B.1ᴴ := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  rw [unitaryConj, Submonoid.coe_mul, Submonoid.coe_mul, hB]
theorem unitaryConj_conjTranspose {d : ℕ} {B M : Unitary d} (hM : M.1ᴴ = M.1) :
    (unitaryConj B M).1ᴴ = (unitaryConj B M).1 := by
  rw [unitaryConj_val, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    hM, Matrix.mul_assoc]
theorem embedUnitary_inv_eq {k n : ℕ} (r : QRegister k n) (U : Unitary (2 ^ k)) :
    r.embedUnitary U⁻¹ = (r.embedUnitary U)⁻¹ :=
  (inv_eq_of_mul_eq_one_right
    (by rw [← QRegister.embedUnitary_mul, mul_inv_cancel, QRegister.embedUnitary_one])).symm
theorem fullSys_zero_add_le (a b : ℕ) : 0 + a ≤ a + b := by omega
theorem intertwinesLocalCat_mul {kAct mCat : ℕ} {U_cat : Unitary (2 ^ mCat)}
    {W₁ W₂ : Unitary (2 ^ (kAct + mCat))} {U₁ U₂ : Unitary (2 ^ kAct)}
    (h₁ : IntertwinesLocalCat U_cat W₁ U₁) (h₂ : IntertwinesLocalCat U_cat W₂ U₂) :
    IntertwinesLocalCat U_cat (W₁ * W₂) (U₁ * U₂) := by
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (fullSys_zero_add_le kAct mCat)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  change IntertwinesCat (rCat0.embedUnitary U_cat).1 (rCat0.basisOutcomeProjector 0)
    (W₁ * W₂).1 (rAct0.embedUnitary (U₁ * U₂)).1
  rw [Submonoid.coe_mul, QRegister.embedUnitary_mul, Submonoid.coe_mul]
  exact h₁.mul h₂
structure FullSysHoistedSelectBundle (mPayload mPGTwist : ℕ) where
  hmPay : 6 ≤ mPayload
  uBarrel : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))
  uMomLocalCat : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (fullSysCoreWires mPayload + mPGTwist))
  uMomLocal : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))
  uTwistRestCat : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (fullSysCoreWires mPayload + mPGTwist))
  uTwistRest : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))
  uPosPhase : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))
  hIntertwinesMomLocal : ∀ c (U_catTwist : Unitary (2 ^ mPGTwist)),
    (∀ m : Fin (2 ^ mPGTwist),
      U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState mPGTwist m) →
    IntertwinesLocalCat U_catTwist (uMomLocalCat c) (uMomLocal c)
  hIntertwinesTwistRest : ∀ c (U_catTwist : Unitary (2 ^ mPGTwist)),
    (∀ m : Fin (2 ^ mPGTwist),
      U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState mPGTwist m) →
    IntertwinesLocalCat U_catTwist (uTwistRestCat c) (uTwistRest c)
  hBarrel_comm_P0 : ∀ c,
    (uBarrel c).1 * slotBitProj (iSlot2 mPayload) 0 = slotBitProj (iSlot2 mPayload) 0 *
      (uBarrel c).1
  hMomLocal_sa : ∀ c, (uMomLocal c).1ᴴ = (uMomLocal c).1
  hMomLocal_on_P0 : ∀ c,
    (uMomLocal c).1 * slotBitProj (iSlot2 mPayload) 0 = slotBitProj (iSlot2 mPayload) 0
  hTwistRest_comm_P1 : ∀ c,
    (uTwistRest c).1 * slotBitProj (iSlot2 mPayload) 1 =
      slotBitProj (iSlot2 mPayload) 1 * (uTwistRest c).1
  hPos_sa : ∀ c, (uPosPhase c).1ᴴ = (uPosPhase c).1
  hPos_on_P1 : ∀ c,
    (uPosPhase c).1 * slotBitProj (iSlot2 mPayload) 1 = slotBitProj (iSlot2 mPayload) 1
noncomputable def FullSysHoistedSelectBundle.uBarrelCat {mPayload mPGTwist : ℕ}
    (hsel : FullSysHoistedSelectBundle mPayload mPGTwist) (c : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload + mPGTwist)) := (QRegister.block 0
    (fullSysCoreWires mPayload) (fullSys_zero_add_le (fullSysCoreWires mPayload)
    mPGTwist)).embedUnitary (hsel.uBarrel c)
theorem FullSysHoistedSelectBundle.barrel_comm_P1 {mPayload mPGTwist : ℕ}
    (hsel : FullSysHoistedSelectBundle mPayload mPGTwist) (c : SpecsAux.SpecMirror.Configuration) :
    (hsel.uBarrel c).1 * slotBitProj (iSlot2 mPayload) 1 = slotBitProj (iSlot2 mPayload) 1 *
    (hsel.uBarrel c).1 := by
  have hP1 : slotBitProj (iSlot2 mPayload) 1 = 1 - slotBitProj (iSlot2 mPayload) 0 :=
    eq_sub_of_add_eq' (FullSysCatSegmentBridge.slotBitProj_zero_add_one (iSlot2 mPayload))
  rw [hP1, Matrix.mul_sub, Matrix.mul_one, hsel.hBarrel_comm_P0 c, Matrix.sub_mul, Matrix.one_mul]
noncomputable def FullSysHoistedSelectBundle.toSelectOracleBundle {mPayload mPGTwist : ℕ}
    (hsel : FullSysHoistedSelectBundle mPayload mPGTwist) :
    FullSysSelectOracleBundle mPayload mPGTwist where
  hmPay := hsel.hmPay
  uMomPhaseCat := fun c ↦ unitaryConj (hsel.uBarrelCat c) (hsel.uMomLocalCat c)
  uMomPhase := fun c ↦ unitaryConj (hsel.uBarrel c) (hsel.uMomLocal c)
  uTwistCat := fun c ↦ hsel.uTwistRestCat c * hsel.uBarrelCat c
  uTwist := fun c ↦ hsel.uTwistRest c * hsel.uBarrel c
  uPosPhase := hsel.uPosPhase
  hIntertwinesMom := fun c U_catTwist hPG ↦ by
    have iB := liftCleanCoreToTwistCat U_catTwist (hsel.uBarrel c)
    exact intertwinesLocalCat_mul (intertwinesLocalCat_mul iB.inv
      (hsel.hIntertwinesMomLocal c U_catTwist hPG)) iB
  hIntertwinesTwist := fun c U_catTwist hPG ↦
    intertwinesLocalCat_mul (hsel.hIntertwinesTwistRest c U_catTwist hPG)
      (liftCleanCoreToTwistCat U_catTwist (hsel.uBarrel c))
  hMom_sa := fun c ↦ unitaryConj_conjTranspose (hsel.hMomLocal_sa c)
  hMom_on_P0 := fun c ↦ by
    rw [unitaryConj_val]
    exact momCleanOp_on_posSlot (congrArg Subtype.val (inv_mul_cancel (hsel.uBarrel c)))
      (hsel.hBarrel_comm_P0 c) (hsel.hMomLocal_on_P0 c)
  hTwist_comm_P1 := fun c ↦ by
    simp only [Submonoid.coe_mul]
    calc (hsel.uTwistRest c).1 * (hsel.uBarrel c).1 * slotBitProj (iSlot2 mPayload) 1
        = (hsel.uTwistRest c).1 * (slotBitProj (iSlot2 mPayload) 1 * (hsel.uBarrel c).1) := by
            rw [Matrix.mul_assoc, hsel.barrel_comm_P1 c]
      _ = ((hsel.uTwistRest c).1 * slotBitProj (iSlot2 mPayload) 1) * (hsel.uBarrel c).1 := by
            simp only [Matrix.mul_assoc]
      _ = slotBitProj (iSlot2 mPayload) 1 * ((hsel.uTwistRest c).1 * (hsel.uBarrel c).1) := by
            rw [hsel.hTwistRest_comm_P1 c, Matrix.mul_assoc]
  hPos_sa := hsel.hPos_sa
  hPos_on_P1 := hsel.hPos_on_P1
end HoistedSwapSelectBridge
end
end ModHoistedSwapSelectBridge

section ModMomSlots01Slot0ElectronKinetic
@[expose] public section
namespace MomSlots01Slot0ElectronKineticAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end MomSlots01Slot0ElectronKineticAlt
namespace MomSlots01Slot0ElectronKinetic
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.DyadicSubgridToeplitz128
open Slots01AndGridGuardBridge
open PosMomSelectSandwich
open PosMomSelectDynamic
open SixSlotEndpointJunctionBridge
open FullSysPrepare6Slot
open FullSysPosSlots24AndTopConcrete
open TwosCompAndWire0Cancel
open LiteralKineticAndMidpoint128
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (elecKinOp sixChannelRaw sixChannelShifted)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
private theorem lemHex339 {c : Prop} [Decidable c] (hc : c) {α : Sort*} {t e : α} :
    (if c then t else e) = t := by simp [hc]
private theorem lemHex33a {c : Prop} [Decidable c] (hnc : ¬c) {α : Sort*} {t e : α} :
    (if c then t else e) = e := by simp [hnc]
private theorem lemHex33b {c : Prop} [Decidable c] (hc : c) {α : Sort*}
    {t : c → α} {e : ¬c → α} : (if h : c then t h else e h) = t hc := by simp [hc]
private theorem lemHex33c {c : Prop} [Decidable c] (hnc : ¬c) {α : Sort*}
    {t : c → α} {e : ¬c → α} : (if h : c then t h else e h) = e hnc := by simp [hnc]
abbrev selWiresSym (mPayload : ℕ) : ℕ := 6 + mPayload
abbrev coreWiresSym (mPayload : ℕ) : ℕ := SpecsAux.SpecMirror.systemQubits + selWiresSym mPayload
abbrev selCoin3Sym (mPayload : ℕ) : QRegister 3 (selWiresSym mPayload) :=
  QRegister.block 0 3 (by dsimp [selWiresSym]; omega)
abbrev coreSysSym (mPayload : ℕ) : QRegister SpecsAux.SpecMirror.systemQubits (coreWiresSym
    mPayload) :=
  QRegister.block 0 SpecsAux.SpecMirror.systemQubits (by dsimp [coreWiresSym]; omega)
abbrev coreAncSym (mPayload : ℕ) : QRegister (selWiresSym mPayload) (coreWiresSym mPayload) :=
  QRegister.block SpecsAux.SpecMirror.systemQubits (selWiresSym mPayload) le_rfl
abbrev corePayloadSym (mPayload : ℕ) : QRegister mPayload (coreWiresSym mPayload) :=
  QRegister.block (SpecsAux.SpecMirror.systemQubits + 6) mPayload (by
    dsimp [coreWiresSym, selWiresSym]
    omega)
noncomputable abbrev coreHadamardUnitary (mPayload : ℕ) : Unitary (2 ^ (coreWiresSym mPayload)) :=
  (hadamardAll (corePayloadSym mPayload)).eval
abbrev iSlot0Mom (mPayload : ℕ) : Wire (coreWiresSym mPayload) :=
  ⟨3948, by
    dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega⟩
abbrev iSlot1Mom (mPayload : ℕ) : Wire (coreWiresSym mPayload) :=
  ⟨3949, by
    dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega⟩
abbrev iSlot2Mom (mPayload : ℕ) : Wire (coreWiresSym mPayload) :=
  ⟨3950, by
    dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega⟩
def coinBitFin2 (c : Fin 8) (j : Fin 3) : Fin 2 := ⟨(basisBits 3 c j).val, ZMod.val_lt _⟩
noncomputable def momCoinProj (mPayload : ℕ) (c : Fin 8) : Operator
    (2 ^ (coreWiresSym mPayload)) := slotBitProj (iSlot0Mom mPayload) (coinBitFin2 c 0) *
    slotBitProj (iSlot1Mom mPayload) (coinBitFin2 c 1) * slotBitProj (iSlot2Mom mPayload)
    (coinBitFin2 c 2)
def slot0AxisInt (u : Fin 64) : ℤ := if u.val = 32 then 0 else twosComp6Int u
noncomputable def slot0Thresh (w_eff : ℝ) (u : Fin 64) : ℕ := Nat.floor ((2 : ℝ) ^ 41 * (1 -
    654 * ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) * ((slot0AxisInt u : ℝ) ^
    2 - 961 / 2) / w_eff))
def crtFwdNat (m : ℕ) : ℕ := 3 * (2 * ((m / 2) % 109) + (m % 2)) + (m % 3)
def crtInvNat (n : ℕ) : ℕ :=
  let q := n / 3
  let a := n % 3
  q + 218 * ((2 * a + q) % 3)
theorem crtFwdNat_lt (m : Fin 654) : crtFwdNat m.val < 654 := by
  have := m.isLt
  dsimp only [crtFwdNat]
  omega
theorem crtInvNat_lt (n : Fin 654) : crtInvNat n.val < 654 := by
  have := n.isLt
  dsimp only [crtInvNat]
  omega
theorem crt_left_inv_nat (m : ℕ) (hm : m < 654) : crtInvNat (crtFwdNat m) = m := by
  dsimp only [crtFwdNat, crtInvNat]
  have hq : (3 * (2 * ((m / 2) % 109) + (m % 2)) + (m % 3)) / 3 =
      2 * ((m / 2) % 109) + (m % 2) := by omega
  have ha : (3 * (2 * ((m / 2) % 109) + (m % 2)) + (m % 3)) % 3 = m % 3 := by omega
  rw [hq, ha]
  omega
theorem crt_right_inv_nat (n : ℕ) (hn : n < 654) : crtFwdNat (crtInvNat n) = n := by
  dsimp only [crtFwdNat, crtInvNat]
  have hd2 : (n / 3 + 218 * ((2 * (n % 3) + n / 3) % 3)) / 2 =
      (n / 3) / 2 + 109 * ((2 * (n % 3) + n / 3) % 3) := by omega
  have hm109 : ((n / 3) / 2 + 109 * ((2 * (n % 3) + n / 3) % 3)) % 109 = (n / 3) / 2 := by omega
  rw [hd2, hm109]
  omega
def crtPerm654 : Equiv.Perm (Fin 654) where
  toFun m := ⟨crtFwdNat m.val, crtFwdNat_lt m⟩
  invFun n := ⟨crtInvNat n.val, crtInvNat_lt n⟩
  left_inv m := Fin.ext (crt_left_inv_nat m.val m.isLt)
  right_inv n := Fin.ext (crt_right_inv_nat n.val n.isLt)
theorem crtPerm654_mod3 (m : Fin 654) : (crtPerm654 m).val % 3 = m.val % 3 := by
  have := m.isLt
  change crtFwdNat m.val % 3 = m.val % 3
  dsimp only [crtFwdNat]
  omega
theorem crtPerm654_div3 (m : Fin 654) :
    (crtPerm654 m).val / 3 = 2 * ((m.val / 2) % 109) + (m.val % 2) := by
  have := m.isLt
  change crtFwdNat m.val / 3 = 2 * ((m.val / 2) % 109) + (m.val % 2)
  dsimp only [crtFwdNat]
  omega
theorem crtPerm654_slot0_div3 (u36 bPar : ℕ) (hb : bPar < 2) :
    (crtPerm654 ⟨2 * (u36 % 327) + bPar, by
      have := Nat.mod_lt u36 (by omega : 0 < 327); omega⟩).val / 3 =
      2 * (u36 % 109) + bPar := by
  rw [crtPerm654_div3]
  dsimp only
  have hdiv : (2 * (u36 % 327) + bPar) / 2 = u36 % 327 := by omega
  have hmod : (2 * (u36 % 327) + bPar) % 2 = bPar := by omega
  have h109 : (u36 % 327) % 109 = u36 % 109 := Nat.mod_mod_of_dvd u36 ⟨3, rfl⟩
  rw [hdiv, hmod, h109]
theorem sum_fin654_crtPerm654 {α : Type*} [AddCommMonoid α] (f : Fin 654 → α) :
    (∑ m : Fin 654, f (crtPerm654 m)) = ∑ m : Fin 654, f m := Equiv.sum_comp crtPerm654 f
noncomputable def slot0PhaseBit {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (β : BitAssignment (coreWiresSym mPayload)) : ZMod 2 :=
  let g := (basisBitsEquiv (coreWiresSym mPayload)).symm β
  let xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) := (coreSysSym mPayload).extractIndex g
  let c0 := β ⟨SpecsAux.SpecMirror.systemQubits, by dsimp [coreWiresSym, selWiresSym]; omega⟩
  let c1 := β ⟨SpecsAux.SpecMirror.systemQubits + 1, by dsimp [coreWiresSym, selWiresSym]; omega⟩
  let c2 := β ⟨SpecsAux.SpecMirror.systemQubits + 2, by dsimp [coreWiresSym, selWiresSym]; omega⟩
  if c0 = 0 ∧ c1 = 0 ∧ c2 = 1 then
    let u36 : ℕ := ∑ i : Fin 36, (β (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val
    let bPar : ℕ := (β (corePayloadSym mPayload ⟨36, by omega⟩)).val
    let uCmp42 : ℕ :=
      ∑ i : Fin 42, (β (corePayloadSym mPayload ⟨37 + i.val, by omega⟩)).val * 2 ^ i.val
    let bTie : ZMod 2 := β (corePayloadSym mPayload ⟨79, by omega⟩)
    if u36 = 2 ^ 36 - 1 then
      bTie
    else
      let mAx : Fin 654 := crtPerm654 ⟨2 * (u36 % 327) + bPar, by
        have h1 : u36 % 327 < 327 := Nat.mod_lt _ (by omega)
        have h2 : bPar < 2 := ZMod.val_lt _
        omega⟩
      if uCmp42 <
        slot0Thresh w_eff ((TwosCompAndWire0Cancel.elec654Axes mAx).extractIndex xSys) then 1 else 0
  else 0
noncomputable def slot0SelectDiag {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    Operator (2 ^ (coreWiresSym mPayload)) := Matrix.diagonal fun g ↦ ((-1 : ℂ) ^
    (slot0PhaseBit hmPay w_eff (basisBits (coreWiresSym mPayload) g)).val)
noncomputable def bUnitTwosSlot0 (w_eff : ℝ) : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
    Matrix.diagonal fun x ↦ ((((210151305 : ℝ) / (2 : ℝ) ^ 37) * ∑ m : Fin 654, (1 - 2 *
    (slot0Thresh w_eff ((TwosCompAndWire0Cancel.elec654Axes m).extractIndex x) : ℝ) / (2 : ℝ)
    ^ 42) : ℝ) : ℂ)
theorem kappaSqHalf_pos : 0 < (2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2 := by
  have hpi : 0 < 2 * π := by linarith [Real.pi_pos]
  have hvol : 0 < SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ) :=
    lt_of_lt_of_le (by positivity) cellVolume_rpow_third_ge_1342516031
  have hquot : 0 < 2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ) := div_pos hpi hvol
  positivity
theorem elecQuadCenterOffset_pos : 0 < elecQuadCenterOffset := by
  rw [elecQuadCenterOffset_eq]
  exact mul_pos kappaSqHalf_pos (by positivity)
theorem elecQuadCenterOffset_le_34416122_div_1000 :
    elecQuadCenterOffset ≤ 34416122 / 1000 := by
  rw [elecQuadCenterOffset_eq]
  have hkappa : ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) ≤ gridKappaRatHi ^
      2 / 2 := kappaSqHalf_le_ratHi
  have hrat : (gridKappaRatHi ^ 2 / 2) * 314247 ≤ (34416122 / 1000 : ℝ) := by
    unfold gridKappaRatHi
    norm_num
  linarith
theorem elecQuadCenterOffset_lt_lambdaSlot0TeHi : elecQuadCenterOffset < lambdaSlot0TeHi := by
  unfold lambdaSlot0TeHi
  linarith [elecQuadCenterOffset_le_34416122_div_1000]
theorem slot0AxisInt_sq_bounds (u : Fin 64) :
    0 ≤ (slot0AxisInt u : ℝ) ^ 2 ∧ (slot0AxisInt u : ℝ) ^ 2 ≤ 961 := by
  have hu := u.isLt
  have hb : -31 ≤ slot0AxisInt u ∧ slot0AxisInt u ≤ 31 := by
    unfold slot0AxisInt twosComp6Int
    split_ifs <;> omega
  have hloR : (-31 : ℝ) ≤ (slot0AxisInt u : ℝ) := by exact_mod_cast hb.1
  have hhiR : (slot0AxisInt u : ℝ) ≤ 31 := by exact_mod_cast hb.2
  exact ⟨sq_nonneg _, by nlinarith⟩
theorem slot0_scaled_axis_bounds (u : Fin 64) : -elecQuadCenterOffset ≤ 654 *
    ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
    ((slot0AxisInt u : ℝ) ^ 2 - 961 / 2) ∧ 654 *
    ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
    ((slot0AxisInt u : ℝ) ^ 2 - 961 / 2) ≤ elecQuadCenterOffset := by
  obtain ⟨hsq0, hsq961⟩ := slot0AxisInt_sq_bounds u
  have hk0 : 0 ≤ (2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2 :=
    kappaSqHalf_nonneg
  rw [elecQuadCenterOffset_eq]
  constructor <;> nlinarith
noncomputable def slot0ThreshReal (w_eff : ℝ) (u : Fin 64) : ℝ := (2 : ℝ) ^ 41 * (1 - 654 *
    ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) * ((slot0AxisInt u : ℝ) ^ 2 -
    961 / 2) / w_eff)
theorem slot0Thresh_eq_floor (w_eff : ℝ) (u : Fin 64) : slot0Thresh w_eff u = Nat.floor
    (slot0ThreshReal w_eff u) := rfl
theorem slot0ThreshReal_bounds {w_eff : ℝ} (hw : elecQuadCenterOffset ≤ w_eff) (u : Fin 64) :
    0 ≤ slot0ThreshReal w_eff u ∧ slot0ThreshReal w_eff u ≤ (2 : ℝ) ^ 42 := by
  have hw_pos : 0 < w_eff := lt_of_lt_of_le elecQuadCenterOffset_pos hw
  obtain ⟨hlo, hhi⟩ := slot0_scaled_axis_bounds u
  have hdiv_hi : 654 * ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
      ((slot0AxisInt u : ℝ) ^ 2 - 961 / 2) / w_eff ≤ 1 := by
    rw [div_le_one hw_pos]
    linarith
  have hdiv_lo : -1 ≤ 654 * ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
      ((slot0AxisInt u : ℝ) ^ 2 - 961 / 2) / w_eff := by
    rw [le_div_iff₀ hw_pos]
    linarith
  unfold slot0ThreshReal
  have hp41 : (0 : ℝ) < (2 : ℝ) ^ 41 := by norm_num
  have hp42 : (2 : ℝ) ^ 41 * 2 = (2 : ℝ) ^ 42 := by norm_num
  constructor <;> nlinarith
theorem slot0Thresh_le_two_pow_42 {w_eff : ℝ} (hw : elecQuadCenterOffset ≤ w_eff) (u : Fin 64) :
    slot0Thresh w_eff u ≤ 2 ^ 42 := by
  rw [slot0Thresh_eq_floor]
  have hb := (slot0ThreshReal_bounds hw u).2
  exact Nat.floor_le_of_le (by exact_mod_cast hb)
private theorem lemHex33d (k : ℕ) : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  have hsq : (-1 : ℂ) ^ 2 = 1 := by ring
  rw [hsq, one_pow]
private theorem lemHex33e {I : Type*} [Fintype I] [DecidableEq I]
    (f d : I → ℂ) (h : ∀ i, f i * (1 - d i) = 1 - d i) :
    Matrix.diagonal f * (1 - Matrix.diagonal d) = 1 - Matrix.diagonal d := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    linear_combination h i
  · simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero]
theorem slot0SelectDiag_conjTranspose {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (slot0SelectDiag hmPay w_eff)ᴴ = slot0SelectDiag hmPay w_eff := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [slot0SelectDiag, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
      star_pow, star_neg, star_one]
  · simp only [slot0SelectDiag, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij), star_zero]
theorem slot0SelectDiag_mul_self {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    slot0SelectDiag hmPay w_eff * slot0SelectDiag hmPay w_eff = 1 := by
  have hdiag : Matrix.diagonal (fun g : Fin (2 ^ (coreWiresSym mPayload)) ↦ ((-1 : ℂ) ^
      (slot0PhaseBit hmPay w_eff (basisBits (coreWiresSym mPayload) g)).val) * ((-1 : ℂ) ^
      (slot0PhaseBit hmPay w_eff (basisBits (coreWiresSym mPayload) g)).val)) =
      Matrix.diagonal (fun _ ↦ (1 : ℂ)) := congrArg Matrix.diagonal (funext fun _ ↦ lemHex33d _)
  rw [slot0SelectDiag, Matrix.diagonal_mul_diagonal, hdiag, Matrix.diagonal_one]
noncomputable def slot0SelectUnitary {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    Unitary (2 ^ (coreWiresSym mPayload)) :=
  ⟨slot0SelectDiag hmPay w_eff, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, slot0SelectDiag_conjTranspose]
    exact slot0SelectDiag_mul_self hmPay w_eff)⟩
@[simp] theorem slot0SelectUnitary_val {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (slot0SelectUnitary hmPay w_eff).1 = slot0SelectDiag hmPay w_eff := rfl
theorem slot0SelectUnitary_sa {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (slot0SelectUnitary hmPay w_eff).1ᴴ = (slot0SelectUnitary hmPay w_eff).1 :=
  slot0SelectDiag_conjTranspose hmPay w_eff
theorem slot0SelectUnitary_offCoin {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (slot0SelectUnitary hmPay w_eff).1 * (1 - momCoinProj mPayload (fullSysCoinIdx 0)) =
      1 - momCoinProj mPayload (fullSysCoinIdx 0) := by
  have hc4 : fullSysCoinIdx 0 = 4 := rfl
  have hb0 : (coinBitFin2 4 0).val = 0 := rfl
  have hb1 : (coinBitFin2 4 1).val = 0 := rfl
  have hb2 : (coinBitFin2 4 2).val = 1 := rfl
  rw [slot0SelectUnitary_val, hc4, momCoinProj, slotBitProj, slotBitProj, slotBitProj,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, slot0SelectDiag]
  refine lemHex33e _ _ fun g ↦ ?_
  have hlt2 : SpecsAux.SpecMirror.systemQubits + 2 < coreWiresSym mPayload := by
    dsimp [coreWiresSym, selWiresSym]
    omega
  have hw0 : (⟨SpecsAux.SpecMirror.systemQubits, by omega⟩ : Wire (coreWiresSym mPayload)) =
      iSlot0Mom mPayload := Fin.ext rfl
  have hw1 : (⟨SpecsAux.SpecMirror.systemQubits + 1, by omega⟩ : Wire (coreWiresSym mPayload)) =
      iSlot1Mom mPayload := Fin.ext rfl
  have hw2 : (⟨SpecsAux.SpecMirror.systemQubits + 2, hlt2⟩ : Wire (coreWiresSym mPayload)) =
      iSlot2Mom mPayload := Fin.ext rfl
  by_cases hAll :
      basisBits (coreWiresSym mPayload) g (iSlot0Mom mPayload) = 0 ∧
      basisBits (coreWiresSym mPayload) g (iSlot1Mom mPayload) = 0 ∧
      basisBits (coreWiresSym mPayload) g (iSlot2Mom mPayload) = 1
  · obtain ⟨hc0, hc1, hc2⟩ := hAll
    have hv1 : (1 : ZMod 2).val = 1 := rfl
    simp [hb0, hb1, hb2, hc0, hc1, hc2, hv1]
  · have hPhase0 : slot0PhaseBit hmPay w_eff (basisBits (coreWiresSym mPayload) g) = 0 := by
      unfold slot0PhaseBit
      rw [hw0, hw1, hw2, lemHex33a hAll]
    rw [hPhase0]
    simp
theorem embedMatrix_diagonal {k N : ℕ} (r : QRegister k N) (f : Fin (2 ^ k) → ℂ) :
    r.embedMatrix (Matrix.diagonal f) = Matrix.diagonal (fun g ↦ f (r.extractIndex g)) := by
  ext i j
  rw [QRegister.embedMatrix_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    by_cases envEq : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2
    · have hexNe : r.extractIndex i ≠ r.extractIndex j := by
        intro hexEq
        apply hij
        apply r.basisSplitEquiv.injective
        exact Prod.ext hexEq envEq
      rw [Matrix.diagonal_apply_ne _ hexNe, zero_mul]
    · simp [envEq]
private abbrev lemHex33f (mPayload : ℕ) : QRegister 6 (coreWiresSym mPayload) :=
  QRegister.block SpecsAux.SpecMirror.systemQubits 6 (by dsimp [coreWiresSym, selWiresSym]; omega)
private noncomputable def lemHex340 (c : Fin 8) : Fin (2 ^ 6) :=
  (basisBitsEquiv 6).symm (fun i ↦ if h : i.val < 3 then basisBits 3 c ⟨i.val, h⟩ else 0)
private theorem lemHex341 {m : ℕ} (f : Fin m → ZMod 2) (i : Fin m) : basisBits m
    ((basisBitsEquiv m).symm f) i = f i := congrFun ((basisBitsEquiv m).apply_symm_apply f) i
private theorem lemHex342 (mPayload : ℕ) (c : Fin 8) : (coreAncSym mPayload).basisOutcomeProjector
    (coinSelOutcome (selCoin3Sym mPayload) c) = (lemHex33f mPayload).basisOutcomeProjector
    (lemHex340 c) * (corePayloadSym mPayload).basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
  have hCoin (w : Wire (selWiresSym mPayload)) (hw : w.val < 3) :
      basisBits (selWiresSym mPayload) (coinSelOutcome (selCoin3Sym mPayload) c) w =
        basisBits 3 c ⟨w.val, hw⟩ := by
    have heq : w = selCoin3Sym mPayload ⟨w.val, hw⟩ := Fin.ext (by
      dsimp [selCoin3Sym, MomSlots01Slot0ElectronKineticAlt.qreg_block_apply,
        MomSlots01Slot0ElectronKineticAlt.qreg_block_wires_apply,
        MomSlots01Slot0ElectronKineticAlt.qreg_whole_wires,
        MomSlots01Slot0ElectronKineticAlt.emb_trans_apply,
        MomSlots01Slot0ElectronKineticAlt.emb_refl_apply,
        MomSlots01Slot0ElectronKineticAlt.emb_mk_apply]
      omega)
    conv_lhs => rw [heq]
    exact basisBits_coinSelOutcome_coin (selCoin3Sym mPayload) c ⟨w.val, hw⟩
  have hOut (w : Wire (selWiresSym mPayload)) (hw : ¬w.val < 3) :
      basisBits (selWiresSym mPayload) (coinSelOutcome (selCoin3Sym mPayload) c) w = 0 := by
    apply basisBits_coinSelOutcome_outside
    intro hmem
    rcases Finset.mem_map.mp hmem with ⟨r, _, hr⟩
    have hv := congrArg Fin.val hr
    dsimp [selCoin3Sym, MomSlots01Slot0ElectronKineticAlt.qreg_block_apply,
      MomSlots01Slot0ElectronKineticAlt.qreg_block_wires_apply,
      MomSlots01Slot0ElectronKineticAlt.qreg_whole_wires,
      MomSlots01Slot0ElectronKineticAlt.emb_trans_apply,
      MomSlots01Slot0ElectronKineticAlt.emb_refl_apply,
      MomSlots01Slot0ElectronKineticAlt.emb_mk_apply] at hv
    omega
  have hPayBit (j : Fin mPayload) (hj : 6 + j.val < selWiresSym mPayload) :
      basisBits mPayload ((corePayloadSym mPayload).extractIndex g) j =
        basisBits (selWiresSym mPayload) ((coreAncSym mPayload).extractIndex g)
          ⟨6 + j.val, hj⟩ := by
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    refine congrArg (basisBits _ _) (Fin.ext ?_)
    dsimp [corePayloadSym, coreAncSym,
      MomSlots01Slot0ElectronKineticAlt.qreg_block_apply,
      MomSlots01Slot0ElectronKineticAlt.qreg_block_wires_apply,
      MomSlots01Slot0ElectronKineticAlt.qreg_whole_wires,
      MomSlots01Slot0ElectronKineticAlt.emb_trans_apply,
      MomSlots01Slot0ElectronKineticAlt.emb_refl_apply,
      MomSlots01Slot0ElectronKineticAlt.emb_mk_apply]
    omega
  have hiff : (coreAncSym mPayload).extractIndex g = coinSelOutcome (selCoin3Sym mPayload) c ↔
      (lemHex33f mPayload).extractIndex g = lemHex340 c ∧ (corePayloadSym mPayload).extractIndex g =
        0 := by
    refine ⟨fun hAnc ↦ ⟨(basisBitsEquiv 6).injective (funext fun i ↦ ?_),
      (basisBitsEquiv mPayload).injective (funext fun j ↦ ?_)⟩,
      fun ⟨hSix, hPay⟩ ↦ (basisBitsEquiv (selWiresSym mPayload)).injective (funext fun k ↦ ?_)⟩
    · change basisBits 6 ((lemHex33f mPayload).extractIndex g) i = basisBits 6 (lemHex340 c) i
      have hi_lt : i.val < selWiresSym mPayload := by
        dsimp [selWiresSym]
        omega
      have h1 : basisBits 6 ((lemHex33f mPayload).extractIndex g) i =
          basisBits (selWiresSym mPayload) ((coreAncSym mPayload).extractIndex g)
            ⟨i.val, hi_lt⟩ := by
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        rfl
      rw [h1, hAnc, lemHex340, lemHex341]
      by_cases h3 : i.val < 3
      · rw [lemHex33b h3, hCoin ⟨i.val, hi_lt⟩ h3]
      · rw [lemHex33c h3, hOut ⟨i.val, hi_lt⟩ h3]
    · change basisBits mPayload ((corePayloadSym mPayload).extractIndex g) j =
        basisBits mPayload 0 j
      have hj_lt : 6 + j.val < selWiresSym mPayload := by
        dsimp [selWiresSym]
        omega
      have hb0 : basisBits mPayload 0 j = 0 := by simp [-Nat.reducePow, basisBits_eq_div_mod]
      have hj_ge3 : ¬(6 + j.val < 3) := by omega
      rw [hPayBit j hj_lt, hAnc, hb0, hOut ⟨6 + j.val, hj_lt⟩ hj_ge3]
    · change basisBits (selWiresSym mPayload) ((coreAncSym mPayload).extractIndex g) k =
        basisBits (selWiresSym mPayload) (coinSelOutcome (selCoin3Sym mPayload) c) k
      by_cases hk6 : k.val < 6
      · have h1 : basisBits (selWiresSym mPayload) ((coreAncSym mPayload).extractIndex g) k =
            basisBits 6 ((lemHex33f mPayload).extractIndex g) ⟨k.val, hk6⟩ := by
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
          rfl
        rw [h1, hSix, lemHex340, lemHex341]
        dsimp only
        by_cases hk3 : k.val < 3
        · rw [lemHex33b hk3, hCoin k hk3]
        · rw [lemHex33c hk3, hOut k hk3]
      · have hk_lt : k.val < 6 + mPayload := k.isLt
        let j : Fin mPayload := ⟨k.val - 6, by omega⟩
        have hj_lt : 6 + j.val < selWiresSym mPayload := by
          dsimp [selWiresSym, j]
          omega
        have hk_eq : k = ⟨6 + j.val, hj_lt⟩ := Fin.ext (Nat.add_sub_cancel' (by omega)).symm
        have hb0 : basisBits mPayload 0 j = 0 := by simp [-Nat.reducePow, basisBits_eq_div_mod]
        have hj_ge3 : ¬(6 + j.val < 3) := by omega
        rw [hk_eq, ← hPayBit j hj_lt, hPay, hb0, hOut ⟨6 + j.val, hj_lt⟩ hj_ge3]
  by_cases hA : (coreAncSym mPayload).extractIndex g = coinSelOutcome (selCoin3Sym mPayload) c
  · obtain ⟨h1, h2⟩ := hiff.mp hA
    simp [hA, h1, h2]
  · by_cases h1 : (lemHex33f mPayload).extractIndex g = lemHex340 c
    · have h2 : (corePayloadSym mPayload).extractIndex g ≠ 0 := fun h2 ↦ hA (hiff.mpr ⟨h1, h2⟩)
      simp [hA, h1, h2]
    · simp [hA, h1]
private noncomputable def lemHex343 {a b R K mPayload : ℕ} (hmPay : a + 1 + b + 1 ≤ mPayload)
    (hR : 0 < R) (hRK : 2 * R = K) (thresh : Fin K → ℕ) (u : Fin (2 ^ mPayload)) : ℂ :=
  let γ := basisBits mPayload u
  let ua : ℕ := ∑ i : Fin a, (γ ⟨i.val, by have := i.isLt; omega⟩).val * 2 ^ i.val
  let bPar : ℕ := (γ ⟨a, by omega⟩).val
  let uCmp : ℕ := ∑ i : Fin b, (γ ⟨a + 1 + i.val, by have := i.isLt; omega⟩).val * 2 ^ i.val
  let bTie : ZMod 2 := γ ⟨a + 1 + b, by omega⟩
  if ua = 2 ^ a - 1 then
    (-1 : ℂ) ^ bTie.val
  else
    let mAx : Fin K := ⟨2 * (ua % R) + bPar, by
      have h1 : ua % R < R := Nat.mod_lt _ hR
      have h2 : bPar < 2 := ZMod.val_lt _
      omega⟩
    if uCmp < thresh mAx then
      (-1 : ℂ)
    else 1
private noncomputable def lemHex344 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (c : Fin 8) (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (u : Fin (2 ^ mPayload)) : ℂ :=
  if c = 4 then
    lemHex343 (a := 36) (b := 42) (R := 327) (K := 654)
      hmPay (by omega) (by omega)
      (fun mAx ↦
        slot0Thresh w_eff ((TwosCompAndWire0Cancel.elec654Axes (crtPerm654 mAx)).extractIndex xSys))
        u
  else 1
private theorem lemHex345 (c : Fin 8) :
    (basisBits 3 c 0 = 0 ∧ basisBits 3 c 1 = 0 ∧ basisBits 3 c 2 = 1) ↔ c = 4 := by
  fin_cases c <;> decide
private theorem lemHex346 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) (c : Fin 8) :
    (lemHex33f mPayload).basisOutcomeProjector (lemHex340 c) * slot0SelectDiag hmPay w_eff =
      ∑ u : Fin
    (2 ^ mPayload), (corePayloadSym mPayload).basisOutcomeProjector u *
    (lemHex33f mPayload).basisOutcomeProjector (lemHex340 c) * (coreSysSym mPayload).embedMatrix
    (Matrix.diagonal (fun xSys ↦ lemHex344 hmPay w_eff c xSys u)) := by
  simp_rw [fun u ↦ embedMatrix_diagonal (coreSysSym mPayload)
      (fun xSys ↦ lemHex344 hmPay w_eff c xSys u),
    QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  rw [slot0SelectDiag, Matrix.diagonal_mul_diagonal]
  ext g₁ g₂
  by_cases hg : g₁ = g₂
  · subst hg
    simp only [Matrix.diagonal_apply_eq, Matrix.sum_apply]
    let u₀ : Fin (2 ^ mPayload) := (corePayloadSym mPayload).extractIndex g₁
    rw [Finset.sum_eq_single u₀ (fun u _ hu ↦ by simp [u₀, Ne.symm hu])
      (fun h ↦ (h (Finset.mem_univ u₀)).elim)]
    simp only [u₀, ↓reduceIte, one_mul]
    by_cases hSix : (lemHex33f mPayload).extractIndex g₁ = lemHex340 c
    · simp only [hSix, ↓reduceIte, one_mul]
      have hlt2 : SpecsAux.SpecMirror.systemQubits + 2 < coreWiresSym mPayload := by
        dsimp [coreWiresSym, selWiresSym]
        omega
      have hc_bit (i : Fin 3) (w : Wire (coreWiresSym mPayload))
          (hw : w.val = SpecsAux.SpecMirror.systemQubits + i.val) :
          basisBits (coreWiresSym mPayload) g₁ w = basisBits 3 c i := by
        have hi6 : i.val < 6 := by omega
        have hwi : (lemHex33f mPayload) ⟨i.val, hi6⟩ = w := Fin.ext (by
          rw [hw]
          dsimp [lemHex33f, MomSlots01Slot0ElectronKineticAlt.qreg_block_apply,
            MomSlots01Slot0ElectronKineticAlt.qreg_block_wires_apply,
            MomSlots01Slot0ElectronKineticAlt.qreg_whole_wires,
            MomSlots01Slot0ElectronKineticAlt.emb_trans_apply,
            MomSlots01Slot0ElectronKineticAlt.emb_refl_apply,
            MomSlots01Slot0ElectronKineticAlt.emb_mk_apply])
        have hb := ((lemHex33f mPayload).basisBits_extractIndex g₁ ⟨i.val, hi6⟩).symm
        rw [hSix, hwi, lemHex340, lemHex341, lemHex33b i.isLt] at hb
        exact hb
      have hpay (k : Fin mPayload) :
          basisBits (coreWiresSym mPayload) g₁ (corePayloadSym mPayload k) =
            basisBits mPayload u₀ k :=
        ((corePayloadSym mPayload).basisBits_extractIndex g₁ k).symm
      have hv0 : (0 : ZMod 2).val = 0 := rfl
      have hv1 : (1 : ZMod 2).val = 1 := rfl
      unfold slot0PhaseBit lemHex344 lemHex343
      rw [hc_bit 0 ⟨SpecsAux.SpecMirror.systemQubits, by omega⟩ (Nat.add_zero _).symm,
        hc_bit 1 ⟨SpecsAux.SpecMirror.systemQubits + 1, by omega⟩ rfl,
        hc_bit 2 ⟨SpecsAux.SpecMirror.systemQubits + 2, hlt2⟩ rfl,
        (basisBitsEquiv (coreWiresSym mPayload)).symm_apply_apply g₁]
      by_cases hc4 : c = 4
      · rw [lemHex339 hc4, lemHex339 ((lemHex345 c).mpr hc4)]
        dsimp only
        have hua : (∑ i : Fin 36,
            (basisBits mPayload u₀ ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩).val * 2 ^ i.val) =
            ∑ i : Fin 36, (basisBits (coreWiresSym mPayload) g₁
              (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val :=
          Finset.sum_congr rfl fun i _ ↦ by rw [hpay]
        have hbP : (basisBits mPayload u₀ ⟨36, by omega⟩).val =
            (basisBits (coreWiresSym mPayload) g₁ (corePayloadSym mPayload ⟨36, by omega⟩)).val :=
          congrArg ZMod.val (hpay ⟨36, by omega⟩).symm
        have huC : (∑ i : Fin 42,
            (basisBits mPayload u₀
              ⟨36 + 1 + i.val, lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (by omega)⟩).val *
                2 ^ i.val) =
            ∑ i : Fin 42, (basisBits (coreWiresSym mPayload) g₁
              (corePayloadSym mPayload ⟨37 + i.val, by omega⟩)).val * 2 ^ i.val :=
          Finset.sum_congr rfl fun i _ ↦
            congrArg (· * 2 ^ i.val) (congrArg ZMod.val (hpay ⟨37 + i.val, by omega⟩).symm)
        have hbT : basisBits mPayload u₀ ⟨36 + 1 + 42, by omega⟩ =
            basisBits (coreWiresSym mPayload) g₁ (corePayloadSym mPayload ⟨79, by omega⟩) :=
          (hpay ⟨79, by omega⟩).symm
        by_cases hmax : (∑ i : Fin 36,
            (basisBits mPayload u₀ ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩).val * 2 ^ i.val) =
            2 ^ 36 - 1
        · rw [lemHex339 hmax, lemHex339 (hua.symm.trans hmax), hbT]
        · rw [lemHex33a hmax, lemHex33a (fun h ↦ hmax (hua.trans h))]
          let remL := (∑ i : Fin 36,
              (basisBits mPayload u₀ ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩).val *
                2 ^ i.val) % 327
          let parL := (basisBits mPayload u₀ ⟨36, by omega⟩).val
          let mAxL : Fin 654 := ⟨2 * remL + parL,
            by have := Nat.mod_lt (∑ i : Fin 36,
                (basisBits mPayload u₀ ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩).val * 2 ^ i.val)
                (by omega : 0 < 327)
               have := ZMod.val_lt (basisBits mPayload u₀ ⟨36, by omega⟩)
               omega⟩
          let remR := (∑ i : Fin 36, (basisBits (coreWiresSym mPayload) g₁
              (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val) % 327
          let parR := (basisBits (coreWiresSym mPayload) g₁
              (corePayloadSym mPayload ⟨36, by omega⟩)).val
          let mAxR : Fin 654 := ⟨2 * remR + parR,
            by have := Nat.mod_lt (∑ i : Fin 36, (basisBits (coreWiresSym mPayload) g₁
                (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val) (by omega : 0 < 327)
               have := ZMod.val_lt (basisBits (coreWiresSym mPayload) g₁
                (corePayloadSym mPayload ⟨36, by omega⟩))
               omega⟩
          have hmAx : mAxL = mAxR := Fin.ext (by
            dsimp [mAxL, mAxR, remL, parL, remR, parR]
            rw [hua, hbP])
          change (-1 : ℂ) ^ (if (∑ i : Fin 42, (basisBits (coreWiresSym mPayload) g₁
              (corePayloadSym mPayload ⟨37 + i.val, _⟩)).val * 2 ^ i.val) <
              slot0Thresh w_eff ((TwosCompAndWire0Cancel.elec654Axes (crtPerm654 mAxR)).extractIndex
                ((coreSysSym mPayload).extractIndex g₁)) then (1 : ZMod 2) else 0).val =
            (if (∑ i : Fin 42, (basisBits mPayload u₀ ⟨36 + 1 + i.val, _⟩).val * 2 ^ i.val) <
              slot0Thresh w_eff ((TwosCompAndWire0Cancel.elec654Axes (crtPerm654 mAxL)).extractIndex
                ((coreSysSym mPayload).extractIndex g₁)) then (-1 : ℂ) else 1)
          rw [huC, hmAx]
          split_ifs
          · rw [hv1]
            ring
          · rw [hv0]
            ring
      · rw [lemHex33a hc4, lemHex33a (fun hh ↦ hc4 ((lemHex345 c).mp hh)), hv0]
        ring
    · simp [hSix]
  · simp only [Matrix.diagonal_apply_ne _ hg, Matrix.sum_apply, Finset.sum_const_zero]
private theorem lemHex347 {N T : ℕ} (hT : T ≤ N) :
    ((Finset.univ : Finset (Fin N)).filter (fun v ↦ v.val < T)).card = T := by
  let emb : Fin T ↪ Fin N := ⟨fun i ↦ ⟨i.val, lt_of_lt_of_le i.isLt hT⟩,
    fun a b (h : (⟨a.val, _⟩ : Fin N) = ⟨b.val, _⟩) ↦
      Fin.ext (congrArg (Fin.val : Fin N → ℕ) h)⟩
  have hmap : Finset.map emb Finset.univ =
      (Finset.univ : Finset (Fin N)).filter (fun v ↦ v.val < T) := by
    ext v
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, emb]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ i.isLt, fun hv ↦ ⟨⟨v.val, hv⟩, rfl⟩⟩
  rw [← hmap, Finset.card_map, Finset.card_fin]
private theorem lemHex348 {N T : ℕ} (hT : T ≤ N) :
    (∑ v : Fin N, (if v.val < T then (-1 : ℂ) else 1)) = (N : ℂ) - 2 * (T : ℂ) := by
  have hpt (v : Fin N) : (if v.val < T then (-1 : ℂ) else 1) =
      1 - 2 * (if v.val < T then (1 : ℂ) else 0) := by
    split_ifs <;> norm_num
  simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.sum_const,
    Finset.card_fin, lemHex347 hT, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]
private def lemHex349 {N M Q R : ℕ} (hR : 0 < R) (hQR : R * Q = M) (hMN : M ≤ N) :
    Fin Q × Fin R ≃ {u : Fin N // u.val < M} where
  toFun qr :=
    have hmul : R * qr.1.val + R ≤ M := by
      rw [← hQR]
      simpa [mul_add, mul_one] using Nat.mul_le_mul_left R (Nat.succ_le_of_lt qr.1.isLt)
    have hr : qr.2.val < R := qr.2.isLt
    have hlt_M : R * qr.1.val + qr.2.val < M := by omega
    ⟨⟨R * qr.1.val + qr.2.val, lt_of_lt_of_le hlt_M hMN⟩, hlt_M⟩
  invFun u :=
    have hlt_mul : R * (u.1.val / R) < R * Q := by
      have hdm := Nat.div_add_mod u.1.val R
      have hu := u.2
      omega
    (⟨u.1.val / R, Nat.lt_of_mul_lt_mul_left hlt_mul⟩,
     ⟨u.1.val % R, Nat.mod_lt _ hR⟩)
  left_inv qr := by
    obtain ⟨q, r⟩ := qr
    have hval : R * q.val + r.val = r.val + R * q.val := add_comm _ _
    ext
    · dsimp
      rw [hval, Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt r.isLt, zero_add]
    · dsimp
      rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  right_inv u := by
    ext
    dsimp
    exact Nat.div_add_mod u.1.val R
private def lemHex34a {R K : ℕ} (hRK : 2 * R = K) : Fin R × Fin 2 ≃ Fin K where
  toFun jp := ⟨2 * jp.1.val + jp.2.val, by
    have hj := jp.1.isLt
    have hp := jp.2.isLt
    omega⟩
  invFun m := (⟨m.val / 2, by have hm := m.isLt; omega⟩,⟨m.val % 2, Nat.mod_lt _ (by omega)⟩)
  left_inv jp := by
    obtain ⟨j, p⟩ := jp
    have hval : 2 * j.val + p.val = p.val + 2 * j.val := add_comm _ _
    ext
    · dsimp
      rw [hval, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt p.isLt, zero_add]
    · dsimp
      rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.isLt]
  right_inv m := by
    ext
    dsimp
    exact Nat.div_add_mod m.val 2
private noncomputable def lemHex34b {a b mPayload : ℕ} (hmPay : a + 1 + b + 1 ≤ mPayload) : Fin
    (2 ^ mPayload) ≃ Fin (2 ^ a) × Fin 2 × Fin (2 ^ b) × ZMod 2 × BitAssignment
    (mPayload - (a + 1 + b + 1)) :=
  (basisBitsEquiv mPayload).trans
  { toFun := fun γ ↦
      ((basisBitsEquiv a).symm (fun i ↦ γ ⟨i.val, by have := i.isLt; omega⟩),
       ⟨(γ ⟨a, by omega⟩).val, ZMod.val_lt _⟩,
       (basisBitsEquiv b).symm (fun i ↦ γ ⟨a + 1 + i.val, by have := i.isLt; omega⟩),
       γ ⟨a + 1 + b, by omega⟩,
       fun j ↦ γ ⟨a + 1 + b + 1 + j.val, by have := j.isLt; omega⟩)
    invFun := fun t idx ↦
      if ha : idx.val < a then
        basisBits a t.1 ⟨idx.val, ha⟩
      else if ha2 : idx.val = a then
        (t.2.1.val : ZMod 2)
      else if hb : idx.val < a + 1 + b then
        basisBits b t.2.2.1 ⟨idx.val - (a + 1), by omega⟩
      else if hb2 : idx.val = a + 1 + b then
        t.2.2.2.1
      else
        t.2.2.2.2 ⟨idx.val - (a + 1 + b + 1), by have := idx.isLt; omega⟩
    left_inv := fun γ ↦ by
      funext idx
      dsimp only
      by_cases h1 : idx.val < a
      · rw [lemHex33b h1, lemHex341]
      · by_cases h2 : idx.val = a
        · rw [lemHex33c h1, lemHex33b h2, ZMod.natCast_zmod_val]
          exact congrArg γ (Fin.ext h2.symm)
        · by_cases h3 : idx.val < a + 1 + b
          · rw [lemHex33c h1, lemHex33c h2, lemHex33b h3, lemHex341]
            exact congrArg γ (Fin.ext (Nat.add_sub_cancel' (by omega)))
          · by_cases h4 : idx.val = a + 1 + b
            · rw [lemHex33c h1, lemHex33c h2, lemHex33c h3, lemHex33b h4]
              exact congrArg γ (Fin.ext h4.symm)
            · rw [lemHex33c h1, lemHex33c h2, lemHex33c h3, lemHex33c h4]
              exact congrArg γ (Fin.ext (Nat.add_sub_cancel' (by omega)))
    right_inv := fun ⟨u, bP, v, bT, rest⟩ ↦ by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
      · dsimp only
        apply (basisBitsEquiv a).injective
        rw [(basisBitsEquiv a).apply_symm_apply]
        funext i
        rw [lemHex33b i.isLt]
        -- ef789d10_rfl
      · ext
        dsimp only
        rw [lemHex33c (by omega : ¬(a < a)), lemHex33b rfl, ZMod.val_natCast]
        exact Nat.mod_eq_of_lt bP.isLt
      · dsimp only
        apply (basisBitsEquiv b).injective
        rw [(basisBitsEquiv b).apply_symm_apply]
        funext i
        rw [lemHex33c (by omega : ¬(a + 1 + i.val < a)), lemHex33c (by omega : a + 1 + i.val ≠ a),
          lemHex33b (Nat.add_lt_add_left i.isLt (a + 1))]
        exact congrArg (basisBits b v) (Fin.ext (Nat.add_sub_cancel_left (a + 1) i.val))
      · dsimp only
        rw [lemHex33c (by omega : ¬(a + 1 + b < a)), lemHex33c (by omega : a + 1 + b ≠ a),
          lemHex33c (by omega : ¬(a + 1 + b < a + 1 + b)), lemHex33b rfl]
      · funext j
        dsimp only
        rw [lemHex33c (by omega : ¬(a + 1 + b + 1 + j.val < a)),
          lemHex33c (by omega : a + 1 + b + 1 + j.val ≠ a),
          lemHex33c (by omega : ¬(a + 1 + b + 1 + j.val < a + 1 + b)),
          lemHex33c (by omega : a + 1 + b + 1 + j.val ≠ a + 1 + b)]
        exact congrArg rest (Fin.ext (Nat.add_sub_cancel_left (a + 1 + b + 1) j.val)) }
private theorem lemHex34c {a b Q R K mPayload : ℕ} (hmPay : a + 1 + b + 1 ≤ mPayload) (hR : 0 < R)
    (hQR : R * Q = 2 ^ a - 1) (hRK : 2 * R = K) (thresh : Fin K → ℕ)
    (hThresh : ∀ m : Fin K, thresh m ≤ 2 ^ b) : ((2 : ℂ)⁻¹ ^ mPayload) *
    (∑ u : Fin (2 ^ mPayload), lemHex343 hmPay hR hRK thresh u) = ((2 : ℂ)⁻¹ ^ (a + 1 + b + 1)) *
    ((Q : ℂ) * ∑ m : Fin K, (2 : ℂ) * (((2 ^ b : ℕ) : ℂ) - 2 * (thresh m : ℂ))) := by
  let d := mPayload - (a + 1 + b + 1)
  have hcard_rest : Fintype.card (BitAssignment d) = 2 ^ d := by simp [BitAssignment]
  have hpow_cancel : ((2 : ℂ)⁻¹ ^ mPayload) * ((2 ^ d : ℕ) : ℂ) = (2 : ℂ)⁻¹ ^ (a + 1 + b + 1) := by
    have hm : mPayload = (a + 1 + b + 1) + d := (Nat.add_sub_cancel' hmPay).symm
    have hd1 : ((2 : ℂ)⁻¹ ^ d) * ((2 ^ d : ℕ) : ℂ) = 1 := by
      push_cast
      rw [inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
    rw [hm, pow_add, mul_assoc, hd1, mul_one]
  rw [← Equiv.sum_comp (lemHex34b hmPay).symm (fun u ↦ lemHex343 hmPay hR hRK thresh u)]
  have hbody (t : Fin (2 ^ a) × Fin 2 × Fin (2 ^ b) × ZMod 2 × BitAssignment d) :
      lemHex343 hmPay hR hRK thresh ((lemHex34b hmPay).symm t) =
        if t.1.val = 2 ^ a - 1 then (-1 : ℂ) ^ t.2.2.2.1.val
        else
          let mAx : Fin K := lemHex34a hRK (⟨t.1.val % R, Nat.mod_lt _ hR⟩, t.2.1)
          if t.2.2.1.val < thresh mAx then (-1 : ℂ) else 1 := by
    rcases t with ⟨u, bP, v, bT, rest⟩
    have ht := (lemHex34b hmPay).apply_symm_apply (u, bP, v, bT, rest)
    have h1 : (∑ i : Fin a, (basisBits mPayload ((lemHex34b hmPay).symm (u, bP, v, bT, rest))
        ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩).val * 2 ^ i.val) = u.val := by
      rw [← bitsVal_basisBits u]
      refine Finset.sum_congr rfl fun i _ ↦ congrArg (· * 2 ^ i.val) (congrArg ZMod.val ?_)
      exact (lemHex341 _ i).symm.trans (congrFun (congrArg (basisBits a) (congrArg Prod.fst ht)) i)
    have h2 : (basisBits mPayload ((lemHex34b hmPay).symm (u, bP, v, bT, rest)) ⟨a, by omega⟩).val =
        bP.val := congrArg (fun p ↦ p.2.1.val) ht
    have h3 : (∑ i : Fin b, (basisBits mPayload ((lemHex34b hmPay).symm (u, bP, v, bT, rest))
        ⟨a + 1 + i.val, lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (by omega)⟩).val *
          2 ^ i.val) = v.val := by
      rw [← bitsVal_basisBits v]
      refine Finset.sum_congr rfl fun i _ ↦ congrArg (· * 2 ^ i.val) (congrArg ZMod.val ?_)
      exact (lemHex341 _ i).symm.trans
        (congrFun (congrArg (basisBits b) (congrArg (fun p ↦ p.2.2.1) ht)) i)
    have h4 : basisBits mPayload ((lemHex34b hmPay).symm (u, bP, v, bT, rest)) ⟨a + 1 + b,
      by omega⟩ =
        bT := congrArg (fun p ↦ p.2.2.2.1) ht
    unfold lemHex343
    dsimp only
    have hmAx : (⟨2 * ((∑ i : Fin a,
        (basisBits mPayload ((lemHex34b hmPay).symm (u, bP, v, bT, rest))
          ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩).val * 2 ^ i.val) % R) +
        (basisBits mPayload ((lemHex34b hmPay).symm (u, bP, v, bT, rest)) ⟨a, by omega⟩).val,
        by
          have := Nat.mod_lt (∑ i : Fin a,
            (basisBits mPayload ((lemHex34b hmPay).symm (u, bP, v, bT, rest))
              ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩).val * 2 ^ i.val) hR
          have := ZMod.val_lt
            (basisBits mPayload ((lemHex34b hmPay).symm (u, bP, v, bT, rest)) ⟨a, by omega⟩)
          omega⟩ : Fin K) = lemHex34a hRK (⟨u.val % R, Nat.mod_lt _ hR⟩, bP) := Fin.ext (by
      dsimp [lemHex34a]
      rw [h1, h2])
    rw [hmAx, h1, h3, h4]
  have htie_cancel : (∑ bT : ZMod 2, (-1 : ℂ) ^ bT.val) = 0 := by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide),
      ZMod.val_zero, ZMod.val_one]
    norm_num
  have htie_two (z : ℂ) : (∑ _bT : ZMod 2, z) = 2 * z := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    norm_num
  simp only [hbody, Fintype.sum_prod_type]
  trans (((2 : ℂ)⁻¹ ^ mPayload) * (((2 ^ d : ℕ) : ℂ) *
      ∑ u : Fin (2 ^ a), ∑ bP : Fin 2, ∑ v : Fin (2 ^ b), ∑ bT : ZMod 2,
        if u.val = 2 ^ a - 1 then (-1 : ℂ) ^ bT.val
        else
          let mAx : Fin K := lemHex34a hRK (⟨u.val % R, Nat.mod_lt _ hR⟩, bP)
          if v.val < thresh mAx then (-1 : ℂ) else 1))
  · congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun bP _ ↦
      Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun bT _ ↦ ?_
    trans (∑ _r : BitAssignment d,
        if u.val = 2 ^ a - 1 then (-1 : ℂ) ^ bT.val
        else
          let mAx : Fin K := lemHex34a hRK (⟨u.val % R, Nat.mod_lt _ hR⟩, bP)
          if v.val < thresh mAx then (-1 : ℂ) else 1)
    · exact Finset.sum_congr rfl fun _ _ ↦ rfl
    · rw [Finset.sum_const, Finset.card_univ, hcard_rest, nsmul_eq_mul]
  rw [← mul_assoc, hpow_cancel]
  have hu_eval (u : Fin (2 ^ a)) :
      (∑ bP : Fin 2, ∑ v : Fin (2 ^ b), ∑ bT : ZMod 2,
        if u.val = 2 ^ a - 1 then (-1 : ℂ) ^ bT.val
        else
          let mAx : Fin K := lemHex34a hRK (⟨u.val % R, Nat.mod_lt _ hR⟩, bP)
          if v.val < thresh mAx then (-1 : ℂ) else 1) =
      if u.val = 2 ^ a - 1 then 0
      else ∑ bP : Fin 2,
        let mAx : Fin K := lemHex34a hRK (⟨u.val % R, Nat.mod_lt _ hR⟩, bP)
        (2 : ℂ) * (((2 ^ b : ℕ) : ℂ) - 2 * (thresh mAx : ℂ)) := by
    by_cases huMax : u.val = 2 ^ a - 1
    · simp_rw [lemHex339 huMax, htie_cancel, Finset.sum_const_zero]
    · simp_rw [lemHex33a huMax, htie_two, ← Finset.mul_sum]
      exact congrArg ((2 : ℂ) * ·) (Finset.sum_congr rfl fun bP _ ↦ lemHex348 (hThresh _))
  simp_rw [hu_eval]
  let fPair : Fin R → ℂ := fun j ↦ ∑ bP : Fin 2,
    let mAx : Fin K := lemHex34a hRK (j, bP)
    (2 : ℂ) * (((2 ^ b : ℕ) : ℂ) - 2 * (thresh mAx : ℂ))
  have hsub : (∑ u : Fin (2 ^ a),
      if u.val = 2 ^ a - 1 then (0 : ℂ) else fPair ⟨u.val % R, Nat.mod_lt _ hR⟩) =
      ∑ u : {u : Fin (2 ^ a) // u.val < 2 ^ a - 1}, fPair ⟨u.1.val % R, Nat.mod_lt _ hR⟩ := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    refine (Finset.sum_congr ?_ fun _ _ ↦ rfl).trans
      (Finset.sum_subtype (Finset.univ.filter fun u : Fin (2 ^ a) ↦ u.val < 2 ^ a - 1)
        (fun _ ↦ by simp) _)
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := u.isLt
    omega
  have hMN : 2 ^ a - 1 ≤ 2 ^ a := Nat.sub_le _ _
  rw [hsub, ← Equiv.sum_comp (lemHex349 hR hQR hMN)]
  have hmod_qr : ∀ qr : Fin Q × Fin R,
      (⟨(lemHex349 hR hQR hMN qr).1.val % R, Nat.mod_lt _ hR⟩ : Fin R) = qr.2 := by
    rintro ⟨q, j⟩
    ext
    dsimp [lemHex349]
    have hv : R * q.val + j.val = j.val + R * q.val := add_comm _ _
    rw [hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  simp_rw [hmod_qr]
  rw [Fintype.sum_prod_type]
  have hconst_q : (∑ _q : Fin Q, ∑ j : Fin R, fPair j) = (Q : ℂ) * ∑ j : Fin R, fPair j := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [hconst_q]
  have hpairK : (∑ j : Fin R, fPair j) = ∑ m : Fin K, (2 : ℂ) *
      (((2 ^ b : ℕ) : ℂ) - 2 * (thresh m : ℂ)) := (Fintype.sum_prod_type (fun p : Fin R × Fin
      2 ↦ (2 : ℂ) * (((2 ^ b : ℕ) : ℂ) - 2 * (thresh (lemHex34a hRK p) : ℂ)))).symm.trans
      (Equiv.sum_comp (lemHex34a hRK) (fun m ↦ (2 : ℂ) * (((2 ^ b : ℕ) : ℂ) - 2 * (thresh m :
      ℂ))))
  rw [hpairK]
private theorem lemHex34d {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {w_eff : ℝ} (hw : elecQuadCenterOffset ≤ w_eff)
    (c : Fin 8) (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    ((2 : ℂ)⁻¹ ^ mPayload) * (∑ u : Fin (2 ^ mPayload), lemHex344 hmPay w_eff c xSys u) =
      if c = 4 then bUnitTwosSlot0 w_eff xSys xSys else 1 := by
  by_cases hc4 : c = 4
  · subst hc4
    rw [lemHex339 rfl]
    have heq4 : ∀ u : Fin (2 ^ mPayload),
        lemHex344 hmPay w_eff 4 xSys u =
          lemHex343 (a := 36) (b := 42) (R := 327) (K := 654)
            hmPay (by omega) (by omega)
            (fun mAx ↦
              slot0Thresh w_eff ((TwosCompAndWire0Cancel.elec654Axes (crtPerm654 mAx)).extractIndex
              xSys)) u :=
      fun u ↦ by unfold lemHex344; exact lemHex339 rfl
    simp_rw [heq4]
    rw [lemHex34c (a := 36) (b := 42) (Q := 210151305) (R := 327) (K := 654)
      hmPay (by omega) (by omega) (by omega)
      (fun mAx ↦
        slot0Thresh w_eff ((TwosCompAndWire0Cancel.elec654Axes (crtPerm654 mAx)).extractIndex xSys))
      (fun mAx ↦ slot0Thresh_le_two_pow_42 hw _)]
    rw [sum_fin654_crtPerm654 (fun m ↦
      (2 : ℂ) * (((2 ^ 42 : ℕ) : ℂ) - 2 *
        (slot0Thresh w_eff ((TwosCompAndWire0Cancel.elec654Axes m).extractIndex xSys) : ℂ)))]
    simp only [bUnitTwosSlot0, Matrix.diagonal_apply_eq]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [inv_pow]
    field_simp
    ring
  · rw [lemHex33a hc4]
    have h1 : ∀ u : Fin (2 ^ mPayload), lemHex344 hmPay w_eff c xSys u = 1 := fun u ↦ by
      unfold lemHex344
      exact lemHex33a hc4
    simp_rw [h1]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]
theorem slot0_hadamard_topBlock_all {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {w_eff : ℝ} (hw : elecQuadCenterOffset ≤ w_eff) (c : Fin 8) :
    let B_c : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
      if c = 4 then bUnitTwosSlot0 w_eff else 1
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) *
      (unitaryConj (coreHadamardUnitary mPayload) (slot0SelectUnitary hmPay w_eff)).1 *
      (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) =
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) *
      (coreSysSym mPayload).embedMatrix B_c *
      (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) := by
  intro B_c
  let sys := coreSysSym mPayload
  let six := lemHex33f mPayload
  let pay := corePayloadSym mPayload
  let H := (hadamardAll pay).eval
  let R_c := six.basisOutcomeProjector (lemHex340 c)
  let P_0 := pay.basisOutcomeProjector 0
  have hDisj_pay_six : pay.DisjointWires six :=
    QRegister.disjoint_comm.mp <|
      QRegister.block_disjoint_of_le SpecsAux.SpecMirror.systemQubits 6
        (SpecsAux.SpecMirror.systemQubits + 6) mPayload
        (by dsimp [coreWiresSym, selWiresSym]; omega)
        (by dsimp [coreWiresSym, selWiresSym]; omega)
        le_rfl
  have hDisj_pay_sys : pay.DisjointWires sys :=
    QRegister.disjoint_comm.mp <|
      QRegister.block_disjoint_of_le 0 SpecsAux.SpecMirror.systemQubits
        (SpecsAux.SpecMirror.systemQubits + 6) mPayload
        (by dsimp [coreWiresSym]; omega)
        (by dsimp [coreWiresSym, selWiresSym]; omega)
        (by omega)
  have hH_sa : H.1ᴴ = H.1 := FullSysPrepare6Slot.hadamardAll_eval_self_adj pay
  have hH_Rc : H.1 * R_c = R_c * H.1 := by
    dsimp only [H, R_c, QRegister.basisOutcomeProjector]
    simpa only [hadamardAll_embed_eq_local pay, QRegister.embedUnitary_val] using
      pay.embedMatrix_comm_of_disjoint six hDisj_pay_six (hadamardPayloadUnitary mPayload).1
        (compProj (lemHex340 c))
  have hH_sys : ∀ M : Operator (2 ^ SpecsAux.SpecMirror.systemQubits),
      H.1 * sys.embedMatrix M = sys.embedMatrix M * H.1 := fun M ↦ by
    dsimp only [H]
    simpa only [hadamardAll_embed_eq_local pay, QRegister.embedUnitary_val] using
      pay.embedMatrix_comm_of_disjoint sys hDisj_pay_sys (hadamardPayloadUnitary mPayload).1 M
  have hP_Rc : ∀ v : Fin (2 ^ mPayload),
      pay.basisOutcomeProjector v * R_c = R_c * pay.basisOutcomeProjector v := fun v ↦ by
    simp only [R_c, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal,
      mul_comm]
  have hP0_sys : ∀ M : Operator (2 ^ SpecsAux.SpecMirror.systemQubits),
      P_0 * sys.embedMatrix M = sys.embedMatrix M * P_0 :=
    fun M ↦
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint sys pay hDisj_pay_sys.symm M
      0).symm
  have hRc_idem : R_c * R_c = R_c := by
    simp only [R_c, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
    split_ifs <;> simp
  have hP0_idem : P_0 * P_0 = P_0 := by
    simp only [P_0, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
    split_ifs <;> simp
  have hP0_Rc : P_0 * R_c = R_c * P_0 := hP_Rc 0
  rw [lemHex342 mPayload c]
  change (R_c * P_0) * (H.1ᴴ * slot0SelectDiag hmPay w_eff * H.1) * (R_c * P_0) =
    (R_c * P_0) * sys.embedMatrix B_c * (R_c * P_0)
  have hLHS1 : (R_c * P_0) * (H.1ᴴ * slot0SelectDiag hmPay w_eff * H.1) * (R_c * P_0) =
      P_0 * H.1ᴴ * (R_c * slot0SelectDiag hmPay w_eff) * H.1 * P_0 * R_c := by
    have hdiag_comm : R_c * slot0SelectDiag hmPay w_eff * R_c =
        R_c * slot0SelectDiag hmPay w_eff := by
      rw [Matrix.mul_assoc, show slot0SelectDiag hmPay w_eff * R_c =
          R_c * slot0SelectDiag hmPay w_eff by
        simp only [R_c, slot0SelectDiag, QRegister.basisOutcomeProjector_eq_diagonal,
          Matrix.diagonal_mul_diagonal, mul_comm], ← Matrix.mul_assoc, hRc_idem]
    calc (R_c * P_0) * (H.1ᴴ * slot0SelectDiag hmPay w_eff * H.1) * (R_c * P_0)
        = P_0 * (R_c * H.1) * slot0SelectDiag hmPay w_eff * (H.1 * R_c) * (P_0 * R_c) := by
            nth_rw 1 [hP0_Rc.symm]
            rw [show R_c * P_0 = R_c * (P_0 * R_c) by rw [hP0_Rc, ← Matrix.mul_assoc, hRc_idem],
              hH_sa]
            simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * (R_c * slot0SelectDiag hmPay w_eff * R_c) * H.1 * P_0 * R_c := by
            rw [hH_Rc]
            nth_rw 1 [← hH_Rc]
            rw [hH_sa]
            simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * (R_c * slot0SelectDiag hmPay w_eff) * H.1 * P_0 * R_c := by
            rw [hdiag_comm]
  rw [hLHS1, lemHex346 hmPay w_eff c, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_mul]
  have hterm (u : Fin (2 ^ mPayload)) :
      (((P_0 * H.1ᴴ) * (pay.basisOutcomeProjector u * R_c *
        sys.embedMatrix (Matrix.diagonal (fun xSys ↦
          lemHex344 hmPay w_eff c xSys u))) * H.1) * P_0) *
        R_c = (R_c * P_0) * (((2 : ℂ)⁻¹ ^ mPayload) •
        sys.embedMatrix (Matrix.diagonal (fun xSys ↦ lemHex344 hmPay w_eff c xSys u))) *
        (R_c * P_0) := by
    let D_u := Matrix.diagonal (fun xSys ↦ lemHex344 hmPay w_eff c xSys u)
    have hDu_Rc : sys.embedMatrix D_u * R_c = R_c * sys.embedMatrix D_u := by
      rw [embedMatrix_diagonal]
      simp only [R_c, QRegister.basisOutcomeProjector_eq_diagonal,
        Matrix.diagonal_mul_diagonal, mul_comm]
    calc (((P_0 * H.1ᴴ) * (pay.basisOutcomeProjector u * R_c * sys.embedMatrix D_u) * H.1) *
            P_0) * R_c
        = P_0 * H.1ᴴ * pay.basisOutcomeProjector u * (R_c * (sys.embedMatrix D_u * H.1)) *
            P_0 * R_c := by simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * pay.basisOutcomeProjector u * H.1 *
            ((R_c * (sys.embedMatrix D_u * P_0)) * R_c) := by
            rw [← hH_sys D_u, ← Matrix.mul_assoc R_c H.1, ← hH_Rc]
            simp only [Matrix.mul_assoc]
      _ = (P_0 * H.1ᴴ * pay.basisOutcomeProjector u * H.1 * P_0) *
            sys.embedMatrix D_u * (R_c * R_c) := by
            rw [← hP0_sys D_u, ← Matrix.mul_assoc R_c P_0, ← hP0_Rc,
              Matrix.mul_assoc P_0 R_c (sys.embedMatrix D_u), hDu_Rc.symm]
            simp only [Matrix.mul_assoc]
      _ = ((2 : ℂ)⁻¹ ^ mPayload) • (P_0 * sys.embedMatrix D_u * R_c) := by
            rw [FullSysPrepare6Slot.hadamardAll_proj_zero_conj pay u, hRc_idem,
              Matrix.smul_mul, Matrix.smul_mul]
      _ = (R_c * P_0) * (((2 : ℂ)⁻¹ ^ mPayload) • sys.embedMatrix D_u) * (R_c * P_0) := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
            refine congrArg (((2 : ℂ)⁻¹ ^ mPayload) • ·) ?_
            calc P_0 * sys.embedMatrix D_u * R_c
                = P_0 * (P_0 * sys.embedMatrix D_u * R_c) * R_c := by
                    nth_rw 1 [← hP0_idem, ← hRc_idem]
                    simp only [Matrix.mul_assoc]
              _ = (R_c * P_0) * sys.embedMatrix D_u * (R_c * P_0) := by
                    rw [hP0_sys D_u, Matrix.mul_assoc (sys.embedMatrix D_u) P_0 R_c, hP0_Rc,
                      ← Matrix.mul_assoc (sys.embedMatrix D_u) R_c P_0, hDu_Rc]
                    simp only [Matrix.mul_assoc]
                    rw [← Matrix.mul_assoc P_0 R_c, hP0_Rc]
                    simp only [Matrix.mul_assoc]
  change (∑ u : Fin (2 ^ mPayload), (((P_0 * H.1ᴴ) * (pay.basisOutcomeProjector u * R_c *
      sys.embedMatrix (Matrix.diagonal (fun xSys ↦ lemHex344 hmPay w_eff c xSys u))) * H.1) * P_0) *
      R_c) = _
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  have hsum_emb : (∑ x : Fin (2 ^ mPayload), ((2 : ℂ)⁻¹ ^ mPayload) • sys.embedMatrix
      (Matrix.diagonal (fun xSys ↦ lemHex344 hmPay w_eff c xSys x))) = Matrix.diagonal (fun g ↦
      ((2 : ℂ)⁻¹ ^ mPayload) * ∑ u : Fin (2 ^ mPayload),
      lemHex344 hmPay w_eff c (sys.extractIndex g) u) := by
    simp_rw [embedMatrix_diagonal]
    ext g₁ g₂
    by_cases hg : g₁ = g₂
    · subst hg
      simp [Matrix.sum_apply, Finset.mul_sum]
    · simp [Matrix.sum_apply, hg]
  rw [hsum_emb]
  have hBc_diag : B_c = Matrix.diagonal
      (fun xSys ↦ if c = 4 then bUnitTwosSlot0 w_eff xSys xSys else 1) := by
    ext i j
    dsimp only [B_c]
    by_cases hc4 : c = 4 <;> by_cases hij : i = j <;>
      simp [hc4, hij, bUnitTwosSlot0, Matrix.one_apply]
  rw [hBc_diag, embedMatrix_diagonal]
  apply congrArg Matrix.diagonal
  funext g
  exact lemHex34d hmPay hw c (sys.extractIndex g)
theorem slot0_hadamard_topBlock_coin4 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {w_eff : ℝ} (hw : elecQuadCenterOffset ≤ w_eff) :
    let c := fullSysCoinIdx 0
    let P_anc := (coreAncSym mPayload).basisOutcomeProjector
      (coinSelOutcome (selCoin3Sym mPayload) c)
    P_anc * (unitaryConj (coreHadamardUnitary mPayload) (slot0SelectUnitary hmPay w_eff)).1 *
      P_anc =
      P_anc * (coreSysSym mPayload).embedMatrix (bUnitTwosSlot0 w_eff) * P_anc := by
  simpa [show fullSysCoinIdx 0 = 4 from rfl] using slot0_hadamard_topBlock_all hmPay hw 4
private theorem slot0_term_abs_le {w_eff : ℝ} (hw : elecQuadCenterOffset ≤ w_eff) (u : Fin 64) :
    |1 - 2 * (slot0Thresh w_eff u : ℝ) / (2 : ℝ) ^ 42| ≤ 1 := by
  have hle : (slot0Thresh w_eff u : ℝ) ≤ (2 : ℝ) ^ 42 :=
    by exact_mod_cast slot0Thresh_le_two_pow_42 hw u
  have h0 : (0 : ℝ) ≤ (slot0Thresh w_eff u : ℝ) := Nat.cast_nonneg _
  have hp42 : (0 : ℝ) < (2 : ℝ) ^ 42 := by positivity
  have hdiv : 2 * (slot0Thresh w_eff u : ℝ) / (2 : ℝ) ^ 42 ≤ 2 :=
    (div_le_iff₀ hp42).mpr (by linarith)
  have hdiv0 : 0 ≤ 2 * (slot0Thresh w_eff u : ℝ) / (2 : ℝ) ^ 42 :=
    div_nonneg (by linarith) hp42.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩
theorem norm_bUnitTwosSlot0_le_one {w_eff : ℝ} (hw : elecQuadCenterOffset ≤ w_eff) :
    ‖bUnitTwosSlot0 w_eff‖ ≤ 1 := by
  refine l2_opNorm_diagonal_le _ 1 zero_le_one fun x ↦ ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (210151305 : ℝ) / (2 : ℝ) ^ 37)]
  have hsum_abs : |∑ m : Fin 654,
      (1 - 2 * (slot0Thresh w_eff ((TwosCompAndWire0Cancel.elec654Axes m).extractIndex x) : ℝ) /
        (2 : ℝ) ^ 42)| ≤ 654 :=
    (Finset.abs_sum_le_sum_abs _ _).trans <|
      (Finset.sum_le_sum fun m _ ↦ slot0_term_abs_le hw _).trans_eq (by simp)
  have hfac : ((210151305 : ℝ) / (2 : ℝ) ^ 37) * 654 ≤ 1 := by norm_num
  nlinarith
private def lemHex34e : Fin numElectrons × Fin 3 ≃ Fin 654 where
  toFun iw := ⟨3 * iw.1.val + iw.2.val, by
    have hne : numElectrons = 218 := rfl
    have hi := iw.1.isLt
    have hw := iw.2.isLt
    omega⟩
  invFun m := (⟨m.val / 3, by
    have hne : numElectrons = 218 := rfl
    have hm := m.isLt
    omega⟩,
    ⟨m.val % 3, Nat.mod_lt _ (by omega)⟩)
  left_inv iw := by
    obtain ⟨i, w⟩ := iw
    have hv : 3 * i.val + w.val = w.val + 3 * i.val := by ring
    ext
    · dsimp
      rw [hv, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt w.isLt, zero_add]
    · dsimp
      rw [hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt w.isLt]
  right_inv m := by
    ext
    dsimp
    exact Nat.div_add_mod m.val 3
private theorem lemHex34f : Function.Injective twosComp6Int := by
  intro u v huv
  have := u.isLt
  have := v.isLt
  unfold twosComp6Int at huv
  split_ifs at huv <;> exact Fin.ext (by omega)
private theorem lemHex350 (u : Fin 64) :
    KaratsubaQft64Matrix.twosComp6Int u = twosComp6Int u := by
  revert u; decide
theorem smToTwosSys_conj_diagonal (d : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → ℂ) :
    smToTwosSysUnitary.1 * Matrix.diagonal d * smToTwosSysUnitary.1 =
      Matrix.diagonal (d ∘ smToTwosSysPerm) := by
  have hU : smToTwosSysUnitary = fwdPermUnitary smToTwosSysPerm := rfl
  nth_rw 1 [← smToTwosSysUnitary_conjTranspose]
  rw [hU]
  exact fwdPermUnitary_conj_diagonal smToTwosSysPerm d
theorem bUnitTwosSlot0_permElectron (w_eff : ℝ) (g : Equiv.Perm (Fin numElectrons))
    (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (hx : IsGridState x) (_hy : IsGridState y) :
    (smToTwosSysUnitary.1 * bUnitTwosSlot0 w_eff * smToTwosSysUnitary.1) (permElectron g x)
    (permElectron g y) = (smToTwosSysUnitary.1 * bUnitTwosSlot0 w_eff * smToTwosSysUnitary.1)
    x y := by
  rw [bUnitTwosSlot0, smToTwosSys_conj_diagonal]
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply]
    apply congrArg (fun s : ℝ ↦ (((210151305 : ℝ) / (2 : ℝ) ^ 37 * s : ℝ) : ℂ))
    rw [← Equiv.sum_comp lemHex34e, ← Equiv.sum_comp lemHex34e,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Eq.trans ?_ (Equiv.sum_comp g fun i ↦ ∑ w : Fin 3, (1 - 2 * (slot0Thresh w_eff
      ((TwosCompAndWire0Cancel.elec654Axes (lemHex34e (i, w))).extractIndex (smToTwosSysPerm x)) :
      ℝ) / (2 : ℝ) ^ 42))
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    have hxg : IsGridState (permElectron g x) := (isGridState_permElectron g x).mpr hx
    have hfield_eq : elecAxisField (smToTwosSysPerm (permElectron g x)) i w = elecAxisField
        (smToTwosSysPerm x) (g i) w := by
      apply lemHex34f
      have hm1 : twosComp6Int (elecAxisField (smToTwosSysPerm (permElectron g x)) i w) =
          momentum (permElectron g x) (.electron i) w :=
        (lemHex350 _).symm.trans (twosComp6_smToTwosSys_eq_momentum hxg i w)
      have hm2 : twosComp6Int (elecAxisField (smToTwosSysPerm x) (g i) w) =
          momentum x (.electron (g i)) w :=
        (lemHex350 _).symm.trans (twosComp6_smToTwosSys_eq_momentum hx (g i) w)
      rw [hm1, hm2, momentum_permElectron_electron]
    exact congrArg (fun u ↦ 1 - 2 * (slot0Thresh w_eff u : ℝ) / (2 : ℝ) ^ 42) hfield_eq
  · have hne : permElectron g x ≠ permElectron g y :=
      fun heq ↦ hxy ((permElectron g).injective heq)
    rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hxy]
private theorem lemHex351 {x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)} (_hx : IsGridState x) :
    (∑ i : Fin numElectrons, waveNumberSq (momentum x (.electron i)) / 2) - elecQuadCenterOffset =
      ∑ i : Fin numElectrons, ∑ w : Fin 3,
        ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
          (((momentum x (.electron i) w : ℤ) : ℝ) ^ 2 - 961 / 2) := by
  rw [sum_electron_stepNumberSq_div_two_eq, elecQuadCenterOffset_eq, Nat.cast_sum]
  have hnorm : ∀ i : Fin numElectrons,
      ((intNormSq (momentum x (.electron i)) : ℕ) : ℝ) =
        ∑ w : Fin 3, ((momentum x (.electron i) w : ℤ) : ℝ) ^ 2 := fun i ↦ by
    rw [Fin.sum_univ_three]
    dsimp [intNormSq]
    have hsq (q : ℤ) : (q.natAbs : ℝ) ^ 2 = (q : ℝ) ^ 2 := by simp
    push_cast
    rw [hsq, hsq, hsq]
  simp_rw [hnorm]
  have hconst : (∑ _i : Fin numElectrons, ∑ _w : Fin 3, (961 / 2 : ℝ)) = 314247 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, numElectrons, nsmul_eq_mul,
      Nat.cast_ofNat]
    ring
  rw [← hconst, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ ↦ ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
theorem bUnitTwosSlot0_fermionic_err_le (cfg : SpecsAux.SpecMirror.Configuration)
    (spinUp : Finset (Fin numElectrons)) (E : Fin 6 → ℝ) (hE0 : E 0 = elecQuadCenterOffset)
    {w_eff : ℝ} (hw : elecQuadCenterOffset ≤ w_eff) : ‖SpecsAux.SpecMirror.fermionicProjector spinUp
    * ((w_eff : ℂ) • (smToTwosSysUnitary.1 * bUnitTwosSlot0 w_eff * smToTwosSysUnitary.1) -
    sixChannelShifted cfg E 0) * SpecsAux.SpecMirror.fermionicProjector spinUp‖ ≤ w_eff / (2 : ℝ) ^
    36 + w_eff / (2 : ℝ) ^ 41 := by
  let P_F := SpecsAux.SpecMirror.fermionicProjector spinUp
  let G := SpecsAux.gridProjector
  let Δ := (w_eff : ℂ) • (smToTwosSysUnitary.1 * bUnitTwosSlot0 w_eff * smToTwosSysUnitary.1) -
    sixChannelShifted cfg E 0
  have hw_pos : 0 < w_eff := lt_of_lt_of_le elecQuadCenterOffset_pos hw
  have hPF_G : P_F * G = P_F := SpecsAux.fermionicProjector_mul_gridProjector spinUp
  have hG_PF : G * P_F = P_F :=
    (SpecsAux.commute_fermionicProjector_gridProjector spinUp).symm.trans hPF_G
  have hwrap : P_F * Δ * P_F = P_F * (G * Δ * G) * P_F := by
    calc P_F * Δ * P_F
        = (P_F * G) * Δ * (G * P_F) := by rw [hPF_G, hG_PF]
      _ = P_F * (G * Δ * G) * P_F := by simp only [Matrix.mul_assoc]
  rw [hwrap]
  have heps_nonneg : 0 ≤ w_eff / (2 : ℝ) ^ 36 + w_eff / (2 : ℝ) ^ 41 := by positivity
  have hGΔG_diag : G * Δ * G =
      Matrix.diagonal (fun x ↦
        open Classical in
        if IsGridState x then
          ((((w_eff * (((210151305 : ℝ) / (2 : ℝ) ^ 37) *
              ∑ m : Fin 654,
                (1 - 2 * (slot0Thresh w_eff
                  ((TwosCompAndWire0Cancel.elec654Axes m).extractIndex (smToTwosSysPerm x)) : ℝ) /
                  (2 : ℝ) ^ 42))) -
            ((∑ i : Fin numElectrons, waveNumberSq (momentum x (.electron i)) / 2) - E 0)) : ℝ) : ℂ)
        else 0) := by
    have hshift : sixChannelShifted cfg E 0 =
        electronKineticOp - (E 0 : ℂ) • LiteralKineticAndMidpoint128.gridProjector := by
      have hraw : sixChannelRaw cfg 0 = electronKineticOp := by
        rw [electronKineticOp_eq_matrixOf]
        ext x y
        change elecKinOp x y = _
        by_cases hxy : x = y
        · subst hxy
          by_cases hx : IsGridState x <;> simp [elecKinOp, hx]
        · simp [elecKinOp, hxy]
      have hGP : SpecsAux.gridProjector = LiteralKineticAndMidpoint128.gridProjector := by
        ext x y
        by_cases h : x = y <;> simp [SpecsAux.gridProjector,
          LiteralKineticAndMidpoint128.gridProjector, h]
      unfold sixChannelShifted
      rw [hraw, sixChannelGridProjector_eq_specsGridProjector, hGP]
    change G * ((w_eff : ℂ) • (smToTwosSysUnitary.1 * bUnitTwosSlot0 w_eff * smToTwosSysUnitary.1) -
        sixChannelShifted cfg E 0) * G = _
    rw [hshift, electronKineticOp_sub_offset_eq_diagonal, bUnitTwosSlot0, smToTwosSys_conj_diagonal]
    have hG_eq : G = Matrix.diagonal (fun x ↦
      open Classical in if IsGridState x then (1 : ℂ) else 0) := rfl
    have hsub_diag : ∀ {d₁ d₂ : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → ℂ},
        (w_eff : ℂ) • Matrix.diagonal d₁ - Matrix.diagonal d₂ =
          Matrix.diagonal (fun x ↦ (w_eff : ℂ) * d₁ x - d₂ x) := by
      intro d₁ d₂
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hG_eq, hsub_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    classical
    by_cases hx : IsGridState x
    · simp only [hx, ↓reduceIte, one_mul, mul_one, Function.comp_apply]
      push_cast
      ring
    · simp [hx]
  have hGΔG_norm : ‖G * Δ * G‖ ≤ w_eff / (2 : ℝ) ^ 36 + w_eff / (2 : ℝ) ^ 41 := by
    rw [hGΔG_diag]
    refine l2_opNorm_diagonal_le _ _ heps_nonneg fun x ↦ ?_
    classical
    split_ifs with hx
    · rw [Complex.norm_real, Real.norm_eq_abs, hE0, lemHex351 hx]
      rw [← Equiv.sum_comp lemHex34e, Fintype.sum_prod_type]
      let termA : Fin numElectrons → Fin 3 → ℝ := fun i w ↦
        1 - 2 * (slot0Thresh w_eff (elecAxisField (smToTwosSysPerm x) i w) : ℝ) / (2 : ℝ) ^ 42
      let termE : Fin numElectrons → Fin 3 → ℝ := fun i w ↦
        ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
          (((momentum x (.electron i) w : ℤ) : ℝ) ^ 2 - 961 / 2)
      let avgA : ℝ := (1 / 654 : ℝ) * ∑ i : Fin numElectrons, ∑ w : Fin 3, termA i w
      let sumE : ℝ := ∑ i : Fin numElectrons, ∑ w : Fin 3, termE i w
      have haxis_ne32 : ∀ (i : Fin numElectrons) (w : Fin 3),
          (elecAxisField (smToTwosSysPerm x) i w).val ≠ 32 := by
        intro i w h32
        have hmom : twosComp6Int (elecAxisField (smToTwosSysPerm x) i w) = momentum x
            (.electron i) w := (lemHex350 _).symm.trans (twosComp6_smToTwosSys_eq_momentum hx i w)
        have h32_int : twosComp6Int (elecAxisField (smToTwosSysPerm x) i w) = -32 := by
          unfold twosComp6Int
          rw [h32]
          norm_num
        rw [h32_int] at hmom
        have hle31 := momentum_electron_natAbs_le_31 x i w
        rw [← hmom] at hle31
        norm_num at hle31
      have haxis_int : ∀ (i : Fin numElectrons) (w : Fin 3),
          slot0AxisInt (elecAxisField (smToTwosSysPerm x) i w) = momentum x (.electron i) w := by
        intro i w
        simp only [slot0AxisInt, haxis_ne32 i w, ite_false]
        exact (lemHex350 _).symm.trans (twosComp6_smToTwosSys_eq_momentum hx i w)
      have hpt_err : ∀ (i : Fin numElectrons) (w : Fin 3),
          |w_eff * termA i w - 654 * termE i w| ≤ w_eff / (2 : ℝ) ^ 41 := by
        intro i w
        let u := elecAxisField (smToTwosSysPerm x) i w
        let X := slot0ThreshReal w_eff u
        have hX0 : 0 ≤ X := (slot0ThreshReal_bounds hw u).1
        have hfl_le : (Nat.floor X : ℝ) ≤ X := Nat.floor_le hX0
        have hlt_fl : X - 1 < (Nat.floor X : ℝ) := by linarith [Nat.lt_floor_add_one X]
        have hE_eq : 654 * termE i w = w_eff * (1 - X / (2 : ℝ) ^ 41) := by
          dsimp [X, slot0ThreshReal, termE, u]
          rw [haxis_int i w]
          field_simp [ne_of_gt hw_pos]
          ring
        have hA_eq : w_eff * termA i w = w_eff * (1 - (Nat.floor X : ℝ) / (2 : ℝ) ^ 41) := by
          dsimp [termA, u, X]
          rw [slot0Thresh_eq_floor]
          ring
        rw [hA_eq, hE_eq]
        have hdiff : w_eff * (1 - (Nat.floor X : ℝ) / (2 : ℝ) ^ 41) - w_eff *
            (1 - X / (2 : ℝ) ^ 41) = (w_eff / (2 : ℝ) ^ 41) * (X - (Nat.floor X : ℝ)) := by
          ring
        rw [hdiff, abs_mul, abs_of_pos (by positivity : 0 < w_eff / (2 : ℝ) ^ 41)]
        have habs1 : |X - (Nat.floor X : ℝ)| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        nlinarith
      have hquant_err : |w_eff * avgA - sumE| ≤ w_eff / (2 : ℝ) ^ 41 := by
        have hrewrite : w_eff * avgA - sumE = (1 / 654 : ℝ) * ∑ i : Fin numElectrons, ∑ w :
            Fin 3, (w_eff * termA i w - 654 * termE i w) := by
          dsimp [avgA, sumE]
          rw [Finset.mul_sum, Finset.mul_sum]
          simp_rw [Finset.mul_sum]
          rw [← Finset.sum_sub_distrib]
          simp_rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
          ring
        rw [hrewrite, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 654)]
        have hsum_le :
            |∑ i : Fin numElectrons, ∑ w : Fin 3, (w_eff * termA i w - 654 * termE i w)| ≤
              654 * (w_eff / (2 : ℝ) ^ 41) := by
          calc |∑ i : Fin numElectrons, ∑ w : Fin 3, (w_eff * termA i w - 654 * termE i w)|
              ≤ ∑ i : Fin numElectrons, |∑ w : Fin 3, (w_eff * termA i w - 654 * termE i w)| :=
                  Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i : Fin numElectrons, ∑ w : Fin 3, |w_eff * termA i w - 654 * termE i w| :=
                  Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin numElectrons, ∑ _w : Fin 3, (w_eff / (2 : ℝ) ^ 41) :=
                  Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun w _ ↦ hpt_err i w
            _ = 654 * (w_eff / (2 : ℝ) ^ 41) := by
                  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, numElectrons,
                    nsmul_eq_mul]
                  ring
        nlinarith
      have havgA_abs : |avgA| ≤ 1 := by
        dsimp [avgA]
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 654)]
        have h2 : |∑ i : Fin numElectrons, ∑ w : Fin 3, termA i w| ≤ 654 := by
          refine ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)).trans ?_
          refine (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun w _ ↦
            slot0_term_abs_le hw _).trans_eq ?_
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, numElectrons,
            nsmul_eq_mul]
          norm_num
        nlinarith
      have hsplit_err : w_eff * (((210151305 : ℝ) / (2 : ℝ) ^ 37) * ∑ i : Fin numElectrons, ∑
          w : Fin 3, termA i w) - sumE = -(w_eff / (2 : ℝ) ^ 36 * avgA) +
          (w_eff * avgA - sumE) := by
        dsimp [avgA]
        ring
      change |w_eff * (((210151305 : ℝ) / (2 : ℝ) ^ 37) *
          ∑ i : Fin numElectrons, ∑ w : Fin 3, termA i w) - sumE| ≤ _
      rw [hsplit_err]
      have hrej_err : |-(w_eff / (2 : ℝ) ^ 36 * avgA)| ≤ w_eff / (2 : ℝ) ^ 36 := by
        rw [abs_neg, abs_mul, abs_of_pos (by positivity : 0 < w_eff / (2 : ℝ) ^ 36)]
        nlinarith
      exact (abs_add_le _ _).trans (add_le_add hrej_err hquant_err)
    · rw [norm_zero]
      exact heps_nonneg
  exact (Slot3Slot5QuantizedChannelBridge.norm_mul_fermionicProjector_le
      spinUp (G * Δ * G)).2.trans hGΔG_norm
theorem bUnitTwosSlot0_fermionic_err_le_six_e7 (cfg : SpecsAux.SpecMirror.Configuration)
    (spinUp : Finset (Fin numElectrons)) (E : Fin 6 → ℝ) (hE0 : E 0 = elecQuadCenterOffset)
    {w_eff : ℝ} (hw_lo : elecQuadCenterOffset ≤ w_eff) (hw_hi : w_eff ≤ 35000) :
    ‖SpecsAux.SpecMirror.fermionicProjector spinUp * ((w_eff : ℂ) • (smToTwosSysUnitary.1 *
    bUnitTwosSlot0 w_eff * smToTwosSysUnitary.1) - sixChannelShifted cfg E 0) *
    SpecsAux.SpecMirror.fermionicProjector spinUp‖ ≤ 6 / 10 ^ 7 := by
  have h1 := bUnitTwosSlot0_fermionic_err_le cfg spinUp E hE0 hw_lo
  have h2 : w_eff / (2 : ℝ) ^ 36 + w_eff / (2 : ℝ) ^ 41 ≤ 6 / 10 ^ 7 := by
    have hnum : (35000 : ℝ) / (2 : ℝ) ^ 36 + (35000 : ℝ) / (2 : ℝ) ^ 41 ≤ 6 / 10 ^ 7 := by
      norm_num
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ 36 by norm_num, show (0 : ℝ) < (2 : ℝ) ^ 41 by norm_num]
  exact h1.trans h2
theorem bUnitTwosSlot0_lambda_err_intr
    (cfg : SpecsAux.SpecMirror.Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E_vec : Fin 6 → ℝ := fun j ↦ if j = 0 then elecQuadCenterOffset else 0
    ‖SpecsAux.SpecMirror.fermionicProjector spinUp *
        ((lambdaSlot0TeHi : ℂ) •
            (smToTwosSysUnitary.1 * bUnitTwosSlot0 lambdaSlot0TeHi * smToTwosSysUnitary.1) -
          sixChannelShifted cfg E_vec 0) *
        SpecsAux.SpecMirror.fermionicProjector spinUp‖ ≤
      6 / 10 ^ 7 :=
  bUnitTwosSlot0_fermionic_err_le_six_e7 cfg spinUp _ (lemHex339 rfl)
    (le_of_lt elecQuadCenterOffset_lt_lambdaSlot0TeHi)
    (by unfold lambdaSlot0TeHi; norm_num)
end MomSlots01Slot0ElectronKinetic
end
end ModMomSlots01Slot0ElectronKinetic

section ModMomSlot0CircuitHalf
@[expose] public section
namespace MomSlot0CircuitHalf
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.DyadicSubgridToeplitz128
open PosMomSelectDynamic
open FullSysPrepare6Slot
open LiteralKineticAndMidpoint128
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open QProg Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux.FullScaleBESector
open MeasureBranchHadamardSem
open StreamingBchComparator
open MomSlots01Slot0ElectronKinetic (coinBitFin2 momCoinProj slot0SelectUnitary bUnitTwosSlot0
  slot0SelectUnitary_sa slot0SelectUnitary_offCoin slot0_hadamard_topBlock_coin4
  norm_bUnitTwosSlot0_le_one bUnitTwosSlot0_permElectron bUnitTwosSlot0_lambda_err_intr
  elecQuadCenterOffset_lt_lambdaSlot0TeHi)
section ClassicalAndGatePrimitives
abbrev uMat {N : ℕ} (U : unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := U.1
noncomputable abbrev ket {K : ℕ} (β : BitAssignment K) : Fin (2 ^ K) → ℂ :=
  basisState ((basisBitsEquiv K).symm β)
@[simp] theorem basisBits_symm_apply {K : ℕ} (β : BitAssignment K) : basisBits K
    ((basisBitsEquiv K).symm β) = β := (basisBitsEquiv K).apply_symm_apply β
@[simp] theorem symm_basisBits_apply {K : ℕ} (j : Fin (2 ^ K)) : (basisBitsEquiv K).symm
    (basisBits K j) = j := (basisBitsEquiv K).symm_apply_apply j
theorem single_eq_ket {K : ℕ} (g : Fin (2 ^ K)) :
    (Pi.single g 1 : Fin (2 ^ K) → ℂ) = ket (basisBits K g) := by
  simp [ket, basisState]
theorem matrix_ext_ket {K : ℕ} {A B : Matrix (Fin (2 ^ K)) (Fin (2 ^ K)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have hcol := congrFun (h (basisBits K j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using hcol
theorem zmod2_eq_or (x : ZMod 2) : x = 0 ∨ x = 1 := by
  match x with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr rfl
@[simp] theorem zmod2_val_zero : (0 : ZMod 2).val = 0 := rfl
@[simp] theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_or x with rfl | rfl <;> rfl
noncomputable def writeReg {K m : ℕ} (β : BitAssignment K) (r : QRegister m K)
    (γ : BitAssignment m) : BitAssignment K :=
  basisBits K (r.replaceIndex ((basisBitsEquiv K).symm β) ((basisBitsEquiv m).symm γ))
theorem writeReg_apply_reg {K m : ℕ} (β : BitAssignment K) (r : QRegister m K)
    (γ : BitAssignment m) (i : Fin m) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]
theorem writeReg_apply_of_not_mem {K m : ℕ} (β : BitAssignment K) (r : QRegister m K)
    (γ : BitAssignment m) (w : Wire K) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
theorem writeReg_eq_update {K m : ℕ} (β : BitAssignment K) (r : QRegister m K)
    (γ : BitAssignment m) (i₀ : Fin m) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeReg β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne (fun h ↦ hi (r.wires.injective h)), hγ i hi]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne]
    exact fun h ↦ hw ⟨i₀, h.symm⟩
noncomputable abbrev localIdx {K m : ℕ} (r : QRegister m K) (β : BitAssignment K) : Fin
    (2 ^ m) := (basisBitsEquiv m).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket {K m : ℕ} (r : QRegister m K)
    (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (β : BitAssignment K) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ m), A l (localIdx r β) • ket (writeReg β r (basisBits m l)) := by
  have hext : r.extractIndex ((basisBitsEquiv K).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ m)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ m), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]
theorem single_gate_mulVec_ket {K : ℕ} (g : PrimitiveGate 1) (q : Wire K)
    (β : BitAssignment K) : (uMat (Circuit.single g q).eval).mulVec (ket β) = uMat g.eval 0
    (if (β q).val = 0 then 0 else 1) • ket (Function.update β q 0) + uMat g.eval 1
    (if (β q).val = 0 then 0 else 1) • ket (Function.update β q 1) := by
  change ((QRegister.singleton q).embedMatrix (uMat g.eval)).mulVec (ket β) = _
  erw [embedMatrix_mulVec_ket, Fin.sum_univ_two]
  have hloc : localIdx (QRegister.singleton q) β = (if (β q).val = 0 then 0 else 1) := by
    apply (basisBitsEquiv 1).injective
    rw [localIdx, Equiv.apply_symm_apply]
    funext i
    fin_cases i
    change β q = basisBits 1 (if (β q).val = 0 then 0 else 1) 0
    rcases zmod2_eq_or (β q) with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  have hw0 : writeReg β (QRegister.singleton q) (basisBits 1 0) = Function.update β q 0 :=
    writeReg_eq_update β (QRegister.singleton q) (basisBits 1 0) 0
      (fun i hi ↦ (hi (Subsingleton.elim i 0)).elim) |>.trans (by congr 1)
  have hw1 : writeReg β (QRegister.singleton q) (basisBits 1 1) = Function.update β q 1 :=
    writeReg_eq_update β (QRegister.singleton q) (basisBits 1 1) 0
      (fun i hi ↦ (hi (Subsingleton.elim i 0)).elim) |>.trans (by congr 1)
  erw [hloc, hw0, hw1]
theorem eval_X_ket {K : ℕ} (q : Wire K) (β : BitAssignment K) :
    (uMat (Circuit.X q).eval).mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  have hx00 : uMat PrimitiveGate.X.eval 0 0 = 0 := by simp [uMat, PrimitiveGate.eval, Qubit.X]
  have hx10 : uMat PrimitiveGate.X.eval 1 0 = 1 := by simp [uMat, PrimitiveGate.eval, Qubit.X]
  have hx01 : uMat PrimitiveGate.X.eval 0 1 = 1 := by simp [uMat, PrimitiveGate.eval, Qubit.X]
  have hx11 : uMat PrimitiveGate.X.eval 1 1 = 0 := by simp [uMat, PrimitiveGate.eval, Qubit.X]
  rw [Circuit.X, single_gate_mulVec_ket]
  rcases zmod2_eq_or (β q) with h | h
  · simp [h, hx00, hx10]
  · simp [h, hx01, hx11]
theorem cnot_matrix_entry (j l : Fin 4) : uMat PrimitiveGate.CNOT.eval l j = if l =
    (if j = 1 then 3 else if j = 3 then 1 else j) then 1 else 0 := by
  dsimp only [uMat]
  rw [PrimitiveGate.eval_cnot_val, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]
  refine ite_congr (propext ?_) (fun _ ↦ rfl) (fun _ ↦ rfl)
  revert j l
  decide
theorem cnot_out_bits (j : Fin 4) (i : Fin 2) :
    basisBits 2 (if j = 1 then 3 else if j = 3 then 1 else j) i =
      if i = 1 then basisBits 2 j 1 + basisBits 2 j 0 else basisBits 2 j i := by
  fin_cases j <;> fin_cases i <;> decide
private theorem eval_permGate_ket {K m : ℕ} (r : QRegister m K)
    (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (out : Fin (2 ^ m) → Fin (2 ^ m))
    (hmat : ∀ j l, A l j = if l = out j then 1 else 0) (i₀ : Fin m) (v : ZMod 2)
    (β : BitAssignment K)
    (hbits : ∀ i : Fin m, basisBits m (out (localIdx r β)) i = if i = i₀ then v else β (r i)) :
    (r.embedMatrix A).mulVec (ket β) = ket (Function.update β (r i₀) v) := by
  rw [embedMatrix_mulVec_ket]
  simp_rw [hmat (localIdx r β), ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [writeReg_eq_update β r _ i₀ (fun i hi ↦ by simp [hbits i, hi])]
  simp [hbits i₀]
theorem eval_CNOT_ket {K : ℕ} (c t : Wire K) (hct : c ≠ t) (β : BitAssignment K) :
    (uMat (Circuit.CNOT c t hct).eval).mulVec (ket β) =
      ket (Function.update β t (β t + β c)) := by
  let r2 : QRegister 2 K := QRegister.pair c t hct
  have hjb (k : Fin 2) : basisBits 2 (localIdx r2 β) k = β (r2 k) :=
    congrFun ((basisBitsEquiv 2).apply_symm_apply _) k
  exact eval_permGate_ket r2 (uMat PrimitiveGate.CNOT.eval)
    (fun j ↦ if j = 1 then 3 else if j = 3 then 1 else j) cnot_matrix_entry 1 (β t + β c) β
    fun i ↦ (cnot_out_bits _ i).trans (by
      simp only [hjb]
      rfl)
theorem toff_matrix_entry (j l : Fin 8) : uMat PrimitiveGate.TOFF.eval l j = if l =
    (if j = 3 then 7 else if j = 7 then 3 else j) then 1 else 0 := by
  dsimp only [uMat]
  rw [PrimitiveGate.eval_toffoli_val, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]
  refine ite_congr (propext ?_) (fun _ ↦ rfl) (fun _ ↦ rfl)
  revert j l
  decide
theorem toff_out_bits (j : Fin 8) (i : Fin 3) :
    basisBits 3 (if j = 3 then 7 else if j = 7 then 3 else j) i =
      if i = 2 then basisBits 3 j 2 + basisBits 3 j 0 * basisBits 3 j 1 else basisBits 3 j i := by
  fin_cases j <;> fin_cases i <;> decide
theorem eval_TOFF_ket {K : ℕ} (c₁ c₂ t : Wire K) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment K) : (uMat (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval).mulVec (ket β) =
    ket (Function.update β t (β t + β c₁ * β c₂)) := by
  let r3 : QRegister 3 K := QRegister.triple c₁ c₂ t h₁₂ h₁t h₂t
  have hjb (k : Fin 3) : basisBits 3 (localIdx r3 β) k = β (r3 k) :=
    congrFun ((basisBitsEquiv 3).apply_symm_apply _) k
  exact eval_permGate_ket r3 (uMat PrimitiveGate.TOFF.eval)
    (fun j ↦ if j = 3 then 7 else if j = 7 then 3 else j) toff_matrix_entry 2
    (β t + β c₁ * β c₂) β fun i ↦ (toff_out_bits _ i).trans (by
      simp only [hjb]
      rfl)
inductive RevProg (K : ℕ) : Type
  | nil : RevProg K
  | x (t : Wire K) : RevProg K
  | cnot (c t : Wire K) (h : c ≠ t) : RevProg K
  | toff (c₁ c₂ t : Wire K) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : RevProg K
  | seq (p₁ p₂ : RevProg K) : RevProg K
namespace RevProg
def toCircuit {K : ℕ} : RevProg K → Circuit K
  | .nil => .identity
  | .x t => Circuit.X t
  | .cnot c t h => Circuit.CNOT c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => p₁.toCircuit.seq p₂.toCircuit
def inv {K : ℕ} : RevProg K → RevProg K
  | .nil => .nil
  | .x t => .x t
  | .cnot c t h => .cnot c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => .toff c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => .seq p₂.inv p₁.inv
def eval {K : ℕ} : RevProg K → BitAssignment K → BitAssignment K
  | .nil, β => β
  | .x t, β => Function.update β t (β t + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .toff c₁ c₂ t _ _ _, β => Function.update β t (β t + β c₁ * β c₂)
  | .seq p₁ p₂, β => p₂.eval (p₁.eval β)
@[simp] theorem toCircuit_inv {K : ℕ} (p : RevProg K) :
    p.inv.toCircuit = p.toCircuit.inverse := by
  induction p with
  | nil => rfl
  | x _ => rfl
  | cnot _ _ _ => rfl
  | toff _ _ _ _ _ _ => rfl
  | seq p₁ p₂ ih₁ ih₂ => simp [inv, toCircuit, Circuit.inverse_seq, ih₁, ih₂]
@[simp] theorem count_t_zero {K : ℕ} (p : RevProg K) :
    p.toCircuit.count PrimitiveGate.T = 0 := by
  induction p <;> simp_all [toCircuit]
@[simp] theorem eval_inv_left {K : ℕ} (p : RevProg K) (β : BitAssignment K) :
    p.inv.eval (p.eval β) = β := by
  induction p generalizing β with
  | nil => rfl
  | x t => simp [inv, eval]
  | cnot c t h => simp [inv, eval, Function.update_of_ne h]
  | toff c₁ c₂ t _ h₁t h₂t => simp [inv, eval, Function.update_of_ne h₁t, Function.update_of_ne h₂t]
  | seq p₁ p₂ ih₁ ih₂ => simp [inv, eval, ih₂, ih₁]
theorem toCircuit_eval_ket {K : ℕ} (p : RevProg K) (β : BitAssignment K) :
    (uMat p.toCircuit.eval).mulVec (ket β) = ket (p.eval β) := by
  induction p generalizing β with
  | nil =>
      change (1 : Matrix (Fin (2 ^ K)) (Fin (2 ^ K)) ℂ).mulVec (ket β) = ket β
      exact Matrix.one_mulVec (ket β)
  | x t => exact eval_X_ket t β
  | cnot c t h => exact eval_CNOT_ket c t h β
  | toff c₁ c₂ t h₁₂ h₁t h₂t => exact eval_TOFF_ket c₁ c₂ t h₁₂ h₁t h₂t β
  | seq p₁ p₂ ih₁ ih₂ =>
      change (uMat p₂.toCircuit.eval * uMat p₁.toCircuit.eval).mulVec (ket β) =
        ket (p₂.eval (p₁.eval β))
      rw [← Matrix.mulVec_mulVec, ih₁, ih₂]
theorem wp_substCircuit_storeConst {Var : Type} [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (anc : Wire n) (c : Circuit n) : ∀
    (Θ : CQAssertionCompat Var (2 ^ n)), (∀ σ₁ σ₂, Θ σ₁ = Θ σ₂) → ∀ σ₁ σ₂, wp
    (ToffoliSubst.substCircuit v anc c).compile Θ σ₁ = wp
    (ToffoliSubst.substCircuit v anc c).compile Θ σ₂ := by
  intro Θ hΘ
  induction c generalizing Θ with
  | identity =>
      intro σ₁ σ₂
      simpa [ToffoliSubst.substCircuit] using hΘ σ₁ σ₂
  | gate g r =>
      intro σ₁ σ₂
      cases g with
      | toffoli =>
          dsimp only [ToffoliSubst.substCircuit, ToffoliSubst.substGate]
          split_ifs with h
          · let M₀ : Observable (Fin (2 ^ n)) := Θ σ₂
            have hEqΘ : Θ = fun _ ↦ M₀ := funext fun s ↦ hΘ s σ₂
            rw [hEqΘ]
            apply Subtype.ext
            simp [DynamicCircuit.jonesToffoli, DynamicCircuit.andUncompute,
              DynamicCircuit.andCompute,
              QProg.measureRegister]
          · simpa using hΘ σ₁ σ₂
      | _ =>
          simp only [ToffoliSubst.substCircuit, ToffoliSubst.substGate,
            DynamicCircuit.compile_circuit, DynamicCircuit.wp_circuit_compile,
            CQAssertion.qAssign_apply, hΘ σ₁ σ₂]
  | seq c₁ c₂ ih₁ ih₂ =>
      intro σ₁ σ₂
      simp only [ToffoliSubst.substCircuit, DynamicCircuit.compile_seq, wp_qSeq]
      exact ih₁ (wp (ToffoliSubst.substCircuit v anc c₂).compile Θ) (ih₂ Θ hΘ) σ₁ σ₂
end RevProg
namespace RevProg
@[simp] theorem eval_seq {K : ℕ} (p₁ p₂ : RevProg K) (β : BitAssignment K) :
    (p₁.seq p₂).eval β = p₂.eval (p₁.eval β) := rfl
def countToff {K : ℕ} : RevProg K → ℕ
  | .nil => 0
  | .x _ => 0
  | .cnot _ _ _ => 0
  | .toff _ _ _ _ _ _ => 1
  | .seq p₁ p₂ => p₁.countToff + p₂.countToff
@[simp] theorem toCircuit_count_toff {K : ℕ} (p : RevProg K) :
    p.toCircuit.count PrimitiveGate.TOFF = p.countToff := by
  induction p <;> simp_all [toCircuit, countToff]
end RevProg
def padZeroBits {kAct mClean : ℕ} (α : BitAssignment kAct) : BitAssignment (kAct + mClean) :=
  Fin.addCases α (fun _ ↦ 0)
noncomputable def phaseDiagUnitary {kAct : ℕ} (pred : BitAssignment kAct → ZMod 2) :
    Unitary (2 ^ kAct) :=
  let M : Matrix (Fin (2 ^ kAct)) (Fin (2 ^ kAct)) ℂ :=
    Matrix.diagonal fun g ↦ ((-1 : ℂ) ^ (pred (basisBits kAct g)).val)
  have hSymm : Mᴴ = M := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [M]
    · simp [M, hij, Ne.symm hij]
  have hSq : M * M = 1 := by
    ext i j
    rw [Matrix.diagonal_mul_diagonal]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rcases zmod2_eq_or (pred (basisBits kAct i)) with hp | hp <;> simp [hp]
    · simp [hij]
  ⟨M, Matrix.mem_unitaryGroup_iff.mpr (by rw [Matrix.star_eq_conjTranspose, hSymm]; exact hSq)⟩
section UnsignedAndSlot0
section UnsignedArithmetic
@[simp] theorem block_wires_eq {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n)
    (j : Fin width) :
    (QRegister.block offset width h).wires j = ⟨offset + j.val, by omega⟩ := rfl
@[simp] theorem fin_one_add_eq_succ {m : ℕ} (j : Fin m) (h : 1 + j.val < m + 1) :
    (⟨1 + j.val, h⟩ : Fin (m + 1)) = j.succ := Fin.ext (Nat.add_comm 1 j.val)
@[simp] theorem slice_one_succ {K m : ℕ} (r : QRegister (m + 1) K) (h : 1 + m ≤ m + 1)
    (j : Fin m) : (r.slice 1 m h) j = r j.succ := by
  simp
@[simp] theorem slice_zero_apply {K w n : ℕ} (r : QRegister n K) (h : 0 + w ≤ n) (j : Fin w) :
    (r.slice 0 w h) j = r ⟨j.val, by omega⟩ := by
  simp
abbrev slot0WorkWires : ℕ := 211
end UnsignedArithmetic
end UnsignedAndSlot0
end ClassicalAndGatePrimitives
theorem momCoinProj_eq_fullSys (mPayload : ℕ) (c : Fin 8) : momCoinProj mPayload c =
    FullSysMomSlots0135Concrete.momCoinProj mPayload c := by
  unfold momCoinProj FullSysMomSlots0135Concrete.momCoinProj coinBitFin2
    FullSysMomSlots0135Concrete.coinBitFin2
  rfl
theorem slot0_hadamard_topBlock_fullSys {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (_cfg : SpecsAux.SpecMirror.Configuration) :
    let P_anc := (FullSysMomSlots0135Concrete.momAncReg mPayload).basisOutcomeProjector
      (coinSelOutcome (FullSysMomSlots0135Concrete.momCoin3Sel mPayload)
        (FullSysPrepare6Slot.fullSysCoinIdx 0))
    P_anc * (unitaryConj (FullSysMomSlots0135Concrete.coreHadamardMom mPayload)
        (slot0SelectUnitary hmPay lambdaSlot0TeHi)).1 *
      P_anc =
      P_anc * (FullSysMomSlots0135Concrete.momSysReg mPayload).embedMatrix
        (bUnitTwosSlot0 lambdaSlot0TeHi) * P_anc :=
  slot0_hadamard_topBlock_coin4 hmPay (le_of_lt elecQuadCenterOffset_lt_lambdaSlot0TeHi)
noncomputable def slot0ElectronKineticOracleSym {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload 48 0 :=
  FullSysMomSlots0135Concrete.MomSingleSlotOracle.ofCoreOnly (mPayload := mPayload) (mPGTwist :=
    48) (k := 0)
    slot0WorkWires
    (fun _ ↦ lambdaSlot0TeHi)
    (fun _ ↦ elecQuadCenterOffset)
    (6 / 10 ^ 7)
    (fun _ ↦ slot0SelectUnitary hmPay lambdaSlot0TeHi)
    (fun _ ↦ bUnitTwosSlot0 lambdaSlot0TeHi)
    (fun _ ↦ by unfold lambdaSlot0TeHi; norm_num)
    (fun _ ↦ slot0SelectUnitary_sa hmPay lambdaSlot0TeHi)
    (fun _ ↦
      let hP := momCoinProj_eq_fullSys mPayload (FullSysPrepare6Slot.fullSysCoinIdx 0)
      (congrArg (fun P ↦ (slot0SelectUnitary hmPay lambdaSlot0TeHi).1 * (1 - P)) hP.symm).trans
        ((slot0SelectUnitary_offCoin hmPay lambdaSlot0TeHi).trans
          (congrArg (fun P ↦ 1 - P) hP)))
    (slot0_hadamard_topBlock_fullSys hmPay)
    (fun _ ↦ norm_bUnitTwosSlot0_le_one (le_of_lt elecQuadCenterOffset_lt_lambdaSlot0TeHi))
    (fun _ g x y hx hy ↦ bUnitTwosSlot0_permElectron lambdaSlot0TeHi g x y hx hy)
    (fun cfg spinUp ↦ bUnitTwosSlot0_lambda_err_intr cfg spinUp)
end MomSlot0CircuitHalf
end
end ModMomSlot0CircuitHalf

end QuantumComputation.Specs.StoppingPowerSolution
