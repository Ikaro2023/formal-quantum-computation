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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.HybridStream168

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModHoistInitStream1300And164
@[expose] public section
namespace HoistInitStream1300And164
section ConfigHoistInitStream1300And164
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
local instance (priority := 1000000) instNeZeroTwoPowHoistInit (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete (dXor32All654)
open NuclearTwistRealizes (slot2AxisSum)
open MeasureBranchHadamardSem (matrix_ext_ket)
open InterWalkRSum42Hoist
  (kFull80 rSum0 rSum14In42 rSum14Full rCoreFull hCoreFull_disj_Sum14 hSum14In42_disj
    pSum42Zero uHybridStream220_compute_ket rCSFull uXor32Full uStreamFull E_rawStream42
    E_stream42 pSum42Zero_mulVec_basisKet rSum0_extractIndex_eq_zero_iff
    uXor32Full_comm_pSum42Zero E_stream42_eq_conj_E_rawStream42 zeroSum14 core_zeroSum14)
open HybridStream168Aux (dCleanHybridStreamAdd164 dCleanHybridStreamInv164)
attribute [local irreducible]
  dXor32All654 dCleanHybridStreamAdd164
  dCleanHybridStreamInv164
def IsSlot2StreamUnitary (uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) : Prop
    := ∀ (w : Fin 3) (β₀ : BitAssignment kFull80), (∀ i : Fin 14, β₀ (rSum14Full w i) = 0) → ∃
    β : BitAssignment kFull80, ((rCSFull w).embedUnitary (uStream w)).1.mulVec (basisKet β₀) =
    basisKet β ∧ (∀ g : Wire kFull80, g ∉ (rSum14Full w).image → β g = β₀ g) ∧ (∀ i : Fin 14,
    β (rSum14Full w i) = if (slot2AxisSum w (fun q ↦ β₀ (rCoreFull q))).testBit i.val then 1
    else 0)
noncomputable def uStreamFullOf (uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14)))
    (w : Fin 3) : Unitary (2 ^ kFull80) := (rCSFull w).embedUnitary (uStream w)
noncomputable def uStream42InitOf
    (uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) : Unitary (2 ^ kFull80) :=
  uXor32Full * (uStreamFullOf uStream 2 *
    (uStreamFullOf uStream 1 * (uStreamFullOf uStream 0 * uXor32Full)))
theorem uStreamFullOf_mulVec_eq_of_zero
    {uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (hStr : IsSlot2StreamUnitary uStream) (w : Fin 3) (β₀ : BitAssignment kFull80)
    (hz : ∀ i : Fin 14, β₀ (rSum14Full w i) = 0) :
    (uStreamFullOf uStream w).1.mulVec (basisKet β₀) =
      (uStreamFull w).1.mulVec (basisKet β₀) := by
  obtain ⟨β₁, hk₁, hout₁, hsum₁⟩ := hStr w β₀ hz
  obtain ⟨β₂, hk₂, hout₂, hsum₂⟩ :=
    uHybridStream220_compute_ket w rCoreFull (rSum14Full w) (hCoreFull_disj_Sum14 w) β₀ hz
  change (uStreamFullOf uStream w).1.mulVec (basisKet β₀) = basisKet β₁ at hk₁
  change (uStreamFull w).1.mulVec (basisKet β₀) = basisKet β₂ at hk₂
  have hβ : β₁ = β₂ := by
    funext g
    by_cases hg : g ∈ (rSum14Full w).image
    · rcases (QRegister.mem_image _ _).mp hg with ⟨i, rfl⟩
      rw [hsum₁ i, hsum₂ i]
    · rw [hout₁ g hg, hout₂ g hg]
  rw [hk₁, hk₂, hβ]
theorem uStreamFullOf_mul_pSum42Zero_eq_E_rawStream42
    {uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (hStr : IsSlot2StreamUnitary uStream) :
    (uStreamFullOf uStream 2 * (uStreamFullOf uStream 1 * uStreamFullOf uStream 0)).1 *
      pSum42Zero = E_rawStream42 := by
  apply matrix_ext_ket; intro β
  change ((uStreamFullOf uStream 2 * (uStreamFullOf uStream 1 * uStreamFullOf uStream 0)).1 *
    pSum42Zero).mulVec (basisKet β) =
    ((uStreamFull 2 * (uStreamFull 1 * uStreamFull 0)).1 * pSum42Zero).mulVec (basisKet β)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pSum42Zero_mulVec_basisKet]
  by_cases h0 : rSum0.extractIndex ((basisBitsEquiv kFull80).symm β) = 0
  · rw [ite_eq_left h0]
    have hzAll : ∀ j : Fin 42, β (rSum0 j) = 0 := (rSum0_extractIndex_eq_zero_iff β).mp h0
    have hz0 : ∀ i : Fin 14, β (rSum14Full 0 i) = 0 := fun i ↦ hzAll (rSum14In42 0 i)
    obtain ⟨β₁, hk₁, hout₁, _⟩ :=
      uHybridStream220_compute_ket 0 rCoreFull (rSum14Full 0) (hCoreFull_disj_Sum14 0) β hz0
    have hz1 : ∀ i : Fin 14, β₁ (rSum14Full 1 i) = 0 := fun i ↦ by
      rw [hout₁ _ (fun hm ↦ ?_)]
      · exact hzAll (rSum14In42 1 i)
      · rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hSum14In42_disj (by decide : (0 : Fin 3) ≠ 1)).ne k i (rSum0.wires.injective hk)
    obtain ⟨β₂, hk₂, hout₂, _⟩ :=
      uHybridStream220_compute_ket 1 rCoreFull (rSum14Full 1) (hCoreFull_disj_Sum14 1) β₁ hz1
    have hz2 : ∀ i : Fin 14, β₂ (rSum14Full 2 i) = 0 := fun i ↦ by
      rw [hout₂ _ (fun hm ↦ ?_), hout₁ _ (fun hm ↦ ?_)]
      · exact hzAll (rSum14In42 2 i)
      · rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hSum14In42_disj (by decide : (0 : Fin 3) ≠ 2)).ne k i (rSum0.wires.injective hk)
      · rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hSum14In42_disj (by decide : (1 : Fin 3) ≠ 2)).ne k i (rSum0.wires.injective hk)
    change (uStreamFull 0).1.mulVec (basisKet β) = basisKet β₁ at hk₁
    change (uStreamFull 1).1.mulVec (basisKet β₁) = basisKet β₂ at hk₂
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    change (uStreamFullOf uStream 2).1.mulVec
      ((uStreamFullOf uStream 1).1.mulVec ((uStreamFullOf uStream 0).1.mulVec (basisKet β))) =
      (uStreamFull 2).1.mulVec ((uStreamFull 1).1.mulVec ((uStreamFull 0).1.mulVec (basisKet β)))
    rw [uStreamFullOf_mulVec_eq_of_zero hStr 0 β hz0, hk₁,
      uStreamFullOf_mulVec_eq_of_zero hStr 1 β₁ hz1, hk₂,
      uStreamFullOf_mulVec_eq_of_zero hStr 2 β₂ hz2]
  · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem uStream42InitOf_mul_pSum42Zero_eq_E_stream42
    {uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (hStr : IsSlot2StreamUnitary uStream) :
    (uStream42InitOf uStream).1 * pSum42Zero = E_stream42 := by
  have hRaw := uStreamFullOf_mul_pSum42Zero_eq_E_rawStream42 hStr
  calc (uStream42InitOf uStream).1 * pSum42Zero
    _ = uXor32Full.1 * (((uStreamFullOf uStream 2 *
          (uStreamFullOf uStream 1 * uStreamFullOf uStream 0)).1 * pSum42Zero) *
          uXor32Full.1) := by
          unfold uStream42InitOf
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          rw [← uXor32Full_comm_pSum42Zero]
    _ = uXor32Full.1 * E_rawStream42 * uXor32Full.1 := by rw [hRaw, Matrix.mul_assoc]
    _ = E_stream42 := E_stream42_eq_conj_E_rawStream42.symm
theorem uStreamFullOf_inv_mulVec_of_slot2AxisSum
    {uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (hStr : IsSlot2StreamUnitary uStream) (w : Fin 3) (γ : BitAssignment kFull80) (hInv : ∀ i
    : Fin 14, γ (rSum14Full w i) = if (slot2AxisSum w (fun q ↦ γ (rCoreFull q))).testBit i.val
    then 1 else 0) : ((uStreamFullOf uStream w)⁻¹).1.mulVec (basisKet γ) = basisKet
    (zeroSum14 w γ) := by
  let γ₀ := zeroSum14 w γ
  have hz₀ : ∀ i : Fin 14, γ₀ (rSum14Full w i) = 0 := fun i ↦
    ite_eq_left ((QRegister.mem_image (rSum14Full w) _).mpr ⟨i, rfl⟩)
  have hCore₀ : (fun q ↦ γ₀ (rCoreFull q)) = (fun q ↦ γ (rCoreFull q)) := core_zeroSum14 w γ
  obtain ⟨γ₁, hk₁, hout₁, hsum₁⟩ := hStr w γ₀ hz₀
  change (uStreamFullOf uStream w).1.mulVec (basisKet γ₀) = basisKet γ₁ at hk₁
  have hγ₁ : γ₁ = γ := by
    funext g
    by_cases hg : g ∈ (rSum14Full w).image
    · rcases (QRegister.mem_image _ _).mp hg with ⟨i, rfl⟩
      rw [hsum₁ i, hCore₀, hInv i]
    · rw [hout₁ g hg]
      dsimp only [γ₀, zeroSum14]
      exact ite_eq_right hg
  rw [hγ₁] at hk₁
  rw [← hk₁, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
    Matrix.one_mulVec]
end ConfigHoistInitStream1300And164
end HoistInitStream1300And164
end
end ModHoistInitStream1300And164

end QuantumComputation.Specs.StoppingPowerSolution
