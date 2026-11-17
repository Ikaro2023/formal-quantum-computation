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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.InterWalkSum42Hoist

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModJunctionPrefixPruned220
@[expose] public section
namespace JunctionPrefixPruned220
section ConfigJunctionPrefixPruned220
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
open ProjZ512QftAndTwist288 hiding
  basisBits_symm_apply fullSysCoreWires_eq_add zmod2_eq_zero_or_one
open FusedVepCore288
open JunctionApexCSA288 hiding
  HProjFlag HProjFlag_congr_S wfBitVal_of_HProjFlag HCoin0Flag dXor32_spec
  HSlot4Flag HSlot4Flag_congr_S dSlot4Axis count_dSlot4Axis_toff count_dSlot4Axis_t
  dSlot4Axis_spec dSlot4Axis_biSpec HPos01AndCoin0 dSlot4Conj count_dSlot4Conj_toff
  count_dSlot4Conj_t dSlot4Conj_spec
local instance (priority := 1000000) instNeZeroTwoPowJunctionPruned (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
abbrev mWork45 : ℕ := 45
lemma mw45_b2 : mWork45 = 45 := rfl
lemma CondStageSpec.peelWork {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload n : ℕ} (k : ℕ) (hk : k + 1 ≤ 45)
    (b₁ b₂ bOut : Bool) (v : Var)
    (c₁ c₂ : Wire n)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork)
    (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ rWork ⟨k, by have := mw45_b2; omega⟩)
    (h₂a : c₂ ≠ rWork ⟨k, by have := mw45_b2; omega⟩)
    (hc1Tot : c₁ ∉ (rWork.slice k (45 - k) (by have := mw45_b2; omega)).image)
    (hc2Tot : c₂ ∉ (rWork.slice k (45 - k) (by have := mw45_b2; omega)).image)
    (hc1S : c₁ ∈ (rHigh rCore).image ∪
      (rWork.slice 0 k (by have := mw45_b2; omega)).image)
    (hc2S : c₂ ∈ (rHigh rCore).image ∪
      (rWork.slice 0 k (by have := mw45_b2; omega)).image)
    {H_outer : BitAssignment n → Prop}
    (hH_anc : ∀ ξ₁ ξ₂ : BitAssignment n,
      (∀ w, w ≠ rWork ⟨k, by have := mw45_b2; omega⟩ → ξ₁ w = ξ₂ w) →
      H_outer ξ₁ → H_outer ξ₂)
    {H_inner : BitAssignment n → Prop}
    (hH_imp : ∀ η : BitAssignment n,
      H_outer η ∧
        η (rWork ⟨k, by have := mw45_b2; omega⟩) =
          genBoolBit b₁ b₂ bOut (η c₁) (η c₂) →
      H_inner η)
    {U : Unitary (2 ^ (fullSysCoreWires mPayload + 48))}
    {dInner : DynamicCircuit Var n}
    (hsInner : CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice (k + 1) (45 - (k + 1)) (by have := mw45_b2; omega))
      ((rHigh rCore).image ∪
        (rWork.slice 0 (k + 1) (by have := mw45_b2; omega)).image)
      H_inner U dInner) :
    CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice k (45 - k) (by have := mw45_b2; omega))
      ((rHigh rCore).image ∪
        (rWork.slice 0 k (by have := mw45_b2; omega)).image)
      H_outer U
      (dGenBoolWrap b₁ b₂ bOut v c₁ c₂
        (rWork ⟨k, by have := mw45_b2; omega⟩) h₁₂ h₁a h₂a dInner) := by
  have hMW : mWork45 = 45 := rfl
  let rTot := rWork.slice k (45 - k) (by omega)
  refine CondStageSpec.dGenBoolWrap b₁ b₂ bOut v c₁ c₂ (rWork ⟨k, by omega⟩) h₁₂ h₁a h₂a
    (rWork.slice (k + 1) (45 - (k + 1)) (by omega)) rTot
    (slice_sub_slice_b2 rWork (k + 1) (45 - (k + 1)) k (45 - k)
      (by omega) (by omega) (by omega) (by omega))
    (reg_mem_slice_b2 rWork k (45 - k) (by omega) ⟨k, by omega⟩ (by dsimp; omega) (by dsimp; omega))
    hc1Tot hc2Tot
    (reg_not_mem_slice_b2 rWork (k + 1) (45 - (k + 1)) (by omega) ⟨k, by omega⟩ (by dsimp; omega))
    ((disj_symm (QRegExt.disjointWires_concat_left hCW hPW)).apply_not_mem_right ⟨k, by omega⟩)
    hc1S hc2S (fun w hw ↦ ?_) hH_anc (hsInner.weaken_H hH_imp)
  rcases Finset.mem_union.mp hw with hSo | hWt
  · exact Finset.mem_union_left _ (Finset.union_subset_union_right
      (slice_sub_slice_b2 rWork 0 k 0 (k + 1) (by omega) (by omega) (by omega) (by omega)) hSo)
  · rcases (QRegister.mem_image rTot w).mp hWt with ⟨j, rfl⟩
    rw [slice_apply_eq]
    have := j.isLt
    by_cases hj0 : j.val = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (reg_mem_slice_b2 rWork 0 (k + 1) (by omega) ⟨k + j.val, by omega⟩
          (by dsimp; omega) (by dsimp; omega)))
    · exact Finset.mem_union_right _
        (reg_mem_slice_b2 rWork (k + 1) (45 - (k + 1)) (by omega) ⟨k + j.val, by omega⟩
          (by dsimp; omega) (by dsimp; omega))
def HProjFlag {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWork45 n) (ξ : BitAssignment n) : Prop :=
  ξ (rWork 6) = if vepHighNuc hm (fun q ↦ ξ (rCore q)) then 1 else 0
lemma HProjFlag_congr_S {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWork : QRegister mWork45 n)
    {S : Finset (Wire n)} (hHigh : (rHigh rCore).image ⊆ S) (hwf : rWork 6 ∈ S) : ∀ ξ₁ ξ₂ :
    BitAssignment n, (∀ w ∈ S, ξ₁ w = ξ₂ w) →
    (HProjFlag hm rCore rWork ξ₁ ↔ HProjFlag hm rCore rWork ξ₂) := by
  intro ξ₁ ξ₂ hEq
  unfold HProjFlag
  rw [hEq (rWork 6) hwf]
  have hv : vepHighNuc hm (fun q ↦ ξ₁ (rCore q)) = vepHighNuc hm (fun q ↦ ξ₂ (rCore q)) :=
    vepHighNuc_eq_of_high_eq hm fun q hq ↦ hEq (rCore q) (hHigh (rCore_mem_rHigh rCore q hq))
  rw [hv]
lemma wfBitVal_of_HProjFlag {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWork : QRegister mWork45 n)
    {ξ : BitAssignment n} (hH : HProjFlag hm rCore rWork ξ) : ((ξ (rWork 6)).val : ℤ) =
    wfBitVal hm (fun q ↦ ξ (rCore q)) := by
  unfold HProjFlag at hH
  unfold wfBitVal
  rw [hH]
  cases vepHighNuc hm (fun q ↦ ξ (rCore q)) <;> decide

lemma core_ne_workMem {mPayload n : ℕ} {rCore : QRegister (fullSysCoreWires mPayload) n}
    {rWork : QRegister mWork45 n} (hCW : rCore.DisjointWires rWork)
    {u v : Wire n} (hu : u ∈ rCore.image) (hv : v ∈ rWork.image) : u ≠ v :=
  fun h ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hu (h ▸ hv)

lemma cosetNeg_mem_core {mPayload n : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) :
    (if isInv then rCosetB1 hm rCore w else rCosetB0 hm rCore w) ∈ rCore.image := by
  cases isInv
  · exact rCosetB0_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  · exact rCosetB1_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)

lemma m6_mem_work {n : ℕ} (rWork : QRegister mWork45 n) (i : Fin 6) :
    ((rWork.slice 2 43 (by have := mw45_b2; omega)).slice 1 6 (by omega)) i ∈ rWork.image :=
  QRegister.image_compose_subset rWork _
    (QRegister.image_compose_subset _ _ ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩))

noncomputable def dSlot4Axis {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type}
    {n : ℕ} (v : Var) (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) : DynamicCircuit Var n :=
  let wb0 := rCosetB0 hm rCore w
  let wb1 := rCosetB1 hm rCore w
  let wNeg := if isInv then wb1 else wb0
  let rU6 := rElecSlotAxis rCore 0 w
  let rT4 := rPGTwist.slice 41 4 (by omega)
  let rW43 := rWork.slice 2 43 (by have := mw45_b2; omega)
  let rM6 := rW43.slice 1 6 (by omega)
  let hb1Core := cosetNeg_mem_core true hm rCore w
  let hNegCore := cosetNeg_mem_core isInv hm rCore w
  let hw430 : rW43 0 ∈ rWork.image :=
    QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW43 _).mpr ⟨0, rfl⟩)
  dXorAndWrap v (rWork 0) wb0 wb1 (rW43 0)
    (by
      have := w.isLt
      have := fullSysCoreWires_eq_3954_add mPayload
      dsimp only [wb0, wb1]
      unfold rCosetB0 rCosetB1
      simp only [slice_apply_eq]
      exact core_wire_ne rCore (by dsimp; omega))
    (core_ne_workMem hCW hb1Core ((QRegister.mem_image rWork _).mpr ⟨0, rfl⟩)).symm
    (fun h ↦ reg_not_mem_slice_b2 rWork 2 43 (by have := mw45_b2; omega) 0
      (by dsimp [mWork45]; omega) ((QRegister.mem_image rW43 _).mpr ⟨0, h.symm⟩))
    (core_ne_workMem hCW hb1Core hw430)
    (dMaskRegWrap 6 v (rW43 0) rU6 rM6
      (fun i ↦ (core_ne_workMem hCW
        (rElecSlotAxis_sub_rCore rCore 0 w ((QRegister.mem_image rU6 _).mpr ⟨i, rfl⟩)) hw430).symm)
      (fun i h ↦ reg_not_mem_slice_b2 rW43 1 6 (by omega) 0 (by dsimp; omega)
        ((QRegister.mem_image rM6 _).mpr ⟨i, h.symm⟩))
      ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW)
        (rElecSlotAxis_sub_rCore rCore 0 w)))
        (Finset.Subset.trans (QRegister.image_compose_subset rW43 _)
          (QRegister.image_compose_subset rWork _)))
      (.seq
        (.circuit (Circuit.S (rM6 5) ;;ᶜ cliffordCZ wNeg (rM6 5)
          (core_ne_workMem hCW hNegCore (m6_mem_work rWork 5)) ;;ᶜ
          (Circuit.S wNeg).inverse ;;ᶜ cApexXorT wNeg (rM6 4)))
        (dApexTAdderCtrlSign v wNeg (rM6.slice 0 4 (by omega)) rT4 (rW43.slice 7 4 (by omega))
          (fun i h ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCP) hNegCore
            (QRegister.image_compose_subset rPGTwist _
              ((QRegister.mem_image rT4 _).mpr ⟨i, h.symm⟩)))
          (disj_symm ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hPW)
            (QRegister.image_compose_subset rPGTwist _)))
            (Finset.Subset.trans (QRegister.image_compose_subset rM6 _)
              (Finset.Subset.trans (QRegister.image_compose_subset rW43 _)
                (QRegister.image_compose_subset rWork _)))))
          ((QRegExt.disjointWires_mono_left (slice_disjoint_of_le rW43 1 6 7 4 (by omega) (by omega)
            (by omega)))
            (QRegister.image_compose_subset rM6 _))
          ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hPW)
            (QRegister.image_compose_subset rPGTwist _)))
            (Finset.Subset.trans (QRegister.image_compose_subset rW43 _)
              (QRegister.image_compose_subset rWork _))))))
@[simp] lemma count_dSlot4Axis_toff {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4Axis isInv hm (Var := Var) v w rCore rPGTwist rWork hCP hCW hPW).count .TOFF = 0 := by
  unfold dSlot4Axis
  dsimp only
  rw [count_dXorAndWrap_toff, count_dMaskRegWrap_toff]
  refine dyn_seq_toff_zero ?_ (count_dApexTAdderCtrlSign_toff ..)
  simp only [DynamicCircuit.count, Circuit.count_seq, count_inverse_toff,
    count_cliffordCZ_toff, count_cApexXorT_toff]
  rfl
@[simp] lemma count_dSlot4Axis_t {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4Axis isInv hm (Var := Var) v w rCore rPGTwist rWork hCP hCW hPW).count .T = 46 := by
  have hNegCore := cosetNeg_mem_core isInv hm rCore w
  have hNeg4 := core_ne_workMem hCW hNegCore (m6_mem_work rWork 4)
  have hwNegC : (if isInv then rCosetB1 hm rCore w else rCosetB0 hm rCore w) ∉
      ((rWork.slice 2 43 (by have := mw45_b2; omega)).slice 7 4 (by omega)).image := fun hm_in ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _ (QRegister.image_compose_subset _ _ hm_in))
  unfold dSlot4Axis
  dsimp only
  rw [count_dXorAndWrap_t, count_dMaskRegWrap_t, count_dyn_seq,
    count_dApexTAdderCtrlSign_t _ _ _ _ _ _ hwNegC]
  dsimp only [DynamicCircuit.count]
  simp only [Circuit.count_seq, count_cliffordCZ_t, count_cApexXorT_t hNeg4]
  rfl
noncomputable def dSlot4Conj {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type}
    {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) : DynamicCircuit Var n :=
  have h10 : rWork 1 ≠ rWork 0 := fun h ↦ by
    have hv := congrArg Fin.val (rWork.wires.injective h); dsimp [mWork45] at hv; omega
  dPureConj (Circuit.CNOT (rWork 1) (rWork 0) h10)
    (dBiSeq isInv
      (dBiSeq isInv
        (dSlot4Axis isInv hm (Var := Var) v 0 rCore rPGTwist rWork hCP hCW hPW)
        (dSlot4Axis isInv hm (Var := Var) v 1 rCore rPGTwist rWork hCP hCW hPW))
      (dSlot4Axis isInv hm (Var := Var) v 2 rCore rPGTwist rWork hCP hCW hPW))
@[simp] lemma count_dSlot4Conj_toff {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4Conj isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW).count .TOFF = 0 := by
  unfold dSlot4Conj
  rw [count_dPureConj_toff _ (by simp [Circuit.CNOT])]
  exact count_dBiSeq_toff isInv (count_dBiSeq_toff isInv (count_dSlot4Axis_toff ..)
    (count_dSlot4Axis_toff ..)) (count_dSlot4Axis_toff ..)
@[simp] lemma count_dSlot4Conj_t {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4Conj isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW).count .T = 138 := by
  unfold dSlot4Conj
  rw [count_dPureConj_t _ (by simp [Circuit.CNOT])]
  simp only [count_dBiSeq_t, count_dSlot4Axis_t]
end ConfigJunctionPrefixPruned220
end JunctionPrefixPruned220
end
end ModJunctionPrefixPruned220

end QuantumComputation.Specs.StoppingPowerSolution
