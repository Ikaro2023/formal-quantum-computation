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

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section BoothOpt_06_Stream217ZeroSave0Width128
set_option maxRecDepth 200000

section
namespace BoothOpt_06_Stream217ZeroSave0Width128
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped BigOperators Matrix
open SpecsAux SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open InPlaceFullAddSlice
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open NuclearTwistRealizes (RealizesCleanPair)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open HybridStream288Aux HybridStream168Aux
section Impl
set_option maxRecDepth 200000
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowBoothOpt (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
/-!
## Section 1: `3906`-Wire Spectator Register (`rSpec217OfCore`), Parametric Step-1 XOR-8, &
Partition Lemmas
-/
theorem widenActivePair_of_eq {Var : Type} [Fintype Var] [DecidableEq Var] {k N m n : ℕ}
    [NeZero (2 ^ n)] {rSub : QRegister k n} {rAct : QRegister N n} {rWork : QRegister m n}
    {sel : QRegister k N} (h : rSub = rAct.compose sel) {u : Unitary (2 ^ k)}
    {d1 d2 : DynamicCircuit Var n} (hp : RealizesCleanPair rSub rWork u d1 d2) :
    RealizesCleanPair rAct rWork (sel.embedUnitary u) d1 d2 :=
  (h ▸ hp).widenActive
/-- 217-electron spectator momentum sum `∑ e : Fin 217, regVal (rElecSlotAxis _ e.succ w) γ`. -/
abbrev spectatorSum217 {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℕ :=
  ∑ e : Fin 217, regVal (rElecSlotAxis (QRegExt.idReg _) e.succ w) γ
theorem spectatorSum217_le_13671 {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    spectatorSum217 w γ ≤ 13671 ∧ spectatorSum217 w γ < 2 ^ 14 := by
  have hle : spectatorSum217 w γ ≤ ∑ _e : Fin 217, 63 := Finset.sum_le_sum fun e _ ↦
    Nat.le_pred_of_lt (regVal_lt_two_pow (rElecSlotAxis (QRegExt.idReg _) e.succ w) γ)
  rw [show (∑ _e : Fin 217, 63) = 13671 by decide] at hle
  exact ⟨hle, by omega⟩
/-- 14-bit slice `[14 * w .. 14 * w + 14)` inside `42`. -/
abbrev rSum14Slice42 (w : Fin 3) : QRegister 14 42 :=
  QRegister.block (14 * w.val) 14 (by have := w.isLt; omega)
/-- Register embedding `(rCore, rSum14(w))` inside `rCore ++ rSum42`
(`fullSysCoreWires mPayload + 42`). -/
abbrev selCoreSum14In42 (mPayload : ℕ) (w : Fin 3) :
    QRegister (fullSysCoreWires mPayload + 14) (fullSysCoreWires mPayload + 42) :=
  let kC := fullSysCoreWires mPayload
  let rC : QRegister kC (kC + 42) := QRegister.block 0 kC (by omega)
  let rS42 : QRegister 42 (kC + 42) := QRegister.block kC 42 le_rfl
  let rS14 : QRegister 14 (kC + 42) := rS42.compose (rSum14Slice42 w)
  let hCS14 : rC.DisjointWires rS14 :=
    (QRegister.block_disjoint_of_le 0 kC kC 42 (by omega) le_rfl (by omega)).compose_right _
  rC.concat rS14 hCS14
theorem compose_selCoreSum14In42 {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum42 : QRegister 42 n)
    (hCSum42 : rCore.DisjointWires rSum42) (w : Fin 3) : (rCore.concat rSum42 hCSum42).compose
    (selCoreSum14In42 mPayload w) = rCore.concat (rSum42.compose (rSum14Slice42 w))
    (hCSum42.compose_right (rSum14Slice42 w)) := by
  apply qreg_ext
  refine Fin.addCases (fun iC ↦ ?_) (fun j14 ↦ ?_)
  · simp only [QRegister.compose_apply, selCoreSum14In42, QRegister.concat_apply_left]
    exact (congrArg _ (Fin.ext (by simp))).trans (QRegister.concat_apply_left _ _ _ iC)
  · simp only [QRegister.compose_apply, selCoreSum14In42, QRegister.concat_apply_right]
    exact (congrArg _ (Fin.ext (by simp))).trans (QRegister.concat_apply_right _ _ _ _)
theorem coreWires_ge_3924 (mPayload : ℕ) : 18 + 3906 ≤ fullSysCoreWires mPayload := by
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
  omega
/-- The `3906`-wire (`217 × 18`) spectator-electron register `rCore.slice 18 3906 _` holding
electrons `1..217` (`e.succ` for `e : Fin 217`), disjoint from Electron `0` (`rCore.slice 0 18`). -/
def rSpec217OfCore {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    QRegister 3906 n := rCore.slice 18 3906 (coreWires_ge_3924 mPayload)
theorem disj_rSpec217OfCore_left {mPayload k n : ℕ}
    {rCore : QRegister (fullSysCoreWires mPayload) n} {rOther : QRegister k n}
    (hCO : rCore.DisjointWires rOther) : (rSpec217OfCore rCore).DisjointWires rOther :=
  QRegExt.disjointWires_mono_left hCO (QRegister.image_compose_subset rCore _)
/-- Wire index `18 * e + 6 * w + r` inside the `3906`-wire spectator register (`e : Fin 217`). -/
def spec217ElecAxisBitWire (w : Fin 3) (r : Fin 6) (e : Fin 217) : Wire 3906 :=
  ⟨18 * e.val + 6 * w.val + r.val, by have := e.isLt; have := w.isLt; have := r.isLt; omega⟩
theorem rSpec217OfCore_spec217ElecAxisBitWire {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) (r : Fin 6) (e : Fin 217) :
    rSpec217OfCore rCore (spec217ElecAxisBitWire w r e) = rCore
    (rElecSlotAxis (QRegExt.idReg _) e.succ w r) :=
  congrArg rCore.wires (Fin.ext (by
    dsimp [rSpec217OfCore, spec217ElecAxisBitWire, rElecSlotAxis, QRegister.slice,
      qreg_block_apply, QRegExt.idReg]
    simp only [Function.Embedding.refl_apply]
    omega))
/-- 217-electron momentum sum along axis `w` evaluated directly on `BitAssignment 3906`. -/
def spec217AxisSum (w : Fin 3) (γ : BitAssignment 3906) : ℕ :=
  ∑ e : Fin 217, ∑ r : Fin 6, (γ (spec217ElecAxisBitWire w r e)).val * 2 ^ r.val
theorem spec217AxisSum_eq_bitPlane_sum (w : Fin 3) (γ : BitAssignment 3906) : spec217AxisSum w
    γ = ∑ r : Fin 6, 2 ^ r.val * ∑ e : Fin 217, (γ (spec217ElecAxisBitWire w r e)).val := by
  simp_rw [spec217AxisSum, mul_comm (_ : ℕ) (2 ^ _)]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ (Finset.mul_sum _ _ _).symm
theorem spec217AxisSum_rSpec217OfCore_eq_spectatorSum217 {mPayload n : ℕ} (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (β : BitAssignment n) : spec217AxisSum
    w (fun q ↦ β (rSpec217OfCore rCore q)) = spectatorSum217 w (fun q ↦ β (rCore q)) := by
  simp only [spec217AxisSum, spectatorSum217, regVal,
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal,
    rSpec217OfCore_spec217ElecAxisBitWire]
/-- Generalized 3-plane chunk wire map directly into `Wire 3906` (`217` spectator electrons). -/
def spec217ThreePlaneChunkWire (w : Fin 3) (pBase : ℕ) (eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ : ℕ)
    (hp : pBase + 3 ≤ 6) (he₀ : eOff₀ + B₀ ≤ 217) (he₁ : eOff₁ + B₁ ≤ 217)
    (he₂ : eOff₂ + B₂ ≤ 217) (u : Fin (B₀ + B₁ + B₂)) : Wire 3906 :=
  if _h1 : u.val < B₀ then
    spec217ElecAxisBitWire w ⟨pBase, by omega⟩ ⟨eOff₀ + u.val, by omega⟩
  else if _h2 : u.val < B₀ + B₁ then
    spec217ElecAxisBitWire w ⟨pBase + 1, by omega⟩ ⟨eOff₁ + (u.val - B₀), by omega⟩
  else
    spec217ElecAxisBitWire w ⟨pBase + 2, by omega⟩ ⟨eOff₂ + (u.val - (B₀ + B₁)), by omega⟩
theorem weightedGenBatchVal_spec217Chunk (w : Fin 3) (pBase : ℕ)
    (eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ : ℕ) (hp : pBase + 3 ≤ 6)
    (he₀ : eOff₀ + B₀ ≤ 217) (he₁ : eOff₁ + B₁ ≤ 217) (he₂ : eOff₂ + B₂ ≤ 217)
    (γ : BitAssignment 3906) :
    weightedGenBatchVal
        (spec217ThreePlaneChunkWire w pBase eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ hp he₀ he₁ he₂) γ =
      (∑ i : Fin B₀, (γ (spec217ElecAxisBitWire w ⟨pBase, by omega⟩ ⟨eOff₀ + i.val,
        by omega⟩)).val) +
      (∑ i : Fin B₁, 2 * (γ (spec217ElecAxisBitWire w ⟨pBase + 1, by omega⟩ ⟨eOff₁ + i.val,
        by omega⟩)).val) +
      (∑ i : Fin B₂, 4 * (γ (spec217ElecAxisBitWire w ⟨pBase + 2, by omega⟩ ⟨eOff₂ + i.val,
        by omega⟩)).val) := by
  unfold weightedGenBatchVal spec217ThreePlaneChunkWire
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
    (Finset.sum_congr rfl fun i _ ↦ ?_)) (Finset.sum_congr rfl fun i _ ↦ ?_)
  · dsimp only
    split_ifs <;> first | rfl | omega
  · have hi := i.isLt
    dsimp only
    split_ifs <;> first | omega | exact congrArg (fun q ↦ 2 * (γ q).val) (congrArg _ (Fin.ext (by
      dsimp
      omega)))
  · have hi := i.isLt
    dsimp only
    split_ifs <;> first | omega | exact congrArg (fun q ↦ 4 * (γ q).val) (congrArg _ (Fin.ext (by
      dsimp
      omega)))
/-- Selector embedding `(rSpec217, rSum14)` (`3906 + 14` wires) inside `rCore ++ rSum14`
(`fullSysCoreWires mPayload + 14` wires), skipping Electron `0` (`wires 0..17`). -/
def selSpec217InCoreSum14 (mPayload : ℕ) :
    QRegister (3906 + 14) (fullSysCoreWires mPayload + 14) :=
  let kC := fullSysCoreWires mPayload
  let rC : QRegister kC (kC + 14) := QRegister.block 0 kC (by omega)
  let rS14 : QRegister 14 (kC + 14) := QRegister.block kC 14 le_rfl
  let rSpec : QRegister 3906 (kC + 14) := rC.slice 18 3906 (coreWires_ge_3924 mPayload)
  let hSpecS14 : rSpec.DisjointWires rS14 := QRegExt.disjointWires_mono_left
      (QRegister.block_disjoint_of_le 0 kC kC 14 (by omega) le_rfl (by omega))
      (QRegister.image_compose_subset rC _)
  rSpec.concat rS14 hSpecS14
theorem compose_selSpec217InCoreSum14 {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) : (rCore.concat rSum14 hCSum).compose
    (selSpec217InCoreSum14 mPayload) = (rSpec217OfCore rCore).concat rSum14
    (disj_rSpec217OfCore_left hCSum) := by
  apply qreg_ext
  refine Fin.addCases (fun iS ↦ ?_) (fun j14 ↦ ?_)
  · simp only [QRegister.compose_apply, selSpec217InCoreSum14, QRegister.concat_apply_left,
      rSpec217OfCore, QRegister.slice]
    exact (congrArg _ (Fin.ext (by
      dsimp [QRegister.slice, qreg_block_apply]
      exact Nat.zero_add _))).trans (QRegister.concat_apply_left _ _ _ _)
  · simp only [QRegister.compose_apply, selSpec217InCoreSum14, QRegister.concat_apply_right]
    exact (congrArg _ (Fin.ext (by dsimp [qreg_block_apply]))).trans
      (QRegister.concat_apply_right _ _ _ _)
theorem rSum14Slice42_disjoint_of_ne {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂) :
    (rSum14Slice42 w₁).DisjointWires (rSum14Slice42 w₂) :=
  QRegister.disjoint_iff.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij ↦ by
    have hv := congrArg Fin.val hij
    have hw : w₁.val < 3 ∧ w₂.val < 3 ∧ w₁.val ≠ w₂.val := ⟨w₁.isLt, w₂.isLt, mt Fin.ext hne⟩
    simp only [rSum14Slice42, qreg_block_apply] at hv
    omega
theorem uThreeAxis217_compute_ket_of_oneAxis {mPayload n : ℕ} [NeZero (2 ^ n)]
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum42 : QRegister 42 n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (uAx : Fin 3 → Unitary (2 ^ (fullSysCoreWires mPayload + 14)))
    (hAx : ∀ (w : Fin 3) (rSum14 : QRegister 14 n) (hCSum : rCore.DisjointWires rSum14),
      ∀ β₀ : Fin n → ZMod 2, (∀ i : Fin 14, β₀ (rSum14 i) = 0) →
        ∃ β : Fin n → ZMod 2,
          ((rCore.concat rSum14 hCSum).embedUnitary (uAx w)).1.mulVec (basisKet β₀) = basisKet β ∧
          (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧
          (∀ i : Fin 14,
            β (rSum14 i) = if (spectatorSum217 w (fun q ↦
              β₀ (rCore q))).testBit i.val then 1 else 0)) :
    let u3 : Unitary (2 ^ (fullSysCoreWires mPayload + 42)) := ((selCoreSum14In42 mPayload
        2).embedUnitary (uAx 2) * (selCoreSum14In42 mPayload 1).embedUnitary (uAx 1)) *
        (selCoreSum14In42 mPayload 0).embedUnitary (uAx 0)
    ∀ β₀ : Fin n → ZMod 2, (∀ j : Fin 42, β₀ (rSum42 j) = 0) →
      ∃ β : Fin n → ZMod 2,
        ((rCore.concat rSum42 hCSum42).embedUnitary u3).1.mulVec (basisKet β₀) = basisKet β ∧
        (∀ g : Fin n, g ∉ rSum42.image → β g = β₀ g) ∧
        (∀ w : Fin 3, ∀ i : Fin 14,
          β ((rSum42.compose (rSum14Slice42 w)) i) =
            if (spectatorSum217 w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0) := by
  intro u3 β₀ hz42
  let rS (w : Fin 3) := rSum42.compose (rSum14Slice42 w)
  have hSub (w : Fin 3) : (rS w).image ⊆ rSum42.image := QRegister.image_compose_subset rSum42 _
  have hDisjS {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂) : (rS w₁).DisjointWires (rS w₂) :=
    QRegister.disjoint_iff.mpr fun i j hij ↦
      (rSum14Slice42_disjoint_of_ne hne).ne i j (rSum42.wires.injective hij)
  have hMat (w : Fin 3) :
      ((rCore.concat rSum42 hCSum42).embedUnitary ((selCoreSum14In42 mPayload w).embedUnitary (uAx
        w))).1 =
        ((rCore.concat (rS w) (hCSum42.compose_right (rSum14Slice42 w))).embedUnitary (uAx w)).1 :=
          by
    simp only [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      compose_selCoreSum14In42, rS]
  obtain ⟨β₁, hk₁, ho₁, hb₁⟩ := hAx 0 (rS 0) (hCSum42.compose_right _) β₀ (fun _ ↦ hz42 _)
  obtain ⟨β₂, hk₂, ho₂, hb₂⟩ := hAx 1 (rS 1) (hCSum42.compose_right _) β₁ fun i ↦ by
    rw [ho₁ _ ((hDisjS (by decide : (1 : Fin 3) ≠ 0)).apply_not_mem_right i)]
    exact hz42 _
  obtain ⟨β₃, hk₃, ho₃, hb₃⟩ := hAx 2 (rS 2) (hCSum42.compose_right _) β₂ fun i ↦ by
    rw [ho₂ _ ((hDisjS (by decide : (2 : Fin 3) ≠ 1)).apply_not_mem_right i),
      ho₁ _ ((hDisjS (by decide : (2 : Fin 3) ≠ 0)).apply_not_mem_right i)]
    exact hz42 _
  have hCore₁ : (fun q ↦ β₁ (rCore q)) = (fun q ↦ β₀ (rCore q)) :=
    funext fun q ↦ ho₁ _ ((hCSum42.compose_right _).apply_not_mem_right q)
  have hCore₂ : (fun q ↦ β₂ (rCore q)) = (fun q ↦ β₀ (rCore q)) := funext fun q ↦
      (ho₂ _ ((hCSum42.compose_right _).apply_not_mem_right q)).trans (congrFun hCore₁ q)
  refine ⟨β₃, ?_, fun g hg ↦ ?_, fun w i ↦ ?_⟩
  · simp only [u3, QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      hMat 0, hMat 1, hMat 2]
    rw [hk₁, hk₂, hk₃]
  · rw [ho₃ g (fun m ↦ hg (hSub 2 m)), ho₂ g (fun m ↦ hg (hSub 1 m)), ho₁ g (fun m ↦ hg (hSub 0 m))]
  · rcases (by decide : ∀ w : Fin 3, w = 0 ∨ w = 1 ∨ w = 2) w with rfl | rfl | rfl
    · simpa only [rS, ho₃ _ ((hDisjS (by decide : (0 : Fin 3) ≠ 2)).apply_not_mem_right i),
        ho₂ _ ((hDisjS (by decide : (0 : Fin 3) ≠ 1)).apply_not_mem_right i)] using hb₁ i
    · simpa only [rS, ho₃ _ ((hDisjS (by decide : (1 : Fin 3) ≠ 2)).apply_not_mem_right i),
        hCore₁] using hb₂ i
    · simpa only [rS, hCore₂] using hb₃ i
theorem sum_fin217_split5 (a b c d e ab abc abcd : ℕ)
    (hab : a + b = ab) (habc : ab + c = abc) (habcd : abc + d = abcd) (h : abcd + e = 217)
    (f : Fin 217 → ℕ) :
    (∑ i : Fin a, f ⟨0 + i.val, by omega⟩) +
      (∑ i : Fin b, f ⟨a + i.val, by omega⟩) +
      (∑ i : Fin c, f ⟨ab + i.val, by omega⟩) +
      (∑ i : Fin d, f ⟨abc + i.val, by omega⟩) +
      (∑ i : Fin e, f ⟨abcd + i.val, by omega⟩) =
      ∑ k : Fin 217, f k := by
  subst hab; subst habc; subst habcd
  let eqv : Fin ((((a + b) + c) + d) + e) ≃ Fin 217 := finCongr h
  rw [← Equiv.sum_comp eqv, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· +
    ·) ?_ ?_) ?_) ?_) ?_
  all_goals refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [eqv]))
/-- 3-plane chunk wire abbreviation on `Wire 3906` with default `decide` bounds. -/
abbrev chunk217 (w : Fin 3) (p e₀ B₀ e₁ B₁ e₂ B₂ : ℕ)
    (hp : p + 3 ≤ 6 := by decide) (h₀ : e₀ + B₀ ≤ 217 := by decide)
    (h₁ : e₁ + B₁ ≤ 217 := by decide) (h₂ : e₂ + B₂ ≤ 217 := by decide) :
    Fin (B₀ + B₁ + B₂) → Wire 3906 :=
  spec217ThreePlaneChunkWire w p e₀ B₀ e₁ B₁ e₂ B₂ hp h₀ h₁ h₂
theorem hybrid131Batch_eq_spec217AxisSum (w : Fin 3) (γ : BitAssignment 3906) :
    (((((((((weightedGenBatchVal (chunk217 w 0 0 17 0 119 0 0) γ +
      2 ^ 0 * weightedGenBatchVal (chunk217 w 0 17 66 119 31 0 32) γ) +
      2 ^ 0 * weightedGenBatchVal (chunk217 w 0 83 66 150 31 32 32) γ) +
      2 ^ 0 * weightedGenBatchVal (chunk217 w 0 149 66 181 31 64 32) γ) +
      2 ^ 0 * weightedGenBatchVal (chunk217 w 0 215 2 212 5 96 121) γ) +
      2 ^ 3 * weightedGenBatchVal (chunk217 w 3 0 42 0 71 0 18) γ) +
      2 ^ 3 * weightedGenBatchVal (chunk217 w 3 42 42 71 71 18 18) γ) +
      2 ^ 3 * weightedGenBatchVal (chunk217 w 3 84 42 142 71 36 18) γ) +
      2 ^ 3 * weightedGenBatchVal (chunk217 w 3 126 86 213 3 54 41) γ) +
      2 ^ 3 * weightedGenBatchVal (chunk217 w 3 212 5 216 1 95 122) γ) =
      spec217AxisSum w γ := by
  dsimp only [chunk217]
  simp only [Nat.pow_zero, one_mul, weightedGenBatchVal_spec217Chunk]
  let p (r : Fin 6) (c : ℕ) : Fin 217 → ℕ :=
    fun e ↦ c * (γ (spec217ElecAxisBitWire w r e)).val
  have hp := sum_fin217_split5
  trans ((∑ e, p 0 1 e) + (∑ e, p 1 2 e) + (∑ e, p 2 4 e)) +
      8 * ((∑ e, p 3 1 e) + (∑ e, p 4 2 e) + (∑ e, p 5 4 e))
  · rw [← hp 17 66 66 66 2 83 149 215 rfl rfl rfl rfl (p 0 1),
      ← hp 119 31 31 31 5 150 181 212 rfl rfl rfl rfl (p 1 2),
      ← hp 0 32 32 32 121 32 64 96 rfl rfl rfl rfl (p 2 4),
      ← hp 42 42 42 86 5 84 126 212 rfl rfl rfl rfl (p 3 1),
      ← hp 71 71 71 3 1 142 213 216 rfl rfl rfl rfl (p 4 2),
      ← hp 18 18 18 41 122 36 54 95 rfl rfl rfl rfl (p 5 4)]
    dsimp only [p]
    simp only [one_mul, show ∀ h, (⟨0, h⟩ : Fin 6) = 0 from fun _ ↦ rfl,
      show ∀ h, (⟨0 + 1, h⟩ : Fin 6) = 1 from fun _ ↦ rfl,
      show ∀ h, (⟨0 + 2, h⟩ : Fin 6) = 2 from fun _ ↦ rfl,
      show ∀ h, (⟨3, h⟩ : Fin 6) = 3 from fun _ ↦ rfl,
      show ∀ h, (⟨3 + 1, h⟩ : Fin 6) = 4 from fun _ ↦ rfl,
      show ∀ h, (⟨3 + 2, h⟩ : Fin 6) = 5 from fun _ ↦ rfl]
    ring
  · rw [spec217AxisSum_eq_bitPlane_sum w γ, Fin.sum_univ_six]
    dsimp only [p]
    simp only [one_mul, ← Finset.mul_sum, Fin.val_zero, Fin.val_one,
      show (2 : Fin 6).val = 2 from rfl, show (3 : Fin 6).val = 3 from rfl,
      show (4 : Fin 6).val = 4 from rfl, show (5 : Fin 6).val = 5 from rfl]
    ring
/-- Ideal unitary on `2 ^ (3906 + 14)` realized by `dStream217SpecAdd131` (`131w`). -/
noncomputable def uStream217Spec131 (w : Fin 3) : Unitary (2 ^ (3906 + 14)) :=
  let w1 := chunk217 w 0 0 17 0 119 0 0
  let w2 := chunk217 w 0 17 66 119 31 0 32
  let w3 := chunk217 w 0 83 66 150 31 32 32
  let w4 := chunk217 w 0 149 66 181 31 64 32
  let w5 := chunk217 w 0 215 2 212 5 96 121
  let w6 := chunk217 w 3 0 42 0 71 0 18
  let w7 := chunk217 w 3 42 42 71 71 18 18
  let w8 := chunk217 w 3 84 42 142 71 36 18
  let w9 := chunk217 w 3 126 86 213 3 54 41
  let w10 := chunk217 w 3 212 5 216 1 95 122
  ((selCoreSlice 3906 3 11 (by decide)).embedUnitary (catModAddUnitary 3906 11 (weightedGenBatchVal
    w10)) *
    ((selCoreSlice 3906 3 11 (by decide)).embedUnitary (catModAddUnitary 3906 11
      (weightedGenBatchVal w9)) *
    ((selCoreSlice 3906 3 10 (by decide)).embedUnitary (catModAddUnitary 3906 10
      (weightedGenBatchVal w8)) *
    ((selCoreSlice 3906 3 10 (by decide)).embedUnitary (catModAddUnitary 3906 10
      (weightedGenBatchVal w7)) *
    ((selCoreSlice 3906 3 9 (by decide)).embedUnitary (catModAddUnitary 3906 9 (weightedGenBatchVal
      w6)) *
    ((selCoreSlice 3906 0 11 (by decide)).embedUnitary (catModAddUnitary 3906 11
      (weightedGenBatchVal w5)) *
    ((selCoreSlice 3906 0 10 (by decide)).embedUnitary (catModAddUnitary 3906 10
      (weightedGenBatchVal w4)) *
    ((selCoreSlice 3906 0 10 (by decide)).embedUnitary (catModAddUnitary 3906 10
      (weightedGenBatchVal w3)) *
    ((selCoreSlice 3906 0 9 (by decide)).embedUnitary (catModAddUnitary 3906 9 (weightedGenBatchVal
      w2)) *
    (selCoreSlice 3906 0 8 (by decide)).embedUnitary (uBitXor 3906 8 (weightedGenBatchVal
      w1)))))))))))
theorem uStream217Spec131_compute_ket {n : ℕ} [NeZero (2 ^ n)] (w : Fin 3)
    (rSpec : QRegister 3906 n) (rSum14 : QRegister 14 n)
    (hSpecSum : rSpec.DisjointWires rSum14) : ∀ β₀ : Fin n → ZMod 2,
    (∀ i : Fin 14, β₀ (rSum14 i) = 0) → ∃ β : Fin n → ZMod 2, ((rSpec.concat rSum14
    hSpecSum).embedUnitary (uStream217Spec131 w)).1.mulVec (basisKet β₀) = basisKet β ∧
    (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧ (∀ i : Fin 14, β (rSum14 i) = if
    (spec217AxisSum w (fun q ↦ β₀ (rSpec q))).testBit i.val then 1 else 0) := by
  intro β₀ hz
  let w1 := chunk217 w 0 0 17 0 119 0 0
  let w2 := chunk217 w 0 17 66 119 31 0 32
  let w3 := chunk217 w 0 83 66 150 31 32 32
  let w4 := chunk217 w 0 149 66 181 31 64 32
  let w5 := chunk217 w 0 215 2 212 5 96 121
  let w6 := chunk217 w 3 0 42 0 71 0 18
  let w7 := chunk217 w 3 42 42 71 71 18 18
  let w8 := chunk217 w 3 84 42 142 71 36 18
  let w9 := chunk217 w 3 126 86 213 3 54 41
  let w10 := chunk217 w 3 212 5 216 1 95 122
  let γ₀ : BitAssignment 3906 := fun q ↦ β₀ (rSpec q)
  have ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ :
      weightedGenBatchVal w1 γ₀ ≤ 255 ∧ weightedGenBatchVal w2 γ₀ ≤ 256 ∧
      weightedGenBatchVal w3 γ₀ ≤ 256 ∧ weightedGenBatchVal w4 γ₀ ≤ 256 ∧
      weightedGenBatchVal w5 γ₀ ≤ 496 ∧ weightedGenBatchVal w6 γ₀ ≤ 256 ∧
      weightedGenBatchVal w7 γ₀ ≤ 256 ∧ weightedGenBatchVal w8 γ₀ ≤ 256 ∧
      weightedGenBatchVal w9 γ₀ ≤ 256 ∧ weightedGenBatchVal w10 γ₀ ≤ 495 :=
    ⟨weightedGenBatchVal_le w1 γ₀, weightedGenBatchVal_le w2 γ₀, weightedGenBatchVal_le w3 γ₀,
      weightedGenBatchVal_le w4 γ₀, weightedGenBatchVal_le w5 γ₀, weightedGenBatchVal_le w6 γ₀,
      weightedGenBatchVal_le w7 γ₀, weightedGenBatchVal_le w8 γ₀, weightedGenBatchVal_le w9 γ₀,
      weightedGenBatchVal_le w10 γ₀⟩
  dsimp only [γ₀] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10
  obtain ⟨b1, hket1, hInv1⟩ := accInvar_step1_bitXor8 rSpec rSum14 hSpecSum (weightedGenBatchVal w1)
    β₀ (accInvar_zero rSum14 β₀ hz) (by omega)
  obtain ⟨b2, hket2, hInv2⟩ := accInvar_step_sliceModAdd rSpec rSum14 hSpecSum 0 9 (by decide)
    (weightedGenBatchVal w2) _ β₀ b1 hInv1 (by omega) (by omega)
  obtain ⟨b3, hket3, hInv3⟩ := accInvar_step_sliceModAdd rSpec rSum14 hSpecSum 0 10 (by decide)
    (weightedGenBatchVal w3) _ β₀ b2 hInv2 (by omega) (by omega)
  obtain ⟨b4, hket4, hInv4⟩ := accInvar_step_sliceModAdd rSpec rSum14 hSpecSum 0 10 (by decide)
    (weightedGenBatchVal w4) _ β₀ b3 hInv3 (by omega) (by omega)
  obtain ⟨b5, hket5, hInv5⟩ := accInvar_step_sliceModAdd rSpec rSum14 hSpecSum 0 11 (by decide)
    (weightedGenBatchVal w5) _ β₀ b4 hInv4 (by omega) (by omega)
  obtain ⟨b6, hket6, hInv6⟩ := accInvar_step_sliceModAdd rSpec rSum14 hSpecSum 3 9 (by decide)
    (weightedGenBatchVal w6) _ β₀ b5 hInv5 (by omega) (by omega)
  obtain ⟨b7, hket7, hInv7⟩ := accInvar_step_sliceModAdd rSpec rSum14 hSpecSum 3 10 (by decide)
    (weightedGenBatchVal w7) _ β₀ b6 hInv6 (by omega) (by omega)
  obtain ⟨b8, hket8, hInv8⟩ := accInvar_step_sliceModAdd rSpec rSum14 hSpecSum 3 10 (by decide)
    (weightedGenBatchVal w8) _ β₀ b7 hInv7 (by omega) (by omega)
  obtain ⟨b9, hket9, hInv9⟩ := accInvar_step_sliceModAdd rSpec rSum14 hSpecSum 3 11 (by decide)
    (weightedGenBatchVal w9) _ β₀ b8 hInv8 (by omega) (by omega)
  obtain ⟨b10, hket10, hInv10⟩ := accInvar_step_sliceModAdd rSpec rSum14 hSpecSum 3 11 (by decide)
    (weightedGenBatchVal w10) _ β₀ b9 hInv9 (by omega) (by omega)
  rw [hybrid131Batch_eq_spec217AxisSum w (fun q ↦ β₀ (rSpec q))] at hInv10
  refine ⟨b10, ?_, hInv10.1, hInv10.2⟩
  simp only [uStream217Spec131, QRegister.embedUnitary_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  rw [hket1, hket2, hket3, hket4, hket5, hket6, hket7, hket8, hket9, hket10]
attribute [irreducible] uStream217Spec131
theorem uStream217Spec131_slice_compute_ket {mPayload n : ℕ} [NeZero (2 ^ n)]
    (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) :
    let hSpecSum := disj_rSpec217OfCore_left hCSum
    ∀ β₀ : Fin n → ZMod 2, (∀ i : Fin 14, β₀ (rSum14 i) = 0) →
      ∃ β : Fin n → ZMod 2,
        (((rSpec217OfCore rCore).concat rSum14 hSpecSum).embedUnitary (uStream217Spec131
          w)).1.mulVec
          (basisKet β₀) = basisKet β ∧
        (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧
        (∀ i : Fin 14,
          β (rSum14 i) = if (spectatorSum217 w (fun q ↦
            β₀ (rCore q))).testBit i.val then 1 else 0) := by
  intro hSpecSum β₀ hz
  obtain ⟨β, hket, hout, hbits⟩ :=
    uStream217Spec131_compute_ket w (rSpec217OfCore rCore) rSum14 hSpecSum β₀ hz
  rw [spec217AxisSum_rSpec217OfCore_eq_spectatorSum217 w rCore β₀] at hbits
  exact ⟨β, hket, hout, hbits⟩
end Impl
end BoothOpt_06_Stream217ZeroSave0Width128
end
end BoothOpt_06_Stream217ZeroSave0Width128

end QuantumComputation.Specs.StoppingPowerSolution
end
