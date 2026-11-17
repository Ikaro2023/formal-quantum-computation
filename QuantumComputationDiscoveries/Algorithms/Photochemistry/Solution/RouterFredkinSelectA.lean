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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SplitRouterNuc47Elec187
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option allowUnsafeReducibility true
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open DynamicCircuit QuantumComputation.Specs PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectOracles
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local semireducible] ComputeProgWires
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
abbrev Assign4 := BitAssignment dLayout
theorem s5k_ax (β₄ : Assign4) (h0 : β₄ wKinAxis0 = 0) (h1 : β₄ wKinAxis1 = 0)
    (hC : β₄ wIsFineCopy = 0) (hE : β₄ wIsElecKin = 0) :
    TargetsIn (fun w ↦ 6056 ≤ w.val ∧ w.val < 6083) pKinAlign0 ∧
    pKinAlign0.fwdBits β₄ wKinAxis0 = β₄ wAxis0 ∧ pKinAlign0.fwdBits β₄ wKinAxis1 = β₄ wAxis1 ∧
    pKinAlign0.fwdBits β₄ wIsFineCopy = β₄ wIsFine ∧ pKinAlign0.fwdBits β₄ wIsElecKin =
        β₄ wHasE1 := by
  have iAl {a : ℕ} {ha} (hk : 6056 ≤ 5947 + a ∧ 5947 + a < 6083 := by decide) :
      6056 ≤ (rAlignLayout ⟨a, ha⟩).val ∧ (rAlignLayout ⟨a, ha⟩).val < 6083 :=
    val_rAlignLayout ⟨a, ha⟩ ▸ hk
  have ne {a c : ℕ} {ha hc} (h : a ≠ c := by
    decide) : rAlignLayout ⟨a, ha⟩ ≠ rAlignLayout ⟨c, hc⟩ := align_ne_align h
  have oNe {a c} := out_ne_align a c
  refine ⟨⟨iAl, iAl, iAl, iAl⟩, ?_, ?_, ?_, ?_⟩ <;> dsimp only [pKinAlign0, ComputeProg.fwdBits]
  · rw [Function.update_of_ne ne, Function.update_of_ne ne, Function.update_of_ne ne,
        Function.update_self, h0, zero_add]
  · rw [Function.update_of_ne ne, Function.update_of_ne ne, Function.update_self,
      Function.update_of_ne ne, Function.update_of_ne oNe, h1, zero_add]
  · rw [Function.update_of_ne ne, Function.update_self, Function.update_of_ne ne,
      Function.update_of_ne ne, Function.update_of_ne oNe, Function.update_of_ne oNe, hC, zero_add]
  · rw [Function.update_self, Function.update_of_ne ne, Function.update_of_ne ne,
        Function.update_of_ne ne,
      Function.update_of_ne oNe, Function.update_of_ne oNe, Function.update_of_ne oNe, hE, zero_add]
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA

namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.SplitRouter47_187
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
/-- First-port classical swap update on `r : RouterReg M D n`. -/
def routerLoBits {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) : BitAssignment n :=
  if h1 : β (rHas1 r) = 1 ∧ routerIdxMinVal r β < M then
    swapVecBits 24 (rBufLo r) (fun b ↦ rSys r ⟨routerIdxMinVal r β, h1.2⟩ b) β
  else β
/-- Two-port classical swap update on `r : RouterReg M D n` matching `uRouterSwapConj r`. -/
def routerSwapBits {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) : BitAssignment n :=
  if h2 : routerHas2Eff r β = 1 ∧ routerIdxMaxVal r β < M then
    swapVecBits 24 (rBufHi r) (fun b ↦ rSys r ⟨routerIdxMaxVal r β, h2.2⟩ b) (routerLoBits r β)
  else routerLoBits r β

theorem routerMinMax_of_valid {M D n : ℕ} {r : RouterReg M D n} {β : BitAssignment n}
    (hβ : ValidRouterInput r β) :
    (β (rHas1 r) = 1 → routerIdxMinVal r β < M) ∧
    (routerHas2Eff r β = 1 → β (rHas1 r) = 1 ∧ routerIdxMinVal r β < M ∧ routerIdxMaxVal r β < M ∧
      routerIdxMinVal r β ≠ routerIdxMaxVal r β ∧
      ((routerIdxMinVal r β = idxValD (rIdx1 r) β ∧ routerIdxMaxVal r β = idxValD (rIdx2 r) β) ∨
       (routerIdxMinVal r β = idxValD (rIdx2 r) β ∧ routerIdxMaxVal r β = idxValD (rIdx1 r) β)))
           := by
  have hraw (he : routerHas2Eff r β = 1) :
      β (rRawHas2 r) = 1 ∧ idxValD (rIdx1 r) β ≠ idxValD (rIdx2 r) β := by
    unfold routerHas2Eff at he
    split_ifs at he with hr
    · exact hr
    · exact absurd he zero_ne_one
  refine ⟨fun hh1 ↦ ?_, fun hh2 ↦ ?_⟩
  · unfold routerIdxMinVal
    split_ifs with hc
    · exact hβ.2.2.1 (hraw hc.1).1
    · exact hβ.2.1 hh1
  · obtain ⟨hr1, hne⟩ := hraw hh2
    unfold routerIdxMinVal routerIdxMaxVal
    split_ifs with hlt
    · exact ⟨hβ.1 hr1, hβ.2.2.1 hr1, hβ.2.1 (hβ.1 hr1), hlt.2.ne, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨hβ.1 hr1, hβ.2.1 (hβ.1 hr1), hβ.2.2.1 hr1, hne, Or.inl ⟨rfl, rfl⟩⟩

theorem uRouterSwapConj_ket_eq {M D n : ℕ} (r : RouterReg M D n) {β : BitAssignment n}
    (hβ : ValidRouterInput r β) :
    have : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
    (uRouterSwapConj r).1.mulVec (ket β) = ket (routerSwapBits r β) := by
  have : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  obtain ⟨hMinLt, hMaxSpec⟩ := routerMinMax_of_valid hβ
  rw [uRouterSwapConj_mulVec_ket r hβ, cFixedSwapCirc, DynCircExt.eval_seq_mulVec]
  have stepSwap (wBuf : Fin 24 → Wire n) (ctrl : Fin M → ZMod 2) {hF : _} (fl : ZMod 2) (idx : ℕ)
      (hCtrl : ∀ p : Fin M, ctrl p = if p.val = idx then fl else 0)
      (hLt : fl = 1 → idx < M) (δ : BitAssignment n) :
      (fixedSwapVecCirc M 24 wBuf ctrl (fun b p ↦ rSys r p b) hF).eval.1.mulVec (ket δ) =
        ket (if h : fl = 1 ∧ idx < M then
          swapVecBits 24 wBuf (fun b ↦ rSys r ⟨idx, h.2⟩ b) δ else δ) := by
    rcases DynCircExt.bit_cases fl with h0 | h1
    · rw [fixedSwapVecCirc_zero_ket_ul 24 _ _ _ _ δ (fun p ↦ by rw [hCtrl p, h0, ite_self]),
          dite_eq_right (fun h ↦ zero_ne_one (h0 ▸ h.1))]
    · rw [fixedSwapVecCirc_oneHot_ket_ul 24 _ _ _ _ ⟨idx, hLt h1⟩ δ (fun p ↦ by
            simp only [hCtrl p, h1, Fin.ext_iff]),
          dite_eq_left ⟨h1, hLt h1⟩]
  rw [stepSwap (rBufLo r) (routerCtrlLo r β) (β (rHas1 r)) (routerIdxMinVal r β)
      (fun _ ↦ rfl) hMinLt β,
      ← routerLoBits,
      stepSwap (rBufHi r) (routerCtrlHi r β) (routerHas2Eff r β) (routerIdxMaxVal r β) (fun _ ↦ rfl)
        (fun h ↦ (hMaxSpec h).2.2.1) (routerLoBits r β),
      ← routerSwapBits]

theorem routerSwapBits_spec {M D n : ℕ} (r : RouterReg M D n) {β : BitAssignment n}
    (hβ : ValidRouterInput r β) :
    (∀ b : Fin 24, routerSwapBits r β (rBufLo r b) =
      if h1 : β (rHas1 r) = 1 ∧ routerIdxMinVal r β < M then β (rSys r ⟨routerIdxMinVal r β,
          h1.2⟩ b) else 0) ∧
    (∀ b : Fin 24, routerSwapBits r β (rBufHi r b) =
      if h2 : routerHas2Eff r β = 1 ∧ routerIdxMaxVal r β < M then β (rSys r ⟨routerIdxMaxVal r β,
          h2.2⟩ b) else 0) ∧
    (∀ (p : Fin M) (b : Fin 24),
      ((β (rHas1 r) = 1 ∧ p.val = routerIdxMinVal r β) ∨ (routerHas2Eff r β = 1 ∧ p.val =
          routerIdxMaxVal r β)) →
      routerSwapBits r β (rSys r p b) = 0) ∧
    (∀ w : Wire n, (∀ b, w ≠ rBufLo r b) → (∀ b, w ≠ rBufHi r b) →
      (∀ (p : Fin M) (b : Fin 24), w = rSys r p b →
        (β (rHas1 r) = 1 → p.val ≠ routerIdxMinVal r β) ∧ (routerHas2Eff r β = 1 → p.val ≠
            routerIdxMaxVal r β)) →
      routerSwapBits r β w = β w) := by
  obtain ⟨hMinLt, hMaxSpec⟩ := routerMinMax_of_valid hβ
  have rNe {a c : ℕ} {ha hc} (h : a ≠ c) : r ⟨a, ha⟩ ≠ r ⟨c, hc⟩ := rr_ne r h
  have neS {p₁ p₂ : Fin M} (hp : p₁.val ≠ p₂.val) (j k : Fin 24) :
      rSys r p₁ j ≠ rSys r p₂ k := rNe (by omega)
  have injSys (p : Fin M) : Function.Injective (rSys r p) :=
    fun _ _ e ↦ Fin.ext (Decidable.byContradiction fun _ ↦ rNe (by omega) e)
  have specLo (p : Fin M) (δ : BitAssignment n) := swapVecBits_spec 24 (rBufLo r) (rSys r p)
    (fun _ _ e ↦ Fin.ext (Decidable.byContradiction fun _ ↦ rNe (by omega) e)) (injSys p)
        (fun _ _ ↦ rNe (by omega)) δ
  have specHi (p : Fin M) (δ : BitAssignment n) := swapVecBits_spec 24 (rBufHi r) (rSys r p)
    (fun _ _ e ↦ Fin.ext (Decidable.byContradiction fun _ ↦ rNe (by omega) e)) (injSys p)
        (fun _ _ ↦ rNe (by omega)) δ
  have loKeep (w : Wire n) (hwLo : ∀ k, w ≠ rBufLo r k)
      (hwSys : ∀ k, β (rHas1 r) = 1 → ∀ hlt : routerIdxMinVal r β < M,
        w ≠ rSys r ⟨routerIdxMinVal r β, hlt⟩ k) : routerLoBits r β w = β w := by
    by_cases h1 : β (rHas1 r) = 1 ∧ routerIdxMinVal r β < M
    · rw [routerLoBits, dite_eq_left h1, (specLo ⟨_, h1.2⟩ β).2.2 w hwLo fun k ↦
          hwSys k h1.1 h1.2]
    · rw [routerLoBits, dite_eq_right h1]
  have hiKeep (w : Wire n) (hwHi : ∀ k, w ≠ rBufHi r k)
      (hwSys : ∀ k, routerHas2Eff r β = 1 → ∀ hlt : routerIdxMaxVal r β < M,
        w ≠ rSys r ⟨routerIdxMaxVal r β, hlt⟩ k) : routerSwapBits r β w =
            routerLoBits r β w := by
    by_cases h2 : routerHas2Eff r β = 1 ∧ routerIdxMaxVal r β < M
    · rw [routerSwapBits, dite_eq_left h2, (specHi ⟨_, h2.2⟩ _).2.2 w hwHi fun k ↦
          hwSys k h2.1 h2.2]
    · rw [routerSwapBits, dite_eq_right h2]
  have loHiZero (b : Fin 24) : routerLoBits r β (rBufHi r b) = 0 :=
    (loKeep _ (fun _ ↦ rNe (by omega)) fun _ _ _ ↦ rNe (by omega)).trans (hβ.2.2.2.1 b).2.1
  refine ⟨fun b ↦ ?_, fun b ↦ ?_, fun p b hp ↦ ?_, fun w hwLo hwHi hwSys ↦
    (hiKeep w hwHi fun k h2 _ e ↦ (hwSys _ k e).2 h2 rfl).trans
      (loKeep w hwLo fun k h1 _ e ↦ (hwSys _ k e).1 h1 rfl)⟩
  · rw [hiKeep _ (fun _ ↦ rNe (by omega)) fun _ _ _ ↦ rNe (by omega)]
    by_cases h1 : β (rHas1 r) = 1 ∧ routerIdxMinVal r β < M
    · rw [routerLoBits, dite_eq_left h1, dite_eq_left h1, (specLo ⟨_, h1.2⟩ β).1 b]
    · rw [routerLoBits, dite_eq_right h1, dite_eq_right h1, (hβ.2.2.2.1 b).1]
  · by_cases h2 : routerHas2Eff r β = 1 ∧ routerIdxMaxVal r β < M
    · rw [routerSwapBits, dite_eq_left h2, dite_eq_left h2, (specHi ⟨_, h2.2⟩ _).1 b]
      exact loKeep _ (fun _ ↦ rNe (by omega)) fun k _ _ ↦ neS (hMaxSpec h2.1).2.2.2.1.symm b k
    · rw [routerSwapBits, dite_eq_right h2, dite_eq_right h2, loHiZero b]
  · rcases hp with ⟨hh1, hpMin⟩ | ⟨hh2, hpMax⟩
    · have h1 : β (rHas1 r) = 1 ∧ routerIdxMinVal r β < M := ⟨hh1, hMinLt hh1⟩
      rw [hiKeep _ (fun _ ↦ rNe (by omega)) fun k h2 _ ↦ neS (hpMin ▸ (hMaxSpec h2).2.2.2.1) b k,
        routerLoBits, dite_eq_left h1, show p = ⟨_, h1.2⟩ from Fin.ext hpMin, (specLo _ β).2.1 b,
        (hβ.2.2.2.1 b).1]
    · have h2 : routerHas2Eff r β = 1 ∧ routerIdxMaxVal r β < M := ⟨hh2, (hMaxSpec hh2).2.2.1⟩
      rw [routerSwapBits, dite_eq_left h2, show p = ⟨_, h2.2⟩ from Fin.ext hpMax,
          (specHi _ _).2.1 b, loHiZero b]
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouterFredkinMux
open scoped ComplexOrder MatrixOrder Circuit.Notation
open PrimitiveGate HermitianMat PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.RouterSelectWiringA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local semireducible] SplitRouterSeqBell26k.tempAndFanoutDyn KinB.andComputeCircuit
    KinB.andUncomputeDyn
theorem mux_lt0 {D : ℕ} (hD1 : 1 ≤ D) : 0 < D := hD1
theorem mux_succ_lt {D k : ℕ} (hk : k + 1 ≤ D - 1) : k + 1 < D := by omega
abbrev muxIdx0 {D : ℕ} (hD1 : 1 ≤ D) : Fin D := ⟨0, mux_lt0 hD1⟩
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouterFredkinMux

namespace QuantumComputation.Specs.PhotochemistrySolution.CoinWrap
open scoped Circuit.Notation
open PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.DynQromUncompA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open PhotochemistrySolution.Stage1Opt41TwoWrap
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg ket matrix_ext_ket)
theorem le81_coin (K : ℕ) : 81 ≤ 81 + K := Nat.le_add_right 81 K
theorem outBlk_le (K : ℕ) : 41 + 40 ≤ 81 + K := le81_coin K
theorem coin_lt_81K (K : ℕ) {v : ℕ} (hv : v < 41) : v < 81 + K := by omega
theorem clean_lt_81K {K : ℕ} (i : Fin (41 + K)) : 40 + i.val < 81 + K := by omega
/-- Maps `0..40 ↦ 0..40` (coin) and `41..40+K ↦ 81..80+K` (clean scratch), skipping `41..80`. -/
def innerIdxCoin (K : ℕ) (i : Fin (41 + K)) : Fin (81 + K) :=
    if h : i.val < 41 then ⟨i.val, coin_lt_81K K h⟩ else ⟨40 + i.val, clean_lt_81K i⟩
theorem innerIdxCoin_val (K : ℕ) (i : Fin (41 + K)) : (innerIdxCoin K i).val = if i.val <
    41 then i.val else 40 + i.val := by
  dsimp only [innerIdxCoin]
  split_ifs <;> rfl
theorem innerIdxCoin_injective (K : ℕ) : Function.Injective (innerIdxCoin K) := fun a b e ↦ by
  have hv := (innerIdxCoin_val K a).symm.trans ((congrArg Fin.val e).trans (innerIdxCoin_val K b))
  split_ifs at hv <;> exact Fin.ext (by omega)
abbrev rCoinInner (K : ℕ) {n : ℕ} (r : QRegister (81 + K) n) : QRegister (41 + K) n :=
    r.compose ⟨⟨innerIdxCoin K, innerIdxCoin_injective K⟩⟩
abbrev rCoinOut40 (K : ℕ) {n : ℕ} (r : QRegister (81 + K) n) : QRegister 40 n :=
    r.compose (QRegister.block 41 40 (outBlk_le K))
abbrev rCoinClean (K : ℕ) {n : ℕ} (r : QRegister (81 + K) n) : QRegister ((81 + K) - 81) n :=
    r.compose (QRegister.block 81 ((81 + K) - 81) (Nat.add_sub_of_le (le81_coin K)).le)
theorem innerCoin_ne_out40 (K : ℕ) {n : ℕ} (r : QRegister (81 + K) n) (i : Fin (41 + K))
    (j : Fin 40) :
    rCoinInner K r i ≠ rCoinOut40 K r j := fun e ↦ by
  have hv := congrArg Fin.val (r.wires.injective e)
  simp only [QRegister.block_apply_val, Function.Embedding.coeFn_mk, innerIdxCoin_val] at hv
  split_ifs at hv
  all_goals omega
theorem innerCoin_ge41_eq_clean (K : ℕ) {n : ℕ} (r : QRegister (81 + K) n) (i : Fin (41 + K))
    (hi : 41 ≤ i.val) :
    rCoinInner K r i = rCoinClean K r ⟨i.val - 41, by omega⟩ :=
  congrArg r (Fin.ext (by
    simp only [QRegister.block_apply_val, Function.Embedding.coeFn_mk]
    rw [innerIdxCoin_val, ifn_tw (by omega)]
    omega))
/-- Parity in `ZMod 2` of bitmask `mask` over `[1, α[0], ..., α[M-1]]`. -/
def maskParity (mask : ℕ) {M : ℕ} (α : BitAssignment M) : (k : ℕ) → k ≤ M → ZMod 2
  | 0, _ => if mask.testBit 0 then 1 else 0
  | k + 1, hk =>
        maskParity mask α k (Nat.le_of_succ_le hk) + (if mask.testBit (1 + k) then α ⟨k, hk⟩ else 0)
/-- XOR `maskParity mask (β ∘ src)` into target wire `dst` disjoint from `src`. -/
def qXorMask1 {M n : ℕ} (src : QRegister M n) (dst : Wire n) (hDisj : ∀ i : Fin M, src i ≠ dst)
    (mask : ℕ) : (k : ℕ) → k ≤ M → ComputeProg n
  | 0, _ => if mask.testBit 0 then .x dst else .id
  | k + 1, hk =>
      let prev := qXorMask1 src dst hDisj mask k (Nat.le_of_succ_le hk)
      if mask.testBit (1 + k) then .seq prev (.cnot (src ⟨k, hk⟩) dst (hDisj ⟨k, hk⟩)) else prev
theorem fwdBits_qXorMask1 {M n : ℕ} (src : QRegister M n) (dst : Wire n)
    (hDisj : ∀ i : Fin M, src i ≠ dst) (mask : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ M) (β : BitAssignment n),
      (qXorMask1 src dst hDisj mask k hk).fwdBits β = Function.update β dst (β dst +
          maskParity mask (fun i ↦ β (src i)) k hk)
  | 0, _, β => by
      dsimp only [qXorMask1, maskParity]
      cases mask.testBit 0 <;> simp [ComputeProg.fwdBits]
  | k + 1, hk, β => by
      have ih := fwdBits_qXorMask1 src dst hDisj mask k (by omega) β
      dsimp only [qXorMask1, maskParity]
      split_ifs
      · simp only [ComputeProg.fwdBits, ih, Function.update_self,
          Function.update_of_ne (hDisj _), Function.update_idem, add_assoc]
      · simpa only [add_zero] using ih
/-- XOR `40` linear parity masks `outs40 j` from `src : QRegister M n` onto disjoint `rDst`. -/
def qXorMask40 {M n : ℕ} (src : QRegister M n) (rDst : QRegister 40 n)
    (hDisj : ∀ i : Fin M, ∀ j : Fin 40, src i ≠ rDst j) (outs40 : Fin 40 → ℕ) : (m : ℕ) → m ≤ 40 →
        ComputeProg n
  | 0, _ => .id
  | m + 1, hm =>
      .seq (qXorMask40 src rDst hDisj outs40 m (Nat.le_of_succ_le hm))
        (qXorMask1 src (rDst ⟨m, hm⟩) (fun i ↦ hDisj i ⟨m, hm⟩) (outs40 ⟨m, hm⟩) M le_rfl)
theorem count_qXorMask40 {M n : ℕ} (src : QRegister M n) (rDst : QRegister 40 n)
    (hDisj : ∀ i : Fin M, ∀ j : Fin 40, src i ≠ rDst j) (outs40 : Fin 40 → ℕ) :
    ∀ (m : ℕ) (hm : m ≤ 40),
      (fwdCirc (qXorMask40 src rDst hDisj outs40 m hm)).count PrimitiveGate.T = 0 ∧
      (fwdCirc (qXorMask40 src rDst hDisj outs40 m hm)).count PrimitiveGate.TOFF = 0
  | 0, _ => by
      unfold qXorMask40 fwdCirc
      exact ⟨rfl, rfl⟩
  | m + 1, hm => by
      have fSeq (p q : ComputeProg n) : fwdCirc (p.seq q) = fwdCirc p ;;ᶜ
        fwdCirc q := by
        conv_lhs => unfold fwdCirc
      have cnt1 (dst) (hD : ∀ i, src i ≠ dst) (mask k) (hk : k ≤ M) :
          (fwdCirc (qXorMask1 src dst hD mask k hk)).count .T = 0 ∧
          (fwdCirc (qXorMask1 src dst hD mask k hk)).count .TOFF = 0 := by
        induction k with
        | zero =>
            dsimp only [qXorMask1]
            cases mask.testBit 0 <;> unfold fwdCirc <;> exact ⟨rfl, rfl⟩
        | succ k ih =>
            obtain ⟨cT, cF⟩ := ih (by omega)
            dsimp only [qXorMask1]
            split_ifs
            · simp only [fSeq, Circuit.count_seq, cT, cF]
              exact ⟨rfl, rfl⟩
            · exact ⟨cT, cF⟩
      obtain ⟨hT, hF⟩ := count_qXorMask40 src rDst hDisj outs40 m (by omega)
      obtain ⟨kT, kF⟩ := cnt1 (rDst ⟨m, hm⟩) (fun i ↦ hDisj i _) (outs40 ⟨m, hm⟩) M le_rfl
      unfold qXorMask40
      simp [fSeq, Circuit.count_seq, hT, hF, kT, kF]
theorem circWires_qXorMask40 {M n : ℕ} {Q : Wire n → Prop} (src : QRegister M n)
    (rDst : QRegister 40 n)
    (hDisj : ∀ i : Fin M, ∀ j : Fin 40, src i ≠ rDst j) (outs40 : Fin 40 → ℕ)
    (hSrc : ∀ i : Fin M, Q (src i)) (hDst : ∀ j : Fin 40, Q (rDst j)) :
    ∀ (m : ℕ) (hm : m ≤ 40), CircWires Q (fwdCirc (qXorMask40 src rDst hDisj outs40 m hm))
  | 0, _ => by
      unfold qXorMask40 fwdCirc CircWires
      trivial
  | m + 1, hm => by
      have fSeq (p q : ComputeProg n) : fwdCirc (p.seq q) = fwdCirc p ;;ᶜ
        fwdCirc q := by
        conv_lhs => unfold fwdCirc
      have cw1 (dst) (hD : ∀ i, src i ≠ dst) (mask) (h1 : Q dst) (k) (hk : k ≤ M) :
          CircWires Q (fwdCirc (qXorMask1 src dst hD mask k hk)) := by
        induction k with
        | zero =>
            dsimp only [qXorMask1]
            cases mask.testBit 0 <;> unfold fwdCirc CircWires
            · trivial
            · exact fun i ↦ by
                fin_cases i
                exact h1
        | succ k ih =>
            dsimp only [qXorMask1]
            split_ifs
            · rw [fSeq]
              exact ⟨ih (by omega), fun i ↦ by
                fin_cases i
                · exact hSrc _
                · exact h1⟩
            · exact ih (by omega)
      unfold qXorMask40
      rw [fSeq]
      exact ⟨circWires_qXorMask40 src rDst hDisj outs40 hSrc hDst m (by omega),
        cw1 (rDst ⟨m, hm⟩) (fun i ↦ hDisj i _) (outs40 _) (hDst _) M le_rfl⟩
/-- Mid-circuit linear output circuit for `outs40 : Fin 40 → ℕ` on `QRegister (81 + K) n`. -/
def cXorMaskCoin (K : ℕ) (outs40 : Fin 40 → ℕ) {n : ℕ} (r : QRegister (81 + K) n) : Circuit n :=
  fwdCirc (qXorMask40 (rCoinInner K r) (rCoinOut40 K r)
      (innerCoin_ne_out40 K r) outs40 40 Nat.le.refl)
theorem ket_cXorMaskCoin (K : ℕ) (outs40 : Fin 40 → ℕ) {n : ℕ} [NeZero (2 ^ n)]
    (r : QRegister (81 + K) n) (β : BitAssignment n) :
    (cXorMaskCoin K outs40 r).eval.1.mulVec (ket β) =
      ket (xorDstK (rCoinOut40 K r) (fun j ↦ maskParity (outs40 j) (fun i ↦ β (rCoinInner K r i))
          (41 + K) le_rfl) 40 Nat.le.refl β) := by
  let f := fun j : Fin 40 ↦ maskParity (outs40 j) (fun i ↦ β (rCoinInner K r i)) (41 + K) le_rfl
  have fwd40 (m : ℕ) (hm : m ≤ 40) :
      (qXorMask40 (rCoinInner K r) (rCoinOut40 K r)
          (innerCoin_ne_out40 K r) outs40 m hm).fwdBits β =
        xorDstK (rCoinOut40 K r) f m hm β := by
    induction m with
    | zero => rfl
    | succ m ih =>
        dsimp only [qXorMask40, ComputeProg.fwdBits, xorDstK]
        rw [ih (by omega), fwdBits_qXorMask1]
        simp only [xorDstK_outside _ f _ _ β (innerCoin_ne_out40 K r _), f]
  rw [cXorMaskCoin, fwdCirc_mulVec_ket, fwd40 40 Nat.le.refl]
theorem cXorMaskCoin_sq (K : ℕ) (outs40 : Fin 40 → ℕ) {n : ℕ} [NeZero (2 ^ n)]
    (r : QRegister (81 + K) n) :
    (cXorMaskCoin K outs40 r).eval * (cXorMaskCoin K outs40 r).eval = 1 := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  rw [coe_mul_u_tw, ← Matrix.mulVec_mulVec, ket_cXorMaskCoin, ket_cXorMaskCoin, coe_one_u_tw,
      Matrix.one_mulVec]
  simp only [show ∀ f i, xorDstK (rCoinOut40 K r) f 40 Nat.le.refl β (rCoinInner K r i) =
      β (rCoinInner K r i) from
    fun _ i ↦ xorDstK_outside _ _ _ _ _ (innerCoin_ne_out40 K r i)]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : ∃ j : Fin 40, w = rCoinOut40 K r j
  · rcases hw with ⟨j, rfl⟩
    rw [xorDstK_dst, ifp_tw j.isLt, xorDstK_dst, ifp_tw j.isLt, add_assoc, CharTwo.add_self_eq_zero,
        add_zero]
  · simp only [xorDstK_outside _ _ _ _ _ fun j e ↦ hw ⟨j, e⟩]
end QuantumComputation.Specs.PhotochemistrySolution.CoinWrap
end
end
