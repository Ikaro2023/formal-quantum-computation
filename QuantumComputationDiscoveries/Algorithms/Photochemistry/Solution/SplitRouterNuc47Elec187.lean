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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.CoulombStage2Unload
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option allowUnsafeReducibility true
set_option autoImplicit false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
set_option exponentiation.threshold 256

noncomputable section
open Operator QProg Matrix QuantumComputation.Specs.PhotochemistrySolution
section
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
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
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn)
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem hne_fixed_router {M D n : ℕ} (r : RouterReg M D n) :
    (∀ (b : Fin 24) (p : Fin M), rBufLo r b ≠ rSys r p b) ∧
    (∀ (b : Fin 24) (p : Fin M), rBufHi r b ≠ rSys r p b) ∧
    (∀ (b : Fin 24) (p : Fin M), rHA r b ≠ rSys r p b) ∧
    (∀ (b : Fin 24) (p : Fin M), rHB r b ≠ rSys r p b) := by
  have ne {a c : ℕ} {ha hc} (h : a ≠ c) : r ⟨a, ha⟩ ≠ r ⟨c, hc⟩ := rr_ne r h
  exact ⟨fun _ _ ↦ ne (by omega), fun _ _ ↦ ne (by omega),
    fun _ _ ↦ ne (by omega), fun _ _ ↦ ne (by omega)⟩
/-- Classical-control pure swap circuit for fixed one-hot vectors `cLo cHi`. -/
def cFixedSwapCirc {M D n : ℕ} (r : RouterReg M D n) (cLo cHi : Fin M → ZMod 2) : Circuit n :=
  fixedSwapVecCirc M 24 (rBufLo r) cLo (fun b p ↦ rSys r p b) (hne_fixed_router r).1 ;;ᶜ
  fixedSwapVecCirc M 24 (rBufHi r) cHi (fun b p ↦ rSys r p b) (hne_fixed_router r).2.1
/-- Classical-control pure Bell overlay circuit for fixed one-hot vectors `cLo cHi`. -/
def cFixedBellOverlayCirc {M D n : ℕ} (r : RouterReg M D n) (cLo cHi : Fin M → ZMod 2) :
    Circuit n :=
  fixedBellVecCirc M 24 (rHA r) cLo (fun b p ↦ rSys r p b) (hne_fixed_router r).2.2.1 ;;ᶜ
  fixedBellVecCirc M 24 (rHB r) cHi (fun b p ↦ rSys r p b) (hne_fixed_router r).2.2.2
def BellModSet {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
  (∃ b : Fin 24, w = rHA r b) ∨
  (∃ b : Fin 24, w = rHB r b) ∨
  (∃ (p : Fin M) (b : Fin 24), w = rSys r p b)
/-- Public index/flag wires `{rHas1 r, rRawHas2 r, rIdx1 r, rIdx2 r}` read by `routerCtrlLo/Hi`. -/
def RouterCtrlSet {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
  w = rHas1 r ∨
  w = rRawHas2 r ∨
  (∃ d : Fin D, w = rIdx1 r d) ∨
  (∃ d : Fin D, w = rIdx2 r d)
theorem routerCtrlSet_disj_bellModSet {M D n : ℕ} (r : RouterReg M D n) {w : Wire n}
    (hc : RouterCtrlSet r w) (hb : BellModSet r w) : False := by
  have ne {a c : ℕ} {ha hc} (h : a ≠ c) : r ⟨a, ha⟩ ≠ r ⟨c, hc⟩ := rr_ne r h
  rcases hc with rfl | rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩ <;>
    rcases hb with ⟨b, h⟩ | ⟨b, h⟩ | ⟨p, b, h⟩ <;> exact ne (by omega) h.symm
theorem routerCtrlPair_eq_of_eq {M D n : ℕ} (r : RouterReg M D n) {α β : BitAssignment n}
    (hEq : ∀ u, RouterCtrlSet r u → α u = β u) :
    routerCtrlLo r α = routerCtrlLo r β ∧ routerCtrlHi r α = routerCtrlHi r β := by
  have hi1 := idxValD_congr fun d ↦ hEq _ (Or.inr (Or.inr (Or.inl ⟨d, rfl⟩)))
  have hi2 := idxValD_congr fun d ↦ hEq _ (Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))
  have hh2 : routerHas2Eff r α = routerHas2Eff r β := by
    simp only [routerHas2Eff, hEq _ (Or.inr (Or.inl rfl)), hi1, hi2]
  exact ⟨funext fun _ ↦ by simp only [routerCtrlLo, hEq _ (Or.inl rfl),
      show routerIdxMinVal r α = routerIdxMinVal r β by simp only [routerIdxMinVal, hh2, hi1, hi2]],
    funext fun _ ↦ by simp only [routerCtrlHi, hh2,
      show routerIdxMaxVal r α = routerIdxMaxVal r β by simp only [routerIdxMaxVal, hh2, hi1, hi2]]⟩
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187

namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
/-!
## Part A1: Unconditional Ket Evaluation Identities for `uBellOverlayConj` & `uRouterSwapConj`
-/

theorem not_allPlaneMod_of_routerCtrlSet {M D n : ℕ} (r : RouterReg M D n) {w : Wire n}
    (hw : RouterCtrlSet r w) : ¬ AllPlaneMod r w := by
  have idxLt {a : ℕ} {ha} (h : a < 2 + 2 * D) : ¬ AllPlaneMod r (r ⟨a, ha⟩) :=
    not_allPlaneMod_of_idx r (Or.inl h)
  rcases hw with rfl | rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩ <;> exact idxLt (by omega)

theorem preservesKetPred_cFixedSwapCirc {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) {P : BitAssignment n → Prop}
    (hModKeep : ∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v))
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cFixedSwapCirc r cLo cHi).eval.1.mulVec ψ) := by
  have hSV (m) {qB cV wT hbt} (hqB : ∀ k, AllPlaneMod r (qB k))
      (hwT : ∀ k p, AllPlaneMod r (wT k p)) {φ} (hφ : PreservesKetPred P φ) :
      PreservesKetPred P ((fixedSwapVecCirc M m qB cV wT hbt).eval.1.mulVec φ) := by
    induction m with
    | zero => simpa [fixedSwapVecCirc] using hφ
    | succ m ihm =>
      simpa only [fixedSwapVecCirc, eval_seq_mulVec] using preservesKetPred_fixedSwap1 M _ _ _ _
        (hModKeep (hqB _)) (fun p ↦ hModKeep (hwT _ p))
        (ihm (fun k ↦ hqB k.castSucc) (fun k ↦ hwT k.castSucc))
  have hwS (b) (p) : AllPlaneMod r (rSys r p b) :=
    ⟨b, .inr (.inr (.inr (.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩
  rw [cFixedSwapCirc, eval_seq_mulVec]
  exact hSV 24 (fun b ↦ ⟨b, .inr (.inl rfl)⟩) hwS (hSV 24 (fun b ↦ ⟨b, .inl rfl⟩) hwS hψ)

theorem preservesKetPred_cFixedBellOverlay {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) {P : BitAssignment n → Prop}
    (hKeep : ∀ {u : Wire n}, BellModSet r u → ∀ α v, P α → P (Function.update α u v))
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cFixedBellOverlayCirc r cLo cHi).eval.1.mulVec ψ) := by
  have hBV (m) {qH cV wT hht} (hqH : ∀ k, BellModSet r (qH k))
      (hwT : ∀ k p, BellModSet r (wT k p)) {φ} (hφ : PreservesKetPred P φ) :
      PreservesKetPred P ((fixedBellVecCirc M m qH cV wT hht).eval.1.mulVec φ) := by
    induction m with
    | zero => simpa [fixedBellVecCirc] using hφ
    | succ m ihm =>
      rw [fixedBellVecCirc, fixedBell1Circ, eval_seq_mulVec, eval_seq_mulVec]
      exact preservesKetPred_fixedFanout M _ _ _ _ (fun p ↦ hKeep (hwT _ p)) (preservesKetPred_H
        (hKeep (hqH _)) (ihm (fun k ↦ hqH k.castSucc) (fun k ↦ hwT k.castSucc)))
  simpa only [cFixedBellOverlayCirc, eval_seq_mulVec] using hBV 24 (fun b ↦ .inr (.inl ⟨b, rfl⟩))
    (fun b p ↦ .inr (.inr ⟨p, b, rfl⟩))
    (hBV 24 (fun b ↦ .inl ⟨b, rfl⟩) (fun b p ↦ .inr (.inr ⟨p, b, rfl⟩)) hψ)

theorem mulVec_ket_apply {n : ℕ} (A : Operator (2 ^ n)) (β : BitAssignment n) (x : Fin (2 ^ n)) :
    (A.mulVec (ket β)) x = A x ((basisBitsEquiv n).symm β) := by
  simp

/--
Column-indexed matrix of any `(routerCtrlLo, routerCtrlHi)` -controlled circuit family `fCirc` .
-/
def uCtrlPairGhostMat {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n) : Operator (2 ^ n) :=
  Matrix.of fun x y ↦
    (fCirc (routerCtrlLo r (basisBitsEquiv n y)) (routerCtrlHi r (basisBitsEquiv n y))).eval.1 x y

theorem uCtrlPairGhostMat_mulVec_ket {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n) (β : BitAssignment n) :
    (uCtrlPairGhostMat r fCirc).mulVec (ket β) =
      (fCirc (routerCtrlLo r β) (routerCtrlHi r β)).eval.1.mulVec (ket β) := by
  funext x
  simp [uCtrlPairGhostMat, mulVec_ket_apply]

theorem preservesKetPred_ctrlPair_ghost {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n)
    (hPres : ∀ cLo cHi {P : BitAssignment n → Prop},
      (∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v)) →
      ∀ {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
          PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ))
    (cLo cHi : Fin M → ZMod 2) (β : BitAssignment n) :
    PreservesKetPred
      (fun α ↦ routerCtrlLo r α = routerCtrlLo r β ∧ routerCtrlHi r α = routerCtrlHi r β)
      ((fCirc cLo cHi).eval.1.mulVec (ket β)) :=
  hPres cLo cHi (fun {u} hu α val hα ↦
    let ⟨eL, eH⟩ := routerCtrlPair_eq_of_eq r (α := Function.update α u val) (β := α) fun w hw ↦
      Function.update_of_ne (fun e : w = u ↦ not_allPlaneMod_of_routerCtrlSet r hw (e ▸ hu)) val α
    ⟨eL.trans hα.1, eH.trans hα.2⟩) (preservesKetPred_ket ⟨rfl, rfl⟩)

theorem uCtrlPairGhost_apply_eq_zero_of_ctrl_ne {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n)
    (hPres : ∀ cLo cHi {P : BitAssignment n → Prop},
      (∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v)) →
      ∀ {ψ : Fin (2 ^ n) → ℂ},
        PreservesKetPred P ψ → PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ))
    (cLo cHi : Fin M → ZMod 2) {x y : Fin (2 ^ n)}
    (hne : ¬ (routerCtrlLo r (basisBitsEquiv n x) = routerCtrlLo r (basisBitsEquiv n y) ∧
      routerCtrlHi r (basisBitsEquiv n x) = routerCtrlHi r (basisBitsEquiv n y))) :
    (fCirc cLo cHi).eval.1 x y = 0 := by
  let P (α : BitAssignment n) : Prop := routerCtrlLo r α = routerCtrlLo r (basisBitsEquiv n y) ∧
    routerCtrlHi r α = routerCtrlHi r (basisBitsEquiv n y)
  simpa only [P, Matrix.zero_mulVec, Pi.zero_apply, Matrix.mulVec_diagonal, mulVec_ket_apply,
    Equiv.symm_apply_apply, ite_eq_right hne, one_mul] using congrFun
    (preservesKetPred_ctrlPair_ghost r fCirc hPres cLo cHi (basisBitsEquiv n y)
      (Matrix.diagonal fun z ↦ if P (basisBitsEquiv n z) then (0 : ℂ) else 1) 0 fun α hα ↦
      funext fun z ↦ by
        rw [mulVec_ket_apply, Matrix.zero_mulVec, Pi.zero_apply]
        exact if hz : z = (basisBitsEquiv n).symm α then by simp [hz, P, hα]
          else Matrix.diagonal_apply_ne _ hz) x

theorem uCtrlPairGhostMat_eq_row {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n)
    (hPres : ∀ cLo cHi {P : BitAssignment n → Prop},
      (∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v)) →
      ∀ {ψ : Fin (2 ^ n) → ℂ},
        PreservesKetPred P ψ → PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ))
    (x y : Fin (2 ^ n)) :
    uCtrlPairGhostMat r fCirc x y =
      (fCirc (routerCtrlLo r (basisBitsEquiv n x))
        (routerCtrlHi r (basisBitsEquiv n x))).eval.1 x y := by
  by_cases h : routerCtrlLo r (basisBitsEquiv n x) = routerCtrlLo r (basisBitsEquiv n y) ∧
      routerCtrlHi r (basisBitsEquiv n x) = routerCtrlHi r (basisBitsEquiv n y)
  · simp only [uCtrlPairGhostMat, Matrix.of_apply, h.1, h.2]
  · simp only [uCtrlPairGhostMat, Matrix.of_apply,
      uCtrlPairGhost_apply_eq_zero_of_ctrl_ne r fCirc hPres _ _ h]

theorem uCtrlPairGhostMat_conjTranspose_mulVec_ket {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n)
    (hPres : ∀ cLo cHi {P : BitAssignment n → Prop},
      (∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v)) →
      ∀ {ψ : Fin (2 ^ n) → ℂ},
        PreservesKetPred P ψ → PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ))
    (β : BitAssignment n) :
    (uCtrlPairGhostMat r fCirc)ᴴ.mulVec (ket β) =
      ((fCirc (routerCtrlLo r β) (routerCtrlHi r β)).eval⁻¹).1.mulVec (ket β) := by
  refine funext fun x ↦ ?_
  simpa [mulVec_ket_apply, show ((fCirc (routerCtrlLo r β) (routerCtrlHi r β)).eval⁻¹).1 =
      ((fCirc (routerCtrlLo r β) (routerCtrlHi r β)).eval.1)ᴴ from Matrix.star_eq_conjTranspose _]
    using congrArg star (uCtrlPairGhostMat_eq_row r fCirc hPres ((basisBitsEquiv n).symm β) x)

/--
Fiberwise block-diagonal ghost unitary acting on each `(routerCtrlLo, routerCtrlHi)` sector
via the classical-control circuit `fCirc cLo cHi` supported inside `AllPlaneMod r`.
-/
def uCtrlPairGhost {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n)
    (hPres : ∀ cLo cHi {P : BitAssignment n → Prop},
      (∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v)) →
      ∀ {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
          PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ)) :
    Unitary (2 ^ n) :=
  ⟨uCtrlPairGhostMat r fCirc, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    apply matrix_ext_ket
    intro β
    let Ub := (fCirc (routerCtrlLo r β) (routerCtrlHi r β)).eval
    rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, uCtrlPairGhostMat_mulVec_ket]
    have hInv : (uCtrlPairGhostMat r fCirc)ᴴ.mulVec (Ub.1.mulVec (ket β)) =
        (Ub⁻¹).1.mulVec (Ub.1.mulVec (ket β)) :=
      preservesKetPred_ctrlPair_ghost r fCirc hPres _ _ β
        (uCtrlPairGhostMat r fCirc)ᴴ (Ub⁻¹).1 fun α hα ↦ by
          rw [uCtrlPairGhostMat_conjTranspose_mulVec_ket r fCirc hPres, hα.1, hα.2]
    rw [hInv, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel Ub,
        Submonoid.coe_one, Matrix.one_mulVec]⟩

/-- Pure-ghost `sPrivClean`-independent router swap unitary `uRouterSwapConj r`. -/
def uRouterSwapConj {M D n : ℕ} (r : RouterReg M D n) : Unitary (2 ^ n) :=
  uCtrlPairGhost r (cFixedSwapCirc r) (preservesKetPred_cFixedSwapCirc r)

theorem uRouterSwapConj_mulVec_ket_any {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) :
    (uRouterSwapConj r).1.mulVec (ket β) =
      (cFixedSwapCirc r (routerCtrlLo r β) (routerCtrlHi r β)).eval.1.mulVec (ket β) :=
  uCtrlPairGhostMat_mulVec_ket r (cFixedSwapCirc r) β

theorem uRouterSwapConj_mulVec_ket {M D n : ℕ} (r : RouterReg M D n) {β : BitAssignment n}
    (_hβ : ValidRouterInput r β) :
    (uRouterSwapConj r).1.mulVec (ket β) =
      (cFixedSwapCirc r (routerCtrlLo r β) (routerCtrlHi r β)).eval.1.mulVec (ket β) :=
  uRouterSwapConj_mulVec_ket_any r β

theorem comm_uRouterSwapConj_embedMatrix {M D k n : ℕ} [NeZero (2 ^ n)]
    (r₁ : RouterReg M D n) (rOff : QRegister k n)
    (hDisj : ∀ (i : Fin (routerWidth M D)) (j : Fin k), r₁ i ≠ rOff j)
    (A : Operator (2 ^ k)) :
    Commute (uRouterSwapConj r₁).1 (rOff.embedMatrix A) := by
  have hComm {c : Circuit n} (hc : CircWires (fun u ↦ ∀ j, u ≠ rOff j) c) :
      Commute c.eval.1 (rOff.embedMatrix A) := by
    induction c with
    | identity => simp [Circuit.eval_identity]
    | gate g reg =>
      exact reg.embedMatrix_comm_of_disjoint rOff (QRegister.disjoint_iff.mpr hc) g.eval.1 A
    | seq _ _ ih₁ ih₂ => exact Circuit.eval_seq _ _ ▸ (ih₂ hc.2).mul_left (ih₁ hc.1)
  have cwSwap1 (K) {qB cV wT hbt} (hq : ∀ j, qB ≠ rOff j) (hw : ∀ p j, wT p ≠ rOff j) :
      CircWires (fun u ↦ ∀ j, u ≠ rOff j) (fixedSwap1Circ K qB cV wT hbt) := by
    induction K with
    | zero => trivial
    | succ K ih =>
      dsimp only [fixedSwap1Circ]
      exact ⟨ih (hw ·.castSucc), if h : cV (Fin.last K) = 1 then
        (ite_eq_left h).symm ▸ ⟨ProviderCore.cw_cnot hq (hw _), ProviderCore.cw_cnot (hw _) hq,
          ProviderCore.cw_cnot hq (hw _)⟩ else (ite_eq_right h).symm ▸ trivial⟩
  have cwSwapV (m) {qB cV wT hbt} (hq : ∀ u j, qB u ≠ rOff j) (hw : ∀ u p j, wT u p ≠ rOff j) :
      CircWires (fun u ↦ ∀ j, u ≠ rOff j) (fixedSwapVecCirc M m qB cV wT hbt) := by
    induction m with
    | zero => trivial
    | succ m ih =>
      exact ⟨ih (hq ·.castSucc) (hw ·.castSucc), cwSwap1 M (hq _) (hw _)⟩
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, show (uRouterSwapConj r₁).1 *ᵥ (rOff.embedMatrix A *ᵥ ket β) =
      (cFixedSwapCirc r₁ (routerCtrlLo r₁ β) (routerCtrlHi r₁ β)).eval.1 *ᵥ
        (rOff.embedMatrix A *ᵥ ket β) by
      rw [PhotochemistrySolution.SelectDataBuilder.embedMatrix_mulVec_ket_sym rOff A β,
        Matrix.mulVec_sum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun z' _ ↦ ?_
      obtain ⟨eL, eH⟩ := routerCtrlPair_eq_of_eq r₁ (β := β)
        (α := DynCircExt.writeReg β rOff (basisBits k z')) fun u hu ↦
        DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ by
          rcases hu with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact hDisj _ j hj.symm
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, uRouterSwapConj_mulVec_ket_any r₁, eL, eH],
    Matrix.mulVec_mulVec, (hComm (c := cFixedSwapCirc r₁ _ _)
      ⟨cwSwapV 24 (fun _ ↦ hDisj _) (fun _ _ ↦ hDisj _),
       cwSwapV 24 (fun _ ↦ hDisj _) (fun _ _ ↦ hDisj _)⟩).eq,
    ← Matrix.mulVec_mulVec, ← uRouterSwapConj_mulVec_ket_any r₁ β, Matrix.mulVec_mulVec]
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
end

section
open Circuit Qubit PrimitiveGate DynamicCircuit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open PhotochemistrySolution.SelectFastFlags
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
-- Stage-2b coordinate aligner, Bell-control safety, and generic ComputeProg target/congruence
-- helpers
theorem align_ne_align {j k : Fin 136} (h : j.val ≠ k.val) : rAlignLayout j ≠ rAlignLayout k :=
  fun e ↦ h (congrArg Fin.val (rAlignLayout.wires.injective e))
theorem nuc_ne_align (i : Fin (routerWidth 47 6)) (k : Fin 136) :
    rNucLayout i ≠ rAlignLayout k := fun e ↦ by
  match val_rNuc_bounds i, val_rAlignLayout k ▸ congrArg Fin.val e with | _, _ => omega
theorem elec_ne_align (j : Fin (routerWidth 187 8)) (k : Fin 136) :
    rElecLayout j ≠ rAlignLayout k := fun e ↦ by
  match val_rElec_bounds j, val_rAlignLayout k ▸ congrArg Fin.val e with | _, _ => omega
theorem out_ne_align (j : Fin 40) (k : Fin 136) : rOut40Layout j ≠ rAlignLayout k := fun e ↦ by
  match val_rOut40Layout j ▸ val_rAlignLayout k ▸ congrArg Fin.val e with | _ => omega
def finSeqCP {N : ℕ} : (k : ℕ) → (Fin k → ComputeProg N) → ComputeProg N
  | 0, _ => .id
  | k + 1, f => .seq (finSeqCP k (fun i ↦ f i.castSucc)) (f (Fin.last k))
theorem computeProgWires_finSeqCP {N : ℕ} {S : Wire N → Prop} :
    ∀ (k : ℕ) (f : Fin k → ComputeProg N),
      (∀ i, ComputeProgWires S (f i)) → ComputeProgWires S (finSeqCP k f)
  | 0, _, _ => trivial
  | k + 1, _f, hf => ⟨computeProgWires_finSeqCP k _ (fun i ↦ hf i.castSucc), hf (Fin.last k)⟩
def pXorNucStep (d : Fin 6) : ComputeProg dLayout :=
    .seq (.x (rXorNuc d)) (.seq (.cnot (rIdx1 rNucLayout d) (rXorNuc d) (nuc_ne_align _ _))
    (.cnot (rIdx2 rNucLayout d) (rXorNuc d) (nuc_ne_align _ _)))
def pXorNuc6 : ComputeProg dLayout := finSeqCP 6 pXorNucStep
def pEqNucStep (d : Fin 6) : ComputeProg dLayout :=
  if _ : d.val = 0 then
    .andGate wRawHasN2 (rXorNuc d) (rEqNucChain d)
      (out_ne_align _ _) (out_ne_align _ _) (align_ne_align (by dsimp; omega))
  else
    .andGate (rEqNucChain ⟨d.val - 1, by omega⟩) (rXorNuc d) (rEqNucChain d)
      (align_ne_align (by dsimp; omega)) (align_ne_align (by dsimp; omega))
      (align_ne_align (by dsimp; omega))
def pEqNucChain6 : ComputeProg dLayout := finSeqCP 6 pEqNucStep
def pCoord1Step (b : Fin 24) : ComputeProg dLayout :=
  .seq (.andGate wEqNuc (rBufLo rNucLayout b) (rCoord1Align b)
      (nuc_ne_align _ _).symm (align_ne_align (by dsimp; omega)) (nuc_ne_align _ _))
    (.cnot (rBufHi rNucLayout b) (rCoord1Align b) (nuc_ne_align _ _))
def pCoord1Align24 : ComputeProg dLayout := finSeqCP 24 pCoord1Step
def pFineBitStep (b : Fin 24) : ComputeProg dLayout :=
  .seq (.andGate wIsMixed (rBufLo rElecLayout b) (rFineT b)
      (elec_ne_align _ _).symm (align_ne_align (by dsimp; omega)) (elec_ne_align _ _))
  (.seq (.cnot (rBufLo rNucLayout b) (pFineA b) (nuc_ne_align _ _))
  (.seq (.cnot (rBufLo rElecLayout b) (pFineA b) (elec_ne_align _ _))
  (.seq (.cnot (rFineT b) (pFineA b) (align_ne_align (by dsimp; omega)))
  (.seq (.cnot (rBufHi rNucLayout b) (pFineB b) (nuc_ne_align _ _))
  (.seq (.cnot (rBufHi rElecLayout b) (pFineB b) (elec_ne_align _ _))
    (.cnot (rFineT b) (pFineB b) (align_ne_align (by dsimp; omega))))))))
def pFineAlign25 : ComputeProg dLayout :=
  .seq
    (.andGate wHasN1 wHasE1 wIsMixed
      (fun e ↦ by have hv := congrArg Fin.val (rOut40Layout.wires.injective e); dsimp at hv; omega)
      (out_ne_align _ _) (out_ne_align _ _))
    (finSeqCP 24 pFineBitStep)
def pKinAlign0 : ComputeProg dLayout :=
    .seq (.cnot wAxis0 wKinAxis0 (out_ne_align _ _))
    (.seq (.cnot wAxis1 wKinAxis1 (out_ne_align _ _))
    (.seq (.cnot wIsFine wIsFineCopy (out_ne_align _ _))
    (.cnot wHasE1 wIsElecKin (out_ne_align _ _))))
def TargetsIn {N : ℕ} (T : Wire N → Prop) : ComputeProg N → Prop
  | .id => True
  | .x u => T u
  | .cnot _ tg _ => T tg
  | .andGate _ _ a _ _ _ => T a
  | .seq p₁ p₂ => TargetsIn T p₁ ∧ TargetsIn T p₂
theorem fwdBits_of_not_targetsIn {N : ℕ} {T : Wire N → Prop} :
    ∀ {p : ComputeProg N}, TargetsIn T p → ∀ (β : BitAssignment N) {w : Wire N}, ¬ T w →
      p.fwdBits β w = β w
  | .id, _, _, _, _ => rfl
  | .x u, hu, _, w, hw => Function.update_of_ne (fun e : w = u ↦ hw (e.symm ▸ hu)) _ _
  | .cnot _ tg _, ht, _, w, hw => Function.update_of_ne (fun e : w = tg ↦ hw (e.symm ▸ ht)) _ _
  | .andGate _ _ a _ _ _, ha, _, w, hw => Function.update_of_ne (fun e : w = a ↦
    hw (e.symm ▸ ha)) _ _
  | .seq _ _, ⟨h₁, h₂⟩, β, _, hw =>
      (fwdBits_of_not_targetsIn h₂ _ hw).trans (fwdBits_of_not_targetsIn h₁ β hw)
theorem fwdBits_congr_wires {N : ℕ} {S : Wire N → Prop} :
    ∀ {p : ComputeProg N}, ComputeProgWires S p → ∀ {β₁ β₂ : BitAssignment N},
      (∀ w, S w → β₁ w = β₂ w) → ∀ w, S w → p.fwdBits β₁ w = p.fwdBits β₂ w
  | .id, _, _, _, hS, w, hw => hS w hw
  | .x _, hu, _, _, hS, w, hw => by
      simp only [ComputeProg.fwdBits, Function.update_apply, hS _ hu, hS w hw]
  | .cnot c tg _, ⟨hc, htg⟩, _, _, hS, w, hw => by
      simp only [ComputeProg.fwdBits, Function.update_apply, hS c hc, hS tg htg, hS w hw]
  | .andGate c₁ c₂ a _ _ _, ⟨hc₁, hc₂, ha⟩, _, _, hS, w, hw => by
      simp only [ComputeProg.fwdBits, Function.update_apply, hS c₁ hc₁, hS c₂ hc₂,
        hS a ha, hS w hw]
  | .seq _ _, ⟨hp₁, hp₂⟩, _, _, hS, w, hw =>
      fwdBits_congr_wires hp₂ (fun u hu ↦ fwdBits_congr_wires hp₁ hS u hu) w hw
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA

namespace QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open scoped Circuit.Notation
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectQft8GidneyStg3
  PhotochemistrySolution.SplitRouterSeqBell26k PhotochemistrySolution.UnembedIdleAncillas
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.Stage4Kin14Scb
open PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (wrapDyn
    remeasureIf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (bellZHalfVecDyn
    bellXHalfVecDyn cnotFanoutCirc czFanoutCirc)
attribute [local semireducible] SubspaceMbu.wrapDynReg SubspaceMbu.mapCPReg wrapDyn
    remeasureIf xUnloadCzPairsSeqDyn tempAndFanoutDyn KinB.andComputeCircuit
    KinB.andUncomputeDyn SplitBellVecCleanStep.bellZHalfVecDyn SplitBellVecCleanStep.bellXHalfVecDyn
    SplitBellVecCleanStep.cnotFanoutCirc SplitBellVecCleanStep.czFanoutCirc
    SplitBellVecCleanStep.bellZHalf1Dyn SplitBellVecCleanStep.bellXHalf1Dyn
-- Universal DynWires -> CommutesWithDyn bridge, symbolic Dual-Bell 4-port DynWires, and
-- Stage-4 wire combinators.
theorem ancWOfScr_layout : ancWOfScr scrWLayout = 1682 := rfl
/-! ## Section 2: Ambient `QRegister.compose` Lifts & Universal `DynWires -> CommutesWithDyn` -/

theorem eval_gate_swap_eq_polySwapWire2Circ {n : ℕ} (reg : QRegister 2 n) :
    (Circuit.gate .swap reg).eval =
      (polySwapWire2Circ (reg 0) (reg 1) (reg.wires.injective.ne (by decide))).eval := by
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 2).symm ((basisBitsEquiv 2).symm γ)) =
        Function.update (Function.update γ 0 (γ 1)) 1 (γ 0) := by decide
  refine Subtype.ext (PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ ?_)
  rw [ket_polySwapWire2Circ, Circuit.eval_gate, QRegister.embedUnitary_val,
    PrimitiveGate.eval_swap_val, PhotochemistrySolution.KinB.embedMatrix_permMatrix_mulVec_ket,
    PhotochemistrySolution.KinB.localIdx, hloc]
  refine congrArg PhotochemistrySolution.KinB.ket (funext fun w ↦ ?_)
  by_cases hw : w ∈ Set.range reg.wires
  · rcases hw with ⟨i, rfl⟩
    fin_cases i <;> simp [KinB.writeReg_apply_reg, reg.wires.injective.eq_iff]
  · simp [KinB.writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne,
      show w ≠ reg 0 from fun e ↦ hw ⟨0, e.symm⟩, show w ≠ reg 1 from fun e ↦ hw ⟨1, e.symm⟩]
end QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
end

namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open DynamicCircuit Circuit Qubit PrimitiveGate PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectCompactRot34 PhotochemistrySolution.UnembedIdleAncillas
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.ProviderCoreFused
  PhotochemistrySolution.FusedUnembedLGen PhotochemistrySolution.ProviderZeroFloor
abbrev mExt (kExt : ℕ) : ℕ := 80 + kExt
abbrev scrLExt (kExt : ℕ) : ℕ := 1565 - kExt
theorem hpExt (kExt : ℕ) (hk : kExt ≤ 72) : scrLExt kExt + (mExt kExt + 2) ≤ scrWLayout + 70 := by
  dsimp only [scrLExt, mExt, scrWLayout]; omega
theorem rCoinExt_lt {kExt : ℕ} (hk : kExt ≤ 72) (i : Fin kExt) : (7215 - kExt) + i.val <
    dLayout := by change (7215 - kExt) + i.val < 7298; omega
/--
Extra `kExt` LCU coin qubits `dLayout[7215 - kExt .. 7214]` reclaimed from top of `rScrLayout` .
-/
def rCoinExt (kExt : ℕ) (hk : kExt ≤ 72) : QRegister kExt dLayout :=
  ⟨⟨fun i ↦ ⟨(7215 - kExt) + i.val, rCoinExt_lt hk i⟩,
    fun _ _ h ↦ Fin.ext (by have hv := congrArg Fin.val h; dsimp only at hv; omega)⟩⟩
theorem val_rCoinExt {kExt : ℕ} (hk : kExt ≤ 72) (i : Fin kExt) :
    (rCoinExt kExt hk i).val = (7215 - kExt) + i.val := rfl
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
end

noncomputable section
/-- Canonical `0`-wire register `QRegister 0 n`. -/
protected abbrev QuantumComputation.Specs.PhotochemistrySolution.QRegExt.empty (n :
    ℕ) : QRegister 0 n :=
  ⟨⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩⟩
/-- Alias matching `SubspaceStep.trans` dot notation for `SubspaceStep.seq`. -/
abbrev QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec.SubspaceStep.trans :=
    @QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec.SubspaceStep.seq
namespace QuantumComputation.Specs.PhotochemistrySolution.Word73PotPool

infixr:60 " ;; " => DynamicCircuit.seq
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
  writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.SubregMBUCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec (openBoxDist1D)
attribute [local semireducible]
  PhotochemistrySolution.SubregMBUCore.onRegCP
  PhotochemistrySolution.SubregMBUCore.wrapDynOnReg
  PhotochemistrySolution.SubregMBUCore.uStageOfCP
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  PhotochemistrySolution.DynQromUncompA.wrapDyn
theorem pDitePos {P : Prop} [Decidable P] {α : Sort*} (h : P) {a : P → α}
    {b : ¬ P → α} : dite P a b = a h := by split_ifs; rfl
theorem pDiteNeg {P : Prop} [Decidable P] {α : Sort*} (h : ¬ P) {a : P → α}
    {b : ¬ P → α} : dite P a b = b h := by split_ifs; rfl
def openBoxDist3DSq (u v : Fin 3 → Fin 256) : ℕ :=
    openBoxDist1D (u 0) (v 0) ^ 2 + openBoxDist1D (u 1) (v 1) ^ 2 + openBoxDist1D (u 2) (v 2) ^ 2
theorem openBoxDist3DSq_le (u v : Fin 3 → Fin 256) : openBoxDist3DSq u v ≤ 195075 := by
  have h1 (i) : openBoxDist1D (u i) (v i) ≤ 255 := by
    match (ZeroNEremSpec.biasCoord_eq_all (u i)).2, (ZeroNEremSpec.biasCoord_eq_all (v i)).2,
        ZeroNEremSpec.biasCoord_sub_eq_twosComplement (u i) (v i) with
    | _, _, _ => unfold openBoxDist1D; omega
  unfold openBoxDist3DSq
  nlinarith [h1 0, h1 1, h1 2]
end QuantumComputation.Specs.PhotochemistrySolution.Word73PotPool
end

noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectApprox PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.SelectFastFlags
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SelectOracles
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open PhotochemistrySolution.SelectSandwich PhotochemistrySolution.XMeasChunkQromUnldA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign sqrtHalf
    sqrtHalf_mul_sqrtHalf)
attribute [local irreducible] SpecDefs.systemQubits_frozen ancWOfScr
    PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel
-- 82-qubit Hadamard LCU sandwich
/-! ## Section 1: Polymorphic Algebraic Combinators for Sector Reduction & Involutivity -/

/-- Circuit applying single-qubit Hadamard gates across all `m` wires of register `r`. -/
def hadamardRegCirc {d : ℕ} : (m : ℕ) → QRegister m d → Circuit d
  | 0, _ => .identity
  | m + 1, r => .seq (Circuit.H (r 0)) (hadamardRegCirc m (tailReg r))
theorem eval_hadamardRegCirc {d : ℕ} (wAnc : Wire d) :
    ∀ (m : ℕ) (r : QRegister m d) (hdisj : ∀ i, r i ≠ wAnc),
      (hadamardRegCirc m r).eval = (hadamardRegSym (Var := Unit) wAnc m r hdisj).unitary
  | 0, _, _ => Circuit.eval_identity
  | m + 1, r, hdisj =>
      congrArg (· * (Circuit.H (r 0)).eval)
        (eval_hadamardRegCirc wAnc m (tailReg r) fun j ↦ hdisj j.succ)
theorem counts_hadamardRegCirc {d : ℕ} :
    ∀ (m : ℕ) (r : QRegister m d),
      (hadamardRegCirc m r).count .T = 0 ∧ (hadamardRegCirc m r).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, r => (counts_hadamardRegCirc m (tailReg r)).imp (zero_add _).trans (zero_add _).trans
theorem circWires_hadamardRegCirc {d : ℕ} {S : Wire d → Prop} :
    ∀ (m : ℕ) (r : QRegister m d), (∀ i : Fin m, S (r i)) → CircWires S (hadamardRegCirc m r)
  | 0, _, _ => trivial
  | m + 1, r, hS => ⟨cw_1 (hS 0), circWires_hadamardRegCirc m (tailReg r) fun j ↦ hS j.succ⟩
theorem circWires_onRegister {d n : ℕ} {P : Wire d → Prop} {S : Wire n → Prop}
    (rTot : QRegister d n) (hP : ∀ w, P w → S (rTot w)) :
    ∀ {c : Circuit d}, CircWires P c → CircWires S (c.onRegister rTot)
  | .identity, _ => trivial
  | .gate _ reg, hc => fun i ↦ hP (reg i) (hc i)
  | .seq _ _, ⟨h₁, h₂⟩ =>
      ⟨circWires_onRegister rTot hP h₁, circWires_onRegister rTot hP h₂⟩
theorem hDisjHad82_layout (i : Fin 82) : rLcu82Layout i ≠ wHasN1 := fun e ↦ by
  match (val_rLcu82Layout i).symm.trans ((congrArg Fin.val e).trans (val_rOut40Layout _)) with
  | _ => omega
/-- Unitary of the 82-qubit Hadamard LCU preparation register on `dLayout`. -/
noncomputable def uHad82Layout : Unitary (2 ^ dLayout) :=
  (hadamardRegSym (Var := Unit) wHasN1 82 rLcu82Layout hDisjHad82_layout).unitary
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.Sub5885
open PhotochemistrySolution.SelectCompactRot34 PhotochemistrySolution.UnembedIdleAncillas
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCoreFused
  PhotochemistrySolution.FusedUnembedLGen PhotochemistrySolution.ProviderZeroFloor
open PhotochemistrySolution.Coin70Lift
/-- `Decidable`-diamond-immune `ite` on `a < b` pinned to `Nat.decLt`. -/
@[inline] def natIte {α : Sort _} (a b : ℕ) (t e : α) : α :=
  @ite α (a < b) (Nat.decLt a b) t e
/-- `Decidable`-diamond-immune `dite` on `a < b` pinned to `Nat.decLt`. -/
@[inline] def natDIte {α : Sort _} (a b : ℕ) (t : a < b → α) (e : ¬ a < b → α) : α :=
    @dite α (a < b) (Nat.decLt a b) t e
theorem natIte_left {α : Sort _} {a b : ℕ} {t e : α} (h : a < b) : natIte a b t e = t :=
  ite_eq_left h
theorem natIte_right {α : Sort _} {a b : ℕ} {t e : α} (h : ¬ a < b) : natIte a b t e = e :=
  ite_eq_right h
theorem natDIte_left {α : Sort _} {a b : ℕ} {t : a < b → α} {e : ¬ a < b → α} (h : a < b) :
    natDIte a b t e = t h := dite_eq_left h
theorem natDIte_right {α : Sort _} {a b : ℕ} {t : a < b → α} {e : ¬ a < b → α} (h : ¬ a < b) :
    natDIte a b t e = e h := dite_eq_right h
end QuantumComputation.Specs.PhotochemistrySolution.Sub5885

namespace QuantumComputation.Specs.PhotochemistrySolution.Sub5885
open PhotochemistrySolution.SelectCompactRot34 PhotochemistrySolution.SelectCsa64ThreeSpec
  PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.UnembedIdleAncillas
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCoreFused PhotochemistrySolution.FusedUnembedLGen
  PhotochemistrySolution.ProviderZeroFloor PhotochemistrySolution.Coin70Lift
attribute [local irreducible] systemQubits_frozen ancWOfScr
/-- Width-polymorphic active-wire predicate on `m` ambient wires. -/
def SafeConcatGen (Pred : Wire dLayout → Prop) {m : ℕ} (rS : QRegister systemQubits_frozen m)
    (rA : QRegister (ancWOfScr scrWLayout) m) (u : Wire m) : Prop :=
    ∃ (hd : rS.DisjointWires rA) (w : Wire dLayout), Pred w ∧ u = (rS.concat rA hd) w
end QuantumComputation.Specs.PhotochemistrySolution.Sub5885

namespace QuantumComputation.Specs.PhotochemistrySolution.DepthArithWalk
set_option exponentiation.threshold 8192
open PhotochemistrySolution.OvBidir PhotochemistrySolution.SelectCompactRot34
  PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.UnembedIdleAncillas
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.Sub5885
attribute [local irreducible] systemQubits_frozen ancWOfScr
/--
Asymmetric bidirectional QSP total `T` -count bound `d * (tUsel + tFixed) + 2 * tCsel + tInit` .
-/
abbrev bidirTotalTAsym (d tUsel tCsel tFixed tInit : ℕ) : ℕ :=
    d * (tUsel + tFixed) + 2 * tCsel + tInit
theorem hSliceGrad3Hi {ancW : ℕ} (hAnc : 100 ≤ ancW) : 31 + 3 ≤ ancW := by omega
/-- Top-3 retired phase-gradient slice `ancIdx 31..33` (`rCat[5..7]`). -/
def locGrad3HiGen {ancW : ℕ} (hAnc : 100 ≤ ancW) : QRegister 3 (systemQubits_frozen + ancW) :=
  (locAncGen ancW).slice 31 3 (hSliceGrad3Hi hAnc)
/-- Compact-layout top-3 retired phase-gradient slice `ancIdx 31..33`. -/
def locGrad3HiCompactGen (scrW : ℕ) : QRegister 3 (totDimCompactGen scrW) :=
  locGrad3HiGen (hAncCompact scrW)
/-- Concrete `dLayout = 7298` top-3 retired phase-gradient register `{5647, 5648, 5649}`. -/
abbrev locGrad3HiLayout : QRegister 3 dLayout :=
  locGrad3HiCompactGen scrWLayout
end QuantumComputation.Specs.PhotochemistrySolution.DepthArithWalk
end
end
