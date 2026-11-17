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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.ClusterXnorFastQft8
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage4KineticComparator

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 8192

noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn fwdCirc_mulVec_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
noncomputable section

open QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
open QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

theorem qreg_bwv_gridSelectOdd {n : ℕ} (o w : ℕ) (h : o + w ≤ n) (i : Fin w) :
    (_root_.QRegister.block o w h).wires i = ⟨o + i.val, by omega⟩ := rfl
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.SelectDataBuilder
open PhotochemistrySolution.TargetBScr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
theorem ancWOfScr_layout_odd : ancWOfScr scrWLayout = 1682 := rfl
attribute [local irreducible] SpecDefs.systemQubits_frozen
  PhotochemistrySolution.SelectCompactAnc.ancWOfScr
theorem embedMatrix_eq_of_ketMap {d n : ℕ} (r : QRegister d n) (A : Operator (2 ^ d))
    (B : Operator (2 ^ n)) (c : BitAssignment d → ℂ) (g : BitAssignment d → BitAssignment d)
    (hA : ∀ α, A.mulVec (KinB.ket α) = c α • KinB.ket (g α))
    (hB : ∀ β, B.mulVec (KinB.ket β) =
    c (fun k ↦ β (r k)) • KinB.ket (DynCircExt.writeReg β r (g (fun k ↦ β (r k))))) :
    r.embedMatrix A = B := by
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ ?_
  rw [embedMatrix_mulVec_ket_sym, hB]
  have hr : (basisBitsEquiv d).symm (fun k ↦ β (r k)) = readRegIdx r β :=
    (congrArg (basisBitsEquiv d).symm (funext fun k ↦ ((QRegExt.basisBits_extractIdx r) _ k).trans
      (congrFun ((basisBitsEquiv n).apply_symm_apply β) _))).symm.trans
      ((basisBitsEquiv d).symm_apply_apply _)
  have hc (l) : A l (readRegIdx r β) = if l = (basisBitsEquiv d).symm (g fun k ↦ β (r k))
      then c fun k ↦ β (r k) else 0 := by
    simpa [PhotochemistrySolution.KinB.ket, basisState, Matrix.mulVec, dotProduct,
      Pi.single_apply, hr, eq_comm] using congrFun (hA fun k ↦ β (r k)) l
  simp [hc, ite_smul, (basisBitsEquiv d).apply_symm_apply]
theorem comm_embedMatrix_of_isPhaseDiag {d k : ℕ} {U : Operator (2 ^ d)}
    {φ : BitAssignment d → ZMod 2} (hU : IsPhaseDiag U φ) (r : QRegister k d) (M : Operator (2 ^ k))
    (hind : ∀ β (γ : BitAssignment k), φ (DynCircExt.writeReg β r γ) = φ β) :
    Commute U (r.embedMatrix M) := by
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, embedMatrix_mulVec_ket_sym r M β,
      Matrix.mulVec_sum, hU β, Matrix.mulVec_smul, embedMatrix_mulVec_ket_sym r M β,
      Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by
    rw [Matrix.mulVec_smul, hU, hind β _, smul_smul, mul_comm (M l _), ← smul_smul]
theorem hoffIndex_bounds_layout {k : ℕ}
    {r : QRegister k (systemQubits_frozen + ancWOfScr scrWLayout)}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r) (i : Fin k) : (5616 ≤ (r i).val ∧ (r i).val < 5650) ∨ (r i).val =
    7297 := by
  obtain ⟨u, hru, hnl, hns⟩ := hoff i
  have : systemQubits_frozen = 5616 ∧ u.val < 1682 := ⟨hSys5616, ancWOfScr_layout_odd ▸ u.isLt⟩
  have hv : (r i).val = 5616 + u.val := by
    have e := congrArg Fin.val hru.symm
    dsimp [locAncPoly, qreg_bwv_gridSelectOdd, QRegister.block_apply_val] at e; omega
  exact if h1 : u.val < 34 then .inl ⟨by omega, by omega⟩
    else if h2 : u.val < 1599 then (hns ⟨⟨u.val - 34, by unfold scrLLayout; omega⟩, Fin.ext (by
      dsimp [scrSubLGen, qreg_bwv_gridSelectOdd, QRegister.block_apply_val]; omega)⟩).elim
    else if h3 : u.val < 1681 then (hnl ⟨⟨u.val - 1599, by unfold mLayout; omega⟩,
      Fin.ext (by simp [lcuSubLGen, QRegister.block_apply_val, scrLLayout]; omega)⟩).elim
    else .inr (by omega)
theorem hoff_cat8_layout :
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) (locCat8SharedCompactGen scrWLayout) := by
  refine fun i ↦ ⟨⟨26 + i.val, by rw [ancWOfScr_layout_odd]; omega⟩, Fin.ext (by
    dsimp [locCat8SharedCompactGen, locAncCompactGen, locAncPoly, QRegister.compose,
      qreg_bwv_gridSelectOdd, QRegister.block_apply_val]; omega), ?_, ?_⟩
  · exact fun ⟨j, hj⟩ ↦ by have hv : 1599 + j.val = 26 + i.val := congrArg Fin.val hj; omega
  · exact fun ⟨j, hj⟩ ↦ by have hv : 34 + j.val = 26 + i.val := congrArg Fin.val hj; omega
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
end

noncomputable section
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix HermitianMat QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k
/- ## Section 2: `portSwap1Circ` / `portSwapVecCirc` & Exact Unextraction Identity -/

/-- Swaps `qB ↔ wTgt p` whenever `wCtrl p = 1` across `p : Fin M`. -/
def portSwap1Circ {n : ℕ} : (M : ℕ) → (qB : Wire n) → (wCtrl wTgt : Fin M → Wire n) →
    (∀ p : Fin M, qB ≠ wCtrl p) → (∀ p : Fin M, qB ≠ wTgt p) →
    (∀ p : Fin M, wCtrl p ≠ wTgt p) → Circuit n
  | 0, _, _, _, _, _, _ => .identity
  | M + 1, qB, wCtrl, wTgt, hbc, hbt, hct =>
      portSwap1Circ M qB (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc)
        (fun p ↦ hbc p.castSucc) (fun p ↦ hbt p.castSucc) (fun p ↦ hct p.castSucc) ;;ᶜ
      (Circuit.CNOT qB (wTgt (Fin.last M)) (hbt (Fin.last M)) ;;ᶜ
       Circuit.TOFF (wCtrl (Fin.last M)) (wTgt (Fin.last M)) qB
         (hct (Fin.last M)) (hbc (Fin.last M)).symm (hbt (Fin.last M)).symm ;;ᶜ
       Circuit.CNOT qB (wTgt (Fin.last M)) (hbt (Fin.last M)))
/-- Bit-level effect of `portSwap1Circ` on a basis assignment. -/
def portSwap1Bits {n : ℕ} : (M : ℕ) → (qB : Wire n) → (wCtrl wTgt : Fin M → Wire n) →
    BitAssignment n → BitAssignment n
  | 0, _, _, _, β => β
  | M + 1, qB, wCtrl, wTgt, β =>
      let β' := portSwap1Bits M qB (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc) β
      let d := β' (wCtrl (Fin.last M)) * (β' (wTgt (Fin.last M)) + β' qB)
      Function.update (Function.update β' qB (β' qB + d))
        (wTgt (Fin.last M)) (β' (wTgt (Fin.last M)) + d)
theorem portSwap1Circ_mulVec_ket {n : ℕ} : ∀ (M : ℕ) (qB : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (hbc : ∀ p : Fin M, qB ≠ wCtrl p) (hbt : ∀ p : Fin M, qB ≠ wTgt p)
    (hct : ∀ p : Fin M, wCtrl p ≠ wTgt p) (β : BitAssignment n),
    (portSwap1Circ M qB wCtrl wTgt hbc hbt hct).eval.1.mulVec (ket β) =
      ket (portSwap1Bits M qB wCtrl wTgt β)
  | 0, _, _, _, _, _, _, β => by
      rw [portSwap1Circ, portSwap1Bits, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | M + 1, qB, wCtrl, wTgt, hbc, hbt, hct, β => by
      rw [portSwap1Circ, portSwap1Bits, eval_seq_mulVec, portSwap1Circ_mulVec_ket M qB _ _ _ _ _ β,
        eval_seq_mulVec, eval_seq_mulVec, ket_CNOT, ket_TOFF, ket_CNOT,
        Function.update_of_ne (hbt (Fin.last M)), Function.update_of_ne (hct (Fin.last M)),
        Function.update_self, Function.update_of_ne (hbt (Fin.last M)).symm, Function.update_self]
      exact congrArg ket (funext fun w ↦ by
        by_cases hwT : w = wTgt (Fin.last M) <;> by_cases hwB : w = qB <;>
          simp [hwT, hwB, hbt (Fin.last M), z2_cswap_tgt])
theorem portSwap1Bits_of_all_zero {n : ℕ} : ∀ (M : ℕ) (qB : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (_hc_disj : ∀ p q : Fin M, wCtrl p ≠ wTgt q) (_hbc : ∀ p : Fin M, qB ≠ wCtrl p)
    (β : BitAssignment n), (∀ p : Fin M, β (wCtrl p) = 0) →
    portSwap1Bits M qB wCtrl wTgt β = β
  | 0, _, _, _, _, _, _, _ => rfl
  | M + 1, qB, wCtrl, wTgt, hc_disj, hbc, β, hz => by
      have hih :=
          portSwap1Bits_of_all_zero M qB (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc)
          (fun p q ↦ hc_disj p.castSucc q.castSucc) (fun p ↦ hbc p.castSucc) β (fun p ↦
          hz p.castSucc)
      simp only [portSwap1Bits, hih, hz (Fin.last M), zero_mul, add_zero, Function.update_eq_self]
theorem portSwap1Bits_of_unique_one {n : ℕ} : ∀ (M : ℕ) (qB : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (_hbc : ∀ p : Fin M, qB ≠ wCtrl p) (_hbt : ∀ p : Fin M, qB ≠ wTgt p)
    (_hc_disj : ∀ p q : Fin M, wCtrl p ≠ wTgt q)
    (_ht_inj : ∀ p q : Fin M, p ≠ q → wTgt p ≠ wTgt q)
    (β : BitAssignment n) (p₀ : Fin M),
    β (wCtrl p₀) = 1 → (∀ p : Fin M, p ≠ p₀ → β (wCtrl p) = 0) →
    portSwap1Bits M qB wCtrl wTgt β =
      Function.update (Function.update β qB (β (wTgt p₀))) (wTgt p₀) (β qB)
  | 0, _, _, _, _, _, _, _, _, p₀, _, _ => p₀.elim0
  | M + 1, qB, wCtrl, wTgt, hbc, hbt, hc_disj, ht_inj, β, p₀, hp₁, hp₀ => by
      induction p₀ using Fin.lastCases with
      | last =>
          rcases z2_cswap_1 (β (wTgt (Fin.last M))) (β qB) with ⟨hc1, hc2⟩
          rw [portSwap1Bits, portSwap1Bits_of_all_zero M qB _ _ (fun p q ↦
              hc_disj p.castSucc q.castSucc)
            (fun p ↦ hbc p.castSucc) β (fun p ↦ hp₀ p.castSucc (Fin.castSucc_ne_last p)), hp₁, hc1,
                hc2]
      | cast p' =>
          simp only [portSwap1Bits, portSwap1Bits_of_unique_one M qB _ _ (fun p ↦ hbc p.castSucc)
            (fun p ↦ hbt p.castSucc) (fun p q ↦ hc_disj p.castSucc q.castSucc)
            (fun p q h ↦ ht_inj p.castSucc q.castSucc (Fin.castSucc_inj.mp · |> h)) β p' hp₁
            (fun p hp ↦ hp₀ p.castSucc (Fin.castSucc_inj.mp · |> hp)),
                Function.update_of_ne (hc_disj _ _),
            Function.update_of_ne (hbc _).symm, hp₀ (Fin.last M) (Fin.castSucc_ne_last p').symm,
            zero_mul, add_zero, Function.update_eq_self]
/-- `m`-plane vector port-swap circuit across bit-planes `0 .. m - 1`. -/
def portSwapVecCirc {n : ℕ} (M : ℕ) : (m : ℕ) → (qB : Fin m → Wire n) →
    (wCtrl : Fin M → Wire n) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ (k : Fin m) (p : Fin M), qB k ≠ wCtrl p) →
    (∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p) →
    (∀ (k : Fin m) (p : Fin M), wCtrl p ≠ wTgt k p) → Circuit n
  | 0, _, _, _, _, _, _ => .identity
  | m + 1, qB, wCtrl, wTgt, hbc, hbt, hct =>
      portSwapVecCirc M m (fun k ↦ qB k.castSucc) wCtrl (fun k ↦ wTgt k.castSucc)
        (fun k ↦ hbc k.castSucc) (fun k ↦ hbt k.castSucc) (fun k ↦ hct k.castSucc) ;;ᶜ
      portSwap1Circ M (qB (Fin.last m)) wCtrl (wTgt (Fin.last m))
        (hbc (Fin.last m)) (hbt (Fin.last m)) (hct (Fin.last m))
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k

namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
/-! ## Section 6: Fixed-Control Pure Circuit `cFixedRouterCirc` & Conjugation Ket Identity -/

/--
Subspace predicate on quantum state vectors `ψ : Fin (2 ^ n) → ℂ`: any two operators agreeing on
all computational basis kets `ket α` with `P α` act identically on `ψ`.
-/
def PreservesKetPred {n : ℕ} (P : BitAssignment n → Prop) (ψ : Fin (2 ^ n) → ℂ) : Prop :=
    ∀ (A B : Operator (2 ^ n)), (∀ α : BitAssignment n, P α → A.mulVec (ket α) = B.mulVec (ket α)) →
    A.mulVec ψ = B.mulVec ψ
theorem preservesKetPred_ket {n : ℕ} {P : BitAssignment n → Prop} {α : BitAssignment n}
    (hα : P α) : PreservesKetPred P (ket α) := fun _ _ h ↦ h α hα
theorem preservesKetPred_add {n : ℕ} {P : BitAssignment n → Prop} {ψ₁ ψ₂ : Fin (2 ^ n) → ℂ}
    (h₁ : PreservesKetPred P ψ₁) (h₂ : PreservesKetPred P ψ₂) : PreservesKetPred P (ψ₁ + ψ₂) :=
  fun A B h ↦ by simp only [Matrix.mulVec_add, h₁ A B h, h₂ A B h]
theorem preservesKetPred_smul {n : ℕ} {P : BitAssignment n → Prop} (c : ℂ) {ψ : Fin (2 ^ n) → ℂ}
    (h₁ : PreservesKetPred P ψ) : PreservesKetPred P (c • ψ) :=
  fun A B h ↦ by simp only [Matrix.mulVec_smul, h₁ A B h]
theorem preservesKetPred_mulVec_of_ket {n : ℕ} {P : BitAssignment n → Prop} {U : Operator (2 ^ n)}
    (hU : ∀ α : BitAssignment n, P α → PreservesKetPred P (U.mulVec (ket α))) {ψ : Fin (2 ^ n) → ℂ}
    (hψ : PreservesKetPred P ψ) : PreservesKetPred P (U.mulVec ψ) :=
  fun A B h ↦ by
    simpa only [Matrix.mulVec_mulVec] using hψ (A * U) (B * U) fun α hα ↦ by
      simpa only [Matrix.mulVec_mulVec] using hU α hα A B h
/-- Classical-control CNOT fanout circuit touching ONLY `qSrc` and `wTgt p`. -/
def fixedFanoutCirc {n : ℕ} : (M : ℕ) → (qSrc : Wire n) → (cVec : Fin M → ZMod 2) →
    (wTgt : Fin M → Wire n) → (∀ p : Fin M, qSrc ≠ wTgt p) → Circuit n
  | 0, _, _, _, _ => .identity
  | M + 1, qSrc, cVec, wTgt, hst =>
      fixedFanoutCirc M qSrc (fun p ↦ cVec p.castSucc) (fun p ↦ wTgt p.castSucc)
        (fun p ↦ hst p.castSucc) ;;ᶜ
      (if cVec (Fin.last M) = 1 then
        Circuit.CNOT qSrc (wTgt (Fin.last M)) (hst (Fin.last M))
      else .identity)
/-- Classical-control single-plane Bell entangler `H ;;ᶜ fixedFanoutCirc`. -/
def fixedBell1Circ {n : ℕ} (M : ℕ) (qH : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
    (hht : ∀ p : Fin M, qH ≠ wTgt p) : Circuit n :=
  Circuit.H qH ;;ᶜ fixedFanoutCirc M qH cVec wTgt hht
/-- Classical-control 3-CNOT swap sweep touching ONLY `qB` and `wTgt p`. -/
def fixedSwap1Circ {n : ℕ} : (M : ℕ) → (qB : Wire n) → (cVec : Fin M → ZMod 2) →
    (wTgt : Fin M → Wire n) → (∀ p : Fin M, qB ≠ wTgt p) → Circuit n
  | 0, _, _, _, _ => .identity
  | M + 1, qB, cVec, wTgt, hbt =>
      fixedSwap1Circ M qB (fun p ↦ cVec p.castSucc) (fun p ↦ wTgt p.castSucc)
        (fun p ↦ hbt p.castSucc) ;;ᶜ
      (if cVec (Fin.last M) = 1 then
        Circuit.CNOT qB (wTgt (Fin.last M)) (hbt (Fin.last M)) ;;ᶜ
        Circuit.CNOT (wTgt (Fin.last M)) qB (hbt (Fin.last M)).symm ;;ᶜ
        Circuit.CNOT qB (wTgt (Fin.last M)) (hbt (Fin.last M))
      else .identity)
/-- Multi-plane vector classical-control swap sweep across `m` bit-planes. -/
def fixedSwapVecCirc {n : ℕ} (M : ℕ) : (m : ℕ) → (qB : Fin m → Wire n) →
    (cVec : Fin M → ZMod 2) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p) → Circuit n
  | 0, _, _, _, _ => .identity
  | m + 1, qB, cVec, wTgt, hbt =>
      fixedSwapVecCirc M m (fun k ↦ qB k.castSucc) cVec (fun k ↦ wTgt k.castSucc)
        (fun k ↦ hbt k.castSucc) ;;ᶜ
      fixedSwap1Circ M (qB (Fin.last m)) cVec (wTgt (Fin.last m)) (hbt (Fin.last m))
/-- Multi-plane vector classical-control Bell entangler across `m` bit-planes. -/
def fixedBellVecCirc {n : ℕ} (M : ℕ) : (m : ℕ) → (qH : Fin m → Wire n) →
    (cVec : Fin M → ZMod 2) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ (k : Fin m) (p : Fin M), qH k ≠ wTgt k p) → Circuit n
  | 0, _, _, _, _ => .identity
  | m + 1, qH, cVec, wTgt, hht =>
      fixedBellVecCirc M m (fun k ↦ qH k.castSucc) cVec (fun k ↦ wTgt k.castSucc)
        (fun k ↦ hht k.castSucc) ;;ᶜ
      fixedBell1Circ M (qH (Fin.last m)) cVec (wTgt (Fin.last m)) (hht (Fin.last m))
/--
Pure circuit on `AllPlaneMod r` executing the 24-plane dual-Bell router for fixed one-hot
vectors `cLo cHi : Fin M → ZMod 2`.
-/
def cFixedRouterCirc {M D n : ℕ} (r : RouterReg M D n) (cLo cHi : Fin M → ZMod 2) : Circuit n :=
  fixedSwapVecCirc M 24 (rBufLo r) cLo (fun b p ↦ rSys r p b)
    (fun b p ↦ rr_ne r (by have := b.isLt; have := p.isLt; dsimp; omega)) ;;ᶜ
  fixedSwapVecCirc M 24 (rBufHi r) cHi (fun b p ↦ rSys r p b)
    (fun b p ↦ rr_ne r (by have := b.isLt; have := p.isLt; dsimp; omega)) ;;ᶜ
  fixedBellVecCirc M 24 (rHA r) cLo (fun b p ↦ rSys r p b)
    (fun b p ↦ rr_ne r (by have := b.isLt; have := p.isLt; dsimp; omega)) ;;ᶜ
  fixedBellVecCirc M 24 (rHB r) cHi (fun b p ↦ rSys r p b)
    (fun b p ↦ rr_ne r (by have := b.isLt; have := p.isLt; dsimp; omega))
theorem preservesKetPred_CNOT {n : ℕ} {P : BitAssignment n → Prop} {c t : Wire n} (h : c ≠ t)
    (hUpd : ∀ α v, P α → P (Function.update α t v)) {ψ : Fin (2 ^ n) → ℂ}
    (hψ : PreservesKetPred P ψ) : PreservesKetPred P ((Circuit.CNOT c t h).eval.1.mulVec ψ) :=
  preservesKetPred_mulVec_of_ket (fun α hα ↦
      by simpa only [ket_CNOT] using preservesKetPred_ket (hUpd α _ hα)) hψ
theorem preservesKetPred_H {n : ℕ} {P : BitAssignment n → Prop} {q : Wire n}
    (hUpd : ∀ α v, P α → P (Function.update α q v)) {ψ : Fin (2 ^ n) → ℂ}
    (hψ : PreservesKetPred P ψ) : PreservesKetPred P ((Circuit.H q).eval.1.mulVec ψ) :=
  preservesKetPred_mulVec_of_ket (fun α hα ↦ by
    rw [PhotochemistrySolution.SplitBellVecCleanStep.ket_H_apply]
    exact preservesKetPred_smul _ (preservesKetPred_add (preservesKetPred_ket (hUpd α 0 hα))
      (preservesKetPred_smul _ (preservesKetPred_ket (hUpd α 1 hα))))) hψ
theorem preservesKetPred_fixedFanout {n : ℕ} {P : BitAssignment n → Prop} :
    ∀ (M : ℕ) (qSrc : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (hst : ∀ p, qSrc ≠ wTgt p)
      (_hUpdT : ∀ p α v, P α → P (Function.update α (wTgt p) v))
      {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
      PreservesKetPred P ((fixedFanoutCirc M qSrc cVec wTgt hst).eval.1.mulVec ψ)
  | 0, _, _, _, _, _, _, hψ => by simpa [fixedFanoutCirc] using hψ
  | M + 1, qSrc, cVec, wTgt, hst, hUpdT, _, hψ => by
      have h₁ :=
          preservesKetPred_fixedFanout M qSrc (cVec ·.castSucc) (wTgt ·.castSucc) (hst ·.castSucc)
          (hUpdT ·.castSucc) hψ
      dsimp only [fixedFanoutCirc]
      exact if h : cVec (.last M) =
          1 then by simpa [eval_seq_mulVec, h] using preservesKetPred_CNOT _ (hUpdT _) h₁
        else by simpa [eval_seq_mulVec, h] using h₁
theorem preservesKetPred_fixedSwap1 {n : ℕ} {P : BitAssignment n → Prop} :
    ∀ (M : ℕ) (qB : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (hbt : ∀ p, qB ≠ wTgt p)
      (_hUpdB : ∀ α v, P α → P (Function.update α qB v))
      (_hUpdT : ∀ p α v, P α → P (Function.update α (wTgt p) v))
      {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
      PreservesKetPred P ((fixedSwap1Circ M qB cVec wTgt hbt).eval.1.mulVec ψ)
  | 0, _, _, _, _, _, _, _, hψ => by simpa [fixedSwap1Circ] using hψ
  | M + 1, qB, cVec, wTgt, hbt, hUpdB, hUpdT, _, hψ => by
      have h₁ :=
          preservesKetPred_fixedSwap1 M qB (cVec ·.castSucc) (wTgt ·.castSucc)
          (hbt ·.castSucc) hUpdB (hUpdT ·.castSucc) hψ
      rw [fixedSwap1Circ, eval_seq_mulVec]; split_ifs <;> try simpa using h₁
      rw [eval_seq_mulVec, eval_seq_mulVec]
      exact preservesKetPred_CNOT _ (hUpdT _)
          (preservesKetPred_CNOT _ hUpdB (preservesKetPred_CNOT _ (hUpdT _) h₁))
theorem toff_fanout_leaf_eq {n : ℕ} {P : BitAssignment n → Prop} {qSrc c t₁ t₂ : Wire n}
    (ht : t₁ = t₂) (hsc : qSrc ≠ c) (hst₁ : qSrc ≠ t₁) (hct₁ : c ≠ t₁) (hst₂ : qSrc ≠ t₂)
    {b : ZMod 2} (hC : ∀ α, P α → α c = b) {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    (Circuit.TOFF qSrc c t₁ hsc hst₁ hct₁).eval.1.mulVec ψ =
    (if b = 1 then Circuit.CNOT qSrc t₂ hst₂ else .identity).eval.1.mulVec ψ := by
  subst ht
  refine hψ _ _ fun α hα ↦ ?_
  rcases bit_cases b with rfl | rfl <;>
    simp only [zero_ne_one, ↓reduceIte, ket_TOFF, ket_CNOT, Circuit.eval_identity,
        Submonoid.coe_one, Matrix.one_mulVec] <;>
    exact congrArg ket (funext fun u ↦ by by_cases hu : u = t₁ <;> simp [hu, hC α hα])
theorem toff_cswap_leaf_eq {n : ℕ} {P : BitAssignment n → Prop}
    {qB c t₁ t₂ : Wire n} (ht : t₁ = t₂) (hbc : qB ≠ c) (hbt₁ : qB ≠ t₁) (hct₁ : c ≠ t₁)
    (hbt₂ : qB ≠ t₂) {b : ZMod 2} (hC : ∀ α, P α → α c = b)
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    (Circuit.CNOT qB t₁ hbt₁ ;;ᶜ Circuit.TOFF c t₁ qB hct₁ hbc.symm hbt₁.symm ;;ᶜ
      Circuit.CNOT qB t₁ hbt₁).eval.1.mulVec ψ =
      (if b = 1 then
        Circuit.CNOT qB t₂ hbt₂ ;;ᶜ Circuit.CNOT t₂ qB hbt₂.symm ;;ᶜ Circuit.CNOT qB t₂ hbt₂
      else .identity).eval.1.mulVec ψ := by
  subst ht
  refine hψ _ _ fun α hα ↦ ?_
  rcases bit_cases b with rfl | rfl <;>
    simp only [zero_ne_one, ↓reduceIte, eval_seq_mulVec, ket_CNOT, ket_TOFF, Circuit.eval_identity,
        Submonoid.coe_one, one_mulVec] <;>
    exact congrArg ket (funext fun u ↦ by
      by_cases huT : u = t₁ <;> by_cases huB : u = qB <;>
        simp [huT, huB, hbt₁, hbt₁.symm, hct₁, hC α hα, show ∀ x y : ZMod 2, x + y + y =
            x by decide +revert])
theorem portSwapVec_eq_fixedSwapVec {n : ℕ} {P : BitAssignment n → Prop} (M : ℕ)
    (wCtrl : Fin M → Wire n) (cVec : Fin M → ZMod 2) (hC : ∀ p α, P α → α (wCtrl p) = cVec p) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wTgt₁ wTgt₂ : Fin m → Fin M → Wire n)
      (_hT : ∀ k p, wTgt₁ k p = wTgt₂ k p)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt₁ : ∀ k p, qB k ≠ wTgt₁ k p)
      (hct : ∀ k p, wCtrl p ≠ wTgt₁ k p) (hbt₂ : ∀ k p, qB k ≠ wTgt₂ k p)
      (_hUpdB : ∀ k α v, P α → P (Function.update α (qB k) v))
      (_hUpdT : ∀ k p α v, P α → P (Function.update α (wTgt₂ k p) v))
      {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
      (portSwapVecCirc M m qB wCtrl wTgt₁ hbc hbt₁ hct).eval.1.mulVec ψ =
        (fixedSwapVecCirc M m qB cVec wTgt₂ hbt₂).eval.1.mulVec ψ ∧
      PreservesKetPred P ((fixedSwapVecCirc M m qB cVec wTgt₂ hbt₂).eval.1.mulVec ψ)
  | 0, _, _, _, _, _, _, _, _, _, _, _, hψ =>
      ⟨by simp [portSwapVecCirc, fixedSwapVecCirc], by simpa [fixedSwapVecCirc] using hψ⟩
  | m + 1, qB, wTgt₁, wTgt₂, hT, hbc, hbt₁, hct, hbt₂, hUpdB, hUpdT, _, hψ => by
      obtain ⟨hEqV, hPV⟩ := portSwapVec_eq_fixedSwapVec M wCtrl cVec hC m _ _ _ (hT ·.castSucc)
        (hbc ·.castSucc) (hbt₁ ·.castSucc) (hct ·.castSucc) (hbt₂ ·.castSucc) (hUpdB ·.castSucc)
            (hUpdT ·.castSucc) hψ
      have hOne : ∀ K {wC cV t₁ t₂ φ} (_ : ∀ p : Fin K, ∀ α, P α → α (wC p) = cV p)
          (_ : ∀ p, t₁ p = t₂ p)
          (hb : ∀ p, qB (.last m) ≠ wC p) (h1 : ∀ p, qB (.last m) ≠ t₁ p) (hc : ∀ p, wC p ≠ t₁ p)
              (h2 : ∀ p, qB (.last m) ≠ t₂ p)
          (_ : ∀ p α v, P α → P (Function.update α (t₂ p) v)), PreservesKetPred P φ →
          (portSwap1Circ K (qB (.last m)) wC t₁ hb h1 hc).eval.1.mulVec φ =
              (fixedSwap1Circ K _ cV t₂ h2).eval.1.mulVec φ := fun K ↦ by
        induction K with
        | zero => intros; simp [portSwap1Circ, fixedSwap1Circ]
        | succ K ih =>
            intro _ _ _ _ _ hcK htK hb h1 hc h2 huTK hφ; dsimp only [portSwap1Circ, fixedSwap1Circ]
            rw [eval_seq_mulVec (c₁ := portSwap1Circ K _ _ _ _ _ _), eval_seq_mulVec (c₁ :=
                fixedSwap1Circ K _ _ _ _),
              ih (hcK ·.castSucc) (htK ·.castSucc) (hb ·.castSucc) (h1 ·.castSucc) (hc ·.castSucc)
                  (h2 ·.castSucc) (huTK ·.castSucc) hφ]
            exact toff_cswap_leaf_eq (htK _) (hb _) (h1 _) (hc _) (h2 _) (hcK _)
              (preservesKetPred_fixedSwap1 K _ _ _ (h2 ·.castSucc) (hUpdB _) (huTK ·.castSucc) hφ)
      dsimp only [portSwapVecCirc, fixedSwapVecCirc]; rw [eval_seq_mulVec, eval_seq_mulVec, hEqV]
      exact ⟨hOne M hC (hT _) (hbc _) (hbt₁ _) (hct _) (hbt₂ _) (hUpdT _) hPV,
        preservesKetPred_fixedSwap1 M _ _ _ (hbt₂ _) (hUpdB _) (hUpdT _) hPV⟩
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
end

noncomputable section
open Operator QProg Matrix HermitianMat QuantumComputation.Specs.PhotochemistrySolution
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open scoped ComplexOrder MatrixOrder Circuit.Notation
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (bellZHalfVecDyn
    bellXHalfVecDyn)
attribute [local semireducible] DynamicCircuit.identity Circuit.H Circuit.X Circuit.T Circuit.S
  DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn DynQromUncompA.fwdCirc
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  SplitBellVecCleanStep.cnotFanoutCirc SplitBellVecCleanStep.czFanoutCirc
  SplitBellVecCleanStep.bellZHalf1Dyn SplitBellVecCleanStep.bellXHalf1Dyn
  SplitBellVecCleanStep.bellZHalfVecDyn SplitBellVecCleanStep.bellXHalfVecDyn
/- ## Section 2: `5 * D + 2 * (M - 1)` `TempAND` Classical Prep Program `pPrepMD` & `ValidProg` -/
theorem hne_prep_dec {M D n : ℕ} (r : RouterReg M D n) : (∀ p : Fin M, rHas1 r ≠ rCtrlLo r p) ∧
    (∀ d : Fin D, ∀ p : Fin M, rIdxMin r d ≠ rCtrlLo r p) ∧ (∀ p q : Fin M, p ≠ q → rCtrlLo r p ≠
    rCtrlLo r q) ∧ (∀ p : Fin M, rHas2Eff r ≠ rCtrlHi r p) ∧ (∀ d : Fin D, ∀ p : Fin M,
    rIdxMax r d ≠ rCtrlHi r p) ∧ (∀ p q : Fin M, p ≠ q → rCtrlHi r p ≠ rCtrlHi r q) :=
  ⟨fun p ↦ rr_ne r (by have := p.isLt; unfold basePub; dsimp; omega),
    fun d p ↦ rr_ne r (by have := d.isLt; have := p.isLt; unfold basePub; dsimp; omega),
   fun p q h ↦ rr_ne r (fun e ↦ h (Fin.ext (by dsimp at e; omega))),
    fun p ↦ rr_ne r (by have := p.isLt; unfold basePub; dsimp; omega),
   fun d p ↦ rr_ne r (by have := d.isLt; have := p.isLt; unfold basePub; dsimp; omega),
    fun p q h ↦ rr_ne r (fun e ↦ h (Fin.ext (by dsimp at e; omega)))⟩
def ProgSupportedIn {n : ℕ} (S : Wire n → Prop) : ComputeProg n → Prop
  | .id => True
  | .x u => S u
  | .cnot c t _ => S c ∧ S t
  | .andGate c₁ c₂ a _ _ _ => S c₁ ∧ S c₂ ∧ S a
  | .seq p₁ p₂ => ProgSupportedIn S p₁ ∧ ProgSupportedIn S p₂
/-- Union of all 24 planes' modified wire sets (`rBufLo`, `rBufHi`, `rHA`, `rHB`, `rSys`). -/
def AllPlaneMod {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
    ∃ b : Fin 24, PlaneModSet (planeOfRouter r b) w
theorem not_allPlaneMod_of_idx {M D n : ℕ} (r : RouterReg M D n) {i : Fin (routerWidth M D)}
    (hi : i.val < 2 + 2 * D ∨ basePub M D ≤ i.val) : ¬ AllPlaneMod r (r i) := by
  unfold basePub at hi
  rintro ⟨b, heq | heq | heq | heq | ⟨p, heq⟩⟩ <;> have _ := b.isLt <;> try have _ := p.isLt
  all_goals simp only [planeOfRouter_bufLo, planeOfRouter_bufHi, planeOfRouter_hA, planeOfRouter_hB,
      planeOfRouter_sys] at heq
  all_goals exact (fun h ↦ by dsimp at h; omega) (congrArg Fin.val (r.wires.injective heq))
/-- Prefix integer value `∑_{d < k} 2^d * [β (wBit d) = 1]`. -/
def idxValPrefix {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) : ∀ k : ℕ, k ≤ D → ℕ
  | 0, _ => 0
  | k + 1, hk =>
        idxValPrefix wBit β k (Nat.le_of_succ_le hk) + if β (wBit ⟨k, hk⟩) = 1 then 2 ^ k else 0
/-- Unsigned `D`-bit integer encoded on `wBit : Fin D → Wire n`. -/
def idxValD {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) : ℕ :=
    idxValPrefix wBit β D le_rfl
theorem idxValPrefix_lt_two_pow {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) : ∀ (k : ℕ)
    (hk : k ≤ D), idxValPrefix wBit β k hk < 2 ^ k
  | 0, _ => Nat.zero_lt_one
  | k + 1, hk => by
      have ih := idxValPrefix_lt_two_pow wBit β k (Nat.le_of_succ_le hk)
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      dsimp only [idxValPrefix]; split_ifs <;> omega
theorem testBit_idxValPrefix {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D) (j : ℕ),
      (idxValPrefix wBit β k hk).testBit j =
        if hj : j < k then decide (β (wBit ⟨j, Nat.lt_of_lt_of_le hj hk⟩) = 1) else false
  | 0, _, _ => by simp [idxValPrefix]
  | k + 1, hk, j => by
      have hlt := idxValPrefix_lt_two_pow wBit β k (Nat.le_of_succ_le hk)
      let lo := idxValPrefix wBit β k (Nat.le_of_succ_le hk)
      let hi := if β (wBit ⟨k, hk⟩) = 1 then 2 ^ k else 0
      change (lo + hi).testBit j = _
      by_cases hjk : j < k
      · have htb := congrArg (·.testBit j) (show (lo + hi) % 2 ^ k = lo by
          dsimp only [lo, hi]; split_ifs <;> simp [Nat.add_mod_right, Nat.mod_eq_of_lt hlt])
        rw [Nat.testBit_mod_two_pow, decide_eq_true hjk, Bool.true_and] at htb
        rw [htb, testBit_idxValPrefix wBit β k (Nat.le_of_succ_le hk) j, ditePos hjk,
            ditePos (Nat.lt_succ_of_lt hjk)]
      · by_cases heq : j = k
        · subst heq; rw [ditePos (Nat.lt_succ_self j), Nat.testBit_eq_decide_div_mod_eq];
              dsimp only [lo,
          hi];
            split_ifs with hb1 <;> simp [Nat.add_div_right, Nat.div_eq_of_lt hlt,
                hb1]
        · have hsum_lt : lo + hi < 2 ^ j :=
            Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow wBit β (k + 1) hk)
              (Nat.pow_le_pow_right (by decide) (by omega))
          rw [diteNeg (by omega : ¬ j < k + 1), Nat.testBit_lt_two_pow hsum_lt]
theorem testBit_idxValD {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n)
    (j : ℕ) : (idxValD wBit β).testBit j = if hj : j < D then decide (β (wBit ⟨j, hj⟩) =
    1) else false := testBit_idxValPrefix wBit β D le_rfl j
theorem idxValD_congr {D n : ℕ} {wBit₁ wBit₂ : Fin D → Wire n} {β₁ β₂ : BitAssignment n}
    (h : ∀ d : Fin D,
  β₁ (wBit₁ d) = β₂ (wBit₂ d)) : idxValD wBit₁ β₁ = idxValD wBit₂ β₂ :=
  Nat.eq_of_testBit_eq fun j ↦ by simp only [testBit_idxValD, h]
/-- Unique highest differing bit between distinct `x, y < 2 ^ D` and exact `<` orientation! -/
theorem exists_msb_diff : ∀ {D : ℕ} {x y : ℕ}, x < 2 ^ D → y < 2 ^ D → x ≠ y →
    ∃ dStar : Fin D,
      x.testBit dStar.val ≠ y.testBit dStar.val ∧
      (∀ d : Fin D, dStar.val < d.val → x.testBit d.val = y.testBit d.val) ∧
      (x.testBit dStar.val = false → x < y) ∧
      (x.testBit dStar.val = true → y < x)
  | 0, x, y, hx, hy, hne => absurd (by omega : x = y) hne
  | k + 1, x, y, hx, hy, hne => by
      have hp2 : 0 < 2 ^ k := Nat.two_pow_pos k
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      have h_eq : ∀ {u : ℕ}, u < 2 ^ (k + 1) → u = u % 2 ^ k + if u.testBit k then 2 ^ k else 0 :=
          fun {u} hu ↦ by
        have hlt2 : u / 2 ^ k < 2 := (Nat.div_lt_iff_lt_mul hp2).mpr (by omega)
        have hd := Nat.div_add_mod u (2 ^ k)
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have h01 : u / 2 ^ k = 0 ∨ u / 2 ^ k = 1 := by
          generalize u / 2 ^ k = q at hlt2
          omega
        rcases h01 with hq | hq <;> simp [hq] at hd ⊢ <;> omega
      have hxE := h_eq hx
      have hyE := h_eq hy
      by_cases htop : x.testBit k = y.testBit k
      · obtain ⟨dS, hneS, hhiS, h0S, h1S⟩ := exists_msb_diff (Nat.mod_lt x hp2)
          (Nat.mod_lt y hp2) fun heq ↦ hne (by rw [hxE, hyE, heq, htop])
        have htb (u : ℕ) {j : ℕ} (hj : j < k) : (u % 2 ^ k).testBit j = u.testBit j := by
          simp [Nat.testBit_mod_two_pow, hj]
        refine ⟨⟨dS.val, Nat.lt_succ_of_lt dS.isLt⟩, by rwa [htb x dS.isLt, htb y dS.isLt] at hneS,
            fun d hd ↦ ?_,
          fun h0 ↦ (fun _ ↦ by rw [htop] at hxE; omega) (h0S ((htb x dS.isLt).trans h0)),
          fun h1 ↦ (fun _ ↦ by rw [htop] at hxE; omega) (h1S ((htb x dS.isLt).trans h1))⟩
        by_cases hdk : d.val < k
        · simpa only [htb x hdk, htb y hdk] using hhiS ⟨d.val, hdk⟩ hd
        · simpa only [Nat.le_antisymm (Nat.le_of_lt_succ d.isLt) (Nat.not_lt.mp hdk)] using htop
      · refine ⟨⟨k, Nat.lt_succ_self k⟩, htop,
          fun d hd ↦ absurd hd (Nat.not_lt_of_ge (Nat.le_of_lt_succ d.isLt)),
          fun h0 ↦ by cases hyb : y.testBit k <;> first | exact absurd (h0.trans hyb.symm) htop |
            (simp only [h0, hyb, Bool.false_eq_true, ↓reduceIte] at hxE hyE; omega),
          fun h1 ↦ by cases hyb : y.testBit k <;> first | exact absurd (h1.trans hyb.symm) htop |
            (simp only [h1, hyb, Bool.false_eq_true, ↓reduceIte] at hxE hyE; omega)⟩
/-! ## Section 4: Closed-Form `ComputeProg.fwdBits` Evaluation of `pPrepMD` Subprograms -/
theorem fwdBits_seq {n : ℕ} (p₁ p₂ : ComputeProg n) (β : BitAssignment n) : (p₁.seq p₂).fwdBits β =
    p₂.fwdBits
    (p₁.fwdBits β) := rfl
theorem idxValPrefix_mono {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) :
    ∀ {k₁ k₂ : ℕ} (hk₁ : k₁ ≤ D) (hk₂ : k₂ ≤ D), k₁ ≤ k₂ →
      idxValPrefix wBit β k₁ hk₁ ≤ idxValPrefix wBit β k₂ hk₂
  | 0, 0, _, _, _ => le_rfl
  | k₁ + 1, 0, _, _, hle => absurd hle (Nat.not_succ_le_zero k₁)
  | k₁, k₂ + 1, hk₁, hk₂, hle => by
      rcases Nat.of_le_succ hle with hlt | rfl
      · exact (idxValPrefix_mono wBit β hk₁ (Nat.le_of_succ_le hk₂) hlt).trans (Nat.le_add_right _
            _)
      · exact le_rfl
/-!
## Section 5: Full `pPrepMD` Control Synthesis Proof (`ValidRouterInput -> ValidPlaneCtrl ∧
ValidPlaneClean`)
-/
/-- Input validity condition on `RouterReg M D n` before `pDualBellRouterMD`. -/
def ValidRouterInput {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) : Prop :=
  (β (rRawHas2 r) = 1 → β (rHas1 r) = 1) ∧
  (β (rHas1 r) = 1 → idxValD (rIdx1 r) β < M) ∧
  (β (rRawHas2 r) = 1 → idxValD (rIdx2 r) β < M) ∧
  (∀ b : Fin 24, β (rBufLo r b) = 0 ∧ β (rBufHi r b) = 0 ∧ β (rHA r b) = 0 ∧ β (rHB r b) = 0) ∧
  (∀ w ∈ sPrivCleanSet r, β w = 0)
/-- Effective strict-2-body flag `1 ↔ rawHas2 = 1 ∧ idx1 ≠ idx2`. -/
def routerHas2Eff {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) : ZMod 2 :=
  if β (rRawHas2 r) = 1 ∧ idxValD (rIdx1 r) β ≠ idxValD (rIdx2 r) β then 1 else 0
/-- Sorted lower index (`min(idx1, idx2)` on strict 2-hit, `idx1` on 1-hit / diagonal). -/
def routerIdxMinVal {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) : ℕ :=
  if routerHas2Eff r β = 1 ∧ idxValD (rIdx2 r) β < idxValD (rIdx1 r) β then
    idxValD (rIdx2 r) β
  else idxValD (rIdx1 r) β
/-- Sorted upper index (`max(idx1, idx2)` on strict 2-hit). -/
def routerIdxMaxVal {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) : ℕ :=
  if routerHas2Eff r β = 1 ∧ idxValD (rIdx2 r) β < idxValD (rIdx1 r) β then
    idxValD (rIdx1 r) β
  else idxValD (rIdx2 r) β
/-- Exact lower one-hot control vector synthesized on `rCtrlLo`. -/
def routerCtrlLo {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) (p : Fin M) : ZMod 2 :=
  if p.val = routerIdxMinVal r β then β (rHas1 r) else 0
/-- Exact upper one-hot control vector synthesized on `rCtrlHi`. -/
def routerCtrlHi {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) (p : Fin M) : ZMod 2 :=
    if p.val = routerIdxMaxVal r β then routerHas2Eff r β else 0
theorem zero_of_valid {M D n : ℕ} {r : RouterReg M D n} {β : BitAssignment n}
    (hβ : ValidRouterInput r β) {i : Fin (routerWidth M D)} (hi : basePub M D ≤ i.val) : β (r i) =
    0 := hβ.2.2.2.2 (r i) ((mem_sPrivCleanSet_iff r i).mpr hi)
/- ## Part A: Single-Buffer Stage-5 Dual-Bell Unload Defs, Counts & Support (`+0 T`) -/
/-! ## Part B: Universal `fwdBits` Disjointness & Cross-Species Overlay Commutation -/
/-- Any wire outside `ProgSupportedIn T p` commutes with `p.fwdBits` under point updates. -/
theorem fwdBits_update_of_not_supp {n : ℕ} {T : Wire n → Prop} :
    ∀ (p : ComputeProg n), ProgSupportedIn T p →
      ∀ {q : Wire n}, ¬ T q → ∀ (β : BitAssignment n) (v : ZMod 2),
      p.fwdBits (Function.update β q v) = Function.update (p.fwdBits β) q v
  | .id, _, _, _, _, _ => rfl
  | .x u, hu, q, hq, _, _ => by
      dsimp only [ComputeProg.fwdBits]; rw [Function.update_of_ne (fun e : u = q ↦ hq (e ▸ hu)),
        Function.update_comm (fun e : u = q ↦ hq (e ▸ hu))]
  | .cnot c t _, ⟨hc, ht⟩, q, hq, _, _ => by
      dsimp only [ComputeProg.fwdBits]
      rw [Function.update_of_ne (fun e : t = q ↦ hq (e ▸ ht)), Function.update_of_ne (fun e : c =
          q ↦ hq (e ▸ hc)),
        Function.update_comm (fun e : t = q ↦ hq (e ▸ ht))]
  | .andGate c₁ c₂ a _ _ _, ⟨hc₁, hc₂, ha⟩, q, hq, _, _ => by
      dsimp only [ComputeProg.fwdBits]
      rw [Function.update_of_ne (fun e : a = q ↦ hq (e ▸ ha)), Function.update_of_ne (fun e : c₁ =
          q ↦ hq (e ▸ hc₁)),
          Function.update_of_ne (fun e : c₂ = q ↦ hq (e ▸ hc₂)), Function.update_comm (fun e : a =
              q ↦ hq (e ▸ ha))]
  | .seq p₁ p₂, ⟨h₁, h₂⟩, _, hq, _, _ => by
      dsimp only [ComputeProg.fwdBits]; rw [fwdBits_update_of_not_supp p₁ h₁ hq,
        fwdBits_update_of_not_supp p₂ h₂ hq]
theorem actsIndepOf_fwdCirc_of_disj {n : ℕ} {S T : Wire n → Prop} (p : ComputeProg n)
    (hp : ProgSupportedIn T p) (hDisj : ∀ q, S q → ¬ T q) : ActsIndepOf S (fwdCirc p).eval :=
    ⟨p.fwdBits, fwdCirc_mulVec_ket p, fun _ hq β v ↦
    fwdBits_update_of_not_supp p hp (hDisj _ hq) β v⟩
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187

namespace QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
open Circuit Qubit PrimitiveGate PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem ite_iff_eq {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) {α : Type}
    (x y : α) : (if P then x else y) = (if Q then x else y) := if_congr h rfl rfl
/--
Strictly sorted, zero-gated router input promise: in addition to `ValidRouterInput r β`,
inactive ports hold zero index bits (`has1 = 0 → idx1 = 0`, `rawHas2 = 0 → idx2 = 0`) and two
active ports satisfy strict ordering `idx1 < idx2` (`rawHas2 = 1 → idx1 < idx2`).
-/
def ValidZeroGatedSortedRouterInput {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) :
    Prop :=
    ValidRouterInput r β ∧ (β (rHas1 r) = 0 → ∀ d : Fin D, β (rIdx1 r d) = 0) ∧ (β (rRawHas2 r) =
    0 → ∀ d : Fin D, β (rIdx2 r d) = 0) ∧ (β (rRawHas2 r) = 1 → idxValD (rIdx1 r) β <
    idxValD (rIdx2 r) β)
theorem routerHas2Eff_of_zeroGatedSorted {M D n : ℕ} {r : RouterReg M D n} {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) : routerHas2Eff r β = β (rRawHas2 r) := by
  rcases zmod2_cases (β (rRawHas2 r)) with hz | ho <;> rw [routerHas2Eff]
  · rw [hz, ite_eq_right (fun h ↦ zero_ne_one h.1)]
  · rw [ho, ite_eq_left ⟨rfl, ne_of_lt (hβ.2.2.2 ho)⟩]
theorem routerIdx2_pos_of_zeroGatedSorted {M D n : ℕ} {r : RouterReg M D n} {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) (h2 : β (rRawHas2 r) = 1) : idxValD (rIdx2 r) β ≠
    0 := by have hlt := hβ.2.2.2 h2; omega
theorem routerCtrlLo_of_zeroGatedSorted {M D n : ℕ} {r : RouterReg M D n} {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) :
    routerCtrlLo r β = fun p : Fin M ↦ if p.val = idxValD (rIdx1 r) β then β (rHas1 r) else 0 := by
  have hMin : routerIdxMinVal r β = idxValD (rIdx1 r) β := by
    rw [routerIdxMinVal, routerHas2Eff_of_zeroGatedSorted hβ,
      ite_eq_right (fun h ↦ Nat.not_lt_of_gt (hβ.2.2.2 h.1) h.2)]
  funext p
  unfold routerCtrlLo
  rw [hMin]
theorem routerCtrlHi_of_zeroGatedSorted {M D n : ℕ} {r : RouterReg M D n} {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) :
    routerCtrlHi r β = fun p : Fin M ↦
        if p.val = idxValD (rIdx2 r) β then β (rRawHas2 r) else 0 := by
  have hMax : routerIdxMaxVal r β = idxValD (rIdx2 r) β := by
    rw [routerIdxMaxVal, routerHas2Eff_of_zeroGatedSorted hβ,
      ite_eq_right (fun h ↦ Nat.not_lt_of_gt (hβ.2.2.2 h.1) h.2)]
  funext p
  unfold routerCtrlHi
  rw [hMax, routerHas2Eff_of_zeroGatedSorted hβ]
theorem idxValPrefix_lt_pow {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) (k : ℕ)
    (hk : k ≤ D) : idxValPrefix wBit β k hk < 2 ^ k := idxValPrefix_lt_two_pow wBit β k hk
theorem fwdBits_id_apply {n : ℕ} (γ : BitAssignment n) (w : Wire n) :
    ComputeProg.id.fwdBits γ w = γ w := rfl
theorem fwdBits_cnot_apply {n : ℕ} (c t : Wire n) (h : c ≠ t) (γ : BitAssignment n) :
    (ComputeProg.cnot c t h).fwdBits γ = Function.update γ t (γ t + γ c) := rfl
theorem fwdBits_and_apply {n : ℕ} (a b t : Wire n) (h1 : a ≠ b) (h2 : a ≠ t) (h3 : b ≠ t)
    (γ : BitAssignment n) :
    (ComputeProg.andGate a b t h1 h2 h3).fwdBits γ = Function.update γ t (γ t + γ a * γ b) := rfl
/-- Zero-`AND` loop XORing `wOut ⟨base + m, _⟩` into `wDst` for all `skip ≤ m < len`. -/
def xorOffsetLoop {M n : ℕ} (wOut : Fin M → Wire n) (base skip : ℕ) (wDst : Wire n) :
    (len : ℕ) → base + len ≤ M →
    (∀ (m : ℕ) (hm : base + m < M), skip ≤ m → m < len → wOut ⟨base + m, hm⟩ ≠ wDst) →
    ComputeProg n
  | 0, _, _ => .id
  | m + 1, hm, hNe =>
      let prev :=
          xorOffsetLoop wOut base skip wDst m (Nat.le_of_succ_le hm)
          (fun j hj hs hlt ↦ hNe j hj hs (Nat.lt_succ_of_lt hlt))
      if hs : skip ≤ m then
        .seq prev (.cnot (wOut ⟨base + m, hm⟩) wDst (hNe m hm hs (Nat.lt_succ_self m)))
      else prev
theorem progSupportedIn_xorOffsetLoop {M n : ℕ} {S : Wire n → Prop} (wOut : Fin M → Wire n)
    (base skip : ℕ)
    (wDst : Wire n)
    (hO : ∀ p,
      S (wOut p)) (hD : S wDst) : ∀ len hlen hNe,
          ProgSupportedIn S (xorOffsetLoop wOut base skip wDst len hlen hNe)
  | 0, _, _ => trivial
  | m + 1, hm, hNe => by
      have ih := progSupportedIn_xorOffsetLoop wOut base skip wDst hO hD m (Nat.le_of_succ_le hm)
          (fun j hj hs hlt ↦ hNe j hj hs (Nat.lt_succ_of_lt hlt))
      dsimp only [xorOffsetLoop]; split_ifs <;> first | exact ⟨ih, hO _, hD⟩ | exact ih
theorem fwdBits_xorOffsetLoop_oneHot {M n : ℕ} (wOut : Fin M → Wire n)
    (base skip lo : ℕ) (v : ZMod 2) (wDst : Wire n)
    (γ : BitAssignment n) :
    ∀ (len : ℕ) (hlen : base + len ≤ M)
      (hNe : ∀ (m : ℕ) (hm : base + m < M), skip ≤ m → m < len → wOut ⟨base + m, hm⟩ ≠ wDst),
      (∀ (m : ℕ) (hm : base + m < M), skip ≤ m → m < len →
        γ (wOut ⟨base + m, hm⟩) = if m = lo then v else 0) →
      let δ := (xorOffsetLoop wOut base skip wDst len hlen hNe).fwdBits γ
      δ wDst = γ wDst + (if skip ≤ lo ∧ lo < len then v else 0) ∧ ∀ w, w ≠ wDst → δ w = γ w
  | 0, _, _, _ =>
        ⟨by rw [xorOffsetLoop, fwdBits_id_apply, ite_eq_right (by omega), add_zero], fun _ _ ↦ rfl⟩
  | m + 1, hm, hNe, hSrc => by
      obtain ⟨ihD, ihO⟩ :=
          fwdBits_xorOffsetLoop_oneHot wOut base skip lo v wDst γ m (Nat.le_of_succ_le hm)
        (fun j hj hs hlt ↦ hNe j hj hs (Nat.lt_succ_of_lt hlt))
            (fun j hj hs hlt ↦ hSrc j hj hs (Nat.lt_succ_of_lt hlt))
      dsimp only [xorOffsetLoop]
      by_cases hs : skip ≤ m
      · rw [dite_eq_left hs]
        refine ⟨?_, fun w hw ↦
            by rw [fwdBits_seq, fwdBits_cnot_apply, Function.update_of_ne hw, ihO w hw]⟩
        rw [fwdBits_seq, fwdBits_cnot_apply, Function.update_self, ihD,
            ihO _ (hNe m hm hs (Nat.lt_succ_self m)),
          hSrc m hm hs (Nat.lt_succ_self m)]
        by_cases hmlo : m = lo
        · subst hmlo; rw [ite_eq_right (fun h ↦ Nat.lt_irrefl _ h.2), ite_eq_left rfl,
              ite_eq_left ⟨hs,
          Nat.lt_succ_self _⟩, add_zero]
        · rw [ite_eq_right hmlo, add_zero, add_right_inj]; exact ite_iff_eq ⟨fun ⟨h1, h2⟩ ↦ ⟨h1,
          Nat.lt_succ_of_lt h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, by omega⟩⟩ v 0
      · rw [dite_eq_right hs]
        exact ⟨ihD.trans (congrArg (γ wDst + ·)
            (ite_iff_eq ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, Nat.lt_succ_of_lt h2⟩, fun ⟨h1,
          h2⟩ ↦ ⟨h1, by omega⟩⟩ v 0)), ihO⟩
theorem splitSkip_lt_lo {M d m : ℕ} (hmM : 2 ^ d + (m + 1) ≤ M) : m < M := by
  have hp : 1 ≤ 2 ^ d := Nat.one_le_two_pow; omega
theorem splitSkip_ne_lh {M d m : ℕ} {n : ℕ} {wOut : Fin M → Wire n}
    (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) (hmM : 2 ^ d + (m + 1) ≤ M) :
    wOut ⟨m, splitSkip_lt_lo hmM⟩ ≠ wOut ⟨2 ^ d + m, hmM⟩ :=
  hInj _ _ fun e ↦ by
    have hp : 1 ≤ 2 ^ d := Nat.one_le_two_pow; have hv := congrArg Fin.val e
    dsimp at hv; omega
/-- Inner `AND`-split loop for `skip ≤ m < len`, saving `skip` `TempAND`s at `0 .. skip - 1`. -/
def oneHotSplitSkip {M D n : ℕ} (wBit : Fin D → Wire n) (wOut : Fin M → Wire n)
    (hBO : ∀ d p, wBit d ≠ wOut p) (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q)
    (d : Fin D) (skip : ℕ) :
    (len : ℕ) → 2 ^ d.val + len ≤ M → len ≤ 2 ^ d.val → ComputeProg n
  | 0, _, _ => .id
  | m + 1, hmM, hm2 =>
      let prev :=
          oneHotSplitSkip wBit wOut hBO hInj d skip m (Nat.le_of_succ_le hmM)
          (Nat.le_of_succ_le hm2)
      if _ : skip ≤ m then
        let pLo : Fin M := ⟨m, splitSkip_lt_lo hmM⟩; let pHi : Fin M := ⟨2 ^ d.val + m, hmM⟩;
        let hNeLH := splitSkip_ne_lh hInj hmM
        .seq prev
          (.seq (.andGate (wOut pLo) (wBit d) (wOut pHi)
                  (hBO d pLo).symm hNeLH (hBO d pHi))
                (.cnot (wOut pHi) (wOut pLo) hNeLH.symm))
      else prev
theorem progSupportedIn_oneHotSplitSkip {M D n : ℕ} {S : Wire n → Prop} (wBit : Fin D → Wire n)
    (wOut : Fin M
  → Wire n)
    (hBO : ∀ d p, wBit d ≠ wOut p) (hInj : ∀ p q, p ≠ q
      → wOut p ≠ wOut q) (d : Fin D) (skip : ℕ) (hB : S (wBit d)) (hO : ∀ p, S (wOut p)) :
    ∀ len hmM hm2, ProgSupportedIn S (oneHotSplitSkip wBit wOut hBO hInj d skip len hmM hm2)
  | 0, _, _ => trivial
  | m + 1, hmM, hm2 => by
      have ih :=
          progSupportedIn_oneHotSplitSkip wBit wOut hBO hInj d skip hB hO m (Nat.le_of_succ_le hmM)
          (Nat.le_of_succ_le hm2)
      dsimp only [oneHotSplitSkip]; split_ifs <;> first
        | exact ⟨ih, ⟨hO _, hB, hO _⟩, hO _, hO _⟩
        | exact ih
theorem fwdBits_oneHotSplitSkip {M D n : ℕ} (wBit : Fin D → Wire n) (wOut : Fin M → Wire n)
    (hBO : ∀ d p, wBit d ≠ wOut p) (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q)
    (d : Fin D) (skip : ℕ) (γ : BitAssignment n)
    (hCleanHi : ∀ p : Fin M, 2 ^ d.val ≤ p.val → γ (wOut p) = 0) :
    ∀ (len : ℕ) (hmM : 2 ^ d.val + len ≤ M) (hm2 : len ≤ 2 ^ d.val),
      let δ := (oneHotSplitSkip wBit wOut hBO hInj d skip len hmM hm2).fwdBits γ
      (∀ p : Fin M, p.val < 2 ^ d.val → δ (wOut p) = if skip ≤ p.val
        ∧ p.val < len then γ (wOut p) + γ (wOut p) * γ (wBit d) else γ (wOut p)) ∧
      (∀ p : Fin M, 2 ^ d.val ≤ p.val → δ (wOut p) = if h : 2 ^ d.val + skip ≤ p.val
        ∧ p.val < 2 ^ d.val + len then γ (wOut ⟨p.val - 2 ^ d.val, by omega⟩) * γ (wBit d) else 0) ∧
      (∀ w, (∀ p : Fin M, w ≠ wOut p) → δ w = γ w)
  | 0, _, _ => ⟨fun p _ ↦ by rw [oneHotSplitSkip, fwdBits_id_apply, ite_eq_right (by omega)],
      fun p hp ↦
          by rw [oneHotSplitSkip, fwdBits_id_apply, hCleanHi p hp, dite_eq_right (by omega)],
          fun _ _ ↦ rfl⟩
  | m + 1, hmM, hm2 => by
      obtain ⟨ihLo, ihHi, ihOth⟩ := fwdBits_oneHotSplitSkip wBit wOut hBO hInj d skip γ hCleanHi
        m (Nat.le_of_succ_le hmM) (Nat.le_of_succ_le hm2)
      have loStep (p : Fin M) (hp : p.val < 2 ^ d.val) (hNe : skip ≤ p.val → p.val ≠ m) :=
        (ihLo p hp).trans (ite_iff_eq (P := skip ≤ p.val ∧ p.val < m)
            (Q := skip ≤ p.val ∧ p.val < m + 1)
          ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, Nat.lt_succ_of_lt h2⟩,
          fun ⟨h1, h2⟩ ↦ ⟨h1, (fun _ ↦ by omega) (hNe h1)⟩⟩ _ _)
      have hiStep (p : Fin M) (hp : 2 ^ d.val ≤ p.val)
          (hNe : 2 ^ d.val + skip ≤ p.val → p.val ≠ 2 ^ d.val + m) :
          (oneHotSplitSkip wBit wOut hBO hInj d skip m (Nat.le_of_succ_le hmM)
              (Nat.le_of_succ_le hm2)).fwdBits γ (wOut p) =
            if h : 2 ^ d.val + skip ≤ p.val ∧ p.val < 2 ^ d.val + (m + 1) then
              γ (wOut ⟨p.val - 2 ^ d.val, by omega⟩) * γ (wBit d) else 0 := by
        rw [ihHi p hp]
        by_cases hc : 2 ^ d.val + skip ≤ p.val ∧ p.val < 2 ^ d.val + m
        · rw [dite_eq_left hc, dite_eq_left ⟨hc.1, by omega⟩]
        · rw [dite_eq_right hc, dite_eq_right fun ⟨h1, h2⟩ ↦ hc ⟨h1, (fun _ ↦ by omega) (hNe h1)⟩]
      dsimp only [oneHotSplitSkip]
      by_cases hs : skip ≤ m
      · rw [dite_eq_left hs]
        let pLo : Fin M := ⟨m, splitSkip_lt_lo hmM⟩
        let pHi : Fin M := ⟨2 ^ d.val + m, hmM⟩
        have ηLo := (ihLo pLo hm2).trans (ite_eq_right fun h ↦ Nat.lt_irrefl m h.2)
        have ηHi :=
            (ihHi pHi (Nat.le_add_right _ _)).trans (dite_eq_right fun h ↦ Nat.lt_irrefl _ h.2)
        refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_, fun w hw ↦ by
          rw [fwdBits_seq, fwdBits_seq, fwdBits_and_apply, fwdBits_cnot_apply,
            Function.update_of_ne (hw pLo), Function.update_of_ne (hw pHi), ihOth w hw]⟩
        · rw [fwdBits_seq, fwdBits_seq, fwdBits_and_apply, fwdBits_cnot_apply]
          by_cases hpm : p = pLo
          · subst hpm; rw [Function.update_self,
                Function.update_of_ne (splitSkip_ne_lh hInj hmM), Function.update_self,
              ηHi, zero_add, ηLo, ihOth (wBit d) (hBO d), ite_eq_left ⟨hs, Nat.lt_succ_self m⟩]
          · rw [Function.update_of_ne (hInj p pLo hpm), Function.update_of_ne (hInj p pHi fun e ↦
              Nat.lt_irrefl _ (hp.trans_le (congrArg Fin.val e ▸ Nat.le_add_right _ _)))]
            exact loStep p hp fun _ e ↦ hpm (Fin.ext e)
        · rw [fwdBits_seq, fwdBits_seq, fwdBits_and_apply, fwdBits_cnot_apply]
          by_cases hpm : p = pHi
          · subst hpm; rw [Function.update_of_ne (splitSkip_ne_lh hInj hmM).symm,
              Function.update_self, ηHi, zero_add, ηLo, ihOth (wBit d) (hBO d),
              dite_eq_left ⟨Nat.add_le_add_left hs _, Nat.add_lt_add_left (Nat.lt_succ_self m) _⟩]
            exact congrArg (fun x : Fin M ↦ γ (wOut x) * γ (wBit d))
                (Fin.ext (Nat.add_sub_cancel_left (2 ^ d.val) m)).symm
          · rw [Function.update_of_ne (hInj p pLo fun e ↦ Nat.not_lt_of_ge hp
              (congrArg Fin.val e ▸ hm2)), Function.update_of_ne (hInj p pHi hpm)]
            exact hiStep p hp fun _ e ↦ hpm (Fin.ext e)
      · rw [dite_eq_right hs]
        exact ⟨fun p hp ↦ loStep p hp (by omega), fun p hp ↦ hiStep p hp (by omega), ihOth⟩
theorem zg_len_hmM {M d : ℕ} (hpow : 2 ^ d < M) :
    2 ^ d + min (M - 2 ^ d) (2 ^ d) ≤ M := by omega
theorem zg_len_hm2 {M d : ℕ} : min (M - 2 ^ d) (2 ^ d) ≤ 2 ^ d := Nat.min_le_right _ _
theorem zg_ne_pow_hi {M d len : ℕ} {n : ℕ} {wOut : Fin M → Wire n}
    (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) (hpow : 2 ^ d < M) : ∀ (m : ℕ) (hm : 2 ^ d + m < M), 1 ≤
    m → m < len → wOut ⟨2 ^ d + m, hm⟩ ≠ wOut ⟨2 ^ d, hpow⟩ :=
  fun _ _ hm1 _ ↦ hInj _ _ fun e ↦ by
    have hv := congrArg Fin.val e; dsimp at hv; omega
theorem zg_ne_nz_zero {M len : ℕ} {n : ℕ} {wOut : Fin M → Wire n}
    (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) (h0 : 0 < M) : ∀ (m : ℕ) (hm : 0 + m < M), 1 ≤ m → m <
    len → wOut ⟨0 + m, hm⟩ ≠ wOut ⟨0, h0⟩ :=
  fun _ _ hm1 _ ↦ hInj _ _ fun e ↦ by
    have hv := congrArg Fin.val e; dsimp at hv; omega
def oneHotZeroOuter {M D n : ℕ} (wBit : Fin D → Wire n) (wOut : Fin M → Wire n)
    (hBO : ∀ d p, wBit d ≠ wOut p) (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) :
    (k : ℕ) → k ≤ D → (∀ d < k, 2 ^ d < M) → ComputeProg n
  | 0, _, _ => .id
  | d + 1, hdD, hPowLt =>
      let prev :=
          oneHotZeroOuter wBit wOut hBO hInj d (Nat.le_of_succ_le hdD)
          (fun j hj ↦ hPowLt j (Nat.lt_succ_of_lt hj))
      let hpow : 2 ^ d < M := hPowLt d (Nat.lt_succ_self d); let len := min (M - 2 ^ d) (2 ^ d);
      let p2d : Fin M := ⟨2 ^ d, hpow⟩
      .seq prev
        (.seq (oneHotSplitSkip wBit wOut hBO hInj ⟨d, hdD⟩ 1 len (zg_len_hmM hpow) zg_len_hm2)
          (.seq (.cnot (wBit ⟨d, hdD⟩) (wOut p2d) (hBO ⟨d, hdD⟩ p2d))
            (xorOffsetLoop wOut (2 ^ d) 1 (wOut p2d) len (zg_len_hmM hpow)
              (zg_ne_pow_hi hInj hpow))))
/--
Complete zero-gated unary decoder `oneHotZeroGated`: writes `[p = idxValD wBit β] * β qAct`
to all `p : Fin M` using `M - 1 - D` `TempAND`s whenever `2 ^ (D - 1) < M ≤ 2 ^ D`.
-/
def oneHotZeroGated {M D n : ℕ} (hM0 : 0 < M) (hPowAll : ∀ d < D, 2 ^ d < M) (qAct : Wire n)
    (wBit : Fin D → Wire n) (wOut : Fin M → Wire n) (hAO : ∀ p, qAct ≠ wOut p)
    (hBO : ∀ d p, wBit d ≠ wOut p) (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) : ComputeProg n :=
  let p0 : Fin M := ⟨0, hM0⟩
  .seq (oneHotZeroOuter wBit wOut hBO hInj D le_rfl hPowAll)
    (.seq (.cnot qAct (wOut p0) (hAO p0))
      (xorOffsetLoop wOut 0 1 (wOut p0) M (Nat.zero_add M).le (zg_ne_nz_zero hInj hM0)))
/--
Positive-index zero-gated unary decoder `oneHotPosZeroGated`: writes
`[p = idxValD wBit β] * β qAct` to all `p : Fin M` using `M - 2 - D` `TempAND`s whenever
`1 ≤ D`, `2 ^ (D - 1) + 2 ≤ M ≤ 2 ^ D`, and `β qAct = 1 → idxValD wBit β ≠ 0`.
-/
theorem zg_zero_add_pow {M D : ℕ} (hMhi : 2 ^ (D - 1) + 2 ≤ M) :
    0 + 2 ^ (D - 1) ≤ M := by omega
def oneHotPosZeroGated {M D n : ℕ} (hD1 : 1 ≤ D) (hMhi : 2 ^ (D - 1) + 2 ≤ M)
    (hPowSub : ∀ d < D - 1, 2 ^ d < M) (qAct : Wire n) (wBit : Fin D → Wire n)
    (wOut : Fin M → Wire n) (hAO : ∀ p, qAct ≠ wOut p) (hBO : ∀ d p, wBit d ≠ wOut p)
    (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) : ComputeProg n :=
  let dLast : Fin D := ⟨D - 1, Nat.sub_lt hD1 Nat.zero_lt_one⟩
  let hpow : 2 ^ (D - 1) < M := by omega
  let hpow1 : 2 ^ (D - 1) + 1 < M := hMhi; let len := min (M - 2 ^ (D - 1)) (2 ^ (D - 1));
  let p2d : Fin M := ⟨2 ^ (D - 1), hpow⟩; let p2d1 : Fin M := ⟨2 ^ (D - 1) + 1, hpow1⟩
  let p1 : Fin M := ⟨1, by have hp : 1 ≤ 2 ^ (D - 1) := Nat.one_le_two_pow; omega⟩
  let hNeHi2 : ∀ (m : ℕ) (hm : 2 ^ (D - 1) + m < M), 2 ≤ m → m < len →
      wOut ⟨2 ^ (D - 1) + m, hm⟩ ≠ wOut p2d1 :=
    fun _ _ hm2 _ ↦ hInj _ _ fun e ↦ by have hv := congrArg Fin.val e; dsimp [p2d1] at hv; omega
  .seq (oneHotZeroOuter wBit wOut hBO hInj (D - 1) (Nat.sub_le D 1) hPowSub)
    (.seq (.cnot qAct (wOut p2d) (hAO p2d))
      (.seq (xorOffsetLoop wOut 0 1 (wOut p2d) (2 ^ (D - 1)) (zg_zero_add_pow hMhi)
          (fun _ hm _ hlt ↦ hInj _ p2d fun e ↦ by
            have hv := congrArg Fin.val e; dsimp [p2d] at hv; omega))
        (.seq (oneHotSplitSkip wBit wOut hBO hInj dLast 2 len (zg_len_hmM hpow) zg_len_hm2)
          (.seq (.cnot (wBit dLast) (wOut p2d1) (hBO dLast p2d1))
            (.seq (.cnot (wOut p2d) (wOut p2d1)
                (hInj p2d p2d1 fun e ↦ by
                  have hv := congrArg Fin.val e; dsimp [p2d, p2d1] at hv; omega))
              (.seq (xorOffsetLoop wOut (2 ^ (D - 1)) 2 (wOut p2d1) len (zg_len_hmM hpow) hNeHi2)
                (.cnot (wOut p2d1) (wOut p1)
                  (hInj p2d1 p1 fun e ↦ by
                    have hp : 1 ≤ 2 ^ (D - 1) := Nat.one_le_two_pow
                    have hv := congrArg Fin.val e; dsimp [p2d1, p1] at hv; omega))))))))
theorem progSupportedIn_oneHotZeroOuter {M D n : ℕ} {S : Wire n → Prop} (wBit : Fin D → Wire n)
    (wOut : Fin M
  → Wire n)
    (hBO : ∀ d p, wBit d ≠ wOut p) (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) (hB : ∀ d, S (wBit d))
        (hO : ∀ p,
      S (wOut p)) :
    ∀ k hk _hPow, ProgSupportedIn S (oneHotZeroOuter wBit wOut hBO hInj k hk _hPow)
  | 0, _, _ => trivial
  | d + 1, hdD, _ =>
      ⟨progSupportedIn_oneHotZeroOuter wBit wOut hBO hInj hB hO d _ _,
        progSupportedIn_oneHotSplitSkip wBit wOut hBO hInj ⟨d, hdD⟩ 1 (hB _) hO _ _ _, ⟨hB _, hO _⟩,
        progSupportedIn_xorOffsetLoop wOut (2 ^ d) 1 _ hO (hO _) _ _ _⟩
theorem progSupportedIn_oneHotZeroGated {M D n : ℕ} {S : Wire n → Prop} (hM0 : 0 < M)
    (hPowAll : ∀ d < D, 2 ^ d < M) (qAct : Wire n) (wBit : Fin D → Wire n) (wOut : Fin M → Wire n)
    (hAO : ∀ p, qAct ≠ wOut p) (hBO : ∀ d p, wBit d ≠ wOut p)
    (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) (hA : S qAct) (hB : ∀ d, S (wBit d))
    (hO : ∀ p, S (wOut p)) :
    ProgSupportedIn S (oneHotZeroGated hM0 hPowAll qAct wBit wOut hAO hBO hInj) :=
    ⟨progSupportedIn_oneHotZeroOuter wBit wOut hBO hInj hB hO D le_rfl hPowAll, ⟨hA, hO _⟩,
    progSupportedIn_xorOffsetLoop wOut 0 1 _ hO (hO _) _ _ _⟩
theorem progSupportedIn_oneHotPosZeroGated {M D n : ℕ} {S : Wire n → Prop} (hD1 : 1 ≤ D)
    (hMlo : 2 ^ (D - 1) + 2 ≤ M) (hPowSub : ∀ d < D - 1, 2 ^ d < M) (qAct : Wire n)
    (wBit : Fin D → Wire n) (wOut : Fin M → Wire n) (hAO : ∀ p, qAct ≠ wOut p)
    (hBO : ∀ d p, wBit d ≠ wOut p) (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) (hA : S qAct)
    (hB : ∀ d, S (wBit d)) (hO : ∀ p, S (wOut p)) :
    ProgSupportedIn S (oneHotPosZeroGated hD1 hMlo hPowSub qAct wBit wOut hAO hBO hInj) :=
    ⟨progSupportedIn_oneHotZeroOuter wBit wOut hBO hInj hB hO _ _ hPowSub, ⟨hA, hO _⟩,
    progSupportedIn_xorOffsetLoop wOut 0 1 _ hO (hO _) _ _ _,
    progSupportedIn_oneHotSplitSkip wBit wOut hBO hInj _ 2 (hB _) hO _ _ _, ⟨hB _, hO _⟩,
    ⟨hO _, hO _⟩, progSupportedIn_xorOffsetLoop wOut (2 ^ (D - 1)) 2 _ hO (hO _) _ _ _,
    ⟨hO _, hO _⟩⟩
theorem fwdBits_oneHotZeroOuter {M D n : ℕ} (wBit : Fin D → Wire n) (wOut : Fin M → Wire n)
    (hBO : ∀ d p,
  wBit d ≠ wOut p) (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q)
    (γ : BitAssignment n) (hIdxLt : idxValD wBit γ < M) (hOut0 : ∀ p : Fin M, γ (wOut p) = 0) :
    ∀ (k : ℕ) (hk : k ≤ D) (hPow : ∀ d < k,
      2 ^ d < M), let δ := (oneHotZeroOuter wBit wOut hBO hInj k hk hPow).fwdBits γ
      (∀ p : Fin M, p.val < 2 ^ k
        → δ (wOut p) = if p.val = 0 then 0 else if idxValPrefix wBit γ k hk = p.val then 1 else 0) ∧
      (∀ p : Fin M, 2 ^ k ≤ p.val → δ (wOut p) = 0) ∧ (∀ w : Wire n, (∀ p : Fin M, w ≠ wOut p) →
          δ w = γ w)
  | 0, _, _ =>
        ⟨fun p hp ↦
        by rw [oneHotZeroOuter, fwdBits_id_apply, hOut0 p, ite_eq_left (Nat.lt_one_iff.mp hp)],
    fun p _ ↦ hOut0 p, fun _ _ ↦ rfl⟩
  | d + 1, hdD, hPow => by
      let hpow : 2 ^ d < M := hPow d (Nat.lt_succ_self d); let len := min (M - 2 ^ d) (2 ^ d);
      let p2d : Fin M := ⟨2 ^ d, hpow⟩; let lo := idxValPrefix wBit γ d (Nat.le_of_succ_le hdD);
      let b := γ (wBit ⟨d, hdD⟩);
      have hloLt : lo < 2 ^ d := idxValPrefix_lt_pow wBit γ d (Nat.le_of_succ_le hdD);
      have hp1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have hp2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      have hModSucc : idxValPrefix wBit γ (d + 1) hdD = lo + (if b = 1 then 2 ^ d else 0) := rfl
      have hb1Len : b = 1 → lo < len := fun hb1 ↦ by
        have hleD : idxValPrefix wBit γ
            (d + 1) hdD ≤ idxValD wBit γ :=
                SplitRouter47_187.idxValPrefix_mono wBit γ hdD le_rfl hdD
        rw [hModSucc, ite_eq_left hb1] at hleD; exact lt_min (by omega) hloLt
      let prev :=
          oneHotZeroOuter wBit wOut hBO hInj d (Nat.le_of_succ_le hdD)
          (fun j hj ↦ hPow j (Nat.lt_succ_of_lt hj))
      let δ0 := prev.fwdBits γ
      have hIH :=
          fwdBits_oneHotZeroOuter wBit wOut hBO hInj γ hIdxLt hOut0 d (Nat.le_of_succ_le hdD)
          (fun j hj ↦ hPow j (Nat.lt_succ_of_lt hj))
      have ihLo : ∀ p : Fin M, p.val < 2 ^ d → δ0 (wOut p) = if p.val = 0 then 0 else if lo =
          p.val then 1 else 0 := hIH.1
      have ihHi : ∀ p : Fin M, 2 ^ d ≤ p.val → δ0 (wOut p) = 0 :=
          hIH.2.1; have ihOth : ∀ w : Wire n, (∀ p : Fin M, w ≠ wOut p) → δ0 w = γ w :=
                     hIH.2.2; have hb0 : δ0 (wBit ⟨d, hdD⟩) = b :=
                                ihOth _ (hBO ⟨d,
                                hdD⟩); let sp :=
                                         oneHotSplitSkip wBit wOut hBO hInj ⟨d,
                                         hdD⟩ 1 len (zg_len_hmM hpow) zg_len_hm2;
                                         let δ1 :=
                                         sp.fwdBits δ0; have hSP :=
                                                          fwdBits_oneHotSplitSkip wBit wOut hBO hInj
                                                          ⟨d,
                                                          hdD⟩ 1 δ0 ihHi len (zg_len_hmM hpow)
                                                          zg_len_hm2
      obtain ⟨sLo, sHi, sOth⟩ := hSP
      change ∀ p : Fin M, p.val < 2 ^ d → δ1 (wOut p) = _ at sLo
      change ∀ p : Fin M, 2 ^ d ≤ p.val → δ1 (wOut p) = _ at sHi
      change ∀ w : Wire n, (∀ p : Fin M, w ≠ wOut p) → δ1 w = δ0 w at sOth
      let δ2 := (ComputeProg.cnot (wBit ⟨d, hdD⟩) (wOut p2d) (hBO ⟨d, hdD⟩ p2d)).fwdBits δ1
      have hSrc2 : ∀ (m : ℕ) (hm : 2 ^ d + m < M), 1 ≤ m → m < len → δ2 (wOut ⟨2 ^ d + m, hm⟩) =
          if m = lo then b else 0 := by
        intro m hm hm1 hmLt; let pm : Fin M := ⟨2 ^ d + m, hm⟩;
        have hne : wOut pm ≠ wOut p2d :=
            zg_ne_pow_hi hInj hpow m hm hm1 hmLt; change (ComputeProg.cnot (wBit ⟨d, hdD⟩)
            (wOut p2d) (hBO ⟨d, hdD⟩ p2d)).fwdBits δ1 (wOut pm) = _
        rw [fwdBits_cnot_apply, Function.update_of_ne hne, sHi pm (Nat.le_add_right _ _),
          dite_eq_left ⟨Nat.add_le_add_left hm1 _, Nat.add_lt_add_left hmLt _⟩,
            (Fin.ext (by dsimp [pm]; omega) : (⟨pm.val - 2 ^ (⟨d, hdD⟩ : Fin D).val,
            by dsimp [pm]; omega⟩ : Fin M) = ⟨m, by omega⟩),
            ihLo ⟨m, by omega⟩ (by dsimp; omega), hb0, ite_eq_right (by dsimp; omega)]
        by_cases hml : m = lo
        · subst hml; rw [ite_eq_left rfl, ite_eq_left rfl]; simp
        · rw [ite_eq_right (Ne.symm hml), ite_eq_right hml, zero_mul]
      obtain ⟨xDst, xOth⟩ :=
          fwdBits_xorOffsetLoop_oneHot wOut (2 ^ d) 1 lo b (wOut p2d) δ2 len (zg_len_hmM hpow)
          (zg_ne_pow_hi hInj hpow) hSrc2; dsimp only [oneHotZeroOuter]; rw [fwdBits_seq,
          fwdBits_seq, fwdBits_seq]
      refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_, fun w hw ↦ ?_⟩
      · by_cases hlt : p.val < 2 ^ d
        · have hne : wOut p ≠ wOut p2d := hInj p p2d fun e ↦ Nat.ne_of_lt hlt (congrArg Fin.val e)
          rw [xOth _ hne]; change (ComputeProg.cnot _ _ _).fwdBits δ1 (wOut p) = _;
          rw [fwdBits_cnot_apply, Function.update_of_ne hne, sLo p hlt, ihLo p hlt, hb0, hModSucc]
          by_cases hp0 : p.val = 0
          · rw [ite_eq_left hp0, zero_mul, add_zero, ite_self, ite_eq_left hp0]
          · rw [ite_eq_right hp0, ite_eq_right hp0]
            rcases zmod2_cases b with hbZ | hbZ <;> rw [hbZ]
            · rw [ite_eq_right zero_ne_one, Nat.add_zero, mul_zero, add_zero, ite_self]
            · rw [ite_eq_left rfl]
              by_cases hpl : lo = p.val
              · rw [ite_eq_left hpl, mul_one, ite_eq_right (by omega : ¬lo + 2 ^ d = p.val),
                    ite_eq_left ⟨by omega, hpl ▸ hb1Len hbZ⟩]; decide
              · rw [ite_eq_right hpl, zero_mul, add_zero, ite_self, ite_eq_right (by omega)]
        · by_cases heq : p = p2d
          · subst heq
            rw [xDst, show δ2 (wOut p2d) = (ComputeProg.cnot _ _ _).fwdBits _ (wOut p2d) from rfl,
                fwdBits_cnot_apply, Function.update_self, sHi p2d le_rfl,
              dite_eq_right (fun h ↦ Nat.not_succ_le_self (2 ^ d) h.1), sOth _ (hBO ⟨d, hdD⟩), hb0,
              show p2d.val = 2 ^ d from rfl, ite_eq_right (by omega : (2 ^ d : ℕ) ≠ 0), hModSucc]
            rcases zmod2_cases b with hbZ | hbZ <;> rw [hbZ]
            · rw [ite_eq_right zero_ne_one, Nat.add_zero, ite_self, add_zero,
                  ite_eq_right (by omega)]; decide
            · rw [ite_eq_left rfl]
              by_cases hlo0 : lo = 0
              · rw [hlo0, ite_eq_right (by omega), zero_add, Nat.zero_add, ite_eq_left rfl];
                    decide
              · rw [ite_eq_left ⟨by omega, hb1Len hbZ⟩,
                    ite_eq_right (by omega : ¬lo + 2 ^ d = 2 ^ d)]; decide
          · have hgt : 2 ^ d + 1 ≤ p.val := (fun _ ↦ by dsimp [p2d] at *; omega) (mt Fin.ext heq)
            rw [xOth _ (hInj p p2d heq), show δ2 (wOut p) =
                (ComputeProg.cnot _ _ _).fwdBits _ (wOut p) from rfl, fwdBits_cnot_apply,
              Function.update_of_ne (hInj p p2d heq), sHi p (by omega),
              dite_eq_left ⟨hgt, (fun _ ↦ by dsimp [len]; omega) p.isLt⟩, ihLo ⟨p.val - 2 ^ d,
                  by omega⟩ (by dsimp; omega), hb0,
              ite_eq_right (Nat.sub_ne_zero_of_lt hgt : (⟨p.val - 2 ^ d, _⟩ : Fin M).val ≠ 0),
              ite_eq_right (by omega : p.val ≠ 0), hModSucc]
            change (if lo = p.val - 2 ^ d then (1 : ZMod 2) else 0) * b = _
            rcases zmod2_cases b with hbZ | hbZ <;> rw [hbZ]
            · simp only [zero_ne_one, ↓reduceIte, add_zero, mul_zero];
                  exact (ite_eq_right (by omega)).symm
            · rw [ite_eq_left rfl, mul_one]; exact ite_iff_eq ⟨fun _ ↦ by omega, fun _ ↦
                  by omega⟩ 1 0
      · have hne : wOut p ≠ wOut p2d := hInj p p2d fun e ↦ by
          have hv := congrArg Fin.val e; dsimp [p2d] at hv; omega
        have hgeLen : ¬ (2 ^ (⟨d, hdD⟩ : Fin D).val + 1 ≤ p.val ∧ p.val <
            2 ^ (⟨d, hdD⟩ : Fin D).val + len)
            := by have : len ≤ 2 ^ d := min_le_right _ _; dsimp; omega
        rw [xOth _ hne]; change (ComputeProg.cnot _ _ _).fwdBits δ1 (wOut p) = 0
        rw [fwdBits_cnot_apply, Function.update_of_ne hne, sHi p (by omega), dite_eq_right hgeLen]
      · rw [xOth w (hw p2d)]; change (ComputeProg.cnot _ _ _).fwdBits δ1 w = γ w;
        rw [fwdBits_cnot_apply, Function.update_of_ne (hw p2d), sOth w hw, ihOth w hw]
theorem fwdBits_oneHotZeroGated {M D n : ℕ} (hM0 : 0 < M) (hMhi : M ≤ 2 ^ D)
    (hPowAll : ∀ d < D, 2 ^ d < M)
    (qAct : Wire n) (wBit : Fin D → Wire n) (wOut : Fin M → Wire n)
    (hAO : ∀ p, qAct ≠ wOut p) (hBO : ∀ d p, wBit d ≠ wOut p)
    (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q)
    (γ : BitAssignment n) (hIdxLt : idxValD wBit γ < M)
    (hZeroGated : γ qAct = 0 → idxValD wBit γ = 0)
    (hOut0 : ∀ p : Fin M, γ (wOut p) = 0) :
    let δ := (oneHotZeroGated hM0 hPowAll qAct wBit wOut hAO hBO hInj).fwdBits γ
    (∀ p : Fin M, δ (wOut p) = if idxValD wBit γ = p.val then γ qAct else 0) ∧
        (∀ w : Wire n, (∀ p : Fin M,
      w ≠ wOut p) → δ w = γ w) := by
  let p0 : Fin M := ⟨0, hM0⟩
  obtain ⟨oLo, _, oOth⟩ :=
      fwdBits_oneHotZeroOuter wBit wOut hBO hInj γ hIdxLt hOut0 D le_rfl hPowAll
  let δ1 :=
      (ComputeProg.cnot qAct (wOut p0)
      (hAO p0)).fwdBits ((oneHotZeroOuter wBit wOut hBO hInj D le_rfl hPowAll).fwdBits γ)
  obtain ⟨xDst, xOth⟩ := fwdBits_xorOffsetLoop_oneHot wOut 0 1 (idxValD wBit γ) 1 (wOut p0) δ1 M
    (Nat.zero_add M).le (zg_ne_nz_zero hInj hM0) fun m hm hm1 hmM ↦ by
      dsimp only [δ1, fwdBits_cnot_apply]
      rw [Function.update_of_ne (zg_ne_nz_zero hInj hM0 m hm hm1 hmM),
        oLo ⟨0 + m, hm⟩ (Nat.lt_of_lt_of_le hm hMhi), ite_eq_right (by dsimp; omega)]
      exact ite_iff_eq ⟨fun _ ↦ by dsimp [idxValD] at *; omega, fun _ ↦
          by dsimp [idxValD] at *; omega⟩ 1 0
  dsimp only [oneHotZeroGated]
  rw [fwdBits_seq, fwdBits_seq]
  refine ⟨fun p ↦ ?_, fun w hw ↦ (xOth w (hw p0)).trans ?_⟩
  · by_cases hp : p = p0
    · subst hp
      rw [xDst, show δ1 (wOut p0) = (ComputeProg.cnot _ _ _).fwdBits _ (wOut p0) from rfl,
          fwdBits_cnot_apply, Function.update_self,
        oLo p0 (Nat.lt_of_lt_of_le hM0 hMhi), ite_eq_left rfl, oOth qAct hAO, zero_add]
      rcases zmod2_cases (γ qAct) with hq | hq
      · simp [p0, hq, hZeroGated hq]
      · rcases eq_or_ne (idxValD wBit γ) 0 with hi0 | hi0 <;>
          simp [p0, hq, hi0, hIdxLt, Nat.one_le_iff_ne_zero, show (1 : ZMod 2) + 1 = 0 from rfl]
    · have hpNe : p.val ≠ 0 := fun e ↦ hp (Fin.ext e)
      rw [xOth _ (hInj p p0 hp), show δ1 (wOut p) =
          (ComputeProg.cnot _ _ _).fwdBits _ (wOut p) from rfl, fwdBits_cnot_apply,
          Function.update_of_ne (hInj p p0 hp),
        oLo p (Nat.lt_of_lt_of_le p.isLt hMhi), ite_eq_right hpNe]
      change (if idxValD wBit γ = p.val then (1 : ZMod 2) else 0) = _
      rcases zmod2_cases (γ qAct) with hq | hq <;> simp [hq, hZeroGated, hpNe.symm]
  · dsimp only [δ1, fwdBits_cnot_apply]
    rw [Function.update_of_ne (hw p0), oOth w hw]
theorem fwdBits_oneHotSplitSkip_ignore_p2d {M D n : ℕ}
    (wBit : Fin D → Wire n) (wOut : Fin M → Wire n)
    (hBO : ∀ d p, wBit d ≠ wOut p) (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q)
    (dLast : Fin D) (p2d : Fin M) (hp2dEq : p2d.val = 2 ^ dLast.val)
    (δ2 : BitAssignment n) :
    let δ2z : BitAssignment n := Function.update δ2 (wOut p2d) 0
    (∀ (k : ℕ) (hkM : 2 ^ dLast.val + k ≤ M) (hk2 : k ≤ 2 ^ dLast.val) (w : Wire n), w ≠ wOut p2d →
      (oneHotSplitSkip wBit wOut hBO hInj dLast 2 k hkM hk2).fwdBits δ2 w =
          (oneHotSplitSkip wBit wOut hBO hInj dLast 2 k hkM hk2).fwdBits δ2z w) ∧
    (∀ (k : ℕ) (hkM : 2 ^ dLast.val + k ≤ M) (hk2 : k ≤ 2 ^ dLast.val),
      (oneHotSplitSkip wBit wOut hBO hInj dLast 2 k hkM hk2).fwdBits δ2 (wOut p2d) = δ2 (wOut p2d))
          := by
  intro δ2z
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · induction k with
    | zero => exact fun _ _ _ hw ↦ (Function.update_of_ne hw 0 δ2).symm
    | succ m ih =>
        intro hkM hk2 w hw; dsimp only [oneHotSplitSkip]
        by_cases hs : 2 ≤ m
        · rw [dite_eq_left hs, fwdBits_seq, fwdBits_seq, fwdBits_seq, fwdBits_seq,
            fwdBits_and_apply, fwdBits_cnot_apply, fwdBits_and_apply, fwdBits_cnot_apply]
          let qL : Fin M := ⟨m, splitSkip_lt_lo hkM⟩
          let qH : Fin M := ⟨2 ^ dLast.val + m, hkM⟩
          have eL := ih (Nat.le_of_succ_le hkM) (Nat.le_of_succ_le hk2) _
            (hInj qL p2d fun e ↦ Nat.ne_of_lt hk2 (hp2dEq ▸ congrArg Fin.val e))
          have eH := ih (Nat.le_of_succ_le hkM) (Nat.le_of_succ_le hk2) _ (hInj qH p2d fun e ↦
            (fun hv ↦ by dsimp [qH] at hv; omega) (congrArg Fin.val e))
          have eB := ih (Nat.le_of_succ_le hkM) (Nat.le_of_succ_le hk2) _ (hBO dLast p2d)
          rcases eq_or_ne w (wOut qL) with rfl | hwL
          · simp [qL, qH, splitSkip_ne_lh hInj hkM, eL, eH, eB]
          · rcases eq_or_ne w (wOut qH) with rfl | hwH
            · simp [qL, qH, hwL, eH, eL, eB]
            · simpa [qL, qH, hwL, hwH] using ih (Nat.le_of_succ_le hkM) (Nat.le_of_succ_le hk2) w hw
        · rw [dite_eq_right hs]; exact ih _ _ w hw
  · induction k with
    | zero => exact fun _ _ ↦ rfl
    | succ m ih =>
        intro hkM hk2; dsimp only [oneHotSplitSkip]
        by_cases hs : 2 ≤ m
        · rw [dite_eq_left hs, fwdBits_seq, fwdBits_seq, fwdBits_and_apply, fwdBits_cnot_apply,
              Function.update_of_ne (hInj p2d _ fun e ↦
                  Nat.ne_of_gt hk2 (hp2dEq ▸ congrArg Fin.val e)),
              Function.update_of_ne (hInj p2d _ fun e ↦
                  Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le Nat.zero_lt_two hs))
                  (hp2dEq ▸ congrArg Fin.val e))]
          exact ih _ _
        · rw [dite_eq_right hs]; exact ih _ _
theorem oneHotPosZeroGated_stage6 {M D n : ℕ} (hD1 : 1 ≤ D)
    (hMlo : 2 ^ (D - 1) + 2 ≤ M) (hMhi : M ≤ 2 ^ D) (hPowSub : ∀ d < D - 1, 2 ^ d < M)
    (qAct : Wire n) (wBit : Fin D → Wire n) (wOut : Fin M → Wire n)
    (hAO : ∀ p, qAct ≠ wOut p) (hBO : ∀ d p, wBit d ≠ wOut p)
    (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q)
    (γ : BitAssignment n) (hIdxLt : idxValD wBit γ < M)
    (hOut0 : ∀ p : Fin M, γ (wOut p) = 0) :
    let p1 : Fin M :=
      ⟨1, Nat.lt_of_lt_of_le (by have := @Nat.one_le_two_pow (D - 1); omega) hMlo⟩
    let p2d : Fin M := ⟨2 ^ (D - 1), by omega⟩
    let p2d1 : Fin M := ⟨2 ^ (D - 1) + 1, hMlo⟩;
    let lo := idxValPrefix wBit γ (D - 1) (Nat.sub_le D 1);
    let b := γ (wBit ⟨D - 1, Nat.sub_lt hD1 Nat.zero_lt_one⟩);
    let len := min (M - 2 ^ (D - 1)) (2 ^ (D - 1))
    ∃ δ6 : BitAssignment n,
        (oneHotPosZeroGated hD1 hMlo hPowSub qAct wBit wOut hAO hBO hInj).fwdBits γ =
        Function.update δ6 (wOut p1) (δ6 (wOut p1) + δ6 (wOut p2d1)) ∧
      idxValD wBit γ = lo + (if b = 1 then 2 ^ (D - 1) else 0) ∧ len = M - 2 ^ (D - 1) ∧
          δ6 (wOut p2d1) = b + (γ qAct + (if 1 ≤ lo then 1 else 0)) + (if 2 ≤ lo
        ∧ lo < len then b else 0) ∧
      (∀ q : Fin M, q ≠ p2d1 → δ6 (wOut q) = if q = p2d then γ qAct + (if 1 ≤ lo then 1 else 0)
        else if q.val < 2 ^ (D - 1) then
          if 2 ≤ q.val
          ∧ q.val < len then (if q.val = 0 then 0 else if lo = q.val then 1 else 0) +
              (if q.val = 0 then 0 else if lo = q.val then 1 else 0) * b else (if q.val =
              0 then 0 else if lo = q.val then 1 else 0)
        else if 2 ^ (D - 1) + 2 ≤ q.val then (if lo = q.val - 2 ^ (D - 1) then 1 else 0) *
            b else 0) ∧
      (∀ w : Wire n, (∀ p : Fin M, w ≠ wOut p) → δ6 w = γ w) := by
  let dLast : Fin D := ⟨D - 1, Nat.sub_lt hD1 Nat.zero_lt_one⟩
  have hpow : 2 ^ (D - 1) < M := by omega
  have hp1Pow : 1 ≤ 2 ^ (D - 1) := Nat.one_le_two_pow
  have h2Pow : 2 ^ D = 2 ^ (D - 1) + 2 ^ (D - 1) := by
    cases D with | zero => omega | succ k => dsimp; ring
  let len := min (M - 2 ^ (D - 1)) (2 ^ (D - 1)); let p2d : Fin M := ⟨2 ^ (D - 1), hpow⟩;
  let p2d1 : Fin M := ⟨2 ^ (D - 1) + 1, hMlo⟩
  let lo := idxValPrefix wBit γ (D - 1) (Nat.sub_le D 1); let b := γ (wBit dLast);
  have hloLt : lo < 2 ^ (D - 1) := idxValPrefix_lt_pow wBit γ (D - 1) (Nat.sub_le D 1)
  have hIdxDecomp : idxValD wBit γ = lo + (if b = 1 then 2 ^ (D - 1) else 0) := by
    cases D with | zero => omega | succ _ => rfl
  have hlenEq : len = M - 2 ^ (D - 1) := min_eq_left (by omega)
  let δ0 := (oneHotZeroOuter wBit wOut hBO hInj (D - 1) (Nat.sub_le D 1) hPowSub).fwdBits γ
  obtain ⟨oLo, oHi, oOth⟩ :=
      fwdBits_oneHotZeroOuter wBit wOut hBO hInj γ hIdxLt hOut0 (D - 1) (Nat.sub_le D 1) hPowSub
  let δ1 := (ComputeProg.cnot qAct (wOut p2d) (hAO p2d)).fwdBits δ0
  let hNe1 (m : ℕ) (hm : 0 + m < M) (_ : 1 ≤ m) (_ : m < 2 ^ (D - 1)) : wOut ⟨0 + m, hm⟩ ≠
      wOut p2d :=
    hInj _ p2d fun e ↦ (fun hv ↦ by dsimp [p2d] at hv; omega) (congrArg Fin.val e)
  obtain ⟨x1Dst, x1Oth⟩ := fwdBits_xorOffsetLoop_oneHot wOut 0 1 lo 1 (wOut p2d) δ1 (2 ^ (D - 1))
    (by omega) hNe1 fun m hm hm1 hmLt ↦ by
      dsimp only [δ1, δ0, lo, fwdBits_cnot_apply]
      rw [Function.update_of_ne (hNe1 m hm hm1 hmLt), oLo ⟨0 + m, hm⟩ (by dsimp; omega),
          ite_eq_right (by dsimp; omega)]
      exact ite_iff_eq ⟨fun _ ↦ by dsimp at *; omega, fun _ ↦ by dsimp; omega⟩ 1 0
  let δ2 := (xorOffsetLoop wOut 0 1 (wOut p2d) (2 ^ (D - 1)) (by omega) hNe1).fwdBits δ1
  have hp2dVal : δ2 (wOut p2d) = γ qAct + (if 1 ≤ lo then 1 else 0) := by
    rw [show δ2 (wOut p2d) = _ from x1Dst]
    dsimp only [δ1, δ0, fwdBits_cnot_apply]
    rw [Function.update_self, oHi p2d le_rfl, oOth qAct hAO, zero_add, add_right_inj]
    exact ite_iff_eq ⟨fun h ↦ h.1, fun h ↦ ⟨h, hloLt⟩⟩ 1 0
  let δ2z : BitAssignment n := Function.update δ2 (wOut p2d) 0
  have hδ2zOth {w : Wire n} (hne : w ≠ wOut p2d) : δ2z w = δ0 w :=
    (Function.update_of_ne hne _ _).trans ((x1Oth w hne).trans
      ((congrFun (fwdBits_cnot_apply qAct (wOut p2d)
          (hAO p2d) δ0) w).trans (Function.update_of_ne hne _ _)))
  have hHi2z : ∀ p : Fin M, 2 ^ dLast.val ≤ p.val → δ2z (wOut p) = 0 := fun p hp ↦
    if he : p =
        p2d then he ▸ Function.update_self _ _ _ else (hδ2zOth (hInj p p2d he)).trans (oHi p hp)
  obtain ⟨hSplitEq, hSplitP2d⟩ :=
      fwdBits_oneHotSplitSkip_ignore_p2d wBit wOut hBO hInj dLast p2d rfl δ2
  let δ3z :=
      (oneHotSplitSkip wBit wOut hBO hInj dLast 2 len (zg_len_hmM hpow) zg_len_hm2).fwdBits δ2z
  obtain ⟨sLo, sHi, sOth⟩ :=
      fwdBits_oneHotSplitSkip wBit wOut hBO hInj dLast 2 δ2z hHi2z len (zg_len_hmM hpow) zg_len_hm2
  let δ3 := (oneHotSplitSkip wBit wOut hBO hInj dLast 2 len (zg_len_hmM hpow) zg_len_hm2).fwdBits δ2
  have hb2z : δ2z (wBit dLast) = b := (hδ2zOth (hBO dLast p2d)).trans (oOth _ (hBO dLast))
  have hLo2z (p : Fin M) (hp : p.val < 2 ^ (D - 1)) : δ2z (wOut p) = if p.val =
      0 then 0 else if lo = p.val then 1 else 0 :=
    (hδ2zOth (hInj p p2d fun e ↦ Nat.ne_of_lt hp (congrArg Fin.val e))).trans (oLo p hp)
  let hNe2 : ∀ (m : ℕ) (hm : 2 ^ (D - 1) + m < M), 2 ≤ m → m < len → wOut ⟨2 ^ (D - 1) + m, hm⟩ ≠
      wOut p2d1 :=
    fun _ _ _ _ ↦ hInj _ _ fun e ↦ by have hv := congrArg Fin.val e; dsimp [p2d1] at hv; omega
  have hp2d1Ne : wOut p2d1 ≠ wOut p2d := hInj _ _ fun e ↦
      Nat.succ_ne_self (2 ^ (D - 1)) (congrArg Fin.val e)
  let δ4 := (ComputeProg.cnot (wBit dLast) (wOut p2d1) (hBO dLast p2d1)).fwdBits δ3
  let δ5 := (ComputeProg.cnot (wOut p2d) (wOut p2d1) hp2d1Ne.symm).fwdBits δ4
  have hδ5Oth {w : Wire n} (hne1 : w ≠ wOut p2d1) : δ5 w = δ3 w :=
    ((congrFun (fwdBits_cnot_apply _ _ _ δ4) w).trans (Function.update_of_ne hne1 _ _)).trans
      ((congrFun (fwdBits_cnot_apply _ _ _ δ3) w).trans (Function.update_of_ne hne1 _ _))
  have hSrc5 : ∀ (m : ℕ) (hm : 2 ^ (D - 1) + m < M), 2 ≤ m → m < len →
      δ5 (wOut ⟨2 ^ (D - 1) + m, hm⟩) = if m = lo then b else 0 := fun m hm hm2 hmLt ↦ by
    let pm : Fin M := ⟨2 ^ (D - 1) + m, hm⟩
    have hne0 : wOut pm ≠ wOut p2d := hInj _ _ fun e ↦ by
      have hv := congrArg Fin.val e; dsimp [pm, p2d] at hv; omega
    rw [(hδ5Oth (hNe2 m hm hm2 hmLt)).trans (hSplitEq _ _ _ _ hne0), sHi pm (Nat.le_add_right _ _),
      dite_eq_left ⟨Nat.add_le_add_left hm2 _, Nat.add_lt_add_left hmLt _⟩,
      show (⟨pm.val - 2 ^ dLast.val, _⟩ : Fin M) =
          ⟨m, by omega⟩ from Fin.ext (by dsimp [pm, dLast]; omega),
      hLo2z ⟨m, by omega⟩ (by dsimp; omega), hb2z, ite_eq_right (by dsimp; omega)]
    by_cases hml : m = lo
    · subst hml; simp
    · rw [ite_eq_right (Ne.symm hml), ite_eq_right hml, zero_mul]
  obtain ⟨x2Dst, x2Oth⟩ :=
      fwdBits_xorOffsetLoop_oneHot wOut (2 ^ (D -
      1)) 2 lo b (wOut p2d1) δ5 len (zg_len_hmM hpow) hNe2 hSrc5
  let δ6 := (xorOffsetLoop wOut (2 ^ (D - 1)) 2 (wOut p2d1) len (zg_len_hmM hpow) hNe2).fwdBits δ5
  have hδ6Oth {w : Wire n} (hne1 : w ≠ wOut p2d1) : δ6 w = δ3 w :=
      (x2Oth w hne1).trans (hδ5Oth hne1)
  have hp2d1Val : δ6 (wOut p2d1) = b + (γ qAct + (if 1 ≤ lo then 1 else 0)) + (if 2 ≤ lo ∧ lo <
      len then b else 0) := by
    rw [show δ6 (wOut p2d1) = δ5 (wOut p2d1) + _ from x2Dst]
    dsimp only [δ5, δ4, δ3, fwdBits_cnot_apply]
    rw [Function.update_self, Function.update_self, Function.update_of_ne hp2d1Ne.symm,
      hSplitP2d, hp2dVal, hSplitEq _ _ _ _ hp2d1Ne, hSplitEq _ _ _ _ (hBO dLast p2d),
      sHi p2d1 (by dsimp [p2d1, dLast]; omega),
      dite_eq_right (by dsimp [p2d1, dLast]; omega), sOth _ (hBO dLast), hb2z, zero_add]
  refine ⟨δ6, ?_, hIdxDecomp, hlenEq, hp2d1Val, fun q hqNe1 ↦ ?_, fun w hw ↦
      (hδ6Oth (hw p2d1)).trans
    ((hSplitEq _ _ _ w (hw p2d)).trans ((sOth w hw).trans ((hδ2zOth (hw p2d)).trans (oOth w hw))))⟩
  · dsimp only [oneHotPosZeroGated]
    rw [fwdBits_seq, fwdBits_seq, fwdBits_seq, fwdBits_seq, fwdBits_seq, fwdBits_seq, fwdBits_seq,
        fwdBits_cnot_apply]
  · rw [hδ6Oth (hInj q p2d1 hqNe1)]
    by_cases hq2d : q = p2d
    · subst hq2d; dsimp only [δ3]; rw [ite_eq_left rfl, hSplitP2d, hp2dVal]
    · rw [ite_eq_right hq2d, show δ3 (wOut q) = _ from hSplitEq _ _ _ _ (hInj q p2d hq2d)]
      by_cases hlt : q.val < 2 ^ (D - 1)
      · rw [ite_eq_left hlt, sLo q hlt, hLo2z q hlt, hb2z]
      · have hgt2 : 2 ^ dLast.val + 2 ≤ q.val :=
          (fun _ _ ↦ by dsimp [dLast, p2d, p2d1] at *; omega) (mt Fin.ext hq2d)
              (mt Fin.ext hqNe1)
        rw [ite_eq_right hlt, ite_eq_left hgt2, sHi q (by dsimp [dLast]; omega),
          dite_eq_left ⟨hgt2, (fun _ ↦ by rw [hlenEq]; dsimp [dLast]; omega) q.isLt⟩,
          hLo2z ⟨q.val - 2 ^ dLast.val, by dsimp [dLast]; omega⟩ (by dsimp [dLast]; omega),
          hb2z, ite_eq_right (by dsimp [dLast] at hgt2 ⊢; omega)]
end QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
open Circuit Qubit PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases ite_iff_eq
    ValidZeroGatedSortedRouterInput)
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem progSupportedIn_pNotFlagsZG {M D n : ℕ} (r : RouterReg M D n) {P : Wire n → Prop}
    (h1 : P (rHas1 r)) (h2 : P (rRawHas2 r))
    (hi1 : ∀ d, P (rIdx1 r d)) (hi2 : ∀ d, P (rIdx2 r d))
    (hnm1 : ∀ d, P (rNotMin r d)) (hnm2 : ∀ d, P (rNotMax r d)) :
    ∀ k hk, ProgSupportedIn P (pNotFlagsZG r k hk)
  | 0, _ => trivial
  | k + 1, hk =>
        ⟨progSupportedIn_pNotFlagsZG r h1 h2 hi1 hi2 hnm1 hnm2 k (Nat.le_of_succ_le hk),
        ⟨h1, hnm1 _⟩,
    ⟨hi1 _, hnm1 _⟩, ⟨h2, hnm2 _⟩, ⟨hi2 _, hnm2 _⟩⟩
theorem progSupportedIn_pUMsbDownLoop {M D n : ℕ} (usePhantom : Bool)
    (r : RouterReg M D n) {P : Wire n → Prop}
    (h1 : P (rHas1 r)) (h2 : P (rRawHas2 r))
    (hi1 : ∀ d, P (rIdx1 r d)) (hi2 : ∀ d, P (rIdx2 r d))
    (hu : ∀ d, P (rUMsb r d)) :
    ∀ k hk, ProgSupportedIn P (pUMsbDownLoop usePhantom r k hk)
  | 0, _ => trivial
  | k + 1, hk =>
      ⟨⟨(by cases usePhantom <;> first | exact ⟨⟨hi1 _, hi2 _⟩, hi2 _⟩ |
          exact ⟨⟨hi1 _, hi2 _⟩, ⟨h1, hi2 _⟩, ⟨h2, hi2 _⟩, hi2 _⟩),
        ⟨hu _, hi2 _, hu _⟩,
        (by cases usePhantom <;> first | exact ⟨hi2 _, ⟨hi1 _, hi2 _⟩⟩ |
          exact ⟨hi2 _, ⟨h2, hi2 _⟩, ⟨h1, hi2 _⟩, ⟨hi1 _, hi2 _⟩⟩),
        ⟨hu _, hu _⟩⟩,
            progSupportedIn_pUMsbDownLoop usePhantom r h1 h2 hi1 hi2 hu k (Nat.lt_of_succ_lt hk)⟩
theorem progSupportedIn_pHdrD1ZG {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) {P : Wire n → Prop}
    (ng : ∀ {u : Fin (routerWidth M D)}, (u.val < 2 + 2 * D ∨ (basePub M D + 6 ≤ u.val ∧ u.val <
    basePub M D + 6 + 2 * D) ∨ (basePub M D + 7 + 2 * D + 2 * M ≤ u.val ∧ u.val < basePub M D + 7 +
    3 * D + 2 * M)) → P (r u)) : ProgSupportedIn P (pHdrD1ZG hD2 r) := by
  have hu (d : Fin D) : P (rUMsb r d) :=
      ng (Or.inr (Or.inr ⟨by dsimp; omega, by have := d.isLt; dsimp; omega⟩))
  have h1 : P (rHas1 r) := ng (Or.inl (by dsimp; omega))
  have h2 : P (rRawHas2 r) := ng (Or.inl (by dsimp; omega))
  have hi1 (d : Fin D) : P (rIdx1 r d) := ng (Or.inl (by have := d.isLt; dsimp; omega))
  have hi2 (d : Fin D) : P (rIdx2 r d) := ng (Or.inl (by have := d.isLt; dsimp; omega))
  have hnm1 (d : Fin D) : P (rNotMin r d) :=
    ng (Or.inr (Or.inl ⟨by dsimp; omega, by have := d.isLt; dsimp; omega⟩))
  have hnm2 (d : Fin D) : P (rNotMax r d) :=
    ng (Or.inr (Or.inl ⟨by dsimp; omega, by have := d.isLt; dsimp; omega⟩))
  exact ⟨progSupportedIn_pNotFlagsZG r h1 h2 hi1 hi2 hnm1 hnm2 D le_rfl,
    ⟨⟨hi1 _, hu _⟩, ⟨hi2 _, hu _⟩, ⟨h1, hu _⟩, ⟨h2, hu _⟩, ⟨h1, hu _⟩, ⟨hu _, hu _⟩⟩,
    progSupportedIn_pUMsbDownLoop true r h1 h2 hi1 hi2 hu (D - 2) (hdr_lt2 hD2)⟩
theorem validProg_pUMsbDownLoop {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) :
    ∀ (k : ℕ) (hk : k < D) (F : Finset (Wire n)),
      (∀ d : Fin D, rIdx2 r d ∉ F) →
      (∀ d : Fin D, rUMsb r d ∈ F ↔ d.val < k) →
      (pUMsbDownLoop usePhantom r k hk).ValidProg ∅ F
  | 0, _, _, _, _ => trivial
  | k + 1, hk, F, hi2, huF => by
      let dk : Fin D := ⟨k + 1, hk⟩
      let dk1 : Fin D := ⟨k, Nat.lt_of_succ_lt hk⟩
      let F' := F.erase (rUMsb r dk1)
      have hi2' (d : Fin D) : rIdx2 r d ∉ F' := fun hm ↦ hi2 d (Finset.mem_of_mem_erase hm)
      have hPre : (pUMsbPre usePhantom r dk).ValidProg ∅ F ∧
          (pUMsbPre usePhantom r dk).finalClean F = F := by
        cases usePhantom <;>
            exact
            ⟨by dsimp [pUMsbPre, ComputeProg.ValidProg, ComputeProg.finalClean]; simp [hi2 dk],
            rfl⟩
      have hPost : (pUMsbPost usePhantom r dk).ValidProg ∅ F' ∧
          (pUMsbPost usePhantom r dk).finalClean F' = F' := by
        cases usePhantom <;>
            exact
            ⟨by dsimp [pUMsbPost, ComputeProg.ValidProg, ComputeProg.finalClean]; simp [hi2' dk],
            rfl⟩
      dsimp only [pUMsbDownLoop, pUMsbStep, ComputeProg.ValidProg, ComputeProg.finalClean]
      rw [hPre.2, hPost.2]
      exact ⟨⟨hPre.1, ⟨Finset.notMem_empty _, Finset.notMem_empty _, Finset.notMem_empty _,
          (huF dk1).mpr (Nat.lt_succ_self k)⟩,
        hPost.1, ⟨Finset.notMem_empty _, Finset.notMem_empty _,
          Or.inl fun hm ↦ Nat.lt_irrefl (k + 1) ((huF dk).mp (Finset.mem_of_mem_erase hm))⟩⟩,
        validProg_pUMsbDownLoop usePhantom r k (Nat.lt_of_succ_lt hk) F' hi2' fun d ↦ by
          simp only [F', Finset.mem_erase, huF d]
          exact ⟨fun ⟨hne, hlt⟩ ↦ (fun _ : d.val ≠ k ↦ by omega) fun e ↦ hne (congrArg (rUMsb r)
              (Fin.ext e)),
            fun hlt ↦
                ⟨rUMsb_ne_of_ne r fun e ↦ Nat.ne_of_lt hlt (congrArg Fin.val e),
                Nat.lt_succ_of_lt hlt⟩⟩⟩
theorem fwdBits_eq_of_not_supp {n : ℕ} (p : ComputeProg n) {P : Wire n → Prop}
    (hp : ProgSupportedIn P p) (γ : BitAssignment n) {w : Wire n} (hw : ¬ P w) : p.fwdBits γ w =
    γ w := by
  induction p generalizing γ with
  | id => rfl
  | x tgt => exact Function.update_of_ne (fun e : w = tgt ↦ hw (e ▸ hp)) _ γ
  | cnot _ tgt _ => exact Function.update_of_ne (fun e : w = tgt ↦ hw (e ▸ hp.2)) _ γ
  | andGate _ _ tgt _ _ _ => exact Function.update_of_ne (fun e : w = tgt ↦ hw (e ▸ hp.2.2)) _ γ
  | seq p1 p2 ih1 ih2 => exact (ih2 hp.2 (p1.fwdBits γ)).trans (ih1 hp.1 γ)
theorem zmod2_pre_true (a b c e : ZMod 2) : b + a + c + e + 1 = 1 + (a + b + c + e) := by ring
theorem zmod2_post_true (a b c e : ZMod 2) : 1 + (a + b + c + e) + 1 + e + c + a = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases e with rfl | rfl <;> decide
theorem fwdBits_pNotFlagsZG {M D n : ℕ} (r : RouterReg M D n) (γ : BitAssignment n)
    (hnm1 : ∀ d : Fin D, γ (rNotMin r d) = 0)
    (hnm2 : ∀ d : Fin D, γ (rNotMax r d) = 0) :
    ∀ (k : ℕ) (hk : k ≤ D),
      (∀ d : Fin D,
        (pNotFlagsZG r k hk).fwdBits γ (rNotMin r d) =
          if d.val < k then γ (rHas1 r) + γ (rIdx1 r d) else 0) ∧
      (∀ d : Fin D,
        (pNotFlagsZG r k hk).fwdBits γ (rNotMax r d) =
          if d.val < k then γ (rRawHas2 r) + γ (rIdx2 r d) else 0) ∧
      (∀ w : Wire n, (∀ d, w ≠ rNotMin r d) → (∀ d, w ≠ rNotMax r d) →
        (pNotFlagsZG r k hk).fwdBits γ w = γ w)
  | 0, _ => ⟨hnm1, hnm2, fun _ _ _ ↦ rfl⟩
  | k + 1, hk => by
      obtain ⟨ihMin, ihMax, ihOth⟩ := fwdBits_pNotFlagsZG r γ hnm1 hnm2 k (Nat.le_of_succ_le hk)
      let dk : Fin D := ⟨k, hk⟩
      have ηPub {u : Fin (routerWidth M D)} (_ : u.val < basePub M D) :
          (pNotFlagsZG r k (Nat.le_of_succ_le hk)).fwdBits γ (r u) = γ (r u) :=
        ihOth _ (fun d ↦ rr_ne r (by have := d.isLt; dsimp; omega)) fun d ↦
            rr_ne r (by have := d.isLt; dsimp; omega)
      have hMinNeMax (d1 d2 : Fin D) : rNotMin r d1 ≠ rNotMax r d2 :=
        rr_ne r (by have := d1.isLt; have := d2.isLt; dsimp; omega)
      dsimp only [pNotFlagsZG, ComputeProg.fwdBits]
      refine ⟨fun d ↦ ?_, fun d ↦ ?_, fun w nw1 nw2 ↦ by
        simp only [Function.update_of_ne (nw2 ⟨k, hk⟩), Function.update_of_ne (nw1 ⟨k, hk⟩)]
        exact ihOth w nw1 nw2⟩
      · simp only [Function.update_of_ne (hMinNeMax d ⟨k, hk⟩)]
        by_cases hdeq : d = dk
        · subst hdeq
          simp only [dk, Function.update_self, Function.update_of_ne ((hne_zg_hdr r).1.2.1 ⟨k, hk⟩),
              ihMin ⟨k, hk⟩,
            Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self, zero_add,
            ηPub (u := ⟨0, by unfold routerWidth; omega⟩)
                (by unfold basePub; dsimp; omega),
            ηPub (u := ⟨2 + k, by unfold routerWidth; omega⟩)
                (by unfold basePub; dsimp; omega)]
        · have _ : d.val ≠ k := fun e ↦ hdeq (Fin.ext e)
          simp only [Function.update_of_ne (rr_ne r (by dsimp; omega) : rNotMin r d ≠
              rNotMin r ⟨k, hk⟩), ihMin d]
          exact ite_iff_eq (by omega) _ _
      · by_cases hdeq : d = dk
        · subst hdeq
          simp only [dk, Function.update_self, Function.update_of_ne ((hne_zg_hdr r).1.2.2.2 ⟨k,
              hk⟩),
            Function.update_of_ne (hMinNeMax ⟨k, hk⟩ ⟨k, hk⟩).symm,
            Function.update_of_ne (rr_ne r (by unfold basePub; dsimp; omega) : rRawHas2 r ≠
                rNotMin r ⟨k, hk⟩),
            Function.update_of_ne (rr_ne r (by unfold basePub; dsimp; omega) : rIdx2 r ⟨k,
                hk⟩ ≠ rNotMin r ⟨k, hk⟩),
            ihMax ⟨k, hk⟩, Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self, zero_add,
            ηPub (u := ⟨1, by unfold routerWidth; omega⟩)
                (by unfold basePub; dsimp; omega),
            ηPub (u := ⟨2 + D + k, by unfold routerWidth; omega⟩)
                (by unfold basePub; dsimp; omega)]
        · have _ : d.val ≠ k := fun e ↦ hdeq (Fin.ext e)
          simp only [Function.update_of_ne (rr_ne r (by dsimp; omega) : rNotMax r d ≠
              rNotMax r ⟨k, hk⟩),
            Function.update_of_ne (hMinNeMax ⟨k, hk⟩ d).symm, ihMax d]
          exact ite_iff_eq (by omega) _ _
/--
Bit-difference indicator at bit `d`: `rIdx1[d] + rIdx2[d]` (`usePhantom = false`) or
`rIdx1[d] + rIdx2[d] + rHas1 + rRawHas2` (`usePhantom = true`).
-/
def diffBit {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) (γ : BitAssignment n)
    (d : Fin D) : ZMod 2 :=
    if usePhantom then γ (rIdx1 r d) + γ (rIdx2 r d) + γ (rHas1 r) +
    γ (rRawHas2 r) else γ (rIdx1 r d) + γ (rIdx2 r d)
theorem diffBit_congr {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n)
    {γ₁ γ₂ : BitAssignment n} (d : Fin D) (hi1 : γ₁ (rIdx1 r d) = γ₂ (rIdx1 r d))
    (hi2 : γ₁ (rIdx2 r d) = γ₂ (rIdx2 r d)) (h1 : γ₁ (rHas1 r) = γ₂ (rHas1 r))
    (h2 : γ₁ (rRawHas2 r) = γ₂ (rRawHas2 r)) : diffBit usePhantom r γ₁ d =
    diffBit usePhantom r γ₂ d := by unfold diffBit; rw [hi1, hi2, h1, h2]
theorem fwdBits_pUMsbStep {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) (m : ℕ)
    (hm : m + 1 < D) (η : BitAssignment n) (hClean : η (rUMsb r ⟨m, Nat.lt_of_succ_lt hm⟩) = 0) :
    (pUMsbStep usePhantom r m hm).fwdBits η (rUMsb r ⟨m + 1, hm⟩) = η (rUMsb r ⟨m + 1, hm⟩) *
    diffBit usePhantom r η ⟨m + 1, hm⟩ ∧ (pUMsbStep usePhantom r m hm).fwdBits η (rUMsb r ⟨m,
    Nat.lt_of_succ_lt hm⟩) = η (rUMsb r ⟨m + 1, hm⟩) * (1 + diffBit usePhantom r η ⟨m + 1, hm⟩) ∧
    (∀ w : Wire n, w ≠ rUMsb r ⟨m + 1, hm⟩ → w ≠ rUMsb r ⟨m, Nat.lt_of_succ_lt hm⟩ →
    (pUMsbStep usePhantom r m hm).fwdBits η w = η w) := by
  let dk : Fin D := ⟨m + 1, hm⟩; let dk1 : Fin D := ⟨m, Nat.lt_of_succ_lt hm⟩;
  have hNeU : dk1 ≠ dk := hdr_succ_ne m hm; let hu := (hne_zg_hdr r).2.2
  have hPreSpec : (pUMsbPre usePhantom r dk).fwdBits η = Function.update η (rIdx2 r dk)
      (1 + diffBit usePhantom r η dk) := by
    cases usePhantom <;> funext w <;> dsimp [pUMsbPre, diffBit, ComputeProg.fwdBits] <;>
        by_cases hw : w = rIdx2 r dk
    · subst hw; simp only [Function.update_self]; ring
    · simp only [Function.update_of_ne hw]
    · subst hw; simp only [Function.update_self, Function.update_of_ne (hu.2.1 dk),
      Function.update_of_ne (hu.2.2.1 dk)]; exact zmod2_pre_true _ _ _ _
    · simp only [Function.update_of_ne hw]
  let ηAnd := Function.update (Function.update η (rIdx2 r dk) (1 + diffBit usePhantom r η dk))
    (rUMsb r dk1) (η (rUMsb r dk) * (1 + diffBit usePhantom r η dk))
  have hAndSpec : (ComputeProg.andGate (rUMsb r dk) (rIdx2 r dk) (rUMsb r dk1)
      (rUMsb_ne_rIdx2 r dk dk)
      (rUMsb_ne_of_ne r hNeU).symm (rUMsb_ne_rIdx2 r dk1 dk).symm).fwdBits ((pUMsbPre usePhantom r
          dk).fwdBits η) = ηAnd := by
    rw [hPreSpec]; funext w; dsimp only [ComputeProg.fwdBits, ηAnd]
    by_cases hw : w = rUMsb r dk1 <;> simp [hw, dk1, rUMsb_ne_rIdx2 r dk1 dk,
        rUMsb_ne_rIdx2 r dk dk, hClean]
  have hPostSpec : (pUMsbPost usePhantom r dk).fwdBits ηAnd =
      Function.update η (rUMsb r dk1) (η (rUMsb r dk) * (1 + diffBit usePhantom r η dk)) := by
    have hA1 : ηAnd (rIdx1 r dk) = η (rIdx1 r dk) := by
      dsimp only [ηAnd]; rw [Function.update_of_ne (rr_ne r
        (by have := dk.isLt; unfold basePub; dsimp; omega)),
        Function.update_of_ne (hu.1 dk)]
    have hAH1 : ηAnd (rHas1 r) = η (rHas1 r) := by simp [ηAnd, hu.2.2.2.1 dk1, hu.2.1 dk]
    have hAH2 : ηAnd (rRawHas2 r) = η (rRawHas2 r) := by simp [ηAnd, hu.2.2.2.2.1 dk1, hu.2.2.1 dk]
    have hA2 : ηAnd (rIdx2 r dk) = 1 + diffBit usePhantom r η dk := by
      simp [ηAnd, (rUMsb_ne_rIdx2 r dk1 dk).symm]
    have hOth {w : Wire n} (hw : w ≠ rIdx2 r dk) :
        ηAnd w = Function.update η (rUMsb r dk1)
            (η (rUMsb r dk) * (1 + diffBit usePhantom r η dk)) w := by
      by_cases hu1 : w = rUMsb r dk1 <;> simp [ηAnd, hu1, hw]
    cases usePhantom <;> funext w <;> dsimp [pUMsbPost, ComputeProg.fwdBits]
    · by_cases hw : w = rIdx2 r dk
      · subst hw; rw [Function.update_self, Function.update_self,
            Function.update_of_ne (hu.1 dk),
          Function.update_of_ne (rUMsb_ne_rIdx2 r dk1 dk).symm, hA2, hA1]
        dsimp [diffBit]; rcases zmod2_cases (η (rIdx1 r dk)) with h1 | h1 <;>
          rcases zmod2_cases (η (rIdx2 r dk)) with h2 | h2 <;> rw [h1, h2] <;> decide
      · simpa only [Function.update_of_ne hw] using hOth hw
    · by_cases hw : w = rIdx2 r dk
      · subst hw
        simp only [Function.update_self, Function.update_of_ne (hu.1 dk),
            Function.update_of_ne (hu.2.1 dk),
          Function.update_of_ne (hu.2.2.1 dk), Function.update_of_ne (rUMsb_ne_rIdx2 r dk1 dk).symm,
              hA2, hA1, hAH1, hAH2]
        exact zmod2_post_true _ _ _ _
      · simpa only [Function.update_of_ne hw] using hOth hw
  unfold pUMsbStep; rw [fwdBits_seq, fwdBits_seq, fwdBits_seq, hAndSpec, hPostSpec];
    dsimp only [ComputeProg.fwdBits]
  refine ⟨?_, by rw [Function.update_of_ne (rUMsb_ne_of_ne r hNeU), Function.update_self],
    fun w n1 n2 ↦ by rw [Function.update_of_ne n1, Function.update_of_ne n2]⟩
  rw [Function.update_self, Function.update_of_ne (rUMsb_ne_of_ne r hNeU).symm,
      Function.update_self]
  rcases zmod2_cases (η (rUMsb r dk)) with h1 | h1 <;>
      rcases zmod2_cases (diffBit usePhantom r η dk) with h2 | h2 <;>
    rw [h1, h2] <;> decide
theorem fwdBits_pUMsbDownLoop_zero {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) :
    ∀ (k : ℕ) (hk : k < D) (η : BitAssignment n),
      (∀ d : Fin D, d.val ≤ k → η (rUMsb r d) = 0) →
      (pUMsbDownLoop usePhantom r k hk).fwdBits η = η
  | 0, _, _, _ => rfl
  | k + 1, hk, η, h0 => by
      obtain ⟨sDk, sDk1, sOth⟩ :=
          fwdBits_pUMsbStep usePhantom r k hk η (h0 ⟨k, Nat.lt_of_succ_lt hk⟩ (Nat.le_succ k))
      have hStepEq : (pUMsbStep usePhantom r k hk).fwdBits η = η := funext fun w ↦ by
        by_cases h1 : w = rUMsb r ⟨k + 1, hk⟩
        · subst h1; rw [sDk, h0 ⟨k + 1, hk⟩ le_rfl, zero_mul]
        · by_cases h2 : w = rUMsb r ⟨k, Nat.lt_of_succ_lt hk⟩
          · subst h2; rw [sDk1, h0 ⟨k + 1, hk⟩ le_rfl, zero_mul]; exact (h0 ⟨k,
            Nat.lt_of_succ_lt hk⟩ (Nat.le_succ k)).symm
          · exact sOth w h1 h2
      dsimp only [pUMsbDownLoop, ComputeProg.fwdBits]; rw [hStepEq]
      exact fwdBits_pUMsbDownLoop_zero usePhantom r k (Nat.lt_of_succ_lt hk) η (fun d hd ↦
          h0 d (Nat.le_succ_of_le hd))
theorem fwdBits_pUMsbDownLoop_one {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) :
    ∀ (k : ℕ) (hk : k < D) (η : BitAssignment n) (dStar : Fin D),
      η (rUMsb r ⟨k, hk⟩) = 1 →
      (∀ d : Fin D, d.val < k → η (rUMsb r d) = 0) →
      dStar.val ≤ k →
      diffBit usePhantom r η dStar = 1 →
      (∀ d : Fin D, dStar.val < d.val → d.val ≤ k → diffBit usePhantom r η d = 0) →
      (∀ d : Fin D, d.val ≤ k →
        (pUMsbDownLoop usePhantom r k hk).fwdBits η (rUMsb r d) =
          if d = dStar then 1 else 0) ∧
      (∀ w : Wire n, (∀ d : Fin D, d.val ≤ k → w ≠ rUMsb r d) →
        (pUMsbDownLoop usePhantom r k hk).fwdBits η w = η w)
  | 0, hk, η, dStar, hTop, _, hdS, _, _ => by
      obtain rfl : dStar = ⟨0, hk⟩ := Fin.ext (Nat.eq_zero_of_le_zero hdS)
      refine ⟨fun d hd ↦ ?_, fun _ _ ↦ rfl⟩
      obtain rfl : d = ⟨0, hk⟩ := Fin.ext (Nat.eq_zero_of_le_zero hd)
      exact hTop.trans (ite_eq_left rfl).symm
  | k + 1, hk, η, dStar, hTop, hClean, hdS, hDiff1, hDiff0 => by
      let dk : Fin D := ⟨k + 1, hk⟩
      let dk1 : Fin D := ⟨k, Nat.lt_of_succ_lt hk⟩
      let η' := (pUMsbStep usePhantom r k hk).fwdBits η
      obtain ⟨sDk, sDk1, sOth⟩ :=
          fwdBits_pUMsbStep usePhantom r k hk η (hClean dk1 (Nat.lt_succ_self k))
      dsimp only [pUMsbDownLoop, ComputeProg.fwdBits]
      have sDk' : η' (rUMsb r dk) = diffBit usePhantom r η dk :=
          sDk.trans ((congrArg (· * _) hTop).trans (one_mul _))
      have sDk1' : η' (rUMsb r dk1) = 1 + diffBit usePhantom r η dk :=
          sDk1.trans ((congrArg (· * _) hTop).trans (one_mul _))
      have hClean' (d : Fin D) (hlt : d.val < k) : η' (rUMsb r d) = 0 :=
        (sOth _ (rUMsb_ne_of_ne r fun e ↦ Nat.ne_of_lt (Nat.lt_succ_of_lt hlt) (congrArg Fin.val e))
          (rUMsb_ne_of_ne r fun e ↦
              Nat.ne_of_lt hlt (congrArg Fin.val e))).trans (hClean d (Nat.lt_succ_of_lt hlt))
      by_cases hEqTop : dStar = dk
      · subst hEqTop
        have hZeroRest (d : Fin D) (hd : d.val ≤ k) : η' (rUMsb r d) = 0 :=
          if hdEq : d = dk1 then hdEq ▸ sDk1'.trans ((congrArg (1 + ·) hDiff1).trans (by decide))
          else hClean' d (Nat.lt_of_le_of_ne hd fun e ↦ hdEq (Fin.ext e))
        rw [fwdBits_pUMsbDownLoop_zero usePhantom r k (Nat.lt_of_succ_lt hk) η' hZeroRest]
        refine ⟨fun d hd ↦ if hdDk : d =
            dk then hdDk ▸ (sDk'.trans hDiff1).trans (ite_eq_left rfl).symm
          else (hZeroRest d (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hd fun e ↦
              hdDk (Fin.ext e)))).trans (ite_eq_right hdDk).symm,
          fun w nw ↦ sOth w (nw dk le_rfl) (nw dk1 (Nat.le_succ k))⟩
      · have hdSk : dStar.val ≤ k :=
            Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hdS fun e ↦ hEqTop (Fin.ext e))
        have hDiffTop0 : diffBit usePhantom r η dk = 0 := hDiff0 dk (Nat.lt_succ_of_le hdSk) le_rfl
        have hDiffEq (d : Fin D) : diffBit usePhantom r η' d = diffBit usePhantom r η d :=
          let hu := (hne_zg_hdr r).2.2
          diffBit_congr usePhantom r d
            (sOth _ (rr_ne r (by have := d.isLt; unfold basePub; dsimp; omega))
              (rr_ne r (by have := d.isLt; unfold basePub; dsimp; omega)))
            (sOth _ (rUMsb_ne_rIdx2 r dk d).symm (rUMsb_ne_rIdx2 r dk1 d).symm)
            (sOth _ (hu.2.2.2.1 dk) (hu.2.2.2.1 dk1)) (sOth _ (hu.2.2.2.2.1 dk) (hu.2.2.2.2.1 dk1))
        obtain ⟨ihU, ihO⟩ :=
            fwdBits_pUMsbDownLoop_one usePhantom r k (Nat.lt_of_succ_lt hk) η' dStar
          (sDk1'.trans ((congrArg (1 + ·) hDiffTop0).trans (add_zero 1))) hClean' hdSk
          ((hDiffEq dStar).trans hDiff1)
              (fun d h1 h2 ↦ (hDiffEq d).trans (hDiff0 d h1 (Nat.le_succ_of_le h2)))
        refine ⟨fun d hd ↦ if hdDk : d = dk then by
            subst hdDk
            rw [ihO _ (fun d' hd' ↦ rUMsb_ne_of_ne r fun e ↦
                Nat.not_lt_of_ge hd' (congrArg Fin.val e ▸ Nat.lt_succ_self k)),
              sDk'.trans hDiffTop0, ite_eq_right (Ne.symm hEqTop)]
          else ihU d (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hd fun e ↦ hdDk (Fin.ext e))),
          fun w nw ↦
              (ihO w fun d hd ↦ nw d (Nat.le_succ_of_le hd)).trans (sOth w (nw dk le_rfl)
              (nw dk1 (Nat.le_succ k)))⟩
theorem testBit_idxValD_fin {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n)
    (d : Fin D) : (idxValD wBit β).testBit d.val = decide (β (wBit d) = 1) := by
  rw [testBit_idxValD, dite_eq_left d.isLt]
theorem not_flag_of_one {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n)
    (d : Fin D) : 1 + β (wBit d) = if (idxValD wBit β).testBit d.val then 0 else 1 := by
  rw [testBit_idxValD_fin]; rcases zmod2_cases (β (wBit d)) with h | h <;> rw [h] <;> decide
theorem zmod2_add_eq_one_iff_ne (a b : ZMod 2) : a + b = 1 ↔ decide (a = 1) ≠ decide (b = 1) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide
theorem zmod2_add_eq_zero_iff_eq (a b : ZMod 2) : a + b = 0 ↔ decide (a = 1) = decide (b = 1) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide
theorem msb_diff_mode2 {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n)
    (hlt : idxValD (rIdx1 r) β < idxValD (rIdx2 r) β) : ∃ dStar : Fin D,
    (idxValD (rIdx1 r) β).testBit dStar.val = false ∧ (idxValD (rIdx2 r) β).testBit dStar.val =
    true ∧ β (rIdx1 r dStar) + β (rIdx2 r dStar) = 1 ∧ (∀ d : Fin D, dStar.val < d.val →
    β (rIdx1 r d) + β (rIdx2 r d) = 0) := by
  obtain ⟨dStar, hne, hhi, _,
    h1false⟩ :=
        exists_msb_diff (idxValPrefix_lt_two_pow (rIdx1 r) β D le_rfl)
        (idxValPrefix_lt_two_pow (rIdx2 r) β D le_rfl) (ne_of_lt hlt)
  have hb1 : (idxValD (rIdx1 r) β).testBit dStar.val = false := by
    cases hb : (idxValD (rIdx1 r) β).testBit dStar.val <;>
      first | rfl | exact absurd (h1false hb) (Nat.not_lt_of_gt hlt)
  have hb2 : (idxValD (rIdx2 r) β).testBit dStar.val = true := by
    cases hb : (idxValD (rIdx2 r) β).testBit dStar.val <;> first
      | exact absurd (hb1.trans hb.symm) hne
      | rfl
  exact ⟨dStar, hb1, hb2,
    (zmod2_add_eq_one_iff_ne _ _).mpr ((testBit_idxValD_fin (rIdx1 r) β dStar).symm ▸
        (testBit_idxValD_fin (rIdx2 r) β dStar).symm ▸ hne),
    fun d hd ↦
        (zmod2_add_eq_zero_iff_eq _ _).mpr ((testBit_idxValD_fin (rIdx1 r) β d).symm ▸
        (testBit_idxValD_fin (rIdx2 r) β d).symm ▸ hhi d hd)⟩
theorem idxValPrefix_ones {D n : ℕ} (wBit : Fin D → Wire n) : ∀ (k : ℕ)
    (hk : k ≤ D), idxValPrefix wBit
    (fun _ ↦ 1) k hk + 1 = 2 ^ k
  | 0, _ => rfl
  | k + 1, hk => by
      have ih := idxValPrefix_ones wBit k (Nat.le_of_succ_le hk)
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      dsimp [idxValPrefix]; omega
theorem msb_diff_mode1 {M D n : ℕ} (hMD : M < 2 ^ D) (r : RouterReg M D n) (β : BitAssignment n)
    (hx : idxValD (rIdx1 r) β < M) : ∃ dStar : Fin D, (idxValD (rIdx1 r) β).testBit dStar.val =
    false ∧ β (rIdx1 r dStar) + 1 = 1 ∧ (∀ d : Fin D, dStar.val < d.val → β (rIdx1 r d) + 1 = 0)
    := by
  let ones : BitAssignment n := fun _ ↦ 1
  have hyEq : idxValD (rIdx1 r) ones + 1 = 2 ^ D := idxValPrefix_ones (rIdx1 r) D le_rfl
  have hlt : idxValD (rIdx1 r) β < idxValD (rIdx1 r) ones := by omega
  obtain ⟨dStar, hne, hhi, _,
    h1false⟩ :=
        exists_msb_diff (idxValPrefix_lt_two_pow (rIdx1 r) β D le_rfl) (by omega) (ne_of_lt hlt)
  have hb1 : (idxValD (rIdx1 r) β).testBit dStar.val = false := by
    cases hb : (idxValD (rIdx1 r) β).testBit dStar.val <;>
      first | rfl | exact absurd (h1false hb) (Nat.not_lt_of_gt hlt)
  exact ⟨dStar, hb1,
      (zmod2_add_eq_one_iff_ne _ _).mpr ((testBit_idxValD_fin (rIdx1 r) β dStar).symm ▸
      by simp [hb1]),
    fun d hd ↦
        (zmod2_add_eq_zero_iff_eq _ _).mpr ((testBit_idxValD_fin (rIdx1 r) β d).symm ▸
        (hhi d hd).trans ((testBit_idxValD_fin (rIdx1 r) ones d).trans rfl))⟩
/--
Agreement of an intermediate bit assignment `γ` with a valid router input `β` on all public
wires, plane buffers, and private scratch wires outside `[bp .. bp + 6)`, `rCtrlLo`/`rCtrlHi`,
and `rTmpGt..rIdxMax`.
-/
def AgreesBeforeHdr {M D n : ℕ} (r : RouterReg M D n) (β γ : BitAssignment n) : Prop :=
    γ (rHas1 r) = β (rHas1 r) ∧ γ (rRawHas2 r) = β (rRawHas2 r) ∧ (∀ d : Fin D, γ (rIdx1 r d) =
    β (rIdx1 r d)) ∧ (∀ d : Fin D, γ (rIdx2 r d) = β (rIdx2 r d)) ∧ (∀ b : Fin 24, γ (rBufLo r b) =
    0 ∧ γ (rBufHi r b) = 0 ∧ γ (rHA r b) = 0 ∧ γ (rHB r b) = 0) ∧ γ (rAnc r) = 0 ∧
    (∀ d : Fin D, γ (rNotMin r d) = 0 ∧ γ (rNotMax r d) = 0 ∧ γ (rUMsb r d) = 0 ∧ γ (rAMsb r d) =
    0 ∧ γ (rCReg r d) = 0)
theorem agreesBeforeHdr_of_eq_outside {M D n : ℕ} (r : RouterReg M D n) {β γ : BitAssignment n}
    (hβ : ValidRouterInput r β) (hOth : ∀ {u : Fin (routerWidth M D)}, (u.val < basePub M D ∨
    (basePub M D + 6 ≤ u.val ∧ u.val < basePub M D + 6 + 2 * D) ∨ (basePub M D + 7 + 2 * D + 2 * M ≤
    u.val ∧ u.val < basePub M D + 7 + 3 * D + 2 * M) ∨ basePub M D + 7 + 7 * D + 2 * M ≤ u.val) →
    γ (r u) = β (r u)) : AgreesBeforeHdr r β γ := by
  have pub {u : Fin (routerWidth M D)} (hu : u.val < basePub M D) : γ (r u) = β (r u) :=
      hOth (.inl hu)
  have prv {u : Fin (routerWidth M D)} (hu : basePub M D ≤ u.val)
      (h : (basePub M D + 6 ≤ u.val ∧ u.val < basePub M D + 6 + 2 * D) ∨
        (basePub M D + 7 + 2 * D + 2 * M ≤ u.val ∧ u.val < basePub M D + 7 + 3 * D + 2 * M) ∨
        basePub M D + 7 + 7 * D + 2 * M ≤ u.val) : γ (r u) = 0 :=
    (hOth (.inr h)).trans (hβ.2.2.2.2 _ ((mem_sPrivCleanSet_iff r _).mpr hu))
  refine ⟨pub (by unfold basePub; dsimp; omega), pub (by unfold basePub; dsimp; omega),
    fun d ↦ pub (by have := d.isLt; unfold basePub; dsimp; omega),
    fun d ↦ pub (by have := d.isLt; unfold basePub; dsimp; omega), fun b ↦ by
      have _ := b.isLt
      exact ⟨(pub (by unfold basePub; dsimp; omega)).trans (hβ.2.2.2.1 b).1,
        (pub (by unfold basePub; dsimp; omega)).trans (hβ.2.2.2.1 b).2.1,
        (pub (by unfold basePub; dsimp; omega)).trans (hβ.2.2.2.1 b).2.2.1,
        (pub (by unfold basePub; dsimp; omega)).trans (hβ.2.2.2.1 b).2.2.2⟩,
    prv (by dsimp; omega) (.inr (.inr (by dsimp; omega))),
    fun d ↦ ⟨prv (by dsimp; omega) (.inl ⟨by dsimp; omega, by dsimp; omega⟩),
      prv (by dsimp; omega) (.inl ⟨by dsimp; omega, by dsimp; omega⟩),
      prv (by dsimp; omega) (.inr (.inl ⟨Nat.le_add_right _ _, by dsimp; omega⟩)),
      prv (by dsimp; omega) (.inr (.inr (by dsimp; omega))),
      prv (by dsimp; omega) (.inr (.inr (by dsimp; omega)))⟩⟩
theorem fwdBits_pHdrD1ZG_spec {M D n : ℕ} (hMD : M < 2 ^ D) (hD2 : 2 ≤ D)
    (r : RouterReg M D n) {β γ : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β)
    (hAg : AgreesBeforeHdr r β γ) :
    let δ := (pHdrD1ZG hD2 r).fwdBits γ
    δ (rHas1 r) = β (rHas1 r) ∧ δ (rRawHas2 r) = β (rRawHas2 r) ∧ (∀ d : Fin D,
      δ (rNotMin r d) = β (rHas1 r) + β (rIdx1 r d)) ∧
    (∀ d : Fin D, δ (rNotMax r d) = β (rRawHas2 r) + β (rIdx2 r d)) ∧ (β (rHas1 r) = 0 →
        ∀ d : Fin D,
      δ (rUMsb r d) = 0) ∧
    (β (rHas1 r) = 1 → β (rRawHas2 r) = 0 → ∃ dStar : Fin D,
        (idxValD (rIdx1 r) β).testBit dStar.val = false
      ∧ ∀ d : Fin D, δ (rUMsb r d) = if d = dStar then 1 else 0) ∧
    (β (rHas1 r) = 1 → β (rRawHas2 r) = 1 → ∃ dStar : Fin D,
        (idxValD (rIdx1 r) β).testBit dStar.val = false
      ∧ (idxValD (rIdx2 r) β).testBit dStar.val = true ∧ ∀ d : Fin D,
      δ (rUMsb r d) = if d = dStar then 1 else 0) := by
  let δ := (pHdrD1ZG hD2 r).fwdBits γ; let dTop : Fin D := ⟨D - 1, hdr_lt1 (Nat.le_of_succ_le hD2)⟩;
  let dSub : Fin D := ⟨D - 2, hdr_lt2 hD2⟩; have hNeTS : dTop ≠ dSub := hdr_top_ne_sub hD2;
  let hu := (hne_zg_hdr r).2.2
  obtain ⟨nfMin, nfMax, nfOth⟩ :=
      fwdBits_pNotFlagsZG r γ (fun d ↦ (hAg.2.2.2.2.2.2 d).1)
      (fun d ↦ (hAg.2.2.2.2.2.2 d).2.1) D le_rfl
  let γ1 := (pNotFlagsZG r D le_rfl).fwdBits γ;
  let pInitTop :=
      ComputeProg.seq (.cnot (rIdx1 r dTop) (rUMsb r dTop) (hu.2.2.2.2.2.1 dTop))
      (.seq (.cnot (rIdx2 r dTop) (rUMsb r dTop) (hu.2.2.2.2.2.2.1 dTop))
      (.seq (.cnot (rHas1 r) (rUMsb r dTop) (hu.2.2.2.1 dTop))
      (.seq (.cnot (rRawHas2 r) (rUMsb r dTop) (hu.2.2.2.2.1 dTop))
      (.seq (.cnot (rHas1 r) (rUMsb r dSub) (hu.2.2.2.1 dSub)) (.cnot (rUMsb r dTop) (rUMsb r dSub)
      (rUMsb_ne_of_ne r hNeTS)))))); let γ3 := pInitTop.fwdBits γ1
  have g1Pub {u : Fin (routerWidth M D)} (_ : u.val < basePub M D) : γ1 (r u) = γ (r u) :=
    nfOth _ (fun d ↦ rr_ne r (by have := d.isLt; dsimp; omega)) fun d ↦
        rr_ne r (by have := d.isLt; dsimp; omega)
  have g1H1 : γ1 (rHas1 r) = β (rHas1 r) :=
      (g1Pub (by unfold basePub; dsimp; omega)).trans hAg.1
  have g1H2 : γ1 (rRawHas2 r) = β (rRawHas2 r) :=
      (g1Pub (by unfold basePub; dsimp; omega)).trans hAg.2.1
  have g1I1 (d : Fin D) : γ1 (rIdx1 r d) = β (rIdx1 r d) :=
    (g1Pub (by have := d.isLt; unfold basePub; dsimp; omega)).trans (hAg.2.2.1 d)
  have g1I2 (d : Fin D) : γ1 (rIdx2 r d) = β (rIdx2 r d) :=
    (g1Pub (by have := d.isLt; unfold basePub; dsimp; omega)).trans (hAg.2.2.2.1 d)
  have g1U0 (d : Fin D) : γ1 (rUMsb r d) = 0 :=
    (nfOth _ (fun j ↦ rr_ne r (by have := j.isLt; dsimp; omega))
      fun j ↦ rr_ne r (by have := j.isLt; dsimp; omega)).trans (hAg.2.2.2.2.2.2 d).2.2.1
  have g3Oth1 {w : Wire n} (nT : w ≠ rUMsb r dTop) (nS : w ≠ rUMsb r dSub) : γ3 w = γ1 w := by
    simp only [γ3, pInitTop, ComputeProg.fwdBits, Function.update_of_ne nS,
        Function.update_of_ne nT]
  have g3Pub : γ3 (rHas1 r) = β (rHas1 r) ∧ γ3 (rRawHas2 r) = β (rRawHas2 r) ∧
      (∀ d, γ3 (rIdx1 r d) = β (rIdx1 r d)) ∧ (∀ d, γ3 (rIdx2 r d) = β (rIdx2 r d)) :=
    ⟨(g3Oth1 (hu.2.2.2.1 dTop) (hu.2.2.2.1 dSub)).trans g1H1, (g3Oth1 (hu.2.2.2.2.1 dTop)
        (hu.2.2.2.2.1 dSub)).trans g1H2,
     fun d ↦ (g3Oth1 (rr_ne r (by have := d.isLt; unfold basePub; dsimp; omega))
       (rr_ne r (by have := d.isLt; unfold basePub; dsimp; omega))).trans (g1I1 d),
     fun d ↦ (g3Oth1 (rUMsb_ne_rIdx2 r dTop d).symm (rUMsb_ne_rIdx2 r dSub d).symm).trans (g1I2 d)⟩
  have g3NotMin (d : Fin D) : γ3 (rNotMin r d) = β (rHas1 r) + β (rIdx1 r d) :=
    (g3Oth1 (rr_ne r (by have := d.isLt; dsimp; omega))
        (rr_ne r (by have := d.isLt; dsimp; omega))).trans
      ((nfMin d).trans (by rw [ite_eq_left d.isLt, hAg.1, hAg.2.2.1 d]))
  have g3NotMax (d : Fin D) : γ3 (rNotMax r d) = β (rRawHas2 r) + β (rIdx2 r d) :=
    (g3Oth1 (rr_ne r (by have := d.isLt; dsimp; omega))
        (rr_ne r (by have := d.isLt; dsimp; omega))).trans
      ((nfMax d).trans (by rw [ite_eq_left d.isLt, hAg.2.1, hAg.2.2.2.1 d]))
  have g3UTop : γ3 (rUMsb r dTop) = diffBit true r β dTop := by
    dsimp only [γ3, pInitTop, ComputeProg.fwdBits];
    rw [Function.update_of_ne (rUMsb_ne_of_ne r hNeTS),
        Function.update_of_ne (rUMsb_ne_of_ne r hNeTS), Function.update_self,
        Function.update_of_ne (hu.2.2.2.2.1 dTop), Function.update_of_ne (hu.2.2.2.2.1 dTop),
        Function.update_of_ne (hu.2.2.2.2.1 dTop), Function.update_self,
        Function.update_of_ne (hu.2.2.2.1 dTop), Function.update_of_ne (hu.2.2.2.1 dTop),
        Function.update_self, Function.update_of_ne (hu.2.2.2.2.2.2.1 dTop), Function.update_self,
        g1U0 dTop, g1I1 dTop, g1I2 dTop, g1H1, g1H2, zero_add]; rfl
  have g3USub : γ3 (rUMsb r dSub) = β (rHas1 r) + diffBit true r β dTop := by
    have hT := g3UTop
    dsimp only [γ3, pInitTop, ComputeProg.fwdBits] at hT ⊢
    simp only [Function.update_of_ne (rUMsb_ne_of_ne r hNeTS)] at hT
    rw [Function.update_self, Function.update_self, Function.update_of_ne (rUMsb_ne_of_ne r hNeTS),
        hT]
    simp only [Function.update_of_ne (rUMsb_ne_of_ne r hNeTS.symm),
      Function.update_of_ne (hu.2.2.2.1 dTop), g1U0 dSub, g1H1, zero_add]
  have g3ULo (d : Fin D) (hlt : d.val < D - 2) : γ3 (rUMsb r d) = 0 :=
    (g3Oth1 (rUMsb_ne_of_ne r fun e ↦ (fun hv : d.val = D - 1 ↦ by omega) (congrArg Fin.val e))
      (rUMsb_ne_of_ne r fun e ↦ Nat.ne_of_lt hlt (congrArg Fin.val e))).trans (g1U0 d)
  have hδDef : δ = (pUMsbDownLoop true r (D - 2) (hdr_lt2 hD2)).fwdBits γ3 := rfl
  have hDiffγ3 (d : Fin D) : diffBit true r γ3 d = diffBit true r β d :=
    diffBit_congr true r d (g3Pub.2.2.1 d) (g3Pub.2.2.2 d) g3Pub.1 g3Pub.2.1
  have leSub {d : Fin D} (hT : d ≠ dTop) : d.val ≤ D - 2 :=
    (fun _ (_ : d.val ≠ D - 1) ↦ by omega) d.isLt fun e ↦ hT (Fin.ext e)
  have ltSub {d : Fin D} (hT : d ≠ dTop) (hS : d ≠ dSub) : d.val < D - 2 :=
    (fun _ (_ : d.val ≠ D - 2) ↦ by omega) (leSub hT) fun e ↦ hS (Fin.ext e)
  have hActive (ho1 : β (rHas1 r) = 1) (dStar : Fin D) (hd1 : diffBit true r β dStar = 1)
      (hd0 : ∀ d : Fin D, dStar.val < d.val → diffBit true r β d = 0) :
      (∀ w : Wire n, (∀ d : Fin D, w ≠ rUMsb r d) → δ w = γ3 w) ∧
        (∀ d : Fin D, δ (rUMsb r d) = if d = dStar then 1 else 0) := by
    by_cases hEqT : dStar = dTop
    · subst hEqT
      have hZeroLe (d : Fin D) (hd : d.val ≤ D - 2) : γ3 (rUMsb r d) = 0 :=
        if hdS : d = dSub then (congrArg (γ3 <| rUMsb r ·) hdS).trans
          (g3USub.trans ((congrArg₂ (· + ·) ho1 hd1).trans (by decide)))
        else g3ULo d ((fun _ : d.val ≠ D - 2 ↦ by omega) fun e ↦ hdS (Fin.ext e))
      have hEq : δ = γ3 :=
          hδDef.trans (fwdBits_pUMsbDownLoop_zero true r (D - 2) (hdr_lt2 hD2) γ3 hZeroLe)
      refine ⟨fun w _ ↦ congrFun hEq w, fun d ↦ (congrFun hEq (rUMsb r d)).trans ?_⟩
      exact if hdT : d =
          dTop then ((congrArg (γ3 <|
          rUMsb r ·) hdT).trans (g3UTop.trans hd1)).trans (ite_eq_left hdT).symm
        else (hZeroLe d (leSub hdT)).trans (ite_eq_right hdT).symm
    · have hTopDiff0 : diffBit true r β dTop = 0 :=
        hd0 dTop ((fun (_ : dTop.val = D - 1) _ ↦ by omega) rfl (leSub hEqT))
      obtain ⟨hU, hO⟩ := fwdBits_pUMsbDownLoop_one true r (D - 2) (hdr_lt2 hD2) γ3 dStar
        (g3USub.trans ((congrArg₂ (· + ·) ho1 hTopDiff0).trans (add_zero 1))) g3ULo (leSub hEqT)
        ((hDiffγ3 dStar).trans hd1) fun d hlt _ ↦ (hDiffγ3 d).trans (hd0 d hlt)
      refine ⟨fun w nw ↦ (congrFun hδDef w).trans (hO w fun d _ ↦ nw d), fun d ↦ ?_⟩
      by_cases hdT : d = dTop
      · subst hdT
        rw [congrFun hδDef (rUMsb r dTop),
          hO _ fun d' hd' ↦ rUMsb_ne_of_ne r fun e ↦
              (fun hv : D - 1 = d'.val ↦ by omega) (congrArg Fin.val e),
          g3UTop.trans hTopDiff0, ite_eq_right (Ne.symm hEqT)]
      · exact (congrFun hδDef (rUMsb r d)).trans (hU d (leSub hdT))
  suffices hM : (∀ w : Wire n, (∀ d : Fin D, w ≠ rUMsb r d) → δ w = γ3 w) ∧
      (β (rHas1 r) = 0 → ∀ d : Fin D, δ (rUMsb r d) = 0) ∧
      (β (rHas1 r) = 1 → β (rRawHas2 r) = 0 → ∃ dStar : Fin D,
        (idxValD (rIdx1 r) β).testBit dStar.val = false ∧
        ∀ d : Fin D, δ (rUMsb r d) = if d = dStar then 1 else 0) ∧
      (β (rHas1 r) = 1 → β (rRawHas2 r) = 1 → ∃ dStar : Fin D,
        (idxValD (rIdx1 r) β).testBit dStar.val = false ∧
        (idxValD (rIdx2 r) β).testBit dStar.val = true ∧
        ∀ d : Fin D, δ (rUMsb r d) = if d = dStar then 1 else 0) from
    ⟨(hM.1 _ fun d ↦ hu.2.2.2.1 d).trans g3Pub.1, (hM.1 _ fun d ↦ hu.2.2.2.2.1 d).trans g3Pub.2.1,
     fun d ↦ (hM.1 _ fun _ ↦ rr_ne r (by have := d.isLt; dsimp; omega)).trans (g3NotMin d),
     fun d ↦
         (hM.1 _ fun _ ↦ rr_ne r (by have := d.isLt; dsimp; omega)).trans (g3NotMax d), hM.2⟩
  rcases zmod2_cases (β (rHas1 r)) with hz1 | ho1
  · have hz2 : β (rRawHas2 r) = 0 := by
      rcases zmod2_cases (β (rRawHas2 r)) with h | h <;>
          first | exact h | exact absurd (hz1.symm.trans (hβ.1.1 h)) zero_ne_one
    have hTopD0 : diffBit true r β dTop = 0 := by
      dsimp [diffBit]; rw [hβ.2.1 hz1 dTop, hβ.2.2.1 hz2 dTop, hz1, hz2]; decide
    have hAll0 (d : Fin D) : γ3 (rUMsb r d) = 0 :=
      if hdT : d = dTop then (congrArg (γ3 <| rUMsb r ·) hdT).trans (g3UTop.trans hTopD0)
      else if hdS : d = dSub then (congrArg (γ3 <| rUMsb r ·) hdS).trans
        (g3USub.trans ((congrArg₂ (· + ·) hz1 hTopD0).trans (add_zero 0)))
      else g3ULo d (ltSub hdT hdS)
    have hEq : δ = γ3 :=
        hδDef.trans (fwdBits_pUMsbDownLoop_zero true r (D - 2) (hdr_lt2 hD2) γ3 fun d _ ↦ hAll0 d)
    exact ⟨fun w _ ↦ congrFun hEq w, fun _ d ↦ (congrFun hEq (rUMsb r d)).trans (hAll0 d),
      fun h ↦ absurd (hz1.symm.trans h) zero_ne_one, fun h ↦ absurd (hz1.symm.trans h) zero_ne_one⟩
  · rcases zmod2_cases (β (rRawHas2 r)) with hz2 | ho2
    · obtain ⟨dStar, hb1, hd1, hd0⟩ := msb_diff_mode1 hMD r β (hβ.1.2.1 ho1)
      have hDEq (d : Fin D) : diffBit true r β d = β (rIdx1 r d) + 1 := by
        dsimp [diffBit]; rw [hβ.2.2.1 hz2 d, ho1, hz2]; ring
      obtain ⟨hO, hU⟩ := hActive ho1 dStar ((hDEq dStar).trans hd1) fun d hlt ↦
          (hDEq d).trans (hd0 d hlt)
      exact ⟨hO, fun h ↦ absurd (ho1.symm.trans h) one_ne_zero, fun _ _ ↦ ⟨dStar, hb1, hU⟩,
          fun _ h ↦ absurd (hz2.symm.trans h) zero_ne_one⟩
    · obtain ⟨dStar, hb1, hb2, hd1, hd0⟩ := msb_diff_mode2 r β (hβ.2.2.2 ho2)
      have hDEq (d : Fin D) : diffBit true r β d = β (rIdx1 r d) + β (rIdx2 r d) := by
        dsimp [diffBit]; rw [ho1, ho2, add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
      obtain ⟨hO, hU⟩ := hActive ho1 dStar ((hDEq dStar).trans hd1) fun d hlt ↦
          (hDEq d).trans (hd0 d hlt)
      exact ⟨hO, fun h ↦ absurd (ho1.symm.trans h) one_ne_zero, fun _ h ↦
          absurd (ho2.symm.trans h) one_ne_zero, fun _ _ ↦ ⟨dStar, hb1, hb2, hU⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
end

noncomputable section
open Operator QProg Matrix QuantumComputation.Specs.PhotochemistrySolution
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat PhotochemistrySolution.XMeasUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
/-! ## Section 6: Exact `SubspaceStep` Proof for `pDualBellPlaneDyn` & `pDualBellPlanesVecMD` -/
/--
Clean initial condition on buffers, shared Bell partners, and `2 * D + 1` plane scratch wires.
-/
def ValidPlaneClean {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) : Prop :=
  β (pBufLo r) = 0 ∧ β (pBufHi r) = 0 ∧ β (pHA r) = 0 ∧ β (pHB r) = 0 ∧
  (∀ d : Fin D, β (pAMsb r d) = 0) ∧
  (∀ d : Fin D, β (pCReg r d) = 0) ∧
  β (pAnc r) = 0
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k

namespace QuantumComputation.Specs.PhotochemistrySolution.Csa36KickStep
open Circuit Qubit PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.ZeroNEremAxisSq18
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.ZeroNEremCsa36Kick
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
/-- One-hot `6`-bit encoding of distance bin `b ∈ 0..7` on wires `4..9`. -/
def binOneHot6 (b : ℕ) : ℕ := if Nat.beq b 0 then 0 else if Nat.ble b 2 then 1 else 1 <<< (b - 2)
theorem binOneHot6_fin8Bin (s : ℕ) : binOneHot6 (fin8Bin s).val = fin8OneHotNat s := by
  have htbl : ∀ b : Fin 8, binOneHot6 b.val = (if b.val == 0 then 0 else if b.val ≤
      2 then 1 else 1 <<< (b.val - 2)) := by decide +kernel
  exact (htbl (fin8Bin s)).trans (fin8OneHotNat_eq s).symm
/-- Abstract `SubspaceStep`, gate counts, and `DynWires` wrapper over `(cp : ComputeProg Wc)`. -/
theorem bennettXorReg_step_of_spec {Var : Type} [Fintype Var] [DecidableEq Var] {W Wc Wt n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister Wc n) (sMask : ℕ)
    (cp : ComputeProg Wc) (hValid : StructuredCB.validProgMask 0 sMask cp = true)
    (outW : Fin Wt → Wire Wc) (rTgt : QRegister Wt n) (hDisj : r.DisjointWires rTgt)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (val : BitAssignment n → ℕ) (nAnd : ℕ) (hAnd : cp.numAnd = nAnd)
    (hZero : ∀ u : Wire Wc, sMask.testBit u.val = true → ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
    st δ (r u) = 0) (hOut : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → ∀ j : Fin Wt, cp.fwdBits (fun u ↦
    st δ (r u)) (outW j) = if (val δ).testBit j.val then 1 else 0) :
    SubspaceStep (mkKetOpW rWork st ph)
    (mkKetOpW rWork (fun δ ↦ writeReg (st δ) rTgt (fun j ↦ st δ (rTgt j) +
    if (val δ).testBit j.val then 1 else 0)) ph) (bennettXorReg v r cp outW rTgt hDisj) ∧
    (bennettXorReg v r cp outW rTgt hDisj).count .T = 4 * nAnd ∧
    (bennettXorReg v r cp outW rTgt hDisj).count .TOFF = 0 ∧ (∀ S : Wire n → Prop, (∀ u, S (r u)) →
    (∀ j, S (rTgt j)) → DynWires S (bennettXorReg v r cp outW rTgt hDisj)) := by
  obtain ⟨ht, hf⟩ := count_bennettXorReg v r cp outW rTgt hDisj
  have hStep :=
      subspaceStep_bennettXorReg_mkKetOpW v rWork r sMask cp hValid outW rTgt hDisj st ph hZero
  refine ⟨Eq.mp (congrArg (fun Q ↦ SubspaceStep _ Q _) (mkKetOpW_congr rWork (fun δ hz ↦ ?_)
      (fun _ _ ↦ rfl))) hStep,
    ht.trans (by rw [hAnd]), hf, fun S ↦ dynWires_bennettXorReg v r cp outW rTgt hDisj⟩
  exact congrArg (writeReg (st δ) rTgt) (funext fun j ↦ by rw [hOut δ hz j])
end QuantumComputation.Specs.PhotochemistrySolution.Csa36KickStep
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
  QuantumComputation.Specs.PhotochemistrySolution.SelectKinThreshCore QProg Circuit Qubit
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
open Operator DynamicCircuit Matrix PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem stepDadda_tag0 (pool : List DToken) (cm cm' : List ℕ) (c : ℕ)
    (htag0 : c % 4 = 0) (hwf : wfDaddaStep pool cm c = some cm') (γ0 γ : BitAssignment 304)
    (hinv : daddaInv pool cm γ0 γ) :
    daddaInv (stepDadda pool c).1 cm' γ0 ((stepDadda pool c).2.fwdBits γ) := by
  obtain ⟨h49, hown, hcl, hsum⟩ := hinv
  unfold wfDaddaStep at hwf; unfold stepDadda
  simp only [htag0, ↓reduceIte] at hwf ⊢
  set k0 := (c / 4) % 256; set wOut := c / 1024; let sp0 := splitTok k0 pool
  split_ifs at hwf with hcond
  injection hwf with hcm'; subst hcm'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond;
  obtain ⟨⟨⟨⟨hk0, hwOut_own⟩, hwOut_cm⟩, ht0_av⟩, hp1_av⟩ := hcond; obtain ⟨hwOut_lt, hwOut_ne49⟩ :=
      owned_facts wOut hwOut_own
  have hγ' : (xorTokCP wOut sp0.1).fwdBits γ = Function.update γ (w304 wOut)
      (γ (w304 wOut) + tokBit sp0.1 γ) :=
    xorTokCP_fwd wOut hwOut_lt sp0.1 (tokAvoid_imp [wOut] wOut (by simp [inNatList]) sp0.1 ht0_av) γ
  rw [hγ']; let γ' := Function.update γ (w304 wOut) (γ (w304 wOut) + tokBit sp0.1 γ)
  have hforb : ∀ u : Wire 304, inNatList u.val [wOut] = false -> γ' u = γ u :=
    upd_outside_forb [wOut] wOut hwOut_lt (by simp [inNatList]) γ γ _ (fun _ _ => rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (w304_ne_of_ne (by omega) hwOut_lt hwOut_ne49.symm)]; exact h49
  · intro u hu hu49
    have hne : u ≠ w304 wOut := fun e => by
      subst e; simp only [w304, finMod, Nat.mod_eq_of_lt hwOut_lt, hwOut_own] at hu;
      exact Bool.noConfusion hu
    rw [Function.update_of_ne hne]; exact hown u hu hu49
  · intro a ha; obtain ⟨hacm, hne⟩ := inNatList_filter cm a wOut ha
    obtain ⟨halt, ha0⟩ := hcl a hacm
    exact ⟨halt, by rw [Function.update_of_ne (w304_ne_of_ne halt hwOut_lt hne)]; exact ha0⟩
  · rw [poolSum_append, poolSum_congr [wOut] sp0.2 hp1_av γ γ' hforb]
    have hsingle : poolSum [(sp0.1.1, [wOut], false)] γ' = (tokBit sp0.1 γ).val * 2 ^ sp0.1.1 := by
      simp only [poolSum, List.foldr, tokBit, Bool.false_eq_true, ↓reduceIte, zero_add, add_zero,
          γ', Function.update_self, (hcl wOut hwOut_cm).2]
    have hsp := (splitTok_sum pool k0 hk0 γ).1
    have heq : poolSum sp0.2 γ + poolSum [(sp0.1.1, [wOut], false)] γ' = poolSum pool γ := by
      dsimp only [sp0] at hsingle hsp ⊢; rw [hsingle, hsp]; ring
    dsimp only [sp0] at heq ⊢; rw [heq, hsum]
theorem stepDadda_tag1 (pool : List DToken) (cm cm' : List ℕ) (c : ℕ)
    (htag0 : ¬ c % 4 = 0) (htag1 : c % 4 = 1) (hwf : wfDaddaStep pool cm c = some cm')
    (γ0 γ : BitAssignment 304) (hinv : daddaInv pool cm γ0 γ) :
    daddaInv (stepDadda pool c).1 cm' γ0 ((stepDadda pool c).2.fwdBits γ) := by
  obtain ⟨h49, hown, hcl, hsum⟩ := hinv
  unfold wfDaddaStep at hwf; unfold stepDadda
  simp only [htag0, ↓reduceIte] at hwf ⊢; simp only [htag1, ↓reduceIte] at hwf ⊢
  set k0 := (c / 4) % 256; set k1 := (c / 1024) % 256; set k2 := (c / 262144) % 256; set wC :=
      c / 67108864
  let s0 := splitTok k0 pool; let s1 := splitTok k1 s0.2; let s2 := splitTok k2 s1.2
  let wS := s0.1.2.1.headD 0
  split_ifs at hwf with hcond
  injection hwf with hcm'; subst hcm'
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true',
      decide_eq_true_eq] at hcond; obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk0, hk1⟩, hk2⟩, ht0_ws⟩, ht0_inv⟩, ht1_b⟩,
      ht2_b⟩, hwS_own⟩, hwC_own⟩, hne_sc⟩, hwS_notcm⟩, hwC_cm⟩, ht1_av⟩, ht2_av⟩, hp3_av⟩ :=
      hcond; obtain ⟨hwS_lt, hwS_ne49⟩ := owned_facts wS hwS_own; obtain ⟨hwC_lt, hwC_ne49⟩ :=
      owned_facts wC hwC_own; let F := [wS, wC, 49]
  obtain ⟨inS, inC, in49⟩ :
      inNatList wS F = true ∧ inNatList wC F = true ∧ inNatList 49 F = true := by
    simp [F, inNatList]
  set x := γ (w304 wS); set y := tokBit s1.1 γ; set z := tokBit s2.1 γ
  have stepX {w : ℕ} (hw : w < 304) (hin : inNatList w F = true) {t : DToken}
      (ht : tokAvoid F t = true) {δ : BitAssignment 304}
      (hf : ∀ u : Wire 304, inNatList u.val F = false → δ u = γ u) :
      (xorTokCP w t).fwdBits δ = Function.update δ (w304 w) (δ (w304 w) + tokBit t γ) ∧
        ∀ u : Wire 304, inNatList u.val F = false → (xorTokCP w t).fwdBits δ u = γ u := by
    have he : (xorTokCP w t).fwdBits δ = Function.update δ (w304 w) (δ (w304 w) + tokBit t γ) := by
      rw [xorTokCP_fwd w hw t (tokAvoid_imp F w hin t ht) δ, tokBit_congr F t ht γ δ hf]
    exact ⟨he, he ▸ upd_outside_forb F w hw hin γ δ _ hf⟩
  obtain ⟨e1, f1⟩ := stepX hwS_lt inS ht2_av (fun _ _ => rfl)
  obtain ⟨e2, f2⟩ := stepX (by omega) in49 ht1_av f1
  let δ3 := (xorTokCP 49 s2.1).fwdBits ((xorTokCP 49 s1.1).fwdBits ((xorTokCP wS s2.1).fwdBits γ))
  obtain ⟨e3, f3⟩ : δ3 = _ ∧ _ := stepX (by omega) in49 ht2_av f2
  have nSC := w304_ne_of_ne hwS_lt hwC_lt hne_sc
  have e4 : (safeAndGateCP (w304 wS) (w304 49) (w304 wC)).fwdBits δ3 =
      Function.update δ3 (w304 wC) (δ3 (w304 wC) + δ3 (w304 wS) * δ3 (w304 49)) :=
    fwdBits_safeAnd (w304_ne_of_ne hwS_lt (by omega) hwS_ne49) nSC
      (w304_ne_of_ne (by omega) hwC_lt hwC_ne49.symm) δ3
  obtain ⟨e5, f5⟩ := stepX (by omega) in49 ht2_av (e4 ▸ upd_outside_forb F wC hwC_lt inC γ δ3 _ f3)
  obtain ⟨e6, f6⟩ := stepX (by omega) in49 ht1_av f5
  obtain ⟨e7, f7⟩ := stepX hwC_lt inC ht2_av f6
  let δ8 := (xorTokCP wS s1.1).fwdBits ((xorTokCP wC s2.1).fwdBits
    ((xorTokCP 49 s1.1).fwdBits ((xorTokCP 49 s2.1).fwdBits
      ((safeAndGateCP (w304 wS) (w304 49) (w304 wC)).fwdBits δ3))))
  obtain ⟨e8, f8⟩ : δ8 = _ ∧ ∀ u : Wire 304, inNatList u.val F = false → δ8 u = γ u :=
    stepX hwS_lt inS ht1_av f7
  change daddaInv _ _ γ0 δ8
  have nK4 := w304_ne_of_ne hwS_lt (by omega) hwS_ne49
  have nC4 := w304_ne_of_ne hwC_lt (by omega) hwC_ne49
  have halg := zmod2_fa_alg x y z
  have d3_49 : δ3 (w304 49) = 0 + y + z := by
    rw [e3, Function.update_self, e2, Function.update_self, e1, Function.update_of_ne nK4.symm, h49]
  have d3_S : δ3 (w304 wS) = x + z := by
    rw [e3, Function.update_of_ne nK4, e2, Function.update_of_ne nK4, e1, Function.update_self]
  have d3_C : δ3 (w304 wC) = 0 := by
    rw [e3, Function.update_of_ne nC4, e2, Function.update_of_ne nC4, e1,
        Function.update_of_ne nSC.symm]; exact (hcl wC hwC_cm).2
  have v49 : δ8 (w304 49) = 0 := by
    rw [e8, Function.update_of_ne nK4.symm, e7, Function.update_of_ne nC4.symm, e6,
        Function.update_self, e5, Function.update_self, e4, Function.update_of_ne nC4.symm,
        d3_49]; exact halg.1
  have vS : δ8 (w304 wS) = x + y + z := by
    rw [e8, Function.update_self, e7, Function.update_of_ne nSC, e6, Function.update_of_ne nK4, e5,
        Function.update_of_ne nK4, e4, Function.update_of_ne nSC, d3_S]; exact halg.2.1
  have vC : δ8 (w304 wC) = (x + z) * (y + z) + z := by
    rw [e8, Function.update_of_ne nSC.symm, e7, Function.update_self, e6, Function.update_of_ne nC4,
        e5, Function.update_of_ne nC4, e4, Function.update_self, d3_C, d3_S,
        d3_49]; exact halg.2.2.1
  refine ⟨v49, fun u hu hu49 =>
      (f8 u (nonown_notIn3 wS wC hwS_own hwC_own u hu hu49)).trans (hown u hu hu49),
      clean_step3 cm wS wC hwS_notcm γ δ8 v49 hcl f8, ?_⟩
  rw [poolSum_append, poolSum_congr F s2.2 hp3_av γ δ8 f8]
  have hp : poolSum [(s0.1.1, [wS], false), (s0.1.1 + 1, [wC], false)] δ8 = x.val * 2 ^ s0.1.1 +
      y.val * 2 ^ s1.1.1 + z.val * 2 ^ s2.1.1 := by
    simp only [poolSum, List.foldr, tokBit, Bool.false_eq_true, ↓reduceIte, zero_add, add_zero, vS,
        vC, Nat.pow_succ]
    calc (x + y + z).val * 2 ^ s0.1.1 + ((x + z) * (y + z) + z).val * (2 ^ s0.1.1 * 2)
        = ((x + y + z).val + 2 * ((x + z) * (y + z) + z).val) * 2 ^ s0.1.1 := by ring
      _ = (x.val + y.val + z.val) * 2 ^ s0.1.1 := by rw [← halg.2.2.2]
      _ = x.val * 2 ^ s0.1.1 + y.val * 2 ^ s1.1.1 + z.val * 2 ^ s2.1.1 := by
        dsimp only [s0, s1, s2]; rw [ht1_b, ht2_b]; ring
  have hs0 := (splitTok_sum pool k0 hk0 γ).1; have hs1 := (splitTok_sum s0.2 k1 hk1 γ).1;
  have hs2 := (splitTok_sum s1.2 k2 hk2 γ).1; rw [tokBit_single s0.1 wS ht0_ws ht0_inv γ] at hs0
  have heq : poolSum s2.2 γ + poolSum [(s0.1.1, [wS], false), (s0.1.1 + 1, [wC], false)] δ8 =
      poolSum pool γ := by
    dsimp only [s0, s1, s2, wS, x, y, z] at hp hs0 hs1 hs2 ⊢; rw [hp, hs0, hs1, hs2]; ring
  dsimp only [s0, s1, s2, wS] at heq ⊢; rw [heq, hsum]
theorem stepDadda_tag2 (pool : List DToken) (cm cm' : List ℕ) (c : ℕ)
    (htag0 : ¬ c % 4 = 0) (htag1 : ¬ c % 4 = 1) (htag2 : c % 4 = 2)
    (hwf : wfDaddaStep pool cm c = some cm') (γ0 γ : BitAssignment 304)
    (hinv : daddaInv pool cm γ0 γ) :
    daddaInv (stepDadda pool c).1 cm' γ0 ((stepDadda pool c).2.fwdBits γ) := by
  obtain ⟨h49, hown, hcl, hsum⟩ := hinv
  unfold wfDaddaStep at hwf; unfold stepDadda
  simp only [htag0, ↓reduceIte] at hwf ⊢; simp only [htag1, ↓reduceIte] at hwf ⊢;
  simp only [htag2, ↓reduceIte] at hwf ⊢
  set k0 := (c / 4) % 256; set k1 := (c / 1024) % 256; set wC := c / 262144
  let s0 := splitTok k0 pool; let s1 := splitTok k1 s0.2
  let wS := s0.1.2.1.headD 0
  split_ifs at hwf with hcond
  injection hwf with hcm'; subst hcm'
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true',
      decide_eq_true_eq] at hcond; obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk0, hk1⟩, ht0_ws⟩, ht0_inv⟩, ht1_b⟩, hwS_own⟩,
      hwC_own⟩, hne_sc⟩, hwS_notcm⟩, hwC_cm⟩, ht1_av⟩, hp2_av⟩ :=
      hcond; obtain ⟨hwS_lt, hwS_ne49⟩ := owned_facts wS hwS_own; obtain ⟨hwC_lt, hwC_ne49⟩ :=
      owned_facts wC hwC_own; let F := [wS, wC, 49]
  obtain ⟨inS, inC, in49⟩ :
      inNatList wS F = true ∧ inNatList wC F = true ∧ inNatList 49 F = true := by
    simp [F, inNatList]
  set x := γ (w304 wS); set y := tokBit s1.1 γ
  let δ1 := (xorTokCP 49 s1.1).fwdBits γ
  have e1 : δ1 = Function.update γ (w304 49) (γ (w304 49) + y) :=
      xorTokCP_fwd 49 (by omega) s1.1 (tokAvoid_imp F 49 in49 s1.1 ht1_av) γ
  have f1 := e1 ▸ upd_outside_forb F 49 (by omega) in49 γ γ _ (fun _ _ => rfl)
  let δ2 := (safeAndGateCP (w304 wS) (w304 49) (w304 wC)).fwdBits δ1
  have e2 : δ2 = Function.update δ1 (w304 wC) (δ1 (w304 wC) + δ1 (w304 wS) * δ1 (w304 49)) :=
    fwdBits_safeAnd (w304_ne_of_ne hwS_lt (by omega) hwS_ne49)
      (w304_ne_of_ne hwS_lt hwC_lt hne_sc) (w304_ne_of_ne (by omega) hwC_lt hwC_ne49.symm) δ1
  have f2 := e2 ▸ upd_outside_forb F wC hwC_lt inC γ δ1 _ f1;
  have nSC := w304_ne_of_ne hwS_lt hwC_lt hne_sc
  have nK4 := w304_ne_of_ne hwS_lt (by omega) hwS_ne49
  have nC4 := w304_ne_of_ne hwC_lt (by omega) hwC_ne49
  let δ3 := (safeCnotCP (w304 49) (w304 wS)).fwdBits δ2
  have e3 : δ3 = Function.update δ2 (w304 wS) (δ2 (w304 wS) + δ2 (w304 49)) := by
    dsimp only [δ3, safeCnotCP]; simp only [nK4.symm, ↓reduceDIte, ComputeProg.fwdBits]
  have f3 := e3 ▸ upd_outside_forb F wS hwS_lt inS γ δ2 _ f2;
  let δ4 := (xorTokCP 49 s1.1).fwdBits δ3
  have e4 : δ4 = Function.update δ3 (w304 49) (δ3 (w304 49) + y) := by
    dsimp only [δ4];
    rw [xorTokCP_fwd 49 (by omega) s1.1 (tokAvoid_imp F 49 in49 s1.1 ht1_av) δ3,
        tokBit_congr F s1.1 ht1_av γ δ3 f3]
  have f4 := e4 ▸ upd_outside_forb F 49 (by omega) in49 γ δ3 _ f3
  change daddaInv _ _ γ0 δ4; have halg := zmod2_ha_alg x y
  have d1_49 : δ1 (w304 49) = 0 + y := by rw [e1, Function.update_self, h49]
  have d1_S : δ1 (w304 wS) = x := by rw [e1, Function.update_of_ne nK4]
  have v49 : δ4 (w304 49) = 0 := by
    rw [e4, Function.update_self, e3, Function.update_of_ne nK4.symm, e2,
        Function.update_of_ne nC4.symm, d1_49]; exact halg.1
  have vC : δ4 (w304 wC) = x * y := by
    rw [e4, Function.update_of_ne nC4, e3, Function.update_of_ne nSC.symm, e2,
      Function.update_self, d1_S, d1_49, e1, Function.update_of_ne nC4, (hcl wC hwC_cm).2]
    exact halg.2.1
  have vS : δ4 (w304 wS) = x + y := by
    rw [e4, Function.update_of_ne nK4, e3, Function.update_self, e2, Function.update_of_ne nSC,
      Function.update_of_ne nC4.symm, d1_S, d1_49]
    exact halg.2.2.1
  refine ⟨v49, fun u hu hu49 =>
      (f4 u (nonown_notIn3 wS wC hwS_own hwC_own u hu hu49)).trans (hown u hu hu49),
      clean_step3 cm wS wC hwS_notcm γ δ4 v49 hcl f4, ?_⟩
  rw [poolSum_append, poolSum_congr F s1.2 hp2_av γ δ4 f4]
  have hp : poolSum [(s0.1.1, [wS], false), (s0.1.1 + 1, [wC], false)] δ4 = x.val * 2 ^ s0.1.1 +
      y.val * 2 ^ s1.1.1 := by
    simp only [poolSum, List.foldr, tokBit, Bool.false_eq_true, ↓reduceIte, zero_add, add_zero, vS,
        vC, Nat.pow_succ]
    calc (x + y).val * 2 ^ s0.1.1 + (x * y).val * (2 ^ s0.1.1 * 2)
        = ((x + y).val + 2 * (x * y).val) * 2 ^ s0.1.1 := by ring
      _ = (x.val + y.val) * 2 ^ s0.1.1 := by rw [← halg.2.2.2]
      _ = x.val * 2 ^ s0.1.1 + y.val * 2 ^ s1.1.1 := by dsimp only [s0, s1]; rw [ht1_b]; ring
  have hs0 := (splitTok_sum pool k0 hk0 γ).1;
  have hs1 := (splitTok_sum s0.2 k1 hk1 γ).1; rw [tokBit_single s0.1 wS ht0_ws ht0_inv γ] at hs0
  have heq : poolSum s1.2 γ + poolSum [(s0.1.1, [wS], false), (s0.1.1 + 1, [wC], false)] δ4 =
      poolSum pool γ := by dsimp only [s0, s1, wS, x, y] at hp hs0 hs1 ⊢; rw [hp, hs0, hs1]; ring
  dsimp only [s0, s1, wS] at heq ⊢; rw [heq, hsum]
theorem stepDadda_tag3 (pool : List DToken) (cm cm' : List ℕ) (c : ℕ)
    (htag0 : ¬ c % 4 = 0) (htag1 : ¬ c % 4 = 1) (htag2 : ¬ c % 4 = 2)
    (hwf : wfDaddaStep pool cm c = some cm') (γ0 γ : BitAssignment 304)
    (hinv : daddaInv pool cm γ0 γ) :
    daddaInv (stepDadda pool c).1 cm' γ0 ((stepDadda pool c).2.fwdBits γ) := by
  obtain ⟨h49, hown, hcl, hsum⟩ := hinv
  unfold wfDaddaStep at hwf; unfold stepDadda
  simp only [htag0, ↓reduceIte] at hwf ⊢; simp only [htag1, ↓reduceIte] at hwf ⊢;
  simp only [htag2, ↓reduceIte] at hwf ⊢
  set k0 := (c / 4) % 256; set k1 := (c / 1024) % 256
  let s0 := splitTok k0 pool; let s1 := splitTok k1 s0.2
  let wS := s0.1.2.1.headD 0
  split_ifs at hwf with hcond
  injection hwf with hcm'; subst hcm'
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hcond;
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hk0, hk1⟩, ht0_17⟩, ht0_ws⟩, ht0_inv⟩, ht1_17⟩, hwS_own⟩, hwS_notcm⟩, ht1_av⟩,
      hp2_av⟩ := hcond; obtain ⟨hwS_lt, hwS_ne49⟩ := owned_facts wS hwS_own; let F := [wS, 49]
  have inS : inNatList wS F = true := by simp [F, inNatList]
  set x := γ (w304 wS); set y := tokBit s1.1 γ
  have e1 : (xorTokCP wS s1.1).fwdBits γ = Function.update γ (w304 wS) (x + y) :=
      xorTokCP_fwd wS hwS_lt s1.1 (tokAvoid_imp F wS inS s1.1 ht1_av) γ
  rw [e1]; let δ1 := Function.update γ (w304 wS) (x + y)
  have f1 := upd_outside_forb F wS hwS_lt inS γ γ (x + y) (fun _ _ => rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (w304_ne_of_ne (by omega) hwS_lt hwS_ne49.symm)]; exact h49
  · intro u hu hu49
    have hne : u ≠ w304 wS := fun e => by
      subst e; simp only [w304, finMod, Nat.mod_eq_of_lt hwS_lt] at hu; dsimp only [s0, wS] at hu;
      rw [hwS_own] at hu; exact Bool.noConfusion hu
    rw [Function.update_of_ne hne]; exact hown u hu hu49
  · intro a ha; obtain ⟨halt, ha0⟩ := hcl a ha
    have hneS : a ≠ wS := fun e => by
      subst e; dsimp only [s0, wS] at ha; rw [ha] at hwS_notcm; exact Bool.noConfusion hwS_notcm
    exact ⟨halt, by rw [Function.update_of_ne (w304_ne_of_ne halt hwS_lt hneS)]; exact ha0⟩
  · rw [poolSum_append, poolSum_congr F s1.2 hp2_av γ δ1 f1]
    have hp : poolSum [(17, [wS], false)] δ1 = (x + y).val * 2 ^ 17 := by
      simp only [poolSum, List.foldr, tokBit, Bool.false_eq_true, ↓reduceIte, zero_add, add_zero,
          δ1, Function.update_self]
    have hm17 := zmod2_x17_mod x y; have hs0 := (splitTok_sum pool k0 hk0 γ).1;
    have hs1 :=
        (splitTok_sum s0.2 k1 hk1 γ).1; rw [tokBit_single s0.1 wS ht0_ws ht0_inv γ,
        ht0_17] at hs0; rw [ht1_17] at hs1
    have hpool : poolSum pool γ = poolSum s1.2 γ + (x.val * 2 ^ 17 + y.val * 2 ^ 17) := by
      dsimp only [s0, s1] at hs0 hs1 ⊢; rw [hs0, hs1]; ring
    dsimp only [s0, s1, wS, x, y] at hp hm17 hpool ⊢;
    rw [hp, Nat.add_mod, hm17, ← Nat.add_mod, ← hpool, hsum]
theorem stepDadda_inv (pool : List DToken) (cm cm' : List ℕ) (c : ℕ)
    (hwf : wfDaddaStep pool cm c = some cm') (γ0 γ : BitAssignment 304)
    (hinv : daddaInv pool cm γ0 γ) :
    daddaInv (stepDadda pool c).1 cm' γ0 ((stepDadda pool c).2.fwdBits γ) := by
  exact if h0 : c % 4 = 0 then stepDadda_tag0 pool cm cm' c h0 hwf γ0 γ hinv
    else if h1 : c % 4 = 1 then stepDadda_tag1 pool cm cm' c h0 h1 hwf γ0 γ hinv
    else if h2 : c % 4 = 2 then stepDadda_tag2 pool cm cm' c h0 h1 h2 hwf γ0 γ hinv
    else stepDadda_tag3 pool cm cm' c h0 h1 h2 hwf γ0 γ hinv
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
  writeReg writeReg_apply_of_not_mem writeReg_apply_reg
-- Polymorphic QROM load package (Low-Kliuchnikov-Schaeffer 2024; Gidney 2018).
theorem idxWire_lt {dIdx B kScr i : ℕ} (hi : i < dIdx) : i < dIdx + B + kScr := by omega
theorem outWire_lt {dIdx B kScr j : ℕ} (hj : j < B) : dIdx + j < dIdx + B + kScr := by omega
theorem outScrWire_lt {dIdx B kScr u : ℕ} (hu : u < B + kScr) :
    dIdx + u < dIdx + B + kScr := by omega
/-- Polymorphic `dIdx`-bit-indexed, `B`-bit-word QROM loader package (`dIdx + B + kScr` wires). -/
structure QromLoadPkgGenN (dIdx B : ℕ) (wordB : ℕ → ℕ) : Type 1 where
  kScr : ℕ
  tLoad : ℕ
  pLoad : {Var : Type} → {n : ℕ} → Var → QRegister (dIdx + B + kScr) n → DynamicCircuit Var n
  step_and_counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (r : QRegister (dIdx + B + kScr) n)
    (st stWB : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ (u : Fin (B + kScr)) (δ : BitAssignment n),
      (∀ w : Fin W, δ (rWork w) = 0) → st δ (r ⟨dIdx + u.val, outScrWire_lt u.isLt⟩) = 0) →
    (∀ (j : Fin B) (δ : BitAssignment n),
      stWB δ (r ⟨dIdx + j.val, outWire_lt j.isLt⟩) =
        if (wordB (natOfZModBits dIdx (fun i ↦ st δ (r ⟨i.val, idxWire_lt i.isLt⟩)))).testBit
            j.val = true
        then 1 else 0) →
    (∀ (w : Wire n) (δ : BitAssignment n),
      (¬∃ j : Fin B, w = r ⟨dIdx + j.val, outWire_lt j.isLt⟩) → stWB δ w = st δ w) →
    SubspaceStep (mkKetOpW rWork st ph) (mkKetOpW rWork stWB ph) (pLoad v r) ∧
    (pLoad v r).count .T = tLoad ∧
    (pLoad v r).count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} (S : Wire n → Prop) (v : Var)
    (r : QRegister (dIdx + B + kScr) n),
    (∀ i : Fin (dIdx + B + kScr), S (r i)) → DynWires S (pLoad v r)
/-- Polymorphic `dIdx`-bit-indexed, `B`-bit-word QROM unloader package (`dIdx + B + kUnload`). -/
structure QromUnloadPkgGenN (dIdx B : ℕ) (wordB : ℕ → ℕ) : Type 1 where
  kUnload : ℕ
  tUnload : ℕ
  pUnload : {Var : Type} → {n : ℕ} → Var → QRegister (dIdx + B + kUnload) n → DynamicCircuit Var n
  step_and_counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (r : QRegister (dIdx + B + kUnload) n)
    (st stWB : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ (u : Fin (B + kUnload)) (δ : BitAssignment n),
      (∀ w : Fin W, δ (rWork w) = 0) → st δ (r ⟨dIdx + u.val, outScrWire_lt u.isLt⟩) = 0) →
    (∀ (j : Fin B) (δ : BitAssignment n),
      stWB δ (r ⟨dIdx + j.val, outWire_lt j.isLt⟩) =
        if (wordB (natOfZModBits dIdx (fun i ↦ st δ (r ⟨i.val, idxWire_lt i.isLt⟩)))).testBit
            j.val = true
        then 1 else 0) →
    (∀ (w : Wire n) (δ : BitAssignment n),
      (¬∃ j : Fin B, w = r ⟨dIdx + j.val, outWire_lt j.isLt⟩) → stWB δ w = st δ w) →
    SubspaceStep (mkKetOpW rWork stWB ph) (mkKetOpW rWork st ph) (pUnload v r) ∧
    (pUnload v r).count .T = tUnload ∧
    (pUnload v r).count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} (S : Wire n → Prop) (v : Var)
    (r : QRegister (dIdx + B + kUnload) n),
    (∀ i : Fin (dIdx + B + kUnload), S (r i)) → DynWires S (pUnload v r)
end QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65

namespace QuantumComputation.Specs.PhotochemistrySolution.CoulombFast
open Operator Matrix PhotochemistrySolution.ZeroNEremAxisSq18
  PhotochemistrySolution.ZeroNEremCsa36Kick PhotochemistrySolution.BandEnc12Sync
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65 (QromUnloadPkgGenN
    idxWire_lt outWire_lt outScrWire_lt)
/-- Empty `0`-wire work register (`0` imports, `0` typeclasses). -/
def rWork0 (n : ℕ) : QRegister 0 n := ⟨⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.CoulombFast

namespace QuantumComputation.Specs.PhotochemistrySolution.OddDivEval
open Operator Matrix PhotochemistrySolution.Poly28Sub254
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg_apply_reg)
theorem natOfZModBits_congr_len {m n : ℕ} (h : m = n) (f : Fin m → ZMod 2) :
    natOfZModBits m f = natOfZModBits n (fun i ↦ f ⟨i.val, h ▸ i.isLt⟩) := h ▸ rfl
/-- Split an `(a + b)`-bit `natOfZModBits` sum into low `a` bits and shifted high `b` bits. -/
theorem natOfZModBits_split : ∀ (a b : ℕ) (f : Fin (a + b) → ZMod 2),
    natOfZModBits (a + b) f =
      natOfZModBits a (fun i ↦ f ⟨i.val, Nat.lt_add_right b i.isLt⟩) +
        2 ^ a * natOfZModBits b (fun j ↦ f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩)
  | 0, b, f => by
      rw [← finBitsVal_eq_natOfZModBits 0, show natOfZModBits (0 + b) f =
        natOfZModBits b (fun j ↦ f ⟨0 + j.val, Nat.add_lt_add_left j.isLt 0⟩) from
        (natOfZModBits_congr_len (Nat.zero_add b) f).trans (congrArg (natOfZModBits b)
          (funext fun j ↦ congrArg f (Fin.ext (Nat.zero_add j.val).symm)))]
      simp [finBitsVal]
  | a + 1, b, f => by
      have hab : a + 1 + b = (a + b) + 1 := by omega
      rw [natOfZModBits_congr_len hab f, ← finBitsVal_eq_natOfZModBits ((a + b) + 1),
        finBitsVal_succ, finBitsVal_eq_natOfZModBits, ← finBitsVal_eq_natOfZModBits (a + 1),
        finBitsVal_succ, finBitsVal_eq_natOfZModBits, natOfZModBits_split a b, pow_succ]
      exact (fun c g h1 h2 (e : h1 = h2) ↦ by subst e; ring :
        ∀ c g h1 h2 : ℕ, h1 = h2 → c + 2 * (g + 2 ^ a * h1) = c + 2 * g + 2 ^ a * 2 * h2) _ _ _ _
        (congrArg (natOfZModBits b) (funext fun j ↦ congrArg f (Fin.ext (by dsimp; omega))))
end QuantumComputation.Specs.PhotochemistrySolution.OddDivEval

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
open Operator DynamicCircuit Matrix PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem zmod2_add_cancel (x c : ZMod 2) : x + c + c = x := by
  fin_cases x <;> fin_cases c <;> rfl
theorem zmod2_col0_val (a b c : ZMod 2) : ((0 : ZMod 2) + 1 + a + b + c).val + 2 * ((0 : ZMod 2) +
    (a + c) * (b + c) + 1 + c).val = (1 + (a + 0)).val * 1 + ((1 + (b + 0)).val * 1 +
    ((1 + (c + 0)).val * 1 + 0)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
end

noncomputable section
-- Binary bit-packing lemmas for Reed-Muller QROM loaders.
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65
theorem natOfBoolBits_lt : ∀ (d : ℕ) (f : Fin d → Bool), natOfBoolBits d f < 2 ^ d
  | 0, _ => by simp [natOfBoolBits]
  | d + 1, f => by
      have ih := natOfBoolBits_lt d (fun i ↦ f ⟨i.val, by omega⟩)
      dsimp only [natOfBoolBits]; rw [Nat.pow_succ']
      split_ifs <;> omega
theorem natOfBoolBits_testBit : ∀ (d : ℕ) (f : Fin d → Bool) (i : Fin d),
    (natOfBoolBits d f).testBit i.val = f i
  | 0, _, i => Fin.elim0 i
  | d + 1, f, i => by
      dsimp only [natOfBoolBits]
      set lo := natOfBoolBits d fun k ↦ f ⟨k.val, by omega⟩
      have hLo : lo < 2 ^ d := natOfBoolBits_lt d _
      if hi : i.val < d then
        have hB :=
            Nat.testBit_mod_two_pow (lo + if f ⟨d, Nat.lt_succ_self d⟩ =
            true then 2 ^ d else 0) d i.val
        rw [show (lo + if f ⟨d, Nat.lt_succ_self d⟩ = true then 2 ^ d else 0) % 2 ^ d = lo by
          split_ifs <;> simp [Nat.mod_eq_of_lt hLo], decide_eq_true hi, Bool.true_and] at hB
        exact hB.symm.trans (natOfBoolBits_testBit d _ ⟨i.val, hi⟩)
      else
        obtain rfl : i = ⟨d, Nat.lt_succ_self d⟩ := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt hi)
        rw [Nat.testBit_eq_decide_div_mod_eq]
        cases f ⟨d, Nat.lt_succ_self d⟩ <;> simp [Nat.div_eq_of_lt hLo]
end QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65
namespace QuantumComputation.Specs.PhotochemistrySolution.PrimGateEval
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18
    (PrimTree decodePrimTree evalPrimTree fwdBits_decodePrimTree_testBit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65 (natOfBoolBits_lt
    natOfBoolBits_testBit)
theorem zmod2_eq_ite_of_beq_one (z : ZMod 2) (b : Bool) (h : (z == 1) = b) : z =
    if b then 1 else 0 := by
  fin_cases z <;> cases b <;> cases h <;> rfl
theorem natOfZModBits_lt (k : ℕ) (β : Fin k → ZMod 2) : natOfZModBits k β < 2 ^ k :=
    natOfBoolBits_lt k _
theorem natOfZModBits_testBit_lt {k : ℕ} (β : Fin k → ZMod 2) {u : ℕ}
    (hu : u < k) : (natOfZModBits k β).testBit u = (β ⟨u, hu⟩ == 1) :=
    natOfBoolBits_testBit k _ ⟨u, hu⟩
theorem fwdBits_decodePrimTree_eq_ite {M : ℕ} (t : PrimTree) (α : Fin (M + 1) → ZMod 2)
    (u : Fin (M + 1)) :
    (decodePrimTree M t).fwdBits α u =
        if (evalPrimTree M (natOfZModBits (M + 1) α) t).testBit u.val then 1 else 0 :=
  zmod2_eq_ite_of_beq_one _ _ (fwdBits_decodePrimTree_testBit t _ _ (fun i ↦
      (natOfBoolBits_testBit (M + 1) (fun j ↦ α j == 1) i).symm) u)
end QuantumComputation.Specs.PhotochemistrySolution.PrimGateEval
namespace QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync
open QProg Qubit PhotochemistrySolution.ZeroNEremCsa36Kick PhotochemistrySolution.ZeroNEremAxisSq18
export _root_.QuantumComputation.Specs.PhotochemistrySolution.PrimGateEval (zmod2_eq_ite_of_beq_one
    natOfZModBits_lt natOfZModBits_testBit_lt)
theorem mod_two_mul_add (M x r : ℕ) (hr : r < 2) : (r + 2 * x) % (2 * M) = r + 2 * (x % M) := by
  have h1 := Nat.div_add_mod (r + 2 * x) (2 * M)
  have h2 := Nat.div_add_mod x M
  rw [← Nat.div_div_eq_div_mul, show (r + 2 * x) / 2 = x by omega, mul_assoc] at h1
  omega
/-- Unsigned integer decoded at lane `q` from little-endian column list `cs`. -/
def vecVal : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, q => (if c.testBit q then 1 else 0) + 2 * vecVal cs q
theorem vecVal_testBit :
    ∀ (cs : List ℕ) (q i : ℕ), (vecVal cs q).testBit i = (cs.getD i 0).testBit q
  | [], _, _ => by simp [vecVal]
  | c :: cs, q, 0 => by by_cases h : c.testBit q <;> simp [vecVal, h, Nat.testBit_zero]
  | c :: cs, q, i + 1 => by
      rw [vecVal, List.getD_cons_succ, Nat.testBit_succ]
      cases c.testBit q <;>
        simp [show (1 + 2 * vecVal cs q) / 2 = vecVal cs q by omega, vecVal_testBit cs q i]
theorem vecVal_coord : ∀ (d q : ℕ), q < 2 ^ d → vecVal (coordState d).2.2 q = q := by
  intro d q hq;
  obtain ⟨_, _, hlen, _, htb⟩ :=
      coordState_spec d; apply Nat.eq_of_testBit_eq; intro i; rw [vecVal_testBit]
  by_cases hi : i < d
  · exact htb i hi q hq
  · have hgt : q < 2 ^ i := hq.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (l := (coordState d).2.2) (i := i)
        (by omega),
      Option.getD_none, Nat.zero_testBit, Nat.testBit_eq_false_of_lt hgt]
/-- Broadcast constant `n` across `k` little-endian columns with 1-mask `mx`. -/
def vecConst (mx : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => (if n % 2 = 1 then mx else 0) :: vecConst mx k (n / 2)
theorem vecConst_length (mx : ℕ) : ∀ k n : ℕ, (vecConst mx k n).length = k
  | 0, _ => rfl
  | k + 1, n => congrArg Nat.succ (vecConst_length mx k (n / 2))
theorem vecVal_const {mx q : ℕ} (hq : mx.testBit q = true) :
    ∀ (k n : ℕ), vecVal (vecConst mx k n) q = n % 2 ^ k
  | 0, n => by simp [vecConst, vecVal, Nat.mod_one]
  | k + 1, n => by
      have hm := mod_two_mul_add (2 ^ k) (n / 2) (n % 2) (by omega)
      rw [show n % 2 + 2 * (n / 2) = n by omega] at hm
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
        simp [vecConst, vecVal, vecVal_const hq k (n / 2), pow_succ', hm, h, hq]
/-- Bitwise column MUX selecting `as` where `m` is `1` and `bs` where `m` is `0`. -/
def vecMux (m : ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => syncNat ((m &&& a) ||| (b ^^^ (m &&& b))) :: vecMux m as bs
theorem vecMux_length (m : ℕ) :
    ∀ (as bs : List ℕ), as.length = bs.length → (vecMux m as bs).length = as.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => congrArg Nat.succ (vecMux_length m as bs (Nat.succ.inj h))
theorem vecVal_mux (m : ℕ) :
    ∀ (as bs : List ℕ) (q : ℕ),
      as.length = bs.length →
      vecVal (vecMux m as bs) q = if m.testBit q then vecVal as q else vecVal bs q
  | [], [], _, _ => by simp [vecMux, vecVal]
  | a :: as, b :: bs, q, hlen => by
      simp only [vecMux, vecVal, syncNat_eq, Nat.testBit_or, Nat.testBit_xor,
        Nat.testBit_and, vecVal_mux m as bs q (Nat.succ.inj hlen)]
      cases m.testBit q <;> cases a.testBit q <;> cases b.testBit q <;> simp
theorem vecVal_drop :
    ∀ (s : ℕ) (cs : List ℕ) (q : ℕ), vecVal (cs.drop s) q = vecVal cs q >>> s
  | 0, cs, q => by simp
  | s + 1, [], q => by simp [vecVal]
  | s + 1, c :: cs, q => by
      simp only [List.drop_succ_cons, vecVal_drop s cs q, vecVal,
        Nat.shiftRight_eq_div_pow, show 2 ^ (s + 1) = 2 * 2 ^ s by ring, ← Nat.div_div_eq_div_mul]
      cases c.testBit q <;> simp [show (1 + 2 * vecVal cs q) / 2 = vecVal cs q by omega]
theorem vecVal_take : ∀ (s : ℕ) (cs : List ℕ) (q : ℕ), vecVal (cs.take s) q =
    vecVal cs q &&& ((1 <<< s) - 1) := by
  refine fun s cs q ↦ Nat.eq_of_testBit_eq fun i ↦ ?_
  by_cases hi : i < s <;> simp [vecVal_testBit, Nat.shiftLeft_eq, 
    List.getD_eq_getElem?_getD, hi]
theorem vecVal_shl :
    ∀ (r : ℕ) (cs : List ℕ) (q : ℕ),
      vecVal (List.replicate r 0 ++ cs) q = vecVal cs q <<< r
  | 0, cs, q => by simp
  | r + 1, cs, q => by
      simp only [List.replicate_succ, List.cons_append, vecVal, Nat.zero_testBit,
          Bool.false_eq_true, ↓reduceIte, zero_add, vecVal_shl r cs q, Nat.shiftLeft_eq]; ring
/-- Load `n` columns from `cs` onto wires `off .. off + n - 1` of an initially-zero `CT`. -/
def loadCols : ℕ → ℕ → List ℕ → CT → CT
  | 0, _, _, ct => ct
  | k + 1, off, cs, ct =>
      let prev := loadCols k off cs ct
      xorStrict 7 prev (off + k) (cs.getD k 0)
theorem getCT_loadCols :
    ∀ (k off : ℕ) (cs : List ℕ) (u : ℕ),
      off + k ≤ 128 → u < 128 →
      getCT 7 (loadCols k off cs (.leaf 0)) u =
        if off ≤ u ∧ u < off + k then cs.getD (u - off) 0 else 0
  | 0, off, _, u, _, _ => by simp [loadCols, getCT, show ¬(off ≤ u ∧ u < off) by omega]
  | k + 1, off, cs, u, hk, hu => by
      rw [loadCols, xorStrict_eq, getCT_xorCT 7 _ u _ _ hu (by omega),
          getCT_loadCols k off cs u (by omega) hu]
      if hku : off + k = u then simp [← hku]
      else simp [hku, show (off ≤ u ∧ u < off + (k + 1)) ↔ (off ≤ u ∧ u < off + k) by omega]
/-- Masked column comparison across `k` output wires `off .. off + k - 1`. -/
def checkColsMask : ℕ → ℕ → CT → List ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | k + 1, off, out, exp, vmask =>
      Nat.beq (getCT 7 out (off + k) &&& vmask) ((exp.getD k 0) &&& vmask) &&
        checkColsMask k off out exp vmask
theorem checkColsMask_sound :
    ∀ (k off : ℕ) (out : CT) (exp : List ℕ) (vmask q : ℕ),
      checkColsMask k off out exp vmask = true →
      vmask.testBit q = true →
      ∀ j < k, (getCT 7 out (off + j)).testBit q = (exp.getD j 0).testBit q
  | 0, _, _, _, _, _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, off, out, exp, vmask, q, hchk, hvm, j, hj => by
      rcases Bool.and_eq_true_iff.mp hchk, eq_or_ne j k with ⟨⟨heq, hrest⟩, rfl | hjk⟩
      · simpa [Nat.testBit_and, hvm] using congrArg (·.testBit q) (Nat.beq_eq.mp heq)
      · exact checkColsMask_sound k off out exp vmask q hrest hvm j (by omega)
/-- Universal MBU `SubspaceStep`, exact `T`/`TOFF` counts, and `DynWires` for `PrimTree`. -/
theorem subspaceStep_primTreeXor {Var : Type} [Fintype Var] [DecidableEq Var] {W B M n nAnd : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (M + 1) n) (sMask : ℕ)
    (t : PrimTree) (hCheck : (checkPrimTree M 0 sMask t).1 = true ∧
    (checkPrimTree M 0 sMask t).2.2 = nAnd) (outW : Fin B → Wire (M + 1)) (rTgt : QRegister B n)
    (hDisj : r.DisjointWires rTgt) (st : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) (hCln : ∀ u : Wire (M + 1), sMask.testBit u.val = true → ∀ δ,
    (∀ k : Fin W, δ (rWork k) = 0) → st δ (r u) = 0) : SubspaceStep (mkKetOpW rWork st ph)
    (mkKetOpW rWork (fun δ ↦ DynCircExt.writeReg (st δ) rTgt (fun j ↦ st δ (rTgt j) +
    if (evalPrimTree M (natOfZModBits (M + 1)
    (fun u ↦ st δ (r u))) t).testBit (outW j).val then 1 else 0)) ph)
    (bennettXorReg v r (decodePrimTree M t) outW rTgt hDisj) ∧
    (bennettXorReg v r (decodePrimTree M t) outW rTgt hDisj).count .T = 4 * nAnd ∧
    (bennettXorReg v r (decodePrimTree M t) outW rTgt hDisj).count .TOFF = 0 ∧ (∀ S : Wire n → Prop,
    (∀ u, S (r u)) → (∀ j, S (rTgt j)) →
    DynWires S (bennettXorReg v r (decodePrimTree M t) outW rTgt hDisj)) := by
  rcases decodePrimTree_spec M t 0 sMask with ⟨hv, _, ha⟩
  obtain ⟨ht, hf⟩ := count_bennettXorReg v r (decodePrimTree M t) outW rTgt hDisj
  have hstep :=
      subspaceStep_bennettXorReg_mkKetOpW v rWork r sMask (decodePrimTree M t)
      (hv.trans hCheck.1) outW rTgt hDisj st ph hCln
  simp_rw [PrimGateEval.fwdBits_decodePrimTree_eq_ite] at hstep
  exact ⟨hstep, ht.trans (congrArg (4 * ·) (ha.trans hCheck.2)), hf, fun S hr htgt ↦
      dynWires_bennettXorReg v r _ outW rTgt hDisj hr htgt⟩
end QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync
namespace QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70
open QProg Qubit PhotochemistrySolution.ZeroNEremAxisSq18 PhotochemistrySolution.ZeroNEremCsa36Kick
  PhotochemistrySolution.BandEnc12Sync
/-- Initial `2 ^ 18`-lane column tree with wire `0 = nn` and wires `1..18 = coordState 18`. -/
def initDomCT (nn : ℕ) : CT :=
  let r := coordState 18
  loadCols 19 0 ((if Nat.beq nn 1 then r.2.1 else 0) :: r.2.2) (.leaf 0)
theorem getCT_initDomCT (nn d2 u : ℕ) (hd2 : d2 < 2 ^ 18)
    (hu : u < 128) : (getCT 7 (initDomCT nn) u).testBit d2 = if u = 0 then Nat.beq nn 1 else if u <
    19 then d2.testBit (u - 1) else false := by
  obtain ⟨_, hM, _, _, htb⟩ := coordState_spec 18
  rw [initDomCT, getCT_loadCols 19 0 _ u (by omega) hu]
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [ite_eq_left (by omega)]; cases Nat.beq nn 1 <;> simp only [Bool.false_eq_true, ↓reduceIte,
      Nat.sub_zero, List.getD_cons_zero, Nat.zero_testBit, hM, Nat.testBit_two_pow_sub_one,
          decide_eq_true hd2]
  · if hu19 : u < 19 then
      obtain ⟨k, rfl⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
      simpa [hu19, hu0] using htb k (by omega) d2 hd2
    else simp [hu0, hu19]
theorem evalStrict_initDomCT {M : ℕ} (hM18 : 18 ≤ M) (hM : M < 128) (t : PrimTree)
    (β : Fin (M + 1) → ZMod 2) (d2 : ℕ) (hd2 : d2 < 2 ^ 18)
    (hd2Eq : ∀ b : Fin 18, (β ⟨1 + b.val, by omega⟩ == 1) = d2.testBit b.val)
    (hZero : ∀ u : Fin (M + 1), 19 ≤ u.val → β u = 0)
    (u : ℕ) (hu : u < M + 1) :
    let nn := if β ⟨0, Nat.succ_pos M⟩ == 1 then 1 else 0
    (getCT 7 (evalStrict M (coordState 18).2.1 (initDomCT nn) t) u).testBit d2 =
        (evalPrimTree M (natOfZModBits (M + 1) β) t).testBit u := by
  refine evalStrict_sound hM t _ _ d2 (by
    rw [(coordState_spec 18).2.1, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hd2)
        (fun v hv ↦ ?_) u hu
  rw [getCT_initDomCT _ d2 v hd2 (by omega), natOfZModBits_testBit_lt β hv]
  rcases eq_or_ne v 0 with rfl | hv0
  · cases β ⟨0, Nat.succ_pos M⟩ == 1 <;> rfl
  · if hv19 : v < 19 then
      simp only [hv0, hv19, ↓reduceIte]
      rw [show (⟨v, hv⟩ : Fin (M + 1)) = ⟨1 + (v - 1), by omega⟩ from Fin.ext (by dsimp; omega),
          hd2Eq ⟨v - 1, by omega⟩]
    else simp [hv0, hv19, hZero ⟨v, hv⟩ (by dsimp; omega)]
end QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70
namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open QProg Qubit PhotochemistrySolution.ZeroNEremAxisSq18
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg_apply_reg)
theorem stepCB_decodePrimTree_apply {M n : ℕ} (t : PrimTree) (r : QRegister (M + 1) n)
    (β : BitAssignment n) (u : Fin (M + 1)) :
    stepCB r (decodePrimTree M t).fwdBits β (r u) =
      if (evalPrimTree M (natOfZModBits (M + 1)
          (fun i ↦ β (r i))) t).testBit u.val then 1 else 0 := by
  exact (writeReg_apply_reg β r _ u).trans (PrimGateEval.fwdBits_decodePrimTree_eq_ite t _ u)
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein

namespace QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep

open Operator QProg Matrix HermitianMat PhotochemistrySolution.XMeasUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding sqrtHalf
  star_sqrtHalf sqrtHalf_mul_sqrtHalf bitSign bitSign_add bitSign_mul_self ket_H_apply
open scoped ComplexOrder MatrixOrder Circuit.Notation
variable {Var : Type}
/--
Complete `m` -wire `X` -half `SubspaceStep` : unloads `C_vec * R` into `S_vec * R` in `0` `T` gates!
-/
theorem subspaceStep_bellXHalfVec [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wCtrl : Fin M → Wire n)
    (wTgt : Fin m → Fin M → Wire n)
      (_hB_inj : ∀ k₁ k₂ : Fin m, k₁ ≠ k₂ → qB k₁ ≠ qB k₂)
    (hbc : ∀ (k : Fin m) (p : Fin M), qB k ≠ wCtrl p)
      (hbt_all : ∀ (k₁ k₂ : Fin m) (p : Fin M), qB k₁ ≠ wTgt k₂ p)
    (hc_disj : ∀ (k : Fin m) (p q : Fin M), wCtrl p ≠ wTgt k q)
      (_ht_disj : ∀ (k₁ k₂ : Fin m), k₁ ≠ k₂ → ∀ p q :
    Fin M, wTgt k₁ p ≠ wTgt k₂ q) (R : Operator (2 ^ n)),
      (∀ k : Fin m, (QRegister.singleton (qB k)).basisOutcomeProjector 0 *
        ((specPortUnextract1Unitary M (qB k) wCtrl (wTgt k)
    (hbc k) (hbt_all k k) (fun p ↦ hc_disj k p p)).1 * R) =
        (specPortUnextract1Unitary M (qB k) wCtrl (wTgt k)
    (hbc k) (hbt_all k k) (fun p ↦ hc_disj k p p)).1 * R) →
      SubspaceStep (Var := Var)
        ((specFanoutCopyVecCirc M m qB wCtrl wTgt hbc (fun k ↦ hbt_all k k)
    (fun k p ↦ hc_disj k p p)).eval.1 * R)
        ((specPortUnextractVecUnitary M m qB wCtrl wTgt hbc
    (fun k ↦ hbt_all k k) (fun k p ↦ hc_disj k p p)).1 * R)
        (bellXHalfVecDyn v M m qB wCtrl wTgt (fun k p ↦ hc_disj k p p))
  | 0, _, _, _, _, _, _, _, _, R, _ => by
      simpa [specFanoutCopyVecCirc, specPortUnextractVecUnitary,
          bellXHalfVecDyn] using subspaceStep_of_circuit (Var := Var) R .identity
  | m + 1, qB, wCtrl, wTgt, hB_inj, hbc, hbt_all, hc_disj, ht_disj, R, hqB_clean => by
      let l := Fin.last m
      let qB' (k : Fin m) := qB k.castSucc
      let wTgt' (k : Fin m) := wTgt k.castSucc
      let ht1 (i) := hbt_all i i
      let hc1 (i) (p) := hc_disj i p p
      let C_pre := (specFanoutCopyVecCirc M m qB' wCtrl wTgt' (fun k ↦ hbc k.castSucc)
        (fun k ↦ ht1 k.castSucc) (fun k ↦ hc1 k.castSucc)).eval.1
      let S (i) := (specPortUnextract1Unitary M (qB i) wCtrl (wTgt i) (hbc i) (ht1 i) (hc1 i)).1
      let C (i) := (specFanoutCopyCirc M (qB i) wCtrl (wTgt i) (hbc i) (ht1 i) (hc1 i)).eval.1
      let U (i) := (bitToggleUnitary (qB i) (czFanoutPhase M wCtrl (wTgt i))
        (czFanoutPhase_indep M wCtrl (wTgt i) (fun p ↦ (hbc i p).symm)
          fun p ↦ (ht1 i p).symm)).1
      have hcSC : S l * C_pre = C_pre * S l :=
        specPortUnextract1_comm_specFanoutCopyVec M (qB l) wCtrl (wTgt l) (hbc l) (ht1 l) (hc1 l)
          (hc_disj l) m qB' wTgt' (fun k ↦ hB_inj _ _ (Fin.castSucc_ne_last k).symm)
          (fun k ↦ hbc k.castSucc) (fun k ↦ ht1 k.castSucc) (fun k ↦ hbt_all k.castSucc l)
          (fun k ↦ hbt_all l k.castSucc) (fun k ↦ hc_disj k.castSucc)
          fun k ↦ ht_disj k.castSucc l (Fin.castSucc_ne_last k)
      have hAbs {P A B : Operator (2 ^ n)} (hAB : A * B = B * A) (hBP : B * P = P * B)
          (hP : P * (A * R) = A * R) : P * (A * (B * R)) = A * (B * R) := by
        rw [← Matrix.mul_assoc A B R, hAB, Matrix.mul_assoc B A R, ← Matrix.mul_assoc P B _, ← hBP,
          Matrix.mul_assoc B P _, hP]
      have hs2 : SubspaceStep (Var := Var) ((specFanoutCopyVecCirc M (m + 1) qB wCtrl wTgt hbc
          ht1 hc1).eval.1 * R) (C_pre * (S l * R))
          (bellXHalf1Dyn v M (qB l) wCtrl (wTgt l) (hc1 l)) := by
        simpa only [specFanoutCopyVecCirc, Circuit.eval_seq, Submonoid.coe_mul,
          Matrix.mul_assoc] using subspaceStep_congr_out
          (subspaceStep_bellXHalf1 v M (qB l) wCtrl (wTgt l) (hbc l) (ht1 l) (hc1 l) (C_pre * R)
            (hAbs hcSC (cleanProj_singleton_comm_specFanoutCopyVec M m qB' wCtrl wTgt'
              (fun k ↦ hbc k.castSucc) (fun k ↦ ht1 k.castSucc) (fun k ↦ hc1 k.castSucc) (qB l)
              fun k ↦ hbt_all l k.castSucc) (hqB_clean l)))
          (by rw [← Matrix.mul_assoc, hcSC, Matrix.mul_assoc])
      have hC2_sq : C l * C l = 1 := matrix_ext_ket fun β ↦ by
        simp only [C, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, specFanoutCopyCirc_mulVec_ket]
        rcases bit_cases (β (qB l)) with hb | hb <;> simp [hb, one_ne_zero,
          fanoutXorBits_of_ne_tgt M wCtrl _ β _ (ht1 _),
              fanoutXorBits_involutive M wCtrl _ (hc_disj l) β]
      have hSC {i j : Fin (m + 1)} (hij : i ≠ j) : (U j * C j) * C i = C i * (U j * C j) :=
        specPortUnextract1_comm_specFanoutCopy1 M (qB i) (qB j) wCtrl (wTgt i) (wTgt j) (hbc _)
          (ht1 _) (hbc _) (ht1 _) (hc1 _) (hc1 _) (hc_disj _) (hc_disj _) (ht_disj _ _ hij)
          (hB_inj _ _ hij.symm) (hbt_all _ _) (hbt_all _ _)
      have hSS (k : Fin m) : S k.castSucc * S l = S l * S k.castSucc := by
        have hne : k.castSucc ≠ l := Fin.castSucc_ne_last k
        have hUU : U k.castSucc * U l = U l * U k.castSucc := matrix_ext_ket fun β ↦ by
          simp only [U, ← Matrix.mulVec_mulVec, bitToggleUnitary_mulVec_ket,
            Function.update_of_ne (hB_inj _ _ hne), Function.update_of_ne (hB_inj _ _ hne.symm),
            czFanoutPhase_indep M wCtrl _ (fun p ↦ (hbc _ p).symm) (fun p ↦ (hbt_all _ _ p).symm),
            Function.update_comm (hB_inj _ _ hne.symm)]
        have hU2C1 : U l * C k.castSucc = C k.castSucc * U l := by
          rw [← Matrix.mul_one (U l), ← hC2_sq, ← Matrix.mul_assoc (U l) (C l),
            Matrix.mul_assoc _ (C l), specFanoutCopy1_comm_specFanoutCopy1 M _ _ wCtrl _ _
              (hbc _) (ht1 _) (hbc _) (ht1 _) (hc1 _) (hc1 _) (hc_disj _) (hc_disj _)
              (ht_disj _ _ hne) (hbt_all _ _) (hbt_all _ _),
            ← Matrix.mul_assoc, hSC hne, Matrix.mul_assoc, Matrix.mul_assoc, hC2_sq, Matrix.mul_one]
        change U k.castSucc * C k.castSucc * (U l * C l) = U l * C l * (U k.castSucc * C k.castSucc)
        rw [Matrix.mul_assoc (U k.castSucc) (C k.castSucc), ← Matrix.mul_assoc (C k.castSucc),
          ← hU2C1, Matrix.mul_assoc (U l), ← Matrix.mul_assoc (U k.castSucc) (U l), hUU]
        simpa only [Matrix.mul_assoc] using congrArg (U l * ·) (hSC hne.symm)
      refine subspaceStep_congr_out (hs2.seq (subspaceStep_bellXHalfVec v M m qB' wCtrl wTgt'
        (fun _ _ h ↦ hB_inj _ _ (Fin.castSucc_inj.mp · |> h)) (fun k ↦ hbc k.castSucc)
        (fun k₁ k₂ ↦ hbt_all k₁.castSucc k₂.castSucc) (fun k ↦ hc_disj k.castSucc)
        (fun _ _ h ↦ ht_disj _ _ (Fin.castSucc_inj.mp · |> h)) (S l * R) fun k ↦
          hAbs (hSS k) (by
            change (U l * C l) * _ = _ * (U l * C l)
            rw [Matrix.mul_assoc (U l) (C l), commute_singleton_proj_of_ket _ _ _
                (specFanoutCopyCirc_mulVec_ket M _ _ _ (hbc _) (ht1 _) (hc1 _)) (fun β ↦ by
                  rcases bit_cases (β (qB l)) with h | h <;> simp [qB', h, one_ne_zero,
                    fanoutXorBits_of_ne_tgt M _ _ β _ (hbt_all k.castSucc _)]),
              ← Matrix.mul_assoc (U l), commute_singleton_proj_of_ket _ _ _
                (bitToggleUnitary_mulVec_ket (qB l) (czFanoutPhase M wCtrl (wTgt l)) _)
                (fun _ ↦ Function.update_of_ne (hB_inj k.castSucc l (Fin.castSucc_ne_last k)) _ _),
              Matrix.mul_assoc]) (hqB_clean k.castSucc))) ?_
      simp only [specPortUnextractVecUnitary, S, l, qB', wTgt', Submonoid.coe_mul, Matrix.mul_assoc]
end QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep

namespace QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore

open Operator QProg Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
theorem zmod2_maj_id (a b c : ZMod 2) : (a + b + c).val + 2 * (((a + c) * (b + c) + c).val) =
    a.val + b.val + c.val := by
  decide +revert
end QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore

namespace QuantumComputation.Specs.PhotochemistrySolution.MidOWCore

open Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution.Stage4FineMbu
  PhotochemistrySolution.InPlaceModAdd
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.ScreenFermatCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg
    counts_wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254 (cnot1_step
    two_mul_mod_add)
attribute [local irreducible] mkKetOpW SubregMBUCore.wrapDynOnReg SubregMBUCore.uStageOfCP
theorem ung_finBitsVal_fin0 (f : Fin 0 → ZMod 2) : finBitsVal f = 0 :=
    Nat.lt_one_iff.mp (finBitsVal_lt f)
theorem pUngatedAddCarryKick_step : ∀ (k : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (3 * k + 3) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ (u : Fin (3 * k + 3)) (δ : BitAssignment n), 2 * k + 3 ≤ u.val →
      (∀ m : Fin W, δ (rWork m) = 0) → st δ (r u) = 0) →
    ∃ st' : BitAssignment n → BitAssignment n,
      SubspaceStep (mkKetOpW rWork st ph)
        (mkKetOpW rWork st' (fun δ ↦ ph δ +
          (((finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨1 + i.val, ungAdd_ltZ k i⟩)) +
             finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨k + 2 + i.val, ungAdd_ltB k i⟩)) +
             (st δ (r ⟨0, ungAdd_lt0 k⟩)).val) / 2 ^ (k + 1) : ℕ) : ZMod 2)))
        (pUngatedAddCarryKick k v r) ∧
      (∀ (δ : BitAssignment n) (w : Wire n),
        (∀ i : Fin (k + 1), w ≠ r ⟨1 + i.val, ungAdd_ltZ k i⟩) → st' δ w = st δ w) ∧
      (∀ (δ : BitAssignment n), (∀ m : Fin W, δ (rWork m) = 0) →
        finBitsVal (fun i : Fin (k + 1) ↦ st' δ (r ⟨1 + i.val, ungAdd_ltZ k i⟩)) =
          (finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨1 + i.val, ungAdd_ltZ k i⟩)) +
           finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨k + 2 + i.val, ungAdd_ltB k i⟩)) +
           (st δ (r ⟨0, ungAdd_lt0 k⟩)).val) % 2 ^ (k + 1))
  | 0, _, _, _, _, _, _, v, rWork, r, st, ph, _ => by
      let w0 := r ⟨0, ungAdd_lt0 0⟩
      let w1 := r ⟨1, ungAdd_lt1 0⟩
      let w2 := r ⟨2, ungAdd_lt2⟩
      have hMajId (δ) : finBitsVal (fun i : Fin 1 ↦ st δ (r ⟨1 + i.val, ungAdd_ltZ 0 i⟩)) +
          finBitsVal (fun i : Fin 1 ↦ st δ (r ⟨0 + 2 + i.val, ungAdd_ltB 0 i⟩)) + (st δ w0).val =
          (st δ w1 + st δ w2 + st δ w0).val +
            2 * (((st δ w1 + st δ w0) * (st δ w2 + st δ w0) + st δ w0).val) := by
        simpa only [w1, w2, finBitsVal_succ, ung_finBitsVal_fin0, Fin.val_zero, add_zero,
          zero_add, mul_zero] using (zmod2_maj_id (st δ w1) (st δ w2) (st δ w0)).symm
      refine ⟨fun δ ↦ Function.update (st δ) w1 (st δ w1 + st δ w2 + st δ w0),
        subspaceStep_of_eq_post
          (subspaceStep_seq_mbu (cnot1_step v rWork w0 w1 (ungAdd_ne01 0 r) st ph)
            (subspaceStep_seq_mbu (cnot1_step v rWork w0 w2 (ungAdd_ne02 r) _ _)
              (subspaceStep_seq_mbu (z1_step rWork w0 _ _)
                (subspaceStep_seq_mbu (cz2_step rWork w1 w2 (ungAdd_ne12 r) _ _)
                  (subspaceStep_seq_mbu (cnot1_step v rWork w0 w2 (ungAdd_ne02 r) _ _)
                    (cnot1_step v rWork w2 w1 (ungAdd_ne21 r) _ _))))))
          (mkKetOpW_congr rWork (fun δ _ ↦ funext fun u ↦ ?_) fun δ _ ↦ ?_),
        fun δ w hw ↦ Function.update_of_ne (hw ⟨0, Nat.zero_lt_one⟩) _ _, fun δ _ ↦ ?_⟩
      · by_cases h1 : u = w1 <;> by_cases h2 : u = w2 <;>
          (try simp only [Function.update_of_ne h1, Function.update_of_ne h2]) <;>
          simp [h1, h2, w0, w1, w2, 
            add_assoc, CharTwo.add_self_eq_zero] <;> ring
      · simp only [w0, w1, w2, Function.update_of_ne (ungAdd_ne02 r),
          Function.update_of_ne (ungAdd_ne01 0 r), Function.update_of_ne (ungAdd_ne12 r),
          Function.update_self, Function.update_of_ne (ungAdd_ne21 r), hMajId δ, pow_one,
          Nat.add_mul_div_left _ _ Nat.zero_lt_two, Nat.div_eq_of_lt (ZMod.val_lt _), zero_add,
          zmod2_val_cast]
        ring
      · dsimp only; rw [finBitsVal_succ, ung_finBitsVal_fin0, Nat.add_zero,
          show r ⟨1 + (0 : Fin 1).val, ungAdd_ltZ 0 0⟩ = w1 from rfl, Function.update_self,
          hMajId δ, pow_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt _)]
  | k + 1, _, _, _, W, n, _, v, rWork, r, st, ph, hCln => by
      let rMaj := r.compose ⟨fUngMaj k, fUngMaj_inj k⟩
      let rSub := r.compose ⟨fUngSub k, fUngSub_inj k⟩
      let wCin := r ⟨0, ungAdd_lt0 (k + 1)⟩
      let wZ0 := r ⟨1, ungAdd_lt1 (k + 1)⟩
      let wB0 := r ⟨k + 3, ungAdd_ltB0 k⟩
      let stFwd (δ) := stepCB rMaj cpMaj4.fwdBits (st δ)
      have hNe3 {i} (hi : i < 3 * (k + 1) + 3) (h : i ≠ 2 * k + 5) : r ⟨i, hi⟩ ≠ rMaj w4_3 :=
        fun e ↦ h (congrArg Fin.val (r.wires.injective e))
      have hrZ (i : Fin (k + 1)) :
          rSub ⟨1 + i.val, ungAdd_ltZ k i⟩ = r ⟨1 + i.succ.val, ungAdd_ltZ (k + 1) i.succ⟩ :=
        congrArg r.wires (Fin.ext (by
          rcases i with ⟨_, _⟩; dsimp [fUngSub, idxUngSub, Fin.val_succ]; split_ifs <;>
            omega))
      obtain ⟨stMid, hMidStep, hMidNot, hMidVal⟩ := pUngatedAddCarryKick_step k v rWork rSub stFwd
        ph fun u δ hu hz ↦ (congrArg (stFwd δ) (congrArg r.wires (Fin.ext
          (by have := u.isLt; dsimp [fUngSub, idxUngSub]; split_ifs <;> omega)))).trans
          ((stepCB_cpMaj4_not rMaj (st δ) (hNe3 (by have := u.isLt; omega) (by omega))).trans
            (hCln ⟨3 + u.val, by have := u.isLt; omega⟩ δ (by dsimp only; omega) hz))
      let stUn (δ) (w) := if w = rMaj w4_3 then st δ w else stMid δ w
      have hSB {f1 f2 : Fin (k + 1) → ℕ} (hf1 : ∀ i, f1 i < 3 * k + 3)
          (hf2 : ∀ i, f2 i < 3 * (k + 1) + 3) (hEq : ∀ i, idxUngSub k ⟨f1 i, hf1 i⟩ = f2 i)
          (hNe : ∀ i, f2 i ≠ 2 * k + 5) (δ) :
          finBitsVal (fun i ↦ stFwd δ (rSub ⟨f1 i, hf1 i⟩)) =
            finBitsVal (fun i ↦ st δ (r ⟨f2 i, hf2 i⟩)) :=
        congrArg finBitsVal (funext fun i ↦ (congrArg (stFwd δ) (congrArg r.wires
          (Fin.ext (hEq i)))).trans (stepCB_cpMaj4_not rMaj (st δ) (hNe3 (hf2 i) (hNe i))))
      let sumIn (δ) := finBitsVal (fun i : Fin (k + 2) ↦ st δ (r ⟨1 + i.val, ungAdd_ltZ _ i⟩)) +
        finBitsVal (fun i : Fin (k + 2) ↦ st δ (r ⟨(k + 1) + 2 + i.val, ungAdd_ltB _ i⟩)) +
        (st δ wCin).val
      have hDecomp (δ) (hz : ∀ m, δ (rWork m) = 0) : sumIn δ = (st δ wZ0 + st δ wB0 + st δ wCin).val
          + 2 * (finBitsVal (fun i : Fin (k + 1) ↦ stFwd δ (rSub ⟨1 + i.val, ungAdd_ltZ k i⟩)) +
            finBitsVal (fun i : Fin (k + 1) ↦ stFwd δ (rSub ⟨k + 2 + i.val, ungAdd_ltB k i⟩)) +
            (stFwd δ (rSub ⟨0, ungAdd_lt0 k⟩)).val) := by
        dsimp only [sumIn]
        rw [finBitsVal_succ fun i ↦ st δ (r ⟨1 + i.val, _⟩),
          finBitsVal_succ fun i ↦ st δ (r ⟨(k + 1) + 2 + i.val, _⟩),
          hSB (ungAdd_ltZ k) (fun i ↦ ungAdd_ltZ (k + 1) i.succ)
            (fun ⟨_, _⟩ ↦ by dsimp [idxUngSub, Fin.val_succ]; split_ifs <;> omega)
            (fun ⟨_, _⟩ ↦ by dsimp [Fin.val_succ]; omega) δ,
          hSB (ungAdd_ltB k) (fun i ↦ ungAdd_ltB (k + 1) i.succ)
            (fun ⟨_, _⟩ ↦ by dsimp [idxUngSub, Fin.val_succ]; split_ifs <;> omega)
            (fun ⟨_, _⟩ ↦ by dsimp [Fin.val_succ]; omega) δ,
          show rSub ⟨0, ungAdd_lt0 k⟩ = rMaj w4_3 from rfl]
        dsimp only [stFwd]
        rw [stepCB_cpMaj4_anc, show rMaj w4_3 = r ⟨2 * k + 5, by omega⟩ from rfl,
          hCln ⟨2 * k + 5, by omega⟩ δ (by dsimp only; omega) hz, zero_add,
          show rMaj w4_0 = wZ0 from rfl, show rMaj w4_1 = wB0 from rfl,
          show rMaj w4_2 = wCin from rfl,
          show r ⟨1 + (0 : Fin (k + 2)).val, ungAdd_ltZ (k + 1) 0⟩ = wZ0 from rfl,
          show r ⟨(k + 1) + 2 + (0 : Fin (k + 2)).val, _⟩ = wB0 from
            congrArg r.wires (Fin.ext (by dsimp))]
        have := zmod2_maj_id (st δ wZ0) (st δ wB0) (st δ wCin)
        omega
      let phPost (δ) := ph δ + ((sumIn δ / 2 ^ (k + 2) : ℕ) : ZMod 2)
      have hWrap := wrapCpMaj4 v rWork rMaj (pUngatedAddCarryKick k v rSub) st stMid ph _ phPost
        (fun δ hz ↦ hCln ⟨2 * k + 5, by omega⟩ δ (by dsimp only; omega) hz)
        (fun u δ ↦ hMidNot δ (rMaj u) fun i e ↦ by
          have hv := congrArg Fin.val (r.wires.injective (e.trans (hrZ i)))
          cases u with | mk _ _ => cases i with | mk _ _ =>
            dsimp [fUngMaj, idxUngMaj, Fin.val_succ] at hv; split_ifs at hv <;> omega)
        (fun δ hz ↦ by
          dsimp only [phPost]; rw [hDecomp δ hz, maj_div_pow_succ (ZMod.val_lt _) _ (k + 1)])
        hMidStep
      have hUnNot (δ) (w) (hw : ∀ i, w ≠ rSub ⟨1 + i.val, ungAdd_ltZ k i⟩) : stUn δ w = st δ w :=
        if hcn : w = rMaj w4_3 then leg_if_pos hcn
        else (leg_if_neg hcn).trans ((hMidNot δ w hw).trans (stepCB_cpMaj4_not rMaj (st δ) hcn))
      let s1 (δ) := Function.update (stUn δ) wZ0 (stUn δ wZ0 + stUn δ wB0)
      let s2 (δ) := Function.update (s1 δ) wZ0 (s1 δ wZ0 + s1 δ wCin)
      refine ⟨s2, subspaceStep_seq_mbu hWrap (subspaceStep_seq_mbu
        (cnot1_step v rWork wB0 wZ0 (ungAdd_neB0Z0 k r) stUn phPost)
        (cnot1_step v rWork wCin wZ0 (ungAdd_ne01 (k + 1) r) s1 phPost)),
        fun δ w hw ↦ by
          simpa only [s2, s1, Function.update_of_ne (show w ≠ wZ0 from hw ⟨0,
              Nat.zero_lt_succ _⟩)] using
            hUnNot δ w fun i e ↦ hw i.succ (e.trans (hrZ i)), fun δ hz ↦ ?_⟩
      have hUnFixed {idx : ℕ} (hi : idx < 3 * (k + 1) + 3) (hni : ∀ i : Fin (k + 1), idx ≠ 2 +
          i.val) :
          stUn δ (r ⟨idx, hi⟩) = st δ (r ⟨idx, hi⟩) := hUnNot δ _ fun i e ↦ hni i (by
        have hv := congrArg Fin.val (r.wires.injective (e.trans (hrZ i)))
        dsimp [Fin.val_succ] at hv; omega)
      dsimp only [s2, s1]; rw [finBitsVal_succ, congrArg finBitsVal (funext fun j ↦ by
          have hne := show r ⟨1 + j.succ.val, ungAdd_ltZ (k + 1) j.succ⟩ ≠ wZ0 from
            fun e ↦
                Nat.succ_ne_zero j.val (Nat.add_left_cancel (congrArg Fin.val (r.wires.injective
                e)))
          simpa only [Function.update_of_ne hne] using
            (leg_if_neg (hNe3 _ (by rcases j with ⟨_, _⟩; dsimp [Fin.val_succ]; omega))).trans
              (congrArg (stMid δ) (hrZ j).symm)),
        hMidVal δ hz, show r ⟨1 + (0 : Fin (k + 2)).val, ungAdd_ltZ (k + 1) 0⟩ = wZ0 from rfl,
        Function.update_self, Function.update_of_ne (ungAdd_ne01 (k + 1) r), Function.update_self,
        hUnFixed _ (fun _ ↦ by omega), hUnFixed _ (fun ⟨_, _⟩ ↦ by omega), hUnFixed _ (fun _ ↦
            by omega),
        two_mul_mod_add (ZMod.val_lt _), ← hDecomp δ hz, (pow_succ' 2 (k + 1)).symm]

/- ### 1. Arithmetic Carry-Prefix Helper `majCarryBit` -/

/-- Carry out of bit `k` (`0`-indexed) of `valA + valB + c0`, cast to `ZMod 2`. -/
def majCarryBit (valA valB c0 k : ℕ) : ZMod 2 :=
    (((valA % 2 ^ (k + 1) + valB % 2 ^ (k + 1) + c0) / 2 ^ (k + 1) : ℕ) : ZMod 2)
theorem bit_add_two_mul_mod {b : ℕ} (hb : b < 2) (X k : ℕ) : (b + 2 * X) % 2 ^ (k + 1) = b + 2 *
    (X % 2 ^ k) := by
  conv_lhs => rw [pow_succ', ← Nat.mod_add_div X (2 ^ k)]
  rw [show b + 2 * (X % 2 ^ k + 2 ^ k * (X / 2 ^ k)) = b + 2 * (X % 2 ^ k) + 2 * 2 ^ k * (X / 2 ^ k)
      by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by have := Nat.mod_lt X (Nat.two_pow_pos k); omega)]
theorem majCarryBit_val {valA valB c0 : ℕ} (hc : c0 ≤ 1)
    (k : ℕ) : (majCarryBit valA valB c0 k).val = (valA % 2 ^ (k + 1) + valB % 2 ^ (k + 1) + c0) /
    2 ^ (k + 1) := by
  have := Nat.mod_lt valA (Nat.two_pow_pos (k + 1))
  have := Nat.mod_lt valB (Nat.two_pow_pos (k + 1))
  exact ZMod.val_natCast_of_lt (Nat.div_lt_of_lt_mul (by omega))
theorem majCarryBit_zero_step (a0 b0 cin : ZMod 2) (valA' valB' : ℕ) : majCarryBit (a0.val + 2 *
    valA') (b0.val + 2 * valB') cin.val 0 = (a0 + cin) * (b0 + cin) + cin := by
  have : _ ∧ _ := ⟨zmod2_maj_id a0 b0 cin, ZMod.val_lt (a0 + b0 + cin)⟩
  simp only [majCarryBit, Nat.zero_add, pow_one, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (ZMod.val_lt _), zmod2_val_cast,
    show (a0.val + b0.val + cin.val) / 2 = ((a0 + cin) * (b0 + cin) + cin).val by omega]
theorem majCarryBit_succ_step (a0 b0 cin : ZMod 2) (valA' valB' k : ℕ) : majCarryBit (a0.val + 2 *
    valA') (b0.val + 2 * valB') cin.val (k + 1) = majCarryBit valA' valB' (((a0 + cin) *
    (b0 + cin) + cin).val) k := by
  have := zmod2_maj_id a0 b0 cin
  dsimp only [majCarryBit]
  rw [bit_add_two_mul_mod (ZMod.val_lt _) valA' _, bit_add_two_mul_mod (ZMod.val_lt _) valB' _,
    show a0.val + 2 * (valA' % 2 ^ (k + 1)) + (b0.val + 2 * (valB' % 2 ^ (k + 1))) + cin.val =
      (a0 + b0 + cin).val + 2 * (valA' % 2 ^ (k + 1) + valB' % 2 ^ (k + 1) +
        ((a0 + cin) * (b0 + cin) + cin).val) by omega, maj_div_pow_succ (ZMod.val_lt _) _ (k + 1)]
theorem majCarryBit_and_zero (a0 b0 : ZMod 2) (valA' valB' : ℕ) : majCarryBit (a0.val + 2 * valA')
    (b0.val + 2 * valB') 0 0 = a0 * b0 := by
  simpa only [ZMod.val_zero, add_zero] using majCarryBit_zero_step a0 b0 0 valA' valB'
theorem majCarryBit_and_succ (a0 b0 : ZMod 2) (valA' valB' k : ℕ) : majCarryBit (a0.val +
  2 * valA') (b0.val + 2 * valB') 0 (k + 1) = majCarryBit valA' valB' (a0 * b0).val k := by
  simpa only [ZMod.val_zero, add_zero] using majCarryBit_succ_step a0 b0 0 valA' valB' k

/- ### 2. Parametric `m`-Step Majority Chain `pWrapMajChain` (`4 * m` `T`, `0` `.TOFF`) -/

theorem majCh_lt0 (m : ℕ) : 0 < 1 + 3 * m := by omega
theorem majCh_ltA (m : ℕ) (j : Fin m) : 1 + j.val < 1 + 3 * m := by have := j.isLt; omega
theorem majCh_ltB (m : ℕ) (j : Fin m) : 1 + m + j.val < 1 + 3 * m := by have := j.isLt; omega
theorem majCh_ltOut (m : ℕ) (j : Fin m) : 1 + 2 * m + j.val < 1 + 3 * m := by
  have := j.isLt; omega
/-- Wire map for the `m` clean carry outputs `r[1+2*m .. 3*m]` of `pWrapMajChain`. -/
def fMajOut (m : ℕ) : Fin m → Fin (1 + 3 * m) := fun j ↦ ⟨1 + 2 * m + j.val, majCh_ltOut m j⟩
theorem fMajOut_inj (m : ℕ) : Function.Injective (fMajOut m) := fun _ _ e ↦ Fin.ext
  (by have := congrArg Fin.val e; dsimp [fMajOut] at this; omega)
/-- Output subregister `r[1+2*m .. 3*m]` of `pWrapMajChain`. -/
def rMajOut (m : ℕ) {n : ℕ} (r : QRegister (1 + 3 * m) n) : QRegister m n :=
  r.compose ⟨fMajOut m, fMajOut_inj m⟩
/-- Head `4`-wire index map `(A[0], B[0], cin, C[0])` for `pWrapMajChain (m + 1)`. -/
def idxMajHead (m : ℕ) (u : Fin 4) : ℕ :=
    if u.val = 0 then 1 else if u.val = 1 then 2 + m else if u.val = 2 then 0 else 3 + 2 * m
theorem idxMajHead_lt (m : ℕ) (u : Fin 4) : idxMajHead m u < 1 + 3 * (m + 1) := by
  dsimp only [idxMajHead]; (try split_ifs) <;> omega
/-- `Fin`-typed head `4`-wire map for `pWrapMajChain (m + 1)`. -/
def fMajHead (m : ℕ) : Fin 4 → Fin (1 + 3 * (m + 1)) := fun u ↦ ⟨idxMajHead m u, idxMajHead_lt m u⟩
theorem fMajHead_inj (m : ℕ) : Function.Injective (fMajHead m) := fun a b e ↦ by
  fin_cases a <;> fin_cases b <;> simp [fMajHead, idxMajHead] at e ⊢ <;> omega
/--
Tail `(1 + 3 * m)` -wire index map `(C[0], A[1..m], B[1..m], C[1..m])` for `pWrapMajChain (m + 1)` .
-/
def idxMajSub (m : ℕ) (u : Fin (1 + 3 * m)) : ℕ :=
    if u.val = 0 then 3 + 2 * m else if u.val < 1 + m then 1 + u.val else if u.val < 1 + 2 *
    m then 2 + u.val else 3 + u.val
theorem idxMajSub_lt (m : ℕ) (u : Fin (1 + 3 * m)) : idxMajSub m u < 1 + 3 * (m + 1) := by
  have _ := u.isLt; dsimp only [idxMajSub]; (try split_ifs) <;> omega
/-- `Fin`-typed tail wire map for `pWrapMajChain (m + 1)`. -/
def fMajSub (m : ℕ) : Fin (1 + 3 * m) → Fin (1 + 3 * (m + 1)) := fun u ↦
    ⟨idxMajSub m u, idxMajSub_lt m u⟩
theorem fMajSub_inj (m : ℕ) : Function.Injective (fMajSub m) := fun a b e ↦ by
  have hv : idxMajSub m a = idxMajSub m b := congrArg Fin.val e
  have : _ ∧ _ := ⟨a.isLt, b.isLt⟩
  dsimp only [idxMajSub] at hv; (try split_ifs at hv) <;> exact Fin.ext (by omega)
/-- Parametric `m`-step majority carry-ripple MBU wrapper (`4 * m` `T`, `0` `.TOFF`). -/
def pWrapMajChain : (m : ℕ) → {Var : Type} → {n : ℕ} → Var → QRegister (1 + 3 * m) n →
    DynamicCircuit Var n → DynamicCircuit Var n
  | 0, _, _, _, _, mid => mid
  | m + 1, _, _, v, r, mid =>
      wrapDynOnReg v (r.compose ⟨fMajHead m, fMajHead_inj m⟩) cpMaj4
        (pWrapMajChain m v (r.compose ⟨fMajSub m, fMajSub_inj m⟩) mid)
theorem pWrapMajChain_counts : ∀ (m : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (r : QRegister (1 + 3 * m) n) (mid : DynamicCircuit Var n),
    (pWrapMajChain m v r mid).count .T = 4 * m + mid.count .T ∧
    (pWrapMajChain m v r mid).count .TOFF = mid.count .TOFF
  | 0, _, _, _, _, mid => ⟨by simp [pWrapMajChain], rfl⟩
  | m + 1, _, _, v, r, mid => by
      obtain ⟨ihT, ihF⟩ := pWrapMajChain_counts m v (r.compose ⟨fMajSub m, _⟩) mid
      obtain ⟨wT, wF⟩ := counts_wrapDynOnReg v (r.compose ⟨fMajHead m, _⟩) cpMaj4 _
      exact ⟨by dsimp [pWrapMajChain]; rw [wT, cpMaj4_numAnd, ihT]; omega, wF.trans ihF⟩
theorem pWrapMajChain_dynWires : ∀ (m : ℕ) {Var : Type} {n : ℕ} (P : Wire n → Prop)
    (v : Var) (r : QRegister (1 + 3 * m) n) (mid : DynamicCircuit Var n),
    (∀ u : Fin (1 + 3 * m), P (r u)) → DynWires P mid →
    DynWires P (pWrapMajChain m v r mid)
  | 0, _, _, _, _, _, _, _, hM => hM
  | m + 1, _, _, P, v, r, mid, hP, hM =>
      dynWires_wrapDynOnReg v (r.compose ⟨fMajHead m, fMajHead_inj m⟩)
          (fun u ↦ hP (fMajHead m u)) cpMaj4
        (pWrapMajChain_dynWires m P v (r.compose ⟨fMajSub m, fMajSub_inj m⟩) mid (fun u ↦
            hP (fMajSub m u)) hM)
/-- Loaded inner state of `pWrapMajChain m`. -/
def stMajIn (m : ℕ) {n : ℕ} (r : QRegister (1 + 3 * m) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : BitAssignment n :=
  writeReg (st δ) (rMajOut m r) (fun j ↦
    majCarryBit
      (finBitsVal (fun i : Fin m ↦ st δ (r ⟨1 + i.val, majCh_ltA m i⟩)))
      (finBitsVal (fun i : Fin m ↦ st δ (r ⟨1 + m + i.val, majCh_ltB m i⟩)))
      (st δ (r ⟨0, majCh_lt0 m⟩)).val
      j.val)
/-- Uncomputed post-state of `pWrapMajChain m`. -/
def stMajOut (m : ℕ) {n : ℕ} (r : QRegister (1 + 3 * m) n)
    (st stMid : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
    writeReg (stMid δ) (rMajOut m r) (fun j ↦ st δ (rMajOut m r j))
theorem pWrapMajChain_step : ∀ (m : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (1 + 3 * m) n)
    (mid : DynamicCircuit Var n)
    (st stMid : BitAssignment n → BitAssignment n) (ph₁ ph₂ : BitAssignment n → ZMod 2),
    (∀ (j : Fin m) (δ : BitAssignment n),
      (∀ q : Fin W, δ (rWork q) = 0) → st δ (rMajOut m r j) = 0) →
    (∀ (u : Fin (1 + 3 * m)) (δ : BitAssignment n),
      (∀ q : Fin W, δ (rWork q) = 0) → stMid δ (r u) = stMajIn m r st δ (r u)) →
    SubspaceStep (mkKetOpW rWork (stMajIn m r st) ph₁) (mkKetOpW rWork stMid ph₂) mid →
    SubspaceStep (mkKetOpW rWork st ph₁) (mkKetOpW rWork (stMajOut m r st stMid) ph₂)
      (pWrapMajChain m v r mid)
  | 0, _, _, _, _, _, _, _, rWork, r, _, st, stMid, ph₁, ph₂, _, _, hInner => by
      have h0 (w) : ¬∃ j, rMajOut 0 r j = w := fun ⟨j, _⟩ ↦ Fin.elim0 j
      rwa [show stMajIn 0 r st = st from funext fun _ ↦ funext fun w ↦
          writeReg_apply_of_not_mem _ _ _ w (h0 w),
        show stMid = stMajOut 0 r st stMid from funext fun _ ↦ funext fun w ↦
            (writeReg_apply_of_not_mem _ _ _ w (h0 w)).symm] at hInner
  | m + 1, _, _, _, W, n, _, v, rWork, r, mid, st, stMid, ph₁, ph₂, hCln, hFix, hInner => by
      let rHead := r.compose ⟨fMajHead m, fMajHead_inj m⟩
      let rSub := r.compose ⟨fMajSub m, fMajSub_inj m⟩
      let st1 (δ) := stepCB rHead cpMaj4.fwdBits (st δ)
      have hNeH3 {i} (hi : i < 1 + 3 * (m + 1)) (h : i ≠ 3 + 2 * m) : r ⟨i, hi⟩ ≠ rHead w4_3 :=
        fun e ↦ h (congrArg Fin.val (r.wires.injective e))
      have hSubBit {f1 f2 : Fin m → ℕ} (hf1 : ∀ i, f1 i < 1 + 3 * m)
          (hf2 : ∀ i, f2 i < 1 + 3 * (m + 1)) (hEq : ∀ i, idxMajSub m ⟨f1 i, hf1 i⟩ = f2 i)
          (hNe : ∀ i, f2 i ≠ 3 + 2 * m) (δ) :
          finBitsVal (fun i ↦ st1 δ (rSub ⟨f1 i, hf1 i⟩)) =
            finBitsVal (fun i ↦ st δ (r ⟨f2 i, hf2 i⟩)) :=
        congrArg finBitsVal (funext fun i ↦ (congrArg (st1 δ) (congrArg r.wires
          (Fin.ext (hEq i)))).trans (stepCB_cpMaj4_not rHead (st δ) (hNeH3 (hf2 i) (hNe i))))
      have hHead3Eq : rHead w4_3 = rMajOut (m + 1) r ⟨0, Nat.zero_lt_succ m⟩ :=
        congrArg r.wires (Fin.ext (by dsimp [fMajHead, idxMajHead, fMajOut, w4_3]; omega))
      have hSubOutEq (j : Fin m) : rMajOut m rSub j = rMajOut (m + 1) r j.succ :=
        congrArg r.wires (Fin.ext (by
          cases j with | mk _ _ =>
            dsimp [fMajSub, idxMajSub, fMajOut, Fin.val_succ]; split_ifs <;> omega))
      have hNotOut (w) (hw3 : w ≠ rHead w4_3) (hmSub : ¬∃ j, rMajOut m rSub j = w) :
          ¬∃ k, rMajOut (m + 1) r k = w := fun ⟨k, hk⟩ ↦ (Fin.eq_zero_or_eq_succ k).elim
        (fun h0 ↦ hw3 (hk.symm.trans ((congrArg (rMajOut (m + 1) r) h0).trans hHead3Eq.symm)))
        fun ⟨j, hj⟩ ↦ hmSub ⟨j, (hSubOutEq j).trans (hj ▸ hk)⟩
      have hHeadNotSub (u : Wire 4) : ¬∃ j : Fin m, rMajOut m rSub j = rHead u := fun ⟨j, hj⟩ ↦ by
        have hv := congrArg Fin.val (r.wires.injective hj.symm)
        cases u with | mk _ _ => cases j with | mk _ _ =>
          dsimp [fMajHead, idxMajHead, fMajSub, idxMajSub, fMajOut] at hv; split_ifs at hv <;>
            omega
      let wA0 := r ⟨1 + (0 : Fin (m + 1)).val, majCh_ltA (m + 1) 0⟩
      let wB0 := r ⟨1 + (m + 1) + (0 : Fin (m + 1)).val, majCh_ltB (m + 1) 0⟩
      have hSt1Head3 (δ) (hz : ∀ q : Fin W, δ (rWork q) = 0) :
          st1 δ (rHead w4_3) = (st δ wA0 + st δ (r ⟨0, majCh_lt0 _⟩)) *
            (st δ wB0 + st δ (r ⟨0, majCh_lt0 _⟩)) + st δ (r ⟨0, majCh_lt0 _⟩) := by
        dsimp only [st1]
        rw [stepCB_cpMaj4_anc, hHead3Eq, hCln ⟨0, Nat.zero_lt_succ m⟩ δ hz, zero_add,
          show rHead w4_0 = wA0 from rfl, show rHead w4_2 = r ⟨0, majCh_lt0 _⟩ from rfl,
          show rHead w4_1 = wB0 from
            congrArg r.wires (Fin.ext (by dsimp [fMajHead, idxMajHead, w4_1]; omega))]
      have hInEq (δ) (hz : ∀ q : Fin W, δ (rWork q) = 0) :
          stMajIn m rSub st1 δ = stMajIn (m + 1) r st δ := funext fun w ↦ by
        have hVA := finBitsVal_succ fun i ↦ st δ (r ⟨1 + i.val, majCh_ltA (m + 1) i⟩)
        have hVB := finBitsVal_succ fun i ↦ st δ (r ⟨1 + (m + 1) + i.val, majCh_ltB _ i⟩)
        dsimp only [stMajIn]
        by_cases hmSub : ∃ j : Fin m, rMajOut m rSub j = w
        · obtain ⟨j, rfl⟩ := hmSub
          rw [writeReg_apply_reg, hSubOutEq j, writeReg_apply_reg,
            hSubBit (majCh_ltA m) (fun i ↦ majCh_ltA (m + 1) i.succ)
              (fun ⟨_, _⟩ ↦ by dsimp [idxMajSub, Fin.val_succ]; split_ifs <;> omega)
              (fun ⟨_, _⟩ ↦ by dsimp [Fin.val_succ]; omega) δ,
            hSubBit (majCh_ltB m) (fun i ↦ majCh_ltB (m + 1) i.succ)
              (fun ⟨_, _⟩ ↦ by dsimp [idxMajSub, Fin.val_succ]; split_ifs <;> omega)
              (fun ⟨_, _⟩ ↦ by dsimp [Fin.val_succ]; omega) δ,
            show rSub ⟨0, majCh_lt0 m⟩ = rHead w4_3 from rfl, hSt1Head3 δ hz, hVA, hVB,
            Fin.val_succ]
          exact (majCarryBit_succ_step _ _ _ _ _ j.val).symm
        · rw [writeReg_apply_of_not_mem _ _ _ w hmSub]
          rcases eq_or_ne w (rHead w4_3) with rfl | hw3
          · rw [hSt1Head3 δ hz, hHead3Eq, writeReg_apply_reg, hVA, hVB]
            exact (majCarryBit_zero_step _ _ _ _ _).symm
          · rw [show st1 δ w = st δ w from stepCB_cpMaj4_not rHead (st δ) hw3,
              writeReg_apply_of_not_mem _ _ _ w (hNotOut w hw3 hmSub)]
      have hSubStep := pWrapMajChain_step m v rWork rSub mid st1 stMid ph₁ ph₂
        (fun j δ hz ↦ (congrArg (st1 δ) (hSubOutEq j)).trans ((stepCB_cpMaj4_not rHead (st δ)
          (hNeH3 (majCh_ltOut (m + 1) j.succ) (by dsimp [Fin.val_succ]; omega))).trans
            (hCln j.succ δ hz)))
        (fun u δ hz ↦ by rw [show rSub u = r (fMajSub m u) from rfl, hFix _ δ hz, ← hInEq δ hz])
        (by rwa [mkKetOpW_congr rWork hInEq fun _ _ ↦ rfl])
      let stMidFix (δ) := writeReg (stMajOut m rSub st1 stMid δ) rHead fun u ↦ st1 δ (rHead u)
      have hMidFixEq (δ) (hz : ∀ q : Fin W, δ (rWork q) = 0) : stMajOut m rSub st1 stMid δ =
          stMidFix δ :=
        funext fun w ↦ if hmH : ∃ u : Wire 4, rHead u = w then by
          obtain ⟨u, rfl⟩ := hmH
          dsimp only [stMidFix, stMajOut]
          rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ (hHeadNotSub u),
            show rHead u = r (fMajHead m u) from rfl, hFix _ δ hz, ← hInEq δ hz]
          exact writeReg_apply_of_not_mem _ _ _ _ (hHeadNotSub u)
        else (writeReg_apply_of_not_mem _ _ _ w hmH).symm
      refine subspaceStep_of_eq_post (wrapCpMaj4 v rWork rHead (pWrapMajChain m v rSub mid) st
          stMidFix
        ph₁ ph₂ ph₂ (fun δ hz ↦ hHead3Eq ▸ hCln ⟨0, Nat.zero_lt_succ m⟩ δ hz)
        (fun u _ ↦ writeReg_apply_reg _ _ _ u) (fun _ _ ↦ rfl)
        (subspaceStep_of_eq_post hSubStep (mkKetOpW_congr rWork hMidFixEq fun _ _ ↦ rfl)))
        (mkKetOpW_congr rWork (fun δ hz ↦ funext fun w ↦ ?_) fun _ _ ↦ rfl)
      rcases eq_or_ne w (rHead w4_3) with rfl | hw3
      · rw [leg_if_pos rfl, hHead3Eq, show stMajOut (m + 1) r st stMid δ _ =
            _ from writeReg_apply_reg _ _ _ _]
      · rw [leg_if_neg hw3, ← hMidFixEq δ hz]
        dsimp only [stMajOut]
        if hmSub : ∃ j : Fin m, rMajOut m rSub j = w then
          obtain ⟨j, rfl⟩ := hmSub
          rw [writeReg_apply_reg, hSubOutEq j, writeReg_apply_reg, ← hSubOutEq j]
          exact stepCB_cpMaj4_not rHead (st δ) hw3
        else rw [writeReg_apply_of_not_mem _ _ _ w hmSub,
            writeReg_apply_of_not_mem _ _ _ w (hNotOut w hw3 hmSub)]
end QuantumComputation.Specs.PhotochemistrySolution.MidOWCore
end
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances

section
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k
open Operator QProg Matrix HermitianMat PhotochemistrySolution.XMeasUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open scoped ComplexOrder MatrixOrder Circuit.Notation
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (fanoutXorBits
    fanoutXorBits_of_ne_tgt specFanoutCopyCirc specFanoutCopyCirc_mulVec_ket)
/-- Operator `U` writes only inside `W` and never reads wires in `O`. -/
def LocalKetOp {n : ℕ} (W O : Wire n → Prop) (U : Operator (2 ^ n))
    (F : BitAssignment n → BitAssignment n) : Prop :=
    (∀ β, U.mulVec (ket β) = ket (F β)) ∧ (∀ β w, ¬ W w → F β w = β w) ∧
    (∀ β₁ β₂, (∀ w, ¬ O w → β₁ w = β₂ w) → ∀ w, W w → F β₁ w = F β₂ w)
open scoped Classical in
theorem localKetOp_comm {n : ℕ} {W₁ W₂ : Wire n → Prop} (hDisj : ∀ w, W₁ w → W₂ w → False)
    {U₁ U₂ : Operator (2 ^ n)}
    {F₁ F₂ : BitAssignment n → BitAssignment n} (h₁ : LocalKetOp W₁ W₂ U₁ F₁)
        (h₂ : LocalKetOp W₂ W₁ U₂ F₂) : U₁ * U₂ = U₂ * U₁ := by
  refine matrix_ext_ket fun β ↦ ?_
  simp only [← Matrix.mulVec_mulVec, h₁.1, h₂.1]
  refine congrArg ket (funext fun q ↦ if hq1 : W₁ q then ?_ else if hq2 : W₂ q then ?_ else ?_)
  · rw [h₁.2.2 (F₂ β) β (fun w hw2 ↦ h₂.2.1 β w hw2) q hq1, h₂.2.1 (F₁ β) q (fun h ↦ hDisj q hq1 h)]
  · rw [h₁.2.1 (F₂ β) q hq1, (h₂.2.2 (F₁ β) β (fun w hw1 ↦ h₁.2.1 β w hw1) q hq2).symm]
  · rw [h₁.2.1 (F₂ β) q hq1, h₂.2.1 β q hq2, h₂.2.1 (F₁ β) q hq2, h₁.2.1 β q hq1]
open scoped Classical in
theorem localKetOp_comm_H {n : ℕ} {W O : Wire n → Prop} {q : Wire n} (hqO : O q) (hqW : ¬ W q)
    {U : Operator (2 ^ n)} {F : BitAssignment n → BitAssignment n} (hU : LocalKetOp W O U F) :
    U * (Circuit.H q).eval.1 = (Circuit.H q).eval.1 * U := by
  refine matrix_ext_ket fun β ↦ ?_
  have hFupd (v : ZMod 2) : F (Function.update β q v) = Function.update (F β) q v := funext fun w ↦
    if hwq : w =
        q then by subst hwq; rw [hU.2.1 _ _ hqW, Function.update_self, Function.update_self]
    else if hwW :
        W w then
        by rw [Function.update_of_ne hwq]; exact hU.2.2 _ β (fun u huO ↦
             Function.update_of_ne (by rintro rfl; exact huO hqO) _ _) w hwW
    else by rw [Function.update_of_ne hwq, hU.2.1 _ w hwW, Function.update_of_ne hwq,
              hU.2.1 β w hwW]
  simp only [← Matrix.mulVec_mulVec, ket_H, hU.1, Matrix.mulVec_smul, Matrix.mulVec_add, hFupd 0,
      hFupd 1, hU.2.1 β q hqW]
theorem comm_H_ne {n : ℕ} {q₁ q₂ : Wire n} (hne : q₁ ≠ q₂) : (Circuit.H q₁).eval.1 *
    (Circuit.H q₂).eval.1 = (Circuit.H q₂).eval.1 * (Circuit.H q₁).eval.1 := by
  refine matrix_ext_ket fun β ↦ ?_
  simp only [← Matrix.mulVec_mulVec, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
      Function.update_of_ne hne, Function.update_of_ne hne.symm, smul_add, smul_smul,
      (Function.update_comm hne _ _ _)]
  simp only [mul_comm, mul_left_comm]
  abel
theorem planeSwap1_localKetOp {M D n : ℕ} (r : PlaneReg M D n) (qB : Wire n) (wC : Fin M → Wire n)
    (hbc : ∀ p, qB ≠ wC p) (hbt : ∀ p, qB ≠ pSys r p) (hct : ∀ p, wC p ≠ pSys r p)
        (hqB : PlaneModSet r qB)
    (O : Wire n → Prop) (hO_disj : ∀ u, PlaneModSet r u → ¬ O u) (hO_C : ∀ p, ¬ O (wC p)) :
    LocalKetOp (PlaneModSet r) O (portSwap1Circ M qB wC (pSys r) hbc hbt hct).eval.1 (portSwap1Bits
        M qB wC (pSys r)) := by
  have mSys (p : Fin M) {u} (e : u = pSys r p) : PlaneModSet r u := .inr (.inr (.inr (.inr ⟨p, e⟩)))
  refine ⟨portSwap1Circ_mulVec_ket M qB wC (pSys r) hbc hbt hct,
    fun β w hw ↦ (Nat.rec (motive := fun k ↦ ∀ hk : k ≤ M, portSwap1Bits k qB
        (fun p ↦ wC ⟨p.1, p.2.trans_le hk⟩) (fun p ↦ pSys r ⟨p.1, p.2.trans_le hk⟩) β w = β w)
      (fun _ ↦ rfl) (fun q ih hk ↦ by
        simp [portSwap1Bits, Fin.val_castSucc, Fin.val_last, Function.update_of_ne fun e ↦
            hw (mSys ⟨q, hk⟩ e),
          Function.update_of_ne (show w ≠ qB from fun e ↦ hw (e ▸ hqB)),
              ih (Nat.le_of_succ_le hk)]) M) le_rfl,
    fun β₁ β₂ hEq w hwW ↦ (Nat.rec (motive := fun k ↦ ∀ (hk : k ≤ M) (u : Wire n), ¬ O u →
        portSwap1Bits k qB (fun p ↦ wC ⟨p.1, p.2.trans_le hk⟩)
            (fun p ↦ pSys r ⟨p.1, p.2.trans_le hk⟩) β₁ u =
        portSwap1Bits k qB (fun p ↦ wC ⟨p.1, p.2.trans_le hk⟩)
            (fun p ↦ pSys r ⟨p.1, p.2.trans_le hk⟩) β₂ u)
      (fun _ ↦ hEq) (fun q ih hq u hu ↦ by
        have ih' := ih (Nat.le_of_succ_le hq)
        simp [portSwap1Bits, Fin.val_castSucc, Fin.val_last, Function.update_apply,
            ih' _ (hO_C ⟨q, hq⟩),
          ih' _ (hO_disj _ (mSys ⟨q, hq⟩ rfl)), ih' qB (hO_disj _ hqB),
              ih' u hu]) M) le_rfl w (hO_disj w hwW)⟩
theorem planeFanout1_localKetOp {M D n : ℕ} (r : PlaneReg M D n) (qS : Wire n) (wC : Fin M → Wire n)
    (hsc : ∀ p, qS ≠ wC p) (hst : ∀ p, qS ≠ pSys r p) (hct : ∀ p, wC p ≠ pSys r p)
        (hqS : PlaneModSet r qS)
    (O : Wire n → Prop) (hO_disj : ∀ u, PlaneModSet r u → ¬ O u) (hO_C : ∀ p, ¬ O (wC p)) :
    LocalKetOp (PlaneModSet r) O (specFanoutCopyCirc M qS wC (pSys r) hsc hst hct).eval.1 (fun β ↦
        if β qS = 0 then β else fanoutXorBits M wC (pSys r) β) := by
  have mSys (p : Fin M) {u} (e : u = pSys r p) : PlaneModSet r u := .inr (.inr (.inr (.inr ⟨p, e⟩)))
  refine ⟨specFanoutCopyCirc_mulVec_ket M qS wC (pSys r) hsc hst hct,
    fun β w hw ↦ if h : β qS = 0 then by simp [h] else by
      simpa [h] using fanoutXorBits_of_ne_tgt M wC (pSys r) β w fun p e ↦ hw (mSys p e),
    fun β₁ β₂ hEq w hwW ↦ by
      dsimp only
      rw [hEq qS (hO_disj qS hqS)]
      if h0 : β₂ qS = 0 then simp [h0, hEq w (hO_disj w hwW)]
      else simpa [h0] using (Nat.rec (motive := fun k ↦ ∀ (hk : k ≤ M) (u : Wire n), ¬ O u →
          fanoutXorBits k (fun p ↦ wC ⟨p.1, p.2.trans_le hk⟩)
              (fun p ↦ pSys r ⟨p.1, p.2.trans_le hk⟩) β₁ u =
          fanoutXorBits k (fun p ↦ wC ⟨p.1, p.2.trans_le hk⟩)
              (fun p ↦ pSys r ⟨p.1, p.2.trans_le hk⟩) β₂ u)
        (fun _ ↦ hEq) (fun q ih hq u hu ↦ by
          have ih' := ih (Nat.le_of_succ_le hq)
          simp [fanoutXorBits, Fin.val_castSucc, Fin.val_last, Function.update_apply,
            ih' _ (hO_C ⟨q, hq⟩), ih' _ (hO_disj _ (mSys ⟨q, hq⟩ rfl)),
                ih' u hu]) M) le_rfl w (hO_disj w hwW)⟩
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage12Instances
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCoreFused
open PhotochemistrySolution.RouterSelectWiringB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem ifp {c : Prop} [inst : Decidable c] (h : c) {α : Sort*}
    {a b : α} : (if c then a else b) = a := by
  cases inst with | isFalse hn => exact absurd h hn | isTrue _ => rfl
theorem cleanWorkStep_of_subreg {Var : Type} [Fintype Var] [DecidableEq Var] {w₁ w₂ n : ℕ}
    [NeZero (2 ^ n)]
    (r₁ : QRegister w₁ n) (r₂ : QRegister w₂ n) (hSub : ∀ u : Fin w₁, ∃ k : Fin w₂, r₁ u = r₂ k)
    (U : Unitary (2 ^ n)) (p : DynamicCircuit Var n) (hComm : U.1 * r₂.basisOutcomeProjector 0 =
        r₂.basisOutcomeProjector 0 * U.1)
    (h1 : CleanWorkStep r₁ U p) : CleanWorkStep r₂ U p :=
  PhotochemistrySolution.XMeasChunkQromUnld.cleanWorkStep_of_subspaceStep_xmeas r₂ U p hComm
    (SelectCsa64ProvSpec.SubspaceStep.of_clean h1 (SelectCsa64ProvSpec.proj_absorb_gen r₂ r₁
        hSub))
variable {W : ℕ}
abbrev rIdGenW : QRegister W W := QRegister.block 0 W (Nat.zero_add W).le
theorem rIdGenW_apply (j : Fin W) : (rIdGenW (W := W)) j = j := Fin.ext (Nat.zero_add j.val)
end QuantumComputation.Specs.PhotochemistrySolution.Stage12Instances

-- Zero-floor ancilla offset witness (`0 <= wIn <= 1132`).
namespace QuantumComputation.Specs.PhotochemistrySolution.ProviderZeroFloor
theorem hOff65Zero : 65 ≤ 65 := le_rfl
end QuantumComputation.Specs.PhotochemistrySolution.ProviderZeroFloor

-- 1,493-wire Stage-1 scratch register rScrCompact1493 ([5680..5712] union [5755..7214]),
-- rStage1CompactGen (W <= 442 + wIn), and Stage-1 compact oracle contract
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCoreFused
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Instances
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
-- Section 1: Generic Subregister Equivariance for Multi-Pass `mapCPSW` Oracles
def scrCompact1493WireFn (k : Fin 1493) : Wire dLayout :=
  if _ : k.val < 33 then rScrLayout ⟨30 + k.val, by dsimp [scrLLayout]; omega⟩
  else rScrLayout ⟨105 + (k.val - 33), by dsimp [scrLLayout]; omega⟩
theorem val_scrCompact1493WireFn (k : Fin 1493) : (scrCompact1493WireFn k).val = if k.val <
    33 then 5680 + k.val else 5755 + (k.val - 33) := by
  unfold scrCompact1493WireFn; split_ifs <;> simp only [val_rScrLayout] <;> omega
/--
Clean `1,493`-wire scratch register `[5680..5712] ∪ [5755..7214]` inside `rScrLayout`,
strictly extending `rScrAfterOut1460` by the `33` active scratch wires `[5680..5712]`.
-/
def rScrCompact1493 : QRegister 1493 dLayout :=
  ⟨⟨scrCompact1493WireFn, fun a b h ↦ by
    have hv := congrArg Fin.val h; rw [val_scrCompact1493WireFn, val_scrCompact1493WireFn] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)⟩⟩
theorem val_rScrCompact1493 (k : Fin 1493) : (rScrCompact1493 k).val = if k.val < 33 then 5680 +
    k.val else 5755 + (k.val - 33) := val_scrCompact1493WireFn k
theorem rScrCompact1493_sub_scr (k : Fin 1493) :
    ∃ m : Fin scrLLayout, rScrCompact1493 k = rScrLayout m := by
  change ∃ m, scrCompact1493WireFn k = _
  unfold scrCompact1493WireFn; split_ifs <;> exact ⟨_, rfl⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open Operator QProg Matrix Circuit Qubit PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.Stage12Instances PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.ProviderCoreFused PhotochemistrySolution.Stage1Opt41TwoWrap
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
structure Stage1ZeroNEremLayout (wIn : ℕ) (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) where
  tStage1 : ℕ
  uLocal : Unitary (2 ^ dLayout)
  fwdAmb : ∀ {Var : Type} {n : ℕ}, Var → QRegister dLayout n → DynamicCircuit Var n
  revAmb : ∀ {Var : Type} {n : ℕ}, Var → QRegister dLayout n → DynamicCircuit Var n
  step_and_counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rTot : QRegister dLayout n),
    CleanWorkStep (rTot.compose rScrCompact1493) (rTot.embedUnitary uLocal) (fwdAmb v rTot) ∧
    CleanWorkStep (rTot.compose rScrCompact1493)
      ((rTot.embedUnitary uLocal)⁻¹) (revAmb v rTot) ∧
    (fwdAmb v rTot).count .T + (revAmb v rTot).count .T = tStage1 ∧
    (fwdAmb v rTot).count .TOFF = 0 ∧ (revAmb v rTot).count .TOFF = 0
  comm_off : ∀ {k : ℕ} (r : QRegister k (systemQubits_frozen + ancWOfScr scrWLayout))
    (M : Operator (2 ^ k)),
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
        (scrSubLGen hpLayout) r →
    Commute uLocal.1 (r.embedMatrix M)
  dynWires_active_wIn : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rTot : QRegister dLayout n),
    (∀ w : Wire dLayout, ActiveLayoutFusedOf wIn w → S (rTot w)) →
    DynWires S (fwdAmb v rTot) ∧ DynWires S (revAmb v rTot)
  ket_of_clean : ∀ (c : Fin (2 ^ 41)) (δ : BitAssignment dLayout),
    (∀ k : Fin 41, δ (rOuter41Layout k) = if c.val.testBit k.val then 1 else 0) →
    (∀ j : Fin 40, δ (rOut40Layout j) = 0) →
    (∀ k : Fin 1493, δ (rScrCompact1493 k) = 0) →
    uLocal.1.mulVec (PhotochemistrySolution.KinB.ket δ) =
      PhotochemistrySolution.KinB.ket
        (DynCircExt.writeReg δ rOut40Layout
          (fun j ↦ if (zeroNEremOutMask (decodeCoin c)).testBit j.val then 1 else 0))
/--
Width-`W` Stage-1 oracle contract (`81 ≤ W`, coin on `0..40`, XOR output on `41..80`, clean
scratch on `81..W-1`) independent of target mask.
-/
structure Stage1ZeroNEremOracleGen (tOneWay W : ℕ) (h81 : 81 ≤ W) where
  u : ∀ {n : ℕ} [NeZero (2 ^ n)], QRegister W n → Unitary (2 ^ n)
  fwdDyn : ∀ {Var : Type} {n : ℕ}, Var → QRegister W n → DynamicCircuit Var n
  revDyn : ∀ {Var : Type} {n : ℕ}, Var → QRegister W n → DynamicCircuit Var n
  cleanWorkStep : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (r : QRegister W n),
    CleanWorkStep (r.compose (QRegister.block 81 (W - 81) (Nat.add_sub_of_le h81).le))
      (u r) (fwdDyn v r) ∧
    CleanWorkStep (r.compose (QRegister.block 81 (W - 81) (Nat.add_sub_of_le h81).le))
      ((u r)⁻¹) (revDyn v r)
  counts : ∀ {Var : Type} {n : ℕ} (v : Var) (r : QRegister W n),
    (fwdDyn v r).count .T = tOneWay ∧ (fwdDyn v r).count .TOFF = 0 ∧
    (revDyn v r).count .T = tOneWay ∧ (revDyn v r).count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} (S : Wire n → Prop) (v : Var) (r : QRegister W n),
    (∀ j : Fin W, S (r j)) →
    DynWires S (fwdDyn v r) ∧ DynWires S (revDyn v r)
theorem embedUnitary_zeroNErem_of_xorOut40 {tOneWay W : ℕ} (h81 : 81 ≤ W)
    (o : Stage1ZeroNEremOracleGen tOneWay W h81)
    (f : BitAssignment W → Fin 40 → ZMod 2)
    (hKet : ∀ {n : ℕ} [NeZero (2 ^ n)] (r : QRegister W n) (β : BitAssignment n),
      (o.u r).1.mulVec (PhotochemistrySolution.KinB.ket β) =
        PhotochemistrySolution.KinB.ket
          (xorDstK (r.compose (QRegister.block 41 40 h81))
            (f (fun k ↦ β (r k))) 40 Nat.le.refl β))
    {n : ℕ} [NeZero (2 ^ n)] (r : QRegister W n) :
    let _ : NeZero (2 ^ W) := ⟨pow_ne_zero W two_ne_zero⟩
    r.embedUnitary (o.u rIdGenW) = o.u r := by
  let _ : NeZero (2 ^ W) := ⟨pow_ne_zero W two_ne_zero⟩
  let b40 := QRegister.block 41 40 h81
  refine Subtype.ext (embedMatrix_eq_of_ketMap r (o.u rIdGenW).1 (o.u r).1 (fun _ ↦ 1)
    (fun α ↦ xorDstK (rIdGenW.compose b40) (f α) 40 le_rfl α)
    (fun α ↦
        by rw [one_smul, hKet rIdGenW α, show (fun k ↦ α (rIdGenW k)) = α from funext fun k ↦
             congrArg α (rIdGenW_apply k)])
    fun β ↦ ?_)
  rw [one_smul, hKet r β]
  refine congrArg _ (funext fun w ↦ ?_)
  if hw : w ∈ Set.range r.wires then
    rcases hw with ⟨u, rfl⟩
    rw [DynCircExt.writeReg_apply_reg]
    if hu : 41 ≤ u.val ∧ u.val < 81 then
      let j : Fin 40 := ⟨u.val - 41, by omega⟩
      have hub : u = b40 j :=
          Fin.ext ((QRegister.block_apply_val 41 40 h81 j).trans (Nat.add_sub_of_le hu.1)).symm
      have huI : u = (rIdGenW.compose b40) j := hub.trans (rIdGenW_apply (b40 j)).symm
      rw [show r u = (r.compose b40) j from congrArg r hub, xorDstK_dst, ifp j.isLt, huI,
          xorDstK_dst, ifp j.isLt]
      exact congrArg (· + _) (congrArg β (congrArg r (hub.symm.trans huI)))
    else
      have hne (j) : u ≠ b40 j := fun e ↦
          hu (by have := (congrArg Fin.val e).trans (QRegister.block_apply_val _ _ _ j); omega)
      rw [xorDstK_outside _ _ _ _ _ fun j e ↦ hne j (r.wires.injective e),
        xorDstK_outside _ _ _ _ _ fun j e ↦ hne j (e.trans (rIdGenW_apply (b40 j)))]
  else rw [xorDstK_outside _ _ _ _ _ fun _ e ↦ hw ⟨_, e.symm⟩,
      DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hw]
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectSymDyn
  PhotochemistrySolution.SelectSymDynInstance
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ProviderCoreFused
  PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.InPlaceModAdd PhotochemistrySolution.Stage4Kin14Scb
  PhotochemistrySolution.Stage4KinFull
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor (byteOfBits)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
theorem fin41_lt_mLayout (k : Fin 41) : k.val < mLayout + 2 := by
  have := k.isLt; dsimp [mLayout]; omega
theorem add41_lt_mLayout (k : Fin 41) : 41 + k.val < mLayout + 2 := by
  have := k.isLt; dsimp [mLayout]; omega
theorem sub41_lt41 {i : Fin (mLayout + 2)} (h : ¬ i.val < 41) : i.val - 41 < 41 := by
  have := i.isLt; dsimp [mLayout] at *; omega
theorem sum_fin_pow2_lt : ∀ (n : ℕ) (f : Fin n → Bool),
    (∑ k : Fin n, if f k then 2 ^ k.val else 0) < 2 ^ n
  | 0, _ => by simp
  | n + 1, f => by
      have := sum_fin_pow2_lt n fun k ↦ f k.castSucc
      rw [Fin.sum_univ_castSucc]; dsimp at *; cases f (.last n) <;> simp at * <;> omega
theorem testBit_sum_fin_pow2 : ∀ (n : ℕ) (f : Fin n → Bool) (j : ℕ),
    (∑ k : Fin n, if f k then 2 ^ k.val else 0).testBit j =
      if hj : j < n then f ⟨j, hj⟩ else false
  | 0, _, _ => by simp
  | n + 1, f, j => by
      rw [Fin.sum_univ_castSucc, Nat.add_comm]; dsimp only [Fin.val_last, Fin.val_castSucc]
      rw [show (if f (.last n) then 2 ^ n else 0) = 2 ^ n *
          if f (.last n) then 1 else 0 by cases f (.last n) <;> simp,
        Nat.testBit_two_pow_mul_add _ (sum_fin_pow2_lt n fun k ↦ f k.castSucc)]
      if hj : j < n then simp [hj, show j < n + 1 by omega, testBit_sum_fin_pow2 n]
      else
        rcases eq_or_ne j n with rfl | hjeq
        · cases hb : f ⟨j, j.lt_succ_self⟩ <;> simp [Fin.last, hb]
        · simpa [hj, show ¬ j < n + 1 by omega] using Nat.testBit_lt_two_pow
            (lt_of_lt_of_le (by cases f (.last n) <;> decide) (Nat.pow_le_pow_right (by omega)
                (by omega : 1 ≤ j - n)))
/-- Outer `41`-bit coin index read from `BitAssignment (mLayout + 2)`. -/
def outerCoinOf82 (γ : BitAssignment (mLayout + 2)) : Fin (2 ^ 41) :=
  ⟨∑ k : Fin 41, if (γ ⟨k.val, fin41_lt_mLayout k⟩ == 1) then 2 ^ k.val else 0,
    sum_fin_pow2_lt 41 (fun k ↦ γ ⟨k.val, fin41_lt_mLayout k⟩ == 1)⟩
/-- Inner `41`-bit coin assignment read from `BitAssignment (mLayout + 2)`. -/
def innerBitsOf82 (γ : BitAssignment (mLayout + 2)) : BitAssignment 41 :=
  fun k ↦ γ ⟨41 + k.val, add41_lt_mLayout k⟩
/-- Pack outer `41`-bit coin index `c` and inner `41`-bit assignment `z` into `mLayout + 2` bits. -/
def pack82 (c : Fin (2 ^ 41)) (z : BitAssignment 41) : BitAssignment (mLayout + 2) :=
  fun i ↦ if h : i.val < 41 then (if c.val.testBit i.val then 1 else 0)
    else z ⟨i.val - 41, sub41_lt41 h⟩
/-- Bit vector encoding `c : Fin (2 ^ 41)` on `rOuter41Layout`. -/
def cBits41 (c : Fin (2 ^ 41)) : BitAssignment 41 := fun k ↦ if c.val.testBit k.val then 1 else 0
theorem pack82_apply_lt (c : Fin (2 ^ 41)) (z : BitAssignment 41) (k : Fin 41) :
    pack82 c z ⟨k.val, fin41_lt_mLayout k⟩ = if c.val.testBit k.val then 1 else 0 := by
      dsimp only [pack82]; exact dite_eq_left k.isLt
theorem outer_pack82 (c : Fin (2 ^ 41)) (z : BitAssignment 41) : outerCoinOf82 (pack82 c z) =
    c :=
  Fin.ext <| Nat.eq_of_testBit_eq fun j ↦ by
    unfold outerCoinOf82; dsimp only; rw [testBit_sum_fin_pow2 41]
    exact if hj : j <
        41 then by rw [dite_eq_left hj, pack82_apply_lt]; cases c.val.testBit j <;> rfl
      else (dite_eq_right hj).trans (Nat.testBit_lt_two_pow (lt_of_lt_of_le c.isLt
                                   (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hj)))).symm
theorem inner_pack82 (c : Fin (2 ^ 41)) (z : BitAssignment 41) : innerBitsOf82 (pack82 c z) =
    z :=
  funext fun k ↦
      (dite_eq_right (by omega : ¬ 41 + k.val < 41)).trans (congrArg z
      (Fin.ext (by dsimp; omega)))
theorem pack82_left_inv (γ : BitAssignment (mLayout + 2)) : pack82 (outerCoinOf82 γ)
    (innerBitsOf82 γ) = γ :=
  funext fun i ↦ if hi : i.val < 41 then by
    unfold pack82 outerCoinOf82; dsimp only
    rw [dite_eq_left hi, testBit_sum_fin_pow2 41, dite_eq_left hi]
    rcases DynCircExt.bit_cases (γ i) with h | h <;> rw [h] <;> rfl
  else (dite_eq_right hi).trans (congrArg γ (Fin.ext (by dsimp; omega)))
/-- Bijection `Fin (2 ^ 41) × BitAssignment 41 ≃ BitAssignment (mLayout + 2)`. -/
def lcu82Equiv : Fin (2 ^ 41) × BitAssignment 41 ≃ BitAssignment (mLayout + 2) where
  toFun p := pack82 p.1 p.2
  invFun γ := (outerCoinOf82 γ, innerBitsOf82 γ)
  left_inv p := Prod.ext (outer_pack82 p.1 p.2) (inner_pack82 p.1 p.2)
  right_inv := pack82_left_inv
theorem sum_bitAssignment82 {M : Type*} [AddCommMonoid M] (f : BitAssignment (mLayout + 2) → M) :
    (∑ γ : BitAssignment (mLayout + 2), f γ) = ∑ c : Fin (2 ^ 41), ∑ z : BitAssignment 41,
        f (pack82 c z) := by
  rw [← Equiv.sum_comp lcu82Equiv, Fintype.sum_prod_type]; rfl
theorem writeReg_pack82_eq_outer_inner (β : BitAssignment dLayout) (c : Fin (2 ^ 41))
    (z : BitAssignment 41) :
    DynCircExt.writeReg β rLcu82Layout (pack82 c z) =
        DynCircExt.writeReg (DynCircExt.writeReg β rOuter41Layout (cBits41 c))
        rInner41Layout z :=
  funext fun w ↦ by
    have eqO (k : Fin 41) : rLcu82Layout ⟨k.val, fin41_lt_mLayout k⟩ = rOuter41Layout k :=
      Fin.ext ((val_rLcu82Layout _).trans (val_rOuter41Layout k).symm)
    have eqI (k : Fin 41) : rLcu82Layout ⟨41 + k.val, add41_lt_mLayout k⟩ = rInner41Layout k :=
      Fin.ext (by rw [val_rLcu82Layout, val_rInner41Layout]; dsimp; omega)
    if hL : w ∈ Set.range rLcu82Layout.wires then
      rcases hL with ⟨i, rfl⟩
      rw [DynCircExt.writeReg_apply_reg]
      if hi : i.val < 41 then
        rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨k, hk⟩ ↦ by
            have :=
                congrArg Fin.val (rLcu82Layout.wires.injective ((eqI k).trans hk));
                dsimp at this; omega,
          (congrArg rLcu82Layout (Fin.ext rfl)).trans (eqO ⟨i.val, hi⟩),
              DynCircExt.writeReg_apply_reg]; exact dite_eq_left hi
      else
        rw [(congrArg rLcu82Layout (Fin.ext (by dsimp; omega))).trans (eqI ⟨i.val - 41,
            sub41_lt41 hi⟩),
          DynCircExt.writeReg_apply_reg]; exact dite_eq_right hi
    else rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hL,
      DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨k, hk⟩ ↦ hL ⟨_, (eqI k).trans hk⟩,
      DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨k, hk⟩ ↦ hL ⟨_, (eqO k).trans hk⟩]
/-- Swap two wires `a, b` in `β : BitAssignment n`. -/
def swapPairBits {n : ℕ} (a b : Wire n) (β : BitAssignment n) : BitAssignment n :=
  Function.update (Function.update β b (β a)) a (β b)
/-- Sequentially swap `m` disjoint pairs `(qB k, wT k)` in `β : BitAssignment n`. -/
def swapVecBits {n : ℕ} : (m : ℕ) → (Fin m → Wire n) → (Fin m → Wire n) →
    BitAssignment n → BitAssignment n
  | 0, _, _, β => β
  | m + 1, qB, wT, β =>
      swapPairBits (qB (Fin.last m)) (wT (Fin.last m))
        (swapVecBits m (fun k ↦ qB k.castSucc) (fun k ↦ wT k.castSucc) β)
theorem swapVecBits_spec {n : ℕ} :
    ∀ (m : ℕ) (qB wT : Fin m → Wire n),
      Function.Injective qB → Function.Injective wT → (∀ j k, qB j ≠ wT k) →
      ∀ β : BitAssignment n,
        (∀ k : Fin m, swapVecBits m qB wT β (qB k) = β (wT k)) ∧
        (∀ k : Fin m, swapVecBits m qB wT β (wT k) = β (qB k)) ∧
        (∀ w : Wire n, (∀ k, w ≠ qB k) → (∀ k, w ≠ wT k) →
          swapVecBits m qB wT β w = β w)
  | 0, _, _, _, _, _, _ => ⟨fun k ↦ Fin.elim0 k, fun k ↦ Fin.elim0 k, fun _ _ _ ↦ rfl⟩
  | m + 1, qB, wT, hqI, htI, hDisj, β => by
      obtain ⟨hQ, hT, hO⟩ := swapVecBits_spec m (fun k ↦ qB k.castSucc) (fun k ↦ wT k.castSucc)
        (fun _ _ e ↦ Fin.castSucc_inj.mp (hqI e)) (fun _ _ e ↦ Fin.castSucc_inj.mp (htI e))
        (fun j k ↦ hDisj j.castSucc k.castSucc) β
      have uNe {w a b} (ha : w ≠ a) (hb : w ≠ b) (ξ : BitAssignment n) : swapPairBits a b ξ w =
          ξ w := by
        dsimp only [swapPairBits]; rw [Function.update_of_ne ha, Function.update_of_ne hb]
      refine ⟨fun k ↦ k.lastCases
          (by simp [swapVecBits, swapPairBits, hO _ (fun j e ↦ hDisj j.castSucc _ e.symm)
            fun j e ↦ (Fin.castSucc_lt_last j).ne (htI e).symm])
          fun j ↦ (uNe (fun e ↦ (Fin.castSucc_lt_last j).ne (hqI e)) (hDisj _ _) _).trans (hQ j),
        fun k ↦ k.lastCases
          (by simp [swapVecBits, swapPairBits, (hDisj _ _).symm,
            hO _ (fun j e ↦ (Fin.castSucc_lt_last j).ne (hqI e).symm) fun j ↦ hDisj _ j.castSucc])
          fun j ↦ (uNe (hDisj _ _).symm (htI · |> (Fin.castSucc_lt_last j).ne) _).trans (hT j),
        fun w hwQ hwT ↦ (uNe (hwQ _) (hwT _) _).trans (hO w (hwQ ·.castSucc) (hwT ·.castSucc))⟩
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
  PgBase.phaseGradientState abpKin14Usel
theorem finBitsVal_eq_sum_pow :
    ∀ {n : ℕ} (f : Fin n → ZMod 2),
      finBitsVal f = ∑ b : Fin n, if f b = 1 then 2 ^ b.val else 0
  | 0, _ => rfl
  | n + 1, f => by
      dsimp only [finBitsVal]
      have hmul : (∑ x : Fin n, 2 * if f x.succ = 1 then 2 ^ x.val else 0) = ∑ x : Fin n,
          if f x.succ = 1 then 2 ^ x.succ.val else 0 :=
        Finset.sum_congr rfl fun x _ ↦ by dsimp only [Fin.val_succ]; split_ifs <;> ring
      rw [finBitsVal_eq_sum_pow (fun i ↦ f i.succ), Fin.sum_univ_succ, Finset.mul_sum, hmul]
      rcases DynCircExt.bit_cases (f 0) with h0 | h0 <;> simp [h0, ZMod.val_one]
theorem kin_conj_mid_mulVec {N : ℕ} (W Uk Ual K Q : Operator.Unitary (2 ^ N))
    (PH : Operator (2 ^ N))
    (v₀ vδ vₖ : Fin (2 ^ N) → ℂ) (f g : Fin 256 → Fin (2 ^ N) → ℂ) (c82 : ℂ)
    (hW : W.1.mulVec v₀ = vδ) (hK4 : Uk.1.mulVec vδ = Ual.1.mulVec vδ)
        (hGrp : W⁻¹ * Ual * W = K⁻¹ * Q * K)
    (hK : K.1.mulVec v₀ = vₖ) (hQ : Q.1.mulVec vₖ = ∑ k : Fin 256, f k)
    (hStep : ∀ k : Fin 256, PH.mulVec ((K⁻¹).1.mulVec (f k)) = c82 • g k) :
    PH.mulVec (((W⁻¹ * Uk * W).1).mulVec v₀) = c82 • ∑ k : Fin 256, g k := by
  have h1 : (W⁻¹).1.mulVec (Uk.1.mulVec (W.1.mulVec v₀)) =
      (K⁻¹).1.mulVec (Q.1.mulVec (K.1.mulVec v₀)) := by
    simpa only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hW, hK4] using
      congrArg (fun M : Operator.Unitary (2 ^ N) ↦ M.1.mulVec v₀) hGrp
  simp only [Submonoid.coe_mul, ← mulVec_mulVec]; rw [h1]; simp only [hK, hQ, mulVec_sum,
      hStep, ← Finset.smul_sum]
theorem byteOfBits_basisBits (y : Fin 256) : byteOfBits (basisBits 8 y) = y := by
  let β : BitAssignment 226 := fun j ↦ if hj : j.val < 8 then basisBits 8 y ⟨j.val, hj⟩ else 0
  have hβ (b : Fin 8) : β (wKin b.val) = basisBits 8 y b :=
    (dite_eq_left ((Nat.mod_eq_of_lt (by omega : b.val < 226)).trans_lt b.isLt)).trans
      (congrArg (basisBits 8 y) (Fin.ext (Nat.mod_eq_of_lt (by omega))))
  have hv := congrArg Fin.val (kOfBits8_of_basisBits8 y β hβ)
  rw [show (kOfBits8 β).val = prefixSum _ 8 % 256 from rfl, prefixSum_eq_sum_pow,
    Finset.sum_congr rfl fun b _ ↦ by rw [hβ b], ← finBitsVal_eq_sum_pow,
    Nat.mod_eq_of_lt (show finBitsVal _ < 256 from (byteOfBits _).isLt)] at hv
  exact Fin.ext hv
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix HermitianMat PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitBellVecCleanStep
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
attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem specBellVec_eq_fixedBellVec {n : ℕ} {P : BitAssignment n → Prop} (M : ℕ)
    (wCtrl : Fin M → Wire n) (cVec : Fin M → ZMod 2) (hC : ∀ p α, P α → α (wCtrl p) = cVec p) :
    ∀ (m : ℕ) (qH : Fin m → Wire n) (wTgt₁ wTgt₂ : Fin m → Fin M → Wire n)
      (_hT : ∀ k p, wTgt₁ k p = wTgt₂ k p)
      (hhc : ∀ k p, qH k ≠ wCtrl p) (hht₁ : ∀ k p, qH k ≠ wTgt₁ k p)
      (hct : ∀ k p, wCtrl p ≠ wTgt₁ k p) (hht₂ : ∀ k p, qH k ≠ wTgt₂ k p)
      (_hUpdH : ∀ k α v, P α → P (Function.update α (qH k) v))
      (_hUpdT : ∀ k p α v, P α → P (Function.update α (wTgt₂ k p) v))
      {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
      (specBellEntangleVecCirc M m qH wCtrl wTgt₁ hhc hht₁ hct).eval.1.mulVec ψ =
        (fixedBellVecCirc M m qH cVec wTgt₂ hht₂).eval.1.mulVec ψ ∧
      PreservesKetPred P ((fixedBellVecCirc M m qH cVec wTgt₂ hht₂).eval.1.mulVec ψ)
  | 0, _, _, _, _, _, _, _, _, _, _, _, hψ =>
      ⟨by simp [specBellEntangleVecCirc, fixedBellVecCirc], by simpa [fixedBellVecCirc] using hψ⟩
  | m + 1, qH, wTgt₁, wTgt₂, hT, hhc, hht₁, hct, hht₂, hUpdH, hUpdT, ψ, hψ => by
      obtain ⟨hEqV, hPV⟩ :=
          specBellVec_eq_fixedBellVec M wCtrl cVec hC m (fun k ↦ qH k.castSucc)
          (fun k ↦ wTgt₁ k.castSucc) (fun k ↦ wTgt₂ k.castSucc) (fun k ↦ hT k.castSucc)
          (fun k ↦ hhc k.castSucc) (fun k ↦ hht₁ k.castSucc) (fun k ↦ hct k.castSucc)
          (fun k ↦ hht₂ k.castSucc) (fun k ↦ hUpdH k.castSucc) (fun k ↦ hUpdT k.castSucc) hψ
      have hOne : ∀ (K : ℕ) (wC : Fin K → Wire n) (cV : Fin K → ZMod 2)
          (hcK : ∀ p α, P α → α (wC p) = cV p) (t₁ t₂ : Fin K → Wire n) (htK : ∀ p, t₁ p = t₂ p)
          (hhcK : ∀ p, qH (Fin.last m) ≠ wC p) (hht1K : ∀ p, qH (Fin.last m) ≠ t₁ p)
          (hctK : ∀ p, wC p ≠ t₁ p) (hht2K : ∀ p, qH (Fin.last m) ≠ t₂ p)
          (huTK : ∀ p α v, P α → P (Function.update α (t₂ p) v)) {φ : Fin (2 ^ n) → ℂ},
          PreservesKetPred P φ →
          (specFanoutCopyCirc K (qH (Fin.last m)) wC t₁ hhcK hht1K hctK).eval.1.mulVec φ =
          (fixedFanoutCirc K (qH (Fin.last m)) cV t₂ hht2K).eval.1.mulVec φ := by
        intro K; induction K with
        | zero => intros; simp [specFanoutCopyCirc, fixedFanoutCirc]
        | succ K ihK =>
            intro wC cV hcK t₁ t₂ htK hhcK hht1K hctK hht2K huTK φ hφ;
            dsimp only [specFanoutCopyCirc, fixedFanoutCirc]
            rw [eval_seq_mulVec, eval_seq_mulVec, ihK (fun p ↦ wC p.castSucc)
                (fun p ↦ cV p.castSucc) (fun p ↦ hcK p.castSucc) (fun p ↦ t₁ p.castSucc)
                (fun p ↦ t₂ p.castSucc) (fun p ↦ htK p.castSucc) (fun p ↦ hhcK p.castSucc)
                (fun p ↦ hht1K p.castSucc) (fun p ↦ hctK p.castSucc) (fun p ↦ hht2K p.castSucc)
                (fun p ↦ huTK p.castSucc) hφ]
            exact toff_fanout_leaf_eq (htK (Fin.last K)) (hhcK (Fin.last K)) (hht1K (Fin.last K))
                (hctK (Fin.last K)) (hht2K (Fin.last K)) (hcK (Fin.last K))
                (preservesKetPred_fixedFanout K _ _ _ _ (fun p ↦ huTK p.castSucc) hφ)
      dsimp only [specBellEntangleVecCirc, fixedBellVecCirc, specBellEntangle1Circ, fixedBell1Circ];
      rw [eval_seq_mulVec, eval_seq_mulVec, hEqV, eval_seq_mulVec, eval_seq_mulVec];
      have hPH :=
          preservesKetPred_H (hUpdH (Fin.last m)) hPV; exact ⟨hOne M wCtrl cVec hC _ _
          (hT (Fin.last m)) (hhc (Fin.last m)) (hht₁ (Fin.last m)) (hct (Fin.last m))
          (hht₂ (Fin.last m)) (hUpdT (Fin.last m)) hPH,
          preservesKetPred_fixedFanout M _ _ _ (hht₂ (Fin.last m)) (hUpdT (Fin.last m)) hPH⟩

/--
Any predicate invariant under updates on `AllPlaneMod r` is preserved across
`cFixedRouterCirc r cLo cHi`.
-/
theorem preservesKetPred_cFixedRouterCirc {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) {P : BitAssignment n → Prop}
    (hModKeep : ∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v))
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cFixedRouterCirc r cLo cHi).eval.1.mulVec ψ) := by
  have hSV : ∀ (m : ℕ) (qB : Fin m → Wire n) (cV : Fin M → ZMod 2) (wT : Fin m → Fin M → Wire n)
      (hbt : ∀ k p, qB k ≠ wT k p) (hqB : ∀ k, AllPlaneMod r (qB k))
      (hwT : ∀ k p, AllPlaneMod r (wT k p)) {φ : Fin (2 ^ n) → ℂ}, PreservesKetPred P φ →
      PreservesKetPred P ((fixedSwapVecCirc M m qB cV wT hbt).eval.1.mulVec φ) := by
    intro m; induction m with
    | zero => intros; simpa [fixedSwapVecCirc]
    | succ m ihm =>
        intro qB cV wT hbt hqB hwT φ hφ
        dsimp only [fixedSwapVecCirc]; rw [eval_seq_mulVec]
        exact preservesKetPred_fixedSwap1 M _ _ _ _ (hModKeep (hqB (Fin.last m)))
            (fun p ↦ hModKeep (hwT (Fin.last m) p)) (ihm _ _ _ _ (fun k ↦ hqB k.castSucc)
            (fun k p ↦ hwT k.castSucc p) hφ)
  have hBV : ∀ (m : ℕ) (qH : Fin m → Wire n) (cV : Fin M → ZMod 2) (wT : Fin m → Fin M → Wire n)
      (hht : ∀ k p, qH k ≠ wT k p) (hqH : ∀ k, AllPlaneMod r (qH k))
      (hwT : ∀ k p, AllPlaneMod r (wT k p)) {φ : Fin (2 ^ n) → ℂ}, PreservesKetPred P φ →
      PreservesKetPred P ((fixedBellVecCirc M m qH cV wT hht).eval.1.mulVec φ) := by
    intro m; induction m with
    | zero => intros; simpa [fixedBellVecCirc]
    | succ m ihm =>
        intro qH cV wT hht hqH hwT φ hφ
        dsimp only [fixedBellVecCirc, fixedBell1Circ]; rw [eval_seq_mulVec, eval_seq_mulVec]
        exact preservesKetPred_fixedFanout M _ _ _ _ (fun p ↦ hModKeep (hwT (Fin.last m) p))
            (preservesKetPred_H (hModKeep (hqH (Fin.last m))) (ihm _ _ _ _ (fun k ↦ hqH k.castSucc)
            (fun k p ↦ hwT k.castSucc p) hφ))
  dsimp only [cFixedRouterCirc]; simp only [eval_seq_mulVec]
  have hwSys : ∀ b p, AllPlaneMod r (rSys r p b) := fun b p ↦
      ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩
  exact hBV 24 (rHB r) cHi (fun b p ↦ rSys r p b)
      (fun b p ↦ rr_ne r (by have := b.isLt; have := p.isLt; dsimp; omega))
      (fun b ↦ ⟨b, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩) hwSys
    (hBV 24 (rHA r) cLo (fun b p ↦ rSys r p b)
        (fun b p ↦ rr_ne r (by have := b.isLt; have := p.isLt; dsimp; omega))
        (fun b ↦ ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩) hwSys
      (hSV 24 (rBufHi r) cHi (fun b p ↦ rSys r p b)
          (fun b p ↦ rr_ne r (by have := b.isLt; have := p.isLt; dsimp; omega))
          (fun b ↦ ⟨b, Or.inr (Or.inl rfl)⟩) hwSys
        (hSV 24 (rBufLo r) cLo (fun b p ↦ rSys r p b)
            (fun b p ↦ rr_ne r (by have := b.isLt; have := p.isLt; dsimp; omega))
            (fun b ↦ ⟨b, Or.inl rfl⟩) hwSys hψ)))
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187

namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open PhotochemistrySolution.ZeroNEremAxisSq18
/-- Encode a CNOT `src -> dst` leaf in `PrimTree`. -/
def pCnot (src dst : ℕ) : PrimTree :=
  .leaf (1 ||| (src <<< 2) ||| (dst <<< 11))
/-- Encode a clean-target TempAND `(a, b) -> dst` leaf in `PrimTree`. -/
def pAnd (a b dst : ℕ) : PrimTree :=
  .leaf (2 ||| (a <<< 2) ||| (b <<< 11) ||| (dst <<< 20))
theorem testBit_false_of_pow (m0 : ℕ) {x m : ℕ} (hx : x < 2 ^ m0) (hm : m0 ≤ m) : x.testBit m =
    false :=
  Nat.testBit_eq_false_of_lt (hx.trans_le (Nat.pow_le_pow_right (by omega) hm))
theorem shift_mod512_96 {c s x : ℕ} (hx : x < 96) (h : ∀ k < 9, c.testBit (s + k) = x.testBit k) :
    ((c >>> s) % 512) % 96 = x := by
  have h512 : (c >>> s) % 512 = x := Nat.eq_of_testBit_eq fun k ↦ by
    rw [show (512 : ℕ) = 2 ^ 9 from rfl, Nat.testBit_mod_two_pow]
    by_cases hk : k < 9
    · simp [hk, Nat.testBit_shiftRight, h k hk]
    · simp [hk, testBit_false_of_pow 9 (x := x) (m := k) (by omega) (by omega)]
  rw [h512, Nat.mod_eq_of_lt hx]
theorem mod4_of_lo2 {c r : ℕ} (hr : r < 4) (h : ∀ k < 2, c.testBit k = r.testBit k) : c % 4 = r :=
  Nat.eq_of_testBit_eq fun k ↦ by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow]
    by_cases hk : k < 2
    · simp [hk, h k hk]
    · simp [hk, testBit_false_of_pow 2 (x := r) (m := k) hr (by omega)]
theorem testBit_cond_xor1 {st dst i : ℕ} (v : Bool) :
    (if v = true then st ^^^ (1 <<< dst) else st).testBit i = if i =
        dst then xor (st.testBit i) v else st.testBit i := by
  cases v
  · by_cases hi : i = dst <;> simp [hi]
  · simp only [↓reduceIte, Nat.testBit_xor, Nat.testBit_shiftLeft]
    by_cases hi : i = dst
    · simp [hi, show (1 : ℕ).testBit 0 = true from rfl]
    · by_cases hle : dst ≤ i
      · simp [hi, hle, testBit_false_of_pow 1 (x := 1) (m := i - dst) (by decide) (by omega)]
      · simp [hi, hle]
theorem hi_bit_zero {x m : ℕ} (hx : x < 96) (hm : 9 ≤ m) : x.testBit m = false :=
  testBit_false_of_pow 9 (by omega) hm
theorem evalPrimTree95_cnot {src dst : ℕ} (hs : src < 96) (hd : dst < 96) (hne : src ≠ dst)
    (st i : ℕ) : (evalPrimTree 95 st (pCnot src dst)).testBit i = if i = dst then xor (st.testBit i)
    (st.testBit src) else st.testBit i := by
  set c := 1 ||| (src <<< 2) ||| (dst <<< 11)
  have hc : c % 4 = 1 := mod4_of_lo2 (by omega) fun k hk ↦ by
    simp [c, Nat.testBit_or, Nat.testBit_shiftLeft,
      show ¬(2 ≤ k) by omega, show ¬(11 ≤ k) by omega]
  have hw1 : ((c >>> 2) % 512) % 96 = src := shift_mod512_96 hs fun k hk ↦ by
    simp [c, Nat.testBit_or, Nat.testBit_shiftLeft, show 2 ≤ 2 + k by omega,
      show ¬(11 ≤ 2 + k) by omega, show 2 + k - 2 = k by omega,
      testBit_false_of_pow 2 (by omega : 1 < 2 ^ 2) (by omega : 2 ≤ 2 + k)]
  have hw2 : ((c >>> 11) % 512) % 96 = dst := shift_mod512_96 hd fun k _ ↦ by
    simp [c, Nat.testBit_or, Nat.testBit_shiftLeft, show 2 ≤ 11 + k by omega,
      show 11 ≤ 11 + k by omega, show 11 + k - 2 = 9 + k by omega,
      show 11 + k - 11 = k by omega, hi_bit_zero hs (by omega : 9 ≤ 9 + k),
      testBit_false_of_pow 2 (by omega : 1 < 2 ^ 2) (by omega : 2 ≤ 11 + k)]
  unfold pCnot evalPrimTree evalPrimGate
  dsimp only
  rw [hc, hw1, hw2, nat_beq_false_of_ne hne]
  simp only [show Nat.beq 1 0 = false from rfl, show Nat.beq 1 1 = true from rfl,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
  exact testBit_cond_xor1 (st.testBit src)
theorem evalPrimTree95_and {a b dst : ℕ} (ha : a < 96) (hb : b < 96) (hd : dst < 96) (hab : a ≠ b)
    (had : a ≠ dst) (hbd : b ≠ dst) (st i : ℕ) : (evalPrimTree 95 st (pAnd a b dst)).testBit i =
    if i = dst then xor (st.testBit i) (st.testBit a && st.testBit b) else st.testBit i := by
  set c := 2 ||| (a <<< 2) ||| (b <<< 11) ||| (dst <<< 20)
  have hc : c % 4 = 2 := mod4_of_lo2 (by omega) fun k hk ↦ by
    simp [c, Nat.testBit_or, Nat.testBit_shiftLeft,
      show ¬(2 ≤ k) by omega, show ¬(11 ≤ k) by omega, show ¬(20 ≤ k) by omega]
  have hw1 : ((c >>> 2) % 512) % 96 = a := shift_mod512_96 ha fun k hk ↦ by
    simp [c, Nat.testBit_or, Nat.testBit_shiftLeft, show 2 ≤ 2 + k by omega,
      show ¬(11 ≤ 2 + k) by omega, show ¬(20 ≤ 2 + k) by omega, show 2 + k - 2 = k by omega,
      testBit_false_of_pow 2 (by omega : 2 < 2 ^ 2) (by omega : 2 ≤ 2 + k)]
  have hw2 : ((c >>> 11) % 512) % 96 = b := shift_mod512_96 hb fun k hk ↦ by
    simp [c, Nat.testBit_or, Nat.testBit_shiftLeft, show 2 ≤ 11 + k by omega,
      show 11 ≤ 11 + k by omega, show ¬(20 ≤ 11 + k) by omega, show 11 + k - 2 = 9 + k by omega,
      show 11 + k - 11 = k by omega, hi_bit_zero ha (by omega : 9 ≤ 9 + k),
      testBit_false_of_pow 2 (by omega : 2 < 2 ^ 2) (by omega : 2 ≤ 11 + k)]
  have hw3 : ((c >>> 20) % 512) % 96 = dst := shift_mod512_96 hd fun k _ ↦ by
    simp [c, Nat.testBit_or, Nat.testBit_shiftLeft, show 2 ≤ 20 + k by omega,
      show 11 ≤ 20 + k by omega, show 20 ≤ 20 + k by omega, show 20 + k - 2 = 18 + k by omega,
      show 20 + k - 11 = 9 + k by omega, show 20 + k - 20 = k by omega,
      hi_bit_zero ha (by omega : 9 ≤ 18 + k), hi_bit_zero hb (by omega : 9 ≤ 9 + k),
      testBit_false_of_pow 2 (by omega : 2 < 2 ^ 2) (by omega : 2 ≤ 20 + k)]
  unfold pAnd evalPrimTree evalPrimGate
  dsimp only
  rw [hc, hw1, hw2, hw3, nat_beq_false_of_ne hab, nat_beq_false_of_ne had, nat_beq_false_of_ne hbd]
  simp only [show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
  exact testBit_cond_xor1 (st.testBit a && st.testBit b)
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein

namespace QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
open Operator QProg Matrix Circuit Qubit PrimitiveGate HermitianMat
  PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem oneHotPos_finish {M n : ℕ} (k : ℕ) (hk : 2 ≤ k) (p1 p2d p2d1 : Fin M) (hp1 : p1.val = 1)
    (hp2d : p2d.val = k) (hp2d1 : p2d1.val = k + 1) (wOut : Fin M → Wire n)
    (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q) (qAct : Wire n) (γ δ6 : BitAssignment n)
    (idx lo len : ℕ) (b : ZMod 2) (hloLt : lo < k) (hIdxLt : idx < M)
    (hZeroGated : γ qAct = 0 → idx = 0) (hPos : γ qAct = 1 → idx ≠ 0)
    (hIdxDecomp : idx = lo + if b = 1 then k else 0) (hlenEq : len = M - k)
    (hp2d1Val : δ6 (wOut p2d1) = b + (γ qAct + if 1 ≤ lo then 1 else 0) + if 2 ≤ lo ∧ lo <
    len then b else 0) (eval6 : ∀ q : Fin M, q ≠ p2d1 → δ6 (wOut q) = if q = p2d then γ qAct +
    if 1 ≤ lo then 1 else 0 else if q.val < k then if 2 ≤ q.val ∧ q.val < len then (if q.val =
    0 then 0 else if lo = q.val then 1 else 0) + (if q.val = 0 then 0 else if lo =
    q.val then 1 else 0) * b else if q.val = 0 then 0 else if lo = q.val then 1 else 0 else if k +
    2 ≤ q.val then (if lo = q.val - k then 1 else 0) * b else 0)
    (p : Fin M) : Function.update δ6 (wOut p1) (δ6 (wOut p1) + δ6 (wOut p2d1))
    (wOut p) = if idx = p.val then γ qAct else 0 := by
  have _ := p2d1.isLt
  have _ := p.isLt
  have h121 : p1 ≠ p2d1 := fun e ↦ absurd (congrArg Fin.val e) (by omega)
  have h12d : p1 ≠ p2d := fun e ↦ absurd (congrArg Fin.val e) (by omega)
  rcases eq_or_ne p p1 with rfl | hp1e
  · rw [Function.update_self, eval6 p h121, hp2d1Val, ite_eq_right h12d, hp1,
      ite_eq_right Nat.one_ne_zero]
    rcases zmod2_cases (γ qAct) with hq | hq
    · have _ := hZeroGated hq
      rcases zmod2_cases b with rfl | rfl
      · rw [ite_eq_right zero_ne_one] at hIdxDecomp
        rw [hq]; split_ifs <;> first | rfl | omega
      · rw [ite_eq_left rfl] at hIdxDecomp
        rw [hq]; split_ifs <;> first | rfl | omega
    · have _ := hPos hq
      rcases zmod2_cases b with rfl | rfl
      · rw [ite_eq_right zero_ne_one] at hIdxDecomp
        rw [hq]; split_ifs <;> first | rfl | omega
      · rw [ite_eq_left rfl] at hIdxDecomp
        rw [hq]; split_ifs <;> first | rfl | omega
  · rw [Function.update_of_ne (hInj p p1 hp1e)]
    have hne1 : p.val ≠ 1 := fun e ↦ hp1e (Fin.ext (e.trans hp1.symm))
    rcases eq_or_ne p p2d1 with rfl | hp21
    · rw [hp2d1Val, hp2d1]
      rcases zmod2_cases (γ qAct) with hq | hq
      · have _ := hZeroGated hq
        rcases zmod2_cases b with rfl | rfl
        · rw [ite_eq_right zero_ne_one] at hIdxDecomp
          rw [hq]; split_ifs <;> first | rfl | omega
        · rw [ite_eq_left rfl] at hIdxDecomp
          rw [hq]; split_ifs <;> first | rfl | omega
      · have _ := hPos hq
        rcases zmod2_cases b with rfl | rfl
        · rw [ite_eq_right zero_ne_one] at hIdxDecomp
          rw [hq]; split_ifs <;> first | rfl | omega
        · rw [ite_eq_left rfl] at hIdxDecomp
          rw [hq]; split_ifs <;> first | rfl | omega
    · rw [eval6 p hp21]
      have hne21 : p.val ≠ k + 1 := fun e ↦ hp21 (Fin.ext (e.trans hp2d1.symm))
      rcases eq_or_ne p p2d with rfl | hp2de
      · rw [ite_eq_left rfl, hp2d]
        rcases zmod2_cases (γ qAct) with hq | hq
        · have _ := hZeroGated hq
          rcases zmod2_cases b with rfl | rfl
          · rw [ite_eq_right zero_ne_one] at hIdxDecomp
            rw [hq]; split_ifs <;> first | rfl | omega
          · rw [ite_eq_left rfl] at hIdxDecomp
            rw [hq]; split_ifs <;> first | rfl | omega
        · have _ := hPos hq
          rcases zmod2_cases b with rfl | rfl
          · rw [ite_eq_right zero_ne_one] at hIdxDecomp
            rw [hq]; split_ifs <;> first | rfl | omega
          · rw [ite_eq_left rfl] at hIdxDecomp
            rw [hq]; split_ifs <;> first | rfl | omega
      · rw [ite_eq_right hp2de]
        have hne2d : p.val ≠ k := fun e ↦ hp2de (Fin.ext (e.trans hp2d.symm))
        rcases zmod2_cases (γ qAct) with hq | hq
        · have _ := hZeroGated hq
          rcases zmod2_cases b with rfl | rfl
          · rw [ite_eq_right zero_ne_one] at hIdxDecomp
            rw [hq]; split_ifs <;> first | rfl | omega
          · rw [ite_eq_left rfl] at hIdxDecomp
            rw [hq]; split_ifs <;> first | rfl | omega
        · have _ := hPos hq
          rcases zmod2_cases b with rfl | rfl
          · rw [ite_eq_right zero_ne_one] at hIdxDecomp
            rw [hq]; split_ifs <;> first | rfl | omega
          · rw [ite_eq_left rfl] at hIdxDecomp
            rw [hq]; split_ifs <;> first | rfl | omega
theorem fwdBits_oneHotPosZeroGated {M D n : ℕ} (hD1 : 1 ≤ D)
    (hMlo : 2 ^ (D - 1) + 2 ≤ M) (hMhi : M ≤ 2 ^ D) (hPowSub : ∀ d < D - 1, 2 ^ d < M)
    (qAct : Wire n) (wBit : Fin D → Wire n) (wOut : Fin M → Wire n)
    (hAO : ∀ p, qAct ≠ wOut p) (hBO : ∀ d p, wBit d ≠ wOut p)
    (hInj : ∀ p q, p ≠ q → wOut p ≠ wOut q)
    (γ : BitAssignment n) (hIdxLt : idxValD wBit γ < M)
    (hZeroGated : γ qAct = 0 → idxValD wBit γ = 0)
    (hPos : γ qAct = 1 → idxValD wBit γ ≠ 0)
    (hOut0 : ∀ p : Fin M, γ (wOut p) = 0) :
    let δ := (oneHotPosZeroGated hD1 hMlo hPowSub qAct wBit wOut hAO hBO hInj).fwdBits γ
    (∀ p : Fin M, δ (wOut p) = if idxValD wBit γ = p.val then γ qAct else 0) ∧
    (∀ w : Wire n, (∀ p : Fin M, w ≠ wOut p) → δ w = γ w) := by
  have h2Pow : 2 ^ D = 2 ^ (D - 1) + 2 ^ (D - 1) :=
    (congrArg (2 ^ ·) (Nat.sub_add_cancel hD1)).symm.trans ((pow_succ 2 (D -
        1)).trans (Nat.mul_two _))
  obtain ⟨δ6, hUnfold, hIdxDecomp, hlenEq, hp2d1Val, eval6, hOth⟩ :=
    oneHotPosZeroGated_stage6 hD1 hMlo hMhi hPowSub qAct wBit wOut hAO hBO hInj γ hIdxLt hOut0
  dsimp only
  rw [hUnfold]
  exact ⟨oneHotPos_finish (2 ^ (D - 1)) (by omega) ⟨1, by omega⟩ ⟨2 ^ (D - 1), by omega⟩
    ⟨2 ^ (D - 1) + 1, hMlo⟩ rfl rfl rfl wOut hInj qAct γ δ6 (idxValD wBit γ)
    (idxValPrefix wBit γ (D - 1) (Nat.sub_le D 1)) (min (M - 2 ^ (D - 1)) (2 ^ (D - 1)))
    (γ (wBit ⟨D - 1, Nat.sub_lt hD1 Nat.zero_lt_one⟩))
    (idxValPrefix_lt_pow wBit γ (D - 1) (Nat.sub_le D 1))
    hIdxLt hZeroGated hPos hIdxDecomp hlenEq hp2d1Val eval6,
    fun w hw ↦ (Function.update_of_ne (hw _) _ _).trans (hOth w hw)⟩
end QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec

namespace QuantumComputation.Specs.PhotochemistrySolution.Qft8PostCancelT5
open PhotochemistrySolution.FastQft8
/-- Low `m`-bit integer value `∑_{k < m} p_k * 2^k` from `p : Fin 8 → Bool`. -/
def rLoBool (m : ℕ) (p : Fin 8 → Bool) : ℕ :=
  regValBool m (fun k ↦ p (Fin.ofNat 8 k.val))
/--
Closed-form post-cancel `x = 0` phase accumulator `eZeroBool m p` (`0 ≤ m ≤ 8`).
Note that `eZeroBool (j + 1) p` depends only on bits `0..j - 1` (never bit `j`!).
-/
def eZeroBool (m : ℕ) (p : Fin 8 → Bool) : ℕ :=
  let b : Fin 8 → ℕ := fun k ↦ cond (p k) 1 0
  match m with
  | 0 => 0
  | 1 => 0
  | 2 => 224 * b 0
  | 3 => 32 + 208 * b 0 + 224 * b 1
  | 4 => 64 + 200 * b 0 + 208 * b 1 + 224 * b 2
  | 5 => 96 + 196 * b 0 + 200 * b 1 + 208 * b 2 + 224 * b 3
  | 6 => 128 + 194 * b 0 + 196 * b 1 + 200 * b 2 + 208 * b 3 + 224 * b 4
  | 7 => 160 + 193 * b 0 + 194 * b 1 + 196 * b 2 + 200 * b 3 + 208 * b 4 + 224 * b 5
  | _ => 192 + 193 * b 0 + 193 * b 1 + 194 * b 2 + 196 * b 3 + 200 * b 4 + 208 * b 5 + 224 * b 6
/-- Pure `Bool` mirror of the mod-`256` phase kickback `δ_j(p)` applied before `H (rP j)`. -/
def deltaLayerBool (j : Fin 8) (p : Fin 8 → Bool) : ℕ :=
    if j.val = 0 then 0 else if j.val = 1 then 32 * (cond (p 1) 1 0 + 7 * cond (xor (p 0)
    (p 1)) 1 0) else if j.val < 7 then 2 ^ (6 - j.val) * (regValBool (j.val - 1)
    (fun i ↦ xor (xor true (p (Fin.ofNat 8 i.val))) (p j)) + cond (!p j) 1 0) + 32 *
    (7 * cond (xor (p (Fin.ofNat 8 (j.val - 1))) (p j)) 1 0 + 2 *
    cond (p j) 1 0) else regValBool 5 (fun i ↦ xor (xor true (p (Fin.ofNat 8 (i.val + 1)))) (p 7)) +
    cond (xor (!(p 7 && p 0)) (p 7)) 1 0 + 32 * (7 * cond (xor (p 6) (p 7)) 1 0 + 2 *
    cond (p 7) 1 0)
theorem eZeroBool_step_aux :
    ∀ (j : Fin 8) (b0 b1 b2 b3 b4 b5 b6 b7 : Bool),
      let p := vec8 b0 b1 b2 b3 b4 b5 b6 b7
      decide ((eZeroBool j.val p + deltaLayerBool j p) % 256 =
        (eZeroBool (j.val + 1) p + rLoBool j.val p * cond (p j) 1 0 * 2 ^ (7 - j.val)) % 256) =
        true := by decide +kernel
theorem eZeroBool_step (j : Fin 8) (p : Fin 8 → Bool) : (eZeroBool j.val p +
    deltaLayerBool j p) % 256 = (eZeroBool (j.val + 1) p + rLoBool j.val p * cond (p j) 1 0 *
    2 ^ (7 - j.val)) % 256 :=
    (vec8_eta p).symm ▸ of_decide_eq_true (eZeroBool_step_aux j (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
    (p 6) (p 7))
theorem eZeroBool_upd_aux :
    ∀ (j : Fin 8) (v b0 b1 b2 b3 b4 b5 b6 b7 : Bool),
      let p := vec8 b0 b1 b2 b3 b4 b5 b6 b7
      decide (eZeroBool (j.val + 1) (updP p j v) = eZeroBool (j.val + 1) p ∧
        rLoBool j.val (updP p j v) = rLoBool j.val p ∧
        rLoBool (j.val + 1) p = rLoBool j.val p + cond (p j) 1 0 * 2 ^ j.val) =
        true := by decide +kernel
theorem eZeroBool_upd_and_rLo (j : Fin 8) (v : Bool) (p : Fin 8 → Bool) : eZeroBool (j.val + 1)
    (updP p j v) = eZeroBool (j.val + 1) p ∧ rLoBool j.val (updP p j v) = rLoBool j.val p ∧
    rLoBool (j.val + 1) p = rLoBool j.val p + cond (p j) 1 0 * 2 ^ j.val :=
    (vec8_eta p).symm ▸ of_decide_eq_true (eZeroBool_upd_aux j v (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
    (p 6) (p 7))
end QuantumComputation.Specs.PhotochemistrySolution.Qft8PostCancelT5

namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k
open PhotochemistrySolution.XMeasLinearCleanStep
/-- Cumulative Gray XOR sum on `pAMsb r [0..k)`. -/
def grayXorSum {M D n : ℕ} (r : PlaneReg M D n) (mask : ℕ → Bool) (δ : BitAssignment n) :
    ∀ k : ℕ, k ≤ D → ZMod 2
  | 0, _ => 0
  | k + 1, hk =>
      grayXorSum r mask δ k (Nat.le_of_succ_le hk) +
        if mask k then δ (pAMsb r ⟨k, hk⟩) else 0
theorem amsbCzIndep {M D n : ℕ} (r : PlaneReg M D n) (d : Fin D) : ∀ p ∈ ([mkWP (pUMsb r d) (pHB r)
    ((hne_Msb_Init r d).1)] : List (WirePair n)), p.1 ≠ pAMsb r d ∧ p.2.1 ≠ pAMsb r d :=
  List.forall_mem_singleton.mpr ⟨(hne_Msb_Init r d).2.2.2.1, (hne_Msb_Init r d).2.2.2.2.1⟩
theorem pr_inj_sys {M D n : ℕ} (r : PlaneReg M D n) (p q : Fin M) (h : p ≠ q) : pSys r p ≠
    pSys r q :=
  pr_ne r fun e ↦ h <| Fin.ext <| by
    dsimp at e
    omega
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB (StructuredCB)

namespace QuantumComputation.Specs.PhotochemistrySolution.LegendreFastEval
open PhotochemistrySolution.OddDivEval
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB (clearBit)
/-- Force `m : ℕ` to WHNF (`Nat.lit`) once before applying `k`. -/
def forceNat (m : ℕ) (k : ℕ → ℕ) : ℕ :=
  match m with
  | 0 => k 0
  | n + 1 => k (n + 1)
theorem forceNat_eq (m : ℕ) (k : ℕ → ℕ) : forceNat m k = k m := by
  cases m <;> rfl
/-- Force `m : ℕ` to WHNF (`Nat.lit`) once before applying `Bool` continuation `k`. -/
def forceNatBool (m : ℕ) (k : ℕ → Bool) : Bool :=
  match m with
  | 0 => k 0
  | n + 1 => k (n + 1)
theorem forceNatBool_eq (m : ℕ) (k : ℕ → Bool) : forceNatBool m k = k m := by
  cases m <;> rfl
def finalCleanMaskFast {M : ℕ} (sMask : ℕ) : ComputeProg M → ℕ
  | .id | .x _ | .cnot _ _ _ => sMask
  | .andGate _ _ anc _ _ _ => forceNat sMask fun s ↦ clearBit s anc.val
  | .seq p₁ p₂ => forceNat (finalCleanMaskFast sMask p₁) fun s ↦ finalCleanMaskFast s p₂
theorem finalCleanMask_eq_fast {M : ℕ} (p : ComputeProg M) : ∀ sMask : ℕ,
    StructuredCB.finalCleanMask sMask p = finalCleanMaskFast sMask p := by
  induction p with
  | id | x _ | cnot _ _ _ => exact fun _ ↦ rfl
  | andGate _ _ _ _ _ _ => exact fun | 0 => rfl | _ + 1 => rfl
  | seq _ _ ih1 ih2 => simp [StructuredCB.finalCleanMask, finalCleanMaskFast, forceNat_eq, ih1, ih2]
/-- Strict `O(|cp|)` `validProgMask 0 sMask p` forcing `sMask` to WHNF at every step. -/
def validProgMask0Fast {M : ℕ} (sMask : ℕ) : ComputeProg M → Bool
  | .id => true
  | .x w => forceNatBool sMask fun s ↦ (s.testBit w.val).not
  | .cnot c t _ => forceNatBool sMask fun s ↦ (s.testBit t.val).not || s.testBit c.val
  | .andGate _ _ anc _ _ _ => forceNatBool sMask fun s ↦ s.testBit anc.val
  | .seq p₁ p₂ =>
      forceNatBool sMask fun s ↦
        validProgMask0Fast s p₁ &&
        forceNatBool (finalCleanMaskFast s p₁) fun s₁ ↦ validProgMask0Fast s₁ p₂
theorem validProgMask_zero_eq_fast {M : ℕ} (p : ComputeProg M) : ∀ sMask : ℕ,
    StructuredCB.validProgMask 0 sMask p = validProgMask0Fast sMask p := by
  induction p with
  | id => exact fun _ ↦ rfl
  | x _ | cnot _ _ _ | andGate _ _ _ _ _ _ =>
      simp [StructuredCB.validProgMask, validProgMask0Fast, forceNatBool_eq]
  | seq _ _ ih1 ih2 =>
      simp [StructuredCB.validProgMask, validProgMask0Fast, forceNatBool_eq, ih1,
        ← finalCleanMask_eq_fast, ih2]
end QuantumComputation.Specs.PhotochemistrySolution.LegendreFastEval

namespace QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17
open Qubit PhotochemistrySolution.LegendreFastEval PhotochemistrySolution.Csa36KickStep
  PhotochemistrySolution.OddDivEval
theorem s14_zero_lt_six : 0 < 6 := Nat.lt_of_sub_eq_succ rfl
theorem s14_one_lt_six : 1 < 6 := Nat.lt_of_sub_eq_succ rfl
theorem s14_two_lt_six : 2 < 6 := Nat.lt_of_sub_eq_succ rfl
theorem s14_three_lt_six : 3 < 6 := Nat.lt_of_sub_eq_succ rfl
theorem s14_four_lt_six : 4 < 6 := Nat.lt_of_sub_eq_succ rfl
theorem s14_five_lt_six : 5 < 6 := Nat.lt_of_sub_eq_succ rfl
def pre5OfFin8 (b : Fin 8) : Fin 6 :=
  match b.val with
  | 0 => ⟨0, s14_zero_lt_six⟩
  | 1 | 2 => ⟨1, s14_one_lt_six⟩
  | 3 => ⟨2, s14_two_lt_six⟩
  | 4 => ⟨3, s14_three_lt_six⟩
  | 5 => ⟨4, s14_four_lt_six⟩
  | _ => ⟨5, s14_five_lt_six⟩
/-- Priority decode of `6`-bit raw `pre6` directly to `Pre5` bucket `Fin 6`. -/
def pre5OfPre6 (p6 : Fin 64) : Fin 6 :=
  cond (!(p6.val.testBit 0)) ⟨0, s14_zero_lt_six⟩
    (cond (p6.val.testBit 4 || p6.val.testBit 5) ⟨5, s14_five_lt_six⟩
      (cond (p6.val.testBit 3) ⟨4, s14_four_lt_six⟩
        (cond (p6.val.testBit 2) ⟨3, s14_three_lt_six⟩
          (cond (p6.val.testBit 1) ⟨2, s14_two_lt_six⟩ ⟨1, s14_one_lt_six⟩))))
/-- `6`-bit priority one-hot word of raw `pre6` matching `ShortBin7Pre6ZHi30.oneHot6OfPre6`. -/
def pre6OneHot6S14 (p6 : ℕ) : ℕ :=
  let b0 := p6.testBit 0; let b1 := p6.testBit 1; let b2 := p6.testBit 2; let b3 := p6.testBit 3;
  let b4 := p6.testBit 4; let b5 := p6.testBit 5; let oh5 := b0 && b5; let rem4 := Bool.xor b0 oh5;
  let oh4 := rem4 && b4; let rem3 := Bool.xor rem4 oh4; let oh3 := rem3 && b3;
  let rem2 := Bool.xor rem3 oh3; let oh2 := rem2 && b2; let rem1 := Bool.xor rem2 oh2;
  let oh1 := rem1 && b1; let oh0 := Bool.xor rem1 oh1
  cond oh0 1 0 |||
    cond oh1 2 0 |||
    cond oh2 4 0 |||
    cond oh3 8 0 |||
    cond oh4 16 0 |||
    cond oh5 32 0
theorem pre5OfPre6_eq_pre5OfFin8_of_oneHot6 : ∀ (p6 : Fin 64) (b : Fin 8), pre6OneHot6S14 p6.val =
    binOneHot6 b.val → pre5OfPre6 p6 = pre5OfFin8 b := by decide +kernel
/-- Canonical `mod 2^31` representative in `0 .. 2^31 - 1` of a signed integer shift. -/
def mod31OfInt (x : ℤ) : ℕ := (x % (2147483648 : ℤ)).toNat
end QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
open Operator QProg DynamicCircuit Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
section IrreducibleDaddaOpt
attribute [local irreducible] pPre304
theorem axMap25_lo8 (ax : Fin 3) (k : Fin 8) :
    axMap25 ax ⟨k.val, by omega⟩ = ⟨8 * ax.val + k.val, by omega⟩ := by
  fin_cases ax <;> fin_cases k <;> rfl
theorem axMap25_mid8 (ax : Fin 3) (k : Fin 8) :
    axMap25 ax ⟨8 + k.val, by omega⟩ = ⟨24 + 8 * ax.val + k.val, by omega⟩ := by
  fin_cases ax <;> fin_cases k <;> rfl
end IrreducibleDaddaOpt
attribute [local irreducible] pAxis25 poolSum
theorem pPre304_fwd_props (γ : BitAssignment 304) : ∃ γ1 : BitAssignment 304, pPre304.fwdBits γ =
    γ1 /\ (∀ ax : Fin 3, ∀ u : Fin 25, γ1 (axMap25 ax u) = pAxis25.fwdBits (fun q =>
    γ (axMap25 ax q)) u) /\ (∀ w : Wire 304, (w.val = 48 \/ w.val = 49 \/ 77 <= w.val) -> γ1 w =
    γ w) := by
  obtain ⟨hinj, _, hdisj, _, _, _⟩ := axMap_facts
  have out (a b : Fin 3) (h : a ≠ b) (β) (v) :
      (mapCP (axMap25 a) pAxis25).fwdBits β (axMap25 b v) = β (axMap25 b v) :=
    mapCP_fwd_outside _ (hinj a) _ _ _ fun q ↦ hdisj a b h q v
  refine ⟨_, by rw [pPre304_eq_xnor,
    cpOfList_fwdBits_3_xnor], fun ax u ↦ ?_, fun w hw ↦ ?_⟩
  · fin_cases ax <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      out 2 0 (by decide), out 1 0 (by decide), out 2 1 (by decide),
      mapCP_fwd_apply _ (hinj _), out 0 1 (by decide), out 1 2 (by decide), out 0 2 (by decide)]
  · rw [mapCP_fwd_outside _ (hinj 2) _ _ _ (axMap25_out_ge77 2 w hw),
      mapCP_fwd_outside _ (hinj 1) _ _ _ (axMap25_out_ge77 1 w hw),
      mapCP_fwd_outside _ (hinj 0) _ _ _ (axMap25_out_ge77 0 w hw)]
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
end

end ScopedLocalHelpers
end
