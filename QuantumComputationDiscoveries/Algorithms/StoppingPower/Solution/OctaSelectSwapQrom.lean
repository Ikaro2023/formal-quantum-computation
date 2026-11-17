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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DyadicOrbitTableCert
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.NumberTheory.Niven
public import Mathlib.Topology.Compactness.Compact

set_option Elab.async false
@[expose] public section
set_option allowUnsafeReducibility true
set_option maxRecDepth 16384

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModOctahedralSelectSwapQrom
@[expose] public section
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace OctahedralOrbit
variable {Var : Type} {n : ℕ}
def regInit {m : ℕ} (r : QRegister (m + 1) n) : QRegister m n :=
  r.compose ⟨Fin.castSucc, Fin.castSucc_injective m⟩
@[simp] theorem regInit_apply {m : ℕ} (r : QRegister (m + 1) n) (i : Fin m) :
    regInit r i = r i.castSucc := rfl
@[simp] theorem basisOutcomeProjector_regZero (r : QRegister 0 n) :
    r.basisOutcomeProjector 0 = 1 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal]
  simp [show ∀ g : Fin (2 ^ n), r.extractIndex g = 0 from fun _ ↦ Fin.ext (by omega)]
theorem basisOutcomeProjector_regSucc {m : ℕ} (r : QRegister (m + 1) n) :
    r.basisOutcomeProjector 0 = (regInit r).basisOutcomeProjector 0 *
    (QRegister.singleton (r (Fin.last m))).basisOutcomeProjector 0 := by
  simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
  have hiff : r.extractIndex g = 0 ↔ (regInit r).extractIndex g = 0 ∧
      (QRegister.singleton (r (Fin.last m))).extractIndex g = 0 := by
    simp only [QRegExt.extractIndex_eq_zero_iff, regInit_apply, QRegister.singleton_apply]
    exact ⟨fun h ↦ ⟨fun i ↦ h i.castSucc, fun _ ↦ h (Fin.last m)⟩,
      fun ⟨hi, hl⟩ i ↦ Fin.lastCases (hl 0) hi i⟩
  by_cases h₁ : (regInit r).extractIndex g = 0 <;> simp [hiff, h₁]
theorem restrictAssertionToZeroAncilla_regSucc {m : ℕ}
    (M : CQAssertionCompat Var (2 ^ n)) (r : QRegister (m + 1) n) :
    CQAssertion.restrictToZeroAncilla M r = CQAssertion.restrictToZeroAncilla
    (CQAssertion.restrictToZeroAncilla M (regInit r)) (QRegister.singleton (r (Fin.last m))) := by
  funext σ
  apply Subtype.ext
  simp only [CQAssertion.restrictToZeroAncilla_coe, conj_conj]
  rw [basisOutcomeProjector_regSucc, QRegExt.basisOutcomeProjector_comm]
def PreservesZeroAncilla {m : ℕ} (rAnc : QRegister m n) (c : Circuit n) : Prop :=
  rAnc.basisOutcomeProjector 0 * (c.eval.1 * rAnc.basisOutcomeProjector 0) =
    c.eval.1 * rAnc.basisOutcomeProjector 0
theorem PreservesZeroAncilla.identity {m : ℕ} (rAnc : QRegister m n) :
    PreservesZeroAncilla rAnc .identity := by
  simp [PreservesZeroAncilla, QRegister.basisOutcomeProjector_mul_self]
theorem PreservesZeroAncilla.seq {m : ℕ} {rAnc : QRegister m n} {c₁ c₂ : Circuit n}
    (h₁ : PreservesZeroAncilla rAnc c₁) (h₂ : PreservesZeroAncilla rAnc c₂) :
    PreservesZeroAncilla rAnc (c₁ ;;ᶜ c₂) := by
  dsimp only [PreservesZeroAncilla] at h₁ h₂ ⊢
  rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc c₂.eval.1, ← h₁,
    ← Matrix.mul_assoc c₂.eval.1, ← Matrix.mul_assoc _ _ (c₁.eval.1 * _), h₂,
    Matrix.mul_assoc, h₁]
theorem PreservesZeroAncilla.of_not_mem_support {m : ℕ} {rAnc : QRegister m n} {c : Circuit n}
    (hc : ∀ i : Fin m, rAnc i ∉ c.support) : PreservesZeroAncilla rAnc c := by
  dsimp only [PreservesZeroAncilla]
  rw [DynCircuitExt.circuit_eval_comm_basisOutcomeProjector_of_not_mem_support c rAnc 0 hc,
    ← Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self]
theorem PreservesZeroAncilla.regZero {c : Circuit n} (rAnc : QRegister 0 n) :
    PreservesZeroAncilla rAnc c := by
  simp [PreservesZeroAncilla]
private theorem preserves_mul_comm {P₁ P₂ U : Operator (2 ^ n)} (hcomm : P₁ * P₂ = P₂ * P₁)
    (h₁ : P₁ * (U * P₁) = U * P₁) (h₂ : P₂ * (U * P₂) = U * P₂) :
    (P₁ * P₂) * (U * (P₁ * P₂)) = U * (P₁ * P₂) := by
  have hr : U * P₂ * P₁ = (U * P₁) * P₂ := by
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc]
  have ha : (P₁ * P₂) * (U * (P₁ * P₂)) = P₁ * ((P₂ * (U * P₂)) * P₁) := by
    nth_rw 2 [hcomm]
    simp only [Matrix.mul_assoc]
  rw [ha, h₂, hr, ← Matrix.mul_assoc P₁ (U * P₁) P₂, h₁, Matrix.mul_assoc]
theorem PreservesZeroAncilla.regSucc {m : ℕ} {rAnc : QRegister (m + 1) n} {c : Circuit n}
    (hinit : PreservesZeroAncilla (regInit rAnc) c) (hlast : PreservesZeroAncilla
    (QRegister.singleton (rAnc (Fin.last m))) c) : PreservesZeroAncilla rAnc c := by
  dsimp only [PreservesZeroAncilla] at hinit hlast ⊢
  rw [basisOutcomeProjector_regSucc]
  exact preserves_mul_comm (QRegExt.basisOutcomeProjector_comm _ 0 _ 0) hinit hlast
theorem restrictAssertionToZeroAncilla_wp_qAssign_of_preservesZeroAncilla [Fintype Var]
    {m : ℕ} (rAnc : QRegister m n) (c : Circuit n) (hc : PreservesZeroAncilla rAnc c)
    (Ψ : CQAssertionCompat Var (2 ^ n)) : CQAssertion.restrictToZeroAncilla
    (wpQAssignCompat c.eval (CQAssertion.restrictToZeroAncilla Ψ rAnc)) rAnc =
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Ψ) rAnc := by
  refine funext fun σ ↦ Subtype.ext ?_
  have hadj : rAnc.basisOutcomeProjector 0 * c.eval.1ᴴ * rAnc.basisOutcomeProjector 0 =
      rAnc.basisOutcomeProjector 0 * c.eval.1ᴴ := by
    simpa only [conjTranspose_mul, rAnc.basisOutcomeProjector_conjTranspose 0,
      ← Matrix.mul_assoc] using congrArg conjTranspose hc
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  rw [← Matrix.mul_assoc, hadj]
def ReadOnlyWire (q : Wire n) (c : Circuit n) : Prop := ∀ o : Fin 2, c.eval.1 *
    (QRegister.singleton q).basisOutcomeProjector o =
    (QRegister.singleton q).basisOutcomeProjector o * c.eval.1
private theorem readOnly_of_ket_update {q wAnc : Wire n} {c : Circuit n}
    (f : BitAssignment n → ZMod 2) (hq : q ≠ wAnc)
    (hc : ∀ β, c.eval.1.mulVec (ket β) = ket (Function.update β wAnc (f β))) :
    ReadOnlyWire q c := fun o ↦ matrix_ext_ket fun β ↦ by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projector, hc]
  by_cases hβ : β q = (o.val : ZMod 2) <;>
    simp only [hβ, ↓reduceIte, hc, Matrix.mulVec_zero, ket_projector, Function.update_of_ne hq]
theorem ReadOnlyWire.identity (q : Wire n) : ReadOnlyWire q .identity := fun _ ↦ by simp
theorem ReadOnlyWire.seq {q : Wire n} {c₁ c₂ : Circuit n}
    (h₁ : ReadOnlyWire q c₁) (h₂ : ReadOnlyWire q c₂) : ReadOnlyWire q (c₁ ;;ᶜ c₂) := fun o ↦ by
  rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, h₁ o, ← Matrix.mul_assoc,
    h₂ o, Matrix.mul_assoc]
theorem ReadOnlyWire.of_not_mem_support {q : Wire n} {c : Circuit n}
    (hq : q ∉ c.support) : ReadOnlyWire q c := fun o ↦
  DynCircuitExt.circuit_eval_comm_basisOutcomeProjector_of_not_mem_support
    c (QRegister.singleton q) o fun i ↦ by rwa [Subsingleton.elim i 0]
theorem ReadOnlyWire.preservesZeroAncilla {q : Wire n} {c : Circuit n}
    (h : ReadOnlyWire q c) : PreservesZeroAncilla (QRegister.singleton q) c := by
  dsimp only [PreservesZeroAncilla]
  rw [h 0, ← Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self]
theorem ReadOnlyWire.cnot {q c t : Wire n} (hct : c ≠ t) (hqt : q ≠ t) :
    ReadOnlyWire q (Circuit.CNOT c t hct) := readOnly_of_ket_update _ hqt (ket_CNOT c t hct)
theorem ReadOnlyWire.toffoli {q c₁ c₂ t : Wire n} (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t)
    (h₂t : c₂ ≠ t) (hqt : q ≠ t) : ReadOnlyWire q (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t) :=
  readOnly_of_ket_update _ hqt (ket_TOFF c₁ c₂ t h₁₂ h₁t h₂t)
theorem ReadOnlyWire.x {q t : Wire n} (hqt : q ≠ t) : ReadOnlyWire q (Circuit.X t) :=
  ReadOnlyWire.of_not_mem_support (by simp [hqt])
theorem ReadOnlyWire.projector_mulVec_eq {q : Wire n} {c : Circuit n} (hc : ReadOnlyWire q c)
    (o : Fin 2) (ψ : Fin (2 ^ n) → ℂ) (hψ : ((QRegister.singleton q).basisOutcomeProjector
    o).mulVec ψ = ψ) : ((QRegister.singleton q).basisOutcomeProjector o).mulVec
    (c.eval.1.mulVec ψ) = c.eval.1.mulVec ψ := by
  rw [Matrix.mulVec_mulVec, ← hc o, ← Matrix.mulVec_mulVec, hψ]
private theorem lemHex141 [Finite Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ ancilla : Wire n) (h₁₂ : control₁ ≠ control₂)
    (Θ : CQAssertionCompat Var (2 ^ n)) (σ : Store Var) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1
    let L₀ := P₀ * (Circuit.H ancilla).eval.1
    let L₁ := (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁ *
      (Circuit.H ancilla).eval.1
    (wp (DynamicCircuit.andUncompute v control₁ control₂ ancilla h₁₂).compile Θ σ).1 =
      (Θ (Function.update σ v 0)).1.conj L₀ᴴ +
        (Θ (Function.update σ v 1)).1.conj L₁ᴴ := by
  cases nonempty_fintype Var
  intro P₀ P₁ L₀ L₁
  let F := Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂
  have hs : σ.subst v 0 = Function.update σ v 0 ∧ σ.subst v 1 = Function.update σ v 1 :=
    ⟨funext fun _ ↦ by simp [Store.subst, Function.update],
      funext fun _ ↦ by simp [Store.subst, Function.update]⟩
  have hmeas_apply : (wp (.qSeq (QProg.measureRegister v (QRegister.singleton ancilla))
      (qprogQIfVar v F.compile .skip)) Θ σ).1 = (Θ (Function.update σ v 0)).1.conj P₀ᴴ +
      ((Θ (Function.update σ v 1)).1.conj F.eval.1ᴴ).conj P₁ᴴ := by
    simp only [wp_qSeq, wp_qIf, wp_skip, QProg.measureRegister, wp_qMeasure_apply,
      qMeasure_obs_map_coe, CQAssertionCompat.subst_apply]
    change ∑ o : Fin 2, _ = _
    rw [Fin.sum_univ_two]
    simp [qMeasure_outcome_herm_eq_conj, hs.1, hs.2, wpQAssignCompat, qAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      QRegister.computationalBasisMeasurement_apply, P₀, P₁, F]
  change (wp (Circuit.H ancilla).compile
    (wp (.qSeq (QProg.measureRegister v (QRegister.singleton ancilla))
      (qprogQIfVar v F.compile .skip)) Θ) σ).1 = _
  rw [DynCircuitExt.wp_circuit_compile_compat]
  simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose]
  rw [hmeas_apply, map_add, conj_conj, conj_conj, conj_conj]
  dsimp only [L₀, L₁, F]
  simp only [Matrix.mul_assoc, conjTranspose_mul]
private theorem lemHex141b [Finite Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    (v : Var) (control₁ control₂ ancilla : Wire n) (h₁₂ : control₁ ≠ control₂)
    (rSubAnc : QRegister m n) (hc₁ : ∀ i, rSubAnc i ≠ control₁)
    (hc₂ : ∀ i, rSubAnc i ≠ control₂) (ha : ∀ i, rSubAnc i ≠ ancilla)
    (Θ : CQAssertionCompat Var (2 ^ n)) :
    wp (DynamicCircuit.andUncompute v control₁ control₂ ancilla h₁₂).compile
      (CQAssertion.restrictToZeroAncilla Θ rSubAnc) =
    CQAssertion.restrictToZeroAncilla
      (wp (DynamicCircuit.andUncompute v control₁ control₂ ancilla h₁₂).compile Θ) rSubAnc := by
  cases nonempty_fintype Var
  refine funext fun σ ↦ Subtype.ext ?_
  let P_sub := rSubAnc.basisOutcomeProjector 0
  have hP_herm : P_subᴴ = P_sub := rSubAnc.basisOutcomeProjector_conjTranspose 0
  have cm {A B : Operator (2 ^ n)} (hA : A * P_sub = P_sub * A) (hB : B * P_sub = P_sub * B) :
      (A * B) * P_sub = P_sub * (A * B) := by
    rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  have hadj {L : Operator (2 ^ n)} (h : L * P_sub = P_sub * L) : P_sub * Lᴴ = Lᴴ * P_sub := by
    simpa only [conjTranspose_mul, hP_herm] using congrArg conjTranspose h
  have hH : (Circuit.H ancilla).eval.1 * P_sub = P_sub * (Circuit.H ancilla).eval.1 :=
    DynCircuitExt.circuit_eval_comm_basisOutcomeProjector_of_not_mem_support
      (Circuit.H ancilla) rSubAnc 0 (fun i ↦ by simp [ha i])
  have hFix : (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P_sub =
      P_sub * (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 :=
    DynCircuitExt.circuit_eval_comm_basisOutcomeProjector_of_not_mem_support
      (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂) rSubAnc 0
      (fun i ↦ by simp [Circuit.andUncomputeFixup, hc₁ i, hc₂ i, ha i])
  have hP0 : (QRegister.singleton ancilla).basisOutcomeProjector 0 * P_sub =
      P_sub * (QRegister.singleton ancilla).basisOutcomeProjector 0 :=
    QRegExt.basisOutcomeProjector_comm (QRegister.singleton ancilla) 0 rSubAnc 0
  have hP1 : (QRegister.singleton ancilla).basisOutcomeProjector 1 * P_sub =
      P_sub * (QRegister.singleton ancilla).basisOutcomeProjector 1 :=
    QRegExt.basisOutcomeProjector_comm (QRegister.singleton ancilla) 1 rSubAnc 0
  let L₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0 * (Circuit.H ancilla).eval.1
  let L₁ := (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 *
    (QRegister.singleton ancilla).basisOutcomeProjector 1 * (Circuit.H ancilla).eval.1
  have hL₀ : P_sub * L₀ᴴ = L₀ᴴ * P_sub := hadj (cm hP0 hH)
  have hL₁ : P_sub * L₁ᴴ = L₁ᴴ * P_sub := hadj (cm (cm hFix hP1) hH)
  dsimp only [P_sub, L₀, L₁] at hL₀ hL₁
  simp only [CQAssertion.restrictToZeroAncilla_coe]
  rw [lemHex141, lemHex141, map_add]
  simp only [CQAssertion.restrictToZeroAncilla_coe, conj_conj]
  rw [← hL₀, ← hL₁]
theorem restrictAssertionToZeroAncilla_wp_andCompute_dyn_andUncompute_of_update_eq
    [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (rSubAnc : QRegister m n) (hc₁ : ∀ i, rSubAnc i ≠ control₁)
    (hc₂ : ∀ i, rSubAnc i ≠ control₂) (ha : ∀ i, rSubAnc i ≠ ancilla)
    (dBody : DynamicCircuit Var n) (cBody : Circuit n)
    (hdBody : ∀ Ψ : CQAssertionCompat Var (2 ^ n),
      (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
      CQAssertion.restrictToZeroAncilla (wp dBody.compile Ψ) rSubAnc =
        CQAssertion.restrictToZeroAncilla (wpQAssignCompat cBody.eval Ψ) rSubAnc)
    (hcBody_sub : PreservesZeroAncilla rSubAnc cBody)
    (hcBody_anc :
      let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1
      P₀ * (T_anc * cBody.eval.1 * T_anc * P₀) = T_anc * cBody.eval.1 * T_anc * P₀)
    (Θ : CQAssertionCompat Var (2 ^ n)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToZeroAncilla
      (wp (DynamicCircuit.seq (DynamicCircuit.andCompute control₁ control₂ ancilla h₁a h₂a)
        (DynamicCircuit.seq dBody
          (DynamicCircuit.andUncompute v control₁ control₂ ancilla h₁₂))).compile Θ) rSubAnc)
      (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat
        (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a ;;ᶜ
          cBody ;;ᶜ
          Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval Θ) rSubAnc)
      (QRegister.singleton ancilla) := by
  have hAnd_comm := DynCircuitExt.circuit_eval_comm_basisOutcomeProjector_of_not_mem_support
    (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a) rSubAnc 0
    (fun i ↦ by simp [hc₁ i, hc₂ i, ha i])
  have hToff_sub : PreservesZeroAncilla rSubAnc
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a) :=
    PreservesZeroAncilla.of_not_mem_support (fun i ↦ by simp [hc₁ i, hc₂ i, ha i])
  have hΘ'_upd : ∀ σ val, CQAssertion.restrictToZeroAncilla Θ rSubAnc (Function.update σ v val) =
      CQAssertion.restrictToZeroAncilla Θ rSubAnc σ := fun σ val ↦ Subtype.ext (by
    simp [CQAssertion.restrictToZeroAncilla_coe, hΘ σ val])
  have hStep1 : CQAssertion.restrictToZeroAncilla (wp (DynamicCircuit.seq
      (DynamicCircuit.andCompute control₁ control₂ ancilla h₁a h₂a) (DynamicCircuit.seq dBody
      (DynamicCircuit.andUncompute v control₁ control₂ ancilla h₁₂))).compile Θ) rSubAnc =
      CQAssertion.restrictToZeroAncilla (wp (DynamicCircuit.seq (DynamicCircuit.andCompute
      control₁ control₂ ancilla h₁a h₂a) (DynamicCircuit.seq (.circuit cBody)
      (DynamicCircuit.andUncompute v control₁ control₂ ancilla h₁₂))).compile
      (CQAssertion.restrictToZeroAncilla Θ rSubAnc)) rSubAnc := by
    simp only [DynamicCircuit.compile_seq, DynamicCircuit.andCompute,
      DynamicCircuit.compile_circuit, wp_qSeq, DynCircuitExt.wp_circuit_compile_compat]
    rw [← DynCircuitExt.wp_qAssign_restrictAssertionToZeroAncilla_comm _ rSubAnc hAnd_comm,
      hdBody _ (fun σ val ↦ DynamicCircuit.wp_andUncompute_update_self v control₁ control₂
        ancilla h₁₂ Θ σ val),
      ← restrictAssertionToZeroAncilla_wp_qAssign_of_preservesZeroAncilla rSubAnc cBody hcBody_sub,
      ← lemHex141b v control₁ control₂ ancilla h₁₂ rSubAnc hc₁ hc₂ ha Θ,
      DynCircuitExt.wp_qAssign_restrictAssertionToZeroAncilla_comm _ rSubAnc hAnd_comm]
  rw [hStep1, restrictAssertionToZeroAncilla_comm, (open DynamicCircuit in
    restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq_compat
      v control₁ control₂ ancilla h₁₂ h₁a h₂a cBody hcBody_anc _ hΘ'_upd),
    ← restrictAssertionToZeroAncilla_comm,
    restrictAssertionToZeroAncilla_wp_qAssign_of_preservesZeroAncilla rSubAnc _
      (hToff_sub.seq (hcBody_sub.seq hToff_sub))]
theorem regInit_ne_last {k : ℕ} (r : QRegister (k + 1) n) (i : Fin k) : regInit r i ≠ r
    (Fin.last k) := fun h ↦ Fin.castSucc_ne_last i (r.wires.injective h)
theorem last_not_mem_range_regInit {k : ℕ} (r : QRegister (k + 1) n) : r (Fin.last k) ∉
    Set.range (regInit r).wires := fun ⟨i, hi⟩ ↦ regInit_ne_last r i hi
theorem not_mem_range_regInit_of_not_mem {k : ℕ} {r : QRegister (k + 1) n} {w : Wire n}
    (hw : w ∉ Set.range r.wires) : w ∉ Set.range (regInit r).wires :=
  fun ⟨i, hi⟩ ↦ hw ⟨i.castSucc, hi⟩
theorem not_mem_of_disjoint {k m : ℕ} {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (i : Fin k) : r i ∉ Set.range s.wires :=
  fun ⟨j, hj⟩ ↦ h.ne i j hj.symm
@[simp] theorem writeReg_zero (β : BitAssignment n) (r : QRegister 0 n) (γ : BitAssignment 0) :
    writeReg β r γ = β :=
  funext fun _ ↦ writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, _⟩ ↦ i.elim0
theorem writeReg_castSucc {k : ℕ} (β : BitAssignment n) (r : QRegister (k + 1) n)
    (γ : BitAssignment (k + 1)) : writeReg β r γ = Function.update
    (writeReg β (regInit r) (fun i ↦ γ i.castSucc)) (r (Fin.last k)) (γ (Fin.last k)) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · rcases hw with ⟨i, rfl⟩
    rw [writeReg_apply_reg]
    refine Fin.lastCases (by simp) (fun j ↦ ?_) i
    rw [← regInit_apply, Function.update_of_ne (regInit_ne_last r j), writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw,
      Function.update_of_ne (fun h ↦ hw ⟨Fin.last k, h.symm⟩),
      writeReg_apply_of_not_mem _ _ _ _ (not_mem_range_regInit_of_not_mem hw)]
theorem localIdx_val {k : ℕ} (r : QRegister k n) (β : BitAssignment n) :
    (localIdx r β : ℕ) = ∑ i : Fin k, (β (r i)).val * 2 ^ (i : ℕ) := by
  simp [localIdx, basisBits, ZMod.finEquiv]
  rfl
theorem localIdx_val_castSucc {k : ℕ} (r : QRegister (k + 1) n) (β : BitAssignment n) :
    (localIdx r β : ℕ) = (localIdx (regInit r) β : ℕ) + (β (r (Fin.last k))).val * 2 ^ k := by
  rw [localIdx_val, localIdx_val, Fin.sum_univ_castSucc]
  rfl
theorem localIdx_update_of_not_mem {k : ℕ} (r : QRegister k n) (β : BitAssignment n)
    {w : Wire n} (hw : w ∉ Set.range r.wires) (x : ZMod 2) :
    localIdx r (Function.update β w x) = localIdx r β := by
  simp only [localIdx]
  exact congrArg _ (funext fun i ↦ Function.update_of_ne (fun h ↦ hw ⟨i, h⟩) _ _)
theorem localIdx_writeReg_of_disjoint {k m : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (s : QRegister m n) (hdisj : r.DisjointWires s) (γ : BitAssignment k) : localIdx s
    (writeReg β r γ) = localIdx s β := by
  simp only [localIdx]
  exact congrArg _ (funext fun i ↦
    writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hdisj) i))
theorem ReadOnlyWire.of_eval_mulVec_ket_update {q wAnc : Wire n} {c : Circuit n}
    (f : BitAssignment n → ZMod 2) (hq : q ≠ wAnc) (hc : ∀ β, c.eval.1.mulVec (ket β) = ket
    (Function.update β wAnc (f β))) : ReadOnlyWire q c :=
  readOnly_of_ket_update f hq hc
def ctrlVal : Option (Wire n) → BitAssignment n → ZMod 2
  | none, _ => 1
  | some wCtrl, β => β wCtrl
def CtrlNe (c : Option (Wire n)) (w : Wire n) : Prop := ∀ c₀, c = some c₀ → c₀ ≠ w
theorem CtrlNe.none (w : Wire n) : CtrlNe none w :=
  fun _ h ↦ nomatch h
theorem CtrlNe.some {a w : Wire n} (h : a ≠ w) : CtrlNe (some a) w :=
  fun _ h' ↦ Option.some.inj h' ▸ h
def wireBitFin (b : ZMod 2) : Fin 2 := if b = 0 then 0 else 1
@[simp] theorem wireBitFin_zero : wireBitFin 0 = 0 := rfl
@[simp] theorem wireBitFin_one : wireBitFin 1 = 1 := rfl
theorem wireBitFin_val (b : ZMod 2) : ((wireBitFin b).val : ZMod 2) = b := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> rfl
def HasWireBit (q : Wire n) (b : ZMod 2) (ψ : Fin (2 ^ n) → ℂ) : Prop :=
  ((QRegister.singleton q).basisOutcomeProjector (wireBitFin b)).mulVec ψ = ψ
theorem HasWireBit.ket (q : Wire n) (β : BitAssignment n) : HasWireBit q (β q) (ket β) := by
  simp only [HasWireBit, ket_projector, wireBitFin_val, ↓reduceIte]
theorem HasWireBit.readOnly {q : Wire n} {b : ZMod 2} {c : Circuit n} {ψ : Fin (2 ^ n) → ℂ}
    (hc : ReadOnlyWire q c) (hψ : HasWireBit q b ψ) : HasWireBit q b (c.eval.1.mulVec ψ) :=
  hc.projector_mulVec_eq (wireBitFin b) ψ hψ
private theorem zmod2_add_one_add_one (b : ZMod 2) : b + 1 + 1 = b := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide
private theorem HasWireBit.of_proj_eq {t : Wire n} {bt' : ZMod 2} {U P : Operator (2 ^ n)}
    {ψ : Fin (2 ^ n) → ℂ} (hψ : P.mulVec ψ = ψ)
    (hmat : (QRegister.singleton t).basisOutcomeProjector (wireBitFin bt') * (U * P) = U * P) :
    HasWireBit t bt' (U.mulVec ψ) := by
  dsimp only [HasWireBit]
  rw [← hψ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hmat,
    ← Matrix.mulVec_mulVec, hψ]
theorem HasWireBit.x_self {q : Wire n} {b : ZMod 2} {ψ : Fin (2 ^ n) → ℂ}
    (hψ : HasWireBit q b ψ) : HasWireBit q (b + 1) ((Circuit.X q).eval.1.mulVec ψ) := by
  refine HasWireBit.of_proj_eq hψ (matrix_ext_ket fun β ↦ ?_)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projector]
  by_cases hβ : β q = ((wireBitFin b).val : ZMod 2)
  · rw [wireBitFin_val] at hβ
    simp only [hβ, ↓reduceIte, ket_X, ket_projector, Function.update_self, wireBitFin_val]
  · simp only [hβ, ↓reduceIte, Matrix.mulVec_zero]
theorem HasWireBit.cnot_target {c t : Wire n} (hct : c ≠ t) {bc bt : ZMod 2}
    {ψ : Fin (2 ^ n) → ℂ} (hc : HasWireBit c bc ψ) (ht : HasWireBit t bt ψ) :
    HasWireBit t (bt + bc) ((Circuit.CNOT c t hct).eval.1.mulVec ψ) := by
  refine HasWireBit.of_proj_eq (P := (QRegister.singleton t).basisOutcomeProjector (wireBitFin bt) *
      (QRegister.singleton c).basisOutcomeProjector (wireBitFin bc))
    (by rw [← Matrix.mulVec_mulVec, hc, ht]) (matrix_ext_ket fun β ↦ ?_)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projector]
  by_cases hβc : β c = ((wireBitFin bc).val : ZMod 2)
  · simp only [hβc, ↓reduceIte, ket_projector]
    by_cases hβt : β t = ((wireBitFin bt).val : ZMod 2)
    · rw [wireBitFin_val] at hβc hβt
      simp only [hβc, hβt, ↓reduceIte, ket_CNOT, ket_projector, Function.update_self,
        wireBitFin_val]
    · simp only [hβt, ↓reduceIte, Matrix.mulVec_zero]
  · simp only [hβc, ↓reduceIte, Matrix.mulVec_zero]
theorem HasWireBit.toffoli_target {c₁ c₂ t : Wire n} (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t)
    (h₂t : c₂ ≠ t) {b₁ b₂ bt : ZMod 2} {ψ : Fin (2 ^ n) → ℂ} (h₁ : HasWireBit c₁ b₁ ψ)
    (h₂ : HasWireBit c₂ b₂ ψ) (ht : HasWireBit t bt ψ) : HasWireBit t (bt + b₁ * b₂)
    ((Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec ψ) := by
  refine HasWireBit.of_proj_eq
    (P := (QRegister.singleton t).basisOutcomeProjector (wireBitFin bt) *
      ((QRegister.singleton c₂).basisOutcomeProjector (wireBitFin b₂) *
        (QRegister.singleton c₁).basisOutcomeProjector (wireBitFin b₁)))
    (by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h₁, h₂, ht]) (matrix_ext_ket fun β ↦ ?_)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ket_projector]
  by_cases hβ1 : β c₁ = ((wireBitFin b₁).val : ZMod 2)
  · simp only [hβ1, ↓reduceIte, ket_projector]
    by_cases hβ2 : β c₂ = ((wireBitFin b₂).val : ZMod 2)
    · simp only [hβ2, ↓reduceIte, ket_projector]
      by_cases hβt : β t = ((wireBitFin bt).val : ZMod 2)
      · rw [wireBitFin_val] at hβ1 hβ2 hβt
        simp only [hβ1, hβ2, hβt, ↓reduceIte, ket_TOFF, ket_projector, Function.update_self,
          wireBitFin_val]
      · simp only [hβt, ↓reduceIte, Matrix.mulVec_zero]
    · simp only [hβ2, ↓reduceIte, Matrix.mulVec_zero]
  · simp only [hβ1, ↓reduceIte, Matrix.mulVec_zero]
theorem andNotNone_eval_mulVec_ket (wMsb wAnc : Wire n) (hMsbAnc : wMsb ≠ wAnc)
    (β : BitAssignment n) :
    ((Circuit.X wMsb).seq ((Circuit.CNOT wMsb wAnc hMsbAnc).seq (Circuit.X wMsb))).eval.1.mulVec
      (ket β) = ket (Function.update β wAnc (β wAnc + (β wMsb + 1))) := by
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_X, ket_CNOT, ket_X]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw_m : w = wMsb
  · subst hw_m
    simp only [Function.update_self, Function.update_of_ne hMsbAnc, zmod2_add_one_add_one]
  · by_cases hw_a : w = wAnc
    · subst hw_a
      simp only [Function.update_of_ne hMsbAnc.symm, Function.update_self]
    · simp only [Function.update_of_ne hw_m, Function.update_of_ne hw_a]
theorem andNotSome_eval_mulVec_ket (wCtrl wMsb wAnc : Wire n)
    (hCtrlMsb : wCtrl ≠ wMsb) (hCtrlAnc : wCtrl ≠ wAnc) (hMsbAnc : wMsb ≠ wAnc)
    (β : BitAssignment n) :
    ((Circuit.X wMsb).seq ((Circuit.TOFF wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc).seq
      (Circuit.X wMsb))).eval.1.mulVec (ket β) =
      ket (Function.update β wAnc (β wAnc + β wCtrl * (β wMsb + 1))) := by
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_X, ket_TOFF, ket_X]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw_m : w = wMsb
  · subst hw_m
    simp only [Function.update_self, Function.update_of_ne hMsbAnc, zmod2_add_one_add_one]
  · by_cases hw_a : w = wAnc
    · subst hw_a
      simp only [Function.update_of_ne hMsbAnc.symm, Function.update_self,
        Function.update_of_ne hCtrlMsb]
    · simp only [Function.update_of_ne hw_m, Function.update_of_ne hw_a]
def branchMsbCircuit (c : Option (Wire n)) (wMsb wAnc : Wire n)
    (hcMsb : CtrlNe c wMsb) (hcAnc : CtrlNe c wAnc) (hMsbAnc : wMsb ≠ wAnc)
    (leftCircuit rightCircuit : Circuit n) : Circuit n :=
  match c with
  | none =>
      (Circuit.X wMsb ;;ᶜ Circuit.CNOT wMsb wAnc hMsbAnc ;;ᶜ Circuit.X wMsb) ;;ᶜ
      leftCircuit ;;ᶜ
      Circuit.X wAnc ;;ᶜ
      rightCircuit ;;ᶜ
      Circuit.CNOT wMsb wAnc hMsbAnc
  | some wCtrl =>
      Circuit.X wMsb ;;ᶜ
      (Circuit.TOFF wCtrl wMsb wAnc (hcMsb wCtrl rfl) (hcAnc wCtrl rfl) hMsbAnc ;;ᶜ
        (Circuit.X wMsb ;;ᶜ
          leftCircuit ;;ᶜ
          Circuit.CNOT wCtrl wAnc (hcAnc wCtrl rfl) ;;ᶜ
          rightCircuit) ;;ᶜ
        Circuit.TOFF wCtrl wMsb wAnc (hcMsb wCtrl rfl) (hcAnc wCtrl rfl) hMsbAnc)
def branchMsbDyn (v : Var) (c : Option (Wire n)) (wMsb wAnc : Wire n)
    (hcMsb : CtrlNe c wMsb) (hcAnc : CtrlNe c wAnc) (hMsbAnc : wMsb ≠ wAnc)
    (leftDyn rightDyn : DynamicCircuit Var n) : DynamicCircuit Var n :=
  match c with
  | none =>
      .seq (.circuit (Circuit.X wMsb ;;ᶜ Circuit.CNOT wMsb wAnc hMsbAnc ;;ᶜ Circuit.X wMsb))
        (.seq leftDyn
          (.seq (.circuit (Circuit.X wAnc))
            (.seq rightDyn
              (.circuit (Circuit.CNOT wMsb wAnc hMsbAnc)))))
  | some wCtrl =>
      .seq (.circuit (Circuit.X wMsb))
        (.seq (DynamicCircuit.andCompute wCtrl wMsb wAnc (hcAnc wCtrl rfl) hMsbAnc)
          (.seq
            (.seq (.circuit (Circuit.X wMsb))
              (.seq leftDyn
                (.seq (.circuit (Circuit.CNOT wCtrl wAnc (hcAnc wCtrl rfl)))
                  rightDyn)))
            (DynamicCircuit.andUncompute v wCtrl wMsb wAnc (hcMsb wCtrl rfl))))
@[simp] theorem count_branchMsbDyn_toff (v : Var) (c : Option (Wire n)) (wMsb wAnc : Wire n)
    (hcMsb : CtrlNe c wMsb) (hcAnc : CtrlNe c wAnc) (hMsbAnc : wMsb ≠ wAnc)
    (leftDyn rightDyn : DynamicCircuit Var n) :
    (branchMsbDyn v c wMsb wAnc hcMsb hcAnc hMsbAnc leftDyn rightDyn).count PrimitiveGate.TOFF =
      leftDyn.count PrimitiveGate.TOFF + rightDyn.count PrimitiveGate.TOFF := by
  cases c <;> simp [branchMsbDyn, Circuit.CNOT]
theorem count_branchMsbDyn_t_some (v : Var) (wCtrl wMsb wAnc : Wire n)
    (hcMsb : CtrlNe (some wCtrl) wMsb) (hcAnc : CtrlNe (some wCtrl) wAnc)
    (hMsbAnc : wMsb ≠ wAnc) (leftDyn rightDyn : DynamicCircuit Var n) : (branchMsbDyn v (some
    wCtrl) wMsb wAnc hcMsb hcAnc hMsbAnc leftDyn rightDyn).count PrimitiveGate.T = 4 +
    leftDyn.count PrimitiveGate.T + rightDyn.count PrimitiveGate.T := by
  simp [branchMsbDyn, Circuit.CNOT]
  omega
structure ValidQromTree [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) {k w : ℕ} (rW : QRegister k n) (rY : QRegister w n)
    (cTree : Circuit n) (dTree : DynamicCircuit Var n) : Prop where
  readOnly_of_ne : ∀ q : Wire n, (∀ i, q ≠ rW i) → (∀ i, q ≠ rY i) → ReadOnlyWire q cTree
  preserves_rW : PreservesZeroAncilla rW cTree
  wp_update_eq : ∀ Ψ : CQAssertionCompat Var (2 ^ n),
    (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
    ∀ σ val, wp dTree.compile Ψ (Function.update σ v val) = wp dTree.compile Ψ σ
  wp_clean : ∀ Ψ : CQAssertionCompat Var (2 ^ n),
    (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
    CQAssertion.restrictToZeroAncilla (wp dTree.compile Ψ) rW =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat cTree.eval Ψ) rW
theorem ValidQromTree.lift_regInit [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    {m w : ℕ} (v : Var) (rSub : QRegister (m + 1) n) (rY : QRegister w n)
    (hSubY : rSub.DisjointWires rY) (cTree : Circuit n) (dTree : DynamicCircuit Var n)
    (h : ValidQromTree v (regInit rSub) rY cTree dTree) :
    ValidQromTree v rSub rY cTree dTree :=
  ⟨fun q hqSub hqY ↦ h.readOnly_of_ne q (fun i ↦ hqSub i.castSucc) hqY,
    PreservesZeroAncilla.regSucc h.preserves_rW
      ((h.readOnly_of_ne (rSub (Fin.last m)) (fun i ↦ (regInit_ne_last rSub i).symm)
        (fun i ↦ hSubY.ne (Fin.last m) i)).preservesZeroAncilla),
    h.wp_update_eq, fun Ψ hΨ ↦ by
      rw [restrictAssertionToZeroAncilla_regSucc, h.wp_clean Ψ hΨ,
        ← restrictAssertionToZeroAncilla_regSucc]⟩
theorem ReadOnlyWire.of_eval_eq {q : Wire n} {c₁ c₂ : Circuit n} (heq : c₁.eval.1 = c₂.eval.1)
    (h : ReadOnlyWire q c₂) : ReadOnlyWire q c₁ := fun o ↦ heq ▸ h o
private theorem lemHex142 [Finite Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (c : Circuit n) (Ψ : CQAssertionCompat Var (2 ^ n))
    (hΨ : ∀ σ val, Ψ (Function.update σ v val) = Ψ σ) (σ : Store Var) (val : ℤ) :
    wp c.compile Ψ (Function.update σ v val) = wp c.compile Ψ σ := by
  cases nonempty_fintype Var
  rw [DynCircuitExt.wp_circuit_compile_compat]
  exact Subtype.ext (by simp [wpQAssignCompat, qAssignObsMap, hΨ σ val])
private theorem lemHex146 [Fintype Var] [DecidableEq Var] {m : ℕ}
    (rSub : QRegister m n) (c : Circuit n) (Ψ : CQAssertionCompat Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla (wp (DynamicCircuit.circuit c).compile Ψ) rSub =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Ψ) rSub := by
  simp only [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
/-- Bundled sub-ancilla preservation, classical variable invariance, and clean `wp` simulation. -/
def SubDynClean [Fintype Var] [DecidableEq Var] {m : ℕ}
    (v : Var) (rSub : QRegister m n) (c : Circuit n) (d : DynamicCircuit Var n) : Prop :=
  PreservesZeroAncilla rSub c ∧
  (∀ Ψ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
    ∀ σ val, wp d.compile Ψ (Function.update σ v val) = wp d.compile Ψ σ) ∧
  (∀ Ψ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
    CQAssertion.restrictToZeroAncilla (wp d.compile Ψ) rSub =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Ψ) rSub)
private theorem SubDynClean.of_valid [Fintype Var] [DecidableEq Var] {m w : ℕ}
    {v : Var} {rSub : QRegister m n} {rY : QRegister w n} {c : Circuit n} {d : DynamicCircuit Var n}
    (h : ValidQromTree v rSub rY c d) : SubDynClean v rSub c d :=
  ⟨h.preserves_rW, h.wp_update_eq, h.wp_clean⟩
private theorem SubDynClean.of_circuit [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    (v : Var) {rSub : QRegister m n} {c : Circuit n} (hc : PreservesZeroAncilla rSub c) :
    SubDynClean v rSub c (.circuit c) :=
  ⟨hc, fun Ψ hΨ ↦ lemHex142 v c Ψ hΨ, fun Ψ _ ↦ lemHex146 rSub c Ψ⟩
theorem SubDynClean.seq [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    {v : Var} {rSub : QRegister m n} {c₁ c₂ : Circuit n} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : SubDynClean v rSub c₁ d₁) (h₂ : SubDynClean v rSub c₂ d₂) :
    SubDynClean v rSub (c₁.seq c₂) (.seq d₁ d₂) :=
  ⟨h₁.1.seq h₂.1,
    fun Ψ hΨ σ val ↦ by
      simp only [DynamicCircuit.compile_seq, wp_qSeq]
      exact h₁.2.1 _ (h₂.2.1 Ψ hΨ) σ val,
    fun Ψ hΨ ↦ by
      simp only [DynamicCircuit.compile_seq, wp_qSeq, Circuit.eval_seq]
      rw [h₁.2.2 (wp d₂.compile Ψ) (h₂.2.1 Ψ hΨ),
        ← restrictAssertionToZeroAncilla_wp_qAssign_of_preservesZeroAncilla rSub c₁ h₁.1,
        h₂.2.2 Ψ hΨ,
        restrictAssertionToZeroAncilla_wp_qAssign_of_preservesZeroAncilla rSub c₁ h₁.1,
        wpQAssignCompat_comp]⟩
theorem ValidQromTree.branchMsb [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m w : ℕ}
    (v : Var) (c : Option (Wire n)) (rX rW : QRegister (m + 1) n) (rY : QRegister w n)
    (hXW : rX.DisjointWires rW) (hXY : rX.DisjointWires rY) (hWY : rW.DisjointWires rY)
    (hcX : ∀ i, CtrlNe c (rX i)) (hcW : ∀ i, CtrlNe c (rW i)) (hcY : ∀ i, CtrlNe c (rY i))
    (leftCircuit rightCircuit : Circuit n) (leftDyn rightDyn : DynamicCircuit Var n)
    (hL : ValidQromTree v (regInit rW) rY leftCircuit leftDyn)
    (hR : ValidQromTree v (regInit rW) rY rightCircuit rightDyn) : ValidQromTree v rW rY
    (branchMsbCircuit c (rX (Fin.last m)) (rW (Fin.last m)) (hcX (Fin.last m)) (hcW (Fin.last
    m)) (hXW.ne (Fin.last m) (Fin.last m)) leftCircuit rightCircuit) (branchMsbDyn v c (rX
    (Fin.last m)) (rW (Fin.last m)) (hcX (Fin.last m)) (hcW (Fin.last m)) (hXW.ne (Fin.last m)
    (Fin.last m)) leftDyn rightDyn) := by
  let wMsb := rX (Fin.last m)
  let wAnc := rW (Fin.last m)
  let rSub := regInit rW
  have hMsbAnc : wMsb ≠ wAnc := hXW.ne (Fin.last m) (Fin.last m)
  have hSubMsb : ∀ i, rSub i ≠ wMsb := fun i ↦ (hXW.ne (Fin.last m) i.castSucc).symm
  have hSubAnc : ∀ i, rSub i ≠ wAnc := fun i ↦ regInit_ne_last rW i
  have hLm := hL.readOnly_of_ne wMsb (fun i ↦ (hSubMsb i).symm) (fun i ↦ hXY.ne (Fin.last m) i)
  have hLa := hL.readOnly_of_ne wAnc (fun i ↦ (hSubAnc i).symm) (fun i ↦ hWY.ne (Fin.last m) i)
  have hRm := hR.readOnly_of_ne wMsb (fun i ↦ (hSubMsb i).symm) (fun i ↦ hXY.ne (Fin.last m) i)
  have hRa := hR.readOnly_of_ne wAnc (fun i ↦ (hSubAnc i).symm) (fun i ↦ hWY.ne (Fin.last m) i)
  have hXMsbSub : PreservesZeroAncilla rSub (Circuit.X wMsb) :=
    PreservesZeroAncilla.of_not_mem_support (fun i ↦ by simp [hSubMsb i])
  have hXAncSub : PreservesZeroAncilla rSub (Circuit.X wAnc) :=
    PreservesZeroAncilla.of_not_mem_support (fun i ↦ by simp [hSubAnc i])
  have hCnotMASub : PreservesZeroAncilla rSub (Circuit.CNOT wMsb wAnc hMsbAnc) :=
    PreservesZeroAncilla.of_not_mem_support (fun i ↦ by simp [Circuit.CNOT, hSubMsb i, hSubAnc i])
  cases c with
  | none =>
      have hNoneSub : SubDynClean v rSub
          (branchMsbCircuit none wMsb wAnc (CtrlNe.none wMsb) (CtrlNe.none wAnc) hMsbAnc
            leftCircuit rightCircuit)
          (branchMsbDyn v none wMsb wAnc (CtrlNe.none wMsb) (CtrlNe.none wAnc) hMsbAnc
            leftDyn rightDyn) :=
        (SubDynClean.of_circuit v (hXMsbSub.seq (hCnotMASub.seq hXMsbSub))).seq
          ((SubDynClean.of_valid hL).seq ((SubDynClean.of_circuit v hXAncSub).seq
            ((SubDynClean.of_valid hR).seq (SubDynClean.of_circuit v hCnotMASub))))
      refine ⟨fun q hqW hqY ↦ ?_, PreservesZeroAncilla.regSucc hNoneSub.1 ?_, hNoneSub.2.1,
        fun Ψ hΨ ↦ ?_⟩
      · exact (ReadOnlyWire.of_eval_mulVec_ket_update _ (hqW (Fin.last m))
          (andNotNone_eval_mulVec_ket wMsb wAnc hMsbAnc)).seq
          ((hL.readOnly_of_ne q (fun i ↦ hqW i.castSucc) hqY).seq
            ((ReadOnlyWire.x (hqW (Fin.last m))).seq ((hR.readOnly_of_ne q (fun i ↦ hqW i.castSucc)
              hqY).seq (ReadOnlyWire.cnot hMsbAnc (hqW (Fin.last m))))))
      · change PreservesZeroAncilla (QRegister.singleton wAnc) _
        dsimp only [PreservesZeroAncilla, branchMsbCircuit]
        refine matrix_ext_ket fun β ↦ ?_
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projector_zero]
        by_cases hβa : β wAnc = 0
        · simp only [hβa, ↓reduceIte]
          rw [eval_seq_mulVec, andNotNone_eval_mulVec_ket, hβa, zero_add,
            eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec]
          let β₁ := Function.update β wAnc (β wMsb + 1)
          have h1_m : HasWireBit wMsb (β wMsb) (ket β₁) := by
            simpa only [β₁, Function.update_of_ne hMsbAnc] using HasWireBit.ket wMsb β₁
          have h1_a : HasWireBit wAnc (β wMsb + 1) (ket β₁) := by
            simpa only [β₁, Function.update_self] using HasWireBit.ket wAnc β₁
          have h5_a := HasWireBit.cnot_target hMsbAnc
            (((h1_m.readOnly hLm).readOnly (ReadOnlyWire.x hMsbAnc)).readOnly hRm)
            (((h1_a.readOnly hLa).x_self).readOnly hRa)
          rw [zmod2_add_one_add_one, CharTwo.add_self_eq_zero] at h5_a
          dsimp only [HasWireBit, wireBitFin_zero] at h5_a
          exact h5_a
        · simp only [hβa, ↓reduceIte, Matrix.mulVec_zero]
      · rw [restrictAssertionToZeroAncilla_regSucc, hNoneSub.2.2 Ψ hΨ,
          ← restrictAssertionToZeroAncilla_regSucc]
  | some wCtrl =>
      dsimp only [branchMsbCircuit, branchMsbDyn]
      let hCtrlMsb := hcX (Fin.last m) wCtrl rfl
      let hCtrlAnc := hcW (Fin.last m) wCtrl rfl
      have hSubCtrl : ∀ i, rSub i ≠ wCtrl := fun i ↦ (hcW i.castSucc wCtrl rfl).symm
      have hLc := hL.readOnly_of_ne wCtrl (fun i ↦ hcW i.castSucc wCtrl rfl)
        (fun i ↦ hcY i wCtrl rfl)
      have hRc := hR.readOnly_of_ne wCtrl (fun i ↦ hcW i.castSucc wCtrl rfl)
        (fun i ↦ hcY i wCtrl rfl)
      have hToffSub : PreservesZeroAncilla rSub
          (Circuit.TOFF wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc) :=
        PreservesZeroAncilla.of_not_mem_support
          (fun i ↦ by simp [Circuit.TOFF, hSubCtrl i, hSubMsb i, hSubAnc i])
      have hCnotSub : PreservesZeroAncilla rSub (Circuit.CNOT wCtrl wAnc hCtrlAnc) :=
        PreservesZeroAncilla.of_not_mem_support
          (fun i ↦ by simp [Circuit.CNOT, hSubCtrl i, hSubAnc i])
      let cMid := (Circuit.X wMsb).seq (leftCircuit.seq
        ((Circuit.CNOT wCtrl wAnc hCtrlAnc).seq rightCircuit))
      have hMid : SubDynClean v rSub cMid
          (.seq (.circuit (Circuit.X wMsb)) (.seq leftDyn
            (.seq (.circuit (Circuit.CNOT wCtrl wAnc hCtrlAnc)) rightDyn))) :=
        (SubDynClean.of_circuit v hXMsbSub).seq ((SubDynClean.of_valid hL).seq
          ((SubDynClean.of_circuit v hCnotSub).seq (SubDynClean.of_valid hR)))
      let P₀ := (QRegister.singleton wAnc).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc).eval.1
      have hAncP0 : P₀ * (T_anc * cMid.eval.1 * T_anc * P₀) = T_anc * cMid.eval.1 * T_anc * P₀ :=
        matrix_ext_ket fun β ↦ by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projector_zero]
          by_cases hβa : β wAnc = 0
          · simp only [hβa, ↓reduceIte]
            have h0_a : HasWireBit wAnc 0 (ket β) := by simpa only [hβa] using HasWireBit.ket wAnc β
            have h3_c := (((HasWireBit.ket wCtrl β).readOnly
              (ReadOnlyWire.toffoli hCtrlMsb hCtrlAnc hMsbAnc hCtrlAnc)).readOnly
                (ReadOnlyWire.x hCtrlMsb)).readOnly hLc
            have h3_m := (((HasWireBit.ket wMsb β).readOnly
              (ReadOnlyWire.toffoli hCtrlMsb hCtrlAnc hMsbAnc hMsbAnc)).x_self).readOnly hLm
            have h3_a := ((HasWireBit.toffoli_target hCtrlMsb hCtrlAnc hMsbAnc
              (HasWireBit.ket wCtrl β) (HasWireBit.ket wMsb β) h0_a).readOnly
                (ReadOnlyWire.x hMsbAnc.symm)).readOnly hLa
            have h6_a := HasWireBit.toffoli_target hCtrlMsb hCtrlAnc hMsbAnc
              ((h3_c.readOnly (ReadOnlyWire.cnot hCtrlAnc hCtrlAnc)).readOnly hRc)
              ((h3_m.readOnly (ReadOnlyWire.cnot hCtrlAnc hMsbAnc)).readOnly hRm)
              ((HasWireBit.cnot_target hCtrlAnc h3_c h3_a).readOnly hRa)
            rw [show (0 + β wCtrl * β wMsb + β wCtrl + β wCtrl * (β wMsb + 1) : ZMod 2) = 0 by
              rw [zero_add, mul_add, mul_one, ← add_assoc,
                add_right_comm (β wCtrl * β wMsb) (β wCtrl) (β wCtrl * β wMsb),
                CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]] at h6_a
            dsimp only [HasWireBit, wireBitFin_zero] at h6_a
            simpa only [cMid, T_anc, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
              using h6_a
          · simp only [hβa, ↓reduceIte, Matrix.mulVec_zero]
      refine ⟨fun q hqW hqY ↦ ?_, PreservesZeroAncilla.regSucc
        (hXMsbSub.seq (hToffSub.seq (hMid.1.seq hToffSub))) ?_, fun Ψ hΨ σ val ↦ ?_, fun Ψ hΨ ↦ ?_⟩
      · refine ReadOnlyWire.of_eval_eq (c₂ := ((Circuit.X wMsb).seq
          ((Circuit.TOFF wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc).seq (Circuit.X wMsb))).seq
          (leftCircuit.seq ((Circuit.CNOT wCtrl wAnc hCtrlAnc).seq (rightCircuit.seq
            (Circuit.TOFF wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc)))))
          (by simp only [wMsb, wAnc, Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]) ?_
        exact (ReadOnlyWire.of_eval_mulVec_ket_update _ (hqW (Fin.last m))
          (andNotSome_eval_mulVec_ket wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc)).seq
          ((hL.readOnly_of_ne q (fun i ↦ hqW i.castSucc) hqY).seq
            ((ReadOnlyWire.cnot hCtrlAnc (hqW (Fin.last m))).seq
              ((hR.readOnly_of_ne q (fun i ↦ hqW i.castSucc) hqY).seq
                (ReadOnlyWire.toffoli hCtrlMsb hCtrlAnc hMsbAnc (hqW (Fin.last m))))))
      · change PreservesZeroAncilla (QRegister.singleton wAnc) _
        refine (PreservesZeroAncilla.of_not_mem_support (c := Circuit.X wMsb) fun i ↦ by
            rw [Subsingleton.elim i 0]
            simp [hMsbAnc.symm]).seq ?_
        dsimp only [PreservesZeroAncilla]
        simpa only [cMid, T_anc, P₀, Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
          using hAncP0
      · dsimp only [DynamicCircuit.andCompute]
        rw [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
          DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
          DynamicCircuit.compile_seq, wp_qSeq]
        exact lemHex142 v (Circuit.X wMsb) _
          (lemHex142 v (Circuit.andCompute wCtrl wMsb wAnc hCtrlAnc
          hMsbAnc) _ (hMid.2.1 _ (fun σ' val' ↦ DynamicCircuit.wp_andUncompute_update_self v wCtrl
          wMsb wAnc hCtrlMsb Ψ σ' val'))) σ val
      · have hPeel := restrictAssertionToZeroAncilla_wp_andCompute_dyn_andUncompute_of_update_eq
          v wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc rSub hSubCtrl hSubMsb hSubAnc
          _ cMid hMid.2.2 hMid.1 hAncP0 Ψ hΨ
        rw [← restrictAssertionToZeroAncilla_regSucc,
          ← restrictAssertionToZeroAncilla_regSucc] at hPeel
        have hXMsb_comm := DynCircuitExt.circuit_eval_comm_basisOutcomeProjector_of_not_mem_support
          (Circuit.X wMsb) rW 0 (fun i ↦ by simp [wMsb, (hXW.ne (Fin.last m) i).symm])
        dsimp only [wMsb, wAnc, cMid] at *
        rw [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp,
          DynCircuitExt.wp_circuit_compile_compat,
          ← DynCircuitExt.wp_qAssign_restrictAssertionToZeroAncilla_comm _ rW hXMsb_comm,
          hPeel, DynCircuitExt.wp_qAssign_restrictAssertionToZeroAncilla_comm _ rW hXMsb_comm,
          wpQAssignCompat_comp, ← Circuit.eval_seq]
theorem disjoint_regInit_both {k₁ k₂ : ℕ} {r₁ : QRegister (k₁ + 1) n}
    {r₂ : QRegister (k₂ + 1) n} (h : r₁.DisjointWires r₂) : (regInit r₁).DisjointWires
    (regInit r₂) := (h.compose_left _).compose_right _
theorem disjoint_regInit_left {k₁ k₂ : ℕ} {r₁ : QRegister (k₁ + 1) n} {r₂ : QRegister k₂ n}
    (h : r₁.DisjointWires r₂) : (regInit r₁).DisjointWires r₂ := h.compose_left _
theorem ValidQromTree.seq [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    {k w : ℕ} (v : Var) (rW : QRegister k n) (rY : QRegister w n)
    (c₁ c₂ : Circuit n) (d₁ d₂ : DynamicCircuit Var n)
    (h₁ : ValidQromTree v rW rY c₁ d₁) (h₂ : ValidQromTree v rW rY c₂ d₂) :
    ValidQromTree v rW rY (c₁ ;;ᶜ c₂) (.seq d₁ d₂) :=
  let hs := (SubDynClean.of_valid h₁).seq (SubDynClean.of_valid h₂)
  ⟨fun q hqW hqY ↦ (h₁.readOnly_of_ne q hqW hqY).seq (h₂.readOnly_of_ne q hqW hqY),
    hs.1, hs.2.1, hs.2.2⟩
theorem localIdx_eq_of_apply_eq_loc {m : ℕ} (r : QRegister m n) (β₁ β₂ : BitAssignment n)
    (h : ∀ i, β₁ (r i) = β₂ (r i)) : localIdx r β₁ = localIdx r β₂ := by
  simp only [localIdx]
  exact congrArg _ (funext h)
theorem localIdx_slice_low_add_high {l h : ℕ} (r : QRegister (l + h) n) (hl : 0 + l ≤ l + h)
    (hh : l + h ≤ l + h) (β : BitAssignment n) : (localIdx r β : ℕ) =
    (localIdx (r.slice 0 l hl) β : ℕ) + 2 ^ l * (localIdx (r.slice l h hh) β : ℕ) := by
  rw [localIdx_val, localIdx_val, localIdx_val, Fin.sum_univ_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) (Finset.sum_congr rfl fun j _ ↦ ?_)
  · rw [show r.slice 0 l hl i = r (Fin.castAdd h i) by
      rw [QRegister.slice_apply]
      exact congrArg r (Fin.ext (by simp))]
    rfl
  · rw [show r.slice l h hh j = r (Fin.natAdd l j) by
      rw [QRegister.slice_apply]
      rfl]
    change (β (r (Fin.natAdd l j))).val * 2 ^ (l + j.val) = _
    rw [pow_add]
    ring
noncomputable def condSwapRegs {w : ℕ} (b : ZMod 2) (rA rB : QRegister w n)
    (β : BitAssignment n) : BitAssignment n := if b = 1 then writeReg
    (writeReg β rA (fun i ↦ β (rB i))) rB (fun i ↦ β (rA i)) else β
theorem condSwapRegs_apply_left {w : ℕ} (b : ZMod 2) (rA rB : QRegister w n)
    (hAB : rA.DisjointWires rB) (β : BitAssignment n) (i : Fin w) :
    condSwapRegs b rA rB β (rA i) = if b = 1 then β (rB i) else β (rA i) := by
  dsimp only [condSwapRegs]
  split_ifs
  · rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hAB i), writeReg_apply_reg]
  · rfl
theorem condSwapRegs_apply_other {w : ℕ} (b : ZMod 2) (rA rB : QRegister w n)
    (β : BitAssignment n) {q : Wire n} (hqA : q ∉ Set.range rA.wires)
    (hqB : q ∉ Set.range rB.wires) : condSwapRegs b rA rB β q = β q := by
  dsimp only [condSwapRegs]
  split_ifs
  · rw [writeReg_apply_of_not_mem _ _ _ _ hqB, writeReg_apply_of_not_mem _ _ _ _ hqA]
  · rfl
end OctahedralOrbit
end
end ModOctahedralSelectSwapQrom

section ModOctahedralMeasUncomputeBase
@[expose] public section
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace OctahedralOrbit
variable {Var : Type} {n : ℕ}
def hadamardReg : {b : ℕ} → QRegister b n → Circuit n
  | 0, _ => .identity
  | b + 1, r =>
      Circuit.H (r 0) ;;ᶜ hadamardReg (r.slice 1 b (by omega))
@[simp] theorem count_hadamardReg_toff {b : ℕ} (r : QRegister b n) :
    (hadamardReg r).count PrimitiveGate.TOFF = 0 := by
  induction b with
  | zero => rfl
  | succ b ih => simp [hadamardReg, ih (r.slice 1 b (by omega))]
@[simp] theorem count_hadamardReg_t {b : ℕ} (r : QRegister b n) :
    (hadamardReg r).count PrimitiveGate.T = 0 := by
  induction b with
  | zero => rfl
  | succ b ih => simp [hadamardReg, ih (r.slice 1 b (by omega))]
noncomputable def sqrtHalfC : ℂ := (Real.sqrt (1 / 2) : ℝ)
theorem sqrtHalfC_mul_sqrtHalfC : sqrtHalfC * sqrtHalfC = 1 / 2 := by
  dsimp [sqrtHalfC]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring
abbrev bitSignC (b : ZMod 2) : ℂ := if b = 0 then 1 else -1
theorem bitSignC_eq_neg_one_pow (b : ZMod 2) : bitSignC b = (-1 : ℂ) ^ b.val := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    simp [bitSignC, ZMod.val_zero]
theorem ket_Z (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (β q).val) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1,0; 0,-1]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e, ZMod.val_zero]
theorem ket_H (q : Wire n) (β : BitAssignment n) : (Circuit.H q).eval.1.mulVec (ket β) =
    sqrtHalfC • (ket (Function.update β q 0) + bitSignC (β q) • ket (Function.update β q 1))
    := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((Real.sqrt (1 / 2) : ℝ) • !![(1 : ℂ), 1; 1,-1])).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;>
    simp [hb, sqrtHalfC, bitSignC, smul_add, Complex.real_smul]
theorem ket_CZ (c t : Wire n) (hct : c ≠ t) (β : BitAssignment n) :
    (Circuit.H t ;;ᶜ Circuit.CNOT c t hct ;;ᶜ Circuit.H t).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (β c * β t).val) • ket β := by
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_H]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT, Function.update_self,
    Function.update_idem, Function.update_of_ne hct, ket_H, smul_add, smul_smul]
  have hsq : sqrtHalfC ^ 2 = 1 / 2 := by rw [sq, sqrtHalfC_mul_sqrtHalfC]
  have h11 : (1 + 1 : ZMod 2) = 0 := rfl
  have hu := Function.update_eq_self t β
  ext idx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases zmod2_eq_zero_or_one (β c) with hc | hc <;>
    rcases zmod2_eq_zero_or_one (β t) with ht | ht <;>
    rw [ht] at hu <;>
    simp [hc, ht, h11, bitSignC, hu] <;>
    ring_nf <;>
    rw [hsq] <;>
    ring
theorem ReadOnlyWire.of_ket_smul (q : Wire n) (c : Circuit n) (φ : BitAssignment n → ℂ)
    (hc : ∀ β : BitAssignment n, c.eval.1.mulVec (ket β) = φ β • ket β) :
    ReadOnlyWire q c := fun o ↦ matrix_ext_ket fun β ↦ by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, ket_projector]
  split_ifs
  · rw [hc]
  · simp
def czBitCircuit (c : Option (Wire n)) (t : Wire n) (hct : CtrlNe c t) : Circuit n :=
  match c with
  | none => Circuit.Z t
  | some wCtrl => Circuit.H t ;;ᶜ Circuit.CNOT wCtrl t (hct wCtrl rfl) ;;ᶜ Circuit.H t
@[simp]
theorem count_czBitCircuit_toff (c : Option (Wire n)) (t : Wire n) (hct : CtrlNe c t) :
    (czBitCircuit c t hct).count PrimitiveGate.TOFF = 0 := by
  cases c <;> simp [czBitCircuit, Circuit.CNOT]
@[simp] theorem count_czBitCircuit_t (c : Option (Wire n)) (t : Wire n) (hct : CtrlNe c t) :
    (czBitCircuit c t hct).count PrimitiveGate.T = 0 := by
  cases c <;> simp [czBitCircuit, Circuit.CNOT]
theorem czBitCircuit_eval_mulVec_ket (c : Option (Wire n)) (t : Wire n) (hct : CtrlNe c t)
    (β : BitAssignment n) : (czBitCircuit c t hct).eval.1.mulVec (ket β) =
    ((-1 : ℂ) ^ (ctrlVal c β * β t).val) • ket β := by
  cases c with
  | none => simpa [czBitCircuit, ctrlVal] using ket_Z t β
  | some wCtrl => exact ket_CZ wCtrl t (hct wCtrl rfl) β
theorem neg_one_pow_zmod2_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
  have h11 : (1 + 1 : ZMod 2) = 0 := rfl
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    simp [h11]
def czFanoutCircuit : {w : ℕ} → (c : Option (Wire n)) → (rY : QRegister w n) →
    (∀ i, CtrlNe c (rY i)) → BitAssignment w → Circuit n
  | 0, _, _, _, _ => .identity
  | m + 1, c, rY, hcY, d =>
      czFanoutCircuit c (regInit rY) (fun i ↦ hcY i.castSucc) (fun i ↦ d i.castSucc) ;;ᶜ
        if d (Fin.last m) = 1 then
          czBitCircuit c (rY (Fin.last m)) (hcY (Fin.last m))
        else
          .identity
@[simp] theorem count_czFanoutCircuit_toff {w : ℕ} (c : Option (Wire n)) (rY : QRegister w n)
    (hcY : ∀ i, CtrlNe c (rY i)) (d : BitAssignment w) :
    (czFanoutCircuit c rY hcY d).count PrimitiveGate.TOFF = 0 := by
  induction w with
  | zero => rfl
  | succ m ih =>
      simp only [czFanoutCircuit, Circuit.count_seq,
        ih (regInit rY) (fun i ↦ hcY i.castSucc) (fun i ↦ d i.castSucc)]
      split_ifs <;> simp
@[simp] theorem count_czFanoutCircuit_t {w : ℕ} (c : Option (Wire n)) (rY : QRegister w n)
    (hcY : ∀ i, CtrlNe c (rY i)) (d : BitAssignment w) :
    (czFanoutCircuit c rY hcY d).count PrimitiveGate.T = 0 := by
  induction w with
  | zero => rfl
  | succ m ih =>
      simp only [czFanoutCircuit, Circuit.count_seq,
        ih (regInit rY) (fun i ↦ hcY i.castSucc) (fun i ↦ d i.castSucc)]
      split_ifs <;> simp
theorem czFanoutCircuit_eval_mulVec_ket {w : ℕ} (c : Option (Wire n)) (rY : QRegister w n)
    (hcY : ∀ i, CtrlNe c (rY i)) (d : BitAssignment w) (β : BitAssignment n) :
    (czFanoutCircuit c rY hcY d).eval.1.mulVec (ket β) =
    ((-1 : ℂ) ^ (∑ i : Fin w, ctrlVal c β * β (rY i) * d i).val) • ket β := by
  induction w with
  | zero =>
      simp only [czFanoutCircuit, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
        Finset.univ_eq_empty, Finset.sum_empty, ZMod.val_zero, _root_.pow_zero, one_smul]
  | succ m ih =>
      dsimp only [czFanoutCircuit]
      rw [eval_seq_mulVec, ih (regInit rY) (fun i ↦ hcY i.castSucc) (fun i ↦ d i.castSucc),
        Matrix.mulVec_smul, Fin.sum_univ_castSucc]
      dsimp only [regInit_apply]
      split_ifs with hd
      · rw [czBitCircuit_eval_mulVec_ket, smul_smul, hd, mul_one,
          neg_one_pow_zmod2_add, mul_comm ((-1 : ℂ) ^ _)]
      · have hd0 : d (Fin.last m) = 0 :=
          (zmod2_eq_zero_or_one (d (Fin.last m))).resolve_right hd
        simp only [hd0, mul_zero, add_zero, Circuit.eval_identity, Submonoid.coe_one,
          Matrix.one_mulVec]
theorem ReadOnlyWire.czFanout {w : ℕ} (q : Wire n) (c : Option (Wire n))
    (rY : QRegister w n) (hcY : ∀ i, CtrlNe c (rY i)) (d : BitAssignment w) :
    ReadOnlyWire q (czFanoutCircuit c rY hcY d) :=
  ReadOnlyWire.of_ket_smul q _ _ (czFanoutCircuit_eval_mulVec_ket c rY hcY d)
def rEmpty0 (n : ℕ) : QRegister 0 n := QRegister.block 0 0 (Nat.zero_le n)
theorem disjoint_rEmpty0 {k : ℕ} (r : QRegister k n) : r.DisjointWires (rEmpty0 n) :=
  QRegister.disjoint_iff.mpr fun _ j ↦ j.elim0
theorem ctrlNe_rEmpty0 (c : Option (Wire n)) : ∀ i : Fin 0, CtrlNe c ((rEmpty0 n) i) :=
  fun i ↦ i.elim0
theorem ValidQromTree.czFanout [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) {w : ℕ} (c : Option (Wire n)) (rW : QRegister 0 n) (rP : QRegister w n)
    (hcP : ∀ i, CtrlNe c (rP i)) (d : BitAssignment w) :
    ValidQromTree v rW (rEmpty0 n) (czFanoutCircuit c rP hcP d)
      (.circuit (czFanoutCircuit c rP hcP d)) where
  readOnly_of_ne q _ _ := ReadOnlyWire.czFanout q c rP hcP d
  preserves_rW := PreservesZeroAncilla.regZero rW
  wp_update_eq Ψ hΨ σ val := by
    simp only [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
    exact Subtype.ext (by simp [wpQAssignCompat, qAssignObsMap, hΨ σ val])
  wp_clean _ _ := by
    simp only [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
theorem branchMsbCircuit_eval_mulVec_ket_diag {m : ℕ} (c : Option (Wire n))
    (rX rW : QRegister (m + 1) n) (hXW : rX.DisjointWires rW) (hcX : ∀ i, CtrlNe c (rX i))
    (hcW : ∀ i, CtrlNe c (rW i)) (leftCircuit rightCircuit : Circuit n) (valL valR : ZMod 2)
    (β : BitAssignment n) (hcleanAnc : β (rW (Fin.last m)) = 0) (hLeftKet : ∀ a : ZMod 2,
    leftCircuit.eval.1.mulVec (ket (Function.update β (rW (Fin.last m)) a)) = ((-1 : ℂ) ^ (a *
    valL).val) • ket (Function.update β (rW (Fin.last m)) a)) (hRightKet : ∀ a : ZMod 2,
    rightCircuit.eval.1.mulVec (ket (Function.update β (rW (Fin.last m)) a)) = ((-1 : ℂ) ^ (a
    * valR).val) • ket (Function.update β (rW (Fin.last m)) a)) : (branchMsbCircuit c (rX
    (Fin.last m)) (rW (Fin.last m)) (hcX (Fin.last m)) (hcW (Fin.last m)) (hXW.ne (Fin.last m)
    (Fin.last m)) leftCircuit rightCircuit).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (ctrlVal c β *
    (if β (rX (Fin.last m)) = 0 then valL else valR)).val) • ket β := by
  let wMsb := rX (Fin.last m)
  let wAnc := rW (Fin.last m)
  have hMsbAnc : wMsb ≠ wAnc := hXW.ne (Fin.last m) (Fin.last m)
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  cases c with
  | none =>
      dsimp only [branchMsbCircuit, ctrlVal]
      rw [eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec,
        andNotNone_eval_mulVec_ket, hcleanAnc, zero_add, hLeftKet, Matrix.mulVec_smul, ket_X,
        Function.update_self, Function.update_idem, Matrix.mulVec_smul, hRightKet, smul_smul,
        Matrix.mulVec_smul, ket_CNOT, Function.update_self, Function.update_of_ne hMsbAnc,
        Function.update_idem]
      have hzero : β wMsb + 1 + 1 + β wMsb = 0 := by
        rcases zmod2_eq_zero_or_one (β wMsb) with h | h <;> rw [h] <;> decide
      rw [hzero, Function.update_eq_self_iff.mpr hcleanAnc.symm, ← neg_one_pow_zmod2_add]
      have hval : (β wMsb + 1) * valL + (β wMsb + 1 + 1) * valR =
          1 * (if β wMsb = 0 then valL else valR) := by
        rcases zmod2_eq_zero_or_one (β wMsb) with hm | hm <;> rw [hm] <;> simp [h10, h11]
      rw [hval]
  | some wCtrl =>
      dsimp only [branchMsbCircuit, ctrlVal]
      let hCtrlMsb := hcX (Fin.last m) wCtrl rfl
      let hCtrlAnc := hcW (Fin.last m) wCtrl rfl
      have heval_assoc :
          (Circuit.X wMsb ;;ᶜ
            (Circuit.TOFF wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc ;;ᶜ
              (Circuit.X wMsb ;;ᶜ leftCircuit ;;ᶜ
                Circuit.CNOT wCtrl wAnc hCtrlAnc ;;ᶜ rightCircuit) ;;ᶜ
              Circuit.TOFF wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc)).eval.1 =
          ((Circuit.X wMsb ;;ᶜ
            Circuit.TOFF wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc ;;ᶜ
            Circuit.X wMsb) ;;ᶜ
            leftCircuit ;;ᶜ
            Circuit.CNOT wCtrl wAnc hCtrlAnc ;;ᶜ
            rightCircuit ;;ᶜ
            Circuit.TOFF wCtrl wMsb wAnc hCtrlMsb hCtrlAnc hMsbAnc).eval.1 := by
        simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
      rw [heval_assoc, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec,
        andNotSome_eval_mulVec_ket, hcleanAnc, zero_add, hLeftKet, Matrix.mulVec_smul,
        ket_CNOT, Function.update_self, Function.update_of_ne hCtrlAnc, Function.update_idem,
        Matrix.mulVec_smul, hRightKet, smul_smul, Matrix.mulVec_smul, ket_TOFF,
        Function.update_self, Function.update_of_ne hCtrlAnc, Function.update_of_ne hMsbAnc,
        Function.update_idem]
      have hzero : β wCtrl * (β wMsb + 1) + β wCtrl + β wCtrl * β wMsb = 0 := by
        rcases zmod2_eq_zero_or_one (β wCtrl) with hc | hc <;>
          rcases zmod2_eq_zero_or_one (β wMsb) with hm | hm <;>
          rw [hc, hm] <;> decide
      rw [hzero, Function.update_eq_self_iff.mpr hcleanAnc.symm, ← neg_one_pow_zmod2_add]
      have hval : (β wCtrl * (β wMsb + 1)) * valL + (β wCtrl * (β wMsb + 1) + β wCtrl) * valR
          = β wCtrl * (if β wMsb = 0 then valL else valR) := by
        rcases zmod2_eq_zero_or_one (β wMsb) with hm | hm <;>
          rw [hm] <;> simp [CharTwo.add_self_eq_zero, h10]
      rw [hval]
def phaseLookupCircuit {w : ℕ} (rP : QRegister w n) :
    {k : ℕ} → (c : Option (Wire n)) → (rX rW : QRegister k n) →
    rX.DisjointWires rW → rW.DisjointWires rP →
    (∀ i, CtrlNe c (rX i)) → (∀ i, CtrlNe c (rW i)) → (∀ i, CtrlNe c (rP i)) →
    (ℕ → BitAssignment w) → Circuit n
  | 0, c, _, _, _, _, _, _, hcP, T => czFanoutCircuit c rP hcP (T 0)
  | m + 1, c, rX, rW, hXW, hWP, hcX, hcW, _hcP, T =>
      let hXW' : (regInit rX).DisjointWires (regInit rW) := disjoint_regInit_both hXW
      let hWP' : (regInit rW).DisjointWires rP := disjoint_regInit_left hWP
      let hcX' : ∀ i, CtrlNe (some (rW (Fin.last m))) ((regInit rX) i) :=
        fun i ↦ CtrlNe.some (hXW.ne i.castSucc (Fin.last m)).symm
      let hcW' : ∀ i, CtrlNe (some (rW (Fin.last m))) ((regInit rW) i) :=
        fun i ↦ CtrlNe.some (regInit_ne_last rW i).symm
      let hcP' : ∀ i, CtrlNe (some (rW (Fin.last m))) (rP i) :=
        fun i ↦ CtrlNe.some (hWP.ne (Fin.last m) i)
      branchMsbCircuit c (rX (Fin.last m)) (rW (Fin.last m))
        (hcX (Fin.last m)) (hcW (Fin.last m)) (hXW.ne (Fin.last m) (Fin.last m))
        (phaseLookupCircuit rP (some (rW (Fin.last m))) (regInit rX) (regInit rW)
          hXW' hWP' hcX' hcW' hcP' (fun j ↦ T j))
        (phaseLookupCircuit rP (some (rW (Fin.last m))) (regInit rX) (regInit rW)
          hXW' hWP' hcX' hcW' hcP' (fun j ↦ T (2 ^ m + j)))
theorem phaseLookupCircuit_eval_mulVec_ket {k w : ℕ} (rP : QRegister w n)
    (c : Option (Wire n)) (rX rW : QRegister k n) (hXW : rX.DisjointWires rW)
    (hWP : rW.DisjointWires rP) (hcX : ∀ i, CtrlNe c (rX i)) (hcW : ∀ i, CtrlNe c (rW i))
    (hcP : ∀ i, CtrlNe c (rP i)) (T : ℕ → BitAssignment w) (β : BitAssignment n)
    (hclean : ∀ i, β (rW i) = 0) :
    (phaseLookupCircuit rP c rX rW hXW hWP hcX hcW hcP T).eval.1.mulVec (ket β) = ((-1 : ℂ) ^
    (ctrlVal c β * ∑ i : Fin w, β (rP i) * T (localIdx rX β) i).val) • ket β := by
  induction k generalizing c T β with
  | zero =>
      dsimp only [phaseLookupCircuit]
      rw [czFanoutCircuit_eval_mulVec_ket, show (localIdx rX β : ℕ) = 0 by omega, Finset.mul_sum]
      exact congrArg (fun x : ZMod 2 ↦ ((-1 : ℂ) ^ x.val) • ket β)
        (Finset.sum_congr rfl fun _ _ ↦ by ring)
  | succ m ih =>
      dsimp only [phaseLookupCircuit]
      let wAnc := rW (Fin.last m)
      have hStep (T' : ℕ → BitAssignment w) (a : ZMod 2) : (phaseLookupCircuit rP (some wAnc)
          (regInit rX) (regInit rW) (disjoint_regInit_both hXW) (disjoint_regInit_left hWP)
          (fun i ↦ CtrlNe.some (hXW.ne i.castSucc (Fin.last m)).symm)
          (fun i ↦ CtrlNe.some (regInit_ne_last rW i).symm)
          (fun i ↦ CtrlNe.some (hWP.ne (Fin.last m) i)) T').eval.1.mulVec
          (ket (Function.update β wAnc a)) = ((-1 : ℂ) ^ (a * ∑ i : Fin w, β (rP i) *
          T' (localIdx (regInit rX) β) i).val) • ket (Function.update β wAnc a) := by
        rw [ih (some wAnc) (regInit rX) (regInit rW) _ _ _ _ _ T' (Function.update β wAnc a)
            (fun i ↦ by
              rw [Function.update_of_ne (regInit_ne_last rW i), regInit_apply, hclean i.castSucc]),
          localIdx_update_of_not_mem _ _ fun ⟨i, hi⟩ ↦ hXW.ne i.castSucc (Fin.last m) hi]
        simp only [ctrlVal, Function.update_self]
        refine congrArg (fun s : ZMod 2 ↦ ((-1 : ℂ) ^ (a * s).val) • _)
          (Finset.sum_congr rfl fun i _ ↦ ?_)
        rw [Function.update_of_ne (hWP.ne (Fin.last m) i).symm]
      rw [branchMsbCircuit_eval_mulVec_ket_diag c rX rW hXW hcX hcW _ _ _ _ β (hclean (Fin.last m))
        (hStep (fun j ↦ T j)) (hStep (fun j ↦ T (2 ^ m + j)))]
      congr 3
      have hidx := localIdx_val_castSucc rX β
      rcases zmod2_eq_zero_or_one (β (rX (Fin.last m))) with hm | hm
      · simp only [hm, ↓reduceIte, ZMod.val_zero, zero_mul, add_zero] at hidx ⊢
        rw [hidx]
      · simp only [hm, (by decide : (1 : ZMod 2) ≠ 0), ↓reduceIte, ZMod.val_one, one_mul] at hidx ⊢
        rw [hidx, add_comm]
theorem PreservesZeroAncilla.concat {m₁ m₂ : ℕ} {r₁ : QRegister m₁ n} {r₂ : QRegister m₂ n}
    (hdisj : r₁.DisjointWires r₂) {c : Circuit n} (h₁ : PreservesZeroAncilla r₁ c)
    (h₂ : PreservesZeroAncilla r₂ c) : PreservesZeroAncilla (r₁.concat r₂ hdisj) c := by
  dsimp only [PreservesZeroAncilla] at h₁ h₂ ⊢
  rw [QRegExt.basisOutcomeProjector_concat_zero]
  exact preserves_mul_comm (QRegExt.basisOutcomeProjector_comm _ 0 _ 0) h₁ h₂
end OctahedralOrbit
end
end ModOctahedralMeasUncomputeBase

section ModDualOneHotAndMeasUncompute128
@[expose] public section
open Operator QProg Matrix HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace OctahedralOrbit
variable {Var : Type} {n : ℕ}
def StoreConst [Fintype Var] (Θ : CQAssertionCompat Var (2 ^ n)) : Prop :=
  ∀ σ₁ σ₂ : Store Var, Θ σ₁ = Θ σ₂
theorem storeConst_wp_circuit [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (c : Circuit n) {Ψ : CQAssertionCompat Var (2 ^ n)} (hΨ : StoreConst Ψ) :
    StoreConst (wp (DynamicCircuit.circuit c : DynamicCircuit Var n).compile Ψ) := fun σ₁ σ₂ ↦ by
  simp only [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
  exact Subtype.ext (by simp [wpQAssignCompat, qAssignObsMap, hΨ σ₁ σ₂])
theorem storeConst_wp_seq [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    {d₁ d₂ : DynamicCircuit Var n} (hd₁ : ∀ {Φ}, StoreConst Φ → StoreConst (wp d₁.compile Φ))
    (hd₂ : ∀ {Ψ}, StoreConst Ψ → StoreConst (wp d₂.compile Ψ)) {Ψ : CQAssertionCompat Var (2 ^ n)}
    (hΨ : StoreConst Ψ) : StoreConst (wp (DynamicCircuit.seq d₁ d₂).compile Ψ) := by
  simp only [DynamicCircuit.compile_seq, wp_qSeq]
  exact hd₁ (hd₂ hΨ)
theorem storeConst_wp_andUncompute [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] (v : Var)
    (a b target : Wire n) (hab : a ≠ b) {Ψ : CQAssertionCompat Var (2 ^ n)} (hΨ : StoreConst Ψ) :
    StoreConst (wp (DynamicCircuit.andUncompute v a b target hab).compile Ψ) := by
  refine storeConst_wp_seq (storeConst_wp_circuit (Circuit.H target)) (fun {Φ} hΦ σ₁ σ₂ ↦ ?_) hΨ
  have hcPhi := storeConst_wp_circuit (Circuit.andUncomputeFixup a b target hab) hΦ
  simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_measure,
    DynamicCircuit.compile_qIf, DynamicCircuit.compile_identity, wp_qSeq, wp_qIf, wp_skip,
    QProg.measureRegister, wp_qMeasure_apply, CQAssertionCompat.subst_apply]
  congr 1
  funext o
  have hv (σ : Store Var) : (σ.subst v (Int.ofNat o.val)) v = Int.ofNat o.val := by
    simp [Store.subst]
  simp only [hv σ₁, hv σ₂]
  split_ifs
  · exact hcPhi _ _
  · exact hΦ _ _
theorem storeConst_wp_branchMsbDyn [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] (v : Var)
    (c : Option (Wire n)) (wMsb wAnc : Wire n) (hcMsb : CtrlNe c wMsb) (hcAnc : CtrlNe c wAnc)
    (hMsbAnc : wMsb ≠ wAnc) {dL dR : DynamicCircuit Var n}
    (hdL : ∀ {Φ}, StoreConst Φ → StoreConst (wp dL.compile Φ))
    (hdR : ∀ {Φ}, StoreConst Φ → StoreConst (wp dR.compile Φ)) {Ψ : CQAssertionCompat Var (2 ^ n)}
    (hΨ : StoreConst Ψ) : StoreConst (wp (branchMsbDyn v c wMsb wAnc hcMsb hcAnc hMsbAnc dL
    dR).compile Ψ) := by
  cases c with
  | none =>
      exact storeConst_wp_seq (storeConst_wp_circuit _) (storeConst_wp_seq hdL
        (storeConst_wp_seq (storeConst_wp_circuit _) (storeConst_wp_seq hdR
        (storeConst_wp_circuit _)))) hΨ
  | some wCtrl =>
      exact storeConst_wp_seq (storeConst_wp_circuit _) (storeConst_wp_seq
        (storeConst_wp_circuit _) (storeConst_wp_seq (storeConst_wp_seq
        (storeConst_wp_circuit _) (storeConst_wp_seq hdL (storeConst_wp_seq
        (storeConst_wp_circuit _) hdR))) (storeConst_wp_andUncompute v wCtrl wMsb wAnc _))) hΨ
end OctahedralOrbit
end
end ModDualOneHotAndMeasUncompute128

section ModOctahedralOrbitUnfold7AndQrom128
@[expose] public section
namespace OctahedralOrbitUnfold7AndQrom128Alt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n)
    (i : Fin width) : (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end OctahedralOrbitUnfold7AndQrom128Alt
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace OctahedralOrbit
variable {Var : Type} {n : ℕ}
theorem pow2_slot_idx_lt {s slot w : ℕ} (hslot : slot < 2 ^ s) (i : Fin w) :
    slot * w + i.val < 2 ^ s * w :=
  lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _)
    (Nat.add_one_mul slot w ▸ Nat.mul_le_mul_right w hslot)
def packTablePow2 (s : ℕ) {w : ℕ} (T : ℕ → BitAssignment w) (blk : ℕ) :
    BitAssignment (2 ^ s * w) :=
  fun j ↦
    have hw : 0 < w := Nat.pos_of_ne_zero fun hw0 ↦ by subst hw0; exact Nat.not_lt_zero _ j.isLt
    T (2 ^ s * blk + j.val / w) ⟨j.val % w, Nat.mod_lt _ hw⟩
theorem packTablePow2_apply_mul_add (s : ℕ) {w : ℕ} (T : ℕ → BitAssignment w) (blk slot : ℕ)
    (hslot : slot < 2 ^ s) (i : Fin w) : packTablePow2 s T blk
    ⟨slot * w + i.val, pow2_slot_idx_lt hslot i⟩ = T (2 ^ s * blk + slot) i := by
  dsimp only [packTablePow2]
  have hw : 0 < w := Nat.zero_lt_of_lt i.isLt
  have hdiv : (slot * w + i.val) / w = slot := by
    rw [mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt i.isLt, add_zero]
  have hmod : (slot * w + i.val) % w = i.val := by
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]
  have h1 : 2 ^ s * blk + (slot * w + i.val) / w = 2 ^ s * blk + slot := by rw [hdiv]
  have h2 : (⟨(slot * w + i.val) % w, Nat.mod_lt _ hw⟩ : Fin w) = i := Fin.ext hmod
  rw [h1, h2]
theorem pow2_half_add_half (s w : ℕ) : 2 ^ s * w + 2 ^ s * w = 2 ^ (s + 1) * w := by ring
abbrev bufLeftHalf (s w : ℕ) (rBuf : QRegister (2 ^ (s + 1) * w) n) : QRegister (2 ^ s * w) n :=
  rBuf.slice 0 (2 ^ s * w) (by
    have := pow2_half_add_half s w
    omega)
abbrev bufRightHalf (s w : ℕ) (rBuf : QRegister (2 ^ (s + 1) * w) n) : QRegister (2 ^ s * w) n :=
  rBuf.slice (2 ^ s * w) (2 ^ s * w) (by
    have := pow2_half_add_half s w
    omega)
abbrev bufPow2Slot0 (s w : ℕ) (rBuf : QRegister (2 ^ s * w) n) : QRegister w n :=
  rBuf.slice 0 w (by
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_pow s 2 (by decide)
    calc 0 + w = 1 * w := by omega
      _ ≤ 2 ^ s * w := Nat.mul_le_mul_right w h1)
noncomputable def swapTreePow2Val : ∀ (s w : ℕ),
    QRegister s n → QRegister (2 ^ s * w) n → BitAssignment n → BitAssignment n
  | 0, _, _, _, β => β
  | s + 1, w, rOff, rBuf, β =>
      swapTreePow2Val s w (regInit rOff) (bufLeftHalf s w rBuf)
        (condSwapRegs (β (rOff (Fin.last s))) (bufLeftHalf s w rBuf) (bufRightHalf s w rBuf) β)
theorem swapTreePow2Val_apply_other : ∀ (s w : ℕ) (rOff : QRegister s n)
    (rBuf : QRegister (2 ^ s * w) n) (β : BitAssignment n) {q : Wire n},
    q ∉ Set.range rBuf.wires → swapTreePow2Val s w rOff rBuf β q = β q
  | 0, _, _, _, _, _, _ => rfl
  | s + 1, w, rOff, rBuf, β, q, hq => by
      have hqL : q ∉ Set.range (bufLeftHalf s w rBuf).wires := fun ⟨_, hj⟩ ↦ hq ⟨_, hj⟩
      have hqR : q ∉ Set.range (bufRightHalf s w rBuf).wires := fun ⟨_, hj⟩ ↦ hq ⟨_, hj⟩
      dsimp only [swapTreePow2Val]
      rw [swapTreePow2Val_apply_other s w (regInit rOff) (bufLeftHalf s w rBuf) _ hqL,
        condSwapRegs_apply_other _ _ _ _ hqL hqR]
theorem localIdx_regInit_add_last {s : ℕ} (rOff : QRegister (s + 1) n) (β : BitAssignment n) :
    (localIdx rOff β : ℕ) =
      (localIdx (regInit rOff) β : ℕ) + 2 ^ s * (β (rOff (Fin.last s))).val := by
  rw [localIdx_val, localIdx_val, Fin.sum_univ_castSucc]
  simp only [regInit_apply, Fin.val_last, Fin.val_castSucc]
  ring
theorem swapTreePow2Val_apply_slot0 (s w : ℕ) (rOff : QRegister s n)
    (rBuf : QRegister (2 ^ s * w) n) (hOffBuf : rOff.DisjointWires rBuf) (β : BitAssignment n)
    (i : Fin w) : swapTreePow2Val s w rOff rBuf β (bufPow2Slot0 s w rBuf i) = β (rBuf
    ⟨(localIdx rOff β : ℕ) * w + i.val, pow2_slot_idx_lt (localIdx rOff β).isLt i⟩) := by
  induction s generalizing β with
  | zero =>
      dsimp only [swapTreePow2Val, bufPow2Slot0]
      rw [QRegister.slice_apply]
      exact congrArg (fun j ↦ β (rBuf j)) (Fin.ext (by simp))
  | succ s ih =>
      dsimp only [swapTreePow2Val]
      let β₁ := condSwapRegs (β (rOff (Fin.last s)))
        (bufLeftHalf s w rBuf) (bufRightHalf s w rBuf) β
      have hSlotEq : bufPow2Slot0 (s + 1) w rBuf i =
          bufPow2Slot0 s w (bufLeftHalf s w rBuf) i := by
        dsimp only [bufPow2Slot0, bufLeftHalf]
        rw [QRegister.slice_apply, QRegister.slice_apply, QRegister.slice_apply]
        exact congrArg rBuf (Fin.ext (by simp))
      have hOffEq : localIdx (regInit rOff) β₁ = localIdx (regInit rOff) β := by
        unfold localIdx
        exact congrArg _ (funext fun k ↦ condSwapRegs_apply_other _ _ _ _
          (fun ⟨j, hj⟩ ↦ (hOffBuf.compose_right _).ne k.castSucc j hj.symm)
          (fun ⟨j, hj⟩ ↦ (hOffBuf.compose_right _).ne k.castSucc j hj.symm))
      have hhw := pow2_half_add_half s w
      have hLR := rBuf.slice_disjoint_of_le 0 (2 ^ s * w) (2 ^ s * w) (2 ^ s * w)
        (by omega) (by omega) (by omega)
      rw [hSlotEq, ih (regInit rOff) (bufLeftHalf s w rBuf)
        ((hOffBuf.compose_left _).compose_right _) β₁, hOffEq]
      dsimp only [β₁]
      rw [condSwapRegs_apply_left _ _ _ hLR]
      have hDecomp := localIdx_regInit_add_last rOff β
      rcases zmod2_eq_zero_or_one (β (rOff (Fin.last s))) with hb | hb
      · simp only [hb, ZMod.val_zero, zero_ne_one, ↓reduceIte] at hDecomp ⊢
        dsimp only [bufLeftHalf, QRegister.slice_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.qreg_slice_wires,
          OctahedralOrbitUnfold7AndQrom128Alt.qreg_block_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.qreg_block_wires_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.qreg_whole_wires,
          OctahedralOrbitUnfold7AndQrom128Alt.emb_trans_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.emb_refl_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.emb_mk_apply]
        congr 2
        ext
        dsimp
        have h0 : (localIdx (regInit rOff) β : ℕ) = (localIdx rOff β : ℕ) := by omega
        rw [zero_add, h0]
      · simp only [hb, ZMod.val_one, ↓reduceIte] at hDecomp ⊢
        dsimp only [bufRightHalf, QRegister.slice_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.qreg_slice_wires,
          OctahedralOrbitUnfold7AndQrom128Alt.qreg_block_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.qreg_block_wires_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.qreg_whole_wires,
          OctahedralOrbitUnfold7AndQrom128Alt.emb_trans_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.emb_refl_apply,
          OctahedralOrbitUnfold7AndQrom128Alt.emb_mk_apply]
        congr 2
        ext
        dsimp
        calc 2 ^ s * w + ((localIdx (regInit rOff) β : ℕ) * w + i.val)
          _ = ((localIdx (regInit rOff) β : ℕ) + 2 ^ s * 1) * w + i.val := by ring
          _ = (localIdx rOff β : ℕ) * w + i.val := by rw [← hDecomp]
noncomputable def lookup3xPow2Val (m : ℕ) {w : ℕ} (T : ℕ → BitAssignment w)
    (rX : QRegister (m + 2) n) (β : BitAssignment n) : BitAssignment w :=
  if β (rX (Fin.last (m + 1))) = 1 then
    if β (rX ⟨m, by omega⟩) = 1 then fun _ ↦ 0
    else T (2 ^ (m + 1) + (localIdx (regInit (regInit rX)) β : ℕ))
  else
    T (localIdx (regInit rX) β : ℕ)
theorem lookup3xPow2Val_eq_of_lt (m : ℕ) {w : ℕ} (T : ℕ → BitAssignment w)
    (rX : QRegister (m + 2) n) (β : BitAssignment n) (hlt : (localIdx rX β : ℕ) < 3 * 2 ^ m) :
    lookup3xPow2Val m T rX β = T (localIdx rX β : ℕ) := by
  have hTop := localIdx_regInit_add_last rX β
  have hSub := localIdx_regInit_add_last (regInit rX) β
  rw [show regInit rX (Fin.last m) = rX ⟨m, by omega⟩ from rfl] at hSub
  have hpow1 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  dsimp only [lookup3xPow2Val]
  rcases zmod2_eq_zero_or_one (β (rX (Fin.last (m + 1)))) with hbTop | hbTop
  · simp only [hbTop, ZMod.val_zero, zero_ne_one, ↓reduceIte] at hTop ⊢
    exact congrArg T (by omega)
  · rcases zmod2_eq_zero_or_one (β (rX ⟨m, by omega⟩)) with hbSub | hbSub
    · simp only [hbTop, hbSub, ZMod.val_one, ZMod.val_zero, zero_ne_one, ↓reduceIte] at hTop hSub ⊢
      exact congrArg T (by omega)
    · simp only [hbTop, hbSub, ZMod.val_one] at hTop hSub
      omega
theorem ValidQromTree.identity [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) {k w : ℕ} (rW : QRegister k n) (rY : QRegister w n) :
    ValidQromTree v rW rY .identity (.circuit .identity) where
  readOnly_of_ne _ _ _ _ := by simp [Circuit.eval_identity]
  preserves_rW := by simp [PreservesZeroAncilla, Circuit.eval_identity]
  wp_update_eq Ψ hΨ σ val := by
    simp only [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
    exact Subtype.ext (by simp [wpQAssignCompat, qAssignObsMap, hΨ σ val])
  wp_clean _ _ := by
    simp only [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
private theorem lemHex149 {k : ℕ} (l h : ℕ) (r : QRegister k n) (hl : 0 + l ≤ k) (hh : l + h ≤ k)
    (hk : l + h = k) (β : BitAssignment n) : (localIdx r β : ℕ) =
    (localIdx (r.slice 0 l hl) β : ℕ) + 2 ^ l * (localIdx (r.slice l h hh) β : ℕ) := by
  subst hk
  exact localIdx_slice_low_add_high r hl hh β
theorem selectSwap3xPow2_slot0_eq (m s : ℕ) {w : ℕ} (rIdx : QRegister (m + 2 + s) n)
    (rBuf : QRegister (2 ^ s * w) n) (hIdxBuf : rIdx.DisjointWires rBuf)
    (T : ℕ → BitAssignment w) (β : BitAssignment n) (hcleanBuf : ∀ j, β (rBuf j) = 0)
    (hlt : (localIdx rIdx β : ℕ) < 3 * 2 ^ (m + s)) (i : Fin w) : swapTreePow2Val s w
    (rIdx.slice 0 s (by omega)) rBuf (writeReg β rBuf (fun j ↦ β (rBuf j) + lookup3xPow2Val m
    (packTablePow2 s T) (rIdx.slice s (m + 2) (by omega)) β j)) (bufPow2Slot0 s w rBuf i) = T
    (localIdx rIdx β) i := by
  let β_mid := writeReg β rBuf (fun j ↦
    β (rBuf j) + lookup3xPow2Val m (packTablePow2 s T) (rIdx.slice s (m + 2) (by omega)) β j)
  have hloc_low : localIdx (rIdx.slice 0 s (by omega)) β_mid =
      localIdx (rIdx.slice 0 s (by omega)) β :=
    localIdx_writeReg_of_disjoint β rBuf (rIdx.slice 0 s (by omega))
      (QRegister.disjoint_comm.mp (hIdxBuf.compose_left _)) _
  have hmid (k : Fin (2 ^ s * w)) : β_mid (rBuf k) =
      lookup3xPow2Val m (packTablePow2 s T) (rIdx.slice s (m + 2) (by omega)) β k := by
    dsimp only [β_mid]
    rw [writeReg_apply_reg, hcleanBuf, zero_add]
  rw [swapTreePow2Val_apply_slot0 s w (rIdx.slice 0 s (by omega)) rBuf
      (hIdxBuf.compose_left _) β_mid i,
    hmid,
    show (⟨(localIdx (rIdx.slice 0 s (by omega)) β_mid : ℕ) * w + i.val,
      pow2_slot_idx_lt (localIdx (rIdx.slice 0 s (by omega)) β_mid).isLt i⟩ : Fin (2 ^ s * w)) =
      ⟨(localIdx (rIdx.slice 0 s (by omega)) β : ℕ) * w + i.val,
        pow2_slot_idx_lt (localIdx (rIdx.slice 0 s (by omega)) β).isLt i⟩ from
      Fin.ext (by simp [hloc_low])]
  have hsplit := lemHex149 s (m + 2) rIdx (by omega) (by omega) (by omega) β
  have hpow_ms : 3 * 2 ^ (m + s) = 2 ^ s * (3 * 2 ^ m) := by ring
  have hhigh_lt : (localIdx (rIdx.slice s (m + 2) (by omega)) β : ℕ) < 3 * 2 ^ m := by
    by_contra hge
    have := Nat.mul_le_mul_left (2 ^ s)
      (show 3 * 2 ^ m ≤ (localIdx (rIdx.slice s (m + 2) (by omega)) β : ℕ) by omega)
    omega
  rw [lookup3xPow2Val_eq_of_lt m (packTablePow2 s T) _ β hhigh_lt,
    packTablePow2_apply_mul_add s T _ _ (localIdx (rIdx.slice 0 s (by omega)) β).isLt i]
  exact congrFun (congrArg T (by omega)) i

theorem storeConst_wp_andCompute [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (a b target : Wire n) (hat : a ≠ target) (hbt : b ≠ target) {Ψ : CQAssertionCompat Var (2 ^ n)}
    (hΨ : StoreConst Ψ) : StoreConst (wp (DynamicCircuit.andCompute a b target hat hbt :
    DynamicCircuit Var n).compile Ψ) := storeConst_wp_circuit _ hΨ

end OctahedralOrbit
end
end ModOctahedralOrbitUnfold7AndQrom128

section ModPosMomSelectSandwich
@[expose] public section
namespace PosMomSelectSandwich
open Operator Matrix
section PolymorphicAlgebra
variable {d : ℕ}
def momCleanOp (U_mom D_momGate : Operator d) : Operator d := U_momᴴ * D_momGate * U_mom
theorem conj_hermitian {V M : Operator d} (hM : Mᴴ = M) : (Vᴴ * M * V)ᴴ = Vᴴ * M * V := by
  rw [Matrix.mul_assoc Vᴴ M V, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, hM, Matrix.mul_assoc]
theorem momCleanOp_on_posSlot {U_mom D_momGate P₀ : Operator d} (hMom_rl : U_momᴴ * U_mom = 1)
    (hMom_P₀ : U_mom * P₀ = P₀ * U_mom) (hGate_P₀ : D_momGate * P₀ = P₀) : momCleanOp U_mom
    D_momGate * P₀ = P₀ := by
  calc U_momᴴ * D_momGate * U_mom * P₀
      = U_momᴴ * (D_momGate * P₀) * U_mom := by
          rw [Matrix.mul_assoc _ U_mom P₀, hMom_P₀]
          simp only [Matrix.mul_assoc]
    _ = (U_momᴴ * U_mom) * P₀ := by
          rw [hGate_P₀, Matrix.mul_assoc U_momᴴ P₀ U_mom, ← hMom_P₀, ← Matrix.mul_assoc]
    _ = P₀ := by rw [hMom_rl, one_mul]
end PolymorphicAlgebra
section CircuitInstantiation
variable {n : ℕ}
def slotBitProj (w : Wire n) (b : Fin 2) : Operator (2 ^ n) := Matrix.diagonal (fun x : Fin (2
    ^ n) ↦ if (basisBits n x w).val = b.val then (1 : ℂ) else 0)
theorem slotBitProj_zero_add_one (w : Wire n) : slotBitProj w 0 + slotBitProj w 1 = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp only [slotBitProj, Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      Fin.val_zero, Fin.val_one]
    have hlt : (basisBits n x w).val < 2 := (basisBits n x w).isLt
    by_cases h0 : (basisBits n x w).val = 0
    · rw [h0]
      norm_num
    · have h1 : (basisBits n x w).val = 1 := by omega
      rw [h1]
      norm_num
  · simp [slotBitProj, hxy]
@[simp] theorem count_toff_inverse (c : Circuit n) :
    c.inverse.count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF := by
  induction c with
  | identity => rfl
  | gate g r =>
      cases g <;> simp [Circuit.inverse, Circuit.inverseGate, Circuit.sequence,
        Circuit.count_seq, Circuit.count_gate, Circuit.count_identity]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.inverse_seq, Circuit.count_seq, ih₁, ih₂]
      omega
end CircuitInstantiation
end PosMomSelectSandwich
end
end ModPosMomSelectSandwich

section ModPosMomSelectDynamic
@[expose] public section
namespace PosMomSelectDynamic
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt
open PosMomSelectSandwich
section UnitarySandwichAlgebra
variable {d : ℕ}
def unitaryConj (U_outer U_inner : Unitary d) : Unitary d := U_outer⁻¹ * U_inner * U_outer
@[simp] theorem unitaryConj_val (U_outer U_inner : Unitary d) :
    (unitaryConj U_outer U_inner).1 = U_outer.1ᴴ * U_inner.1 * U_outer.1 := by
  simp only [unitaryConj, Submonoid.coe_mul, Matrix.mul_assoc]
  rfl
theorem unitaryConj_conjTranspose {U_outer U_inner : Unitary d}
    (hInner : U_inner.1ᴴ = U_inner.1) :
    (unitaryConj U_outer U_inner).1ᴴ = (unitaryConj U_outer U_inner).1 := by
  rw [unitaryConj_val]
  exact conj_hermitian hInner
theorem mul_conjTranspose_of_comm {U_posCore U_momCore : Unitary d}
    (hPos : U_posCore.1ᴴ = U_posCore.1) (hMom : U_momCore.1ᴴ = U_momCore.1)
    (hcomm : U_posCore.1 * U_momCore.1 = U_momCore.1 * U_posCore.1) :
    (U_posCore * U_momCore).1ᴴ = (U_posCore * U_momCore).1 := by
  simp only [Submonoid.coe_mul, conjTranspose_mul, hPos, hMom, ← hcomm]
end UnitarySandwichAlgebra
section PolymorphicGateIdentities
variable {k : ℕ}
theorem embedMatrix_diagonal {m : ℕ} (r : QRegister m k) (d : Fin (2 ^ m) → ℂ) :
    r.embedMatrix (Matrix.diagonal d) =
      Matrix.diagonal (fun x : Fin (2 ^ k) ↦ d (r.extractIndex x)) := by
  ext i j
  rw [QRegister.embedMatrix_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · by_cases hEnv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2
    · have hLoc : r.extractIndex i ≠ r.extractIndex j := fun hEq ↦
        hij (r.basisSplitEquiv.injective (Prod.ext hEq hEnv))
      simp [hij, hEnv, Matrix.diagonal_apply_ne _ hLoc]
    · simp [hij, hEnv]
theorem embedMatrix_comm_diagonal_of_outside {m : ℕ} (r : QRegister m k)
    (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (d : Fin (2 ^ k) → ℂ)
    (hd : ∀ i j : Fin (2 ^ k), r.AgreeOutside i j → d i = d j) :
    r.embedMatrix A * Matrix.diagonal d = Matrix.diagonal d * r.embedMatrix A := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hEnv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2
  · rw [hd i j ((r.basisSplit_environment_eq_iff i j).mp hEnv), mul_comm]
  · simp [QRegister.embedMatrix_apply, hEnv]
end PolymorphicGateIdentities
end PosMomSelectDynamic
end
end ModPosMomSelectDynamic

section ModSegmentedTimeEvolution
@[expose] public section
namespace SpecsAux
open Operator Matrix
open scoped Matrix Matrix.Norms.L2Operator
theorem l2_opNorm_unitary_le_one {d : ℕ} (U : Unitary d) : ‖U.1‖ ≤ 1 := by
  have h1 : ‖U.1‖ * ‖U.1‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self U.1,
      show U.1ᴴ * U.1 = 1 by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U,
      ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ ↦ by simp
  nlinarith [norm_nonneg U.1]
theorem exp_neg_I_smul_mem_unitary {d : ℕ} {H : Operator d} (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) ∈ unitary (Operator d) := by
  let A : Operator d := (-Complex.I * (t : ℂ)) • H
  have hA : Aᴴ = -A := by
    simp [A, conjTranspose_smul, hH.eq, Complex.conj_ofReal, neg_smul]
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hA,
    ← Matrix.exp_add_of_commute (-A) A (Commute.refl A).neg_left,
    ← Matrix.exp_add_of_commute A (-A) (Commute.refl A).neg_right,
    neg_add_cancel, add_neg_cancel, NormedSpace.exp_zero]
  exact ⟨rfl, rfl⟩
noncomputable def expTimeEvolutionUnitary {d : ℕ} (H : Operator d) (hH : H.IsHermitian)
    (t : ℝ) : Unitary d :=
  ⟨NormedSpace.exp ((-Complex.I * (t : ℂ)) • H), exp_neg_I_smul_mem_unitary hH t⟩
@[simp]
theorem expTimeEvolutionUnitary_coe {d : ℕ} (H : Operator d) (hH : H.IsHermitian) (t : ℝ) :
    (expTimeEvolutionUnitary H hH t).1 = NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) := rfl
theorem commute_exp_neg_I_smul {d : ℕ} {H P : Operator d} (hHP : Commute H P) (t : ℝ) :
    Commute (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)) P :=
  (hHP.smul_left (-Complex.I * (t : ℂ))).exp_left
theorem exp_neg_I_add_smul {d : ℕ} (H : Operator d) (t₁ t₂ : ℝ) : NormedSpace.exp
    ((-Complex.I * ((t₁ + t₂ : ℝ) : ℂ)) • H) = NormedSpace.exp ((-Complex.I * (t₁ : ℂ)) • H) *
    NormedSpace.exp ((-Complex.I * (t₂ : ℂ)) • H) := by
  rw [show (-Complex.I * ((t₁ + t₂ : ℝ) : ℂ)) • H =
      (-Complex.I * (t₁ : ℂ)) • H + (-Complex.I * (t₂ : ℂ)) • H by
      rw [← add_smul]
      exact congrArg (· • H) (by
        push_cast
        ring),
    Matrix.exp_add_of_commute _ _ (((Commute.refl H).smul_left _).smul_right _)]
theorem approximatesTimeEvolution_mono {k m : ℕ} {H : Operator (2 ^ k)} {t ε₁ ε₂ : ℝ}
    {P : Operator (2 ^ k)} {W : Unitary (2 ^ (k + m))}
    (h : ApproximatesTimeEvolution H t ε₁ P W) (hε : ε₁ ≤ ε₂) :
    ApproximatesTimeEvolution H t ε₂ P W :=
  let ⟨φ, hφ⟩ := h
  ⟨φ, hφ.trans hε⟩
theorem approximatesTimeEvolution_zero {k m : ℕ} (H : Operator (2 ^ k)) (P : Operator (2 ^ k)) :
    ApproximatesTimeEvolution H 0 0 P (1 : Unitary (2 ^ (k + m))) :=
  ⟨0, by simp [NormedSpace.exp_zero]⟩
theorem approximatesTimeEvolution_mul {k m : ℕ} {H : Operator (2 ^ k)} (hH : H.IsHermitian)
    {P : Operator (2 ^ k)} (hHP : Commute H P) {t₁ t₂ ε₁ ε₂ : ℝ}
    {W₁ W₂ : Unitary (2 ^ (k + m))} (h₁ : ApproximatesTimeEvolution H t₁ ε₁ P W₁)
    (h₂ : ApproximatesTimeEvolution H t₂ ε₂ P W₂) : ApproximatesTimeEvolution H (t₁ + t₂)
    (ε₁ + ε₂) P (W₁ * W₂) := by
  rcases h₁, h₂ with ⟨⟨φ₁, hφ₁⟩, ⟨φ₂, hφ₂⟩⟩
  refine ⟨φ₁ + φ₂, ?_⟩
  set sys : QRegister k (k + m) := .block 0 k (by omega)
  set anc : QRegister m (k + m) := .block k m le_rfl
  set E₁ := NormedSpace.exp ((-Complex.I * (t₁ : ℂ)) • H)
  set E₂ := NormedSpace.exp ((-Complex.I * (t₂ : ℂ)) • H)
  set T₁ := Complex.exp (φ₁ * Complex.I) • sys.embedMatrix E₁
  set T₂ := Complex.exp (φ₂ * Complex.I) • sys.embedMatrix E₂
  set input := sys.embedMatrix P * anc.basisOutcomeProjector 0
  have hE₂_comm_P : sys.embedMatrix E₂ * sys.embedMatrix P =
      sys.embedMatrix P * sys.embedMatrix E₂ := by
    rw [← sys.embedMatrix_mul, ← sys.embedMatrix_mul, (commute_exp_neg_I_smul hHP t₂).eq]
  have hE₂_comm_anc : sys.embedMatrix E₂ * anc.basisOutcomeProjector 0 =
      anc.basisOutcomeProjector 0 * sys.embedMatrix E₂ :=
    sys.embedMatrix_comm_of_disjoint anc
      (QRegister.block_disjoint_of_le 0 k k m (by omega) le_rfl (by omega)) E₂ (compProj 0)
  have hT₂_comm : T₂ * input = input * T₂ := by
    rw [smul_mul_assoc, mul_smul_comm, ← Matrix.mul_assoc, hE₂_comm_P,
      Matrix.mul_assoc (sys.embedMatrix P), hE₂_comm_anc, ← Matrix.mul_assoc]
  have htarget_mul : Complex.exp (((φ₁ + φ₂ : ℝ) : ℂ) * Complex.I) • sys.embedMatrix
      (NormedSpace.exp ((-Complex.I * ((t₁ + t₂ : ℝ) : ℂ)) • H)) = T₁ * T₂ := by
    rw [exp_neg_I_add_smul H t₁ t₂, sys.embedMatrix_mul, smul_mul_smul_comm,
      ← Complex.exp_add, ← add_mul, Complex.ofReal_add]
  have hnorm_T₂ : ‖T₂‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact l2_opNorm_unitary_le_one (sys.embedUnitary (expTimeEvolutionUnitary H hH t₂))
  have hsplit : (W₁.1 * W₂.1 - T₁ * T₂) * input =
      W₁.1 * ((W₂.1 - T₂) * input) + ((W₁.1 - T₁) * input) * T₂ := by
    rw [show ((W₁.1 - T₁) * input) * T₂ = (W₁.1 - T₁) * T₂ * input by
      rw [Matrix.mul_assoc, ← hT₂_comm, ← Matrix.mul_assoc]]
    noncomm_ring
  rw [htarget_mul, Submonoid.coe_mul, hsplit]
  have ht₁ := (Matrix.l2_opNorm_mul W₁.1 ((W₂.1 - T₂) * input)).trans
    ((mul_le_mul_of_nonneg_right (l2_opNorm_unitary_le_one W₁) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hφ₂))
  have ht₂ := (Matrix.l2_opNorm_mul ((W₁.1 - T₁) * input) T₂).trans
    ((mul_le_mul_of_nonneg_left hnorm_T₂ (norm_nonneg _)).trans
      (by simpa only [mul_one] using hφ₁))
  linarith [norm_add_le (W₁.1 * ((W₂.1 - T₂) * input)) (((W₁.1 - T₁) * input) * T₂)]
theorem approximatesTimeEvolution_pow {k m : ℕ} {H : Operator (2 ^ k)} (hH : H.IsHermitian)
    {P : Operator (2 ^ k)} (hHP : Commute H P) {τ ε_seg : ℝ} {W_seg : Unitary (2 ^ (k + m))}
    (hseg : ApproximatesTimeEvolution H τ ε_seg P W_seg) (S : ℕ) : ApproximatesTimeEvolution H
    ((S : ℝ) * τ) ((S : ℝ) * ε_seg) P (W_seg ^ S) := by
  induction S with
  | zero => simpa using approximatesTimeEvolution_zero H P
  | succ S ih =>
      have hadd (x : ℝ) : ((S + 1 : ℕ) : ℝ) * x = (S : ℝ) * x + x := by
        push_cast
        ring
      rw [pow_succ, hadd τ, hadd ε_seg]
      exact approximatesTimeEvolution_mul hH hHP ih hseg
theorem approximatesTimeEvolution_pow_of_div {k m : ℕ} {H : Operator (2 ^ k)}
    (hH : H.IsHermitian) {P : Operator (2 ^ k)} (hHP : Commute H P) {t ε_seg ε : ℝ}
    {W_seg : Unitary (2 ^ (k + m))} {S : ℕ} (hS : S ≠ 0)
    (hseg : ApproximatesTimeEvolution H (t / (S : ℝ)) ε_seg P W_seg)
    (hε : (S : ℝ) * ε_seg ≤ ε) : ApproximatesTimeEvolution H t ε P (W_seg ^ S) := by
  have hpow := approximatesTimeEvolution_pow hH hHP hseg S
  rw [mul_div_cancel₀ t (Nat.cast_ne_zero.mpr hS)] at hpow
  exact approximatesTimeEvolution_mono hpow hε
end SpecsAux
end
end ModSegmentedTimeEvolution

section ModBridgeFermionicComm
@[expose] public section
namespace SpecsAux
open Operator Matrix SpecsAux.SpecMirror
namespace BridgeFermionicComm
open scoped Matrix
section Parametric
variable {d : ℕ}
noncomputable def predProjector (Pred : Fin d → Prop) : Operator d :=
  open Classical in
  Matrix.diagonal fun x ↦ if Pred x then 1 else 0
@[simp] theorem predProjector_mul_self (Pred : Fin d → Prop) :
    predProjector Pred * predProjector Pred = predProjector Pred := by
  classical
  rw [predProjector, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun x ↦ by by_cases hp : Pred x <;> simp [hp])
theorem permutationUnitary_apply (e : Equiv.Perm (Fin d)) (x y : Fin d) :
    (permutationUnitary e).1 x y = if x = e y then 1 else 0 := by
  change (Equiv.Perm.permMatrix ℂ (e⁻¹)) x y = _
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, Equiv.Perm.inv_def]
  by_cases h : x = e y
  · subst h
    simp
  · simp [h, show e.symm x ≠ y from fun heq ↦ h (by rw [← heq, Equiv.apply_symm_apply])]
theorem mul_permutationUnitary_apply (A : Operator d) (e : Equiv.Perm (Fin d)) (x y : Fin d) :
    (A * (permutationUnitary e).1) x y = A x (e y) := by
  rw [Matrix.mul_apply]
  simp_rw [permutationUnitary_apply]
  rw [Finset.sum_eq_single (e y) (fun z _ hz ↦ by rw [ite_eq_right hz, mul_zero])
    (fun h ↦ (h (Finset.mem_univ _)).elim)]
  simp
theorem permutationUnitary_mul_apply (A : Operator d) (e : Equiv.Perm (Fin d)) (x y : Fin d) :
    ((permutationUnitary e).1 * A) x y = A (e.symm x) y := by
  rw [Matrix.mul_apply]
  simp_rw [permutationUnitary_apply]
  rw [Finset.sum_eq_single (e.symm x)
    (fun z _ hz ↦ by
      rw [ite_eq_right (fun heq ↦ hz (by rw [heq, Equiv.symm_apply_apply])), zero_mul])
    (fun h ↦ (h (Finset.mem_univ _)).elim)]
  simp
theorem permutationUnitary_mul_of_comp {e₁ e₂ e₃ : Equiv.Perm (Fin d)}
    (h : ∀ x, e₁ (e₂ x) = e₃ x) : (permutationUnitary e₁).1 * (permutationUnitary e₂).1 =
    (permutationUnitary e₃).1 := by
  ext x y
  rw [mul_permutationUnitary_apply, permutationUnitary_apply, permutationUnitary_apply, h y]
theorem predProjector_comm_permutationUnitary (Pred : Fin d → Prop) (e : Equiv.Perm (Fin d))
    (hpred : ∀ y, Pred (e y) ↔ Pred y) : predProjector Pred * (permutationUnitary e).1 =
    (permutationUnitary e).1 * predProjector Pred := by
  classical
  ext x y
  rw [predProjector, Matrix.diagonal_mul, Matrix.mul_diagonal, permutationUnitary_apply]
  by_cases hxy : x = e y
  · subst hxy
    simp [hpred y]
  · simp [hxy]
theorem commutes_predProjector_of_off_zero (Pred : Fin d → Prop) (A : Operator d)
    (hoff : ∀ x y, ¬ (Pred x ∧ Pred y) → A x y = 0) :
    A * predProjector Pred = predProjector Pred * A := by
  classical
  ext x y
  rw [predProjector, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hxy : Pred x ∧ Pred y
  · simp [hxy.1, hxy.2]
  · simp [hoff x y hxy]
theorem commutes_permutationUnitary_of_entry (e : Equiv.Perm (Fin d)) (A : Operator d)
    (hA : ∀ x y, A (e x) (e y) = A x y) :
    A * (permutationUnitary e).1 = (permutationUnitary e).1 * A := by
  ext x y
  rw [mul_permutationUnitary_apply, permutationUnitary_mul_apply]
  simpa using hA (e.symm x) y
noncomputable def groupAvgProj {ι : Type*} (G : Finset ι) (c : ι → ℂ) (Pred : Fin d → Prop)
    (π : ι → Equiv.Perm (Fin d)) : Operator d := (G.card : ℂ)⁻¹ • ∑ g ∈ G, c g •
    (predProjector Pred * (permutationUnitary (π g)).1)
theorem groupAvgProj_apply {ι : Type*} (G : Finset ι) (c : ι → ℂ)
    (Pred : Fin d → Prop) (π : ι → Equiv.Perm (Fin d)) (x y : Fin d) :
    open Classical in
    groupAvgProj G c Pred π x y =
      if Pred x then (G.card : ℂ)⁻¹ * ∑ g ∈ G, if x = π g y then c g else 0 else 0 := by
  classical
  simp only [groupAvgProj, predProjector, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Matrix.diagonal_mul, permutationUnitary_apply]
  by_cases hx : Pred x <;> simp [hx]
theorem matrix_of_pred_sum_eq_groupAvgProj {ι : Type*} (G : Finset ι) (c : ι → ℂ)
    (Pred : Fin d → Prop) [DecidablePred Pred] (π : ι → Equiv.Perm (Fin d))
    (hpred : ∀ g ∈ G, ∀ y, Pred (π g y) ↔ Pred y) (Rel : ι → Fin d → Fin d → Prop)
    [∀ g x y, Decidable (Rel g x y)]
    (hrel : ∀ g ∈ G, ∀ {x y}, Pred x → Pred y → (Rel g x y ↔ x = π g y)) : (Matrix.of fun x y
    ↦ if Pred x ∧ Pred y then (∑ g ∈ G, if Rel g x y then c g else 0) / G.card else 0) =
    groupAvgProj G c Pred π := by
  classical
  ext x y
  simp only [Matrix.of_apply, groupAvgProj_apply]
  by_cases hx : Pred x
  · by_cases hy : Pred y
    · rw [ite_eq_left ⟨hx, hy⟩, ite_eq_left hx, div_eq_inv_mul]
      exact congrArg _ (Finset.sum_congr rfl fun g hg ↦ if_congr (hrel g hg hx hy) rfl rfl)
    · rw [ite_eq_right (fun h ↦ hy h.2), ite_eq_left hx, Finset.sum_eq_zero (fun g hg ↦
        ite_eq_right fun h ↦ hy ((hpred g hg y).mp (Eq.mp (congrArg Pred h) hx))), mul_zero]
  · rw [ite_eq_right (fun h ↦ hx h.1), ite_eq_right hx]
theorem commutes_groupAvgProj {ι : Type*} (G : Finset ι) (c : ι → ℂ) (Pred : Fin d → Prop)
    (π : ι → Equiv.Perm (Fin d)) (A : Operator d)
    (hgrid : A * predProjector Pred = predProjector Pred * A) (hsymm : ∀ g ∈ G, A *
    (permutationUnitary (π g)).1 = (permutationUnitary (π g)).1 * A) : A * groupAvgProj G c
    Pred π = groupAvgProj G c Pred π * A := by
  simp only [groupAvgProj, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun g hg ↦ congrArg _ ?_)
  rw [← Matrix.mul_assoc, hgrid, Matrix.mul_assoc, hsymm g hg, ← Matrix.mul_assoc]
theorem groupAvgProj_isHermitian {G_type : Type*} [Group G_type] (G : Finset G_type)
    (c : G_type → ℂ) (Pred : Fin d → Prop) (π : G_type → Equiv.Perm (Fin d))
    (hinv : ∀ {g}, g ∈ G → g⁻¹ ∈ G) (hc_real : ∀ g ∈ G, (starRingEnd ℂ) (c g) = c g)
    (hc_inv : ∀ g ∈ G, c g⁻¹ = c g) (hpred : ∀ g ∈ G, ∀ y, Pred (π g y) ↔ Pred y)
    (hπ_inv : ∀ g ∈ G, ∀ y, π g⁻¹ y = (π g).symm y) : (groupAvgProj G c Pred π).IsHermitian := by
  classical
  ext x y
  rw [Matrix.conjTranspose_apply, Complex.star_def, groupAvgProj_apply, groupAvgProj_apply]
  by_cases hx : Pred x
  · by_cases hy : Pred y
    · rw [ite_eq_left hy, ite_eq_left hx, map_mul, map_inv₀, map_natCast, map_sum]
      refine congrArg _ (Finset.sum_bij (fun g _ ↦ g⁻¹) (fun _ hg ↦ hinv hg)
        (fun _ _ _ _ h ↦ inv_injective h) (fun g hg ↦ ⟨g⁻¹, hinv hg, inv_inv g⟩) fun g hg ↦ ?_)
      have heq : (y = π g x) ↔ (x = π g⁻¹ y) := by
        rw [hπ_inv g hg y]
        exact ⟨fun h ↦ by rw [h, Equiv.symm_apply_apply],
          fun h ↦ by rw [h, Equiv.apply_symm_apply]⟩
      by_cases h : x = π g⁻¹ y
      · rw [ite_eq_left (heq.mpr h), ite_eq_left h, hc_real g hg, hc_inv g hg]
      · rw [ite_eq_right (mt heq.mp h), ite_eq_right h, map_zero]
    · rw [ite_eq_right hy, ite_eq_left hx, map_zero, Finset.sum_eq_zero (fun g hg ↦
        ite_eq_right fun h ↦ hy ((hpred g hg y).mp (Eq.mp (congrArg Pred h) hx))), mul_zero]
  · by_cases hy : Pred y
    · rw [ite_eq_left hy, ite_eq_right hx, Finset.sum_eq_zero (fun g hg ↦
        ite_eq_right fun h ↦ hx ((hpred g hg x).mp (Eq.mp (congrArg Pred h) hy))), mul_zero,
        map_zero]
    · rw [ite_eq_right hy, ite_eq_right hx, map_zero]
theorem groupAvgProj_idem {G_type : Type*} [Group G_type] (G : Finset G_type) (c : G_type → ℂ)
    (Pred : Fin d → Prop) (π : G_type → Equiv.Perm (Fin d)) (hG_ne : G.Nonempty)
    (hinv : ∀ {g}, g ∈ G → g⁻¹ ∈ G) (hmul : ∀ {g₁ g₂}, g₁ ∈ G → g₂ ∈ G → g₁ * g₂ ∈ G)
    (hc_mul : ∀ g₁ g₂, c (g₁ * g₂) = c g₁ * c g₂)
    (hpred : ∀ g ∈ G, ∀ y, Pred (π g y) ↔ Pred y)
    (hπ_comp : ∀ g₁ g₂ x, π g₁ (π g₂ x) = π (g₂ * g₁) x) : groupAvgProj G c Pred π *
    groupAvgProj G c Pred π = groupAvgProj G c Pred π := by
  have hcard : (G.card : ℂ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hG_ne
  let P := predProjector Pred
  dsimp only [groupAvgProj]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul]
  have hinner (g₁ : G_type) (hg₁ : g₁ ∈ G) :
      c g₁ • (P * (permutationUnitary (π g₁)).1) *
          ∑ g₂ ∈ G, c g₂ • (P * (permutationUnitary (π g₂)).1) =
        ∑ k ∈ G, c k • (P * (permutationUnitary (π k)).1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun g₂ _ ↦ g₂ * g₁) (fun _ hg₂ ↦ hmul hg₂ hg₁)
      (fun _ _ _ _ h ↦ mul_right_cancel h)
      (fun k hk ↦ ⟨k * g₁⁻¹, hmul hk (hinv hg₁), inv_mul_cancel_right k g₁⟩) fun g₂ _ ↦ ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (c g₁) (c g₂), ← hc_mul]
    refine congrArg _ ?_
    rw [Matrix.mul_assoc P, ← Matrix.mul_assoc (permutationUnitary (π g₁)).1,
      ← predProjector_comm_permutationUnitary Pred (π g₁) (hpred g₁ hg₁),
      Matrix.mul_assoc P (permutationUnitary (π g₁)).1, ← Matrix.mul_assoc P P,
      predProjector_mul_self, permutationUnitary_mul_of_comp (hπ_comp g₁ g₂)]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, mul_assoc, inv_mul_cancel₀ hcard, mul_one]
end Parametric
namespace SpecInner
noncomputable abbrev gridProjector : Operator (2 ^ systemQubits) := predProjector IsGridState
theorem componentBits_pos (a : Particle) : 0 < componentBits a := by
  cases a <;> simp [componentBits, electronBits, projectileBits]
theorem bitOffset_add_componentBits_le (a : Particle) (w : Fin 3) :
    bitOffset a w + componentBits a ≤ systemQubits := by
  cases a with
  | electron i =>
    have hi : i.val < 218 := i.isLt
    have hw : w.val < 3 := w.isLt
    change 6 * (3 * i.val + w.val) + 6 ≤ 3948
    omega
  | projectile =>
    have hw : w.val < 3 := w.isLt
    change 3 * 6 * 218 + 8 * w.val + 8 ≤ 3948
    omega
theorem div_18_lt_numElectrons {n : ℕ} (hn : n < 3924) : n / 18 < numElectrons := by
  change n / 18 < 218
  omega
theorem eq_of_ite_eq {α : Type*} {a b : α} (hne : a ≠ b) {p q : Bool}
    (h : (if p then a else b) = (if q then a else b)) : p = q := by
  cases p <;> cases q <;> first | rfl | exact absurd h (by simpa using hne) |
    exact absurd h (by simpa using hne.symm)
theorem exists_particle_field_of_lt (k : ℕ) (hk : k < systemQubits) : ∃ (a : Particle)
    (w : Fin 3) (b : ℕ), b < componentBits a ∧ k = bitOffset a w + b := by
  change k < 3948 at hk
  by_cases hproj : k < 3924
  · exact ⟨.electron ⟨k / 18, div_18_lt_numElectrons hproj⟩, ⟨(k / 6) % 3, by omega⟩, k % 6,
      show k % 6 < 6 by omega, show k = 6 * (3 * (k / 18) + (k / 6) % 3) + k % 6 by omega⟩
  · exact ⟨.projectile, ⟨(k - 3924) / 8, by omega⟩, (k - 3924) % 8,
      show (k - 3924) % 8 < 8 by omega,
      show k = 3924 + 8 * ((k - 3924) / 8) + (k - 3924) % 8 by omega⟩
theorem testBit_div_two_pow_mod_two_pow (n offset width b : ℕ) (hb : b < width) :
    ((n / 2 ^ offset) % 2 ^ width).testBit b = n.testBit (offset + b) := by
  rw [Nat.testBit_mod_two_pow, decide_eq_true hb, Bool.true_and, Nat.testBit_div_two_pow, add_comm]
theorem signMagnitude_fst_eq_testBit (x : Fin (2 ^ systemQubits)) (a : Particle) (w : Fin 3) :
    (signMagnitude x a w).1 = if x.val.testBit (bitOffset a w + (componentBits a - 1)) then 1
    else 0 := by
  simp only [signMagnitude, Nat.div_div_eq_div_mul, ← pow_add, ← Nat.toNat_testBit]
  cases x.val.testBit (bitOffset a w + (componentBits a - 1)) <;> rfl
theorem signMagnitude_eq_of_testBit_eq (x y : Fin (2 ^ systemQubits)) (a₁ a₂ : Particle)
    (w : Fin 3) (hc : componentBits a₁ = componentBits a₂) (h : ∀ b < componentBits a₁,
    x.val.testBit (bitOffset a₁ w + b) = y.val.testBit (bitOffset a₂ w + b)) : signMagnitude x
    a₁ w = signMagnitude y a₂ w := by
  refine Prod.ext ?_ (Nat.eq_of_testBit_eq fun b ↦ ?_)
  · rw [signMagnitude_fst_eq_testBit, signMagnitude_fst_eq_testBit, ← hc,
      h _ (by
        have := componentBits_pos a₁
        omega)]
  · by_cases hb : b < componentBits a₁ - 1
    · simp only [signMagnitude, testBit_div_two_pow_mod_two_pow _ _ _ _ hb,
        testBit_div_two_pow_mod_two_pow _ _ _ _ (show b < componentBits a₂ - 1 by omega),
        h b (by omega)]
    · simp [signMagnitude, Nat.testBit_mod_two_pow, hb, show ¬(b < componentBits a₂ - 1) by omega]
theorem testBit_eq_of_signMagnitude_eq (x y : Fin (2 ^ systemQubits)) (a : Particle)
    (w : Fin 3) (h : signMagnitude x a w = signMagnitude y a w) (b : ℕ)
    (hb : b < componentBits a) : x.val.testBit (bitOffset a w + b) = y.val.testBit
    (bitOffset a w + b) := by
  by_cases hbs : b = componentBits a - 1
  · subst hbs
    have h1 := congrArg Prod.fst h
    rw [signMagnitude_fst_eq_testBit, signMagnitude_fst_eq_testBit] at h1
    exact eq_of_ite_eq (by decide : (1 : ℕ) ≠ 0) h1
  · have hblt : b < componentBits a - 1 := by
      have := componentBits_pos a
      omega
    simpa only [signMagnitude, testBit_div_two_pow_mod_two_pow _ _ _ _ hblt] using
      congrArg (fun n ↦ n.testBit b) (congrArg Prod.snd h)
theorem eq_of_signMagnitude_eq {x y : Fin (2 ^ systemQubits)}
    (h : ∀ a w, signMagnitude x a w = signMagnitude y a w) : x = y := by
  refine Fin.ext (Nat.eq_of_testBit_eq fun k ↦ ?_)
  by_cases hk : k < systemQubits
  · obtain ⟨a, w, b, hb, rfl⟩ := exists_particle_field_of_lt k hk
    exact testBit_eq_of_signMagnitude_eq x y a w (h a w) b hb
  · rw [Nat.testBit_lt_two_pow (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (y.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
theorem signMagnitude_eq_of_momentum_eq_of_isGridState {x y : Fin (2 ^ systemQubits)}
    (hx : IsGridState x) (hy : IsGridState y) (a : Particle) (w : Fin 3)
    (hm : momentum x a w = momentum y a w) : signMagnitude x a w = signMagnitude y a w := by
  have hs (z : Fin (2 ^ systemQubits)) :
      (signMagnitude z a w).1 = 0 ∨ (signMagnitude z a w).1 = 1 := by
    simp only [signMagnitude]
    omega
  rcases hs x with hsx | hsx <;> rcases hs y with hsy | hsy
  · simp only [momentum, hsx, hsy, pow_zero, one_mul, Nat.cast_inj] at hm
    exact Prod.ext (hsx.trans hsy.symm) hm
  · simp only [momentum, hsx, hsy, pow_zero, pow_one, one_mul, neg_one_mul] at hm
    exact (hy a w (Prod.ext hsy (by omega))).elim
  · simp only [momentum, hsx, hsy, pow_zero, pow_one, one_mul, neg_one_mul] at hm
    exact (hx a w (Prod.ext hsx (by omega))).elim
  · simp only [momentum, hsx, hsy, pow_one, neg_one_mul, neg_inj, Nat.cast_inj] at hm
    exact Prod.ext (hsx.trans hsy.symm) hm
theorem eq_of_momentum_eq_of_isGridState {x y : Fin (2 ^ systemQubits)} (hx : IsGridState x)
    (hy : IsGridState y) (hm : ∀ a w, momentum x a w = momentum y a w) : x = y :=
    eq_of_signMagnitude_eq fun a w ↦ signMagnitude_eq_of_momentum_eq_of_isGridState hx hy a w
    (hm a w)
def permElectronWireFun (g : Equiv.Perm (Fin numElectrons)) (q : Fin systemQubits) :
    Fin systemQubits :=
  if hq : q.val < 3924 then
    let i : Fin numElectrons := ⟨q.val / 18, div_18_lt_numElectrons hq⟩
    let r := q.val % 18
    ⟨18 * (g i).val + r, by
      have hgi : (g i).val < 218 := (g i).isLt
      have hr : r < 18 := Nat.mod_lt _ (by decide)
      change 18 * (g i).val + r < 3948
      omega⟩
  else
    q
theorem permElectronWireFun_inv (g : Equiv.Perm (Fin numElectrons)) (q : Fin systemQubits) :
    permElectronWireFun g.symm (permElectronWireFun g q) = q := by
  apply Fin.ext
  by_cases hq : q.val < 3924
  · have hgi : (g ⟨q.val / 18, div_18_lt_numElectrons hq⟩).val < 218 :=
      (g ⟨q.val / 18, div_18_lt_numElectrons hq⟩).isLt
    have hlt : 18 * (g ⟨q.val / 18, div_18_lt_numElectrons hq⟩).val + q.val % 18 < 3924 := by
      omega
    unfold permElectronWireFun
    rw [dite_eq_left hq]
    dsimp only
    rw [dite_eq_left hlt]
    dsimp only
    have hfin : (⟨(18 * (g ⟨q.val / 18, div_18_lt_numElectrons hq⟩).val + q.val % 18) / 18,
        div_18_lt_numElectrons hlt⟩ : Fin numElectrons) =
        g ⟨q.val / 18, div_18_lt_numElectrons hq⟩ := Fin.ext (by
      dsimp
      omega)
    rw [hfin, Equiv.symm_apply_apply]
    change 18 * (q.val / 18) + (18 * _ + q.val % 18) % 18 = q.val
    omega
  · unfold permElectronWireFun
    rw [dite_eq_right hq, dite_eq_right hq]
def permElectronWire (g : Equiv.Perm (Fin numElectrons)) :
    Equiv.Perm (Fin systemQubits) where
  toFun := permElectronWireFun g
  invFun := permElectronWireFun g.symm
  left_inv := permElectronWireFun_inv g
  right_inv := permElectronWireFun_inv g.symm
def permElectron (g : Equiv.Perm (Fin numElectrons)) : Equiv.Perm (Fin (2 ^ systemQubits)) :=
    (basisBitsEquiv systemQubits).trans ((Equiv.piCongrLeft' (fun _ ↦ ZMod 2)
    (permElectronWire g).symm).trans (basisBitsEquiv systemQubits).symm)
theorem basisBits_permElectron {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Fin (2 ^ N)) (q : Fin N)
    : basisBits N (((basisBitsEquiv N).trans ((Equiv.piCongrLeft' (fun _ ↦ ZMod 2)
    π.symm).trans (basisBitsEquiv N).symm)) x) q = basisBits N x (π q) := by
  simp
theorem testBit_permElectron (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) (q : Fin systemQubits) :
    (permElectron g x).val.testBit q.val = x.val.testBit (permElectronWire g q).val := by
  have h := basisBits_permElectron (permElectronWire g) x q
  change basisBits systemQubits (permElectron g x) q =
    basisBits systemQubits x (permElectronWire g q) at h
  rw [basisBits_eq_testBit, basisBits_eq_testBit] at h
  exact eq_of_ite_eq (by decide : (1 : ZMod 2) ≠ 0) h
theorem permElectronWire_electron (g : Equiv.Perm (Fin numElectrons)) (i : Fin numElectrons)
    (w : Fin 3) (b : ℕ) (hb : b < electronBits) : (permElectronWire g ⟨bitOffset (.electron i)
    w + b, lt_of_lt_of_le (Nat.add_lt_add_left hb _) (bitOffset_add_componentBits_le
    (.electron i) w)⟩).val = bitOffset (.electron (g i)) w + b := by
  have hi : i.val < 218 := i.isLt
  have hw : w.val < 3 := w.isLt
  change b < 6 at hb
  have hlt : bitOffset (.electron i) w + b < 3924 := by
    change 6 * (3 * i.val + w.val) + b < 3924
    omega
  change (permElectronWireFun g ⟨bitOffset (.electron i) w + b, _⟩).val = _
  unfold permElectronWireFun
  rw [dite_eq_left hlt]
  dsimp only
  have hdiv : (bitOffset (.electron i) w + b) / 18 = i.val := by
    change (6 * (3 * i.val + w.val) + b) / 18 = i.val
    omega
  rw [show (⟨(bitOffset (.electron i) w + b) / 18, div_18_lt_numElectrons hlt⟩ :
      Fin numElectrons) = i from Fin.ext hdiv]
  change 18 * (g i).val + (6 * (3 * i.val + w.val) + b) % 18 = 6 * (3 * (g i).val + w.val) + b
  omega
theorem permElectronWire_projectile (g : Equiv.Perm (Fin numElectrons)) (w : Fin 3) (b : ℕ)
    (hb : b < projectileBits) : (permElectronWire g ⟨bitOffset .projectile w + b,
    lt_of_lt_of_le (Nat.add_lt_add_left hb _) (bitOffset_add_componentBits_le .projectile
    w)⟩).val = bitOffset .projectile w + b := by
  have hge : ¬ (bitOffset .projectile w + b < 3924) := by
    change ¬ (3924 + 8 * w.val + b < 3924)
    omega
  change (permElectronWireFun g ⟨bitOffset .projectile w + b, _⟩).val = _
  unfold permElectronWireFun
  rw [dite_eq_right hge]
theorem signMagnitude_permElectron_electron (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons) (w : Fin 3) : signMagnitude
    (permElectron g x) (.electron i) w = signMagnitude x (.electron (g i)) w :=
  signMagnitude_eq_of_testBit_eq (permElectron g x) x (.electron i) (.electron (g i)) w rfl
    fun b hb ↦ (testBit_permElectron g x ⟨bitOffset (.electron i) w + b,
      lt_of_lt_of_le (Nat.add_lt_add_left hb _)
        (bitOffset_add_componentBits_le (.electron i) w)⟩).trans
      (congrArg x.val.testBit (permElectronWire_electron g i w b hb))
theorem signMagnitude_permElectron_projectile (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    signMagnitude (permElectron g x) .projectile w = signMagnitude x .projectile w :=
  signMagnitude_eq_of_testBit_eq (permElectron g x) x .projectile .projectile w rfl
    fun b hb ↦ (testBit_permElectron g x ⟨bitOffset .projectile w + b,
      lt_of_lt_of_le (Nat.add_lt_add_left hb _)
        (bitOffset_add_componentBits_le .projectile w)⟩).trans
      (congrArg x.val.testBit (permElectronWire_projectile g w b hb))
theorem momentum_permElectron_electron (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons) :
    momentum (permElectron g x) (.electron i) = momentum x (.electron (g i)) :=
  funext fun w ↦ by simp only [momentum, signMagnitude_permElectron_electron]
theorem momentum_permElectron_projectile (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) :
    momentum (permElectron g x) .projectile = momentum x .projectile :=
  funext fun w ↦ by simp only [momentum, signMagnitude_permElectron_projectile]
theorem permElectron_comp_apply (g₁ g₂ : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) :
    permElectron g₁ (permElectron g₂ x) = permElectron (g₂ * g₁) x :=
  eq_of_signMagnitude_eq fun a w ↦ by
    cases a <;> simp [signMagnitude_permElectron_electron,
      signMagnitude_permElectron_projectile, Equiv.Perm.mul_apply]
theorem permElectron_one (x : Fin (2 ^ systemQubits)) : permElectron 1 x = x :=
  eq_of_signMagnitude_eq fun a w ↦ by
    cases a <;> simp [signMagnitude_permElectron_electron, signMagnitude_permElectron_projectile]
theorem permElectron_inv_apply (g : Equiv.Perm (Fin numElectrons))
    (y : Fin (2 ^ systemQubits)) : permElectron g⁻¹ y = (permElectron g).symm y :=
  (permElectron g).injective (by
    rw [permElectron_comp_apply, inv_mul_cancel, permElectron_one, Equiv.apply_symm_apply])
theorem isGridState_permElectron (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) : IsGridState (permElectron g x) ↔ IsGridState x := by
  refine ⟨fun h a w ↦ ?_, fun h a w ↦ ?_⟩
  · cases a with
    | electron j => simpa [signMagnitude_permElectron_electron] using h (.electron (g.symm j)) w
    | projectile => simpa [signMagnitude_permElectron_projectile] using h .projectile w
  · cases a with
    | electron i => simpa [signMagnitude_permElectron_electron] using h (.electron (g i)) w
    | projectile => simpa [signMagnitude_permElectron_projectile] using h .projectile w
theorem grid_momentum_perm_iff (g : Equiv.Perm (Fin numElectrons))
    {x y : Fin (2 ^ systemQubits)} (hx : IsGridState x) (hy : IsGridState y) : (momentum x
    .projectile = momentum y .projectile ∧ ∀ i, momentum x (.electron i) = momentum y
    (.electron (g i))) ↔ x = permElectron g y := by
  refine ⟨fun ⟨hp, he⟩ ↦ eq_of_momentum_eq_of_isGridState hx ((isGridState_permElectron g y).2 hy)
    fun a w ↦ ?_, ?_⟩
  · cases a with
    | electron i => rw [momentum_permElectron_electron, he i]
    | projectile => rw [momentum_permElectron_projectile, hp]
  · rintro rfl
    exact ⟨momentum_permElectron_projectile g y, fun i ↦ momentum_permElectron_electron g y i⟩
def spinGroupAux {η : ℕ} (spinUp : Finset (Fin η)) : Finset (Equiv.Perm (Fin η)) :=
  {g | ∀ i, g i ∈ spinUp ↔ i ∈ spinUp}
theorem mem_spinGroupAux_iff {η : ℕ} (spinUp : Finset (Fin η)) (g : Equiv.Perm (Fin η)) : g ∈
    spinGroupAux spinUp ↔ ∀ i, g i ∈ spinUp ↔ i ∈ spinUp := by
  simp only [spinGroupAux, Finset.mem_filter, Finset.mem_univ, true_and]
theorem card_spinGroupAux {η : ℕ} (spinUp : Finset (Fin η)) : (spinGroupAux spinUp).card =
    spinUp.card.factorial * (η - spinUp.card).factorial := by
  have heq : {g : Equiv.Perm (Fin η) // ∀ i, g i ∈ spinUp ↔ i ∈ spinUp} ≃
      Equiv.Perm {i : Fin η // i ∈ spinUp} × Equiv.Perm {i : Fin η // i ∉ spinUp} :=
    { toFun := fun ⟨g, hg⟩ ↦
        (Equiv.subtypeEquiv g fun i ↦ (hg i).symm,
         Equiv.subtypeEquiv g fun i ↦ not_congr (hg i).symm)
      invFun := fun ⟨gUp, gDown⟩ ↦ ⟨Equiv.Perm.subtypeCongr gUp gDown, fun i ↦ by
        by_cases hi : i ∈ spinUp
        · simp [Equiv.Perm.subtypeCongr, hi]
        · simp [Equiv.Perm.subtypeCongr, hi, (gDown ⟨i, hi⟩).2]⟩
      left_inv := fun ⟨g, _⟩ ↦ Subtype.ext (Equiv.ext fun i ↦ by
        by_cases hi : i ∈ spinUp <;> simp [Equiv.Perm.subtypeCongr, Equiv.subtypeEquiv, hi])
      right_inv := fun ⟨gUp, gDown⟩ ↦ Prod.ext
        (Equiv.ext fun ⟨i, hi⟩ ↦ by simp [Equiv.Perm.subtypeCongr, Equiv.subtypeEquiv, *])
        (Equiv.ext fun ⟨i, hi⟩ ↦ by simp [Equiv.Perm.subtypeCongr, Equiv.subtypeEquiv, *]) }
  rw [spinGroupAux, ← Fintype.card_subtype, Fintype.card_congr heq, Fintype.card_prod,
    Fintype.card_perm, Fintype.card_perm, Fintype.card_coe, Fintype.card_subtype_compl,
    Fintype.card_fin, Fintype.card_coe]
theorem spinGroupAux_nonempty {η : ℕ} (spinUp : Finset (Fin η)) :
    (spinGroupAux spinUp).Nonempty := ⟨1, (mem_spinGroupAux_iff spinUp 1).mpr fun _ ↦ Iff.rfl⟩
theorem spinGroupAux_inv {η : ℕ} {spinUp : Finset (Fin η)} {g : Equiv.Perm (Fin η)}
    (hg : g ∈ spinGroupAux spinUp) : g⁻¹ ∈ spinGroupAux spinUp :=
  (mem_spinGroupAux_iff _ _).mpr fun i ↦ by
    simpa using ((mem_spinGroupAux_iff _ _).mp hg (g.symm i)).symm
theorem spinGroupAux_mul {η : ℕ} {spinUp : Finset (Fin η)} {g₁ g₂ : Equiv.Perm (Fin η)}
    (hg₁ : g₁ ∈ spinGroupAux spinUp) (hg₂ : g₂ ∈ spinGroupAux spinUp) :
    g₁ * g₂ ∈ spinGroupAux spinUp :=
  (mem_spinGroupAux_iff _ _).mpr fun i ↦
    ((mem_spinGroupAux_iff _ _).mp hg₁ (g₂ i)).trans ((mem_spinGroupAux_iff _ _).mp hg₂ i)
theorem int_units_inv_eq_self (u : ℤˣ) : u⁻¹ = u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl
theorem fermionicProjector_eq_groupAvgProj (spinUp : Finset (Fin numElectrons)) :
    fermionicProjector spinUp = groupAvgProj (spinGroupAux spinUp)
    (fun g ↦ ((Equiv.Perm.sign g : ℤ) : ℂ)) IsGridState permElectron := by
  classical
  have hrew : fermionicProjector spinUp = Matrix.of fun x y ↦ if IsGridState x ∧ IsGridState y
      then (∑ g ∈ spinGroupAux spinUp, if momentum x .projectile = momentum y .projectile ∧ ∀
      i, momentum x (.electron i) = momentum y (.electron (g i)) then ((Equiv.Perm.sign g : ℤ)
      : ℂ) else 0) / ((spinGroupAux spinUp).card : ℂ) else 0 := by
    ext x y
    simp only [fermionicProjector, Matrix.of_apply, ← card_spinGroupAux spinUp]
    by_cases hxy : IsGridState x ∧ IsGridState y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
      refine congrArg (· / ((spinGroupAux spinUp).card : ℂ)) ?_
      rw [spinGroupAux, Finset.sum_filter]
      exact Finset.sum_congr rfl fun g _ ↦ by
        by_cases hg : ∀ i, g i ∈ spinUp ↔ i ∈ spinUp <;> simp [hg]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
  rw [hrew]
  exact matrix_of_pred_sum_eq_groupAvgProj (spinGroupAux spinUp)
    (fun g ↦ ((Equiv.Perm.sign g : ℤ) : ℂ)) IsGridState permElectron
    (fun g _ y ↦ isGridState_permElectron g y) (fun g x y ↦ momentum x .projectile = momentum
    y .projectile ∧ ∀ i, momentum x (.electron i) = momentum y (.electron (g i)))
    (fun g _ _ _ hx hy ↦ grid_momentum_perm_iff g hx hy)
theorem fermionicProjector_isHermitian (spinUp : Finset (Fin numElectrons)) :
    (fermionicProjector spinUp).IsHermitian := by
  rw [fermionicProjector_eq_groupAvgProj spinUp]
  refine groupAvgProj_isHermitian (spinGroupAux spinUp)
    (fun g ↦ ((Equiv.Perm.sign g : ℤ) : ℂ)) IsGridState permElectron
    spinGroupAux_inv (fun _ _ ↦ by simp) (fun _ _ ↦ by rw [map_inv, int_units_inv_eq_self])
    (fun g _ y ↦ isGridState_permElectron g y) (fun g _ y ↦ permElectron_inv_apply g y)
theorem fermionicProjector_idem (spinUp : Finset (Fin numElectrons)) :
    fermionicProjector spinUp * fermionicProjector spinUp = fermionicProjector spinUp := by
  rw [fermionicProjector_eq_groupAvgProj spinUp]
  exact groupAvgProj_idem (spinGroupAux spinUp) (fun g ↦ ((Equiv.Perm.sign g : ℤ) : ℂ))
    IsGridState permElectron (spinGroupAux_nonempty spinUp) spinGroupAux_inv spinGroupAux_mul
    (fun _ _ ↦ by rw [map_mul, Units.val_mul, Int.cast_mul])
    (fun g _ y ↦ isGridState_permElectron g y) permElectron_comp_apply
theorem stepVector_neg (ν : Fin 3 → ℤ) : waveVector (-ν) = -waveVector ν :=
  funext fun _ ↦ by simp [waveVector, neg_div]
theorem stepNumberSq_neg (ν : Fin 3 → ℤ) : waveNumberSq (-ν) = waveNumberSq ν := by
  simp only [waveNumberSq, stepVector_neg, dotProduct_neg, neg_dotProduct, neg_neg]
theorem coulombKernel_neg (ν : Fin 3 → ℤ) : coulombKernel (-ν) = coulombKernel ν := by
  simp only [coulombKernel, stepNumberSq_neg]
def particlePerm (g : Equiv.Perm (Fin numElectrons)) : Equiv.Perm Particle where
  toFun
    | .electron i => .electron (g i)
    | .projectile => .projectile
  invFun
    | .electron i => .electron (g⁻¹ i)
    | .projectile => .projectile
  left_inv a := by cases a <;> simp
  right_inv a := by cases a <;> simp
@[simp]
theorem particlePerm_electron (g : Equiv.Perm (Fin numElectrons)) (i : Fin numElectrons) :
    particlePerm g (.electron i) = .electron (g i) := rfl
@[simp] theorem particlePerm_projectile (g : Equiv.Perm (Fin numElectrons)) :
    particlePerm g .projectile = .projectile := rfl
@[simp] theorem charge_particlePerm (g : Equiv.Perm (Fin numElectrons)) (a : Particle) :
    charge (particlePerm g a) = charge a := by
  cases a <;> rfl
theorem momentum_permElectron_particle (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) (a : Particle) :
    momentum (permElectron g x) a = momentum x (particlePerm g a) := by
  cases a with
  | electron i => exact momentum_permElectron_electron g x i
  | projectile => exact momentum_permElectron_projectile g x
theorem kineticEnergy_permElectron (c : Configuration) (g : Equiv.Perm (Fin numElectrons))
    (x : Fin (2 ^ systemQubits)) :
    kineticEnergy c (momentum (permElectron g x)) = kineticEnergy c (momentum x) := by
  dsimp only [kineticEnergy]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp_rw [momentum_permElectron_electron]
    exact Equiv.sum_comp g (fun i ↦ waveNumberSq (momentum x (.electron i)) / 2)
  · rw [momentum_permElectron_projectile]
theorem hamiltonian_permElectron (c : Configuration) (g : Equiv.Perm (Fin numElectrons))
    (x y : Fin (2 ^ systemQubits)) :
    hamiltonian c (permElectron g x) (permElectron g y) = hamiltonian c x y := by
  classical
  simp only [hamiltonian, Matrix.of_apply, isGridState_permElectron]
  by_cases hxy : IsGridState x ∧ IsGridState y
  · rw [ite_eq_left hxy, ite_eq_left hxy]
    have hfor (P : Particle → Prop) : (∀ d, P (particlePerm g d)) ↔ (∀ d, P d) :=
      ⟨fun h d ↦ by simpa using h ((particlePerm g).symm d), fun h d ↦ h _⟩
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) (congrArg Complex.ofReal ?_)
    · rw [if_congr (permElectron g).apply_eq_iff_eq rfl rfl, kineticEnergy_permElectron]
    · refine Eq.trans (Finset.sum_congr rfl fun a _ ↦ ?_) (Equiv.sum_comp (particlePerm g) fun a ↦
        if ∀ b ≠ a, momentum x b = momentum y b then (charge a : ℂ) *
          structureFactor c (momentum x a - momentum y a) *
          (coulombKernel (momentum x a - momentum y a) : ℂ) else 0)
      rw [if_congr (by
        simpa only [ne_eq, (particlePerm g).apply_eq_iff_eq, momentum_permElectron_particle] using
          hfor fun b ↦ b ≠ particlePerm g a → momentum x b = momentum y b) rfl rfl]
      simp only [momentum_permElectron_particle, charge_particlePerm]
    · let term (u v : Particle) : ℝ :=
        if u ≠ v ∧ (∀ d, d ≠ u → d ≠ v → momentum x d = momentum y d) ∧
            momentum x u + momentum x v = momentum y u + momentum y v then
          (charge u : ℝ) * (charge v : ℝ) * coulombKernel (momentum x u - momentum y u) / 2
        else 0
      refine Eq.trans (Finset.sum_congr rfl fun a _ ↦ Eq.trans (Finset.sum_congr rfl fun b _ ↦ ?_)
        (Equiv.sum_comp (particlePerm g) (term (particlePerm g a))))
        (Equiv.sum_comp (particlePerm g) fun a ↦ ∑ b, term a b)
      have hcond : (a ≠ b ∧
          (∀ d, d ≠ a → d ≠ b → momentum (permElectron g x) d = momentum (permElectron g y) d) ∧
          momentum (permElectron g x) a + momentum (permElectron g x) b =
            momentum (permElectron g y) a + momentum (permElectron g y) b) ↔
          (particlePerm g a ≠ particlePerm g b ∧
            (∀ d, d ≠ particlePerm g a → d ≠ particlePerm g b → momentum x d = momentum y d) ∧
            momentum x (particlePerm g a) + momentum x (particlePerm g b) =
              momentum y (particlePerm g a) + momentum y (particlePerm g b)) := by
        simp only [ne_eq, (particlePerm g).apply_eq_iff_eq, momentum_permElectron_particle]
        exact and_congr_right fun _ ↦ and_congr_left fun _ ↦ by
          simpa only [ne_eq, (particlePerm g).apply_eq_iff_eq] using
            hfor fun d ↦ d ≠ particlePerm g a → d ≠ particlePerm g b →
              momentum x d = momentum y d
      rw [if_congr hcond rfl rfl]
      simp only [momentum_permElectron_particle, charge_particlePerm, term]
  · rw [ite_eq_right hxy, ite_eq_right hxy]
theorem hamiltonian_comm_fermionicProjector (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) : hamiltonian c * fermionicProjector spinUp =
    fermionicProjector spinUp * hamiltonian c := by
  classical
  rw [fermionicProjector_eq_groupAvgProj spinUp]
  exact commutes_groupAvgProj (spinGroupAux spinUp) (fun g ↦ ((Equiv.Perm.sign g : ℤ) : ℂ))
    IsGridState permElectron (hamiltonian c)
    (commutes_predProjector_of_off_zero _ _ fun x y hxy ↦ by
      simpa only [hamiltonian, Matrix.of_apply] using ite_eq_right hxy)
    (fun g _ ↦ commutes_permutationUnitary_of_entry (permElectron g) (hamiltonian c)
      (hamiltonian_permElectron c g))
end SpecInner
end BridgeFermionicComm
end SpecsAux
end
end ModBridgeFermionicComm

section ModSingleRBEGridGuardWalk
@[expose] public section
namespace SingleRBEGridGuardWalkAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
end SingleRBEGridGuardWalkAlt
namespace SingleRBEGridGuardWalk
open Operator Matrix Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
private lemma lemHex152 (q : ℕ) (i : Fin q) : basisBits q (0 : Fin (2 ^ q)) i = 0 := by
  simp [-Nat.reducePow, basisBits_eq_div_mod]
private lemma lemHex153 {q : ℕ} (b : BitAssignment q) :
    basisBits q ((basisBitsEquiv q).symm b) = b :=
  Equiv.apply_symm_apply (basisBitsEquiv q) b
private lemma lemHex154 {r N : ℕ} (reg : QRegister r N) (o : Fin (2 ^ r)) (M : Operator (2 ^ N))
    (i j : Fin (2 ^ N)) : (reg.basisOutcomeProjector o * M) i j = if reg.extractIndex i = o
    then M i j else 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul]
  by_cases h : reg.extractIndex i = o <;> simp [h]
private lemma lemHex155 {r N : ℕ} (M : Operator (2 ^ N)) (reg : QRegister r N) (o : Fin (2 ^ r))
    (i j : Fin (2 ^ N)) : (M * reg.basisOutcomeProjector o) i j = if reg.extractIndex j = o
    then M i j else 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal]
  by_cases h : reg.extractIndex j = o <;> simp [h]
noncomputable def projGridAncZero (k m : ℕ) (P : Operator (2 ^ k)) : Operator (2 ^ (k + m)) :=
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  sys.embedMatrix P * anc.basisOutcomeProjector 0
noncomputable def phaseOp {d : ℕ} (c : ℂ) (P : Operator d) : Operator d := 1 + (c - 1) • P
noncomputable def reflOfProj {d : ℕ} (P : Operator d) : Operator d := (2 : ℂ) • P - 1
noncomputable def singleRBEReflMatrix (k m : ℕ) (P : Operator (2 ^ k)) : Operator (2 ^ (k + m)) :=
  reflOfProj (projGridAncZero k m P)
noncomputable def singleRBEReflNegMatrix (k m : ℕ) (P : Operator (2 ^ k)) : Operator
    (2 ^ (k + m)) := 1 - (2 : ℂ) • projGridAncZero k m P
theorem phaseOp_neg_one {d : ℕ} (P : Operator d) : phaseOp (-1 : ℂ) P = 1 - (2 : ℂ) • P := by
  rw [phaseOp, show (-1 - 1 : ℂ) = -(2 : ℂ) by norm_num, neg_smul, sub_eq_add_neg]
theorem reflOfProj_conjTranspose {d : ℕ} {P : Operator d} (hP_herm : P.IsHermitian) :
    (reflOfProj P)ᴴ = reflOfProj P := by
  simp [reflOfProj, conjTranspose_sub, conjTranspose_smul, hP_herm.eq]
theorem reflOfProj_mul_self {d : ℕ} {P : Operator d} (hP_idem : P * P = P) :
    reflOfProj P * reflOfProj P = 1 := by
  rw [reflOfProj, (two_smul ℂ P).trans (two_mul P).symm,
    show (2 * P - 1) * (2 * P - 1) = 4 * (P * P - P) + 1 by noncomm_ring,
    hP_idem, sub_self, mul_zero, zero_add]
theorem basisOutcomeProjector_idem {n m : ℕ} (r : QRegister m n) (o : Fin (2 ^ m)) :
    r.basisOutcomeProjector o * r.basisOutcomeProjector o = r.basisOutcomeProjector o :=
  r.basisOutcomeProjector_mul_self o
theorem basisOutcomeProjector_mul_eq_zero_of_ne {n m : ℕ} (r : QRegister m n)
    {o₁ o₂ : Fin (2 ^ m)} (hne : o₁ ≠ o₂) :
    r.basisOutcomeProjector o₁ * r.basisOutcomeProjector o₂ = 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h₁ : r.extractIndex i = o₁
    · simp [h₁, hne]
    · simp [h₁]
  · simp [hij]
theorem embedMatrix_comm_basisOutcomeProjector_disjoint {n k m : ℕ} (rAct : QRegister k n)
    (rWork : QRegister m n) (hdisj : rAct.DisjointWires rWork) (A : Operator (2 ^ k))
    (o : Fin (2 ^ m)) : rAct.embedMatrix A * rWork.basisOutcomeProjector o =
    rWork.basisOutcomeProjector o * rAct.embedMatrix A :=
  rAct.embedMatrix_comm_of_disjoint rWork hdisj A (compProj o)
theorem projGridAncZero_isHermitian (k m : ℕ) {P : Operator (2 ^ k)} (hP_herm : P.IsHermitian) :
    (projGridAncZero k m P).IsHermitian := by
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  have hcomm := embedMatrix_comm_basisOutcomeProjector_disjoint sys anc
    (QRegister.block_disjoint_of_le 0 k k m (by omega) le_rfl (by omega)) P 0
  change (sys.embedMatrix P * anc.basisOutcomeProjector 0)ᴴ =
    sys.embedMatrix P * anc.basisOutcomeProjector 0
  rw [conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose,
    ← sys.embedMatrix_conjTranspose, hP_herm.eq, hcomm]
theorem projGridAncZero_idem (k m : ℕ) {P : Operator (2 ^ k)} (hP_idem : P * P = P) :
    projGridAncZero k m P * projGridAncZero k m P = projGridAncZero k m P := by
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  have hcomm := embedMatrix_comm_basisOutcomeProjector_disjoint sys anc
    (QRegister.block_disjoint_of_le 0 k k m (by omega) le_rfl (by omega)) P 0
  change (sys.embedMatrix P * anc.basisOutcomeProjector 0) *
      (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
    sys.embedMatrix P * anc.basisOutcomeProjector 0
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (anc.basisOutcomeProjector 0), ← hcomm,
    Matrix.mul_assoc (sys.embedMatrix P), basisOutcomeProjector_idem,
    ← Matrix.mul_assoc, ← sys.embedMatrix_mul, hP_idem]
abbrev sysReg (k m : ℕ) : QRegister k (k + (m + 1)) := .block 0 k (by omega)
abbrev ancReg (k m : ℕ) : QRegister m (k + (m + 1)) := .block k m (by omega)
abbrev baseReg (k m : ℕ) : QRegister (k + m) (k + (m + 1)) := .block 0 (k + m) (by omega)
abbrev ancGhostReg (k m : ℕ) : QRegister (m + 1) (k + (m + 1)) := .block k (m + 1) le_rfl
abbrev ghostWire (k m : ℕ) : Wire (k + (m + 1)) := ⟨k + m, by omega⟩
abbrev ghostReg (k m : ℕ) : QRegister 1 (k + (m + 1)) := .singleton (ghostWire k m)
noncomputable def ghostZeroProj (k m : ℕ) : Operator (2 ^ (k + (m + 1))) :=
  (ghostReg k m).basisOutcomeProjector 0
noncomputable def ghostOneProj (k m : ℕ) : Operator (2 ^ (k + (m + 1))) :=
  (ghostReg k m).basisOutcomeProjector 1
noncomputable def ancGhostZeroProj (k m : ℕ) : Operator (2 ^ (k + (m + 1))) :=
  (ancGhostReg k m).basisOutcomeProjector 0
noncomputable def diagProj (k : ℕ) (Valid : Fin (2 ^ k) → Bool) : Operator (2 ^ k) :=
  Matrix.diagonal (fun x ↦ if Valid x then (1 : ℂ) else 0)
theorem diagProj_isHermitian (k : ℕ) (Valid : Fin (2 ^ k) → Bool) :
    (diagProj k Valid).IsHermitian := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    cases Valid x <;> simp [diagProj]
  · simp [diagProj, hxy, Ne.symm hxy]
theorem diagProj_idem (k : ℕ) (Valid : Fin (2 ^ k) → Bool) :
    diagProj k Valid * diagProj k Valid = diagProj k Valid := by
  unfold diagProj
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  cases Valid x <;> simp
theorem diagProj_conj_apply (k : ℕ) (Valid : Fin (2 ^ k) → Bool) (A : Operator (2 ^ k))
    (x y : Fin (2 ^ k)) : (diagProj k Valid * A * diagProj k Valid) x y = if Valid x && Valid
    y then A x y else 0 := by
  unfold diagProj
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases Valid x <;> cases Valid y <;> simp
noncomputable def ghostGuardStep (k m : ℕ) (Valid : Fin (2 ^ k) → Bool)
    (g : Fin (2 ^ (k + (m + 1)))) : Fin (2 ^ (k + (m + 1))) := if (ancReg k m).extractIndex g
    = 0 ∧ Valid ((sysReg k m).extractIndex g) = false then (basisBitsEquiv (k + (m + 1))).symm
    (Function.update (basisBits (k + (m + 1)) g) (ghostWire k m) (basisBits (k + (m + 1)) g
    (ghostWire k m) + 1)) else g
private lemma lemHex158 (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) (g : Fin (2 ^ (k + (m + 1))))
    (hcond : (ancReg k m).extractIndex g = 0 ∧ Valid ((sysReg k m).extractIndex g) = false) :
    ghostGuardStep k m Valid g = (basisBitsEquiv (k + (m + 1))).symm (Function.update
    (basisBits (k + (m + 1)) g) (ghostWire k m) (basisBits (k + (m + 1)) g (ghostWire k m) +
    1)) := ite_eq_left hcond
private lemma lemHex159 (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) (g : Fin (2 ^ (k + (m + 1))))
    (hcond : ¬ ((ancReg k m).extractIndex g = 0 ∧ Valid ((sysReg k m).extractIndex g) =
    false)) : ghostGuardStep k m Valid g = g := ite_eq_right hcond
private lemma lemHex15a (k m : ℕ) (Valid : Fin (2 ^ k) → Bool)
    (g : Fin (2 ^ (k + (m + 1)))) (w : Wire (k + (m + 1))) (hw : w.val < k + m) :
    basisBits (k + (m + 1)) (ghostGuardStep k m Valid g) w = basisBits (k + (m + 1)) g w := by
  by_cases hcond : (ancReg k m).extractIndex g = 0 ∧ Valid ((sysReg k m).extractIndex g) = false
  · rw [lemHex158 k m Valid g hcond, lemHex153, Function.update_of_ne]
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [ghostWire] at hv
    omega
  · rw [lemHex159 k m Valid g hcond]
private theorem ghostGuardStep_block {k m off w : ℕ} (hw : off + w ≤ k + m)
    (h : off + w ≤ k + (m + 1)) (Valid : Fin (2 ^ k) → Bool) (g : Fin (2 ^ (k + (m + 1)))) :
    (QRegister.block off w h).extractIndex (ghostGuardStep k m Valid g) =
      (QRegister.block off w h).extractIndex g :=
  (basisBitsEquiv w).injective (funext fun idx ↦ by
    simpa [-Nat.reducePow, basisBitsEquiv, QRegister.basisBits_extractIndex] using
      lemHex15a k m Valid g _ (by
        dsimp [SingleRBEGridGuardWalkAlt.qreg_block_apply]
        omega))
theorem ghostGuardStep_baseReg (k m : ℕ) (Valid : Fin (2 ^ k) → Bool)
    (g : Fin (2 ^ (k + (m + 1)))) :
    (baseReg k m).extractIndex (ghostGuardStep k m Valid g) = (baseReg k m).extractIndex g :=
  ghostGuardStep_block (by omega) _ Valid g
theorem ghostGuardStep_sysReg (k m : ℕ) (Valid : Fin (2 ^ k) → Bool)
    (g : Fin (2 ^ (k + (m + 1)))) :
    (sysReg k m).extractIndex (ghostGuardStep k m Valid g) = (sysReg k m).extractIndex g :=
  ghostGuardStep_block (by omega) _ Valid g
theorem ghostGuardStep_ancReg (k m : ℕ) (Valid : Fin (2 ^ k) → Bool)
    (g : Fin (2 ^ (k + (m + 1)))) :
    (ancReg k m).extractIndex (ghostGuardStep k m Valid g) = (ancReg k m).extractIndex g :=
  ghostGuardStep_block (by omega) _ Valid g
@[simp] theorem ghostGuardStep_involutive (k m : ℕ) (Valid : Fin (2 ^ k) → Bool)
    (g : Fin (2 ^ (k + (m + 1)))) :
    ghostGuardStep k m Valid (ghostGuardStep k m Valid g) = g := by
  by_cases hcond : (ancReg k m).extractIndex g = 0 ∧ Valid ((sysReg k m).extractIndex g) = false
  · set g' := ghostGuardStep k m Valid g
    have hcond' : (ancReg k m).extractIndex g' = 0 ∧
        Valid ((sysReg k m).extractIndex g') = false := by
      rwa [ghostGuardStep_ancReg, ghostGuardStep_sysReg]
    have hg'_bits : basisBits (k + (m + 1)) g' = Function.update (basisBits (k + (m + 1)) g)
        (ghostWire k m) (basisBits (k + (m + 1)) g (ghostWire k m) + 1) := by
      dsimp only [g']
      rw [lemHex158 k m Valid g hcond, lemHex153]
    apply (basisBitsEquiv (k + (m + 1))).injective
    change basisBits (k + (m + 1)) (ghostGuardStep k m Valid g') = basisBits (k + (m + 1)) g
    rw [lemHex158 k m Valid g' hcond', lemHex153, hg'_bits]
    funext w
    by_cases hw : w = ghostWire k m
    · subst hw
      simp only [Function.update_self, add_assoc]
      have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      rw [h11, add_zero]
    · simp [Function.update_of_ne hw]
  · rw [lemHex159 k m Valid g hcond, lemHex159 k m Valid g hcond]
theorem ghostGuardStep_injective (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) :
    Function.Injective (ghostGuardStep k m Valid) :=
  Function.Involutive.injective (ghostGuardStep_involutive k m Valid)
noncomputable def ghostGuardMatrix (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) :
    Operator (2 ^ (k + (m + 1))) :=
  Matrix.of (fun i j ↦ if ghostGuardStep k m Valid j = i then (1 : ℂ) else 0)
private theorem involutive_permMatrix_props {N : ℕ} {f : Fin N → Fin N}
    (hf : Function.Involutive f) :
    let M : Operator N := Matrix.of (fun i j ↦ if f j = i then (1 : ℂ) else 0)
    Mᴴ = M ∧ M * M = 1 := by
  intro M
  constructor
  · ext i j
    simp only [M, Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : f j = i
    · subst h
      simp [hf j]
    · simp [h, show f i ≠ j from fun hij ↦ h (hij ▸ hf i)]
  · ext i j
    simp only [M, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (f j) (fun x _ hx ↦ by simp [Ne.symm hx])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, mul_one, hf j]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
theorem ghostGuardMatrix_conjTranspose (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) :
    (ghostGuardMatrix k m Valid)ᴴ = ghostGuardMatrix k m Valid :=
  (involutive_permMatrix_props (ghostGuardStep_involutive k m Valid)).1
theorem ghostGuardMatrix_mul_self (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) :
    ghostGuardMatrix k m Valid * ghostGuardMatrix k m Valid = 1 :=
  (involutive_permMatrix_props (ghostGuardStep_involutive k m Valid)).2
theorem ghostGuardMatrix_conj_apply (k m : ℕ) (Valid : Fin (2 ^ k) → Bool)
    (M : Operator (2 ^ (k + (m + 1)))) (i j : Fin (2 ^ (k + (m + 1)))) :
    (ghostGuardMatrix k m Valid * M * ghostGuardMatrix k m Valid) i j =
      M (ghostGuardStep k m Valid i) (ghostGuardStep k m Valid j) := by
  simp only [ghostGuardMatrix, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (ghostGuardStep k m Valid j) (fun _ _ hx ↦ by simp [Ne.symm hx])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp only [↓reduceIte, mul_one]
  rw [Finset.sum_eq_single (ghostGuardStep k m Valid i)
      (fun x _ hx ↦ by simp [show ghostGuardStep k m Valid x ≠ i from
        fun h ↦ hx (by rw [← h, ghostGuardStep_involutive])])
      (fun h ↦ absurd (Finset.mem_univ _) h),
    ghostGuardStep_involutive]
  simp
noncomputable def ghostGuardUnitary (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) :
    Unitary (2 ^ (k + (m + 1))) :=
  ⟨ghostGuardMatrix k m Valid, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, ghostGuardMatrix_conjTranspose]
    exact ghostGuardMatrix_mul_self k m Valid)⟩
private lemma lemHex15b {r N : ℕ} (reg : QRegister r N) (g : Fin (2 ^ N)) :
    reg.extractIndex g = 0 ↔ ∀ idx : Fin r, basisBits N g (reg idx) = 0 := by
  refine ⟨fun h idx ↦ ?_, fun h ↦ (basisBitsEquiv r).injective (funext fun idx ↦ ?_)⟩
  · simpa [-Nat.reducePow, QRegister.basisBits_extractIndex, lemHex152] using
      congrArg (fun x ↦ basisBits r x idx) h
  · change basisBits r (reg.extractIndex g) idx = basisBits r 0 idx
    simpa [-Nat.reducePow, QRegister.basisBits_extractIndex, lemHex152] using h idx
private lemma lemHex15c (k m : ℕ) (g : Fin (2 ^ (k + (m + 1)))) : (ghostReg k m).extractIndex g =
    0 ↔ basisBits (k + (m + 1)) g (ghostWire k m) = 0 :=
  (lemHex15b _ g).trans ⟨fun h ↦ h 0, fun hb idx ↦ Subsingleton.elim idx 0 ▸ hb⟩
private lemma lemHex15d (k m : ℕ) (g : Fin (2 ^ (k + (m + 1)))) :
    (ancGhostReg k m).extractIndex g = 0 ↔
      (ancReg k m).extractIndex g = 0 ∧ basisBits (k + (m + 1)) g (ghostWire k m) = 0 := by
  rw [lemHex15b, lemHex15b]
  refine ⟨fun h ↦ ⟨fun idx ↦ ?_, ?_⟩, fun ⟨hanc, hgh⟩ idx ↦ ?_⟩
  · rw [show (ancReg k m) idx = (ancGhostReg k m) ⟨idx.val, by omega⟩ by
      ext
      simp [ancReg, ancGhostReg, SingleRBEGridGuardWalkAlt.qreg_block_apply]]
    exact h _
  · rw [show ghostWire k m = (ancGhostReg k m) ⟨m, by omega⟩ by
      ext
      simp [ancGhostReg, SingleRBEGridGuardWalkAlt.qreg_block_apply]]
    exact h _
  · by_cases hlt : idx.val < m
    · rw [show (ancGhostReg k m) idx = (ancReg k m) ⟨idx.val, hlt⟩ by
        ext
        simp [ancReg, ancGhostReg, SingleRBEGridGuardWalkAlt.qreg_block_apply]]
      exact hanc _
    · rw [show (ancGhostReg k m) idx = ghostWire k m by
        ext
        simp [ancGhostReg, SingleRBEGridGuardWalkAlt.qreg_block_apply,
          show idx.val = m by omega]]
      exact hgh
private lemma lemHex15e (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) (g : Fin (2 ^ (k + (m + 1))))
    (hgh : basisBits (k + (m + 1)) g (ghostWire k m) = 0) : basisBits (k + (m + 1))
    (ghostGuardStep k m Valid g) (ghostWire k m) = if (ancReg k m).extractIndex g = 0 ∧ Valid
    ((sysReg k m).extractIndex g) = false then 1 else 0 := by
  by_cases hcond : (ancReg k m).extractIndex g = 0 ∧ Valid ((sysReg k m).extractIndex g) = false
  · rw [lemHex158 k m Valid g hcond, lemHex153, Function.update_self, hgh, zero_add]
    simp [hcond]
  · rw [lemHex159 k m Valid g hcond, hgh]
    simp [hcond]
theorem baseReg_disjoint_ghostReg (k m : ℕ) : (baseReg k m).DisjointWires (ghostReg k m) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  fin_cases j
  have hv : k + m = 0 + i.val := congrArg Fin.val hj
  omega
theorem baseReg_embedMatrix_apply (k m : ℕ) (M : Operator (2 ^ (k + m)))
    (i j : Fin (2 ^ (k + (m + 1)))) : ((baseReg k m).embedMatrix M) i j = if basisBits
    (k + (m + 1)) i (ghostWire k m) = basisBits (k + (m + 1)) j (ghostWire k m) then M
    ((baseReg k m).extractIndex i) ((baseReg k m).extractIndex j) else 0 := by
  have hiff : ((baseReg k m).basisSplitEquiv i).2 = ((baseReg k m).basisSplitEquiv j).2 ↔
      basisBits (k + (m + 1)) i (ghostWire k m) = basisBits (k + (m + 1)) j (ghostWire k m) := by
    rw [(baseReg k m).basisSplit_environment_eq_iff]
    refine ⟨fun hOut ↦ hOut (ghostWire k m) fun ⟨idx, hidx⟩ ↦ ?_, fun hbit w hw ↦ ?_⟩
    · have hv := congrArg Fin.val hidx
      dsimp [baseReg, SingleRBEGridGuardWalkAlt.qreg_block_apply, ghostWire] at hv
      omega
    · by_cases hlt : w.val < k + m
      · exact (hw ⟨⟨w.val, hlt⟩, by
          ext
          simp [baseReg, SingleRBEGridGuardWalkAlt.qreg_block_apply]⟩).elim
      · exact (show w = ghostWire k m by
          ext
          dsimp [ghostWire]
          omega) ▸ hbit
  by_cases h : basisBits (k + (m + 1)) i (ghostWire k m) =
      basisBits (k + (m + 1)) j (ghostWire k m)
  · simp [QRegister.embedMatrix_apply, hiff.mpr h, h]
  · simp [QRegister.embedMatrix_apply, show _ ≠ _ from fun hs ↦ h (hiff.mp hs), h]
private lemma lemHex15f (k m : ℕ) (g : Fin (2 ^ (k + (m + 1)))) :
    (QRegister.block 0 k (by omega : 0 + k ≤ k + m)).extractIndex
    ((baseReg k m).extractIndex g) = (sysReg k m).extractIndex g :=
  (basisBitsEquiv k).injective (funext fun idx ↦ by
    simp [-Nat.reducePow, basisBitsEquiv, QRegister.basisBits_extractIndex, baseReg, sysReg,
      SingleRBEGridGuardWalkAlt.qreg_block_apply])
private lemma lemHex160 (k m : ℕ) (g : Fin (2 ^ (k + (m + 1)))) :
    (QRegister.block k m (le_rfl : k + m ≤ k + m)).extractIndex ((baseReg k m).extractIndex g)
    = (ancReg k m).extractIndex g :=
  (basisBitsEquiv m).injective (funext fun idx ↦ by
    simp [-Nat.reducePow, basisBitsEquiv, QRegister.basisBits_extractIndex, baseReg, ancReg,
      SingleRBEGridGuardWalkAlt.qreg_block_apply])
private lemma lemHex161 {a b : ℕ}
    (M : Operator (2 ^ a)) (u v : Fin (2 ^ (a + b)))
    (hu : (QRegister.block a b le_rfl).extractIndex u = 0)
    (hv : (QRegister.block a b le_rfl).extractIndex v = 0) :
    let rA : QRegister a (a + b) := .block 0 a (by omega)
    (rA.embedMatrix M) u v = M (rA.extractIndex u) (rA.extractIndex v) := by
  intro rA
  have hOut : rA.AgreeOutside u v := fun w hw ↦ by
    by_cases hlt : w.val < a
    · exact (hw ⟨⟨w.val, hlt⟩, by
        ext
        simp [rA, SingleRBEGridGuardWalkAlt.qreg_block_apply]⟩).elim
    · rw [show w = (QRegister.block a b le_rfl) ⟨w.val - a, by omega⟩ by
        ext
        simp [SingleRBEGridGuardWalkAlt.qreg_block_apply]
        omega, (lemHex15b _ u).mp hu _, (lemHex15b _ v).mp hv _]
  simp [QRegister.embedMatrix_apply, (rA.basisSplit_environment_eq_iff u v).mpr hOut]
noncomputable def ghostMuxOp (k m : ℕ) (M₀ M₁ : Operator (2 ^ (k + m))) : Operator
    (2 ^ (k + (m + 1))) := (baseReg k m).embedMatrix M₀ * ghostZeroProj k m +
    (baseReg k m).embedMatrix M₁ * ghostOneProj k m
theorem ghostZero_add_ghostOne (k m : ℕ) : ghostZeroProj k m + ghostOneProj k m = 1 := by
  ext i j
  unfold ghostZeroProj ghostOneProj
  rw [Matrix.add_apply, QRegister.basisOutcomeProjector_eq_diagonal,
    QRegister.basisOutcomeProjector_eq_diagonal]
  by_cases hij : i = j
  · subst hij
    rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) ((ghostReg k m).extractIndex i) with
      hx | hx <;> simp [hx]
  · simp [hij]
theorem baseReg_embedMatrix_comm_ghostZeroProj (k m : ℕ) (M : Operator (2 ^ (k + m))) :
    (baseReg k m).embedMatrix M * ghostZeroProj k m = ghostZeroProj k m *
    (baseReg k m).embedMatrix M := embedMatrix_comm_basisOutcomeProjector_disjoint
    (baseReg k m) (ghostReg k m) (baseReg_disjoint_ghostReg k m) M 0
theorem baseReg_embedMatrix_comm_ghostOneProj (k m : ℕ) (M : Operator (2 ^ (k + m))) :
    (baseReg k m).embedMatrix M * ghostOneProj k m = ghostOneProj k m *
    (baseReg k m).embedMatrix M := embedMatrix_comm_basisOutcomeProjector_disjoint
    (baseReg k m) (ghostReg k m) (baseReg_disjoint_ghostReg k m) M 1
theorem ghostMuxOp_one (k m : ℕ) : ghostMuxOp k m 1 1 = 1 := by
  unfold ghostMuxOp
  rw [(baseReg k m).embedMatrix_one, one_mul, one_mul, ghostZero_add_ghostOne]
theorem ghostMuxOp_conjTranspose (k m : ℕ) (M₀ M₁ : Operator (2 ^ (k + m))) :
    (ghostMuxOp k m M₀ M₁)ᴴ = ghostMuxOp k m M₀ᴴ M₁ᴴ := by
  unfold ghostMuxOp
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
    show (ghostZeroProj k m)ᴴ = ghostZeroProj k m from
      QRegister.basisOutcomeProjector_conjTranspose (ghostReg k m) 0,
    show (ghostOneProj k m)ᴴ = ghostOneProj k m from
      QRegister.basisOutcomeProjector_conjTranspose (ghostReg k m) 1,
    ← (baseReg k m).embedMatrix_conjTranspose, ← (baseReg k m).embedMatrix_conjTranspose,
    ← baseReg_embedMatrix_comm_ghostZeroProj k m M₀ᴴ,
    ← baseReg_embedMatrix_comm_ghostOneProj k m M₁ᴴ]
private lemma lemHex165 {d : ℕ} (EA₀ EA₁ EB₀ EB₁ P₀ P₁ : Operator d) (hB0 : EB₀ * P₀ = P₀ * EB₀)
    (hB1 : EB₁ * P₁ = P₁ * EB₁) (hp00 : P₀ * P₀ = P₀) (hp11 : P₁ * P₁ = P₁)
    (hp01 : P₀ * P₁ = 0) (hp10 : P₁ * P₀ = 0) : (EA₀ * P₀ + EA₁ * P₁) * (EB₀ * P₀ + EB₁ * P₁)
    = (EA₀ * EB₀) * P₀ + (EA₁ * EB₁) * P₁ := by
  have hmul {A B P Q R : Operator d} (hcomm : B * Q = Q * B) (hpq : P * Q = R) :
      (A * P) * (B * Q) = A * (R * B) := by
    calc (A * P) * (B * Q)
        = A * ((P * Q) * B) := by
            rw [hcomm]
            simp only [Matrix.mul_assoc]
      _ = A * (R * B) := by rw [hpq]
  rw [add_mul, mul_add, mul_add, hmul hB0 hp00, ← hB0, ← Matrix.mul_assoc,
    hmul hB1 hp01, zero_mul, mul_zero, add_zero,
    hmul hB0 hp10, zero_mul, mul_zero, zero_add,
    hmul hB1 hp11, ← hB1, ← Matrix.mul_assoc]
theorem ghostMuxOp_mul (k m : ℕ) (A₀ A₁ B₀ B₁ : Operator (2 ^ (k + m))) :
    ghostMuxOp k m A₀ A₁ * ghostMuxOp k m B₀ B₁ = ghostMuxOp k m (A₀ * B₀) (A₁ * B₁) := by
  unfold ghostMuxOp
  rw [lemHex165 _ _ _ _ _ _ (baseReg_embedMatrix_comm_ghostZeroProj k m B₀)
      (baseReg_embedMatrix_comm_ghostOneProj k m B₁)
      (basisOutcomeProjector_idem (ghostReg k m) 0)
      (basisOutcomeProjector_idem (ghostReg k m) 1)
      (basisOutcomeProjector_mul_eq_zero_of_ne (ghostReg k m) (by decide))
      (basisOutcomeProjector_mul_eq_zero_of_ne (ghostReg k m) (by decide)),
    ← (baseReg k m).embedMatrix_mul, ← (baseReg k m).embedMatrix_mul]
theorem ghostMuxOp_mul_ghostZeroProj (k m : ℕ) (M₀ M₁ : Operator (2 ^ (k + m))) : ghostMuxOp k
    m M₀ M₁ * ghostZeroProj k m = (baseReg k m).embedMatrix M₀ * ghostZeroProj k m := by
  have h00 : ghostZeroProj k m * ghostZeroProj k m = ghostZeroProj k m :=
    basisOutcomeProjector_idem (ghostReg k m) 0
  have h10 : ghostOneProj k m * ghostZeroProj k m = 0 :=
    basisOutcomeProjector_mul_eq_zero_of_ne (ghostReg k m) (by decide)
  unfold ghostMuxOp
  rw [add_mul, Matrix.mul_assoc, h00, Matrix.mul_assoc, h10, mul_zero, add_zero]
noncomputable def ghostMuxUnitary (k m : ℕ) (U₀ U₁ : Unitary (2 ^ (k + m))) :
    Unitary (2 ^ (k + (m + 1))) :=
  ⟨ghostMuxOp k m U₀.1 U₁.1, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, ghostMuxOp_conjTranspose, ghostMuxOp_mul]
    have hu0 : U₀.1 * U₀.1ᴴ = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
        Unitary.coe_mul_star_self U₀
    have hu1 : U₁.1 * U₁.1ᴴ = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
        Unitary.coe_mul_star_self U₁
    rw [hu0, hu1, ghostMuxOp_one])⟩
theorem ghostMuxOp_apply (k m : ℕ) (M₀ M₁ : Operator (2 ^ (k + m)))
    (i j : Fin (2 ^ (k + (m + 1)))) : ghostMuxOp k m M₀ M₁ i j = if basisBits (k + (m + 1)) i
    (ghostWire k m) = basisBits (k + (m + 1)) j (ghostWire k m) then if basisBits
    (k + (m + 1)) j (ghostWire k m) = 0 then M₀ ((baseReg k m).extractIndex i)
    ((baseReg k m).extractIndex j) else M₁ ((baseReg k m).extractIndex i)
    ((baseReg k m).extractIndex j) else 0 := by
  unfold ghostMuxOp ghostZeroProj ghostOneProj
  rw [Matrix.add_apply, lemHex155, lemHex155, baseReg_embedMatrix_apply, baseReg_embedMatrix_apply]
  rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) ((ghostReg k m).extractIndex j) with h0 | h1
  · simp [h0, (lemHex15c k m j).mp h0]
  · simp [h1, show basisBits (k + (m + 1)) j (ghostWire k m) ≠ 0 from
      fun hb ↦ absurd (h1.symm.trans ((lemHex15c k m j).mpr hb)) (by decide)]
noncomputable def ancFlipStep (k m : ℕ) (hm : 0 < m)
    (u : Fin (2 ^ (k + m))) : Fin (2 ^ (k + m)) :=
  let w0 : Wire (k + m) := ⟨k, by omega⟩
  (basisBitsEquiv (k + m)).symm
    (Function.update (basisBits (k + m) u) w0 (basisBits (k + m) u w0 + 1))
theorem ancFlipStep_involutive (k m : ℕ) (hm : 0 < m) (u : Fin (2 ^ (k + m))) :
    ancFlipStep k m hm (ancFlipStep k m hm u) = u := by
  refine (basisBitsEquiv (k + m)).injective (funext fun w ↦ ?_)
  change basisBits (k + m) (ancFlipStep k m hm (ancFlipStep k m hm u)) w = basisBits (k + m) u w
  unfold ancFlipStep
  rw [lemHex153, lemHex153]
  by_cases hw : w = ⟨k, by omega⟩
  · subst hw
    simp [add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl]
  · rw [Function.update_of_ne hw, Function.update_of_ne hw]
noncomputable def ancFlipMatrix (k m : ℕ) (hm : 0 < m) : Operator (2 ^ (k + m)) :=
  Matrix.of (fun u v ↦ if ancFlipStep k m hm v = u then (1 : ℂ) else 0)
theorem ancFlipMatrix_conjTranspose (k m : ℕ) (hm : 0 < m) :
    (ancFlipMatrix k m hm)ᴴ = ancFlipMatrix k m hm :=
  (involutive_permMatrix_props (ancFlipStep_involutive k m hm)).1
theorem ancFlipMatrix_mul_self (k m : ℕ) (hm : 0 < m) :
    ancFlipMatrix k m hm * ancFlipMatrix k m hm = 1 :=
  (involutive_permMatrix_props (ancFlipStep_involutive k m hm)).2
theorem ancFlipMatrix_apply_of_anc_zero (k m : ℕ) (hm : 0 < m) (u v : Fin (2 ^ (k + m)))
    (hu : (QRegister.block k m le_rfl).extractIndex u = 0)
    (hv : (QRegister.block k m le_rfl).extractIndex v = 0) : ancFlipMatrix k m hm u v = 0 := by
  simp only [ancFlipMatrix, Matrix.of_apply]
  refine ite_eq_right_of_eq_false _ _ (eq_false fun heq ↦ ?_)
  have hb := congrArg (fun x ↦ basisBits (k + m) x ⟨k, by omega⟩) heq
  unfold ancFlipStep at hb
  rw [lemHex153, Function.update_self,
    show basisBits (k + m) v ⟨k, by omega⟩ = 0 by
      simpa [SingleRBEGridGuardWalkAlt.qreg_block_apply] using (lemHex15b _ v).mp hv ⟨0, hm⟩,
    show basisBits (k + m) u ⟨k, by omega⟩ = 0 by
      simpa [SingleRBEGridGuardWalkAlt.qreg_block_apply] using (lemHex15b _ u).mp hu ⟨0, hm⟩,
    zero_add] at hb
  exact absurd hb (by decide)
noncomputable def ancFlipUnitary (k m : ℕ) (hm : 0 < m) : Unitary (2 ^ (k + m)) :=
  ⟨ancFlipMatrix k m hm, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, ancFlipMatrix_conjTranspose]
    exact ancFlipMatrix_mul_self k m hm)⟩
noncomputable def ghostZeroedBE (k m : ℕ) (hm : 0 < m) (Valid : Fin (2 ^ k) → Bool)
    (U_raw : Unitary (2 ^ (k + m))) : Unitary (2 ^ (k + (m + 1))) := ghostGuardUnitary k m
    Valid * ghostMuxUnitary k m U_raw (ancFlipUnitary k m hm) * ghostGuardUnitary k m Valid
theorem ghostZeroedBE_conjTranspose {k m : ℕ} (hm : 0 < m) (Valid : Fin (2 ^ k) → Bool)
    {U_raw : Unitary (2 ^ (k + m))} (hU_sa : U_raw.1ᴴ = U_raw.1) :
    (ghostZeroedBE k m hm Valid U_raw).1ᴴ = (ghostZeroedBE k m hm Valid U_raw).1 := by
  change (ghostGuardMatrix k m Valid * ghostMuxOp k m U_raw.1 (ancFlipMatrix k m hm) *
    ghostGuardMatrix k m Valid)ᴴ = ghostGuardMatrix k m Valid * ghostMuxOp k m U_raw.1
    (ancFlipMatrix k m hm) * ghostGuardMatrix k m Valid
  rw [conjTranspose_mul, conjTranspose_mul, ghostGuardMatrix_conjTranspose,
    ghostMuxOp_conjTranspose, hU_sa, ancFlipMatrix_conjTranspose, Matrix.mul_assoc]
theorem ghostGuard_mul_inGrid_eq (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) : ghostGuardMatrix k m
    Valid * (ancGhostZeroProj k m * (sysReg k m).embedMatrix (diagProj k Valid)) =
    ancGhostZeroProj k m * (sysReg k m).embedMatrix (diagProj k Valid) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [ghostGuardMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (ghostGuardStep k m Valid i)
    (fun x _ hx ↦ by simp [show ghostGuardStep k m Valid x ≠ i from
      fun h ↦ hx (by rw [← h, ghostGuardStep_involutive])])
    (fun h ↦ absurd (Finset.mem_univ _) h)]
  rw [ghostGuardStep_involutive]
  simp only [↓reduceIte, one_mul]
  unfold ancGhostZeroProj
  rw [lemHex154, lemHex154]
  by_cases hcond : (ancReg k m).extractIndex i = 0 ∧ Valid ((sysReg k m).extractIndex i) = false
  · have hzero (x : Fin (2 ^ (k + (m + 1)))) (hV : Valid ((sysReg k m).extractIndex x) = false) :
        ((sysReg k m).embedMatrix (diagProj k Valid)) x j = 0 := by
      by_cases hA : ((sysReg k m).basisSplitEquiv x).2 = ((sysReg k m).basisSplitEquiv j).2
      · simp [QRegister.embedMatrix_apply, hA, diagProj, Matrix.diagonal_apply, hV]
      · simp [QRegister.embedMatrix_apply, hA]
    rw [hzero _ (ghostGuardStep_sysReg k m Valid i ▸ hcond.2), hzero i hcond.2]
    simp
  · rw [lemHex159 k m Valid i hcond]
theorem ghostGuard_conj_proj_mul_ghostZero (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) :
    let G := ghostGuardMatrix k m Valid
    (G * ancGhostZeroProj k m * G) * ghostZeroProj k m =
      (baseReg k m).embedMatrix (projGridAncZero k m (diagProj k Valid)) * ghostZeroProj k m := by
  intro G
  have hproj : (baseReg k m).embedMatrix (projGridAncZero k m (diagProj k Valid)) =
      Matrix.diagonal fun x ↦ (if Valid ((sysReg k m).extractIndex x) then (1 : ℂ) else 0) *
        (if (ancReg k m).extractIndex x = 0 then (1 : ℂ) else 0) := by
    unfold projGridAncZero diagProj
    dsimp only
    rw [PosMomSelectDynamic.embedMatrix_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal, PosMomSelectDynamic.embedMatrix_diagonal]
    simp_rw [lemHex15f, lemHex160]
  ext i j
  unfold ghostZeroProj ancGhostZeroProj
  rw [hproj, lemHex155, lemHex155, ghostGuardMatrix_conj_apply,
    QRegister.basisOutcomeProjector_eq_diagonal]
  by_cases hj : (ghostReg k m).extractIndex j = 0
  · by_cases hij : i = j
    · subst hij
      simp only [hj, ↓reduceIte, Matrix.diagonal_apply, lemHex15d, ghostGuardStep_ancReg,
        lemHex15e k m Valid i ((lemHex15c k m i).mp hj)]
      have h10 : ((1 : ZMod 2) = 0) ↔ False := by decide
      by_cases hanc : (ancReg k m).extractIndex i = 0 <;>
        cases Valid ((sysReg k m).extractIndex i) <;> simp [hanc, h10]
    · simp [hj, Matrix.diagonal_apply_ne _ hij,
        Matrix.diagonal_apply_ne _ fun hs ↦ hij (ghostGuardStep_injective k m Valid hs)]
  · simp [hj]
theorem ghostGuard_conj_refl_mul_ghostZero (k m : ℕ) (Valid : Fin (2 ^ k) → Bool) :
    let G := ghostGuardMatrix k m Valid
    (G * reflOfProj (ancGhostZeroProj k m) * G) * ghostZeroProj k m =
      (baseReg k m).embedMatrix (singleRBEReflMatrix k m (diagProj k Valid)) *
        ghostZeroProj k m := by
  intro G
  have hn1 : -(1 : Operator (2 ^ (k + (m + 1)))) = (-1 : ℂ) • 1 := (neg_one_smul ℂ _).symm
  have hn2 : -(1 : Operator (2 ^ (k + m))) = (-1 : ℂ) • 1 := (neg_one_smul ℂ _).symm
  unfold singleRBEReflMatrix reflOfProj
  rw [sub_eq_add_neg, sub_eq_add_neg, hn1, hn2, mul_add, add_mul, add_mul, mul_smul_comm,
    smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, Matrix.mul_one,
    ghostGuardMatrix_mul_self, one_mul, ghostGuard_conj_proj_mul_ghostZero,
    (baseReg k m).embedMatrix_add, (baseReg k m).embedMatrix_smul, (baseReg k m).embedMatrix_smul,
    (baseReg k m).embedMatrix_one, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
theorem ghostZeroedBE_topBlock_eq_proj_conj (k m : ℕ) (hm : 0 < m) (Valid : Fin (2 ^ k) → Bool)
    (U_raw : Unitary (2 ^ (k + m))) (A_raw : Operator (2 ^ k))
    (hBE :
      let sys0 : QRegister k (k + m) := .block 0 k (by omega)
      let anc0 : QRegister m (k + m) := .block k m le_rfl
      anc0.basisOutcomeProjector 0 * U_raw.1 * anc0.basisOutcomeProjector 0 =
        anc0.basisOutcomeProjector 0 * sys0.embedMatrix A_raw * anc0.basisOutcomeProjector 0) :
    ancGhostZeroProj k m * (ghostZeroedBE k m hm Valid U_raw).1 * ancGhostZeroProj k m =
      ancGhostZeroProj k m *
        (sysReg k m).embedMatrix (diagProj k Valid * A_raw * diagProj k Valid) *
        ancGhostZeroProj k m := by
  change ancGhostZeroProj k m *
      (ghostGuardMatrix k m Valid * ghostMuxOp k m U_raw.1 (ancFlipMatrix k m hm) *
        ghostGuardMatrix k m Valid) * ancGhostZeroProj k m = _
  ext i j
  unfold ancGhostZeroProj
  rw [lemHex155, lemHex154, lemHex155, lemHex154]
  by_cases hi : (ancGhostReg k m).extractIndex i = 0
  · by_cases hj : (ancGhostReg k m).extractIndex j = 0
    · simp only [hi, hj, ↓reduceIte]
      rcases (lemHex15d k m i).mp hi with ⟨hanc_i, hgh_i⟩
      rcases (lemHex15d k m j).mp hj with ⟨hanc_j, hgh_j⟩
      rw [ghostGuardMatrix_conj_apply, ghostMuxOp_apply, ghostGuardStep_baseReg,
        ghostGuardStep_baseReg, lemHex15e k m Valid i hgh_i, lemHex15e k m Valid j hgh_j,
        lemHex161 (diagProj k Valid * A_raw * diagProj k Valid) i j hi hj, diagProj_conj_apply]
      have hu0 : (QRegister.block k m le_rfl).extractIndex ((baseReg k m).extractIndex i) = 0 := by
        simpa [lemHex160] using hanc_i
      have hv0 : (QRegister.block k m le_rfl).extractIndex ((baseReg k m).extractIndex j) = 0 := by
        simpa [lemHex160] using hanc_j
      have hentry := congrFun (congrFun hBE ((baseReg k m).extractIndex i))
        ((baseReg k m).extractIndex j)
      rw [lemHex155, lemHex154, lemHex155, lemHex154] at hentry
      simp only [hu0, hv0, ↓reduceIte, lemHex161 A_raw _ _ hu0 hv0, lemHex15f] at hentry
      rw [hentry, ancFlipMatrix_apply_of_anc_zero k m hm _ _ hu0 hv0]
      have h01 : ((0 : ZMod 2) = 1) ↔ False := by decide
      have h10 : ((1 : ZMod 2) = 0) ↔ False := by decide
      cases Valid ((sysReg k m).extractIndex i) <;>
        cases Valid ((sysReg k m).extractIndex j) <;> simp [hanc_i, hanc_j, h01, h10]
    · simp [hj]
  · simp [hi]
end SingleRBEGridGuardWalk
end
end ModSingleRBEGridGuardWalk

section ModSixChannelHamiltonianSplit
@[expose] public section
namespace SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open Operator Matrix SpecsAux SpecsAux.SpecMirror
open scoped Matrix BigOperators Matrix.Norms.L2Operator Real
theorem norm_projector_le_one {d : Type*} [Fintype d] [DecidableEq d] (P : Matrix d d ℂ)
    (hHerm : P.IsHermitian) (hIdem : P * P = P) : ‖P‖ ≤ 1 := by
  have hsq : ‖P‖ = ‖P‖ * ‖P‖ := by
    calc ‖P‖
      _ = ‖Pᴴ * P‖ := by rw [hHerm.eq, hIdem]
      _ = ‖P‖ * ‖P‖ := Matrix.l2_opNorm_conjTranspose_mul_self P
  nlinarith [norm_nonneg P]
open Classical in
noncomputable def gridProjector : Operator (2 ^ systemQubits) :=
  Matrix.diagonal fun x ↦ if IsGridState x then 1 else 0
theorem componentBits_pos (a : Particle) : 0 < componentBits a :=
  SpecsAux.BridgeFermionicComm.SpecInner.componentBits_pos a
theorem exists_particle_field_of_lt (k : ℕ) (hk : k < systemQubits) : ∃ (a : Particle)
    (w : Fin 3) (b : ℕ), b < componentBits a ∧ k = bitOffset a w + b :=
  SpecsAux.BridgeFermionicComm.SpecInner.exists_particle_field_of_lt k hk
theorem testBit_div_two_pow_mod_two_pow (n offset width b : ℕ) (hb : b < width) :
    ((n / 2 ^ offset) % 2 ^ width).testBit b = n.testBit (offset + b) :=
  SpecsAux.BridgeFermionicComm.SpecInner.testBit_div_two_pow_mod_two_pow
    n offset width b hb
theorem signMagnitude_fst_eq_testBit (x : Fin (2 ^ systemQubits)) (a : Particle) (w : Fin 3) :
    (signMagnitude x a w).1 =
      if x.val.testBit (bitOffset a w + (componentBits a - 1)) then 1 else 0 :=
  SpecsAux.BridgeFermionicComm.SpecInner.signMagnitude_fst_eq_testBit x a w
theorem testBit_eq_of_signMagnitude_eq (x y : Fin (2 ^ systemQubits))
    (a : Particle) (w : Fin 3) (h : signMagnitude x a w = signMagnitude y a w)
    (b : ℕ) (hb : b < componentBits a) :
    x.val.testBit (bitOffset a w + b) = y.val.testBit (bitOffset a w + b) :=
  SpecsAux.BridgeFermionicComm.SpecInner.testBit_eq_of_signMagnitude_eq
    x y a w h b hb
theorem signMagnitude_eq_of_momentum_eq_of_isGridState {x y : Fin (2 ^ systemQubits)}
    (hx : IsGridState x) (hy : IsGridState y) (a : Particle) (w : Fin 3)
    (hm : momentum x a w = momentum y a w) : signMagnitude x a w = signMagnitude y a w :=
  SpecsAux.BridgeFermionicComm.SpecInner.signMagnitude_eq_of_momentum_eq_of_isGridState
    hx hy a w hm
theorem momentum_eq_iff_eq_of_isGridState {x y : Fin (2 ^ systemQubits)} (hx : IsGridState x)
    (hy : IsGridState y) : (∀ a, momentum x a = momentum y a) ↔ x = y :=
  ⟨fun h ↦ SpecsAux.BridgeFermionicComm.SpecInner.eq_of_momentum_eq_of_isGridState
    hx hy (fun a w ↦ congrFun (h a) w), fun h ↦ h ▸ fun _ ↦ rfl⟩
def fin3TupleEquiv (α : Type*) : (α × α × α) ≃ (Fin 3 → α) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun f := (f 0, f 1, f 2)
  left_inv p := by rcases p with ⟨_, _, _⟩; rfl
  right_inv f := by ext i; fin_cases i <;> rfl
def openBox3D62 : Finset (Fin 3 → ℤ) := (Finset.Icc (-62) 62 ×ˢ (Finset.Icc (-62) 62 ×ˢ
    Finset.Icc (-62) 62)).map (fin3TupleEquiv ℤ).toEmbedding
theorem mem_openBox3D62_iff (ν : Fin 3 → ℤ) :
    ν ∈ openBox3D62 ↔ ∀ w, -62 ≤ ν w ∧ ν w ≤ 62 := by
  simp only [openBox3D62, Finset.mem_map_equiv, Finset.mem_product, Finset.mem_Icc,
    fin3TupleEquiv, Equiv.coe_fn_symm_mk]
  exact ⟨fun ⟨h0, h1, h2⟩ w ↦ by fin_cases w <;> assumption, fun h ↦ ⟨h 0, h 1, h 2⟩⟩
attribute [irreducible] openBox3D62
theorem sub_mem_openBox3D62_of_mem_Icc {p q : Fin 3 → ℤ} (hp : ∀ w, -31 ≤ p w ∧ p w ≤ 31)
    (hq : ∀ w, -31 ≤ q w ∧ q w ≤ 31) : p - q ∈ openBox3D62 :=
  (mem_openBox3D62_iff _).mpr fun w ↦ by
    have := hp w
    have := hq w
    change -62 ≤ p w - q w ∧ p w - q w ≤ 62
    omega
theorem electron_momentum_mem_Icc (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons) (w : Fin 3) :
    -31 ≤ momentum x (.electron i) w ∧ momentum x (.electron i) w ≤ 31 := by
  dsimp [momentum, signMagnitude, componentBits, electronBits]
  set s := x.val / 2 ^ bitOffset (.electron i) w / 32 % 2
  set m := x.val / 2 ^ bitOffset (.electron i) w % 32
  have hs : s = 0 ∨ s = 1 := by omega
  have hm : m ≤ 31 := by omega
  rcases hs with h | h <;> rw [h] <;> simp <;> omega
theorem coulombKernel_neg (ν : Fin 3 → ℤ) : coulombKernel (-ν) = coulombKernel ν :=
  BridgeFermionicComm.SpecInner.coulombKernel_neg ν
theorem coulombKernel_nonneg (ν : Fin 3 → ℤ) : 0 ≤ coulombKernel ν := by
  unfold coulombKernel waveNumberSq dotProduct
  apply div_nonneg
  · positivity
  · apply mul_nonneg (by norm_num [cellVolume])
    exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
def particleEquiv : Fin numElectrons ⊕ Unit ≃ Particle where
  toFun
    | .inl i => .electron i
    | .inr () => .projectile
  invFun
    | .electron i => .inl i
    | .projectile => .inr ()
  left_inv
    | .inl _ => rfl
    | .inr () => rfl
  right_inv
    | .electron _ => rfl
    | .projectile => rfl
theorem sum_particle {M : Type*} [AddCommMonoid M] (f : Particle → M) :
    (∑ a : Particle, f a) = (∑ i : Fin numElectrons, f (.electron i)) + f .projectile := by
  rw [← Equiv.sum_comp particleEquiv f, Fintype.sum_sum_type]
  simp [particleEquiv]
open Classical in
noncomputable def elecKinOp : Operator (2 ^ systemQubits) := Matrix.of fun x y ↦ if
    IsGridState x ∧ IsGridState y then if x = y then ((∑ i : Fin numElectrons, waveNumberSq
    (momentum x (.electron i)) / 2 : ℝ) : ℂ) else 0 else 0
open Classical in
noncomputable def projKinOp (c : Configuration) : Operator (2 ^ systemQubits) := Matrix.of fun
    x y ↦ if IsGridState x ∧ IsGridState y then if x = y then ((waveNumberSq (momentum x
    .projectile - c.projectileMomentum) / (2 * projectileMass) : ℝ) : ℂ) else 0 else 0
open Classical in
noncomputable def elecNucOp (c : Configuration) : Operator (2 ^ systemQubits) := ∑ i : Fin
    numElectrons, Matrix.of fun x y ↦ if IsGridState x ∧ IsGridState y ∧
    (∀ a ≠ .electron i, momentum x a = momentum y a) then (charge (.electron i) : ℂ) *
    structureFactor c (momentum x (.electron i) - momentum y (.electron i)) * (coulombKernel
    (momentum x (.electron i) - momentum y (.electron i)) : ℂ) else 0
open Classical in
noncomputable def projNucOp (c : Configuration) : Operator (2 ^ systemQubits) := Matrix.of fun
    x y ↦ if IsGridState x ∧ IsGridState y ∧
    (∀ b ≠ Particle.projectile, momentum x b = momentum y b) then
    (charge Particle.projectile : ℂ) * structureFactor c
    (momentum x .projectile - momentum y .projectile) * (coulombKernel (momentum x .projectile
    - momentum y .projectile) : ℂ) else 0
open Classical in
noncomputable def elecElecOp : Operator (2 ^ systemQubits) := ∑ i : Fin numElectrons, ∑ j :
    Fin numElectrons, Matrix.of fun x y ↦ if IsGridState x ∧ IsGridState y ∧ i ≠ j ∧ (∀ d, d ≠
    .electron i → d ≠ .electron j → momentum x d = momentum y d) ∧ momentum x (.electron i) +
    momentum x (.electron j) = momentum y (.electron i) + momentum y (.electron j) then
    ((coulombKernel (momentum x (.electron i) - momentum y (.electron i)) / 2 : ℝ) : ℂ) else 0
open Classical in
noncomputable def elecProjOp : Operator (2 ^ systemQubits) := ∑ i : Fin numElectrons,
    Matrix.of fun x y ↦ if IsGridState x ∧ IsGridState y ∧ (∀ d, d ≠ .electron i → d ≠
    .projectile → momentum x d = momentum y d) ∧ momentum x (.electron i) + momentum x
    .projectile = momentum y (.electron i) + momentum y .projectile then ((-2 * coulombKernel
    (momentum x (.electron i) - momentum y (.electron i)) : ℝ) : ℂ) else 0
noncomputable def sixChannelRaw (c : Configuration) : Fin 6 → Operator (2 ^ systemQubits) :=
  ![elecKinOp, projKinOp c, elecNucOp c, projNucOp c, elecElecOp, elecProjOp]
theorem proj_elec_pair_cond_iff (p q : Particle → Fin 3 → ℤ) (i : Fin numElectrons) :
    (Particle.projectile ≠ .electron i ∧ (∀ d, d ≠ .projectile → d ≠ .electron i → p d = q d)
    ∧ p .projectile + p (.electron i) = q .projectile + q (.electron i)) ↔ ((∀ d, d ≠
    .electron i → d ≠ .projectile → p d = q d) ∧ p (.electron i) + p .projectile = q
    (.electron i) + q .projectile) :=
  ⟨fun ⟨_, hd, hs⟩ ↦ ⟨fun d h1 h2 ↦ hd d h2 h1, by
      rw [add_comm (p _), add_comm (q _)]
      exact hs⟩,
    fun ⟨hd, hs⟩ ↦ ⟨by simp, fun d h1 h2 ↦ hd d h2 h1, by
      rw [add_comm (p _), add_comm (q _)]
      exact hs⟩⟩
theorem coulombKernel_proj_eq_of_momentum_conservation {p q : Particle → Fin 3 → ℤ}
    {i : Fin numElectrons}
    (hsum : p (.electron i) + p .projectile = q (.electron i) + q .projectile) :
    coulombKernel (p .projectile - q .projectile) =
      coulombKernel (p (.electron i) - q (.electron i)) := by
  rw [show p .projectile - q .projectile = -(p (.electron i) - q (.electron i)) from
    funext fun w ↦ by
      have hw := congrFun hsum w
      dsimp at hw ⊢
      linarith,
    coulombKernel_neg]
theorem sum_twoBody_real (p q : Particle → Fin 3 → ℤ) : (∑ a : Particle, ∑ b : Particle, if a
    ≠ b ∧ (∀ d, d ≠ a → d ≠ b → p d = q d) ∧ p a + p b = q a + q b then (charge a : ℝ) *
    (charge b : ℝ) * coulombKernel (p a - q a) / 2 else 0) = (∑ i : Fin numElectrons, ∑ j :
    Fin numElectrons, if i ≠ j ∧ (∀ d, d ≠ .electron i → d ≠ .electron j → p d = q d) ∧ p
    (.electron i) + p (.electron j) = q (.electron i) + q (.electron j) then coulombKernel (p
    (.electron i) - q (.electron i)) / 2 else 0) + (∑ i : Fin numElectrons, if (∀ d, d ≠
    .electron i → d ≠ .projectile → p d = q d) ∧ p (.electron i) + p .projectile = q
    (.electron i) + q .projectile then -2 * coulombKernel (p (.electron i) - q (.electron i))
    else 0) := by
  rw [sum_particle]
  simp only [sum_particle, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
    add_zero, Finset.sum_add_distrib, add_assoc]
  rw [← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Particle.electron.injEq, charge]
    split_ifs
    · push_cast
      ring
    · rfl
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hcond : (∀ d, d ≠ .electron i → d ≠ .projectile → p d = q d) ∧
        p (.electron i) + p .projectile = q (.electron i) + q .projectile
    · have hc1 : ¬Particle.electron i = .projectile ∧ _ := ⟨by simp, hcond⟩
      have hc2 := (proj_elec_pair_cond_iff p q i).mpr hcond
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc1), ite_eq_left_of_eq_true _ _ (eq_true hc2),
        ite_eq_left_of_eq_true _ _ (eq_true hcond),
        coulombKernel_proj_eq_of_momentum_conservation hcond.2]
      simp only [charge]
      push_cast
      ring
    · have hc1 : ¬(¬Particle.electron i = .projectile ∧ _) := fun h ↦ hcond h.2
      have hc2 : ¬(¬Particle.projectile = .electron i ∧ _) :=
        fun h ↦ hcond ((proj_elec_pair_cond_iff p q i).mp h)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_right_of_eq_false _ _ (eq_false hc2),
        ite_eq_right_of_eq_false _ _ (eq_false hcond), add_zero]
theorem ofReal_sum_ite {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P] (g : ι → ℝ) :
    ((∑ i ∈ s, (if P i then g i else 0) : ℝ) : ℂ) =
      ∑ i ∈ s, (if P i then (g i : ℂ) else 0) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : P i <;> simp [h]
theorem sum_sixChannelRaw_eq_hamiltonian (c : Configuration) :
    (∑ k : Fin 6, sixChannelRaw c k) = hamiltonian c := by
  ext x y
  simp only [sixChannelRaw, Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.sum_apply, elecKinOp, projKinOp, elecNucOp,
    projNucOp, elecElecOp, elecProjOp, hamiltonian, Matrix.of_apply]
  by_cases hxy : IsGridState x ∧ IsGridState y
  · simp only [hxy.1, hxy.2, true_and, ↓reduceIte]
    have hKin : (if x = y then ((∑ i : Fin numElectrons, waveNumberSq (momentum x (.electron
        i)) / 2 : ℝ) : ℂ) else 0) + (if x = y then ((waveNumberSq (momentum x .projectile -
        c.projectileMomentum) / (2 * projectileMass) : ℝ) : ℂ) else 0) =
        (if x = y then (kineticEnergy c (momentum x) : ℂ) else 0) := by
      by_cases heq : x = y <;> simp [heq, kineticEnergy]
    have hNuc := (sum_particle fun a ↦ if ∀ b ≠ a, momentum x b = momentum y b then
      (charge a : ℂ) * structureFactor c (momentum x a - momentum y a) *
      (coulombKernel (momentum x a - momentum y a) : ℂ) else 0).symm
    have hTwoBody : (∑ i : Fin numElectrons, ∑ j : Fin numElectrons, if i ≠ j ∧ (∀ d, d ≠
        .electron i → d ≠ .electron j → momentum x d = momentum y d) ∧ momentum x (.electron
        i) + momentum x (.electron j) = momentum y (.electron i) + momentum y (.electron j)
        then ((coulombKernel (momentum x (.electron i) - momentum y (.electron i)) / 2 : ℝ) :
        ℂ) else 0) + (∑ i : Fin numElectrons, if (∀ d, d ≠ .electron i → d ≠ .projectile →
        momentum x d = momentum y d) ∧ momentum x (.electron i) + momentum x .projectile =
        momentum y (.electron i) + momentum y .projectile then ((-2 * coulombKernel (momentum
        x (.electron i) - momentum y (.electron i)) : ℝ) : ℂ) else 0) = ((∑ a : Particle, ∑ b
        : Particle, if a ≠ b ∧ (∀ d, d ≠ a → d ≠ b → momentum x d = momentum y d) ∧ momentum x
        a + momentum x b = momentum y a + momentum y b then (charge a : ℝ) * (charge b : ℝ) *
        coulombKernel (momentum x a - momentum y a) / 2 else 0 : ℝ) : ℂ) := by
      rw [sum_twoBody_real (momentum x) (momentum y), Complex.ofReal_add, Complex.ofReal_sum,
        ofReal_sum_ite]
      exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ (ofReal_sum_ite _ _ _).symm) rfl
    linear_combination hKin + hNuc + hTwoBody
  · simp [hxy, fun P : Prop ↦ show ¬(IsGridState x ∧ IsGridState y ∧ P) from
      fun h ↦ hxy ⟨h.1, h.2.1⟩]
open Classical in
noncomputable def elecProjMomTransferOp (i : Fin numElectrons) (ν : Fin 3 → ℤ) : Operator
    (2 ^ systemQubits) := Matrix.of fun x y ↦ if IsGridState x ∧ IsGridState y ∧ (∀ d, d ≠
    .electron i → d ≠ .projectile → momentum x d = momentum y d) ∧ momentum x (.electron i) -
    momentum y (.electron i) = ν ∧ momentum x .projectile = momentum y .projectile - ν then 1
    else 0
theorem elecProjOp_eq_sum_openBox3D62 : elecProjOp = ∑ i : Fin numElectrons, ∑ ν ∈
    openBox3D62, ((-2 * coulombKernel ν : ℝ) : ℂ) • elecProjMomTransferOp i ν := by
  ext x y
  simp only [elecProjOp, elecProjMomTransferOp, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hcond : IsGridState x ∧ IsGridState y ∧
      (∀ d, d ≠ .electron i → d ≠ .projectile → momentum x d = momentum y d) ∧
      momentum x (.electron i) + momentum x .projectile =
        momentum y (.electron i) + momentum y .projectile
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hcond)]
    symm
    rw [Finset.sum_eq_single (momentum x (.electron i) - momentum y (.electron i))
      (fun ν _ hne ↦ ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hne h.2.2.2.1.symm))
      (fun hnot ↦ (hnot (sub_mem_openBox3D62_of_mem_Icc (electron_momentum_mem_Icc x i)
        (electron_momentum_mem_Icc y i))).elim)]
    refine ite_eq_left_of_eq_true _ _ (eq_true ⟨hcond.1, hcond.2.1, hcond.2.2.1, rfl, ?_⟩)
    ext w
    have hw := congrFun hcond.2.2.2 w
    dsimp at hw ⊢
    linarith
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)]
    symm
    refine Finset.sum_eq_zero fun ν _ ↦ ite_eq_right_of_eq_false _ _ (eq_false fun h ↦
      hcond ⟨h.1, h.2.1, h.2.2.1, ?_⟩)
    ext w
    have h1 := congrFun h.2.2.2.1 w
    have h2 := congrFun h.2.2.2.2 w
    dsimp at h1 h2 ⊢
    linarith
theorem sum_abs_elecProjOp_lcu_weights :
    (∑ _i : Fin numElectrons, ∑ ν ∈ openBox3D62, |-2 * coulombKernel ν|) =
      436 * ∑ ν ∈ openBox3D62, coulombKernel ν := by
  have hterm (ν : Fin 3 → ℤ) : |-2 * coulombKernel ν| = 2 * coulombKernel ν := by
    rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg,
      abs_of_nonneg (coulombKernel_nonneg ν)]
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num [numElectrons]
  ring
private theorem norm_le_weightedPartialPerm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hRow : ∀ x y₁ y₂, M x y₁ ≠ 0 → M x y₂ ≠ 0 → y₁ = y₂)
    (hCol : ∀ x₁ x₂ y, M x₁ y ≠ 0 → M x₂ y ≠ 0 → x₁ = x₂) (hBound : ∀ x y, ‖M x y‖ ≤ B) :
    ‖M‖ ≤ B := by
  let d : n → ℂ := fun y ↦ ∑ z : n, (Mᴴ y z) * M z y
  have hmul : Mᴴ * M = Matrix.diagonal d := by
    ext y₁ y₂
    by_cases hy : y₁ = y₂
    · subst hy
      simp [d, Matrix.mul_apply]
    · rw [Matrix.mul_apply, Matrix.diagonal_apply_ne _ hy]
      refine Finset.sum_eq_zero fun z _ ↦ ?_
      by_cases h1 : M z y₁ = 0
      · simp [Matrix.conjTranspose_apply, h1]
      · simp [Matrix.conjTranspose_apply,
          show M z y₂ = 0 from Classical.byContradiction fun h2 ↦ hy (hRow z y₁ y₂ h1 h2)]
  have hd_norm (y : n) : ‖d y‖ ≤ B ^ 2 := by
    by_cases hex : ∃ x₀, M x₀ y ≠ 0
    · rcases hex with ⟨x₀, hx₀⟩
      rw [show d y = (Mᴴ y x₀) * M x₀ y from Finset.sum_eq_single x₀
          (fun z _ hz ↦ by
            simp [show M z y = 0 from
              Classical.byContradiction fun hz' ↦ hz (hCol z x₀ y hz' hx₀)])
          (fun h ↦ (h (Finset.mem_univ x₀)).elim),
        norm_mul, Matrix.conjTranspose_apply, norm_star, sq]
      exact mul_le_mul (hBound x₀ y) (hBound x₀ y) (norm_nonneg _) hB
    · push Not at hex
      rw [show d y = 0 from Finset.sum_eq_zero fun z _ ↦ by simp [hex z], norm_zero]
      positivity
  refine (mul_self_le_mul_self_iff (norm_nonneg M) hB).mpr ?_
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self M, hmul, Matrix.l2_opNorm_diagonal]
  linarith [(pi_norm_le_iff_of_nonneg (sq_nonneg B)).mpr hd_norm]
open Classical in
theorem norm_le_one_of_partialPerm {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (P : n → n → Prop) (hM : ∀ x y, M x y = if P x y then (1 : ℂ) else 0)
    (hCol : ∀ x₁ x₂ y, P x₁ y → P x₂ y → x₁ = x₂)
    (hRow : ∀ x y₁ y₂, P x y₁ → P x y₂ → y₁ = y₂) : ‖M‖ ≤ 1 := by
  have hP {x y : n} (h : M x y ≠ 0) : P x y :=
    Classical.byContradiction fun hn ↦ h (by simp [hM, hn])
  refine norm_le_weightedPartialPerm M zero_le_one
    (fun x y₁ y₂ h1 h2 ↦ hRow x y₁ y₂ (hP h1) (hP h2))
    (fun x₁ x₂ y h1 h2 ↦ hCol x₁ x₂ y (hP h1) (hP h2)) fun x y ↦ ?_
  rw [hM]
  split_ifs <;> simp
theorem norm_elecProjMomTransferOp_le_one (i : Fin numElectrons) (ν : Fin 3 → ℤ) :
    ‖elecProjMomTransferOp i ν‖ ≤ 1 := by
  refine norm_le_one_of_partialPerm (elecProjMomTransferOp i ν) (fun x y ↦ IsGridState x ∧
    IsGridState y ∧ (∀ d, d ≠ .electron i → d ≠ .projectile → momentum x d = momentum y d) ∧
    momentum x (.electron i) - momentum y (.electron i) = ν ∧ momentum x .projectile =
    momentum y .projectile - ν) (fun x y ↦ ?_) (fun x₁ x₂ y h₁ h₂ ↦ ?_) (fun x y₁ y₂ h₁ h₂ ↦ ?_)
  · simp only [elecProjMomTransferOp, Matrix.of_apply]
    congr 1
  · refine (momentum_eq_iff_eq_of_isGridState h₁.1 h₂.1).mp fun a ↦ ?_
    rcases a with j | _
    · by_cases hij : j = i
      · subst hij
        ext w
        have hw1 := congrFun h₁.2.2.2.1 w
        have hw2 := congrFun h₂.2.2.2.1 w
        dsimp at hw1 hw2
        linarith
      · exact (h₁.2.2.1 _ (by simp [hij]) (by simp)).trans
          (h₂.2.2.1 _ (by simp [hij]) (by simp)).symm
    · exact h₁.2.2.2.2.trans h₂.2.2.2.2.symm
  · refine (momentum_eq_iff_eq_of_isGridState h₁.2.1 h₂.2.1).mp fun a ↦ ?_
    rcases a with j | _
    · by_cases hij : j = i
      · subst hij
        ext w
        have hw1 := congrFun h₁.2.2.2.1 w
        have hw2 := congrFun h₂.2.2.2.1 w
        dsimp at hw1 hw2
        linarith
      · exact (h₁.2.2.1 _ (by simp [hij]) (by simp)).symm.trans
          (h₂.2.2.1 _ (by simp [hij]) (by simp))
    · ext w
      have hw1 := congrFun h₁.2.2.2.2 w
      have hw2 := congrFun h₂.2.2.2.2 w
      dsimp at hw1 hw2
      linarith
theorem norm_elecProjOp_le : ‖elecProjOp‖ ≤ 436 * ∑ ν ∈ openBox3D62, coulombKernel ν := by
  rw [elecProjOp_eq_sum_openBox3D62, ← sum_abs_elecProjOp_lcu_weights]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ ↦ ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ν _ ↦ ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_elecProjMomTransferOp_le_one i ν)
noncomputable def sixChannelShifted (c : Configuration) (E : Fin 6 → ℝ) : Fin 6 → Operator
    (2 ^ systemQubits) := fun k ↦ sixChannelRaw c k - (E k : ℂ) • gridProjector
theorem sum_sixChannelShifted_eq_hamiltonian_sub_gridProjector (c : Configuration)
    (E : Fin 6 → ℝ) : (∑ k : Fin 6, sixChannelShifted c E k) = hamiltonian c -
    ((∑ k : Fin 6, E k : ℝ) : ℂ) • gridProjector := by
  simp only [sixChannelShifted, Finset.sum_sub_distrib, sum_sixChannelRaw_eq_hamiltonian,
    ← Finset.sum_smul, Complex.ofReal_sum]
theorem norm_structureFactor_le (c : Configuration) (ν : Fin 3 → ℤ) :
    ‖structureFactor c ν‖ ≤ 216 := by
  unfold structureFactor
  refine (norm_sum_le _ _).trans_eq
    ((Finset.sum_congr rfl (g := fun _ ↦ (1 : ℝ)) fun l _ ↦ ?_).trans (by simp))
  simpa only [Complex.ofReal_neg] using
    Complex.norm_exp_ofReal_mul_I (-(waveVector ν ⬝ᵥ c.nuclei l))
end SpecsAux.SpecMirror.SixChannelHamiltonianSplit
end
end ModSixChannelHamiltonianSplit

section ModModWrapCoarse8PureMomentum
@[expose] public section
namespace ModWrapCoarse8PureMomentum
open Operator Matrix SpecsAux SpecsAux.SpecMirror
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open scoped Matrix BigOperators Matrix.Norms.L2Operator Real
instance modWrapNeZeroPow2 {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k (by decide)⟩
theorem ite_false_eq {α : Type*} {P : Prop} [Decidable P] (hP : ¬ P) (a b : α) :
    (if P then a else b) = b := ite_eq_right_iff.mpr fun h ↦ (hP h).elim
theorem ite_true_eq {α : Type*} {P : Prop} [inst : Decidable P] (hP : P) (a b : α) :
    (if P then a else b) = a :=
  match inst with
  | isTrue _ => rfl
  | isFalse h => (h hP).elim
theorem hasDerivAt_fn_add {f g : ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) : HasDerivAt (fun y ↦ f y + g y) (f' + g') x := by
  simpa only [Pi.add_def] using hf.add hg
theorem hasDerivAt_fn_sub {f g : ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) : HasDerivAt (fun y ↦ f y - g y) (f' - g') x := by
  simpa only [Pi.sub_def] using hf.sub hg
theorem nonneg_of_deriv_nonneg (f : ℝ → ℝ) {f' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf0 : f 0 = 0)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 ≤ x → x ≤ t → 0 ≤ f' x) :
    0 ≤ f t := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · exact hf0.symm.le
  · have hcont : ContinuousOn f (Set.Icc 0 t) :=
      fun x _ ↦ (hderiv x).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 t) :=
      fun x _ ↦ (hderiv x).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope f ht_pos hcont hdiff with ⟨c, ⟨hc0, hct⟩, hslope⟩
    rw [hf0, sub_zero, sub_zero, (hderiv c).deriv, eq_div_iff ht_pos.ne'] at hslope
    have hc_nn : 0 ≤ f' c := hpos c hc0.le hct.le
    nlinarith
noncomputable def cosLowerPoly10 (t : ℝ) : ℝ :=
  1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800
noncomputable def cosUpperPoly12 (t : ℝ) : ℝ := cosLowerPoly10 t + t ^ 12 / 479001600
theorem cosLowerPoly10_le_cos_and_cos_le_cosUpperPoly12 {t : ℝ} (ht : 0 ≤ t) :
    cosLowerPoly10 t ≤ Real.cos t ∧ Real.cos t ≤ cosUpperPoly12 t := by
  let P2 : ℝ → ℝ := fun y ↦ 1 - y ^ 2 / 2
  let S3 : ℝ → ℝ := fun y ↦ y - y ^ 3 / 6
  let P4 : ℝ → ℝ := fun y ↦ P2 y + y ^ 4 / 24
  let S5 : ℝ → ℝ := fun y ↦ S3 y + y ^ 5 / 120
  let P6 : ℝ → ℝ := fun y ↦ P4 y - y ^ 6 / 720
  let S7 : ℝ → ℝ := fun y ↦ S5 y - y ^ 7 / 5040
  let P8 : ℝ → ℝ := fun y ↦ P6 y + y ^ 8 / 40320
  let S9 : ℝ → ℝ := fun y ↦ S7 y + y ^ 9 / 362880
  let S11 : ℝ → ℝ := fun y ↦ S9 y - y ^ 11 / 39916800
  have hd_P2 (x : ℝ) : HasDerivAt P2 (-x) x :=
    (hasDerivAt_fn_sub (hasDerivAt_const x (1 : ℝ)) ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv
      (by norm_num)
  have hd_S3 (x : ℝ) : HasDerivAt S3 (P2 x) x :=
    (hasDerivAt_fn_sub (hasDerivAt_id' x) ((hasDerivAt_pow 3 x).div_const 6)).congr_deriv (by ring)
  have hd_P4 (x : ℝ) : HasDerivAt P4 (-S3 x) x :=
    (hasDerivAt_fn_add (hd_P2 x) ((hasDerivAt_pow 4 x).div_const 24)).congr_deriv (by ring)
  have hd_S5 (x : ℝ) : HasDerivAt S5 (P4 x) x :=
    (hasDerivAt_fn_add (hd_S3 x) ((hasDerivAt_pow 5 x).div_const 120)).congr_deriv (by ring)
  have hd_P6 (x : ℝ) : HasDerivAt P6 (-S5 x) x :=
    (hasDerivAt_fn_sub (hd_P4 x) ((hasDerivAt_pow 6 x).div_const 720)).congr_deriv (by ring)
  have hd_S7 (x : ℝ) : HasDerivAt S7 (P6 x) x :=
    (hasDerivAt_fn_sub (hd_S5 x) ((hasDerivAt_pow 7 x).div_const 5040)).congr_deriv (by ring)
  have hd_P8 (x : ℝ) : HasDerivAt P8 (-S7 x) x :=
    (hasDerivAt_fn_add (hd_P6 x) ((hasDerivAt_pow 8 x).div_const 40320)).congr_deriv (by ring)
  have hd_S9 (x : ℝ) : HasDerivAt S9 (P8 x) x :=
    (hasDerivAt_fn_add (hd_S7 x) ((hasDerivAt_pow 9 x).div_const 362880)).congr_deriv (by ring)
  have hd_P10 (x : ℝ) : HasDerivAt cosLowerPoly10 (-S9 x) x :=
    (hasDerivAt_fn_sub (hd_P8 x) ((hasDerivAt_pow 10 x).div_const 3628800)).congr_deriv (by ring)
  have hd_S11 (x : ℝ) : HasDerivAt S11 (cosLowerPoly10 x) x :=
    (hasDerivAt_fn_sub (hd_S9 x) ((hasDerivAt_pow 11 x).div_const 39916800)).congr_deriv (by
      unfold cosLowerPoly10
      ring)
  have hd_P12 (x : ℝ) : HasDerivAt cosUpperPoly12 (-S11 x) x :=
    (hasDerivAt_fn_add (hd_P10 x)
      ((hasDerivAt_pow 12 x).div_const 479001600)).congr_deriv (by ring)
  have hstep {f g f' g' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
      (hg : ∀ x, HasDerivAt g (g' x) x) (h0 : f 0 - g 0 = 0)
      (hfg : ∀ x, 0 ≤ x → 0 ≤ f' x - g' x) : ∀ z, 0 ≤ z → 0 ≤ f z - g z := fun z hz ↦
    nonneg_of_deriv_nonneg (fun y ↦ f y - g y) hz h0 (fun x ↦ hasDerivAt_fn_sub (hf x) (hg x))
      (fun x hx _ ↦ hfg x hx)
  have h1 := hstep hasDerivAt_id' Real.hasDerivAt_sin (by norm_num)
    (fun x _ ↦ by linarith [Real.cos_le_one x])
  have h2 := hstep Real.hasDerivAt_cos hd_P2 (by norm_num [P2]) (fun x hx ↦ by linarith [h1 x hx])
  have h3 := hstep Real.hasDerivAt_sin hd_S3 (by norm_num [S3]) h2
  have h4 := hstep hd_P4 Real.hasDerivAt_cos (by norm_num [P4, P2])
    (fun x hx ↦ by linarith [h3 x hx])
  have h5 := hstep hd_S5 Real.hasDerivAt_sin (by norm_num [S5, S3]) h4
  have h6 := hstep Real.hasDerivAt_cos hd_P6 (by norm_num [P6, P4, P2])
    (fun x hx ↦ by linarith [h5 x hx])
  have h7 := hstep Real.hasDerivAt_sin hd_S7 (by norm_num [S7, S5, S3]) h6
  have h8 := hstep hd_P8 Real.hasDerivAt_cos (by norm_num [P8, P6, P4, P2])
    (fun x hx ↦ by linarith [h7 x hx])
  have h9 := hstep hd_S9 Real.hasDerivAt_sin (by norm_num [S9, S7, S5, S3]) h8
  have h10 := hstep Real.hasDerivAt_cos hd_P10 (by norm_num [cosLowerPoly10])
    (fun x hx ↦ by linarith [h9 x hx])
  have h11 := hstep Real.hasDerivAt_sin hd_S11 (by norm_num [S11, S9, S7, S5, S3]) h10
  have h12 := hstep hd_P12 Real.hasDerivAt_cos (by norm_num [cosUpperPoly12, cosLowerPoly10])
    (fun x hx ↦ by linarith [h11 x hx])
  exact ⟨sub_nonneg.mp (h10 t ht), sub_nonneg.mp (h12 t ht)⟩
theorem one_sub_sq_div_two_le_cos (θ : ℝ) : 1 - θ ^ 2 / 2 ≤ Real.cos θ := by
  have h1 : ∀ z, 0 ≤ z → 0 ≤ z - Real.sin z := fun z hz ↦
    nonneg_of_deriv_nonneg (fun y ↦ y - Real.sin y) hz (by norm_num)
      (fun x ↦ hasDerivAt_fn_sub (hasDerivAt_id' x) (Real.hasDerivAt_sin x))
      (fun x _ _ ↦ by linarith [Real.cos_le_one x])
  have hd2 (x : ℝ) : HasDerivAt (fun y ↦ 1 - y ^ 2 / 2) (-x) x :=
    (hasDerivAt_fn_sub (hasDerivAt_const x (1 : ℝ))
      ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv (by norm_num)
  have h2 : 0 ≤ Real.cos |θ| - (1 - |θ| ^ 2 / 2) :=
    nonneg_of_deriv_nonneg (fun y ↦ Real.cos y - (1 - y ^ 2 / 2)) (abs_nonneg θ) (by norm_num)
      (fun x ↦ hasDerivAt_fn_sub (Real.hasDerivAt_cos x) (hd2 x))
      (fun x hx _ ↦ by linarith [h1 x hx])
  rw [← Real.cos_abs θ, ← sq_abs θ]
  linarith
theorem pi_bounds_8digit : (31415926 / 10000000 : ℝ) ≤ π ∧ π ≤ (31415927 / 10000000 : ℝ) := by
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  set t0 : ℝ := 31415926 / 40000000
  set t1 : ℝ := 31415927 / 40000000
  have hb0 := (cosLowerPoly10_le_cos_and_cos_le_cosUpperPoly12 (by positivity : (0 : ℝ) ≤ t0)).1
  have hb1 := (cosLowerPoly10_le_cos_and_cos_le_cosUpperPoly12 (by positivity : (0 : ℝ) ≤ t1)).2
  have hp0_pos : (0 : ℝ) < cosLowerPoly10 t0 := by norm_num [cosLowerPoly10, t0]
  have hp0_sq : (0 : ℝ) < 2 * cosLowerPoly10 t0 ^ 2 - 1 := by norm_num [cosLowerPoly10, t0]
  have hp1_sq : 2 * cosUpperPoly12 t1 ^ 2 - 1 < 0 := by
    norm_num [cosUpperPoly12, cosLowerPoly10, t1]
  have hcos_2t0 : 0 < Real.cos (2 * t0) := by
    rw [Real.cos_two_mul]
    nlinarith [mul_self_le_mul_self hp0_pos.le hb0]
  have hcos_t1_nn : 0 ≤ Real.cos t1 :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have hcos_2t1 : Real.cos (2 * t1) < 0 := by
    rw [Real.cos_two_mul]
    nlinarith [mul_self_le_mul_self hcos_t1_nn hb1]
  have hmem_pi2 : π / 2 ∈ Set.Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
  have hmem_2t0 : 2 * t0 ∈ Set.Icc (0 : ℝ) π := ⟨by norm_num [t0], by
    dsimp [t0]
    linarith⟩
  have hmem_2t1 : 2 * t1 ∈ Set.Icc (0 : ℝ) π := ⟨by norm_num [t1], by
    dsimp [t1]
    linarith⟩
  constructor
  · by_contra hlt
    push Not at hlt
    have hle : Real.cos (2 * t0) ≤ Real.cos (π / 2) :=
      Real.strictAntiOn_cos.antitoneOn hmem_pi2 hmem_2t0 (by
        dsimp [t0]
        linarith)
    rw [Real.cos_pi_div_two] at hle
    linarith
  · by_contra hlt
    push Not at hlt
    have hle : Real.cos (π / 2) ≤ Real.cos (2 * t1) :=
      Real.strictAntiOn_cos.antitoneOn hmem_2t1 hmem_pi2 (by
        dsimp [t1]
        linarith)
    rw [Real.cos_pi_div_two] at hle
    linarith
theorem cellVolume_rpow_third_bounds : (13425160 / 1000000 : ℝ) ≤ cellVolume ^ (1 / 3 : ℝ) ∧
    cellVolume ^ (1 / 3 : ℝ) ≤ (13425161 / 1000000 : ℝ) := by
  have hlo3 : (13425160 / 1000000 : ℝ) ^ 3 ≤ cellVolume := by norm_num [cellVolume]
  have hhi3 : cellVolume ≤ (13425161 / 1000000 : ℝ) ^ 3 := by norm_num [cellVolume]
  have hc_nn : (0 : ℝ) ≤ cellVolume := by norm_num [cellVolume]
  have h1 := Real.rpow_le_rpow (by positivity) hlo3 (by positivity : (0 : ℝ) ≤ 1 / 3)
  have h2 := Real.rpow_le_rpow hc_nn hhi3 (by positivity : (0 : ℝ) ≤ 1 / 3)
  have cancel_cube (r : ℝ) (hr : 0 ≤ r) : (r ^ 3) ^ (1 / 3 : ℝ) = r := by
    rw [show r ^ 3 = r ^ (3 : ℝ) by norm_num, ← Real.rpow_mul hr]
    norm_num
  rw [cancel_cube _ (by positivity)] at h1
  rw [cancel_cube _ (by positivity)] at h2
  exact ⟨h1, h2⟩
theorem pi_mul_cellVolume_rpow_bounds : (4217638 / 100000 : ℝ) ≤ π * cellVolume ^ (1 / 3 : ℝ)
    ∧ π * cellVolume ^ (1 / 3 : ℝ) ≤ (4217639 / 100000 : ℝ) := by
  rcases pi_bounds_8digit with ⟨hp1, hp2⟩
  rcases cellVolume_rpow_third_bounds with ⟨hv1, hv2⟩
  exact ⟨by linarith [mul_le_mul hp1 hv1 (by norm_num) (by linarith)],
    by linarith [mul_le_mul hp2 hv2 (by linarith) (by norm_num)]⟩
def symmIcc (K : ℕ) : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
def box3D (M : ℤ) : Finset (Fin 3 → ℤ) :=
  (Finset.Icc (-M) M ×ˢ (Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M)).map
    (fin3TupleEquiv ℤ).toEmbedding
def nonzeroBox3D (M : ℤ) : Finset (Fin 3 → ℤ) := (box3D M).erase 0
theorem mem_box3D (M : ℤ) (ν : Fin 3 → ℤ) : ν ∈ box3D M ↔ ∀ w, -M ≤ ν w ∧ ν w ≤ M := by
  simp only [box3D, Finset.mem_map_equiv, Finset.mem_product, Finset.mem_Icc,
    fin3TupleEquiv, Equiv.coe_fn_symm_mk]
  exact ⟨fun ⟨h0, h1, h2⟩ w ↦ by fin_cases w <;> assumption, fun h ↦ ⟨h 0, h 1, h 2⟩⟩
theorem mem_nonzeroBox3D (M : ℤ) (ν : Fin 3 → ℤ) :
    ν ∈ nonzeroBox3D M ↔ ν ≠ 0 ∧ ∀ w, -M ≤ ν w ∧ ν w ≤ M := by
  rw [nonzeroBox3D, Finset.mem_erase, mem_box3D]
def sumNatAbsSq (ν : Fin 3 → ℤ) : ℕ := ∑ w : Fin 3, (ν w).natAbs ^ 2
def natAbsSum (ν : Fin 3 → ℤ) : ℕ := ∑ w : Fin 3, (ν w).natAbs
def maxCoordNatAbs (ν : Fin 3 → ℤ) : ℕ := max (ν 0).natAbs (max (ν 1).natAbs (ν 2).natAbs)
def shellIndex (ν : Fin 3 → ℤ) : ℕ := Nat.log 2 (maxCoordNatAbs ν)
theorem sumNatAbsSq_pos_of_ne_zero {ν : Fin 3 → ℤ} (hν : ν ≠ 0) : 0 < sumNatAbsSq ν := by
  by_contra h0
  have hall := Finset.sum_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (not_lt.mp h0))
  exact hν (funext fun w ↦ Int.natAbs_eq_zero.mp (by nlinarith [hall w (Finset.mem_univ w)]))
theorem maxCoordNatAbs_pos_of_ne_zero {ν : Fin 3 → ℤ} (hν : ν ≠ 0) : 0 < maxCoordNatAbs ν := by
  by_contra h0
  unfold maxCoordNatAbs at h0
  have hle : max (ν 0).natAbs (max (ν 1).natAbs (ν 2).natAbs) ≤ 0 := not_lt.mp h0
  refine hν (funext fun w ↦ Int.natAbs_eq_zero.mp ?_)
  fin_cases w
  · exact Nat.eq_zero_of_le_zero (le_trans (le_max_left _ _) hle)
  · exact Nat.eq_zero_of_le_zero (le_trans (le_max_of_le_right (le_max_left _ _)) hle)
  · exact Nat.eq_zero_of_le_zero (le_trans (le_max_of_le_right (le_max_right _ _)) hle)
theorem maxCoordNatAbs_le_of_mem_box3D {K : ℕ} {ν : Fin 3 → ℤ} (hν : ν ∈ box3D (K : ℤ)) :
    maxCoordNatAbs ν ≤ K := by
  rw [mem_box3D] at hν
  have h0 := hν 0
  have h1 := hν 1
  have h2 := hν 2
  unfold maxCoordNatAbs
  omega
theorem coulombKernel_eq_sumNatAbsSq (ν : Fin 3 → ℤ) : coulombKernel ν =
    (1 / (π * cellVolume ^ (1 / 3 : ℝ))) * (1 / (sumNatAbsSq ν : ℝ)) := by
  by_cases hν : ν = 0
  · subst hν
    simp [coulombKernel, sumNatAbsSq, waveNumberSq, waveVector, dotProduct]
  · have hs_ne : (sumNatAbsSq ν : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (sumNatAbsSq_pos_of_ne_zero hν).ne'
    have hcv : (0 : ℝ) < cellVolume := by
      unfold cellVolume
      positivity
    have hL_ne : cellVolume ^ (1 / 3 : ℝ) ≠ 0 := (by positivity : (0 : ℝ) < _).ne'
    have hv_cube : (cellVolume ^ (1 / 3 : ℝ)) ^ 3 = cellVolume := by
      rw [show (cellVolume ^ (1 / 3 : ℝ)) ^ 3 = (cellVolume ^ (1 / 3 : ℝ)) ^ (3 : ℝ) by norm_num,
        ← Real.rpow_mul hcv.le]
      norm_num
    have hsq (z : ℤ) : (z : ℝ) * (z : ℝ) = (z.natAbs : ℝ) ^ 2 := by
      rcases Int.natAbs_eq z with h | h
      · conv_lhs => rw [h, Int.cast_natCast]
        ring
      · conv_lhs => rw [h, Int.cast_neg, Int.cast_natCast]
        ring
    have hwn : waveNumberSq ν =
        (4 * π ^ 2 / (cellVolume ^ (1 / 3 : ℝ)) ^ 2) * (sumNatAbsSq ν : ℝ) := by
      unfold waveNumberSq waveVector dotProduct sumNatAbsSq
      rw [Fin.sum_univ_three, Fin.sum_univ_three]
      push_cast
      rw [← hsq (ν 0), ← hsq (ν 1), ← hsq (ν 2)]
      field_simp [hL_ne]
      ring
    unfold coulombKernel
    rw [hwn, ← hv_cube]
    field_simp [Real.pi_ne_zero, hL_ne, hs_ne]
    rw [hv_cube, hv_cube]
theorem forty_two_mul_coulombKernel_le (ν : Fin 3 → ℤ) :
    42 * coulombKernel ν ≤ (4200000 / 4217638 : ℝ) * (1 / (sumNatAbsSq ν : ℝ)) := by
  rw [coulombKernel_eq_sumNatAbsSq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (by
      rw [mul_one_div, div_le_iff₀ (by linarith [pi_mul_cellVolume_rpow_bounds.1])]
      linarith [pi_mul_cellVolume_rpow_bounds.1])
    (by positivity)
noncomputable def boxRadConst (B : ℕ) (W_rad w_rad : ℝ) (μ : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ (2 * μ + B) * w_rad / (W_rad * (π * cellVolume ^ (1 / 3 : ℝ)))⌋₊
def coarseEnv8Count (C s : ℕ) : ℕ := (C + 2 ^ 28 * s - 1) / (2 ^ 28 * s)
noncomputable def coarseBoxRadKernel8 (ν : Fin 3 → ℤ) : ℝ := (1 / 42 : ℝ) * (coarseEnv8Count
    (boxRadConst 36 (1 / 42) 1 (shellIndex ν)) (sumNatAbsSq ν) : ℝ) / (2 : ℝ) ^
    (2 * shellIndex ν + 8)
noncomputable def coulombCoarse8PreOAAProb (M M_box : ℕ) : ℝ :=
  (42 / (M_box : ℝ)) * ∑ ν ∈ nonzeroBox3D (M : ℤ), coarseBoxRadKernel8 ν
noncomputable def boost31_coarse8_w13 : ℝ := (3 - 4 * coulombCoarse8PreOAAProb 31 2048) ^ 2
noncomputable def boost127_coarse8_w13 : ℝ := (3 - 4 * coulombCoarse8PreOAAProb 127 8192) ^ 2
def coarseRadCeilVal7 (μ : ℕ) : ℕ := bif Nat.blt μ 4 then bif Nat.blt μ 2 then
    (bif Nat.beq μ 0 then 254 else 1019) else (bif Nat.beq μ 2 then 4078 else 16315) else bif
    Nat.blt μ 6 then (bif Nat.beq μ 4 then 65261 else 261047) else 1044190
def c36Ub7 (μ : ℕ) : ℕ := (4200000 * 2 ^ (2 * μ + 36)) / 4217638
def c36Lb7 (μ : ℕ) : ℕ := (4200000 * 2 ^ (2 * μ + 36)) / 4217639
theorem c36Lb7_le_boxRadConst_and_le_c36Ub7 (μ : ℕ) :
    c36Lb7 μ ≤ boxRadConst 36 (1 / 42) 1 μ ∧ boxRadConst 36 (1 / 42) 1 μ ≤ c36Ub7 μ := by
  rcases pi_mul_cellVolume_rpow_bounds with ⟨hlo, hhi⟩
  have hden_pos : (0 : ℝ) < (1 / 42 : ℝ) * (π * cellVolume ^ (1 / 3 : ℝ)) := by linarith
  refine ⟨Nat.le_floor ?_, (Nat.le_div_iff_mul_le (by decide)).mpr ?_⟩
  · rw [mul_one, le_div_iff₀ hden_pos]
    have hdiv : (c36Lb7 μ : ℝ) * 4217639 ≤ 4200000 * (2 : ℝ) ^ (2 * μ + 36) := by
      exact_mod_cast Nat.div_mul_le_self (4200000 * 2 ^ (2 * μ + 36)) 4217639
    linarith [mul_le_mul_of_nonneg_left (show (1 / 42 : ℝ) * (π * cellVolume ^ (1 / 3 : ℝ)) ≤
      4217639 / 4200000 by linarith) (Nat.cast_nonneg (c36Lb7 μ))]
  · refine Nat.cast_le (α := ℝ).mp ?_
    push_cast
    have hfl := Nat.floor_le (a := (2 : ℝ) ^ (2 * μ + 36) * 1 /
      ((1 / 42 : ℝ) * (π * cellVolume ^ (1 / 3 : ℝ)))) (by positivity)
    have hbd : (2 : ℝ) ^ (2 * μ + 36) * 1 / ((1 / 42 : ℝ) * (π * cellVolume ^ (1 / 3 : ℝ))) ≤
        (4200000 / 4217638 : ℝ) * (2 : ℝ) ^ (2 * μ + 36) := by
      rw [mul_one, div_le_iff₀ hden_pos]
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ (2 * μ + 36) by positivity]
    unfold boxRadConst
    linarith
theorem coarseEnv8Count_eq_coarseRadCeilVal7 {μ s : ℕ} (hμ : μ ≤ 6) (hs : 0 < s) :
    coarseEnv8Count (boxRadConst 36 (1 / 42) 1 μ) s = (coarseRadCeilVal7 μ + s) / s := by
  rcases c36Lb7_le_boxRadConst_and_le_c36Ub7 μ with ⟨hlo, hhi⟩
  have hfin : ∀ μ ≤ 6, 0 < c36Lb7 μ ∧ (c36Lb7 μ - 1) / 2 ^ 28 = coarseRadCeilVal7 μ ∧
      (c36Ub7 μ - 1) / 2 ^ 28 = coarseRadCeilVal7 μ := by decide
  obtain ⟨hlb_pos, hdiv_lo, hdiv_hi⟩ := hfin μ hμ
  have h1 := Nat.div_le_div_right (c := 2 ^ 28) (Nat.sub_le_sub_right hlo 1)
  have h2 := Nat.div_le_div_right (c := 2 ^ 28) (Nat.sub_le_sub_right hhi 1)
  unfold coarseEnv8Count
  rw [show boxRadConst 36 (1 / 42) 1 μ + 2 ^ 28 * s - 1 =
      (boxRadConst 36 (1 / 42) 1 μ - 1) + s * 2 ^ 28 by omega,
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by decide),
    show (boxRadConst 36 (1 / 42) 1 μ - 1) / 2 ^ 28 = coarseRadCeilVal7 μ by omega]
def log2Fast127 (m : ℕ) : ℕ := bif Nat.blt m 2 then 0 else bif Nat.blt m 4 then 1 else bif
    Nat.blt m 8 then 2 else bif Nat.blt m 16 then 3 else bif Nat.blt m 32 then 4 else bif
    Nat.blt m 64 then 5 else 6
theorem log2Fast127_eq_ite (m : ℕ) : log2Fast127 m = if m < 2 then 0 else if m < 4 then 1 else
    if m < 8 then 2 else if m < 16 then 3 else if m < 32 then 4 else if m < 64 then 5 else 6 := by
  have hb (a b : ℕ) {t e : ℕ} : (bif Nat.blt a b then t else e) = if a < b then t else e := by
    cases h : Nat.blt a b
    · split_ifs with hlt
      · exact Bool.noConfusion (h.symm.trans (Nat.blt_eq.mpr hlt))
      · rfl
    · split_ifs with hlt
      · rfl
      · exact (hlt (Nat.blt_eq.mp h)).elim
  unfold log2Fast127
  rw [hb, hb, hb, hb, hb, hb]
theorem log2Fast127_le_six (m : ℕ) : log2Fast127 m ≤ 6 := by
  rw [log2Fast127_eq_ite]
  split_ifs <;> omega
theorem nat_log_two_eq_log2Fast127 {m : ℕ} (hm1 : 1 ≤ m) (hm127 : m ≤ 127) :
    Nat.log 2 m = log2Fast127 m := by
  have hlog (lo hi k : ℕ) (h1 : 2 ^ k ≤ lo) (h2 : hi < 2 ^ (k + 1)) (hlo : lo ≤ m) (hhi : m ≤ hi) :
      Nat.log 2 m = k :=
    Nat.le_antisymm (Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) (by omega)))
      (Nat.le_log_of_pow_le (by decide) (by omega))
  rw [log2Fast127_eq_ite]
  split_ifs
  · exact hlog 1 1 0 (by decide) (by decide) hm1 (by omega)
  · exact hlog 2 3 1 (by decide) (by decide) (by omega) (by omega)
  · exact hlog 4 7 2 (by decide) (by decide) (by omega) (by omega)
  · exact hlog 8 15 3 (by decide) (by decide) (by omega) (by omega)
  · exact hlog 16 31 4 (by decide) (by decide) (by omega) (by omega)
  · exact hlog 32 63 5 (by decide) (by decide) (by omega) (by omega)
  · exact hlog 64 127 6 (by decide) (by decide) (by omega) hm127
def octWeight (a : ℕ) : ℕ := bif Nat.beq a 0 then 1 else 2
def natSum (n : ℕ) (g : ℕ → ℕ) : ℕ := Nat.rec 0 (fun k acc ↦ acc + g k) n
@[simp] private theorem lemHex166 (g : ℕ → ℕ) : natSum 0 g = 0 := rfl
@[simp] private theorem lemHex167 (k : ℕ) (g : ℕ → ℕ) : natSum (k + 1) g = natSum k g + g k := rfl
theorem sum_range_eq_natSum (n : ℕ) (g : ℕ → ℕ) :
    ∑ a ∈ Finset.range n, (g a : ℝ) = (natSum n g : ℝ) := by
  induction n with
  | zero => simp [lemHex166]
  | succ k ih =>
      rw [Finset.sum_range_succ, lemHex167, ih]
      push_cast
      rfl
theorem natSum_congr {n : ℕ} {g₁ g₂ : ℕ → ℕ} (h : ∀ a < n, g₁ a = g₂ a) :
    natSum n g₁ = natSum n g₂ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [lemHex167, lemHex167, ih fun a ha ↦ h a (by omega), h k (by omega)]
theorem natSum_add (n : ℕ) (g₁ g₂ : ℕ → ℕ) :
    natSum n (fun a ↦ g₁ a + g₂ a) = natSum n g₁ + natSum n g₂ := by
  induction n with
  | zero => rfl
  | succ _ ih =>
      simp only [lemHex167, ih]
      omega
theorem natSum_add_split (m n : ℕ) (g : ℕ → ℕ) :
    natSum (m + n) g = natSum m g + natSum n (fun i ↦ g (m + i)) := by
  induction n with
  | zero => simp [lemHex166]
  | succ _ ih => rw [Nat.add_succ, lemHex167, lemHex167, ih, Nat.add_assoc]
theorem natSum_symm2D (n : ℕ) (F : ℕ → ℕ → ℕ) (hsym : ∀ b c, F b c = F c b) :
    natSum n (fun b ↦ natSum n (fun c ↦ F b c)) =
      natSum n (fun b ↦ F b b + 2 * natSum b (fun c ↦ F b c)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [lemHex167]
      rw [natSum_add, ← ih]
      have hswap : natSum k (fun b ↦ F b k) = natSum k (fun c ↦ F k c) :=
        natSum_congr fun b _ ↦ hsym b k
      omega
theorem natSum_symm3D (n : ℕ) (G : ℕ → ℕ → ℕ → ℕ) (h12 : ∀ a b c, G a b c = G b a c)
    (h23 : ∀ a b c, G a b c = G a c b) : natSum n
    (fun a ↦ natSum n (fun b ↦ natSum n (fun c ↦ G a b c))) = natSum n (fun k ↦ G k k k + 3 *
    natSum k (fun b ↦ G k k b) + 3 * natSum k (fun b ↦ G k b b + 2 * natSum b (fun c ↦ G k b
    c))) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h_in (a : ℕ) : natSum (k + 1) (fun b ↦ natSum (k + 1) (fun c ↦ G a b c)) = natSum k
        (fun b ↦ natSum k (fun c ↦ G a b c)) + natSum k (fun b ↦ G a b k) + natSum k
        (fun c ↦ G a k c) + G a k k := by
      simp only [lemHex167, natSum_add]
      omega
    change natSum k (fun a ↦ natSum (k + 1) (fun b ↦ natSum (k + 1) (fun c ↦ G a b c))) +
      natSum (k + 1) (fun b ↦ natSum (k + 1) (fun c ↦ G k b c)) = _
    simp_rw [h_in]
    rw [natSum_add, natSum_add, natSum_add, ih,
      show natSum k (fun a ↦ natSum k (fun b ↦ G a b k)) =
        natSum k (fun b ↦ natSum k (fun c ↦ G k b c)) from
        natSum_congr fun a _ ↦ natSum_congr fun b _ ↦ (h23 a b k).trans (h12 a k b),
      show natSum k (fun a ↦ natSum k (fun c ↦ G a k c)) =
        natSum k (fun b ↦ natSum k (fun c ↦ G k b c)) from
        natSum_congr fun a _ ↦ natSum_congr fun c _ ↦ h12 a k c,
      show natSum k (fun a ↦ G a k k) = natSum k (fun b ↦ G k k b) from
        natSum_congr fun a _ ↦ (h12 a k k).trans (h23 k a k),
      show natSum k (fun b ↦ G k b k) = natSum k (fun b ↦ G k k b) from
        natSum_congr fun b _ ↦ h23 k b k,
      natSum_symm2D k (fun b c ↦ G k b c) (fun b c ↦ h23 k b c), lemHex167]
    omega
def natSum32_2 (d : ℕ) (g : ℕ → ℕ) : ℕ := (natSum 32 g + natSum 32 (fun j ↦ g (32 + j))) +
    (natSum 32 (fun j ↦ g (64 + j)) + natSum d (fun j ↦ g (96 + j)))
theorem natSum_96_add_eq (d : ℕ) (g : ℕ → ℕ) : natSum (96 + d) g = natSum32_2 d g := by
  unfold natSum32_2
  rw [show 96 + d = ((32 + 32) + 32) + d from rfl, natSum_add_split ((32 + 32) + 32) d,
    natSum_add_split (32 + 32) 32, natSum_add_split 32 32]
  simp only [Nat.reduceAdd, Nat.add_assoc]
def octShell (T : ℕ → ℕ → ℕ → ℕ) (k : ℕ) : ℕ := T k k k + 3 * natSum k (fun b ↦ T k k b) + 3 *
    natSum k (fun b ↦ T k b b + 2 * natSum b (fun c ↦ T k b c))
def octShell96 (T : ℕ → ℕ → ℕ → ℕ) (d : ℕ) : ℕ :=
  let k := 96 + d
  T k k k + 3 * natSum32_2 d (fun b ↦ T k k b) +
  3 * ((natSum 32 (fun b ↦ T k b b + 2 * natSum b (fun c ↦ T k b c)) +
        natSum 32 (fun j ↦
          let b := 32 + j
          T k b b + 2 * (natSum 32 (fun c ↦ T k b c) + natSum j (fun c ↦ T k b (32 + c))))) +
       (natSum 32 (fun j ↦
          let b := 64 + j
          T k b b + 2 * ((natSum 32 (fun c ↦ T k b c) + natSum 32 (fun c ↦ T k b (32 + c))) +
            natSum j (fun c ↦ T k b (64 + c)))) +
        natSum d (fun j ↦
          let b := 96 + j
          T k b b + 2 * natSum32_2 j (fun c ↦ T k b c))))
theorem octShell_96_add_eq (T : ℕ → ℕ → ℕ → ℕ) (d : ℕ) :
    octShell T (96 + d) = octShell96 T d := by
  unfold octShell octShell96
  dsimp only
  rw [natSum_96_add_eq d (fun b ↦ T (96 + d) (96 + d) b),
    natSum_96_add_eq d (fun b ↦ T (96 + d) b b + 2 * natSum b (fun c ↦ T (96 + d) b c))]
  unfold natSum32_2
  have h32 (j : ℕ) : natSum (32 + j) (fun c ↦ T (96 + d) (32 + j) c) = natSum 32
      (fun c ↦ T (96 + d) (32 + j) c) + natSum j (fun c ↦ T (96 + d) (32 + j) (32 + c)) :=
      natSum_add_split 32 j _
  have h64 (j : ℕ) : natSum (64 + j) (fun c ↦ T (96 + d) (64 + j) c) = (natSum 32 (fun c ↦ T
      (96 + d) (64 + j) c) + natSum 32 (fun c ↦ T (96 + d) (64 + j) (32 + c))) + natSum j
      (fun c ↦ T (96 + d) (64 + j) (64 + c)) := by
    have h64_eq : 64 + j = (32 + 32) + j := rfl
    rw [h64_eq, natSum_add_split (32 + 32) j, natSum_add_split 32 32]
  have h96 (j : ℕ) : natSum (96 + j) (fun c ↦ T (96 + d) (96 + j) c) = natSum32_2 j
      (fun c ↦ T (96 + d) (96 + j) c) := natSum_96_add_eq j _
  simp_rw [h32, h64, h96]
  rfl
theorem sum_symmIcc_succ (K : ℕ) (f : ℤ → ℝ) : ∑ x ∈ symmIcc (K + 1), f x =
    (∑ x ∈ symmIcc K, f x) + f (-(K + 1 : ℤ)) + f (K + 1 : ℤ) := by
  have hs : symmIcc (K + 1) = insert (-(K + 1 : ℤ)) (insert (K + 1 : ℤ) (symmIcc K)) := by
    ext x
    simp only [symmIcc, Finset.mem_insert, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
    omega
  have hn1 : (-(K + 1 : ℤ)) ∉ insert (K + 1 : ℤ) (symmIcc K) := by
    simp only [symmIcc, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hs, Finset.sum_insert hn1, Finset.sum_insert (by simp [symmIcc])]
  ring
theorem sum_symmIcc_natAbs (K : ℕ) (h : ℕ → ℝ) : ∑ x ∈ symmIcc K, h x.natAbs = ∑ a ∈
    Finset.range (K + 1), (octWeight a : ℝ) * h a := by
  induction K with
  | zero => simp [symmIcc, octWeight]
  | succ K ih =>
    rw [sum_symmIcc_succ, ih, Finset.sum_range_succ (n := K + 1),
      show (-(K + 1 : ℤ)).natAbs = K + 1 by omega, show ((K + 1 : ℤ)).natAbs = K + 1 by omega,
      show octWeight (K + 1) = 2 from rfl]
    push_cast
    ring
theorem sum_nonzeroBox3D_eq_oct_natSum (K : ℕ) (F : ℕ → ℕ → ℕ → ℕ) (h0 : F 0 0 0 = 0)
    (h12 : ∀ a b c, F a b c = F b a c) (h23 : ∀ a b c, F a b c = F a c b) : ∑ ν ∈ nonzeroBox3D
    (K : ℤ), (F (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) = (natSum (K + 1) (octShell (fun a
    b c ↦ octWeight a * octWeight b * octWeight c * F a b c)) : ℝ) := by
  have rotAux : ∑ ν ∈ nonzeroBox3D (K : ℤ), (F (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) =
      ∑ ν ∈ box3D (K : ℤ), (F (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) := by
    unfold nonzeroBox3D
    have h := Finset.add_sum_erase (box3D (K : ℤ))
      (fun ν ↦ (F (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ))
      ((mem_box3D (K : ℤ) 0).mpr fun _ ↦ by simp)
    simp only [Pi.zero_apply, Int.natAbs_zero, h0, Nat.cast_zero, zero_add] at h
    exact h
  rw [rotAux]
  unfold box3D
  rw [Finset.sum_map]
  simp_rw [Finset.sum_product]
  change ∑ x ∈ symmIcc K, ∑ y ∈ symmIcc K, ∑ z ∈ symmIcc K,
      (F x.natAbs y.natAbs z.natAbs : ℝ) = _
  have hinner : ∑ x ∈ symmIcc K, ∑ y ∈ symmIcc K, ∑ z ∈ symmIcc K,
      (F x.natAbs y.natAbs z.natAbs : ℝ) = ∑ a ∈ Finset.range (K + 1), (octWeight a : ℝ) * ∑ b
      ∈ Finset.range (K + 1), (octWeight b : ℝ) * ∑ c ∈ Finset.range (K + 1),
      (octWeight c : ℝ) * (F a b c : ℝ) := by
    rw [sum_symmIcc_natAbs K (fun a ↦
      ∑ y ∈ symmIcc K, ∑ z ∈ symmIcc K, (F a y.natAbs z.natAbs : ℝ))]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    congr 1
    rw [sum_symmIcc_natAbs K (fun b ↦ ∑ z ∈ symmIcc K, (F a b z.natAbs : ℝ))]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    congr 1
    exact sum_symmIcc_natAbs K (fun c ↦ (F a b c : ℝ))
  rw [hinner]
  let T : ℕ → ℕ → ℕ → ℕ := fun a b c ↦ octWeight a * octWeight b * octWeight c * F a b c
  simp_rw [Finset.mul_sum, show ∀ a b c,
      (octWeight a : ℝ) * ((octWeight b : ℝ) * ((octWeight c : ℝ) * (F a b c : ℝ))) = (T a b c : ℝ)
      from fun a b c ↦ by
        dsimp [T]
        push_cast
        ring,
    sum_range_eq_natSum (K + 1)]
  exact congrArg Nat.cast (natSum_symm3D (K + 1) T
    (fun a b c ↦ by
      dsimp [T]
      rw [h12 a b c]
      ring)
    (fun a b c ↦ by
      dsimp [T]
      rw [h23 a b c]
      ring))
def max2Nat (a b : ℕ) : ℕ := bif Nat.ble a b then b else a
def max3Nat (a b c : ℕ) : ℕ := max2Nat a (max2Nat b c)
def sq3Nat (a b c : ℕ) : ℕ := a * a + b * b + c * c
theorem max3Nat_eq_max (a b c : ℕ) : max3Nat a b c = max a (max b c) := by
  have hb (x y : ℕ) : max2Nat x y = max x y := by
    unfold max2Nat
    match h : Nat.ble x y with
    | true => exact (Nat.max_eq_right (Nat.ble_eq.mp h)).symm
    | false =>
      exact (Nat.max_eq_left
        (Nat.le_of_not_ge fun hle ↦ Bool.noConfusion (h.symm.trans (Nat.ble_eq.mpr hle)))).symm
  unfold max3Nat
  rw [hb, hb]
theorem cond_beq_zero_ne {m : ℕ} (hm : m ≠ 0) (x : ℕ) : (bif Nat.beq m 0 then 0 else x) = x :=
  match h : Nat.beq m 0 with
  | false => rfl
  | true => (hm (Nat.beq_eq.mp h)).elim
theorem max3Nat_swap12 (a b c : ℕ) : max3Nat a b c = max3Nat b a c := by
  simp only [max3Nat_eq_max, max_left_comm a b c]
theorem max3Nat_swap23 (a b c : ℕ) : max3Nat a b c = max3Nat a c b := by
  simp only [max3Nat_eq_max, max_comm b c]
theorem sq3Nat_swap12 (a b c : ℕ) : sq3Nat a b c = sq3Nat b a c := by
  unfold sq3Nat
  ring
theorem sq3Nat_swap23 (a b c : ℕ) : sq3Nat a b c = sq3Nat a c b := by
  unfold sq3Nat
  ring
theorem maxCoordNatAbs_eq_max3Nat (ν : Fin 3 → ℤ) : maxCoordNatAbs ν = max3Nat (ν 0).natAbs
    (ν 1).natAbs (ν 2).natAbs := (max3Nat_eq_max _ _ _).symm
theorem sumNatAbsSq_eq_sq3Nat (ν : Fin 3 → ℤ) :
    sumNatAbsSq ν = sq3Nat (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs := by
  unfold sumNatAbsSq sq3Nat
  rw [Fin.sum_univ_three]
  ring
theorem oct_natSum_128_eq_chunks (T : ℕ → ℕ → ℕ → ℕ) {c0 c1 c2 c3 c4 tot : ℕ} (hc0 : natSum 32
    (octShell T) + natSum 32 (fun i ↦ octShell T (32 + i)) = c0)
    (hc1 : natSum 24 (fun i ↦ octShell T (64 + i)) = c1) (hc2 : natSum 8 (fun i ↦ octShell T
    (88 + i)) + natSum 8 (fun i ↦ octShell96 T i) = c2)
    (hc3 : natSum 12 (fun i ↦ octShell96 T (8 + i)) = c3)
    (hc4 : natSum 12 (fun i ↦ octShell96 T (20 + i)) = c4)
    (htot : (((c0 + c1) + c2) + c3) + c4 = tot) : natSum 128 (octShell T) = tot := by
  have hsplit : natSum 128 (octShell T) = ((((natSum 32 (octShell T) + natSum 32 (fun i ↦
      octShell T (32 + i))) + natSum 24 (fun i ↦ octShell T (64 + i))) + (natSum 8 (fun i ↦
      octShell T (88 + i)) + natSum 8 (fun i ↦ octShell T (96 + i)))) + natSum 12 (fun i ↦
      octShell T (104 + i))) + natSum 12 (fun i ↦ octShell T (116 + i)) := by
    rw [show (128 : ℕ) = (((((32 + 32) + 24) + 8) + 8) + 12) + 12 from rfl,
      natSum_add_split (((((32 + 32) + 24) + 8) + 8) + 12) 12,
      natSum_add_split ((((32 + 32) + 24) + 8) + 8) 12,
      natSum_add_split (((32 + 32) + 24) + 8) 8, natSum_add_split ((32 + 32) + 24) 8,
      natSum_add_split (32 + 32) 24, natSum_add_split 32 32]
    simp only [Nat.reduceAdd]
    ac_rfl
  rw [hsplit, natSum_congr fun i _ ↦ octShell_96_add_eq T i,
    natSum_congr fun i _ ↦
      (congrArg (octShell T) (show 104 + i = 96 + (8 + i) by omega)).trans
        (octShell_96_add_eq T _),
    natSum_congr fun i _ ↦
      (congrArg (octShell T) (show 116 + i = 96 + (20 + i) by omega)).trans
        (octShell_96_add_eq T _),
    hc0, hc1, hc2, hc3, hc4, htot]
def inv4Val7 (μ : ℕ) : ℕ := bif Nat.blt μ 4 then bif Nat.blt μ 2 then
    (bif Nat.beq μ 0 then 4096 else 1024) else (bif Nat.beq μ 2 then 256 else 64) else bif
    Nat.blt μ 6 then (bif Nat.beq μ 4 then 16 else 4) else 1
theorem inv4Val7_eq {μ : ℕ} (hμ : μ ≤ 6) : inv4Val7 μ = 2 ^ (12 - 2 * μ) := by
  rcases (show μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
def fOaa (a b c : ℕ) : ℕ :=
  let m := max3Nat a b c
  let s := sq3Nat a b c
  bif Nat.beq m 0 then 0
  else ((coarseRadCeilVal7 (log2Fast127 m) + s) / s) * inv4Val7 (log2Fast127 m)
def fInv4 (a b c : ℕ) : ℕ :=
  let m := max3Nat a b c
  bif Nat.beq m 0 then 0 else inv4Val7 (log2Fast127 m)
def fInvSq (a b c : ℕ) : ℕ :=
  let s := sq3Nat a b c
  bif Nat.beq s 0 then 0 else (1048576 + s - 1) / s
def fLin (a b c : ℕ) : ℕ :=
  let s := sq3Nat a b c
  bif Nat.beq s 0 then 0 else ((a + b + c) * 1048576 + s - 1) / s
def octOaa (a b c : ℕ) : ℕ := octWeight a * octWeight b * octWeight c * fOaa a b c
def octInv4 (a b c : ℕ) : ℕ := octWeight a * octWeight b * octWeight c * fInv4 a b c
def octInvSq (a b c : ℕ) : ℕ := octWeight a * octWeight b * octWeight c * fInvSq a b c
def octLin (a b c : ℕ) : ℕ := octWeight a * octWeight b * octWeight c * fLin a b c
private def lemHex168 (cVal wVal a b c : ℕ) : ℕ :=
  let s := sq3Nat a b c
  ((cVal + s) / s) * wVal
private def lemHex169 (k : ℕ) : ℕ :=
  bif Nat.beq k 0 then 0
  else
    let μ := log2Fast127 k
    octShell (fun a b c ↦ octWeight a * octWeight b * octWeight c *
      lemHex168 (coarseRadCeilVal7 μ) (inv4Val7 μ) a b c) k
private def lemHex16a (d : ℕ) : ℕ :=
  let μ := log2Fast127 (96 + d)
  octShell96 (fun a b c ↦ octWeight a * octWeight b * octWeight c *
    lemHex168 (coarseRadCeilVal7 μ) (inv4Val7 μ) a b c) d
private def lemHex16b (k : ℕ) : ℕ :=
  bif Nat.beq k 0 then 0
  else
    let wVal := inv4Val7 (log2Fast127 k)
    octShell (fun a b c ↦ octWeight a * octWeight b * octWeight c * wVal) k
private def lemHex16c (d : ℕ) : ℕ :=
  let wVal := inv4Val7 (log2Fast127 (96 + d))
  octShell96 (fun a b c ↦ octWeight a * octWeight b * octWeight c * wVal) d
private theorem lemHex16d {k b c : ℕ} (hb : b ≤ k) (hc : c ≤ k) : max3Nat k b c = k := by
  rw [max3Nat_eq_max]; omega
private theorem lemHex16e (T₁ T₂ : ℕ → ℕ → ℕ → ℕ) (k : ℕ)
    (h : ∀ b c, b ≤ k → c ≤ k → T₁ k b c = T₂ k b c) : octShell T₁ k = octShell T₂ k := by
  unfold octShell
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (h k k le_rfl le_rfl)
      (congrArg (3 * ·) (natSum_congr fun b hb ↦ h k b le_rfl hb.le)))
    (congrArg (3 * ·) (natSum_congr fun b hb ↦ congrArg₂ (· + ·) (h b b hb.le hb.le)
      (congrArg (2 * ·) (natSum_congr fun c hc ↦ h b c hb.le (hc.trans hb).le))))
private theorem lemHex16f (T₁ T₂ : ℕ → ℕ → ℕ → ℕ) (d : ℕ) (h : ∀ b c, b ≤ 96 + d → c ≤ 96 + d → T₁
    (96 + d) b c = T₂ (96 + d) b c) : octShell96 T₁ d = octShell96 T₂ d := by
  rw [← octShell_96_add_eq, ← octShell_96_add_eq]
  exact lemHex16e T₁ T₂ (96 + d) h
private theorem lemHex170 (k : ℕ) : octShell octOaa k = lemHex169 k := by
  cases k with
  | zero => rfl
  | succ m =>
    have hbeq : Nat.beq (m + 1) 0 = false := rfl
    change octShell octOaa (m + 1) =
      octShell (fun a b c ↦ octWeight a * octWeight b * octWeight c *
        lemHex168 (coarseRadCeilVal7 (log2Fast127 (m + 1)))
          (inv4Val7 (log2Fast127 (m + 1))) a b c) (m + 1)
    refine lemHex16e _ _ (m + 1) fun b c hb hc ↦ ?_
    unfold octOaa fOaa lemHex168
    rw [lemHex16d hb hc]
    dsimp
    rw [hbeq]
    rfl
private theorem lemHex171 (d : ℕ) : octShell96 octOaa d = lemHex16a d := by
  have hbeq : Nat.beq (96 + d) 0 = false := by
    rw [show 96 + d = (95 + d) + 1 by omega]
    rfl
  unfold lemHex16a
  dsimp
  refine lemHex16f _ _ d fun b c hb hc ↦ ?_
  unfold octOaa fOaa lemHex168
  rw [lemHex16d hb hc]
  dsimp
  rw [hbeq]
  rfl
private theorem lemHex172 (k : ℕ) : octShell octInv4 k = lemHex16b k := by
  cases k with
  | zero => rfl
  | succ m =>
    have hbeq : Nat.beq (m + 1) 0 = false := rfl
    change octShell octInv4 (m + 1) = octShell (fun a b c ↦ octWeight a * octWeight b *
      octWeight c * inv4Val7 (log2Fast127 (m + 1))) (m + 1)
    refine lemHex16e _ _ (m + 1) fun b c hb hc ↦ ?_
    unfold octInv4 fInv4
    rw [lemHex16d hb hc]
    dsimp
    rw [hbeq]
    rfl
private theorem lemHex173 (d : ℕ) : octShell96 octInv4 d = lemHex16c d := by
  have hbeq : Nat.beq (96 + d) 0 = false := by
    rw [show 96 + d = (95 + d) + 1 by omega]
    rfl
  unfold lemHex16c
  dsimp
  refine lemHex16f _ _ d fun b c hb hc ↦ ?_
  unfold octInv4 fInv4
  rw [lemHex16d hb hc]
  dsimp
  rw [hbeq]
  rfl
private theorem lemHex174 : octShell octOaa = lemHex169 := funext lemHex170
private theorem lemHex175 : octShell96 octOaa = lemHex16a := funext lemHex171
private theorem lemHex176 : octShell octInv4 = lemHex16b := funext lemHex172
private theorem lemHex177 : octShell96 octInv4 = lemHex16c := funext lemHex173
private theorem lemHex178 (a m n : ℕ) (g : ℕ → ℕ) : natSum (m + n) (fun i ↦ g (a + i)) =
    natSum m (fun i ↦ g (a + i)) + natSum n (fun i ↦ g ((a + m) + i)) := by
  rw [natSum_add_split m n]
  exact congrArg _ (natSum_congr fun i _ ↦ congrArg g (Nat.add_assoc a m i).symm)
private theorem lemHex179 {g' : ℕ → ℕ} {tot : ℕ} (g : ℕ → ℕ) (v0 v1 v2 v3 : ℕ)
    (hg : g' = g := by rfl) (h0 : natSum 32 g = v0 := by rfl)
    (h1 : natSum 16 (fun i ↦ g (32 + i)) = v1 := by rfl)
    (h2 : natSum 8 (fun i ↦ g (48 + i)) = v2 := by rfl)
    (h3 : natSum 8 (fun i ↦ g (56 + i)) = v3 := by rfl)
    (htot : v0 + (v1 + (v2 + v3)) = tot := by decide) :
    natSum 32 g' + natSum 32 (fun i ↦ g' (32 + i)) = tot := by
  rw [hg, lemHex178 32 16 16 g, lemHex178 48 8 8 g, h0, h1, h2, h3, htot]
private theorem p17_3x4 {g' : ℕ → ℕ} {tot : ℕ} (g : ℕ → ℕ) (a v0 v1 v2 : ℕ)
    (hg : g' = g := by rfl) (h0 : natSum 4 (fun i ↦ g (a + i)) = v0 := by rfl)
    (h1 : natSum 4 (fun i ↦ g ((a + 4) + i)) = v1 := by rfl)
    (h2 : natSum 4 (fun i ↦ g ((a + 8) + i)) = v2 := by rfl)
    (htot : v0 + (v1 + v2) = tot := by decide) :
    natSum 12 (fun i ↦ g' (a + i)) = tot := by
  rw [hg, lemHex178 a 4 8 g, lemHex178 (a + 4) 4 4 g, h0, h1, h2, htot]
private theorem p17_4x2 {g' : ℕ → ℕ} {tot : ℕ} (g : ℕ → ℕ) (a v0 v1 v2 v3 : ℕ)
    (hg : g' = g := by rfl) (h0 : natSum 2 (fun i ↦ g (a + i)) = v0 := by rfl)
    (h1 : natSum 2 (fun i ↦ g ((a + 2) + i)) = v1 := by rfl)
    (h2 : natSum 2 (fun i ↦ g ((a + 4) + i)) = v2 := by rfl)
    (h3 : natSum 2 (fun i ↦ g ((a + 6) + i)) = v3 := by rfl)
    (htot : v0 + (v1 + (v2 + v3)) = tot := by decide) :
    natSum 8 (fun i ↦ g' (a + i)) = tot := by
  rw [hg, lemHex178 a 2 6 g, lemHex178 (a + 2) 2 4 g, lemHex178 (a + 4) 2 2 g, h0, h1, h2, h3, htot]
private theorem p17_3x2 {g' : ℕ → ℕ} {tot : ℕ} (g : ℕ → ℕ) (a v0 v1 v2 : ℕ)
    (hg : g' = g := by rfl) (h0 : natSum 2 (fun i ↦ g (a + i)) = v0 := by rfl)
    (h1 : natSum 2 (fun i ↦ g ((a + 2) + i)) = v1 := by rfl)
    (h2 : natSum 2 (fun i ↦ g ((a + 4) + i)) = v2 := by rfl)
    (htot : v0 + (v1 + v2) = tot := by decide) :
    natSum 6 (fun i ↦ g' (a + i)) = tot := by
  rw [hg, lemHex178 a 2 4 g, lemHex178 (a + 2) 2 2 g, h0, h1, h2, htot]
private theorem p17_6x1 {g' : ℕ → ℕ} {tot : ℕ} (g : ℕ → ℕ) (a u0 u1 u2 u3 u4 u5 : ℕ)
    (hg : g' = g := by rfl) (h0 : natSum 1 (fun i ↦ g (a + i)) = u0 := by rfl)
    (h1 : natSum 1 (fun i ↦ g ((a + 1) + i)) = u1 := by rfl)
    (h2 : natSum 1 (fun i ↦ g ((a + 2) + i)) = u2 := by rfl)
    (h3 : natSum 1 (fun i ↦ g ((a + 3) + i)) = u3 := by rfl)
    (h4 : natSum 1 (fun i ↦ g ((a + 4) + i)) = u4 := by rfl)
    (h5 : natSum 1 (fun i ↦ g ((a + 5) + i)) = u5 := by rfl)
    (htot : u0 + (u1 + (u2 + (u3 + (u4 + u5)))) = tot := by decide) :
    natSum 6 (fun i ↦ g' (a + i)) = tot := by
  rw [hg, lemHex178 a 1 5 g, lemHex178 (a + 1) 1 4 g, lemHex178 (a + 2) 1 3 g,
    lemHex178 (a + 3) 1 2 g, lemHex178 (a + 4) 1 1 g, h0, h1, h2, h3, h4, h5, htot]
private theorem p17_comb (T : ℕ → ℕ → ℕ → ℕ) (tot : ℕ)
    {c0 c1a c1b c2a c2b c3a c3b c4a c4b : ℕ}
    (hc0 : natSum 32 (octShell T) + natSum 32 (fun i ↦ octShell T (32 + i)) = c0)
    (hc1a : natSum 12 (fun i ↦ octShell T (64 + i)) = c1a)
    (hc1b : natSum 12 (fun i ↦ octShell T (76 + i)) = c1b)
    (hc2a : natSum 8 (fun i ↦ octShell T (88 + i)) = c2a)
    (hc2b : natSum 8 (fun i ↦ octShell96 T (0 + i)) = c2b)
    (hc3a : natSum 6 (fun i ↦ octShell96 T (8 + i)) = c3a)
    (hc3b : natSum 6 (fun i ↦ octShell96 T (14 + i)) = c3b)
    (hc4a : natSum 6 (fun i ↦ octShell96 T (20 + i)) = c4a)
    (hc4b : natSum 6 (fun i ↦ octShell96 T (26 + i)) = c4b)
    (htot : (((c0 + (c1a + c1b)) + (c2a + c2b)) + (c3a + c3b)) + (c4a + c4b) = tot :=
      by decide) :
    natSum 128 (octShell T) = tot := by
  refine oct_natSum_128_eq_chunks T hc0 ?_ ?_ ?_ ?_ htot
  · rw [lemHex178 64 12 12 (octShell T), hc1a, hc1b]
  · rw [hc2a, show (fun i ↦ octShell96 T i) = fun i ↦ octShell96 T (0 + i) from
      funext fun i ↦ congrArg (octShell96 T) (Nat.zero_add i).symm, hc2b]
  · rw [lemHex178 8 6 6 (octShell96 T), hc3a, hc3b]
  · rw [lemHex178 20 6 6 (octShell96 T), hc4a, hc4b]
private theorem sum_127_of_oct (F : ℕ → ℕ → ℕ → ℕ) (tot : ℕ) (r : ℝ) (h0 : F 0 0 0 = 0)
    (h12 : ∀ a b c, F a b c = F b a c) (h23 : ∀ a b c, F a b c = F a c b)
    (hcomb : natSum 128 (octShell (fun a b c ↦
      octWeight a * octWeight b * octWeight c * F a b c)) = tot)
    (hr : (tot : ℝ) = r := by norm_num) :
    ∑ ν ∈ nonzeroBox3D (127 : ℤ), (F (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) = r := by
  rw [← hr, show (127 : ℤ) = ((127 : ℕ) : ℤ) from rfl,
    sum_nonzeroBox3D_eq_oct_natSum 127 F h0 h12 h23, hcomb]
theorem sum_fOaa_31 : ∑ ν ∈ nonzeroBox3D (31 : ℤ),
    (fOaa (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) = 498655168 := by
  rw [show (31 : ℤ) = ((31 : ℕ) : ℤ) from rfl, sum_nonzeroBox3D_eq_oct_natSum 31 fOaa rfl
    (fun a b c ↦ by simp only [fOaa, max3Nat_swap12, sq3Nat_swap12])
    (fun a b c ↦ by simp only [fOaa, max3Nat_swap23, sq3Nat_swap23])]
  have hs : natSum 32 (octShell octOaa) = 498655168 := by
    rw [lemHex174]
    rfl
  exact_mod_cast hs
private theorem octOaa_c0 :
    natSum 32 (octShell octOaa) + natSum 32 (fun i ↦ octShell octOaa (32 + i)) = 1015092512 :=
  lemHex179 lemHex169 498655168 257631696 129234384 129571264 lemHex174
private theorem octOaa_c1a : natSum 12 (fun i ↦ octShell octOaa (64 + i)) = 193009702 :=
  p17_3x4 lemHex169 64 64309540 64336016 64364146 lemHex174
private theorem octOaa_c1b : natSum 12 (fun i ↦ octShell octOaa (76 + i)) = 193278222 :=
  p17_3x4 lemHex169 76 64394604 64425832 64457786 lemHex174
private theorem octOaa_c2a : natSum 8 (fun i ↦ octShell octOaa (88 + i)) = 129013130 :=
  p17_4x2 lemHex169 88 32238850 32249356 32257906 32267018 lemHex174
private theorem octOaa_c2b : natSum 8 (fun i ↦ octShell96 octOaa (0 + i)) = 129163206 :=
  p17_4x2 lemHex16a 0 32276106 32285708 32295740 32305652 lemHex175
private theorem octOaa_c3a : natSum 6 (fun i ↦ octShell96 octOaa (8 + i)) = 96976166 :=
  p17_3x2 lemHex16a 8 32315620 32324650 32335896 lemHex175
private theorem octOaa_c3b : natSum 6 (fun i ↦ octShell96 octOaa (14 + i)) = 97069584 :=
  p17_3x2 lemHex16a 14 32344820 32357152 32367612 lemHex175
private theorem octOaa_c4a : natSum 6 (fun i ↦ octShell96 octOaa (20 + i)) = 97171502 :=
  p17_6x1 lemHex16a 20 16188496 16191322 16193666 16196600 16199378 16202040 lemHex175
private theorem octOaa_c4b : natSum 6 (fun i ↦ octShell96 octOaa (26 + i)) = 97273782 :=
  p17_6x1 lemHex16a 26 16204674 16208232 16210528 16213114 16216952 16220282 lemHex175
theorem sum_fOaa_127 : ∑ ν ∈ nonzeroBox3D (127 : ℤ),
    (fOaa (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) = 2048047806 :=
  sum_127_of_oct fOaa 2048047806 2048047806 rfl
    (fun a b c ↦ by simp only [fOaa, max3Nat_swap12, sq3Nat_swap12])
    (fun a b c ↦ by simp only [fOaa, max3Nat_swap23, sq3Nat_swap23])
    (p17_comb octOaa 2048047806 octOaa_c0 octOaa_c1a octOaa_c1b octOaa_c2a octOaa_c2b
      octOaa_c3a octOaa_c3b octOaa_c4a octOaa_c4b)
private theorem octInv4_c0 :
    natSum 32 (octShell octInv4) + natSum 32 (fun i ↦ octShell octInv4 (32 + i)) = 13614336 :=
  lemHex179 lemHex16b 6420992 2429312 2041024 2723008 lemHex176
private theorem octInv4_c1a : natSum 12 (fun i ↦ octShell octInv4 (64 + i)) = 1394568 :=
  p17_3x4 lemHex16b 64 411992 463832 518744 lemHex176
private theorem octInv4_c1b : natSum 12 (fun i ↦ octShell octInv4 (76 + i)) = 1916424 :=
  p17_3x4 lemHex16b 76 576728 637784 701912 lemHex176
private theorem octInv4_c2a : natSum 8 (fun i ↦ octShell octInv4 (88 + i)) = 1608496 :=
  p17_4x2 lemHex16b 88 375964 393148 410716 428668 lemHex176
private theorem octInv4_c2b : natSum 8 (fun i ↦ octShell96 octInv4 (0 + i)) = 1901872 :=
  p17_4x2 lemHex16c 0 447004 465724 484828 504316 lemHex177
private theorem octInv4_c3a : natSum 6 (fun i ↦ octShell96 octInv4 (8 + i)) = 1633716 :=
  p17_3x2 lemHex16c 8 524188 544444 565084 lemHex177
private theorem octInv4_c3b : natSum 6 (fun i ↦ octShell96 octInv4 (14 + i)) = 1822932 :=
  p17_3x2 lemHex16c 14 586108 607516 629308 lemHex177
private theorem octInv4_c4a : natSum 6 (fun i ↦ octShell96 octInv4 (20 + i)) = 2022516 :=
  p17_6x1 lemHex16c 20 322946 328538 334178 339866 345602 351386 lemHex177
private theorem octInv4_c4b : natSum 6 (fun i ↦ octShell96 octInv4 (26 + i)) = 2232468 :=
  p17_6x1 lemHex16c 26 357218 363098 369026 375002 381026 387098 lemHex177
theorem sum_fInv4_127 : ∑ ν ∈ nonzeroBox3D (127 : ℤ),
    (fInv4 (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) = 28147328 :=
  sum_127_of_oct fInv4 28147328 28147328 rfl
    (fun a b c ↦ by simp only [fInv4, max3Nat_swap12])
    (fun a b c ↦ by simp only [fInv4, max3Nat_swap23])
    (p17_comb octInv4 28147328 octInv4_c0 octInv4_c1a octInv4_c1b octInv4_c2a octInv4_c2b
      octInv4_c3a octInv4_c3b octInv4_c4a octInv4_c4b)
private theorem octInvSq_c0 :
    natSum 32 (octShell octInvSq) + natSum 32 (fun i ↦ octShell octInvSq (32 + i)) = 1013640730 :=
  lemHex179 (octShell octInvSq) 497763910 257791408 128999260 129086152
private theorem octInvSq_c1a : natSum 12 (fun i ↦ octShell octInvSq (64 + i)) = 193818280 :=
  p17_3x4 (octShell octInvSq) 64 64578356 64605830 64634094
private theorem octInvSq_c1b : natSum 12 (fun i ↦ octShell octInvSq (76 + i)) = 194074876 :=
  p17_3x4 (octShell octInvSq) 76 64659950 64689562 64725364
private theorem octInvSq_c2a : natSum 8 (fun i ↦ octShell octInvSq (88 + i)) = 129552848 :=
  p17_4x2 (octShell octInvSq) 88 32375282 32384682 32392456 32400428
private theorem octInvSq_c2b : natSum 8 (fun i ↦ octShell96 octInvSq (0 + i)) = 129696050 :=
  p17_4x2 (octShell96 octInvSq) 0 32409488 32419202 32428796 32438564
private theorem octInvSq_c3a : natSum 6 (fun i ↦ octShell96 octInvSq (8 + i)) = 97377436 :=
  p17_3x2 (octShell96 octInvSq) 8 32449114 32459256 32469066
private theorem octInvSq_c3b : natSum 6 (fun i ↦ octShell96 octInvSq (14 + i)) = 97473054 :=
  p17_3x2 (octShell96 octInvSq) 14 32479946 32492434 32500674
private theorem octInvSq_c4a : natSum 6 (fun i ↦ octShell96 octInvSq (20 + i)) = 97570630 :=
  p17_6x1 (octShell96 octInvSq) 20 16254808 16257874 16259968 16262882 16265522 16269576
private theorem octInvSq_c4b : natSum 6 (fun i ↦ octShell96 octInvSq (26 + i)) = 97676462 :=
  p17_6x1 (octShell96 octInvSq) 26 16271586 16275312 16276666 16281184 16284610 16287104
theorem sum_fInvSq_127 : ∑ ν ∈ nonzeroBox3D (127 : ℤ),
    (fInvSq (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) = 2050880366 :=
  sum_127_of_oct fInvSq 2050880366 2050880366 rfl
    (fun a b c ↦ by simp only [fInvSq, sq3Nat_swap12])
    (fun a b c ↦ by simp only [fInvSq, sq3Nat_swap23])
    (p17_comb octInvSq 2050880366 octInvSq_c0 octInvSq_c1a octInvSq_c1b octInvSq_c2a
      octInvSq_c2b octInvSq_c3a octInvSq_c3b octInvSq_c4a octInvSq_c4b)
private theorem octLin_c0 :
    natSum 32 (octShell octLin) + natSum 32 (fun i ↦ octShell octLin (32 + i)) = 61628535266 :=
  lemHex179 (octShell octLin) 15152979224 19323586488 12597444820 14554524734
private theorem octLin_c1a : natSum 12 (fun i ↦ octShell octLin (64 + i)) = 25501304046 :=
  p17_3x4 (octShell octLin) 64 8011165534 8500433774 8989704738
private theorem octLin_c1b : natSum 12 (fun i ↦ octShell octLin (76 + i)) = 29904725346 :=
  p17_3x4 (octShell octLin) 76 9478969036 9968241928 10457514382
private theorem octLin_c2a : natSum 8 (fun i ↦ octShell octLin (88 + i)) = 22382844336 :=
  p17_4x2 (octShell octLin) 88 5412234404 5534553292 5656870980 5779185660
private theorem octLin_c2b : natSum 8 (fun i ↦ octShell96 octLin (0 + i)) = 24339935992 :=
  p17_4x2 (octShell96 octLin) 0 5901504580 6023825480 6146143176 6268462756
private theorem octLin_c3a : natSum 6 (fun i ↦ octShell96 octLin (8 + i)) = 19539303418 :=
  p17_3x2 (octShell96 octLin) 8 6390780348 6513099746 6635423324
private theorem octLin_c3b : natSum 6 (fun i ↦ octShell96 octLin (14 + i)) = 20640175722 :=
  p17_3x2 (octShell96 octLin) 14 6757737736 6880060022 7002377964
private theorem octLin_c4a : natSum 6 (fun i ↦ octShell96 octLin (20 + i)) = 21741053726 :=
  p17_6x1 (octShell96 octLin) 20 3547058648 3577638838 3608220230
    3638797304 3669379494 3699959212
private theorem octLin_c4b : natSum 6 (fun i ↦ octShell96 octLin (26 + i)) = 22841942094 :=
  p17_6x1 (octShell96 octLin) 26 3730542222 3761121468 3791699826
    3822277442 3852860510 3883440626
theorem sum_fLin_127 : ∑ ν ∈ nonzeroBox3D (127 : ℤ),
    (fLin (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) = 248519819946 :=
  sum_127_of_oct fLin 248519819946 248519819946 rfl
    (fun a b c ↦ by simp only [fLin, sq3Nat_swap12, show a + b + c = b + a + c by ring])
    (fun a b c ↦ by simp only [fLin, sq3Nat_swap23, show a + b + c = a + c + b by ring])
    (p17_comb octLin 248519819946 octLin_c0 octLin_c1a octLin_c1b octLin_c2a octLin_c2b
      octLin_c3a octLin_c3b octLin_c4a octLin_c4b)
attribute [local irreducible] box3D nonzeroBox3D
theorem nat_le_mul_ceilDiv (N : ℕ) {s : ℕ} (hs : 0 < s) : N ≤ s * ((N + s - 1) / s) := by
  have hmod := Nat.div_add_mod (N + s - 1) s
  have hlt : (N + s - 1) % s < s := Nat.mod_lt _ hs
  omega
theorem forty_two_mul_coarseBoxRadKernel8_eq_fOaa {K : ℕ} (hK : K ≤ 127) {ν : Fin 3 → ℤ}
    (hmem : ν ∈ nonzeroBox3D (K : ℤ)) : 42 * coarseBoxRadKernel8 ν =
    (fOaa (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) / 2 ^ 20 := by
  rcases (mem_nonzeroBox3D (K : ℤ) ν).mp hmem with ⟨hν0, hb⟩
  have hm1 : 1 ≤ maxCoordNatAbs ν := maxCoordNatAbs_pos_of_ne_zero hν0
  have hμ : shellIndex ν = log2Fast127 (maxCoordNatAbs ν) := nat_log_two_eq_log2Fast127 hm1
    ((maxCoordNatAbs_le_of_mem_box3D ((mem_box3D (K : ℤ) ν).mpr hb)).trans hK)
  have hμ6 := log2Fast127_le_six (maxCoordNatAbs ν)
  unfold coarseBoxRadKernel8 fOaa
  rw [← maxCoordNatAbs_eq_max3Nat, ← sumNatAbsSq_eq_sq3Nat, cond_beq_zero_ne (by omega), hμ,
    coarseEnv8Count_eq_coarseRadCeilVal7 hμ6 (sumNatAbsSq_pos_of_ne_zero hν0),
    inv4Val7_eq hμ6, eq_div_iff (by positivity)]
  set μ := log2Fast127 (maxCoordNatAbs ν)
  set q := (coarseRadCeilVal7 μ + sumNatAbsSq ν) / sumNatAbsSq ν
  have hpow : (2 : ℝ) ^ (2 * μ + 8) * (2 : ℝ) ^ (12 - 2 * μ) = 2 ^ 20 := by
    rw [← pow_add]
    exact congrArg _ (by omega)
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 * μ + 8) := by positivity
  push_cast
  calc 42 * ((1 / 42 : ℝ) * (q : ℝ) / (2 : ℝ) ^ (2 * μ + 8)) * 2 ^ 20
      = (q : ℝ) / (2 : ℝ) ^ (2 * μ + 8) * ((2 : ℝ) ^ (2 * μ + 8) * (2 : ℝ) ^ (12 - 2 * μ)) := by
          rw [hpow]
          ring
    _ = (q : ℝ) * (2 : ℝ) ^ (12 - 2 * μ) := by field_simp [h2pos.ne']
theorem inv_four_pow_shellIndex_eq_fInv4 {K : ℕ} (hK : K ≤ 127) {ν : Fin 3 → ℤ}
    (hmem : ν ∈ nonzeroBox3D (K : ℤ)) : (1 : ℝ) / (2 : ℝ) ^ (2 * shellIndex ν) =
    (fInv4 (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) / 2 ^ 12 := by
  rcases (mem_nonzeroBox3D (K : ℤ) ν).mp hmem with ⟨hν0, hb⟩
  have hm1 : 1 ≤ maxCoordNatAbs ν := maxCoordNatAbs_pos_of_ne_zero hν0
  have hμ : shellIndex ν = log2Fast127 (maxCoordNatAbs ν) := nat_log_two_eq_log2Fast127 hm1
    ((maxCoordNatAbs_le_of_mem_box3D ((mem_box3D (K : ℤ) ν).mpr hb)).trans hK)
  have hμ6 := log2Fast127_le_six (maxCoordNatAbs ν)
  unfold fInv4
  rw [← maxCoordNatAbs_eq_max3Nat, cond_beq_zero_ne (by omega), inv4Val7_eq hμ6, hμ,
    eq_div_iff (by positivity)]
  set μ := log2Fast127 (maxCoordNatAbs ν)
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 * μ) := by positivity
  push_cast
  rw [show (2 : ℝ) ^ 12 = (2 : ℝ) ^ (2 * μ) * (2 : ℝ) ^ (12 - 2 * μ) by
      rw [← pow_add]
      exact congrArg _ (by omega)]
  field_simp [h2pos.ne']
theorem inv_sumNatAbsSq_le_fInvSq {ν : Fin 3 → ℤ} (hν : ν ≠ 0) : (1 : ℝ) / (sumNatAbsSq ν : ℝ)
    ≤ (fInvSq (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) / 1048576 := by
  have hs := sumNatAbsSq_pos_of_ne_zero hν
  unfold fInvSq
  rw [← sumNatAbsSq_eq_sq3Nat, cond_beq_zero_ne hs.ne',
    div_le_div_iff₀ (Nat.cast_pos.mpr hs) (by positivity)]
  linarith [show (1048576 : ℝ) ≤ (sumNatAbsSq ν : ℝ) *
    (((1048576 + sumNatAbsSq ν - 1) / sumNatAbsSq ν : ℕ) : ℝ) by
    exact_mod_cast nat_le_mul_ceilDiv 1048576 hs]
theorem natAbsSum_div_sumNatAbsSq_le_fLin {ν : Fin 3 → ℤ} (hν : ν ≠ 0) : (natAbsSum ν : ℝ) /
    (sumNatAbsSq ν : ℝ) ≤ (fLin (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) / 1048576 := by
  have hs := sumNatAbsSq_pos_of_ne_zero hν
  unfold fLin
  rw [← sumNatAbsSq_eq_sq3Nat, show (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs = natAbsSum ν by
      unfold natAbsSum
      rw [Fin.sum_univ_three],
    cond_beq_zero_ne hs.ne', div_le_div_iff₀ (Nat.cast_pos.mpr hs) (by positivity)]
  have hmul : ((natAbsSum ν * 1048576 : ℕ) : ℝ) ≤ (sumNatAbsSq ν : ℝ) *
      (((natAbsSum ν * 1048576 + sumNatAbsSq ν - 1) / sumNatAbsSq ν : ℕ) : ℝ) := by
    exact_mod_cast nat_le_mul_ceilDiv (natAbsSum ν * 1048576) hs
  push_cast at hmul
  linarith
private theorem preOAAProb_eq {M M_box : ℕ} (hM : M ≤ 127) :
    coulombCoarse8PreOAAProb M M_box = (1 / (M_box : ℝ)) *
      ((∑ ν ∈ nonzeroBox3D (M : ℤ), (fOaa (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ)) /
        2 ^ 20) := by
  unfold coulombCoarse8PreOAAProb
  rw [show (42 / (M_box : ℝ)) * ∑ ν ∈ nonzeroBox3D (M : ℤ), coarseBoxRadKernel8 ν =
      (1 / (M_box : ℝ)) * ∑ ν ∈ nonzeroBox3D (M : ℤ), 42 * coarseBoxRadKernel8 ν by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring,
    Finset.sum_congr rfl fun _ hν ↦ forty_two_mul_coarseBoxRadKernel8_eq_fOaa hM hν,
    ← Finset.sum_div]
theorem boost127_coarse8_w13_eq :
    boost127_coarse8_w13 = (2197201569 / 1073741824 : ℝ) ^ 2 := by
  unfold boost127_coarse8_w13
  rw [preOAAProb_eq (M := 127) le_rfl,
    show nonzeroBox3D ((127 : ℕ) : ℤ) = nonzeroBox3D (127 : ℤ) from rfl, sum_fOaa_127]
  norm_num
theorem w13_slot3_slot5_oaa_caps : (17374337 / 8388608 : ℝ) ^ 2 ≤ boost31_coarse8_w13 ∧
    (8343 / 4096 : ℝ) ^ 2 ≤ boost127_coarse8_w13 ∧ boost127_coarse8_w13 ≤ 4285 / 1000 ∧
    boost31_coarse8_w13 ≤ 4290 / 1000 ∧ (8192 * 216 * (2 / 42 : ℝ)) / boost127_coarse8_w13 ≤
    20123 ∧ (2048 * 218 * (2 / 42 : ℝ)) / boost31_coarse8_w13 ≤ 495630 / 100 := by
  have hb31 : boost31_coarse8_w13 = (17374337 / 8388608 : ℝ) ^ 2 := by
    unfold boost31_coarse8_w13
    rw [preOAAProb_eq (M := 31) (by decide),
      show nonzeroBox3D ((31 : ℕ) : ℤ) = nonzeroBox3D (31 : ℤ) from rfl, sum_fOaa_31]
    norm_num
  rw [hb31, boost127_coarse8_w13_eq]
  norm_num
theorem sum_inv_four_pow_shellIndex_127_eq :
    ∑ ν ∈ nonzeroBox3D (127 : ℤ), (1 : ℝ) / (2 : ℝ) ^ (2 * shellIndex ν) = 219901 / 32 := by
  have hcongr : ∑ ν ∈ nonzeroBox3D (127 : ℤ), (1 : ℝ) / (2 : ℝ) ^ (2 * shellIndex ν) =
      (∑ ν ∈ nonzeroBox3D (127 : ℤ), (fInv4 (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ)) /
        2 ^ 12 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun ν hν ↦
      inv_four_pow_shellIndex_eq_fInv4 (K := 127) le_rfl hν
  rw [hcongr, sum_fInv4_127]
  norm_num
theorem sum_inv_sumNatAbsSq_127_le :
    ∑ ν ∈ nonzeroBox3D (127 : ℤ), (1 : ℝ) / (sumNatAbsSq ν : ℝ) ≤ 2050880366 / 1048576 := by
  refine (Finset.sum_le_sum fun ν hν ↦
    inv_sumNatAbsSq_le_fInvSq ((mem_nonzeroBox3D 127 ν).mp hν).1).trans_eq ?_
  rw [← Finset.sum_div, sum_fInvSq_127]
def modWrapCoord (M0 : ℕ) (p ν : ℤ) : ℤ :=
  ((p + ν + (M0 : ℤ)) % (2 * (M0 : ℤ) + 1)) - (M0 : ℤ)
def modFoldCoord (M0 : ℕ) (d : ℤ) : ℤ := modWrapCoord M0 0 d
def modFold3D (M0 : ℕ) (d : Fin 3 → ℤ) : Fin 3 → ℤ := fun w ↦ modFoldCoord M0 (d w)
theorem emod_eq_of_Ico_shift {L x k : ℤ} (hlo : k * L ≤ x) (hhi : x < (k + 1) * L) : x % L = x
    - k * L := by
  rw [show x = (x - k * L) + k * L by ring, Int.add_mul_emod_self_right,
    Int.emod_eq_of_lt (by linarith) (by linarith)]
  ring
theorem modWrapCoord_bounds (M0 : ℕ) (p ν : ℤ) :
    -(M0 : ℤ) ≤ modWrapCoord M0 p ν ∧ modWrapCoord M0 p ν ≤ (M0 : ℤ) := by
  unfold modWrapCoord
  have hL : (0 : ℤ) < 2 * (M0 : ℤ) + 1 := by omega
  have := Int.emod_nonneg (p + ν + (M0 : ℤ)) hL.ne'
  have := Int.emod_lt_of_pos (p + ν + (M0 : ℤ)) hL
  omega
theorem modFoldCoord_eq (M0 : ℕ) {d : ℤ} (hd : -(2 * (M0 : ℤ)) ≤ d ∧ d ≤ 2 * (M0 : ℤ)) :
    modFoldCoord M0 d = if (M0 : ℤ) < d then d - (2 * (M0 : ℤ) + 1) else if d < -(M0 : ℤ) then
    d + (2 * (M0 : ℤ) + 1) else d := by
  unfold modFoldCoord modWrapCoord
  rw [zero_add]
  split_ifs with hgt hlt
  · rw [emod_eq_of_Ico_shift (k := 1) (by omega) (by omega)]
    ring
  · rw [emod_eq_of_Ico_shift (k := -1) (by omega) (by omega)]
    ring
  · rw [emod_eq_of_Ico_shift (k := 0) (by omega) (by omega)]
    ring
theorem modFoldCoord_bounds (M0 : ℕ) (d : ℤ) : -(M0 : ℤ) ≤ modFoldCoord M0 d ∧ modFoldCoord M0
    d ≤ (M0 : ℤ) := modWrapCoord_bounds M0 0 d
theorem modFoldCoord_eq_zero_iff (M0 : ℕ) {d : ℤ}
    (hd : -(2 * (M0 : ℤ)) ≤ d ∧ d ≤ 2 * (M0 : ℤ)) : modFoldCoord M0 d = 0 ↔ d = 0 := by
  rw [modFoldCoord_eq M0 hd]
  split_ifs <;> omega
theorem modFoldCoord_sub_inj_left (M0 : ℕ) {p₁ p₂ q : ℤ}
    (hp₁ : -(M0 : ℤ) ≤ p₁ ∧ p₁ ≤ (M0 : ℤ)) (hp₂ : -(M0 : ℤ) ≤ p₂ ∧ p₂ ≤ (M0 : ℤ))
    (hq : -(M0 : ℤ) ≤ q ∧ q ≤ (M0 : ℤ))
    (heq : modFoldCoord M0 (p₁ - q) = modFoldCoord M0 (p₂ - q)) : p₁ = p₂ := by
  rw [modFoldCoord_eq M0 ⟨by omega, by omega⟩, modFoldCoord_eq M0 ⟨by omega, by omega⟩] at heq
  split_ifs at heq <;> omega
theorem modFoldCoord_sub_inj_right (M0 : ℕ) {p q₁ q₂ : ℤ} (hp : -(M0 : ℤ) ≤ p ∧ p ≤ (M0 : ℤ))
    (hq₁ : -(M0 : ℤ) ≤ q₁ ∧ q₁ ≤ (M0 : ℤ)) (hq₂ : -(M0 : ℤ) ≤ q₂ ∧ q₂ ≤ (M0 : ℤ))
    (heq : modFoldCoord M0 (p - q₁) = modFoldCoord M0 (p - q₂)) : q₁ = q₂ := by
  rw [modFoldCoord_eq M0 ⟨by omega, by omega⟩, modFoldCoord_eq M0 ⟨by omega, by omega⟩] at heq
  split_ifs at heq <;> omega
theorem modFold3D_mem_box3D (M0 : ℕ) (d : Fin 3 → ℤ) : modFold3D M0 d ∈ box3D (M0 : ℤ) := by
  rw [mem_box3D]
  exact fun w ↦ modFoldCoord_bounds M0 (d w)
theorem modFold3D_mem_nonzeroBox3D (M0 : ℕ) {d : Fin 3 → ℤ}
    (hd : d ∈ nonzeroBox3D (2 * (M0 : ℤ))) : modFold3D M0 d ∈ nonzeroBox3D (M0 : ℤ) := by
  rw [mem_nonzeroBox3D] at hd ⊢
  have hbox : d ∈ box3D (2 * (M0 : ℤ)) := (mem_box3D (2 * (M0 : ℤ)) d).mpr hd.2
  refine ⟨fun h0 ↦ hd.1 ?_, (mem_box3D (M0 : ℤ) _).mp (modFold3D_mem_box3D M0 d)⟩
  ext w
  exact (modFoldCoord_eq_zero_iff M0 ((mem_box3D (2 * (M0 : ℤ)) d).mp hbox w)).mp
    (congrFun h0 w)
theorem modFold3D_sub_inj_left (M0 : ℕ) {p₁ p₂ q : Fin 3 → ℤ} (hp₁ : p₁ ∈ box3D (M0 : ℤ))
    (hp₂ : p₂ ∈ box3D (M0 : ℤ)) (hq : q ∈ box3D (M0 : ℤ))
    (heq : modFold3D M0 (p₁ - q) = modFold3D M0 (p₂ - q)) : p₁ = p₂ := by
  ext w
  exact modFoldCoord_sub_inj_left M0 ((mem_box3D _ _).mp hp₁ w)
    ((mem_box3D _ _).mp hp₂ w) ((mem_box3D _ _).mp hq w) (congrFun heq w)
theorem modFold3D_sub_inj_right (M0 : ℕ) {p q₁ q₂ : Fin 3 → ℤ} (hp : p ∈ box3D (M0 : ℤ))
    (hq₁ : q₁ ∈ box3D (M0 : ℤ)) (hq₂ : q₂ ∈ box3D (M0 : ℤ))
    (heq : modFold3D M0 (p - q₁) = modFold3D M0 (p - q₂)) : q₁ = q₂ := by
  ext w
  exact modFoldCoord_sub_inj_right M0 ((mem_box3D _ _).mp hp w)
    ((mem_box3D _ _).mp hq₁ w) ((mem_box3D _ _).mp hq₂ w) (congrFun heq w)
theorem natAbs_modFoldCoord_le (M0 : ℕ) {d : ℤ} (hd : -(2 * (M0 : ℤ)) ≤ d ∧ d ≤ 2 * (M0 : ℤ))
    : (modFoldCoord M0 d).natAbs ≤ d.natAbs := by
  rw [modFoldCoord_eq M0 hd]
  split_ifs <;> omega
theorem sumNatAbsSq_modFold3D_le (M0 : ℕ) {d : Fin 3 → ℤ} (hd : d ∈ box3D (2 * (M0 : ℤ))) :
    sumNatAbsSq (modFold3D M0 d) ≤ sumNatAbsSq d := by
  rw [mem_box3D] at hd
  unfold sumNatAbsSq modFold3D
  exact Finset.sum_le_sum fun w _ ↦ Nat.pow_le_pow_left (natAbs_modFoldCoord_le M0 (hd w)) 2
theorem modFoldCoord_natAbs_cases (M0 : ℕ) {x : ℤ}
    (hx : -(2 * (M0 : ℤ)) ≤ x ∧ x ≤ 2 * (M0 : ℤ)) :
    ((modFoldCoord M0 x).natAbs = x.natAbs ∧ x.natAbs ≤ M0) ∨ (M0 + 1 ≤ x.natAbs ∧ x.natAbs ≤
    2 * M0 ∧ x.natAbs + (modFoldCoord M0 x).natAbs = 2 * M0 + 1) := by
  rw [modFoldCoord_eq M0 hx]
  split_ifs
  · right; exact ⟨by omega, by omega, by omega⟩
  · right; exact ⟨by omega, by omega, by omega⟩
  · left; exact ⟨rfl, by omega⟩
theorem pair_fold_cross_le (M0 : ℕ) {a u b v : ℤ} (ha : (u = a ∧ 0 ≤ a ∧ a ≤ (M0 : ℤ)) ∨ ((M0
    : ℤ) + 1 ≤ a ∧ a ≤ 2 * (M0 : ℤ) ∧ a + u = 2 * (M0 : ℤ) + 1)) (hb : (v = b ∧ 0 ≤ b ∧ b ≤
    (M0 : ℤ)) ∨ ((M0 : ℤ) + 1 ≤ b ∧ b ≤ 2 * (M0 : ℤ) ∧ b + v = 2 * (M0 : ℤ) + 1)) : a * v ^ 2
    + b * u ^ 2 ≤ u * b ^ 2 + v * a ^ 2 := by
  let L : ℤ := 2 * (M0 : ℤ) + 1
  rcases ha with ⟨rfl, ha0, haM⟩ | ⟨ha1, ha2, hau⟩
  · rcases hb with ⟨rfl, hb0, hbM⟩ | ⟨hb1, hb2, hbv⟩
    · linarith
    · linarith [show (u * b ^ 2 + v * u ^ 2) - (u * v ^ 2 + b * u ^ 2) =
        u * (b - v) * ((b + v) - u) by ring,
        mul_nonneg (mul_nonneg ha0 (by omega : 0 ≤ b - v)) (by omega : 0 ≤ (b + v) - u)]
  · rcases hb with ⟨rfl, hb0, hbM⟩ | ⟨hb1, hb2, hbv⟩
    · linarith [show (u * v ^ 2 + v * a ^ 2) - (a * v ^ 2 + v * u ^ 2) =
        v * (a - u) * ((a + u) - v) by ring,
        mul_nonneg (mul_nonneg hb0 (by omega : 0 ≤ a - u)) (by omega : 0 ≤ (a + u) - v)]
    · rw [show u = L - a by omega, show v = L - b by omega]
      linarith [show ((L - a) * b ^ 2 + (L - b) * a ^ 2) - (a * (L - b) ^ 2 + b * (L - a) ^ 2) =
        (a + b - L) * (b * (L - a) + a * (L - b)) by ring,
        mul_nonneg (by omega : (0 : ℤ) ≤ a + b - L)
          (add_nonneg (mul_nonneg (by omega : (0 : ℤ) ≤ b) (by omega : (0 : ℤ) ≤ L - a))
            (mul_nonneg (by omega : (0 : ℤ) ≤ a) (by omega : (0 : ℤ) ≤ L - b)))]
theorem natAbsSum_mul_sumNatAbsSq_modFold3D_le (M0 : ℕ) {d : Fin 3 → ℤ}
    (hd : d ∈ box3D (2 * (M0 : ℤ))) : natAbsSum d * sumNatAbsSq (modFold3D M0 d) ≤ natAbsSum
    (modFold3D M0 d) * sumNatAbsSq d := by
  have hd' := (mem_box3D (2 * (M0 : ℤ)) d).mp hd
  let a : Fin 3 → ℤ := fun w ↦ (d w).natAbs
  let u : Fin 3 → ℤ := fun w ↦ (modFoldCoord M0 (d w)).natAbs
  have hc (w : Fin 3) : (u w = a w ∧ 0 ≤ a w ∧ a w ≤ (M0 : ℤ)) ∨
      ((M0 : ℤ) + 1 ≤ a w ∧ a w ≤ 2 * (M0 : ℤ) ∧ a w + u w = 2 * (M0 : ℤ) + 1) := by
    dsimp only [a, u]
    rcases modFoldCoord_natAbs_cases M0 (hd' w) with ⟨heq, hle⟩ | ⟨h1, h2, hsum⟩
    · exact Or.inl ⟨by exact_mod_cast heq, Nat.cast_nonneg _, by exact_mod_cast hle⟩
    · exact Or.inr ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast hsum⟩
  have hdiag (w : Fin 3) : 0 ≤ a w * u w * (a w - u w) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (sub_nonneg.mpr (Int.ofNat_le.mpr (natAbs_modFoldCoord_le M0 (hd' w))))
  have hmain : (a 0 + a 1 + a 2) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) ≤
      (u 0 + u 1 + u 2) * (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) := by
    linarith [hdiag 0, hdiag 1, hdiag 2, pair_fold_cross_le M0 (hc 0) (hc 1),
      pair_fold_cross_le M0 (hc 0) (hc 2), pair_fold_cross_le M0 (hc 1) (hc 2),
      show (u 0 + u 1 + u 2) * (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) -
        (a 0 + a 1 + a 2) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) =
        a 0 * u 0 * (a 0 - u 0) + a 1 * u 1 * (a 1 - u 1) + a 2 * u 2 * (a 2 - u 2) +
        ((u 0 * a 1 ^ 2 + u 1 * a 0 ^ 2) - (a 0 * u 1 ^ 2 + a 1 * u 0 ^ 2)) +
        ((u 0 * a 2 ^ 2 + u 2 * a 0 ^ 2) - (a 0 * u 2 ^ 2 + a 2 * u 0 ^ 2)) +
        ((u 1 * a 2 ^ 2 + u 2 * a 1 ^ 2) - (a 1 * u 2 ^ 2 + a 2 * u 1 ^ 2)) by ring]
  refine Int.ofNat_le.mp ?_
  unfold natAbsSum sumNatAbsSq modFold3D
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using hmain
theorem norm_le_of_weightedPartialPerm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hRow : ∀ x y₁ y₂, M x y₁ ≠ 0 → M x y₂ ≠ 0 → y₁ = y₂)
    (hCol : ∀ x₁ x₂ y, M x₁ y ≠ 0 → M x₂ y ≠ 0 → x₁ = x₂) (hBound : ∀ x y, ‖M x y‖ ≤ B) : ‖M‖
    ≤ B :=
  norm_le_weightedPartialPerm M hB hRow hCol hBound
theorem operator_sum_apply {d : ℕ} {α : Type*} (s : Finset α) (g : α → Operator d)
    (x y : Fin d) : (∑ c ∈ s, g c) x y = ∑ c ∈ s, g c x y := Matrix.sum_apply x y s g
noncomputable def modWrapRadKernelApprox (B M0 : ℕ) (W_rad w_rad : ℝ) (ν_true : Fin 3 → ℤ) : ℝ
    := W_rad * ((boxRadConst B W_rad w_rad (shellIndex (modFold3D M0 ν_true)) / sumNatAbsSq
    ν_true : ℕ) : ℝ) / (2 : ℝ) ^ (2 * shellIndex (modFold3D M0 ν_true) + B)
noncomputable def dampCoinConst (B_damp : ℕ) (R w_rad : ℝ) : ℕ :=
  ⌊(2 : ℝ) ^ B_damp * (w_rad / 42) / R⌋₊
noncomputable def dampedModWrapKernelApprox (B_rad B_damp M0 : ℕ) (R w_rad : ℝ)
    (ν_true : Fin 3 → ℤ) : ℝ := R * ((dampCoinConst B_damp R w_rad : ℝ) / (2 : ℝ) ^ B_damp) *
    (42 * modWrapRadKernelApprox B_rad M0 (1 / 42) 1 ν_true)
noncomputable def nearestProtonCoord (B_kick : ℕ) (L r : ℝ) : ℤ :=
  ⌊(2 : ℝ) ^ B_kick * (r / L) + 1 / 2⌋
noncomputable def thetaProtonNearest (B_kick : ℕ) (c : Configuration) (l : Fin 216)
    (ν : Fin 3 → ℤ) : ℝ := -2 * π * ∑ w : Fin 3, (ν w : ℝ) * ((nearestProtonCoord B_kick
    (cellVolume ^ (1 / 3 : ℝ)) (c.nuclei l w) : ℝ) / (2 : ℝ) ^ B_kick)
noncomputable def quantizedStructureFactorNearest (B_kick : ℕ) (c : Configuration)
    (ν : Fin 3 → ℤ) : ℂ :=
  ∑ l : Fin 216, Complex.exp ((thetaProtonNearest B_kick c l ν : ℂ) * Complex.I)
open Classical in
noncomputable def modWrapProjNucOp (c : Configuration) (B_rad B_damp B_kick : ℕ)
    (R_3 wt_3 : ℝ) : Operator (2 ^ systemQubits) := Matrix.of fun x y ↦ if IsGridState x ∧
    IsGridState y ∧ (∀ b ≠ Particle.projectile, momentum x b = momentum y b) then (wt_3 : ℂ) *
    quantizedStructureFactorNearest B_kick c (momentum x .projectile - momentum y .projectile)
    * (dampedModWrapKernelApprox B_rad B_damp 127 R_3 2 (momentum x .projectile - momentum y
    .projectile) : ℂ) else 0
theorem dampedModWrapKernelApprox_zero (B_rad B_damp M0 : ℕ) (R w_rad : ℝ) :
    dampedModWrapKernelApprox B_rad B_damp M0 R w_rad 0 = 0 := by
  simp [dampedModWrapKernelApprox, modWrapRadKernelApprox, sumNatAbsSq]
theorem dampedModWrapKernelApprox_bounds (B_rad B_damp M0 : ℕ) {R w_rad : ℝ}
    (hR : 0 < R) (hw : 0 ≤ w_rad) {ν_true : Fin 3 → ℤ} (hν : ν_true ≠ 0) :
    0 ≤ dampedModWrapKernelApprox B_rad B_damp M0 R w_rad ν_true ∧
      dampedModWrapKernelApprox B_rad B_damp M0 R w_rad ν_true ≤ w_rad * coulombKernel ν_true ∧
      w_rad * coulombKernel ν_true - dampedModWrapKernelApprox B_rad B_damp M0 R w_rad ν_true ≤
        (w_rad / 42) / (2 : ℝ) ^ (2 * shellIndex (modFold3D M0 ν_true) + B_rad) +
          R / (2 : ℝ) ^ B_damp * (42 * coulombKernel ν_true) := by
  set μ : ℕ := shellIndex (modFold3D M0 ν_true)
  set S : ℕ := sumNatAbsSq ν_true
  have hS_pos : 0 < S := sumNatAbsSq_pos_of_ne_zero hν
  have hSR_pos : (0 : ℝ) < (S : ℝ) := Nat.cast_pos.mpr hS_pos
  have h2r_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * μ + B_rad) := by positivity
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ B_damp := by positivity
  have hpi : (0 : ℝ) < π * cellVolume ^ (1 / 3 : ℝ) := by
    linarith [pi_mul_cellVolume_rpow_bounds.1]
  set X : ℝ := (2 : ℝ) ^ (2 * μ + B_rad) * 1 / ((1 / 42 : ℝ) * (π * cellVolume ^ (1 / 3 : ℝ)))
  set C : ℕ := ⌊X⌋₊
  have h_id : (1 / 42 : ℝ) * (X / (S : ℝ)) / (2 : ℝ) ^ (2 * μ + B_rad) = coulombKernel ν_true := by
    rw [coulombKernel_eq_sumNatAbsSq]
    dsimp [X, S]
    field_simp [h2r_pos.ne', hSR_pos.ne', hpi.ne']
  have hdiv_real : ((C / S : ℕ) : ℝ) ≤ X / (S : ℝ) :=
    (le_div_iff₀ hSR_pos).mpr ((by exact_mod_cast Nat.div_mul_le_self C S :
      ((C / S : ℕ) : ℝ) * (S : ℝ) ≤ (C : ℝ)).trans (Nat.floor_le (by positivity)))
  have hrad_le : modWrapRadKernelApprox B_rad M0 (1 / 42) 1 ν_true ≤ coulombKernel ν_true := by
    unfold modWrapRadKernelApprox boxRadConst
    change (1 / 42 : ℝ) * ((C / S : ℕ) : ℝ) / (2 : ℝ) ^ (2 * μ + B_rad) ≤ coulombKernel ν_true
    rw [← h_id]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv_real (by norm_num)) h2r_pos.le
  have hC_succ : (C : ℝ) + 1 ≤ (((C / S : ℕ) : ℝ) + 1) * (S : ℝ) := by
    exact_mod_cast (show C + 1 ≤ (C / S + 1) * S by
      have h1 := Nat.div_add_mod C S
      have h2 := Nat.mod_lt C hS_pos
      have h3 : (C / S + 1) * S = S * (C / S) + S := by ring
      omega)
  have hdiff : X / (S : ℝ) - ((C / S : ℕ) : ℝ) ≤ 1 := by
    linarith [(div_le_iff₀ hSR_pos).mpr ((Nat.lt_floor_add_one X).le.trans hC_succ)]
  have hrad_err : coulombKernel ν_true - modWrapRadKernelApprox B_rad M0 (1 / 42) 1 ν_true ≤
      (1 / 42 : ℝ) / (2 : ℝ) ^ (2 * μ + B_rad) := by
    unfold modWrapRadKernelApprox boxRadConst
    rw [← h_id, show (1 / 42 : ℝ) * (X / (S : ℝ)) / (2 : ℝ) ^ (2 * μ + B_rad) -
        (1 / 42 : ℝ) * ((⌊X⌋₊ / S : ℕ) : ℝ) / (2 : ℝ) ^ (2 * μ + B_rad) =
        (1 / 42 : ℝ) * (X / (S : ℝ) - ((C / S : ℕ) : ℝ)) / (2 : ℝ) ^ (2 * μ + B_rad) by ring]
    simpa only [mul_one] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdiff (by norm_num : (0 : ℝ) ≤ 1 / 42)) h2r_pos.le
  set Y : ℝ := (2 : ℝ) ^ B_damp * (w_rad / 42) / R
  have hY_id : R * (Y / (2 : ℝ) ^ B_damp) = w_rad / 42 := by
    dsimp [Y]
    field_simp [hR.ne', h2d_pos.ne']
  have hd_le : R * ((dampCoinConst B_damp R w_rad : ℝ) / (2 : ℝ) ^ B_damp) ≤ w_rad / 42 := by
    unfold dampCoinConst
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Nat.floor_le (by positivity)) h2d_pos.le) hR.le).trans_eq hY_id
  have hd_err : (w_rad / 42) - R * ((dampCoinConst B_damp R w_rad : ℝ) / (2 : ℝ) ^ B_damp) ≤
      R / (2 : ℝ) ^ B_damp := by
    unfold dampCoinConst
    calc (w_rad / 42) - R * ((⌊Y⌋₊ : ℝ) / (2 : ℝ) ^ B_damp)
        = R * (Y / (2 : ℝ) ^ B_damp) - R * ((⌊Y⌋₊ : ℝ) / (2 : ℝ) ^ B_damp) := by rw [hY_id]
      _ = R * ((Y - (⌊Y⌋₊ : ℝ)) / (2 : ℝ) ^ B_damp) := by ring
      _ ≤ R * (1 / (2 : ℝ) ^ B_damp) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (by linarith [Nat.lt_floor_add_one Y]) h2d_pos.le) hR.le
      _ = R / (2 : ℝ) ^ B_damp := by ring
  refine ⟨by
      unfold dampedModWrapKernelApprox modWrapRadKernelApprox
      positivity, ?_, ?_⟩
  · unfold dampedModWrapKernelApprox
    calc R * ((dampCoinConst B_damp R w_rad : ℝ) / (2 : ℝ) ^ B_damp) *
            (42 * modWrapRadKernelApprox B_rad M0 (1 / 42) 1 ν_true)
        ≤ (w_rad / 42) * (42 * coulombKernel ν_true) :=
          mul_le_mul hd_le (mul_le_mul_of_nonneg_left hrad_le (by norm_num))
            (by
              unfold modWrapRadKernelApprox
              positivity) (by positivity)
      _ = w_rad * coulombKernel ν_true := by ring
  · unfold dampedModWrapKernelApprox
    set D : ℝ := R * ((dampCoinConst B_damp R w_rad : ℝ) / (2 : ℝ) ^ B_damp)
    set K : ℝ := modWrapRadKernelApprox B_rad M0 (1 / 42) 1 ν_true
    have hsplit : w_rad * coulombKernel ν_true - D * (42 * K) =
        ((w_rad / 42) - D) * (42 * coulombKernel ν_true) +
          D * (42 * (coulombKernel ν_true - K)) := by ring
    rw [hsplit]
    have h1 : ((w_rad / 42) - D) * (42 * coulombKernel ν_true) ≤
        (R / (2 : ℝ) ^ B_damp) * (42 * coulombKernel ν_true) :=
      mul_le_mul_of_nonneg_right hd_err (mul_nonneg (by norm_num) (coulombKernel_nonneg _))
    have h2 : D * (42 * (coulombKernel ν_true - K)) ≤
        (w_rad / 42) * (42 * ((1 / 42 : ℝ) / (2 : ℝ) ^ (2 * μ + B_rad))) :=
      mul_le_mul hd_le (mul_le_mul_of_nonneg_left hrad_err (by norm_num))
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hrad_le)) (by positivity)
    linarith [show (w_rad / 42) * (42 * ((1 / 42 : ℝ) / (2 : ℝ) ^ (2 * μ + B_rad))) =
      (w_rad / 42) / (2 : ℝ) ^ (2 * μ + B_rad) by ring]
theorem norm_exp_ofReal_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  let θ : ℝ := a - b
  have hfac : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp ((θ : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    dsimp [θ]
    push_cast
    ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = 2 * (1 - Real.cos θ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.exp_ofReal_mul_I]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
      add_zero, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add,
      Complex.one_im]
    linarith [Real.sin_sq_add_cos_sq θ]
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (abs_nonneg _)).mpr
    (by nlinarith [one_sub_sq_div_two_le_cos θ, sq_abs θ])
theorem projectile_momentum_mem_box3D (x : Fin (2 ^ systemQubits)) :
    momentum x .projectile ∈ box3D 127 := by
  rw [mem_box3D]
  intro w
  dsimp [momentum, signMagnitude, componentBits, projectileBits]
  set s := x.val / 2 ^ bitOffset .projectile w / 128 % 2
  set m := x.val / 2 ^ bitOffset .projectile w % 128
  have hs : s = 0 ∨ s = 1 := by omega
  have hm : m ≤ 127 := by omega
  rcases hs with h | h <;> rw [h] <;> simp <;> omega
theorem projectile_sub_mem_box3D_254 (x y : Fin (2 ^ systemQubits)) :
    momentum x .projectile - momentum y .projectile ∈ box3D (2 * (127 : ℤ)) :=
  (mem_box3D _ _).mpr fun w ↦ by
    have := (mem_box3D 127 _).mp (projectile_momentum_mem_box3D x) w
    have := (mem_box3D 127 _).mp (projectile_momentum_mem_box3D y) w
    change -(2 * (127 : ℤ)) ≤ momentum x .projectile w - momentum y .projectile w ∧
      momentum x .projectile w - momentum y .projectile w ≤ 2 * (127 : ℤ)
    omega
theorem norm_projector_sandwich_le {d : ℕ} [NeZero d] (P D : Operator d)
    (hHerm : P.IsHermitian) (hIdem : P * P = P) : ‖P * D * P‖ ≤ ‖D‖ ∧ ‖D * P‖ ≤ ‖D‖ := by
  have hP : ‖P‖ ≤ 1 := norm_projector_le_one P hHerm hIdem
  have hDP : ‖D * P‖ ≤ ‖D‖ := (norm_mul_le D P).trans (mul_le_of_le_one_right (norm_nonneg D) hP)
  exact ⟨by
    rw [Matrix.mul_assoc]
    exact (norm_mul_le P (D * P)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hP).trans hDP), hDP⟩
theorem norm_fermionicProjector_sandwich_le (spinUp : Finset (Fin numElectrons))
    (D : Operator (2 ^ systemQubits)) : ‖fermionicProjector spinUp * D * fermionicProjector
    spinUp‖ ≤ ‖D‖ ∧ ‖D * fermionicProjector spinUp‖ ≤ ‖D‖ := norm_projector_sandwich_le
    (fermionicProjector spinUp) D
    (BridgeFermionicComm.SpecInner.fermionicProjector_isHermitian spinUp)
    (BridgeFermionicComm.SpecInner.fermionicProjector_idem spinUp)
end ModWrapCoarse8PureMomentum
end
end ModModWrapCoarse8PureMomentum

section ModStoppingPowerSubspaceInvariance
@[expose] public section
namespace SpecsAux
open Operator Matrix SpecsAux.SpecMirror
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open Classical in
noncomputable def gridProjector : Operator (2 ^ systemQubits) :=
  Matrix.diagonal fun x ↦ if IsGridState x then 1 else 0
@[simp] theorem mem_gridStates_iff (x : Fin (2 ^ systemQubits)) :
    x ∈ gridStates ↔ IsGridState x := by
  simp [gridStates]
theorem gridProjector_isHermitian : gridProjector.IsHermitian := by
  rw [Matrix.IsHermitian, gridProjector, Matrix.diagonal_conjTranspose]
  exact congrArg _ (funext fun x ↦ by by_cases hx : IsGridState x <;> simp [hx])
@[simp] theorem gridProjector_conjTranspose : gridProjectorᴴ = gridProjector :=
  gridProjector_isHermitian.eq
@[simp] theorem gridProjector_mul_self : gridProjector * gridProjector = gridProjector := by
  rw [gridProjector, Matrix.diagonal_mul_diagonal]
  exact congrArg _ (funext fun x ↦ by by_cases hx : IsGridState x <;> simp [hx])
theorem mul_gridProjector_of_supported_on_gridStates {M : Operator (2 ^ systemQubits)}
    (hM : ∀ x y, ¬(IsGridState x ∧ IsGridState y) → M x y = 0) : M * gridProjector = M := by
  ext x y
  rw [gridProjector, Matrix.mul_diagonal]
  by_cases hy : IsGridState y
  · simp [hy]
  · simp [hy, hM x y fun h ↦ hy h.2]
theorem gridProjector_mul_of_supported_on_gridStates {M : Operator (2 ^ systemQubits)}
    (hM : ∀ x y, ¬(IsGridState x ∧ IsGridState y) → M x y = 0) : gridProjector * M = M := by
  ext x y
  rw [gridProjector, Matrix.diagonal_mul]
  by_cases hx : IsGridState x
  · simp [hx]
  · simp [hx, hM x y fun h ↦ hx h.1]
theorem commute_gridProjector_of_supported_on_gridStates {M : Operator (2 ^ systemQubits)}
    (hM : ∀ x y, ¬(IsGridState x ∧ IsGridState y) → M x y = 0) : Commute M gridProjector := by
  rw [Commute, SemiconjBy, mul_gridProjector_of_supported_on_gridStates hM,
    gridProjector_mul_of_supported_on_gridStates hM]
theorem fermionicProjector_eq_zero_of_not_grid (spinUp : Finset (Fin numElectrons))
    (x y : Fin (2 ^ systemQubits)) (h : ¬(IsGridState x ∧ IsGridState y)) :
    fermionicProjector spinUp x y = 0 := by simp [fermionicProjector, h]
@[simp] theorem fermionicProjector_mul_gridProjector (spinUp : Finset (Fin numElectrons)) :
    fermionicProjector spinUp * gridProjector = fermionicProjector spinUp :=
  mul_gridProjector_of_supported_on_gridStates (fermionicProjector_eq_zero_of_not_grid spinUp)
@[simp] theorem gridProjector_mul_fermionicProjector (spinUp : Finset (Fin numElectrons)) :
    gridProjector * fermionicProjector spinUp = fermionicProjector spinUp :=
  gridProjector_mul_of_supported_on_gridStates (fermionicProjector_eq_zero_of_not_grid spinUp)
theorem commute_fermionicProjector_gridProjector (spinUp : Finset (Fin numElectrons)) :
    Commute (fermionicProjector spinUp) gridProjector :=
  commute_gridProjector_of_supported_on_gridStates (fermionicProjector_eq_zero_of_not_grid spinUp)
theorem hamiltonian_eq_zero_of_not_grid (c : Configuration) (x y : Fin (2 ^ systemQubits))
    (h : ¬(IsGridState x ∧ IsGridState y)) : hamiltonian c x y = 0 := by simp [hamiltonian, h]
@[simp] theorem hamiltonian_mul_gridProjector (c : Configuration) :
    hamiltonian c * gridProjector = hamiltonian c :=
  mul_gridProjector_of_supported_on_gridStates (hamiltonian_eq_zero_of_not_grid c)
@[simp] theorem gridProjector_mul_hamiltonian (c : Configuration) :
    gridProjector * hamiltonian c = hamiltonian c :=
  gridProjector_mul_of_supported_on_gridStates (hamiltonian_eq_zero_of_not_grid c)
@[simp] theorem stepVector_zero : waveVector 0 = 0 := funext fun _ ↦ by simp [waveVector]
@[simp] theorem stepVector_neg (ν : Fin 3 → ℤ) : waveVector (-ν) = -waveVector ν :=
  funext fun _ ↦ by simp [waveVector, neg_div]
@[simp] theorem stepNumberSq_zero : waveNumberSq 0 = 0 := by simp [waveNumberSq]
@[simp] theorem stepNumberSq_neg (ν : Fin 3 → ℤ) : waveNumberSq (-ν) = waveNumberSq ν := by
  simp [waveNumberSq]
@[simp] theorem coulombKernel_zero : coulombKernel 0 = 0 := by simp [coulombKernel]
@[simp] theorem coulombKernel_neg (ν : Fin 3 → ℤ) : coulombKernel (-ν) = coulombKernel ν := by
  simp [coulombKernel]
theorem fermionicProjector_isHermitian (spinUp : Finset (Fin numElectrons)) :
    (fermionicProjector spinUp).IsHermitian :=
  BridgeFermionicComm.SpecInner.fermionicProjector_isHermitian spinUp
end SpecsAux
end
end ModStoppingPowerSubspaceInvariance

section ModSParameterizedSchedule
@[expose] public section
namespace SpecsAux
open Operator Matrix SpecsAux.SpecMirror
open scoped Matrix BigOperators Matrix.Norms.L2Operator
@[simp] theorem count_repeat_seq_identity {Var : Type} {n a : ℕ} (g : PrimitiveGate a)
    (dSeg : DynamicCircuit Var n) (k : ℕ) :
    (Nat.repeat (.seq dSeg) k DynamicCircuit.identity).count g = k * dSeg.count g := by
  induction k with
  | zero => simp [Nat.repeat]
  | succ k ih =>
      simp only [Nat.repeat, DynamicCircuit.count, ih]
      ring
end SpecsAux
end
end ModSParameterizedSchedule

section ModRegimeAAdaptiveSchedule
@[expose] public section
namespace SpecsAux
open Operator Matrix QProg Circuit SpecsAux.SpecMirror BridgeFermionicComm
open scoped Matrix BigOperators Matrix.Norms.L2Operator
def runScheduleCircuitAdaptive {Var : Type} {n : ℕ} (R : Fin 10 → ℕ)
    (dInit : DynamicCircuit Var n) (dSeg : Fin 10 → DynamicCircuit Var n)
    (dUninit : DynamicCircuit Var n) (j : Fin 10) : DynamicCircuit Var n :=
  .seq dInit (.seq (Nat.repeat (.seq (dSeg j)) (R j) .identity) dUninit)
theorem count_runScheduleCircuitAdaptive {Var : Type} {n a : ℕ} (g : PrimitiveGate a)
    (R : Fin 10 → ℕ) (dInit : DynamicCircuit Var n)
    (dSeg : Fin 10 → DynamicCircuit Var n) (dUninit : DynamicCircuit Var n) (j : Fin 10) :
    (runScheduleCircuitAdaptive R dInit dSeg dUninit j).count g =
      dInit.count g + R j * (dSeg j).count g + dUninit.count g := by
  simp only [runScheduleCircuitAdaptive, DynamicCircuit.count, count_repeat_seq_identity]
  ring
end SpecsAux
end
end ModRegimeAAdaptiveSchedule

end QuantumComputation.Specs.StoppingPowerSolution
