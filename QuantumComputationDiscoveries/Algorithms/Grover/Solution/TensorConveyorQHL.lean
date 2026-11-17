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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PipelinedFuseWarmR1
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.DeflateFunctor
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.StageLoop
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.TensorConveyorCertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.TensorConveyorBasis2d
public import QuantumComputation.Maths.Tsum
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Coherent Multi-Register `TensorConveyor` QHL Harvester & Bellman Engine
(`TensorConveyorQHL`)

Formalizes the `m`-parallel `d`-register (`d ≤ 12`) coherent `TensorConveyor` stage harvester,
the `d`-round swap-verification readout, the Born `L1` product perturbation and fiber-uniform
coupon-occupancy reduction to `TensorConveyorCertDefs`, and the generic Cold-Tail Bellman
stage
splice `tcCellCircuitAt` over any ambient qubit count `Q ≥ tcMinQubits n m k`.
-/

section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

section
open Operator
open scoped InnerProductSpace
private theorem qcExpectEqTsumStore {Var : Type} {d : ℕ}
    (Δ : CQState (Store Var) d) (θ : CQAssertion (Store Var) d) :
    expect Δ θ = ∑' σ : Store Var, ⟪(θ σ).1, (Δ.1 σ).1⟫_ℝ :=
  rfl
end

section
open Operator QProg
open scoped Matrix
private theorem wp_measureRegister_coe {Var : Type} [DecidableEq Var] {n k : ℕ}
    (res : Var) (r : QRegister k n) (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) :
    (wp (QProg.measureRegister res r) Θ σ).1 =
      ∑ o : Fin (2 ^ k),
        HermitianMat.conj (r.basisOutcomeProjector o)ᴴ
          (Θ (Store.subst σ res ↑o.val)).1 :=
  rfl
end

@[expose] public section

open Store (Expr)

namespace QuantumComputation.Specs.GroverFindAll

open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal InnerProductSpace QHLExpectation
open QuantumComputation.Specs.GroverFindAll.PipeFuseCert
open QuantumComputation.Specs.GroverFindAll.TensorConveyorCert

/-- Standard `+ 12 * m * n` ancilla budget for standalone `TensorConveyor` (`m ≥ 1`). -/
def tensorConveyorQubits (n m k : ℕ) : ℕ :=
  findAllQubits n m k + 12 * m * n

/-- Minimum ambient qubit width required by a `TensorConveyor` cell `(n, m, k)` (`d ≤ 12`). -/
def tcMinQubits (n m k : ℕ) : ℕ :=
  max (findAllQubits n m k) ((n + 1) * m + 12 * m * n + 1)

theorem findAllQubits_le_tcMinQubits (n m k : ℕ) :
    findAllQubits n m k ≤ tcMinQubits n m k :=
  le_max_left _ _

theorem tcStageBound_le_tcMinQubits (n m k : ℕ) :
    (n + 1) * m + 12 * m * n + 1 ≤ tcMinQubits n m k :=
  le_max_right _ _

theorem findAllQubits_le_tensorConveyorQubits (n m k : ℕ) :
    findAllQubits n m k ≤ tensorConveyorQubits n m k :=
  Nat.le_add_right _ _

theorem tcMinQubits_le_tensorConveyorQubits (n m k : ℕ) :
    tcMinQubits n m k ≤ tensorConveyorQubits n m k := by
  unfold tcMinQubits tensorConveyorQubits findAllQubits
  exact max_le (by omega) (by omega)

theorem tcMinQubits_m1_le_findAllQubits {n k : ℕ} (hk : 12 ≤ k) :
    tcMinQubits n 1 k ≤ findAllQubits n 1 k := by
  unfold tcMinQubits findAllQubits
  refine max_le le_rfl ?_
  have hnk : 12 * 1 * n ≤ n * k := by
    calc 12 * 1 * n = n * 12 := by ring
      _ ≤ n * k := Nat.mul_le_mul_left n hk
  omega

/-- Low `Q₀`-qubit prefix subregister `0.. Q₀ - 1` inside `Q` qubits (`Q₀ ≤ Q`). -/
def tcLowBlockReg {Q₀ Q : ℕ} (hQ : Q₀ ≤ Q) : QRegister Q₀ Q :=
  QRegister.block 0 Q₀ (by omega)

/-- Global-phase guard ensuring `0` step cost under `CostModel.ofEmbeddedOracle`. -/
noncomputable def tcEnsureImagUnitary {d : ℕ} [NeZero d] (M : Unitary d) : Unitary d :=
  open Classical in
  if IsRealMatrix M.1 then phaseI M else M

theorem cqState_qAssign_tcEnsureImagUnitary {Var : Type} {d : ℕ} [NeZero d] (M : Unitary d)
    (Δ : CQState (Store Var) d) :
    CQState.qAssign (tcEnsureImagUnitary M) Δ = CQState.qAssign M Δ := by
  dsimp only [tcEnsureImagUnitary]
  split_ifs
  · exact cqState_qAssign_phaseI M Δ
  · rfl

theorem unitaryCost_tcEnsureImagUnitary_eq_zero {Q w : ℕ} {oracle : Unitary (2 ^ w)}
    (horacle : IsRealMatrix oracle.1) (M : Unitary (2 ^ Q)) :
    (CostModel.ofEmbeddedOracle (n := Q) oracle).unitaryCost (tcEnsureImagUnitary M) = 0 := by
  dsimp only [tcEnsureImagUnitary]
  split_ifs with hreal
  · exact ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacle hreal
  · simp only [CostModel.ofEmbeddedOracle, ite_eq_right_iff]
    rintro ⟨reg, hM⟩
    exfalso
    apply hreal
    rw [congrArg Subtype.val hM]
    exact isRealMatrix_embedMatrix reg horacle

/-- Functorial low-register circuit lift from `Q₀` to `Q` (`Q₀ ≤ Q`) at zero step cost. -/
noncomputable def tcLiftCircLow {Var : Type} {Q₀ Q w : ℕ} (hQ : Q₀ ≤ Q) :
    OracleDynamicCircuit (Unitary (2 ^ Q₀)) Var Q₀ w →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w
  | .skip => .skip
  | .step U => .step (tcEnsureImagUnitary ((tcLowBlockReg hQ).embedUnitary U))
  | .oracle reg => .oracle ((tcLowBlockReg hQ).compose reg)
  | .measure x reg => .measure x ((tcLowBlockReg hQ).compose reg)
  | .seq c₁ c₂ => .seq (tcLiftCircLow hQ c₁) (tcLiftCircLow hQ c₂)
  | @OracleDynamicCircuit.qIf _ _ _ _ b dec c₁ c₂ =>
      @OracleDynamicCircuit.qIf _ _ _ _ b dec (tcLiftCircLow hQ c₁) (tcLiftCircLow hQ c₂)
  | @OracleDynamicCircuit.qWhile _ _ _ _ b dec body =>
      @OracleDynamicCircuit.qWhile _ _ _ _ b dec (tcLiftCircLow hQ body)

/-- Rectangular clean-ancilla isometry `|z₀⟩ ↦ |z₀⟩ ⊗ |0⟩` along `r: QRegister Q₀ Q`. -/
noncomputable def tcLowPadIso {Q₀ Q : ℕ} (r : QRegister Q₀ Q) :
    Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q₀)) ℂ :=
  Matrix.of fun z z₀ ↦ if r.basisSplitEquiv z = (z₀, 0) then 1 else 0

theorem tcLowPadIso_conjTranspose_mul_self {Q₀ Q : ℕ} (r : QRegister Q₀ Q) :
    (tcLowPadIso r)ᴴ * tcLowPadIso r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply,
    Finset.sum_eq_single (r.basisSplitEquiv.symm (a, 0))]
  · simp [tcLowPadIso, Prod.mk.injEq]
  · intro z _ hne
    have hsplit : r.basisSplitEquiv z ≠ (a, 0) :=
      fun h ↦ hne (r.basisSplitEquiv.eq_symm_apply.2 h)
    simp [tcLowPadIso, hsplit]
  · intro habs; exact (habs (Finset.mem_univ _)).elim

theorem embedMatrix_mul_tcLowPadIso {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (M : Matrix (Fin (2 ^ Q₀)) (Fin (2 ^ Q₀)) ℂ) :
    r.embedMatrix M * tcLowPadIso r = tcLowPadIso r * M := by
  ext z z₀
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single (r.basisSplitEquiv.symm (z₀, 0))]
  · have hu_fst : r.extractIndex (r.basisSplitEquiv.symm (z₀, 0)) = z₀ := by
      rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    simp only [QRegister.embedMatrix_apply, tcLowPadIso, Matrix.of_apply, Equiv.apply_symm_apply,
      ↓reduceIte, mul_one, hu_fst]
    by_cases henv : (r.basisSplitEquiv z).2 = 0
    · rw [ite_eq_left henv, mul_one, Finset.sum_eq_single (r.extractIndex z)]
      · have hsplit : r.basisSplitEquiv z = (r.extractIndex z, 0) :=
          Prod.ext (r.basisSplitEquiv_apply_fst z) henv
        simp [hsplit]
      · intro v₀ _ hne
        have hsplit : r.basisSplitEquiv z ≠ (v₀, 0) := fun h ↦
          hne (by rw [← QRegister.basisSplitEquiv_apply_fst, h])
        simp [hsplit]
      · intro habs; exact (habs (Finset.mem_univ _)).elim
    · rw [ite_eq_right henv, mul_zero, eq_comm]
      refine Finset.sum_eq_zero fun v₀ _ ↦ ?_
      have hsplit : r.basisSplitEquiv z ≠ (v₀, 0) := fun h ↦ henv (congrArg Prod.snd h)
      simp [hsplit]
  · intro u _ hne
    have hsplit : r.basisSplitEquiv u ≠ (z₀, 0) :=
      fun h ↦ hne (r.basisSplitEquiv.eq_symm_apply.2 h)
    simp [tcLowPadIso, hsplit]
  · intro habs; exact (habs (Finset.mem_univ _)).elim

theorem trace_conj_tcLowPadIso {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (A : HermitianMat (Fin (2 ^ Q₀)) ℂ) :
    (A.conj (tcLowPadIso r)).trace = A.trace := by
  rw [HermitianMat.trace_eq_re_trace, HermitianMat.trace_eq_re_trace, HermitianMat.conj_apply_mat,
    Matrix.trace_mul_comm _ (tcLowPadIso r)ᴴ, ← Matrix.mul_assoc,
    tcLowPadIso_conjTranspose_mul_self, Matrix.one_mul]

/-- Partial-density-operator clean-ancilla embedding along `r: QRegister Q₀ Q`. -/
noncomputable def tcPadPDO {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (ρ : 𝒟 (Fin (2 ^ Q₀))) :
    𝒟 (Fin (2 ^ Q)) :=
  ⟨ρ.1.conj (tcLowPadIso r), ρ.1.conj_nonneg _ ρ.2.1,
    (trace_conj_tcLowPadIso r ρ.1).trans_le ρ.2.2⟩

/-- Monotone order-homomorphism wrapper around `tcPadPDO`. -/
noncomputable def tcPadPDOOrderHom {Q₀ Q : ℕ} (r : QRegister Q₀ Q) :
    𝒟 (Fin (2 ^ Q₀)) →o 𝒟 (Fin (2 ^ Q)) where
  toFun := tcPadPDO r
  monotone' _ _ h := HermitianMat.conj_mono h

theorem tcPadPDO_ωSup {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (ch : OmegaCompletePartialOrder.Chain (𝒟 (Fin (2 ^ Q₀)))) :
    tcPadPDO r (OmegaCompletePartialOrder.ωSup ch) =
      OmegaCompletePartialOrder.ωSup (ch.map (tcPadPDOOrderHom r)) := by
  have hcont : Continuous (tcPadPDO r) :=
    Continuous.subtype_mk
      ((HermitianMat.continuous_conj_right (tcLowPadIso r)).comp continuous_subtype_val) _
  exact tendsto_nhds_unique
    ((hcont.tendsto _).comp (OmegaCompletePartialOrder.tendsto_ωSup ch))
    (OmegaCompletePartialOrder.tendsto_ωSup (ch.map (tcPadPDOOrderHom r)))

/-- `CQState` clean-ancilla embedding along `r: QRegister Q₀ Q`. -/
noncomputable def tcPadStateLow {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (Δ₀ : CQState (Store Var) (2 ^ Q₀)) : CQState (Store Var) (2 ^ Q) :=
  ⟨fun σ ↦ tcPadPDO r (Δ₀.1 σ), by
    have h : (fun σ ↦ (tcPadPDO r (Δ₀.1 σ)).trace) = fun σ ↦ (Δ₀.1 σ).trace :=
      funext fun σ ↦ Subtype.ext (trace_conj_tcLowPadIso r (Δ₀.1 σ).1)
    exact ⟨Δ₀.trace, h ▸ Δ₀.hasSum_trace, Δ₀.trace_le_one⟩⟩

@[simp]
theorem trace_tcPadStateLow {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (Δ₀ : CQState (Store Var) (2 ^ Q₀)) :
    (tcPadStateLow r Δ₀).trace = Δ₀.trace := by
  apply NNReal.eq
  rw [CQState.coe_trace_eq_tsum, CQState.coe_trace_eq_tsum]
  exact tsum_congr fun σ ↦ trace_conj_tcLowPadIso r (Δ₀.1 σ).1

@[simp]
theorem stateMass_tcPadStateLow {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (Δ₀ : CQState (Store Var) (2 ^ Q₀)) :
    stateMass (tcPadStateLow r Δ₀) = stateMass Δ₀ := by
  rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, trace_tcPadStateLow]

theorem tcPadStateLow_trueState {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (b : Store Var → Prop) [DecidablePred b] (Δ₀ : CQState (Store Var) (2 ^ Q₀)) :
    CQState.cqTrueSt b (tcPadStateLow r Δ₀) = tcPadStateLow r (CQState.cqTrueSt b Δ₀) := by
  apply Subtype.ext; funext σ; apply Subtype.ext
  by_cases hb : b σ <;> simp [CQState.cqTrueSt, tcPadStateLow, tcPadPDO, hb]

theorem tcPadStateLow_falseState {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (b : Store Var → Prop) [DecidablePred b] (Δ₀ : CQState (Store Var) (2 ^ Q₀)) :
    CQState.cqFalseSt b (tcPadStateLow r Δ₀) = tcPadStateLow r (CQState.cqFalseSt b Δ₀) := by
  apply Subtype.ext; funext σ; apply Subtype.ext
  by_cases hb : b σ <;> simp [CQState.cqFalseSt, tcPadStateLow, tcPadPDO, hb]

theorem tcPadStateLow_map {Var Var' : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (f : Store Var → Store Var') (Δ₀ : CQState (Store Var) (2 ^ Q₀)) :
    (tcPadStateLow r Δ₀).map f = tcPadStateLow r (Δ₀.map f) :=
  Subtype.ext <| funext fun _ ↦ Subtype.ext <|
    (HermitianMat.conj_tsum (tcLowPadIso r) (Δ₀.summable.subtype _)).symm

theorem tcPadStateLow_qAssign_embed {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (U : Unitary (2 ^ Q₀)) (Δ₀ : CQState (Store Var) (2 ^ Q₀)) :
    CQState.qAssign (r.embedUnitary U) (tcPadStateLow r Δ₀) =
      tcPadStateLow r (CQState.qAssign U Δ₀) := by
  apply Subtype.ext; funext σ; apply Subtype.ext
  change ((Δ₀.1 σ).1.conj (tcLowPadIso r)).conj (r.embedMatrix U.1) =
    ((Δ₀.1 σ).1.conj U.1).conj (tcLowPadIso r)
  rw [HermitianMat.conj_conj, HermitianMat.conj_conj, embedMatrix_mul_tcLowPadIso]

theorem tcPadStateLow_qMeasure_compose {Var : Type} [DecidableEq Var] {Q₀ Q w : ℕ}
    (r : QRegister Q₀ Q) (x : Var) (reg : QRegister w Q₀) (Δ₀ : CQState (Store Var) (2 ^ Q₀)) :
    CQState.qMeasurement x
        ((r.compose reg).computationalBasisMeasurement : Measurement (2 ^ Q) (2 ^ w))
        (tcPadStateLow r Δ₀) =
      tcPadStateLow r
        (CQState.qMeasurement x
          (reg.computationalBasisMeasurement : Measurement (2 ^ Q₀) (2 ^ w)) Δ₀) := by
  apply Subtype.ext; funext σ; apply Subtype.ext
  dsimp only [CQState.qMeasurement, CQState.sum, PartialDensityOperator.sum, tcPadStateLow,
    tcPadPDO]
  rw [map_sum (HermitianMat.conj (tcLowPadIso r))]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  let M₁ := ((r.compose reg).computationalBasisMeasurement : Measurement (2 ^ Q) (2 ^ w))
  let M₀ := (reg.computationalBasisMeasurement : Measurement (2 ^ Q₀) (2 ^ w))
  have hconj :
      (tcPadStateLow r Δ₀).conj (M₁.1 o) (M₁.le_one o) =
        tcPadStateLow r
          (Δ₀.conj (M₀.1 o) (M₀.le_one o)) := by
    apply Subtype.ext; funext τ; apply Subtype.ext
    change ((Δ₀.1 τ).1.conj (tcLowPadIso r)).conj ((r.compose reg).basisOutcomeProjector o) =
      ((Δ₀.1 τ).1.conj (reg.basisOutcomeProjector o)).conj (tcLowPadIso r)
    have hproj : (r.compose reg).basisOutcomeProjector o =
        r.embedMatrix (reg.basisOutcomeProjector o) :=
      r.embedMatrix_compose reg (compProj o)
    rw [hproj, HermitianMat.conj_conj, HermitianMat.conj_conj, embedMatrix_mul_tcLowPadIso]
  have hbranch :
      ((tcPadStateLow r Δ₀).conj (M₁.1 o) (M₁.le_one o)).assign x ↑o.1 =
        tcPadStateLow r
          ((Δ₀.conj (M₀.1 o) (M₀.le_one o)).assign x ↑o.1) := by
    rw [CQState.assign, CQState.assign, hconj, tcPadStateLow_map]
  exact congrArg (fun Y : CQState (Store Var) (2 ^ Q) ↦ (Y.1 σ).1) hbranch

theorem interp_tcLiftCircLow {Var : Type} [DecidableEq Var] {Q₀ Q w : ℕ} (hQ : Q₀ ≤ Q)
    (oracle : Unitary (2 ^ w)) (c : OracleDynamicCircuit (Unitary (2 ^ Q₀)) Var Q₀ w)
    (Δ₀ : CQState (Store Var) (2 ^ Q₀)) :
    (interp ((tcLiftCircLow hQ c).compile QProg.qAssign oracle)).toStateFun
        (tcPadStateLow (tcLowBlockReg hQ) Δ₀) =
      tcPadStateLow (tcLowBlockReg hQ)
        ((interp (c.compile QProg.qAssign oracle)).toStateFun Δ₀) := by
  set r := tcLowBlockReg hQ
  induction c generalizing Δ₀ with
  | «skip» => rfl
  | «step» U =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_step, interp_qAssign,
        QMonad.Q.toStateFun_qAssign, cqState_qAssign_tcEnsureImagUnitary]
      exact tcPadStateLow_qAssign_embed r U Δ₀
  | «oracle» reg =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_oracle, interp_qAssign,
        QMonad.Q.toStateFun_qAssign, QRegister.embedUnitary_compose]
      exact tcPadStateLow_qAssign_embed r (reg.embedUnitary oracle) Δ₀
  | «measure» x reg =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_measure, QProg.measureRegister,
        interp_qMeasure, QMonad.Q.toStateFun_qMeasurement]
      exact tcPadStateLow_qMeasure_compose r x reg Δ₀
  | «seq» _ _ ih₁ ih₂ =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_seq, interp_qSeq,
        QMonad.Q.toStateFun_bind, ih₁, ih₂]
  | «qIf» _ _ _ ih₁ ih₂ =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_qIf, interp_qIf,
        QMonad.Q.cqToStateFunIf, tcPadStateLow_trueState, tcPadStateLow_falseState, ih₁, ih₂]
      apply Subtype.ext; funext σ; apply Subtype.ext
      dsimp only [CQState.add, PartialDensityOperator.add, tcPadStateLow, tcPadPDO]
      exact (map_add (HermitianMat.conj (tcLowPadIso r)) _ _).symm
  | «qWhile» b body ih =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_qWhile, interp_qWhile,
        QMonad.Q.toStateFun_ωSup]
      let bQ := interp ((tcLiftCircLow hQ body).compile QProg.qAssign oracle)
      let b0 := interp (body.compile QProg.qAssign oracle)
      have hrec : ∀ t : ℕ, ∀ Υ₀ : CQState (Store Var) (2 ^ Q₀),
          (QMonad.Q.whileRec bQ b t).toStateFun (tcPadStateLow r Υ₀) =
            tcPadStateLow r ((QMonad.Q.whileRec b0 b t).toStateFun Υ₀) := by
        intro t
        induction t with
        | zero =>
            intro Υ₀
            rw [QMonad.Q.whileRec_zero, QMonad.Q.toStateFun_abort,
              QMonad.Q.whileRec_zero, QMonad.Q.toStateFun_abort]
            apply Subtype.ext; funext σ; apply Subtype.ext
            exact (map_zero (HermitianMat.conj (tcLowPadIso r))).symm
        | succ t iht =>
            intro Υ₀
            rw [QMonad.Q.whileRec_succ, QMonad.Q.whileRec_succ]
            simp only [QMonad.Q.cqToStateFunIf, QMonad.Q.toStateFun_bind,
              QMonad.Q.toStateFun_pure, tcPadStateLow_trueState, tcPadStateLow_falseState]
            apply Subtype.ext; funext σ; apply Subtype.ext
            dsimp only [CQState.add, PartialDensityOperator.add, bQ, b0]
            rw [ih, iht]
            dsimp only [tcPadStateLow, tcPadPDO]
            exact (map_add (HermitianMat.conj (tcLowPadIso r)) _ _).symm
      apply Subtype.ext; funext σ
      let ch0 : OmegaCompletePartialOrder.Chain (𝒟 (Fin (2 ^ Q₀))) :=
        (((⟨QMonad.Q.whileRec b0 b, QMonad.Q.whileRec_monotone b0 b⟩ :
            OmegaCompletePartialOrder.Chain (QMonad.Q (Store Var) (2 ^ Q₀) Unit)).map
          QMonad.Q.toStateFunEmb.toOrderHom).map (Pi.evalOrderHom Δ₀) |>.map
          (OrderHom.Subtype.val _) |>.map (Pi.evalOrderHom σ))
      have hchQ :
          (((⟨QMonad.Q.whileRec bQ b, QMonad.Q.whileRec_monotone bQ b⟩ :
              OmegaCompletePartialOrder.Chain (QMonad.Q (Store Var) (2 ^ Q) Unit)).map
            QMonad.Q.toStateFunEmb.toOrderHom).map (Pi.evalOrderHom (tcPadStateLow r Δ₀)) |>.map
            (OrderHom.Subtype.val _) |>.map (Pi.evalOrderHom σ)) =
            (ch0.map (tcPadPDOOrderHom r)) := by
        apply DFunLike.ext; intro t
        exact congrArg (fun Y : CQState (Store Var) (2 ^ Q) ↦ Y.1 σ) (hrec t Δ₀)
      change (OmegaCompletePartialOrder.ωSup
          ((((⟨QMonad.Q.whileRec bQ b, QMonad.Q.whileRec_monotone bQ b⟩ :
              OmegaCompletePartialOrder.Chain (QMonad.Q (Store Var) (2 ^ Q) Unit)).map
            QMonad.Q.toStateFunEmb.toOrderHom).map (Pi.evalOrderHom (tcPadStateLow r Δ₀))).map
            (OrderHom.Subtype.val _) |>.map (Pi.evalOrderHom σ))) =
        tcPadPDO r (OmegaCompletePartialOrder.ωSup ch0)
      rw [hchQ, tcPadPDO_ωSup]

theorem expect_tcPadStateLow_liftPureProp {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (Δ₀ : CQState (Store Var) (2 ^ Q₀)) (P : Store Var → Prop) :
    𝔼[tcPadStateLow r Δ₀, liftPureProp P] = 𝔼[Δ₀, liftPureProp P] := by
  open Classical in
  rw [qcExpectEqTsumStore, qcExpectEqTsumStore]
  refine tsum_congr fun σ ↦ ?_
  by_cases hP : P σ
  · simp only [liftPureProp_apply, hP, ↓reduceIte, Observable.coe_one, HermitianMat.one_inner]
    exact trace_conj_tcLowPadIso r (Δ₀.1 σ).1
  · simp [liftPureProp_apply, hP]

theorem expectedCost_tcLiftCircLow_le {Var : Type} [DecidableEq Var] {Q₀ Q w : ℕ} (hQ : Q₀ ≤ Q)
    {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q₀)) Var Q₀ w)
    (Δ₀ : CQState (Store Var) (2 ^ Q₀)) :
    expectedCost (CostModel.ofEmbeddedOracle oracle)
        ((tcLiftCircLow hQ c).compile QProg.qAssign oracle)
        (tcPadStateLow (tcLowBlockReg hQ) Δ₀) ≤
      expectedCost (CostModel.ofEmbeddedOracle oracle) (c.compile QProg.qAssign oracle) Δ₀ := by
  induction c generalizing Δ₀ with
  | «skip» => simp [tcLiftCircLow]
  | «step» _ =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_step, expectedCost_qAssign,
        unitaryCost_tcEnsureImagUnitary_eq_zero horacle, Nat.cast_zero, mul_zero]
      exact zero_le
  | «oracle» _ =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_oracle, expectedCost_qAssign,
        CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary, trace_tcPadStateLow]
      exact le_rfl
  | «measure» _ _ =>
      simp [tcLiftCircLow, OracleDynamicCircuit.compile_measure, QProg.measureRegister,
        CostModel.ofEmbeddedOracle]
  | «seq» _ _ ih₁ ih₂ =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_seq, expectedCost_qSeq,
        interp_tcLiftCircLow]
      exact add_le_add (ih₁ Δ₀) (ih₂ _)
  | «qIf» _ _ _ ih₁ ih₂ =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_qIf, cqExpectedCostIf,
        tcPadStateLow_trueState, tcPadStateLow_falseState]
      exact add_le_add (ih₁ _) (ih₂ _)
  | «qWhile» _ _ ih =>
      simp only [tcLiftCircLow, OracleDynamicCircuit.compile_qWhile, expectedCost_qWhile]
      refine iSup_mono fun t ↦ ?_
      induction t generalizing Δ₀ with
      | zero => simp [whileRecCost]
      | succ _ iht =>
          simp only [cqWhileRecCostSuc, tcPadStateLow_trueState, interp_tcLiftCircLow]
          exact add_le_add (ih _) (iht _)

/-- Reset matrix `tr(ρ) |0⟩⟨0|` on `Fin (2 ^ Q₀)` for `ρ: 𝒟 (2 ^ Q)`. -/
noncomputable def tcQSetLowMat (Q₀ : ℕ) {Q : ℕ} (ρ : 𝒟 (Fin (2 ^ Q))) :
    HermitianMat (Fin (2 ^ Q₀)) ℂ :=
  ⟨Matrix.single (0 : Fin (2 ^ Q₀)) (0 : Fin (2 ^ Q₀)) (ρ.1.trace : ℂ),
    show (Matrix.single (0 : Fin (2 ^ Q₀)) (0 : Fin (2 ^ Q₀)) (ρ.1.trace : ℂ)).IsHermitian by
      simp [Matrix.IsHermitian, Matrix.conjTranspose_single, RCLike.star_def]⟩

@[simp]
theorem tcQSetLowMat_mat (Q₀ : ℕ) {Q : ℕ} (ρ : 𝒟 (Fin (2 ^ Q))) :
    (tcQSetLowMat Q₀ ρ).mat = Matrix.single 0 0 (ρ.1.trace : ℂ) := rfl

@[simp]
theorem trace_tcQSetLowMat (Q₀ : ℕ) {Q : ℕ} (ρ : 𝒟 (Fin (2 ^ Q))) :
    (tcQSetLowMat Q₀ ρ).trace = ρ.1.trace := by
  rw [HermitianMat.trace_eq_re_trace, tcQSetLowMat_mat, ← Matrix.diagonal_single,
    Matrix.trace_diagonal]
  simp

/-- Partial density operator `tr(ρ) |0⟩⟨0|` on `2 ^ Q₀`. -/
noncomputable def tcQSetLowPDO (Q₀ : ℕ) {Q : ℕ} (ρ : 𝒟 (Fin (2 ^ Q))) : 𝒟 (Fin (2 ^ Q₀)) :=
  ⟨tcQSetLowMat Q₀ ρ, by
    refine ⟨?_, (trace_tcQSetLowMat Q₀ ρ).trans_le ρ.2.2⟩
    rw [HermitianMat.zero_le_iff, tcQSetLowMat_mat, ← Matrix.diagonal_single,
      Matrix.posSemidef_diagonal_iff]
    intro i
    rcases eq_or_ne i 0 with rfl | hi <;> simp [*, HermitianMat.trace_nonneg ρ.2.1]⟩

/-- Store-preserving `|0⟩`-reset projection onto `2 ^ Q₀`. -/
noncomputable def tcQSetLow {Var : Type} (Q₀ : ℕ) {Q : ℕ} (Δ : CQState (Store Var) (2 ^ Q)) :
    CQState (Store Var) (2 ^ Q₀) :=
  ⟨fun σ ↦ tcQSetLowPDO Q₀ (Δ.1 σ), by
    have h : (fun σ ↦ (tcQSetLowPDO Q₀ (Δ.1 σ)).trace) = fun σ ↦ (Δ.1 σ).trace :=
      funext fun σ ↦ Subtype.ext (trace_tcQSetLowMat Q₀ (Δ.1 σ))
    exact ⟨Δ.trace, h ▸ Δ.hasSum_trace, Δ.trace_le_one⟩⟩

theorem qSet_tcQSetLow {Var : Type} (Q₀ : ℕ) {Q : ℕ} (Δ : CQState (Store Var) (2 ^ Q)) :
    (tcQSetLow Q₀ Δ).qSet = tcQSetLow Q₀ Δ := by
  apply Subtype.ext; funext σ; apply Subtype.ext; apply HermitianMat.ext
  rw [Operator.cqState_qSet_mat]
  dsimp only [tcQSetLow, tcQSetLowPDO]
  rw [trace_tcQSetLowMat, tcQSetLowMat_mat]

theorem supportedOn_zero_tcQSetLow {Var : Type} (Q₀ : ℕ) {Q : ℕ} (Δ : CQState (Store Var) (2 ^ Q)) :
    SupportedOn (· = (0 : Fin (2 ^ Q₀))) (tcQSetLow Q₀ Δ) := by
  rw [← qSet_tcQSetLow Q₀ Δ]
  exact supportedOn_qSet (pred := fun z : Fin (2 ^ Q₀) ↦ z = 0) rfl (tcQSetLow Q₀ Δ)

theorem tcBasisSplitEquiv_zero {Q₀ Q : ℕ} (r : QRegister Q₀ Q) :
    r.basisSplitEquiv 0 = (0, 0) := by
  apply Prod.ext
  · rw [QRegister.basisSplitEquiv_apply_fst]
    apply (basisBits Q₀).injective
    funext w
    rw [QRegister.basisBits_extractIndex, basisBits_zero, basisBits_zero]
    rfl
  · funext q
    simp [QRegister.basisSplitEquiv_apply_snd, basisBits_zero]

theorem tcPadStateLow_tcQSetLow_of_supportedOn_zero {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = (0 : Fin (2 ^ Q))) Δ) :
    tcPadStateLow r (tcQSetLow Q₀ Δ) = Δ := by
  apply Subtype.ext; funext σ; apply Subtype.ext; apply HermitianMat.ext
  have hM := (hΔ σ).symm
  have htr : ((Δ.1 σ).1.trace : ℂ) = (Δ.1 σ).1.mat 0 0 := by
    rw [HermitianMat.trace_eq_re_trace, RCLike.re_eq_complex_re, hM, Matrix.trace,
      Finset.sum_eq_single 0]
    · rw [Matrix.diag_apply, diagProj_mul_mul_diagProj_apply]
      simp only [and_self, ↓reduceIte]
      exact Complex.ext (by simp) (by simp)
    · intro z _ hz
      rw [Matrix.diag_apply, diagProj_mul_mul_diagProj_apply]
      simp [hz]
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  dsimp only [tcPadStateLow, tcPadPDO, tcQSetLow, tcQSetLowPDO]
  rw [HermitianMat.conj_apply_mat, tcQSetLowMat_mat, htr]
  conv_rhs => rw [hM]
  ext a b
  rw [diagProj_mul_mul_diagProj_apply, Matrix.mul_apply,
    Finset.sum_eq_single (0 : Fin (2 ^ Q₀))]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (2 ^ Q₀))]
    · simp only [Matrix.single_apply_same, tcLowPadIso, Matrix.of_apply,
        Matrix.conjTranspose_apply]
      have ha0 : (r.basisSplitEquiv a = (0, 0)) ↔ a = 0 :=
        ⟨fun h ↦ r.basisSplitEquiv.injective (h.trans (tcBasisSplitEquiv_zero r).symm),
          fun h ↦ h ▸ tcBasisSplitEquiv_zero r⟩
      have hb0 : (r.basisSplitEquiv b = (0, 0)) ↔ b = 0 :=
        ⟨fun h ↦ r.basisSplitEquiv.injective (h.trans (tcBasisSplitEquiv_zero r).symm),
          fun h ↦ h ▸ tcBasisSplitEquiv_zero r⟩
      simp only [ha0, hb0]
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
    · intro x _ hx; simp [hx.symm]
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  · intro y _ hy
    rw [Matrix.mul_apply]
    have hz0 : ∑ x : Fin (2 ^ Q₀),
        tcLowPadIso r a x * Matrix.single 0 0 ((Δ.1 σ).1.mat 0 0) x y = 0 :=
      Finset.sum_eq_zero fun x _ ↦ by simp [hy.symm]
    rw [hz0, zero_mul]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim

theorem tcLiftFromSet_transition {Var : Type} [DecidableEq Var] (res : Var)
    {Q₀ Q n m k : ℕ} (hQ : Q₀ ≤ Q)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q₀)) Var Q₀ ((n + 1) * m))
    {S : Finset (Fin (2 ^ n))} {B : ℝ}
    (hc : ∀ {Δ₀ : CQState (Store Var) (2 ^ Q₀)}, SupportedOn (· = 0) Δ₀ →
      let prog₀ := c.compile QProg.qAssign (parallelMarkingOracle m S)
      𝔼[(interp prog₀).toStateFun Δ₀,
        liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ₀.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog₀ Δ₀ ≤
        stateMass Δ₀ * ENNReal.ofReal B)
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (tcLiftCircLow hQ c).compile QProg.qAssign (parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ,
      liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
    expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal B := by
  intro prog
  let Δ₀ := tcQSetLow Q₀ Δ
  have hpad : tcPadStateLow (tcLowBlockReg hQ) Δ₀ = Δ :=
    tcPadStateLow_tcQSetLow_of_supportedOn_zero _ hΔ
  have htr₀ : Δ₀.trace = Δ.trace := by
    rw [← hpad, trace_tcPadStateLow]
  have hmass₀ : stateMass Δ₀ = stateMass Δ := by
    rw [← hpad, stateMass_tcPadStateLow]
  obtain ⟨hexp₀, hcost₀⟩ := hc (supportedOn_zero_tcQSetLow Q₀ Δ)
  refine ⟨?_, ?_⟩
  · dsimp only [prog]
    conv_lhs => rw [← hpad]
    rw [interp_tcLiftCircLow, expect_tcPadStateLow_liftPureProp, hexp₀, htr₀]
  · dsimp only [prog]
    conv_lhs => rw [← hpad]
    rw [← hmass₀]
    exact (expectedCost_tcLiftCircLow_le hQ (isRealMatrix_parallelMarkingOracle S) c Δ₀).trans
      hcost₀

/-- Checker that `MHTail` (`r = 1`) cost is bounded by `(v1 / 10^16) * √(2^n)`. -/
def tcCheckLockR1Tail (e v1 : ℕ) : Bool :=
  decide ((4091549431 * 785398163398 * 10000) ^ 2 ≤
    2 ^ e * (v1 * 5000000000) ^ 2)

/-- Ambient-`Q` `r = 1` Stationary-chord tail circuit lifted from `findAllQubits n m k`. -/
noncomputable def tcLockR1TailCircuit {Var : Type} (res : Var) (n m k Q : ℕ)
    (hQ : findAllQubits n m k ≤ Q) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  tcLiftCircLow hQ (lockSingleFromSetCircuit res n m k T)

theorem tcLockR1Tail_transition {Var : Type} [DecidableEq Var] (res : Var)
    {e n k Q v1 : ℕ} (hn : 100 ≤ n) (he : e ≤ 10) (hk1024 : k ≤ 1024)
    (hQ : findAllQubits n (2 ^ e) k ≤ Q)
    (hchk : tcCheckLockR1Tail e v1 = true)
    {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hrem1 : k - T.card = 1)
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (tcLockR1TailCircuit res n (2 ^ e) k Q hQ T).compile
      QProg.qAssign (parallelMarkingOracle (2 ^ e) S)
    𝔼[(interp prog).toStateFun Δ,
      liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
    expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal (((v1 : ℝ) / 10000000000000000) * √(2 ^ n : ℝ)) := by
  have hm1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hm1024 : 2 ^ e ≤ 1024 := by
    calc 2 ^ e ≤ 2 ^ 10 := Nat.pow_le_pow_right (by positivity) he
      _ = 1024 := by norm_num
  refine tcLiftFromSet_transition res hQ (lockSingleFromSetCircuit res n (2 ^ e) k T) ?_ hΔ
  intro Δ₀ hΔ₀
  obtain ⟨hexp, hcost⟩ := lockSingleFromSet_transition res hn hm1 hm1024 hk1024 hScard hTS
    hrem1 hΔ₀
  refine ⟨hexp, hcost.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le)⟩
  unfold tcCheckLockR1Tail at hchk
  simp only [decide_eq_true_eq] at hchk
  have hpi_hi : π / 4 ≤ (785398163398 : ℝ) / 1000000000000 := by
    linarith [Real.pi_lt_d20]
  have hrel : ((relCostLock : ℚ≥0) : ℝ) = (4091549431 : ℝ) / 5000000000 := by
    unfold relCostLock; push_cast; norm_num
  have hSN_nn : 0 ≤ √(2 ^ n : ℝ) := Real.sqrt_nonneg _
  have hsm_pos : (0 : ℝ) < √((2 ^ e : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hcoeff :
      ((4091549431 : ℝ) / 5000000000) * ((785398163398 : ℝ) / 1000000000000) /
          √((2 ^ e : ℕ) : ℝ) ≤
        (v1 : ℝ) / 10000000000000000 := by
    suffices h5 :
        (4091549431 * 785398163398 * 10000 : ℝ) ≤
          5000000000 * ((v1 : ℝ) * √((2 ^ e : ℕ) : ℝ)) by
      rw [div_le_div_iff₀ hsm_pos (by norm_num)]
      linarith
    set A : ℝ := (4091549431 * 785398163398 * 10000 : ℝ)
    set B : ℝ := 5000000000 * ((v1 : ℝ) * √((2 ^ e : ℕ) : ℝ))
    have hcast : A ^ 2 ≤ ((2 ^ e : ℕ) : ℝ) * ((v1 : ℝ) * 5000000000) ^ 2 := by
      have hc :
          (((4091549431 * 785398163398 * 10000 : ℕ) : ℝ) ^ 2) ≤
            ((2 ^ e : ℕ) : ℝ) * (((v1 * 5000000000 : ℕ) : ℝ) ^ 2) := by
        exact_mod_cast hchk
      have hA : ((4091549431 * 785398163398 * 10000 : ℕ) : ℝ) = A := by
        dsimp only [A]; norm_num
      have hV : ((v1 * 5000000000 : ℕ) : ℝ) = (v1 : ℝ) * 5000000000 := by
        push_cast; rfl
      rwa [hA, hV] at hc
    have hB_sq : B ^ 2 = ((2 ^ e : ℕ) : ℝ) * ((v1 : ℝ) * 5000000000) ^ 2 := by
      dsimp only [B]
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 ^ e : ℕ))]
      ring
    have hB_nn : 0 ≤ B := by dsimp only [B]; positivity
    by_contra hlt
    have hp : 0 < (A - B) * (A + B) := mul_pos (by linarith) (by linarith [hB_nn])
    linarith [show (A - B) * (A + B) = A ^ 2 - B ^ 2 by ring, hcast, hB_sq]
  rw [hrel, Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n)]
  have h1 : ((4091549431 : ℝ) / 5000000000) * (π / 4) *
      (√(2 ^ n : ℝ) / √((2 ^ e : ℕ) : ℝ)) ≤
      (((4091549431 : ℝ) / 5000000000) * ((785398163398 : ℝ) / 1000000000000) /
        √((2 ^ e : ℕ) : ℝ)) * √(2 ^ n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hpi_hi (by positivity : (0 : ℝ) ≤ 4091549431 / 5000000000)
    have hd := div_le_div_of_nonneg_right hm hsm_pos.le
    have hmr := mul_le_mul_of_nonneg_right hd hSN_nn
    linarith [hmr,
      show ((4091549431 : ℝ) / 5000000000) * (π / 4) *
          (√(2 ^ n : ℝ) / √((2 ^ e : ℕ) : ℝ)) =
        (((4091549431 : ℝ) / 5000000000) * (π / 4) / √((2 ^ e : ℕ) : ℝ)) * √(2 ^ n : ℝ) by ring]
  exact h1.trans (mul_le_mul_of_nonneg_right hcoeff hSN_nn)

/-! ## 2. Disjoint Register Swap Permutation & `TensorConveyor` Register Layout -/

/-- Basis permutation swapping two disjoint `W`-qubit registers `r₁` and `r₂` on `Fin (2 ^
  Q)`. -/
noncomputable def tcSwapRegsFun {W Q : ℕ} (r₁ r₂ : QRegister W Q) (z : Fin (2 ^ Q)) :
    Fin (2 ^ Q) :=
  r₁.replaceIndex (r₂.replaceIndex z (r₁.extractIndex z)) (r₂.extractIndex z)

theorem tcSwapRegsFun_extract_left {W Q : ℕ} (r₁ r₂ : QRegister W Q) (z : Fin (2 ^ Q)) :
    r₁.extractIndex (tcSwapRegsFun r₁ r₂ z) = r₂.extractIndex z :=
  r₁.extractIndex_replaceIndex _ _

theorem tcSwapRegsFun_extract_right {W Q : ℕ} {r₁ r₂ : QRegister W Q}
    (h : r₁.DisjointWires r₂) (z : Fin (2 ^ Q)) :
    r₂.extractIndex (tcSwapRegsFun r₁ r₂ z) = r₁.extractIndex z := by
  dsimp only [tcSwapRegsFun]
  rw [r₂.extractIndex_replaceIndex_of_disjoint _ h.symm,
    r₂.extractIndex_replaceIndex]

theorem tcSwapRegsFun_extract_other {W W' Q : ℕ} {r₁ r₂ : QRegister W Q} {r₃ : QRegister W' Q}
    (h31 : r₃.DisjointWires r₁) (h32 : r₃.DisjointWires r₂) (z : Fin (2 ^ Q)) :
    r₃.extractIndex (tcSwapRegsFun r₁ r₂ z) = r₃.extractIndex z := by
  dsimp only [tcSwapRegsFun]
  rw [r₃.extractIndex_replaceIndex_of_disjoint _ h31,
    r₃.extractIndex_replaceIndex_of_disjoint _ h32]

theorem tcSwapRegsFun_basisBits_outside {W Q : ℕ} (r₁ r₂ : QRegister W Q) (z : Fin (2 ^ Q))
    {w : Wire Q} (hw1 : w ∉ Set.range r₁.wires) (hw2 : w ∉ Set.range r₂.wires) :
    basisBits Q (tcSwapRegsFun r₁ r₂ z) w = basisBits Q z w := by
  dsimp only [tcSwapRegsFun]
  rw [r₁.basisBits_replaceIndex_of_not_mem _ _ _ hw1,
    r₂.basisBits_replaceIndex_of_not_mem _ _ _ hw2]

theorem tcSwapRegsFun_involutive {W Q : ℕ} {r₁ r₂ : QRegister W Q}
    (h : r₁.DisjointWires r₂) : Function.Involutive (tcSwapRegsFun r₁ r₂) := by
  intro z
  apply (basisBits Q).injective
  funext w
  by_cases hw1 : w ∈ Set.range r₁.wires
  · obtain ⟨b, rfl⟩ := hw1
    rw [← r₁.basisBits_extractIndex, tcSwapRegsFun_extract_left,
      tcSwapRegsFun_extract_right h, r₁.basisBits_extractIndex]
  · by_cases hw2 : w ∈ Set.range r₂.wires
    · obtain ⟨b, rfl⟩ := hw2
      rw [← r₂.basisBits_extractIndex, tcSwapRegsFun_extract_right h,
        tcSwapRegsFun_extract_left, r₂.basisBits_extractIndex]
    · rw [tcSwapRegsFun_basisBits_outside r₁ r₂ _ hw1 hw2,
        tcSwapRegsFun_basisBits_outside r₁ r₂ _ hw1 hw2]

/-- Involutive `Equiv.Perm` swapping two disjoint `W`-qubit registers. -/
noncomputable def tcSwapRegsEquiv {W Q : ℕ} (r₁ r₂ : QRegister W Q) (h : r₁.DisjointWires r₂) :
    Equiv.Perm (Fin (2 ^ Q)) :=
  (tcSwapRegsFun_involutive h).toPerm

@[simp]
theorem tcSwapRegsEquiv_apply {W Q : ℕ} (r₁ r₂ : QRegister W Q) (h : r₁.DisjointWires r₂)
    (z : Fin (2 ^ Q)) :
    tcSwapRegsEquiv r₁ r₂ h z = tcSwapRegsFun r₁ r₂ z :=
  rfl

/-- Low `(n + 1) * m` oracle wires inside `Q`. -/
def tcOracleReg (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q) :
    QRegister ((n + 1) * m) Q :=
  QRegister.block 0 ((n + 1) * m) (by omega)

/-- Slot `i` (`n + 1` wires: `0` marker + `1..n` active index) inside `Q`. -/
def tcSlotOracleReg (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) :
    QRegister (n + 1) Q :=
  (tcOracleReg n m Q hQ).compose (localSlotReg n m i)

/-- Slot `i` marker wire `i * (n + 1)` inside `Q`. -/
def tcMarkerReg (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) :
    QRegister 1 Q :=
  (tcSlotOracleReg n m Q hQ i).compose (localMarkerReg n)

/-- Slot `i` active `n`-qubit index register `i * (n + 1) + 1.. i * (n + 1) + n` inside `Q`. -/
def tcActiveIdxReg (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) :
    QRegister n Q :=
  (tcSlotOracleReg n m Q hQ i).compose (localIdxReg n)

/-- Slot `i` passive `n`-qubit subregister `p: Fin 11` (`q = p + 1`) inside `Q`. -/
def tcPassiveReg (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) (p : Fin 11) :
    QRegister n Q :=
  QRegister.block ((n + 1) * m + (i.val * 11 + p.val) * n) n (by
    have hi : i.val + 1 ≤ m := i.isLt
    have hp : p.val + 1 ≤ 11 := p.isLt
    have hmul : i.val * 11 + p.val + 1 ≤ 11 * m := by nlinarith
    have hmul2 : (i.val * 11 + p.val + 1) * n ≤ 11 * m * n := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_right n hmul
    nlinarith)

/-- Verification flag wire `(i, q)` (`i < m, q < 12`) in `[(n + 1)*m + 11*m*n.. + 12*m*n)`. -/
def tcVerifFlagReg (n m Q : ℕ) (hn12 : 12 ≤ n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (i : Fin m) (q : Fin 12) : QRegister 1 Q :=
  QRegister.block ((n + 1) * m + 11 * m * n + i.val * 12 + q.val) 1 (by
    have hi : i.val + 1 ≤ m := i.isLt
    have hq : q.val + 1 ≤ 12 := q.isLt
    have h12 : i.val * 12 + q.val + 1 ≤ 12 * m := by nlinarith
    have hmn : 12 * m ≤ m * n := by nlinarith
    nlinarith)

@[simp]
theorem tcOracleReg_apply_val (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (w : Fin ((n + 1) * m)) :
    (tcOracleReg n m Q hQ w).val = w.val := by
  simp only [tcOracleReg, QRegister.block_apply_val, zero_add]

@[simp]
theorem tcSlotOracleReg_apply_val (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (i : Fin m) (w : Fin (n + 1)) :
    (tcSlotOracleReg n m Q hQ i w).val = i.val * (n + 1) + w.val := by
  simp only [tcSlotOracleReg, QRegister.compose_apply, tcOracleReg_apply_val, localSlotReg,
    QRegister.block_apply_val]

@[simp]
theorem tcMarkerReg_apply_val (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (i : Fin m) (w : Fin 1) :
    (tcMarkerReg n m Q hQ i w).val = i.val * (n + 1) + w.val := by
  simp only [tcMarkerReg, QRegister.compose_apply, tcSlotOracleReg_apply_val, localMarkerReg,
    QRegister.block_apply_val, zero_add]

@[simp]
theorem tcActiveIdxReg_apply_val (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (i : Fin m) (w : Fin n) :
    (tcActiveIdxReg n m Q hQ i w).val = i.val * (n + 1) + (1 + w.val) := by
  simp only [tcActiveIdxReg, QRegister.compose_apply, tcSlotOracleReg_apply_val, localIdxReg,
    QRegister.block_apply_val]

@[simp]
theorem tcPassiveReg_apply_val (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (i : Fin m) (p : Fin 11) (w : Fin n) :
    (tcPassiveReg n m Q hQ i p w).val = (n + 1) * m + (i.val * 11 + p.val) * n + w.val := by
  simp only [tcPassiveReg, QRegister.block_apply_val]

@[simp]
theorem tcVerifFlagReg_apply_val (n m Q : ℕ) (hn12 : 12 ≤ n)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) (q : Fin 12) (w : Fin 1) :
    (tcVerifFlagReg n m Q hn12 hQ i q w).val =
      (n + 1) * m + 11 * m * n + i.val * 12 + q.val + w.val := by
  simp only [tcVerifFlagReg, QRegister.block_apply_val]

theorem tcActiveIdx_val_lt {n m : ℕ} (i : Fin m) (w : Fin n) :
    i.val * (n + 1) + (1 + w.val) < (n + 1) * m := by
  calc i.val * (n + 1) + (1 + w.val)
      < i.val * (n + 1) + (n + 1) := by omega
    _ = (i.val + 1) * (n + 1) := by ring
    _ ≤ m * (n + 1) := Nat.mul_le_mul_right (n + 1) i.isLt
    _ = (n + 1) * m := by ring

theorem tcMarker_val_lt {n m : ℕ} (i : Fin m) :
    i.val * (n + 1) < (n + 1) * m := by
  calc i.val * (n + 1) < i.val * (n + 1) + (n + 1) := by omega
    _ = (i.val + 1) * (n + 1) := by ring
    _ ≤ m * (n + 1) := Nat.mul_le_mul_right (n + 1) i.isLt
    _ = (n + 1) * m := by ring

/-- Combined `n * d`-qubit `TensorConveyor` register for slot `i` (`1 ≤ d ≤ 12`, `0 < n`). -/
def tcSlotConveyorReg (n m d Q : ℕ) (hn : 0 < n) (hd : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) : QRegister (n * d) Q where
  wires :=
    ⟨fun (w : Fin (n * d)) ↦
      if _hq0 : w.val / n = 0 then
        tcActiveIdxReg n m Q hQ i ⟨w.val % n, Nat.mod_lt _ hn⟩
      else
        tcPassiveReg n m Q hQ i
          ⟨w.val / n - 1, by
            have hlt : w.val / n < d := Nat.div_lt_of_lt_mul w.isLt
            omega⟩
          ⟨w.val % n, Nat.mod_lt _ hn⟩, by
      intro w₁ w₂ hwire
      have heq := congrArg Fin.val hwire
      dsimp only at heq
      have h1 : w₁.val = n * (w₁.val / n) + w₁.val % n := (Nat.div_add_mod w₁.val n).symm
      have h2 : w₂.val = n * (w₂.val / n) + w₂.val % n := (Nat.div_add_mod w₂.val n).symm
      have hm1 : w₁.val % n < n := Nat.mod_lt _ hn
      have hm2 : w₂.val % n < n := Nat.mod_lt _ hn
      have hi_lt := tcActiveIdx_val_lt i ⟨w₁.val % n, hm1⟩
      have hi_lt2 := tcActiveIdx_val_lt i ⟨w₂.val % n, hm2⟩
      dsimp only at hi_lt hi_lt2
      by_cases hq1 : w₁.val / n = 0 <;> by_cases hq2 : w₂.val / n = 0
      · simp only [hq1, hq2, ↓reduceDIte, tcActiveIdxReg_apply_val] at heq
        have hmod_eq : w₁.val % n = w₂.val % n := by omega
        apply Fin.ext
        rw [h1, h2, hq1, hq2, hmod_eq]
      · simp only [hq1, hq2, ↓reduceDIte, tcActiveIdxReg_apply_val, tcPassiveReg_apply_val] at heq
        omega
      · simp only [hq1, hq2, ↓reduceDIte, tcActiveIdxReg_apply_val, tcPassiveReg_apply_val] at heq
        omega
      · simp only [hq1, hq2, ↓reduceDIte, tcPassiveReg_apply_val] at heq
        have hsub : (i.val * 11 + (w₁.val / n - 1)) * n + w₁.val % n =
            (i.val * 11 + (w₂.val / n - 1)) * n + w₂.val % n := by omega
        have hr1 : (i.val * 11 + (w₁.val / n - 1)) * n + w₁.val % n =
            n * (i.val * 11 + (w₁.val / n - 1)) + w₁.val % n := by ring
        have hr2 : (i.val * 11 + (w₂.val / n - 1)) * n + w₂.val % n =
            n * (i.val * 11 + (w₂.val / n - 1)) + w₂.val % n := by ring
        have hdiv_eq : i.val * 11 + (w₁.val / n - 1) = i.val * 11 + (w₂.val / n - 1) := by
          have hd1 := congrArg (· / n) hsub
          rw [hr1, hr2, Nat.mul_add_div hn, Nat.mul_add_div hn, Nat.div_eq_of_lt hm1,
            Nat.div_eq_of_lt hm2, add_zero, add_zero] at hd1
          exact hd1
        have hsub1 : w₁.val / n - 1 = w₂.val / n - 1 := Nat.add_left_cancel hdiv_eq
        have hq1_pos : 1 ≤ w₁.val / n := Nat.pos_of_ne_zero hq1
        have hq2_pos : 1 ≤ w₂.val / n := Nat.pos_of_ne_zero hq2
        have hq_eq : w₁.val / n = w₂.val / n := by
          calc w₁.val / n = (w₁.val / n - 1) + 1 := (Nat.sub_add_cancel hq1_pos).symm
            _ = (w₂.val / n - 1) + 1 := by rw [hsub1]
            _ = w₂.val / n := Nat.sub_add_cancel hq2_pos
        rw [hdiv_eq] at hsub
        have hmod_eq : w₁.val % n = w₂.val % n := Nat.add_left_cancel hsub
        apply Fin.ext
        rw [h1, h2, hq_eq, hmod_eq]⟩

@[simp]
theorem tcSlotConveyorReg_apply (n m d Q : ℕ) (hn : 0 < n) (hd : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) (w : Fin (n * d)) :
    tcSlotConveyorReg n m d Q hn hd hQ i w =
      if _hq0 : w.val / n = 0 then
        tcActiveIdxReg n m Q hQ i ⟨w.val % n, Nat.mod_lt _ hn⟩
      else
        tcPassiveReg n m Q hQ i
          ⟨w.val / n - 1, by
            have hlt : w.val / n < d := Nat.div_lt_of_lt_mul w.isLt
            omega⟩
          ⟨w.val % n, Nat.mod_lt _ hn⟩ := rfl

theorem tcSlotConveyorReg_compose_zero {n m d Q : ℕ} (hn : 0 < n) (hd1 : 1 ≤ d) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) :
    (tcSlotConveyorReg n m d Q hn hd12 hQ i).compose (localMemSlotReg n d ⟨0, hd1⟩) =
      tcActiveIdxReg n m Q hQ i := by
  apply QRegister.ext; apply Function.Embedding.ext; intro b
  change tcSlotConveyorReg n m d Q hn hd12 hQ i (localMemSlotReg n d ⟨0, hd1⟩ b) =
    tcActiveIdxReg n m Q hQ i b
  have hb := b.isLt
  have hval : (localMemSlotReg n d ⟨0, hd1⟩ b).val = b.val := by
    simp [localMemSlotReg]
  have hdiv : (localMemSlotReg n d ⟨0, hd1⟩ b).val / n = 0 := by
    rw [hval]; exact Nat.div_eq_of_lt hb
  have hmod : (localMemSlotReg n d ⟨0, hd1⟩ b).val % n = b.val := by
    rw [hval]; exact Nat.mod_eq_of_lt hb
  rw [tcSlotConveyorReg_apply, dite_eq_left hdiv]
  congr 1
  exact Fin.ext hmod

theorem tcSlotConveyorReg_compose_pos {n m d Q : ℕ} (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) (q : Fin d) (hq : 1 ≤ q.val) :
    (tcSlotConveyorReg n m d Q hn hd12 hQ i).compose (localMemSlotReg n d q) =
      tcPassiveReg n m Q hQ i ⟨q.val - 1, by omega⟩ := by
  apply QRegister.ext; apply Function.Embedding.ext; intro b
  change tcSlotConveyorReg n m d Q hn hd12 hQ i (localMemSlotReg n d q b) =
    tcPassiveReg n m Q hQ i ⟨q.val - 1, by omega⟩ b
  have hb := b.isLt
  have hval : (localMemSlotReg n d q b).val = n * q.val + b.val := by
    simp only [localMemSlotReg, QRegister.block_apply_val]; ring
  have hdiv : (localMemSlotReg n d q b).val / n = q.val := by
    rw [hval, Nat.mul_add_div hn, Nat.div_eq_of_lt hb, add_zero]
  have hmod : (localMemSlotReg n d q b).val % n = b.val := by
    rw [hval, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have hne0 : (localMemSlotReg n d q b).val / n ≠ 0 := by omega
  rw [tcSlotConveyorReg_apply, dite_eq_right hne0]
  have hp_eq : (⟨(localMemSlotReg n d q b).val / n - 1, by
      have hlt : (localMemSlotReg n d q b).val / n < d :=
        Nat.div_lt_of_lt_mul (localMemSlotReg n d q b).isLt
      omega⟩ : Fin 11) = ⟨q.val - 1, by omega⟩ := by
    apply Fin.ext; dsimp only; rw [hdiv]
  have hb_eq : (⟨(localMemSlotReg n d q b).val % n, Nat.mod_lt _ hn⟩ : Fin n) = b :=
    Fin.ext hmod
  rw [hp_eq, hb_eq]

theorem tcSlotConveyorReg_disjoint {n m d Q : ℕ} (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) {i₁ i₂ : Fin m} (hne : i₁ ≠ i₂) :
    (tcSlotConveyorReg n m d Q hn hd12 hQ i₁).DisjointWires
      (tcSlotConveyorReg n m d Q hn hd12 hQ i₂) := by
  rw [QRegister.disjoint_iff]
  intro w₁ w₂ heq
  have hval := congrArg Fin.val heq
  have hm1 : w₁.val % n < n := Nat.mod_lt _ hn
  have hm2 : w₂.val % n < n := Nat.mod_lt _ hn
  have hlt1 := tcActiveIdx_val_lt i₁ ⟨w₁.val % n, hm1⟩
  have hlt2 := tcActiveIdx_val_lt i₂ ⟨w₂.val % n, hm2⟩
  dsimp only at hlt1 hlt2
  by_cases hq1 : w₁.val / n = 0 <;> by_cases hq2 : w₂.val / n = 0
  · simp only [tcSlotConveyorReg_apply, hq1, hq2, ↓reduceDIte, tcActiveIdxReg_apply_val] at hval
    have hd1 := congrArg (· / (n + 1)) hval
    have hr1 : i₁.val * (n + 1) + (1 + w₁.val % n) = (n + 1) * i₁.val + (1 + w₁.val % n) := by ring
    have hr2 : i₂.val * (n + 1) + (1 + w₂.val % n) = (n + 1) * i₂.val + (1 + w₂.val % n) := by ring
    rw [hr1, hr2, Nat.mul_add_div (by omega), Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)] at hd1
    exact hne (Fin.ext (by omega))
  · simp only [tcSlotConveyorReg_apply, hq1, hq2, ↓reduceDIte, tcActiveIdxReg_apply_val,
      tcPassiveReg_apply_val] at hval
    omega
  · simp only [tcSlotConveyorReg_apply, hq1, hq2, ↓reduceDIte, tcActiveIdxReg_apply_val,
      tcPassiveReg_apply_val] at hval
    omega
  · simp only [tcSlotConveyorReg_apply, hq1, hq2, ↓reduceDIte, tcPassiveReg_apply_val] at hval
    have hsub : (i₁.val * 11 + (w₁.val / n - 1)) * n + w₁.val % n =
        (i₂.val * 11 + (w₂.val / n - 1)) * n + w₂.val % n := by omega
    have hr_a : (i₁.val * 11 + (w₁.val / n - 1)) * n + w₁.val % n =
        n * (i₁.val * 11 + (w₁.val / n - 1)) + w₁.val % n := by ring
    have hr_b : (i₂.val * 11 + (w₂.val / n - 1)) * n + w₂.val % n =
        n * (i₂.val * 11 + (w₂.val / n - 1)) + w₂.val % n := by ring
    have hd1 := congrArg (· / n) hsub
    rw [hr_a, hr_b, Nat.mul_add_div hn, Nat.mul_add_div hn, Nat.div_eq_of_lt hm1,
      Nat.div_eq_of_lt hm2, add_zero, add_zero] at hd1
    have hp1 : w₁.val / n - 1 < 11 := by
      have : w₁.val / n < d := Nat.div_lt_of_lt_mul w₁.isLt
      omega
    have hp2 : w₂.val / n - 1 < 11 := by
      have : w₂.val / n < d := Nat.div_lt_of_lt_mul w₂.isLt
      omega
    have hi_eq := congrArg (· / 11) hd1
    have hr1 : i₁.val * 11 + (w₁.val / n - 1) = 11 * i₁.val + (w₁.val / n - 1) := by ring
    have hr2 : i₂.val * 11 + (w₂.val / n - 1) = 11 * i₂.val + (w₂.val / n - 1) := by ring
    rw [hr1, hr2, Nat.mul_add_div (by positivity), Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt hp1, Nat.div_eq_of_lt hp2] at hi_eq
    exact hne (Fin.ext (by omega))

theorem tcActiveIdxReg_disjoint {n m Q : ℕ} (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    {i₁ i₂ : Fin m} (hne : i₁ ≠ i₂) :
    (tcActiveIdxReg n m Q hQ i₁).DisjointWires (tcActiveIdxReg n m Q hQ i₂) := by
  rw [QRegister.disjoint_iff]
  intro a b heq
  have hval := congrArg Fin.val heq
  simp only [tcActiveIdxReg_apply_val] at hval
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · have hm : (i₁.val + 1) * (n + 1) ≤ i₂.val * (n + 1) := Nat.mul_le_mul_right (n + 1) h
    have hr : (i₁.val + 1) * (n + 1) = i₁.val * (n + 1) + (n + 1) := by ring
    have := a.isLt
    omega
  · have hm : (i₂.val + 1) * (n + 1) ≤ i₁.val * (n + 1) := Nat.mul_le_mul_right (n + 1) h
    have hr : (i₂.val + 1) * (n + 1) = i₂.val * (n + 1) + (n + 1) := by ring
    have := b.isLt
    omega

/-- Aggregated `m * n`-qubit active index register across all `m` slots (`0 < n`). -/
def tcAllActReg (n m Q : ℕ) (hn : 0 < n) (hQ : (n + 1) * m + 12 * m * n ≤ Q) :
    QRegister (m * n) Q where
  wires :=
    ⟨fun (w : Fin (m * n)) ↦
      tcActiveIdxReg n m Q hQ
        ⟨w.val / n, Nat.div_lt_of_lt_mul (show w.val < n * m by linarith [w.isLt])⟩
        ⟨w.val % n, Nat.mod_lt _ hn⟩, by
      intro w₁ w₂ hwire
      have heq := congrArg Fin.val hwire
      simp only [tcActiveIdxReg_apply_val] at heq
      have hm1 : w₁.val % n < n := Nat.mod_lt _ hn
      have hm2 : w₂.val % n < n := Nat.mod_lt _ hn
      have hd := congrArg (· / (n + 1)) heq
      have hr1 : (w₁.val / n) * (n + 1) + (1 + w₁.val % n) =
          (n + 1) * (w₁.val / n) + (1 + w₁.val % n) := by ring
      have hr2 : (w₂.val / n) * (n + 1) + (1 + w₂.val % n) =
          (n + 1) * (w₂.val / n) + (1 + w₂.val % n) := by ring
      have hd1 : (1 + w₁.val % n) / (n + 1) = 0 := Nat.div_eq_of_lt (by linarith)
      have hd2 : (1 + w₂.val % n) / (n + 1) = 0 := Nat.div_eq_of_lt (by linarith)
      rw [hr1, hr2, Nat.mul_add_div (by positivity), Nat.mul_add_div (by positivity),
        hd1, hd2, add_zero, add_zero] at hd
      rw [hd] at heq
      have hrem : w₁.val % n = w₂.val % n := by omega
      apply Fin.ext
      rw [← Nat.div_add_mod w₁.val n, ← Nat.div_add_mod w₂.val n, hd, hrem]⟩

@[simp]
theorem tcAllActReg_apply (n m Q : ℕ) (hn : 0 < n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (w : Fin (m * n)) :
    tcAllActReg n m Q hn hQ w =
      tcActiveIdxReg n m Q hQ
        ⟨w.val / n, Nat.div_lt_of_lt_mul (show w.val < n * m by linarith [w.isLt])⟩
        ⟨w.val % n, Nat.mod_lt _ hn⟩ := rfl

/-- Aggregated `m * n`-qubit passive storage register at index `p: Fin 11` (`0 < n`). -/
def tcAllPasReg (n m Q : ℕ) (hn : 0 < n) (hQ : (n + 1) * m + 12 * m * n ≤ Q) (p : Fin 11) :
    QRegister (m * n) Q where
  wires :=
    ⟨fun (w : Fin (m * n)) ↦
      tcPassiveReg n m Q hQ
        ⟨w.val / n, Nat.div_lt_of_lt_mul (show w.val < n * m by linarith [w.isLt])⟩ p
        ⟨w.val % n, Nat.mod_lt _ hn⟩, by
      intro w₁ w₂ hwire
      have heq := congrArg Fin.val hwire
      simp only [tcPassiveReg_apply_val] at heq
      have hm1 : w₁.val % n < n := Nat.mod_lt _ hn
      have hm2 : w₂.val % n < n := Nat.mod_lt _ hn
      have hsub : ((w₁.val / n) * 11 + p.val) * n + w₁.val % n =
          ((w₂.val / n) * 11 + p.val) * n + w₂.val % n := by omega
      have hr1 : ((w₁.val / n) * 11 + p.val) * n + w₁.val % n =
          n * ((w₁.val / n) * 11 + p.val) + w₁.val % n := by ring
      have hr2 : ((w₂.val / n) * 11 + p.val) * n + w₂.val % n =
          n * ((w₂.val / n) * 11 + p.val) + w₂.val % n := by ring
      have hd := congrArg (· / n) hsub
      rw [hr1, hr2, Nat.mul_add_div hn, Nat.mul_add_div hn, Nat.div_eq_of_lt hm1,
        Nat.div_eq_of_lt hm2, add_zero, add_zero] at hd
      have hq : w₁.val / n = w₂.val / n := by omega
      rw [hd] at hsub
      have hrem : w₁.val % n = w₂.val % n := Nat.add_left_cancel hsub
      apply Fin.ext
      rw [← Nat.div_add_mod w₁.val n, ← Nat.div_add_mod w₂.val n, hq, hrem]⟩

@[simp]
theorem tcAllPasReg_apply (n m Q : ℕ) (hn : 0 < n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (p : Fin 11) (w : Fin (m * n)) :
    tcAllPasReg n m Q hn hQ p w =
      tcPassiveReg n m Q hQ
        ⟨w.val / n, Nat.div_lt_of_lt_mul (show w.val < n * m by linarith [w.isLt])⟩ p
        ⟨w.val % n, Nat.mod_lt _ hn⟩ := rfl

/-- Aggregated `m`-qubit marker register across all `m` slots. -/
def tcAllMarkReg (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q) :
    QRegister m Q where
  wires :=
    ⟨fun (i : Fin m) ↦ tcMarkerReg n m Q hQ i 0, by
      intro i₁ i₂ hwire
      have heq := congrArg Fin.val hwire
      simp only [tcMarkerReg_apply_val, Fin.val_zero, add_zero] at heq
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) heq)⟩

@[simp]
theorem tcAllMarkReg_apply (n m Q : ℕ) (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) :
    tcAllMarkReg n m Q hQ i = tcMarkerReg n m Q hQ i 0 := rfl

/-- Aggregated `m`-qubit verification flag register at round `q: Fin 12`. -/
def tcAllVerifReg (n m Q : ℕ) (hn12 : 12 ≤ n) (hQ : (n + 1) * m + 12 * m * n ≤ Q) (q : Fin 12) :
    QRegister m Q where
  wires :=
    ⟨fun (i : Fin m) ↦ tcVerifFlagReg n m Q hn12 hQ i q 0, by
      intro i₁ i₂ hwire
      have heq := congrArg Fin.val hwire
      simp only [tcVerifFlagReg_apply_val, Fin.val_zero, add_zero] at heq
      exact Fin.ext (by omega)⟩

@[simp]
theorem tcAllVerifReg_apply (n m Q : ℕ) (hn12 : 12 ≤ n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (q : Fin 12) (i : Fin m) :
    tcAllVerifReg n m Q hn12 hQ q i = tcVerifFlagReg n m Q hn12 hQ i q 0 := rfl

theorem tcAllActReg_disjoint_pas {n m Q : ℕ} (hn : 0 < n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (p : Fin 11) :
    (tcAllActReg n m Q hn hQ).DisjointWires (tcAllPasReg n m Q hn hQ p) := by
  rw [QRegister.disjoint_iff]
  intro w₁ w₂ heq
  have hval := congrArg Fin.val heq
  simp only [tcAllActReg_apply, tcAllPasReg_apply, tcActiveIdxReg_apply_val,
    tcPassiveReg_apply_val] at hval
  have hdiv : w₁.val / n < m :=
    Nat.div_lt_of_lt_mul (show w₁.val < n * m by linarith [w₁.isLt])
  have hlt := tcActiveIdx_val_lt ⟨w₁.val / n, hdiv⟩ ⟨w₁.val % n, Nat.mod_lt _ hn⟩
  dsimp only at hlt
  omega

theorem tcAllMarkReg_disjoint_verif {n m Q : ℕ} (hn12 : 12 ≤ n)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (q : Fin 12) :
    (tcAllMarkReg n m Q hQ).DisjointWires (tcAllVerifReg n m Q hn12 hQ q) := by
  rw [QRegister.disjoint_iff]
  intro i₁ i₂ heq
  have hval := congrArg Fin.val heq
  simp only [tcAllMarkReg_apply, tcAllVerifReg_apply, tcMarkerReg_apply_val,
    tcVerifFlagReg_apply_val, Fin.val_zero, add_zero] at hval
  have hlt := tcMarker_val_lt (n := n) i₁
  omega

/-! ## 3. Coherent `m`-Slot `TensorConveyor` Pulses & `+d` Swap-Verification -/

/-- Basis state on `Fin (2 ^ Q)` packing `u: Fin m → Fin (2 ^ (n * d))` into
  `tcSlotConveyorReg`
  with `0` on all remaining wires. -/
noncomputable def tcPackConveyorBasis (n m d Q : ℕ) (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (u : Fin m → Fin (2 ^ (n * d))) : Fin (2 ^ Q) :=
  (List.finRange m).foldl
    (fun acc i ↦ (tcSlotConveyorReg n m d Q hn hd12 hQ i).replaceIndex acc (u i)) 0

theorem tcExtract_conveyor_pack (n m d Q : ℕ) (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (u : Fin m → Fin (2 ^ (n * d))) (j : Fin m) :
    (tcSlotConveyorReg n m d Q hn hd12 hQ j).extractIndex
      (tcPackConveyorBasis n m d Q hn hd12 hQ u) = u j := by
  have hfold : ∀ (l : List (Fin m)) (acc : Fin (2 ^ Q)), l.Nodup →
      (tcSlotConveyorReg n m d Q hn hd12 hQ j).extractIndex
        (l.foldl (fun a i ↦ (tcSlotConveyorReg n m d Q hn hd12 hQ i).replaceIndex a (u i)) acc) =
      if j ∈ l then u j else (tcSlotConveyorReg n m d Q hn hd12 hQ j).extractIndex acc := by
    intro l
    induction l with
    | nil => simp
    | cons i rest ih =>
        intro acc hl
        rcases List.nodup_cons.mp hl with ⟨hni, hrest⟩
        simp only [List.foldl_cons, ih _ hrest, List.mem_cons]
        by_cases hji : j = i
        · subst hji
          simp [QRegister.extractIndex_replaceIndex]
        · rw [(tcSlotConveyorReg n m d Q hn hd12 hQ j).extractIndex_replaceIndex_of_disjoint _
            (tcSlotConveyorReg_disjoint hn hd12 hQ hji)]
          simp [hji]
  rw [tcPackConveyorBasis, hfold (List.finRange m) 0 (List.nodup_finRange m),
    ite_eq_left (List.mem_finRange j)]

theorem tcBasisBits_pack_outside (n m d Q : ℕ) (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (u : Fin m → Fin (2 ^ (n * d)))
    {w : Wire Q} (hw : ∀ i : Fin m, w ∉ Set.range (tcSlotConveyorReg n m d Q hn hd12 hQ i).wires) :
    basisBits Q (tcPackConveyorBasis n m d Q hn hd12 hQ u) w = 0 := by
  have hfold : ∀ (l : List (Fin m)) (acc : Fin (2 ^ Q)),
      basisBits Q
        (l.foldl (fun a i ↦ (tcSlotConveyorReg n m d Q hn hd12 hQ i).replaceIndex a (u i)) acc) w =
      basisBits Q acc w := by
    intro l
    induction l with
    | nil => simp
    | cons i rest ih =>
        intro acc
        simp only [List.foldl_cons, ih]
        exact (tcSlotConveyorReg n m d Q hn hd12 hQ i).basisBits_replaceIndex_of_not_mem _ _ _
          (hw i)
  rw [tcPackConveyorBasis, hfold, basisBits_zero, Pi.zero_apply]

theorem tcMarkerWire_not_mem_conveyor {n m d Q : ℕ} (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (j i : Fin m) :
    tcMarkerReg n m Q hQ j 0 ∉ Set.range (tcSlotConveyorReg n m d Q hn hd12 hQ i).wires := by
  rintro ⟨w, heq⟩
  have hval := congrArg Fin.val heq
  have hm : w.val % n < n := Nat.mod_lt _ hn
  by_cases hq0 : w.val / n = 0
  · simp only [tcSlotConveyorReg_apply, hq0, ↓reduceDIte, tcActiveIdxReg_apply_val,
      tcMarkerReg_apply_val, Fin.val_zero, add_zero] at hval
    have hmod := congrArg (· % (n + 1)) hval
    have hr1 : i.val * (n + 1) + (1 + w.val % n) = (n + 1) * i.val + (1 + w.val % n) := by ring
    have hr2 : j.val * (n + 1) = (n + 1) * j.val + 0 := by ring
    have hm1 : (1 + w.val % n) % (n + 1) = 1 + w.val % n := Nat.mod_eq_of_lt (by linarith)
    have hm0 : 0 % (n + 1) = 0 := Nat.zero_mod _
    rw [hr1, hr2, Nat.mul_add_mod, Nat.mul_add_mod, hm1, hm0] at hmod
    omega
  · simp only [tcSlotConveyorReg_apply, hq0, ↓reduceDIte, tcPassiveReg_apply_val,
      tcMarkerReg_apply_val, Fin.val_zero, add_zero] at hval
    have hlt := tcMarker_val_lt (n := n) j
    omega

theorem tcVerifWire_not_mem_conveyor {n m d Q : ℕ} (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (j i : Fin m) (q : Fin 12) :
    tcVerifFlagReg n m Q hn12 hQ j q 0 ∉
      Set.range (tcSlotConveyorReg n m d Q (by omega) hd12 hQ i).wires := by
  rintro ⟨w, heq⟩
  have hval := congrArg Fin.val heq
  have hm : w.val % n < n := Nat.mod_lt _ (by omega)
  by_cases hq0 : w.val / n = 0
  · simp only [tcSlotConveyorReg_apply, hq0, ↓reduceDIte, tcActiveIdxReg_apply_val,
      tcVerifFlagReg_apply_val, Fin.val_zero, add_zero] at hval
    have hlt := tcActiveIdx_val_lt i ⟨w.val % n, hm⟩
    dsimp only at hlt
    omega
  · simp only [tcSlotConveyorReg_apply, hq0, ↓reduceDIte, tcPassiveReg_apply_val,
      tcVerifFlagReg_apply_val, Fin.val_zero, add_zero] at hval
    have hp : w.val / n - 1 < 11 := by
      have : w.val / n < d := Nat.div_lt_of_lt_mul w.isLt
      omega
    have hhi : (i.val * 11 + (w.val / n - 1)) * n + w.val % n < 11 * m * n := by
      have h1 : i.val * 11 + (w.val / n - 1) + 1 ≤ 11 * m := by
        calc i.val * 11 + (w.val / n - 1) + 1 ≤ i.val * 11 + 11 := by omega
          _ = (i.val + 1) * 11 := by ring
          _ ≤ m * 11 := Nat.mul_le_mul_right 11 i.isLt
          _ = 11 * m := by ring
      calc (i.val * 11 + (w.val / n - 1)) * n + w.val % n
          < (i.val * 11 + (w.val / n - 1)) * n + n := by omega
        _ = (i.val * 11 + (w.val / n - 1) + 1) * n := by ring
        _ ≤ (11 * m) * n := Nat.mul_le_mul_right n h1
        _ = 11 * m * n := by ring
    omega

/-- Terminal basis state after `d` swap-verification rounds on `u: Fin m → Fin (2 ^ (n *
  d))`:
  sets `tcVerifFlagReg i ⟨q, _⟩` to `1` iff `(localMemSlotReg n d q).extractIndex (u i) ∈
  R`. -/
noncomputable def tcPackVerifBasis (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    (u : Fin m → Fin (2 ^ (n * d))) : Fin (2 ^ Q) :=
  (basisBits Q).symm fun w ↦
    basisBits Q (tcPackConveyorBasis n m d Q (by omega) hd12 hQ u) w +
      ∑ i : Fin m, ∑ q : Fin d,
        if w = tcVerifFlagReg n m Q hn12 hQ i ⟨q.val, by omega⟩ 0 ∧
            (localMemSlotReg n d q).extractIndex (u i) ∈ R then
          1
        else
          0

theorem tcExtract_conveyor_packVerif (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    (u : Fin m → Fin (2 ^ (n * d))) (j : Fin m) :
    (tcSlotConveyorReg n m d Q (by omega) hd12 hQ j).extractIndex
      (tcPackVerifBasis n m d Q hn12 hd12 hQ R u) = u j := by
  apply (basisBits (n * d)).injective
  funext w
  rw [(tcSlotConveyorReg n m d Q (by omega) hd12 hQ j).basisBits_extractIndex, tcPackVerifBasis,
    Equiv.apply_symm_apply]
  have hsum0 : (∑ i : Fin m, ∑ q : Fin d,
      if tcSlotConveyorReg n m d Q (by omega) hd12 hQ j w =
          tcVerifFlagReg n m Q hn12 hQ i ⟨q.val, by omega⟩ 0 ∧
          (localMemSlotReg n d q).extractIndex (u i) ∈ R then (1 : ZMod 2) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun q _ ↦ ?_
    have hne : tcSlotConveyorReg n m d Q (by omega) hd12 hQ j w ≠
        tcVerifFlagReg n m Q hn12 hQ i ⟨q.val, by omega⟩ 0 := fun h ↦
      tcVerifWire_not_mem_conveyor hn12 hd12 hQ i j ⟨q.val, by omega⟩ ⟨w, h⟩
    simp only [hne, false_and, ↓reduceIte]
  rw [hsum0, add_zero, ← (tcSlotConveyorReg n m d Q (by omega) hd12 hQ j).basisBits_extractIndex,
    tcExtract_conveyor_pack]

theorem tcPackVerifBasis_injective (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n))) :
    Function.Injective (tcPackVerifBasis n m d Q hn12 hd12 hQ R) := by
  intro u₁ u₂ heq
  funext j
  have h := congrArg (tcSlotConveyorReg n m d Q (by omega) hd12 hQ j).extractIndex heq
  rwa [tcExtract_conveyor_packVerif, tcExtract_conveyor_packVerif] at h

/-- Generic product-state factoring lemma for a list of pairwise-disjoint register
  embeddings. -/
theorem listProd_embedMatrix_mulVec_pack {n m d Q : ℕ} (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (M : Fin m → Matrix (Fin (2 ^ (n * d))) (Fin (2 ^ (n * d))) ℂ)
    (ψ : Fin m → Fin (2 ^ (n * d)) → ℂ) :
    (((List.finRange m).map fun i ↦
        (tcSlotConveyorReg n m d Q hn hd12 hQ i).embedMatrix (M i)).prod) *ᵥ
      (∑ u : Fin m → Fin (2 ^ (n * d)),
        (∏ i : Fin m, ψ i (u i)) •
          Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ)) =
    ∑ u : Fin m → Fin (2 ^ (n * d)),
      (∏ i : Fin m, (M i *ᵥ ψ i) (u i)) •
        Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ) := by
  have hstep : ∀ (j : Fin m) (φ : Fin m → Fin (2 ^ (n * d)) → ℂ),
      (tcSlotConveyorReg n m d Q hn hd12 hQ j).embedMatrix (M j) *ᵥ
        (∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m, φ i (u i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ)) =
      ∑ u : Fin m → Fin (2 ^ (n * d)),
        (∏ i : Fin m, (if i = j then M j *ᵥ φ j else φ i) (u i)) •
          Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ) := by
    intro j φ
    set rj := tcSlotConveyorReg n m d Q hn hd12 hQ j
    rw [Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, rj.embedMatrix_mulVec_single_factors]
    have hexpand (u : Fin m → Fin (2 ^ (n * d))) :
        rj.tensorState (M j *ᵥ Pi.single (rj.extractIndex
            (tcPackConveyorBasis n m d Q hn hd12 hQ u)) 1)
          (Pi.single (rj.basisSplitEquiv (tcPackConveyorBasis n m d Q hn hd12 hQ u)).2 1) =
        ∑ x : Fin (2 ^ (n * d)),
          M j x (u j) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ (Function.update u j x)) 1 := by
      rw [tcExtract_conveyor_pack]
      have hlin : ∀ (v : Fin (2 ^ (n * d)) → ℂ),
          rj.tensorState v
            (Pi.single (rj.basisSplitEquiv (tcPackConveyorBasis n m d Q hn hd12 hQ u)).2 1) =
          ∑ x : Fin (2 ^ (n * d)),
            v x • Pi.single (rj.replaceIndex (tcPackConveyorBasis n m d Q hn hd12 hQ u) x) 1 := by
        intro v
        funext z
        rw [Finset.sum_apply]
        have hv : v = ∑ x : Fin (2 ^ (n * d)), v x • Pi.single x 1 := by
          funext x'; rw [Finset.sum_apply]; simp [Pi.single_apply]
        have hsum_eq :
            rj.tensorState (∑ x : Fin (2 ^ (n * d)), v x • Pi.single x 1)
              (Pi.single (rj.basisSplitEquiv (tcPackConveyorBasis n m d Q hn hd12 hQ u)).2 1) z =
            ∑ x : Fin (2 ^ (n * d)),
              (v x • rj.tensorState (Pi.single x 1)
                (Pi.single (rj.basisSplitEquiv
                  (tcPackConveyorBasis n m d Q hn hd12 hQ u)).2 1)) z := by
          simp [QRegister.tensorState, Finset.sum_apply, Finset.sum_mul, mul_assoc]
        conv_lhs => rw [hv]
        rw [hsum_eq]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [Pi.smul_apply, rj.tensorState_single_replaceIndex]
      rw [hlin]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hcol : (M j *ᵥ Pi.single (u j) 1) x = M j x (u j) := by
        rw [Matrix.mulVec_single_one, Matrix.col_apply]
      have hrep : rj.replaceIndex (tcPackConveyorBasis n m d Q hn hd12 hQ u) x =
          tcPackConveyorBasis n m d Q hn hd12 hQ (Function.update u j x) := by
        apply (basisBits Q).injective
        funext w
        by_cases hwj : w ∈ Set.range rj.wires
        · obtain ⟨b, rfl⟩ := hwj
          rw [rj.basisBits_replaceIndex_apply, ← rj.basisBits_extractIndex,
            tcExtract_conveyor_pack, Function.update_self]
        · rw [rj.basisBits_replaceIndex_of_not_mem _ _ _ hwj]
          by_cases hwi : ∃ i : Fin m,
              w ∈ Set.range (tcSlotConveyorReg n m d Q hn hd12 hQ i).wires
          · obtain ⟨i, b, rfl⟩ := hwi
            have hij : i ≠ j := fun h ↦ hwj (h ▸ ⟨b, rfl⟩)
            rw [← (tcSlotConveyorReg n m d Q hn hd12 hQ i).basisBits_extractIndex,
              ← (tcSlotConveyorReg n m d Q hn hd12 hQ i).basisBits_extractIndex,
              tcExtract_conveyor_pack, tcExtract_conveyor_pack, Function.update_of_ne hij]
          · push Not at hwi
            rw [tcBasisBits_pack_outside n m d Q hn hd12 hQ _ hwi,
              tcBasisBits_pack_outside n m d Q hn hd12 hQ _ hwi]
      rw [hcol, hrep]
    simp_rw [hexpand, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    -- Reindex `(x, u)` by `u' = Function.update u j x` and `y = u j`
    symm
    calc ∑ u' : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m, (if i = j then M j *ᵥ φ j else φ i) (u' i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u') (1 : ℂ)
        = ∑ u' : Fin m → Fin (2 ^ (n * d)), ∑ y : Fin (2 ^ (n * d)),
            ((∏ i ∈ Finset.univ.erase j, φ i (u' i)) * (M j (u' j) y * φ j y)) •
              Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u') (1 : ℂ) := by
          refine Finset.sum_congr rfl fun u' _ ↦ ?_
          rw [← Finset.sum_smul]
          congr 1
          rw [← Finset.mul_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
          simp only [↓reduceIte]
          have hmv : (M j *ᵥ φ j) (u' j) = ∑ y : Fin (2 ^ (n * d)), M j (u' j) y * φ j y := rfl
          rw [hmv]
          have hrest : (∏ x ∈ Finset.univ.erase j,
              (if x = j then M j *ᵥ φ j else φ x) (u' x)) =
              ∏ x ∈ Finset.univ.erase j, φ x (u' x) :=
            Finset.prod_congr rfl fun x hx ↦ by simp [Finset.ne_of_mem_erase hx]
          rw [hrest, mul_comm]
      _ = ∑ x : Fin (2 ^ (n * d)), ∑ u : Fin m → Fin (2 ^ (n * d)),
            ((∏ i : Fin m, φ i (u i)) * M j x (u j)) •
              Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ (Function.update u j x)) 1 := by
          rw [Finset.sum_sigma', Finset.sum_sigma']
          refine Finset.sum_bij
            (fun (p : Σ _ : Fin m → Fin (2 ^ (n * d)), Fin (2 ^ (n * d))) _ ↦
              ⟨p.1 j, Function.update p.1 j p.2⟩)
            (fun _ _ ↦ Finset.mem_univ _)
            (fun p₁ _ p₂ _ heq ↦ ?_)
            (fun q _ ↦ ⟨⟨Function.update q.2 j q.1, q.2 j⟩, Finset.mem_univ _, ?_⟩)
            (fun p _ ↦ ?_)
          · simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
            rcases heq with ⟨hj_eq, hupd⟩
            have hp2 : p₁.2 = p₂.2 := by
              have h := congrFun hupd j
              simpa using h
            have hp1 : p₁.1 = p₂.1 := by
              funext i
              by_cases hij : i = j
              · subst hij; exact hj_eq
              · have h := congrFun hupd i
                simpa [hij] using h
            exact Sigma.ext hp1 (heq_of_eq hp2)
          · simp
          · simp only [Function.update_idem, Function.update_eq_self]
            congr 1
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
            have her : (∏ i ∈ Finset.univ.erase j, φ i (Function.update p.1 j p.2 i)) =
                ∏ i ∈ Finset.univ.erase j, φ i (p.1 i) :=
              Finset.prod_congr rfl fun i hi ↦ by simp [Finset.ne_of_mem_erase hi]
            rw [her, Function.update_self]
            ring
  have hlist : ∀ (l : List (Fin m)), l.Nodup →
      ((l.map fun i ↦ (tcSlotConveyorReg n m d Q hn hd12 hQ i).embedMatrix (M i)).prod) *ᵥ
        (∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m, ψ i (u i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ)) =
      ∑ u : Fin m → Fin (2 ^ (n * d)),
        (∏ i : Fin m, (if i ∈ l then M i *ᵥ ψ i else ψ i) (u i)) •
          Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ) := by
    intro l
    induction l with
    | nil => simp
    | cons j rest ih =>
        intro hl
        rcases List.nodup_cons.mp hl with ⟨hni, hrest⟩
        rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih hrest, hstep]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        congr 1
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        by_cases hij : i = j
        · subst hij; simp [hni]
        · simp [hij]
  simpa [List.mem_finRange] using hlist (List.finRange m) (List.nodup_finRange m)

/-- Zero-cost real-unitary `.step` wrapper `phaseI U`. -/
noncomputable def tcRealStep {Var : Type} {Q w : ℕ} (U : Unitary (2 ^ Q)) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w :=
  .step (phaseI U)

/-- Single parallel active-head Grover iteration across all `m` slots (`1` oracle query). -/
noncomputable def tcParallelGroverStep {Var : Type} (n m Q : ℕ)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  let fc := (tcOracleReg n m Q hQ).embedUnitary (flagConj n m)
  let diff := ((List.finRange m).map fun i ↦
    (tcActiveIdxReg n m Q hQ i).embedUnitary (Grover.diffuserUnitary (n := n))).prod
  .seq (tcRealStep fc)
    (.seq (.oracle (tcOracleReg n m Q hQ))
      (.seq (tcRealStep fc) (tcRealStep diff)))

/-- `K` repeated parallel active-head Grover iterations (`K` oracle queries). -/
noncomputable def tcParallelGroverIter {Var : Type} (n m Q : ℕ)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) :
    ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)
  | 0 => .skip
  | K + 1 => .seq (tcParallelGroverIter n m Q hQ K) (tcParallelGroverStep n m Q hQ)

/-- `t` coherent `TensorConveyor` pulses across all `m` slots (`t * K_blk` oracle queries). -/
noncomputable def tcPulsesBodyCircuit {Var : Type} (n m d Q : ℕ) (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) :
    ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)
  | 0 => .skip
  | t + 1 =>
      let inter := ((List.finRange m).map fun i ↦
        (tcSlotConveyorReg n m d Q hn hd12 hQ i).embedUnitary
          (tcIntertwinerUnitary n d (uFn t))).prod
      .seq (tcPulsesBodyCircuit n m d Q hn hd12 hQ K_blk uFn t)
        (.seq (tcParallelGroverIter n m Q hQ K_blk) (tcRealStep inter))

/-- Full `steps`-pulse preparation + evolution circuit (`steps * K_blk` oracle queries). -/
noncomputable def tcPulsesCircuit {Var : Type} (n m d Q : ℕ) (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  let initH := ((List.finRange m).map fun i ↦
    (tcSlotConveyorReg n m d Q hn hd12 hQ i).embedUnitary (hadamardUnitary (q := n * d))).prod
  .seq (tcRealStep initH) (tcPulsesBodyCircuit n m d Q hn hd12 hQ K_blk uFn steps)

/-- Single swap-verification round `q < d` (`1` oracle query). -/
noncomputable def tcVerifRoundCircuit {Var : Type} (n m Q : ℕ) (hn12 : 12 ≤ n)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (q : ℕ) (hq : q < 12) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  let swapAddr : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
    if hq0 : q = 0 then
      .skip
    else
      tcRealStep (permutationUnitary
        (tcSwapRegsEquiv (tcAllActReg n m Q (by omega) hQ)
          (tcAllPasReg n m Q (by omega) hQ ⟨q - 1, by omega⟩)
          (tcAllActReg_disjoint_pas (by omega) hQ ⟨q - 1, by omega⟩)))
  let swapFlag := tcRealStep (permutationUnitary
    (tcSwapRegsEquiv (tcAllMarkReg n m Q hQ)
      (tcAllVerifReg n m Q hn12 hQ ⟨q, hq⟩)
      (tcAllMarkReg_disjoint_verif hn12 hQ ⟨q, hq⟩)))
  .seq swapAddr (.seq (.oracle (tcOracleReg n m Q hQ)) (.seq swapFlag swapAddr))

/-- First `cnt` swap-verification rounds `0.. cnt - 1` (`cnt` oracle queries). -/
noncomputable def tcVerifCircuit {Var : Type} (n m Q : ℕ) (hn12 : 12 ≤ n)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) :
    (cnt : ℕ) → (cnt ≤ 12) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)
  | 0, _ => .skip
  | q + 1, hq =>
      .seq (tcVerifCircuit n m Q hn12 hQ q (by omega))
        (tcVerifRoundCircuit n m Q hn12 hQ q (by omega))

/-- Full single-attempt coherent `TensorConveyor` + `+d` verification circuit (before
  reset). -/
noncomputable def tcAttemptUnitaryCircuit {Var : Type} (n m d Q : ℕ) (hn12 : 12 ≤ n)
    (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  .seq (tcPulsesCircuit n m d Q (by omega) hd12 hQ K_blk uFn steps)
    (tcVerifCircuit n m Q hn12 hQ d hd12)

theorem zeroStepCost_tcAttemptUnitaryCircuit {Var : Type} (n m d Q : ℕ) (hn12 : 12 ≤ n)
    (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ) :
    ZeroStepCost (tcAttemptUnitaryCircuit (Var := Var) n m d Q hn12 hd12 hQ K_blk uFn steps) := by
  have hstep : ZeroStepCost (tcParallelGroverStep (Var := Var) n m Q hQ) := by
    refine ⟨zeroStepCost_step_phaseI (isRealMatrix_embedMatrix _ (isRealMatrix_flagConj n m)),
      trivial,
      zeroStepCost_step_phaseI (isRealMatrix_embedMatrix _ (isRealMatrix_flagConj n m)),
      zeroStepCost_step_phaseI (isRealMatrix_listProd _ ?_)⟩
    intro U hU
    rw [List.mem_map] at hU
    obtain ⟨i, _, rfl⟩ := hU
    exact isRealMatrix_embedMatrix _ (isRealMatrix_diffuserMatrix n)
  have hiter : ∀ K, ZeroStepCost (tcParallelGroverIter (Var := Var) n m Q hQ K) := by
    intro K; induction K with
    | zero => trivial
    | succ K ih => exact ⟨ih, hstep⟩
  have hpulses : ∀ t,
      ZeroStepCost (tcPulsesBodyCircuit (Var := Var) n m d Q (by omega) hd12 hQ K_blk uFn t) := by
    intro t; induction t with
    | zero => trivial
    | succ t ih =>
        refine ⟨ih, hiter K_blk, zeroStepCost_step_phaseI (isRealMatrix_listProd _ ?_)⟩
        intro U hU
        rw [List.mem_map] at hU
        obtain ⟨i, _, rfl⟩ := hU
        exact isRealMatrix_embedMatrix _ (isRealMatrix_tcIntertwinerUnitary n d (uFn t))
  have hinit : ZeroStepCost (tcPulsesCircuit (Var := Var) n m d Q (by omega) hd12 hQ K_blk uFn
      steps) := by
    refine ⟨zeroStepCost_step_phaseI (isRealMatrix_listProd _ ?_), hpulses steps⟩
    intro U hU
    rw [List.mem_map] at hU
    obtain ⟨i, _, rfl⟩ := hU
    exact isRealMatrix_embedMatrix _ (isRealMatrix_hadamardMatrix (n * d))
  have hverif : ∀ cnt (hcnt : cnt ≤ 12),
      ZeroStepCost (tcVerifCircuit (Var := Var) n m Q hn12 hQ cnt hcnt) := by
    intro cnt; induction cnt with
    | zero => intro _; trivial
    | succ q ih =>
        intro hq
        refine ⟨ih (by omega), ?_⟩
        unfold tcVerifRoundCircuit
        let permA (hq0 : q ≠ 0) :=
          tcSwapRegsEquiv (tcAllActReg n m Q (by omega) hQ)
            (tcAllPasReg n m Q (by omega) hQ ⟨q - 1, by omega⟩)
            (tcAllActReg_disjoint_pas (by omega) hQ ⟨q - 1, by omega⟩)
        let permF :=
          tcSwapRegsEquiv (tcAllMarkReg n m Q hQ)
            (tcAllVerifReg n m Q hn12 hQ ⟨q, by omega⟩)
            (tcAllMarkReg_disjoint_verif hn12 hQ ⟨q, by omega⟩)
        have hsa : ZeroStepCost (if hq0 : q = 0 then (.skip :
            OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
            else tcRealStep (permutationUnitary (permA hq0))) := by
          split_ifs with hq0
          · trivial
          · exact zeroStepCost_step_phaseI (isRealMatrix_permutationUnitary (permA hq0))
        exact ⟨hsa, trivial,
          zeroStepCost_step_phaseI (isRealMatrix_permutationUnitary permF), hsa⟩
  exact ⟨hinit, hverif d hd12⟩

/-- Effective unitary compiled by an `OracleDynamicCircuit` with no
  measurements/branches/loops. -/
noncomputable def tcCompileUnitary {Var : Type} {Q w : ℕ} (oracle : Unitary (2 ^ w)) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w → Option (Unitary (2 ^ Q))
  | .skip => some 1
  | .step U => some U
  | .oracle reg => some (reg.embedUnitary oracle)
  | .measure _ _ => none
  | .seq c₁ c₂ =>
      (tcCompileUnitary oracle c₁).bind fun U₁ ↦
        (tcCompileUnitary oracle c₂).bind fun U₂ ↦
          some (U₂ * U₁)
  | @OracleDynamicCircuit.qIf _ _ _ _ _ _ _ _ => none
  | @OracleDynamicCircuit.qWhile _ _ _ _ _ _ _ => none

theorem wp_of_tcCompileUnitary_eq_some {Var : Type} [DecidableEq Var] {Q w : ℕ}
    (oracle : Unitary (2 ^ w)) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
    {U : Unitary (2 ^ Q)} (hU : tcCompileUnitary oracle c = some U)
    (Θ : CQAssertion (Store Var) (2 ^ Q)) :
    wp (c.compile QProg.qAssign oracle) Θ = Θ.qAssign U := by
  induction c generalizing U Θ with
  | «skip» =>
      dsimp only [tcCompileUnitary] at hU
      injection hU with hU
      subst hU
      simp [OracleDynamicCircuit.compile_skip, wp_skip]
  | «step» V =>
      dsimp only [tcCompileUnitary] at hU
      injection hU with hU
      subst hU
      simp [OracleDynamicCircuit.compile_step, wp_qAssign]
  | «oracle» reg =>
      dsimp only [tcCompileUnitary] at hU
      injection hU with hU
      subst hU
      simp [OracleDynamicCircuit.compile_oracle, wp_qAssign]
  | «measure» _ _ => simp [tcCompileUnitary] at hU
  | «seq» c₁ c₂ ih₁ ih₂ =>
      simp only [tcCompileUnitary, Option.bind_eq_some_iff, Option.some.injEq] at hU
      obtain ⟨U₁, h1, U₂, h2, rfl⟩ := hU
      rw [OracleDynamicCircuit.compile_seq, wp_qSeq, ih₂ h2, ih₁ h1, CQAssertion.qAssign_qAssign]
  | «qIf» _ _ _ => simp [tcCompileUnitary] at hU
  | «qWhile» _ _ => simp [tcCompileUnitary] at hU

/-- Count of `.oracle` nodes in a loop/branch-free circuit. -/
noncomputable def tcOracleCount {Var : Type} {Q w : ℕ} :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w → ℕ
  | .skip => 0
  | .step _ => 0
  | .oracle _ => 1
  | .measure _ _ => 0
  | .seq c₁ c₂ => tcOracleCount c₁ + tcOracleCount c₂
  | @OracleDynamicCircuit.qIf _ _ _ _ _ _ c₁ c₂ => max (tcOracleCount c₁) (tcOracleCount c₂)
  | @OracleDynamicCircuit.qWhile _ _ _ _ _ _ _ => 0

theorem costBound_of_zeroStepCost_noWhile {Var : Type} [DecidableEq Var] {Q w : ℕ}
    {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1)
    {c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w}
    (hzero : ZeroStepCost c)
    (hnowhile : ∀ {V : Unitary (2 ^ w)}, (tcCompileUnitary V c).isSome = true) :
    CostBound (CostModel.ofEmbeddedOracle oracle) (c.compile QProg.qAssign oracle)
      (tcOracleCount c : ℝ≥0) := by
  induction c with
  | «skip» =>
      intro Δ; simp [tcOracleCount]
  | «step» U =>
      intro Δ
      simp only [OracleDynamicCircuit.compile_step, expectedCost_qAssign, hzero horacle,
        tcOracleCount, Nat.cast_zero, mul_zero]
      exact zero_le
  | «oracle» reg =>
      intro Δ
      simp [OracleDynamicCircuit.compile_oracle, expectedCost_qAssign,
        CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary, tcOracleCount]
  | «measure» _ _ =>
      have h := @hnowhile oracle
      simp [tcCompileUnitary] at h
  | «seq» c₁ c₂ ih₁ ih₂ =>
      have hcb := CostBound.seq (ih₁ hzero.1 ?_) (ih₂ hzero.2 ?_)
      · simpa [OracleDynamicCircuit.compile_seq, tcOracleCount, Nat.cast_add] using hcb
      · intro V
        have hs := @hnowhile V
        simp only [tcCompileUnitary, Option.isSome_iff_exists,
          Option.bind_eq_some_iff] at hs ⊢
        obtain ⟨_, Wa, ha, _, _, _⟩ := hs
        exact ⟨Wa, ha⟩
      · intro V
        have hs := @hnowhile V
        simp only [tcCompileUnitary, Option.isSome_iff_exists,
          Option.bind_eq_some_iff] at hs ⊢
        obtain ⟨_, _, _, Wb, hb, _⟩ := hs
        exact ⟨Wb, hb⟩
  | «qIf» _ _ _ =>
      have h := @hnowhile oracle
      simp [tcCompileUnitary] at h
  | «qWhile» _ _ =>
      have h := @hnowhile oracle
      simp [tcCompileUnitary] at h

theorem tcOracleCount_attempt (Var : Type) (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ) :
    tcOracleCount (tcAttemptUnitaryCircuit (Var := Var) n m d Q hn12 hd12 hQ K_blk uFn steps) =
      steps * K_blk + d := by
  have hstep : tcOracleCount (tcParallelGroverStep (Var := Var) n m Q hQ) = 1 := rfl
  have hiter : ∀ K, tcOracleCount (tcParallelGroverIter (Var := Var) n m Q hQ K) = K := by
    intro K; induction K with
    | zero => rfl
    | succ K ih => simp [tcParallelGroverIter, tcOracleCount, ih, hstep]
  have hpulses : ∀ t,
      tcOracleCount
        (tcPulsesBodyCircuit (Var := Var) n m d Q (by omega) hd12 hQ K_blk uFn t) =
      t * K_blk := by
    intro t; induction t with
    | zero => simp [tcPulsesBodyCircuit, tcOracleCount]
    | succ t ih =>
        simp [tcPulsesBodyCircuit, tcOracleCount, tcRealStep, ih, hiter, Nat.succ_mul]
  have hverif : ∀ cnt (hcnt : cnt ≤ 12),
      tcOracleCount (tcVerifCircuit (Var := Var) n m Q hn12 hQ cnt hcnt) = cnt := by
    intro cnt; induction cnt with
    | zero => intro _; rfl
    | succ q ih =>
        intro hq
        have hr : tcOracleCount (tcVerifRoundCircuit (Var := Var) n m Q hn12 hQ q (by omega)) =
            1 := by
          unfold tcVerifRoundCircuit
          by_cases hq0 : q = 0 <;> simp [hq0, tcOracleCount, tcRealStep]
        simp [tcVerifCircuit, tcOracleCount, ih (by omega), hr]
  simp [tcAttemptUnitaryCircuit, tcPulsesCircuit, tcOracleCount, tcRealStep, hpulses, hverif]

/-- Unitary compiled by `tcAttemptUnitaryCircuit` (up to global phase `i ^ _`, absorbed
  below). -/
theorem tcAttemptUnitaryCircuit_isSome {Var : Type} (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) :
    (tcCompileUnitary oracle
      (tcAttemptUnitaryCircuit (Var := Var) n m d Q hn12 hd12 hQ K_blk uFn steps)).isSome =
      true := by
  have hseq {c₁ c₂ : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)}
      (h1 : (tcCompileUnitary oracle c₁).isSome = true)
      (h2 : (tcCompileUnitary oracle c₂).isSome = true) :
      (tcCompileUnitary oracle (.seq c₁ c₂)).isSome = true := by
    rw [Option.isSome_iff_exists] at h1 h2 ⊢
    obtain ⟨U₁, h1⟩ := h1; obtain ⟨U₂, h2⟩ := h2
    exact ⟨U₂ * U₁, by simp [tcCompileUnitary, h1, h2]⟩
  have hstep : (tcCompileUnitary oracle
      (tcParallelGroverStep (Var := Var) n m Q hQ)).isSome = true := rfl
  have hiter : ∀ K, (tcCompileUnitary oracle
      (tcParallelGroverIter (Var := Var) n m Q hQ K)).isSome = true := by
    intro K; induction K with
    | zero => rfl
    | succ K ih => exact hseq ih hstep
  have hpulses : ∀ t, (tcCompileUnitary oracle
      (tcPulsesBodyCircuit (Var := Var) n m d Q (by omega) hd12 hQ K_blk uFn t)).isSome = true := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => exact hseq ih (hseq (hiter K_blk) rfl)
  have hverif : ∀ cnt (hcnt : cnt ≤ 12), (tcCompileUnitary oracle
      (tcVerifCircuit (Var := Var) n m Q hn12 hQ cnt hcnt)).isSome = true := by
    intro cnt; induction cnt with
    | zero => intro _; rfl
    | succ q ih =>
        intro hq
        refine hseq (ih (by omega)) ?_
        unfold tcVerifRoundCircuit
        let permA (hq0 : q ≠ 0) :=
          tcSwapRegsEquiv (tcAllActReg n m Q (by omega) hQ)
            (tcAllPasReg n m Q (by omega) hQ ⟨q - 1, by omega⟩)
            (tcAllActReg_disjoint_pas (by omega) hQ ⟨q - 1, by omega⟩)
        have hsa : (tcCompileUnitary oracle
            (if hq0 : q = 0 then (.skip :
              OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
              else tcRealStep (permutationUnitary (permA hq0)))).isSome = true := by
          split_ifs <;> rfl
        exact hseq hsa (hseq rfl (hseq rfl hsa))
  exact hseq (hseq rfl (hpulses steps)) (hverif d hd12)

/-- Parallel active-head Grover step acts as `∏_i (tcActiveIdxReg i).embedMatrix (groverStep
  R)`
  on every basis vector `Pi.single z 1` whose `m` marker bits are `0` (up to global phase `i
  ^ 3`). -/
theorem tcParallelGroverStep_mulVec_cleanMarker {Var : Type} (n m Q : ℕ)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    {U : Unitary (2 ^ Q)}
    (hU : tcCompileUnitary (parallelMarkingOracle m R)
      (tcParallelGroverStep (Var := Var) n m Q hQ) = some U) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ z : Fin (2 ^ Q),
      (∀ i : Fin m, (tcMarkerReg n m Q hQ i).extractIndex z = 0) →
      U.1 *ᵥ Pi.single z 1 =
        γ • ((((List.finRange m).map fun i ↦
          (tcActiveIdxReg n m Q hQ i).embedMatrix (groverStepUnitary R).1).prod) *ᵥ
          Pi.single z 1) := by
  dsimp only [tcParallelGroverStep, tcRealStep, tcCompileUnitary, Option.bind] at hU
  injection hU with hU
  subst hU
  refine ⟨Complex.I * Complex.I * Complex.I, by simp, fun z hz ↦ ?_⟩
  simp only [Submonoid.coe_mul, phaseI_val]
  set rOr := tcOracleReg n m Q hQ
  set diffL := (List.finRange m).map fun i ↦
    (tcActiveIdxReg n m Q hQ i).embedUnitary (Grover.diffuserUnitary (n := n))
  have hconj :
      (rOr.embedUnitary (flagConj n m)).1 *ᵥ
        ((rOr.embedUnitary (parallelMarkingOracle m R)).1 *ᵥ
          ((rOr.embedUnitary (flagConj n m)).1 *ᵥ Pi.single z 1)) =
      (∏ i : Fin m, if (tcActiveIdxReg n m Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) •
        Pi.single z 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hem : (rOr.embedUnitary (flagConj n m)).1 *
        (rOr.embedUnitary (parallelMarkingOracle m R)).1 *
        (rOr.embedUnitary (flagConj n m)).1 = rOr.embedMatrix (sDiagM n m R) := by
      change rOr.embedMatrix (flagConj n m).1 *
        rOr.embedMatrix (parallelMarkingOracle m R).1 *
        rOr.embedMatrix (flagConj n m).1 = _
      rw [← rOr.embedMatrix_mul, ← rOr.embedMatrix_mul,
        flagConj_mul_parallelMarkingOracle_mul_flagConj]
    rw [hem, rOr.embedMatrix_mulVec_single_factors]
    have hdiag : sDiagM n m R *ᵥ Pi.single (rOr.extractIndex z) 1 =
        (∏ i : Fin m, if (tcActiveIdxReg n m Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) •
          Pi.single (rOr.extractIndex z) 1 := by
      have hval :
          (∏ i : Fin m,
              slotDiag n R ((localSlotReg n m i).extractIndex (rOr.extractIndex z))) =
            ∏ i : Fin m,
              if (tcActiveIdxReg n m Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1 := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        unfold slotDiag
        have hm0 : (localMarkerReg n).extractIndex
            ((localSlotReg n m i).extractIndex (rOr.extractIndex z)) = 0 := by
          have h := hz i
          rw [tcMarkerReg, tcSlotOracleReg, QRegister.extractIndex_compose,
            QRegister.extractIndex_compose] at h
          exact h
        have hxu : (localIdxReg n).extractIndex
            ((localSlotReg n m i).extractIndex (rOr.extractIndex z)) =
            (tcActiveIdxReg n m Q hQ i).extractIndex z := by
          rw [tcActiveIdxReg, tcSlotOracleReg, QRegister.extractIndex_compose,
            QRegister.extractIndex_compose]
        rw [hm0, hxu]
        simp
      rw [sDiagM, Matrix.diagonal_mulVec_single, mul_one, hval]
      funext j
      by_cases hj : j = rOr.extractIndex z <;> simp [hj]
    rw [hdiag, rOr.tensorState_smul_left, rOr.tensorState_single_replaceIndex,
      rOr.replaceIndex_extractIndex]
  have hphase_pull :
      ((Complex.I • diffL.prod.1) *
        (Complex.I • (rOr.embedUnitary (flagConj n m)).1) *
        (rOr.embedUnitary (parallelMarkingOracle m R)).1 *
        (Complex.I • (rOr.embedUnitary (flagConj n m)).1)) *ᵥ Pi.single z 1 =
      (Complex.I * Complex.I * Complex.I) •
        (diffL.prod.1 *ᵥ
          ((rOr.embedUnitary (flagConj n m)).1 *ᵥ
            ((rOr.embedUnitary (parallelMarkingOracle m R)).1 *ᵥ
              ((rOr.embedUnitary (flagConj n m)).1 *ᵥ Pi.single z 1)))) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  rw [hphase_pull, hconj, Matrix.mulVec_smul]
  congr 1
  have hcomm_step : ∀ (l : List (Fin m)), l.Nodup →
      ((l.map fun i ↦ (tcActiveIdxReg n m Q hQ i).embedMatrix
          (Grover.diffuserUnitary (n := n)).1).prod) *ᵥ
        ((∏ i ∈ l.toFinset,
            if (tcActiveIdxReg n m Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) •
          Pi.single z 1) =
      ((l.map fun i ↦ (tcActiveIdxReg n m Q hQ i).embedMatrix
          (groverStepUnitary R).1).prod) *ᵥ Pi.single z 1 := by
    intro l hl
    have hor : ((l.map fun i ↦ (tcActiveIdxReg n m Q hQ i).embedMatrix
          (setOracleUnitary R).1).prod) *ᵥ Pi.single z 1 =
        (∏ i ∈ l.toFinset,
            if (tcActiveIdxReg n m Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) •
          Pi.single z 1 := by
      induction l with
      | nil =>
          rw [List.map_nil, List.prod_nil, Matrix.one_mulVec, List.toFinset_nil,
            Finset.prod_empty, one_smul]
      | cons i rest ih =>
          rcases List.nodup_cons.mp hl with ⟨hni, hrest⟩
          rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih hrest, Matrix.mulVec_smul,
            List.toFinset_cons, Finset.prod_insert (List.mem_toFinset.not.mpr hni)]
          have h1 : (tcActiveIdxReg n m Q hQ i).embedMatrix (setOracleUnitary R).1 *ᵥ
              Pi.single z 1 =
              (if (tcActiveIdxReg n m Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) •
                Pi.single z 1 := by
            rw [(tcActiveIdxReg n m Q hQ i).embedMatrix_mulVec_single_factors,
              setOracleUnitary]
            change (tcActiveIdxReg n m Q hQ i).tensorState
              (setOracleMatrix R *ᵥ Pi.single ((tcActiveIdxReg n m Q hQ i).extractIndex z) 1) _ = _
            rw [setOracleMatrix, Matrix.diagonal_mulVec_single, mul_one]
            have hsingle :
                Pi.single ((tcActiveIdxReg n m Q hQ i).extractIndex z)
                  (if (tcActiveIdxReg n m Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) =
                (if (tcActiveIdxReg n m Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) •
                  Pi.single ((tcActiveIdxReg n m Q hQ i).extractIndex z) 1 := by
              funext j
              by_cases hj : j = (tcActiveIdxReg n m Q hQ i).extractIndex z <;>
                simp [hj]
            rw [hsingle, (tcActiveIdxReg n m Q hQ i).tensorState_smul_left,
              (tcActiveIdxReg n m Q hQ i).tensorState_single_replaceIndex,
              (tcActiveIdxReg n m Q hQ i).replaceIndex_extractIndex]
          rw [h1, smul_smul, mul_comm]
    have hprod_mul :
        ((l.map fun i ↦ (tcActiveIdxReg n m Q hQ i).embedMatrix
            (Grover.diffuserUnitary (n := n)).1).prod) *
          ((l.map fun i ↦ (tcActiveIdxReg n m Q hQ i).embedMatrix
            (setOracleUnitary R).1).prod) =
        (l.map fun i ↦ (tcActiveIdxReg n m Q hQ i).embedMatrix
          (groverStepUnitary R).1).prod := by
      clear hor
      induction l with
      | nil => simp
      | cons i rest ih =>
          rcases List.nodup_cons.mp hl with ⟨hni, hrest⟩
          simp only [List.map_cons, List.prod_cons]
          have hcomm_rest :
              ((rest.map fun j ↦ (tcActiveIdxReg n m Q hQ j).embedMatrix
                  (Grover.diffuserUnitary (n := n)).1).prod) *
                (tcActiveIdxReg n m Q hQ i).embedMatrix (setOracleUnitary R).1 =
              (tcActiveIdxReg n m Q hQ i).embedMatrix (setOracleUnitary R).1 *
                ((rest.map fun j ↦ (tcActiveIdxReg n m Q hQ j).embedMatrix
                  (Grover.diffuserUnitary (n := n)).1).prod) := by
            clear ih hl
            induction rest with
            | nil => simp
            | cons j rs ihrs =>
                rcases List.nodup_cons.mp hrest with ⟨_, hrs⟩
                have hij : j ≠ i := fun h ↦ hni (h ▸ List.mem_cons_self)
                have hni' : i ∉ rs := fun h ↦ hni (List.mem_cons_of_mem j h)
                simp only [List.map_cons, List.prod_cons, Matrix.mul_assoc]
                rw [ihrs hni' hrs, ← Matrix.mul_assoc,
                  QRegister.embedMatrix_comm_of_disjoint _ _
                    (tcActiveIdxReg_disjoint hQ hij),
                  Matrix.mul_assoc]
          calc _ = (tcActiveIdxReg n m Q hQ i).embedMatrix (Grover.diffuserUnitary (n := n)).1 *
                    (((rest.map fun j ↦ (tcActiveIdxReg n m Q hQ j).embedMatrix
                        (Grover.diffuserUnitary (n := n)).1).prod) *
                      (tcActiveIdxReg n m Q hQ i).embedMatrix (setOracleUnitary R).1) *
                    ((rest.map fun j ↦ (tcActiveIdxReg n m Q hQ j).embedMatrix
                      (setOracleUnitary R).1).prod) := by simp [Matrix.mul_assoc]
            _ = ((tcActiveIdxReg n m Q hQ i).embedMatrix (Grover.diffuserUnitary (n := n)).1 *
                  (tcActiveIdxReg n m Q hQ i).embedMatrix (setOracleUnitary R).1) *
                  (((rest.map fun j ↦ (tcActiveIdxReg n m Q hQ j).embedMatrix
                      (Grover.diffuserUnitary (n := n)).1).prod) *
                    ((rest.map fun j ↦ (tcActiveIdxReg n m Q hQ j).embedMatrix
                      (setOracleUnitary R).1).prod)) := by
                  rw [hcomm_rest]; simp [Matrix.mul_assoc]
            _ = _ := by
                  rw [← QRegister.embedMatrix_mul, ih hrest]
                  rfl
    rw [← hor, Matrix.mulVec_mulVec, hprod_mul]
  have hfin : (List.finRange m).toFinset = Finset.univ := by
    ext i; simp
  have hc := hcomm_step (List.finRange m) (List.nodup_finRange m)
  rw [hfin] at hc
  rw [← Matrix.mulVec_smul]
  dsimp only [diffL]
  rw [Submonoid.coe_list_prod, List.map_map]
  exact hc

theorem tcExtract_marker_pack (n m d Q : ℕ) (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (u : Fin m → Fin (2 ^ (n * d))) (i : Fin m) :
    (tcMarkerReg n m Q hQ i).extractIndex (tcPackConveyorBasis n m d Q hn hd12 hQ u) = 0 := by
  apply (basisBits 1).injective
  funext b
  have hb0 : b = 0 := Subsingleton.elim b 0
  subst hb0
  rw [QRegister.basisBits_extractIndex, basisBits_zero, Pi.zero_apply]
  exact tcBasisBits_pack_outside n m d Q hn hd12 hQ u
    (fun k ↦ tcMarkerWire_not_mem_conveyor hn hd12 hQ i k)

theorem tcParallelGroverStep_mulVec_pack {Var : Type} (n m d Q : ℕ) (hn : 0 < n)
    (hd1 : 1 ≤ d) (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (R : Finset (Fin (2 ^ n))) {U : Unitary (2 ^ Q)}
    (hU : tcCompileUnitary (parallelMarkingOracle m R)
      (tcParallelGroverStep (Var := Var) n m Q hQ) = some U) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ ψ : Fin m → Fin (2 ^ (n * d)) → ℂ,
      U.1 *ᵥ
        (∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m, ψ i (u i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ)) =
      γ •
        ∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m,
            (((localMemSlotReg n d ⟨0, hd1⟩).embedUnitary (groverStepUnitary R)).1 *ᵥ ψ i)
              (u i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ) := by
  obtain ⟨γ, hγ, hsingle⟩ := tcParallelGroverStep_mulVec_cleanMarker n m Q hQ R hU
  refine ⟨γ, hγ, fun ψ ↦ ?_⟩
  have hact_eq :
      ((List.finRange m).map fun i ↦
        (tcActiveIdxReg n m Q hQ i).embedMatrix (groverStepUnitary R).1) =
      ((List.finRange m).map fun i ↦
        (tcSlotConveyorReg n m d Q hn hd12 hQ i).embedMatrix
          ((localMemSlotReg n d ⟨0, hd1⟩).embedUnitary (groverStepUnitary R)).1) := by
    refine List.map_congr_left fun i _ ↦ ?_
    rw [← tcSlotConveyorReg_compose_zero hn hd1 hd12 hQ i, QRegister.embedMatrix_compose]
    rfl
  rw [Matrix.mulVec_sum]
  have hterm : ∀ u ∈ (Finset.univ : Finset (Fin m → Fin (2 ^ (n * d)))),
      U.1 *ᵥ ((∏ i : Fin m, ψ i (u i)) •
          Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ)) =
      γ • ((((List.finRange m).map fun i ↦
          (tcSlotConveyorReg n m d Q hn hd12 hQ i).embedMatrix
            ((localMemSlotReg n d ⟨0, hd1⟩).embedUnitary (groverStepUnitary R)).1).prod) *ᵥ
        ((∏ i : Fin m, ψ i (u i)) •
          Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ))) := by
    intro u _
    rw [Matrix.mulVec_smul,
      hsingle _ (tcExtract_marker_pack n m d Q hn hd12 hQ u),
      hact_eq, Matrix.mulVec_smul, smul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← Matrix.mulVec_sum,
    listProd_embedMatrix_mulVec_pack]

theorem tcParallelGroverIter_mulVec_pack {Var : Type} (n m d Q : ℕ) (hn : 0 < n)
    (hd1 : 1 ≤ d) (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (R : Finset (Fin (2 ^ n))) (K : ℕ) {U : Unitary (2 ^ Q)}
    (hU : tcCompileUnitary (parallelMarkingOracle m R)
      (tcParallelGroverIter (Var := Var) n m Q hQ K) = some U) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ ψ : Fin m → Fin (2 ^ (n * d)) → ℂ,
      U.1 *ᵥ
        (∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m, ψ i (u i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ)) =
      γ •
        ∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m,
            (((localMemSlotReg n d ⟨0, hd1⟩).embedUnitary (groverStepUnitary R ^ K)).1 *ᵥ ψ i)
              (u i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ) := by
  induction K generalizing U with
  | zero =>
      dsimp only [tcParallelGroverIter, tcCompileUnitary] at hU
      injection hU with hU
      subst hU
      refine ⟨1, norm_one, fun _ ↦ ?_⟩
      simp
  | succ K ih =>
      simp only [tcParallelGroverIter, tcCompileUnitary, Option.bind_eq_some_iff,
        Option.some.injEq] at hU
      obtain ⟨U₁, h1, U₂, h2, rfl⟩ := hU
      obtain ⟨γ₁, hγ₁, ih₁⟩ := ih h1
      obtain ⟨γ₂, hγ₂, hstep⟩ := tcParallelGroverStep_mulVec_pack n m d Q hn hd1 hd12 hQ R h2
      refine ⟨γ₁ * γ₂, by rw [norm_mul, hγ₁, hγ₂, mul_one], fun ψ ↦ ?_⟩
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih₁ ψ, Matrix.mulVec_smul, hstep, smul_smul]
      congr 1
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [Matrix.mulVec_mulVec]
      have hmul :
          ((localMemSlotReg n d ⟨0, hd1⟩).embedUnitary (groverStepUnitary R)).1 *
            ((localMemSlotReg n d ⟨0, hd1⟩).embedUnitary (groverStepUnitary R ^ K)).1 =
          ((localMemSlotReg n d ⟨0, hd1⟩).embedUnitary (groverStepUnitary R ^ (K + 1))).1 := by
        change (localMemSlotReg n d ⟨0, hd1⟩).embedMatrix (groverStepUnitary R).1 *
            (localMemSlotReg n d ⟨0, hd1⟩).embedMatrix (groverStepUnitary R ^ K).1 =
          (localMemSlotReg n d ⟨0, hd1⟩).embedMatrix (groverStepUnitary R ^ (K + 1)).1
        rw [← QRegister.embedMatrix_mul, ← Submonoid.coe_mul, ← pow_succ']
      rw [hmul]

theorem tcPackConveyorBasis_zero (n m d Q : ℕ) (hn : 0 < n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) :
    tcPackConveyorBasis n m d Q hn hd12 hQ 0 = 0 := by
  have hfold : ∀ l : List (Fin m),
      l.foldl (fun a i ↦ (tcSlotConveyorReg n m d Q hn hd12 hQ i).replaceIndex a 0) 0 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i rest ih =>
        have hr0 : (tcSlotConveyorReg n m d Q hn hd12 hQ i).replaceIndex 0 0 = 0 := by
          have hz0 : (0 : Fin (2 ^ (n * d))) =
              (tcSlotConveyorReg n m d Q hn hd12 hQ i).extractIndex 0 :=
            (extractIndex_zero _).symm
          conv_lhs => rw [hz0]
          exact (tcSlotConveyorReg n m d Q hn hd12 hQ i).replaceIndex_extractIndex 0
        simp [List.foldl_cons, hr0, ih]
  exact hfold (List.finRange m)

theorem tcPulsesBodyCircuit_mulVec_pack {Var : Type} (n m d Q : ℕ) (hn : 0 < n)
    (hd1 : 1 ≤ d) (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (R : Finset (Fin (2 ^ n))) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (t : ℕ)
    {U : Unitary (2 ^ Q)}
    (hU : tcCompileUnitary (parallelMarkingOracle m R)
      (tcPulsesBodyCircuit (Var := Var) n m d Q hn hd12 hQ K_blk uFn t) = some U) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ ψ : Fin m → Fin (2 ^ (n * d)) → ℂ,
      U.1 *ᵥ
        (∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m, ψ i (u i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ)) =
      γ •
        ∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m,
            ((tcSlotConveyorUnitary n d hd1 R K_blk uFn t).1 *ᵥ ψ i) (u i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ) := by
  induction t generalizing U with
  | zero =>
      dsimp only [tcPulsesBodyCircuit, tcCompileUnitary] at hU
      injection hU with hU
      subst hU
      exact ⟨1, norm_one, fun _ ↦ by simp [tcSlotConveyorUnitary]⟩
  | succ t ih =>
      simp only [tcPulsesBodyCircuit, tcRealStep, tcCompileUnitary, Option.bind_some,
        Option.bind_eq_some_iff, Option.some.injEq] at hU
      obtain ⟨U₁, h1, _, ⟨U₂, h2, rfl⟩, rfl⟩ := hU
      obtain ⟨γ₁, hγ₁, ih₁⟩ := ih h1
      obtain ⟨γ₂, hγ₂, hiter⟩ := tcParallelGroverIter_mulVec_pack n m d Q hn hd1 hd12 hQ R
        K_blk h2
      refine ⟨Complex.I * (γ₂ * γ₁), by simp [hγ₁, hγ₂], fun ψ ↦ ?_⟩
      simp only [Submonoid.coe_mul, phaseI_val, Matrix.mul_assoc]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih₁ ψ, Matrix.mulVec_smul,
        hiter, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul]
      rw [Submonoid.coe_list_prod, List.map_map]
      change γ₁ • (Complex.I • (γ₂ •
        ((((List.finRange m).map fun i ↦
            (tcSlotConveyorReg n m d Q hn hd12 hQ i).embedMatrix
              (tcIntertwinerUnitary n d (uFn t)).1).prod) *ᵥ _))) = _
      rw [listProd_embedMatrix_mulVec_pack]
      simp only [smul_smul]
      refine congrArg₂ (· • ·) (by ring) ?_
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      simp [tcSlotConveyorUnitary, tcSlotPulseUnitary, Submonoid.coe_mul, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]

theorem tcPulsesCircuit_mulVec_zero {Var : Type} (n m d Q : ℕ) (hn : 0 < n)
    (hd1 : 1 ≤ d) (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (R : Finset (Fin (2 ^ n))) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ)
    {U : Unitary (2 ^ Q)}
    (hU : tcCompileUnitary (parallelMarkingOracle m R)
      (tcPulsesCircuit (Var := Var) n m d Q hn hd12 hQ K_blk uFn steps) = some U) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧
      U.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) =
      γ •
        ∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m, tcSlotConveyorVec n d hd1 R K_blk uFn steps (u i)) •
            Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ) := by
  simp only [tcPulsesCircuit, tcRealStep, tcCompileUnitary, Option.bind_some,
    Option.bind_eq_some_iff, Option.some.injEq] at hU
  obtain ⟨U_body, hbody, rfl⟩ := hU
  obtain ⟨γ_b, hγ_b, hpack⟩ := tcPulsesBodyCircuit_mulVec_pack n m d Q hn hd1 hd12 hQ R K_blk
    uFn steps hbody
  refine ⟨Complex.I * γ_b, by simp [hγ_b], ?_⟩
  let e0 : Fin (2 ^ (n * d)) → ℂ := Pi.single 0 1
  have h0_sum : Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) =
      ∑ u : Fin m → Fin (2 ^ (n * d)),
        (∏ i : Fin m, e0 (u i)) •
          (Pi.single (tcPackConveyorBasis n m d Q hn hd12 hQ u) (1 : ℂ) : Fin (2 ^ Q) → ℂ) := by
    symm
    rw [Finset.sum_eq_single 0]
    · simp [e0, tcPackConveyorBasis_zero]
    · intro u _ hu
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
      have hp0 : (∏ j : Fin m, e0 (u j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Pi.single_eq_of_ne hi 1)
      rw [hp0, zero_smul]
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  simp only [Submonoid.coe_mul, phaseI_val]
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, h0_sum, Submonoid.coe_list_prod, List.map_map]
  change U_body.1 *ᵥ (Complex.I •
      ((((List.finRange m).map fun i ↦
          (tcSlotConveyorReg n m d Q hn hd12 hQ i).embedMatrix
            (hadamardUnitary (q := n * d)).1).prod) *ᵥ _)) = _
  rw [listProd_embedMatrix_mulVec_pack, Matrix.mulVec_smul, hpack, smul_smul]
  rfl

/-- Partial swap-verification basis state after `cnt` rounds `0.. cnt - 1`. -/
noncomputable def tcPackVerifPartBasis (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n))) (cnt : ℕ)
    (u : Fin m → Fin (2 ^ (n * d))) : Fin (2 ^ Q) :=
  (basisBits Q).symm fun w ↦
    basisBits Q (tcPackConveyorBasis n m d Q (by omega) hd12 hQ u) w +
      ∑ i : Fin m, ∑ q : Fin d,
        if q.val < cnt ∧ w = tcVerifFlagReg n m Q hn12 hQ i ⟨q.val, by omega⟩ 0 ∧
            (localMemSlotReg n d q).extractIndex (u i) ∈ R then
          1
        else
          0

theorem tcPackVerifPartBasis_zero (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    (u : Fin m → Fin (2 ^ (n * d))) :
    tcPackVerifPartBasis n m d Q hn12 hd12 hQ R 0 u =
      tcPackConveyorBasis n m d Q (by omega) hd12 hQ u := by
  simp [tcPackVerifPartBasis]

theorem tcPackVerifPartBasis_full (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    (u : Fin m → Fin (2 ^ (n * d))) :
    tcPackVerifPartBasis n m d Q hn12 hd12 hQ R d u =
      tcPackVerifBasis n m d Q hn12 hd12 hQ R u := by
  unfold tcPackVerifPartBasis tcPackVerifBasis
  congr 1
  funext w
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  simp [q.isLt]

theorem tcBasisBits_swapRegsFun {W Q : ℕ} {r₁ r₂ : QRegister W Q} (h : r₁.DisjointWires r₂)
    (z : Fin (2 ^ Q)) (b : Fin W) :
    basisBits Q (tcSwapRegsFun r₁ r₂ z) (r₁ b) = basisBits Q z (r₂ b) ∧
    basisBits Q (tcSwapRegsFun r₁ r₂ z) (r₂ b) = basisBits Q z (r₁ b) := by
  constructor
  · rw [← r₁.basisBits_extractIndex, tcSwapRegsFun_extract_left, r₂.basisBits_extractIndex]
  · rw [← r₂.basisBits_extractIndex, tcSwapRegsFun_extract_right h, r₁.basisBits_extractIndex]

theorem tcVerifWire_inj {n m Q : ℕ} (hn12 : 12 ≤ n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    {i₁ i₂ : Fin m} {q₁ q₂ : Fin 12}
    (h : tcVerifFlagReg n m Q hn12 hQ i₁ q₁ 0 = tcVerifFlagReg n m Q hn12 hQ i₂ q₂ 0) :
    i₁ = i₂ ∧ q₁ = q₂ := by
  have hv := congrArg Fin.val h
  simp only [tcVerifFlagReg_apply_val, Fin.val_zero, add_zero] at hv
  have hsub : i₁.val * 12 + q₁.val = i₂.val * 12 + q₂.val := by omega
  have hd := congrArg (· / 12) hsub
  have hr1 : i₁.val * 12 + q₁.val = 12 * i₁.val + q₁.val := by ring
  have hr2 : i₂.val * 12 + q₂.val = 12 * i₂.val + q₂.val := by ring
  rw [hr1, hr2, Nat.mul_add_div (by positivity), Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt q₁.isLt, Nat.div_eq_of_lt q₂.isLt] at hd
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

theorem tcVerifWire_not_mem_act {n m Q : ℕ} (hn12 : 12 ≤ n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (i : Fin m) (q : Fin 12) :
    tcVerifFlagReg n m Q hn12 hQ i q 0 ∉
      Set.range (tcAllActReg n m Q (by omega) hQ).wires := by
  rintro ⟨w, heq⟩
  have hv := congrArg Fin.val heq
  simp only [tcAllActReg_apply, tcActiveIdxReg_apply_val, tcVerifFlagReg_apply_val,
    Fin.val_zero, add_zero] at hv
  have hd : w.val / n < m :=
    Nat.div_lt_of_lt_mul (show w.val < n * m by linarith [w.isLt])
  have hlt := tcActiveIdx_val_lt ⟨w.val / n, hd⟩ ⟨w.val % n, Nat.mod_lt _ (by omega)⟩
  dsimp only at hlt
  omega

theorem tcVerifWire_not_mem_pas {n m Q : ℕ} (hn12 : 12 ≤ n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (i : Fin m) (q : Fin 12) (p : Fin 11) :
    tcVerifFlagReg n m Q hn12 hQ i q 0 ∉
      Set.range (tcAllPasReg n m Q (by omega) hQ p).wires := by
  rintro ⟨w, heq⟩
  have hv := congrArg Fin.val heq
  simp only [tcAllPasReg_apply, tcPassiveReg_apply_val, tcVerifFlagReg_apply_val,
    Fin.val_zero, add_zero] at hv
  have hm : w.val % n < n := Nat.mod_lt _ (by omega)
  have hd : w.val / n < m :=
    Nat.div_lt_of_lt_mul (show w.val < n * m by linarith [w.isLt])
  have h1 : (w.val / n) * 11 + p.val + 1 ≤ 11 * m := by
    calc (w.val / n) * 11 + p.val + 1 ≤ (w.val / n) * 11 + 11 := by omega
      _ = (w.val / n + 1) * 11 := by ring
      _ ≤ m * 11 := Nat.mul_le_mul_right 11 hd
      _ = 11 * m := by ring
  have hhi : ((w.val / n) * 11 + p.val) * n + w.val % n < 11 * m * n := by
    calc ((w.val / n) * 11 + p.val) * n + w.val % n
        < ((w.val / n) * 11 + p.val) * n + n := by omega
      _ = ((w.val / n) * 11 + p.val + 1) * n := by ring
      _ ≤ (11 * m) * n := Nat.mul_le_mul_right n h1
      _ = 11 * m * n := by ring
  omega

theorem tcMarkWire_not_mem_act {n m Q : ℕ} (hn : 0 < n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (i : Fin m) :
    tcMarkerReg n m Q hQ i 0 ∉ Set.range (tcAllActReg n m Q hn hQ).wires := by
  rintro ⟨w, heq⟩
  have hv := congrArg Fin.val heq
  simp only [tcAllActReg_apply, tcActiveIdxReg_apply_val, tcMarkerReg_apply_val,
    Fin.val_zero, add_zero] at hv
  have hm : w.val % n < n := Nat.mod_lt _ hn
  have hmod := congrArg (· % (n + 1)) hv
  have hr1 : (w.val / n) * (n + 1) + (1 + w.val % n) =
      (n + 1) * (w.val / n) + (1 + w.val % n) := by ring
  have hr2 : i.val * (n + 1) = (n + 1) * i.val + 0 := by ring
  have hm1 : (1 + w.val % n) % (n + 1) = 1 + w.val % n := Nat.mod_eq_of_lt (by linarith)
  have hm0 : 0 % (n + 1) = 0 := Nat.zero_mod _
  rw [hr1, hr2, Nat.mul_add_mod, Nat.mul_add_mod, hm1, hm0] at hmod
  omega

theorem tcMarkWire_not_mem_pas {n m Q : ℕ} (hn : 0 < n) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (i : Fin m) (p : Fin 11) :
    tcMarkerReg n m Q hQ i 0 ∉ Set.range (tcAllPasReg n m Q hn hQ p).wires := by
  rintro ⟨w, heq⟩
  have hv := congrArg Fin.val heq
  simp only [tcAllPasReg_apply, tcPassiveReg_apply_val, tcMarkerReg_apply_val,
    Fin.val_zero, add_zero] at hv
  have hlt := tcMarker_val_lt (n := n) i
  omega

theorem tcVerifWire_not_mem_oracle {n m Q : ℕ} (hn12 : 12 ≤ n)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (i : Fin m) (q : Fin 12) :
    tcVerifFlagReg n m Q hn12 hQ i q 0 ∉ Set.range (tcOracleReg n m Q hQ).wires := by
  rintro ⟨w, heq⟩
  have hv := congrArg Fin.val heq
  simp only [tcOracleReg_apply_val, tcVerifFlagReg_apply_val, Fin.val_zero, add_zero] at hv
  have := w.isLt
  omega

theorem tcVerifRoundCircuit_mulVec_part {Var : Type} (n m d Q : ℕ) (hn12 : 12 ≤ n)
    (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    (q : ℕ) (hqd : q < d) {U : Unitary (2 ^ Q)}
    (hU : tcCompileUnitary (parallelMarkingOracle m R)
      (tcVerifRoundCircuit (Var := Var) n m Q hn12 hQ q (by omega)) = some U) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ u : Fin m → Fin (2 ^ (n * d)),
      U.1 *ᵥ Pi.single (tcPackVerifPartBasis n m d Q hn12 hd12 hQ R q u) (1 : ℂ) =
        γ • Pi.single (tcPackVerifPartBasis n m d Q hn12 hd12 hQ R (q + 1) u) (1 : ℂ) := by
  have hn : 0 < n := by omega
  let q12 : Fin 12 := ⟨q, by omega⟩
  let qd : Fin d := ⟨q, hqd⟩
  let rOr := tcOracleReg n m Q hQ
  let rMark := tcAllMarkReg n m Q hQ
  let rVer := tcAllVerifReg n m Q hn12 hQ q12
  let permFlag := tcSwapRegsEquiv rMark rVer (tcAllMarkReg_disjoint_verif hn12 hQ q12)
  let permAddr : Equiv.Perm (Fin (2 ^ Q)) :=
    if hq0 : q = 0 then 1
    else tcSwapRegsEquiv (tcAllActReg n m Q hn hQ)
      (tcAllPasReg n m Q hn hQ ⟨q - 1, by omega⟩)
      (tcAllActReg_disjoint_pas hn hQ ⟨q - 1, by omega⟩)
  have hpermAddr_inv : Function.Involutive permAddr := by
    intro x
    dsimp only [permAddr]
    split_ifs with hq0
    · rfl
    · exact tcSwapRegsFun_involutive (tcAllActReg_disjoint_pas hn hQ ⟨q - 1, by omega⟩) x
  have hstep_compile :
      ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ z₀ : Fin (2 ^ Q),
        U.1 *ᵥ Pi.single z₀ (1 : ℂ) =
          γ • Pi.single
            (permAddr (permFlag (rOr.replaceIndex (permAddr z₀)
              (localAppMark n m R (List.finRange m) (rOr.extractIndex (permAddr z₀)))))) 1 := by
    unfold tcVerifRoundCircuit at hU
    by_cases hq0 : q = 0
    · simp only [hq0, ↓reduceDIte] at hU
      dsimp only [tcRealStep, tcCompileUnitary, Option.bind] at hU
      injection hU with hU
      subst hU
      refine ⟨Complex.I, Complex.norm_I, fun z₀ ↦ ?_⟩
      simp only [one_mul, mul_one, Submonoid.coe_mul, phaseI_val, permAddr, hq0, ↓reduceDIte,
        Equiv.Perm.coe_one, id_eq]
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
        QRegister.embedUnitary_val, QRegister.embedMatrix_mulVec_single_factors,
        parallelMarkingOracle_mulVec_single_local, QRegister.tensorState_single_replaceIndex,
        permutationUnitary_mulVec_single]
      have hq12 : (⟨0, by omega⟩ : Fin 12) = q12 := Fin.ext hq0.symm
      have hswap_eq (x : Fin (2 ^ Q)) (q' : Fin 12) (hq' : q' = q12)
          {hd : (tcAllMarkReg n m Q hQ).DisjointWires (tcAllVerifReg n m Q hn12 hQ q')} :
          tcSwapRegsEquiv (tcAllMarkReg n m Q hQ) (tcAllVerifReg n m Q hn12 hQ q') hd x =
            tcSwapRegsEquiv rMark (tcAllVerifReg n m Q hn12 hQ q12)
              (tcAllMarkReg_disjoint_verif hn12 hQ q12) x := by
        subst hq'
        rfl
      dsimp only [permFlag, rVer, rOr]
      rw [hswap_eq _ ⟨0, by omega⟩ hq12]
    · simp only [hq0, ↓reduceDIte] at hU
      dsimp only [tcRealStep, tcCompileUnitary, Option.bind] at hU
      injection hU with hU
      subst hU
      refine ⟨Complex.I * Complex.I * Complex.I, by simp, fun z₀ ↦ ?_⟩
      simp only [Submonoid.coe_mul, phaseI_val, permAddr, hq0, ↓reduceDIte, Matrix.mul_assoc]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, permutationUnitary_mulVec_single,
        QRegister.embedUnitary_val, QRegister.embedMatrix_mulVec_single_factors,
        parallelMarkingOracle_mulVec_single_local, QRegister.tensorState_single_replaceIndex,
        smul_smul]
      rfl
  obtain ⟨γ, hγ, hU_apply⟩ := hstep_compile
  refine ⟨γ, hγ, fun u ↦ ?_⟩
  rw [hU_apply]
  congr 2
  set z₀ := tcPackVerifPartBasis n m d Q hn12 hd12 hQ R q u
  set z₁ := permAddr z₀
  set z₂ := rOr.replaceIndex z₁ (localAppMark n m R (List.finRange m) (rOr.extractIndex z₁))
  set z₃ := permFlag z₂
  have hz0_nonverif : ∀ {w : Wire Q},
      (∀ i : Fin m, ∀ q' : Fin d, q'.val < q →
        w ≠ tcVerifFlagReg n m Q hn12 hQ i ⟨q'.val, by omega⟩ 0) →
      basisBits Q z₀ w = basisBits Q (tcPackConveyorBasis n m d Q hn hd12 hQ u) w := by
    intro w hw
    dsimp only [z₀, tcPackVerifPartBasis]
    rw [Equiv.apply_symm_apply]
    have hs0 : (∑ i : Fin m, ∑ q' : Fin d,
        if q'.val < q ∧ w = tcVerifFlagReg n m Q hn12 hQ i ⟨q'.val, by omega⟩ 0 ∧
            (localMemSlotReg n d q').extractIndex (u i) ∈ R then (1 : ZMod 2) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun q' _ ↦ ?_
      by_cases hlt : q'.val < q
      · simp [hlt, hw i q' hlt]
      · simp [hlt]
    rw [hs0, add_zero]
  have hz0_conv (i : Fin m) :
      (tcSlotConveyorReg n m d Q hn hd12 hQ i).extractIndex z₀ = u i := by
    apply (basisBits (n * d)).injective
    funext w
    rw [(tcSlotConveyorReg n m d Q hn hd12 hQ i).basisBits_extractIndex,
      hz0_nonverif (fun j q' _ h ↦
        tcVerifWire_not_mem_conveyor hn12 hd12 hQ j i ⟨q'.val, by omega⟩ ⟨w, h⟩),
      ← (tcSlotConveyorReg n m d Q hn hd12 hQ i).basisBits_extractIndex,
      tcExtract_conveyor_pack]
  have hz0_mark (i : Fin m) : basisBits Q z₀ (rMark i) = 0 := by
    change basisBits Q z₀ (tcMarkerReg n m Q hQ i 0) = 0
    rw [hz0_nonverif]
    · exact tcBasisBits_pack_outside n m d Q hn hd12 hQ u
        (fun k ↦ tcMarkerWire_not_mem_conveyor hn hd12 hQ i k)
    · intro j q' _ h
      exact (tcAllMarkReg_disjoint_verif hn12 hQ ⟨q'.val, by omega⟩).ne i j h
  have hz0_verq (i : Fin m) : basisBits Q z₀ (rVer i) = 0 := by
    change basisBits Q z₀ (tcVerifFlagReg n m Q hn12 hQ i q12 0) = 0
    rw [hz0_nonverif]
    · exact tcBasisBits_pack_outside n m d Q hn hd12 hQ u
        (fun k ↦ tcVerifWire_not_mem_conveyor hn12 hd12 hQ i k q12)
    · intro j q' hlt h
      obtain ⟨_, hqq⟩ := tcVerifWire_inj hn12 hQ h
      have hval := congrArg Fin.val hqq
      dsimp [q12] at hval
      omega
  have hz1_outside : ∀ {w : Wire Q},
      w ∉ Set.range (tcAllActReg n m Q hn hQ).wires →
      (∀ p : Fin 11, w ∉ Set.range (tcAllPasReg n m Q hn hQ p).wires) →
      basisBits Q z₁ w = basisBits Q z₀ w := by
    intro w hact hpas
    dsimp only [z₁, permAddr]
    split_ifs with hq0
    · rfl
    · exact tcSwapRegsFun_basisBits_outside _ _ z₀ hact (hpas ⟨q - 1, by omega⟩)
  have hz1_mark (i : Fin m) : (tcMarkerReg n m Q hQ i).extractIndex z₁ = 0 := by
    apply (basisBits 1).injective
    funext b
    have hb0 : b = 0 := Subsingleton.elim b 0
    subst hb0
    rw [QRegister.basisBits_extractIndex, basisBits_zero, Pi.zero_apply,
      hz1_outside (tcMarkWire_not_mem_act hn hQ i) (tcMarkWire_not_mem_pas hn hQ i)]
    exact hz0_mark i
  have hz1_act (i : Fin m) :
      (tcActiveIdxReg n m Q hQ i).extractIndex z₁ =
        (localMemSlotReg n d qd).extractIndex (u i) := by
    apply (basisBits n).injective
    funext b
    rw [(tcActiveIdxReg n m Q hQ i).basisBits_extractIndex]
    dsimp only [z₁, permAddr]
    split_ifs with hq0
    · have hqd0 : qd = ⟨0, by omega⟩ := Fin.ext hq0
      rw [hqd0, Equiv.Perm.coe_one, id_eq,
        ← tcSlotConveyorReg_compose_zero hn (by omega) hd12 hQ i,
        QRegister.compose_apply,
        ← (tcSlotConveyorReg n m d Q hn hd12 hQ i).basisBits_extractIndex, hz0_conv i,
        (localMemSlotReg n d ⟨0, by omega⟩).basisBits_extractIndex]
    · let wb : Fin (m * n) := ⟨i.val * n + b.val, by nlinarith [i.isLt, b.isLt]⟩
      have hwb_eq : wb.val = n * i.val + b.val := by dsimp [wb]; ring
      have hdiv : wb.val / n = i.val := by
        rw [hwb_eq, Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, add_zero]
      have hmod : wb.val % n = b.val := by
        rw [hwb_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
      have hw_act : tcActiveIdxReg n m Q hQ i b = tcAllActReg n m Q hn hQ wb := by
        apply Fin.ext
        simp only [tcAllActReg_apply, tcActiveIdxReg_apply_val, hdiv, hmod]
      have hw_pas : tcAllPasReg n m Q hn hQ ⟨q - 1, by omega⟩ wb =
          tcPassiveReg n m Q hQ i ⟨q - 1, by omega⟩ b := by
        apply Fin.ext
        simp only [tcAllPasReg_apply, tcPassiveReg_apply_val, hdiv, hmod]
      rw [hw_act, tcSwapRegsEquiv_apply,
        (tcBasisBits_swapRegsFun (tcAllActReg_disjoint_pas hn hQ ⟨q - 1, by omega⟩) z₀ wb).1,
        hw_pas]
      have hpos : (tcSlotConveyorReg n m d Q hn hd12 hQ i).compose (localMemSlotReg n d qd) =
          tcPassiveReg n m Q hQ i ⟨q - 1, by omega⟩ :=
        tcSlotConveyorReg_compose_pos hn hd12 hQ i qd (by dsimp [qd]; omega)
      rw [← hpos, QRegister.compose_apply,
        ← (tcSlotConveyorReg n m d Q hn hd12 hQ i).basisBits_extractIndex, hz0_conv i,
        (localMemSlotReg n d qd).basisBits_extractIndex]
  have hz2_mark (i : Fin m) :
      basisBits Q z₂ (rMark i) =
        if (localMemSlotReg n d qd).extractIndex (u i) ∈ R then 1 else 0 := by
    have hex_slot : (localSlotReg n m i).extractIndex
        (localAppMark n m R (List.finRange m) (rOr.extractIndex z₁)) =
        slotMarkPerm R ((localSlotReg n m i).extractIndex (rOr.extractIndex z₁)) := by
      rw [extractIndex_localSlotReg_localAppMark n m R _ (List.nodup_finRange m),
        ite_eq_left (List.mem_finRange i)]
    change basisBits Q z₂ ((rOr.compose (localSlotReg n m i)).compose (localMarkerReg n) 0) = _
    dsimp only [z₂]
    rw [← ((rOr.compose (localSlotReg n m i)).compose (localMarkerReg n)).basisBits_extractIndex,
      QRegister.extractIndex_compose, QRegister.extractIndex_compose,
      QRegister.extractIndex_replaceIndex, hex_slot,
      extractIndex_localMarkerReg_slotMarkPerm]
    have hm1 : (localMarkerReg n).extractIndex
        ((localSlotReg n m i).extractIndex (rOr.extractIndex z₁)) = 0 := by
      simpa [tcMarkerReg, tcSlotOracleReg, QRegister.extractIndex_compose] using hz1_mark i
    have ha1 : (localIdxReg n).extractIndex
        ((localSlotReg n m i).extractIndex (rOr.extractIndex z₁)) =
        (localMemSlotReg n d qd).extractIndex (u i) := by
      simpa [tcActiveIdxReg, tcSlotOracleReg, QRegister.extractIndex_compose] using hz1_act i
    rw [hm1, zero_add, ha1, basisBits_eq_testBit]
    by_cases hmem : (localMemSlotReg n d qd).extractIndex (u i) ∈ R <;>
      simp only [hmem, ↓reduceIte] <;> rfl
  have hz2_nonmark : ∀ {w : Wire Q}, w ∉ Set.range rMark.wires →
      basisBits Q z₂ w = basisBits Q z₁ w := by
    intro w hnm
    by_cases hwor : w ∈ Set.range rOr.wires
    · obtain ⟨u_or, rfl⟩ := hwor
      let j : Fin m := ⟨u_or.val / (n + 1), Nat.div_lt_of_lt_mul u_or.isLt⟩
      let r_in : Fin (n + 1) := ⟨u_or.val % (n + 1), Nat.mod_lt _ (by omega)⟩
      have hu_eq : u_or = localSlotReg n m j r_in := by
        apply Fin.ext
        simp only [localSlotReg, QRegister.block_apply_val, j, r_in]
        linarith [Nat.div_add_mod u_or.val (n + 1)]
      have hr_ne0 : r_in.val ≠ 0 := by
        intro hr0
        have hr_zero : r_in = 0 := Fin.ext hr0
        apply hnm
        refine ⟨j, ?_⟩
        change tcMarkerReg n m Q hQ j 0 = rOr u_or
        rw [hu_eq, hr_zero]
        rfl
      let b : Fin n := ⟨r_in.val - 1, by omega⟩
      have hr_idx : r_in = localIdxReg n b := by
        apply Fin.ext
        simp [localIdxReg, b]
        omega
      have hex_slot : (localSlotReg n m j).extractIndex
          (localAppMark n m R (List.finRange m) (rOr.extractIndex z₁)) =
          slotMarkPerm R ((localSlotReg n m j).extractIndex (rOr.extractIndex z₁)) := by
        rw [extractIndex_localSlotReg_localAppMark n m R _ (List.nodup_finRange m),
          ite_eq_left (List.mem_finRange j)]
      rw [hu_eq, hr_idx]
      change basisBits Q z₂ ((rOr.compose (localSlotReg n m j)).compose (localIdxReg n) b) =
        basisBits Q z₁ ((rOr.compose (localSlotReg n m j)).compose (localIdxReg n) b)
      dsimp only [z₂]
      rw [← ((rOr.compose (localSlotReg n m j)).compose (localIdxReg n)).basisBits_extractIndex,
        ← ((rOr.compose (localSlotReg n m j)).compose (localIdxReg n)).basisBits_extractIndex,
        QRegister.extractIndex_compose, QRegister.extractIndex_compose,
        QRegister.extractIndex_compose, QRegister.extractIndex_compose,
        QRegister.extractIndex_replaceIndex, hex_slot, extractIndex_localIdxReg_slotMarkPerm]
    · exact rOr.basisBits_replaceIndex_of_not_mem _ _ _ hwor
  have hz3_ver (i : Fin m) :
      basisBits Q z₃ (rVer i) =
        if (localMemSlotReg n d qd).extractIndex (u i) ∈ R then 1 else 0 := by
    dsimp only [z₃, permFlag]
    rw [tcSwapRegsEquiv_apply,
      (tcBasisBits_swapRegsFun (tcAllMarkReg_disjoint_verif hn12 hQ q12) z₂ i).2, hz2_mark i]
  have hz3_nonver : ∀ {w : Wire Q}, w ∉ Set.range rVer.wires →
      basisBits Q z₃ w = basisBits Q z₁ w := by
    intro w hnv
    dsimp only [z₃, permFlag]
    rw [tcSwapRegsEquiv_apply]
    by_cases hwm : w ∈ Set.range rMark.wires
    · obtain ⟨i, rfl⟩ := hwm
      rw [(tcBasisBits_swapRegsFun (tcAllMarkReg_disjoint_verif hn12 hQ q12) z₂ i).1]
      have hnv_m : rVer i ∉ Set.range rMark.wires := by
        rintro ⟨j, hj⟩
        exact (tcAllMarkReg_disjoint_verif hn12 hQ q12).ne j i hj
      rw [hz2_nonmark hnv_m]
      change basisBits Q z₁ (tcVerifFlagReg n m Q hn12 hQ i q12 0) =
        basisBits Q z₁ (tcMarkerReg n m Q hQ i 0)
      rw [hz1_outside (tcVerifWire_not_mem_act hn12 hQ i q12)
          (tcVerifWire_not_mem_pas hn12 hQ i q12),
        hz1_outside (tcMarkWire_not_mem_act hn hQ i) (tcMarkWire_not_mem_pas hn hQ i)]
      exact (show basisBits Q z₀ (tcVerifFlagReg n m Q hn12 hQ i q12 0) = 0 from hz0_verq i).trans
        (show basisBits Q z₀ (tcMarkerReg n m Q hQ i 0) = 0 from hz0_mark i).symm
    · rw [tcSwapRegsFun_basisBits_outside _ _ z₂ hwm hnv, hz2_nonmark hwm]
  apply (basisBits Q).injective
  funext w
  by_cases hwv : w ∈ Set.range rVer.wires
  · obtain ⟨i, rfl⟩ := hwv
    have hpa : basisBits Q (permAddr z₃) (rVer i) = basisBits Q z₃ (rVer i) := by
      dsimp only [permAddr]
      split_ifs with hq0
      · rfl
      · exact tcSwapRegsFun_basisBits_outside _ _ z₃
          (tcVerifWire_not_mem_act hn12 hQ i q12)
          (tcVerifWire_not_mem_pas hn12 hQ i q12 ⟨q - 1, by omega⟩)
    rw [hpa, hz3_ver i, tcPackVerifPartBasis, Equiv.apply_symm_apply]
    have hpack0 : basisBits Q (tcPackConveyorBasis n m d Q hn hd12 hQ u) (rVer i) = 0 :=
      tcBasisBits_pack_outside n m d Q hn hd12 hQ u
        (fun k ↦ tcVerifWire_not_mem_conveyor hn12 hd12 hQ i k q12)
    rw [hpack0, zero_add, Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single qd]
      · simp [rVer, q12, qd]
      · intro q' _ hne
        have hneq_w : rVer i ≠ tcVerifFlagReg n m Q hn12 hQ i ⟨q'.val, by omega⟩ 0 := by
          intro h
          obtain ⟨_, hqq⟩ := tcVerifWire_inj hn12 hQ h
          exact hne (Fin.ext (congrArg Fin.val hqq).symm)
        simp [hneq_w]
      · intro habs; exact (habs (Finset.mem_univ qd)).elim
    · intro j _ hji
      refine Finset.sum_eq_zero fun q' _ ↦ ?_
      have hneq_w : rVer i ≠ tcVerifFlagReg n m Q hn12 hQ j ⟨q'.val, by omega⟩ 0 := by
        intro h
        exact hji (tcVerifWire_inj hn12 hQ h).1.symm
      simp [hneq_w]
    · intro habs; exact (habs (Finset.mem_univ i)).elim
  · have hpa_eq : basisBits Q (permAddr z₃) w = basisBits Q (permAddr z₁) w := by
      dsimp only [permAddr]
      split_ifs with hq0
      · exact hz3_nonver hwv
      · set rA := tcAllActReg n m Q hn hQ
        set rP := tcAllPasReg n m Q hn hQ ⟨q - 1, by omega⟩
        have hdis := tcAllActReg_disjoint_pas hn hQ ⟨q - 1, by omega⟩
        by_cases hwa : w ∈ Set.range rA.wires
        · obtain ⟨b, rfl⟩ := hwa
          rw [tcSwapRegsEquiv_apply, tcSwapRegsEquiv_apply,
            (tcBasisBits_swapRegsFun hdis z₃ b).1, (tcBasisBits_swapRegsFun hdis z₁ b).1]
          refine hz3_nonver ?_
          rintro ⟨j, hj⟩
          exact tcVerifWire_not_mem_pas hn12 hQ j q12 ⟨q - 1, by omega⟩ ⟨b, hj.symm⟩
        · by_cases hwp : w ∈ Set.range rP.wires
          · obtain ⟨b, rfl⟩ := hwp
            rw [tcSwapRegsEquiv_apply, tcSwapRegsEquiv_apply,
              (tcBasisBits_swapRegsFun hdis z₃ b).2, (tcBasisBits_swapRegsFun hdis z₁ b).2]
            refine hz3_nonver ?_
            rintro ⟨j, hj⟩
            exact tcVerifWire_not_mem_act hn12 hQ j q12 ⟨b, hj.symm⟩
          · rw [tcSwapRegsEquiv_apply, tcSwapRegsEquiv_apply,
              tcSwapRegsFun_basisBits_outside rA rP z₃ hwa hwp,
              tcSwapRegsFun_basisBits_outside rA rP z₁ hwa hwp]
            exact hz3_nonver hwv
    rw [hpa_eq, hpermAddr_inv z₀]
    dsimp only [z₀, tcPackVerifPartBasis]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun q' _ ↦ ?_
    by_cases hqq : q'.val = q
    · have hneq_w : w ≠ tcVerifFlagReg n m Q hn12 hQ i ⟨q'.val, by omega⟩ 0 := by
        intro h
        apply hwv
        refine ⟨i, ?_⟩
        rw [h]
        apply Fin.ext
        simp [rVer, q12, hqq]
      simp [hneq_w]
    · have hlt_iff : q'.val < q ↔ q'.val < q + 1 := by omega
      simp [hlt_iff]

theorem tcVerifCircuit_mulVec_part {Var : Type} (n m d Q : ℕ) (hn12 : 12 ≤ n)
    (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    (cnt : ℕ) (hcnt : cnt ≤ d) {U : Unitary (2 ^ Q)}
    (hU : tcCompileUnitary (parallelMarkingOracle m R)
      (tcVerifCircuit (Var := Var) n m Q hn12 hQ cnt (hcnt.trans hd12)) = some U) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ c : (Fin m → Fin (2 ^ (n * d))) → ℂ,
      U.1 *ᵥ
        (∑ u : Fin m → Fin (2 ^ (n * d)),
          c u • Pi.single (tcPackConveyorBasis n m d Q (by omega) hd12 hQ u) (1 : ℂ)) =
      γ •
        ∑ u : Fin m → Fin (2 ^ (n * d)),
          c u • Pi.single (tcPackVerifPartBasis n m d Q hn12 hd12 hQ R cnt u) (1 : ℂ) := by
  induction cnt generalizing U with
  | zero =>
      dsimp only [tcVerifCircuit, tcCompileUnitary] at hU
      injection hU with hU
      subst hU
      exact ⟨1, norm_one, fun _ ↦ by simp [tcPackVerifPartBasis_zero]⟩
  | succ q ih =>
      simp only [tcVerifCircuit, tcCompileUnitary, Option.bind_eq_some_iff,
        Option.some.injEq] at hU
      obtain ⟨U₁, h1, U₂, h2, rfl⟩ := hU
      obtain ⟨γ₁, hγ₁, ih₁⟩ := ih (by omega) h1
      obtain ⟨γ₂, hγ₂, hrnd⟩ := tcVerifRoundCircuit_mulVec_part n m d Q hn12 hd12 hQ R q
        (by omega) h2
      refine ⟨γ₁ * γ₂, by rw [norm_mul, hγ₁, hγ₂, mul_one], fun c ↦ ?_⟩
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih₁ c, Matrix.mulVec_smul,
        Matrix.mulVec_sum]
      simp_rw [Matrix.mulVec_smul, hrnd, smul_comm (c _), ← Finset.smul_sum, smul_smul]

theorem tcAttemptUnitaryCircuit_mulVec_zero {Var : Type} (n m d Q : ℕ) (hn12 : 12 ≤ n)
    (hd1 : 1 ≤ d) (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (R : Finset (Fin (2 ^ n))) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ)
    {U : Unitary (2 ^ Q)}
    (hU : tcCompileUnitary (parallelMarkingOracle m R)
      (tcAttemptUnitaryCircuit (Var := Var) n m d Q hn12 hd12 hQ K_blk uFn steps) = some U) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧
      U.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) =
      γ •
        ∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m, tcSlotConveyorVec n d hd1 R K_blk uFn steps (u i)) •
            Pi.single (tcPackVerifBasis n m d Q hn12 hd12 hQ R u) (1 : ℂ) := by
  simp only [tcAttemptUnitaryCircuit, tcCompileUnitary, Option.bind_eq_some_iff,
    Option.some.injEq] at hU
  obtain ⟨U₁, h1, U₂, h2, rfl⟩ := hU
  obtain ⟨γ₁, hγ₁, hpulses⟩ := tcPulsesCircuit_mulVec_zero n m d Q (by omega) hd1 hd12 hQ R
    K_blk uFn steps h1
  obtain ⟨γ₂, hγ₂, hverif⟩ := tcVerifCircuit_mulVec_part n m d Q hn12 hd12 hQ R d le_rfl h2
  refine ⟨γ₁ * γ₂, by rw [norm_mul, hγ₁, hγ₂, mul_one], ?_⟩
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hpulses, Matrix.mulVec_smul, hverif, smul_smul]
  simp_rw [tcPackVerifPartBasis_full]

/-- Classical bit reader for verification flag `(i, q)` from `v: ℕ`. -/
def tcVerifBitNat (n m : ℕ) (v : ℕ) (i : Fin m) (q : ℕ) : Bool :=
  v.testBit ((n + 1) * m + 11 * m * n + i.val * 12 + q)

/-- Classical predicate testing whether at least one of the `m * d` verification flags is
  `1`. -/
def tcHasVerifHit (n m d : ℕ) (v : ℕ) : Bool :=
  (List.finRange m).any fun i ↦ (List.range d).any fun q ↦ tcVerifBitNat n m v i q

/-- Classical `n`-bit address reader for slot `i`, subregister `q` (`0` active, `≥ 1`
  passive). -/
def tcSubRegAddrNat (n m : ℕ) (v : ℕ) (i : Fin m) (q : ℕ) : Fin (2 ^ n) :=
  (basisBits n).symm fun b ↦
    if v.testBit
        (if q = 0 then i.val * (n + 1) + 1 + b.val
         else (n + 1) * m + (i.val * 11 + (q - 1)) * n + b.val) then
      1
    else
      0

/-- Classical harvested target subset decoded from a full-register measurement outcome `v:
  ℕ`. -/
def tcDecodeHarvest (n m d : ℕ) (v : ℕ) : Finset (Fin (2 ^ n)) :=
  Finset.univ.biUnion fun i : Fin m ↦
    (Finset.range d).biUnion fun q ↦
      if tcVerifBitNat n m v i q then {tcSubRegAddrNat n m v i q} else ∅

/-- Ideal harvested target subset from `m`-slot tuple `u: Fin m → Fin (2 ^ (n * d))`. -/
def tcHarvestSet {n m d : ℕ} (R : Finset (Fin (2 ^ n))) (u : Fin m → Fin (2 ^ (n * d))) :
    Finset (Fin (2 ^ n)) :=
  Finset.univ.biUnion fun i : Fin m ↦
    (tcHitRegs n d R (u i)).image fun q ↦ (localMemSlotReg n d q).extractIndex (u i)

theorem tcHarvestSet_subset {n m d : ℕ} (R : Finset (Fin (2 ^ n)))
    (u : Fin m → Fin (2 ^ (n * d))) :
    tcHarvestSet R u ⊆ R := by
  intro x hx
  simp only [tcHarvestSet, tcHitRegs, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_filter] at hx
  obtain ⟨i, q, hqR, rfl⟩ := hx
  exact hqR

theorem tcHasVerifHit_zero (n m d : ℕ) : tcHasVerifHit n m d 0 = false := by
  simp [tcHasVerifHit, tcVerifBitNat]

theorem tcVerifBitNat_packVerif (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    (u : Fin m → Fin (2 ^ (n * d))) (i : Fin m) (q : ℕ) (hq : q < d) :
    tcVerifBitNat n m (tcPackVerifBasis n m d Q hn12 hd12 hQ R u).val i q =
      decide ((localMemSlotReg n d ⟨q, hq⟩).extractIndex (u i) ∈ R) := by
  set o := tcPackVerifBasis n m d Q hn12 hd12 hQ R u
  let q12 : Fin 12 := ⟨q, by omega⟩
  have hidx : (tcVerifFlagReg n m Q hn12 hQ i q12 0).val =
      (n + 1) * m + 11 * m * n + i.val * 12 + q := by
    simp [q12]
  have hb_lhs : basisBits Q o (tcVerifFlagReg n m Q hn12 hQ i q12 0) =
      if tcVerifBitNat n m o.val i q then 1 else 0 := by
    rw [basisBits_eq_testBit, hidx]
    rfl
  have hb_rhs : basisBits Q o (tcVerifFlagReg n m Q hn12 hQ i q12 0) =
      if (localMemSlotReg n d ⟨q, hq⟩).extractIndex (u i) ∈ R then 1 else 0 := by
    dsimp only [o, tcPackVerifBasis]
    rw [Equiv.apply_symm_apply,
      tcBasisBits_pack_outside n m d Q (by omega) hd12 hQ u
        (fun k ↦ tcVerifWire_not_mem_conveyor hn12 hd12 hQ i k q12),
      zero_add, Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single ⟨q, hq⟩]
      · simp [q12]
      · intro q' _ hne
        have hnw : tcVerifFlagReg n m Q hn12 hQ i q12 0 ≠
            tcVerifFlagReg n m Q hn12 hQ i ⟨q'.val, by omega⟩ 0 := by
          intro h
          exact hne (Fin.ext (congrArg Fin.val (tcVerifWire_inj hn12 hQ h).2).symm)
        simp [hnw]
      · intro habs; exact (habs (Finset.mem_univ _)).elim
    · intro j _ hji
      refine Finset.sum_eq_zero fun q' _ ↦ ?_
      have hnw : tcVerifFlagReg n m Q hn12 hQ i q12 0 ≠
          tcVerifFlagReg n m Q hn12 hQ j ⟨q'.val, by omega⟩ 0 :=
        fun h ↦ hji (tcVerifWire_inj hn12 hQ h).1.symm
      simp [hnw]
    · intro habs; exact (habs (Finset.mem_univ i)).elim
  rw [hb_lhs] at hb_rhs
  cases hbit : tcVerifBitNat n m o.val i q <;>
    by_cases hmem : (localMemSlotReg n d ⟨q, hq⟩).extractIndex (u i) ∈ R <;>
    simp [hbit, hmem] at hb_rhs ⊢

theorem tcSubRegAddrNat_packVerif (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    (u : Fin m → Fin (2 ^ (n * d))) (i : Fin m) (q : ℕ) (hq : q < d) :
    tcSubRegAddrNat n m (tcPackVerifBasis n m d Q hn12 hd12 hQ R u).val i q =
      (localMemSlotReg n d ⟨q, hq⟩).extractIndex (u i) := by
  have hn : 0 < n := by omega
  apply (basisBits n).injective
  funext b
  rw [tcSubRegAddrNat, Equiv.apply_symm_apply, ← tcExtract_conveyor_packVerif n m d Q hn12 hd12
    hQ R u i, ← QRegister.extractIndex_compose, QRegister.basisBits_extractIndex]
  by_cases hq0 : q = 0
  · subst hq0
    have hidx : (tcActiveIdxReg n m Q hQ i b).val = i.val * (n + 1) + 1 + b.val := by
      rw [tcActiveIdxReg_apply_val]
      omega
    rw [tcSlotConveyorReg_compose_zero hn hq hd12 hQ i, basisBits_eq_testBit, hidx]
    simp
  · have hidx : (tcPassiveReg n m Q hQ i ⟨q - 1, by omega⟩ b).val =
        (n + 1) * m + (i.val * 11 + (q - 1)) * n + b.val := by
      rw [tcPassiveReg_apply_val]
    rw [tcSlotConveyorReg_compose_pos hn hd12 hQ i ⟨q, hq⟩ (show 1 ≤ q by omega),
      basisBits_eq_testBit, hidx]
    simp [hq0]

theorem tcDecodeHarvest_packVerif (n m d Q : ℕ) (hn12 : 12 ≤ n) (hd12 : d ≤ 12)
    (hQ : (n + 1) * m + 12 * m * n ≤ Q) (R : Finset (Fin (2 ^ n)))
    (u : Fin m → Fin (2 ^ (n * d))) :
    tcDecodeHarvest n m d (tcPackVerifBasis n m d Q hn12 hd12 hQ R u).val =
      tcHarvestSet R u := by
  ext x
  simp only [tcDecodeHarvest, tcHarvestSet, tcHitRegs, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_range, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨i, q, hq, hx⟩
    rw [tcVerifBitNat_packVerif n m d Q hn12 hd12 hQ R u i q hq,
      tcSubRegAddrNat_packVerif n m d Q hn12 hd12 hQ R u i q hq] at hx
    by_cases hmem : (localMemSlotReg n d ⟨q, hq⟩).extractIndex (u i) ∈ R
    · simp only [hmem, decide_true, ↓reduceIte, Finset.mem_singleton] at hx
      exact ⟨i, ⟨q, hq⟩, hmem, hx.symm⟩
    · simp [hmem] at hx
  · rintro ⟨i, q, hqR, rfl⟩
    refine ⟨i, q.val, q.isLt, ?_⟩
    rw [tcVerifBitNat_packVerif n m d Q hn12 hd12 hQ R u i q.val q.isLt,
      tcSubRegAddrNat_packVerif n m d Q hn12 hd12 hQ R u i q.val q.isLt]
    simp [hqR]

theorem tcHasVerifHit_eq_harvest_card (n m d : ℕ) (v : ℕ) :
    tcHasVerifHit n m d v = decide (1 ≤ (tcDecodeHarvest n m d v).card) := by
  rw [Bool.eq_iff_iff]
  simp only [tcHasVerifHit, List.any_eq_true, List.mem_finRange, true_and, List.mem_range,
    decide_eq_true_eq, Finset.one_le_card, Finset.Nonempty, tcDecodeHarvest, Finset.mem_biUnion,
    Finset.mem_univ, Finset.mem_range]
  constructor
  · rintro ⟨i, q, hq, hbit⟩
    exact ⟨tcSubRegAddrNat n m v i q, i, q, hq, by simp [hbit]⟩
  · rintro ⟨x, i, q, hq, hx⟩
    refine ⟨i, q, hq, ?_⟩
    by_cases hbit : tcVerifBitNat n m v i q
    · exact hbit
    · simp [hbit] at hx

/-! ## 4. Born `L1` Product Perturbation & Fiber-Uniform Coupon Occupancy -/

theorem sum_normSq_tcSlotConveyorVec (n d : ℕ) (hd1 : 1 ≤ d) (R : Finset (Fin (2 ^ n)))
    (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ) :
    ∑ z : Fin (2 ^ (n * d)),
      Complex.normSq (tcSlotConveyorVec n d hd1 R K_blk uFn steps z) = 1 := by
  unfold tcSlotConveyorVec
  rw [sum_normSq_unitary_mulVec, sum_normSq_unitary_mulVec, Finset.sum_eq_single 0]
  · simp
  · intro z _ hz; simp [Pi.single_eq_of_ne hz]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim

theorem sum_abs_normSq_sub_le {ι : Type*} [Fintype ι] (ψ₁ ψ₂ : ι → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (h1 : ∑ z : ι, Complex.normSq (ψ₁ z) = 1)
    (h2 : ∑ z : ι, Complex.normSq (ψ₂ z) = 1)
    (hdiff : ∑ z : ι, Complex.normSq (ψ₁ z - ψ₂ z) ≤ δ ^ 2) :
    ∑ z : ι, |Complex.normSq (ψ₁ z) - Complex.normSq (ψ₂ z)| ≤ (5 / 2 : ℝ) * δ := by
  have hpt (z : ι) :
      2 * δ * |Complex.normSq (ψ₁ z) - Complex.normSq (ψ₂ z)| ≤
        Complex.normSq (ψ₁ z - ψ₂ z) +
          2 * δ ^ 2 * (Complex.normSq (ψ₁ z) + Complex.normSq (ψ₂ z)) := by
    simp only [Complex.normSq_eq_norm_sq]
    have hnn_sum : 0 ≤ ‖ψ₁ z‖ + ‖ψ₂ z‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsub : |‖ψ₁ z‖ ^ 2 - ‖ψ₂ z‖ ^ 2| = |‖ψ₁ z‖ - ‖ψ₂ z‖| * (‖ψ₁ z‖ + ‖ψ₂ z‖) := by
      have hf : ‖ψ₁ z‖ ^ 2 - ‖ψ₂ z‖ ^ 2 = (‖ψ₁ z‖ - ‖ψ₂ z‖) * (‖ψ₁ z‖ + ‖ψ₂ z‖) := by ring
      rw [hf, abs_mul, abs_of_nonneg hnn_sum]
    have htri : |‖ψ₁ z‖ - ‖ψ₂ z‖| ≤ ‖ψ₁ z - ψ₂ z‖ := abs_norm_sub_norm_le (ψ₁ z) (ψ₂ z)
    have hmul := mul_le_mul_of_nonneg_right htri hnn_sum
    have hamgm1 : 0 ≤ (‖ψ₁ z - ψ₂ z‖ - δ * (‖ψ₁ z‖ + ‖ψ₂ z‖)) ^ 2 := sq_nonneg _
    have hamgm2 : 0 ≤ (‖ψ₁ z‖ - ‖ψ₂ z‖) ^ 2 := sq_nonneg _
    rw [hsub]
    nlinarith
  have hsum := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) ↦ hpt z
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    h1, h2] at hsum
  nlinarith

theorem sum_prod_pi_eq_one {α : Type*} [Fintype α] (m : ℕ) (p : α → ℝ)
    (hp : ∑ z : α, p z = 1) :
    ∑ u : Fin m → α, ∏ i : Fin m, p (u i) = 1 := by
  have h := (Fintype.prod_sum (fun (_ : Fin m) ↦ p)).symm
  simp only [hp, Finset.prod_const_one] at h
  exact h

theorem sum_abs_prod_sub_le {α : Type*} [Fintype α] (m : ℕ) (p₁ p₂ : α → ℝ)
    (hp1_nn : ∀ z, 0 ≤ p₁ z) (hp2_nn : ∀ z, 0 ≤ p₂ z)
    (hp1_sum : ∑ z : α, p₁ z = 1) (hp2_sum : ∑ z : α, p₂ z = 1) :
    ∑ u : Fin m → α, |(∏ i : Fin m, p₁ (u i)) - (∏ i : Fin m, p₂ (u i))| ≤
      (m : ℝ) * ∑ z : α, |p₁ z - p₂ z| := by
  induction m with
  | zero => simp
  | succ m ih =>
      let eqCons : α × (Fin m → α) ≃ (Fin (m + 1) → α) :=
        { toFun := fun p ↦ Fin.cons p.1 p.2
          invFun := fun u ↦ (u 0, fun i ↦ u i.succ)
          left_inv := fun ⟨x, y⟩ ↦ by simp
          right_inv := fun u ↦ by funext i; refine Fin.cases ?_ ?_ i <;> simp }
      rw [← eqCons.sum_comp, Fintype.sum_prod_type]
      have hstep (z : α) (u : Fin m → α) :
          |(∏ i : Fin (m + 1), p₁ (eqCons (z, u) i)) -
              (∏ i : Fin (m + 1), p₂ (eqCons (z, u) i))| ≤
            |p₁ z - p₂ z| * (∏ i : Fin m, p₁ (u i)) +
              p₂ z * |(∏ i : Fin m, p₁ (u i)) - (∏ i : Fin m, p₂ (u i))| := by
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        simp only [eqCons, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
        have hid : p₁ z * (∏ i : Fin m, p₁ (u i)) - p₂ z * (∏ i : Fin m, p₂ (u i)) =
            (p₁ z - p₂ z) * (∏ i : Fin m, p₁ (u i)) +
              p₂ z * ((∏ i : Fin m, p₁ (u i)) - (∏ i : Fin m, p₂ (u i))) := by ring
        have hpr1 : 0 ≤ ∏ i : Fin m, p₁ (u i) := Finset.prod_nonneg fun i _ ↦ hp1_nn (u i)
        rw [hid]
        exact (abs_add_le _ _).trans_eq (by
          rw [abs_mul, abs_mul, abs_of_nonneg hpr1, abs_of_nonneg (hp2_nn z)])
      have hle :
          ∑ x : α, ∑ y : Fin m → α,
              |(∏ i : Fin (m + 1), p₁ (eqCons (x, y) i)) -
                (∏ i : Fin (m + 1), p₂ (eqCons (x, y) i))| ≤
            ∑ x : α, ∑ y : Fin m → α,
              (|p₁ x - p₂ x| * (∏ i : Fin m, p₁ (y i)) +
                p₂ x * |(∏ i : Fin m, p₁ (y i)) - (∏ i : Fin m, p₂ (y i))|) :=
        Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦ hstep x y
      refine hle.trans ?_
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_prod_pi_eq_one m p₁ hp1_sum, mul_one,
        ← Finset.sum_mul, hp2_sum, one_mul, Nat.cast_add, Nat.cast_one]
      linarith

/-- Equivalence between an `n * d`-qubit conveyor slot and `d` addresses in `Fin (2 ^ n)`. -/
def tcSlotTupleEquiv (n d : ℕ) (hn : 0 < n) : Fin (2 ^ (n * d)) ≃ (Fin d → Fin (2 ^ n)) where
  toFun z q := (localMemSlotReg n d q).extractIndex z
  invFun f := (basisBits (n * d)).symm fun w ↦
    basisBits n (f ⟨w.val / n, Nat.div_lt_of_lt_mul w.isLt⟩)
      ⟨w.val % n, Nat.mod_lt _ hn⟩
  left_inv z := by
    apply (basisBits (n * d)).injective
    funext w
    rw [Equiv.apply_symm_apply, QRegister.basisBits_extractIndex]
    refine congrArg (basisBits (n * d) z) (Fin.ext ?_)
    simp only [localMemSlotReg, QRegister.block_apply_val]
    linarith [Nat.div_add_mod w.val n]
  right_inv f := by
    funext q
    apply (basisBits n).injective
    funext b
    rw [QRegister.basisBits_extractIndex, Equiv.apply_symm_apply]
    have hqb : q.val * n + b.val = n * q.val + b.val := by ring
    have hdiv : (q.val * n + b.val) / n = q.val := by
      rw [hqb, Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, add_zero]
    have hmod : (q.val * n + b.val) % n = b.val := by
      rw [hqb, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
    simp [localMemSlotReg, hdiv, hmod]

/-- Coordinatewise hit-swap involution on `Fin (2 ^ n) × R`. -/
def tcHitSwapCoord {n : ℕ} {R : Finset (Fin (2 ^ n))} (p : Fin (2 ^ n) × {x // x ∈ R}) :
    Fin (2 ^ n) × {x // x ∈ R} :=
  if hx : p.1 ∈ R then (p.2.1, ⟨p.1, hx⟩) else p

theorem tcHitSwapCoord_involutive {n : ℕ} {R : Finset (Fin (2 ^ n))} :
    Function.Involutive (tcHitSwapCoord (R := R)) := by
  rintro ⟨x, y⟩
  by_cases hx : x ∈ R
  · have h1 : tcHitSwapCoord (x, y) = (y.1, ⟨x, hx⟩) := by simp [tcHitSwapCoord, hx]
    rw [h1]
    simp [tcHitSwapCoord, y.2]
  · have h1 : tcHitSwapCoord (x, y) = (x, y) := by simp [tcHitSwapCoord, hx]
    rw [h1, h1]

theorem tcHitSwapCoord_fst_mem_iff {n : ℕ} {R : Finset (Fin (2 ^ n))}
    (p : Fin (2 ^ n) × {x // x ∈ R}) :
    (tcHitSwapCoord p).1 ∈ R ↔ p.1 ∈ R := by
  dsimp only [tcHitSwapCoord]
  split_ifs with hx
  · simp [hx, p.2.2]
  · simp [hx]

theorem tcCouponTail_card_filter_eq {I : Type*} [Fintype I] [DecidableEq I]
    {n : ℕ} (R : Finset (Fin (2 ^ n))) (hr1 : 1 ≤ R.card)
    (W : Finset I) (j : ℕ) :
    (((Finset.univ.filter fun g : I → {x // x ∈ R} ↦
        j ≤ (W.image fun idx ↦ (g idx).1).card).card : ℕ) : ℝ) /
      (R.card : ℝ) ^ Fintype.card I =
    tcCouponTailReal R.card W.card j := by
  have hr_pos : (0 : ℝ) < (R.card : ℝ) := by positivity
  have hcardR : Fintype.card {x // x ∈ R} = R.card := Fintype.card_coe R
  induction W using Finset.induction_on generalizing j with
  | empty =>
      simp only [Finset.image_empty, Finset.card_empty, tcCouponTailReal]
      by_cases hj0 : j = 0
      · subst hj0
        simp [Fintype.card_pi, hcardR, div_self (pow_ne_zero _ hr_pos.ne')]
      · have hgt : ¬ (j ≤ 0) := by omega
        simp [hj0, hgt]
  | @insert a W ha ih =>
      rw [Finset.card_insert_of_notMem ha]
      -- Split `g: I → R` into `(g_rest: {idx // idx ≠ a} → R) × {x // x ∈ R}`
      let splitG : (I → {x // x ∈ R}) ≃ ({idx : I // idx ≠ a} → {x // x ∈ R}) × {x // x ∈ R} :=
        { toFun := fun g ↦ (fun idx ↦ g idx.1, g a)
          invFun := fun p idx ↦ if h : idx = a then p.2 else p.1 ⟨idx, h⟩
          left_inv := fun g ↦ by funext idx; by_cases h : idx = a <;> simp [h]
          right_inv := fun ⟨gr, ga⟩ ↦ by
            apply Prod.ext
            · funext idx; simp [idx.2]
            · simp }
      have himg_split (gr : {idx : I // idx ≠ a} → {x // x ∈ R}) (ga : {x // x ∈ R}) :
          ((insert a W).image fun idx ↦ (splitG.symm (gr, ga) idx).1) =
            insert ga.1 (W.image fun idx ↦ (splitG.symm (gr, ga) idx).1) := by
        simp [splitG, Finset.image_insert]
      have himg_indep (gr : {idx : I // idx ≠ a} → {x // x ∈ R}) (ga₁ ga₂ : {x // x ∈ R}) :
          (W.image fun idx ↦ (splitG.symm (gr, ga₁) idx).1) =
            (W.image fun idx ↦ (splitG.symm (gr, ga₂) idx).1) := by
        refine Finset.image_congr fun idx hidx ↦ ?_
        have hne : idx ≠ a := fun h ↦ ha (h ▸ hidx)
        simp [splitG, hne]
      obtain ⟨y₀, hy₀⟩ := Finset.card_pos.1 hr1
      let ga₀ : {x // x ∈ R} := ⟨y₀, hy₀⟩
      let Sg (gr : {idx : I // idx ≠ a} → {x // x ∈ R}) : Finset (Fin (2 ^ n)) :=
        W.image fun idx ↦ (splitG.symm (gr, ga₀) idx).1
      have hSg_sub (gr : {idx : I // idx ≠ a} → {x // x ∈ R}) : Sg gr ⊆ R := by
        intro x hx
        rcases Finset.mem_image.1 hx with ⟨idx, _, rfl⟩
        exact (splitG.symm (gr, ga₀) idx).2
      have hcount_step (k : ℕ) :
          ((Finset.univ.filter fun g : I → {x // x ∈ R} ↦
              k ≤ (W.image fun idx ↦ (g idx).1).card).card : ℝ) =
            (R.card : ℝ) *
              ∑ gr : {idx : I // idx ≠ a} → {x // x ∈ R},
                if k ≤ (Sg gr).card then (1 : ℝ) else 0 := by
        rw [Finset.card_filter, Nat.cast_sum, ← splitG.symm.sum_comp, Fintype.sum_prod_type]
        simp_rw [himg_indep _ _ ga₀, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        change (∑ gr, ∑ _ga : {x // x ∈ R}, if k ≤ (Sg gr).card then (1 : ℝ) else 0) = _
        simp_rw [Finset.sum_const, Finset.card_univ, hcardR, nsmul_eq_mul, ← Finset.mul_sum]
      have hcount_ins :
          ((Finset.univ.filter fun g : I → {x // x ∈ R} ↦
              j ≤ ((insert a W).image fun idx ↦ (g idx).1).card).card : ℝ) =
            ∑ gr : {idx : I // idx ≠ a} → {x // x ∈ R},
              ∑ ga : {x // x ∈ R},
                if j ≤ (insert ga.1 (Sg gr)).card then (1 : ℝ) else 0 := by
        rw [Finset.card_filter, Nat.cast_sum, ← splitG.symm.sum_comp, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun gr _ ↦ Finset.sum_congr rfl fun ga _ ↦ ?_
        rw [himg_split, himg_indep gr ga ga₀, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      unfold tcCouponTailReal
      by_cases hj0 : j = 0
      · subst hj0
        simp [Fintype.card_pi, hcardR, div_self (pow_ne_zero _ hr_pos.ne')]
      · simp only [hj0, ↓reduceIte]
        by_cases hjr : j ≤ R.card
        · simp only [hjr, ↓reduceIte]
          have hinner (gr : {idx : I // idx ≠ a} → {x // x ∈ R}) :
              (∑ ga : {x // x ∈ R},
                  if j ≤ (insert ga.1 (Sg gr)).card then (1 : ℝ) else 0) =
                ((j - 1 : ℕ) : ℝ) * (if j ≤ (Sg gr).card then 1 else 0) +
                  ((R.card + 1 - j : ℕ) : ℝ) * (if j - 1 ≤ (Sg gr).card then 1 else 0) := by
            have hScard_le : (Sg gr).card ≤ R.card := Finset.card_le_card (hSg_sub gr)
            by_cases hge : j ≤ (Sg gr).card
            · have hge1 : j - 1 ≤ (Sg gr).card := by omega
              have hall : ∀ ga : {x // x ∈ R}, j ≤ (insert ga.1 (Sg gr)).card :=
                fun ga ↦ hge.trans (Finset.card_le_card (Finset.subset_insert _ _))
              simp only [hall, hge, hge1, ↓reduceIte, Finset.sum_const, Finset.card_univ, hcardR,
                nsmul_eq_mul, mul_one]
              exact_mod_cast (show R.card = (j - 1) + (R.card + 1 - j) by omega)
            · by_cases heq1 : (Sg gr).card = j - 1
              · have hge1 : j - 1 ≤ (Sg gr).card := by omega
                have hiff (ga : {x // x ∈ R}) :
                    j ≤ (insert ga.1 (Sg gr)).card ↔ ga.1 ∈ R \ Sg gr := by
                  by_cases hmem : ga.1 ∈ Sg gr
                  · rw [Finset.insert_eq_of_mem hmem]
                    simp [hmem, hge]
                  · rw [Finset.card_insert_of_notMem hmem, heq1]
                    simp [hmem, ga.2, show j ≤ j - 1 + 1 by omega]
                simp_rw [hiff]
                have hbij : (∑ ga : {x // x ∈ R}, if ga.1 ∈ R \ Sg gr then (1 : ℝ) else 0) =
                    ((R \ Sg gr).card : ℝ) := by
                  rw [Finset.sum_coe_sort R (fun x ↦ if x ∈ R \ Sg gr then (1 : ℝ) else 0),
                    ← Finset.sum_filter]
                  have hfeq : R.filter (fun x ↦ x ∈ R \ Sg gr) = R \ Sg gr := by
                    ext x; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
                  rw [hfeq, Finset.sum_const, nsmul_eq_mul, mul_one]
                rw [ite_eq_right hge, ite_eq_left hge1, mul_zero, zero_add, mul_one, hbij,
                  Finset.card_sdiff, Finset.inter_eq_left.2 (hSg_sub gr), heq1]
                exact_mod_cast (show R.card - (j - 1) = R.card + 1 - j by omega)
              · have hn1 : ¬ (j - 1 ≤ (Sg gr).card) := by omega
                have hnone : ∀ ga : {x // x ∈ R}, ¬ (j ≤ (insert ga.1 (Sg gr)).card) := by
                  intro ga
                  have hle1 := Finset.card_insert_le ga.1 (Sg gr)
                  omega
                simp [hnone, hge, hn1]
          rw [hcount_ins]
          simp_rw [hinner, Finset.sum_add_distrib, ← Finset.mul_sum]
          set S1 := ∑ gr : {idx : I // idx ≠ a} → {x // x ∈ R},
            if j ≤ (Sg gr).card then (1 : ℝ) else 0
          set S2 := ∑ gr : {idx : I // idx ≠ a} → {x // x ∈ R},
            if j - 1 ≤ (Sg gr).card then (1 : ℝ) else 0
          rw [← ih j, ← ih (j - 1), hcount_step j, hcount_step (j - 1)]
          field_simp [hr_pos.ne', pow_ne_zero (Fintype.card I) hr_pos.ne']
          ring
        · have hnone : ∀ gr (ga : {x // x ∈ R}), ¬ (j ≤ (insert ga.1 (Sg gr)).card) := by
            intro gr ga
            have hsub : insert ga.1 (Sg gr) ⊆ R :=
              Finset.insert_subset_iff.2 ⟨ga.2, hSg_sub gr⟩
            have hle := Finset.card_le_card hsub
            omega
          rw [hcount_ins]
          simp [hnone, hjr]

theorem sum_convPow2_eq {α : Type*} [Fintype α] (d : ℕ) (wt : α → ℕ)
    (hwt : ∀ x, wt x ≤ d) (pA : α → ℝ) (pW : ℕ → ℝ)
    (hpW : ∀ w ≤ d, (∑ x : α with wt x = w, pA x) = pW w) :
    ∀ (e h : ℕ), h ≤ 2 ^ e * d →
      (∑ u : Fin (2 ^ e) → α with (∑ i : Fin (2 ^ e), wt (u i)) = h,
        ∏ i : Fin (2 ^ e), pA (u i)) =
      tcConvPow2Real d pW e h := by
  intro e
  induction e with
  | zero =>
      intro h hh
      simp only [pow_zero, one_mul] at hh
      unfold tcConvPow2Real
      rw [← hpW h hh]
      let eq1 : (Fin 1 → α) ≃ α := Equiv.funUnique (Fin 1) α
      rw [Finset.sum_filter, Finset.sum_filter, ← eq1.sum_comp]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      simp [eq1]
  | succ e ih =>
      intro h hh
      unfold tcConvPow2Real tcConvReal
      let eIdx : Fin (2 ^ (e + 1)) ≃ Fin (2 ^ e) ⊕ Fin (2 ^ e) :=
        (finCongr (show 2 ^ (e + 1) = 2 ^ e + 2 ^ e by omega)).trans finSumFinEquiv.symm
      let splitE : (Fin (2 ^ (e + 1)) → α) ≃ (Fin (2 ^ e) → α) × (Fin (2 ^ e) → α) :=
        { toFun := fun f ↦
            (fun j ↦ f (eIdx.symm (Sum.inl j)), fun j ↦ f (eIdx.symm (Sum.inr j)))
          invFun := fun p i ↦ Sum.elim p.1 p.2 (eIdx i)
          left_inv := fun f ↦ by
            funext i
            change (Sum.elim (fun j ↦ f (eIdx.symm (Sum.inl j)))
              (fun j ↦ f (eIdx.symm (Sum.inr j)))) (eIdx i) = f i
            generalize he : eIdx i = s
            rcases s with j | j
            · simp only [Sum.elim_inl]; rw [← he, Equiv.symm_apply_apply]
            · simp only [Sum.elim_inr]; rw [← he, Equiv.symm_apply_apply]
          right_inv := fun ⟨u₁, u₂⟩ ↦ by
            apply Prod.ext <;> funext j <;> simp }
      have hsum_wt (u₁ u₂ : Fin (2 ^ e) → α) :
          (∑ i : Fin (2 ^ (e + 1)), wt (splitE.symm (u₁, u₂) i)) =
            (∑ i : Fin (2 ^ e), wt (u₁ i)) + (∑ i : Fin (2 ^ e), wt (u₂ i)) :=
        (eIdx.sum_comp (fun s ↦ wt (Sum.elim u₁ u₂ s))).trans (Fintype.sum_sum_type _)
      have hprod_pA (u₁ u₂ : Fin (2 ^ e) → α) :
          (∏ i : Fin (2 ^ (e + 1)), pA (splitE.symm (u₁, u₂) i)) =
            (∏ i : Fin (2 ^ e), pA (u₁ i)) * (∏ i : Fin (2 ^ e), pA (u₂ i)) :=
        (eIdx.prod_comp (fun s ↦ pA (Sum.elim u₁ u₂ s))).trans (Fintype.prod_sum_type _)
      have hwt_bd (u₁ : Fin (2 ^ e) → α) : (∑ i : Fin (2 ^ e), wt (u₁ i)) ≤ 2 ^ e * d := by
        calc ∑ i : Fin (2 ^ e), wt (u₁ i) ≤ ∑ _i : Fin (2 ^ e), d :=
              Finset.sum_le_sum fun i _ ↦ hwt (u₁ i)
          _ = 2 ^ e * d := by simp
      rw [Finset.sum_filter, ← splitE.symm.sum_comp, Fintype.sum_prod_type]
      simp_rw [hsum_wt, hprod_pA]
      -- Partition `u₁` by `w₁ = ∑ i, wt (u₁ i) ∈ range (2 ^ e * d + 1)`
      have hpart :
          (∑ u₁ : Fin (2 ^ e) → α, ∑ u₂ : Fin (2 ^ e) → α,
              if (∑ i, wt (u₁ i)) + (∑ i, wt (u₂ i)) = h then
                (∏ i, pA (u₁ i)) * (∏ i, pA (u₂ i))
              else 0) =
            ∑ w₁ ∈ Finset.range (2 ^ e * d + 1),
              (∑ u₁ : Fin (2 ^ e) → α with (∑ i, wt (u₁ i)) = w₁, ∏ i, pA (u₁ i)) *
                (∑ u₂ : Fin (2 ^ e) → α with w₁ + (∑ i, wt (u₂ i)) = h, ∏ i, pA (u₂ i)) := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (g := fun u₁ : Fin (2 ^ e) → α ↦ ∑ i, wt (u₁ i))
          (t := Finset.range (2 ^ e * d + 1))
          (fun u₁ _ ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (hwt_bd u₁)))]
        refine Finset.sum_congr rfl fun w₁ _ ↦ ?_
        simp_rw [Finset.sum_filter]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u₁ _ ↦ ?_
        by_cases hw1 : (∑ i, wt (u₁ i)) = w₁
        · simp [hw1, Finset.mul_sum]
        · simp [hw1]
      rw [hpart]
      refine Finset.sum_congr rfl fun w₁ hw₁ ↦ ?_
      have hw1_le : w₁ ≤ 2 ^ e * d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hw₁)
      by_cases hcond : w₁ ≤ h ∧ h - w₁ ≤ 2 ^ e * d
      · simp only [hcond, and_self, ↓reduceIte]
        have hfeq : (Finset.univ.filter fun u₂ : Fin (2 ^ e) → α ↦
            w₁ + (∑ i, wt (u₂ i)) = h) =
            (Finset.univ.filter fun u₂ : Fin (2 ^ e) → α ↦
              (∑ i, wt (u₂ i)) = h - w₁) := by
          ext u₂; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
        rw [hfeq, ih w₁ hw1_le, ih (h - w₁) hcond.2]
      · simp only [hcond, ↓reduceIte]
        have hempty : ∀ u₂ : Fin (2 ^ e) → α, ¬ (w₁ + (∑ i, wt (u₂ i)) = h) := by
          intro u₂ heq
          have hb2 := hwt_bd u₂
          exact hcond ⟨by omega, by omega⟩
        simp [Finset.sum_filter, hempty]

theorem sum_ideal_harvest_ge_eq_conv_coupon {n d e : ℕ} (hn : 0 < n)
    (R : Finset (Fin (2 ^ n))) (hr1 : 1 ≤ R.card)
    (ψ_id : Fin (2 ^ (n * d)) → ℂ) (pW : ℕ → ℝ)
    (hsym : ∀ z₁ z₂ : Fin (2 ^ (n * d)),
      tcHitRegs n d R z₁ = tcHitRegs n d R z₂ →
        Complex.normSq (ψ_id z₁) = Complex.normSq (ψ_id z₂))
    (hpW : ∀ w ≤ d,
      (∑ z : Fin (2 ^ (n * d)) with (tcHitRegs n d R z).card = w,
        Complex.normSq (ψ_id z)) = pW w)
    (j : ℕ) :
    (∑ u : Fin (2 ^ e) → Fin (2 ^ (n * d)) with j ≤ (tcHarvestSet R u).card,
      ∏ i : Fin (2 ^ e), Complex.normSq (ψ_id (u i))) =
    ∑ h ∈ Finset.range (2 ^ e * d + 1),
      tcConvPow2Real d pW e h * tcCouponTailReal R.card h j := by
  set m := 2 ^ e
  let tupEq := tcSlotTupleEquiv n d hn
  -- Involution on `(Fin m → Fin (2 ^ (n * d))) × (Fin m × Fin d → {x // x ∈ R})`
  let swapAll :
      ((Fin m → Fin (2 ^ (n * d))) × (Fin m × Fin d → {x // x ∈ R})) →
      ((Fin m → Fin (2 ^ (n * d))) × (Fin m × Fin d → {x // x ∈ R})) :=
    fun ⟨u, g⟩ ↦
      (fun i ↦ tupEq.symm fun q ↦ (tcHitSwapCoord (tupEq (u i) q, g (i, q))).1,
       fun ⟨i, q⟩ ↦ (tcHitSwapCoord (tupEq (u i) q, g (i, q))).2)
  have hswapAll_inv : Function.Involutive swapAll := by
    rintro ⟨u, g⟩
    apply Prod.ext
    · funext i
      apply tupEq.injective
      funext q
      simp only [swapAll, Equiv.apply_symm_apply]
      exact congrArg Prod.fst (tcHitSwapCoord_involutive (tupEq (u i) q, g (i, q)))
    · funext ⟨i, q⟩
      simp only [swapAll, Equiv.apply_symm_apply]
      exact congrArg Prod.snd (tcHitSwapCoord_involutive (tupEq (u i) q, g (i, q)))
  let swapEquiv : Equiv.Perm ((Fin m → Fin (2 ^ (n * d))) × (Fin m × Fin d → {x // x ∈ R})) :=
    hswapAll_inv.toPerm
  have hhit_pres (u : Fin m → Fin (2 ^ (n * d))) (g : Fin m × Fin d → {x // x ∈ R}) (i : Fin m) :
      tcHitRegs n d R ((swapAll (u, g)).1 i) = tcHitRegs n d R (u i) := by
    ext q
    simp only [tcHitRegs, Finset.mem_filter, Finset.mem_univ, true_and]
    change tupEq ((swapAll (u, g)).1 i) q ∈ R ↔ tupEq (u i) q ∈ R
    simp only [swapAll, Equiv.apply_symm_apply]
    exact tcHitSwapCoord_fst_mem_iff _
  let hitPairs (u : Fin m → Fin (2 ^ (n * d))) : Finset (Fin m × Fin d) :=
    Finset.univ.filter fun p : Fin m × Fin d ↦ (localMemSlotReg n d p.2).extractIndex (u p.1) ∈ R
  have hcard_hitPairs (u : Fin m → Fin (2 ^ (n * d))) :
      (hitPairs u).card = ∑ i : Fin m, (tcHitRegs n d R (u i)).card := by
    simp only [hitPairs, tcHitRegs, Finset.card_filter]
    rw [Fintype.sum_prod_type]
  have hharv_swap (u : Fin m → Fin (2 ^ (n * d))) (g : Fin m × Fin d → {x // x ∈ R}) :
      tcHarvestSet R (swapAll (u, g)).1 = (hitPairs u).image (fun p ↦ (g p).1) := by
    unfold tcHarvestSet
    simp_rw [hhit_pres]
    ext x
    simp only [tcHitRegs, hitPairs, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_filter, Prod.exists]
    constructor
    · rintro ⟨i, q, hqR, rfl⟩
      refine ⟨i, q, hqR, ?_⟩
      change (g (i, q)).1 = tupEq ((swapAll (u, g)).1 i) q
      simp only [swapAll, Equiv.apply_symm_apply, tcHitSwapCoord]
      have hqR' : tupEq (u i) q ∈ R := hqR
      simp [hqR']
    · rintro ⟨i, q, hqR, rfl⟩
      refine ⟨i, q, hqR, ?_⟩
      change tupEq ((swapAll (u, g)).1 i) q = (g (i, q)).1
      simp only [swapAll, Equiv.apply_symm_apply, tcHitSwapCoord]
      have hqR' : tupEq (u i) q ∈ R := hqR
      simp [hqR']
  have hr_pos : (0 : ℝ) < (R.card : ℝ) := by positivity
  have hcardG : (Fintype.card (Fin m × Fin d → {x // x ∈ R}) : ℝ) =
      (R.card : ℝ) ^ Fintype.card (Fin m × Fin d) := by
    rw [Fintype.card_pi]
    simp [Fintype.card_coe]
  have hsym_avg :
      (∑ u : Fin m → Fin (2 ^ (n * d)) with j ≤ (tcHarvestSet R u).card,
          ∏ i : Fin m, Complex.normSq (ψ_id (u i))) =
        ∑ u : Fin m → Fin (2 ^ (n * d)),
          (∏ i : Fin m, Complex.normSq (ψ_id (u i))) *
            tcCouponTailReal R.card (∑ i : Fin m, (tcHitRegs n d R (u i)).card) j := by
    rw [Finset.sum_filter]
    have hconst : ∀ u : Fin m → Fin (2 ^ (n * d)),
        (if j ≤ (tcHarvestSet R u).card then ∏ i : Fin m, Complex.normSq (ψ_id (u i)) else 0) =
        (∑ _g : Fin m × Fin d → {x // x ∈ R},
            if j ≤ (tcHarvestSet R u).card then
              ∏ i : Fin m, Complex.normSq (ψ_id (u i))
            else 0) /
          (R.card : ℝ) ^ Fintype.card (Fin m × Fin d) := by
      intro u
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardG,
        mul_div_cancel_left₀ _ (pow_ne_zero _ hr_pos.ne')]
    let fPre :
        ((Fin m → Fin (2 ^ (n * d))) × (Fin m × Fin d → {x // x ∈ R})) → ℝ :=
      fun p ↦ if j ≤ (tcHarvestSet R p.1).card then
        ∏ i : Fin m, Complex.normSq (ψ_id (p.1 i)) else 0
    rw [Finset.sum_congr rfl fun u _ ↦ hconst u, ← tcFinset_sum_div,
      ← Fintype.sum_prod_type fPre, ← Equiv.sum_comp swapEquiv fPre,
      Fintype.sum_prod_type (fun p ↦ fPre (swapEquiv p))]
    change (∑ u, ∑ g,
        if j ≤ (tcHarvestSet R (swapAll (u, g)).1).card then
          ∏ i : Fin m, Complex.normSq (ψ_id ((swapAll (u, g)).1 i))
        else 0) / _ = _
    have hprod_eq (u : Fin m → Fin (2 ^ (n * d))) (g : Fin m × Fin d → {x // x ∈ R}) :
        (∏ i : Fin m, Complex.normSq (ψ_id ((swapAll (u, g)).1 i))) =
          ∏ i : Fin m, Complex.normSq (ψ_id (u i)) :=
      Finset.prod_congr rfl fun i _ ↦ hsym _ _ (hhit_pres u g i)
    simp_rw [hharv_swap, hprod_eq]
    rw [tcFinset_sum_div]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    have hpull :
        (∑ g : Fin m × Fin d → {x // x ∈ R},
            if j ≤ ((hitPairs u).image fun p ↦ (g p).1).card then
              ∏ i : Fin m, Complex.normSq (ψ_id (u i))
            else 0) =
          (∏ i : Fin m, Complex.normSq (ψ_id (u i))) *
            (((Finset.univ.filter fun g : Fin m × Fin d → {x // x ∈ R} ↦
              j ≤ ((hitPairs u).image fun p ↦ (g p).1).card).card : ℕ) : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      by_cases hj : j ≤ ((hitPairs u).image fun p ↦ (g p).1).card <;> simp [hj]
    rw [hpull, mul_div_assoc, tcCouponTail_card_filter_eq R hr1 (hitPairs u) j, hcard_hitPairs]
  rw [hsym_avg]
  have hwt_u (u : Fin m → Fin (2 ^ (n * d))) :
      (∑ i : Fin m, (tcHitRegs n d R (u i)).card) ≤ m * d := by
    calc ∑ i : Fin m, (tcHitRegs n d R (u i)).card ≤ ∑ _i : Fin m, d :=
          Finset.sum_le_sum fun i _ ↦ (Finset.card_filter_le _ _).trans_eq (by simp)
      _ = m * d := by simp
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun u : Fin m → Fin (2 ^ (n * d)) ↦ ∑ i : Fin m, (tcHitRegs n d R (u i)).card)
    (t := Finset.range (m * d + 1))
    (fun u _ ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (hwt_u u)))]
  refine Finset.sum_congr rfl fun h hh ↦ ?_
  have hh_le : h ≤ m * d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hh)
  have hconst_h :
      (∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin (2 ^ (n * d)) ↦
          (∑ i : Fin m, (tcHitRegs n d R (u i)).card) = h),
        (∏ i : Fin m, Complex.normSq (ψ_id (u i))) * tcCouponTailReal R.card
          (∑ i : Fin m, (tcHitRegs n d R (u i)).card) j) =
      (∑ u : Fin m → Fin (2 ^ (n * d)) with
          (∑ i : Fin m, (tcHitRegs n d R (u i)).card) = h,
        ∏ i : Fin m, Complex.normSq (ψ_id (u i))) * tcCouponTailReal R.card h j := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    rw [(Finset.mem_filter.1 hu).2]
  rw [hconst_h, sum_convPow2_eq d (fun z ↦ (tcHitRegs n d R z).card)
    (fun z ↦ (Finset.card_filter_le _ _).trans_eq (by simp))
    (fun z ↦ Complex.normSq (ψ_id z)) pW hpW e h hh_le]

theorem tcActualHarvest_tail_lb {e n : ℕ} (hn700 : 700 ≤ n) (he : e ≤ 10)
    {sc : TensorSchedCert} {rMin sMax : ℕ} {convLb tailLb : ℕ → ℤ}
    {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card) (hr1024 : R.card ≤ 1024)
    (hrMin : rMin ≤ R.card)
    (hsc : tcCheckSched sc = true)
    (hconv : tcCheckConvPow2 e sc.d sc.wProbLb convLb = true)
    (hcoup : tcCheckCouponBucket rMin sMax (2 ^ e * sc.d) convLb tailLb = true) :
    let K_blk := tcKBlk n R.card sc.tauNum sc.tauDen
    let pSlot : Fin (2 ^ (n * sc.d)) → ℝ := fun z ↦
      Complex.normSq (tcSlotConveyorVec n sc.d (by
        have h := tcCheckSched_sound hn700 hr1 hr1024 hsc; omega)
        R K_blk sc.uFn sc.steps z)
    1 ≤ sMax ∧ sMax ≤ R.card ∧ 1 ≤ tailLb 1 ∧
    ∀ s, 1 ≤ s → s ≤ sMax →
      0 ≤ tailLb s ∧
      (tailLb s : ℝ) / (tcScale : ℝ) ≤
        ∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)) with s ≤ (tcHarvestSet R u).card,
          ∏ i : Fin (2 ^ e), pSlot (u i) := by
  intro K_blk pSlot
  rcases tcCheckSched_sound hn700 hr1 hr1024 hsc with
    ⟨hd2, hd12, _, hst250, _, _, hu_nz, hw_lb, _, hsqrt_ge⟩
  obtain ⟨ψ_id, hunit_id, hdiff_sq, hsym_id, hpW_id⟩ :=
    tcSlotConveyorVec_ideal_approx hn700 hd2 hd12 R hr1 hr1024 K_blk sc.steps hst250 sc.uFn hu_nz
  set a := tcEvolutionReal sc.d
    (Real.cos ((K_blk : ℝ) * tcTheta1Real (2 ^ n) R.card))
    (Real.sin ((K_blk : ℝ) * tcTheta1Real (2 ^ n) R.card)) sc.uFn sc.steps
  have hconv_lb : ∀ h ≤ 2 ^ e * sc.d,
      (convLb h : ℝ) / (tcScale : ℝ) ≤ tcConvPow2Real sc.d (tcWeightProbReal sc.d a) e h :=
    fun h hh ↦ (tcCheckConvPow2_sound hw_lb hconv h hh).2
  set pActual : ℕ → ℝ := fun s ↦
    ∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)) with s ≤ (tcHarvestSet R u).card,
      ∏ i : Fin (2 ^ e), pSlot (u i)
  have hp0 : ∀ s, 0 ≤ pActual s := fun s ↦
    Finset.sum_nonneg fun u _ ↦ Finset.prod_nonneg fun i _ ↦ Complex.normSq_nonneg _
  refine tcCheckCouponBucket_actual_le hrMin hconv_lb hp0 (fun s hs1 hsMax ↦ ?_) hcoup
  rw [← sum_ideal_harvest_ge_eq_conv_coupon (by omega) R hr1 ψ_id
    (tcWeightProbReal sc.d a) hsym_id hpW_id s]
  -- Bound `∑_{u: s ≤ card} p_id(u) - ∑_{u: s ≤ card} pSlot(u) ≤ 1 / tcScale`
  set δ : ℝ := (2 * ((sc.steps + 1 : ℕ) : ℝ) * (sc.d : ℝ)) * √((R.card : ℝ) / (2 ^ n : ℝ))
  have hratio_pos : (0 : ℝ) < √((R.card : ℝ) / (2 ^ n : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hL1_slot : ∑ z : Fin (2 ^ (n * sc.d)), |pSlot z - Complex.normSq (ψ_id z)| ≤
      (5 / 2 : ℝ) * δ :=
    sum_abs_normSq_sub_le _ ψ_id hδ_pos
      (sum_normSq_tcSlotConveyorVec n sc.d (by omega) R K_blk sc.uFn sc.steps) hunit_id hdiff_sq
  have hL1_prod :
      ∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)),
          |(∏ i, pSlot (u i)) - (∏ i, Complex.normSq (ψ_id (u i)))| ≤
        ((2 ^ e : ℕ) : ℝ) * ((5 / 2 : ℝ) * δ) := by
    refine (sum_abs_prod_sub_le (2 ^ e) pSlot (fun z ↦ Complex.normSq (ψ_id z))
      (fun _ ↦ Complex.normSq_nonneg _) (fun _ ↦ Complex.normSq_nonneg _)
      (sum_normSq_tcSlotConveyorVec n sc.d (by omega) R K_blk sc.uFn sc.steps) hunit_id).trans ?_
    exact mul_le_mul_of_nonneg_left hL1_slot (by positivity)
  have hsub_le :
      (∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)) with s ≤ (tcHarvestSet R u).card,
          ∏ i, Complex.normSq (ψ_id (u i))) - pActual s ≤
        ∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)),
          |(∏ i, pSlot (u i)) - (∏ i, Complex.normSq (ψ_id (u i)))| := by
    dsimp [pActual]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_le_sum fun u _ ↦ ?_).trans
      (Finset.sum_le_univ_sum_of_nonneg fun u ↦ abs_nonneg _)
    rw [abs_sub_comm]
    exact le_abs_self _
  have herr_le : ((2 ^ e : ℕ) : ℝ) * ((5 / 2 : ℝ) * δ) ≤ 1 / (tcScale : ℝ) := by
    have hm_le : ((2 ^ e : ℕ) : ℝ) ≤ 1024 := by
      have hm_nat : 2 ^ e ≤ 2 ^ 10 := Nat.pow_le_pow_right (by positivity) he
      exact_mod_cast (hm_nat.trans (by norm_num : 2 ^ 10 ≤ 1024))
    have hsd_le : 2 * ((sc.steps + 1 : ℕ) : ℝ) * (sc.d : ℝ) ≤ 6024 := by
      have hs_r : (sc.steps : ℝ) ≤ 250 := by exact_mod_cast hst250
      have hd_r : (sc.d : ℝ) ≤ 12 := by exact_mod_cast hd12
      push_cast; nlinarith
    have hsqrt_le : √((R.card : ℝ) / (2 ^ n : ℝ)) ≤ (1 : ℝ) / ((10 : ℝ) ^ 103) := by
      have hinv : √((R.card : ℝ) / (2 ^ n : ℝ)) = (√((2 ^ n : ℝ) / (R.card : ℝ)))⁻¹ := by
        rw [← Real.sqrt_inv, inv_div]
      rw [hinv, one_div]
      exact inv_anti₀ (by positivity) hsqrt_ge
    have hδ_le : δ ≤ 6024 / ((10 : ℝ) ^ 103) := by
      dsimp [δ]
      calc (2 * ((sc.steps + 1 : ℕ) : ℝ) * (sc.d : ℝ)) * √((R.card : ℝ) / (2 ^ n : ℝ))
          ≤ 6024 * ((1 : ℝ) / ((10 : ℝ) ^ 103)) :=
            mul_le_mul hsd_le hsqrt_le (by positivity) (by positivity)
        _ = 6024 / ((10 : ℝ) ^ 103) := by ring
    have hS_val : (tcScale : ℝ) = 1000000000000 := by unfold tcScale; norm_num
    rw [hS_val]
    have hnum : (1024 : ℝ) * ((5 / 2 : ℝ) * (6024 / ((10 : ℝ) ^ 103))) ≤
        1 / 1000000000000 := by norm_num
    calc ((2 ^ e : ℕ) : ℝ) * ((5 / 2 : ℝ) * δ)
        ≤ 1024 * ((5 / 2 : ℝ) * (6024 / ((10 : ℝ) ^ 103))) := by
          exact mul_le_mul hm_le (mul_le_mul_of_nonneg_left hδ_le (by positivity))
            (by positivity) (by positivity)
      _ ≤ 1 / 1000000000000 := hnum
  linarith [hsub_le.trans (hL1_prod.trans herr_le)]

/-!
 ## 5. Stationary `|0⟩`-Reset `.qWhile` Engine, Bellman Stage Loop & `ValidFindAllFamilyTC`
-/

/-- Full `Q`-qubit identity register `0.. Q - 1`. -/
abbrev tcAllQReg (Q : ℕ) : QRegister Q Q :=
  QRegister.whole Q

theorem tcAllQReg_extractIndex {Q : ℕ} (z : Fin (2 ^ Q)) :
    (tcAllQReg Q).extractIndex z = z :=
  QRegister.whole_extractIndex z

theorem tcAllQReg_replaceIndex_zero {Q : ℕ} (z : Fin (2 ^ Q)) :
    (tcAllQReg Q).replaceIndex z 0 = 0 := by
  apply (basisBits Q).injective
  funext w
  change basisBits Q ((tcAllQReg Q).replaceIndex z 0) (tcAllQReg Q w) =
    basisBits Q 0 w
  rw [QRegister.basisBits_replaceIndex_apply]

theorem tcAllQReg_resetKraus_apply {Q : ℕ} (o a b : Fin (2 ^ Q)) :
    (tcAllQReg Q).resetKraus o a b = if a = 0 ∧ b = o then 1 else 0 := by
  have hcol : (tcAllQReg Q).resetKraus o a b =
      (((tcAllQReg Q).resetKraus o) *ᵥ Pi.single b 1) a := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol, ← permutationUnitary_regMaskVec_mul_basisOutcomeProjector, ← Matrix.mulVec_mulVec,
    (tcAllQReg Q).basisOutcomeProjector_mulVec_single, tcAllQReg_extractIndex]
  by_cases hbo : b = o
  · subst hbo
    simp only [↓reduceIte, permutationUnitary_mulVec_single]
    rw [xorBitsPerm_regMaskVec_eq_replaceIndex_zero (tcAllQReg Q) b b (tcAllQReg_extractIndex b),
      tcAllQReg_replaceIndex_zero]
    by_cases ha0 : a = 0 <;> simp [ha0]
  · simp [hbo]

theorem tcAllQReg_resetKraus_mulVec {Q : ℕ} (o : Fin (2 ^ Q)) (ψ : Fin (2 ^ Q) → ℂ) :
    (tcAllQReg Q).resetKraus o *ᵥ ψ = ψ o • Pi.single (0 : Fin (2 ^ Q)) 1 := by
  funext a
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single o]
  · rw [tcAllQReg_resetKraus_apply]
    by_cases ha0 : a = 0 <;> simp [ha0]
  · intro b _ hne
    rw [tcAllQReg_resetKraus_apply]
    simp [hne]
  · intro habs; exact (habs (Finset.mem_univ o)).elim

theorem sum_normSq_unitary_mulVec_zero {d : ℕ} [NeZero d] (U : Unitary d) :
    ∑ o : Fin d, Complex.normSq ((U.1 *ᵥ Pi.single (0 : Fin d) (1 : ℂ)) o) = 1 := by
  rw [sum_normSq_unitary_mulVec, Finset.sum_eq_single 0]
  · simp
  · intro z _ hz; simp [Pi.single_eq_of_ne hz]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim

/-- Classical-store-conditioned `|0⟩` observable on `(σ res).toNat % 2 ^ Q = v`. -/
noncomputable def tcBranchZeroAssertion {Var : Type} (res : Var) (Q v : ℕ) :
    CQAssertion (Store Var) (2 ^ Q) :=
  fun σ ↦ if (σ res).toNat % 2 ^ Q = v then diagObs (· = (0 : Fin (2 ^ Q))) else 0

theorem expect_tcBranchZeroAssertion_eq_sliceState {Var : Type} {Q : ℕ} (res : Var) (v : ℕ)
    (Ξ : CQState (Store Var) (2 ^ Q)) :
    𝔼[Ξ, tcBranchZeroAssertion res Q v] =
      𝔼[sliceState res 0 Q v Ξ, diagAssertion (· = (0 : Fin (2 ^ Q)))] := by
  rw [qcExpectEqTsumStore, qcExpectEqTsumStore]
  refine tsum_congr fun σ ↦ ?_
  change ⟪(if (σ res).toNat % 2 ^ Q = v then diagObs (· = (0 : Fin (2 ^ Q))) else 0).1,
      (Ξ.1 σ).1⟫_ℝ =
    ⟪(diagObs (· = (0 : Fin (2 ^ Q)))).1,
      (if ((σ res).toNat / 2 ^ 0) % 2 ^ Q = v then Ξ.1 σ else 0).1⟫_ℝ
  simp only [pow_zero, Nat.div_one]
  by_cases hv : (σ res).toNat % 2 ^ Q = v <;> simp [hv]

/-- Stationary full-register measure-and-reset `.qWhile` loop starting at clean `|0⟩`. -/
noncomputable def tcResetWhileCircuit {Var : Type} {Q w : ℕ} (res : Var) (keepLoop : ℕ → Bool)
    (cStep : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w :=
  .seq (.measure res (tcAllQReg Q))
    (.qWhile (fun σ ↦ keepLoop (σ res).toNat = true)
      (.seq cStep (resetRegCircuit res (tcAllQReg Q))))

theorem zeroStepCost_tcResetWhileCircuit {Var : Type} {Q w : ℕ} (res : Var) (keepLoop : ℕ → Bool)
    {cStep : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w} (hc : ZeroStepCost cStep) :
    ZeroStepCost (tcResetWhileCircuit res keepLoop cStep) :=
  ⟨trivial, hc, zeroStepCost_resetRegCircuit res (tcAllQReg Q)⟩

theorem wp_measure_tcAllQReg_zero {Var : Type} [DecidableEq Var] {Q : ℕ} (res : Var)
    (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) :
    (wp (QProg.measureRegister res (tcAllQReg Q)) Θ σ).1.mat 0 0 =
      (Θ (Store.subst σ res 0)).1.mat 0 0 := by
  have hproj (o : Fin (2 ^ Q)) :
      (tcAllQReg Q).basisOutcomeProjector o =
        diagProj (fun z ↦ (tcAllQReg Q).extractIndex z = o) :=
    (tcAllQReg Q).basisOutcomeProjector_eq_diagonal o
  rw [wp_measureRegister_coe, HermitianMat.mat_finset_sum,
    Matrix.sum_apply, Finset.sum_eq_single 0]
  · simp only [Nat.cast_zero, Fin.val_zero, HermitianMat.conj_apply_mat,
      QRegister.basisOutcomeProjector_conjTranspose]
    rw [hproj, diagProj_mul_mul_diagProj_apply]
    simp
  · intro o _ ho
    simp only [HermitianMat.conj_apply_mat,
      QRegister.basisOutcomeProjector_conjTranspose]
    rw [hproj, diagProj_mul_mul_diagProj_apply]
    simp [ho.symm]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim

theorem wp_tcStepReset_zero {Var : Type} [DecidableEq Var] {Q w : ℕ} (res : Var)
    (oracle : Unitary (2 ^ w)) (cStep : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
    {U : Unitary (2 ^ Q)} (hU : tcCompileUnitary oracle cStep = some U)
    (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) :
    (wp ((OracleDynamicCircuit.seq cStep (resetRegCircuit res (tcAllQReg Q))).compile
        QProg.qAssign oracle) Θ σ).1.mat 0 0 =
      ∑ o : Fin (2 ^ Q),
        (Complex.normSq ((U.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) o) : ℂ) *
          (Θ (Store.subst σ res ↑o.val)).1.mat 0 0 := by
  set ψ := U.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)
  rw [OracleDynamicCircuit.compile_seq, wp_qSeq, wp_of_tcCompileUnitary_eq_some oracle cStep hU,
    ← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
    wp_resetRegCircuit, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  have hassoc : U.1ᴴ *
        (((tcAllQReg Q).resetKraus o)ᴴ * (Θ (Store.subst σ res ↑o.val)).1.mat *
          (tcAllQReg Q).resetKraus o) * U.1 =
      (((tcAllQReg Q).resetKraus o * U.1)ᴴ * (Θ (Store.subst σ res ↑o.val)).1.mat *
        ((tcAllQReg Q).resetKraus o * U.1)) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hassoc, conjTranspose_mul_mul_apply_single, ← Matrix.mulVec_mulVec]
  change star ((tcAllQReg Q).resetKraus o *ᵥ ψ) ⬝ᵥ
      ((Θ (Store.subst σ res ↑o.val)).1.mat *ᵥ ((tcAllQReg Q).resetKraus o *ᵥ ψ)) = _
  rw [tcAllQReg_resetKraus_mulVec o ψ]
  simp only [Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    Matrix.mulVec_single_one]
  have hdot : star (Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) ⬝ᵥ
      (Θ (Store.subst σ res ↑o.val)).1.mat.col 0 =
      (Θ (Store.subst σ res ↑o.val)).1.mat 0 0 := by
    simp [dotProduct, Pi.single_apply]
  rw [hdot, ← mul_assoc, mul_comm (ψ o) (star (ψ o)), star_mul_self_eq_normSq]

theorem tcToNat_subst_mod {Var : Type} [DecidableEq Var] (σ : Store Var) (res : Var)
    {Q : ℕ} (o : Fin (2 ^ Q)) :
    ((Store.subst σ res (o.val : Expr Var)) res).toNat % 2 ^ Q = o.val := by
  have h : ((Store.subst σ res (o.val : Expr Var)) res).toNat = o.val := by
    simp [Store.subst]
  rw [h, Nat.mod_eq_of_lt o.isLt]

theorem tcResetWhile_transition {Var : Type} [DecidableEq Var] {Q w : ℕ} (res : Var)
    {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1)
    {keepLoop : ℕ → Bool} (hkeep0 : keepLoop 0 = true)
    (cStep : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
    (hzero : ZeroStepCost cStep)
    (hnowhile : ∀ {V : Unitary (2 ^ w)}, (tcCompileUnitary V cStep).isSome = true)
    {U : Unitary (2 ^ Q)} (hU : tcCompileUnitary oracle cStep = some U)
    (hsucc_pos : 0 < ∑ o : Fin (2 ^ Q) with keepLoop o.val = false,
      Complex.normSq ((U.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) o))
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = (0 : Fin (2 ^ Q))) Δ) :
    let prog := (tcResetWhileCircuit res keepLoop cStep).compile QProg.qAssign oracle
    let wt : Fin (2 ^ Q) → ℝ := fun o ↦
      Complex.normSq ((U.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) o)
    let pSucc : ℝ := ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o
    let Δout := (interp prog).toStateFun Δ
    (∀ v : ℕ, (hv : v < 2 ^ Q) →
      SupportedOn (· = (0 : Fin (2 ^ Q))) (sliceState res 0 Q v Δout) ∧
      (sliceState res 0 Q v Δout).trace =
        if keepLoop v = false then (wt ⟨v, hv⟩ / pSucc) * Δ.trace else 0) ∧
    expectedCost (CostModel.ofEmbeddedOracle oracle) prog Δ ≤
      stateMass Δ * ENNReal.ofReal ((tcOracleCount cStep : ℝ) / pSucc) := by
  intro prog wt pSucc Δout
  have hwt_nn : ∀ o : Fin (2 ^ Q), 0 ≤ wt o := fun _ ↦ Complex.normSq_nonneg _
  have hwt_sum : ∑ o : Fin (2 ^ Q), wt o = 1 := sum_normSq_unitary_mulVec_zero U
  set q : ℝ := ∑ o : Fin (2 ^ Q) with keepLoop o.val = true, wt o
  have hpart_wt : q + pSucc = 1 := by
    dsimp [q, pSucc]
    rw [← Finset.sum_union]
    · convert hwt_sum using 2
      ext o
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases keepLoop o.val <;> simp
    · rw [Finset.disjoint_filter]
      intro _ _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
  have hq_nn : 0 ≤ q := Finset.sum_nonneg fun o _ ↦ hwt_nn o
  have hq_lt : q < 1 := by linarith
  have h1mq_eq : 1 - q = pSucc := by linarith
  have h1mq_pos : 0 < 1 - q := by linarith
  set guard : Store Var → Prop := fun σ ↦ keepLoop (σ res).toNat = true
  set cInit : QProg Var (2 ^ Q) := QProg.measureRegister res (tcAllQReg Q)
  set cBody : QProg Var (2 ^ Q) :=
    (OracleDynamicCircuit.seq cStep (resetRegCircuit res (tcAllQReg Q))).compile
      QProg.qAssign oracle
  set cLoop : QProg Var (2 ^ Q) := .qWhile guard cBody
  have hprog_eq : prog = (cInit ;; cLoop) := rfl
  set Δmid := (interp cInit).toStateFun Δ
  have hact_zero (t : ℕ) (σ : Store Var) :
      (whileActiveWP (wp cBody) guard t σ).1.mat 0 0 =
        if guard σ then ((q ^ t : ℝ) : ℂ) else 0 := by
    induction t generalizing σ with
    | zero =>
        rw [whileActiveWP]
        by_cases hg : guard σ <;> simp [hg]
    | succ t ih =>
        rw [whileActiveWP]
        by_cases hg : guard σ
        · simp only [hg, ↓reduceIte]
          rw [wp_tcStepReset_zero res oracle cStep hU _ σ]
          have hterm (o : Fin (2 ^ Q)) :
              (wt o : ℂ) *
                  (whileActiveWP (wp cBody) guard t (Store.subst σ res ↑o.val)).1.mat 0 0 =
                if keepLoop o.val = true then (wt o : ℂ) * ((q ^ t : ℝ) : ℂ) else 0 := by
            rw [ih (Store.subst σ res ↑o.val)]
            have hg_o : guard (Store.subst σ res ↑o.val) ↔ keepLoop o.val = true := by
              simp [guard]
            by_cases hk : keepLoop o.val = true <;> simp [hg_o, hk]
          rw [Finset.sum_congr rfl fun o _ ↦ hterm o, ← Finset.sum_filter,
            ← Finset.sum_mul, ← Complex.ofReal_sum]
          change ((q : ℝ) : ℂ) * ((q ^ t : ℝ) : ℂ) = _
          push_cast [pow_succ']
          ring
        · simp [hg]
  have hrec_zero (o_tgt : Fin (2 ^ Q)) (ho_tgt : keepLoop o_tgt.val = false)
      (t : ℕ) (σ : Store Var) (hg : guard σ) :
      (whileRecWP (wp cBody) guard (t + 1) (tcBranchZeroAssertion res Q o_tgt.val) σ).1.mat 0 0 =
        (((1 - q ^ t) * (wt o_tgt / (1 - q)) : ℝ) : ℂ) := by
    set Ψ := tcBranchZeroAssertion (Var := Var) res Q o_tgt.val
    induction t generalizing σ with
    | zero =>
        have hbot : wp cBody ⊥ = ⊥ := by
          dsimp only [cBody]
          rw [OracleDynamicCircuit.compile_seq, wp_qSeq,
            wp_of_tcCompileUnitary_eq_some oracle cStep hU]
          have hr_bot : wp ((resetRegCircuit res (tcAllQReg Q)).compile
              QProg.qAssign oracle) ⊥ = ⊥ := by
            funext ν; ext1; ext x y
            rw [wp_resetRegCircuit]
            simp
          rw [hr_bot, CQAssertion.qAssign_bot]
        simp [whileRecWP, hg, hbot]
    | succ t ih =>
        rw [whileRecWP]
        simp only [hg, ↓reduceIte]
        rw [wp_tcStepReset_zero res oracle cStep hU _ σ]
        have hsplit : (Finset.univ : Finset (Fin (2 ^ Q))) =
            (Finset.univ.filter fun o : Fin (2 ^ Q) ↦ keepLoop o.val = true) ∪
            (Finset.univ.filter fun o : Fin (2 ^ Q) ↦ keepLoop o.val = false) := by
          ext o
          simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
          cases keepLoop o.val <;> simp
        have hdisj : Disjoint
            (Finset.univ.filter fun o : Fin (2 ^ Q) ↦ keepLoop o.val = true)
            (Finset.univ.filter fun o : Fin (2 ^ Q) ↦ keepLoop o.val = false) := by
          rw [Finset.disjoint_filter]
          intro _ _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
        rw [hsplit, Finset.sum_union hdisj]
        have htrue_sum :
            (∑ o ∈ Finset.univ.filter (fun o : Fin (2 ^ Q) ↦ keepLoop o.val = true),
              (wt o : ℂ) *
                (whileRecWP (wp cBody) guard (t + 1) Ψ (Store.subst σ res ↑o.val)).1.mat 0 0) =
              ((q * ((1 - q ^ t) * (wt o_tgt / (1 - q))) : ℝ) : ℂ) := by
          have hterm : ∀ o ∈ Finset.univ.filter (fun o : Fin (2 ^ Q) ↦ keepLoop o.val = true),
              (wt o : ℂ) *
                  (whileRecWP (wp cBody) guard (t + 1) Ψ (Store.subst σ res ↑o.val)).1.mat 0 0 =
                (wt o : ℂ) * (((1 - q ^ t) * (wt o_tgt / (1 - q)) : ℝ) : ℂ) := by
            intro o ho
            have hk : keepLoop o.val = true := (Finset.mem_filter.1 ho).2
            have hg' : guard (Store.subst σ res ↑o.val) := by simp [guard, hk]
            rw [ih (Store.subst σ res ↑o.val) hg']
          rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Complex.ofReal_sum]
          push_cast [q]; ring
        have hfalse_sum :
            (∑ o ∈ Finset.univ.filter (fun o : Fin (2 ^ Q) ↦ keepLoop o.val = false),
              (wt o : ℂ) *
                (whileRecWP (wp cBody) guard (t + 1) Ψ (Store.subst σ res ↑o.val)).1.mat 0 0) =
              (wt o_tgt : ℂ) := by
          rw [Finset.sum_eq_single o_tgt]
          · have hng : ¬ guard (Store.subst σ res ↑o_tgt.val) := by simp [guard, ho_tgt]
            rw [whileRecWP_succ_apply_of_not _ hng]
            have hmat : (Ψ (Store.subst σ res (o_tgt.val : Expr Var))).1.mat =
                diagProj (· = (0 : Fin (2 ^ Q))) := by
              dsimp only [Ψ, tcBranchZeroAssertion]
              rw [ite_eq_left (tcToNat_subst_mod σ res o_tgt)]
              rfl
            rw [hmat]
            simp [diagProj]
          · intro o ho hne
            have hk : keepLoop o.val = false := (Finset.mem_filter.1 ho).2
            have hng : ¬ guard (Store.subst σ res ↑o.val) := by simp [guard, hk]
            rw [whileRecWP_succ_apply_of_not _ hng]
            have hnev : ((Store.subst σ res (o.val : Expr Var)) res).toNat % 2 ^ Q ≠
                o_tgt.val := by
              rw [tcToNat_subst_mod σ res o]
              exact fun h ↦ hne (Fin.ext h)
            have hmat : (Ψ (Store.subst σ res (o.val : Expr Var))).1.mat = 0 := by
              dsimp only [Ψ, tcBranchZeroAssertion]
              rw [ite_eq_right hnev]
              simp
            rw [hmat, Matrix.zero_apply, mul_zero]
          · intro habs
            exact (habs (Finset.mem_filter.2 ⟨Finset.mem_univ _, ho_tgt⟩)).elim
        rw [htrue_sum, hfalse_sum]
        have hreal : q * ((1 - q ^ t) * (wt o_tgt / (1 - q))) + wt o_tgt =
            (1 - q ^ (t + 1)) * (wt o_tgt / (1 - q)) := by
          have hne : 1 - q ≠ 0 := h1mq_pos.ne'
          field_simp [hne]
          ring
        exact_mod_cast hreal
  have hbranch_ge (o_tgt : Fin (2 ^ Q)) (ho_tgt : keepLoop o_tgt.val = false) :
      (wt o_tgt / (1 - q)) * Δ.trace ≤
        𝔼[sliceState res 0 Q o_tgt.val Δout, diagAssertion (· = (0 : Fin (2 ^ Q)))] := by
    rw [← expect_tcBranchZeroAssertion_eq_sliceState]
    set Ψ := tcBranchZeroAssertion (Var := Var) res Q o_tgt.val
    have hexp_t (t : ℕ) :
        ((1 - q ^ t) * (wt o_tgt / (1 - q))) * Δ.trace ≤ 𝔼[Δout, Ψ] := by
      have hle_wp : whileRecWP (wp cBody) guard (t + 1) Ψ ≤ wp cLoop Ψ :=
        whileRecWP_le_wp_qWhile _ _ (t + 1) _
      have hexp1 : 𝔼[Δmid, whileRecWP (wp cBody) guard (t + 1) Ψ] ≤ 𝔼[Δout, Ψ] := by
        dsimp only [Δout]
        rw [← wp_expectation_eq prog Δ, hprog_eq, wp_qSeq, wp_expectation_eq cInit Δ]
        exact expect_mono le_rfl hle_wp
      rw [← wp_expectation_eq cInit Δ] at hexp1
      have hproj_eq : ∀ σ,
          diagProj (· = (0 : Fin (2 ^ Q))) *
              (wp cInit (whileRecWP (wp cBody) guard (t + 1) Ψ) σ).1.mat *
              diagProj (· = (0 : Fin (2 ^ Q))) =
            (((1 - q ^ t) * (wt o_tgt / (1 - q)) : ℝ) : ℂ) •
              diagProj (· = (0 : Fin (2 ^ Q))) := by
        intro σ
        rw [diagProj_zero_eq_smul_iff, wp_measure_tcAllQReg_zero]
        have hg0 : guard (Store.subst σ res 0) := by simp [guard, hkeep0]
        exact hrec_zero o_tgt ho_tgt t (Store.subst σ res 0) hg0
      rwa [expect_of_supportedOn hΔ hproj_eq] at hexp1
    have htend :
        Filter.Tendsto (fun t : ℕ ↦ ((1 - q ^ t) * (wt o_tgt / (1 - q))) * Δ.trace)
          Filter.atTop (nhds ((wt o_tgt / (1 - q)) * Δ.trace)) := by
      have hp0 := tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt
      have h1 := (((tendsto_const_nhds (x := (1 : ℝ))).sub hp0).mul
        (tendsto_const_nhds (x := wt o_tgt / (1 - q)))).mul
        (tendsto_const_nhds (x := (Δ.trace : ℝ)))
      rw [sub_zero, one_mul] at h1
      exact h1
    exact le_of_tendsto' htend hexp_t
  -- Saturation across all `v ∈ Finset.range (2 ^ Q)`
  let lb : ℕ → ℝ := fun v ↦
    if hv : v < 2 ^ Q then
      if keepLoop v = false then (wt ⟨v, hv⟩ / (1 - q)) * Δ.trace else 0
    else 0
  have hlb_le_exp : ∀ v ∈ Finset.range (2 ^ Q),
      lb v ≤ 𝔼[sliceState res 0 Q v Δout, diagAssertion (· = (0 : Fin (2 ^ Q)))] := by
    intro v hv_mem
    have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem
    dsimp only [lb]
    rw [dite_eq_left hv]
    by_cases hk : keepLoop v = false
    · rw [ite_eq_left hk]
      exact hbranch_ge ⟨v, hv⟩ hk
    · rw [ite_eq_right hk, qcExpectEqTsumStore]
      exact tsum_nonneg fun σ ↦ expect_term_nonneg _ _ σ
  have hexp_le_tr : ∀ v : ℕ,
      𝔼[sliceState res 0 Q v Δout, diagAssertion (· = (0 : Fin (2 ^ Q)))] ≤
        (sliceState res 0 Q v Δout).trace := by
    intro v
    rw [← expect_top (sliceState res 0 Q v Δout)]
    exact expect_mono le_rfl le_top
  have hsum_lb : ∑ v ∈ Finset.range (2 ^ Q), lb v = Δ.trace := by
    have hfin : ∑ v ∈ Finset.range (2 ^ Q), lb v =
        ∑ o : Fin (2 ^ Q),
          (if keepLoop o.val = false then (wt o / (1 - q)) * Δ.trace else 0) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      dsimp only [lb]
      rw [dite_eq_left o.isLt]
    rw [hfin, ← Finset.sum_filter]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    change pSucc * (1 - q)⁻¹ * Δ.trace = Δ.trace
    rw [← h1mq_eq, mul_inv_cancel₀ h1mq_pos.ne', one_mul]
  have hsum_tr_le :
      (∑ v ∈ Finset.range (2 ^ Q), ((sliceState res 0 Q v Δout).trace : ℝ)) ≤
        ∑ v ∈ Finset.range (2 ^ Q), lb v := by
    rw [← NNReal.coe_sum, sum_sliceState_trace, hsum_lb]
    exact NNReal.coe_le_coe.mpr ((interp prog).trace_toStateFun_le Δ)
  have hlb_eq_tr := eq_of_le_of_finset_sum_le (Finset.range (2 ^ Q))
    (fun v hv ↦ (hlb_le_exp v hv).trans (hexp_le_tr v)) hsum_tr_le
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv_mem : v ∈ Finset.range (2 ^ Q) := Finset.mem_range.2 hv
    have heq_v := hlb_eq_tr v hv_mem
    have hexp_eq :
        𝔼[sliceState res 0 Q v Δout, diagAssertion (· = (0 : Fin (2 ^ Q)))] =
          (sliceState res 0 Q v Δout).trace :=
      le_antisymm (hexp_le_tr v) (heq_v ▸ hlb_le_exp v hv_mem)
    refine ⟨supportedOn_of_expect_diagAssertion_eq_trace hexp_eq, ?_⟩
    rw [← heq_v]
    dsimp only [lb]
    rw [dite_eq_left hv, h1mq_eq]
  · let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle oracle
    rw [hprog_eq, expectedCost_qSeq]
    have hc_init : expectedCost model cInit Δ = 0 := by
      simp [cInit, QProg.measureRegister, model]
    rw [hc_init, zero_add]
    have hact_mass (t : ℕ) :
        stateMass (activeIter guard cBody t Δmid) = stateMass Δ * (ENNReal.ofReal q) ^ t := by
      rw [← ofReal_expect_whileActiveWP, ← wp_expectation_eq cInit Δ]
      have hproj_act : ∀ σ,
          diagProj (· = (0 : Fin (2 ^ Q))) *
              (wp cInit (whileActiveWP (wp cBody) guard t) σ).1.mat *
              diagProj (· = (0 : Fin (2 ^ Q))) =
            ((q ^ t : ℝ) : ℂ) • diagProj (· = (0 : Fin (2 ^ Q))) := by
        intro σ
        rw [diagProj_zero_eq_smul_iff, wp_measure_tcAllQReg_zero]
        have hg0 : guard (Store.subst σ res 0) := by simp [guard, hkeep0]
        simpa [hg0] using hact_zero t (Store.subst σ res 0)
      rw [expect_of_supportedOn hΔ hproj_act, mul_comm, stateMass_eq_ofReal_trace,
        ENNReal.ofReal_mul Δ.trace.coe_nonneg, ENNReal.ofReal_pow hq_nn]
    have hexp_iter : expectedIterations guard cBody Δmid =
        stateMass Δ * ENNReal.ofReal ((1 - q)⁻¹) := by
      rw [expectedIterations]
      simp_rw [hact_mass]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ hq_nn, ENNReal.ofReal_inv_of_pos h1mq_pos]
    have hcb_body : CostBound model cBody (tcOracleCount cStep : ℝ≥0) := by
      dsimp only [cBody]
      rw [OracleDynamicCircuit.compile_seq]
      have h1 := costBound_of_zeroStepCost_noWhile horacle hzero hnowhile
      have h2 := costBound_resetRegCircuit horacle res (tcAllQReg Q)
      simpa only [add_zero] using CostBound.seq h1 h2
    calc expectedCost model cLoop Δmid
        ≤ expectedIterations guard cBody Δmid * ((tcOracleCount cStep : ℝ≥0) : ℝ≥0∞) :=
          expectedCost_qWhile_le hcb_body _ Δmid
      _ = stateMass Δ *
            (ENNReal.ofReal ((1 - q)⁻¹) * ENNReal.ofReal (tcOracleCount cStep : ℝ)) := by
          rw [hexp_iter, mul_assoc]
          congr 2
          rw [← ENNReal.ofReal_coe_nnreal]; rfl
      _ = stateMass Δ * ENNReal.ofReal ((tcOracleCount cStep : ℝ) / pSucc) := by
          congr 1
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 h1mq_pos.le), inv_mul_eq_div, h1mq_eq]

theorem tcWriteFinsetLift_transition {Var : Type} [DecidableEq Var] (res : Var)
    {n m k Q : ℕ} (hQ : findAllQubits n m k ≤ Q)
    {S : Finset (Fin (2 ^ n))} (hScard : S.card = k)
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = (0 : Fin (2 ^ Q))) Δ) :
    let prog := (tcLiftCircLow hQ (writeFinsetCircuit res n m k S)).compile
      QProg.qAssign (parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ,
      liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
    expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal 0 := by
  refine tcLiftFromSet_transition res hQ (writeFinsetCircuit res n m k S) (B := 0) ?_ hΔ
  intro Δ₀ hΔ₀
  refine ⟨?_, ?_⟩
  · rw [← wp_expectation_eq _ Δ₀,
      expect_of_supportedOn hΔ₀
        (diagProj_zero_wp_writeFinsetCircuit res hScard (parallelMarkingOracle m S)),
      one_mul]
  · rw [expectedCost_writeFinsetCircuit res n m k S (isRealMatrix_parallelMarkingOracle S) Δ₀,
      ENNReal.ofReal_zero, mul_zero]

/-- Fuel-indexed multi-stage `TensorConveyor` circuit from clean `|0⟩` with known subset
  `T`. -/
noncomputable def tcStagesLoopCircuit {Var : Type} (res : Var) (n m k Q : ℕ)
    (hn12 : 12 ≤ n) (hQ_stage : (n + 1) * m + 12 * m * n ≤ Q)
    (hQ_base : findAllQubits n m k ≤ Q)
    (bSched : ℕ → TensorSchedCert) (useNat stageBid : ℕ → ℕ)
    (tailCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)) :
    ℕ → ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)
  | 0, _, T => tcLiftCircLow hQ_base (writeFinsetCircuit res n m k T)
  | fuel + 1, rem, T =>
      if rem == 0 then
        tcLiftCircLow hQ_base (writeFinsetCircuit res n m k T)
      else if useNat rem == 0 then
        tailCirc rem T
      else
        let sc := bSched (stageBid rem)
        if hd12 : sc.d ≤ 12 then
          let K_blk := tcKBlk n rem sc.tauNum sc.tauDen
          let cAtt := deflateCirc n m T
            (tcResetWhileCircuit res (fun v ↦ !tcHasVerifHit n m sc.d v)
              (tcAttemptUnitaryCircuit n m sc.d Q hn12 hd12 hQ_stage K_blk sc.uFn sc.steps))
          .seq cAtt
            (dispBits res Q 0 fun v ↦
              let H := tcDecodeHarvest n m sc.d v
              if 1 ≤ H.card then
                tcStagesLoopCircuit res n m k Q hn12 hQ_stage hQ_base bSched useNat
                  stageBid tailCirc fuel (rem - H.card) (T ∪ H)
              else
                .skip)
        else
          .skip

theorem tcAttemptOutcome_profile {Var : Type} {n m d Q : ℕ} (hn12 : 12 ≤ n)
    (hd1 : 1 ≤ d) (hd12 : d ≤ 12) (hQ : (n + 1) * m + 12 * m * n ≤ Q)
    (R : Finset (Fin (2 ^ n))) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ)
    {U : Unitary (2 ^ Q)}
    (hU : tcCompileUnitary (parallelMarkingOracle m R)
      (tcAttemptUnitaryCircuit (Var := Var) n m d Q hn12 hd12 hQ K_blk uFn steps) = some U) :
    let wt : Fin (2 ^ Q) → ℝ := fun o ↦
      Complex.normSq ((U.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) o)
    let pSlot : Fin (2 ^ (n * d)) → ℝ := fun z ↦
      Complex.normSq (tcSlotConveyorVec n d hd1 R K_blk uFn steps z)
    (∀ u : Fin m → Fin (2 ^ (n * d)),
      wt (tcPackVerifBasis n m d Q hn12 hd12 hQ R u) = ∏ i : Fin m, pSlot (u i)) ∧
    (∀ o : Fin (2 ^ Q), o ∉ Set.range (tcPackVerifBasis n m d Q hn12 hd12 hQ R) → wt o = 0) ∧
    (∀ P : ℕ → ℝ, P 0 = 0 →
      (∑ o : Fin (2 ^ Q) with (!tcHasVerifHit n m d o.val) = false,
          wt o * P (tcDecodeHarvest n m d o.val).card) =
        ∑ u : Fin m → Fin (2 ^ (n * d)) with 1 ≤ (tcHarvestSet R u).card,
          (∏ i : Fin m, pSlot (u i)) * P (tcHarvestSet R u).card) := by
  intro wt pSlot
  obtain ⟨γ, hγ, hvec⟩ := tcAttemptUnitaryCircuit_mulVec_zero n m d Q hn12 hd1 hd12 hQ R K_blk
    uFn steps hU
  have hnorm_γ : Complex.normSq γ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hγ, one_pow]
  set pack := tcPackVerifBasis n m d Q hn12 hd12 hQ R
  have hinj := tcPackVerifBasis_injective n m d Q hn12 hd12 hQ R
  have hwt_pack : ∀ u : Fin m → Fin (2 ^ (n * d)), wt (pack u) = ∏ i : Fin m, pSlot (u i) := by
    intro u
    dsimp only [wt, pSlot]
    rw [hvec, Pi.smul_apply, Finset.sum_apply, Finset.sum_eq_single u]
    · simp [pack, Complex.normSq_mul, hnorm_γ, map_prod Complex.normSq]
    · intro u' _ hne
      have hne_p : pack u' ≠ pack u := fun h ↦ hne (hinj h)
      simp [Pi.single_eq_of_ne hne_p.symm]
    · intro habs; exact (habs (Finset.mem_univ u)).elim
  have hwt_out : ∀ o : Fin (2 ^ Q), o ∉ Set.range pack → wt o = 0 := by
    intro o ho
    dsimp only [wt]
    rw [hvec, Pi.smul_apply, Finset.sum_apply]
    have hz : (∑ x : Fin m → Fin (2 ^ (n * d)),
        ((∏ i : Fin m, tcSlotConveyorVec n d hd1 R K_blk uFn steps (x i)) •
          Pi.single (pack x) (1 : ℂ)) o) = 0 := by
      refine Finset.sum_eq_zero fun u _ ↦ ?_
      have hne : pack u ≠ o := fun h ↦ ho ⟨u, h⟩
      simp [Pi.single_eq_of_ne hne.symm]
    rw [hz, smul_zero, Complex.normSq_zero]
  refine ⟨hwt_pack, hwt_out, fun P _ ↦ ?_⟩
  have hsub_img :
      (Finset.univ.filter fun o : Fin (2 ^ Q) ↦
          (!tcHasVerifHit n m d o.val) = false ∧ wt o ≠ 0) ⊆
        (Finset.univ.filter fun u : Fin m → Fin (2 ^ (n * d)) ↦
          1 ≤ (tcHarvestSet R u).card).image pack := by
    intro o ho
    rcases Finset.mem_filter.1 ho with ⟨_, hhit, hnz⟩
    have hmem_rng : o ∈ Set.range pack := by
      by_contra hnot; exact hnz (hwt_out o hnot)
    obtain ⟨u, rfl⟩ := hmem_rng
    rw [Finset.mem_image]
    refine ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [Bool.not_eq_false', tcHasVerifHit_eq_harvest_card, tcDecodeHarvest_packVerif,
      decide_eq_true_eq] at hhit
    exact hhit
  have hlhs_eq :
      (∑ o : Fin (2 ^ Q) with (!tcHasVerifHit n m d o.val) = false,
          wt o * P (tcDecodeHarvest n m d o.val).card) =
        ∑ o ∈ (Finset.univ.filter fun u : Fin m → Fin (2 ^ (n * d)) ↦
            1 ≤ (tcHarvestSet R u).card).image pack,
          wt o * P (tcDecodeHarvest n m d o.val).card := by
    trans ∑ o ∈ Finset.univ.filter (fun o : Fin (2 ^ Q) ↦
        (!tcHasVerifHit n m d o.val) = false ∧ wt o ≠ 0),
        wt o * P (tcDecodeHarvest n m d o.val).card
    · symm
      refine Finset.sum_subset (fun o ho ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
          (Finset.mem_filter.1 ho).2.1⟩) fun o ho hnot ↦ ?_
      have hhit := (Finset.mem_filter.1 ho).2
      have hwt0 : wt o = 0 := by
        by_contra hnz
        exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, hhit, hnz⟩)
      rw [hwt0, zero_mul]
    · refine Finset.sum_subset hsub_img fun o ho hnot ↦ ?_
      rcases Finset.mem_image.1 ho with ⟨u, hu, rfl⟩
      have hu1 : 1 ≤ (tcHarvestSet R u).card := (Finset.mem_filter.1 hu).2
      have hhit : (!tcHasVerifHit n m d (pack u).val) = false := by
        rw [Bool.not_eq_false', tcHasVerifHit_eq_harvest_card, tcDecodeHarvest_packVerif,
          decide_eq_true_eq]
        exact hu1
      have hwt0 : wt (pack u) = 0 := by
        by_contra hnz
        exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, hhit, hnz⟩)
      rw [hwt0, zero_mul]
  rw [hlhs_eq, Finset.sum_image (fun u₁ _ u₂ _ h ↦ hinj h)]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [hwt_pack u, tcDecodeHarvest_packVerif]

theorem tcStagesLoop_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {e k Q n : ℕ} (hn700 : 700 ≤ n) (he : e < 11) (hk1024 : k ≤ 1024)
    (hn12 : 12 ≤ n) (hQ_stage : (n + 1) * 2 ^ e + 12 * 2 ^ e * n ≤ Q)
    (hQ_base : findAllQubits n (2 ^ e) k ≤ Q)
    (bSched : ℕ → TensorSchedCert) (bRMin bSMax : ℕ → ℕ)
    (bConvLb bTailLb : ℕ → ℕ → ℤ)
    (vTail16 vTbl attemptUb useNat stageBid : ℕ → ℕ)
    (tailCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 2 ^ e))
    (hstage_certs : ∀ r, 1 ≤ r → r ≤ k → useNat r ≠ 0 →
      let bid := stageBid r
      let sc := bSched bid
      tcCheckSched sc = true ∧
      tcCheckConvPow2 e sc.d sc.wProbLb (bConvLb bid) = true ∧
      tcCheckCouponBucket (bRMin bid) (bSMax bid) (2 ^ e * sc.d)
        (bConvLb bid) (bTailLb bid) = true)
    (hestages : tcCheckEStages 1024 bSched bRMin bSMax bTailLb
      vTail16 vTbl attemptUb useNat stageBid = true)
    {S : Finset (Fin (2 ^ n))} (hScard : S.card = k)
    (htail_corr : ∀ {T : Finset (Fin (2 ^ n))}, T ⊆ S →
      let r := k - T.card
      1 ≤ r → useNat r = 0 →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        𝔼[(interp ((tailCirc r T).compile QProg.qAssign
            (parallelMarkingOracle (2 ^ e) S))).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace) :
    ∀ fuel rem (T : Finset (Fin (2 ^ n))),
      rem ≤ fuel → T ⊆ S → k - T.card = rem →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = (0 : Fin (2 ^ Q))) Δ →
        𝔼[(interp ((tcStagesLoopCircuit res n (2 ^ e) k Q hn12 hQ_stage hQ_base
            bSched useNat stageBid tailCirc fuel rem T).compile QProg.qAssign
              (parallelMarkingOracle (2 ^ e) S))).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace := by
  intro fuel
  induction fuel with
  | zero =>
      intro rem T hrem_fuel hTS hrem_eq Δ hΔ
      have hrem0 : rem = 0 := by omega
      subst hrem0
      have hTS_eq : T = S :=
        Finset.eq_of_subset_of_card_le hTS (by have := Finset.card_le_card hTS; omega)
      subst hTS_eq
      exact (tcWriteFinsetLift_transition res hQ_base hScard hΔ).1
  | succ fuel ih =>
      intro rem T hrem_fuel hTS hrem_eq Δ hΔ
      by_cases hrem0 : rem = 0
      · subst hrem0
        have hTS_eq : T = S :=
          Finset.eq_of_subset_of_card_le hTS (by have := Finset.card_le_card hTS; omega)
        subst hTS_eq
        simp only [tcStagesLoopCircuit, beq_self_eq_true, ↓reduceIte]
        exact (tcWriteFinsetLift_transition res hQ_base hScard hΔ).1
      · have hr1 : 1 ≤ rem := by omega
        have hr_le_k : rem ≤ k := by omega
        have hbeq_rem : (rem == 0) = false := beq_false_of_ne hrem0
        by_cases huse0 : useNat rem = 0
        · have hbeq_use : (useNat rem == 0) = true := beq_iff_eq.2 huse0
          simp only [tcStagesLoopCircuit, hbeq_rem, hbeq_use, Bool.false_eq_true, ↓reduceIte]
          subst hrem_eq
          exact htail_corr hTS hr1 huse0 hΔ
        · have hbeq_use : (useNat rem == 0) = false := beq_false_of_ne huse0
          rcases hstage_certs rem hr1 hr_le_k huse0 with ⟨hsc, hconv, hcoup⟩
          unfold tcCheckEStages at hestages
          simp only [Bool.and_eq_true] at hestages
          have hitem := of_allRange hestages.2 (show rem - 1 < 1024 by omega)
          rw [show rem - 1 + 1 = rem by omega, hbeq_use] at hitem
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
            decide_eq_true_eq] at hitem
          have hrMin_le : bRMin (stageBid rem) ≤ rem := hitem.1.1
          set bid := stageBid rem
          set sc := bSched bid
          set R := S \ T
          have hR_card : R.card = rem := by
            have hadd := Finset.card_sdiff_add_card_eq_card hTS
            dsimp only [R]; omega
          have hr1024 : R.card ≤ 1024 := by omega
          rcases tcCheckSched_sound hn700 (hR_card ▸ hr1) hr1024 hsc with
            ⟨hd2, hd12, _, _, _, _, _, _, _, _⟩
          have hd1 : 1 ≤ sc.d := by omega
          set K_blk := tcKBlk n rem sc.tauNum sc.tauDen
          set cStep := tcAttemptUnitaryCircuit (Var := Var) n (2 ^ e) sc.d Q hn12 hd12 hQ_stage
            K_blk sc.uFn sc.steps
          simp only [tcStagesLoopCircuit, hbeq_rem, hbeq_use, Bool.false_eq_true, ↓reduceIte]
          have hsc_def : bSched (stageBid rem) = sc := rfl
          have hK_def : tcKBlk n rem sc.tauNum sc.tauDen = K_blk := rfl
          have hcStep_def : tcAttemptUnitaryCircuit (Var := Var) n (2 ^ e) sc.d Q hn12 hd12
            hQ_stage K_blk sc.uFn sc.steps = cStep := rfl
          have hR_def : S \ T = R := rfl
          rw [hsc_def, dite_eq_left hd12, hK_def, hcStep_def, OracleDynamicCircuit.compile_seq,
            interp_qSeq, QMonad.Q.toStateFun_bind, interp_deflateCirc n (2 ^ e) hTS, hR_def]
          obtain ⟨U_att, hU_att⟩ := Option.isSome_iff_exists.1
            (tcAttemptUnitaryCircuit_isSome (Var := Var) n (2 ^ e) sc.d Q hn12 hd12 hQ_stage K_blk
              sc.uFn sc.steps (parallelMarkingOracle (2 ^ e) R))
          obtain ⟨_, hwt_out, hwt_sum⟩ :=
            tcAttemptOutcome_profile hn12 hd1 hd12 hQ_stage R K_blk sc.uFn sc.steps hU_att
          have hK_eq : K_blk = tcKBlk n R.card sc.tauNum sc.tauDen := by rw [hR_card]
          rcases tcActualHarvest_tail_lb hn700 (by omega) (hR_card ▸ hr1) hr1024
            (hR_card ▸ hrMin_le) hsc hconv hcoup with ⟨_, _, ht1_ge1, htail_fn⟩
          have hsucc_pos : 0 < ∑ o : Fin (2 ^ Q) with (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false,
              Complex.normSq ((U_att.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) o) := by
            have h1 := hwt_sum (fun s ↦ if s = 0 then 0 else 1) rfl
            have hlhs :
                (∑ o : Fin (2 ^ Q) with (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false,
                    Complex.normSq ((U_att.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) o)) =
                  ∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)) with 1 ≤ (tcHarvestSet R u).card,
                    ∏ i : Fin (2 ^ e),
                      Complex.normSq
                        (tcSlotConveyorVec n sc.d hd1 R K_blk sc.uFn sc.steps (u i)) := by
              calc _ = ∑ o : Fin (2 ^ Q) with (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false,
                        Complex.normSq ((U_att.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) o) *
                          (if (tcDecodeHarvest n (2 ^ e) sc.d o.val).card = 0 then 0 else 1) := by
                      refine Finset.sum_congr rfl fun o ho ↦ ?_
                      have hhit := (Finset.mem_filter.1 ho).2
                      rw [Bool.not_eq_false', tcHasVerifHit_eq_harvest_card,
                        decide_eq_true_eq] at hhit
                      have hne0 : (tcDecodeHarvest n (2 ^ e) sc.d o.val).card ≠ 0 := by omega
                      simp [hne0]
                _ = _ := by
                      rw [h1]
                      refine Finset.sum_congr rfl fun u hu ↦ ?_
                      have hu1 : 1 ≤ (tcHarvestSet R u).card := (Finset.mem_filter.1 hu).2
                      have hne0 : (tcHarvestSet R u).card ≠ 0 := by omega
                      simp [hne0]
            rw [hlhs, hK_eq]
            have hlb1 := (htail_fn 1 le_rfl (by omega)).2
            have hpos : (0 : ℝ) < (bTailLb bid 1 : ℝ) / (tcScale : ℝ) :=
              div_pos (by exact_mod_cast (show (0 : ℤ) < bTailLb bid 1 by omega)) tcScale_pos_real
            exact lt_of_lt_of_le hpos hlb1
          have hkeep0 : (!tcHasVerifHit n (2 ^ e) sc.d 0) = true := by simp [tcHasVerifHit_zero]
          obtain ⟨hslice_att, _⟩ := tcResetWhile_transition res
            (keepLoop := fun v ↦ !tcHasVerifHit n (2 ^ e) sc.d v)
            (isRealMatrix_parallelMarkingOracle R) hkeep0 cStep
            (zeroStepCost_tcAttemptUnitaryCircuit n (2 ^ e) sc.d Q hn12 hd12 hQ_stage K_blk
              sc.uFn sc.steps)
            (fun {V} ↦ tcAttemptUnitaryCircuit_isSome n (2 ^ e) sc.d Q hn12 hd12 hQ_stage K_blk
              sc.uFn sc.steps V)
            hU_att hsucc_pos hΔ
          set Δ_att := (interp ((tcResetWhileCircuit res (fun v ↦ !tcHasVerifHit n (2 ^ e) sc.d v)
            cStep).compile QProg.qAssign (parallelMarkingOracle (2 ^ e) R))).toStateFun Δ
          rw [expect_dispBits]
          have hterm : ∀ v ∈ Finset.range (2 ^ Q),
              𝔼[(interp (((let H := tcDecodeHarvest n (2 ^ e) sc.d v
                  if 1 ≤ H.card then
                    tcStagesLoopCircuit res n (2 ^ e) k Q hn12 hQ_stage hQ_base bSched useNat
                      stageBid tailCirc fuel (rem - H.card) (T ∪ H)
                  else .skip)).compile QProg.qAssign
                  (parallelMarkingOracle (2 ^ e) S))).toStateFun
                (sliceState res 0 Q v Δ_att),
                liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
                (sliceState res 0 Q v Δ_att).trace := by
            intro v hv_mem
            have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem
            obtain ⟨hsupp_v, htr_v⟩ := hslice_att v hv
            by_cases hk : (!tcHasVerifHit n (2 ^ e) sc.d v) = false
            · by_cases hmem_rng : (⟨v, hv⟩ : Fin (2 ^ Q)) ∈
                  Set.range (tcPackVerifBasis n (2 ^ e) sc.d Q hn12 hd12 hQ_stage R)
              · obtain ⟨u, hu_eq⟩ := hmem_rng
                have hv_eq : v = (tcPackVerifBasis n (2 ^ e) sc.d Q hn12 hd12 hQ_stage R u).val :=
                  (congrArg Fin.val hu_eq).symm
                have hH_eq : tcDecodeHarvest n (2 ^ e) sc.d v = tcHarvestSet R u := by
                  rw [hv_eq, tcDecodeHarvest_packVerif]
                have hH_card1 : 1 ≤ (tcDecodeHarvest n (2 ^ e) sc.d v).card := by
                  have hk' := hk
                  rw [Bool.not_eq_false', tcHasVerifHit_eq_harvest_card,
                    decide_eq_true_eq] at hk'
                  exact hk'
                have hH_sub_R : tcDecodeHarvest n (2 ^ e) sc.d v ⊆ R :=
                  hH_eq ▸ tcHarvestSet_subset R u
                have hTU_sub : T ∪ tcDecodeHarvest n (2 ^ e) sc.d v ⊆ S :=
                  Finset.union_subset hTS (hH_sub_R.trans Finset.sdiff_subset)
                have hdisj_TH : Disjoint T (tcDecodeHarvest n (2 ^ e) sc.d v) :=
                  Finset.disjoint_left.2 fun x hxT hxH ↦
                    (Finset.mem_sdiff.1 (hH_sub_R hxH)).2 hxT
                have hH_le_rem : (tcDecodeHarvest n (2 ^ e) sc.d v).card ≤ rem := by
                  rw [← hR_card]; exact Finset.card_le_card hH_sub_R
                have hrem_next : k - (T ∪ tcDecodeHarvest n (2 ^ e) sc.d v).card =
                    rem - (tcDecodeHarvest n (2 ^ e) sc.d v).card := by
                  rw [Finset.card_union_of_disjoint hdisj_TH]; omega
                simp only [hH_card1, ↓reduceIte]
                exact ih (rem - (tcDecodeHarvest n (2 ^ e) sc.d v).card)
                  (T ∪ tcDecodeHarvest n (2 ^ e) sc.d v) (by omega) hTU_sub hrem_next hsupp_v
              · have hwt0 := hwt_out ⟨v, hv⟩ hmem_rng
                have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                  NNReal.coe_eq_zero.mp (by rw [htr_v, ite_eq_left hk, hwt0, zero_div, zero_mul])
                rw [expect_eq_zero_of_trace_eq_zero (nonpos_iff_eq_zero.mp
                  (((interp _).trace_toStateFun_le _).trans_eq htr0)), htr0, NNReal.coe_zero]
            · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                NNReal.coe_eq_zero.mp (by rw [htr_v, ite_eq_right hk])
              rw [expect_eq_zero_of_trace_eq_zero (nonpos_iff_eq_zero.mp
                (((interp _).trace_toStateFun_le _).trans_eq htr0)), htr0, NNReal.coe_zero]
          refine (Finset.sum_congr rfl hterm).trans ?_
          -- Sum of slice traces equals `Δ.trace`
          have hfin : ∑ v ∈ Finset.range (2 ^ Q), ((sliceState res 0 Q v Δ_att).trace : ℝ) =
              ∑ o : Fin (2 ^ Q), ((sliceState res 0 Q o.val Δ_att).trace : ℝ) :=
            (Fin.sum_univ_eq_sum_range
              (fun v ↦ ((sliceState res 0 Q v Δ_att).trace : ℝ)) (2 ^ Q)).symm
          rw [hfin]
          have htr_o : ∀ o : Fin (2 ^ Q),
              (sliceState res 0 Q o.val Δ_att).trace =
                if (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false then
                  (Complex.normSq ((U_att.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) o) /
                    (∑ x : Fin (2 ^ Q) with (!tcHasVerifHit n (2 ^ e) sc.d x.val) = false,
                      Complex.normSq ((U_att.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) x))) *
                    Δ.trace
                else 0 :=
            fun o ↦ (hslice_att o.val o.isLt).2
          rw [Finset.sum_congr rfl fun o _ ↦ htr_o o, ← Finset.sum_filter]
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul, ← Finset.sum_mul, mul_inv_cancel₀ hsucc_pos.ne', one_mul]

theorem tcStagesLoop_costBound {Var : Type} [DecidableEq Var] (res : Var)
    {e k Q n : ℕ} (hn700 : 700 ≤ n) (he : e < 11) (hk1024 : k ≤ 1024)
    (hn12 : 12 ≤ n) (hQ_stage : (n + 1) * 2 ^ e + 12 * 2 ^ e * n ≤ Q)
    (hQ_base : findAllQubits n (2 ^ e) k ≤ Q)
    (bSched : ℕ → TensorSchedCert) (bRMin bSMax : ℕ → ℕ)
    (bConvLb bTailLb : ℕ → ℕ → ℤ)
    (vTail16 vTbl attemptUb useNat stageBid : ℕ → ℕ)
    (tailCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 2 ^ e))
    (hstage_certs : ∀ r, 1 ≤ r → r ≤ k → useNat r ≠ 0 →
      let bid := stageBid r
      let sc := bSched bid
      tcCheckSched sc = true ∧
      tcCheckConvPow2 e sc.d sc.wProbLb (bConvLb bid) = true ∧
      tcCheckCouponBucket (bRMin bid) (bSMax bid) (2 ^ e * sc.d)
        (bConvLb bid) (bTailLb bid) = true)
    (hestages : tcCheckEStages 1024 bSched bRMin bSMax bTailLb
      vTail16 vTbl attemptUb useNat stageBid = true)
    {S : Finset (Fin (2 ^ n))} (hScard : S.card = k)
    (htail_cost : ∀ {T : Finset (Fin (2 ^ n))}, T ⊆ S →
      let r := k - T.card
      1 ≤ r → useNat r = 0 →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) S))
          ((tailCirc r T).compile QProg.qAssign (parallelMarkingOracle (2 ^ e) S)) Δ ≤
          stateMass Δ *
            ENNReal.ofReal (((vTail16 r : ℝ) / 10000000000000000) * √(2 ^ n : ℝ))) :
    ∀ fuel rem (T : Finset (Fin (2 ^ n))),
      rem ≤ fuel → T ⊆ S → k - T.card = rem →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = (0 : Fin (2 ^ Q))) Δ →
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) S))
          ((tcStagesLoopCircuit res n (2 ^ e) k Q hn12 hQ_stage hQ_base
            bSched useNat stageBid tailCirc fuel rem T).compile QProg.qAssign
              (parallelMarkingOracle (2 ^ e) S)) Δ ≤
          stateMass Δ *
            ENNReal.ofReal (((vTbl rem : ℝ) / 10000000000000000) * √(2 ^ n : ℝ)) := by
  unfold tcCheckEStages at hestages
  simp only [Bool.and_eq_true] at hestages
  rcases tcCheckMonotone_sound hestages.1 with ⟨hv0, hv_mono⟩
  set α : ℝ := √(2 ^ n : ℝ) / 10000000000000000
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hrew : ∀ x : ℕ, ((x : ℝ) / 10000000000000000) * √(2 ^ n : ℝ) = (x : ℝ) * α := by
    intro x; dsimp [α]; ring
  intro fuel
  induction fuel with
  | zero =>
      intro rem T hrem_fuel hTS hrem_eq Δ hΔ
      have hrem0 : rem = 0 := by omega
      subst hrem0
      have hTS_eq : T = S :=
        Finset.eq_of_subset_of_card_le hTS (by have := Finset.card_le_card hTS; omega)
      subst hTS_eq
      rw [hv0]
      exact (tcWriteFinsetLift_transition res hQ_base hScard hΔ).2.trans_eq (by simp)
  | succ fuel ih =>
      intro rem T hrem_fuel hTS hrem_eq Δ hΔ
      by_cases hrem0 : rem = 0
      · subst hrem0
        have hTS_eq : T = S :=
          Finset.eq_of_subset_of_card_le hTS (by have := Finset.card_le_card hTS; omega)
        subst hTS_eq
        rw [hv0]
        simp only [tcStagesLoopCircuit, beq_self_eq_true, ↓reduceIte]
        exact (tcWriteFinsetLift_transition res hQ_base hScard hΔ).2.trans_eq (by simp)
      · have hr1 : 1 ≤ rem := by omega
        have hr_le_k : rem ≤ k := by omega
        have hr1024 : rem ≤ 1024 := hr_le_k.trans hk1024
        have hbeq_rem : (rem == 0) = false := beq_false_of_ne hrem0
        have hitem := of_allRange hestages.2 (show rem - 1 < 1024 by omega)
        rw [show rem - 1 + 1 = rem by omega] at hitem
        by_cases huse0 : useNat rem = 0
        · have hbeq_use : (useNat rem == 0) = true := beq_iff_eq.2 huse0
          rw [hbeq_use] at hitem
          simp only [↓reduceIte, tcCheckStageStep, Bool.not_false, decide_eq_true_eq] at hitem
          simp only [tcStagesLoopCircuit, hbeq_rem, hbeq_use, Bool.false_eq_true, ↓reduceIte]
          subst hrem_eq
          refine (htail_cost hTS hr1 huse0 hΔ).trans ?_
          rw [hrew, hrew]
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hitem) hα
        · have hbeq_use : (useNat rem == 0) = false := beq_false_of_ne huse0
          rw [hbeq_use] at hitem
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
            decide_eq_true_eq] at hitem
          rcases hitem with ⟨⟨hrMin_le, hub_chk⟩, hstep_chk⟩
          rcases hstage_certs rem hr1 hr_le_k huse0 with ⟨hsc, hconv, hcoup⟩
          set bid := stageBid rem
          set sc := bSched bid
          set R := S \ T
          have hR_card : R.card = rem := by
            have hadd := Finset.card_sdiff_add_card_eq_card hTS
            dsimp only [R]; omega
          rcases tcCheckSched_sound hn700 hr1 hr1024 hsc with
            ⟨hd2, hd12, _, hst250, _, hden, _, _, hK_le, _⟩
          have hd1 : 1 ≤ sc.d := by omega
          have hub_sound := tcCheckStageCostUb16_sound hn700 hr1 hr1024 hst250 hd12 hden hK_le
            hub_chk
          set K_blk := tcKBlk n rem sc.tauNum sc.tauDen
          set cStep := tcAttemptUnitaryCircuit (Var := Var) n (2 ^ e) sc.d Q hn12 hd12 hQ_stage
            K_blk sc.uFn sc.steps
          set cRaw := tcResetWhileCircuit res (fun v ↦ !tcHasVerifHit n (2 ^ e) sc.d v) cStep
          have hzero_raw : ZeroStepCost cRaw :=
            zeroStepCost_tcResetWhileCircuit res _
              (zeroStepCost_tcAttemptUnitaryCircuit n (2 ^ e) sc.d Q hn12 hd12 hQ_stage K_blk
                sc.uFn sc.steps)
          simp only [tcStagesLoopCircuit, hbeq_rem, hbeq_use, Bool.false_eq_true, ↓reduceIte]
          have hsc_def : bSched (stageBid rem) = sc := rfl
          have hK_def : tcKBlk n rem sc.tauNum sc.tauDen = K_blk := rfl
          have hcStep_def : tcAttemptUnitaryCircuit (Var := Var) n (2 ^ e) sc.d Q hn12 hd12
            hQ_stage K_blk sc.uFn sc.steps = cStep := rfl
          have hcRaw_def : tcResetWhileCircuit res (fun v ↦ !tcHasVerifHit n (2 ^ e) sc.d v)
            cStep = cRaw := rfl
          have hR_def : S \ T = R := rfl
          rw [hsc_def, dite_eq_left hd12, hK_def, hcStep_def, hcRaw_def,
            OracleDynamicCircuit.compile_seq, expectedCost_qSeq,
            interp_deflateCirc n (2 ^ e) hTS, expectedCost_deflateCirc n (2 ^ e) hTS hzero_raw,
            hR_def]
          set model : CostModel (2 ^ Q) :=
            CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) S)
          obtain ⟨U_att, hU_att⟩ := Option.isSome_iff_exists.1
            (tcAttemptUnitaryCircuit_isSome (Var := Var) n (2 ^ e) sc.d Q hn12 hd12 hQ_stage K_blk
              sc.uFn sc.steps (parallelMarkingOracle (2 ^ e) R))
          obtain ⟨_, hwt_out, hwt_sum⟩ :=
            tcAttemptOutcome_profile hn12 hd1 hd12 hQ_stage R K_blk sc.uFn sc.steps hU_att
          have hK_eq : K_blk = tcKBlk n R.card sc.tauNum sc.tauDen := by rw [hR_card]
          set pSlot : Fin (2 ^ (n * sc.d)) → ℝ := fun z ↦
            Complex.normSq (tcSlotConveyorVec n sc.d hd1 R K_blk sc.uFn sc.steps z)
          set pHit : ℕ → ℝ := fun s ↦
            ∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)) with (tcHarvestSet R u).card = s,
              ∏ i : Fin (2 ^ e), pSlot (u i)
          have hpHit_nn : ∀ s, 0 ≤ pHit s := fun s ↦
            Finset.sum_nonneg fun u _ ↦ Finset.prod_nonneg fun i _ ↦ Complex.normSq_nonneg _
          have htail_eq : ∀ j, 1 ≤ j →
              (∑ s ∈ Finset.Icc j rem, pHit s) =
                ∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)) with j ≤ (tcHarvestSet R u).card,
                  ∏ i : Fin (2 ^ e), pSlot (u i) := by
            intro j _
            dsimp [pHit]
            rw [← Finset.sum_biUnion]
            · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
              ext u
              simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ,
                true_and]
              constructor
              · rintro ⟨s, ⟨hjs, _⟩, rfl⟩; exact hjs
              · intro hju
                have hle : (tcHarvestSet R u).card ≤ rem := by
                  rw [← hR_card]; exact Finset.card_le_card (tcHarvestSet_subset R u)
                exact ⟨(tcHarvestSet R u).card, ⟨hju, hle⟩, rfl⟩
            · intro s₁ _ s₂ _ hne
              dsimp only [Function.onFun]
              rw [Finset.disjoint_filter]
              intro _ _ h1 h2; exact hne (h1.symm.trans h2)
          rcases tcActualHarvest_tail_lb hn700 (by omega) (hR_card ▸ hr1) (hR_card ▸ hr1024)
            (hR_card ▸ hrMin_le) hsc hconv hcoup with ⟨hsMax_ge1, _, ht1_ge1, htail_fn⟩
          have htail_pHit : ∀ j, 1 ≤ j → j ≤ bSMax bid →
              0 ≤ bTailLb bid j ∧
              (bTailLb bid j : ℝ) / (tcScale : ℝ) ≤ ∑ s ∈ Finset.Icc j rem, pHit s := by
            intro j hj1 hjMax
            obtain ⟨hnn_j, hlb_j⟩ := htail_fn j hj1 hjMax
            refine ⟨hnn_j, ?_⟩
            rw [htail_eq j hj1]
            simpa only [pSlot, hK_eq] using hlb_j
          set wt : Fin (2 ^ Q) → ℝ := fun o ↦
            Complex.normSq ((U_att.1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) o)
          set pSucc : ℝ := ∑ o : Fin (2 ^ Q) with (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false,
            wt o
          have hpSucc_eq : pSucc = ∑ s ∈ Finset.Icc (1 : ℕ) rem, pHit s := by
            rw [htail_eq 1 le_rfl]
            have h1 := hwt_sum (fun s ↦ if s = 0 then 0 else 1) rfl
            calc pSucc
                = ∑ o : Fin (2 ^ Q) with (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false,
                    wt o * (if (tcDecodeHarvest n (2 ^ e) sc.d o.val).card = 0 then 0 else 1) := by
                  refine Finset.sum_congr rfl fun o ho ↦ ?_
                  have hhit := (Finset.mem_filter.1 ho).2
                  rw [Bool.not_eq_false', tcHasVerifHit_eq_harvest_card, decide_eq_true_eq] at hhit
                  have hne0 : (tcDecodeHarvest n (2 ^ e) sc.d o.val).card ≠ 0 := by omega
                  simp [hne0]
              _ = _ := by
                  rw [h1]
                  refine Finset.sum_congr rfl fun u hu ↦ ?_
                  have hu1 : 1 ≤ (tcHarvestSet R u).card := (Finset.mem_filter.1 hu).2
                  have hne0 : (tcHarvestSet R u).card ≠ 0 := by omega
                  simp [hne0]
          have hpSucc_pos : 0 < pSucc := by
            rw [hpSucc_eq]
            have hlb1 := (htail_pHit 1 le_rfl hsMax_ge1).2
            have hpos : (0 : ℝ) < (bTailLb bid 1 : ℝ) / (tcScale : ℝ) :=
              div_pos (by exact_mod_cast (show (0 : ℤ) < bTailLb bid 1 by omega)) tcScale_pos_real
            exact lt_of_lt_of_le hpos hlb1
          have hkeep0 : (!tcHasVerifHit n (2 ^ e) sc.d 0) = true := by simp [tcHasVerifHit_zero]
          obtain ⟨hslice_att, hcost_att⟩ := tcResetWhile_transition res
            (keepLoop := fun v ↦ !tcHasVerifHit n (2 ^ e) sc.d v)
            (isRealMatrix_parallelMarkingOracle R) hkeep0 cStep
            (zeroStepCost_tcAttemptUnitaryCircuit n (2 ^ e) sc.d Q hn12 hd12 hQ_stage K_blk
              sc.uFn sc.steps)
            (fun {V} ↦ tcAttemptUnitaryCircuit_isSome n (2 ^ e) sc.d Q hn12 hd12 hQ_stage K_blk
              sc.uFn sc.steps V)
            hU_att hpSucc_pos hΔ
          dsimp only [cStep] at hcost_att
          rw [tcOracleCount_attempt] at hcost_att
          set Δ_att := (interp (cRaw.compile QProg.qAssign
            (parallelMarkingOracle (2 ^ e) R))).toStateFun Δ
          -- Bound continuation cost across `dispBits res Q 0`
          set B : ℕ → ℝ := fun j ↦ (vTbl j : ℝ) * α
          have hB_nn : ∀ j, 0 ≤ B j := fun j ↦ mul_nonneg (Nat.cast_nonneg _) hα
          rw [expectedCost_dispBits]
          have hdisp_le :
              ∑ v ∈ Finset.range (2 ^ Q),
                expectedCost model
                  (((let H := tcDecodeHarvest n (2 ^ e) sc.d v
                    if 1 ≤ H.card then
                      tcStagesLoopCircuit res n (2 ^ e) k Q hn12 hQ_stage hQ_base bSched useNat
                        stageBid tailCirc fuel (rem - H.card) (T ∪ H)
                    else .skip)).compile QProg.qAssign (parallelMarkingOracle (2 ^ e) S))
                  (sliceState res 0 Q v Δ_att) ≤
              stateMass Δ *
                ENNReal.ofReal
                  ((∑ s ∈ Finset.Icc (1 : ℕ) rem, pHit s * B (rem - s)) / pSucc) := by
            have hterm_le : ∀ v ∈ Finset.range (2 ^ Q),
                expectedCost model
                  (((let H := tcDecodeHarvest n (2 ^ e) sc.d v
                    if 1 ≤ H.card then
                      tcStagesLoopCircuit res n (2 ^ e) k Q hn12 hQ_stage hQ_base bSched useNat
                        stageBid tailCirc fuel (rem - H.card) (T ∪ H)
                    else .skip)).compile QProg.qAssign (parallelMarkingOracle (2 ^ e) S))
                  (sliceState res 0 Q v Δ_att) ≤
                stateMass Δ * ENNReal.ofReal
                  (if hv : v < 2 ^ Q then
                    if (!tcHasVerifHit n (2 ^ e) sc.d v) = false then
                      (wt ⟨v, hv⟩ * B (rem - (tcDecodeHarvest n (2 ^ e) sc.d v).card)) / pSucc
                    else 0
                  else 0) := by
              intro v hv_mem
              have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem
              obtain ⟨hsupp_v, htr_v⟩ := hslice_att v hv
              rw [dite_eq_left hv]
              by_cases hk : (!tcHasVerifHit n (2 ^ e) sc.d v) = false
              · rw [ite_eq_left hk]
                by_cases hmem_rng : (⟨v, hv⟩ : Fin (2 ^ Q)) ∈
                    Set.range (tcPackVerifBasis n (2 ^ e) sc.d Q hn12 hd12 hQ_stage R)
                · obtain ⟨u, hu_eq⟩ := hmem_rng
                  have hv_eq :
                      v = (tcPackVerifBasis n (2 ^ e) sc.d Q hn12 hd12 hQ_stage R u).val :=
                    (congrArg Fin.val hu_eq).symm
                  have hH_eq : tcDecodeHarvest n (2 ^ e) sc.d v = tcHarvestSet R u := by
                    rw [hv_eq, tcDecodeHarvest_packVerif]
                  have hH_card1 : 1 ≤ (tcDecodeHarvest n (2 ^ e) sc.d v).card := by
                    have hk' := hk
                    rw [Bool.not_eq_false', tcHasVerifHit_eq_harvest_card,
                      decide_eq_true_eq] at hk'
                    exact hk'
                  have hH_sub_R : tcDecodeHarvest n (2 ^ e) sc.d v ⊆ R :=
                    hH_eq ▸ tcHarvestSet_subset R u
                  have hTU_sub : T ∪ tcDecodeHarvest n (2 ^ e) sc.d v ⊆ S :=
                    Finset.union_subset hTS (hH_sub_R.trans Finset.sdiff_subset)
                  have hdisj_TH : Disjoint T (tcDecodeHarvest n (2 ^ e) sc.d v) :=
                    Finset.disjoint_left.2 fun x hxT hxH ↦
                      (Finset.mem_sdiff.1 (hH_sub_R hxH)).2 hxT
                  have hH_le_rem : (tcDecodeHarvest n (2 ^ e) sc.d v).card ≤ rem := by
                    rw [← hR_card]; exact Finset.card_le_card hH_sub_R
                  have hrem_next : k - (T ∪ tcDecodeHarvest n (2 ^ e) sc.d v).card =
                      rem - (tcDecodeHarvest n (2 ^ e) sc.d v).card := by
                    rw [Finset.card_union_of_disjoint hdisj_TH]; omega
                  simp only [hH_card1, ↓reduceIte]
                  have hih := ih (rem - (tcDecodeHarvest n (2 ^ e) sc.d v).card)
                    (T ∪ tcDecodeHarvest n (2 ^ e) sc.d v) (by omega) hTU_sub hrem_next hsupp_v
                  rw [hrew] at hih
                  refine hih.trans (le_of_eq ?_)
                  have hwt_nn_v : 0 ≤ wt ⟨v, hv⟩ := Complex.normSq_nonneg _
                  have hdiv_nn : 0 ≤ wt ⟨v, hv⟩ / pSucc := div_nonneg hwt_nn_v hpSucc_pos.le
                  rw [stateMass_eq_ofReal_trace, htr_v, ite_eq_left hk,
                    ENNReal.ofReal_mul hdiv_nn, mul_comm (ENNReal.ofReal (wt ⟨v, hv⟩ / pSucc)),
                    ← stateMass_eq_ofReal_trace, mul_assoc, ← ENNReal.ofReal_mul hdiv_nn,
                    div_mul_eq_mul_div]
                · have hwt0 := hwt_out ⟨v, hv⟩ hmem_rng
                  have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 := NNReal.coe_eq_zero.mp (by
                    rw [htr_v, ite_eq_left hk]
                    change (wt ⟨v, hv⟩ / pSucc) * Δ.trace = 0
                    rw [hwt0, zero_div, zero_mul])
                  rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0, hwt0, zero_mul,
                    zero_div, ENNReal.ofReal_zero, mul_zero]
              · rw [ite_eq_right hk, ENNReal.ofReal_zero, mul_zero]
                have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 := NNReal.coe_eq_zero.mp (by
                  rw [htr_v, ite_eq_right hk])
                rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0]
            refine (Finset.sum_le_sum hterm_le).trans (le_of_eq ?_)
            rw [← Finset.mul_sum]
            congr 1
            have hsum_real_nn : ∀ v ∈ Finset.range (2 ^ Q),
                0 ≤ (if hv : v < 2 ^ Q then
                  if (!tcHasVerifHit n (2 ^ e) sc.d v) = false then
                    (wt ⟨v, hv⟩ * B (rem - (tcDecodeHarvest n (2 ^ e) sc.d v).card)) / pSucc
                  else 0
                else 0) := by
              intro v _
              split_ifs with hv hk
              · exact div_nonneg (mul_nonneg (Complex.normSq_nonneg _) (hB_nn _)) hpSucc_pos.le
              · exact le_rfl
              · exact le_rfl
            rw [← ENNReal.ofReal_sum_of_nonneg hsum_real_nn]
            congr 1
            rw [← Fin.sum_univ_eq_sum_range]
            have hsimp_o :
                (∑ o : Fin (2 ^ Q),
                  (if hv : o.val < 2 ^ Q then
                    if (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false then
                      (wt ⟨o.val, hv⟩ * B (rem - (tcDecodeHarvest n (2 ^ e) sc.d o.val).card)) /
                        pSucc
                    else 0
                  else 0)) =
                (∑ o : Fin (2 ^ Q) with (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false,
                  wt o * (if (tcDecodeHarvest n (2 ^ e) sc.d o.val).card = 0 then 0
                    else B (rem - (tcDecodeHarvest n (2 ^ e) sc.d o.val).card))) / pSucc := by
              have hlhs :
                  (∑ o : Fin (2 ^ Q),
                    (if hv : o.val < 2 ^ Q then
                      if (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false then
                        (wt ⟨o.val, hv⟩ * B (rem - (tcDecodeHarvest n (2 ^ e) sc.d o.val).card)) /
                          pSucc
                      else 0
                    else 0)) =
                  ∑ o : Fin (2 ^ Q) with (!tcHasVerifHit n (2 ^ e) sc.d o.val) = false,
                    (wt o * B (rem - (tcDecodeHarvest n (2 ^ e) sc.d o.val).card)) / pSucc := by
                rw [Finset.sum_filter]
                refine Finset.sum_congr rfl fun o _ ↦ ?_
                rw [dite_eq_left o.isLt]
              rw [hlhs, Finset.sum_div]
              refine Finset.sum_congr rfl fun o ho ↦ ?_
              congr 1
              have hhit := (Finset.mem_filter.1 ho).2
              rw [Bool.not_eq_false', tcHasVerifHit_eq_harvest_card, decide_eq_true_eq] at hhit
              have hne0 : (tcDecodeHarvest n (2 ^ e) sc.d o.val).card ≠ 0 := by omega
              simp [hne0]
            rw [hsimp_o,
              hwt_sum (fun s ↦ if s = 0 then 0 else B (rem - s)) (by simp)]
            congr 1
            have hu_sum :
                (∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)) with 1 ≤ (tcHarvestSet R u).card,
                  (∏ i : Fin (2 ^ e), pSlot (u i)) *
                    (if (tcHarvestSet R u).card = 0 then 0
                      else B (rem - (tcHarvestSet R u).card))) =
                ∑ s ∈ Finset.Icc (1 : ℕ) rem, pHit s * B (rem - s) := by
              symm
              dsimp [pHit]
              simp_rw [Finset.sum_mul]
              have hinner_eq :
                  (∑ s ∈ Finset.Icc (1 : ℕ) rem,
                    ∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)) with (tcHarvestSet R u).card = s,
                      (∏ i : Fin (2 ^ e), pSlot (u i)) * B (rem - s)) =
                  ∑ s ∈ Finset.Icc (1 : ℕ) rem,
                    ∑ u : Fin (2 ^ e) → Fin (2 ^ (n * sc.d)) with (tcHarvestSet R u).card = s,
                      (∏ i : Fin (2 ^ e), pSlot (u i)) * B (rem - (tcHarvestSet R u).card) :=
                Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun u hu ↦ by
                  rw [(Finset.mem_filter.1 hu).2]
              rw [hinner_eq, ← Finset.sum_biUnion]
              · refine Finset.sum_congr ?_ fun u hu ↦ ?_
                · ext u
                  simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ,
                    true_and]
                  constructor
                  · rintro ⟨s, ⟨h1s, _⟩, rfl⟩; exact h1s
                  · intro h1u
                    have hle : (tcHarvestSet R u).card ≤ rem := by
                      rw [← hR_card]; exact Finset.card_le_card (tcHarvestSet_subset R u)
                    exact ⟨(tcHarvestSet R u).card, ⟨h1u, hle⟩, rfl⟩
                · have hu1 : 1 ≤ (tcHarvestSet R u).card := (Finset.mem_filter.1 hu).2
                  have hne0 : (tcHarvestSet R u).card ≠ 0 := by omega
                  simp [hne0]
              · intro s₁ _ s₂ _ hne
                dsimp only [Function.onFun]
                rw [Finset.disjoint_filter]
                intro _ _ h1 h2; exact hne (h1.symm.trans h2)
            exact hu_sum
          -- Combine attempt + continuation and invoke `tcCheckStageStep_sound`
          set C_val : ℝ :=
            (((sc.steps * K_blk + sc.d : ℕ) : ℝ) +
              ∑ s ∈ Finset.Icc (1 : ℕ) rem, pHit s * B (rem - s)) / pSucc
          have htot_le :
              expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) R))
                (cRaw.compile QProg.qAssign (parallelMarkingOracle (2 ^ e) R)) Δ +
              ∑ v ∈ Finset.range (2 ^ Q),
                expectedCost model
                  (((let H := tcDecodeHarvest n (2 ^ e) sc.d v
                    if 1 ≤ H.card then
                      tcStagesLoopCircuit res n (2 ^ e) k Q hn12 hQ_stage hQ_base bSched useNat
                        stageBid tailCirc fuel (rem - H.card) (T ∪ H)
                    else .skip)).compile QProg.qAssign (parallelMarkingOracle (2 ^ e) S))
                  (sliceState res 0 Q v Δ_att) ≤
              stateMass Δ * ENNReal.ofReal C_val := by
            refine (add_le_add hcost_att hdisp_le).trans (le_of_eq ?_)
            rw [← mul_add, ← ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg _) hpSucc_pos.le)
              (div_nonneg
                (Finset.sum_nonneg fun s _ ↦ mul_nonneg (hpHit_nn s) (hB_nn _))
                hpSucc_pos.le),
              ← add_div]
          refine htot_le.trans ?_
          rw [hrew]
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
          set V : ℕ → ℝ := fun j ↦ if j = rem then C_val else B j
          have hV_rem : V rem = C_val := by simp [V]
          rw [← hV_rem]
          exact tcCheckStageStep_sound (sMax := bSMax bid) (attemptCostUb16 := attemptUb rem)
            (tailLb := bTailLb bid) (useTc := true) (vTail16 := vTail16) (pHit := pHit)
            (attemptCost := ((sc.steps * K_blk + sc.d : ℕ) : ℝ))
            hα
            (fun i hi ↦ hv_mono i (i + 1) (by omega) (by omega))
            (fun j hj ↦ by simp [V, hj.ne, B])
            (fun h ↦ Bool.noConfusion h)
            (fun _ s _ ↦ hpHit_nn s)
            (fun _ ↦ htail_pHit)
            (fun _ ↦ by
              have hcast : ((sc.steps * K_blk + sc.d : ℕ) : ℝ) =
                  (sc.steps : ℝ) * (K_blk : ℝ) + (sc.d : ℝ) := by push_cast; ring
              rw [hcast]
              exact hub_sound.trans_eq (hrew (attemptUb rem)))
            (fun _ ↦ by
              have hbell_eq :
                  (∑ s ∈ Finset.Icc (1 : ℕ) rem, pHit s) * V rem =
                    ((sc.steps * K_blk + sc.d : ℕ) : ℝ) +
                      ∑ s ∈ Finset.Icc (1 : ℕ) rem, pHit s * V (rem - s) := by
                rw [hV_rem]
                have hrhs_eq :
                    ∑ s ∈ Finset.Icc (1 : ℕ) rem, pHit s * V (rem - s) =
                      ∑ s ∈ Finset.Icc (1 : ℕ) rem, pHit s * B (rem - s) := by
                  refine Finset.sum_congr rfl fun s hs ↦ ?_
                  have hs1 : 1 ≤ s := (Finset.mem_Icc.1 hs).1
                  have hne : rem - s ≠ rem := by omega
                  simp [V, hne]
                rw [hrhs_eq, ← hpSucc_eq]
                dsimp [C_val]
                exact mul_div_cancel₀ _ hpSucc_pos.ne'
              exact le_of_eq hbell_eq)
            hstep_chk

/-- Generic ambient-`Q` `TensorConveyor` cell circuit at `(n, m, k, Q)` handing off to
  `tailCirc`
  whenever `useNat r == 0` (`700 ≤ n`, clean `|0⟩` precondition on `Q` qubits). -/
noncomputable def tcCellCircuitAt {Var : Type} (res : Var) (n m k Q : ℕ)
    (bSched : ℕ → TensorSchedCert) (useNat stageBid : ℕ → ℕ)
    (tailCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  if h : 700 ≤ n ∧ (n + 1) * m + 12 * m * n ≤ Q ∧ findAllQubits n m k ≤ Q then
    tcStagesLoopCircuit res n m k Q (by omega) h.2.1 h.2.2 bSched useNat stageBid
      tailCirc k k ∅
  else if hQ0 : findAllQubits n m k ≤ Q then
    tcLiftCircLow hQ0 (findAllCircuit res (fun _ _ _ ↦ 0) n m k)
  else
    .skip

theorem tcCellAt_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {e kIdx n Q : ℕ} (_hn : 1 ≤ n) (he : e < 11) (hkIdx : kIdx < 11)
    (hkN : 2 ^ kIdx ≤ 2 ^ n) (hQ : tcMinQubits n (2 ^ e) (2 ^ kIdx) ≤ Q)
    (bSched : ℕ → TensorSchedCert) (bRMin bSMax : ℕ → ℕ)
    (bConvLb bTailLb : ℕ → ℕ → ℤ)
    (vTail16 vTbl attemptUb useNat stageBid : ℕ → ℕ)
    (tailCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 2 ^ e))
    (hstage_certs : ∀ r, 1 ≤ r → r ≤ 2 ^ kIdx → useNat r ≠ 0 →
      let bid := stageBid r
      let sc := bSched bid
      tcCheckSched sc = true ∧
      tcCheckConvPow2 e sc.d sc.wProbLb (bConvLb bid) = true ∧
      tcCheckCouponBucket (bRMin bid) (bSMax bid) (2 ^ e * sc.d)
        (bConvLb bid) (bTailLb bid) = true)
    (hestages : tcCheckEStages 1024 bSched bRMin bSMax bTailLb
      vTail16 vTbl attemptUb useNat stageBid = true)
    (htail_corr : 700 ≤ n → ∀ {S T : Finset (Fin (2 ^ n))},
      S.card = 2 ^ kIdx → T ⊆ S →
      let r := 2 ^ kIdx - T.card
      1 ≤ r → useNat r = 0 →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        𝔼[(interp ((tailCirc r T).compile QProg.qAssign
            (parallelMarkingOracle (2 ^ e) S))).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n (2 ^ kIdx) (τ res) = S)] = Δ.trace)
    {S : Finset (Fin (2 ^ n))} (hScard : S.card = 2 ^ kIdx) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Q)) ⦄
    (QProg.qSet ;;
      (tcCellCircuitAt res n (2 ^ e) (2 ^ kIdx) Q bSched useNat stageBid tailCirc).compile
        QProg.qAssign (parallelMarkingOracle (2 ^ e) S))
    ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n (2 ^ kIdx) (σ res) = S) ⦄ := by
  intro Δ
  have hQ_base : findAllQubits n (2 ^ e) (2 ^ kIdx) ≤ Q :=
    (findAllQubits_le_tcMinQubits _ _ _).trans hQ
  have hQ_stage : (n + 1) * 2 ^ e + 12 * 2 ^ e * n ≤ Q := by
    have h := (tcStageBound_le_tcMinQubits n (2 ^ e) (2 ^ kIdx)).trans hQ; omega
  have hsupp_qSet : SupportedOn (· = (0 : Fin (2 ^ Q))) Δ.qSet := by
    refine supportedOn_qSet ?_ Δ; rfl
  rw [expect_top, interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet]
  by_cases hn700 : 700 ≤ n
  · have hcond : 700 ≤ n ∧ (n + 1) * 2 ^ e + 12 * 2 ^ e * n ≤ Q ∧
        findAllQubits n (2 ^ e) (2 ^ kIdx) ≤ Q := ⟨hn700, hQ_stage, hQ_base⟩
    have hk1024 : 2 ^ kIdx ≤ 1024 := by
      calc 2 ^ kIdx ≤ 2 ^ 10 := Nat.pow_le_pow_right (by positivity) (by omega)
        _ = 1024 := by norm_num
    unfold tcCellCircuitAt
    rw [dite_eq_left hcond]
    exact ((tcStagesLoop_correctness res hn700 he hk1024 (by omega) hQ_stage hQ_base
      bSched bRMin bSMax bConvLb bTailLb vTail16 vTbl attemptUb useNat stageBid tailCirc
      hstage_certs hestages hScard
      (fun {T} hTS hr1 huse0 {Δ} hΔ ↦ htail_corr hn700 hScard hTS hr1 huse0 hΔ)
      (2 ^ kIdx) (2 ^ kIdx) ∅ le_rfl (Finset.empty_subset S) (by simp) hsupp_qSet).trans
      (congrArg NNReal.toReal (CQState.trace_qSet Δ))).symm.le
  · have hcond : ¬ (700 ≤ n ∧ (n + 1) * 2 ^ e + 12 * 2 ^ e * n ≤ Q ∧
        findAllQubits n (2 ^ e) (2 ^ kIdx) ≤ Q) := fun h ↦ hn700 h.1
    unfold tcCellCircuitAt
    rw [dite_eq_right hcond, dite_eq_left hQ_base]
    let Δ₀ := tcQSetLow (findAllQubits n (2 ^ e) (2 ^ kIdx)) Δ.qSet
    have hpad : tcPadStateLow (tcLowBlockReg hQ_base) Δ₀ = Δ.qSet :=
      tcPadStateLow_tcQSetLow_of_supportedOn_zero _ hsupp_qSet
    have htr₀ : Δ₀.trace = Δ.trace := by
      rw [← CQState.trace_qSet Δ, ← hpad, trace_tcPadStateLow]
    have hm1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have hcorr₀ := findAllProgram_correctness res (fun _ _ _ ↦ 0) hm1 hScard hkN
      (fun r hr1 hrk ↦ p_succ_set_zero_pos hr1 (hrk.trans hkN)) Δ₀
    rw [expect_top, interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet,
      qSet_tcQSetLow, htr₀] at hcorr₀
    rw [← hpad, interp_tcLiftCircLow, expect_tcPadStateLow_liftPureProp]
    exact hcorr₀

theorem tcCellAt_costBound {Var : Type} [DecidableEq Var] (res : Var)
    {e kIdx n Q relNum relDen : ℕ} (hn700 : 700 ≤ n) (hkN : 2 ^ kIdx ≤ 2 ^ n)
    (hQ : tcMinQubits n (2 ^ e) (2 ^ kIdx) ≤ Q)
    (bSched : ℕ → TensorSchedCert) (bRMin bSMax : ℕ → ℕ)
    (bConvLb bTailLb : ℕ → ℕ → ℤ)
    (vTail16 vTbl attemptUb useNat stageBid : ℕ → ℕ)
    (tailCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 2 ^ e))
    (hstage_certs : ∀ r, 1 ≤ r → r ≤ 2 ^ kIdx → useNat r ≠ 0 →
      let bid := stageBid r
      let sc := bSched bid
      tcCheckSched sc = true ∧
      tcCheckConvPow2 e sc.d sc.wProbLb (bConvLb bid) = true ∧
      tcCheckCouponBucket (bRMin bid) (bSMax bid) (2 ^ e * sc.d)
        (bConvLb bid) (bTailLb bid) = true)
    (hestages : tcCheckEStages 1024 bSched bRMin bSMax bTailLb
      vTail16 vTbl attemptUb useNat stageBid = true)
    (hcell : tcCheckRelCostCell e kIdx vTbl relNum relDen = true)
    (htail : ∀ {S T : Finset (Fin (2 ^ n))},
      S.card = 2 ^ kIdx → T ⊆ S →
      let r := 2 ^ kIdx - T.card
      1 ≤ r → useNat r = 0 →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        let prog := (tailCirc r T).compile QProg.qAssign (parallelMarkingOracle (2 ^ e) S)
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n (2 ^ kIdx) (τ res) = S)] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) S)) prog Δ ≤
          stateMass Δ *
            ENNReal.ofReal (((vTail16 r : ℝ) / 10000000000000000) * √(2 ^ n : ℝ))) :
    ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
      (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard (2 ^ kIdx),
        CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) S))
          (QProg.qSet ;;
            (tcCellCircuitAt (Var := Var) res n (2 ^ e) (2 ^ kIdx) Q bSched useNat stageBid
              tailCirc).compile QProg.qAssign (parallelMarkingOracle (2 ^ e) S))
          (q S)) ∧
      (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard (2 ^ kIdx), (q S : ℝ)) /
          ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard (2 ^ kIdx)).card ≤
        (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) *
          ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) *
            √((2 ^ n : ℝ) / (2 ^ e : ℕ))) := by
  have hcell_copy := hcell
  unfold tcCheckRelCostCell at hcell_copy
  simp only [decide_eq_true_eq] at hcell_copy
  rcases hcell_copy with ⟨he, hkIdx, _, _⟩
  have hk1024 : 2 ^ kIdx ≤ 1024 := by
    calc 2 ^ kIdx ≤ 2 ^ 10 := Nat.pow_le_pow_right (by positivity) (by omega)
      _ = 1024 := by norm_num
  have hQ_base : findAllQubits n (2 ^ e) (2 ^ kIdx) ≤ Q :=
    (findAllQubits_le_tcMinQubits _ _ _).trans hQ
  have hQ_stage : (n + 1) * 2 ^ e + 12 * 2 ^ e * n ≤ Q := by
    have h := (tcStageBound_le_tcMinQubits n (2 ^ e) (2 ^ kIdx)).trans hQ; omega
  have hcond : 700 ≤ n ∧ (n + 1) * 2 ^ e + 12 * 2 ^ e * n ≤ Q ∧
      findAllQubits n (2 ^ e) (2 ^ kIdx) ≤ Q := ⟨hn700, hQ_stage, hQ_base⟩
  set cVal : ℝ := ((vTbl (2 ^ kIdx) : ℝ) / 10000000000000000) * √(2 ^ n : ℝ)
  have hcVal_nn : 0 ≤ cVal := by dsimp [cVal]; positivity
  let cNN : ℝ≥0 := ⟨cVal, hcVal_nn⟩
  refine ⟨fun _ ↦ cNN, ?_, ?_⟩
  · intro S hS Δ
    have hScard : S.card = 2 ^ kIdx := (Finset.mem_powersetCard.1 hS).2
    let model : CostModel (2 ^ Q) :=
      CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) S)
    rw [expectedCost_qSeq, expectedCost_qSet, CostModel.ofEmbeddedOracle_resetCost,
      Nat.cast_zero, mul_zero, zero_add, interp_qSet, QMonad.Q.toStateFun_qSet]
    have hsupp_qSet : SupportedOn (· = (0 : Fin (2 ^ Q))) Δ.qSet := by
      refine supportedOn_qSet ?_ Δ; rfl
    have hmass_qSet : stateMass Δ.qSet = stateMass Δ := by
      rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, CQState.trace_qSet]
    unfold tcCellCircuitAt
    rw [dite_eq_left hcond]
    have hcb := tcStagesLoop_costBound res hn700 he hk1024 (by omega) hQ_stage hQ_base
      bSched bRMin bSMax bConvLb bTailLb vTail16 vTbl attemptUb useNat stageBid tailCirc
      hstage_certs hestages hScard
      (fun {T} hTS hr1 huse0 {Δ} hΔ ↦ (htail hScard hTS hr1 huse0 hΔ).2)
      (2 ^ kIdx) (2 ^ kIdx) ∅ le_rfl (Finset.empty_subset S) (by simp) hsupp_qSet
    rw [hmass_qSet] at hcb
    dsimp only
    have hcNN : (cNN : ℝ≥0∞) = ENNReal.ofReal cVal := ENNReal.ofReal_coe_nnreal.symm
    rw [hcNN]
    exact hcb
  · set Ps := (Finset.univ : Finset (Fin (2 ^ n))).powersetCard (2 ^ kIdx)
    have hcard_pos : 0 < Ps.card := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact Nat.choose_pos hkN
    have havg : (∑ _ ∈ Ps, (cNN : ℝ)) / (Ps.card : ℝ) = cVal := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ (Nat.cast_pos.2 hcard_pos).ne']
      rfl
    rw [havg]
    have hsound := tcCheckRelCostCell_sound (n := n) hcell
    have hrat : (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) = (relNum : ℝ) / (relDen : ℝ) := by
      push_cast; rfl
    have hm_cast : ((2 ^ e : ℕ) : ℝ) = (2 : ℝ) ^ e := by push_cast; rfl
    rw [hrat, hm_cast]
    exact hsound

/-- Standalone `tensorConveyorQubits n m k` specialization of `tcCellCircuitAt`. -/
noncomputable abbrev tcCellCircuit {Var : Type} (res : Var) (n m k : ℕ)
    (bSched : ℕ → TensorSchedCert) (useNat stageBid : ℕ → ℕ)
    (tailCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ tensorConveyorQubits n m k)) Var
        (tensorConveyorQubits n m k) ((n + 1) * m)) :
    OracleDynamicCircuit (Unitary (2 ^ tensorConveyorQubits n m k)) Var
      (tensorConveyorQubits n m k) ((n + 1) * m) :=
  tcCellCircuitAt res n m k (tensorConveyorQubits n m k) bSched useNat stageBid tailCirc

theorem tcCell_correctness_and_costBound_of_tail {Var : Type} [DecidableEq Var] (res : Var)
    {e kIdx n relNum relDen : ℕ} (he : e < 11) (hkIdx : kIdx < 11)
    (bSched : ℕ → TensorSchedCert) (bRMin bSMax : ℕ → ℕ)
    (bConvLb bTailLb : ℕ → ℕ → ℤ)
    (vTail16 vTbl attemptUb useNat stageBid : ℕ → ℕ)
    (tailCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ tensorConveyorQubits n (2 ^ e) (2 ^ kIdx))) Var
        (tensorConveyorQubits n (2 ^ e) (2 ^ kIdx)) ((n + 1) * 2 ^ e))
    (hstage_certs : ∀ r, 1 ≤ r → r ≤ 2 ^ kIdx → useNat r ≠ 0 →
      let bid := stageBid r
      let sc := bSched bid
      tcCheckSched sc = true ∧
      tcCheckConvPow2 e sc.d sc.wProbLb (bConvLb bid) = true ∧
      tcCheckCouponBucket (bRMin bid) (bSMax bid) (2 ^ e * sc.d)
        (bConvLb bid) (bTailLb bid) = true)
    (hestages : tcCheckEStages 1024 bSched bRMin bSMax bTailLb
      vTail16 vTbl attemptUb useNat stageBid = true)
    (hcell : tcCheckRelCostCell e kIdx vTbl relNum relDen = true)
    (htail : 700 ≤ n → ∀ {S T : Finset (Fin (2 ^ n))},
      S.card = 2 ^ kIdx → T ⊆ S →
      let r := 2 ^ kIdx - T.card
      1 ≤ r → useNat r = 0 →
      ∀ {Δ : CQState (Store Var) (2 ^ tensorConveyorQubits n (2 ^ e) (2 ^ kIdx))},
        SupportedOn (· = 0) Δ →
        let prog := (tailCirc r T).compile QProg.qAssign (parallelMarkingOracle (2 ^ e) S)
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n (2 ^ kIdx) (τ res) = S)] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) S)) prog Δ ≤
          stateMass Δ *
            ENNReal.ofReal (((vTail16 r : ℝ) / 10000000000000000) * √(2 ^ n : ℝ))) :
    (1 ≤ n → 2 ^ kIdx ≤ 2 ^ n →
      ∀ {S : Finset (Fin (2 ^ n))}, S.card = 2 ^ kIdx →
        ⦃ (⊤ : CQAssertion (Store Var) (2 ^ tensorConveyorQubits n (2 ^ e) (2 ^ kIdx))) ⦄
        (QProg.qSet ;;
          (tcCellCircuit res n (2 ^ e) (2 ^ kIdx) bSched useNat stageBid tailCirc).compile
            QProg.qAssign (parallelMarkingOracle (2 ^ e) S))
        ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n (2 ^ kIdx) (σ res) = S) ⦄) ∧
    (700 ≤ n → 2 ^ kIdx ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard (2 ^ kIdx),
          CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle (2 ^ e) S))
            (QProg.qSet ;;
              (tcCellCircuit (Var := Var) res n (2 ^ e) (2 ^ kIdx) bSched useNat stageBid
                tailCirc).compile QProg.qAssign (parallelMarkingOracle (2 ^ e) S))
            (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard (2 ^ kIdx), (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard (2 ^ kIdx)).card ≤
          (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) *
              √((2 ^ n : ℝ) / (2 ^ e : ℕ)))) := by
  have hQ := tcMinQubits_le_tensorConveyorQubits n (2 ^ e) (2 ^ kIdx)
  refine ⟨fun hn hkN {S} hScard ↦
    tcCellAt_correctness res hn he hkIdx hkN hQ bSched bRMin bSMax bConvLb bTailLb
      vTail16 vTbl attemptUb useNat stageBid tailCirc hstage_certs hestages
      (fun hn700 {S T} hSc hTS hr1 huse0 {Δ} hΔ ↦ (htail hn700 hSc hTS hr1 huse0 hΔ).1) hScard,
    fun hn700 hkN ↦
      tcCellAt_costBound res hn700 hkN hQ bSched bRMin bSMax bConvLb bTailLb
        vTail16 vTbl attemptUb useNat stageBid tailCirc hstage_certs hestages hcell
        (htail hn700)⟩

/-- Variable-width family specification (`res p qFn circuit`, matching router conventions). -/
structure ValidFindAllFamilyTC {Var : Type} [DecidableEq Var] (res : Var)
    (p : FindAllCostProfile) (qFn : ℕ → ℕ → ℕ → ℕ)
    (circuit : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ qFn n m k)) Var (qFn n m k) ((n + 1) * m)) : Prop where
  correctness :
    ∀ {n m k : ℕ} {S : Finset (Fin (2 ^ n))},
      1 ≤ n → isGridCell m k = true → p.validCell m k = true → k ≤ 2 ^ n →
        S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k →
        ⦃ (⊤ : CQAssertion (Store Var) (2 ^ qFn n m k)) ⦄
        (QProg.qSet ;; (circuit n m k).compile QProg.qAssign (parallelMarkingOracle m S))
        ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S) ⦄
  costBound_uniform :
    ∀ {m k : ℕ}, isGridCell m k = true → p.validCell m k = true →
      ∀ n ≥ p.n0 m k, k ≤ 2 ^ n →
        ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
          (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
            CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
              (QProg.qSet ;; (circuit n m k).compile QProg.qAssign
                (parallelMarkingOracle m S))
              (q S)) ∧
          (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
              ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
            ((p.relCost m k : ℚ≥0) : ℝ) *
              ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m))

/-- Pointwise clean-ancilla lifting of a circuit family from `q₁` to `q₂` (`q₁ ≤ q₂`). -/
noncomputable abbrev ValidFindAllFamilyTC.liftCirc {Var : Type}
    {q₁ : ℕ → ℕ → ℕ → ℕ}
    (c : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ q₁ n m k)) Var (q₁ n m k) ((n + 1) * m))
    (q₂ : ℕ → ℕ → ℕ → ℕ) (hq : ∀ n m k, q₁ n m k ≤ q₂ n m k) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ q₂ n m k)) Var (q₂ n m k) ((n + 1) * m) :=
  tcLiftCircLow (hq n m k) (c n m k)

theorem ValidFindAllFamilyTC.ofStandard {Var : Type} [DecidableEq Var] {res : Var}
    {p : FindAllCostProfile}
    {c : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m)}
    (h : ValidFindAllFamily res p c) :
    ValidFindAllFamilyTC res p findAllQubits c :=
  ⟨h.correctness, h.costBound_uniform⟩

theorem ValidFindAllFamilyTC.toStandard {Var : Type} [DecidableEq Var] {res : Var}
    {p : FindAllCostProfile}
    {c : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m)}
    (h : ValidFindAllFamilyTC res p findAllQubits c) :
    ValidFindAllFamily res p c :=
  ⟨h.correctness, h.costBound_uniform⟩

theorem ValidFindAllFamilyTC.liftToQubits {Var : Type} [DecidableEq Var] {res : Var}
    {p : FindAllCostProfile} {q₁ : ℕ → ℕ → ℕ → ℕ}
    {c : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ q₁ n m k)) Var (q₁ n m k) ((n + 1) * m)}
    (h : ValidFindAllFamilyTC res p q₁ c)
    (q₂ : ℕ → ℕ → ℕ → ℕ) (hq : ∀ n m k, q₁ n m k ≤ q₂ n m k) :
    ValidFindAllFamilyTC res p q₂ (ValidFindAllFamilyTC.liftCirc c q₂ hq) where
  correctness {n m k S} hn hmk hvalid hkN hS Δ := by
    let hQ := hq n m k
    let Δ₀ := tcQSetLow (q₁ n m k) Δ.qSet
    have hsupp : SupportedOn (· = (0 : Fin (2 ^ q₂ n m k))) Δ.qSet := by
      refine supportedOn_qSet ?_ Δ; rfl
    have hpad : tcPadStateLow (tcLowBlockReg hQ) Δ₀ = Δ.qSet :=
      tcPadStateLow_tcQSetLow_of_supportedOn_zero _ hsupp
    have htr₀ : Δ₀.trace = Δ.trace := by
      rw [← CQState.trace_qSet Δ, ← hpad, trace_tcPadStateLow]
    have hc := h.correctness hn hmk hvalid hkN hS Δ₀
    rw [expect_top, interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet,
      qSet_tcQSetLow, htr₀] at hc
    rw [expect_top, interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet,
      ← hpad, interp_tcLiftCircLow, expect_tcPadStateLow_liftPureProp]
    exact hc
  costBound_uniform {m k} hmk hvalid n hn hkN := by
    obtain ⟨q, hq_cb, hq_avg⟩ := h.costBound_uniform hmk hvalid n hn hkN
    refine ⟨q, fun S hS Δ ↦ ?_, hq_avg⟩
    let hQ := hq n m k
    have horacle := isRealMatrix_parallelMarkingOracle (m := m) S
    let Δ₀ := tcQSetLow (q₁ n m k) Δ.qSet
    have hsupp : SupportedOn (· = (0 : Fin (2 ^ q₂ n m k))) Δ.qSet := by
      refine supportedOn_qSet ?_ Δ; rfl
    have hpad : tcPadStateLow (tcLowBlockReg hQ) Δ₀ = Δ.qSet :=
      tcPadStateLow_tcQSetLow_of_supportedOn_zero _ hsupp
    have htr₀ : Δ₀.trace = Δ.trace := by
      rw [← CQState.trace_qSet Δ, ← hpad, trace_tcPadStateLow]
    have hcb₀ := hq_cb S hS Δ₀
    rw [expectedCost_qSeq, expectedCost_qSet, CostModel.ofEmbeddedOracle_resetCost,
      Nat.cast_zero, mul_zero, zero_add, interp_qSet, QMonad.Q.toStateFun_qSet,
      qSet_tcQSetLow, htr₀] at hcb₀
    rw [expectedCost_qSeq, expectedCost_qSet, CostModel.ofEmbeddedOracle_resetCost,
      Nat.cast_zero, mul_zero, zero_add, interp_qSet, QMonad.Q.toStateFun_qSet, ← hpad]
    exact (expectedCost_tcLiftCircLow_le hQ horacle (c n m k) Δ₀).trans hcb₀

/-- Cellwise circuit dispatcher over an arbitrary qubit-width function `qFn`. -/
noncomputable abbrev dispatchFindAllCircuitTC {Var : Type}
    (qFn : ℕ → ℕ → ℕ → ℕ)
    (useLeft : ℕ → ℕ → Bool)
    (c₁ c₂ : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ qFn n m k)) Var (qFn n m k) ((n + 1) * m))
    (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ qFn n m k)) Var (qFn n m k) ((n + 1) * m) :=
  if useLeft m k then c₁ n m k else c₂ n m k

theorem ValidFindAllFamilyTC.combine {Var : Type} [DecidableEq Var] {res : Var}
    {p₁ p₂ : FindAllCostProfile} {qFn : ℕ → ℕ → ℕ → ℕ}
    {c₁ c₂ : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ qFn n m k)) Var (qFn n m k) ((n + 1) * m)}
    (h₁ : ValidFindAllFamilyTC res p₁ qFn c₁)
    (h₂ : ValidFindAllFamilyTC res p₂ qFn c₂) :
    ValidFindAllFamilyTC res (p₁.combine p₂) qFn
      (dispatchFindAllCircuitTC qFn (p₁.selectLeft p₂) c₁ c₂) where
  correctness hn hmk hvalid hkN hS := by
    dsimp only [dispatchFindAllCircuitTC]
    cases hsel : p₁.selectLeft p₂ _ _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact h₂.correctness hn hmk (p₁.validCell_right_of_not_selectLeft hvalid hsel) hkN hS
    · simp only [↓reduceIte]
      exact h₁.correctness hn hmk (p₁.validCell_left_of_selectLeft hsel) hkN hS
  costBound_uniform hmk hvalid := by
    dsimp only [FindAllCostProfile.combine, dispatchFindAllCircuitTC]
    cases hsel : p₁.selectLeft p₂ _ _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact h₂.costBound_uniform hmk (p₁.validCell_right_of_not_selectLeft hvalid hsel)
    · simp only [↓reduceIte]
      exact h₁.costBound_uniform hmk (p₁.validCell_left_of_selectLeft hsel)

end QuantumComputation.Specs.GroverFindAll
