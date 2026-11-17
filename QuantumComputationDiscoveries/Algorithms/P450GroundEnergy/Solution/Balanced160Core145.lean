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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MobiusZeroCmp20
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ZeroCmp20OuterAnfParam

/-!
# Balanced `145`-Leaf Stage-2 Core (`11,818 T`, `0 TOFF`, `159` Clean Inner Ancillas)

Defines the balanced `145`-leaf Stage-2 `SELECT` core (`11,818 T`, `0 TOFF`, `159` clean inner
ancillas) on top of `MobiusZeroCmp20` and `ZeroCmp20OuterAnfParam`.
-/
@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open CircuitModular GivensOps
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation

namespace Lac2Fused184Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OneHotSimulates
/-- Syntactic predicate stating that a `DynamicCircuit` only measures into classical store
variable `v` and only branches on expressions depending solely on `σ v`. -/
def OnlyUsesVar {Var : Type} {n : ℕ} (v : Var) : DynamicCircuit Var n → Prop :=
  DynamicCircuit.qcRec
    (fun _ ↦ True)
    (fun x _ ↦ x = v)
    (fun cond _ _ ht hf ↦
      (∀ σ₁ σ₂ : Store Var, σ₁ v = σ₂ v → cond.holds σ₁ = cond.holds σ₂) ∧ ht ∧ hf)
    (fun _ _ h₁ h₂ ↦ h₁ ∧ h₂)
theorem wp_measure_coe {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (q : QRegister 1 n) (A : QCAssertion Var (2 ^ n))
    (σ : Store Var) :
    (wp (DynamicCircuit.measure v q).compile A σ).1 =
      ∑ o : Fin 2,
        (A (Function.update σ v (Int.ofNat o.val))).1.conj (q.basisOutcomeProjector o)ᴴ := by
  have := Fintype.ofFinite Var
  rw [DynamicCircuit.compile_measure, QProg.measureRegister, qc_wp_qMeasure',
    qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe]
  simp [qc_qMeasure_outcome_herm_eq_conj, Store.subst]
theorem wp_eq_of_eq_on_v_fiber {Var : Type} [Finite Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {v : Var} {P : DynamicCircuit Var n}
    (hP : OnlyUsesVar v P) {Φ₁ Φ₂ : QCAssertion Var (2 ^ n)} {σ₁ σ₂ : Store Var}
    (hσ : σ₁ v = σ₂ v)
    (hΦ : ∀ val : ℤ, Φ₁ (Function.update σ₁ v val) = Φ₂ (Function.update σ₂ v val)) :
    wp P.compile Φ₁ σ₁ = wp P.compile Φ₂ σ₂ := by
  have := Fintype.ofFinite Var
  induction P using DynamicCircuit.qcInd generalizing Φ₁ Φ₂ σ₁ σ₂ with
  | circuit c =>
      have hΦeq : Φ₁ σ₁ = Φ₂ σ₂ := by
        have h := hΦ (σ₁ v)
        rwa [Function.update_eq_self, hσ, Function.update_eq_self] at h
      simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile,
        qcWpQAssign, hΦeq]
  | measure x r =>
      have hx : x = v := hP
      subst hx
      apply Subtype.ext
      rw [wp_measure_coe, wp_measure_coe]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [hΦ (Int.ofNat o.val)]
  | qIf cond t f iht ihf =>
      rcases hP with ⟨hcond, ht, hf⟩
      have hc : cond.holds σ₁ = cond.holds σ₂ := hcond σ₁ σ₂ hσ
      by_cases h0 : cond.holds σ₂ <;>
        simp [hc, h0, iht ht hσ hΦ, ihf hf hσ hΦ]
  | seq p₁ p₂ ih₁ ih₂ =>
      rcases hP with ⟨hp₁, hp₂⟩
      simp only [DynamicCircuit.compile_seq, wp]
      refine ih₁ hp₁ hσ fun val => ih₂ hp₂ (by simp) fun val' => ?_
      simpa only [Function.update_idem] using hΦ val'
/-- Converts `DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace` into
`CleanDyn.CleanRealizes` whenever `P.count .TOFF = 0` and `OnlyUsesVar v P`. -/
theorem cleanRealizes_of_realizesEmbedded {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)] (v : Var)
    (rAct : QRegister k N) (rScr : QRegister s N) (hdisj : rAct.DisjointWires rScr)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Var N)
    (htoff : P.count PrimitiveGate.TOFF = 0)
    (hvar : OnlyUsesVar v P)
    (hemb : DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rScr U P) :
    CleanDyn.CleanRealizes v rAct rScr U P := by
  refine CleanDyn.CleanRealizes.mk_of_disjoint v rAct rScr hdisj U P htoff ?_ ?_
  · intro Θ hΘ σ val
    obtain ⟨M', hM', _⟩ := hemb (Θ σ)
    have h1 := wp_eq_of_eq_on_v_fiber hvar (Φ₁ := Θ) (Φ₂ := fun _ => Θ σ)
      (σ₁ := Function.update σ v val) (σ₂ := Function.update σ v val) rfl
      (fun val' => by simp only [Function.update_idem, hΘ σ val'])
    have h2 := wp_eq_of_eq_on_v_fiber hvar (Φ₁ := Θ) (Φ₂ := fun _ => Θ σ)
      (σ₁ := σ) (σ₂ := σ) rfl (fun val' => hΘ σ val')
    rw [h1, h2, congrFun hM' (Function.update σ v val), congrFun hM' σ]
  · intro Θ hΘ
    funext σ
    obtain ⟨M', hM', hproj⟩ := hemb (Θ σ)
    have h1 := wp_eq_of_eq_on_v_fiber hvar (Φ₁ := Θ) (Φ₂ := fun _ => Θ σ)
      (σ₁ := σ) (σ₂ := σ) rfl (fun val' => hΘ σ val')
    have hM'σ : wp P.compile (fun _ => Θ σ) σ = M' := congrFun hM' σ
    apply Subtype.ext; ext1
    simp only [restrictAssertionToZeroAncilla_coe, h1, hM'σ, qcWpQAssign, qcQAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_apply_mat,
      QRegister.basisOutcomeProjector_conjTranspose, conjTranspose_conjTranspose,
      Matrix.mul_assoc] at hproj ⊢
    exact hproj
/-- Converts `CleanDyn.CleanRealizes` into
`DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace` whenever `OnlyUsesVar v P`. -/
theorem realizesEmbedded_of_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)] (v : Var)
    (rAct : QRegister k N) (rScr : QRegister s N)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Var N)
    (hvar : OnlyUsesVar v P)
    (hclean : CleanDyn.CleanRealizes v rAct rScr U P) :
    DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rScr U P := by
  intro M
  let σ₀ : Store Var := fun _ => 0
  refine ⟨wp P.compile (fun _ => M) σ₀, ?_, ?_⟩
  · funext σ
    have h1 := wp_eq_of_eq_on_v_fiber hvar (Φ₁ := fun _ => M) (Φ₂ := fun _ => M)
      (σ₁ := σ) (σ₂ := Function.update σ₀ v (σ v)) (by simp) (fun _ => rfl)
    rw [h1, hclean.2.1 (fun _ => M) (fun _ _ => rfl) σ₀ (σ v)]
  · have hproj := congrArg (fun f : QCAssertion Var (2 ^ N) => (f σ₀).1.mat)
      (hclean.2.2.1 (fun _ => M) (fun _ _ => rfl))
    simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_apply_mat,
      QRegister.basisOutcomeProjector_conjTranspose, conjTranspose_conjTranspose,
      Matrix.mul_assoc] at hproj ⊢
    exact hproj
/-- Lifts a single-variable `DynamicCircuit Unit n` into `DynamicCircuit Var n` by mapping
all classical measurements and store reads to variable `v : Var`. -/
def liftUnitVar {Var : Type} {n : ℕ} (v : Var) : DynamicCircuit Unit n → DynamicCircuit Var n :=
  DynamicCircuit.qcFold
    .circuit
    (fun _ r ↦ .measure v r)
    (fun cond t f ↦ DynamicCircuit.qcRawQIf (cond.pull (fun σ _ ↦ σ v)) t f)
    .seq

@[simp]
theorem liftUnitVar_circuit {Var : Type} {n : ℕ} (v : Var) (c : Circuit n) :
    liftUnitVar v (.circuit c) = .circuit c :=
  DynamicCircuit.qcFold_circuit _ _ _ _ c

@[simp]
theorem liftUnitVar_measure {Var : Type} {n : ℕ} (v : Var) (u : Unit) (r : QRegister 1 n) :
    liftUnitVar v (.measure u r) = .measure v r :=
  DynamicCircuit.qcFold_measure _ _ _ _ u r

@[simp]
theorem liftUnitVar_qIf {Var : Type} {n : ℕ} (v : Var) (cond : QCRawGuard Unit)
    (t f : DynamicCircuit Unit n) :
    liftUnitVar v (DynamicCircuit.qcRawQIf cond t f) =
      DynamicCircuit.qcRawQIf (cond.pull (fun σ _ ↦ σ v)) (liftUnitVar v t) (liftUnitVar v f) :=
  DynamicCircuit.qcFold_qIf _ _ _ _ cond t f

@[simp]
theorem liftUnitVar_seq {Var : Type} {n : ℕ} (v : Var) (p₁ p₂ : DynamicCircuit Unit n) :
    liftUnitVar v (.seq p₁ p₂) = .seq (liftUnitVar v p₁) (liftUnitVar v p₂) :=
  DynamicCircuit.qcFold_seq _ _ _ _ p₁ p₂
@[simp]
theorem count_liftUnitVar {Var : Type} {n a : ℕ} (v : Var) (g : PrimitiveGate a)
    (P : DynamicCircuit Unit n) :
    (liftUnitVar v P).count g = P.count g := by
  induction P using DynamicCircuit.qcInd with
  | circuit _ => simp
  | measure _ _ => simp
  | qIf _ _ _ iht ihf => simp [iht, ihf]
  | seq _ _ ih₁ ih₂ => simp [ih₁, ih₂]
theorem onlyUsesVar_liftUnitVar {Var : Type} {n : ℕ} (v : Var) (P : DynamicCircuit Unit n) :
    OnlyUsesVar v (liftUnitVar v P) := by
  induction P using DynamicCircuit.qcInd with
  | circuit _ => simp only [liftUnitVar_circuit]; trivial
  | measure _ _ => simp only [liftUnitVar_measure]; rfl
  | qIf cond _ _ iht ihf =>
      simp only [liftUnitVar_qIf]
      exact ⟨fun _ _ h => congrArg cond.holds (funext fun _ => h), iht, ihf⟩
  | seq _ _ ih₁ ih₂ => simp only [liftUnitVar_seq]; exact ⟨ih₁, ih₂⟩
theorem wp_liftUnitVar {Var : Type} [Finite Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (P : DynamicCircuit Unit n)
    (Φ : QCAssertion Unit (2 ^ n)) (σ : Store Var) :
    wp (liftUnitVar v P).compile (fun τ => Φ (fun _ => τ v)) σ =
      wp P.compile Φ (fun _ => σ v) := by
  have := Fintype.ofFinite Var
  induction P using DynamicCircuit.qcInd generalizing Φ σ with
  | circuit c =>
      simp only [liftUnitVar_circuit, DynamicCircuit.compile_circuit,
        DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign]
  | measure u r =>
      apply Subtype.ext
      simp only [liftUnitVar_measure]
      rw [wp_measure_coe, wp_measure_coe]
      refine Finset.sum_congr rfl fun o _ => ?_
      have hsub : (fun _ : Unit => Function.update σ v (Int.ofNat o.val) v) =
          Function.update (fun _ : Unit => σ v) u (Int.ofNat o.val) := by
        funext x; cases x; cases u; simp
      rw [hsub]
  | qIf cond t f iht ihf =>
      by_cases h0 : cond.holds (fun _ => σ v) <;>
        simp [h0, iht, ihf]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [liftUnitVar_seq, DynamicCircuit.compile_seq, wp]
      have h₂ : wp (liftUnitVar v p₂).compile (fun τ' => Φ (fun _ => τ' v)) =
          (fun τ : Store Var => wp p₂.compile Φ (fun _ => τ v)) :=
        funext fun τ => ih₂ Φ τ
      rw [h₂, ih₁]
theorem realizesEmbedded_liftUnitVar {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)] (v : Var)
    (rAct : QRegister k N) (rScr : QRegister s N)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Unit N)
    (hemb : DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rScr U P) :
    DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rScr U (liftUnitVar v P) := by
  intro M
  obtain ⟨M', hM', hproj⟩ := hemb M
  refine ⟨M', ?_, hproj⟩
  funext σ
  simpa only [congrFun hM' (fun _ => σ v)] using wp_liftUnitVar v P (fun _ => M) σ
theorem cleanRealizes_liftUnitVar {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)] (v : Var)
    (rAct : QRegister k N) (rScr : QRegister s N) (hdisj : rAct.DisjointWires rScr)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Unit N)
    (htoff : P.count PrimitiveGate.TOFF = 0)
    (hemb : DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rScr U P) :
    CleanDyn.CleanRealizes v rAct rScr U (liftUnitVar v P) :=
  cleanRealizes_of_realizesEmbedded v rAct rScr hdisj U (liftUnitVar v P)
    (by simp [htoff]) (onlyUsesVar_liftUnitVar v P)
    (realizesEmbedded_liftUnitVar v rAct rScr U P hemb)
/-- Computational-basis diagonal projector onto bit assignments satisfying `S`. -/
noncomputable def ketPredProj {n : ℕ} (S : BitAssignment n → Prop) : Operator (2 ^ n) :=
  open Classical in
  Matrix.diagonal fun g => if S (basisBits n g) then 1 else 0
theorem ketPredProj_mulVec_ket {n : ℕ} (S : BitAssignment n → Prop) [DecidablePred S]
    (β : BitAssignment n) :
    (ketPredProj S).mulVec (ket β) = if S β then ket β else 0 := by
  classical
  have hket : ket β = Pi.single ((basisBits n).symm β) 1 := rfl
  rw [ketPredProj, hket, Matrix.diagonal_mulVec_single, mul_one, basisBits_basisBitsEquiv_symm]
  by_cases h : S β <;> simp [h]
/-- Predicate characterizing computational-basis `{0, 1}`-diagonal projectors. -/
def IsDiagProj {n : ℕ} (P : Operator (2 ^ n)) : Prop :=
  ∃ S : BitAssignment n → Prop, P = ketPredProj S
theorem IsDiagProj.conjTranspose_eq {n : ℕ} {P : Operator (2 ^ n)} (hP : IsDiagProj P) :
    Pᴴ = P := by
  classical
  rcases hP with ⟨S, rfl⟩
  rw [ketPredProj, Matrix.diagonal_conjTranspose]
  congr 1; funext g; by_cases h : S (basisBits n g) <;> simp [h]
theorem IsDiagProj.mul_self {n : ℕ} {P : Operator (2 ^ n)} (hP : IsDiagProj P) :
    P * P = P := by
  classical
  rcases hP with ⟨S, rfl⟩
  rw [ketPredProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext g; by_cases h : S (basisBits n g) <;> simp [h]
theorem IsDiagProj.comm {n : ℕ} {P₁ P₂ : Operator (2 ^ n)}
    (h₁ : IsDiagProj P₁) (h₂ : IsDiagProj P₂) : P₁ * P₂ = P₂ * P₁ := by
  classical
  rcases h₁ with ⟨S₁, rfl⟩; rcases h₂ with ⟨S₂, rfl⟩
  rw [ketPredProj, ketPredProj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext g; ring
theorem IsDiagProj.mul {n : ℕ} {P₁ P₂ : Operator (2 ^ n)}
    (h₁ : IsDiagProj P₁) (h₂ : IsDiagProj P₂) : IsDiagProj (P₁ * P₂) := by
  classical
  rcases h₁ with ⟨S₁, rfl⟩; rcases h₂ with ⟨S₂, rfl⟩
  refine ⟨fun β => S₁ β ∧ S₂ β, ?_⟩
  rw [ketPredProj, ketPredProj, ketPredProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext g
  by_cases h1 : S₁ (basisBits n g) <;> by_cases h2 : S₂ (basisBits n g) <;> simp [h1, h2]
theorem IsDiagProj.basisOutcomeProjector {m n : ℕ} (r : QRegister m n) (o : Fin (2 ^ m)) :
    IsDiagProj (r.basisOutcomeProjector o) := by
  refine ⟨fun β => localIdx r β = o, ?_⟩
  classical
  rw [QRegister.basisOutcomeProjector_eq_diagonal, ketPredProj]
  congr 1; funext g
  have heq : localIdx r (basisBits n g) = r.extractIndex g := by
    simp [localIdx, QRegister.extractIndex]
  simp [heq]
theorem unitary_conjTranspose_mul_self_eq {d : ℕ} (U : Unitary d) : U.1ᴴ * U.1 = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp U.2
theorem IsDiagProj.conj_of_ket_map {n : ℕ} (U : Unitary (2 ^ n))
    (hU : ∀ β : BitAssignment n, ∃ β' : BitAssignment n, U.1.mulVec (ket β) = ket β')
    {P : Operator (2 ^ n)} (hP : IsDiagProj P) :
    IsDiagProj (U.1ᴴ * P * U.1) := by
  classical
  rcases hP with ⟨S, rfl⟩
  choose f hf using hU
  refine ⟨fun β => S (f β), ?_⟩
  apply matrix_ext_ket; intro β
  have hu_inv : U.1ᴴ.mulVec (U.1.mulVec (ket β)) = ket β := by
    rw [Matrix.mulVec_mulVec, unitary_conjTranspose_mul_self_eq U, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf β, ketPredProj_mulVec_ket,
    ketPredProj_mulVec_ket]
  by_cases h : S (f β)
  · simp only [h, ↓reduceIte, ← hf β, hu_inv]
  · simp only [h, ↓reduceIte, Matrix.mulVec_zero]
/-- Generalization of `GlobalCleanSimulates` to any computational-basis diagonal projector `P`. -/
def DiagProjSimulates {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (P : Operator (2 ^ n)) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  IsDiagProj P ∧
  U.1 * P = P * U.1 ∧
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    P * M'.1.1 * P = P * (U.1ᴴ * M.1.1 * U.1) * P
theorem DiagProjSimulates.ofGlobalCleanSimulates {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)] {rClean : QRegister m n} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (hd : GlobalCleanSimulates rClean U d) :
    DiagProjSimulates (rClean.basisOutcomeProjector 0) U d :=
  ⟨IsDiagProj.basisOutcomeProjector rClean 0, hd.1, hd.2⟩
theorem DiagProjSimulates.toGlobalCleanSimulates {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)] {rClean : QRegister m n} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (hd : DiagProjSimulates (rClean.basisOutcomeProjector 0) U d) :
    GlobalCleanSimulates rClean U d :=
  ⟨hd.2.1, hd.2.2⟩
theorem DiagProjSimulates.tighten {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P₁ P₂ : Operator (2 ^ n)} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (hd : DiagProjSimulates P₂ U d)
    (hP₁ : IsDiagProj P₁) (hsub : P₁ * P₂ = P₁) (hcomm : U.1 * P₁ = P₁ * U.1) :
    DiagProjSimulates P₁ U d := by
  have hsubR : P₂ * P₁ = P₁ := (hP₁.comm hd.1).symm.trans hsub
  refine ⟨hP₁, hcomm, fun M => ?_⟩
  obtain ⟨M', hwp, hproj⟩ := hd.2.2 M
  refine ⟨M', hwp, ?_⟩
  calc P₁ * M'.1.1 * P₁ = (P₁ * P₂) * M'.1.1 * (P₂ * P₁) := by rw [hsub, hsubR]
    _ = P₁ * (P₂ * M'.1.1 * P₂) * P₁ := by simp only [Matrix.mul_assoc]
    _ = P₁ * (P₂ * (U.1ᴴ * M.1.1 * U.1) * P₂) * P₁ := by rw [hproj]
    _ = (P₁ * P₂) * (U.1ᴴ * M.1.1 * U.1) * (P₂ * P₁) := by simp only [Matrix.mul_assoc]
    _ = P₁ * (U.1ᴴ * M.1.1 * U.1) * P₁ := by rw [hsub, hsubR]
theorem ketPredProj_congr {n : ℕ} {S₁ S₂ : BitAssignment n → Prop}
    (h : ∀ β, S₁ β ↔ S₂ β) : ketPredProj S₁ = ketPredProj S₂ := by
  classical
  rw [ketPredProj, ketPredProj]
  congr 1; funext g
  by_cases hg : S₁ (basisBits n g)
  · simp [hg, (h _).mp hg]
  · simp [hg, mt (h _).mpr hg]
theorem ketPredProj_mul {n : ℕ} (S₁ S₂ : BitAssignment n → Prop) :
    ketPredProj S₁ * ketPredProj S₂ = ketPredProj (fun β => S₁ β ∧ S₂ β) := by
  classical
  rw [ketPredProj, ketPredProj, ketPredProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext g
  by_cases h1 : S₁ (basisBits n g) <;> by_cases h2 : S₂ (basisBits n g) <;> simp [h1, h2]
theorem ketPredProj_mul_of_imp {n : ℕ} {S₁ S₂ : BitAssignment n → Prop}
    (h : ∀ β, S₁ β → S₂ β) : ketPredProj S₁ * ketPredProj S₂ = ketPredProj S₁ :=
  (ketPredProj_mul S₁ S₂).trans (ketPredProj_congr fun β => ⟨And.left, fun h1 => ⟨h1, h β h1⟩⟩)
theorem basisOutcomeProjector_zero_eq_ketPredProj {m n : ℕ} (r : QRegister m n) :
    r.basisOutcomeProjector 0 = ketPredProj (fun β => ∀ i : Fin m, β (r i) = 0) := by
  classical
  rw [QRegister.basisOutcomeProjector_eq_diagonal, ketPredProj]
  congr 1; funext g
  simp [QRegister.extractIndex_eq_zero_iff]
theorem DiagProjSimulates.conjSelfInv {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P : Operator (2 ^ n)} {U : Unitary (2 ^ n)}
    {body : DynamicCircuit Var n} (hBody : DiagProjSimulates P U body)
    (c : Circuit n) (hsq : c.eval * c.eval = 1)
    (hket : ∀ β : BitAssignment n, ∃ β', c.eval.1.mulVec (ket β) = ket β') :
    DiagProjSimulates (c.eval.1 * P * c.eval.1) (c.eval * U * c.eval)
      (.seq (.circuit c) (.seq body (.circuit c))) := by
  obtain ⟨C, hC⟩ : ∃ C, c.eval = C := ⟨c.eval, rfl⟩
  rw [hC] at hsq hket ⊢
  obtain ⟨P_out, hP_out⟩ : ∃ P_out : Operator (2 ^ n), C.1 * P * C.1 = P_out := ⟨_, rfl⟩
  rw [hP_out]
  have hCherm : C.1ᴴ = C.1 := unitary_conjTranspose_eq_self_of_mul_self C hsq
  have hCsq : C.1 * C.1 = 1 := congrArg Subtype.val hsq
  have hDiag : IsDiagProj P_out := by
    rw [← hP_out]; nth_rw 1 [← hCherm]; exact hBody.1.conj_of_ket_map C hket
  have hCP : C.1 * P_out = P * C.1 := by
    rw [← hP_out]
    calc C.1 * (C.1 * P * C.1) = (C.1 * C.1) * P * C.1 := by simp only [Matrix.mul_assoc]
      _ = P * C.1 := by rw [hCsq, Matrix.one_mul]
  have hPC : P_out * C.1 = C.1 * P := by
    rw [← hP_out]
    calc (C.1 * P * C.1) * C.1 = C.1 * P * (C.1 * C.1) := by simp only [Matrix.mul_assoc]
      _ = C.1 * P := by rw [hCsq, Matrix.mul_one]
  refine ⟨hDiag, ?_, fun M => ?_⟩
  · change (C.1 * U.1 * C.1) * P_out = P_out * (C.1 * U.1 * C.1)
    calc (C.1 * U.1 * C.1) * P_out
        = C.1 * U.1 * (C.1 * P_out) := by simp only [Matrix.mul_assoc]
      _ = C.1 * (U.1 * P) * C.1 := by rw [hCP]; simp only [Matrix.mul_assoc]
      _ = (C.1 * P) * U.1 * C.1 := by rw [hBody.2.1]; simp only [Matrix.mul_assoc]
      _ = (P_out * C.1) * U.1 * C.1 := by rw [hPC]
      _ = P_out * (C.1 * U.1 * C.1) := by simp only [Matrix.mul_assoc]
  · let M₂ := qcQAssignObsMap C M
    obtain ⟨M₁, hwp₁, hproj₁⟩ := hBody.2.2 M₂
    refine ⟨qcQAssignObsMap C M₁, ?_, ?_⟩
    · funext σ
      simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp,
        DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, hC]
      exact congrArg (qcQAssignObsMap C) (congrFun hwp₁ σ)
    · have hM₂ : M₂.1.1 = C.1ᴴ * M.1.1 * C.1 := by
        simp [M₂, qcQAssignObsMap, Matrix.star_eq_conjTranspose]
      have hM' : (qcQAssignObsMap C M₁).1.1 = C.1ᴴ * M₁.1.1 * C.1 := by
        simp [qcQAssignObsMap, Matrix.star_eq_conjTranspose]
      change P_out * (qcQAssignObsMap C M₁).1.1 * P_out =
        P_out * ((C.1 * U.1 * C.1)ᴴ * M.1.1 * (C.1 * U.1 * C.1)) * P_out
      rw [hM', hCherm]
      calc P_out * (C.1 * M₁.1.1 * C.1) * P_out
          = (P_out * C.1) * M₁.1.1 * (C.1 * P_out) := by simp only [Matrix.mul_assoc]
        _ = C.1 * (P * M₁.1.1 * P) * C.1 := by rw [hPC, hCP]; simp only [Matrix.mul_assoc]
        _ = C.1 * (P * (U.1ᴴ * M₂.1.1 * U.1) * P) * C.1 := by rw [hproj₁]
        _ = (C.1 * P) * U.1ᴴ * (C.1 * M.1.1 * C.1) * U.1 * (P * C.1) := by
              rw [hM₂, hCherm]; simp only [Matrix.mul_assoc]
        _ = (P_out * C.1) * U.1ᴴ * (C.1 * M.1.1 * C.1) * U.1 * (C.1 * P_out) := by
              rw [hPC, hCP]
        _ = P_out * ((C.1 * U.1 * C.1)ᴴ * M.1.1 * (C.1 * U.1 * C.1)) * P_out := by
              simp only [Matrix.conjTranspose_mul, hCherm, Matrix.mul_assoc]
theorem DiagProjSimulates.tempAnd {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    {P_mid : Operator (2 ^ n)} {U_mid : Unitary (2 ^ n)} {body : DynamicCircuit Var n}
    (hBody : DiagProjSimulates P_mid U_mid body)
    (hc₁ : CommutesWithWire c₁ U_mid.1)
    (hc₂ : CommutesWithWire c₂ U_mid.1)
    (hanc : CommutesWithWire anc U_mid.1) :
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
    let P_a := (QRegister.singleton anc).basisOutcomeProjector 0
    DiagProjSimulates ((T_anc.1 * P_mid * T_anc.1) * P_a) (T_anc * U_mid * T_anc)
      (tempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a body) := by
  dsimp only
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  let P_a := (QRegister.singleton anc).basisOutcomeProjector 0
  have hT_sq : T_anc * T_anc = 1 := toffoli_eval_mul_self c₁ c₂ anc h₁₂ h₁a h₂a
  have hT_herm : T_anc.1ᴴ = T_anc.1 := unitary_conjTranspose_eq_self_of_mul_self T_anc hT_sq
  have hPa_diag : IsDiagProj P_a := IsDiagProj.basisOutcomeProjector (QRegister.singleton anc) 0
  have hPa_herm : P_aᴴ = P_a := hPa_diag.conjTranspose_eq
  have hPre_diag : IsDiagProj (T_anc.1 * P_mid * T_anc.1) := by
    have heq : T_anc.1 * P_mid * T_anc.1 = T_anc.1ᴴ * P_mid * T_anc.1 := by rw [hT_herm]
    rw [heq]; exact hBody.1.conj_of_ket_map T_anc fun β => ⟨_, ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β⟩
  have hVa_raw : (T_anc * U_mid * T_anc).1 * P_a = P_a * (T_anc * U_mid * T_anc).1 :=
    (toffoli_conj_commutesWithWire_ancilla h₁₂ h₁a h₂a hc₁ hc₂ hanc) 0
  obtain ⟨P_pre, hP_pre⟩ : ∃ P_pre : Operator (2 ^ n), T_anc.1 * P_mid * T_anc.1 = P_pre :=
    ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Unitary (2 ^ n), T_anc * U_mid * T_anc = V := ⟨_, rfl⟩
  change DiagProjSimulates ((T_anc.1 * P_mid * T_anc.1) * P_a) (T_anc * U_mid * T_anc)
    (tempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a body)
  rw [hP_pre, hV]
  rw [hP_pre] at hPre_diag
  rw [hV] at hVa_raw
  have hT_mat_sq : T_anc.1 * T_anc.1 = 1 := congrArg Subtype.val hT_sq
  have hP_comm : P_pre * P_a = P_a * P_pre := hPre_diag.comm hPa_diag
  have hTP : T_anc.1 * P_pre = P_mid * T_anc.1 := by
    rw [← hP_pre]
    calc T_anc.1 * (T_anc.1 * P_mid * T_anc.1) = (T_anc.1 * T_anc.1) * P_mid * T_anc.1 := by
          simp only [Matrix.mul_assoc]
      _ = P_mid * T_anc.1 := by rw [hT_mat_sq, Matrix.one_mul]
  have hPT : P_pre * T_anc.1 = T_anc.1 * P_mid := by
    rw [← hP_pre]
    calc (T_anc.1 * P_mid * T_anc.1) * T_anc.1 = T_anc.1 * P_mid * (T_anc.1 * T_anc.1) := by
          simp only [Matrix.mul_assoc]
      _ = T_anc.1 * P_mid := by rw [hT_mat_sq, Matrix.mul_one]
  have hV_a_adj : P_a * V.1ᴴ = V.1ᴴ * P_a := by
    simpa only [Matrix.conjTranspose_mul, hPa_herm] using congrArg Matrix.conjTranspose hVa_raw
  have hV_pre : V.1 * P_pre = P_pre * V.1 := by
    rw [← hV]
    change (T_anc.1 * U_mid.1 * T_anc.1) * P_pre = P_pre * (T_anc.1 * U_mid.1 * T_anc.1)
    calc (T_anc.1 * U_mid.1 * T_anc.1) * P_pre
        = T_anc.1 * U_mid.1 * (T_anc.1 * P_pre) := by simp only [Matrix.mul_assoc]
      _ = T_anc.1 * (U_mid.1 * P_mid) * T_anc.1 := by rw [hTP]; simp only [Matrix.mul_assoc]
      _ = (T_anc.1 * P_mid) * U_mid.1 * T_anc.1 := by rw [hBody.2.1]; simp only [Matrix.mul_assoc]
      _ = (P_pre * T_anc.1) * U_mid.1 * T_anc.1 := by rw [hPT]
      _ = P_pre * (T_anc.1 * U_mid.1 * T_anc.1) := by simp only [Matrix.mul_assoc]
  have hUT : U_mid.1 * T_anc.1 = T_anc.1 * V.1 := by
    have h : T_anc * V = U_mid * T_anc := by
      rw [← hV, ← mul_assoc T_anc (T_anc * U_mid) T_anc, ← mul_assoc T_anc T_anc U_mid,
        hT_sq, one_mul]
    exact (congrArg Subtype.val h).symm
  refine ⟨hPre_diag.mul hPa_diag, ?_, fun M => ?_⟩
  · calc V.1 * (P_pre * P_a) = (V.1 * P_pre) * P_a := by rw [← Matrix.mul_assoc]
      _ = P_pre * (V.1 * P_a) := by rw [hV_pre, Matrix.mul_assoc]
      _ = (P_pre * P_a) * V.1 := by rw [hVa_raw, ← Matrix.mul_assoc]
  · obtain ⟨M_unc, hwp_unc⟩ := wp_andUncompute_const v c₁ c₂ anc h₁₂ M
    obtain ⟨M_body, hwp_body, hproj_body⟩ := hBody.2.2 M_unc
    let C_and := (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval
    let M' := qcQAssignObsMap C_and M_body
    refine ⟨M', ?_, ?_⟩
    · funext σ
      simp only [tempAndProg, DynamicCircuit.andCompute, DynamicCircuit.compile_seq,
        DynamicCircuit.compile_circuit, wp, DynamicCircuit.qc_wp_circuit_compile, hwp_unc, hwp_body]
      rfl
    · have h1_raw := open DynamicCircuit in
        qc_wp_toffoli_andUncompute_of_update_eq
          v c₁ c₂ anc h₁₂ h₁a h₂a (fun _ : Store Var => M) (fun _ _ => rfl)
      have h1_val := congrArg (fun f : QCAssertion Var (2 ^ n) => (f 0).1.1) h1_raw
      rw [hwp_unc] at h1_val
      have hstar1 : P_a * (T_anc.1ᴴ * M_unc.1.1 * T_anc.1) * P_a = P_a * M.1.1 * P_a := by
        dsimp only [P_a, T_anc, restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap]
          at h1_val ⊢
        simpa only [Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
          conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose,
          conjTranspose_conjTranspose, Matrix.mul_assoc, val_eq_coe] using h1_val
      have h3_raw := DynamicCircuit.qc_wp_qAssign_andCompute
        c₁ c₂ anc h₁₂ h₁a h₂a (fun _ : Store Var => M_body)
      have h3_val := congrArg (fun f : QCAssertion Var (2 ^ n) => (f 0).1.1) h3_raw
      have hstaMain : P_a * M'.1.1 * P_a = P_a * (T_anc.1ᴴ * M_body.1.1 * T_anc.1) * P_a := by
        dsimp only [P_a, T_anc, M', C_and, restrictAssertionToZeroAncilla_coe, qcWpQAssign,
          qcQAssignObsMap] at h3_val ⊢
        simpa only [Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
          conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose,
          conjTranspose_conjTranspose, Matrix.mul_assoc, val_eq_coe] using h3_val
      have hUT_Pa : U_mid.1 * (T_anc.1 * P_a) = (T_anc.1 * P_a) * V.1 := by
        calc U_mid.1 * (T_anc.1 * P_a) = (U_mid.1 * T_anc.1) * P_a := by rw [← Matrix.mul_assoc]
          _ = T_anc.1 * (V.1 * P_a) := by rw [hUT, Matrix.mul_assoc]
          _ = (T_anc.1 * P_a) * V.1 := by rw [hVa_raw, ← Matrix.mul_assoc]
      have hUT_Pa_adj : (P_a * T_anc.1ᴴ) * U_mid.1ᴴ = V.1ᴴ * (P_a * T_anc.1ᴴ) := by
        simpa only [Matrix.conjTranspose_mul, hPa_herm, Matrix.mul_assoc] using
          congrArg Matrix.conjTranspose hUT_Pa
      have hL1 : P_pre * P_a * T_anc.1ᴴ = P_a * T_anc.1ᴴ * P_mid := by
        rw [hP_comm, hT_herm, Matrix.mul_assoc, hPT, ← Matrix.mul_assoc]
      have hR1 : T_anc.1 * P_a * P_pre = P_mid * T_anc.1 * P_a := by
        rw [Matrix.mul_assoc, ← hP_comm, ← Matrix.mul_assoc, hTP]
      calc (P_pre * P_a) * M'.1.1 * (P_pre * P_a)
          = P_pre * (P_a * M'.1.1 * P_a) * P_pre := by
              nth_rw 2 [hP_comm]; simp only [Matrix.mul_assoc]
        _ = (P_pre * P_a * T_anc.1ᴴ) * M_body.1.1 * (T_anc.1 * P_a * P_pre) := by
              rw [hstaMain]; simp only [Matrix.mul_assoc]
        _ = (P_a * T_anc.1ᴴ) * (P_mid * M_body.1.1 * P_mid) * (T_anc.1 * P_a) := by
              rw [hL1, hR1]; simp only [Matrix.mul_assoc]
        _ = (P_a * T_anc.1ᴴ) * (P_mid * (U_mid.1ᴴ * M_unc.1.1 * U_mid.1) * P_mid) *
              (T_anc.1 * P_a) := by rw [hproj_body]
        _ = ((P_a * T_anc.1ᴴ * P_mid) * U_mid.1ᴴ) * M_unc.1.1 *
              (U_mid.1 * (P_mid * T_anc.1 * P_a)) := by simp only [Matrix.mul_assoc]
        _ = P_pre * (((P_a * T_anc.1ᴴ) * U_mid.1ᴴ) * M_unc.1.1 *
              (U_mid.1 * (T_anc.1 * P_a))) * P_pre := by
              rw [← hL1, ← hR1]; simp only [Matrix.mul_assoc]
        _ = P_pre * (V.1ᴴ * (P_a * (T_anc.1ᴴ * M_unc.1.1 * T_anc.1) * P_a) * V.1) * P_pre := by
              rw [hUT_Pa_adj, hUT_Pa]; simp only [Matrix.mul_assoc]
        _ = P_pre * (V.1ᴴ * (P_a * M.1.1 * P_a) * V.1) * P_pre := by rw [hstar1]
        _ = (P_pre * P_a) * (V.1ᴴ * M.1.1 * V.1) * (P_pre * P_a) := by
              calc P_pre * (V.1ᴴ * (P_a * M.1.1 * P_a) * V.1) * P_pre
                  = P_pre * (V.1ᴴ * P_a) * M.1.1 * (P_a * V.1) * P_pre := by
                      simp only [Matrix.mul_assoc]
                _ = P_pre * P_a * V.1ᴴ * M.1.1 * V.1 * (P_a * P_pre) := by
                      rw [← hV_a_adj, ← hVa_raw]; simp only [Matrix.mul_assoc]
                _ = (P_pre * P_a) * (V.1ᴴ * M.1.1 * V.1) * (P_pre * P_a) := by
                      rw [← hP_comm]; simp only [Matrix.mul_assoc]
/-- Zero-`T`, zero-`TOFF` CNOT fan-in circuit XORing `∑_{i : keep i} rSrc[i]` into `wDst`. -/
def xorFilteredRegToWireCircuit {n : ℕ} :
    (m : ℕ) → (Fin m → Bool) → (rSrc : QRegister m n) → (wDst : Wire n) →
      (∀ i : Fin m, rSrc i ≠ wDst) → Circuit n
  | 0, _, _, _, _ => .identity
  | m + 1, keep, rSrc, wDst, hne =>
      let cRest := xorFilteredRegToWireCircuit m (fun i => keep i.castSucc)
        (regInit rSrc) wDst (fun i => hne i.castSucc)
      if keep (Fin.last m) then
        cRest ;;ᶜ Circuit.CNOT (rSrc (Fin.last m)) wDst (hne (Fin.last m))
      else
        cRest
/-- Zero-`T`, zero-`TOFF` CNOT fan-in circuit XORing `∑_i rSrc[i]` into `wDst`. -/
abbrev xorRegToWireCircuit {n : ℕ} (m : ℕ) (rSrc : QRegister m n) (wDst : Wire n)
    (hne : ∀ i : Fin m, rSrc i ≠ wDst) : Circuit n :=
  xorFilteredRegToWireCircuit m (fun _ => true) rSrc wDst hne
@[simp]
theorem count_xorFilteredRegToWireCircuit_t {n : ℕ} :
    ∀ (m : ℕ) (keep : Fin m → Bool) (rSrc : QRegister m n) (wDst : Wire n)
      (hne : ∀ i : Fin m, rSrc i ≠ wDst),
      (xorFilteredRegToWireCircuit m keep rSrc wDst hne).count .T = 0
  | 0, _, _, _, _ => rfl
  | m + 1, keep, rSrc, wDst, hne => by
      dsimp only [xorFilteredRegToWireCircuit]
      have ih := count_xorFilteredRegToWireCircuit_t m (fun i => keep i.castSucc)
        (regInit rSrc) wDst (fun i => hne i.castSucc)
      split_ifs <;> simp [ih]
@[simp]
theorem count_xorFilteredRegToWireCircuit_toff {n : ℕ} :
    ∀ (m : ℕ) (keep : Fin m → Bool) (rSrc : QRegister m n) (wDst : Wire n)
      (hne : ∀ i : Fin m, rSrc i ≠ wDst),
      (xorFilteredRegToWireCircuit m keep rSrc wDst hne).count .TOFF = 0
  | 0, _, _, _, _ => rfl
  | m + 1, keep, rSrc, wDst, hne => by
      dsimp only [xorFilteredRegToWireCircuit]
      have ih := count_xorFilteredRegToWireCircuit_toff m (fun i => keep i.castSucc)
        (regInit rSrc) wDst (fun i => hne i.castSucc)
      split_ifs <;> simp [ih]
theorem ket_xorFilteredRegToWireCircuit {n : ℕ} :
    ∀ (m : ℕ) (keep : Fin m → Bool) (rSrc : QRegister m n) (wDst : Wire n)
      (hne : ∀ i : Fin m, rSrc i ≠ wDst) (β : BitAssignment n),
      (xorFilteredRegToWireCircuit m keep rSrc wDst hne).eval.1.mulVec (ket β) =
        ket (Function.update β wDst (β wDst + ∑ i : Fin m, if keep i then β (rSrc i) else 0))
  | 0, _, _, wDst, _, β => by
      dsimp only [xorFilteredRegToWireCircuit]
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
      simp
  | m + 1, keep, rSrc, wDst, hne, β => by
      dsimp only [xorFilteredRegToWireCircuit]
      have ih := ket_xorFilteredRegToWireCircuit m (fun i => keep i.castSucc)
        (regInit rSrc) wDst (fun i => hne i.castSucc) β
      have hreg : ∀ i : Fin m, (regInit rSrc) i = rSrc i.castSucc := fun _ => rfl
      simp_rw [hreg] at ih
      rw [Fin.sum_univ_castSucc]
      by_cases hk : keep (Fin.last m) = true
      · rw [ite_eq_left hk, eval_seq_mulVec, ih, ket_CNOT]
        congr 1
        rw [Function.update_of_ne (hne (Fin.last m)), Function.update_self,
          Function.update_idem, ite_eq_left hk, add_assoc]
      · rw [ite_eq_right hk, ih, ite_eq_right hk, add_zero]
/-- Control index `0` (`sub = row % 2`) inside `rCtrl10 : QRegister 10 n`. -/
def subIdx10 : Fin 10 := ⟨0, by decide⟩
/-- Control index `1` (`act = en_R`) inside `rCtrl10 : QRegister 10 n`. -/
def actIdx10 : Fin 10 := ⟨1, by decide⟩
/-- Control subregister `2..9` (`pair = row / 2`) inside `rCtrl10 : QRegister 10 n`. -/
def selPair10 : QRegister 8 10 := QRegister.block 2 8 (by decide)
/-- XORs one-hot register `rOneHot` into binary index register `rIdx`. -/
def xorOneHotToIdxCircuit {n : ℕ} :
    (m G : ℕ) → (rIdx : QRegister m n) → (rOneHot : QRegister G n) →
      (∀ i : Fin m, ∀ g : Fin G, rOneHot g ≠ rIdx i) → Circuit n
  | 0, _, _, _, _ => .identity
  | m + 1, G, rIdx, rOneHot, hne =>
      xorOneHotToIdxCircuit m G (regInit rIdx) rOneHot (fun i g => hne i.castSucc g) ;;ᶜ
        xorFilteredRegToWireCircuit G (fun g => decide (g.val / 2 ^ m % 2 = 1))
          rOneHot (rIdx (Fin.last m)) (hne (Fin.last m))
@[simp]
theorem count_xorOneHotToIdxCircuit_t {n : ℕ} :
    ∀ (m G : ℕ) (rIdx : QRegister m n) (rOneHot : QRegister G n)
      (hne : ∀ i : Fin m, ∀ g : Fin G, rOneHot g ≠ rIdx i),
      (xorOneHotToIdxCircuit m G rIdx rOneHot hne).count .T = 0
  | 0, _, _, _, _ => rfl
  | m + 1, G, rIdx, rOneHot, hne => by
      dsimp only [xorOneHotToIdxCircuit]
      simp [count_xorOneHotToIdxCircuit_t m G (regInit rIdx) rOneHot (fun i g => hne i.castSucc g)]
@[simp]
theorem count_xorOneHotToIdxCircuit_toff {n : ℕ} :
    ∀ (m G : ℕ) (rIdx : QRegister m n) (rOneHot : QRegister G n)
      (hne : ∀ i : Fin m, ∀ g : Fin G, rOneHot g ≠ rIdx i),
      (xorOneHotToIdxCircuit m G rIdx rOneHot hne).count .TOFF = 0
  | 0, _, _, _, _ => rfl
  | m + 1, G, rIdx, rOneHot, hne => by
      dsimp only [xorOneHotToIdxCircuit]
      simp [count_xorOneHotToIdxCircuit_toff m G (regInit rIdx) rOneHot
        (fun i g => hne i.castSucc g)]
theorem ket_xorOneHotToIdxCircuit {n : ℕ} :
    ∀ (m G : ℕ) (rIdx : QRegister m n) (rOneHot : QRegister G n)
      (hne : ∀ i : Fin m, ∀ g : Fin G, rOneHot g ≠ rIdx i) (β : BitAssignment n),
      (xorOneHotToIdxCircuit m G rIdx rOneHot hne).eval.1.mulVec (ket β) =
        ket (writeReg β rIdx (fun i =>
          β (rIdx i) +
            ∑ g : Fin G, if decide (g.val / 2 ^ i.val % 2 = 1) then β (rOneHot g) else 0))
  | 0, _, rIdx, _, _, β => by
      dsimp only [xorOneHotToIdxCircuit]
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
      congr 1; funext w
      by_cases hw : w ∈ Set.range rIdx.wires
      · obtain ⟨i, _⟩ := hw; exact i.elim0
      · exact (writeReg_apply_of_not_mem _ _ _ _ hw).symm
  | m + 1, G, rIdx, rOneHot, hne, β => by
      dsimp only [xorOneHotToIdxCircuit]
      rw [eval_seq_mulVec, ket_xorOneHotToIdxCircuit m G (regInit rIdx) rOneHot
        (fun i g => hne i.castSucc g) β, ket_xorFilteredRegToWireCircuit]
      congr 1
      let f_init : Fin m → ZMod 2 := fun i =>
        β ((regInit rIdx) i) +
          ∑ g : Fin G, if decide (g.val / 2 ^ i.val % 2 = 1) then β (rOneHot g) else 0
      have hlast_not_init : rIdx (Fin.last m) ∉ Set.range (regInit rIdx).wires := by
        rintro ⟨i, hi⟩
        exact Fin.castSucc_ne_last i (rIdx.wires.injective hi)
      have hoh_not_init : ∀ g : Fin G, rOneHot g ∉ Set.range (regInit rIdx).wires := by
        intro g ⟨i, hi⟩
        exact hne i.castSucc g hi.symm
      have hγ_last : writeReg β (regInit rIdx) f_init (rIdx (Fin.last m)) =
          β (rIdx (Fin.last m)) :=
        writeReg_apply_of_not_mem _ _ _ _ hlast_not_init
      have hγ_sum :
          (∑ g : Fin G, if decide (g.val / 2 ^ m % 2 = 1) then
              writeReg β (regInit rIdx) f_init (rOneHot g) else 0) =
            ∑ g : Fin G, if decide (g.val / 2 ^ m % 2 = 1) then β (rOneHot g) else 0 := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [writeReg_apply_of_not_mem _ _ _ _ (hoh_not_init g)]
      rw [hγ_last, hγ_sum]
      funext w
      by_cases hw : w ∈ Set.range rIdx.wires
      · obtain ⟨idx, rfl⟩ := hw
        refine Fin.lastCases ?_ (fun i => ?_) idx
        · rw [Function.update_self, writeReg_apply_reg]; rfl
        · have hne_last : rIdx i.castSucc ≠ rIdx (Fin.last m) :=
            fun h => Fin.castSucc_ne_last i (rIdx.wires.injective h)
          rw [Function.update_of_ne hne_last, writeReg_apply_reg]
          exact writeReg_apply_reg β (regInit rIdx) _ i
      · have hw_ne_last : w ≠ rIdx (Fin.last m) := fun h => hw ⟨Fin.last m, h.symm⟩
        have hw_not_init : w ∉ Set.range (regInit rIdx).wires :=
          fun ⟨i, hi⟩ => hw ⟨i.castSucc, hi⟩
        rw [Function.update_of_ne hw_ne_last, writeReg_apply_of_not_mem _ _ _ _ hw_not_init,
          writeReg_apply_of_not_mem _ _ _ _ hw]
theorem DiagProjSimulates.tightenCongr {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P₁ P₂ : Operator (2 ^ n)} {U₁ U₂ : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (hd : DiagProjSimulates P₂ U₁ d)
    (hP₁ : IsDiagProj P₁) (hsub : P₁ * P₂ = P₁)
    (heq : U₁.1 * P₁ = U₂.1 * P₁) (hcomm₂ : U₂.1 * P₁ = P₁ * U₂.1) :
    DiagProjSimulates P₁ U₂ d := by
  have hsubR : P₂ * P₁ = P₁ := (hP₁.comm hd.1).symm.trans hsub
  have hadj : P₁ * U₁.1ᴴ = P₁ * U₂.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP₁.conjTranspose_eq] using
      congrArg Matrix.conjTranspose heq
  refine ⟨hP₁, hcomm₂, fun M => ?_⟩
  obtain ⟨M', hwp, hproj⟩ := hd.2.2 M
  refine ⟨M', hwp, ?_⟩
  calc P₁ * M'.1.1 * P₁
      = (P₁ * P₂) * M'.1.1 * (P₂ * P₁) := by rw [hsub, hsubR]
    _ = P₁ * (P₂ * M'.1.1 * P₂) * P₁ := by simp only [Matrix.mul_assoc]
    _ = P₁ * (P₂ * (U₁.1ᴴ * M.1.1 * U₁.1) * P₂) * P₁ := by rw [hproj]
    _ = ((P₁ * P₂) * U₁.1ᴴ) * M.1.1 * (U₁.1 * (P₂ * P₁)) := by simp only [Matrix.mul_assoc]
    _ = (P₁ * U₂.1ᴴ) * M.1.1 * (U₂.1 * P₁) := by rw [hsub, hsubR, hadj, heq]
    _ = P₁ * (U₂.1ᴴ * M.1.1 * U₂.1) * P₁ := by simp only [Matrix.mul_assoc]
/-- Zero-`T`, zero-`TOFF` CNOT fan-out XORing the active flag and binary index of `rOneHot` into
`wAct` and `rIdx`. -/
def fanoutActIdxCircuit {n : ℕ} (m G : ℕ) (wAct : Wire n) (rIdx : QRegister m n)
    (rOneHot : QRegister G n)
    (hOH_act : ∀ g : Fin G, rOneHot g ≠ wAct)
    (hOH_idx : ∀ i : Fin m, ∀ g : Fin G, rOneHot g ≠ rIdx i) : Circuit n :=
  xorRegToWireCircuit G rOneHot wAct hOH_act ;;ᶜ
    xorOneHotToIdxCircuit m G rIdx rOneHot hOH_idx
@[simp]
theorem count_fanoutActIdxCircuit_t {n : ℕ} (m G : ℕ) (wAct : Wire n) (rIdx : QRegister m n)
    (rOneHot : QRegister G n) (hOH_act : ∀ g : Fin G, rOneHot g ≠ wAct)
    (hOH_idx : ∀ i : Fin m, ∀ g : Fin G, rOneHot g ≠ rIdx i) :
    (fanoutActIdxCircuit m G wAct rIdx rOneHot hOH_act hOH_idx).count .T = 0 := by
  simp [fanoutActIdxCircuit]
@[simp]
theorem count_fanoutActIdxCircuit_toff {n : ℕ} (m G : ℕ) (wAct : Wire n) (rIdx : QRegister m n)
    (rOneHot : QRegister G n) (hOH_act : ∀ g : Fin G, rOneHot g ≠ wAct)
    (hOH_idx : ∀ i : Fin m, ∀ g : Fin G, rOneHot g ≠ rIdx i) :
    (fanoutActIdxCircuit m G wAct rIdx rOneHot hOH_act hOH_idx).count .TOFF = 0 := by
  simp [fanoutActIdxCircuit]
/-- Computational-basis bit-assignment produced by `fanoutActIdxCircuit` on `ket β`. -/
noncomputable def fanoutActIdxAssign {n : ℕ} (m G : ℕ) (wAct : Wire n) (rIdx : QRegister m n)
    (rOneHot : QRegister G n) (β : BitAssignment n) : BitAssignment n :=
  writeReg (Function.update β wAct (β wAct + ∑ g : Fin G, β (rOneHot g))) rIdx
    (fun i => β (rIdx i) +
      ∑ g : Fin G, if decide (g.val / 2 ^ i.val % 2 = 1) then β (rOneHot g) else 0)
theorem ket_fanoutActIdxCircuit {n : ℕ} (m G : ℕ) (wAct : Wire n) (rIdx : QRegister m n)
    (rOneHot : QRegister G n) (hOH_act : ∀ g : Fin G, rOneHot g ≠ wAct)
    (hOH_idx : ∀ i : Fin m, ∀ g : Fin G, rOneHot g ≠ rIdx i)
    (hActIdx : ∀ i : Fin m, wAct ≠ rIdx i) (β : BitAssignment n) :
    (fanoutActIdxCircuit m G wAct rIdx rOneHot hOH_act hOH_idx).eval.1.mulVec (ket β) =
      ket (fanoutActIdxAssign m G wAct rIdx rOneHot β) := by
  dsimp only [fanoutActIdxCircuit]
  rw [eval_seq_mulVec]
  have h1 : (xorRegToWireCircuit G rOneHot wAct hOH_act).eval.1.mulVec (ket β) =
      ket (Function.update β wAct (β wAct + ∑ g : Fin G, β (rOneHot g))) := by
    simpa using ket_xorFilteredRegToWireCircuit G (fun _ => true) rOneHot wAct hOH_act β
  rw [h1, ket_xorOneHotToIdxCircuit]
  congr 1; dsimp only [fanoutActIdxAssign]; congr 1; funext i
  rw [Function.update_of_ne (hActIdx i).symm]
  congr 1; refine Finset.sum_congr rfl fun g _ => ?_
  rw [Function.update_of_ne (hOH_act g)]
/-- `10`-bit-controlled Stage 2 branch family on `L.rSpin` (`N = 58`). -/
noncomputable abbrev phase2Ctrl10Branch : Fin (2 ^ 10) → Unitary (2 ^ 58) :=
  fun c10 =>
    OneHotMux.oneHotActiveLac2BranchUnitary OneHotMux.h58_gt_1 OneHotMux.h160_ge_1
      UnsignedGivens.p450Split160Lac2Table actIdx10 selPair10 subIdx10 c10
theorem localIdx_congr {k n : ℕ} (r : QRegister k n) {β₁ β₂ : BitAssignment n}
    (h : ∀ i : Fin k, β₁ (r i) = β₂ (r i)) :
    UnsignedGivens.localIdx r β₁ = UnsignedGivens.localIdx r β₂ :=
  congrArg (fun f : BitAssignment k => (basisBits k).symm f) (funext h)
end Lac2Fused184Select

namespace CompactStepFast176Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
/-- Pure `ℕ` decoding of `pair8` (`f10 2..9`) on `f10 : Fin 10 → Bool`. -/
def pair8NatOf10 (f10 : Fin 10 → Bool) : ℕ :=
  (if f10 2 then 1 else 0) + 2 * (if f10 3 then 1 else 0) +
    4 * (if f10 4 then 1 else 0) + 8 * (if f10 5 then 1 else 0) +
    16 * (if f10 6 then 1 else 0) + 32 * (if f10 7 then 1 else 0) +
    64 * (if f10 8 then 1 else 0) + 128 * (if f10 9 then 1 else 0)
/-- Packs `(xo', so, b, si, neg)` into a `16`-bit router control word `Fin 16 → Bool`. -/
def pack16 (xo' : Fin 256) (so : Bool) (b : Fin 32) (si neg : Bool) : Fin 16 → Bool :=
  fun k ↦
    if k.val < 8 then decide (xo'.val / 2 ^ k.val % 2 = 1)
    else if k.val = 8 then so
    else if k.val < 14 then decide (b.val / 2 ^ (k.val - 9) % 2 = 1)
    else if k.val = 14 then si
    else neg
/-- Remaining active wire count `off + (m - (off + kZero))` (`rfl`-identical to
`Cat11CompactPhase2Bridge.blockRemWidth`). -/
abbrev blockRemWidth (m off kZero : ℕ) : ℕ :=
  off + (m - (off + kZero))
/-- Remaining active outer width `(8 + wOuter + 1) - kZeroOut` (`rfl`-compatible with walk bridges).
-/
abbrev outRemWidth (wOuter kZeroOut : ℕ) : ℕ :=
  blockRemWidth (mOutUB wOuter) 8 kZeroOut
/-- Remaining active `mid` width `5 + (wInner2 - kZeroMid + 1)` (`rfl`-identical to
`Cat11CompactPhase2Bridge.midRemWidth`). -/
abbrev midRemWidth (wInner2 kZeroMid : ℕ) : ℕ :=
  blockRemWidth (mMidUB wInner2) 5 kZeroMid
/-- Combined active reflection control width (`rfl`-compatible with `MobiusOptSubcube163Walk`). -/
abbrev combARem (wOuter wInner2 kZeroOut kZeroMid : ℕ) : ℕ :=
  outRemWidth wOuter kZeroOut + midRemWidth wInner2 kZeroMid
namespace StepCore
/-- `2-T`, `0-TOFF` `W`-split primitive mapping `|0, 0⟩ ↦ |0, 0⟩` and
`|1, 0⟩ ↦ (|1, 0⟩ + |0, 1⟩) / √2` on distinct wires `(a, b)`. -/
def wSplitPair {n : ℕ} (a b : Wire n) (h : a ≠ b) : Circuit n :=
  Circuit.S b ;;ᶜ Circuit.H b ;;ᶜ Circuit.T b ;;ᶜ
  Circuit.CNOT a b h ;;ᶜ
  Circuit.Z b ;;ᶜ Circuit.S b ;;ᶜ Circuit.T b ;;ᶜ
  Circuit.H b ;;ᶜ Circuit.Z b ;;ᶜ Circuit.S b ;;ᶜ
  Circuit.CNOT b a h.symm
@[simp] theorem count_wSplitPair_toff {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (wSplitPair a b h).count .TOFF = 0 := rfl
@[simp] theorem count_wSplitPair_t {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (wSplitPair a b h).count .T = 2 := rfl
/-- Insert a `0` bit at position `d < 5` into `s < 16` (`s % 2^d + 2^(d+1) * (s / 2^d) < 32`). -/
def insertZeroBit (d : Fin 5) (s : Fin 16) : Fin 32 :=
  ⟨s.val % 2 ^ d.val + 2 ^ (d.val + 1) * (s.val / 2 ^ d.val), by
    fin_cases d <;> (have := s.isLt; dsimp; omega)⟩
/-- Set bit `d < 5` to `1` on `insertZeroBit d s`. -/
def insertOneBit (d : Fin 5) (s : Fin 16) : Fin 32 :=
  ⟨(insertZeroBit d s).val + 2 ^ d.val, by
    fin_cases d <;> (have := s.isLt; dsimp [insertZeroBit]; omega)⟩
end StepCore
end CompactStepFast176Select

open CompactStepFast176Select CompactStepFast176Select.StepCore Lac2Fused184Select

namespace StepEncK
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge
/-- Operator acting on `ket β` as `f β` when `S β` holds and `0` otherwise. -/
noncomputable def ketMapOp {n : ℕ} (S : BitAssignment n → Prop)
    (f : BitAssignment n → (Fin (2 ^ n) → ℂ)) : Operator (2 ^ n) :=
  open Classical in
  Matrix.of fun i j ↦ if S (basisBits n j) then f (basisBits n j) i else 0
theorem ketMapOp_mulVec_ket {n : ℕ} (S : BitAssignment n → Prop) [DecidablePred S]
    (f : BitAssignment n → (Fin (2 ^ n) → ℂ)) (β : BitAssignment n) :
    (ketMapOp S f).mulVec (XMeasCircuit.ket β) = if S β then f β else 0 := by
  classical
  ext i
  have h1 : (ketMapOp S f).mulVec (XMeasCircuit.ket β) i =
      ketMapOp S f i ((basisBits n).symm β) := by
    simp [QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.ket, basisState]
  rw [h1]
  simp only [ketMapOp, Matrix.of_apply, XMeasCircuit.basisBits_basisBitsEquiv_symm]
  split_ifs <;> simp
theorem ketMapOp_eq_ketPredProj {n : ℕ} (S : BitAssignment n → Prop) :
    ketMapOp S XMeasCircuit.ket = Lac2Fused184Select.ketPredProj S := by
  classical
  refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  have hk : OneHotSimulates.ket β = XMeasCircuit.ket β := rfl
  rw [ketMapOp_mulVec_ket, ← hk, Lac2Fused184Select.ketPredProj_mulVec_ket]
theorem mul_ketMapOp {n : ℕ} (A : Operator (2 ^ n)) (S : BitAssignment n → Prop)
    (f : BitAssignment n → (Fin (2 ^ n) → ℂ)) :
    A * ketMapOp S f = ketMapOp S (fun β ↦ A.mulVec (f β)) := by
  classical
  refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ketMapOp_mulVec_ket, ketMapOp_mulVec_ket]
  split_ifs <;> simp
theorem smul_ketMapOp {n : ℕ} (c : ℂ) (S : BitAssignment n → Prop)
    (f : BitAssignment n → (Fin (2 ^ n) → ℂ)) :
    c • ketMapOp S f = ketMapOp S (fun β ↦ c • f β) := by
  classical
  refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [Matrix.smul_mulVec, ketMapOp_mulVec_ket, ketMapOp_mulVec_ket]
  split_ifs <;> simp
theorem ketMapOp_congr {n : ℕ} {S : BitAssignment n → Prop}
    {f g : BitAssignment n → (Fin (2 ^ n) → ℂ)} (h : ∀ β, S β → f β = g β) :
    ketMapOp S f = ketMapOp S g := by
  classical
  refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [ketMapOp_mulVec_ket, ketMapOp_mulVec_ket]
  by_cases hS : S β
  · simp [hS, h β hS]
  · simp [hS]
/-- Backward-predicate QHL simulation relation `R₀ᴴ * M' * R₀ = R₁ᴴ * M * R₁`. -/
def SubspaceStepU {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (R₀ R₁ : Operator (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    R₀ᴴ * M'.1.1 * R₀ = R₁ᴴ * M.1.1 * R₁
theorem SubspaceStepU.congr {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₀ R₀' R₁ R₁' : Operator (2 ^ n)} {d : DynamicCircuit Var n}
    (h₀ : R₀ = R₀') (h₁ : R₁ = R₁') (h : SubspaceStepU R₀ R₁ d) :
    SubspaceStepU R₀' R₁' d := by
  subst h₀; subst h₁; exact h
theorem SubspaceStepU.mul_right {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₀ R₁ : Operator (2 ^ n)} {d : DynamicCircuit Var n} (A : Operator (2 ^ n))
    (h : SubspaceStepU R₀ R₁ d) :
    SubspaceStepU (R₀ * A) (R₁ * A) d := fun M ↦ by
  obtain ⟨M', hwp, heq⟩ := h M
  refine ⟨M', hwp, ?_⟩
  calc (R₀ * A)ᴴ * M'.1.1 * (R₀ * A)
      = Aᴴ * (R₀ᴴ * M'.1.1 * R₀) * A := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Aᴴ * (R₁ᴴ * M.1.1 * R₁) * A := by rw [heq]
    _ = (R₁ * A)ᴴ * M.1.1 * (R₁ * A) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
theorem SubspaceStepU.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₀ R₁ R₂ : Operator (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : SubspaceStepU R₀ R₁ d₁) (h₂ : SubspaceStepU R₁ R₂ d₂) :
    SubspaceStepU R₀ R₂ (.seq d₁ d₂) := fun M ↦ by
  obtain ⟨M₂, hwp₂, heq₂⟩ := h₂ M
  obtain ⟨M₁, hwp₁, heq₁⟩ := h₁ M₂
  refine ⟨M₁, ?_, heq₁.trans heq₂⟩
  rw [DynamicCircuit.compile_seq, wp_qSeq, hwp₂, hwp₁]
theorem SubspaceStepU.of_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₀ R₁ : Operator (2 ^ n)} (c : Circuit n) (hc : c.eval.1 * R₀ = R₁) :
    SubspaceStepU (Var := Var) R₀ R₁ (.circuit c) := fun M ↦ by
  refine ⟨qcQAssignObsMap c.eval M, ?_, ?_⟩
  · funext σ
    rw [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile (Var := Var),
      qcWpQAssign]
  · have hM : (qcQAssignObsMap c.eval M).1.1 = c.eval.1ᴴ * M.1.1 * c.eval.1 := by
      simp [qcQAssignObsMap, Matrix.star_eq_conjTranspose]
    have hadj : R₀ᴴ * c.eval.1ᴴ = R₁ᴴ := by
      simpa only [Matrix.conjTranspose_mul] using congrArg (·ᴴ) hc
    rw [hM]
    calc R₀ᴴ * (c.eval.1ᴴ * M.1.1 * c.eval.1) * R₀
        = (R₀ᴴ * c.eval.1ᴴ) * M.1.1 * (c.eval.1 * R₀) := by simp only [Matrix.mul_assoc]
      _ = R₁ᴴ * M.1.1 * R₁ := by rw [hadj, hc]
theorem SubspaceStepU.of_diagProjSimulates {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {P R₀ : Operator (2 ^ n)} {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hd : Lac2Fused184Select.DiagProjSimulates P U d) (hPR : P * R₀ = R₀) :
    SubspaceStepU R₀ (U.1 * R₀) d := fun M ↦ by
  obtain ⟨M', hwp, hproj⟩ := hd.2.2 M
  have hPherm : Pᴴ = P := hd.1.conjTranspose_eq
  have hadj : R₀ᴴ * P = R₀ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hPherm] using congrArg (·ᴴ) hPR
  refine ⟨M', hwp, ?_⟩
  have hproj' : P * M'.1.1 * P = P * (U.1ᴴ * M.1.1 * U.1) * P := hproj
  calc R₀ᴴ * M'.1.1 * R₀
      = (R₀ᴴ * P) * M'.1.1 * (P * R₀) := by rw [hadj, hPR]
    _ = R₀ᴴ * (P * M'.1.1 * P) * R₀ := by simp only [Matrix.mul_assoc]
    _ = R₀ᴴ * (P * (U.1ᴴ * M.1.1 * U.1) * P) * R₀ := by rw [hproj']
    _ = (R₀ᴴ * P) * U.1ᴴ * M.1.1 * U.1 * (P * R₀) := by simp only [Matrix.mul_assoc]
    _ = (U.1 * R₀)ᴴ * M.1.1 * (U.1 * R₀) := by
          rw [hadj, hPR, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
theorem SubspaceStepU.toDiagProjSimulates {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {P : Operator (2 ^ n)} {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hP : Lac2Fused184Select.IsDiagProj P) (hComm : U.1 * P = P * U.1)
    (hStep : SubspaceStepU P (U.1 * P) d) :
    Lac2Fused184Select.DiagProjSimulates P U d := by
  have hPherm : Pᴴ = P := hP.conjTranspose_eq
  refine ⟨hP, hComm, fun M ↦ ?_⟩
  obtain ⟨M', hwp, heq⟩ := hStep M
  refine ⟨M', hwp, ?_⟩
  calc P * M'.1.1 * P
      = Pᴴ * M'.1.1 * P := by rw [hPherm]
    _ = (U.1 * P)ᴴ * M.1.1 * (U.1 * P) := heq
    _ = P * (U.1ᴴ * M.1.1 * U.1) * P := by
          rw [Matrix.conjTranspose_mul, hPherm]; simp only [Matrix.mul_assoc]
theorem SubspaceStepU.remeasure {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₀ R₁ : Operator (2 ^ n)} (v : Var) (q : Wire n) (onOne : DynamicCircuit Var n)
    (h0 : (QRegister.singleton q).basisOutcomeProjector 0 * R₀ = XMeasCircuit.sqrtHalf • R₁)
    (h1 : SubspaceStepU ((QRegister.singleton q).basisOutcomeProjector 1 * R₀)
      (XMeasCircuit.sqrtHalf • R₁) onOne) :
    SubspaceStepU R₀ R₁ (XMeasCircuit.remeasureIfDyn v q onOne) := fun M ↦ by
  obtain ⟨M₁, hwp₁, heq₁⟩ := h1 M
  let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton q).basisOutcomeProjector 1
  let d := XMeasCircuit.remeasureIfDyn v q onOne
  let σ₀ : Store Var := fun _ ↦ 0
  let M' : Observable (Fin (2 ^ n)) := wp d.compile (fun _ ↦ M) σ₀
  have hval (σ : Store Var) :
      (wp d.compile (fun _ ↦ M) σ).1 = M.1.conj P₀ + M₁.1.conj P₁ := by
    rw [XMeasCircuit.wp_remeasureIfDyn_apply, hwp₁]
  refine ⟨M', ?_, ?_⟩
  · funext σ; apply Subtype.ext; exact (hval σ).trans (hval σ₀).symm
  · have hM' : M'.1.1 = P₀ * M.1.1 * P₀ᴴ + P₁ * M₁.1.1 * P₁ᴴ := by
      change (wp d.compile (fun _ ↦ M) σ₀).1.1 = _
      rw [hval σ₀]; rfl
    have hP₀h : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
    have hP₁h : P₁ᴴ = P₁ := QRegister.basisOutcomeProjector_conjTranspose _ 1
    have h0Eq : (P₀ * R₀)ᴴ * M.1.1 * (P₀ * R₀) =
        (XMeasCircuit.sqrtHalf • R₁)ᴴ * M.1.1 * (XMeasCircuit.sqrtHalf • R₁) := by rw [h0]
    have hsum : R₀ᴴ * M'.1.1 * R₀ =
        (P₀ * R₀)ᴴ * M.1.1 * (P₀ * R₀) + (P₁ * R₀)ᴴ * M₁.1.1 * (P₁ * R₀) := by
      rw [hM', hP₀h, hP₁h, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.conjTranspose_mul, hP₀h, hP₁h, Matrix.mul_assoc]
    rw [hsum, h0Eq, heq₁]
    simp only [Matrix.conjTranspose_smul, XMeasCircuit.star_sqrtHalf, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← add_smul, XMeasCircuit.sqrtHalf_mul_sqrtHalf]
    norm_num
theorem SubspaceStepU.xMeasUnload_circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {R₁ : Operator (2 ^ n)} (v : Var) (q : Wire n)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β b, f (Function.update β q b) = f β)
    (cFix : Circuit n) (hcFix : cFix.eval = XMeasCircuit.phaseFlipUnitary f)
    (hClean : XMeasCircuit.cleanFinsetProj {q} * R₁ = R₁) :
    SubspaceStepU ((XMeasCircuit.xorWireUnitary q f hf).1 * R₁) R₁
      (XMeasCircuit.xMeasUnloadWireDyn v q (.circuit cFix)) := by
  let Uxor := (XMeasCircuit.xorWireUnitary q f hf).1
  let Hq := (Circuit.H q).eval.1
  let Xq := (Circuit.X q).eval.1
  let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton q).basisOutcomeProjector 1
  have hmem : q ∈ ({q} : Finset (Wire n)) := Finset.mem_singleton_self q
  refine SubspaceStepU.seq (SubspaceStepU.of_circuit (Var := Var) (Circuit.H q) rfl)
    (SubspaceStepU.remeasure v q _ ?_ ?_)
  · calc P₀ * (Hq * (Uxor * R₁))
        = ((P₀ * Hq) * Uxor * XMeasCircuit.cleanFinsetProj {q}) * R₁ := by
            nth_rw 1 [← hClean]; simp only [Matrix.mul_assoc]
      _ = (XMeasCircuit.sqrtHalf • XMeasCircuit.cleanFinsetProj {q}) * R₁ := by
            rw [XMeasCircuit.xMeas_kraus_zero q {q} hmem f hf]
      _ = XMeasCircuit.sqrtHalf • R₁ := by rw [Matrix.smul_mul, hClean]
  · refine SubspaceStepU.seq (SubspaceStepU.of_circuit (Var := Var) (Circuit.X q) rfl)
      (SubspaceStepU.of_circuit (Var := Var) cFix ?_)
    have hkr1 : (Xq * P₁ * Hq) * Uxor * XMeasCircuit.cleanFinsetProj {q} =
        XMeasCircuit.sqrtHalf • (XMeasCircuit.cleanFinsetProj {q} *
          (XMeasCircuit.phaseFlipUnitary f).1) :=
      XMeasCircuit.xMeas_kraus_one q {q} hmem f hf
    have hsq : (XMeasCircuit.phaseFlipUnitary f).1 * (XMeasCircuit.phaseFlipUnitary f).1 = 1 :=
      congrArg Subtype.val (XMeasCircuit.phaseFlipUnitary_mul_self f)
    calc cFix.eval.1 * (Xq * (P₁ * (Hq * (Uxor * R₁))))
        = cFix.eval.1 * (((Xq * P₁ * Hq) * Uxor * XMeasCircuit.cleanFinsetProj {q}) * R₁) := by
            nth_rw 1 [← hClean]; simp only [Matrix.mul_assoc]
      _ = (XMeasCircuit.phaseFlipUnitary f).1 *
            ((XMeasCircuit.sqrtHalf • (XMeasCircuit.cleanFinsetProj {q} *
              (XMeasCircuit.phaseFlipUnitary f).1)) * R₁) := by rw [hcFix, hkr1]
      _ = QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.sqrtHalf •
            (((XMeasCircuit.phaseFlipUnitary f).1 *
              (XMeasCircuit.cleanFinsetProj {q} * (XMeasCircuit.phaseFlipUnitary f).1)) * R₁) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
      _ = XMeasCircuit.sqrtHalf • R₁ := by
            rw [← Matrix.mul_assoc (XMeasCircuit.phaseFlipUnitary f).1,
              XMeasCircuit.phaseFlipUnitary_comm_cleanFinsetProj f {q},
              Matrix.mul_assoc (XMeasCircuit.cleanFinsetProj {q}), hsq, Matrix.mul_one, hClean]
theorem SubspaceStepU.of_andCompute {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {R₀ : Operator (2 ^ n)} (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hClean : (QRegister.singleton anc).basisOutcomeProjector 0 * R₀ = R₀) :
    SubspaceStepU (Var := Var) R₀ ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * R₀)
      (.circuit (Circuit.andCompute c₁ c₂ anc h₁a h₂a)) := fun M ↦ by
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  have hPherm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hadj : R₀ᴴ * P₀ = R₀ᴴ := by
    have hc : P₀ * R₀ = R₀ := hClean
    simpa only [Matrix.conjTranspose_mul, hPherm] using congrArg (·ᴴ) hc
  have hrest := congrArg (fun x : Observable (Fin (2 ^ n)) ↦ x.1)
    (congrFun (DynamicCircuit.qc_wp_qAssign_andCompute (Var := Var)
      c₁ c₂ anc h₁₂ h₁a h₂a (fun _ ↦ M)) (fun _ ↦ 0))
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose] at hrest
  refine ⟨qcQAssignObsMap (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval M, ?_, ?_⟩
  · funext σ
    rw [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile (Var := Var),
      qcWpQAssign]
  · generalize (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval = U₁,
      (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval = U₂ at hrest ⊢
    have hmat : P₀ * (U₁.1ᴴ * M.1.1 * U₁.1) * P₀ = P₀ * (U₂.1ᴴ * M.1.1 * U₂.1) * P₀ := by
      have hv : (M.1.conj U₁.1ᴴ).conj P₀ = (M.1.conj U₂.1ᴴ).conj P₀ := hrest
      have hv1 := congrArg Subtype.val hv
      change P₀ * (U₁.1ᴴ * M.1.1 * U₁.1ᴴᴴ) * P₀ᴴ =
        P₀ * (U₂.1ᴴ * M.1.1 * U₂.1ᴴᴴ) * P₀ᴴ at hv1
      simpa only [Matrix.conjTranspose_conjTranspose, hPherm] using hv1
    have hM : (qcQAssignObsMap U₁ M).1.1 = U₁.1ᴴ * M.1.1 * U₁.1 := by
      simp [qcQAssignObsMap, Matrix.star_eq_conjTranspose]
    rw [hM]
    calc R₀ᴴ * (U₁.1ᴴ * M.1.1 * U₁.1) * R₀
        = (R₀ᴴ * P₀) * (U₁.1ᴴ * M.1.1 * U₁.1) * (P₀ * R₀) := by rw [hadj, hClean]
      _ = R₀ᴴ * (P₀ * (U₁.1ᴴ * M.1.1 * U₁.1) * P₀) * R₀ := by simp only [Matrix.mul_assoc]
      _ = R₀ᴴ * (P₀ * (U₂.1ᴴ * M.1.1 * U₂.1) * P₀) * R₀ := by rw [hmat]
      _ = (R₀ᴴ * P₀) * U₂.1ᴴ * M.1.1 * U₂.1 * (P₀ * R₀) := by simp only [Matrix.mul_assoc]
      _ = (U₂.1 * R₀)ᴴ * M.1.1 * (U₂.1 * R₀) := by
            rw [hadj, hClean, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
theorem ket_CNOT {n : ℕ} (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (XMeasCircuit.ket β) =
      XMeasCircuit.ket (Function.update β t (β t + β c)) :=
  CircuitModular.UnsignedGivens.evolve_CNOT_ket c t h β
theorem ket_TOFF {n : ℕ} (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) (β : BitAssignment n) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (XMeasCircuit.ket β) =
      XMeasCircuit.ket (Function.update β t (β t + β c₁ * β c₂)) :=
  CircuitModular.UnsignedGivens.evolve_TOFF_ket c₁ c₂ t h₁₂ h₁t h₂t β
theorem eval_seq_mulVec {n : ℕ} (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (c₁ ;;ᶜ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
theorem czCircuit_eval_eq_phaseFlip {n : ℕ} (w₁ w₂ : Wire n) (h : w₁ ≠ w₂) :
    (SelectSwapQROM.czCircuit w₁ w₂ h).eval =
      XMeasCircuit.phaseFlipUnitary (fun β ↦ β w₁ * β w₂) := by
  apply Subtype.ext; refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
  have hket : SelectSwapQROM.ket β = XMeasCircuit.ket β := rfl
  have hbs : SelectSwapQROM.bitSign (β w₁ * β w₂) = XMeasCircuit.bitSign (β w₁ * β w₂) := by
    generalize β w₁ * β w₂ = x; fin_cases x <;> rfl
  rw [SelectSwapQROM.ket_czCircuit w₁ w₂ h β, hket, hbs,
    ← XMeasCircuit.phaseFlipUnitary_mulVec_ket (fun β ↦ β w₁ * β w₂) β]
theorem ite_posE {c : Prop} [Decidable c] (hc : c) {α : Sort*} {t e : α} :
    ite c t e = t := by simp [hc]
theorem ite_negE {c : Prop} [Decidable c] (hnc : ¬ c) {α : Sort*} {t e : α} :
    ite c t e = e := by simp [hnc]
theorem ket_cnotMaskReg {n : ℕ} (G : ℕ) (rSrc : QRegister G n) (dst : Wire n)
    (mask : Fin G → Bool) (hdisj : ∀ g, rSrc g ≠ dst) (β : BitAssignment n) :
    (UnsignedGivens.cnotMaskReg G rSrc dst mask hdisj).eval.1.mulVec (XMeasCircuit.ket β) =
      XMeasCircuit.ket (Function.update β dst (β dst + UnsignedGivens.maskSumBit rSrc mask β)) :=
  CircuitModular.UnsignedGivens.evolve_cnotMaskReg_ket G rSrc dst mask hdisj β
end StepEncK

namespace StepDecK
open StepEncK
theorem embed_muxCtrl_comm_ketPredProj {n kSc kC : ℕ}
    (rSC : QRegister kSc n) (rCtrl : QRegister kC n) (hCtrl2 : rSC.DisjointWires rCtrl)
    (W : Fin (2 ^ kC) → Unitary (2 ^ kSc)) (S : BitAssignment n → Prop)
    (hSWr : ∀ (β : BitAssignment n) (l : Fin (2 ^ kSc)),
      S (CircuitModular.UnsignedGivens.writeReg β rSC (basisBits kSc l)) ↔ S β) :
    let U := (rSC.concat rCtrl hCtrl2).embedUnitary (CircuitModular.UnsignedGivens.muxCtrlUnitary W)
    U.1 * Lac2Fused184Select.ketPredProj S =
      Lac2Fused184Select.ketPredProj S * U.1 := by
  classical
  intro U
  have hketEq : ∀ γ : BitAssignment n, UnsignedGivens.ket γ = OneHotSimulates.ket γ := fun _ ↦ rfl
  apply OneHotSimulates.matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Lac2Fused184Select.ketPredProj_mulVec_ket]
  dsimp only [U]
  by_cases hS : S β
  · simp only [hS, ↓reduceIte]
    simp_rw [← hketEq]
    rw [UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket, QRegister.embedUnitary_val,
      CircuitModular.UnsignedGivens.embedMatrix_mulVec_ket, Matrix.mulVec_sum]
    simp_rw [hketEq]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Matrix.mulVec_smul]; congr 1; symm
    rw [Lac2Fused184Select.ketPredProj_mulVec_ket, ite_posE ((hSWr β l).mpr hS)]
  · simp only [hS, ↓reduceIte, Matrix.mulVec_zero]
    simp_rw [← hketEq]
    rw [UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket, QRegister.embedUnitary_val,
      CircuitModular.UnsignedGivens.embedMatrix_mulVec_ket, Matrix.mulVec_sum]
    simp_rw [hketEq]; symm
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    rw [Matrix.mulVec_smul, Lac2Fused184Select.ketPredProj_mulVec_ket,
      ite_negE (mt (hSWr β l).mp hS), smul_zero]
end StepDecK

namespace CompactOuter9Bound50Core
open StepEncK StepDecK
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
theorem bitsToNat_pair8_eq_pair8NatOf10_b (f10 : Fin 10 → Bool) :
    OneHotSimulates.bitsToNat (fun i : Fin 8 ↦ if f10 ⟨i.val + 2, by omega⟩ then (1 : ZMod 2) else
      0) =
      pair8NatOf10 f10 := by
  have hb (b : Bool) : (if b then (1 : ZMod 2) else 0).val = if b then 1 else 0 := by
    cases b <;> rfl
  dsimp only [OneHotSimulates.bitsToNat]
  simp only [hb]
  change 0 + 2 ^ 0 * (if f10 2 then 1 else 0) + 2 ^ 1 * (if f10 3 then 1 else 0) +
      2 ^ 2 * (if f10 4 then 1 else 0) + 2 ^ 3 * (if f10 5 then 1 else 0) +
      2 ^ 4 * (if f10 6 then 1 else 0) + 2 ^ 5 * (if f10 7 then 1 else 0) +
      2 ^ 6 * (if f10 8 then 1 else 0) + 2 ^ 7 * (if f10 9 then 1 else 0) =
    pair8NatOf10 f10
  dsimp only [pair8NatOf10]
  ring
theorem bitsOfFin_eq_div_mod_b {w : ℕ} (v : Fin (2 ^ w)) (i : Fin w) :
    bitsOfFin w v i = decide (v.val / 2 ^ i.val % 2 = 1) := by
  change decide (basisBits w v i = 1) = _
  rw [basisBits_eq_testBit, Nat.testBit_eq_decide_div_mod_eq]
  cases h : v.val / 2 ^ i.val % 2 == 1
  · simp only [beq_eq_false_iff_ne] at h; simp [h]
  · simp only [beq_iff_eq] at h; simp [h]
theorem ite_negOneUnitary_mul_b (n : ℕ) (p q : Bool) :
    (if p then negOneUnitary n else 1) * (if q then negOneUnitary n else 1) =
      if xor p q then negOneUnitary n else 1 := by
  apply Subtype.ext; cases p <;> cases q <;> simp [Submonoid.coe_mul, negOneUnitary_val]
theorem unitary_self_inv_b {d : ℕ} {U : Unitary d} (h : U * U = 1) : U⁻¹ = U :=
  (eq_inv_of_mul_eq_one_left h).symm
/-- `10`-wire Stage-2 control map inside `rRouter17 : QRegister (1 + 16) N`:
`[B0, XO7, B1, B2, B3, B4, U3, U4, U5, W0] = [10, 8, 11, 12, 13, 14, 5, 6, 7, 0]`. -/
def routed10Wire17 : Fin 10 → Wire (1 + 16)
  | 0 => 10 | 1 => 8 | 2 => 11 | 3 => 12 | 4 => 13
  | 5 => 14 | 6 => 5 | 7 => 6 | 8 => 7 | _ => 0
/-- `10`-wire Stage-2 control subregister inside `1 + 16`. -/
def routed10Sub17 : QRegister 10 (1 + 16) :=
  ⟨⟨routed10Wire17, by decide⟩⟩
/-- Overwrites the wires of `r` in bit assignment `β` with `γ`. -/
noncomputable def writeRegBitsBound50 {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBits n).symm β) ((basisBits k).symm γ))
@[simp]
theorem writeRegBitsBound50_apply_reg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeRegBitsBound50 β r γ (r i) = γ i := by
  simp [writeRegBitsBound50, QRegister.basisBits_replaceIndex_apply]
theorem writeRegBitsBound50_apply_of_not_mem {n k : ℕ} (β : BitAssignment n)
    (r : QRegister k n) (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeRegBitsBound50 β r γ w = β w := by
  simp [writeRegBitsBound50, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
theorem embedMatrix_mulVec_ket_bound50 {n k : ℕ} (r : QRegister k n)
    (A : Operator (2 ^ k)) (β : BitAssignment n) :
    (r.embedMatrix A) *ᵥ CoherentAlias.ket β =
      ∑ l : Fin (2 ^ k),
        A l ((basisBits k).symm (fun i ↦ β (r i))) •
          CoherentAlias.ket (writeRegBitsBound50 β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBits n).symm β) =
      (basisBits k).symm (fun i ↦ β (r i)) := by simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A *ᵥ (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [CoherentAlias.ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeRegBitsBound50, CoherentAlias.ket, basisState]
theorem localIdx_congr_bound50 {n k : ℕ} (r : QRegister k n) {β₁ β₂ : BitAssignment n}
    (h : ∀ i : Fin k, β₁ (r i) = β₂ (r i)) :
    UnsignedGivens.localIdx r β₁ = UnsignedGivens.localIdx r β₂ := by
  apply (basisBits k).injective; funext i
  simp [UnsignedGivens.localIdx, h i]
theorem pack16_eq_self_bound50 (x : Fin 16 → Bool) :
    pack16 (finOfBits 8 fun i ↦ x ⟨i.val, by omega⟩) (x 8)
      (finOfBits 5 fun i ↦ x ⟨9 + i.val, by omega⟩) (x 14) (x 15) = x := by
  funext k; dsimp only [pack16]
  by_cases hk8 : k.val < 8
  · rw [ite_eq_left hk8, ← bitsOfFin_eq_div_mod_b _ ⟨k.val, hk8⟩, bitsOfFin_finOfBits]
  · by_cases hkEq8 : k.val = 8
    · rw [ite_eq_right hk8, ite_eq_left hkEq8]; exact congrArg x (Fin.ext hkEq8.symm)
    · by_cases hk14 : k.val < 14
      · rw [ite_eq_right hk8, ite_eq_right hkEq8, ite_eq_left hk14,
          ← bitsOfFin_eq_div_mod_b _ ⟨k.val - 9, by omega⟩, bitsOfFin_finOfBits]
        exact congrArg x (Fin.ext (by dsimp; omega))
      · by_cases hkEq14 : k.val = 14
        · rw [ite_eq_right hk8, ite_eq_right hkEq8, ite_eq_right hk14, ite_eq_left hkEq14]
          exact congrArg x (Fin.ext hkEq14.symm)
        · rw [ite_eq_right hk8, ite_eq_right hkEq8, ite_eq_right hk14, ite_eq_right hkEq14]
          exact congrArg x (Fin.ext (by have := k.isLt; dsimp; omega))
end CompactOuter9Bound50Core

namespace PolymorphicFused184Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
/-- Polymorphic `16`-wire control subregister `(xo : 8, so : 1, b : 5, si : 1, wNegIn : 1)` inside
`mAncUB wOuter wInner2` for arbitrary `(wOuter, wInner2 : ℕ)` and inner-sign payload wire `wNegIn :
Wire wInner2`. -/
def selPolyCtrl16 (wOuter wInner2 : ℕ) (wNegIn : Wire wInner2) : QRegister (15 + 1)
    (mAncUB wOuter wInner2) :=
  (selCtrlInAnc wOuter wInner2).concat
    (QRegister.singleton
      ⟨mOutUB wOuter + 5 + wNegIn.val, by have := wNegIn.isLt; dsimp [mAncUB, mMidUB]; omega⟩)
    (by
      rw [QRegister.disjoint_iff]; intro i j h; fin_cases j
      have hv := congrArg Fin.val h
      have hw := wNegIn.isLt
      rcases selCtrlInAnc_val_cases (w_go := wOuter) (w_gi := wInner2) i with h1 | h2 | h3 | h4 <;>
        (dsimp [mOutUB] at *; omega))
/-- `16`-wire control subregister inside `nUB wOuter wInner2 + 11`. -/
def rPolyCtrl16InCat (wOuter wInner2 : ℕ) (wNegIn : Wire wInner2) :
    QRegister (15 + 1) (nUB wOuter wInner2 + 11) :=
  (rAllInCat wOuter wInner2 11).compose (selPolyCtrl16 wOuter wInner2 wNegIn)
/-- Inner-ancilla `mMidUB wInner2`-wire block `[mOutUB wOuter .. mOutUB wOuter + mMidUB wInner2)`
inside
`mAncUB wOuter wInner2`. -/
def bMidPolyInAnc (wOuter wInner2 : ℕ) : QRegister (mMidUB wInner2) (mAncUB wOuter wInner2) :=
  QRegister.block (mOutUB wOuter) (mMidUB wInner2) (by dsimp [mAncUB]; omega)
end PolymorphicFused184Select

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open CircuitModular GivensOps
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation

namespace CompactStepFast176Select
namespace UnsignedGivens
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensOps
/-- Reconstructs bit `0` of a one-hot `(G' + 1)`-vector from its `G'`-tail via `1 + ∑ hbits'`. -/
def extendHot0 {G' : ℕ} (hbits' : Fin G' → ZMod 2) : Fin (G' + 1) → ZMod 2 :=
  Fin.cases (1 + ∑ g : Fin G', hbits' g) hbits'
theorem isOneHotBits_extendHot0_of_zero {G' : ℕ} {hbits' : Fin G' → ZMod 2}
    (hz : ∀ g : Fin G', hbits' g = 0) :
    IsOneHotBits 0 (extendHot0 hbits') := by
  refine ⟨?_, fun k hk => ?_⟩
  · simp [extendHot0, hz]
  · cases k using Fin.cases with
    | zero => exact absurd rfl hk
    | succ g => simp [extendHot0, hz g]
theorem isOneHotBits_extendHot0_of_succ {G' : ℕ} {g₀ : Fin G'} {hbits' : Fin G' → ZMod 2}
    (h : IsOneHotBits g₀ hbits') :
    IsOneHotBits g₀.succ (extendHot0 hbits') := by
  have hsum : (∑ g : Fin G', hbits' g) = 1 := by
    rw [Finset.sum_eq_single g₀ (fun g _ hne => h.2 g hne)
      (fun hg => absurd (Finset.mem_univ g₀) hg), h.1]
  refine ⟨by simp [extendHot0, h.1], fun k hk => ?_⟩
  cases k using Fin.cases with
  | zero => simp [extendHot0, hsum, zmod2_add_self]
  | succ g =>
      have hne : g ≠ g₀ := fun heq => hk (congrArg Fin.succ heq)
      simp [extendHot0, h.2 g hne]
theorem atMostOneHot_extendHot0 {G' : ℕ} {hbits' : Fin G' → ZMod 2}
    (h : AtMostOneHotBits hbits') :
    AtMostOneHotBits (extendHot0 hbits') := by
  by_cases hall : ∀ g : Fin G', hbits' g = 0
  · exact (isOneHotBits_extendHot0_of_zero hall).atMostOneHot
  · push Not at hall
    obtain ⟨g₀, hg₀⟩ := hall
    have hg1 : hbits' g₀ = 1 := by
      rcases zmod2_eq_zero_or_one (hbits' g₀) with h0 | h1
      · exact absurd h0 hg₀
      · exact h1
    have hoh : IsOneHotBits g₀ hbits' := ⟨hg1, fun g hne => by
      rcases h g₀ g hne.symm with h0 | h0
      · exact absurd h0 hg₀
      · exact h0⟩
    exact (isOneHotBits_extendHot0_of_succ hoh).atMostOneHot
/-- Conditional `X` gate (`0 T`, `0 TOFF`). -/
def condX {n : ℕ} (c0 : Bool) (q : Wire n) : Circuit n :=
  if c0 then Circuit.X q else .identity
@[simp] theorem count_condX_t {n : ℕ} (c0 : Bool) (q : Wire n) :
    (condX c0 q).count .T = 0 := by
  cases c0 <;> simp [condX]
@[simp] theorem count_condX_toff {n : ℕ} (c0 : Bool) (q : Wire n) :
    (condX c0 q).count .TOFF = 0 := by
  cases c0 <;> simp [condX]
theorem support_condX_subset {n : ℕ} (c0 : Bool) (q : Wire n) :
    (condX c0 q).support ⊆ {q} := by
  cases c0 <;> simp [condX]
theorem evolve_condX_ket {n : ℕ} (c0 : Bool) (q : Wire n) (β : BitAssignment n) :
    (condX c0 q).eval.1.mulVec (ket β) =
      ket (Function.update β q (β q + if c0 then 1 else 0)) := by
  cases c0
  · change Circuit.identity.eval.1.mulVec (ket β) = _
    rw [eval_identity_mulVec]
    simp
  · change (Circuit.X q).eval.1.mulVec (ket β) = _
    rw [evolve_X_ket]
    simp
/-- Affine masked fan-in `CNOT` + `condX` (`0 T`, `0 TOFF`), reading `rHot'` of width `G'` to
evaluate any `(G' + 1)`-entry mask `m : Fin (G' + 1) → Bool` on `extendHot0`. -/
def affineMaskReg {n : ℕ} (G' : ℕ) (rHot' : QRegister G' n) (dst : Wire n)
    (m : Fin (G' + 1) → Bool) (hdisj : ∀ g, rHot' g ≠ dst) : Circuit n :=
  cnotMaskReg G' rHot' dst (fun g => xor (m g.succ) (m 0)) hdisj ;;ᶜ condX (m 0) dst
/-- Affine parity bit computed by `affineMaskReg` on `rHot'`. -/
noncomputable def affineMaskBit {n G' : ℕ} (rHot' : QRegister G' n)
    (m : Fin (G' + 1) → Bool) (β : BitAssignment n) : ZMod 2 :=
  maskSumBit rHot' (fun g => xor (m g.succ) (m 0)) β + if m 0 then 1 else 0
@[simp] theorem count_affineMaskReg_t {n : ℕ} (G' : ℕ) (rHot' : QRegister G' n) (dst : Wire n)
    (m : Fin (G' + 1) → Bool) (hdisj : ∀ g, rHot' g ≠ dst) :
    (affineMaskReg G' rHot' dst m hdisj).count .T = 0 := by
  simp [affineMaskReg]
@[simp] theorem count_affineMaskReg_toff {n : ℕ} (G' : ℕ) (rHot' : QRegister G' n) (dst : Wire n)
    (m : Fin (G' + 1) → Bool) (hdisj : ∀ g, rHot' g ≠ dst) :
    (affineMaskReg G' rHot' dst m hdisj).count .TOFF = 0 := by
  simp [affineMaskReg]
theorem support_affineMaskReg_subset {n : ℕ} (G' : ℕ) (rHot' : QRegister G' n) (dst : Wire n)
    (m : Fin (G' + 1) → Bool) (hdisj : ∀ g, rHot' g ≠ dst) :
    (affineMaskReg G' rHot' dst m hdisj).support ⊆ insert dst rHot'.image := by
  intro q hq
  simp only [affineMaskReg, Circuit.support_seq, Finset.mem_union] at hq
  rcases hq with h1 | h2
  · exact support_cnotMaskReg_subset G' rHot' dst _ hdisj h1
  · have hx := support_condX_subset (m 0) dst h2
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact Finset.mem_insert_self dst _
theorem evolve_affineMaskReg_ket {n : ℕ} (G' : ℕ) (rHot' : QRegister G' n) (dst : Wire n)
    (m : Fin (G' + 1) → Bool) (hdisj : ∀ g, rHot' g ≠ dst) (β : BitAssignment n) :
    (affineMaskReg G' rHot' dst m hdisj).eval.1.mulVec (ket β) =
      ket (Function.update β dst (β dst + affineMaskBit rHot' m β)) := by
  rw [affineMaskReg, eval_seq_mulVec, evolve_cnotMaskReg_ket, evolve_condX_ket]
  apply congrArg ket; funext w
  by_cases hw : w = dst
  · subst hw; simp [affineMaskBit, add_assoc]
  · simp [Function.update_of_ne hw]
theorem affineMaskBit_update_of_ne {n G' : ℕ} (rHot' : QRegister G' n)
    (m : Fin (G' + 1) → Bool) (β : BitAssignment n) (w : Wire n)
    (hw : ∀ g, rHot' g ≠ w) (x : ZMod 2) :
    affineMaskBit rHot' m (Function.update β w x) = affineMaskBit rHot' m β := by
  unfold affineMaskBit maskSumBit
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Function.update_of_ne (hw g)]
theorem affineMaskBit_eq_maskBitSum_extendHot0 {n G' : ℕ} (rHot' : QRegister G' n)
    (m : Fin (G' + 1) → Bool) (β : BitAssignment n) :
    affineMaskBit rHot' m β = maskBitSum (extendHot0 (fun g => β (rHot' g))) m := by
  unfold affineMaskBit maskSumBit maskBitSum
  rw [Fin.sum_univ_succ]
  simp only [extendHot0, Fin.cases_zero, Fin.cases_succ]
  cases hm0 : m 0
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_add, Bool.xor_false]
  · simp only [↓reduceIte, Bool.xor_true]
    have hsplit : (∑ x : Fin G', if (!m x.succ) = true then β (rHot' x) else 0) =
        (∑ x : Fin G', β (rHot' x)) + ∑ x : Fin G', if m x.succ = true then β (rHot' x) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      cases m g.succ <;> simp [zmod2_add_self]
    rw [hsplit]
    ring
/-- Affine Rank-2 Bilinear `PhasedStep` (`4 T`, `0 TOFF`), evaluating `(G' + 1)`-row masks
`(b0, b1)` on `extendHot0` while reading only `rHot' : QRegister G' n`. -/
def affineBilinearBitStep {n : ℕ} (G' : ℕ) (u v : Wire n) (rHot' : QRegister G' n)
    (b0 b1 : Fin (G' + 1) → Bool) (anc : Wire n)
    (huv : u ≠ v) (hua : u ≠ anc) (hva : v ≠ anc)
    (hhu : ∀ g, rHot' g ≠ u) (hhv : ∀ g, rHot' g ≠ v) (hha : ∀ g, rHot' g ≠ anc) :
    PhasedStep n where
  c₁ := u
  c₂ := v
  anc := anc
  h₁₂ := huv
  h₁a := hua
  h₂a := hva
  pre := affineMaskReg G' rHot' u b1 hhu ;;ᶜ affineMaskReg G' rHot' v b0 hhv
  midPre := affineMaskReg G' rHot' v b0 hhv ;;ᶜ
              affineMaskReg G' rHot' u b1 hhu ;;ᶜ
              affineMaskReg G' rHot' anc (fun g => b0 g && b1 g) hha
  midPost := affineMaskReg G' rHot' anc (fun g => b0 g && b1 g) hha ;;ᶜ
               affineMaskReg G' rHot' u b1 hhu ;;ᶜ
               affineMaskReg G' rHot' v b0 hhv
  post := affineMaskReg G' rHot' v b0 hhv ;;ᶜ affineMaskReg G' rHot' u b1 hhu
/-- Affine Rank-2 Bilinear output bit computed by `affineBilinearBitStep`. -/
noncomputable def affineBilinearBitVal {n G' : ℕ} (u v : Wire n) (rHot' : QRegister G' n)
    (b0 b1 : Fin (G' + 1) → Bool) (β : BitAssignment n) : ZMod 2 :=
  (β u + affineMaskBit rHot' b1 β) * (β v + affineMaskBit rHot' b0 β) +
    affineMaskBit rHot' (fun g => b0 g && b1 g) β
theorem affineBilinearBitVal_eq_formula {n G' : ℕ} (u v : Wire n) (rHot' : QRegister G' n)
    (b0 b1 : Fin (G' + 1) → Bool) (β : BitAssignment n) :
    affineBilinearBitVal u v rHot' b0 b1 β =
      bilinearBitFormula (β u) (β v) (extendHot0 (fun g => β (rHot' g))) b0 b1 := by
  unfold affineBilinearBitVal bilinearBitFormula
  simp only [affineMaskBit_eq_maskBitSum_extendHot0]
theorem isCleanBitStep_affineBilinearBitStep {n : ℕ} (G' : ℕ) (u v : Wire n)
    (rHot' : QRegister G' n) (b0 b1 : Fin (G' + 1) → Bool) (anc : Wire n)
    (huv : u ≠ v) (hua : u ≠ anc) (hva : v ≠ anc)
    (hhu : ∀ g, rHot' g ≠ u) (hhv : ∀ g, rHot' g ≠ v) (hha : ∀ g, rHot' g ≠ anc) :
    IsCleanBitStep (affineBilinearBitStep G' u v rHot' b0 b1 anc huv hua hva hhu hhv hha)
      (affineBilinearBitVal u v rHot' b0 b1) (insert u (insert v rHot'.image)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [affineBilinearBitStep, PhasedStep.IsCliffordWrapper]
  · simp only [affineBilinearBitStep, Finset.mem_insert, QRegister.mem_image, not_or, not_exists]
    exact ⟨hua.symm, hva.symm, fun g hg => hha g hg⟩
  · intro hmem
    simp only [affineBilinearBitStep, Circuit.support_seq, Finset.mem_union] at hmem
    rcases hmem with h1 | h2
    · have hs := support_affineMaskReg_subset G' rHot' u b1 hhu h1
      simp only [Finset.mem_insert, QRegister.mem_image] at hs
      rcases hs with h | ⟨g, hg⟩
      · exact hua h.symm
      · exact hha g hg
    · have hs := support_affineMaskReg_subset G' rHot' v b0 hhv h2
      simp only [Finset.mem_insert, QRegister.mem_image] at hs
      rcases hs with h | ⟨g, hg⟩
      · exact hva h.symm
      · exact hha g hg
  · intro q hq
    simp only [affineBilinearBitStep, Circuit.support_seq, Finset.mem_union] at hq
    rcases hq with h1 | h2
    · have hs := support_affineMaskReg_subset G' rHot' u b1 hhu h1
      simp only [Finset.mem_insert, QRegister.mem_image] at hs ⊢
      tauto
    · have hs := support_affineMaskReg_subset G' rHot' v b0 hhv h2
      simp only [Finset.mem_insert, QRegister.mem_image] at hs ⊢
      tauto
  · simp [affineBilinearBitStep]
  · simp [affineBilinearBitStep]
  · intro q hq
    simp only [affineBilinearBitStep, Circuit.support_seq, Finset.mem_union] at hq
    rcases hq with h1 | (h2 | h3)
    · have hs := support_affineMaskReg_subset G' rHot' v b0 hhv h1
      simp only [Finset.mem_insert, QRegister.mem_image] at hs ⊢
      tauto
    · have hs := support_affineMaskReg_subset G' rHot' u b1 hhu h2
      simp only [Finset.mem_insert, QRegister.mem_image] at hs ⊢
      tauto
    · have hs := support_affineMaskReg_subset G' rHot' anc (fun g => b0 g && b1 g) hha h3
      simp only [Finset.mem_insert, QRegister.mem_image] at hs ⊢
      tauto
  · intro β
    let s := affineBilinearBitStep G' u v rHot' b0 b1 anc huv hua hva hhu hhv hha
    have hpre : s.pre = affineMaskReg G' rHot' u b1 hhu ;;ᶜ affineMaskReg G' rHot' v b0 hhv := rfl
    have hmidPre : s.midPre = affineMaskReg G' rHot' v b0 hhv ;;ᶜ
        affineMaskReg G' rHot' u b1 hhu ;;ᶜ
        affineMaskReg G' rHot' anc (fun g => b0 g && b1 g) hha := rfl
    have hs1 : s.c₁ = u := rfl
    have hs2 : s.c₂ = v := rfl
    have hsa : s.anc = anc := rfl
    rw [one_smul]
    simp only [eval_seq_mulVec]
    change s.midPre.eval.1.mulVec
        ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1.mulVec
          (s.pre.eval.1.mulVec (ket β))) = _
    rw [hpre, hmidPre]
    simp only [eval_seq_mulVec]
    rw [evolve_affineMaskReg_ket, evolve_affineMaskReg_ket, evolve_TOFF_ket, hs1, hs2, hsa,
      evolve_affineMaskReg_ket, evolve_affineMaskReg_ket, evolve_affineMaskReg_ket]
    apply congrArg ket
    simp only [affineMaskBit_update_of_ne _ _ _ u hhu, affineMaskBit_update_of_ne _ _ _ v hhv,
      affineMaskBit_update_of_ne _ _ _ anc hha, Function.update_of_ne huv,
      Function.update_of_ne huv.symm, Function.update_of_ne hua, Function.update_of_ne hva,
      Function.update_of_ne hua.symm, Function.update_of_ne hva.symm,
      Function.update_self, zmod2_add_cancel_right]
    funext w
    by_cases hwu : w = u
    · subst hwu; simp [Function.update_of_ne hua]
    · by_cases hwv : w = v
      · subst hwv; simp [Function.update_of_ne hva, Function.update_of_ne huv.symm]
      · by_cases hwa : w = anc
        · subst hwa; simp [affineBilinearBitVal, add_assoc]
        · simp [Function.update_of_ne hwa, Function.update_of_ne hwu, Function.update_of_ne hwv]
  · intro β
    let s := affineBilinearBitStep G' u v rHot' b0 b1 anc huv hua hva hhu hhv hha
    have hmidPost : s.midPost = affineMaskReg G' rHot' anc (fun g => b0 g && b1 g) hha ;;ᶜ
        affineMaskReg G' rHot' u b1 hhu ;;ᶜ affineMaskReg G' rHot' v b0 hhv := rfl
    have hpost : s.post = affineMaskReg G' rHot' v b0 hhv ;;ᶜ affineMaskReg G' rHot' u b1 hhu := rfl
    have hs1 : s.c₁ = u := rfl
    have hs2 : s.c₂ = v := rfl
    have hsa : s.anc = anc := rfl
    simp only [eval_seq_mulVec]
    change s.post.eval.1.mulVec
        ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1.mulVec
          (s.midPost.eval.1.mulVec (ket β))) = _
    rw [hmidPost, hpost]
    simp only [eval_seq_mulVec]
    rw [evolve_affineMaskReg_ket, evolve_affineMaskReg_ket, evolve_affineMaskReg_ket,
      evolve_TOFF_ket, hs1, hs2, hsa, evolve_affineMaskReg_ket, evolve_affineMaskReg_ket]
    apply congrArg ket
    simp only [affineMaskBit_update_of_ne _ _ _ u hhu, affineMaskBit_update_of_ne _ _ _ v hhv,
      affineMaskBit_update_of_ne _ _ _ anc hha, Function.update_of_ne huv,
      Function.update_of_ne huv.symm, Function.update_of_ne hua, Function.update_of_ne hva,
      Function.update_of_ne hua.symm, Function.update_of_ne hva.symm,
      Function.update_self, zmod2_add_cancel_right]
    funext w
    by_cases hwu : w = u
    · subst hwu; simp [Function.update_of_ne hua]
    · by_cases hwv : w = v
      · subst hwv; simp [Function.update_of_ne hva, Function.update_of_ne huv.symm]
      · by_cases hwa : w = anc
        · subst hwa
          simp only [Function.update_of_ne hua.symm, Function.update_of_ne hva.symm,
            Function.update_self, affineBilinearBitVal]
          ring
        · simp [Function.update_of_ne hwa, Function.update_of_ne hwu, Function.update_of_ne hwv]
  · intro β₁ β₂ h
    have hm_eq : ∀ m : Fin (G' + 1) → Bool,
        affineMaskBit rHot' m β₁ = affineMaskBit rHot' m β₂ := by
      intro m; unfold affineMaskBit maskSumBit
      congr 1
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [h (rHot' g) (by simp [QRegister.mem_image])]
    simp only [affineBilinearBitVal, h u (by simp), h v (by simp), hm_eq]
  · intro c_in φ_in f_in hperm hfa hfc
    let β_mp : BitAssignment n → BitAssignment n := fun β =>
      Function.update
        (Function.update
          (Function.update β v (β v + affineMaskBit rHot' b0 β))
          u (β u + affineMaskBit rHot' b1 β))
        anc (β anc + affineMaskBit rHot' (fun g => b0 g && b1 g) β)
    let f_b : BitAssignment n → BitAssignment n := fun β =>
      Function.update
        (Function.update
          (Function.update (f_in (β_mp β)) anc (β anc))
          u (β u))
        v (β v)
    refine ⟨fun β => φ_in (β_mp β), f_b, ?_, ?_, ?_, ?_⟩
    · intro β
      dsimp only [affineBilinearBitStep]
      simp only [eval_seq_mulVec]
      rw [evolve_affineMaskReg_ket, evolve_affineMaskReg_ket, evolve_affineMaskReg_ket]
      simp only [affineMaskBit_update_of_ne _ _ _ v hhv, affineMaskBit_update_of_ne _ _ _ u hhu,
        Function.update_of_ne huv, Function.update_of_ne hua.symm,
        Function.update_of_ne hva.symm]
      have hcin : c_in.eval.1.mulVec
          (ket (Function.update
            (Function.update (Function.update β v (β v + affineMaskBit rHot' b0 β))
              u (β u + affineMaskBit rHot' b1 β))
            anc (β anc + affineMaskBit rHot' (fun g => b0 g && b1 g) β))) =
          φ_in (β_mp β) • ket (f_in (β_mp β)) := hperm (β_mp β)
      rw [hcin]
      simp only [Matrix.mulVec_smul]
      congr 1
      rw [evolve_affineMaskReg_ket, evolve_affineMaskReg_ket, evolve_affineMaskReg_ket]
      apply congrArg ket
      have hhot_fix : ∀ m : Fin (G' + 1) → Bool,
          affineMaskBit rHot' m (f_in (β_mp β)) = affineMaskBit rHot' m β := by
        intro m; unfold affineMaskBit maskSumBit
        congr 1
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hfc (β_mp β) (rHot' g) (by simp [QRegister.mem_image])]
        dsimp [β_mp]
        rw [Function.update_of_ne (hha g), Function.update_of_ne (hhu g),
          Function.update_of_ne (hhv g)]
      simp only [affineMaskBit_update_of_ne _ _ _ anc hha, affineMaskBit_update_of_ne _ _ _ u hhu,
        hhot_fix]
      have hanc_eq : f_in (β_mp β) anc = β anc + affineMaskBit rHot' (fun g => b0 g && b1 g) β := by
        dsimp only [affineBilinearBitStep] at hfa
        rw [hfa (β_mp β)]; dsimp [β_mp]; simp
      have hu_eq : f_in (β_mp β) u = β u + affineMaskBit rHot' b1 β := by
        rw [hfc (β_mp β) u (by simp)]; dsimp [β_mp]
        rw [Function.update_of_ne hua, Function.update_self]
      have hv_eq : f_in (β_mp β) v = β v + affineMaskBit rHot' b0 β := by
        rw [hfc (β_mp β) v (by simp)]; dsimp [β_mp]
        rw [Function.update_of_ne hva, Function.update_of_ne huv.symm, Function.update_self]
      funext w
      by_cases hwv : w = v
      · subst hwv
        simp [f_b, Function.update_of_ne hva, Function.update_of_ne huv.symm, hv_eq,
          zmod2_add_cancel_right]
      · by_cases hwu : w = u
        · subst hwu
          simp [f_b, Function.update_of_ne huv, Function.update_of_ne hua, hu_eq,
            zmod2_add_cancel_right]
        · by_cases hwa : w = anc
          · subst hwa
            simp [f_b, Function.update_of_ne hva.symm, Function.update_of_ne hua.symm, hanc_eq,
              zmod2_add_cancel_right]
          · simp [f_b, Function.update_of_ne hwv, Function.update_of_ne hwu,
              Function.update_of_ne hwa]
    · intro β; dsimp [affineBilinearBitStep, f_b]
      rw [Function.update_of_ne huv, Function.update_self]
    · intro β; dsimp [affineBilinearBitStep, f_b]; rw [Function.update_self]
    · intro β; dsimp [affineBilinearBitStep, f_b]
      rw [Function.update_of_ne hva.symm, Function.update_of_ne hua.symm, Function.update_self]
theorem isCleanBitStep_affineBilinearFormula {n : ℕ} (G' : ℕ) (u v : Wire n)
    (rHot' : QRegister G' n) (b0 b1 : Fin (G' + 1) → Bool) (anc : Wire n)
    (huv : u ≠ v) (hua : u ≠ anc) (hva : v ≠ anc)
    (hhu : ∀ g, rHot' g ≠ u) (hhv : ∀ g, rHot' g ≠ v) (hha : ∀ g, rHot' g ≠ anc) :
    IsCleanBitStep (affineBilinearBitStep G' u v rHot' b0 b1 anc huv hua hva hhu hhv hha)
      (fun β => bilinearBitFormula (β u) (β v) (extendHot0 (fun g => β (rHot' g))) b0 b1)
      (insert u (insert v rHot'.image)) := by
  have heq : affineBilinearBitVal u v rHot' b0 b1 =
      fun β => bilinearBitFormula (β u) (β v) (extendHot0 (fun g => β (rHot' g))) b0 b1 :=
    funext (affineBilinearBitVal_eq_formula u v rHot' b0 b1)
  rw [← heq]
  exact isCleanBitStep_affineBilinearBitStep G' u v rHot' b0 b1 anc huv hua hva hhu hhv hha
/-- Effective `13`-bit unsigned integer produced on an affine non-apex plane at `(qc, c)`. -/
noncomputable def affinePlaneEffK {k_ctrl G' : ℕ} (row : Fin (G' + 1) → Bool → ℕ)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    (qc : ZMod 2) (c : Fin (2 ^ k_ctrl)) : ℕ :=
  let s_bit := basisBits k_ctrl c subIdx
  let hbits := extendHot0 (ctrlHotBits selHot' c)
  bilinearRowLo 11 row qc s_bit hbits +
    2 ^ 11 * bilinearRowBit 11 row qc s_bit hbits +
    2 ^ (11 + 1) * bilinearRowBit 12 row qc s_bit hbits
/-- Effective `13`-bit unsigned apex integer produced on an affine apex plane at `(qc, c)`. -/
noncomputable def affineApexEffK {k_ctrl G' : ℕ} (row0 : Fin (G' + 1) → Bool → ℕ)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    (qc : ZMod 2) (c : Fin (2 ^ k_ctrl)) : ℕ :=
  let s_bit := basisBits k_ctrl c subIdx
  let hbits := extendHot0 (ctrlHotBits selHot' c)
  bilinearRowLo 10 row0 qc s_bit hbits +
    2 ^ 10 * bilinearRowBit 10 row0 qc s_bit hbits +
    2 ^ (10 + 1) * bilinearRowBit 12 row0 qc s_bit hbits +
    2 ^ (10 + 1) * qc.val
theorem affinePlaneEffK_zero_of_atMostOneHot {k_ctrl G' : ℕ} (row : Fin (G' + 1) → Bool → ℕ)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) {c : Fin (2 ^ k_ctrl)}
    (h : AtMostOneHotBits (ctrlHotBits selHot' c)) :
    affinePlaneEffK row selHot' subIdx 0 c = 0 := by
  have hext := atMostOneHot_extendHot0 h
  dsimp only [affinePlaneEffK]
  rw [bilinearRowLo_zero_of_atMostOneHot _ _ _ hext,
    bilinearRowBit_zero_of_atMostOneHot _ _ _ hext,
    bilinearRowBit_zero_of_atMostOneHot _ _ _ hext]
  simp
theorem affinePlaneEffK_one_of_isOneHot {k_ctrl G' : ℕ} (row : Fin (G' + 1) → Bool → ℕ)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    {g₀ : Fin (G' + 1)} {c : Fin (2 ^ k_ctrl)}
    (h : IsOneHotBits g₀ (extendHot0 (ctrlHotBits selHot' c)))
    (hlt : row g₀ (decide (basisBits k_ctrl c subIdx = 1)) < 8192) :
    affinePlaneEffK row selHot' subIdx 1 c =
      row g₀ (decide (basisBits k_ctrl c subIdx = 1)) := by
  dsimp only [affinePlaneEffK]
  rw [bilinearRowLo_one_of_isOneHot _ _ _ h,
    bilinearRowBit_one_of_isOneHot _ _ _ h,
    bilinearRowBit_one_of_isOneHot _ _ _ h]
  exact nat_decomp_13bit hlt
theorem affineApexEffK_zero_of_atMostOneHot {k_ctrl G' : ℕ} (row0 : Fin (G' + 1) → Bool → ℕ)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) {c : Fin (2 ^ k_ctrl)}
    (h : AtMostOneHotBits (ctrlHotBits selHot' c)) :
    affineApexEffK row0 selHot' subIdx 0 c = 0 := by
  have hext := atMostOneHot_extendHot0 h
  dsimp only [affineApexEffK]
  rw [bilinearRowLo_zero_of_atMostOneHot _ _ _ hext,
    bilinearRowBit_zero_of_atMostOneHot _ _ _ hext,
    bilinearRowBit_zero_of_atMostOneHot _ _ _ hext, zmod2_val_zero]
  simp
theorem affineApexEffK_one_of_isOneHot {k_ctrl G' : ℕ} (row0 : Fin (G' + 1) → Bool → ℕ)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    {g₀ : Fin (G' + 1)} {c : Fin (2 ^ k_ctrl)}
    (h : IsOneHotBits g₀ (extendHot0 (ctrlHotBits selHot' c)))
    (hlo : 2048 ≤ row0 g₀ (decide (basisBits k_ctrl c subIdx = 1)))
    (hhi : row0 g₀ (decide (basisBits k_ctrl c subIdx = 1)) < 6144) :
    affineApexEffK row0 selHot' subIdx 1 c =
      row0 g₀ (decide (basisBits k_ctrl c subIdx = 1)) := by
  dsimp only [affineApexEffK]
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  rw [bilinearRowLo_one_of_isOneHot _ _ _ h,
    bilinearRowBit_one_of_isOneHot _ _ _ h,
    bilinearRowBit_one_of_isOneHot _ _ _ h, hv1]
  exact nat_decomp_apex hlo hhi
/-- Affine `(G' + 1)`-row Wire-Controlled cascade unitary specification. -/
noncomputable def affineUnsignedBilinearLac2CascadeCtrlUnitary {N k_ctrl G' : ℕ} (hN : 1 < N)
    (table : Fin (G' + 1) → Bool → Fin N → ℕ)
    (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    (c : Fin (2 ^ k_ctrl)) : Unitary (2 ^ N) :=
  let z0 : Fin N := ⟨0, by omega⟩
  let act := basisBits k_ctrl c actIdx
  let α_plane : ZMod 2 → ℕ → ℝ := fun b₁ p =>
    if hp : p + 1 < N then
      2 * π * (affinePlaneEffK (fun g b => table g b ⟨p, by omega⟩) selHot' subIdx b₁ c : ℝ) /
        (2 : ℝ) ^ 14
    else 0
  let α₀_apex := 2 * π *
    (affineApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot' subIdx (act * 0) c : ℝ) /
    (2 : ℝ) ^ 13
  let α₁_apex := 2 * π *
    (affineApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot' subIdx (act * 1) c : ℝ) /
    (2 : ℝ) ^ 13
  let U_tail := genTailUnitary N (α_plane 0) (α_plane 1) (N - 2) (by omega)
  let U_apex := (if act = 0 then 1 else (QRegister.singleton z0).embedUnitary Qubit.Z) *
    (GivensOps.pairAdj N 0 hN).embedUnitary (genGivensPosUnitary α₀_apex α₁_apex)
  U_tail⁻¹ * U_apex * U_tail
theorem affineUnsignedBilinearLac2CascadeCtrlUnitary_eq_one_of_act_zero
    {N k_ctrl G' : ℕ} (hN : 1 < N)
    (table : Fin (G' + 1) → Bool → Fin N → ℕ)
    (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    {c : Fin (2 ^ k_ctrl)}
    (hact0 : basisBits k_ctrl c actIdx = 0)
    (hatmost : AtMostOneHotBits (ctrlHotBits selHot' c)) :
    affineUnsignedBilinearLac2CascadeCtrlUnitary hN table actIdx selHot' subIdx c = 1 := by
  dsimp only [affineUnsignedBilinearLac2CascadeCtrlUnitary]
  have h0_eff : affineApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot' subIdx 0 c = 0 :=
    affineApexEffK_zero_of_atMostOneHot _ selHot' subIdx hatmost
  have hα0 : 2 * π *
      (affineApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot' subIdx
        (basisBits k_ctrl c actIdx * 0) c : ℝ) / (2 : ℝ) ^ 13 = 0 := by
    rw [hact0, zero_mul, h0_eff, Nat.cast_zero, mul_zero, zero_div]
  have hα1 : 2 * π *
      (affineApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot' subIdx
        (basisBits k_ctrl c actIdx * 1) c : ℝ) / (2 : ℝ) ^ 13 = 0 := by
    rw [hact0, zero_mul, h0_eff, Nat.cast_zero, mul_zero, zero_div]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hact0), hα0, hα1,
    genGivensPosUnitary_zero_zero, embedUnitary_one_eq, one_mul, mul_one, inv_mul_cancel]
theorem affineUnsignedBilinearLac2CascadeCtrlUnitary_eq_singleSpinReflection
    {N k_ctrl G' : ℕ} (hN : 1 < N)
    (table : Fin (G' + 1) → Bool → Fin N → ℕ)
    (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    {g₀ : Fin (G' + 1)} {c : Fin (2 ^ k_ctrl)}
    (hact1 : basisBits k_ctrl c actIdx = 1)
    (hoh : IsOneHotBits g₀ (extendHot0 (ctrlHotBits selHot' c)))
    (hlt : ∀ (p : ℕ) (hp : p + 1 < N),
      table g₀ (decide (basisBits k_ctrl c subIdx = 1)) ⟨p, by omega⟩ < 8192)
    (hlo0 : 2048 ≤ table g₀ (decide (basisBits k_ctrl c subIdx = 1)) ⟨0, by omega⟩)
    (hhi0 : table g₀ (decide (basisBits k_ctrl c subIdx = 1)) ⟨0, by omega⟩ < 6144) :
    let b_sel := decide (basisBits k_ctrl c subIdx = 1)
    let k : Fin N → ℤ := fun j => (table g₀ b_sel j : ℤ)
    affineUnsignedBilinearLac2CascadeCtrlUnitary hN table actIdx selHot' subIdx c =
      singleSpinReflectionUnitary N hN 15 k := by
  intro b_sel k
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hatmost : AtMostOneHotBits (ctrlHotBits selHot' c) := by
    intro g₁ g₂ hne
    exact hoh.atMostOneHot g₁.succ g₂.succ (fun heq => hne (Fin.succ_inj.mp heq))
  dsimp only [affineUnsignedBilinearLac2CascadeCtrlUnitary, singleSpinReflectionUnitary]
  rw [hact1, mul_zero, mul_one, ite_eq_right_of_eq_false _ _ (eq_false h10)]
  have htail : genTailUnitary N
      (fun p => if hp : p + 1 < N then
        2 * π * (affinePlaneEffK (fun g b => table g b ⟨p, by omega⟩) selHot' subIdx 0 c : ℝ) /
          (2 : ℝ) ^ 14 else 0)
      (fun p => if hp : p + 1 < N then
        2 * π * (affinePlaneEffK (fun g b => table g b ⟨p, by omega⟩) selHot' subIdx 1 c : ℝ) /
          (2 : ℝ) ^ 14 else 0)
      (N - 2) (by omega) =
      GivensOps.givensCascadeTail N (GivensOps.givensLeafAngle N 15 k) (N - 2) (by omega) := by
    apply genTailUnitary_eq_givensCascadeTail
    · intro p _ hpt
      have hp : p + 1 < N := by omega
      simp only [hp, ↓reduceDIte,
        affinePlaneEffK_zero_of_atMostOneHot _ selHot' subIdx hatmost,
        Nat.cast_zero, mul_zero, zero_div]
    · intro p _ hpt
      have hp : p + 1 < N := by omega
      simp only [hp, ↓reduceDIte]
      rw [affinePlaneEffK_one_of_isOneHot _ selHot' subIdx hoh (hlt p hp)]
      exact angle_13bit_eq_givensLeafAngle k p (by omega) _ rfl
  have hapex0 : 2 * π *
      (affineApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot' subIdx 0 c : ℝ) /
      (2 : ℝ) ^ 13 = 0 := by
    rw [affineApexEffK_zero_of_atMostOneHot _ selHot' subIdx hatmost,
      Nat.cast_zero, mul_zero, zero_div]
  have hapex1 : 2 * π *
      (affineApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot' subIdx 1 c : ℝ) /
      (2 : ℝ) ^ 13 = 2 * GivensOps.givensLeafAngle N 15 k 0 := by
    rw [affineApexEffK_one_of_isOneHot _ selHot' subIdx hoh hlo0 hhi0]
    exact angle_apex_eq_two_mul_givensLeafAngle hN k _ rfl
  rw [htail, hapex0, hapex1, genGivensPosUnitary_zero_left]
  rfl
/-- Self-inverse `0-T`, `0-TOFF` circuit clearing `wHot0` (`rOneHot 0`) to `|0⟩` on every
one-hot `(G' + 1)`-state by XORing `1 + ∑_{g=0}^{G'-1} rHot'[g]` into `wHot0`. -/
def clearHot0Circuit {n G' : ℕ} (rHot' : QRegister G' n) (wHot0 : Wire n)
    (hne : ∀ g : Fin G', rHot' g ≠ wHot0) : Circuit n :=
  cnotMaskReg G' rHot' wHot0 (fun _ => true) hne ;;ᶜ Circuit.X wHot0
@[simp] theorem count_clearHot0Circuit_t {n G' : ℕ} (rHot' : QRegister G' n) (wHot0 : Wire n)
    (hne : ∀ g : Fin G', rHot' g ≠ wHot0) :
    (clearHot0Circuit rHot' wHot0 hne).count .T = 0 := by
  simp [clearHot0Circuit]
@[simp] theorem count_clearHot0Circuit_toff {n G' : ℕ} (rHot' : QRegister G' n) (wHot0 : Wire n)
    (hne : ∀ g : Fin G', rHot' g ≠ wHot0) :
    (clearHot0Circuit rHot' wHot0 hne).count .TOFF = 0 := by
  simp [clearHot0Circuit]
theorem evolve_clearHot0Circuit_ket {n G' : ℕ} (rHot' : QRegister G' n) (wHot0 : Wire n)
    (hne : ∀ g : Fin G', rHot' g ≠ wHot0) (β : BitAssignment n) :
    (clearHot0Circuit rHot' wHot0 hne).eval.1.mulVec (ket β) =
      ket (Function.update β wHot0 (β wHot0 + (1 + ∑ g : Fin G', β (rHot' g)))) := by
  dsimp only [clearHot0Circuit]
  rw [eval_seq_mulVec, evolve_cnotMaskReg_ket, evolve_X_ket]
  have hsum : maskSumBit rHot' (fun _ => true) β = ∑ g : Fin G', β (rHot' g) := by
    simp [maskSumBit]
  rw [hsum, Function.update_self, Function.update_idem]
  refine congrArg (ket ∘ Function.update β wHot0) ?_
  ring
theorem clearHot0Circuit_eval_mul_self {n G' : ℕ}
    (rHot' : QRegister G' n) (wHot0 : Wire n) (hne : ∀ g : Fin G', rHot' g ≠ wHot0) :
    (clearHot0Circuit rHot' wHot0 hne).eval * (clearHot0Circuit rHot' wHot0 hne).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket; intro β
  change ((clearHot0Circuit rHot' wHot0 hne).eval.1 *
    (clearHot0Circuit rHot' wHot0 hne).eval.1).mulVec (ket β) = (1 : Matrix _ _ ℂ).mulVec (ket β)
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    evolve_clearHot0Circuit_ket, evolve_clearHot0Circuit_ket,
    Function.update_self, Function.update_idem]
  have hsame : (∑ g : Fin G',
      Function.update β wHot0 (β wHot0 + (1 + ∑ g' : Fin G', β (rHot' g'))) (rHot' g)) =
      ∑ g : Fin G', β (rHot' g) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    exact Function.update_of_ne (hne g) _ _
  rw [hsame]
  have hcancel : β wHot0 + (1 + ∑ g : Fin G', β (rHot' g)) + (1 + ∑ g : Fin G', β (rHot' g)) =
      β wHot0 := by
    rw [add_assoc, zmod2_add_self, add_zero]
  rw [hcancel, Function.update_eq_self]
theorem clearHot0_zero_of_isOneHot {G' : ℕ} {g₀ : Fin (G' + 1)} {fullBits : Fin (G' + 1) → ZMod 2}
    (h : IsOneHotBits g₀ fullBits) :
    fullBits 0 + (1 + ∑ g : Fin G', fullBits g.succ) = 0 ∧
      IsOneHotBits g₀ (extendHot0 (fun g : Fin G' => fullBits g.succ)) := by
  cases g₀ using Fin.cases with
  | zero =>
      have hz : ∀ g : Fin G', fullBits g.succ = 0 := fun g => h.2 g.succ (Fin.succ_ne_zero g)
      refine ⟨?_, isOneHotBits_extendHot0_of_zero hz⟩
      simp [h.1, hz, zmod2_add_self]
  | succ g₁ =>
      have h0 : fullBits 0 = 0 := h.2 0 (Fin.succ_ne_zero g₁).symm
      have htail : IsOneHotBits g₁ (fun g : Fin G' => fullBits g.succ) :=
        ⟨h.1, fun g hne => h.2 g.succ (fun heq => hne (Fin.succ_inj.mp heq))⟩
      have hsum : (∑ g : Fin G', fullBits g.succ) = 1 := by
        rw [Finset.sum_eq_single g₁ (fun g _ hne => htail.2 g hne)
          (fun hg => absurd (Finset.mem_univ g₁) hg)]
        exact h.1
      refine ⟨?_, isOneHotBits_extendHot0_of_succ htail⟩
      rw [h0, zero_add, hsum, zmod2_add_self]
end UnsignedGivens
end CompactStepFast176Select

open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensCascade
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn

namespace Router10Lac2Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.OneHotMux
/-- Parity control index `0` (`idx[0]`) inside the `10`-bit `(idx319 : 9, enR : 1)` register. -/
def subIdx10 : Fin 10 := ⟨0, by decide⟩
/-- Pair-index register `1..8` (`idx[1..8]`) inside the `10`-bit `(idx319 : 9, enR : 1)` slice. -/
def selPair10 : QRegister 8 10 := QRegister.block 1 8 (by decide)
/-- Active-enable index `9` (`enR`) inside the `10`-bit `(idx319 : 9, enR : 1)` register. -/
def actIdx10 : Fin 10 := ⟨9, by decide⟩
/-- Pure `58`-qubit branch unitary of `lac2Refl10LocalPUnit` indexed by `Fin (2 ^ 10)`. -/
noncomputable def lac2PureBranch10 (c : Fin (2 ^ 10)) : Unitary (2 ^ 58) :=
  oneHotActiveLac2BranchUnitary h58_gt_1 h160_ge_1
    UnsignedGivens.p450Split160Lac2Table actIdx10 selPair10 subIdx10 c
/-- Pure `58`-qubit branch unitary indexed by `10` control bits `(idx319 : 9, enR : 1)`. -/
noncomputable def lac2PureReflBits (z : Fin 10 → Bool) : Unitary (2 ^ 58) :=
  lac2PureBranch10 (finOfBits 10 z)
theorem lac2PureReflBits_of_false (z : Fin 10 → Bool) (hz : z 9 = false) :
    lac2PureReflBits z = 1 := by
  have hb0 : basisBits 10 (finOfBits 10 z) actIdx10 = 0 := by
    simp [finOfBits, actIdx10, hz]
  exact oneHotActiveLac2BranchUnitary_eq_one_of_act_zero h58_gt_1 h160_ge_1
    UnsignedGivens.p450Split160Lac2Table actIdx10 selPair10 subIdx10 hb0
theorem lac2PureReflBits_of_true_lt319 (idx : Fin 319) (z : Fin 10 → Bool)
    (hz : z 9 = true)
    (hfin : finOfBits 9 (fun j : Fin 9 ↦ z ⟨j.val, by omega⟩) =
      ⟨idx.val, by have := idx.isLt; omega⟩) :
    (lac2PureReflBits z).1 = singleSpinReflection (p450RowVector idx) := by
  let c10 := finOfBits 10 z
  have hb10 (k : Fin 10) : basisBits 10 c10 k = if z k then 1 else 0 := by
    change (basisBits 10 (finOfBits 10 z)) k = _
    simp [finOfBits]
  have hb9 (k : Fin 9) : z ⟨k.val, by omega⟩ =
      decide (basisBits 9 ⟨idx.val, by have := idx.isLt; omega⟩ k = 1) := by
    have hbf := congrFun (bitsOfFin_finOfBits 9 (fun j : Fin 9 ↦ z ⟨j.val, by omega⟩)) k
    rw [hfin] at hbf
    exact hbf.symm
  have hact1 : basisBits 10 c10 actIdx10 = 1 := by
    rw [hb10 actIdx10]; simp [actIdx10, hz]
  have hsub : decide (basisBits 10 c10 subIdx10 = 1) = decide (idx.val % 2 = 1) := by
    rw [hb10 subIdx10]
    have hz0 : z ⟨0, by decide⟩ =
        decide (basisBits 9 ⟨idx.val, by have := idx.isLt; omega⟩ 0 = 1) := hb9 0
    change decide ((if z ⟨0, by decide⟩ = true then (1 : ZMod 2) else 0) = 1) =
      decide (idx.val % 2 = 1)
    rw [hz0, basisBits_eq_div_mod]
    simp only [Fin.val_zero, _root_.pow_zero, Nat.div_one]
    rcases Nat.mod_two_eq_zero_or_one idx.val with h | h <;> simp [h]
  have hpair_bits : (fun i : Fin 8 ↦ basisBits 10 c10 (selPair10 i)) =
      basisBits 8 ⟨idx.val / 2, by have := idx.isLt; omega⟩ := by
    funext i
    have hs : selPair10 i = ⟨1 + i.val, by omega⟩ := by ext; simp [selPair10]
    rw [hs, hb10, hb9 ⟨1 + i.val, by omega⟩, basisBits_eq_div_mod, basisBits_eq_div_mod]
    have hdiv : idx.val / 2 ^ (1 + i.val) = (idx.val / 2) / 2 ^ i.val := by
      rw [pow_add, pow_one, ← Nat.div_div_eq_div_mul]
    dsimp only; rw [hdiv]
    rcases Nat.mod_two_eq_zero_or_one ((idx.val / 2) / 2 ^ i.val) with h | h <;> simp [h]
  have hg₀ : oneHotDecodeIdx 8 160 h160_ge_1 (fun i ↦ basisBits 10 c10 (selPair10 i)) =
      ⟨idx.val / 2, by have := idx.isLt; omega⟩ := by
    apply Fin.ext
    rw [hpair_bits, oneHotDecodeIdx_val_of_lt _ _ _ _
      (by rw [OneHotSimulates.bitsToNat_basisBits]; dsimp; have := idx.isLt; omega),
      OneHotSimulates.bitsToNat_basisBits]
  have hrefl := oneHotActiveLac2BranchUnitary_eq_singleSpinReflection_of_act_one h58_gt_1 h160_ge_1
    UnsignedGivens.p450Split160Lac2Table actIdx10 selPair10 subIdx10 (c_out := c10) hact1
    UnsignedGivens.p450Split160Lac2Table_bounds
  dsimp only at hrefl
  change (oneHotActiveLac2BranchUnitary h58_gt_1 h160_ge_1 UnsignedGivens.p450Split160Lac2Table
      actIdx10 selPair10 subIdx10 c10).1 = _
  rw [hrefl, hg₀, hsub, UnsignedGivens.singleSpinReflectionUnitary_val,
    givensLeaf_p450Split160Lac2Table_eq_unifiedOrbitalVector idx.isLt]
  have hvec : AliasTableData.unifiedOrbitalVector idx.val = p450RowVector idx := by
    unfold p450RowVector
    by_cases hlt : idx.val < 58
    · simp only [hlt, ↓reduceDIte]
      exact AliasTableData.unifiedOrbitalVector_oneBody ⟨idx.val, hlt⟩
    · simp only [hlt, ↓reduceDIte]
      have h58 : idx.val = 58 + (idx.val - 58) := by omega
      conv_lhs => rw [h58]
      exact AliasTableData.unifiedOrbitalVector_leaf ⟨idx.val - 58, by have := idx.isLt; omega⟩
  rw [hvec]; rfl
end Router10Lac2Select

namespace Lac2Fused184SelectWrap
/-- Overwrites register `r` in bit assignment `β` with bit vector `v`. -/
noncomputable def writeRegBits {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBits n).symm β) ((basisBits k).symm γ))
@[simp]
theorem writeRegBits_apply_reg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeRegBits β r γ (r i) = γ i := by
  simp [writeRegBits, QRegister.basisBits_replaceIndex_apply]
/-- Maps a `10`-bit `selectCoreArithSteps` prefix `(idx319 : 9, enR : 1)` to the `10`-bit
`Phase2Bal161Layout` control word `(0: row_0, 1: enR, 2..9: enR && row_1..row_8)`. -/
def permMaskedFrom10 (z10 : Fin 10 → Bool) : Fin 10 → Bool
  | 0 => z10 0
  | 1 => z10 9
  | ⟨k + 2, _⟩ => z10 9 && z10 ⟨k + 1, by omega⟩
theorem phase2Ctrl10Branch_permMaskedFrom10_eq (z10 : Fin 10 → Bool) :
    Lac2Fused184Select.phase2Ctrl10Branch (finOfBits 10 (permMaskedFrom10 z10)) =
      Router10Lac2Select.lac2PureReflBits z10 := by
  let c_m := finOfBits 10 (permMaskedFrom10 z10)
  let c_r := finOfBits 10 z10
  have hbm (k : Fin 10) : basisBits 10 c_m k = if permMaskedFrom10 z10 k then 1 else 0 := by
    simp [c_m, finOfBits]
  have hbr (k : Fin 10) : basisBits 10 c_r k = if z10 k then 1 else 0 := by
    simp [c_r, finOfBits]
  dsimp only [Lac2Fused184Select.phase2Ctrl10Branch, Router10Lac2Select.lac2PureReflBits,
    Router10Lac2Select.lac2PureBranch10]
  cases hz9 : z10 9
  · have hm0 : basisBits 10 c_m Lac2Fused184Select.actIdx10 = 0 := by
      rw [hbm]; simp [Lac2Fused184Select.actIdx10, permMaskedFrom10, hz9]
    have hr0 : basisBits 10 c_r Router10Lac2Select.actIdx10 = 0 := by
      rw [hbr]; simp [Router10Lac2Select.actIdx10, hz9]
    rw [CircuitModular.OneHotMux.oneHotActiveLac2BranchUnitary_eq_one_of_act_zero _ _ _ _ _ _ hm0,
      CircuitModular.OneHotMux.oneHotActiveLac2BranchUnitary_eq_one_of_act_zero _ _ _ _ _ _ hr0]
  · have hm1 : basisBits 10 c_m Lac2Fused184Select.actIdx10 = 1 := by
      rw [hbm]; simp [Lac2Fused184Select.actIdx10, permMaskedFrom10, hz9]
    have hr1 : basisBits 10 c_r Router10Lac2Select.actIdx10 = 1 := by
      rw [hbr]; simp [Router10Lac2Select.actIdx10, hz9]
    have hsub : basisBits 10 c_m Lac2Fused184Select.subIdx10 =
        basisBits 10 c_r Router10Lac2Select.subIdx10 := by
      rw [hbm, hbr]; rfl
    have hpair : (fun i : Fin 8 ↦ basisBits 10 c_m (Lac2Fused184Select.selPair10 i)) =
        fun i : Fin 8 ↦ basisBits 10 c_r (Router10Lac2Select.selPair10 i) := by
      funext i; rw [hbm, hbr]
      have hm_idx : Lac2Fused184Select.selPair10 i = ⟨i.val + 2, by omega⟩ := by
        fin_cases i <;> rfl
      have hr_idx : Router10Lac2Select.selPair10 i = ⟨i.val + 1, by omega⟩ := by
        fin_cases i <;> rfl
      rw [hm_idx, hr_idx]; simp [permMaskedFrom10, hz9]
    rw [OneHotMux.oneHotActiveLac2BranchUnitary_eq_singleSpinReflection_of_act_one _ _ _
        _ _ _ hm1 UnsignedGivens.p450Split160Lac2Table_bounds,
      OneHotMux.oneHotActiveLac2BranchUnitary_eq_singleSpinReflection_of_act_one _ _ _
        _ _ _ hr1 UnsignedGivens.p450Split160Lac2Table_bounds,
      hpair, hsub]
end Lac2Fused184SelectWrap

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open CircuitModular GivensOps
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation

namespace CompactStepFast176Select
namespace OneHotMux
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.OneHotMux
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensOps
/-- Tail `(G')`-wire subregister `g ↦ rOneHot g.succ` of a `(G' + 1)`-wire one-hot register. -/
def oneHotTailReg {n G' : ℕ} (rOneHot : QRegister (G' + 1) n) : QRegister G' n :=
  rOneHot.compose ⟨⟨Fin.succ, Fin.succ_injective G'⟩⟩
theorem clearHot0Circuit_conj_muxCtrlUnitary_eq
    {n k_3 k_ctrl G' : ℕ}
    (rSC : QRegister k_3 n) (rCtrlTail : QRegister k_ctrl n)
    (hCtrl2 : rSC.DisjointWires rCtrlTail)
    (selHot' : QRegister G' k_ctrl) (wHot0 : Wire n)
    (hNotSC0 : wHot0 ∉ Set.range rSC.wires)
    (hNotCtrl0 : ∀ j : Fin k_ctrl, rCtrlTail j ≠ wHot0)
    (W_aff : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_3)) :
    let rHot' := rCtrlTail.compose selHot'
    have hne0 : ∀ g : Fin G', rHot' g ≠ wHot0 := fun g => hNotCtrl0 (selHot' g)
    let cClear0 := UnsignedGivens.clearHot0Circuit rHot' wHot0 hne0
    let uAff := (rSC.concat rCtrlTail hCtrl2).embedUnitary (UnsignedGivens.muxCtrlUnitary W_aff)
    cClear0.eval * uAff * cClear0.eval = uAff := by
  intro rHot' hne0 cClear0 uAff
  have hNotSC_hot : ∀ g : Fin G', rHot' g ∉ Set.range rSC.wires := fun g ⟨sc, hsc⟩ =>
    QRegister.disjoint_iff.mp hCtrl2 sc (selHot' g) hsc
  apply Subtype.ext
  apply UnsignedGivens.matrix_ext_ket; intro β
  let δ : ZMod 2 := 1 + ∑ g : Fin G', β (rHot' g)
  let β₁ := Function.update β wHot0 (β wHot0 + δ)
  have hLocSC : UnsignedGivens.localIdx rSC β₁ = UnsignedGivens.localIdx rSC β := by
    dsimp only [UnsignedGivens.localIdx, β₁]; congr 1; funext sc
    exact Function.update_of_ne (fun h => hNotSC0 ⟨sc, h⟩) _ β
  have hLocCtrl : UnsignedGivens.localIdx rCtrlTail β₁ = UnsignedGivens.localIdx rCtrlTail β := by
    dsimp only [UnsignedGivens.localIdx, β₁]; congr 1; funext j
    exact Function.update_of_ne (hNotCtrl0 j) _ β
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, UnsignedGivens.evolve_clearHot0Circuit_ket]
  change cClear0.eval.1.mulVec (uAff.1.mulVec (UnsignedGivens.ket β₁)) =
    uAff.1.mulVec (UnsignedGivens.ket β)
  have hket_eq : @UnsignedGivens.ket n = @OneHotSimulates.ket n := rfl
  have hwreg_eq : @UnsignedGivens.writeReg n k_3 = @OneHotSimulates.writeReg n k_3 := rfl
  have hloc_eq : @UnsignedGivens.localIdx n k_3 = @OneHotSimulates.localIdx n k_3 := rfl
  dsimp only [uAff]
  rw [UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket,
    UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket,
    QRegister.embedUnitary_val, QRegister.embedUnitary_val, hket_eq,
    OneHotSimulates.embedMatrix_mulVec_ket, OneHotSimulates.embedMatrix_mulVec_ket,
    ← hket_eq, ← hwreg_eq, ← hloc_eq, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mulVec_smul, hLocSC, hLocCtrl]
  congr 1
  set γ := UnsignedGivens.writeReg β₁ rSC (basisBits k_3 l)
  rw [UnsignedGivens.evolve_clearHot0Circuit_ket]
  apply congrArg UnsignedGivens.ket
  have hγ_hot : (1 + ∑ g : Fin G', γ (rHot' g)) = δ := by
    dsimp only [δ, γ, β₁]; congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hNotSC_hot g),
      Function.update_of_ne (hne0 g)]
  have hγ_0 : γ wHot0 = β wHot0 + δ := by
    dsimp only [γ, β₁]
    rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hNotSC0, Function.update_self]
  rw [hγ_hot, hγ_0, add_assoc, UnsignedGivens.zmod2_add_self, add_zero]
  funext w
  by_cases hw0 : w = wHot0
  · subst hw0
    rw [Function.update_self, UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hNotSC0]
  · rw [Function.update_of_ne hw0]
    dsimp only [γ, β₁]
    by_cases hwSC : w ∈ Set.range rSC.wires
    · obtain ⟨sc, rfl⟩ := hwSC
      rw [UnsignedGivens.writeReg_apply_reg, UnsignedGivens.writeReg_apply_reg]
    · rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwSC,
        UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwSC, Function.update_of_ne hw0]
end OneHotMux
/-- `0-TOFF`, `4-T` reverse temporary-AND wrapper (`andUncompute ;; body ;; andCompute`), freeing a
dirty ancilla `anc = c₁ * c₂` to `0` across `body` and recomputing `anc = c₁ * c₂` afterward. -/
def revTempAndProg {Var : Type} {n : ℕ} (v : Var)
    (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.andUncompute v c₁ c₂ anc h₁₂)
    (.seq body (.andCompute c₁ c₂ anc h₁a h₂a))
@[simp]
theorem count_revTempAndProg_toff {Var : Type} {n : ℕ} (v : Var)
    (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : DynamicCircuit Var n) :
    (revTempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a body).count .TOFF = body.count .TOFF := by
  have ha : (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).count .TOFF = 0 := rfl
  have hu : (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).count .TOFF = 0 := rfl
  simp [revTempAndProg, DynamicCircuit.count, ha, hu]
@[simp]
theorem count_revTempAndProg_t {Var : Type} {n : ℕ} (v : Var)
    (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : DynamicCircuit Var n) :
    (revTempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a body).count .T = body.count .T + 4 := by
  have ha : (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).count .T = 4 := rfl
  have hu : (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).count .T = 0 := rfl
  simp only [revTempAndProg, DynamicCircuit.count, ha, hu]
  omega
theorem x_eval_mul_self_loc {n : ℕ} (q : Wire n) :
    (Circuit.X q).eval * (Circuit.X q).eval = 1 := by
  apply Subtype.ext; apply OneHotSimulates.matrix_ext_ket; intro β
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, OneHotSimulates.ket_X, OneHotSimulates.ket_X,
    Submonoid.coe_one, Matrix.one_mulVec]
  congr 1; funext w
  by_cases hw : w = q
  · subst hw; simp [add_assoc, CharTwo.add_self_eq_zero]
  · simp [hw]
theorem x_conj_commutesWithWire {n : ℕ} {q t : Wire n} {A : Operator (2 ^ n)}
    (hA : OneHotSimulates.CommutesWithWire q A) :
    OneHotSimulates.CommutesWithWire q ((Circuit.X t).eval.1 * A * (Circuit.X t).eval.1) := by
  by_cases hqt : q = t
  · subst hqt
    intro o
    have hoLt := o.isLt
    let o' : Fin 2 := ⟨1 - o.val, by omega⟩
    have hXP (u : Fin 2) :
        (Circuit.X q).eval.1 * (QRegister.singleton q).basisOutcomeProjector u =
          (QRegister.singleton q).basisOutcomeProjector ⟨1 - u.val, by omega⟩ *
            (Circuit.X q).eval.1 := by
      apply OneHotSimulates.matrix_ext_ket; intro β
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, OneHotSimulates.ket_projector,
        OneHotSimulates.ket_X, OneHotSimulates.ket_projector, Function.update_self]
      have hiff : (β q + 1 = ((1 - u.val : ℕ) : ZMod 2)) ↔ (β q = (u.val : ZMod 2)) := by
        rcases UnsignedGivens.zmod2_eq_zero_or_one (β q) with hq | hq <;>
          fin_cases u <;> rw [hq] <;> decide
      by_cases hu : β q = (u.val : ZMod 2)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hu),
          ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr hu)), OneHotSimulates.ket_X]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hu),
          ite_eq_right_of_eq_false _ _ (eq_false (mt hiff.mp hu)), Matrix.mulVec_zero]
    have hPX : (Circuit.X q).eval.1 * (QRegister.singleton q).basisOutcomeProjector o' =
        (QRegister.singleton q).basisOutcomeProjector o * (Circuit.X q).eval.1 := by
      convert hXP o' using 2
      congr 1; apply Fin.ext; dsimp [o']; omega
    calc ((Circuit.X q).eval.1 * A * (Circuit.X q).eval.1) *
            (QRegister.singleton q).basisOutcomeProjector o
        = (Circuit.X q).eval.1 * (A * (QRegister.singleton q).basisOutcomeProjector o') *
            (Circuit.X q).eval.1 := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hXP o]
            simp only [o', Matrix.mul_assoc]
      _ = ((Circuit.X q).eval.1 * (QRegister.singleton q).basisOutcomeProjector o') *
            A * (Circuit.X q).eval.1 := by
            rw [hA o']; simp only [Matrix.mul_assoc]
      _ = (QRegister.singleton q).basisOutcomeProjector o *
            ((Circuit.X q).eval.1 * A * (Circuit.X q).eval.1) := by
            rw [hPX]; simp only [Matrix.mul_assoc]
  · have hX : OneHotSimulates.CommutesWithWire q (Circuit.X t).eval.1 :=
      OneHotSimulates.CommutesWithWire.of_ket_map fun β ↦
        ⟨1, Function.update β t (β t + 1), Function.update_of_ne hqt _ _,
          by rw [one_smul]; exact OneHotSimulates.ket_X t β⟩
    exact (hX.mul hA).mul hX
/-- `DiagProjSimulates` rule for `revTempAndProg`: conjugates `(P_mid * P_a)` and `U_mid` by
`Circuit.TOFF c₁ c₂ anc`. -/
theorem DiagProjSimulates.revTempAnd {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    {P_mid : Operator (2 ^ n)} {U_mid : Unitary (2 ^ n)} {body : DynamicCircuit Var n}
    (hMid : Lac2Fused184Select.DiagProjSimulates P_mid U_mid body)
    (hanc : OneHotSimulates.CommutesWithWire anc U_mid.1) :
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
    let P_a := (QRegister.singleton anc).basisOutcomeProjector 0
    Lac2Fused184Select.DiagProjSimulates
      (T_anc.1 * (P_mid * P_a) * T_anc.1) (T_anc * U_mid * T_anc)
      (revTempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a body) := by
  dsimp only
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  let P_a := (QRegister.singleton anc).basisOutcomeProjector 0
  let P' := P_mid * P_a
  have hPa_diag : Lac2Fused184Select.IsDiagProj P_a :=
    Lac2Fused184Select.IsDiagProj.basisOutcomeProjector (QRegister.singleton anc) 0
  have hPa_herm : P_aᴴ = P_a := hPa_diag.conjTranspose_eq
  have hP'_diag : Lac2Fused184Select.IsDiagProj P' := hMid.1.mul hPa_diag
  have hU_Pa : U_mid.1 * P_a = P_a * U_mid.1 := hanc 0
  have hU_P' : U_mid.1 * P' = P' * U_mid.1 := by
    dsimp only [P']
    rw [← Matrix.mul_assoc, hMid.2.1, Matrix.mul_assoc, hU_Pa, ← Matrix.mul_assoc]
  have hSim' : Lac2Fused184Select.DiagProjSimulates P' U_mid body := by
    refine hMid.tighten hP'_diag ?_ hU_P'
    dsimp only [P']
    rw [hMid.1.comm hPa_diag, Matrix.mul_assoc, hMid.1.mul_self]
  have hT_sq : T_anc * T_anc = 1 := OneHotSimulates.toffoli_eval_mul_self c₁ c₂ anc h₁₂ h₁a h₂a
  have hT_herm : T_anc.1ᴴ = T_anc.1 :=
    OneHotSimulates.unitary_conjTranspose_eq_self_of_mul_self T_anc hT_sq
  have hOut_diag : Lac2Fused184Select.IsDiagProj (T_anc.1 * P' * T_anc.1) := by
    have heq : T_anc.1 * P' * T_anc.1 = T_anc.1ᴴ * P' * T_anc.1 := by rw [hT_herm]
    rw [heq]
    exact hP'_diag.conj_of_ket_map T_anc fun β ↦
      ⟨_, OneHotSimulates.ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β⟩
  obtain ⟨P_out, hP_out⟩ : ∃ P_out : Operator (2 ^ n), T_anc.1 * P' * T_anc.1 = P_out :=
    ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Unitary (2 ^ n), T_anc * U_mid * T_anc = V := ⟨_, rfl⟩
  change Lac2Fused184Select.DiagProjSimulates
    (T_anc.1 * P' * T_anc.1) (T_anc * U_mid * T_anc)
    (revTempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a body)
  rw [hP_out, hV]
  rw [hP_out] at hOut_diag
  have hT_mat_sq : T_anc.1 * T_anc.1 = 1 := congrArg Subtype.val hT_sq
  have hTP : T_anc.1 * P_out = P' * T_anc.1 := by
    rw [← hP_out]
    calc T_anc.1 * (T_anc.1 * P' * T_anc.1) = (T_anc.1 * T_anc.1) * P' * T_anc.1 := by
          simp only [Matrix.mul_assoc]
      _ = P' * T_anc.1 := by rw [hT_mat_sq, Matrix.one_mul]
  have hPT : P_out * T_anc.1 = T_anc.1 * P' := by
    rw [← hP_out]
    calc (T_anc.1 * P' * T_anc.1) * T_anc.1 = T_anc.1 * P' * (T_anc.1 * T_anc.1) := by
          simp only [Matrix.mul_assoc]
      _ = T_anc.1 * P' := by rw [hT_mat_sq, Matrix.mul_one]
  refine ⟨hOut_diag, ?_, fun M ↦ ?_⟩
  · rw [← hV]
    change (T_anc.1 * U_mid.1 * T_anc.1) * P_out = P_out * (T_anc.1 * U_mid.1 * T_anc.1)
    calc (T_anc.1 * U_mid.1 * T_anc.1) * P_out
        = T_anc.1 * U_mid.1 * (T_anc.1 * P_out) := by simp only [Matrix.mul_assoc]
      _ = T_anc.1 * (U_mid.1 * P') * T_anc.1 := by rw [hTP]; simp only [Matrix.mul_assoc]
      _ = (T_anc.1 * P') * U_mid.1 * T_anc.1 := by rw [hU_P']; simp only [Matrix.mul_assoc]
      _ = (P_out * T_anc.1) * U_mid.1 * T_anc.1 := by rw [hPT]
      _ = P_out * (T_anc.1 * U_mid.1 * T_anc.1) := by simp only [Matrix.mul_assoc]
  · let C_and := (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval
    let M₃ : Observable (Fin (2 ^ n)) := qcQAssignObsMap C_and M
    obtain ⟨M₂, hwp₂, hproj₂⟩ := hSim'.2.2 M₃
    obtain ⟨M₁, hwp₁⟩ := OneHotSimulates.wp_andUncompute_const v c₁ c₂ anc h₁₂ M₂
    refine ⟨M₁, ?_, ?_⟩
    · funext σ
      have h3 : (wp (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).compile
          fun _ ↦ M) = fun _ ↦ M₃ := by
        funext σ'
        simp [DynamicCircuit.andCompute, DynamicCircuit.compile_circuit, qcWpQAssign, M₃, C_and]
      dsimp only [revTempAndProg]
      simp only [DynamicCircuit.compile_seq, wp, h3, hwp₂]
      exact congrFun hwp₁ σ
    · have h3_raw := DynamicCircuit.qc_wp_qAssign_andCompute
        c₁ c₂ anc h₁₂ h₁a h₂a (fun _ : Store Var ↦ M)
      have h3_val := congrArg (fun f : QCAssertion Var (2 ^ n) ↦ (f 0).1.1) h3_raw
      have hM₃_Pa : P_a * M₃.1.1 * P_a = P_a * (T_anc.1ᴴ * M.1.1 * T_anc.1) * P_a := by
        dsimp only [P_a, T_anc, M₃, C_and, restrictAssertionToZeroAncilla_coe, qcWpQAssign,
          qcQAssignObsMap] at h3_val ⊢
        simpa only [Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
          conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose,
          conjTranspose_conjTranspose, Matrix.mul_assoc, val_eq_coe] using h3_val
      have h1_raw := open DynamicCircuit in
        qc_wp_toffoli_andUncompute_of_update_eq
          v c₁ c₂ anc h₁₂ h₁a h₂a (fun _ : Store Var ↦ M₂) (fun _ _ ↦ rfl)
      have h1_val := congrArg (fun f : QCAssertion Var (2 ^ n) ↦ (f 0).1.1) h1_raw
      rw [hwp₁] at h1_val
      have hM₁_Pa : P_a * (T_anc.1ᴴ * M₁.1.1 * T_anc.1) * P_a = P_a * M₂.1.1 * P_a := by
        dsimp only [P_a, T_anc, restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap]
          at h1_val ⊢
        simpa only [Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
          conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose,
          conjTranspose_conjTranspose, Matrix.mul_assoc, val_eq_coe] using h1_val
      obtain ⟨T_op, hT_op⟩ : ∃ T_op : Unitary (2 ^ n), T_anc = T_op := ⟨_, rfl⟩
      rw [hT_op] at hT_herm hT_mat_sq hTP hPT hV hM₃_Pa hM₁_Pa
      rw [hT_herm] at hM₃_Pa hM₁_Pa
      have hP'_Pa : P' * P_a = P' := by
        dsimp only [P']; rw [Matrix.mul_assoc, hPa_diag.mul_self]
      have hPa_P' : P_a * P' = P' := by
        rw [hPa_diag.comm hP'_diag, hP'_Pa]
      have hUadj_Pa : P_a * U_mid.1ᴴ = U_mid.1ᴴ * P_a := by
        simpa only [Matrix.conjTranspose_mul, hPa_herm] using
          congrArg (·ᴴ) hU_Pa
      have hUPaP' : U_mid.1 * (P_a * P') = P_a * (U_mid.1 * P') := by
        rw [← Matrix.mul_assoc, hU_Pa, Matrix.mul_assoc]
      have hMidEq : P' * M₂.1.1 * P' =
          P' * (U_mid.1ᴴ * (T_op.1 * M.1.1 * T_op.1) * U_mid.1) * P' := by
        rw [hproj₂]
        calc P' * (U_mid.1ᴴ * M₃.1.1 * U_mid.1) * P'
            = (P' * P_a) * U_mid.1ᴴ * M₃.1.1 * U_mid.1 * (P_a * P') := by
                rw [hP'_Pa, hPa_P']; simp only [Matrix.mul_assoc]
          _ = P' * U_mid.1ᴴ * (P_a * M₃.1.1 * P_a) * U_mid.1 * P' := by
                rw [Matrix.mul_assoc P' P_a, hUadj_Pa, Matrix.mul_assoc _ U_mid.1 (P_a * P'),
                  hUPaP']
                simp only [Matrix.mul_assoc]
          _ = P' * U_mid.1ᴴ * (P_a * (T_op.1 * M.1.1 * T_op.1) * P_a) * U_mid.1 * P' := by
                rw [hM₃_Pa]
          _ = (P' * P_a) * U_mid.1ᴴ * (T_op.1 * M.1.1 * T_op.1) * U_mid.1 * (P_a * P') := by
                rw [Matrix.mul_assoc P' P_a, hUadj_Pa, Matrix.mul_assoc _ U_mid.1 (P_a * P'),
                  hUPaP']
                simp only [Matrix.mul_assoc]
          _ = P' * (U_mid.1ᴴ * (T_op.1 * M.1.1 * T_op.1) * U_mid.1) * P' := by
                rw [hP'_Pa, hPa_P']; simp only [Matrix.mul_assoc]
      have hV_adj : V.1ᴴ * M.1.1 * V.1 = T_op.1 * (U_mid.1ᴴ * (T_op.1 * M.1.1 * T_op.1) * U_mid.1) *
          T_op.1 := by
        rw [← hV]
        simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, hT_herm, Matrix.mul_assoc]
      calc P_out * M₁.1.1 * P_out
          = (P_out * T_op.1) * (T_op.1 * M₁.1.1 * T_op.1) * (T_op.1 * P_out) := by
              calc P_out * M₁.1.1 * P_out
                  = P_out * (T_op.1 * T_op.1) * M₁.1.1 * (T_op.1 * T_op.1) * P_out := by
                      rw [hT_mat_sq, Matrix.mul_one, Matrix.mul_one]
                _ = (P_out * T_op.1) * (T_op.1 * M₁.1.1 * T_op.1) * (T_op.1 * P_out) := by
                      simp only [Matrix.mul_assoc]
        _ = (T_op.1 * P') * (T_op.1 * M₁.1.1 * T_op.1) * (P' * T_op.1) := by rw [hPT, hTP]
        _ = T_op.1 * (P' * P_a) * (T_op.1 * M₁.1.1 * T_op.1) * (P_a * P') * T_op.1 := by
              rw [hP'_Pa, hPa_P']; simp only [Matrix.mul_assoc]
        _ = T_op.1 * P' * (P_a * (T_op.1 * M₁.1.1 * T_op.1) * P_a) * P' * T_op.1 := by
              simp only [Matrix.mul_assoc]
        _ = T_op.1 * P' * (P_a * M₂.1.1 * P_a) * P' * T_op.1 := by rw [hM₁_Pa]
        _ = T_op.1 * ((P' * P_a) * M₂.1.1 * (P_a * P')) * T_op.1 := by
              simp only [Matrix.mul_assoc]
        _ = T_op.1 * (P' * M₂.1.1 * P') * T_op.1 := by rw [hP'_Pa, hPa_P']
        _ = T_op.1 * (P' * (U_mid.1ᴴ * (T_op.1 * M.1.1 * T_op.1) * U_mid.1) * P') * T_op.1 := by
              rw [hMidEq]
        _ = (T_op.1 * P') * (U_mid.1ᴴ * (T_op.1 * M.1.1 * T_op.1) * U_mid.1) * (P' * T_op.1) := by
              simp only [Matrix.mul_assoc]
        _ = (P_out * T_op.1) * (U_mid.1ᴴ * (T_op.1 * M.1.1 * T_op.1) * U_mid.1) *
              (T_op.1 * P_out) := by rw [← hPT, ← hTP]
        _ = P_out * (V.1ᴴ * M.1.1 * V.1) * P_out := by
              rw [hV_adj]; simp only [Matrix.mul_assoc]
/-- Reversible / measurement-uncomputed gate primitive for zero-`TOFF` conjugation wrappers,
supporting `X`, `CNOT`, clean-ancilla `.andAlloc` (`4 T` in Entry), and dirty-ancilla `.andFree`
(`4 T` in Exit). -/
inductive RouterStep (n : ℕ) where
  /-- Single-qubit Pauli-`X` conjugation step (`0 T`). -/
  | x (t : Wire n)
  /-- Controlled-NOT conjugation step (`0 T`). -/
  | cnot (c t : Wire n) (hne : c ≠ t)
  /-- Forward temporary-AND step (`andCompute ;; body ;; andUncompute`, `4 T`). -/
  | andAlloc (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
  /-- Reverse temporary-AND step (`andUncompute ;; body ;; andCompute`, `4 T`). -/
  | andFree (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
/-- Reference forward classical `Circuit` for a single `RouterStep`. -/
def RouterStep.toCircuit {n : ℕ} : RouterStep n → Circuit n
  | .x t => .X t
  | .cnot c t hne => .CNOT c t hne
  | .andAlloc c₁ c₂ anc h₁₂ h₁a h₂a => .TOFF c₁ c₂ anc h₁₂ h₁a h₂a
  | .andFree c₁ c₂ anc h₁₂ h₁a h₂a => .TOFF c₁ c₂ anc h₁₂ h₁a h₂a
/-- Computational-basis bit-assignment update for a single `RouterStep`. -/
def RouterStep.assign {n : ℕ} : RouterStep n → BitAssignment n → BitAssignment n
  | .x t, β => Function.update β t (β t + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .andAlloc c₁ c₂ anc _ _ _, β => Function.update β anc (β anc + β c₁ * β c₂)
  | .andFree c₁ c₂ anc _ _ _, β => Function.update β anc (β anc + β c₁ * β c₂)
/-- Predicate stating that every wire touched by a `RouterStep` satisfies `W`. -/
def RouterStep.TouchesIn {n : ℕ} (W : Wire n → Prop) : RouterStep n → Prop
  | .x t => W t
  | .cnot c t _ => W c ∧ W t
  | .andAlloc c₁ c₂ anc _ _ _ => W c₁ ∧ W c₂ ∧ W anc
  | .andFree c₁ c₂ anc _ _ _ => W c₁ ∧ W c₂ ∧ W anc
/-- Forward reference `Circuit` for a list of `RouterStep`s. -/
def routerStepsCircuit {n : ℕ} : List (RouterStep n) → Circuit n
  | [] => .identity
  | s :: rest => s.toCircuit ;;ᶜ routerStepsCircuit rest
/-- Zero-`TOFF` `DynamicCircuit` conjugation wrapper for a list of `RouterStep`s around `body`. -/
def routerStepsProg {Var : Type} {n : ℕ} (v : Var) :
    List (RouterStep n) → DynamicCircuit Var n → DynamicCircuit Var n
  | [], body => body
  | .x t :: rest, body =>
      .seq (.circuit (.X t)) (.seq (routerStepsProg v rest body) (.circuit (.X t)))
  | .cnot c t hne :: rest, body =>
      .seq (.circuit (.CNOT c t hne))
        (.seq (routerStepsProg v rest body) (.circuit (.CNOT c t hne)))
  | .andAlloc c₁ c₂ anc h₁₂ h₁a h₂a :: rest, body =>
      OneHotSimulates.tempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a (routerStepsProg v rest body)
  | .andFree c₁ c₂ anc h₁₂ h₁a h₂a :: rest, body =>
      revTempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a (routerStepsProg v rest body)
/-- Total number of `.andAlloc` and `.andFree` steps in a `RouterStep` list (`4 T` each). -/
def numRouterAnds {n : ℕ} : List (RouterStep n) → ℕ
  | [] => 0
  | .x _ :: rest => numRouterAnds rest
  | .cnot _ _ _ :: rest => numRouterAnds rest
  | .andAlloc _ _ _ _ _ _ :: rest => 1 + numRouterAnds rest
  | .andFree _ _ _ _ _ _ :: rest => 1 + numRouterAnds rest
@[simp]
theorem numRouterAnds_append {n : ℕ} (xs ys : List (RouterStep n)) :
    numRouterAnds (xs ++ ys) = numRouterAnds xs + numRouterAnds ys := by
  induction xs with
  | nil => simp [numRouterAnds]
  | cons s rest ih => cases s <;> simp [numRouterAnds, ih, Nat.add_assoc]
/-- Forward bit-assignment action of a `RouterStep` list. -/
def routerStepsAssign {n : ℕ} : List (RouterStep n) → BitAssignment n → BitAssignment n
  | [], β => β
  | s :: rest, β => routerStepsAssign rest (s.assign β)
@[simp]
theorem routerStepsAssign_append {n : ℕ} (xs ys : List (RouterStep n)) (β : BitAssignment n) :
    routerStepsAssign (xs ++ ys) β = routerStepsAssign ys (routerStepsAssign xs β) := by
  induction xs generalizing β with
  | nil => rfl
  | cons s rest ih => exact ih (s.assign β)
/-- Ancilla precondition along forward execution of a `RouterStep` list. -/
def routerStepsOk {n : ℕ} : List (RouterStep n) → BitAssignment n → Prop
  | [], _ => True
  | .x t :: rest, β => routerStepsOk rest (Function.update β t (β t + 1))
  | .cnot c t _ :: rest, β => routerStepsOk rest (Function.update β t (β t + β c))
  | .andAlloc c₁ c₂ anc _ _ _ :: rest, β =>
      β anc = 0 ∧ routerStepsOk rest (Function.update β anc (β anc + β c₁ * β c₂))
  | .andFree c₁ c₂ anc _ _ _ :: rest, β =>
      β anc = β c₁ * β c₂ ∧ routerStepsOk rest (Function.update β anc (β anc + β c₁ * β c₂))
@[simp]
theorem count_routerStepsProg_toff {Var : Type} {n : ℕ} (v : Var)
    (steps : List (RouterStep n)) (body : DynamicCircuit Var n) :
    (routerStepsProg v steps body).count .TOFF = body.count .TOFF := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | x t => simp [routerStepsProg, DynamicCircuit.count, ih]
      | cnot c t hne => simp [routerStepsProg, DynamicCircuit.count, ih]
      | andAlloc c₁ c₂ anc h₁₂ h₁a h₂a => simp [routerStepsProg, ih]
      | andFree c₁ c₂ anc h₁₂ h₁a h₂a => simp [routerStepsProg, ih]
theorem ket_routerStep {n : ℕ} (s : RouterStep n) (β : BitAssignment n) :
    s.toCircuit.eval.1.mulVec (OneHotSimulates.ket β) = OneHotSimulates.ket (s.assign β) := by
  cases s with
  | x t => exact OneHotSimulates.ket_X t β
  | cnot c t hne => exact OneHotSimulates.ket_CNOT c t hne β
  | andAlloc c₁ c₂ anc h₁₂ h₁a h₂a => exact OneHotSimulates.ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β
  | andFree c₁ c₂ anc h₁₂ h₁a h₂a => exact OneHotSimulates.ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β
theorem routerStep_eval_mul_self {n : ℕ} (s : RouterStep n) :
    s.toCircuit.eval * s.toCircuit.eval = 1 := by
  cases s with
  | x t => exact x_eval_mul_self_loc t
  | cnot c t hne => exact OneHotSimulates.cnot_eval_mul_self c t hne
  | andAlloc c₁ c₂ anc h₁₂ h₁a h₂a =>
    exact OneHotSimulates.toffoli_eval_mul_self c₁ c₂ anc h₁₂ h₁a h₂a
  | andFree c₁ c₂ anc h₁₂ h₁a h₂a =>
    exact OneHotSimulates.toffoli_eval_mul_self c₁ c₂ anc h₁₂ h₁a h₂a
theorem ket_routerStepsCircuit {n : ℕ} (steps : List (RouterStep n)) (β : BitAssignment n) :
    (routerStepsCircuit steps).eval.1.mulVec (OneHotSimulates.ket β) =
      OneHotSimulates.ket (routerStepsAssign steps β) := by
  induction steps generalizing β with
  | nil =>
      rw [routerStepsCircuit, routerStepsAssign, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec]
  | cons s rest ih =>
      dsimp only [routerStepsCircuit, routerStepsAssign]
      rw [UnsignedGivens.eval_seq_mulVec, ket_routerStep, ih]
theorem routerSteps_raw {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (W : Wire n → Prop)
    (steps : List (RouterStep n)) (hW : ∀ s ∈ steps, s.TouchesIn W)
    {P_body : Operator (2 ^ n)} {U_body : Unitary (2 ^ n)} {body : DynamicCircuit Var n}
    (hBody : Lac2Fused184Select.DiagProjSimulates P_body U_body body)
    (hComm : ∀ q, W q → OneHotSimulates.CommutesWithWire q U_body.1) :
    ∃ P_out : Operator (2 ^ n),
      let Dc := (routerStepsCircuit steps).eval
      Lac2Fused184Select.DiagProjSimulates P_out (Dc⁻¹ * U_body * Dc)
        (routerStepsProg v steps body) ∧
      (∀ q, W q → OneHotSimulates.CommutesWithWire q (Dc⁻¹ * U_body * Dc).1) ∧
      (∀ β : BitAssignment n, routerStepsOk steps β →
        P_body.mulVec (OneHotSimulates.ket (routerStepsAssign steps β)) =
          OneHotSimulates.ket (routerStepsAssign steps β) →
        P_out.mulVec (OneHotSimulates.ket β) = OneHotSimulates.ket β) := by
  induction steps with
  | nil =>
      refine ⟨P_body, ?_, ?_, ?_⟩
      · simpa [routerStepsCircuit, routerStepsProg] using hBody
      · intro q hq; simpa [routerStepsCircuit] using hComm q hq
      · intro β _ hP; exact hP
  | cons s rest ih =>
      have hsW : s.TouchesIn W := hW s (List.mem_cons_self ..)
      have hrestW : ∀ s' ∈ rest, s'.TouchesIn W :=
        fun s' hm ↦ hW s' (List.mem_cons_of_mem _ hm)
      obtain ⟨P_mid, hSimMid, hCommMid, hFixMid⟩ := ih hrestW
      let D_rest := (routerStepsCircuit rest).eval
      let U_mid := D_rest⁻¹ * U_body * D_rest
      let Cs := s.toCircuit.eval
      have hCs_sq : Cs * Cs = 1 := routerStep_eval_mul_self s
      have hCs_inv : Cs⁻¹ = Cs := mul_eq_one_iff_inv_eq.mp hCs_sq
      have hCs_mat_sq : Cs.1 * Cs.1 = 1 := congrArg Subtype.val hCs_sq
      have hDc_eq : (routerStepsCircuit (s :: rest)).eval⁻¹ * U_body *
          (routerStepsCircuit (s :: rest)).eval = Cs * U_mid * Cs := by
        dsimp only [routerStepsCircuit]
        rw [Circuit.eval_seq]
        change (D_rest * Cs)⁻¹ * U_body * (D_rest * Cs) = Cs * (D_rest⁻¹ * U_body * D_rest) * Cs
        rw [_root_.mul_inv_rev, hCs_inv]
        simp only [mul_assoc]
      cases s with
      | x t =>
          refine ⟨Cs.1 * P_mid * Cs.1, ?_⟩
          dsimp only
          rw [hDc_eq]
          refine ⟨?_, ?_, ?_⟩
          · exact hSimMid.conjSelfInv (.X t) hCs_sq (fun β ↦ ⟨_, OneHotSimulates.ket_X t β⟩)
          · intro q hqW
            exact x_conj_commutesWithWire (hCommMid q hqW)
          · intro β hOk hPb
            have hX1 : Cs.1.mulVec (OneHotSimulates.ket β) =
                OneHotSimulates.ket (Function.update β t (β t + 1)) :=
              OneHotSimulates.ket_X t β
            have hMid := hFixMid _ hOk hPb
            have hX2 : Cs.1.mulVec (OneHotSimulates.ket (Function.update β t (β t + 1))) =
                OneHotSimulates.ket β := by
              rw [← hX1, Matrix.mulVec_mulVec, hCs_mat_sq, Matrix.one_mulVec]
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hX1, hMid, hX2]
      | cnot c t hne =>
          obtain ⟨hcW, _⟩ := hsW
          refine ⟨Cs.1 * P_mid * Cs.1, ?_⟩
          dsimp only
          rw [hDc_eq]
          refine ⟨?_, ?_, ?_⟩
          · exact hSimMid.conjSelfInv (.CNOT c t hne) hCs_sq
              (fun β ↦ ⟨_, OneHotSimulates.ket_CNOT c t hne β⟩)
          · intro q hqW
            by_cases hqt : q = t
            · subst hqt
              exact OneHotSimulates.cnot_conj_commutesWithWire_target hne
                (hCommMid c hcW) (hCommMid q hqW)
            · exact ((OneHotSimulates.CommutesWithWire.cnot_of_ne_target hne hqt).mul
                (hCommMid q hqW)).mul
                (OneHotSimulates.CommutesWithWire.cnot_of_ne_target hne hqt)
          · intro β hOk hPb
            have hC1 : Cs.1.mulVec (OneHotSimulates.ket β) =
                OneHotSimulates.ket (Function.update β t (β t + β c)) :=
              OneHotSimulates.ket_CNOT c t hne β
            have hMid := hFixMid _ hOk hPb
            have hC2 : Cs.1.mulVec (OneHotSimulates.ket (Function.update β t (β t + β c))) =
                OneHotSimulates.ket β := by
              rw [← hC1, Matrix.mulVec_mulVec, hCs_mat_sq, Matrix.one_mulVec]
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hC1, hMid, hC2]
      | andAlloc c₁ c₂ anc h₁₂ h₁a h₂a =>
          obtain ⟨hc₁W, hc₂W, haW⟩ := hsW
          let P_a := (QRegister.singleton anc).basisOutcomeProjector 0
          refine ⟨(Cs.1 * P_mid * Cs.1) * P_a, ?_⟩
          dsimp only
          rw [hDc_eq]
          refine ⟨?_, ?_, ?_⟩
          · exact Lac2Fused184Select.DiagProjSimulates.tempAnd v c₁ c₂ anc h₁₂ h₁a h₂a hSimMid
              (hCommMid c₁ hc₁W) (hCommMid c₂ hc₂W) (hCommMid anc haW)
          · intro q hqW
            by_cases hqa : q = anc
            · subst hqa
              exact OneHotSimulates.toffoli_conj_commutesWithWire_ancilla h₁₂ h₁a h₂a
                (hCommMid c₁ hc₁W) (hCommMid c₂ hc₂W) (hCommMid q hqW)
            · exact ((OneHotSimulates.CommutesWithWire.toffoli_of_ne_target h₁₂ h₁a h₂a hqa).mul
                (hCommMid q hqW)).mul
                (OneHotSimulates.CommutesWithWire.toffoli_of_ne_target h₁₂ h₁a h₂a hqa)
          · intro β hOk hPb
            obtain ⟨hanc0, hOkRest⟩ := hOk
            have hPa : P_a.mulVec (OneHotSimulates.ket β) = OneHotSimulates.ket β := by
              dsimp only [P_a]
              rw [UnsignedGivens.register_basisOutcomeProjector_zero_ket,
                ite_eq_left_of_eq_true _ _ (eq_true fun i ↦ by fin_cases i; exact hanc0)]
            have hT1 : Cs.1.mulVec (OneHotSimulates.ket β) =
                OneHotSimulates.ket (Function.update β anc (β anc + β c₁ * β c₂)) :=
              OneHotSimulates.ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β
            have hMid := hFixMid _ hOkRest hPb
            have hT2 : Cs.1.mulVec (OneHotSimulates.ket (Function.update β anc (β anc + β c₁ * β
                c₂))) =
                OneHotSimulates.ket β := by
              rw [← hT1, Matrix.mulVec_mulVec, hCs_mat_sq, Matrix.one_mulVec]
            simp only [← Matrix.mulVec_mulVec]
            rw [hPa, hT1, hMid, hT2]
      | andFree c₁ c₂ anc h₁₂ h₁a h₂a =>
          obtain ⟨hc₁W, hc₂W, haW⟩ := hsW
          let P_a := (QRegister.singleton anc).basisOutcomeProjector 0
          refine ⟨Cs.1 * (P_mid * P_a) * Cs.1, ?_⟩
          dsimp only
          rw [hDc_eq]
          refine ⟨?_, ?_, ?_⟩
          · exact DiagProjSimulates.revTempAnd v c₁ c₂ anc h₁₂ h₁a h₂a hSimMid (hCommMid anc haW)
          · intro q hqW
            by_cases hqa : q = anc
            · subst hqa
              exact OneHotSimulates.toffoli_conj_commutesWithWire_ancilla h₁₂ h₁a h₂a
                (hCommMid c₁ hc₁W) (hCommMid c₂ hc₂W) (hCommMid q hqW)
            · exact ((OneHotSimulates.CommutesWithWire.toffoli_of_ne_target h₁₂ h₁a h₂a hqa).mul
                (hCommMid q hqW)).mul
                (OneHotSimulates.CommutesWithWire.toffoli_of_ne_target h₁₂ h₁a h₂a hqa)
          · intro β hOk hPb
            obtain ⟨hancEq, hOkRest⟩ := hOk
            let β' := Function.update β anc (β anc + β c₁ * β c₂)
            have hT1 : Cs.1.mulVec (OneHotSimulates.ket β) = OneHotSimulates.ket β' :=
              OneHotSimulates.ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β
            have hanc0 : β' anc = 0 := by
              dsimp only [β']
              rw [Function.update_self, hancEq, CharTwo.add_self_eq_zero]
            have hPa : P_a.mulVec (OneHotSimulates.ket β') = OneHotSimulates.ket β' := by
              dsimp only [P_a]
              rw [UnsignedGivens.register_basisOutcomeProjector_zero_ket,
                ite_eq_left_of_eq_true _ _ (eq_true fun i ↦ by fin_cases i; exact hanc0)]
            have hMid := hFixMid β' hOkRest hPb
            have hT2 : Cs.1.mulVec (OneHotSimulates.ket β') = OneHotSimulates.ket β := by
              rw [← hT1, Matrix.mulVec_mulVec, hCs_mat_sq, Matrix.one_mulVec]
            simp only [← Matrix.mulVec_mulVec]
            rw [hT1, hPa, hMid, hT2]
/-- General valid-subspace conjugation theorem for any `RouterStep` sequence. -/
theorem DiagProjSimulates.routerSteps {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (W : Wire n → Prop)
    (steps : List (RouterStep n)) (hW : ∀ s ∈ steps, s.TouchesIn W)
    {P_body : Operator (2 ^ n)} {U_body U_tgt : Unitary (2 ^ n)} {body : DynamicCircuit Var n}
    (hBody : Lac2Fused184Select.DiagProjSimulates P_body U_body body)
    (hComm : ∀ q, W q → OneHotSimulates.CommutesWithWire q U_body.1)
    (S : BitAssignment n → Prop)
    (hOk : ∀ β, S β → routerStepsOk steps β)
    (hFixBody : ∀ β, S β →
      P_body.mulVec (OneHotSimulates.ket (routerStepsAssign steps β)) =
        OneHotSimulates.ket (routerStepsAssign steps β))
    (hEqU : ((routerStepsCircuit steps).eval⁻¹ * U_body * (routerStepsCircuit steps).eval).1 *
      Lac2Fused184Select.ketPredProj S = U_tgt.1 * Lac2Fused184Select.ketPredProj S)
    (hCommTgt : U_tgt.1 * Lac2Fused184Select.ketPredProj S =
      Lac2Fused184Select.ketPredProj S * U_tgt.1) :
    Lac2Fused184Select.DiagProjSimulates (Lac2Fused184Select.ketPredProj S) U_tgt
      (routerStepsProg v steps body) := by
  classical
  obtain ⟨P_out, hSim, _, hFix⟩ := routerSteps_raw v W steps hW hBody hComm
  have hSub : Lac2Fused184Select.ketPredProj S * P_out = Lac2Fused184Select.ketPredProj S := by
    rw [Lac2Fused184Select.IsDiagProj.comm ⟨S, rfl⟩ hSim.1]
    apply OneHotSimulates.matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, Lac2Fused184Select.ketPredProj_mulVec_ket]
    by_cases hS : S β
    · simp only [hS, ↓reduceIte]
      exact hFix β (hOk β hS) (hFixBody β hS)
    · simp [hS]
  exact hSim.tightenCongr ⟨S, rfl⟩ hSub hEqU hCommTgt
end CompactStepFast176Select

namespace CompactOuter9Bound50Core
open CompactStepFast176Select CompactStepFast176Select.StepCore Lac2Fused184Select
open StepEncK StepDecK
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge
theorem onlyUsesVar_unit_bound50 {n : ℕ} (P : DynamicCircuit Unit n) :
    Lac2Fused184Select.OnlyUsesVar () P := by
  induction P using DynamicCircuit.qcInd with
  | circuit _ => trivial
  | measure x _ => exact Subsingleton.elim x ()
  | qIf _ _ _ iht ihf =>
      exact ⟨fun _ _ h ↦ congrArg _ (funext fun u ↦ by cases u; exact h), iht, ihf⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
theorem diagProjSimulates_of_cleanRealizes_unit_bound50 {N k s : ℕ}
    (rAct : QRegister k N) (rWork : QRegister s N) (hdisj : rAct.DisjointWires rWork)
    (U : Unitary (2 ^ k)) (d : DynamicCircuit Unit N)
    (h : CleanDyn.CleanRealizes () rAct rWork U d) :
    Lac2Fused184Select.DiagProjSimulates (rWork.basisOutcomeProjector 0)
      (rAct.embedUnitary U) d :=
  Lac2Fused184Select.DiagProjSimulates.ofGlobalCleanSimulates
    (OneHotSimulates.GlobalCleanSimulates.ofRealizesEmbedded hdisj
      (Lac2Fused184Select.realizesEmbedded_of_cleanRealizes () rAct rWork U d
        (onlyUsesVar_unit_bound50 d) h))
theorem diagProjSimulates_seq_same_bound50 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {P : Operator (2 ^ n)} {U₁ U₂ : Unitary (2 ^ n)}
    {d₁ d₂ : DynamicCircuit Var n}
    (hd₁ : Lac2Fused184Select.DiagProjSimulates P U₁ d₁)
    (hd₂ : Lac2Fused184Select.DiagProjSimulates P U₂ d₂) :
    Lac2Fused184Select.DiagProjSimulates P (U₂ * U₁) (.seq d₁ d₂) := by
  have hP2 : P * P = P := hd₁.1.mul_self
  have hComm : (U₂ * U₁).1 * P = P * (U₂ * U₁).1 := by
    calc (U₂ * U₁).1 * P = U₂.1 * (U₁.1 * P) := by simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (U₂.1 * P) * U₁.1 := by rw [hd₁.2.1]; simp only [Matrix.mul_assoc]
      _ = P * (U₂ * U₁).1 := by rw [hd₂.2.1]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  refine ⟨hd₁.1, hComm, fun M ↦ ?_⟩
  obtain ⟨M₂, hwp₂, hproj₂⟩ := hd₂.2.2 M
  obtain ⟨M₁, hwp₁, hproj₁⟩ := hd₁.2.2 M₂
  refine ⟨M₁, by simp only [DynamicCircuit.compile_seq, wp, hwp₂, hwp₁], ?_⟩
  have hUP : U₁.1 * P = P * (U₁.1 * P) := by rw [hd₁.2.1, ← Matrix.mul_assoc, hP2]
  have hPU : P * U₁.1ᴴ = (P * U₁.1ᴴ) * P := by
    simpa only [Matrix.conjTranspose_mul, hd₁.1.conjTranspose_eq, Matrix.mul_assoc] using
      congrArg (·ᴴ) hUP
  calc P * M₁.1.1 * P
      = P * (U₁.1ᴴ * M₂.1.1 * U₁.1) * P := hproj₁
    _ = (P * U₁.1ᴴ) * M₂.1.1 * (U₁.1 * P) := by simp only [Matrix.mul_assoc]
    _ = ((P * U₁.1ᴴ) * P) * M₂.1.1 * (P * (U₁.1 * P)) := by nth_rw 1 [hPU, hUP]
    _ = (P * U₁.1ᴴ) * (P * M₂.1.1 * P) * (U₁.1 * P) := by simp only [Matrix.mul_assoc]
    _ = (P * U₁.1ᴴ) * (P * (U₂.1ᴴ * M.1.1 * U₂.1) * P) * (U₁.1 * P) := by rw [hproj₂]
    _ = ((P * U₁.1ᴴ) * P) * (U₂.1ᴴ * M.1.1 * U₂.1) * (P * (U₁.1 * P)) := by
          simp only [Matrix.mul_assoc]
    _ = P * ((U₂ * U₁).1ᴴ * M.1.1 * (U₂ * U₁).1) * P := by
          rw [← hPU, ← hUP]
          simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
theorem embedMatrix_comm_ketPredProj_bound50 {n k : ℕ}
    (r : QRegister k n) (A : Operator (2 ^ k)) (S : BitAssignment n → Prop)
    (hInv : ∀ (β : BitAssignment n) (l : Fin (2 ^ k)),
      S (writeRegBitsBound50 β r (basisBits k l)) ↔ S β) :
    r.embedMatrix A * Lac2Fused184Select.ketPredProj S =
      Lac2Fused184Select.ketPredProj S * r.embedMatrix A := by
  classical
  apply OneHotSimulates.matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Lac2Fused184Select.ketPredProj_mulVec_ket]
  have hket : OneHotSimulates.ket β = CoherentAlias.ket β := rfl
  by_cases hS : S β
  · simp only [hS, ↓reduceIte, hket]
    rw [embedMatrix_mulVec_ket_bound50, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Matrix.mulVec_smul]; congr 1; symm
    change (Lac2Fused184Select.ketPredProj S).mulVec (OneHotSimulates.ket _) = OneHotSimulates.ket _
    rw [Lac2Fused184Select.ketPredProj_mulVec_ket,
      ite_eq_left_of_eq_true _ _ (eq_true ((hInv β l).mpr hS))]
  · simp only [hS, ↓reduceIte, Matrix.mulVec_zero, hket]
    rw [embedMatrix_mulVec_ket_bound50, Matrix.mulVec_sum]; symm
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    rw [Matrix.mulVec_smul]
    change _ • (Lac2Fused184Select.ketPredProj S).mulVec (OneHotSimulates.ket _) = 0
    rw [Lac2Fused184Select.ketPredProj_mulVec_ket,
      ite_eq_right_of_eq_false _ _ (eq_false (mt (hInv β l).mp hS)), smul_zero]
end CompactOuter9Bound50Core

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open CircuitModular GivensOps
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactZeroCmp20OuterParam

namespace SelectRouter10
end SelectRouter10

namespace Lac2ZeroPar183Select
end Lac2ZeroPar183Select

namespace ZeroPar183CompactSelect
end ZeroPar183CompactSelect

namespace CompactFoldedSelect
end CompactFoldedSelect

namespace CompactStepFast175Core
end CompactStepFast175Core

namespace CompactStepFast176Select

end CompactStepFast176Select

namespace CompactOuter9Bound50Core

end CompactOuter9Bound50Core

namespace CompactOuter9Bound50Select

open CompactOuter9Bound50Core

end CompactOuter9Bound50Select

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Balanced160Select
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real
open QuantumComputation.Specs QuantumComputation.Specs.P450 CoherentAlias
open CircuitModular GivensOps
open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensCascade
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectRouter10
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Lac2Fused184Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Lac2Fused184SelectWrap
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Router10Lac2Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Phase2MidSandwich
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.PolymorphicFused184Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Lac2ZeroPar183Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ZeroPar183CompactSelect
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactFoldedSelect
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast176Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepEncK
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepDecK
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast175Core
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactOuter9Bound50Core
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactOuter9Bound50Select
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactTuned162StepWalk
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactTuned162StepZeroCmp20
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactZeroCmp20OuterParam
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepZeroCmp20OuterParam
open WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge CleanDyn
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OneHotSimulates
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowBal160Core (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1A: `145`-Leaf Table-Parametric Stage-2 Branch & `Phase2Bal161Layout` -/

/-- Positivity witness `1 ≤ 145` for `oneHotDecodeIdx` and `oneHotActiveLac2BranchUnitary`. -/
theorem h145Ge1 : 1 ≤ 145 := by decide

/-- Permuted `145 × 2 × 58` `Lac = 2` Givens angle table indexed by `orbitalOf`. -/
def p450Bal145OrbitalTable (orbitalOf : Fin 145 → Bool → Fin 319)
    (g : Fin 145) (s : Bool) (j : Fin 58) : ℕ :=
  let u := (orbitalOf g s).val
  UnsignedGivens.p450Split160Lac2Table ⟨u / 2, by have := (orbitalOf g s).isLt; omega⟩
    (decide (u % 2 = 1)) j

theorem p450Bal145OrbitalTable_bounds (orbitalOf : Fin 145 → Bool → Fin 319)
    (g : Fin 145) (s : Bool) :
    (∀ (p : ℕ) (_ : p + 1 < 58), p450Bal145OrbitalTable orbitalOf g s ⟨p, by omega⟩ < 8192) ∧
    2048 ≤ p450Bal145OrbitalTable orbitalOf g s ⟨0, by decide⟩ ∧
    p450Bal145OrbitalTable orbitalOf g s ⟨0, by decide⟩ < 6144 :=
  CircuitModular.UnsignedGivens.p450Split160Lac2Table_bounds _ _

/-- Toggles `actIdx10` in a `10`-bit control index according to `actFlipMask` on `pair8`. -/
noncomputable def flipActCtrl10_145 (actFlipMask : Fin 145 → Bool)
    (c10 : Fin (2 ^ 10)) : Fin (2 ^ 10) :=
  let b := basisBits 10 c10
  let j₀ := OneHotMux.oneHotDecodeIdx 8 145 h145Ge1 (fun i ↦ b (Lac2Fused184Select.selPair10 i))
  (basisBits 10).symm (Function.update b Lac2Fused184Select.actIdx10
    (b Lac2Fused184Select.actIdx10 + if actFlipMask j₀ then 1 else 0))

@[simp] theorem flipActCtrl10_145_involutive (actFlipMask : Fin 145 → Bool)
    (c10 : Fin (2 ^ 10)) :
    flipActCtrl10_145 actFlipMask (flipActCtrl10_145 actFlipMask c10) = c10 := by
  dsimp only [flipActCtrl10_145]
  have hsym := CircuitModular.UnsignedGivens.basisBits_symm_eq (Function.update (basisBits 10 c10)
    Lac2Fused184Select.actIdx10 (basisBits 10 c10 Lac2Fused184Select.actIdx10 +
      if actFlipMask (OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
        (fun i ↦ basisBits 10 c10 (Lac2Fused184Select.selPair10 i))) then 1 else 0))
  rw [hsym]
  have hp : (fun i ↦ Function.update (basisBits 10 c10) Lac2Fused184Select.actIdx10
      (basisBits 10 c10 Lac2Fused184Select.actIdx10 +
        if actFlipMask (OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
          (fun i ↦ basisBits 10 c10 (Lac2Fused184Select.selPair10 i))) then 1 else 0)
      (Lac2Fused184Select.selPair10 i)) =
      fun i ↦ basisBits 10 c10 (Lac2Fused184Select.selPair10 i) :=
    funext fun i ↦ Function.update_of_ne (by fin_cases i <;> decide) _ _
  rw [hp, Function.update_self, Function.update_idem, add_assoc, zmod2_add_self, add_zero,
    Function.update_eq_self]
  exact (basisBits 10).symm_apply_apply c10

/-- Raw `10`-bit Stage-2 phase-kick predicate (`act = 1 ∧ negMask j₀`). -/
noncomputable def ctrl10RawPhase145 (negMask : Fin 145 → Bool) (c10 : Fin (2 ^ 10)) : Bool :=
  decide (basisBits 10 c10 Lac2Fused184Select.actIdx10 = 1) &&
    negMask (OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
      (fun i ↦ basisBits 10 c10 (Lac2Fused184Select.selPair10 i)))

/-- Raw unphased `58`-qubit `10`-bit Stage-2 branch unitary for `p450Bal145OrbitalTable`. -/
noncomputable def phase2Bal145RawBranch (orbitalOf : Fin 145 → Bool → Fin 319)
    (c10 : Fin (2 ^ 10)) : Unitary (2 ^ 58) :=
  OneHotMux.oneHotActiveLac2BranchUnitary OneHotMux.h58_gt_1 h145Ge1
    (p450Bal145OrbitalTable orbitalOf) Lac2Fused184Select.actIdx10
    Lac2Fused184Select.selPair10 Lac2Fused184Select.subIdx10 c10

/-- Raw phased `58`-qubit `10`-bit Stage-2 branch unitary for `145` leaves. -/
noncomputable def phase2Bal145RawPhasedBranch (orbitalOf : Fin 145 → Bool → Fin 319)
    (negMask : Fin 145 → Bool) (c10 : Fin (2 ^ 10)) : Unitary (2 ^ 58) :=
  (if ctrl10RawPhase145 negMask c10 then negOneUnitary 58 else 1) *
    phase2Bal145RawBranch orbitalOf c10

/-- Effective `10`-bit phase predicate kicked by the `145`-leaf core. -/
noncomputable def ctrl10PhaseBal145 (actFlipMask : Fin 145 → Bool)
    (negMask : Fin 145 → Bool) (c10 : Fin (2 ^ 10)) : Bool :=
  ctrl10RawPhase145 negMask (flipActCtrl10_145 actFlipMask c10)

/-- Effective unphased `58`-qubit `10`-bit Stage-2 branch unitary for `145` leaves. -/
noncomputable def phase2Bal145Branch (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (c10 : Fin (2 ^ 10)) : Unitary (2 ^ 58) :=
  phase2Bal145RawBranch orbitalOf (flipActCtrl10_145 actFlipMask c10)

/-- Effective phased `58`-qubit `10`-bit Stage-2 branch unitary for `145` leaves. -/
noncomputable def phase2Bal145PhasedBranch (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (negMask : Fin 145 → Bool)
    (c10 : Fin (2 ^ 10)) : Unitary (2 ^ 58) :=
  phase2Bal145RawPhasedBranch orbitalOf negMask (flipActCtrl10_145 actFlipMask c10)

/-- Maps a raw `10`-bit `orbitalOf` control state `c10` to `phase2Ctrl10Branch`. -/
noncomputable def bal145RawToSplitCtrl10 (orbitalOf : Fin 145 → Bool → Fin 319)
    (c10 : Fin (2 ^ 10)) : Fin (2 ^ 10) :=
  let act := bitsOfFin 10 c10 Lac2Fused184Select.actIdx10
  let sub := bitsOfFin 10 c10 Lac2Fused184Select.subIdx10
  let j₀ := OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
    (fun i ↦ basisBits 10 c10 (Lac2Fused184Select.selPair10 i))
  let u := (orbitalOf j₀ sub).val
  let g' : Fin 160 := ⟨u / 2, by have := (orbitalOf j₀ sub).isLt; omega⟩
  finOfBits 10 fun l ↦
    if l = Lac2Fused184Select.subIdx10 then decide (u % 2 = 1)
    else if l = Lac2Fused184Select.actIdx10 then act
    else act && decide (g'.val / 2 ^ (l.val - 2) % 2 = 1)

theorem phase2Bal145RawBranch_eq_split (orbitalOf : Fin 145 → Bool → Fin 319)
    (c10 : Fin (2 ^ 10)) :
    phase2Bal145RawBranch orbitalOf c10 =
      Lac2Fused184Select.phase2Ctrl10Branch (bal145RawToSplitCtrl10 orbitalOf c10) := by
  let act := bitsOfFin 10 c10 Lac2Fused184Select.actIdx10
  let sub := bitsOfFin 10 c10 Lac2Fused184Select.subIdx10
  let j₀ := OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
    (fun i ↦ basisBits 10 c10 (Lac2Fused184Select.selPair10 i))
  let u := (orbitalOf j₀ sub).val
  let g' : Fin 160 := ⟨u / 2, by have := (orbitalOf j₀ sub).isLt; omega⟩
  let f10 : Fin 10 → Bool := fun l ↦
    if l = Lac2Fused184Select.subIdx10 then decide (u % 2 = 1)
    else if l = Lac2Fused184Select.actIdx10 then act
    else act && decide (g'.val / 2 ^ (l.val - 2) % 2 = 1)
  let c' := bal145RawToSplitCtrl10 orbitalOf c10
  have hbitsF (l : Fin 10) (b : Bool) (hf : f10 l = b) :
      basisBits 10 c' l = if b then 1 else 0 := by
    have hbf : bitsOfFin 10 c' l = b :=
      (congrFun (bitsOfFin_finOfBits 10 f10) l).trans hf
    have hb : bitsOfFin 10 c' l = decide (basisBits 10 c' l = 1) := rfl
    rw [hb] at hbf
    rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (basisBits 10 c' l) with h | h <;>
      cases b <;> simp_all
  have hfAct : f10 Lac2Fused184Select.actIdx10 = act := by
    dsimp only [f10]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have hfSub : f10 Lac2Fused184Select.subIdx10 = decide (u % 2 = 1) := by
    dsimp only [f10]; exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
  have hfPair (i : Fin 8) :
      f10 (Lac2Fused184Select.selPair10 i) =
        (act && decide (g'.val / 2 ^ i.val % 2 = 1)) := by
    have hne0 : Lac2Fused184Select.selPair10 i ≠ Lac2Fused184Select.subIdx10 := by
      fin_cases i <;> decide
    have hne1 : Lac2Fused184Select.selPair10 i ≠ Lac2Fused184Select.actIdx10 := by
      fin_cases i <;> decide
    have hsub2 : (Lac2Fused184Select.selPair10 i).val - 2 = i.val := by
      fin_cases i <;> rfl
    dsimp only [f10]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne0),
      ite_eq_right_of_eq_false _ _ (eq_false hne1), hsub2]
  change phase2Bal145RawBranch orbitalOf c10 = Lac2Fused184Select.phase2Ctrl10Branch c'
  rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one
      (basisBits 10 c10 Lac2Fused184Select.actIdx10) with ha0 | ha1
  · have hactF : act = false := by dsimp [act, bitsOfFin]; rw [ha0]; decide
    have hc'Act : basisBits 10 c' Lac2Fused184Select.actIdx10 = 0 :=
      hbitsF _ false (hfAct.trans hactF)
    dsimp only [phase2Bal145RawBranch, Lac2Fused184Select.phase2Ctrl10Branch]
    rw [OneHotMux.oneHotActiveLac2BranchUnitary_eq_one_of_act_zero _ _ _ _ _ _ ha0,
      OneHotMux.oneHotActiveLac2BranchUnitary_eq_one_of_act_zero _ _ _ _ _ _ hc'Act]
  · have hactT : act = true := by dsimp [act, bitsOfFin]; rw [ha1]; decide
    have hc'Act : basisBits 10 c' Lac2Fused184Select.actIdx10 = 1 :=
      hbitsF _ true (hfAct.trans hactT)
    have hc'Sub : decide (basisBits 10 c' Lac2Fused184Select.subIdx10 = 1) =
        decide (u % 2 = 1) :=
      (congrArg (fun x : ZMod 2 ↦ decide (x = 1))
        (hbitsF _ (decide (u % 2 = 1)) hfSub)).trans (by cases decide (u % 2 = 1) <;> decide)
    have hsubEq : decide (basisBits 10 c10 Lac2Fused184Select.subIdx10 = 1) = sub := rfl
    have hc'Pair : (fun i : Fin 8 ↦ basisBits 10 c' (Lac2Fused184Select.selPair10 i)) =
        basisBits 8 ⟨g'.val, by omega⟩ := by
      funext i
      rw [hbitsF _ (decide (g'.val / 2 ^ i.val % 2 = 1))
          ((hfPair i).trans (by rw [hactT, Bool.true_and])), basisBits_eq_div_mod]
      rcases Nat.mod_two_eq_zero_or_one (g'.val / 2 ^ i.val) with h0 | h1
      · rw [h0]; rfl
      · rw [h1]; rfl
    have hdecG' : OneHotMux.oneHotDecodeIdx 8 160 OneHotMux.h160_ge_1
        (fun i ↦ basisBits 10 c' (Lac2Fused184Select.selPair10 i)) = g' := by
      apply Fin.ext
      have hval : OneHotSimulates.bitsToNat
          (fun i ↦ basisBits 10 c' (Lac2Fused184Select.selPair10 i)) = g'.val := by
        rw [hc'Pair, OneHotSimulates.bitsToNat_basisBits]
      rw [OneHotMux.oneHotDecodeIdx_val_of_lt 8 160 OneHotMux.h160_ge_1 _ (hval ▸ g'.isLt), hval]
    dsimp only [phase2Bal145RawBranch, Lac2Fused184Select.phase2Ctrl10Branch]
    rw [OneHotMux.oneHotActiveLac2BranchUnitary_eq_singleSpinReflection_of_act_one _ _ _ _ _ _
        ha1 (p450Bal145OrbitalTable_bounds orbitalOf),
      OneHotMux.oneHotActiveLac2BranchUnitary_eq_singleSpinReflection_of_act_one _ _ _ _ _ _
        hc'Act CircuitModular.UnsignedGivens.p450Split160Lac2Table_bounds, hsubEq, hc'Sub, hdecG']
    rfl

theorem singleSpinReflectionUnitary_inv_bal145 (N : ℕ) (hN : 1 < N)
    (b : ℕ) (k : Fin N → ℤ) :
    (CircuitModular.UnsignedGivens.singleSpinReflectionUnitary N hN b k)⁻¹ =
      CircuitModular.UnsignedGivens.singleSpinReflectionUnitary N hN b k := by
  apply Subtype.ext
  change (CircuitModular.UnsignedGivens.singleSpinReflectionUnitary N hN b k).1ᴴ =
    (CircuitModular.UnsignedGivens.singleSpinReflectionUnitary N hN b k).1
  rw [CircuitModular.UnsignedGivens.singleSpinReflectionUnitary_val]
  dsimp only [GivensOps.singleSpinOrbitalNumberOp]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp

theorem phase2Ctrl10Branch_inv_bal145 (c10 : Fin (2 ^ 10)) :
    (Lac2Fused184Select.phase2Ctrl10Branch c10)⁻¹ =
      Lac2Fused184Select.phase2Ctrl10Branch c10 := by
  rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one
      (basisBits 10 c10 Lac2Fused184Select.actIdx10) with hact | hact1
  · rw [Lac2Fused184Select.phase2Ctrl10Branch,
      OneHotMux.oneHotActiveLac2BranchUnitary_eq_one_of_act_zero _ _ _ _ _ _ hact, inv_one]
  · rw [Lac2Fused184Select.phase2Ctrl10Branch,
      OneHotMux.oneHotActiveLac2BranchUnitary_eq_singleSpinReflection_of_act_one _ _ _ _ _
        _ hact1 CircuitModular.UnsignedGivens.p450Split160Lac2Table_bounds]
    exact singleSpinReflectionUnitary_inv_bal145 _ _ _ _

theorem phase2Bal145PhasedBranch_inv (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (negMask : Fin 145 → Bool) (c10 : Fin (2 ^ 10)) :
    (phase2Bal145PhasedBranch actFlipMask orbitalOf negMask c10)⁻¹ =
      phase2Bal145PhasedBranch actFlipMask orbitalOf negMask c10 := by
  apply unitary_self_inv_b; apply Subtype.ext
  dsimp only [phase2Bal145PhasedBranch, phase2Bal145RawPhasedBranch]
  have hsq :
      (phase2Bal145RawBranch orbitalOf (flipActCtrl10_145 actFlipMask c10)).1 *
        (phase2Bal145RawBranch orbitalOf (flipActCtrl10_145 actFlipMask c10)).1 = 1 := by
    rw [phase2Bal145RawBranch_eq_split]
    let u := Lac2Fused184Select.phase2Ctrl10Branch
      (bal145RawToSplitCtrl10 orbitalOf (flipActCtrl10_145 actFlipMask c10))
    have hm : u * u = 1 := by
      calc u * u = u⁻¹ * u := by rw [phase2Ctrl10Branch_inv_bal145]
        _ = 1 := inv_mul_cancel u
    simpa only [Submonoid.coe_mul, Submonoid.coe_one] using congrArg Subtype.val hm
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_one]
  cases ctrl10RawPhase145 negMask (flipActCtrl10_145 actFlipMask c10)
  · simp only [Bool.false_eq_true, ↓reduceIte, Submonoid.coe_one, one_mul]; exact hsq
  · simp only [↓reduceIte, negOneUnitary_val, smul_mul_assoc, mul_smul_comm, one_mul, smul_smul,
      neg_mul, neg_neg, one_smul]; exact hsq

/-- Decodes `pair8NatOf10 f10` into `Fin 145` (clamping to `0` if `≥ 145`). -/
def bal145DecodeJ0 (f10 : Fin 10 → Bool) : Fin 145 :=
  if h : pair8NatOf10 f10 < 145 then ⟨pair8NatOf10 f10, h⟩ else 0

/-- Effective Stage-2 active bit `xor (f10 1) (actFlipMask (bal145DecodeJ0 f10))`. -/
def bal145ActOf10 (actFlipMask : Fin 145 → Bool) (f10 : Fin 10 → Bool) : Bool :=
  xor (f10 1) (actFlipMask (bal145DecodeJ0 f10))

/-- Effective `Fin 319` orbital index `orbitalOf (bal145DecodeJ0 f10) (f10 0)`. -/
def bal145RowIdxOf10 (orbitalOf : Fin 145 → Bool → Fin 319) (f10 : Fin 10 → Bool) : Fin 319 :=
  orbitalOf (bal145DecodeJ0 f10) (f10 0)

/-- Effective Stage-2 phase bit `bal145ActOf10 && negMask (bal145DecodeJ0 f10)`. -/
def bal145PhaseOf10 (actFlipMask negMask : Fin 145 → Bool) (f10 : Fin 10 → Bool) : Bool :=
  bal145ActOf10 actFlipMask f10 && negMask (bal145DecodeJ0 f10)

theorem oneHotDecodeIdx145_finOfBits_eq (f10 : Fin 10 → Bool)
    (h145 : pair8NatOf10 f10 < 145) :
    OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
        (fun i ↦ basisBits 10 (finOfBits 10 f10) (Lac2Fused184Select.selPair10 i)) =
      bal145DecodeJ0 f10 := by
  have hbPair : (fun i : Fin 8 ↦
      basisBits 10 (finOfBits 10 f10) (Lac2Fused184Select.selPair10 i)) =
      fun i ↦ if f10 ⟨i.val + 2, by omega⟩ then (1 : ZMod 2) else 0 := by
    funext i
    have hs : Lac2Fused184Select.selPair10 i = ⟨i.val + 2, by omega⟩ := by fin_cases i <;> rfl
    rw [hs]; change (basisBits 10 (finOfBits 10 f10)) _ = _; simp [finOfBits]
  have hbn : OneHotSimulates.bitsToNat
      (fun i ↦ basisBits 10 (finOfBits 10 f10) (Lac2Fused184Select.selPair10 i)) =
      pair8NatOf10 f10 := by
    rw [hbPair, bitsToNat_pair8_eq_pair8NatOf10_b]
  apply Fin.ext
  rw [OneHotMux.oneHotDecodeIdx_val_of_lt 8 145 h145Ge1 _ (hbn ▸ h145), hbn]
  dsimp only [bal145DecodeJ0]; rw [dite_eq_left h145]

theorem flipActCtrl10_145_finOfBits (actFlipMask : Fin 145 → Bool) (f10 : Fin 10 → Bool)
    (h145 : pair8NatOf10 f10 < 145) :
    flipActCtrl10_145 actFlipMask (finOfBits 10 f10) =
      finOfBits 10 (fun l ↦ if l = 1 then bal145ActOf10 actFlipMask f10 else f10 l) := by
  have hbb (k : Fin 10) :
      basisBits 10 ((basisBits 10).symm (fun i ↦ if f10 i then 1 else 0)) k =
        if f10 k then (1 : ZMod 2) else 0 :=
    congrFun ((basisBits 10).apply_symm_apply _) k
  dsimp only [flipActCtrl10_145]
  rw [oneHotDecodeIdx145_finOfBits_eq f10 h145]
  dsimp only [finOfBits]
  refine congrArg (basisBits 10).symm (funext fun l ↦ ?_)
  by_cases hl : l = 1
  · subst hl
    have ha1 : (1 : Fin 10) = Lac2Fused184Select.actIdx10 := rfl
    rw [ha1, Function.update_self, hbb]
    change ((if f10 1 then (1 : ZMod 2) else 0) +
        if actFlipMask (bal145DecodeJ0 f10) then 1 else 0) =
      if bal145ActOf10 actFlipMask f10 then 1 else 0
    dsimp only [bal145ActOf10]
    exact (by decide : ∀ x y : Bool,
      ((if x then (1 : ZMod 2) else 0) + if y then 1 else 0) = if xor x y then 1 else 0)
      (f10 1) (actFlipMask (bal145DecodeJ0 f10))
  · have hl' : l ≠ Lac2Fused184Select.actIdx10 := hl
    rw [Function.update_of_ne hl', hbb l]; simp only [hl, ↓reduceIte]

theorem ctrl10PhaseBal145_finOfBits (actFlipMask negMask : Fin 145 → Bool)
    (f10 : Fin 10 → Bool) (h145 : pair8NatOf10 f10 < 145) :
    ctrl10PhaseBal145 actFlipMask negMask (finOfBits 10 f10) =
      bal145PhaseOf10 actFlipMask negMask f10 := by
  let fAct : Fin 10 → Bool := fun l ↦ if l = 1 then bal145ActOf10 actFlipMask f10 else f10 l
  have hpEq : pair8NatOf10 fAct = pair8NatOf10 f10 := rfl
  have hjEq : bal145DecodeJ0 fAct = bal145DecodeJ0 f10 := by
    dsimp only [bal145DecodeJ0]; simp only [hpEq]
  dsimp only [ctrl10PhaseBal145]
  rw [flipActCtrl10_145_finOfBits actFlipMask f10 h145]
  dsimp only [ctrl10RawPhase145, bal145PhaseOf10]
  rw [oneHotDecodeIdx145_finOfBits_eq fAct (hpEq.symm ▸ h145), hjEq]
  have ha : decide (basisBits 10 (finOfBits 10 fAct) Lac2Fused184Select.actIdx10 = 1) =
      bal145ActOf10 actFlipMask f10 :=
    congrFun (bitsOfFin_finOfBits 10 fAct) 1
  rw [ha]

theorem phase2Bal145Branch_finOfBits_eq_lac2 (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (f10 : Fin 10 → Bool)
    (h145 : pair8NatOf10 f10 < 145) :
    let u := (bal145RowIdxOf10 orbitalOf f10).val
    let z10 : Fin 10 → Bool := fun k ↦
      if k.val < 9 then decide (u / 2 ^ k.val % 2 = 1) else bal145ActOf10 actFlipMask f10
    phase2Bal145Branch actFlipMask orbitalOf (finOfBits 10 f10) =
      Router10Lac2Select.lac2PureReflBits z10 := by
  intro u z10
  let fAct : Fin 10 → Bool := fun l ↦ if l = 1 then bal145ActOf10 actFlipMask f10 else f10 l
  have hpEq : pair8NatOf10 fAct = pair8NatOf10 f10 := rfl
  have hjEq : bal145DecodeJ0 fAct = bal145DecodeJ0 f10 := by
    dsimp only [bal145DecodeJ0]; simp only [hpEq]
  dsimp only [phase2Bal145Branch]
  rw [flipActCtrl10_145_finOfBits actFlipMask f10 h145, phase2Bal145RawBranch_eq_split,
    ← phase2Ctrl10Branch_permMaskedFrom10_eq z10]
  let cF := finOfBits 10 fAct
  have ha : bitsOfFin 10 cF Lac2Fused184Select.actIdx10 = bal145ActOf10 actFlipMask f10 :=
    congrFun (bitsOfFin_finOfBits 10 fAct) 1
  have hs : bitsOfFin 10 cF Lac2Fused184Select.subIdx10 = f10 0 :=
    congrFun (bitsOfFin_finOfBits 10 fAct) 0
  have hu : (orbitalOf
      (OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
        (fun i ↦ basisBits 10 cF (Lac2Fused184Select.selPair10 i)))
      (bitsOfFin 10 cF Lac2Fused184Select.subIdx10)).val = u :=
    congrArg Fin.val (congrArg₂ orbitalOf
      ((oneHotDecodeIdx145_finOfBits_eq fAct (hpEq.symm ▸ h145)).trans hjEq) hs)
  unfold bal145RawToSplitCtrl10
  refine congrArg Lac2Fused184Select.phase2Ctrl10Branch
    (congrArg (finOfBits 10) (funext fun l ↦ ?_))
  match l with
  | ⟨0, h0⟩ =>
    have heq0 : (⟨0, h0⟩ : Fin 10) = Lac2Fused184Select.subIdx10 := Fin.ext rfl
    dsimp only [permMaskedFrom10, z10]
    rw [ite_eq_left heq0, ite_eq_left (show (0 : Fin 10).val < 9 by decide)]
    exact (congrArg (fun n ↦ decide (n % 2 = 1)) hu).trans
      (by rw [Fin.val_zero, Nat.pow_zero, Nat.div_one])
  | ⟨1, _⟩ => exact ha
  | ⟨k + 2, hk⟩ =>
    have hne0 : (⟨k + 2, hk⟩ : Fin 10) ≠ Lac2Fused184Select.subIdx10 := by
      intro h; have := congrArg Fin.val h; simp [Lac2Fused184Select.subIdx10] at this
    have hne1 : (⟨k + 2, hk⟩ : Fin 10) ≠ Lac2Fused184Select.actIdx10 := by
      intro h; have := congrArg Fin.val h; simp [Lac2Fused184Select.actIdx10] at this
    dsimp only [permMaskedFrom10, z10]
    rw [ite_eq_right hne0, ite_eq_right hne1, ite_eq_left (show k + 1 < 9 by omega)]
    refine congrArg₂ and ha ?_
    have hdiv : ∀ n : ℕ, (n / 2) / 2 ^ k = n / 2 ^ (k + 1) := fun n ↦ by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]
    exact (congrArg (fun n ↦ decide ((n / 2) / 2 ^ (k + 2 - 2) % 2 = 1)) hu).trans
      (by simp only [Nat.add_sub_cancel]; rw [hdiv])

theorem ite_negOneUnitary_embed_spinCat0_bal145 (p : Bool) :
    (spinCatSub 0).embedUnitary (if p then negOneUnitary 58 else 1) =
      if p then negOneUnitary (2 * 58 + 0) else 1 := by
  apply Subtype.ext; cases p
  · simp
  · simp only [↓reduceIte, QRegister.embedUnitary_val, negOneUnitary_val,
      QRegister.embedMatrix_smul, QRegister.embedMatrix_one]

theorem spinSwapPermUnitary_mul_self_bal145 :
    Operator.permutationUnitary (spinSwapEquiv 58) *
      Operator.permutationUnitary (spinSwapEquiv 58) = 1 := by
  apply Subtype.ext; ext i j
  have h := congrFun (Matrix.mulVec_mulVec (Pi.single j (1 : ℂ))
    (Operator.permutationUnitary (spinSwapEquiv 58)).1
    (Operator.permutationUnitary (spinSwapEquiv 58)).1) i
  rw [Operator.permutationUnitary_mulVec_single, Operator.permutationUnitary_mulVec_single,
    spinSwapEquiv_involutive, Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [Submonoid.coe_mul, OneMemClass.coe_one, ← h]
  simp only [Matrix.one_apply, Pi.single_apply]

theorem y12_bal145_eq_selectBranchUnitary (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (negMask : Fin 145 → Bool) (y12 : Fin 12 → Bool)
    (xo : Fin 256) (so : Fin 2) (b : Fin 32) (si : Fin 2)
    (h145 : pair8NatOf10 (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) < 145)
    (hen : bal145ActOf10 actFlipMask (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) = enROf xo b si)
    (hrow : bal145ActOf10 actFlipMask (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) = true →
      bal145RowIdxOf10 orbitalOf (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) = rowIdxOf xo b)
    (hsig : y12 10 = decide (sigSelOf xo so si = 1))
    (hph : xor (y12 11)
      (bal145PhaseOf10 actFlipMask negMask (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩)) =
      negPhaseOf xo b si) :
    selectGenCoreBranch 0
      (fun m10 ↦ phase2Bal145PhasedBranch actFlipMask orbitalOf negMask (finOfBits 10 m10)) y12 =
      selectBranchUnitary xo so b si := by
  let f10 : Fin 10 → Bool := fun j ↦ y12 ⟨j.val, by omega⟩
  let yRow : Fin 12 → Bool := fun j ↦
    if j.val < 9 then decide ((rowIdxOf xo b).val / 2 ^ j.val % 2 = 1)
    else if j.val = 9 then bal145ActOf10 actFlipMask f10
    else if j.val = 10 then y12 10
    else xor (y12 11) (bal145PhaseOf10 actFlipMask negMask f10)
  have hBr : phase2Bal145Branch actFlipMask orbitalOf (finOfBits 10 f10) =
      Router10Lac2Select.lac2PureReflBits (fun k : Fin 10 ↦ yRow ⟨k.val, by omega⟩) := by
    rw [phase2Bal145Branch_finOfBits_eq_lac2 actFlipMask orbitalOf f10 h145]
    by_cases hact : bal145ActOf10 actFlipMask f10 = true
    · congr 1; funext k; dsimp only [yRow]; rw [hrow hact]
      by_cases hk9 : k.val < 9
      · rw [ite_eq_left hk9, ite_eq_left hk9]
      · have hkEq9 : k.val = 9 := by omega
        rw [ite_eq_right hk9, ite_eq_right hk9, ite_eq_left hkEq9]
    · simp only [Bool.not_eq_true] at hact
      rw [Router10Lac2Select.lac2PureReflBits_of_false _ (by simp [hact]),
        Router10Lac2Select.lac2PureReflBits_of_false _ (by dsimp [yRow]; simp [hact])]
  have hGenEq : selectGenCoreBranch 0
      (fun m10 ↦ phase2Bal145PhasedBranch actFlipMask orbitalOf negMask (finOfBits 10 m10)) y12 =
      selectGenCoreBranch 0 Router10Lac2Select.lac2PureReflBits yRow := by
    apply Subtype.ext; dsimp only [selectGenCoreBranch]
    have hySig : y12 10 = yRow 10 := rfl
    have hy11 : yRow 11 = xor (y12 11) (bal145PhaseOf10 actFlipMask negMask f10) := rfl
    have hPhDef : phase2Bal145PhasedBranch actFlipMask orbitalOf negMask (finOfBits 10 f10) =
        (if ctrl10PhaseBal145 actFlipMask negMask (finOfBits 10 f10)
          then negOneUnitary 58 else 1) *
          phase2Bal145Branch actFlipMask orbitalOf (finOfBits 10 f10) := rfl
    rw [hySig, hPhDef, ctrl10PhaseBal145_finOfBits actFlipMask negMask f10 h145, hBr,
      (spinCatSub 0).embedUnitary_mul, ite_negOneUnitary_embed_spinCat0_bal145, hy11]
    cases y12 11 <;> cases bal145PhaseOf10 actFlipMask negMask f10 <;>
      simp [Submonoid.coe_mul, negOneUnitary_val]
  rw [hGenEq]
  refine selectGenCoreBranch_zero_eq_selectBranchUnitary
    Router10Lac2Select.lac2PureReflBits Router10Lac2Select.lac2PureReflBits_of_false
    Router10Lac2Select.lac2PureReflBits_of_true_lt319 xo so b si yRow ?_ ?_ ?_ ?_
  · have h9 : (fun j : Fin 9 ↦ yRow ⟨j.val, by omega⟩) =
        bitsOfFin 9 ⟨(rowIdxOf xo b).val, by have := (rowIdxOf xo b).isLt; omega⟩ := by
      funext j; dsimp only [yRow]; rw [ite_eq_left j.isLt, bitsOfFin_eq_div_mod_b]
    rw [h9, finOfBits_bitsOfFin]
  · exact hen
  · change (finOfBits 1 fun _ ↦ y12 10) = sigSelOf xo so si
    rw [hsig]; generalize sigSelOf xo so si = s; fin_cases s <;> decide
  · exact hph

theorem y12_bal145_eq_one_of_act_false (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (negMask : Fin 145 → Bool) (y12 : Fin 12 → Bool)
    (h145 : pair8NatOf10 (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) < 145)
    (hact : bal145ActOf10 actFlipMask (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) = false)
    (hsgn : y12 11 = false) :
    selectGenCoreBranch 0
      (fun m10 ↦ phase2Bal145PhasedBranch actFlipMask orbitalOf negMask (finOfBits 10 m10)) y12 =
      1 := by
  let f10 : Fin 10 → Bool := fun j ↦ y12 ⟨j.val, by omega⟩
  have hPh0 : ctrl10PhaseBal145 actFlipMask negMask (finOfBits 10 f10) = false := by
    rw [ctrl10PhaseBal145_finOfBits actFlipMask negMask f10 h145]
    dsimp [bal145PhaseOf10]; rw [hact, Bool.false_and]
  have hBr1 : phase2Bal145Branch actFlipMask orbitalOf (finOfBits 10 f10) = 1 := by
    rw [phase2Bal145Branch_finOfBits_eq_lac2 actFlipMask orbitalOf f10 h145]
    exact Router10Lac2Select.lac2PureReflBits_of_false _ hact
  have hPhBr1 : phase2Bal145PhasedBranch actFlipMask orbitalOf negMask (finOfBits 10 f10) = 1 := by
    change (if ctrl10PhaseBal145 actFlipMask negMask (finOfBits 10 f10)
      then negOneUnitary 58 else 1) *
      phase2Bal145Branch actFlipMask orbitalOf (finOfBits 10 f10) = 1
    rw [hPh0, hBr1]; simp
  dsimp only [selectGenCoreBranch]
  change (if y12 11 then negOneUnitary (2 * 58 + 0) else 1) *
    ((QRegister.block 0 (2 * 58) _).embedUnitary
      (if y12 10 then Operator.permutationUnitary (spinSwapEquiv 58) else 1) *
    ((spinCatSub 0).embedUnitary
      (phase2Bal145PhasedBranch actFlipMask orbitalOf negMask (finOfBits 10 f10)) *
    (QRegister.block 0 (2 * 58) _).embedUnitary
      (if y12 10 then Operator.permutationUnitary (spinSwapEquiv 58) else 1))) = 1
  rw [hsgn, ite_eq_right Bool.false_ne_true, one_mul, hPhBr1, QRegister.embedUnitary_one, one_mul,
    ← QRegister.embedUnitary_mul]
  cases y12 10
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one, QRegister.embedUnitary_one]
  · simp only [↓reduceIte, spinSwapPermUnitary_mul_self_bal145, QRegister.embedUnitary_one]

/-- `238`-wire Stage-2 core layout (`58` spin + `10` ctrl + `11` cat + `14` Givens rest +
`145` one-hot leaves = `58 + 10 + 11 + 159 = 238`). -/
structure Phase2Bal161Layout (n : ℕ) where
  /-- Underlying `238`-wire injective register. -/
  rFull : QRegister 238 n

namespace Phase2Bal161Layout

/-- `58`-wire spin target register (`rFull[0..57]`). -/
def rSpin {n : ℕ} (L : Phase2Bal161Layout n) : QRegister 58 n :=
  L.rFull.compose (QRegister.block 0 58 (by decide))

/-- `10`-wire Stage-2 control register (`rFull[58..67]`). -/
def rCtrl10 {n : ℕ} (L : Phase2Bal161Layout n) : QRegister 10 n :=
  L.rFull.compose (QRegister.block 58 10 (by decide))

/-- `11`-wire phase-gradient catalyst register (`rFull[68..78]`). -/
def rCat11 {n : ℕ} (L : Phase2Bal161Layout n) : QRegister 11 n :=
  L.rFull.compose (QRegister.block 68 11 (by decide))

/-- `159`-wire clean inner workspace (`rFull[79..237]`). -/
def rInner159 {n : ℕ} (L : Phase2Bal161Layout n) : QRegister 159 n :=
  L.rFull.compose (QRegister.block 79 159 (by decide))

/-- `14`-wire non-one-hot Givens workspace (`rInner159[0..13] = rFull[79..92]`). -/
def rGivRest14 {n : ℕ} (L : Phase2Bal161Layout n) : QRegister 14 n :=
  L.rInner159.compose (QRegister.block 0 14 (by decide))

/-- `145`-wire one-hot leaf register (`rInner159[14..158] = rFull[93..237]`). -/
def rOneHot145 {n : ℕ} (L : Phase2Bal161Layout n) : QRegister 145 n :=
  L.rInner159.compose (QRegister.block 14 145 (by decide))

/-- Sub-register bit `0` (`subIdx10 = 0`, `rFull 58`). -/
def wSub {n : ℕ} (L : Phase2Bal161Layout n) : Wire n :=
  L.rCtrl10 Lac2Fused184Select.subIdx10

/-- Active control wire (`actIdx10 = 1`, `rFull 59`). -/
def wAct {n : ℕ} (L : Phase2Bal161Layout n) : Wire n :=
  L.rCtrl10 Lac2Fused184Select.actIdx10

/-- `8`-wire binary leaf index register (`selPair10`, `rFull[60..67]`). -/
def rSelPair8 {n : ℕ} (L : Phase2Bal161Layout n) : QRegister 8 n :=
  L.rCtrl10.compose Lac2Fused184Select.selPair10

/-- Constant-`|1⟩` midpoint helper wire (`rGivRest14 0 = rFull 79`). -/
abbrev wOne {n : ℕ} (L : Phase2Bal161Layout n) : Wire n := L.rGivRest14 0

/-- Phase-kick target wire (`rGivRest14 1 = rFull 80`). -/
abbrev wPh {n : ℕ} (L : Phase2Bal161Layout n) : Wire n := L.rGivRest14 1

/-- Barrel-shift syndrome measurement wire (`rGivRest14 2 = rFull 81`). -/
abbrev qEnc {n : ℕ} (L : Phase2Bal161Layout n) : Wire n := L.rGivRest14 2

/-- Leaf `0` of `rOneHot145` (`rFull 93`), recycled as the `23`rd cascade work wire. -/
abbrev wHot0 {n : ℕ} (L : Phase2Bal161Layout n) : Wire n := L.rOneHot145 0

/-- `144`-wire tail `rOneHot145[1..144]` (`rFull[94..237]`). -/
abbrev rHot144 {n : ℕ} (L : Phase2Bal161Layout n) : QRegister 144 n :=
  OneHotMux.oneHotTailReg L.rOneHot145

theorem rSpin_eq {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin 58) :
    L.rSpin i = L.rFull ⟨i.val, by omega⟩ := by
  dsimp [rSpin, QRegister.block]; exact congrArg L.rFull (Fin.ext (Nat.zero_add i.val))

theorem rCtrl10_eq {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin 10) :
    L.rCtrl10 i = L.rFull ⟨58 + i.val, by omega⟩ := rfl

theorem rCat11_eq {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin 11) :
    L.rCat11 i = L.rFull ⟨68 + i.val, by omega⟩ := rfl

theorem rInner159_eq {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin 159) :
    L.rInner159 i = L.rFull ⟨79 + i.val, by omega⟩ := rfl

theorem rGivRest14_eq {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin 14) :
    L.rGivRest14 i = L.rFull ⟨79 + i.val, by omega⟩ := by
  dsimp only [rGivRest14]; rw [QRegister.compose_apply, L.rInner159_eq]; congr 1; ext; simp

theorem rOneHot145_eq {n : ℕ} (L : Phase2Bal161Layout n) (g : Fin 145) :
    L.rOneHot145 g = L.rFull ⟨93 + g.val, by omega⟩ := by
  dsimp only [rOneHot145]; rw [QRegister.compose_apply, L.rInner159_eq]; congr 1; ext; simp; omega

theorem rSelPair8_eq {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin 8) :
    L.rSelPair8 i = L.rFull ⟨60 + i.val, by omega⟩ := by
  have hs : (Lac2Fused184Select.selPair10 i).val = 2 + i.val := by fin_cases i <;> rfl
  dsimp [rSelPair8]; rw [rCtrl10_eq]; exact congrArg L.rFull (Fin.ext (by dsimp; omega))

theorem rFull_ne {n : ℕ} (L : Phase2Bal161Layout n) {a b : Fin 238} (hab : a.val ≠ b.val) :
    L.rFull a ≠ L.rFull b :=
  L.rFull.wires.injective.ne (fun h ↦ hab (congrArg Fin.val h))

end Phase2Bal161Layout

namespace Phase2Bal161Layout

theorem hsc {n : ℕ} (L : Phase2Bal161Layout n) : L.rSpin.DisjointWires L.rCtrl10 :=
  QRegister.disjoint_iff.mpr fun i j ↦ by
    rw [L.rSpin_eq, L.rCtrl10_eq]; exact L.rFull_ne (by dsimp; omega)

theorem hac {n : ℕ} (L : Phase2Bal161Layout n) :
    (L.rSpin.concat L.rCtrl10 L.hsc).DisjointWires L.rCat11 :=
  QRegister.disjoint_iff.mpr fun ij k ↦ by
    rw [L.rCat11_eq]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) ij
    · rw [QRegister.concat_apply_left, L.rSpin_eq]; exact L.rFull_ne (by dsimp; omega)
    · rw [QRegister.concat_apply_right, L.rCtrl10_eq]; exact L.rFull_ne (by dsimp; omega)

theorem hPairGiv14 {n : ℕ} (L : Phase2Bal161Layout n) :
    L.rSelPair8.DisjointWires L.rGivRest14 :=
  QRegister.disjoint_iff.mpr fun i j ↦ by
    rw [L.rSelPair8_eq, L.rGivRest14_eq]; exact L.rFull_ne (by dsimp; omega)

/-- `22`-wire Givens cascade workspace (`rSelPair8 ++ rGivRest14`). -/
def rGivens22 {n : ℕ} (L : Phase2Bal161Layout n) : QRegister (8 + 14) n :=
  L.rSelPair8.concat L.rGivRest14 L.hPairGiv14

theorem rGivens22_in_rFull {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin (8 + 14)) :
    ∃ k : Fin 238, L.rGivens22 i = L.rFull k ∧ 60 ≤ k.val ∧ k.val < 93 ∧ k.val < 68 ∨
      L.rGivens22 i = L.rFull k ∧ 79 ≤ k.val ∧ k.val < 93 := by
  refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i
  · refine ⟨⟨60 + a.val, by omega⟩, Or.inl ⟨?_, by dsimp; omega, by dsimp; omega, by dsimp; omega⟩⟩
    dsimp [rGivens22]; rw [QRegister.concat_apply_left, L.rSelPair8_eq]
  · refine ⟨⟨79 + b.val, by omega⟩, Or.inr ⟨?_, by dsimp; omega, by dsimp; omega⟩⟩
    dsimp [rGivens22]; rw [QRegister.concat_apply_right, L.rGivRest14_eq]

theorem hSubHot144 {n : ℕ} (L : Phase2Bal161Layout n) :
    (QRegister.singleton L.wSub).DisjointWires L.rHot144 :=
  QRegister.disjoint_iff.mpr fun _ g ↦ by
    rw [QRegister.singleton_apply]; dsimp [wSub, rHot144, OneHotMux.oneHotTailReg]
    rw [L.rCtrl10_eq, L.rOneHot145_eq]
    exact L.rFull_ne (by dsimp [Lac2Fused184Select.subIdx10]; omega)

theorem hActSubHot144 {n : ℕ} (L : Phase2Bal161Layout n) :
    (QRegister.singleton L.wAct).DisjointWires
      ((QRegister.singleton L.wSub).concat L.rHot144 L.hSubHot144) :=
  QRegister.disjoint_iff.mpr fun _ j ↦ by
    rw [QRegister.singleton_apply]; dsimp [wAct]; rw [L.rCtrl10_eq]
    refine Fin.addCases (fun _ ↦ ?_) (fun g ↦ ?_) j
    · rw [QRegister.concat_apply_left, QRegister.singleton_apply]
      dsimp [wSub]; rw [L.rCtrl10_eq]
      exact L.rFull_ne
        (by dsimp [Lac2Fused184Select.actIdx10, Lac2Fused184Select.subIdx10]; omega)
    · rw [QRegister.concat_apply_right]; dsimp [rHot144, OneHotMux.oneHotTailReg]
      rw [L.rOneHot145_eq]
      exact L.rFull_ne (by dsimp [Lac2Fused184Select.actIdx10]; omega)

/-- `146`-wire cascade control register `[wAct] ++ ([wSub] ++ rHot144)`. -/
abbrev rCtrlTail146 {n : ℕ} (L : Phase2Bal161Layout n) : QRegister (1 + (1 + 144)) n :=
  (QRegister.singleton L.wAct).concat
    ((QRegister.singleton L.wSub).concat L.rHot144 L.hSubHot144) L.hActSubHot144

theorem rCtrlTail146_in_rFull {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin (1 + (1 + 144))) :
    ∃ k : Fin 238, L.rCtrlTail146 i = L.rFull k ∧ (k.val = 58 ∨ k.val = 59 ∨ 94 ≤ k.val) := by
  refine Fin.addCases (fun _ ↦ ⟨⟨59, by decide⟩, ?_, Or.inr (Or.inl rfl)⟩)
    (Fin.addCases (fun _ ↦ ⟨⟨58, by decide⟩, ?_, Or.inl rfl⟩)
      (fun g ↦ ⟨⟨94 + g.val, by omega⟩, ?_, Or.inr (Or.inr (by dsimp; omega))⟩)) i
  · dsimp [rCtrlTail146]; rw [QRegister.concat_apply_left, QRegister.singleton_apply]
    dsimp [wAct]; rw [L.rCtrl10_eq]; rfl
  · dsimp [rCtrlTail146]
    rw [QRegister.concat_apply_right, QRegister.concat_apply_left, QRegister.singleton_apply]
    dsimp [wSub]; rw [L.rCtrl10_eq]; rfl
  · dsimp [rCtrlTail146]
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
    dsimp [rHot144, OneHotMux.oneHotTailReg]; rw [L.rOneHot145_eq]
    exact congrArg L.rFull (Fin.ext (by dsimp; omega))

theorem hSpinTail146 {n : ℕ} (L : Phase2Bal161Layout n) :
    L.rSpin.DisjointWires L.rCtrlTail146 :=
  QRegister.disjoint_iff.mpr fun i j ↦ by
    obtain ⟨k, hk, _⟩ := L.rCtrlTail146_in_rFull j
    rw [L.rSpin_eq, hk]; exact L.rFull_ne (by dsimp; omega)

theorem hSpinTail146Cat {n : ℕ} (L : Phase2Bal161Layout n) :
    (L.rSpin.concat L.rCtrlTail146 L.hSpinTail146).DisjointWires L.rCat11 :=
  QRegister.disjoint_iff.mpr fun ij m ↦ by
    rw [L.rCat11_eq]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) ij
    · rw [QRegister.concat_apply_left, L.rSpin_eq]; exact L.rFull_ne (by dsimp; omega)
    · obtain ⟨k, hk, _⟩ := L.rCtrlTail146_in_rFull j
      rw [QRegister.concat_apply_right, hk]; exact L.rFull_ne (by dsimp; omega)

theorem hGiv22Hot0 {n : ℕ} (L : Phase2Bal161Layout n) :
    L.rGivens22.DisjointWires (QRegister.singleton L.wHot0) :=
  QRegister.disjoint_iff.mpr fun i _ ↦ by
    rw [QRegister.singleton_apply]; dsimp [wHot0]; rw [L.rOneHot145_eq]
    rcases L.rGivens22_in_rFull i with ⟨k, ⟨hk, _, _, _⟩ | ⟨hk, _, _⟩⟩ <;>
      (rw [hk]; exact L.rFull_ne (by dsimp; omega))

theorem hSpinTail146CatGiv22Hot0 {n : ℕ} (L : Phase2Bal161Layout n) :
    ((L.rSpin.concat L.rCtrlTail146 L.hSpinTail146).concat L.rCat11
      L.hSpinTail146Cat).DisjointWires
      (L.rGivens22.concat (QRegister.singleton L.wHot0) L.hGiv22Hot0) :=
  QRegister.disjoint_iff.mpr fun ijm uv ↦ by
    have hR : ∃ kr : Fin 238,
        (L.rGivens22.concat (QRegister.singleton L.wHot0) L.hGiv22Hot0) uv = L.rFull kr ∧
        ((60 ≤ kr.val ∧ kr.val < 68) ∨ (79 ≤ kr.val ∧ kr.val ≤ 93)) := by
      refine Fin.addCases (fun u ↦ ?_) (fun _ ↦ ?_) uv
      · rcases L.rGivens22_in_rFull u with ⟨kr, ⟨h, h1, _, h2⟩ | ⟨h, h1, h2⟩⟩
        · exact ⟨kr, by rw [QRegister.concat_apply_left, h], Or.inl ⟨h1, h2⟩⟩
        · exact ⟨kr, by rw [QRegister.concat_apply_left, h], Or.inr ⟨h1, by omega⟩⟩
      · refine ⟨⟨93, by decide⟩, ?_, Or.inr ⟨by decide, by decide⟩⟩
        rw [QRegister.concat_apply_right, QRegister.singleton_apply]
        dsimp [wHot0]; rw [L.rOneHot145_eq]; rfl
    obtain ⟨kr, hkr, _⟩ := hR; rw [hkr]
    refine Fin.addCases (fun ij ↦ ?_) (fun m ↦ ?_) ijm
    · rw [QRegister.concat_apply_left]
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) ij
      · rw [QRegister.concat_apply_left, L.rSpin_eq]; exact L.rFull_ne (by dsimp; omega)
      · obtain ⟨kl, hkl, _⟩ := L.rCtrlTail146_in_rFull j
        rw [QRegister.concat_apply_right, hkl]; exact L.rFull_ne (by dsimp; omega)
    · rw [QRegister.concat_apply_right, L.rCat11_eq]; exact L.rFull_ne (by dsimp; omega)

end Phase2Bal161Layout

/-- Active control index `0` inside `rCtrlTail146`. -/
abbrev actIdx146 : Fin (1 + (1 + 144)) := Fin.castAdd (1 + 144) 0

/-- Sub-register index `1` inside `rCtrlTail146`. -/
abbrev subIdx146 : Fin (1 + (1 + 144)) := Fin.natAdd 1 (Fin.castAdd 144 0)

/-- `144`-wire one-hot tail selector inside `rCtrlTail146`. -/
abbrev selHot144 : QRegister 144 (1 + (1 + 144)) :=
  ⟨⟨fun g ↦ Fin.natAdd 1 (Fin.natAdd 1 g),
    fun _ _ h ↦ by simpa [Fin.ext_iff] using h⟩⟩

theorem rCtrlTail146_hot {n : ℕ} (L : Phase2Bal161Layout n) (g : Fin 144) :
    L.rCtrlTail146 (selHot144 g) = L.rOneHot145 g.succ := by
  have hs : selHot144 g = Fin.natAdd 1 (Fin.natAdd 1 g) := rfl
  dsimp only [Phase2Bal161Layout.rCtrlTail146]
  rw [hs, QRegister.concat_apply_right, QRegister.concat_apply_right]
  rfl

/-- Expands a `10`-bit `(sub, act, pair8)` control state to `1 + (1 + 144)` tail bits. -/
noncomputable def ctrl10ToTail146Bits (c10 : Fin (2 ^ 10)) :
    Fin (1 + (1 + 144)) → ZMod 2 :=
  let j₀ := OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
    (fun i ↦ basisBits 10 c10 (Lac2Fused184Select.selPair10 i))
  Fin.addCases (fun _ ↦ basisBits 10 c10 Lac2Fused184Select.actIdx10)
    (Fin.addCases (fun _ ↦ basisBits 10 c10 Lac2Fused184Select.subIdx10)
      (fun g ↦ if g.succ = j₀ then 1 else 0))

/-- Index in `Fin (2 ^ (1 + (1 + 144)))` of `ctrl10ToTail146Bits c10`. -/
noncomputable def ctrl10ToTail146Idx (c10 : Fin (2 ^ 10)) :
    Fin (2 ^ (1 + (1 + 144))) :=
  (basisBits (1 + (1 + 144))).symm (ctrl10ToTail146Bits c10)

theorem affCascadeBranch_bal145_ctrl10ToTail146Idx
    (orbitalOf : Fin 145 → Bool → Fin 319) (c10 : Fin (2 ^ 10)) :
    CompactStepFast176Select.UnsignedGivens.affineUnsignedBilinearLac2CascadeCtrlUnitary
        OneHotMux.h58_gt_1 (p450Bal145OrbitalTable orbitalOf) actIdx146 selHot144 subIdx146
        (ctrl10ToTail146Idx c10) =
      phase2Bal145RawBranch orbitalOf c10 := by
  open CompactStepFast176Select.UnsignedGivens in
  let c := ctrl10ToTail146Idx c10
  let j₀ := OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
    (fun i ↦ basisBits 10 c10 (Lac2Fused184Select.selPair10 i))
  have hbits : basisBits (1 + (1 + 144)) c = ctrl10ToTail146Bits c10 :=
    CircuitModular.UnsignedGivens.basisBits_symm_eq (ctrl10ToTail146Bits c10)
  have hact : basisBits (1 + (1 + 144)) c actIdx146 =
      basisBits 10 c10 Lac2Fused184Select.actIdx10 := by
    rw [hbits]; dsimp only [ctrl10ToTail146Bits, actIdx146]; rw [Fin.addCases_left]
  have hsub : basisBits (1 + (1 + 144)) c subIdx146 =
      basisBits 10 c10 Lac2Fused184Select.subIdx10 := by
    rw [hbits]; dsimp only [ctrl10ToTail146Bits, subIdx146]
    rw [Fin.addCases_right, Fin.addCases_left]
  have hhot : CircuitModular.UnsignedGivens.ctrlHotBits selHot144 c =
      fun g : Fin 144 ↦ if g.succ = j₀ then (1 : ZMod 2) else 0 := by
    funext g; change basisBits (1 + (1 + 144)) c (Fin.natAdd 1 (Fin.natAdd 1 g)) = _
    rw [hbits]; dsimp only [ctrl10ToTail146Bits]
    rw [Fin.addCases_right, Fin.addCases_right]
  dsimp only [phase2Bal145RawBranch]
  rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one
      (basisBits 10 c10 Lac2Fused184Select.actIdx10) with ha0 | ha1
  · rw [OneHotMux.oneHotActiveLac2BranchUnitary_eq_one_of_act_zero OneHotMux.h58_gt_1 h145Ge1
      (p450Bal145OrbitalTable orbitalOf) Lac2Fused184Select.actIdx10
      Lac2Fused184Select.selPair10 Lac2Fused184Select.subIdx10 ha0]
    exact affineUnsignedBilinearLac2CascadeCtrlUnitary_eq_one_of_act_zero
      OneHotMux.h58_gt_1 (p450Bal145OrbitalTable orbitalOf) actIdx146 selHot144 subIdx146
      (hact.trans ha0) (by
        rw [hhot]; intro a b hab
        by_cases ha : a.succ = j₀
        · right; have hb : b.succ ≠ j₀ := fun h ↦ hab (Fin.succ_inj.mp (ha.trans h.symm))
          simp [hb]
        · left; simp [ha])
  · rw [OneHotMux.oneHotActiveLac2BranchUnitary_eq_singleSpinReflection_of_act_one
      OneHotMux.h58_gt_1
      h145Ge1 (p450Bal145OrbitalTable orbitalOf) Lac2Fused184Select.actIdx10
      Lac2Fused184Select.selPair10 Lac2Fused184Select.subIdx10 ha1
      (p450Bal145OrbitalTable_bounds orbitalOf)]
    have hb := p450Bal145OrbitalTable_bounds orbitalOf j₀
      (decide (basisBits 10 c10 Lac2Fused184Select.subIdx10 = 1))
    have hExtOh : CircuitModular.UnsignedGivens.IsOneHotBits j₀
        (extendHot0 (CircuitModular.UnsignedGivens.ctrlHotBits selHot144 c)) := by
      rw [hhot]
      cases j₀ using Fin.cases with
      | zero =>
          exact isOneHotBits_extendHot0_of_zero fun g ↦
            ite_eq_right_of_eq_false _ _ (eq_false (Fin.succ_ne_zero g))
      | succ g₀ =>
          exact isOneHotBits_extendHot0_of_succ
            ⟨by simp, fun g hne ↦
              ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hne (Fin.succ_inj.mp h)))⟩
    have hres := affineUnsignedBilinearLac2CascadeCtrlUnitary_eq_singleSpinReflection
      OneHotMux.h58_gt_1 (p450Bal145OrbitalTable orbitalOf) actIdx146 selHot144 subIdx146
      (hact.trans ha1) hExtOh (by simpa only [hsub] using hb.1)
      (by simpa only [hsub] using hb.2.1) (by simpa only [hsub] using hb.2.2)
    simpa only [hsub] using hres

/-! ## Section 1B: `145`-Leaf Stage-2 Core (`11,818 T`, `0 TOFF`, `159` Clean Wires) -/

/-- Starting index in `Fin 145` of block `b : Fin 6` (`0, 32, 64, 96, 128, 144`). -/
def leafBase145 (b : Fin 6) : ℕ :=
  if b.val < 5 then 32 * b.val else 144

/-- Leaf capacity of block `b : Fin 6` (`32, 32, 32, 32, 16, 1`). -/
def leafCap145 (b : Fin 6) : ℕ :=
  if b.val < 4 then 32 else if b.val = 4 then 16 else 1

theorem leafCap145_pos (b : Fin 6) : 0 < leafCap145 b := by
  have := b.isLt; dsimp [leafCap145]; split_ifs <;> omega

/-- Combined leaf index `leafBase145 b + p` inside `Fin 145`. -/
def leafIdx145 (b : Fin 6) (p : ℕ) (hp : p < leafCap145 b) : Fin 145 :=
  ⟨leafBase145 b + p, by
    have := b.isLt; dsimp [leafBase145, leafCap145] at hp ⊢; split_ifs at hp ⊢ <;> omega⟩

/-- One-hot wire for block `b : Fin 6` and intra-block offset `p < leafCap145 b`. -/
abbrev wLeaf145 {n : ℕ} (L : Phase2Bal161Layout n) (b : Fin 6) (p : ℕ)
    (hp : p < leafCap145 b) : Wire n :=
  L.rOneHot145 (leafIdx145 b p hp)

theorem leafIdx145_inj {b₁ b₂ : Fin 6} {p₁ p₂ : ℕ} {h₁ : p₁ < leafCap145 b₁}
    {h₂ : p₂ < leafCap145 b₂} (heq : leafIdx145 b₁ p₁ h₁ = leafIdx145 b₂ p₂ h₂) :
    b₁ = b₂ ∧ p₁ = p₂ := by
  have hb1 := b₁.isLt; have hb2 := b₂.isLt
  have hv := congrArg Fin.val heq
  dsimp [leafIdx145, leafBase145, leafCap145] at h₁ h₂ hv
  split_ifs at h₁ h₂ hv <;> exact ⟨Fin.ext (by omega), by omega⟩

theorem wLeaf145_inj {n : ℕ} (L : Phase2Bal161Layout n) {b₁ b₂ : Fin 6} {p₁ p₂ : ℕ}
    {h₁ : p₁ < leafCap145 b₁} {h₂ : p₂ < leafCap145 b₂}
    (heq : wLeaf145 L b₁ p₁ h₁ = wLeaf145 L b₂ p₂ h₂) :
    b₁ = b₂ ∧ p₁ = p₂ :=
  leafIdx145_inj (L.rOneHot145.wires.injective heq)

theorem oh145_ne_pair {n : ℕ} (L : Phase2Bal161Layout n) (g : Fin 145) (i : Fin 8) :
    L.rOneHot145 g ≠ L.rSelPair8 i := by
  rw [L.rOneHot145_eq, L.rSelPair8_eq]; exact L.rFull_ne (by dsimp; omega)

theorem oh145_ne_rest {n : ℕ} (L : Phase2Bal161Layout n) (g : Fin 145) (j : Fin 14) :
    L.rOneHot145 g ≠ L.rGivRest14 j := by
  rw [L.rOneHot145_eq, L.rGivRest14_eq]; exact L.rFull_ne (by dsimp; omega)

theorem oh145_ne_wAct {n : ℕ} (L : Phase2Bal161Layout n) (g : Fin 145) :
    L.rOneHot145 g ≠ L.wAct := by
  dsimp [Phase2Bal161Layout.wAct]; rw [L.rOneHot145_eq, L.rCtrl10_eq]
  exact L.rFull_ne (by dsimp [Lac2Fused184Select.actIdx10]; omega)

theorem rest14_ne_pair {n : ℕ} (L : Phase2Bal161Layout n) (j : Fin 14) (i : Fin 8) :
    L.rGivRest14 j ≠ L.rSelPair8 i := by
  rw [L.rGivRest14_eq, L.rSelPair8_eq]; exact L.rFull_ne (by dsimp; omega)

theorem pair_ne_pair {n : ℕ} (L : Phase2Bal161Layout n) {i j : Fin 8} (h : i ≠ j) :
    L.rSelPair8 i ≠ L.rSelPair8 j :=
  L.rSelPair8.wires.injective.ne h

theorem act145_ne_pair {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin 8) :
    L.wAct ≠ L.rSelPair8 i := by
  dsimp [Phase2Bal161Layout.wAct, Phase2Bal161Layout.rSelPair8]
  exact L.rCtrl10.wires.injective.ne (by fin_cases i <;> decide)

/-- Valid `159`-inner-clean Stage-2 entry predicate (`pair8 < 145` and `rInner159 = 0`). -/
def sValid145 {n : ℕ} (L : Phase2Bal161Layout n) (β : BitAssignment n) : Prop :=
  (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 145 ∧
    ∀ idx : Fin 159, β (L.rInner159 idx) = 0

/-- `6`-block index for `x < 145` (`x / 32` for `x < 144`, `5` for `x = 144`). -/
noncomputable def b0E145 {n : ℕ} (L : Phase2Bal161Layout n) (β : BitAssignment n) : Fin 6 :=
  let x := (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val
  if hx : x < 144 then ⟨x / 32, by omega⟩ else 5

/-- Intra-block leaf offset for `x < 145` (`x % 32` for `x < 144`, `0` for `x = 144`). -/
noncomputable def loE145 {n : ℕ} (L : Phase2Bal161Layout n) (β : BitAssignment n) : ℕ :=
  let x := (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val
  if x < 144 then x % 32 else 0

theorem loE145_lt_cap_all {n : ℕ} (L : Phase2Bal161Layout n) (β : BitAssignment n) :
    loE145 L β < leafCap145 (b0E145 L β) := by
  by_cases hx144 : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144
  · have hb0 : (b0E145 L β).val = (UnsignedGivens.localIdx L.rSelPair8 β).val / 32 := by
      rw [b0E145, dite_eq_left hx144]
    have hlo : loE145 L β = (UnsignedGivens.localIdx L.rSelPair8 β).val % 32 := ite_eq_left hx144
    rw [hlo]; dsimp [leafCap145]; rw [hb0]; split_ifs <;> omega
  · have hb0 : (b0E145 L β).val = 5 := by rw [b0E145, dite_eq_right hx144]; rfl
    have hlo : loE145 L β = 0 := ite_eq_right hx144
    rw [hlo]; dsimp [leafCap145]; rw [hb0]; split_ifs <;> omega

theorem loE145_lt_cap {n : ℕ} {L : Phase2Bal161Layout n} {β : BitAssignment n}
    (_hS : sValid145 L β) : loE145 L β < leafCap145 (b0E145 L β) :=
  loE145_lt_cap_all L β

theorem leafBase_add_loE145 {n : ℕ} {L : Phase2Bal161Layout n} {β : BitAssignment n}
    (hS : sValid145 L β) :
    leafBase145 (b0E145 L β) + loE145 L β = (UnsignedGivens.localIdx L.rSelPair8 β).val := by
  have hx := hS.1
  by_cases hx144 : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144
  · have hb0 : (b0E145 L β).val = (UnsignedGivens.localIdx L.rSelPair8 β).val / 32 := by
      rw [b0E145, dite_eq_left hx144]
    have hlo : loE145 L β = (UnsignedGivens.localIdx L.rSelPair8 β).val % 32 := ite_eq_left hx144
    dsimp [leafBase145]; rw [hb0, hlo]; split_ifs <;> omega
  · have hb0 : (b0E145 L β).val = 5 := by rw [b0E145, dite_eq_right hx144]; rfl
    have hlo : loE145 L β = 0 := ite_eq_right hx144
    dsimp [leafBase145]; rw [hb0, hlo]; split_ifs <;> omega

theorem b0E145_of_lt144 {n : ℕ} {L : Phase2Bal161Layout n} {β : BitAssignment n}
    (hx : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144) :
    b0E145 L β = ⟨(UnsignedGivens.localIdx L.rSelPair8 β).val / 32, by omega⟩ := dite_eq_left hx
theorem b0E145_of_not_lt144 {n : ℕ} {L : Phase2Bal161Layout n} {β : BitAssignment n}
    (hx : ¬ (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144) :
    b0E145 L β = 5 := dite_eq_right hx
theorem loE145_of_lt144 {n : ℕ} {L : Phase2Bal161Layout n} {β : BitAssignment n}
    (hx : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144) :
    loE145 L β = (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val % 32 := ite_eq_left hx
theorem loE145_of_not_lt144 {n : ℕ} {L : Phase2Bal161Layout n} {β : BitAssignment n}
    (hx : ¬ (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144) :
    loE145 L β = 0 := ite_eq_right hx
theorem b0E145_congr {n : ℕ} (L : Phase2Bal161Layout n) {β₁ β₂ : BitAssignment n}
    (h : UnsignedGivens.localIdx L.rSelPair8 β₁ = UnsignedGivens.localIdx L.rSelPair8 β₂) :
    b0E145 L β₁ = b0E145 L β₂ := by dsimp only [b0E145]; simp_rw [h]
theorem loE145_congr {n : ℕ} (L : Phase2Bal161Layout n) {β₁ β₂ : BitAssignment n}
    (h : UnsignedGivens.localIdx L.rSelPair8 β₁ = UnsignedGivens.localIdx L.rSelPair8 β₂) :
    loE145 L β₁ = loE145 L β₂ := by dsimp only [loE145]; simp_rw [h]
private theorem wLeaf145_congr {n : ℕ} (L : Phase2Bal161Layout n) (b : Fin 6) {p₁ p₂ : ℕ}
    (hp₁ : p₁ < leafCap145 b) (hp₂ : p₂ < leafCap145 b) (h : p₁ = p₂) :
    wLeaf145 L b p₁ hp₁ = wLeaf145 L b p₂ hp₂ := by subst h; rfl

theorem oh145_zero_of_sValid {n : ℕ} {L : Phase2Bal161Layout n} {β : BitAssignment n}
    (hS : sValid145 L β) (g : Fin 145) : β (L.rOneHot145 g) = 0 := by
  dsimp only [Phase2Bal161Layout.rOneHot145]; rw [QRegister.compose_apply]; exact hS.2 _
theorem rest14_zero_of_sValid {n : ℕ} {L : Phase2Bal161Layout n} {β : BitAssignment n}
    (hS : sValid145 L β) (j : Fin 14) : β (L.rGivRest14 j) = 0 := by
  dsimp only [Phase2Bal161Layout.rGivRest14]; rw [QRegister.compose_apply]; exact hS.2 _

theorem selPair8_bit_eq_145 {n : ℕ} (L : Phase2Bal161Layout n) (β : BitAssignment n) (i : Fin 8) :
    β (L.rSelPair8 i) =
      if (UnsignedGivens.localIdx L.rSelPair8 β).val / 2 ^ i.val % 2 = 1 then 1 else 0 := by
  have hb : basisBits 8 (UnsignedGivens.localIdx L.rSelPair8 β) i = β (L.rSelPair8 i) :=
    congrFun (CircuitModular.UnsignedGivens.basisBits_symm_eq (fun k ↦ β (L.rSelPair8 k))) i
  rw [← hb, basisBits_eq_div_mod]
  rcases Nat.mod_two_eq_zero_or_one
      ((CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val / 2 ^ i.val) with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem wRoot0_ne {n : ℕ} (L : Phase2Bal161Layout n) {a b : Fin 6} (hab : a ≠ b) :
    wLeaf145 L a 0 (leafCap145_pos a) ≠ wLeaf145 L b 0 (leafCap145_pos b) :=
  fun h ↦ hab (wLeaf145_inj L h).1

theorem pair_ne_wRoot0 {n : ℕ} (L : Phase2Bal161Layout n) (i : Fin 8) (b : Fin 6) :
    L.rSelPair8 i ≠ wLeaf145 L b 0 (leafCap145_pos b) :=
  (oh145_ne_pair L _ i).symm

/-- `0-T` linear CNOT/X root decoder on `wLeaf145 L 0..5 0` after `w3 = u5*u6`, `w5 = u7*u4`. -/
def wRoot6LinCirc145 {n : ℕ} (L : Phase2Bal161Layout n) : Circuit n :=
  let w (b : Fin 6) := wLeaf145 L b 0 (leafCap145_pos b)
  Circuit.CNOT (L.rSelPair8 7) (w 4) (pair_ne_wRoot0 L 7 4) ;;ᶜ
  Circuit.CNOT (w 5) (w 4) (wRoot0_ne L (by decide)) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 6) (w 2) (pair_ne_wRoot0 L 6 2) ;;ᶜ
  Circuit.CNOT (w 3) (w 2) (wRoot0_ne L (by decide)) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 5) (w 1) (pair_ne_wRoot0 L 5 1) ;;ᶜ
  Circuit.CNOT (w 3) (w 1) (wRoot0_ne L (by decide)) ;;ᶜ
  Circuit.X (w 0) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 7) (w 0) (pair_ne_wRoot0 L 7 0) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 6) (w 0) (pair_ne_wRoot0 L 6 0) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 5) (w 0) (pair_ne_wRoot0 L 5 0) ;;ᶜ
  Circuit.CNOT (w 3) (w 0) (wRoot0_ne L (by decide))

/-- Exact reverse of `wRoot6LinCirc145` (`0 T`, `0 TOFF`). -/
def wRoot6UninitLinCirc145 {n : ℕ} (L : Phase2Bal161Layout n) : Circuit n :=
  let w (b : Fin 6) := wLeaf145 L b 0 (leafCap145_pos b)
  Circuit.CNOT (w 3) (w 0) (wRoot0_ne L (by decide)) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 5) (w 0) (pair_ne_wRoot0 L 5 0) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 6) (w 0) (pair_ne_wRoot0 L 6 0) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 7) (w 0) (pair_ne_wRoot0 L 7 0) ;;ᶜ
  Circuit.X (w 0) ;;ᶜ
  Circuit.CNOT (w 3) (w 1) (wRoot0_ne L (by decide)) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 5) (w 1) (pair_ne_wRoot0 L 5 1) ;;ᶜ
  Circuit.CNOT (w 3) (w 2) (wRoot0_ne L (by decide)) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 6) (w 2) (pair_ne_wRoot0 L 6 2) ;;ᶜ
  Circuit.CNOT (w 5) (w 4) (wRoot0_ne L (by decide)) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 7) (w 4) (pair_ne_wRoot0 L 7 4)

theorem cnot_eval_sq145 {n : ℕ} (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).eval * (Circuit.CNOT c t h).eval = 1 := by
  apply Subtype.ext; refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, StepEncK.ket_CNOT, StepEncK.ket_CNOT,
    Submonoid.coe_one, Matrix.one_mulVec]
  congr 1; funext w
  by_cases hw : w = t
  · subst hw; simp [Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero]
  · simp [Function.update_of_ne hw]

theorem x_eval_sq145 {n : ℕ} (q : Wire n) :
    (Circuit.X q).eval * (Circuit.X q).eval = 1 := by
  apply Subtype.ext; refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, XMeasCircuit.ket_X, XMeasCircuit.ket_X,
    Submonoid.coe_one, Matrix.one_mulVec]
  congr 1; funext w
  by_cases hw : w = q
  · subst hw; simp [add_assoc, CharTwo.add_self_eq_zero]
  · simp [Function.update_of_ne hw]

theorem wRoot6Uninit_mul_wRoot6Lin145 {n : ℕ} (L : Phase2Bal161Layout n) :
    (wRoot6UninitLinCirc145 L).eval * (wRoot6LinCirc145 L).eval = 1 := by
  have hc {c t : Wire n} (h : c ≠ t) (y : Unitary (2 ^ n)) :
      (Circuit.CNOT c t h).eval * ((Circuit.CNOT c t h).eval * y) = y := by
    rw [← mul_assoc, cnot_eval_sq145, one_mul]
  have hx (q : Wire n) (y : Unitary (2 ^ n)) :
      (Circuit.X q).eval * ((Circuit.X q).eval * y) = y := by
    rw [← mul_assoc, x_eval_sq145, one_mul]
  dsimp only [wRoot6UninitLinCirc145, wRoot6LinCirc145]
  simp only [Circuit.eval_seq, mul_assoc, hc, hx, cnot_eval_sq145]

private def rootBlkOfQ16 (q : Fin 10) : Fin 6 :=
  if h9 : q.val < 9 then ⟨q.val / 2, by omega⟩ else 5

private def rootBlk6Formula (q : Fin 10) (k : Fin 6) : ZMod 2 :=
  let p4 : ZMod 2 := if q.val % 2 = 1 then 1 else 0
  let p5 : ZMod 2 := if q.val / 2 % 2 = 1 then 1 else 0
  let p6 : ZMod 2 := if q.val / 4 % 2 = 1 then 1 else 0
  let p7 : ZMod 2 := if q.val / 8 % 2 = 1 then 1 else 0
  let v3 : ZMod 2 := p5 * p6; let v5 : ZMod 2 := p7 * p4
  if k = 0 then 1 + p7 + p6 + p5 + v3 else if k = 1 then p5 + v3
  else if k = 2 then p6 + v3 else if k = 3 then v3 else if k = 4 then p7 + v5 else v5

private theorem rootBlk6Formula_eq (q : Fin 10) (k : Fin 6) :
    rootBlk6Formula q k = if k = rootBlkOfQ16 q then 1 else 0 := by revert q k; decide

theorem wRoot6LinCirc145_ket {n : ℕ} (L : Phase2Bal161Layout n) {β : BitAssignment n}
    (hS : sValid145 L β) :
    let w3 := wLeaf145 L 3 0 (leafCap145_pos 3)
    let w5 := wLeaf145 L 5 0 (leafCap145_pos 5)
    let γ₃ := Function.update β w3 (β (L.rSelPair8 5) * β (L.rSelPair8 6))
    let γ₅ := Function.update γ₃ w5 (β (L.rSelPair8 7) * β (L.rSelPair8 4))
    (wRoot6LinCirc145 L).eval.1.mulVec (XMeasCircuit.ket γ₅) =
      XMeasCircuit.ket (Function.update β (wLeaf145 L (b0E145 L β) 0 (leafCap145_pos _)) 1) := by
  intro w3 w5 γ₃ γ₅
  have hw0 (b : Fin 6) : β (wLeaf145 L b 0 (leafCap145_pos b)) = 0 := oh145_zero_of_sValid hS _
  have hxv : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 145 := hS.1
  obtain ⟨q16, hq16⟩ : ∃ q16 : Fin 10,
      q16.val = (UnsignedGivens.localIdx L.rSelPair8 β).val / 16 := ⟨⟨_, by omega⟩, rfl⟩
  have hb0Eq : b0E145 L β = rootBlkOfQ16 q16 := by
    by_cases hx144 : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144
    · rw [b0E145_of_lt144 hx144, rootBlkOfQ16, dite_eq_left (by omega)]
      exact Fin.ext (by dsimp; omega)
    · rw [b0E145_of_not_lt144 hx144, rootBlkOfQ16, dite_eq_right (by omega)]
  let p4 := β (L.rSelPair8 4); let p5 := β (L.rSelPair8 5)
  let p6 := β (L.rSelPair8 6); let p7 := β (L.rSelPair8 7)
  let v3 := p5 * p6; let v5 := p7 * p4
  have hb4 : p4 = if q16.val % 2 = 1 then 1 else 0 := by
    dsimp only [p4]; rw [selPair8_bit_eq_145 L β 4]; exact if_congr (by dsimp; omega) rfl rfl
  have hb5 : p5 = if q16.val / 2 % 2 = 1 then 1 else 0 := by
    dsimp only [p5]; rw [selPair8_bit_eq_145 L β 5]; exact if_congr (by dsimp; omega) rfl rfl
  have hb6 : p6 = if q16.val / 4 % 2 = 1 then 1 else 0 := by
    dsimp only [p6]; rw [selPair8_bit_eq_145 L β 6]; exact if_congr (by dsimp; omega) rfl rfl
  have hb7 : p7 = if q16.val / 8 % 2 = 1 then 1 else 0 := by
    dsimp only [p7]; rw [selPair8_bit_eq_145 L β 7]; exact if_congr (by dsimp; omega) rfl rfl
  have hupSame (γ : BitAssignment n) (a : Fin 6) (v : ZMod 2) :
      Function.update γ (wLeaf145 L a 0 (leafCap145_pos a)) v
        (wLeaf145 L a 0 (leafCap145_pos a)) = v := Function.update_self _ _ _
  have hupDiff (γ : BitAssignment n) {a b : Fin 6} (v : ZMod 2) (h : b ≠ a) :
      Function.update γ (wLeaf145 L a 0 (leafCap145_pos a)) v
        (wLeaf145 L b 0 (leafCap145_pos b)) = γ (wLeaf145 L b 0 (leafCap145_pos b)) :=
    Function.update_of_ne (wRoot0_ne L h) _ _
  have hupLeaf (γ : BitAssignment n) (a b : Fin 6) (v : ZMod 2) :
      Function.update γ (wLeaf145 L a 0 (leafCap145_pos a)) v
        (wLeaf145 L b 0 (leafCap145_pos b)) =
        if b = a then v else γ (wLeaf145 L b 0 (leafCap145_pos b)) := by
    by_cases h : b = a
    · subst h; rw [ite_eq_left rfl]; exact hupSame γ _ v
    · rw [ite_eq_right h]; exact hupDiff γ v h
  have hupPair (γ : BitAssignment n) (a : Fin 6) (v : ZMod 2) (i : Fin 8) :
      Function.update γ (wLeaf145 L a 0 (leafCap145_pos a)) v (L.rSelPair8 i) =
        γ (L.rSelPair8 i) := Function.update_of_ne (pair_ne_wRoot0 L i a) _ _
  have hstepC {c t : Wire n} {h : c ≠ t} {γ : BitAssignment n} {v : ZMod 2} (hv : γ t + γ c = v) :
      (Circuit.CNOT c t h).eval.1.mulVec (XMeasCircuit.ket γ) =
        XMeasCircuit.ket (Function.update γ t v) := by rw [StepEncK.ket_CNOT, hv]
  have hstepX {q : Wire n} {γ : BitAssignment n} {v : ZMod 2} (hv : γ q + 1 = v) :
      (Circuit.X q).eval.1.mulVec (XMeasCircuit.ket γ) =
        XMeasCircuit.ket (Function.update γ q v) := by rw [XMeasCircuit.ket_X, hv]
  let α₄ := Function.update γ₅ (wLeaf145 L 4 0 (leafCap145_pos 4)) (p7 + v5)
  let α₂ := Function.update α₄ (wLeaf145 L 2 0 (leafCap145_pos 2)) (p6 + v3)
  let α₁ := Function.update α₂ (wLeaf145 L 1 0 (leafCap145_pos 1)) (p5 + v3)
  let α₀ := Function.update α₁ (wLeaf145 L 0 0 (leafCap145_pos 0)) (1 + p7 + p6 + p5 + v3)
  have hg1 : γ₅ (wLeaf145 L 4 0 (leafCap145_pos 4)) + γ₅ (L.rSelPair8 7) = p7 := by
    dsimp only [γ₅, γ₃, w3, w5, p7]
    rw [hupDiff _ _ (by decide), hupDiff _ _ (by decide), hw0 4, zero_add, hupPair, hupPair]
  have hg2 : Function.update γ₅ (wLeaf145 L 4 0 (leafCap145_pos 4)) p7
      (wLeaf145 L 4 0 (leafCap145_pos 4)) + Function.update γ₅
      (wLeaf145 L 4 0 (leafCap145_pos 4)) p7 (wLeaf145 L 5 0 (leafCap145_pos 5)) = p7 + v5 := by
    dsimp only [γ₅, w5, v5, p7, p4]; rw [hupSame, hupDiff _ _ (by decide), hupSame]
  have hg3 : α₄ (wLeaf145 L 2 0 (leafCap145_pos 2)) + α₄ (L.rSelPair8 6) = p6 := by
    dsimp only [α₄, γ₅, γ₃, w3, w5, p6]; rw [hupDiff _ _ (by decide), hupDiff _ _ (by decide),
      hupDiff _ _ (by decide), hw0 2, zero_add, hupPair, hupPair, hupPair]
  have hg4 : Function.update α₄ (wLeaf145 L 2 0 (leafCap145_pos 2)) p6
      (wLeaf145 L 2 0 (leafCap145_pos 2)) + Function.update α₄
      (wLeaf145 L 2 0 (leafCap145_pos 2)) p6 (wLeaf145 L 3 0 (leafCap145_pos 3)) = p6 + v3 := by
    dsimp only [α₄, γ₅, γ₃, w3, w5, v3, p5, p6]
    rw [hupSame, hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupSame]
  have hg5 : α₂ (wLeaf145 L 1 0 (leafCap145_pos 1)) + α₂ (L.rSelPair8 5) = p5 := by
    dsimp only [α₂, α₄, γ₅, γ₃, w3, w5, p5]; rw [hupDiff _ _ (by decide), hupDiff _ _ (by decide),
      hupDiff _ _ (by decide), hupDiff _ _ (by decide), hw0 1, zero_add, hupPair, hupPair,
      hupPair, hupPair]
  have hg6 : Function.update α₂ (wLeaf145 L 1 0 (leafCap145_pos 1)) p5
      (wLeaf145 L 1 0 (leafCap145_pos 1)) + Function.update α₂
      (wLeaf145 L 1 0 (leafCap145_pos 1)) p5 (wLeaf145 L 3 0 (leafCap145_pos 3)) = p5 + v3 := by
    dsimp only [α₂, α₄, γ₅, γ₃, w3, w5, v3, p5, p6]; rw [hupSame, hupDiff _ _ (by decide),
      hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupSame]
  have hg7 : α₁ (wLeaf145 L 0 0 (leafCap145_pos 0)) + 1 = 1 := by
    dsimp only [α₁, α₂, α₄, γ₅, γ₃, w3, w5]; rw [hupDiff _ _ (by decide), hupDiff _ _ (by decide),
      hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupDiff _ _ (by decide), hw0 0, zero_add]
  have hα₁Pair (i : Fin 8) : α₁ (L.rSelPair8 i) = β (L.rSelPair8 i) := by
    dsimp only [α₁, α₂, α₄, γ₅, γ₃, w3, w5]; rw [hupPair, hupPair, hupPair, hupPair, hupPair]
  have hα₁W3 : α₁ (wLeaf145 L 3 0 (leafCap145_pos 3)) = v3 := by
    dsimp only [α₁, α₂, α₄, γ₅, γ₃, w3, w5, v3, p5, p6]
    rw [hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupDiff _ _ (by decide),
      hupDiff _ _ (by decide), hupSame]
  have hg0P (u : ZMod 2) (i : Fin 8) :
      Function.update α₁ (wLeaf145 L 0 0 (leafCap145_pos 0)) u
        (wLeaf145 L 0 0 (leafCap145_pos 0)) +
      Function.update α₁ (wLeaf145 L 0 0 (leafCap145_pos 0)) u (L.rSelPair8 i) =
        u + β (L.rSelPair8 i) := by rw [hupSame, hupPair, hα₁Pair]
  have hg0W3 (u : ZMod 2) :
      Function.update α₁ (wLeaf145 L 0 0 (leafCap145_pos 0)) u
        (wLeaf145 L 0 0 (leafCap145_pos 0)) +
      Function.update α₁ (wLeaf145 L 0 0 (leafCap145_pos 0)) u
        (wLeaf145 L 3 0 (leafCap145_pos 3)) = u + v3 := by
    rw [hupSame, hupDiff _ _ (by decide), hα₁W3]
  dsimp only [wRoot6LinCirc145]; simp only [StepEncK.eval_seq_mulVec]
  rw [hstepC hg1, hstepC hg2, Function.update_idem]; change _ = _
  rw [hstepC hg3, hstepC hg4, Function.update_idem, hstepC hg5, hstepC hg6, Function.update_idem,
    hstepX hg7, hstepC (hg0P 1 7), Function.update_idem,
    hstepC (hg0P (1 + p7) 6), Function.update_idem,
    hstepC (hg0P (1 + p7 + p6) 5), Function.update_idem,
    hstepC (hg0W3 (1 + p7 + p6 + p5)), Function.update_idem]
  change QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.ket α₀ = _
  have hα₀ (k : Fin 6) : α₀ (wLeaf145 L k 0 (leafCap145_pos k)) =
      if k = 0 then 1 + p7 + p6 + p5 + v3 else if k = 1 then p5 + v3
      else if k = 2 then p6 + v3 else if k = 3 then v3
      else if k = 4 then p7 + v5 else v5 := by
    rcases (by decide +revert : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · dsimp only [α₀]; rw [hupSame]; rfl
    · dsimp only [α₀, α₁]; rw [hupDiff _ _ (by decide), hupSame]; rfl
    · dsimp only [α₀, α₁, α₂]; rw [hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupSame]; rfl
    · dsimp only [α₀, α₁, α₂, α₄, γ₅, γ₃, w3, w5, v3, p5, p6]
      rw [hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupDiff _ _ (by decide),
        hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupSame]; rfl
    · dsimp only [α₀, α₁, α₂, α₄]
      rw [hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupSame]; rfl
    · dsimp only [α₀, α₁, α₂, α₄, γ₅, w5, v5, p7, p4]
      rw [hupDiff _ _ (by decide), hupDiff _ _ (by decide), hupDiff _ _ (by decide),
        hupDiff _ _ (by decide), hupSame]; rfl
  refine congrArg XMeasCircuit.ket (funext fun w ↦ ?_)
  by_cases hw : ∃ k : Fin 6, w = wLeaf145 L k 0 (leafCap145_pos k)
  · obtain ⟨k, rfl⟩ := hw
    rw [hα₀ k, hupLeaf β (b0E145 L β) k 1, hw0 k]; dsimp only [v3, v5]
    rw [hb0Eq, hb4, hb5, hb6, hb7]; exact rootBlk6Formula_eq q16 k
  · have hne (k : Fin 6) : w ≠ wLeaf145 L k 0 (leafCap145_pos k) := fun h ↦ hw ⟨k, h⟩
    dsimp only [α₀, α₁, α₂, α₄, γ₅, γ₃, w3, w5]
    rw [Function.update_of_ne (hne 0), Function.update_of_ne (hne 1),
      Function.update_of_ne (hne 2), Function.update_of_ne (hne 4),
      Function.update_of_ne (hne 5), Function.update_of_ne (hne 3), Function.update_of_ne (hne _)]

theorem wRoot6UninitLinCirc145_ket {n : ℕ} (L : Phase2Bal161Layout n) {β : BitAssignment n}
    (hS : sValid145 L β) :
    (wRoot6UninitLinCirc145 L).eval.1.mulVec
        (XMeasCircuit.ket (Function.update β (wLeaf145 L (b0E145 L β) 0 (leafCap145_pos _)) 1)) =
      QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.ket (Function.update
        (Function.update β (wLeaf145 L 3 0 (leafCap145_pos 3))
          (β (L.rSelPair8 5) * β (L.rSelPair8 6)))
        (wLeaf145 L 5 0 (leafCap145_pos 5))
        (β (L.rSelPair8 7) * β (L.rSelPair8 4))) := by
  have hm := congrArg Subtype.val (wRoot6Uninit_mul_wRoot6Lin145 L)
  rw [← wRoot6LinCirc145_ket L hS, Matrix.mulVec_mulVec]
  simpa only [Submonoid.coe_mul, Submonoid.coe_one, Matrix.one_mulVec] using
    congrArg (fun M : Operator (2 ^ n) ↦ M.mulVec _) hm

/-- Eighth root of unity `(1 + i) / √2` used in W-tree splitting. -/
noncomputable def omega8_145 : ℂ := (1 + Complex.I) / (√2 : ℂ)

theorem omega8_145_eq : omega8_145 = (1 + Complex.I) * XMeasCircuit.sqrtHalf := by
  dsimp only [omega8_145, XMeasCircuit.sqrtHalf]
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  have hmul : (√(1 / 2 : ℝ) : ℂ) * (√2 : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]; norm_num
  rw [div_eq_iff h2, mul_assoc, hmul, mul_one]

theorem ket_S_145 {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (XMeasCircuit.ket β) =
      (if β q = 0 then (1 : ℂ) else Complex.I) • XMeasCircuit.ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, Complex.I]).mulVec _ = _
  rw [XMeasCircuit.singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e]

theorem ket_T_145 {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (XMeasCircuit.ket β) =
      (if β q = 0 then (1 : ℂ) else omega8_145) • XMeasCircuit.ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, omega8_145]).mulVec _ = _
  rw [XMeasCircuit.singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e]

theorem wSplitPair_ket_00_145 {n : ℕ} (a b : Wire n) (h : a ≠ b)
    {β : BitAssignment n} (ha : β a = 0) (hb : β b = 0) :
    (StepCore.wSplitPair a b h).eval.1.mulVec (XMeasCircuit.ket β) = XMeasCircuit.ket β := by
  have hub0 : Function.update β b 0 = β := Function.update_eq_self_iff.mpr hb.symm
  have hua0 : Function.update β a 0 = β := Function.update_eq_self_iff.mpr ha.symm
  have h10 : ((1 : ZMod 2) = 0) = False := by decide
  have hsq : XMeasCircuit.sqrtHalf ^ 2 = 1 / 2 := by
    linear_combination XMeasCircuit.sqrtHalf_mul_sqrtHalf
  have hp4 : XMeasCircuit.sqrtHalf ^ 4 = 1 / 4 := by
    linear_combination (XMeasCircuit.sqrtHalf ^ 2 + 1 / 2) * hsq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * Complex.I_sq
  have hi4 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq
  simp only [StepCore.wSplitPair, StepEncK.eval_seq_mulVec, ket_S_145, ket_T_145,
    XMeasCircuit.ket_H, XMeasCircuit.ket_Z, StepEncK.ket_CNOT, Matrix.mulVec_smul,
    Matrix.mulVec_add, ha, hb, h10, ↓reduceIte, one_smul, add_zero, zero_add, Function.update_self,
    Function.update_idem, Function.update_of_ne h, hub0, hua0, XMeasCircuit.bitSign, smul_add,
    smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  refine (congrArg₂ (· + ·) (congrArg (· • _) (?_ : _ = (1 : ℂ)))
    (congrArg (· • _) (?_ : _ = (0 : ℂ)))).trans (by simp)
  · rw [omega8_145_eq]; ring_nf; simp only [hsq, hp4, Complex.I_sq, hi3]; ring
  · rw [omega8_145_eq]; ring_nf; simp only [hsq, hp4, Complex.I_sq, hi3, hi4]; ring

theorem wSplitPair_ket_10_145 {n : ℕ} (a b : Wire n) (h : a ≠ b)
    {β : BitAssignment n} (ha : β a = 1) (hb : β b = 0) :
    (StepCore.wSplitPair a b h).eval.1.mulVec (XMeasCircuit.ket β) =
      XMeasCircuit.sqrtHalf • XMeasCircuit.ket β +
        XMeasCircuit.sqrtHalf • XMeasCircuit.ket (Function.update (Function.update β a 0) b 1) := by
  have hub0 : Function.update β b 0 = β := Function.update_eq_self_iff.mpr hb.symm
  have hua1 : Function.update β a 1 = β := Function.update_eq_self_iff.mpr ha.symm
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have h10 : ((1 : ZMod 2) = 0) = False := by decide
  have hsq : XMeasCircuit.sqrtHalf ^ 2 = 1 / 2 := by
    linear_combination XMeasCircuit.sqrtHalf_mul_sqrtHalf
  have hp3 : XMeasCircuit.sqrtHalf ^ 3 = (1 / 2) * XMeasCircuit.sqrtHalf := by
    linear_combination XMeasCircuit.sqrtHalf * hsq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * Complex.I_sq
  have hcomm : Function.update (Function.update β b 1) a 0 =
      Function.update (Function.update β a 0) b 1 := Function.update_comm h.symm 1 0 β
  simp only [StepCore.wSplitPair, StepEncK.eval_seq_mulVec, ket_S_145, ket_T_145,
    XMeasCircuit.ket_H, XMeasCircuit.ket_Z, StepEncK.ket_CNOT, Matrix.mulVec_smul,
    Matrix.mulVec_add, ha, hb, h11, h10, ↓reduceIte, one_smul, zero_add, add_zero,
    Function.update_self, Function.update_idem, Function.update_of_ne h, hub0, hua1,
    XMeasCircuit.bitSign, hcomm, smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  refine congrArg₂ (· + ·) (congrArg (· • _) ?_) (congrArg (· • _) ?_)
  · rw [omega8_145_eq]; ring_nf; simp only [hp3, Complex.I_sq]; ring
  · rw [omega8_145_eq]; ring_nf; simp only [hp3, Complex.I_sq, hi3]; ring

/-- Number of active blocks at tree level `r : Fin 5` (`5` for `r < 4`, `4` for `r = 4`). -/
def levelBlocks145 (r : Fin 5) : ℕ :=
  if r.val < 4 then 5 else 4

/-- Effective `W`-tree depth of block `b : Fin 6` after `R ≤ 5` rounds. -/
def treeDepth145 (b : Fin 6) (R : ℕ) : ℕ :=
  if b.val < 4 then R else if b.val = 4 then min R 4 else 0

theorem two_mul_pow_le_cap145 {r : Fin 5} {b : Fin 6} (hb : b.val < levelBlocks145 r) :
    2 * 2 ^ r.val ≤ leafCap145 b := by
  have hbv := b.isLt
  fin_cases r <;> (dsimp [levelBlocks145, leafCap145] at hb ⊢; split_ifs at hb ⊢ <;> omega)

theorem pow_treeDepth145_le_cap (b : Fin 6) {R : ℕ} (hR : R ≤ 5) :
    2 ^ treeDepth145 b R ≤ leafCap145 b := by
  have hbv := b.isLt
  dsimp [treeDepth145, leafCap145]
  split_ifs
  · exact Nat.pow_le_pow_right (by omega) hR
  · exact Nat.pow_le_pow_right (by omega) (Nat.min_le_right R 4)
  · simp

/-- `m` `wSplitPair` gates inside block `b` at level `r`. -/
def wSplitBlockFrom145 {n : ℕ} (L : Phase2Bal161Layout n) (r : Fin 5) (b : Fin 6)
    (hb : b.val < levelBlocks145 r) : ∀ (m : ℕ), m ≤ 2 ^ r.val → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      have hcap := two_mul_pow_le_cap145 hb
      wSplitBlockFrom145 L r b hb m (by omega) ;;ᶜ
        StepCore.wSplitPair (wLeaf145 L b m (by omega))
          (wLeaf145 L b (m + 2 ^ r.val) (by omega))
          (fun h ↦ by have hp := (wLeaf145_inj L h).2; have := Nat.two_pow_pos r.val; omega)

/-- `B` blocks of `wSplitBlockFrom145` at level `r`. -/
def wSplitLevelBlocks145 {n : ℕ} (L : Phase2Bal161Layout n) (r : Fin 5) :
    ∀ (B : ℕ), B ≤ levelBlocks145 r → Circuit n
  | 0, _ => .identity
  | B + 1, hB =>
      have hlt6 : B < 6 := by dsimp [levelBlocks145] at hB; split_ifs at hB <;> omega
      wSplitLevelBlocks145 L r B (by omega) ;;ᶜ
        wSplitBlockFrom145 L r ⟨B, hlt6⟩ (by dsimp; omega) (2 ^ r.val) le_rfl

/-- `5`-round `145`-leaf `W`-state prefix circuit (`278 T`, `0 TOFF`). -/
def wTreePrefixLevels145 {n : ℕ} (L : Phase2Bal161Layout n) : ∀ (R : ℕ), R ≤ 5 → Circuit n
  | 0, _ => .identity
  | R + 1, hR =>
      wTreePrefixLevels145 L R (by omega) ;;ᶜ
        wSplitLevelBlocks145 L ⟨R, hR⟩ (levelBlocks145 ⟨R, hR⟩) le_rfl

theorem count_wSplitBlockFrom145_toff {n : ℕ} (L : Phase2Bal161Layout n) (r : Fin 5)
    (b : Fin 6) (hb : b.val < levelBlocks145 r) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ r.val), (wSplitBlockFrom145 L r b hb m hm).count .TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [wSplitBlockFrom145, count_wSplitBlockFrom145_toff L r b hb m (by omega)]

theorem count_wSplitBlockFrom145_t {n : ℕ} (L : Phase2Bal161Layout n) (r : Fin 5)
    (b : Fin 6) (hb : b.val < levelBlocks145 r) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ r.val), (wSplitBlockFrom145 L r b hb m hm).count .T = 2 * m
  | 0, _ => rfl
  | m + 1, hm => by
      simp [wSplitBlockFrom145, count_wSplitBlockFrom145_t L r b hb m (by omega)]; omega

theorem count_wSplitLevelBlocks145_toff {n : ℕ} (L : Phase2Bal161Layout n) (r : Fin 5) :
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 r), (wSplitLevelBlocks145 L r B hB).count .TOFF = 0
  | 0, _ => rfl
  | B + 1, hB => by
      simp [wSplitLevelBlocks145, count_wSplitLevelBlocks145_toff L r B (by omega),
        count_wSplitBlockFrom145_toff]

theorem count_wSplitLevelBlocks145_t {n : ℕ} (L : Phase2Bal161Layout n) (r : Fin 5) :
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 r),
      (wSplitLevelBlocks145 L r B hB).count .T = B * (2 * 2 ^ r.val)
  | 0, _ => by simp [wSplitLevelBlocks145]
  | B + 1, hB => by
      simp [wSplitLevelBlocks145, count_wSplitLevelBlocks145_t L r B (by omega),
        count_wSplitBlockFrom145_t]
      ring

theorem count_wTreePrefixLevels145_toff {n : ℕ} (L : Phase2Bal161Layout n) :
    ∀ (R : ℕ) (hR : R ≤ 5), (wTreePrefixLevels145 L R hR).count .TOFF = 0
  | 0, _ => rfl
  | R + 1, hR => by
      simp [wTreePrefixLevels145, count_wTreePrefixLevels145_toff L R (by omega),
        count_wSplitLevelBlocks145_toff]

theorem count_wTreePrefixLevels145_t {n : ℕ} (L : Phase2Bal161Layout n) :
    (wTreePrefixLevels145 L 5 le_rfl).count .T = 278 := by
  simp only [wTreePrefixLevels145, Circuit.count_seq, count_wSplitLevelBlocks145_t, levelBlocks145]
  rfl

/-- Intermediate W-tree superposition state at tree level `R` on `Phase2Bal161Layout`. -/
noncomputable def wTreeVec145 {n : ℕ} (L : Phase2Bal161Layout n) (R : ℕ) (hR : R ≤ 5)
    (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  let b₀ := b0E145 L β
  (XMeasCircuit.sqrtHalf ^ treeDepth145 b₀ R) •
    ∑ t : Fin (2 ^ treeDepth145 b₀ R),
      XMeasCircuit.ket (Function.update β
        (wLeaf145 L b₀ t.val (lt_of_lt_of_le t.isLt (pow_treeDepth145_le_cap b₀ hR))) 1)

theorem wSplitBlockFrom145_ket_fix {n : ℕ} (L : Phase2Bal161Layout n) (r : Fin 5)
    (b b₀ : Fin 6) (hb : b.val < levelBlocks145 r) (p₀ : ℕ) (hp₀ : p₀ < leafCap145 b₀)
    {β : BitAssignment n} (hS : sValid145 L β) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ r.val),
      (b ≠ b₀ ∨ ∀ k < m, k ≠ p₀ ∧ k + 2 ^ r.val ≠ p₀) →
      (wSplitBlockFrom145 L r b hb m hm).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ p₀ hp₀) 1)) =
        XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ p₀ hp₀) 1)
  | 0, _, _ => by
      simp only [wSplitBlockFrom145, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | m + 1, hm, hdisj => by
      have hcap := two_mul_pow_le_cap145 hb
      have hprev := wSplitBlockFrom145_ket_fix L r b b₀ hb p₀ hp₀ hS m (by omega)
        (hdisj.imp id fun hk k hlt ↦ hk k (by omega))
      have hne1 : wLeaf145 L b m (by omega) ≠ wLeaf145 L b₀ p₀ hp₀ := fun heq ↦ by
        obtain ⟨rfl, hp⟩ := wLeaf145_inj L heq
        exact hdisj.elim (· rfl) (fun hk ↦ (hk m (by omega)).1 hp)
      have hne2 : wLeaf145 L b (m + 2 ^ r.val) (by omega) ≠ wLeaf145 L b₀ p₀ hp₀ := fun heq ↦ by
        obtain ⟨rfl, hp⟩ := wLeaf145_inj L heq
        exact hdisj.elim (· rfl) (fun hk ↦ (hk m (by omega)).2 hp)
      rw [wSplitBlockFrom145, StepEncK.eval_seq_mulVec, hprev]
      exact wSplitPair_ket_00_145 _ _ _
        (by rw [Function.update_of_ne hne1]; exact oh145_zero_of_sValid hS _)
        (by rw [Function.update_of_ne hne2]; exact oh145_zero_of_sValid hS _)

theorem wSplitBlockFrom145_ket_split {n : ℕ} (L : Phase2Bal161Layout n) (r : Fin 5)
    (b₀ : Fin 6) (hb₀ : b₀.val < levelBlocks145 r) (t : Fin (2 ^ r.val))
    {β : BitAssignment n} (hS : sValid145 L β) :
    have hcap := two_mul_pow_le_cap145 hb₀
    ∀ (m : ℕ) (hm : m ≤ 2 ^ r.val), t.val < m →
      (wSplitBlockFrom145 L r b₀ hb₀ m hm).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ t.val (by omega)) 1)) =
        QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.sqrtHalf •
            XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ t.val (by omega)) 1) +
          XMeasCircuit.sqrtHalf • XMeasCircuit.ket
            (Function.update β (wLeaf145 L b₀ (t.val + 2 ^ r.val) (by omega)) 1) := by
  intro hcap m hm hlt
  induction m with
  | zero => omega
  | succ m ih =>
      have htLt := t.isLt
      rw [wSplitBlockFrom145, StepEncK.eval_seq_mulVec]
      by_cases hmt : m = t.val
      · subst hmt
        have hfix := wSplitBlockFrom145_ket_fix L r b₀ b₀ hb₀ t.val (by omega) hS t.val (by omega)
          (Or.inr fun k hk ↦ ⟨by omega, by omega⟩)
        have hne12 :
            wLeaf145 L b₀ (t.val + 2 ^ r.val) (by omega) ≠ wLeaf145 L b₀ t.val (by omega) :=
          fun h ↦ by have hp := (wLeaf145_inj L h).2; have := Nat.two_pow_pos r.val; omega
        rw [hfix, wSplitPair_ket_10_145 _ _ _ (by rw [Function.update_self])
          (by rw [Function.update_of_ne hne12]; exact oh145_zero_of_sValid hS _)]
        have hclr : Function.update (Function.update β (wLeaf145 L b₀ t.val (by omega)) 1)
            (wLeaf145 L b₀ t.val (by omega)) 0 = β := by
          rw [Function.update_idem]
          exact Function.update_eq_self_iff.mpr (oh145_zero_of_sValid hS _).symm
        rw [hclr]
      · have hprev := ih (by omega) (by omega)
        have hneA1 : wLeaf145 L b₀ m (by omega) ≠ wLeaf145 L b₀ t.val (by omega) :=
          fun h ↦ hmt (wLeaf145_inj L h).2
        have hneA2 : wLeaf145 L b₀ (m + 2 ^ r.val) (by omega) ≠ wLeaf145 L b₀ t.val (by omega) :=
          fun h ↦ by have hp := (wLeaf145_inj L h).2; omega
        have hneB1 :
            wLeaf145 L b₀ m (by omega) ≠ wLeaf145 L b₀ (t.val + 2 ^ r.val) (by omega) :=
          fun h ↦ by have hp := (wLeaf145_inj L h).2; omega
        have hneB2 : wLeaf145 L b₀ (m + 2 ^ r.val) (by omega) ≠
            wLeaf145 L b₀ (t.val + 2 ^ r.val) (by omega) :=
          fun h ↦ hmt (by have hp := (wLeaf145_inj L h).2; omega)
        rw [hprev, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          wSplitPair_ket_00_145 _ _ _
            (by rw [Function.update_of_ne hneA1]; exact oh145_zero_of_sValid hS _)
            (by rw [Function.update_of_ne hneA2]; exact oh145_zero_of_sValid hS _),
          wSplitPair_ket_00_145 _ _ _
            (by rw [Function.update_of_ne hneB1]; exact oh145_zero_of_sValid hS _)
            (by rw [Function.update_of_ne hneB2]; exact oh145_zero_of_sValid hS _)]

theorem wSplitLevelBlocks145_ket {n : ℕ} (L : Phase2Bal161Layout n) (r : Fin 5)
    (b₀ : Fin 6) (p₀ : ℕ) (hp₀ : p₀ < leafCap145 b₀)
    (hpLt : b₀.val < levelBlocks145 r → p₀ < 2 ^ r.val)
    {β : BitAssignment n} (hS : sValid145 L β) :
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 r),
      (wSplitLevelBlocks145 L r B hB).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ p₀ hp₀) 1)) =
        if hlt : b₀.val < B then
          have hcap := two_mul_pow_le_cap145 (lt_of_lt_of_le hlt hB)
          have hp2 := hpLt (lt_of_lt_of_le hlt hB)
          QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.sqrtHalf •
              XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ p₀ hp₀) 1) +
            QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.sqrtHalf •
              XMeasCircuit.ket (Function.update β
                (wLeaf145 L b₀ (p₀ + 2 ^ r.val) (by omega)) 1)
        else XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ p₀ hp₀) 1) := by
  intro B hB
  induction B with
  | zero =>
      simp only [wSplitLevelBlocks145, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec, Nat.not_lt_zero, ↓reduceDIte]
  | succ B ih =>
      have hlt6 : B < 6 := by dsimp [levelBlocks145] at hB; split_ifs at hB <;> omega
      rw [wSplitLevelBlocks145, StepEncK.eval_seq_mulVec, ih (by omega)]
      clear ih
      by_cases hprev : b₀.val < B
      · have hnext : b₀.val < B + 1 := by omega
        have hne : (⟨B, hlt6⟩ : Fin 6) ≠ b₀ := fun h ↦ by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        rw [dite_eq_left hprev, dite_eq_left hnext, Matrix.mulVec_add, Matrix.mulVec_smul,
          Matrix.mulVec_smul, wSplitBlockFrom145_ket_fix L r _ _ _ _ _ hS _ _ (Or.inl hne),
          wSplitBlockFrom145_ket_fix L r _ _ _ _ _ hS _ _ (Or.inl hne)]
      · rw [dite_eq_right hprev]
        by_cases hcur : b₀.val = B
        · have hnext : b₀.val < B + 1 := by omega
          have hp2 : p₀ < 2 ^ r.val := hpLt (by omega)
          have hbEq : b₀ = ⟨B, hlt6⟩ := Fin.ext hcur
          rw [dite_eq_left hnext]
          subst hbEq
          simpa using wSplitBlockFrom145_ket_split L r ⟨B, hlt6⟩
            (by dsimp; omega) ⟨p₀, hp2⟩ hS (2 ^ r.val) le_rfl hp2
        · have hnNext : ¬ b₀.val < B + 1 := by omega
          have hne : (⟨B, hlt6⟩ : Fin 6) ≠ b₀ := fun h ↦ hcur (congrArg Fin.val h).symm
          rw [dite_eq_right hnNext]
          exact wSplitBlockFrom145_ket_fix L r _ _ _ _ _ hS _ _ (Or.inl hne)

theorem sum_fin_two_pow_split_145 {M : Type*} [AddCommMonoid M] (R : ℕ)
    (f : Fin (2 ^ (R + 1)) → M) :
    (∑ t : Fin (2 ^ (R + 1)), f t) =
      ∑ s : Fin (2 ^ R),
        (f ⟨s.val, by have := s.isLt; omega⟩ +
          f ⟨s.val + 2 ^ R, by have := s.isLt; omega⟩) := by
  have heq : 2 ^ (R + 1) = 2 ^ R + 2 ^ R := by ring
  rw [← Equiv.sum_comp (finCongr heq).symm, Fin.sum_univ_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ congrArg₂ (· + ·)
    (congrArg f (Fin.ext (by simp [finCongr])))
    (congrArg f (Fin.ext (by simp [finCongr])))

theorem smul_sum_pow_cast145 {n k₁ k₂ : ℕ} (hk : k₁ = k₂)
    (g : ∀ m : ℕ, m < 2 ^ k₁ → Fin (2 ^ n) → ℂ) :
    (XMeasCircuit.sqrtHalf ^ k₁) • (∑ t : Fin (2 ^ k₁), g t.val t.isLt) =
      (XMeasCircuit.sqrtHalf ^ k₂) • (∑ t : Fin (2 ^ k₂), g t.val (hk ▸ t.isLt)) := by
  subst hk; rfl

theorem smul_sum_pow_zero145 {n k : ℕ} (hk : k = 0)
    (g : ∀ m : ℕ, m < 2 ^ k → Fin (2 ^ n) → ℂ) :
    (XMeasCircuit.sqrtHalf ^ k) • (∑ t : Fin (2 ^ k), g t.val t.isLt) =
      g 0 (by rw [hk]; decide) := by
  subst hk; simp

theorem wTreePrefixLevels145_ket_aux {n : ℕ} (L : Phase2Bal161Layout n) (b₀ : Fin 6)
    {β : BitAssignment n} (hS : sValid145 L β) :
    ∀ (R : ℕ) (hR : R ≤ 5),
      (wTreePrefixLevels145 L R hR).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ 0 (leafCap145_pos b₀)) 1)) =
        (XMeasCircuit.sqrtHalf ^ treeDepth145 b₀ R) •
          ∑ t : Fin (2 ^ treeDepth145 b₀ R),
            XMeasCircuit.ket (Function.update β
              (wLeaf145 L b₀ t.val (lt_of_lt_of_le t.isLt (pow_treeDepth145_le_cap b₀ hR))) 1)
  | 0, hR => by
      have hd0 : treeDepth145 b₀ 0 = 0 := by dsimp [treeDepth145]; split_ifs <;> rfl
      rw [wTreePrefixLevels145, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
        smul_sum_pow_zero145 hd0 (fun m hm ↦ XMeasCircuit.ket (Function.update β
          (wLeaf145 L b₀ m (lt_of_lt_of_le hm (pow_treeDepth145_le_cap b₀ hR))) 1))]
  | R + 1, hR => by
      rw [wTreePrefixLevels145, StepEncK.eval_seq_mulVec,
        wTreePrefixLevels145_ket_aux L b₀ hS R (by omega), Matrix.mulVec_smul, Matrix.mulVec_sum]
      have hcapR := pow_treeDepth145_le_cap b₀ (by omega : R ≤ 5)
      have hcapR1 := pow_treeDepth145_le_cap b₀ hR
      by_cases hAct : b₀.val < levelBlocks145 ⟨R, hR⟩
      · have hdR : treeDepth145 b₀ R = R := by
          have := b₀.isLt; dsimp [treeDepth145, levelBlocks145] at hAct ⊢
          split_ifs at hAct ⊢ <;> omega
        have hdR1 : treeDepth145 b₀ (R + 1) = R + 1 := by
          have := b₀.isLt; dsimp [treeDepth145, levelBlocks145] at hAct ⊢
          split_ifs at hAct ⊢ <;> omega
        rw [smul_sum_pow_cast145 hdR (fun m hm ↦
              (wSplitLevelBlocks145 L ⟨R, hR⟩ (levelBlocks145 ⟨R, hR⟩) le_rfl).eval.1.mulVec
                (XMeasCircuit.ket (Function.update β
                  (wLeaf145 L b₀ m (lt_of_lt_of_le hm hcapR)) 1))),
          smul_sum_pow_cast145 hdR1 (fun m hm ↦ XMeasCircuit.ket (Function.update β
            (wLeaf145 L b₀ m (lt_of_lt_of_le hm hcapR1)) 1)),
          sum_fin_two_pow_split_145 R, _root_.pow_succ, ← smul_smul]
        apply congrArg (XMeasCircuit.sqrtHalf ^ R • ·); rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        have htCap : t.val < leafCap145 b₀ :=
          lt_of_lt_of_le (by rw [hdR]; exact t.isLt) hcapR
        have hsp := wSplitLevelBlocks145_ket L ⟨R, hR⟩ b₀ t.val htCap (fun _ ↦ t.isLt) hS
          (levelBlocks145 ⟨R, hR⟩) le_rfl
        rw [hsp, dite_eq_left hAct, smul_add]
      · have hdEq : treeDepth145 b₀ (R + 1) = treeDepth145 b₀ R := by
          have := b₀.isLt; dsimp [treeDepth145, levelBlocks145] at hAct ⊢
          split_ifs at hAct ⊢ <;> omega
        rw [smul_sum_pow_cast145 hdEq (fun m hm ↦ XMeasCircuit.ket (Function.update β
          (wLeaf145 L b₀ m (lt_of_lt_of_le hm hcapR1)) 1))]
        apply congrArg (_ • ·)
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        have hsp := wSplitLevelBlocks145_ket L ⟨R, hR⟩ b₀ t.val (lt_of_lt_of_le t.isLt hcapR)
          (fun h ↦ absurd h hAct) hS (levelBlocks145 ⟨R, hR⟩) le_rfl
        rw [hsp, dite_eq_right hAct]

theorem wTreePrefixLevels145_ket {n : ℕ} (L : Phase2Bal161Layout n) {β : BitAssignment n}
    (hS : sValid145 L β) (R : ℕ) (hR : R ≤ 5) :
    (wTreePrefixLevels145 L R hR).eval.1.mulVec
        (XMeasCircuit.ket (Function.update β (wLeaf145 L (b0E145 L β) 0 (leafCap145_pos _)) 1)) =
      wTreeVec145 L R hR β := by
  dsimp only [wTreeVec145]; exact wTreePrefixLevels145_ket_aux L (b0E145 L β) hS R hR

/-- Number of SWAP pairs in block `b` (`16` for `b < 4`, `8` for `b ≥ 4`). -/
def bswapPairs145 (b : Fin 6) : ℕ :=
  if b.val < 4 then 16 else 8

theorem insertZeroBit_lt_16_145 (d' : Fin 5) (s' : Fin 8) :
    d'.val < 4 → (StepCore.insertZeroBit d' ⟨s'.val, by omega⟩).val < 16 := by
  revert d' s'; decide

theorem insertOneBit_lt_16_145 (d' : Fin 5) (s' : Fin 8) :
    d'.val < 4 → (StepCore.insertOneBit d' ⟨s'.val, by omega⟩).val < 16 := by
  revert d' s'; decide

theorem insertZeroBit_lt_cap145 {d : Fin 5} {b : Fin 6} (hb : b.val < levelBlocks145 d)
    {s : ℕ} (hs : s < bswapPairs145 b) :
    (StepCore.insertZeroBit d
      ⟨s, by dsimp [bswapPairs145] at hs; split_ifs at hs <;> omega⟩).val <
      leafCap145 b := by
  have hb5 : b.val < 5 := by dsimp [levelBlocks145] at hb; split_ifs at hb <;> omega
  by_cases hb4 : b.val < 4
  · simp only [leafCap145, hb4, ↓reduceIte]
    exact (StepCore.insertZeroBit d
      ⟨s, by simp only [bswapPairs145, hb4, ↓reduceIte] at hs; exact hs⟩).isLt
  · have hbEq4 : b.val = 4 := by omega
    have hd4 : d.val < 4 := by dsimp [levelBlocks145] at hb; split_ifs at hb <;> omega
    have hs8 : s < 8 := by simp only [bswapPairs145, hb4, ↓reduceIte] at hs; exact hs
    simp only [leafCap145, hbEq4, ↓reduceIte]
    exact insertZeroBit_lt_16_145 d ⟨s, hs8⟩ hd4

theorem insertOneBit_lt_cap145 {d : Fin 5} {b : Fin 6} (hb : b.val < levelBlocks145 d)
    {s : ℕ} (hs : s < bswapPairs145 b) :
    (StepCore.insertOneBit d ⟨s, by dsimp [bswapPairs145] at hs; split_ifs at hs <;> omega⟩).val <
      leafCap145 b := by
  have hb5 : b.val < 5 := by dsimp [levelBlocks145] at hb; split_ifs at hb <;> omega
  by_cases hb4 : b.val < 4
  · simp only [leafCap145, hb4, ↓reduceIte]
    exact (StepCore.insertOneBit d
      ⟨s, by simp only [bswapPairs145, hb4, ↓reduceIte] at hs; exact hs⟩).isLt
  · have hbEq4 : b.val = 4 := by omega
    have hd4 : d.val < 4 := by dsimp [levelBlocks145] at hb; split_ifs at hb <;> omega
    have hs8 : s < 8 := by simp only [bswapPairs145, hb4, ↓reduceIte] at hs; exact hs
    simp only [leafCap145, hbEq4, ↓reduceIte]
    exact insertOneBit_lt_16_145 d ⟨s, hs8⟩ hd4

theorem insertZero_ne_insertOne_145 (d : Fin 5) (s : Fin 16) :
    (StepCore.insertZeroBit d s).val ≠ (StepCore.insertOneBit d s).val := by
  revert d s; decide

/-- `m` bit-`d` `SWAP` pairs inside block `b`. -/
def bswapBlockFrom145 {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) (b : Fin 6)
    (hb : b.val < levelBlocks145 d) : ∀ (m : ℕ), m ≤ bswapPairs145 b → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      let s16 : Fin 16 := ⟨m, by dsimp [bswapPairs145] at hm; split_ifs at hm <;> omega⟩
      bswapBlockFrom145 L d b hb m (by omega) ;;ᶜ
        Circuit.SWAP
          (wLeaf145 L b (StepCore.insertZeroBit d s16).val (insertZeroBit_lt_cap145 hb hm))
          (wLeaf145 L b (StepCore.insertOneBit d s16).val (insertOneBit_lt_cap145 hb hm))
          (fun h ↦ insertZero_ne_insertOne_145 d s16 (wLeaf145_inj L h).2)

/-- `B` blocks of `bswapBlockFrom145` at barrel-shift stage `d`. -/
def bswapLevelBlocks145 {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) :
    ∀ (B : ℕ), B ≤ levelBlocks145 d → Circuit n
  | 0, _ => .identity
  | B + 1, hB =>
      have hlt6 : B < 6 := by dsimp [levelBlocks145] at hB; split_ifs at hB <;> omega
      bswapLevelBlocks145 L d B (by omega) ;;ᶜ
        bswapBlockFrom145 L d ⟨B, hlt6⟩ (by dsimp; omega) (bswapPairs145 ⟨B, hlt6⟩) le_rfl

/-- Leaf parity mask at barrel-shift stage `d : Fin 5` (`0 T`):
for `d < 4`, active on `g < 144` with bit `d` of `g % 32` equal to `1`;
for `d = 4`, active on `(g < 128 ∧ bit 4 of g % 32 = 1) ∨ g = 144`. -/
def shiftParityMask145 (d : Fin 5) (g : Fin 145) : Bool :=
  if d.val < 4 then decide (g.val < 144 ∧ (g.val % 32) / 2 ^ d.val % 2 = 1)
  else decide ((g.val < 128 ∧ (g.val % 32) / 16 % 2 = 1) ∨ g.val = 144)

/-- `0-T` syndrome parity circuit writing `shiftParityMask145 d + rSelPair8 d` onto `L.qEnc`. -/
def shiftParityCirc145 {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) : Circuit n :=
  CircuitModular.UnsignedGivens.cnotMaskReg 145 L.rOneHot145 L.qEnc (shiftParityMask145 d)
    (fun g ↦ oh145_ne_rest L g 2) ;;ᶜ
  Circuit.CNOT (L.rSelPair8 ⟨d.val, by omega⟩) L.qEnc (rest14_ne_pair L 2 _).symm

/-- `2-T`, `0-TOFF` controlled-Hadamard primitive fixing `|0, y⟩` and mapping
`|1, 0⟩ ↦ (|1, 0⟩ + |1, 1⟩) / √2` on distinct wires `(a, b)`. -/
def cHadPair145 {n : ℕ} (a b : Wire n) (h : a ≠ b) : Circuit n :=
  Circuit.S b ;;ᶜ Circuit.H b ;;ᶜ Circuit.T b ;;ᶜ
  Circuit.CNOT a b h ;;ᶜ
  Circuit.Z b ;;ᶜ Circuit.S b ;;ᶜ Circuit.T b ;;ᶜ
  Circuit.H b ;;ᶜ Circuit.Z b ;;ᶜ Circuit.S b

@[simp] theorem count_cHadPair145_toff {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (cHadPair145 a b h).count .TOFF = 0 := rfl

@[simp] theorem count_cHadPair145_t {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (cHadPair145 a b h).count .T = 2 := rfl

/-- Single-wire Case-B indicator at barrel-shift stage `d` (`wLeaf145 L 5 0` for `d < 4`,
`L.rSelPair8 7` for `d = 4`). -/
def ctrlHad145 {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) : Wire n :=
  if d.val < 4 then wLeaf145 L 5 0 (leafCap145_pos 5) else L.rSelPair8 7

theorem ctrlHad145_ne_qEnc {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) :
    ctrlHad145 L d ≠ L.qEnc := by
  dsimp [ctrlHad145, wLeaf145, Phase2Bal161Layout.qEnc]
  split_ifs
  · exact oh145_ne_rest L _ 2
  · exact (rest14_ne_pair L 2 7).symm

/-- `5`-stage `10-T`, `0-TOFF` measurement-based barrel shifter for `145` leaves. -/
def wShiftFromDyn145 {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    ∀ (D : ℕ), D ≤ 5 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | D + 1, hD =>
      let d : Fin 5 := ⟨5 - (D + 1), by omega⟩
      .seq (.circuit (shiftParityCirc145 L d ;;ᶜ
            cHadPair145 (ctrlHad145 L d) L.qEnc (ctrlHad145_ne_qEnc L d)))
        (.seq (XMeasCircuit.remeasureIfDyn v L.qEnc
              (.circuit (Circuit.X L.qEnc ;;ᶜ bswapLevelBlocks145 L d (levelBlocks145 d) le_rfl)))
          (wShiftFromDyn145 v L D (by omega)))

theorem count_bswapBlockFrom145 {n k : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (b : Fin 6) (hb : b.val < levelBlocks145 d) (g : PrimitiveGate k)
    (hSwap : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.SWAP x y h).count g = 0) :
    ∀ (m : ℕ) (hm : m ≤ bswapPairs145 b), (bswapBlockFrom145 L d b hb m hm).count g = 0
  | 0, _ => rfl
  | m + 1, hm => by
      rw [bswapBlockFrom145, Circuit.count_seq,
        count_bswapBlockFrom145 L d b hb g hSwap m (by omega), hSwap, add_zero]

theorem count_bswapLevelBlocks145 {n k : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (g : PrimitiveGate k)
    (hSwap : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.SWAP x y h).count g = 0) :
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 d), (bswapLevelBlocks145 L d B hB).count g = 0
  | 0, _ => rfl
  | B + 1, hB => by
      rw [bswapLevelBlocks145, Circuit.count_seq,
        count_bswapLevelBlocks145 L d g hSwap B (by omega),
        count_bswapBlockFrom145 L d _ _ g hSwap _ le_rfl, add_zero]

theorem count_wShiftFromDyn145_toff {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    ∀ (D : ℕ) (hD : D ≤ 5), (wShiftFromDyn145 v L D hD).count .TOFF = 0
  | 0, _ => rfl
  | D + 1, hD => by
      have hb (d : Fin 5) :=
        count_bswapLevelBlocks145 L d .TOFF (fun _ _ _ ↦ rfl) (levelBlocks145 d) le_rfl
      simp [wShiftFromDyn145, shiftParityCirc145, XMeasCircuit.remeasureIfDyn, DynamicCircuit.count,
        hb, count_wShiftFromDyn145_toff v L D (by omega)]

theorem count_wShiftFromDyn145_t {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    ∀ (D : ℕ) (hD : D ≤ 5), (wShiftFromDyn145 v L D hD).count .T = 2 * D
  | 0, _ => rfl
  | D + 1, hD => by
      have hb (d : Fin 5) :=
        count_bswapLevelBlocks145 L d .T (fun _ _ _ ↦ rfl) (levelBlocks145 d) le_rfl
      simp [wShiftFromDyn145, shiftParityCirc145, XMeasCircuit.remeasureIfDyn, DynamicCircuit.count,
        hb, count_wShiftFromDyn145_t v L D (by omega)]
      omega

/-- Deletes bit `d` from a `5`-bit leaf offset `p : Fin 32`. -/
def shrinkBit145 (d : Fin 5) (p : Fin 32) : Fin 16 :=
  ⟨p.val % 2 ^ d.val + 2 ^ d.val * (p.val / 2 ^ (d.val + 1)), by revert d p; decide⟩

/-- Toggles bit `d` of a `5`-bit leaf offset `p : Fin 32`. -/
def flipLeafBit145 (d : Fin 5) (p : Fin 32) : Fin 32 :=
  if p.val / 2 ^ d.val % 2 = 0 then StepCore.insertOneBit d (shrinkBit145 d p)
  else StepCore.insertZeroBit d (shrinkBit145 d p)

theorem shrinkBit145_props (d : Fin 5) (s : Fin 16) (p : Fin 32) :
    shrinkBit145 d (StepCore.insertZeroBit d s) = s ∧
    shrinkBit145 d (StepCore.insertOneBit d s) = s ∧
    shrinkBit145 d (flipLeafBit145 d p) = shrinkBit145 d p ∧
    ((StepCore.insertZeroBit d (shrinkBit145 d p) = p ∧
      StepCore.insertOneBit d (shrinkBit145 d p) = flipLeafBit145 d p) ∨
     (StepCore.insertOneBit d (shrinkBit145 d p) = p ∧
      StepCore.insertZeroBit d (shrinkBit145 d p) = flipLeafBit145 d p)) := by
  exact ⟨by revert d s; decide, by revert d s; decide,
    by revert d p; decide, by revert d p; decide⟩

theorem flipLeafBit145_lt_16 (d' : Fin 5) (p' : Fin 16) :
    d'.val < 4 → (flipLeafBit145 d' ⟨p'.val, by omega⟩).val < 16 := by
  revert d' p'; decide

theorem flipLeafBit145_lt_cap {d : Fin 5} {b : Fin 6} {p₀ : ℕ}
    (hb : b.val < levelBlocks145 d) (hp₀ : p₀ < leafCap145 b) :
    (flipLeafBit145 d ⟨p₀, by dsimp [leafCap145] at hp₀; split_ifs at hp₀ <;> omega⟩).val <
      leafCap145 b := by
  by_cases hb4 : b.val < 4
  · simp only [leafCap145, hb4, ↓reduceIte]; exact (flipLeafBit145 d ⟨p₀, _⟩).isLt
  · have hbEq4 : b.val = 4 := by
      have := b.isLt; dsimp [levelBlocks145] at hb; split_ifs at hb <;> omega
    have hd4 : d.val < 4 := by dsimp [levelBlocks145] at hb; split_ifs at hb <;> omega
    have hp16 : p₀ < 16 := by simp only [leafCap145, hbEq4, ↓reduceIte] at hp₀; exact hp₀
    simp only [leafCap145, hbEq4, ↓reduceIte]
    exact flipLeafBit145_lt_16 d ⟨p₀, hp16⟩ hd4

theorem swap_ket_00_145 {n : ℕ} (a b : Wire n) (hab : a ≠ b) {γ : BitAssignment n}
    (ha : γ a = 0) (hb : γ b = 0) :
    (Circuit.SWAP a b hab).eval.1.mulVec (XMeasCircuit.ket γ) = XMeasCircuit.ket γ := by
  rw [CircuitModular.UnsignedGivens.evolve_SWAP_ket, ha, hb]
  congr 1; funext w
  by_cases hwb : w = b
  · subst hwb; simp [hb]
  · by_cases hwa : w = a
    · subst hwa; simp [Function.update_of_ne hwb, ha]
    · simp [Function.update_of_ne hwb, Function.update_of_ne hwa]

theorem swap_ket_10_145 {n : ℕ} (a b : Wire n) (hab : a ≠ b) {β : BitAssignment n}
    (ha : β a = 0) (hb : β b = 0) :
    (Circuit.SWAP a b hab).eval.1.mulVec (XMeasCircuit.ket (Function.update β a 1)) =
      XMeasCircuit.ket (Function.update β b 1) ∧
    (Circuit.SWAP a b hab).eval.1.mulVec (XMeasCircuit.ket (Function.update β b 1)) =
      XMeasCircuit.ket (Function.update β a 1) := by
  constructor
  · rw [CircuitModular.UnsignedGivens.evolve_SWAP_ket]; congr 1; funext w
    by_cases hwb : w = b
    · subst hwb; simp
    · by_cases hwa : w = a
      · subst hwa; simp [Function.update_of_ne hwb, Function.update_of_ne hab.symm, ha, hb]
      · simp [Function.update_of_ne hwb, Function.update_of_ne hwa]
  · rw [CircuitModular.UnsignedGivens.evolve_SWAP_ket]; congr 1; funext w
    by_cases hwb : w = b
    · subst hwb
      rw [Function.update_self, Function.update_of_ne hab, ha, Function.update_of_ne hab.symm, hb]
    · by_cases hwa : w = a
      · subst hwa; simp [Function.update_of_ne hwb]
      · simp [Function.update_of_ne hwb, Function.update_of_ne hwa]

theorem shrinkBit145_lt_8 (d' : Fin 5) (p' : Fin 16) :
    d'.val < 4 → (shrinkBit145 d' ⟨p'.val, by omega⟩).val < 8 := by
  revert d' p'; decide

theorem shrinkBit145_lt_pairs {d : Fin 5} {b : Fin 6} {p₀ : ℕ}
    (hb : b.val < levelBlocks145 d) (hp₀ : p₀ < leafCap145 b) :
    (shrinkBit145 d ⟨p₀, by dsimp [leafCap145] at hp₀; split_ifs at hp₀ <;> omega⟩).val <
      bswapPairs145 b := by
  by_cases hb4 : b.val < 4
  · simp only [bswapPairs145, hb4, ↓reduceIte]; exact (shrinkBit145 d ⟨p₀, _⟩).isLt
  · have hbEq4 : b.val = 4 := by
      have := b.isLt; dsimp [levelBlocks145] at hb; split_ifs at hb <;> omega
    have hd4 : d.val < 4 := by dsimp [levelBlocks145] at hb; split_ifs at hb <;> omega
    have hp16 : p₀ < 16 := by simp only [leafCap145, hbEq4, ↓reduceIte] at hp₀; exact hp₀
    simp only [bswapPairs145, hb4, ↓reduceIte]
    exact shrinkBit145_lt_8 d ⟨p₀, hp16⟩ hd4

theorem bswapBlockFrom145_ket {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (b b₀ : Fin 6) (hb : b.val < levelBlocks145 d) (p₀ : ℕ) (hp₀ : p₀ < leafCap145 b₀)
    {β : BitAssignment n} (hOh : ∀ g : Fin 145, β (L.rOneHot145 g) = 0) :
    let p32 : Fin 32 := ⟨p₀, by dsimp [leafCap145] at hp₀; split_ifs at hp₀ <;> omega⟩
    ∀ (m : ℕ) (hm : m ≤ bswapPairs145 b),
      (bswapBlockFrom145 L d b hb m hm).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ p₀ hp₀) 1)) =
        if hc : b = b₀ ∧ (shrinkBit145 d p32).val < m then
          XMeasCircuit.ket (Function.update β
            (wLeaf145 L b₀ (flipLeafBit145 d p32).val
              (flipLeafBit145_lt_cap (by rw [← hc.1]; exact hb) hp₀)) 1)
        else XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ p₀ hp₀) 1) := by
  intro p32 m hm
  induction m with
  | zero =>
      simp only [bswapBlockFrom145, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec, Nat.not_lt_zero, and_false, ↓reduceDIte]
  | succ m ih =>
      let s16 : Fin 16 := ⟨m, by dsimp [bswapPairs145] at hm; split_ifs at hm <;> omega⟩
      have hzCap : (StepCore.insertZeroBit d s16).val < leafCap145 b :=
        insertZeroBit_lt_cap145 hb hm
      have hoCap : (StepCore.insertOneBit d s16).val < leafCap145 b :=
        insertOneBit_lt_cap145 hb hm
      have hpr := shrinkBit145_props d s16 p32
      rw [bswapBlockFrom145, StepEncK.eval_seq_mulVec, ih (by omega)]
      by_cases hprev : b = b₀ ∧ (shrinkBit145 d p32).val < m
      · have hflCap := flipLeafBit145_lt_cap (by rw [← hprev.1]; exact hb) hp₀
        rw [dite_eq_left hprev, dite_eq_left ⟨hprev.1, by omega⟩]
        have hns : s16 ≠ shrinkBit145 d (flipLeafBit145 d p32) := by
          rw [hpr.2.2.1]; intro heq; have hv := congrArg Fin.val heq; dsimp [s16] at hv; omega
        have hn0 : wLeaf145 L b (StepCore.insertZeroBit d s16).val hzCap ≠
            wLeaf145 L b₀ (flipLeafBit145 d p32).val hflCap := fun h ↦ by
          have hp := (wLeaf145_inj L h).2
          exact hns (by rw [← hpr.1]; exact congrArg (shrinkBit145 d) (Fin.ext hp))
        have hn1 : wLeaf145 L b (StepCore.insertOneBit d s16).val hoCap ≠
            wLeaf145 L b₀ (flipLeafBit145 d p32).val hflCap := fun h ↦ by
          have hp := (wLeaf145_inj L h).2
          exact hns (by rw [← hpr.2.1]; exact congrArg (shrinkBit145 d) (Fin.ext hp))
        exact swap_ket_00_145 _ _ _
          (by rw [Function.update_of_ne hn0]; exact hOh _)
          (by rw [Function.update_of_ne hn1]; exact hOh _)
      · rw [dite_eq_right hprev]
        by_cases hcur : b = b₀ ∧ (shrinkBit145 d p32).val = m
        · obtain ⟨rfl, hsm⟩ := hcur
          have hflCap := flipLeafBit145_lt_cap hb hp₀
          have hsEq : s16 = shrinkBit145 d p32 := Fin.ext hsm.symm
          rw [dite_eq_left ⟨rfl, by omega⟩]
          rcases hpr.2.2.2 with ⟨hz, ho⟩ | ⟨ho, hz⟩
          · have hz' : p₀ = (StepCore.insertZeroBit d s16).val :=
              congrArg Fin.val (hz.symm.trans (congrArg _ hsEq.symm))
            have ho' : (flipLeafBit145 d p32).val = (StepCore.insertOneBit d s16).val :=
              congrArg Fin.val (ho.symm.trans (congrArg _ hsEq.symm))
            have hw1 : wLeaf145 L b p₀ hp₀ =
                wLeaf145 L b (StepCore.insertZeroBit d s16).val hzCap :=
              congrArg L.rOneHot145 (Fin.ext (by dsimp [leafIdx145]; rw [hz']))
            have hw2 : wLeaf145 L b (flipLeafBit145 d p32).val hflCap =
                wLeaf145 L b (StepCore.insertOneBit d s16).val hoCap := by simp_rw [ho']
            rw [hw1, hw2]; exact (swap_ket_10_145 _ _ _ (hOh _) (hOh _)).1
          · have ho' : p₀ = (StepCore.insertOneBit d s16).val :=
              congrArg Fin.val (ho.symm.trans (congrArg _ hsEq.symm))
            have hz' : (flipLeafBit145 d p32).val = (StepCore.insertZeroBit d s16).val :=
              congrArg Fin.val (hz.symm.trans (congrArg _ hsEq.symm))
            have hw1 : wLeaf145 L b p₀ hp₀ =
                wLeaf145 L b (StepCore.insertOneBit d s16).val hoCap :=
              congrArg L.rOneHot145 (Fin.ext (by dsimp [leafIdx145]; rw [ho']))
            have hw2 : wLeaf145 L b (flipLeafBit145 d p32).val hflCap =
                wLeaf145 L b (StepCore.insertZeroBit d s16).val hzCap := by simp_rw [hz']
            rw [hw1, hw2]; exact (swap_ket_10_145 _ _ _ (hOh _) (hOh _)).2
        · have hnNext : ¬ (b = b₀ ∧ (shrinkBit145 d p32).val < m + 1) := fun ⟨hbEq, hlt⟩ ↦
            by_cases (fun heq : (shrinkBit145 d p32).val = m ↦ hcur ⟨hbEq, heq⟩)
              (fun hne ↦ hprev ⟨hbEq, by omega⟩)
          rw [dite_eq_right hnNext]
          have hn0 : wLeaf145 L b (StepCore.insertZeroBit d s16).val hzCap ≠
              wLeaf145 L b₀ p₀ hp₀ := fun h ↦ by
            obtain ⟨rfl, hp⟩ := wLeaf145_inj L h
            exact hcur ⟨rfl, by
              have hsEq : shrinkBit145 d p32 = s16 :=
                (congrArg (shrinkBit145 d) (Fin.ext hp.symm)).trans hpr.1
              exact congrArg Fin.val hsEq⟩
          have hn1 : wLeaf145 L b (StepCore.insertOneBit d s16).val hoCap ≠
              wLeaf145 L b₀ p₀ hp₀ := fun h ↦ by
            obtain ⟨rfl, hp⟩ := wLeaf145_inj L h
            exact hcur ⟨rfl, by
              have hsEq : shrinkBit145 d p32 = s16 :=
                (congrArg (shrinkBit145 d) (Fin.ext hp.symm)).trans hpr.2.1
              exact congrArg Fin.val hsEq⟩
          exact swap_ket_00_145 _ _ _
            (by rw [Function.update_of_ne hn0]; exact hOh _)
            (by rw [Function.update_of_ne hn1]; exact hOh _)

theorem bswapLevelBlocks145_ket {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (b₀ : Fin 6) (p₀ : ℕ) (hp₀ : p₀ < leafCap145 b₀)
    {β : BitAssignment n} (hOh : ∀ g : Fin 145, β (L.rOneHot145 g) = 0) :
    let p32 : Fin 32 := ⟨p₀, by dsimp [leafCap145] at hp₀; split_ifs at hp₀ <;> omega⟩
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 d),
      (bswapLevelBlocks145 L d B hB).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ p₀ hp₀) 1)) =
        if hc : b₀.val < B then
          XMeasCircuit.ket (Function.update β
            (wLeaf145 L b₀ (flipLeafBit145 d p32).val
              (flipLeafBit145_lt_cap (lt_of_lt_of_le hc hB) hp₀)) 1)
        else XMeasCircuit.ket (Function.update β (wLeaf145 L b₀ p₀ hp₀) 1) := by
  intro p32 B hB
  induction B with
  | zero =>
      simp only [bswapLevelBlocks145, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec, Nat.not_lt_zero, ↓reduceDIte]
  | succ B ih =>
      have hlt6 : B < 6 := by dsimp [levelBlocks145] at hB; split_ifs at hB <;> omega
      rw [bswapLevelBlocks145, StepEncK.eval_seq_mulVec, ih (by omega)]
      by_cases hlt : b₀.val < B
      · have hne : (⟨B, hlt6⟩ : Fin 6) ≠ b₀ := fun h ↦ by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        rw [dite_eq_left hlt, bswapBlockFrom145_ket L d _ _ _ _ _ hOh _ le_rfl,
          dite_eq_right (fun h ↦ hne h.1), dite_eq_left (by omega)]
      · rw [dite_eq_right hlt, bswapBlockFrom145_ket L d _ _ _ _ _ hOh _ le_rfl]
        by_cases heq : b₀.val = B
        · have hbEq : (⟨B, hlt6⟩ : Fin 6) = b₀ := Fin.ext heq.symm
          have hshLt : (shrinkBit145 d p32).val < bswapPairs145 ⟨B, hlt6⟩ := by
            rw [hbEq]; exact shrinkBit145_lt_pairs (by omega) hp₀
          rw [dite_eq_left ⟨hbEq, hshLt⟩, dite_eq_left (by omega)]
        · have hne : (⟨B, hlt6⟩ : Fin 6) ≠ b₀ := fun h ↦ heq (congrArg Fin.val h).symm
          rw [dite_eq_right (fun h ↦ hne h.1), dite_eq_right (by omega)]

/-- Remaining active barrel-shift stages for block `b` after `5 - D` steps. -/
def shiftRem145 (b : Fin 6) (D : ℕ) : ℕ :=
  if b.val < 4 then D else if b.val = 4 then D - 1 else 0

theorem shiftLeafIdx145_lt_cap {b : Fin 6} {D : ℕ} (hD : D ≤ 5) {lo : ℕ}
    (hlo : lo < leafCap145 b) (t : Fin (2 ^ shiftRem145 b D)) :
    lo % 2 ^ (5 - D) + 2 ^ (5 - D) * t.val < leafCap145 b := by
  have ht := t.isLt
  rcases (by omega : D = 0 ∨ D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases b <;> (dsimp [shiftRem145, leafCap145] at ht hlo ⊢; omega)

/-- Intermediate barrel-shifted W-state superposition at stage `D` on `Phase2Bal161Layout`. -/
noncomputable def wShiftVec145 {n : ℕ} (L : Phase2Bal161Layout n) (D : ℕ) (hD : D ≤ 5)
    (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  let b₀ := b0E145 L β
  if hlo : loE145 L β < leafCap145 b₀ then
    (XMeasCircuit.sqrtHalf ^ shiftRem145 b₀ D) •
      ∑ t : Fin (2 ^ shiftRem145 b₀ D),
        XMeasCircuit.ket (Function.update β
          (wLeaf145 L b₀ (loE145 L β % 2 ^ (5 - D) + 2 ^ (5 - D) * t.val)
            (shiftLeafIdx145_lt_cap hD hlo t)) 1)
  else 0

/-- Equivalence splitting `Fin (2 ^ (R + 1))` into even and odd indices. -/
def finTwoPowEvenOdd145 (R : ℕ) : Fin (2 ^ R) ⊕ Fin (2 ^ R) ≃ Fin (2 ^ (R + 1)) where
  toFun
    | .inl s => ⟨2 * s.val, by have := s.isLt; omega⟩
    | .inr s => ⟨1 + 2 * s.val, by have := s.isLt; omega⟩
  invFun t :=
    if t.val % 2 = 0 then .inl ⟨t.val / 2, by have := t.isLt; omega⟩
    else .inr ⟨t.val / 2, by have := t.isLt; omega⟩
  left_inv x := by
    cases x with
    | inl s => dsimp; rw [ite_posE (by omega)]; exact congrArg Sum.inl (Fin.ext (by dsimp; omega))
    | inr s => dsimp; rw [ite_negE (by omega)]; exact congrArg Sum.inr (Fin.ext (by dsimp; omega))
  right_inv t := by dsimp; split_ifs <;> exact Fin.ext (by dsimp; omega)

theorem sum_even_odd145 {M : Type*} [AddCommMonoid M] (R : ℕ)
    (f : Fin (2 ^ (R + 1)) → M) :
    (∑ t : Fin (2 ^ (R + 1)), f t) =
      ∑ s : Fin (2 ^ R),
        (f ⟨2 * s.val, by have := s.isLt; omega⟩ +
          f ⟨1 + 2 * s.val, by have := s.isLt; omega⟩) := by
  rw [← Equiv.sum_comp (finTwoPowEvenOdd145 R) f, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

theorem shiftParity_arith145 {x p₀ : ℕ} (hx : x < 145) (d : Fin 5) :
    let b₀ : Fin 6 := if hx4 : x < 144 then ⟨x / 32, by omega⟩ else 5
    let lo : ℕ := if x < 144 then x % 32 else 0
    ∀ (hp₀ : p₀ < leafCap145 b₀),
      (if shiftParityMask145 d (leafIdx145 b₀ p₀ hp₀) then (1 : ZMod 2) else 0) +
          (if x / 2 ^ d.val % 2 = 1 then 1 else 0) =
        if b₀.val < levelBlocks145 d then
          (if p₀ / 2 ^ d.val % 2 = 1 then 1 else 0) +
            (if lo / 2 ^ d.val % 2 = 1 then 1 else 0)
        else 0 := by
  intro b₀ lo hp₀
  have hxbit : x / 2 ^ d.val % 2 = (x % 32) / 2 ^ d.val % 2 := by
    fin_cases d <;> (dsimp; omega)
  by_cases hd4 : d.val < 4
  · have hblk : levelBlocks145 d = 5 := ite_eq_left hd4
    by_cases h144 : x < 144
    · have hbLt : b₀.val < 5 := by dsimp [b₀]; rw [dite_eq_left h144]; dsimp; omega
      have hg144 : (leafIdx145 b₀ p₀ hp₀).val < 144 := by
        dsimp [leafIdx145, leafBase145, leafCap145, b₀] at hp₀ ⊢
        rw [dite_eq_left h144] at hp₀ ⊢; dsimp at hp₀ ⊢; split_ifs at hp₀ ⊢ <;> omega
      have hgMod : (leafIdx145 b₀ p₀ hp₀).val % 32 = p₀ := by
        dsimp [leafIdx145, leafBase145, leafCap145, b₀] at hp₀ ⊢
        rw [dite_eq_left h144] at hp₀ ⊢; dsimp at hp₀ ⊢; split_ifs at hp₀ ⊢ <;> omega
      have hlo : lo = x % 32 := ite_eq_left h144
      simp [shiftParityMask145, hd4, hblk, hbLt, hg144, hgMod, hxbit, hlo]
    · have hxEq : x = 144 := by omega
      subst hxEq; dsimp [b₀] at hp₀ ⊢
      have hp0 : p₀ = 0 := by dsimp [leafCap145] at hp₀; omega
      subst hp0
      have hd0 : 144 / 2 ^ d.val % 2 = 0 := by revert hd4; fin_cases d <;> decide
      simp [shiftParityMask145, hd4, hblk, leafIdx145, leafBase145, hd0]
  · have hdEq4 : d.val = 4 := by have := d.isLt; omega
    have hblk : levelBlocks145 d = 4 := ite_eq_right hd4
    by_cases h128 : x < 128
    · have h144 : x < 144 := by omega
      have hbLt : b₀.val < 4 := by dsimp [b₀]; rw [dite_eq_left h144]; dsimp; omega
      have hg128 : (leafIdx145 b₀ p₀ hp₀).val < 128 := by
        dsimp [leafIdx145, leafBase145, leafCap145, b₀] at hp₀ ⊢
        rw [dite_eq_left h144] at hp₀ ⊢; dsimp at hp₀ ⊢; split_ifs at hp₀ ⊢ <;> omega
      have hgNe144 : (leafIdx145 b₀ p₀ hp₀).val ≠ 144 := by omega
      have hgMod : (leafIdx145 b₀ p₀ hp₀).val % 32 = p₀ := by
        dsimp [leafIdx145, leafBase145, leafCap145, b₀] at hp₀ ⊢
        rw [dite_eq_left h144] at hp₀ ⊢; dsimp at hp₀ ⊢; split_ifs at hp₀ ⊢ <;> omega
      have hlo : lo = x % 32 := ite_eq_left h144
      have hxbit16 : x / 16 % 2 = (x % 32) / 16 % 2 := by omega
      simp [shiftParityMask145, hdEq4, hblk, hbLt, hg128, hgNe144, hgMod, hxbit16, hlo]
    · by_cases h144 : x < 144
      · have hbEq4 : b₀.val = 4 := by dsimp [b₀]; rw [dite_eq_left h144]; dsimp; omega
        have hgBounds : ¬ ((leafIdx145 b₀ p₀ hp₀).val < 128) ∧
            (leafIdx145 b₀ p₀ hp₀).val ≠ 144 := by
          dsimp [leafIdx145, leafBase145, leafCap145] at hp₀ ⊢
          rw [hbEq4] at hp₀ ⊢; simp at hp₀ ⊢; omega
        have hx0 : x / 16 % 2 = 0 := by omega
        simp [shiftParityMask145, hdEq4, hblk, hbEq4, hgBounds.1, hgBounds.2, hx0]
      · have hxEq : x = 144 := by omega
        subst hxEq; dsimp [b₀] at hp₀ ⊢
        have hp0 : p₀ = 0 := by dsimp [leafCap145] at hp₀; omega
        subst hp0
        simp [shiftParityMask145, hdEq4, hblk, leafIdx145, leafBase145]

theorem shiftParityCirc145_ket {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) (p₀ : ℕ)
    {β : BitAssignment n} (hS : sValid145 L β) (hp₀ : p₀ < leafCap145 (b0E145 L β)) :
    (shiftParityCirc145 L d).eval.1.mulVec
        (XMeasCircuit.ket (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1)) =
      XMeasCircuit.ket (Function.update (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1)
        L.qEnc
        (if (b0E145 L β).val < levelBlocks145 d then
          (if p₀ / 2 ^ d.val % 2 = 1 then 1 else 0) +
            (if loE145 L β / 2 ^ d.val % 2 = 1 then 1 else 0)
        else 0)) := by
  let γ := Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1
  let g₀ := leafIdx145 (b0E145 L β) p₀ hp₀
  have hq0 : γ L.qEnc = 0 := by
    dsimp [γ, wLeaf145, Phase2Bal161Layout.qEnc]
    rw [Function.update_of_ne (oh145_ne_rest L _ 2).symm]
    exact rest14_zero_of_sValid hS 2
  have hmask : CircuitModular.UnsignedGivens.maskSumBit L.rOneHot145 (shiftParityMask145 d) γ =
      if shiftParityMask145 d g₀ then 1 else 0 := by
    dsimp only [CircuitModular.UnsignedGivens.maskSumBit]
    have hite (g : Fin 145) :
        (if shiftParityMask145 d g then γ (L.rOneHot145 g) else 0) =
          if g = g₀ then (if shiftParityMask145 d g₀ then (1 : ZMod 2) else 0) else 0 := by
      by_cases hg : g = g₀
      · subst hg; have h1 : γ (L.rOneHot145 g₀) = 1 := Function.update_self _ _ _
        rw [ite_posE rfl, h1]
      · have h0 : γ (L.rOneHot145 g) = 0 := by
          dsimp [γ, wLeaf145]; rw [Function.update_of_ne (L.rOneHot145.wires.injective.ne hg)]
          exact oh145_zero_of_sValid hS g
        rw [ite_negE hg, h0, ite_self]
    simp_rw [hite]; rw [Finset.sum_ite_eq' Finset.univ g₀, ite_posE (Finset.mem_univ g₀)]
  have hbit : γ (L.rSelPair8 ⟨d.val, by omega⟩) =
      if (UnsignedGivens.localIdx L.rSelPair8 β).val / 2 ^ d.val % 2 = 1 then 1 else 0 := by
    dsimp [γ, wLeaf145]
    rw [Function.update_of_ne (oh145_ne_pair L _ _).symm, selPair8_bit_eq_145 L β _]
  have hpairNeQ : L.rSelPair8 ⟨d.val, by omega⟩ ≠ L.qEnc := (rest14_ne_pair L 2 _).symm
  change (shiftParityCirc145 L d).eval.1.mulVec (XMeasCircuit.ket γ) = _
  rw [shiftParityCirc145, StepEncK.eval_seq_mulVec, ket_cnotMaskReg, hq0, zero_add, hmask,
    StepEncK.ket_CNOT, Function.update_self, Function.update_of_ne hpairNeQ,
    Function.update_idem, hbit]
  exact congrArg (fun v ↦ XMeasCircuit.ket (Function.update γ L.qEnc v))
    (shiftParity_arith145 hS.1 d hp₀)

attribute [irreducible] b0E145 loE145

theorem cHadPair145_eval_eq {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (cHadPair145 a b h).eval =
      (Circuit.CNOT b a h.symm).eval * (StepCore.wSplitPair a b h).eval := by
  have hc : (Circuit.CNOT b a h.symm).eval * (Circuit.CNOT b a h.symm).eval = 1 :=
    cnot_eval_sq145 b a h.symm
  have hw : (StepCore.wSplitPair a b h).eval =
      (Circuit.CNOT b a h.symm).eval * (cHadPair145 a b h).eval := by
    dsimp only [StepCore.wSplitPair, cHadPair145]
    simp only [Circuit.eval_seq, mul_assoc]
  rw [hw, ← mul_assoc, hc, one_mul]

theorem cHadPair145_ket_00 {n : ℕ} (a b : Wire n) (h : a ≠ b)
    {β : BitAssignment n} (ha : β a = 0) (hb : β b = 0) :
    (cHadPair145 a b h).eval.1.mulVec (XMeasCircuit.ket β) = XMeasCircuit.ket β := by
  rw [cHadPair145_eval_eq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    wSplitPair_ket_00_145 a b h ha hb, StepEncK.ket_CNOT, hb, add_zero,
    Function.update_eq_self]

theorem cHadPair145_ket_01 {n : ℕ} (a b : Wire n) (h : a ≠ b)
    {β : BitAssignment n} (ha : β a = 0) (hb : β b = 1) :
    (cHadPair145 a b h).eval.1.mulVec (XMeasCircuit.ket β) = XMeasCircuit.ket β := by
  have hub1 : Function.update β b 1 = β := Function.update_eq_self_iff.mpr hb.symm
  have h10 : ((1 : ZMod 2) = 0) = False := by decide
  have hsq : XMeasCircuit.sqrtHalf ^ 2 = 1 / 2 := by
    linear_combination XMeasCircuit.sqrtHalf_mul_sqrtHalf
  have hp4 : XMeasCircuit.sqrtHalf ^ 4 = 1 / 4 := by
    linear_combination (XMeasCircuit.sqrtHalf ^ 2 + 1 / 2) * hsq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * Complex.I_sq
  have hi4 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq
  have hi5 : Complex.I ^ 5 = Complex.I := by linear_combination Complex.I * hi4
  simp only [cHadPair145, StepEncK.eval_seq_mulVec, ket_S_145, ket_T_145, XMeasCircuit.ket_H,
    XMeasCircuit.ket_Z, StepEncK.ket_CNOT, Matrix.mulVec_smul, Matrix.mulVec_add, ha, hb, h10,
    ↓reduceIte, one_smul, add_zero, Function.update_self, Function.update_idem,
    Function.update_of_ne h, hub1, XMeasCircuit.bitSign, smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  refine (congrArg₂ (· + ·) (congrArg (· • _) (?_ : _ = (0 : ℂ)))
    (congrArg (· • _) (?_ : _ = (1 : ℂ)))).trans (by simp)
  · rw [omega8_145_eq]; ring_nf; simp only [hsq, hp4, Complex.I_sq, hi3, hi4]; ring
  · rw [omega8_145_eq]; ring_nf; simp only [hsq, hp4, Complex.I_sq, hi3, hi4, hi5]; ring

theorem cHadPair145_ket_0 {n : ℕ} (a b : Wire n) (h : a ≠ b)
    {β : BitAssignment n} (ha : β a = 0) :
    (cHadPair145 a b h).eval.1.mulVec (XMeasCircuit.ket β) = XMeasCircuit.ket β := by
  rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β b) with hb0 | hb1
  · exact cHadPair145_ket_00 a b h ha hb0
  · exact cHadPair145_ket_01 a b h ha hb1

theorem cHadPair145_ket_10 {n : ℕ} (a b : Wire n) (h : a ≠ b)
    {β : BitAssignment n} (ha : β a = 1) (hb : β b = 0) :
    (cHadPair145 a b h).eval.1.mulVec (XMeasCircuit.ket β) =
      XMeasCircuit.sqrtHalf • XMeasCircuit.ket β +
        XMeasCircuit.sqrtHalf • XMeasCircuit.ket (Function.update β b 1) := by
  rw [cHadPair145_eval_eq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    wSplitPair_ket_10_145 a b h ha hb, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, StepEncK.ket_CNOT, hb, add_zero, Function.update_eq_self,
    StepEncK.ket_CNOT]
  congr 3; funext w
  by_cases hwa : w = a
  · subst hwa; simp [Function.update_of_ne h, ha]
  · by_cases hwb : w = b
    · subst hwb; simp [Function.update_of_ne hwa]
    · simp [Function.update_of_ne hwa, Function.update_of_ne hwb]

theorem ctrlHad145_val {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) (p₀ : ℕ)
    {β : BitAssignment n} (hS : sValid145 L β) (hp₀ : p₀ < leafCap145 (b0E145 L β))
    (qVal : ZMod 2) :
    Function.update (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1) L.qEnc qVal
        (ctrlHad145 L d) =
      if (b0E145 L β).val < levelBlocks145 d then 0 else 1 := by
  rw [Function.update_of_ne (ctrlHad145_ne_qEnc L d)]
  have hx := hS.1
  by_cases hd4 : d.val < 4
  · rw [ctrlHad145, ite_eq_left hd4, levelBlocks145, ite_eq_left hd4]
    by_cases hb5 : (b0E145 L β).val < 5
    · have hne : wLeaf145 L 5 0 (leafCap145_pos 5) ≠ wLeaf145 L (b0E145 L β) p₀ hp₀ :=
        fun h ↦ by have hb := (wLeaf145_inj L h).1; rw [← hb] at hb5; exact absurd hb5 (by decide)
      rw [ite_eq_left hb5, Function.update_of_ne hne]; exact oh145_zero_of_sValid hS _
    · have hbEq5 : b0E145 L β = 5 := Fin.ext (by have := (b0E145 L β).isLt; omega)
      have hpEq0 : p₀ = 0 := by rw [hbEq5] at hp₀; dsimp [leafCap145] at hp₀; omega
      subst hpEq0; rw [ite_eq_right hb5]; simp_rw [hbEq5]; exact Function.update_self _ _ _
  · rw [ctrlHad145, ite_eq_right hd4, levelBlocks145, ite_eq_right hd4,
      Function.update_of_ne (oh145_ne_pair L _ 7).symm, selPair8_bit_eq_145 L β 7]
    by_cases hx128 : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 128
    · have hx144 : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144 := by omega
      have hdiv0 : (UnsignedGivens.localIdx L.rSelPair8 β).val / 2 ^ (7 : Fin 8).val % 2 ≠ 1 :=
        by dsimp; omega
      have hb4 : (b0E145 L β).val < 4 := by rw [b0E145_of_lt144 hx144]; dsimp; omega
      rw [ite_eq_right hdiv0, ite_eq_left hb4]
    · have hdiv1 : (UnsignedGivens.localIdx L.rSelPair8 β).val / 2 ^ (7 : Fin 8).val % 2 = 1 :=
        by dsimp; omega
      have hnb4 : ¬ (b0E145 L β).val < 4 := by
        by_cases hx144 : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144
        · rw [b0E145_of_lt144 hx144]; dsimp; omega
        · rw [b0E145_of_not_lt144 hx144]; decide
      rw [ite_eq_left hdiv1, ite_eq_right hnb4]

theorem shift_even_odd_props145 (d : Fin 5) (lo : Fin 32) (s : Fin 16)
    (he : lo.val % 2 ^ d.val + 2 ^ d.val * (2 * s.val) < 32)
    (ho : lo.val % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val) < 32)
    (hn : lo.val % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val < 32) :
    let pe : Fin 32 := ⟨lo.val % 2 ^ d.val + 2 ^ d.val * (2 * s.val), he⟩
    let po : Fin 32 := ⟨lo.val % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val), ho⟩
    let pn : Fin 32 := ⟨lo.val % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val, hn⟩
    pe.val / 2 ^ d.val % 2 = 0 ∧ po.val / 2 ^ d.val % 2 = 1 ∧
      (lo.val / 2 ^ d.val % 2 = 0 → pe = pn ∧ flipLeafBit145 d po = pn) ∧
      (lo.val / 2 ^ d.val % 2 = 1 → po = pn ∧ flipLeafBit145 d pe = pn) := by
  revert d lo s he ho hn; decide +kernel

theorem shiftPhaseCirc145_ket {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) (p₀ : ℕ)
    {β : BitAssignment n} (hS : sValid145 L β) (hp₀ : p₀ < leafCap145 (b0E145 L β)) :
    (shiftParityCirc145 L d ;;ᶜ
      cHadPair145 (ctrlHad145 L d) L.qEnc (ctrlHad145_ne_qEnc L d)).eval.1.mulVec
        (XMeasCircuit.ket (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1)) =
      if (b0E145 L β).val < levelBlocks145 d then
        XMeasCircuit.ket (Function.update (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1)
          L.qEnc ((if p₀ / 2 ^ d.val % 2 = 1 then 1 else 0) +
            (if loE145 L β / 2 ^ d.val % 2 = 1 then 1 else 0)))
      else
        XMeasCircuit.sqrtHalf • XMeasCircuit.ket
            (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1) +
          XMeasCircuit.sqrtHalf • XMeasCircuit.ket
            (Function.update (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1) L.qEnc 1) := by
  rw [StepEncK.eval_seq_mulVec, shiftParityCirc145_ket L d p₀ hS hp₀]
  have hctrl := ctrlHad145_val L d p₀ hS hp₀
  by_cases hb : (b0E145 L β).val < levelBlocks145 d
  · rw [ite_eq_left hb, ite_eq_left hb]
    exact cHadPair145_ket_0 _ _ _ (by rw [hctrl, ite_eq_left hb])
  · rw [ite_eq_right hb, ite_eq_right hb]
    have hq0 : Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1 L.qEnc = 0 := by
      dsimp [wLeaf145, Phase2Bal161Layout.qEnc]
      rw [Function.update_of_ne (oh145_ne_rest L _ 2).symm]
      exact rest14_zero_of_sValid hS 2
    have hclr : Function.update (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1) L.qEnc 0 =
        Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1 :=
      Function.update_eq_self_iff.mpr hq0.symm
    have hc1 : Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1 (ctrlHad145 L d) = 1 := by
      rw [← hclr, hctrl 0, ite_eq_right hb]
    rw [hclr]; exact cHadPair145_ket_10 _ _ _ hc1 hq0

theorem shiftRem145_step_cases (b : Fin 6) {D : ℕ} (hD : D + 1 ≤ 5) :
    let d : Fin 5 := ⟨5 - (D + 1), by omega⟩
    (b.val < levelBlocks145 d → shiftRem145 b (D + 1) = shiftRem145 b D + 1) ∧
    (¬ (b.val < levelBlocks145 d) → shiftRem145 b (D + 1) = 0 ∧ shiftRem145 b D = 0) := by
  intro d; have := b.isLt
  dsimp [d, levelBlocks145, shiftRem145]; split_ifs <;> exact ⟨fun _ ↦ by omega, fun _ ↦ by omega⟩

theorem wShift145_kraus0 {n : ℕ} (L : Phase2Bal161Layout n) {D : ℕ} (hD : D + 1 ≤ 5)
    {β : BitAssignment n} (hS : sValid145 L β) :
    let d : Fin 5 := ⟨5 - (D + 1), by omega⟩
    let cStg := shiftParityCirc145 L d ;;ᶜ
      cHadPair145 (ctrlHad145 L d) L.qEnc (ctrlHad145_ne_qEnc L d)
    (QRegister.singleton L.qEnc).basisOutcomeProjector 0 *ᵥ
        (cStg.eval.1.mulVec (wShiftVec145 L (D + 1) hD β)) =
      XMeasCircuit.sqrtHalf • wShiftVec145 L D (by omega) β := by
  intro d cStg
  have hlo := loE145_lt_cap hS
  have hlo32 : loE145 L β < 32 := by dsimp [leafCap145] at hlo; split_ifs at hlo <;> omega
  have hq0 : β L.qEnc = 0 := rest14_zero_of_sValid hS 2
  have hd_eq : 5 - (D + 1) = d.val := rfl
  have hd1_eq : 5 - D = d.val + 1 := by dsimp [d]; omega
  have hrem := shiftRem145_step_cases (b0E145 L β) hD
  dsimp only [wShiftVec145]
  rw [dite_eq_left hlo, dite_eq_left hlo, Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Matrix.mulVec_sum]
  by_cases hb : (b0E145 L β).val < levelBlocks145 d
  · have hremEq := hrem.1 hb
    let R := shiftRem145 (b0E145 L β) D
    have hR4 : R ≤ 4 := by dsimp [R, shiftRem145]; split_ifs <;> omega
    rw [smul_sum_pow_cast145 hremEq (fun m hm ↦
      (QRegister.singleton L.qEnc).basisOutcomeProjector 0 *ᵥ
        (cStg.eval.1.mulVec (XMeasCircuit.ket (Function.update β
          (wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ (5 - (D + 1)) +
            2 ^ (5 - (D + 1)) * m) (shiftLeafIdx145_lt_cap hD hlo ⟨m, hm⟩)) 1)))),
      sum_even_odd145 R, smul_smul, _root_.pow_succ, mul_comm (XMeasCircuit.sqrtHalf ^ R)]
    congr 1; refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hs16 : s.val < 16 := lt_of_lt_of_le s.isLt
      (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hR4)
    let peN := loE145 L β % 2 ^ d.val + 2 ^ d.val * (2 * s.val)
    let poN := loE145 L β % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val)
    let pnN := loE145 L β % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val
    have hpeC : peN < leafCap145 (b0E145 L β) := shiftLeafIdx145_lt_cap hD hlo
      ⟨2 * s.val, by rw [hremEq, _root_.pow_succ]; have := s.isLt; dsimp only [R] at this; omega⟩
    have hpoC : poN < leafCap145 (b0E145 L β) := shiftLeafIdx145_lt_cap hD hlo ⟨1 + 2 * s.val,
      by rw [hremEq, _root_.pow_succ]; have := s.isLt; dsimp only [R] at this; omega⟩
    have hpnC : pnN < leafCap145 (b0E145 L β) := by
      simpa only [pnN, hd1_eq] using shiftLeafIdx145_lt_cap (by omega : D ≤ 5) hlo s
    have hpe32 : peN < 32 := by dsimp [leafCap145] at hpeC; split_ifs at hpeC <;> omega
    have hpo32 : poN < 32 := by dsimp [leafCap145] at hpoC; split_ifs at hpoC <;> omega
    have hpn32 : pnN < 32 := by dsimp [leafCap145] at hpnC; split_ifs at hpnC <;> omega
    have hp := shift_even_odd_props145 d ⟨loE145 L β, hlo32⟩ ⟨s.val, hs16⟩ hpe32 hpo32 hpn32
    rw [shiftPhaseCirc145_ket L d peN hS hpeC, shiftPhaseCirc145_ket L d poN hS hpoC,
      ite_eq_left hb, ite_eq_left hb]
    have hpeBit : peN / 2 ^ d.val % 2 = 0 := hp.1
    have hpoBit : poN / 2 ^ d.val % 2 = 1 := hp.2.1
    rw [hpeBit, hpoBit, XMeasCircuit.ket_projector_zero, XMeasCircuit.ket_projector_zero]
    rcases Nat.mod_two_eq_zero_or_one (loE145 L β / 2 ^ d.val) with hlo0 | hlo1
    · have hpePn : peN = pnN := congrArg Fin.val (hp.2.2.1 hlo0).1
      simp only [hlo0, Nat.zero_ne_one, ↓reduceIte, add_zero, Function.update_self, one_ne_zero]
      congr 1; funext w
      by_cases hw : w = L.qEnc
      · subst hw; rw [Function.update_self, Function.update_of_ne (oh145_ne_rest L _ 2).symm, hq0]
      · rw [Function.update_of_ne hw]
        exact congrArg (fun x ↦ Function.update β x 1 w)
          (wLeaf145_congr L _ _ _ (hpePn.trans (by dsimp only [pnN]; rw [hd1_eq])))
    · have hpoPn : poN = pnN := congrArg Fin.val (hp.2.2.2 hlo1).1
      simp only [hlo1, Nat.zero_ne_one, ↓reduceIte, zero_add, CharTwo.add_self_eq_zero,
        Function.update_self, one_ne_zero]
      congr 1; funext w
      by_cases hw : w = L.qEnc
      · subst hw; rw [Function.update_self, Function.update_of_ne (oh145_ne_rest L _ 2).symm, hq0]
      · rw [Function.update_of_ne hw]
        exact congrArg (fun x ↦ Function.update β x 1 w)
          (wLeaf145_congr L _ _ _ (hpoPn.trans (by dsimp only [pnN]; rw [hd1_eq])))
  · obtain ⟨hr1, hr0⟩ := hrem.2 hb
    have hpow0 {k : ℕ} (hk : k = 0) (g : ∀ m : ℕ, m < 2 ^ k → Fin (2 ^ n) → ℂ) :
        (XMeasCircuit.sqrtHalf ^ k) • (∑ t : Fin (2 ^ k), g t.val t.isLt) =
          g 0 (by rw [hk]; decide) := by subst hk; simp
    have hloMod : loE145 L β % 2 ^ (5 - (D + 1)) = loE145 L β ∧
        loE145 L β % 2 ^ (5 - D) = loE145 L β := by
      have hx := hS.1
      by_cases hx144 : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144
      · have hb' : ¬ (UnsignedGivens.localIdx L.rSelPair8 β).val / 32 < levelBlocks145 d := by
          rwa [b0E145_of_lt144 hx144] at hb
        dsimp [d, levelBlocks145] at hb'
        by_cases hd4 : 5 - (D + 1) < 4
        · rw [ite_eq_left hd4] at hb'; omega
        · have hd0 : D = 0 := by omega
          subst hd0; dsimp at hb'; rw [loE145_of_lt144 hx144]
          exact ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩
      · simp [loE145_of_not_lt144 hx144]
    rw [hpow0 hr1 (fun m hm ↦ (QRegister.singleton L.qEnc).basisOutcomeProjector 0 *ᵥ
          (cStg.eval.1.mulVec (XMeasCircuit.ket (Function.update β
            (wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ (5 - (D + 1)) +
              2 ^ (5 - (D + 1)) * m) (shiftLeafIdx145_lt_cap hD hlo ⟨m, hm⟩)) 1)))),
      hpow0 hr0 (fun m hm ↦ XMeasCircuit.ket (Function.update β
        (wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ (5 - D) + 2 ^ (5 - D) * m)
          (shiftLeafIdx145_lt_cap (by omega) hlo ⟨m, hm⟩)) 1))]
    simp only [mul_zero, add_zero]
    rw [shiftPhaseCirc145_ket L d _ hS _, ite_eq_right hb, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, XMeasCircuit.ket_projector_zero, XMeasCircuit.ket_projector_zero,
      Function.update_self, ite_eq_right one_ne_zero, smul_zero, add_zero,
      Function.update_of_ne (oh145_ne_rest L _ 2).symm, hq0, ite_eq_left rfl]
    congr 2; simp_rw [hloMod.1, hloMod.2]

theorem wShift145_kraus1 {n : ℕ} (L : Phase2Bal161Layout n) {D : ℕ} (hD : D + 1 ≤ 5)
    {β : BitAssignment n} (hS : sValid145 L β) :
    let d : Fin 5 := ⟨5 - (D + 1), by omega⟩
    let cStg := shiftParityCirc145 L d ;;ᶜ
      cHadPair145 (ctrlHad145 L d) L.qEnc (ctrlHad145_ne_qEnc L d)
    let cFix := Circuit.X L.qEnc ;;ᶜ bswapLevelBlocks145 L d (levelBlocks145 d) le_rfl
    cFix.eval.1.mulVec ((QRegister.singleton L.qEnc).basisOutcomeProjector 1 *ᵥ
        (cStg.eval.1.mulVec (wShiftVec145 L (D + 1) hD β))) =
      XMeasCircuit.sqrtHalf • wShiftVec145 L D (by omega) β := by
  intro d cStg cFix
  have hlo := loE145_lt_cap hS
  have hlo32 : loE145 L β < 32 := by dsimp [leafCap145] at hlo; split_ifs at hlo <;> omega
  have hq0 : β L.qEnc = 0 := rest14_zero_of_sValid hS 2
  have hd1_eq : 5 - D = d.val + 1 := by dsimp [d]; omega
  have hrem := shiftRem145_step_cases (b0E145 L β) hD
  have hclrQ (p₀ : ℕ) (hp₀ : p₀ < leafCap145 (b0E145 L β)) :
      Function.update (Function.update (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1)
        L.qEnc 1) L.qEnc
        (Function.update (Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1)
          L.qEnc 1 L.qEnc + 1) =
      Function.update β (wLeaf145 L (b0E145 L β) p₀ hp₀) 1 := by
    rw [Function.update_idem, Function.update_self, CharTwo.add_self_eq_zero]
    funext w; by_cases hw : w = L.qEnc
    · subst hw; rw [Function.update_self, Function.update_of_ne (oh145_ne_rest L _ 2).symm, hq0]
    · exact Function.update_of_ne hw _ _
  dsimp only [wShiftVec145]
  rw [dite_eq_left hlo, dite_eq_left hlo, Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_sum]
  by_cases hb : (b0E145 L β).val < levelBlocks145 d
  · have hremEq := hrem.1 hb
    let R := shiftRem145 (b0E145 L β) D
    have hR4 : R ≤ 4 := by dsimp [R, shiftRem145]; split_ifs <;> omega
    rw [smul_sum_pow_cast145 hremEq (fun m hm ↦ cFix.eval.1.mulVec
          ((QRegister.singleton L.qEnc).basisOutcomeProjector 1 *ᵥ
            (cStg.eval.1.mulVec (XMeasCircuit.ket (Function.update β
              (wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ (5 - (D + 1)) +
                2 ^ (5 - (D + 1)) * m) (shiftLeafIdx145_lt_cap hD hlo ⟨m, hm⟩)) 1))))),
      sum_even_odd145 R, smul_smul, _root_.pow_succ, mul_comm (XMeasCircuit.sqrtHalf ^ R)]
    congr 1; refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hs16 : s.val < 16 := lt_of_lt_of_le s.isLt
      (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hR4)
    let peN := loE145 L β % 2 ^ d.val + 2 ^ d.val * (2 * s.val)
    let poN := loE145 L β % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val)
    let pnN := loE145 L β % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val
    have hpeC : peN < leafCap145 (b0E145 L β) := shiftLeafIdx145_lt_cap hD hlo
      ⟨2 * s.val, by rw [hremEq, _root_.pow_succ]; have := s.isLt; dsimp only [R] at this; omega⟩
    have hpoC : poN < leafCap145 (b0E145 L β) := shiftLeafIdx145_lt_cap hD hlo ⟨1 + 2 * s.val,
      by rw [hremEq, _root_.pow_succ]; have := s.isLt; dsimp only [R] at this; omega⟩
    have hpnC : pnN < leafCap145 (b0E145 L β) := by
      simpa only [pnN, hd1_eq] using shiftLeafIdx145_lt_cap (by omega : D ≤ 5) hlo s
    have hpe32 : peN < 32 := by dsimp [leafCap145] at hpeC; split_ifs at hpeC <;> omega
    have hpo32 : poN < 32 := by dsimp [leafCap145] at hpoC; split_ifs at hpoC <;> omega
    have hpn32 : pnN < 32 := by dsimp [leafCap145] at hpnC; split_ifs at hpnC <;> omega
    have hp := shift_even_odd_props145 d ⟨loE145 L β, hlo32⟩ ⟨s.val, hs16⟩ hpe32 hpo32 hpn32
    rw [shiftPhaseCirc145_ket L d peN hS hpeC, shiftPhaseCirc145_ket L d poN hS hpoC,
      ite_eq_left hb, ite_eq_left hb]
    have hpeBit : peN / 2 ^ d.val % 2 = 0 := hp.1
    have hpoBit : poN / 2 ^ d.val % 2 = 1 := hp.2.1
    rw [hpeBit, hpoBit, XMeasCircuit.ket_projector_one, XMeasCircuit.ket_projector_one]
    rcases Nat.mod_two_eq_zero_or_one (loE145 L β / 2 ^ d.val) with hlo0 | hlo1
    · have hflPn : (flipLeafBit145 d ⟨poN, hpo32⟩).val = pnN := congrArg Fin.val (hp.2.2.1 hlo0).2
      simp only [hlo0, ↓reduceIte, add_zero, zero_add, Function.update_self, zero_ne_one,
        Matrix.mulVec_zero]
      rw [StepEncK.eval_seq_mulVec, XMeasCircuit.ket_X, hclrQ poN hpoC,
        bswapLevelBlocks145_ket L d _ poN hpoC (oh145_zero_of_sValid hS) _ le_rfl, dite_eq_left hb]
      congr 2; exact wLeaf145_congr L _ _ _ (hflPn.trans (by dsimp only [pnN]; rw [hd1_eq]))
    · have hflPn : (flipLeafBit145 d ⟨peN, hpe32⟩).val = pnN := congrArg Fin.val (hp.2.2.2 hlo1).2
      simp only [hlo1, ↓reduceIte, zero_add, CharTwo.add_self_eq_zero, Function.update_self,
        zero_ne_one, Matrix.mulVec_zero, add_zero]
      rw [StepEncK.eval_seq_mulVec, XMeasCircuit.ket_X, hclrQ peN hpeC,
        bswapLevelBlocks145_ket L d _ peN hpeC (oh145_zero_of_sValid hS) _ le_rfl, dite_eq_left hb]
      congr 2; exact wLeaf145_congr L _ _ _ (hflPn.trans (by dsimp only [pnN]; rw [hd1_eq]))
  · obtain ⟨hr1, hr0⟩ := hrem.2 hb
    have hloMod : loE145 L β % 2 ^ (5 - (D + 1)) = loE145 L β ∧
        loE145 L β % 2 ^ (5 - D) = loE145 L β := by
      have hx := hS.1
      by_cases hx144 : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144
      · have hb' : ¬ (UnsignedGivens.localIdx L.rSelPair8 β).val / 32 < levelBlocks145 d := by
          rwa [b0E145_of_lt144 hx144] at hb
        dsimp [d, levelBlocks145] at hb'
        by_cases hd4 : 5 - (D + 1) < 4
        · rw [ite_eq_left hd4] at hb'; omega
        · have hd0 : D = 0 := by omega
          subst hd0; dsimp at hb'; rw [loE145_of_lt144 hx144]
          exact ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩
      · simp [loE145_of_not_lt144 hx144]
    rw [smul_sum_pow_zero145 hr1 (fun m hm ↦ cFix.eval.1.mulVec
          ((QRegister.singleton L.qEnc).basisOutcomeProjector 1 *ᵥ
            (cStg.eval.1.mulVec (XMeasCircuit.ket (Function.update β
              (wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ (5 - (D + 1)) +
                2 ^ (5 - (D + 1)) * m) (shiftLeafIdx145_lt_cap hD hlo ⟨m, hm⟩)) 1))))),
      smul_sum_pow_zero145 hr0 (fun m hm ↦ XMeasCircuit.ket (Function.update β
        (wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ (5 - D) + 2 ^ (5 - D) * m)
          (shiftLeafIdx145_lt_cap (by omega) hlo ⟨m, hm⟩)) 1))]
    simp only [mul_zero, add_zero]
    rw [shiftPhaseCirc145_ket L d _ hS _, ite_eq_right hb, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, XMeasCircuit.ket_projector_one, XMeasCircuit.ket_projector_one,
      Function.update_of_ne (oh145_ne_rest L _ 2).symm, hq0, ite_eq_right zero_ne_one,
      smul_zero, zero_add, Function.update_self, ite_eq_left rfl, Matrix.mulVec_smul,
      StepEncK.eval_seq_mulVec, XMeasCircuit.ket_X, hclrQ _ _,
      bswapLevelBlocks145_ket L d _ _ _ (oh145_zero_of_sValid hS) _ le_rfl, dite_eq_right hb]
    congr 2; simp_rw [hloMod.1, hloMod.2]

theorem wShiftFromDyn145_step {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (L : Phase2Bal161Layout n) :
    ∀ (D : ℕ) (hD : D ≤ 5),
      SubspaceStepU (Var := Var)
        (ketMapOp (sValid145 L) (wShiftVec145 L D hD))
        (ketMapOp (sValid145 L) (wShiftVec145 L 0 (by omega)))
        (wShiftFromDyn145 v L D hD)
  | 0, _ => SubspaceStepU.of_circuit (Var := Var) Circuit.identity
      (by rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul])
  | D + 1, hD => by
      rw [wShiftFromDyn145]
      let d : Fin 5 := ⟨5 - (D + 1), by omega⟩
      let cStg := shiftParityCirc145 L d ;;ᶜ
        cHadPair145 (ctrlHad145 L d) L.qEnc (ctrlHad145_ne_qEnc L d)
      refine SubspaceStepU.seq
        (SubspaceStepU.of_circuit (Var := Var) cStg
          (R₁ := ketMapOp (sValid145 L) fun β ↦
            cStg.eval.1.mulVec (wShiftVec145 L (D + 1) hD β))
          (by rw [mul_ketMapOp]))
        (SubspaceStepU.seq
          (SubspaceStepU.remeasure v L.qEnc _ ?_ ?_)
          (wShiftFromDyn145_step v L D (by omega)))
      · rw [mul_ketMapOp, smul_ketMapOp]
        exact ketMapOp_congr fun β hS ↦ wShift145_kraus0 L hD hS
      · refine SubspaceStepU.of_circuit (Var := Var) _ ?_
        rw [mul_ketMapOp, mul_ketMapOp, smul_ketMapOp]
        exact ketMapOp_congr fun β hS ↦ wShift145_kraus1 L hD hS

/-- Basis assignment after coherent `145`-leaf `W`-state unary encoding onto `L.rOneHot145`. -/
noncomputable def encAssign145 {n : ℕ} (L : Phase2Bal161Layout n)
    (β : BitAssignment n) : BitAssignment n :=
  Function.update β (wLeaf145 L (b0E145 L β) (loE145 L β) (loE145_lt_cap_all L β)) 1

/-- Coherent `145`-leaf `W`-state unary encoder (`296 T = 4 + 4 + 278 + 10`, `0 TOFF`). -/
def dEnc145Dyn {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    DynamicCircuit Var n :=
  .seq (.circuit (Circuit.andCompute (L.rSelPair8 5) (L.rSelPair8 6)
        (wLeaf145 L 3 0 (leafCap145_pos 3))
        (pair_ne_wRoot0 L 5 3) (pair_ne_wRoot0 L 6 3)))
    (.seq (.circuit (Circuit.andCompute (L.rSelPair8 7) (L.rSelPair8 4)
          (wLeaf145 L 5 0 (leafCap145_pos 5))
          (pair_ne_wRoot0 L 7 5) (pair_ne_wRoot0 L 4 5)))
      (.seq (.circuit (wRoot6LinCirc145 L ;;ᶜ wTreePrefixLevels145 L 5 le_rfl))
        (wShiftFromDyn145 v L 5 le_rfl)))

@[simp] theorem count_dEnc145Dyn_toff {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    (dEnc145Dyn v L).count .TOFF = 0 := by
  simp [dEnc145Dyn, wRoot6LinCirc145, DynamicCircuit.count, count_wTreePrefixLevels145_toff,
    count_wShiftFromDyn145_toff]

@[simp] theorem count_dEnc145Dyn_t {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    (dEnc145Dyn v L).count .T = 296 := by
  simp [dEnc145Dyn, wRoot6LinCirc145, DynamicCircuit.count, count_wTreePrefixLevels145_t,
    count_wShiftFromDyn145_t]

theorem dEnc145Dyn_step {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (L : Phase2Bal161Layout n) :
    SubspaceStepU (Var := Var)
      (Lac2Fused184Select.ketPredProj (sValid145 L))
      (ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (encAssign145 L β)))
      (dEnc145Dyn v L) := by
  let w3 := wLeaf145 L 3 0 (leafCap145_pos 3)
  let w5 := wLeaf145 L 5 0 (leafCap145_pos 5)
  have h56 : L.rSelPair8 5 ≠ L.rSelPair8 6 := pair_ne_pair L (by decide)
  have h74 : L.rSelPair8 7 ≠ L.rSelPair8 4 := pair_ne_pair L (by decide)
  have hP : Lac2Fused184Select.ketPredProj (sValid145 L) =
      ketMapOp (sValid145 L) XMeasCircuit.ket := (ketMapOp_eq_ketPredProj _).symm
  have hClean3 : (QRegister.singleton w3).basisOutcomeProjector 0 *
      ketMapOp (sValid145 L) XMeasCircuit.ket = ketMapOp (sValid145 L) XMeasCircuit.ket := by
    rw [mul_ketMapOp]; refine ketMapOp_congr fun β hS ↦ ?_
    rw [XMeasCircuit.ket_projector_zero, ite_posE (oh145_zero_of_sValid hS _)]
  have hAnd3 := SubspaceStepU.of_andCompute (Var := Var)
    (L.rSelPair8 5) (L.rSelPair8 6) w3 h56 (pair_ne_wRoot0 L 5 3) (pair_ne_wRoot0 L 6 3) hClean3
  let R₃ := (Circuit.TOFF (L.rSelPair8 5) (L.rSelPair8 6) w3 h56
    (pair_ne_wRoot0 L 5 3) (pair_ne_wRoot0 L 6 3)).eval.1 *
    ketMapOp (sValid145 L) XMeasCircuit.ket
  have hClean5 : (QRegister.singleton w5).basisOutcomeProjector 0 * R₃ = R₃ := by
    dsimp only [R₃]; rw [mul_ketMapOp, mul_ketMapOp]
    refine ketMapOp_congr fun β hS ↦ ?_
    rw [StepEncK.ket_TOFF, XMeasCircuit.ket_projector_zero,
      Function.update_of_ne (wRoot0_ne L (by decide : (5 : Fin 6) ≠ 3)),
      ite_posE (oh145_zero_of_sValid hS _)]
  have hAnd5 := SubspaceStepU.of_andCompute (Var := Var)
    (L.rSelPair8 7) (L.rSelPair8 4) w5 h74 (pair_ne_wRoot0 L 7 5) (pair_ne_wRoot0 L 4 5) hClean5
  have hTree : (wRoot6LinCirc145 L ;;ᶜ wTreePrefixLevels145 L 5 le_rfl).eval.1 *
      ((Circuit.TOFF (L.rSelPair8 7) (L.rSelPair8 4) w5 h74
          (pair_ne_wRoot0 L 7 5) (pair_ne_wRoot0 L 4 5)).eval.1 * R₃) =
      ketMapOp (sValid145 L) (wShiftVec145 L 5 le_rfl) := by
    dsimp only [R₃]; rw [mul_ketMapOp, mul_ketMapOp, mul_ketMapOp]
    refine ketMapOp_congr fun β hS ↦ ?_
    have hw30 : β w3 = 0 := oh145_zero_of_sValid hS _
    have hw50 : Function.update β w3 (β (L.rSelPair8 5) * β (L.rSelPair8 6)) w5 = 0 := by
      rw [Function.update_of_ne (wRoot0_ne L (by decide : (5 : Fin 6) ≠ 3))]
      exact oh145_zero_of_sValid hS _
    have hp7 : Function.update β w3 (β (L.rSelPair8 5) * β (L.rSelPair8 6)) (L.rSelPair8 7) =
        β (L.rSelPair8 7) := Function.update_of_ne (pair_ne_wRoot0 L 7 3) _ _
    have hp4 : Function.update β w3 (β (L.rSelPair8 5) * β (L.rSelPair8 6)) (L.rSelPair8 4) =
        β (L.rSelPair8 4) := Function.update_of_ne (pair_ne_wRoot0 L 4 3) _ _
    rw [StepEncK.ket_TOFF, hw30, zero_add, StepEncK.ket_TOFF, hw50, zero_add, hp7, hp4,
      StepEncK.eval_seq_mulVec, wRoot6LinCirc145_ket L hS,
      wTreePrefixLevels145_ket L hS 5 le_rfl]
    have htdEq : treeDepth145 (b0E145 L β) 5 = shiftRem145 (b0E145 L β) 5 := by
      dsimp [treeDepth145, shiftRem145]; split_ifs <;> rfl
    dsimp only [wTreeVec145, wShiftVec145]
    rw [dite_eq_left (loE145_lt_cap hS), smul_sum_pow_cast145 htdEq (fun m hm ↦ XMeasCircuit.ket
      (Function.update β (wLeaf145 L (b0E145 L β) m
        (lt_of_lt_of_le hm (pow_treeDepth145_le_cap (b0E145 L β) le_rfl))) 1))]
    apply congrArg (_ • ·); refine Finset.sum_congr rfl fun t _ ↦ ?_
    simp only [Nat.sub_self, _root_.pow_zero, Nat.mod_one, zero_add, one_mul]
  have hEnd : ketMapOp (sValid145 L) (wShiftVec145 L 0 (by omega)) =
      ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (encAssign145 L β)) := by
    refine ketMapOp_congr fun β hS ↦ ?_
    have hlo := loE145_lt_cap hS
    have hr0 : shiftRem145 (b0E145 L β) 0 = 0 := by dsimp [shiftRem145]; split_ifs <;> rfl
    have hlo32 : loE145 L β % 32 = loE145 L β :=
      Nat.mod_eq_of_lt (by dsimp [leafCap145] at hlo; split_ifs at hlo <;> omega)
    dsimp only [wShiftVec145, encAssign145]
    rw [dite_eq_left hlo, smul_sum_pow_zero145 hr0 (fun m hm ↦ XMeasCircuit.ket
      (Function.update β (wLeaf145 L (b0E145 L β)
        (loE145 L β % 2 ^ (5 - 0) + 2 ^ (5 - 0) * m)
        (shiftLeafIdx145_lt_cap (by omega) hlo ⟨m, hm⟩)) 1))]
    congr 2; apply wLeaf145_congr; simp only [Nat.sub_zero, mul_zero, add_zero]; exact hlo32
  exact SubspaceStepU.congr hP.symm hEnd
    (SubspaceStepU.seq hAnd3
      (SubspaceStepU.seq hAnd5
        (SubspaceStepU.seq (SubspaceStepU.of_circuit (Var := Var) _ hTree)
          (wShiftFromDyn145_step v L 5 le_rfl))))

/-- Fold CNOTs `CNOT w[b, s + 2^d] w[b, s]` for `s < m` (`m ≤ 2^d`) in block `b`. -/
def wFoldBlockFrom145 {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) (b : Fin 6)
    (hb : b.val < levelBlocks145 d) : ∀ (m : ℕ), m ≤ 2 ^ d.val → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      have hcap := two_mul_pow_le_cap145 hb
      wFoldBlockFrom145 L d b hb m (by omega) ;;ᶜ
        Circuit.CNOT (wLeaf145 L b (m + 2 ^ d.val) (by omega))
          (wLeaf145 L b m (by omega))
          (fun h ↦ by have hp := (wLeaf145_inj L h).2; have := Nat.two_pow_pos d.val; omega)

/-- `B` blocks of `wFoldBlockFrom145` at level `d`. -/
def wFoldLevelBlocks145 {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5) :
    ∀ (B : ℕ), B ≤ levelBlocks145 d → Circuit n
  | 0, _ => .identity
  | B + 1, hB =>
      have hlt6 : B < 6 := by dsimp [levelBlocks145] at hB; split_ifs at hB <;> omega
      wFoldLevelBlocks145 L d B (by omega) ;;ᶜ
        wFoldBlockFrom145 L d ⟨B, hlt6⟩ (by dsimp; omega) (2 ^ d.val) le_rfl

/-- `0-T`, `0-TOFF` X-measurement unload of `w[b, s + 2^d]` (`s < m`) with `CZ(w[b, s], u_d)`. -/
def wUnloadBlockFrom145 {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n)
    (d : Fin 5) (b : Fin 6) (hb : b.val < levelBlocks145 d) :
    ∀ (m : ℕ), m ≤ 2 ^ d.val → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | m + 1, hm =>
      have hcap := two_mul_pow_le_cap145 hb
      .seq (wUnloadBlockFrom145 v L d b hb m (by omega))
        (XMeasCircuit.xMeasUnloadWireDyn v (wLeaf145 L b (m + 2 ^ d.val) (by omega))
          (.circuit (SelectSwapQROM.czCircuit (wLeaf145 L b m (by omega))
            (L.rSelPair8 ⟨d.val, by omega⟩) (oh145_ne_pair L _ _))))

/-- `B` blocks of `wUnloadBlockFrom145` at level `d`. -/
def wUnloadLevelBlocks145 {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) (d : Fin 5) :
    ∀ (B : ℕ), B ≤ levelBlocks145 d → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | B + 1, hB =>
      have hlt6 : B < 6 := by dsimp [levelBlocks145] at hB; split_ifs at hB <;> omega
      .seq (wUnloadLevelBlocks145 v L d B (by omega))
        (wUnloadBlockFrom145 v L d ⟨B, hlt6⟩ (by dsimp; omega) (2 ^ d.val) le_rfl)

/-- `5`-round `0-T`, `0-TOFF` MBU tree decoder for `145` leaves. -/
def wUncompTreeLevels145 {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    ∀ (R : ℕ), R ≤ 5 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | R + 1, hR =>
      let d : Fin 5 := ⟨R, hR⟩
      .seq (.seq (.circuit (wFoldLevelBlocks145 L d (levelBlocks145 d) le_rfl))
          (wUnloadLevelBlocks145 v L d (levelBlocks145 d) le_rfl))
        (wUncompTreeLevels145 v L R (by omega))

/-- Full `0-T`, `0-TOFF` MBU unary decoder uncomputing `encAssign145` back to `sValid145`. -/
def dDec145Dyn {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    DynamicCircuit Var n :=
  .seq (wUncompTreeLevels145 v L 5 le_rfl)
    (.seq (.circuit (wRoot6UninitLinCirc145 L))
      (.seq (XMeasCircuit.xMeasUnloadWireDyn v (wLeaf145 L 5 0 (leafCap145_pos 5))
            (.circuit (SelectSwapQROM.czCircuit (L.rSelPair8 7) (L.rSelPair8 4)
              (pair_ne_pair L (by decide)))))
        (XMeasCircuit.xMeasUnloadWireDyn v (wLeaf145 L 3 0 (leafCap145_pos 3))
          (.circuit (SelectSwapQROM.czCircuit (L.rSelPair8 5) (L.rSelPair8 6)
            (pair_ne_pair L (by decide)))))))

theorem count_wFoldBlockFrom145 {n k : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (b : Fin 6) (hb : b.val < levelBlocks145 d) (g : PrimitiveGate k)
    (hc : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.CNOT x y h).count g = 0) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val), (wFoldBlockFrom145 L d b hb m hm).count g = 0
  | 0, _ => rfl
  | m + 1, hm => by
      rw [wFoldBlockFrom145, Circuit.count_seq,
        count_wFoldBlockFrom145 L d b hb g hc m (by omega), hc, add_zero]

theorem count_wFoldLevelBlocks145 {n k : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (g : PrimitiveGate k)
    (hc : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.CNOT x y h).count g = 0) :
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 d), (wFoldLevelBlocks145 L d B hB).count g = 0
  | 0, _ => rfl
  | B + 1, hB => by
      rw [wFoldLevelBlocks145, Circuit.count_seq,
        count_wFoldLevelBlocks145 L d g hc B (by omega),
        count_wFoldBlockFrom145 L d _ _ g hc _ le_rfl, add_zero]

theorem count_wUnloadBlockFrom145_toff {Var : Type} {n : ℕ} (v : Var)
    (L : Phase2Bal161Layout n) (d : Fin 5) (b : Fin 6) (hb : b.val < levelBlocks145 d) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val), (wUnloadBlockFrom145 v L d b hb m hm).count .TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      simp [wUnloadBlockFrom145, DynamicCircuit.count, XMeasCircuit.xMeasUnloadWireDyn,
        SelectSwapQROM.count_czCircuit_toff,
        count_wUnloadBlockFrom145_toff v L d b hb m (by omega)]

theorem count_wUnloadBlockFrom145_t {Var : Type} {n : ℕ} (v : Var)
    (L : Phase2Bal161Layout n) (d : Fin 5) (b : Fin 6) (hb : b.val < levelBlocks145 d) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val), (wUnloadBlockFrom145 v L d b hb m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, hm => by
      simp [wUnloadBlockFrom145, DynamicCircuit.count, XMeasCircuit.xMeasUnloadWireDyn,
        SelectSwapQROM.count_czCircuit_t,
        count_wUnloadBlockFrom145_t v L d b hb m (by omega)]

theorem count_wUnloadLevelBlocks145_toff {Var : Type} {n : ℕ} (v : Var)
    (L : Phase2Bal161Layout n) (d : Fin 5) :
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 d), (wUnloadLevelBlocks145 v L d B hB).count .TOFF = 0
  | 0, _ => rfl
  | B + 1, hB => by
      simp [wUnloadLevelBlocks145, DynamicCircuit.count,
        count_wUnloadLevelBlocks145_toff v L d B (by omega), count_wUnloadBlockFrom145_toff]

theorem count_wUnloadLevelBlocks145_t {Var : Type} {n : ℕ} (v : Var)
    (L : Phase2Bal161Layout n) (d : Fin 5) :
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 d), (wUnloadLevelBlocks145 v L d B hB).count .T = 0
  | 0, _ => rfl
  | B + 1, hB => by
      simp [wUnloadLevelBlocks145, DynamicCircuit.count,
        count_wUnloadLevelBlocks145_t v L d B (by omega), count_wUnloadBlockFrom145_t]

theorem count_wUncompTreeLevels145_toff {Var : Type} {n : ℕ} (v : Var)
    (L : Phase2Bal161Layout n) :
    ∀ (R : ℕ) (hR : R ≤ 5), (wUncompTreeLevels145 v L R hR).count .TOFF = 0
  | 0, _ => rfl
  | R + 1, hR => by
      have hf := count_wFoldLevelBlocks145 L ⟨R, hR⟩ .TOFF (fun _ _ _ ↦ rfl) _ le_rfl
      simp [wUncompTreeLevels145, DynamicCircuit.count, hf, count_wUnloadLevelBlocks145_toff,
        count_wUncompTreeLevels145_toff v L R (by omega)]

theorem count_wUncompTreeLevels145_t {Var : Type} {n : ℕ} (v : Var)
    (L : Phase2Bal161Layout n) :
    ∀ (R : ℕ) (hR : R ≤ 5), (wUncompTreeLevels145 v L R hR).count .T = 0
  | 0, _ => rfl
  | R + 1, hR => by
      have hf := count_wFoldLevelBlocks145 L ⟨R, hR⟩ .T (fun _ _ _ ↦ rfl) _ le_rfl
      simp [wUncompTreeLevels145, DynamicCircuit.count, hf, count_wUnloadLevelBlocks145_t,
        count_wUncompTreeLevels145_t v L R (by omega)]

@[simp] theorem count_dDec145Dyn_toff {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    (dDec145Dyn v L).count .TOFF = 0 := by
  have hcz : ∀ (x y : Wire n) (h : x ≠ y), (SelectSwapQROM.czCircuit x y h).count .TOFF = 0 :=
    fun _ _ _ ↦ rfl
  simp [dDec145Dyn, wRoot6UninitLinCirc145, DynamicCircuit.count, count_wUncompTreeLevels145_toff,
    XMeasCircuit.xMeasUnloadWireDyn, hcz]

@[simp] theorem count_dDec145Dyn_t {Var : Type} {n : ℕ} (v : Var) (L : Phase2Bal161Layout n) :
    (dDec145Dyn v L).count .T = 0 := by
  have hcz : ∀ (x y : Wire n) (h : x ≠ y), (SelectSwapQROM.czCircuit x y h).count .T = 0 :=
    fun _ _ _ ↦ rfl
  simp [dDec145Dyn, wRoot6UninitLinCirc145, DynamicCircuit.count, count_wUncompTreeLevels145_t,
    XMeasCircuit.xMeasUnloadWireDyn, hcz]

theorem loE145_mod_lt_cap {n : ℕ} (L : Phase2Bal161Layout n) (β : BitAssignment n) (k : ℕ) :
    loE145 L β % k < leafCap145 (b0E145 L β) :=
  lt_of_le_of_lt (Nat.mod_le _ _) (loE145_lt_cap_all L β)

/-- Decoded one-hot leaf bit assignment at barrel-unload stage `R`. -/
noncomputable def wDecAssign145 {n : ℕ} (L : Phase2Bal161Layout n) (R : ℕ)
    (β : BitAssignment n) : BitAssignment n :=
  Function.update β (wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ R)
    (loE145_mod_lt_cap L β (2 ^ R))) 1

/-- Base one-hot bit assignment prior to folding stage `d` during W-tree unload. -/
noncomputable def γBase145 {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (β : BitAssignment n) : BitAssignment n :=
  wDecAssign145 L d.val β

theorem pHi145_lt_cap {n : ℕ} {L : Phase2Bal161Layout n} {d : Fin 5}
    {β : BitAssignment n} (hb : (b0E145 L β).val < levelBlocks145 d) :
    loE145 L β % 2 ^ d.val + 2 ^ d.val < leafCap145 (b0E145 L β) := by
  have := Nat.mod_lt (loE145 L β) (Nat.two_pow_pos d.val)
  have := two_mul_pow_le_cap145 hb
  omega

/-- Folded one-hot bit assignment at barrel-unload stage `d`. -/
noncomputable def γFold145 {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (β : BitAssignment n) : BitAssignment n :=
  if hb : (b0E145 L β).val < levelBlocks145 d then
    Function.update (γBase145 L d β)
      (wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val + 2 ^ d.val) (pHi145_lt_cap hb))
      (β (L.rSelPair8 ⟨d.val, by omega⟩))
  else γBase145 L d β

theorem lo_mod_succ_cases145 (d : Fin 5) {lo : ℕ} (hlo : lo < 32) :
    (lo / 2 ^ d.val % 2 = 0 ∧ lo % 2 ^ (d.val + 1) = lo % 2 ^ d.val) ∨
    (lo / 2 ^ d.val % 2 = 1 ∧ lo % 2 ^ (d.val + 1) = lo % 2 ^ d.val + 2 ^ d.val) := by
  have hdec : ∀ (d' : Fin 5) (l : Fin 32),
      (l.val / 2 ^ d'.val % 2 = 0 ∧ l.val % 2 ^ (d'.val + 1) = l.val % 2 ^ d'.val) ∨
      (l.val / 2 ^ d'.val % 2 = 1 ∧ l.val % 2 ^ (d'.val + 1) = l.val % 2 ^ d'.val + 2 ^ d'.val) :=
    by decide
  exact hdec d ⟨lo, hlo⟩

theorem wFoldBlockFrom145_ket {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (b : Fin 6) (hb : b.val < levelBlocks145 d) {β : BitAssignment n} (hS : sValid145 L β) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val),
      (wFoldBlockFrom145 L d b hb m hm).eval.1.mulVec
          (XMeasCircuit.ket (wDecAssign145 L (d.val + 1) β)) =
        if b = b0E145 L β ∧ loE145 L β % 2 ^ d.val < m then
          XMeasCircuit.ket (γFold145 L d β)
        else XMeasCircuit.ket (wDecAssign145 L (d.val + 1) β) := by
  intro m hm
  have hlo32 : loE145 L β < 32 := by
    have hlo := loE145_lt_cap hS; dsimp [leafCap145] at hlo; split_ifs at hlo <;> omega
  induction m with
  | zero =>
      simp only [wFoldBlockFrom145, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec, Nat.not_lt_zero, and_false, ↓reduceIte]
  | succ m ih =>
      have hmHiCap : m + 2 ^ d.val < leafCap145 b := by
        have := two_mul_pow_le_cap145 hb; omega
      have hmLoCap : m < leafCap145 b := by omega
      have hloMod0 := loE145_mod_lt_cap L β (2 ^ d.val)
      have hloMod1 := loE145_mod_lt_cap L β (2 ^ (d.val + 1))
      rw [wFoldBlockFrom145, StepEncK.eval_seq_mulVec, ih (by omega)]
      by_cases hprev : b = b0E145 L β ∧ loE145 L β % 2 ^ d.val < m
      · have hb0 : (b0E145 L β).val < levelBlocks145 d := hprev.1 ▸ hb
        rw [ite_posE hprev, ite_posE ⟨hprev.1, by omega⟩, StepEncK.ket_CNOT]
        have hne1 : wLeaf145 L b (m + 2 ^ d.val) hmHiCap ≠
            wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val + 2 ^ d.val) (pHi145_lt_cap hb0) :=
          fun h ↦ by have hp := (wLeaf145_inj L h).2; omega
        have hne2 : wLeaf145 L b (m + 2 ^ d.val) hmHiCap ≠
            wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val) hloMod0 :=
          fun h ↦ by
            have hp := (wLeaf145_inj L h).2
            have := Nat.mod_lt (loE145 L β) (Nat.two_pow_pos d.val); omega
        have hsrc0 : γFold145 L d β (wLeaf145 L b (m + 2 ^ d.val) hmHiCap) = 0 := by
          dsimp only [γFold145, γBase145, wDecAssign145]
          rw [dite_eq_left hb0, Function.update_of_ne hne1, Function.update_of_ne hne2]
          exact oh145_zero_of_sValid hS _
        rw [hsrc0, add_zero, Function.update_eq_self]
      · rw [ite_negE hprev, StepEncK.ket_CNOT]
        by_cases hcur : b = b0E145 L β ∧ loE145 L β % 2 ^ d.val = m
        · obtain ⟨rfl, hpm⟩ := hcur
          let b := b0E145 L β
          have hx144 : (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val < 144 := by
            by_contra hge
            have hb5 : (b0E145 L β).val = 5 := congrArg Fin.val (b0E145_of_not_lt144 hge)
            dsimp [levelBlocks145] at hb; rw [hb5] at hb; split_ifs at hb <;> omega
          have hbit : β (L.rSelPair8 ⟨d.val, by omega⟩) =
              if loE145 L β / 2 ^ d.val % 2 = 1 then 1 else 0 := by
            have hxbit : (UnsignedGivens.localIdx L.rSelPair8 β).val / 2 ^ d.val % 2 =
                ((UnsignedGivens.localIdx L.rSelPair8 β).val % 32) / 2 ^ d.val % 2 := by
              fin_cases d <;> (dsimp; omega)
            rw [selPair8_bit_eq_145 L β _, hxbit, loE145_of_lt144 hx144]
          rw [ite_posE ⟨rfl, by omega⟩]
          rcases lo_mod_succ_cases145 d hlo32 with ⟨h0, hpEq⟩ | ⟨h1, hpEq⟩
          · have hneSrc : wLeaf145 L b (m + 2 ^ d.val) hmHiCap ≠
                wLeaf145 L b (loE145 L β % 2 ^ (d.val + 1)) hloMod1 := fun h ↦ by
              have hp := (wLeaf145_inj L h).2; omega
            have hsrc0 : wDecAssign145 L (d.val + 1) β (wLeaf145 L b (m + 2 ^ d.val) hmHiCap) =
                0 := by
              dsimp [wDecAssign145]; rw [Function.update_of_ne hneSrc]
              exact oh145_zero_of_sValid hS _
            rw [hsrc0, add_zero, Function.update_eq_self]
            congr 1; funext w
            dsimp only [γFold145, γBase145, wDecAssign145]
            rw [dite_eq_left hb, hbit, ite_negE (by omega)]
            by_cases hw : w = wLeaf145 L b (loE145 L β % 2 ^ d.val + 2 ^ d.val) (pHi145_lt_cap hb)
            · subst hw
              have hneHi : wLeaf145 L b (loE145 L β % 2 ^ d.val + 2 ^ d.val) (pHi145_lt_cap hb) ≠
                  wLeaf145 L b (loE145 L β % 2 ^ (d.val + 1)) hloMod1 := fun h ↦ by
                have hp := (wLeaf145_inj L h).2; have := Nat.two_pow_pos d.val; omega
              rw [Function.update_self, Function.update_of_ne hneHi]
              exact oh145_zero_of_sValid hS _
            · rw [Function.update_of_ne hw]; simp_rw [hpEq]
          · have hwSrc : wLeaf145 L b (m + 2 ^ d.val) hmHiCap =
                wLeaf145 L b (loE145 L β % 2 ^ (d.val + 1)) hloMod1 := by simp_rw [hpEq, hpm]
            have hwDst : wLeaf145 L b m hmLoCap =
                wLeaf145 L b (loE145 L β % 2 ^ d.val) hloMod0 := by simp_rw [hpm]
            have hneDstSrc : wLeaf145 L b (loE145 L β % 2 ^ d.val) hloMod0 ≠
                wLeaf145 L b (loE145 L β % 2 ^ (d.val + 1)) hloMod1 := fun h ↦ by
              have hp := (wLeaf145_inj L h).2; have := Nat.two_pow_pos d.val; omega
            dsimp only [wDecAssign145]
            rw [hwSrc, hwDst, Function.update_self, Function.update_of_ne hneDstSrc,
              oh145_zero_of_sValid hS _, zero_add]
            congr 1; funext w
            dsimp only [γFold145, γBase145, wDecAssign145]
            rw [dite_eq_left hb, hbit, ite_posE h1]
            by_cases hw1 : w = wLeaf145 L b (loE145 L β % 2 ^ d.val) hloMod0
            · subst hw1; rw [Function.update_self, Function.update_of_ne (by
                intro h; have hp := (wLeaf145_inj L h).2; have := Nat.two_pow_pos d.val; omega),
                Function.update_self]
            · rw [Function.update_of_ne hw1]
              by_cases hw2 : w = wLeaf145 L b (loE145 L β % 2 ^ d.val + 2 ^ d.val)
                  (pHi145_lt_cap hb)
              · subst hw2; dsimp only [b]
                rw [wLeaf145_congr L _ _ _ hpEq, Function.update_self, Function.update_self]
                exact pHi145_lt_cap hb
              · rw [Function.update_of_ne hw2, Function.update_of_ne hw1]
                exact Function.update_of_ne (by simp_rw [hpEq]; exact hw2) _ _
        · have hnNext : ¬ (b = b0E145 L β ∧ loE145 L β % 2 ^ d.val < m + 1) := fun ⟨hbEq, hlt⟩ ↦
            by_cases (fun heq : loE145 L β % 2 ^ d.val = m ↦ hcur ⟨hbEq, heq⟩)
              (fun hne ↦ hprev ⟨hbEq, by omega⟩)
          rw [ite_negE hnNext]
          have hneSrc : wLeaf145 L b (m + 2 ^ d.val) hmHiCap ≠
              wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ (d.val + 1)) hloMod1 := fun h ↦ by
            obtain ⟨rfl, hp⟩ := wLeaf145_inj L h
            rcases lo_mod_succ_cases145 d hlo32 with ⟨_, hpEq⟩ | ⟨_, hpEq⟩
            · have := Nat.mod_lt (loE145 L β) (Nat.two_pow_pos d.val); omega
            · exact hcur ⟨rfl, by omega⟩
          have hsrc0 :
              wDecAssign145 L (d.val + 1) β (wLeaf145 L b (m + 2 ^ d.val) hmHiCap) = 0 := by
            dsimp [wDecAssign145]; rw [Function.update_of_ne hneSrc]
            exact oh145_zero_of_sValid hS _
          rw [hsrc0, add_zero, Function.update_eq_self]

theorem wFoldLevelBlocks145_ket {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    {β : BitAssignment n} (hS : sValid145 L β) :
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 d),
      (wFoldLevelBlocks145 L d B hB).eval.1.mulVec
          (XMeasCircuit.ket (wDecAssign145 L (d.val + 1) β)) =
        if (b0E145 L β).val < B then XMeasCircuit.ket (γFold145 L d β)
        else XMeasCircuit.ket (wDecAssign145 L (d.val + 1) β) := by
  intro B hB
  induction B with
  | zero =>
      simp only [wFoldLevelBlocks145, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec, Nat.not_lt_zero, ↓reduceIte]
  | succ B ih =>
      have hlt6 : B < 6 := by dsimp [levelBlocks145] at hB; split_ifs at hB <;> omega
      rw [wFoldLevelBlocks145, StepEncK.eval_seq_mulVec, ih (by omega)]
      by_cases hlt : (b0E145 L β).val < B
      · have hb0 : (b0E145 L β).val < levelBlocks145 d := lt_of_lt_of_le (by omega) hB
        have hne : (⟨B, hlt6⟩ : Fin 6) ≠ b0E145 L β := fun h ↦ by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        rw [ite_posE hlt, ite_posE (by omega)]
        have hfix : ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val),
            (wFoldBlockFrom145 L d ⟨B, hlt6⟩ (by dsimp; omega) m hm).eval.1.mulVec
                (XMeasCircuit.ket (γFold145 L d β)) =
              XMeasCircuit.ket (γFold145 L d β) := by
          intro m hm; induction m with
          | zero =>
              simp only [wFoldBlockFrom145, Circuit.eval_identity, Submonoid.coe_one,
                Matrix.one_mulVec]
          | succ m ihm =>
              have hmHiCap : m + 2 ^ d.val < leafCap145 ⟨B, hlt6⟩ := by
                have := two_mul_pow_le_cap145 (by dsimp; omega : (⟨B, hlt6⟩ : Fin 6).val <
                  levelBlocks145 d)
                omega
              rw [wFoldBlockFrom145, StepEncK.eval_seq_mulVec, ihm (by omega),
                StepEncK.ket_CNOT]
              have hne1 : wLeaf145 L ⟨B, hlt6⟩ (m + 2 ^ d.val) hmHiCap ≠
                  wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val + 2 ^ d.val)
                    (pHi145_lt_cap hb0) := fun h ↦ hne (wLeaf145_inj L h).1
              have hne2 : wLeaf145 L ⟨B, hlt6⟩ (m + 2 ^ d.val) hmHiCap ≠
                  wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val)
                    (loE145_mod_lt_cap L β (2 ^ d.val)) :=
                fun h ↦ hne (wLeaf145_inj L h).1
              have hsrc0 : γFold145 L d β (wLeaf145 L ⟨B, hlt6⟩ (m + 2 ^ d.val) hmHiCap) = 0 := by
                dsimp only [γFold145, γBase145, wDecAssign145]
                rw [dite_eq_left hb0, Function.update_of_ne hne1, Function.update_of_ne hne2]
                exact oh145_zero_of_sValid hS _
              rw [hsrc0, add_zero, Function.update_eq_self]
        exact hfix (2 ^ d.val) le_rfl
      · rw [ite_negE hlt, wFoldBlockFrom145_ket L d ⟨B, hlt6⟩ _ hS (2 ^ d.val) le_rfl]
        by_cases heq : (b0E145 L β).val = B
        · have hbEq : (⟨B, hlt6⟩ : Fin 6) = b0E145 L β := Fin.ext heq.symm
          have hcurLt : loE145 L β % 2 ^ d.val < 2 ^ d.val := Nat.mod_lt _ (Nat.two_pow_pos _)
          rw [ite_posE ⟨hbEq, hcurLt⟩, ite_posE (by omega)]
        · have hne : (⟨B, hlt6⟩ : Fin 6) ≠ b0E145 L β := fun h ↦ heq (congrArg Fin.val h).symm
          rw [ite_negE (fun h ↦ hne h.1), ite_negE (by omega)]

/-- Partially unloaded bit assignment after blocks `< B` and leaves `< m` at stage `d`. -/
noncomputable def γUnload145 {n : ℕ} (L : Phase2Bal161Layout n) (d : Fin 5)
    (B m : ℕ) (β : BitAssignment n) : BitAssignment n :=
  if (b0E145 L β).val < B ∨ ((b0E145 L β).val = B ∧ loE145 L β % 2 ^ d.val < m) then
    γBase145 L d β
  else γFold145 L d β

theorem cleanFinset_singleton_ketMapOp145 {n : ℕ} (q : Wire n)
    (S : BitAssignment n → Prop) (g : BitAssignment n → BitAssignment n)
    (hg : ∀ β, S β → g β q = 0) :
    XMeasCircuit.cleanFinsetProj {q} * ketMapOp S (fun β ↦ XMeasCircuit.ket (g β)) =
      ketMapOp S (fun β ↦ XMeasCircuit.ket (g β)) := by
  have himg : (QRegister.singleton q).image = {q} := by ext w; simp
  rw [← himg, ← XMeasCircuit.basisOutcomeProjector_zero_eq_cleanFinsetProj, mul_ketMapOp]
  refine ketMapOp_congr fun β hS ↦ ?_
  rw [XMeasCircuit.ket_projector_zero, ite_posE (hg β hS)]

theorem wUnloadBlockFrom145_step {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (L : Phase2Bal161Layout n) (d : Fin 5) (b : Fin 6) (hb : b.val < levelBlocks145 d) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val),
      SubspaceStepU (Var := Var)
        (ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γUnload145 L d b.val 0 β)))
        (ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γUnload145 L d b.val m β)))
        (wUnloadBlockFrom145 v L d b hb m hm)
  | 0, _ => SubspaceStepU.of_circuit (Var := Var) Circuit.identity
      (by rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul])
  | m + 1, hm => by
      have hcap := two_mul_pow_le_cap145 hb
      let q := wLeaf145 L b (m + 2 ^ d.val) (by omega)
      let wLo := wLeaf145 L b m (by omega)
      let wBit := L.rSelPair8 ⟨d.val, by omega⟩
      let f : BitAssignment n → ZMod 2 := fun γ ↦ γ wLo * γ wBit
      have hqLo : wLo ≠ q := fun h ↦ by
        have hp := (wLeaf145_inj L h).2; have := Nat.two_pow_pos d.val; omega
      have hqBit : wBit ≠ q := (oh145_ne_pair L _ _).symm
      have hf : ∀ γ val, f (Function.update γ q val) = f γ := fun γ val ↦ by
        dsimp only [f]; rw [Function.update_of_ne hqLo, Function.update_of_ne hqBit]
      have hClean : XMeasCircuit.cleanFinsetProj {q} *
          ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γUnload145 L d b.val (m + 1) β)) =
          ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γUnload145 L d b.val (m + 1) β)) :=
        cleanFinset_singleton_ketMapOp145 q (sValid145 L) _ fun β hS ↦ by
          have hneCur : q ≠ wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val)
              (loE145_mod_lt_cap L β (2 ^ d.val)) := fun h ↦ by
            have hp := (wLeaf145_inj L h).2
            have := Nat.mod_lt (loE145 L β) (Nat.two_pow_pos d.val); omega
          dsimp only [γUnload145, γFold145, γBase145, wDecAssign145]
          split_ifs with hc hb0
          · rw [Function.update_of_ne hneCur]; exact oh145_zero_of_sValid hS _
          · have hneHi : q ≠ wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val + 2 ^ d.val)
                (pHi145_lt_cap hb0) := fun h ↦ by
              obtain ⟨hbEq, hp⟩ := wLeaf145_inj L h
              exact hc (Or.inr ⟨congrArg Fin.val hbEq.symm, by omega⟩)
            rw [Function.update_of_ne hneHi, Function.update_of_ne hneCur]
            exact oh145_zero_of_sValid hS _
          · rw [Function.update_of_ne hneCur]; exact oh145_zero_of_sValid hS _
      have hXor : (XMeasCircuit.xorWireUnitary q f hf).1 *
          ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γUnload145 L d b.val (m + 1) β)) =
          ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γUnload145 L d b.val m β)) := by
        rw [mul_ketMapOp]; refine ketMapOp_congr fun β hS ↦ ?_
        rw [XMeasCircuit.xorWireUnitary_mulVec_ket]; congr 1
        by_cases hhit : (b0E145 L β).val = b.val ∧ loE145 L β % 2 ^ d.val = m
        · obtain ⟨hbv, hpm⟩ := hhit
          have hbEq : b0E145 L β = b := Fin.ext hbv
          have hb0 : (b0E145 L β).val < levelBlocks145 d := hbv.symm ▸ hb
          have hqEq : q = wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val + 2 ^ d.val)
              (pHi145_lt_cap hb0) := by dsimp [q]; simp_rw [hbEq, hpm]
          have hwLoEq : wLo = wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val)
              (loE145_mod_lt_cap L β (2 ^ d.val)) := by
            dsimp [wLo]; simp_rw [hbEq, hpm]
          have h1 : γUnload145 L d b.val (m + 1) β = γBase145 L d β :=
            ite_posE (Or.inr ⟨hbv, by omega⟩)
          have h0 : γUnload145 L d b.val m β = γFold145 L d β := ite_negE (by omega)
          have hwLo1 : γBase145 L d β wLo = 1 := by
            dsimp [γBase145, wDecAssign145]; rw [hwLoEq, Function.update_self]
          have hwBit1 : γBase145 L d β wBit = β wBit :=
            Function.update_of_ne (oh145_ne_pair L _ _).symm _ _
          have hq0 : γBase145 L d β q = 0 := by
            dsimp [γBase145, wDecAssign145]; rw [← hwLoEq, Function.update_of_ne hqLo.symm]
            exact oh145_zero_of_sValid hS _
          rw [h1, h0]; dsimp only [f, γFold145]
          rw [dite_eq_left hb0, hq0, hwLo1, hwBit1, zero_add, one_mul, hqEq]
        · have heqUnl : γUnload145 L d b.val (m + 1) β = γUnload145 L d b.val m β := by
            dsimp only [γUnload145]
            have hiff : ((b0E145 L β).val < b.val ∨
                ((b0E145 L β).val = b.val ∧ loE145 L β % 2 ^ d.val < m + 1)) ↔
              ((b0E145 L β).val < b.val ∨
                ((b0E145 L β).val = b.val ∧ loE145 L β % 2 ^ d.val < m)) := by omega
            by_cases hc : (b0E145 L β).val < b.val ∨
                ((b0E145 L β).val = b.val ∧ loE145 L β % 2 ^ d.val < m)
            · rw [ite_posE (hiff.mpr hc), ite_posE hc]
            · rw [ite_negE (mt hiff.mp hc), ite_negE hc]
          have hwLo0 : γUnload145 L d b.val m β wLo = 0 := by
            have hneCur : wLo ≠ wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val)
                (loE145_mod_lt_cap L β (2 ^ d.val)) := fun h ↦ by
              obtain ⟨hbEq, hp⟩ := wLeaf145_inj L h
              exact hhit ⟨congrArg Fin.val hbEq.symm, hp.symm⟩
            dsimp only [γUnload145, γFold145, γBase145, wDecAssign145]
            split_ifs with _ hb0
            · rw [Function.update_of_ne hneCur]; exact oh145_zero_of_sValid hS _
            · have hneHi : wLo ≠ wLeaf145 L (b0E145 L β) (loE145 L β % 2 ^ d.val + 2 ^ d.val)
                  (pHi145_lt_cap hb0) := fun h ↦ by
                have hp := (wLeaf145_inj L h).2; omega
              rw [Function.update_of_ne hneHi, Function.update_of_ne hneCur]
              exact oh145_zero_of_sValid hS _
            · rw [Function.update_of_ne hneCur]; exact oh145_zero_of_sValid hS _
          rw [heqUnl]; dsimp only [f]; rw [hwLo0, zero_mul, add_zero, Function.update_eq_self]
      exact SubspaceStepU.seq (wUnloadBlockFrom145_step v L d b hb m (by omega))
        (SubspaceStepU.congr hXor rfl
          (SubspaceStepU.xMeasUnload_circuit v q f hf _
            (StepEncK.czCircuit_eval_eq_phaseFlip wLo wBit _) hClean))

theorem wUnloadLevelBlocks145_step {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (L : Phase2Bal161Layout n) (d : Fin 5) :
    ∀ (B : ℕ) (hB : B ≤ levelBlocks145 d),
      SubspaceStepU (Var := Var)
        (ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γFold145 L d β)))
        (ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γUnload145 L d B 0 β)))
        (wUnloadLevelBlocks145 v L d B hB)
  | 0, _ => SubspaceStepU.of_circuit (Var := Var) Circuit.identity (by
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul]
      exact ketMapOp_congr fun β _ ↦ congrArg XMeasCircuit.ket (ite_negE (by omega)).symm)
  | B + 1, hB => by
      have hlt6 : B < 6 := by dsimp [levelBlocks145] at hB; split_ifs at hB <;> omega
      have hEnd :
          ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γUnload145 L d B (2 ^ d.val) β)) =
          ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γUnload145 L d (B + 1) 0 β)) := by
        refine ketMapOp_congr fun β _ ↦ congrArg XMeasCircuit.ket ?_
        have hcurLt : loE145 L β % 2 ^ d.val < 2 ^ d.val := Nat.mod_lt _ (Nat.two_pow_pos _)
        have hiff : ((b0E145 L β).val < B ∨
            ((b0E145 L β).val = B ∧ loE145 L β % 2 ^ d.val < 2 ^ d.val)) ↔
          ((b0E145 L β).val < B + 1 ∨
            ((b0E145 L β).val = B + 1 ∧ loE145 L β % 2 ^ d.val < 0)) := by omega
        dsimp only [γUnload145]
        by_cases hc : (b0E145 L β).val < B + 1 ∨
            ((b0E145 L β).val = B + 1 ∧ loE145 L β % 2 ^ d.val < 0)
        · rw [ite_posE (hiff.mpr hc), ite_posE hc]
        · rw [ite_negE (mt hiff.mp hc), ite_negE hc]
      exact SubspaceStepU.seq (wUnloadLevelBlocks145_step v L d B (by omega))
        (SubspaceStepU.congr rfl hEnd
          (wUnloadBlockFrom145_step v L d ⟨B, hlt6⟩ (by dsimp; omega) (2 ^ d.val) le_rfl))

theorem wUncompTreeLevels145_step {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (L : Phase2Bal161Layout n) :
    ∀ (R : ℕ) (hR : R ≤ 5),
      SubspaceStepU (Var := Var)
        (ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (wDecAssign145 L R β)))
        (ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (wDecAssign145 L 0 β)))
        (wUncompTreeLevels145 v L R hR)
  | 0, _ => SubspaceStepU.of_circuit (Var := Var) Circuit.identity
      (by rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul])
  | R + 1, hR => by
      let d : Fin 5 := ⟨R, hR⟩
      have hFold : (wFoldLevelBlocks145 L d (levelBlocks145 d) le_rfl).eval.1 *
          ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (wDecAssign145 L (R + 1) β)) =
          ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (γFold145 L d β)) := by
        rw [mul_ketMapOp]; refine ketMapOp_congr fun β hS ↦ ?_
        rw [wFoldLevelBlocks145_ket L d hS (levelBlocks145 d) le_rfl]
        by_cases hb : (b0E145 L β).val < levelBlocks145 d
        · exact ite_posE hb
        · rw [ite_negE hb]; congr 1
          have hloLt : loE145 L β < 2 ^ d.val := by
            have hlo := loE145_lt_cap hS
            have hb6 := (b0E145 L β).isLt
            by_cases hd4 : d.val < 4
            · simp only [levelBlocks145, hd4, ↓reduceIte] at hb
              have hbEq5 : (b0E145 L β).val = 5 := by omega
              simp only [leafCap145, hbEq5, show ¬ (5 < 4) by omega, show ¬ (5 = 4) by omega,
                ↓reduceIte] at hlo
              have := Nat.two_pow_pos d.val; omega
            · have hdEq4 : d.val = 4 := by have := d.isLt; omega
              simp only [levelBlocks145, hd4, ↓reduceIte] at hb
              dsimp [leafCap145] at hlo; rw [hdEq4]; split_ifs at hlo <;> omega
          have hm1 : loE145 L β % 2 ^ (d.val + 1) = loE145 L β :=
            Nat.mod_eq_of_lt (lt_of_lt_of_le hloLt (Nat.pow_le_pow_right (by omega) (by omega)))
          have hm0 : loE145 L β % 2 ^ d.val = loE145 L β := Nat.mod_eq_of_lt hloLt
          dsimp only [γFold145, γBase145, wDecAssign145]
          rw [dite_eq_right hb]; simp_rw [hm1, hm0]
      have hUnl : ketMapOp (sValid145 L)
            (fun β ↦ XMeasCircuit.ket (γUnload145 L d (levelBlocks145 d) 0 β)) =
          ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (wDecAssign145 L R β)) := by
        refine ketMapOp_congr fun β _ ↦ congrArg XMeasCircuit.ket ?_
        dsimp only [γUnload145, γFold145, γBase145]
        by_cases hb : (b0E145 L β).val < levelBlocks145 d
        · exact ite_posE (Or.inl hb)
        · rw [ite_negE (by omega), dite_eq_right hb]
      exact SubspaceStepU.seq
        (SubspaceStepU.seq
          (SubspaceStepU.of_circuit (Var := Var) _ hFold)
          (SubspaceStepU.congr rfl hUnl (wUnloadLevelBlocks145_step v L d _ le_rfl)))
        (wUncompTreeLevels145_step v L R (by omega))

theorem dDec145Dyn_step {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (L : Phase2Bal161Layout n) :
    SubspaceStepU (Var := Var)
      (ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (encAssign145 L β)))
      (Lac2Fused184Select.ketPredProj (sValid145 L))
      (dDec145Dyn v L) := by
  let w3 := wLeaf145 L 3 0 (leafCap145_pos 3)
  let w5 := wLeaf145 L 5 0 (leafCap145_pos 5)
  have hStart : ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (wDecAssign145 L 5 β)) =
      ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (encAssign145 L β)) := by
    refine ketMapOp_congr fun β hS ↦ ?_
    have hlo := loE145_lt_cap hS
    have hm5 : loE145 L β % 2 ^ 5 = loE145 L β :=
      Nat.mod_eq_of_lt (by dsimp [leafCap145] at hlo; split_ifs at hlo <;> omega)
    dsimp only [wDecAssign145, encAssign145]; simp_rw [hm5]
  let f5 : BitAssignment n → ZMod 2 := fun γ ↦ γ (L.rSelPair8 7) * γ (L.rSelPair8 4)
  let f3 : BitAssignment n → ZMod 2 := fun γ ↦ γ (L.rSelPair8 5) * γ (L.rSelPair8 6)
  have hf5 : ∀ γ val, f5 (Function.update γ w5 val) = f5 γ := fun γ val ↦ by
    dsimp only [f5]
    rw [Function.update_of_ne (pair_ne_wRoot0 L 7 5), Function.update_of_ne (pair_ne_wRoot0 L 4 5)]
  have hf3 : ∀ γ val, f3 (Function.update γ w3 val) = f3 γ := fun γ val ↦ by
    dsimp only [f3]
    rw [Function.update_of_ne (pair_ne_wRoot0 L 5 3), Function.update_of_ne (pair_ne_wRoot0 L 6 3)]
  let R₃ := ketMapOp (sValid145 L) (fun β ↦
    XMeasCircuit.ket (Function.update β w3 (β (L.rSelPair8 5) * β (L.rSelPair8 6))))
  have hClean5 : XMeasCircuit.cleanFinsetProj {w5} * R₃ = R₃ :=
    cleanFinset_singleton_ketMapOp145 w5 (sValid145 L) _ fun β hS ↦ by
      rw [Function.update_of_ne (wRoot0_ne L (by decide : (5 : Fin 6) ≠ 3))]
      exact oh145_zero_of_sValid hS _
  have hClean3 : XMeasCircuit.cleanFinsetProj {w3} * ketMapOp (sValid145 L) XMeasCircuit.ket =
      ketMapOp (sValid145 L) XMeasCircuit.ket :=
    cleanFinset_singleton_ketMapOp145 w3 (sValid145 L) id fun _ hS ↦ oh145_zero_of_sValid hS _
  have hUninit : (wRoot6UninitLinCirc145 L).eval.1 *
      ketMapOp (sValid145 L) (fun β ↦ XMeasCircuit.ket (wDecAssign145 L 0 β)) =
      (XMeasCircuit.xorWireUnitary w5 f5 hf5).1 * R₃ := by
    dsimp only [R₃]; rw [mul_ketMapOp, mul_ketMapOp]
    refine ketMapOp_congr fun β hS ↦ ?_
    have hd0 : wDecAssign145 L 0 β =
        Function.update β (wLeaf145 L (b0E145 L β) 0 (leafCap145_pos _)) 1 := by
      dsimp only [wDecAssign145]; simp only [_root_.pow_zero, Nat.mod_one]
    have hw50 : Function.update β w3 (β (L.rSelPair8 5) * β (L.rSelPair8 6)) w5 = 0 := by
      rw [Function.update_of_ne (wRoot0_ne L (by decide : (5 : Fin 6) ≠ 3))]
      exact oh145_zero_of_sValid hS _
    have hp7 : Function.update β w3 (β (L.rSelPair8 5) * β (L.rSelPair8 6)) (L.rSelPair8 7) =
        β (L.rSelPair8 7) := Function.update_of_ne (pair_ne_wRoot0 L 7 3) _ _
    have hp4 : Function.update β w3 (β (L.rSelPair8 5) * β (L.rSelPair8 6)) (L.rSelPair8 4) =
        β (L.rSelPair8 4) := Function.update_of_ne (pair_ne_wRoot0 L 4 3) _ _
    rw [hd0, wRoot6UninitLinCirc145_ket L hS, XMeasCircuit.xorWireUnitary_mulVec_ket, hw50,
      zero_add]
    dsimp only [f5]; rw [hp7, hp4]
  have hXoMain : R₃ = (XMeasCircuit.xorWireUnitary w3 f3 hf3).1 *
      ketMapOp (sValid145 L) XMeasCircuit.ket := by
    dsimp only [R₃]; rw [mul_ketMapOp]
    refine ketMapOp_congr fun β hS ↦ ?_
    rw [XMeasCircuit.xorWireUnitary_mulVec_ket, oh145_zero_of_sValid hS _, zero_add]
  exact SubspaceStepU.congr hStart (ketMapOp_eq_ketPredProj _)
    (SubspaceStepU.seq (wUncompTreeLevels145_step v L 5 le_rfl)
      (SubspaceStepU.seq (SubspaceStepU.of_circuit (Var := Var) _ hUninit)
        (SubspaceStepU.seq
          (SubspaceStepU.xMeasUnload_circuit v w5 f5 hf5 _
            (StepEncK.czCircuit_eval_eq_phaseFlip _ _ _) hClean5)
          (SubspaceStepU.congr hXoMain.symm rfl
            (SubspaceStepU.xMeasUnload_circuit v w3 f3 hf3 _
              (StepEncK.czCircuit_eval_eq_phaseFlip _ _ _) hClean3)))))

/-- Wrapper around the `8 × 145` active-index fanout circuit on `Phase2Bal161Layout`. -/
noncomputable def cFan145 {n : ℕ} (L : Phase2Bal161Layout n) : Circuit n :=
  Lac2Fused184Select.fanoutActIdxCircuit 8 145 L.wOne L.rSelPair8 L.rOneHot145
    (fun g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i)

theorem ket_cFan145 {n : ℕ} (L : Phase2Bal161Layout n) (β : BitAssignment n) :
    (cFan145 L).eval.1.mulVec (OneHotSimulates.ket β) =
      OneHotSimulates.ket (Lac2Fused184Select.fanoutActIdxAssign 8 145 L.wOne L.rSelPair8
        L.rOneHot145 β) :=
  Lac2Fused184Select.ket_fanoutActIdxCircuit 8 145 L.wOne L.rSelPair8 L.rOneHot145
    (fun g ↦ oh145_ne_rest L g 0) (fun i g ↦ oh145_ne_pair L g i)
    (fun i ↦ rest14_ne_pair L 0 i) β

theorem cFan145_eval_mul_self {n : ℕ} (L : Phase2Bal161Layout n) :
    (cFan145 L).eval.1 * (cFan145 L).eval.1 = 1 := by
  refine OneHotSimulates.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ket_cFan145]
  obtain ⟨γ, hγ⟩ : ∃ γ,
      Lac2Fused184Select.fanoutActIdxAssign 8 145 L.wOne L.rSelPair8 L.rOneHot145 β = γ :=
    ⟨_, rfl⟩
  rw [hγ, ket_cFan145]
  refine congrArg OneHotSimulates.ket ?_
  have hohNot : ∀ g : Fin 145, L.rOneHot145 g ∉ Set.range L.rSelPair8.wires :=
    fun g ⟨i, hi⟩ ↦ oh145_ne_pair L g i hi.symm
  have hactNot : L.wOne ∉ Set.range L.rSelPair8.wires :=
    fun ⟨i, hi⟩ ↦ rest14_ne_pair L 0 i hi.symm
  have hγOh : ∀ g : Fin 145, γ (L.rOneHot145 g) = β (L.rOneHot145 g) := fun g ↦ by
    rw [← hγ]; dsimp only [Lac2Fused184Select.fanoutActIdxAssign]
    rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ (hohNot g),
      Function.update_of_ne (oh145_ne_rest L g 0)]
  funext w
  by_cases hwIdx : w ∈ Set.range L.rSelPair8.wires
  · obtain ⟨i, rfl⟩ := hwIdx
    dsimp only [Lac2Fused184Select.fanoutActIdxAssign]
    rw [OneHotSimulates.writeReg_apply_reg]
    simp_rw [hγOh]
    rw [← hγ]; dsimp only [Lac2Fused184Select.fanoutActIdxAssign]
    rw [OneHotSimulates.writeReg_apply_reg, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · dsimp only [Lac2Fused184Select.fanoutActIdxAssign]
    rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ hwIdx]
    by_cases hwAct : w = L.wOne
    · subst hwAct; rw [Function.update_self]
      simp_rw [hγOh]
      rw [← hγ]; dsimp only [Lac2Fused184Select.fanoutActIdxAssign]
      rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ hactNot, Function.update_self,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [Function.update_of_ne hwAct, ← hγ]
      dsimp only [Lac2Fused184Select.fanoutActIdxAssign]
      rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ hwIdx, Function.update_of_ne hwAct]

attribute [irreducible] cFan145

theorem rCtrlTail146_act {n : ℕ} (L : Phase2Bal161Layout n) :
    L.rCtrlTail146 actIdx146 = L.wAct := by
  dsimp only [Phase2Bal161Layout.rCtrlTail146, actIdx146]
  rw [QRegister.concat_apply_left, QRegister.singleton_apply]

theorem rCtrlTail146_sub {n : ℕ} (L : Phase2Bal161Layout n) :
    L.rCtrlTail146 subIdx146 = L.wSub := by
  dsimp only [Phase2Bal161Layout.rCtrlTail146, subIdx146]
  rw [QRegister.concat_apply_right, QRegister.concat_apply_left, QRegister.singleton_apply]

theorem encAssign145_update_wOne_eq {n : ℕ} (L : Phase2Bal161Layout n) {β : BitAssignment n}
    (hS : sValid145 L β) :
    Function.update (encAssign145 L β) L.wOne 1 =
      OneHotMux.oneHotActiveAssign 8 145 h145Ge1 L.wOne L.rSelPair8 L.rOneHot145
        (Function.update β L.wOne 1) := by
  let β₁ := Function.update β L.wOne 1
  have hpEq : (fun i ↦ β₁ (L.rSelPair8 i)) = (fun i ↦ β (L.rSelPair8 i)) :=
    funext fun i ↦ Function.update_of_ne (rest14_ne_pair L 0 i).symm _ _
  have hbtn : OneHotSimulates.bitsToNat (fun i ↦ β (L.rSelPair8 i)) =
      (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val :=
    (OneHotSimulates.bitsToNat_reg_eq_extractIndex_val L.rSelPair8 β).trans
      (by simp [CircuitModular.UnsignedGivens.localIdx, QRegister.extractIndex])
  let j₀ := OneHotMux.oneHotDecodeIdx 8 145 h145Ge1 (fun i ↦ β₁ (L.rSelPair8 i))
  have hjVal : j₀.val = (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val := by
    dsimp only [j₀]; rw [hpEq]
    exact (OneHotMux.oneHotDecodeIdx_val_of_lt 8 145 h145Ge1 _ (hbtn.symm ▸ hS.1)).trans hbtn
  have hwLeafEq : wLeaf145 L (b0E145 L β) (loE145 L β) (loE145_lt_cap_all L β) =
      L.rOneHot145 j₀ :=
    congrArg L.rOneHot145 (Fin.ext (by
      dsimp [leafIdx145]; rw [leafBase_add_loE145 hS, hjVal]))
  funext w
  by_cases hw1 : w = L.wOne
  · subst hw1
    have hnotOh : L.wOne ∉ Set.range L.rOneHot145.wires := fun ⟨g, hg⟩ ↦ oh145_ne_rest L g 0 hg
    rw [Function.update_self, OneHotMux.oneHotActiveAssign,
      CircuitModular.UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hnotOh]
    exact (Function.update_self L.wOne 1 β).symm
  · rw [Function.update_of_ne hw1]
    by_cases hwOh : w ∈ Set.range L.rOneHot145.wires
    · obtain ⟨g, rfl⟩ := hwOh
      rw [OneHotMux.oneHotActiveAssign, CircuitModular.UnsignedGivens.writeReg_apply_reg]
      have hone1 : β₁ L.wOne = 1 := Function.update_self _ _ _
      change encAssign145 L β (L.rOneHot145 g) = if g = j₀ then β₁ L.wOne else 0
      dsimp only [encAssign145]; rw [hwLeafEq, hone1]
      by_cases hg : g = j₀
      · subst hg; simp
      · rw [ite_negE hg, Function.update_of_ne (L.rOneHot145.wires.injective.ne hg)]
        exact oh145_zero_of_sValid hS g
    · rw [OneHotMux.oneHotActiveAssign, UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwOh]
      have hneL : w ≠ wLeaf145 L (b0E145 L β) (loE145 L β) (loE145_lt_cap_all L β) :=
        fun h ↦ hwOh ⟨_, h.symm⟩
      dsimp only [encAssign145, β₁]
      rw [Function.update_of_ne hneL, Function.update_of_ne hw1]

theorem fanout_enc_sCascValid145 {n : ℕ} (L : Phase2Bal161Layout n) {β : BitAssignment n}
    (hS : sValid145 L β) :
    let βAct := Function.update (encAssign145 L β) L.wOne 1
    let β₂ := Lac2Fused184Select.fanoutActIdxAssign 8 145 L.wOne L.rSelPair8 L.rOneHot145 βAct
    (∃ g₀ : Fin 145,
      CircuitModular.UnsignedGivens.IsOneHotBits g₀
        (Fin.cases (β₂ L.wHot0) (fun g ↦ β₂ (L.rCtrlTail146 (selHot144 g))))) ∧
    ∀ idx : Fin (8 + 14), β₂ (L.rGivens22 idx) = 0 := by
  intro βAct β₂
  let g₀ : Fin 145 := ⟨(CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val, hS.1⟩
  have hwLeafEq : wLeaf145 L (b0E145 L β) (loE145 L β) (loE145_lt_cap_all L β) =
      L.rOneHot145 g₀ :=
    congrArg L.rOneHot145 (Fin.ext (by dsimp [leafIdx145, g₀]; exact leafBase_add_loE145 hS))
  have hohNotPair (g : Fin 145) : L.rOneHot145 g ∉ Set.range L.rSelPair8.wires :=
    fun ⟨i, hi⟩ ↦ oh145_ne_pair L g i hi.symm
  have honeNotPair : L.wOne ∉ Set.range L.rSelPair8.wires :=
    fun ⟨i, hi⟩ ↦ rest14_ne_pair L 0 i hi.symm
  have hrestNotPair (j : Fin 14) : L.rGivRest14 j ∉ Set.range L.rSelPair8.wires :=
    fun ⟨i, hi⟩ ↦ rest14_ne_pair L j i hi.symm
  have hβActOh (g : Fin 145) : βAct (L.rOneHot145 g) = if g = g₀ then 1 else 0 := by
    dsimp only [βAct, encAssign145]
    rw [Function.update_of_ne (oh145_ne_rest L g 0), hwLeafEq]
    by_cases hg : g = g₀
    · subst hg; simp
    · rw [ite_negE hg, Function.update_of_ne (L.rOneHot145.wires.injective.ne hg)]
      exact oh145_zero_of_sValid hS g
  have hβ₂Oh (g : Fin 145) : β₂ (L.rOneHot145 g) = if g = g₀ then 1 else 0 := by
    dsimp only [β₂, Lac2Fused184Select.fanoutActIdxAssign]
    rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ (hohNotPair g),
      Function.update_of_ne (oh145_ne_rest L g 0), hβActOh g]
  refine ⟨⟨g₀, ?_⟩, ?_⟩
  · have hfn : (Fin.cases (β₂ L.wHot0) (fun g ↦ β₂ (L.rCtrlTail146 (selHot144 g))) :
        Fin 145 → ZMod 2) = fun g ↦ if g = g₀ then 1 else 0 := by
      funext k; cases k using Fin.cases with
      | zero => exact hβ₂Oh 0
      | succ g => rw [Fin.cases_succ, rCtrlTail146_hot L g, hβ₂Oh g.succ]
    rw [hfn]; exact ⟨by simp, fun k hk ↦ by simp [hk]⟩
  · have hβ₂One : β₂ L.wOne = 0 := by
      dsimp only [β₂, Lac2Fused184Select.fanoutActIdxAssign]
      rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ honeNotPair, Function.update_self]
      have hone1 : βAct L.wOne = 1 := Function.update_self _ _ _
      simp_rw [hβActOh]
      rw [hone1, Finset.sum_ite_eq' Finset.univ g₀, ite_posE (Finset.mem_univ g₀),
        CharTwo.add_self_eq_zero]
    have hβ₂Rest (j : Fin 14) : β₂ (L.rGivRest14 j) = 0 := by
      by_cases hj0 : j = 0
      · subst hj0; exact hβ₂One
      · have hneOne : L.rGivRest14 j ≠ L.wOne := fun h ↦ hj0 (L.rGivRest14.wires.injective h)
        dsimp only [β₂, Lac2Fused184Select.fanoutActIdxAssign, βAct, encAssign145]
        rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ (hrestNotPair j),
          Function.update_of_ne hneOne, Function.update_of_ne hneOne,
          hwLeafEq, Function.update_of_ne (oh145_ne_rest L g₀ j).symm]
        exact rest14_zero_of_sValid hS j
    have hβ₂Pair (i : Fin 8) : β₂ (L.rSelPair8 i) = 0 := by
      dsimp only [β₂, Lac2Fused184Select.fanoutActIdxAssign]
      rw [OneHotSimulates.writeReg_apply_reg]
      have hpEq : βAct (L.rSelPair8 i) = β (L.rSelPair8 i) := by
        dsimp only [βAct, encAssign145]
        rw [Function.update_of_ne (rest14_ne_pair L 0 i).symm,
          Function.update_of_ne (oh145_ne_pair L _ i).symm]
      have hite (g : Fin 145) :
          (if decide (g.val / 2 ^ i.val % 2 = 1) then βAct (L.rOneHot145 g) else 0) =
            if g = g₀ then (if g₀.val / 2 ^ i.val % 2 = 1 then (1 : ZMod 2) else 0) else 0 := by
        rw [hβActOh g]
        by_cases hg : g = g₀
        · rw [hg, ite_posE rfl, ite_posE rfl]
          by_cases hb : g₀.val / 2 ^ i.val % 2 = 1 <;> simp [hb]
        · rw [ite_negE hg, ite_negE hg, ite_self]
      simp_rw [hite]
      rw [hpEq, Finset.sum_ite_eq' Finset.univ g₀, ite_posE (Finset.mem_univ g₀),
        ← selPair8_bit_eq_145 L β i, CharTwo.add_self_eq_zero]
    intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · dsimp [Phase2Bal161Layout.rGivens22]; rw [QRegister.concat_apply_left]; exact hβ₂Pair i
    · dsimp [Phase2Bal161Layout.rGivens22]; rw [QRegister.concat_apply_right]; exact hβ₂Rest j

theorem localIdx_tail146_fanout {n : ℕ} (L : Phase2Bal161Layout n) {β : BitAssignment n}
    (hS : sValid145 L β) :
    let βAct := Function.update (encAssign145 L β) L.wOne 1
    let β₂ := Lac2Fused184Select.fanoutActIdxAssign 8 145 L.wOne L.rSelPair8 L.rOneHot145 βAct
    CircuitModular.UnsignedGivens.localIdx L.rCtrlTail146 β₂ =
      ctrl10ToTail146Idx (CircuitModular.UnsignedGivens.localIdx L.rCtrl10 β) := by
  intro βAct β₂
  have hactEq := encAssign145_update_wOne_eq L hS
  let β₁ := Function.update β L.wOne 1
  let βA := OneHotMux.oneHotActiveAssign 8 145 h145Ge1 L.wOne L.rSelPair8 L.rOneHot145 β₁
  have hβ₂Eq : β₂ = Lac2Fused184Select.fanoutActIdxAssign 8 145
      L.wOne L.rSelPair8 L.rOneHot145 βA := by dsimp only [β₂, βAct]; rw [hactEq]
  have hone1 : β₁ L.wOne = 1 := Function.update_self _ _ _
  have hp1 : (fun i ↦ β₁ (L.rSelPair8 i)) = (fun i ↦ β (L.rSelPair8 i)) :=
    funext fun i ↦ Function.update_of_ne (rest14_ne_pair L 0 i).symm _ _
  have htailNeOne (k : Fin (1 + (1 + 144))) : L.rCtrlTail146 k ≠ L.wOne := by
    obtain ⟨kf, hkf, hkb⟩ := L.rCtrlTail146_in_rFull k
    dsimp [Phase2Bal161Layout.wOne]; rw [hkf, L.rGivRest14_eq]
    exact L.rFull_ne (by dsimp; omega)
  have htailNotPair (k : Fin (1 + (1 + 144))) :
      L.rCtrlTail146 k ∉ Set.range L.rSelPair8.wires := by
    rintro ⟨i, hi⟩; obtain ⟨kf, hkf, hkb⟩ := L.rCtrlTail146_in_rFull k
    rw [L.rSelPair8_eq, hkf] at hi; exact L.rFull_ne (by dsimp; omega) hi
  refine congrArg (basisBits (1 + (1 + 144))).symm (funext fun k ↦ ?_)
  have hfanK : β₂ (L.rCtrlTail146 k) = βA (L.rCtrlTail146 k) := by
    rw [hβ₂Eq]; dsimp only [Lac2Fused184Select.fanoutActIdxAssign]
    rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ (htailNotPair k),
      Function.update_of_ne (htailNeOne k)]
  rw [hfanK]
  refine Fin.addCases (fun i0 ↦ ?_) (Fin.addCases (fun i1 ↦ ?_) (fun g ↦ ?_)) k
  · rw [Fin.eq_zero i0]; dsimp only [ctrl10ToTail146Bits]
    rw [Fin.addCases_left, show Fin.castAdd (1 + 144) (0 : Fin 1) = actIdx146 from rfl,
      rCtrlTail146_act L]
    have hnotOh : L.wAct ∉ Set.range L.rOneHot145.wires := fun ⟨g, hg⟩ ↦ oh145_ne_wAct L g hg
    have hne1 : L.wAct ≠ L.wOne := by
      dsimp [Phase2Bal161Layout.wAct, Phase2Bal161Layout.wOne]
      rw [L.rCtrl10_eq, L.rGivRest14_eq]
      exact L.rFull_ne (by dsimp [Lac2Fused184Select.actIdx10]; omega)
    dsimp only [βA, OneHotMux.oneHotActiveAssign, β₁]
    rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hnotOh, Function.update_of_ne hne1]
    exact (congrFun (CircuitModular.UnsignedGivens.basisBits_symm_eq (fun l ↦ β (L.rCtrl10 l)))
      Lac2Fused184Select.actIdx10).symm
  · rw [Fin.eq_zero i1]; dsimp only [ctrl10ToTail146Bits]
    rw [Fin.addCases_right, Fin.addCases_left,
      show Fin.natAdd 1 (Fin.castAdd 144 (0 : Fin 1)) = subIdx146 from rfl, rCtrlTail146_sub L]
    have hnotOh : L.wSub ∉ Set.range L.rOneHot145.wires := by
      rintro ⟨g, hg⟩; dsimp [Phase2Bal161Layout.wSub] at hg
      rw [L.rOneHot145_eq, L.rCtrl10_eq] at hg
      exact L.rFull_ne (by dsimp [Lac2Fused184Select.subIdx10]; omega) hg
    have hne1 : L.wSub ≠ L.wOne := by
      dsimp [Phase2Bal161Layout.wSub, Phase2Bal161Layout.wOne]
      rw [L.rCtrl10_eq, L.rGivRest14_eq]
      exact L.rFull_ne (by dsimp [Lac2Fused184Select.subIdx10]; omega)
    dsimp only [βA, OneHotMux.oneHotActiveAssign, β₁]
    rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hnotOh, Function.update_of_ne hne1]
    exact (congrFun (CircuitModular.UnsignedGivens.basisBits_symm_eq (fun l ↦ β (L.rCtrl10 l)))
      Lac2Fused184Select.subIdx10).symm
  · dsimp only [ctrl10ToTail146Bits]
    rw [Fin.addCases_right, Fin.addCases_right,
      show Fin.natAdd 1 (Fin.natAdd 1 g) = selHot144 g from rfl, rCtrlTail146_hot L g]
    dsimp only [βA, OneHotMux.oneHotActiveAssign]
    rw [CircuitModular.UnsignedGivens.writeReg_apply_reg, hone1, hp1]
    have hp : (fun i ↦ basisBits 10 (CircuitModular.UnsignedGivens.localIdx L.rCtrl10 β)
        (Lac2Fused184Select.selPair10 i)) = (fun i ↦ β (L.rSelPair8 i)) :=
      funext fun i ↦ congrFun (UnsignedGivens.basisBits_symm_eq (fun l ↦ β (L.rCtrl10 l)))
        (Lac2Fused184Select.selPair10 i)
    rw [hp]

/-- `0-T`, `0-TOFF` CNOT fan-in from `L.rOneHot145` into `L.wAct` according to `actFlipMask`. -/
def flipAct145Circuit {n : ℕ} (actFlipMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) : Circuit n :=
  CircuitModular.UnsignedGivens.cnotMaskReg 145 L.rOneHot145 L.wAct actFlipMask (oh145_ne_wAct L)

@[simp] theorem count_flipAct145Circuit_toff {n : ℕ} (actFlipMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) : (flipAct145Circuit actFlipMask L).count .TOFF = 0 := by
  simp [flipAct145Circuit, CircuitModular.UnsignedGivens.count_cnotMaskReg_toff]

@[simp] theorem count_flipAct145Circuit_t {n : ℕ} (actFlipMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) : (flipAct145Circuit actFlipMask L).count .T = 0 := by
  simp [flipAct145Circuit, CircuitModular.UnsignedGivens.count_cnotMaskReg_t]

theorem act145_ne_wPh {n : ℕ} (L : Phase2Bal161Layout n) : L.wAct ≠ L.wPh := by
  dsimp [Phase2Bal161Layout.wAct, Phase2Bal161Layout.wPh]
  rw [L.rCtrl10_eq, L.rGivRest14_eq]
  exact L.rFull_ne (by dsimp [Lac2Fused184Select.actIdx10]; omega)

/-- `0-T`, `0-TOFF` `wAct`-controlled negative-sign phase kick on `Phase2Bal161Layout`. -/
def zMaskAct145Circuit {n : ℕ} (negMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) : Circuit n :=
  UnsignedGivens.cnotMaskReg 145 L.rOneHot145 L.wPh negMask (fun g ↦ oh145_ne_rest L g 1) ;;ᶜ
    CircuitModular.UnsignedGivens.czCircuit L.wAct L.wPh (act145_ne_wPh L) ;;ᶜ
    UnsignedGivens.cnotMaskReg 145 L.rOneHot145 L.wPh negMask (fun g ↦ oh145_ne_rest L g 1)

@[simp] theorem count_zMaskAct145Circuit_toff {n : ℕ} (negMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) : (zMaskAct145Circuit negMask L).count .TOFF = 0 := by
  simp [zMaskAct145Circuit]

@[simp] theorem count_zMaskAct145Circuit_t {n : ℕ} (negMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) : (zMaskAct145Circuit negMask L).count .T = 0 := by
  simp [zMaskAct145Circuit]

theorem ket_zMaskAct145Circuit {n : ℕ} (negMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) (β : BitAssignment n) :
    (zMaskAct145Circuit negMask L).eval.1.mulVec (OneHotSimulates.ket β) =
      ((-1 : ℂ) ^
        (β L.wAct * (β L.wPh + UnsignedGivens.maskSumBit L.rOneHot145 negMask β)).val) •
        OneHotSimulates.ket β := by
  have hketM : ∀ γ : BitAssignment n, OneHotSimulates.ket γ = UnsignedGivens.ket γ := fun _ ↦ rfl
  let s := CircuitModular.UnsignedGivens.maskSumBit L.rOneHot145 negMask β
  let β₁ := Function.update β L.wPh (β L.wPh + s)
  have hs₁ : CircuitModular.UnsignedGivens.maskSumBit L.rOneHot145 negMask β₁ = s := by
    dsimp only [CircuitModular.UnsignedGivens.maskSumBit, s, β₁]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [Function.update_of_ne (oh145_ne_rest L g 1)]
  have hact₁ : β₁ L.wAct = β L.wAct := Function.update_of_ne (act145_ne_wPh L) _ _
  have hph₁ : β₁ L.wPh = β L.wPh + s := Function.update_self _ _ _
  rw [hketM β, zMaskAct145Circuit, CircuitModular.UnsignedGivens.eval_seq_mulVec,
    UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_cnotMaskReg_ket,
    CircuitModular.UnsignedGivens.evolve_czCircuit_ket, Matrix.mulVec_smul,
    CircuitModular.UnsignedGivens.evolve_cnotMaskReg_ket]
  change ((-1 : ℂ) ^ (β₁ L.wAct * β₁ L.wPh).val) •
      CircuitModular.UnsignedGivens.ket (Function.update β₁ L.wPh
        (β₁ L.wPh + CircuitModular.UnsignedGivens.maskSumBit L.rOneHot145 negMask β₁)) = _
  have hfn : Function.update β₁ L.wPh (β L.wPh + s + s) = β := by
    funext w; by_cases hw : w = L.wPh
    · subst hw; simp [β₁, add_assoc, CircuitModular.UnsignedGivens.zmod2_add_self]
    · dsimp only [β₁]; rw [Function.update_of_ne hw, Function.update_of_ne hw]
  rw [hact₁, hph₁, hs₁, hfn, ← hketM]

/-- Basis assignment after toggling `L.wAct` by `actFlipMask(pair8)`. -/
noncomputable def flipAct145Assign {n : ℕ} (actFlipMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) (β : BitAssignment n) : BitAssignment n :=
  let j₀ := OneHotMux.oneHotDecodeIdx 8 145 h145Ge1 (fun i ↦ β (L.rSelPair8 i))
  Function.update β L.wAct (β L.wAct + if actFlipMask j₀ then 1 else 0)

theorem act145_ne_inner {n : ℕ} (L : Phase2Bal161Layout n) (idx : Fin 159) :
    L.wAct ≠ L.rInner159 idx := by
  dsimp [Phase2Bal161Layout.wAct]; rw [L.rCtrl10_eq, L.rInner159_eq]
  exact L.rFull_ne (by dsimp [Lac2Fused184Select.actIdx10]; omega)

theorem sValid145_flipAct145Assign {n : ℕ} (actFlipMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) (β : BitAssignment n) :
    sValid145 L (flipAct145Assign actFlipMask L β) ↔ sValid145 L β := by
  have hp : CircuitModular.UnsignedGivens.localIdx L.rSelPair8 (flipAct145Assign actFlipMask L β) =
      CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β :=
    localIdx_congr L.rSelPair8 fun i ↦ Function.update_of_ne (act145_ne_pair L i).symm _ _
  have hi (idx : Fin 159) :
      flipAct145Assign actFlipMask L β (L.rInner159 idx) = β (L.rInner159 idx) :=
    Function.update_of_ne (act145_ne_inner L idx).symm _ _
  dsimp only [sValid145]; simp only [hp, hi]

theorem flipAct145Assign_involutive {n : ℕ} (actFlipMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) (β : BitAssignment n) :
    flipAct145Assign actFlipMask L (flipAct145Assign actFlipMask L β) = β := by
  dsimp only [flipAct145Assign]
  have hp : (fun i ↦ Function.update β L.wAct
      (β L.wAct + if actFlipMask (OneHotMux.oneHotDecodeIdx 8 145 h145Ge1
        (fun i ↦ β (L.rSelPair8 i))) then 1 else 0) (L.rSelPair8 i)) =
      (fun i ↦ β (L.rSelPair8 i)) :=
    funext fun i ↦ Function.update_of_ne (act145_ne_pair L i).symm _ _
  rw [hp, Function.update_self, Function.update_idem, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]
  exact Function.update_eq_self L.wAct β

theorem localIdx_ctrl10_flipAct145Assign {n : ℕ} (actFlipMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) (β : BitAssignment n) :
    CircuitModular.UnsignedGivens.localIdx L.rCtrl10 (flipAct145Assign actFlipMask L β) =
      flipActCtrl10_145 actFlipMask (CircuitModular.UnsignedGivens.localIdx L.rCtrl10 β) := by
  let c10 := CircuitModular.UnsignedGivens.localIdx L.rCtrl10 β
  have hp : (fun i ↦ basisBits 10 c10 (Lac2Fused184Select.selPair10 i)) =
      (fun i ↦ β (L.rSelPair8 i)) :=
    funext fun i ↦ congrFun (UnsignedGivens.basisBits_symm_eq (fun l ↦ β (L.rCtrl10 l)))
      (Lac2Fused184Select.selPair10 i)
  dsimp only [flipActCtrl10_145]
  change (basisBits 10).symm _ = _
  congr 1; rw [hp]; funext l
  have hbl : basisBits 10 c10 l = β (L.rCtrl10 l) :=
    congrFun (CircuitModular.UnsignedGivens.basisBits_symm_eq (fun k ↦ β (L.rCtrl10 k))) l
  by_cases hl : l = Lac2Fused184Select.actIdx10
  · subst hl
    change flipAct145Assign actFlipMask L β L.wAct = _
    dsimp only [flipAct145Assign]
    rw [Function.update_self, Function.update_self, hbl]; rfl
  · have hne : L.rCtrl10 l ≠ L.wAct := L.rCtrl10.wires.injective.ne hl
    dsimp only [flipAct145Assign]
    rw [Function.update_of_ne hne, Function.update_of_ne hl, hbl]

theorem flipAct145Circuit_enc_ket {n : ℕ} (actFlipMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) {β : BitAssignment n} (hS : sValid145 L β) :
    (flipAct145Circuit actFlipMask L).eval.1.mulVec (XMeasCircuit.ket (encAssign145 L β)) =
      XMeasCircuit.ket (encAssign145 L (flipAct145Assign actFlipMask L β)) := by
  rw [flipAct145Circuit, ket_cnotMaskReg]; congr 1
  have hp : CircuitModular.UnsignedGivens.localIdx L.rSelPair8 (flipAct145Assign actFlipMask L β) =
      CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β :=
    localIdx_congr L.rSelPair8 fun i ↦ Function.update_of_ne (act145_ne_pair L i).symm _ _
  have hb0 : b0E145 L (flipAct145Assign actFlipMask L β) = b0E145 L β := b0E145_congr L hp
  have hlo : loE145 L (flipAct145Assign actFlipMask L β) = loE145 L β := loE145_congr L hp
  let j₀ := OneHotMux.oneHotDecodeIdx 8 145 h145Ge1 (fun i ↦ β (L.rSelPair8 i))
  have hbtn : OneHotSimulates.bitsToNat (fun i ↦ β (L.rSelPair8 i)) =
      (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val :=
    (OneHotSimulates.bitsToNat_reg_eq_extractIndex_val L.rSelPair8 β).trans
      (by simp [CircuitModular.UnsignedGivens.localIdx, QRegister.extractIndex])
  have hjVal : j₀.val = (CircuitModular.UnsignedGivens.localIdx L.rSelPair8 β).val :=
    (OneHotMux.oneHotDecodeIdx_val_of_lt 8 145 h145Ge1 _ (hbtn.symm ▸ hS.1)).trans hbtn
  have hwLeafEq : wLeaf145 L (b0E145 L β) (loE145 L β) (loE145_lt_cap_all L β) =
      L.rOneHot145 j₀ :=
    congrArg L.rOneHot145 (Fin.ext (by
      dsimp [leafIdx145]; rw [leafBase_add_loE145 hS, hjVal]))
  have hsum : (∑ i : Fin 145, if actFlipMask i then encAssign145 L β (L.rOneHot145 i) else 0) =
      if actFlipMask j₀ then 1 else 0 := by
    have hite (g : Fin 145) :
        (if actFlipMask g then encAssign145 L β (L.rOneHot145 g) else 0) =
          if g = j₀ then (if actFlipMask j₀ then (1 : ZMod 2) else 0) else 0 := by
      dsimp only [encAssign145]; rw [hwLeafEq]
      by_cases hg : g = j₀
      · subst hg; simp
      · rw [ite_negE hg, Function.update_of_ne (L.rOneHot145.wires.injective.ne hg),
          oh145_zero_of_sValid hS g, ite_self]
    simp_rw [hite]; rw [Finset.sum_ite_eq' Finset.univ j₀, ite_posE (Finset.mem_univ j₀)]
  have hencAct : encAssign145 L β L.wAct = β L.wAct :=
    Function.update_of_ne (oh145_ne_wAct L _).symm _ _
  dsimp only [CircuitModular.UnsignedGivens.maskSumBit]
  rw [hsum, hencAct]
  have hwLeafF : wLeaf145 L (b0E145 L (flipAct145Assign actFlipMask L β))
      (loE145 L (flipAct145Assign actFlipMask L β))
      (loE145_lt_cap_all L (flipAct145Assign actFlipMask L β)) = L.rOneHot145 j₀ := by
    rw [← hwLeafEq]; simp_rw [hb0, hlo]
  dsimp only [encAssign145]
  rw [hwLeafF, hwLeafEq]
  exact Function.update_comm (oh145_ne_wAct L _) 1 _ β

theorem zMask145_enc_ket {n : ℕ} (negMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) {β : BitAssignment n} (hS : sValid145 L β) :
    let βAct := Function.update (encAssign145 L β) L.wOne 1
    (zMaskAct145Circuit negMask L).eval.1.mulVec (OneHotSimulates.ket βAct) =
      (if ctrl10RawPhase145 negMask (CircuitModular.UnsignedGivens.localIdx L.rCtrl10 β) then
          (-1 : ℂ) else 1) • OneHotSimulates.ket βAct := by
  intro βAct; dsimp only [βAct]
  rw [encAssign145_update_wOne_eq L hS, ket_zMaskAct145Circuit]
  let β₁ := Function.update β L.wOne 1
  let βA := OneHotMux.oneHotActiveAssign 8 145 h145Ge1 L.wOne L.rSelPair8 L.rOneHot145 β₁
  let j₀ := OneHotMux.oneHotDecodeIdx 8 145 h145Ge1 (fun i ↦ β₁ (L.rSelPair8 i))
  refine congrArg (· • OneHotSimulates.ket βA) ?_
  have hact1 : β₁ L.wAct = β L.wAct := Function.update_of_ne (by
    dsimp [Phase2Bal161Layout.wAct, Phase2Bal161Layout.wOne]
    rw [L.rCtrl10_eq, L.rGivRest14_eq]
    exact L.rFull_ne (by dsimp [Lac2Fused184Select.actIdx10]; omega)) _ _
  have hactEq : βA L.wAct = β L.wAct :=
    (CircuitModular.UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _
      (fun ⟨g, hg⟩ ↦ oh145_ne_wAct L g hg)).trans hact1
  have hph0 : βA L.wPh = 0 := by
    have hne : L.wPh ≠ L.wOne := L.rGivRest14.wires.injective.ne (by decide)
    exact (CircuitModular.UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _
      (fun ⟨g, hg⟩ ↦ oh145_ne_rest L g 1 hg)).trans
      ((Function.update_of_ne hne _ _).trans (rest14_zero_of_sValid hS 1))
  have hone1 : β₁ L.wOne = 1 := Function.update_self _ _ _
  have hmask : CircuitModular.UnsignedGivens.maskSumBit L.rOneHot145 negMask βA =
      if negMask j₀ then 1 else 0 := by
    dsimp only [CircuitModular.UnsignedGivens.maskSumBit]
    have hite (g : Fin 145) :
        (if negMask g then βA (L.rOneHot145 g) else 0) =
          if g = j₀ then (if negMask j₀ then (1 : ZMod 2) else 0) else 0 := by
      have hoh : βA (L.rOneHot145 g) = if g = j₀ then 1 else 0 := by
        simpa only [βA, OneHotMux.oneHotActiveAssign, hone1] using
          CircuitModular.UnsignedGivens.writeReg_apply_reg β₁ L.rOneHot145
            (fun k ↦ if k = j₀ then β₁ L.wOne else 0) g
      rw [hoh]; by_cases hg : g = j₀ <;> simp [hg]
    simp_rw [hite]; rw [Finset.sum_ite_eq' Finset.univ j₀, ite_posE (Finset.mem_univ j₀)]
  have hp1 : (fun i ↦ β₁ (L.rSelPair8 i)) = (fun i ↦ β (L.rSelPair8 i)) :=
    funext fun i ↦ Function.update_of_ne (rest14_ne_pair L 0 i).symm _ _
  have haDec : decide (basisBits 10 (CircuitModular.UnsignedGivens.localIdx L.rCtrl10 β)
      Lac2Fused184Select.actIdx10 = 1) = decide (β L.wAct = 1) :=
    congrArg (fun x ↦ decide (x = 1))
      (congrFun (CircuitModular.UnsignedGivens.basisBits_symm_eq (fun l ↦ β (L.rCtrl10 l)))
        Lac2Fused184Select.actIdx10)
  have hp : (fun i ↦ basisBits 10 (CircuitModular.UnsignedGivens.localIdx L.rCtrl10 β)
      (Lac2Fused184Select.selPair10 i)) = (fun i ↦ β₁ (L.rSelPair8 i)) :=
    (funext fun i ↦ congrFun (UnsignedGivens.basisBits_symm_eq (fun l ↦ β (L.rCtrl10 l)))
      (Lac2Fused184Select.selPair10 i)).trans hp1.symm
  change (-1 : ℂ) ^ (βA L.wAct *
      (βA L.wPh + CircuitModular.UnsignedGivens.maskSumBit L.rOneHot145 negMask βA)).val = _
  unfold ctrl10RawPhase145
  rw [hactEq, hph0, zero_add, hmask, haDec, hp]
  cases negMask j₀
  · simp
  · rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β L.wAct) with ha | ha <;> simp [ha]

theorem rSC145_not_mem {n : ℕ} (L : Phase2Bal161Layout n) :
    let rSC := L.rSpin.concat L.rCat11 (OneHotMux.disj_sys_cat_of L.hsc L.hac)
    (∀ l : Fin 10, L.rCtrl10 l ∉ Set.range rSC.wires) ∧
    (∀ idx : Fin 159, L.rInner159 idx ∉ Set.range rSC.wires) ∧
    (∀ j : Fin 14, L.rGivRest14 j ∉ Set.range rSC.wires) ∧
    (∀ g : Fin 145, L.rOneHot145 g ∉ Set.range rSC.wires) := by
  intro rSC
  have h1 (l : Fin 10) : L.rCtrl10 l ∉ Set.range rSC.wires :=
    fun ⟨sc, hsc⟩ ↦ QRegister.disjoint_iff.mp (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac) sc l hsc
  have h2 (idx : Fin 159) : L.rInner159 idx ∉ Set.range rSC.wires := by
    rintro ⟨sc, hsc⟩; revert hsc
    refine Fin.addCases (fun i hsc ↦ ?_) (fun j hsc ↦ ?_) sc
    · dsimp [rSC] at hsc; rw [QRegister.concat_apply_left, L.rSpin_eq, L.rInner159_eq] at hsc
      exact L.rFull_ne (by dsimp; omega) hsc
    · dsimp [rSC] at hsc; rw [QRegister.concat_apply_right, L.rCat11_eq, L.rInner159_eq] at hsc
      exact L.rFull_ne (by dsimp; omega) hsc
  exact ⟨h1, h2,
    fun j ↦ by dsimp only [Phase2Bal161Layout.rGivRest14]; rw [QRegister.compose_apply]; exact h2 _,
    fun g ↦ by
      dsimp only [Phase2Bal161Layout.rOneHot145]; rw [QRegister.compose_apply]; exact h2 _⟩

theorem writeReg_fanout145_comm {n : ℕ} (actFlipMask : Fin 145 → Bool)
    (L : Phase2Bal161Layout n) (β : BitAssignment n) (l : Fin (2 ^ (58 + 11))) :
    let rSC := L.rSpin.concat L.rCat11 (OneHotMux.disj_sys_cat_of L.hsc L.hac)
    let βF (γ : BitAssignment n) := flipAct145Assign actFlipMask L γ
    let β₂ (γ : BitAssignment n) :=
      Lac2Fused184Select.fanoutActIdxAssign 8 145 L.wOne L.rSelPair8 L.rOneHot145
        (Function.update (encAssign145 L (βF γ)) L.wOne 1)
    let γL := CircuitModular.UnsignedGivens.writeReg β rSC (basisBits (58 + 11) l)
    UnsignedGivens.localIdx rSC (β₂ β) = UnsignedGivens.localIdx rSC β ∧
    CircuitModular.UnsignedGivens.writeReg (β₂ β) rSC (basisBits (58 + 11) l) = β₂ γL := by
  intro rSC βF β₂ γL
  obtain ⟨hnotC, hnotI, hnotR, hnotO⟩ := rSC145_not_mem L
  have hLocSC : UnsignedGivens.localIdx rSC (β₂ β) = UnsignedGivens.localIdx rSC β :=
    localIdx_congr rSC fun sc ↦ by
      have hnp : rSC sc ∉ Set.range L.rSelPair8.wires :=
        fun ⟨i, hi⟩ ↦ hnotC (Lac2Fused184Select.selPair10 i) ⟨sc, hi.symm⟩
      have hno : rSC sc ≠ L.wOne := fun h ↦ hnotR 0 ⟨sc, h⟩
      have hnl : rSC sc ≠ wLeaf145 L (b0E145 L (βF β)) (loE145 L (βF β))
          (loE145_lt_cap_all L (βF β)) :=
        fun h ↦ hnotO _ ⟨sc, h⟩
      have hna : rSC sc ≠ L.wAct := fun h ↦ hnotC Lac2Fused184Select.actIdx10 ⟨sc, h⟩
      dsimp only [β₂, Lac2Fused184Select.fanoutActIdxAssign, encAssign145]
      rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ hnp, Function.update_of_ne hno,
        Function.update_of_ne hno, Function.update_of_ne hnl]
      dsimp only [βF, flipAct145Assign]; rw [Function.update_of_ne hna]
  refine ⟨hLocSC, ?_⟩
  have hpγ (i : Fin 8) : γL (L.rSelPair8 i) = β (L.rSelPair8 i) :=
    UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hnotC (Lac2Fused184Select.selPair10 i))
  have hflWr : UnsignedGivens.writeReg (βF β) rSC (basisBits (58 + 11) l) = βF γL := by
    dsimp only [βF, flipAct145Assign]
    have hpEq : (fun i ↦ γL (L.rSelPair8 i)) = (fun i ↦ β (L.rSelPair8 i)) := funext hpγ
    have hactγ : γL L.wAct = β L.wAct :=
      UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hnotC Lac2Fused184Select.actIdx10)
    rw [hpEq, hactγ]; funext w
    by_cases hwSC : w ∈ Set.range rSC.wires
    · obtain ⟨sc, rfl⟩ := hwSC
      have hna : rSC sc ≠ L.wAct := fun h ↦ hnotC Lac2Fused184Select.actIdx10 ⟨sc, h⟩
      rw [CircuitModular.UnsignedGivens.writeReg_apply_reg, Function.update_of_ne hna]
      exact (CircuitModular.UnsignedGivens.writeReg_apply_reg _ _ _ sc).symm
    · rw [CircuitModular.UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwSC]
      by_cases hwa : w = L.wAct
      · subst hwa; simp
      · rw [Function.update_of_ne hwa, Function.update_of_ne hwa]
        exact (CircuitModular.UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwSC).symm
  have hpFγ (i : Fin 8) : (βF γL) (L.rSelPair8 i) = (βF β) (L.rSelPair8 i) := by
    dsimp only [βF, flipAct145Assign]
    rw [Function.update_of_ne (act145_ne_pair L i).symm,
      Function.update_of_ne (act145_ne_pair L i).symm, hpγ i]
  have hlocEq : CircuitModular.UnsignedGivens.localIdx L.rSelPair8 (βF γL) =
      CircuitModular.UnsignedGivens.localIdx L.rSelPair8 (βF β) := localIdx_congr L.rSelPair8 hpFγ
  have hb0Eq : b0E145 L (βF γL) = b0E145 L (βF β) := b0E145_congr L hlocEq
  have hloEq : loE145 L (βF γL) = loE145 L (βF β) := loE145_congr L hlocEq
  have hleafEq : wLeaf145 L (b0E145 L (βF γL)) (loE145 L (βF γL)) (loE145_lt_cap_all L (βF γL)) =
      wLeaf145 L (b0E145 L (βF β)) (loE145 L (βF β)) (loE145_lt_cap_all L (βF β)) := by
    simp_rw [hb0Eq, hloEq]
  have hγOh (g : Fin 145) : (βF γL) (L.rOneHot145 g) = (βF β) (L.rOneHot145 g) := by
    rw [← hflWr]; exact CircuitModular.UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ (hnotO g)
  have hencOh (g : Fin 145) :
      Function.update (encAssign145 L (βF γL)) L.wOne 1 (L.rOneHot145 g) =
        Function.update (encAssign145 L (βF β)) L.wOne 1 (L.rOneHot145 g) := by
    rw [Function.update_of_ne (oh145_ne_rest L g 0), Function.update_of_ne (oh145_ne_rest L g 0)]
    dsimp only [encAssign145]; rw [hleafEq]
    by_cases hw : L.rOneHot145 g = wLeaf145 L (b0E145 L (βF β)) (loE145 L (βF β))
        (loE145_lt_cap_all L (βF β))
    · rw [hw, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hγOh g]
  funext w
  by_cases hwSC : w ∈ Set.range rSC.wires
  · obtain ⟨sc, rfl⟩ := hwSC
    have hnp : rSC sc ∉ Set.range L.rSelPair8.wires :=
      fun ⟨i, hi⟩ ↦ hnotC (Lac2Fused184Select.selPair10 i) ⟨sc, hi.symm⟩
    have hno : rSC sc ≠ L.wOne := fun h ↦ hnotR 0 ⟨sc, h⟩
    have hnl : rSC sc ≠ wLeaf145 L (b0E145 L (βF β)) (loE145 L (βF β))
        (loE145_lt_cap_all L (βF β)) :=
      fun h ↦ hnotO _ ⟨sc, h⟩
    rw [CircuitModular.UnsignedGivens.writeReg_apply_reg]
    dsimp only [β₂, Lac2Fused184Select.fanoutActIdxAssign, encAssign145]
    rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ hnp, Function.update_of_ne hno,
      Function.update_of_ne hno, hleafEq, Function.update_of_ne hnl, ← hflWr]
    exact (CircuitModular.UnsignedGivens.writeReg_apply_reg _ _ _ sc).symm
  · rw [CircuitModular.UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwSC]
    by_cases hwP : w ∈ Set.range L.rSelPair8.wires
    · obtain ⟨i, rfl⟩ := hwP
      dsimp only [β₂, Lac2Fused184Select.fanoutActIdxAssign]
      rw [OneHotSimulates.writeReg_apply_reg, OneHotSimulates.writeReg_apply_reg]
      simp_rw [hencOh]
      rw [Function.update_of_ne (rest14_ne_pair L 0 i).symm,
        Function.update_of_ne (rest14_ne_pair L 0 i).symm]
      dsimp only [encAssign145]; rw [hleafEq,
        Function.update_of_ne (oh145_ne_pair L _ i).symm,
        Function.update_of_ne (oh145_ne_pair L _ i).symm, hpFγ i]
    · dsimp only [β₂, Lac2Fused184Select.fanoutActIdxAssign]
      rw [OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ hwP,
        OneHotSimulates.writeReg_apply_of_not_mem _ _ _ _ hwP]
      simp only [Function.update_idem]
      by_cases hw1 : w = L.wOne
      · subst hw1; simp only [Function.update_self]; simp_rw [hencOh]
      · rw [Function.update_of_ne hw1, Function.update_of_ne hw1]
        dsimp only [encAssign145]; rw [hleafEq]
        by_cases hwl : w = wLeaf145 L (b0E145 L (βF β)) (loE145 L (βF β))
            (loE145_lt_cap_all L (βF β))
        · subst hwl; simp
        · rw [Function.update_of_ne hwl, Function.update_of_ne hwl, ← hflWr]
          exact (CircuitModular.UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwSC).symm

attribute [irreducible] dEnc145Dyn dDec145Dyn

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Balanced160Select

end
