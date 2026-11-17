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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.TableXUncompute

set_option Elab.async false

@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModGridGuard654Refl
@[expose] public section
namespace GridGuard654ReflAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
end GridGuard654ReflAlt
namespace GridGuard654ReflAux
section ConfigGridGuard654Refl
set_option maxRecDepth 4096
local instance (priority := 1000000) instNeZeroTwoPowGridGuard (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Real Operator Matrix QProg HermitianMat LocalClassicalPerm
open SpecsAux SpecsAux.SpecMirror
open scoped Matrix BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder Circuit.Notation
section GenericGuardEngine
variable {Var : Type} {n : ℕ}
theorem localPermX {S : Finset (Wire n)} (q : Wire n) (hq : q ∈ S) :
    LocalClassicalPerm S (Circuit.X q) (fun β ↦ Function.update β q (β q + 1)) where
  perm := ClassicalPerm.X q
  support_sub := by
    intro w hw
    simp only [Circuit.support_single, Finset.mem_singleton] at hw
    exact hw ▸ hq
  preserves_outside β w hw := by
    have hwq : w ≠ q := fun h ↦ hw (h ▸ hq)
    exact Function.update_of_ne hwq _ _
  depends_on β₁ β₂ hβ w hw := by
    by_cases hwq : w = q
    · subst hwq; simp [hβ w hw]
    · simp [Function.update_of_ne hwq, hβ w hw]
@[simp] theorem xPerm_self_cancel (q : Wire n) (β : BitAssignment n) :
    let f := fun γ : BitAssignment n ↦ Function.update γ q (γ q + 1)
    f (f β) = β := by
  intro f; funext w; dsimp only [f]
  by_cases hwq : w = q
  · subst hwq; simp [LocalClassicalPerm.zmod2_add_cancel_right]
  · simp [Function.update_of_ne hwq]
def symWrapDynList (v : Var) (L : List (SymTempAndStep n)) (core : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  TempAndStep.wrapDynamicList v (L.map SymTempAndStep.toTempAndStep) core
def symWrapCircuitList (L : List (SymTempAndStep n)) (core : Circuit n) : Circuit n :=
  TempAndStep.wrapCircuitList (L.map SymTempAndStep.toTempAndStep) core
def symStepFwdList : List (SymTempAndStep n) → BitAssignment n → BitAssignment n
  | [], β => β
  | s :: rest, β => symStepFwdList rest (s.stepFwd β)
@[simp] theorem symStepFwdList_nil (β : BitAssignment n) :
    symStepFwdList ([] : List (SymTempAndStep n)) β = β := rfl
@[simp] theorem symStepFwdList_cons (s : SymTempAndStep n) (rest : List (SymTempAndStep n))
    (β : BitAssignment n) :
    symStepFwdList (s :: rest) β = symStepFwdList rest (s.stepFwd β) := rfl
theorem symStepFwdList_append (L₁ L₂ : List (SymTempAndStep n)) (β : BitAssignment n) :
    symStepFwdList (L₁ ++ L₂) β = symStepFwdList L₂ (symStepFwdList L₁ β) := by
  induction L₁ generalizing β with
  | nil => rfl
  | cons s rest ih => exact ih (s.stepFwd β)
theorem symWrapDynList_count_TOFF (v : Var) (L : List (SymTempAndStep n))
    (core : DynamicCircuit Var n) :
    (symWrapDynList v L core).count .TOFF = core.count .TOFF := by
  apply TempAndStep.count_wrapDynamicList_toff
  intro s hs
  rcases List.mem_map.mp hs with ⟨s', _, rfl⟩
  exact s'.clifford
theorem symWrapDynList_count_T (v : Var) (L : List (SymTempAndStep n))
    (core : DynamicCircuit Var n) :
    (symWrapDynList v L core).count .T = 4 * L.length + core.count .T := by
  rw [symWrapDynList, TempAndStep.count_wrapDynamicList_t]
  · simp
  · intro s hs
    rcases List.mem_map.mp hs with ⟨s', _, rfl⟩
    exact s'.clifford
def ValidSymStepList (M : Finset (Wire n)) {m_anc : ℕ} (rAnc : QRegister m_anc n) :
    ℕ → List (SymTempAndStep n) → Prop
  | _, [] => True
  | offset, s :: rest =>
      ∃ hlt : offset < m_anc,
        s.anc = rAnc ⟨offset, hlt⟩ ∧
        Disjoint s.S M ∧
        (∀ j : Fin m_anc, offset < j.val → rAnc j ∉ s.S) ∧
        ValidSymStepList M rAnc (offset + 1) rest
theorem validSymStepList_append (M : Finset (Wire n)) {m_anc : ℕ} (rAnc : QRegister m_anc n)
    (offset : ℕ) (L₁ L₂ : List (SymTempAndStep n)) :
    ValidSymStepList M rAnc offset (L₁ ++ L₂) ↔
      ValidSymStepList M rAnc offset L₁ ∧ ValidSymStepList M rAnc (offset + L₁.length) L₂ := by
  induction L₁ generalizing offset with
  | nil => simp [ValidSymStepList]
  | cons s rest ih =>
      simp only [List.cons_append, ValidSymStepList, List.length_cons]
      have hadd : offset + (rest.length + 1) = (offset + 1) + rest.length := by omega
      rw [hadd, ih (offset + 1)]
      constructor
      · rintro ⟨hlt, hanc, hdisj, hlat, hrest, hL₂⟩
        exact ⟨⟨hlt, hanc, hdisj, hlat, hrest⟩, hL₂⟩
      · rintro ⟨⟨hlt, hanc, hdisj, hlat, hrest⟩, hL₂⟩
        exact ⟨hlt, hanc, hdisj, hlat, hrest, hL₂⟩
theorem wp_wrapDynamic_update_eq [Finite Var] [DecidableEq Var] [NeZero (2 ^ n)] (v : Var)
    (s : TempAndStep n) (inner : DynamicCircuit Var n) (h_inner : ∀ Ψ : CQAssertionCompat Var (2 ^
    n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) → ∀ σ val, wp inner.compile Ψ
    (Function.update σ v val) = wp inner.compile Ψ σ) (Θ : CQAssertionCompat Var (2 ^ n))
    (_hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) (σ : Store Var) (val : ℤ) : wp
    (s.wrapDynamic v inner).compile Θ (Function.update σ v val) = wp
    (s.wrapDynamic v inner).compile Θ σ := by
  cases nonempty_fintype Var
  let Θ₁ := wpQAssignCompat s.post.eval Θ
  let Ψ := wpQAssignCompat s.midPost.eval
    (wp (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).compile Θ₁)
  have hΨ : ∀ σ' val', Ψ (Function.update σ' v val') = Ψ σ' := by
    intro σ' val'
    dsimp only [Ψ, wpQAssignCompat]
    rw [DynamicCircuit.wp_andUncompute_update_self]
  have h_in := h_inner Ψ hΨ σ val
  have hexpand : wp (s.wrapDynamic v inner).compile Θ = wpQAssignCompat s.pre.eval
      (wpQAssignCompat (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a).eval (wpQAssignCompat
      s.midPre.eval (wp inner.compile Ψ))) := by
    simp [TempAndStep.wrapDynamic, DynamicCircuit.andCompute, Θ₁, Ψ]
  rw [hexpand]
  simp only [wpQAssignCompat, h_in]
lemma restrictAssertionToZeroAncilla_slice_cast {m_anc : ℕ}
    (A : CQAssertionCompat Var (2 ^ n)) (r : QRegister m_anc n) (o q₁ q₂ : ℕ) (hq : q₁ = q₂)
    (h₁ : o + q₁ ≤ m_anc) (h₂ : o + q₂ ≤ m_anc) : CQAssertion.restrictToZeroAncilla A
    (r.slice o q₁ h₁) = CQAssertion.restrictToZeroAncilla A (r.slice o q₂ h₂) := by
  subst hq; rfl
theorem symWrapList_correct
    [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m_anc m_inner : ℕ}
    (v : Var) (M : Finset (Wire n)) (rAnc : QRegister m_anc n)
    (offset : ℕ) (L : List (SymTempAndStep n))
    (hbound : offset + L.length + m_inner ≤ m_anc)
    (hvalid : ValidSymStepList M rAnc offset L)
    (inner : DynamicCircuit Var n) (c_inner : Circuit n)
    (f_inner : BitAssignment n → BitAssignment n)
    (h_inner_perm : ClassicalPerm c_inner f_inner)
    (h_inner_out : ∀ β w, w ∉ M → f_inner β w = β w)
    (h_inner_wp : ∀ Ψ : CQAssertionCompat Var (2 ^ n),
      (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
        CQAssertion.restrictToZeroAncilla (wp inner.compile Ψ)
          (rAnc.slice (offset + L.length) m_inner (by omega)) =
        CQAssertion.restrictToZeroAncilla (wpQAssignCompat c_inner.eval Ψ)
          (rAnc.slice (offset + L.length) m_inner (by omega)))
    (h_inner_upd : ∀ Ψ : CQAssertionCompat Var (2 ^ n),
      (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
      ∀ σ val, wp inner.compile Ψ (Function.update σ v val) = wp inner.compile Ψ σ) :
    let f_wrap : BitAssignment n → BitAssignment n :=
      fun β w ↦ if w ∈ M then f_inner (symStepFwdList L β) w else β w
    ClassicalPerm (symWrapCircuitList L c_inner) f_wrap ∧
    (∀ β w, w ∉ M → f_wrap β w = β w) ∧
    (∀ Θ : CQAssertionCompat Var (2 ^ n),
      (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
        CQAssertion.restrictToZeroAncilla
          (wp (symWrapDynList v L inner).compile Θ)
          (rAnc.slice offset (L.length + m_inner) (by omega)) =
        CQAssertion.restrictToZeroAncilla
          (wpQAssignCompat (symWrapCircuitList L c_inner).eval Θ)
          (rAnc.slice offset (L.length + m_inner) (by omega))) ∧
    (∀ Θ : CQAssertionCompat Var (2 ^ n),
      (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ val, wp (symWrapDynList v L inner).compile Θ (Function.update σ v val) =
        wp (symWrapDynList v L inner).compile Θ σ) := by
  induction L generalizing offset with
  | nil =>
      intro f_wrap
      have hf : f_wrap = f_inner := funext fun β ↦ funext fun w ↦ by
        by_cases hw : w ∈ M
        · simp [f_wrap, symStepFwdList, hw]
        · simp [f_wrap, symStepFwdList, hw, h_inner_out β w hw]
      refine ⟨by simpa [symWrapCircuitList, TempAndStep.wrapCircuitList, hf] using h_inner_perm,
        fun β w hw ↦ by simp [f_wrap, hw], fun Θ hΘ ↦ ?_, h_inner_upd⟩
      have hlen0 : ([] : List (SymTempAndStep n)).length + m_inner = m_inner := Nat.zero_add _
      rw [restrictAssertionToZeroAncilla_slice_cast _ rAnc offset _ m_inner hlen0,
        restrictAssertionToZeroAncilla_slice_cast _ rAnc offset _ m_inner hlen0]
      simpa [symWrapDynList, symWrapCircuitList, TempAndStep.wrapDynamicList,
        TempAndStep.wrapCircuitList] using h_inner_wp Θ hΘ
  | cons s rest ih =>
      intro f_wrap
      rcases hvalid with ⟨hlt, hanc, hdisj_SM, hlat, hvalid_rest⟩
      have hbound_rest : (offset + 1) + rest.length + m_inner ≤ m_anc := by
        simp only [List.length_cons] at hbound; omega
      have hreg : rAnc.slice ((offset + 1) + rest.length) m_inner (by omega) =
          rAnc.slice (offset + (s :: rest).length) m_inner (by omega) :=
        QRegister.ext (Function.Embedding.ext fun i ↦
          congrArg rAnc.wires (Fin.ext (by dsimp [List.length_cons]; omega)))
      obtain ⟨hperm_rest, hout_rest, hwp_rest, hupd_rest⟩ :=
        ih (offset + 1) hbound_rest hvalid_rest fun Ψ hΨ ↦ hreg.symm ▸ h_inner_wp Ψ hΨ
      let rTotal := rAnc.slice offset ((rest.length + m_inner) + 1) (by omega)
      have hrTotal_zero : s.anc = rTotal 0 :=
        hanc.trans (congrArg rAnc.wires (Fin.ext (by dsimp))).symm
      have hrTotal_tail : rTotal.slice 1 (rest.length + m_inner) (by omega) =
          rAnc.slice (offset + 1) (rest.length + m_inner) (by omega) :=
        QRegister.ext (Function.Embedding.ext fun i ↦
          congrArg rAnc.wires (Fin.ext (by dsimp; omega)))
      have hdisj_S_tail :
          Disjoint s.S (rTotal.slice 1 (rest.length + m_inner) (by omega)).image := by
        rw [hrTotal_tail, Finset.disjoint_right]
        rintro w hw
        rcases (QRegister.mem_image _ w).mp hw with ⟨i, rfl⟩
        exact hlat ⟨(offset + 1) + i.val, by omega⟩ (by dsimp; omega)
      obtain ⟨hperm_s, _, hwp_s⟩ :=
        s.wrap_correct v hdisj_SM (symWrapDynList v rest inner) (symWrapCircuitList rest c_inner)
          _ rTotal hrTotal_zero hdisj_S_tail hperm_rest hout_rest
          (fun Ψ hΨ ↦ hrTotal_tail.symm ▸ hwp_rest Ψ hΨ)
      have hf_eq : (fun β w ↦ if w ∈ M then (if w ∈ M then f_inner (symStepFwdList rest
          (s.stepFwd β)) w else s.stepFwd β w) else β w) = f_wrap :=
        funext fun β ↦ funext fun w ↦ by
          dsimp only [f_wrap, symStepFwdList]
          by_cases hw : w ∈ M <;> simp only [hw, ↓reduceIte]
      have hlen : (rest.length + m_inner) + 1 = (s :: rest).length + m_inner := by
        dsimp [List.length_cons]; omega
      refine ⟨by simpa [symWrapCircuitList, TempAndStep.wrapCircuitList, hf_eq] using hperm_s,
        fun β w hw ↦ by simp [f_wrap, hw], fun Θ hΘ ↦ ?_, fun Θ hΘ σ val ↦
          wp_wrapDynamic_update_eq v s.toTempAndStep _ hupd_rest Θ hΘ σ val⟩
      rw [← restrictAssertionToZeroAncilla_slice_cast _ rAnc offset _ _ hlen,
        ← restrictAssertionToZeroAncilla_slice_cast _ rAnc offset _ _ hlen]
      exact hwp_s Θ hΘ
def StoreConst [Fintype Var] [DecidableEq Var] (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ ↦ M) =
    (fun _ ↦ M')
namespace StoreConst
section WithVar
variable [Fintype Var] [DecidableEq Var]
theorem identity : StoreConst (.identity : DynamicCircuit Var n) := fun M ↦ ⟨M, rfl⟩
theorem circuit (c : Circuit n) : StoreConst (.circuit c : DynamicCircuit Var n) :=
  fun M ↦ ⟨qAssignObsMap c.eval M, by
    funext σ
    rw [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
    rfl⟩
theorem seq {d₁ d₂ : DynamicCircuit Var n} (h₁ : StoreConst d₁) (h₂ : StoreConst d₂) :
    StoreConst (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hm₂⟩ := h₂ M
  obtain ⟨M₁, hm₁⟩ := h₁ M₂
  exact ⟨M₁, by simp only [DynamicCircuit.compile_seq, wp_qSeq, hm₂, hm₁]⟩
theorem andUncompute [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) :
    StoreConst (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂) := by
  intro M
  let σ₀ : Store Var := fun _ ↦ 0
  refine ⟨wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile (fun _ ↦ M) σ₀, ?_⟩
  funext σ
  let F := Circuit.andUncomputeFixup c₁ c₂ anc h₁₂
  let qifProg : QProg Var (2 ^ n) := qprogQIfVar v F.compile .skip
  let measProg : QProg Var (2 ^ n) :=
    .qSeq (QProg.measureRegister v (QRegister.singleton anc)) qifProg
  have hF_const : ∀ τ₁ τ₂ : Store Var,
      wp F.compile (fun _ ↦ M) τ₁ = wp F.compile (fun _ ↦ M) τ₂ := by
    intro τ₁ τ₂
    rw [DynCircuitExt.wp_circuit_compile_compat]
    rfl
  have hqif : ∀ τ₁ τ₂ : Store Var, τ₁ v = τ₂ v →
      wp qifProg (fun _ ↦ M) τ₁ = wp qifProg (fun _ ↦ M) τ₂ := by
    intro τ₁ τ₂ heq
    simp only [qifProg, wp_qIf, wp_skip, heq, hF_const τ₁ τ₂]
  have hmeas : wp measProg (fun _ ↦ M) = fun _ ↦ wp measProg (fun _ ↦ M) σ₀ := by
    funext τ; apply Subtype.ext
    simp only [measProg, QProg.measureRegister, wp_qSeq, wp_qMeasure_apply,
      qMeasure_obs_map_coe, CQAssertionCompat.subst_apply]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    have hv : (τ.subst v (Int.ofNat o.val)) v = (σ₀.subst v (Int.ofNat o.val)) v := by
      simp [Store.subst]
    rw [hqif _ _ hv]
  change wp (Circuit.H anc).compile (wp measProg (fun _ ↦ M)) σ =
    wp (Circuit.H anc).compile (wp measProg (fun _ ↦ M)) σ₀
  rw [hmeas, DynCircuitExt.wp_circuit_compile_compat]
  rfl
theorem wrapDynamic [NeZero (2 ^ n)] (v : Var) (s : TempAndStep n) {inner : DynamicCircuit Var n}
    (h_in : StoreConst inner) :
    StoreConst (s.wrapDynamic v inner) := by
  unfold TempAndStep.wrapDynamic DynamicCircuit.andCompute
  exact (circuit s.pre).seq ((circuit _).seq (((circuit s.midPre).seq (h_in.seq (circuit
    s.midPost))).seq ((andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).seq (circuit s.post))))
theorem symWrapDynList [NeZero (2 ^ n)] (v : Var) (L : List (SymTempAndStep n))
    {inner : DynamicCircuit Var n} (h_in : StoreConst inner) :
    StoreConst (GridGuard654ReflAux.symWrapDynList v L inner) := by
  induction L with
  | nil => exact h_in
  | cons s rest ih => exact wrapDynamic v s.toTempAndStep ih
end WithVar
end StoreConst
theorem realizesEmbeddedUnitary_of_wp_eq_and_mul_proj [Fintype Var] [DecidableEq Var]
    [NeZero (2 ^ n)] {k m : ℕ} (rAct : QRegister k n) (rWork : QRegister m n)
    (u : Unitary (2 ^ k)) (d : DynamicCircuit Var n) (c_ref : Circuit n)
    (hconst : StoreConst d) (hwp : ∀ M : Observable (Fin (2 ^ n)), CQAssertion.restrictToZeroAncilla
    (wp d.compile (fun _ ↦ M)) rWork = CQAssertion.restrictToZeroAncilla (wpQAssignCompat
    c_ref.eval (fun _ ↦ M)) rWork) (hproj : c_ref.eval.1 * rWork.basisOutcomeProjector 0 =
    (rAct.embedUnitary u).1 * rWork.basisOutcomeProjector 0) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d := by
  intro M
  obtain ⟨M', hm'⟩ := hconst M
  refine ⟨M', hm', ?_⟩
  let σ₀ : Store Var := fun _ ↦ 0
  have hP₀_herm : (rWork.basisOutcomeProjector 0)ᴴ = rWork.basisOutcomeProjector 0 :=
    rWork.basisOutcomeProjector_conjTranspose 0
  have hadj : rWork.basisOutcomeProjector 0 * c_ref.eval.1ᴴ =
      rWork.basisOutcomeProjector 0 * (rAct.embedUnitary u).1ᴴ := by
    have h := congrArg conjTranspose hproj
    rwa [conjTranspose_mul, conjTranspose_mul, hP₀_herm] at h
  have h1 := congrArg (fun A ↦ (A σ₀).1) (hwp M)
  rw [hm'] at h1
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj] at h1
  rw [hadj] at h1
  have heq := congrArg Subtype.val h1
  simpa [Matrix.mul_assoc, hP₀_herm] using heq
theorem realizesEmbeddedUnitary_changeActive_of_mul_proj
    [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {k₁ k₂ m : ℕ}
    (rAct₁ : QRegister k₁ n) (rAct₂ : QRegister k₂ n) (rWork : QRegister m n)
    (u₁ : Unitary (2 ^ k₁)) (u₂ : Unitary (2 ^ k₂)) (d : DynamicCircuit Var n)
    (hreal : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct₁ rWork u₁ d)
    (hproj : (rAct₁.embedUnitary u₁).1 * rWork.basisOutcomeProjector 0 =
      (rAct₂.embedUnitary u₂).1 * rWork.basisOutcomeProjector 0) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct₂ rWork u₂ d := by
  intro M
  obtain ⟨M', hwp, heq⟩ := hreal M
  refine ⟨M', hwp, ?_⟩
  have hP₀_herm : (rWork.basisOutcomeProjector 0)ᴴ = rWork.basisOutcomeProjector 0 :=
    rWork.basisOutcomeProjector_conjTranspose 0
  have hadj : rWork.basisOutcomeProjector 0 * (rAct₁.embedUnitary u₁).1ᴴ =
      rWork.basisOutcomeProjector 0 * (rAct₂.embedUnitary u₂).1ᴴ := by
    have h := congrArg conjTranspose hproj
    rwa [conjTranspose_mul, conjTranspose_mul, hP₀_herm] at h
  calc rWork.basisOutcomeProjector 0 * M'.1.1 * rWork.basisOutcomeProjector 0
      = (rWork.basisOutcomeProjector 0 * (rAct₁.embedUnitary u₁).1ᴴ) * M.1.1 *
          ((rAct₁.embedUnitary u₁).1 * rWork.basisOutcomeProjector 0) := by
          simpa only [Matrix.mul_assoc] using heq
    _ = rWork.basisOutcomeProjector 0 *
          ((rAct₂.embedUnitary u₂).1ᴴ * M.1.1 * (rAct₂.embedUnitary u₂).1) *
          rWork.basisOutcomeProjector 0 := by
          rw [hadj, hproj]
          simp only [Matrix.mul_assoc]
noncomputable def guardReflMatrix {d : ℕ} (P : Operator d) : Operator d := (2 : ℂ) • P - 1
theorem guardReflMatrix_conjTranspose {d : ℕ} {P : Operator d} (hP_herm : P.IsHermitian) :
    (guardReflMatrix P)ᴴ = guardReflMatrix P := by
  simp [guardReflMatrix, conjTranspose_sub, conjTranspose_smul, hP_herm.eq]
theorem guardReflMatrix_mul_self {d : ℕ} {P : Operator d} (hP_idem : P * P = P) :
    guardReflMatrix P * guardReflMatrix P = 1 := by
  have h2 : ∀ M : Operator d, (2 : ℂ) • M = 2 * M :=
    fun M ↦ (two_smul ℂ M).trans (two_mul M).symm
  rw [guardReflMatrix, h2]
  calc (2 * P - 1) * (2 * P - 1)
      = 4 * (P * P - P) + 1 := by noncomm_ring
    _ = 1 := by rw [hP_idem, sub_self, mul_zero, zero_add]
noncomputable def ctrlInvolutionMatrix {k : ℕ} (g : Wire n) (r : QRegister k n)
    (R : Operator (2 ^ k)) : Operator (2 ^ n) := (QRegister.singleton g).basisOutcomeProjector
    0 + (QRegister.singleton g).basisOutcomeProjector 1 * r.embedMatrix R
lemma basisOutcomeProjector_idem_local {m k : ℕ} (r : QRegister m k) (o : Fin (2 ^ m)) :
    r.basisOutcomeProjector o * r.basisOutcomeProjector o = r.basisOutcomeProjector o := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  by_cases h : r.extractIndex x = o <;> simp [h]
lemma basisOutcomeProjector_orthogonal_local {m k : ℕ} (r : QRegister m k)
    {o₁ o₂ : Fin (2 ^ m)} (h : o₁ ≠ o₂) :
    r.basisOutcomeProjector o₁ * r.basisOutcomeProjector o₂ = 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h₁ : r.extractIndex i = o₁
    · simp [h₁, h]
    · simp only [Matrix.diagonal_apply, ↓reduceIte, h₁, zero_mul, Matrix.zero_apply]
  · simp [hij]
noncomputable def ctrlLocalUnitary {k : ℕ} (R : Unitary (2 ^ k)) : Unitary (2 ^ (k + 1)) :=
  let rSysLoc : QRegister k (k + 1) := .block 0 k (by omega)
  let qCtrlLoc : Wire (k + 1) := ⟨k, by omega⟩
  let M : Operator (2 ^ (k + 1)) := ctrlInvolutionMatrix qCtrlLoc rSysLoc R.1
  ⟨M, by
    have hdisj : rSysLoc.DisjointWires (QRegister.singleton qCtrlLoc) := by
      rw [QRegExt.disjointWires_iff_disjoint_image, QRegister.image_singleton,
        Finset.disjoint_singleton_right]
      intro hmem
      rcases (QRegister.mem_image rSysLoc qCtrlLoc).mp hmem with ⟨idx, hidx⟩
      have hv := congrArg Fin.val hidx
      dsimp [rSysLoc, qCtrlLoc, GridGuard654ReflAlt.qreg_block_apply] at hv
      omega
    let P₀ := (QRegister.singleton qCtrlLoc).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton qCtrlLoc).basisOutcomeProjector 1
    have hP₀_herm : P₀ᴴ = P₀ := (QRegister.singleton qCtrlLoc).basisOutcomeProjector_conjTranspose 0
    have hP₁_herm : P₁ᴴ = P₁ := (QRegister.singleton qCtrlLoc).basisOutcomeProjector_conjTranspose 1
    have hP₀_idem : P₀ * P₀ = P₀ := basisOutcomeProjector_idem_local _ 0
    have hP₁_idem : P₁ * P₁ = P₁ := basisOutcomeProjector_idem_local _ 1
    have hP₀₁ : P₀ * P₁ = 0 := basisOutcomeProjector_orthogonal_local _ (by decide)
    have hP₁₀ : P₁ * P₀ = 0 := basisOutcomeProjector_orthogonal_local _ (by decide)
    have hsum : P₀ + P₁ = 1 := by
      ext i j
      dsimp only [P₀, P₁]
      rw [Matrix.add_apply, QRegister.basisOutcomeProjector_eq_diagonal,
        QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1)
          ((QRegister.singleton qCtrlLoc).extractIndex i) with hx | hx <;> simp [hx]
      · simp [hij]
    have hcomm₁ : rSysLoc.embedMatrix R.1 * P₁ = P₁ * rSysLoc.embedMatrix R.1 :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rSysLoc) _ hdisj R.1 1
    have hRR : rSysLoc.embedMatrix R.1 * (rSysLoc.embedMatrix R.1)ᴴ = 1 := by
      simpa only [QRegister.embedUnitary_val, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
        Unitary.coe_mul_star_self (rSysLoc.embedUnitary R)
    have hRR' : (rSysLoc.embedMatrix R.1)ᴴ * rSysLoc.embedMatrix R.1 = 1 := by
      simpa only [QRegister.embedUnitary_val, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
        Unitary.coe_star_mul_self (rSysLoc.embedUnitary R)
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    dsimp only [M, ctrlInvolutionMatrix]
    change (P₀ + P₁ * rSysLoc.embedMatrix R.1)ᴴ * (P₀ + P₁ * rSysLoc.embedMatrix R.1) = 1 ∧
      (P₀ + P₁ * rSysLoc.embedMatrix R.1) * (P₀ + P₁ * rSysLoc.embedMatrix R.1)ᴴ = 1
    rw [conjTranspose_add, conjTranspose_mul, hP₀_herm, hP₁_herm]
    have hcomm₁_adj : (rSysLoc.embedMatrix R.1)ᴴ * P₁ = P₁ * (rSysLoc.embedMatrix R.1)ᴴ := by
      have h := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rSysLoc) _ hdisj R.1ᴴ 1
      rwa [QRegister.embedMatrix_conjTranspose] at h
    constructor
    · calc (P₀ + (rSysLoc.embedMatrix R.1)ᴴ * P₁) * (P₀ + P₁ * rSysLoc.embedMatrix R.1)
          = P₀ * P₀ + (P₀ * P₁) * rSysLoc.embedMatrix R.1 +
              (rSysLoc.embedMatrix R.1)ᴴ * (P₁ * P₀) +
              (rSysLoc.embedMatrix R.1)ᴴ * (P₁ * P₁) * rSysLoc.embedMatrix R.1 := by noncomm_ring
        _ = P₀ + P₁ * ((rSysLoc.embedMatrix R.1)ᴴ * rSysLoc.embedMatrix R.1) := by
              rw [hP₀_idem, hP₀₁, hP₁₀, hP₁_idem, hcomm₁_adj]
              noncomm_ring
        _ = 1 := by rw [hRR', Matrix.mul_one, hsum]
    · calc (P₀ + P₁ * rSysLoc.embedMatrix R.1) * (P₀ + (rSysLoc.embedMatrix R.1)ᴴ * P₁)
          = P₀ * P₀ + P₁ * rSysLoc.embedMatrix R.1 * P₀ +
              P₀ * (rSysLoc.embedMatrix R.1)ᴴ * P₁ +
              P₁ * (rSysLoc.embedMatrix R.1 * (rSysLoc.embedMatrix R.1)ᴴ) * P₁ := by noncomm_ring
        _ = P₀ + P₁ := by
              have h10a : P₁ * rSysLoc.embedMatrix R.1 * P₀ =
                  rSysLoc.embedMatrix R.1 * (P₁ * P₀) := by rw [← hcomm₁]; noncomm_ring
              have h01a : P₀ * (rSysLoc.embedMatrix R.1)ᴴ * P₁ =
                  (P₀ * P₁) * (rSysLoc.embedMatrix R.1)ᴴ := by
                rw [Matrix.mul_assoc P₀, hcomm₁_adj]; noncomm_ring
              rw [hP₀_idem, h10a, h01a, hP₁₀, hP₀₁, hRR, Matrix.mul_one, hP₁_idem]
              noncomm_ring
        _ = 1 := hsum⟩
def optX (inv : Bool) (q : Wire n) : Circuit n := if inv then Circuit.X q else .identity
def polBit (inv : Bool) (b : ZMod 2) : ZMod 2 := if inv then b + 1 else b
theorem localClassicalPerm_optX {S : Finset (Wire n)} (inv : Bool) (q : Wire n) (hq : q ∈ S) :
    LocalClassicalPerm S (optX inv q) (fun β ↦ Function.update β q (polBit inv (β q))) := by
  cases inv
  · have hid : (fun β : BitAssignment n ↦ Function.update β q (polBit false (β q))) = id := by
      funext β w; simp [polBit]
    rw [hid]
    exact LocalClassicalPerm.identity S
  · simpa [optX, polBit] using localPermX q hq
@[simp] theorem optX_self_cancel (inv : Bool) (q : Wire n) (β : BitAssignment n) :
    let f := fun γ : BitAssignment n ↦ Function.update γ q (polBit inv (γ q))
    f (f β) = β := by
  cases inv
  · intro f; simp [f, polBit]
  · exact xPerm_self_cancel q β
def litAndSymStep (polA polB polOut : Bool) (a b anc : Wire n)
    (hab : a ≠ b) (ha_anc : a ≠ anc) (hb_anc : b ≠ anc) : SymTempAndStep n where
  pre := optX polA a ;;ᶜ optX polB b
  c₁ := a
  c₂ := b
  anc := anc
  h₁₂ := hab
  h₁a := ha_anc
  h₂a := hb_anc
  midPre := optX polB b ;;ᶜ (optX polA a ;;ᶜ optX polOut anc)
  midPost := optX polOut anc ;;ᶜ (optX polA a ;;ᶜ optX polB b)
  post := optX polB b ;;ᶜ optX polA a
  S := {a, b, anc}
  f_pre := (fun β ↦ Function.update β b (polBit polB (β b))) ∘
    (fun β ↦ Function.update β a (polBit polA (β a)))
  f_midPre := ((fun β ↦ Function.update β anc (polBit polOut (β anc))) ∘
    (fun β ↦ Function.update β a (polBit polA (β a)))) ∘
    (fun β ↦ Function.update β b (polBit polB (β b)))
  f_midPost := ((fun β ↦ Function.update β b (polBit polB (β b))) ∘
    (fun β ↦ Function.update β a (polBit polA (β a)))) ∘
    (fun β ↦ Function.update β anc (polBit polOut (β anc)))
  f_post := (fun β ↦ Function.update β a (polBit polA (β a))) ∘
    (fun β ↦ Function.update β b (polBit polB (β b)))
  clifford := by
    cases polA <;> cases polB <;> cases polOut <;> simp [optX, TempAndStep.IsCliffordWrapper]
  local_pre := (localClassicalPerm_optX polA a (by simp)).seq
    (localClassicalPerm_optX polB b (by simp))
  local_post := (localClassicalPerm_optX polB b (by simp)).seq
    (localClassicalPerm_optX polA a (by simp))
  local_midPre := (localClassicalPerm_optX polB b (by simp)).seq
    ((localClassicalPerm_optX polA a (by simp)).seq
      (localClassicalPerm_optX polOut anc (by simp)))
  local_midPost := (localClassicalPerm_optX polOut anc (by simp)).seq
    ((localClassicalPerm_optX polA a (by simp)).seq
      (localClassicalPerm_optX polB b (by simp)))
  post_pre_id := LocalClassicalPerm.comp_self_inv₂ _ _
    (optX_self_cancel polA a) (optX_self_cancel polB b)
  midPost_midPre_id := fun β ↦ by
    simp only [Function.comp_apply, optX_self_cancel polOut anc,
      optX_self_cancel polA a, optX_self_cancel polB b]
  c₁_mem := by simp
  c₂_mem := by simp
  anc_mem := by simp
  anc_not_mem_pre := by
    cases polA <;> cases polB <;> simp [optX, Circuit.support_seq, ha_anc.symm, hb_anc.symm]
theorem litAndSymStep_stepFwd (polA polB polOut : Bool) (a b anc : Wire n) (hab : a ≠ b)
    (ha_anc : a ≠ anc) (hb_anc : b ≠ anc) (β : BitAssignment n) (hβ_anc : β anc = 0) :
    (litAndSymStep polA polB polOut a b anc hab ha_anc hb_anc).stepFwd β = Function.update β
    anc (polBit polOut (polBit polA (β a) * polBit polB (β b))) := by
  have hpol : ∀ (inv : Bool) (x : ZMod 2), polBit inv (polBit inv x) = x := by decide
  funext w
  dsimp only [SymTempAndStep.stepFwd, litAndSymStep, Function.comp_apply]
  by_cases hw_anc : w = anc
  · subst hw_anc
    simp [Function.update_self, Function.update_of_ne ha_anc.symm,
      Function.update_of_ne hb_anc.symm, Function.update_of_ne hab,
      Function.update_of_ne hab.symm, hβ_anc]
  · by_cases hwa : w = a
    · subst hwa
      simp [Function.update_self, Function.update_of_ne hw_anc, Function.update_of_ne hab, hpol]
    · by_cases hwb : w = b
      · subst hwb
        simp [Function.update_self, Function.update_of_ne hw_anc, Function.update_of_ne hwa, hpol]
      · simp [Function.update_of_ne hw_anc, Function.update_of_ne hwa, Function.update_of_ne hwb]
def czClifford (c t : Wire n) (h : c ≠ t) : Circuit n :=
  Circuit.S c ;;ᶜ Circuit.S t ;;ᶜ Circuit.CNOT c t h ;;ᶜ
    (Circuit.S t).inverse ;;ᶜ Circuit.CNOT c t h
def ctrlNegZeroCore (g qFlag : Wire n) (h : g ≠ qFlag) : Circuit n :=
  Circuit.Z g ;;ᶜ czClifford g qFlag h
@[simp] theorem count_ctrlNegZeroCore_toff (g qFlag : Wire n) (h : g ≠ qFlag) :
    (ctrlNegZeroCore g qFlag h).count .TOFF = 0 := rfl
@[simp] theorem count_ctrlNegZeroCore_t (g qFlag : Wire n) (h : g ≠ qFlag) :
    (ctrlNegZeroCore g qFlag h).count .T = 0 := rfl
theorem single_diag_gate_evolve (g : PrimitiveGate 1) (q : Wire n) (c₁ : ℂ)
    (hg00 : g.eval.1 0 0 = 1) (hg10 : g.eval.1 1 0 = 0) (hg01 : g.eval.1 0 1 = 0)
    (hg11 : g.eval.1 1 1 = c₁) (β : BitAssignment n) :
    (Circuit.gate g (QRegister.singleton q)).eval.1.mulVec (basisKet β) =
    (if β q = 0 then 1 else c₁) • basisKet β := by
  let r := QRegister.singleton q
  have hext : r.extractIndex ((basisBitsEquiv n).symm β) = if β q = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    simpa [r, QRegister.extractIndex] using h (β q)
  have hcol : g.eval.1.mulVec (Pi.single (if β q = 0 then (0 : Fin 2) else 1) 1) =
      (if β q = 0 then 1 else c₁) • Pi.single (if β q = 0 then (0 : Fin 2) else 1) 1 := by
    by_cases hq : β q = 0 <;> simp only [hq, ↓reduceIte]
    · funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, hg00, hg10]
    · funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, hg01, hg11]
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, basisKet, basisState,
    r.embedMatrix_mulVec_single_factors, hext, hcol, QRegister.tensorState_smul_left,
    QRegister.tensorState_single_replaceIndex, ← hext, r.replaceIndex_extractIndex]
theorem evolve_ctrlNegZeroCore_basisKet (g qFlag : Wire n) (h : g ≠ qFlag) (β : BitAssignment n) :
    (ctrlNegZeroCore g qFlag h).eval.1.mulVec (basisKet β) =
      (if β g = 1 ∧ β qFlag = 0 then (-1 : ℂ) else 1) • basisKet β := by
  have hZ : ∀ γ : BitAssignment n, (Circuit.Z g).eval.1.mulVec (basisKet γ) =
      (if γ g = 0 then (1 : ℂ) else -1) • basisKet γ := fun γ ↦ single_diag_gate_evolve .Z g
      (-1) rfl rfl rfl rfl γ
  have hS : ∀ (q : Wire n) (γ : BitAssignment n), (Circuit.S q).eval.1.mulVec (basisKet γ) =
      (if γ q = 0 then (1 : ℂ) else Complex.I) • basisKet γ := fun q γ ↦
      single_diag_gate_evolve .S q Complex.I rfl rfl rfl rfl γ
  have hSinv : ∀ (q : Wire n) (γ : BitAssignment n), (Circuit.S q).inverse.eval.1.mulVec
      (basisKet γ) = (if γ q = 0 then (1 : ℂ) else -Complex.I) • basisKet γ := by
    intro q γ
    change (Circuit.gate .S (QRegister.singleton q)).inverse.eval.1.mulVec (basisKet γ) = _
    simp only[Circuit.inverse_gate, Circuit.inverseGate, Circuit.sequence, Circuit.eval_seq,
        Circuit.eval_identity, one_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    have hZq := single_diag_gate_evolve .Z q (-1) rfl rfl rfl rfl γ
    rw [hS q γ, Matrix.mulVec_smul, hZq, smul_smul]
    congr 1
    by_cases hγ : γ q = 0 <;> simp [hγ]
  unfold ctrlNegZeroCore czClifford
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    hZ, hS, hSinv, evolve_CNOT_basisKet, Matrix.mulVec_smul, smul_smul]
  have hcnot2 := LocalClassicalPerm.cnot_self_cancel g qFlag h β
  dsimp only at hcnot2
  rw [hcnot2]
  congr 1
  rw [Function.update_self]
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (β g) with hg | hg <;>
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (β qFlag) with hf | hf <;>
    simp [hg, hf]
lemma toff_update_self_cancel (c₁ c₂ anc : Wire n) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (δ : BitAssignment n) :
    let f := fun γ : BitAssignment n ↦ Function.update γ anc (γ anc + γ c₁ * γ c₂)
    f (f δ) = δ := by
  intro f
  funext w
  dsimp only [f]
  by_cases hwa : w = anc
  · subst hwa
    simp [Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
      LocalClassicalPerm.zmod2_add_cancel_right]
  · simp [Function.update_of_ne hwa]
end GenericGuardEngine
section PebbledGuardGeneric
variable {Var : Type} {n : ℕ}
def fieldValidBool {b : ℕ} (isOffsetZero : Bool) (rField : QRegister (b + 1) n)
    (β : BitAssignment n) : Bool :=
  !(decide (∀ u : Fin b, β (rField u.castSucc) = 0) &&
    decide (polBit isOffsetZero (β (rField ⟨b, by omega⟩)) = 1))
def fieldValidStepAt {b : ℕ} (isOffsetZero : Bool)
    (rField : QRegister (b + 1) n) (rAnc : QRegister b n)
    (hdisj : rField.DisjointWires rAnc) (j : Fin b) : SymTempAndStep n :=
  if hj0 : j.val = 0 then
    have hab : rField 0 ≠ rField j.succ := fun h ↦ Fin.succ_ne_zero j (rField.wires.injective
      h.symm)
    have ha_anc : rField 0 ≠ rAnc j := hdisj.ne 0 j
    have hb_anc : rField j.succ ≠ rAnc j := hdisj.ne j.succ j
    litAndSymStep true (!decide (j.val + 1 = b) || isOffsetZero) (decide (j.val + 1 = b))
      (rField 0) (rField j.succ) (rAnc j) hab ha_anc hb_anc
  else
    let jPrev : Fin b := ⟨j.val - 1, by omega⟩
    have hprev_ne : rAnc jPrev ≠ rAnc j := fun h ↦ by
      have hv := congrArg Fin.val (rAnc.wires.injective h); dsimp [jPrev] at hv; omega
    have hab : rAnc jPrev ≠ rField j.succ := (hdisj.ne j.succ jPrev).symm
    have hb_anc : rField j.succ ≠ rAnc j := hdisj.ne j.succ j
    litAndSymStep false (!decide (j.val + 1 = b) || isOffsetZero) (decide (j.val + 1 = b))
      (rAnc jPrev) (rField j.succ) (rAnc j) hab hprev_ne hb_anc
def fieldValidPrefix {b : ℕ} (isOffsetZero : Bool)
    (rField : QRegister (b + 1) n) (rAnc : QRegister b n)
    (hdisj : rField.DisjointWires rAnc) : (t : ℕ) → t ≤ b → List (SymTempAndStep n)
  | 0, _ => []
  | t + 1, ht =>
      fieldValidPrefix isOffsetZero rField rAnc hdisj t (by omega) ++
        [fieldValidStepAt isOffsetZero rField rAnc hdisj ⟨t, ht⟩]
theorem fieldValidPrefix_length {b : ℕ} (isOffsetZero : Bool) (rField : QRegister (b + 1) n)
    (rAnc : QRegister b n) (hdisj : rField.DisjointWires rAnc) (t : ℕ) (ht : t ≤ b) :
    (fieldValidPrefix isOffsetZero rField rAnc hdisj t ht).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [fieldValidPrefix, ih (by omega)]
def fieldValidSteps {b : ℕ} (isOffsetZero : Bool) (rField : QRegister (b + 1) n)
    (rAnc : QRegister b n) (hdisj : rField.DisjointWires rAnc) : List (SymTempAndStep n) :=
    fieldValidPrefix isOffsetZero rField rAnc hdisj b le_rfl
@[simp] theorem fieldValidSteps_length {b : ℕ} (isOffsetZero : Bool)
    (rField : QRegister (b + 1) n) (rAnc : QRegister b n) (hdisj : rField.DisjointWires rAnc)
    : (fieldValidSteps isOffsetZero rField rAnc hdisj).length = b := fieldValidPrefix_length
    isOffsetZero rField rAnc hdisj b le_rfl
def ladderStepAt {p : ℕ} (negIn : Bool) (inWires : Fin (p + 2) → Wire n)
    (hinj : Function.Injective inWires) (rAnc : QRegister (p + 1) n)
    (hdisj : ∀ t, inWires t ∉ rAnc.image) (j : Fin (p + 1)) : SymTempAndStep n :=
  if hj0 : j.val = 0 then
    have hab : inWires 0 ≠ inWires j.succ := fun h ↦ Fin.succ_ne_zero j (hinj h.symm)
    have ha_anc : inWires 0 ≠ rAnc j := QRegister.ne_apply_of_not_mem_image rAnc _ (hdisj 0) j
    have hb_anc : inWires j.succ ≠ rAnc j :=
      QRegister.ne_apply_of_not_mem_image rAnc _ (hdisj j.succ) j
    litAndSymStep negIn negIn false (inWires 0) (inWires j.succ) (rAnc j) hab ha_anc hb_anc
  else
    let jPrev : Fin (p + 1) := ⟨j.val - 1, by omega⟩
    have hprev_ne : rAnc jPrev ≠ rAnc j := fun h ↦ by
      have hv := congrArg Fin.val (rAnc.wires.injective h); dsimp [jPrev] at hv; omega
    have hab : rAnc jPrev ≠ inWires j.succ :=
      (QRegister.ne_apply_of_not_mem_image rAnc _ (hdisj j.succ) jPrev).symm
    have hb_anc : inWires j.succ ≠ rAnc j :=
      QRegister.ne_apply_of_not_mem_image rAnc _ (hdisj j.succ) j
    litAndSymStep false negIn false (rAnc jPrev) (inWires j.succ) (rAnc j) hab hprev_ne hb_anc
def ladderPrefix {p : ℕ} (negIn : Bool)
    (inWires : Fin (p + 2) → Wire n) (hinj : Function.Injective inWires)
    (rAnc : QRegister (p + 1) n) (hdisj : ∀ t, inWires t ∉ rAnc.image) :
    (t : ℕ) → t ≤ p + 1 → List (SymTempAndStep n)
  | 0, _ => []
  | t + 1, ht =>
      ladderPrefix negIn inWires hinj rAnc hdisj t (by omega) ++
        [ladderStepAt negIn inWires hinj rAnc hdisj ⟨t, ht⟩]
theorem ladderPrefix_length {p : ℕ} (negIn : Bool) (inWires : Fin (p + 2) → Wire n)
    (hinj : Function.Injective inWires) (rAnc : QRegister (p + 1) n)
    (hdisj : ∀ t, inWires t ∉ rAnc.image) (t : ℕ) (ht : t ≤ p + 1) :
    (ladderPrefix negIn inWires hinj rAnc hdisj t ht).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [ladderPrefix, ih (by omega)]
def ladderSteps {p : ℕ} (negIn : Bool) (inWires : Fin (p + 2) → Wire n)
    (hinj : Function.Injective inWires) (rAnc : QRegister (p + 1) n)
    (hdisj : ∀ t, inWires t ∉ rAnc.image) : List (SymTempAndStep n) := ladderPrefix negIn
    inWires hinj rAnc hdisj (p + 1) le_rfl
@[simp] theorem ladderSteps_length {p : ℕ} (negIn : Bool) (inWires : Fin (p + 2) → Wire n)
    (hinj : Function.Injective inWires) (rAnc : QRegister (p + 1) n)
    (hdisj : ∀ t, inWires t ∉ rAnc.image) : (ladderSteps negIn inWires hinj rAnc hdisj).length
    = p + 1 := ladderPrefix_length negIn inWires hinj rAnc hdisj (p + 1) le_rfl
private theorem litAnd_chain_step {m m_scr : ℕ} (rScr : QRegister m_scr n)
    (offset : ℕ) (hoff : offset + m ≤ m_scr) (rAnc : QRegister m n)
    (hrAnc : rAnc = rScr.slice offset m hoff) (M : Finset (Wire n))
    (hdisj_scr_M : Disjoint rScr.image M) (inW : Fin (m + 1) → Wire n)
    (hinj : Function.Injective inW) (hin_M : ∀ u, inW u ∉ M)
    (hin_later : ∀ u (j : Fin m_scr), offset ≤ j.val → inW u ≠ rScr j)
    (t : ℕ) (ht : t < m) (Lt : List (SymTempAndStep n)) (hlen_t : Lt.length = t)
    (hval_t : ValidSymStepList M rScr offset Lt) (pol0 polB polOut : Bool)
    (st : SymTempAndStep n)
    (hst :
      let aW := if t = 0 then inW 0 else rAnc ⟨t - 1, by omega⟩
      let bW := inW ⟨t + 1, by omega⟩
      let ancW := rAnc ⟨t, ht⟩
      ∀ (hab : aW ≠ bW) (ha : aW ≠ ancW) (hb : bW ≠ ancW),
        st = litAndSymStep (if t = 0 then pol0 else false) polB polOut aW bW ancW hab ha hb) :
    ValidSymStepList M rScr offset (Lt ++ [st]) ∧
    ∀ β : BitAssignment n,
      (∀ w, w ∉ rAnc.image → symStepFwdList Lt β w = β w) →
      (∀ j : Fin m, t ≤ j.val → symStepFwdList Lt β (rAnc j) = 0) →
      (∀ w, w ∉ rAnc.image → symStepFwdList (Lt ++ [st]) β w = β w) ∧
      (∀ j : Fin m, t + 1 ≤ j.val → symStepFwdList (Lt ++ [st]) β (rAnc j) = 0) ∧
      symStepFwdList (Lt ++ [st]) β (rAnc ⟨t, ht⟩) =
        polBit polOut
          ((if t = 0 then polBit pol0 (β (inW 0))
            else polBit false (symStepFwdList Lt β (rAnc ⟨t - 1, by omega⟩))) *
           polBit polB (β (inW ⟨t + 1, by omega⟩))) := by
  have hin_anc : ∀ u, inW u ∉ rAnc.image := fun u hm ↦ by
    rcases (QRegister.mem_image rAnc _).mp hm with ⟨v, hv⟩
    rw [hrAnc, QRegister.slice_apply] at hv
    exact hin_later u ⟨offset + v.val, by omega⟩ (by dsimp; omega) hv.symm
  have hab : (if t = 0 then inW 0 else rAnc ⟨t - 1, by omega⟩) ≠ inW ⟨t + 1, by omega⟩ := by
    split_ifs with ht0
    · exact hinj.ne (fun h ↦ by simpa using congrArg Fin.val h)
    · exact (QRegister.ne_apply_of_not_mem_image rAnc _ (hin_anc _) _).symm
  have ha : (if t = 0 then inW 0 else rAnc ⟨t - 1, by omega⟩) ≠ rAnc ⟨t, ht⟩ := by
    split_ifs with ht0
    · exact QRegister.ne_apply_of_not_mem_image rAnc _ (hin_anc 0) ⟨t, ht⟩
    · exact fun h ↦ by have hv := congrArg Fin.val (rAnc.wires.injective h); dsimp at hv; omega
  have hb : inW ⟨t + 1, by omega⟩ ≠ rAnc ⟨t, ht⟩ :=
    QRegister.ne_apply_of_not_mem_image rAnc _ (hin_anc _) ⟨t, ht⟩
  obtain rfl := hst hab ha hb
  have hanc_M : ∀ u : Fin m, rAnc u ∉ M := fun u ↦ by
    refine Finset.disjoint_left.mp hdisj_scr_M ?_
    rw [hrAnc]
    exact QRegister.image_compose_subset rScr _
      (QRegister.mem_image (rScr.slice offset m hoff) _ |>.mpr ⟨u, rfl⟩)
  have hdisj_st_M : Disjoint (litAndSymStep (if t = 0 then pol0 else false) polB polOut
      (if t = 0 then inW 0 else rAnc ⟨t - 1, by omega⟩)
      (inW ⟨t + 1, by omega⟩) (rAnc ⟨t, ht⟩) hab ha hb).S M := by
    rw [Finset.disjoint_left]
    intro w hw
    simp only [litAndSymStep, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · split_ifs with ht0
      · exact hin_M 0
      · exact hanc_M _
    · exact hin_M _
    · exact hanc_M _
  have hlat_st : ∀ j : Fin m_scr, offset + t < j.val →
      rScr j ∉ (litAndSymStep (if t = 0 then pol0 else false) polB polOut
        (if t = 0 then inW 0 else rAnc ⟨t - 1, by omega⟩)
        (inW ⟨t + 1, by omega⟩) (rAnc ⟨t, ht⟩) hab ha hb).S := by
    intro j hj hmem
    simp only [litAndSymStep, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · split_ifs at h1 with ht0
      · exact hin_later 0 j (by omega) h1.symm
      · rw [hrAnc, QRegister.slice_apply] at h1
        have hv := congrArg Fin.val (rScr.wires.injective h1); dsimp at hv; omega
    · exact hin_later _ j (by omega) h1.symm
    · rw [hrAnc, QRegister.slice_apply] at h1
      have hv := congrArg Fin.val (rScr.wires.injective h1); dsimp at hv; omega
  have hanc_eq : (litAndSymStep (if t = 0 then pol0 else false) polB polOut
      (if t = 0 then inW 0 else rAnc ⟨t - 1, by omega⟩)
      (inW ⟨t + 1, by omega⟩) (rAnc ⟨t, ht⟩) hab ha hb).anc =
      rScr ⟨offset + t, by omega⟩ := by
    dsimp only [litAndSymStep]
    rw [hrAnc, QRegister.slice_apply]
  have hval_all : ValidSymStepList M rScr offset
      (Lt ++ [litAndSymStep (if t = 0 then pol0 else false) polB polOut
        (if t = 0 then inW 0 else rAnc ⟨t - 1, by omega⟩)
        (inW ⟨t + 1, by omega⟩) (rAnc ⟨t, ht⟩) hab ha hb]) := by
    rw [validSymStepList_append, hlen_t]
    exact ⟨hval_t, ⟨by omega, hanc_eq, hdisj_st_M, hlat_st, trivial⟩⟩
  refine ⟨hval_all, fun β hout_t hzero_t ↦ ?_⟩
  let γ := symStepFwdList Lt β
  have hfwd_eq : symStepFwdList
      (Lt ++ [litAndSymStep (if t = 0 then pol0 else false) polB polOut
        (if t = 0 then inW 0 else rAnc ⟨t - 1, by omega⟩)
        (inW ⟨t + 1, by omega⟩) (rAnc ⟨t, ht⟩) hab ha hb]) β =
      Function.update γ (rAnc ⟨t, ht⟩)
        (polBit polOut
          (polBit (if t = 0 then pol0 else false)
            (γ (if t = 0 then inW 0 else rAnc ⟨t - 1, by omega⟩)) *
           polBit polB (γ (inW ⟨t + 1, by omega⟩)))) := by
    rw [symStepFwdList_append]
    exact litAndSymStep_stepFwd _ _ _ _ _ _ hab ha hb γ (hzero_t ⟨t, ht⟩ le_rfl)
  rw [hfwd_eq]
  refine ⟨fun w hw ↦ ?_, fun j hj ↦ ?_, ?_⟩
  · rw [Function.update_of_ne (fun h ↦ hw (QRegister.mem_image rAnc w |>.mpr ⟨⟨t, ht⟩, h.symm⟩))]
    exact hout_t w hw
  · have hne : rAnc j ≠ rAnc ⟨t, ht⟩ := fun h ↦ by
      have hv := congrArg Fin.val (rAnc.wires.injective h); dsimp at hv; omega
    rw [Function.update_of_ne hne]
    exact hzero_t j (by omega)
  · rw [Function.update_self]
    dsimp only [γ]
    rw [hout_t (inW ⟨t + 1, by omega⟩) (hin_anc _)]
    split_ifs with ht0
    · rw [hout_t (inW 0) (hin_anc 0)]
    · rfl
theorem fieldValidSteps_spec {b : ℕ} (hb : 0 < b) (isOffsetZero : Bool)
    (rField : QRegister (b + 1) n) {m_scr : ℕ} (rScr : QRegister m_scr n)
    (offset : ℕ) (hoff : offset + b ≤ m_scr) (M : Finset (Wire n))
    (hdisj_field_M : Disjoint rField.image M) (hdisj_scr_M : Disjoint rScr.image M)
    (hdisj_field_scr : rField.DisjointWires rScr) :
    let rAnc := rScr.slice offset b hoff
    let hdisj : rField.DisjointWires rAnc := hdisj_field_scr.compose_right _
    let L := fieldValidSteps isOffsetZero rField rAnc hdisj
    ValidSymStepList M rScr offset L ∧
    (∀ β : BitAssignment n, (∀ j : Fin b, β (rAnc j) = 0) →
      (∀ w, w ∉ rAnc.image → symStepFwdList L β w = β w) ∧
      symStepFwdList L β (rAnc ⟨b - 1, by omega⟩) =
        if fieldValidBool isOffsetZero rField β then 1 else 0) := by
  intro rAnc hdisj L
  change ValidSymStepList M rScr offset (fieldValidPrefix isOffsetZero rField rAnc hdisj b le_rfl) ∧
    _
  have hin_M : ∀ u, rField u ∉ M := fun u ↦
    Finset.disjoint_left.mp hdisj_field_M (QRegister.mem_image rField _ |>.mpr ⟨u, rfl⟩)
  have hpref : ∀ (t : ℕ) (ht : t ≤ b),
      let Lt := fieldValidPrefix isOffsetZero rField rAnc hdisj t ht
      ValidSymStepList M rScr offset Lt ∧
      ∀ β : BitAssignment n, (∀ j : Fin b, β (rAnc j) = 0) →
        (∀ w, w ∉ rAnc.image → symStepFwdList Lt β w = β w) ∧
        (∀ j : Fin b, t ≤ j.val → symStepFwdList Lt β (rAnc j) = 0) ∧
        (0 < t → t < b →
          (symStepFwdList Lt β (rAnc ⟨t - 1, by omega⟩) = 1 ↔
            ∀ u : Fin (b + 1), u.val ≤ t → β (rField u) = 0)) ∧
        (t = b →
          symStepFwdList Lt β (rAnc ⟨b - 1, by omega⟩) =
            if fieldValidBool isOffsetZero rField β then 1 else 0) := by
    intro t; induction t with
    | zero =>
        intro _
        exact ⟨trivial, fun _ h0 ↦ ⟨fun _ _ ↦ rfl, fun j _ ↦ h0 j,
          fun hpos _ ↦ absurd hpos (Nat.not_lt_zero 0),
          fun htb ↦ absurd (htb ▸ hb) (Nat.not_lt_zero 0)⟩⟩
    | succ t ih =>
        intro ht
        obtain ⟨hval_t, hsem_t⟩ := ih (by omega)
        let st := fieldValidStepAt isOffsetZero rField rAnc hdisj ⟨t, ht⟩
        obtain ⟨hval_all, hstep⟩ := litAnd_chain_step rScr offset hoff rAnc rfl M
          hdisj_scr_M rField.wires rField.wires.injective hin_M
          (fun u j _ ↦ hdisj_field_scr.ne u j) t ht _
          (fieldValidPrefix_length isOffsetZero rField rAnc hdisj t (by omega)) hval_t
          true (!decide (t + 1 = b) || isOffsetZero) (decide (t + 1 = b)) st
          (fun _ _ _ ↦ by
            by_cases ht0 : t = 0
            · simp only [st, fieldValidStepAt, ht0, ↓reduceDIte, ↓reduceIte, Fin.succ]
            · simp only [st, fieldValidStepAt, ht0, ↓reduceDIte, ↓reduceIte, Fin.succ])
        refine ⟨hval_all, fun β h0 ↦ ?_⟩
        obtain ⟨hout_t, hzero_t, hmid_t, _⟩ := hsem_t β h0
        obtain ⟨hout_s, hzero_s, hcur⟩ := hstep β hout_t hzero_t
        refine ⟨hout_s, hzero_s, fun _ hlt_b ↦ ?_, fun htb ↦ ?_⟩
        · have hne_end : t + 1 ≠ b := by omega
          have hidx_t : (⟨(t + 1) - 1, by omega⟩ : Fin b) = ⟨t, ht⟩ := Fin.ext (by dsimp)
          dsimp only [fieldValidPrefix]; rw [hidx_t, hcur]
          simp only [hne_end, decide_false, Bool.not_false, Bool.true_or]
          by_cases ht0 : t = 0
          · subst ht0; simp only [↓reduceIte]
            rw [(by decide : ∀ x y : ZMod 2, polBit false (polBit true x * polBit true y) = 1 ↔
              x = 0 ∧ y = 0)]
            exact ⟨fun ⟨h0f, h1f⟩ u hu ↦ by
              rcases (by omega : u.val = 0 ∨ u.val = 1) with hu0 | hu1
              · exact (Fin.ext (by simpa using hu0) : u = 0) ▸ h0f
              · exact (Fin.ext hu1 : u = ⟨1, by omega⟩) ▸ h1f,
              fun hall ↦ ⟨hall 0 (by dsimp; omega), hall ⟨1, by omega⟩ (by dsimp; omega)⟩⟩
          · simp only [ht0, ↓reduceIte]
            rw [(by decide : ∀ x y : ZMod 2, polBit false (polBit false x * polBit true y) = 1 ↔
              x = 1 ∧ y = 0), hmid_t (by omega) (by omega)]
            exact ⟨fun ⟨hp, hc⟩ u hu ↦ by
              rcases (by omega : u.val ≤ t ∨ u.val = t + 1) with hle | heq
              · exact hp u hle
              · exact (Fin.ext heq : u = ⟨t + 1, by omega⟩) ▸ hc,
              fun hall ↦ ⟨fun u hu ↦ hall u (by omega), hall ⟨t + 1, by omega⟩ le_rfl⟩⟩
        · have hidx : (⟨b - 1, by omega⟩ : Fin b) = ⟨t, ht⟩ := Fin.ext (by dsimp; omega)
          dsimp only [fieldValidPrefix]; rw [hidx, hcur]
          simp only [htb, decide_true, Bool.not_true, Bool.false_or]
          by_cases ht0 : t = 0
          · subst ht0
            obtain rfl : b = 1 := by omega
            simp only [↓reduceIte]
            have hdec : decide (∀ u : Fin 1, β (rField u.castSucc) = 0) =
                decide (β (rField 0) = 0) :=
              decide_eq_decide.mpr ⟨fun h ↦ h 0, fun h u ↦ by fin_cases u; exact h⟩
            rw [(by decide : ∀ (inv : Bool) (x y : ZMod 2),
              polBit true (polBit true x * polBit inv y) =
                if (!(decide (x = 0) && decide (polBit inv y = 1))) then 1 else 0)]
            exact congrArg (fun c : Bool ↦ if c then (1 : ZMod 2) else 0)
              (by unfold fieldValidBool; rw [hdec])
          · subst htb
            simp only [ht0, ↓reduceIte]
            have hprev_iff : (symStepFwdList
                (fieldValidPrefix isOffsetZero rField rAnc hdisj t (by omega)) β
                (rAnc ⟨t - 1, by omega⟩) = 1) ↔
                (∀ u : Fin (t + 1), β (rField u.castSucc) = 0) :=
              (hmid_t (by omega) (by omega)).trans
                ⟨fun h u ↦ h u.castSucc (by dsimp; omega), fun h u hu ↦ h ⟨u.val, by omega⟩⟩
            have hdec : decide (symStepFwdList
                (fieldValidPrefix isOffsetZero rField rAnc hdisj t (by omega)) β
                (rAnc ⟨t - 1, by omega⟩) = 1) =
                decide (∀ u : Fin (t + 1), β (rField u.castSucc) = 0) :=
              decide_eq_decide.mpr hprev_iff
            rw [(by decide : ∀ (inv : Bool) (x y : ZMod 2),
              polBit true (polBit false x * polBit inv y) =
                if (!(decide (x = 1) && decide (polBit inv y = 1))) then 1 else 0)]
            exact congrArg (fun c : Bool ↦ if c then (1 : ZMod 2) else 0)
              (by unfold fieldValidBool; rw [hdec])
  obtain ⟨hv, hs⟩ := hpref b le_rfl
  exact ⟨hv, fun β h0 ↦ ⟨(hs β h0).1, (hs β h0).2.2.2 rfl⟩⟩
theorem ladderSteps_spec {p : ℕ} (negIn : Bool)
    (inWires : Fin (p + 2) → Wire n) (hinj : Function.Injective inWires)
    {m_scr : ℕ} (rScr : QRegister m_scr n) (offset : ℕ) (hoff : offset + (p + 1) ≤ m_scr)
    (M : Finset (Wire n)) (hin_M : ∀ t, inWires t ∉ M) (hdisj_scr_M : Disjoint rScr.image M)
    (hin_later : ∀ t (j : Fin m_scr), offset ≤ j.val → inWires t ≠ rScr j) :
    let rAnc := rScr.slice offset (p + 1) hoff
    let hdisj : ∀ t, inWires t ∉ rAnc.image := by
      intro t hmem; rcases (QRegister.mem_image rAnc _).mp hmem with ⟨u, hu⟩
      exact hin_later t ⟨offset + u.val, by omega⟩ (by dsimp; omega) hu.symm
    let L := ladderSteps negIn inWires hinj rAnc hdisj
    ValidSymStepList M rScr offset L ∧
    (∀ β : BitAssignment n, (∀ j : Fin (p + 1), β (rAnc j) = 0) →
      (∀ w, w ∉ rAnc.image → symStepFwdList L β w = β w) ∧
      symStepFwdList L β (rAnc ⟨p, by omega⟩) =
        if (∀ t : Fin (p + 2), polBit negIn (β (inWires t)) = 1) then 1 else 0) := by
  intro rAnc hdisj L
  change ValidSymStepList M rScr offset (ladderPrefix negIn inWires hinj rAnc hdisj (p +
    1) le_rfl) ∧ _
  have hpref : ∀ (t : ℕ) (ht : t ≤ p + 1),
      let Lt := ladderPrefix negIn inWires hinj rAnc hdisj t ht
      ValidSymStepList M rScr offset Lt ∧
      ∀ β : BitAssignment n, (∀ j : Fin (p + 1), β (rAnc j) = 0) →
        (∀ w, w ∉ rAnc.image → symStepFwdList Lt β w = β w) ∧
        (∀ j : Fin (p + 1), t ≤ j.val → symStepFwdList Lt β (rAnc j) = 0) ∧
        (0 < t →
          (symStepFwdList Lt β (rAnc ⟨t - 1, by omega⟩) = 1 ↔
            ∀ u : Fin (p + 2), u.val ≤ t → polBit negIn (β (inWires u)) = 1)) := by
    intro t; induction t with
    | zero =>
        intro _; exact ⟨trivial, fun _ h0 ↦ ⟨fun _ _ ↦ rfl, fun j _ ↦ h0 j,
          fun hpos ↦ absurd hpos (Nat.not_lt_zero 0)⟩⟩
    | succ t ih =>
        intro ht
        obtain ⟨hval_t, hsem_t⟩ := ih (by omega)
        let st := ladderStepAt negIn inWires hinj rAnc hdisj ⟨t, ht⟩
        obtain ⟨hval_all, hstep⟩ := litAnd_chain_step (m := p + 1) rScr offset hoff
          rAnc rfl M hdisj_scr_M inWires hinj hin_M hin_later t ht _
          (ladderPrefix_length negIn inWires hinj rAnc hdisj t (by omega)) hval_t
          negIn negIn false st
          (fun _ _ _ ↦ by
            by_cases ht0 : t = 0
            · simp only [st, ladderStepAt, ht0, ↓reduceDIte, ↓reduceIte, Fin.succ]
            · simp only [st, ladderStepAt, ht0, ↓reduceDIte, ↓reduceIte, Fin.succ])
        refine ⟨hval_all, fun β h0 ↦ ?_⟩
        obtain ⟨hout_t, hzero_t, hmid_t⟩ := hsem_t β h0
        obtain ⟨hout_s, hzero_s, hcur⟩ := hstep β hout_t hzero_t
        refine ⟨hout_s, hzero_s, fun _ ↦ ?_⟩
        have hidx_t : (⟨(t + 1) - 1, by omega⟩ : Fin (p + 1)) = ⟨t, ht⟩ := Fin.ext (by dsimp)
        dsimp only [ladderPrefix]; rw [hidx_t, hcur]
        by_cases ht0 : t = 0
        · subst ht0; simp only [↓reduceIte]
          rw [(by decide : ∀ (inv : Bool) (x y : ZMod 2),
            polBit false (polBit inv x * polBit inv y) = 1 ↔
              polBit inv x = 1 ∧ polBit inv y = 1)]
          exact ⟨fun ⟨h0f, h1f⟩ u hu ↦ by
            rcases (by omega : u.val = 0 ∨ u.val = 1) with hu0 | hu1
            · exact (Fin.ext (by simpa using hu0) : u = 0) ▸ h0f
            · exact (Fin.ext hu1 : u = ⟨1, by omega⟩) ▸ h1f,
            fun hall ↦ ⟨hall 0 (Nat.zero_le _), hall ⟨1, by omega⟩ (by simp)⟩⟩
        · simp only [ht0, ↓reduceIte]
          rw [(by decide : ∀ (inv : Bool) (x y : ZMod 2),
            polBit false (polBit false x * polBit inv y) = 1 ↔
              x = 1 ∧ polBit inv y = 1), hmid_t (by omega)]
          exact ⟨fun ⟨hp, hc⟩ u hu ↦ by
            rcases (by omega : u.val ≤ t ∨ u.val = t + 1) with hle | heq
            · exact hp u hle
            · exact (Fin.ext heq : u = ⟨t + 1, by omega⟩) ▸ hc,
            fun hall ↦ ⟨fun u hu ↦ hall u (by omega), hall ⟨t + 1, by omega⟩ le_rfl⟩⟩
  obtain ⟨hv, hs⟩ := hpref (p + 1) le_rfl
  refine ⟨hv, fun β h0 ↦ ⟨(hs β h0).1, ?_⟩⟩
  have h1 : (symStepFwdList (ladderPrefix negIn inWires hinj rAnc hdisj (p + 1) le_rfl) β
      (rAnc ⟨p, by omega⟩) = 1) ↔ ∀ t : Fin (p + 2), polBit negIn (β (inWires t)) = 1 := by
    have hp_idx : (⟨(p + 1) - 1, by omega⟩ : Fin (p + 1)) = ⟨p, by omega⟩ := Fin.ext (by dsimp)
    exact hp_idx ▸ ((hs β h0).2.2 (by omega)).trans
      ⟨fun h t ↦ h t (by omega), fun h u _ ↦ h u⟩
  change symStepFwdList (ladderPrefix negIn inWires hinj rAnc hdisj (p + 1) le_rfl) β
    (rAnc ⟨p, by omega⟩) = _
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1)
      (symStepFwdList (ladderPrefix negIn inWires hinj rAnc hdisj (p + 1) le_rfl)
        β (rAnc ⟨p, by omega⟩)) with hz0 | hz1
  · rw [ite_eq_right (fun hh ↦ by rw [h1.mpr hh] at hz0; exact absurd hz0 (by decide))]; exact hz0
  · rw [ite_eq_left (h1.mp hz1)]; exact hz1
structure ScratchFlagProducer {m_scr : ℕ} (rScr : QRegister m_scr n) (M : Finset (Wire n))
    (offset : ℕ) where
  len : ℕ
  hlen : 0 < len
  hfit : offset + len ≤ m_scr
  steps : List (SymTempAndStep n)
  steps_len : steps.length = len
  pred : BitAssignment n → Bool
  pred_indep_scr : ∀ β₁ β₂, (∀ w, w ∉ rScr.image → β₁ w = β₂ w) → pred β₁ = pred β₂
  valid : ValidSymStepList M rScr offset steps
  spec : ∀ β : BitAssignment n,
    (∀ j : Fin len, β (rScr.slice offset len hfit j) = 0) →
    (∀ w, w ∉ (rScr.slice offset len hfit).image → symStepFwdList steps β w = β w) ∧
    symStepFwdList steps β (rScr ⟨offset + len - 1, by omega⟩) = if pred β then 1 else 0
def fieldFlagProducer {b m_scr : ℕ} (hb : 0 < b) (isOffsetZero : Bool)
    (rField : QRegister (b + 1) n) (rScr : QRegister m_scr n) (M : Finset (Wire n))
    (offset : ℕ) (hoff : offset + b ≤ m_scr) (hdisj_field_M : Disjoint rField.image M)
    (hdisj_scr_M : Disjoint rScr.image M) (hdisj_field_scr : rField.DisjointWires rScr) :
    ScratchFlagProducer rScr M offset :=
  let rAnc := rScr.slice offset b hoff
  let hdisj : rField.DisjointWires rAnc := hdisj_field_scr.compose_right _
  let hspec := fieldValidSteps_spec hb isOffsetZero rField rScr offset hoff M
    hdisj_field_M hdisj_scr_M hdisj_field_scr
  { len := b
    hlen := hb
    hfit := hoff
    steps := fieldValidSteps isOffsetZero rField rAnc hdisj
    steps_len := fieldValidSteps_length isOffsetZero rField rAnc hdisj
    pred := fieldValidBool isOffsetZero rField
    pred_indep_scr := by
      intro β₁ β₂ hagree
      have hf : ∀ u : Fin (b + 1), β₁ (rField u) = β₂ (rField u) :=
        fun u ↦ hagree (rField u) (hdisj_field_scr.apply_not_mem_right u)
      simp only [fieldValidBool, hf]
    valid := hspec.1
    spec := fun β h0 ↦ by
      obtain ⟨hout, hlast⟩ := hspec.2 β h0
      refine ⟨hout, ?_⟩
      have hidx : rScr ⟨offset + b - 1, by omega⟩ = rAnc ⟨b - 1, by omega⟩ := by
        simp only [rAnc, QRegister.slice_apply]
        apply congrArg rScr.wires
        ext; dsimp; omega
      rw [hidx, hlast] }
def uniformFieldsChain {b m_scr : ℕ} (hb : 0 < b) (isOffsetZero : Bool)
    (M : Finset (Wire n)) (rScr : QRegister m_scr n)
    (hdisj_scr_M : Disjoint rScr.image M) :
    (c : ℕ) → (fields : Fin c → QRegister (b + 1) n) →
    (hfit : c * b ≤ m_scr) →
    (hdisj_M : ∀ i, Disjoint (fields i).image M) →
    (hdisj_scr : ∀ i, (fields i).DisjointWires rScr) →
    List (SymTempAndStep n)
  | 0, _, _, _, _ => []
  | c + 1, fields, hfit, hdisj_M, hdisj_scr =>
      uniformFieldsChain hb isOffsetZero M rScr hdisj_scr_M c
        (fun i ↦ fields i.castSucc) (by nlinarith)
        (fun i ↦ hdisj_M i.castSucc) (fun i ↦ hdisj_scr i.castSucc) ++
      (fieldFlagProducer hb isOffsetZero (fields ⟨c, by omega⟩) rScr M (c * b)
        (by nlinarith) (hdisj_M _) hdisj_scr_M (hdisj_scr _)).steps
theorem uniformFieldsChain_length {b m_scr : ℕ} (hb : 0 < b) (isOffsetZero : Bool)
    (M : Finset (Wire n)) (rScr : QRegister m_scr n) (hdisj_scr_M : Disjoint rScr.image M)
    (c : ℕ) (fields : Fin c → QRegister (b + 1) n) (hfit : c * b ≤ m_scr)
    (hdisj_M : ∀ i, Disjoint (fields i).image M)
    (hdisj_scr : ∀ i, (fields i).DisjointWires rScr) : (uniformFieldsChain hb isOffsetZero M
    rScr hdisj_scr_M c fields hfit hdisj_M hdisj_scr).length = c * b := by
  induction c with
  | zero => simp [uniformFieldsChain]
  | succ c ih =>
      rw [uniformFieldsChain, List.length_append, ih]
      dsimp only [fieldFlagProducer]
      rw [fieldValidSteps_length]
      ring
theorem flagIdx_lt {i b c : ℕ} (hb : 0 < b) (hi : i < c) : i * b + (b - 1) < c * b := by
  calc i * b + (b - 1) < i * b + b := by omega
    _ = (i + 1) * b := by ring
    _ ≤ c * b := Nat.mul_le_mul_right b hi
theorem uniformFieldsChain_spec {b m_scr : ℕ} (hb : 0 < b) (isOffsetZero : Bool)
    (M : Finset (Wire n)) (rScr : QRegister m_scr n)
    (hdisj_scr_M : Disjoint rScr.image M)
    (c : ℕ) (fields : Fin c → QRegister (b + 1) n)
    (hfit : c * b ≤ m_scr)
    (hdisj_M : ∀ i, Disjoint (fields i).image M)
    (hdisj_scr : ∀ i, (fields i).DisjointWires rScr) :
    let L := uniformFieldsChain hb isOffsetZero M rScr hdisj_scr_M c fields hfit hdisj_M hdisj_scr
    ValidSymStepList M rScr 0 L ∧
    ∀ β : BitAssignment n,
      (∀ u : Fin (c * b), β ((rScr.slice 0 (c * b) (by omega)) u) = 0) →
      (∀ w, w ∉ (rScr.slice 0 (c * b) (by omega)).image → symStepFwdList L β w = β w) ∧
      (∀ i : Fin c,
        symStepFwdList L β
          (rScr ⟨i.val * b + (b - 1), lt_of_lt_of_le (flagIdx_lt hb i.isLt) hfit⟩) =
          if fieldValidBool isOffsetZero (fields i) β then 1 else 0) := by
  dsimp only
  induction c with
  | zero =>
      refine ⟨trivial, fun _ _ ↦ ⟨fun _ _ ↦ rfl, fun i ↦ i.elim0⟩⟩
  | succ c ih =>
      have hcb_le : c * b ≤ m_scr := le_trans (Nat.mul_le_mul_right b (Nat.le_succ c)) hfit
      obtain ⟨hval_c, hsem_c⟩ := ih (fun i ↦ fields i.castSucc) hcb_le
        (fun i ↦ hdisj_M i.castSucc) (fun i ↦ hdisj_scr i.castSucc)
      let P := fieldFlagProducer hb isOffsetZero (fields ⟨c, by omega⟩) rScr M (c * b)
        (by nlinarith) (hdisj_M _) hdisj_scr_M (hdisj_scr _)
      have hlen_c := uniformFieldsChain_length hb isOffsetZero M rScr hdisj_scr_M c
        (fun i ↦ fields i.castSucc) hcb_le
        (fun i ↦ hdisj_M i.castSucc) (fun i ↦ hdisj_scr i.castSucc)
      have hvalid_all : ValidSymStepList M rScr 0 (uniformFieldsChain hb isOffsetZero M rScr
          hdisj_scr_M (c + 1) fields hfit hdisj_M hdisj_scr) := by
        dsimp only [uniformFieldsChain]
        rw [validSymStepList_append, Nat.zero_add, hlen_c]
        exact ⟨hval_c, P.valid⟩
      refine ⟨hvalid_all, fun β h0 ↦ ?_⟩
      have h0_c : ∀ u : Fin (c * b), β ((rScr.slice 0 (c * b) (by omega)) u) = 0 :=
        fun u ↦ by
          simpa only [QRegister.slice_apply] using
            h0 ⟨u.val, lt_of_lt_of_le u.isLt (Nat.mul_le_mul_right b (Nat.le_succ c))⟩
      obtain ⟨hout_c, hflags_c⟩ := hsem_c β h0_c
      let γ := symStepFwdList (uniformFieldsChain hb isOffsetZero M rScr hdisj_scr_M c (fun i
          ↦ fields i.castSucc) hcb_le (fun i ↦ hdisj_M i.castSucc) (fun i ↦ hdisj_scr
          i.castSucc)) β
      have hγ0 : ∀ j : Fin P.len, γ (rScr.slice (c * b) P.len P.hfit j) = 0 := by
        intro j
        have hnot_c : rScr.slice (c * b) P.len P.hfit j ∉
            (rScr.slice 0 (c * b) (by omega)).image := by
          intro hm
          rcases (QRegister.mem_image _ _).mp hm with ⟨u, hu⟩
          simp only [QRegister.slice_apply] at hu
          have hv := congrArg Fin.val (rScr.wires.injective hu)
          dsimp at hv; omega
        dsimp only [γ]
        rw [hout_c _ hnot_c, QRegister.slice_apply]
        have hj_lt : c * b + j.val < (c + 1) * b := by
          have hj : j.val < b := j.isLt
          calc c * b + j.val < c * b + b := by omega
            _ = (c + 1) * b := by ring
        simpa only [QRegister.slice_apply, zero_add] using h0 ⟨c * b + j.val, hj_lt⟩
      obtain ⟨hout_P, hflag_P⟩ := P.spec γ hγ0
      have happ : symStepFwdList (uniformFieldsChain hb isOffsetZero M rScr hdisj_scr_M (c +
          1) fields hfit hdisj_M hdisj_scr) β = symStepFwdList P.steps γ := by
        dsimp only [uniformFieldsChain]; rw [symStepFwdList_append]
      rw [happ]
      refine ⟨?_, ?_⟩
      · intro w hw
        have hw_P : w ∉ (rScr.slice (c * b) P.len P.hfit).image := by
          intro hm
          rcases (QRegister.mem_image _ _).mp hm with ⟨u, rfl⟩
          have hu_lt : c * b + u.val < (c + 1) * b := by
            have hu : u.val < b := u.isLt
            calc c * b + u.val < c * b + b := by omega
              _ = (c + 1) * b := by ring
          exact hw ((QRegister.mem_image _ _).mpr
            ⟨⟨c * b + u.val, hu_lt⟩, congrArg rScr.wires (Fin.ext (by dsimp; omega))⟩)
        have hw_c : w ∉ (rScr.slice 0 (c * b) (by omega)).image := by
          intro hm; rcases (QRegister.mem_image _ _).mp hm with ⟨u, rfl⟩
          exact hw ((QRegister.mem_image _ _).mpr
            ⟨⟨u.val, lt_of_lt_of_le u.isLt (Nat.mul_le_mul_right b (Nat.le_succ c))⟩,
              congrArg rScr.wires (Fin.ext (by dsimp))⟩)
        rw [hout_P w hw_P]
        exact hout_c w hw_c
      · intro i
        rcases (by omega : i.val < c ∨ i.val = c) with hlt | heq
        · have hbound_i : i.val * b + (b - 1) < c * b := flagIdx_lt hb hlt
          have hnot_sub : rScr ⟨i.val * b + (b - 1), lt_of_lt_of_le (flagIdx_lt hb i.isLt) hfit⟩ ∉
              (rScr.slice (c * b) P.len P.hfit).image := by
            intro hm
            rcases (QRegister.mem_image _ _).mp hm with ⟨u, hu⟩
            rw [QRegister.slice_apply] at hu
            have hv := congrArg Fin.val (rScr.wires.injective hu)
            dsimp [P, fieldFlagProducer] at hv
            omega
          rw [hout_P _ hnot_sub]
          exact hflags_c ⟨i.val, hlt⟩
        · have hi_eq : i = ⟨c, by omega⟩ := by ext; exact heq
          have hout_c_full : ∀ w, w ∉ rScr.image → γ w = β w :=
            fun w hw ↦ hout_c w (fun hm ↦ hw (QRegister.image_compose_subset rScr _ hm))
          rw [P.pred_indep_scr γ β hout_c_full] at hflag_P
          have hidx_eq : (⟨i.val * b + (b - 1), lt_of_lt_of_le (flagIdx_lt hb i.isLt) hfit⟩ :
              Fin m_scr) =
              ⟨c * b + P.len - 1, lt_of_lt_of_le
                (by
                  dsimp [P, fieldFlagProducer];
                  have hmul : c * b + b = (c + 1) * b := (by ring); omega) hfit⟩ := by
            ext; dsimp [P, fieldFlagProducer]; rw [heq]; omega
          rw [hidx_eq, hflag_P]
          dsimp only [P, fieldFlagProducer]
          rw [hi_eq]; rfl
def uniformFieldsChainAt {b m_scr : ℕ} (hb : 0 < b) (isOffsetZero : Bool)
    (M : Finset (Wire n)) (rScr : QRegister m_scr n) (offset : ℕ)
    (hdisj_scr_M : Disjoint rScr.image M) (c : ℕ) (fields : Fin c → QRegister (b + 1) n)
    (hfit : offset + c * b ≤ m_scr) (hdisj_M : ∀ i, Disjoint (fields i).image M)
    (hdisj_scr : ∀ i, (fields i).DisjointWires rScr) : List (SymTempAndStep n) :=
  let rSub := rScr.slice offset (c * b) hfit
  have hsub_M : Disjoint rSub.image M :=
    Finset.disjoint_of_subset_left (QRegister.image_compose_subset rScr _) hdisj_scr_M
  uniformFieldsChain hb isOffsetZero M rSub hsub_M c fields le_rfl hdisj_M
    (fun i ↦ (hdisj_scr i).compose_right _)
theorem uniformFieldsChainAt_length {b m_scr : ℕ} (hb : 0 < b) (isOffsetZero : Bool)
    (M : Finset (Wire n)) (rScr : QRegister m_scr n) (offset : ℕ)
    (hdisj_scr_M : Disjoint rScr.image M) (c : ℕ) (fields : Fin c → QRegister (b + 1) n)
    (hfit : offset + c * b ≤ m_scr) (hdisj_M : ∀ i, Disjoint (fields i).image M)
    (hdisj_scr : ∀ i, (fields i).DisjointWires rScr) : (uniformFieldsChainAt hb isOffsetZero M
    rScr offset hdisj_scr_M c fields hfit hdisj_M hdisj_scr).length = c * b :=
    uniformFieldsChain_length hb isOffsetZero M _ _ c fields le_rfl hdisj_M _
lemma validSymStepList_of_slice {M : Finset (Wire n)} {m_scr m_sub : ℕ}
    (rScr : QRegister m_scr n) (offset : ℕ) (hoff : offset + m_sub ≤ m_scr)
    (L : List (SymTempAndStep n)) (o : ℕ) (ho : o + L.length ≤ m_sub)
    (hval : ValidSymStepList M (rScr.slice offset m_sub hoff) o L)
    (hnot_after : ∀ s ∈ L, ∀ j : Fin m_scr, offset + m_sub ≤ j.val → rScr j ∉ s.S) :
    ValidSymStepList M rScr (offset + o) L := by
  induction L generalizing o with
  | nil => exact trivial
  | cons s rest ih =>
      rcases hval with ⟨hlt, hanc, hdisj, hlat, hrest⟩
      refine ⟨by omega, ?_, hdisj, ?_, ?_⟩
      · rw [hanc]; exact QRegister.slice_apply rScr offset m_sub hoff ⟨o, hlt⟩
      · intro j hj
        rcases (by omega : j.val < offset + m_sub ∨ offset + m_sub ≤ j.val) with hlt_end | hge_end
        · have hj_eq : rScr j = (rScr.slice offset m_sub hoff) ⟨j.val - offset, by omega⟩ := by
            simp only [QRegister.slice_apply]
            apply congrArg rScr.wires
            ext; dsimp; omega
          rw [hj_eq]
          exact hlat ⟨j.val - offset, by omega⟩ (by dsimp; omega)
        · exact hnot_after s (by simp) j hge_end
      · rw [show offset + o + 1 = offset + (o + 1) by omega]
        exact ih (o + 1) (by rw [List.length_cons] at ho; omega) hrest
          (fun s' hs' ↦ hnot_after s' (List.mem_cons_of_mem s hs'))
lemma mem_uniformFieldsChain_S {b m_sub : ℕ} (hb : 0 < b) (isOffsetZero : Bool)
    (M : Finset (Wire n)) (rSub : QRegister m_sub n) (hsub_M : Disjoint rSub.image M) :
    ∀ (c : ℕ) (fields : Fin c → QRegister (b + 1) n) (hfit : c * b ≤ m_sub)
      (hdisj_M : ∀ i, Disjoint (fields i).image M)
      (hdisj_scr : ∀ i, (fields i).DisjointWires rSub)
      (s : SymTempAndStep n),
      s ∈ uniformFieldsChain hb isOffsetZero M rSub hsub_M c fields hfit hdisj_M hdisj_scr →
      s.S ⊆ rSub.image ∪ Finset.biUnion Finset.univ (fun i ↦ (fields i).image)
  | 0, _, _, _, _, _, hs => by simp [uniformFieldsChain] at hs
  | c + 1, fields, hfit, hdisj_M, hdisj_scr, s, hs => by
      dsimp only [uniformFieldsChain] at hs
      rcases List.mem_append.mp hs with hs1 | hs2
      · intro w hw
        have hmem := mem_uniformFieldsChain_S hb isOffsetZero M rSub hsub_M c
          (fun i ↦ fields i.castSucc) (by nlinarith)
          (fun i ↦ hdisj_M i.castSucc) (fun i ↦ hdisj_scr i.castSucc) s hs1 hw
        rcases Finset.mem_union.mp hmem with hsub | hbi
        · exact Finset.mem_union_left _ hsub
        · rcases Finset.mem_biUnion.mp hbi with ⟨i, _, hi⟩
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨i.castSucc, Finset.mem_univ _, hi⟩)
      · intro w hw
        dsimp only [fieldFlagProducer, fieldValidSteps] at hs2
        have hpref_mem : ∀ (t : ℕ) (ht : t ≤ b),
            s ∈ fieldValidPrefix isOffsetZero (fields ⟨c, by omega⟩)
              (rSub.slice (c * b) b (by nlinarith))
              ((hdisj_scr _).compose_right _) t ht →
            ∃ j : Fin b, s = fieldValidStepAt isOffsetZero (fields ⟨c, by omega⟩)
              (rSub.slice (c * b) b (by nlinarith))
              ((hdisj_scr _).compose_right _) j := by
          intro t
          induction t with
          | zero => intro _ hm; simp [fieldValidPrefix] at hm
          | succ t iht =>
              intro ht hm
              dsimp only [fieldValidPrefix] at hm
              rcases List.mem_append.mp hm with hm1 | hm2
              · exact iht (by omega) hm1
              · simp only [List.mem_singleton] at hm2
                exact ⟨⟨t, ht⟩, hm2⟩
        rcases hpref_mem b le_rfl hs2 with ⟨j, rfl⟩
        have hF (idx : Fin (b + 1)) : (fields ⟨c, by omega⟩) idx ∈
            rSub.image ∪ Finset.biUnion Finset.univ (fun i ↦ (fields i).image) :=
          Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨⟨c, by omega⟩, Finset.mem_univ _,
              (QRegister.mem_image _ _).mpr ⟨idx, rfl⟩⟩)
        have hR (idx : Fin b) : (rSub.slice (c * b) b (by nlinarith)) idx ∈
            rSub.image ∪ Finset.biUnion Finset.univ (fun i ↦ (fields i).image) :=
          Finset.mem_union_left _
            (QRegister.image_compose_subset rSub _ ((QRegister.mem_image _ _).mpr ⟨idx, rfl⟩))
        dsimp only [fieldValidStepAt] at hw
        split_ifs at hw with hj0
        · simp only [litAndSymStep, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact hF 0
          · exact hF _
          · exact hR _
        · simp only [litAndSymStep, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact hR _
          · exact hF _
          · exact hR _
theorem uniformFieldsChainAt_spec {b m_scr : ℕ} (hb : 0 < b) (isOffsetZero : Bool)
    (M : Finset (Wire n)) (rScr : QRegister m_scr n)
    (offset : ℕ) (hdisj_scr_M : Disjoint rScr.image M)
    (c : ℕ) (fields : Fin c → QRegister (b + 1) n)
    (hfit : offset + c * b ≤ m_scr)
    (hdisj_M : ∀ i, Disjoint (fields i).image M)
    (hdisj_scr : ∀ i, (fields i).DisjointWires rScr) :
    let L := uniformFieldsChainAt hb isOffsetZero M rScr offset hdisj_scr_M c fields hfit
      hdisj_M hdisj_scr
    ValidSymStepList M rScr offset L ∧
    ∀ β : BitAssignment n, (∀ u : Fin (c * b), β ((rScr.slice offset (c * b) hfit) u) = 0) →
      (∀ w, w ∉ (rScr.slice offset (c * b) hfit).image → symStepFwdList L β w = β w) ∧
      (∀ i : Fin c,
        symStepFwdList L β
          (rScr ⟨offset + (i.val * b + (b - 1)), by
            have h1 : i.val * b + (b - 1) < (i.val + 1) * b := by
              calc i.val * b + (b - 1) < i.val * b + b := by omega
                _ = (i.val + 1) * b := by ring
            have h2 : (i.val + 1) * b ≤ c * b := Nat.mul_le_mul_right b i.isLt
            omega⟩) =
          if fieldValidBool isOffsetZero (fields i) β then 1 else 0) := by
  dsimp only
  let rSub := rScr.slice offset (c * b) hfit
  have hsub_M : Disjoint rSub.image M :=
    Finset.disjoint_of_subset_left (QRegister.image_compose_subset rScr _) hdisj_scr_M
  obtain ⟨hval_sub, hsem_sub⟩ := uniformFieldsChain_spec hb isOffsetZero M rSub hsub_M c fields
    le_rfl hdisj_M (fun i ↦ (hdisj_scr i).compose_right _)
  have hval : ValidSymStepList M rScr offset (uniformFieldsChainAt hb isOffsetZero M rScr
      offset hdisj_scr_M c fields hfit hdisj_M hdisj_scr) := by
    have hv := validSymStepList_of_slice rScr offset hfit _ 0
      (by rw [Nat.zero_add, uniformFieldsChain_length]) hval_sub ?_
    · dsimp only [uniformFieldsChainAt]
      simpa [Nat.add_zero] using hv
    · intro s hs j hj hmem
      have hsub := mem_uniformFieldsChain_S hb isOffsetZero M rSub hsub_M c fields le_rfl
        hdisj_M _ s hs hmem
      rcases Finset.mem_union.mp hsub with hr | hf
      · rcases (QRegister.mem_image rSub _).mp hr with ⟨u, hu⟩
        rw [QRegister.slice_apply] at hu
        have hv2 := congrArg Fin.val (rScr.wires.injective hu)
        dsimp at hv2; omega
      · rcases Finset.mem_biUnion.mp hf with ⟨i, _, hi⟩
        rcases (QRegister.mem_image _ _).mp hi with ⟨u, hu⟩
        exact (hdisj_scr i).ne u j hu
  refine ⟨hval, fun β h0 ↦ ?_⟩
  have h0_sub : ∀ u : Fin (c * b), β ((rSub.slice 0 (c * b) (by omega)) u) = 0 :=
    fun u ↦ by rw [QRegister.slice_apply]; simpa only [zero_add] using h0 u
  obtain ⟨hout_sub, hflags⟩ := hsem_sub β h0_sub
  have hout : ∀ w, w ∉ rSub.image → symStepFwdList (uniformFieldsChain hb isOffsetZero M rSub
      hsub_M c fields le_rfl hdisj_M (fun i ↦ (hdisj_scr i).compose_right _)) β w = β w := fun
      w hw ↦ hout_sub w (fun hm ↦ hw (QRegister.image_compose_subset rSub _ hm))
  dsimp only [uniformFieldsChainAt]
  refine ⟨hout, fun i ↦ ?_⟩
  have hbound_i : i.val * b + (b - 1) < c * b := flagIdx_lt hb i.isLt
  have hidx : rScr ⟨offset + (i.val * b + (b - 1)), by
      have h1 : i.val * b + (b - 1) < (i.val + 1) * b := by
        calc i.val * b + (b - 1) < i.val * b + b := by omega
          _ = (i.val + 1) * b := by ring
      have h2 : (i.val + 1) * b ≤ c * b := Nat.mul_le_mul_right b i.isLt
      omega⟩ =
      rSub ⟨i.val * b + (b - 1), hbound_i⟩ :=
    (QRegister.slice_apply rScr offset (c * b) hfit ⟨i.val * b + (b - 1), hbound_i⟩).symm
  rw [hidx]
  exact hflags i
end PebbledGuardGeneric
section PebbledChunkHelpers
variable {Var : Type} {n : ℕ}
theorem count_symWrapDynList_toff (v : Var) (L : List (SymTempAndStep n))
    (inner : DynamicCircuit Var n) (hinner : inner.count .TOFF = 0) :
    (symWrapDynList v L inner).count .TOFF = 0 := by
  rw [symWrapDynList_count_TOFF, hinner]
theorem count_symWrapDynList_t (v : Var) (L : List (SymTempAndStep n))
    (inner : DynamicCircuit Var n) : (symWrapDynList v L inner).count .T = 4 * L.length +
    inner.count .T := symWrapDynList_count_T v L inner
end PebbledChunkHelpers
section StoppingPowerGridGuard
variable {Var : Type} {n : ℕ}
lemma mod_two_pow_eq_zero_iff_testBit :
    ∀ (b f : ℕ), f % 2 ^ b = 0 ↔ ∀ u : Fin b, f.testBit u.val = false
  | 0, f => by simp [Nat.mod_one]
  | b + 1, f => by
      constructor
      · intro h u
        have htb : (f % 2 ^ (b + 1)).testBit u.val = false := by simp [h]
        simpa [Nat.testBit_mod_two_pow, u.isLt] using htb
      · intro hall
        have h0 : f % 2 = 0 := by
          have hzero := hall 0
          rcases Nat.mod_two_eq_zero_or_one f with h | h <;>
            simp [Nat.testBit_zero, h] at hzero
          exact h
        have hdiv : (f / 2) % 2 ^ b = 0 := by
          rw [mod_two_pow_eq_zero_iff_testBit b (f / 2)]
          intro u
          have := hall u.succ
          rwa [Fin.val_succ, Nat.testBit_succ] at this
        obtain ⟨q, hq⟩ : 2 ^ b ∣ f / 2 := Nat.dvd_of_mod_eq_zero hdiv
        have hf : f = 2 ^ (b + 1) * q := by
          have := Nat.div_add_mod f 2
          rw [pow_succ']
          linarith
        simp [hf]
def electronFieldLinearIdx (f : Fin 654) (u : Fin 6) : Fin systemQubits :=
  ⟨6 * f.val + u.val, by have := f.isLt; have := u.isLt; change _ < 3948; omega⟩
def projectileFieldLinearIdx (w : Fin 3) (u : Fin 8) : Fin systemQubits :=
  ⟨3924 + 8 * w.val + u.val, by have := w.isLt; have := u.isLt; change _ < 3948; omega⟩
theorem disjointWires_singleton_of_not_mem {k : ℕ} (r : QRegister k n) (g : Wire n)
    (hg : g ∉ r.image) : r.DisjointWires (QRegister.singleton g) :=
  QRegister.disjoint_iff.mpr fun i _ ↦ (QRegister.ne_apply_of_not_mem_image r g hg i).symm
theorem disjointWires_concat_left {k₁ k₂ m : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    {s : QRegister m n} (h₁₂ : r₁.DisjointWires r₂) (h₁ : r₁.DisjointWires s)
    (h₂ : r₂.DisjointWires s) : (r₁.concat r₂ h₁₂).DisjointWires s :=
  QRegister.disjoint_iff.mpr fun i j ↦ by
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
    cases x with
    | inl i₁ =>
        simp only [finSumFinEquiv_apply_left, QRegister.concat_apply_left]
        exact h₁.ne i₁ j
    | inr i₂ =>
        simp only [finSumFinEquiv_apply_right, QRegister.concat_apply_right]
        exact h₂.ne i₂ j
def guardCenterProjFields (rSys : QRegister systemQubits n) (w : Fin 3) : QRegister 8 n :=
  rSys.slice (3924 + 8 * w.val) 8 (by have hw : w.val < 3 := w.isLt; change _ ≤ 3948; omega)
attribute [irreducible] fieldValidSteps ladderSteps uniformFieldsChain uniformFieldsChainAt
noncomputable def projGridAncZero (k m_be : ℕ) (P : Operator (2 ^ k)) : Operator (2 ^ (k + m_be)) :=
  let sys : QRegister k (k + m_be) := .block 0 k (by omega)
  let anc : QRegister m_be (k + m_be) := .block k m_be le_rfl
  sys.embedMatrix P * anc.basisOutcomeProjector 0
noncomputable def singleRBEReflNegMatrix (k m_be : ℕ) (P : Operator (2 ^ k)) : Operator
    (2 ^ (k + m_be)) := 1 - (2 : ℂ) • projGridAncZero k m_be P
theorem projGridAncZero_isHermitian (k m_be : ℕ) {P : Operator (2 ^ k)} (hP_herm : P.IsHermitian) :
    (projGridAncZero k m_be P).IsHermitian := by
  let sys : QRegister k (k + m_be) := .block 0 k (by omega)
  let anc : QRegister m_be (k + m_be) := .block k m_be le_rfl
  have hdisj : sys.DisjointWires anc :=
    QRegister.block_disjoint_of_le 0 k k m_be (by omega) le_rfl (by omega)
  have hcomm := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint sys) anc hdisj P 0
  change (sys.embedMatrix P * anc.basisOutcomeProjector 0)ᴴ =
    sys.embedMatrix P * anc.basisOutcomeProjector 0
  rw [conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose,
    ← sys.embedMatrix_conjTranspose, hP_herm.eq, hcomm]
theorem projGridAncZero_idem (k m_be : ℕ) {P : Operator (2 ^ k)} (hP_idem : P * P = P) :
    projGridAncZero k m_be P * projGridAncZero k m_be P = projGridAncZero k m_be P := by
  let sys : QRegister k (k + m_be) := .block 0 k (by omega)
  let anc : QRegister m_be (k + m_be) := .block k m_be le_rfl
  have hdisj : sys.DisjointWires anc :=
    QRegister.block_disjoint_of_le 0 k k m_be (by omega) le_rfl (by omega)
  have hcomm := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint sys) anc hdisj P 0
  have h00 : anc.basisOutcomeProjector 0 * anc.basisOutcomeProjector 0 =
      anc.basisOutcomeProjector 0 := basisOutcomeProjector_idem_local anc 0
  change (sys.embedMatrix P * anc.basisOutcomeProjector 0) *
      (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
    sys.embedMatrix P * anc.basisOutcomeProjector 0
  calc (sys.embedMatrix P * anc.basisOutcomeProjector 0) *
        (sys.embedMatrix P * anc.basisOutcomeProjector 0)
      = sys.embedMatrix P * (anc.basisOutcomeProjector 0 * sys.embedMatrix P) *
          anc.basisOutcomeProjector 0 := by noncomm_ring
    _ = (sys.embedMatrix P * sys.embedMatrix P) *
          (anc.basisOutcomeProjector 0 * anc.basisOutcomeProjector 0) := by
          rw [← hcomm]; noncomm_ring
    _ = sys.embedMatrix P * anc.basisOutcomeProjector 0 := by
          rw [← sys.embedMatrix_mul, hP_idem, h00]
noncomputable def singleRBEReflNegUnitary (k m_be : ℕ) (P : Operator (2 ^ k))
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P) : Unitary (2 ^ (k + m_be)) :=
  ⟨singleRBEReflNegMatrix k m_be P, by
    have heq : singleRBEReflNegMatrix k m_be P = -guardReflMatrix (projGridAncZero k m_be P) := by
      unfold singleRBEReflNegMatrix guardReflMatrix
      abel
    rw [heq, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_neg,
      guardReflMatrix_conjTranspose (projGridAncZero_isHermitian k m_be hP_herm), neg_mul_neg]
    exact guardReflMatrix_mul_self (projGridAncZero_idem k m_be hP_idem)⟩
theorem singleRBEReflNegUnitary_mulVec_single {k m_be : ℕ} (P : Operator (2 ^ k))
    (Pred : Fin (2 ^ k) → Prop) [DecidablePred Pred] (hP_herm : P.IsHermitian)
    (hP_idem : P * P = P) (hP_diag : ∀ u, P u u = if Pred u then (1 : ℂ) else 0)
    (hP_off : ∀ u v, u ≠ v → P u v = 0) (l : Fin (2 ^ (k + m_be))) :
    (singleRBEReflNegUnitary k m_be P hP_herm hP_idem).1.mulVec (Pi.single l 1) = (if
    (QRegister.block k m_be le_rfl).extractIndex l = 0 ∧ Pred ((QRegister.block 0 k
    (by omega)).extractIndex l) then (-1 : ℂ) else 1) • Pi.single l 1 := by
  funext y
  change (singleRBEReflNegMatrix k m_be P).mulVec (Pi.single l 1) y = _
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
  dsimp only [singleRBEReflNegMatrix, projGridAncZero]
  rw [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal]
  by_cases hyl : y = l
  · subst hyl
    simp only [↓reduceIte]
    by_cases ha0 : (QRegister.block k m_be le_rfl).extractIndex y = 0
    · rw [ite_eq_left ha0, QRegister.embedMatrix_apply, ite_eq_left rfl,
        hP_diag ((QRegister.block 0 k (by omega)).extractIndex y)]
      by_cases hv : Pred ((QRegister.block 0 k (by omega)).extractIndex y)
      · rw [ite_eq_left hv, ite_eq_left ⟨ha0, hv⟩]; norm_num
      · rw [ite_eq_right hv, ite_eq_right (fun h ↦ hv h.2)]; norm_num
    · rw [ite_eq_right ha0, ite_eq_right (fun h ↦ ha0 h.1), QRegister.embedMatrix_apply,
        mul_zero, mul_zero, sub_zero]
  · simp only [hyl, ↓reduceIte]
    by_cases ha0 : (QRegister.block k m_be le_rfl).extractIndex l = 0
    · rw [ite_eq_left ha0, QRegister.embedMatrix_apply]
      by_cases hsplit : ((QRegister.block 0 k (by omega)).basisSplitEquiv y).2 =
          ((QRegister.block 0 k (by omega)).basisSplitEquiv l).2
      · rw [ite_eq_left hsplit]
        have hex_ne : (QRegister.block 0 k (by omega)).extractIndex y ≠
            (QRegister.block 0 k (by omega)).extractIndex l := fun hex ↦
          hyl ((QRegister.block 0 k (by omega)).basisSplitEquiv.injective (Prod.ext hex hsplit))
        rw [hP_off _ _ hex_ne]; norm_num
      · rw [ite_eq_right hsplit]; norm_num
    · rw [ite_eq_right ha0, QRegister.embedMatrix_apply, mul_zero, mul_zero, sub_zero]
end StoppingPowerGridGuard
end ConfigGridGuard654Refl
set_option maxRecDepth 2000
end GridGuard654ReflAux
end
end ModGridGuard654Refl

section ModParametricMulKickAndSlopePG
public section
namespace ParametricMulKickAndSlopePG
open Operator Matrix QProg HermitianMat Real SpecsAux
open SpecsAux.PhaseGradCatalystCore
open InPlaceFullAddSlice
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
section SlopePGAlgebra
noncomputable def turnPow2 (W : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * (k : ℂ) / (2 ^ W : ℂ))
theorem turnPow2_add (W : ℕ) (a b : ℤ) :
    turnPow2 W (a + b) = turnPow2 W a * turnPow2 W b := by
  unfold turnPow2
  rw [← Complex.exp_add]
  congr 1; push_cast; ring
theorem turnPow2_add_period (W : ℕ) (a q : ℤ) :
    turnPow2 W (a + q * (2 ^ W : ℤ)) = turnPow2 W a := by
  unfold turnPow2
  have hne : ((2 : ℂ) ^ W) ≠ 0 := pow_ne_zero W (by norm_num)
  have hsplit : 2 * π * Complex.I * ((a + q * (2 ^ W : ℤ) : ℤ) : ℂ) / (2 ^ W : ℂ) = 2 * π *
      Complex.I * (a : ℂ) / (2 ^ W : ℂ) + (q : ℂ) * (2 * π * Complex.I) := by
    push_cast; field_simp [hne]
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem turnPow2_eq_of_emod_eq (W : ℕ) {a b : ℤ} (h : a % (2 ^ W : ℤ) = b % (2 ^ W : ℤ)) :
    turnPow2 W a = turnPow2 W b := by
  have ha : a = a % (2 ^ W : ℤ) + (a / (2 ^ W : ℤ)) * (2 ^ W : ℤ) := by
    linarith [Int.emod_add_mul_ediv a (2 ^ W : ℤ)]
  have hb : b = b % (2 ^ W : ℤ) + (b / (2 ^ W : ℤ)) * (2 ^ W : ℤ) := by
    linarith [Int.emod_add_mul_ediv b (2 ^ W : ℤ)]
  calc turnPow2 W a
      = turnPow2 W (a % (2 ^ W : ℤ) + (a / (2 ^ W : ℤ)) * (2 ^ W : ℤ)) := by rw [← ha]
    _ = turnPow2 W (a % (2 ^ W : ℤ)) := turnPow2_add_period W _ _
    _ = turnPow2 W (b % (2 ^ W : ℤ)) := by rw [h]
    _ = turnPow2 W (b % (2 ^ W : ℤ) + (b / (2 ^ W : ℤ)) * (2 ^ W : ℤ)) :=
          (turnPow2_add_period W _ _).symm
    _ = turnPow2 W b := by rw [← hb]
theorem turnPow2_scale_pow (a b : ℕ) (k : ℤ) :
    turnPow2 (a + b) ((2 ^ a : ℤ) * k) = turnPow2 b k := by
  unfold turnPow2
  congr 1
  have hne : ((2 : ℂ) ^ a) ≠ 0 := pow_ne_zero a (by norm_num)
  rw [pow_add]
  push_cast; field_simp [hne]
def sysCatEquiv (kSys W : ℕ) :
    Fin (2 ^ (kSys + W)) ≃ BitAssignment kSys × Fin (2 ^ W) :=
  (basisBitsEquiv (kSys + W)).trans
    { toFun := fun f ↦
        (fun i ↦ f (Fin.castAdd W i),(basisBitsEquiv W).symm (fun j ↦ f (Fin.natAdd kSys j)))
      invFun := fun p ↦ Fin.addCases p.1 (basisBits W p.2)
      left_inv := fun f ↦ by
        funext idx
        refine Fin.addCases (fun _ ↦ by simp) (fun _ ↦ by simp) idx
      right_inv := fun ⟨γ, m⟩ ↦ by
        ext i <;> simp }
@[simp]
theorem basisBits_sysCatEquiv_symm (kSys W : ℕ) (γ : BitAssignment kSys) (m : Fin (2 ^ W)) :
    basisBits (kSys + W) ((sysCatEquiv kSys W).symm (γ, m)) =
      Fin.addCases γ (basisBits W m) := by
  have h : ((fun i ↦ basisBits (kSys + W) ((sysCatEquiv kSys W).symm (γ, m)) (Fin.castAdd W
      i)), (basisBitsEquiv W).symm (fun j' ↦ basisBits (kSys + W) ((sysCatEquiv kSys W).symm
      (γ, m)) (Fin.natAdd kSys j'))) = (γ, m) := (sysCatEquiv kSys W).apply_symm_apply (γ, m)
  funext idx
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · rw [Fin.addCases_left]
    exact congrFun (congrArg Prod.fst h) i
  · rw [Fin.addCases_right]
    have h2 : (fun j' ↦ basisBits (kSys + W) ((sysCatEquiv kSys W).symm (γ, m)) (Fin.natAdd
        kSys j')) = (basisBitsEquiv W) m := (basisBitsEquiv W).symm_apply_eq.mp
        (congrArg Prod.snd h)
    exact congrFun h2 j
def sysCatShiftPerm (kSys W : ℕ) (Δ : BitAssignment kSys → ℕ) :
    Equiv.Perm (Fin (2 ^ (kSys + W))) :=
  let inner : Equiv.Perm (BitAssignment kSys × Fin (2 ^ W)) :=
    { toFun := fun p ↦ (p.1, ⟨(p.2.val + Δ p.1) % 2 ^ W, Nat.mod_lt _ (by positivity)⟩)
      invFun := fun p ↦
        (p.1, ⟨(p.2.val + (2 ^ W - Δ p.1 % 2 ^ W)) % 2 ^ W, Nat.mod_lt _ (by positivity)⟩)
      left_inv := fun ⟨γ, y⟩ ↦ by
        ext
        · rfl
        · have hM : 0 < 2 ^ W := by positivity
          have hd : Δ γ % 2 ^ W < 2 ^ W := Nat.mod_lt _ hM
          have hsub : Δ γ % 2 ^ W + (2 ^ W - Δ γ % 2 ^ W) = 2 ^ W := Nat.add_sub_of_le hd.le
          have hdiv : (Δ γ / 2 ^ W) * 2 ^ W + Δ γ % 2 ^ W = Δ γ := Nat.div_add_mod' (Δ γ) (2 ^ W)
          have heq_sum : y.val + Δ γ + (2 ^ W - Δ γ % 2 ^ W) =
              (y.val + 2 ^ W) + (Δ γ / 2 ^ W) * 2 ^ W := by linarith
          dsimp only
          rw [Nat.mod_add_mod, heq_sum, Nat.add_mul_mod_self_right, Nat.add_mod_right,
            Nat.mod_eq_of_lt y.isLt]
      right_inv := fun ⟨γ, y⟩ ↦ by
        ext
        · rfl
        · have hM : 0 < 2 ^ W := by positivity
          have hd : Δ γ % 2 ^ W < 2 ^ W := Nat.mod_lt _ hM
          calc ((y.val + (2 ^ W - Δ γ % 2 ^ W)) % 2 ^ W + Δ γ) % 2 ^ W
              = (y.val + (2 ^ W - Δ γ % 2 ^ W) + Δ γ % 2 ^ W) % 2 ^ W := by
                  rw [Nat.mod_add_mod, Nat.add_mod_mod]
            _ = (y.val + 2 ^ W) % 2 ^ W := by congr 1; omega
            _ = y.val := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt] }
  (sysCatEquiv kSys W).trans (inner.trans (sysCatEquiv kSys W).symm)
@[simp] theorem sysCatEquiv_sysCatShiftPerm (kSys W : ℕ) (Δ : BitAssignment kSys → ℕ)
    (col : Fin (2 ^ (kSys + W))) : sysCatEquiv kSys W (sysCatShiftPerm kSys W Δ col) =
    ((sysCatEquiv kSys W col).1, ⟨((sysCatEquiv kSys W col).2.val + Δ (sysCatEquiv kSys W
    col).1) % 2 ^ W, Nat.mod_lt _ (by positivity)⟩) := by
  simp [sysCatShiftPerm]
noncomputable def catShiftUnitary (kSys W : ℕ) (Δ : BitAssignment kSys → ℕ) :
    Unitary (2 ^ (kSys + W)) :=
  ⟨Matrix.of fun row col ↦ if sysCatShiftPerm kSys W Δ col = row then 1 else 0, by
    rw [Matrix.mem_unitaryGroup_iff']
    ext col₁ col₂
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    by_cases h : col₁ = col₂
    · subst h
      rw [Finset.sum_eq_single (sysCatShiftPerm kSys W Δ col₁)]
      · simp [Matrix.star_apply]
      · intro row _ hne
        have hne' : sysCatShiftPerm kSys W Δ col₁ ≠ row := fun e ↦ hne e.symm
        simp [hne']
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun row _ ↦ ?_
      by_cases hr : sysCatShiftPerm kSys W Δ col₁ = row
      · have hr2 : sysCatShiftPerm kSys W Δ col₂ ≠ row := fun e ↦
          h ((sysCatShiftPerm kSys W Δ).injective (hr.trans e.symm))
        simp [hr, hr2]
      · simp [hr]⟩
@[simp] theorem catShiftUnitary_apply (kSys W : ℕ) (Δ : BitAssignment kSys → ℕ)
    (row col : Fin (2 ^ (kSys + W))) : (catShiftUnitary kSys W Δ).1 row col = if
    sysCatShiftPerm kSys W Δ col = row then 1 else 0 := rfl
theorem embedUnitary_catShiftUnitary_mulVec_ket {n kSys W : ℕ}
    (rSys : QRegister kSys n) (rPG : QRegister W n) (hdisj : rSys.DisjointWires rPG)
    (Δ : BitAssignment kSys → ℕ) (β : BitAssignment n) :
    let rAct := rSys.concat rPG hdisj
    let γ : BitAssignment kSys := fun i ↦ β (rSys i)
    let mNext : Fin (2 ^ W) := ⟨(regVal rPG β + Δ γ) % 2 ^ W, Nat.mod_lt _ (by positivity)⟩
    (rAct.embedUnitary (catShiftUnitary kSys W Δ)).1.mulVec (ket β) =
      ket (basisBits n (rPG.replaceIndex ((basisBitsEquiv n).symm β) mNext)) := by
  intro rAct γ mNext
  let gIdx := (basisBitsEquiv n).symm β
  have hext_act : sysCatEquiv kSys W (rAct.extractIndex gIdx) =
      (γ, rPG.extractIndex gIdx) := by
    ext i
    · change basisBits (kSys + W) (rAct.extractIndex gIdx) (Fin.castAdd W i) = β (rSys i)
      rw [rAct.basisBits_extractIndex, QRegister.concat_apply_left]
      exact congrFun ((basisBitsEquiv n).apply_symm_apply β) (rSys i)
    · have hbits : (fun j ↦ (basisBitsEquiv (kSys + W)) (rAct.extractIndex gIdx)
          (Fin.natAdd kSys j)) = (basisBitsEquiv W) (rPG.extractIndex gIdx) := by
        funext j
        change basisBits (kSys + W) (rAct.extractIndex gIdx) (Fin.natAdd kSys j) =
          basisBits W (rPG.extractIndex gIdx) j
        rw [rAct.basisBits_extractIndex, rPG.basisBits_extractIndex, QRegister.concat_apply_right]
      change ((basisBitsEquiv W).symm (fun j ↦ _)).val = (rPG.extractIndex gIdx).val
      rw [hbits, (basisBitsEquiv W).symm_apply_apply]
  have hm_eq : (rPG.extractIndex gIdx).val = regVal rPG β :=
    (regVal_eq_extractIndex_val rPG β).symm
  have hlocal : (catShiftUnitary kSys W Δ).1.mulVec (Pi.single (rAct.extractIndex gIdx) 1) =
      Pi.single (sysCatShiftPerm kSys W Δ (rAct.extractIndex gIdx)) 1 := by
    funext row
    rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single (rAct.extractIndex gIdx)
      (fun c hc ↦ by simp [hc])]
    simp only [Pi.single_apply, ↓reduceIte, mul_one, catShiftUnitary_apply]
    by_cases h : sysCatShiftPerm kSys W Δ (rAct.extractIndex gIdx) = row
    · subst h; simp
    · have h' : row ≠ sysCatShiftPerm kSys W Δ (rAct.extractIndex gIdx) := fun e ↦ h e.symm
      simp [h, h']
  have hrep_eq : rAct.replaceIndex gIdx (sysCatShiftPerm kSys W Δ (rAct.extractIndex gIdx)) =
      rPG.replaceIndex gIdx mNext := by
    apply (basisBitsEquiv n).injective
    funext w
    change basisBits n (rAct.replaceIndex gIdx _) w = basisBits n (rPG.replaceIndex gIdx mNext) w
    have hshift_bits : ∀ idx,
        basisBits (kSys + W) (sysCatShiftPerm kSys W Δ (rAct.extractIndex gIdx)) idx =
          Fin.addCases γ (basisBits W mNext) idx := by
      intro idx
      have hsymm : sysCatEquiv kSys W (sysCatShiftPerm kSys W Δ (rAct.extractIndex gIdx)) =
          (γ, mNext) := by
        rw [sysCatEquiv_sysCatShiftPerm, hext_act]
        ext
        · rfl
        · dsimp only [mNext]; rw [hm_eq]
      have h2 := congrArg (sysCatEquiv kSys W).symm hsymm
      rw [Equiv.symm_apply_apply] at h2
      rw [h2]
      exact congrFun (basisBits_sysCatEquiv_symm kSys W γ mNext) idx
    by_cases hwAct : w ∈ Set.range rAct.wires
    · rcases hwAct with ⟨idx, rfl⟩
      rw [rAct.basisBits_replaceIndex_apply, hshift_bits idx]
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · simp only [Fin.addCases_left, rAct, QRegister.concat_apply_left, γ]
        have hnotPG : rSys i ∉ Set.range rPG.wires :=
          fun hmem ↦ Set.disjoint_left.mp hdisj ⟨i, rfl⟩ hmem
        rw [rPG.basisBits_replaceIndex_of_not_mem _ _ _ hnotPG]
        exact (congrFun ((basisBitsEquiv n).apply_symm_apply β) (rSys i)).symm
      · simp only [Fin.addCases_right, rAct, QRegister.concat_apply_right,
          rPG.basisBits_replaceIndex_apply]
    · have hwNotPG : w ∉ Set.range rPG.wires := by
        rintro ⟨j, rfl⟩
        exact hwAct ⟨Fin.natAdd kSys j, QRegister.concat_apply_right rSys rPG hdisj j⟩
      rw [rAct.basisBits_replaceIndex_of_not_mem _ _ _ hwAct,
        rPG.basisBits_replaceIndex_of_not_mem _ _ _ hwNotPG]
  rw [QRegister.embedUnitary_val, ket, basisState, rAct.embedMatrix_mulVec_single_factors,
    hlocal, rAct.tensorState_single_replaceIndex, hrep_eq]
  dsimp only [ket, basisState, gIdx]
  congr 1
  exact ((basisBitsEquiv n).symm_apply_apply _).symm
end SlopePGAlgebra
section ParametricMulKick
variable {Var : Type} {n : ℕ}
theorem regVal_split_at_slice {W n : ℕ} (s b : ℕ) (hs : s + b = W) (rPG : QRegister W n)
    (β : BitAssignment n) : regVal rPG β = regVal (rPG.slice 0 s (by omega)) β + 2 ^ s *
    regVal (rPG.slice s b (by omega)) β := by
  unfold regVal bitsVal
  have hcast : W = s + b := hs.symm
  subst hcast
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Fin.val_castAdd, QRegister.slice_apply]
    have hidx : (⟨0 + i.val, by omega⟩ : Fin (s + b)) = Fin.castAdd b i := by
      ext; dsimp; omega
    rw [hidx]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Fin.val_natAdd, pow_add, QRegister.slice_apply]
    have hidx : (⟨s + j.val, by omega⟩ : Fin (s + b)) = Fin.natAdd s j := by ext; dsimp
    rw [hidx]
    ring
end ParametricMulKick
end ParametricMulKickAndSlopePG
end
end ModParametricMulKickAndSlopePG

section ModPosSlots24BranchConcrete
set_option maxRecDepth 65536
@[expose] public section
namespace PosSlots24BranchConcreteAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end PosSlots24BranchConcreteAlt
namespace PosSlots24BranchConcrete
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux.DyadicSubgridToeplitz128 (anchorParity1D anchorSubTarget1D)
open OctahedralOrbit Dyadic128CoulombMath
open CanonRank7Circuit
open MeasureBranchHadamardSem (projZeroAll ket_projZeroAll projZeroAll_conjTranspose
  RealizesCleanUnitary)
open StreamingBchComparator BchCubeDecoder
instance instNeZeroTwoPow (n : ℕ) : NeZero (2 ^ n) := ⟨(Nat.two_pow_pos n).ne'⟩
section CleanCircuitBridges
variable {Var : Type} {n : ℕ}
theorem mbh_ket_eq_ket (β : BitAssignment n) : MeasureBranchHadamardSem.ket β = ket β := by
  funext x
  simp [MeasureBranchHadamardSem.ket, ket, basisState]
theorem ket_diagonalSignUnitaryN (p : BitAssignment n → Bool) (β : BitAssignment n) :
    (diagonalSignUnitaryN p).1.mulVec (ket β) = (if p β then (-1 : ℂ) else 1) • ket β := by
  have hb_ket : (Pi.single ((basisBitsEquiv n).symm β) (1 : ℂ) : Fin (2 ^ n) → ℂ) = ket β := by
    funext x; simp [ket, basisState]
  rw [diagonalSignUnitaryN, diagonalSignUnitary, ← hb_ket, Matrix.diagonal_mulVec_single,
    show basisBits n ((basisBitsEquiv n).symm β) = β from (basisBitsEquiv n).apply_symm_apply β,
    mul_one]
  funext x
  by_cases hx : x = (basisBitsEquiv n).symm β <;> simp [hx]
theorem diagonalSignUnitaryN_conjTranspose (p : BitAssignment n → Bool) :
    (diagonalSignUnitaryN p).1ᴴ = (diagonalSignUnitaryN p).1 := by
  unfold diagonalSignUnitaryN diagonalSignUnitary
  ext r c
  by_cases hrc : r = c
  · subst hrc
    simp only [conjTranspose_apply, Matrix.diagonal_apply_eq]
    by_cases hp : p (basisBits n r) <;> simp [hp]
  · simp [conjTranspose_apply, Matrix.diagonal_apply_ne _ hrc,
      Matrix.diagonal_apply_ne _ (Ne.symm hrc)]
theorem matrix_ext_of_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  simpa only [mbh_ket_eq_ket] using h β
abbrev _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.ofFin (k : ℕ) : QRegister k k
    where
  wires := { toFun := id, inj' := Function.injective_id }
@[simp] theorem eval_identity_mulVec (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.identity : Circuit n).eval.1.mulVec ψ = ψ := by
  rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
@[simp] theorem col_one_eq_ket (β : BitAssignment n) :
    Matrix.col (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) ((basisBitsEquiv n).symm β) = ket β := by
  funext i
  simp [Matrix.col_apply, Matrix.one_apply, ket, basisState, Pi.single_apply]
@[simp] theorem support_X_eq (w : Wire n) : (Circuit.X w).support = {w} := by
  simp [Circuit.X]
@[simp] theorem support_CNOT_eq (c t : Wire n) (h : c ≠ t) : (Circuit.CNOT c t h).support =
    {c, t} := Circuit.support_cnot c t h
@[simp]
theorem support_TOFF_eq (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).support = {c₁, c₂, t} :=
  Circuit.support_toffoli c₁ c₂ t h₁₂ h₁t h₂t
theorem projZeroAll_eq_diagonal (k : ℕ) (scr : Fin k → Wire n) : projZeroAll k scr =
    Matrix.diagonal (fun x : Fin (2 ^ n) ↦ if ∀ j : Fin k, basisBits n x (scr j) = 0 then (1 :
    ℂ) else 0) := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [ket_projZeroAll, MeasureBranchHadamardSem.ket, basisState, Matrix.diagonal_mulVec_single]
  have hb : basisBits n ((basisBitsEquiv n).symm β) = β := (basisBitsEquiv n).apply_symm_apply β
  rw [hb]
  by_cases h : ∀ j : Fin k, β (scr j) = 0 <;> simp [h]
theorem regVal_congr' {k : ℕ} {r₁ r₂ : QRegister k n} {β₁ β₂ : BitAssignment n}
    (h : ∀ j : Fin k, β₁ (r₁ j) = β₂ (r₂ j)) : regVal r₁ β₁ = regVal r₂ β₂ := by
  unfold regVal bitsVal
  exact Finset.sum_congr rfl fun j _ ↦ by dsimp only; rw [h j]
theorem RealizesCleanUnitary.congr_on_clean_ket [Fintype Var] [DecidableEq Var] {mWork : ℕ}
    [NeZero (2 ^ n)] {v : Var} {f : Fin mWork → Wire n} {d : DynamicCircuit Var n}
    {U₁ U₂ : Unitary (2 ^ n)} (hd : RealizesCleanUnitary v (projZeroAll mWork f) d U₁) (hket :
    ∀ β : BitAssignment n, (∀ j : Fin mWork, β (f j) = 0) → U₁.1.mulVec (ket β) = U₂.1.mulVec
    (ket β)) : RealizesCleanUnitary v (projZeroAll mWork f) d U₂ := by
  have hP_herm : (projZeroAll mWork f)ᴴ = projZeroAll mWork f := projZeroAll_conjTranspose mWork f
  have hU_eq : U₁.1 * projZeroAll mWork f = U₂.1 * projZeroAll mWork f := by
    apply matrix_ext_of_ket
    intro β
    have hb_ket : Pi.single ((basisBitsEquiv n).symm β) (1 : ℂ) = ket β := by
      funext x; simp [ket, basisState]
    have hbits_eq : basisBits n ((basisBitsEquiv n).symm β) = β :=
      (basisBitsEquiv n).apply_symm_apply β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, projZeroAll_eq_diagonal, ← hb_ket,
      Matrix.diagonal_mulVec_single]
    simp only [hbits_eq]
    by_cases hz : ∀ j : Fin mWork, β (f j) = 0
    · rw [ite_eq_left hz, one_mul, hb_ket]
      exact hket β hz
    · simp [hz]
  exact RealizesCleanUnitary.congr_unitary hP_herm hd hU_eq
end CleanCircuitBridges
section CoreLayoutAndArithmetic
@[reducible] def posPayloadWires : ℕ := 80
@[reducible] def posCoreWires : ℕ := 4034
section CoreSlices
variable {n : ℕ}
def rElecSlot (rCore : QRegister posCoreWires n) (e : Fin 218) : QRegister 18 n :=
  rCore.slice (18 * e.val) 18 (by have := e.isLt; dsimp [posCoreWires]; omega)
def wSlot0Core (rCore : QRegister posCoreWires n) : Wire n := rCore ⟨3948, by decide⟩
def wSlot1Core (rCore : QRegister posCoreWires n) : Wire n := rCore ⟨3949, by decide⟩
def wSlot2Core (rCore : QRegister posCoreWires n) : Wire n := rCore ⟨3950, by decide⟩
def rSubPayloadCore (rCore : QRegister posCoreWires n) : QRegister 80 n :=
  rCore.slice 3954 80 (by decide)
def rCosetB1 (rCore : QRegister posCoreWires n) : QRegister 3 n :=
  (rSubPayloadCore rCore).slice 0 3 (by decide)
def rCosetB0 (rCore : QRegister posCoreWires n) : QRegister 3 n :=
  (rSubPayloadCore rCore).slice 3 3 (by decide)
def rNucIdx (rCore : QRegister posCoreWires n) : QRegister 8 n :=
  (rSubPayloadCore rCore).slice 6 8 (by decide)
def rAnchorIdx (rCore : QRegister posCoreWires n) : QRegister 8 n :=
  (rSubPayloadCore rCore).slice 14 8 (by decide)
def rPartnerIdx (rCore : QRegister posCoreWires n) : QRegister 8 n :=
  (rSubPayloadCore rCore).slice 22 8 (by decide)
def wIsHead (rCore : QRegister posCoreWires n) : Wire n :=
  (rSubPayloadCore rCore) ⟨30, by decide⟩
def wHeadThresh (rCore : QRegister posCoreWires n) : Wire n :=
  (rSubPayloadCore rCore) ⟨31, by decide⟩
def rHeadFine21 (rCore : QRegister posCoreWires n) : QRegister 21 n :=
  (rSubPayloadCore rCore).slice 32 21 (by decide)
def rTailKeep30 (rCore : QRegister posCoreWires n) : QRegister 30 n :=
  (rSubPayloadCore rCore).slice 32 30 (by decide)
def wSubReject (rCore : QRegister posCoreWires n) : Wire n :=
  (rSubPayloadCore rCore) ⟨62, by decide⟩
def wRejectZero (rCore : QRegister posCoreWires n) : Wire n :=
  (rSubPayloadCore rCore) ⟨79, by decide⟩
def axisBitRev6 (rSlot18 : QRegister 18 n) (w : Fin 3) : QRegister 6 n where
  wires :=
    { toFun := fun j ↦ rSlot18 ⟨6 * w.val + (5 - j.val), by omega⟩
      inj' := fun j₁ j₂ h ↦ by
        have hv := congrArg Fin.val (rSlot18.wires.injective h)
        ext; dsimp at hv; omega }
def slotSubGridCoord64 (rSlot18 : QRegister 18 n) (β : BitAssignment n) : SubGridCoord64 :=
  fun w ↦ ⟨regVal (axisBitRev6 rSlot18 w) β, regVal_lt_two_pow _ β⟩
def parity3OfReg (rB : QRegister 3 n) (β : BitAssignment n) : Fin 3 → Bool :=
  fun w ↦ decide (β (rB w) = 1)
theorem bitsVal_injective : ∀ {k : ℕ} {f g : BitAssignment k},
    bitsVal f = bitsVal g → f = g
  | 0, _, _, _ => funext fun i ↦ Fin.elim0 i
  | k + 1, f, g, h => by
      have hsp : ∀ δ : BitAssignment (k + 1),
          bitsVal δ = (δ 0).val + 2 * bitsVal (fun i : Fin k ↦ δ i.succ) := fun δ ↦ by
        unfold bitsVal; rw [Fin.sum_univ_succ, Finset.mul_sum]
        simp only [Fin.val_zero, _root_.pow_zero, mul_one, Fin.val_succ]
        exact congrArg ((δ 0).val + ·) (Finset.sum_congr rfl fun _ _ ↦ by rw [pow_succ']; ring)
      rw [hsp f, hsp g] at h
      have := ZMod.val_lt (f 0); have := ZMod.val_lt (g 0)
      have heq_tail := bitsVal_injective (show bitsVal (fun i : Fin k ↦ f i.succ) =
        bitsVal (fun i : Fin k ↦ g i.succ) by omega)
      funext idx; refine Fin.cases ?_ (fun i ↦ congrFun heq_tail i) idx
      exact ZMod.val_injective 2 (by omega)
theorem slotSubGridCoord64_eq_iff (rA rB : QRegister 18 n) (β₁ β₂ : BitAssignment n) :
    slotSubGridCoord64 rA β₁ = slotSubGridCoord64 rB β₂ ↔
      ∀ q : Fin 18, β₁ (rA q) = β₂ (rB q) := by
  constructor
  · intro h q
    let w : Fin 3 := ⟨q.val / 6, by omega⟩
    let j : Fin 6 := ⟨5 - q.val % 6, by omega⟩
    have hw := congrArg Fin.val (congrFun h w)
    dsimp [slotSubGridCoord64, regVal] at hw
    have hbits := bitsVal_injective hw
    have hj : β₁ (axisBitRev6 rA w j) = β₂ (axisBitRev6 rB w j) := congrFun hbits j
    have hA : axisBitRev6 rA w j = rA q := congrArg rA.wires (by ext; dsimp [w, j]; omega)
    have hB : axisBitRev6 rB w j = rB q := congrArg rB.wires (by ext; dsimp [w, j]; omega)
    rwa [hA, hB] at hj
  · intro h
    funext w
    ext
    dsimp [slotSubGridCoord64]
    exact regVal_congr' (fun j ↦ h ⟨6 * w.val + (5 - j.val), by omega⟩)
theorem regVal_slice1_eq_div2 (r7 : QRegister 7 n) (β : BitAssignment n) :
    regVal (r7.slice 1 6 (by omega)) β = regVal r7 β / 2 := by
  have rhs_split : regVal r7 β =
      (β (r7 0)).val + ∑ i : Fin 6, (β (r7 i.succ)).val * 2 ^ i.succ.val := by
    unfold regVal bitsVal
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, _root_.pow_zero, mul_one]
  have htail : (∑ i : Fin 6, (β (r7 i.succ)).val * 2 ^ i.succ.val) =
      2 * regVal (r7.slice 1 6 (by omega)) β := by
    unfold regVal bitsVal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi : r7 i.succ = (r7.slice 1 6 (by omega)) i := by
      rw [QRegister.slice_apply]; exact congrArg r7.wires (Fin.ext (by dsimp; omega))
    rw [hi, Fin.val_succ, pow_succ']; ring
  have h0lt := ZMod.val_lt (β (r7 0))
  rw [rhs_split, htail]
  omega
end CoreSlices
theorem anchorSubTarget1D_fst_val_eq (y₀ : Fin 64) (b₀ : Bool) (d : Fin 128) :
    ((anchorSubTarget1D y₀ (if b₀ then 1 else 0) d).1).val =
      (y₀.val + (((if b₀ then 1 else 0) + 128 - d.val) % 128) / 2) % 64 := by
  have hy := y₀.isLt
  have hd := d.isLt
  rw [SpecsAux.DyadicSubgridToeplitz128.anchorSubTarget1D_fst_eq_borrow]
  cases b₀ <;> dsimp <;> omega
theorem tailFineDiff1D_eq (y₀ y₁ : Fin 64) (b₀ b₁ : Bool) :
    let d : Fin 128 := ⟨(2 * y₀.val + (if b₀ then 1 else 0) + 128 -
        (2 * y₁.val + (if b₁ then 1 else 0))) % 128, Nat.mod_lt _ (by omega)⟩
    (anchorSubTarget1D y₀ (if b₀ then 1 else 0) d).1 = y₁ ∧
      anchorParity1D (if b₀ then 1 else 0) d = (if b₁ then 1 else 0) := by
  have hy0 := y₀.isLt
  have hy1 := y₁.isLt
  intro d
  constructor
  · ext
    rw [anchorSubTarget1D_fst_val_eq]
    cases b₀ <;> cases b₁ <;> dsimp [d] <;> omega
  · ext
    unfold anchorParity1D
    cases b₀ <;> cases b₁ <;> dsimp [d] <;> omega
section CombinationalGadgets
variable {n : ℕ}
@[simp] theorem count_copyXorRegCircuit_toff {k : ℕ} (rSrc rDst : QRegister k n)
    (hSD : rSrc.DisjointWires rDst) :
    (copyXorRegCircuit rSrc rDst hSD).count PrimitiveGate.TOFF = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [copyXorRegCircuit, Circuit.count_seq, ih (regInit rSrc) (regInit rDst) _]
      simp [Circuit.CNOT]
@[simp] theorem count_copyXorRegCircuit_t {k : ℕ} (rSrc rDst : QRegister k n)
    (hSD : rSrc.DisjointWires rDst) :
    (copyXorRegCircuit rSrc rDst hSD).count PrimitiveGate.T = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [copyXorRegCircuit, Circuit.count_seq, ih (regInit rSrc) (regInit rDst) _]
      simp [Circuit.CNOT]
end CombinationalGadgets
end CoreLayoutAndArithmetic
section Specification
def packTailTable31 (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (r : ℕ) : BitAssignment 31 := if hr : r <
    orbitCount47905 then fun j ↦ if j.val = 30 then if tailSign ⟨r, hr⟩ then 1 else 0 else if
    ((tailMag30 ⟨r, hr⟩).val / 2 ^ j.val) % 2 = 1 then 1 else 0 else fun _ ↦ 0
theorem packTailTable31_low30_val (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (r : Fin orbitCount47905) :
    bitsVal (fun j : Fin 30 ↦
      packTailTable31 tailSign tailMag30 r.val ⟨j.val, by omega⟩) =
      (tailMag30 r).val := by
  unfold packTailTable31 bitsVal
  simp only [r.isLt, ↓reduceDIte]
  refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans
    (_root_.QuantumComputation.Specs.StoppingPowerSolution.sum_div_two_pow_mod_two_mul_two_pow 30
      (tailMag30 r).val (tailMag30 r).isLt)
  have hjne : j.val ≠ 30 := by omega
  rcases Nat.mod_two_eq_zero_or_one ((tailMag30 r).val / 2 ^ j.val) with h | h
  · simp [hjne, h]
  · simp [hjne, h]
theorem packTailTable31_sign_bit (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (r : Fin orbitCount47905) :
    packTailTable31 tailSign tailMag30 r.val ⟨30, by omega⟩ =
      if tailSign r then 1 else 0 := by
  simp [packTailTable31, r.isLt]
def headPhaseBitSpec (β : BitAssignment posCoreWires) : Bool :=
  let rCore := QRegExt.ofFin posCoreWires
  let isPos01 := (β (wSlot2Core rCore) == 0) && (β (wSlot1Core rCore) == 1 → False)
  let isPos01B : Bool := (β (wSlot2Core rCore) == 0) && !(β (wSlot1Core rCore) == 1)
  let _ := isPos01
  let s0 := β (wSlot0Core rCore) == 1
  let nucOk := !s0 → regVal (rNucIdx rCore) β < 216
  let ancOk := regVal (rAnchorIdx rCore) β < 218
  let inB : Bool := decide nucOk && ancOk
  let enHead : Bool := isPos01B && !(β (wSubReject rCore) == 1) && inB && (β (wIsHead rCore) == 1)
  if !enHead then false
  else
    let dHead := fineCoordOfReg21 (rHeadFine21 rCore) β
    let y0 := slotSubGridCoord64 (rElecSlot rCore 0) β
    let b0 := parity3OfReg (rCosetB0 rCore) β
    let yTarget : SubGridCoord64 := fun w ↦
      if !s0 then ⟨(dHead w).val / 2, by omega⟩
      else (anchorSubTarget1D (y0 w) (if b0 w then 1 else 0) (dHead w)).1
    let hitSet : Finset (Fin 218) := Finset.univ.filter fun e ↦
      (!s0 || decide (e.val ≠ 0)) &&
        decide (slotSubGridCoord64 (rElecSlot rCore e) β = yTarget)
    let s1Zero := proj38ZeroBit hitSet
    let rZero := proj38OddXorZeroBit hitSet
    zeroParityThreshExp (!s0) (β (wHeadThresh rCore) == 1) s1Zero rZero
def tailAndSlackPhaseBitSpec (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (β : BitAssignment posCoreWires) : Bool
    :=
  let rCore := QRegExt.ofFin posCoreWires
  let b2 := β (wSlot2Core rCore) == 1
  let b1 := β (wSlot1Core rCore) == 1
  let s0 := β (wSlot0Core rCore) == 1
  if b2 then false
  else if b1 then s0
  else
    let nucOk := !s0 → regVal (rNucIdx rCore) β < 216
    let ancOk := regVal (rAnchorIdx rCore) β < 218
    let partOk := (s0 && !(β (wIsHead rCore) == 1)) → regVal (rPartnerIdx rCore) β < 217
    let accept : Bool := !(β (wSubReject rCore) == 1) && decide nucOk && ancOk && decide partOk
    if !accept then
      β (wRejectZero rCore) == 1
    else if β (wIsHead rCore) == 1 then
      false
    else
      let iIdx := regVal (rAnchorIdx rCore) β
      let mIdx := regVal (rPartnerIdx rCore) β
      let ySlot2 := if slot2SwappedTo0 then slotSubGridCoord64 (rElecSlot rCore 0) β else
          slotSubGridCoord64 (rElecSlot rCore ⟨iIdx % 218, Nat.mod_lt _ (by omega)⟩) β
      let y0 := slotSubGridCoord64 (rElecSlot rCore 0) β
      let y1 := slotSubGridCoord64
        (rElecSlot rCore ⟨(mIdx % 217) + 1, by have := Nat.mod_lt mIdx (by omega : 0 < 217); omega⟩)
          β
      let coset1 := parity3OfReg (rCosetB1 rCore) β
      let coset0 := parity3OfReg (rCosetB0 rCore) β
      let dTail : FineCoord128 := fun w ↦
        if !s0 then
          ⟨2 * (ySlot2 w).val + (if coset1 w then 1 else 0), by
            have := (ySlot2 w).isLt; split_ifs <;> omega⟩
        else
          ⟨(2 * (y0 w).val + (if coset0 w then 1 else 0) + 128 -
            (2 * (y1 w).val + (if coset1 w then 1 else 0))) % 128,
            Nat.mod_lt _ (by omega)⟩
      let rOrbit := tetRank65 (canonTriple128 dTail)
      let keepLt := regVal (rTailKeep30 rCore) β < (tailMag30 rOrbit).val
      if keepLt then
        if !s0 then !(tailSign rOrbit) else tailSign rOrbit
      else
        β (wRejectZero rCore) == 1
def posPhaseBit (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (β : BitAssignment posCoreWires) : Bool
    := xor (headPhaseBitSpec β)
    (tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β)
noncomputable def uPosPhase (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : Unitary (2 ^ posCoreWires) :=
    diagonalSignUnitaryN (posPhaseBit slot2SwappedTo0 tailSign tailMag30)
theorem uPosPhase_mulVec_ket (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (β : BitAssignment posCoreWires) :
    (uPosPhase slot2SwappedTo0 tailSign tailMag30).1.mulVec (ket β) = (if posPhaseBit
    slot2SwappedTo0 tailSign tailMag30 β then (-1 : ℂ) else 1) • ket β :=
    ket_diagonalSignUnitaryN (posPhaseBit slot2SwappedTo0 tailSign tailMag30) β
theorem uPosPhase_conjTranspose (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhase slot2SwappedTo0 tailSign tailMag30).1ᴴ =
    (uPosPhase slot2SwappedTo0 tailSign tailMag30).1 := diagonalSignUnitaryN_conjTranspose
    (posPhaseBit slot2SwappedTo0 tailSign tailMag30)
end Specification
section ConcreteCircuits
section CleanSandwichAndHeadPhase
variable {Var : Type} {n : ℕ}
theorem RealizesCleanUnitary.seq_comm [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    {v : Var} {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hP_herm : Pᴴ = P)
    {d₁ d₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)}
    (hd₁ : RealizesCleanUnitary v P d₁ U₁) (hd₂ : RealizesCleanUnitary v P d₂ U₂)
    (hcomm₁ : U₁.1 * P = P * U₁.1) : RealizesCleanUnitary v P (.seq d₁ d₂) (U₂ * U₁) := by
  have hadj₁ : P * U₁.1ᴴ = U₁.1ᴴ * P := by
    simpa only [conjTranspose_mul, hP_herm] using congrArg conjTranspose hcomm₁
  refine ⟨fun Θ hΘ ↦ hd₁.1 (wp d₂.compile Θ) (hd₂.1 Θ hΘ), fun Θ hΘ σ ↦ ?_⟩
  have hb₁ := congrArg HermitianMat.mat (hd₁.2 (wp d₂.compile Θ) (hd₂.1 Θ hΘ) σ)
  have hb₂ := congrArg HermitianMat.mat (hd₂.2 Θ hΘ σ)
  rw [HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat, hP_herm] at hb₁ hb₂
  ext1
  rw [HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat, hP_herm]
  let M₁₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := (wp d₁.compile (wp d₂.compile Θ) σ).1.1
  let M₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := (wp d₂.compile Θ σ).1.1
  have hq₁ : (wpQAssignCompat U₁ (wp d₂.compile Θ) σ).1.1 = U₁.1ᴴ * M₂ * U₁.1 := by
    simp [M₂, wpQAssignCompat, qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hq₂ : (wpQAssignCompat U₂ Θ σ).1.1 = U₂.1ᴴ * (Θ σ).1.1 * U₂.1 := by
    simp [wpQAssignCompat, qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hq₁₂ : (wpQAssignCompat (U₂ * U₁) Θ σ).1.1 = U₁.1ᴴ * U₂.1ᴴ * (Θ σ).1.1 * (U₂.1 * U₁.1) := by
    simp [wpQAssignCompat, qAssignObsMap, Matrix.star_eq_conjTranspose, conjTranspose_mul,
      Matrix.mul_assoc]
  change P * M₁₂ * P = P * (wpQAssignCompat U₁ (wp d₂.compile Θ) σ).1.1 * P at hb₁
  change P * M₂ * P = P * (wpQAssignCompat U₂ Θ σ).1.1 * P at hb₂
  rw [hq₁] at hb₁
  rw [hq₂] at hb₂
  change P * M₁₂ * P = P * (wpQAssignCompat (U₂ * U₁) Θ σ).1.1 * P
  rw [hq₁₂]
  calc P * M₁₂ * P
      = (P * U₁.1ᴴ) * M₂ * (U₁.1 * P) := by
        rw [hb₁]; simp only [Matrix.mul_assoc]
    _ = U₁.1ᴴ * (P * M₂ * P) * U₁.1 := by
        rw [hadj₁, hcomm₁]; simp only [Matrix.mul_assoc]
    _ = U₁.1ᴴ * (P * (U₂.1ᴴ * (Θ σ).1.1 * U₂.1) * P) * U₁.1 := by
        rw [hb₂]
    _ = (P * U₁.1ᴴ) * U₂.1ᴴ * (Θ σ).1.1 * U₂.1 * (U₁.1 * P) := by
        simp only [← Matrix.mul_assoc]; rw [← hadj₁]; simp only [Matrix.mul_assoc]; rw [← hcomm₁]
    _ = P * (U₁.1ᴴ * U₂.1ᴴ * (Θ σ).1.1 * (U₂.1 * U₁.1)) * P := by
        simp only [Matrix.mul_assoc]
end CleanSandwichAndHeadPhase
section HeadPhaseComplete
variable {Var : Type} {n : ℕ}
theorem embedMatrix_comm_projZeroAll {a mWork : ℕ} (r : QRegister a n)
    (M : Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℂ) (f : Fin mWork → Wire n)
    (hdisj : ∀ k : Fin mWork, f k ∉ r.image) :
    r.embedMatrix M * projZeroAll mWork f = projZeroAll mWork f * r.embedMatrix M := by
  rw [projZeroAll_eq_diagonal]
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [QRegister.embedMatrix_apply]
  by_cases envEq : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2
  · have hsame : (∀ k, basisBits n y (f k) = 0) ↔ (∀ k, basisBits n x (f k) = 0) :=
      forall_congr' fun k ↦ by
        have hnot : f k ∉ Set.range r.wires := fun ⟨i, hi⟩ ↦
          hdisj k (QRegister.mem_image r _ |>.mpr ⟨i, hi⟩)
        rw [(r.basisSplit_environment_eq_iff x y).mp envEq (f k) hnot]
    by_cases hx : ∀ k, basisBits n x (f k) = 0
    · simp [envEq, hx, hsame.mpr hx]
    · simp [envEq, hx, mt hsame.mp hx]
  · simp [envEq]
theorem circuit_eval_comm_projZeroAll {mWork : ℕ} (f : Fin mWork → Wire n) :
    ∀ (c : Circuit n),(∀ k : Fin mWork, f k ∉ c.support) →
      c.eval.1 * projZeroAll mWork f = projZeroAll mWork f * c.eval.1
  | .identity, _ => by simp
  | .gate g r, hnot => embedMatrix_comm_projZeroAll r g.eval.1 f hnot
  | .seq c₁ c₂, hnot => by
      have h₁ : ∀ k, f k ∉ c₁.support := fun k h ↦ hnot k (Finset.mem_union_left _ h)
      have h₂ : ∀ k, f k ∉ c₂.support := fun k h ↦ hnot k (Finset.mem_union_right _ h)
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      calc (c₂.eval.1 * c₁.eval.1) * projZeroAll mWork f
          = c₂.eval.1 * (c₁.eval.1 * projZeroAll mWork f) := Matrix.mul_assoc _ _ _
        _ = c₂.eval.1 * (projZeroAll mWork f * c₁.eval.1) := by
            rw [circuit_eval_comm_projZeroAll f c₁ h₁]
        _ = (c₂.eval.1 * projZeroAll mWork f) * c₁.eval.1 := (Matrix.mul_assoc _ _ _).symm
        _ = (projZeroAll mWork f * c₂.eval.1) * c₁.eval.1 := by
            rw [circuit_eval_comm_projZeroAll f c₂ h₂]
        _ = projZeroAll mWork f * (c₂.eval.1 * c₁.eval.1) := Matrix.mul_assoc _ _ _
end HeadPhaseComplete
section TailAndSlackPhase
variable {Var : Type} {n : ℕ}
def tailDecisionBool (b2 b1 s0 sr ih rz ltN ltA ltP keepLt tSign : Bool) : Bool :=
  if b2 then false
  else if b1 then s0
  else
    let nucOk := (!s0) → (ltN = true)
    let partOk := (s0 && !ih) → (ltP = true)
    let accept : Bool := (!sr) && decide nucOk && ltA && decide partOk
    if !accept then rz
    else if ih then false
    else if keepLt then
      if !s0 then !tSign else tSign
    else rz
attribute [local irreducible] condSwapRegs
attribute [local irreducible] copyXorRegCircuit
theorem regVal_congr_cross {k n₁ n₂ : ℕ} (r₁ : QRegister k n₁) (r₂ : QRegister k n₂)
    (β₁ : BitAssignment n₁) (β₂ : BitAssignment n₂) (h : ∀ j : Fin k, β₁ (r₁ j) = β₂ (r₂ j)) :
    regVal r₁ β₁ = regVal r₂ β₂ := by
  unfold regVal bitsVal
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only
  rw [h j]
def tailOrbitCoord128 (slot2SwappedTo0 : Bool) (β : BitAssignment posCoreWires) : FineCoord128 :=
  let rCore := QRegExt.ofFin posCoreWires
  let s0 := β (wSlot0Core rCore) == 1
  let iIdx := regVal (rAnchorIdx rCore) β
  let mIdx := regVal (rPartnerIdx rCore) β
  let ySlot2 := if slot2SwappedTo0 then slotSubGridCoord64 (rElecSlot rCore 0) β else
      slotSubGridCoord64 (rElecSlot rCore ⟨iIdx % 218, Nat.mod_lt _ (by omega)⟩) β
  let y0 := slotSubGridCoord64 (rElecSlot rCore 0) β
  let y1 := slotSubGridCoord64
    (rElecSlot rCore ⟨(mIdx % 217) + 1, by have := Nat.mod_lt mIdx (by omega : 0 < 217); omega⟩) β
  let coset1 := parity3OfReg (rCosetB1 rCore) β
  let coset0 := parity3OfReg (rCosetB0 rCore) β
  fun w ↦
    if !s0 then
      ⟨2 * (ySlot2 w).val + (if coset1 w then 1 else 0), by
        have := (ySlot2 w).isLt; split_ifs <;> omega⟩
    else
      ⟨(2 * (y0 w).val + (if coset0 w then 1 else 0) + 128 -
        (2 * (y1 w).val + (if coset1 w then 1 else 0))) % 128,
        Nat.mod_lt _ (by omega)⟩
attribute [local irreducible] canonTriple128 tetRank65
attribute [local irreducible] swapTreePow2Val
attribute [local irreducible] packTailTable31 packTablePow2 tailOrbitCoord128
end TailAndSlackPhase
end ConcreteCircuits
end PosSlots24BranchConcrete
end
end ModPosSlots24BranchConcrete

section ModPosSlots24PartnerMux288
@[expose] public section
namespace PosSlots24PartnerMux288
set_option maxRecDepth 16000000
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open OctahedralOrbit Dyadic128CoulombMath
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open BchCubeDecoder
open PosSlots24BranchConcrete
instance (priority := 100000) instNeZeroTwoPowPartnerMux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable abbrev uPosTailAndSlack (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : Unitary (2 ^ posCoreWires) :=
  diagonalSignUnitaryN (tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30)
attribute [local irreducible]
  copyXorRegCircuit canonTriple128 tetRank65 tailAndSlackPhaseBitSpec
section GenericBridges
variable {Var : Type} {n : ℕ}
@[simp] theorem basisBits_symm_apply {q : ℕ} (f : BitAssignment q) : basisBits q
    ((basisBitsEquiv q).symm f) = f := (basisBitsEquiv q).apply_symm_apply f
theorem ite_pos {α : Sort*} {c : Prop} [h : Decidable c] (hc : c) {a b : α} :
    ite c a b = a := by
  cases h with
  | isTrue _ => rfl
  | isFalse hnc => exact absurd hc hnc
theorem ite_neg {α : Sort*} {c : Prop} [h : Decidable c] (hc : ¬ c) {a b : α} :
    ite c a b = b := by
  cases h with
  | isTrue hc' => exact absurd hc' hc
  | isFalse _ => rfl
@[simp] theorem basisBits_symm_apply_at {q : ℕ} (f : BitAssignment q) (i : Fin q) :
    basisBits q ((basisBitsEquiv q).symm f) i = f i :=
  congrFun ((basisBitsEquiv q).apply_symm_apply f) i
theorem eq_of_basisBits_eq {q : ℕ} {x y : Fin (2 ^ q)}
    (h : ∀ i : Fin q, basisBits q x i = basisBits q y i) : x = y :=
  (basisBitsEquiv q).injective (funext h)
theorem qreg_ext {k : ℕ} {r₁ r₂ : QRegister k n} (h : ∀ i : Fin k, r₁ i = r₂ i) : r₁ = r₂ := by
  cases r₁ with
  | mk w₁ =>
      cases r₂ with
      | mk w₂ =>
          congr 1
          apply Function.Embedding.ext
          intro i
          exact h i
theorem disj_symm {k₁ k₂ : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    (h : r₁.DisjointWires r₂) : r₂.DisjointWires r₁ :=
  QRegister.disjoint_iff.mpr fun i j heq ↦ h.ne j i heq.symm
theorem permMatrix_mem_unitaryGroup {k : ℕ} (perm : Equiv.Perm (Fin (2 ^ k))) :
    Equiv.Perm.permMatrix ℂ perm ∈ Matrix.unitaryGroup (Fin (2 ^ k)) ℂ := by
  have hstar : star (Equiv.Perm.permMatrix ℂ perm) = Equiv.Perm.permMatrix ℂ perm.symm := by
    ext i j
    simp only [Matrix.star_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    have hiff : (i ∈ perm.toPEquiv j) ↔ (j ∈ perm.symm.toPEquiv i) := by
      simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
      exact ⟨fun h ↦ by subst h; simp, fun h ↦ by subst h; simp⟩
    by_cases h1 : i ∈ perm.toPEquiv j
    · rw [ite_pos h1, ite_pos (hiff.mp h1), star_one]
    · rw [ite_neg h1, ite_neg (mt hiff.mpr h1), star_zero]
  have hm : ∀ (e : Equiv.Perm (Fin (2 ^ k))),
      Equiv.Perm.permMatrix ℂ e.symm * Equiv.Perm.permMatrix ℂ e = 1 := fun e ↦ by
    ext i j
    simp only [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    rw [Finset.sum_eq_single (e.symm j)]
    · simp [Matrix.one_apply]
    · intro x _ hx; simp [show ¬ e x = j from fun hp ↦ hx (by rw [← hp]; simp)]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  exact ⟨by rw [hstar]; exact hm perm, by rw [hstar]; exact hm perm.symm⟩
noncomputable abbrev invPermMat {k : ℕ} (perm : Equiv.Perm (Fin (2 ^ k))) : Matrix
    (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ := Equiv.Perm.permMatrix ℂ perm.symm
noncomputable def permSignUnitary {k : ℕ}
    (perm : Equiv.Perm (Fin (2 ^ k))) (phase : Fin (2 ^ k) → Bool) : Unitary (2 ^ k) :=
  ⟨invPermMat perm * (diagSignUnitary phase).1,
    Submonoid.mul_mem _ (permMatrix_mem_unitaryGroup perm.symm) (diagSignUnitary phase).2⟩
end GenericBridges
section OrbitToggle
variable {n : ℕ}
def rawOrbitCoord128 (slot2SwappedTo0 : Bool)
    (βCore : BitAssignment posCoreWires) (βPartner : BitAssignment 18) : FineCoord128 :=
  let rCoreL := QRegExt.ofFin posCoreWires
  let rP18L := QRegExt.ofFin 18
  fun w ↦
    if Bool.not (βCore (wSlot0Core rCoreL) == 1) then
      ⟨2 * (if slot2SwappedTo0 then regVal (axisBitRev6 (rElecSlot rCoreL 0) w) βCore
            else regVal (axisBitRev6 rP18L w) βPartner) +
        (if decide (βCore (rCosetB1 rCoreL w) = 1) then 1 else 0),
       by
         have h1 := regVal_lt_two_pow (axisBitRev6 (rElecSlot rCoreL 0) w) βCore
         have h2 := regVal_lt_two_pow (axisBitRev6 rP18L w) βPartner
         split_ifs <;> omega⟩
    else
      ⟨(2 * regVal (axisBitRev6 (rElecSlot rCoreL 0) w) βCore +
          (if decide (βCore (rCosetB0 rCoreL w) = 1) then 1 else 0) + 128 -
        (2 * regVal (axisBitRev6 rP18L w) βPartner +
          (if decide (βCore (rCosetB1 rCoreL w) = 1) then 1 else 0))) % 128,
       Nat.mod_lt _ (by omega)⟩
noncomputable def orbitRankFin16 (slot2SwappedTo0 : Bool)
    (βCore : BitAssignment posCoreWires) (βPartner : BitAssignment 18) : Fin (2 ^ 16) :=
  let r := tetRank65 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0 βCore βPartner))
  ⟨r.val, by have := r.isLt; dsimp [orbitCount47905] at this; omega⟩
theorem val_orbitRankFin16 (slot2SwappedTo0 : Bool) (βCore : BitAssignment posCoreWires)
    (βPartner : BitAssignment 18) : (orbitRankFin16 slot2SwappedTo0 βCore βPartner).val =
    (tetRank65 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0 βCore βPartner))).val := rfl
attribute [local irreducible] tailOrbitCoord128 rawOrbitCoord128 orbitRankFin16
end OrbitToggle
attribute [local irreducible] tailOrbitCoord128 rawOrbitCoord128 orbitRankFin16 posCoreWires
section MasterWrapper288
variable {Var : Type} {n : ℕ}
set_option allowUnsafeReducibility true in
noncomputable def sandPhase18 (slot2SwappedTo0 : Bool)
    (midPhase : Fin (2 ^ (posCoreWires + 16)) → Bool)
    (w : Fin (2 ^ (posCoreWires + 18))) : Bool :=
  let bits := basisBits (posCoreWires + 18) w
  let βC : BitAssignment posCoreWires := fun i ↦ bits (Fin.castAdd 18 i)
  let βP : BitAssignment 18 := fun j ↦ bits (Fin.natAdd posCoreWires j)
  let rk := orbitRankFin16 slot2SwappedTo0 βC βP
  midPhase ((basisBitsEquiv (posCoreWires + 16)).symm fun m ↦
    if hm : m.val < posCoreWires then βC ⟨m.val, hm⟩
    else basisBits 16 rk ⟨m.val - posCoreWires, by omega⟩)
attribute [local irreducible] DynCircuitExt.measureXResetAndBranch
end MasterWrapper288
end PosSlots24PartnerMux288
end
end ModPosSlots24PartnerMux288

section ModPosSlots24PhaseTailConcrete
@[expose] public section
end
end ModPosSlots24PhaseTailConcrete

section ModPrunedQromLookup
@[expose] public section
namespace PrunedQromLookup
open Operator QProg Matrix HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open OctahedralOrbit
section EffectiveIndex
def prunedEffIdx : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | m + 1, Q, x =>
      if Q ≤ 2 ^ m then
        prunedEffIdx m Q (x % 2 ^ m)
      else if x < 2 ^ m then
        x
      else
        2 ^ m + prunedEffIdx m (Q - 2 ^ m) (x % 2 ^ m)
theorem prunedEffIdx_eq_self : ∀ (k Q x : ℕ), Q ≤ 2 ^ k → x < Q → prunedEffIdx k Q x = x
  | 0, Q, x, hQk, hx => by
      dsimp only [prunedEffIdx]
      omega
  | m + 1, Q, x, hQk, hx => by
      have hsucc : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      dsimp only [prunedEffIdx]
      split_ifs with hle hlt
      · have hmod : x % 2 ^ m = x := Nat.mod_eq_of_lt (lt_of_lt_of_le hx hle)
        rw [hmod]
        exact prunedEffIdx_eq_self m Q x hle hx
      · rfl
      · have hmod : x % 2 ^ m = x - 2 ^ m := by
          rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hmod, prunedEffIdx_eq_self m (Q - 2 ^ m) (x - 2 ^ m) (by omega) (by omega)]
        omega
end EffectiveIndex
section PrunedPhaseQrom
variable {Var : Type} {n : ℕ}
def phaseLookupPrunedCircuit {w : ℕ} (rP : QRegister w n) :
    {k : ℕ} → (c : Option (Wire n)) → (Q : ℕ) → (rX rW : QRegister k n) →
    rX.DisjointWires rW → rW.DisjointWires rP →
    (∀ i, CtrlNe c (rX i)) → (∀ i, CtrlNe c (rW i)) → (∀ i, CtrlNe c (rP i)) →
    (ℕ → BitAssignment w) → Circuit n
  | 0, c, _, _, _, _, _, _, _, hcP, T => czFanoutCircuit c rP hcP (T 0)
  | m + 1, c, Q, rX, rW, hXW, hWP, hcX, hcW, hcP, T =>
      let hXW' : (regInit rX).DisjointWires (regInit rW) := disjoint_regInit_both hXW
      let hWP' : (regInit rW).DisjointWires rP := disjoint_regInit_left hWP
      if Q ≤ 2 ^ m then
        phaseLookupPrunedCircuit rP c Q (regInit rX) (regInit rW) hXW' hWP'
          (fun i ↦ hcX i.castSucc) (fun i ↦ hcW i.castSucc) hcP T
      else
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
          (phaseLookupPrunedCircuit rP (some (rW (Fin.last m))) (Q - 2 ^ m)
            (regInit rX) (regInit rW) hXW' hWP' hcX' hcW' hcP' (fun j ↦ T (2 ^ m + j)))
theorem phaseLookupPrunedCircuit_eval_mulVec_ket {k w : ℕ} (rP : QRegister w n)
    (c : Option (Wire n)) (Q : ℕ) (rX rW : QRegister k n) (hXW : rX.DisjointWires rW)
    (hWP : rW.DisjointWires rP) (hcX : ∀ i, CtrlNe c (rX i)) (hcW : ∀ i, CtrlNe c (rW i))
    (hcP : ∀ i, CtrlNe c (rP i)) (T : ℕ → BitAssignment w) (β : BitAssignment n)
    (hclean : ∀ i, β (rW i) = 0) : (phaseLookupPrunedCircuit rP c Q rX rW hXW hWP hcX hcW hcP
    T).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (ctrlVal c β * ∑ i : Fin w, β (rP i) * T
    (prunedEffIdx k Q (localIdx rX β)) i).val) • ket β := by
  induction k generalizing c Q T β with
  | zero =>
      dsimp only [phaseLookupPrunedCircuit, prunedEffIdx]
      have hsum : (∑ i : Fin w, ctrlVal c β * β (rP i) * T 0 i) =
          ctrlVal c β * ∑ i : Fin w, β (rP i) * T 0 i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring
      rw [czFanoutCircuit_eval_mulVec_ket, hsum]
  | succ m ih =>
      have hidx := localIdx_val_castSucc rX β
      have hlt_sub : (localIdx (regInit rX) β : ℕ) < 2 ^ m := (localIdx (regInit rX) β).isLt
      dsimp only [phaseLookupPrunedCircuit]
      split_ifs with hle
      · rw [ih c Q (regInit rX) (regInit rW) (disjoint_regInit_both hXW) (disjoint_regInit_left hWP)
          (fun i ↦ hcX i.castSucc) (fun i ↦ hcW i.castSucc) hcP T β
          (fun i ↦ by rw [regInit_apply]; exact hclean i.castSucc)]
        congr 3
        have hmod : (localIdx rX β : ℕ) % 2 ^ m = (localIdx (regInit rX) β : ℕ) := by
          rcases zmod2_eq_zero_or_one (β (rX (Fin.last m))) with hm | hm <;> rw [hm] at hidx
          · rw [ZMod.val_zero, zero_mul, add_zero] at hidx
            rw [hidx, Nat.mod_eq_of_lt hlt_sub]
          · rw [ZMod.val_one, one_mul] at hidx
            rw [hidx, Nat.add_mod_right, Nat.mod_eq_of_lt hlt_sub]
        dsimp only [prunedEffIdx]
        simp only [hle, ↓reduceIte]
        rw [hmod]
      · let wAnc := rW (Fin.last m)
        have hAncNotX : wAnc ∉ Set.range (regInit rX).wires :=
          fun ⟨i, hi⟩ ↦ hXW.ne i.castSucc (Fin.last m) hi
        have hCleanUpd (a : ZMod 2) (i : Fin m) :
            Function.update β wAnc a ((regInit rW) i) = 0 := by
          rw [Function.update_of_ne (regInit_ne_last rW i), regInit_apply, hclean i.castSucc]
        have hSumUpd (a : ZMod 2) (f : BitAssignment w) :
            (∑ i : Fin w, Function.update β wAnc a (rP i) * f i) = ∑ i : Fin w, β (rP i) * f i :=
          Finset.sum_congr rfl fun i _ ↦ by rw [Function.update_of_ne (hWP.ne (Fin.last m) i).symm]
        rw [branchMsbCircuit_eval_mulVec_ket_diag c rX rW hXW hcX hcW _ _
          (∑ i : Fin w, β (rP i) * T (localIdx (regInit rX) β) i)
          (∑ i : Fin w, β (rP i) *
            T (2 ^ m + prunedEffIdx m (Q - 2 ^ m) (localIdx (regInit rX) β)) i)
          β (hclean (Fin.last m))
          (fun a ↦ by
            rw [phaseLookupCircuit_eval_mulVec_ket rP (some wAnc) (regInit rX) (regInit rW)
                _ _ _ _ _ (fun j ↦ T j) (Function.update β wAnc a) (hCleanUpd a),
              localIdx_update_of_not_mem _ _ hAncNotX]
            simp only [ctrlVal, Function.update_self]
            rw [hSumUpd a])
          (fun a ↦ by
            rw [ih (some wAnc) (Q - 2 ^ m) (regInit rX) (regInit rW) _ _ _ _ _
                (fun j ↦ T (2 ^ m + j)) (Function.update β wAnc a) (hCleanUpd a),
              localIdx_update_of_not_mem _ _ hAncNotX]
            simp only [ctrlVal, Function.update_self]
            rw [hSumUpd a])]
        congr 3
        dsimp only [prunedEffIdx]
        simp only [hle, ↓reduceIte]
        rcases zmod2_eq_zero_or_one (β (rX (Fin.last m))) with hm | hm <;> rw [hm]
        · simp only [↓reduceIte]
          rw [hm, ZMod.val_zero, zero_mul, add_zero] at hidx
          simp only [hidx, hlt_sub, ↓reduceIte]
        · have h10 : (1 : ZMod 2) ≠ 0 := by decide
          simp only [h10, ↓reduceIte]
          rw [hm, ZMod.val_one, one_mul] at hidx
          have hnotlt : ¬ ((localIdx rX β : ℕ) < 2 ^ m) := by omega
          simp only [hnotlt, ↓reduceIte]
          rw [hidx, Nat.add_mod_right, Nat.mod_eq_of_lt hlt_sub]
end PrunedPhaseQrom
section PrunedDataQrom
variable {Var : Type} {n : ℕ}
private theorem lemHex337 {b : ℕ} (q : Wire n) (rTail : QRegister b n)
    (hq : ∀ j : Fin b, q ≠ rTail j) : (hadamardReg rTail).eval.1 * (Circuit.H q).eval.1 =
    (Circuit.H q).eval.1 * (hadamardReg rTail).eval.1 := by
  induction b with
  | zero =>
      simp [hadamardReg]
  | succ m ih =>
      let rRest := rTail.slice 1 m (by omega)
      have hRestNe : ∀ j : Fin m, q ≠ rRest j := fun j ↦ by
        dsimp only [rRest]
        rw [QRegister.slice_apply]
        exact hq ⟨1 + j.val, by omega⟩
      have h0Ne : q ≠ rTail 0 := hq 0
      have hSingleComm : (Circuit.H (rTail 0)).eval.1 * (Circuit.H q).eval.1 =
          (Circuit.H q).eval.1 * (Circuit.H (rTail 0)).eval.1 := by
        apply matrix_ext_ket
        intro β
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_H, Matrix.mulVec_smul,
          Matrix.mulVec_add, Matrix.mulVec_smul, ket_H, ket_H, ket_H, Matrix.mulVec_smul,
          Matrix.mulVec_add, Matrix.mulVec_smul, ket_H, ket_H]
        simp only [Function.update_of_ne h0Ne, Function.update_of_ne h0Ne.symm, smul_add, smul_smul]
        rw [Function.update_comm h0Ne.symm 0 0 β, Function.update_comm h0Ne.symm 0 1 β,
            Function.update_comm h0Ne.symm 1 0 β, Function.update_comm h0Ne.symm 1 1 β]
        ext idx
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hExpand : (hadamardReg rTail).eval.1 =
          (hadamardReg rRest).eval.1 * (Circuit.H (rTail 0)).eval.1 := by
        simp [hadamardReg, rRest]
      rw [hExpand, Matrix.mul_assoc, hSingleComm, ← Matrix.mul_assoc, ih rRest hRestNe,
        Matrix.mul_assoc]
private theorem lemHex338 (q : Wire n) (d₀ : ZMod 2) (β₀ β₁ : BitAssignment n)
    (hβ : Function.update β₀ q 1 = β₁ ∧ Function.update β₁ q 0 = β₀) (bInit : ZMod 2) :
    (Circuit.H q).eval.1.mulVec (sqrtHalfC • (ket β₀ + bitSignC (bInit + d₀) • ket β₁)) = ket
    (if bInit + d₀ = 0 then β₀ else β₁) := by
  rcases hβ with ⟨h01, h10⟩
  have hq0 : β₀ q = 0 := by
    rw [← h10, Function.update_self]
  have hq1 : β₁ q = 1 := by
    rw [← h01, Function.update_self]
  have hu00 : Function.update β₀ q 0 = β₀ := Function.update_eq_self_iff.mpr hq0.symm
  have hu11 : Function.update β₁ q 1 = β₁ := Function.update_eq_self_iff.mpr hq1.symm
  rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, ket_H, ket_H,
    hq0, hq1, hu00, hu11, h01, h10]
  have hsq : sqrtHalfC * sqrtHalfC = 1 / 2 := sqrtHalfC_mul_sqrtHalfC
  have h10z : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod2_eq_zero_or_one (bInit + d₀) with hs | hs <;> rw [hs]
  · simp only [↓reduceIte, bitSignC, h10z, one_smul, neg_one_smul, smul_add, smul_smul, smul_neg]
    ext idx
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination 2 * ket β₀ idx * hsq
  · simp only [h10z, ↓reduceIte, bitSignC, one_smul, neg_one_smul, smul_add, smul_smul, smul_neg]
    ext idx
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination 2 * ket β₁ idx * hsq
theorem hadamardReg_conj_phase_mulVec_ket {w : ℕ} (rP : QRegister w n)
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (d : BitAssignment w) (β : BitAssignment n) (hA
    : ∀ γ : BitAssignment w, A.mulVec (ket (writeReg β rP γ)) = ((-1 : ℂ) ^ (∑ i : Fin w, γ i
    * d i).val) • ket (writeReg β rP γ)) :
    ((hadamardReg rP).eval.1 * A * (hadamardReg rP).eval.1).mulVec (ket β) = ket
    (writeReg β rP (fun i ↦ β (rP i) + d i)) := by
  induction w generalizing A β with
  | zero =>
      have hd : (∑ i : Fin 0, (Fin.elim0 i : ZMod 2) * d i) = 0 := by simp
      have h0 : writeReg β rP Fin.elim0 = β := by
        funext q; exact writeReg_apply_of_not_mem β rP Fin.elim0 q (fun ⟨i, _⟩ ↦ i.elim0)
      have hout : writeReg β rP (fun i ↦ β (rP i) + d i) = β := by
        funext q; exact writeReg_apply_of_not_mem β rP _ q (fun ⟨i, _⟩ ↦ i.elim0)
      have hA0 := hA Fin.elim0
      rw [h0, hd, ZMod.val_zero, _root_.pow_zero, one_smul] at hA0
      simp only [hadamardReg, Circuit.eval_identity, Submonoid.coe_one, one_mul, mul_one, hA0, hout]
  | succ m ih =>
      let rTail := rP.slice 1 m (by omega)
      have hTailWire : ∀ j : Fin m, rTail j = rP j.succ := fun j ↦ by
        dsimp only [rTail]; rw [QRegister.slice_apply]; congr 1; ext; dsimp; omega
      have h0Ne : ∀ j : Fin m, rP 0 ≠ rTail j := fun j h ↦
        Fin.succ_ne_zero j (rP.wires.injective (h.trans (hTailWire j)).symm)
      have hH : (hadamardReg rP).eval.1 =
          (hadamardReg rTail).eval.1 * (Circuit.H (rP 0)).eval.1 := by
        simp [hadamardReg, rTail]
      have hComm := lemHex337 (rP 0) rTail h0Ne
      have hConsSlice : ∀ (x₀ : ZMod 2) (xTail : BitAssignment m),
          writeReg (Function.update β (rP 0) x₀) rTail xTail = writeReg β rP (Fin.cons x₀ xTail) :=
            by
        intro x₀ xTail
        funext q
        by_cases hqTail : q ∈ Set.range rTail.wires
        · obtain ⟨j, rfl⟩ := hqTail
          rw [writeReg_apply_reg, hTailWire j, writeReg_apply_reg, Fin.cons_succ]
        · rw [writeReg_apply_of_not_mem _ _ _ _ hqTail]
          by_cases hq0 : q = rP 0
          · subst hq0; rw [Function.update_self, writeReg_apply_reg, Fin.cons_zero]
          · rw [Function.update_of_ne hq0, writeReg_apply_of_not_mem β rP _ q]
            rintro ⟨i, rfl⟩
            cases i using Fin.cases with
            | zero => exact hq0 rfl
            | succ j => exact hqTail ⟨j, hTailWire j⟩
      have hBranch : ∀ b₀ : ZMod 2,
          ((hadamardReg rTail).eval.1 * A * (hadamardReg rTail).eval.1).mulVec
          (ket (Function.update β (rP 0) b₀)) = ((-1 : ℂ) ^ (b₀ * d 0).val) • ket
          (writeReg β rP (Fin.cons b₀ (fun j ↦ β (rP j.succ) + d j.succ))) := by
        intro b₀
        let s : ℂ := (-1 : ℂ) ^ (b₀ * d 0).val
        have hs_inv : s * s = 1 := by
          rcases zmod2_eq_zero_or_one (b₀ * d 0) with h | h <;>
            simp only [s, h, ZMod.val_zero, ZMod.val_one] <;> norm_num
        have hScaled := ih rTail (s • A) (fun j ↦ d j.succ) (Function.update β (rP 0) b₀)
          (fun γTail ↦ by
            rw [Matrix.smul_mulVec, hConsSlice b₀ γTail, hA (Fin.cons b₀ γTail), smul_smul,
              Fin.sum_univ_succ, neg_one_pow_zmod2_add]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [← mul_assoc, hs_inv, one_mul])
        have hLin : ((hadamardReg rTail).eval.1 * (s • A) * (hadamardReg rTail).eval.1) =
            s • ((hadamardReg rTail).eval.1 * A * (hadamardReg rTail).eval.1) := by
          rw [mul_smul_comm, smul_mul_assoc]
        rw [hLin, Matrix.smul_mulVec] at hScaled
        have hisolate : ((hadamardReg rTail).eval.1 * A * (hadamardReg rTail).eval.1).mulVec
            (ket (Function.update β (rP 0) b₀)) = s • ket (writeReg (Function.update β (rP 0)
            b₀) rTail (fun j ↦ Function.update β (rP 0) b₀ (rTail j) + d j.succ)) := by
          calc _ = (1 : ℂ) • _ := (one_smul _ _).symm
            _ = (s * s) • _ := by rw [hs_inv]
            _ = s • (s • _) := mul_smul s s _
            _ = s • _ := by rw [hScaled]
        rw [hisolate, hConsSlice]
        congr 4
        funext j
        rw [Function.update_of_ne (h0Ne j).symm, hTailWire j]
      calc
        ((hadamardReg rP).eval.1 * A * (hadamardReg rP).eval.1).mulVec (ket β)
            = ((Circuit.H (rP 0)).eval.1 *
                ((hadamardReg rTail).eval.1 * A * (hadamardReg rTail).eval.1) *
                (Circuit.H (rP 0)).eval.1).mulVec (ket β) := by
              nth_rw 1 [hH]
              rw [hComm]
              nth_rw 1 [hH]
              simp only [Matrix.mul_assoc]
        _ = (Circuit.H (rP 0)).eval.1.mulVec
              (sqrtHalfC • (ket (writeReg β rP (Fin.cons 0 (fun j ↦ β (rP j.succ) + d j.succ))) +
                bitSignC (β (rP 0) + d 0) •
                  ket (writeReg β rP (Fin.cons 1 (fun j ↦ β (rP j.succ) + d j.succ))))) := by
              rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_H, Matrix.mulVec_smul,
                Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hBranch 0, hBranch 1]
              simp only [zero_mul, ZMod.val_zero, _root_.pow_zero, one_smul, one_mul,
                smul_smul, ← bitSignC_eq_neg_one_pow]
              have hsign : ∀ x y : ZMod 2, bitSignC x * bitSignC y = bitSignC (x + y) := by
                intro x y
                rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
                  rcases zmod2_eq_zero_or_one y with rfl | rfl <;>
                  simp [bitSignC, show (1 : ZMod 2) ≠ 0 by decide,
                    show (1 + 1 : ZMod 2) = 0 by decide]
              rw [hsign, ← Matrix.mulVec_smul]
        _ = ket (if β (rP 0) + d 0 = 0
              then writeReg β rP (Fin.cons 0 (fun j ↦ β (rP j.succ) + d j.succ))
              else writeReg β rP (Fin.cons 1 (fun j ↦ β (rP j.succ) + d j.succ))) := by
              have hUpd (b c : ZMod 2) : Function.update
                  (writeReg β rP (Fin.cons b (fun j ↦ β (rP j.succ) + d j.succ))) (rP 0) c =
                  writeReg β rP (Fin.cons c (fun j ↦ β (rP j.succ) + d j.succ)) := by
                funext q
                by_cases hq : q ∈ Set.range rP.wires
                · obtain ⟨i, rfl⟩ := hq
                  cases i using Fin.cases with
                  | zero => rw [Function.update_self, writeReg_apply_reg, Fin.cons_zero]
                  | succ j =>
                      have hne : rP j.succ ≠ rP 0 :=
                        fun h ↦ Fin.succ_ne_zero j (rP.wires.injective h)
                      rw [Function.update_of_ne hne, writeReg_apply_reg, writeReg_apply_reg,
                        Fin.cons_succ, Fin.cons_succ]
                · have hne0 : q ≠ rP 0 := fun h ↦ hq ⟨0, h.symm⟩
                  rw [Function.update_of_ne hne0, writeReg_apply_of_not_mem _ _ _ _ hq,
                    writeReg_apply_of_not_mem _ _ _ _ hq]
              exact lemHex338 (rP 0) (d 0) _ _ ⟨hUpd 0 1, hUpd 1 0⟩ (β (rP 0))
        _ = ket (writeReg β rP (fun i ↦ β (rP i) + d i)) := by
              have hite (f : ZMod 2 → BitAssignment n) (b : ZMod 2) :
                  (if b = 0 then f 0 else f 1) = f b := by
                rcases zmod2_eq_zero_or_one b with rfl | rfl
                · simp only [↓reduceIte]
                · simp only [show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
              rw [hite (fun x ↦ writeReg β rP (Fin.cons x (fun j ↦ β (rP j.succ) + d j.succ)))]
              apply congrArg ket
              apply congrArg (writeReg β rP)
              funext i
              cases i using Fin.cases with
              | zero => simp only [Fin.cons_zero]
              | succ _ => rfl
end PrunedDataQrom
end PrunedQromLookup
end
end ModPrunedQromLookup

section ModTwosCompAndWire0Cancel
@[expose] public section
namespace TwosCompAndWire0CancelAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end TwosCompAndWire0CancelAlt
namespace TwosCompAndWire0Cancel
open Operator Matrix QProg HermitianMat SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.DyadicSubgridToeplitz128
open KaratsubaQft64Matrix
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
section PermBridge
variable {Var : Type} {n : ℕ}
def fwdPermMatrix {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j ↦ if σ j = i then 1 else 0
@[simp] theorem fwdPermMatrix_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (i j : Fin N) :
    fwdPermMatrix σ i j = if σ j = i then 1 else 0 := rfl
theorem fwdPermMatrix_refl (N : ℕ) : fwdPermMatrix (Equiv.refl (Fin N)) = 1 := by
  ext i j
  simp [fwdPermMatrix, Matrix.one_apply, eq_comm]
theorem fwdPermMatrix_mul {N : ℕ} (σ₁ σ₂ : Equiv.Perm (Fin N)) :
    fwdPermMatrix σ₂ * fwdPermMatrix σ₁ = fwdPermMatrix (σ₁.trans σ₂) := by
  ext i j
  simp only [Matrix.mul_apply, fwdPermMatrix_apply, Equiv.trans_apply]
  rw [Finset.sum_eq_single (σ₁ j) (fun k _ hk ↦ by simp [hk.symm]) (by simp)]
  simp only [↓reduceIte, mul_one]
  rfl
theorem fwdPermMatrix_conjTranspose {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (fwdPermMatrix σ)ᴴ = fwdPermMatrix σ.symm := by
  ext i j
  simp [fwdPermMatrix_apply, Matrix.conjTranspose_apply, σ.symm_apply_eq, eq_comm]
def fwdPermUnitary {N : ℕ} (σ : Equiv.Perm (Fin N)) : Unitary N :=
  ⟨fwdPermMatrix σ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, fwdPermMatrix_conjTranspose,
      fwdPermMatrix_mul, Equiv.symm_trans_self, fwdPermMatrix_refl]⟩
theorem fwdPermUnitary_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (i j : Fin N) :
    (fwdPermUnitary σ).1 i j = if σ j = i then 1 else 0 := rfl
@[simp] theorem fwdPermUnitary_mulVec_single {N : ℕ} (σ : Equiv.Perm (Fin N)) (j : Fin N) :
    (fwdPermUnitary σ).1.mulVec (Pi.single j 1) = Pi.single (σ j) 1 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, fwdPermUnitary_apply, eq_comm]
@[simp] theorem fwdPermUnitary_refl (N : ℕ) : fwdPermUnitary (Equiv.refl (Fin N)) = 1 :=
  Subtype.ext (fwdPermMatrix_refl N)
theorem fwdPermUnitary_trans {N : ℕ} (σ₁ σ₂ : Equiv.Perm (Fin N)) :
    fwdPermUnitary (σ₁.trans σ₂) = fwdPermUnitary σ₂ * fwdPermUnitary σ₁ :=
  Subtype.ext (fwdPermMatrix_mul σ₁ σ₂).symm
@[simp] theorem fwdPermUnitary_inv {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (fwdPermUnitary σ)⁻¹ = fwdPermUnitary σ.symm := by
  apply inv_eq_of_mul_eq_one_right
  rw [← fwdPermUnitary_trans, Equiv.symm_trans_self, fwdPermUnitary_refl]
theorem fwdPermUnitary_conjTranspose {N : ℕ} (σ : Equiv.Perm (Fin N)) : (fwdPermUnitary σ).1ᴴ
    = (fwdPermUnitary σ.symm).1 := fwdPermMatrix_conjTranspose σ
theorem fwdPermUnitary_mul_self_of_symm_eq {N : ℕ} (σ : Equiv.Perm (Fin N)) (h : σ.symm = σ) :
    fwdPermUnitary σ * fwdPermUnitary σ = 1 := by
  calc fwdPermUnitary σ * fwdPermUnitary σ
      = fwdPermUnitary σ * (fwdPermUnitary σ)⁻¹ := by rw [fwdPermUnitary_inv, h]
    _ = 1 := mul_inv_cancel _
theorem fwdPermUnitary_conj_diagonal {N : ℕ} (σ : Equiv.Perm (Fin N)) (d : Fin N → ℂ) :
    (fwdPermUnitary σ).1ᴴ * Matrix.diagonal d * (fwdPermUnitary σ).1 =
      Matrix.diagonal (d ∘ σ) := by
  rw [fwdPermUnitary_conjTranspose]
  ext i j
  simp only [Matrix.mul_apply, fwdPermUnitary_apply, Matrix.diagonal_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (σ j) (fun k _ hk ↦ by simp [hk.symm]) (by simp)]
  simp only [↓reduceIte, mul_one]
  rw [Finset.sum_eq_single (σ i)
    (fun k _ hk ↦ by
      have hne : σ.symm k ≠ i := fun hh ↦ hk (by rw [← hh, Equiv.apply_symm_apply])
      simp [hne])
    (by simp)]
  by_cases hij : i = j <;> simp [hij, σ.injective.eq_iff]
def StoreConst [Fintype Var] [DecidableEq Var] (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ ↦ M) =
    (fun _ ↦ M')
namespace StoreConst
section WithVar
variable [Fintype Var] [DecidableEq Var]
theorem circuit (c : Circuit n) : StoreConst (.circuit c : DynamicCircuit Var n) :=
  GridGuard654ReflAux.StoreConst.circuit c
theorem seq {d₁ d₂ : DynamicCircuit Var n} (h₁ : StoreConst d₁) (h₂ : StoreConst d₂) :
    StoreConst (.seq d₁ d₂) :=
  GridGuard654ReflAux.StoreConst.seq h₁ h₂
theorem andUncompute [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) :
    StoreConst (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂) :=
  GridGuard654ReflAux.StoreConst.andUncompute v c₁ c₂ anc h₁₂
theorem wrapDynamic [NeZero (2 ^ n)] (v : Var) (s : TempAndStep n) {inner : DynamicCircuit Var n}
    (h_in : StoreConst inner) : StoreConst (s.wrapDynamic v inner) :=
  GridGuard654ReflAux.StoreConst.wrapDynamic v s h_in
theorem gidneyAdderAuxDyn [NeZero (2 ^ n)] (v : Var) (k : ℕ) (uWires : Fin (k + 1) → Wire n)
    (rT : QRegister (k + 1) n) (rC : QRegister k n) (cin : Wire n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, cin ≠ uWires j) (hcin_T : cin ∉ rT.image)
    (hcin_C : cin ∉ rC.image) : StoreConst
      (_root_.QuantumComputation.Specs.StoppingPowerSolution.gidneyAdderAuxDyn v k uWires rT rC cin
      hu_T
    hu_C hdisj_TC hcin_u hcin_T hcin_C) := by
  induction k generalizing cin with
  | zero =>
      simp only [_root_.QuantumComputation.Specs.StoppingPowerSolution.gidneyAdderAuxDyn]
      exact circuit _
  | succ k ih =>
      simp only [_root_.QuantumComputation.Specs.StoppingPowerSolution.gidneyAdderAuxDyn]
      exact wrapDynamic v _ (ih (fun j ↦ uWires j.succ)
        (rT.slice 1 (k + 1) (by omega)) (rC.slice 1 k (by omega)) (rC 0)
        (fun j hj ↦ hu_T j.succ (QRegister.image_compose_subset rT _ hj))
        (fun j hj ↦ hu_C j.succ (QRegister.image_compose_subset rC _ hj))
        ((hdisj_TC.compose_left _).compose_right _)
        (fun j h ↦ hu_C j.succ (QRegister.mem_image rC _ |>.mpr ⟨0, h⟩))
        (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj))
        (QRegExt.head_not_mem_tail_image rC))
theorem gidneyAdderDyn [NeZero (2 ^ n)] (v : Var) (k : ℕ) (uWires : Fin (k + 2) → Wire n)
    (rT : QRegister (k + 2) n) (rC : QRegister (k + 1) n) (hu_T : ∀ j, uWires j ∉ rT.image)
    (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) : StoreConst
    (_root_.QuantumComputation.Specs.StoppingPowerSolution.gidneyAdderDyn v k uWires rT rC hu_T hu_C
      hdisj_TC) := by
  unfold _root_.QuantumComputation.Specs.StoppingPowerSolution.gidneyAdderDyn
  exact wrapDynamic v _ (gidneyAdderAuxDyn v k (fun j ↦ uWires j.succ)
    (rT.slice 1 (k + 1) (by omega)) (rC.slice 1 k (by omega)) (rC 0)
    (fun j hj ↦ hu_T j.succ (QRegister.image_compose_subset rT _ hj))
    (fun j hj ↦ hu_C j.succ (QRegister.image_compose_subset rC _ hj))
    ((hdisj_TC.compose_left _).compose_right _)
    (fun j h ↦ hu_C j.succ (QRegister.mem_image rC _ |>.mpr ⟨0, h⟩))
    (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj))
    (QRegExt.head_not_mem_tail_image rC))
end WithVar
end StoreConst
theorem realizesEmbeddedUnitary_of_wp_eq_and_mul_proj [Fintype Var] [DecidableEq Var]
    [NeZero (2 ^ n)] {k m : ℕ} (rAct : QRegister k n) (rWork : QRegister m n)
    (u : Unitary (2 ^ k)) (d : DynamicCircuit Var n) (c_ref : Circuit n)
    (hconst : StoreConst d) (hwp : ∀ M : Observable (Fin (2 ^ n)), CQAssertion.restrictToZeroAncilla
    (wp d.compile (fun _ ↦ M)) rWork = CQAssertion.restrictToZeroAncilla (wpQAssignCompat
    c_ref.eval (fun _ ↦ M)) rWork) (hproj : c_ref.eval.1 * rWork.basisOutcomeProjector 0 =
    (rAct.embedUnitary u).1 * rWork.basisOutcomeProjector 0) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d :=
  GridGuard654ReflAux.realizesEmbeddedUnitary_of_wp_eq_and_mul_proj
    rAct rWork u d c_ref hconst hwp hproj
theorem realizes_fwdPermUnitary_of_regVal [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    {k m : ℕ} (rAct : QRegister k n) (rWork : QRegister m n) (σ : Equiv.Perm (Fin (2 ^ k)))
    (d : DynamicCircuit Var n) (c_ref : Circuit n) (f : BitAssignment n → BitAssignment n)
    (hconst : StoreConst d) (hwp : ∀ M : Observable (Fin (2 ^ n)), CQAssertion.restrictToZeroAncilla
    (wp d.compile (fun _ ↦ M)) rWork = CQAssertion.restrictToZeroAncilla (wpQAssignCompat
    c_ref.eval (fun _ ↦ M)) rWork) (hperm : ClassicalPerm c_ref f)
    (hout : ∀ β w, w ∉ rAct.image → f β w = β w) (hval : ∀ β, (∀ j : Fin m, β (rWork j) = 0) →
    regVal rAct (f β) = (σ ⟨regVal rAct β, regVal_lt_two_pow rAct β⟩).val) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (fwdPermUnitary σ) d
    := by
  refine realizesEmbeddedUnitary_of_wp_eq_and_mul_proj rAct rWork (fwdPermUnitary σ) d c_ref
    hconst hwp ?_
  apply matrix_ext_basisKet
  intro β
  simp only [← Matrix.mulVec_mulVec, register_basisOutcomeProjector_zero_mulVec_basisKet]
  by_cases h0 : ∀ j : Fin m, β (rWork j) = 0
  · simp only [h0, implies_true, ↓reduceIte]
    rw [hperm β]
    let g_idx := (basisBitsEquiv n).symm β
    have hg_bits : basisBits n g_idx = β := basisBits_basisBitsEquiv_symm_eq β
    have hextr_eq : rAct.extractIndex g_idx = ⟨regVal rAct β, regVal_lt_two_pow rAct β⟩ := by
      ext
      exact (regVal_eq_extractIndex_val rAct β).symm
    let outIdx := σ (rAct.extractIndex g_idx)
    rw [QRegister.embedUnitary_val, basisKet, basisState, rAct.embedMatrix_mulVec_single_factors,
      fwdPermUnitary_mulVec_single, QRegister.tensorState_single_replaceIndex,
      pi_single_eq_basisKet, pi_single_eq_basisKet, basisBits_basisBitsEquiv_symm_eq]
    apply congrArg basisKet
    have hbits_eq : (fun i : Fin k ↦ f β (rAct i)) = basisBits k outIdx := by
      apply (basisBitsEquiv k).symm.injective
      ext
      rw [← bitsVal_eq_symm_val, ← bitsVal_eq_symm_val, bitsVal_basisBits]
      change regVal rAct (f β) = outIdx.val
      dsimp only [outIdx]
      rw [hextr_eq]
      exact hval β h0
    funext w
    by_cases hw : w ∈ Set.range rAct.wires
    · obtain ⟨i, rfl⟩ := hw
      rw [rAct.basisBits_replaceIndex_apply]
      exact congrFun hbits_eq i
    · have hw_img : w ∉ rAct.image := fun hm ↦ hw ((QRegister.mem_image rAct w).mp hm)
      rw [rAct.basisBits_replaceIndex_of_not_mem g_idx outIdx w hw, hg_bits, hout β w hw_img]
  · simp [h0]
theorem regVal_concat {q₁ q₂ : ℕ} (r₁ : QRegister q₁ n) (r₂ : QRegister q₂ n)
    (hdisj : r₁.DisjointWires r₂) (β : BitAssignment n) :
    regVal (r₁.concat r₂ hdisj) β = regVal r₁ β + 2 ^ q₁ * regVal r₂ β := by
  unfold regVal bitsVal
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only
    rw [QRegister.concat_apply_left]
    rfl
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [QRegister.concat_apply_right, Fin.val_natAdd, pow_add]
    ring
end PermBridge
section SmToTwos
variable {Var : Type} {n : ℕ}
def smToTwosAxisFun (k : ℕ) (u : Fin (2 ^ (k + 3))) : Fin (2 ^ (k + 3)) :=
  let p := 2 ^ (k + 2)
  let m := u.val % p
  if u.val < p then ⟨m, by have : m < p := Nat.mod_lt _ (Nat.two_pow_pos _); rw [pow_succ']; omega⟩
  else ⟨p + (p - m) % p, by
    have : (p - m) % p < p := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [pow_succ']; omega⟩
theorem smToTwosAxisFun_val (k : ℕ) (u : Fin (2 ^ (k + 3))) : (smToTwosAxisFun k u).val = if
    u.val < 2 ^ (k + 2) then u.val % 2 ^ (k + 2) else 2 ^ (k + 2) +
    (2 ^ (k + 2) - u.val % 2 ^ (k + 2)) % 2 ^ (k + 2) := by
  dsimp [smToTwosAxisFun]
  split_ifs <;> rfl
theorem smToTwosAxisFun_involutive (k : ℕ) : Function.Involutive (smToTwosAxisFun k) := by
  intro u; apply Fin.ext
  rw [smToTwosAxisFun_val, smToTwosAxisFun_val]
  set p := 2 ^ (k + 2)
  have hu : u.val < 2 * p := by simpa only [p, pow_succ'] using u.isLt
  by_cases hlt : u.val < p
  · rw [ite_eq_left hlt, Nat.mod_eq_of_lt hlt, ite_eq_left hlt, Nat.mod_eq_of_lt hlt]
  · rw [ite_eq_right hlt]
    set d := u.val - p
    have hd_lt : d < p := by omega
    have hu_eq : u.val = d + p := by omega
    have hmod_u : u.val % p = d := by rw [hu_eq, Nat.add_mod_right, Nat.mod_eq_of_lt hd_lt]
    rw [hmod_u]
    by_cases hd0 : d = 0
    · rw [hd0]
      have hpp : ¬ p < p := lt_irrefl p
      rw [Nat.sub_zero, Nat.mod_self, add_zero, ite_eq_right hpp, Nat.mod_self,
          Nat.sub_zero, Nat.mod_self, add_zero, hu_eq, hd0, zero_add]
    · have hlt2 : p - d < p := by omega
      have hge : ¬ p + (p - d) < p := by omega
      have hmod2 : (p + (p - d)) % p = p - d := by
        rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
      rw [Nat.mod_eq_of_lt hlt2, ite_eq_right hge, hmod2,
          show p - (p - d) = d by omega, Nat.mod_eq_of_lt hd_lt, hu_eq, add_comm]
def smToTwosAxisPerm (k : ℕ) : Equiv.Perm (Fin (2 ^ (k + 3))) :=
  (smToTwosAxisFun_involutive k).toPerm
@[simp] theorem smToTwosAxisPerm_self (k : ℕ) (u : Fin (2 ^ (k + 3))) : smToTwosAxisPerm k
    (smToTwosAxisPerm k u) = u := smToTwosAxisFun_involutive k u
lemma two_pow_sub_helper {p p2 uv : ℕ} (h2 : p2 = p + p) (hu : uv < p + p) :
    p + (p - (uv - p)) = p2 - (uv - p) := by
  omega
lemma smToTwos_eq_p_helper {p p2 uv : ℕ} (h2 : p2 = p + p) (hu : uv < p + p) :
    (if uv < p then uv else if uv = p then p else p2 - (uv - p)) = p ↔ uv = p := by
  split_ifs <;> omega
theorem smToTwosAxisPerm_val (k : ℕ) (u : Fin (2 ^ (k + 3))) : (smToTwosAxisPerm k u).val = if
    u.val < 2 ^ (k + 2) then u.val else if u.val = 2 ^ (k + 2) then 2 ^ (k + 2) else 2 ^
    (k + 3) - (u.val - 2 ^ (k + 2)) := by
  change (smToTwosAxisFun k u).val = _
  rw [smToTwosAxisFun_val]
  set p := 2 ^ (k + 2)
  have hu2 : 2 ^ (k + 3) = p + p := by dsimp [p]; rw [pow_succ']; ring
  have hu : u.val < p + p := u.isLt.trans_eq hu2
  by_cases hlt : u.val < p
  · simp only [hlt, ↓reduceIte, Nat.mod_eq_of_lt hlt]
  · simp only [hlt, ↓reduceIte]
    have hlt_sub : u.val - p < p := by omega
    have hm_eq : u.val % p = u.val - p := by
      conv_lhs => rw [show u.val = (u.val - p) + p * 1 by omega]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_sub]
    rw [hm_eq]
    by_cases heq : u.val = p
    · rw [heq]
      simp only [↓reduceIte, Nat.sub_self, Nat.sub_zero, Nat.mod_self, add_zero]
    · simp only [heq, ↓reduceIte, Nat.mod_eq_of_lt (show p - (u.val - p) < p by omega)]
      exact two_pow_sub_helper hu2 hu
theorem smToTwosAxisPerm_eq_negZero_iff (k : ℕ) (u : Fin (2 ^ (k + 3))) :
    (smToTwosAxisPerm k u).val = 2 ^ (k + 2) ↔ u.val = 2 ^ (k + 2) := by
  rw [smToTwosAxisPerm_val]
  have h2 : 2 ^ (k + 3) = 2 ^ (k + 2) + 2 ^ (k + 2) := by rw [pow_succ']; ring
  exact smToTwos_eq_p_helper h2 (u.isLt.trans_eq h2)
def smToTwosAxisUnitary (k : ℕ) : Unitary (2 ^ (k + 3)) := fwdPermUnitary (smToTwosAxisPerm k)
private theorem compPow2_smToTwos (k : ℕ) {u : Fin (2 ^ (k + 3))}
    (hu : u.val ≠ 2 ^ (k + 2)) :
    let p := 2 ^ (k + 2)
    let w := (smToTwosAxisPerm k u).val
    ((w % p : ℕ) : ℤ) - (p : ℤ) * ((w / p : ℕ) : ℤ) =
      (-1 : ℤ) ^ (u.val / p) * ((u.val % p : ℕ) : ℤ) := by
  intro p w
  have hw : w = if u.val < p then u.val else if u.val = p then p else 2 * p - (u.val - p) := by
    simpa [w, p, pow_succ', two_mul] using smToTwosAxisPerm_val k u
  have hlt2 : u.val < 2 * p := by simpa [p, pow_succ', two_mul] using u.isLt
  rw [hw]
  by_cases hlt : u.val < p
  · simp only [hlt, ↓reduceIte, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, _root_.pow_zero]
    omega
  · simp only [hlt, show u.val ≠ p from hu, ↓reduceIte]
    have hp : 0 < p := Nat.two_pow_pos _
    have hsub : u.val - p < p := by omega
    have hudiv : u.val / p = 1 := by
      rw [show u.val = (u.val - p) + p * 1 by omega, Nat.add_mul_div_left _ _ hp,
        Nat.div_eq_of_lt hsub, zero_add]
    have humod : u.val % p = u.val - p := by
      conv_lhs => rw [show u.val = (u.val - p) + p * 1 by omega]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsub]
    have hw_split : 2 * p - (u.val - p) = (p - (u.val - p)) + p * 1 := by omega
    have hw_lt : p - (u.val - p) < p := by omega
    rw [hudiv, humod, pow_one, hw_split, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hw_lt,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw_lt]
    omega
theorem twosComp6Int_smToTwosAxisPerm {u : Fin 64} (hu : u.val ≠ 32) :
    twosComp6Int (smToTwosAxisPerm 3 u) = (-1 : ℤ) ^ (u.val / 32) * (u.val % 32 : ℤ) :=
  compPow2_smToTwos 3 hu
def twosComp8Int (u : Fin 256) : ℤ := ((u.val % 128 : ℕ) : ℤ) - 128 * ((u.val / 128 : ℕ) : ℤ)
theorem twosComp8Int_smToTwosAxisPerm {u : Fin 256} (hu : u.val ≠ 128) :
    twosComp8Int (smToTwosAxisPerm 5 u) = (-1 : ℤ) ^ (u.val / 128) * (u.val % 128 : ℤ) :=
  compPow2_smToTwos 5 hu
theorem bitsVal_flip_add_self :
    ∀ {q : ℕ} (γ : BitAssignment q), bitsVal (fun i ↦ γ i + 1) + bitsVal γ = 2 ^ q - 1
  | 0, _ => by simp [bitsVal]
  | q + 1, γ => by
      have hbit : ∀ b : ZMod 2, (b + 1).val + b.val = 1 := by decide
      have htail : ∀ δ : BitAssignment (q + 1),
          bitsVal δ = (δ 0).val + 2 * bitsVal (fun i : Fin q ↦ δ i.succ) := fun δ ↦ by
        unfold bitsVal; rw [Fin.sum_univ_succ, Finset.mul_sum]
        simp only [Fin.val_zero, _root_.pow_zero, mul_one]; congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [Fin.val_succ, pow_succ]; ring
      rw [htail, htail]
      have ih := bitsVal_flip_add_self (fun i : Fin q ↦ γ i.succ)
      have hb0 := hbit (γ 0)
      have hpow : 1 ≤ 2 ^ q := Nat.one_le_two_pow
      rw [pow_succ']; omega
def cnotFanoutCircuit : {q n : ℕ} → (wCtrl : Wire n) → (r : QRegister q n) →
    (wCtrl ∉ r.image) → Circuit n
  | 0, _, _, _, _ => .identity
  | q + 1, _, wCtrl, r, hCtrl =>
      have hw0 : wCtrl ≠ r 0 := QRegister.ne_apply_of_not_mem_image r wCtrl hCtrl 0
      have htail : wCtrl ∉ (r.slice 1 q (by omega)).image :=
        fun hm ↦ hCtrl (QRegister.image_compose_subset r _ hm)
      Circuit.CNOT wCtrl (r 0) hw0 ;;ᶜ cnotFanoutCircuit wCtrl (r.slice 1 q (by omega)) htail
@[simp] theorem count_cnotFanoutCircuit_toff :
    ∀ {q n : ℕ} (wCtrl : Wire n) (r : QRegister q n) (hCtrl : wCtrl ∉ r.image),
      (cnotFanoutCircuit wCtrl r hCtrl).count .TOFF = 0
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, _, _ => by simp [cnotFanoutCircuit, count_cnotFanoutCircuit_toff]
@[simp] theorem count_cnotFanoutCircuit_t :
    ∀ {q n : ℕ} (wCtrl : Wire n) (r : QRegister q n) (hCtrl : wCtrl ∉ r.image),
      (cnotFanoutCircuit wCtrl r hCtrl).count .T = 0
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, _, _ => by simp [cnotFanoutCircuit, count_cnotFanoutCircuit_t]
theorem support_cnotFanoutCircuit_subset :
    ∀ {q n : ℕ} (wCtrl : Wire n) (r : QRegister q n) (hCtrl : wCtrl ∉ r.image),
      (cnotFanoutCircuit wCtrl r hCtrl).support ⊆ insert wCtrl r.image
  | 0, _, _, _, _ => by simp [cnotFanoutCircuit]
  | q + 1, _, wCtrl, r, hCtrl => by
      rw [cnotFanoutCircuit, QRegExt.image_head_tail, Circuit.support_seq]
      refine Finset.union_subset ?_ ((support_cnotFanoutCircuit_subset _ _ _).trans ?_)
      · simp [Circuit.support_gate, QRegister.image_pair]
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx')
def xorCtrlMap {q n : ℕ} (wCtrl : Wire n) (r : QRegister q n) (β : BitAssignment n) :
    BitAssignment n := fun w ↦ if w ∈ r.image then β w + β wCtrl else β w
theorem classicalPerm_cnotFanoutCircuit :
    ∀ {q n : ℕ} (wCtrl : Wire n) (r : QRegister q n) (hCtrl : wCtrl ∉ r.image),
      ClassicalPerm (cnotFanoutCircuit wCtrl r hCtrl) (xorCtrlMap wCtrl r)
  | 0, _, wCtrl, r, _ => by
      have h : xorCtrlMap wCtrl r = id := by
        funext β w; simp [xorCtrlMap, show w ∉ r.image by simp [QRegister.mem_image]]
      rw [cnotFanoutCircuit, h]; exact ClassicalPerm.identity
  | q + 1, _, wCtrl, r, hCtrl => by
      rw [cnotFanoutCircuit]
      have hw0 : wCtrl ≠ r 0 := QRegister.ne_apply_of_not_mem_image r wCtrl hCtrl 0
      have htail : wCtrl ∉ (r.slice 1 q (by omega)).image :=
        fun hm ↦ hCtrl (QRegister.image_compose_subset r _ hm)
      have hseq := (ClassicalPerm.CNOT wCtrl (r 0) hw0).seq
        (classicalPerm_cnotFanoutCircuit wCtrl (r.slice 1 q (by omega)) htail)
      have heq : (xorCtrlMap wCtrl (r.slice 1 q (by omega)) ∘
          fun β ↦ Function.update β (r 0) (β (r 0) + β wCtrl)) = xorCtrlMap wCtrl r := by
        funext β w; dsimp only [Function.comp_apply, xorCtrlMap]
        rw [QRegExt.image_head_tail]
        by_cases hw : w = r 0
        · subst hw
          have hnot : r 0 ∉ (r.slice 1 q (by omega)).image := QRegExt.head_not_mem_tail_image r
          simp only [hnot, Finset.mem_insert_self, ↓reduceIte, Function.update_self]
        · rw [Function.update_of_ne hw, Function.update_of_ne hw0]
          simp only [Finset.mem_insert, hw, false_or]
      exact heq ▸ hseq
def smToTwosAxisDyn (v : Var) (k : ℕ)
    (rAxis : QRegister (k + 3) n) (rWork : QRegister (k + 2) n)
    (hdisj : rAxis.DisjointWires rWork) : DynamicCircuit Var n :=
  let rMag := rAxis.slice 0 (k + 2) (by omega)
  let wSign := rAxis ⟨k + 2, by omega⟩
  let uWires : Fin (k + 2) → Wire n := Fin.cases wSign (fun _ ↦ rWork 0)
  have hwSign_not_mag : wSign ∉ rMag.image := by
    rw [QRegister.mem_image]; rintro ⟨j, hj⟩
    rw [QRegister.slice_apply] at hj
    have hv := congrArg Fin.val (rAxis.wires.injective hj); dsimp [wSign] at hv; omega
  have hu_mag : ∀ j, uWires j ∉ rMag.image := Fin.cases hwSign_not_mag (fun _ hm ↦
      hdisj.apply_not_mem_left 0 (QRegister.image_compose_subset rAxis _ hm))
  have hu_carry : ∀ j, uWires j ∉ (rWork.slice 1 (k + 1) (by omega)).image :=
    Fin.cases
      (fun hm ↦ hdisj.apply_not_mem_right ⟨k + 2, by omega⟩ (QRegister.image_compose_subset rWork _
        hm))
      (fun _ ↦ QRegExt.head_not_mem_tail_image rWork)
  .seq (.circuit (cnotFanoutCircuit wSign rMag hwSign_not_mag))
    (gidneyAdderDyn v k uWires rMag (rWork.slice 1 (k + 1) (by omega))
      hu_mag hu_carry ((hdisj.compose_left _).compose_right _))
@[simp] theorem count_smToTwosAxisDyn_toff (v : Var) (k : ℕ) (rAxis : QRegister (k + 3) n)
    (rWork : QRegister (k + 2) n) (hdisj : rAxis.DisjointWires rWork) :
    (smToTwosAxisDyn v k rAxis rWork hdisj).count .TOFF = 0 := by
  simp [smToTwosAxisDyn, count_gidneyAdderDyn_toff]
@[simp] theorem count_smToTwosAxisDyn_t (v : Var) (k : ℕ) (rAxis : QRegister (k + 3) n)
    (rWork : QRegister (k + 2) n) (hdisj : rAxis.DisjointWires rWork) :
    (smToTwosAxisDyn v k rAxis rWork hdisj).count .T = 4 * (k + 1) := by
  simp [smToTwosAxisDyn, count_gidneyAdderDyn_t]
theorem smToTwosAxisDyn_realizes [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] (v : Var)
    (k : ℕ) (rAxis : QRegister (k + 3) n) (rWork : QRegister (k + 2) n)
    (hdisj : rAxis.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAxis rWork
    (smToTwosAxisUnitary k) (smToTwosAxisDyn v k rAxis rWork hdisj) := by
  let rMag := rAxis.slice 0 (k + 2) (by omega)
  let wSign := rAxis ⟨k + 2, by omega⟩
  let rCarry := rWork.slice 1 (k + 1) (by omega)
  let uWires : Fin (k + 2) → Wire n := Fin.cases wSign (fun _ ↦ rWork 0)
  have hwSign_not_mag : wSign ∉ rMag.image := by
    rw [QRegister.mem_image]; rintro ⟨j, hj⟩
    rw [QRegister.slice_apply] at hj
    have hv := congrArg Fin.val (rAxis.wires.injective hj); dsimp [wSign] at hv; omega
  have hu_mag : ∀ j, uWires j ∉ rMag.image := Fin.cases hwSign_not_mag (fun _ hm ↦
      hdisj.apply_not_mem_left 0 (QRegister.image_compose_subset rAxis _ hm))
  have hu_carry : ∀ j, uWires j ∉ rCarry.image :=
    Fin.cases
      (fun hm ↦ hdisj.apply_not_mem_right ⟨k + 2, by omega⟩ (QRegister.image_compose_subset rWork _
        hm))
      (fun _ ↦ QRegExt.head_not_mem_tail_image rWork)
  have hdisj_MC : rMag.DisjointWires rCarry := (hdisj.compose_left _).compose_right _
  obtain ⟨fAdd, hpermAdd, houtAdd, hvalAdd, hwpAdd⟩ :=
    gidneyAdder_correct (Var := Var) v k uWires rMag rCarry hu_mag hu_carry hdisj_MC
  let cPre := cnotFanoutCircuit wSign rMag hwSign_not_mag
  have hcPre_disj : Disjoint cPre.support rWork.image := by
    refine Finset.disjoint_of_subset_left (support_cnotFanoutCircuit_subset wSign rMag
      hwSign_not_mag) ?_
    rw [Finset.disjoint_insert_left]
    exact ⟨hdisj.apply_not_mem_right _,
      Finset.disjoint_of_subset_left (QRegister.image_compose_subset rAxis _)
        ((QRegExt.disjointWires_iff_disjoint_image rAxis rWork).mp hdisj)⟩
  let cTot := cPre ;;ᶜ gidneyAdderCircuit k uWires rMag rCarry hu_mag hu_carry hdisj_MC
  let fTot := fAdd ∘ xorCtrlMap wSign rMag
  have houtMag (γ : BitAssignment n) (w : Wire n) (hw : w ∉ rMag.image) : fTot γ w = γ w := by
    dsimp only [fTot, Function.comp_apply]
    rw [houtAdd _ w hw]
    simp only [xorCtrlMap, hw, ↓reduceIte]
  refine realizes_fwdPermUnitary_of_regVal rAxis rWork (smToTwosAxisPerm k)
    (smToTwosAxisDyn v k rAxis rWork hdisj) cTot fTot ((StoreConst.circuit cPre).seq
    (StoreConst.gidneyAdderDyn v k uWires rMag rCarry hu_mag hu_carry hdisj_MC)) (fun M ↦ ?_)
    ((classicalPerm_cnotFanoutCircuit wSign rMag hwSign_not_mag).seq hpermAdd)
    (fun β w hw ↦ houtMag β w (fun hm ↦ hw (QRegister.image_compose_subset rAxis _ hm)))
    (fun β h0 ↦ ?_)
  · calc CQAssertion.restrictToZeroAncilla
          (wp (smToTwosAxisDyn v k rAxis rWork hdisj).compile (fun _ ↦ M)) rWork
      _ = wpQAssignCompat cPre.eval
            (CQAssertion.restrictToZeroAncilla
              (wp (gidneyAdderDyn v k uWires rMag rCarry hu_mag hu_carry hdisj_MC).compile
                (fun _ ↦ M)) rWork) := by
            simp only [smToTwosAxisDyn, DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit,
              wp_qSeq, DynCircuitExt.wp_circuit_compile_compat]
            exact restrictToZeroAncilla_wp_qAssign_comm_of_disjoint cPre rWork hcPre_disj _
      _ = wpQAssignCompat cPre.eval
            (CQAssertion.restrictToZeroAncilla
              (wpQAssignCompat (gidneyAdderCircuit k uWires rMag rCarry hu_mag hu_carry
                hdisj_MC).eval
                (fun _ ↦ M)) rWork) := by
            rw [restrictAssertionToZeroAncilla_head_tail _ rWork,
                restrictAssertionToZeroAncilla_comm _ (QRegister.singleton (rWork 0)) rCarry,
                hwpAdd (fun _ ↦ M) (fun _ _ ↦ rfl),
                ← restrictAssertionToZeroAncilla_comm _ (QRegister.singleton (rWork 0)) rCarry,
                ← restrictAssertionToZeroAncilla_head_tail _ rWork]
      _ = CQAssertion.restrictToZeroAncilla (wpQAssignCompat cTot.eval (fun _ ↦ M)) rWork := by
            rw [← restrictToZeroAncilla_wp_qAssign_comm_of_disjoint cPre rWork hcPre_disj _]
            simp only [cTot, Circuit.eval_seq, wpQAssignCompat_comp]
  · have hAxisSplit : ∀ γ : BitAssignment n,
        regVal rAxis γ = regVal rMag γ + 2 ^ (k + 2) * (γ wSign).val := fun γ ↦ by
      have heqReg : rMag.concat (QRegister.singleton wSign) (QRegister.disjoint_iff.mpr fun j
          _ h ↦ hwSign_not_mag ((QRegister.mem_image rMag _).mpr ⟨j, h⟩)) = rAxis := by
        apply TwosCompAndWire0CancelAlt.qreg_ext; intro idx
        by_cases hlt : idx.val < k + 2
        · have hi : idx = Fin.castAdd 1 ⟨idx.val, hlt⟩ := Fin.ext rfl
          rw [hi, QRegister.concat_apply_left]
          dsimp only [rMag]; rw [QRegister.slice_apply]
          exact congrArg rAxis.wires (Fin.ext (by dsimp; omega))
        · have hi : idx = Fin.natAdd (k + 2) ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hi, QRegister.concat_apply_right]
          rfl
      rw [← heqReg, regVal_concat]
      simp [regVal, bitsVal, _root_.pow_zero]
    let β₁ := xorCtrlMap wSign rMag β
    have hCarry0 : ∀ i : Fin (k + 1), β₁ (rCarry i) = 0 := fun i ↦ by
      have hni : rCarry i ∉ rMag.image := hdisj_MC.apply_not_mem_left i
      dsimp only [β₁, xorCtrlMap]; simp only [hni, ↓reduceIte]
      rw [QRegister.slice_apply]; exact h0 ⟨1 + i.val, by omega⟩
    have hwSign_keep : fTot β wSign = β wSign := houtMag β wSign hwSign_not_mag
    have hw0_keep : β₁ (rWork 0) = 0 := by
      have hn0 : rWork 0 ∉ rMag.image :=
        fun hm ↦ hdisj.apply_not_mem_left 0 (QRegister.image_compose_subset rAxis _ hm)
      dsimp only [β₁, xorCtrlMap]; simp [hn0, h0 0]
    have huVal : bitsVal (fun j ↦ β₁ (uWires j)) = (β wSign).val := by
      unfold bitsVal; rw [Fin.sum_univ_succ]
      have hsign1 : β₁ wSign = β wSign := by dsimp [β₁, xorCtrlMap]; simp [hwSign_not_mag]
      simp only [uWires, Fin.cases_zero, Fin.cases_succ, hsign1, hw0_keep,
        ZMod.val_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, _root_.pow_zero,
          mul_one]
    rw [hAxisSplit (fTot β), hwSign_keep]
    dsimp only [fTot, Function.comp_apply]
    change regVal rMag (fAdd β₁) + 2 ^ (k + 2) * (β wSign).val = _
    rw [hvalAdd β₁ hCarry0, huVal, smToTwosAxisPerm_val]
    set p := 2 ^ (k + 2)
    have hp : 0 < p := Nat.two_pow_pos _
    have hm : regVal rMag β < p := regVal_lt_two_pow rMag β
    have hp2 : 2 ^ (k + 3) = p + p := by dsimp [p]; rw [pow_succ']; ring
    have hb_cases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases hb_cases (β wSign) with hs0 | hs1
    · have hβ₁_eq : regVal rMag β₁ = regVal rMag β :=
        regVal_congr rMag fun j ↦ by
          dsimp [β₁, xorCtrlMap]; simp [(QRegister.mem_image rMag (rMag j)).mpr ⟨j, rfl⟩, hs0]
      have hAxisβ : regVal rAxis β = regVal rMag β := by rw [hAxisSplit β, hs0]; simp
      rw [hβ₁_eq, hs0, ZMod.val_zero, mul_zero, add_zero, add_zero, Nat.mod_eq_of_lt hm]
      simp only [hAxisβ, hm, ↓reduceIte]
    · have hβ₁_eq : regVal rMag β₁ = p - 1 - regVal rMag β := by
        have hfl : regVal rMag β₁ = bitsVal (fun j : Fin (k + 2) ↦ β (rMag j) + 1) := by
          unfold regVal bitsVal
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          dsimp [β₁, xorCtrlMap]
          simp [(QRegister.mem_image rMag (rMag j)).mpr ⟨j, rfl⟩, hs1]
        have hsum := bitsVal_flip_add_self (fun j : Fin (k + 2) ↦ β (rMag j))
        change _ + regVal rMag β = p - 1 at hsum; rw [hfl]; omega
      have hone : (1 : ZMod 2).val = 1 := by decide
      have hAxisβ : regVal rAxis β = regVal rMag β + p := by
        rw [hAxisSplit β, hs1, hone, mul_one]
      have hnlt : ¬ regVal rAxis β < p := by omega
      rw [hβ₁_eq, hs1, hone, mul_one, show p - 1 - regVal rMag β + 1 = p - regVal rMag β by omega]
      simp only [hnlt, ↓reduceIte]
      by_cases hm0 : regVal rMag β = 0
      · have heqp : regVal rAxis β = p := by omega
        simp only [hm0, heqp, ↓reduceIte, Nat.sub_zero, Nat.mod_self, zero_add]
      · have hnep : regVal rAxis β ≠ p := by omega
        have hlt2 : p - regVal rMag β < p := by omega
        simp only [hnep, ↓reduceIte, Nat.mod_eq_of_lt hlt2, hp2]
        omega
noncomputable def embedPerm {q K : ℕ} (sel : QRegister q K) (e : Equiv.Perm (Fin (2 ^ q))) :
    Equiv.Perm (Fin (2 ^ K)) where
  toFun x := sel.replaceIndex x (e (sel.extractIndex x))
  invFun x := sel.replaceIndex x (e.symm (sel.extractIndex x))
  left_inv x := by simp
  right_inv x := by simp
theorem embedUnitary_fwdPermUnitary {q K : ℕ} [NeZero (2 ^ K)]
    (sel : QRegister q K) (e : Equiv.Perm (Fin (2 ^ q))) :
    sel.embedUnitary (fwdPermUnitary e) = fwdPermUnitary (embedPerm sel e) := by
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  rw [QRegister.embedUnitary_val, basisKet, basisState,
    sel.embedMatrix_mulVec_single_factors, fwdPermUnitary_mulVec_single,
    QRegister.tensorState_single_replaceIndex, fwdPermUnitary_mulVec_single]
  rfl
noncomputable def foldAxesPerm {q K : ℕ} (e : Equiv.Perm (Fin (2 ^ q))) :
    {M : ℕ} → (Fin M → QRegister q K) → Equiv.Perm (Fin (2 ^ K))
  | 0, _ => Equiv.refl _
  | M + 1, axes =>
      (embedPerm (axes 0) e).trans (foldAxesPerm e (fun i : Fin M ↦ axes i.succ))
@[simp] theorem foldAxesPerm_zero {q K : ℕ} (e : Equiv.Perm (Fin (2 ^ q)))
    (axes : Fin 0 → QRegister q K) : foldAxesPerm e axes = Equiv.refl _ := rfl
@[simp] theorem foldAxesPerm_succ {q K M : ℕ} (e : Equiv.Perm (Fin (2 ^ q)))
    (axes : Fin (M + 1) → QRegister q K) : foldAxesPerm e axes = (embedPerm (axes 0) e).trans
    (foldAxesPerm e (fun i : Fin M ↦ axes i.succ)) := rfl
attribute [irreducible] foldAxesPerm
theorem foldAxesPerm_extractIndex {q K : ℕ} (e : Equiv.Perm (Fin (2 ^ q))) :
    ∀ {M : ℕ} (axes : Fin M → QRegister q K)
      (_hpair : ∀ a b, a ≠ b → (axes a).DisjointWires (axes b))
      (m : Fin M) (x : Fin (2 ^ K)),
      (axes m).extractIndex (foldAxesPerm e axes x) = e ((axes m).extractIndex x)
  | 0, _, _hpair, m, _ => Fin.elim0 m
  | M + 1, axes, hpair, m, x => by
      have hunch : ∀ {L : ℕ} (sub : Fin L → QRegister q K) (r : QRegister q K),
          (∀ j, r.DisjointWires (sub j)) → ∀ y, r.extractIndex (foldAxesPerm e sub y) =
            r.extractIndex y := by
        intro L; induction L with
        | zero => intros; simp
        | succ L ih =>
            intro sub r hd y
            simp only [foldAxesPerm_succ, Equiv.trans_apply]
            rw [ih (fun j ↦ sub j.succ) r (fun j ↦ hd j.succ)]
            exact r.extractIndex_replaceIndex_of_disjoint (sub 0) (hd 0) y _
      simp only [foldAxesPerm_succ, Equiv.trans_apply]
      rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨m', rfl⟩
      · rw [hunch (fun i : Fin M ↦ axes i.succ) (axes 0)
              (fun j ↦ hpair 0 j.succ (Fin.succ_ne_zero j).symm)]
        simp [embedPerm]
      · rw [foldAxesPerm_extractIndex e (fun i : Fin M ↦ axes i.succ)
              (fun a b hab ↦ hpair a.succ b.succ (Fin.succ_inj.ne.mpr hab)) m']
        congr 1
        exact (axes m'.succ).extractIndex_replaceIndex_of_disjoint (axes 0)
          (hpair m'.succ 0 (Fin.succ_ne_zero m')) x _
theorem foldAxesPerm_outside {q K : ℕ} (e : Equiv.Perm (Fin (2 ^ q))) :
    ∀ {M : ℕ} (axes : Fin M → QRegister q K) (w : Wire K)
      (_ : ∀ m, w ∉ Set.range (axes m).wires) (x : Fin (2 ^ K)),
      basisBits K (foldAxesPerm e axes x) w = basisBits K x w
  | 0, _, _, _, _ => by simp
  | M + 1, axes, w, hout, x => by
      simp only [foldAxesPerm_succ, Equiv.trans_apply]
      rw [foldAxesPerm_outside e (fun i : Fin M ↦ axes i.succ) w (fun m ↦ hout m.succ)]
      change basisBits K ((axes 0).replaceIndex x (e ((axes 0).extractIndex x))) w = _
      exact (axes 0).basisBits_replaceIndex_of_not_mem _ _ w (hout 0)
theorem foldAxesPerm_self_of_involutive {q K M : ℕ} {e : Equiv.Perm (Fin (2 ^ q))}
    (he : ∀ u, e (e u) = u) (axes : Fin M → QRegister q K)
    (hpair : ∀ a b, a ≠ b → (axes a).DisjointWires (axes b)) (x : Fin (2 ^ K)) :
    foldAxesPerm e axes (foldAxesPerm e axes x) = x := by
  apply (basisBitsEquiv K).injective; funext w
  change basisBits K (foldAxesPerm e axes (foldAxesPerm e axes x)) w = basisBits K x w
  by_cases hmem : ∃ m : Fin M, w ∈ Set.range (axes m).wires
  · rcases hmem with ⟨m, i, rfl⟩
    rw [← QRegister.basisBits_extractIndex, foldAxesPerm_extractIndex e axes hpair m,
        foldAxesPerm_extractIndex e axes hpair m, he, QRegister.basisBits_extractIndex]
  · have hmem' : ∀ m, w ∉ Set.range (axes m).wires := fun m hm ↦ hmem ⟨m, hm⟩
    rw [foldAxesPerm_outside e axes w hmem', foldAxesPerm_outside e axes w hmem']
def smToTwosAxesDyn {K : ℕ} (v : Var) (k : ℕ) :
    {M : ℕ} → (axes : Fin M → QRegister (k + 3) K) →
    (rTarget : QRegister K n) → (rWork : QRegister (k + 2) n) →
    (rTarget.DisjointWires rWork) → DynamicCircuit Var n
  | 0, _, _, _, _ => .identity
  | M + 1, axes, rTarget, rWork, hdisj =>
      .seq (smToTwosAxisDyn v k (rTarget.compose (axes 0)) rWork (hdisj.compose_left (axes 0)))
        (smToTwosAxesDyn v k (fun i : Fin M ↦ axes i.succ) rTarget rWork hdisj)
@[simp] theorem count_smToTwosAxesDyn_toff {K : ℕ} (v : Var) (k : ℕ) :
    ∀ {M : ℕ} (axes : Fin M → QRegister (k + 3) K) (rTarget : QRegister K n)
      (rWork : QRegister (k + 2) n) (hdisj : rTarget.DisjointWires rWork),
      (smToTwosAxesDyn v k axes rTarget rWork hdisj).count .TOFF = 0
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, _, _ => by simp [smToTwosAxesDyn, count_smToTwosAxesDyn_toff]
@[simp] theorem count_smToTwosAxesDyn_t {K : ℕ} (v : Var) (k : ℕ) :
    ∀ {M : ℕ} (axes : Fin M → QRegister (k + 3) K) (rTarget : QRegister K n)
      (rWork : QRegister (k + 2) n) (hdisj : rTarget.DisjointWires rWork),
      (smToTwosAxesDyn v k axes rTarget rWork hdisj).count .T = M * (4 * (k + 1))
  | 0, _, _, _, _ => by simp [smToTwosAxesDyn]
  | M + 1, _, _, _, _ => by
      simp only [smToTwosAxesDyn, DynamicCircuit.count, count_smToTwosAxisDyn_t,
        count_smToTwosAxesDyn_t]
      ring
theorem smToTwosAxesDyn_realizes [Fintype Var] [DecidableEq Var]
    {K : ℕ} [NeZero (2 ^ K)] [NeZero (2 ^ n)] (v : Var) (k : ℕ) :
    ∀ {M : ℕ} (axes : Fin M → QRegister (k + 3) K) (rTarget : QRegister K n)
      (rWork : QRegister (k + 2) n) (hdisj : rTarget.DisjointWires rWork),
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        rTarget rWork (fwdPermUnitary (foldAxesPerm (smToTwosAxisPerm k) axes))
        (smToTwosAxesDyn v k axes rTarget rWork hdisj)
  | 0, axes, rTarget, rWork, _ => by
      rw [foldAxesPerm_zero, fwdPermUnitary_refl]
      exact DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_identity rTarget rWork
  | M + 1, axes, rTarget, rWork, hdisj => by
      have hhead := (smToTwosAxisDyn_realizes v k (rTarget.compose (axes 0)) rWork
        (hdisj.compose_left (axes 0))).widenActive
      rw [smToTwosAxisUnitary, embedUnitary_fwdPermUnitary] at hhead
      have hseq := hhead.seq hdisj
        (smToTwosAxesDyn_realizes v k (fun i : Fin M ↦ axes i.succ) rTarget rWork hdisj)
      have hmul : fwdPermUnitary (foldAxesPerm (smToTwosAxisPerm k) (fun i : Fin M ↦ axes i.succ)) *
          fwdPermUnitary (embedPerm (axes 0) (smToTwosAxisPerm k)) =
          fwdPermUnitary (foldAxesPerm (smToTwosAxisPerm k) axes) := by
        rw [← fwdPermUnitary_trans, ← foldAxesPerm_succ]
      unfold smToTwosAxesDyn
      simpa only [hmul] using hseq
attribute [irreducible] smToTwosAxesDyn
def elec654Axes : Fin 654 → QRegister 6 systemQubits :=
  fun m ↦ QRegister.block (6 * m.val) 6 (by change 6 * m.val + 6 ≤ 3948; omega)
def proj3Axes : Fin 3 → QRegister 8 systemQubits :=
  fun w ↦ QRegister.block (3924 + 8 * w.val) 8 (by change 3924 + 8 * w.val + 8 ≤ 3948; omega)
theorem elec654Axes_disjoint {a b : Fin 654} (hab : a ≠ b) :
    (elec654Axes a).DisjointWires (elec654Axes b) := by
  rcases lt_trichotomy a.val b.val with h | h | h
  · exact QRegister.block_disjoint_of_le _ _ _ _ _ _ (by omega)
  · exact absurd (Fin.ext h) hab
  · exact QRegister.disjoint_comm.mp (QRegister.block_disjoint_of_le _ _ _ _ _ _ (by omega))
theorem proj3Axes_disjoint {a b : Fin 3} (hab : a ≠ b) :
    (proj3Axes a).DisjointWires (proj3Axes b) := by
  rcases lt_trichotomy a.val b.val with h | h | h
  · exact QRegister.block_disjoint_of_le _ _ _ _ _ _ (by omega)
  · exact absurd (Fin.ext h) hab
  · exact QRegister.disjoint_comm.mp (QRegister.block_disjoint_of_le _ _ _ _ _ _ (by omega))
noncomputable def smToTwos654SysPerm : Equiv.Perm (Fin (2 ^ systemQubits)) :=
  foldAxesPerm (smToTwosAxisPerm 3) elec654Axes
noncomputable def smToTwosProj3Perm : Equiv.Perm (Fin (2 ^ systemQubits)) :=
  foldAxesPerm (smToTwosAxisPerm 5) proj3Axes
noncomputable def smToTwosSysPerm : Equiv.Perm (Fin (2 ^ systemQubits)) :=
  smToTwos654SysPerm.trans smToTwosProj3Perm
noncomputable def smToTwos654SysUnitary : Unitary (2 ^ systemQubits) :=
  fwdPermUnitary smToTwos654SysPerm
noncomputable def smToTwosSysUnitary : Unitary (2 ^ systemQubits) :=
  fwdPermUnitary smToTwosSysPerm
def smToTwos654Dyn (v : Var) (rSys : QRegister systemQubits n) (rWork : QRegister 5 n)
    (hdisj : rSys.DisjointWires rWork) : DynamicCircuit Var n := smToTwosAxesDyn v 3
    elec654Axes rSys rWork hdisj
def smToTwosProj3Dyn (v : Var) (rSys : QRegister systemQubits n) (rWork : QRegister 7 n)
    (hdisj : rSys.DisjointWires rWork) : DynamicCircuit Var n := smToTwosAxesDyn v 5 proj3Axes
    rSys rWork hdisj
def smToTwosSysDyn (v : Var) (rSys : QRegister systemQubits n) (rWork : QRegister 7 n)
    (hdisj : rSys.DisjointWires rWork) : DynamicCircuit Var n := .seq (smToTwos654Dyn v rSys
    (rWork.slice 0 5 (by omega)) (hdisj.compose_right _))
    (smToTwosProj3Dyn v rSys rWork hdisj)
@[simp] theorem count_smToTwos654Dyn_toff (v : Var) (rSys : QRegister systemQubits n)
    (rWork : QRegister 5 n) (hdisj : rSys.DisjointWires rWork) :
    (smToTwos654Dyn v rSys rWork hdisj).count .TOFF = 0 := count_smToTwosAxesDyn_toff ..
@[simp] theorem count_smToTwos654Dyn_t (v : Var)
    (rSys : QRegister systemQubits n) (rWork : QRegister 5 n) (hdisj : rSys.DisjointWires rWork) :
    (smToTwos654Dyn v rSys rWork hdisj).count .T = 10464 := by
  rw [smToTwos654Dyn, count_smToTwosAxesDyn_t]
@[simp] theorem count_smToTwosProj3Dyn_toff (v : Var) (rSys : QRegister systemQubits n)
    (rWork : QRegister 7 n) (hdisj : rSys.DisjointWires rWork) :
    (smToTwosProj3Dyn v rSys rWork hdisj).count .TOFF = 0 := count_smToTwosAxesDyn_toff ..
@[simp] theorem count_smToTwosProj3Dyn_t (v : Var)
    (rSys : QRegister systemQubits n) (rWork : QRegister 7 n) (hdisj : rSys.DisjointWires rWork) :
    (smToTwosProj3Dyn v rSys rWork hdisj).count .T = 72 := by
  rw [smToTwosProj3Dyn, count_smToTwosAxesDyn_t]
@[simp] theorem count_smToTwosSysDyn_toff (v : Var)
    (rSys : QRegister systemQubits n) (rWork : QRegister 7 n) (hdisj : rSys.DisjointWires rWork) :
    (smToTwosSysDyn v rSys rWork hdisj).count .TOFF = 0 := by
  simp [smToTwosSysDyn]
@[simp] theorem count_smToTwosSysDyn_t (v : Var)
    (rSys : QRegister systemQubits n) (rWork : QRegister 7 n) (hdisj : rSys.DisjointWires rWork) :
    (smToTwosSysDyn v rSys rWork hdisj).count .T = 10536 := by
  simp [smToTwosSysDyn]
theorem smToTwos654Dyn_realizes [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var)
    (rSys : QRegister systemQubits n) (rWork : QRegister 5 n) (hdisj : rSys.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rSys rWork smToTwos654SysUnitary (smToTwos654Dyn v rSys rWork hdisj) :=
  smToTwosAxesDyn_realizes v 3 elec654Axes rSys rWork hdisj
theorem smToTwosSysDyn_realizes [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var)
    (rSys : QRegister systemQubits n) (rWork : QRegister 7 n) (hdisj : rSys.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rSys rWork smToTwosSysUnitary (smToTwosSysDyn v rSys rWork hdisj) := by
  have h654 := (smToTwos654Dyn_realizes v rSys (rWork.slice 0 5 (by omega))
    (hdisj.compose_right _)).widenWorkspace
  have hproj : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rSys rWork (fwdPermUnitary smToTwosProj3Perm) (smToTwosProj3Dyn v rSys rWork hdisj) :=
    smToTwosAxesDyn_realizes v 5 proj3Axes rSys rWork hdisj
  have hseq := h654.seq hdisj hproj
  have hmul : fwdPermUnitary smToTwosProj3Perm * smToTwos654SysUnitary = smToTwosSysUnitary := by
    dsimp only [smToTwos654SysUnitary, smToTwosSysUnitary, smToTwosSysPerm]
    rw [← fwdPermUnitary_trans]
  unfold smToTwosSysDyn
  simpa only [hmul] using hseq
lemma div_mod_two_pow_bit (X q j : ℕ) (hj : j < q) :
    ((X % 2 ^ q) / 2 ^ j) % 2 = (X / 2 ^ j) % 2 := by
  have hq : q = j + 1 + (q - 1 - j) := by omega
  rw [hq, pow_add, pow_add, pow_one]
  set A := 2 ^ j
  set B := 2 ^ (q - 1 - j)
  have hA : 0 < A := Nat.two_pow_pos _
  have hX : X = X % (A * 2 * B) + A * (2 * (B * (X / (A * 2 * B)))) := by
    calc X = A * 2 * B * (X / (A * 2 * B)) + X % (A * 2 * B) := (Nat.div_add_mod X (A * 2 * B)).symm
      _ = X % (A * 2 * B) + A * (2 * (B * (X / (A * 2 * B)))) := by ring
  conv_rhs => rw [hX, Nat.add_mul_div_left _ _ hA, Nat.add_mul_mod_self_left]
theorem extractIndex_block_val {q K : ℕ} (off : ℕ) (h : off + q ≤ K) (x : Fin (2 ^ K)) :
    ((QRegister.block off q h).extractIndex x).val = (x.val / 2 ^ off) % 2 ^ q := by
  rw [← bitsVal_basisBits ((QRegister.block off q h).extractIndex x)]
  unfold bitsVal
  have hbit : ∀ j : Fin q,
      (basisBits q ((QRegister.block off q h).extractIndex x) j).val =
        ((x.val / 2 ^ off) % 2 ^ q) / 2 ^ j.val % 2 := fun j ↦ by
    rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, QRegister.block_apply_val,
        ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide)), pow_add, ← Nat.div_div_eq_div_mul]
    exact (div_mod_two_pow_bit (x.val / 2 ^ off) q j.val j.isLt).symm
  simp_rw [hbit]
  exact sum_div_two_pow_mod_two_mul_two_pow q _ (Nat.mod_lt _ (Nat.two_pow_pos _))
def elecAxisField (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons) (w : Fin 3) : Fin 64 :=
  (elec654Axes ⟨3 * i.val + w.val,
    by have : numElectrons = 218 := rfl; have := i.isLt; have := w.isLt; omega⟩).extractIndex x
def projAxisField (x : Fin (2 ^ systemQubits)) (w : Fin 3) : Fin 256 :=
  (proj3Axes w).extractIndex x
theorem signMagnitude_electron_eq (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons) (w : Fin 3) :
    SpecsAux.SpecMirror.signMagnitude x (.electron i) w =
      ((elecAxisField x i w).val / 32, (elecAxisField x i w).val % 32) := by
  dsimp [SpecsAux.SpecMirror.signMagnitude, componentBits, electronBits, bitOffset, elecAxisField,
    elec654Axes]
  rw [extractIndex_block_val]
  set f := x.val / 2 ^ (6 * (3 * i.val + w.val))
  ext <;> dsimp
  · have hdm := Nat.div_add_mod f 64
    have h1 : f = f % 64 + 32 * (2 * (f / 64)) := by omega
    conv_lhs => rw [h1, Nat.add_mul_div_left _ _ (by decide)]
    omega
  · have hdm := Nat.div_add_mod f 64
    omega
theorem signMagnitude_projectile_eq (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    SpecsAux.SpecMirror.signMagnitude x .projectile w =
      ((projAxisField x w).val / 128, (projAxisField x w).val % 128) := by
  dsimp [SpecsAux.SpecMirror.signMagnitude, componentBits, projectileBits, bitOffset, projAxisField,
    proj3Axes]
  have hoff : 3 * electronBits * numElectrons + 8 * w.val = 3924 + 8 * w.val := rfl
  rw [hoff, extractIndex_block_val]
  set f := x.val / 2 ^ (3924 + 8 * w.val)
  ext <;> dsimp
  · have hdm := Nat.div_add_mod f 256
    have h1 : f = f % 256 + 128 * (2 * (f / 256)) := by omega
    conv_lhs => rw [h1, Nat.add_mul_div_left _ _ (by decide)]
    omega
  · have hdm := Nat.div_add_mod f 256
    omega
theorem elecAxisField_smToTwos654 (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons) (w : Fin 3) :
    elecAxisField (smToTwos654SysPerm x) i w = smToTwosAxisPerm 3 (elecAxisField x i w) :=
  foldAxesPerm_extractIndex (smToTwosAxisPerm 3) elec654Axes
    (fun _ _ ↦ elec654Axes_disjoint)
    ⟨3 * i.val + w.val, by have : numElectrons = 218 := rfl; have := i.isLt; have := w.isLt; omega⟩
      x
theorem projAxisField_smToTwos654 (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    projAxisField (smToTwos654SysPerm x) w = projAxisField x w := by
  dsimp only [projAxisField, smToTwos654SysPerm]
  apply (basisBitsEquiv 8).injective; funext j
  change basisBits 8 ((proj3Axes w).extractIndex (foldAxesPerm (smToTwosAxisPerm 3) elec654Axes x))
    j =
    basisBits 8 ((proj3Axes w).extractIndex x) j
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  exact foldAxesPerm_outside (smToTwosAxisPerm 3) elec654Axes (proj3Axes w j)
    (fun m ⟨l, hl⟩ ↦ by
      have hv := congrArg Fin.val hl
      change 6 * m.val + l.val = 3924 + 8 * w.val + j.val at hv
      omega) x
theorem smToTwosSysPerm_apply (x : Fin (2 ^ systemQubits)) :
    smToTwosSysPerm x = smToTwosProj3Perm (smToTwos654SysPerm x) :=
  Equiv.trans_apply smToTwos654SysPerm smToTwosProj3Perm x
theorem elecAxisField_smToTwosProj3 (y : Fin (2 ^ systemQubits)) (i : Fin numElectrons) (w : Fin
    3) :
    elecAxisField (smToTwosProj3Perm y) i w = elecAxisField y i w := by
  let rAx := elec654Axes
    ⟨3 * i.val + w.val, by have : numElectrons = 218 := rfl; have := i.isLt; have := w.isLt; omega⟩
  dsimp only [elecAxisField, smToTwosProj3Perm]
  apply (basisBitsEquiv 6).injective; funext j
  change basisBits 6 (rAx.extractIndex (foldAxesPerm (smToTwosAxisPerm 5) proj3Axes y)) j =
    basisBits 6 (rAx.extractIndex y) j
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  exact foldAxesPerm_outside (smToTwosAxisPerm 5) proj3Axes (rAx j)
    (fun m ⟨l, hl⟩ ↦ by
      have hne : numElectrons = 218 := rfl
      have hi := i.isLt
      have hw := w.isLt
      have hv := congrArg Fin.val hl
      change 3924 + 8 * m.val + l.val = 6 * (3 * i.val + w.val) + j.val at hv
      omega) y
theorem projAxisField_smToTwosProj3 (y : Fin (2 ^ systemQubits)) (w : Fin 3) :
    projAxisField (smToTwosProj3Perm y) w = smToTwosAxisPerm 5 (projAxisField y w) :=
  foldAxesPerm_extractIndex (smToTwosAxisPerm 5) proj3Axes (fun _ _ ↦ proj3Axes_disjoint) w y
theorem elecAxisField_smToTwosSys (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons) (w : Fin 3) :
    elecAxisField (smToTwosSysPerm x) i w = smToTwosAxisPerm 3 (elecAxisField x i w) := by
  rw [smToTwosSysPerm_apply, elecAxisField_smToTwosProj3, elecAxisField_smToTwos654]
theorem projAxisField_smToTwosSys (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    projAxisField (smToTwosSysPerm x) w = smToTwosAxisPerm 5 (projAxisField x w) := by
  rw [smToTwosSysPerm_apply, projAxisField_smToTwosProj3, projAxisField_smToTwos654]
theorem twosComp6_smToTwos654_eq_momentum {x : Fin (2 ^ systemQubits)} (hx : IsGridState x)
    (i : Fin numElectrons) (w : Fin 3) :
    twosComp6Int (elecAxisField (smToTwos654SysPerm x) i w) =
      SpecsAux.SpecMirror.momentum x (.electron i) w := by
  have hsm := hx (.electron i) w
  rw [signMagnitude_electron_eq] at hsm
  have hne : (elecAxisField x i w).val ≠ 32 := fun h32 ↦ hsm (by rw [h32])
  rw [elecAxisField_smToTwos654, twosComp6Int_smToTwosAxisPerm hne,
      SpecsAux.SpecMirror.momentum, signMagnitude_electron_eq]
  rfl
theorem twosComp6_smToTwosSys_eq_momentum {x : Fin (2 ^ systemQubits)} (hx : IsGridState x)
    (i : Fin numElectrons) (w : Fin 3) : twosComp6Int (elecAxisField (smToTwosSysPerm x) i w)
    = SpecsAux.SpecMirror.momentum x (.electron i) w := by
  rw [elecAxisField_smToTwosSys, ← elecAxisField_smToTwos654, twosComp6_smToTwos654_eq_momentum hx]
theorem twosComp8_smToTwosSys_eq_momentum {x : Fin (2 ^ systemQubits)} (hx : IsGridState x)
    (w : Fin 3) : twosComp8Int (projAxisField (smToTwosSysPerm x) w) = SpecsAux.SpecMirror.momentum
    x .projectile w := by
  have hsm := hx .projectile w
  rw [signMagnitude_projectile_eq] at hsm
  have hne : (projAxisField x w).val ≠ 128 := fun h128 ↦ hsm (by rw [h128])
  rw [projAxisField_smToTwosSys, twosComp8Int_smToTwosAxisPerm hne,
      SpecsAux.SpecMirror.momentum, signMagnitude_projectile_eq]
  rfl
theorem signMag_inj_of_ne {B u v : ℕ} (hu_lt : u < 2 * B) (hv_lt : v < 2 * B)
    (hu : u ≠ B) (hv : v ≠ B) :
    ((-1 : ℤ) ^ (u / B) * ((u % B : ℕ) : ℤ) = (-1 : ℤ) ^ (v / B) * ((v % B : ℕ) : ℤ)) ↔ u = v := by
  refine ⟨fun heq ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hsp : ∀ {z : ℕ}, z < 2 * B →
      (z < B ∧ (-1 : ℤ) ^ (z / B) * ((z % B : ℕ) : ℤ) = (z : ℤ)) ∨
      (B ≤ z ∧ (-1 : ℤ) ^ (z / B) * ((z % B : ℕ) : ℤ) = -((z - B : ℕ) : ℤ)) := fun {z} hz ↦ by
    by_cases hlt : z < B
    · exact Or.inl ⟨hlt, by
        rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, _root_.pow_zero, one_mul]⟩
    · have hB : 0 < B := by omega
      have hlt2 : z - B < B := by omega
      have h1 : z = (z - B) + B * 1 := by omega
      have hd : z / B = 1 := by
        rw [h1, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hlt2, zero_add]
      have hm : z % B = z - B := by
        conv_lhs => rw [h1]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
      exact Or.inr ⟨by omega, by rw [hd, hm, pow_one, neg_one_mul]⟩
  rcases hsp hu_lt with ⟨_, heu⟩ | ⟨_, heu⟩ <;>
    rcases hsp hv_lt with ⟨_, hev⟩ | ⟨_, hev⟩ <;> rw [heu, hev] at heq <;> omega
theorem fwdPerm_comm_grid_and_fermionic {e : Equiv.Perm (Fin (2 ^ systemQubits))}
    {φe : Equiv.Perm (Fin 64)} {φp : Equiv.Perm (Fin 256)}
    (he_elec : ∀ x i w, elecAxisField (e x) i w = φe (elecAxisField x i w))
    (he_proj : ∀ x w, projAxisField (e x) w = φp (projAxisField x w))
    (hφe32 : ∀ u : Fin 64, (φe u).val = 32 ↔ u.val = 32)
    (hφp128 : ∀ u : Fin 256, (φp u).val = 128 ↔ u.val = 128) :
    (∀ x, IsGridState (e x) ↔ IsGridState x) ∧
    (fwdPermUnitary e).1 * BridgeFermionicComm.SpecInner.gridProjector =
      BridgeFermionicComm.SpecInner.gridProjector * (fwdPermUnitary e).1 ∧
    (∀ spinUp, (fwdPermUnitary e).1 * SpecsAux.SpecMirror.fermionicProjector spinUp =
      SpecsAux.SpecMirror.fermionicProjector spinUp * (fwdPermUnitary e).1) := by
  have hbad_e : ∀ x i w, SpecsAux.SpecMirror.signMagnitude x (.electron i) w = (1, 0) ↔
      (elecAxisField x i w).val = 32 := fun x i w ↦ by
    rw [signMagnitude_electron_eq, Prod.mk.injEq]; have := (elecAxisField x i w).isLt; omega
  have hbad_p : ∀ x w, SpecsAux.SpecMirror.signMagnitude x .projectile w = (1, 0) ↔
      (projAxisField x w).val = 128 := fun x w ↦ by
    rw [signMagnitude_projectile_eq, Prod.mk.injEq]; have := (projAxisField x w).isLt; omega
  have hgrid : ∀ x, IsGridState (e x) ↔ IsGridState x := fun x ↦
    forall_congr' fun a ↦ forall_congr' fun w ↦ not_congr <| by
      cases a with
      | electron i => rw [hbad_e, hbad_e, he_elec]; exact hφe32 _
      | projectile => rw [hbad_p, hbad_p, he_proj]; exact hφp128 _
  have hfwd_eq_perm : (fwdPermUnitary e).1 = (permutationUnitary e).1 := by
    ext i j; rw [fwdPermUnitary_apply, permutationUnitary_apply]
    by_cases hij : e j = i
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have h6_inj : ∀ {u v : Fin 64}, u.val ≠ 32 → v.val ≠ 32 →
      ((-1 : ℤ) ^ (u.val / 32) * ((u.val % 32 : ℕ) : ℤ) =
        (-1 : ℤ) ^ (v.val / 32) * ((v.val % 32 : ℕ) : ℤ) ↔ u = v) := fun {u v} hu hv ↦
    (signMag_inj_of_ne (B := 32) u.isLt v.isLt hu hv).trans (@Fin.val_inj 64 u v)
  have h8_inj : ∀ {u v : Fin 256}, u.val ≠ 128 → v.val ≠ 128 →
      ((-1 : ℤ) ^ (u.val / 128) * ((u.val % 128 : ℕ) : ℤ) =
        (-1 : ℤ) ^ (v.val / 128) * ((v.val % 128 : ℕ) : ℤ) ↔ u = v) := fun {u v} hu hv ↦
    (signMag_inj_of_ne (B := 128) u.isLt v.isLt hu hv).trans (@Fin.val_inj 256 u v)
  rw [hfwd_eq_perm]
  refine ⟨hgrid, (predProjector_comm_permutationUnitary IsGridState e hgrid).symm, fun spinUp ↦ ?_⟩
  symm; refine commutes_permutationUnitary_of_entry e _ fun x y ↦ ?_
  dsimp only [SpecsAux.SpecMirror.fermionicProjector, Matrix.of_apply]
  by_cases hxy : IsGridState x ∧ IsGridState y
  · rcases hxy with ⟨hx, hy⟩
    have hex : IsGridState (e x) := (hgrid x).mpr hx
    have hey : IsGridState (e y) := (hgrid y).mpr hy
    simp only [hx, hy, hex, hey, and_self, ↓reduceIte]
    refine congrArg (· / ((spinUp.card.factorial * (numElectrons - spinUp.card).factorial : ℕ)
      : ℂ)) (Finset.sum_congr rfl fun g _ ↦ ?_)
    have hp_iff : SpecsAux.SpecMirror.momentum (e x) .projectile = SpecsAux.SpecMirror.momentum (e
      y) .projectile ↔
        SpecsAux.SpecMirror.momentum x .projectile = SpecsAux.SpecMirror.momentum y .projectile :=
          by
      simp only [funext_iff, SpecsAux.SpecMirror.momentum, signMagnitude_projectile_eq]
      refine forall_congr' fun w ↦ ?_
      rw [h8_inj (mt (hbad_p _ _).mpr (hex .projectile w))
          (mt (hbad_p _ _).mpr (hey .projectile w)),
        h8_inj (mt (hbad_p _ _).mpr (hx .projectile w)) (mt (hbad_p _ _).mpr (hy .projectile w)),
        he_proj, he_proj, φp.apply_eq_iff_eq]
    have he_iff : (∀ i, SpecsAux.SpecMirror.momentum (e x) (.electron i) =
      SpecsAux.SpecMirror.momentum (e
        y) (.electron (g i))) ↔ (∀ i, SpecsAux.SpecMirror.momentum x (.electron i) =
        SpecsAux.SpecMirror.momentum y (.electron (g i))) := by
      refine forall_congr' fun i ↦ ?_
      simp only [funext_iff, SpecsAux.SpecMirror.momentum, signMagnitude_electron_eq]
      refine forall_congr' fun w ↦ ?_
      rw [h6_inj (mt (hbad_e _ _ _).mpr (hex (.electron i) w))
          (mt (hbad_e _ _ _).mpr (hey (.electron (g i)) w)),
        h6_inj (mt (hbad_e _ _ _).mpr (hx (.electron i) w))
          (mt (hbad_e _ _ _).mpr (hy (.electron (g i)) w)),
        he_elec, he_elec, φe.apply_eq_iff_eq]
    simp only [hp_iff, he_iff]
  · simp [hxy, show ¬ (IsGridState (e x) ∧ IsGridState (e y)) from
      fun ⟨h1, h2⟩ ↦ hxy ⟨(hgrid x).mp h1, (hgrid y).mp h2⟩]
theorem smToTwosSysPerm_self (x : Fin (2 ^ systemQubits)) :
    smToTwosSysPerm (smToTwosSysPerm x) = x := by
  apply (basisBitsEquiv systemQubits).injective; funext w
  change basisBits systemQubits (smToTwosSysPerm (smToTwosSysPerm x)) w = basisBits systemQubits x w
  rcases BridgeFermionicComm.SpecInner.exists_particle_field_of_lt w.val w.isLt with ⟨a, coord, b,
    hb, hw⟩
  cases a with
  | electron i =>
      have hw_eq : w = elec654Axes
          ⟨3 * i.val + coord.val, by
            have : numElectrons = 218 := rfl; have := i.isLt; have := coord.isLt; omega⟩
          ⟨b, hb⟩ :=
        Fin.ext hw
      rw [hw_eq, ← QRegister.basisBits_extractIndex]
      change basisBits 6 (elecAxisField (smToTwosSysPerm (smToTwosSysPerm x)) i coord) ⟨b, hb⟩ = _
      rw [elecAxisField_smToTwosSys, elecAxisField_smToTwosSys, smToTwosAxisPerm_self]
      exact QRegister.basisBits_extractIndex _ x ⟨b, hb⟩
  | projectile =>
      have hw_eq : w = proj3Axes coord ⟨b, hb⟩ := Fin.ext hw
      rw [hw_eq, ← QRegister.basisBits_extractIndex]
      change basisBits 8 (projAxisField (smToTwosSysPerm (smToTwosSysPerm x)) coord) ⟨b, hb⟩ = _
      rw [projAxisField_smToTwosSys, projAxisField_smToTwosSys, smToTwosAxisPerm_self]
      exact QRegister.basisBits_extractIndex _ x ⟨b, hb⟩
theorem smToTwosSysPerm_symm : smToTwosSysPerm.symm = smToTwosSysPerm := by
  ext x
  exact congrArg Fin.val (smToTwosSysPerm.symm_apply_eq.mpr (smToTwosSysPerm_self x).symm)
theorem smToTwosSysUnitary_mul_self : smToTwosSysUnitary * smToTwosSysUnitary = 1 :=
    fwdPermUnitary_mul_self_of_symm_eq smToTwosSysPerm smToTwosSysPerm_symm
theorem smToTwosSysUnitary_conjTranspose : smToTwosSysUnitary.1ᴴ = smToTwosSysUnitary.1 := by
  rw [smToTwosSysUnitary, fwdPermUnitary_conjTranspose, smToTwosSysPerm_symm]
theorem smToTwosSys_comm_gridProjector : smToTwosSysUnitary.1 *
    BridgeFermionicComm.SpecInner.gridProjector =
    BridgeFermionicComm.SpecInner.gridProjector * smToTwosSysUnitary.1 :=
    (fwdPerm_comm_grid_and_fermionic elecAxisField_smToTwosSys projAxisField_smToTwosSys
    (smToTwosAxisPerm_eq_negZero_iff 3) (smToTwosAxisPerm_eq_negZero_iff 5)).2.1
theorem smToTwosSys_comm_fermionicProjector (spinUp : Finset (Fin numElectrons)) :
    smToTwosSysUnitary.1 * SpecsAux.SpecMirror.fermionicProjector spinUp =
    SpecsAux.SpecMirror.fermionicProjector spinUp * smToTwosSysUnitary.1 :=
    (fwdPerm_comm_grid_and_fermionic elecAxisField_smToTwosSys projAxisField_smToTwosSys
    (smToTwosAxisPerm_eq_negZero_iff 3) (smToTwosAxisPerm_eq_negZero_iff 5)).2.2 spinUp
end SmToTwos
section Wire0Cancel
def bitRev6GridEquiv : NyqGrid3D64 ≃ NyqGrid3D64 := Equiv.piCongrRight fun _ ↦ bitRev6Equiv
noncomputable def karatsubaOutPhase3D (y : NyqGrid3D64) : ℂ :=
  ∏ w : Fin 3, karatsubaOutPhase64 (y w)
theorem karatsubaOutPhase3D_unit (y : NyqGrid3D64) :
    star (karatsubaOutPhase3D y) * karatsubaOutPhase3D y = 1 := by
  unfold karatsubaOutPhase3D karatsubaOutPhase64
  rw [RCLike.star_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ ↦ ?_
  rw [← RCLike.star_def]
  exact star_mul_omega128_self _
noncomputable def karatsubaOffset3D128 (b : NyqParity3D) : Matrix NyqGrid3D64 NyqGrid3D64 ℂ :=
  Matrix.of fun z u ↦ ∏ w : Fin 3, karatsubaOffsetUnitary128 (b w) (z w) (u w)
theorem karatsubaOffset3D128_apply (b : NyqParity3D) (z u : NyqGrid3D64) :
    karatsubaOffset3D128 b z u =
      karatsubaOutPhase3D (bitRev6GridEquiv z) * subGridUnitary64 b (bitRev6GridEquiv z) u := by
  dsimp [karatsubaOffset3D128, karatsubaOutPhase3D, subGridUnitary64, subGridElem64_3D,
         bitRev6GridEquiv, shiftedMom3D]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [karatsubaOffsetUnitary128_apply]
  change karatsubaOutPhase64 (bitRev6Equiv (z w)) * subGridUnitary128 (b w) (bitRev6Equiv (z w)) (u
    w) =
    karatsubaOutPhase64 (bitRev6Equiv (z w)) *
      subGridElem64_1D (b w) (bitRev6Equiv (z w)) (DyadicSubgridToeplitz128.shiftedFin64ToInt (u w))
  congr 1
  dsimp [subGridUnitary128, subGridElem128, subGridElem64_1D, DyadicSubgridToeplitz128.omega128,
    KaratsubaQft64Matrix.shiftedFin64ToInt, DyadicSubgridToeplitz128.shiftedFin64ToInt]
  rw [KaratsubaQft64Matrix.omega128_def]
end Wire0Cancel
end TwosCompAndWire0Cancel
end
end ModTwosCompAndWire0Cancel

end QuantumComputation.Specs.StoppingPowerSolution
