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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.FusedSlot4Slot0

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section SyndromeUncomp

namespace SyndromeUncomp
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority := 1000000) instNeZeroTwoPowSub (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
abbrev cToff3 {n : ℕ} (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    Circuit n :=
  TOFF c₁ c₂ anc h₁₂ h₁a h₂a
open PrimitiveGate (TOFF T)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
open SpecsAux
open SpecsAux.SpecMirror
-- Root solution namespace already active.
open SingleRBEGridGuardWalk (diagProj diagProj_isHermitian diagProj_idem)
open Slots01AndGridGuardBridge (elecAxisWord6)
open FullSysCatSegmentBridge (fullSysBEWires fullSysRawAncWires)
open GridGuard654ReflAux hiding disjointWires_concat_left
open GridGuard654Flag288
open SingleCatClosure
  (kActSingleCatClosure rBEInSingleCat qSigInSingleCat rBEInSingleCat_disj_qSig optXSingleCat)
open GidneySignalRotPart2 (restrictAssertionToZeroAncilla_congr_image)
open HoistBorrow42TwoAngleBridge (uSignalRotTwoAngleSingleCat)
open InterWalkRSum42Hoist (qreg_ext)
/-- Canonical count of electrons `i : Fin 218` having at least one `-0` (`100000₂ = 32`) momentum
word. -/
def badElecCount (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : ℕ :=
  (Finset.univ.filter fun i : Fin SpecsAux.SpecMirror.numElectrons ↦
    decide ((elecAxisWord6 x i 0).val = 32 ∨ (elecAxisWord6 x i 1).val = 32 ∨ (elecAxisWord6 x i
      2).val = 32)).card
/-- Generalized `1 - 2 • (diagProj bValid ⊗ |0⟩⟨0|_anc)` reflection unitary on `fullSysBEWires
mPayload`. -/
noncomputable def fullSysGuardReflUnitaryGen (mPayload : ℕ)
    (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool) : Unitary (2 ^ (fullSysBEWires
      mPayload)) :=
  singleRBEReflNegUnitary SpecsAux.SpecMirror.systemQubits (fullSysRawAncWires mPayload)
    (diagProj SpecsAux.SpecMirror.systemQubits bValid) (diagProj_isHermitian
      SpecsAux.SpecMirror.systemQubits bValid)
    (diagProj_idem SpecsAux.SpecMirror.systemQubits bValid)
/-- Generalized local guard reflection `guardPolLocal` for arbitrary `bValid`. -/
noncomputable def guardPolLocalGen (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool)
    (mPayload kMid : ℕ) (hkMid : 1 ≤ kMid) (b : Bool) : Unitary (2 ^ (fullSysBEWires mPayload +
      kMid)) :=
  if b then
    (QRegister.block 0 (fullSysBEWires mPayload + 1) ((Nat.zero_add _).le.trans (Nat.add_le_add_left
      hkMid _))).embedUnitary
      (ctrlLocalUnitary (fullSysGuardReflUnitaryGen mPayload bValid))
  else 1
/-- Generalized single-catalyst guard reflection `guardPolSingleCat` for arbitrary `bValid`. -/
noncomputable def guardPolSingleCatGen (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool)
    (mPayload B_tot kWorkConst : ℕ) (b : Bool) : Unitary (2 ^ (kActSingleCatClosure mPayload B_tot
      kWorkConst)) :=
  if b then
    ((rBEInSingleCat mPayload B_tot kWorkConst).concat (QRegister.singleton (qSigInSingleCat
      mPayload B_tot kWorkConst))
      (rBEInSingleCat_disj_qSig mPayload B_tot kWorkConst)).embedUnitary
      (ctrlLocalUnitary (fullSysGuardReflUnitaryGen mPayload bValid))
  else 1
/-- Generalized active unitary of a 2-angle Gidney guard-signal sandwich on
`kActSingleCatClosure`. -/
noncomputable def uGuardWrapTwoAngleSingleCatGen (bValid : Fin (2 ^
    SpecsAux.SpecMirror.systemQubits) → Bool)
    {mPayload B_tot kWorkConst : ℕ} (hB42 : 42 ≤ B_tot) (preX postX : Bool) (C_d D_d : Fin (2 ^
      42)) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
  guardPolSingleCatGen bValid mPayload B_tot kWorkConst true * (optXSingleCat mPayload B_tot
    kWorkConst postX *
    (uSignalRotTwoAngleSingleCat hB42 C_d D_d * (optXSingleCat mPayload B_tot kWorkConst preX *
      guardPolSingleCatGen bValid mPayload B_tot kWorkConst true)))
/-- Bit-level badness predicate for 6-bit electron momentum field `f : Fin 654` (`-0` =
`100000₂`). -/
def elecFieldBadBits (γ : BitAssignment systemQubits) (f : Fin 654) : Bool :=
  decide (∀ u : Fin 5, γ (electronFieldLinearIdx f u.castSucc) = 0) &&
    decide (γ (electronFieldLinearIdx f 5) = 1)
/-- Bit-level validity predicate for 8-bit projectile momentum field `w : Fin 3` (`≠ 10000000₂`). -/
def projFieldValidBits (γ : BitAssignment systemQubits) (w : Fin 3) : Bool :=
  !(decide (∀ u : Fin 7, γ (projectileFieldLinearIdx w u.castSucc) = 0) &&
    decide (γ (projectileFieldLinearIdx w 7) = 1))
theorem elecFieldBadBits_eq_true_iff (x : Fin (2 ^ systemQubits)) (f : Fin 654) :
    elecFieldBadBits (basisBits systemQubits x) f = true ↔
      signMagnitude x (.electron ⟨f.val / 3, by have := f.isLt; change _ < 218; omega⟩)
        ⟨f.val % 3, by omega⟩ = (1, 0) := by
  let γ := basisBits systemQubits x
  let e : Fin numElectrons := ⟨f.val / 3, by have := f.isLt; change _ < 218; omega⟩
  let w : Fin 3 := ⟨f.val % 3, by omega⟩
  have hbit : ∀ k (hk : k < systemQubits),
      (γ ⟨k, hk⟩ = 0 ↔ x.val.testBit k = false) ∧ (γ ⟨k, hk⟩ = 1 ↔ x.val.testBit k = true) :=
        fun k hk ↦ by
    dsimp only [γ]
    rw [basisBits_eq_testBit]
    cases x.val.testBit k <;> simp
  have hoff : bitOffset (.electron e) w = 6 * f.val := by
    change 6 * (3 * (f.val / 3) + f.val % 3) = 6 * f.val
    omega
  let q := x.val / 2 ^ (6 * f.val)
  have hq_tb : ∀ b : ℕ, q.testBit b = x.val.testBit (6 * f.val + b) := fun b ↦ by
    simp [q, Nat.testBit_div_two_pow, Nat.add_comm]
  unfold elecFieldBadBits
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  rw [signMagnitude, hoff]
  change ((∀ u : Fin 5, γ (electronFieldLinearIdx f u.castSucc) = 0) ∧
      γ (electronFieldLinearIdx f 5) = 1) ↔ (q / 32 % 2, q % 2 ^ 5) = (1, 0)
  rw [Prod.mk.injEq, and_comm, mod_two_pow_eq_zero_iff_testBit 5 q]
  refine and_congr ?_ (forall_congr' fun u ↦ ?_)
  · rw [(hbit _ _).2, show (electronFieldLinearIdx f 5).val = 6 * f.val + 5 from rfl,
      ← hq_tb 5, Nat.testBit, Nat.shiftRight_eq_div_pow]
    rcases (by omega : q / 32 % 2 = 0 ∨ q / 32 % 2 = 1) with h | h <;> simp [h]
  · rw [(hbit _ _).1, show (electronFieldLinearIdx f u.castSucc).val = 6 * f.val + u.val from rfl,
      ← hq_tb]
theorem elecAxisWord6_val_eq_32_iff_signMagnitude (x : Fin (2 ^ systemQubits)) (i : Fin
    numElectrons) (w : Fin 3) :
    (elecAxisWord6 x i w).val = 32 ↔ signMagnitude x (.electron i) w = (1, 0) := by
  have hs1 : (signMagnitude x (.electron i) w).1 < 2 := by
    simp only [signMagnitude]
    omega
  have hs2 : (signMagnitude x (.electron i) w).2 < 32 := by
    simp only [signMagnitude, show componentBits (.electron i) - 1 = 5 from rfl, show 2 ^ 5 =
      32 from rfl]
    omega
  simp only [elecAxisWord6, Prod.ext_iff]
  omega
private theorem restrict_wp_eval_comm {Var : Type} [Fintype Var] {n m : ℕ}
    (c : Circuit n) (r : QRegister m n) (hdisj : Disjoint c.support r.image) (A : CQAssertionCompat
      Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval A) r =
      wpQAssignCompat c.eval (CQAssertion.restrictToZeroAncilla A r) := by
  refine funext fun σ ↦ Subtype.ext ?_
  have hcomm : c.eval.1 * r.basisOutcomeProjector 0 = r.basisOutcomeProjector 0 * c.eval.1 :=
    eval_comm_embedMatrix_of_disjoint_support c r hdisj (compProj 0)
  have hP_herm : (r.basisOutcomeProjector 0)ᴴ = r.basisOutcomeProjector 0 :=
    r.basisOutcomeProjector_conjTranspose 0
  have hadj : r.basisOutcomeProjector 0 * c.eval.1ᴴ = c.eval.1ᴴ * r.basisOutcomeProjector 0 := by
    simpa only [conjTranspose_mul, hP_herm] using congrArg conjTranspose hcomm
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  change (A σ).1.conj (r.basisOutcomeProjector 0 * c.eval.1ᴴ) =
    (A σ).1.conj (c.eval.1ᴴ * r.basisOutcomeProjector 0)
  rw [hadj]
private theorem slice_image_eq {n m : ℕ} (r : QRegister m n) {o₁ l₁ o₂ l₂ : ℕ}
    (h₁ : o₁ + l₁ ≤ m) (h₂ : o₂ + l₂ ≤ m) (ho : o₁ = o₂) (hl : l₁ = l₂) :
    (r.slice o₁ l₁ h₁).image = (r.slice o₂ l₂ h₂).image := by
  subst ho
  subst hl
  rfl
open DynCircuitExt
  (restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq) in
theorem symWrapDynList_unitary_gen {Var : Type} [Fintype Var] [DecidableEq Var] {n m_pool m_bot
    m_rem k_sub : ℕ}
    (v : Var) (rPool : QRegister m_pool n) (hPool : m_bot + m_rem ≤ m_pool) (rSub : QRegister k_sub
      n)
    (offset : ℕ) (L : List (SymTempAndStep n)) (hvalid : ValidSymStepList (∅ : Finset (Wire n))
      (rPool.slice 0 m_bot (by omega)) offset L) (hlen : offset + L.length = m_bot)
    (hdisj_L_sub : ∀ s ∈ L, Disjoint s.S rSub.image) (hdisj_L_rem : ∀ s ∈ L, Disjoint s.S
      (rPool.slice m_bot m_rem hPool).image)
    (dCore : DynamicCircuit Var n) (U_core : Unitary (2 ^ n)) (φCore : BitAssignment n → Bool)
    (uBranch : BitAssignment n → Unitary (2 ^ k_sub)) (hcore_const : StoreConst dCore)
    (hcore_evolve : ∀ γ : BitAssignment n, U_core.1.mulVec (basisKet γ) =
        (if φCore γ then (-1 : ℂ) else 1) • (rSub.embedUnitary (uBranch γ)).1.mulVec (basisKet γ))
    (hcore_wp : ∀ M : Observable (Fin (2 ^ n)), CQAssertion.restrictToZeroAncilla (wp dCore.compile
      (fun _ ↦ M))
        (rPool.slice m_bot m_rem hPool) = CQAssertion.restrictToZeroAncilla (wpQAssignCompat U_core
          (fun _ ↦ M))
        (rPool.slice m_bot m_rem hPool)) : ∃ U_wrap : Unitary (2 ^ n), StoreConst (symWrapDynList v
          L dCore) ∧
      (∀ β : BitAssignment n, U_wrap.1.mulVec (basisKet β) = (if φCore (symStepFwdList L β) then
        (-1 : ℂ) else 1) •
            (rSub.embedUnitary (uBranch (symStepFwdList L β))).1.mulVec (basisKet β)) ∧
      (∀ M : Observable (Fin (2 ^ n)), CQAssertion.restrictToZeroAncilla (wp (symWrapDynList v L
        dCore).compile (fun _ ↦ M))
          (rPool.slice offset (L.length + m_rem) (by omega)) = CQAssertion.restrictToZeroAncilla
          (wpQAssignCompat U_wrap (fun _ ↦ M)) (rPool.slice offset (L.length +
            m_rem) (by omega))) := by
  induction L generalizing offset with
  | nil =>
      refine ⟨U_core, hcore_const, hcore_evolve, fun M ↦ ?_⟩
      have h0 : offset = m_bot := by simpa using hlen
      have himg : (rPool.slice offset (([] : List (SymTempAndStep n)).length +
        m_rem) (by omega)).image =
          (rPool.slice m_bot m_rem hPool).image := slice_image_eq rPool _ hPool h0 (Nat.zero_add
            m_rem)
      rw [restrictAssertionToZeroAncilla_congr_image _ _ _ himg,
        restrictAssertionToZeroAncilla_congr_image _ _ _ himg]
      exact hcore_wp M
  | cons s rest ih =>
      rcases hvalid with ⟨_, hanc_s, _, hlat_s, hvalid_rest⟩
      have hlen' : offset + (rest.length + 1) = m_bot := by simpa [List.length_cons] using hlen
      have hs_sub : Disjoint s.S rSub.image := hdisj_L_sub s (List.mem_cons_self ..)
      obtain ⟨U_rest, hconst_rest, hevolve_rest, hwp_rest⟩ := ih (offset + 1) hvalid_rest
        (by simp [List.length_cons] at hlen; omega)
        (fun s' hs' ↦ hdisj_L_sub s' (List.mem_cons_of_mem s hs'))
        (fun s' hs' ↦ hdisj_L_rem s' (List.mem_cons_of_mem s hs'))
      let T_anc : Unitary (2 ^ n) := (cToff3 s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval
      let U_body : Unitary (2 ^ n) := s.midPost.eval * U_rest * s.midPre.eval
      let V : Unitary (2 ^ n) := T_anc * U_body * T_anc
      let U_wrap : Unitary (2 ^ n) := s.post.eval * V * s.pre.eval
      have hsupp_toff : (cToff3 s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).support ⊆ s.S := fun w hw ↦ by
        rcases (QRegister.mem_image _ w).mp hw with ⟨i, rfl⟩
        fin_cases i
        · exact s.c₁_mem
        · exact s.c₂_mem
        · exact s.anc_mem
      have comm_sub (c : Circuit n) (hc : c.support ⊆ s.S) (W : Unitary (2 ^ k_sub)) (δ :
        BitAssignment n) :
          c.eval.1.mulVec ((rSub.embedUnitary W).1.mulVec (basisKet δ)) =
            (rSub.embedUnitary W).1.mulVec (c.eval.1.mulVec (basisKet δ)) := by
        rw [Matrix.mulVec_mulVec]
        change (c.eval.1 * rSub.embedMatrix W.1).mulVec (basisKet δ) = _
        rw [eval_comm_embedMatrix_of_disjoint_support c rSub (Finset.disjoint_of_subset_left hc
          hs_sub) W.1,
          ← Matrix.mulVec_mulVec]
        rfl
      have hV_evolve (γ : BitAssignment n) : V.1.mulVec (basisKet γ) =
          (if φCore (symStepFwdList rest (s.f_midPre (Function.update γ s.anc (γ s.anc + γ s.c₁ *
            γ s.c₂))))
             then (-1 : ℂ) else 1) •
            (rSub.embedUnitary (uBranch (symStepFwdList rest
              (s.f_midPre (Function.update γ s.anc (γ s.anc + γ s.c₁ * γ s.c₂)))))).1.mulVec
                (basisKet γ) := by
        dsimp only [V, U_body, T_anc, cToff3]
        simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        rw [evolve_TOFF_basisKet, s.local_midPre.perm, hevolve_rest, Matrix.mulVec_smul,
          comm_sub s.midPost s.local_midPost.support_sub, s.local_midPost.perm, s.midPost_midPre_id,
          Matrix.mulVec_smul, comm_sub _ hsupp_toff, evolve_TOFF_basisKet]
        exact congrArg (fun δ ↦ _ • (rSub.embedUnitary _).1.mulVec (basisKet δ))
          (toff_update_self_cancel s.c₁ s.c₂ s.anc s.h₁a s.h₂a γ)
      let P₀ := (QRegister.singleton s.anc).basisOutcomeProjector 0
      have hc_body : P₀ * (V.1 * P₀) = V.1 * P₀ := matrix_ext_basisKet fun γ ↦ by
        dsimp only [P₀]
        simp only [← Matrix.mulVec_mulVec, basisOutcomeProjector_zero_mulVec_basisKet]
        by_cases h0 : γ s.anc = 0
        · rw [ite_eq_left h0, hV_evolve γ, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
          change _ • ((QRegister.singleton s.anc).basisOutcomeProjector 0 * rSub.embedMatrix
            _).mulVec (basisKet γ) = _
          rw [← (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rSub)
            (QRegister.singleton s.anc)
              (by rw [QRegExt.disjointWires_iff_disjoint_image, QRegister.image_singleton,
                    Finset.disjoint_singleton_right]
                  exact Finset.disjoint_left.mp hs_sub s.anc_mem) _ 0,
            ← Matrix.mulVec_mulVec, basisOutcomeProjector_zero_mulVec_basisKet, ite_eq_left h0]
          rfl
        · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
      refine ⟨U_wrap, StoreConst.wrapDynamic v s.toTempAndStep hconst_rest, fun β ↦ ?_, fun M ↦ ?_⟩
      · dsimp only [U_wrap]
        simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        rw [s.local_pre.perm β, hV_evolve (s.f_pre β), Matrix.mulVec_smul,
          comm_sub s.post s.local_post.support_sub, s.local_post.perm, s.post_pre_id β]
        rfl
      · let rTot : QRegister ((rest.length + m_rem) + 1) n := rPool.slice offset ((rest.length +
          m_rem) + 1) (by omega)
        let rRestSlice : QRegister (rest.length + m_rem) n := rTot.slice 1 (rest.length +
          m_rem) (by omega)
        have hslice_eq : rRestSlice = rPool.slice (offset + 1) (rest.length + m_rem) (by omega) :=
          qreg_ext fun idx ↦ congrArg rPool.wires (Fin.ext (by dsimp [rRestSlice, rTot]; omega))
        have hanc0 : s.anc = rTot 0 := hanc_s.trans (congrArg rPool.wires (Fin.ext (by simp)))
        have hdisj_S_rest : Disjoint s.S rRestSlice.image := by
          rw [hslice_eq, Finset.disjoint_right]
          intro w hw
          rcases (QRegister.mem_image _ w).mp hw with ⟨idx, rfl⟩
          simp only [QRegister.slice_apply]
          by_cases hlt_idx : idx.val < rest.length
          · rw [show rPool ⟨(offset + 1) + idx.val, by omega⟩ =
                (rPool.slice 0 m_bot (by omega)) ⟨(offset + 1) + idx.val, by omega⟩ from
                congrArg rPool.wires (Fin.ext (by simp))]
            exact hlat_s ⟨(offset + 1) + idx.val, by omega⟩ (by dsimp; omega)
          · rw [show rPool ⟨(offset + 1) + idx.val, by omega⟩ =
                (rPool.slice m_bot m_rem hPool) ⟨idx.val - rest.length, by omega⟩ from
                congrArg rPool.wires (Fin.ext (by dsimp; omega))]
            exact Finset.disjoint_right.mp (hdisj_L_rem s (List.mem_cons_self ..))
              ((QRegister.mem_image _ _).mpr ⟨_, rfl⟩)
        have hdisj_anc_rest : (QRegister.singleton s.anc).DisjointWires rRestSlice := by
          rw [QRegExt.disjointWires_iff_disjoint_image, QRegister.image_singleton,
            Finset.disjoint_singleton_left]
          exact Finset.disjoint_left.mp hdisj_S_rest s.anc_mem
        have hpre_tot : Disjoint s.pre.support rTot.image := by
          rw [Finset.disjoint_right]
          intro w hw
          rcases (QRegister.mem_image _ w).mp hw with ⟨idx, rfl⟩
          by_cases hi0 : idx.val = 0
          · rw [(Fin.ext hi0 : idx = 0), ← hanc0]
            exact s.anc_not_mem_pre
          · exact Finset.disjoint_right.mp (Finset.disjoint_of_subset_left s.local_pre.support_sub
              hdisj_S_rest)
              ((QRegister.mem_image _ _).mpr ⟨⟨idx.val - 1, by omega⟩,
                congrArg rTot.wires (Fin.ext (by dsimp; omega))⟩)
        obtain ⟨M_and, hM_and⟩ := StoreConst.andUncompute (Var := Var) v s.c₁ s.c₂ s.anc s.h₁₂
          (qAssignObsMap s.post.eval M)
        let M_mid : Observable (Fin (2 ^ n)) := qAssignObsMap s.midPost.eval M_and
        let Θ : CQAssertionCompat Var (2 ^ n) := wpQAssignCompat s.post.eval (fun _ ↦ M)
        have hΨ_eq : wpQAssignCompat s.midPost.eval
            (wp (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).compile Θ) = fun _ ↦ M_mid :=
              by
          dsimp only [Θ, M_mid]
          rw [show (fun _ : Store Var ↦ qAssignObsMap s.post.eval M) =
            wpQAssignCompat s.post.eval (fun _ ↦ M) from rfl] at hM_and
          rw [hM_and]
          rfl
        have himg_out : (rPool.slice offset ((s :: rest).length + m_rem) (by
          simp [List.length_cons]; omega)).image =
            rTot.image := slice_image_eq rPool _ _ rfl (by simp [List.length_cons]; omega)
        have himg_split : rTot.image = ((QRegister.singleton s.anc).concat rRestSlice
          hdisj_anc_rest).image := by
          ext w
          simp only [QRegExt.image_concat, QRegister.image_singleton, Finset.singleton_union,
            Finset.mem_insert]
          refine ⟨fun hw ↦ ?_, ?_⟩
          · rcases (QRegister.mem_image _ w).mp hw with ⟨idx, rfl⟩
            by_cases hi0 : idx.val = 0
            · exact Or.inl (by rw [(Fin.ext hi0 : idx = 0), hanc0])
            · exact Or.inr ((QRegister.mem_image _ _).mpr ⟨⟨idx.val - 1, by omega⟩,
                congrArg rTot.wires (Fin.ext (by dsimp; omega))⟩)
          · rintro (rfl | hw)
            · exact hanc0 ▸ (QRegister.mem_image _ _).mpr ⟨0, rfl⟩
            · rcases (QRegister.mem_image _ w).mp hw with ⟨j, rfl⟩
              exact (QRegister.mem_image _ _).mpr ⟨⟨1 + j.val, by omega⟩, rfl⟩
        have hand_disj : Disjoint (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a).support
          rRestSlice.image :=
          Finset.disjoint_of_subset_left (by
            rw [Circuit.support_andCompute]
            exact Finset.insert_subset_iff.mpr ⟨s.c₁_mem, Finset.insert_subset_iff.mpr ⟨s.c₂_mem,
              Finset.singleton_subset_iff.mpr s.anc_mem⟩⟩) hdisj_S_rest
        have hmid_disj := Finset.disjoint_of_subset_left s.local_midPre.support_sub hdisj_S_rest
        rw [restrictAssertionToZeroAncilla_congr_image _ _ _ himg_out,
          restrictAssertionToZeroAncilla_congr_image _ _ _ himg_out,
          show wp (symWrapDynList v (s :: rest) dCore).compile (fun _ ↦ M) =
            wpQAssignCompat s.pre.eval (wpQAssignCompat (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a
              s.h₂a).eval
              (wpQAssignCompat s.midPre.eval (wp (symWrapDynList v rest dCore).compile (fun _ ↦
                M_mid)))) by
            change wp (s.toTempAndStep.wrapDynamic v (symWrapDynList v rest dCore)).compile (fun _ ↦
              M) = _
            simp only [TempAndStep.wrapDynamic, DynamicCircuit.andCompute,
              DynamicCircuit.compile_seq,
              DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat, wp_qSeq,
              Θ, hΨ_eq],
          show wpQAssignCompat U_wrap (fun _ : Store Var ↦ M) = wpQAssignCompat s.pre.eval
            (wpQAssignCompat V Θ) by
            dsimp only [U_wrap, Θ]
            simp only [wpQAssignCompat_comp, mul_assoc],
          restrict_wp_eval_comm s.pre rTot hpre_tot, restrict_wp_eval_comm s.pre rTot hpre_tot]
        apply congrArg (wpQAssignCompat s.pre.eval)
        rw [restrictAssertionToZeroAncilla_congr_image _ _ _ himg_split,
          restrictAssertionToZeroAncilla_congr_image _ _ _ himg_split,
          restrictAssertionToZeroAncilla_concat _ (QRegister.singleton s.anc) rRestSlice
            hdisj_anc_rest,
          restrictAssertionToZeroAncilla_concat _ (QRegister.singleton s.anc) rRestSlice
            hdisj_anc_rest,
          restrictAssertionToZeroAncilla_comm _ (QRegister.singleton s.anc) rRestSlice,
          restrict_wp_eval_comm _ rRestSlice hand_disj, restrict_wp_eval_comm s.midPre rRestSlice
            hmid_disj,
          hslice_eq, hwp_rest M_mid, ← hslice_eq,
          ← restrict_wp_eval_comm s.midPre rRestSlice hmid_disj, ← restrict_wp_eval_comm _
            rRestSlice hand_disj,
          restrictAssertionToZeroAncilla_comm _ rRestSlice (QRegister.singleton s.anc)]
        apply congrArg (fun A ↦ CQAssertion.restrictToZeroAncilla A rRestSlice)
        have hV_restrict (Ψ : CQAssertionCompat Var (2 ^ n)) :
            CQAssertion.restrictToZeroAncilla (wpQAssignCompat V (CQAssertion.restrictToZeroAncilla
              Ψ (QRegister.singleton s.anc)))
              (QRegister.singleton s.anc) =
            CQAssertion.restrictToZeroAncilla (wpQAssignCompat V Ψ) (QRegister.singleton s.anc) :=
              funext fun σ ↦ Subtype.ext <| by
          simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
            Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
          rw [← Matrix.mul_assoc, show P₀ * V.1ᴴ * P₀ = P₀ * V.1ᴴ by
            simpa [P₀, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose _ 0,
              ← Matrix.mul_assoc] using
              congrArg conjTranspose hc_body]
        rw [DynCircuitExt.restrictAssertionToZeroAncilla_wpQAssign_andCompute s.c₁ s.c₂ s.anc s.h₁₂
          s.h₁a s.h₂a,
          show wpQAssignCompat s.midPre.eval (wpQAssignCompat U_rest (fun _ : Store Var ↦ M_mid)) =
            wpQAssignCompat U_body (wp (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).compile
              Θ) by
            rw [← hΨ_eq]
            dsimp only [U_body]
            simp only [wpQAssignCompat_comp, mul_assoc],
          wpQAssignCompat_comp T_anc U_body, show U_body * T_anc = T_anc * V by
            dsimp [V]
            rw [← mul_assoc, ← mul_assoc, show T_anc * T_anc = 1 from Subtype.ext
              (matrix_ext_basisKet fun γ ↦ by
              simp only [T_anc, cToff3, Submonoid.coe_mul, OneMemClass.coe_one,
                ← Matrix.mulVec_mulVec,
                Matrix.one_mulVec, evolve_TOFF_basisKet, toff_update_self_cancel s.c₁ s.c₂ s.anc
                  s.h₁a s.h₂a γ]), one_mul],
          ← wpQAssignCompat_comp, ← hV_restrict,
          restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
            v s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a Θ (fun _ _ ↦ rfl), hV_restrict]
theorem symWrapDynList_realizesEmbeddedUnitary
    {Var : Type} [Fintype Var] [DecidableEq Var] {n m_pool m_bot m_rem k_act k_sub : ℕ} (v : Var)
    (rAct : QRegister k_act n) (rPool : QRegister m_pool n) (rSub : QRegister k_sub n)
    (hPool : m_bot + m_rem ≤ m_pool) (L : List (SymTempAndStep n))
    (hvalid : ValidSymStepList (∅ : Finset (Wire n)) (rPool.slice 0 m_bot (by omega)) 0 L)
    (hlen : L.length = m_bot) (hdisj_L_sub : ∀ s ∈ L, Disjoint s.S rSub.image)
    (hdisj_L_rem : ∀ s ∈ L, Disjoint s.S (rPool.slice m_bot m_rem hPool).image)
    {k_core : ℕ} (rCore : QRegister k_core n) (uCore : Unitary (2 ^ k_core)) (dCore : DynamicCircuit
      Var n)
    (hdCore : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rCore (rPool.slice m_bot m_rem hPool) uCore dCore) (φCore : BitAssignment n → Bool)
    (uBranch : BitAssignment n → Unitary (2 ^ k_sub)) (hcore_evolve : ∀ γ : BitAssignment n,
      (rCore.embedUnitary uCore).1.mulVec (basisKet γ) =
        (if φCore γ then (-1 : ℂ) else 1) • (rSub.embedUnitary (uBranch γ)).1.mulVec (basisKet γ))
    (uTarget : Unitary (2 ^ k_act)) (htarget_on_zero : ∀ β : BitAssignment n,
      (∀ j : Fin (m_bot + m_rem), β ((rPool.slice 0 (m_bot + m_rem) (by omega)) j) = 0) →
      (if φCore (symStepFwdList L β) then (-1 : ℂ) else 1) •
          (rSub.embedUnitary (uBranch (symStepFwdList L β))).1.mulVec (basisKet β) =
        (rAct.embedUnitary uTarget).1.mulVec (basisKet β)) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rPool uTarget (symWrapDynList v L
      dCore) := by
  have hwp_core (M : Observable (Fin (2 ^ n))) :
      CQAssertion.restrictToZeroAncilla (wp dCore.compile (fun _ ↦ M)) (rPool.slice m_bot m_rem
        hPool) =
        CQAssertion.restrictToZeroAncilla (wpQAssignCompat (rCore.embedUnitary uCore) (fun _ ↦ M))
          (rPool.slice m_bot m_rem hPool) := by
    obtain ⟨M', hwp, hproj⟩ := hdCore M
    rw [hwp]
    refine funext fun _ ↦ Subtype.ext ?_
    ext1
    have hP_herm : ((rPool.slice m_bot m_rem hPool).basisOutcomeProjector 0)ᴴ =
        (rPool.slice m_bot m_rem hPool).basisOutcomeProjector 0 :=
      (rPool.slice m_bot m_rem hPool).basisOutcomeProjector_conjTranspose 0
    simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
      Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat,
        conjTranspose_conjTranspose,
      hP_herm]
    exact hproj
  obtain ⟨U_wrap, hconst_wrap, hevolve_wrap, hwp_wrap⟩ :=
    symWrapDynList_unitary_gen v rPool hPool rSub 0 L hvalid (by omega) hdisj_L_sub hdisj_L_rem
      dCore (rCore.embedUnitary uCore) φCore uBranch
      (fun M ↦ ⟨(hdCore M).choose, (hdCore M).choose_spec.1⟩) hcore_evolve hwp_core
  let rUsed := rPool.slice 0 (m_bot + m_rem) (by omega)
  apply DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace.widenWorkspace
    (sel := QRegister.block 0 (m_bot + m_rem) (by omega))
  rw [show rPool.compose (QRegister.block 0 (m_bot + m_rem) (by omega)) = rUsed from qreg_ext fun _
    ↦ rfl]
  intro M
  obtain ⟨M', hm'⟩ := hconst_wrap M
  refine ⟨M', hm', ?_⟩
  have hP_herm := rUsed.basisOutcomeProjector_conjTranspose 0
  have hadj : rUsed.basisOutcomeProjector 0 * U_wrap.1ᴴ =
      rUsed.basisOutcomeProjector 0 * (rAct.embedUnitary uTarget).1ᴴ := by
    simpa only [conjTranspose_mul, hP_herm] using congrArg conjTranspose (show U_wrap.1 *
      rUsed.basisOutcomeProjector 0 =
        (rAct.embedUnitary uTarget).1 * rUsed.basisOutcomeProjector 0 from matrix_ext_basisKet fun β
          ↦ by
        simp only [← Matrix.mulVec_mulVec, register_basisOutcomeProjector_zero_mulVec_basisKet]
        split_ifs with h0
        · exact (hevolve_wrap β).trans (htarget_on_zero β h0)
        · simp)
  have himg : (rPool.slice 0 (L.length + m_rem) (by omega)).image = rUsed.image := slice_image_eq
    rPool _ _ rfl (by omega)
  have h1 := congrArg (fun A ↦ (A (fun _ ↦ 0)).1) ((restrictAssertionToZeroAncilla_congr_image _ _ _
    himg).symm.trans
      ((hwp_wrap M).trans (restrictAssertionToZeroAncilla_congr_image (wpQAssignCompat U_wrap _) _ _
        himg)))
  rw [hm'] at h1
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj] at h1
  rw [hadj] at h1
  simpa [Matrix.mul_assoc, hP_herm] using congrArg Subtype.val h1
-- ============================================================================
-- Section 3: Held (`0-T`) & Unheld (`16-T`) Phase Fixup & Forward `19`-Wire Syndrome Compute
-- ============================================================================
/-- 6-wire electron field `f : Fin 654` inside `rBE : QRegister (fullSysBEWires mPayload) n`. -/
def rElecFieldInBE {n : ℕ} (mPayload : ℕ) (rBE : QRegister (fullSysBEWires mPayload) n) (f : Fin
    654) : QRegister 6 n :=
  (rBE.compose (beSysReg mPayload)).compose (QRegister.block (6 * f.val) 6 (by
    have := f.isLt; change _ ≤ 3948; omega))
@[simp]
theorem rElecFieldInBE_apply {n : ℕ} (mPayload : ℕ) (rBE : QRegister (fullSysBEWires mPayload) n)
    (f : Fin 654) (u : Fin 6) :
    rElecFieldInBE mPayload rBE f u = rBE (beSysReg mPayload (electronFieldLinearIdx f u)) := rfl
theorem disjointWires_slice_left {k m n : ℕ} {r₁ : QRegister k n} {r₂ : QRegister m n}
    (h : r₁.DisjointWires r₂) (off len : ℕ) (hlen : off + len ≤ k) : (r₁.slice off len
      hlen).DisjointWires r₂ :=
  QRegister.disjoint_iff.mpr fun i j hij ↦ h.ne ⟨off + i.val, by omega⟩ j (by
    simpa [QRegister.slice_apply] using hij)
theorem disjointWires_slice_right {k m n : ℕ} {r₁ : QRegister k n} {r₂ : QRegister m n}
    (h : r₁.DisjointWires r₂) (off len : ℕ) (hlen : off + len ≤ m) : r₁.DisjointWires (r₂.slice off
      len hlen) :=
  (QRegExt.disjointWires_symm (disjointWires_slice_left (QRegExt.disjointWires_symm h) off len
    hlen))
theorem validSymStepList_slice_zero {n m_pool m_bot : ℕ} {M : Finset (Wire n)}
    {rPool : QRegister m_pool n} (hbot : m_bot ≤ m_pool) : ∀ {offset : ℕ} {L : List (SymTempAndStep
      n)},
      offset + L.length ≤ m_bot → ValidSymStepList M rPool offset L →
      ValidSymStepList M (rPool.slice 0 m_bot (by omega)) offset L
  | _, [], _, _ => trivial
  | offset, _ :: _, hlen, ⟨_, hanc, hdisj, hlat, hrest⟩ =>
      ⟨by simp [List.length_cons] at hlen; omega,
       by
         rw [hanc, QRegister.slice_apply]
         exact congrArg rPool.wires (Fin.ext (Nat.zero_add offset).symm),
       hdisj,
       fun j hj ↦ by
         rw [QRegister.slice_apply]
         exact hlat ⟨0 + j.val, by omega⟩ (by dsimp; omega),
       validSymStepList_slice_zero hbot (by simp [List.length_cons] at hlen; omega) hrest⟩
theorem elecLow5ValidBool_eq_false_iff {n : ℕ} (rField : QRegister 6 n) (β : BitAssignment n) :
    fieldValidBool true (rField.slice 0 5 (by decide)) β = false ↔ ∀ u : Fin 5,
      β (rField u.castSucc) = 0 := by
  unfold fieldValidBool polBit
  simp only [↓reduceIte, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_iff]
  refine ⟨fun ⟨hlow, h4⟩ u ↦ ?_, fun hall ↦ ⟨fun u ↦ ?_, ?_⟩⟩
  · rcases (by omega : u.val < 4 ∨ u.val = 4) with hu4 | hu4
    · rw [← show (rField.slice 0 5 (by decide)) ⟨u.val, by omega⟩ = rField u.castSucc from
        congrArg rField.wires (Fin.ext (by simp))]
      exact hlow ⟨u.val, hu4⟩
    · rw [show u.castSucc = (⟨4, by decide⟩ : Fin 6) from Fin.ext hu4]
      simpa [QRegister.slice_apply] using (by decide : ∀ b : ZMod 2, b + 1 = 1 → b = 0) _ h4
  · rw [show (rField.slice 0 5 (by decide)) u.castSucc = rField (⟨u.val, by omega⟩ : Fin 5).castSucc
      from
      congrArg rField.wires (Fin.ext (by simp))]
    exact hall ⟨u.val, by omega⟩
  · rw [show β ((rField.slice 0 5 (by decide)) ⟨4, by decide⟩) = 0 by
      simpa [QRegister.slice_apply] using hall 4]
    rfl
/-- Effective field-badness predicate on `(rBE, rMid, rHeld)`: uses held flag `rHeld (4*i + 3)` for
`i < p_held` and all 6 field wires of `rBE` for `p_held ≤ i < 654`. -/
def effElecBadOnData (mPayload kMid p_held : ℕ)
    (x : Fin (2 ^ ((fullSysBEWires mPayload + kMid) + 4 * p_held))) (f : Fin 654) : Bool :=
  let γ := basisBits ((fullSysBEWires mPayload + kMid) + 4 * p_held) x
  let rBELoc : QRegister (fullSysBEWires mPayload) ((fullSysBEWires mPayload + kMid) + 4 *
    p_held) :=
    QRegister.block 0 (fullSysBEWires mPayload) (by omega)
  let rHeldLoc : QRegister (4 * p_held) ((fullSysBEWires mPayload + kMid) + 4 * p_held) :=
    QRegister.block (fullSysBEWires mPayload + kMid) (4 * p_held) le_rfl
  if hf : f.val < p_held then
    decide (γ (rHeldLoc ⟨4 * f.val + 3, by omega⟩) = 0) &&
      decide (γ (rBELoc (beSysReg mPayload (electronFieldLinearIdx f 5))) = 1)
  else
    elecFieldBadBits (fun u ↦ γ (rBELoc (beSysReg mPayload u))) f
theorem effElecBadOnData_extractIndex {n : ℕ} (mPayload kMid p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n) (rHeld : QRegister (4 *
      p_held) n)
    (hBEMid : rBE.DisjointWires rMid) (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (β : BitAssignment n) (f : Fin 654) : effElecBadOnData mPayload kMid p_held
        (((rBE.concat rMid hBEMid).concat rHeld hBMHeld).extractIndex ((basisBitsEquiv n).symm β))
          f =
      if hf : f.val < p_held then
        decide (β (rHeld ⟨4 * f.val + 3, by omega⟩) = 0) &&
          decide (β (rBE (beSysReg mPayload (electronFieldLinearIdx f 5))) = 1)
      else
        elecFieldBadBits (fun u ↦ β (rBE (beSysReg mPayload u))) f := by
  let rDataHeld := (rBE.concat rMid hBEMid).concat rHeld hBMHeld
  have hbit_BE (h_le : 0 + fullSysBEWires mPayload ≤ (fullSysBEWires mPayload + kMid) + 4 * p_held)
      (idx : Fin (fullSysBEWires mPayload)) : basisBits ((fullSysBEWires mPayload + kMid) + 4 *
        p_held)
        (rDataHeld.extractIndex ((basisBitsEquiv n).symm β))
        (QRegister.block 0 (fullSysBEWires mPayload) h_le idx) = β (rBE idx) := by
    rw [rDataHeld.basisBits_extractIndex, basisBits_basisBitsEquiv_symm_eq,
      show QRegister.block 0 (fullSysBEWires mPayload) h_le idx =
        Fin.castAdd (4 * p_held) (Fin.castAdd kMid idx) from Fin.ext (by simp [QRegister.block]),
      QRegister.concat_apply_left, QRegister.concat_apply_left]
  have hbit_Held (h_le : (fullSysBEWires mPayload + kMid) + 4 * p_held ≤
        (fullSysBEWires mPayload + kMid) + 4 * p_held) (idx : Fin (4 * p_held)) :
      basisBits ((fullSysBEWires mPayload + kMid) + 4 * p_held) (rDataHeld.extractIndex
        ((basisBitsEquiv n).symm β))
        (QRegister.block (fullSysBEWires mPayload + kMid) (4 * p_held) h_le idx) = β (rHeld idx) :=
          by
    rw [rDataHeld.basisBits_extractIndex, basisBits_basisBitsEquiv_symm_eq,
      show QRegister.block (fullSysBEWires mPayload + kMid) (4 * p_held) h_le idx =
        Fin.natAdd (fullSysBEWires mPayload + kMid) idx from Fin.ext (by simp [QRegister.block]),
          QRegister.concat_apply_right]
  dsimp only [rDataHeld] at hbit_BE hbit_Held
  dsimp only [effElecBadOnData]
  simp only [hbit_BE, hbit_Held]
theorem sum_if_lt_finRange : ∀ (N p a b : ℕ), p ≤ N →
      ((List.finRange N).map fun f : Fin N ↦ if f.val < p then a else b).sum = a * p + b * (N - p)
  | 0, p, _, _, hp => by
      rw [Nat.eq_zero_of_le_zero hp]
      simp
  | N + 1, p, a, b, hp => by
      rw [← Fin.sum_univ_def, Fin.sum_univ_castSucc]
      rcases (by omega : p ≤ N ∨ p = N + 1) with hpN | rfl
      · rw [show (∑ i : Fin N, if (i.castSucc : Fin (N + 1)).val < p then a else b) = a * p + b *
          (N - p) by
            simpa only [Fin.val_castSucc, ← Fin.sum_univ_def] using sum_if_lt_finRange N p a b hpN,
          ite_eq_right (by rw [Fin.val_last]; omega : ¬((Fin.last N).val < p)),
          show N + 1 - p = (N - p) + 1 by omega]
        ring
      · simp only [show ∀ i : Fin N, (i.castSucc : Fin (N + 1)).val < N + 1 from fun i ↦
          i.castSucc.isLt,
          ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          ite_eq_left (Fin.last N).isLt, Nat.sub_self]
        ring
theorem sequenceList_diagSignUnitary_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {α :
    Type*} {n k m : ℕ}
    (rAct : QRegister k n) (rWork : QRegister m n) (hdisj : rAct.DisjointWires rWork)
    (L : List α) (pOf : α → Fin (2 ^ k) → Bool) (dOf : α → DynamicCircuit Var n)
    (hd : ∀ a ∈ L, DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      (_root_.QuantumComputation.Specs.StoppingPowerSolution.diagSignUnitary (pOf a)) (dOf a)) :
        DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      (_root_.QuantumComputation.Specs.StoppingPowerSolution.diagSignUnitary fun x ↦ L.foldr (fun a
        acc ↦ xor (pOf a x) acc) false)
      (DynCircuitExt.sequenceList (L.map dOf)) := by
  induction L with
  | nil =>
      simp only [List.foldr_nil, List.map_nil, DynCircuitExt.sequenceList_nil,
        diagSignUnitary_false]
      exact DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_identity rAct rWork
  | cons a tl ih =>
      simp only [List.map_cons, DynCircuitExt.sequenceList_cons, List.foldr_cons]
      have hseq := DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace.seq hdisj
        (hd a (List.mem_cons_self ..)) (ih fun b hb ↦ hd b (List.mem_cons_of_mem a hb))
      have hxor (p₁ p₂ : Fin (2 ^ k) → Bool) :
          _root_.QuantumComputation.Specs.StoppingPowerSolution.diagSignUnitary p₁ *
            _root_.QuantumComputation.Specs.StoppingPowerSolution.diagSignUnitary p₂ =
            _root_.QuantumComputation.Specs.StoppingPowerSolution.diagSignUnitary (fun x ↦
            xor (p₂ x) (p₁ x)) := by
        apply Subtype.ext
        rw [Submonoid.coe_mul]
        change (Matrix.diagonal fun x : Fin (2 ^ k) ↦ if p₁ x then (-1 : ℂ) else 1) *
            (Matrix.diagonal fun x : Fin (2 ^ k) ↦ if p₂ x then (-1 : ℂ) else 1) =
          Matrix.diagonal fun x : Fin (2 ^ k) ↦ if xor (p₂ x) (p₁ x) then (-1 : ℂ) else 1
        rw [Matrix.diagonal_mul_diagonal]
        refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
        cases p₁ x <;> cases p₂ x <;> norm_num
      rwa [hxor] at hseq
theorem validSymStepList_disjoint {n m_anc : ℕ} {M : Finset (Wire n)} {rAnc : QRegister m_anc n} :
    ∀ {offset : ℕ} {L : List (SymTempAndStep n)}, ValidSymStepList M rAnc offset L → ∀ s ∈ L,
      Disjoint s.S M
  | _, [], _, _, hs => False.elim (List.not_mem_nil hs)
  | _, _ :: _, ⟨_, _, hdisj, _, hrest⟩, _, hs =>
      (List.mem_cons.mp hs).elim (fun h ↦ h ▸ hdisj) (validSymStepList_disjoint hrest _)
theorem validSymStepList_mono {n m_anc : ℕ} {M M' : Finset (Wire n)} (hsub : M' ⊆ M)
    {rAnc : QRegister m_anc n} : ∀ {offset : ℕ} {L : List (SymTempAndStep n)},
      ValidSymStepList M rAnc offset L → ValidSymStepList M' rAnc offset L
  | _, [], _ => trivial
  | _, _ :: _, ⟨hlt, hanc, hdisj, hlat, hrest⟩ =>
      ⟨hlt, hanc, Finset.disjoint_of_subset_right hsub hdisj, hlat, validSymStepList_mono hsub
        hrest⟩
noncomputable def involUnitary {d : ℕ} (perm : Fin d → Fin d) (hinv : Function.Involutive perm) :
    Unitary d :=
  ⟨Matrix.of fun i j ↦ if i = perm j then (1 : ℂ) else 0, by
    set M := Matrix.of fun i j : Fin d ↦ if i = perm j then (1 : ℂ) else 0
    have hsym (i j : Fin d) : (i = perm j) ↔ (j = perm i) := ⟨fun h ↦ by
      rw [h, hinv j], fun h ↦ by rw [h, hinv i]⟩
    have hsa : star M = M := by
      ext i j
      simp only [M, Matrix.star_apply, Matrix.of_apply, hsym j i]
      split_ifs <;> simp
    have hsq : M * M = 1 := by
      ext i j
      simp only [M, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
      rw [Finset.sum_eq_single (perm j) (fun _ _ hk ↦ by simp [hk]) (fun h ↦ absurd (Finset.mem_univ
        _) h)]
      simp [hinv j]
    rw [Unitary.mem_iff, hsa]
    exact ⟨hsq, hsq⟩⟩
theorem involUnitary_mulVec_single {d : ℕ} (perm : Fin d → Fin d) (hinv : Function.Involutive perm)
    (j : Fin d) : (involUnitary perm hinv).1.mulVec (Pi.single j 1) = Pi.single (perm j) 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change (if i = perm j then (1 : ℂ) else 0) = (Pi.single (perm j) (1 : ℂ) : Fin d → ℂ) i
  by_cases hi : i = perm j <;> simp [hi]
end SyndromeUncomp
end SyndromeUncomp

noncomputable section MidGuardGuard24000

section
set_option backward.isDefEq.respectTransparency false
namespace MidGuardGuard24000
section Config
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority := 1000000) instNeZeroTwoPowExt (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (TOFF T)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
open SpecsAux SpecsAux.SpecMirror GridGuard654Flag288
open PhaseGradSignalRot hiding IntertwinesCat
open SingleRBEGridGuardWalk (diagProj diagProj_isHermitian diagProj_idem)
open FullSysCatSegmentBridge (fullSysBEWires fullSysRawAncWires)
open FullSysGuardWrapSpec (midEmbed)
open GridGuard654ReflAux hiding disjointWires_concat_left
open SingleCatClosure (rBEInSingleCat qSigInSingleCat optXSingleCat compose_concat_eq_singleCat)
open GidneySignalRotPart1
open InterWalkRSum42Hoist (kActOrig kFull80 rAct0 rBEOrig E_stream42 qreg_ext qreg_block_apply)
open GidneyTwoAngleGuardWrap220 (uSigMidTwoAngle43)
open HoistBorrow42ProjBridge (RealizesOnProj)
open HoistBorrow42TwoAngleBridge (uSignalRotTwoAngleSingleCat)
open Leaf4Ext48TopStitch (rUnusedCtrl3Orig rAct0_val_eq pCtrl3ZeroOrig pCtrl3Zero pSlack3Zero
  pPGIdleZero E_segExt pHoistExtOn pExt6Zero_eq_mul pExt6IdleZero_eq_mul E_stream42_comm_pCtrl3Zero
  embedAct0_pCtrl3ZeroOrig rBE77Orig rMid43Orig rMid43Full rMid43Orig_zero_val
  rBE77Orig_disj_rMid43Orig rBEMid77Orig rMid43EffFull rMid43EffFull_val_eq rBEMid77Full
  rBEMid77EffFull embedUnitary_rMid43EffFull_uSigMidTwoAngle43_eq)
open ChainedGuardStepBridge
open SyndromeUncomp
theorem ite_true_eq {c : Prop} [Decidable c] (hc : c) {α : Sort _} {t e : α} :
    (if c then t else e) = t := by simp [hc]
theorem ite_false_eq {c : Prop} [Decidable c] (hnc : ¬ c) {α : Sort _} {t e : α} :
    (if c then t else e) = e := by simp [hnc]
set_option exponentiation.threshold 5000 in
/-- Tight 2-kick Gidney guard-wrap bundle on `(kFull80, mWork)` over `pHoistExtOn k_idle hk` with
zero step-recompute overhead (`2 * gidneyRotToffEquiv C_d.val + 2 * gidneyRotToffEquiv D_d.val`,
yielding `2 * rotToffSum` directly at `C_d = 0`). -/
structure GidneyTwoKickExtHkGuardSpecBundleGen
    (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool)
    (mWork k_idle : ℕ) (hk : k_idle ≤ 48) (tGuard : ℕ) where
  dGuardWrap : ∀ {Var : Type} {n : ℕ},
    Bool → Bool → Fin (2 ^ 42) → Fin (2 ^ 42) → Var →
    (rAct : QRegister kFull80 n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  hToff : ∀ {Var : Type} {n : ℕ} (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42)) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dGuardWrap bPre bPost C_d D_d v rAct rWork hDisj).count TOFF = 0
  hT : ∀ {Var : Type} {n : ℕ} (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42)) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dGuardWrap bPre bPost C_d D_d v rAct rWork hDisj).count T ≤
      tGuard + 2 * gidneyRotToffEquiv C_d.val + 2 * gidneyRotToffEquiv D_d.val
  hRealizes : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42))
    (_hC : 2 ^ (k_idle - 6) ∣ C_d.val) (_hD : 2 ^ (k_idle - 6) ∣ D_d.val) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    RealizesOnProj (pHoistExtOn k_idle hk rAct rWork)
      (rAct.embedUnitary
        (rAct0.embedUnitary
          (uGuardWrapTwoAngleSingleCatGen bValid (by decide : 42 ≤ 48) bPre bPost C_d D_d)))
      (dGuardWrap bPre bPost C_d D_d v rAct rWork hDisj)
def validBEPredBoolGen (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool) (mPayload : ℕ)
    (γ : BitAssignment (fullSysBEWires mPayload)) : Bool :=
  bValid ((basisBitsEquiv SpecsAux.SpecMirror.systemQubits).symm (fun u ↦ γ (beSysReg mPayload u)))
    &&
    decide (∀ j : Fin (fullSysRawAncWires mPayload), γ (beAncReg mPayload j) = 0)
theorem validBEPredBoolGen_iff (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) →
    Bool) (mPayload : ℕ) (x : Fin (2 ^ (fullSysBEWires mPayload))) : validBEPredBoolGen bValid
    mPayload (basisBits (fullSysBEWires
    mPayload) x) = true ↔ (beAncReg mPayload).extractIndex x = 0 ∧ bValid ((beSysReg
      mPayload).extractIndex x) = true := by
  have hsys_eq : (basisBitsEquiv SpecsAux.SpecMirror.systemQubits).symm
        (fun u ↦ basisBits (fullSysBEWires mPayload) x (beSysReg mPayload u)) =
      (beSysReg mPayload).extractIndex x := by
    apply (basisBitsEquiv SpecsAux.SpecMirror.systemQubits).injective
    rw [Equiv.apply_symm_apply]
    funext u
    exact (QRegister.basisBits_extractIndex (beSysReg mPayload) x u).symm
  have hanc_iff : (∀ j : Fin (fullSysRawAncWires mPayload), basisBits (fullSysBEWires
      mPayload) x (beAncReg mPayload j) = 0) ↔ (beAncReg mPayload).extractIndex x = 0 := by
    rw [QRegExt.extractIndex_eq_zero_iff]
  unfold validBEPredBoolGen
  rw [hsys_eq]
  simp only [Bool.and_eq_true, decide_eq_true_iff, hanc_iff, and_comm]
theorem guardPolLocalGen_mulVec_basisKet
    (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool) {n : ℕ} (mPayload kMid : ℕ)
    (hkMid : 1 ≤ kMid) (pol : Bool) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid : QRegister kMid n) (hBEMid : rBE.DisjointWires rMid) (δ : BitAssignment n) :
    ((rBE.concat rMid hBEMid).embedUnitary (guardPolLocalGen bValid mPayload kMid hkMid
    pol)).1.mulVec (basisKet δ) = (if pol && validBEPredBoolGen bValid mPayload (fun i ↦ δ
    (rBE i)) && decide (δ (rMid ⟨0, hkMid⟩) = 1) then (-1 : ℂ) else 1) • basisKet δ := by
  let rBEMid := rBE.concat rMid hBEMid
  cases pol
  · rw [show guardPolLocalGen bValid mPayload kMid hkMid false = 1 from rfl,
      rBEMid.embedUnitary_one, Submonoid.coe_one, Matrix.one_mulVec]
    simp
  · let rSubLoc : QRegister (fullSysBEWires mPayload + 1) (fullSysBEWires mPayload + kMid) :=
      .block 0 (fullSysBEWires mPayload + 1)
        ((Nat.zero_add _).le.trans (Nat.add_le_add_left hkMid _))
    have hdisj_sig : rBE.DisjointWires (QRegister.singleton (rMid ⟨0, hkMid⟩)) :=
      disjointWires_singleton_of_not_mem rBE _ (hBEMid.apply_not_mem_left ⟨0, hkMid⟩)
    let rBESig := rBE.concat (QRegister.singleton (rMid ⟨0, hkMid⟩)) hdisj_sig
    have hcomp_sub : rBEMid.compose rSubLoc = rBESig := by
      apply qreg_ext; intro idx
      refine Fin.addCases (fun i₀ ↦ ?_) (fun j₀ ↦ ?_) idx
      · have hl : rSubLoc (Fin.castAdd 1 i₀) = Fin.castAdd kMid i₀ := by ext; simp [rSubLoc]
        simp only [QRegister.compose_apply, hl, rBEMid, rBESig, QRegister.concat_apply_left]
      · have hj₀ : j₀ = 0 := Subsingleton.elim _ _; subst hj₀
        have hl : rSubLoc (Fin.natAdd (fullSysBEWires mPayload) 0) =
            Fin.natAdd (fullSysBEWires mPayload) ⟨0, hkMid⟩ := by ext; simp [rSubLoc]
        simp only [QRegister.compose_apply, hl, rBEMid, rBESig, QRegister.concat_apply_right,
          QRegister.singleton_apply]
    let g_idx := (basisBitsEquiv n).symm δ
    have hg_bits : basisBits n g_idx = δ := basisBits_basisBitsEquiv_symm_eq δ
    let l_sub : Fin (2 ^ (fullSysBEWires mPayload + 1)) := rBESig.extractIndex g_idx
    let l_be : Fin (2 ^ (fullSysBEWires mPayload)) :=
      (QRegister.block 0 (fullSysBEWires mPayload) (by omega)).extractIndex l_sub
    have hl_be_eq : l_be = rBE.extractIndex g_idx := by
      dsimp only [l_be, l_sub]
      rw [← QRegister.extractIndex_compose]
      have hc : rBESig.compose (.block 0 (fullSysBEWires mPayload) (by omega)) = rBE := by
        apply qreg_ext; intro i
        have h1 : (QRegister.block 0 (fullSysBEWires mPayload) (by omega)) i = Fin.castAdd 1 i :=
          by ext; simp
        change rBESig ((QRegister.block 0 (fullSysBEWires mPayload) (by omega)) i) = rBE i
        rw [h1, QRegister.concat_apply_left]
      rw [hc]
    have hsig_bit : basisBits (fullSysBEWires mPayload + 1) l_sub
        ⟨fullSysBEWires mPayload, by omega⟩ = δ (rMid ⟨0, hkMid⟩) := by
      dsimp only [l_sub]
      rw [QRegister.basisBits_extractIndex, hg_bits]
      have h1 : (⟨fullSysBEWires mPayload, by omega⟩ : Fin (fullSysBEWires mPayload + 1)) =
          Fin.natAdd (fullSysBEWires mPayload) (0 : Fin 1) := by ext; rfl
      rw [h1, QRegister.concat_apply_right]; rfl
    have hsingle_ctrl : (ctrlLocalUnitary (fullSysGuardReflUnitaryGen mPayload bValid)).1.mulVec
        (Pi.single l_sub 1) =
        (if validBEPredBoolGen bValid mPayload (basisBits (fullSysBEWires mPayload) l_be) &&
            decide (basisBits (fullSysBEWires mPayload + 1) l_sub
              ⟨fullSysBEWires mPayload, by omega⟩ = 1)
         then (-1 : ℂ) else 1) • Pi.single l_sub 1 := by
      unfold fullSysGuardReflUnitaryGen
      funext y
      change (Slots01AndGridGuardBridge.ctrlInvolutionMatrix ⟨fullSysBEWires mPayload, by omega⟩
        (.block 0 (fullSysBEWires mPayload) (by omega))
        (singleRBEReflNegMatrix SpecsAux.SpecMirror.systemQubits (fullSysRawAncWires mPayload)
          (diagProj SpecsAux.SpecMirror.systemQubits bValid))).mulVec
        (Pi.single l_sub 1) y = _
      have hneg_single := singleRBEReflNegUnitary_mulVec_single
        (k := SpecsAux.SpecMirror.systemQubits) (m_be := fullSysRawAncWires mPayload)
        (diagProj SpecsAux.SpecMirror.systemQubits bValid)
        (fun x ↦ bValid x = true)
        (diagProj_isHermitian SpecsAux.SpecMirror.systemQubits bValid)
        (diagProj_idem SpecsAux.SpecMirror.systemQubits bValid)
        (fun x ↦ by simp [diagProj])
        (fun u v huv ↦ by simp [diagProj, huv])
        l_be
      have hqL_extr : ∀ z : Fin (2 ^ (fullSysBEWires mPayload + 1)),
          (QRegister.singleton (⟨fullSysBEWires mPayload, by omega⟩ :
            Wire (fullSysBEWires mPayload + 1))).extractIndex z =
            if basisBits (fullSysBEWires mPayload + 1) z
              ⟨fullSysBEWires mPayload, by omega⟩ = 0 then 0 else 1 := by
        intro z
        have hz : ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) =
            if b = 0 then 0 else 1 := fun b ↦ by
          rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide
        simpa [QRegister.extractIndex] using hz _
      have hembed_neg : ((QRegister.block 0 (fullSysBEWires mPayload) (by omega)).embedMatrix
          (singleRBEReflNegMatrix SpecsAux.SpecMirror.systemQubits (fullSysRawAncWires mPayload)
            (diagProj SpecsAux.SpecMirror.systemQubits bValid))).mulVec (Pi.single l_sub 1) =
          (if validBEPredBoolGen bValid mPayload (basisBits (fullSysBEWires mPayload) l_be)
           then (-1 : ℂ) else 1) • Pi.single l_sub 1 := by
        rw [QRegister.embedMatrix_mulVec_single_factors, show (singleRBEReflNegMatrix
          SpecsAux.SpecMirror.systemQubits (fullSysRawAncWires mPayload) (diagProj
          SpecsAux.SpecMirror.systemQubits bValid)) =
            (singleRBEReflNegUnitary SpecsAux.SpecMirror.systemQubits (fullSysRawAncWires mPayload)
              (diagProj SpecsAux.SpecMirror.systemQubits bValid) (diagProj_isHermitian
              SpecsAux.SpecMirror.systemQubits bValid)
            (diagProj_idem SpecsAux.SpecMirror.systemQubits bValid)).1 from rfl, hneg_single,
              QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex,
              QRegister.replaceIndex_extractIndex]
        change ((if (beAncReg mPayload).extractIndex l_be = 0 ∧ bValid ((beSysReg
          mPayload).extractIndex l_be) = true then (-1 : ℂ) else 1) • Pi.single l_sub 1) = _
        congr 1
        by_cases hv : validBEPredBoolGen bValid mPayload (basisBits (fullSysBEWires mPayload)
          l_be) = true
        · rw [ite_true_eq hv, ite_true_eq ((validBEPredBoolGen_iff bValid mPayload l_be).mp hv)]
        · rw [ite_false_eq hv, ite_false_eq (mt (validBEPredBoolGen_iff bValid mPayload l_be).mpr
            hv)]
      have hmul_vec : (Slots01AndGridGuardBridge.ctrlInvolutionMatrix
          ⟨fullSysBEWires mPayload, by omega⟩
          (.block 0 (fullSysBEWires mPayload) (by omega))
          (singleRBEReflNegMatrix SpecsAux.SpecMirror.systemQubits (fullSysRawAncWires mPayload)
            (diagProj SpecsAux.SpecMirror.systemQubits bValid))).mulVec (Pi.single l_sub 1) y =
          (((QRegister.singleton (⟨fullSysBEWires mPayload, by omega⟩ :
              Wire (fullSysBEWires mPayload + 1))).basisOutcomeProjector 0).mulVec
              (Pi.single l_sub 1) +
            ((QRegister.singleton (⟨fullSysBEWires mPayload, by omega⟩ :
              Wire (fullSysBEWires mPayload + 1))).basisOutcomeProjector 1).mulVec
              (((QRegister.block 0 (fullSysBEWires mPayload) (by omega)).embedMatrix
                (singleRBEReflNegMatrix SpecsAux.SpecMirror.systemQubits (fullSysRawAncWires
                  mPayload)
                  (diagProj SpecsAux.SpecMirror.systemQubits bValid))).mulVec (Pi.single l_sub 1)))
                    y := by
        rw [show Slots01AndGridGuardBridge.ctrlInvolutionMatrix
            ⟨fullSysBEWires mPayload, by omega⟩
            (.block 0 (fullSysBEWires mPayload) (by omega))
            (singleRBEReflNegMatrix SpecsAux.SpecMirror.systemQubits (fullSysRawAncWires mPayload)
              (diagProj SpecsAux.SpecMirror.systemQubits bValid)) =
          (QRegister.singleton (⟨fullSysBEWires mPayload, by omega⟩ :
            Wire (fullSysBEWires mPayload + 1))).basisOutcomeProjector 0 +
          (QRegister.singleton (⟨fullSysBEWires mPayload, by omega⟩ :
            Wire (fullSysBEWires mPayload + 1))).basisOutcomeProjector 1 *
            (QRegister.block 0 (fullSysBEWires mPayload) (by omega)).embedMatrix
              (singleRBEReflNegMatrix SpecsAux.SpecMirror.systemQubits (fullSysRawAncWires mPayload)
                (diagProj SpecsAux.SpecMirror.systemQubits bValid))
          from rfl,
          Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
      rw [hmul_vec, hembed_neg, Matrix.mulVec_smul]
      simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mulVec, dotProduct,
        Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, Matrix.diagonal_apply,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, hqL_extr]
      by_cases hyl : y = l_sub
      · rw [hyl]
        simp only [↓reduceIte]
        rcases zmod2_eq_zero_or_one
          (basisBits (fullSysBEWires mPayload + 1) l_sub ⟨fullSysBEWires mPayload, by omega⟩)
          with hq0 | hq1
        · cases validBEPredBoolGen bValid mPayload (basisBits (fullSysBEWires mPayload) l_be) <;>
            simp [hq0]
        · cases validBEPredBoolGen bValid mPayload (basisBits (fullSysBEWires mPayload) l_be) <;>
            simp [hq1]
      · simp [hyl]
    have hguard_emb : rBEMid.embedUnitary (guardPolLocalGen bValid mPayload kMid hkMid true) =
        rBESig.embedUnitary (ctrlLocalUnitary (fullSysGuardReflUnitaryGen mPayload bValid)) := by
      dsimp only [guardPolLocalGen]
      simp only [↓reduceIte]
      rw [← QRegister.embedUnitary_compose]
      exact congrArg (fun r : QRegister (fullSysBEWires mPayload + 1) n ↦ r.embedUnitary
        (ctrlLocalUnitary (fullSysGuardReflUnitaryGen mPayload bValid))) hcomp_sub
    rw [hguard_emb, QRegister.embedUnitary_val, basisKet, basisState,
      rBESig.embedMatrix_mulVec_single_factors, hsingle_ctrl, QRegister.tensorState_smul_left,
      QRegister.tensorState_single_replaceIndex,
        rBESig.replaceIndex_extractIndex, pi_single_eq_basisKet, hg_bits]
    have hbe_bits : basisBits (fullSysBEWires mPayload) l_be = fun i ↦ δ (rBE i) := by
      rw [hl_be_eq]; funext i; rw [QRegister.basisBits_extractIndex, hg_bits]
    rw [hbe_bits, hsig_bit]
    simp
theorem guardWrapTargetUnitary_mulVec_basisKet_gen
    (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool)
    {n : ℕ} (mPayload kMid : ℕ) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid : QRegister kMid n)
    (hBEMid : rBE.DisjointWires rMid)
    (uMid : Unitary (2 ^ kMid))
    (β : BitAssignment n) :
    let rBEMid := rBE.concat rMid hBEMid
    let u₁ : Unitary (2 ^ kMid) := optZLocal hkMid bPost * uMid * optZLocal hkMid bPre
    (rBEMid.embedUnitary
        (guardPolLocalGen bValid mPayload kMid hkMid bPost *
          midEmbed mPayload kMid uMid *
          guardPolLocalGen bValid mPayload kMid hkMid bPre)).1.mulVec (basisKet β) =
      (rBEMid.embedUnitary
        (muxFlagUnitary (validBEPredBoolGen bValid mPayload) uMid u₁)).1.mulVec (basisKet β) := by
  intro rBEMid u₁
  let P₀ := rBE.embedMatrix (diagBoolProj fun γ ↦ !validBEPredBoolGen bValid mPayload γ)
  let P₁ := rBE.embedMatrix (diagBoolProj (validBEPredBoolGen bValid mPayload))
  have hmid_eq : rBEMid.embedUnitary (midEmbed mPayload kMid uMid) =
      rMid.embedUnitary uMid := by
    dsimp only [midEmbed]
    rw [← QRegister.embedUnitary_compose]
    congr 1; apply qreg_ext; intro j
    have h1 : (QRegister.block (fullSysBEWires mPayload) kMid le_rfl) j =
        Fin.natAdd (fullSysBEWires mPayload) j := by ext; simp
    change rBEMid ((QRegister.block (fullSysBEWires mPayload) kMid le_rfl) j) = rMid j
    rw [h1, QRegister.concat_apply_right]
  have hc0 : (rMid.embedUnitary uMid).1 * P₀ = P₀ * (rMid.embedUnitary uMid).1 :=
    (rBE.embedMatrix_comm_of_disjoint rMid hBEMid _ uMid.1).symm
  have hc1 : (rMid.embedUnitary uMid).1 * P₁ = P₁ * (rMid.embedUnitary uMid).1 :=
    (rBE.embedMatrix_comm_of_disjoint rMid hBEMid _ uMid.1).symm
  have hg_P0 : ∀ pol : Bool,
      (rBEMid.embedUnitary (guardPolLocalGen bValid mPayload kMid hkMid pol)).1 * P₀ = P₀ := by
    intro pol
    apply matrix_ext_basisKet; intro δ
    rw [← Matrix.mulVec_mulVec]
    dsimp only [P₀]
    rw [embed_diagBoolProj_mulVec_basisKet]
    cases hv : validBEPredBoolGen bValid mPayload (fun i ↦ δ (rBE i))
    · simp only [Bool.not_false, ↓reduceIte, one_smul]
      rw [guardPolLocalGen_mulVec_basisKet]
      simp [hv]
    · simp
  have hg_P1 : ∀ pol : Bool, (rBEMid.embedUnitary (guardPolLocalGen bValid mPayload kMid hkMid
      pol)).1 * P₁ = (rMid.embedUnitary (optZLocal hkMid pol)).1 * P₁ := by
    intro pol
    apply matrix_ext_basisKet; intro δ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [P₁]
    rw [embed_diagBoolProj_mulVec_basisKet]
    cases hv : validBEPredBoolGen bValid mPayload (fun i ↦ δ (rBE i))
    · simp
    · simp only [↓reduceIte, one_smul]
      rw [guardPolLocalGen_mulVec_basisKet, embed_optZLocal_mulVec_basisKet]
      simp [hv]
  rw [embed_muxFlagUnitary_mulVec_basisKet, rBEMid.embedUnitary_mul, rBEMid.embedUnitary_mul,
    Submonoid.coe_mul, Submonoid.coe_mul, hmid_eq]
  cases hv : validBEPredBoolGen bValid mPayload (fun i ↦ β (rBE i))
  · have hp0 : P₀.mulVec (basisKet β) = basisKet β := by
      dsimp only [P₀]; rw [embed_diagBoolProj_mulVec_basisKet]; simp [hv]
    have hmul0 : (rBEMid.embedUnitary (guardPolLocalGen bValid mPayload kMid hkMid bPost)).1 *
        (rMid.embedUnitary uMid).1 * (rBEMid.embedUnitary (guardPolLocalGen bValid mPayload
        kMid hkMid bPre)).1 * P₀ = (rMid.embedUnitary uMid).1 * P₀ := by
      calc _ = (rBEMid.embedUnitary (guardPolLocalGen bValid mPayload kMid hkMid bPost)).1 *
                ((rMid.embedUnitary uMid).1 * P₀) := by
                rw [Matrix.mul_assoc, hg_P0, Matrix.mul_assoc]
        _ = ((rBEMid.embedUnitary (guardPolLocalGen bValid mPayload kMid hkMid bPost)).1 * P₀) *
              (rMid.embedUnitary uMid).1 := by rw [hc0, ← Matrix.mul_assoc]
        _ = (rMid.embedUnitary uMid).1 * P₀ := by rw [hg_P0, hc0]
    rw [← hp0, Matrix.mulVec_mulVec, hmul0, ← Matrix.mulVec_mulVec, hp0]
    simp
  · have hp1 : P₁.mulVec (basisKet β) = basisKet β := by
      dsimp only [P₁]; rw [embed_diagBoolProj_mulVec_basisKet]; simp [hv]
    have hc_pre : (rMid.embedUnitary (optZLocal hkMid bPre)).1 * P₁ =
        P₁ * (rMid.embedUnitary (optZLocal hkMid bPre)).1 :=
      (rBE.embedMatrix_comm_of_disjoint rMid hBEMid _ _).symm
    have hmul1 : (rBEMid.embedUnitary (guardPolLocalGen bValid mPayload kMid hkMid bPost)).1 *
        (rMid.embedUnitary uMid).1 * (rBEMid.embedUnitary (guardPolLocalGen bValid mPayload
        kMid hkMid bPre)).1 * P₁ = (rMid.embedUnitary u₁).1 * P₁ := by
      dsimp only [u₁]
      rw [rMid.embedUnitary_mul, rMid.embedUnitary_mul, Submonoid.coe_mul, Submonoid.coe_mul,
        Matrix.mul_assoc _ _ P₁, hg_P1, hc_pre, ← Matrix.mul_assoc _ P₁, Matrix.mul_assoc _ _ P₁,
        hc1, ← Matrix.mul_assoc _
          P₁, hg_P1, Matrix.mul_assoc _ P₁, ← hc1, ← Matrix.mul_assoc _ _ P₁, Matrix.mul_assoc _ P₁,
            ← hc_pre, ← Matrix.mul_assoc]
    rw [← hp1, Matrix.mulVec_mulVec, hmul1, ← Matrix.mulVec_mulVec, hp1]
    simp
theorem embedUnitary_twoAngleGuardWrap_singleCat_gen (bValid : Fin (2 ^
    SpecsAux.SpecMirror.systemQubits) → Bool) {mPayload B_tot kWorkConst : ℕ} (hB42 : 42 ≤ B_tot)
    (preX postX : Bool) (C_d D_d : Fin (2 ^ 42)) :
    ((rBEInSingleCat mPayload B_tot kWorkConst).concat (rMid43InSingleCat mPayload B_tot kWorkConst
      hB42) (rBEInSingleCat_disj_rMid43 hB42)).embedUnitary (guardPolLocalGen bValid mPayload (1 +
      42) (by decide)
    true * midEmbed mPayload (1 + 42) (uSigMidTwoAngle43 preX postX C_d D_d) * guardPolLocalGen
      bValid mPayload (1 + 42) (by decide) true) = uGuardWrapTwoAngleSingleCatGen bValid hB42 preX
      postX C_d D_d := by
  let kBE := fullSysBEWires mPayload
  let rCat := (rBEInSingleCat mPayload B_tot kWorkConst).concat
    (rMid43InSingleCat mPayload B_tot kWorkConst hB42) (rBEInSingleCat_disj_rMid43 hB42)
  have hGuardEq : rCat.embedUnitary (guardPolLocalGen bValid mPayload (1 + 42) (by decide) true) =
      guardPolSingleCatGen bValid mPayload B_tot kWorkConst true := by
    unfold guardPolLocalGen guardPolSingleCatGen
    simp only [↓reduceIte, ← QRegister.embedUnitary_compose]
    congr 1
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simp only [QRegister.compose_apply]
      have hL : (QRegister.block 0 (kBE + 1)
          ((Nat.zero_add _).le.trans (Nat.add_le_add_left (by decide : 1 ≤ 1 + 42) _)))
          (Fin.castAdd 1 i) = Fin.castAdd (1 + 42) i := by ext; simp
      rw [hL, QRegister.concat_apply_left, QRegister.concat_apply_left]
    · fin_cases j
      simp only [QRegister.compose_apply]
      have hR : (QRegister.block 0 (fullSysBEWires mPayload + 1)
          ((Nat.zero_add _).le.trans (Nat.add_le_add_left (by decide : 1 ≤ 1 + 42) _)))
          (Fin.natAdd (fullSysBEWires mPayload) ⟨0, by decide⟩) =
          Fin.natAdd (fullSysBEWires mPayload) ⟨0, by decide⟩ := by ext; simp
      rw [hR, QRegister.concat_apply_right, QRegister.concat_apply_right, rMid43InSingleCat_zero
        hB42]
      rfl
  have hMidEq : rCat.embedUnitary
      (midEmbed mPayload (1 + 42) (uSigMidTwoAngle43 preX postX C_d D_d)) =
      (rMid43InSingleCat mPayload B_tot kWorkConst hB42).embedUnitary
        (uSigMidTwoAngle43 preX postX C_d D_d) := by
    unfold midEmbed
    rw [← QRegister.embedUnitary_compose]
    congr 1; apply qreg_ext; intro i
    have hB : (QRegister.block kBE (1 + 42) le_rfl) i = Fin.natAdd kBE i := by ext; simp
    change rCat _ = rMid43InSingleCat mPayload B_tot kWorkConst hB42 i
    rw [hB, QRegister.concat_apply_right]
  have hOpt : ∀ b : Bool, (rMid43InSingleCat mPayload B_tot kWorkConst hB42).embedUnitary
      (optX43 b).eval = optXSingleCat mPayload B_tot kWorkConst b := by
    intro b; cases b
    · simp [optX43, optXSingleCat]
    · have hComp : (rMid43InSingleCat mPayload B_tot kWorkConst hB42).compose
          (QRegister.singleton ⟨0, by decide⟩) =
          QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst) := by
        apply qreg_ext; intro i; fin_cases i
        exact rMid43InSingleCat_zero hB42
      simp only [optX43, optXSingleCat, ↓reduceIte, Circuit.X, Circuit.eval_single,
        ← QRegister.embedUnitary_compose, hComp]
  have hMidTwo : (rMid43InSingleCat mPayload B_tot kWorkConst hB42).embedUnitary
      (uSigMidTwoAngle43 preX postX C_d D_d) = optXSingleCat mPayload B_tot kWorkConst postX *
      (uSignalRotTwoAngleSingleCat hB42 C_d D_d * optXSingleCat mPayload B_tot kWorkConst
      preX) := by
    unfold uSigMidTwoAngle43 uSignalRotTwoAngleSingleCat
    rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, hOpt postX, hOpt preX]
    rfl
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, hGuardEq, hMidEq, hMidTwo]
  unfold uGuardWrapTwoAngleSingleCatGen
  simp only [mul_assoc]
theorem midEmbed_uKickGidney43_comm_guardPolLocalGen (bValid : Fin (2 ^
    SpecsAux.SpecMirror.systemQubits) → Bool) (mPayload : ℕ) (C' : Fin (2 ^ 42)) : midEmbed mPayload
    (1 + 42) (uKickGidney43 C') * guardPolLocalGen
    bValid mPayload (1 + 42) (by decide) true = guardPolLocalGen bValid mPayload (1 +
      42) (by decide) true * midEmbed mPayload (1 + 42) (uKickGidney43 C') := by
  apply Subtype.ext
  let kBE := fullSysBEWires mPayload
  let rMid : QRegister (1 + 42) (kBE + (1 + 42)) := QRegister.block kBE (1 + 42) le_rfl
  let rGuard : QRegister (kBE + 1) (kBE + (1 + 42)) :=
    QRegister.block 0 (kBE + 1) ((Nat.zero_add _).le.trans (Nat.add_le_add_left (by decide) _))
  let rSysLoc : QRegister kBE (kBE + 1) := QRegister.block 0 kBE (by omega)
  let qCtrlLoc : Wire (kBE + 1) := ⟨kBE, by omega⟩
  have hP : ∀ o : Fin (2 ^ 1),
      rGuard.embedMatrix ((QRegister.singleton qCtrlLoc).basisOutcomeProjector o) =
        (rGuard.compose (QRegister.singleton qCtrlLoc)).basisOutcomeProjector o := fun o ↦ by
    rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
      ← QRegister.embedMatrix_compose]
  have hS : rGuard.embedMatrix (rSysLoc.embedMatrix (fullSysGuardReflUnitaryGen mPayload bValid).1)
    =
      (rGuard.compose rSysLoc).embedMatrix (fullSysGuardReflUnitaryGen mPayload bValid).1 :=
    (QRegister.embedMatrix_compose rGuard rSysLoc _).symm
  have hGuardVal : (guardPolLocalGen bValid mPayload (1 + 42) (by decide) true).1 =
      (rGuard.compose (QRegister.singleton qCtrlLoc)).basisOutcomeProjector 0 +
        (rGuard.compose (QRegister.singleton qCtrlLoc)).basisOutcomeProjector 1 *
          (rGuard.compose rSysLoc).embedMatrix (fullSysGuardReflUnitaryGen mPayload bValid).1 := by
    unfold guardPolLocalGen
    rw [ite_true_eq rfl, QRegister.embedUnitary_val]
    change rGuard.embedMatrix ((QRegister.singleton qCtrlLoc).basisOutcomeProjector 0 +
      (QRegister.singleton qCtrlLoc).basisOutcomeProjector 1 * rSysLoc.embedMatrix
      (fullSysGuardReflUnitaryGen mPayload bValid).1) = _
    rw [rGuard.embedMatrix_add, rGuard.embedMatrix_mul, hP 0, hP 1, hS]
  have hMidVal : (midEmbed mPayload (1 + 42) (uKickGidney43 C')).1 =
      rMid.embedMatrix (uKickGidney43 C').1 := rfl
  have hSingEq : rGuard.compose (QRegister.singleton qCtrlLoc) =
      rMid.compose (QRegister.singleton (⟨0, by decide⟩ : Wire (1 + 42))) := by
    apply qreg_ext; intro i; fin_cases i
    ext; simp [rGuard, rMid, qCtrlLoc]
  have hCommProj : ∀ o : Fin (2 ^ 1),
      rMid.embedMatrix (uKickGidney43 C').1 *
          (rGuard.compose (QRegister.singleton qCtrlLoc)).basisOutcomeProjector o =
        (rGuard.compose (QRegister.singleton qCtrlLoc)).basisOutcomeProjector o *
          rMid.embedMatrix (uKickGidney43 C').1 := fun o ↦ by
    rw [hSingEq, QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
      ← QRegister.basisOutcomeProjector, ← rMid.embedMatrix_mul, ← rMid.embedMatrix_mul,
      uKickGidney43_comm_singleton0_proj]
  have hDisjSys : rMid.DisjointWires (rGuard.compose rSysLoc) := by
    rw [QRegister.disjoint_iff]; intro a b hab
    have hv := congrArg Fin.val hab
    have hb := b.isLt
    change kBE + a.val = 0 + (0 + b.val) at hv
    omega
  have hCommSys : rMid.embedMatrix (uKickGidney43 C').1 * (rGuard.compose rSysLoc).embedMatrix
      (fullSysGuardReflUnitaryGen mPayload bValid).1 = (rGuard.compose rSysLoc).embedMatrix
      (fullSysGuardReflUnitaryGen mPayload bValid).1 * rMid.embedMatrix (uKickGidney43 C').1
      := rMid.embedMatrix_comm_of_disjoint (rGuard.compose rSysLoc) hDisjSys _ _
  simp only [Submonoid.coe_mul, hGuardVal, hMidVal]
  rw [Matrix.mul_add, Matrix.add_mul, hCommProj 0, ← Matrix.mul_assoc, hCommProj 1,
    Matrix.mul_assoc, hCommSys, ← Matrix.mul_assoc]
theorem guardPolLocalGen_uSigMidTwoAngle43_eq_rightKick_mul_kick (bValid : Fin (2 ^
    SpecsAux.SpecMirror.systemQubits) → Bool) (mPayload : ℕ) (preX postX : Bool) (C_d D_d : Fin (2 ^
    42)) : guardPolLocalGen bValid
    mPayload (1 + 42) (by decide) true * midEmbed mPayload (1 + 42) (uSigMidTwoAngle43 preX postX
      C_d D_d) * guardPolLocalGen bValid mPayload (1 + 42) (by decide) true = (guardPolLocalGen
      bValid mPayload (1 +
    42) (by decide) true * midEmbed mPayload (1 + 42) (uSigMidRightKick43 preX postX D_d) *
      guardPolLocalGen bValid mPayload (1 + 42) (by decide) true) * midEmbed mPayload (1 +
      42) (uKickGidney43
    (condNegAngle42 preX C_d)) := by
  have hMidMul : midEmbed mPayload (1 + 42) (uSigMidTwoAngle43 preX postX C_d D_d) =
      midEmbed mPayload (1 + 42) (uSigMidRightKick43 preX postX D_d) *
        midEmbed mPayload (1 + 42) (uKickGidney43 (condNegAngle42 preX C_d)) := by
    rw [uSigMidTwoAngle43_eq_rightKick_mul_kick]
    exact QRegister.embedUnitary_mul _ _ _
  apply Subtype.ext
  have hc := congrArg Subtype.val (midEmbed_uKickGidney43_comm_guardPolLocalGen bValid mPayload
    (condNegAngle42 preX C_d))
  simp only [Submonoid.coe_mul] at hc
  simp only [hMidMul, Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hc]
theorem validBEPredBoolGen_77_eq_80_of_ctrl3_zero
    (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool) (β : BitAssignment kActOrig)
    (h0 : ∀ t : Fin 3, β (rUnusedCtrl3Orig t) = 0) : validBEPredBoolGen bValid 77
    (fun i ↦ β (rBE77Orig i)) = validBEPredBoolGen bValid 80 (fun i ↦ β (rBEOrig i)) := by
  have hsys : (fun u : Fin SpecsAux.SpecMirror.systemQubits ↦ β (rBE77Orig (beSysReg 77 u))) =
      (fun u : Fin SpecsAux.SpecMirror.systemQubits ↦ β (rBEOrig (beSysReg 80 u))) := by
    funext u
    have hu : u.val < 3948 := u.isLt
    congr 1; apply Fin.ext
    dsimp [rBE77Orig, rBEOrig, rBEInSingleCat, beSysReg, qreg_block_apply]
    rw [ite_true_eq (by omega)]; omega
  have heq77_80 (j : Fin (fullSysRawAncWires 77)) (j' : Fin (fullSysRawAncWires 80))
      (h : (if j.val < 3 then j.val else j.val + 3) = j'.val) :
      rBE77Orig (beAncReg 77 j) = rBEOrig (beAncReg 80 j') := by
    apply Fin.ext
    have hj := j.isLt
    have hj' := j'.isLt
    dsimp [rBE77Orig, rBEOrig, rBEInSingleCat, beAncReg, qreg_block_apply,
      SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    by_cases h3 : j.val < 3
    · rw [ite_true_eq h3] at h
      rw [ite_true_eq (by omega)]
      omega
    · rw [ite_false_eq h3] at h
      rw [ite_false_eq (by omega)]
      omega
  have hanc : (∀ j : Fin (fullSysRawAncWires 77), β (rBE77Orig (beAncReg 77 j)) = 0) ↔
      (∀ j' : Fin (fullSysRawAncWires 80), β (rBEOrig (beAncReg 80 j')) = 0) := by
    refine ⟨fun h77 j' ↦ ?_, fun h80 j ↦ ?_⟩
    · have hj' : j'.val < 86 := j'.isLt
      by_cases hlt3 : j'.val < 3
      · rw [← heq77_80 ⟨j'.val, by dsimp [fullSysRawAncWires]; omega⟩ j' (by
          dsimp; rw [ite_true_eq hlt3])]
        exact h77 _
      · by_cases hlt6 : j'.val < 6
        · convert h0 ⟨j'.val - 3, by omega⟩ using 2
          apply Fin.ext
          dsimp [rUnusedCtrl3Orig, rBEOrig, rBEInSingleCat, beAncReg, qreg_block_apply,
            SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
            SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
          omega
        · rw [← heq77_80 ⟨j'.val - 3, by dsimp [fullSysRawAncWires]; omega⟩ j' (by
            dsimp; rw [ite_false_eq (by omega)]; omega)]
          exact h77 _
    · have hj : j.val < 83 := j.isLt
      by_cases hlt3 : j.val < 3
      · rw [heq77_80 j ⟨j.val, by dsimp [fullSysRawAncWires]; omega⟩ (by rw [ite_true_eq hlt3])]
        exact h80 _
      · rw [heq77_80 j ⟨j.val + 3, by dsimp [fullSysRawAncWires]; omega⟩ (by
          rw [ite_false_eq hlt3])]
        exact h80 _
  unfold validBEPredBoolGen
  rw [hsys]
  simp only [hanc]
noncomputable def uGuard77TwoAngleLocalGen
    (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool) (bPre bPost : Bool)
    (C_d D_d : Fin (2 ^ 42)) : Unitary (2 ^ (fullSysBEWires 77 + (1 + 42))) :=
    guardPolLocalGen bValid 77 (1 + 42) (by decide) true * midEmbed 77 (1 + 42)
    (uSigMidTwoAngle43 bPre bPost C_d D_d) * guardPolLocalGen bValid 77 (1 + 42) (by decide)
    true
set_option exponentiation.threshold 5000 in
theorem uGuard77TwoAngleOrigGen_mul_pCtrl3ZeroOrig_eq
    (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → Bool)
    (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42)) :
    (rBEMid77Orig.embedUnitary (uGuard77TwoAngleLocalGen bValid bPre bPost C_d D_d)).1 *
        pCtrl3ZeroOrig =
      (uGuardWrapTwoAngleSingleCatGen bValid (mPayload := 80) (kWorkConst := 40)
        (by decide : 42 ≤ 48) bPre bPost C_d D_d).1 * pCtrl3ZeroOrig := by
  unfold uGuard77TwoAngleLocalGen
  rw [← embedUnitary_twoAngleGuardWrap_singleCat_gen bValid (mPayload := 80) (kWorkConst := 40)
    (by decide : 42 ≤ 48) bPre bPost C_d D_d]
  apply matrix_ext_basisKet
  intro β
  simp only [pCtrl3ZeroOrig, ← Matrix.mulVec_mulVec,
    register_basisOutcomeProjector_zero_mulVec_basisKet]
  split_ifs with h0
  · rw [guardWrapTargetUnitary_mulVec_basisKet_gen bValid 77 (1 + 42) (by decide) true true
        rBE77Orig rMid43Orig rBE77Orig_disj_rMid43Orig (uSigMidTwoAngle43 bPre bPost C_d D_d) β,
      embed_muxFlagUnitary_mulVec_basisKet,
      guardWrapTargetUnitary_mulVec_basisKet_gen bValid 80 (1 + 42) (by decide) true true
        rBEOrig rMid43Orig _ (uSigMidTwoAngle43 bPre bPost C_d D_d) β,
      embed_muxFlagUnitary_mulVec_basisKet,
      validBEPredBoolGen_77_eq_80_of_ctrl3_zero bValid β h0]
  · simp
theorem embedUnitary_rBEMid77EffFull_eq_gen (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) →
    Bool) (k_idle : ℕ) (hk : k_idle ≤ 48) (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42)) (hC : 2 ^
    (k_idle - 6) ∣ C_d.val)
    (hD : 2 ^ (k_idle - 6) ∣ D_d.val) : (rBEMid77EffFull k_idle hk).embedUnitary
      (uGuard77TwoAngleLocalGen bValid bPre bPost C_d D_d) = rAct0.embedUnitary
      (rBEMid77Orig.embedUnitary (uGuard77TwoAngleLocalGen
    bValid bPre bPost C_d D_d)) := by
  have hCatEq : rBEMid77Full = rAct0.compose rBEMid77Orig :=
    compose_concat_eq_singleCat rAct0 rBE77Orig rMid43Orig rBE77Orig_disj_rMid43Orig
  rw [← QRegister.embedUnitary_compose, ← hCatEq]
  unfold uGuard77TwoAngleLocalGen
  have hGuardEq : (rBEMid77EffFull k_idle hk).embedUnitary
        (guardPolLocalGen bValid 77 (1 + 42) (by decide) true) =
      rBEMid77Full.embedUnitary (guardPolLocalGen bValid 77 (1 + 42) (by decide) true) := by
    unfold guardPolLocalGen
    simp only [↓reduceIte, ← QRegister.embedUnitary_compose]
    congr 1; apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · have hL : (QRegister.block 0 (fullSysBEWires 77 + 1)
          ((Nat.zero_add _).le.trans (Nat.add_le_add_left (by decide : 1 ≤ 1 + 42) _)))
          (Fin.castAdd 1 i) = Fin.castAdd (1 + 42) i := by ext; simp
      simp only [QRegister.compose_apply, hL, rBEMid77EffFull, rBEMid77Full,
        QRegister.concat_apply_left]
    · fin_cases j
      have hR : (QRegister.block 0 (fullSysBEWires 77 + 1)
          ((Nat.zero_add _).le.trans (Nat.add_le_add_left (by decide : 1 ≤ 1 + 42) _)))
          (Fin.natAdd (fullSysBEWires 77) ⟨0, by decide⟩) =
          Fin.natAdd (fullSysBEWires 77) ⟨0, by decide⟩ := by ext; simp
      simp only [QRegister.compose_apply, hR, rBEMid77EffFull, rBEMid77Full,
        QRegister.concat_apply_right]
      apply Fin.ext
      rw [rMid43EffFull_val_eq, ite_true_eq rfl]
      change 4034 = (rAct0 (rMid43Orig ⟨0, by decide⟩)).val
      rw [rAct0_val_eq, rMid43Orig_zero_val]
  have hMidEq : (rBEMid77EffFull k_idle hk).embedUnitary
        (midEmbed 77 (1 + 42) (uSigMidTwoAngle43 bPre bPost C_d D_d)) =
      rBEMid77Full.embedUnitary
        (midEmbed 77 (1 + 42) (uSigMidTwoAngle43 bPre bPost C_d D_d)) := by
    have hCompEff : (rBEMid77EffFull k_idle hk).compose
        (QRegister.block (fullSysBEWires 77) (1 + 42) le_rfl) = rMid43EffFull k_idle hk := by
      apply qreg_ext; intro j
      have hB : QRegister.block (fullSysBEWires 77) (1 + 42) le_rfl j =
          Fin.natAdd (fullSysBEWires 77) j := by ext; simp
      change rBEMid77EffFull k_idle hk _ = _
      rw [hB, rBEMid77EffFull, QRegister.concat_apply_right]
    have hCompStd : rBEMid77Full.compose
        (QRegister.block (fullSysBEWires 77) (1 + 42) le_rfl) = rMid43Full := by
      apply qreg_ext; intro j
      have hB : QRegister.block (fullSysBEWires 77) (1 + 42) le_rfl j =
          Fin.natAdd (fullSysBEWires 77) j := by ext; simp
      change rBEMid77Full _ = _
      rw [hB, rBEMid77Full, QRegister.concat_apply_right]
    unfold midEmbed
    rw[← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose, hCompEff, hCompStd,
      embedUnitary_rMid43EffFull_uSigMidTwoAngle43_eq k_idle hk bPre bPost C_d D_d hC hD]
  simp only [QRegister.embedUnitary_mul, hGuardEq, hMidEq]
set_option exponentiation.threshold 5000 in
theorem uBEMid77EffFull_mul_E_segExt_eq_gen (bValid : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) →
    Bool) (k_idle : ℕ) (hk : k_idle ≤ 48) (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42)) (hC : 2 ^
    (k_idle - 6) ∣ C_d.val)
    (hD : 2 ^ (k_idle - 6) ∣ D_d.val) : ((rBEMid77EffFull k_idle hk).embedUnitary
      (uGuard77TwoAngleLocalGen bValid bPre bPost C_d D_d)).1 * E_segExt k_idle hk =
      (rAct0.embedUnitary
    (uGuardWrapTwoAngleSingleCatGen bValid (by decide : 42 ≤ 48) bPre bPost C_d D_d)).1 *
      E_segExt k_idle hk := by
  have hFactor : E_segExt k_idle hk =
      pCtrl3Zero * (E_stream42 * (pSlack3Zero * pPGIdleZero k_idle hk)) := by
    unfold E_segExt
    rw [pExt6IdleZero_eq_mul, pExt6Zero_eq_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      E_stream42_comm_pCtrl3Zero, Matrix.mul_assoc, Matrix.mul_assoc]
  have hOrig : (rAct0.embedUnitary (rBEMid77Orig.embedUnitary (uGuard77TwoAngleLocalGen bValid
      bPre bPost C_d D_d))).1 * pCtrl3Zero = (rAct0.embedUnitary
      (uGuardWrapTwoAngleSingleCatGen bValid (by decide : 42 ≤ 48) bPre bPost C_d D_d)).1 *
      pCtrl3Zero := by
    rw [← embedAct0_pCtrl3ZeroOrig, QRegister.embedUnitary_val rAct0 (rBEMid77Orig.embedUnitary _),
      QRegister.embedUnitary_val rAct0 (uGuardWrapTwoAngleSingleCatGen _ _ _ _ _ _),
      ← QRegister.embedMatrix_mul, ←
        QRegister.embedMatrix_mul, uGuard77TwoAngleOrigGen_mul_pCtrl3ZeroOrig_eq bValid bPre bPost
          C_d D_d]
  rw [embedUnitary_rBEMid77EffFull_eq_gen bValid k_idle hk bPre bPost C_d D_d hC hD, hFactor,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hOrig]
  simp only [Matrix.mul_assoc]
theorem dSigMidRightKickGidney43Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (preX postX : Bool) (D_d : Fin (2 ^ 42)) (rMid43 : QRegister (1 +
    42) n) (rCarryD :
    QRegister (activeMsbWidth42 D_d.val - 2) n) (hDisjD : rMid43.DisjointWires rCarryD) :
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rMid43 rCarryD (uSigMidRightKick43
      preX postX D_d)
    (dSigMidRightKickGidney43Dyn v preX postX D_d rMid43 rCarryD hDisjD) := by
  obtain ⟨hwp, _, hproj⟩ :=
    cSigMidRightKickGidney43Ref_props (Var := Var) v preX postX D_d rMid43 rCarryD hDisjD
  exact GridGuard654ReflAux.realizesEmbeddedUnitary_of_wp_eq_and_mul_proj rMid43 rCarryD
    (uSigMidRightKick43 preX postX D_d)
    (dSigMidRightKickGidney43Dyn v preX postX D_d rMid43 rCarryD hDisjD)
    (cSigMidRightKickGidney43Ref preX postX D_d rMid43 rCarryD hDisjD)
    (storeConst_dSigMidRightKickGidney43Dyn v preX postX D_d rMid43 rCarryD hDisjD)
    (fun M ↦ hwp (fun _ ↦ M) (fun _ _ ↦ rfl)) hproj
theorem le_trailingZeros42Aux_of_two_pow_dvd :
    ∀ (fuel k c : ℕ), k ≤ fuel → 2 ^ k ∣ c → k ≤ trailingZeros42Aux fuel c
  | 0, k, _, hk, _ => by omega
  | fuel + 1, 0, _, _, _ => Nat.zero_le _
  | fuel + 1, k + 1, c, hk, hdvd => by
      unfold trailingZeros42Aux
      split_ifs with h0 hmod
      · omega
      · rcases hdvd with ⟨q, rfl⟩
        have hdiv : (2 ^ (k + 1) * q) / 2 = 2 ^ k * q := by
          rw [Nat.pow_succ', mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
        rw [hdiv]
        have hih := le_trailingZeros42Aux_of_two_pow_dvd fuel k (2 ^ k * q) (by omega) ⟨q, rfl⟩
        omega
      · exfalso
        rcases hdvd with ⟨q, rfl⟩
        rw [Nat.pow_succ', mul_assoc, Nat.mul_mod_right] at hmod
        exact hmod rfl
theorem activeMsbWidth42_sub_two_le_of_two_pow_dvd {k c : ℕ} (hk : k ≤ 42) (hdvd : 2 ^ k ∣ c) :
    activeMsbWidth42 c - 2 ≤ 40 - k := by
  have htz : k ≤ trailingZeros42 c := le_trailingZeros42Aux_of_two_pow_dvd 42 k c hk hdvd
  unfold activeMsbWidth42
  omega
-- ============================================================================
-- Section 2: Syndrome Guard Engine (`23,736 + 4 * mPayload - 16 * p_held + dMid.count .T`,
-- `0 TOFF`)
-- ============================================================================
/-- Multiplexed unitary on `K` wires: applies `u₁` on `rSub` when `pred β = true` and `u₀` when
`pred β = false`, provided `pred` depends only on wires outside `rSub.image`. -/
noncomputable def muxSubUnitary {K kSub : ℕ} (rSub : QRegister kSub K)
    (pred : BitAssignment K → Bool) (hIndep : ∀ β₁ β₂ : BitAssignment K, (∀ w, w ∉ rSub.image
    → β₁ w = β₂ w) → pred β₁ = pred β₂) (u₀ u₁ : Unitary (2 ^ kSub)) : Unitary (2 ^ K) :=
  let p₀ : Fin (2 ^ K) → Bool := fun x ↦ !(pred (basisBits K x))
  let p₁ : Fin (2 ^ K) → Bool := fun x ↦ pred (basisBits K x)
  let P₀ := diagProj K p₀
  let P₁ := diagProj K p₁
  let M : Operator (2 ^ K) := rSub.embedMatrix u₀.1 * P₀ + rSub.embedMatrix u₁.1 * P₁
  ⟨M, by
    have hpred_eq : ∀ x y : Fin (2 ^ K), rSub.AgreeOutside x y → pred (basisBits K x) = pred
        (basisBits K y) := fun x y hout ↦ hIndep _ _ fun w hw ↦ hout w fun ⟨idx, hidx⟩ ↦ hw
        ((QRegister.mem_image rSub w).mpr ⟨idx, hidx⟩)
    have hcomm : ∀ (B : Operator (2 ^ kSub)) (p : Fin (2 ^ K) → Bool),
        (∀ x y : Fin (2 ^ K), rSub.AgreeOutside x y → p x = p y) →
        rSub.embedMatrix B * diagProj K p = diagProj K p * rSub.embedMatrix B := by
      intro B p hp
      ext i j
      unfold diagProj
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, QRegister.embedMatrix_apply]
      by_cases henv : (rSub.basisSplitEquiv i).2 = (rSub.basisSplitEquiv j).2
      · rw [hp i j ((rSub.basisSplit_environment_eq_iff i j).mp henv), mul_comm]
      · simp [henv]
    have hcomm₀ : ∀ B : Operator (2 ^ kSub), rSub.embedMatrix B * P₀ = P₀ * rSub.embedMatrix B :=
      fun B ↦ hcomm B p₀ fun x y h ↦ by dsimp [p₀]; rw [hpred_eq x y h]
    have hcomm₁ : ∀ B : Operator (2 ^ kSub), rSub.embedMatrix B * P₁ = P₁ * rSub.embedMatrix B :=
      fun B ↦ hcomm B p₁ hpred_eq
    have hP₀_herm : P₀ᴴ = P₀ := (diagProj_isHermitian K p₀).eq
    have hP₁_herm : P₁ᴴ = P₁ := (diagProj_isHermitian K p₁).eq
    have hP₀_idem : P₀ * P₀ = P₀ := diagProj_idem K p₀
    have hP₁_idem : P₁ * P₁ = P₁ := diagProj_idem K p₁
    have hP₀₁ : P₀ * P₁ = 0 := by
      dsimp only [P₀, P₁, diagProj]
      rw [Matrix.diagonal_mul_diagonal]
      ext x y
      by_cases hxy : x = y
      · subst hxy
        cases pred (basisBits K x) <;> simp [p₀, p₁]
      · simp [hxy]
    have hP₁₀ : P₁ * P₀ = 0 := by
      rw [← hP₁_herm, ← hP₀_herm, ← conjTranspose_mul, hP₀₁, conjTranspose_zero]
    have hsum : P₀ + P₁ = 1 := by
      dsimp only [P₀, P₁, diagProj]
      ext x y
      by_cases hxy : x = y
      · subst hxy
        dsimp only [p₀, p₁]
        by_cases hp : pred (basisBits K x) = true <;> simp [Matrix.diagonal, hp]
      · simp [hxy]
    have hunit_L (u : Unitary (2 ^ kSub)) : (rSub.embedMatrix u.1)ᴴ * rSub.embedMatrix u.1 = 1 := by
      rw [← QRegister.embedMatrix_conjTranspose, ← rSub.embedMatrix_mul,
        show u.1ᴴ * u.1 = 1 by
          simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
          Unitary.coe_star_mul_self u,
        rSub.embedMatrix_one]
    have hunit_R (u : Unitary (2 ^ kSub)) : rSub.embedMatrix u.1 * (rSub.embedMatrix u.1)ᴴ = 1 := by
      rw [← QRegister.embedMatrix_conjTranspose, ← rSub.embedMatrix_mul,
        show u.1 * u.1ᴴ = 1 by
          simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
          Unitary.coe_mul_star_self u,
        rSub.embedMatrix_one]
    have hc₀_adj : (rSub.embedMatrix u₀.1)ᴴ * P₀ = P₀ * (rSub.embedMatrix u₀.1)ᴴ := by
      rw [← QRegister.embedMatrix_conjTranspose]
      exact hcomm₀ _
    have hc₁_adj : (rSub.embedMatrix u₁.1)ᴴ * P₁ = P₁ * (rSub.embedMatrix u₁.1)ᴴ := by
      rw [← QRegister.embedMatrix_conjTranspose]
      exact hcomm₁ _
    have hz_cross {A B Q R : Operator (2 ^ K)} (hAQ : A * Q = Q * A) (hBR : B * R = R * B) (hQR : Q
      * R = 0) :
        Q * A * (B * R) = 0 := by
      rw [← hAQ, hBR, Matrix.mul_assoc A Q, ← Matrix.mul_assoc Q R B, hQR, Matrix.zero_mul,
        Matrix.mul_zero]
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    dsimp only [M]
    rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hP₀_herm, hP₁_herm]
    constructor
    · calc
        (P₀ * (rSub.embedMatrix u₀.1)ᴴ + P₁ * (rSub.embedMatrix u₁.1)ᴴ) *
            (rSub.embedMatrix u₀.1 * P₀ + rSub.embedMatrix u₁.1 * P₁)
            = P₀ * ((rSub.embedMatrix u₀.1)ᴴ * rSub.embedMatrix u₀.1) * P₀ +
                P₀ * (rSub.embedMatrix u₀.1)ᴴ * (rSub.embedMatrix u₁.1 * P₁) +
                P₁ * (rSub.embedMatrix u₁.1)ᴴ * (rSub.embedMatrix u₀.1 * P₀) +
                P₁ * ((rSub.embedMatrix u₁.1)ᴴ * rSub.embedMatrix u₁.1) * P₁ := by noncomm_ring
        _ = P₀ + P₁ := by
              rw [hunit_L u₀, hunit_L u₁, Matrix.mul_one, Matrix.mul_one, hP₀_idem, hP₁_idem,
                hz_cross hc₀_adj (hcomm₁ u₁.1) hP₀₁, hz_cross hc₁_adj (hcomm₀ u₀.1) hP₁₀]
              abel
        _ = 1 := hsum
    · calc
        (rSub.embedMatrix u₀.1 * P₀ + rSub.embedMatrix u₁.1 * P₁) *
            (P₀ * (rSub.embedMatrix u₀.1)ᴴ + P₁ * (rSub.embedMatrix u₁.1)ᴴ)
            = rSub.embedMatrix u₀.1 * (P₀ * P₀) * (rSub.embedMatrix u₀.1)ᴴ +
                rSub.embedMatrix u₀.1 * (P₀ * P₁) * (rSub.embedMatrix u₁.1)ᴴ +
                rSub.embedMatrix u₁.1 * (P₁ * P₀) * (rSub.embedMatrix u₀.1)ᴴ +
                rSub.embedMatrix u₁.1 * (P₁ * P₁) * (rSub.embedMatrix u₁.1)ᴴ := by noncomm_ring
        _ = P₀ + P₁ := by
              rw [hP₀_idem, hP₁_idem, hP₀₁, hP₁₀, hcomm₀ u₀.1, hcomm₁ u₁.1]
              have h0 : P₀ * rSub.embedMatrix u₀.1 * (rSub.embedMatrix u₀.1)ᴴ = P₀ := by
                rw [Matrix.mul_assoc, hunit_R u₀, Matrix.mul_one]
              have h1 : P₁ * rSub.embedMatrix u₁.1 * (rSub.embedMatrix u₁.1)ᴴ = P₁ := by
                rw [Matrix.mul_assoc, hunit_R u₁, Matrix.mul_one]
              simp only [Matrix.mul_zero, Matrix.zero_mul]
              rw [h0, h1]
              abel
        _ = 1 := hsum⟩
theorem embedMatrix_diagProj_mulVec_basisKet {n K : ℕ}
    (rBig : QRegister K n) (p : Fin (2 ^ K) → Bool) (β : BitAssignment n) :
    (rBig.embedMatrix (diagProj K p)).mulVec (basisKet β) =
      if p (rBig.extractIndex ((basisBitsEquiv n).symm β)) then basisKet β else 0 := by
  let g := (basisBitsEquiv n).symm β
  change (rBig.embedMatrix (diagProj K p)).mulVec (Pi.single g 1) =
    if p (rBig.extractIndex g) then Pi.single g 1 else 0
  funext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, QRegister.embedMatrix_apply]
  unfold diagProj
  by_cases hig : i = g
  · subst hig; by_cases hp : p (rBig.extractIndex g) = true <;> simp [Matrix.diagonal, hp]
  · have hRHS : (if p (rBig.extractIndex g) then (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ) else 0) i =
      0 := by
      cases p (rBig.extractIndex g) <;> simp [hig]
    rw [hRHS]
    by_cases henv : (rBig.basisSplitEquiv i).2 = (rBig.basisSplitEquiv g).2
    · have hex : rBig.extractIndex i ≠ rBig.extractIndex g := fun heq ↦
        hig (rBig.basisSplitEquiv.injective
          (Prod.ext (by simpa [QRegister.basisSplitEquiv_apply_fst] using heq) henv))
      simp [henv, Matrix.diagonal, hex]
    · simp [henv]
theorem embed_muxSubUnitary_mulVec_basisKet {n K kSub : ℕ} (rBig : QRegister K n)
    (sel : QRegister kSub K) (pred : BitAssignment K → Bool) (hIndep : ∀ β₁ β₂ : BitAssignment
    K, (∀ w, w ∉ sel.image → β₁ w = β₂ w) → pred β₁ = pred β₂) (u₀ u₁ : Unitary (2 ^ kSub))
    (β : BitAssignment n) : (rBig.embedUnitary (muxSubUnitary sel pred hIndep u₀ u₁)).1.mulVec
    (basisKet β) = ((rBig.compose sel).embedUnitary (if pred (fun idx ↦ β (rBig idx)) then u₁
    else u₀)).1.mulVec (basisKet β) := by
  let g := (basisBitsEquiv n).symm β
  have hbits : basisBits K (rBig.extractIndex g) = fun idx ↦ β (rBig idx) := by
    funext idx; rw [rBig.basisBits_extractIndex, basisBits_basisBitsEquiv_symm_eq]
  have hcomp : ∀ u : Unitary (2 ^ kSub),
      rBig.embedMatrix (sel.embedMatrix u.1) = ((rBig.compose sel).embedUnitary u).1 := by
    intro u
    simpa only [QRegister.embedUnitary_val] using
      (congrArg Subtype.val (QRegister.embedUnitary_compose rBig sel u)).symm
  change (rBig.embedMatrix
      (sel.embedMatrix u₀.1 * diagProj K (fun x ↦ !(pred (basisBits K x))) +
        sel.embedMatrix u₁.1 * diagProj K (fun x ↦ pred (basisBits K x)))).mulVec (basisKet β) = _
  rw[rBig.embedMatrix_add, rBig.embedMatrix_mul, rBig.embedMatrix_mul, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, embedMatrix_diagProj_mulVec_basisKet,
      embedMatrix_diagProj_mulVec_basisKet, hcomp u₀, hcomp u₁]
  rw [hbits]
  cases pred (fun idx ↦ β (rBig idx)) <;> simp [Matrix.mulVec_zero]
def beWireInDHMidGuard (mPayload kMid p_held : ℕ) (i : Fin (fullSysBEWires mPayload)) :
    Wire ((fullSysBEWires mPayload + kMid) + 4 * p_held) :=
  Fin.castAdd (4 * p_held) (Fin.castAdd kMid i)
def selMidInDHMidGuard (mPayload kMid p_held : ℕ) :
    QRegister kMid ((fullSysBEWires mPayload + kMid) + 4 * p_held) :=
  QRegister.block (fullSysBEWires mPayload) kMid (by omega)
theorem effElecBadOnData_indep_mid (mPayload kMid p_held : ℕ) (δ₁ δ₂ : BitAssignment
    ((fullSysBEWires mPayload + kMid) + 4 * p_held)) (h : ∀ w, w ∉ (selMidInDHMidGuard mPayload kMid
    p_held).image → δ₁ w = δ₂ w) (f
    : Fin 654) : effElecBadOnData mPayload kMid p_held ((basisBitsEquiv ((fullSysBEWires mPayload +
      kMid) + 4 * p_held)).symm δ₁) f = effElecBadOnData mPayload kMid p_held ((basisBitsEquiv
      ((fullSysBEWires
    mPayload + kMid) + 4 * p_held)).symm δ₂) f := by
  have hnot_be : ∀ i : Fin (fullSysBEWires mPayload),
      (QRegister.block 0 (fullSysBEWires mPayload)
        (by
          omega : 0 + fullSysBEWires mPayload ≤ (fullSysBEWires mPayload + kMid) + 4 * p_held) i) ∉
        (selMidInDHMidGuard mPayload kMid p_held).image := by
    intro i hm
    rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    simp only [selMidInDHMidGuard, qreg_block_apply] at hv
    have := i.isLt; omega
  have hnot_held : ∀ t : Fin (4 * p_held), (QRegister.block (fullSysBEWires mPayload + kMid)
      (4 * p_held) le_rfl t) ∉ (selMidInDHMidGuard mPayload kMid p_held).image := by
    intro t hm
    rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    simp only [selMidInDHMidGuard, qreg_block_apply] at hv
    have := j.isLt; omega
  unfold effElecBadOnData
  dsimp only
  rw [basisBits_basisBitsEquiv_symm_eq, basisBits_basisBitsEquiv_symm_eq]
  split_ifs with hf
  · rw [h _ (hnot_held _), h _ (hnot_be _)]
  · congr 1; funext u; exact h _ (hnot_be _)
end
end Config
end MidGuardGuard24000
end
end MidGuardGuard24000

end QuantumComputation.Specs.StoppingPowerSolution
end
