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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DyadicQft64Walk

@[expose] public section
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModDyadicQft64WalkCircuit288
@[expose] public section
namespace DyadicQft64WalkCircuit288Alt
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
end DyadicQft64WalkCircuit288Alt
namespace DyadicQft64WalkCircuit288
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux
open DyadicQft64Engine DyadicQft64
open DyadicQft64WalkCircuit
open FullSysCatSegmentBridge
open scoped Matrix BigOperators
section ConfigDyadicQft64WalkCircuit288
set_option maxRecDepth 65536
instance (priority := 1000000) instNeZeroTwoPowQft288 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
abbrev nCanon4222 : ℕ := (3924 + 3 + 7) + 288
def rQftCanon288 : QRegister (3924 + 3 + 7) nCanon4222 :=
  QRegister.block 0 (3924 + 3 + 7) (by decide)
def rWorkCanon288 : QRegister 288 nCanon4222 := QRegister.block (3924 + 3 + 7) 288 (by decide)
theorem rQftCanon288_disjoint_rWorkCanon288 : rQftCanon288.DisjointWires rWorkCanon288 :=
  disjoint_block_sep (by decide)
def rSysCanon288 : QRegister (3924 + 3) nCanon4222 := rQftCanon288.compose rIdInCat
def rPGCanon288 : QRegister 7 nCanon4222 := rQftCanon288.compose rPGInCat
theorem rSysCanon288_disjoint_rPGCanon288 : rSysCanon288.DisjointWires rPGCanon288 :=
  rIdOfCat_disjoint_rPGOfCat rQftCanon288
theorem rSysCanon288_disjoint_rWorkCanon288 : rSysCanon288.DisjointWires rWorkCanon288 :=
  rQftCanon288_disjoint_rWorkCanon288.compose_left _
theorem rPGCanon288_disjoint_rWorkCanon288 : rPGCanon288.DisjointWires rWorkCanon288 :=
  rQftCanon288_disjoint_rWorkCanon288.compose_left _
def embCanon4102In4222 : QRegister nCanon4102 nCanon4222 :=
  QRegister.block 0 nCanon4102 (by decide)
theorem embCanon4102_compose_rQft : embCanon4102In4222.compose rQftCanon = rQftCanon288 := by
  apply DyadicQft64WalkCircuit288Alt.qreg_ext; intro i; apply Fin.ext
  simp [embCanon4102In4222, rQftCanon, rQftCanon288,
    DyadicQft64WalkCircuit288Alt.qreg_block_apply]
theorem embCanon4102_compose_rWork :
    embCanon4102In4222.compose rWorkCanon = rWorkCanon288.slice 0 168 (by decide) := by
  apply DyadicQft64WalkCircuit288Alt.qreg_ext; intro j; apply Fin.ext
  simp [embCanon4102In4222, rWorkCanon, rWorkCanon288,
    DyadicQft64WalkCircuit288Alt.qreg_block_apply]
structure CanonStageSpec288 where
  uCat : Unitary (2 ^ (3924 + 3 + 7))
  uEff : Unitary (2 ^ (3924 + 3))
  tCost : ℕ
  dFwd : DynamicCircuit Unit nCanon4222
  dInv : DynamicCircuit Unit nCanon4222
  hToffFwd : dFwd.count .TOFF = 0
  hToffInv : dInv.count .TOFF = 0
  hTFwd : dFwd.count .T = tCost
  hTInv : dInv.count .T = tCost
  hRealFwd : RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon288 rWorkCanon288 uCat dFwd
  hRealInv : RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon288 rWorkCanon288 uCat⁻¹ dInv
  hIntertwines : ∀ {N : ℕ} [NeZero (2 ^ N)]
    (rId : QRegister (3924 + 3) N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG)
    (U_cat7 : Unitary (2 ^ 7)),
    U_cat7.1.mulVec (Pi.single 0 1) = DyadicQft64.phaseGradKet 7 →
    DyadicQft64.IntertwinesCatOp
      (rPG.embedUnitary U_cat7).1
      (rPG.basisOutcomeProjector 0)
      ((rId.concat rPG hdisj).embedUnitary uCat).1
      (rId.embedUnitary uEff).1
noncomputable def CanonStageSpec288.ofCanon168 (S : CanonStageSpec) : CanonStageSpec288 where
  uCat := S.uCat
  uEff := S.uEff
  tCost := S.tCost
  dFwd := liftDynamic () embCanon4102In4222 S.dFwd
  dInv := liftDynamic () embCanon4102In4222 S.dInv
  hToffFwd := (count_liftDynamic .TOFF () embCanon4102In4222 S.dFwd).trans S.hToffFwd
  hToffInv := (count_liftDynamic .TOFF () embCanon4102In4222 S.dInv).trans S.hToffInv
  hTFwd := (count_liftDynamic .T () embCanon4102In4222 S.dFwd).trans S.hTFwd
  hTInv := (count_liftDynamic .T () embCanon4102In4222 S.dInv).trans S.hTInv
  hRealFwd :=
    realizes_congr_slice2 (by decide : 168 ≤ 288)
      embCanon4102_compose_rQft embCanon4102_compose_rWork
      (realizes_liftDynamic () embCanon4102In4222 rQftCanon rWorkCanon S.uCat S.dFwd S.hRealFwd)
  hRealInv :=
    realizes_congr_slice2 (by decide : 168 ≤ 288)
      embCanon4102_compose_rQft embCanon4102_compose_rWork
      (realizes_liftDynamic () embCanon4102In4222 rQftCanon rWorkCanon S.uCat⁻¹ S.dInv S.hRealInv)
  hIntertwines := S.hIntertwines
noncomputable def CanonStageSpec288.seq (S₁ S₂ : CanonStageSpec288) : CanonStageSpec288 where
  uCat := S₂.uCat * S₁.uCat
  uEff := S₂.uEff * S₁.uEff
  tCost := S₁.tCost + S₂.tCost
  dFwd := .seq S₁.dFwd S₂.dFwd
  dInv := .seq S₂.dInv S₁.dInv
  hToffFwd := by simp [S₁.hToffFwd, S₂.hToffFwd]
  hToffInv := by simp [S₂.hToffInv, S₁.hToffInv]
  hTFwd := by simp [S₁.hTFwd, S₂.hTFwd]
  hTInv := by simp only [DynamicCircuit.count, S₂.hTInv, S₁.hTInv, Nat.add_comm]
  hRealFwd := S₁.hRealFwd.seq rQftCanon288_disjoint_rWorkCanon288 S₂.hRealFwd
  hRealInv := by
    rw [_root_.mul_inv_rev]
    exact S₂.hRealInv.seq rQftCanon288_disjoint_rWorkCanon288 S₁.hRealInv
  hIntertwines rId rPG hdisj U_cat7 hcol0 := by
    rw [(rId.concat rPG hdisj).embedUnitary_mul, rId.embedUnitary_mul,
      Submonoid.coe_mul, Submonoid.coe_mul]
    exact (S₂.hIntertwines rId rPG hdisj U_cat7 hcol0).mul
      (S₁.hIntertwines rId rPG hdisj U_cat7 hcol0)
noncomputable def CanonStageSpec288.congr (S : CanonStageSpec288)
    {uEff' : Unitary (2 ^ (3924 + 3))} {tCost' : ℕ}
    (hu : S.uEff = uEff') (ht : S.tCost = tCost') : CanonStageSpec288 where
  uCat := S.uCat
  uEff := uEff'
  tCost := tCost'
  dFwd := S.dFwd
  dInv := S.dInv
  hToffFwd := S.hToffFwd
  hToffInv := S.hToffInv
  hTFwd := S.hTFwd.trans ht
  hTInv := S.hTInv.trans ht
  hRealFwd := S.hRealFwd
  hRealInv := S.hRealInv
  hIntertwines rId rPG hdisj U_cat7 hcol0 := by
    rw [← hu]
    exact S.hIntertwines rId rPG hdisj U_cat7 hcol0
noncomputable def CanonStageSpec288.id : CanonStageSpec288 :=
  CanonStageSpec288.ofCanon168 CanonStageSpec.id
section ApexButterflyEngine
open HermitianMat
open scoped Circuit.Notation
variable {Var : Type} {n : ℕ}
lemma zmod2_full_adder_val_local (a b c : ZMod 2) :
    (a + b + c).val + 2 * (c + (a + c) * (b + c)).val = a.val + b.val + c.val := by
  revert a b c; decide
theorem toffoli_conj_preserves_zero_ancilla_of_phasePerm {M : Finset (Wire n)}
    (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (c_body : Circuit n) (φ_body : BitAssignment n → ℂ)
    (f_body : BitAssignment n → BitAssignment n) (hperm : PhasePerm M c_body φ_body f_body)
    (hc₁ : ∀ β, f_body β c₁ = β c₁) (hc₂ : ∀ β, f_body β c₂ = β c₂)
    (hanc : ∀ β, f_body β anc = β anc) :
    let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1
    P₀ * (T_anc * c_body.eval.1 * T_anc * P₀) = T_anc * c_body.eval.1 * T_anc * P₀ := by
  intro P₀ T_anc
  apply matrix_ext_basisKet
  intro β
  dsimp only [P₀, T_anc]
  simp only [← Matrix.mulVec_mulVec, basisOutcomeProjector_zero_mulVec_basisKet]
  by_cases hβ : β anc = 0
  · simp only [hβ, ↓reduceIte, evolve_TOFF_basisKet, zero_add]
    let β₁ := Function.update β anc (β c₁ * β c₂)
    rw [hperm.evolve β₁]
    simp only [Matrix.mulVec_smul, evolve_TOFF_basisKet, basisOutcomeProjector_zero_mulVec_basisKet]
    have hzero : f_body β₁ anc + f_body β₁ c₁ * f_body β₁ c₂ = 0 := by
      rw [hanc β₁, hc₁ β₁, hc₂ β₁]
      dsimp only [β₁]
      rw [Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
        CharTwo.add_self_eq_zero]
    simp [hzero]
  · simp [hβ]
abbrev gidneyApexStep0 {m : ℕ} (uWires : Fin (m + 1) → Wire n)
    (rT rC : QRegister (m + 1) n) (c_in : Wire n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) : TempAndStep n :=
  gidneyRippleStep (uWires 0) (rT 0) c_in (rC 0)
    (QRegister.ne_apply_of_not_mem_image rT _ (hu_T 0) 0)
    (QRegister.ne_apply_of_not_mem_image rC _ (hu_C 0) 0)
    (hdisj_TC.ne 0 0) (hcin_u 0)
    (QRegister.ne_apply_of_not_mem_image rT _ hcin_T 0)
    (QRegister.ne_apply_of_not_mem_image rC _ hcin_C 0)
def gidneyApexChainCircuit (isInv : Bool) :
    (w : ℕ) → (uWires : Fin w → Wire n) → (rT : QRegister w n) → (rC : QRegister w n) →
    (c_in : Wire n) → (∀ j, uWires j ∉ rT.image) → (∀ j, uWires j ∉ rC.image) →
    rT.DisjointWires rC → (∀ j, c_in ≠ uWires j) → c_in ∉ rT.image → c_in ∉ rC.image →
    Circuit n
  | 0, _, _, _, c_in, _, _, _, _, _, _ =>
      if isInv then (Circuit.T c_in).inverse else Circuit.T c_in
  | m + 1, uWires, rT, rC, c_in, hu_T, hu_C, hdisj_TC, hcin_u, hcin_T, hcin_C =>
      (gidneyApexStep0 uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).wrapCircuit
        (gidneyApexChainCircuit isInv m (fun j ↦ uWires j.succ)
          (rT.slice 1 m (by omega)) (rC.slice 1 m (by omega)) (rC 0)
          (fun j hj ↦ hu_T j.succ (QRegister.image_compose_subset rT _ hj))
          (fun j hj ↦ hu_C j.succ (QRegister.image_compose_subset rC _ hj))
          ((hdisj_TC.compose_left _).compose_right _)
          (fun j h ↦ hu_C j.succ ((QRegister.mem_image rC _).mpr ⟨0, h⟩))
          (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj))
          (QRegExt.head_not_mem_tail_image rC))
def gidneyApexChainDyn (v : Var) (isInv : Bool) :
    (w : ℕ) → (uWires : Fin w → Wire n) → (rT : QRegister w n) → (rC : QRegister w n) →
    (c_in : Wire n) → (∀ j, uWires j ∉ rT.image) → (∀ j, uWires j ∉ rC.image) →
    rT.DisjointWires rC → (∀ j, c_in ≠ uWires j) → c_in ∉ rT.image → c_in ∉ rC.image →
    DynamicCircuit Var n
  | 0, _, _, _, c_in, _, _, _, _, _, _ =>
      DynamicCircuit.circuit (if isInv then (Circuit.T c_in).inverse else Circuit.T c_in)
  | m + 1, uWires, rT, rC, c_in, hu_T, hu_C, hdisj_TC, hcin_u, hcin_T, hcin_C =>
      (gidneyApexStep0 uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).wrapDynamic v
        (gidneyApexChainDyn v isInv m (fun j ↦ uWires j.succ)
          (rT.slice 1 m (by omega)) (rC.slice 1 m (by omega)) (rC 0)
          (fun j hj ↦ hu_T j.succ (QRegister.image_compose_subset rT _ hj))
          (fun j hj ↦ hu_C j.succ (QRegister.image_compose_subset rC _ hj))
          ((hdisj_TC.compose_left _).compose_right _)
          (fun j h ↦ hu_C j.succ ((QRegister.mem_image rC _).mpr ⟨0, h⟩))
          (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj))
          (QRegExt.head_not_mem_tail_image rC))
@[simp] theorem count_gidneyApexChainDyn_toff (v : Var) (isInv : Bool) (w : ℕ)
    (uWires : Fin w → Wire n) (rT : QRegister w n) (rC : QRegister w n) (c_in : Wire n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) : (gidneyApexChainDyn v isInv w
    uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).count .TOFF = 0 := by
  induction w generalizing c_in with
  | zero => cases isInv <;> rfl
  | succ m ih =>
      rw [gidneyApexChainDyn, gidneyApexStep0,
        TempAndStep.count_wrapDynamic_toff _ _ _ (gidneyRippleStep_isClifford ..)]
      exact ih ..
@[simp] theorem count_gidneyApexChainDyn_t (v : Var) (isInv : Bool) (w : ℕ)
    (uWires : Fin w → Wire n) (rT : QRegister w n) (rC : QRegister w n) (c_in : Wire n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) : (gidneyApexChainDyn v isInv w
    uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).count .T = 4 * w + 1 := by
  induction w generalizing c_in with
  | zero => cases isInv <;> rfl
  | succ m ih =>
      rw [gidneyApexChainDyn, gidneyApexStep0,
        TempAndStep.count_wrapDynamic_t _ _ _ (gidneyRippleStep_isClifford ..), ih]
      omega
theorem gidneyApexChainDyn_wp_const [Finite Var] [DecidableEq Var] (v : Var) (isInv : Bool)
    (w : ℕ) (uWires : Fin w → Wire n) (rT : QRegister w n) (rC : QRegister w n)
    (c_in : Wire n) (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) (M : Observable (Fin (2 ^ n))) : ∃ M' :
    Observable (Fin (2 ^ n)), wp (gidneyApexChainDyn v isInv w uWires rT rC c_in hu_T hu_C hdisj_TC
    hcin_u hcin_T hcin_C).compile (fun _ ↦ M) = fun _ ↦ M' := by
  cases nonempty_fintype Var
  induction w generalizing c_in M with
  | zero =>
      let c0 : Circuit n := if isInv then (Circuit.T c_in).inverse else Circuit.T c_in
      exact ⟨qAssignObsMap c0.eval M, DynCircuitExt.wp_circuit_compile_compat c0 (fun _ ↦ M)⟩
  | succ m ih =>
      rw [gidneyApexChainDyn]
      exact TempAndStep.wp_wrapDynamic_const v _ _ (fun M₁ ↦ ih (fun j ↦ uWires j.succ)
        (rT.slice 1 m (by omega)) (rC.slice 1 m (by omega)) (rC 0) _ _ _ _ _ _ M₁) M
theorem gidneyApexChain_correct [Fintype Var] [DecidableEq Var]
    (v : Var) (isInv : Bool) (w : ℕ)
    (uWires : Fin w → Wire n) (rT : QRegister w n) (rC : QRegister w n) (c_in : Wire n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC)
    (hcin_u : ∀ j, c_in ≠ uWires j) (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) :
    ∃ (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n),
      PhasePerm rT.image
        (gidneyApexChainCircuit isInv w uWires rT rC c_in
          hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) φ f ∧
      (∀ β, (∀ i : Fin w, β (rC i) = 0) →
        let S := regVal rT β + bitsVal (fun j ↦ β (uWires j)) + (β c_in).val
        φ β = dyadicTurn 7 ((if isInv then (-16 : ℤ) else 16) * ((S / 2 ^ w : ℕ) : ℤ)) ∧
        regVal rT (f β) = S % 2 ^ w) ∧
      (∀ Θ : CQAssertionCompat Var (2 ^ n),
        (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
          CQAssertion.restrictToZeroAncilla
            (wp (gidneyApexChainDyn v isInv w uWires rT rC c_in
              hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).compile Θ) rC =
          CQAssertion.restrictToZeroAncilla
            (wpQAssignCompat (gidneyApexChainCircuit isInv w uWires rT rC c_in
              hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).eval Θ) rC) := by
  induction w generalizing c_in with
  | zero =>
      refine ⟨fun β ↦ dyadicTurn 7 ((if isInv then (-16 : ℤ) else 16) * (β c_in).val),
        id, ?_, fun β _ ↦ ?_, fun Θ _ ↦ ?_⟩
      · dsimp only [gidneyApexChainCircuit]
        cases isInv
        · exact (PhasePerm.gateT c_in).mono (Finset.empty_subset rT.image)
        · exact (PhasePerm.gateTDag c_in).mono (Finset.empty_subset rT.image)
      · have hreg0 : ∀ γ : BitAssignment n, regVal rT γ = 0 := fun _ ↦ by simp [regVal, bitsVal]
        have hbits0 : bitsVal (fun j : Fin 0 ↦ β (uWires j)) = 0 := by simp [bitsVal]
        dsimp only
        rw [hreg0, hreg0, hbits0, zero_add, zero_add, Nat.pow_zero, Nat.div_one, Nat.mod_one]
        exact ⟨rfl, rfl⟩
      · rw [gidneyApexChainDyn, gidneyApexChainCircuit, DynamicCircuit.compile_circuit,
          DynCircuitExt.wp_circuit_compile_compat]
  | succ m ih =>
      let rT_rest := rT.slice 1 m (by omega)
      let rC_rest := rC.slice 1 m (by omega)
      have hut : uWires 0 ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT _ (hu_T 0) 0
      have huc : uWires 0 ≠ rC 0 := QRegister.ne_apply_of_not_mem_image rC _ (hu_C 0) 0
      have htc : rT 0 ≠ rC 0 := hdisj_TC.ne 0 0
      have hcin_t : c_in ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT _ hcin_T 0
      have hcin_c : c_in ≠ rC 0 := QRegister.ne_apply_of_not_mem_image rC _ hcin_C 0
      have hu_T_rest : ∀ j : Fin m, uWires j.succ ∉ rT_rest.image :=
        fun j hj ↦ hu_T j.succ (QRegister.image_compose_subset rT _ hj)
      have hu_C_rest : ∀ j : Fin m, uWires j.succ ∉ rC_rest.image :=
        fun j hj ↦ hu_C j.succ (QRegister.image_compose_subset rC _ hj)
      have hdisj_TC_rest : rT_rest.DisjointWires rC_rest :=
        (hdisj_TC.compose_left _).compose_right _
      have hc0_u : ∀ j : Fin m, rC 0 ≠ uWires j.succ :=
        fun j h ↦ hu_C j.succ ((QRegister.mem_image rC _).mpr ⟨0, h⟩)
      have hc0_T_rest : rC 0 ∉ rT_rest.image :=
        fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj)
      have hc0_C_rest : rC 0 ∉ rC_rest.image := QRegExt.head_not_mem_tail_image rC
      have ht0_T_rest : rT 0 ∉ rT_rest.image := QRegExt.head_not_mem_tail_image rT
      have hu0_T_rest : uWires 0 ∉ rT_rest.image :=
        fun hj ↦ hu_T 0 (QRegister.image_compose_subset rT _ hj)
      have hcin_T_rest : c_in ∉ rT_rest.image :=
        fun hj ↦ hcin_T (QRegister.image_compose_subset rT _ hj)
      obtain ⟨φ_rest, f_rest, hperm_rest, hval_rest, hwp_rest⟩ := ih (fun j ↦ uWires j.succ)
        rT_rest rC_rest (rC 0) hu_T_rest hu_C_rest hdisj_TC_rest hc0_u hc0_T_rest hc0_C_rest
      have hout_rest := hperm_rest.outside
      let s_step := gidneyApexStep0 uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C
      let c_inner := gidneyApexChainCircuit isInv m (fun j ↦ uWires j.succ) rT_rest rC_rest
        (rC 0) hu_T_rest hu_C_rest hdisj_TC_rest hc0_u hc0_T_rest hc0_C_rest
      let d_inner := gidneyApexChainDyn v isInv m (fun j ↦ uWires j.succ) rT_rest rC_rest
        (rC 0) hu_T_rest hu_C_rest hdisj_TC_rest hc0_u hc0_T_rest hc0_C_rest
      let f_pre := fun β : BitAssignment n ↦ Function.update
        (Function.update β (uWires 0) (β (uWires 0) + β c_in)) (rT 0) (β (rT 0) + β c_in)
      let f_midPre := fun β : BitAssignment n ↦ Function.update
        (Function.update β (uWires 0) (β (uWires 0) + β c_in)) (rC 0) (β (rC 0) + β c_in)
      let f_midPost := fun β : BitAssignment n ↦ Function.update
        (Function.update β (rC 0) (β (rC 0) + β c_in)) (uWires 0) (β (uWires 0) + β c_in)
      let f_post := fun β : BitAssignment n ↦
        let β' := Function.update β (uWires 0) (β (uWires 0) + β c_in)
        Function.update β' (rT 0) (β' (rT 0) + β' (uWires 0))
      let f_toff := fun β : BitAssignment n ↦
        Function.update β (rC 0) (β (rC 0) + β (uWires 0) * β (rT 0))
      have hpre_perm : ClassicalPerm s_step.pre f_pre := fun β ↦ by
        dsimp only [s_step, gidneyApexStep0, gidneyRippleStep, f_pre]
        rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          evolve_CNOT_basisKet, evolve_CNOT_basisKet]
        congr 1
        funext q
        by_cases hqt : q = rT 0
        · subst hqt
          simp [Function.update_of_ne hut.symm, Function.update_of_ne (hcin_u 0)]
        · simp [Function.update_of_ne hqt]
      have hmidPre_perm : ClassicalPerm s_step.midPre f_midPre := fun β ↦ by
        dsimp only [s_step, gidneyApexStep0, gidneyRippleStep, f_midPre]
        rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          evolve_CNOT_basisKet, evolve_CNOT_basisKet]
        congr 1
        funext q
        by_cases hqc : q = rC 0
        · subst hqc
          simp [Function.update_of_ne huc.symm, Function.update_of_ne (hcin_u 0)]
        · simp [Function.update_of_ne hqc]
      have hmidPost_perm : ClassicalPerm s_step.midPost f_midPost := fun β ↦ by
        dsimp only [s_step, gidneyApexStep0, gidneyRippleStep, f_midPost]
        rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          evolve_CNOT_basisKet, evolve_CNOT_basisKet]
        congr 1
        funext q
        by_cases hqu : q = uWires 0
        · subst hqu
          simp [Function.update_of_ne huc, Function.update_of_ne hcin_c]
        · simp [Function.update_of_ne hqu]
      have hpost_perm : ClassicalPerm s_step.post f_post := fun β ↦ by
        dsimp only [s_step, gidneyApexStep0, gidneyRippleStep, f_post]
        rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          evolve_CNOT_basisKet, evolve_CNOT_basisKet]
      let f_body := f_midPost ∘ f_rest ∘ f_midPre
      have hcl_univ {c : Circuit n} {f : BitAssignment n → BitAssignment n}
          (hp : ClassicalPerm c f) : PhasePerm Finset.univ c (fun _ ↦ 1) f :=
        PhasePerm.of_classicalPerm hp (fun _ _ h ↦ absurd (Finset.mem_univ _) h)
      have hbody_phase : PhasePerm Finset.univ
          (s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost)
          (fun γ ↦ φ_rest (f_midPre γ)) f_body :=
        PhasePerm.congr_phase ((hcl_univ hmidPre_perm).seq
          ((hperm_rest.mono (Finset.subset_univ _)).seq (hcl_univ hmidPost_perm)))
          (fun _ ↦ by simp)
      have hbody_u0 : ∀ β, f_body β (uWires 0) = β (uWires 0) := fun β ↦ by
        simp [f_body, f_midPost, f_midPre, Function.update_of_ne huc,
          hout_rest _ (uWires 0) hu0_T_rest, hout_rest _ c_in hcin_T_rest,
          Function.update_of_ne (hcin_u 0), Function.update_of_ne hcin_c]
      have hbody_t0 : ∀ β, f_body β (rT 0) = β (rT 0) := fun β ↦ by
        simp [f_body, f_midPost, f_midPre, Function.update_of_ne hut.symm,
          Function.update_of_ne htc, hout_rest _ (rT 0) ht0_T_rest]
      have hbody_c0 : ∀ β, f_body β (rC 0) = β (rC 0) := fun β ↦ by
        simp [f_body, f_midPost, f_midPre, Function.update_of_ne huc.symm,
          hout_rest _ (rC 0) hc0_T_rest, hout_rest _ c_in hcin_T_rest,
          Function.update_of_ne (hcin_u 0), Function.update_of_ne hcin_c]
      have hbody_cin : ∀ β, f_body β c_in = β c_in := fun β ↦ by
        simp [f_body, f_midPost, f_midPre, Function.update_of_ne (hcin_u 0),
          Function.update_of_ne hcin_c, hout_rest _ c_in hcin_T_rest]
      have hc_body := toffoli_conj_preserves_zero_ancilla_of_phasePerm
        (uWires 0) (rT 0) (rC 0) hut huc htc (s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost)
        (fun γ ↦ φ_rest (f_midPre γ)) f_body hbody_phase hbody_u0 hbody_t0 hbody_c0
      let f_total := f_post ∘ f_toff ∘ f_body ∘ f_toff ∘ f_pre
      let φ_total : BitAssignment n → ℂ := fun β ↦ φ_rest (f_midPre (f_toff (f_pre β)))
      have hout_total : ∀ β q, q ∉ rT.image → f_total β q = β q := fun β q hq ↦ by
        have hqt0 : q ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT q hq 0
        have hq_rest : q ∉ rT_rest.image := fun hj ↦ hq (QRegister.image_compose_subset rT _ hj)
        let β₂ := f_toff (f_pre β)
        change f_post (f_toff (f_body β₂)) q = β q
        by_cases hqu : q = uWires 0
        · subst hqu
          dsimp only [f_post, f_toff]
          simp only [Function.update_of_ne hut, Function.update_self, Function.update_of_ne huc,
            Function.update_of_ne hcin_c, hbody_u0 β₂, hbody_cin β₂]
          dsimp only [β₂, f_toff, f_pre]
          simp [Function.update_of_ne huc, Function.update_of_ne hut, Function.update_of_ne hcin_c,
            Function.update_of_ne hcin_t, Function.update_of_ne (hcin_u 0)]
        · by_cases hqc : q = rC 0
          · subst hqc
            dsimp only [f_post, f_toff]
            simp only [Function.update_of_ne htc.symm, Function.update_of_ne huc.symm,
              Function.update_self, hbody_c0 β₂, hbody_u0 β₂, hbody_t0 β₂]
            dsimp only [β₂, f_toff, f_pre]
            simp [Function.update_of_ne huc, Function.update_of_ne htc,
              Function.update_of_ne htc.symm, Function.update_of_ne huc.symm]
          · dsimp only [f_post, f_toff]
            simp only [Function.update_of_ne hqt0, Function.update_of_ne hqu,
              Function.update_of_ne hqc]
            dsimp only [f_body, f_midPost, f_midPre, Function.comp_apply]
            simp only [Function.update_of_ne hqu, Function.update_of_ne hqc, hout_rest _ q hq_rest]
            dsimp only [β₂, f_toff, f_pre]
            simp [Function.update_of_ne hqc, Function.update_of_ne hqt0, Function.update_of_ne hqu]
      have htotal_phase : PhasePerm rT.image (gidneyApexChainCircuit isInv (m + 1) uWires rT
          rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) φ_total f_total := by
        have hp_toff := hcl_univ (ClassicalPerm.TOFF (uWires 0) (rT 0) (rC 0) hut huc htc)
        have hseq := (hcl_univ hpre_perm).seq
          (hp_toff.seq (hbody_phase.seq (hp_toff.seq (hcl_univ hpost_perm))))
        refine { evolve := fun β ↦ ?_, outside := hout_total }
        rw [gidneyApexChainCircuit, show s_step.wrapCircuit c_inner =
            s_step.pre ;;ᶜ (Circuit.TOFF (uWires 0) (rT 0) (rC 0) hut huc htc ;;ᶜ
              ((s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost) ;;ᶜ
                (Circuit.TOFF (uWires 0) (rT 0) (rC 0) hut huc htc ;;ᶜ s_step.post))) by
          simp [s_step, gidneyRippleStep, TempAndStep.wrapCircuit]]
        simpa [φ_total, f_total, Function.comp_apply] using hseq.evolve β
      refine ⟨φ_total, f_total, htotal_phase, fun β hβ_C ↦ ?_, fun Θ hΘ ↦ ?_⟩
      · let β_mid := f_midPre (f_toff (f_pre β))
        have hβ_mid_ne {q : Wire n} (hq_u0 : q ≠ uWires 0) (hq_t0 : q ≠ rT 0)
            (hq_c0 : q ≠ rC 0) : β_mid q = β q := by
          simp [β_mid, f_midPre, f_toff, f_pre, Function.update_of_ne hq_c0,
            Function.update_of_ne hq_u0, Function.update_of_ne hq_t0]
        have hβ_mid_c0 : β_mid (rC 0) =
            β c_in + (β (uWires 0) + β c_in) * (β (rT 0) + β c_in) := by
          simp [β_mid, f_midPre, f_toff, f_pre, Function.update_of_ne huc.symm,
            Function.update_of_ne htc.symm, Function.update_of_ne huc, Function.update_of_ne hut,
            Function.update_of_ne (hcin_u 0), Function.update_of_ne hcin_t,
            Function.update_of_ne hcin_c, hβ_C 0, add_comm]
        have hβ_mid_u : ∀ j : Fin m, β_mid (uWires j.succ) = β (uWires j.succ) := fun j ↦ by
          by_cases hju : uWires j.succ = uWires 0
          · rw [hju]
            simp [β_mid, f_midPre, f_toff, f_pre, Function.update_of_ne huc,
              Function.update_of_ne hut, Function.update_of_ne hcin_c,
              Function.update_of_ne hcin_t, Function.update_of_ne (hcin_u 0)]
          · exact hβ_mid_ne hju (QRegister.ne_apply_of_not_mem_image rT _ (hu_T j.succ) 0)
              (QRegister.ne_apply_of_not_mem_image rC _ (hu_C j.succ) 0)
        have hT_rest_ne (i : Fin m) :
            rT_rest i ≠ uWires 0 ∧ rT_rest i ≠ rT 0 ∧ rT_rest i ≠ rC 0 := by
          have hi := (QRegister.mem_image rT_rest _).mpr ⟨i, rfl⟩
          exact ⟨fun h ↦ hu0_T_rest (h ▸ hi), fun h ↦ ht0_T_rest (h ▸ hi),
            fun h ↦ hc0_T_rest (h ▸ hi)⟩
        have hβ_mid_T_rest : ∀ i : Fin m, β_mid (rT_rest i) = β (rT_rest i) := fun i ↦
          hβ_mid_ne (hT_rest_ne i).1 (hT_rest_ne i).2.1 (hT_rest_ne i).2.2
        have hβ_mid_C_rest : ∀ i : Fin m, β_mid (rC_rest i) = 0 := fun i ↦ by
          have hi := (QRegister.mem_image rC_rest _).mpr ⟨i, rfl⟩
          have hiC := QRegister.image_compose_subset rC _ hi
          rw [hβ_mid_ne (fun h ↦ hu_C 0 (h ▸ hiC))
            (fun h ↦ hdisj_TC.apply_not_mem_right 0 (h ▸ hiC)) (fun h ↦ hc0_C_rest (h ▸ hi))]
          exact hβ_C ⟨1 + i.val, by omega⟩
        have htotal_t0 : f_total β (rT 0) = β (uWires 0) + β (rT 0) + β c_in := by
          let β₂ := f_toff (f_pre β)
          change f_post (f_toff (f_body β₂)) (rT 0) = _
          dsimp only [f_post, f_toff]
          simp only [Function.update_self, Function.update_of_ne hut.symm,
            Function.update_of_ne htc, Function.update_of_ne huc, Function.update_of_ne hcin_c,
            hbody_t0 β₂, hbody_u0 β₂, hbody_cin β₂]
          dsimp only [β₂, f_toff, f_pre]
          simp only [Function.update_of_ne htc, Function.update_of_ne huc,
            Function.update_of_ne hut, Function.update_self, Function.update_of_ne hcin_c,
            Function.update_of_ne hcin_t, Function.update_of_ne (hcin_u 0)]
          rw [zmod2_add_cancel_right]
          ring
        have htotal_T_rest : ∀ i : Fin m, f_total β (rT_rest i) = f_rest β_mid (rT_rest i) :=
          fun i ↦ by
            obtain ⟨hu0, ht0, hc0⟩ := hT_rest_ne i
            simp [f_total, f_post, f_toff, f_body, f_midPost, β_mid,
              Function.update_of_ne ht0, Function.update_of_ne hu0, Function.update_of_ne hc0]
        obtain ⟨hφ_ih, hreg_ih⟩ := hval_rest β_mid hβ_mid_C_rest
        have hubits : bitsVal (fun j : Fin m ↦ β_mid (uWires j.succ)) =
            bitsVal (fun j : Fin m ↦ β (uWires j.succ)) :=
          Finset.sum_congr rfl fun j _ ↦ by dsimp only; rw [hβ_mid_u j]
        have hubits_split : bitsVal (fun j : Fin (m + 1) ↦ β (uWires j)) =
            (β (uWires 0)).val + 2 * bitsVal (fun j : Fin m ↦ β (uWires j.succ)) := by
          unfold bitsVal
          rw [Fin.sum_univ_succ, Finset.mul_sum]
          simp only [Fin.val_zero, _root_.pow_zero, mul_one]
          exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ by rw [Fin.val_succ, pow_succ]; ring)
        let S_mid : ℕ := regVal rT_rest β_mid +
          bitsVal (fun j : Fin m ↦ β_mid (uWires j.succ)) + (β_mid (rC 0)).val
        let s₀ : ℕ := (β (uWires 0) + β (rT 0) + β c_in).val
        have hS_eq : regVal rT β + bitsVal (fun j : Fin (m + 1) ↦ β (uWires j)) + (β c_in).val =
            s₀ + 2 * S_mid := by
          have hT_eq : regVal rT_rest β_mid = regVal rT_rest β :=
            regVal_congr rT_rest hβ_mid_T_rest
          dsimp only [S_mid, s₀]
          rw [regVal_head_tail rT β, hubits_split, hT_eq, hubits, hβ_mid_c0]
          dsimp only [rT_rest] at hT_eq ⊢
          linarith [zmod2_full_adder_val_local (β (uWires 0)) (β (rT 0)) (β c_in)]
        refine ⟨?_, ?_⟩
        · change φ_rest β_mid = _
          rw [hφ_ih, hS_eq, pow_succ', ← Nat.div_div_eq_div_mul,
            show (s₀ + 2 * S_mid) / 2 = S_mid from by
              have := ZMod.val_lt (β (uWires 0) + β (rT 0) + β c_in); omega]
        · rw [regVal_head_tail rT (f_total β)]
          change (f_total β (rT 0)).val + 2 * regVal rT_rest (f_total β) = _
          rw [htotal_t0, regVal_congr rT_rest htotal_T_rest, hreg_ih]
          change s₀ + 2 * (S_mid % 2 ^ m) = _
          rw [add_two_mul_mod s₀ S_mid (2 ^ m) (ZMod.val_lt _), ← pow_succ', ← hS_eq]
      · rw [gidneyApexChainDyn, gidneyApexChainCircuit]
        have hcin_Cr : c_in ∉ rC_rest.image :=
          fun hj ↦ hcin_C (QRegister.image_compose_subset rC _ hj)
        have hc1_rest : uWires 0 ∉ rC_rest.image :=
          fun hj ↦ hu_C 0 (QRegister.image_compose_subset rC _ hj)
        have hc2_rest : rT 0 ∉ rC_rest.image :=
          fun hj ↦ hdisj_TC.apply_not_mem_right 0 (QRegister.image_compose_subset rC _ hj)
        exact TempAndStep.restrictToZeroAncilla_wp_wrapDynamic_head_tail
          v s_step d_inner c_inner rC rfl
          (by simp [s_step, gidneyRippleStep, Circuit.support_seq, Circuit.support_gate,
            QRegister.image_pair, hcin_c.symm, huc.symm, htc.symm])
          (by
            dsimp only [s_step, gidneyApexStep0, gidneyRippleStep]
            simp only [Circuit.support_seq, Circuit.support_gate, QRegister.image_pair,
              Finset.disjoint_union_left, Finset.disjoint_insert_left,
              Finset.disjoint_singleton_left]
            exact ⟨⟨hcin_Cr, hc1_rest⟩, hcin_Cr, hc2_rest⟩)
          hc1_rest hc2_rest
          (by
            dsimp only [s_step, gidneyApexStep0, gidneyRippleStep]
            simp only [Circuit.support_seq, Circuit.support_gate, QRegister.image_pair,
              Finset.disjoint_union_left, Finset.disjoint_insert_left,
              Finset.disjoint_singleton_left]
            exact ⟨⟨hcin_Cr, hc1_rest⟩, hcin_Cr, hc0_C_rest⟩)
          hc_body hwp_rest Θ hΘ
def gidneyApexInvCircuit (w : ℕ) (uWires : Fin w → Wire n) (rT : QRegister w n)
    (rC : QRegister w n) (c_in : Wire n) (hu_T : ∀ j, uWires j ∉ rT.image)
    (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC)
    (hcin_u : ∀ j, c_in ≠ uWires j) (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) :
    Circuit n :=
  xAllCircuit rT ;;ᶜ
    gidneyApexChainCircuit true w uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C ;;ᶜ
    xAllCircuit rT
def gidneyApexInvDyn (v : Var) (w : ℕ) (uWires : Fin w → Wire n) (rT : QRegister w n)
    (rC : QRegister w n) (c_in : Wire n) (hu_T : ∀ j, uWires j ∉ rT.image)
    (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC)
    (hcin_u : ∀ j, c_in ≠ uWires j) (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) :
    DynamicCircuit Var n :=
  (DynamicCircuit.circuit (xAllCircuit rT)).seq ((gidneyApexChainDyn v true w uWires rT rC c_in
    hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq (DynamicCircuit.circuit (xAllCircuit rT)))
@[simp] theorem count_gidneyApexInvDyn_toff (v : Var) (w : ℕ) (uWires : Fin w → Wire n)
    (rT : QRegister w n) (rC : QRegister w n) (c_in : Wire n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) : (gidneyApexInvDyn v w uWires rT rC
    c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).count .TOFF = 0 := by
  simp [gidneyApexInvDyn]
@[simp] theorem count_gidneyApexInvDyn_t (v : Var) (w : ℕ) (uWires : Fin w → Wire n)
    (rT : QRegister w n) (rC : QRegister w n) (c_in : Wire n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) : (gidneyApexInvDyn v w uWires rT rC
    c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).count .T = 4 * w + 1 := by
  simp [gidneyApexInvDyn]
theorem gidneyApexInv_correct [Fintype Var] [DecidableEq Var] (v : Var) (w : ℕ)
    (uWires : Fin w → Wire n) (rT : QRegister w n) (rC : QRegister w n) (c_in : Wire n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC)
    (hcin_u : ∀ j, c_in ≠ uWires j) (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) :
    ∃ (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n),
      CleanPhasePerm rC rT.image
        (gidneyApexInvDyn v w uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C)
        (gidneyApexInvCircuit w uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C)
        φ f ∧
      (∀ β, (∀ i : Fin w, β (rC i) = 0) →
        let S_inv := (2 ^ w - 1 - regVal rT β) + bitsVal (fun j ↦ β (uWires j)) + (β c_in).val
        φ β = dyadicTurn 7 ((-16 : ℤ) * ((S_inv / 2 ^ w : ℕ) : ℤ)) ∧
        regVal rT (f β) = 2 ^ w - 1 - (S_inv % 2 ^ w)) ∧
      (∀ Θ : CQAssertionCompat Var (2 ^ n),
        (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
          CQAssertion.restrictToZeroAncilla
            (wp (gidneyApexInvDyn v w uWires rT rC c_in
              hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).compile Θ) rC =
          CQAssertion.restrictToZeroAncilla
            (wpQAssignCompat (gidneyApexInvCircuit w uWires rT rC c_in
              hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).eval Θ) rC) := by
  obtain ⟨φ_mid, f_mid, hp_mid, hval_mid, hwp_mid⟩ :=
    gidneyApexChain_correct v true w uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C
  have hx_phase : PhasePerm rT.image (xAllCircuit rT) (fun _ ↦ 1) (flipRegBits rT) :=
    PhasePerm.of_classicalPerm (classicalPerm_xAllCircuit rT) (flipRegBits_outside rT)
  have hcpp_sand := cleanPhasePerm_sandwich_phase
    (xAllCircuit rT) (xAllCircuit rT) (fun _ ↦ 1) (fun _ ↦ 1)
    (flipRegBits rT) (flipRegBits rT) hx_phase hx_phase (disjWires_image hdisj_TC)
    ⟨hp_mid, gidneyApexChainDyn_wp_const v true w uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u
      hcin_T hcin_C, fun Q ↦ hwp_mid _ fun _ _ ↦ rfl⟩
  refine ⟨fun β ↦ φ_mid (flipRegBits rT β), flipRegBits rT ∘ f_mid ∘ flipRegBits rT,
    ⟨PhasePerm.congr_phase (hcpp_sand.phasePerm.mono (by simp)) (fun _ ↦ by simp),
      hcpp_sand.wp_const, hcpp_sand.wp_obs⟩, fun β hβ_C ↦ ?_,
    restrictAssertionToZeroAncilla_sandwich_var v rC rT.image (xAllCircuit rT) (xAllCircuit rT)
      (fun _ ↦ 1) (flipRegBits rT) hx_phase (disjWires_image hdisj_TC) _ _ hwp_mid⟩
  let β₁ := flipRegBits rT β
  have hβ₁_u : bitsVal (fun j : Fin w ↦ β₁ (uWires j)) = bitsVal (fun j : Fin w ↦ β (uWires j)) :=
    Finset.sum_congr rfl fun j _ ↦ by dsimp only [β₁]; rw [flipRegBits_outside rT β (hu_T j)]
  obtain ⟨hφ₁, hreg₁⟩ := hval_mid β₁ fun i ↦ by
    dsimp only [β₁]
    rw [flipRegBits_outside rT β (hdisj_TC.apply_not_mem_left i), hβ_C i]
  have hβ₁_cin : β₁ c_in = β c_in := flipRegBits_outside rT β hcin_T
  dsimp only [Function.comp_apply]
  rw [regVal_flipRegBits rT β, hβ₁_u, hβ₁_cin] at hφ₁ hreg₁
  exact ⟨by simpa using hφ₁, by rw [regVal_flipRegBits rT (f_mid β₁), hreg₁]⟩
theorem ones_complement_div_mod_eq (W a u : ℕ) (hW : 0 < W) (ha : a < W) :
    (W - 1 - ((a + u) % W)) + u = (W - 1 - a) + W * ((a + u) / W) := by
  have hmod : (a + u) % W < W := Nat.mod_lt _ hW
  have hdiv : W * ((a + u) / W) + (a + u) % W = a + u := Nat.div_add_mod (a + u) W
  omega
theorem ones_complement_mod_cancel (W a u : ℕ) (hW : 0 < W) (ha : a < W) :
    W - 1 - (((W - 1 - ((a + u) % W)) + u) % W) = a := by
  have hlt : W - 1 - a < W := by omega
  rw [ones_complement_div_mod_eq W a u hW ha, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  omega
theorem ones_complement_div_eq (W a u : ℕ) (hW : 0 < W) (ha : a < W) :
    ((W - 1 - ((a + u) % W)) + u) / W = (a + u) / W := by
  have hlt : W - 1 - a < W := by omega
  rw [ones_complement_div_mod_eq W a u hW ha, Nat.add_mul_div_left _ _ hW,
    Nat.div_eq_of_lt hlt, zero_add]
def pack7Slices (s a b c : ℕ) : ℕ := a + 2 ^ s * b + 16 * c
theorem pack7Slices_lt (s : ℕ) (hs : s ≤ 3) (a b c : ℕ) (ha : a < 2 ^ s)
    (hb : b < 2 ^ (4 - s)) (hc : c < 8) : pack7Slices s a b c < 2 ^ 7 := by
  dsimp only [pack7Slices]
  interval_cases s <;> omega
theorem pack7Slices_parts (s : ℕ) (hs : s ≤ 3) (a b c : ℕ) (ha : a < 2 ^ s)
    (hb : b < 2 ^ (4 - s)) (_hc : c < 8) : (pack7Slices s a b c) % 2 ^ s = a ∧
    ((pack7Slices s a b c) / 2 ^ s) % 2 ^ (4 - s) = b ∧ (pack7Slices s a b c) / 16 = c := by
  dsimp only [pack7Slices]
  interval_cases s <;> omega
theorem unpack7Slices_eq (s : ℕ) (hs : s ≤ 3) (m : ℕ) (_hm : m < 2 ^ 7) :
    pack7Slices s (m % 2 ^ s) ((m / 2 ^ s) % 2 ^ (4 - s)) (m / 16) = m := by
  dsimp only [pack7Slices]
  interval_cases s <;> omega
theorem regVal_three_slices7 (s : ℕ) (hs : s ≤ 3) (rPG : QRegister 7 n) (δ : BitAssignment n) :
    regVal rPG δ = pack7Slices s (regVal (rPG.slice 0 s (by omega)) δ)
      (regVal (rPG.slice s (4 - s) (by omega)) δ) (regVal (rPG.slice 4 3 (by omega)) δ) := by
  have hslice (o o' w : ℕ) (ho : s + o = o') (h1 : o + w ≤ 7 - s) (h2 : o' + w ≤ 7) :
      (rPG.slice s (7 - s) (by omega)).slice o w h1 = rPG.slice o' w h2 :=
    DyadicQft64WalkCircuit288Alt.qreg_ext fun i ↦ by
      rw [QRegister.slice_apply, QRegister.slice_apply, QRegister.slice_apply]
      exact congrArg rPG (Fin.ext (by dsimp; omega))
  rw [regVal_split_slice rPG (s := s) (k_hi := 7 - s) (by omega) δ,
    regVal_split_slice (rPG.slice s (7 - s) (by omega)) (s := 4 - s) (k_hi := 3) (by omega) δ,
    hslice 0 s (4 - s) (by omega) (by omega) (by omega),
    hslice (4 - s) 4 3 (by omega) (by omega) (by omega),
    pack7Slices, ← two_pow_mul_four_sub s hs]
  ring
theorem regVal_midSlice7_eq (s : ℕ) (hs : s ≤ 3) (rPG : QRegister 7 n) (δ : BitAssignment n) :
    regVal (rPG.slice s (4 - s) (by omega)) δ = ((regVal rPG δ) / 2 ^ s) % 2 ^ (4 - s) := by
  rw [regVal_three_slices7 s hs rPG δ]
  exact (pack7Slices_parts s hs _ _ _ (regVal_lt_two_pow _ δ) (regVal_lt_two_pow _ δ)
    (regVal_lt_two_pow _ δ)).2.1.symm
theorem regVal_after_midSlice7 (s : ℕ) (hs : s ≤ 3) (rPG : QRegister 7 n)
    (f : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (hout : ∀ q, q ∉ (rPG.slice
    s (4 - s) (by omega)).image → f δ q = δ q) : regVal rPG (f δ) = pack7Slices s
    ((regVal rPG δ) % 2 ^ s) (regVal (rPG.slice s (4 - s) (by omega)) (f δ))
    ((regVal rPG δ) / 16) := by
  let rLo := rPG.slice 0 s (by omega)
  let rMid := rPG.slice s (4 - s) (by omega)
  let rHi := rPG.slice 4 3 (by omega)
  have hdisj_lm := QRegister.slice_disjoint_of_le rPG 0 s s (4 - s) (by omega) (by omega) (by omega)
  have hdisj_mh := QRegister.slice_disjoint_of_le rPG s (4 - s) 4 3 (by omega) (by omega) (by omega)
  have hlo_f : regVal rLo (f δ) = regVal rLo δ :=
    regVal_congr rLo fun i ↦ hout (rLo i) (hdisj_lm.apply_not_mem_right i)
  have hhi_f : regVal rHi (f δ) = regVal rHi δ :=
    regVal_congr rHi fun i ↦ hout (rHi i) (hdisj_mh.apply_not_mem_left i)
  have hparts := pack7Slices_parts s hs (regVal rLo δ) (regVal rMid δ) (regVal rHi δ)
    (regVal_lt_two_pow _ δ) (regVal_lt_two_pow _ δ) (regVal_lt_two_pow _ δ)
  rw [regVal_three_slices7 s hs rPG (f δ)]
  change pack7Slices s (regVal rLo (f δ)) (regVal rMid (f δ)) (regVal rHi (f δ)) = _
  rw [hlo_f, hhi_f, regVal_three_slices7 s hs rPG δ, hparts.1, hparts.2.2]
def sysCatGenPerm (kSys B : ℕ) (e : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B))) :
    Equiv.Perm (Fin (2 ^ (kSys + B))) :=
  let inner : Equiv.Perm (BitAssignment kSys × Fin (2 ^ B)) :=
    { toFun := fun p ↦ (p.1, e p.1 p.2)
      invFun := fun p ↦ (p.1, (e p.1).symm p.2)
      left_inv := fun ⟨_, _⟩ ↦ by simp
      right_inv := fun ⟨_, _⟩ ↦ by simp }
  (sysCatEquiv kSys B).trans (inner.trans (sysCatEquiv kSys B).symm)
theorem sysCatEquiv_sysCatGenPerm (kSys B : ℕ)
    (e : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B))) (col : Fin (2 ^ (kSys + B))) :
    sysCatEquiv kSys B (sysCatGenPerm kSys B e col) = ((sysCatEquiv kSys B col).1, e
    (sysCatEquiv kSys B col).1 (sysCatEquiv kSys B col).2) := by
  simp [sysCatGenPerm]
noncomputable def genCatPhasePermUnitary (kSys B : ℕ)
    (e : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B)))
    (ψ : BitAssignment kSys → Fin (2 ^ B) → ℤ) : Unitary (2 ^ (kSys + B)) :=
  ⟨Matrix.of fun row col ↦
    if sysCatGenPerm kSys B e col = row then
      dyadicTurn B (ψ (sysCatEquiv kSys B col).1 (sysCatEquiv kSys B col).2)
    else 0, by
    rw [Matrix.mem_unitaryGroup_iff']
    ext col₁ col₂
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (sysCatGenPerm kSys B e col₁)]
    · by_cases h : col₁ = col₂
      · subst h
        simpa only [Matrix.star_apply, Matrix.of_apply, ↓reduceIte] using
          star_dyadicTurn_mul_self B _
      · have hne : sysCatGenPerm kSys B e col₂ ≠ sysCatGenPerm kSys B e col₁ :=
          fun eq ↦ h ((sysCatGenPerm kSys B e).injective eq.symm)
        simp only [Matrix.star_apply, Matrix.of_apply, h, hne, ↓reduceIte, mul_zero]
    · intro row _ hne
      simp only [Matrix.star_apply, Matrix.of_apply, Ne.symm hne, ↓reduceIte, star_zero, zero_mul]
    · intro hm
      exact absurd (Finset.mem_univ _) hm⟩
@[simp] theorem genCatPhasePermUnitary_apply (kSys B : ℕ)
    (e : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B)))
    (ψ : BitAssignment kSys → Fin (2 ^ B) → ℤ) (row col : Fin (2 ^ (kSys + B))) :
    (genCatPhasePermUnitary kSys B e ψ).1 row col = if sysCatGenPerm kSys B e col = row then
    dyadicTurn B (ψ (sysCatEquiv kSys B col).1 (sysCatEquiv kSys B col).2) else 0 := rfl
theorem genCatPhasePermUnitary_mul (kSys B : ℕ)
    (e₁ e₂ : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B)))
    (ψ₁ ψ₂ : BitAssignment kSys → Fin (2 ^ B) → ℤ) : genCatPhasePermUnitary kSys B e₂ ψ₂ *
    genCatPhasePermUnitary kSys B e₁ ψ₁ = genCatPhasePermUnitary kSys B
    (fun γ ↦ (e₁ γ).trans (e₂ γ)) (fun γ m ↦ ψ₁ γ m + ψ₂ γ (e₁ γ m)) := by
  ext row col
  rw [Submonoid.coe_mul, Matrix.mul_apply, genCatPhasePermUnitary_apply,
    Finset.sum_eq_single (sysCatGenPerm kSys B e₁ col)
      (fun mid _ hne ↦ by simp [Ne.symm hne])
      (fun hmem ↦ absurd (Finset.mem_univ _) hmem)]
  simp only [genCatPhasePermUnitary_apply, ↓reduceIte]
  have hcomp : sysCatGenPerm kSys B e₂ (sysCatGenPerm kSys B e₁ col) =
      sysCatGenPerm kSys B (fun γ ↦ (e₁ γ).trans (e₂ γ)) col :=
    (sysCatEquiv kSys B).injective (by simp [sysCatEquiv_sysCatGenPerm])
  rw [hcomp, sysCatEquiv_sysCatGenPerm]
  split_ifs
  · rw [dyadicTurn_add]
    dsimp only
    rw [add_comm]
  · simp
theorem genCatPhasePermUnitary_id (kSys B : ℕ) :
    genCatPhasePermUnitary kSys B (fun _ ↦ Equiv.refl _) (fun _ _ ↦ 0) = 1 := by
  ext row col
  rw [genCatPhasePermUnitary_apply, OneMemClass.coe_one, Matrix.one_apply]
  have hid : sysCatGenPerm kSys B (fun _ ↦ Equiv.refl _) col = col :=
    (sysCatEquiv kSys B).injective (by simp [sysCatEquiv_sysCatGenPerm])
  rw [hid]
  by_cases h : col = row
  · subst h
    simp
  · simp [h, Ne.symm h]
theorem genCatPhasePermUnitary_inv (kSys B : ℕ)
    (e : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B)))
    (ψ : BitAssignment kSys → Fin (2 ^ B) → ℤ) : (genCatPhasePermUnitary kSys B e ψ)⁻¹ =
    genCatPhasePermUnitary kSys B (fun γ ↦ (e γ).symm) (fun γ k ↦ -ψ γ ((e γ).symm k)) := by
  apply inv_eq_of_mul_eq_one_left
  rw [genCatPhasePermUnitary_mul]
  have he : (fun γ ↦ (e γ).trans (e γ).symm) = fun _ ↦ Equiv.refl (Fin (2 ^ B)) := by
    funext γ
    ext m
    simp
  have hψ : (fun γ m ↦ ψ γ m + -ψ γ ((e γ).symm (e γ m))) = fun _ _ ↦ (0 : ℤ) := by
    funext γ m
    simp
  rw [he, hψ]
  exact genCatPhasePermUnitary_id kSys B
theorem embedUnitary_genCatPhasePermUnitary_mulVec_basisKet {kSys B : ℕ}
    (rSys : QRegister kSys n) (rPG : QRegister B n) (hdisj : rSys.DisjointWires rPG)
    (e : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B)))
    (ψ : BitAssignment kSys → Fin (2 ^ B) → ℤ)
    (β : BitAssignment n) :
    let rAct := rSys.concat rPG hdisj
    let γ : BitAssignment kSys := fun i ↦ β (rSys i)
    let mIn : Fin (2 ^ B) := ⟨regVal rPG β, regVal_lt_two_pow rPG β⟩
    let mNext : Fin (2 ^ B) := e γ mIn
    (rAct.embedUnitary (genCatPhasePermUnitary kSys B e ψ)).1.mulVec (basisKet β) =
      dyadicTurn B (ψ γ mIn) •
        basisKet (basisBits n (rPG.replaceIndex ((basisBitsEquiv n).symm β) mNext)) := by
  intro rAct γ mIn mNext
  let gIdx := (basisBitsEquiv n).symm β
  have hm_eq : rPG.extractIndex gIdx = mIn := Fin.ext (regVal_eq_extractIndex_val rPG β).symm
  have hext_act : sysCatEquiv kSys B (rAct.extractIndex gIdx) = (γ, mIn) := by
    ext i
    · change basisBits (kSys + B) (rAct.extractIndex gIdx) (Fin.castAdd B i) = β (rSys i)
      rw [rAct.basisBits_extractIndex, QRegister.concat_apply_left]
      exact congrFun ((basisBitsEquiv n).apply_symm_apply β) (rSys i)
    · have hbits : (fun j ↦ (basisBitsEquiv (kSys + B)) (rAct.extractIndex gIdx)
          (Fin.natAdd kSys j)) = (basisBitsEquiv B) (rPG.extractIndex gIdx) := by
        funext j
        change basisBits (kSys + B) (rAct.extractIndex gIdx) (Fin.natAdd kSys j) =
          basisBits B (rPG.extractIndex gIdx) j
        rw [rAct.basisBits_extractIndex, rPG.basisBits_extractIndex, QRegister.concat_apply_right]
      change ((basisBitsEquiv B).symm (fun j ↦ _)).val = mIn.val
      rw [hbits, (basisBitsEquiv B).symm_apply_apply, hm_eq]
  have hlocal :
      (genCatPhasePermUnitary kSys B e ψ).1.mulVec (Pi.single (rAct.extractIndex gIdx) 1) =
        dyadicTurn B (ψ γ mIn) • Pi.single (sysCatGenPerm kSys B e (rAct.extractIndex gIdx)) 1 := by
    funext row
    rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single (rAct.extractIndex gIdx)
      (fun c hc ↦ by simp [hc])]
    simp only [Pi.single_apply, ↓reduceIte, mul_one, genCatPhasePermUnitary_apply, Pi.smul_apply,
      smul_eq_mul, hext_act]
    by_cases h : sysCatGenPerm kSys B e (rAct.extractIndex gIdx) = row
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hrep_eq : rAct.replaceIndex gIdx (sysCatGenPerm kSys B e (rAct.extractIndex gIdx)) =
      rPG.replaceIndex gIdx mNext := by
    apply (basisBitsEquiv n).injective
    funext q
    change basisBits n (rAct.replaceIndex gIdx _) q = basisBits n (rPG.replaceIndex gIdx mNext) q
    have hsymm : sysCatGenPerm kSys B e (rAct.extractIndex gIdx) =
        (sysCatEquiv kSys B).symm (γ, mNext) := by
      apply (sysCatEquiv kSys B).injective
      rw [sysCatEquiv_sysCatGenPerm, hext_act, Equiv.apply_symm_apply]
    by_cases hqAct : q ∈ Set.range rAct.wires
    · rcases hqAct with ⟨idx, rfl⟩
      rw [rAct.basisBits_replaceIndex_apply, hsymm, basisBits_sysCatEquiv_symm]
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · simp only [Fin.addCases_left, rAct, QRegister.concat_apply_left, γ]
        rw [rPG.basisBits_replaceIndex_of_not_mem _ _ _
          (fun hmem ↦ Set.disjoint_left.mp hdisj ⟨i, rfl⟩ hmem)]
        exact (congrFun ((basisBitsEquiv n).apply_symm_apply β) (rSys i)).symm
      · simp only [Fin.addCases_right, rAct, QRegister.concat_apply_right,
          rPG.basisBits_replaceIndex_apply]
    · rw [rAct.basisBits_replaceIndex_of_not_mem _ _ _ hqAct,
        rPG.basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨j, hj⟩ ↦
          hqAct ⟨Fin.natAdd kSys j, (QRegister.concat_apply_right rSys rPG hdisj j).trans hj⟩)]
  rw [QRegister.embedUnitary_val, basisKet, basisState, rAct.embedMatrix_mulVec_single_factors,
    hlocal, rAct.tensorState_smul_left, rAct.tensorState_single_replaceIndex, hrep_eq]
  dsimp only [basisKet, basisState, gIdx]
  congr 2
  exact ((basisBitsEquiv n).symm_apply_apply _).symm
theorem cleanPhasePerm_realizes_genCatPhasePerm [Fintype Var] [DecidableEq Var] {kSys B m : ℕ}
    {rSys : QRegister kSys n} {rPG : QRegister B n} {rWork : QRegister m n}
    (hdisj : rSys.DisjointWires rPG) {M : Finset (Wire n)} {d : DynamicCircuit Var n}
    {c : Circuit n} {φ_ket : BitAssignment n → ℂ} {f_ket : BitAssignment n → BitAssignment n}
    (hcpp : CleanPhasePerm rWork M d c φ_ket f_ket)
    (e : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B)))
    (ψ : BitAssignment kSys → Fin (2 ^ B) → ℤ) (hφ : ∀ β, (∀ j : Fin m, β (rWork j) = 0) →
    φ_ket β = dyadicTurn B (ψ (fun i ↦ β (rSys i)) ⟨regVal rPG β, regVal_lt_two_pow rPG β⟩))
    (hout : ∀ β q, q ∉ rPG.image → f_ket β q = β q) (hval : ∀ β, (∀ j : Fin m, β (rWork j) =
    0) → regVal rPG (f_ket β) = (e (fun i ↦ β (rSys i)) ⟨regVal rPG β, regVal_lt_two_pow rPG
    β⟩).val) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rSys.concat rPG hdisj) rWork (genCatPhasePermUnitary kSys B e ψ) d := by
  refine CleanPhasePerm.realizes hcpp (genCatPhasePermUnitary kSys B e ψ) fun β hzero ↦ ?_
  rw [embedUnitary_genCatPhasePermUnitary_mulVec_basisKet rSys rPG hdisj e ψ β, hφ β hzero]
  congr 2
  funext q
  by_cases hqP : q ∈ Set.range rPG.wires
  · rcases hqP with ⟨j, rfl⟩
    have hbits : basisBits B ⟨regVal rPG (f_ket β), regVal_lt_two_pow rPG (f_ket β)⟩ =
        fun t ↦ f_ket β (rPG t) :=
      (basisBitsEquiv B).symm.injective (Fin.ext (by simp [regVal, bitsVal_eq_symm_val]))
    have heq_fin : e (fun i ↦ β (rSys i)) ⟨regVal rPG β, regVal_lt_two_pow rPG β⟩ =
        ⟨regVal rPG (f_ket β), regVal_lt_two_pow rPG (f_ket β)⟩ := Fin.ext (hval β hzero).symm
    rw [rPG.basisBits_replaceIndex_apply, heq_fin, hbits]
  · rw [rPG.basisBits_replaceIndex_of_not_mem _ _ q hqP, basisBits_symm_apply_2a,
      hout β q fun hm ↦ hqP ((QRegister.mem_image rPG q).mp hm)]
theorem genCatPhasePermUnitary_intertwinesCat {N kSys B : ℕ} [NeZero (2 ^ N)]
    (rSys : QRegister kSys N) (rCat : QRegister B N) (hdisj : rSys.DisjointWires rCat)
    (U_cat_B : Unitary (2 ^ B)) (hcol0 : U_cat_B.1.mulVec (Pi.single 0 1) =
    DyadicQft64.phaseGradKet B) (e : BitAssignment kSys → Equiv.Perm (Fin (2 ^ B)))
    (ψ : BitAssignment kSys → Fin (2 ^ B) → ℤ) (Θ_eff : BitAssignment kSys → ℤ) (hrel : ∀ (γ :
    BitAssignment kSys) (m : Fin (2 ^ B)), ψ γ m + ((e γ m).val : ℤ) = Θ_eff γ + (m.val : ℤ))
    : DyadicQft64.IntertwinesCatOp (rCat.embedUnitary U_cat_B).1
    (rCat.basisOutcomeProjector 0) ((rSys.concat rCat hdisj).embedUnitary
    (genCatPhasePermUnitary kSys B e ψ)).1
    (rSys.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys B Θ_eff)).1 := by
  refine ⟨?_, rSys.embedMatrix_comm_of_disjoint rCat hdisj _ _,
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rSys) rCat hdisj _ 0⟩
  apply matrix_ext_basisKet
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, register_basisOutcomeProjector_zero_mulVec_basisKet]
  split_ifs with hzero
  · let idx₀ := (basisBitsEquiv N).symm β
    let γ : BitAssignment kSys := fun i ↦ β (rSys i)
    have hext0 : rCat.extractIndex idx₀ = 0 :=
      (QRegExt.extractIndex_eq_zero_iff ..).mpr fun j ↦ by simp [idx₀, hzero j]
    have hprep : (rCat.embedUnitary U_cat_B).1.mulVec (basisKet β) = ∑ m : Fin (2 ^ B),
        DyadicQft64.phaseGradKet B m • basisKet (basisBits N (rCat.replaceIndex idx₀ m)) := by
      have hexpand : DyadicQft64.phaseGradKet B =
          ∑ m : Fin (2 ^ B), DyadicQft64.phaseGradKet B m • Pi.single m (1 : ℂ) := by
        funext x
        rw [Finset.sum_apply, Finset.sum_eq_single x (fun m _ hmx ↦ by simp [Ne.symm hmx])
          (fun hx ↦ absurd (Finset.mem_univ x) hx)]
        simp
      conv_lhs =>
        rw [QRegister.embedUnitary_val, basisKet, basisState,
          rCat.embedMatrix_mulVec_single_factors, hext0, hcol0, hexpand,
          rCat.tensorState_sum_left]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [rCat.tensorState_smul_left, rCat.tensorState_single_replaceIndex]
      have hidx : (basisBitsEquiv N).symm (basisBits N (rCat.replaceIndex idx₀ m)) =
          rCat.replaceIndex idx₀ m :=
        (basisBitsEquiv N).symm_apply_apply (rCat.replaceIndex idx₀ m)
      dsimp only [idx₀] at hidx ⊢
      simp only [basisKet, basisState, hidx]
    rw [embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul, hprep,
      Matrix.mulVec_sum, Finset.smul_sum]
    have hstep (m : Fin (2 ^ B)) : ((rSys.concat rCat hdisj).embedUnitary
        (genCatPhasePermUnitary kSys B e ψ)).1.mulVec
        (basisKet (basisBits N (rCat.replaceIndex idx₀ m))) = dyadicTurn B (ψ γ m) • basisKet
        (basisBits N (rCat.replaceIndex idx₀ (e γ m))) := by
      let β_m := basisBits N (rCat.replaceIndex idx₀ m)
      have hraw := embedUnitary_genCatPhasePermUnitary_mulVec_basisKet rSys rCat hdisj e ψ β_m
      have hsys_m : (fun i ↦ β_m (rSys i)) = γ := funext fun i ↦ by
        dsimp only [β_m]
        rw [rCat.basisBits_replaceIndex_of_not_mem idx₀ m (rSys i)
          (fun ⟨j, hj⟩ ↦ hdisj.ne i j hj.symm)]
        simp [γ, idx₀]
      have hm_in : (⟨regVal rCat β_m, regVal_lt_two_pow rCat β_m⟩ : Fin (2 ^ B)) = m := by
        apply Fin.ext
        change regVal rCat β_m = m.val
        rw [regVal, show (fun j ↦ β_m (rCat j)) = basisBits B m from
          funext (rCat.basisBits_replaceIndex_apply idx₀ m), bitsVal_basisBits]
      have hrep_m : rCat.replaceIndex ((basisBitsEquiv N).symm β_m) (e γ m) =
          rCat.replaceIndex idx₀ (e γ m) := by
        have hidx : (basisBitsEquiv N).symm β_m = rCat.replaceIndex idx₀ m :=
          (basisBitsEquiv N).symm_apply_apply (rCat.replaceIndex idx₀ m)
        rw [hidx, QRegister.replaceIndex_replaceIndex]
      dsimp only at hraw
      rwa [hsys_m, hm_in, hrep_m] at hraw
    simp_rw [Matrix.mulVec_smul, hstep, smul_smul]
    rw [← (e γ).symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    let m' := (e γ).symm k
    have hek : e γ m' = k := (e γ).apply_symm_apply k
    change (DyadicQft64.phaseGradKet B m' * dyadicTurn B (ψ γ m')) •
        basisKet (basisBits N (rCat.replaceIndex idx₀ (e γ m'))) =
      (dyadicTurn B (Θ_eff γ) * DyadicQft64.phaseGradKet B k) •
        basisKet (basisBits N (rCat.replaceIndex idx₀ k))
    rw [hek]
    congr 1
    rw [phaseGradKet_eq_norm_mul_dyadicTurn B m', phaseGradKet_eq_norm_mul_dyadicTurn B k,
      mul_assoc, dyadicTurn_add, ← mul_assoc, mul_comm (dyadicTurn B (Θ_eff γ)), mul_assoc,
      dyadicTurn_add]
    congr 2
    have hrel' := hrel γ m'
    rw [hek] at hrel'
    omega
  · simp
def midSlicePerm7 (s : ℕ) (hs : s ≤ 3) (u : ℕ) : Equiv.Perm (Fin (2 ^ 7)) where
  toFun m :=
    ⟨pack7Slices s
        (m.val % 2 ^ s)
        (((m.val / 2 ^ s) % 2 ^ (4 - s) + u) % 2 ^ (4 - s))
        (m.val / 16),
      pack7Slices_lt s hs _ _ _
        (Nat.mod_lt _ (by positivity))
        (Nat.mod_lt _ (by positivity))
        (by have := m.isLt; omega)⟩
  invFun k :=
    ⟨pack7Slices s
        (k.val % 2 ^ s)
        (2 ^ (4 - s) - 1 -
          (((2 ^ (4 - s) - 1 - ((k.val / 2 ^ s) % 2 ^ (4 - s))) + u) % 2 ^ (4 - s)))
        (k.val / 16),
      pack7Slices_lt s hs _ _ _
        (Nat.mod_lt _ (by positivity))
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (by positivity) Nat.one_pos))
        (by have := k.isLt; omega)⟩
  left_inv m := by
    apply Fin.ext
    have hW : 0 < 2 ^ (4 - s) := by positivity
    obtain ⟨p1, p2, p3⟩ := pack7Slices_parts s hs _ _ _ (Nat.mod_lt _ (by positivity))
      (Nat.mod_lt _ hW) (show m.val / 16 < 8 by have := m.isLt; omega)
    dsimp only
    rw [p1, p2, p3, ones_complement_mod_cancel (2 ^ (4 - s)) _ u hW (Nat.mod_lt _ hW),
      unpack7Slices_eq s hs m.val m.isLt]
  right_inv k := by
    apply Fin.ext
    let W := 2 ^ (4 - s)
    have hW : 0 < W := by positivity
    let b := (k.val / 2 ^ s) % W
    have hb : b < W := Nat.mod_lt _ hW
    obtain ⟨p1, p2, p3⟩ := pack7Slices_parts s hs (k.val % 2 ^ s)
      (W - 1 - (((W - 1 - b) + u) % W)) (k.val / 16) (Nat.mod_lt _ (by positivity))
      (by omega) (show k.val / 16 < 8 by have := k.isLt; omega)
    dsimp only
    change pack7Slices s _ _ _ = k.val
    rw [p1, p2, p3]
    have hdiv_mod := ones_complement_div_mod_eq W (W - 1 - b) u hW (by omega)
    rw [show W - 1 - (W - 1 - b) = b by omega] at hdiv_mod
    rw [hdiv_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb,
      unpack7Slices_eq s hs k.val k.isLt]
noncomputable def apexCatUnitary (kSys s : ℕ) (hs : s ≤ 3) (Φ : BitAssignment kSys → ℤ)
    (uLow : BitAssignment kSys → ℕ) : Unitary (2 ^ (kSys + 7)) := genCatPhasePermUnitary kSys
    7 (fun γ ↦ midSlicePerm7 s hs (uLow γ)) (fun γ m ↦ Φ γ + 16 * (((((m.val / 2 ^ s) % 2 ^ (4
    - s)) + uLow γ) / 2 ^ (4 - s) : ℕ) : ℤ))
theorem apexCatUnitary_intertwinesCat {N kSys : ℕ} [NeZero (2 ^ N)] (s : ℕ) (hs : s ≤ 3)
    (rSys : QRegister kSys N) (rPG : QRegister 7 N) (hdisj : rSys.DisjointWires rPG)
    (U_cat7 : Unitary (2 ^ 7)) (hcol0 : U_cat7.1.mulVec (Pi.single 0 1) =
    DyadicQft64.phaseGradKet 7) (Φ : BitAssignment kSys → ℤ) (uLow : BitAssignment kSys → ℕ) :
    DyadicQft64.IntertwinesCatOp (rPG.embedUnitary U_cat7).1 (rPG.basisOutcomeProjector 0)
    ((rSys.concat rPG hdisj).embedUnitary (apexCatUnitary kSys s hs Φ uLow)).1
    (rSys.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 7 (fun γ ↦ Φ γ + ((2 ^ s * uLow γ :
    ℕ) : ℤ)))).1 := by
  refine genCatPhasePermUnitary_intertwinesCat rSys rPG hdisj U_cat7 hcol0
    (fun γ ↦ midSlicePerm7 s hs (uLow γ)) (fun γ m ↦ Φ γ + 16 * (((((m.val / 2 ^ s) % 2 ^ (4 -
    s)) + uLow γ) / 2 ^ (4 - s) : ℕ) : ℤ)) (fun γ ↦ Φ γ + ((2 ^ s * uLow γ : ℕ) : ℤ)) fun γ m
    ↦ ?_
  let W := 2 ^ (4 - s)
  let a := m.val % 2 ^ s
  let b := (m.val / 2 ^ s) % W
  let c := m.val / 16
  have hnat : 16 * ((b + uLow γ) / W) + (a + 2 ^ s * ((b + uLow γ) % W) + 16 * c) =
      2 ^ s * uLow γ + m.val := by
    calc 16 * ((b + uLow γ) / W) + (a + 2 ^ s * ((b + uLow γ) % W) + 16 * c)
        = (2 ^ s * W) * ((b + uLow γ) / W) + 2 ^ s * ((b + uLow γ) % W) + (a + 16 * c) := by
            rw [two_pow_mul_four_sub s hs]
            ring
      _ = 2 ^ s * (b + uLow γ) + (a + 16 * c) := by
            rw [mul_assoc (2 ^ s), ← mul_add (2 ^ s), Nat.div_add_mod]
      _ = 2 ^ s * uLow γ + m.val := by
            rw [← unpack7Slices_eq s hs m.val m.isLt]
            unfold pack7Slices
            ring
  have hnat_z : 16 * ((((b + uLow γ) / W : ℕ) : ℤ)) +
      (((midSlicePerm7 s hs (uLow γ) m).val : ℕ) : ℤ) =
        ((2 ^ s * uLow γ : ℕ) : ℤ) + (m.val : ℤ) := by
    change 16 * ((((b + uLow γ) / W : ℕ) : ℤ)) +
        ((a + 2 ^ s * ((b + uLow γ) % W) + 16 * c : ℕ) : ℤ) = _
    exact_mod_cast hnat
  linarith [hnat_z]
end ApexButterflyEngine
abbrev rW232Canon288 : QRegister 232 nCanon4222 := rWorkCanon288.slice 0 232 (by decide)
abbrev rSub225Canon288 : QRegister (232 - 7) nCanon4222 :=
  rW232Canon288.slice 7 (232 - 7) (by decide)
theorem rSub225_disj_sys : rSysCanon288.DisjointWires rSub225Canon288 :=
  (rSysCanon288_disjoint_rWorkCanon288.compose_right _).compose_right _
theorem rSub225_disj_pg : rPGCanon288.DisjointWires rSub225Canon288 :=
  (rPGCanon288_disjoint_rWorkCanon288.compose_right _).compose_right _
theorem rSub225_disj_qft : (rSysCanon288.concat rPGCanon288
    rSysCanon288_disjoint_rPGCanon288).DisjointWires rSub225Canon288 := disjoint_concat_left
    rSysCanon288_disjoint_rPGCanon288 rSub225_disj_sys rSub225_disj_pg
structure InnerModAddSpec288 where
  shift : BitAssignment (3924 + 3) → ℕ
  tCost : ℕ
  dFwd : DynamicCircuit Unit nCanon4222
  dInv : DynamicCircuit Unit nCanon4222
  hToffFwd : dFwd.count .TOFF = 0
  hToffInv : dInv.count .TOFF = 0
  hTFwd : dFwd.count .T = tCost
  hTInv : dInv.count .T = tCost
  hRealFwd : RealizesEmbeddedUnitaryWithCleanWorkspace
    (rSysCanon288.concat rPGCanon288 rSysCanon288_disjoint_rPGCanon288)
    rSub225Canon288
    (catModAddUnitary (3924 + 3) 7 shift) dFwd
  hRealInv : RealizesEmbeddedUnitaryWithCleanWorkspace
    (rSysCanon288.concat rPGCanon288 rSysCanon288_disjoint_rPGCanon288)
    rSub225Canon288
    (catModAddUnitary (3924 + 3) 7 shift)⁻¹ dInv
noncomputable def InnerModAddSpec288.id : InnerModAddSpec288 where
  shift := fun _ ↦ 0
  tCost := 0
  dFwd := .identity
  dInv := .identity
  hToffFwd := rfl
  hToffInv := rfl
  hTFwd := rfl
  hTInv := rfl
  hRealFwd := by
    rw [catModAddUnitary_zero_eq_one]
    exact realizesEmbeddedUnitaryWithCleanWorkspace_identity _ _
  hRealInv := by
    rw [catModAddUnitary_zero_eq_one, inv_one]
    exact realizesEmbeddedUnitaryWithCleanWorkspace_identity _ _
noncomputable def InnerModAddSpec288.seq (A B : InnerModAddSpec288) : InnerModAddSpec288 where
  shift := fun γ ↦ A.shift γ + B.shift γ
  tCost := A.tCost + B.tCost
  dFwd := .seq A.dFwd B.dFwd
  dInv := .seq B.dInv A.dInv
  hToffFwd := by simp [A.hToffFwd, B.hToffFwd]
  hToffInv := by simp [B.hToffInv, A.hToffInv]
  hTFwd := by simp [A.hTFwd, B.hTFwd]
  hTInv := by simp only [DynamicCircuit.count, B.hTInv, A.hTInv, Nat.add_comm]
  hRealFwd := by
    rw [← catModAddUnitary_mul_add]
    exact A.hRealFwd.seq rSub225_disj_qft B.hRealFwd
  hRealInv := by
    rw [← catModAddUnitary_mul_add, _root_.mul_inv_rev]
    exact B.hRealInv.seq rSub225_disj_qft A.hRealInv
/-- Holder for the `(3924 + 3)`-wire core QFT Hadamard-and-phase unitary. -/
structure CoreQftEffHolder288 where
  uEff : Unitary (2 ^ (3924 + 3))
/-- Exact `(3924 + 3)`-wire core QFT Hadamard-and-phase unitary. -/
noncomputable def coreQftHadamardStages288 : CoreQftEffHolder288 :=
  ⟨stageH654 0 * (stageD654 1 * stageH654 1) * (stageD654 2 * stageH654 2) *
    (stageD654 3 * stageH654 3) * (stageD654 4 * stageH654 4) * (stageD654 5 * stageH654 5)⟩
theorem qft64Ideal654Unitary_eq_core_mul_preDiag :
    qft64Ideal654Unitary = coreQftHadamardStages288.uEff * (preDiag654 * bit5Flip654) := by
  have hdef : qft64Ideal654Unitary = (coreQftHadamardStages288.uEff * preDiag654) * bit5Flip654 :=
    rfl
  rw [hdef, _root_.mul_assoc]
theorem mulVec_col0_eq_phaseGradKet7 (U_cat7 : Unitary (2 ^ 7))
    (hcol : ∀ m : Fin (2 ^ 7), U_cat7.1 m 0 = PhaseGradCatalystCore.phaseGradientState 7 m) :
    U_cat7.1.mulVec (Pi.single 0 1) = DyadicQft64.phaseGradKet 7 := by
  funext m
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (0 : Fin (2 ^ 7))]
  · rw [Pi.single_eq_same, mul_one, hcol m]
    unfold PhaseGradCatalystCore.phaseGradientState DyadicQft64.phaseGradKet
      PhaseGradCatalystCore.instHPowComplexRealCompat
    rfl
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro h0
    exact absurd (Finset.mem_univ (0 : Fin (2 ^ 7))) h0
theorem concat_blocks_eq_whole_local (k m : ℕ) :
    let rA : QRegister k (k + m) := QRegister.block 0 k (by omega)
    let rB : QRegister m (k + m) := QRegister.block k m le_rfl
    ∀ h : rA.DisjointWires rB, rA.concat rB h = QRegister.whole (k + m) := by
  intro rA rB h
  apply DyadicQft64WalkCircuit288Alt.qreg_ext; intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · rw [QRegister.concat_apply_left]; apply Fin.ext; simp [rA,
    DyadicQft64WalkCircuit288Alt.qreg_block_apply]
  · rw [QRegister.concat_apply_right]; apply Fin.ext; simp [rB,
    DyadicQft64WalkCircuit288Alt.qreg_block_apply]
theorem qft_act0_le : 0 + (3924 + 3) ≤ (3924 + 3) + 7 := by decide
theorem qft_disj0 : (QRegister.block 0 (3924 + 3) qft_act0_le).DisjointWires
    (QRegister.block (3924 + 3) 7 (le_refl ((3924 + 3) + 7))) :=
    QRegister.block_disjoint_of_le 0 (3924 + 3) (3924 + 3) 7 qft_act0_le le_rfl (by decide)
noncomputable def fullSysQft654Bundle288 : FullSysCatSegmentBridge.FullSysQft654Bundle :=
  FullSysCatSegmentBridge.FullSysQft654Bundle.ofIdeal654 288 qft64Ideal654Unitary
noncomputable def coreQftHadamardBundle288 : FullSysCatSegmentBridge.FullSysQft654Bundle :=
  FullSysCatSegmentBridge.FullSysQft654Bundle.ofIdeal654 288 coreQftHadamardStages288.uEff
@[simp]
theorem fullSysQft654Bundle288_mWorkQft : fullSysQft654Bundle288.mWorkQft = 288 := rfl
@[simp]
theorem coreQftHadamardBundle288_mWorkQft : coreQftHadamardBundle288.mWorkQft = 288 := rfl
@[simp] theorem fullSysQft654Bundle288_uQft654 :
    fullSysQft654Bundle288.uQft654 = qft64Ideal654Unitary := rfl
@[simp] theorem coreQftHadamardBundle288_uQft654 :
    coreQftHadamardBundle288.uQft654 = coreQftHadamardStages288.uEff := rfl
end ConfigDyadicQft64WalkCircuit288
set_option maxRecDepth 2000
end DyadicQft64WalkCircuit288
end
end ModDyadicQft64WalkCircuit288

section ModFullSysGuardWrapSpec
@[expose] public section
namespace FullSysGuardWrapSpec
open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open FullSysCatSegmentBridge
noncomputable def midEmbed (mPayload kMid : ℕ) (U : Unitary (2 ^ kMid)) :
    Unitary (2 ^ (fullSysBEWires mPayload + kMid)) :=
  (QRegister.block (fullSysBEWires mPayload) kMid le_rfl).embedUnitary U
end FullSysGuardWrapSpec
end
end ModFullSysGuardWrapSpec

section ModFullSysPosSlots24AndTopConcrete
@[expose] public section
namespace FullSysPosSlots24AndTopConcreteAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
end FullSysPosSlots24AndTopConcreteAlt
namespace FullSysPosSlots24AndTopConcrete
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open TwosCompAndWire0Cancel
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable def hadamardPayloadUnitary (m : ℕ) : Unitary (2 ^ m) :=
  (hadamardAll (QRegister.whole m)).eval
def hadamardPayloadDyn {Var : Type} {m n : ℕ} (rPayload : QRegister m n) : DynamicCircuit Var
    n := .circuit (hadamardAll rPayload)
@[simp] theorem count_hadamardPayloadDyn_t {Var : Type} {m n : ℕ} (rPayload : QRegister m n) :
    (hadamardPayloadDyn (Var := Var) rPayload).count .T = 0 := by
  simp [hadamardPayloadDyn]
@[simp]
theorem count_hadamardPayloadDyn_toff {Var : Type} {m n : ℕ} (rPayload : QRegister m n) :
    (hadamardPayloadDyn (Var := Var) rPayload).count .TOFF = 0 := by
  simp [hadamardPayloadDyn]
theorem onRegister_sequence {k n : ℕ} (placement : QRegister k n) (cs : List (Circuit k)) :
    Circuit.onRegister placement (Circuit.sequence cs) = Circuit.sequence
    (cs.map (Circuit.onRegister placement)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      exact congrArg (Circuit.seq (Circuit.onRegister placement c)) ih
theorem onRegister_hadamardAll_whole {m n : ℕ} (rPayload : QRegister m n) :
    Circuit.onRegister rPayload (hadamardAll (QRegister.whole m)) = hadamardAll rPayload := by
  unfold hadamardAll
  rw [onRegister_sequence, List.map_ofFn]
  refine congrArg Circuit.sequence (congrArg List.ofFn ?_)
  funext i
  exact congrArg (Circuit.gate PrimitiveGate.H)
    (FullSysPosSlots24AndTopConcreteAlt.qreg_ext fun _ ↦ rfl)
theorem hadamardAll_embed_eq_local {m n : ℕ} (rPayload : QRegister m n) :
    (hadamardAll rPayload).eval = rPayload.embedUnitary (hadamardPayloadUnitary m) := by
  rw [← onRegister_hadamardAll_whole rPayload, Circuit.eval_onRegister]
  rfl
theorem hadamardPayloadDyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {m k n : ℕ} [NeZero (2 ^ n)]
    (rPayload : QRegister m n) (rWork : QRegister k n) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rPayload rWork (hadamardPayloadUnitary m) (hadamardPayloadDyn (Var := Var) rPayload) :=
  DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
    rPayload rWork (hadamardPayloadUnitary m) (hadamardAll rPayload)
    (hadamardAll_embed_eq_local rPayload)
theorem smToTwosSys_mul_self_val : smToTwosSysUnitary.1 * smToTwosSysUnitary.1 = 1 := by
  rw [← Submonoid.coe_mul, smToTwosSysUnitary_mul_self, OneMemClass.coe_one]
theorem conj_comm_local {D : ℕ} (U H P : Operator D) (hUP : U * P = P * U)
    (hHP : H * P = P * H) : (U * H * U) * P = P * (U * H * U) := by
  rw [Matrix.mul_assoc (U * H), hUP, Matrix.mul_assoc U H, ← Matrix.mul_assoc H P, hHP,
    ← Matrix.mul_assoc U (P * H), ← Matrix.mul_assoc U P, hUP, Matrix.mul_assoc P U,
    Matrix.mul_assoc P (U * H)]
theorem conj_middle_swap_local {D : ℕ} (U D_op P : Operator D) (hUP : U * P = P * U) : P *
    (U * D_op * U) * P = U * (P * D_op * P) * U := by
  calc (P * (U * D_op * U)) * P
      = (P * U) * D_op * (U * P) := by noncomm_ring
    _ = (U * P) * D_op * (P * U) := congrArg₂ (· * ·) (congrArg (· * D_op) hUP.symm) hUP
    _ = U * (P * D_op * P) * U := by noncomm_ring
end FullSysPosSlots24AndTopConcrete
end
end ModFullSysPosSlots24AndTopConcrete

section ModFullSysFullPrepareAndTopConcrete
@[expose] public section
namespace FullSysFullPrepareAndTopConcrete
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open PosMomSelectDynamic
open FullSysPrepare6Slot
open FullSysPosSlots24AndTopConcrete
open scoped Matrix BigOperators Matrix.Norms.L2Operator
abbrev selWiresSym (mPayload : ℕ) : ℕ := 6 + mPayload
abbrev coreWiresSym (mPayload : ℕ) : ℕ := SpecsAux.SpecMirror.systemQubits + selWiresSym mPayload
abbrev selCoin3Sym (mPayload : ℕ) : QRegister 3 (selWiresSym mPayload) :=
  QRegister.block 0 3 (by dsimp [selWiresSym]; omega)
abbrev coreSysSym (mPayload : ℕ) : QRegister SpecsAux.SpecMirror.systemQubits (coreWiresSym
    mPayload) :=
  QRegister.block 0 SpecsAux.SpecMirror.systemQubits (by dsimp [coreWiresSym]; omega)
abbrev coreAncSym (mPayload : ℕ) : QRegister (selWiresSym mPayload) (coreWiresSym mPayload) :=
  QRegister.block SpecsAux.SpecMirror.systemQubits (selWiresSym mPayload) le_rfl
abbrev corePayloadSym (mPayload : ℕ) : QRegister mPayload (coreWiresSym mPayload) :=
  QRegister.block (SpecsAux.SpecMirror.systemQubits + 6) mPayload (by
    dsimp [coreWiresSym, selWiresSym]
    omega)
noncomputable def coreHadamardUnitary (mPayload : ℕ) : Unitary (2 ^ (coreWiresSym mPayload)) :=
  (hadamardAll (corePayloadSym mPayload)).eval
theorem coreHadamardUnitary_eq_embed (mPayload : ℕ) : coreHadamardUnitary mPayload =
    (corePayloadSym mPayload).embedUnitary (hadamardPayloadUnitary mPayload) :=
    hadamardAll_embed_eq_local (corePayloadSym mPayload)
@[simp] theorem coreHadamardUnitary_inv (mPayload : ℕ) : (coreHadamardUnitary mPayload)⁻¹ =
    coreHadamardUnitary mPayload := hadamardAll_eval_inv (corePayloadSym mPayload)
theorem unitaryConj_mul_outer {D : ℕ} (A B S : Unitary D) :
    unitaryConj (A * B) S = unitaryConj B (unitaryConj A S) := by
  unfold unitaryConj
  rw [_root_.mul_inv_rev]
  simp only [_root_.mul_assoc]
end FullSysFullPrepareAndTopConcrete
end
end ModFullSysFullPrepareAndTopConcrete

section ModFullSysMomSlots0135Concrete
@[expose] public section
namespace FullSysMomSlots0135ConcreteAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end FullSysMomSlots0135ConcreteAlt
namespace FullSysMomSlots0135Concrete
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open PosMomSelectSandwich
open PosMomSelectDynamic
open FullSysPrepare6Slot
open FullSysPosSlots24AndTopConcrete
open TwosCompAndWire0Cancel
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem mom_zero_add_le (a b : ℕ) : 0 + a ≤ a + b := by omega
theorem mom_zero_add_le_self (a : ℕ) : 0 + a ≤ a := by omega
abbrev momSelWires (mPayload : ℕ) : ℕ := 6 + mPayload
abbrev momCoreWires (mPayload : ℕ) : ℕ := SpecsAux.SpecMirror.systemQubits + momSelWires mPayload
abbrev momCoin3Sel (mPayload : ℕ) : QRegister 3 (momSelWires mPayload) :=
  QRegister.block 0 3 (by dsimp [momSelWires]; omega)
abbrev momSysReg (mPayload : ℕ) : QRegister SpecsAux.SpecMirror.systemQubits (momCoreWires mPayload)
    :=
  QRegister.block 0 SpecsAux.SpecMirror.systemQubits (by dsimp [momCoreWires]; omega)
abbrev momAncReg (mPayload : ℕ) : QRegister (momSelWires mPayload) (momCoreWires mPayload) :=
  QRegister.block SpecsAux.SpecMirror.systemQubits (momSelWires mPayload) le_rfl
abbrev momCoinReg (mPayload : ℕ) : QRegister 3 (momCoreWires mPayload) :=
  QRegister.block 3948 3 (by
    dsimp [momCoreWires, momSelWires, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega)
abbrev momPayloadReg (mPayload : ℕ) : QRegister mPayload (momCoreWires mPayload) :=
  QRegister.block (SpecsAux.SpecMirror.systemQubits + 6) mPayload (by
    dsimp [momCoreWires, momSelWires]
    omega)
abbrev iSlot0Mom (mPayload : ℕ) : Wire (momCoreWires mPayload) :=
  ⟨3948, by
    dsimp [momCoreWires, momSelWires, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega⟩
abbrev iSlot1Mom (mPayload : ℕ) : Wire (momCoreWires mPayload) :=
  ⟨3949, by
    simp [momCoreWires, momSelWires, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega⟩
abbrev iSlot2Mom (mPayload : ℕ) : Wire (momCoreWires mPayload) :=
  ⟨3950, by
    simp [momCoreWires, momSelWires, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega⟩
noncomputable abbrev coreHadamardMom (mPayload : ℕ) : Unitary (2 ^ (momCoreWires mPayload)) :=
  (hadamardAll (momPayloadReg mPayload)).eval
abbrev IntertwinesMomCat {kAct mCat : ℕ} (U_cat : Unitary (2 ^ mCat))
    (W_cat : Unitary (2 ^ (kAct + mCat))) (U_eff : Unitary (2 ^ kAct)) : Prop :=
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (mom_zero_add_le kAct mCat)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  IntertwinesCat
    (rCat0.embedUnitary U_cat).1
    (rCat0.basisOutcomeProjector 0)
    W_cat.1
    (rAct0.embedUnitary U_eff).1
theorem intertwinesMomCat_of_coreOnly {kAct mCat : ℕ} (U_cat : Unitary (2 ^ mCat))
    (U_eff : Unitary (2 ^ kAct)) : IntertwinesMomCat U_cat ((QRegister.block 0 kAct
    (mom_zero_add_le kAct mCat)).embedUnitary U_eff) U_eff := by
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (mom_zero_add_le kAct mCat)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  have hdisj : rAct0.DisjointWires rCat0 := QRegister.block_disjoint_of_le 0 kAct kAct mCat
      (mom_zero_add_le kAct mCat) le_rfl (mom_zero_add_le_self kAct)
  exact intertwinesCat_of_disjoint rAct0 rCat0 hdisj U_cat U_eff.1
theorem IntertwinesMomCat.mul {kAct mCat : ℕ} {U_cat : Unitary (2 ^ mCat)}
    {A_cat B_cat : Unitary (2 ^ (kAct + mCat))} {A_eff B_eff : Unitary (2 ^ kAct)}
    (hA : IntertwinesMomCat U_cat A_cat A_eff) (hB : IntertwinesMomCat U_cat B_cat B_eff) :
    IntertwinesMomCat U_cat (A_cat * B_cat) (A_eff * B_eff) := by
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (mom_zero_add_le kAct mCat)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  change IntertwinesCat (rCat0.embedUnitary U_cat).1 (rCat0.basisOutcomeProjector 0)
    (A_cat.1 * B_cat.1) (rAct0.embedUnitary (A_eff * B_eff)).1
  rw [rAct0.embedUnitary_mul]
  exact IntertwinesCat.mul hA hB
def coinBitFin2 (c : Fin 8) (j : Fin 3) : Fin 2 := ⟨(basisBits 3 c j).val, ZMod.val_lt _⟩
noncomputable def momCoinProj (mPayload : ℕ) (c : Fin 8) : Operator
    (2 ^ (momCoreWires mPayload)) := slotBitProj (iSlot0Mom mPayload) (coinBitFin2 c 0) *
    slotBitProj (iSlot1Mom mPayload) (coinBitFin2 c 1) * slotBitProj (iSlot2Mom mPayload)
    (coinBitFin2 c 2)
noncomputable def slot45MomProj (mPayload : ℕ) : Operator (2 ^ (momCoreWires mPayload)) :=
  slotBitProj (iSlot2Mom mPayload) 1 * slotBitProj (iSlot1Mom mPayload) 0
noncomputable def slot67MomProj (mPayload : ℕ) : Operator (2 ^ (momCoreWires mPayload)) :=
  slotBitProj (iSlot2Mom mPayload) 1 * slotBitProj (iSlot1Mom mPayload) 1
theorem slotBitProj_self_adj {k : ℕ} (w : Wire k) (b : Fin 2) :
    (slotBitProj w b)ᴴ = slotBitProj w b := by
  ext x y
  by_cases hxy : x = y
  · subst hxy; simp [slotBitProj]
  · simp [slotBitProj, hxy, Ne.symm hxy]
theorem slotBitProj_comm_any {k : ℕ} (w₁ w₂ : Wire k) (b₁ b₂ : Fin 2) :
    slotBitProj w₁ b₁ * slotBitProj w₂ b₂ = slotBitProj w₂ b₂ * slotBitProj w₁ b₁ := by
  simp only [slotBitProj, Matrix.diagonal_mul_diagonal, mul_comm]
theorem slotBitProj_zero_mul_one_eq_zero {k : ℕ} (w : Wire k) :
    slotBitProj w 0 * slotBitProj w 1 = (0 : Operator (2 ^ k)) := by
  ext x y
  rw [slotBitProj, slotBitProj, Matrix.diagonal_mul_diagonal]
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.diagonal_apply_eq, Matrix.zero_apply]
    split_ifs with h0 h1
    · exact absurd (h0.symm.trans h1) (by decide)
    · exact mul_zero _
    · exact zero_mul _
    · exact zero_mul _
  · rw [Matrix.diagonal_apply_ne _ hxy, Matrix.zero_apply]
theorem slotBitProj_one_mul_zero_eq_zero {k : ℕ} (w : Wire k) :
    slotBitProj w 1 * slotBitProj w 0 = (0 : Operator (2 ^ k)) := by
  rw [slotBitProj_comm_any, slotBitProj_zero_mul_one_eq_zero]
theorem slotBitProj_ne_mul_eq_zero {k : ℕ} (w : Wire k) {b₁ b₂ : Fin 2} (hne : b₁ ≠ b₂) :
    slotBitProj w b₁ * slotBitProj w b₂ = (0 : Operator (2 ^ k)) := by
  fin_cases b₁ <;> fin_cases b₂
  · exact absurd rfl hne
  · exact slotBitProj_zero_mul_one_eq_zero w
  · exact slotBitProj_one_mul_zero_eq_zero w
  · exact absurd rfl hne
theorem slotBitProj_mul_idem {k : ℕ} (w : Wire k) (b : Fin 2) :
    slotBitProj w b * slotBitProj w b = slotBitProj w b := by
  rw [slotBitProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> ring
theorem momCoinProj_eq_diagonal (mPayload : ℕ) (c : Fin 8) : momCoinProj mPayload c =
    Matrix.diagonal (fun x ↦ (if (basisBits (momCoreWires mPayload) x (iSlot0Mom
    mPayload)).val = (coinBitFin2 c 0).val then (1 : ℂ) else 0) * (if (basisBits (momCoreWires
    mPayload) x (iSlot1Mom mPayload)).val = (coinBitFin2 c 1).val then (1 : ℂ) else 0) * (if
    (basisBits (momCoreWires mPayload) x (iSlot2Mom mPayload)).val = (coinBitFin2 c 2).val
    then (1 : ℂ) else 0)) := by
  simp only [momCoinProj, slotBitProj, Matrix.diagonal_mul_diagonal]
theorem triple_mul_triple_comm {D : ℕ} (A₀ A₁ A₂ B₀ B₁ B₂ : Operator D)
    (h₂₀ : A₂ * B₀ = B₀ * A₂) (h₁₀ : A₁ * B₀ = B₀ * A₁) (h₂₁ : A₂ * B₁ = B₁ * A₂) :
    (A₀ * A₁ * A₂) * (B₀ * B₁ * B₂) = (A₀ * B₀) * (A₁ * B₁) * (A₂ * B₂) := by
  calc (A₀ * A₁ * A₂) * (B₀ * B₁ * B₂)
      = A₀ * A₁ * (A₂ * B₀) * B₁ * B₂ := by simp only [Matrix.mul_assoc]
    _ = A₀ * (A₁ * B₀) * (A₂ * B₁) * B₂ := by rw [h₂₀]; simp only [Matrix.mul_assoc]
    _ = (A₀ * B₀) * (A₁ * B₁) * (A₂ * B₂) := by rw [h₁₀, h₂₁]; simp only [Matrix.mul_assoc]
theorem pair_mul_triple_comm {D : ℕ} (A₂ A₁ B₀ B₁ B₂ : Operator D) (h₂₁_a : A₂ * A₁ = A₁ * A₂)
    (h₁₀ : A₁ * B₀ = B₀ * A₁) (h₂₀ : A₂ * B₀ = B₀ * A₂) (h₂₁ : A₂ * B₁ = B₁ * A₂) : (A₂ * A₁)
    * (B₀ * B₁ * B₂) = B₀ * (A₁ * B₁) * (A₂ * B₂) := by
  calc (A₂ * A₁) * (B₀ * B₁ * B₂)
      = (1 * A₁ * A₂) * (B₀ * B₁ * B₂) := by rw [h₂₁_a, Matrix.one_mul]
    _ = (1 * B₀) * (A₁ * B₁) * (A₂ * B₂) := triple_mul_triple_comm 1 A₁ A₂ B₀ B₁ B₂ h₂₀ h₁₀ h₂₁
    _ = B₀ * (A₁ * B₁) * (A₂ * B₂) := by rw [Matrix.one_mul]
theorem momCoinProj_conjTranspose (mPayload : ℕ) (c : Fin 8) :
    (momCoinProj mPayload c)ᴴ = momCoinProj mPayload c := by
  unfold momCoinProj
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    slotBitProj_self_adj, slotBitProj_self_adj, slotBitProj_self_adj,
    slotBitProj_comm_any (iSlot1Mom mPayload) (iSlot0Mom mPayload),
    ← Matrix.mul_assoc (slotBitProj (iSlot2Mom mPayload) _),
    slotBitProj_comm_any (iSlot2Mom mPayload) (iSlot0Mom mPayload),
    Matrix.mul_assoc (slotBitProj (iSlot0Mom mPayload) _),
    slotBitProj_comm_any (iSlot2Mom mPayload) (iSlot1Mom mPayload),
    ← Matrix.mul_assoc (slotBitProj (iSlot0Mom mPayload) _)]
theorem exists_coinBitFin2_ne_of_ne {c₁ c₂ : Fin 8} (h : c₁ ≠ c₂) : coinBitFin2 c₁ 0 ≠
    coinBitFin2 c₂ 0 ∨ coinBitFin2 c₁ 1 ≠ coinBitFin2 c₂ 1 ∨ coinBitFin2 c₁ 2 ≠ coinBitFin2 c₂
    2 := by
  revert h
  fin_cases c₁ <;> fin_cases c₂ <;> decide
theorem momCoinProj_mul_of_ne (mPayload : ℕ) {c₁ c₂ : Fin 8} (hne : c₁ ≠ c₂) :
    momCoinProj mPayload c₁ * momCoinProj mPayload c₂ = 0 := by
  rw [momCoinProj, momCoinProj,
    triple_mul_triple_comm _ _ _ _ _ _
      (slotBitProj_comm_any _ _ _ _) (slotBitProj_comm_any _ _ _ _) (slotBitProj_comm_any _ _ _ _)]
  rcases exists_coinBitFin2_ne_of_ne hne with h0 | h1 | h2
  · rw [slotBitProj_ne_mul_eq_zero _ h0, Matrix.zero_mul, Matrix.zero_mul]
  · rw [slotBitProj_ne_mul_eq_zero _ h1, Matrix.mul_zero, Matrix.zero_mul]
  · rw [slotBitProj_ne_mul_eq_zero _ h2, Matrix.mul_zero]
theorem slot45MomProj_mul_slot67MomProj (mPayload : ℕ) :
    slot45MomProj mPayload * slot67MomProj mPayload = 0 := by
  rw [slot45MomProj, slot67MomProj, Matrix.mul_assoc _ (slotBitProj (iSlot1Mom mPayload) 0),
    ← Matrix.mul_assoc (slotBitProj (iSlot1Mom mPayload) 0),
    slotBitProj_comm_any (iSlot1Mom mPayload) (iSlot2Mom mPayload),
    Matrix.mul_assoc (slotBitProj (iSlot2Mom mPayload) 1) (slotBitProj (iSlot1Mom mPayload) 0),
    slotBitProj_zero_mul_one_eq_zero, Matrix.mul_zero, Matrix.mul_zero]
theorem slot67MomProj_mul_slot45MomProj (mPayload : ℕ) :
    slot67MomProj mPayload * slot45MomProj mPayload = 0 := by
  rw [slot67MomProj, slot45MomProj, Matrix.mul_assoc _ (slotBitProj (iSlot1Mom mPayload) 1),
    ← Matrix.mul_assoc (slotBitProj (iSlot1Mom mPayload) 1),
    slotBitProj_comm_any (iSlot1Mom mPayload) (iSlot2Mom mPayload),
    Matrix.mul_assoc (slotBitProj (iSlot2Mom mPayload) 1) (slotBitProj (iSlot1Mom mPayload) 1),
    slotBitProj_one_mul_zero_eq_zero, Matrix.mul_zero, Matrix.mul_zero]
theorem slot45MomProj_mul_iSlot2_zero (mPayload : ℕ) :
    slot45MomProj mPayload * slotBitProj (iSlot2Mom mPayload) 0 = 0 := by
  rw [slot45MomProj, Matrix.mul_assoc,
    slotBitProj_comm_any (iSlot1Mom mPayload) (iSlot2Mom mPayload),
    ← Matrix.mul_assoc, slotBitProj_one_mul_zero_eq_zero, Matrix.zero_mul]
theorem slot67MomProj_mul_iSlot2_zero (mPayload : ℕ) :
    slot67MomProj mPayload * slotBitProj (iSlot2Mom mPayload) 0 = 0 := by
  rw [slot67MomProj, Matrix.mul_assoc,
    slotBitProj_comm_any (iSlot1Mom mPayload) (iSlot2Mom mPayload),
    ← Matrix.mul_assoc, slotBitProj_one_mul_zero_eq_zero, Matrix.zero_mul]
theorem slot45MomProj_mul_momCoinProj (mPayload : ℕ) {c : Fin 8}
    (hc2 : coinBitFin2 c 2 = 1) (hc1 : coinBitFin2 c 1 = 0) :
    slot45MomProj mPayload * momCoinProj mPayload c = momCoinProj mPayload c := by
  rw [slot45MomProj, momCoinProj, hc2, hc1,
    pair_mul_triple_comm _ _ _ _ _
      (slotBitProj_comm_any _ _ _ _)
      (slotBitProj_comm_any _ _ _ _) (slotBitProj_comm_any _ _ _ _) (slotBitProj_comm_any _ _ _ _),
    slotBitProj_mul_idem, slotBitProj_mul_idem]
theorem slot67MomProj_mul_momCoinProj (mPayload : ℕ) {c : Fin 8}
    (hc2 : coinBitFin2 c 2 = 1) (hc1 : coinBitFin2 c 1 = 1) :
    slot67MomProj mPayload * momCoinProj mPayload c = momCoinProj mPayload c := by
  rw [slot67MomProj, momCoinProj, hc2, hc1,
    pair_mul_triple_comm _ _ _ _ _
      (slotBitProj_comm_any _ _ _ _)
      (slotBitProj_comm_any _ _ _ _) (slotBitProj_comm_any _ _ _ _) (slotBitProj_comm_any _ _ _ _),
    slotBitProj_mul_idem, slotBitProj_mul_idem]
theorem slotBitProj_zero_add_one_local {k : ℕ} (w : Wire k) :
    slotBitProj w 0 + slotBitProj w 1 = (1 : Operator (2 ^ k)) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp only [slotBitProj, Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have hlt : (basisBits k x w).val < 2 := ZMod.val_lt _
    rcases (by omega : (basisBits k x w).val = 0 ∨ (basisBits k x w).val = 1) with hv | hv
    · simp [hv]
    · simp [hv]
  · simp [slotBitProj, hxy]
theorem momCoinProj_4_add_5_eq_slot45 (mPayload : ℕ) :
    momCoinProj mPayload 4 + momCoinProj mPayload 5 = slot45MomProj mPayload := by
  have hc : coinBitFin2 4 0 = 0 ∧ coinBitFin2 4 1 = 0 ∧ coinBitFin2 4 2 = 1 ∧
      coinBitFin2 5 0 = 1 ∧ coinBitFin2 5 1 = 0 ∧ coinBitFin2 5 2 = 1 := by decide
  rw [momCoinProj, momCoinProj, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2,
    slot45MomProj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.add_mul,
    slotBitProj_zero_add_one_local, Matrix.one_mul, slotBitProj_comm_any]
theorem momCoinProj_6_add_7_eq_slot67 (mPayload : ℕ) :
    momCoinProj mPayload 6 + momCoinProj mPayload 7 = slot67MomProj mPayload := by
  have hc : coinBitFin2 6 0 = 0 ∧ coinBitFin2 6 1 = 1 ∧ coinBitFin2 6 2 = 1 ∧
      coinBitFin2 7 0 = 1 ∧ coinBitFin2 7 1 = 1 ∧ coinBitFin2 7 2 = 1 := by decide
  rw [momCoinProj, momCoinProj, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2,
    slot67MomProj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.add_mul,
    slotBitProj_zero_add_one_local, Matrix.one_mul, slotBitProj_comm_any]
theorem wire_lt_3954_not_mem_momPayload {mPayload : ℕ} {w : Wire (momCoreWires mPayload)}
    (hw : w.val < 3954) : w ∉ Set.range (momPayloadReg mPayload).wires := by
  rintro ⟨idx, hEq⟩
  have hv := congrArg Fin.val hEq
  dsimp [momPayloadReg, FullSysMomSlots0135ConcreteAlt.qreg_block_apply,
    FullSysMomSlots0135ConcreteAlt.qreg_block_wires_apply,
    FullSysMomSlots0135ConcreteAlt.qreg_whole_wires,
    FullSysMomSlots0135ConcreteAlt.emb_trans_apply,
    FullSysMomSlots0135ConcreteAlt.emb_refl_apply,
    FullSysMomSlots0135ConcreteAlt.emb_mk_apply, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hv
  omega
theorem coreHadamardMom_comm_slotBitProj {mPayload : ℕ} {w : Wire (momCoreWires mPayload)}
    (hw : w.val < 3954) (b : Fin 2) : (coreHadamardMom mPayload).1 * slotBitProj w b =
    slotBitProj w b * (coreHadamardMom mPayload).1 := by
  have hwOut := wire_lt_3954_not_mem_momPayload hw
  have hemb : coreHadamardMom mPayload = (momPayloadReg mPayload).embedUnitary
      (hadamardPayloadUnitary mPayload) := hadamardAll_embed_eq_local (momPayloadReg mPayload)
  rw [hemb, QRegister.embedUnitary_val, slotBitProj]
  refine embedMatrix_comm_diagonal_of_outside (momPayloadReg mPayload)
    (hadamardPayloadUnitary mPayload).1 _ (fun i j hOut ↦ ?_)
  rw [hOut w hwOut]
theorem op_comm_triple {D : ℕ} (H P₀ P₁ P₂ : Operator D)
    (h₀ : H * P₀ = P₀ * H) (h₁ : H * P₁ = P₁ * H) (h₂ : H * P₂ = P₂ * H) :
    H * (P₀ * P₁ * P₂) = (P₀ * P₁ * P₂) * H := by
  calc H * (P₀ * P₁ * P₂)
      = (H * P₀) * P₁ * P₂ := by simp only [Matrix.mul_assoc]
    _ = P₀ * (H * P₁) * P₂ := by rw [h₀]; simp only [Matrix.mul_assoc]
    _ = P₀ * P₁ * (H * P₂) := by rw [h₁]; simp only [Matrix.mul_assoc]
    _ = (P₀ * P₁ * P₂) * H := by rw [h₂]; simp only [Matrix.mul_assoc]
theorem coreHadamardMom_comm_momCoinProj (mPayload : ℕ) (c : Fin 8) :
    (coreHadamardMom mPayload).1 * momCoinProj mPayload c =
      momCoinProj mPayload c * (coreHadamardMom mPayload).1 := by
  rw [momCoinProj]
  exact op_comm_triple _ _ _ _
    (coreHadamardMom_comm_slotBitProj (by dsimp [iSlot0Mom]; omega) (coinBitFin2 c 0))
    (coreHadamardMom_comm_slotBitProj (by dsimp [iSlot1Mom]; omega) (coinBitFin2 c 1))
    (coreHadamardMom_comm_slotBitProj (by dsimp [iSlot2Mom]; omega) (coinBitFin2 c 2))
theorem momCoinProj_mul_ancOutcomeProj (mPayload : ℕ) (c : Fin 8) : momCoinProj mPayload c *
    (momAncReg mPayload).basisOutcomeProjector (coinSelOutcome (momCoin3Sel mPayload) c) =
    (momAncReg mPayload).basisOutcomeProjector (coinSelOutcome (momCoin3Sel mPayload) c) := by
  rw [momCoinProj_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  by_cases hx : (momAncReg mPayload).extractIndex x = coinSelOutcome (momCoin3Sel mPayload) c
  · have hv (j : Fin 3) (w : Wire (momCoreWires mPayload)) (hwj : w.val = 3948 + j.val) :
        (basisBits (momCoreWires mPayload) x w).val = (coinBitFin2 c j).val := by
      have hw : (momAncReg mPayload) (momCoin3Sel mPayload j) = w := Fin.ext (by
        rw [hwj]
        dsimp [momAncReg, momCoin3Sel, FullSysMomSlots0135ConcreteAlt.qreg_block_apply,
          FullSysMomSlots0135ConcreteAlt.qreg_block_wires_apply,
          FullSysMomSlots0135ConcreteAlt.qreg_whole_wires,
          FullSysMomSlots0135ConcreteAlt.emb_trans_apply,
          FullSysMomSlots0135ConcreteAlt.emb_refl_apply,
          FullSysMomSlots0135ConcreteAlt.emb_mk_apply, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega)
      rw [← hw, ← (momAncReg mPayload).basisBits_extractIndex x (momCoin3Sel mPayload j),
        hx, basisBits_coinSelOutcome_coin]
      rfl
    simp [hx, hv 0 (iSlot0Mom mPayload) rfl, hv 1 (iSlot1Mom mPayload) rfl,
      hv 2 (iSlot2Mom mPayload) rfl]
  · simp [hx]
theorem ancOutcomeProj_mul_momCoinProj (mPayload : ℕ) (c : Fin 8) :
    (momAncReg mPayload).basisOutcomeProjector (coinSelOutcome (momCoin3Sel mPayload) c) *
        momCoinProj mPayload c =
      (momAncReg mPayload).basisOutcomeProjector (coinSelOutcome (momCoin3Sel mPayload) c) := by
  have h := congrArg Matrix.conjTranspose (momCoinProj_mul_ancOutcomeProj mPayload c)
  simpa only [Matrix.conjTranspose_mul, momCoinProj_conjTranspose,
    QRegister.basisOutcomeProjector_conjTranspose] using h
theorem conjHadamard_branch_topBlock_of_eq_on_coin {mPayload : ℕ} (c : Fin 8)
    (U_all U_slot : Unitary (2 ^ (momCoreWires mPayload)))
    (hOnCoin : U_all.1 * momCoinProj mPayload c = U_slot.1 * momCoinProj mPayload c) :
    let P_anc := (momAncReg mPayload).basisOutcomeProjector
      (coinSelOutcome (momCoin3Sel mPayload) c)
    P_anc * (unitaryConj (coreHadamardMom mPayload) U_all).1 * P_anc =
      P_anc * (unitaryConj (coreHadamardMom mPayload) U_slot).1 * P_anc := by
  intro P_anc
  have hComm : (coreHadamardMom mPayload).1 * momCoinProj mPayload c = momCoinProj mPayload c
      * (coreHadamardMom mPayload).1 := coreHadamardMom_comm_momCoinProj mPayload c
  have hAbs : momCoinProj mPayload c * P_anc = P_anc := momCoinProj_mul_ancOutcomeProj mPayload c
  calc P_anc * (unitaryConj (coreHadamardMom mPayload) U_all).1 * P_anc
      = P_anc * (coreHadamardMom mPayload).1ᴴ *
          (U_all.1 * ((coreHadamardMom mPayload).1 * (momCoinProj mPayload c * P_anc))) := by
            rw [hAbs, unitaryConj_val]
            simp only [Matrix.mul_assoc]
    _ = P_anc * (coreHadamardMom mPayload).1ᴴ *
          ((U_all.1 * momCoinProj mPayload c) * (coreHadamardMom mPayload).1 * P_anc) := by
            rw [← Matrix.mul_assoc (coreHadamardMom mPayload).1, hComm]
            simp only [Matrix.mul_assoc]
    _ = P_anc * (coreHadamardMom mPayload).1ᴴ *
          ((U_slot.1 * momCoinProj mPayload c) * (coreHadamardMom mPayload).1 * P_anc) := by
            rw [hOnCoin]
    _ = P_anc * (coreHadamardMom mPayload).1ᴴ *
          (U_slot.1 * ((coreHadamardMom mPayload).1 * (momCoinProj mPayload c * P_anc))) := by
            rw [Matrix.mul_assoc U_slot.1 (momCoinProj mPayload c) (coreHadamardMom mPayload).1,
              ← hComm]
            simp only [Matrix.mul_assoc]
    _ = P_anc * (unitaryConj (coreHadamardMom mPayload) U_slot).1 * P_anc := by
          rw [hAbs, unitaryConj_val]
          simp only [Matrix.mul_assoc]
theorem offProj_left_of_sa_and_right {D : ℕ} {P : Operator D} {U : Unitary D} (hP_sa : Pᴴ = P)
    (hU_sa : U.1ᴴ = U.1) (hRight : U.1 * (1 - P) = 1 - P) : (1 - P) * U.1 = 1 - P := by
  have h := congrArg Matrix.conjTranspose hRight
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    hP_sa, hU_sa] using h
theorem unitaryConj_sa_and_offProj {D : ℕ} {P : Operator D} (U_prep M_ctrl : Unitary D)
    (hPrepComm : U_prep.1 * P = P * U_prep.1) (hCoreSA : M_ctrl.1ᴴ = M_ctrl.1)
    (hCoreOff : M_ctrl.1 * (1 - P) = 1 - P) : (unitaryConj U_prep M_ctrl).1ᴴ =
    (unitaryConj U_prep M_ctrl).1 ∧ (unitaryConj U_prep M_ctrl).1 * (1 - P) = 1 - P := by
  refine ⟨unitaryConj_conjTranspose hCoreSA, ?_⟩
  have hCommCompl : U_prep.1 * (1 - P) = (1 - P) * U_prep.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hPrepComm]
  have hInv : U_prep.1ᴴ * U_prep.1 = 1 := congrArg Subtype.val (inv_mul_cancel U_prep)
  calc (unitaryConj U_prep M_ctrl).1 * (1 - P)
      = U_prep.1ᴴ * (M_ctrl.1 * (U_prep.1 * (1 - P))) := by
          rw [unitaryConj_val]; simp only [Matrix.mul_assoc]
    _ = U_prep.1ᴴ * ((M_ctrl.1 * (1 - P)) * U_prep.1) := by
          rw [hCommCompl, Matrix.mul_assoc]
    _ = (U_prep.1ᴴ * U_prep.1) * (1 - P) := by
          rw [hCoreOff, ← hCommCompl, Matrix.mul_assoc]
    _ = 1 - P := by rw [hInv, Matrix.one_mul]
structure MomSingleSlotOracle (mPayload mPGTwist : ℕ) (k : Fin 6) where
  mWork : ℕ
  wSlot : SpecsAux.SpecMirror.Configuration → ℝ
  eShift : SpecsAux.SpecMirror.Configuration → ℝ
  epsIntr : ℝ
  uSlotCat : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (momCoreWires mPayload + mPGTwist))
  uSlotEff : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (momCoreWires mPayload))
  bUnitTwos : SpecsAux.SpecMirror.Configuration → Operator (2 ^ SpecsAux.SpecMirror.systemQubits)
  hWNonneg : ∀ cfg, 0 ≤ wSlot cfg
  hIntertwines : ∀ cfg (U_catTwist : Unitary (2 ^ mPGTwist)),
    (∀ m : Fin (2 ^ mPGTwist),
      U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState mPGTwist m) →
    IntertwinesMomCat U_catTwist (uSlotCat cfg) (uSlotEff cfg)
  hSA : ∀ cfg, (uSlotEff cfg).1ᴴ = (uSlotEff cfg).1
  hOffCoin : ∀ cfg,
    (uSlotEff cfg).1 * (1 - momCoinProj mPayload (fullSysCoinIdx k)) =
      1 - momCoinProj mPayload (fullSysCoinIdx k)
  hTopBlock : ∀ cfg,
    let c := fullSysCoinIdx k
    let P_anc := (momAncReg mPayload).basisOutcomeProjector
      (coinSelOutcome (momCoin3Sel mPayload) c)
    P_anc * (unitaryConj (coreHadamardMom mPayload) (uSlotEff cfg)).1 * P_anc =
      P_anc * (momSysReg mPayload).embedMatrix (bUnitTwos cfg) * P_anc
  hUnitNorm : ∀ cfg, ‖bUnitTwos cfg‖ ≤ 1
  hPermSm : ∀ cfg (g : Equiv.Perm (Fin numElectrons))
    (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)),
    IsGridState x → IsGridState y →
      (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1)
        (permElectron g x) (permElectron g y) =
      (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) x y
  hErrIntrSm : ∀ cfg (spinUp : Finset (Fin numElectrons)),
    let E_vec : Fin 6 → ℝ := fun j ↦ if j = k then eShift cfg else 0
    ‖fermionicProjector spinUp *
      ((wSlot cfg : ℂ) • (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) -
        sixChannelShifted cfg E_vec k) *
      fermionicProjector spinUp‖ ≤ epsIntr
noncomputable def MomSingleSlotOracle.ofCoreOnly {mPayload mPGTwist : ℕ} {k : Fin 6}
    (mWork : ℕ)
    (wSlot eShift : SpecsAux.SpecMirror.Configuration → ℝ)
    (epsIntr : ℝ)
    (uSlotEff : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (momCoreWires mPayload)))
    (bUnitTwos : SpecsAux.SpecMirror.Configuration →
      Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hWNonneg : ∀ cfg, 0 ≤ wSlot cfg)
    (hSA : ∀ cfg, (uSlotEff cfg).1ᴴ = (uSlotEff cfg).1)
    (hOffCoin : ∀ cfg,
      (uSlotEff cfg).1 * (1 - momCoinProj mPayload (fullSysCoinIdx k)) =
        1 - momCoinProj mPayload (fullSysCoinIdx k))
    (hTopBlock : ∀ cfg,
      let c := fullSysCoinIdx k
      let P_anc := (momAncReg mPayload).basisOutcomeProjector
        (coinSelOutcome (momCoin3Sel mPayload) c)
      P_anc * (unitaryConj (coreHadamardMom mPayload) (uSlotEff cfg)).1 * P_anc =
        P_anc * (momSysReg mPayload).embedMatrix (bUnitTwos cfg) * P_anc)
    (hUnitNorm : ∀ cfg, ‖bUnitTwos cfg‖ ≤ 1)
    (hPermSm : ∀ cfg (g : Equiv.Perm (Fin numElectrons))
      (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)),
      IsGridState x → IsGridState y →
        (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1)
          (permElectron g x) (permElectron g y) =
        (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) x y)
    (hErrIntrSm : ∀ cfg (spinUp : Finset (Fin numElectrons)),
      let E_vec : Fin 6 → ℝ := fun j ↦ if j = k then eShift cfg else 0
      ‖fermionicProjector spinUp *
        ((wSlot cfg : ℂ) • (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) -
          sixChannelShifted cfg E_vec k) *
        fermionicProjector spinUp‖ ≤ epsIntr) :
    MomSingleSlotOracle mPayload mPGTwist k where
  mWork := mWork
  wSlot := wSlot
  eShift := eShift
  epsIntr := epsIntr
  uSlotCat := fun cfg ↦
    (QRegister.block 0 (momCoreWires mPayload)
      (mom_zero_add_le (momCoreWires mPayload) mPGTwist)).embedUnitary (uSlotEff cfg)
  uSlotEff := uSlotEff
  bUnitTwos := bUnitTwos
  hWNonneg := hWNonneg
  hIntertwines := fun cfg U_cat _ ↦ intertwinesMomCat_of_coreOnly U_cat (uSlotEff cfg)
  hSA := hSA
  hOffCoin := hOffCoin
  hTopBlock := hTopBlock
  hUnitNorm := hUnitNorm
  hPermSm := hPermSm
  hErrIntrSm := hErrIntrSm

structure MomSingleSlotCircuit (mPayload mPGTwist : ℕ) (k : Fin 6)
    extends MomSingleSlotOracle mPayload mPGTwist k where
  tSlot : ℕ
  dSlot : SpecsAux.SpecMirror.Configuration → ∀ {Var : Type} {n : ℕ},
    Var →
    (rCore : QRegister (momCoreWires mPayload) n) →
    (rPGTwist : QRegister mPGTwist n) →
    (rWork : QRegister mWork n) →
    rCore.DisjointWires rPGTwist →
    rCore.DisjointWires rWork →
    rPGTwist.DisjointWires rWork →
    DynamicCircuit Var n
  hToff : ∀ cfg {Var : Type} {n : ℕ} (v : Var)
    (rC : QRegister (momCoreWires mPayload) n) (rP : QRegister mPGTwist n)
    (rW : QRegister mWork n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rW) (hPW : rP.DisjointWires rW),
    (dSlot cfg v rC rP rW hCP hCW hPW).count PrimitiveGate.TOFF = 0
  hT : ∀ cfg {Var : Type} {n : ℕ} (v : Var)
    (rC : QRegister (momCoreWires mPayload) n) (rP : QRegister mPGTwist n)
    (rW : QRegister mWork n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rW) (hPW : rP.DisjointWires rW),
    (dSlot cfg v rC rP rW hCP hCW hPW).count PrimitiveGate.T ≤ tSlot
  hReal : ∀ cfg {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rC : QRegister (momCoreWires mPayload) n) (rP : QRegister mPGTwist n)
    (rW : QRegister mWork n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rW) (hPW : rP.DisjointWires rW),
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rC.concat rP hCP) rW (uSlotCat cfg) (dSlot cfg v rC rP rW hCP hCW hPW)

noncomputable def MomSingleSlotCircuit.ofCoreOnly {mPayload mPGTwist : ℕ} {k : Fin 6}
    (mWork tSlot : ℕ)
    (wSlot eShift : SpecsAux.SpecMirror.Configuration → ℝ)
    (epsIntr : ℝ)
    (uSlotEff : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (momCoreWires mPayload)))
    (bUnitTwos : SpecsAux.SpecMirror.Configuration →
      Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (dCore : SpecsAux.SpecMirror.Configuration → ∀ {Var : Type} {n : ℕ},
      Var →
      (rCore : QRegister (momCoreWires mPayload) n) →
      (rWork : QRegister mWork n) →
      rCore.DisjointWires rWork →
      DynamicCircuit Var n)
    (hWNonneg : ∀ cfg, 0 ≤ wSlot cfg)
    (hToff : ∀ cfg {Var : Type} {n : ℕ} (v : Var)
      (rC : QRegister (momCoreWires mPayload) n) (rW : QRegister mWork n)
      (hCW : rC.DisjointWires rW),
      (dCore cfg v rC rW hCW).count PrimitiveGate.TOFF = 0)
    (hT : ∀ cfg {Var : Type} {n : ℕ} (v : Var)
      (rC : QRegister (momCoreWires mPayload) n) (rW : QRegister mWork n)
      (hCW : rC.DisjointWires rW),
      (dCore cfg v rC rW hCW).count PrimitiveGate.T ≤ tSlot)
    (hRealCore : ∀ cfg {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
      (v : Var) (rC : QRegister (momCoreWires mPayload) n) (rW : QRegister mWork n)
      (hCW : rC.DisjointWires rW),
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        rC rW (uSlotEff cfg) (dCore cfg v rC rW hCW))
    (hSA : ∀ cfg, (uSlotEff cfg).1ᴴ = (uSlotEff cfg).1)
    (hOffCoin : ∀ cfg,
      (uSlotEff cfg).1 * (1 - momCoinProj mPayload (fullSysCoinIdx k)) =
        1 - momCoinProj mPayload (fullSysCoinIdx k))
    (hTopBlock : ∀ cfg,
      let c := fullSysCoinIdx k
      let P_anc := (momAncReg mPayload).basisOutcomeProjector
        (coinSelOutcome (momCoin3Sel mPayload) c)
      P_anc * (unitaryConj (coreHadamardMom mPayload) (uSlotEff cfg)).1 * P_anc =
        P_anc * (momSysReg mPayload).embedMatrix (bUnitTwos cfg) * P_anc)
    (hUnitNorm : ∀ cfg, ‖bUnitTwos cfg‖ ≤ 1)
    (hPermSm : ∀ cfg (g : Equiv.Perm (Fin numElectrons))
      (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)),
      IsGridState x → IsGridState y →
        (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1)
          (permElectron g x) (permElectron g y) =
        (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) x y)
    (hErrIntrSm : ∀ cfg (spinUp : Finset (Fin numElectrons)),
      let E_vec : Fin 6 → ℝ := fun j ↦ if j = k then eShift cfg else 0
      ‖fermionicProjector spinUp *
        ((wSlot cfg : ℂ) • (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) -
          sixChannelShifted cfg E_vec k) *
        fermionicProjector spinUp‖ ≤ epsIntr) :
    MomSingleSlotCircuit mPayload mPGTwist k where
  toMomSingleSlotOracle := MomSingleSlotOracle.ofCoreOnly mWork wSlot eShift epsIntr uSlotEff
    bUnitTwos hWNonneg hSA hOffCoin hTopBlock hUnitNorm hPermSm hErrIntrSm
  tSlot := tSlot
  dSlot := fun cfg {Var} {n} v rC _rP rW _hCP hCW _hPW ↦ dCore cfg v rC rW hCW
  hToff := fun cfg {Var} {n} v rC _rP rW _hCP hCW _hPW ↦ hToff cfg v rC rW hCW
  hT := fun cfg {Var} {n} v rC _rP rW _hCP hCW _hPW ↦ hT cfg v rC rW hCW
  hReal := fun cfg {Var} [Fintype Var] [DecidableEq Var] {n} [NeZero (2 ^ n)]
      v rC rP rW hCP hCW _hPW ↦ by
    let selCore : QRegister (momCoreWires mPayload) (momCoreWires mPayload + mPGTwist) :=
      QRegister.block 0 (momCoreWires mPayload)
        (mom_zero_add_le (momCoreWires mPayload) mPGTwist)
    have hComp : (rC.concat rP hCP).compose selCore = rC := by
      apply FullSysMomSlots0135ConcreteAlt.qreg_ext
      intro i
      have hEq : selCore i = Fin.castAdd mPGTwist i := by
        ext; simp [selCore, FullSysMomSlots0135ConcreteAlt.qreg_block_apply]
      change (rC.concat rP hCP) (selCore i) = rC i
      rw [hEq, QRegister.concat_apply_left]
    have hAct : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        ((rC.concat rP hCP).compose selCore) rW (uSlotEff cfg) (dCore cfg v rC rW hCW) := by
      rw [hComp]
      exact hRealCore cfg v rC rW hCW
    exact hAct.widenActive

theorem disjoint_two_proj_comm_and_sum {D : ℕ} (P Q : Operator D) (U V : Unitary D)
    (hP_sa : Pᴴ = P) (hQ_sa : Qᴴ = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hU_right : U.1 * (1 - P) = 1 - P) (hV_right : V.1 * (1 - Q) = 1 - Q) (hU_sa : U.1ᴴ = U.1)
    (hV_sa : V.1ᴴ = V.1) : (V * U).1 = 1 + (V.1 - 1) + (U.1 - 1) ∧ (V * U).1ᴴ = (V * U).1 ∧
    (V * U).1 * P = U.1 * P ∧ (V * U).1 * Q = V.1 * Q ∧ (V * U).1 * (1 - (P + Q)) = 1 -
    (P + Q) ∧ ∀ R : Operator D, P * R = 0 → Q * R = 0 → (V * U).1 * R = R := by
  have hFixR {W X : Operator D} (h : W * (1 - X) = 1 - X) :
      (W - 1) * (1 - X) = 0 ∧ (W - 1) * X = W - 1 := by
    have hz : (W - 1) * (1 - X) = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
    refine ⟨hz, ?_⟩
    calc (W - 1) * X = (W - 1) - (W - 1) * (1 - X) := by noncomm_ring
      _ = W - 1 := by rw [hz, sub_zero]
  have hFixL {W X : Operator D} (h : (1 - X) * W = 1 - X) : X * (W - 1) = W - 1 := by
    have hz : (1 - X) * (W - 1) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
    calc X * (W - 1) = (W - 1) - (1 - X) * (W - 1) := by noncomm_ring
      _ = W - 1 := by rw [hz, sub_zero]
  have hAnn {A X R : Operator D} (hAX : A * X = A) (hXR : X * R = 0) : A * R = 0 := by
    rw [← hAX, Matrix.mul_assoc, hXR, Matrix.mul_zero]
  obtain ⟨hzU, hAU⟩ := hFixR hU_right
  obtain ⟨hzV, hBV⟩ := hFixR hV_right
  have hPA := hFixL (offProj_left_of_sa_and_right hP_sa hU_sa hU_right)
  have hQB := hFixL (offProj_left_of_sa_and_right hQ_sa hV_sa hV_right)
  have hAB : (U.1 - 1) * (V.1 - 1) = 0 := by
    rw [← hQB, ← Matrix.mul_assoc, hAnn hAU hPQ, Matrix.zero_mul]
  have hBA : (V.1 - 1) * (U.1 - 1) = 0 := by
    rw [← hPA, ← Matrix.mul_assoc, hAnn hBV hQP, Matrix.zero_mul]
  have hVU : (V * U).1 = 1 + (V.1 - 1) + (U.1 - 1) := by
    calc V.1 * U.1 = 1 + (V.1 - 1) + (U.1 - 1) + (V.1 - 1) * (U.1 - 1) := by noncomm_ring
      _ = 1 + (V.1 - 1) + (U.1 - 1) := by rw [hBA, add_zero]
  have hUV : (U * V).1 = 1 + (V.1 - 1) + (U.1 - 1) := by
    calc U.1 * V.1 = 1 + (V.1 - 1) + (U.1 - 1) + (U.1 - 1) * (V.1 - 1) := by noncomm_ring
      _ = 1 + (V.1 - 1) + (U.1 - 1) := by rw [hAB, add_zero]
  have hSA : (V * U).1ᴴ = (V * U).1 := by
    change (V.1 * U.1)ᴴ = V.1 * U.1
    rw [Matrix.conjTranspose_mul, hU_sa, hV_sa]
    change (U * V).1 = (V * U).1
    rw [hUV, hVU]
  have hBP := hAnn hBV hQP
  have hAQ := hAnn hAU hPQ
  have hOnP : (V * U).1 * P = U.1 * P := by
    rw [hVU]
    calc (1 + (V.1 - 1) + (U.1 - 1)) * P = U.1 * P + (V.1 - 1) * P := by noncomm_ring
      _ = U.1 * P := by rw [hBP, add_zero]
  have hOnQ : (V * U).1 * Q = V.1 * Q := by
    rw [hVU]
    calc (1 + (V.1 - 1) + (U.1 - 1)) * Q = V.1 * Q + (U.1 - 1) * Q := by noncomm_ring
      _ = V.1 * Q := by rw [hAQ, add_zero]
  have hOffSum : (V * U).1 * (1 - (P + Q)) = 1 - (P + Q) := by
    rw [hVU]
    calc (1 + (V.1 - 1) + (U.1 - 1)) * (1 - (P + Q))
        = (1 - (P + Q)) + ((V.1 - 1) * (1 - Q) - (V.1 - 1) * P) +
            ((U.1 - 1) * (1 - P) - (U.1 - 1) * Q) := by noncomm_ring
      _ = 1 - (P + Q) := by simp [hzV, hBP, hzU, hAQ]
  refine ⟨hVU, hSA, hOnP, hOnQ, hOffSum, fun R hPR hQR ↦ ?_⟩
  rw [hVU, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, hAnn hBV hQR, hAnn hAU hPR,
    add_zero, add_zero]
end FullSysMomSlots0135Concrete
end
end ModFullSysMomSlots0135Concrete

section ModGridGuard654Flag288
@[expose] public section
namespace GridGuard654Flag288Alt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
end GridGuard654Flag288Alt
namespace GridGuard654Flag288
open Operator QProg Matrix HermitianMat Circuit _root_.DynamicCircuit DynCircuitExt
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysRawAncWires fullSysBEWires)
open GridGuard654ReflAux
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
section MuxFlagAlgebra
noncomputable def diagBoolProj {k_act : ℕ} (pred : BitAssignment k_act → Bool) : Operator
    (2 ^ k_act) := Matrix.diagonal fun x ↦ if pred (basisBits k_act x) then (1 : ℂ) else 0
theorem diagBoolProj_conjTranspose {k_act : ℕ} (pred : BitAssignment k_act → Bool) :
    (diagBoolProj pred)ᴴ = diagBoolProj pred := by
  ext i j
  simp only [diagBoolProj, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    cases pred (basisBits k_act i) <;> simp
  · simp [hij, Ne.symm hij]
theorem diagBoolProj_mul_self {k_act : ℕ} (pred : BitAssignment k_act → Bool) :
    diagBoolProj pred * diagBoolProj pred = diagBoolProj pred := by
  rw [diagBoolProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  cases pred (basisBits k_act x) <;> simp
theorem diagBoolProj_mul_neg {k_act : ℕ} (pred : BitAssignment k_act → Bool) :
    diagBoolProj (fun γ ↦ !pred γ) * diagBoolProj pred = 0 := by
  rw [diagBoolProj, diagBoolProj, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    cases pred (basisBits k_act i) <;> simp
  · simp [hij]
theorem diagBoolProj_neg_mul {k_act : ℕ} (pred : BitAssignment k_act → Bool) :
    diagBoolProj pred * diagBoolProj (fun γ ↦ !pred γ) = 0 := by
  rw [diagBoolProj, diagBoolProj, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    cases pred (basisBits k_act i) <;> simp
  · simp [hij]
theorem diagBoolProj_add_compl {k_act : ℕ} (pred : BitAssignment k_act → Bool) :
    diagBoolProj (fun γ ↦ !pred γ) + diagBoolProj pred = 1 := by
  ext i j
  simp only [diagBoolProj, Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hp : pred (basisBits k_act i) = true <;> simp [hp]
  · simp [hij]
theorem embedMatrix_add_local {k n : ℕ} (r : QRegister k n) (A B : Operator (2 ^ k)) :
    r.embedMatrix (A + B) = r.embedMatrix A + r.embedMatrix B := by
  ext i j
  simp only [QRegister.embedMatrix_apply, Matrix.add_apply]
  split_ifs <;> ring
theorem embed_diagBoolProj_mulVec_basisKet {n k_act : ℕ}
    (rAct : QRegister k_act n) (pred : BitAssignment k_act → Bool) (β : BitAssignment n) :
    (rAct.embedMatrix (diagBoolProj pred)).mulVec (basisKet β) =
      (if pred (fun i ↦ β (rAct i)) then (1 : ℂ) else 0) • basisKet β := by
  have hsingle : ∀ l : Fin (2 ^ k_act), (diagBoolProj pred).mulVec (Pi.single l 1) =
      (if pred (basisBits k_act l) then (1 : ℂ) else 0) • Pi.single l 1 := by
    intro l
    funext x
    simp only [diagBoolProj, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Pi.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply]
    by_cases hxl : x = l <;> simp [hxl]
  let g_idx := (basisBitsEquiv n).symm β
  have hg_bits : basisBits n g_idx = β := basisBits_basisBitsEquiv_symm_eq β
  rw [basisKet, basisState, rAct.embedMatrix_mulVec_single_factors, hsingle,
    QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex,
    rAct.replaceIndex_extractIndex, pi_single_eq_basisKet, hg_bits]
  have hex : basisBits k_act (rAct.extractIndex g_idx) = fun i ↦ β (rAct i) := by
    funext i
    rw [QRegister.basisBits_extractIndex, hg_bits]
  rw [hex]
noncomputable def muxFlagMatrix {k_act k_mid : ℕ} (pred : BitAssignment k_act → Bool)
    (u₀ u₁ : Unitary (2 ^ k_mid)) : Operator (2 ^ (k_act + k_mid)) :=
  let rActLoc : QRegister k_act (k_act + k_mid) :=
    .block 0 k_act ((Nat.zero_add k_act).le.trans (Nat.le_add_right k_act k_mid))
  let rMidLoc : QRegister k_mid (k_act + k_mid) := .block k_act k_mid le_rfl
  rActLoc.embedMatrix (diagBoolProj fun γ ↦ !pred γ) * rMidLoc.embedMatrix u₀.1 +
    rActLoc.embedMatrix (diagBoolProj pred) * rMidLoc.embedMatrix u₁.1
noncomputable def muxFlagUnitary {k_act k_mid : ℕ} (pred : BitAssignment k_act → Bool)
    (u₀ u₁ : Unitary (2 ^ k_mid)) : Unitary (2 ^ (k_act + k_mid)) :=
  ⟨muxFlagMatrix pred u₀ u₁, by
    let rActLoc : QRegister k_act (k_act + k_mid) :=
      .block 0 k_act ((Nat.zero_add k_act).le.trans (Nat.le_add_right k_act k_mid))
    let rMidLoc : QRegister k_mid (k_act + k_mid) := .block k_act k_mid le_rfl
    have hdisj : rActLoc.DisjointWires rMidLoc := QRegister.block_disjoint_of_le 0 k_act k_act
      k_mid ((Nat.zero_add k_act).le.trans (Nat.le_add_right k_act k_mid)) le_rfl
      (Nat.zero_add k_act).le
    let P₀ := rActLoc.embedMatrix (diagBoolProj fun γ ↦ !pred γ)
    let P₁ := rActLoc.embedMatrix (diagBoolProj pred)
    let U₀ := rMidLoc.embedMatrix u₀.1
    let U₁ := rMidLoc.embedMatrix u₁.1
    have hEmbProj (q : BitAssignment k_act → Bool) :
        (rActLoc.embedMatrix (diagBoolProj q))ᴴ = rActLoc.embedMatrix (diagBoolProj q) ∧
        rActLoc.embedMatrix (diagBoolProj q) * rActLoc.embedMatrix (diagBoolProj q) =
          rActLoc.embedMatrix (diagBoolProj q) :=
      ⟨by rw [← QRegister.embedMatrix_conjTranspose, diagBoolProj_conjTranspose],
        by rw [← rActLoc.embedMatrix_mul, diagBoolProj_mul_self]⟩
    obtain ⟨hP₀_herm, hP₀_idem⟩ := hEmbProj (fun γ ↦ !pred γ)
    obtain ⟨hP₁_herm, hP₁_idem⟩ := hEmbProj pred
    have hP₀₁ : P₀ * P₁ = 0 := by
      dsimp only [P₀, P₁]; rw [← rActLoc.embedMatrix_mul, diagBoolProj_mul_neg,
        rActLoc.embedMatrix_zero]
    have hP₁₀ : P₁ * P₀ = 0 := by
      dsimp only [P₀, P₁]; rw [← rActLoc.embedMatrix_mul, diagBoolProj_neg_mul,
        rActLoc.embedMatrix_zero]
    have hsum : P₀ + P₁ = 1 := by
      dsimp only [P₀, P₁]; rw [← embedMatrix_add_local, diagBoolProj_add_compl,
        rActLoc.embedMatrix_one]
    have hEmbU (u : Unitary (2 ^ k_mid)) :
        (rMidLoc.embedMatrix u.1)ᴴ * rMidLoc.embedMatrix u.1 = 1 ∧
        rMidLoc.embedMatrix u.1 * (rMidLoc.embedMatrix u.1)ᴴ = 1 := by
      rw [← QRegister.embedMatrix_conjTranspose, ← rMidLoc.embedMatrix_mul,
        ← rMidLoc.embedMatrix_mul]
      have hl : u.1ᴴ * u.1 = 1 := by
        simpa [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self u
      have hr : u.1 * u.1ᴴ = 1 := by
        simpa [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self u
      rw [hl, hr, rMidLoc.embedMatrix_one]
      exact ⟨rfl, rfl⟩
    obtain ⟨hU₀_l, hU₀_r⟩ := hEmbU u₀
    obtain ⟨hU₁_l, hU₁_r⟩ := hEmbU u₁
    have hc₀_adj : U₀ᴴ * P₀ = P₀ * U₀ᴴ := by
      dsimp only [P₀, U₀]; rw [← QRegister.embedMatrix_conjTranspose]
      exact (rActLoc.embedMatrix_comm_of_disjoint rMidLoc hdisj _ u₀.1ᴴ).symm
    have hc₁_adj : U₁ᴴ * P₁ = P₁ * U₁ᴴ := by
      dsimp only [P₁, U₁]; rw [← QRegister.embedMatrix_conjTranspose]
      exact (rActLoc.embedMatrix_comm_of_disjoint rMidLoc hdisj _ u₁.1ᴴ).symm
    have hc₀₁ : U₀ * P₁ = P₁ * U₀ :=
      (rActLoc.embedMatrix_comm_of_disjoint rMidLoc hdisj _ u₀.1).symm
    have hc₁₀ : U₁ * P₀ = P₀ * U₁ :=
      (rActLoc.embedMatrix_comm_of_disjoint rMidLoc hdisj _ u₁.1).symm
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    change (P₀ * U₀ + P₁ * U₁)ᴴ * (P₀ * U₀ + P₁ * U₁) = 1 ∧
      (P₀ * U₀ + P₁ * U₁) * (P₀ * U₀ + P₁ * U₁)ᴴ = 1
    rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hP₀_herm, hP₁_herm]
    constructor
    · calc (U₀ᴴ * P₀ + U₁ᴴ * P₁) * (P₀ * U₀ + P₁ * U₁)
          = U₀ᴴ * (P₀ * P₀) * U₀ + U₀ᴴ * (P₀ * P₁) * U₁ +
              U₁ᴴ * (P₁ * P₀) * U₀ + U₁ᴴ * (P₁ * P₁) * U₁ := by noncomm_ring
        _ = P₀ * (U₀ᴴ * U₀) + P₁ * (U₁ᴴ * U₁) := by
              rw [hP₀_idem, hP₀₁, hP₁₀, hP₁_idem, hc₀_adj, hc₁_adj]; noncomm_ring
        _ = 1 := by rw [hU₀_l, hU₁_l, Matrix.mul_one, Matrix.mul_one, hsum]
    · have tDiag {P U : Operator (2 ^ (k_act + k_mid))} (hUr : U * Uᴴ = 1) (hPi : P * P = P) :
          (P * U) * (Uᴴ * P) = P := by
        rw [Matrix.mul_assoc P, ← Matrix.mul_assoc U, hUr, one_mul, hPi]
      have tCross {P Q U V : Operator (2 ^ (k_act + k_mid))}
          (hcV : Vᴴ * Q = Q * Vᴴ) (hcU : U * Q = Q * U) (hPQ : P * Q = 0) :
          (P * U) * (Vᴴ * Q) = 0 := by
        rw [hcV, ← Matrix.mul_assoc (P * U), Matrix.mul_assoc P U Q, hcU,
          ← Matrix.mul_assoc P Q U, hPQ, zero_mul, zero_mul]
      calc (P₀ * U₀ + P₁ * U₁) * (U₀ᴴ * P₀ + U₁ᴴ * P₁)
          = (P₀ * U₀) * (U₀ᴴ * P₀) + (P₀ * U₀) * (U₁ᴴ * P₁) +
              (P₁ * U₁) * (U₀ᴴ * P₀) + (P₁ * U₁) * (U₁ᴴ * P₁) := by noncomm_ring
        _ = 1 := by
              rw [tDiag hU₀_r hP₀_idem, tCross hc₁_adj hc₀₁ hP₀₁, tCross hc₀_adj hc₁₀ hP₁₀,
                tDiag hU₁_r hP₁_idem, add_zero, add_zero, hsum]⟩
theorem embed_muxFlagUnitary_mulVec_basisKet {n k_act k_mid : ℕ} (rAct : QRegister k_act n)
    (rMid : QRegister k_mid n) (hdisj : rAct.DisjointWires rMid)
    (pred : BitAssignment k_act → Bool) (u₀ u₁ : Unitary (2 ^ k_mid)) (β : BitAssignment n) :
    ((rAct.concat rMid hdisj).embedUnitary (muxFlagUnitary pred u₀ u₁)).1.mulVec (basisKet β)
    = (rMid.embedUnitary (if pred (fun i ↦ β (rAct i)) then u₁ else u₀)).1.mulVec (basisKet β)
    := by
  let rTot := rAct.concat rMid hdisj
  let rActLoc : QRegister k_act (k_act + k_mid) := .block 0 k_act (by omega)
  let rMidLoc : QRegister k_mid (k_act + k_mid) := .block k_act k_mid le_rfl
  have hcomp_act : rTot.compose rActLoc = rAct := by
    ext i
    apply congrArg Fin.val
    have h1 : rActLoc i = Fin.castAdd k_mid i := by
      ext; simp [rActLoc, GridGuard654Flag288Alt.qreg_block_apply]
    change rTot (rActLoc i) = rAct i
    rw [h1, QRegister.concat_apply_left]
  have hcomp_mid : rTot.compose rMidLoc = rMid := by
    ext j
    apply congrArg Fin.val
    have h1 : rMidLoc j = Fin.natAdd k_act j := by
      ext; simp [rMidLoc, GridGuard654Flag288Alt.qreg_block_apply]
    change rTot (rMidLoc j) = rMid j
    rw [h1, QRegister.concat_apply_right]
  have hexpand : (rTot.embedUnitary (muxFlagUnitary pred u₀ u₁)).1 =
      rMid.embedMatrix u₀.1 * rAct.embedMatrix (diagBoolProj fun γ ↦ !pred γ) +
        rMid.embedMatrix u₁.1 * rAct.embedMatrix (diagBoolProj pred) := by
    change rTot.embedMatrix (muxFlagMatrix pred u₀ u₁) = _
    dsimp only [muxFlagMatrix]
    rw[embedMatrix_add_local, rTot.embedMatrix_mul, rTot.embedMatrix_mul,
        ← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose,
        ← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose, hcomp_act,
        hcomp_mid, rAct.embedMatrix_comm_of_disjoint rMid hdisj _ u₀.1,
        rAct.embedMatrix_comm_of_disjoint rMid hdisj _ u₁.1]
  rw [hexpand, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    embed_diagBoolProj_mulVec_basisKet, embed_diagBoolProj_mulVec_basisKet,
    Matrix.mulVec_smul, Matrix.mulVec_smul]
  cases h : pred (fun i ↦ β (rAct i)) <;> simp [QRegister.embedUnitary_val]
end MuxFlagAlgebra
section CenterMuxEngine
def embedCircuit {k n : ℕ} (r : QRegister k n) : Circuit k → Circuit n
  | .identity => .identity
  | .gate g sub => .gate g (r.compose sub)
  | .seq c₁ c₂ => .seq (embedCircuit r c₁) (embedCircuit r c₂)
theorem embedCircuit_eval {k n : ℕ} (r : QRegister k n) (c : Circuit k) :
    (embedCircuit r c).eval = r.embedUnitary c.eval := by
  induction c with
  | identity => simp [embedCircuit, QRegister.embedUnitary_one]
  | gate g sub => simp [embedCircuit, QRegister.embedUnitary_compose]
  | seq c₁ c₂ ih₁ ih₂ => simp [embedCircuit, Circuit.eval_seq, ih₁, ih₂]
theorem eval_comm_embedMatrix_of_disjoint_support {n k_mid : ℕ} (c : Circuit n)
    (rMid : QRegister k_mid n) (hdisj : Disjoint c.support rMid.image)
    (A : Operator (2 ^ k_mid)) : c.eval.1 * rMid.embedMatrix A = rMid.embedMatrix A * c.eval.1
    := by
  induction c with
  | identity => simp
  | gate g r =>
      have hdr : r.DisjointWires rMid := by
        rw [QRegExt.disjointWires_iff_disjoint_image]
        exact hdisj
      simpa only [Circuit.eval_gate, QRegister.embedUnitary_val] using
        r.embedMatrix_comm_of_disjoint rMid hdr g.eval.1 A
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.disjoint_union_left] at hdisj
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ hdisj.1, ← Matrix.mul_assoc, ih₂ hdisj.2, Matrix.mul_assoc]
noncomputable def optZLocal {kMid : ℕ} (hkMid : 1 ≤ kMid) (pol : Bool) : Unitary (2 ^ kMid) :=
    if pol then (Circuit.Z (⟨0, hkMid⟩ : Wire kMid)).eval else 1
theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem embed_optZLocal_mulVec_basisKet {n kMid : ℕ}
    (hkMid : 1 ≤ kMid) (pol : Bool) (rMid : QRegister kMid n) (β : BitAssignment n) :
    (rMid.embedUnitary (optZLocal hkMid pol)).1.mulVec (basisKet β) =
      (if pol && decide (β (rMid ⟨0, hkMid⟩) = 1) then (-1 : ℂ) else 1) • basisKet β := by
  cases pol
  · rw [show optZLocal hkMid false = 1 from rfl, rMid.embedUnitary_one, Submonoid.coe_one,
      Matrix.one_mulVec]
    simp
  · have hemb : rMid.embedUnitary (optZLocal hkMid true) =
        (Circuit.Z (rMid ⟨0, hkMid⟩)).eval := by
      dsimp only [optZLocal]
      simp only [↓reduceIte]
      exact (embedCircuit_eval rMid (Circuit.Z ⟨0, hkMid⟩)).symm
    rw [hemb, single_diag_gate_evolve .Z (rMid ⟨0, hkMid⟩) (-1) rfl rfl rfl rfl β]
    rcases zmod2_eq_zero_or_one (β (rMid ⟨0, hkMid⟩)) with h0 | h1
    · simp [h0]
    · simp [h1]
def optCz {n : ℕ} (pol : Bool) (wFlag qSig : Wire n) (hne : wFlag ≠ qSig) : Circuit n :=
  if pol then czClifford wFlag qSig hne else .identity
@[simp]
theorem count_optCz_toff {n : ℕ} (pol : Bool) (wFlag qSig : Wire n) (hne : wFlag ≠ qSig) :
    (optCz pol wFlag qSig hne).count .TOFF = 0 := by
  cases pol <;> rfl
@[simp]
theorem count_optCz_t {n : ℕ} (pol : Bool) (wFlag qSig : Wire n) (hne : wFlag ≠ qSig) :
    (optCz pol wFlag qSig hne).count .T = 0 := by
  cases pol <;> rfl
theorem evolve_optCz_basisKet {n : ℕ} (pol : Bool) (wFlag qSig : Wire n) (hne : wFlag ≠ qSig)
    (β : BitAssignment n) : (optCz pol wFlag qSig hne).eval.1.mulVec (basisKet β) =
    (if pol && decide (β wFlag = 1 ∧ β qSig = 1) then (-1 : ℂ) else 1) • basisKet β := by
  cases pol
  · simp only [optCz, Bool.false_eq_true, ↓reduceIte, Circuit.eval_identity, Submonoid.coe_one,
      Matrix.one_mulVec, Bool.false_and, one_smul]
  · have hS : ∀ (q : Wire n) (γ : BitAssignment n), (Circuit.S q).eval.1.mulVec (basisKet γ) =
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
    unfold optCz czClifford
    simp only [↓reduceIte, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      hS, hSinv, evolve_CNOT_basisKet, Matrix.mulVec_smul, smul_smul]
    have hcnot2 := LocalClassicalPerm.cnot_self_cancel wFlag qSig hne β
    dsimp only at hcnot2
    rw [hcnot2]
    congr 1
    rw [Function.update_self]
    rcases zmod2_eq_zero_or_one (β wFlag) with hg | hg <;>
      rcases zmod2_eq_zero_or_one (β qSig) with hf | hf <;>
      simp [hg, hf]
end CenterMuxEngine
section DirectRootEngine
def PreservesNonAnc {n : ℕ} (s : SymTempAndStep n) : Prop :=
  ∀ (β : BitAssignment n) (w : Wire n), w ≠ s.anc → s.stepFwd β w = β w
theorem litAndSymStep_preservesNonAnc {n : ℕ} (polA polB polOut : Bool) (a b anc : Wire n)
    (hab : a ≠ b) (ha_anc : a ≠ anc) (hb_anc : b ≠ anc) :
    PreservesNonAnc (litAndSymStep polA polB polOut a b anc hab ha_anc hb_anc) := by
  intro β w hw_anc
  change w ≠ anc at hw_anc
  let stp := litAndSymStep polA polB polOut a b anc hab ha_anc hb_anc
  let β₁ := stp.f_pre β
  have hβ₁_a : β₁ a = polBit polA (β a) := by
    dsimp only [β₁, stp, litAndSymStep, Function.comp_apply]
    simp [Function.update_of_ne hab]
  have hβ₁_b : β₁ b = polBit polB (β b) := by
    dsimp only [β₁, stp, litAndSymStep, Function.comp_apply]
    simp [Function.update_of_ne hab.symm]
  let β₂ := Function.update β₁ anc (β₁ anc + β₁ a * β₁ b)
  have hβ₂_a : β₂ a = polBit polA (β a) := by simp [β₂, Function.update_of_ne ha_anc, hβ₁_a]
  have hβ₂_b : β₂ b = polBit polB (β b) := by simp [β₂, Function.update_of_ne hb_anc, hβ₁_b]
  change stp.f_midPre β₂ w = β w
  dsimp only [stp, litAndSymStep, Function.comp_apply]
  have hpol_cancel : ∀ (inv : Bool) (x : ZMod 2), polBit inv (polBit inv x) = x := by decide
  by_cases hwa : w = a
  · subst hwa
    simp [Function.update_self, Function.update_of_ne hw_anc,
      Function.update_of_ne hab, hβ₂_a, hpol_cancel]
  · by_cases hwb : w = b
    · subst hwb
      simp [Function.update_self, Function.update_of_ne hw_anc,
        Function.update_of_ne hwa, hβ₂_b, hpol_cancel]
    · have hβ₂_w : β₂ w = β w := by
        dsimp only [β₂, β₁, stp, litAndSymStep, Function.comp_apply]
        simp [Function.update_of_ne hw_anc, Function.update_of_ne hwb,
          Function.update_of_ne hwa]
      simp [Function.update_of_ne hw_anc, Function.update_of_ne hwa,
        Function.update_of_ne hwb, hβ₂_w]
theorem ladderStepAt_preservesNonAnc {n p : ℕ} (negIn : Bool) (inWires : Fin (p + 2) → Wire n)
    (hinj : Function.Injective inWires) (rAnc : QRegister (p + 1) n)
    (hdisj : ∀ t, inWires t ∉ rAnc.image) (j : Fin (p + 1)) : PreservesNonAnc
    (ladderStepAt negIn inWires hinj rAnc hdisj j) := by
  intro β w hw
  dsimp only [ladderStepAt] at hw ⊢
  split_ifs at hw ⊢ <;> exact litAndSymStep_preservesNonAnc _ _ _ _ _ _ _ _ _ β w hw
theorem validSymStepList_init_target {n m_scr : ℕ}
    {rScr : QRegister m_scr n} {s : SymTempAndStep n} :
    ∀ (offset : ℕ) (L : List (SymTempAndStep n)) (hoff : offset + L.length < m_scr),
      ValidSymStepList (∅ : Finset (Wire n)) rScr offset (L ++ [s]) →
      s.anc = rScr ⟨offset + L.length, hoff⟩ →
      ValidSymStepList ({s.anc} : Finset (Wire n)) rScr offset L
  | _, [], _, _, _ => trivial
  | offset, u :: rest, hoff, hval, hs_anc => by
      simp only [List.cons_append] at hval
      rcases hval with ⟨hlt, hanc, _, hlat, hrest⟩
      have hoff_rest : (offset + 1) + rest.length < m_scr := by
        simp only [List.length_cons] at hoff; omega
      have hs_anc_rest : s.anc = rScr ⟨(offset + 1) + rest.length, hoff_rest⟩ := by
        rw [hs_anc]
        apply congrArg rScr.wires
        ext; simp [List.length_cons]; omega
      have hdisj_u : Disjoint u.S ({s.anc} : Finset (Wire n)) := by
        rw [Finset.disjoint_singleton_right, hs_anc]
        exact hlat ⟨offset + (u :: rest).length, hoff⟩
          (by simp only [List.length_cons]; omega)
      exact ⟨hlt, hanc, hdisj_u, hlat,
        validSymStepList_init_target (offset + 1) rest hoff_rest hrest hs_anc_rest⟩
theorem classicalPerm_comp_eval_eq_one {n : ℕ} {c₁ c₂ : Circuit n}
    {f₁ f₂ : BitAssignment n → BitAssignment n}
    (h₁ : ClassicalPerm c₁ f₁) (h₂ : ClassicalPerm c₂ f₂)
    (hinv : ∀ β, f₂ (f₁ β) = β) :
    (c₁ ;;ᶜ c₂).eval = 1 ∧ (c₂ ;;ᶜ c₁).eval = 1 := by
  have h12 : (c₁ ;;ᶜ c₂).eval = 1 := by
    apply Subtype.ext
    apply matrix_ext_basisKet
    intro β
    simp only [Circuit.eval_seq, Submonoid.coe_mul, Submonoid.coe_one,
      ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    rw [h₁ β, h₂ (f₁ β), hinv β]
  refine ⟨h12, ?_⟩
  rw [Circuit.eval_seq] at h12 ⊢
  calc c₁.eval * c₂.eval
      = (c₂.eval)⁻¹ * (c₂.eval * c₁.eval) * c₂.eval := by simp
    _ = 1 := by rw [h12]; simp
theorem toff_self_eval_eq_one {n : ℕ} (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval = 1 :=
  (classicalPerm_comp_eval_eq_one
    (ClassicalPerm.TOFF c₁ c₂ anc h₁₂ h₁a h₂a)
    (ClassicalPerm.TOFF c₁ c₂ anc h₁₂ h₁a h₂a)
    (toff_update_self_cancel c₁ c₂ anc h₁a h₂a)).1
def symStepComputeDyn {Var : Type} {n : ℕ} (s : SymTempAndStep n) : DynamicCircuit Var n :=
  .seq (.circuit s.pre)
    (.seq (DynamicCircuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a) (.circuit s.midPre))
def symStepUncomputeDyn {Var : Type} {n : ℕ} (v : Var) (s : SymTempAndStep n) : DynamicCircuit
    Var n := .seq (.circuit s.midPost) (.seq (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc
    s.h₁₂) (.circuit s.post))
def symStepRootCircuit {n : ℕ} (s : SymTempAndStep n) : Circuit n :=
  (s.pre ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a) ;;ᶜ s.midPre
def directRootWrapDyn {Var : Type} {n : ℕ} (v : Var) (L : List (SymTempAndStep n))
    (s : SymTempAndStep n) (dInner : DynamicCircuit Var n) : DynamicCircuit Var n := .seq
    (symWrapDynList v L (symStepComputeDyn s))
    (.seq dInner (symWrapDynList v L (symStepUncomputeDyn v s)))
theorem count_symStepComputeDyn_toff {Var : Type} {n : ℕ} (s : SymTempAndStep n) :
    (symStepComputeDyn (Var := Var) s).count .TOFF = 0 := by
  rcases s.clifford with ⟨hp_toff, _, hmp_toff, _, _, _, _, _⟩
  simp [symStepComputeDyn, DynamicCircuit.count_andCompute_toff, hp_toff, hmp_toff]
theorem count_symStepComputeDyn_t {Var : Type} {n : ℕ} (s : SymTempAndStep n) :
    (symStepComputeDyn (Var := Var) s).count .T = 4 := by
  rcases s.clifford with ⟨_, hp_t, _, hmp_t, _, _, _, _⟩
  simp [symStepComputeDyn, DynamicCircuit.count_andCompute_t, hp_t, hmp_t]
theorem count_symStepUncomputeDyn_toff {Var : Type} {n : ℕ} (v : Var) (s : SymTempAndStep n) :
    (symStepUncomputeDyn v s).count .TOFF = 0 := by
  rcases s.clifford with ⟨_, _, _, _, hmq_toff, _, hpo_toff, _⟩
  simp [symStepUncomputeDyn, DynamicCircuit.count_andUncompute_toff, hmq_toff, hpo_toff]
theorem count_symStepUncomputeDyn_t {Var : Type} {n : ℕ} (v : Var) (s : SymTempAndStep n) :
    (symStepUncomputeDyn v s).count .T = 0 := by
  rcases s.clifford with ⟨_, _, _, _, _, hmq_t, _, hpo_t⟩
  simp [symStepUncomputeDyn, DynamicCircuit.count_andUncompute_t, hmq_t, hpo_t]
theorem count_directRootWrapDyn_toff {Var : Type} {n : ℕ} (v : Var)
    (L : List (SymTempAndStep n)) (s : SymTempAndStep n) (dInner : DynamicCircuit Var n) :
    (directRootWrapDyn v L s dInner).count .TOFF = dInner.count .TOFF := by
  dsimp only [directRootWrapDyn]
  simp only [DynamicCircuit.count,
    count_symWrapDynList_toff v L _ (count_symStepComputeDyn_toff s),
    count_symWrapDynList_toff v L _ (count_symStepUncomputeDyn_toff v s),
    Nat.zero_add, Nat.add_zero]
theorem count_directRootWrapDyn_t {Var : Type} {n : ℕ} (v : Var)
    (L : List (SymTempAndStep n)) (s : SymTempAndStep n) (dInner : DynamicCircuit Var n) :
    (directRootWrapDyn v L s dInner).count .T = (8 * L.length + 4) + dInner.count .T := by
  dsimp only [directRootWrapDyn]
  simp only [DynamicCircuit.count, count_symWrapDynList_t,
    count_symStepComputeDyn_t, count_symStepUncomputeDyn_t]
  omega
theorem storeConst_symStepComputeDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (s : SymTempAndStep n) :
    StoreConst (symStepComputeDyn (Var := Var) s) := by
  unfold symStepComputeDyn DynamicCircuit.andCompute
  exact (StoreConst.circuit s.pre).seq
    ((StoreConst.circuit _).seq (StoreConst.circuit s.midPre))
theorem storeConst_symStepUncomputeDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (s : SymTempAndStep n) :
    StoreConst (symStepUncomputeDyn v s) := by
  unfold symStepUncomputeDyn
  exact (StoreConst.circuit s.midPost).seq
    ((StoreConst.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).seq (StoreConst.circuit s.post))
theorem symStepRootCircuit_perm {n : ℕ} (s : SymTempAndStep n) : ClassicalPerm
    (symStepRootCircuit s) s.stepFwd := (s.local_pre.perm.seq (ClassicalPerm.TOFF s.c₁ s.c₂
    s.anc s.h₁₂ s.h₁a s.h₂a)).seq s.local_midPre.perm
theorem symStepRootCircuit_support_sub {n : ℕ} (s : SymTempAndStep n) :
    (symStepRootCircuit s).support ⊆ s.S := by
  have htoff : (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).support ⊆ s.S := by
    intro w hw
    rcases (QRegister.mem_image _ w).mp hw with ⟨i, rfl⟩
    fin_cases i
    · exact s.c₁_mem
    · exact s.c₂_mem
    · exact s.anc_mem
  dsimp only [symStepRootCircuit]
  simp only [Circuit.support_seq]
  exact Finset.union_subset (Finset.union_subset s.local_pre.support_sub htoff)
    s.local_midPre.support_sub
theorem symWrapCircuitList_support_sub {n : ℕ} :
    ∀ (L : List (SymTempAndStep n)) (c : Circuit n) (S_all : Finset (Wire n)),
      c.support ⊆ S_all →
      (∀ u ∈ L, u.S ⊆ S_all) →
      (symWrapCircuitList L c).support ⊆ S_all
  | [], c, _, hc, _ => hc
  | u :: rest, c, S_all, hc, hL => by
      have hu : u.S ⊆ S_all := hL u (List.mem_cons_self ..)
      have hrest := symWrapCircuitList_support_sub rest c S_all hc
        (fun x hx ↦ hL x (List.mem_cons_of_mem u hx))
      have htoff : (Circuit.TOFF u.c₁ u.c₂ u.anc u.h₁₂ u.h₁a u.h₂a).support ⊆ S_all := by
        intro w hw
        rcases (QRegister.mem_image _ w).mp hw with ⟨i, rfl⟩
        fin_cases i
        · exact hu u.c₁_mem
        · exact hu u.c₂_mem
        · exact hu u.anc_mem
      change (u.toTempAndStep.wrapCircuit (symWrapCircuitList rest c)).support ⊆ S_all
      dsimp only [TempAndStep.wrapCircuit]
      simp only [Circuit.support_seq, Finset.union_subset_iff,
        u.local_pre.support_sub.trans hu, u.local_midPre.support_sub.trans hu,
        u.local_midPost.support_sub.trans hu, u.local_post.support_sub.trans hu,
        htoff, hrest, and_self]
theorem wp_symStepComputeDyn_update_eq {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (s : SymTempAndStep n) (Ψ : CQAssertionCompat Var (2 ^ n))
    (hΨ : ∀ σ val, Ψ (Function.update σ v val) = Ψ σ) :
    ∀ σ val, wp (symStepComputeDyn s).compile Ψ (Function.update σ v val) =
      wp (symStepComputeDyn s).compile Ψ σ := by
  cases nonempty_fintype Var
  intro σ val
  simp only [symStepComputeDyn, DynamicCircuit.andCompute, DynamicCircuit.compile_seq,
    DynamicCircuit.compile_circuit, wp_qSeq, DynCircuitExt.wp_circuit_compile_compat,
    wpQAssignCompat, hΨ]
theorem wp_symStepUncomputeDyn_update_eq {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (s : SymTempAndStep n) (Θ : CQAssertionCompat Var (2 ^ n)) :
    ∀ σ val, wp (symStepUncomputeDyn v s).compile Θ (Function.update σ v val) =
      wp (symStepUncomputeDyn v s).compile Θ σ := by
  cases nonempty_fintype Var
  intro σ val
  simp only [symStepUncomputeDyn, DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit,
    wp_qSeq, DynCircuitExt.wp_circuit_compile_compat, wpQAssignCompat,
    DynamicCircuit.wp_andUncompute_update_self]
theorem restrictZero_wp_symStepComputeDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (s : SymTempAndStep n) (Ψ : CQAssertionCompat Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla (wp (symStepComputeDyn s).compile Ψ)
    (QRegister.singleton s.anc) = CQAssertion.restrictToZeroAncilla
    (wpQAssignCompat (symStepRootCircuit s).eval Ψ) (QRegister.singleton s.anc) := by
  have hpre_disj : Disjoint s.pre.support (QRegister.singleton s.anc).image := by
    rw [QRegister.image_singleton, Finset.disjoint_singleton_right]
    exact s.anc_not_mem_pre
  have hlhs : wp (symStepComputeDyn s).compile Ψ = wpQAssignCompat s.pre.eval (wp
      ((DynamicCircuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a).compile.qSeq s.midPre.compile)
      Ψ) := by
    simp [symStepComputeDyn, DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit]
  have hrhs : wpQAssignCompat (symStepRootCircuit s).eval Ψ = wpQAssignCompat s.pre.eval
      (wpQAssignCompat (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval (wp
      s.midPre.compile Ψ)) := by
    simp[symStepRootCircuit, Circuit.eval_seq, wpQAssignCompat_comp, mul_assoc]
  rw [hlhs, hrhs,
    restrictToZeroAncilla_wp_qAssign_comm_of_disjoint s.pre _ hpre_disj,
    restrictToZeroAncilla_wp_qAssign_comm_of_disjoint s.pre _ hpre_disj,
    DynCircuitExt.restrictToZeroAncilla_wp_andCompute_seq_compat
      s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a]
theorem restrictZero_wp_symStepRoot_uncompute_cancel {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (s : SymTempAndStep n)
    (Θ : CQAssertionCompat Var (2 ^ n)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat (symStepRootCircuit s).eval (wp
    (symStepUncomputeDyn v s).compile Θ)) (QRegister.singleton s.anc) =
    CQAssertion.restrictToZeroAncilla Θ (QRegister.singleton s.anc) := by
  have hpre_disj : Disjoint s.pre.support (QRegister.singleton s.anc).image := by
    rw [QRegister.image_singleton, Finset.disjoint_singleton_right]
    exact s.anc_not_mem_pre
  have hcancel {c₁ c₂ : Circuit n} (h1 : (c₁ ;;ᶜ c₂).eval = 1) (Φ : CQAssertionCompat Var (2 ^ n)) :
      wpQAssignCompat c₁.eval (wpQAssignCompat c₂.eval Φ) = Φ := by
    have hc : wpQAssignCompat c₁.eval (wpQAssignCompat c₂.eval Φ) =
        wpQAssignCompat (c₁ ;;ᶜ c₂).eval Φ := by simp [Circuit.eval_seq, wpQAssignCompat_comp]
    rw [hc, h1]
    funext σ
    exact Subtype.ext (by simp [wpQAssignCompat, qAssignObsMap])
  let Θ₁ := wpQAssignCompat s.post.eval Θ
  have hexp : wpQAssignCompat (symStepRootCircuit s).eval (wp (symStepUncomputeDyn v s).compile Θ) =
      wpQAssignCompat s.pre.eval
        (wpQAssignCompat (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval
          (wp (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).compile Θ₁)) := by
    have h1 : wp (symStepUncomputeDyn v s).compile Θ = wpQAssignCompat s.midPost.eval (wp
        (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).compile Θ₁) := by
      simp [symStepUncomputeDyn, Θ₁, DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit]
    have h2 : wpQAssignCompat (symStepRootCircuit s).eval (wpQAssignCompat s.midPost.eval (wp
        (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).compile Θ₁)) = wpQAssignCompat
        s.pre.eval (wpQAssignCompat (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval
        (wpQAssignCompat s.midPre.eval (wpQAssignCompat s.midPost.eval (wp
        (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).compile Θ₁)))) := by
      simp [symStepRootCircuit, Circuit.eval_seq, wpQAssignCompat_comp, mul_assoc]
    rw [h1, h2, hcancel (classicalPerm_comp_eval_eq_one s.local_midPre.perm s.local_midPost.perm
      s.midPost_midPre_id).1]
  rw [hexp,
    restrictToZeroAncilla_wp_qAssign_comm_of_disjoint s.pre _ hpre_disj,
    DynCircuitExt.restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
      v s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a Θ₁
      (fun σ val ↦ by dsimp only [Θ₁, wpQAssignCompat]; rw [hΘ σ val]),
    ← restrictToZeroAncilla_wp_qAssign_comm_of_disjoint s.pre _ hpre_disj,
    hcancel (classicalPerm_comp_eval_eq_one s.local_pre.perm s.local_post.perm s.post_pre_id).1]
theorem classicalPerm_comm_proj_zero {n m : ℕ} {c : Circuit n}
    {f : BitAssignment n → BitAssignment n} (r : QRegister m n)
    (hperm : ClassicalPerm c f) (hr : ∀ β (j : Fin m), f β (r j) = β (r j)) :
    c.eval.1 * r.basisOutcomeProjector 0 = r.basisOutcomeProjector 0 * c.eval.1 := by
  apply matrix_ext_basisKet
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    register_basisOutcomeProjector_zero_mulVec_basisKet]
  by_cases h0 : ∀ j : Fin m, β (r j) = 0
  · have hf0 : ∀ j : Fin m, f β (r j) = 0 := fun j ↦ (hr β j).trans (h0 j)
    rw [ite_eq_left h0, hperm β, register_basisOutcomeProjector_zero_mulVec_basisKet,
      ite_eq_left hf0]
  · have hf0 : ¬ ∀ j : Fin m, f β (r j) = 0 := fun hf ↦ h0 fun j ↦ (hr β j).symm.trans (hf j)
    rw [ite_eq_right h0, Matrix.mulVec_zero, hperm β,
      register_basisOutcomeProjector_zero_mulVec_basisKet, ite_eq_right hf0]
theorem restrictZero_wp_qAssign_comm_of_perm {Var : Type} [Fintype Var] {n m : ℕ}
    {c : Circuit n} {f : BitAssignment n → BitAssignment n} (r : QRegister m n)
    (hperm : ClassicalPerm c f) (hr : ∀ β (j : Fin m), f β (r j) = β (r j))
    (Φ : CQAssertionCompat Var (2 ^ n)) : CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval
      Φ)
    r = wpQAssignCompat c.eval (CQAssertion.restrictToZeroAncilla Φ r) := by
  funext σ
  apply Subtype.ext
  let P₀ := r.basisOutcomeProjector 0
  have hadj : P₀ * c.eval.1ᴴ = c.eval.1ᴴ * P₀ := by
    simpa only [P₀, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
      congrArg conjTranspose (classicalPerm_comm_proj_zero r hperm hr)
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  change (Φ σ).1.conj (P₀ * c.eval.1ᴴ) = (Φ σ).1.conj (c.eval.1ᴴ * P₀)
  rw [hadj]
theorem wrapCircuit_seq_symStepRootCircuit_eval {n : ℕ} (u : SymTempAndStep n) (c_rest : Circuit n)
    :
    (u.toTempAndStep.wrapCircuit c_rest ;;ᶜ symStepRootCircuit u).eval =
      (symStepRootCircuit u ;;ᶜ c_rest).eval := by
  let T := (Circuit.TOFF u.c₁ u.c₂ u.anc u.h₁₂ u.h₁a u.h₂a).eval
  have hpost_pre : u.pre.eval * u.post.eval = 1 := by
    simpa only [Circuit.eval_seq] using
      (classicalPerm_comp_eval_eq_one u.local_pre.perm u.local_post.perm u.post_pre_id).2
  have htoff : T * T = 1 := by
    simpa only [T, Circuit.eval_seq] using toff_self_eval_eq_one u.c₁ u.c₂ u.anc u.h₁₂ u.h₁a u.h₂a
  have hmid : u.midPre.eval * u.midPost.eval = 1 := by
    simpa only [Circuit.eval_seq] using
      (classicalPerm_comp_eval_eq_one u.local_midPre.perm u.local_midPost.perm
        u.midPost_midPre_id).2
  dsimp only [TempAndStep.wrapCircuit, symStepRootCircuit]
  simp only [Circuit.eval_seq]
  calc (u.midPre.eval * (T * u.pre.eval)) *
        (u.post.eval * T * (u.midPost.eval * c_rest.eval * u.midPre.eval) * T * u.pre.eval)
      = u.midPre.eval * T * (u.pre.eval * u.post.eval) * T *
          (u.midPost.eval * c_rest.eval * u.midPre.eval) * T * u.pre.eval := by
            simp only [mul_assoc]
    _ = u.midPre.eval * (T * T) * (u.midPost.eval * c_rest.eval * u.midPre.eval) *
          T * u.pre.eval := by rw [hpost_pre, mul_one]; simp only [mul_assoc]
    _ = (u.midPre.eval * u.midPost.eval) * c_rest.eval *
          (u.midPre.eval * (T * u.pre.eval)) := by rw [htoff, mul_one]; simp only [mul_assoc]
    _ = c_rest.eval * (u.midPre.eval * (T * u.pre.eval)) := by rw [hmid, one_mul]
theorem restrictZero_wp_cFwd_uncompute_cancel
    {Var : Type} [Fintype Var] [DecidableEq Var] {n m_comb : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister m_comb n)
    (s : SymTempAndStep n) (hs : PreservesNonAnc s) :
    ∀ (offset : ℕ) (L : List (SymTempAndStep n)) (hbound : offset + (L.length + 1) ≤ m_comb),
      ValidSymStepList ({s.anc} : Finset (Wire n)) rComb offset L →
      s.anc = rComb ⟨offset + L.length, by omega⟩ →
      ∀ (Θ : CQAssertionCompat Var (2 ^ n)),
        (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
        CQAssertion.restrictToZeroAncilla
          (wpQAssignCompat (symWrapCircuitList L (symStepRootCircuit s)).eval
            (wp (symWrapDynList v L (symStepUncomputeDyn v s)).compile Θ))
          (rComb.slice offset (L.length + 1) hbound) =
        CQAssertion.restrictToZeroAncilla Θ (rComb.slice offset (L.length + 1) hbound)
  | offset, [], hbound, _, hs_anc, Θ, hΘ => by
      have hreg : rComb.slice offset (([] : List (SymTempAndStep n)).length + 1) hbound =
          QRegister.singleton s.anc := by
        ext idx; fin_cases idx
        simp only [QRegister.slice_apply]
        rw [hs_anc]
        exact congrArg Fin.val (congrArg rComb.wires (Fin.ext (by simp)))
      rw [hreg]
      exact restrictZero_wp_symStepRoot_uncompute_cancel v s Θ hΘ
  | offset, u :: rest, hbound, hvalid, hs_anc, Θ, hΘ => by
      have hbound_rest : (offset + 1) + (rest.length + 1) ≤ m_comb := by
        simp only [List.length_cons] at hbound; omega
      have hs_anc_rest : s.anc = rComb ⟨(offset + 1) + rest.length, by omega⟩ := by
        rw [hs_anc]; exact congrArg rComb.wires (Fin.ext (by simp [List.length_cons]; omega))
      obtain ⟨hperm_u, hout_u, _, _⟩ :=
        symWrapList_correct (m_inner := 0) v ({s.anc} : Finset (Wire n)) rComb offset (u :: rest)
          (by simp only [List.length_cons] at hbound ⊢; omega) hvalid
          (.circuit (symStepRootCircuit s)) (symStepRootCircuit s) s.stepFwd
          (symStepRootCircuit_perm s)
          (fun β w hw ↦ hs β w (Finset.notMem_singleton.mp hw))
          (fun Ψ _ ↦
            by rw [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat])
          (fun Ψ hΨ σ val ↦ by
            rw [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
            simp only [wpQAssignCompat, hΨ])
      rcases hvalid with ⟨hlt, hanc_u, _, hlat_u, hvalid_rest⟩
      have hu_ne_s : u.anc ≠ s.anc := fun heq ↦ by
        have hv := congrArg Fin.val (rComb.wires.injective (hanc_u.symm.trans (heq.trans hs_anc)))
        simp [List.length_cons] at hv
      have hu_fix : ∀ β (j : Fin 1),
          (if (QRegister.singleton u.anc j) ∈ ({s.anc} : Finset (Wire n))
           then s.stepFwd (symStepFwdList (u :: rest) β) (QRegister.singleton u.anc j)
           else β (QRegister.singleton u.anc j)) =
          β (QRegister.singleton u.anc j) := fun β j ↦ by
        fin_cases j
        exact hout_u β u.anc (Finset.notMem_singleton.mpr hu_ne_s)
      let c_rest := symWrapCircuitList rest (symStepRootCircuit s)
      let d_rest := symWrapDynList v rest (symStepUncomputeDyn v s)
      let c_u := symWrapCircuitList (u :: rest) (symStepRootCircuit s)
      let d_u := symWrapDynList v (u :: rest) (symStepUncomputeDyn v s)
      let rSub : QRegister ((rest.length + 1) + 1) n :=
        rComb.slice offset ((rest.length + 1) +
          1) (by simp only [List.length_cons] at hbound; omega)
      have hrSub_eq : rComb.slice offset ((u :: rest).length + 1) hbound = rSub := by
        ext idx; simp [rSub, GridGuard654ReflAlt.qreg_block_apply, List.length_cons]
      have hrSub_0 : rSub 0 = u.anc := by
        rw [hanc_u]; simp only [rSub, QRegister.slice_apply]
        exact congrArg rComb.wires (Fin.ext (by simp))
      let rTail := rSub.slice 1 (rest.length + 1) (by omega)
      have hrTail_eq : rTail = rComb.slice (offset + 1) (rest.length + 1) hbound_rest := by
        ext idx; simp only [rTail, rSub, QRegister.slice_apply]
        exact congrArg Fin.val (congrArg rComb.wires (Fin.ext (by simp; omega)))
      have hdisj_root_tail : Disjoint (symStepRootCircuit u).support rTail.image := by
        refine Finset.disjoint_of_subset_left (symStepRootCircuit_support_sub u) ?_
        rw [hrTail_eq, Finset.disjoint_right]
        intro w hw
        rcases (QRegister.mem_image _ w).mp hw with ⟨idx, rfl⟩
        exact hlat_u ⟨(offset + 1) + idx.val, by omega⟩ (by dsimp; omega)
      let Ψ_post := wp (symStepUncomputeDyn v u).compile Θ
      have hd_u_exp : CQAssertion.restrictToZeroAncilla (wp d_u.compile Θ)
          (QRegister.singleton u.anc) = CQAssertion.restrictToZeroAncilla (wpQAssignCompat
          (symStepRootCircuit u).eval (wp d_rest.compile Ψ_post)) (QRegister.singleton u.anc) := by
        have hd_u_eq : wp d_u.compile Θ =
            wp (symStepComputeDyn u).compile (wp d_rest.compile Ψ_post) := by
          change wp (u.toTempAndStep.wrapDynamic v d_rest).compile Θ = _
          simp [TempAndStep.wrapDynamic, symStepComputeDyn, symStepUncomputeDyn, Ψ_post,
            DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit]
        rw [hd_u_eq]
        exact restrictZero_wp_symStepComputeDyn u (wp d_rest.compile Ψ_post)
      have hcu_cancel : wpQAssignCompat c_u.eval (wpQAssignCompat (symStepRootCircuit u).eval
          (wp d_rest.compile Ψ_post)) = wpQAssignCompat (symStepRootCircuit u).eval
          (wpQAssignCompat c_rest.eval (wp d_rest.compile Ψ_post)) := by
        have hc1 : wpQAssignCompat c_u.eval
              (wpQAssignCompat (symStepRootCircuit u).eval (wp d_rest.compile Ψ_post)) =
            wpQAssignCompat (u.toTempAndStep.wrapCircuit c_rest ;;ᶜ symStepRootCircuit u).eval
              (wp d_rest.compile Ψ_post) := by
          change wpQAssignCompat (u.toTempAndStep.wrapCircuit c_rest).eval _ = _
          simp [Circuit.eval_seq, wpQAssignCompat_comp]
        rw [hc1, wrapCircuit_seq_symStepRootCircuit_eval u c_rest]
        simp [Circuit.eval_seq, wpQAssignCompat_comp]
      have hih := restrictZero_wp_cFwd_uncompute_cancel v rComb s hs (offset + 1) rest
        hbound_rest hvalid_rest hs_anc_rest Ψ_post (wp_symStepUncomputeDyn_update_eq v u Θ)
      rw [hrSub_eq]
      change CQAssertion.restrictToZeroAncilla (wpQAssignCompat c_u.eval (wp d_u.compile Θ)) rSub =
        CQAssertion.restrictToZeroAncilla Θ rSub
      rw [restrictAssertionToZeroAncilla_head_tail _ rSub, hrSub_0,
        restrictZero_wp_qAssign_comm_of_perm (QRegister.singleton u.anc) hperm_u hu_fix,
        hd_u_exp,
        ← restrictZero_wp_qAssign_comm_of_perm (QRegister.singleton u.anc) hperm_u hu_fix,
        hcu_cancel,
        restrictAssertionToZeroAncilla_comm _ (QRegister.singleton u.anc) rTail,
        restrictToZeroAncilla_wp_qAssign_comm_of_disjoint
          (symStepRootCircuit u) rTail hdisj_root_tail,
        show rTail = rComb.slice (offset + 1) (rest.length + 1) hbound_rest from hrTail_eq,
        hih,
        ← show rTail = rComb.slice (offset + 1) (rest.length + 1) hbound_rest from hrTail_eq,
        ← restrictToZeroAncilla_wp_qAssign_comm_of_disjoint
          (symStepRootCircuit u) rTail hdisj_root_tail,
        restrictAssertionToZeroAncilla_comm _ rTail (QRegister.singleton u.anc),
        restrictZero_wp_symStepRoot_uncompute_cancel v u Θ hΘ,
        ← hrSub_0,
        ← restrictAssertionToZeroAncilla_head_tail Θ rSub]
theorem proj_zero_absorb_of_image_subset {n m₁ m₂ : ℕ} {rSmall : QRegister m₁ n}
    {rBig : QRegister m₂ n} (hsub : rSmall.image ⊆ rBig.image) : rBig.basisOutcomeProjector 0
    * rSmall.basisOutcomeProjector 0 = rBig.basisOutcomeProjector 0 ∧
    rSmall.basisOutcomeProjector 0 * rBig.basisOutcomeProjector 0 = rBig.basisOutcomeProjector
    0 := by
  have himp (β : BitAssignment n) (hBig : ∀ j : Fin m₂, β (rBig j) = 0) (i : Fin m₁) :
      β (rSmall i) = 0 := by
    rcases (QRegister.mem_image rBig (rSmall i)).mp
      (hsub ((QRegister.mem_image rSmall _).mpr ⟨i, rfl⟩)) with ⟨j, hj⟩
    rw [← hj]
    exact hBig j
  constructor
  · apply matrix_ext_basisKet; intro β
    rw [← Matrix.mulVec_mulVec, register_basisOutcomeProjector_zero_mulVec_basisKet]
    by_cases hBig : ∀ j : Fin m₂, β (rBig j) = 0
    · rw [ite_eq_left (himp β hBig), register_basisOutcomeProjector_zero_mulVec_basisKet,
        ite_eq_left hBig]
    · by_cases hSmall : ∀ i : Fin m₁, β (rSmall i) = 0
      · rw [ite_eq_left hSmall, register_basisOutcomeProjector_zero_mulVec_basisKet,
        ite_eq_right hBig]
      · rw [ite_eq_right hSmall, Matrix.mulVec_zero,
          register_basisOutcomeProjector_zero_mulVec_basisKet, ite_eq_right hBig]
  · apply matrix_ext_basisKet; intro β
    rw [← Matrix.mulVec_mulVec, register_basisOutcomeProjector_zero_mulVec_basisKet]
    by_cases hBig : ∀ j : Fin m₂, β (rBig j) = 0
    · rw [ite_eq_left hBig, register_basisOutcomeProjector_zero_mulVec_basisKet,
        ite_eq_left (himp β hBig)]
    · rw [ite_eq_right hBig, Matrix.mulVec_zero]
structure DirectRootSpec {n : ℕ} (k_act : ℕ) where
  L : List (SymTempAndStep n)
  s : SymTempAndStep n
  tIdx : Fin k_act
  pred : BitAssignment k_act → Bool
  hpred : ∀ γ val, pred (Function.update γ tIdx val) = pred γ
def DirectRootSpecRealizes {n k_act k_mid m_pool : ℕ}
    (rAct : QRegister k_act n) (rMid : QRegister k_mid n) (rPool : QRegister m_pool n)
    (sp : DirectRootSpec (n := n) k_act) : Prop :=
  ∃ (hfit : sp.L.length ≤ m_pool) (m_c : ℕ) (hm_c : sp.L.length + 1 = m_c)
    (rComb : QRegister m_c n),
    (∀ (j : ℕ) (hj : j < sp.L.length),
      rComb ⟨j, hm_c ▸ Nat.lt_succ_of_lt hj⟩ = rPool ⟨j, lt_of_lt_of_le hj hfit⟩) ∧
    rComb ⟨sp.L.length, hm_c ▸ Nat.lt_succ_self _⟩ = rAct sp.tIdx ∧
    sp.s.anc = rAct sp.tIdx ∧
    PreservesNonAnc sp.s ∧
    ValidSymStepList ({sp.s.anc} : Finset (Wire n)) rComb 0 sp.L ∧
    Disjoint sp.s.S rMid.image ∧
    (∀ u ∈ sp.L, Disjoint u.S rMid.image) ∧
    (∀ β : BitAssignment n,
      (∀ j : Fin m_c, β (rComb j) = 0) →
      sp.s.stepFwd (symStepFwdList sp.L β) (rAct sp.tIdx) =
        if sp.pred (fun i ↦ β (rAct i)) then 1 else 0)
def DirectRootSpec.togglePred {n k_act : ℕ} (sp : DirectRootSpec (n := n) k_act)
    (acc : BitAssignment k_act → Bool) (γ : BitAssignment k_act) : Bool :=
  acc (Function.update γ sp.tIdx (γ sp.tIdx + if sp.pred γ then 1 else 0))
theorem directRootWrapDyn_muxFlag_step {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k_act k_mid m_pool m_clean m_clean' : ℕ} [NeZero (2 ^ n)]
    (v : Var)
    (rAct : QRegister k_act n) (rMid : QRegister k_mid n) (rPool : QRegister m_pool n)
    (hActMid : rAct.DisjointWires rMid)
    (hMidPool : rMid.DisjointWires rPool)
    (rClean : QRegister m_clean n) (rClean' : QRegister m_clean' n)
    (sp : DirectRootSpec (n := n) k_act)
    (hsp : DirectRootSpecRealizes rAct rMid rPool sp)
    (hClean_sub : rClean.image ⊆ rClean'.image)
    (hPool_sub : rPool.image ⊆ rClean'.image)
    (ht_in : rAct sp.tIdx ∈ rClean'.image)
    (ht_not_clean : rAct sp.tIdx ∉ rClean.image)
    (dInner : DynamicCircuit Var n)
    (pred : BitAssignment k_act → Bool)
    (u₀ u₁ : Unitary (2 ^ k_mid))
    (hInner : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rAct.concat rMid hActMid) rClean (muxFlagUnitary pred u₀ u₁) dInner) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rAct.concat rMid hActMid) rClean'
      (muxFlagUnitary (sp.togglePred pred) u₀ u₁)
      (directRootWrapDyn v sp.L sp.s dInner) := by
  obtain ⟨hfit, m_c, hm_c, rComb, hrComb_low, hrComb_top, hs_anc, hs_pres,
    hvalid, hs_mid, hL_mid, hroot_eval⟩ := hsp
  subst hm_c
  have hrComb_sub : rComb.image ⊆ rClean'.image := fun w hw ↦ by
    rcases (QRegister.mem_image rComb w).mp hw with ⟨idx, rfl⟩
    by_cases hlt : idx.val < sp.L.length
    · rw [show idx = ⟨idx.val, Nat.lt_succ_of_lt hlt⟩ from Fin.ext rfl, hrComb_low idx.val hlt]
      exact hPool_sub ((QRegister.mem_image rPool _).mpr ⟨_, rfl⟩)
    · rw [show idx = ⟨sp.L.length, Nat.lt_succ_self _⟩ from Fin.ext (by dsimp; omega), hrComb_top]
      exact ht_in
  have hdisj_mid_comb : rMid.DisjointWires rComb := QRegister.disjoint_iff.mpr fun i idx heq ↦ by
    by_cases hlt : idx.val < sp.L.length
    · rw [show idx = ⟨idx.val, Nat.lt_succ_of_lt hlt⟩ from Fin.ext rfl,
      hrComb_low idx.val hlt] at heq
      exact hMidPool.ne i _ heq
    · rw [show idx = ⟨sp.L.length, Nat.lt_succ_self _⟩ from Fin.ext (by dsimp; omega),
      hrComb_top] at heq
      exact hActMid.ne sp.tIdx i heq.symm
  have hs_anc_comb : sp.s.anc = rComb ⟨0 + sp.L.length, by omega⟩ := by
    simpa only [Nat.zero_add] using hs_anc.trans hrComb_top.symm
  have hrComb_tail1 : rComb.slice (0 + sp.L.length) 1 (by omega) =
      QRegister.singleton sp.s.anc := by
    ext idx; fin_cases idx
    simp only [QRegister.slice_apply]
    exact congrArg Fin.val hs_anc_comb.symm
  have hrComb_all : rComb.slice 0 (sp.L.length + 1) (by omega) = rComb := by
    ext idx; simp [GridGuard654ReflAlt.qreg_block_apply]
  obtain ⟨hperm_fwd, hout_fwd, hwp_fwd, _⟩ :=
    symWrapList_correct (m_inner := 1) v ({sp.s.anc} : Finset (Wire n)) rComb 0 sp.L
      (by omega) hvalid
      (symStepComputeDyn sp.s) (symStepRootCircuit sp.s) sp.s.stepFwd
      (symStepRootCircuit_perm sp.s)
      (fun β w hw ↦ hs_pres β w (Finset.notMem_singleton.mp hw))
      (fun Ψ _ ↦ by rw [hrComb_tail1]; exact restrictZero_wp_symStepComputeDyn sp.s Ψ)
      (fun Ψ hΨ ↦ wp_symStepComputeDyn_update_eq v sp.s Ψ hΨ)
  let cFwd := symWrapCircuitList sp.L (symStepRootCircuit sp.s)
  let f_fwd : BitAssignment n → BitAssignment n := fun β w ↦
    if w ∈ ({sp.s.anc} : Finset (Wire n)) then sp.s.stepFwd (symStepFwdList sp.L β) w else β w
  have hcFwd_disj_mid : Disjoint cFwd.support rMid.image := by
    have hsub := symWrapCircuitList_support_sub sp.L (symStepRootCircuit sp.s)
      (Finset.univ \ rMid.image)
      ((symStepRootCircuit_support_sub sp.s).trans fun w hw ↦
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, Finset.disjoint_left.mp hs_mid hw⟩)
      (fun u hu w hw ↦
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, Finset.disjoint_left.mp (hL_mid u hu) hw⟩)
    exact Finset.disjoint_left.mpr fun w hw hm ↦ (Finset.mem_sdiff.mp (hsub hw)).2 hm
  let pred' : BitAssignment k_act → Bool := sp.togglePred pred
  let P' := rClean'.basisOutcomeProjector 0
  let P_clean := rClean.basisOutcomeProjector 0
  let P_comb := rComb.basisOutcomeProjector 0
  let U_old := ((rAct.concat rMid hActMid).embedUnitary (muxFlagUnitary pred u₀ u₁)).1
  let U_new := ((rAct.concat rMid hActMid).embedUnitary (muxFlagUnitary pred' u₀ u₁)).1
  have hP'_herm : P'ᴴ = P' := rClean'.basisOutcomeProjector_conjTranspose 0
  have hP_comb_herm : P_combᴴ = P_comb := rComb.basisOutcomeProjector_conjTranspose 0
  obtain ⟨hP'_clean_r, hP'_clean_l⟩ := proj_zero_absorb_of_image_subset hClean_sub
  obtain ⟨hP'_comb_r, hP'_comb_l⟩ := proj_zero_absorb_of_image_subset hrComb_sub
  have hcFwd_comm_clean : cFwd.eval.1 * P_clean = P_clean * cFwd.eval.1 :=
    classicalPerm_comm_proj_zero rClean hperm_fwd fun β j ↦
      hout_fwd β (rClean j) (Finset.notMem_singleton.mpr fun heq ↦
        ht_not_clean ((QRegister.mem_image rClean _).mpr ⟨j, heq.trans hs_anc⟩))
  have hcFwd_adj_comm_clean : P_clean * cFwd.eval.1ᴴ = cFwd.eval.1ᴴ * P_clean := by
    simpa only [P_clean, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
      congrArg conjTranspose hcFwd_comm_clean
  have hU_new_comm_comb : U_new * P_comb = P_comb * U_new := by
    apply matrix_ext_basisKet; intro δ
    let V_δ := if pred' (fun i ↦ δ (rAct i)) then u₁ else u₀
    have hcommV : (rMid.embedUnitary V_δ).1 * P_comb = P_comb * (rMid.embedUnitary V_δ).1 :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rMid) rComb hdisj_mid_comb V_δ.1 0
    have hUδ : U_new.mulVec (basisKet δ) = (rMid.embedUnitary V_δ).1.mulVec (basisKet δ) :=
      embed_muxFlagUnitary_mulVec_basisKet rAct rMid hActMid pred' u₀ u₁ δ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUδ,
      Matrix.mulVec_mulVec (basisKet δ) P_comb, ← hcommV, ← Matrix.mulVec_mulVec]
    dsimp only [P_comb]
    rw [register_basisOutcomeProjector_zero_mulVec_basisKet]
    by_cases h0 : ∀ j, δ (rComb j) = 0
    · rw [ite_eq_left h0, hUδ]
    · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hU_new_adj_comm_comb : P_comb * U_newᴴ = U_newᴴ * P_comb := by
    simpa only [conjTranspose_mul, hP_comb_herm] using congrArg conjTranspose hU_new_comm_comb
  have hintertwine : U_old * cFwd.eval.1 * P' = cFwd.eval.1 * U_new * P' := by
    apply matrix_ext_basisKet; intro β
    simp only [← Matrix.mulVec_mulVec]
    dsimp only [P']
    rw [register_basisOutcomeProjector_zero_mulVec_basisKet]
    by_cases h0' : ∀ j, β (rClean' j) = 0
    · rw [ite_eq_left h0']
      have h0_comb : ∀ j, β (rComb j) = 0 := fun j ↦ by
        rcases (QRegister.mem_image rClean' (rComb j)).mp
          (hrComb_sub ((QRegister.mem_image rComb _).mpr ⟨j, rfl⟩)) with ⟨u, hu⟩
        rw [← hu]; exact h0' u
      have hf_act : (fun i ↦ f_fwd β (rAct i)) = Function.update (fun i ↦ β (rAct i)) sp.tIdx
          (β (rAct sp.tIdx) + if sp.pred (fun i ↦ β (rAct i)) then 1 else 0) := by
        funext i
        by_cases hi : i = sp.tIdx
        · subst hi
          dsimp only [f_fwd]
          rw [hs_anc, ite_eq_left (Finset.mem_singleton_self _), Function.update_self,
            hroot_eval β h0_comb, ← hrComb_top, h0_comb ⟨sp.L.length, Nat.lt_succ_self _⟩, zero_add]
        · dsimp only [f_fwd]
          rw [ite_eq_right (Finset.notMem_singleton.mpr (by
              rw [hs_anc]; exact fun h ↦ hi (rAct.wires.injective h))),
            Function.update_of_ne hi]
      let V_β := if pred' (fun i ↦ β (rAct i)) then u₁ else u₀
      have hpred_match : pred (fun i ↦ f_fwd β (rAct i)) = pred' (fun i ↦ β (rAct i)) := by
        dsimp only [pred', DirectRootSpec.togglePred]; rw [hf_act]
      rw [hperm_fwd β, embed_muxFlagUnitary_mulVec_basisKet, hpred_match,
        embed_muxFlagUnitary_mulVec_basisKet]
      change (rMid.embedUnitary V_β).1.mulVec (basisKet (f_fwd β)) =
        cFwd.eval.1.mulVec ((rMid.embedUnitary V_β).1.mulVec (basisKet β))
      rw [Matrix.mulVec_mulVec]
      change _ = (cFwd.eval.1 * rMid.embedMatrix V_β.1).mulVec (basisKet β)
      rw [eval_comm_embedMatrix_of_disjoint_support cFwd rMid hcFwd_disj_mid V_β.1,
        ← Matrix.mulVec_mulVec, hperm_fwd β]
      rfl
    · rw [ite_eq_right h0', Matrix.mulVec_zero, Matrix.mulVec_zero,
        Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hintertwine_adj : P' * cFwd.eval.1ᴴ * U_oldᴴ = P' * U_newᴴ * cFwd.eval.1ᴴ := by
    simpa only [conjTranspose_mul, hP'_herm, Matrix.mul_assoc] using
      congrArg conjTranspose hintertwine
  intro M
  obtain ⟨M₁, hM₁⟩ := StoreConst.symWrapDynList v sp.L (storeConst_symStepUncomputeDyn v sp.s) M
  obtain ⟨M₂, hM₂, hInner_eq⟩ := hInner M₁
  obtain ⟨M₃, hM₃⟩ := StoreConst.symWrapDynList v sp.L (storeConst_symStepComputeDyn sp.s) M₂
  refine ⟨M₃, by
    dsimp only [directRootWrapDyn]
    simp only [DynamicCircuit.compile_seq, wp_qSeq,
      hM₁, hM₂, hM₃], ?_⟩
  let σ₀ : Store Var := fun _ ↦ 0
  have hA_comb : P_comb * M₃.1.1 * P_comb =
      P_comb * (cFwd.eval.1ᴴ * M₂.1.1 * cFwd.eval.1) * P_comb := by
    have h := hwp_fwd (fun _ ↦ M₂) (fun _ _ ↦ rfl)
    rw [hrComb_all, hM₃] at h
    have h1 := congrArg (fun A ↦ (A σ₀).1) h
    simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose] at h1
    simpa [P_comb, Matrix.mul_assoc, hP_comb_herm] using congrArg Subtype.val h1
  have hD_comb : P_comb * (cFwd.eval.1ᴴ * M₁.1.1 * cFwd.eval.1) * P_comb =
      P_comb * M.1.1 * P_comb := by
    have h := restrictZero_wp_cFwd_uncompute_cancel v rComb sp.s hs_pres 0 sp.L (by omega)
      hvalid hs_anc_comb (fun _ ↦ M) (fun _ _ ↦ rfl)
    rw [hrComb_all, hM₁] at h
    have h1 := congrArg (fun A ↦ (A σ₀).1) h
    simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose] at h1
    simpa [P_comb, Matrix.mul_assoc, hP_comb_herm] using congrArg Subtype.val h1
  have hSandwich {P_sub W X Y : Operator (2 ^ n)}
      (hPr : P' * P_sub = P') (hPl : P_sub * P' = P')
      (hWc : W * P_sub = P_sub * W) (hWa : P_sub * Wᴴ = Wᴴ * P_sub)
      (hXY : P_sub * X * P_sub = P_sub * Y * P_sub) :
      (P' * Wᴴ) * X * (W * P') = (P' * Wᴴ) * Y * (W * P') := by
    have hL : (P' * Wᴴ) * P_sub = P' * Wᴴ := by
      rw [Matrix.mul_assoc, ← hWa, ← Matrix.mul_assoc, hPr]
    have hR : P_sub * (W * P') = W * P' := by
      rw [← Matrix.mul_assoc, ← hWc, Matrix.mul_assoc, hPl]
    have hw (Z : Operator (2 ^ n)) :
        (P' * Wᴴ) * Z * (W * P') = (P' * Wᴴ) * (P_sub * Z * P_sub) * (W * P') := by
      calc (P' * Wᴴ) * Z * (W * P')
          = ((P' * Wᴴ) * P_sub) * Z * (P_sub * (W * P')) := by rw [hL, hR]
        _ = (P' * Wᴴ) * (P_sub * Z * P_sub) * (W * P') := by simp only [Matrix.mul_assoc]
    rw [hw X, hXY, ← hw Y]
  have hStepA : P' * M₃.1.1 * P' = P' * cFwd.eval.1ᴴ * M₂.1.1 * cFwd.eval.1 * P' := by
    simpa only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc] using
      hSandwich (W := 1) hP'_comb_r hP'_comb_l (by simp) (by simp) hA_comb
  have hStepB : P' * cFwd.eval.1ᴴ * M₂.1.1 * cFwd.eval.1 * P' =
      (P' * cFwd.eval.1ᴴ * U_oldᴴ) * M₁.1.1 * (U_old * cFwd.eval.1 * P') := by
    simpa only [Matrix.mul_assoc] using
      hSandwich hP'_clean_r hP'_clean_l hcFwd_comm_clean hcFwd_adj_comm_clean hInner_eq
  have hStepD : (P' * U_newᴴ * cFwd.eval.1ᴴ) * M₁.1.1 * (cFwd.eval.1 * U_new * P') =
      P' * (U_newᴴ * M.1.1 * U_new) * P' := by
    simpa only [Matrix.mul_assoc] using
      hSandwich hP'_comb_r hP'_comb_l hU_new_comm_comb hU_new_adj_comm_comb hD_comb
  rw [hStepA, hStepB, hintertwine, hintertwine_adj, hStepD]
theorem ladderStepAt_anc {n p : ℕ} (negIn : Bool) (inWires : Fin (p + 2) → Wire n)
    (hinj : Function.Injective inWires) (rAnc : QRegister (p + 1) n)
    (hdisj : ∀ t, inWires t ∉ rAnc.image) (j : Fin (p + 1)) :
    (ladderStepAt negIn inWires hinj rAnc hdisj j).anc = rAnc j := by
  unfold ladderStepAt; split_ifs <;> rfl
theorem ladderStepAt_preserves {n p : ℕ} (negIn : Bool) (inWires : Fin (p + 2) → Wire n)
    (hinj : Function.Injective inWires) (rAnc : QRegister (p + 1) n)
    (hdisj : ∀ t, inWires t ∉ rAnc.image) (j : Fin (p + 1)) : PreservesNonAnc
    (ladderStepAt negIn inWires hinj rAnc hdisj j) := fun β w hw ↦
    ladderStepAt_preservesNonAnc negIn inWires hinj rAnc hdisj j β w hw
theorem ladderSteps_eq_prefix_append_last {n p : ℕ} (negIn : Bool)
    (inWires : Fin (p + 2) → Wire n) (hinj : Function.Injective inWires)
    (rAnc : QRegister (p + 1) n) (hdisj : ∀ t, inWires t ∉ rAnc.image) :
    ladderPrefix negIn inWires hinj rAnc hdisj p (Nat.le_succ p) ++
      [ladderStepAt negIn inWires hinj rAnc hdisj ⟨p, Nat.lt_succ_self p⟩] =
    ladderSteps negIn inWires hinj rAnc hdisj := by
  unfold ladderSteps
  rfl
theorem mem_ladderPrefix_S_sub {n p : ℕ} (negIn : Bool)
    (inWires : Fin (p + 2) → Wire n) (hinj : Function.Injective inWires)
    (rAnc : QRegister (p + 1) n) (hdisj : ∀ t, inWires t ∉ rAnc.image) :
    ∀ (t : ℕ) (ht : t ≤ p + 1) (u : SymTempAndStep n),
      u ∈ ladderPrefix negIn inWires hinj rAnc hdisj t ht →
      u.S ⊆ rAnc.image ∪ Finset.univ.image inWires
  | 0, _, _, hu => by simp [ladderPrefix] at hu
  | t + 1, ht, u, hu => by
      dsimp only [ladderPrefix] at hu
      rcases List.mem_append.mp hu with h1 | h2
      · exact mem_ladderPrefix_S_sub negIn inWires hinj rAnc hdisj t (by omega) u h1
      · rw [List.mem_singleton.mp h2]
        intro w hw
        dsimp only [ladderStepAt] at hw
        split_ifs at hw with hj0
        · simp only [litAndSymStep, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact Finset.mem_union_right _ (Finset.mem_image_of_mem inWires (Finset.mem_univ _))
          · exact Finset.mem_union_right _ (Finset.mem_image_of_mem inWires (Finset.mem_univ _))
          · exact Finset.mem_union_left _ ((QRegister.mem_image rAnc _).mpr ⟨_, rfl⟩)
        · simp only [litAndSymStep, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact Finset.mem_union_left _ ((QRegister.mem_image rAnc _).mpr ⟨_, rfl⟩)
          · exact Finset.mem_union_right _ (Finset.mem_image_of_mem inWires (Finset.mem_univ _))
          · exact Finset.mem_union_left _ ((QRegister.mem_image rAnc _).mpr ⟨_, rfl⟩)
theorem ancZeroInWires_injective {n m_be : ℕ} (hbe : 2 ≤ m_be) (rAncBE : QRegister m_be n) :
    Function.Injective (fun t : Fin ((m_be - 2) + 2) ↦ rAncBE ⟨t.val, by omega⟩) :=
  fun _ _ h ↦ Fin.ext (by simpa using congrArg Fin.val (rAncBE.wires.injective h))
abbrev ancZeroComb0 {n k_act m_be m_pool : ℕ}
    (rAct : QRegister k_act n) (rPool : QRegister m_pool n)
    (tIdx : Fin k_act) (hfit : m_be - 2 ≤ m_pool)
    (hActPool : rAct.DisjointWires rPool) : QRegister ((m_be - 2) + 1) n :=
  let rPoolSub := rPool.slice 0 (m_be - 2) (by omega)
  rPoolSub.concat (QRegister.singleton (rAct tIdx))
    (disjointWires_singleton_of_not_mem rPoolSub (rAct tIdx)
      ((hActPool.compose_right _).apply_not_mem_right tIdx))
theorem ancZeroInWires_ne_comb0 {n k_act m_be m_pool : ℕ} (hbe : 2 ≤ m_be)
    (rAct : QRegister k_act n) (rPool : QRegister m_pool n) (rAncBE : QRegister m_be n)
    (tIdx : Fin k_act) (ancIdx : Fin m_be → Fin k_act)
    (hanc_eq : ∀ j, rAncBE j = rAct (ancIdx j)) (hne_tIdx : ∀ j, ancIdx j ≠ tIdx)
    (hfit : m_be - 2 ≤ m_pool) (hActPool : rAct.DisjointWires rPool)
    (t : Fin ((m_be - 2) + 2)) (u : Fin ((m_be - 2) + 1)) :
    rAncBE ⟨t.val, by omega⟩ ≠ (ancZeroComb0 rAct rPool tIdx hfit hActPool) u := by
  intro heq
  rw [hanc_eq ⟨t.val, by omega⟩] at heq
  by_cases hlt : u.val < m_be - 2
  · rw [show u = Fin.castAdd 1 ⟨u.val, hlt⟩ from Fin.ext rfl, QRegister.concat_apply_left] at heq
    exact (hActPool.compose_right _).ne _ _ heq
  · rw [show u = Fin.natAdd (m_be - 2) (0 : Fin 1) from Fin.ext (by dsimp; omega),
      QRegister.concat_apply_right] at heq
    exact hne_tIdx ⟨t.val, by omega⟩ (rAct.wires.injective heq)
def ancZeroDirectRootSpec {n k_act m_be m_pool : ℕ}
    (hbe : 2 ≤ m_be)
    (rAct : QRegister k_act n) (rPool : QRegister m_pool n)
    (rAncBE : QRegister m_be n)
    (tIdx : Fin k_act)
    (ancIdx : Fin m_be → Fin k_act)
    (hanc_eq : ∀ j, rAncBE j = rAct (ancIdx j))
    (hne_tIdx : ∀ j, ancIdx j ≠ tIdx)
    (hfit : m_be - 2 ≤ m_pool)
    (hActPool : rAct.DisjointWires rPool) :
    DirectRootSpec (n := n) k_act :=
  let p := m_be - 2
  let rComb0 := ancZeroComb0 rAct rPool tIdx hfit hActPool
  let rComb := rComb0.slice 0 (p + 1) (Nat.zero_add (p + 1)).le
  let inWires : Fin (p + 2) → Wire n := fun t ↦ rAncBE ⟨t.val, by omega⟩
  have hdisj_in : ∀ t, inWires t ∉ rComb.image := fun t hm ↦ by
    rcases (QRegister.mem_image rComb0 _).mp (QRegister.image_compose_subset rComb0 _ hm) with
      ⟨u, hu⟩
    exact ancZeroInWires_ne_comb0 hbe rAct rPool rAncBE tIdx ancIdx hanc_eq hne_tIdx hfit
      hActPool t u hu.symm
  { L := ladderPrefix true inWires (ancZeroInWires_injective hbe rAncBE) rComb hdisj_in p (by omega)
    s :=
      ladderStepAt true inWires (ancZeroInWires_injective hbe rAncBE) rComb hdisj_in ⟨p, by omega⟩
    tIdx := tIdx
    pred := fun γ ↦ decide (∀ j : Fin m_be, γ (ancIdx j) = 0)
    hpred := fun γ val ↦ by
      simp only [fun j ↦ Function.update_of_ne (hne_tIdx j) val γ] }
theorem ancZeroDirectRootSpec_L_length {n k_act m_be m_pool : ℕ} (hbe : 2 ≤ m_be)
    (rAct : QRegister k_act n) (rPool : QRegister m_pool n) (rAncBE : QRegister m_be n)
    (tIdx : Fin k_act) (ancIdx : Fin m_be → Fin k_act)
    (hanc_eq : ∀ j, rAncBE j = rAct (ancIdx j)) (hne_tIdx : ∀ j, ancIdx j ≠ tIdx)
    (hfit : m_be - 2 ≤ m_pool) (hActPool : rAct.DisjointWires rPool) : (ancZeroDirectRootSpec
    hbe rAct rPool rAncBE tIdx ancIdx hanc_eq hne_tIdx hfit hActPool).L.length = m_be - 2 :=
    ladderPrefix_length ..
theorem ancZeroDirectRootSpec_realizes {n k_act k_mid m_be m_pool : ℕ} (hbe : 2 ≤ m_be)
    (rAct : QRegister k_act n) (rMid : QRegister k_mid n) (rPool : QRegister m_pool n)
    (rAncBE : QRegister m_be n) (tIdx : Fin k_act) (ancIdx : Fin m_be → Fin k_act)
    (hanc_eq : ∀ j, rAncBE j = rAct (ancIdx j)) (hne_tIdx : ∀ j, ancIdx j ≠ tIdx)
    (hfit : m_be - 2 ≤ m_pool) (hActMid : rAct.DisjointWires rMid)
    (hActPool : rAct.DisjointWires rPool) (hMidPool : rMid.DisjointWires rPool) :
    DirectRootSpecRealizes rAct rMid rPool (ancZeroDirectRootSpec hbe rAct rPool rAncBE tIdx
    ancIdx hanc_eq hne_tIdx hfit hActPool) := by
  let sp := ancZeroDirectRootSpec hbe rAct rPool rAncBE tIdx ancIdx hanc_eq hne_tIdx hfit hActPool
  let p := m_be - 2
  let rComb0 := ancZeroComb0 rAct rPool tIdx hfit hActPool
  let rComb := rComb0.slice 0 (p + 1) (Nat.zero_add (p + 1)).le
  let inWires : Fin (p + 2) → Wire n := fun t ↦ rAncBE ⟨t.val, by omega⟩
  let hinj : Function.Injective inWires := ancZeroInWires_injective hbe rAncBE
  have hdisj_in : ∀ t, inWires t ∉ rComb.image := fun t hm ↦ by
    rcases (QRegister.mem_image rComb0 _).mp (QRegister.image_compose_subset rComb0 _ hm) with
      ⟨u, hu⟩
    exact ancZeroInWires_ne_comb0 hbe rAct rPool rAncBE tIdx ancIdx hanc_eq hne_tIdx hfit
      hActPool t u hu.symm
  obtain ⟨hv_all, hs_all⟩ := ladderSteps_spec true inWires hinj rComb0 0
    (Nat.zero_add (p + 1)).le ∅ (fun _ ↦ Finset.notMem_empty _) (Finset.disjoint_empty_right _)
    (fun t j _ ↦ ancZeroInWires_ne_comb0 hbe rAct rPool rAncBE tIdx ancIdx hanc_eq hne_tIdx hfit
      hActPool t j)
  have hlen : sp.L.length = p := ancZeroDirectRootSpec_L_length ..
  have hrComb0_top : rComb0 ⟨p, by omega⟩ = rAct tIdx := by
    rw [show (⟨p, by omega⟩ : Fin (p + 1)) = Fin.natAdd p (0 : Fin 1) from Fin.ext rfl,
      QRegister.concat_apply_right]
    rfl
  have hs_anc : sp.s.anc = rAct tIdx := by
    dsimp only [sp, ancZeroDirectRootSpec]
    rw [ladderStepAt_anc, QRegister.slice_apply]
    simpa only [Nat.zero_add] using hrComb0_top
  have happ_eq : sp.L ++ [sp.s] = ladderSteps true inWires hinj rComb hdisj_in :=
    ladderSteps_eq_prefix_append_last true inWires hinj rComb hdisj_in
  have hvalid_L : ValidSymStepList ({sp.s.anc} : Finset (Wire n)) rComb0 0 sp.L :=
    validSymStepList_init_target 0 sp.L (by rw [hlen]; omega) (happ_eq ▸ hv_all) (by
      rw [hs_anc, show (⟨0 + sp.L.length, by rw [hlen]; omega⟩ : Fin (p + 1)) = ⟨p, by omega⟩ from
        Fin.ext (by dsimp; omega), hrComb0_top])
  have hcomb_disj_mid : Disjoint (rComb.image ∪ Finset.univ.image inWires) rMid.image := by
    rw [Finset.disjoint_union_left]
    refine ⟨Finset.disjoint_of_subset_left (QRegister.image_compose_subset rComb0 _)
      (Finset.disjoint_left.mpr fun w hw ↦ ?_), Finset.disjoint_left.mpr fun w hw ↦ ?_⟩
    · rcases (QRegister.mem_image rComb0 w).mp hw with ⟨u, rfl⟩
      by_cases hlt : u.val < p
      · rw [show u = Fin.castAdd 1 ⟨u.val, hlt⟩ from Fin.ext rfl, QRegister.concat_apply_left]
        exact (hMidPool.compose_right _).apply_not_mem_left _
      · rw [show u = Fin.natAdd p (0 : Fin 1) from Fin.ext (by dsimp; omega),
          QRegister.concat_apply_right]
        exact hActMid.apply_not_mem_right tIdx
    · rcases Finset.mem_image.mp hw with ⟨t, _, rfl⟩
      dsimp only [inWires]
      rw [hanc_eq]
      exact hActMid.apply_not_mem_right _
  have hs_mem_all : sp.s ∈ ladderPrefix true inWires hinj rComb hdisj_in (p + 1) le_rfl := by
    dsimp only [sp, ancZeroDirectRootSpec, ladderPrefix]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨by rw [hlen]; exact hfit, p + 1, by rw [hlen], rComb0,
    fun j hj ↦ ?_, ?_, hs_anc,
    ladderStepAt_preserves true inWires hinj rComb hdisj_in ⟨p, by omega⟩, hvalid_L,
    Finset.disjoint_of_subset_left
      (mem_ladderPrefix_S_sub true inWires hinj rComb hdisj_in (p + 1) le_rfl sp.s hs_mem_all)
      hcomb_disj_mid,
    fun u hu ↦ Finset.disjoint_of_subset_left
      (mem_ladderPrefix_S_sub true inWires hinj rComb hdisj_in p (by omega) u hu) hcomb_disj_mid,
    fun β h0 ↦ ?_⟩
  · rw [show (⟨j, (by rw [hlen] : sp.L.length + 1 = p + 1) ▸ Nat.lt_succ_of_lt hj⟩ : Fin (p + 1)) =
        Fin.castAdd 1 ⟨j, by rw [← hlen]; exact hj⟩ from Fin.ext rfl,
      QRegister.concat_apply_left, QRegister.slice_apply]
    exact congrArg rPool.wires (Fin.ext (by simp))
  · rw [show (⟨sp.L.length, (by rw [hlen] : sp.L.length + 1 = p + 1) ▸ Nat.lt_succ_self _⟩ :
        Fin (p + 1)) = ⟨p, by omega⟩ from Fin.ext hlen, hrComb0_top]
    rfl
  · change sp.s.stepFwd (symStepFwdList sp.L β) (rAct tIdx) =
      if sp.pred (fun i ↦ β (rAct i)) = true then 1 else 0
    obtain ⟨_, hlad⟩ := hs_all β fun j ↦ by rw [QRegister.slice_apply]; exact h0 _
    have hrComb_p : (rComb0.slice 0 (p + 1) (Nat.zero_add (p + 1)).le) ⟨p, by omega⟩ =
        rAct tIdx := by
      rw [QRegister.slice_apply]; simpa only [Nat.zero_add] using hrComb0_top
    rw [hrComb_p] at hlad
    change symStepFwdList (ladderSteps true inWires hinj rComb hdisj_in) β (rAct tIdx) = _ at hlad
    have happ : sp.s.stepFwd (symStepFwdList sp.L β) =
        symStepFwdList (ladderSteps true inWires hinj rComb hdisj_in) β := by
      rw [show sp.s.stepFwd (symStepFwdList sp.L β) = symStepFwdList (sp.L ++ [sp.s]) β from by
        rw [symStepFwdList_append]; rfl, happ_eq]
    rw [congrFun happ (rAct tIdx), hlad]
    have hiff : (∀ t : Fin (p + 2), polBit true (β (inWires t)) = 1) ↔
        sp.pred (fun i ↦ β (rAct i)) = true := by
      dsimp only [sp, ancZeroDirectRootSpec]
      simp only [decide_eq_true_iff, polBit, ↓reduceIte]
      have hz0 : ∀ b : ZMod 2, b + 1 = 1 ↔ b = 0 := by decide
      exact ⟨fun hall j ↦ by simpa only [← hanc_eq j] using (hz0 _).mp (hall ⟨j.val, by omega⟩),
        fun hall t ↦ (hz0 _).mpr (by
          rw [show inWires t = rAncBE ⟨t.val, by omega⟩ from rfl, hanc_eq]
          exact hall ⟨t.val, by omega⟩)⟩
    by_cases hc : sp.pred (fun i ↦ β (rAct i)) = true
    · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]
    · rw [ite_eq_right (mt hiff.mp hc), ite_eq_right hc]
end DirectRootEngine
section ParametricGuardWrap
theorem disjointWires_of_concat_left {k₁ k₂ k₃ n : ℕ} {r₁ : QRegister k₁ n}
    {r₂ : QRegister k₂ n} {r₃ : QRegister k₃ n} {h₁₂ : r₁.DisjointWires r₂}
    (h : (r₁.concat r₂ h₁₂).DisjointWires r₃) : r₁.DisjointWires r₃ :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ h.ne (Fin.castAdd k₂ i) j
    ((QRegister.concat_apply_left r₁ r₂ h₁₂ i).trans hij)
theorem disjointWires_of_concat_right {k₁ k₂ k₃ n : ℕ} {r₁ : QRegister k₁ n}
    {r₂ : QRegister k₂ n} {r₃ : QRegister k₃ n} {h₁₂ : r₁.DisjointWires r₂}
    (h : (r₁.concat r₂ h₁₂).DisjointWires r₃) : r₂.DisjointWires r₃ :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ h.ne (Fin.natAdd k₁ i) j
    ((QRegister.concat_apply_right r₁ r₂ h₁₂ i).trans hij)
theorem disjoint_image_of_disjointWires {k₁ k₂ n : ℕ} {r₁ : QRegister k₁ n}
    {r₂ : QRegister k₂ n} (h : r₁.DisjointWires r₂) : Disjoint r₁.image r₂.image := by
  rw [← QRegExt.disjointWires_iff_disjoint_image]
  exact h
def beSysReg (mPayload : ℕ) : QRegister systemQubits (fullSysBEWires mPayload) :=
  .block 0 systemQubits (by simp [fullSysBEWires, fullSysRawAncWires, systemQubits])
def beAncReg (mPayload : ℕ) : QRegister (fullSysRawAncWires mPayload)
    (fullSysBEWires mPayload) := .block systemQubits (fullSysRawAncWires mPayload) le_rfl
end ParametricGuardWrap
end GridGuard654Flag288
end
end ModGridGuard654Flag288

end QuantumComputation.Specs.StoppingPowerSolution
