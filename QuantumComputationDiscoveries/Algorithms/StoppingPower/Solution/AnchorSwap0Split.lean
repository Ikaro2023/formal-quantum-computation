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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.AnchorTable218


@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section AnchorSwap0Split133_p1
local instance (priority := 1000000) instNeZeroTwoPow_AnchorSwap0Split133_p1 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `133`-Wire (`18 + 115`) `72 + 54` Split Anchor Swap-0 Bridge (`AnchorSwap0Split133`)

Row-aligned `72 + 54 = 126` (`4 × 18 + 3 × 18`) 2-batch diagonal load split in `115` clean work
wires (`18 + 115 = 133 ≤ mWork`):

1. **`dAnchorSwap0Conj115Unclamped`** (`133 ≤ mWork`):
   - Realizes `HoistedSwapSelectBridge.unitaryConj (uSwap0Gen selMux aliasIdx218 _) uInner`
     with `.TOFF = dInner.count PrimitiveGate.TOFF` and `.T ≤ 8748 + dInner.count PrimitiveGate.T`
     (`8,224` load + `524` phase-fix).
2. **`dAnchorSwap0Conj115Clamped`** (`133 ≤ mWork`):
   - Realizes `HoistedSwapSelectBridge.unitaryConj (uSwap0Gen selMux clampIdx218 _) uInner`
     with `.TOFF = dInner.count PrimitiveGate.TOFF` and `.T ≤ 8788 + dInner.count PrimitiveGate.T`
     (`8,260` load + `528` phase-fix).
-/

public section

namespace AnchorSwap0Split133

section ConfigAnchorSwap0Split133
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

local instance (priority :=
  1000000) instLoc_AnchorSwap0Split133_1InstNeZeroTwoPowAnchorS (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open Real
open OctahedralOrbit hiding
  ket eval_seq_mulVec ket_X ket_CNOT ket_TOFF matrix_ext_ket ket_projector_zero
open Dyadic128CoulombMath
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open MeasureBranchHadamardSem
  (ket ket_H bitSign bit_cases matrix_ext_ket eval_seq_mulVec ket_CNOT ket_TOFF ket_projector_zero
  projZeroAll ket_projZeroAll projZeroAll_eq_basisOutcomeProjector_zero)
open StreamingBchComparator BchCubeDecoder
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding
  ite_pos ite_neg dite_pos dite_neg
-- Root solution namespace already active.
open PosSlots24Barrel3Pass

attribute [local irreducible] cXorE0217Locked
/-- Helper declaration `p2d_writeReg` for the 133-wire 2D split anchor Swap-0 bridge. -/
noncomputable def p2d_writeReg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
theorem p2d_writeReg_apply_reg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : p2d_writeReg β r γ (r i) = γ i := by
  simp [p2d_writeReg, QRegister.basisBits_replaceIndex_apply]
theorem p2d_writeReg_apply_of_not_mem {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    p2d_writeReg β r γ w = β w := by
  simp [p2d_writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
/-- Helper declaration `p2d_ketPredProj` for the 133-wire 2D split anchor Swap-0 bridge. -/
noncomputable def p2d_ketPredProj {n : ℕ} (S : BitAssignment n → Prop) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  haveI := Classical.decPred S
  Matrix.diagonal (fun g : Fin (2 ^ n) ↦ if S (basisBits n g) then (1 : ℂ) else 0)
theorem p2d_ket_eq_single {n : ℕ} (β : BitAssignment n) :
    ket β = Pi.single ((basisBitsEquiv n).symm β) (1 : ℂ) := by
  funext y
  simp [ket, basisState]
theorem p2d_ketPredProj_conjTranspose {n : ℕ} (S : BitAssignment n → Prop) :
    (p2d_ketPredProj S)ᴴ = p2d_ketPredProj S := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hs : S (basisBits n i) <;> simp [p2d_ketPredProj, Matrix.diagonal, hs]
  · have hji : j ≠ i := Ne.symm hij
    simp [p2d_ketPredProj, Matrix.conjTranspose_apply, Matrix.diagonal, hij, hji]
theorem p2d_ketPredProj_mul_ket {n : ℕ} (S : BitAssignment n → Prop)
    [DecidablePred S] (β : BitAssignment n) :
    (p2d_ketPredProj S).mulVec (ket β) = if S β then ket β else 0 := by
  let g := (basisBitsEquiv n).symm β
  have hg : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  rw [p2d_ket_eq_single β]
  ext i
  dsimp only [p2d_ketPredProj]
  rw [Matrix.mulVec_diagonal]
  by_cases hig : i = g
  · rw [hig, hg]
    by_cases hs : S β <;> simp [hs, g]
  · by_cases hs : S β <;> by_cases hsi : S (basisBits n i) <;>
      simp [hig, hs, hsi, g]
theorem p2d_ketPredProj_mul_imp {n : ℕ} {S₁ S₂ : BitAssignment n → Prop}
    (h : ∀ β : BitAssignment n, S₁ β → S₂ β) :
    p2d_ketPredProj S₂ * p2d_ketPredProj S₁ = p2d_ketPredProj S₁ := by
  classical
  apply matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
  by_cases h1 : S₁ β
  · rw [ite_eq_left h1, p2d_ketPredProj_mul_ket, ite_eq_left (h β h1)]
  · rw [ite_eq_right h1, Matrix.mulVec_zero]
theorem p2d_ketPredProj_mul_imp_right {n : ℕ} {S₁ S₂ : BitAssignment n → Prop}
    (h : ∀ β : BitAssignment n, S₁ β → S₂ β) :
    p2d_ketPredProj S₁ * p2d_ketPredProj S₂ = p2d_ketPredProj S₁ := by
  have hc := congrArg conjTranspose (p2d_ketPredProj_mul_imp h)
  simpa only [Matrix.conjTranspose_mul, p2d_ketPredProj_conjTranspose] using hc
theorem p2d_projZeroAll_eq_ketPredProj {n k : ℕ} (scr : Fin k → Wire n) :
    projZeroAll k scr = p2d_ketPredProj (fun β ↦ ∀ j : Fin k, β (scr j) = 0) := by
  classical
  apply matrix_ext_ket
  intro β
  rw [ket_projZeroAll, p2d_ketPredProj_mul_ket]
theorem p2d_basisOutcomeProjector_zero_eq_ketPredProj {n k : ℕ} (r : QRegister k n) :
    r.basisOutcomeProjector 0 = p2d_ketPredProj (fun β ↦ ∀ j : Fin k, β (r j) = 0) := by
  rw [← projZeroAll_eq_basisOutcomeProjector_zero, p2d_projZeroAll_eq_ketPredProj]
/-- Helper declaration `p2d_RealizesConstCleanUnitary` for the 133-wire 2D split anchor Swap-0
  bridge. -/
def p2d_RealizesConstCleanUnitary {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (d : DynamicCircuit Var n)
    (U : Unitary (2 ^ n)) : Prop := PreservesStoreConst d ∧ ∀ M : Observable (Fin (2 ^ n)), ∀ σ :
    Store Var, P * (wp d.compile (fun _ ↦ M) σ).1.1 * P = P * (U.1ᴴ * M.1.1 * U.1) * P
theorem p2d_RealizesConstCleanUnitary_circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (c : Circuit n) :
    p2d_RealizesConstCleanUnitary (Var := Var) P (.circuit c) c.eval := by
  refine ⟨PreservesStoreConst.circuit c, fun M σ ↦ ?_⟩
  simp [DynamicCircuit.compile_circuit,
    wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc]
theorem p2d_RealizesConstCleanUnitary_mono_proj {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P_small P_big : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {d : DynamicCircuit Var n} {U : Unitary (2 ^ n)} (hPs : P_smallᴴ = P_small)
    (hPb : P_bigᴴ = P_big) (hsub : P_small * P_big = P_big)
    (hd : p2d_RealizesConstCleanUnitary P_small d U) : p2d_RealizesConstCleanUnitary P_big d U
    := by
  have hleft : P_big * P_small = P_big := by
    have h := congrArg conjTranspose hsub
    simpa [Matrix.conjTranspose_mul, hPs, hPb] using h
  refine ⟨hd.1, fun M σ ↦ ?_⟩
  calc P_big * (wp d.compile (fun _ ↦ M) σ).1.1 * P_big
      = P_big * (P_small * (wp d.compile (fun _ ↦ M) σ).1.1 * P_small) * P_big := by
          simp only [← Matrix.mul_assoc, hleft]; simp only [Matrix.mul_assoc, hsub]
    _ = P_big * (P_small * (U.1ᴴ * M.1.1 * U.1) * P_small) * P_big := by rw [hd.2 M σ]
    _ = P_big * (U.1ᴴ * M.1.1 * U.1) * P_big := by
          simp only [← Matrix.mul_assoc, hleft]; simp only [Matrix.mul_assoc, hsub]
theorem p2d_RealizesConstCleanUnitary_congr_unitary {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {d : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP : Pᴴ = P)
    (hd : p2d_RealizesConstCleanUnitary P d U₁) (heq : U₁.1 * P = U₂.1 * P) :
    p2d_RealizesConstCleanUnitary P d U₂ := by
  have hadj : P * U₁.1ᴴ = P * U₂.1ᴴ := by
    have h := congrArg conjTranspose heq
    simpa [Matrix.conjTranspose_mul, hP] using h
  refine ⟨hd.1, fun M σ ↦ ?_⟩
  rw [hd.2 M σ]
  calc P * (U₁.1ᴴ * M.1.1 * U₁.1) * P
      = (P * U₁.1ᴴ) * M.1.1 * (U₁.1 * P) := by simp only [Matrix.mul_assoc]
    _ = (P * U₂.1ᴴ) * M.1.1 * (U₂.1 * P) := by rw [hadj, heq]
    _ = P * (U₂.1ᴴ * M.1.1 * U₂.1) * P := by simp only [Matrix.mul_assoc]
theorem p2d_RealizesConstCleanUnitary_seq_proj {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P₁ P₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {d₁ d₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP₁ : P₁ᴴ = P₁) (hP₂ : P₂ᴴ = P₂)
    (h₁ : p2d_RealizesConstCleanUnitary P₁ d₁ U₁)
    (h₂ : p2d_RealizesConstCleanUnitary P₂ d₂ U₂) (hclean : P₂ * (U₁.1 * P₁) = U₁.1 * P₁) :
    p2d_RealizesConstCleanUnitary P₁ (.seq d₁ d₂) (U₂ * U₁) := by
  have hadj : P₁ * U₁.1ᴴ * P₂ = P₁ * U₁.1ᴴ := by
    have h := congrArg conjTranspose hclean
    simpa only [Matrix.conjTranspose_mul, hP₁, hP₂, Matrix.mul_assoc] using h
  refine ⟨PreservesStoreConst.seq h₁.1 h₂.1, fun M σ ↦ ?_⟩
  obtain ⟨M₂, hM₂⟩ := h₂.1 M
  have hSeqWp : wp (DynamicCircuit.seq d₁ d₂).compile (fun _ ↦ M) σ =
      wp d₁.compile (fun _ ↦ M₂) σ := by
    simp only [DynamicCircuit.compile_seq, wp_qSeq, hM₂]
  have hM₂_eq : M₂ = wp d₂.compile (fun _ ↦ M) σ := (congrFun hM₂ σ).symm
  rw [hSeqWp, h₁.2 M₂ σ]
  calc P₁ * (U₁.1ᴴ * M₂.1.1 * U₁.1) * P₁
      = (P₁ * U₁.1ᴴ) * M₂.1.1 * (U₁.1 * P₁) := by simp only [Matrix.mul_assoc]
    _ = (P₁ * U₁.1ᴴ * P₂) * M₂.1.1 * (P₂ * (U₁.1 * P₁)) := by rw [hadj, hclean]
    _ = (P₁ * U₁.1ᴴ) * (P₂ * M₂.1.1 * P₂) * (U₁.1 * P₁) := by simp only [Matrix.mul_assoc]
    _ = (P₁ * U₁.1ᴴ) * (P₂ * (U₂.1ᴴ * M.1.1 * U₂.1) * P₂) * (U₁.1 * P₁) := by rw [hM₂_eq, h₂.2 M σ]
    _ = (P₁ * U₁.1ᴴ * P₂) * (U₂.1ᴴ * M.1.1 * U₂.1) * (P₂ * (U₁.1 * P₁)) := by
          simp only [Matrix.mul_assoc]
    _ = P₁ * ((U₂ * U₁).1ᴴ * M.1.1 * (U₂ * U₁).1) * P₁ := by
          rw [hadj, hclean]
          simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
theorem p2d_RealizesConstCleanUnitary_toEmbeddedCleanWorkspace {Var : Type} [Fintype Var]
    [DecidableEq Var] {n k mClean : ℕ} [NeZero (2 ^ n)] (rData : QRegister k n)
    (rClean : QRegister mClean n) (uTarget : Unitary (2 ^ k)) (d : DynamicCircuit Var n) (hd :
    p2d_RealizesConstCleanUnitary (rClean.basisOutcomeProjector 0) d (rData.embedUnitary
    uTarget)) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData rClean uTarget
    d := by
  intro M
  obtain ⟨M', hWp⟩ := hd.1 M
  refine ⟨M', hWp, ?_⟩
  let σ₀ : Store Var := default
  have hEq := hd.2 M σ₀
  rw [congrFun hWp σ₀] at hEq
  exact hEq
theorem p2d_xResetKraus_mulVec_ket {n k : ℕ} (rOut : QRegister k n) (f : Fin k → Bool)
    (α : BitAssignment n) : (DynCircuitExt.xResetKraus rOut f).mulVec (ket α) = ((((√(1 / 2))
    ^ k : ℝ) : ℂ) * ∏ b : Fin k, if f b then (-1 : ℂ) ^ (α (rOut b)).val else 1) • ket
    (p2d_writeReg α rOut (fun _ ↦ 0)) := by
  let g := (basisBitsEquiv n).symm α
  have hgα : basisBits n g = α := (basisBitsEquiv n).apply_symm_apply α
  rw [p2d_ket_eq_single α, DynCircuitExt.xResetKraus_mulVec_single k rOut f g]
  refine congrArg₂ (· • ·) ?_ ?_
  · congr 1
    refine Finset.prod_congr rfl fun b _ ↦ ?_
    have hb : basisBits k (rOut.extractIndex g) b = α (rOut b) := by
      rw [QRegister.basisBits_extractIndex, hgα]
    rw [hb]
    cases f b <;> rcases bit_cases (α (rOut b)) with h | h <;> simp [h]
  · have hzero_symm : (basisBitsEquiv k).symm (fun _ : Fin k ↦ (0 : ZMod 2)) = 0 := by
      apply (basisBitsEquiv k).injective
      rw [(basisBitsEquiv k).apply_symm_apply]
      funext idx
      change _ = basisBits k (0 : Fin (2 ^ k)) idx
      simp [-Nat.reducePow, basisBits_eq_div_mod]
    have hrep : (basisBitsEquiv n).symm (p2d_writeReg α rOut (fun _ ↦ 0)) =
        rOut.replaceIndex g 0 := by
      dsimp only [p2d_writeReg, g]
      rw [hzero_symm]
      exact (basisBitsEquiv n).symm_apply_apply _
    rw [p2d_ket_eq_single (p2d_writeReg α rOut (fun _ ↦ 0)), hrep]
theorem p2d_RealizesConstCleanUnitary_seq_measureXReset {Var : Type} [Fintype Var]
    [DecidableEq Var] {n k : ℕ} [NeZero (2 ^ n)] (v : Var) (rOut : QRegister k n)
    {P_pre P_post : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {dPre : DynamicCircuit Var n}
    {cont : (Fin k → Bool) → DynamicCircuit Var n} {U_pre U_target : Unitary (2 ^ n)}
    {U_fix : (Fin k → Bool) → Unitary (2 ^ n)} (hPreH : P_preᴴ = P_pre)
    (hPostH : P_postᴴ = P_post) (hdPre : p2d_RealizesConstCleanUnitary P_pre dPre U_pre)
    (hdCont : ∀ f : Fin k → Bool, p2d_RealizesConstCleanUnitary P_post (cont f) (U_fix f))
    (hPostClean : ∀ f : Fin k → Bool, P_post * (DynCircuitExt.xResetKraus rOut f * U_pre.1 *
    P_pre) = DynCircuitExt.xResetKraus rOut f * U_pre.1 * P_pre) (hBranch : ∀ f : Fin k →
    Bool, ((U_fix f).1 * DynCircuitExt.xResetKraus rOut f * U_pre.1) * P_pre = ((((√(1 / 2))
    ^ k : ℝ) : ℂ)) • (U_target.1 * P_pre)) : p2d_RealizesConstCleanUnitary P_pre
    (.seq dPre (DynCircuitExt.measureXResetAndBranch v k rOut cont)) U_target := by
  have hConstAll : PreservesStoreConst
      (.seq dPre (DynCircuitExt.measureXResetAndBranch v k rOut cont)) := by
    intro M
    choose MCont hCont_wp using fun f ↦ (hdCont f).1 M
    obtain ⟨MMid, hMid_wp, _⟩ :=
      DynCircuitExt.wp_measureXResetAndBranch_const v k rOut cont M MCont hCont_wp
    obtain ⟨M', hPre_wp⟩ := hdPre.1 MMid
    refine ⟨M', funext fun σ ↦ ?_⟩
    change wp (DynamicCircuit.seq dPre (DynCircuitExt.measureXResetAndBranch v k rOut cont)).compile
      (fun _ ↦ M) σ = M'
    simp only [DynamicCircuit.compile_seq, wp_qSeq, hMid_wp, hPre_wp]
  refine ⟨hConstAll, fun M σ ↦ ?_⟩
  choose MCont hCont_wp using fun f ↦ (hdCont f).1 M
  obtain ⟨MMid, hMid_wp, hMid_mat⟩ :=
    DynCircuitExt.wp_measureXResetAndBranch_const v k rOut cont M MCont hCont_wp
  have hSeqWp : wp
    (DynamicCircuit.seq dPre (DynCircuitExt.measureXResetAndBranch v k rOut cont)).compile
      (fun _ ↦ M) σ = wp dPre.compile (fun _ ↦ MMid) σ := by
    simp only [DynamicCircuit.compile_seq, wp_qSeq, hMid_wp]
  rw [hSeqWp, hdPre.2 MMid σ, hMid_mat]
  let w : ℝ := (√(1 / 2)) ^ k
  have hTerm : ∀ f : Fin k → Bool, P_pre * (U_pre.1ᴴ * ((DynCircuitExt.xResetKraus rOut f)ᴴ *
      (MCont f).1.1 * DynCircuitExt.xResetKraus rOut f) * U_pre.1) * P_pre =
      ((w ^ 2 : ℝ) : ℂ) • (P_pre * (U_target.1ᴴ * M.1.1 * U_target.1) * P_pre) := by
    intro f
    let Kf := DynCircuitExt.xResetKraus rOut f
    let Uf := (U_fix f).1
    have hClean : P_post * (Kf * U_pre.1 * P_pre) = Kf * U_pre.1 * P_pre := hPostClean f
    have hClean_adj : P_pre * U_pre.1ᴴ * Kfᴴ * P_post = P_pre * U_pre.1ᴴ * Kfᴴ := by
      have h := congrArg conjTranspose hClean
      simpa only [Matrix.conjTranspose_mul, hPostH, hPreH, Matrix.mul_assoc] using h
    have hProd : Uf * P_post * Kf * U_pre.1 * P_pre = (w : ℂ) • (U_target.1 * P_pre) := by
      calc Uf * P_post * Kf * U_pre.1 * P_pre
          = Uf * (P_post * (Kf * U_pre.1 * P_pre)) := by simp only [Matrix.mul_assoc]
        _ = (Uf * Kf * U_pre.1) * P_pre := by rw [hClean]; simp only [Matrix.mul_assoc]
        _ = (w : ℂ) • (U_target.1 * P_pre) := hBranch f
    have hstar : star (w : ℂ) = (w : ℂ) := Complex.conj_ofReal w
    have hProd_adj : P_pre * U_pre.1ᴴ * Kfᴴ * P_post * Ufᴴ = (w : ℂ) • (P_pre * U_target.1ᴴ) := by
      have h := congrArg conjTranspose hProd
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hstar,
        hPostH, hPreH, Matrix.mul_assoc] using h
    have hMCont_eq : MCont f = wp (cont f).compile (fun _ ↦ M) σ := (congrFun (hCont_wp f) σ).symm
    have hCont_conj : P_post * (MCont f).1.1 * P_post = P_post * (Ufᴴ * M.1.1 * Uf) * P_post := by
      rw [hMCont_eq]; exact (hdCont f).2 M σ
    calc P_pre * (U_pre.1ᴴ * (Kfᴴ * (MCont f).1.1 * Kf) * U_pre.1) * P_pre
        = (P_pre * U_pre.1ᴴ * Kfᴴ) * (MCont f).1.1 * (Kf * U_pre.1 * P_pre) := by
            simp only [Matrix.mul_assoc]
      _ = (P_pre * U_pre.1ᴴ * Kfᴴ * P_post) * (MCont f).1.1 * (P_post * (Kf * U_pre.1 * P_pre)) :=
            congrArg₂ (· * ·) (congrArg₂ (· * ·) hClean_adj.symm rfl) hClean.symm
      _ = (P_pre * U_pre.1ᴴ * Kfᴴ) * (P_post * (MCont f).1.1 * P_post) * (Kf * U_pre.1 * P_pre) :=
        by
            simp only [Matrix.mul_assoc]
      _ = (P_pre * U_pre.1ᴴ * Kfᴴ) * (P_post * (Ufᴴ * M.1.1 * Uf) * P_post) *
        (Kf * U_pre.1 * P_pre) := by
            rw [hCont_conj]
      _ = (P_pre * U_pre.1ᴴ * Kfᴴ * P_post * Ufᴴ) * M.1.1 * (Uf * P_post * Kf * U_pre.1 * P_pre) :=
        by
            simp only [Matrix.mul_assoc]
      _ = ((w : ℂ) • (P_pre * U_target.1ᴴ)) * M.1.1 * ((w : ℂ) • (U_target.1 * P_pre)) := by
            rw [hProd_adj, hProd]
      _ = ((w ^ 2 : ℝ) : ℂ) • (P_pre * (U_target.1ᴴ * M.1.1 * U_target.1) * P_pre) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
            congr 1; push_cast; ring
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_congr rfl fun f _ ↦ hTerm f, ← Finset.sum_smul]
  have hsum_c : (∑ _f : Fin k → Bool, ((w ^ 2 : ℝ) : ℂ)) = 1 := by
    exact_mod_cast DynCircuitExt.sum_sqrt_half_pow_sq k
  rw [hsum_c, one_smul]
theorem p2d_RealizesConstCleanUnitary_withTempAnd {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) {S_pre S_post : BitAssignment n → Prop} {dBody : DynamicCircuit Var n}
    {U_body : Unitary (2 ^ n)} (hAnc0 : ∀ β : BitAssignment n, S_pre β → β anc = 0) (hFwd : ∀
    β : BitAssignment n, S_pre β → S_post (Function.update β anc (β anc + β c₁ * β c₂)))
    (hdBody : p2d_RealizesConstCleanUnitary (p2d_ketPredProj S_post) dBody U_body) (hRestore :
    ∀ β : BitAssignment n, S_pre β → ((QRegister.singleton anc).basisOutcomeProjector
    0).mulVec (((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval * U_body * (Circuit.TOFF c₁ c₂ anc
    h₁₂ h₁a h₂a).eval).1.mulVec (ket β)) = ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval * U_body
    * (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval).1.mulVec (ket β)) :
    p2d_RealizesConstCleanUnitary (p2d_ketPredProj S_pre) (.seq (DynamicCircuit.andCompute c₁
    c₂ anc h₁a h₂a) (.seq dBody (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))) ((Circuit.TOFF
    c₁ c₂ anc h₁₂ h₁a h₂a).eval * U_body * (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval) := by
  let P_pre := p2d_ketPredProj S_pre
  let P_post := p2d_ketPredProj S_post
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  let U_clean := T_anc * U_body * T_anc
  have hPreH : P_preᴴ = P_pre := p2d_ketPredProj_conjTranspose S_pre
  have hPostH : P_postᴴ = P_post := p2d_ketPredProj_conjTranspose S_post
  have hP₀H : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hP₀_eq : P₀ = p2d_ketPredProj (fun β ↦ β anc = 0) := by
    classical
    apply matrix_ext_ket
    intro β
    rw [ket_projector_zero, p2d_ketPredProj_mul_ket]
  have hP₀_pre : P₀ * P_pre = P_pre := by
    rw [hP₀_eq]; exact p2d_ketPredProj_mul_imp hAnc0
  have hPre_P₀ : P_pre * P₀ = P_pre := by
    rw [hP₀_eq]; exact p2d_ketPredProj_mul_imp_right hAnc0
  have hToffSq : T_anc.1 * T_anc.1 = 1 := by
    apply matrix_ext_ket
    intro β
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    dsimp only [T_anc]
    rw [ket_TOFF, ket_TOFF, Function.update_self, Function.update_of_ne h₁a,
      Function.update_of_ne h₂a, add_assoc, CharTwo.add_self_eq_zero, add_zero,
      Function.update_idem, Function.update_eq_self]
  have hTU_comm : U_body.1 * T_anc.1 = T_anc.1 * U_clean.1 := by
    dsimp only [U_clean]
    simp only [Submonoid.coe_mul, ← Matrix.mul_assoc, hToffSq, Matrix.one_mul]
  have hTU_adj_comm : T_anc.1ᴴ * U_body.1ᴴ = U_clean.1ᴴ * T_anc.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg conjTranspose hTU_comm
  have hPost_T_pre : P_post * (T_anc.1 * P_pre) = T_anc.1 * P_pre := by
    classical
    apply matrix_ext_ket
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [P_pre, P_post, T_anc]
    rw [p2d_ketPredProj_mul_ket]
    by_cases hs : S_pre β
    · rw [ite_eq_left hs, ket_TOFF, p2d_ketPredProj_mul_ket, ite_eq_left (hFwd β hs)]
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hPre_Tadj_Post : P_pre * T_anc.1ᴴ * P_post = P_pre * T_anc.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hPostH, hPreH,
      Matrix.mul_assoc] using congrArg conjTranspose hPost_T_pre
  have hP₀_U_pre : P₀ * (U_clean.1 * P_pre) = U_clean.1 * P_pre := by
    classical
    apply matrix_ext_ket
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [P_pre]
    rw [p2d_ketPredProj_mul_ket]
    by_cases hs : S_pre β
    · rw [ite_eq_left hs]; exact hRestore β hs
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hPre_Uadj_P₀ : P_pre * U_clean.1ᴴ * P₀ = P_pre * U_clean.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP₀H, hPreH,
      Matrix.mul_assoc] using congrArg conjTranspose hP₀_U_pre
  have hConstWrap : PreservesStoreConst (.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
      (.seq dBody (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))) := PreservesStoreConst.seq
      (PreservesStoreConst.circuit _) (PreservesStoreConst.seq hdBody.1
      (PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂))
  refine ⟨hConstWrap, fun M σ ↦ ?_⟩
  let dUncomp := DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂
  obtain ⟨M_uncomp, hUncomp_wp⟩ := PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂ M
  obtain ⟨M_body, hBody_wp⟩ := hdBody.1 M_uncomp
  have hStep1Raw := congrArg HermitianMat.mat (congrArg Subtype.val (congrFun
    (DynCircuitExt.restrictToZeroAncilla_wp_andCompute_seq_compat c₁ c₂ anc h₁₂ h₁a h₂a
      (.qSeq dBody.compile dUncomp.compile) (fun _ ↦ M)) σ))
  have hBodySeqWp : wp (.qSeq dBody.compile dUncomp.compile) (fun _ ↦ M) = fun _ ↦ M_body := by
    funext τ
    change wp dBody.compile (wp dUncomp.compile (fun _ ↦ M)) τ = M_body
    rw [hUncomp_wp, hBody_wp]
  rw [hBodySeqWp] at hStep1Raw
  have hStep1 : P₀ * (wp (DynamicCircuit.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
      (DynamicCircuit.seq dBody dUncomp)).compile (fun _ ↦ M) σ).1.1 * P₀ =
      P₀ * (T_anc.1ᴴ * M_body.1.1 * T_anc.1) * P₀ := by
    simp only [CQAssertion.restrictToZeroAncilla, CQAssertion.conj, T_anc, P₀,
      QRegister.basisOutcomeProjector_conjTranspose, DynamicCircuit.compile_seq,
      HermitianMat.conj_apply_mat, wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] at hStep1Raw ⊢
    exact hStep1Raw
  have hStepUncompRaw := congrArg HermitianMat.mat (congrArg Subtype.val (congrFun
    (DynCircuitExt.restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
      v c₁ c₂ anc h₁₂ h₁a h₂a (fun _ ↦ M) (fun _ _ ↦ rfl)) σ))
  rw [hUncomp_wp] at hStepUncompRaw
  have hStepUncomp : P₀ * (T_anc.1ᴴ * M_uncomp.1.1 * T_anc.1) * P₀ = P₀ * M.1.1 * P₀ := by
    simp only [CQAssertion.restrictToZeroAncilla, CQAssertion.conj, T_anc, P₀,
      QRegister.basisOutcomeProjector_conjTranspose,
      HermitianMat.conj_apply_mat, wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] at hStepUncompRaw ⊢
    exact hStepUncompRaw
  have hBodyConj : P_post * M_body.1.1 * P_post =
      P_post * (U_body.1ᴴ * M_uncomp.1.1 * U_body.1) * P_post :=
    (congrFun hBody_wp σ).symm ▸ hdBody.2 M_uncomp σ
  calc P_pre * (wp (DynamicCircuit.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
        (DynamicCircuit.seq dBody dUncomp)).compile (fun _ ↦ M) σ).1.1 * P_pre
      = P_pre * (P₀ * (wp (DynamicCircuit.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
          (DynamicCircuit.seq dBody dUncomp)).compile (fun _ ↦ M) σ).1.1 * P₀) * P_pre := by
          simp only [← Matrix.mul_assoc, hPre_P₀]; simp only [Matrix.mul_assoc, hP₀_pre]
    _ = P_pre * (P₀ * (T_anc.1ᴴ * M_body.1.1 * T_anc.1) * P₀) * P_pre := by rw [hStep1]
    _ = (P_pre * T_anc.1ᴴ) * M_body.1.1 * (T_anc.1 * P_pre) := by
          simp only [← Matrix.mul_assoc, hPre_P₀]; simp only [Matrix.mul_assoc, hP₀_pre]
    _ = (P_pre * T_anc.1ᴴ * P_post) * M_body.1.1 * (P_post * (T_anc.1 * P_pre)) := by
          rw [hPre_Tadj_Post, hPost_T_pre]
    _ = (P_pre * T_anc.1ᴴ) * (P_post * M_body.1.1 * P_post) * (T_anc.1 * P_pre) := by
          simp only [Matrix.mul_assoc]
    _ = (P_pre * T_anc.1ᴴ) * (P_post * (U_body.1ᴴ * M_uncomp.1.1 * U_body.1) * P_post) *
          (T_anc.1 * P_pre) := by rw [hBodyConj]
    _ = (P_pre * T_anc.1ᴴ * P_post) * (U_body.1ᴴ * M_uncomp.1.1 * U_body.1) *
          (P_post * (T_anc.1 * P_pre)) := by simp only [Matrix.mul_assoc]
    _ = P_pre * (T_anc.1ᴴ * U_body.1ᴴ) * M_uncomp.1.1 * (U_body.1 * T_anc.1 * P_pre) := by
          rw [hPre_Tadj_Post, hPost_T_pre]; simp only [Matrix.mul_assoc]
    _ = (P_pre * U_clean.1ᴴ) * (T_anc.1ᴴ * M_uncomp.1.1 * T_anc.1) * (U_clean.1 * P_pre) := by
          rw [hTU_adj_comm, hTU_comm]
          simp only [Matrix.mul_assoc]
    _ = (P_pre * U_clean.1ᴴ * P₀) * (T_anc.1ᴴ * M_uncomp.1.1 * T_anc.1) *
          (P₀ * (U_clean.1 * P_pre)) := by rw [hPre_Uadj_P₀, hP₀_U_pre]
    _ = (P_pre * U_clean.1ᴴ) * (P₀ * (T_anc.1ᴴ * M_uncomp.1.1 * T_anc.1) * P₀) *
          (U_clean.1 * P_pre) := by simp only [Matrix.mul_assoc]
    _ = (P_pre * U_clean.1ᴴ) * (P₀ * M.1.1 * P₀) * (U_clean.1 * P_pre) := by rw [hStepUncomp]
    _ = (P_pre * U_clean.1ᴴ * P₀) * M.1.1 * (P₀ * (U_clean.1 * P_pre)) := by
          simp only [Matrix.mul_assoc]
    _ = P_pre * (U_clean.1ᴴ * M.1.1 * U_clean.1) * P_pre := by
          rw [hPre_Uadj_P₀, hP₀_U_pre]; simp only [Matrix.mul_assoc]
/-- Helper declaration `cBitStepChain` for the 133-wire 2D split anchor Swap-0 bridge. -/
def cBitStepChain {n : ℕ} (z : Wire n) (A : ℕ) (uAct xAct : Fin A → Wire n)
    (hxz : ∀ i : Fin A, xAct i ≠ z) (huz : ∀ i : Fin A, uAct i ≠ z) :
    (k : ℕ) → (hk : k ≤ A) → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let ik : Fin A := ⟨k, by omega⟩
      cBitStepChain z A uAct xAct hxz huz k (by omega) ;;ᶜ
      oneHotBitStep z (uAct ik) (xAct ik) (hxz ik) (huz ik)
theorem cBitStepChain_count_toff {n : ℕ} (z : Wire n) (A : ℕ) (uAct xAct : Fin A → Wire n)
    (hxz : ∀ i : Fin A, xAct i ≠ z) (huz : ∀ i : Fin A, uAct i ≠ z) : ∀ (k : ℕ) (hk : k ≤ A),
      (cBitStepChain z A uAct xAct hxz huz k hk).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cBitStepChain]
      rw [Circuit.count_seq, cBitStepChain_count_toff z A uAct xAct hxz huz k,
          oneHotBitStep_count_toff, add_zero]
theorem cBitStepChain_count_t {n : ℕ} (z : Wire n) (A : ℕ) (uAct xAct : Fin A → Wire n)
    (hxz : ∀ i : Fin A, xAct i ≠ z) (huz : ∀ i : Fin A, uAct i ≠ z) : ∀ (k : ℕ) (hk : k ≤ A),
      (cBitStepChain z A uAct xAct hxz huz k hk).count PrimitiveGate.T = 2 * k
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cBitStepChain]
      rw [Circuit.count_seq, cBitStepChain_count_t z A uAct xAct hxz huz k, oneHotBitStep_count_t]
      ring
theorem cBitStepChain_eval_ket {n : ℕ} (z : Wire n) (A : ℕ) (uAct xAct : Fin A → Wire n)
    (hxz : ∀ i : Fin A, xAct i ≠ z) (huz : ∀ i : Fin A, uAct i ≠ z) (β : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ A), (cBitStepChain z A uAct xAct hxz huz k hk).eval.1.mulVec (ket β) =
        (∏ i : Fin k,
          oneHotBitPhase (β z) (β (uAct ⟨i.val, by omega⟩)) (β (xAct ⟨i.val, by omega⟩))) • ket β
  | 0, _ => by simp [cBitStepChain]
  | k + 1, hk => by
      dsimp only [cBitStepChain]
      rw [eval_seq_mulVec, cBitStepChain_eval_ket z A uAct xAct hxz huz β k (by omega),
          Matrix.mulVec_smul, ket_oneHotBitStep, smul_smul, Fin.prod_univ_castSucc]
      rfl
/-- Helper declaration `cPhaseMux1Bit` for the 133-wire 2D split anchor Swap-0 bridge. -/
def cPhaseMux1Bit {n : ℕ} (z : Wire n) (A : ℕ) (uAct xAct : Fin A → Wire n) (uBnd : Wire n)
    (hxz : ∀ i : Fin A, xAct i ≠ z) (huz : ∀ i : Fin A, uAct i ≠ z) (hbz : uBnd ≠ z) : Circuit n :=
  Circuit.H z ;;ᶜ
  ((cBitStepChain z A uAct xAct hxz huz A le_rfl ;;ᶜ oneHotBoundaryFix z uBnd hbz) ;;ᶜ
   (Circuit.H z ;;ᶜ Circuit.S z))
theorem cPhaseMux1Bit_count_toff {n : ℕ} (z : Wire n) (A : ℕ) (uAct xAct : Fin A → Wire n)
    (uBnd : Wire n) (hxz : ∀ i : Fin A, xAct i ≠ z) (huz : ∀ i : Fin A, uAct i ≠ z)
    (hbz : uBnd ≠ z) : (cPhaseMux1Bit z A uAct xAct uBnd hxz huz hbz).count PrimitiveGate.TOFF
    = 0 := by
  have hh : (Circuit.H z).count PrimitiveGate.TOFF = 0 := rfl
  have hs : (Circuit.S z).count PrimitiveGate.TOFF = 0 := rfl
  dsimp only [cPhaseMux1Bit]
  simp only[Circuit.count_seq, hh, hs, cBitStepChain_count_toff, oneHotBoundaryFix_count_toff]
theorem cPhaseMux1Bit_count_t {n : ℕ} (z : Wire n) (A : ℕ) (uAct xAct : Fin A → Wire n)
    (uBnd : Wire n) (hxz : ∀ i : Fin A, xAct i ≠ z) (huz : ∀ i : Fin A, uAct i ≠ z)
    (hbz : uBnd ≠ z) : (cPhaseMux1Bit z A uAct xAct uBnd hxz huz hbz).count PrimitiveGate.T =
    2 * A + 2 := by
  have hh : (Circuit.H z).count PrimitiveGate.T = 0 := rfl
  have hs : (Circuit.S z).count PrimitiveGate.T = 0 := rfl
  dsimp only [cPhaseMux1Bit]
  simp only[Circuit.count_seq, hh, hs, cBitStepChain_count_t, oneHotBoundaryFix_count_t]
  ring
theorem cPhaseMux1Bit_eval_ket {n : ℕ} (z : Wire n) (A : ℕ) (uAct xAct : Fin A → Wire n)
    (uBnd : Wire n) (hxz : ∀ i : Fin A, xAct i ≠ z) (huz : ∀ i : Fin A, uAct i ≠ z)
    (hbz : uBnd ≠ z) (β : BitAssignment n) (hz0 : β z = 0) (y : ZMod 2) (hCases : ((∀ i : Fin
    A, β (uAct i) = 0) ∧ β uBnd = 1 ∧ y = 0) ∨ (∃ i₀ : Fin A, (∀ i : Fin A, β (uAct i) = if i
    = i₀ then 1 else 0) ∧ β uBnd = 0 ∧ y = β (xAct i₀))) :
    (cPhaseMux1Bit z A uAct xAct uBnd hxz huz hbz).eval.1.mulVec (ket β) = ket
    (Function.update β z y) := by
  let g0 := Function.update β z 0
  let g1 := Function.update β z 1
  have hbs0 : bitSign (β z) = 1 := by simp [hz0, bitSign]
  have hDiag : ∀ b : ZMod 2, (cBitStepChain z A uAct xAct hxz huz A le_rfl ;;ᶜ
       oneHotBoundaryFix z uBnd hbz).eval.1.mulVec (ket (Function.update β z b)) =
      targetDiagScalar b y • ket (Function.update β z b) := fun b ↦ by
    let gb := Function.update β z b
    have hgb_z : gb z = b := Function.update_self _ _ _
    have hgb_u : ∀ i : Fin A, gb (uAct i) = β (uAct i) := fun i ↦ Function.update_of_ne (huz i) _ _
    have hgb_x : ∀ i : Fin A, gb (xAct i) = β (xAct i) := fun i ↦ Function.update_of_ne (hxz i) _ _
    have hgb_bnd : gb uBnd = β uBnd := Function.update_of_ne hbz _ _
    rw [eval_seq_mulVec, cBitStepChain_eval_ket, Matrix.mulVec_smul, ket_oneHotBoundaryFix,
      smul_smul]
    change ((∏ i : Fin A,
      oneHotBitPhase (gb z) (gb (uAct ⟨i.val, i.isLt⟩)) (gb (xAct ⟨i.val, i.isLt⟩))) *
      oneHotBoundaryPhase (gb z) (gb uBnd)) • ket gb = _
    have hprod_simp : (∏ i : Fin A, oneHotBitPhase (gb z) (gb (uAct ⟨i.val, i.isLt⟩)) (gb
        (xAct ⟨i.val, i.isLt⟩))) = ∏ i : Fin A, oneHotBitPhase b (β (uAct i)) (β (xAct i)) :=
      Finset.prod_congr rfl fun i _ ↦ by
        have hieq : (⟨i.val, i.isLt⟩ : Fin A) = i := Fin.ext rfl
        rw [hieq, hgb_z, hgb_u, hgb_x]
    rw [hprod_simp, hgb_z, hgb_bnd]
    refine congrArg (· • ket gb) ?_
    rcases hCases with ⟨hAll0, hB1, rfl⟩ | ⟨i₀, hOneHot, hB0, rfl⟩
    · have hp1 : (∏ i : Fin A, oneHotBitPhase b (β (uAct i)) (β (xAct i))) = 1 :=
        Finset.prod_eq_one fun i _ ↦ by rw [hAll0 i, oneHotBitPhase_zero_u]
      rw [hp1, one_mul, hB1, oneHotBoundaryPhase_one]
      simp [targetDiagScalar]
    · have hp1 : (∏ i : Fin A, oneHotBitPhase b (β (uAct i)) (β (xAct i))) =
          oneHotBitPhase b 1 (β (xAct i₀)) := by
        rw [Finset.prod_eq_single i₀]
        · rw [hOneHot i₀, ite_eq_left rfl]
        · intro i _ hne; rw [hOneHot i, ite_eq_right hne, oneHotBitPhase_zero_u]
        · intro habs; exact absurd (Finset.mem_univ i₀) habs
      rw [hp1, hB0, oneHotBitPhase_one_mul_boundary_zero]
  dsimp only [cPhaseMux1Bit]
  rw[eval_seq_mulVec, MeasureBranchHadamardSem.ket_H, hbs0,
      one_smul, eval_seq_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add, hDiag 0, hDiag 1]
  exact hs_collapse_targetDiagScalar z y β
/-- Helper declaration `cCenter1BitChain` for the 133-wire 2D split anchor Swap-0 bridge. -/
def cCenter1BitChain {n : ℕ} (anchor : Wire n) (B : ℕ)
    (xAct : Fin B → Wire n) (hax : ∀ i : Fin B, anchor ≠ xAct i) :
    (k : ℕ) → (hk : k ≤ B) → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let ik : Fin B := ⟨k, by omega⟩
      cCenter1BitChain anchor B xAct hax k (by omega) ;;ᶜ
      Circuit.CNOT anchor (xAct ik) (hax ik)
theorem cCenter1BitChain_count_toff {n : ℕ} (anchor : Wire n) (B : ℕ)
    (xAct : Fin B → Wire n) (hax : ∀ i : Fin B, anchor ≠ xAct i) : ∀ (k : ℕ) (hk : k ≤ B),
      (cCenter1BitChain anchor B xAct hax k hk).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      have hc : (Circuit.CNOT anchor (xAct ⟨k, by omega⟩) (hax _)).count PrimitiveGate.TOFF = 0 :=
        rfl
      dsimp only [cCenter1BitChain]
      rw [Circuit.count_seq, cCenter1BitChain_count_toff anchor B xAct hax k, hc, add_zero]
theorem cCenter1BitChain_count_t {n : ℕ} (anchor : Wire n) (B : ℕ)
    (xAct : Fin B → Wire n) (hax : ∀ i : Fin B, anchor ≠ xAct i) : ∀ (k : ℕ) (hk : k ≤ B),
      (cCenter1BitChain anchor B xAct hax k hk).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      have hc : (Circuit.CNOT anchor (xAct ⟨k, by omega⟩) (hax _)).count PrimitiveGate.T = 0 := rfl
      dsimp only [cCenter1BitChain]
      rw [Circuit.count_seq, cCenter1BitChain_count_t anchor B xAct hax k, hc, add_zero]
theorem cCenter1BitChain_eval_ket {n : ℕ} (anchor : Wire n) (B : ℕ)
    (xAct : Fin B → Wire n) (hax : ∀ i : Fin B, anchor ≠ xAct i)
    (hxInj : Function.Injective xAct) : ∀ (k : ℕ) (hk : k ≤ B) (β : BitAssignment n),
      ∃ β' : BitAssignment n,
        (cCenter1BitChain anchor B xAct hax k hk).eval.1.mulVec (ket β) = ket β' ∧
        (∀ w : Wire n, (∀ i : Fin B, i.val < k → w ≠ xAct i) → β' w = β w) ∧
        (∀ i : Fin B, i.val < k → β' (xAct i) = β (xAct i) + β anchor)
  | 0, _, β => ⟨β, by simp [cCenter1BitChain], fun _ _ ↦ rfl, fun _ h ↦ absurd h (by omega)⟩
  | k + 1, hk, β => by
      obtain ⟨β₁, hKet₁, hOther₁, hAct₁⟩ :=
        cCenter1BitChain_eval_ket anchor B xAct hax hxInj k (by omega) β
      let ik : Fin B := ⟨k, by omega⟩
      let β₂ := Function.update β₁ (xAct ik) (β₁ (xAct ik) + β₁ anchor)
      have hAnch₁ : β₁ anchor = β anchor := hOther₁ anchor fun i _ ↦ hax i
      have hik_unch : β₁ (xAct ik) = β (xAct ik) :=
        hOther₁ (xAct ik) fun i hi h ↦ by
          have := congrArg Fin.val (hxInj h).symm; dsimp [ik] at this; omega
      refine ⟨β₂, ?_, fun w hw ↦ ?_, fun i hi ↦ ?_⟩
      · dsimp only [cCenter1BitChain]
        rw [eval_seq_mulVec, hKet₁, ket_CNOT]
      · dsimp only [β₂]
        rw [Function.update_of_ne (hw ik (by dsimp [ik]; omega))]
        exact hOther₁ w fun i hi ↦ hw i (by omega)
      · dsimp only [β₂]
        by_cases hik : i = ik
        · subst hik; rw [Function.update_self, hik_unch, hAnch₁]
        · have hi_lt : i.val < k := by
            have : i.val ≠ k := fun hv ↦ hik (Fin.ext hv)
            omega
          rw [Function.update_of_ne (hxInj.ne hik)]
          exact hAct₁ i hi_lt
/-- Helper declaration `cLoadRowAnchored1Bit` for the 133-wire 2D split anchor Swap-0 bridge. -/
def cLoadRowAnchored1Bit {n : ℕ} (W A : ℕ) (hA : 1 ≤ A) (hAW : A ≤ W) (uLo : Fin W → Wire n)
    (uBnd anchor : Wire n) (wAct : Fin (A - 1) → Wire n) (wOut : Wire n)
    (hax : ∀ i : Fin (A - 1), anchor ≠ wAct i) (hxOut : ∀ i : Fin (A - 1), wAct i ≠ wOut)
    (haOut : anchor ≠ wOut) (huOut : ∀ l : Fin W, uLo l ≠ wOut) (hbOut : uBnd ≠ wOut) :
    Circuit n :=
  cCenter1BitChain anchor (A - 1) wAct hax (A - 1) le_rfl ;;ᶜ
  (cPhaseMux1Bit wOut (A - 1)
    (fun i ↦ uLo ⟨i.val + 1, by omega⟩) wAct uBnd
    hxOut (fun i ↦ huOut _) hbOut ;;ᶜ
   (cCenter1BitChain anchor (A - 1) wAct hax (A - 1) le_rfl ;;ᶜ Circuit.CNOT anchor wOut haOut))
theorem cLoadRowAnchored1Bit_count_toff {n : ℕ} (W A : ℕ) (hA : 1 ≤ A) (hAW : A ≤ W)
    (uLo : Fin W → Wire n) (uBnd anchor : Wire n) (wAct : Fin (A - 1) → Wire n)
    (wOut : Wire n) (hax : ∀ i : Fin (A - 1), anchor ≠ wAct i)
    (hxOut : ∀ i : Fin (A - 1), wAct i ≠ wOut) (haOut : anchor ≠ wOut)
    (huOut : ∀ l : Fin W, uLo l ≠ wOut) (hbOut : uBnd ≠ wOut) : (cLoadRowAnchored1Bit W A hA
    hAW uLo uBnd anchor wAct wOut hax hxOut haOut huOut hbOut).count PrimitiveGate.TOFF = 0 := by
  have hc : (Circuit.CNOT anchor wOut haOut).count PrimitiveGate.TOFF = 0 := rfl
  dsimp only [cLoadRowAnchored1Bit]
  simp only [Circuit.count_seq, cCenter1BitChain_count_toff, cPhaseMux1Bit_count_toff, hc]
theorem cLoadRowAnchored1Bit_count_t {n : ℕ} (W A : ℕ) (hA : 1 ≤ A) (hAW : A ≤ W)
    (uLo : Fin W → Wire n) (uBnd anchor : Wire n) (wAct : Fin (A - 1) → Wire n)
    (wOut : Wire n) (hax : ∀ i : Fin (A - 1), anchor ≠ wAct i)
    (hxOut : ∀ i : Fin (A - 1), wAct i ≠ wOut) (haOut : anchor ≠ wOut)
    (huOut : ∀ l : Fin W, uLo l ≠ wOut) (hbOut : uBnd ≠ wOut) : (cLoadRowAnchored1Bit W A hA
    hAW uLo uBnd anchor wAct wOut hax hxOut haOut huOut hbOut).count PrimitiveGate.T = 2 * A := by
  have hc : (Circuit.CNOT anchor wOut haOut).count PrimitiveGate.T = 0 := rfl
  dsimp only [cLoadRowAnchored1Bit]
  simp only [Circuit.count_seq, cCenter1BitChain_count_t, cPhaseMux1Bit_count_t, hc]
  omega
theorem cLoadRowAnchored1Bit_eval_ket {n : ℕ} (W A : ℕ) (hA : 1 ≤ A) (hAW : A ≤ W)
    (uLo : Fin W → Wire n) (uBnd anchor : Wire n) (wAct : Fin (A - 1) → Wire n) (wOut : Wire n)
    (hax : ∀ i : Fin (A - 1), anchor ≠ wAct i) (hxOut : ∀ i : Fin (A - 1), wAct i ≠ wOut)
    (haOut : anchor ≠ wOut) (huOut : ∀ l : Fin W, uLo l ≠ wOut) (hbOut : uBnd ≠ wOut)
    (hxInj : Function.Injective wAct) (huNotAct : ∀ (l : Fin W) (i : Fin (A - 1)), uLo l ≠ wAct i)
    (hbNotAct : ∀ i : Fin (A - 1), uBnd ≠ wAct i) (β : BitAssignment n) (hOut0 : β wOut = 0)
    (l₀ : ℕ) (hl₀ : l₀ < W) (hOneHot : ∀ l : Fin W, β (uLo l) = if l.val = l₀ then 1 else 0)
    (hBndVal : β uBnd = if (l₀ = 0 ∨ A ≤ l₀) then 1 else 0) :
    (cLoadRowAnchored1Bit W A hA hAW uLo uBnd anchor wAct wOut
      hax hxOut haOut huOut hbOut).eval.1.mulVec (ket β) = ket (Function.update β wOut
        (if h0 : l₀ = 0 then β anchor else if hlt : l₀ < A then β (wAct ⟨l₀ - 1, by omega⟩)
         else β anchor)) := by
  obtain ⟨β₁, hKet₁, hOther₁, hAct₁⟩ :=
    cCenter1BitChain_eval_ket anchor (A - 1) wAct hax hxInj (A - 1) le_rfl β
  have hβ₁_out : β₁ wOut = 0 := (hOther₁ wOut fun i _ ↦ (hxOut i).symm).trans hOut0
  have hβ₁_u : ∀ l : Fin W, β₁ (uLo l) = if l.val = l₀ then 1 else 0 := fun l ↦
    (hOther₁ (uLo l) fun i _ ↦ huNotAct l i).trans (hOneHot l)
  have hβ₁_bnd : β₁ uBnd = if (l₀ = 0 ∨ A ≤ l₀) then 1 else 0 :=
    (hOther₁ uBnd fun i _ ↦ hbNotAct i).trans hBndVal
  let yDiff : ZMod 2 :=
    if h0 : l₀ = 0 then 0
    else if hlt : l₀ < A then β (wAct ⟨l₀ - 1, by omega⟩) + β anchor
    else 0
  have hMux : (cPhaseMux1Bit wOut (A - 1) (fun i ↦ uLo ⟨i.val + 1, by omega⟩) wAct uBnd
      hxOut (fun i ↦ huOut _) hbOut).eval.1.mulVec (ket β₁) =
      ket (Function.update β₁ wOut yDiff) := by
    apply cPhaseMux1Bit_eval_ket _ _ _ _ _ _ _ _ β₁ hβ₁_out yDiff
    by_cases hOutBnd : l₀ = 0 ∨ A ≤ l₀
    · refine Or.inl ⟨fun i ↦ ?_, ?_, ?_⟩
      · rw [hβ₁_u ⟨i.val + 1, by omega⟩]; dsimp
        have hvne : i.val + 1 ≠ l₀ := by omega
        exact ite_eq_right hvne
      · rw [hβ₁_bnd, ite_eq_left hOutBnd]
      · dsimp [yDiff]
        rcases hOutBnd with rfl | hge
        · simp
        · rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    · push Not at hOutBnd
      obtain ⟨hne0, hltA⟩ := hOutBnd
      refine Or.inr ⟨⟨l₀ - 1, by omega⟩, fun i ↦ ?_, ?_, ?_⟩
      · rw [hβ₁_u ⟨i.val + 1, by omega⟩]; dsimp
        by_cases hi : i = ⟨l₀ - 1, by omega⟩
        · rw [ite_eq_left hi, ite_eq_left (by have := congrArg Fin.val hi; dsimp at this; omega)]
        · have hvne : i.val + 1 ≠ l₀ := fun hv ↦ hi (Fin.ext (by dsimp; omega))
          rw [ite_eq_right hvne, ite_eq_right hi]
      · rw [hβ₁_bnd, ite_eq_right (by omega)]
      · dsimp [yDiff]
        rw [dite_eq_right hne0, dite_eq_left hltA, hAct₁ ⟨l₀ - 1, by omega⟩ (by dsimp; omega)]
  let β₂ := Function.update β₁ wOut yDiff
  obtain ⟨β₃, hKet₃, hOther₃, hAct₃⟩ :=
    cCenter1BitChain_eval_ket anchor (A - 1) wAct hax hxInj (A - 1) le_rfl β₂
  dsimp only [cLoadRowAnchored1Bit]
  rw [eval_seq_mulVec, hKet₁, eval_seq_mulVec, hMux, eval_seq_mulVec, hKet₃, ket_CNOT]
  refine congrArg ket ?_
  have hβ₃_anch : β₃ anchor = β anchor := by
    rw [hOther₃ anchor fun i _ ↦ hax i]
    dsimp [β₂]
    rw [Function.update_of_ne haOut]
    exact hOther₁ anchor fun i _ ↦ hax i
  have hβ₃_out : β₃ wOut = yDiff := by
    rw [hOther₃ wOut fun i _ ↦ (hxOut i).symm]
    dsimp [β₂]; exact Function.update_self _ _ _
  funext w
  by_cases hw : w = wOut
  · subst hw
    rw [Function.update_self, Function.update_self, hβ₃_out, hβ₃_anch]
    dsimp [yDiff]
    by_cases h0 : l₀ = 0
    · simp [h0]
    · rw [dite_eq_right h0, dite_eq_right h0]
      by_cases hlt : l₀ < A
      · rw [dite_eq_left hlt, dite_eq_left hlt, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · rw [dite_eq_right hlt, dite_eq_right hlt, zero_add]
  · rw [Function.update_of_ne hw, Function.update_of_ne hw]
    by_cases hInAct : ∃ i : Fin (A - 1), w = wAct i
    · obtain ⟨i, rfl⟩ := hInAct
      rw [hAct₃ i i.isLt]
      dsimp [β₂]
      rw[Function.update_of_ne (hxOut i), Function.update_of_ne haOut, hAct₁ i i.isLt,
          hOther₁ anchor fun j _ ↦ hax j, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · push Not at hInAct
      rw [hOther₃ w fun i _ ↦ hInAct i]
      dsimp [β₂]
      rw [Function.update_of_ne hw]
      exact hOther₁ w fun i _ ↦ hInAct i
/-- Helper declaration `cXorTailAux` for the 133-wire 2D split anchor Swap-0 bridge. -/
def cXorTailAux {n : ℕ} (W KRem : ℕ) (hKR : KRem ≤ W)
    (uLo : Fin W → Wire n) (wPar : Wire n) (huPar : ∀ l : Fin W, uLo l ≠ wPar) :
    (k : ℕ) → (hk : k ≤ W - KRem) → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let lk : Fin W := ⟨KRem + k, by omega⟩
      cXorTailAux W KRem hKR uLo wPar huPar k (by omega) ;;ᶜ
      Circuit.CNOT (uLo lk) wPar (huPar lk)
/-- Helper declaration `cXorTailParity` for the 133-wire 2D split anchor Swap-0 bridge. -/
def cXorTailParity {n : ℕ} (W KRem : ℕ) (hW : 1 ≤ W) (hKR : KRem ≤ W)
    (uLo : Fin W → Wire n) (wPar : Wire n) (huPar : ∀ l : Fin W, uLo l ≠ wPar) : Circuit n :=
  Circuit.CNOT (uLo ⟨0, hW⟩) wPar (huPar _) ;;ᶜ
  cXorTailAux W KRem hKR uLo wPar huPar (W - KRem) le_rfl
theorem cXorTailAux_count_toff {n : ℕ} (W KRem : ℕ) (hKR : KRem ≤ W)
    (uLo : Fin W → Wire n) (wPar : Wire n) (huPar : ∀ l : Fin W, uLo l ≠ wPar) :
    ∀ (k : ℕ) (hk : k ≤ W - KRem),
      (cXorTailAux W KRem hKR uLo wPar huPar k hk).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      have hc : (Circuit.CNOT (uLo ⟨KRem + k,
        by omega⟩) wPar (huPar _)).count PrimitiveGate.TOFF = 0 := rfl
      dsimp only [cXorTailAux]
      rw [Circuit.count_seq, cXorTailAux_count_toff W KRem hKR uLo wPar huPar k, hc, add_zero]
theorem cXorTailAux_count_t {n : ℕ} (W KRem : ℕ) (hKR : KRem ≤ W)
    (uLo : Fin W → Wire n) (wPar : Wire n) (huPar : ∀ l : Fin W, uLo l ≠ wPar) :
    ∀ (k : ℕ) (hk : k ≤ W - KRem),
      (cXorTailAux W KRem hKR uLo wPar huPar k hk).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      have hc : (Circuit.CNOT (uLo ⟨KRem + k,
        by omega⟩) wPar (huPar _)).count PrimitiveGate.T = 0 := rfl
      dsimp only [cXorTailAux]
      rw [Circuit.count_seq, cXorTailAux_count_t W KRem hKR uLo wPar huPar k, hc, add_zero]
theorem cXorTailParity_count_toff {n : ℕ} (W KRem : ℕ) (hW : 1 ≤ W) (hKR : KRem ≤ W)
    (uLo : Fin W → Wire n) (wPar : Wire n) (huPar : ∀ l : Fin W, uLo l ≠ wPar) :
    (cXorTailParity W KRem hW hKR uLo wPar huPar).count PrimitiveGate.TOFF = 0 := by
  have hc : (Circuit.CNOT (uLo ⟨0, hW⟩) wPar (huPar _)).count PrimitiveGate.TOFF = 0 := rfl
  dsimp only [cXorTailParity]
  rw [Circuit.count_seq, hc, cXorTailAux_count_toff, zero_add]
theorem cXorTailParity_count_t {n : ℕ} (W KRem : ℕ) (hW : 1 ≤ W) (hKR : KRem ≤ W)
    (uLo : Fin W → Wire n) (wPar : Wire n) (huPar : ∀ l : Fin W, uLo l ≠ wPar) :
    (cXorTailParity W KRem hW hKR uLo wPar huPar).count PrimitiveGate.T = 0 := by
  have hc : (Circuit.CNOT (uLo ⟨0, hW⟩) wPar (huPar _)).count PrimitiveGate.T = 0 := rfl
  dsimp only [cXorTailParity]
  rw [Circuit.count_seq, hc, cXorTailAux_count_t, zero_add]
theorem cXorTailAux_eval_ket {n : ℕ} (W KRem : ℕ) (hKR : KRem ≤ W)
    (uLo : Fin W → Wire n) (wPar : Wire n) (huPar : ∀ l : Fin W, uLo l ≠ wPar)
    (β : BitAssignment n) : ∀ (k : ℕ) (hk : k ≤ W - KRem),
      (cXorTailAux W KRem hKR uLo wPar huPar k hk).eval.1.mulVec (ket β) =
        ket (Function.update β wPar (β wPar + ∑ i : Fin k, β (uLo ⟨KRem + i.val, by omega⟩)))
  | 0, _ => by simp [cXorTailAux]
  | k + 1, hk => by
      dsimp only [cXorTailAux]
      rw [eval_seq_mulVec, cXorTailAux_eval_ket W KRem hKR uLo wPar huPar β k (by omega),
          ket_CNOT, Function.update_self, Function.update_of_ne (huPar _),
          Function.update_idem, Fin.sum_univ_castSucc, add_assoc]
      rfl
theorem cXorTailParity_eval_ket {n : ℕ} (W KRem : ℕ) (hKR1 : 1 ≤ KRem) (hKR : KRem ≤ W)
    (uLo : Fin W → Wire n) (wPar : Wire n) (huPar : ∀ l : Fin W, uLo l ≠ wPar)
    (β : BitAssignment n) (l₀ : ℕ) (hl₀ : l₀ < W)
    (hOneHot : ∀ l : Fin W, β (uLo l) = if l.val = l₀ then 1 else 0) :
    (cXorTailParity W KRem (by omega) hKR uLo wPar huPar).eval.1.mulVec (ket β) = ket
    (Function.update β wPar (β wPar + if (l₀ = 0 ∨ KRem ≤ l₀) then 1 else 0)) := by
  dsimp only [cXorTailParity]
  rw [eval_seq_mulVec, ket_CNOT, cXorTailAux_eval_ket]
  refine congrArg ket ?_
  have hReadU : ∀ l : Fin W,
      Function.update β wPar (β wPar + β (uLo ⟨0, by omega⟩)) (uLo l) = β (uLo l) :=
    fun l ↦ Function.update_of_ne (huPar l) _ _
  simp only [Function.update_self, Function.update_idem, hReadU, add_assoc]
  congr 2
  rw [hOneHot ⟨0, by omega⟩]; dsimp
  have hsum : (∑ i : Fin (W - KRem), β (uLo ⟨KRem + i.val, by omega⟩)) =
      if KRem ≤ l₀ then 1 else 0 := by
    by_cases hge : KRem ≤ l₀
    · rw [ite_eq_left hge, Finset.sum_eq_single ⟨l₀ - KRem, by omega⟩]
      · rw [hOneHot]; dsimp; exact ite_eq_left (by omega)
      · intro i _ hne
        rw [hOneHot]; dsimp
        have hvne : KRem + i.val ≠ l₀ := fun hv ↦ hne (Fin.ext (by dsimp; omega))
        exact ite_eq_right hvne
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · rw [ite_eq_right hge]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [hOneHot]; dsimp
      exact ite_eq_right (by omega)
  rw [hsum]
  by_cases h0 : l₀ = 0
  · subst h0; simp [show ¬ (KRem ≤ 0) by omega]
  · have h0ne : 0 ≠ l₀ := Ne.symm h0
    by_cases hge : KRem ≤ l₀ <;> simp [h0, h0ne, hge]
/-- Helper declaration `cFixRowAnchored1BitAux` for the 133-wire 2D split anchor Swap-0 bridge. -/
def cFixRowAnchored1BitAux {n : ℕ} (W A : ℕ) (hA : 1 ≤ A) (hAW : A ≤ W)
    (uLo : Fin W → Wire n) (anchor : Wire n) (wAct : Fin (A - 1) → Wire n)
    (hua : ∀ l : Fin W, uLo l ≠ anchor) (huw : ∀ (l : Fin W) (i : Fin (A - 1)), uLo l ≠ wAct i) :
    (k : ℕ) → (hk : k ≤ W) → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let lk : Fin W := ⟨k, by omega⟩
      let prev := cFixRowAnchored1BitAux W A hA hAW uLo anchor wAct hua huw k (by omega)
      if h0 : k = 0 then
        prev ;;ᶜ czCircuit (uLo lk) anchor (hua lk)
      else if hlt : k < A then
        prev ;;ᶜ czCircuit (uLo lk) (wAct ⟨k - 1, by omega⟩) (huw lk _)
      else
        prev ;;ᶜ czCircuit (uLo lk) anchor (hua lk)
theorem cFixRowAnchored1BitAux_count_toff {n : ℕ} (W A : ℕ) (hA : 1 ≤ A) (hAW : A ≤ W)
    (uLo : Fin W → Wire n) (anchor : Wire n) (wAct : Fin (A - 1) → Wire n)
    (hua : ∀ l : Fin W, uLo l ≠ anchor) (huw : ∀ (l : Fin W) (i : Fin (A - 1)), uLo l ≠ wAct i) :
    ∀ (k : ℕ) (hk : k ≤ W),
      (cFixRowAnchored1BitAux W A hA hAW uLo anchor wAct hua huw k hk).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cFixRowAnchored1BitAux]
      split_ifs <;>
        rw [Circuit.count_seq,
          cFixRowAnchored1BitAux_count_toff W A hA hAW uLo anchor wAct hua huw k,
            czCircuit_count_toff, add_zero]
theorem cFixRowAnchored1BitAux_count_t {n : ℕ} (W A : ℕ) (hA : 1 ≤ A) (hAW : A ≤ W)
    (uLo : Fin W → Wire n) (anchor : Wire n) (wAct : Fin (A - 1) → Wire n)
    (hua : ∀ l : Fin W, uLo l ≠ anchor) (huw : ∀ (l : Fin W) (i : Fin (A - 1)), uLo l ≠ wAct i) :
    ∀ (k : ℕ) (hk : k ≤ W),
      (cFixRowAnchored1BitAux W A hA hAW uLo anchor wAct hua huw k hk).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cFixRowAnchored1BitAux]
      split_ifs <;>
        rw [Circuit.count_seq, cFixRowAnchored1BitAux_count_t W A hA hAW uLo anchor wAct hua huw k,
            czCircuit_count_t, add_zero]
theorem cFixRowAnchored1BitAux_eval_ket {n : ℕ} (W A : ℕ) (hA : 1 ≤ A) (hAW : A ≤ W)
    (uLo : Fin W → Wire n) (anchor : Wire n) (wAct : Fin (A - 1) → Wire n)
    (hua : ∀ l : Fin W, uLo l ≠ anchor) (huw : ∀ (l : Fin W) (i : Fin (A - 1)), uLo l ≠ wAct i)
    (β : BitAssignment n) : ∀ (k : ℕ) (hk : k ≤ W),
      (cFixRowAnchored1BitAux W A hA hAW uLo anchor wAct hua huw k hk).eval.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (∑ l : Fin k, β (uLo ⟨l.val, by omega⟩) * (if h0 : l.val = 0 then β anchor
             else if hlt : l.val < A then β (wAct ⟨l.val - 1, by omega⟩)
             else β anchor)).val) • ket β
  | 0, _ => by simp [cFixRowAnchored1BitAux]
  | k + 1, hk => by
      dsimp only [cFixRowAnchored1BitAux]
      by_cases h0 : k = 0
      · rw [dite_eq_left h0, eval_seq_mulVec,
            cFixRowAnchored1BitAux_eval_ket W A hA hAW uLo anchor wAct hua huw β k (by omega),
            Matrix.mulVec_smul, ket_czCircuit, smul_smul,
            TempPhaseProg.neg_one_pow_zmod2_mul, Fin.sum_univ_castSucc]
        simp [h0]
      · rw [dite_eq_right h0]
        by_cases hlt : k < A
        · rw [dite_eq_left hlt, eval_seq_mulVec,
              cFixRowAnchored1BitAux_eval_ket W A hA hAW uLo anchor wAct hua huw β k (by omega),
              Matrix.mulVec_smul, ket_czCircuit, smul_smul,
              TempPhaseProg.neg_one_pow_zmod2_mul, Fin.sum_univ_castSucc]
          simp [h0, hlt]
        · rw [dite_eq_right hlt, eval_seq_mulVec,
              cFixRowAnchored1BitAux_eval_ket W A hA hAW uLo anchor wAct hua huw β k (by omega),
              Matrix.mulVec_smul, ket_czCircuit, smul_smul,
              TempPhaseProg.neg_one_pow_zmod2_mul, Fin.sum_univ_castSucc]
          simp [h0, hlt]
theorem cFixRowAnchored1Bit_eval_ket {n : ℕ} (W A : ℕ) (hA : 1 ≤ A) (hAW : A ≤ W)
    (uLo : Fin W → Wire n) (anchor : Wire n) (wAct : Fin (A - 1) → Wire n)
    (hua : ∀ l : Fin W, uLo l ≠ anchor) (huw : ∀ (l : Fin W) (i : Fin (A - 1)), uLo l ≠ wAct i)
    (β : BitAssignment n) (l₀ : ℕ) (hl₀ : l₀ < W)
    (hOneHot : ∀ l : Fin W, β (uLo l) = if l.val = l₀ then 1 else 0) :
    (cFixRowAnchored1BitAux W A hA hAW uLo anchor wAct hua huw W le_rfl).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (if h0 : l₀ = 0 then β anchor
        else if hlt : l₀ < A then β (wAct ⟨l₀ - 1, by omega⟩) else β anchor).val) • ket β := by
  rw [cFixRowAnchored1BitAux_eval_ket]
  refine congrArg (fun z : ZMod 2 ↦ ((-1 : ℂ) ^ z.val) • ket β) ?_
  rw [Finset.sum_eq_single ⟨l₀, hl₀⟩]
  · have hle : (⟨l₀, hl₀⟩ : Fin W) = ⟨l₀, hl₀⟩ := rfl
    rw [hOneHot ⟨l₀, hl₀⟩]; dsimp; rw [ite_eq_left rfl, one_mul]
  · intro l _ hne
    have hvne : l.val ≠ l₀ := fun hv ↦ hne (Fin.ext hv)
    have hle : (⟨l.val, l.isLt⟩ : Fin W) = l := Fin.ext rfl
    rw [hle, hOneHot l, ite_eq_right hvne, zero_mul]
  · intro habs; exact absurd (Finset.mem_univ _) habs
theorem p2dEmptyReg_inj (n : ℕ) : Function.Injective (Fin.elim0 : Fin 0 → Wire n) :=
  fun i ↦ Fin.elim0 i
/-- Helper declaration `p2dEmptyReg` for the 133-wire 2D split anchor Swap-0 bridge. -/
abbrev p2dEmptyReg (n : ℕ) : QRegister 0 n :=
  { wires := { toFun := Fin.elim0, inj' := p2dEmptyReg_inj n } }
theorem p2dEmptyReg_disj {M n : ℕ} (r : QRegister M n) : r.DisjointWires (p2dEmptyReg n) :=
    QRegister.disjoint_iff.mpr fun _ j ↦ Fin.elim0 j
theorem p2dSubReg_inj {n m : ℕ} (rSub : QRegister m n) (off len : ℕ) (h : off + len ≤ m) :
    Function.Injective (fun k : Fin len ↦ rSub ⟨off + k.val, by omega⟩) :=
  fun i j hij ↦ by
    have hv := congrArg Fin.val (rSub.wires.injective hij)
    dsimp at hv
    exact Fin.ext (by omega)
/-- Helper declaration `p2dSubReg` for the 133-wire 2D split anchor Swap-0 bridge. -/
abbrev p2dSubReg {n m : ℕ} (rSub : QRegister m n) (off len : ℕ) (h : off + len ≤ m) :
    QRegister len n :=
  { wires :=
    { toFun := fun k ↦ rSub ⟨off + k.val, by omega⟩
      inj' := p2dSubReg_inj rSub off len h } }
theorem rSub_ne_of_ne {n m : ℕ} (rSub : QRegister m n) {a b : ℕ} (ha : a < m) (hb : b < m)
    (hne : a ≠ b) : rSub ⟨a, ha⟩ ≠ rSub ⟨b, hb⟩ := rSub.wires.injective.ne (Fin.ne_of_val_ne hne)
theorem rCore_ne_rSub {n m : ℕ} {rCore : QRegister posCoreWires n} {rSub : QRegister m n}
    (hCS : rCore.DisjointWires rSub) (e : Fin 218) (j : Fin 18) (k : Fin m) :
    rElecSlot rCore e j ≠ rSub k := by
  rw [rElecSlot_apply_ofFin rCore]
  exact hCS.ne _ k
theorem rElecSlot_inj_slot {n : ℕ} (rCore : QRegister posCoreWires n) (j : Fin 18)
    {a b : ℕ} (ha : a < 218) (hb : b < 218)
    (heq : rElecSlot rCore ⟨a, ha⟩ j = rElecSlot rCore ⟨b, hb⟩ j) : a = b := by
  rw [rElecSlot_apply_ofFin rCore, rElecSlot_apply_ofFin rCore] at heq
  have hv := congrArg Fin.val (rCore.wires.injective heq)
  change 18 * a + j.val = 18 * b + j.val at hv
  omega
theorem rElecSlot_ne_of_slot_ne {n : ℕ} (rCore : QRegister posCoreWires n) (j : Fin 18)
    {a b : ℕ} (ha : a < 218) (hb : b < 218) (hne : a ≠ b) : rElecSlot rCore ⟨a, ha⟩ j ≠
    rElecSlot rCore ⟨b, hb⟩ j := fun heq ↦ hne (rElecSlot_inj_slot rCore j ha hb heq)
theorem p2d_writeReg_reset_zero_of_zero {n K : ℕ} (β : BitAssignment n) (rOut : QRegister K n)
    (vals : Fin K → ZMod 2) (hZero : ∀ idx : Fin K, β (rOut idx) = 0) :
    p2d_writeReg (p2d_writeReg β rOut vals) rOut (fun _ ↦ 0) = β := by
  funext w
  by_cases hm : w ∈ Set.range rOut.wires
  · obtain ⟨idx, rfl⟩ := hm
    rw [p2d_writeReg_apply_reg, hZero idx]
  · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hm, p2d_writeReg_apply_of_not_mem _ _ _ _ hm]

/- ## Section 3: Shared `72 + 54 = 126` (`115`-Wire) 2-Batch Row-Aligned Diagonal Load -/

end ConfigAnchorSwap0Split133
end AnchorSwap0Split133
end
end AnchorSwap0Split133_p1

end QuantumComputation.Specs.StoppingPowerSolution
