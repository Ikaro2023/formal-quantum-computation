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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectRawOps
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectMux
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectArithBase

/-!
# Zero-Toffoli `SELECT` Core & Multiplexer Pullbacks (`SelectCoreDyn`)

Assembles zero-Toffoli `DynamicCircuit` realizations of Step-3 `SELECT` on `nUB w_go w_gi` (pure
ancilla) and `nUB w_go w_gi + k_cat` (catalytic `phaseGradientState 14` interface):
1. `TempProg.wrapSubDyn` & `TempProg.cleanRealizes_wrapSubMux`: generic `TempProg` wrapper
   pulling back a multiplexed core unitary along an output wire map `outReg`.
2. `selectCoreReflDyn` (`464 + t_refl` `T`) & `selectCoreSixStepDyn` (`464 + t_G + t_Ginv` `T`):
   3-step fused-reflection and 6-step `G · CZ · G†` cores on `12` decoded control bits.
3. `selectCatCoreReflDyn` (`464 + t_refl` `T`) & `adaptGivensReflCatFn`: catalytic `SELECT` core
   with zero-gate wire-order adapter for `(en_R : 1, rowIdx : 9, rSpin0 : 58, rCat : k_cat)`.
4. `selectStandaloneDyn` / `selectCatStandaloneDyn` (`1236 + t_refl` `T`, self-contained signs) and
   `selectPrecomputedSignsDyn` / `selectCatPrecomputedSignsDyn` (`620 + t_refl` `T`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputation.Specs.P450

open BlockEncodingCore

open Operator Matrix Circuit QProg CleanDyn HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-! ### 1. Generic `TempProg` Output-Subregister Multiplexer Pullback (`wrapSubDyn`) -/

theorem bitsOfFin_extractIndex {k m : ℕ} (r : QRegister m k) (c : Fin (2 ^ k)) :
    bitsOfFin m (r.extractIndex c) = fun j ↦ bitsOfFin k c (r j) := by
  funext j
  dsimp only [bitsOfFin]
  rw [r.basisBits_extractIndex]

theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i : Fin k, r i = s i) : r = s := by
  ext i; exact congrArg Fin.val (h i)

@[simp]
theorem finSumFinEquiv_inl_val {k m : ℕ} (a : Fin k) :
    (finSumFinEquiv (Sum.inl a : Fin k ⊕ Fin m)).val = a.val := by
  simp [finSumFinEquiv_apply_left]

@[simp]
theorem finSumFinEquiv_inr_val {k m : ℕ} (b : Fin m) :
    (finSumFinEquiv (Sum.inr b : Fin k ⊕ Fin m)).val = k + b.val := by
  simp [finSumFinEquiv_apply_right]

theorem disjoint_block_ctrl_tgt (k_t k_c : ℕ) :
    (QRegister.block (n := k_t + k_c) k_t k_c (by omega)).DisjointWires
      (QRegister.block (n := k_t + k_c) 0 k_t (by omega)) :=
  (QRegister.block_disjoint_of_le (n := k_t + k_c) 0 k_t k_t k_c
    (by omega) (by omega) (by omega)).symm

private theorem muxUnitary_pullback_ctrl {n k_c k_t k₀ : ℕ}
    (rCtrl : QRegister k_c n) (rTgt : QRegister k_t n)
    (hdisj : rCtrl.DisjointWires rTgt)
    (subCtrl : QRegister k₀ k_c)
    {hdisjL : (rCtrl.compose subCtrl).DisjointWires rTgt}
    (F₀ : Fin (2 ^ k₀) → Unitary (2 ^ k_t)) :
    muxUnitary (rCtrl.compose subCtrl) rTgt hdisjL F₀ =
      muxUnitary rCtrl rTgt hdisj (fun c ↦ F₀ (subCtrl.extractIndex c)) := by
  have hdisj₀ : (rCtrl.compose subCtrl).DisjointWires rTgt := by
    rw [QRegister.disjoint_iff]; intro i j; exact hdisj.ne (subCtrl i) j
  apply Subtype.ext; ext i g
  let c₀ := rCtrl.extractIndex g
  have hg (g' : Fin (2 ^ n)) (h : rCtrl.extractIndex g' ≠ c₀) :
      Pi.single (M := fun _ ↦ ℂ) g 1 g' = 0 := by
    rw [Pi.single_eq_of_ne]; rintro rfl; exact h rfl
  have hg₀ (g' : Fin (2 ^ n))
      (h : (rCtrl.compose subCtrl).extractIndex g' ≠ subCtrl.extractIndex c₀) :
      Pi.single (M := fun _ ↦ ℂ) g 1 g' = 0 := by
    rw [Pi.single_eq_of_ne]; rintro rfl; exact h (QRegister.extractIndex_compose _ _ _)
  have hlhs : ((muxUnitary (rCtrl.compose subCtrl) rTgt hdisj₀ F₀).1 *ᵥ Pi.single g 1) i =
      (rTgt.embedMatrix (F₀ (subCtrl.extractIndex c₀)).1 *ᵥ Pi.single g 1) i := by
    rw [muxUnitary_mulVec_of_proj (rCtrl.compose subCtrl) rTgt hdisj₀ F₀
      (subCtrl.extractIndex c₀) _ hg₀]
  have hrhs : ((muxUnitary rCtrl rTgt hdisj (fun c ↦ F₀ (subCtrl.extractIndex c))).1 *ᵥ
      Pi.single g 1) i =
      (rTgt.embedMatrix (F₀ (subCtrl.extractIndex c₀)).1 *ᵥ Pi.single g 1) i := by
    rw [muxUnitary_mulVec_of_proj rCtrl rTgt hdisj _ c₀ _ hg]
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at hlhs hrhs
  exact hlhs.trans hrhs.symm

/-- Pullback register `(0 .. k_t - 1) ++ (k_t + outReg)` inside `k_t + k_out`. -/
def subActPullback (k_t : ℕ) {k_out m_sub : ℕ} (outReg : QRegister m_sub k_out) :
    QRegister (k_t + m_sub) (k_t + k_out) :=
  (QRegister.block 0 k_t (by omega)).concat
    ((QRegister.block k_t k_out (by omega)).compose outReg)
    (by
      rw [QRegister.disjoint_iff]
      intro i j heq
      have hv := congrArg Fin.val heq; simp at hv; omega)

theorem subActPullback_embedUnitary_muxOnAct {k_t k_out m_sub : ℕ}
    (outReg : QRegister m_sub k_out)
    (G : (Fin m_sub → Bool) → Unitary (2 ^ k_t)) :
    (subActPullback k_t outReg).embedUnitary (muxOnAct k_t m_sub G) =
      muxOnAct k_t k_out (fun y ↦ G (fun j ↦ y (outReg j))) := by
  unfold subActPullback
  rw [embedUnitary_muxOnAct, muxUnitary_pullback_ctrl _ _ (disjoint_block_ctrl_tgt k_t k_out)]
  unfold muxOnAct
  congr 1; funext c
  rw [bitsOfFin_extractIndex]

theorem embedUnitary_muxUnitary {n m k₀ m₀ : ℕ}
    (sub : QRegister m n)
    (rC₀ : QRegister k₀ m) (rT₀ : QRegister m₀ m) (hdisj₀ : rC₀.DisjointWires rT₀)
    (F₀ : Fin (2 ^ k₀) → Unitary (2 ^ m₀)) :
    sub.embedUnitary (muxUnitary rC₀ rT₀ hdisj₀ F₀) =
      muxUnitary (sub.compose rC₀) (sub.compose rT₀)
        (by
          rw [QRegister.disjoint_iff]
          intro i j heq
          exact hdisj₀.ne i j (sub.wires.injective heq))
        F₀ := by
  apply Subtype.ext
  change sub.embedMatrix (muxUnitary rC₀ rT₀ hdisj₀ F₀).1 = _
  dsimp only [muxUnitary]
  rw [sub.embedMatrix_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [QRegister.embedMatrix_mul, ← compose_basisOutcomeProjector, QRegister.embedMatrix_compose]

private theorem muxUnitary_congr_regs {n k_c k_t : ℕ}
    {rC₁ rC₂ : QRegister k_c n} {rT₁ rT₂ : QRegister k_t n}
    (hC : rC₁ = rC₂) (hT : rT₁ = rT₂)
    (hd₁ : rC₁.DisjointWires rT₁) (hd₂ : rC₂.DisjointWires rT₂)
    (F : Fin (2 ^ k_c) → Unitary (2 ^ k_t)) :
    muxUnitary rC₁ rT₁ hd₁ F = muxUnitary rC₂ rT₂ hd₂ F := by
  subst hC; subst hT; rfl

private theorem extractIndex_eq_finOfBits {k m : ℕ} (r : QRegister m k) (c : Fin (2 ^ k)) :
    r.extractIndex c = finOfBits m (fun j ↦ bitsOfFin k c (r j)) := by
  rw [← bitsOfFin_extractIndex, finOfBits_bitsOfFin]

private theorem embedUnitary_mux_to_muxOnAct {k_t k_c m k₀ m₀ : ℕ}
    (sub : QRegister m (k_t + k_c))
    (rC₀ : QRegister k₀ m) (rT₀ : QRegister m₀ m) (hdisj₀ : rC₀.DisjointWires rT₀)
    (subCtrl : QRegister k₀ k_c) (subTgt : QRegister m₀ k_t)
    (hC : sub.compose rC₀ = (QRegister.block k_t k_c (by omega)).compose subCtrl)
    (hT : sub.compose rT₀ = (QRegister.block 0 k_t (by omega)).compose subTgt)
    (F₀ : Fin (2 ^ k₀) → Unitary (2 ^ m₀)) :
    sub.embedUnitary (muxUnitary rC₀ rT₀ hdisj₀ F₀) =
      muxOnAct k_t k_c
        (fun y ↦ subTgt.embedUnitary (F₀ (finOfBits k₀ (fun j ↦ y (subCtrl j))))) := by
  have hd' :
      ((QRegister.block (n := k_t + k_c) k_t k_c (by omega)).compose subCtrl).DisjointWires
        ((QRegister.block (n := k_t + k_c) 0 k_t (by omega)).compose subTgt) := by
    rw [QRegister.disjoint_iff]; intro i j
    exact (disjoint_block_ctrl_tgt k_t k_c).ne (subCtrl i) (subTgt j)
  have hp := muxUnitary_pullback (QRegister.block (n := k_t + k_c) k_t k_c (by omega))
    (QRegister.block (n := k_t + k_c) 0 k_t (by omega))
    (disjoint_block_ctrl_tgt k_t k_c) subCtrl subTgt F₀
  rw [embedUnitary_muxUnitary, muxUnitary_congr_regs hC hT _ hd', hp]
  unfold muxOnAct
  congr 1; funext c
  rw [extractIndex_eq_finOfBits]

private theorem muxOnAct_congr {k_t k_c : ℕ}
    {F₁ F₂ : (Fin k_c → Bool) → Unitary (2 ^ k_t)}
    (h : ∀ x, F₁ x = F₂ x) :
    muxOnAct k_t k_c F₁ = muxOnAct k_t k_c F₂ := by
  unfold muxOnAct
  congr 1; funext c; exact h _

theorem embedUnitary_muxOnAct_to_muxOnAct {k_t k_c k₀ m₀ : ℕ}
    (sub : QRegister (m₀ + k₀) (k_t + k_c))
    (subCtrl : QRegister k₀ k_c) (subTgt : QRegister m₀ k_t)
    (hC : sub.compose (QRegister.block m₀ k₀ (by omega)) =
      (QRegister.block k_t k_c (by omega)).compose subCtrl)
    (hT : sub.compose (QRegister.block 0 m₀ (by omega)) =
      (QRegister.block 0 k_t (by omega)).compose subTgt)
    (G₀ : (Fin k₀ → Bool) → Unitary (2 ^ m₀)) :
    sub.embedUnitary (muxOnAct m₀ k₀ G₀) =
      muxOnAct k_t k_c (fun y ↦ subTgt.embedUnitary (G₀ (fun j ↦ y (subCtrl j)))) := by
  rw [show muxOnAct m₀ k₀ G₀ = muxUnitary (QRegister.block m₀ k₀ (by omega))
        (QRegister.block 0 m₀ (by omega)) _ (fun c ↦ G₀ (bitsOfFin k₀ c)) from rfl,
    embedUnitary_mux_to_muxOnAct sub _ _ _ subCtrl subTgt hC hT]
  exact muxOnAct_congr fun y ↦ by rw [bitsOfFin_finOfBits]

/-- Subregister `(spin0 : 58) ++ (cat : k_cat)` inside `2 * 58 + k_cat`. -/
def spinCatSub (k_cat : ℕ) : QRegister (58 + k_cat) (2 * 58 + k_cat) :=
  (QRegister.block 0 58 (by omega)).concat (QRegister.block (2 * 58) k_cat (by omega))
    (by
      rw [QRegister.disjoint_iff]; intro a b h
      have hv := congrArg Fin.val h; simp at hv; omega)

theorem spinCatSub_zero : spinCatSub 0 = rSpin0 := by
  apply qreg_ext; intro idx
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
  · rw [finSumFinEquiv_apply_left, spinCatSub, QRegister.concat_apply_left]; ext; simp [rSpin0]
  · exact Fin.elim0 j

/-- Branch unitary on `2 * 58 + k_cat` qubits realized by `selectGenCoreReflDyn` on `12`-bit
decoded control `y = (rowIdx : 9, en_R, σ_sel, negPhase)`. -/
noncomputable def selectGenCoreBranch (k_cat : ℕ)
    (R_bits : (Fin 10 → Bool) → Unitary (2 ^ (58 + k_cat)))
    (y : Fin 12 → Bool) : Unitary (2 ^ (2 * 58 + k_cat)) :=
  let S_swap : Unitary (2 ^ (2 * 58 + k_cat)) :=
    (QRegister.block 0 (2 * 58) (by omega)).embedUnitary
      (if y 10 then Operator.permutationUnitary (spinSwapEquiv 58) else 1)
  let U_refl : Unitary (2 ^ (2 * 58 + k_cat)) :=
    (spinCatSub k_cat).embedUnitary (R_bits (fun j : Fin 10 ↦ y ⟨j.val, by omega⟩))
  let U_ph : Unitary (2 ^ (2 * 58 + k_cat)) :=
    if y 11 then negOneUnitary (2 * 58 + k_cat) else 1
  U_ph * (S_swap * (U_refl * S_swap))

theorem spinSwapUnitary_mul_self (N : ℕ) :
    Operator.permutationUnitary (spinSwapEquiv N) *
      Operator.permutationUnitary (spinSwapEquiv N) = 1 := by
  apply Subtype.ext; ext i g
  have h : ((Operator.permutationUnitary (spinSwapEquiv N) *
      Operator.permutationUnitary (spinSwapEquiv N)).1 *ᵥ Pi.single g 1) i =
      ((1 : Unitary (2 ^ (2 * N))).1 *ᵥ Pi.single g 1) i := by
    simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
      Operator.permutationUnitary_mulVec_single, spinSwapEquiv_involutive]
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem spinSwapUnitary_conjTranspose (N : ℕ) :
    (Operator.permutationUnitary (spinSwapEquiv N)).1ᴴ =
      (Operator.permutationUnitary (spinSwapEquiv N)).1 := by
  have hinv : (Operator.permutationUnitary (spinSwapEquiv N))⁻¹ =
      Operator.permutationUnitary (spinSwapEquiv N) :=
    (eq_inv_of_mul_eq_one_left (spinSwapUnitary_mul_self N)).symm
  exact congrArg Subtype.val hinv

theorem selectGenCoreBranch_zero_eq_selectBranchUnitary
    (R_bits : (Fin 10 → Bool) → Unitary (2 ^ 58))
    (hR0 : ∀ z : Fin 10 → Bool, z 9 = false → R_bits z = 1)
    (hR1 : ∀ (idx : Fin 319) (z : Fin 10 → Bool),
      z 9 = true →
      finOfBits 9 (fun j : Fin 9 ↦ z ⟨j.val, by omega⟩) =
        ⟨idx.val, by have := idx.isLt; omega⟩ →
      (R_bits z).1 = singleSpinReflection (p450RowVector idx))
    (xo : Fin (2 ^ 8)) (so : Fin 2) (b : Fin (2 ^ 5)) (si : Fin 2)
    (y : Fin 12 → Bool)
    (hrow : finOfBits 9 (fun j : Fin 9 ↦ y ⟨j.val, by omega⟩) =
      ⟨(rowIdxOf xo b).val, by have := (rowIdxOf xo b).isLt; omega⟩)
    (hen : y 9 = enROf xo b si)
    (hsig : finOfBits 1 (fun _ : Fin 1 ↦ y 10) = sigSelOf xo so si)
    (hph : y 11 = negPhaseOf xo b si) :
    selectGenCoreBranch 0 R_bits y = selectBranchUnitary xo so b si := by
  apply Subtype.ext
  have hwhole : QRegister.block 0 (2 * 58) (by omega : 0 + 2 * 58 ≤ 2 * 58 + 0) =
      QRegister.whole (2 * 58) := by apply qreg_ext; intro i; ext; simp
  have hsig_iff : (y 10 = false) ↔ sigSelOf xo so si = 0 := by
    rw [← hsig]; cases y 10 <;> decide
  dsimp only [selectGenCoreBranch]
  rw [hwhole, spinCatSub_zero, hph]
  simp only [Submonoid.coe_mul, QRegister.whole_embedUnitary, QRegister.embedUnitary_val]
  have hph_mat (A : Operator (2 ^ (2 * 58))) :
      ((if negPhaseOf xo b si then negOneUnitary (2 * 58) else 1 :
        Unitary (2 ^ (2 * 58))) : Operator (2 ^ (2 * 58))) * A =
        (if negPhaseOf xo b si then (-1 : ℂ) else 1) • A := by
    by_cases hp : negPhaseOf xo b si = true
    · simp [hp, negOneUnitary_val]
    · simp only [Bool.not_eq_true] at hp; simp [hp]
  rw [hph_mat]
  dsimp only [selectBranchUnitary, blockedRowReflectionUnitary]
  refine congrArg ((if negPhaseOf xo b si then (-1 : ℂ) else 1) • ·) ?_
  let z10 : Fin 10 → Bool := fun j ↦ y ⟨j.val, by omega⟩
  have hz9 : z10 9 = y 9 := rfl
  by_cases he : enROf xo b si = true
  · have hRz : (R_bits z10).1 = singleSpinReflection (p450RowVector (rowIdxOf xo b)) :=
      hR1 (rowIdxOf xo b) z10 (by rw [hz9, hen, he]) hrow
    rw [ite_eq_left he, hRz]
    by_cases hy10 : y 10 = true
    · have hs_ne : sigSelOf xo so si ≠ 0 := by
        intro hs0; have := hsig_iff.mpr hs0; simp [hy10] at this
      simp only [hy10, ↓reduceIte]
      dsimp only [blockedOrbitalReflection, rSpin0, rSpin1]
      rw [ite_eq_right hs_ne, ← Matrix.mul_assoc]
      have hconj := spinSwapUnitary_conj_block0 58
        (singleSpinReflection (p450RowVector (rowIdxOf xo b)))
      rw [spinSwapUnitary_conjTranspose 58] at hconj
      exact hconj
    · simp only [Bool.not_eq_true] at hy10
      have hs0 : sigSelOf xo so si = 0 := hsig_iff.mp hy10
      simp [hy10, hs0, blockedOrbitalReflection]
  · simp only [Bool.not_eq_true] at he
    have hRz : R_bits z10 = 1 := hR0 z10 (by rw [hz9, hen, he])
    rw [hRz, Submonoid.coe_one, rSpin0.embedMatrix_one, one_mul]
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    by_cases hy10 : y 10 = true
    · simp only [hy10, ↓reduceIte]
      have hmul := congrArg Subtype.val (spinSwapUnitary_mul_self 58)
      rw [Submonoid.coe_mul, Submonoid.coe_one] at hmul
      exact hmul
    · simp only [Bool.not_eq_true] at hy10; simp [hy10]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
