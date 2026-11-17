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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectCoreDyn

/-!
# Standalone Ambient `SELECT` `DynamicCircuit`s (`SelectDyn`)

Exports:
1. `selectPureImplUnitary`, `selectPureImplUnitary_eq_selectIdealUnitary`, and
   `selectPureImplUnitary_opNorm_sub_le` (covering both exact `δ_sel = 0` and angle-quantized
   `δ_sel > 0` single-spin reflections).
2. `selectCatStandaloneDyn` & `selectStandaloneDyn` (`1236 + t_refl` `T`, `0 TOFF`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Circuit QProg CleanDyn HermitianMat
open BlockEncodingCore
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator

/-! ### 3. Ambient `SELECT` `DynamicCircuit` Wrappers & Catalytic `tensorUBCat` Bridge -/

/-- Product state `|ψ₀⟩_{spin0} ⊗ |cat⟩_{cat}` inside `Fin (2 ^ (58 + k_cat)) → ℂ`. -/
noncomputable def tensorSpinCat {k_cat : ℕ}
    (ψ₀ : Fin (2 ^ 58) → ℂ) (cat : Fin (2 ^ k_cat) → ℂ) :
    Fin (2 ^ (58 + k_cat)) → ℂ :=
  fun g ↦ ψ₀ ((QRegister.block 0 58 (by omega)).extractIndex g) *
    cat ((QRegister.block 58 k_cat (by omega)).extractIndex g)

/-- `9`-wire `(xo : 8, so : 1)` control subregister inside `mOutUB w_go`. -/
def selOutCtrlLoc (w_go : ℕ) : QRegister (8 + 1) (mOutUB w_go) :=
  (rXoLoc w_go).concat (rSigOutLoc w_go)
    (by
      rw [QRegister.disjoint_iff]; intro i j h
      have hv := congrArg Fin.val h; simp [rXoLoc, rSigOutLoc] at hv; omega)

/-- `6`-wire `(b : 5, si : 1)` control subregister inside `mMidUB w_gi`. -/
def selMidCtrlLoc (w_gi : ℕ) : QRegister (5 + 1) (mMidUB w_gi) :=
  (rBLoc w_gi).concat (rSigInLoc w_gi)
    (by
      rw [QRegister.disjoint_iff]; intro i j h
      have hv := congrArg Fin.val h; simp [rBLoc, rSigInLoc] at hv; omega)

/-- `15`-wire `(xo : 8, so : 1, b : 5, si : 1)` control subregister inside `mAncUB w_go w_gi`. -/
def selCtrlInAnc (w_go w_gi : ℕ) : QRegister 15 (mAncUB w_go w_gi) :=
  ((QRegister.block 0 (mOutUB w_go) (by dsimp [mAncUB]; omega)).compose
    (selOutCtrlLoc w_go)).concat
  ((QRegister.block (mOutUB w_go) (mMidUB w_gi) (by dsimp [mAncUB]; omega)).compose
    (selMidCtrlLoc w_gi))
  (by
    rw [QRegister.disjoint_iff]; intro i j h
    have hv := congrArg Fin.val h; simp at hv; omega)

/-- Ambient `15`-wire `SELECT` control subregister `(xo, so, b, si)` inside `nUB w_go w_gi`. -/
def rSelCtrlUB (w_go w_gi : ℕ) : QRegister 15 (nUB w_go w_gi) :=
  (rAllUB w_go w_gi).compose (selCtrlInAnc w_go w_gi)

theorem muxUnitary_congr {n k_c k_t : ℕ}
    (rCtrl : QRegister k_c n) (rTgt : QRegister k_t n)
    {hdisj₁ hdisj₂ : rCtrl.DisjointWires rTgt}
    {F₁ F₂ : Fin (2 ^ k_c) → Unitary (2 ^ k_t)}
    (hF : ∀ c, F₁ c = F₂ c) :
    muxUnitary rCtrl rTgt hdisj₁ F₁ = muxUnitary rCtrl rTgt hdisj₂ F₂ := by
  rw [show F₁ = F₂ from funext hF]

theorem selCtrlInAnc_val_cases {w_go w_gi : ℕ} (i : Fin 15) :
    (selCtrlInAnc w_go w_gi i).val < 8 ∨
    (selCtrlInAnc w_go w_gi i).val = 8 + w_go ∨
    (mOutUB w_go ≤ (selCtrlInAnc w_go w_gi i).val ∧
      (selCtrlInAnc w_go w_gi i).val < mOutUB w_go + 5) ∨
    (selCtrlInAnc w_go w_gi i).val = mOutUB w_go + 5 + w_gi := by
  have hi_lt := i.isLt
  by_cases h8 : i.val < 8
  · left
    have hi : i = Fin.castAdd (5 + 1) (Fin.castAdd 1 (⟨i.val, h8⟩ : Fin 8)) := Fin.ext rfl
    rw [hi, selCtrlInAnc, QRegister.concat_apply_left, QRegister.compose_apply,
      selOutCtrlLoc, QRegister.concat_apply_left]
    simp [rXoLoc]; omega
  · by_cases h9 : i.val < 9
    · right; left
      have hi : i = Fin.castAdd (5 + 1) (Fin.natAdd 8 (0 : Fin 1)) := Fin.ext (by simp; omega)
      rw [hi, selCtrlInAnc, QRegister.concat_apply_left, QRegister.compose_apply,
        selOutCtrlLoc, QRegister.concat_apply_right]
      simp [rSigOutLoc]
    · by_cases h14 : i.val < 14
      · right; right; left
        have hi : i = Fin.natAdd (8 + 1) (Fin.castAdd 1 (⟨i.val - 9, by omega⟩ : Fin 5)) :=
          Fin.ext (by simp; omega)
        rw [hi, selCtrlInAnc, QRegister.concat_apply_right, QRegister.compose_apply,
          selMidCtrlLoc, QRegister.concat_apply_left]
        simp [rBLoc]; omega
      · right; right; right
        have hi : i = Fin.natAdd (8 + 1) (Fin.natAdd 5 (0 : Fin 1)) :=
          Fin.ext (by simp; omega)
        rw [hi, selCtrlInAnc, QRegister.concat_apply_right, QRegister.compose_apply,
          selMidCtrlLoc, QRegister.concat_apply_right]
        simp [rSigInLoc]; omega

/-- System + catalyst register `(2 * 58 + k_cat)` inside `nUB w_go w_gi + k_cat`. -/
def rSysCatUB (w_go w_gi k_cat : ℕ) : QRegister (2 * 58 + k_cat) (nUB w_go w_gi + k_cat) :=
  ((rUBInCat w_go w_gi k_cat).compose (rSysUB w_go w_gi)).concat
    (rCatInCat w_go w_gi k_cat)
    (by
      rw [QRegister.disjoint_iff]; intro i j
      exact (disjoint_rUBInCat_rCatInCat w_go w_gi k_cat).ne _ j)

/-- Combined `mAncUB w_go w_gi` ancilla register inside `nUB w_go w_gi + k_cat`. -/
def rAllInCat (w_go w_gi k_cat : ℕ) : QRegister (mAncUB w_go w_gi) (nUB w_go w_gi + k_cat) :=
  (rUBInCat w_go w_gi k_cat).compose (rAllUB w_go w_gi)

theorem disjoint_rAllInCat_rSysCatUB (w_go w_gi k_cat : ℕ) :
    (rAllInCat w_go w_gi k_cat).DisjointWires (rSysCatUB w_go w_gi k_cat) := by
  rw [QRegister.disjoint_iff]; intro i idx
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective idx
  · intro heq
    rw [finSumFinEquiv_apply_left, rSysCatUB, QRegister.concat_apply_left] at heq
    exact (disjoint_rAllUB_rSysUB w_go w_gi).ne i a
      ((rUBInCat w_go w_gi k_cat).wires.injective heq)
  · intro heq
    rw [finSumFinEquiv_apply_right, rSysCatUB, QRegister.concat_apply_right] at heq
    exact (disjoint_rUBInCat_rCatInCat w_go w_gi k_cat).ne _ b heq

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
end

/-!
# Catalytic `tensorUBCat` Bridge & Precomputed-Sign `SELECT` (`SelectDyn`)

Exports:
1. `selectCatImplUnitary_mulVec_tensorUBCat_eq` & `selectCatImplUnitary_l2_perturbation_le`
   (directly discharging hypothesis `hSelCat` of `ubCat_l2_perturbation_le`).
2. `selectCatPrecomputedSignsDyn` & `selectPrecomputedSignsDyn` (`620 + t_refl` `T`, `0 TOFF`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Circuit QProg CleanDyn HermitianMat
open BlockEncodingCore
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator

/-! ### 4. Catalytic `tensorSpinCat` / `tensorUBCat` Bridge & Precomputed-Sign `SELECT` -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
end
